/*
* Copyright (c) 2014 Amlogic, Inc. All rights reserved.
* *
This source code is subject to the terms and conditions defined in the
* file 'LICENSE' which is part of this source code package.
* *
Description:
*/

#include <ctype.h>
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <fcntl.h>
#include <time.h>
#include <selinux/selinux.h>
#include <ftw.h>
#include <sys/capability.h>
#include <sys/xattr.h>
#include <linux/xattr.h>
#include <inttypes.h>
#include <ziparchive/zip_archive.h>

#include <memory>
#include <vector>

#include "bootloader.h"
#include "cutils/android_reboot.h"
#include "cutils/properties.h"
#include "edify/expr.h"
#include "error_code.h"
#include "updater/updater.h"
#include "check/dtbcheck.h"
#include "ubootenv/uboot_env.h"

#include "roots.h"
#include <bootloader_message/bootloader_message.h>
#include <fs_mgr.h>

#include "common.h"
#include "device.h"

#include "ui.h"
#include <dirent.h>

#include <android-base/file.h>
#include <android-base/parseint.h>
#include <android-base/stringprintf.h>
#include <android-base/strings.h>

#define ARRAY_SIZE(x)  sizeof(x)/sizeof(x[0])
#define EMMC_USER_PARTITION        "bootloader"
#define EMMC_BLK0BOOT0_PARTITION   "mmcblk0boot0"
#define EMMC_BLK0BOOT1_PARTITION   "mmcblk0boot1"
#define EMMC_BLK1BOOT0_PARTITION   "mmcblk1boot0"
#define EMMC_BLK1BOOT1_PARTITION   "mmcblk1boot1"
#define COMMAND_FILE "/cache/recovery/command"
#define CACHE_ROOT "/cache"

#define UNCRYPT_FILE "/cache/recovery/uncrypt_file"


enum emmcPartition {
    USER = 0,
    BLK0BOOT0,
    BLK0BOOT1,
    BLK1BOOT0,
    BLK1BOOT1,
};

static int sEmmcPartionIndex = -1;
static const char *sEmmcPartionName[] = {
    EMMC_USER_PARTITION,
    EMMC_BLK0BOOT0_PARTITION,
    EMMC_BLK0BOOT1_PARTITION,
    EMMC_BLK1BOOT0_PARTITION,
    EMMC_BLK1BOOT1_PARTITION,
};

int wipe_flag = 0;

int RecoverySecureCheck(const ZipArchiveHandle zipArchive);
int RecoveryDtbCheck(const ZipArchiveHandle zipArchive);
int GetEnvPartitionOffset(const ZipArchiveHandle za);
/*
 * return value: 0 if no error; 1 if path not existed, -1 if access failed
 *
 */
static int read_sysfs_val(const char* path, char* rBuf, const unsigned bufSz, int * readCnt)
{
    int ret = 0;
    int fd  = -1;
    int count = 0;

    if (access(path, F_OK)) {
            printf("path[%s] not existed\n", path);
            return 1;
    }
    if (access(path, R_OK)) {
            printf("path[%s] cannot read\n", path);
            return -1;
    }

    fd = open(path, O_RDONLY);
    if (fd < 0) {
            printf("fail in open[%s] in O_RDONLY\n", path);
            goto _exit;
    }

    count = read(fd, rBuf, bufSz);
    if (count <= 0) {
            printf("read %s failed (count:%d)\n",
                            path, count);
            close(fd);
            return -1;
    }
    *readCnt = count;

    ret = 0;
_exit:
    if (fd >= 0) close(fd);
    return ret;
}

static int getBootloaderOffset(int* bootloaderOffset)
{
    const char* PathBlOff = "/sys/class/aml_store/bl_off_bytes" ;
    int             iret  = 0;
    int             blOff = 0;
    char  buf[16]         = { 0 };
    int           readCnt = 0;

    iret = read_sysfs_val(PathBlOff, buf, 16, &readCnt);
    if (iret < 0) {
            printf("fail when read path[%s]\n", PathBlOff);
            return __LINE__;
    }
    buf[readCnt] = 0;
    *bootloaderOffset = atoi(buf);
    printf("bootloaderOffset is %s\n", buf);

    return 0;
}

static int _mmcblOffBytes = 0;


static int write_data(int fd, const char *data, ssize_t len)
{
    ssize_t size = len;
    char *verify = NULL;

    off_t pos = lseek(fd, 0, SEEK_CUR);
    fprintf(stderr, "data len = %d, pos = %ld\n", len, pos);


    if (write(fd, data, len) != len) {
        fprintf(stderr, " write error at 0x%08lx (%s)\n",pos, strerror(errno));
        return -1;
    }

    verify = (char *)malloc(size);
    if (verify == NULL) {
        fprintf(stderr, "block: failed to malloc size=%u (%s)\n", size, strerror(errno));
        return -1;
    }

    if ((lseek(fd, pos, SEEK_SET) != pos) ||(read(fd, verify, size) != size)) {
        fprintf(stderr, "block: re-read error at 0x%08lx (%s)\n",pos, strerror(errno));
        if (verify) {
            free(verify);
        }
        return -1;
    }

    if (memcmp(data, verify, size) != 0) {
        fprintf(stderr, "block: verification error at 0x%08lx (%s)\n",pos, strerror(errno));
        if (verify) {
            free(verify);
        }
        return -1;
    }

    fprintf(stderr, "successfully wrote data at %ld\n", pos);
    if (verify) {
        free(verify);
    }

    return len;
}


//return value
// -1  :   failed
//  0   :   success
static int backup_partition_data(const char *name,const char *dir, long offset) {
    int ret = 0;
    int fd = 0;
    FILE *fp = NULL;
    int sor_fd = -1;
    int dst_fd = -1;
    ssize_t wrote = 0;
    ssize_t readed = 0;
    char devpath[128] = {0};
    char dstpath[128] = {0};
    const int BUFFER_MAX =  32*1024*1024;   //Max support 32*M
    printf("backup partition name:%s, to dir:%s\n", name, dir);

    if ((name == NULL) || (dir == NULL)) {
        fprintf(stderr, "name(%s) or dir(%s) is NULL!\n", name, dir);
        return -1;
    }

    if (!strcmp(name, "dtb")) {//dtb is char device
        sprintf(devpath, "/dev/%s", name);
    } else {
        sprintf(devpath, "/dev/block/%s", name);
    }

    sprintf(dstpath, "%s%s.img", dir, name);

    sor_fd = open(devpath, O_RDONLY);
    if (sor_fd < 0) {
        fprintf(stderr, "open %s failed (%s)\n",devpath, strerror(errno));
        return -1;
    }

    dst_fd = open(dstpath, O_WRONLY | O_CREAT, 00777);
    if (dst_fd < 0) {
        fprintf(stderr, "open %s failed (%s)\n",dstpath, strerror(errno));
        return -1;
    }

    char* buffer = (char *)malloc(BUFFER_MAX);
    if (buffer == NULL) {
        fprintf(stderr, "can't malloc %d buffer!\n", BUFFER_MAX);
        goto err_out;
    }

    if (strcmp(name, "dtb")) {
        lseek(sor_fd, offset, SEEK_SET);
    }

    readed = read(sor_fd, buffer, BUFFER_MAX);
    if (readed <= 0) {
        fprintf(stderr, "read failed read:%d!\n", readed);
        goto err_out;
    }

    wrote = write(dst_fd, buffer, readed);
    if (wrote != readed) {
        fprintf(stderr, "write %s failed (%s)\n",dstpath, strerror(errno));
        goto err_out;
    }

    close(dst_fd);
    close(sor_fd);
    free(buffer);
    buffer == NULL;

    //umount /cache and do fsync for data save
    ret = umount("/cache");
    if (ret != 0) {
        fprintf(stderr, "umount cache failed (%s)\n",dstpath, strerror(errno));
    }

    fd = open("/dev/block/cache", O_RDWR);
    if (fd < 0) {
        fprintf(stderr, "open %s failed (%s)\n","/dev/block/cache", strerror(errno));
        return -1;
    }

    fp = fdopen(fd, "r+");
    if (fp == NULL) {
        printf("fdopen failed!\n");
        close(fd);
        return -1;
    }

    fflush(fp);
    fsync(fd);
    fclose(fp);

    ret = mount("/dev/block/cache", "/cache", "ext4",\
        MS_NOATIME | MS_NODEV | MS_NODIRATIME,"discard");
    if (ret < 0 ) {
        fprintf(stderr, "mount cache failed (%s)\n","/dev/block/cache", strerror(errno));
    }

    return 0;


err_out:
    if (sor_fd > 0) {
        close(sor_fd);
    }

    if (dst_fd > 0) {
        close(dst_fd);
    }

    if (buffer) {
        free(buffer);
        buffer == NULL;
    }

    return -1;

}


static ssize_t write_chrdev_data(const char *dev, const char *data, const ssize_t size)
{
    int fd = -1;
    ssize_t wrote = 0;
    ssize_t readed = 0;
    char *verify = NULL;

    fd = open(dev, O_RDWR);
    if (fd < 0) {
        fprintf(stderr, "open %s failed (%s)\n", dev, strerror(errno));
        return -1;
    }

    fprintf(stderr, "data len = %d\n", size);
    if ((wrote = write(fd, data, size)) != size) {
        fprintf(stderr, "wrote error, count %d (%s)\n",wrote, strerror(errno));
        goto err;
    }

    fsync(fd);
    close(fd);
    sync();

    fd = open(dev, O_RDWR);
    if (fd < 0) {
        fprintf(stderr, "open %s failed after wrote success (%s)\n", dev, strerror(errno));
        return -1;
    }

    verify = (char *)malloc(256*1024);
    if (verify == NULL) {
        fprintf(stderr, "failed to malloc size=%d (%s)\n", size, strerror(errno));
        goto err;
    }

    memset(verify, 0, 256*1024);

    if ((readed = read(fd, verify, size)) != size) {
        fprintf(stderr, "readed error, count %d (%s)\n", readed, strerror(errno));
        if (verify != NULL) {
            free(verify);
        }
        goto err;
    }

    if (memcmp(data, verify, size) != 0) {
        fprintf(stderr, "verification error, wrote != readed\n");
        if (verify != NULL) {
            free(verify);
        }
        goto err;
    }

    fprintf(stderr, " successfully wrote data\n");
    if (verify != NULL) {
        free(verify);
    }

    if (fd > 0) {
        close(fd);
    }
    return wrote;

err:
    if (fd > 0) {
        close(fd);
    }
    return -1;
}

int block_write_data( const std::string& args, off_t offset) {
    int fd = -1;
    int result = 0;
    bool success = false;
    char * tmp_name = NULL;
    char devname[64] = {0};

    memset(devname, 0, sizeof(devname));
    sprintf(devname, "/dev/%s", "bootloader");  //nand partition
    fd = open(devname, O_RDWR);
    if (fd < 0) {
        memset(devname, 0, sizeof(devname));
        // emmc user, boot0, boot1 partition
        sprintf(devname, "/dev/block/%s", sEmmcPartionName[sEmmcPartionIndex]);
        fd = open(devname, O_RDWR);
        if (fd < 0) {
            tmp_name = "mtdblock0";
            memset(devname, 0, sizeof(devname));
            sprintf(devname, "/dev/block/%s", tmp_name); //spi partition
            fd = open(devname, O_RDWR);
            if (fd < 0) {
                printf("failed to open %s\n", devname);
                goto done;
            }
        }

        printf("start to write bootloader to %s...\n", devname);
        lseek(fd, offset, SEEK_SET);//seek to skip mmc area since gxl
        ssize_t wrote = write_data(fd, args.c_str(), args.size());
        success = (wrote == args.size());


        if (!success) {
            fprintf(stderr, "write_data to %s partition failed: %s\n", devname, strerror(errno));
        } else {
            printf("write_data to %s partition successful\n", devname);
        }
    } else {
        printf("start to write bootloader to %s...\n", devname);
        success = true;
        int size =  args.size();
        lseek(fd, offset, SEEK_SET);//need seek one sector to skip MBR area since gxl
        fprintf(stderr, "size = %d offset = %d\n", size, offset);
        if (write(fd, args.c_str(), size) != size) {
            fprintf(stderr, " write error at offset :%d (%s)\n",offset, strerror(errno));
            success = false;
        }

        if (!success) {
            fprintf(stderr, "write_data to %s partition failed: %s\n", devname, strerror(errno));
        } else {
            printf("write_data to %s partition successful\n", devname);
        }
    }

    result = success ? 0 : -1;
    return result;

done:
    if (fd > 0) {
        close(fd);
        fd = -1;
    }
    return -1;
}


Value* WriteBootloaderImageFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
    char* result = NULL;
    int iRet = 0;

    if (argv.size() != 1) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() expects at least 1 arg", name);
    }

    std::vector<std::unique_ptr<Value>> args;
    if (!ReadValueArgs(state, argv, &args)) {
        return nullptr;
    }

    if ((args[0]->type == VAL_STRING || (args[0]->data.size())) == 0) {
        ErrorAbort(state, kArgsParsingFailure, "file argument to %s can't be empty", name);
        return nullptr;
    }

    iRet = getBootloaderOffset(&_mmcblOffBytes);
    if (iRet) {
        printf("Fail in getBootloaderOffset, ret=%d\n", iRet);
        return StringValue("bootloader err");
    }

    unsigned int i;
    char emmcPartitionPath[128];
    for (i = BLK0BOOT0; i < ARRAY_SIZE(sEmmcPartionName); i ++) {
        memset(emmcPartitionPath, 0, sizeof(emmcPartitionPath));
        sprintf(emmcPartitionPath, "/dev/block/%s", sEmmcPartionName[i]);
        if (!access(emmcPartitionPath, F_OK)) {
            sEmmcPartionIndex = i;
            iRet = block_write_data(args[0]->data, _mmcblOffBytes);
            if (iRet == 0) {
                printf("Write Uboot Image to %s successful!\n\n", sEmmcPartionName[sEmmcPartionIndex]);
            } else {
                printf("Write Uboot Image to %s failed!\n\n", sEmmcPartionName[sEmmcPartionIndex]);
                printf("iRet= %d, exit !!!\n", iRet);
                return ErrorAbort(state, kFwriteFailure, "%s() update bootloader", name);
            }
        }
    }

    sEmmcPartionIndex = USER;
    iRet = block_write_data(args[0]->data, _mmcblOffBytes);
    if (iRet == 0) {
        printf("Write Uboot Image successful!\n\n");
    } else {
        printf("Write Uboot Image failed!\n\n");
        printf("iRet= %d, exit !!!\n", iRet);
        return ErrorAbort(state, kFwriteFailure, "%s() update bootloader", name);
    }

    return StringValue("bootloader");
}

Value* WriteDtbImageFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
    bool success = false;
    const char *DTB_DEV=  "/dev/dtb";
    const int DTB_DATA_MAX =  256*1024;// write 256K dtb datas to dtb device maximum,kernel limit

    if (argv.size() != 1) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() expects at least 1 arg", name);
    }

    std::vector<std::unique_ptr<Value>> args;

    if (!ReadValueArgs(state, argv, &args)) {
        return nullptr;
    }

    if (args[0]->type == VAL_INVALID) {
        return StringValue("");
    }

    fprintf(stderr, "\nstart to write dtb.img to %s...\n", DTB_DEV);
    if (args[0]->type == VAL_BLOB) {
        fprintf(stderr, "contents type: VAL_BLOB\ncontents size: %d\n", args[0]->data.size());
        if (!args[0]->data.c_str() || -1 == args[0]->data.size()) {
            fprintf(stderr, "#ERR:BLOb Data extracted FAILED for dtb\n");
            success = false;
        } else {
            if (args[0]->data.size() > DTB_DATA_MAX) {
                fprintf(stderr, "data size(%d) out of range size(max:%d)\n", args[0]->data.size(), DTB_DATA_MAX);
                return StringValue("");
            }
            ssize_t wrote = write_chrdev_data(DTB_DEV, args[0]->data.c_str(), args[0]->data.size());
            success = (wrote == args[0]->data.size());
        }
    }

    if (!success) {
        return ErrorAbort(state, kFwriteFailure, "%s() update dtb failed", name);
    } else {
        return StringValue("dtb");
    }
}

Value* SetBootloaderEnvFn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
    int ret = 0;
    if (argv.size() != 2) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() expects 2 args, got %zu", name,argv.size());
    }

    std::vector<std::string> args;
    if (!ReadArgs(state, argv, &args)) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
    }

    const std::string& env_name = args[0];
    const std::string& env_val = args[1];

    if ((env_name.size() == 0) || (env_val.size() == 0)) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() Failed, one of the argument(s) is null ", name);
    }

    ret = set_bootloader_env(env_name.c_str(), env_val.c_str());
    printf("setenv %s %s %s.(%d)\n", env_name.c_str(), env_val.c_str(), (ret < 0) ? "failed" : "successful", ret);
    if (!ret) {
        return StringValue("success");
    } else {
        return StringValue("");
    }
}


Value* OtaZipCheck(const char* name, State* state,
                           const std::vector<std::unique_ptr<Expr>>&argv) {
    int check = 0;
    ZipArchiveHandle za = static_cast<UpdaterInfo*>(state->cookie)->package_zip;

    printf("\n-- Secure Check...\n");

    check = RecoverySecureCheck(za);
    if (check <= 0) {
        return ErrorAbort(state, "Secure check failed. %s\n\n", !check ? "(Not match)" : "");
    } else if (check == 1) {
        printf("Secure check complete.\n\n");
    }

#ifndef RECOVERY_DISABLE_DTB_CHECK
    printf("\n-- Dtb Check...\n");

    check = RecoveryDtbCheck(za);
    if (check != 0) {
#ifdef SUPPORT_PARTNUM_CHANGE
        check = 3;//allow upgrade by two step
#endif
        if (check > 1) {
            if (check == 3) {
                printf("data offset changed, need wipe_data\n\n");
                wipe_flag = 1;

                FILE *pf = fopen("/cache/recovery/stage", "w+");
                if (pf != NULL) {
                    printf("write /cache/recovery/stage \n\n");
                    int len = fwrite("2", 1, strlen("2"), pf);
                    printf("stage write len:%d, 2\n", len);
                    fflush(pf);
                    fclose(pf);
                }
            }
            printf("dtb check not match, but can upgrade by two step.\n\n");
            return StringValue(strdup("1"));
        }
        return ErrorAbort(state, "Dtb check failed. %s\n\n", !check ? "(Not match)" : "");
    } else {
        printf("dtb check complete.\n\n");
    }
#endif
    return StringValue(strdup("0"));
}

Value* BackupDataCache(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
    int ret = 0;
    if (argv.size() != 2) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() expects 2 args, got %zu", name, argv.size());
    }

    std::vector<std::string> args;
    if (!ReadArgs(state, argv, &args)) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
    }

    const std::string& partition = args[0];
    const std::string& destination = args[1];

    ret = backup_partition_data(partition.c_str(), destination.c_str(), 0);
    if (ret != 0) {
        printf("backup %s to %s , failed!\n", partition.c_str(), destination.c_str());
    } else {
        printf("backup %s to %s , success!\n", partition.c_str(), destination.c_str());
    }

    return StringValue("backup");
}

Value* RebootRecovery(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
    struct bootloader_message boot {};
    std::string err;

    read_bootloader_message(&boot,  &err);

    printf("boot.command: %s\n", boot.command);
    printf("boot.recovery: %s\n", boot.recovery);

    if (strstr(boot.recovery, "--update_package=")) {
        printf("check bootloader_message \n");
        if (wipe_flag == 1) {
            printf("need wipe data \n");
            strlcat(boot.recovery, "--wipe_data\n", sizeof(boot.recovery));
        }
    }

    printf("boot.command: %s\n", boot.command);
    printf("boot.recovery: %s\n", boot.recovery);

    printf("write_bootloader_message \n");
    if (!write_bootloader_message(boot, &err)) {
        printf("%s\n", err.c_str());
        printf("write_bootloader_message failed!\n");
    }


    if (!strstr(boot.recovery, "--update_package=")) {
        std::string content;
        printf("bootloader_message is null \n");
        if (android::base::ReadFileToString(COMMAND_FILE, &content)) {
            printf("recovery command: %s\n", content.c_str());
            if (wipe_flag == 1) {
                printf("need wipe data \n");
                std::string content2 = content + "--wipe_data\n";
                printf("recovery command 2: %s\n", content2.c_str());

                if (!android::base::WriteStringToFile(content2, COMMAND_FILE)) {
                    printf("failed to write %s\n", COMMAND_FILE);
                }
            }
        }
        printf("read %s error\n", COMMAND_FILE);
    }

    property_set(ANDROID_RB_PROPERTY, "reboot,recovery");
    sleep(5);

    return ErrorAbort(state, "reboot to recovery failed!\n");
}


Value* Reboot(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {

    property_set(ANDROID_RB_PROPERTY, "reboot");
    sleep(5);

    return ErrorAbort(state, "reboot failed!\n");
}


Value* SetUpdateStage(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
    int ret = 0;
    if (argv.size() != 1) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() expects 1 args, got %zu", name, argv.size());
    }

    std::vector<std::string> args;
    if (!ReadArgs(state, argv, &args)) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
    }

    const std::string& stage_step = args[0];

    FILE *pf = fopen("/cache/recovery/stage", "w+");
    if (pf == NULL) {
        return ErrorAbort(state, "fopen stage failed!\n");
    }

    int len = fwrite(stage_step.c_str(), 1, strlen(stage_step.c_str()), pf);
    printf("stage write len:%d, %s\n", len, stage_step.c_str());
    fflush(pf);
    fclose(pf);

    return StringValue("done");
}

Value* GetUpdateStage(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
    char buff[128] = {0};

    FILE *pf = fopen("/cache/recovery/stage", "r");
    if (pf == NULL) {
        return StringValue("0");
    }

    int len = fread(buff, 1, 128, pf);
    printf("stage fread len:%d, %s\n", len, buff);
    fclose(pf);

    return StringValue(buff);
}

Value* BackupEnvPartition(const char* name, State* state,
                           const std::vector<std::unique_ptr<Expr>>&argv) {
    int offset = 0;
    char tmpbuf[32] = {0};
    ZipArchiveHandle za = static_cast<UpdaterInfo*>(state->cookie)->package_zip;

    offset = GetEnvPartitionOffset(za);
    if (offset <= 0) {
        return ErrorAbort(state, "get env partition offset failed!\n");
    }

    offset = offset/(1024*1024);

    sprintf(tmpbuf, "%s%d", "seek=", offset);
    char *args2[7] = {"/sbin/busybox", "dd", "if=/dev/block/env", "of=/dev/block/mmcblk0", "bs=1M"};
    args2[5] = &tmpbuf[0];
    args2[6] = nullptr;
    pid_t child = fork();
    if (child == 0) {
        execv("/sbin/busybox", args2);
        printf("execv failed\n");
        _exit(EXIT_FAILURE);
    }

    int status;
    waitpid(child, &status, 0);
    if (WIFEXITED(status)) {
        if (WEXITSTATUS(status) != 0) {
            ErrorAbort(state,"child exited with status:%d\n", WEXITSTATUS(status));
        }
    } else if (WIFSIGNALED(status)) {
        ErrorAbort(state,"child terminated by signal :%d\n", WTERMSIG(status));
    }

    return StringValue(strdup("0"));
}

Value* BackupUpdatePackage(const char* name, State* state,
                           const std::vector<std::unique_ptr<Expr>>&argv) {
    int ret = 0;
    if (argv.size() != 2) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() expects 2 args, got %zu", name, argv.size());
    }

    std::vector<std::string> args;
    if (!ReadArgs(state, argv, &args)) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
    }

    const std::string& partition = args[0];
    const std::string& offset = args[1];

    std::string err;
    char buf[256] = {0};
    char tmp[256] = {0};
    char path[256] = {0};
    struct bootloader_message boot {};

    read_bootloader_message(&boot,  &err);

    printf("boot.command: %s\n", boot.command);
    printf("boot.recovery: %s\n", boot.recovery);

    if (strstr(boot.recovery, "--update_package=")) {
        printf("check bootloader_message \n");
        strcpy(tmp, strstr(boot.recovery, "--update_package="));
        char *p = strtok(tmp, "\n");
        strcpy(path, tmp+strlen("--update_package="));
    }

    if (!strstr(boot.recovery, "--update_package=")) {
        std::string content;
        printf("bootloader_message is null \n");
        if (android::base::ReadFileToString(COMMAND_FILE, &content)) {
            printf("recovery command: %s\n", content.c_str());
            if (strstr(content.c_str(), "--update_package=")) {
                strcpy(tmp, strstr(content.c_str(), "--update_package="));
                char *p = strtok(tmp, "\n");
                strcpy(path, tmp+strlen("--update_package="));
            } else {
                ret = -1;
            }
        }
    }

    printf("update package path: %s\n", path);

    //if update_package=@/cache/recovery/block.map
    //need to find the real data of package and backup to /dev/block/mmcblk0
    //and save the size and name of package to /cache/recovery/zipinfo
    if (path[0] == '@') {
        std::string content;
        if (android::base::ReadFileToString(UNCRYPT_FILE, &content)) {
            printf("recovery uncrypt: %s\n", content.c_str());
            strcpy(path, content.c_str());
        }

        printf("%s %s %d", path, offset.c_str(), static_cast<UpdaterInfo*>(state->cookie)->package_zip_len);
        sprintf(buf, "%s %s %d", path, offset.c_str(), static_cast<UpdaterInfo*>(state->cookie)->package_zip_len);

        FILE *pf = fopen("/cache/recovery/zipinfo", "w+");
        if (pf == NULL) {
            return ErrorAbort(state, "fopen zipinfo failed!\n");
        }

        int len = fwrite(buf, 1, strlen(buf), pf);
        printf("zipinfo write len:%d, %s\n", len, buf);
        fflush(pf);
        fclose(pf);

        int fd = open(partition.c_str(), O_RDWR);
        if (fd < 0) {
            printf("open %s failed!\n", partition.c_str());
            return ErrorAbort(state, "open mmcblk failed!\n");
        }

        int offset_w = strtoul(offset.c_str(), NULL, 10);

        int result = lseek(fd, offset_w*1024*1024, SEEK_SET);
        if (result == -1) {
            printf("lseek %s failed!\n", partition.c_str());
            return ErrorAbort(state, "lseek mmcblk failed!\n");
        }

        int len_w = write(fd, static_cast<UpdaterInfo*>(state->cookie)->package_zip_addr,static_cast<UpdaterInfo*>(state->cookie)->package_zip_len);
        if (len_w != static_cast<UpdaterInfo*>(state->cookie)->package_zip_len) {
            printf("write %s failed!\n", partition.c_str());
            return ErrorAbort(state, "write mmcblk failed!\n");
        }

        FILE *fp = NULL;
        fp = fdopen(fd, "r+");
        if (fp == NULL) {
            printf("fdopen failed!\n");
            close(fd);
            return ErrorAbort(state, "close mmcblk failed!\n");
        }

        fflush(fp);
        fsync(fd);
        fclose(fp);
    } else if (!strncmp(path, "/data", 5)) {
        printf("%s %s %d", path, offset.c_str(), static_cast<UpdaterInfo*>(state->cookie)->package_zip_len);
        sprintf(buf, "%s %s %d", path, offset.c_str(), static_cast<UpdaterInfo*>(state->cookie)->package_zip_len);

        FILE *pf = fopen("/cache/recovery/zipinfo", "w+");
        if (pf == NULL) {
            return ErrorAbort(state, "fopen zipinfo failed!\n");
        }

        int len = fwrite(buf, 1, strlen(buf), pf);
        printf("zipinfo write len:%d, %s\n", len, buf);
        fflush(pf);
        fclose(pf);

        char buf_in[64] = {0};
        char buf_out[64] = {0};
        char buf_bs[16] = {0};
        char buf_seek[64] = {0};
        sprintf(buf_in, "%s%s", "if=", path);
        sprintf(buf_out, "%s%s", "of=", partition.c_str());
        sprintf(buf_bs, "%s", "bs=1M");
        sprintf(buf_seek, "%s%s", "seek=", offset.c_str());

        char *args2[7] = {"/sbin/busybox", "dd"};
        args2[2] = &buf_in[0];
        args2[3] = &buf_out[0];
        args2[4] = &buf_bs[0];
        args2[5] = &buf_seek[0];
        args2[6] = nullptr;

        pid_t child = fork();
        if (child == 0) {
            execv("/sbin/busybox", args2);
            printf("execv failed\n");
            _exit(EXIT_FAILURE);
        }

        int status;
        waitpid(child, &status, 0);
        if (WIFEXITED(status)) {
            if (WEXITSTATUS(status) != 0) {
                ErrorAbort(state,"child exited with status:%d\n", WEXITSTATUS(status));
            }
        } else if (WIFSIGNALED(status)) {
            ErrorAbort(state,"child terminated by signal :%d\n", WTERMSIG(status));
        }
    }

    if (ret == 0) {
        return StringValue(strdup("0"));
    } else {
        return ErrorAbort(state, "backup update to /dev/block/mmcblk* failed!\n");
    }
}

Value* DeleteFileByName(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
    int ret = 0;
    if (argv.size() != 1) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() expects 1 args, got %zu", name, argv.size());
    }

    std::vector<std::string> args;
    if (!ReadArgs(state, argv, &args)) {
        return ErrorAbort(state, kArgsParsingFailure, "%s() Failed to parse the argument(s)", name);
    }

    const std::string& file = args[0];

    struct stat st;
    if (stat(file.c_str(), &st) == 0) {
        unlink(file.c_str());
    } else {
        printf("%s not exist, can not delete it!\n", file.c_str());
    }

    return StringValue("done");
}

void Register_libinstall_amlogic() {
    RegisterFunction("write_dtb_image", WriteDtbImageFn);
    RegisterFunction("write_bootloader_image", WriteBootloaderImageFn);
    RegisterFunction("reboot_recovery", RebootRecovery);
    RegisterFunction("reboot", Reboot);
    RegisterFunction("backup_data_cache", BackupDataCache);
    RegisterFunction("set_bootloader_env", SetBootloaderEnvFn);
    RegisterFunction("ota_zip_check", OtaZipCheck);
    RegisterFunction("get_update_stage", GetUpdateStage);
    RegisterFunction("set_update_stage", SetUpdateStage);
    RegisterFunction("backup_env_partition", BackupEnvPartition);
    RegisterFunction("backup_update_package", BackupUpdatePackage);
    RegisterFunction("delete_file", DeleteFileByName);
}
