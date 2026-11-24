/*
 * Copyright (C) 2025-2026 AxionOS
 * Copyright (C) 2026 VoltageOS
 * Copyright (C) 2026 crDroid Android Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "custom_rom_hide.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <linux/magic.h>
#include <linux/memfd.h>
#include <linux/stat.h>
#include <pthread.h>
#include <stdio.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/syscall.h>
#include <sys/sysmacros.h>
#include <sys/system_properties.h>
#include <unistd.h>
#include <private/android_filesystem_config.h>
#include <private/bionic_lock.h>

#define HIDE_MEMFD_TAG "mf"
#define HIDE_MEMFD_NAME_PREFIX HIDE_MEMFD_TAG ":"
#define HIDE_MEMFD_LINK_PREFIX "/memfd:" HIDE_MEMFD_TAG ":"
#define HIDE_MEMFD_LINK_PREFIX_LEN (sizeof(HIDE_MEMFD_LINK_PREFIX) - 1)

#ifndef OVERLAYFS_SUPER_MAGIC
#define OVERLAYFS_SUPER_MAGIC 0x794c7630
#endif
#ifndef EROFS_SUPER_MAGIC_V1
#define EROFS_SUPER_MAGIC_V1 0xe0f5e1e2
#endif
#ifndef TMPFS_MAGIC
#define TMPFS_MAGIC 0x01021994
#endif

struct PrefixEntry {
    const char* str;
    size_t len;
};
#define PE(s) { s, sizeof(s) - 1 }

static const char* const kBlockedDirnames[] = {
    "addon.d", "init.d", "TWRP", nullptr
};

static const PrefixEntry kDirParents[] = {
    PE("/system"), PE("/system/etc"),
    PE("/system_ext"), PE("/system_ext/etc"),
    PE("/product"), PE("/product/etc"),
    PE("/vendor"), PE("/vendor/etc"),
    PE("/odm"), PE("/odm/etc"),
    PE("/etc"),
    PE("/sdcard"), PE("/data/media/0"),
    { nullptr, 0 }
};

static const PrefixEntry kFrameworkDirs[] = {
    PE("/system/framework"),
    PE("/system_ext/framework"),
    PE("/product/framework"),
    { nullptr, 0 }
};

static const PrefixEntry kOverlayDirs[] = {
    PE("/system/overlay"),
    PE("/system_ext/overlay"),
    PE("/product/overlay"),
    PE("/vendor/overlay"),
    PE("/odm/overlay"),
    { nullptr, 0 }
};

static const PrefixEntry kRomArtifactPrefixes[] = {
    PE("com.shinkai."),
    PE("org.shinkai."),
    PE("net.pixelos."),
    PE("org.evolution."),
    PE("org.lineageos."),
    PE("org.libremobileos."),
    PE("com.crdroid."),
    PE("lineage-sdk"),
    PE("lineagesettings"),
    PE("co.aospa."),
    PE("com.android.axion."),
    PE("org.lunaris."),
    PE("org.omnirom."),
    PE("org.protonaosp."),
    { nullptr, 0 }
};

static const PrefixEntry kProcFilterKeywords[] = {
    PE("shinkai"), PE("Shinkai"), PE("pixelos"), PE("PixelOS"),
    PE("lineage"), PE("Lineage"), PE("evolution"), PE("Evolution"),
    PE("omnirom"), PE("aospa"),
    { nullptr, 0 }
};

static const PrefixEntry kConfigDirs[] = {
    PE("/system/etc/selinux"),      PE("/system_ext/etc/selinux"),
    PE("/product/etc/selinux"),     PE("/vendor/etc/selinux"),
    PE("/odm/etc/selinux"),
    PE("/system/etc/init"),         PE("/system_ext/etc/init"),
    PE("/product/etc/init"),        PE("/vendor/etc/init"),
    PE("/odm/etc/init"),
    PE("/system/etc/permissions"),  PE("/system_ext/etc/permissions"),
    PE("/product/etc/permissions"), PE("/vendor/etc/permissions"),
    PE("/system/etc/sysconfig"),    PE("/system_ext/etc/sysconfig"),
    PE("/product/etc/sysconfig"),
    PE("/system/etc/vintf"),        PE("/system_ext/etc/vintf"),
    PE("/product/etc/vintf"),       PE("/vendor/etc/vintf"),
    { nullptr, 0 }
};

static const char* const kMountFilterKeywords[] = {
    "/debug_ramdisk", "overlay", "magisk", "ksu", "KSU", "ksud", "apatch", "/data/adb", nullptr
};

static const char* const kAllowlistedPackages[] = {
    "net.pixelos.ota",
    "org.lineageos.updater",
    nullptr
};

#define DM_MAJOR 253u

struct PartitionDevEntry {
    const char* path;
    unsigned int dm_minor;
};

static const PartitionDevEntry kPartitionDmMap[] = {
    { "/system",     0 },
    { "/vendor",     1 },
    { "/product",    2 },
    { "/system_ext", 3 },
    { "/odm",        4 },
    { nullptr,       0 },
};

// Metadata of the real file, captured when the substitution is created while the
// canonical path still resolves. It is the fallback for fstat/statx once that path
// no longer resolves, for example after a thread supplying /proc/thread-self exits.
struct FdMeta {
    struct stat sb;
    struct statx sx;
    bool sb_ok;
    bool sx_ok;
};

static constexpr unsigned kStatxCaptureMask = STATX_ALL | STATX_DIOALIGN |
        STATX_MNT_ID_UNIQUE | STATX_SUBVOL | STATX_WRITE_ATOMIC | STATX_DIO_READ_ALIGN;

// Sparse pages cover the full nonnegative int range without allocating a
// descriptor-sized table in every process. Pages stay alive once published so
// ordinary close, fstat, and signal handlers stay lock-free and allocation-free.
static constexpr unsigned kFdPageBits = 6;
static constexpr unsigned kFdPageSize = 1u << kFdPageBits;
static constexpr unsigned kFdPageMask = kFdPageSize - 1;
static constexpr unsigned kFdTableBits = 8;
static constexpr unsigned kFdTableSize = 1u << kFdTableBits;
static constexpr unsigned kFdTableMask = kFdTableSize - 1;
static constexpr unsigned kFdDirEntries = 512;

struct FdPage {
    _Atomic(uint64_t) tracked;
    FdMeta metadata[kFdPageSize];
    _Atomic(uint32_t) meta_seq[kFdPageSize];
    _Atomic(bool) meta_valid[kFdPageSize];
};

struct FdPageTable {
    _Atomic(FdPage*) pages[kFdTableSize];
};

struct FdDirectory {
    _Atomic(FdPageTable*) tables[kFdTableSize];
};

static _Atomic(FdDirectory*) g_fd_directories[kFdDirEntries];
static Lock g_pif_custom_lock;
static pthread_once_t g_fd_meta_atfork_once = PTHREAD_ONCE_INIT;

static void prepare_fd_meta_fork() {
    g_pif_custom_lock.lock();
}
static void parent_fd_meta_fork() {
    g_pif_custom_lock.unlock();
}
static void child_fd_meta_fork() {
    g_pif_custom_lock.init(false);
}

static void register_fd_meta_atfork() {
    pthread_atfork(prepare_fd_meta_fork, parent_fd_meta_fork, child_fd_meta_fork);
}

template <typename T>
static T* get_fd_table(_Atomic(T*)* slot, bool create) {
    T* table = atomic_load_explicit(slot, memory_order_acquire);
    if (table || !create) return table;

    void* mem = mmap(nullptr, sizeof(T), PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mem == MAP_FAILED) return nullptr;
    T* fresh = static_cast<T*>(mem);
    if (atomic_compare_exchange_strong_explicit(slot, &table, fresh, memory_order_acq_rel,
                                                memory_order_acquire)) {
        return fresh;
    }
    munmap(fresh, sizeof(T));
    return table;
}

static FdPage* get_fd_page(int fd, bool create = false) {
    if (fd < 0) return nullptr;
    unsigned index = static_cast<unsigned>(fd);
    auto* directory = get_fd_table<FdDirectory>(
            &g_fd_directories[index >> (kFdPageBits + kFdTableBits * 2)], create);
    if (!directory) return nullptr;
    auto* table = get_fd_table<FdPageTable>(
            &directory->tables[(index >> (kFdPageBits + kFdTableBits)) & kFdTableMask], create);
    if (!table) return nullptr;
    return get_fd_table<FdPage>(&table->pages[(index >> kFdPageBits) & kFdTableMask], create);
}

static bool is_tracked_fd(int fd) {
    FdPage* page = get_fd_page(fd);
    if (!page) return false;
    unsigned index = static_cast<unsigned>(fd) & kFdPageMask;
    uint64_t bit = 1ULL << index;
    return (atomic_load_explicit(&page->tracked, memory_order_acquire) & bit) != 0;
}

static void set_fd_tracking(int fd, bool tracked, const FdMeta* meta = nullptr) {
    if (!tracked && !is_tracked_fd(fd)) return;
    int saved_errno = errno;
    FdPage* page = get_fd_page(fd, tracked);
    if (!page) {
        errno = saved_errno;
        return;
    }

    unsigned index = static_cast<unsigned>(fd) & kFdPageMask;
    uint64_t bit = 1ULL << index;

    if (!tracked) {
        atomic_store_explicit(&page->meta_valid[index], false, memory_order_release);
        atomic_fetch_and_explicit(&page->tracked, ~bit, memory_order_release);
        errno = saved_errno;
        return;
    }

    uint32_t seq = atomic_load_explicit(&page->meta_seq[index], memory_order_relaxed);
    if ((seq & 1u) == 0 &&
        atomic_compare_exchange_strong_explicit(&page->meta_seq[index], &seq, seq + 1u,
                                                memory_order_acq_rel, memory_order_relaxed)) {
        atomic_thread_fence(memory_order_release);
        if (meta) {
            page->metadata[index] = *meta;
            atomic_store_explicit(&page->meta_valid[index], true, memory_order_relaxed);
        } else {
            atomic_store_explicit(&page->meta_valid[index], false, memory_order_relaxed);
        }
        atomic_store_explicit(&page->meta_seq[index], seq + 2u, memory_order_release);
    }
    atomic_fetch_or_explicit(&page->tracked, bit, memory_order_release);
    errno = saved_errno;
}

static bool load_fd_meta(int fd, FdMeta* out) {
    FdPage* page = get_fd_page(fd);
    if (!page) return false;
    unsigned index = static_cast<unsigned>(fd) & kFdPageMask;
    for (int attempt = 0; attempt < 4; ++attempt) {
        uint32_t s1 = atomic_load_explicit(&page->meta_seq[index], memory_order_acquire);
        if ((s1 & 1u) != 0) continue;
        bool valid = atomic_load_explicit(&page->meta_valid[index], memory_order_relaxed);
        FdMeta copy = {};
        if (valid) copy = page->metadata[index];
        atomic_thread_fence(memory_order_acquire);
        uint32_t s2 = atomic_load_explicit(&page->meta_seq[index], memory_order_relaxed);
        if (s1 == s2) {
            if (valid) *out = copy;
            return valid;
        }
    }
    return false;
}

void custom_rom_hide_unregister_fd(int fd) {
    set_fd_tracking(fd, false);
}

void custom_rom_hide_transfer_fd(int old_fd, int new_fd) {
    if (new_fd < 0 || old_fd == new_fd) return;
    if (is_tracked_fd(old_fd)) {
        FdMeta meta;
        set_fd_tracking(new_fd, true, load_fd_meta(old_fd, &meta) ? &meta : nullptr);
    } else {
        custom_rom_hide_unregister_fd(new_fd);
    }
}

static inline int raw_openat(const char* path, int flags) {
    return static_cast<int>(syscall(__NR_openat, AT_FDCWD, path, flags, 0));
}

static inline ssize_t raw_read(int fd, void* buf, size_t count) {
    return syscall(__NR_read, fd, buf, count);
}

static inline ssize_t raw_write(int fd, const void* buf, size_t count) {
    return syscall(__NR_write, fd, buf, count);
}

static inline int raw_close(int fd) {
    return static_cast<int>(syscall(__NR_close, fd));
}

static inline off_t raw_lseek(int fd, off_t offset, int whence) {
    return syscall(__NR_lseek, fd, offset, whence);
}

static inline int raw_memfd_create(const char* name, unsigned int flags) {
    return static_cast<int>(syscall(__NR_memfd_create, name, flags));
}

static inline ssize_t raw_readlinkat(const char* path, char* buf, size_t size) {
    return syscall(__NR_readlinkat, AT_FDCWD, path, buf, size);
}

static inline int raw_fstatat(int dirfd, const char* path, struct stat* sb, int flags) {
#if defined(__LP64__)
    return static_cast<int>(syscall(__NR_newfstatat, dirfd, path, sb, flags));
#else
    return static_cast<int>(syscall(__NR_fstatat64, dirfd, path, sb, flags));
#endif
}

static inline int raw_statx(int dirfd, const char* path, int flags, unsigned mask, struct statx* sx) {
    return static_cast<int>(syscall(__NR_statx, dirfd, path, flags, mask, sx));
}

static inline int raw_statfs(const char* path, struct statfs* sf) {
#if defined(__LP64__)
    return static_cast<int>(syscall(__NR_statfs, path, sf));
#else
    return static_cast<int>(syscall(__NR_statfs64, path, sizeof(*sf), sf));
#endif
}

static bool read_cmdline_name(char* out, size_t out_size) {
    if (out_size == 0) return false;
    int fd = raw_openat("/proc/self/cmdline", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return false;

    ssize_t n = raw_read(fd, out, out_size - 1);
    raw_close(fd);
    if (n <= 0) return false;

    out[n] = '\0';
    if (char* colon = strchr(out, ':')) *colon = '\0';
    return true;
}

static bool name_is_zygote(const char* name) {
    if (strcmp(name, "app_process") == 0 || strcmp(name, "app_process64") == 0 ||
        strcmp(name, "app_process32") == 0) return true;
    size_t len = strlen(name);
    static const char kZygoteSuffix[] = "_zygote";
    size_t slen = sizeof(kZygoteSuffix) - 1;
    if (len >= slen && strcmp(name + len - slen, kZygoteSuffix) == 0) return true;
    if (strcmp(name, "zygote") == 0 || strcmp(name, "zygote64") == 0) return true;
    if (strcmp(name, "usap32") == 0 || strcmp(name, "usap64") == 0) return true;
    if (strcmp(name, "<pre-initialized>") == 0) return true;
    return false;
}

static bool compute_exempt(bool* is_zygote) {
    *is_zygote = false;

    char name[256];
    if (!read_cmdline_name(name, sizeof(name)) || name[0] == '\0') {
        *is_zygote = true;
        return true;
    }

    if (name_is_zygote(name)) { *is_zygote = true; return true; }

    for (const char* const* p = kAllowlistedPackages; *p; ++p) {
        if (strcmp(name, *p) == 0) return true;
    }
    return false;
}

static constexpr uint64_t kPidCacheValidBit = 2ULL;
static constexpr uint64_t kPidCacheValueBit = 1ULL;

static inline uint64_t pack_pid_bool_cache(pid_t pid, bool value) {
    return (static_cast<uint64_t>(static_cast<uint32_t>(pid)) << 2) |
           kPidCacheValidBit | (value ? kPidCacheValueBit : 0ULL);
}

static inline bool unpack_pid_bool_cache(uint64_t word, pid_t cur, bool* out) {
    if ((word & kPidCacheValidBit) == 0 ||
        static_cast<pid_t>(static_cast<uint32_t>(word >> 2)) != cur) {
        return false;
    }
    *out = (word & kPidCacheValueBit) != 0;
    return true;
}

static bool is_exempt_process() {
    static _Atomic(uint64_t) cached_state = 0;
    pid_t cur = getpid();
    bool cached_value = false;
    if (unpack_pid_bool_cache(atomic_load_explicit(&cached_state, memory_order_acquire),
                              cur, &cached_value)) {
        return cached_value;
    }

    bool is_zygote = false;
    bool result = compute_exempt(&is_zygote);
    if (!is_zygote) {
        atomic_store_explicit(&cached_state, pack_pid_bool_cache(cur, result),
                              memory_order_release);
    }
    return result;
}

bool custom_rom_hide_is_app_process() {
    // Read the calling thread's live real UID once per libc operation. Raw setuid
    // syscalls can change it without passing through a libc invalidation hook.
    if ((getuid() % AID_USER_OFFSET) < AID_APP_START) return false;
    const int saved_errno = errno;
    const bool is_app = !is_exempt_process();
    errno = saved_errno;
    return is_app;
}

// Dynamic prop overrides are only meant for DroidGuard, mirroring PIFork's scope.
// The process name is only final once ActivityThread has called Process.setArgV0(),
// before that cmdline still reads "zygote*" or "<pre-initialized>". Only cache
// once it is final so an early read can't pin the wrong answer for this pid.
#define DROIDGUARD_PROCESS_NAME "com.google.android.gms.unstable"

static bool compute_droidguard(bool* resolved) {
    *resolved = false;

    int fd = raw_openat("/proc/self/cmdline", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return false;

    char cmdline[256];
    ssize_t n = raw_read(fd, cmdline, sizeof(cmdline) - 1);
    raw_close(fd);
    if (n <= 0) return false;

    cmdline[n] = '\0';
    if (name_is_zygote(cmdline) || strncmp(cmdline, "zygote", 6) == 0) {
        return false;
    }

    *resolved = true;
    return strcmp(cmdline, DROIDGUARD_PROCESS_NAME) == 0;
}

static bool is_droidguard_process() {
    static _Atomic(uint64_t) cached_state = 0;

    pid_t cur = getpid();
    bool cached_value = false;
    if (unpack_pid_bool_cache(atomic_load_explicit(&cached_state, memory_order_acquire),
                              cur, &cached_value)) {
        return cached_value;
    }

    bool resolved = false;
    bool result = compute_droidguard(&resolved);
    if (resolved) {
        atomic_store_explicit(&cached_state, pack_pid_bool_cache(cur, result),
                              memory_order_release);
    }
    return result;
}

static const char* path_basename(const char* path) {
    const char* slash = strrchr(path, '/');
    return slash ? slash + 1 : path;
}

static bool path_parent_equals(const char* path, const char* parent, size_t plen) {
    if (strncmp(path, parent, plen) != 0) return false;
    return path[plen] == '/';
}

static bool basename_is_rom_artifact(const char* name) {
    for (const PrefixEntry* p = kRomArtifactPrefixes; p->str; ++p) {
        if (strncmp(name, p->str, p->len) == 0) return true;
    }
    return false;
}

static bool name_has_rom_keyword(const char* name) {
    for (const PrefixEntry* kw = kProcFilterKeywords; kw->str; ++kw) {
        if (strstr(name, kw->str) != nullptr) return true;
    }
    return false;
}

static bool dir_is_config(const char* dir_path) {
    for (const PrefixEntry* d = kConfigDirs; d->str; ++d) {
        if (strcmp(dir_path, d->str) == 0) return true;
    }
    return false;
}

static bool is_rom_framework_artifact(const char* path) {
    const char* rest = nullptr;
    for (const PrefixEntry* d = kFrameworkDirs; d->str; ++d) {
        if (strncmp(path, d->str, d->len) == 0 && path[d->len] == '/') {
            rest = path + d->len + 1;
            break;
        }
    }
    if (!rest) return false;
    const char* slash = strrchr(rest, '/');
    return basename_is_rom_artifact(slash ? slash + 1 : rest);
}

static bool is_rom_overlay(const char* path) {
    const char* rest = nullptr;
    for (const PrefixEntry* d = kOverlayDirs; d->str; ++d) {
        if (strncmp(path, d->str, d->len) == 0 && path[d->len] == '/') {
            rest = path + d->len + 1;
            break;
        }
    }
    if (!rest) return false;
    const char* slash = strrchr(rest, '/');
    const char* base = slash ? slash + 1 : rest;
    return basename_is_rom_artifact(base) || name_has_rom_keyword(base);
}

static bool is_blocked_dir(const char* path) {
    const char* base = path_basename(path);

    bool name_match = false;
    for (const char* const* dn = kBlockedDirnames; *dn; ++dn) {
        if (strcmp(base, *dn) == 0) { name_match = true; break; }
    }
    if (!name_match) return false;

    for (const PrefixEntry* pp = kDirParents; pp->str; ++pp) {
        if (path_parent_equals(path, pp->str, pp->len)) return true;
    }
    return false;
}

static bool is_rom_path(const char* path) {
    if (!path || path[0] != '/') return false;

    size_t len = strlen(path);
    bool has_trailing = len > 1 && path[len - 1] == '/';
    char stack_buf[512];
    const char* clean = path;
    if (has_trailing) {
        if (len >= sizeof(stack_buf)) len = sizeof(stack_buf) - 1;
        memcpy(stack_buf, path, len);
        while (len > 1 && stack_buf[len - 1] == '/') len--;
        stack_buf[len] = '\0';
        clean = stack_buf;
    }

    if (is_blocked_dir(clean)) return true;
    if (is_rom_framework_artifact(clean)) return true;
    return false;
}

static bool resolve_fd_path(int fd, char* buf, size_t size) {
    char proc_link[64];
    if (fd < 0 || !buf || size < 2) return false;
    snprintf(proc_link, sizeof(proc_link), "/proc/self/fd/%d", fd);
    ssize_t n = raw_readlinkat(proc_link, buf, size - 1);
    if (n > 0) {
        buf[n] = '\0';
        return true;
    }
    return false;
}

bool custom_rom_hide_should_block(const char* path) {
    if (!path || reinterpret_cast<uintptr_t>(path) < 0x1000000) return false;
    if (path[0] != '/') return false;
    return is_rom_path(path);
}

bool custom_rom_hide_should_block_at(int dirfd, const char* path) {
    if (!path || reinterpret_cast<uintptr_t>(path) < 0x1000000) return false;

    int saved_errno = errno;
    bool result = false;

    if (path[0] == '/') {
        result = is_rom_path(path);
    } else if (dirfd != AT_FDCWD) {
        size_t plen = strlen(path);
        bool candidate = plen > 0 && path[plen - 1] == '/';
        if (!candidate) {
            const char* base = path_basename(path);
            for (const char* const* dn = kBlockedDirnames; *dn; ++dn) {
                if (strcmp(base, *dn) == 0) { candidate = true; break; }
            }
            if (!candidate && basename_is_rom_artifact(base)) candidate = true;
        }
        if (candidate) {
            char dir_path[256];
            if (resolve_fd_path(dirfd, dir_path, sizeof(dir_path))) {
                char full_path[512];
                int n = snprintf(full_path, sizeof(full_path), "%s/%s", dir_path, path);
                if (n > 0 && static_cast<size_t>(n) < sizeof(full_path)) {
                    result = is_rom_path(full_path);
                }
            }
        }
    }

    errno = saved_errno;
    return result;
}

bool custom_rom_hide_is_symlink(const char* path) {
    int saved_errno = errno;
    struct stat sb;
    bool result = raw_fstatat(AT_FDCWD, path, &sb, AT_SYMLINK_NOFOLLOW) == 0 && S_ISLNK(sb.st_mode);
    errno = saved_errno;
    return result;
}

bool custom_rom_hide_should_filter_dirent(int dirfd, const char* name) {
    if (!name || reinterpret_cast<uintptr_t>(name) < 0x1000000) return false;

    if (name[0] == '.' && (name[1] == '\0'
            || (name[1] == '.' && name[2] == '\0'))) {
        return false;
    }

    bool maybe = false;
    for (const char* const* dn = kBlockedDirnames; *dn; ++dn) {
        if (strcmp(name, *dn) == 0) { maybe = true; break; }
    }
    if (!maybe && basename_is_rom_artifact(name)) maybe = true;
    if (!maybe && name_has_rom_keyword(name)) maybe = true;
    if (!maybe) return false;

    int saved_errno = errno;
    bool result = false;

    char dir_path[384];
    if (resolve_fd_path(dirfd, dir_path, sizeof(dir_path))) {
        char full_path[640];
        int n = snprintf(full_path, sizeof(full_path), "%s/%s", dir_path, name);
        if (n > 0 && static_cast<size_t>(n) < sizeof(full_path)) {
            // Overlays are hidden from listings only: apps open their own RROs by path.
            result = is_rom_path(full_path) || is_rom_overlay(full_path) ||
                     (dir_is_config(dir_path) && name_has_rom_keyword(name));
        }
    }

    errno = saved_errno;
    return result;
}

// Descriptor links expose the resolved proc path, not the alias used to open it.
static const char* canonicalize_proc_path(const char* path, char* resolved, size_t size) {
    if (strncmp(path, "/proc/", 6) != 0) return path;

    int saved_errno = errno;
    int fd = raw_openat(path, O_PATH | O_CLOEXEC);
    if (fd >= 0) {
        if (resolve_fd_path(fd, resolved, size)) path = resolved;
        raw_close(fd);
    }
    errno = saved_errno;
    return path;
}

static int create_encoded_memfd(const char* path) {
    char resolved_path[512];
    path = canonicalize_proc_path(path, resolved_path, sizeof(resolved_path));

    char memfd_name[250];
    int n = snprintf(memfd_name, sizeof(memfd_name), HIDE_MEMFD_NAME_PREFIX "%s", path);
    if (n < 0 || static_cast<size_t>(n) >= sizeof(memfd_name)) {
        errno = ENAMETOOLONG;
        return -1;
    }
    int fd = raw_memfd_create(memfd_name, 0);
    if (fd >= 0) {
        int saved_errno = errno;
        FdMeta meta = {};
        meta.sb_ok = raw_fstatat(AT_FDCWD, path, &meta.sb, 0) == 0;
        // Older kernels can reject the newest mask bits; STATX_ALL is the compatibility floor.
        meta.sx_ok = raw_statx(AT_FDCWD, path, 0, kStatxCaptureMask, &meta.sx) == 0;
        if (!meta.sx_ok && errno == EINVAL) {
            meta.sx_ok = raw_statx(AT_FDCWD, path, 0, STATX_ALL, &meta.sx) == 0;
        }
        set_fd_tracking(fd, true, (meta.sb_ok || meta.sx_ok) ? &meta : nullptr);
        errno = saved_errno;
    }
    return fd;
}

static bool decode_encoded_memfd_link(const char* link, char* out, size_t out_size) {
    if (!link || !out || out_size == 0) return false;
    if (strncmp(link, HIDE_MEMFD_LINK_PREFIX, HIDE_MEMFD_LINK_PREFIX_LEN) != 0) return false;

    const char* real_path = link + HIDE_MEMFD_LINK_PREFIX_LEN;
    size_t real_len = strlen(real_path);
    const char* deleted_suffix = strstr(real_path, " (deleted)");
    if (deleted_suffix) real_len = static_cast<size_t>(deleted_suffix - real_path);
    if (real_len == 0 || real_len >= out_size) return false;

    memcpy(out, real_path, real_len);
    out[real_len] = '\0';
    return true;
}

static bool resolve_encoded_memfd_path(int fd, char* out, size_t out_size) {
    if (!is_tracked_fd(fd)) return false;

    char fd_path[512];
    if (!resolve_fd_path(fd, fd_path, sizeof(fd_path))) return false;
    bool decoded = decode_encoded_memfd_link(fd_path, out, out_size);
    if (!decoded) custom_rom_hide_unregister_fd(fd);
    return decoded;
}

static bool is_tracked_proc_fd_link(const char* path) {
    if (!path) return false;
    const char* number = nullptr;
    if (strncmp(path, "/proc/self/fd/", 14) == 0) number = path + 14;
    else if (strncmp(path, "/proc/thread-self/fd/", 21) == 0) number = path + 21;
    else if (strncmp(path, "/proc/", 6) == 0) {
        const char* p = path + 6;
        char* next = nullptr;
        long pid = strtol(p, &next, 10);
        if (p == next || pid != getpid() || strncmp(next, "/fd/", 4) != 0) return false;
        number = next + 4;
    }
    if (!number || *number < '0' || *number > '9') return false;
    char* end = nullptr;
    errno = 0;
    long fd = strtol(number, &end, 10);
    return errno == 0 && *end == '\0' && fd >= 0 && fd <= INT_MAX &&
           is_tracked_fd(static_cast<int>(fd));
}

ssize_t custom_rom_hide_readlinkat_post(int dirfd, const char* path, char* buf,
                                        size_t size, ssize_t ret) {
    if (ret <= 0 || !buf) return ret;
    int saved_errno = errno;
    bool has_prefix = ret >= static_cast<ssize_t>(HIDE_MEMFD_LINK_PREFIX_LEN) &&
                      memcmp(buf, HIDE_MEMFD_LINK_PREFIX, HIDE_MEMFD_LINK_PREFIX_LEN) == 0;
    if (!has_prefix && !is_tracked_proc_fd_link(path)) {
        errno = saved_errno;
        return ret;
    }

    char link[512];
    ssize_t n = syscall(__NR_readlinkat, dirfd, path, link, sizeof(link) - 1);
    if (n <= 0 || static_cast<size_t>(n) >= sizeof(link) - 1) {
        errno = saved_errno;
        return ret;
    }
    link[n] = '\0';
    char real_path[512];
    if (!decode_encoded_memfd_link(link, real_path, sizeof(real_path))) {
        errno = saved_errno;
        return ret;
    }
    size_t path_len = strlen(real_path);
    size_t to_copy = path_len < size ? path_len : size;
    memcpy(buf, real_path, to_copy);
    errno = saved_errno;
    return static_cast<ssize_t>(to_copy);
}

enum ProcFilterType {
    PROC_FILTER_NONE, PROC_FILTER_MAPS, PROC_FILTER_MOUNTS,
    PROC_FILTER_MOUNTINFO, PROC_FILTER_FILESYSTEMS, PROC_FILTER_CMDLINE,
};

static ProcFilterType get_proc_filter_type(const char* path) {
    if (!path || reinterpret_cast<uintptr_t>(path) < 0x1000000) return PROC_FILTER_NONE;
    if (strcmp(path, "/proc/cmdline") == 0) return PROC_FILTER_CMDLINE;
    if (strcmp(path, "/proc/filesystems") == 0) return PROC_FILTER_FILESYSTEMS;
    if (strncmp(path, "/proc/", 6) != 0) return PROC_FILTER_NONE;

    const char* leaf = nullptr;
    if (strncmp(path, "/proc/self/", 11) == 0) leaf = path + 11;
    else if (strncmp(path, "/proc/thread-self/", 18) == 0) leaf = path + 18;
    else {
        const char* p = path + 6;
        while (*p >= '0' && *p <= '9') p++;
        if (*p == '/' && *(p + 1) != '\0') leaf = p + 1;
        else leaf = path + 6;
    }

    if (!leaf) return PROC_FILTER_NONE;

    const char* leaf_base = strrchr(leaf, '/');
    leaf_base = leaf_base ? leaf_base + 1 : leaf;

    if (strcmp(leaf_base, "maps") == 0 || strcmp(leaf_base, "smaps") == 0) return PROC_FILTER_MAPS;
    if (strcmp(leaf_base, "mounts") == 0) return PROC_FILTER_MOUNTS;
    if (strcmp(leaf_base, "mountinfo") == 0) return PROC_FILTER_MOUNTINFO;

    return PROC_FILTER_NONE;
}

static bool line_has_blocked_segment(const char* line) {
    const char* path = strchr(line, '/');
    if (!path) return false;

    if (is_rom_framework_artifact(path)) return true;
    if (is_rom_overlay(path)) return true;

    for (const PrefixEntry* kw = kProcFilterKeywords; kw->str; ++kw) {
        const char* p = path;
        while ((p = strstr(p, kw->str)) != nullptr) {
            char before = (p == line) ? '/' : p[-1];
            char after = p[kw->len];
            bool lb = before == '/' || before == ' ' || before == '\0';
            bool rb = after == '/' || after == ' ' || after == '.' || after == '\0' || after == '\n';
            if (lb && rb) return true;
            p += kw->len;
        }
    }
    return false;
}

static bool line_contains_any(const char* line, const char* const* keywords) {
    for (const char* const* kw = keywords; *kw; ++kw) {
        if (strstr(line, *kw) != nullptr) return true;
    }
    return false;
}

static bool should_filter_line(ProcFilterType type, const char* line) {
    switch (type) {
        case PROC_FILTER_MAPS: return line_has_blocked_segment(line);
        case PROC_FILTER_MOUNTS:
        case PROC_FILTER_MOUNTINFO: return line_contains_any(line, kMountFilterKeywords);
        case PROC_FILTER_FILESYSTEMS: return strstr(line, "overlay") != nullptr;
        default: return false;
    }
}

static char* read_file_raw(const char* path, size_t* out_size) {
    int fd = raw_openat(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return nullptr;

    constexpr size_t kMaxFileBytes = 64 * 1024 * 1024;
    size_t capacity = 16384;
    size_t size = 0;
    char* buf = static_cast<char*>(malloc(capacity));
    if (!buf) { raw_close(fd); return nullptr; }

    while (true) {
        if (size == capacity - 1) {
            if (capacity >= kMaxFileBytes + 1) {
                errno = EFBIG;
                break;
            }
            size_t grown = capacity * 2;
            if (grown > kMaxFileBytes + 1) grown = kMaxFileBytes + 1;
            char* next = static_cast<char*>(realloc(buf, grown));
            if (!next) break;
            buf = next;
            capacity = grown;
        }
        ssize_t n = raw_read(fd, buf + size, capacity - size - 1);
        if (n > 0) { size += static_cast<size_t>(n); continue; }
        if (n == 0) {
            buf[size] = '\0';
            raw_close(fd);
            *out_size = size;
            return buf;
        }
        if (errno == EINTR) continue;
        break;
    }
    int saved_errno = errno;
    free(buf);
    raw_close(fd);
    errno = saved_errno;
    return nullptr;
}

typedef bool (*LinePredicate)(const char* line, void* ctx);

static bool raw_write_all(int fd, const void* buffer, size_t size) {
    const char* data = static_cast<const char*>(buffer);
    while (size != 0) {
        ssize_t n = raw_write(fd, data, size);
        if (n > 0) {
            size -= static_cast<size_t>(n);
            data += n;
            continue;
        }
        if (n < 0 && errno == EINTR) continue;
        if (n == 0) errno = EIO;
        return false;
    }
    return true;
}

class BufferedOutput {
  public:
    explicit BufferedOutput(int fd) : fd_(fd), buffer_(static_cast<char*>(malloc(kCapacity))) {}
    ~BufferedOutput() { free(buffer_); }

    bool append(const char* data, size_t size) {
        if (size == 0) return true;
        if (!buffer_) return raw_write_all(fd_, data, size);
        if (size > kCapacity - used_ && !flush()) return false;
        if (size >= kCapacity) return raw_write_all(fd_, data, size);
        memcpy(buffer_ + used_, data, size);
        used_ += size;
        return true;
    }

    bool flush() {
        if (used_ == 0) return true;
        if (!raw_write_all(fd_, buffer_, used_)) return false;
        used_ = 0;
        return true;
    }

  private:
    static constexpr size_t kCapacity = 64 * 1024;
    int fd_;
    char* buffer_;
    size_t used_ = 0;
};

using LineWriter = bool (*)(BufferedOutput& output, char* line, size_t line_len, void* ctx);

static int filter_file_with(const char* path, LinePredicate drop, LineWriter writer, void* ctx) {
    size_t file_size = 0;
    char* content = read_file_raw(path, &file_size);
    if (!content) return -1;

    int mem_fd = create_encoded_memfd(path);
    if (mem_fd < 0) {
        free(content);
        return -1;
    }

    BufferedOutput output(mem_fd);
    bool ok = true;
    char* pos = content;
    char* end = content + file_size;
    while (pos < end) {
        char* eol = static_cast<char*>(memchr(pos, '\n', end - pos));
        size_t line_len = eol ? static_cast<size_t>(eol - pos + 1)
                              : static_cast<size_t>(end - pos);
        char saved = pos[line_len];
        pos[line_len] = '\0';
        if ((!drop || !drop(pos, ctx)) &&
            !(writer ? writer(output, pos, line_len, ctx) : output.append(pos, line_len))) {
            ok = false;
        }
        pos[line_len] = saved;
        if (!ok) break;
        pos += line_len;
    }

    free(content);
    if (ok && output.flush() && raw_lseek(mem_fd, 0, SEEK_SET) >= 0) return mem_fd;
    int saved_errno = errno;
    custom_rom_hide_unregister_fd(mem_fd);
    raw_close(mem_fd);
    errno = saved_errno;
    return -1;
}

static void replace_all_cmdline(char* content, size_t len, const char* needle, size_t needle_len,
                                const char* replacement, size_t replacement_len) {
    if (needle_len == 0 || needle_len != replacement_len) return;

    char* end = content + strnlen(content, len);
    for (char* p = content; p < end;) {
        char* hit = strstr(p, needle);
        if (!hit || hit >= end) break;
        memcpy(hit, replacement, needle_len);
        p = hit + needle_len;
    }
}

#define REPLACE_CMDLINE_LITERAL(content, len, needle, replacement) \
    do { \
        static_assert(sizeof(needle) == sizeof(replacement), \
                      "cmdline replacement must preserve byte length"); \
        replace_all_cmdline(content, len, needle, sizeof(needle) - 1, replacement, \
                            sizeof(replacement) - 1); \
    } while (false)

static bool filter_cmdline(int mem_fd, char* content, size_t len) {
    REPLACE_CMDLINE_LITERAL(content, len, "androidboot.verifiedbootstate=orange", "androidboot.verifiedbootstate=green ");
    REPLACE_CMDLINE_LITERAL(content, len, "androidboot.verifiedbootstate=yellow", "androidboot.verifiedbootstate=green ");
    REPLACE_CMDLINE_LITERAL(content, len, "androidboot.flash.locked=0", "androidboot.flash.locked=1");
    REPLACE_CMDLINE_LITERAL(content, len, "androidboot.vbmeta.device_state=unlocked", "androidboot.vbmeta.device_state=locked  ");
    return raw_write_all(mem_fd, content, strnlen(content, len));
}

struct MountDm { const char* mnt; const char* dev; };
static const MountDm kMountDm[] = {
    { " /system ",     "/dev/block/dm-0" },
    { " /vendor ",     "/dev/block/dm-1" },
    { " /product ",    "/dev/block/dm-2" },
    { " /system_ext ", "/dev/block/dm-3" },
    { " /odm ",        "/dev/block/dm-4" },
    { nullptr,         nullptr },
};

static bool write_spoofed_mount_line(BufferedOutput& output, char* line, size_t line_len, void*) {
    const char* replacement = nullptr;
    for (const MountDm* m = kMountDm; m->mnt; ++m) {
        if (strstr(line, m->mnt)) { replacement = m->dev; break; }
    }
    if (!replacement &&
        (strstr(line, " / / ") || strstr(line, " / ext4") ||
         strstr(line, " / erofs") || strstr(line, " / f2fs"))) {
        replacement = "/dev/block/dm-0";
    }

    const bool is_ro_system_mount = replacement != nullptr && !strstr(line, "/dev/block/loop");
    if (is_ro_system_mount) {
        char* rw_delim = strstr(line, ",rw,");
        if (rw_delim) { rw_delim[1] = 'r'; rw_delim[2] = 'o'; }
        rw_delim = strstr(line, " rw,");
        if (rw_delim) { rw_delim[1] = 'r'; rw_delim[2] = 'o'; }
        rw_delim = strstr(line, ",rw ");
        if (rw_delim) { rw_delim[1] = 'r'; rw_delim[2] = 'o'; }

        char* dev_start = strstr(line, "/dev/block/");
        if (!dev_start) dev_start = strstr(line, "/dev/root");

        if (dev_start) {
            char* dev_end = strchr(dev_start, ' ');
            if (!dev_end) dev_end = dev_start + strlen(dev_start);
            return output.append(line, dev_start - line) &&
                   output.append(replacement, strlen(replacement)) &&
                   output.append(dev_end, line_len - (dev_end - line));
        }
    }
    return output.append(line, line_len);
}

static bool drop_proc_line(const char* line, void* ctx) {
    return should_filter_line(*static_cast<ProcFilterType*>(ctx), line);
}

int custom_rom_hide_filter_proc(const char* path) {
    if (!path || reinterpret_cast<uintptr_t>(path) < 0x1000000) return -1;

    int saved_errno = errno;
    ProcFilterType type = get_proc_filter_type(path);
    if (type == PROC_FILTER_NONE) { errno = saved_errno; return -1; }

    if (type != PROC_FILTER_CMDLINE) {
        LineWriter writer = (type == PROC_FILTER_MOUNTS || type == PROC_FILTER_MOUNTINFO)
                ? write_spoofed_mount_line : nullptr;
        int mem_fd = filter_file_with(path, drop_proc_line, writer, &type);
        errno = saved_errno;
        return mem_fd;
    }

    size_t file_size = 0;
    char* content = read_file_raw(path, &file_size);
    if (!content) { errno = saved_errno; return -1; }

    int mem_fd = create_encoded_memfd(path);
    if (mem_fd < 0) { free(content); errno = saved_errno; return -1; }

    bool ok = filter_cmdline(mem_fd, content, file_size);
    free(content);
    if (!ok || raw_lseek(mem_fd, 0, SEEK_SET) < 0) {
        custom_rom_hide_unregister_fd(mem_fd);
        raw_close(mem_fd);
        errno = saved_errno;
        return -1;
    }
    errno = saved_errno;
    return mem_fd;
}

static bool is_selinux_policy_path(const char* path) {
    static const PrefixEntry kSelinuxDirs[] = {
        PE("/system/etc/selinux"), PE("/system_ext/etc/selinux"),
        PE("/product/etc/selinux"), PE("/vendor/etc/selinux"),
        PE("/odm/etc/selinux"), {nullptr, 0}
    };
    bool in_system_policy_dir = false;
    for (const PrefixEntry* entry = kSelinuxDirs; entry->str; ++entry) {
        if (strncmp(path, entry->str, entry->len) == 0 && path[entry->len] == '/') {
            in_system_policy_dir = true;
            break;
        }
    }
    if (!in_system_policy_dir) return false;
    const char* base = path_basename(path);
    return strstr(base, "_contexts") != nullptr ||
           strstr(base, "sepolicy.cil") != nullptr;
}

static bool line_has_rom_keyword(const char* line) {
    for (const PrefixEntry* kw = kProcFilterKeywords; kw->str; ++kw) {
        if (strstr(line, kw->str) != nullptr) return true;
    }
    return false;
}

static bool drop_sepolicy_line(const char* line, void*) {
    return line_has_rom_keyword(line);
}

int custom_rom_hide_filter_sepolicy(const char* path) {
    if (!path || reinterpret_cast<uintptr_t>(path) < 0x1000000) return -1;

    int saved_errno = errno;
    if (!is_selinux_policy_path(path)) { errno = saved_errno; return -1; }

    int mem_fd = filter_file_with(path, drop_sepolicy_line, nullptr, nullptr);
    errno = saved_errno;
    return mem_fd;
}

#ifndef CUSTOM_ROM_HIDE_FILTER_VINTF
#define CUSTOM_ROM_HIDE_FILTER_VINTF 1
#endif

#if CUSTOM_ROM_HIDE_FILTER_VINTF
static const char* const kVintfFilterPaths[] = {
    "/system/etc/vintf/compatibility_matrix.xml", "/system/etc/vintf/compatibility_matrix.device.xml",
    "/vendor/etc/vintf/compatibility_matrix.xml", "/vendor/etc/vintf/compatibility_matrix.device.xml",
    "/product/etc/vintf/compatibility_matrix.xml", "/product/etc/vintf/compatibility_matrix.device.xml",
    "/system_ext/etc/vintf/compatibility_matrix.xml", "/system_ext/etc/vintf/compatibility_matrix.device.xml",
    "/odm/etc/vintf/compatibility_matrix.xml", "/odm/etc/vintf/compatibility_matrix.device.xml",
    "/system/etc/vintf/manifest.xml", "/vendor/etc/vintf/manifest.xml", "/product/etc/vintf/manifest.xml",
    "/system_ext/etc/vintf/manifest.xml", "/odm/etc/vintf/manifest.xml", nullptr
};

static const char* const kVintfFilterKeywords[] = {
    "shinkai", "Shinkai", "pixelos", "PixelOS",
    "lineage", "Lineage", "evolution", "Evolution", nullptr
};
#endif

static bool contains_keyword_n(const char* buf, size_t len, const char* const* keywords) {
    for (const char* const* kw = keywords; *kw; ++kw) {
        size_t kw_len = strlen(*kw);
        if (kw_len > 0 && kw_len <= len && memmem(buf, len, *kw, kw_len) != nullptr) {
            return true;
        }
    }
    return false;
}

static bool write_vintf_non_hal_span(BufferedOutput& output, const char* span, size_t len) {
    const char* pos = span;
    const char* end = span + len;
    while (pos < end) {
        const char* eol = static_cast<const char*>(memchr(pos, '\n', end - pos));
        size_t line_len = eol ? static_cast<size_t>(eol - pos + 1)
                              : static_cast<size_t>(end - pos);
        if (!contains_keyword_n(pos, line_len, kVintfFilterKeywords)) {
            if (!output.append(pos, line_len)) return false;
        }
        pos += line_len;
    }
    return true;
}

int custom_rom_hide_filter_vintf(const char* path) {
#if !CUSTOM_ROM_HIDE_FILTER_VINTF
    (void) path;
    return -1;
#else
    if (!path || reinterpret_cast<uintptr_t>(path) < 0x1000000) return -1;

    int saved_errno = errno;
    bool match = false;
    for (const char* const* p = kVintfFilterPaths; *p; ++p) {
        if (strcmp(path, *p) == 0) { match = true; break; }
    }
    if (!match) { errno = saved_errno; return -1; }

    size_t file_size = 0;
    char* content = read_file_raw(path, &file_size);
    if (!content) { errno = saved_errno; return -1; }

    int mem_fd = create_encoded_memfd(path);
    if (mem_fd < 0) {
        free(content);
        errno = saved_errno;
        return -1;
    }

    BufferedOutput output(mem_fd);
    bool ok = true;
    const char* span_start = content;
    const char* scan = content;
    const char* end = content + file_size;

    while (scan < end) {
        const char* tag_pos = static_cast<const char*>(memmem(scan, end - scan, "<hal", 4));
        if (!tag_pos) break;
        if (tag_pos + 4 >= end) {
            ok = false;
            break;
        }
        char after = tag_pos[4];
        if (after != ' ' && after != '\t' && after != '\r' && after != '\n' &&
            after != '>' && after != '/') {
            scan = tag_pos + 4;
            continue;
        }

        if (!write_vintf_non_hal_span(output, span_start, static_cast<size_t>(tag_pos - span_start))) {
            ok = false;
            break;
        }

        const char* open_end = static_cast<const char*>(
                memchr(tag_pos + 4, '>', end - (tag_pos + 4)));
        if (!open_end) {
            ok = false;
            break;
        }

        const char* block_end = nullptr;
        if (open_end[-1] == '/') {
            block_end = open_end + 1;
        } else {
            const char* close_tag = static_cast<const char*>(
                    memmem(open_end + 1, end - (open_end + 1), "</hal>", 6));
            if (!close_tag) {
                ok = false;
                break;
            }
            block_end = close_tag + 6;
        }

        if (block_end + 1 < end && block_end[0] == '\r' && block_end[1] == '\n') {
            block_end += 2;
        } else if (block_end < end && block_end[0] == '\n') {
            block_end += 1;
        }

        size_t block_len = static_cast<size_t>(block_end - tag_pos);
        if (!contains_keyword_n(tag_pos, block_len, kVintfFilterKeywords)) {
            if (!output.append(tag_pos, block_len)) {
                ok = false;
                break;
            }
        }
        span_start = block_end;
        scan = block_end;
    }

    if (ok && span_start < end) {
        ok = write_vintf_non_hal_span(output, span_start, static_cast<size_t>(end - span_start));
    }

    free(content);
    if (ok && output.flush() && raw_lseek(mem_fd, 0, SEEK_SET) >= 0) {
        errno = saved_errno;
        return mem_fd;
    }
    custom_rom_hide_unregister_fd(mem_fd);
    raw_close(mem_fd);
    errno = saved_errno;
    return -1;
#endif
}

static const char* const kSpoofedEmptyProps[] = {
    "ro.shinkai.version", "ro.shinkai.build.date", "ro.shinkai.maintainer",
    "ro.custom.version", "ro.custom.build.date", "ro.custom.device", "ro.custom.fingerprint",
    "net.shinkai.version", "net.shinkai.build_type", "net.pixelos.version",
    "ro.evolution.version", "ro.evolution.build.version", "ro.evolution.display.version",
    "ro.lineage.version", "ro.lineage.display.version", "ro.lineage.build.version",
    "ro.lineage.releasetype", "ro.lineage.device", "ro.lineagelegal.url",
    "ro.cm.build.version", "ro.modversion",
    "persist.sys.shinkai_debug_enabled", "persist.sys.pairip.activity.block",
    "init.svc_debug_pid.adb_root", "init.svc.adb_root", "service.adb.root", nullptr
};

struct PropOverride { const char* name; const char* value; };
static const PropOverride kSpoofedValueProps[] = {
    {"ro.debuggable", "0"},
    {"ro.build.type", "user"},
    {"ro.build.tags", "release-keys"},
    {"ro.system.build.type", "user"},
    {"ro.system.build.tags", "release-keys"},
    {"ro.vendor.build.type", "user"},
    {"ro.vendor.build.tags", "release-keys"},
    {"ro.secure", "1"},
    {"ro.adb.secure", "1"},
    // Boot state as stock reports it on a locked device, matching the cmdline
    // rewrite in filter_cmdline(). App processes only, so
    // system_server's OemLock/PersistentDataBlock checks still see the real state.
    {"ro.boot.verifiedbootstate", "green"},
    {"vendor.boot.verifiedbootstate", "green"},
    {"ro.boot.vbmeta.device_state", "locked"},
    {"vendor.boot.vbmeta.device_state", "locked"},
    {"ro.boot.flash.locked", "1"},
    {"ro.boot.veritymode", "enforcing"},
    {"ro.secureboot.lockstate", "locked"},
    {nullptr, nullptr}
};

// Read-only keys that mirror whatever AxSpoofManager staged into the matching
// persist.sys.pif.* prop after a fingerprint refresh. Unlike kSpoofedValueProps
// these have no fixed value — read at call time, only applied when the staging
// prop is actually set (empty = no PIF config loaded yet, so don't blank out the
// real device identity), and only served to the DroidGuard process.
struct DynamicPropOverride { const char* name; const char* staging_name; };
static const DynamicPropOverride kDynamicProductProps[] = {
    {"ro.product.manufacturer",        "persist.sys.pif.product.manufacturer"},
    {"ro.product.brand",               "persist.sys.pif.product.brand"},
    {"ro.product.model",               "persist.sys.pif.product.model"},
    {"ro.product.device",              "persist.sys.pif.product.device"},
    {"ro.product.name",                "persist.sys.pif.product.name"},
    {"ro.product.system.manufacturer", "persist.sys.pif.product.manufacturer"},
    {"ro.product.system.brand",        "persist.sys.pif.product.brand"},
    {"ro.product.system.model",        "persist.sys.pif.product.model"},
    {"ro.product.vendor.manufacturer", "persist.sys.pif.product.manufacturer"},
    {"ro.product.vendor.brand",        "persist.sys.pif.product.brand"},
    {"ro.product.vendor.model",        "persist.sys.pif.product.model"},
    {"ro.build.product",               "persist.sys.pif.product.device"},
    {"ro.build.description",           "persist.sys.pif.build.description"},
    {"ro.build.flavor",                "persist.sys.pif.build.flavor"},
    {nullptr, nullptr}
};

// ro.product.<partition>.<field> for every partition (system, vendor, odm, product,
// system_ext, the *_dlkm ones, ...), served from the same staged product identity as the
// table above. A stock Pixel reports one identity on all of them, and the ROM's own device
// and name would otherwise show through on the partitions that table doesn't list.
static const char* find_product_partition_staging(const char* name) {
    static const char kPrefix[] = "ro.product.";
    if (strncmp(name, kPrefix, sizeof(kPrefix) - 1) != 0) return nullptr;
    const char* partition = name + sizeof(kPrefix) - 1;
    const char* dot = partition;
    while (*dot && *dot != '.') ++dot;
    if (dot == partition || *dot != '.') return nullptr;  // needs "<partition>.<field>"
    const char* field = dot + 1;
    for (const char* c = field; *c; ++c) {
        if (*c == '.') return nullptr;
    }
    if (strcmp(field, "manufacturer") == 0) return "persist.sys.pif.product.manufacturer";
    if (strcmp(field, "brand") == 0) return "persist.sys.pif.product.brand";
    if (strcmp(field, "model") == 0) return "persist.sys.pif.product.model";
    if (strcmp(field, "device") == 0) return "persist.sys.pif.product.device";
    if (strcmp(field, "name") == 0) return "persist.sys.pif.product.name";
    return nullptr;
}

// PIFork's leading-* wildcard properties: every read-only prop ending in the
// suffix is served the same staged value, so partitions the table above would
// have to list one by one (vendor_dlkm, odm, bootimage, ...) are covered as
// well. Only "ro." keys match. That also keeps the persist.sys.pif.* staging
// props themselves out of the match, which end in these suffixes too and
// would send the staging read back through this lookup.
struct DynamicSuffixOverride { const char* suffix; size_t suffix_len; const char* staging_name; };
#define DYNAMIC_SUFFIX(suffix, staging) { suffix, sizeof(suffix) - 1, staging }
static const DynamicSuffixOverride kDynamicSuffixProps[] = {
    DYNAMIC_SUFFIX(".build.id",        "persist.sys.pif.build.id"),
    DYNAMIC_SUFFIX(".security_patch",  "persist.sys.pif.security_patch"),
    DYNAMIC_SUFFIX("api_level",        "persist.sys.pif.api_level"),
    // ro.build.version.real_security_patch, which ".security_patch" does not reach.
    DYNAMIC_SUFFIX(".real_security_patch", "persist.sys.pif.security_patch"),
    // The build type and tags of the partitions kSpoofedValueProps doesn't pin (odm, product,
    // system_ext, bootimage, ...), taken from the fingerprint instead of a fixed value.
    DYNAMIC_SUFFIX(".build.type",      "persist.sys.pif.build.type"),
    DYNAMIC_SUFFIX(".build.tags",      "persist.sys.pif.build.tags"),
    {nullptr, 0, nullptr}
};

// Fixed values served to DroidGuard only, as PIFork's property hook does. adbd
// and USB state are read by init, system_server and Settings, none of which are
// app processes, so they keep the real values. Only the property callback path
// applies these, like the dynamic tables above.
static const PropOverride kDroidGuardValueProps[] = {
    {"init.svc.adbd", "stopped"},
    {"sys.usb.state", "mtp"},
    {nullptr, nullptr}
};

static const DynamicSuffixOverride* find_dynamic_suffix_override(const char* name) {
    if (strncmp(name, "ro.", 3) != 0) return nullptr;
    size_t len = strlen(name);
    for (const DynamicSuffixOverride* o = kDynamicSuffixProps; o->suffix; ++o) {
        if (len > o->suffix_len && strcmp(name + len - o->suffix_len, o->suffix) == 0) return o;
    }
    return nullptr;
}

// The staging props only exist to feed the DroidGuard overrides above. Hide them
// from every other app process so a plain getprop can't reveal them; the override
// lookup itself runs inside DroidGuard and still reads them.
#define PIF_STAGING_PROP_PREFIX "persist.sys.pif."

static bool is_hidden_staging_prop(const char* name) {
    return strncmp(name, PIF_STAGING_PROP_PREFIX, sizeof(PIF_STAGING_PROP_PREFIX) - 1) == 0 &&
           !is_droidguard_process();
}

// Entries from the PIF config that the tables above don't cover: exact property names and
// leading-* suffix wildcards, like PIFork's jsonProps. AxSpoofManager stages them as
// persist.sys.pif.x.<i> = "name=value" ("*suffix=value" for a wildcard), sorted by key, with
// persist.sys.pif.x.count saying how many slots are live. Keep the names and the slot limit
// in sync with AxSpoofManager.
//
// Like PIFork an exact match beats every wildcard, and the first matching wildcard wins.
// A bare "*" is ignored, since it would match every property. Only called from the
// DroidGuard process, and never for the staging props themselves.
#define PIF_CUSTOM_COUNT_PROP "persist.sys.pif.x.count"
#define PIF_CUSTOM_SLOT_PREFIX "persist.sys.pif.x."
#define PIF_CUSTOM_SLOT_MAX 32

struct PifCustomSlot {
    char key[PROP_VALUE_MAX];
    char value[PROP_VALUE_MAX];
    size_t key_len;
    bool is_wildcard;
};
static _Atomic(uint32_t) g_pif_custom_serial = 0;
static _Atomic(int) g_pif_custom_count = -1; // -1 = uninitialized
static PifCustomSlot g_pif_custom_slots[PIF_CUSTOM_SLOT_MAX];

static const char* find_custom_prop_override(const char* name, char* buffer, bool wildcard) {
    if (strncmp(name, PIF_STAGING_PROP_PREFIX, sizeof(PIF_STAGING_PROP_PREFIX) - 1) == 0) {
        return nullptr;
    }

    const uint32_t area_serial = __system_property_area_serial();
    if (atomic_load_explicit(&g_pif_custom_count, memory_order_acquire) == 0 &&
        atomic_load_explicit(&g_pif_custom_serial, memory_order_acquire) == area_serial &&
        atomic_load_explicit(&g_pif_custom_count, memory_order_acquire) == 0) {
        return nullptr;
    }

    pthread_once(&g_fd_meta_atfork_once, register_fd_meta_atfork);
    g_pif_custom_lock.lock();

    int count = atomic_load_explicit(&g_pif_custom_count, memory_order_relaxed);
    uint32_t cached_serial = atomic_load_explicit(&g_pif_custom_serial, memory_order_relaxed);
    if (count < 0 || cached_serial != area_serial) {
        const uint32_t load_serial = __system_property_area_serial();
        atomic_store_explicit(&g_pif_custom_count, -1, memory_order_relaxed);
        atomic_store_explicit(&g_pif_custom_serial, load_serial, memory_order_release);

        int raw_count = 0;
        // This code is also linked into the loader, so stick to plain string operations.
        char raw[PROP_VALUE_MAX];
        if (__system_property_get(PIF_CUSTOM_COUNT_PROP, raw) > 0) {
            for (const char* c = raw; *c >= '0' && *c <= '9' && raw_count < 1000; ++c) {
                raw_count = raw_count * 10 + (*c - '0');
            }
            if (raw_count > PIF_CUSTOM_SLOT_MAX) raw_count = PIF_CUSTOM_SLOT_MAX;
        }

        int valid_count = 0;
        char slot[sizeof(PIF_CUSTOM_SLOT_PREFIX) + 3];
        memcpy(slot, PIF_CUSTOM_SLOT_PREFIX, sizeof(PIF_CUSTOM_SLOT_PREFIX) - 1);
        for (int i = 0; i < raw_count; ++i) {
            char* p = slot + sizeof(PIF_CUSTOM_SLOT_PREFIX) - 1;
            if (i >= 10) *p++ = static_cast<char>('0' + i / 10);
            *p++ = static_cast<char>('0' + i % 10);
            *p = '\0';

            char entry[PROP_VALUE_MAX];
            if (__system_property_get(slot, entry) <= 0) continue;
            char* eq = entry;
            while (*eq && *eq != '=') ++eq;
            if (*eq != '=') continue;
            *eq = '\0';
            const char* key = entry;
            const char* value = eq + 1;

            const bool is_wildcard = (key[0] == '*');
            const char* match_key = is_wildcard ? (key + 1) : key;
            const size_t key_len = strlen(match_key);
            if (is_wildcard && key_len == 0) continue;

            PifCustomSlot& dst = g_pif_custom_slots[valid_count];
            dst.is_wildcard = is_wildcard;
            dst.key_len = key_len;
            memcpy(dst.key, match_key, key_len + 1);
            const size_t val_len = strlen(value);
            memcpy(dst.value, value, val_len + 1);
            ++valid_count;
        }

        count = valid_count;
        atomic_store_explicit(&g_pif_custom_count, count, memory_order_release);
    }

    const char* result = nullptr;
    const size_t name_len = strlen(name);
    for (int i = 0; i < count; ++i) {
        const PifCustomSlot& entry = g_pif_custom_slots[i];
        if (entry.is_wildcard != wildcard) continue;
        bool match;
        if (entry.is_wildcard) {
            match = entry.key_len > 0 && name_len >= entry.key_len &&
                    memcmp(name + name_len - entry.key_len, entry.key, entry.key_len) == 0;
        } else {
            match = (name_len == entry.key_len) &&
                    (memcmp(entry.key, name, name_len) == 0);
        }
        if (match) {
            size_t val_len = strlen(entry.value);
            if (val_len >= PROP_VALUE_MAX) val_len = PROP_VALUE_MAX - 1;
            memcpy(buffer, entry.value, val_len);
            buffer[val_len] = '\0';
            result = buffer;
            break;
        }
    }

    g_pif_custom_lock.unlock();
    return result;
}

bool custom_rom_hide_should_spoof_prop(const char* name, char* value) {
    if (!name || !value) return false;
    if (reinterpret_cast<uintptr_t>(name) < 0x1000000) return false;
    if (reinterpret_cast<uintptr_t>(value) < 0x1000000) return false;
    if (is_hidden_staging_prop(name)) { value[0] = '\0'; return true; }
    for (const char* const* p = kSpoofedEmptyProps; *p; ++p) {
        if (strcmp(name, *p) == 0) { value[0] = '\0'; return true; }
    }
    for (const PropOverride* o = kSpoofedValueProps; o->name; ++o) {
        if (strcmp(name, o->name) == 0) { strcpy(value, o->value); return true; }
    }
    return false;
}

bool custom_rom_hide_should_hide_prop(const char* name) {
    if (!name || reinterpret_cast<uintptr_t>(name) < 0x1000000) return false;
    if (is_hidden_staging_prop(name)) return true;
    for (const char* const* p = kSpoofedEmptyProps; *p; ++p) {
        if (strcmp(name, *p) == 0) return true;
    }
    return false;
}

const char* custom_rom_hide_get_prop_override(const char* name, char* buffer) {
    if (!name || reinterpret_cast<uintptr_t>(name) < 0x1000000) return nullptr;
    if (strncmp(name, PIF_STAGING_PROP_PREFIX, sizeof(PIF_STAGING_PROP_PREFIX) - 1) == 0) {
        return nullptr;
    }
    // is_droidguard_process() is cached per pid once the process name is final.
    const bool droidguard = is_droidguard_process();
    // An exact entry from the PIF config wins over everything below, as in PIFork.
    if (droidguard) {
        if (const char* v = find_custom_prop_override(name, buffer, false)) return v;
    }
    if (name[0] == 'r' || name[0] == 'v') {
        for (const PropOverride* o = kSpoofedValueProps; o->name; ++o) {
            if (strcmp(name, o->name) == 0) return o->value;
        }
    }
    if (!droidguard) return nullptr;
    for (const DynamicPropOverride* o = kDynamicProductProps; o->name; ++o) {
        if (strcmp(name, o->name) == 0) {
            // This code is also linked into the loader, which cannot contain ELF TLS.
            // The caller owns a PROP_VALUE_MAX buffer for the duration of the read.
            int len = __system_property_get(o->staging_name, buffer);
            if (len > 0) return buffer;
            return nullptr; // staging prop unset — leave the real value alone
        }
    }
    if (const char* staging = find_product_partition_staging(name)) {
        int len = __system_property_get(staging, buffer);
        if (len > 0) return buffer;
        return nullptr;
    }
    if (const DynamicSuffixOverride* o = find_dynamic_suffix_override(name)) {
        int len = __system_property_get(o->staging_name, buffer);
        if (len > 0) return buffer;
    }
    for (const PropOverride* o = kDroidGuardValueProps; o->name; ++o) {
        if (strcmp(name, o->name) == 0) return o->value;
    }
    // Wildcard entries from the PIF config apply last, after the fixed tables.
    return find_custom_prop_override(name, buffer, true);
}

static const PartitionDevEntry* find_partition_entry(const char* path) {
    if (!path) return nullptr;
    for (const PartitionDevEntry* e = kPartitionDmMap; e->path; ++e) {
        if (strcmp(path, e->path) == 0) return e;
    }
    return nullptr;
}

static constexpr size_t kPartitionDmCount =
        sizeof(kPartitionDmMap) / sizeof(kPartitionDmMap[0]) - 1;

struct PartitionRootStat {
    _Atomic(dev_t) dev;
    _Atomic(uint64_t) ino;
    _Atomic(bool) active;
};

static PartitionRootStat g_partition_roots[kPartitionDmCount];
static _Atomic(bool) g_partition_roots_initialized = false;

static void ensure_partition_roots_initialized() {
    if (atomic_load_explicit(&g_partition_roots_initialized, memory_order_acquire)) {
        return;
    }
    for (size_t i = 0; i < kPartitionDmCount; ++i) {
        struct stat sb;
        bool active = false;
        dev_t dev = 0;
        uint64_t ino = 0;
        if (raw_fstatat(AT_FDCWD, kPartitionDmMap[i].path, &sb, 0) == 0 &&
            S_ISDIR(sb.st_mode) && major(sb.st_dev) != DM_MAJOR) {
            active = true;
            dev = sb.st_dev;
            ino = static_cast<uint64_t>(sb.st_ino);
        }
        atomic_store_explicit(&g_partition_roots[i].dev, dev, memory_order_relaxed);
        atomic_store_explicit(&g_partition_roots[i].ino, ino, memory_order_relaxed);
        atomic_store_explicit(&g_partition_roots[i].active, active, memory_order_relaxed);
    }
    atomic_store_explicit(&g_partition_roots_initialized, true, memory_order_release);
}

static bool may_be_spoofed_partition_root(dev_t dev, uint64_t ino, bool has_ino) {
    ensure_partition_roots_initialized();
    for (size_t i = 0; i < kPartitionDmCount; ++i) {
        if (!atomic_load_explicit(&g_partition_roots[i].active, memory_order_relaxed)) {
            continue;
        }
        if (atomic_load_explicit(&g_partition_roots[i].dev, memory_order_relaxed) != dev) {
            continue;
        }
        if (!has_ino ||
            atomic_load_explicit(&g_partition_roots[i].ino, memory_order_relaxed) == ino) {
            return true;
        }
    }
    return false;
}

static void normalize_statfs_type(struct statfs* sf) {
    if (sf->f_type == static_cast<decltype(sf->f_type)>(OVERLAYFS_SUPER_MAGIC)) {
        sf->f_type = static_cast<decltype(sf->f_type)>(EROFS_SUPER_MAGIC_V1);
    }
}

void custom_rom_hide_spoof_stat(const char* path, struct stat* sb) {
    if (!path || !sb) return;
    const PartitionDevEntry* e = find_partition_entry(path);
    if (e && major(sb->st_dev) != DM_MAJOR) sb->st_dev = makedev(DM_MAJOR, e->dm_minor);
}

void custom_rom_hide_spoof_statx(const char* path, struct statx* sx) {
    if (!path || !sx) return;
    const PartitionDevEntry* e = find_partition_entry(path);
    if (e && sx->stx_dev_major != DM_MAJOR) {
        sx->stx_dev_major = DM_MAJOR;
        sx->stx_dev_minor = e->dm_minor;
    }
}

void custom_rom_hide_spoof_statfs(const char* path, struct statfs* sf) {
    if (!path || !sf) return;
    normalize_statfs_type(sf);
}

void custom_rom_hide_spoof_fd_stat(int fd, struct stat* sb) {
    if (fd < 0 || !sb) return;

    int saved_errno = errno;
    if (is_tracked_fd(fd)) {
        // resolve_encoded_memfd_path gates on the memfd link still decoding, so a stale
        // tracking bit on a reused fd number self-heals instead of reporting old metadata.
        char real_path[512];
        if (resolve_encoded_memfd_path(fd, real_path, sizeof(real_path))) {
            // The live path is exact when it still resolves; the captured record covers
            // the case where the task it named has gone.
            struct stat real_sb;
            FdMeta meta;
            if (raw_fstatat(AT_FDCWD, real_path, &real_sb, 0) == 0) *sb = real_sb;
            else if (load_fd_meta(fd, &meta) && meta.sb_ok) *sb = meta.sb;
        }
    } else if (S_ISDIR(sb->st_mode) && major(sb->st_dev) != DM_MAJOR &&
               may_be_spoofed_partition_root(sb->st_dev, static_cast<uint64_t>(sb->st_ino), true)) {
        char fd_path[512];
        if (resolve_fd_path(fd, fd_path, sizeof(fd_path))) {
            custom_rom_hide_spoof_stat(fd_path, sb);
        }
    }
    errno = saved_errno;
}

void custom_rom_hide_spoof_fd_statx(int fd, unsigned mask, struct statx* sx) {
    if (fd < 0 || !sx) return;

    int saved_errno = errno;
    if (is_tracked_fd(fd)) {
        char real_path[512];
        if (resolve_encoded_memfd_path(fd, real_path, sizeof(real_path))) {
            // The live path honors the caller's mask exactly; the captured record is
            // the fallback for when the task it named has gone.
            struct statx real_sx;
            FdMeta meta;
            if (raw_statx(AT_FDCWD, real_path, 0, mask, &real_sx) == 0) *sx = real_sx;
            else if (load_fd_meta(fd, &meta) && meta.sx_ok) *sx = meta.sx;
        }
    } else if ((sx->stx_mode == 0 || S_ISDIR(sx->stx_mode)) &&
               sx->stx_dev_major != DM_MAJOR &&
               may_be_spoofed_partition_root(makedev(sx->stx_dev_major, sx->stx_dev_minor),
                                             sx->stx_ino, (sx->stx_mask & STATX_INO) != 0)) {
        char fd_path[512];
        if (resolve_fd_path(fd, fd_path, sizeof(fd_path))) {
            custom_rom_hide_spoof_statx(fd_path, sx);
        }
    }
    errno = saved_errno;
}

void custom_rom_hide_spoof_fd_statfs(int fd, struct statfs* sf) {
    if (fd < 0 || !sf) return;

    int saved_errno = errno;
    if (is_tracked_fd(fd)) {
        char real_path[512];
        if (resolve_encoded_memfd_path(fd, real_path, sizeof(real_path))) {
            struct statfs real_sf;
            if (raw_statfs(real_path, &real_sf) == 0) {
                *sf = real_sf;
            } else {
                sf->f_type = PROC_SUPER_MAGIC;
            }
        }
    }
    normalize_statfs_type(sf);
    errno = saved_errno;
}
