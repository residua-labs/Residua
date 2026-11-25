/* provenance: ours (searched: plan9port@1f1396913f src/lib9/convM2S.c,convS2M.c,src/lib9p [Plan 9 Bell Labs files excluded from src/lib9/LICENSE]; u9fs@fec9fe04 [no license file]; host/devsrv Cargo.toml ninep=0.6.0 [requires Rust/Cargo]; glue/host/proc9.c; lib/Proc9.rsd)
 *
 * glue/host/proc9core.h — the backend-independent half of the Proc
 * execution host: flat-ABI marshalling (Int-as-record object ABI
 * revision 2, docs/OBJECT-ABI.md), the device connection layer (either an
 * in-process POSIX 9P2000 responder for env/fs/clock when devsrv is "-" or
 * $RSD_PROC_NS is unset, or unix sockets under $RSD_PROC_NS + `devsrv
 * args` when $RSD_PROC_NS is active), and exact-n frame reads. Shared by
 * the wasm2c host (proc9.c) and the wasmtime host (procwt.c); the includer
 * supplies the linear-memory hooks below.
 *
 *   static void host_mem_refresh(void);      reload mod_data/mod_size
 *   static void host_mem_grow(uint32_t p);   grow memory p wasm pages
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <time.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <signal.h>

#define MOD_FB 24ULL
#define MOD_FHEAP 65536ULL
#define MOD_NIL 1ULL
#define HDR_CONS 0x0102000000000001ULL
#define HDR_INT 0x0001000000000001ULL
#define HDR_DIG 0x0101000000000001ULL
#define MOD_FUEL ((1ULL << 62))
#define MAX_STEPS 100000
#define STEP_MS 30000
#define READ_MAX 8192
#define LIST_MAX (1 << 22)

static uint8_t *mod_data;
static uint64_t mod_size;

static void host_mem_refresh(void);
static void host_mem_grow(uint32_t pages);

static uint64_t mrd(uint64_t o) { uint64_t x; memcpy(&x, mod_data + o, 8); return x; }
static void mwr(uint64_t o, uint64_t x) { memcpy(mod_data + o, &x, 8); }

static void flat_reset(void) {
  host_mem_refresh();
  if (mod_size >= MOD_FHEAP)
    memset(mod_data + MOD_FB + 64, 0, MOD_FHEAP - MOD_FB - 64);
  mwr(MOD_FB + 0, MOD_FHEAP);
  mwr(MOD_FB + 8, mod_size);
  for (int i = 16; i <= 56; i += 8) mwr(MOD_FB + i, 0);
}

static int refuse(const char *name, int code, const char *detail) {
  if (detail && detail[0]) fprintf(stderr, "[%s] %s\n", name, detail);
  else fprintf(stderr, "[%s]\n", name);
  return code;
}

static uint64_t ocell(void) {
  uint64_t b = mrd(MOD_FB), need = 24;
  if (b + need > mod_size) {
    uint64_t gap = b + need - mod_size;
    uint32_t pages = (uint32_t)((gap + 65535) / 65536);
    host_mem_grow(pages);
    if (b + need > mod_size) { fprintf(stderr, "[capacity]\n"); exit(51); }
    mwr(MOD_FB + 8, mod_size);
  }
  mwr(MOD_FB, b + need);
  return b;
}

static uint64_t dig_list(uint64_t v) {
  if (v == 0) return MOD_NIL;
  uint64_t ds[64]; int n = 0;
  while (v && n < 64) { ds[n++] = v & 255; v >>= 8; }
  uint64_t cs[64];
  for (int i = 0; i < n; i++) cs[i] = ocell();
  for (int i = 0; i < n; i++) {
    mwr(cs[i], HDR_DIG);
    mwr(cs[i] + 8, i + 1 == n ? MOD_NIL : cs[i + 1]);
    mwr(cs[i] + 16, ds[i]);
  }
  return cs[0];
}

static uint64_t int_rec(int64_t w) {
  uint64_t r = ocell();
  uint64_t m = w < 0 ? (uint64_t)(-(w + 1)) + 1 : (uint64_t)w;
  mwr(r, HDR_INT);
  mwr(r + 8, dig_list(m));
  mwr(r + 16, w < 0 ? 1 : 0);
  return r;
}

/* Int record from an existing (sgn, mag-list) pair — a flat Int field in a
   result run becomes the boxed object again for the next call's argument. */
static inline uint64_t int_obj(uint64_t digp, uint64_t sgn) {
  uint64_t r = ocell();
  mwr(r, HDR_INT);
  mwr(r + 8, digp);
  mwr(r + 16, sgn);
  return r;
}

static uint64_t list_i(const int64_t *ws, int n) {
  if (n <= 0) return MOD_NIL;
  uint64_t *cs = malloc(sizeof(uint64_t) * (size_t)n);
  uint64_t *es = malloc(sizeof(uint64_t) * (size_t)n);
  for (int i = 0; i < n; i++) cs[i] = ocell();
  for (int i = 0; i < n; i++) es[i] = int_rec(ws[i]);
  for (int i = 0; i < n; i++) {
    mwr(cs[i], HDR_CONS);
    mwr(cs[i] + 8, es[i]);
    mwr(cs[i] + 16, i + 1 == n ? MOD_NIL : cs[i + 1]);
  }
  uint64_t r = cs[0];
  free(cs); free(es);
  return r;
}

/* A guest pointer the host dereferences must name a full 3-word cell in
   the heap arena: MOD_FHEAP <= p, 8-aligned, p + 24 <= mod_size. A result
   run that fails this is not the shape these walkers decode, so they set
   gp_bad and the caller skips the probe candidate or refuses the step. */
static int gp_bad;

static int gp_ok(uint64_t p) {
  return p >= MOD_FHEAP && !(p & 7) && p + 24 <= mod_size;
}

static uint64_t dig_val(uint64_t p) {
  uint64_t v = 0; int sh = 0;
  for (int g = 0; g < 256 && p != MOD_NIL; g++) {
    if (!gp_ok(p) || sh >= 64) { gp_bad = 1; return 0; }
    v |= mrd(p + 16) << sh; sh += 8; p = mrd(p + 8);
  }
  return v;
}

static int64_t int_val(uint64_t p) {
  if (!gp_ok(p)) { gp_bad = 1; return 0; }
  uint64_t m = dig_val(mrd(p + 8));
  return mrd(p + 16) ? -(int64_t)m : (int64_t)m;
}

/* flat Int pair (sgn, mag-list) in a structure result run */
static inline int64_t sgn_mag(uint64_t sgn, uint64_t magp) {
  uint64_t m = dig_val(magp);
  return sgn ? -(int64_t)m : (int64_t)m;
}

/* *n = -1 when the walk hit a bad guest pointer (gp_bad set). */
static int64_t *list_words(uint64_t p, int *n) {
  int64_t *o = malloc(sizeof(int64_t) * LIST_MAX);
  int i = 0;
  while (p != MOD_NIL && i < LIST_MAX) {
    if (!gp_ok(p)) { gp_bad = 1; break; }
    o[i++] = int_val(mrd(p + 8));
    if (gp_bad) break;
    p = mrd(p + 16);
  }
  *n = gp_bad ? -1 : i;
  return o;
}

/* rsc ABI status words: 0 value, 1 residue, 2 fuel, 3 stuck (detail 1 =
   capacity), 4 capacity. Returns the status; *dt gets the detail word. */
static uint64_t status_of(uint64_t *dt) {
  *dt = mrd(MOD_FB + 24);
  return mrd(MOD_FB + 16);
}

static inline int status_refuse(uint64_t st, uint64_t dt) {
  if (st == 2) return refuse("fuel", 50, "");
  if (st == 4 || (st == 3 && dt == 1)) return refuse("capacity", 51, "");
  if (st == 3) return refuse("stuck", 55, "");
  char d[32]; snprintf(d, sizeof d, "%llu", (unsigned long long)dt);
  return refuse(st == 1 ? "residue" : "proc_abi_status", 56, d);
}

/* ---------- In-process 9P2000 responder (env, fs, clock) ---------- */

#define P9_VFD_ENV   (-100)
#define P9_VFD_FS    (-101)
#define P9_VFD_CLOCK (-102)
#define P9_MAX_FIDS  32

enum {
  FID_NONE = 0,
  FID_ENV_ROOT,
  FID_ENV_ARGS,
  FID_FS_PATH,
  FID_CLOCK_ROOT,
  FID_CLOCK_FILE
};

typedef struct {
  int kind;
  int os_fd;
  int is_dir;
  uint64_t qpath;
  char path[4096];
  char snap[64];
  int snap_len;
} DirectFid;

static DirectFid dfids[3][P9_MAX_FIDS];
static uint8_t direct_rbuf[3][16384];
static size_t direct_rlen[3];
static size_t direct_roff[3];

static int dev_is_direct(const char *devsrv) {
  const char *ns = getenv("RSD_PROC_NS");
  if (!ns || !ns[0]) return 1;
  if (!devsrv || !devsrv[0] || !strcmp(devsrv, "-")) return 1;
  return access(devsrv, X_OK) != 0;
}

static uint16_t p9_r16(const uint8_t *p) {
  return (uint16_t)p[0] | ((uint16_t)p[1] << 8);
}

static uint32_t p9_r32(const uint8_t *p) {
  return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
         ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

static uint64_t p9_r64(const uint8_t *p) {
  return (uint64_t)p9_r32(p) | ((uint64_t)p9_r32(p + 4) << 32);
}

static void p9_w16(uint8_t *p, uint16_t v) {
  p[0] = (uint8_t)(v & 255); p[1] = (uint8_t)(v >> 8);
}

static void p9_w32(uint8_t *p, uint32_t v) {
  p[0] = (uint8_t)(v & 255); p[1] = (uint8_t)((v >> 8) & 255);
  p[2] = (uint8_t)((v >> 16) & 255); p[3] = (uint8_t)((v >> 24) & 255);
}

static void p9_w64(uint8_t *p, uint64_t v) {
  p9_w32(p, (uint32_t)(v & 0xffffffffULL));
  p9_w32(p + 4, (uint32_t)(v >> 32));
}

static void p9_wqid(uint8_t *p, uint8_t qt, uint32_t qv, uint64_t qp) {
  p[0] = qt;
  p9_w32(p + 1, qv);
  p9_w64(p + 5, qp);
}

static void p9_finish(int d, uint8_t mtype, uint16_t tag, size_t pay_len) {
  uint8_t *r = direct_rbuf[d];
  size_t total = 7 + pay_len;
  p9_w32(r, (uint32_t)total);
  r[4] = mtype;
  p9_w16(r + 5, tag);
  direct_rlen[d] = total;
  direct_roff[d] = 0;
}

static void p9_rerror(int d, uint16_t tag, const char *msg) {
  size_t n = strlen(msg);
  if (n > 256) n = 256;
  uint8_t *r = direct_rbuf[d];
  p9_w16(r + 7, (uint16_t)n);
  memcpy(r + 9, msg, n);
  p9_finish(d, 107, tag, 2 + n);
}

static const char *p9_errno_name(int e) {
  if (e == ENOENT || e == ENOTDIR) return "no_such_file";
  if (e == EACCES || e == EPERM || e == EROFS) return "permission_denied";
  if (e == EISDIR) return "is_a_directory";
  return "io_error";
}

static DirectFid *p9_fid_slot(int d, uint32_t fid) {
  if (fid >= P9_MAX_FIDS) return NULL;
  return &dfids[d][fid];
}

static void p9_fid_reset(DirectFid *f) {
  if (f->kind != FID_NONE && f->os_fd >= 0) {
    close(f->os_fd);
  }
  memset(f, 0, sizeof(*f));
  f->os_fd = -1;
}

static int p9_valid_seg(const uint8_t *seg, uint16_t slen) {
  if (slen == 0) return 0;
  if (slen == 1 && seg[0] == '.') return 0;
  if (slen == 2 && seg[0] == '.' && seg[1] == '.') return 0;
  for (uint16_t i = 0; i < slen; i++) {
    if (seg[i] == '/' || seg[i] == 0) return 0;
  }
  return 1;
}

static int p9_join_path(char *dst, size_t cap, const char *base,
                        const uint8_t *seg, uint16_t slen) {
  if (!p9_valid_seg(seg, slen)) return -1;
  int n;
  if (!strcmp(base, ".")) {
    n = snprintf(dst, cap, "%.*s", (int)slen, (const char *)seg);
  } else if (!strcmp(base, "/")) {
    n = snprintf(dst, cap, "/%.*s", (int)slen, (const char *)seg);
  } else {
    n = snprintf(dst, cap, "%s/%.*s", base, (int)slen, (const char *)seg);
  }
  return (n < 0 || (size_t)n >= cap) ? -1 : 0;
}

static int direct_9p_handle(int vfd, const uint8_t *t, size_t tlen,
                            const uint8_t *argbuf, int alen) {
  int d = -100 - vfd;
  if (d < 0 || d > 2) return -1;
  direct_rlen[d] = 0;
  direct_roff[d] = 0;
  if (tlen < 7 || tlen > 8192) return -1;
  uint32_t sz = p9_r32(t);
  uint8_t mtype = t[4];
  uint16_t tag = p9_r16(t + 5);
  if (sz < 7 || sz > 8192 || sz != tlen) return -1;
  uint8_t *r = direct_rbuf[d];

  if (mtype == 100) { /* Tversion */
    if (tlen < 13) { p9_rerror(d, tag, "short_version"); return 0; }
    uint32_t req_ms = p9_r32(t + 7);
    uint16_t vlen = p9_r16(t + 11);
    if (13 + (size_t)vlen != tlen) { p9_rerror(d, tag, "bad_version"); return 0; }
    uint32_t ms = req_ms > 8192 ? 8192 : req_ms;
    const char *ver = (vlen >= 6 && !memcmp(t + 13, "9P2000", 6)) ? "9P2000" : "unknown";
    size_t vn = strlen(ver);
    for (int i = 0; i < P9_MAX_FIDS; i++) p9_fid_reset(&dfids[d][i]);
    p9_w32(r + 7, ms);
    p9_w16(r + 11, (uint16_t)vn);
    memcpy(r + 13, ver, vn);
    p9_finish(d, 101, tag, 6 + vn);
    return 0;
  }

  if (mtype == 104) { /* Tattach */
    if (tlen < 19) { p9_rerror(d, tag, "short_attach"); return 0; }
    uint32_t fid = p9_r32(t + 7);
    uint16_t ulen = p9_r16(t + 15);
    if (17 + (size_t)ulen + 2 > tlen) { p9_rerror(d, tag, "bad_attach"); return 0; }
    size_t ao = 17 + (size_t)ulen;
    uint16_t anlen = p9_r16(t + ao);
    if (ao + 2 + (size_t)anlen != tlen) { p9_rerror(d, tag, "bad_attach"); return 0; }
    for (uint16_t i = 0; i < ulen; i++) {
      if (t[17 + i] == 0) { p9_rerror(d, tag, "bad_attach"); return 0; }
    }
    if (anlen != 0 && !(anlen == 1 && t[ao + 2] == '/')) {
      p9_rerror(d, tag, "invalid_aname");
      return 0;
    }
    DirectFid *f = p9_fid_slot(d, fid);
    if (!f) { p9_rerror(d, tag, "bad_fid"); return 0; }
    p9_fid_reset(f);
    if (d == 0) {
      f->kind = FID_ENV_ROOT;
      f->is_dir = 1;
      f->qpath = 1;
    } else if (d == 1) {
      f->kind = FID_FS_PATH;
      f->is_dir = 1;
      f->qpath = 1;
      if (anlen == 1 && t[ao + 2] == '/') strcpy(f->path, "/");
      else strcpy(f->path, ".");
    } else {
      f->kind = FID_CLOCK_ROOT;
      f->is_dir = 1;
      f->qpath = 1;
    }
    p9_wqid(r + 7, 0x80, 0, 1);
    p9_finish(d, 105, tag, 13);
    return 0;
  }

  if (mtype == 110) { /* Twalk */
    if (tlen < 17) { p9_rerror(d, tag, "short_walk"); return 0; }
    uint32_t fid = p9_r32(t + 7);
    uint32_t newfid = p9_r32(t + 11);
    uint16_t nw = p9_r16(t + 15);
    if (nw > 16) { p9_rerror(d, tag, "too_many_wnames"); return 0; }
    DirectFid *src = p9_fid_slot(d, fid);
    DirectFid *dst = p9_fid_slot(d, newfid);
    if (!src || src->kind == FID_NONE || !dst) { p9_rerror(d, tag, "bad_fid"); return 0; }
    size_t off = 17;
    if (nw == 0) {
      if (newfid != fid) {
        p9_fid_reset(dst);
        *dst = *src;
        dst->os_fd = -1;
      }
      p9_w16(r + 7, 0);
      p9_finish(d, 111, tag, 2);
      return 0;
    }
    if (d == 0) { /* env */
      uint16_t slen = (off + 2 <= tlen) ? p9_r16(t + off) : 0;
      if (nw == 1 && off + 2 + slen == tlen && src->kind == FID_ENV_ROOT &&
          slen == 4 && !memcmp(t + off + 2, "args", 4)) {
        if (newfid != fid) p9_fid_reset(dst);
        dst->kind = FID_ENV_ARGS;
        dst->os_fd = -1;
        dst->is_dir = 0;
        dst->qpath = 2;
        p9_w16(r + 7, 1);
        p9_wqid(r + 9, 0x00, 0, 2);
        p9_finish(d, 111, tag, 15);
        return 0;
      }
      p9_rerror(d, tag, "no_such_file");
      return 0;
    }
    if (d == 2) { /* clock */
      uint16_t slen = (off + 2 <= tlen) ? p9_r16(t + off) : 0;
      if (nw == 1 && off + 2 + slen == tlen && src->kind == FID_CLOCK_ROOT &&
          slen == 5 && !memcmp(t + off + 2, "clock", 5)) {
        if (newfid != fid) p9_fid_reset(dst);
        dst->kind = FID_CLOCK_FILE;
        dst->os_fd = -1;
        dst->is_dir = 0;
        dst->qpath = 3;
        p9_w16(r + 7, 1);
        p9_wqid(r + 9, 0x00, 0, 3);
        p9_finish(d, 111, tag, 15);
        return 0;
      }
      p9_rerror(d, tag, "no_such_file");
      return 0;
    }
    /* fs */
    if (src->kind != FID_FS_PATH) { p9_rerror(d, tag, "bad_fid"); return 0; }
    char cur[4096], next[4096];
    snprintf(cur, sizeof cur, "%s", src->path);
    int cur_dir = src->is_dir;
    uint64_t cur_qp = src->qpath;
    uint8_t qbuf[16 * 13];
    uint16_t walked = 0;
    for (uint16_t k = 0; k < nw; k++) {
      if (off + 2 > tlen) { p9_rerror(d, tag, "bad_walk"); return 0; }
      uint16_t slen = p9_r16(t + off);
      off += 2;
      if (off + slen > tlen) { p9_rerror(d, tag, "bad_walk"); return 0; }
      if (!p9_valid_seg(t + off, slen)) {
        p9_rerror(d, tag, "invalid_path_segment");
        return 0;
      }
      if (!cur_dir || p9_join_path(next, sizeof next, cur, t + off, slen) != 0) {
        if (k == 0) { p9_rerror(d, tag, "no_such_file"); return 0; }
        break;
      }
      off += slen;
      struct stat st;
      if (stat(next, &st) != 0) {
        if (k == 0) { p9_rerror(d, tag, p9_errno_name(errno)); return 0; }
        break;
      }
      snprintf(cur, sizeof cur, "%s", next);
      cur_dir = S_ISDIR(st.st_mode) ? 1 : 0;
      cur_qp = (uint64_t)st.st_ino;
      p9_wqid(qbuf + walked * 13, cur_dir ? 0x80 : 0x00, 0, cur_qp);
      walked++;
    }
    if (walked == nw && off != tlen) {
      p9_rerror(d, tag, "bad_walk");
      return 0;
    }
    if (walked == nw) {
      if (newfid != fid) p9_fid_reset(dst);
      else if (dst->os_fd >= 0) { close(dst->os_fd); dst->os_fd = -1; }
      dst->kind = FID_FS_PATH;
      dst->os_fd = -1;
      dst->is_dir = cur_dir;
      dst->qpath = cur_qp;
      snprintf(dst->path, sizeof dst->path, "%s", cur);
    }
    p9_w16(r + 7, walked);
    memcpy(r + 9, qbuf, (size_t)walked * 13);
    p9_finish(d, 111, tag, 2 + (size_t)walked * 13);
    return 0;
  }

  if (mtype == 112) { /* Topen */
    if (tlen != 12) { p9_rerror(d, tag, "bad_open"); return 0; }
    uint32_t fid = p9_r32(t + 7);
    uint8_t mode = t[11];
    DirectFid *f = p9_fid_slot(d, fid);
    if (!f || f->kind == FID_NONE) { p9_rerror(d, tag, "bad_fid"); return 0; }
    if (f->kind == FID_ENV_ARGS) {
      p9_wqid(r + 7, 0x00, 0, 2);
      p9_w32(r + 20, 8168);
      p9_finish(d, 113, tag, 17);
      return 0;
    }
    if (f->kind == FID_CLOCK_FILE) {
      struct timespec ts;
      clock_gettime(CLOCK_REALTIME, &ts);
      f->snap_len = snprintf(f->snap, sizeof f->snap, "%lld.%09ld\n",
                             (long long)ts.tv_sec, (long)ts.tv_nsec);
      p9_wqid(r + 7, 0x00, 0, 3);
      p9_w32(r + 20, 8168);
      p9_finish(d, 113, tag, 17);
      return 0;
    }
    if (f->kind == FID_FS_PATH) {
      int acc = (mode & 3) == 0 ? O_RDONLY : ((mode & 3) == 1 ? O_WRONLY : O_RDWR);
      if (mode & 0x10) acc |= O_TRUNC;
      int fd = open(f->path, acc);
      if (fd < 0) { p9_rerror(d, tag, p9_errno_name(errno)); return 0; }
      if (f->os_fd >= 0) close(f->os_fd);
      f->os_fd = fd;
      p9_wqid(r + 7, f->is_dir ? 0x80 : 0x00, 0, f->qpath);
      p9_w32(r + 20, 8168);
      p9_finish(d, 113, tag, 17);
      return 0;
    }
    p9_rerror(d, tag, "permission_denied");
    return 0;
  }

  if (mtype == 114) { /* Tcreate */
    if (d != 1 || tlen < 18) { p9_rerror(d, tag, "permission_denied"); return 0; }
    uint32_t fid = p9_r32(t + 7);
    uint16_t nlen = p9_r16(t + 11);
    if (13 + (size_t)nlen + 5 != tlen) { p9_rerror(d, tag, "bad_create"); return 0; }
    uint32_t perm = p9_r32(t + 13 + nlen);
    uint8_t mode = t[13 + nlen + 4];
    DirectFid *f = p9_fid_slot(d, fid);
    if (!f || f->kind != FID_FS_PATH || !f->is_dir) {
      p9_rerror(d, tag, "bad_fid");
      return 0;
    }
    char child[4096];
    if (!p9_valid_seg(t + 13, nlen)) {
      p9_rerror(d, tag, "invalid_path_segment");
      return 0;
    }
    if (p9_join_path(child, sizeof child, f->path, t + 13, nlen) != 0) {
      p9_rerror(d, tag, "no_such_file");
      return 0;
    }
    int acc = ((mode & 3) == 2 ? O_RDWR : O_WRONLY) | O_CREAT | O_TRUNC;
    int fd = open(child, acc, (mode_t)(perm & 0777));
    if (fd < 0) { p9_rerror(d, tag, p9_errno_name(errno)); return 0; }
    if (f->os_fd >= 0) close(f->os_fd);
    f->os_fd = fd;
    f->is_dir = 0;
    struct stat st;
    f->qpath = (fstat(fd, &st) == 0) ? (uint64_t)st.st_ino : 4;
    snprintf(f->path, sizeof f->path, "%s", child);
    p9_wqid(r + 7, 0x00, 0, f->qpath);
    p9_w32(r + 20, 8168);
    p9_finish(d, 115, tag, 17);
    return 0;
  }

  if (mtype == 116) { /* Tread */
    if (tlen != 23) { p9_rerror(d, tag, "bad_read"); return 0; }
    uint32_t fid = p9_r32(t + 7);
    uint64_t off = p9_r64(t + 11);
    uint32_t cnt = p9_r32(t + 19);
    if (cnt > 8168) cnt = 8168;
    DirectFid *f = p9_fid_slot(d, fid);
    if (!f || f->kind == FID_NONE) { p9_rerror(d, tag, "bad_fid"); return 0; }
    if (f->kind == FID_ENV_ARGS) {
      uint32_t n = 0;
      if (off < (uint64_t)alen) {
        uint64_t rem = (uint64_t)alen - off;
        n = rem < cnt ? (uint32_t)rem : cnt;
        memcpy(r + 11, argbuf + off, n);
      }
      p9_w32(r + 7, n);
      p9_finish(d, 117, tag, 4 + n);
      return 0;
    }
    if (f->kind == FID_CLOCK_FILE) {
      uint32_t n = 0;
      if (off < (uint64_t)f->snap_len) {
        uint64_t rem = (uint64_t)f->snap_len - off;
        n = rem < cnt ? (uint32_t)rem : cnt;
        memcpy(r + 11, f->snap + off, n);
      }
      p9_w32(r + 7, n);
      p9_finish(d, 117, tag, 4 + n);
      return 0;
    }
    if (f->kind == FID_FS_PATH && f->os_fd >= 0) {
      ssize_t n = pread(f->os_fd, r + 11, cnt, (off_t)off);
      if (n < 0) { p9_rerror(d, tag, p9_errno_name(errno)); return 0; }
      p9_w32(r + 7, (uint32_t)n);
      p9_finish(d, 117, tag, 4 + (size_t)n);
      return 0;
    }
    p9_rerror(d, tag, "bad_fid");
    return 0;
  }

  if (mtype == 118) { /* Twrite */
    if (tlen < 23) { p9_rerror(d, tag, "bad_write"); return 0; }
    uint32_t fid = p9_r32(t + 7);
    uint64_t off = p9_r64(t + 11);
    uint32_t cnt = p9_r32(t + 19);
    if (23 + (size_t)cnt != tlen) { p9_rerror(d, tag, "bad_write"); return 0; }
    DirectFid *f = p9_fid_slot(d, fid);
    if (!f || f->kind != FID_FS_PATH || f->os_fd < 0) {
      p9_rerror(d, tag, "bad_fid");
      return 0;
    }
    uint32_t done = 0;
    while (done < cnt) {
      ssize_t w = pwrite(f->os_fd, t + 23 + done, cnt - done, (off_t)(off + done));
      if (w < 0) {
        if (errno == EINTR) continue;
        p9_rerror(d, tag, p9_errno_name(errno));
        return 0;
      }
      done += (uint32_t)w;
    }
    p9_w32(r + 7, done);
    p9_finish(d, 119, tag, 4);
    return 0;
  }

  if (mtype == 120) { /* Tclunk */
    if (tlen != 11) { p9_rerror(d, tag, "bad_clunk"); return 0; }
    uint32_t fid = p9_r32(t + 7);
    DirectFid *f = p9_fid_slot(d, fid);
    if (!f || f->kind == FID_NONE) { p9_rerror(d, tag, "bad_fid"); return 0; }
    p9_fid_reset(f);
    p9_finish(d, 121, tag, 0);
    return 0;
  }

  p9_rerror(d, tag, "unsupported_op");
  return 0;
}

/* ---------- 9P device connections ---------- */

typedef struct { char name[16]; int fd; } DevConn;
static DevConn devs[8];
static int ndevs;

static int unix_conn(const char *path) {
  int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0) return -1;
  struct sockaddr_un a;
  memset(&a, 0, sizeof a);
  a.sun_family = AF_UNIX;
  strncpy(a.sun_path, path, sizeof(a.sun_path) - 1);
  if (connect(fd, (struct sockaddr *)&a, sizeof a)) { close(fd); return -1; }
  return fd;
}

/* connect to <dir>/<name> via a relative path: absolute socket paths under
   deep worktrees exceed sun_path (~104), so chdir in, connect, and restore. */
static int unix_conn_rel(const char *dir, const char *name) {
  int cw = open(".", O_RDONLY);
  if (cw < 0 || chdir(dir)) { if (cw >= 0) close(cw); return -1; }
  int fd = unix_conn(name);
  int e = errno;
  if (fchdir(cw)) { /* ignore */ }
  close(cw);
  errno = e;
  return fd;
}

/* env `devsrv args` child is spawned BEFORE the wasm engine compiles anything
   when external devsrv mode is active. */
static struct env_child { char dir[160]; int pin, pout; pid_t pid; int used; } env_ch;
static int env_spawned = 0;

static const char *env_abs_devsrv(const char *devsrv0, char *dsabs, size_t cap) {
  if (devsrv0[0] == '/') return devsrv0;
  char cw[512];
  if (getcwd(cw, sizeof cw) && snprintf(dsabs, cap, "%s/%s", cw, devsrv0) > 0)
    return dsabs;
  return devsrv0;
}

static void env_child_cleanup(void) {
  if (env_spawned && !env_ch.used) {
    kill(env_ch.pid, SIGKILL);
    waitpid(env_ch.pid, 0, 0);
  }
}

static int env_spawn(const char *devsrv0) {
  if (dev_is_direct(devsrv0)) return 0;
  if (env_spawned) return 0;
  char dsabs[1024];
  const char *devsrv = env_abs_devsrv(devsrv0, dsabs, sizeof dsabs);
  const char *tds[4];
  tds[0] = getenv("RSD_PROC_NS");
  tds[1] = getenv("TMPDIR");
  tds[2] = getenv("HOME");
  tds[3] = "/tmp";
  int i;
  for (i = 0; i < 4; i++) {
    if (!tds[i] || !*tds[i]) continue;
    snprintf(env_ch.dir, sizeof env_ch.dir, "%s/eXXXXXX", tds[i]);
    if (mkdtemp(env_ch.dir)) break;
  }
  if (i == 4) { fprintf(stderr, "env_spawn: mkdtemp failed (td0=%s)\n", tds[0] ? tds[0] : "?"); return -1; }
  char elog[200];
  snprintf(elog, sizeof elog, "%s/e", env_ch.dir);
  int pin[2], pout[2];
  if (pipe(pin) || pipe(pout)) return -1;
  fcntl(pin[0], F_SETFD, FD_CLOEXEC); fcntl(pin[1], F_SETFD, FD_CLOEXEC);
  fcntl(pout[0], F_SETFD, FD_CLOEXEC); fcntl(pout[1], F_SETFD, FD_CLOEXEC);
  pid_t pid = fork();
  if (pid == 0) {
    dup2(pin[0], 0); dup2(pout[1], 1);
    int efd = open(elog, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (efd >= 0) { dup2(efd, 2); fcntl(efd, F_SETFD, FD_CLOEXEC); }
    if (chdir(env_ch.dir) == 0)
      execl(devsrv, devsrv, "args", "s", (char *)0);
    _exit(127);
  }
  close(pin[0]); close(pout[1]);
  if (pid < 0) { close(pin[1]); close(pout[0]); return -1; }
  env_ch.pin = pin[1]; env_ch.pout = pout[0]; env_ch.pid = pid; env_ch.used = 0;
  env_spawned = 1;
  atexit(env_child_cleanup);
  return 0;
}

static int env_conn(const char *devsrv0, const uint8_t *args, int alen) {
  if (!env_spawned && env_spawn(devsrv0)) return -1;
  if (env_ch.used) { fprintf(stderr, "env_conn: second env request\n"); return -1; }
  env_ch.used = 1;
  char sock[192], elog[192];
  snprintf(sock, sizeof sock, "%s/s", env_ch.dir);
  snprintf(elog, sizeof elog, "%s/e", env_ch.dir);
  if (alen > 0) {
    ssize_t wr = write(env_ch.pin, args, (size_t)alen);
    (void)wr;
  }
  close(env_ch.pin);
  char ready[8] = {0};
  struct pollfd pf = { env_ch.pout, POLLIN, 0 };
  int ok = 0;
  if (poll(&pf, 1, STEP_MS) > 0 && read(env_ch.pout, ready, 6) == 6 &&
      !memcmp(ready, "ready\n", 6)) ok = 1;
  close(env_ch.pout);
  if (!ok) {
    int wst = 0; waitpid(env_ch.pid, &wst, WNOHANG);
    fprintf(stderr, "env_conn: no ready from devsrv args %s (status %x)\n", sock, wst);
    char eb[512]; int ef = open(elog, O_RDONLY);
    if (ef >= 0) { ssize_t en = read(ef, eb, sizeof eb - 1); close(ef); if (en > 0) { eb[en] = 0; fprintf(stderr, "env_conn devsrv: %s\n", eb); } }
    kill(env_ch.pid, SIGKILL); waitpid(env_ch.pid, 0, 0); return -1;
  }
  int cfd = unix_conn_rel(env_ch.dir, "s");
  if (cfd < 0) fprintf(stderr, "env_conn: connect %s failed\n", sock);
  return cfd;
}

static int dev_conn(const char *dev, const char *devsrv,
                    const uint8_t *args, int alen) {
  for (int i = 0; i < ndevs; i++) if (!strcmp(devs[i].name, dev)) return devs[i].fd;
  int fd;
  if (dev_is_direct(devsrv)) {
    if (!strcmp(dev, "env")) fd = P9_VFD_ENV;
    else if (!strcmp(dev, "fs")) fd = P9_VFD_FS;
    else if (!strcmp(dev, "clock")) fd = P9_VFD_CLOCK;
    else {
      const char *ns = getenv("RSD_PROC_NS");
      if (!ns || !ns[0]) exit(refuse("proc_namespace_unset", 70, ""));
      fd = unix_conn_rel(ns, dev);
      if (fd < 0) exit(refuse("proc_socket_unavailable", 70, dev));
    }
  } else if (!strcmp(dev, "env")) {
    fd = env_conn(devsrv, args, alen);
    if (fd < 0) exit(refuse("proc_args_device", 70, ""));
  } else {
    const char *ns = getenv("RSD_PROC_NS");
    if (!ns || !ns[0]) exit(refuse("proc_namespace_unset", 70, ""));
    fd = unix_conn_rel(ns, dev);
    if (fd < 0) exit(refuse("proc_socket_unavailable", 70, dev));
  }
  snprintf(devs[ndevs].name, sizeof devs[ndevs].name, "%s", dev);
  devs[ndevs++].fd = fd;
  return fd;
}

/* Write a complete outbound 9P T-frame to a connected device. */
static int dev_write_frame(int fd, const uint8_t *frame, size_t len,
                           const uint8_t *argbuf, int alen) {
  if (fd <= -100) {
    return direct_9p_handle(fd, frame, len, argbuf, alen);
  }
  size_t off = 0;
  while (off < len) {
    ssize_t w = write(fd, frame + off, len - off);
    if (w < 0) { if (errno == EINTR) continue; return -1; }
    if (w == 0) return -1;
    off += (size_t)w;
  }
  return 0;
}

/* read exactly n bytes -> evt 0; eos 1; closed 2; timeout 4. */
static int read_n(int fd, uint8_t *buf, int n) {
  if (fd <= -100) {
    int d = -100 - fd;
    if (d < 0 || d > 2) return 2;
    size_t avail = direct_rlen[d] - direct_roff[d];
    if (avail == 0) return 1;
    if (avail < (size_t)n) return 2;
    memcpy(buf, direct_rbuf[d] + direct_roff[d], (size_t)n);
    direct_roff[d] += (size_t)n;
    return 0;
  }
  int got = 0;
  while (got < n) {
    struct pollfd pf = { fd, POLLIN, 0 };
    int pr = poll(&pf, 1, STEP_MS);
    if (pr < 0) return errno == EINTR ? read_n(fd, buf + got, n - got) : 2;
    if (pr == 0) return 4;
    if (pf.revents & (POLLHUP | POLLERR)) {
      if (got == 0) return 2;
    }
    ssize_t r = read(fd, buf + got, (size_t)(n - got));
    if (r < 0) { if (errno == EINTR) continue; return 2; }
    if (r == 0) return got == 0 ? 1 : 2;
    got += (int)r;
  }
  return 0;
}
