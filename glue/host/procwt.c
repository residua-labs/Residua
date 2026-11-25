/* provenance: ours; wasmtime engine/linking pattern adapted from
 * bootstrap/seed/stage-14274/seed-host.c (bootstrap/seed/stage-14274, wasmtime v50.0.1 C API),
 * device and marshalling code shared via glue/host/proc9core.h
 *
 * glue/host/procwt.c — resident-memory Proc execution host on the wasmtime
 * C API. Same wire protocol as host/exec9.cjs procMain and glue/host/proc9.c,
 * but the step entry is Lib.Proc.driveS, not drive9: the continuation stays
 * in the guest's linear memory as a live value, so a step carries only its
 * request/response bytes instead of an lp-encoded copy of the whole state.
 *
 *   argv: procwt <wasm> <f<entry>> <step|auto> <fuel> <out> <err> <devsrv>
 *                 [script args...]
 *   out/err: "" means stdout/stderr; a path gets the bytes appended
 *            (exec9.cjs procMain's dest convention).
 *
 * PStep flat result run at FB+96: structures flatten field-by-field and
 * Int flattens to (sgn, mag), so PStep{act out need acc p} is 12 words:
 *   [act.sgn act.mag out need.sgn need.mag acc p0..p5]
 * The host decodes only act and out; need's two flat words, acc and
 * p0..p5 go back verbatim. Int arguments are flat (sgn, mag) pairs, so
 * driveS is a 12-word call.
 *
 * Exit codes/refusal names: exec9.cjs procMain's (act 1 -> exit byte +
 * stdout; act 2 -> [residue] or [proc_rerror] on stderr, exit 56).
 */

#if !defined(_DEFAULT_SOURCE)
#define _DEFAULT_SOURCE
#endif
#define _POSIX_C_SOURCE 200809L
#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE
#endif
#include <wasm.h>
#include <wasmtime.h>
#include <inttypes.h>
#include <pthread.h>

static void host_mem_refresh(void);
static void host_mem_grow(uint32_t pages);
#include "proc9core.h"

static char **args;
static int result = 1;
static wasmtime_context_t *CTX;
static wasmtime_memory_t MEM;
static wasmtime_store_t *STORE;
static wasmtime_instance_t INST;
static wasmtime_func_t STEP_FN;
static int have_step;

static void host_mem_refresh(void) {
  mod_data = wasmtime_memory_data(CTX, &MEM);
  mod_size = wasmtime_memory_data_size(CTX, &MEM);
}

static void host_mem_grow(uint32_t pages) {
  uint64_t prev;
  wasmtime_error_t *err = wasmtime_memory_grow(CTX, &MEM, pages, &prev);
  if (err) { wasmtime_error_delete(err); return; }
  host_mem_refresh();
}

/* ---------- wasmtime helpers ---------- */

_Noreturn static void wt_fail(const char *where, wasmtime_error_t *err,
                              wasm_trap_t *trap) {
  wasm_byte_vec_t msg;
  if (err) {
    wasmtime_error_message(err, &msg);
    wasmtime_error_delete(err);
  } else {
    wasm_trap_message(trap, &msg);
    wasm_trap_delete(trap);
  }
  fprintf(stderr, "%s:%.*s\n", where, (int)msg.size, msg.data);
  wasm_byte_vec_delete(&msg);
  exit(70);
}

/* A trap stays a trap, named as one (exec9 classify): never a refusal. */
_Noreturn static void trap_exit(wasm_trap_t *trap) {
  wasm_byte_vec_t msg;
  wasm_trap_message(trap, &msg);
  wasm_trap_delete(trap);
  fprintf(stderr, "[host_trap] trap_wasm_runtime %.*s\n", (int)msg.size, msg.data);
  wasm_byte_vec_delete(&msg);
  exit(57);
}

static size_t func_params(wasmtime_func_t *f) {
  wasm_functype_t *ft = wasmtime_func_type(CTX, f);
  const wasm_valtype_vec_t *ps = wasm_functype_params(ft);
  size_t n = ps->size;
  for (size_t i = 0; i < n; i++)
    if (wasm_valtype_kind(ps->data[i]) != WASMTIME_I64) { n = 0; break; }
  wasm_functype_delete(ft);
  return n;
}

static size_t func_results(wasmtime_func_t *f) {
  wasm_functype_t *ft = wasmtime_func_type(CTX, f);
  size_t n = wasm_functype_results(ft)->size;
  wasm_functype_delete(ft);
  return n;
}

/* Call a guest function. rc: 0 ok, 1 trap (printed), 2 host error. */
static int guest_call(wasmtime_func_t *f, wasmtime_val_t *av, size_t na) {
  size_t nr = func_results(f);
  wasmtime_val_t rv[4];
  if (nr > 4) { fprintf(stderr, "[proc_abi_exports]\n"); exit(70); }
  wasm_trap_t *trap = NULL;
  wasmtime_error_t *err = wasmtime_func_call(CTX, f, av, na, rv, nr, &trap);
  if (err) wt_fail("proc_call", err, NULL);
  if (trap) trap_exit(trap);
  return 0;
}

static int get_export_fn(const char *name, wasmtime_func_t *out) {
  wasmtime_extern_t item;
  if (!wasmtime_instance_export_get(CTX, &INST, name, strlen(name), &item) ||
      item.kind != WASMTIME_EXTERN_FUNC)
    return 0;
  *out = item.of.func;
  return 1;
}

/* ---------- module cache (cwasm keyed by the wasm's content name) ---------- */

static int is_q_name(const char *base) {
  if (strlen(base) != 64) return 0;
  for (int i = 0; i < 64; i++) {
    char c = base[i];
    if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))) return 0;
  }
  return 1;
}

static void cache_path(char *dst, size_t cap, const char *wasm_path) {
  const char *dir = getenv("RSD_PROCWT_CACHE");
  char fallback[4096];
  if (!dir) {
    const char *home = getenv("HOME");
    snprintf(fallback, sizeof fallback, "%s/.cache/rsd/cwasm",
             home ? home : ".");
    dir = fallback;
  }
  const char *base = strrchr(wasm_path, '/');
  base = base ? base + 1 : wasm_path;
  if (is_q_name(base)) {
    snprintf(dst, cap, "%s/%s.v50.cwasm", dir, base);
  } else {
    uint64_t h = 1469598103934665603ULL;
    for (const uint8_t *p = (const uint8_t *)wasm_path; *p; p++) {
      h ^= *p; h *= 1099511628211ULL;
    }
    snprintf(dst, cap, "%s/p%" PRIx64 ".v50.cwasm", dir, h);
  }
  /* mkdir -p the cache dir (best effort; a later failure just recompiles) */
  char mk[4200];
  snprintf(mk, sizeof mk, "%s", dir);
  for (char *p = mk + 1; ; p++) {
    if (*p == '/' || *p == 0) {
      char c = *p; *p = 0;
      mkdir(mk, 0755);
      *p = c;
      if (c == 0) break;
    }
  }
}

/* ---------- flatPatch: add a `memory` export when the module omits it ------
   (port of exec9.cjs flatPatch; rsdc stores already-patched wasm, this is
   a fallback for hand-built modules) */

static uint64_t leb_at(const uint8_t *b, size_t *o) {
  uint64_t n = 0; int s = 0;
  for (;;) { uint8_t c = b[(*o)++]; n |= (uint64_t)(c & 127) << s; s += 7;
    if (!(c & 128)) return n; }
}

static size_t uleb(uint64_t n, uint8_t *o) {
  size_t i = 0;
  do { uint8_t b = n & 127; n >>= 7; if (n) b |= 128; o[i++] = b; } while (n);
  return i;
}

static uint8_t *flat_patch(const uint8_t *buf, size_t len, size_t *out_len) {
  if (len < 8) return NULL;
  /* pass 1: find the export section and scan for a `memory` export */
  size_t o = 8, exp_pos = 0, exp_body = 0, exp_bl = 0;
  uint64_t exp_cnt = 0;
  int have_mem = 0;
  while (o + 1 < len) {
    uint8_t id = buf[o];
    size_t lo = o + 1;
    size_t q = lo;
    uint64_t ln = leb_at(buf, &q);
    if (q + ln > len) return NULL;
    if (id == 7) {
      exp_pos = lo;            /* position of the section-length field */
      exp_body = q;            /* position of the section body */
      exp_bl = (size_t)ln;
      size_t e = q;
      exp_cnt = leb_at(buf, &e);
      for (uint64_t i = 0; i < exp_cnt && e < q + ln; i++) {
        uint64_t nl = leb_at(buf, &e);
        if (nl == 6 && !memcmp(buf + e, "memory", 6)) have_mem = 1;
        e += nl + 1;
        leb_at(buf, &e);
      }
    }
    o = q + ln;
  }
  if (have_mem) { *out_len = len; return (uint8_t *)buf; }
  if (!exp_body) return NULL;
  /* pass 2: rebuild with one extra export (memory, kind 2, index 0) */
  uint8_t add[16]; size_t an = 0;
  an += uleb(6, add + an);
  memcpy(add + an, "memory", 6); an += 6;
  add[an++] = 2;
  an += uleb(0, add + an);
  size_t e = exp_body;
  uint64_t cnt = leb_at(buf, &e);       /* entries start at e */
  size_t entries_len = exp_bl - (e - exp_body);
  uint8_t cb[8]; size_t cn = uleb(cnt + 1, cb);
  uint8_t *out = malloc(len + 64);
  size_t w = 0, r = 0;
  while (r < len) {
    if (r == exp_pos - 1) {
      /* rewrite the export section */
      out[w++] = 7;
      w += uleb(cn + entries_len + an, out + w);
      memcpy(out + w, cb, cn); w += cn;
      memcpy(out + w, buf + e, entries_len); w += entries_len;
      memcpy(out + w, add, an); w += an;
      r = exp_body + exp_bl;
    } else {
      out[w++] = buf[r++];
    }
  }
  *out_len = w;
  return out;
}

/* ---------- output sink (exec9 write(dest, fd, bytes)) ---------- */

static void sink_write(const char *dest, int fd, const uint8_t *b, size_t n) {
  if (dest && dest[0]) {
    FILE *f = fopen(dest, "ab");
    if (f) { fwrite(b, 1, n, f); fclose(f); return; }
  }
  size_t off = 0;
  while (off < n) {
    ssize_t w = write(fd, b + off, n - off);
    if (w <= 0) return;
    off += (size_t)w;
  }
}

static int refuse_o(const char *errp, const char *name, int code,
                    const char *detail) {
  char line[256];
  if (detail && detail[0])
    snprintf(line, sizeof line, "[%s] %s\n", name, detail);
  else
    snprintf(line, sizeof line, "[%s]\n", name);
  sink_write(errp, 2, (const uint8_t *)line, strlen(line));
  return code;
}

/* status_refuse against the errPath sink (same names/codes). */
static int status_refuse_o(const char *errp, uint64_t st, uint64_t dt) {
  char d[32];
  snprintf(d, sizeof d, "%llu", (unsigned long long)dt);
  if (st == 2) return refuse_o(errp, "fuel", 50, "");
  if (st == 4 || (st == 3 && dt == 1)) return refuse_o(errp, "capacity", 51, "");
  if (st == 3) return refuse_o(errp, "stuck", 55, "");
  return refuse_o(errp, st == 1 ? "residue" : "proc_abi_status", 56, d);
}

/* ---------- the run (on a big native stack, seed-host pattern) ---------- */

static void *run(void *unused) {
  (void)unused;
  const char *wasm_path = args[1], *entry = args[2], *fuel_s = args[4];
  const char *out_path = args[5], *err_path = args[6], *devsrv = args[7];
  if (!devsrv[0]) devsrv = getenv("RSD_DEVSRV");
  if (!devsrv || !devsrv[0]) devsrv = "-";
  /* fuel: decimal, 1..2^63-1 (exec9 procFuel) */
  uint64_t fuel = 0;
  if (!fuel_s[0]) { result = refuse_o(err_path, "proc_fuel_input", 50, ""); return NULL; }
  for (const char *p = fuel_s; *p; p++) {
    if (*p < '0' || *p > '9') { result = refuse_o(err_path, "proc_fuel_input", 50, ""); return NULL; }
    if (fuel > (UINT64_MAX - 9) / 10) { result = refuse_o(err_path, "proc_fuel_limit", 50, ""); return NULL; }
    fuel = fuel * 10 + (uint64_t)(*p - '0');
  }
  if (fuel > ((1ULL << 63) - 1)) { result = refuse_o(err_path, "proc_fuel_limit", 50, ""); return NULL; }
  if (fuel == 0) { result = refuse_o(err_path, "fuel", 50, ""); return NULL; }

  /* env child must exec before the engine JITs anything: children of a
     post-compile process get SIGKILLed at exec on this host. */
  env_spawn(devsrv);

  FILE *f = fopen(wasm_path, "rb");
  if (!f || fseek(f, 0, SEEK_END)) { result = refuse_o(err_path, "proc_host_failure", 70, "wasm_read"); return NULL; }
  long mn = ftell(f);
  if (mn < 0) { fclose(f); result = refuse_o(err_path, "proc_host_failure", 70, "wasm_read"); return NULL; }
  rewind(f);
  uint8_t *mbytes = malloc(mn ? (size_t)mn : 1);
  if (!mbytes || fread(mbytes, 1, (size_t)mn, f) != (size_t)mn) {
    if (f) fclose(f);
    result = refuse_o(err_path, "proc_host_failure", 70, "wasm_read");
    return NULL;
  }
  fclose(f);
  size_t plen = 0;
  uint8_t *patched = flat_patch(mbytes, (size_t)mn, &plen);
  if (!patched) { free(mbytes); result = refuse_o(err_path, "proc_abi_exports", 70, ""); return NULL; }

  wasm_config_t *cfg = wasm_config_new();
  wasmtime_config_wasm_exceptions_set(cfg, true);
  wasmtime_config_max_wasm_stack_set(cfg, (size_t)512 * 1024 * 1024);
  wasmtime_config_async_stack_size_set(cfg, (size_t)768 * 1024 * 1024);
  /* Engine fuel bounds every guest call; a wrong -7 probe candidate that
     ignores the guest fuel arg (and so loops forever) still traps. The
     cwasm cache entry is engine-config dependent, so toggling this
     changes which serialized modules load — an old entry just misses. */
  wasmtime_config_consume_fuel_set(cfg, true);
  wasm_engine_t *engine = wasm_engine_new_with_config(cfg);
  if (!engine) { result = refuse_o(err_path, "proc_host_failure", 70, "engine"); return NULL; }
  STORE = wasmtime_store_new(engine, NULL, NULL);
  CTX = wasmtime_store_context(STORE);
  /* Real step calls re-arm this per call below; the value only caps a
     guest that ignores its fuel argument. */
  if (wasmtime_context_set_fuel(CTX, (uint64_t)1 << 62)) {
    result = refuse_o(err_path, "proc_host_failure", 70, "fuel");
    return NULL;
  }

  /* cwasm module cache keyed by the wasm's content name */
  char cp[4200];
  cache_path(cp, sizeof cp, wasm_path);
  wasmtime_module_t *mod = NULL;
  if (getenv("PROCWT_DEBUG"))
    fprintf(stderr, "cwasm path %s\n", cp);
  wasmtime_error_t *err = wasmtime_module_deserialize_file(engine, cp, &mod);
  if (err) { wasmtime_error_delete(err); mod = NULL; }
  if (getenv("PROCWT_DEBUG"))
    fprintf(stderr, "deserialize %s\n", mod ? "hit" : "miss");
  if (!mod) {
    err = wasmtime_module_new(engine, patched, plen, &mod);
    if (err) wt_fail("proc_module_compile", err, NULL);
    wasm_byte_vec_t ser;
    err = wasmtime_module_serialize(mod, &ser);
    if (!err) {
      char tp[4216];
      snprintf(tp, sizeof tp, "%s.tmp%ld", cp, (long)getpid());
      FILE *o = fopen(tp, "wb");
      if (o) {
        fwrite(ser.data, 1, ser.size, o);
        if (!fclose(o)) rename(tp, cp);
      }
      wasm_byte_vec_delete(&ser);
    } else {
      wasmtime_error_delete(err);
    }
  }

  if (getenv("PROCWT_DEBUG")) fprintf(stderr, "module ready\n");
  wasm_trap_t *trap = NULL;
  err = wasmtime_instance_new(CTX, mod, NULL, 0, &INST, &trap);
  if (err) wt_fail("proc_instantiate", err, NULL);
  if (trap) trap_exit(trap);

  wasmtime_extern_t item;
  if (!wasmtime_instance_export_get(CTX, &INST, "memory", 6, &item) ||
      item.kind != WASMTIME_EXTERN_MEMORY) {
    result = refuse_o(err_path, "proc_abi_exports", 70, "");
    return NULL;
  }
  MEM = item.of.memory;
  wasmtime_func_t entry_fn;
  if (!get_export_fn(entry, &entry_fn) || func_params(&entry_fn) != 2) {
    result = refuse_o(err_path, "proc_abi_exports", 70, "");
    return NULL;
  }

  /* NUL-separated argv bytes for the env device (exec9 procArgBytes). */
  uint8_t argbuf[8192]; int alen = 0;
  for (int i = 8; args[i] && alen < 8188; i++) {
    int l = strlen(args[i]);
    memcpy(argbuf + alen, args[i], l); alen += l;
    argbuf[alen++] = 0;
  }

  flat_reset();
  wasmtime_val_t av[16];
  for (int i = 0; i < 16; i++) av[i].kind = WASMTIME_I64;
  av[0].of.i64 = (int64_t)MOD_FB;
  av[1].of.i64 = (int64_t)fuel;
  guest_call(&entry_fn, av, 2);
  host_mem_refresh();
  {
    uint64_t dt; uint64_t st = status_of(&dt);
    if (st) { result = status_refuse_o(err_path, st, dt); return NULL; }
  }
  /* Seven-word Proc image at FB+96 (tag.sgn, tag.mag, res, req, rep, contsF,
     contsB); updated each step. */
  uint64_t p[7];
  for (int i = 0; i < 7; i++) p[i] = mrd(MOD_FB + 96 + i * 8);

  /* Find driveS: the f-export with 13 i64 params that answers the -7
     probe with act 7, out "rsdS". Int params are flat (sgn, mag-list)
     pairs, so driveS(base, fuel, p0..p6, need.sgn, need.mag, acc, rB) is 13 words.
     The bump rewinds after each probe. */
  uint64_t need_s = 0, need_d = MOD_NIL, acc_w = MOD_NIL, r_w = MOD_NIL;
  have_step = 0;
  /* A `f<n>` step slot names driveS directly; `auto` probes every
     13-param export with -7. The named path is one probe, which keeps
     warm start inside budget on modules with hundreds of exports. */
  const char *step_arg = args[3];
  if (step_arg && step_arg[0] == 'f' && step_arg[1]) {
    wasmtime_func_t cand;
    if (get_export_fn(step_arg, &cand) && func_params(&cand) == 13 &&
        func_results(&cand) <= 4) {
      uint64_t bump0 = mrd(MOD_FB);
      uint64_t probe_mag = dig_list(7);
      av[0].of.i64 = (int64_t)MOD_FB;
      av[1].of.i64 = 200000;
      for (int j = 0; j < 7; j++) av[2 + j].of.i64 = (int64_t)p[j];
      av[9].of.i64 = 1;
      av[10].of.i64 = (int64_t)probe_mag;
      av[11].of.i64 = (int64_t)MOD_NIL;
      av[12].of.i64 = (int64_t)MOD_NIL;
      wasm_trap_t *pt = NULL;
      wasmtime_val_t rv[4];
      wasmtime_context_set_fuel(CTX, 4000000);
      wasmtime_error_t *pe = wasmtime_func_call(CTX, &cand, av, 13, rv,
                                                func_results(&cand), &pt);
      if (pe) wasmtime_error_delete(pe);
      if (pt) wasm_trap_delete(pt);
      if (!pe && !pt) {
        host_mem_refresh();
        uint64_t dt; uint64_t st = status_of(&dt);
        if (st == 0) {
          gp_bad = 0;
          int64_t act = sgn_mag(mrd(MOD_FB + 96), mrd(MOD_FB + 96 + 8));
          if (!gp_bad && act == 7) {
            int n = 0;
            int64_t *w = list_words(mrd(MOD_FB + 96 + 16), &n);
            if (!gp_bad && n == 4 && w[0] == 114 && w[1] == 115 &&
                w[2] == 100 && w[3] == 83) {
              STEP_FN = cand;
              have_step = 1;
            }
            free(w);
          }
        }
      }
      mwr(MOD_FB, bump0);
      mwr(MOD_FB + 16, 0); mwr(MOD_FB + 24, 0);
      if (getenv("PROCWT_DEBUG"))
        fprintf(stderr, "step slot %s: %s\n", step_arg,
                have_step ? "ok" : "probe failed, scanning");
    }
  }
  if (getenv("PROCWT_DEBUG")) {
    for (int i = 0; i < 256; i++) {
      char nm[16];
      snprintf(nm, sizeof nm, "f%d", i);
      wasmtime_func_t cand;
      if (!get_export_fn(nm, &cand)) continue;
      fprintf(stderr, "export %s: %d params %d results\n", nm,
              (int)func_params(&cand), (int)func_results(&cand));
    }
  }
  for (int i = 0; i < 8192 && !have_step; i++) {
    char nm[16];
    snprintf(nm, sizeof nm, "f%d", i);
    wasmtime_func_t cand;
    if (!get_export_fn(nm, &cand)) continue;
    if (func_params(&cand) != 13) continue;
    if (func_results(&cand) > 4) continue;
    if (getenv("PROCWT_DEBUG"))
      fprintf(stderr, "probe candidate %s\n", nm);
    uint64_t bump0 = mrd(MOD_FB);
    uint64_t probe_mag = dig_list(7);
    av[0].of.i64 = (int64_t)MOD_FB;
    /* the -7 probe is O(1) in a real driveS; a small fuel keeps a wrong
       candidate that diverges on probe args from stalling the scan. */
    av[1].of.i64 = 200000;
    for (int j = 0; j < 7; j++) av[2 + j].of.i64 = (int64_t)p[j];
    av[9].of.i64 = 1;
    av[10].of.i64 = (int64_t)probe_mag;
    av[11].of.i64 = (int64_t)MOD_NIL;
    av[12].of.i64 = (int64_t)MOD_NIL;
    wasm_trap_t *pt = NULL;
    wasmtime_val_t rv[4];
    wasmtime_context_set_fuel(CTX, 4000000);
    wasmtime_error_t *pe = wasmtime_func_call(CTX, &cand, av, 13, rv,
                                            func_results(&cand), &pt);
    if (pe) { wasmtime_error_delete(pe); mwr(MOD_FB, bump0); continue; }
    if (pt) { wasm_trap_delete(pt); mwr(MOD_FB, bump0); continue; }
    host_mem_refresh();
    uint64_t dt; uint64_t st = status_of(&dt);
    if (st == 0) {
      if (getenv("PROCWT_DEBUG")) {
        fprintf(stderr, "probe %s:", nm);
        for (int j = 0; j < 18; j++)
          fprintf(stderr, " %llx", (unsigned long long)mrd(MOD_FB + 96 + j * 8));
        fprintf(stderr, "\n");
        for (int j = 0; j < 18; j++) {
          uint64_t w = mrd(MOD_FB + 96 + j * 8);
          if (w >= MOD_FHEAP && w + 24 <= mod_size && !(w & 7))
            fprintf(stderr, "  w%d@%llx: %llx %llx %llx\n", j,
              (unsigned long long)w,
              (unsigned long long)mrd(w), (unsigned long long)mrd(w + 8),
              (unsigned long long)mrd(w + 16));
        }
      }
      gp_bad = 0;
      int64_t act = sgn_mag(mrd(MOD_FB + 96), mrd(MOD_FB + 96 + 8));
      if (!gp_bad && act == 7) {
        int n = 0;
        int64_t *w = list_words(mrd(MOD_FB + 96 + 16), &n);
        if (!gp_bad && n == 4 && w[0] == 114 && w[1] == 115 && w[2] == 100 &&
            w[3] == 83) {
          STEP_FN = cand;
          have_step = 1;
        }
        free(w);
      }
    }
    mwr(MOD_FB, bump0);
    mwr(MOD_FB + 16, 0); mwr(MOD_FB + 24, 0);
  }
  if (!have_step) {
    /* no driveS in the module: not a structured-step program */
    result = refuse_o(err_path, "proc_abi_exports", 70, "driveS_missing");
    return NULL;
  }

  /* Cold step: need = Int 0, acc = rB = []. Real calls get the large
     budget back — probes above ran on a 4M leash. */
  wasmtime_context_set_fuel(CTX, (uint64_t)1 << 62);
  need_s = 0; need_d = MOD_NIL;
  int curfd = -1;

  for (int n = 1; n <= MAX_STEPS; n++) {
    uint64_t bump0 = mrd(MOD_FB);
    av[0].of.i64 = (int64_t)MOD_FB;
    av[1].of.i64 = (int64_t)fuel;
    for (int j = 0; j < 7; j++) av[2 + j].of.i64 = (int64_t)p[j];
    av[9].of.i64 = (int64_t)need_s;
    av[10].of.i64 = (int64_t)need_d;
    av[11].of.i64 = (int64_t)acc_w;
    av[12].of.i64 = (int64_t)r_w;
    guest_call(&STEP_FN, av, 13);
    host_mem_refresh();
    /* capacity: a step is pure — grow memory, rewind the bump and
       status words, and call it again. */
    for (int tries = 0; ; tries++) {
      uint64_t dt; uint64_t st = status_of(&dt);
      if (st == 0) break;
      if (st == 4 || (st == 3 && dt == 1)) {
        if (tries >= 40) { result = refuse_o(err_path, "capacity", 51, ""); return NULL; }
        mwr(MOD_FB, bump0);
        mwr(MOD_FB + 16, 0); mwr(MOD_FB + 24, 0);
        uint64_t have_pages = mod_size / 65536;
        uint64_t add = have_pages / 2;
        if (add < 1024) add = 1024;        /* >=64 MiB per retry */
        host_mem_grow((uint32_t)add);
        mwr(MOD_FB + 8, mod_size);
        guest_call(&STEP_FN, av, 13);
        host_mem_refresh();
        continue;
      }
      result = status_refuse_o(err_path, st, dt);
      return NULL;
    }
    host_mem_refresh();
    if (getenv("PROCWT_DEBUG")) {
      fprintf(stderr, "step %d:", n);
      for (int j = 0; j < 18; j++)
        fprintf(stderr, " %llx", (unsigned long long)mrd(MOD_FB + 96 + j * 8));
      fprintf(stderr, "\n");
      for (int j = 0; j < 18; j++) {
        uint64_t w = mrd(MOD_FB + 96 + j * 8);
        if (w >= MOD_FHEAP && w + 24 <= mod_size && !(w & 7))
          fprintf(stderr, "  w%d@%llx: %llx %llx %llx\n", j,
            (unsigned long long)w,
            (unsigned long long)mrd(w), (unsigned long long)mrd(w + 8),
            (unsigned long long)mrd(w + 16));
      }
    }
    /* PStep flat run at FB+96: act.sgn act.mag out need.sgn need.mag
       acc p0..p6. */
    gp_bad = 0;
    int64_t act = sgn_mag(mrd(MOD_FB + 96), mrd(MOD_FB + 96 + 8));
    uint64_t out_p = mrd(MOD_FB + 96 + 16);
    need_s = mrd(MOD_FB + 96 + 24);
    need_d = mrd(MOD_FB + 96 + 32);
    acc_w = mrd(MOD_FB + 96 + 40);
    for (int j = 0; j < 7; j++) p[j] = mrd(MOD_FB + 96 + 48 + j * 8);
    int n_out = 0;
    int64_t *out = list_words(out_p, &n_out);
    if (gp_bad) {
      free(out);
      result = refuse_o(err_path, "proc_abi_reply", 56, "");
      return NULL;
    }
    r_w = MOD_NIL;

    if (act == 1) {
      if (n_out < 1) { free(out); result = refuse_o(err_path, "proc_exit_missing", 56, ""); return NULL; }
      uint8_t *bb = malloc((size_t)(n_out > 1 ? n_out - 1 : 1));
      for (int i = 1; i < n_out; i++) bb[i - 1] = (uint8_t)out[i];
      sink_write(out_path, 1, bb, (size_t)(n_out - 1));
      free(bb);
      int code = (int)(out[0] & 255);
      free(out);
      result = code;
      return NULL;
    }
    if (act == 2) {
      /* exec9: a [a-z][a-z0-9_]* residue is the refusal name; anything
         else is proc_rerror with the residue quoted. */
      int named = n_out > 0;
      for (int i = 0; i < n_out && named; i++) {
        int64_t c = out[i];
        int alpha = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
        int okc = alpha || (c >= '0' && c <= '9') || c == '_';
        if (!okc || (i == 0 && !alpha)) named = 0;
      }
      if (named) {
        char nm2[128];
        for (int i = 0; i < n_out && i < 120; i++) nm2[i] = (char)out[i];
        nm2[n_out < 120 ? n_out : 120] = 0;
        result = refuse_o(err_path, nm2, 56, "");
      } else {
        char *res = malloc((size_t)n_out + 3);
        res[0] = '"';
        for (int i = 0; i < n_out; i++) res[i + 1] = (char)out[i];
        res[n_out + 1] = '"'; res[n_out + 2] = 0;
        result = refuse_o(err_path, "proc_rerror", 56, res);
        free(res);
      }
      free(out);
      return NULL;
    }
    if (act == 0) {
      int sep = -1;
      for (int i = 0; i < n_out; i++) if (out[i] == 10) { sep = i; break; }
      if (sep < 0 || sep >= 15) { free(out); result = refuse_o(err_path, "proc_device", 56, ""); return NULL; }
      char dev[16];
      for (int i = 0; i < sep; i++) dev[i] = (char)out[i];
      dev[sep] = 0;
      if (strcmp(dev, "env") && strcmp(dev, "fs") && strcmp(dev, "store") &&
          strcmp(dev, "clock") && strcmp(dev, "cmd")) {
        free(out);
        result = refuse_o(err_path, "proc_device", 56, "");
        return NULL;
      }
      int fd = dev_conn(dev, devsrv, argbuf, alen);
      curfd = fd;
      if (getenv("PROCWT_DEBUG")) {
        fprintf(stderr, "step %d dev %s wr %d:", n, dev, n_out - sep - 1);
        for (int i = sep + 1; i < n_out && i < sep + 97; i++)
          fprintf(stderr, " %02x", (unsigned)(uint8_t)out[i]);
        fprintf(stderr, "\n");
      }
      size_t flen = (size_t)(n_out - sep - 1);
      uint8_t *fbuf = malloc(flen ? flen : 1);
      for (size_t i = 0; i < flen; i++) fbuf[i] = (uint8_t)out[sep + 1 + (int)i];
      int wrc = dev_write_frame(fd, fbuf, flen, argbuf, alen);
      free(fbuf);
      if (wrc != 0) {
        free(out);
        result = refuse_o(err_path, "proc_socket_dead", 70, dev);
        return NULL;
      }
      free(out);
      continue;
    }
    if (act == 3) {
      if (n_out != 1 || out[0] <= 0 || out[0] > READ_MAX || curfd == -1) {
        free(out);
        result = refuse_o(err_path, "proc_read_limit", 56, "");
        return NULL;
      }
      int cnt = (int)out[0];
      free(out);
      uint8_t *buf = malloc((size_t)cnt);
      int evt = read_n(curfd, buf, cnt);
      if (getenv("PROCWT_DEBUG")) {
        fprintf(stderr, "step %d rd %d evt %d:", n, cnt, evt);
        for (int i = 0; i < cnt && i < 96; i++)
          fprintf(stderr, " %02x", buf[i]);
        fprintf(stderr, "\n");
      }
      int rn = (evt == 0 ? cnt : 0) + 1;
      int64_t *rw = malloc(sizeof(int64_t) * (size_t)rn);
      rw[0] = evt;
      for (int i = 0; i < rn - 1; i++) rw[i + 1] = buf[i];
      r_w = list_i(rw, rn);
      free(rw);
      free(buf);
      continue;
    }
    free(out);
    result = refuse_o(err_path, "proc_abi_act", 56, "");
    return NULL;
  }
  result = refuse_o(err_path, "host_step_limit", 56, "");
  return NULL;
}

int main(int argc, char **argv) {
  if (argc < 8) {
    fprintf(stderr, "procwt <wasm> <entry> <step> <fuel> <out> <err> <devsrv> [args]\n");
    return 2;
  }
  args = argv;
  pthread_attr_t attr;
  pthread_t thread;
  /* The wasm runs on this thread's native stack under wasmtime; the
   * reservation covers the module's max_wasm_stack bound plus runtime
   * overhead (bootstrap/seed/stage-14274/seed-host.c). */
  if (pthread_attr_init(&attr) ||
      pthread_attr_setstacksize(&attr, (size_t)1536 * 1024 * 1024) ||
      pthread_create(&thread, &attr, run, NULL)) {
    fprintf(stderr, "[host_thread]\n");
    return 70;
  }
  pthread_attr_destroy(&attr);
  if (pthread_join(thread, NULL)) return 70;
  return result;
}
