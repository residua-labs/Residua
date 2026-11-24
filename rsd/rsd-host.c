// rsd/rsd-host.c — C execution host for rsc-ABI wasm (RSD-0).
// Same protocol as rsd/runhost.cjs (the portable node fallback):
//   argv: rsd-host <wasm> <export> <fuel> <retCode> [i64 args...]
//   rsc ABI on main (rsc.rsd offBump..offCap, resAt, as rsc/out/rowhost.cjs):
//   block at 24: +0 bump +8 limit +16 status +24 detail +32 abump +40 cap;
//   the export returns the outcome tag (0 value 1 residue 2 fuel 3 stuck
//   4 capacity); the result word is at block+96; heap at 65536.
// The wasm must already export `memory` (rsdc patches the export section
// at store time; stored bytes are what this host loads — unchanged ABI).
// stdout protocol (one per line):
//   status <value|residue|fuel|stuck|trap>
//   detail <name|n>
//   value_i64 <n>
//   value_hex <utf8 hex of rendered value>   (only when status is value)
// Exit 0 always means the call ran; exit 1 means the host itself failed.
#include <wasmtime.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define BLOCK 24
#define RES 96
#define HEAP 65536
#define EMPTYSTR 8
#define EMPTYLIST 16
#define FWD (1ULL << 61)
#define HASMAP (1ULL << 62)
#define MASK ((1ULL << 61) - 1)

static wasmtime_context_t *CTX;
static wasmtime_memory_t MEM;
static uint8_t *mem_data;
static size_t mem_size;

// memory grows under GC — the data pointer must be re-fetched, never cached
// across a call (same reason runhost rebuilds its DataView).
static void refresh_mem(void) {
  mem_data = wasmtime_memory_data(CTX, &MEM);
  mem_size = wasmtime_memory_data_size(CTX, &MEM);
}
static int64_t rd64(size_t off) {
  int64_t v;
  memcpy(&v, mem_data + off, 8);
  return v;
}
static void wr64(size_t off, int64_t v) { memcpy(mem_data + off, &v, 8); }

// RSD_TIME=1: `[rsd_time] <phase> <us>` on stderr, us since the last mark.
static int TIME_ON;
static uint64_t T_LAST;
static uint64_t now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}
static void mark(const char *phase) {
  if (!TIME_ON) return;
  uint64_t t = now_ns();
  fprintf(stderr, "[rsd_time] %s %llu\n", phase, (unsigned long long)((t - T_LAST) / 1000));
  T_LAST = now_ns();
}

struct buf {
  char *p;
  size_t n, cap;
};
static void bput(struct buf *b, char c) {
  if (b->n + 1 >= b->cap) {
    b->cap = b->cap ? b->cap * 2 : 256;
    b->p = realloc(b->p, b->cap);
  }
  b->p[b->n++] = c;
  b->p[b->n] = 0;
}
static void bputs(struct buf *b, const char *s) {
  while (*s) bput(b, *s++);
}
static void bputi(struct buf *b, int64_t v) {
  char tmp[32];
  snprintf(tmp, sizeof tmp, "%lld", (long long)v);
  bputs(b, tmp);
}

static size_t chase(size_t p, int64_t *h) {
  for (;;) {
    int64_t hv = rd64(p);
    if (hv < 0 && (((uint64_t)hv) & FWD)) {
      p = (size_t)rd64(p + 8);
      continue;
    }
    *h = hv;
    return p;
  }
}

// OBJECT-ABI v1 String (tag 249): byte_size including the trailing NUL at
// +8, capacity at +16, character count at +24, packed UTF-8 at +32.
// Tag 249 sets the old forwarding bit, so that chase must not run first.
// runhost.cjs decodes the same layout. An older blob is an i64 header
// (len in the low 61 bits) and then one byte per i64 slot.
static void str_at(struct buf *b, size_t p0) {
  if (p0 == EMPTYSTR || p0 == 0) return;
  if (p0 >= 8 && mem_size >= 40 && p0 <= mem_size - 40) {
    int64_t h0 = rd64(p0);
    unsigned tag = (unsigned)(((uint64_t)h0 >> 56) & 0xffu);
    if (tag == 249) {
      int64_t n64 = rd64(p0 + 8);
      if (n64 < 1) return;
      uint64_t n = (uint64_t)n64 - 1;
      if (p0 <= mem_size - 32 && n <= mem_size - 32 - p0) {
        for (uint64_t i = 0; i < n; i++)
          bput(b, (char)mem_data[p0 + 32 + i]);
        return;
      }
      char tmp[64];
      snprintf(tmp, sizeof tmp, "<str@%zu>", p0);
      bputs(b, tmp);
      return;
    }
  }
  int64_t h;
  size_t q = chase(p0, &h);
  if (h < 0) {
    bputs(b, "<bad-str>");
    return;
  }
  uint64_t n = ((uint64_t)h) & MASK;
  for (uint64_t i = 0; i < n; i++)
    bput(b, (char)(rd64(q + 8 + i * 8) & 0xff));
}

// linked cons cell: header = payload words | bit63 allPtr | bit62 hasMap;
// hasMap adds a map word at +8 (payload then at +16). head is payload
// word 0, tail the last payload word; nil is the EMPTYLIST pointer. (allPtr
// cell: negative header, head +8, tail +16; hasMap cell like `list i64`:
// positive header, head +16, tail +24.)
static void list_at(struct buf *b, size_t p0, int elem) {
  bput(b, '[');
  int first = 1;
  for (int i = 0; i < 100000; i++) {
    if (p0 == EMPTYLIST) break;
    int64_t h;
    size_t q = chase(p0, &h);
    uint64_t pay = ((uint64_t)h) & MASK;
    if (pay < 2) break;
    size_t base = q + ((((uint64_t)h) & HASMAP) ? 16 : 8);
    int64_t head = rd64(base);
    if (!first) bput(b, ' ');
    first = 0;
    if (elem == 3) str_at(b, (size_t)head);
    else bputi(b, head);
    p0 = (size_t)rd64(base + 8 * (pay - 1));
  }
  bput(b, ']');
}

// Lean's integers and strings as the front end writes them (rsdc/Compile.rsd): a Nat is the list
// of its base-256 digits, least first; an Int is two result words, a sign and such a list; a
// String is the list of its code points. A list cell is an object of docs/OBJECT-ABI.md revision
// 2: the number of object fields at bits 48..55 of the header; with a scalar head that is 1, the
// tail at +8 and the head at +16. nil is a boxed scalar, which is odd. runhost.cjs decodes the
// same layout.
// The scalar heads of the list at p0, malloc'd into *out with their count in *n; 0 when p0 is no
// such list.
static int scalars_at(size_t p0, int64_t **out, size_t *n) {
  size_t cap = 16, k = 0;
  int64_t *xs = malloc(cap * sizeof *xs);
  if (!xs) return 0;
  while ((p0 & 7) == 0 && p0 >= 8 && mem_size >= 24 && p0 <= mem_size - 24 && k <= mem_size / 24) {
    if (((((uint64_t)rd64(p0)) >> 48) & 0xffu) != 1) { free(xs); return 0; }
    if (k == cap) {
      cap *= 2;
      int64_t *ys = realloc(xs, cap * sizeof *xs);
      if (!ys) { free(xs); return 0; }
      xs = ys;
    }
    xs[k++] = rd64(p0 + 16);
    p0 = (size_t)rd64(p0 + 8);
  }
  if ((p0 & 1) != 1) { free(xs); return 0; }
  *out = xs;
  *n = k;
  return 1;
}

// The decimal of the natural number whose base-256 digits are ds[0..n), least first, with a minus
// sign when neg and the number is not zero. *low gets the value's low 64 bits. 0 when a digit is
// no byte.
static int nat_put(struct buf *b, const int64_t *ds, size_t n, int neg, int64_t *low) {
  uint8_t *d = malloc(n ? n : 1);
  if (!d) return 0;
  for (size_t i = 0; i < n; i++) {
    if (ds[i] < 0 || ds[i] > 255) { free(d); return 0; }
    d[i] = (uint8_t)ds[i];
  }
  uint64_t lo = 0;
  for (size_t i = 0; i < n && i < 8; i++) lo |= (uint64_t)d[i] << (8 * i);
  size_t top = n;
  while (top > 0 && d[top - 1] == 0) top--;
  int zero = top == 0;
  // 256 < 10^3: three decimal digits for each base-256 digit are enough
  char *dec = malloc(top * 3 + 2);
  if (!dec) { free(d); return 0; }
  size_t k = 0;
  while (top > 0) {
    unsigned rem = 0;
    for (size_t i = top; i-- > 0;) {
      unsigned cur = rem * 256u + d[i];
      d[i] = (uint8_t)(cur / 10u);
      rem = cur % 10u;
    }
    dec[k++] = (char)('0' + rem);
    while (top > 0 && d[top - 1] == 0) top--;
  }
  if (zero) dec[k++] = '0';
  if (neg && !zero) bput(b, '-');
  while (k > 0) bput(b, dec[--k]);
  *low = (int64_t)(neg && !zero ? (uint64_t)0 - lo : lo);
  free(dec);
  free(d);
  return 1;
}

static void utf8_put(struct buf *b, uint32_t c) {
  if (c < 0x80) {
    bput(b, (char)c);
  } else if (c < 0x800) {
    bput(b, (char)(0xc0 | (c >> 6)));
    bput(b, (char)(0x80 | (c & 0x3f)));
  } else if (c < 0x10000) {
    bput(b, (char)(0xe0 | (c >> 12)));
    bput(b, (char)(0x80 | ((c >> 6) & 0x3f)));
    bput(b, (char)(0x80 | (c & 0x3f)));
  } else {
    bput(b, (char)(0xf0 | (c >> 18)));
    bput(b, (char)(0x80 | ((c >> 12) & 0x3f)));
    bput(b, (char)(0x80 | ((c >> 6) & 0x3f)));
    bput(b, (char)(0x80 | (c & 0x3f)));
  }
}

// p is the first result word and p2 the second. *shown is what value_i64 prints: the low 64 bits
// of an Int or a Nat, the first result word otherwise.
static void decode(struct buf *b, int64_t p, int64_t p2, int ret, int64_t *shown) {
  *shown = p;
  if (ret == 1 || ret == 4) {
    int64_t *ds;
    size_t n;
    if (scalars_at((size_t)(ret == 1 ? p2 : p), &ds, &n)) {
      int ok = nat_put(b, ds, n, ret == 1 && p != 0, shown);
      free(ds);
      if (ok) return;
      b->n = 0;
      *shown = p;
    }
    bputs(b, ret == 1 ? "<int@" : "<nat@");
    bputi(b, p);
    bput(b, '>');
  } else if (ret == 2 || ret == 5) {
    bputi(b, p);
  } else if (ret == 3) {
    int64_t *cs;
    size_t n;
    if (scalars_at((size_t)p, &cs, &n)) {
      int ok = 1;
      for (size_t i = 0; i < n; i++) ok = ok && cs[i] >= 0 && cs[i] <= 0x10ffff;
      if (ok)
        for (size_t i = 0; i < n; i++) utf8_put(b, (uint32_t)cs[i]);
      free(cs);
      if (ok) return;
    }
    str_at(b, (size_t)p);
  } else if (ret >= 1000) {
    list_at(b, (size_t)p, ret - 1000);
  } else {
    bputs(b, "<ptr ");
    bputi(b, p);
    bput(b, '>');
  }
}

static int host_trap(const char *msg) {
  fprintf(stderr, "trap %.300s\n", msg);
  printf("status trap\nvalue_i64 0\n");
  return 1;
}

static int host_trap_wt(wasmtime_error_t *err, wasm_trap_t *trap) {
  wasm_byte_vec_t msg;
  if (err) {
    wasmtime_error_message(err, &msg);
    wasmtime_error_delete(err);
  } else {
    wasm_trap_message(trap, &msg);
    wasm_trap_delete(trap);
  }
  int r = host_trap(msg.data);
  wasm_byte_vec_delete(&msg);
  return r;
}

// Precompiled module cache (CHAIN-CLOSE-0 Methods by source, rsd warm
// start: wasmtime's Module::serialize / Module::deserialize):
//   --cwasm-in P   deserialize the compiled module from P. The caller has
//                  checked P's bytes against their q; wasmtime itself refuses
//                  an artifact from another version / config / target.
//   --cwasm-out P  compile from the wasm, then serialize the module to P.
// A refused --cwasm-in falls back to compiling (stderr `[cwasm_refused]`).
// One request: fresh store + module + instance on `engine`, same protocol
// as the one-shot main (status/detail/value lines on stdout; the exit code
// is the return value). Shared by main and the resident `--worker` loop
// (RSD-OPT-1), so served requests produce identical bytes.
static int run_one(wasm_engine_t *engine, const char *cwasm_in, const char *cwasm_out,
                   const char *wasm_path, const char *exp, int64_t fuel, int ret,
                   int nargs, char **argvs) {
  wasmtime_store_t *store = wasmtime_store_new(engine, NULL, NULL);
  CTX = wasmtime_store_context(store);
  mark("h_engine");
  int rc = 1;

  wasmtime_module_t *mod = NULL;
  wasmtime_error_t *err = NULL;
  if (cwasm_in) {
    err = wasmtime_module_deserialize_file(engine, cwasm_in, &mod);
    if (err) {
      wasm_byte_vec_t msg;
      wasmtime_error_message(err, &msg);
      fprintf(stderr, "[cwasm_refused] %.*s\n", (int)msg.size, msg.data);
      wasm_byte_vec_delete(&msg);
      wasmtime_error_delete(err);
      err = NULL;
      mod = NULL;
    }
    mark("h_deserialize");
  }
  if (!mod) {
    FILE *f = fopen(wasm_path, "rb");
    if (!f) { rc = host_trap("open failed"); goto done; }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *bytes = malloc(n);
    if (fread(bytes, 1, n, f) != (size_t)n) {
      fclose(f);
      rc = host_trap("read failed"); goto done;
    }
    fclose(f);
    err = wasmtime_module_new(engine, bytes, n, &mod);
    free(bytes);
    if (err) { rc = host_trap_wt(err, NULL); goto done; }
    mark("h_compile");
    if (cwasm_out) {
      wasm_byte_vec_t ser;
      err = wasmtime_module_serialize(mod, &ser);
      if (err) {
        wasmtime_error_delete(err);
        err = NULL;
      } else {
        FILE *o = fopen(cwasm_out, "wb");
        if (o) {
          fwrite(ser.data, 1, ser.size, o);
          fclose(o);
        }
        wasm_byte_vec_delete(&ser);
      }
      mark("h_serialize");
    }
  }

  wasmtime_instance_t inst;
  wasm_trap_t *trap = NULL;
  err = wasmtime_instance_new(CTX, mod, NULL, 0, &inst, &trap);
  if (err) { rc = host_trap_wt(err, NULL); goto done; }
  if (trap) { rc = host_trap_wt(NULL, trap); goto done; }

  wasmtime_extern_t item;
  if (!wasmtime_instance_export_get(CTX, &inst, "memory", 6, &item) ||
      item.kind != WASMTIME_EXTERN_MEMORY) {
    rc = host_trap("export_missing memory"); goto done;
  }
  MEM = item.of.memory;

  if (!wasmtime_instance_export_get(CTX, &inst, exp, strlen(exp), &item) ||
      item.kind != WASMTIME_EXTERN_FUNC) {
    rc = host_trap("export_missing"); goto done;
  }
  wasmtime_func_t fn = item.of.func;
  mark("h_instantiate");

  refresh_mem();
  wr64(BLOCK + 0, HEAP);
  wr64(BLOCK + 8, (int64_t)mem_size);
  wr64(BLOCK + 16, 0);
  wr64(BLOCK + 24, 0);
  wr64(BLOCK + 32, 0);
  wr64(BLOCK + 40, 0);

  wasmtime_val_t *avals = calloc(2 + nargs, sizeof(wasmtime_val_t));
  wasmtime_val_t rvals[1];
  avals[0].kind = WASMTIME_I64;
  avals[0].of.i64 = BLOCK;
  avals[1].kind = WASMTIME_I64;
  avals[1].of.i64 = fuel;
  for (int i = 0; i < nargs; i++) {
    avals[2 + i].kind = WASMTIME_I64;
    avals[2 + i].of.i64 = strtoll(argvs[i], NULL, 10);
  }

  err = wasmtime_func_call(CTX, &fn, avals, 2 + nargs, rvals, 1, &trap);
  if (err) { free(avals); rc = host_trap_wt(err, NULL); goto done; }
  if (trap) { free(avals); rc = host_trap_wt(NULL, trap); goto done; }
  int64_t tag = rvals[0].of.i64;
  mark("h_call");

  refresh_mem();
  int64_t detail = rd64(BLOCK + 24);
  int64_t result = rd64(BLOCK + RES);
  const char *tn = tag == 0   ? "value"
                   : tag == 1 ? "residue"
                   : tag == 2 ? "fuel"
                   : tag == 3 ? "stuck"
                   : tag == 4 ? "capacity"
                              : "?";
  char dnbuf[32];
  const char *dn;
  if (tag == 1)
    dn = detail == 1   ? "divisionByZero"
         : detail == 2 ? "nonExactDivision"
         : detail == 3 ? "signedOverflow"
                       : (snprintf(dnbuf, sizeof dnbuf, "%lld", (long long)detail), dnbuf);
  else {
    snprintf(dnbuf, sizeof dnbuf, "%lld", (long long)detail);
    dn = dnbuf;
  }
  printf("status %s\n", tn);
  printf("detail %s\n", dn);
  if (tag == 0) {
    struct buf b = {0};
    int64_t shown = result;
    decode(&b, result, rd64(BLOCK + RES + 8), ret, &shown);
    printf("value_i64 %lld\n", (long long)shown);
    printf("value_hex ");
    for (size_t i = 0; i < b.n; i++) printf("%02x", (unsigned char)b.p[i]);
    printf("\n");
    free(b.p);
  } else {
    printf("value_i64 %lld\n", (long long)result);
  }
  free(avals);
  rc = 0;
done:
  fflush(stdout);
  if (mod) wasmtime_module_delete(mod);
  wasmtime_store_delete(store);
  return rc;
}

// The resident host worker (RSD-OPT-1): one engine, one request per
// stdin line — `cwasm_in|cwasm_out|wasm|export|fuel|ret|nargs|arg|...`
// (`-` for no cwasm field) — answered with the usual protocol lines
// plus an `end` sentinel. The rsd resident server holds the pipes, so
// a second hello costs no process spawn.
static const char *nonul(const char *s) { return s && strcmp(s, "-") ? s : NULL; }
static int worker_main(void) {
  wasm_engine_t *engine = wasm_engine_new();
  static char line[1 << 20];
  static char *argvs[512];
  while (fgets(line, sizeof line, stdin)) {
    char *save = NULL;
    const char *cw_in = strtok_r(line, "|\n", &save);
    const char *cw_out = strtok_r(NULL, "|\n", &save);
    const char *wasm = strtok_r(NULL, "|\n", &save);
    const char *exp = strtok_r(NULL, "|\n", &save);
    const char *fuel_s = strtok_r(NULL, "|\n", &save);
    const char *ret_s = strtok_r(NULL, "|\n", &save);
    const char *nargs_s = strtok_r(NULL, "|\n", &save);
    if (!wasm || !exp || !fuel_s || !ret_s || !nargs_s) {
      printf("status trap\ndetail bad_request\nvalue_i64 0\nend\n");
      fflush(stdout);
      continue;
    }
    int nargs = atoi(nargs_s);
    if (nargs < 0 || nargs > 500) nargs = 0;
    for (int i = 0; i < nargs; i++) {
      argvs[i] = strtok_r(NULL, "|\n", &save);
      if (!argvs[i]) argvs[i] = (char *)"0";
    }
    run_one(engine, nonul(cw_in), nonul(cw_out),
            wasm, exp, strtoll(fuel_s, NULL, 10), atoi(ret_s), nargs, argvs);
    printf("end\n");
    fflush(stdout);
  }
  return 0;
}

int main(int argc, char **argv) {
  TIME_ON = getenv("RSD_TIME") != NULL;
  T_LAST = now_ns();
  const char *cwasm_in = NULL, *cwasm_out = NULL;
  if (argc >= 2 && strcmp(argv[1], "--worker") == 0)
    return worker_main();
  while (argc >= 3 && (strcmp(argv[1], "--cwasm-in") == 0 || strcmp(argv[1], "--cwasm-out") == 0)) {
    if (argv[1][8] == 'i') cwasm_in = argv[2];
    else cwasm_out = argv[2];
    argv += 2;
    argc -= 2;
  }
  if (argc < 5) {
    fprintf(stderr, "usage: rsd-host [--worker] [--cwasm-in P | --cwasm-out P] <wasm> <export> <fuel> <ret> [i64 args...]\n");
    return 1;
  }
  const char *wasm_path = argv[1], *exp = argv[2];
  int64_t fuel = strtoll(argv[3], NULL, 10);
  int ret = atoi(argv[4]);
  int nargs = argc - 5;

  wasm_engine_t *engine = wasm_engine_new();
  int r = run_one(engine, cwasm_in, cwasm_out, wasm_path, exp, fuel, ret, nargs, argv + 5);
  wasm_engine_delete(engine);
  return r;
}
