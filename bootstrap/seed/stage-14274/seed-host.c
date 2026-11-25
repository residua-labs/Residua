/* Seed executor host on the wasmtime C API — the release recipe's
 * execution host for bootstrap/seed/stage-14274.
 *
 * Same protocol as reports/codex4-assign5-stage-word/Wasm2CHost.c (the
 * wasm2c host this file replaces in the release route): the seed's
 * structural Nat/Int ABI, canonical LE base256 digits, zero=[]. The host
 * reads the input file, writes the object graph into the module's
 * exported linear memory, calls the entry export, prints the same
 * status JSON object, and decodes the emitted byte list to the output
 * file. All compiler decisions remain in the wasm module. No compiler
 * interpretation here.
 *
 * The seed modules carry legacy exception-handling instructions, which
 * wasmtime does not implement; the recipe feeds this host the module
 * after `wasm-opt --translate-to-exnref`, which wasmtime runs with the
 * exceptions proposal enabled.
 *
 *   argv: seed-host <rsdc|rsc> <entry> <module.wasm> <input> <output>
 *                    <config> cons
 *   stdout: one JSON line
 *     {"tag":"T","status":"S","detail":"D","wall_ns":"W",
 *      "memory_bytes":M,"live_bytes":L,"peak_live_bytes":P}
 *   exit 0: the call ran and produced an output; exit 1: host failure. */
#define _POSIX_C_SOURCE 200809L /* clock_gettime under -std=c11 (glibc) */
#include <wasmtime.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static char **args;
static int result = 1;
static wasmtime_context_t *CTX;
static wasmtime_memory_t MEM;
static uint8_t *mem_data;
static size_t mem_size;
static uint64_t cursor;
static const uint64_t nil = 1;

_Noreturn static void fail(const char *reason) {
  fprintf(stderr, "%s\n", reason);
  exit(1);
}

static void refresh_mem(void) {
  mem_data = wasmtime_memory_data(CTX, &MEM);
  mem_size = wasmtime_memory_data_size(CTX, &MEM);
}

static void extent(uint64_t p, uint64_t n) {
  if (p > mem_size || n > mem_size - p) fail("seed_pointer");
}

static uint64_t read64(uint64_t p) {
  uint64_t v;
  if (p & 7) fail("seed_alignment");
  extent(p, 8);
  memcpy(&v, mem_data + p, 8);
  return v;
}

static void write64(uint64_t p, uint64_t v) {
  if (p & 7) fail("seed_alignment");
  extent(p, 8);
  memcpy(mem_data + p, &v, 8);
}

/* Borrowed block: metadata0 followed by a 24-byte OBJECT-ABI payload.
 * Int box: objects1/tag0, magnitude+8, sign byte+16.
 * Word cons: objects1/tag1, tail+8, scalar digit+16.
 * Int cons: objects2/tag1, boxed head+8, tail+16. */
static uint64_t borrowed(uint64_t objects, uint64_t tag) {
  uint64_t p = cursor + 8;
  cursor += 32;
  if (cursor > mem_size) fail("seed_input_capacity");
  write64(p - 8, 0);
  write64(p, (objects << 48) | (tag << 56));
  write64(p + 8, 0);
  write64(p + 16, 0);
  return p;
}

static uint64_t digit_cons(uint64_t d, uint64_t tail) {
  uint64_t p = borrowed(1, 1);
  write64(p + 8, tail);
  write64(p + 16, d);
  return p;
}

static uint64_t magnitude(uint64_t n) {
  uint8_t ds[8];
  unsigned count = 0;
  while (n) { ds[count++] = n & 255; n >>= 8; }
  uint64_t p = nil;
  while (count) p = digit_cons(ds[--count], p);
  return p;
}

static void object(uint64_t p, uint64_t high) {
  if (p < 65536 || (p & 7)) fail("seed_output_pointer");
  extent(p, 24);
  if ((read64(p) >> 48) != high) fail("seed_output_header");
}

static uint64_t byte_of_int(uint64_t p) {
  object(p, 1);
  if (mem_data[p + 16] != 0) fail("seed_output_negative_byte");
  uint64_t ds = read64(p + 8);
  if (ds == nil) return 0;
  object(ds, 257);
  uint64_t d = read64(ds + 16);
  if (read64(ds + 8) != nil || d == 0 || d > 255)
    fail("seed_output_byte_magnitude");
  return d;
}

static uint64_t now(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC, &t)) fail("seed_clock");
  return (uint64_t)t.tv_sec * 1000000000 + t.tv_nsec;
}

static void wt_fail(const char *where, wasmtime_error_t *err,
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
  exit(1);
}

static void *run(void *unused) {
  (void)unused;
  const int frontend = !strcmp(args[1], "rsdc");
  if ((!frontend && strcmp(args[1], "rsc")) || strcmp(args[7], "cons"))
    fail("seed_layout");
  const char *entry = args[2];
  const char *module_path = args[3];
  uint16_t endian = 1;
  if (*(uint8_t *)&endian != 1) fail("seed_host_endianness");
  char *end;
  uint64_t config = strtoull(args[6], &end, 10);
  if (!args[6][0] || *end || config > 16383 || (frontend && config))
    fail("seed_config");
  FILE *input = fopen(args[4], "rb");
  if (!input || fseek(input, 0, SEEK_END)) fail("seed_input");
  long length = ftell(input);
  if (length < 0 || (uint64_t)length >= (UINT64_C(1) << 26))
    fail("seed_input_capacity");
  rewind(input);
  uint8_t *bytes = malloc(length ? (size_t)length : 1);
  if (!bytes || fread(bytes, 1, length, input) != (size_t)length)
    fail("seed_input_read");
  fclose(input);

  wasm_config_t *cfg = wasm_config_new();
  wasmtime_config_wasm_exceptions_set(cfg, true);
  /* wasmtime runs wasm on the calling thread's native stack; the entry
   * recurses along the source's structure depth. The bound is the
   * module's own stack accounting, below the thread's reservation. */
  wasmtime_config_max_wasm_stack_set(cfg, (size_t)512 * 1024 * 1024);
  wasmtime_config_async_stack_size_set(cfg, (size_t)768 * 1024 * 1024);
  wasm_engine_t *engine = wasm_engine_new_with_config(cfg);
  if (!engine) fail("seed_engine");
  wasmtime_store_t *store = wasmtime_store_new(engine, NULL, NULL);
  CTX = wasmtime_store_context(store);

  /* Precompiled-module cache: <module>.cwasm next to the module. The
   * recipe uses a fresh output directory per run, so a stale cache
   * cannot outlive the module it was serialized from. */
  char cache_path[4096];
  int n = snprintf(cache_path, sizeof cache_path, "%s.cwasm", module_path);
  if (n < 0 || (size_t)n >= sizeof cache_path) fail("seed_path");
  wasmtime_module_t *mod = NULL;
  wasmtime_error_t *err =
      wasmtime_module_deserialize_file(engine, cache_path, &mod);
  if (err) { wasmtime_error_delete(err); mod = NULL; }
  if (!mod) {
    FILE *f = fopen(module_path, "rb");
    if (!f || fseek(f, 0, SEEK_END)) fail("seed_module");
    long mn = ftell(f);
    if (mn < 0) fail("seed_module");
    rewind(f);
    uint8_t *mbytes = malloc(mn ? (size_t)mn : 1);
    if (!mbytes || fread(mbytes, 1, mn, f) != (size_t)mn) {
      if (f) fclose(f);
      fail("seed_module_read");
    }
    fclose(f);
    err = wasmtime_module_new(engine, mbytes, (size_t)mn, &mod);
    free(mbytes);
    if (err) wt_fail("seed_module_compile", err, NULL);
    wasm_byte_vec_t ser;
    err = wasmtime_module_serialize(mod, &ser);
    if (!err) {
      char tmp_path[4104];
      snprintf(tmp_path, sizeof tmp_path, "%s.tmp", cache_path);
      FILE *o = fopen(tmp_path, "wb");
      if (o) {
        fwrite(ser.data, 1, ser.size, o);
        if (!fclose(o)) rename(tmp_path, cache_path);
      }
      wasm_byte_vec_delete(&ser);
    } else {
      wasmtime_error_delete(err);
    }
  }

  wasmtime_instance_t inst;
  wasm_trap_t *trap = NULL;
  err = wasmtime_instance_new(CTX, mod, NULL, 0, &inst, &trap);
  if (err) wt_fail("seed_instantiate", err, NULL);
  if (trap) wt_fail("seed_wasm_trap", NULL, trap);

  wasmtime_extern_t item;
  if (!wasmtime_instance_export_get(CTX, &inst, "memory", 6, &item) ||
      item.kind != WASMTIME_EXTERN_MEMORY)
    fail("seed_export_memory");
  MEM = item.of.memory;
  if (!wasmtime_instance_export_get(CTX, &inst, entry, strlen(entry),
                                    &item) ||
      item.kind != WASMTIME_EXTERN_FUNC)
    fail("seed_export_entry");
  wasmtime_func_t fn = item.of.func;

  refresh_mem();
  /* Allocate input beyond the module's immutable ground objects. */
  uint64_t heap_base = 65536;
  if (wasmtime_instance_export_get(CTX, &inst, "__heap_base", 11, &item)) {
    if (item.kind != WASMTIME_EXTERN_GLOBAL) fail("seed_export_heap_base");
    wasmtime_val_t base;
    wasmtime_global_get(CTX, &item.of.global, &base);
    if (base.kind == WASMTIME_I32) heap_base = (uint32_t)base.of.i32;
    else if (base.kind == WASMTIME_I64) heap_base = (uint64_t)base.of.i64;
    else fail("seed_export_heap_base");
    if (heap_base < 65536 || heap_base > mem_size || (heap_base & 7))
      fail("seed_export_heap_base");
  }
  cursor = heap_base;
  /* Reuse256 borrowed constants: O(input bytes) storage, not 96B/byte. */
  uint64_t capacity = heap_base + 32 * ((uint64_t)length + 520);
  uint64_t pages = (capacity + 65535) / 65536;
  uint64_t have = wasmtime_memory_size(CTX, &MEM);
  if (pages > have) {
    uint64_t prev;
    err = wasmtime_memory_grow(CTX, &MEM, pages - have, &prev);
    if (err) wt_fail("seed_memory_capacity", err, NULL);
    refresh_mem();
  }
  uint64_t byte_ints[256];
  for (unsigned b = 0; b < 256; ++b) {
    uint64_t digits = magnitude(b);
    uint64_t p = borrowed(1, 0);
    write64(p + 8, digits);
    byte_ints[b] = p;
  }
  uint64_t config_digits = magnitude(config);
  uint64_t head = nil;
  for (long i = length; i-- > 0;) {
    uint64_t p = borrowed(2, 1);
    write64(p + 8, byte_ints[bytes[i]]);
    write64(p + 16, head);
    head = p;
  }
  free(bytes);
  write64(24, cursor);
  write64(32, mem_size);
  write64(632, cursor - heap_base);
  write64(640, cursor - heap_base);
  uint64_t started = now();
  wasmtime_val_t avals[6], rvals[1];
  for (int i = 0; i < 6; ++i) avals[i].kind = WASMTIME_I64;
  avals[0].of.i64 = 24;
  if (frontend) {
    avals[1].of.i64 = (int64_t)UINT64_C(10000000000);
    avals[2].of.i64 = (int64_t)config_digits;
    avals[3].of.i64 = (int64_t)head;
    avals[4].of.i64 = 0;
  } else {
    avals[1].of.i64 = (int64_t)UINT64_C(1000000000);
    avals[2].of.i64 = 0;
    avals[3].of.i64 = (int64_t)config_digits;
    avals[4].of.i64 = (int64_t)head;
    avals[5].of.i64 = 0;
  }
  trap = NULL;
  err = wasmtime_func_call(CTX, &fn, avals, frontend ? 5 : 6, rvals, 1,
                           &trap);
  if (err) wt_fail("seed_call", err, NULL);
  if (trap) {
    wasm_byte_vec_t msg;
    wasm_trap_message(trap, &msg);
    wasm_trap_delete(trap);
    fprintf(stderr, "seed_wasm_trap:%.*s\n", (int)msg.size, msg.data);
    wasm_byte_vec_delete(&msg);
    return NULL;
  }
  uint64_t tag = (uint64_t)rvals[0].of.i64;
  uint64_t wall_ns = now() - started;

  refresh_mem();
  uint64_t status = read64(40), detail = read64(48);
  printf("{\"tag\":\"%" PRIu64 "\",\"status\":\"%" PRIu64
         "\",\"detail\":\"%" PRIu64 "\",\"wall_ns\":\"%" PRIu64
         "\",\"memory_bytes\":%" PRIu64 ",\"live_bytes\":\"%" PRIu64
         "\",\"peak_live_bytes\":\"%" PRIu64 "\"}\n",
         tag, status, detail, wall_ns, (uint64_t)mem_size, read64(632),
         read64(640));
  fflush(stdout);
  if (tag || status) fail("seed_compile_status");
  if (!frontend && (read64(120) != 0 || read64(128) != nil))
    fail("seed_compile_refusal");
  uint64_t p = read64(frontend ? 120 : 136), count = 0;
  FILE *output = fopen(args[5], "wb");
  if (!output) fail("seed_output");
  while (p != nil) {
    object(p, 258);
    if (++count > mem_size / 32) fail("seed_output_list_cycle");
    uint64_t b = byte_of_int(read64(p + 8));
    if (fputc((int)b, output) == EOF) fail("seed_output_write");
    p = read64(p + 16);
  }
  if (fclose(output) || !count) fail("seed_output_empty_or_write");
  wasmtime_module_delete(mod);
  wasmtime_store_delete(store);
  wasm_engine_delete(engine);
  result = 0;
  return NULL;
}

int main(int argc, char **argv) {
  if (argc != 8)
    fail("seed-host rsc|rsdc ENTRY WASM INPUT OUTPUT CONFIG cons");
  args = argv;
  pthread_attr_t attr;
  pthread_t thread;
  /* The wasm runs on this thread's native stack under wasmtime; the
   * reservation covers the module's max_wasm_stack bound plus runtime
   * overhead. */
  if (pthread_attr_init(&attr) ||
      pthread_attr_setstacksize(&attr, (size_t)1536 * 1024 * 1024) ||
      pthread_create(&thread, &attr, run, NULL)) fail("seed_thread");
  pthread_attr_destroy(&attr);
  if (pthread_join(thread, NULL)) fail("seed_thread_join");
  return result;
}
