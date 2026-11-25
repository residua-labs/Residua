/* Host of a compiler module that rsc's stage wrote (lib/lrc, object fields of
 * eight bytes): runs the entry of rsc or of rsdc on a file's bytes and writes
 * the result's bytes. Built against the module's wasm2c output, with
 * SEED_ENTRY (the entry's export) and SEED_FRONTEND (1 for rsdc).
 *
 * It is the stage-word Wasm2CHost.c executor host
 * that bootstrap/seed/stage-14274 pins, with one difference: a number goes in
 * as its immediate (docs/OBJECT-ABI.md "Numbers at a public entry of a stage
 * module"). The pinned file passes every input byte as the object of a limb
 * list and the stage word as a limb list. The module takes both forms and
 * gives the same bytes; with the objects every comparison of a byte goes
 * through the limbs of both numbers (the HOST-SMALL note
 * has the cost). A result is read in either form.
 * All compiler decisions remain in seed.c. No compiler interpretation here. */
#include "seed.h"
#include "wasm-rt-exceptions.h"
#include "wasm-rt-impl.h"
#include <inttypes.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef SEED_ENTRY
#error SEED_ENTRY must name the current generated export
#endif
#ifndef SEED_FRONTEND
#error SEED_FRONTEND must be 0 or 1
#endif
#if SEED_FRONTEND != 0 && SEED_FRONTEND != 1
#error Unsupported compiler entry mode
#endif

static char **args;
static int result = 1;
static wasm_rt_memory_t *memory;
static uint64_t cursor = 65536;
static const uint64_t nil = 1;

_Noreturn static void fail(const char *reason) {
  fprintf(stderr, "%s\n", reason);
  exit(1);
}

static void extent(uint64_t p, uint64_t n) {
  if (p > memory->size || n > memory->size - p) fail("seed_pointer");
}

static uint64_t read64(uint64_t p) {
  uint64_t v;
  if (p & 7) fail("seed_alignment");
  extent(p, 8);
  memcpy(&v, memory->data + p, 8);
  return v;
}

static void write64(uint64_t p, uint64_t v) {
  if (p & 7) fail("seed_alignment");
  extent(p, 8);
  memcpy(memory->data + p, &v, 8);
}

/* Borrowed block: metadata0 followed by a 24-byte OBJECT-ABI payload.
 * Int cons: objects2/tag1, head+8 (an immediate, or an Int box), tail+16.
 * Read in a result only: Int box: objects1/tag0, magnitude+8, sign byte+16;
 * word cons: objects1/tag1, tail+8, scalar digit+16. */
static uint64_t borrowed(uint64_t objects, uint64_t tag) {
  uint64_t p = cursor + 8;
  cursor += 32;
  if (cursor > memory->size) fail("seed_input_capacity");
  write64(p - 8, 0);
  write64(p, (objects << 48) | (tag << 56));
  write64(p + 8, 0);
  write64(p + 16, 0);
  return p;
}

/* The immediate of a number: 2 * n + 1, lean.h's `lean_box`. A magnitude
 * below 2^56 has one, and so has an integer of such a magnitude; what this
 * host passes (a byte, the stage word) is far below. */
static uint64_t small(uint64_t n) {
  if (n >> 55) fail("seed_small_number");
  return 2 * n + 1;
}

static void object(uint64_t p, uint64_t high) {
  if (p < 65536 || (p & 7)) fail("seed_output_pointer");
  extent(p, 24);
  if ((read64(p) >> 48) != high) fail("seed_output_header");
}

#if SEED_FRONTEND || !defined(SEED_PACKED_ENTRY)
static uint64_t byte_of_int(uint64_t p) {
  if (p & 1) {
    if (p > 511) fail("seed_output_byte_magnitude");
    return p >> 1;
  }
  object(p, 1);
  if (memory->data[p + 16] != 0) fail("seed_output_negative_byte");
  uint64_t ds = read64(p + 8);
  if (ds == nil) return 0;
  object(ds, 257);
  uint64_t d = read64(ds + 16);
  if (read64(ds + 8) != nil || d == 0 || d > 255)
    fail("seed_output_byte_magnitude");
  return d;
}
#endif

static uint64_t now(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC, &t)) fail("seed_clock");
  return (uint64_t)t.tv_sec * 1000000000 + t.tv_nsec;
}

static void *run(void *unused) {
  (void)unused;
  const int frontend = !strcmp(args[1], "rsdc");
  if (frontend != SEED_FRONTEND ||
      (!frontend && strcmp(args[1], "rsc")) || strcmp(args[5], "cons"))
    fail("seed_layout");
  uint16_t endian = 1;
  if (*(uint8_t *)&endian != 1) fail("seed_host_endianness");
  char *end;
  uint64_t config = strtoull(args[4], &end, 10);
  if (!args[4][0] || *end || config > 16383 || (frontend && config))
    fail("seed_config");
  FILE *input = fopen(args[2], "rb");
  if (!input || fseek(input, 0, SEEK_END)) fail("seed_input");
  long length = ftell(input);
  if (length < 0 || (uint64_t)length >= (UINT64_C(1) << 26))
    fail("seed_input_capacity");
  rewind(input);
  uint8_t *bytes = malloc(length ? (size_t)length : 1);
  if (!bytes || fread(bytes, 1, length, input) != (size_t)length)
    fail("seed_input_read");
  fclose(input);

  wasm_rt_init();
  wasm_rt_trap_t trap = wasm_rt_impl_try();
  if (trap) {
    fprintf(stderr, "seed_wasm_trap:%s\n", wasm_rt_strerror(trap));
    return NULL;
  }
  w2c_seed instance;
  wasm2c_seed_instantiate(&instance);
  memory = w2c_seed_memory(&instance);
  uint64_t heap_base = memory->size < 65536 ? 65536 : memory->size;
  cursor = heap_base;
  uint64_t capacity = heap_base + 32 * ((uint64_t)length + 520);
  uint64_t pages = (capacity + 65535) / 65536;
  if (pages > memory->pages &&
      wasm_rt_grow_memory(memory, pages - memory->pages) == UINT64_MAX)
    fail("seed_memory_capacity");
  uint64_t config_digits = small(config);
  uint64_t head = nil;
  for (long i = length; i-- > 0;) {
    uint64_t p = borrowed(2, 1);
    write64(p + 8, small(bytes[i]));
    write64(p + 16, head);
    head = p;
  }
  free(bytes);
  write64(24, cursor);
  write64(32, memory->size);
  write64(632, cursor - heap_base);
  write64(640, cursor - heap_base);
  uint64_t started = now();
#if SEED_FRONTEND
  uint64_t tag = SEED_ENTRY(&instance, 24, UINT64_C(10000000000),
                            config_digits, head, 0);
#elif defined(SEED_PACKED_ENTRY)
  uint64_t tag = SEED_PACKED_ENTRY(&instance, 24, UINT64_C(1000000000),
                                   0, config_digits, head, 0);
#else
  uint64_t tag = SEED_ENTRY(&instance, 24, UINT64_C(1000000000),
                            0, config_digits, head, 0);
#endif
  uint64_t wall_ns = now() - started;
  uint64_t status = read64(40), detail = read64(48);
  printf("{\"tag\":\"%" PRIu64 "\",\"status\":\"%" PRIu64
         "\",\"detail\":\"%" PRIu64 "\",\"wall_ns\":\"%" PRIu64
         "\",\"memory_bytes\":%" PRIu64 ",\"live_bytes\":\"%" PRIu64
         "\",\"peak_live_bytes\":\"%" PRIu64 "\"}\n",
         tag, status, detail, wall_ns, memory->size, read64(632), read64(640));
  fflush(stdout);
  if (tag || status) fail("seed_compile_status");
  if (!frontend && (read64(120) != 0 || read64(128) != nil))
    fail("seed_compile_refusal");
  uint64_t p = read64(frontend ? 120 : 136), count = 0;
  FILE *output = fopen(args[3], "wb");
  if (!output) fail("seed_output");
#if !SEED_FRONTEND && defined(SEED_PACKED_ENTRY)
  uint64_t written = 0;
  while (p != nil) {
    object(p, 257);
    if (++count > memory->size / 24) fail("seed_output_list_cycle");
    uint64_t chunk_len = read64(p + 16);
    p = read64(p + 8);
    if (!chunk_len || chunk_len > (UINT64_C(1) << 31))
      fail("seed_output_chunk_length");
    while (chunk_len > 0) {
      if (p == nil) fail("seed_output_chunk_trunc");
      object(p, 257);
      if (++count > memory->size / 24) fail("seed_output_list_cycle");
      uint64_t w = read64(p + 16);
      if (w > UINT64_C(0xffffffff)) fail("seed_output_word_magnitude");
      uint8_t buf[4] = {
        (uint8_t)(w & 255),
        (uint8_t)((w >> 8) & 255),
        (uint8_t)((w >> 16) & 255),
        (uint8_t)((w >> 24) & 255),
      };
      size_t take = chunk_len < 4 ? (size_t)chunk_len : 4;
      if (fwrite(buf, 1, take, output) != take) fail("seed_output_write");
      written += take;
      chunk_len -= take;
      p = read64(p + 8);
    }
  }
  if (fclose(output) || !written) fail("seed_output_empty_or_write");
#else
  while (p != nil) {
    object(p, 258);
    if (++count > memory->size / 32) fail("seed_output_list_cycle");
    uint64_t b = byte_of_int(read64(p + 8));
    if (fputc((int)b, output) == EOF) fail("seed_output_write");
    p = read64(p + 16);
  }
  if (fclose(output) || !count) fail("seed_output_empty_or_write");
#endif
  wasm2c_seed_free(&instance);
  wasm_rt_free();
  result = 0;
  return NULL;
}

int main(int argc, char **argv) {
  if (argc != 6) fail("Wasm2CHost rsc|rsdc INPUT OUTPUT CONFIG cons");
  args = argv;
  pthread_attr_t attr;
  pthread_t thread;
  if (pthread_attr_init(&attr) ||
      pthread_attr_setstacksize(&attr, (size_t)1024 * 1024 * 1024) ||
      pthread_create(&thread, &attr, run, NULL)) fail("seed_thread");
  pthread_attr_destroy(&attr);
  if (pthread_join(thread, NULL)) fail("seed_thread_join");
  return result;
}
