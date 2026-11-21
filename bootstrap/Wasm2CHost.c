/* Stock wasm2c host glue. Compiler decisions stay in the generated module. */
/* madvise and MADV_HUGEPAGE are not POSIX: glibc declares them under _DEFAULT_SOURCE, and the builds of this
 * file name _POSIX_C_SOURCE alone. This has to stand before the first header. */
#if defined(__linux__) && !defined(_DEFAULT_SOURCE)
#define _DEFAULT_SOURCE 1
#endif
#include "seed.h"
#include "wasm-rt-exceptions.h"
#include "wasm-rt-impl.h"
#include <inttypes.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(__linux__)
#include <sys/mman.h>
#endif
#include <sys/resource.h>
#include <time.h>

#ifndef SEED_ENTRY
#error SEED_ENTRY must name a generated export
#endif
#ifndef SEED_WORDS
#error SEED_WORDS must name the pinned entry arity
#endif

static char **args;
static int result = 1;
static wasm_rt_memory_t *memory;

/* wasm32 seeds lack aw. A weak definition also links on Mach-O when
 * the generated object has no such export. A generated export overrides it. */
static int has_aw = 1;
__attribute__((weak, noinline)) uint64_t w2c_seed_aw(w2c_seed *instance) {
  (void)instance;
  has_aw = 0;
  return 32;
}

_Noreturn static void fail(const char *reason) {
  fprintf(stderr, "%s\n", reason);
  exit(1);
}

static uint64_t read64(uint64_t p) {
  uint64_t x;
  if ((p & 7) || p > memory->size || memory->size - p < 8)
    fail("seed_pointer");
  memcpy(&x, memory->data + p, 8);
  return x;
}

static void write64(uint64_t p, uint64_t x) {
  if ((p & 7) || p > memory->size || memory->size - p < 8)
    fail("seed_pointer");
  memcpy(memory->data + p, &x, 8);
}

static uint64_t now(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC, &t)) fail("seed_clock");
  return (uint64_t)t.tv_sec * 1000000000 + t.tv_nsec;
}

static void *run(void *unused) {
  (void)unused;
  const int frontend = !strcmp(args[1], "rsdc");
  const int array = !strcmp(args[5], "array");
  if ((!frontend && strcmp(args[1], "rsc")) ||
      (strcmp(args[5], "cons") && !array) || (frontend && array))
    fail("seed_layout");
  uint16_t endian = 1;
  if (*(uint8_t *)&endian != 1) fail("seed_host_endianness");
  char *end;
  uint64_t config = strtoull(args[4], &end, 10);
  if (!args[4][0] || *end || config > 255 || (frontend && config))
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
  uint64_t address_width = w2c_seed_aw(&instance);
  if (address_width != (memory->is64 ? 64 : 32) ||
      (has_aw && address_width != 64))
    fail("seed_address_width");
#if defined(__linux__) && defined(MADV_HUGEPAGE) && WASM_RT_USE_MMAP
  /* The module's whole heap is this one linear memory, and the runtime has reserved its address range up to
   * max_pages. Ask for transparent huge pages there: the kernel's usual setting (`madvise`) gives them only on
   * request, and an allocator like mimalloc asks the same way. A refusal changes nothing. */
  (void)madvise(memory->data, (size_t)memory->max_pages << 16, MADV_HUGEPAGE);
#endif
  uint64_t seed_bytes = 64 * (uint64_t)length, size_class = 6;
  if (array && length) {
    seed_bytes = 32;
    size_class = 5;
    while (seed_bytes < 24 + 8 * (uint64_t)length) {
      seed_bytes *= 2;
      size_class++;
    }
  }
  uint64_t end_input = 65536 + seed_bytes;
  if (end_input >= (UINT64_C(1) << 32)) fail("seed_input_capacity");
  uint64_t pages = (end_input + 65535) / 65536;
  if (pages > memory->pages &&
      wasm_rt_grow_memory(memory, pages - memory->pages) == UINT64_MAX)
    fail("seed_memory_capacity");
  uint64_t head = 16;
  if (array && length) {
    head = 65552;
    write64(head - 16, 1);
    write64(head - 8, size_class);
    write64(head, length);
    for (long i = 0; i < length; ++i) write64(head + 8 + 8 * i, bytes[i]);
  } else if (!array) {
    for (long i = length; i-- > 0;) {
      uint64_t p = 65552 + 64 * ((uint64_t)length - 1 - i);
      write64(p - 16, 1);
      write64(p - 8, 6);
      write64(p, UINT64_C(4611686018427387906));
      write64(p + 8, UINT64_C(144115188075855874));
      write64(p + 16, bytes[i]);
      write64(p + 24, head);
      head = p;
    }
  }
  free(bytes);
  write64(24, end_input);
  write64(32, memory->size);
  write64(632, seed_bytes);
  write64(640, seed_bytes);
  uint64_t started = now();
#if SEED_WORDS == 4
  uint64_t tag = SEED_ENTRY(&instance, 24, 1000000000, config, head);
#elif SEED_WORDS == 5
  uint64_t tag = SEED_ENTRY(&instance, 24, frontend ? 10000000000 : 1000000000,
                            config, head, 0);
#else
#error Unsupported seed entry arity
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
  if (!frontend && read64(120)) fail("seed_compile_refusal");
  uint64_t p = read64(frontend ? 120 : 128), count = 0;
  FILE *output = fopen(args[3], "wb");
  if (!output) fail("seed_output");
  if (array) {
    uint64_t n = read64(p) & UINT64_C(2305843009213693951);
    uint64_t offset = read64(136);
    if (offset > n || n > memory->size / 8) fail("seed_output_extent");
    for (uint64_t i = offset; i < n; ++i) {
      uint64_t b = read64(p + 8 + 8 * i);
      if (b > 255 || fputc((int)b, output) == EOF) fail("seed_output_byte");
      count++;
    }
  } else {
    while (p != 16) {
      if (p < 65536 || ++count > memory->size / 64 ||
          read64(p) != UINT64_C(4611686018427387906) ||
          read64(p + 8) != UINT64_C(144115188075855874))
        fail("seed_output_list");
      uint64_t b = read64(p + 16);
      if (b > 255 || fputc((int)b, output) == EOF) fail("seed_output_byte");
      p = read64(p + 24);
    }
  }
  if (fclose(output) || !count) fail("seed_output_empty_or_write");
  wasm2c_seed_free(&instance);
  wasm_rt_free();
  result = 0;
  return NULL;
}

int main(int argc, char **argv) {
  if (argc != 6) fail("Wasm2CHost rsc|rsdc INPUT OUTPUT CONFIG cons|array");
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
