/* C-only Proc transport for modules compiled by the committed cons64 seed.
 * The generated RSD entry is (state words, response words) -> reply words.
 * RSD owns continuations, 9P framing and all verdicts. This file only moves
 * opaque words and bytes between a fresh Wasm instance and Unix sockets.
 */
#include "seed.h"
#include "wasm-rt-exceptions.h"
#include "wasm-rt-impl.h"
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <time.h>
#include <unistd.h>

#ifndef PROC_STEP
#error PROC_STEP must name the pinned step export
#endif
/* The lowered source may take a final scratch arena parameter. Proc state and
 * replies contain only serialized words, so no arena handle crosses a call.
 * Pin this mode with the export signature; never infer it at runtime. */
#ifndef PROC_STEP_ARENA
#define PROC_STEP_ARENA 0
#endif
#if PROC_STEP_ARENA != 0 && PROC_STEP_ARENA != 1
#error PROC_STEP_ARENA must be zero or one
#endif
#define MAX_WORDS 1048576
#define MAX_IO 8192
#define MAX_CONNECTIONS 16
#define NIL UINT64_C(16)
#define CONS_HEADER UINT64_C(4611686018427387906)
#define CONS_MAP UINT64_C(144115188075855874)

typedef struct { uint64_t *v; size_t n; } Words;
typedef struct { char name[33]; int fd; } Connection;
static char **args;
static int result = 70;
static wasm_rt_memory_t *memory;
static FILE *trace;
static uint64_t fuel, io_ms;

_Noreturn static void fail(const char *name, int code) {
  fprintf(stderr, "%s\n", name);
  exit(code);
}
static uint64_t now_ms(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC, &t)) fail("proc_host_clock", 70);
  return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000;
}
static uint64_t number(const char *s, uint64_t limit) {
  if (!*s) fail("proc_host_number", 70);
  uint64_t n = 0;
  for (; *s; s++) {
    if (*s < '0' || *s > '9' || n > (limit - (uint64_t)(*s - '0')) / 10)
      fail("proc_host_number", 70);
    n = n * 10 + (uint64_t)(*s - '0');
  }
  if (!n) fail("proc_host_number", 70);
  return n;
}
static uint64_t read64(uint64_t p) {
  uint64_t n;
  if ((p & 7) || p > memory->size || memory->size - p < 8)
    fail("proc_abi_pointer", 56);
  memcpy(&n, memory->data + p, 8);
  return n;
}
static void write64(uint64_t p, uint64_t n) {
  if ((p & 7) || p > memory->size || memory->size - p < 8)
    fail("proc_abi_pointer", 56);
  memcpy(memory->data + p, &n, 8);
}
static Words copy_words(const uint64_t *v, size_t n) {
  if (n > MAX_WORDS) fail("proc_words_limit", 51);
  Words w = { malloc((n ? n : 1) * sizeof(uint64_t)), n };
  if (!w.v) fail("proc_host_memory", 51);
  if (n) memcpy(w.v, v, n * sizeof(uint64_t));
  return w;
}
static uint64_t list(Words w) {
  uint64_t bump = read64(24), end = bump + 64 * (uint64_t)w.n;
  if (w.n > MAX_WORDS || end >= UINT64_C(4294967296))
    fail("proc_words_limit", 51);
  uint64_t pages = (end + 65535) / 65536;
  if (pages > memory->pages &&
      wasm_rt_grow_memory(memory, pages - memory->pages) == UINT64_MAX)
    fail("capacity", 51);
  uint64_t head = NIL;
  for (size_t i = w.n; i > 0; i--) {
    uint64_t p = bump + 16 + 64 * (uint64_t)(w.n - i);
    write64(p - 16, 1);
    write64(p - 8, 6);
    write64(p, CONS_HEADER);
    write64(p + 8, CONS_MAP);
    write64(p + 16, w.v[i - 1]);
    write64(p + 24, head);
    head = p;
  }
  write64(24, end);
  write64(32, memory->size);
  return head;
}
static Words words(uint64_t p) {
  size_t cap = 64;
  Words w = { malloc(cap * sizeof(uint64_t)), 0 };
  if (!w.v) fail("proc_host_memory", 51);
  while (p != NIL) {
    if (w.n == MAX_WORDS) fail("proc_words_limit", 51);
    if (p < 65536 || read64(p) != CONS_HEADER || read64(p + 8) != CONS_MAP)
      fail("proc_abi_list", 56);
    if (w.n == cap) {
      cap *= 2;
      uint64_t *v = realloc(w.v, cap * sizeof(uint64_t));
      if (!v) fail("proc_host_memory", 51);
      w.v = v;
    }
    w.v[w.n++] = read64(p + 16);
    p = read64(p + 24);
  }
  return w;
}
static void trace_words(Words w) {
  if (!trace) return;
  uint64_t n = w.n;
  if (fwrite(&n, 8, 1, trace) != 1 ||
      (w.n && fwrite(w.v, 8, w.n, trace) != w.n))
    fail("proc_trace_write", 70);
}
static Words call(Words state, Words response) {
  w2c_seed instance;
  wasm2c_seed_instantiate(&instance);
  memory = w2c_seed_memory(&instance);
  write64(24, 65536);
  write64(32, memory->size);
  uint64_t a = list(state), b = list(response);
  write64(632, 64 * (state.n + response.n));
  write64(640, read64(632));
#if PROC_STEP_ARENA
  uint64_t tag = PROC_STEP(&instance, 24, fuel, a, b, NIL);
#else
  uint64_t tag = PROC_STEP(&instance, 24, fuel, a, b);
#endif
  uint64_t status = read64(40), detail = read64(48);
  if (tag || status) {
    fprintf(stderr, "proc_wasm_status:%" PRIu64 ":%" PRIu64 ":%" PRIu64 "\n", tag, status, detail);
    if (status == 2) fail("fuel", 50);
    if (status == 4 || (status == 3 && detail == 1)) fail("capacity", 51);
    if (status == 3) fail("stuck", 55);
    fail("proc_abi_status", 56);
  }
  Words reply = words(read64(120));
  trace_words(state);
  trace_words(response);
  trace_words(reply);
  if (trace && fflush(trace)) fail("proc_trace_write", 70);
  wasm2c_seed_free(&instance);
  return reply;
}
static int ready(int fd, short events, uint64_t deadline) {
  for (;;) {
    uint64_t now = now_ms();
    if (now >= deadline) return 0;
    uint64_t remaining = deadline - now;
    struct pollfd p = { fd, events, 0 };
    int n = poll(&p, 1, remaining > INT_MAX ? INT_MAX : (int)remaining);
    if (n < 0 && errno == EINTR) continue;
    if (n < 0) return -1;
    if (!n) return 0;
    return 1;
  }
}
static void send_bytes(int fd, const uint64_t *v, size_t n) {
  unsigned char bytes[MAX_IO];
  if (n > MAX_IO) fail("proc_send_limit", 56);
  for (size_t i = 0; i < n; i++) {
    if (v[i] > 255) fail("proc_abi_byte", 56);
    bytes[i] = (unsigned char)v[i];
  }
  uint64_t deadline = now_ms() + io_ms;
  size_t at = 0;
  while (at < n) {
    if (ready(fd, POLLOUT, deadline) != 1) fail("proc_device_write_timeout", 70);
    ssize_t k = write(fd, bytes + at, n - at);
    if (k < 0 && errno == EINTR) continue;
    if (k <= 0) fail("proc_device_write", 70);
    at += (size_t)k;
  }
}
static Words receive_bytes(int fd, size_t n) {
  Words w = copy_words(NULL, 0);
  free(w.v);
  w.v = malloc((n + 1) * sizeof(uint64_t));
  if (!w.v) fail("proc_host_memory", 51);
  w.n = 1;
  w.v[0] = 0;
  uint64_t deadline = now_ms() + io_ms;
  while (w.n - 1 < n) {
    int r = ready(fd, POLLIN, deadline);
    if (r <= 0) { w.v[0] = r ? 2 : 4; break; }
    unsigned char bytes[MAX_IO];
    ssize_t k = read(fd, bytes, n - (w.n - 1));
    if (k < 0 && errno == EINTR) continue;
    if (k < 0) { w.v[0] = 2; break; }
    if (!k) { w.v[0] = 1; break; }
    for (ssize_t i = 0; i < k; i++) w.v[w.n++] = bytes[i];
  }
  return w;
}
static int connection(Connection *cs, size_t *count, const uint64_t *out, size_t n, size_t *start) {
  size_t len = 0;
  while (len < n && out[len] != 10) len++;
  if (!len || len > 32 || len == n) fail("proc_device_name", 70);
  char name[33];
  for (size_t i = 0; i < len; i++) {
    uint64_t c = out[i];
    if (!((c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_'))
      fail("proc_device_name", 70);
    name[i] = (char)c;
  }
  name[len] = 0;
  *start = len + 1;
  for (size_t i = 0; i < *count; i++) if (!strcmp(cs[i].name, name)) return cs[i].fd;
  if (*count == MAX_CONNECTIONS) fail("proc_device_limit", 70);
  struct sockaddr_un addr;
  memset(&addr, 0, sizeof(addr));
  addr.sun_family = AF_UNIX;
  int size = snprintf(addr.sun_path, sizeof(addr.sun_path), "%s/%s", args[1], name);
  if (size < 0 || (size_t)size >= sizeof(addr.sun_path)) fail("proc_device_path", 70);
  int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0 || connect(fd, (struct sockaddr *)&addr, sizeof(addr))) fail("proc_device_connect", 70);
  memcpy(cs[*count].name, name, len + 1);
  cs[*count].fd = fd;
  (*count)++;
  return fd;
}
static void output_bytes(FILE *f, const uint64_t *v, size_t n) {
  for (size_t i = 0; i < n; i++) {
    if (v[i] > 255) fail("proc_abi_byte", 56);
    if (fputc((int)v[i], f) == EOF) fail("proc_host_output", 70);
  }
  if (fflush(f)) fail("proc_host_output", 70);
}
static void *run(void *unused) {
  (void)unused;
  wasm_rt_init();
  wasm_rt_trap_t trap = wasm_rt_impl_try();
  if (trap) {
    fprintf(stderr, "proc_wasm_trap:%s\n", wasm_rt_strerror(trap));
    result = 57;
    return NULL;
  }
  Words state = copy_words(NULL, 0), response = copy_words(NULL, 0);
  Connection cs[MAX_CONNECTIONS];
  size_t count = 0;
  int current = -1;
  for (size_t step = 0; step < 65536; step++) {
    Words reply = call(state, response);
    free(state.v);
    free(response.v);
    if (reply.n < 3 || reply.v[1] > reply.n - 3) fail("proc_abi_reply", 56);
    size_t out_n = (size_t)reply.v[1], state_at = 2 + out_n;
    if (reply.v[state_at] != reply.n - state_at - 1) fail("proc_abi_reply", 56);
    size_t state_n = (size_t)reply.v[state_at];
    uint64_t act = reply.v[0];
    const uint64_t *out = reply.v + 2;
    state = copy_words(reply.v + state_at + 1, state_n);
    response = copy_words(NULL, 0);
    if (act == 0 && state_n) {
      size_t start;
      current = connection(cs, &count, out, out_n, &start);
      send_bytes(current, out + start, out_n - start);
    } else if (act == 3 && state_n && out_n == 1 && out[0] && out[0] <= MAX_IO && current >= 0) {
      free(response.v);
      response = receive_bytes(current, (size_t)out[0]);
    } else if (act == 1 && !state_n && out_n && out[0] <= 255) {
      result = (int)out[0];
      output_bytes(stdout, out + 1, out_n - 1);
      free(reply.v);
      free(state.v);
      free(response.v);
      for (size_t i = 0; i < count; i++) close(cs[i].fd);
      if (trace && fclose(trace)) fail("proc_trace_write", 70);
      wasm_rt_free();
      return NULL;
    } else if (act == 2 && !state_n) {
      output_bytes(stderr, out, out_n);
      fail("proc_refused", 56);
    } else fail("proc_abi_reply", 56);
    free(reply.v);
  }
  fail("proc_step_limit", 50);
  return NULL;
}
int main(int argc, char **argv) {
  if (argc != 4 && argc != 5) fail("ProcWasm2CHost NAMESPACE FUEL IO_MS [RAW_TRACE]", 70);
  uint16_t endian = 1;
  if (*(uint8_t *)&endian != 1) fail("proc_host_endianness", 70);
  args = argv;
  fuel = number(args[2], INT64_MAX);
  io_ms = number(args[3], INT_MAX);
  if (argc == 5) {
    trace = fopen(args[4], "wb");
    if (!trace || fwrite("RSP1\n", 1, 5, trace) != 5) fail("proc_trace_open", 70);
  }
  signal(SIGPIPE, SIG_IGN);
  pthread_attr_t attr;
  pthread_t thread;
  if (pthread_attr_init(&attr) ||
      pthread_attr_setstacksize(&attr, (size_t)1024 * 1024 * 1024) ||
      pthread_create(&thread, &attr, run, NULL)) fail("proc_host_thread", 70);
  pthread_attr_destroy(&attr);
  if (pthread_join(thread, NULL)) fail("proc_host_join", 70);
  return result;
}
