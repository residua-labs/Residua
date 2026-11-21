/* Recorded transport for the C2 RC cons ABI. The fixed block and RC prefix
 * follow bootstrap/ProcWasm2CHost.c. The emitted IntMag1 sequence flattens
 * each element into sign and magnitude, followed by the list tail. A
 * magnitude is a cons sequence of little-endian base-256 digits. */
#include "seed.h"
#include "wasm-rt-exceptions.h"
#include "wasm-rt-impl.h"
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if !defined(TRACE_STEP) || !defined(TRACE_STEP_ARENA)
#error Pin the step export and its scratch arena parameter
#endif
#if TRACE_STEP_ARENA != 0 && TRACE_STEP_ARENA != 1
#error TRACE_STEP_ARENA must be zero or one
#endif

enum { BLOCK = 24, RESULTS = 120, HEAP = 65536, NIL = 16, RC_BLOCK = 64,
       WORDS = 2048, STEPS = 64 };
static const uint64_t digit_header = UINT64_C(0x4000000000000002);
static const uint64_t digit_map = UINT64_C(0x0200000000000002);
static const uint64_t int_header = UINT64_C(0x4000000000000003);
static const uint64_t int_map = UINT64_C(0x0300000000000006);

typedef struct { uint64_t data[WORDS]; size_t size; } List;
typedef struct {
    FILE *out, *trace;
    unsigned char marker;
    int eof_second;
    size_t requests, used;
} Tape;

_Noreturn static void refuse(const char *name, int status) {
    fprintf(stderr, "[%s]\n", name);
    exit(status);
}

static unsigned char *slot(wasm_rt_memory_t *m, uint64_t ptr) {
    if ((ptr & 7) || ptr > m->size || m->size - ptr < 8) refuse("proc_abi_pointer", 56);
    return m->data + ptr;
}

static uint64_t get(wasm_rt_memory_t *m, uint64_t ptr) {
    uint64_t value;
    memcpy(&value, slot(m, ptr), 8);
    return value;
}

static void put(wasm_rt_memory_t *m, uint64_t ptr, uint64_t value) {
    memcpy(slot(m, ptr), &value, 8);
}

static uint64_t seed_node(wasm_rt_memory_t *m, uint64_t header, uint64_t map) {
    uint64_t bump = get(m, BLOCK), ptr = bump + 16;
    if (bump + RC_BLOCK > m->size) {
        if (wasm_rt_grow_memory(m, 1) == UINT64_MAX) refuse("capacity", 51);
        put(m, BLOCK + 8, m->size);
    }
    put(m, ptr - 16, 1);
    put(m, ptr - 8, 6);
    put(m, ptr, header);
    put(m, ptr + 8, map);
    put(m, BLOCK, bump + RC_BLOCK);
    return ptr;
}

static uint64_t seed(wasm_rt_memory_t *m, const List *list) {
    uint64_t tail = NIL;
    for (size_t i = list->size; i > 0; --i) {
        uint64_t word = list->data[i - 1], magnitude = NIL;
        unsigned char digits[8];
        size_t count = 0;
        for (; word; word >>= 8) digits[count++] = (unsigned char)word;
        while (count) {
            uint64_t digit = seed_node(m, digit_header, digit_map);
            put(m, digit + 16, digits[--count]);
            put(m, digit + 24, magnitude);
            magnitude = digit;
        }
        uint64_t ptr = seed_node(m, int_header, int_map);
        put(m, ptr + 16, 0);
        put(m, ptr + 24, magnitude);
        put(m, ptr + 32, tail);
        tail = ptr;
    }
    return tail;
}

static uint64_t read_magnitude(wasm_rt_memory_t *m, uint64_t ptr) {
    uint64_t value = 0;
    for (unsigned shift = 0; ptr != NIL; shift += 8) {
        if (shift == 64 || ptr < HEAP || get(m, ptr) != digit_header || get(m, ptr + 8) != digit_map)
            refuse("proc_abi_magnitude", 56);
        uint64_t digit = get(m, ptr + 16);
        ptr = get(m, ptr + 24);
        if (digit > 255 || (!digit && ptr == NIL)) refuse("proc_abi_digit", 56);
        value |= digit << shift;
    }
    return value;
}

static List read_list(wasm_rt_memory_t *m, uint64_t ptr) {
    List list = {0};
    while (ptr != NIL) {
        if (list.size == WORDS || ptr < HEAP ||
            get(m, ptr) != int_header || get(m, ptr + 8) != int_map) {
            fprintf(stderr, "proc_abi_list:%zu:ptr=%" PRIu64, list.size, ptr);
            if (ptr >= HEAP && !(ptr & 7) && ptr <= m->size && m->size - ptr >= 16)
                fprintf(stderr, ":header=%" PRIx64 ":map=%" PRIx64, get(m, ptr), get(m, ptr + 8));
            fputc('\n', stderr);
            refuse("proc_abi_list", 56);
        }
        if (get(m, ptr + 16)) refuse("proc_abi_negative", 56);
        list.data[list.size++] = read_magnitude(m, get(m, ptr + 24));
        ptr = get(m, ptr + 32);
    }
    return list;
}

static void check_call(wasm_rt_memory_t *m, uint64_t tag) {
    uint64_t status = get(m, BLOCK + 16);
    if (!tag && !status) return;
    if (status == 2) refuse("fuel", 50);
    if (status == 4 || (status == 3 && get(m, BLOCK + 24) == 1)) refuse("capacity", 51);
    if (status == 3) refuse("stuck", 55);
    fprintf(stderr, "proc_abi_status:%" PRIu64 ":%" PRIu64 ":%" PRIu64 "\n",
            tag, status, get(m, BLOCK + 24));
    refuse("proc_abi_status", 56);
}

static unsigned char as_byte(uint64_t word) {
    if (word > 255) refuse("proc_abi_byte", 56);
    return (unsigned char)word;
}

static void send(Tape *tape, const uint64_t *out, size_t size) {
    size_t sep = 0;
    while (sep < size && out[sep] >= 'a' && out[sep] <= 'z') ++sep;
    if (!sep || sep == size || out[sep] != 10) refuse("proc_device", 56);
    fputs("T\t", tape->trace);
    for (size_t i = 0; i < sep; ++i) fputc(as_byte(out[i]), tape->trace);
    fputc('\t', tape->trace);
    for (size_t i = sep + 1; i < size; ++i) fprintf(tape->trace, "%02x", as_byte(out[i]));
    fputc('\n', tape->trace);
    ++tape->requests;
    tape->used = 0;
}

static List receive(Tape *tape, uint64_t count) {
    unsigned char reply[] = {10,0,0,0,107,0,0,1,0,tape->requests == 1 ? tape->marker : 'B'};
    if (!count || count >= WORDS || !tape->requests || tape->requests > 2)
        refuse("trace_tape_read", 70);
    List response = { .size = 1 };
    size_t remaining = tape->requests == 2 && tape->eof_second ? 0 : sizeof reply - tape->used;
    size_t available = count < remaining ? (size_t)count : remaining;
    response.data[0] = available == count ? 0 : 1;
    fprintf(tape->trace, "R\t%" PRIu64 "\t", response.data[0]);
    for (size_t i = 0; i < available; ++i) {
        unsigned char byte = reply[tape->used++];
        response.data[response.size++] = byte;
        fprintf(tape->trace, "%02x", byte);
    }
    fputc('\n', tape->trace);
    return response;
}

static int run(Tape *tape, uint64_t fuel) {
    List state = {0}, response = {0};
    for (size_t step = 0; step < STEPS; ++step) {
        w2c_seed instance;
        wasm2c_seed_instantiate(&instance);
        wasm_rt_memory_t *m = w2c_seed_memory(&instance);
        put(m, BLOCK, HEAP);
        put(m, BLOCK + 8, m->size);
        uint64_t state_ptr = seed(m, &state), response_ptr = seed(m, &response);
        uint64_t live = get(m, BLOCK) - HEAP;
        put(m, 632, live);
        put(m, 640, live);
#if TRACE_STEP_ARENA
        check_call(m, TRACE_STEP(&instance, BLOCK, fuel, state_ptr, response_ptr, NIL));
#else
        check_call(m, TRACE_STEP(&instance, BLOCK, fuel, state_ptr, response_ptr));
#endif
        List reply = read_list(m, get(m, RESULTS));
        wasm2c_seed_free(&instance);

        if (reply.size < 4 || reply.data[0] != 1812203133 || reply.data[2] > reply.size - 4)
            refuse("proc_abi_reply", 56);
        size_t out_size = (size_t)reply.data[2], offset = 3 + out_size;
        state.size = reply.size - offset - 1;
        uint64_t act = reply.data[1];
        const uint64_t *out = reply.data + 3;
        if (reply.data[offset] != state.size || ((act == 0 || act == 3) != (state.size > 0)))
            refuse("proc_abi_reply", 56);
        memcpy(state.data, reply.data + offset + 1, state.size * sizeof(uint64_t));
        response.size = 0;
        if (act == 0) send(tape, out, out_size);
        else if (act == 3 && out_size == 1) response = receive(tape, out[0]);
        else if (act == 1 && out_size) {
            for (size_t i = 1; i < out_size; ++i) fputc(as_byte(out[i]), tape->out);
            return as_byte(out[0]);
        } else if (act == 2) {
            fputc('[', stderr);
            for (size_t i = 0; i < out_size; ++i) fputc(as_byte(out[i]), stderr);
            fputs("]\n", stderr);
            return 56;
        } else refuse("proc_abi_action", 56);
    }
    refuse("host_step_limit", 56);
}

int main(int argc, char **argv) {
    if (argc != 6 || strlen(argv[2]) != 1 || (strcmp(argv[3], "0") && strcmp(argv[3], "1")))
        refuse("trace_runner_usage", 70);
    char *end;
    uint64_t fuel = strtoull(argv[1], &end, 10);
    if (*end || !fuel || fuel > INT64_MAX) refuse("trace_runner_fuel", 70);
    Tape tape = { fopen(argv[4], "wb"), fopen(argv[5], "w"), (unsigned char)argv[2][0], argv[3][0] == '1', 0, 0 };
    if (!tape.out || !tape.trace) refuse("trace_runner_file", 70);
    wasm_rt_init();
    if (wasm_rt_impl_try()) refuse("host_trap", 57);
    int result = run(&tape, fuel);
    wasm_rt_free();
    if (fclose(tape.out) || fclose(tape.trace)) refuse("trace_runner_file", 70);
    return result;
}
