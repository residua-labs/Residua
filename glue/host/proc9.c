/* provenance: ours (searched: host/exec9.cjs, docs/OBJECT-ABI.md)
 * glue/host/proc9.c — native Proc execution host for `rsd run`, wasm2c
 * backend.
 *
 * Compiled once per program: the glue emits a tiny drv.c that includes the
 * wasm2c-generated <gen>.h, defines the MOD_* macros below, then includes
 * this file. The chain route is rsdc -> rsc -> wasm2c -> cc (the route
 * sql/run/BuildAccept.rsd documents); this file is the execution-layer host
 * the binary links, a C port of host/exec9.cjs's procMain against object
 * ABI revision 2 (docs/OBJECT-ABI.md).
 *
 * Protocol (identical to exec9.cjs procMain):
 *   FB=24 header: [bump | limit | status | detail | res | .. | image @+96]
 *   flat region starts at FHEAP=65536; host inputs are rc-0 borrowed cells.
 *   p image = 7 words: Proc{tag-sgn tag-mag res req rep contsF contsB} (tag is Int).
 *   STEP(block, fuel, p0..p6, stP, rP) -> reply list at FB+96:
 *     [act] ++ lp(out) ++ lp(st), lp(x) = len ++ bytes as boxed-Int list.
 *   act: 1 done (out[0]=exit code, rest = stdout), 2 refuse,
 *        0 send (out = "<dev>\n" ++ T-frame bytes), 3 read-more (out=[count]).
 *
 * Marshalling, device connections and the exact-n read live in
 * proc9core.h; this file supplies the wasm2c memory hooks and the
 * drive9 step loop. */

#include "wasm-rt-impl.h"
#include "wasm-rt-exceptions.h"

/* The generated drv.c supplies: INST_TYPE, MOD_INSTANTIATE, MOD_FREE,
   MOD_MEM, MOD_ENTRY(block,fuel), MOD_STEP(block,fuel,p0..p5,stP,rP). */
static INST_TYPE mod_inst;
static wasm_rt_memory_t *mod_mem;

static void host_mem_refresh(void) {
  mod_data = mod_mem->data;
  mod_size = mod_mem->size;
}

static void host_mem_grow(uint32_t pages) {
  wasm_rt_grow_memory(mod_mem, pages);
  host_mem_refresh();
}

#include "proc9core.h"

static void call_status(const char *what) {
  uint64_t dt;
  uint64_t st = status_of(&dt);
  if (st == 0) return;
  exit(status_refuse(st, dt));
  (void)what;
}

int main(int argc, char **argv) {
  const char *devsrv = getenv("RSD_DEVSRV");
  if (!devsrv) devsrv = MOD_DEVSRV;
  /* NUL-separated argv bytes for the env device (exec9 procArgBytes). */
  uint8_t argbuf[8192]; int alen = 0;
  for (int i = 1; i < argc && alen < 8188; i++) {
    int l = strlen(argv[i]);
    memcpy(argbuf + alen, argv[i], l); alen += l;
    argbuf[alen++] = 0;
  }

  wasm_rt_init();
  wasm_rt_trap_t trap = wasm_rt_impl_try();
  if (trap) {
    fprintf(stderr, "trap:%s\n", wasm_rt_strerror(trap));
    return 55;
  }
  MOD_INSTANTIATE(&mod_inst);
  mod_mem = MOD_MEM(&mod_inst);

  flat_reset();
  MOD_ENTRY(&mod_inst, MOD_FB, MOD_FUEL);
  call_status("entry");
  uint64_t pimg[7];
  for (int i = 0; i < 7; i++) pimg[i] = mrd(MOD_FB + 96 + i * 8);

  int64_t *st = NULL, *resp = NULL;
  int stn = 0, respn = 0, curfd = -1;

  for (int n = 1; n <= MAX_STEPS; n++) {
    uint64_t stP = list_i(st, stn), rP = list_i(resp, respn);
    MOD_STEP(&mod_inst, MOD_FB, MOD_FUEL,
             pimg[0], pimg[1], pimg[2], pimg[3], pimg[4], pimg[5], pimg[6], stP, rP);
    call_status("step");
    int nw = 0;
    int64_t *w = list_words(mrd(MOD_FB + 96), &nw);
    if (nw < 3) exit(refuse("proc_abi_reply", 56, ""));
    int64_t act = w[0], outLen = w[1];
    if (outLen < 0 || outLen > nw - 3) exit(refuse("proc_abi_reply", 56, ""));
    int64_t *out = w + 2;
    int stl = 2 + (int)outLen;
    free(st);
    stn = nw - stl - 1;
    st = malloc(sizeof(int64_t) * (stn > 0 ? stn : 1));
    memcpy(st, w + stl + 1, sizeof(int64_t) * stn);
    if (w[stl] != stn) exit(refuse("proc_abi_reply", 56, ""));
    free(w);
    respn = 0; free(resp); resp = NULL;

    if (act == 1) {
      if (outLen < 1) exit(refuse("proc_exit_missing", 56, ""));
      for (int64_t i = 1; i < outLen; i++) putchar((int)out[i]);
      fflush(stdout);
      MOD_FREE(&mod_inst);
      return (int)(out[0] & 255);
    }
    if (act == 2) {
      fprintf(stderr, "refused: ");
      for (int64_t i = 0; i < outLen; i++) fputc((int)out[i], stderr);
      fputc('\n', stderr);
      return 56;
    }
    if (act == 0) {
      int sep = -1;
      for (int64_t i = 0; i < outLen; i++) if (out[i] == 10) { sep = (int)i; break; }
      if (sep < 0) exit(refuse("proc_device", 56, ""));
      char dev[16];
      if (sep >= 15) exit(refuse("proc_device", 56, ""));
      for (int i = 0; i < sep; i++) dev[i] = (char)out[i];
      dev[sep] = 0;
      if (strcmp(dev, "env") && strcmp(dev, "fs") && strcmp(dev, "store") &&
          strcmp(dev, "clock") && strcmp(dev, "cmd"))
        exit(refuse("proc_device", 56, ""));
      curfd = dev_conn(dev, devsrv, argbuf, alen);
      size_t flen = (size_t)(outLen - sep - 1);
      uint8_t *fbuf = malloc(flen ? flen : 1);
      for (size_t i = 0; i < flen; i++) fbuf[i] = (uint8_t)out[sep + 1 + (int64_t)i];
      int wrc = dev_write_frame(curfd, fbuf, flen, argbuf, alen);
      free(fbuf);
      if (wrc != 0) exit(refuse("proc_socket_dead", 70, dev));
      continue;
    }
    if (act == 3) {
      if (outLen != 1 || out[0] <= 0 || out[0] > READ_MAX || curfd == -1)
        exit(refuse("proc_read_limit", 56, ""));
      int cnt = (int)out[0];
      uint8_t *buf = malloc(cnt);
      int evt = read_n(curfd, buf, cnt);
      resp = malloc(sizeof(int64_t) * (cnt + 1));
      resp[0] = evt; respn = (evt == 0 ? cnt : 0) + 1;
      for (int i = 0; i < respn - 1; i++) resp[i + 1] = buf[i];
      free(buf);
      continue;
    }
    exit(refuse("proc_abi_act", 56, ""));
  }
  return refuse("host_step_limit", 56, "");
}
