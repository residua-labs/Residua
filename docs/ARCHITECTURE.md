# ARCHITECTURE — how Residua is put together

English | [中文](ARCHITECTURE.zh-CN.md)

This document describes the design and says plainly which parts release
0.2 ships. Status cells are checked against the shipped head.

## The idea

Every layer of Residua has a formal semantics that is both a
kernel-checked definition and an executable reference interpreter, a
canonical form identified by its content address q, one canonical entry,
and a hop to the next layer that carries evidence (a proof, or
translation validation where a proof is out of proportion). Results are
stored as q-identified nodes and judgments as edges: a graph, not a set
of files and versions.

## Surface syntax

Residua stores meaning, not text. Each surface (today: rsd) is a
notation mapped one to one onto rsx syntax trees; text is parsed into a
tree and printed back from it, and two texts with the same tree have the
same q. rsd's surface in 0.2 is a subset of Lean 4.14's syntax, read the
way Lean's own parser reads it; it is a bootstrap surface, not the
language's final design. The reader has a fast Pratt tier ported from
Lean's parser and a general Earley tier used as its oracle.

## The semantic chain (top to bottom)

| Layer | Semantics | Hop below | Status at 0.2 |
|---|---|---|---|
| rsx: the dependent type theory (CIC.md) | typing and conversion, value semantics | erasure, defunctionalisation, fuel, to scm | semantics frozen (revision 1); not yet the compiler's only input |
| scm: the erased functional core | evalLF | to lambda-RC | semantics frozen; 205 of 205 decidable alignment rows (224 corpus rows; 19 host-class gaps excluded by the protocol) |
| lambda-RC: functional IR with reference counting and reuse (ported from Lean's IR) | lambda-pure and lambda-RC | to wasm0 (simulation) | semantics frozen; RC erasure proved; hops checked by differential gates with planted mutants |
| wasm0: the integer core of WebAssembly | the MVP integer-core profile | to machine code by stencils | semantics frozen (revision 2) |
| Machine code (AArch64 first) | the machine's formal ISA semantics | — | partial (stencils proved one by one); 0.2 executes the seed wasm through wasm2c and a C compiler, which are part of 0.2's trusted base |
| AIR and zk (proof branch below wasm0) | execution traces as constraints; STARK soundness | — | designed, not started |
| Effects | programs return effect values (requests/responses); meaning = I/O traces | trace refinement | boundary semantics shipped (`semantics/Effect/` E0–E4); no effect constructs in the language |

Proofs live at the rsx layer: they are checked there by the kernel and
erased below it, so the code that runs is the erasure of the checked
term. The test of this end to end is not yet passed (see the README:
0.2 ships the compilation half; proof checking comes later).

## Identity and trust

- Content address q: the typed, versioned q format v1
  (`docs/QFORMAT.md`) shipped at 0.2; raw SHA-256 over the bytes
  remains as `digest` for file integrity and interop.
- The compiler is trusted by self-reproduction from a committed seed
  (fixpoint, byte for byte) and by third-party reproduction; later also
  by diverse double compiling. In 0.2 the trusted base additionally
  includes wasm2c, the C compiler and the host tools the seed recipe
  calls (see `docs/TRUST.md`).
- Proofs are trusted by a kernel whose rules are fixed by Lean's kernel,
  checked against independent kernels (lean4lean, nanoda); R-CIC,
  Residua's own checker compiled by this chain, is in progress and not
  in 0.2.

## How work enters and is built (tools, not in 0.2)

The agent entry (claim, publish by q, check, read
at a cut). Rsd: builds and caches by q, incrementally. The performance harness: Lean
builds by declaration, admission by kernel replay only, reuse across
versions by q.

## Where the pieces live in this archive

- `bootstrap/seed/stage-14274/` — the committed seeds, their source
  closure and the rebuild recipe
- `semantics/` — the shipped frozen semantics texts
  (`Lrc/Sem.rsd`, `Wasm0/Sem.rsd`) and hop statements
  (`Rsx/Lower.rsd`, `Wasm0/Hop.rsd`)
- `lean/rsd-cert/Residua/` — the scm layer's evalLF specification text
- `gates/semalign/` — the rscm-vs-evalLF differential gate, its corpus
  and its METHOD
- `docs/SPECS.md` — the per-specification table with sha256 pins

closure_claim = 0
