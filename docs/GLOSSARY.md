# GLOSSARY

English | [中文](GLOSSARY.zh-CN.md)

- **q** — the content address of an object: the typed, versioned `q`
  format v1 of `docs/QFORMAT.md`, over SHA-256 digests.
- **qbe** — the back-end layer the `-qbe` benchmark variants compile
  through.
- **rsd** — Residua's language and toolchain.
- **rsx** — the canonical syntax tree of rsd terms (dependent type
  theory).
- **scm** — the erased functional core every program is lowered to.
- **lambda-RC** — the functional IR with reference counting and
  in-place reuse.
- **wasm0** — the integer-core subset of WebAssembly the compiler
  emits.
- **seed** — the committed wasm modules that rebuild the compiler.
- **fixed point** — the compiler built by itself equals itself byte for
  byte.
- **Seal** — a review signature by an independent model family on a
  release candidate.
- **Residue** — a named, recorded limitation or open item, never
  silent.
- **Stage word** — the identifier of the compiler stage revision that
  produced an image.
- **R-CIC** — Residua's kernel checker for Lean-compatible proofs (not
  shipped).
- **rscm** — the `.rscm` module the front end emits: scm encoded for
  the back end.
- **stencil** — a pinned program fragment the back end instantiates.
- **receipt** — a signed machine-readable record of a check run, bound
  to the bytes it checked.
- **twin** — the OCaml reference front end the differential checks run
  the shipped front end against.
- **ExecModel** — the execution-model instance an NF admission check is
  built on; see `docs/RELEASE-NOTES.md` for per-layer status.
- **MST-NF** — the normal-form composition theorem framework the NF
  results sit in; proofs are held by the upstream repository
  `https://github.com/residua-labs/MST-NF` (pinned commit `4432a34`).
