# Residua

English | [中文](README.zh-CN.md)

Residua is infrastructure for using another party's computation or proof
without trusting that party: results are identified by content (q) and
admitted only by mechanical checking, over a network of formally defined
semantics. Residua is designed so that computation and proof are one: in
rsd a program and a proof are meant to be terms of the same dependent
type theory — one object that is both compiled to fast native or wasm
code and checked by the kernel, not two systems kept in sync. That unity
is the design and is not yet demonstrated end to end; release 0.1 ships
the compilation half of it — the proof-checking half (the R-CIC kernel)
comes later, see the limits below.

Why it exists — three facts:

- Re-checking, repair after upstream changes, coordination and review
  dominate the cost of formal results; the kernel check is a small share.
- Most producers will be machines that cannot be trusted; only mechanical
  checking and content identity scale.
- Semantics are siloed (Lean, Rocq, K, wasm, EVM); results do not compose
  across them.

## What release 0.1 offers

Verifiable-provenance compilation. Given a source and an artifact, anyone
can rebuild from a committed wasm seed — with a C compiler and no other
toolchain — and check byte for byte that the artifact comes from the
source, trusting neither the publisher nor a large binary toolchain.

Supporting it:

- the rsd compiler chain `rsd -> rscm -> wasm` (`rsdc`, `rsc`), whose own
  sources ship in this archive
- frozen formal semantics per layer (scm, lambda-RC, wasm0) pinned by
  content digest, shipped as specification texts under `semantics/`,
  `gates/semalign/` and `lean/rsd-cert/`
- a per-version performance record (`release/docs/PERF-RECORD.tsv`;
  the fixed PERF-RECORD-0 form is described in
  `release/docs/PERF-RECORD`)
- two-family seals and a third-party reproduction of the seed recipe
  (evidence repository-side)

Start here:

- `release/docs/INSTALL` — the minimum steps
- `release/docs/QUICKSTART` — the first run, narrated
- `release/docs/VERIFY-RELEASE` — the full verification protocol
- `release/docs/OVERVIEW` — what is and is not in 0.1
- `release/docs/ARCHITECTURE` — the semantic chain, surfaces, identity
  and trust
- `release/docs/TRUST`, `GLOSSARY`, `STABILITY`, `FAQ`,
  `RELATED-WORK`, `CONTRIBUTING-SECURITY` — what 0.1 trusts, the terms
  it uses, what it promises, and how it relates to other work (each in
  `release/docs/`, English with a Chinese mirror)
- `release/MANIFEST.md` — the release requirements this archive was built to

## Stated limits of 0.1

- single-module programs (no `import`)
- no I/O execution layer
- no proof checking (the R-CIC checker is not in this release; shipped
  `theorem` texts are pinned specification, not checked claims)
- no UInt64; a 4 GiB address space
- the q content-identity format is not final
- no publish/query entry for results
- the 0.1 `.rsd` surface is a strict bootstrap subset — `theorem`,
  `axiom`, `class`, `abbrev`, `by` are refused (`release/docs/LANGUAGE`)

0.1 is for reproducible, auditable compilation — supply chain, the step
before trusted execution — and for research on verified, bootstrappable
compilers. It is not presented as a general-purpose language.

## Order after 0.1

Each item names its acceptance object; no dates.

1. Using another's result without trusting them, first instance: the
   R-CIC kernel (Lean Kernel Arena: no invalid input accepted, then
   init/std, then mathlib within 16 GiB) plus the q format and Jig's
   publish/query entry — the first point where a stranger can find, check
   and reuse another's result; it ranks above programming features.
2. Programming completeness: modules, real programs, UInt64, an
   execution layer (I/O as typed effects), 64-bit addressing, and the
   application suites (Cedar, Anvil, Tendril, SQLite) as acceptance.
3. Cheap confirmation of execution: wasm0 -> AIR -> zk.
4. The network: generic connectors to external semantics (K/KORE,
   Lean/Rocq import), ranked by how many semantics one bridge opens.

## Naming

Residua is the project. `rsd` is the language and the toolchain.
`raisin` stays internal.

closure_claim = 0
