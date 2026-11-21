# OVERVIEW — what Residua is, what release 0.2 offers, its limits

English | [中文](OVERVIEW.zh-CN.md)

This document is part of the release archive. Claims marked
*repository-side* cite files that do not ship in this archive; they are
recorded here for auditors who also hold the source repository.
Citations without a commit are at the head this document ships with.

## One line

Residua is infrastructure for using another party's computation or proof
without trusting that party: results are identified by content (q) and
admitted only by mechanical checking, over a network of formally defined
semantics. Residua is designed so that computation and proof are one:
in rsd a program and a proof are meant to be terms of the same
dependent type theory — one object that is both compiled to fast native
or wasm code and checked by the kernel, not two systems kept in sync.
That unity is the design and is not yet demonstrated end to end;
release 0.2 ships the compilation half of it — the proof-checking half
(the R-CIC kernel) is named under the limits and the order below.

Why — three facts, no mission claims: re-checking, repair after upstream
changes, coordination and review dominate the cost of formal results
(the kernel check is a small share); most producers will be machines
that cannot be trusted, so only mechanical checking and content identity
scale; semantics are siloed (Lean, Rocq, K, wasm, EVM) and results do
not compose across them.

## What 0.2 offers — and only this

Verifiable-provenance compilation: given a source and an artifact,
anyone can rebuild from a committed wasm seed, with a C compiler and no
other toolchain, and check byte for byte that the artifact comes from
the source — trusting neither the publisher nor a large binary
toolchain.

Supporting it:

- The rsd compiler chain `rsd -> rscm -> wasm` (`rsdc`, `rsc`), self-hosted:
  both compilers ship as wasm seeds in
  `bootstrap/seed/stage-14274/` (sha256 `dcd40993dcda…` and `ce2cff5b42fd…`,
  `bootstrap/seed/stage-14274/SHA256SUMS`) together with their 53-member
  source closure (`SOURCE-MEMBERS-SHA256SUMS`) and the member-to-bundle
  link (`ASSEMBLY.tsv`: which member sits in which `RscSourceModule_`
  section of the two whole-module sources, in order).
- The bootstrap recipe `bootstrap/seed/stage-14274/README.md`: a clean
  Linux x86-64 environment with GCC/binutils/coreutils/Bash/curl/tar and
  no Lean, elan, lake, Node or OCaml rebuilds both compilers; the recipe's
  rebuilt images compare byte-identical to the committed seeds
  (`seed_roundtrip=2/2`). A third-party run of this
  recipe on the release archive reached the fixpoint (evidence
  repository-side).
- Frozen formal semantics per layer (scm, lambda-RC, wasm0), pinned by
  content digest: `lean/rsd-cert/Residua/Bootstrap/Semantics.lean`
  `evalLF` at `1fef580a3`, q
  `4ffcb7d990e8c77fa5dce42bcb4e1ae798e3cddd04803ac7c1fcbd2cb7fa46d2`
  (the frozen waist scm row). The whole `Residua.Bootstrap` spec set ships (9
  files) plus its `Residua.SHA256` import, so the pinned spec's `import`
  lines resolve inside the archive; `theorem` declarations in these
  texts are pinned spec content, not proof checking.
- A per-version performance record (`docs/PERF-RECORD.md` +
  `PERF-RECORD.tsv`, shipped in this archive; `perf/` also carries the
  Cedar engine's table).
- Two-family seals of the release tag and a third-party reproduction of
  the recipe (repository-side evidence).

New in 0.2:

- The final typed content identity `q` (format v1): the kind of the
  addressed content is inside the hashed bytes; raw SHA-256 remains as
  `digest` for file integrity only (`docs/QFORMAT.md`; vectors
  `release/checks/qformat/`).
- The syntax engine, closed over its grammar class: engine sources
  `rsdc/syntax/`, the class with its reference decider and soundness
  proof `semantics/Syntax/`, the surface profiles `rsdc/profiles/*.syn`
  shipped as data, and the acceptance suite over generated grammars.
- The execution-boundary formal semantics E0–E4 (`semantics/Effect/`):
  the wire format, admission and seal judgments, the conformance
  classifier and recorded transport sessions; acceptance evidence
  `reports/effect-sem/` (repository-side).
- The Cedar authorization engine ported to rsd (`policy/cedar/`,
  Apache-2.0 `policy/NOTICE-CEDAR`), with its harness, oracle build and
  request corpus (`bench/cedar-perf/`), a decision-equality gate against
  the published Rust implementation, and its performance record on the
  release machine type (`perf/`; evidence `reports/cedar-perf/`).

## The chain in this archive

- `rsdc` compiles `.rsd` source to `.rscm` (the scm layer's binary form;
  magic `52 53 43 4d` + version byte, written in `rsdc/Compile.rsd` and
  read in `rsc/rsc.rsd`).
- `rsc` lowers `.rscm` to `.wasm` at the stage's pinned word (14274).
- The C host bridge of the `execution-bridge` component (named in
  `bootstrap/seed/stage-14274/EXECUTOR-SHA256SUMS`) plus the wasm2c
  runtime pinned in `bootstrap/seed/stage-14274/WABT-SHA256SUMS`
  execute the seeds; `bootstrap/Wasm2CHost.c` and
  `bootstrap/ProcWasm2CHost.c` are the generic host variants.
- Invocation is the stage host's file contract:
  `"$out/rsdc/run" rsdc <in.rsd> <out.rscm> 0 cons` and
  `"$out/rsc/run" rsc <in.rscm> <out.wasm> 14274 cons`
  (`docs/RSD-COMMAND.md`).

## File formats

| format | what it is | source | shipped in 0.2 |
|---|---|---|---|
| `.rsd` | text spelling of the pre-elaboration tree; the 0.2 front edge accepts the bootstrap subset | `docs/LANGUAGE.md` | yes — the source members plus the `semantics/`/`gates/semalign/` specification texts |
| `.rsj` | text spelling of the same tree, Reason-style | grammar profile `rsdc/profiles/rsj.syn` | yes — the profile ships as engine data; the compiler's accepted input remains `.rsd` |
| `.rsm` | text spelling of the same tree, Racket-family (renamed from `.rsl`) | grammar profile `rsdc/profiles/rsm.syn` | yes — the profile ships as engine data |
| `.rsx` | canonical kernel form: csexp of the canonical s-expression over the source-level AST | repository-side grammar | no — repository-only |
| `.scm` | text programs in the scm language; also the named Scheme view over the canonical tree | repository-side grammar | no — repository-only |
| `.rscm` | binary scm-layer interface | `docs/EMITTER.md` | yes — `bootstrap/seed/rsc.rscm`, and the recipe emits `.rscm` on rebuild |
| `.wasm` | committed compiler seeds | `bootstrap/seed/stage-14274/{rsdc,rsc}.wasm`, `bootstrap/seed/{rsdc,rsc}.wasm` | yes — 4 files |
| `.lean` | Lean 4.14 specification texts of the frozen semantics | `lean/rsd-cert/Residua/Bootstrap/`, `lean/rsd-cert/Residua/SHA256.lean` | yes — the specification set only; all other `.lean` is repository-only |

The semantics `.rsd` files under `semantics/` and `gates/semalign/` are
Lean 4.14 program texts shipped as specifications (`docs/SPECS.md`
marks the row GATED; `gates/semalign/METHOD.md` names the protocol).
They are not accepted by the 0.2 `rsdc` front edge — the 0.2 `.rsd`
grammar is the bootstrap subset of `docs/LANGUAGE.md`, which
refuses `theorem`, `axiom`, `class`, `abbrev`, `variable`, `opaque`,
`by` and `import`. The syntax engine itself accepts any grammar of the
class as data (`semantics/Syntax/Class.rsd`).

## Stated limits of 0.2

- Single-module programs: `import` is refused by the front edge.
- No I/O execution layer: program input/output is the stage host's
  file contract, not a language effect.
- No proof checking: the R-CIC checker, `rsd_proofs` and certificates
  are not in this release; shipped `theorem` texts are pinned
  specification, not checked claims.
- No UInt64; a 4 GiB address space.
- No publish/query entry for results; no dispatcher command.
- No importable standard library (`docs/STDLIB.md`).

Who 0.2 is for: reproducible, auditable compilation — supply chain, the
step before trusted execution — and research on verified, bootstrappable
compilers. It is not presented as a general-purpose language.

## Order after 0.2

Each item names its acceptance object; no dates.

1. Using another's result without trusting them, first instance: the
   R-CIC kernel (Lean Kernel Arena: no invalid input accepted, then
   init/std, then mathlib within 16 GiB) plus a publish/query entry
   for results — the first point where a stranger can find,
   check and reuse another's result; it ranks above programming
   features. R-CIC kernel rules target current Lean including the
   4.32–4.34 soundness fixes; input is 4.35 exports.
2. Programming completeness: modules, real programs, UInt64, an
   execution layer (I/O as typed effects), 64-bit addressing, and the
   application suites (Cedar, SQLite) as acceptance.
   Basic data representation follows current Lean from 0.2
   (Int8..Int64/ISize, Float32, String as UTF-8 ByteArray,
   Std.TreeMap), one card per type.
3. Cheap confirmation of execution: wasm0 -> AIR -> zk.
4. The network: generic connectors to external semantics (K/KORE,
   Lean/Rocq import), ranked by how many semantics one bridge opens.

## Naming and surface spellings

Residua is the project; `rsd` is the language and toolchain.

Repository-side, Residua sources exist in three surface spellings of a
single pre-elaboration tree — the `surface rsd` grammar (a Lean 4.14.0
syntax subset ported from stock Lean 4.14.0 commit
`410fab7284703f41660ca2454218dcca9b2ec896`), a Reason-style spelling and
a Racket-family spelling — alongside the canonical kernel form `.rsx`.
In 0.2 only the `.rsd` spelling ships and only the bootstrap subset of
it is accepted (`docs/LANGUAGE.md`: the chain's own sources parse
err=0, 6/6 files plus the 1,208,186-byte concatenated bundle; every
refuse-corpus row refuses, 54/54 — repository-side evidence).

For the layer-by-layer design — the semantic chain, the surface
syntaxes, identity and trust — see `docs/ARCHITECTURE.md`. The
outside-reader set `docs/{TRUST.md,GLOSSARY.md,STABILITY.md,FAQ.md,
RELATED-WORK.md,CONTRIBUTING-SECURITY.md}` covers what 0.2 trusts, its terms,
its promises and its relations; each ships in English and Chinese.

`closure_claim=0` (`release/MANIFEST.md`: "No release tag, seal or
author attestation is made here").
