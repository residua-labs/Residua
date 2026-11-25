# Release manifest: closure roles and pending files

This file is the release inventory, one section per version (0.1,
0.2, 0.3, 0.4 below). The 0.1 section is the inventory for release 0.1,
the minimal self-bootstrap closure, not a publishable file list. The
requirements are
the public-release-0 requirement revisions 4e and 4f and the
`MinimalBootstrap` closure plan. The 0.1 candidate contains the committed wasm seed
(`bootstrap/seed/stage-14274/`), the source closure of `rsdc` and `rsc`
(the 53 members of `bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS`),
the runtime (`lib/rt` and the `lib/Runtime*` members, plus the C host
bridges the seed recipe and execution host use), and the stranger
documents (`docs/`, `bootstrap/README.md`, `LICENSE`, `NOTICE`,
`lean-toolchain`, `README.md`, `README.zh-CN.md`, `CHANGELOG.md`,
`CHANGELOG.zh-CN.md`, `ACKNOWLEDGEMENTS.md`, `ACKNOWLEDGEMENTS.zh-CN.md`,
`CONTRIBUTING.md`, `CONTRIBUTING.zh-CN.md`, `CODE_OF_CONDUCT.md`,
`SECURITY.md`, `TESTING.md`, `TESTING.zh-CN.md`, `.github/`, `perf/`,
`reports/nf-compose/`,
`release/notes/`, `release/licenses/`, `release/checks/`,
`release/TERMS.tsv`, `release/NOTICES.md`, `release/PROVENANCE.tsv`).

The closure is met: seed -> rsdc, rsc -> fixpoint byte-equal in a clean
environment without Lean, elan, lake, Node or OCaml
(clean-environment reproduction recorded repository-side,
installed at `0d7bf0239`, seed recipe in `bootstrap/seed/stage-14274/README.md`),
plus the scm semantics gate (`gates/semalign/`).

Not in 0.1 (deferred to the 0.1.x line, named): modules, real programs,
the no-Lean chain beyond the bootstrap cone, the
q-format batch, the application suites (SQLite/Cedar apply from
a later 0.1.x), the R-CIC checker and `rsd_proofs`, the new surface syntax and
the rsx entry, the frozen waist semantics as a claim, the internal
dispatcher command and its examples, the rsd closure, and the OCaml
instrumented route. Those files remain in the repository as
repository-only rows; their documents may ship as specifications marked
"draft" in a later version. Phase-2 web, Cedar and performance tooling
are outside this candidate.

`ARTIFACTS.tsv` is the artifact denominator. Each role stays in that
table until its path, digest, complete build inputs and two-host
observation exist. A `pending` path is an unresolved artifact, never an
omitted artifact or an equal pair. The 0.1 seed pair
(`stage-14274/rsdc.wasm`, `stage-14274/rsc.wasm`) is bound by the seed
recipe's own clean-environment reproduction
(clean-environment reproduction recorded repository-side;
`bootstrap/seed/stage-14274/{SHA256SUMS,REBUILT-SHA256SUMS,
SOURCE-MEMBERS-SHA256SUMS,SEED-HOST-SHA256SUMS,WASMTIME-SHA256SUMS,
BINARYEN-SHA256SUMS}` at 0.3; the 0.1 recipe pinned a WABT route that 0.3
replaces), plus the member verification of each cut from git objects. The combined declared/prerequisite/
build closure is tracked in `BUILD-INPUTS.tsv`. The offline replay
checks the named receipt facts and then compares the inputs against the
current tree. The older pinned seed pair (`bootstrap/seed/{rsdc,rsc}.wasm`,
`rsc.rscm`, `manifest.json`, `bootstrap/sources.json`) shipped until 0.2
as seed material of an alternate bootstrap route; from 0.3 it stays in the
development repository.

`SHIP-RULES.tsv` declares the ordered component rules (first match
wins); `SOURCE-ROLES.tsv` is the complete component-to-file map
regenerated at each head by `reports/release-readiness-r1/SourceRoles.rsd`.
The 0.1 ship set is the rows with `distribution = ship-set-source`:
seed, compiler-closure, runtime, execution-bridge, documentation,
legal and build-tooling. Every other file carries a repository-only row
with its reason. `SourceArchive.rsd` writes a normalized-metadata ustar
over the ship set, whose digest is a pure function of the shipped path
set, modes and bytes.

The source archive has the complete path/digest inventory above. The
`ext:.lean` rule classifies `.lean` files repository-only, but the
earlier `prefix:lean/rsd-cert/Residua/Bootstrap/` rule wins for the
nine frozen spec texts under that directory, which ship as
`ship-set-source` (`specification`); every other `.lean` file is
excluded. Proof sources and oracle programs remain in the
repository outside that inventory. Negative fixtures and scanner
definitions remain in the repository and in raw scan evidence. A
manifest exclusion requires a component reason; it cannot be used to
erase an NF or path-scan finding.

The name-form check still examines every tracked `.rsd`/`.lean` outside the root
`reports/` directory, regardless of the eventual archive selection; the
0.1 counter is the ship-set files that *declare* an NF instance (an NF
shell or Model/Profile instance) and fail NFCheck — files declaring no
instance are outside that check. At this head the count is 3, each row named
with its NFCheck classes repository-side (ships as-is; a fix
is a new seed cut). For the
path-scan checks the
current global census is diagnostic until each manifest path is
classified; the 43 seat-name rows inside q-pinned spec, seed and
generated manifest files are likewise named repository-side.
No zero-finding or
complete-provenance claim follows from this draft inventory.

Evidence and recipes are retained under `reports/release-readiness-r1/`
and the `reports/release-02/evidence/` tree. They are not
executable dependencies. The two historical `release/scan/leakage`
tables are repository-only raw diagnostic evidence, outside the source
archive and executable/artifact inputs. Their candidates remain in the
raw census and are classified as retained nonshipping diagnostics, not
as false positives. Other paths require their own reviewed component
reasons.
No release tag, seal or author attestation is made here. The candidate
tag is `rsd-0.1-rc<N>`; the release tag is `rsd-0.1` (the pre-existing
`v0.1.0`, `d15d81ad3`, is left untouched).

Provenance directory selectors that contain `.lean` sources are
expanded into tracked leaf paths. Every leaf is retained; `.lean` proof
or adapter sources outside the `lean/rsd-cert/Residua/{Bootstrap/,SHA256.lean}`
specification set use repository-only (or oracle-only for declared
oracles), outside the archive. Stock-Lean runtime harnesses and the
Earley reference remain oracle-only. This is a source-role boundary,
not removal of third-party attribution.

The third-party check covers the seed and the scm formats only for
0.1; the proof-certificate check does not apply: 0.1 ships no proof
checking (no checker, no
certificates). The shipped specification texts under `lean/rsd-cert/` are
Lean 4.14 sources pinned as text — their `theorem` declarations are part
of the pinned spec, not claims checked inside 0.1.

## 0.2

0.2 is a feature release on the same 0.1.2 source closure: the 53
committed-seed members are unchanged at the `be7c7608c9` member-map bytes,
and the seed round-trip is unchanged. In the release archive, in closing order:

- the typed content address (q format v1), landed at 6d700789eb, with
  its specification (`docs/QFORMAT.md`), conformance check
  (`release/checks/qformat/`), release note
  (`release/notes/qformat-1.md`) and audit evidence
  (`reports/release-02/evidence/`);
- the syntax engine closed over its grammar class
  (`semantics/Syntax/Class.rsd`), with its release note
  (`release/notes/syntax-engine.md`) and audit evidence
  (`reports/release-02/evidence/`);
- the execution-boundary semantics E0–E4, with its release note
  (`release/notes/effect-sem.md`) and audit evidence
  (`reports/release-02/evidence/`).

Held out of 0.2: Cedar (its close audit refused; a later release after
re-audit), the `rsd` build tool and the internal-name directory rename
(the tool
sources need post-cut `UInt64`/`USize` members; both move to 0.3 with
the recut seed), and internal dogfood targets. The macOS arm64 host is
bound by the same seed recipe, run under `env -i` with base-system
tools only (`bootstrap/seed/stage-14274/README.md`).

## 0.3

0.3 is a feature release on a recut seed (`fc0fb23a3a`): the committed
seed is rebuilt at this release's sources and carries `UInt64`/`USize`
and the current 54-member source closure
(`bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS` — 54 members,
`SHA256SUMS` digests `1aeacfb6b097…`/`b7db967608fe…`). In the release
archive, in closing order:

- the `rsd` build tool's sources (`rsd/`, `lib/rsd/`, `lib/Rsd.rsd`,
  `lib/laws/RsdScheduleLaws.rsd`), its documentation (`docs/BUILD.md`),
  check suite (`release/checks/rsd-tool/`) and release note
  (`release/notes/rsd-tool.md`) — sources ship; part of the tool's
  build closure is repository-side (`release/GAPS.tsv`);
- the three-surface work (`docs/surfaces/`, `examples/surfaces/`,
  `semantics/Rsx/Lower.rsd`'s revised adequacy statements, the added
  `rsv.syn` grammar productions) and the root testing guide
  (`TESTING.md`, `TESTING.zh-CN.md`);
- the restored 0.1.2 suites dropped by 0.2 (`benchmarks/`,
  `instruments/lrc-host/`, `perf/`) plus the Koka tables
  (`benchmarks/koka/{entries,images,modules}.tsv`);
- the MST-NF composition package (`lean/nf-compose/`, pinned model
  included, proofs held by `github.com/residua-labs/MST-NF` @ `4432a34`)
  with its audit report (`reports/nf-compose/REPORT.md`), and the
  admission `ExecModel` instances (`semantics/Effect/AdmissionNF.lean`
  ships for audit; its imports are repository-side).

Held out of 0.3: Cedar (its close audit refused), the internal
dogfood targets, the URL parser (a separate repository's work), compiled
dispatcher binaries, modules, proof checking and the application
suites. macOS arm64 remains a named gap: the generated seed recipe is
Linux x86-64 only (`release/GAPS.tsv`).

## 0.4

0.4 is a feature release on a recut seed (`476f974ed5`, from the frozen
compiler head `2ba35d752d`): the committed seed is rebuilt at this
release's sources and carries `Float` (`binary64`), modules and `Proc`
`do`-notation over the same 54-member source closure
(`bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS` — 54 members,
`SHA256SUMS` digests `845b99efab72…`/`b52b07d1009f…`; `seed-host.c`
reads each module's exported `__heap_base`). In the release archive, in
closing order:

- the `Proc` execution hosts (`glue/host/`), the standard `Proc` modules
  (`lib/ProcBytes.rsd`, `lib/Proc9.rsd`, `glue/std/`) and the `rsd run`
  entry (`glue/rsd/`);
- the multi-module CLI example (`examples/app04/`), built and run from
  the seed by the `README.md` quick start;
- the Apache-2.0 balanced map (`lib/AvlMap.rsd`, ported from Lean
  v4.36.0), replacing the 0.3 port named in `release/PROVENANCE.tsv`;
- the multi-hop and recursion composition theorems
  (`lean/nf-compose/NfCompose/HopCompose.lean`,
  `lean/nf-compose/NfCompose/Rec.lean`,
  `lean/nf-compose/NfRec/CheckedStatus.lean`) and the `Float`
  differential and mutation inputs under `instruments/lrc-host/`.

Held out of 0.4: GPU benchmarks (`benchmarks/bend/`), the surface-syntax
Lean package, Cedar, proof checking, and the repository-side parts of
the `rsd` native build closure (`release/GAPS.tsv`). No path shipped in
0.3 leaves the archive (`release/PRIOR-SHIP-SETS.tsv` carries the 602
`rsd-0.3` rows).
