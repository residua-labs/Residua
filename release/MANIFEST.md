# Release manifest: closure roles and pending files

This is the inventory for release 0.1, the minimal self-bootstrap
closure, not a publishable file list. The requirements are
the public-release-0 requirement revisions 4e and 4f and the
`MinimalBootstrap` closure plan. The 0.1 candidate contains the committed wasm seed
(`bootstrap/seed/stage-14274/`), the source closure of `rsdc` and `rsc`
(the 53 members of `bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS`),
the runtime (`lib/rt` and the `lib/Runtime*` members, plus the C host
bridges the seed recipe and execution host use), and the stranger
documents (`docs/`, `bootstrap/README.md`, `LICENSE`, `NOTICE`,
`lean-toolchain`, `README.md`, `README.zh-CN.md`, `CHANGELOG.md`,
`CHANGELOG.zh-CN.md`, `release/notes/`, `release/licenses/`,
`release/NOTICES.md`, `release/PROVENANCE.tsv`).

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
`bootstrap/seed/stage-14274/{SHA256SUMS,EXECUTOR-SHA256SUMS,
REBUILT-SHA256SUMS,SOURCE-MEMBERS-SHA256SUMS,WABT-SHA256SUMS,
WABT-RUNTIME-SHA256SUMS}`), plus the 53/53 member verification from git
objects recorded at the branch cut. The combined declared/prerequisite/
build closure is tracked in `BUILD-INPUTS.tsv`. The offline replay
checks the named receipt facts and then compares the inputs against the
current tree. The older pinned seed pair (`bootstrap/seed/{rsdc,rsc}.wasm`,
`rsc.rscm`, `manifest.json`, `bootstrap/sources.json`) ships as
committed seed material for the alternate bootstrap route; it is seed
input, not a rebuilt artifact of this candidate.

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
with its NFCheck classes in `release/FINDINGS.tsv` (ships as-is; a fix
is a new seed cut, routed to owners for a 0.1.x update). For the
path-scan checks the
current global census is diagnostic until each manifest path is
classified; the 43 seat-name rows inside q-pinned spec, seed and
generated manifest files are likewise named in `release/FINDINGS.tsv`.
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
stage-14274 members are unchanged at the `be7c7608c9` member-map bytes,
and the seed round-trip is unchanged. In the packet, in closing order:

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
