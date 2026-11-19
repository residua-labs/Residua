# Release manifest: closure roles and pending files

This is the inventory for release 0.1, the minimal self-bootstrap
closure, not a publishable file list. The requirements are
PUBLIC-RELEASE-0 revisions 4e and 4f and plan/Closure.lean
`MinimalBootstrap`. The 0.1 candidate contains the committed wasm seed
(`bootstrap/seed/stage-14274/`), the source closure of `rsdc` and `rsc`
(the 54 members of `bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS`),
the runtime (`lib/rt` and the `lib/Runtime*` members, plus the C host
bridges the seed recipe and execution host use), and the stranger
documents (`release/docs/`, `bootstrap/README.md`, `LICENSE`, `NOTICE`,
`lean-toolchain`).

The closure is met: seed -> rsdc, rsc -> fixpoint byte-equal in a clean
environment without Lean, elan, lake, Node or OCaml
(clean-environment reproduction recorded repository-side,
installed at `0d7bf0239`, seed recipe in `bootstrap/seed/stage-14274/README.md`),
plus the scm semantics of hole 6 (`gates/semalign/`).

Not in 0.1 (deferred to 0.1x, named): modules (hole 7), real programs
(hole 12), the no-Lean chain beyond the bootstrap cone (hole 11), the
q-format batch, the application suites (SQLite/Tendril/Cedar apply from
0.11), the R-CIC checker and `rsd_proofs`, the new surface syntax and
the rsx entry, the frozen waist semantics as a claim, the `raisin`
command and its examples, the trellis closure, and the OCaml
instrumented route. Those files remain in the repository as
repository-only rows; their documents may ship as specifications marked
"draft" in a later version. Phase-2 web, Cedar, performance and Quench
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
WABT-RUNTIME-SHA256SUMS}`), plus the 54/54 member verification from git
objects recorded at the branch cut. The combined declared/prerequisite/
build closure is tracked in `BUILD-INPUTS.tsv`. The offline replay
checks the named receipt facts and then compares the inputs against the
current tree. The older pinned-Z1 pair (`bootstrap/seed/{rsdc,rsc}.wasm`,
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

p9 still examines every tracked `.rsd`/`.lean` outside the root
`reports/` directory, regardless of the eventual archive selection; the
0.1 counter is the ship-set files that *declare* an NF instance (an NF
shell or Model/Profile instance) and fail NFCheck — files declaring no
instance are outside p9. At this head the count is 4, each row named
with its NFCheck classes in `release/FINDINGS.tsv` (ships as-is; a fix
is a new seed cut, routed to owners for 0.1x). For p3/p4 the
current global census is diagnostic until each manifest path is
classified; the 38 seat-name rows inside q-pinned spec and seed
files are likewise named in `release/FINDINGS.tsv`. No zero-finding or
complete-provenance claim follows from this draft inventory.

Evidence and recipes are retained under `reports/release-readiness-r1/`
and the existing `reports/trellis-evidence/` tree. They are not
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

p7, the third-party check, covers the seed and the scm formats only for
0.1; p8 does not apply: 0.1 ships no proof checking (no checker, no
certificates). The shipped specification texts under `lean/rsd-cert/` are
Lean 4.14 sources pinned as text — their `theorem` declarations are part
of the pinned spec, not claims checked inside 0.1.
