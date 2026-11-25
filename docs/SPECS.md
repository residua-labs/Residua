# SPECS — the specification set

One row per specification the shipped artifacts depend on. Columns:
name, version, file, commit, sha256, status, governs. `commit` is the
revision at which the row was read (8771db1e0 for the frozen set;
the row's sha256 is the binding value — re-check every sha256 against
the tag). Status: FROZEN = pinned by content digest; STATED = prose or
statement form, no proof claimed; GATED = accompanied by a mechanical
gate whose result is reproduced at the tag.

name	version	file	commit	sha256	status	governs
S4	evalLF	lean/rsd-cert/Residua/Bootstrap/Semantics.lean	8771db1e0	4ffcb7d990e8c77fa5dce42bcb4e1ae798e3cddd04803ac7c1fcbd2cb7fa46d2	FROZEN	the scm layer's semantics (evalLF / evalBoot); what `.scm`/`.rscm` programs mean
S5	r2	semantics/Lrc/Sem.rsd	release-head	9223f1a544bf27e5122164c6f4f7d3a4e3392d310bf9b93e1ab7a35df43138d0	FROZEN	the lambda-RC intermediate language (r2 text: the r2 datatype declarations live in lib/lrc/Ir.rsd; r1 q 05eceed6… was read at 8771db1e0 and is superseded)
S6	r2	semantics/Wasm0/Sem.rsd	8771db1e0	f500578a516e03486e6930a8e825b508e37d415c2a1243d60f98a96c22c04689	FROZEN	the wasm0 instruction set of the committed seeds and of every emitted module
S7	rsx->scm	semantics/Rsx/Lower.rsd	release-head	57e122579cd59121c642ef98a593c2fc0cf49ef67320ee807a3cfef02417c173	STATED	the adequacy statement of the reference lowering rsx to scm ; no proof claimed
S7	lambda-RC->wasm0	semantics/Wasm0/Hop.rsd	8771db1e0	141d72a2d306f26b805603339bb4cc145721a752151f1390b07e6512d6870835	STATED	the hop statement lambda-RC to wasm0 ; no proof claimed
S7	per-hop gate	gates/semalign/Check.rsd	8771db1e0	cea7f10fe33703af2828f2177498840bac80caf30ce1a6ac4daf3f7eeb2fa6ab	GATED	the rscm-vs-evalLF differential gate over gates/semalign/CORPUS.tsv; METHOD.md records the protocol, rerun at the tag
S12	0.1	docs/LANGUAGE.md	release-head	67a004b0894d0a2e6aca55aa1107fcf102ee5283defdf3a7c98cd2af373c99e4	GATED	the fixed grammar: what the shipped rsdc front edge accepts and refuses; measured against the probe corpus (repository-side)
W	v2	docs/EMITTER.md	release-head	e3f2c0502637a4f968d2bf06701d6b3bab3be94bec0d024fddf586e6aa5be46b	STATED	the RSCM wire format (the scm layer's binary form, `.rscm`); its `52 53 43 4d` + version header is emitted in `rsdc/Compile.rsd` and read in `rsc/rsc.rsd`
W	v2	lib/RscBase.rsd	release-head	95076a324e82d28f0a9c003bb62e81725ea4a12589665c235d680136b0c3265a	STATED	the calling convention and the wire op set the emitter writes and the loader reads (WIRE-SEQ-0 revision 2)
B	stage-14274	bootstrap/seed/stage-14274/README.md	release-head	face6f899960d4ef298b3db2fc4237fe3640674e37663e96c6c08d6ad0413e1f	STATED	the [seed](GLOSSARY.md) format and the bootstrap recipe (clean-env rebuild, member verification, controls; Linux x86-64)
B	stage-14274	bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS	release-head	99f55f6a19d81cee3c03e26e4853ebefb81d94edeee5764218bb3e65d74a52fe	STATED	the 54-member source closure the seeds are cut from
D	sha256	bootstrap/seed/stage-14274/SHA256SUMS	release-head	35a4fd926889284c9e3ac87046b1d4ae05f00a992d7f54685be1dd91b01743e9	STATED	artifact identity for 0.4: sha256 of bytes (the seed pair's published digests; the archive and receipts are recorded in a repository-side manifest table); the typed q of row Q is the content identity

Q	v1	docs/QFORMAT.md	release-head	20e227e2ad302e9df7d36fb7dc43a4deeb0f11a2f7faa57fc8a312ba898a1daf	STATED	the typed content address: digest vs q, preimage grammar, kind registry v1, comparison rule
S10	class	semantics/Syntax/Class.rsd	release-head	ada9fd3a711d07c8d06c0efaac014e93584363151a8f0a3693c5dfc082c556dc	FROZEN	the grammar class the syntax engine is closed over (`SynSpec.Grammar`, `Parses`, `refParses` with soundness); acceptance evidence repository-side
E0–E4	r3	semantics/Effect/Judgment.lean	release-head	5a4a077475ea6faa72ab92c98e2fc2c57c90a461d6f6a503e63db75cd895aa82	FROZEN	the effect-boundary semantics: wire format, admission and seal judgments, conformance classifier, recorded transport (all 37 files of `semantics/Effect/` pinned per file in `release/SOURCE-ROLES.tsv`; evidence `reports/effect-sem/`)

NF	4432a34	lean/nf-compose/pinned/MSTNecessityExecModelMWE.lean	release-head	3949bccb8b940250c130f4a1ee7dc16af237d46200fd90b9fb8607663ffb0758	FROZEN	the pinned `ExecModel` instance the MST-NF composition theorems are proved over (vendored from `github.com/residua-labs/MST-NF` @ `4432a34`, which holds the proofs)

Not in this set (own versions later): the rsx/R-CIC specs
(S1–S3), modules (S16.md), Lean IR (S22.md).

