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
S5	r2	semantics/Lrc/Sem.rsd	release-head	bb75167a9511235dd660260fc2a91cd857184861bffd6db0197ec8facf00545c	FROZEN	the lambda-RC intermediate language (r2 text: the r2 datatype declarations live in lib/lrc/Ir.rsd; r1 q 05eceed6… was read at 8771db1e0 and is superseded)
S6	r2	semantics/Wasm0/Sem.rsd	8771db1e0	70023458875ad0ebc875d4420e89e2c54f700215bd5c56e621adf205213837b6	FROZEN	the wasm0 instruction set of the committed seeds and of every emitted module
S7	rsx->scm	semantics/Rsx/Lower.rsd	release-head	193ad7e607eea1cbdbcb4858808b76c2fcb6cef4761295c1efb2661e21834f19	STATED	the adequacy statement of the reference lowering rsx to scm ; no proof claimed
S7	lambda-RC->wasm0	semantics/Wasm0/Hop.rsd	8771db1e0	141d72a2d306f26b805603339bb4cc145721a752151f1390b07e6512d6870835	STATED	the hop statement lambda-RC to wasm0 ; no proof claimed
S7	per-hop gate	gates/semalign/Check.rsd	8771db1e0	cea7f10fe33703af2828f2177498840bac80caf30ce1a6ac4daf3f7eeb2fa6ab	GATED	the rscm-vs-evalLF differential gate over gates/semalign/CORPUS.tsv; METHOD.md records the protocol, rerun at the tag
S12	0.1	docs/LANGUAGE.md	release-head	1c055bd4551d874168f4a1e9433572b99664e7e200b68517d24b149f93025159	GATED	the fixed grammar: what the shipped rsdc front edge accepts and refuses; measured against the probe corpus (repository-side)
W	v2	docs/EMITTER.md	release-head	7676d13bdf921591c847bbb3884e8d0c827fd0bcefecd623b3c7fedf385dd98f	STATED	the RSCM wire format (the scm layer's binary form, `.rscm`); its `52 53 43 4d` + version header is emitted in `rsdc/Compile.rsd` and read in `rsc/rsc.rsd`
W	v2	lib/RscBase.rsd	release-head	6a52e004b371149794eed2925e13f8aa315001e8cbdcf933ecd19e7abde5851c	STATED	the calling convention and the wire op set the emitter writes and the loader reads (WIRE-SEQ-0 revision 2)
B	stage-14274	bootstrap/seed/stage-14274/README.md	release-head	b26e8d406f0590c8dfe728b99f88b2337caba411573da81ad130142984fef402	STATED	the [seed](GLOSSARY.md) format and the bootstrap recipe (clean-env rebuild, member verification, controls; Linux x86-64)
B	stage-14274	bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS	release-head	b49104e5fea04094c3c30e48c24cbe082c068c763d1037fec99089513f46a197	STATED	the 54-member source closure the seeds are cut from
B	z1	bootstrap/seed/manifest.json	release-head	81de792e8cd82dd9529075df64db8891797b86df5b809f62e3632e18a0cf77e6	STATED	the older pinned-z1 seed pair's identity manifest (alternate route)
D	sha256	bootstrap/seed/stage-14274/SHA256SUMS	release-head	80ec0ae56258b13385c187104499e6bb0ea5ddb5e58847b0e9a59d8eeca45ea2	STATED	artifact identity for 0.3: sha256 of bytes (the seed pair's published digests; the archive and receipts are recorded in a repository-side manifest table); the typed q of row Q is the content identity

Q	v1	docs/QFORMAT.md	release-head	6aecf2a54a4b2aea198fd7f76d427a0792c09d043d59c24e9e7e625baa4120c1	STATED	the typed content address: digest vs q, preimage grammar, kind registry v1, comparison rule
S10	class	semantics/Syntax/Class.rsd	release-head	ada9fd3a711d07c8d06c0efaac014e93584363151a8f0a3693c5dfc082c556dc	FROZEN	the grammar class the syntax engine is closed over (`SynSpec.Grammar`, `Parses`, `refParses` with soundness); acceptance evidence repository-side
E0–E4	r3	semantics/Effect/Judgment.lean	release-head	5a4a077475ea6faa72ab92c98e2fc2c57c90a461d6f6a503e63db75cd895aa82	FROZEN	the effect-boundary semantics: wire format, admission and seal judgments, conformance classifier, recorded transport (all 37 files of `semantics/Effect/` pinned per file in `release/SOURCE-ROLES.tsv`; evidence `reports/effect-sem/`)

NF	4432a34	lean/nf-compose/pinned/MSTNecessityExecModelMWE.lean	release-head	3949bccb8b940250c130f4a1ee7dc16af237d46200fd90b9fb8607663ffb0758	FROZEN	the pinned `ExecModel` instance the MST-NF composition theorems are proved over (vendored from `github.com/residua-labs/MST-NF` @ `4432a34`, which holds the proofs)

Not in this set (own versions later): the rsx/R-CIC specs
(S1–S3), modules (S16.md), Lean IR (S22.md).

