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
S7	rsx->scm	semantics/Rsx/Lower.rsd	release-head	4e93ca5cc389e368f369d0e3a02ee8b282b5197eecd20489b4af5b216acd2e86	STATED	the adequacy statement of the reference lowering rsx to scm ; no proof claimed
S7	lambda-RC->wasm0	semantics/Wasm0/Hop.rsd	8771db1e0	141d72a2d306f26b805603339bb4cc145721a752151f1390b07e6512d6870835	STATED	the hop statement lambda-RC to wasm0 ; no proof claimed
S7	per-hop gate	gates/semalign/Check.rsd	8771db1e0	cea7f10fe33703af2828f2177498840bac80caf30ce1a6ac4daf3f7eeb2fa6ab	GATED	the rscm-vs-evalLF differential gate over gates/semalign/CORPUS.tsv; METHOD.md records the protocol, rerun at the tag
S12	0.1	docs/LANGUAGE.md	release-head	ff9bd84845281284197c04d17b9abf7b9f24539e491bf8766a3c6225f22f5339	GATED	the fixed grammar: what the shipped rsdc front edge accepts and refuses; measured against the probe corpus (repository-side)
W	v2	docs/EMITTER.md	release-head	46f73b69cf45d487a4ebee0bef44225c99688965042b5d0114cb9c57e1087f3e	STATED	the RSCM wire format (the scm layer's binary form, `.rscm`); its `52 53 43 4d` + version header is emitted in `rsdc/Compile.rsd` and read in `rsc/rsc.rsd`
W	v2	lib/RscBase.rsd	release-head	b616c95952977f208ccb2228e374c06da803cf595048129a906a83b379f0cf66	STATED	the calling convention and the wire op set the emitter writes and the loader reads (WIRE-SEQ-0 revision 2)
B	stage-14274	bootstrap/seed/stage-14274/README.md	release-head	c466cbc9354772e5c31d706a8cef33734f857da4592189f8116edee1efb99597	STATED	the seed format and the bootstrap recipe (clean-env rebuild, member verification, controls)
B	stage-14274	bootstrap/seed/stage-14274/SOURCE-MEMBERS-SHA256SUMS	release-head	f087a106a539ef2abd164b52869f6f3c2041546b556d426f0d098dc411916ae4	STATED	the 53-member source closure the seeds are cut from
B	stage-14274	bootstrap/seed/stage-14274/ASSEMBLY.tsv	release-head	4fdd3977b83f295573b340dec44f23db5646e3f12f9f69a54f9d66dd96bd51e4	STATED	the member-to-bundle assembly link: per-section order, member digest, span digest and kind
B	z1	bootstrap/seed/manifest.json	release-head	81de792e8cd82dd9529075df64db8891797b86df5b809f62e3632e18a0cf77e6	STATED	the older pinned-z1 seed pair's identity manifest (alternate route)
D	sha256	bootstrap/seed/stage-14274/SHA256SUMS	release-head	6c897b35f87bf5da640cb2e580a2f0f661e2054abd698d80954d87cb352e86b4	STATED	artifact identity for 0.2: sha256 of bytes (the seed pair's published digests; the archive and receipts are recorded in a repository-side manifest table); the typed q of row Q is the content identity

Q	v1	docs/QFORMAT.md	release-head	6805f5fad6d601d5b5eabb4290f061ab89d4e4a0fb876dc7755dec94106ff2c5	STATED	the typed content address: digest vs q, preimage grammar, kind registry v1, comparison rule
S10	class	semantics/Syntax/Class.rsd	release-head	ada9fd3a711d07c8d06c0efaac014e93584363151a8f0a3693c5dfc082c556dc	FROZEN	the grammar class the syntax engine is closed over (`SynSpec.Grammar`, `Parses`, `refParses` with soundness); acceptance evidence repository-side
E0–E4	r3	semantics/Effect/Judgment.lean	release-head	5a4a077475ea6faa72ab92c98e2fc2c57c90a461d6f6a503e63db75cd895aa82	FROZEN	the effect-boundary semantics: wire format, admission and seal judgments, conformance classifier, recorded transport (all 36 files of `semantics/Effect/` pinned per file in `release/SOURCE-ROLES.tsv`; evidence `reports/effect-sem/`)

Not in this set (0.2x, own versions later): the rsx/R-CIC specs
(S1–S3), modules (S16.md), Lean IR (S22.md).

`closure_claim = 0`
