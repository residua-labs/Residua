# LANGUAGE — rsd bootstrap syntax 0.3

GENERATED — do not edit. Produced by the repository-side syntax
generator and the OCaml reference front end (its digests are pinned below;
evidence not shipped in 0.3).

This is the 0.3 bootstrap surface: the forms the committed
[seed](GLOSSARY.md)'s front edge (`rsdc/Compile.rsd`) accepts. It
**will change** in later versions
(0.4, ...): the repository-side design grammar is design-only
and is not this language; `.rsl`, the new surface, RSX entry, the
elaborator and theorem checking are not part of 0.3.

## Pinned inputs

- head `b4e22c2c32fcdf4ed3520c28fc18414bdca50da8`
- `rsdc/Compile.rsd` sha256 `cba87a068c374534e67679cd4b15933aa456e4e8841621dc251090996ad9dd89`
- `rsdc-ml` reference front end source sha256 `c85a6278b81bac2ad1338f5a044d385a90cb49dabb92b248ec9846c5e32243cc` (instrument binary sha256 `71ef9c2797ae6b8ba067121c47aead12b23c46216d923a9bb61f6eea7b04d9ef`; evidence not shipped in 0.3)
- `bootstrap/sources.json` sha256 `d18201d45a0b5aaeb91a868f7c941d460701f3569a645b8f88f7c15594e2b1bd` (development-repository file, not in the archive)
- `bootstrap/seed/manifest.json` sha256 `81de792e8cd82dd9529075df64db8891797b86df5b809f62e3632e18a0cf77e6` (development-repository file, not in the archive; the 0.3 seed identity is `bootstrap/seed/stage-14274/CUT.tsv`)
- refuse-corpus table sha256 `3aaad5cfd1f33d3d7a3c16892c9069f60d9bad12d0e164277f0c2711479d94a5` (private contract text; evidence not shipped in 0.3)

## Corpus verdicts

Accept corpus — the chain's own sources (bodies = file minus `^import `
lines, the `BuildAssembly.stripImports` rule):

| file | body bytes | reference `parse` |
|---|---|---|
| `lib/Tarjan.rsd` | 5206 | err=0 |
| `rsdc/Compile.rsd` | 889647 | err=0 |
| `lib/RscBase.rsd` | 86728 | err=0 |
| `lib/ShortCutFusion.rsd` | 8521 | err=0 |
| `lib/TypeFacts.rsd` | 5494 | err=0 |
| `rsc/rsc.rsd` | 329535 | err=0 |

Concatenated bundle (1325136 bytes): `parse` err=0.

Refuse corpus — the `form=rsdc-emit` rows of the pinned corpus table, run
against the `rsdc-ml` reference check. Every existing row still refuses (54 checked).
Rows citing `repository-side evidence` name files outside the source
archive, pinned by path and sha256 at this head.
Recorded gap rows are point-in-time: verdicts are `match` (20),
`pos_drift` (30, same residue at a moved line — the file
was edited after the gaps run), `residue_changed` (4,
still refused, on a different first construct), `missing` (1, an
untracked worktree copy of a `web/` source).

| file | recorded | observed | verdict |
|---|---|---|---|
| `lib/Proc.rsd` | rsdc_syntax@1:1 | rsdc_syntax@1:1 | match |
| `web/stdhttp/Char.rsd` — repository-side evidence, sha256 `4f22ddfc496a50176a22572776cc08d8ea19867954abe9cc56640bcd0f703bdb` | rsdc_syntax@95:65 | rsdc_syntax@24:1 | pos_drift |
| `web/stdhttp/Version.rsd` — repository-side evidence, sha256 `8760f427017843e8bb789157f83763fdcba19f8265acb2d90ad53efcee642ef5` | rsdc_syntax@19:1 | rsdc_syntax@87:29 | pos_drift |
| `web/stdhttp/ChunkedBuffer.rsd` — repository-side evidence, sha256 `505a48e2e04b9ec3ccc15173114f0f484616ac20eb690fdbc38d74e9e24ca225` | rsdc_syntax@19:1 | rsdc_syntax@41:1 | pos_drift |
| `web/stdhttp/Encode.rsd` — repository-side evidence, sha256 `d1ea02446e77c38162ba9956dca24f731f3f873ff8dc1ff865d505fe57712cfd` | rsdc_syntax@18:1 | rsdc_syntax@24:1 | pos_drift |
| `web/stdhttp/Method.rsd` — repository-side evidence, sha256 `66bd20d2a8d7ab2201767ace328086a7475830c80bf018762c61470d04ecd3b9` | rsdc_syntax@25:1 | rsdc_syntax@334:28 | pos_drift |
| `web/stdhttp/Status.rsd` — repository-side evidence, sha256 `dc4c2b6c3c68869fd675092ede9424df8b5266c2dc7a1577338b172a99f2ad4f` | rsdc_syntax@21:1 | rsdc_syntax@31:28 | pos_drift |
| `web/stdhttp/LowerCase.rsd` — repository-side evidence, sha256 `87fdd1d6d3e755e26bba409e20316195790bf3a09feca68ad7ab8add59e5e799` | rsdc_syntax@18:1 | rsdc_syntax@16:1 | pos_drift |
| `web/stdhttp/String.rsd` — repository-side evidence, sha256 `9319536839d3aa4d15bbb7c4bd0e411bd6aad977e76b73298a0d9a6399a44018` | rsdc_syntax@30:8 | rsdc_unclosed@47:20 | residue_changed |
| `web/stdhttp/IndexMultiMap.rsd` — repository-side evidence, sha256 `e43c23e7edfaa64d57efb710478e01e464c4ecd3245d6a87c0ea169819337117` | rsdc_unclosed@26:36 | rsdc_unclosed@26:36 | match |
| `web/stdhttp/HeaderName.rsd` — repository-side evidence, sha256 `93434d69309f7346aa1a53595e8873c4d472d00934031fcdd1a543bef983a647` | rsdc_syntax@20:1 | rsdc_syntax@28:26 | pos_drift |
| `web/stdhttp/HeaderValue.rsd` — repository-side evidence, sha256 `3b6d1deb9841f8f2f9e8baf75997f7ae0d8fcc34f24c069dccc65afcd6ad4997` | rsdc_syntax@20:1 | rsdc_syntax@34:27 | pos_drift |
| `web/stdhttp/Headers.rsd` — repository-side evidence, sha256 `813a59fcd5b64840c493e30fde865cd8fb77b1e90a58584d3e603479a443acaf` | rsdc_syntax@19:1 | rsdc_syntax@36:43 | pos_drift |
| `web/stdhttp/UriEncoding.rsd` — repository-side evidence, sha256 `b1c3261bb1940b2dcedf61c146ce92e194f8ae2732a5aa76328c7272d4cb99f7` | rsdc_syntax@21:1 | rsdc_syntax@30:17 | pos_drift |
| `web/stdhttp/IpAddress.rsd` — repository-side evidence, sha256 `d438f64bcf29a683a19317d4c2248e988aa4de09123f7c26e733b0e8fb27a3a3` | rsdc_syntax@27:29 | rsdc_syntax@27:29 | match |
| `web/stdhttp/Parsec.rsd` — repository-side evidence, sha256 `51baa75361eda895a2ba493714f9ee5635d5b6b9bd7c0990e2eaad352792837d` | rsdc_syntax@28:27 | rsdc_syntax@28:27 | match |
| `web/stdhttp/ByteArray.rsd` — repository-side evidence, sha256 `bfb12717955a0fa2ee5bfdb6cce8877cc80f2b7b62d7f6de826318a64691b8f1` | rsdc_syntax@196:14 | rsdc_syntax@196:14 | match |
| `web/stdhttp/UriBasic.rsd` — repository-side evidence, sha256 `8d7cbdefd31bb9daa7a9fcc897980fbd3ecb1f811b40916288d3682a3289ed18` | rsdc_syntax@28:1 | rsdc_syntax@42:22 | pos_drift |
| `web/stdhttp/UriParser.rsd` — repository-side evidence, sha256 `8bf942a77201ce44e9c39eb85a1aff5329769e8718fdeabbe5c3d906df713876` | rsdc_syntax@27:1 | rsdc_syntax@32:1 | pos_drift |
| `web/stdhttp/HeaderBasic.rsd` — repository-side evidence, sha256 `5b69a4e9f08d3f962ea680eefdf7bd2ba0e9d7430de67fcc1261d3a71d6cce9e` | rsdc_syntax@19:1 | rsdc_syntax@26:1 | pos_drift |
| `web/stdhttp/BodyLength.rsd` — repository-side evidence, sha256 `1ec4057a39ef14bc28cdd28013f3dc9a752bcc72f33a962e2c225d5a6beab345` | rsdc_syntax@18:1 | rsdc_syntax@41:1 | pos_drift |
| `web/stdhttp/Chunk.rsd` — repository-side evidence, sha256 `6e37efaa526cea076be0b5aca734cbff0af15c0e184f292d024841bfa8db496d` | rsdc_syntax@30:29 | rsdc_syntax@30:29 | match |
| `web/stdhttp/RequestHead.rsd` — repository-side evidence, sha256 `39ec52ac9a236afdf416beba2ee5e03dddbd95c97d34733dc4c5b032f7aba7c5` | rsdc_syntax@21:1 | rsdc_syntax@56:26 | pos_drift |
| `web/stdhttp/ResponseHead.rsd` — repository-side evidence, sha256 `bfae70b742d682d2ccfa223ae70860889235192e4c4485de0a18d629a3b6b073` | rsdc_syntax@18:1 | rsdc_syntax@45:26 | pos_drift |
| `web/stdhttp/H1Config.rsd` — repository-side evidence, sha256 `ecd4b7e79e9377639d55b69f7e41deae09a0a3c31b484638b993d71d68581bf9` | rsdc_syntax@18:1 | rsdc_unbound@26:11 | residue_changed |
| `web/stdhttp/H1Message.rsd` — repository-side evidence, sha256 `3de2f9c3be9e991205efb984045860281d5037f96be9b2bbb4bbb42c62f50835` | rsdc_syntax@22:1 | rsdc_syntax@42:23 | pos_drift |
| `web/stdhttp/H1Parser.rsd` — repository-side evidence, sha256 `60d0b1c98ccf31c1cec80b2f88f55ca521234592c09ff80844954a1f2b0d7527` | rsdc_syntax@24:1 | rsdc_syntax@24:1 | match |
| `web/stdhttp/H1Error.rsd` — repository-side evidence, sha256 `7525bb578f74f015ad7054b52540ecd1ce6a85aa078efee2fb0b391fed9b014d` | rsdc_syntax@18:1 | rsdc_syntax@87:27 | pos_drift |
| `web/stdhttp/H1Event.rsd` — repository-side evidence, sha256 `9e1dbfa5b824df4a3211e9c04fbc78218f6b37ec33cf7b13c96bd0d5b1254384` | rsdc_syntax@18:1 | rsdc_syntax@23:24 | pos_drift |
| `web/stdhttp/H1Reader.rsd` — repository-side evidence, sha256 `cdc27362018f02ef0fe49b5bee27630e99d23ad88a8d11d6923c4370bbc4864e` | rsdc_syntax@19:1 | rsdc_syntax@49:31 | pos_drift |
| `web/stdhttp/H1Writer.rsd` — repository-side evidence, sha256 `c29e495624c7f3e3cd20972c9ffb51a0a5ff6e52cc4c5509a8dfb0f74ae49836` | rsdc_syntax@19:1 | rsdc_syntax@73:25 | pos_drift |
| `web/stdhttp/H1Machine.rsd` — repository-side evidence, sha256 `b4f547df943c12eb4a26133f20dc44adc357ba4ae4fa77da48a8961e0d7d096f` | rsdc_syntax@19:1 | rsdc_syntax@27:29 | pos_drift |
| `web/Application.rsd` — repository-side evidence, sha256 `4d83dda3cb0f44076e33c42593133f35aee969d34af34800b5fc54f8e1fac8da` | rsdc_syntax@1:1 | rsdc_syntax@43:1 | pos_drift |
| `web/HttpGrammar.rsd` — repository-side evidence, sha256 `175eed00b37881ec5b31bd549a2b7b8ea3171bd329e1c6707910f22955b7bacf` | rsdc_syntax@23:9 | rsdc_syntax@23:9 | match |
| `web/HttpMatcher.rsd` — repository-side evidence, sha256 `326316ae0a315ff9b331e8edee88e5f4292cbf6e4c9f790f02c0d40531b4812d` | rsdc_syntax@45:3 | rsdc_syntax@45:3 | match |
| `web/h5i/H1Valid.rsd` — repository-side evidence, sha256 `6c5cdb97b3e9076c1eca80c442858a1c920d8691216831506f05a102f67e1a91` | rsdc_syntax@53:10 | rsdc_syntax@53:10 | match |
| `web/h5i/H1Decide.rsd` — repository-side evidence, sha256 `42cd1e438fb7bd5b06b7f8f5c3d8ca217f5243bcebdd31785a4d6b324113823b` | rsdc_syntax@21:1 | rsdc_syntax@21:1 | match |
| `web/h1/H1Rfc.rsd` — repository-side evidence, sha256 `e690a0c06f74508e5553fb54a1c21eccb708ad5f7ecebb529513427b43a441ad` | rsdc_syntax@32:52 | rsdc_syntax@32:52 | match |
| `web/h1/H1Stream.rsd` — repository-side evidence, sha256 `8cf3437fa9ad5d7503a6093e59075a4700809a7f4db1f34cab896330dbaf965f` | rsdc_syntax@29:20 | rsdc_syntax@29:20 | match |
| `web/Http.rsd` — repository-side evidence, sha256 `f5fa3c258c1d33bb1c30d1a131237a419eb3416e9157c3540b3f5d9ae1004525` | rsdc_syntax@72:3 | rsdc_syntax@72:3 | match |
| `web/HttpCodec.rsd` — repository-side evidence, sha256 `ef95387fe8c36481e46e39981f52c81471c67f9963854d428b7718806db33bc1` | rsdc_syntax@41:3 | rsdc_syntax@41:3 | match |
| `web/net/Admission.rsd` — repository-side evidence, sha256 `5ec3179dc7717424257d43a501d7c41fa7a336217dc923a59fdfa542541f2e83` | rsdc_syntax@1:1 | rsdc_syntax@57:72 | pos_drift |
| `web/net/Wire.rsd` — repository-side evidence, sha256 `383616b1cfdb7afd88591a111acae1ebdb8a0a6a75653bd87e3d35635be54c60` | rsdc_syntax@29:3 | rsdc_syntax@29:3 | match |
| `web/net/Completions.rsd` — repository-side evidence, sha256 `41e57c71bbaff631b47e1ff3264ec4a046e6750cc13cb3d91259a3e24c00034b` | rsdc_syntax@138:1 | rsdc_unbound@135:1 | residue_changed |
| `web/net/CompletionWire.rsd` — repository-side evidence, sha256 `5c928c633b8ee2ee1d99cbb739002dcd50e304ef3e202d54f7638c7c31de4784` | rsdc_syntax@16:3 | rsdc_syntax@16:3 | match |
| `web/server/Model.rsd` — repository-side evidence, sha256 `b6346c3b5fceb592f3e562d8c56f3976fe58a84e3c81b9d1803ae93c556b269d` | rsdc_syntax@30:13 | rsdc_syntax@29:13 | pos_drift |
| `web/server/Codec.rsd` — repository-side evidence, sha256 `7e1d54878b9960af560d0a13bae15f6aa51da77bcf6460672d932e0d62cf2b70` | rsdc_syntax@29:26 | rsdc_syntax@28:36 | pos_drift |
| `web/server/Proc.rsd` — repository-side evidence, sha256 `b92ea9de9532e6978731623037fb0c7614e6fcb2ea69e04ba1d3cd38f179f516` | rsdc_unclosed@41:71 | rsdc_unclosed@40:71 | pos_drift |
| `web/net/Context.rsd` — repository-side evidence, sha256 `97fc6905f6b355d2a07b6f862527327bd96820226fc9282f118470462b2cefe7` | rsdc_syntax@65:31 | rsdc_syntax@65:31 | match |
| `web/net/Rows.rsd` — repository-side evidence, sha256 `fd54958401975e2f673b0cf7ea2c51db313431d5633f632e5b69c056f9b9e75f` | rsdc_syntax@13:8 | rsdc_syntax@12:8 | pos_drift |
| `web/net/HostProbe.rsd` — repository-side evidence, sha256 `68748dc43c4067f9de4b7b336d3ad093e1060ed1817ba24e6ff72ad015a0d429` | rsdc_syntax@3:34 | rsdc_syntax@3:34 | match |
| `web/server/Live.rsd` — repository-side evidence, sha256 `f53f4a77f27a8e23a357d506220d2f99f9c5a62512ef330a9fabf3056b267cae` | rsdc_syntax@6:13 | rsdc_syntax@5:13 | pos_drift |
| `web/load/Serve.rsd` — repository-side evidence, sha256 `94e8565092af74c47eea76a14d3e024b7f05fd3f367359cfdb027f4f37d48d25` | rsdc_syntax@5:13 | rsdc_syntax@5:13 | match |
| `benchmarks/koka/KokaBase.rsd` | ? | rsdc_syntax@60:3 | residue_changed |

## Declaration probes

Minimal measured snippets (reference `parse` err codes):

| lead token | probe | err |
|---|---|---|
| `def` | `def f : Nat := 0` | err=0 |
| `structure` | `structure S where x : Nat` | err=0 |
| `inductive` | `inductive Foo where | a | b` | err=0 |
| `abbrev` | `abbrev A : Nat := 0` | err=1 |
| `abbrev` | `abbrev A : Nat` | err=1 |
| `instance` | `instance : Inhabited Nat := ⟨0⟩` | err=6 |
| `mutual` | `mutual def a : Nat := 0 def b : Nat := 1 end` | err=0 |
| `namespace` | `namespace N def a : Nat := 0 end N` | err=0 |
| `open` | `open N` | err=0 |
| `section` | `section S end S` | err=0 |
| `theorem` | `theorem t : Nat := 1` | err=1 |
| `axiom` | `axiom a : Nat` | err=1 |
| `class` | `class C where m : Nat` | err=1 |
| `variable` | `variable (n : Nat)` | err=1 |
| `opaque` | `opaque o : Nat` | err=1 |
| `import` | `import Lib.X` | err=1 |
| `partial` | `partial def f : Nat := 0` | err=0 |
| `by` | `def f : Nat := by exact 0` | err=1 |
| `deriving` | `structure S where x : Nat deriving Repr` | err=0 |
| `fun` | `def f : Nat -> Nat := fun x => x` | err=0 |

## Parse-tree contract

The front edge's own contract, verbatim from `rsdc/Compile.rsd`:

```
-- rsdc front edge: .rsd text to a parse tree, for the annotated subset.
-- Nodes are four Int slots in a persistent, chunked Array; node ids and links
-- are stable indices, -1 is none. The AVL holds synthetic name spans only.
-- 1 id a=start b=end (UTF-8 byte positions). 2 num a=start b=end c=value.
-- 3 str a=start b=end, raw, quotes included. 4 hole.
-- 5 app a=fn b=first li. 6 bin a=op b=lhs c=rhs.
-- 7 una a=op b=expr (1 neg, 2 not). 8 if a=c b=t c=e.
-- 9 let a=name b=ty c=let2. 10 let2 a=val b=body.
-- 11 list a=first li. 12 li a=expr b=next.
-- 13 paren a=inner. 14 inst a=ty b=first fld. 15 fld a=name b=expr c=next.
-- 16 arrow a=dom b=cod. 17 proj a=expr b=index.
-- 18 file a=first cmd. 19 cmd a=decl b=next.
-- 20 def a=name b=sig c=val. 21 sig a=first grp b=ret.
-- 22 grp a=first li b=ty c=next. 23 eqns a=first alt.
-- 24 alt a=first li b=body c=next. 25 body a=expr.
-- 26 struct a=name b=first fdcl. 27 fdcl a=name b=ty c=next.
-- 28 mutual a=first cmd. 29 dproj a=expr b=ns c=ne. 30 ascribe a=expr b=ty.
-- 31 termMatch a=scrutinee li b=first alt c=inferred result type after prep.
-- 32 lambda a=first grp b=body c=inferred result type after prep.
-- 33 checked index a=list receiver b=Nat index.
-- 34 namespace a=name b=cmds. 35 open a=names.
-- 36 scoped commands a=open names (-1 for section) b=cmdSpine.
-- 37 abbrev a=name b=ty.
-- 43 doBind a=name b=expr. 44 doBare a=expr. 45 doLet a=name b=ty c=expr.
-- 46 doBlock a=stmt spine. desugarSt erases these before check.
-- 47 anonymous constructor expression a=element spine.
-- 48 instance declaration a=name (-1 if automatic) b=sig c=val; erased by instanceLower.
-- 56 inferred type a=concrete type code; private to preparation.
-- Qualified decl names: ident slot c holds qa (a synth span >= fileLen);
-- receiver-pinned use-site idents hold c == -9.
-- bin ops: 1 +  2 -  3 *  4 /  5 ==  6 !=  7 <  8 >  9 <=  10 >=
-- 11 &&  12 ||  13 ::  14 ++
-- err: 1 syntax, 2 unclosed, 3 fuel, 4 nonassoc, 5 unbound, 6 type, 7 arity.
```

## Reserved words (33)

`def`, `do`, `deriving`, `decreasing_by`, `structure`, `section`, `set_option`, `where`, `with`, `mutual`, `match`, `end`, `else`, `if`, `in`, `inductive`, `instance`, `import`, `then`, `theorem`, `termination_by`, `let`, `namespace`, `abbrev`, `axiom`, `class`, `by`, `fun`, `return`, `open`, `opaque`, `variable`, `partial`

Reserved words are tokens, not all of them declaration forms: the probe
table above measures which lead positions the parser accepts at this
head (10 of 20 probes parse clean).

## Refusal vocabulary

Front-edge err codes (contract above). The reference instrument's named
residues (27):

`rsdc_arena_field`, `rsdc_arity`, `rsdc_array_operation`, `rsdc_array_receiver`, `rsdc_basic_data_lowering`, `rsdc_budget`, `rsdc_do`, `rsdc_dup_binder`, `rsdc_fuel`, `rsdc_mixed_partial`, `rsdc_nonassoc`, `rsdc_rec_ind`, `rsdc_runtime_binder`, `rsdc_runtime_fuel`, `rsdc_runtime_loop_scope`, `rsdc_runtime_name`, `rsdc_runtime_primitive_scope`, `rsdc_runtime_syntax`, `rsdc_runtime_type`, `rsdc_runtime_wire`, `rsdc_syntax`, `rsdc_type`, `rsdc_type_depth`, `rsdc_unbound`, `rsdc_unclosed`, `rsdc_unknown`, `rsdc_word_op`

## Lexical notes

- Line comments: `--` to end of line.
- String literals `"..."` are stored raw (node 3 keeps the quotes);
  character literals use `'x'`; anonymous constructors use `⟨...⟩`
  (UTF-8 ⟨, codepoint 10216); `#[` opens an array literal.
- Application is juxtaposition; `( )` groups; `[a, b]` is a list;
  `e[i]` is a checked index (node 33); `x.y` / `x.y.z` are projections
  (nodes 17, 29); `t : T` ascription is node 30.
- `if .. then .. else`, `let`, `fun`, `match`, `do` blocks and
  `{ ty with f := v, .. }` instance literals follow the tag table.
- Indentation is tracked by the front edge (`St.indent`); command
  spines and do-blocks follow it.
- Bodies are compiled without `import` lines: the toolchain strips
  every `^import ` line (`BuildAssembly.stripImports`); name resolution
  is positional against the bundle.

## Not in 0.3

Theorem proving (`theorem`, `by`, `simp`/`rw`/...), the elaborator and
R-CIC (`rsd_proofs`), the `.rsl` reader surface, the new surface syntax,
RSX entry and the repository-side design grammar. All later versions.
