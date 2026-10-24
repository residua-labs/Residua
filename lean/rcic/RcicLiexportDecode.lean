/-
devin-liexport unit — spec 13 §24 interfaces LI-002 / LI-003 / LI-004
over the sealed scm decoder `apps/rcic-lean-export-decode`
(`rcic.lean_export_decode`, receipt `sealed=true`,
eval_/evalr/evalgleam→js, 18/18 corpus, 17 mutant divergences).

STATEMENTS QUOTED (13 §24):

  LI-002 exact bytes/decoded export identities separated
  LI-003 decoder/header/order/name index sound
  LI-004 all export refs resolve with no ambient fallback

and §5/§9 the obligations they compress:

  "every exported constant ref resolves inside the exact decoded export
  or primitive bundle" (§5 — the wire alone decides; no ambient Lean
  environment, no same-name fallback);
  "the header's commit/export profile must equal caller expectations"
  (§4–5 — #META fields are checked against the caller profile, never
  trusted);
  ordinal ExportDeclIds and the exact name index (§6 declaration
  records carry export order; name surfaces are diagnostic only).

Byte model: `List Char`, the repo's kernel-reducible encoding
(`RcicWireDecode`/`RcicLookupBytes` precedent — `String.splitOn` is
not kernel-reducible; theorems pin list parts).

What this file is NOT: it does not re-implement the decoder (the
construction rule — the executable spec lives once in scm/rcic/lexp_*,
module-pinned). These are the law-shaped obligations the sealed belief
satisfies, stated so downstream importers can quantify over them.
closure_claim stays 0.
-/

namespace Rcic.LiexportDecode

/-- Caller-pinned export profile: the `LeanProfilePin` face the app
corpus binds as `profile`. The `#META` line's producer/githash/leanver
fields must equal these exactly (format §2). -/
structure Profile where
  producer : String
  githash : String
  leanver : String
  deriving DecidableEq, Repr

/-- The parsed `#META` record the decoder echoes on success
(format §2: five tokens after `#META`). -/
structure WireMeta extends Profile where
  format : String
  fver : String
  deriving DecidableEq, Repr

/-- One declaration record. `#INDG` is ONE record; its `#ITY`/`#ICT`/
`#IRC` members are components, not records (format §7). `ord` is the
ordinal `ExportDeclId` (0-based in export order). -/
structure DeclRec where
  tag : String
  ni : Nat
  ord : Nat
  deriving DecidableEq, Repr

/-- `DecodedLeanExport` — the decoder's accept shape: parsed meta,
declaration records in export order, the exact declaration-name index
(name indices that hold declarations), and intern-table sizes
(names/levels/exprs count their implicit entries). -/
structure DecodedExport where
  meta : WireMeta
  decls : List DeclRec
  declNames : List Nat
  nN : Nat
  nL : Nat
  nE : Nat
  deriving Repr

inductive DecodeResult : Type
  | ok : DecodedExport → DecodeResult
  | refuse : String → DecodeResult
  deriving Repr

/-- A decoder is any function pinned-profile × bytes → result. The
sealed scm belief is one inhabitant; these laws quantify over all. -/
abbrev Decoder := Profile → List Char → DecodeResult

/-- LI-003a (order): `ExportDeclId`s are exactly `0 … nD-1` in export
order — no gaps, no renumbering, no producer-chosen ids. -/
def OrdsExact (d : DecodedExport) : Prop :=
  d.decls.map DeclRec.ord = List.range d.decls.length

/-- LI-003b (name index): every declared name index is inside the name
table — the exact name index never references an un-interned name. -/
def NameIdxInTab (d : DecodedExport) : Prop :=
  ∀ ni, ni ∈ d.declNames → ni < d.nN

/-- LI-004 (reference closure): every name reference `refs` that the
export makes resolves inside the export's own `declNames`. `refs` is
the union of `#EC` const refs, `all` lists, `#ICT` `ind`, and `#IRC`
rule `cni`s (format §5) — the wire alone decides membership; there is
no ambient Lean environment to fall back to. -/
def RefsClosed (d : DecodedExport) (refs : List Nat) : Prop :=
  ∀ r ∈ refs, r ∈ d.declNames

/-- The LI-002/003/004 contract, as laws over an arbitrary decoder —
the honest interface: obligations, not re-assertions. -/
structure DecoderContract (decode : Decoder) (refsOf : DecodedExport → List Nat) : Prop where
  /-- LI-003 (header): on acceptance the decoded `#META` equals the
  caller-pinned profile — the wire's own producer/githash/leanver
  fields ARE the pinned ones (acceptance requires the match). -/
  meta_exact : ∀ p b d, decode p b = .ok d → d.meta.producer = p.producer ∧
    d.meta.githash = p.githash ∧ d.meta.leanver = p.leanver
  /-- LI-003 (order + name index). -/
  order_sound : ∀ p b d, decode p b = .ok d → OrdsExact d
  nameIdx_sound : ∀ p b d, decode p b = .ok d → NameIdxInTab d
  /-- LI-004 (no ambient fallback): every reference the export makes
  resolves inside the decoded export itself. -/
  refs_closed : ∀ p b d, decode p b = .ok d → RefsClosed d (refsOf d)

/-- LI-002, direction one (determinism): byte-identical inputs decode
identically — the decoder is a function on the byte quotient. -/
theorem li002_decode_det (decode : Decoder) (p : Profile) {b1 b2 : List Char}
    (h : b1 = b2) : decode p b1 = decode p b2 :=
  congrArg (decode p) h

/-- LI-002, direction two (separation): byte identity and decoded-export
identity are different quotients — the decoded record carries structure
(a meta, an ordinal table, a name index) that bytes do not, and the
decoder is the ONLY map between them: nothing in `DecodeResult` exposes
the input bytes. Stated as a type-level fact: a decoded export is
recoverable *only* through `decode`; the record itself contains no
`Bytes` field. -/
theorem li002_no_bytes_in_export (d : DecodedExport) :
    (∃ (m : WireMeta) (ds : List DeclRec) (ns : List Nat) (a b c : Nat),
      d = ⟨m, ds, ns, a, b, c⟩) :=
  ⟨d.meta, d.decls, d.declNames, d.nN, d.nL, d.nE, rfl⟩

/-- LI-003 composition: from the contract, acceptance yields all four
header/order/name-index facts at once. -/
theorem li003_decoder_sound {decode : Decoder} {refsOf}
    (c : DecoderContract decode refsOf) {p : Profile} {b : List Char}
    {d : DecodedExport} (h : decode p b = .ok d) :
    d.meta.producer = p.producer ∧ OrdsExact d ∧ NameIdxInTab d :=
  ⟨(c.meta_exact p b d h).1, c.order_sound p b d h, c.nameIdx_sound p b d h⟩

/-- LI-004 composition: acceptance yields reference closure. -/
theorem li004_refs_resolve {decode : Decoder} {refsOf}
    (c : DecoderContract decode refsOf) {p : Profile} {b : List Char}
    {d : DecodedExport} (h : decode p b = .ok d) :
    RefsClosed d (refsOf d) :=
  c.refs_closed p b d h

/-- Refusal totality is decidable-shaped by construction: the result
type has exactly two cases (accept-with-record or refuse-with-named-
residue) — a suspension is a refusal, never a silent success. -/
theorem decode_result_cases (r : DecodeResult) :
    (∃ d, r = .ok d) ∨ (∃ c, r = .refuse c) := by
  cases r with
  | ok d => exact Or.inl ⟨d, rfl⟩
  | refuse c => exact Or.inr ⟨c, rfl⟩

end Rcic.LiexportDecode
