/-
RCIC 06 §18 — the bound core type and the semantic value transcribed as
R-CIC propositions over bound refs and canonical bytes (#6029 K3c: the
minimal citable source-target snapshot, delivered ahead of K4-2), pinned
to the `apps/rcic-scm-type-value` carrier that `ScmBoundTV` transcribes.

Owner text (06 §18, `docs/rcic/06_SCM_CORE_SEMANTICS.md`):

  CanonicalObjectAt(ref, bytes) : Prop      (01 §6, `RcicBoundObject`)
  BoundCoreType { type_ref, type_bytes,
                  type_at : CanonicalCoreTypeAt(type_ref,type_bytes) }
  SemanticValue(T : BoundCoreType) := Σ value_bytes, ValueAt(T,value_bytes)
  ValueAt is one of the seven wire execution predicates, "R-CIC
      propositions over bound refs and canonical bytes. They never invoke
      an ambient object store."

TRANSCRIPTION TABLE (06 §18 → Lean):

  CanonicalCoreTypeAt(type_ref,type_bytes) → `CanonicalCoreTypeAt`
        = `CanonicalObjectAt coreTypeSchema` (01 §6 at the core-type
        grammar, `ScmBoundTV.coreTypeSchema`)
  BoundCoreType { type_ref, type_bytes, type_at } → `BoundCoreType`,
        field names verbatim
  ValueAt(T, value_bytes)                    → `ValueAt`
  SemanticValue(T) = Σ value_bytes, ValueAt  → `SemanticValue`, the
        spec's Σ as a subtype (cf. `BoundObject`)

The carrier pin (M-002): `valueAt`'s two wire conditions — a whole-input
decode of the value bytes and an exact re-encode — are `valueBytesAt`,
and its typing check `rcic.scm_val_of_ty` is `toCore` (pinned in K2,
`ScmCore`). The Prop-level decode runs at fuel = the input's own length,
the convention `coreTypeSchema.decode` already uses; the carrier's fuel
refusal is "beyond the bound refused, not decided", so agreement with the
carrier decisions is stated at that fuel (`typeAt_atLength_accepts`,
`valueAt_atLength_accepts`). Agreement at an arbitrary accepting fuel
needs the decoder's fuel monotonicity — a K3c lemma, not assumed here.

NOT TRANSCRIBED (K3c proper, with the intrinsic side): the 06 §19 bridge
directions (encode → ValueAt, ValueAt → unique intrinsic value) and
`BoundCoreProgram` / `ProgramBundleAt` (their pin carrier is
`ScmBoundProgram`).
-/
import rcic.ScmBoundTV

namespace Rcic.Scm.BoundTV
open Rcic.Scm Rcic.Scm.Wire Rcic.BoundObject

/-- 06 §18 `CanonicalCoreTypeAt(type_ref, type_bytes)`: the generic
    `CanonicalObjectAt` (01 §6) at `coreTypeSchema`. -/
def CanonicalCoreTypeAt (r : Ref) (bytes : String) : Prop :=
  CanonicalObjectAt coreTypeSchema r bytes

instance (r : Ref) (bytes : String) : Decidable (CanonicalCoreTypeAt r bytes) :=
  inferInstanceAs (Decidable (CanonicalObjectAt coreTypeSchema r bytes))

/-- 06 §18 `BoundCoreType { type_ref, type_bytes, type_at }`, field names
    verbatim. -/
structure BoundCoreType where
  type_ref : Ref
  type_bytes : String
  type_at : CanonicalCoreTypeAt type_ref type_bytes

/-- `T`'s type as the schema reads it (`T.type_at` makes the decode
    succeed). -/
def BoundCoreType.ty (T : BoundCoreType) : CoreTy :=
  (coreTypeSchema.decode T.type_bytes).getD unitTy

/-- `valueBytesAt b`: `b` decodes whole-input at the input's own fuel (the
    `coreTypeSchema.decode` convention) and re-encodes exactly — the two
    wire conditions of the carrier's `scm_tv_value_at`. -/
def valueBytesAt (b : String) : Option Val :=
  match dec0 1 b.length b with
  | .ok (it, p) =>
    if p = b.length ∧ encVal (asVal it) = b then some (asVal it) else none
  | .error _ => none

/-- 06 §18 `ValueAt(T, value_bytes)`: `T`'s bytes decode under
    `coreTypeSchema` to `t`, `value_bytes` are the canonical wire bytes of
    `v`, and `v` elaborates at `t` (`toCore`, the model of the carrier's
    `rcic.scm_val_of_ty`). -/
def ValueAt (T : BoundCoreType) (vbytes : String) : Prop :=
  ∃ t : CoreTy, coreTypeSchema.decode T.type_bytes = some t ∧
    ∃ v : Val, valueBytesAt vbytes = some v ∧ (toCore t v).isSome = true

/-- 06 §18 `SemanticValue(T) := Σ value_bytes, ValueAt(T, value_bytes)`,
    the spec's Σ as a subtype. -/
def SemanticValue (T : BoundCoreType) : Type :=
  { vbytes : String // ValueAt T vbytes }

/-! ## Agreement with the carrier (at the input's own fuel) -/

/-- `typeAt` accepting yields its decoded type: the accepting case of
    `typeAt_accepts`, with the produced `CoreTy` named. -/
theorem typeAt_accepts_ty {fuel : Int} {r : Ref} {b : String}
    (h : (typeAt fuel r b).ok = 1) :
    ∃ it p, dec0 0 fuel b = .ok (it, p) ∧ p = b.length ∧
      encTy (asTy it) = b ∧ (typeAt fuel r b).t = asTy it := by
  obtain ⟨hc, hk, ⟨it, p, hd, hp, he⟩, hdg⟩ := typeAt_accepts _ _ _ h
  refine ⟨it, p, hd, hp, he, ?_⟩
  have htr : typeAt fuel r b = tvOk (asTy it) unitVal b r.digest := by
    unfold typeAt
    rw [if_neg (not_not_intro hc), if_neg (not_not_intro hk), hd]
    dsimp only
    rw [if_neg (not_not_intro hp), if_neg (not_not_intro he),
      if_neg (not_not_intro hdg)]
  rw [htr]
  rfl

/-- An accepting `typeAt` at the input's own fuel establishes
    `CanonicalCoreTypeAt`. -/
theorem typeAt_atLength_accepts {r : Ref} {b : String}
    (h : (typeAt b.length r b).ok = 1) : CanonicalCoreTypeAt r b := by
  obtain ⟨hc, hk, ⟨it, p, hd, hp, he⟩, hdg⟩ := typeAt_accepts _ _ _ h
  have hpre : prefixTy b = some (asTy it, p) := by
    unfold prefixTy; rw [hd]
  have hd0 : coreTypeSchema.decode b = some (asTy it) := by
    show (prefixTy b).map Prod.fst = some (asTy it)
    rw [hpre]
    rfl
  unfold CanonicalCoreTypeAt CanonicalObjectAt
  rw [hd0]
  dsimp only
  refine ⟨⟨he, ?_⟩, ?_, ?_⟩
  · rw [hc, hk]
    rfl
  · rw [hc, hk]
    exact hdg
  · show (match prefixTy b with
          | some (_, p') => p' == b.length
          | none => false) = true
    rw [hpre, hp]
    simp

/-- An accepting `valueAt` decomposes into its three conditions. -/
theorem valueAt_accepts {fuel : Int} {tt : TVOut} {b : String}
    (h : (valueAt fuel tt b).ok = 1) :
    ∃ it p, dec0 1 fuel b = .ok (it, p) ∧ p = b.length ∧
      encVal (asVal it) = b ∧ (toCore tt.t (asVal it)).isSome = true := by
  unfold valueAt at h
  cases hd : dec0 1 fuel b with
  | error c =>
    rw [hd] at h
    have h' : (0 : Int) = 1 := h
    exact absurd h' (by decide)
  | ok v =>
    obtain ⟨it, p⟩ := v
    rw [hd] at h
    dsimp only at h
    by_cases hp : p ≠ b.length
    · rw [if_pos hp] at h
      have h' : (0 : Int) = 1 := h
      exact absurd h' (by decide)
    · rw [if_neg hp] at h
      by_cases he : encVal (asVal it) ≠ b
      · rw [if_pos he] at h
        have h' : (0 : Int) = 1 := h
        exact absurd h' (by decide)
      · rw [if_neg he] at h
        cases ht : (toCore tt.t (asVal it)).isNone
        · rw [ht] at h
          refine ⟨it, p, rfl, Decidable.of_not_not hp, Decidable.of_not_not he, ?_⟩
          cases hx : toCore tt.t (asVal it) with
          | none => simp [hx] at ht
          | some _ => rfl
        · rw [ht] at h
          have h' : (0 : Int) = 1 := h
          exact absurd h' (by decide)

/-- Accepting `typeAt`/`valueAt` decisions at each input's own fuel
    establish `ValueAt`: the proposition this snapshot transcribes is what
    the carrier decides. -/
theorem valueAt_atLength_accepts {T : BoundCoreType} {vbytes : String}
    (hT : (typeAt T.type_bytes.length T.type_ref T.type_bytes).ok = 1)
    (hv : (valueAt vbytes.length
        (typeAt T.type_bytes.length T.type_ref T.type_bytes) vbytes).ok = 1) :
    ValueAt T vbytes := by
  obtain ⟨it0, p0, hd0, _, _, ht_t⟩ := typeAt_accepts_ty hT
  obtain ⟨it1, p1, hd1, hp1, he1, hval⟩ := valueAt_accepts hv
  rw [ht_t] at hval
  refine ⟨asTy it0, ?_, asVal it1, ?_, hval⟩
  · show (prefixTy T.type_bytes).map Prod.fst = some (asTy it0)
    unfold prefixTy
    rw [hd0]
    rfl
  · show (match dec0 1 vbytes.length vbytes with
          | .ok (it, p) =>
            if p = vbytes.length ∧ encVal (asVal it) = vbytes
              then some (asVal it) else none
          | .error _ => none) = some (asVal it1)
    rw [hd1]
    dsimp only
    rw [if_pos ⟨hp1, he1⟩]

end Rcic.Scm.BoundTV

/-! ## Instance witnesses (M-005)

The wire decoder (`dec0`, via `charAt`'s array indexing) is extern-backed
and does NOT reduce in the kernel, so the propositions above cannot be
inhabited by `rfl`/`decide` on concrete bytes — every pin in this library
is native (`#guard`). The snapshot's universal statements are witnessed by
the corpus rows below, which exercise both sides of the agreements at the
inputs' own fuel. -/

namespace Rcic.Scm.BoundTV.Pins
open Rcic.Scm Rcic.Scm.BoundTV

-- W0 the corpus' bound bool type is a `CanonicalCoreTypeAt` (native
-- evaluation of the Decidable instance; cf. the row-1 pin)
#guard decide (CanonicalCoreTypeAt (rf "b") "b")
-- W1 likewise at the nested record type (row 4)
#guard decide (CanonicalCoreTypeAt (rf TB) TB)
-- W2 a value's canonical bytes at the input's own fuel (row 16's input)
#guard valueBytesAt "B1;" == some (.b 1)
-- W3 row 20's nested value
#guard valueBytesAt VB == some V
-- W4 a noncanonical spelling has no canonical bytes (row 27's input)
#guard valueBytesAt "I007;" == none
-- W5 both agreement premises accept at own fuel (rows 1 and 16)
#guard (typeAt "b".length (rf "b") "b").ok == 1
    && (valueAt "B1;".length (typeAt "b".length (rf "b") "b") "B1;").ok == 1
-- W6 a refused type decision gives no bound type (row 7's input)
#guard (typeAt "i".length (rf "b") "i").ok == 0

end Rcic.Scm.BoundTV.Pins
