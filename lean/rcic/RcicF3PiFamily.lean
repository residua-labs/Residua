import rcic.RcicF3PiProducer

/-!
# Indexed families from dependent guarded W signatures

`family_cases` exposes the actual constructor and every product-typed
recursive field of a family member. `family_iff` also folds arbitrary
product members, using explicit ambient choice data. The signatures
retain arbitrary finite Pi depth and dependent result indices.

This is the semantic family equation. It does not identify a raw typed
group with a signature or assert the full group invariant.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.F3.PSet
universe u v

/-- Every indexed family member has an actual constructor presentation,
with all recursive fields in their full dependent products. -/
theorem RecSig.family_cases {I : Type v} (S : RecSig.{u, v} I) (i : I) {z : PSet.{u}}
    (hz : z ∈ S.family i) :
    ∃ (s : S.Sh) (f : S.Field s → PSet.{u}),
      (∀ k, f k ∈ (S.tel s k).denote S.family) ∧
      Equiv z (S.code s f) ∧ S.tag (S.code s f) i := by
  obtain ⟨⟨w, hw⟩, ht, he⟩ := mem_sep.mp hz
  cases hw with
  | sup s g hg hok =>
    let v : (k : S.Field s) → PiTel.Value.{u, u + 1}
        (S.tel s k).tel (fun _ => PSet.{u}) := fun k => (S.tel s k).tel.unflatten
      (fun p => decG S.toPiSig.toGSig (g ⟨k, p⟩))
    have hr : ∀ k, (S.tel s k).Rel S.family (v k) := by
      intro k
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      rw [show v k = (S.tel s k).tel.unflatten
        (fun p => decG S.toPiSig.toGSig (g ⟨k, p⟩)) from rfl,
        PiTel.flatten_unflatten]
      refine mem_sep.mpr ⟨⟨g ⟨k, p⟩, hg ⟨k, p⟩⟩, ?_, Equiv.rfl⟩
      simpa only [RecSig.toPiSig, PiSig.toGSig, PiTel.flatten_unflatten] using hok k p
    exact ⟨s, fun k => (S.tel s k).encode (v k),
      fun k => (S.tel s k).encode_mem _ _ (hr k), he.symm, ht⟩

/-- Constructor closure at all result tags, retaining every full product
field. A tag need not be injective; the definition makes no such assumption. -/
def RecSig.Closed {I : Type v} (S : RecSig.{u, v} I) (X : I → PSet.{u}) : Prop :=
  ∀ (s : S.Sh) (f : S.Field s → PSet.{u}),
    (∀ k, f k ∈ (S.tel s k).denote X) →
    ∀ i, S.tag (S.code s f) i → S.code s f ∈ X i

/-- Exact constructor equation. The backward direction uses explicit
choice data only to represent arbitrary product-typed children as trees. -/
theorem RecSig.family_iff {I : Type v} (ch : Choice.{u}) (S : RecSig.{u, v} I)
    (i : I) (z : PSet.{u}) :
    z ∈ S.family i ↔ ∃ (s : S.Sh) (f : S.Field s → PSet.{u}),
      (∀ k, f k ∈ (S.tel s k).denote S.family) ∧
      Equiv z (S.code s f) ∧ S.tag (S.code s f) i := by
  constructor
  · exact S.family_cases i
  · rintro ⟨s, f, hf, hz, ht⟩
    obtain ⟨w, _, he⟩ := mem_sep.mp (S.produce_of_mem ch s f hf)
    exact mem_sep.mpr ⟨w, S.tag_congr _ _ he.symm i ht, he.trans hz.symm⟩

/-- Leastness among all constructor-closed indexed families. The proof
uses guarded-W induction, without finite-height or bounded-Pi premises. -/
theorem RecSig.family_least {I : Type v} (S : RecSig.{u, v} I) (X : I → PSet.{u})
    (h : S.Closed X) : ∀ i, Sub (S.family i) (X i) := by
  have key := S.toPiSig.induction_mem (fun z => ∀ i, S.tag z i → z ∈ X i)
    (fun a b he ha i hb => mem_congr_left he
      (ha i (S.tag_congr b a he.symm i hb)))
    (by
      intro s f ih hok i ht
      apply h s (fun k => (S.tel s k).encode (f k)) ?_ i ht
      intro k
      apply (S.tel s k).encode_mem
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      exact ((PiTel.all_iff _ _ _).mp (ih k) p) _ (hok k p))
  intro i z hz
  obtain ⟨w, ht, he⟩ := mem_sep.mp hz
  exact key z ⟨w, he⟩ i (S.tag_congr _ _ he i ht)

/-- Elementary folding of the exact equation; no closure premise is
required from the caller. -/
theorem RecSig.family_closed {I : Type v} (ch : Choice.{u}) (S : RecSig.{u, v} I) :
    S.Closed S.family :=
  fun s f hf i ht => (S.family_iff ch i _).mpr ⟨s, f, hf, Equiv.rfl, ht⟩

/-- Semantic closure for a small signature cannot refute supplied model
data: its only choice input is the existing `c0` field. This is not a
non-refutability theorem for `RoleModel.StepAG`. -/
theorem RecSig.closure_nonrefutable (P : Premises4) {I : Type v} (S : RecSig.{0, v} I) :
    ¬ (S.Closed S.family → (Premises4 → False)) := by
  intro h
  exact h (S.family_closed P.c0) P

end Rcic.F3.PSet
