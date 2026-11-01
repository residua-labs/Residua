import rcic.RcicF3PiEraseField
import rcic.RcicF3PiProducer

/-!
# Indexed guarded-W construction with proof-erased function fields

Result indices guard trees before proof erasure. They are not recovered
from decoded values: distinct Prop fibres may both contain only `∅`.
The small trees retain arbitrary dependent branch telescopes; their index
labels may inhabit a larger universe. A uniform constructor result face
supplies dichotomy. Typed-syntax extraction remains unpaid.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet
universe u v

/-- Decode the small trees with actual R-CIC proof erasure. The indexed
validity relation below, rather than a predicate on values, guards them. -/
def RecSig.erasedPiSig {I : Type v} (M : Interp.{u}) (S : RecSig.{u, v} I) : PiSig.{u} where
  Sh := S.Sh
  Field := S.Field
  depth := S.depth
  tel := fun s k => (S.tel s k).tel
  code := fun s f => S.code s (fun k => (S.tel s k).erasedEncode M (f k))
  ok := fun _ _ => True
  code_congr := fun s _ _ h => S.code_congr s _ _
    (fun k => (S.tel s k).erasedEncode_congr M _ _ (h k))
  ok_congr := fun _ _ _ _ h => h

/-- Index correctness is checked on tree children before their values
are erased. No injectivity or index discrimination by codes is assumed. -/
inductive RecSig.IndexedValid {I : Type v} (M : Interp.{u}) (S : RecSig.{u, v} I) :
    I → GT (S.erasedPiSig M).toGSig → Prop where
  | sup (s : S.Sh) (g : (S.erasedPiSig M).toGSig.br s → GT (S.erasedPiSig M).toGSig)
      (hg : ∀ k p, S.IndexedValid M ((S.tel s k).result p) (g ⟨k, p⟩)) :
      S.IndexedValid M (S.out s) (.sup s g)

/-- The indexed family contains all index-correct trees, of every height. -/
def RecSig.erasedFamily {I : Type v} (M : Interp.{u}) (S : RecSig.{u, v} I) (i : I) : PSet.{u} :=
  PSet.mk {w : GT (S.erasedPiSig M).toGSig // S.IndexedValid M i w}
    (fun w => decG (S.erasedPiSig M).toGSig w.1)

/-- A single family result face: all codes are proofs, or all are data.
Both alternatives are allowed; no domain-inhabitation condition appears. -/
def RecSig.CodeDich {I : Type v} (S : RecSig.{u, v} I) : Prop :=
  (∀ s f, Equiv (S.code s f) pempty) ∨ (∀ s f, ¬Equiv (S.code s f) pempty)

/-- The constructor face proves dichotomy of every indexed family fibre. -/
theorem RecSig.erasedFamily_dich {I : Type v} (M : Interp.{u}) (S : RecSig.{u, v} I)
    (hS : S.CodeDich) (i : I) : Dich (S.erasedFamily M i) := by
  rcases hS with hS | hS
  · apply Or.inl
    intro z ⟨⟨w, hw⟩, he⟩
    cases hw with
    | sup s g hg => exact he.symm.trans (hS s _)
  · apply Or.inr
    intro ⟨⟨w, hw⟩, he⟩
    cases hw with
    | sup s g hg => exact hS s _ he

/-- Arbitrary actual R-CIC field members fold into their declared result
fibre. Small choice selects trees only, never quotient representatives. -/
theorem RecSig.erasedProduce_of_mem {I : Type v} (M : Interp.{u}) (ch : Choice.{u})
    (S : RecSig.{u, v} I) (hS : S.CodeDich)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (s : S.Sh) (f : S.Field s → PSet.{u})
    (hf : ∀ k, f k ∈ Ed M ((S.tel s k).erasedType M (S.erasedFamily M))) :
    S.code s f ∈ S.erasedFamily M (S.out s) := by
  let Q := S.erasedPiSig M
  let r := fun k => (S.tel s k).erasedRead M (f k)
  have hr := fun k => (S.tel s k).erasedRead_spec M (hD s k)
    (S.erasedFamily M) (S.erasedFamily_dich M hS) (hf k)
  have hex : ∀ k p, ∃ w : GT Q.toGSig,
      S.IndexedValid M ((S.tel s k).result p) w ∧
        Equiv (decG Q.toGSig w) ((S.tel s k).tel.flatten (r k) p) := by
    intro k p
    have hp := (PiTel.all_iff _ _ _).mp (hr k).1 p
    obtain ⟨⟨w, hw⟩, he⟩ := hp
    exact ⟨w, hw, he⟩
  let pick := fun k p => ch (α := ULift.{u + 1} (GT Q.toGSig))
    (fun w => S.IndexedValid M ((S.tel s k).result p) w.down ∧
      Equiv (decG Q.toGSig w.down) ((S.tel s k).tel.flatten (r k) p))
    (let ⟨w, hw⟩ := hex k p; ⟨⟨w⟩, hw⟩)
  let ts : (k : S.Field s) → (S.tel s k).tel.Value (fun _ => GT Q.toGSig) :=
    fun k => (S.tel s k).tel.unflatten (fun p => (pick k p).1.down)
  have hv : S.IndexedValid M (S.out s) (Q.roll s ts) := by
    apply RecSig.IndexedValid.sup
    intro k p
    simpa only [Q, RecSig.erasedPiSig, ts, PiTel.flatten_unflatten] using (pick k p).2.1
  refine ⟨⟨Q.roll s ts, hv⟩, S.code_congr s _ f ?_⟩
  intro k
  apply Equiv.trans ((S.tel s k).erasedEncode_congr M _ (r k) ?_)
    (hr k).2.symm
  intro p
  simpa only [Q, RecSig.erasedPiSig, ts, PiTel.flatten_unflatten] using (pick k p).2.2

/-- Members expose their constructor with the exact output index. -/
theorem RecSig.erasedFamily_cases {I : Type v} (M : Interp.{u})
    (S : RecSig.{u, v} I) (hS : S.CodeDich)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (i : I) {z : PSet.{u}}
    (hz : z ∈ S.erasedFamily M i) :
    ∃ (s : S.Sh) (f : S.Field s → PSet.{u}),
      (∀ k, f k ∈ Ed M ((S.tel s k).erasedType M (S.erasedFamily M))) ∧
      Equiv z (S.code s f) ∧ S.out s = i := by
  obtain ⟨⟨w, hw⟩, he⟩ := hz
  cases hw with
  | sup s g hg =>
    let v : (k : S.Field s) → PiTel.Value.{u, u + 1}
        (S.tel s k).tel (fun _ => PSet.{u}) := fun k => (S.tel s k).tel.unflatten
      (fun p => decG (S.erasedPiSig M).toGSig (g ⟨k, p⟩))
    have hr : ∀ k, (S.tel s k).Rel (S.erasedFamily M) (v k) := by
      intro k
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      rw [show v k = (S.tel s k).tel.unflatten
        (fun p => decG (S.erasedPiSig M).toGSig (g ⟨k, p⟩)) from rfl,
        PiTel.flatten_unflatten]
      exact ⟨⟨g ⟨k, p⟩, hg k p⟩, Equiv.rfl⟩
    exact ⟨s, fun k => (S.tel s k).erasedEncode M (v k),
      fun k => (S.tel s k).erasedEncode_mem M (hD s k) _ (S.erasedFamily_dich M hS) _ (hr k),
      he.symm, rfl⟩

/-- Closure into each declared output fibre. -/
def RecSig.ErasedClosed {I : Type v} (M : Interp.{u}) (S : RecSig.{u, v} I)
    (X : I → PSet.{u}) : Prop :=
  ∀ (s : S.Sh) (f : S.Field s → PSet.{u}),
    (∀ k, f k ∈ Ed M ((S.tel s k).erasedType M X)) → S.code s f ∈ X (S.out s)

/-- The exact constructor equation retains output indices before erasure. -/
theorem RecSig.erasedFamily_iff {I : Type v} (M : Interp.{u}) (ch : Choice.{u})
    (S : RecSig.{u, v} I) (hS : S.CodeDich)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (i : I) (z : PSet.{u}) :
    z ∈ S.erasedFamily M i ↔ ∃ (s : S.Sh) (f : S.Field s → PSet.{u}),
      (∀ k, f k ∈ Ed M ((S.tel s k).erasedType M (S.erasedFamily M))) ∧
      Equiv z (S.code s f) ∧ S.out s = i := by
  constructor
  · exact S.erasedFamily_cases M hS hD i
  · rintro ⟨s, f, hf, hz, hi⟩
    subst i
    exact mem_congr_left hz.symm (S.erasedProduce_of_mem M ch hS hD s f hf)

/-- Leastness among dichotomous constructor-closed families, without
finite-height assumptions or set monotonicity across erasure changes. -/
theorem RecSig.erasedFamily_least {I : Type v} (M : Interp.{u}) (S : RecSig.{u, v} I)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (X : I → PSet.{u})
    (hX : ∀ i, Dich (X i)) (h : S.ErasedClosed M X) :
    ∀ i, Sub (S.erasedFamily M i) (X i) := by
  have key : ∀ i w, S.IndexedValid M i w → decG (S.erasedPiSig M).toGSig w ∈ X i := by
    intro i w hw
    induction hw with
    | sup s g hg ih =>
      apply h s _
      intro k
      apply (S.tel s k).erasedEncode_mem M (hD s k) X hX
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      simpa only [RecSig.erasedPiSig, PiTel.flatten_unflatten] using ih k p
  intro i z ⟨⟨w, hw⟩, he⟩
  exact mem_congr_left he (key i w hw)

/-- Elementary projection of the constructor-closure theorem. -/
theorem RecSig.erasedFamily_closed {I : Type v} (M : Interp.{u}) (ch : Choice.{u})
    (S : RecSig.{u, v} I) (hS : S.CodeDich)
    (hD : ∀ s k, (S.tel s k).DomainsDich) : S.ErasedClosed M (S.erasedFamily M) :=
  S.erasedProduce_of_mem M ch hS hD

/-- Local semantic closure cannot refute supplied model data. This is
not a certificate for the universal raw-group RoleModel.StepAG target. -/
theorem RecSig.erasedClosure_nonrefutable (P : Premises4) {I : Type v}
    (M : Interp.{0}) (S : RecSig.{0, v} I) (hS : S.CodeDich)
    (hD : ∀ s k, (S.tel s k).DomainsDich) :
    ¬ (S.ErasedClosed M (S.erasedFamily M) → (Premises4 → False)) := by
  intro h
  exact h (S.erasedFamily_closed M P.c0 hS hD) P

end Rcic.F3.PSet
