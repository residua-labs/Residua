import rcic.RcicF3PiSmallField
/-!
# Small indexed trees with large R-CIC values

Constructor shapes and branch domains are small. The decoder produces
actual universe-4 values; Choice3 selects only small trees. This is a
semantic signature construction, not yet a raw inductive-group compiler.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallProducer
universe v
open PiSmallCompile PiSmallField

structure Sig (I : Type v) where
  Sh : Type 3
  Field : Sh → Type 3
  depth : (s : Sh) → Field s → Nat
  tel : (s : Sh) → (k : Field s) → RecTel.{3,v} I (depth s k)
  out : Sh → I
  code : (s : Sh) → (Field s → PSet.{4}) → PSet.{4}
  code_congr : ∀ s f g, (∀ k, Equiv (f k) (g k)) → Equiv (code s f) (code s g)

inductive Tree {I : Type v} (S : Sig I) : Type 3 where
  | sup (s : S.Sh) (g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S) : Tree S

def decode {I : Type v} (M : Interp.{4}) (S : Sig I) : Tree S → PSet.{4}
  | .sup s g => S.code s (fun k => encode M (S.tel s k)
      ((S.tel s k).tel.unflatten (fun p => decode M S (g ⟨k, p⟩))))

inductive Valid {I : Type v} (S : Sig I) : I → Tree S → Prop where
  | sup (s : S.Sh) (g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S)
      (hg : ∀ k p, Valid S ((S.tel s k).result p) (g ⟨k,p⟩)) :
      Valid S (S.out s) (.sup s g)

def family {I : Type v} (M : Interp.{4}) (S : Sig I) (i : I) : PSet.{4} :=
  mk (ULift.{4} {w : Tree S // Valid S i w}) (fun w => decode M S w.down.1)

def CodeDich {I : Type v} (S : Sig I) : Prop :=
  (∀ s f, Equiv (S.code s f) pempty) ∨ (∀ s f, ¬Equiv (S.code s f) pempty)

theorem family_dich {I : Type v} (M : Interp.{4}) (S : Sig I)
    (hS : CodeDich S) (i : I) : Dich (family M S i) := by
  rcases hS with h | h
  · apply Or.inl
    intro z ⟨⟨⟨w, hw⟩⟩, he⟩
    cases hw with
    | sup s g hg => exact he.symm.trans (h s _)
  · apply Or.inr
    intro ⟨⟨⟨w, hw⟩⟩, he⟩
    cases hw with
    | sup s g hg => exact h s _ he


theorem produce {I : Type v} (M : Interp.{4}) (ch : Choice.{3}) (S : Sig I)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (s : S.Sh) (f : S.Field s → PSet.{4})
    (hf : ∀ k, f k ∈ Ed M ((widen (S.tel s k)).erasedType M (family M S))) :
    S.code s f ∈ family M S (S.out s) := by
  let r := fun k => read M (S.tel s k) (f k)
  have hr := fun k => read_spec M (S.tel s k) (hD s k)
    (family M S) (family_dich M S hS) (hf k)
  have hex : ∀ k p, ∃ w : Tree S,
      Valid S ((S.tel s k).result p) w ∧
        Equiv (decode M S w) ((S.tel s k).tel.flatten (r k) p) := by
    intro k p
    have hp := (PiTel.all_iff _ _ _).mp (hr k).1 p
    obtain ⟨⟨⟨w, hw⟩⟩, he⟩ := hp
    exact ⟨w, hw, he⟩
  let pick := fun k p => ch (α := ULift.{4} (Tree S))
    (fun w => Valid S ((S.tel s k).result p) w.down ∧
      Equiv (decode M S w.down) ((S.tel s k).tel.flatten (r k) p))
    (let ⟨w, hw⟩ := hex k p; ⟨⟨w⟩, hw⟩)
  let g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S :=
    fun p => (pick p.1 p.2).1.down
  have hv : Valid S (S.out s) (.sup s g) :=
    Valid.sup s g (fun k p => (pick k p).2.1)
  refine ⟨⟨⟨.sup s g, hv⟩⟩, S.code_congr s _ f ?_⟩
  intro k
  apply Equiv.trans (encode_congr M (S.tel s k) _ (r k) ?_) (hr k).2.symm
  intro p
  simpa only [PiTel.flatten_unflatten] using (pick k p).2.2


theorem cases_mem {I : Type v} (M : Interp.{4}) (S : Sig I)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich) (i : I)
    {z : PSet.{4}} (hz : z ∈ family M S i) :
    ∃ (s : S.Sh) (f : S.Field s → PSet.{4}),
      (∀ k, f k ∈ Ed M ((widen (S.tel s k)).erasedType M (family M S))) ∧
      Equiv z (S.code s f) ∧ S.out s = i := by
  obtain ⟨⟨⟨w, hw⟩⟩, he⟩ := hz
  cases hw with
  | sup s g hg =>
    let v : (k : S.Field s) → PiTel.Value.{3,5}
        (S.tel s k).tel (fun _ => PSet.{4}) := fun k => (S.tel s k).tel.unflatten
      (fun p => decode M S (g ⟨k,p⟩))
    have hr : ∀ k, Related (S.tel s k) (family M S) (v k) := by
      intro k
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      rw [show v k = (S.tel s k).tel.unflatten
        (fun p => decode M S (g ⟨k,p⟩)) from rfl, PiTel.flatten_unflatten]
      exact ⟨⟨⟨g ⟨k,p⟩, hg k p⟩⟩, Equiv.rfl⟩
    exact ⟨s, fun k => encode M (S.tel s k) (v k),
      fun k => encode_mem M (S.tel s k) (hD s k) _ (family_dich M S hS) _ (hr k),
      he.symm, rfl⟩


def Closed {I : Type v} (M : Interp.{4}) (S : Sig I) (X : I → PSet.{4}) : Prop :=
  ∀ s f, (∀ k, f k ∈ Ed M ((widen (S.tel s k)).erasedType M X)) → S.code s f ∈ X (S.out s)

theorem family_iff {I : Type v} (M : Interp.{4}) (ch : Choice.{3}) (S : Sig I)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich) (i : I) (z : PSet.{4}) :
    z ∈ family M S i ↔ ∃ (s : S.Sh) (f : S.Field s → PSet.{4}),
      (∀ k, f k ∈ Ed M ((widen (S.tel s k)).erasedType M (family M S))) ∧
      Equiv z (S.code s f) ∧ S.out s = i := by
  constructor
  · exact cases_mem M S hS hD i
  · rintro ⟨s, f, hf, hz, hi⟩
    subst i
    exact mem_congr_left hz.symm (produce M ch S hS hD s f hf)


theorem family_least {I : Type v} (M : Interp.{4}) (S : Sig I)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (X : I → PSet.{4})
    (hX : ∀ i, Dich (X i)) (h : Closed M S X) :
    ∀ i, Sub (family M S i) (X i) := by
  have key : ∀ i w, Valid S i w → decode M S w ∈ X i := by
    intro i w hw
    induction hw with
    | sup s g hg ih =>
      apply h s _
      intro k
      apply encode_mem M (S.tel s k) (hD s k) X hX
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      simpa only [PiTel.flatten_unflatten] using ih k p
  intro i z ⟨⟨⟨w, hw⟩⟩, he⟩
  exact mem_congr_left he (key i w hw)


/-- Elementary projection; only the already supplied Choice3 is used. -/
theorem family_closed {I : Type v} (P : Premises4) (M : Interp.{4}) (S : Sig I)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich) :
    Closed M S (family M S) := by
  exact produce M P.c3 S hS hD


/-- Local semantic closure only; not universal RoleModel.StepAG. -/
theorem closure_nonrefutable {I : Type v} (P : Premises4) (M : Interp.{4}) (S : Sig I)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich) :
    ¬ (Closed M S (family M S) → (Premises4 → False)) := by
  intro h
  exact h (family_closed P M S hS hD) P

end Rcic.F3.PSet.PiSmallProducer
