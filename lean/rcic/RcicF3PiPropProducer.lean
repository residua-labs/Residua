import rcic.RcicF3PiEraseField
/-! Proof-valued indexed closure with arbitrary ambient telescope domains.
Validity is an inductive proposition; the proof fibre is its truth set.
Constructor closure, exact equation and leastness use no choice input and
do not impose a domain smallness condition. Raw signature extraction and
universal group closure are separate. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiPropProducer
universe u v w
structure Sig (I : Type v) where
  Sh : Type w
  Field : Sh → Type w
  depth : (s : Sh) → Field s → Nat
  tel : (s : Sh) → (k : Field s) → RecTel.{u,v} I (depth s k)
  out : Sh → I
inductive Valid {I : Type v} (S : Sig.{u,v,w} I) : I → Prop where
  | sup (s : S.Sh) (hg : ∀ k p, Valid S ((S.tel s k).result p)) : Valid S (S.out s)
def family {I : Type v} (S : Sig.{u,v,w} I) (i : I) : PSet.{u} := tv (Valid S i)
theorem family_iff {I : Type v} (S : Sig.{u,v,w} I) (i : I) (z : PSet.{u}) :
    z ∈ family S i ↔ Valid S i ∧ Equiv z pempty := by
  exact mem_tv

theorem family_dich {I : Type v} (S : Sig.{u,v,w} I) (i : I) : Dich (family S i) := by
  exact Or.inl (fun _ h => (family_iff S i _).mp h |>.2)

theorem produce {I : Type v} (M : Interp.{u}) (S : Sig.{u,v,w} I)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (s : S.Sh) (f : S.Field s → PSet.{u})
    (hf : ∀ k, f k ∈ Ed M ((S.tel s k).erasedType M (family S))) :
    pempty ∈ family S (S.out s) := by
  apply (family_iff S (S.out s) pempty).mpr
  refine ⟨Valid.sup s ?_, Equiv.rfl⟩
  intro k p
  have hr := (S.tel s k).erasedRead_spec M (hD s k) (family S) (family_dich S) (hf k)
  exact ((family_iff S _ _).mp ((PiTel.all_iff _ _ _).mp hr.1 p)).1

/-- Closure of a proof interpretation, with no small-domain or choice premise. -/
def Closed {I : Type v} (M : Interp.{u}) (S : Sig.{u,v,w} I)
    (X : I → PSet.{u}) : Prop :=
  ∀ (s : S.Sh) (f : S.Field s → PSet.{u}),
    (∀ k, f k ∈ Ed M ((S.tel s k).erasedType M X)) → pempty ∈ X (S.out s)
theorem family_least {I : Type v} (M : Interp.{u}) (S : Sig.{u,v,w} I)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (X : I → PSet.{u})
    (hX : ∀ i, Dich (X i)) (h : Closed M S X) :
    ∀ i, Sub (family S i) (X i) := by
  have key : ∀ i, Valid S i → pempty ∈ X i := by
    intro i hi
    induction hi with
    | sup s hg ih =>
      let v : (k : S.Field s) → PiTel.Value.{u,u+1}
          (S.tel s k).tel (fun _ => PSet.{u}) :=
        fun k => (S.tel s k).tel.unflatten (fun _ => pempty)
      apply h s (fun k => (S.tel s k).erasedEncode M (v k))
      intro k
      apply (S.tel s k).erasedEncode_mem M (hD s k) X hX
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      simpa only [v, PiTel.flatten_unflatten] using ih k p
  intro i z hz
  obtain ⟨hi, he⟩ := (family_iff S i z).mp hz
  exact mem_congr_left he.symm (key i hi)
theorem family_equation {I : Type v} (M : Interp.{u}) (S : Sig.{u,v,w} I)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (i : I) (z : PSet.{u}) :
    z ∈ family S i ↔ ∃ (s : S.Sh) (f : S.Field s → PSet.{u}),
      (∀ k, f k ∈ Ed M ((S.tel s k).erasedType M (family S))) ∧
      Equiv z pempty ∧ S.out s = i := by
  constructor
  · intro hz
    obtain ⟨hi, he⟩ := (family_iff S i z).mp hz
    cases hi with
    | sup s hg =>
      let v : (k : S.Field s) → PiTel.Value.{u,u+1}
          (S.tel s k).tel (fun _ => PSet.{u}) :=
        fun k => (S.tel s k).tel.unflatten (fun _ => pempty)
      refine ⟨s, fun k => (S.tel s k).erasedEncode M (v k), ?_, he, rfl⟩
      intro k
      apply (S.tel s k).erasedEncode_mem M (hD s k) (family S) (family_dich S)
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      rw [show v k = (S.tel s k).tel.unflatten (fun _ => pempty) from rfl,
        PiTel.flatten_unflatten]
      exact (family_iff S _ _).mpr ⟨hg k p, Equiv.rfl⟩
  · rintro ⟨s, f, hf, hz, hi⟩
    rw [← hi]
    exact mem_congr_left hz.symm (produce M S hD s f hf)

theorem family_closed {I : Type v} (M : Interp.{u}) (S : Sig.{u,v,w} I)
    (hD : ∀ s k, (S.tel s k).DomainsDich) : Closed M S (family S) := by
  exact produce M S hD

end Rcic.F3.PSet.PiPropProducer
