import rcic.RcicF3PiSmallFieldAt

/-!
# Field-dependent indices with an explicit small-tree universe

Shapes, recursive branch addresses, and trees live in u. Decoded values
live in max(u+1,v); complete child/result indices may be larger. Validity
retains the actual decoded fields. Readback and key transport are unchanged
from PiSmallKeyProducer, and only Choice u selects trees or representatives.

The exact W4 wrappers select u=0,1,2,3 and the corresponding Premises4
choice field. No lower-stage bound is inferred from Small3. Construction
of one candidate-independent admitted-data signature remains open.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallKeyProducerAt
universe u v w x
open PiSmallRecursive (widen)
open PiSmallFieldAt

structure Sig (I : Type w) (J : Type x) where
  Sh : Type u
  Field : Sh → Type u
  depth : (s : Sh) → Field s → Nat
  tel : (s : Sh) → (k : Field s) → RecTel.{u,x} J (depth s k)
  child : (s : Sh) → (Field s → PSet.{max (u+1) v}) → Field s → J → I
  out : (s : Sh) → (Field s → PSet.{max (u+1) v}) → I
  code : (s : Sh) → (Field s → PSet.{max (u+1) v}) → PSet.{max (u+1) v}
  child_congr : ∀ s f g, (∀ k, Equiv (f k) (g k)) →
    ∀ k j, child s f k j = child s g k j
  out_congr : ∀ s f g, (∀ k, Equiv (f k) (g k)) → out s f = out s g
  code_congr : ∀ s f g, (∀ k, Equiv (f k) (g k)) →
    Equiv (code s f) (code s g)

inductive Tree {I : Type w} {J : Type x} (S : Sig.{u,v,w,x} I J) : Type u where
  | sup (s : S.Sh)
      (g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S) : Tree S

noncomputable def decode {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J) : Tree S → PSet.{max (u+1) v}
  | .sup s g => S.code s (fun k => encode.{u,v,x} M (S.tel s k)
      ((S.tel s k).tel.unflatten (fun p => decode M S (g ⟨k,p⟩))))

noncomputable def fieldsOf {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J) (s : S.Sh)
    (g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S) :
    S.Field s → PSet.{max (u+1) v} :=
  fun k => encode.{u,v,x} M (S.tel s k)
    ((S.tel s k).tel.unflatten (fun p => decode M S (g ⟨k,p⟩)))

inductive Valid {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J) : I → Tree S → Prop where
  | sup (s : S.Sh)
      (g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S)
      (hg : ∀ k p,
        Valid M S (S.child s (fieldsOf M S s g) k ((S.tel s k).result p))
          (g ⟨k,p⟩)) :
      Valid M S (S.out s (fieldsOf M S s g)) (.sup s g)

noncomputable def family {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J) (i : I) : PSet.{max (u+1) v} :=
  mk (ULift.{max (u+1) v} {t : Tree S // Valid M S i t})
    (fun t => decode M S t.down.1)

def CodeDich {I : Type w} {J : Type x} (S : Sig.{u,v,w,x} I J) : Prop :=
  (∀ s f, Equiv (S.code s f) pempty) ∨
    (∀ s f, ¬ Equiv (S.code s f) pempty)

theorem family_dich {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J) (hS : CodeDich S) (i : I) :
    Dich (family M S i) := by
  rcases hS with h | h
  · apply Or.inl
    intro z ⟨⟨⟨t, ht⟩⟩, he⟩
    cases ht with
    | sup s g hg => exact he.symm.trans (h s _)
  · apply Or.inr
    intro ⟨⟨⟨t, ht⟩⟩, he⟩
    cases ht with
    | sup s g hg => exact h s _ he

/-- The field and its complete child-key reader use the same supplied f.
The key reader is not evaluated at a placeholder or erased field tuple. -/
def FieldsFit {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J) (X : I → PSet.{max (u+1) v})
    (s : S.Sh) (f : S.Field s → PSet.{max (u+1) v}) : Prop :=
  ∀ k, f k ∈ Ed M ((widen.{u,v,x} (S.tel s k)).erasedType M
    (fun j => X (S.child s f k j)))

theorem produce {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (ch : Choice.{u}) (S : Sig.{u,v,w,x} I J)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (s : S.Sh) (f : S.Field s → PSet.{max (u+1) v})
    (hf : FieldsFit M S (family M S) s f) :
    S.code s f ∈ family M S (S.out s f) := by
  let r := fun k => PiSmallFieldAt.read.{u,v,x} M (S.tel s k) (f k)
  have hr := fun k => read_spec.{u,v,x} M (S.tel s k) (hD s k)
    (fun j => family M S (S.child s f k j))
    (fun j => family_dich M S hS (S.child s f k j)) (hf k)
  have hex : ∀ k p, ∃ t : Tree S,
      Valid M S (S.child s f k ((S.tel s k).result p)) t ∧
        Equiv (decode M S t) ((S.tel s k).tel.flatten (r k) p) := by
    intro k p
    have hp := (PiTel.all_iff _ _ _).mp (hr k).1 p
    obtain ⟨⟨⟨t, ht⟩⟩, he⟩ := hp
    exact ⟨t, ht, he⟩
  let pick := fun k p => ch (α := ULift.{u+1} (Tree S))
    (fun t => Valid M S (S.child s f k ((S.tel s k).result p)) t.down ∧
      Equiv (decode M S t.down) ((S.tel s k).tel.flatten (r k) p))
    (let ⟨t, ht⟩ := hex k p; ⟨⟨t⟩, ht⟩)
  let g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S :=
    fun p => (pick p.1 p.2).1.down
  have he : ∀ k, Equiv (fieldsOf M S s g k) (f k) := by
    intro k
    apply Equiv.trans (encode_congr.{u,v,x} M (S.tel s k) _ (r k) ?_) (hr k).2.symm
    intro p
    simpa only [PiTel.flatten_unflatten] using (pick k p).2.2
  have hg : ∀ k p,
      Valid M S (S.child s (fieldsOf M S s g) k ((S.tel s k).result p))
        (g ⟨k,p⟩) := by
    intro k p
    rw [S.child_congr s (fieldsOf M S s g) f he]
    exact (pick k p).2.1
  have hv : Valid M S (S.out s f) (.sup s g) := by
    rw [← S.out_congr s (fieldsOf M S s g) f he]
    exact Valid.sup s g hg
  exact ⟨⟨⟨.sup s g, hv⟩⟩, S.code_congr s (fieldsOf M S s g) f he⟩

theorem cases_mem {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J) (hS : CodeDich S)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (i : I)
    {z : PSet.{max (u+1) v}} (hz : z ∈ family M S i) :
    ∃ (s : S.Sh) (f : S.Field s → PSet.{max (u+1) v}),
      FieldsFit M S (family M S) s f ∧ Equiv z (S.code s f) ∧
        S.out s f = i := by
  obtain ⟨⟨⟨t, ht⟩⟩, he⟩ := hz
  cases ht with
  | sup s g hg =>
    let v : (k : S.Field s) → PiTel.Value.{u,max (u+1) v + 1}
        (S.tel s k).tel (fun _ => PSet.{max (u+1) v}) :=
      fun k => (S.tel s k).tel.unflatten (fun p => decode M S (g ⟨k,p⟩))
    have hr : ∀ k, Related.{u,v,x} (S.tel s k)
        (fun j => family M S (S.child s (fieldsOf M S s g) k j)) (v k) := by
      intro k
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      rw [show v k = (S.tel s k).tel.unflatten
        (fun p => decode M S (g ⟨k,p⟩)) from rfl, PiTel.flatten_unflatten]
      exact ⟨⟨⟨g ⟨k,p⟩, hg k p⟩⟩, Equiv.rfl⟩
    refine ⟨s, fieldsOf M S s g, ?_, he.symm, rfl⟩
    intro k
    exact encode_mem.{u,v,x} M (S.tel s k) (hD s k)
      (fun j => family M S (S.child s (fieldsOf M S s g) k j))
      (fun j => family_dich M S hS _) (v k) (hr k)

def Closed {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J) (X : I → PSet.{max (u+1) v}) : Prop :=
  ∀ s f, FieldsFit M S X s f → S.code s f ∈ X (S.out s f)

theorem family_iff {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (ch : Choice.{u}) (S : Sig.{u,v,w,x} I J)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (i : I) (z : PSet.{max (u+1) v}) :
    z ∈ family M S i ↔ ∃ (s : S.Sh) (f : S.Field s → PSet.{max (u+1) v}),
      FieldsFit M S (family M S) s f ∧ Equiv z (S.code s f) ∧
        S.out s f = i := by
  constructor
  · exact cases_mem M S hS hD i
  · rintro ⟨s, f, hf, hz, hi⟩
    subst i
    exact mem_congr_left hz.symm (produce M ch S hS hD s f hf)

theorem family_least {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (X : I → PSet.{max (u+1) v})
    (hX : ∀ i, Dich (X i)) (h : Closed M S X) :
    ∀ i, Sub (family M S i) (X i) := by
  have key : ∀ i t, Valid M S i t → decode M S t ∈ X i := by
    intro i t ht
    induction ht with
    | sup s g hg ih =>
      apply h s (fieldsOf M S s g)
      intro k
      apply encode_mem.{u,v,x} M (S.tel s k) (hD s k)
        (fun j => X (S.child s (fieldsOf M S s g) k j)) (fun j => hX _)
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      simpa only [PiTel.flatten_unflatten] using ih k p
  intro i z ⟨⟨⟨t, ht⟩⟩, he⟩
  exact mem_congr_left he (key i t ht)

theorem family_closed {I : Type w} {J : Type x}
    (ch : Choice.{u}) (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich) :
    Closed M S (family M S) :=
  produce M ch S hS hD

theorem decode_small {I : Type w} {J : Type x}
    (ch : Choice.{u}) (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J)
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : ∀ s f, (∀ k, Small.{u,max (u+1) v} (f k)) → Small.{u,max (u+1) v} (S.code s f))
    (t : Tree S) : Small.{u,max (u+1) v} (decode M S t) := by
  induction t with
  | sup s g ih =>
    apply hcode s
    intro k
    apply PiSmallFieldAt.encode_small.{u,v,x} ch M (S.tel s k) (hD s k)
    intro p
    simpa only [PiTel.flatten_unflatten] using ih ⟨k,p⟩

theorem family_small {I : Type w} {J : Type x}
    (ch : Choice.{u}) (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J)
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : ∀ s f, (∀ k, Small.{u,max (u+1) v} (f k)) → Small.{u,max (u+1) v} (S.code s f))
    (i : I) : Small.{u,max (u+1) v} (family M S i) :=
  PiSmallStage.small_mk.{u,max (u+1) v} ch {t : Tree S // Valid M S i t}
    (fun t => decode M S t.1)
    (fun t => decode_small ch M S hD hcode t.1)

def DataCode {I : Type w} {J : Type x} (S : Sig.{u,v,w,x} I J) : Prop :=
  ∀ s f, ¬ Equiv (S.code s f) pempty

def CodeStage {I : Type w} {J : Type x} (S : Sig.{u,v,w,x} I J)
    (W : PSet.{max (u+1) v}) : Prop :=
  ∀ s f, (∀ k, f k ∈ W) → S.code s f ∈ W

theorem family_data {I : Type w} {J : Type x}
    (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J)
    (hS : DataCode S) (i : I) : ¬ pempty ∈ family M S i := by
  intro ⟨⟨⟨t, ht⟩⟩, he⟩
  cases ht with
  | sup s g hg => exact hS s _ he

theorem family_mem_univ {I : Type w} {J : Type x}
    (ch : Choice.{u}) (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J)
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : CodeStage S (univIn.{u,v})) (i : I) :
    family M S i ∈ univIn.{u,v} := by
  apply mem_univIn.{u,v}.mpr
  apply family_small ch M S hD
  intro s f hf
  exact mem_univIn.{u,v}.mp (hcode s f (fun k => mem_univIn.{u,v}.mpr (hf k)))

/-- Closure and the literal data admissibility clauses at this signature's
selected small universe. The choice operation is only at that universe. -/
theorem component {I : Type w} {J : Type x}
    (ch : Choice.{u}) (M : Interp.{max (u+1) v}) (S : Sig.{u,v,w,x} I J)
    (hS : DataCode S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : CodeStage S (univIn.{u,v})) :
    Closed M S (family M S) ∧
      ∀ i, family M S i ∈ univIn.{u,v} ∧ ¬ pempty ∈ family M S i :=
  ⟨family_closed ch M S (Or.inr hS) hD,
    fun i => ⟨family_mem_univ ch M S hD hcode i, family_data M S hS i⟩⟩

theorem component_stage_one {I : Type w} {J : Type x}
    (P : Premises4) (M : Interp.{4}) (S : Sig.{0,4,w,x} I J)
    (hS : DataCode S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : CodeStage S (W4 1)) :
    Closed M S (family M S) ∧ ∀ i, family M S i ∈ W4 1 ∧ ¬ pempty ∈ family M S i :=
  component.{0,4,w,x} P.c0 M S hS hD hcode

theorem component_stage_two {I : Type w} {J : Type x}
    (P : Premises4) (M : Interp.{4}) (S : Sig.{1,4,w,x} I J)
    (hS : DataCode S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : CodeStage S (W4 2)) :
    Closed M S (family M S) ∧ ∀ i, family M S i ∈ W4 2 ∧ ¬ pempty ∈ family M S i :=
  component.{1,4,w,x} P.c1 M S hS hD hcode

theorem component_stage_three {I : Type w} {J : Type x}
    (P : Premises4) (M : Interp.{4}) (S : Sig.{2,4,w,x} I J)
    (hS : DataCode S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : CodeStage S (W4 3)) :
    Closed M S (family M S) ∧ ∀ i, family M S i ∈ W4 3 ∧ ¬ pempty ∈ family M S i :=
  component.{2,4,w,x} P.c2 M S hS hD hcode

theorem component_stage_four_plus {I : Type w} {J : Type x}
    (P : Premises4) (M : Interp.{4}) (S : Sig.{3,4,w,x} I J)
    (hS : DataCode S) (hD : ∀ s k, (S.tel s k).DomainsDich) (k : Nat)
    (hcode : CodeStage S (W4 (k + 4))) :
    Closed M S (family M S) ∧
      ∀ i, family M S i ∈ W4 (k + 4) ∧ ¬ pempty ∈ family M S i :=
  component.{3,4,w,x} P.c3 M S hS hD hcode

/-- The generic component's non-refutability is conditional on the literal
signature premises; the separate fixture supplies all of them from P. -/
theorem component_nonrefutable {I : Type w} {J : Type x}
    (P : Premises4) (ch : Choice.{u}) (M : Interp.{max (u+1) v})
    (S : Sig.{u,v,w,x} I J) (hS : DataCode S)
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : CodeStage S (univIn.{u,v})) :
    ¬ ((Closed M S (family M S) ∧
      ∀ i, family M S i ∈ univIn.{u,v} ∧ ¬ pempty ∈ family M S i) →
        (Premises4 → False)) :=
  fun h => h (component ch M S hS hD hcode) P

end Rcic.F3.PSet.PiSmallKeyProducerAt
