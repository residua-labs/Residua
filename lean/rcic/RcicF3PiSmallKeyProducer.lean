import rcic.RcicF3PiSmallStage

/-!
# Small trees whose complete indices depend on decoded fields

The branch topology is fixed by a small constructor shape. The complete
child and result indices may depend on every reconstructed recursive field.
Validity records those indices after decoding; it does not store large
recursive values in the constructor shape. Extensionality of the literal
index readers transports the reconstructed fields back to the supplied
fields. Only the supplied Choice3 chooses small trees.

This removes the fixed-index restriction of PiSmallProducer.Sig. It does
not compile admitted syntax to candidate-independent branch domains, and
it does not supply result-stage-one, two, or three signatures.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallKeyProducer
universe v w
open PiSmallCompile PiSmallField

structure Sig (I : Type v) (J : Type w) where
  Sh : Type 3
  Field : Sh → Type 3
  depth : (s : Sh) → Field s → Nat
  tel : (s : Sh) → (k : Field s) → RecTel.{3,w} J (depth s k)
  child : (s : Sh) → (Field s → PSet.{4}) → Field s → J → I
  out : (s : Sh) → (Field s → PSet.{4}) → I
  code : (s : Sh) → (Field s → PSet.{4}) → PSet.{4}
  child_congr : ∀ s f g, (∀ k, Equiv (f k) (g k)) →
    ∀ k j, child s f k j = child s g k j
  out_congr : ∀ s f g, (∀ k, Equiv (f k) (g k)) → out s f = out s g
  code_congr : ∀ s f g, (∀ k, Equiv (f k) (g k)) →
    Equiv (code s f) (code s g)

inductive Tree {I : Type v} {J : Type w} (S : Sig I J) : Type 3 where
  | sup (s : S.Sh)
      (g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S) : Tree S

noncomputable def decode {I : Type v} {J : Type w}
    (M : Interp.{4}) (S : Sig I J) : Tree S → PSet.{4}
  | .sup s g => S.code s (fun k => encode M (S.tel s k)
      ((S.tel s k).tel.unflatten (fun p => decode M S (g ⟨k,p⟩))))

noncomputable def fieldsOf {I : Type v} {J : Type w}
    (M : Interp.{4}) (S : Sig I J) (s : S.Sh)
    (g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S) :
    S.Field s → PSet.{4} :=
  fun k => encode M (S.tel s k)
    ((S.tel s k).tel.unflatten (fun p => decode M S (g ⟨k,p⟩)))

inductive Valid {I : Type v} {J : Type w}
    (M : Interp.{4}) (S : Sig I J) : I → Tree S → Prop where
  | sup (s : S.Sh)
      (g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S)
      (hg : ∀ k p,
        Valid M S (S.child s (fieldsOf M S s g) k ((S.tel s k).result p))
          (g ⟨k,p⟩)) :
      Valid M S (S.out s (fieldsOf M S s g)) (.sup s g)

noncomputable def family {I : Type v} {J : Type w}
    (M : Interp.{4}) (S : Sig I J) (i : I) : PSet.{4} :=
  mk (ULift.{4} {t : Tree S // Valid M S i t})
    (fun t => decode M S t.down.1)

def CodeDich {I : Type v} {J : Type w} (S : Sig I J) : Prop :=
  (∀ s f, Equiv (S.code s f) pempty) ∨
    (∀ s f, ¬ Equiv (S.code s f) pempty)

theorem family_dich {I : Type v} {J : Type w}
    (M : Interp.{4}) (S : Sig I J) (hS : CodeDich S) (i : I) :
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
def FieldsFit {I : Type v} {J : Type w}
    (M : Interp.{4}) (S : Sig I J) (X : I → PSet.{4})
    (s : S.Sh) (f : S.Field s → PSet.{4}) : Prop :=
  ∀ k, f k ∈ Ed M ((widen (S.tel s k)).erasedType M
    (fun j => X (S.child s f k j)))

theorem produce {I : Type v} {J : Type w}
    (M : Interp.{4}) (ch : Choice.{3}) (S : Sig I J)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (s : S.Sh) (f : S.Field s → PSet.{4})
    (hf : FieldsFit M S (family M S) s f) :
    S.code s f ∈ family M S (S.out s f) := by
  let r := fun k => read M (S.tel s k) (f k)
  have hr := fun k => read_spec M (S.tel s k) (hD s k)
    (fun j => family M S (S.child s f k j))
    (fun j => family_dich M S hS (S.child s f k j)) (hf k)
  have hex : ∀ k p, ∃ t : Tree S,
      Valid M S (S.child s f k ((S.tel s k).result p)) t ∧
        Equiv (decode M S t) ((S.tel s k).tel.flatten (r k) p) := by
    intro k p
    have hp := (PiTel.all_iff _ _ _).mp (hr k).1 p
    obtain ⟨⟨⟨t, ht⟩⟩, he⟩ := hp
    exact ⟨t, ht, he⟩
  let pick := fun k p => ch (α := ULift.{4} (Tree S))
    (fun t => Valid M S (S.child s f k ((S.tel s k).result p)) t.down ∧
      Equiv (decode M S t.down) ((S.tel s k).tel.flatten (r k) p))
    (let ⟨t, ht⟩ := hex k p; ⟨⟨t⟩, ht⟩)
  let g : ((k : S.Field s) × (S.tel s k).tel.Path) → Tree S :=
    fun p => (pick p.1 p.2).1.down
  have he : ∀ k, Equiv (fieldsOf M S s g k) (f k) := by
    intro k
    apply Equiv.trans (encode_congr M (S.tel s k) _ (r k) ?_) (hr k).2.symm
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

theorem cases_mem {I : Type v} {J : Type w}
    (M : Interp.{4}) (S : Sig I J) (hS : CodeDich S)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (i : I)
    {z : PSet.{4}} (hz : z ∈ family M S i) :
    ∃ (s : S.Sh) (f : S.Field s → PSet.{4}),
      FieldsFit M S (family M S) s f ∧ Equiv z (S.code s f) ∧
        S.out s f = i := by
  obtain ⟨⟨⟨t, ht⟩⟩, he⟩ := hz
  cases ht with
  | sup s g hg =>
    let v : (k : S.Field s) → PiTel.Value.{3,5}
        (S.tel s k).tel (fun _ => PSet.{4}) :=
      fun k => (S.tel s k).tel.unflatten (fun p => decode M S (g ⟨k,p⟩))
    have hr : ∀ k, Related (S.tel s k)
        (fun j => family M S (S.child s (fieldsOf M S s g) k j)) (v k) := by
      intro k
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      rw [show v k = (S.tel s k).tel.unflatten
        (fun p => decode M S (g ⟨k,p⟩)) from rfl, PiTel.flatten_unflatten]
      exact ⟨⟨⟨g ⟨k,p⟩, hg k p⟩⟩, Equiv.rfl⟩
    refine ⟨s, fieldsOf M S s g, ?_, he.symm, rfl⟩
    intro k
    exact encode_mem M (S.tel s k) (hD s k)
      (fun j => family M S (S.child s (fieldsOf M S s g) k j))
      (fun j => family_dich M S hS _) (v k) (hr k)

def Closed {I : Type v} {J : Type w}
    (M : Interp.{4}) (S : Sig I J) (X : I → PSet.{4}) : Prop :=
  ∀ s f, FieldsFit M S X s f → S.code s f ∈ X (S.out s f)

theorem family_iff {I : Type v} {J : Type w}
    (M : Interp.{4}) (ch : Choice.{3}) (S : Sig I J)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (i : I) (z : PSet.{4}) :
    z ∈ family M S i ↔ ∃ (s : S.Sh) (f : S.Field s → PSet.{4}),
      FieldsFit M S (family M S) s f ∧ Equiv z (S.code s f) ∧
        S.out s f = i := by
  constructor
  · exact cases_mem M S hS hD i
  · rintro ⟨s, f, hf, hz, hi⟩
    subst i
    exact mem_congr_left hz.symm (produce M ch S hS hD s f hf)

theorem family_least {I : Type v} {J : Type w}
    (M : Interp.{4}) (S : Sig I J)
    (hD : ∀ s k, (S.tel s k).DomainsDich) (X : I → PSet.{4})
    (hX : ∀ i, Dich (X i)) (h : Closed M S X) :
    ∀ i, Sub (family M S i) (X i) := by
  have key : ∀ i t, Valid M S i t → decode M S t ∈ X i := by
    intro i t ht
    induction ht with
    | sup s g hg ih =>
      apply h s (fieldsOf M S s g)
      intro k
      apply encode_mem M (S.tel s k) (hD s k)
        (fun j => X (S.child s (fieldsOf M S s g) k j)) (fun j => hX _)
      apply (PiTel.all_iff _ _ _).mpr
      intro p
      simpa only [PiTel.flatten_unflatten] using ih k p
  intro i z ⟨⟨⟨t, ht⟩⟩, he⟩
  exact mem_congr_left he (key i t ht)

theorem family_closed {I : Type v} {J : Type w}
    (P : Premises4) (M : Interp.{4}) (S : Sig I J)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich) :
    Closed M S (family M S) :=
  produce M P.c3 S hS hD

theorem decode_small {I : Type v} {J : Type w}
    (ch : Choice.{3}) (M : Interp.{4}) (S : Sig I J)
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : ∀ s f, (∀ k, Small.{3,4} (f k)) → Small.{3,4} (S.code s f))
    (t : Tree S) : Small.{3,4} (decode M S t) := by
  induction t with
  | sup s g ih =>
    apply hcode s
    intro k
    apply PiSmallStage.encode_small ch M (S.tel s k) (hD s k)
    intro p
    simpa only [PiTel.flatten_unflatten] using ih ⟨k,p⟩

theorem family_small {I : Type v} {J : Type w}
    (ch : Choice.{3}) (M : Interp.{4}) (S : Sig I J)
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : ∀ s f, (∀ k, Small.{3,4} (f k)) → Small.{3,4} (S.code s f))
    (i : I) : Small.{3,4} (family M S i) :=
  PiSmallStage.small_mk ch {t : Tree S // Valid M S i t}
    (fun t => decode M S t.1)
    (fun t => decode_small ch M S hD hcode t.1)

/-- The literal saturated-stage bound. No bound for W4 1, 2, or 3 is claimed. -/
theorem family_stage_four_plus {I : Type v} {J : Type w}
    (P : Premises4) (M : Interp.{4}) (S : Sig I J)
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : ∀ s f, (∀ k, Small.{3,4} (f k)) → Small.{3,4} (S.code s f))
    (i : I) (k : Nat) : family M S i ∈ W4 (k + 4) := by
  change family M S i ∈ univIn.{3,4}
  exact mem_univIn.{3,4}.mpr (family_small P.c3 M S hD hcode i)

/-- Decomposition carries the checked local closure and size composition. -/
theorem component {I : Type v} {J : Type w}
    (P : Premises4) (M : Interp.{4}) (S : Sig I J)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : ∀ s f, (∀ k, Small.{3,4} (f k)) → Small.{3,4} (S.code s f)) :
    Closed M S (family M S) ∧ ∀ i k, family M S i ∈ W4 (k + 4) :=
  ⟨family_closed P M S hS hD, family_stage_four_plus P M S hD hcode⟩

theorem component_nonrefutable {I : Type v} {J : Type w}
    (P : Premises4) (M : Interp.{4}) (S : Sig I J)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : ∀ s f, (∀ k, Small.{3,4} (f k)) → Small.{3,4} (S.code s f)) :
    ¬ ((Closed M S (family M S) ∧ ∀ i k, family M S i ∈ W4 (k + 4)) →
      (Premises4 → False)) :=
  fun h => h (component P M S hS hD hcode) P

end Rcic.F3.PSet.PiSmallKeyProducer
