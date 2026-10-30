import rcic.RcicF3PiTel

/-!
# An indexed accessibility fixture for dependent Pi branches

The recursive field at `x` is `forall y, R y x -> child y`: two binders,
including a dependent proof domain. The guard requires the decoded child
to carry index `y`. The code carries index `x` and its decoded children.
This is a semantic fixture, not a typed R-CIC environment or
a `StepAG` producer. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PiAcc

/-- The two dependent binders of an accessibility constructor field. -/
def tel (R : Nat → Nat → Prop) (x : Nat) : PiTel.{0} 2 :=
  .cons Nat (fun y => .cons (PLift (R y x)) (fun _ => .nil))

/-- The child-index guard is invariant under extensional equality. -/
def sig (R : Nat → Nat → Prop) : PiSig.{0} where
  Sh := Nat
  Field := fun _ => PUnit
  depth := fun _ _ => 2
  tel := fun x _ => tel R x
  code := fun x f => ordPair (ord x) (mk (tel R x).Path ((tel R x).flatten (f .unit)))
  ok := fun x f => ∀ p, Equiv (pfst ((tel R x).flatten (f .unit) p)) (ord p.1)
  code_congr := by
    intro x f g h
    apply ordPair_congr Equiv.rfl
    exact ext (fun z => ⟨fun ⟨p, hp⟩ => ⟨p, (h .unit p).symm.trans hp⟩,
      fun ⟨p, hp⟩ => ⟨p, (h .unit p).trans hp⟩⟩)
  ok_congr := fun _ _ _ h hf p => (pfst_congr (h .unit p)).symm.trans (hf p)

/-- An accessible point supplies a tree without selecting any witnesses. -/
noncomputable def tree (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) : GT (sig R).toGSig :=
  Acc.ndrec (C := fun _ => GT (sig R).toGSig)
    (fun x _ ih => .sup x (fun p => ih p.2.1 p.2.2.1.down)) h

/-- Decoding preserves the root's index. -/
theorem tree_index (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    Equiv (pfst (decG (sig R).toGSig (tree R x h))) (ord x) := by
  cases h
  exact pfst_pair

/-- Every child has the required index and recursively satisfies the guard. -/
theorem tree_valid (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    ValidW (sig R).toGSig (tree R x h) := by
  induction h with
  | intro x hx ih =>
    apply ValidW.sup
    · intro p
      exact ih p.2.1 p.2.2.1.down
    · intro p
      simpa only [PiSig.toGSig, PiTel.flatten_unflatten] using
        tree_index R p.1 (hx p.1 p.2.1.down)

/-- The index guard rules out trees at inaccessible points. -/
theorem valid_accessible (R : Nat → Nat → Prop) (w : GT (sig R).toGSig)
    (hw : ValidW (sig R).toGSig w) (x : Nat)
    (hx : Equiv (pfst (decG (sig R).toGSig w)) (ord x)) : Acc R x := by
  induction hw generalizing x with
  | sup s g hg hok ih =>
    have hs : s = x := ord_inj (pfst_pair.symm.trans hx)
    subst x
    apply Acc.intro
    intro y hy
    apply ih ⟨.unit, ⟨y, ⟨⟨hy⟩, PUnit.unit⟩⟩⟩ y
    simpa only [PiSig.toGSig, PiTel.flatten_unflatten] using
      hok ⟨y, ⟨⟨hy⟩, PUnit.unit⟩⟩

/-- The semantic family is the index fibre of decoded guarded trees. -/
def fiber (R : Nat → Nat → Prop) (x : Nat) : PSet.{0} :=
  sep (fun z => Equiv (pfst z) (ord x)) (gSet (sig R).toGSig)

/-- The family has an element exactly at accessible points. -/
theorem fiber_inhabited_iff (R : Nat → Nat → Prop) (x : Nat) :
    (∃ z, z ∈ fiber R x) ↔ Acc R x := by
  constructor
  · intro ⟨z, hz⟩
    obtain ⟨w, hw, _⟩ := mem_sep.mp hz
    exact valid_accessible R w.1 w.2 x hw
  · intro h
    exact ⟨decG (sig R).toGSig (tree R x h),
      mem_sep.mpr ⟨⟨tree R x h, tree_valid R x h⟩, tree_index R x h, Equiv.rfl⟩⟩

/-- Every natural number has a semantic accessibility inhabitant for `<`. -/
theorem natLt_inhabited (x : Nat) : ∃ z, z ∈ fiber Nat.lt x := by
  exact (fiber_inhabited_iff Nat.lt x).mpr (Nat.lt_wfRel.wf.apply x)

/-- A self-loop cannot acquire a semantic inhabitant by ignoring the guard. -/
theorem selfLoop_empty (x : Nat) : ¬ ∃ z, z ∈ fiber (fun a b => a = b) x := by
  intro h
  have ha := (fiber_inhabited_iff (fun a b => a = b) x).mp h
  clear h
  induction ha with
  | intro y _ ih => exact ih y rfl

end Rcic.F3.PSet.PiAcc
