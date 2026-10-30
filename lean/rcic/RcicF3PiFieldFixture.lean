import rcic.RcicF3PiField
import rcic.RcicF3PiAcc
import rcic.RcicF3PiW

/-!
# Non-vacuity and adversarial cases for the dependent field interpretation

The Acc field has a Nat binder followed by a dependent proof binder.
The W field ranges over infinitely many children. These test the actual
set-product logical relation, beyond Type-level telescope flattening.
Semantic fixtures only: no raw admission/StepAG assertion.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PiFieldFixture

/-- Recover a Nat label from its extensional domain class. -/
def natOf : FBr fnDom.{0} → Nat :=
  Quotient.lift (fun n => n.down) (fun _ _ h => ord_inj h)

/-- A proof domain has one extensional value exactly when the proposition holds. -/
def proofDom (p : Prop) : PSet.{0} := mk (PLift p) (fun _ => pempty)

/-- A class in the proof domain supplies the proof, without a decision oracle. -/
theorem proofOf (p : Prop) (q : FBr (proofDom p)) : p :=
  Quotient.inductionOn q (fun i => i.down)

/-- The recursive result depends on the first of two dependent arguments. -/
def accTel (R : Nat → Nat → Prop) (x : Nat) : RecTel Nat 2 :=
  .pi fnDom (fun q => .pi (proofDom (R (natOf q) x)) (fun _ => .ret (natOf q)))

/-- Accessibility constructs every child in the dependent field. -/
noncomputable def accAssignment (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    PiTel.Value.{0, 1} (accTel R x).tel (fun _ => PSet.{0}) :=
  fun q r => decG (PiAcc.sig R).toGSig
    (PiAcc.tree R (natOf q) (Acc.inv h (proofOf _ r)))

/-- Both the child guard and its result index hold at every dependent path. -/
theorem acc_related (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    (accTel R x).Rel (PiAcc.fiber R) (accAssignment R x h) := by
  intro q r
  exact mem_sep.mpr ⟨⟨_, PiAcc.tree_valid R _ (Acc.inv h (proofOf _ r))⟩,
    PiAcc.tree_index R _ (Acc.inv h (proofOf _ r)), Equiv.refl _⟩

/-- Every Nat.lt Acc field is inhabited in the actual dependent product. -/
theorem accNatLt_product (x : Nat) :
    ∃ f, f ∈ (accTel Nat.lt x).denote (PiAcc.fiber Nat.lt) := by
  let h := Nat.lt_wfRel.wf.apply x
  exact ⟨_, (accTel Nat.lt x).encode_mem _ _ (acc_related Nat.lt x h)⟩

/-- One genuinely infinitely branching recursive W field. -/
def wTel : RecTel PUnit 1 := .pi fnDom (fun _ => .ret .unit)

/-- The children have unbounded finite heights. -/
def wAssignment : PiTel.Value.{0, 1} wTel.tel (fun _ => PSet.{0}) :=
  fun q => decG PiW.sig.toGSig (PiW.embed (fnDepth q))

/-- All children survive in the W family, including the unbounded assignment. -/
theorem w_product : wTel.encode wAssignment ∈ wTel.denote (fun _ => gSet PiW.sig.toGSig) := by
  apply wTel.encode_mem
  intro q
  exact ⟨⟨PiW.embed (fnDepth q), PiW.embed_valid _⟩, Equiv.refl _⟩

/-- Three dependent binders with a result varying in two arguments. -/
def nestedTel : RecTel Nat 3 :=
  .pi fnDom (fun q => .pi (proofDom (natOf q < natOf q + 1))
    (fun _ => .pi fnDom (fun r => .ret (natOf q + natOf r))))

/-- No binder or dependent result index is erased. -/
theorem nested_product : ∃ f, f ∈ nestedTel.denote (fun i => singleton (ord i)) := by
  apply (nestedTel.inhabited_iff (fun i => singleton (ord i))).mpr
  exact ⟨fun q _ r => ord (natOf q + natOf r),
    fun _ _ _ => mem_singleton.mpr Equiv.rfl⟩

/-- Constant zero cannot satisfy the varying result fibre. -/
theorem wrong_index_refused :
    ¬ (RecTel.pi fnDom (fun q => RecTel.ret (natOf q))).Rel
      (fun i => singleton (ord i)) (fun _ => ord 0) := by
  intro h
  have he : Equiv (ord 0 : PSet.{0}) (ord 1) := mem_singleton.mp (h (fnCls 1))
  exact Nat.noConfusion (ord_inj he)

/-- Empty-domain child tests alone are vacuous; the total-graph conjunct
still refuses a nonempty junk field. -/
theorem empty_children_not_sufficient :
    let t : RecTel Nat 1 := .pi pempty (fun _ => .ret 0)
    t.Rel (fun _ => pempty) (t.read junk₁) ∧
      junk₁ ∉ t.denote (fun _ => pempty) := by
  constructor
  · intro q
    refine Quotient.inductionOn q ?_
    intro i
    exact PEmpty.elim i
  · intro hf
    have hg := isFuncOnDep_of_mem_piSet
      (fun a b e => classFiber_congr pempty (fun _ => pempty) (a := a) (a' := b) e) hf
    obtain ⟨_, ⟨i, _⟩, _, _, _⟩ := hg.2.1 pempty
      (mem_singleton.mpr Equiv.rfl : pempty ∈ junk₁)
    exact PEmpty.elim i

end Rcic.F3.PSet.PiFieldFixture
