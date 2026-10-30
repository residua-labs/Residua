import rcic.RcicF3PiProducer
import rcic.RcicF3PiFieldFixture

/-! Concrete Acc Nat.lt and unbounded W instances of every local producer
premise. Semantic construction only. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiProducerFixture
open PiFieldFixture

def accSig (R : Nat → Nat → Prop) : RecSig Nat where
  Sh := Nat
  Field := fun _ => PUnit
  depth := fun _ _ => 2
  tel := fun x _ => accTel R x
  out := id
  code := fun x f => ordPair (ord x) (f .unit)
  tag := fun z x => Equiv (pfst z) (ord x)
  tag_congr := fun _ _ h _ hx => (pfst_congr h).symm.trans hx
  code_tag := fun _ _ => pfst_pair
  code_congr := fun _ _ _ h => ordPair_congr Equiv.rfl (h .unit)

noncomputable def accTree (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    GT (accSig R).toPiSig.toGSig :=
  Acc.ndrec (C := fun _ => GT (accSig R).toPiSig.toGSig)
    (fun x _ ih => .sup x (fun p => ih (natOf p.2.1) (proofOf _ p.2.2.1))) h

theorem accTree_index (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    Equiv (pfst (decG (accSig R).toPiSig.toGSig (accTree R x h))) (ord x) := by
  cases h
  exact pfst_pair

theorem accTree_valid (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    ValidW (accSig R).toPiSig.toGSig (accTree R x h) := by
  induction h with
  | intro x hx ih =>
    apply ValidW.sup
    · intro p
      exact ih (natOf p.2.1) (proofOf _ p.2.2.1)
    · intro k p
      simpa only [RecSig.toPiSig, PiTel.flatten_unflatten] using
        accTree_index R (natOf p.1) (hx _ (proofOf _ p.2.1))

noncomputable def accArgs (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    (accSig R).Args x where
  trees := fun _ q r => accTree R (natOf q) (Acc.inv h (proofOf _ r))
  valid := fun _ _ _ => accTree_valid R _ _
  indexed := fun _ _ => accTree_index R _ _

/-- All producer premises are paid at each accessible point. -/
theorem acc_produced (R : Nat → Nat → Prop) (x : Nat) (h : Acc R x) :
    ∃ f : PUnit → PSet.{0},
      (∀ k, f k ∈ ((accSig R).tel x k).denote (accSig R).family) ∧
      (accSig R).code x f ∈ (accSig R).family x := by
  let a := accArgs R x h
  exact ⟨fun k => ((accSig R).tel x k).encode (a.values k),
    (accSig R).produce x a _ (fun _ => Equiv.rfl)⟩

theorem natLt_produced (x : Nat) :
    ∃ f : PUnit → PSet.{0},
      (∀ k, f k ∈ ((accSig Nat.lt).tel x k).denote (accSig Nat.lt).family) ∧
      (accSig Nat.lt).code x f ∈ (accSig Nat.lt).family x :=
  acc_produced Nat.lt x (Nat.lt_wfRel.wf.apply x)


def wSig : RecSig PUnit where
  Sh := Fn2Sh
  Field := PiW.Field
  depth := fun _ _ => 1
  tel := fun s k => match s with
    | .leaf => PEmpty.elim k
    | .node => wTel
  out := fun _ => .unit
  code := fun s f => match s with
    | .leaf => dataVal 0 []
    | .node => dataVal 1 [f .unit]
  tag := fun _ _ => True
  tag_congr := fun _ _ _ _ h => h
  code_tag := fun _ _ => trivial
  code_congr := by
    intro s f g h
    cases s with
    | leaf => exact Equiv.rfl
    | node => exact dataVal_congr 1 ⟨h .unit, trivial⟩

def wTree : GT Fn2GSig.{0} → GT wSig.toPiSig.toGSig
  | .sup .leaf _ => .sup .leaf (fun p => PEmpty.elim p.1)
  | .sup .node g => .sup .node (fun p => wTree (g p.2.1))

theorem wTree_decode (w : GT Fn2GSig.{0}) :
    Equiv (decG wSig.toPiSig.toGSig (wTree w)) (decG Fn2GSig w) := by
  induction w with
  | sup s g ih =>
    cases s with
    | leaf => exact Equiv.rfl
    | node => exact dataVal_congr 1 ⟨graphOf_congr ih, trivial⟩

theorem wTree_valid (w : GT Fn2GSig.{0}) : ValidW wSig.toPiSig.toGSig (wTree w) := by
  induction w with
  | sup s g ih =>
    cases s with
    | leaf =>
      exact ValidW.sup (S := wSig.toPiSig.toGSig) Fn2Sh.leaf _
        (fun p => PEmpty.elim p.1) (fun k => PEmpty.elim k)
    | node =>
      exact ValidW.sup (S := wSig.toPiSig.toGSig) Fn2Sh.node _
        (fun p => ih p.2.1) (fun _ _ => trivial)

def wArgs : wSig.Args .node where
  trees := fun _ q => wTree (fnDepth q)
  valid := fun _ q => wTree_valid (fnDepth q)
  indexed := fun _ _ => trivial

/-- Actual producer composition at height omega, not merely a leaf. -/
theorem w_produced : ∃ f : PUnit → PSet.{0},
    (∀ k, f k ∈ (wSig.tel .node k).denote wSig.family) ∧
    wSig.code .node f ∈ wSig.family .unit ∧
    wSig.code .node f ∉ gUnion.{0} := by
  let f := fun k => (wSig.tel .node k).encode (wArgs.values k)
  have hp := wSig.produce .node wArgs f (fun _ => Equiv.rfl)
  refine ⟨f, hp.1, hp.2, ?_⟩
  intro h
  change decG wSig.toPiSig.toGSig (wTree fnW) ∈ gUnion at h
  exact fnW_not_mem_union (mem_congr_left (wTree_decode fnW) h)

/-- A wrong child index fails within the genuine Nat.lt constructor domain. -/
theorem wrong_acc_index_refused :
    ¬ ∀ (q : FBr fnDom.{0}) (_r : FBr (proofDom (natOf q < 2))),
      (accSig Nat.lt).tag
        (decG (accSig Nat.lt).toPiSig.toGSig
          (accTree Nat.lt 0 (Nat.lt_wfRel.wf.apply 0))) (natOf q) := by
  intro h
  have he := h (fnCls 1) (Quotient.mk _ ⟨Nat.lt_succ_self 1⟩)
  have hc := (accTree_index Nat.lt 0 (Nat.lt_wfRel.wf.apply 0)).symm.trans he
  exact Nat.noConfusion (ord_inj hc)

end Rcic.F3.PSet.PiProducerFixture
