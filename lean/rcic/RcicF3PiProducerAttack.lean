import rcic.RcicF3PiProducerFixture

/-! Fresh attacks exercise the producer itself, including a three-binder
indexed field, hidden graphs and arbitrary numerical offsets.
No raw StepAG integration is asserted. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiProducerAttack
open PiFieldFixture PiProducerFixture

/-- A leaf at each index, and a constructor with three dependent binders. -/
def deepField : Option Nat → Type
  | .some _ => PEmpty
  | .none => PUnit

def deepSig : RecSig Nat where
  Sh := Option Nat
  Field := deepField
  depth := fun _ _ => 3
  tel := fun s k => match s with
    | .some _ => PEmpty.elim k
    | .none => nestedTel
  out := fun s => s.getD 0
  code := fun s f => ordPair (ord (s.getD 0)) (match s with
    | .some _ => dataVal 0 []
    | .none => dataVal 1 [f .unit])
  tag := fun z i => Equiv (pfst z) (ord i)
  tag_congr := fun _ _ h _ hx => (pfst_congr h).symm.trans hx
  code_tag := fun _ _ => pfst_pair
  code_congr := by
    intro s f g h
    apply ordPair_congr Equiv.rfl
    cases s with
    | some _ => exact Equiv.rfl
    | none => exact dataVal_congr 1 ⟨h .unit, trivial⟩

def deepLeaf (i : Nat) : GT deepSig.toPiSig.toGSig :=
  .sup (.some i) (fun p => PEmpty.elim p.1)

theorem deepLeaf_valid (i : Nat) : ValidW deepSig.toPiSig.toGSig (deepLeaf i) :=
  ValidW.sup (S := deepSig.toPiSig.toGSig) (.some i) _ (fun p => PEmpty.elim p.1) (fun k => PEmpty.elim k)

def deepArgs : deepSig.Args .none where
  trees := fun _ q _ r => deepLeaf (natOf q + natOf r)
  valid := fun _ q _ r => deepLeaf_valid (natOf q + natOf r)
  indexed := fun _ _ => pfst_pair

/-- All premises of the producer are inhabited at genuine depth three,
including a result index varying with two arguments. -/
theorem deep_produced : ∃ f : PUnit → PSet.{0},
    (∀ k, f k ∈ (deepSig.tel .none k).denote deepSig.family) ∧
    deepSig.code .none f ∈ deepSig.family 0 := by
  exact ⟨_, deepSig.produce .none deepArgs
    (fun k => (deepSig.tel .none k).encode (deepArgs.values k)) (fun _ => Equiv.rfl)⟩

/-- Beta/delta/let-hidden raw graphs pass the GENERAL product producer,
using the existing explicit ambient premise. -/
theorem hidden_w_produced (P : Premises4) : ∃ f : PUnit → PSet.{0},
    wSig.code .node f ∈ wSig.family .unit ∧ wSig.code .node f ∉ gUnion.{0} := by
  let f := (fun g : PUnit → PSet.{0} => let h := g; h)
    (fun k => (wSig.tel .node k).encode (wArgs.values k))
  have hp := wSig.produce .node wArgs f (fun _ => Equiv.rfl)
  refine ⟨f, wSig.produce_of_mem P.c0 .node f hp.1, ?_⟩
  intro h
  change decG wSig.toPiSig.toGSig (wTree fnW) ∈ gUnion at h
  exact fnW_not_mem_union (mem_congr_left (wTree_decode fnW) h)

/-- Hidden relabellings preserve actual producer inhabitants at every offset. -/
theorem shifted_acc_produced (offset x : Nat) :
    let R := (fun r : Nat → Nat → Prop => let q := r; q)
      (fun a b => a + offset < b + offset)
    ∃ f : PUnit → PSet.{0},
      (∀ k, f k ∈ ((accSig R).tel x k).denote (accSig R).family) ∧
      (accSig R).code x f ∈ (accSig R).family x := by
  have hx : Acc (fun a b => a + offset < b + offset) x := by
    induction Nat.lt_wfRel.wf.apply x with
    | intro y _ ih =>
      exact Acc.intro y (fun z hz => ih z (Nat.lt_of_add_lt_add_right hz))
  exact acc_produced _ x hx
end Rcic.F3.PSet.PiProducerAttack
