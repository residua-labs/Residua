import rcic.RcicF8DViaSSupply
import rcic.RcicF8JTransViaPins
import rcic.RcicF8JLocalStoredPins

/-!
Actual source D runs under genuine ins/sub/subLet stacks. These pins retain
whole outputs and the actual emitted producer/DTile. Existing J trans and
LOCAL-STORED controls remain live imports. W-DX-VIAS's answered domain is the
canonical source read via #7205's exact stored-tail lookup; its open is
nontrivial-stack origin transport. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.DViaS.Pins
open Rcic.Syn PEqTProofFront

def roots (Γ : LCtx) : List (Jd emptyEnv 0) :=
  [.cv (.irr Γ P p q (P_ty Γ) (p_ty Γ) (q_ty Γ))]

def producer (Γ : LCtx) : EvPar (roots Γ) Γ p q P :=
  literalIrrProducer (P_ty Γ) (p_ty Γ) (q_ty Γ)

def left (Γ : LCtx) : EvParStar (roots Γ) Γ p q P :=
  .tail (producer Γ) (.refl (producer Γ).rightTy)

def right (Γ : LCtx) : EvParStar (roots Γ) Γ p p P :=
  .refl (literalIrrPayload (P_ty Γ) (p_ty Γ) (q_ty Γ)).leftTy

theorem input_nonreflexive : p ≠ q := IrrPins.nonidentity

/-- Explicit expected whole sigma: no target expressions or typings occur. -/
def expected (Γ : LCtx) :
    Σ' d : Expr Nat, EvParStar (roots Γ) Γ q d P × EvParStar (roots Γ) Γ p d P :=
  ⟨q, .refl (producer Γ).rightTy,
    .trans (.tail (producer Γ) (.refl (producer Γ).rightTy))
      (.refl (producer Γ).rightTy)⟩

def subLetCtx : LCtx :=
  [.assumption (.bvar 0), .letBinding (.sort (.succ .zero)) (.sort .zero)]

def subLetHv : HasTyT emptyEnv 0 (substRemove (.sort .zero) 1 subLetCtx)
    (lift 0 1 (.sort .zero)) (lift 0 1 (.sort (.succ .zero))) := .sort _ _

def subLetVia : CtxWfViaS emptyEnv 0 subLetCtx :=
  .subLet 1 rfl subLetHv (.ofWf depthTargetWf)

theorem subLet_action : subLetVia.σ.apply (.bvar 1) = .sort .zero := rfl
theorem sub_action : depthViaS.σ.apply (.bvar 1) = .sort .zero := rfl
theorem sub_target_differs : depthViaS.target ≠ depthCtx := by intro h; cases h
theorem subLet_target_differs : subLetVia.target ≠ subLetCtx := by intro h; cases h

theorem sub_output (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcViaS EnvWfT.empty su depthViaS (left depthCtx) (right depthCtx) =
      expected depthCtx := rfl

theorem subLet_output (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcViaS EnvWfT.empty su subLetVia (left subLetCtx) (right subLetCtx) =
      expected subLetCtx := rfl

/-- Two nonreflexive inputs force the actual proof-index table row. -/
def tableStep (Γ : LCtx) : DStep (roots Γ) Γ q q P :=
  .base (proofIndexJoin (literalIrrPayload (P_ty Γ) (p_ty Γ) (q_ty Γ))
    (producer Γ).rightTy)

def tableExpected (Γ : LCtx) :
    Σ' d : Expr Nat, EvParStar (roots Γ) Γ q d P × EvParStar (roots Γ) Γ q d P :=
  ⟨q, .trans (tableStep Γ).star1 (.refl (producer Γ).rightTy),
    .refl (producer Γ).rightTy⟩

theorem sub_table_emitter (su : F8A2Support.SortUnique emptyEnv 0) :
    (dStepDiamondViaS EnvWfT.empty su depthViaS
      (.base (producer depthCtx)) (.base (producer depthCtx))).left =
      DOpt.step (tableStep depthCtx) := rfl

theorem subLet_table_emitter (su : F8A2Support.SortUnique emptyEnv 0) :
    (dStepDiamondViaS EnvWfT.empty su subLetVia
      (.base (producer subLetCtx)) (.base (producer subLetCtx))).left =
      DOpt.step (tableStep subLetCtx) := rfl

theorem sub_table_output (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcViaS EnvWfT.empty su depthViaS (left depthCtx) (left depthCtx) =
      tableExpected depthCtx := rfl

theorem subLet_table_output (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcViaS EnvWfT.empty su subLetVia (left subLetCtx) (left subLetCtx) =
      tableExpected subLetCtx := rfl

/-- The input bundles are exactly the original stars, independently of hv. -/
theorem input_bundle (Γ : LCtx) :
    (left Γ).leaves ++ (right Γ).leaves =
      [Jd.ty (P_ty Γ), Jd.ty (p_ty Γ), Jd.ty (q_ty Γ),
        Jd.ty (q_ty Γ), Jd.ty (p_ty Γ)] := rfl

theorem sub_no_replacement_leaf :
    Jd.ty depthHv ∉ (left depthCtx).leaves ++ (right depthCtx).leaves := by
  rw [input_bundle]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro h
  rcases h with h | h | h | h | h <;> cases h

theorem subLet_no_replacement_leaf :
    Jd.ty subLetHv ∉ (left subLetCtx).leaves ++ (right subLetCtx).leaves := by
  rw [input_bundle]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro h
  rcases h with h | h | h | h | h <;> cases h

theorem source_leaf_contract (su : F8A2Support.SortUnique emptyEnv 0)
    {Γ : LCtx} (v : CtxWfViaS emptyEnv 0 Γ) :
    ∀ ℓ ∈ (dProcViaS EnvWfT.empty su v (left Γ) (right Γ)).2.1.leaves ++
      (dProcViaS EnvWfT.empty su v (left Γ) (right Γ)).2.2.leaves,
      ∃ k ∈ (left Γ).leaves ++ (right Γ).leaves, SubEq ℓ k :=
  dContractViaS EnvWfT.empty su (roots Γ) v (left Γ) (right Γ)

/-- Existing nonreflexive J trans pins now run through the canonical object. -/
theorem ins_whole_output (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcViaS EnvWfT.empty su J5aVia.Pins.via.toS
      J5a.Pins.first.valley.right J5a.Pins.second.valley.left = J5a.Pins.groundD :=
  (DProofVia.dProc_eq_dProcViaS EnvWfT.empty su J5aVia.Pins.via _ _ _ _).symm.trans
    (J5aVia.Pins.actual_source_D su)

open DTilePins in
def piVia : CtxWfViaS emptyEnv 0 [] :=
  .ins (.assumption (.sort .zero)) 0
    (.ofWf (.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)))

open DTilePins
def piClosing (su : F8A2Support.SortUnique emptyEnv 0) :=
  structPiJoinViaS EnvWfT.empty su piVia pinStructPiPayload pinStructPiPayload

def piStep (su : F8A2Support.SortUnique emptyEnv 0) :
    DStep [pinPiRoot] [] (.pi pinDomR (.bvar 0)) (.pi pinDomR (.bvar 0))
      (.sort (.imax (.succ (.max .zero .zero)) .zero)) :=
  .base (.structPi (piClosing su))

theorem pi_actual_emitter (su : F8A2Support.SortUnique emptyEnv 0) :
    (dStepDiamondViaS EnvWfT.empty su piVia
      (.base (.structPi pinStructPiPayload)) (.base (.structPi pinStructPiPayload))).left =
      DOpt.step (piStep su) := rfl

def piInput : EvParStar [pinPiRoot] [] (.pi pinDomL (.bvar 0))
    (.pi pinDomR (.bvar 0)) (.sort (.imax (.succ (.max .zero .zero)) .zero)) :=
  .tail (.structPi pinStructPiPayload) (.refl (EvPar.structPi pinStructPiPayload).rightTy)

theorem pi_full_output (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcViaS EnvWfT.empty su piVia piInput piInput =
      ⟨.pi pinDomR (.bvar 0),
        .trans (piStep su).star1 (.refl (EvPar.structPi pinStructPiPayload).rightTy),
        .refl (EvPar.structPi pinStructPiPayload).rightTy⟩ := rfl

theorem pi_leaf_contract (su : F8A2Support.SortUnique emptyEnv 0) :
    ∀ ℓ ∈ (dProcViaS EnvWfT.empty su piVia piInput piInput).2.1.leaves ++
      (dProcViaS EnvWfT.empty su piVia piInput piInput).2.2.leaves,
      ∃ k ∈ piInput.leaves ++ piInput.leaves, SubEq ℓ k :=
  dContractViaS EnvWfT.empty su [pinPiRoot] piVia piInput piInput

def piTile (su : F8A2Support.SortUnique emptyEnv 0) : DTile [pinPiRoot] :=
  (piStep su).toDTile J5a.Pins.cl J5a.Pins.ss piInput.leaves

theorem pi_same_step_tile (su : F8A2Support.SortUnique emptyEnv 0) :
    (piTile su).step = (EvPar.structPi (piClosing su)).val J5a.Pins.cl J5a.Pins.ss := rfl

/-- Conditional soundness alone admits the vacuous supplier. -/
def noneSupply : ∀ R : List (Jd emptyEnv 0), DProcViaSP R :=
  fun _ {_ _ _ _ _} _ _ _ => none

theorem none_contract : DContractViaSP noneSupply := by
  intro R Γ a b c T v s₁ s₂ out hout
  cases hout

theorem positive_sub_coverage (su : F8A2Support.SortUnique emptyEnv 0) :
    d1ViaSP EnvWfT.empty su (roots depthCtx) depthViaS (left depthCtx) (right depthCtx) =
      some (expected depthCtx) := rfl

theorem none_fails_coverage :
    noneSupply (roots depthCtx) depthViaS (left depthCtx) (right depthCtx) ≠
      some (expected depthCtx) := by intro h; cases h

end Rcic.Declarative.F8Measure.DViaS.Pins

#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.roots
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.producer
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.left
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.right
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.input_nonreflexive
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.expected
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.subLetCtx
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.subLetHv
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.subLetVia
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.subLet_action
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.sub_action
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.sub_target_differs
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.subLet_target_differs
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.sub_output
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.subLet_output
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.input_bundle
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.sub_no_replacement_leaf
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.subLet_no_replacement_leaf
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.source_leaf_contract
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.ins_whole_output
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.piVia
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.piClosing
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.piStep
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.pi_actual_emitter
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.piInput
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.pi_full_output
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.pi_leaf_contract
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.piTile
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.pi_same_step_tile
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.noneSupply
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.none_contract
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.positive_sub_coverage
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.none_fails_coverage

#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.tableStep
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.tableExpected
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.sub_table_emitter
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.subLet_table_emitter
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.sub_table_output
#print axioms Rcic.Declarative.F8Measure.DViaS.Pins.subLet_table_output
