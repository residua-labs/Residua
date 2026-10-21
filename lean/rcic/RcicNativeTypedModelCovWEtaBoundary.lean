import rcic.RcicNativeTypedModelCovWTypedBetaBoundary

/-!
# The inhabited old-model eta defect at native Nat successor

This module measures the unchanged `ApproxTW` and `ApproxTKW` relations.
Native `succ : Nat -> Nat` is eta-convertible to `fun x : Nat => succ x`.
The lambda observes the exact graph `.lam [([.bot], .spine 2 [.bot])]`,
strictly typed at an actual observation of its native arrow type. Native
successor cannot observe any lambda graph: forgetting to `ApproxT` and
using its rigid-constant inversion leaves only bottom or `.spine 2 []`.

The native eta rule is stated in its actual contraction direction, and
its symmetry is supplied separately. The closed counterexample bundles
include environment admission, context well-formedness, a realized finite
typed bottom valuation, both native endpoint typings, the observed arrow
code, and the nonbottom typed graph. There are no hypothetical premises,
K calls, index-guard failures, or dependencies on the new eta relation.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovUAudit TypedModelCovVAudit TypedModelCovTAudit
open TypedModelCovXAudit TypedModelAudit.TypingFin TypedModelCovWAudit
open TypedModelCovWTypedAudit

def covWEtaNatFn : Expr Nat := .const 2 []
def covWEtaNatExpand : Expr Nat :=
  .lam (.const 0 []) (.app (.const 2 []) (.bvar 0))
def covWEtaNatArrow : Expr Nat := covWTypedBetaNatArrow
def covWEtaNatGraph : CptT := .lam [([.bot], .spine 2 [.bot])]
def covWEtaNatArrowCode : CptT :=
  .pi (.spine 0 []) [([.bot], .spine 0 [])]

def covWEtaNatFn_ty (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ covWEtaNatFn covWEtaNatArrow :=
  hasTyT_natEnvU_succ n Γ

def covWEtaNatExpand_ty (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ covWEtaNatExpand covWEtaNatArrow :=
  .lam Γ (.const 0 []) (.succ .zero)
    (.app (.const 2 []) (.bvar 0)) (.const 0 [])
    (hasTyT_natEnvU_nat n Γ)
    (.app (.assumption (.const 0 []) :: Γ) (.const 2 []) (.bvar 0)
      (.const 0 []) (.const 0 [])
      (hasTyT_natEnvU_succ n (.assumption (.const 0 []) :: Γ))
      (.bvar (.assumption (.const 0 []) :: Γ) 0 (.const 0 []) rfl))

def covWEtaNatArrow_ty (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ covWEtaNatArrow
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  covWTypedBetaNatArrow_ty n Γ

/-- Native eta contracts the displayed lambda to successor. -/
def covWEtaNat_contract (n : Nat) (Γ : LCtx) :
    ConvT natEnvU n Γ covWEtaNatExpand covWEtaNatFn covWEtaNatArrow :=
  .eta Γ (.const 2 []) (.const 0 []) (.const 0 [])
    (hasTyT_natEnvU_succ n Γ)

/-- The opposite conversion is native symmetry of eta contraction. -/
def covWEtaNat_expand_conv (n : Nat) (Γ : LCtx) :
    ConvT natEnvU n Γ covWEtaNatFn covWEtaNatExpand covWEtaNatArrow :=
  .symm Γ covWEtaNatExpand covWEtaNatFn covWEtaNatArrow
    (covWEtaNat_contract n Γ)

theorem covWEtaNat_fn_raw (ρ : EnvT) :
    ApproxTW natEnvU ρ covWEtaNatFn (.spine 2 []) :=
  .const ρ 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ

/-- The exact nonempty-demand graph is already observed by the old lambda. -/
theorem covWEtaNat_expand_raw (ρ : EnvT) :
    ApproxTW natEnvU ρ covWEtaNatExpand covWEtaNatGraph := by
  refine .lam
    (.const ρ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)
    ?_ ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · exact ⟨([.bot], .spine 2 [.bot]), List.mem_singleton.mpr rfl,
      fun he => CptT.noConfusion he⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .appSpine
      (.const _ 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ)
      (.bot _ _)

/-- The type code is obtained by observing the actual native arrow. -/
theorem covWEtaNat_arrow_raw (ρ : EnvT) :
    ApproxTW natEnvU ρ covWEtaNatArrow covWEtaNatArrowCode := by
  refine .pi
    (.const ρ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat) ?_ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat

theorem covWEtaNat_fn_guarded (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKW natEnvU n Γ ρ covWEtaNatFn (.spine 2 []) :=
  .free (kFreeT_natEnvU _) (covWEtaNat_fn_raw ρ)

theorem covWEtaNat_expand_guarded (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKW natEnvU n Γ ρ covWEtaNatExpand covWEtaNatGraph :=
  .free (kFreeT_natEnvU _) (covWEtaNat_expand_raw ρ)

theorem covWEtaNat_arrow_guarded (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKW natEnvU n Γ ρ covWEtaNatArrow covWEtaNatArrowCode :=
  .free (kFreeT_natEnvU _) (covWEtaNat_arrow_raw ρ)

theorem covWEtaNat_arrow_not_prop : ¬ IsPropCT natEnvU covWEtaNatArrowCode := by
  intro h
  cases h with
  | pi _ hg =>
      exact not_isPropCT_natEnvU_nat_spine []
        (hg ([.bot], .spine 0 []) (List.mem_singleton.mpr rfl))

/-- Strict graph typing includes the actual singleton codomain coverage. -/
theorem covWEtaNat_graph_typed :
    CTyS natEnvU covWEtaNatGraph covWEtaNatArrowCode := by
  change CTyS natEnvU (.lam [([.bot], .spine 2 [.bot])])
    (.pi (.spine 0 []) [([.bot], .spine 0 [])])
  rw [CTyS]
  refine Or.inr ⟨_, rfl, covWEtaNat_arrow_not_prop, ?_, ?_, ?_⟩
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    exact ctyS_bot _
  · intro s hs t ht _
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp ht
    exact covWTypedBetaNat_compact_typed
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact Or.inr ⟨([.bot], .spine 0 []), List.mem_singleton.mpr rfl,
      fun _ hu => hu⟩

theorem covWEtaNat_graph_nonbottom : covWEtaNatGraph ≠ .bot :=
  fun he => CptT.noConfusion he

/-- The full old relation has only bottom or the rigid constant spine. -/
theorem covWEtaNat_old_shape {ρ : EnvT} {c : CptT}
    (h : ApproxT natEnvU ρ covWEtaNatFn c) :
    c = .bot ∨ c = .spine 2 [] :=
  approxT_rigid_const_inv rigidConst_natEnvU_succ h

/-- No lambda graph is available, independently of its row contents. -/
theorem covWEtaNat_old_no_lambda (ρ : EnvT) (rows : List (List CptT × CptT)) :
    ¬ ApproxT natEnvU ρ covWEtaNatFn (.lam rows) := by
  intro h
  rcases covWEtaNat_old_shape h with hb | hr
  · exact CptT.noConfusion hb
  · exact CptT.noConfusion hr

theorem covWEtaNat_raw_no_lambda (ρ : EnvT) (rows : List (List CptT × CptT)) :
    ¬ ApproxTW natEnvU ρ covWEtaNatFn (.lam rows) :=
  fun h => covWEtaNat_old_no_lambda ρ rows
    (approxTN_forget (approxTW_forget h))

theorem covWEtaNat_guarded_no_lambda (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (rows : List (List CptT × CptT)) :
    ¬ ApproxTKW natEnvU n Γ ρ covWEtaNatFn (.lam rows) :=
  fun h => covWEtaNat_old_no_lambda ρ rows
    (approxTK_forget (covW_forget_old h))

/-- Both endpoint syntax trees avoid the sole native Nat recursor. -/
theorem covWEtaNat_no_rec_occurrence :
    occursConst 3 covWEtaNatFn = false ∧
    occursConst 3 covWEtaNatExpand = false ∧
    occursConst 3 covWEtaNatArrow = false := by decide

theorem covWEtaNat_kFree :
    KFreeT natEnvU covWEtaNatFn ∧ KFreeT natEnvU covWEtaNatExpand ∧
    KFreeT natEnvU covWEtaNatArrow :=
  ⟨kFreeT_natEnvU _, kFreeT_natEnvU _, kFreeT_natEnvU _⟩

/-- All native and semantic premises of the closed eta comparison are
stored as evidence. The source is not claimed to be bottom-only. -/
structure CovWEtaNatFailureAt (n : Nat) (M : CtxModelT natEnvU) : Prop where
  envWf : Nonempty (EnvWfT natEnvU)
  ctxWf : Nonempty (CtxWfT natEnvU n [])
  realized : CovWRealized natEnvU n 3 [] EnvT.bot SubstT.id
  valuation : EnvTypedFinAtT M [] EnvT.bot
  coherence : CtxEnvM M [] EnvT.bot
  functionTy : Nonempty (HasTyT natEnvU n [] covWEtaNatFn covWEtaNatArrow)
  expansionTy : Nonempty (HasTyT natEnvU n [] covWEtaNatExpand covWEtaNatArrow)
  typeTy : Nonempty (HasTyT natEnvU n [] covWEtaNatArrow
    (.sort (.imax (.succ .zero) (.succ .zero))))
  contraction : Nonempty (ConvT natEnvU n []
    covWEtaNatExpand covWEtaNatFn covWEtaNatArrow)
  expansionConversion : Nonempty (ConvT natEnvU n []
    covWEtaNatFn covWEtaNatExpand covWEtaNatArrow)
  functionKFree : KFreeT natEnvU covWEtaNatFn
  expansionKFree : KFreeT natEnvU covWEtaNatExpand
  functionBot : M.Ap EnvT.bot covWEtaNatFn .bot
  functionRigid : M.Ap EnvT.bot covWEtaNatFn (.spine 2 [])
  expansionObservation : M.Ap EnvT.bot covWEtaNatExpand covWEtaNatGraph
  typeObservation : M.Ap EnvT.bot covWEtaNatArrow covWEtaNatArrowCode
  demand : CTyS natEnvU covWEtaNatGraph covWEtaNatArrowCode
  nonbottom : covWEtaNatGraph ≠ .bot
  functionNoGraph : ∀ ρ, ¬ M.Ap ρ covWEtaNatFn covWEtaNatGraph

theorem CovWEtaNatFailureAt.refutes {n : Nat} {M : CtxModelT natEnvU}
    (h : CovWEtaNatFailureAt n M)
    {R : Expr Nat → Expr Nat → Prop} (hR : R covWEtaNatFn covWEtaNatExpand) :
    ¬ covWTyped_antiReductionAt natEnvU n [] M R := by
  intro hback
  exact h.functionNoGraph EnvT.bot
    (hback EnvT.bot covWEtaNatFn covWEtaNatExpand covWEtaNatArrow
      (.imax (.succ .zero) (.succ .zero)) covWEtaNatGraph covWEtaNatArrowCode
      h.envWf h.ctxWf h.valuation h.functionTy h.expansionTy h.typeTy
      hR h.expansionObservation h.typeObservation h.demand h.nonbottom)

theorem covWEtaNat_raw_failure (n : Nat) :
    CovWEtaNatFailureAt n (⟨ApproxTW natEnvU⟩ : CtxModelT natEnvU) where
  envWf := ⟨natEnvUWfT⟩
  ctxWf := ⟨.nil⟩
  realized := covW_realized_nil _ _ _
  valuation := covWTyped_raw_bot_valuation natEnvU []
  coherence := fun _ _ hv => Option.noConfusion hv
  functionTy := ⟨covWEtaNatFn_ty n []⟩
  expansionTy := ⟨covWEtaNatExpand_ty n []⟩
  typeTy := ⟨covWEtaNatArrow_ty n []⟩
  contraction := ⟨covWEtaNat_contract n []⟩
  expansionConversion := ⟨covWEtaNat_expand_conv n []⟩
  functionKFree := covWEtaNat_kFree.1
  expansionKFree := covWEtaNat_kFree.2.1
  functionBot := .bot _ _
  functionRigid := covWEtaNat_fn_raw EnvT.bot
  expansionObservation := covWEtaNat_expand_raw EnvT.bot
  typeObservation := covWEtaNat_arrow_raw EnvT.bot
  demand := covWEtaNat_graph_typed
  nonbottom := covWEtaNat_graph_nonbottom
  functionNoGraph := fun ρ => covWEtaNat_raw_no_lambda ρ _

theorem covWEtaNat_guarded_failure (n : Nat) :
    CovWEtaNatFailureAt n (⟨ApproxTKW natEnvU n []⟩ : CtxModelT natEnvU) where
  envWf := ⟨natEnvUWfT⟩
  ctxWf := ⟨.nil⟩
  realized := covW_realized_nil _ _ _
  valuation := covWTyped_guarded_bot_valuation natEnvU n []
  coherence := fun _ _ hv => Option.noConfusion hv
  functionTy := ⟨covWEtaNatFn_ty n []⟩
  expansionTy := ⟨covWEtaNatExpand_ty n []⟩
  typeTy := ⟨covWEtaNatArrow_ty n []⟩
  contraction := ⟨covWEtaNat_contract n []⟩
  expansionConversion := ⟨covWEtaNat_expand_conv n []⟩
  functionKFree := covWEtaNat_kFree.1
  expansionKFree := covWEtaNat_kFree.2.1
  functionBot := .bot _ _ _
  functionRigid := covWEtaNat_fn_guarded n [] EnvT.bot
  expansionObservation := covWEtaNat_expand_guarded n [] EnvT.bot
  typeObservation := covWEtaNat_arrow_guarded n [] EnvT.bot
  demand := covWEtaNat_graph_typed
  nonbottom := covWEtaNat_graph_nonbottom
  functionNoGraph := fun ρ => covWEtaNat_guarded_no_lambda n [] ρ _

theorem covWEtaNat_no_raw_conversion_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTW natEnvU⟩ : CtxModelT natEnvU)
      (fun e e' => Nonempty (ConvT natEnvU n [] e e' covWEtaNatArrow)) :=
  (covWEtaNat_raw_failure n).refutes ⟨covWEtaNat_expand_conv n []⟩

theorem covWEtaNat_no_guarded_conversion_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTKW natEnvU n []⟩ : CtxModelT natEnvU)
      (fun e e' => Nonempty (ConvT natEnvU n [] e e' covWEtaNatArrow)) :=
  (covWEtaNat_guarded_failure n).refutes ⟨covWEtaNat_expand_conv n []⟩

/-- The source, expanded graph, native type, and realizer coexist at one
finite information stage. Universe-parameter arity remains arbitrary. -/
theorem covWEtaNat_same_stage (n : Nat) :
    CovWRealized natEnvU n 3 [] EnvT.bot SubstT.id ∧
    ApproxTKWStage natEnvU n 3 [] EnvT.bot covWEtaNatFn (.spine 2 []) ∧
    ApproxTKWStage natEnvU n 3 [] EnvT.bot covWEtaNatExpand covWEtaNatGraph ∧
    ApproxTKWStage natEnvU n 3 [] EnvT.bot covWEtaNatArrow covWEtaNatArrowCode :=
  ⟨covW_realized_nil _ _ _,
    ⟨covWEtaNat_fn_guarded n [] EnvT.bot,
      by simp [covTObservationBudget, covWEtaNatGraph, covWEtaNatArrowCode]⟩,
    ⟨covWEtaNat_expand_guarded n [] EnvT.bot,
      by simp [covTObservationBudget, covWEtaNatGraph, covWEtaNatArrowCode]⟩,
    ⟨covWEtaNat_arrow_guarded n [] EnvT.bot,
      by simp [covTObservationBudget, covWEtaNatGraph, covWEtaNatArrowCode]⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_BOUNDARY_ROOTS
#print axioms covWEtaNatFn
#print axioms covWEtaNatExpand
#print axioms covWEtaNatArrow
#print axioms covWEtaNatGraph
#print axioms covWEtaNatArrowCode
#print axioms covWEtaNatFn_ty
#print axioms covWEtaNatExpand_ty
#print axioms covWEtaNatArrow_ty
#print axioms covWEtaNat_contract
#print axioms covWEtaNat_expand_conv
#print axioms covWEtaNat_fn_raw
#print axioms covWEtaNat_expand_raw
#print axioms covWEtaNat_arrow_raw
#print axioms covWEtaNat_fn_guarded
#print axioms covWEtaNat_expand_guarded
#print axioms covWEtaNat_arrow_guarded
#print axioms covWEtaNat_arrow_not_prop
#print axioms covWEtaNat_graph_typed
#print axioms covWEtaNat_graph_nonbottom
#print axioms covWEtaNat_old_shape
#print axioms covWEtaNat_old_no_lambda
#print axioms covWEtaNat_raw_no_lambda
#print axioms covWEtaNat_guarded_no_lambda
#print axioms covWEtaNat_no_rec_occurrence
#print axioms covWEtaNat_kFree
#print axioms CovWEtaNatFailureAt
#print axioms CovWEtaNatFailureAt.refutes
#print axioms covWEtaNat_raw_failure
#print axioms covWEtaNat_guarded_failure
#print axioms covWEtaNat_no_raw_conversion_antiReduction
#print axioms covWEtaNat_no_guarded_conversion_antiReduction
#print axioms covWEtaNat_same_stage
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_ETA_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWEtaAudit
