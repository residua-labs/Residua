import rcic.RcicNativeTypedModelCovWTypedAntiReduction
import rcic.RcicNativeTypedModelCovWRevealed

/-!
# Typed beta and let observation boundaries without K

The closed native source `((fun f : Nat -> Nat => f zero) succ)` takes
one literal CK2 beta step to `succ zero`. Both terms have native type Nat.
The reduct has the nonbottom compact `.spine 2 [.bot]`, strictly typed at
the observed Nat code `.spine 0 []`, but every raw or guarded observation
of the source is bottom. The corresponding let source has the same failure.

The obstruction is the binder's demand typing: a Pi domain permits only
bottom or lambda compacts, while native succ has only bottom or its rigid
spine compact. Every argument demand actually met by succ is therefore
bottom, which cannot supply an application observation for the body.
No K step, recursor occurrence, or failed index guard participates.

Both failures retain native argument typing, the finite-joint typed bottom
valuation, an actual closed realizer, and an observed type code. Their
explicit matching normal constructor reduct excludes a normalization or
matching-head interpretation of the negative result. Proofs compose landed
typing rules and observation inversions. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovUAudit TypedModelCovVAudit TypedModelCovTAudit
open TypedModelCovXAudit TypedModelAudit.TypingFin TypedModelCovWAudit

def covWTypedBetaNatArrow : Expr Nat := .pi (.const 0 []) (.const 0 [])
def covWTypedBetaNatBody : Expr Nat := .app (.bvar 0) (.const 1 [])
def covWTypedBetaNatSource : Expr Nat :=
  .app (.lam covWTypedBetaNatArrow covWTypedBetaNatBody) (.const 2 [])
def covWTypedBetaNatLet : Expr Nat :=
  .letE covWTypedBetaNatArrow (.const 2 []) covWTypedBetaNatBody
def covWTypedBetaNatTarget : Expr Nat := .app (.const 2 []) (.const 1 [])
def covWTypedBetaNatCpt : CptT := .spine 2 [.bot]

def covWTypedBetaNatArrow_ty (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ covWTypedBetaNatArrow
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ (.const 0 []) (.succ .zero) (.const 0 []) (.succ .zero)
    (hasTyT_natEnvU_nat n Γ)
    (hasTyT_natEnvU_nat n (.assumption (.const 0 []) :: Γ))

def covWTypedBetaNatBody_ty (n : Nat) :
    HasTyT natEnvU n [.assumption covWTypedBetaNatArrow]
      covWTypedBetaNatBody (.const 0 []) :=
  .app _ _ _ (.const 0 []) (.const 0 [])
    (.bvar _ 0 _ rfl) (hasTyT_natEnvU_zero n _)

def covWTypedBetaNatLetBody_ty (n : Nat) :
    HasTyT natEnvU n [.letBinding covWTypedBetaNatArrow (.const 2 [])]
      covWTypedBetaNatBody (.const 0 []) :=
  .app _ _ _ (.const 0 []) (.const 0 [])
    (.bvar _ 0 _ rfl) (hasTyT_natEnvU_zero n _)

def covWTypedBetaNatSource_ty (n : Nat) :
    HasTyT natEnvU n [] covWTypedBetaNatSource (.const 0 []) :=
  .app [] _ _ covWTypedBetaNatArrow (.const 0 [])
    (.lam [] covWTypedBetaNatArrow (.imax (.succ .zero) (.succ .zero))
      covWTypedBetaNatBody (.const 0 [])
      (covWTypedBetaNatArrow_ty n []) (covWTypedBetaNatBody_ty n))
    (hasTyT_natEnvU_succ n [])

def covWTypedBetaNatLet_ty (n : Nat) :
    HasTyT natEnvU n [] covWTypedBetaNatLet (.const 0 []) :=
  .letE [] covWTypedBetaNatArrow (.imax (.succ .zero) (.succ .zero))
    (.const 2 []) (.const 0 []) covWTypedBetaNatBody
    (covWTypedBetaNatArrow_ty n []) (hasTyT_natEnvU_succ n [])
    (covWTypedBetaNatLetBody_ty n)

def covWTypedBetaNatTarget_ty (n : Nat) :
    HasTyT natEnvU n [] covWTypedBetaNatTarget (.const 0 []) :=
  .app [] _ _ _ _ (hasTyT_natEnvU_succ n []) (hasTyT_natEnvU_zero n [])

def covWTypedBetaNat_conv (n : Nat) :
    ConvT natEnvU n [] covWTypedBetaNatSource covWTypedBetaNatTarget (.const 0 []) :=
  .beta [] covWTypedBetaNatArrow covWTypedBetaNatBody (.const 2 []) (.const 0 [])
    (.imax (.succ .zero) (.succ .zero))
    (covWTypedBetaNatArrow_ty n []) (covWTypedBetaNatBody_ty n)
    (hasTyT_natEnvU_succ n [])

theorem covWTypedBetaNat_step (n : Nat) :
    WhStepCK2 natEnvU n [] covWTypedBetaNatSource covWTypedBetaNatTarget :=
  .ctx (.beta covWTypedBetaNatArrow covWTypedBetaNatBody (.const 2 []))

theorem covWTypedBetaNat_let_step (n : Nat) :
    WhStepCK2 natEnvU n [] covWTypedBetaNatLet covWTypedBetaNatTarget :=
  .ctx (.zeta covWTypedBetaNatArrow (.const 2 []) covWTypedBetaNatBody)

private theorem covWTypedBetaNat_demand_bot {ρ : EnvT} {a : CptT}
    {us : List CptT}
    (hA : ApproxT natEnvU ρ covWTypedBetaNatArrow a)
    (ht : ∀ u ∈ us, CTyS natEnvU u a)
    (ha : ∀ u ∈ us, ApproxT natEnvU ρ (.const 2 []) u) :
    ∀ u ∈ us, u = .bot := by
  intro u hu
  rcases approxT_rigid_const_inv rigidConst_natEnvU_succ (ha u hu) with hb | rfl
  · exact hb
  · rcases approxT_pi_inv hA with rfl | ⟨d, rows, rfl, _⟩
    · exact ctyS_bot_inv (ht _ hu)
    · rcases ctyS_pi_inv (ht _ hu) with hb | ⟨f, he, _⟩
      · exact hb
      · exact CptT.noConfusion he

/-- All raw observations of the higher-order beta source are bottom. -/
theorem covWTypedBetaNat_source_bot {ρ : EnvT} {c : CptT}
    (h : ApproxT natEnvU ρ covWTypedBetaNatSource c) : c = .bot := by
  rcases approxT_app_inv h with hb | ⟨g, s, hec, hf, hs, ha⟩ |
    ⟨r, args, u, _, hf, _⟩
  · exact hb
  · rcases approxT_lam_inv hf with hb | ⟨a, g', he, hA, _, hg⟩
    · exact CptT.noConfusion hb
    · injection he with hgg
      subst g'
      have hdem := covWTypedBetaNat_demand_bot hA (hg s hs).1 ha
      have hbody : s.2 = .bot :=
        covUProj_app_bot_of_function_bot (fun d hd => by
          rcases approxT_bvar_inv hd with hb | hm
          · exact hb
          · exact hdem d hm) (hg s hs).2
      exact hec.trans hbody
  · rcases approxT_lam_inv hf with hb | ⟨a, g, he, _⟩
    · exact CptT.noConfusion hb
    · exact CptT.noConfusion he

theorem covWTypedBetaNat_let_bot {ρ : EnvT} {c : CptT}
    (h : ApproxT natEnvU ρ covWTypedBetaNatLet c) : c = .bot := by
  cases h with
  | bot => rfl
  | letE h => exact covWTypedBetaNat_source_bot h

theorem covWTypedBetaNat_target_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKW natEnvU n Γ ρ covWTypedBetaNatTarget covWTypedBetaNatCpt :=
  .free (kFreeT_natEnvU _) (.appSpine
    (.const ρ 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ)
    (.bot _ _))

theorem covWTypedBetaNat_type_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKW natEnvU n Γ ρ (.const 0 []) (.spine 0 []) :=
  .free (kFreeT_natEnvU _)
    (.const ρ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)

theorem covWTypedBetaNat_compact_typed :
    CTyS natEnvU covWTypedBetaNatCpt (.spine 0 []) := by
  rw [CTyS]
  exact Or.inr ⟨⟨2, [.bot], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

theorem covWTypedBetaNat_source_not_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTKW natEnvU n Γ ρ covWTypedBetaNatSource covWTypedBetaNatCpt := by
  intro h
  exact CptT.noConfusion
    (covWTypedBetaNat_source_bot (approxTK_forget (covW_forget_old h)))

theorem covWTypedBetaNat_let_not_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTKW natEnvU n Γ ρ covWTypedBetaNatLet covWTypedBetaNatCpt := by
  intro h
  exact CptT.noConfusion
    (covWTypedBetaNat_let_bot (approxTK_forget (covW_forget_old h)))

def covWTypedBetaNat_type_ty (n : Nat) :
    HasTyT natEnvU n [] (.const 0 []) (.sort (.succ .zero)) :=
  hasTyT_natEnvU_nat n []

def covWTypedBetaNat_let_conv (n : Nat) :
    ConvT natEnvU n [] covWTypedBetaNatLet covWTypedBetaNatTarget (.const 0 []) :=
  .zeta [] covWTypedBetaNatArrow (.const 2 []) covWTypedBetaNatBody (.const 0 [])
    (.imax (.succ .zero) (.succ .zero))
    (covWTypedBetaNatArrow_ty n []) (hasTyT_natEnvU_succ n [])
    (covWTypedBetaNatLetBody_ty n)

theorem covWTypedBetaNat_normal (n : Nat) :
    NormalR (WhStepCK2 natEnvU n) [] covWTypedBetaNatTarget :=
  covV_body_free_spine_normal (m := natSuccMember)
    (rfl : natEnvU.members 2 = some natSuccMember) rfl (by decide)
    [] [.const 1 []]

theorem covWTypedBetaNat_readback (n : Nat) :
    RedR (WhStepCK2 natEnvU n) [] covWTypedBetaNatSource covWTypedBetaNatTarget :=
  redR_single (covWTypedBetaNat_step n)

theorem covWTypedBetaNat_let_readback (n : Nat) :
    RedR (WhStepCK2 natEnvU n) [] covWTypedBetaNatLet covWTypedBetaNatTarget :=
  redR_single (covWTypedBetaNat_let_step n)

/-- The witnessed native head has precisely the constructor reference and
the actual field of the compact's spine, including a normality certificate. -/
theorem covWTypedBetaNat_matching_constructor (n : Nat) :
    covWTypedBetaNatTarget = foldApps (.const 2 []) [.const 1 []] ∧
    covWTypedBetaNatCpt = .spine 2 [.bot] ∧
    (natEnvU.members 2 = some natSuccMember) ∧
    (natSuccMember.mclass = .constructorM) ∧
    RedR (WhStepCK2 natEnvU n) [] covWTypedBetaNatSource
      (foldApps (.const 2 []) [.const 1 []]) ∧
    RedR (WhStepCK2 natEnvU n) [] covWTypedBetaNatLet
      (foldApps (.const 2 []) [.const 1 []]) ∧
    NormalR (WhStepCK2 natEnvU n) [] (foldApps (.const 2 []) [.const 1 []]) :=
  ⟨rfl, rfl, rfl, rfl, covWTypedBetaNat_readback n,
    covWTypedBetaNat_let_readback n, covWTypedBetaNat_normal n⟩

theorem covWTypedBetaNat_kFree :
    KFreeT natEnvU covWTypedBetaNatSource ∧
    KFreeT natEnvU covWTypedBetaNatLet ∧
    KFreeT natEnvU covWTypedBetaNatTarget :=
  ⟨kFreeT_natEnvU _, kFreeT_natEnvU _, kFreeT_natEnvU _⟩

/-- Reference 3 is the admitted Nat environment's sole recursor. It does
not occur in either source or in the reduct. -/
theorem covWTypedBetaNat_no_rec_occurrence :
    occursConst 3 covWTypedBetaNatSource = false ∧
    occursConst 3 covWTypedBetaNatLet = false ∧
    occursConst 3 covWTypedBetaNatTarget = false := by decide

theorem covWTypedBetaNat_nat_not_prop : ¬ IsPropCT natEnvU (.spine 0 []) :=
  not_isPropCT_natEnvU_nat_spine []

theorem covWTypedBetaNat_nonbottom : covWTypedBetaNatCpt ≠ .bot :=
  fun he => CptT.noConfusion he

theorem covWTypedBetaNat_target_raw (ρ : EnvT) :
    ApproxTW natEnvU ρ covWTypedBetaNatTarget covWTypedBetaNatCpt :=
  .appSpine
    (.const ρ 2 [] rigidConst_natEnvU_succ not_propCtorT_natEnvU_succ)
    (.bot _ _)

theorem covWTypedBetaNat_type_raw (ρ : EnvT) :
    ApproxTW natEnvU ρ (.const 0 []) (.spine 0 []) :=
  .const ρ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat

theorem covWTypedBetaNat_source_raw_only_bot {ρ : EnvT} {c : CptT}
    (h : ApproxTW natEnvU ρ covWTypedBetaNatSource c) : c = .bot :=
  covWTypedBetaNat_source_bot (approxTN_forget (approxTW_forget h))

theorem covWTypedBetaNat_let_raw_only_bot {ρ : EnvT} {c : CptT}
    (h : ApproxTW natEnvU ρ covWTypedBetaNatLet c) : c = .bot :=
  covWTypedBetaNat_let_bot (approxTN_forget (approxTW_forget h))

theorem covWTypedBetaNat_source_guarded_only_bot {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {c : CptT}
    (h : ApproxTKW natEnvU n Γ ρ covWTypedBetaNatSource c) : c = .bot :=
  covWTypedBetaNat_source_bot (approxTK_forget (covW_forget_old h))

theorem covWTypedBetaNat_let_guarded_only_bot {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {c : CptT}
    (h : ApproxTKW natEnvU n Γ ρ covWTypedBetaNatLet c) : c = .bot :=
  covWTypedBetaNat_let_bot (approxTK_forget (covW_forget_old h))

/-- A beta/let failure contains all concrete native and semantic evidence;
its native step is deliberately not required to be a K step. -/
structure CovWTypedNatFailureAt (n : Nat) (M : CtxModelT natEnvU)
    (e : Expr Nat) : Prop where
  envWf : Nonempty (EnvWfT natEnvU)
  ctxWf : Nonempty (CtxWfT natEnvU n [])
  realized : CovWRealized natEnvU n 1 [] EnvT.bot SubstT.id
  valuation : EnvTypedFinAtT M [] EnvT.bot
  coherence : CtxEnvM M [] EnvT.bot
  argumentTy : Nonempty (HasTyT natEnvU n [] (.const 2 []) covWTypedBetaNatArrow)
  sourceTy : Nonempty (HasTyT natEnvU n [] e (.const 0 []))
  reductTy : Nonempty (HasTyT natEnvU n [] covWTypedBetaNatTarget (.const 0 []))
  typeTy : Nonempty (HasTyT natEnvU n [] (.const 0 []) (.sort (.succ .zero)))
  conversion : Nonempty (ConvT natEnvU n [] e covWTypedBetaNatTarget (.const 0 []))
  step : WhStepCK2 natEnvU n [] e covWTypedBetaNatTarget
  readback : RedR (WhStepCK2 natEnvU n) [] e covWTypedBetaNatTarget
  normal : NormalR (WhStepCK2 natEnvU n) [] covWTypedBetaNatTarget
  sourceKFree : KFreeT natEnvU e
  reductKFree : KFreeT natEnvU covWTypedBetaNatTarget
  sourceBot : M.Ap EnvT.bot e .bot
  reductObservation : M.Ap EnvT.bot covWTypedBetaNatTarget covWTypedBetaNatCpt
  typeObservation : M.Ap EnvT.bot (.const 0 []) (.spine 0 [])
  demand : CTyS natEnvU covWTypedBetaNatCpt (.spine 0 [])
  nonbottom : covWTypedBetaNatCpt ≠ .bot
  sourceOnlyBot : ∀ (ρ : EnvT) (d : CptT), M.Ap ρ e d → d = .bot

theorem CovWTypedNatFailureAt.refutes {n : Nat} {M : CtxModelT natEnvU}
    {e : Expr Nat} (h : CovWTypedNatFailureAt n M e)
    {R : Expr Nat → Expr Nat → Prop} (hR : R e covWTypedBetaNatTarget) :
    ¬ covWTyped_antiReductionAt natEnvU n [] M R := by
  intro hback
  exact h.nonbottom (h.sourceOnlyBot EnvT.bot covWTypedBetaNatCpt
    (hback EnvT.bot e covWTypedBetaNatTarget (.const 0 []) (.succ .zero)
      covWTypedBetaNatCpt (.spine 0 []) h.envWf h.ctxWf h.valuation
      h.sourceTy h.reductTy h.typeTy hR h.reductObservation h.typeObservation
      h.demand h.nonbottom))

theorem covWTypedBetaNat_raw_failure (n : Nat) :
    CovWTypedNatFailureAt n (⟨ApproxTW natEnvU⟩ : CtxModelT natEnvU)
      covWTypedBetaNatSource where
  envWf := ⟨natEnvUWfT⟩
  ctxWf := ⟨.nil⟩
  realized := covW_realized_nil _ _ _
  valuation := covWTyped_raw_bot_valuation natEnvU []
  coherence := fun _ _ hv => Option.noConfusion hv
  argumentTy := ⟨hasTyT_natEnvU_succ n []⟩
  sourceTy := ⟨covWTypedBetaNatSource_ty n⟩
  reductTy := ⟨covWTypedBetaNatTarget_ty n⟩
  typeTy := ⟨covWTypedBetaNat_type_ty n⟩
  conversion := ⟨covWTypedBetaNat_conv n⟩
  step := covWTypedBetaNat_step n
  readback := covWTypedBetaNat_readback n
  normal := covWTypedBetaNat_normal n
  sourceKFree := covWTypedBetaNat_kFree.1
  reductKFree := covWTypedBetaNat_kFree.2.2
  sourceBot := .bot _ _
  reductObservation := covWTypedBetaNat_target_raw EnvT.bot
  typeObservation := covWTypedBetaNat_type_raw EnvT.bot
  demand := covWTypedBetaNat_compact_typed
  nonbottom := covWTypedBetaNat_nonbottom
  sourceOnlyBot := fun _ _ h => covWTypedBetaNat_source_raw_only_bot h

theorem covWTypedBetaNat_guarded_failure (n : Nat) :
    CovWTypedNatFailureAt n (⟨ApproxTKW natEnvU n []⟩ : CtxModelT natEnvU)
      covWTypedBetaNatSource where
  envWf := ⟨natEnvUWfT⟩
  ctxWf := ⟨.nil⟩
  realized := covW_realized_nil _ _ _
  valuation := covWTyped_guarded_bot_valuation natEnvU n []
  coherence := fun _ _ hv => Option.noConfusion hv
  argumentTy := ⟨hasTyT_natEnvU_succ n []⟩
  sourceTy := ⟨covWTypedBetaNatSource_ty n⟩
  reductTy := ⟨covWTypedBetaNatTarget_ty n⟩
  typeTy := ⟨covWTypedBetaNat_type_ty n⟩
  conversion := ⟨covWTypedBetaNat_conv n⟩
  step := covWTypedBetaNat_step n
  readback := covWTypedBetaNat_readback n
  normal := covWTypedBetaNat_normal n
  sourceKFree := covWTypedBetaNat_kFree.1
  reductKFree := covWTypedBetaNat_kFree.2.2
  sourceBot := .bot _ _ _
  reductObservation := covWTypedBetaNat_target_observed n [] EnvT.bot
  typeObservation := covWTypedBetaNat_type_observed n [] EnvT.bot
  demand := covWTypedBetaNat_compact_typed
  nonbottom := covWTypedBetaNat_nonbottom
  sourceOnlyBot := fun _ _ h => covWTypedBetaNat_source_guarded_only_bot h

theorem covWTypedBetaNat_let_raw_failure (n : Nat) :
    CovWTypedNatFailureAt n (⟨ApproxTW natEnvU⟩ : CtxModelT natEnvU)
      covWTypedBetaNatLet where
  envWf := ⟨natEnvUWfT⟩
  ctxWf := ⟨.nil⟩
  realized := covW_realized_nil _ _ _
  valuation := covWTyped_raw_bot_valuation natEnvU []
  coherence := fun _ _ hv => Option.noConfusion hv
  argumentTy := ⟨hasTyT_natEnvU_succ n []⟩
  sourceTy := ⟨covWTypedBetaNatLet_ty n⟩
  reductTy := ⟨covWTypedBetaNatTarget_ty n⟩
  typeTy := ⟨covWTypedBetaNat_type_ty n⟩
  conversion := ⟨covWTypedBetaNat_let_conv n⟩
  step := covWTypedBetaNat_let_step n
  readback := covWTypedBetaNat_let_readback n
  normal := covWTypedBetaNat_normal n
  sourceKFree := covWTypedBetaNat_kFree.2.1
  reductKFree := covWTypedBetaNat_kFree.2.2
  sourceBot := .bot _ _
  reductObservation := covWTypedBetaNat_target_raw EnvT.bot
  typeObservation := covWTypedBetaNat_type_raw EnvT.bot
  demand := covWTypedBetaNat_compact_typed
  nonbottom := covWTypedBetaNat_nonbottom
  sourceOnlyBot := fun _ _ h => covWTypedBetaNat_let_raw_only_bot h

theorem covWTypedBetaNat_let_guarded_failure (n : Nat) :
    CovWTypedNatFailureAt n (⟨ApproxTKW natEnvU n []⟩ : CtxModelT natEnvU)
      covWTypedBetaNatLet where
  envWf := ⟨natEnvUWfT⟩
  ctxWf := ⟨.nil⟩
  realized := covW_realized_nil _ _ _
  valuation := covWTyped_guarded_bot_valuation natEnvU n []
  coherence := fun _ _ hv => Option.noConfusion hv
  argumentTy := ⟨hasTyT_natEnvU_succ n []⟩
  sourceTy := ⟨covWTypedBetaNatLet_ty n⟩
  reductTy := ⟨covWTypedBetaNatTarget_ty n⟩
  typeTy := ⟨covWTypedBetaNat_type_ty n⟩
  conversion := ⟨covWTypedBetaNat_let_conv n⟩
  step := covWTypedBetaNat_let_step n
  readback := covWTypedBetaNat_let_readback n
  normal := covWTypedBetaNat_normal n
  sourceKFree := covWTypedBetaNat_kFree.2.1
  reductKFree := covWTypedBetaNat_kFree.2.2
  sourceBot := .bot _ _ _
  reductObservation := covWTypedBetaNat_target_observed n [] EnvT.bot
  typeObservation := covWTypedBetaNat_type_observed n [] EnvT.bot
  demand := covWTypedBetaNat_compact_typed
  nonbottom := covWTypedBetaNat_nonbottom
  sourceOnlyBot := fun _ _ h => covWTypedBetaNat_let_guarded_only_bot h

/-- A literal outer beta relation, without reduction in subexpressions. -/
def CovWTypedBetaHead (e e' : Expr Nat) : Prop :=
  ∃ D body arg, e = .app (.lam D body) arg ∧ e' = instantiate0 arg body

def CovWTypedLetHead (e e' : Expr Nat) : Prop :=
  ∃ D value body, e = .letE D value body ∧ e' = instantiate0 value body

theorem covWTypedBetaNat_no_raw_beta_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTW natEnvU⟩ : CtxModelT natEnvU) CovWTypedBetaHead :=
  (covWTypedBetaNat_raw_failure n).refutes
    ⟨covWTypedBetaNatArrow, covWTypedBetaNatBody, .const 2 [], rfl, rfl⟩

theorem covWTypedBetaNat_no_guarded_beta_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTKW natEnvU n []⟩ : CtxModelT natEnvU) CovWTypedBetaHead :=
  (covWTypedBetaNat_guarded_failure n).refutes
    ⟨covWTypedBetaNatArrow, covWTypedBetaNatBody, .const 2 [], rfl, rfl⟩

theorem covWTypedBetaNat_no_raw_let_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTW natEnvU⟩ : CtxModelT natEnvU) CovWTypedLetHead :=
  (covWTypedBetaNat_let_raw_failure n).refutes
    ⟨covWTypedBetaNatArrow, .const 2 [], covWTypedBetaNatBody, rfl, rfl⟩

theorem covWTypedBetaNat_no_guarded_let_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTKW natEnvU n []⟩ : CtxModelT natEnvU) CovWTypedLetHead :=
  (covWTypedBetaNat_let_guarded_failure n).refutes
    ⟨covWTypedBetaNatArrow, .const 2 [], covWTypedBetaNatBody, rfl, rfl⟩

theorem covWTypedBetaNat_no_raw_step_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTW natEnvU⟩ : CtxModelT natEnvU) (WhStepCK2 natEnvU n []) :=
  (covWTypedBetaNat_raw_failure n).refutes (covWTypedBetaNat_step n)

theorem covWTypedBetaNat_no_guarded_step_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTKW natEnvU n []⟩ : CtxModelT natEnvU) (WhStepCK2 natEnvU n []) :=
  (covWTypedBetaNat_guarded_failure n).refutes (covWTypedBetaNat_step n)

theorem covWTypedBetaNat_no_raw_conversion_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTW natEnvU⟩ : CtxModelT natEnvU)
      (fun e e' => Nonempty (ConvT natEnvU n [] e e' (.const 0 []))) :=
  (covWTypedBetaNat_raw_failure n).refutes ⟨covWTypedBetaNat_conv n⟩

theorem covWTypedBetaNat_no_guarded_conversion_antiReduction (n : Nat) :
    ¬ covWTyped_antiReductionAt natEnvU n []
      (⟨ApproxTKW natEnvU n []⟩ : CtxModelT natEnvU)
      (fun e e' => Nonempty (ConvT natEnvU n [] e e' (.const 0 []))) :=
  (covWTypedBetaNat_guarded_failure n).refutes ⟨covWTypedBetaNat_conv n⟩

/-- Both sources, the actual reduct, and its native type use the same
finite information stage. The closed realizer uses this stage as well. -/
theorem covWTypedBetaNat_same_stage (n : Nat) :
    CovWRealized natEnvU n 1 [] EnvT.bot SubstT.id ∧
    ApproxTKWStage natEnvU n 1 [] EnvT.bot covWTypedBetaNatSource .bot ∧
    ApproxTKWStage natEnvU n 1 [] EnvT.bot covWTypedBetaNatLet .bot ∧
    ApproxTKWStage natEnvU n 1 [] EnvT.bot covWTypedBetaNatTarget covWTypedBetaNatCpt ∧
    ApproxTKWStage natEnvU n 1 [] EnvT.bot (.const 0 []) (.spine 0 []) := by
  exact ⟨covW_realized_nil _ _ _,
    ⟨.bot _ _ _, by simp [covTObservationBudget]⟩,
    ⟨.bot _ _ _, by simp [covTObservationBudget]⟩,
    ⟨covWTypedBetaNat_target_observed n [] EnvT.bot,
      by simp [covTObservationBudget, covWTypedBetaNatCpt]⟩,
    ⟨covWTypedBetaNat_type_observed n [] EnvT.bot,
      by simp [covTObservationBudget]⟩⟩


-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_TYPED_BETA_BOUNDARY_ROOTS
#print axioms covWTypedBetaNatArrow
#print axioms covWTypedBetaNatBody
#print axioms covWTypedBetaNatSource
#print axioms covWTypedBetaNatLet
#print axioms covWTypedBetaNatTarget
#print axioms covWTypedBetaNatCpt
#print axioms covWTypedBetaNatArrow_ty
#print axioms covWTypedBetaNatBody_ty
#print axioms covWTypedBetaNatLetBody_ty
#print axioms covWTypedBetaNatSource_ty
#print axioms covWTypedBetaNatLet_ty
#print axioms covWTypedBetaNatTarget_ty
#print axioms covWTypedBetaNat_conv
#print axioms covWTypedBetaNat_step
#print axioms covWTypedBetaNat_let_step
#print axioms covWTypedBetaNat_source_bot
#print axioms covWTypedBetaNat_let_bot
#print axioms covWTypedBetaNat_target_observed
#print axioms covWTypedBetaNat_type_observed
#print axioms covWTypedBetaNat_compact_typed
#print axioms covWTypedBetaNat_source_not_observed
#print axioms covWTypedBetaNat_let_not_observed
#print axioms covWTypedBetaNat_type_ty
#print axioms covWTypedBetaNat_let_conv
#print axioms covWTypedBetaNat_normal
#print axioms covWTypedBetaNat_readback
#print axioms covWTypedBetaNat_let_readback
#print axioms covWTypedBetaNat_matching_constructor
#print axioms covWTypedBetaNat_kFree
#print axioms covWTypedBetaNat_no_rec_occurrence
#print axioms covWTypedBetaNat_nat_not_prop
#print axioms covWTypedBetaNat_nonbottom
#print axioms covWTypedBetaNat_target_raw
#print axioms covWTypedBetaNat_type_raw
#print axioms covWTypedBetaNat_source_raw_only_bot
#print axioms covWTypedBetaNat_let_raw_only_bot
#print axioms covWTypedBetaNat_source_guarded_only_bot
#print axioms covWTypedBetaNat_let_guarded_only_bot
#print axioms CovWTypedNatFailureAt
#print axioms CovWTypedNatFailureAt.refutes
#print axioms covWTypedBetaNat_raw_failure
#print axioms covWTypedBetaNat_guarded_failure
#print axioms covWTypedBetaNat_let_raw_failure
#print axioms covWTypedBetaNat_let_guarded_failure
#print axioms CovWTypedBetaHead
#print axioms CovWTypedLetHead
#print axioms covWTypedBetaNat_no_raw_beta_antiReduction
#print axioms covWTypedBetaNat_no_guarded_beta_antiReduction
#print axioms covWTypedBetaNat_no_raw_let_antiReduction
#print axioms covWTypedBetaNat_no_guarded_let_antiReduction
#print axioms covWTypedBetaNat_no_raw_step_antiReduction
#print axioms covWTypedBetaNat_no_guarded_step_antiReduction
#print axioms covWTypedBetaNat_no_raw_conversion_antiReduction
#print axioms covWTypedBetaNat_no_guarded_conversion_antiReduction
#print axioms covWTypedBetaNat_same_stage
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_TYPED_BETA_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWTypedAudit
