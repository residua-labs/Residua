import rcic.RcicNativeTypedModelCovWAligned
import rcic.RcicNativeTypedModelCovVBasicK

/-!
# Actual-call True and And controls

The new observations use the saturated native K rule. Every call carries
its own index and common-typing certificates. The And witness uses the
deterministic projection canon, with actual native typing of that canon.
The retained CovV observations supply only the computation-source checks;
the right-hand observations are new derivations.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelKAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelKFragmentAudit TypedModelKIndexFreeAudit TypedModelKGuardAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovVAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem covW_basic_empty_application {E : ResolvedEnv} {ρ : EnvT}
    {f x : Expr Nat} {c : CptT}
    (h : ApproxTW E ρ f (.lam [([], c)])) :
    ApproxTW E ρ (.app f x) c :=
  .app h (List.mem_singleton.mpr rfl)
    (fun u hu => (List.not_mem_nil u hu).elim)

private theorem covW_basic_empty_lambda {E : ResolvedEnv} {ρ : EnvT}
    {A b : Expr Nat} {c : CptT} (hc : c ≠ .bot)
    (h : ApproxTW E (EnvT.cons (demandT []) ρ) b c) :
    ApproxTW E ρ (.lam A b) (.lam [([], c)]) := by
  refine .lam (.bot _ _) ?_ ⟨([], c), List.mem_singleton.mpr rfl, hc⟩ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil u hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact h

/-- True has no indices; both complete families are the same actual Prop. -/
theorem covW_trueK_index (n : Nat) :
    KIndexGuardAt trueEnvU n kVarCtx wTrueRecU :=
  ⟨⟨.refl _ _ _ trueEnvUF_ty⟩,
    fun ρ => semEqDI_refl trueEnvU ρ (.const 0 [])⟩

/-- The actual variable major and the unique constructor inhabit True. -/
theorem covW_trueK_common (n : Nat) :
    KCommonAt trueEnvU n kVarCtx wTrueRecU (.bvar 0) :=
  ⟨⟨trueEnvUF_ty⟩, ⟨kVar_ty n⟩, ⟨trueEnvUtt_ty⟩⟩

theorem covW_trueK_native_head (n : Nat) :
    KNativeHead trueEnvU n kVarCtx (kRec (.bvar 0)) (.sort .zero) :=
  covW_k_head (w := wTrueRecU) (Or.inl ⟨rfl, rfl, rfl⟩)
    not_isCtorSpine_bvar (covW_trueK_index n) (covW_trueK_common n)

/-- Only this natively typed call is used. Its raw source is the retained
aligned observation; its Prop right-hand observation is a new free leaf. -/
theorem covW_trueK_observed (n : Nat) (ρ : EnvT) :
    ApproxTKW trueEnvU n kVarCtx ρ (kRec (.bvar 0)) .prop :=
  .recursorPropK wTrueRecU (.bvar 0) (Or.inl ⟨rfl, rfl, rfl⟩)
    not_isCtorSpine_bvar (covW_trueK_index n) (covW_trueK_common n)
    (approxTKN_forgetN (covV_trueK_observed n kVarCtx ρ (.bvar 0)))
    (.free (kFreeT_sort trueEnvU .zero) (.sort ρ .zero))

theorem covW_trueK_control (n : Nat) :
    Nonempty (EnvWfT trueEnvU) ∧ Nonempty (CtxWfT trueEnvU n kVarCtx) ∧
    Nonempty (NativeSpineHead.Step trueEnvU n kVarCtx
      (kRec (.bvar 0)) (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT trueEnvU n kVarCtx (.sort .zero)
      (kRec (.bvar 0)) (.sort (.succ .zero))) ∧
    KIndexGuardAt trueEnvU n kVarCtx wTrueRecU ∧
    KCommonAt trueEnvU n kVarCtx wTrueRecU (.bvar 0) ∧
    ApproxTKW trueEnvU n kVarCtx EnvT.bot (kRec (.bvar 0)) .prop ∧
    RedR (WhStepCK2 trueEnvU n) kVarCtx (kRec (.bvar 0)) (.sort .zero) :=
  ⟨⟨trueEnvUWfT⟩, ⟨kVarCtx_wf n⟩, ⟨stepK_kRec_var n⟩,
    ⟨kRec_conv_sort (kVar_ty n)⟩, covW_trueK_index n, covW_trueK_common n,
    covW_trueK_observed n EnvT.bot, redR_single (.native (covW_trueK_native_head n))⟩

/-- Unlike the old existential K certificate, this witness uses the actual
deterministic projections of the neutral major. -/
def covWAndCanonWitness : IotaWitness andEnvU := kProjWitness mixAndW (.bvar 0)

theorem covW_andK_canon : KCanonW covWAndCanonWitness (.bvar 0) := by
  refine Or.inr ⟨kfieldW_kProjWitness kfieldW_mixAndW (.bvar 0), ?_⟩
  exact (projFields_eq_of (w₁ := kProjWitness mixAndW (.bvar 0)) (w₂ := mixAndW)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (.bvar 0)).symm

private def covWAndProjMotive0 : Expr Nat := .lam mixAndFamApp (.bvar 5)
private def covWAndProjMotive1 : Expr Nat := .lam mixAndFamApp (.bvar 4)
private def covWAndProjMinor0 : Expr Nat := .lam (.bvar 4) (.lam (.bvar 4) (.bvar 1))
private def covWAndProjMinor1 : Expr Nat := .lam (.bvar 4) (.lam (.bvar 4) (.bvar 0))
private def covWAndProj0 : Expr Nat :=
  recCall (.const 2 [.zero])
    [.bvar 4, .bvar 3, covWAndProjMotive0, covWAndProjMinor0] (.bvar 0)
private def covWAndProj1 : Expr Nat :=
  recCall (.const 2 [.zero])
    [.bvar 4, .bvar 3, covWAndProjMotive1, covWAndProjMinor1] (.bvar 0)
private def covWAndXYCtx : LCtx :=
  .assumption (.bvar 4) :: .assumption (.bvar 4) :: mixAndCtx

private def covW_andK_xy_family_typed :
    HasTyT andEnvU 0 covWAndXYCtx (andApp (.bvar 6) (.bvar 5)) (.sort .zero) :=
  .app covWAndXYCtx _ _ _ _
    (.app covWAndXYCtx _ _ _ _
      (.const covWAndXYCtx 0 [] andFamMember rfl rfl rfl)
      (.bvar covWAndXYCtx 6 (.sort .zero) rfl))
    (.bvar covWAndXYCtx 5 (.sort .zero) rfl)

private def covW_andK_xy_ctor_typed :
    HasTyT andEnvU 0 covWAndXYCtx mixAndMkTel (andApp (.bvar 6) (.bvar 5)) :=
  .app covWAndXYCtx _ _ _ _
    (.app covWAndXYCtx _ _ _ _
      (.app covWAndXYCtx _ _ _ _
        (.app covWAndXYCtx _ _ _ _
          (.const covWAndXYCtx 1 [] andIntroMember rfl rfl rfl)
          (.bvar covWAndXYCtx 6 (.sort .zero) rfl))
        (.bvar covWAndXYCtx 5 (.sort .zero) rfl))
      (.bvar covWAndXYCtx 1 (.bvar 6) rfl))
    (.bvar covWAndXYCtx 0 (.bvar 5) rfl)

private def covW_andK_motive0_typed :
    HasTyT andEnvU 0 mixAndCtx covWAndProjMotive0
      (.pi mixAndFamApp (.sort .zero)) :=
  .lam _ _ .zero _ _ mixAndFamTy (.bvar _ 5 _ rfl)

private def covW_andK_motive1_typed :
    HasTyT andEnvU 0 mixAndCtx covWAndProjMotive1
      (.pi mixAndFamApp (.sort .zero)) :=
  .lam _ _ .zero _ _ mixAndFamTy (.bvar _ 4 _ rfl)

private def covW_andK_minor0_typed :
    HasTyT andEnvU 0 mixAndCtx covWAndProjMinor0
      (.pi (.bvar 4) (.pi (.bvar 4)
        (.app (lift 0 2 covWAndProjMotive0) mixAndMkTel))) := by
  have hb : ConvT andEnvU 0 covWAndXYCtx
      (.app (lift 0 2 covWAndProjMotive0) mixAndMkTel) (.bvar 6) (.sort .zero) :=
    .beta _ (andApp (.bvar 6) (.bvar 5)) (.bvar 7) mixAndMkTel (.sort .zero) .zero
      covW_andK_xy_family_typed (.bvar _ 7 _ rfl) covW_andK_xy_ctor_typed
  exact .lam _ _ .zero _ _ mixTyA
    (.lam _ _ .zero _ _ (.bvar _ 4 _ rfl)
      (.conv _ _ _ _ .zero (.bvar _ 1 _ rfl) (.symm _ _ _ _ hb)))

private def covW_andK_minor1_typed :
    HasTyT andEnvU 0 mixAndCtx covWAndProjMinor1
      (.pi (.bvar 4) (.pi (.bvar 4)
        (.app (lift 0 2 covWAndProjMotive1) mixAndMkTel))) := by
  have hb : ConvT andEnvU 0 covWAndXYCtx
      (.app (lift 0 2 covWAndProjMotive1) mixAndMkTel) (.bvar 5) (.sort .zero) :=
    .beta _ (andApp (.bvar 6) (.bvar 5)) (.bvar 6) mixAndMkTel (.sort .zero) .zero
      covW_andK_xy_family_typed (.bvar _ 6 _ rfl) covW_andK_xy_ctor_typed
  exact .lam _ _ .zero _ _ mixTyA
    (.lam _ _ .zero _ _ (.bvar _ 4 _ rfl)
      (.conv _ _ _ _ .zero (.bvar _ 0 _ rfl) (.symm _ _ _ _ hb)))

private def covW_andK_projection0_typed :
    HasTyT andEnvU 0 mixAndCtx covWAndProj0 (.bvar 4) := by
  have hp : HasTyT andEnvU 0 mixAndCtx covWAndProj0
      (.app covWAndProjMotive0 (.bvar 0)) :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _
            (.app _ _ _ _ _ (.const _ 2 [.zero] andRecMemberU rfl rfl rfl) mixTyA)
            mixTyB)
          covW_andK_motive0_typed)
        covW_andK_minor0_typed)
      mixTyH
  exact .conv _ _ _ _ .zero hp
    (.beta _ mixAndFamApp (.bvar 5) (.bvar 0) (.sort .zero) .zero
      mixAndFamTy (.bvar _ 5 _ rfl) mixTyH)

private def covW_andK_projection1_typed :
    HasTyT andEnvU 0 mixAndCtx covWAndProj1 (.bvar 3) := by
  have hp : HasTyT andEnvU 0 mixAndCtx covWAndProj1
      (.app covWAndProjMotive1 (.bvar 0)) :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _
            (.app _ _ _ _ _ (.const _ 2 [.zero] andRecMemberU rfl rfl rfl) mixTyA)
            mixTyB)
          covW_andK_motive1_typed)
        covW_andK_minor1_typed)
      mixTyH
  exact .conv _ _ _ _ .zero hp
    (.beta _ mixAndFamApp (.bvar 4) (.bvar 0) (.sort .zero) .zero
      mixAndFamTy (.bvar _ 4 _ rfl) mixTyH)

/-- The two actual selectors have types a and b by native beta conversion.
Applying the admitted constructor gives the deterministic canon's typing. -/
def covW_andK_canon_typed :
    HasTyT andEnvU 0 mixAndCtx (ctorMajorRec covWAndCanonWitness) mixAndFamApp :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _ (.const _ 1 [] andIntroMember rfl rfl rfl) mixTyA)
        mixTyB)
      covW_andK_projection0_typed)
    covW_andK_projection1_typed

/-- The And family has no indices; no index-conversion oracle is required. -/
theorem covW_andK_index : KIndexGuardAt andEnvU 0 mixAndCtx covWAndCanonWitness :=
  ⟨⟨.refl _ _ _ mixAndFamTy⟩, fun ρ => semEqDI_refl andEnvU ρ mixAndFamApp⟩

theorem covW_andK_common :
    KCommonAt andEnvU 0 mixAndCtx covWAndCanonWitness (.bvar 0) :=
  ⟨⟨mixAndFamTy⟩, ⟨mixTyH⟩, ⟨covW_andK_canon_typed⟩⟩

/-- The minor ignores both proof fields. Its new raw observation therefore
needs no observation of a projection or an old non-strict recursor row. -/
theorem covW_andK_rhs_observed (ρ : EnvT) :
    ApproxTKW andEnvU 0 mixAndCtx ρ (iotaRhsOf covWAndCanonWitness) (.pi .bot []) := by
  apply ApproxTKW.free (kFreeT_andEnvU _)
  apply covW_basic_empty_application
  apply covW_basic_empty_application
  apply covW_basic_empty_lambda (by intro h; cases h)
  apply covW_basic_empty_lambda (by intro h; cases h)
  exact .pi (.bot _ _) (fun _ h => (List.not_mem_nil _ h).elim)
    (fun _ h => (List.not_mem_nil _ h).elim)

theorem covW_andK_native_head :
    KNativeHead andEnvU 0 mixAndCtx mixAndRedex (iotaRhsOf covWAndCanonWitness) :=
  covW_k_head covW_andK_canon not_isCtorSpine_bvar covW_andK_index covW_andK_common

theorem covW_andK_observed (ρ : EnvT) :
    ApproxTKW andEnvU 0 mixAndCtx ρ mixAndRedex (.pi .bot []) :=
  .recursorPropK covWAndCanonWitness (.bvar 0) covW_andK_canon
    not_isCtorSpine_bvar covW_andK_index covW_andK_common
    (approxTKN_forgetN (covV_andK_observed 0 mixAndCtx ρ))
    (covW_andK_rhs_observed ρ)

theorem covW_andK_read :
    RedR (WhStepCK2 andEnvU 0) mixAndCtx mixAndRedex mixPi :=
  .step (.native covW_andK_native_head)
    (.step (.ctx (.appHead (.beta _ _ _)))
      (.step (.ctx (.beta _ _ _)) (.refl _)))

theorem covW_andK_control :
    Nonempty (EnvWfT andEnvU) ∧ Nonempty (CtxWfT andEnvU 0 mixAndCtx) ∧
    Nonempty (NativeSpineHead.Step andEnvU 0 mixAndCtx mixAndRedex mixAndRhs
      (.app mixAndMot mixAndMkApp)) ∧
    Nonempty (ConvT andEnvU 0 mixAndCtx mixAndRedex mixPi
      (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
    KIndexGuardAt andEnvU 0 mixAndCtx covWAndCanonWitness ∧
    KCommonAt andEnvU 0 mixAndCtx covWAndCanonWitness (.bvar 0) ∧
    ApproxTKW andEnvU 0 mixAndCtx EnvT.bot mixAndRedex (.pi .bot []) ∧
    RedR (WhStepCK2 andEnvU 0) mixAndCtx mixAndRedex mixPi :=
  ⟨⟨andEnvUWfT⟩, ⟨Rcic.Domain.Model.PiInversion.mixAndCtx_wf⟩,
    ⟨stepK_mixAnd⟩, mixAnd_conv, covW_andK_index, covW_andK_common,
    covW_andK_observed EnvT.bot, covW_andK_read⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_BASIC_K_ROOTS
#print axioms covW_trueK_index
#print axioms covW_trueK_common
#print axioms covW_trueK_native_head
#print axioms covW_trueK_observed
#print axioms covW_trueK_control
#print axioms covWAndCanonWitness
#print axioms covW_andK_canon
#print axioms covW_andK_canon_typed
#print axioms covW_andK_index
#print axioms covW_andK_common
#print axioms covW_andK_rhs_observed
#print axioms covW_andK_native_head
#print axioms covW_andK_observed
#print axioms covW_andK_read
#print axioms covW_andK_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_BASIC_K_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWAudit
