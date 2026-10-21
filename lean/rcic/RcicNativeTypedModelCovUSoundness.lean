import rcic.RcicNativeTypedModelCovUSoundnessEnv
import rcic.RcicNativeTypedModelCovURealized

/-!
# The observation-soundness gate fails at the old non-strict Prop recursor

The major is an actual closed native proof `Ω : W`. The admitted higher-order
singleton has no legacy witness, hence neither native K clause can apply.
Its recursor call steps to itself through major reduction, while the old
`ApproxT.recursorProp` clause ignores the major and observes Prop. This is a
failure of head existence itself, with a realized empty valuation.

All premises are supplied. No interpretation is built past this gate.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelKFragmentAudit TypedModelKTransportAudit
open ReadbackCKAudit ReadbackCK2Audit FamModelLRSAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covUHoMotive : Expr Nat := .lam (.const 63 []) (.sort (.succ .zero))
def covUHoIhTy : Expr Nat :=
  .pi (.sort .zero) (.app covUHoMotive (.app (.bvar 1) (.bvar 0)))
def covUHoMinor : Expr Nat :=
  .lam covUHoField (.lam covUHoIhTy (.sort .zero))
def covUHoMajor : Expr Nat := covUOmega (covUCycleX 63 66)
def covUHoType : Expr Nat :=
  recCall (.const 65 [.succ (.succ .zero)]) [covUHoMotive, covUHoMinor] covUHoMajor

/-- Actual native typing of the closed diverging proof used as major. -/
def covUHoMajor_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covUHoMajor (.const 63 []) :=
  covUCycle_omega_hasTy 63 66 Γ covUHoEnv_wf rfl rfl rfl
    (fun Δ => .const Δ 63 [] covUHoFam rfl rfl rfl)
    (fun Δ => .const Δ 66 [] covUHoParameter rfl rfl rfl)

private def covUHoMotive_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covUHoMotive
      (.pi (.const 63 []) (.sort (.succ (.succ .zero)))) :=
  .lam _ _ _ _ _ (.const _ 63 [] covUHoFam rfl rfl rfl) (.sort _ _)

private def covUHoField_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covUHoField (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ _ _ _ _ (.sort _ _) (.const _ 63 [] covUHoFam rfl rfl rfl)

private def covUHoIh_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n (.assumption covUHoField :: Γ) covUHoIhTy
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) := by
  have hf : HasTyT covUHoEnv n
      (.assumption (.sort .zero) :: .assumption covUHoField :: Γ)
      (.bvar 1) covUHoField := .bvar _ 1 _ rfl
  have hp : HasTyT covUHoEnv n
      (.assumption (.sort .zero) :: .assumption covUHoField :: Γ)
      (.bvar 0) (.sort .zero) := .bvar _ 0 _ rfl
  exact .pi _ _ _ _ _ (.sort _ _)
    (.app _ _ _ _ _ (covUHoMotive_hasTy n _) (.app _ _ _ _ _ hf hp))

private def covUHoMinor_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covUHoMinor (instantiate0 covUHoMotive covUHoMinTy) := by
  let Δ := .assumption covUHoIhTy :: .assumption covUHoField :: Γ
  have hf : HasTyT covUHoEnv n Δ (.bvar 1) covUHoField := .bvar _ 1 _ rfl
  have hc : HasTyT covUHoEnv n Δ (.app (.const 64 []) (.bvar 1)) (.const 63 []) :=
    .app _ _ _ _ _ (.const _ 64 [] covUHoCtor rfl rfl rfl) hf
  have hb : ConvT covUHoEnv n Δ
      (.app covUHoMotive (.app (.const 64 []) (.bvar 1))) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
    .beta _ _ _ _ _ _ (.const _ 63 [] covUHoFam rfl rfl rfl) (.sort _ _) hc
  exact .lam _ _ _ _ _ (covUHoField_hasTy n Γ)
    (.lam _ _ _ _ _ (covUHoIh_hasTy n Γ)
      (.conv _ _ _ _ _ (.sort _ .zero) (.symm _ _ _ _ hb)))

private def covUHoPartial_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ
      (foldApps (.const 65 [.succ (.succ .zero)]) [covUHoMotive, covUHoMinor])
      (.pi (.const 63 []) (.app covUHoMotive (.bvar 0))) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (.const _ 65 [.succ (.succ .zero)] covUHoRec rfl rfl rfl)
      (covUHoMotive_hasTy n Γ)) (covUHoMinor_hasTy n Γ)

/-- The self-looping whole expression is a native TYPE at Sort 1. -/
def covUHoType_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covUHoEnv n Γ covUHoType (.sort (.succ .zero)) := by
  have hm := covUHoMajor_hasTy n Γ
  have hraw := HasTyT.app Γ _ _ _ _ (covUHoPartial_hasTy n Γ) hm
  have hb : ConvT covUHoEnv n Γ (.app covUHoMotive covUHoMajor)
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .beta Γ (.const 63 []) (.sort (.succ .zero)) covUHoMajor
      (.sort (.succ (.succ .zero))) .zero
      (.const Γ 63 [] covUHoFam rfl rfl rfl) (.sort _ _) hm
  exact .conv _ _ _ _ _ hraw hb

/-- The structured typed witness is computed from the actual stored HO telescope. -/
def covUHoWitness : IotaWitnessS covUHoEnv where
  recRef := 65
  ctorRef := 64
  ls := [.succ (.succ .zero)]
  lsC := []
  recMember := covUHoRec
  ctorMember := covUHoCtor
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [covUHoMotive, covUHoMinor]
  fields := [.bvar 0]
  ctorParams := []
  familyRef := 63
  famMember := covUHoFam
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  ctorDoms := [covUHoField]
  ctorResult := .const 63 []
  hpeel := rfl
  hfamApp := rfl
  recDoms := [covUHoMotTy, covUHoMinTy, .const 63 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 8
  shapes := [.recursive 1]
  hshapes := rfl
  schema := .app (.app (.bvar 1) (.bvar 0))
    (.lam (.sort .zero)
      (.app (.app (.app (.const 65 [.param 0]) (.bvar 3)) (.bvar 2))
        (.app (.bvar 1) (.bvar 0))))
  hschema := rfl
  hstable := iotaWitnessS_hstable_of_constsMemberFuel rfl rfl (by
    with_unfolding_all rfl)
  hschemaScope := rfl

/-- Legacy K eligibility really fails; no native witness is left implicit. -/
theorem covUHo_no_legacy_witness (w : IotaWitness covUHoEnv) (hr : w.recRef = 65) : False := by
  have hm : w.recMember = covUHoRec := by
    have hh := w.hrec
    rw [hr] at hh
    exact (Option.some.inj hh).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 3 at hn
  have hi := w.hidx
  have hnp : w.nparams = 0 := by omega
  have hni : w.nindices = 0 := by omega
  have hnm : w.nMinors = 1 := by omega
  have hci : w.ctorIdx = 0 := by omega
  have hfr : w.familyRef = 63 := by have hh := w.hrecIdx; omega
  have hcr : w.ctorRef = 64 := by have hh := w.hctorIdx; omega
  have hc : w.ctorMember = covUHoCtor := by
    have hh := w.hctor
    rw [hcr] at hh
    exact (Option.some.inj hh).symm
  have hnf := w.hnpar
  rw [hc] at hnf
  change w.nparams + w.fields.length = 1 at hnf
  exact not_iotaWitness_of_higherOrderField (E := covUHoEnv)
    (c := 64) (fam := 63) (cm := covUHoCtor) rfl (p := 0) (T := covUHoField)
    rfl rfl rfl w hcr hfr (by omega) (by omega)

theorem covUHo_not_kFreeRec : ¬ KFreeRec covUHoEnv 65 := by
  rintro ⟨w, hr, _⟩
  exact covUHo_no_legacy_witness w hr

theorem covUHo_not_kProjRec : ¬ KProjRec covUHoEnv 65 := by
  rintro ⟨w, hr, _⟩
  exact covUHo_no_legacy_witness w hr

/-- The whole type has an actual CK2 self-step through its actual closed major. -/
theorem covUHoType_self_step (n : Nat) (Γ : LCtx) :
    WhStepCK2 covUHoEnv n Γ covUHoType covUHoType :=
  .recMajor (m := covUHoRec) rfl rfl rfl covUHo_not_kFreeRec covUHo_not_kProjRec
    (covUOmega_self_step covUHoEnv n Γ (covUCycleX 63 66))

/-- Determinism excludes every finite native head readback, including recursor spines. -/
theorem covUHoType_no_normal_head (n : Nat) (Γ : LCtx) :
    ¬ ∃ N, RedR (WhStepCK2 covUHoEnv n) Γ covUHoType N ∧
      NormalR (WhStepCK2 covUHoEnv n) Γ N :=
  covU_no_normal_readback_of_self_step covUHoEnv_wf (covUHoType_self_step n Γ)

/-- Both admitted families have no indices, so the entire environment is K-free. -/
theorem covUHo_no_indexed (r : Nat) : ¬ IndexedPropRecT covUHoEnv r := by
  rintro ⟨w, _, _, hni⟩
  have hf := w.hfam
  have hk := w.hfamK
  have hz : piCount w.famMember.mtype = 0 := by
    rw [covUHoEnv_members] at hf
    split at hf
    · have he : w.famMember = covUHoParameter := (Option.some.inj hf).symm
      rw [he] at hk
      cases hk
    · split at hf
      · have he : w.famMember = covUHoRec := (Option.some.inj hf).symm
        rw [he] at hk
        cases hk
      · split at hf
        · have he : w.famMember = covUHoCtor := (Option.some.inj hf).symm
          rw [he] at hk
          cases hk
        · split at hf
          · have he : w.famMember = covUHoFam := (Option.some.inj hf).symm
            rw [he]
            rfl
          · split at hf
            · have he : w.famMember = pinLoopRecT := (Option.some.inj hf).symm
              rw [he] at hk
              cases hk
            · split at hf
              · have he : w.famMember = pinLoopMkT := (Option.some.inj hf).symm
                rw [he] at hk
                cases hk
              · split at hf
                · have he : w.famMember = pinLoopFamT := (Option.some.inj hf).symm
                  rw [he]
                  rfl
                · cases hf
  have hn := w.hnidx
  rw [hz] at hn
  exact hni (by omega)

def covUHoMinorCode : CptT := .lam [([], .lam [([], .prop)])]

theorem covUHoMinor_observed (ρ : EnvT) :
    ApproxT covUHoEnv ρ covUHoMinor covUHoMinorCode := by
  refine .lam (.bot _ _) (by intro s hs u hu; simp at hs; subst s; cases hu) ?_ ?_
  · exact ⟨(_, _), List.mem_singleton_self _, CptT.noConfusion⟩
  · intro s hs
    have he : s = ([], CptT.lam [([], .prop)]) := List.mem_singleton.mp hs
    subst s
    refine .lam (.bot _ _) (by intro s hs u hu; simp at hs; subst s; cases hu) ?_ ?_
    · exact ⟨(_, _), List.mem_singleton_self _, CptT.noConfusion⟩
    · intro s hs
      have he : s = ([], CptT.prop) := List.mem_singleton.mp hs
      subst s
      exact .sort _ .zero

/-- The offending legacy rule is non-strict in both the major and the HO field. -/
theorem covUHoType_approxT (ρ : EnvT) : ApproxT covUHoEnv ρ covUHoType .prop := by
  have hr : ApproxT covUHoEnv ρ (.const 65 [.succ (.succ .zero)])
      (curryStepT [[], [covUHoMinorCode], []] .prop) := by
    apply ApproxT.recursorProp (w := covUHoWitness) [.succ (.succ .zero)] rfl
      (us_pre := [[], [covUHoMinorCode]]) rfl
    change ApproxT covUHoEnv
      (EnvT.cons (demandT [])
        (EnvT.cons (demandT [covUHoMinorCode]) (EnvT.cons (demandT []) EnvT.bot)))
      (.app (.app (.bvar 1) (.bvar 0)) _) .prop
    refine .app (g := [([], .prop)]) (s := ([], .prop)) ?_
      (List.mem_singleton_self _) (by intro u hu; cases hu)
    refine .app (g := [([], .lam [([], .prop)])]) (s := ([], .lam [([], .prop)])) ?_
      (List.mem_singleton_self _) (by intro u hu; cases hu)
    exact .bvar (List.mem_singleton_self _)
  have h1 : ApproxT covUHoEnv ρ
      (.app (.const 65 [.succ (.succ .zero)]) covUHoMotive)
      (curryStepT [[covUHoMinorCode], []] .prop) :=
    .app hr (List.mem_singleton_self _) (by intro u hu; cases hu)
  have h2 : ApproxT covUHoEnv ρ
      (.app (.app (.const 65 [.succ (.succ .zero)]) covUHoMotive) covUHoMinor)
      (curryStepT [[]] .prop) := by
    apply ApproxT.app h1 (List.mem_singleton_self _)
    intro u hu
    have he : u = covUHoMinorCode := List.mem_singleton.mp hu
    subst u
    exact covUHoMinor_observed ρ
  exact .app h2 (List.mem_singleton_self _) (by intro u hu; cases hu)

/-- The actual ApproxTK `.free` arm admits the old non-strict observation. -/
theorem covUHoType_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK covUHoEnv n Γ ρ covUHoType .prop :=
  .free (kFreeT_of_no_indexed covUHo_no_indexed covUHoType) (covUHoType_approxT ρ)

theorem covUHoType_observed_stage (n : Nat) :
    ApproxTKStage covUHoEnv n 1 [] EnvT.bot covUHoType .prop :=
  ⟨covUHoType_observed n [] EnvT.bot, by simp [covTObservationBudget]⟩

/-- Every premise of the proposed head supplier is inhabited, at the same stage. -/
theorem covU_obs_sound_head_boundary (n : Nat) :
    Nonempty (EnvWfT covUHoEnv) ∧ Nonempty (CtxWfT covUHoEnv n []) ∧
    CovTRealized covUHoEnv n 1 [] EnvT.bot SubstT.id ∧
    EnvTypedFinAtT (ctxModelT_approxTK covUHoEnv n []) [] EnvT.bot ∧
    CtxEnvM (ctxModelT_approxTK covUHoEnv n []) [] EnvT.bot ∧
    Nonempty (HasTyT covUHoEnv n [] covUHoType (.sort (.succ .zero))) ∧
    ApproxTKStage covUHoEnv n 1 [] EnvT.bot covUHoType .prop ∧
    CptT.prop ≠ .bot ∧
    ¬ ∃ N, RedR (WhStepCK2 covUHoEnv n) [] covUHoType N ∧
      NormalR (WhStepCK2 covUHoEnv n) [] N :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, covU_realized_nil covUHoEnv n 1,
    envTypedFinAtT_nil _ _, (fun _ _ hv => Option.noConfusion hv),
    ⟨covUHoType_hasTy n []⟩, covUHoType_observed_stage n,
    CptT.noConfusion, covUHoType_no_normal_head n []⟩

/-- A necessary consequence of the requested realized, matching-head supply.
This asks only for a native normal readback; its head and trace are unrestricted. -/
def CovURealizedHeadSupply (E : ResolvedEnv) (arity stage : Nat) : Prop :=
  ∀ (Γ : LCtx) (ρ : EnvT) (σ : SubstT) (A : Expr Nat) (u : Level) (c : CptT),
    Nonempty (EnvWfT E) → Nonempty (CtxWfT E arity Γ) →
    Nonempty (HasTyT E arity Γ A (.sort u)) →
    EnvTypedFinAtT (ctxModelT_approxTK E arity Γ) Γ ρ →
    CtxEnvM (ctxModelT_approxTK E arity Γ) Γ ρ →
    CovTRealized E arity stage Γ ρ σ →
    ApproxTKStage E arity stage Γ ρ A c →
    Nonempty (HasTyT E arity [] (substT σ A) (.sort u)) →
    ApproxTKStage E arity stage [] EnvT.bot (substT σ A) c → c ≠ .bot →
    ∃ N, RedR (WhStepCK2 E arity) [] (substT σ A) N ∧
      NormalR (WhStepCK2 E arity) [] N

/-- The fully inhabited closed instance refutes even this weaker head-existence port. -/
theorem covU_no_realized_head_supply (n : Nat) :
    ¬ CovURealizedHeadSupply covUHoEnv n 1 := by
  intro hs
  have hsub : substT SubstT.id covUHoType = covUHoType := substT_id _
  have ht : Nonempty (HasTyT covUHoEnv n [] covUHoType (.sort (.succ .zero))) :=
    ⟨covUHoType_hasTy n []⟩
  have ho := covUHoType_observed_stage n
  have hn := hs [] EnvT.bot SubstT.id covUHoType (.succ .zero) .prop
    ⟨covUHoEnv_wf⟩ ⟨.nil⟩ ht (envTypedFinAtT_nil _ _)
    (fun _ _ hv => Option.noConfusion hv) (covU_realized_nil _ _ _) ho
    (by simpa only [hsub] using ht) (by simpa only [hsub] using ho) CptT.noConfusion
  rw [hsub] at hn
  exact covUHoType_no_normal_head n [] hn

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_U_SOUNDNESS_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMotive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoIhTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMajor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMajor_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_no_legacy_witness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_not_kFreeRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_not_kProjRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_self_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_no_normal_head
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHo_no_indexed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinorCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinor_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_approxT
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoType_observed_stage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_obs_sound_head_boundary
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.CovURealizedHeadSupply
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covU_no_realized_head_supply
-- END RCIC_NATIVE_TYPED_MODEL_COV_U_SOUNDNESS_ROOTS
