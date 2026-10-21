import rcic.RcicNativeTypedModelKControls

/-!
# Typed positive controls and the native eta boundary

The source observation needed by the saturated rule is constructed below,
including in the admitted delta extension.  No global iota or Fundamental
supplier is assumed.  The two environments required for nondegeneracy have
actual native terms, non-bottom observations and semantic typing witnesses.

The eta control is a negative for the additional DI certificate, not for
the imported native K rule.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKGuardAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKControlAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}

private theorem oldEq_sort_minor_extend (hE : ExtendsEqEnv E)
    (ρ : EnvT) (ls : List Level) (A a mot b major : Expr Nat) :
    ApproxT E ρ (recCall (.const 65 ls) [A, a, mot, .sort .zero, b] major) .prop := by
  obtain ⟨w, hw⟩ := eqRec_structured_exists
  obtain ⟨hP, hpre, hfields, hschema⟩ := eqRec_model_schema w hw
  let w' := extWitnessS hE w
  let us : List (List CptT) := [[], [], [], [.prop], []]
  have hc : ApproxT E ρ (.const 65 ls) (curryStepT (us ++ [[]]) .prop) := by
    rw [← hw]
    apply ApproxT.recursorProp (w := w') ls hP
    · exact hpre.symm
    · change ApproxT E (EnvT.pushArgs ((us ++ w.fields.map (fun _ => [])).map demandT)
        EnvT.bot) (instantiateLevels ls w.schema) .prop
      rw [hfields, List.map_nil, List.append_nil, hschema]
      exact .bvar (show CptT.prop ∈ [.prop] from List.mem_singleton.mpr rfl)
  have empty : ∀ {f x : Expr Nat} {c : CptT},
      ApproxT E ρ f (.lam [([], c)]) → ApproxT E ρ (.app f x) c := by
    intro f x c hf
    exact .app hf (List.mem_singleton.mpr rfl)
      (fun _ h => (List.not_mem_nil _ h).elim)
  have hm : ApproxT E ρ
      (.app (.app (.app (.app (.const 65 ls) A) a) mot) (.sort .zero))
      (curryStepT [[], []] .prop) := by
    apply ApproxT.app (empty (empty (empty hc))) (List.mem_singleton.mpr rfl)
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact approxT_sort_code E ρ .zero
  exact empty (empty hm)

/-- The source filter of the saturated constructor is inhabited throughout
the actual Eq extension controls.  The remaining inputs are exactly its gates. -/
theorem approxTK_eq_sort_minor (hE : ExtendsEqEnv E) (ρ : EnvT)
    (A a mot b : Expr Nat)
    (hi : KIndexGuardAt E n Γ (eqConvW hE A a b mot (.sort .zero)))
    (hc : KCommonAt E n Γ (eqConvW hE A a b mot (.sort .zero)) (.bvar 0)) :
    ApproxTK E n Γ ρ
      (recCall (.const 65 [.succ (.succ .zero)]) [A, a, mot, .sort .zero, b] (.bvar 0))
      .prop :=
  .recursorPropK (eqConvW hE A a b mot (.sort .zero)) (.bvar 0)
    (.inl ⟨rfl, rfl, rfl⟩) not_isCtorSpine_bvar hi hc
    (oldEq_sort_minor_extend hE ρ _ A a mot b (.bvar 0))
    (approxTK_sort_code E n Γ ρ .zero)

theorem approxTK_binder_prop (n : Nat) (ρ : EnvT) :
    ApproxTK eqEnvT n binderEqCtx ρ binderIndexRedex .prop := by
  apply approxTK_eq_sort_minor (fun _ _ h => h) ρ indexFn indexId binderIndexMot
    indexBinderBeta (kIndexGuardAt_binder n)
  exact (eqKGate_of_indexConv (fun _ _ h => h) binderIndexMot (.sort .zero)
    (indexFnTy eqEnvT n binderEqCtx) (indexIdTy eqEnvT n binderEqCtx)
    (indexBinderBetaTy eqEnvT n binderEqCtx) (.bvar binderEqCtx 0 _ rfl)
    (indexBinderBetaConv eqEnvT n binderEqCtx)).2

theorem approxTK_delta_prop (n : Nat) (ρ : EnvT) :
    ApproxTK deltaEqEnv n deltaHeadEqCtx ρ (deltaRedex (.const 66 [])) .prop := by
  apply approxTK_eq_sort_minor deltaEqExtends ρ indexFn indexId binderIndexMot
    (.const 66 []) (kIndexGuardAt_delta n)
  exact (eqKGate_of_indexConv deltaEqExtends binderIndexMot (.sort .zero)
    (indexFnTy deltaEqEnv n deltaHeadEqCtx) (indexIdTy deltaEqEnv n deltaHeadEqCtx)
    (deltaConstTy n deltaHeadEqCtx) (.bvar deltaHeadEqCtx 0 _ rfl)
    (deltaIndexConv n deltaHeadEqCtx)).2

theorem approxTK_delta_under_binder_prop (n : Nat) (ρ : EnvT) :
    ApproxTK deltaEqEnv n deltaUnderBinderEqCtx ρ (deltaRedex deltaBinderIndex) .prop := by
  apply approxTK_eq_sort_minor deltaEqExtends ρ indexFn indexId binderIndexMot
    deltaBinderIndex (kIndexGuardAt_delta_under_binder n)
  exact (eqKGate_of_indexConv deltaEqExtends binderIndexMot (.sort .zero)
    (indexFnTy deltaEqEnv n deltaUnderBinderEqCtx)
    (indexIdTy deltaEqEnv n deltaUnderBinderEqCtx)
    (deltaBinderTy n deltaUnderBinderEqCtx) (.bvar deltaUnderBinderEqCtx 0 _ rfl)
    (deltaBinderIndexConv n deltaUnderBinderEqCtx)).2

/-- The complete new grammar rejects the native eta control, rather than
only rejecting one selected canonical witness. -/
theorem approxTK_etaIndexRedex_bot {c : CptT}
    (h : ApproxTK eqEnvT n etaEqCtx ρ etaIndexRedex c) : c = .bot := by
  rcases approxTK_eqRec_bvar_inv (by decide) h with hb | ⟨w, hr, hp, hk, hi⟩
  · exact hb
  · exact (not_indexAgreementDI_eta hr hp hk hi.2).elim

/-- The native eta redex is fully typed and natively converts to Sort zero,
but the bounded candidate observes only bottom. -/
theorem typed_eta_model_boundary (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n etaEqCtx) ∧
    Nonempty (ConvT eqEnvT n etaEqCtx etaIndexRedex (.sort .zero)
      (.sort (.succ .zero))) ∧
    KNativeHead eqEnvT n etaEqCtx etaIndexRedex (.sort .zero) ∧
    (∀ c, ApproxTK eqEnvT n etaEqCtx ρ etaIndexRedex c → c = .bot) ∧
    ApproxTK eqEnvT n etaEqCtx ρ (.sort .zero) .prop :=
  ⟨⟨pinEqGroupWfT⟩, ⟨etaEqCtxWf n⟩, ⟨etaIndexRedexConv n⟩,
    kNativeHead_eta n, fun _ h => approxTK_etaIndexRedex_bot h,
    approxTK_sort_code eqEnvT n etaEqCtx ρ .zero⟩

/-- A fully typed native conversion refutes global model conversion
invariance independently of the separate beta-alias obstruction. -/
theorem not_native_eta_model_sound (n : Nat) :
    ¬ (∀ {a b A : Expr Nat}, ConvT eqEnvT n etaEqCtx a b A →
      ∀ ρ, ModelConvSoundAt (ctxModelT_approxTK eqEnvT n etaEqCtx) ρ a b) := by
  intro h
  have hp := (h (etaIndexRedexConv n) EnvT.bot .prop).mpr
    (approxTK_sort_code eqEnvT n etaEqCtx EnvT.bot .zero)
  exact CptT.noConfusion (approxTK_etaIndexRedex_bot hp)

/-- The exact typed native computation port a complete K model would need.
The source and result must both be natively typed at the same type, in an
admitted environment and well-formed context.  There is no DI or old-model
source filter in this obligation. -/
def TypedNativeKForwardTK (E : ResolvedEnv) (n : Nat) : Prop :=
  EnvWfT E → ∀ {Γ : LCtx} {src dst A : Expr Nat}, CtxWfT E n Γ →
    HasTyT E n Γ src A → HasTyT E n Γ dst A → KNativeHead E n Γ src dst →
      ∀ {ρ : EnvT} {c : CptT}, ApproxTK E n Γ ρ dst c → ApproxTK E n Γ ρ src c

/-- The exact typed native-forward port is false for this bounded candidate.
The fully admitted eta control satisfies every native hypothesis. -/
theorem not_typedNativeKForwardTK_eqEnv (n : Nat) :
    ¬ TypedNativeKForwardTK eqEnvT n := by
  intro h
  have ht := convEnds pinEqGroupWfT (etaEqCtxWf n) (etaIndexRedexConv n)
  have hp := h pinEqGroupWfT (etaEqCtxWf n) ht.1 ht.2.1 (kNativeHead_eta n)
    (approxTK_sort_code eqEnvT n etaEqCtx EnvT.bot .zero)
  exact CptT.noConfusion (approxTK_etaIndexRedex_bot hp)

private theorem apartRight_kFree : KFreeT eqEnvT apartRight := by
  have hp : KFreeT eqEnvT idPiProp := kFreeT_pi (kFreeT_sort eqEnvT .zero)
    (kFreeT_bvar eqEnvT 0)
  have hEq : KFreeT eqEnvT (.const 63 []) := kFreeT_rigid_const
    (rigidConst_of_inductiveM pinEqGroupWfT (r := 63) (m := eqFamT) rfl rfl) []
  exact kFreeT_app (kFreeT_app (kFreeT_app hEq (kFreeT_sort eqEnvT .zero)) hp) hp

/-- Nondegeneracy at the admitted Eq environment: the closed family-headed
proposition retains an actual, typed, non-bottom spine observation. -/
theorem eq_typed_compact_controlTK (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT eqEnvT) ∧
      TypedCompactWitnessT (ctxModelT_approxTK eqEnvT n []) n [] ρ
        apartRight (.sort .zero) (.spine 63 [.bot, .bot, .bot]) .prop := by
  obtain ⟨hE, h⟩ := eq_typed_compact_control n ρ
  exact ⟨hE, (typedCompactWitnessT_congr
    (modelAgreementAtT_kFree apartRight_kFree)
    (modelAgreementAtT_kFree (kFreeT_sort eqEnvT .zero))).mpr h⟩

/-- Nondegeneracy at natEnvUWfT uses the actual zero constructor, its Nat
family code and semantic compact typing; neither compact is bottom. -/
theorem nat_typed_compact_controlTK (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT natEnvU) ∧
      TypedCompactWitnessT (ctxModelT_approxTK natEnvU n []) n [] ρ
        (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) := by
  obtain ⟨hE, h⟩ := nat_typed_compact_control n ρ
  exact ⟨hE, (typedCompactWitnessT_congr
    (modelAgreementAtT_kFree (kFreeT_natEnvU (.const 1 [])))
    (modelAgreementAtT_kFree (kFreeT_natEnvU (.const 0 [])))).mpr h⟩

/-- The repaired positive K observation itself is nondegenerate and typed,
at the original nonempty context and its actual result universe. -/
theorem eqGap_typed_compact_controlTK (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT eqEnvT) ∧
      TypedCompactWitnessT (ctxModelT_approxTK eqEnvT n eqGapCtx) n eqGapCtx ρ
        eqGapRedex (.sort (.succ .zero)) .prop .sort := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨hc⟩ := eqGap_conv n
  exact ⟨⟨pinEqGroupWfT⟩, ⟨hΓ⟩, ⟨(convEnds pinEqGroupWfT hΓ hc).2.1⟩,
    approxTK_eqGap_prop n ρ, approxTK_sort_code eqEnvT n eqGapCtx ρ (.succ .zero),
    (by rw [CTyS]; exact Or.inr TyCodeCT.prop), fun h => CptT.noConfusion h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_POSITIVE_ROOTS
#print axioms approxTK_eq_sort_minor
#print axioms approxTK_binder_prop
#print axioms approxTK_delta_prop
#print axioms approxTK_delta_under_binder_prop
#print axioms approxTK_etaIndexRedex_bot
#print axioms typed_eta_model_boundary
#print axioms not_native_eta_model_sound
#print axioms TypedNativeKForwardTK
#print axioms not_typedNativeKForwardTK_eqEnv
#print axioms eq_typed_compact_controlTK
#print axioms nat_typed_compact_controlTK
#print axioms eqGap_typed_compact_controlTK
-- END RCIC_NATIVE_TYPED_MODEL_K_POSITIVE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit
