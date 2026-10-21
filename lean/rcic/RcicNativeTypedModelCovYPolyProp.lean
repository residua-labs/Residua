import rcic.RcicNativeTypedModelCovYCore
import rcic.RcicNativeTypedModelCovXBoundary

/-!
# The impredicative lambda at a finite semantic type code

The domain of `covXPolyPropLam` is the unchanged impredicative proposition.
Its compact TYPE code uses bottom at that domain and one actual sort output
row. Every observation of the lambda has only bottom argument demands; this
is derived from the landed proposition-code theorem, not assumed. Thus the
complete family of lambda observations has a common code and ordinary actions.

The old eager-view refutation remains true. No finite native view is built or
assumed, and no observation/model statement is altered. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYPolyPropAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovRelAudit TypedModelCovRelEscapeAudit TypedModelCovNormCov2Audit
open TypedModelCovXAudit TypedModelCovYAudit

/-- A finite actual type code with no eager domain traversal. -/
def covYPolyPropCode : CptT := .pi .bot [([], .sort)]

theorem approxTK_covYPolyPropCode (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK eqEnvT n Γ ρ covXPolyPropLamTy covYPolyPropCode := by
  refine ApproxTK.pi (.bot _ _ _) ?_ ?_
  · intro row hr u hu
    obtain rfl := List.mem_singleton.mp hr
    exact (List.not_mem_nil _ hu).elim
  · intro row hr
    obtain rfl := List.mem_singleton.mp hr
    simpa only [TypingFin.sortCode_succ] using
      approxTK_sort_code eqEnvT n (.assumption idPiProp :: Γ)
        (EnvT.cons (demandT []) ρ) (.succ .zero)

/-- Actual observations have only bottom argument demands and bottom/Prop
outputs. Both claims follow by inversion of the same model derivation. -/
theorem covY_polyProp_observation {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ covXPolyPropLam c) :
    c = .bot ∨ ∃ g : List (List CptT × CptT), c = .lam g ∧
      (∀ row ∈ g, ∀ u ∈ row.1, u = .bot) ∧
      ∀ row ∈ g, row.2 = .bot ∨ row.2 = .prop := by
  rcases approxTK_lam_inv h with hb | ⟨a, g, he, hA, _, hbody⟩
  · exact Or.inl hb
  · refine Or.inr ⟨g, he, ?_, ?_⟩
    · intro row hr u hu
      exact ctyS_prop_bot (isPropCT_of_approxT_idPiProp (approxTK_forget hA))
        ((hbody row hr).1 u hu)
    · intro row hr
      simpa only [sortCode_zero] using approxTK_sort_inv (hbody row hr).2

/-- The existing strict typing judgment already supplies this common code.
The new covariant gate is obtained by the imported inclusion only. -/
theorem covY_polyProp_code_typed (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ covXPolyPropLam c) : C.ty c covYPolyPropCode := by
  rcases covY_polyProp_observation h with rfl | ⟨g, rfl, hd, ho⟩
  · exact C.bot _
  · apply hS
    rw [covYPolyPropCode, CTyS]
    refine Or.inr ⟨g, rfl, ?_, ?_, ?_, ?_⟩
    · intro hp
      cases hp with
      | pi _ hs => exact not_isPropCT_sort eqEnvT (hs ([], .sort)
          (List.mem_singleton.mpr rfl))
    · intro row hr u hu
      rw [hd row hr u hu]
      exact ctyS_bot _
    · intro row hr s hs _
      obtain rfl := List.mem_singleton.mp hs
      rcases ho row hr with hb | hp
      · rw [hb]; exact ctyS_bot _
      · rw [hp]; exact ctyS_prop_sort eqEnvT
    · intro row hr
      exact Or.inr ⟨([], .sort), List.mem_singleton.mpr rfl,
        fun _ hu => (List.not_mem_nil _ hu).elim⟩

theorem covY_polyProp_action_shape {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ covXPolyPropLam c)
    {ds : List CptT} {out : CptT} (ha : CovXCompactAction eqEnvT c ds out) :
    out = .bot ∨ out = .prop := by
  rcases covY_polyProp_observation h with rfl | ⟨g, rfl, hd, ho⟩
  · cases ha with
    | bot => exact Or.inl rfl
  · cases ha with
    | bot => exact Or.inl rfl
    | app hs _ => exact ho _ hs

/-- The only codomain row covers every actual action; this is a proved
coverage fact, including actions at every typed finite demand list. -/
theorem covY_polyProp_coverage (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ covXPolyPropLam c) :
    CovYActionCoverage C c .bot [([], .sort)] := by
  intro ds out ha _
  rcases covY_polyProp_action_shape h ha with hb | rfl
  · exact Or.inl hb
  · exact Or.inr ⟨([], .sort), List.mem_singleton.mpr rfl,
      (fun _ hu => (List.not_mem_nil _ hu).elim), hS _ _ (ctyS_prop_sort eqEnvT)⟩

/-- Reuse the landed positive one-layer behavior at the exact native
function, extracting its actual sort-view payload by view coherence. -/
theorem covY_polyProp_app_prop (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (Γ : LCtx) (N N' : Expr Nat) :
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n Γ
      (.app covXPolyPropLam N) (.app covXPolyPropLam N')
      (.sort (.succ .zero)) .prop .sort := by
  have ha : CovXCompactAction eqEnvT (.lam [([], .prop)]) [] .prop :=
    .app (List.mem_singleton_self _) (fun _ hu => (List.not_mem_nil _ hu).elim)
  have h := covXPolyPropLam_one_layer_action C hS n Γ [] .prop ha N N'
  have hv := (lrSCoreCovX_iff_at_view C (readbackLaws_whStepCK2 eqEnvT n)
    (normalUniqueR_whStepCK2 pinEqGroupWfT)
    (CovXTypeView.sort (.succ .zero) (RedR.refl (.sort (.succ .zero)))) .prop).mp h
  apply lrSCoreCovY_of_old_leaf C (fun _ _ h => CptT.noConfusion h)
    (hS _ _ (ctyS_prop_sort eqEnvT))
  exact hv.2

/-- All actual compact observations of this lambda are related at one finite
type code, in every target native context. The impossible eager view is absent. -/
theorem covY_polyProp_related_observed (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (Ξ Γ : LCtx) (ρ : EnvT) (c : CptT)
    (h : ApproxTK eqEnvT n Ξ ρ covXPolyPropLam c) :
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n Γ covXPolyPropLam covXPolyPropLam
      covXPolyPropLamTy c covYPolyPropCode := by
  rw [covYPolyPropCode, lrSCoreCovY_pi_iff]
  refine ⟨covY_polyProp_code_typed C hS h, Or.inr ⟨idPiProp,
    .sort (.succ .zero), .refl _, covY_polyProp_coverage C hS h, ?_⟩⟩
  intro ds out ha row hr _ N N' _ _ _ _
  obtain rfl := List.mem_singleton.mp hr
  rcases covY_polyProp_action_shape h ha with rfl | rfl
  · exact ⟨lrSCoreCovY_bot C _ _ _ _ _, lrSCoreCovY_bot C _ _ _ _ _⟩
  · exact ⟨covY_polyProp_app_prop C hS n Γ N N', covY_polyProp_app_prop C hS n Γ N N'⟩

/-- At the precise old non-bottom fixture, the repaired relation and the old
eager-view exclusion coexist. This is a concrete supply, not a view premise. -/
theorem covY_polyProp_relation_changed (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (Γ : LCtx) :
    LRSCoreCovY C (WhStepCK2 eqEnvT n) n Γ covXPolyPropLam covXPolyPropLam
      covXPolyPropLamTy (.lam [([], .prop)]) covYPolyPropCode ∧
    ¬ Nonempty (CovXTypeView eqEnvT (WhStepCK2 eqEnvT n) n Γ idPiProp) :=
  ⟨covY_polyProp_related_observed C hS n Γ Γ EnvT.bot _
      (covXPolyPropLam_observed n Γ EnvT.bot), not_covXTypeView_idPiProp_eq n Γ⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_POLY_PROP_ROOTS
#print axioms covYPolyPropCode
#print axioms approxTK_covYPolyPropCode
#print axioms covY_polyProp_observation
#print axioms covY_polyProp_code_typed
#print axioms covY_polyProp_action_shape
#print axioms covY_polyProp_coverage
#print axioms covY_polyProp_app_prop
#print axioms covY_polyProp_related_observed
#print axioms covY_polyProp_relation_changed
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_POLY_PROP_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYPolyPropAudit
