import rcic.RcicNativeTypedModelKControls

/-!
# Concrete inherited-interface failures of `ApproxTK`

The saturated repair admits the original positive Eq call while assigning
only bottom to its proper recursor prefixes.  Its old application inversion
therefore fails, even though ordinary application introduction is retained.

There is a separate, natively typed beta obstruction to global model
conversion soundness.  Passing the proper prefix through the identity
function erases every nonbottom observation in this model, while beta
conversion exposes the directly guarded call and its `.prop` observation.
The source type is extracted from the admitted gap's actual typing; no
choice, global adequacy premise, or new derivation induction is involved.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKFailureAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKControlAudit
open Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}

/-- The old raw beta-factorization input remains false on the unchanged
recursor-free Pi probe, for every frozen native context. -/
theorem not_modelBetaExpandT_approxTK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ¬ ModelBetaExpandT (ctxModelT_approxTK E n Γ) :=
  not_modelBetaExpandT_of_approxT_projection (fun h => approxTK_forget h)
    (approxTK_pi_bot_nil E n Γ EnvT.bot (.sort .zero) (.sort .zero))

/-- The actual five-argument function immediately preceding the positive
gap's neutral major. -/
def eqGapPrefix : Expr Nat :=
  foldApps (.const 65 [.succ (.succ .zero)]) eqGapW.preMajor

theorem eqGapRedex_eq_app_prefix : eqGapRedex = .app eqGapPrefix (.bvar 0) := rfl

theorem approxTK_eqGapPrefix_bot {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ eqGapPrefix c) : c = .bot :=
  approxTK_eqRec_fold_prefix_bot (by decide) h

/-- The positive guarded call refutes the exact old `app_inv` field. -/
theorem not_ctxModelTLaws_approxTK_eqGap (n : Nat) :
    ¬ CtxModelTLaws (ctxModelT_approxTK eqEnvT n eqGapCtx) := by
  apply not_ctxModelTLaws_of_bot_function
    (M := ctxModelT_approxTK eqEnvT n eqGapCtx) (ρ := EnvT.bot)
    (f := eqGapPrefix) (x := .bvar 0)
  · exact fun h => approxTK_eqGapPrefix_bot h
  · exact approxTK_eqGap_prop n EnvT.bot

theorem not_ctxModelTLaws'_approxTK_eqGap (n : Nat) :
    ¬ CtxModelTLaws' (ctxModelT_approxTK eqEnvT n eqGapCtx) :=
  fun h => not_ctxModelTLaws_approxTK_eqGap n h.toCtxModelTLaws

/-- Neither saturated computation constructor has a nonconstant head.
This reads only the actual source syntax stored in its certificate. -/
theorem not_saturatedComputationTK_of_nonconst_head {e : Expr Nat} {c : CptT}
    (hhead : ∀ r ls, (appsSpine e).1 ≠ .const r ls) :
    ¬ SaturatedComputationTK E n Γ ρ e c := by
  rintro (⟨w, he, _⟩ | ⟨w, x, he, _⟩)
  · have hh := congrArg (fun e => (appsSpine e).1) he
    simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const] at hh
    exact hhead _ _ hh
  · have hh := congrArg (fun e => (appsSpine e).1) he
    simp only [recCall, appsSpine_foldApps_const] at hh
    exact hhead _ _ hh

/-- Away from constant-headed syntax, a bottom-only function still
forces a bottom-only application, using the complete new inversion. -/
theorem approxTK_app_bot_of_function_bot {f x : Expr Nat} {c : CptT}
    (hhead : ∀ r ls, (appsSpine f).1 ≠ .const r ls)
    (hfun : ∀ {d : CptT}, ApproxTK E n Γ ρ f d → d = .bot)
    (h : ApproxTK E n Γ ρ (.app f x) c) : c = .bot := by
  rcases approxTK_app_inv h with hbot | ⟨g, s, _, hf, _⟩ |
    ⟨r, args, u, _, hf, _⟩ | hs
  · exact hbot
  · exact CptT.noConfusion (hfun hf)
  · exact CptT.noConfusion (hfun hf)
  · exact (not_saturatedComputationTK_of_nonconst_head
      (e := .app f x) (fun r ls => hhead r ls) hs).elim

/-- The identity function cannot transmit a nonbottom compact from an
argument whose new-model interpretation contains only bottom. -/
theorem approxTK_identity_app_bot {D f : Expr Nat} {c : CptT}
    (hfun : ∀ {d : CptT}, ApproxTK E n Γ ρ f d → d = .bot)
    (h : ApproxTK E n Γ ρ (.app (.lam D (.bvar 0)) f) c) : c = .bot := by
  rcases approxTK_app_inv h with hbot | ⟨g, s, hec, hfg, hs, hargs⟩ |
    ⟨r, args, u, _, hfg, _⟩ | hsat
  · exact hbot
  · rcases approxTK_lam_inv hfg with hbot | ⟨a, g', he, _, _, hb⟩
    · exact CptT.noConfusion hbot
    · injection he with hg
      subst g'
      rcases approxTK_bvar_inv (hb s hs).2 with hbot | hmem
      · exact hec.trans hbot
      · exact hec.trans (hfun (hargs s.2 hmem))
  · rcases approxTK_lam_inv hfg with hbot | ⟨a, g, he, _⟩
    · exact CptT.noConfusion hbot
    · exact CptT.noConfusion he
  · exact (not_saturatedComputationTK_of_nonconst_head
      (fun _ _ he => Expr.noConfusion he) hsat).elim

/-- The positive Eq call with its proper prefix first passed through
an explicitly annotated identity function. -/
def eqGapAlias (A B : Expr Nat) : Expr Nat :=
  .app (.app (.lam (.pi A B) (.bvar 0)) eqGapPrefix) (.bvar 0)

theorem approxTK_eqGapAlias_bot (A B : Expr Nat) {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ (eqGapAlias A B) c) : c = .bot :=
  approxTK_app_bot_of_function_bot (fun _ _ he => Expr.noConfusion he)
    (fun h => approxTK_identity_app_bot (fun h => approxTK_eqGapPrefix_bot h) h) h

/-- Native beta for an identity wrapper, at the function's actual type.
The only regularity call concerns the given native typing. -/
theorem native_identity_beta (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {f F : Expr Nat} (hf : HasTyT E n Γ f F) :
    Nonempty (ConvT E n Γ (.app (.lam F (.bvar 0)) f) f F) := by
  obtain ⟨u, hF⟩ := tySort hW hΓ hf
  have hb : HasTyT E n (.assumption F :: Γ) (.bvar 0) (lift 0 1 F) :=
    .bvar _ 0 _ rfl
  have hβ := ConvT.beta Γ F (.bvar 0) f (lift 0 1 F) u hF hb hf
  exact ⟨by simpa only [instantiate0, instantiate, if_pos rfl,
    instantiate_lift_id] using hβ⟩

/-- The binder annotation is extracted from the admitted positive gap's
actual application derivation.  The resulting beta conversion, source
collapse, and target observation are all kernel witnesses. -/
theorem eqGapAlias_native_beta_control (n : Nat) :
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx eqGapPrefix (.pi A B)) ∧
      Nonempty (ConvT eqEnvT n eqGapCtx (eqGapAlias A B) eqGapRedex
        (.sort (.succ .zero))) ∧
      (∀ ρ c, ApproxTK eqEnvT n eqGapCtx ρ (eqGapAlias A B) c → c = .bot) ∧
      (∀ ρ, ApproxTK eqEnvT n eqGapCtx ρ eqGapRedex .prop) := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨hc⟩ := eqGap_conv n
  have ht : HasTyT eqEnvT n eqGapCtx (.app eqGapPrefix (.bvar 0))
      (.sort (.succ .zero)) := (convEnds pinEqGroupWfT hΓ hc).2.1
  obtain ⟨A, B, hf, hx, hT⟩ := hasTyTInv_app ht rfl
  refine ⟨A, B, ⟨hf⟩, ?_, fun _ _ h => approxTK_eqGapAlias_bot A B h,
    approxTK_eqGap_prop n⟩
  obtain ⟨hβ⟩ := native_identity_beta pinEqGroupWfT hΓ hf
  exact ⟨convT_of_tyConv (.app eqGapCtx _ _ (.bvar 0) (.bvar 0) A B hβ
    (.refl _ _ _ hx)) hT⟩

/-- Global native conversion soundness fails for this repaired model,
already at the actual well-formed positive-gap context and a typed beta
conversion.  This is independent of a global fundamental supplier. -/
theorem not_native_conversion_sound_approxTK (n : Nat) :
    ¬ (∀ {a b A : Expr Nat}, ConvT eqEnvT n eqGapCtx a b A →
      ∀ ρ, ModelConvSoundAt (ctxModelT_approxTK eqEnvT n eqGapCtx) ρ a b) := by
  intro hsound
  obtain ⟨A, B, _, ⟨hβ⟩, hbot, hprop⟩ := eqGapAlias_native_beta_control n
  have hm := (hsound hβ EnvT.bot .prop).mpr (hprop EnvT.bot)
  exact CptT.noConfusion (hbot EnvT.bot .prop hm)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_FAILURE_ROOTS
#print axioms not_modelBetaExpandT_approxTK
#print axioms eqGapPrefix
#print axioms eqGapRedex_eq_app_prefix
#print axioms approxTK_eqGapPrefix_bot
#print axioms not_ctxModelTLaws_approxTK_eqGap
#print axioms not_ctxModelTLaws'_approxTK_eqGap
#print axioms not_saturatedComputationTK_of_nonconst_head
#print axioms approxTK_app_bot_of_function_bot
#print axioms approxTK_identity_app_bot
#print axioms eqGapAlias
#print axioms approxTK_eqGapAlias_bot
#print axioms native_identity_beta
#print axioms eqGapAlias_native_beta_control
#print axioms not_native_conversion_sound_approxTK
-- END RCIC_NATIVE_TYPED_MODEL_K_FAILURE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKFailureAudit
