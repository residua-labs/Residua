import rcic.RcicNativeTypedModelKFailure

/-!
# A typed beta-factorization obstruction for the saturated model

The argument is the actual, natively typed five-argument Eq prefix.  Its
new interpretation contains only bottom, so it satisfies the joint semantic
typing premise at a concrete code of its actual Pi type.  The instantiated
body is the positive guarded Eq call, which has `.prop`.  Nevertheless no
realized finite demand can give the variable-headed body that compact.

The direct beta conversion and the complete identity related-substitution
package are constructed at the existing well-formed, nonempty Eq context.
Thus neither native typing, joint semantic typing, nor the strengthened
environment-typing package removes this particular obstruction.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.PiProbeRelIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKControlAudit
open Rcic.Declarative.NativeValleys.TypedModelKFailureAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : EnvT}

/-- The context-indexed counterpart of the landed joint-typing premise. -/
def ArgTypedTK (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (ρ : EnvT)
    (arg A : Expr Nat) : Prop :=
  ∃ a, ApproxTK E n Γ ρ A a ∧
    ∀ u, ApproxTK E n Γ ρ arg u → CTyS E u a

/-- The typed finite-demand factorization, with the actual native binder
context in its body premise.  This is a named port, not an axiom. -/
def ModelBetaExpandTypedTK (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {ρ : EnvT} {A arg body : Expr Nat} {c : CptT},
    ArgTypedTK E n Γ ρ arg A → ApproxTK E n Γ ρ (instantiate0 arg body) c →
    ∃ (a : CptT) (us : List CptT), ApproxTK E n Γ ρ A a ∧
      (∀ u ∈ us, CTyS E u a) ∧ (∀ u ∈ us, ApproxTK E n Γ ρ arg u) ∧
      ApproxTK E n (.assumption A :: Γ) (EnvT.cons (demandT us) ρ) body c

/-- The joint-typing premise is inhabited, including a concrete nonbottom
code of the binder's Pi type. -/
theorem eqGapPrefix_argTypedTK (A B : Expr Nat) :
    ArgTypedTK eqEnvT n Γ ρ eqGapPrefix (.pi A B) := by
  refine ⟨.pi .bot [], approxTK_pi_bot_nil eqEnvT n Γ ρ A B, ?_⟩
  intro u hu
  rw [approxTK_eqGapPrefix_bot hu]
  exact ctyS_bot _

/-- Every realized demand on the proper prefix is bottom.  Consequently
the variable-headed body cannot carry the target's `.prop` observation. -/
theorem no_eqGap_typed_beta_factorization (D : Expr Nat) :
    ¬ ∃ (a : CptT) (us : List CptT), ApproxTK eqEnvT n Γ ρ D a ∧
      (∀ u ∈ us, CTyS eqEnvT u a) ∧
      (∀ u ∈ us, ApproxTK eqEnvT n Γ ρ eqGapPrefix u) ∧
      ApproxTK eqEnvT n (.assumption D :: Γ) (EnvT.cons (demandT us) ρ)
        (.app (.bvar 0) (.bvar 1)) .prop := by
  rintro ⟨a, us, _, _, hreal, hbody⟩
  have hf : ∀ {c : CptT},
      ApproxTK eqEnvT n (.assumption D :: Γ) (EnvT.cons (demandT us) ρ)
        (.bvar 0) c → c = .bot := by
    intro c hc
    rcases approxTK_bvar_inv hc with hbot | hmem
    · exact hbot
    · exact approxTK_eqGapPrefix_bot (hreal c hmem)
  exact CptT.noConfusion (approxTK_app_bot_of_function_bot
    (fun _ _ he => Expr.noConfusion he) hf hbody)

/-- The direct beta source uses the same native Pi annotation extracted
from the admitted gap, and abstracts its whole final application. -/
def eqGapDirectAlias (A B : Expr Nat) : Expr Nat :=
  .app (.lam (.pi A B) (.app (.bvar 0) (.bvar 1))) eqGapPrefix

theorem eqGapDirectAlias_contractum :
    instantiate0 eqGapPrefix (.app (.bvar 0) (.bvar 1)) = eqGapRedex := rfl

theorem not_approxTK_eqGapDirectAlias_prop (A B : Expr Nat) :
    ¬ ApproxTK eqEnvT n Γ ρ (eqGapDirectAlias A B) .prop := by
  intro h
  rcases approxTK_app_inv h with hbot | ⟨g, s, hec, hfg, hs, hargs⟩ |
    ⟨r, args, u, he, _⟩ | hsat
  · exact CptT.noConfusion hbot
  · rcases approxTK_lam_inv hfg with hbot | ⟨a, g', he, hA, _, hb⟩
    · exact CptT.noConfusion hbot
    · injection he with hg
      subst g'
      have hbody := (hb s hs).2
      rw [← hec] at hbody
      exact no_eqGap_typed_beta_factorization (.pi A B)
        ⟨a, s.1, hA, (hb s hs).1, hargs, hbody⟩
  · exact CptT.noConfusion he
  · exact not_saturatedComputationTK_of_nonconst_head
      (fun _ _ he => Expr.noConfusion he) hsat

/-- The counterexample also admits the actual native binder type, a
direct native beta derivation, joint semantic typing at that binder type,
and the positive target observation. -/
theorem eqGapDirectAlias_native_beta_control (n : Nat) :
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx eqGapPrefix (.pi A B)) ∧
      Nonempty (ConvT eqEnvT n eqGapCtx (eqGapDirectAlias A B) eqGapRedex
        (.sort (.succ .zero))) ∧
      (∀ ρ, ArgTypedTK eqEnvT n eqGapCtx ρ eqGapPrefix (.pi A B)) ∧
      (∀ ρ, ApproxTK eqEnvT n eqGapCtx ρ eqGapRedex .prop ∧
        ¬ ApproxTK eqEnvT n eqGapCtx ρ (eqGapDirectAlias A B) .prop) := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨hc⟩ := eqGap_conv n
  have ht : HasTyT eqEnvT n eqGapCtx (.app eqGapPrefix (.bvar 0))
      (.sort (.succ .zero)) := (convEnds pinEqGroupWfT hΓ hc).2.1
  obtain ⟨A, B, hf, hx, hT⟩ := hasTyTInv_app ht rfl
  obtain ⟨u, hF⟩ := tySort pinEqGroupWfT hΓ hf
  let F : Expr Nat := .pi A B
  have hx' : HasTyT eqEnvT n (.assumption F :: eqGapCtx)
      (.bvar 1) (lift 0 1 A) := by
    simpa only [insertAt_zero] using
      hasTyTWeaken (.assumption F) (envClosed_of_envWfT pinEqGroupWfT) (c := 0) hx
  have hvar : HasTyT eqEnvT n (.assumption F :: eqGapCtx) (.bvar 0)
      (.pi (lift 0 1 A) (lift 1 1 B)) := .bvar _ 0 _ rfl
  have hb : HasTyT eqEnvT n (.assumption F :: eqGapCtx)
      (.app (.bvar 0) (.bvar 1)) (lift 0 1 (instantiate0 (.bvar 0) B)) := by
    have hcomm := lift_instantiate_low 1 0 0 (Expr.bvar 0) (Nat.le_refl 0) B
    change lift 0 1 (instantiate0 (.bvar 0) B) =
      instantiate0 (.bvar 1) (lift 1 1 B) at hcomm
    rw [hcomm]
    exact .app _ _ _ _ _ hvar hx'
  have hβ := ConvT.beta eqGapCtx F (.app (.bvar 0) (.bvar 1)) eqGapPrefix
    (lift 0 1 (instantiate0 (.bvar 0) B)) u hF hb hf
  have hi : instantiate0 eqGapPrefix (lift 0 1 (instantiate0 (.bvar 0) B)) =
      instantiate0 (.bvar 0) B := instantiate_lift_id _ _ _
  rw [eqGapDirectAlias_contractum, hi] at hβ
  refine ⟨A, B, ⟨hf⟩, ⟨convT_of_tyConv hβ hT⟩,
    fun _ => eqGapPrefix_argTypedTK A B, ?_⟩
  exact fun ρ => ⟨approxTK_eqGap_prop n ρ, not_approxTK_eqGapDirectAlias_prop A B⟩

/-- The exact strengthened semantic beta input is false at the actual
native binder type extracted above, with both semantic premises inhabited. -/
theorem not_modelBetaExpandTypedTK_eqEnv (n : Nat) :
    ¬ ModelBetaExpandTypedTK eqEnvT n := by
  intro hβ
  obtain ⟨A, B, _, _, harg, hobs⟩ := eqGapDirectAlias_native_beta_control n
  have hm : ApproxTK eqEnvT n eqGapCtx EnvT.bot
      (instantiate0 eqGapPrefix (.app (.bvar 0) (.bvar 1))) .prop :=
    (hobs EnvT.bot).1
  exact no_eqGap_typed_beta_factorization (.pi A B) (hβ (harg EnvT.bot) hm)

/-- The bottom valuation is typed for the new carrier at every source
context, since every type still has bottom and bottom has every compact type. -/
theorem envTypedAtT_approxTK_bot (E : ResolvedEnv) (n : Nat) (Γ Δ : LCtx) :
    EnvTypedAtT (ctxModelT_approxTK E n Γ) Δ EnvT.bot := by
  intro i A _ c hc
  have he : c = .bot := hc
  subst c
  exact ⟨.bot, .bot _ _ _, ctyS_bot _⟩

/-- The strengthened related-substitution package is inhabited at the
same actual nonempty native context used by the typed beta counterexample. -/
theorem eqGap_typed_identity_approxTK (R : Readback) (n : Nat) :
    RelSubstTypedAtT (ctxModelT_approxTK eqEnvT n eqGapCtx) R n eqGapCtx
      EnvT.bot EnvT.bot SubstT.id SubstT.id eqGapCtx :=
  ⟨relSubstIdT_eqGap_bot (ctxModelT_approxTK eqEnvT n eqGapCtx) R n,
    envTypedAtT_approxTK_bot eqEnvT n eqGapCtx eqGapCtx,
    envTypedAtT_approxTK_bot eqEnvT n eqGapCtx eqGapCtx⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_TYPED_BETA_ROOTS
#print axioms ArgTypedTK
#print axioms ModelBetaExpandTypedTK
#print axioms eqGapPrefix_argTypedTK
#print axioms no_eqGap_typed_beta_factorization
#print axioms eqGapDirectAlias
#print axioms eqGapDirectAlias_contractum
#print axioms not_approxTK_eqGapDirectAlias_prop
#print axioms not_modelBetaExpandTypedTK_eqEnv
#print axioms eqGapDirectAlias_native_beta_control
#print axioms envTypedAtT_approxTK_bot
#print axioms eqGap_typed_identity_approxTK
-- END RCIC_NATIVE_TYPED_MODEL_K_TYPED_BETA_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit
