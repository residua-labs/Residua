import rcic.RcicNativeTypedModelKTypedBeta
import rcic.RcicNativeReadbackCK2

/-!
# The direction of function-variable propagation

This leaf separates a source-to-contractum model obligation from expansion
of the logical relation.  The generic conversion adapter needs only
preservation of observations already present at the source, a readback of
the substituted source, and the contractum's `FundTyAt` supplier.  The last
input is explicit: the contractum is not generally a child of the original
typing derivation.  No global Fundamental supplier is constructed here.

The concrete model theorem contracts the direct function-variable beta
pattern for every argument and compact.  It reads no compact-typing premise,
so changing the demand typing does not alter its argument provided the
same application, lambda, variable and nonconstant-head inversion rules
are available.  The actual typed Eq alias then gives strict one-way model
preservation and a positive `.prop` relation witness.  The source still has
only bottom; relation expansion supplies no missing model observation.

All landed observations and definitions are unchanged.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKFailureAudit
open Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat} {Γ : LCtx} {ρ : EnvT}

/-- A conversion link from one-way model preservation and a contractum
diagonal.  Readback is requested in the actual related target context;
no raw substitution stability of a native K step is assumed. -/
theorem fundConvAt_of_model_contractT (hL : ReadbackLaws E R)
    {M : CtxModelT E} {src dst A : Expr Nat}
    (hpres : ∀ ρ c, M.Ap ρ src c → M.Ap ρ dst c)
    (hread : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      CtxWfT E n Δ → RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
      RedR R Δ (substT σ src) (substT σ dst))
    (htarget : FundTyAt M R n Γ dst A) :
    FundConvAt M R n Γ src dst A := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  apply lrSCoreS_expand_red hL (hread hΔ hS) c
  apply htarget hΔ hS c
  exact hc.elim (fun h => Or.inl (hpres ρ c h)) Or.inr

/-- Beta expansion belongs to `LRSCoreS` once the contractum diagonal is
supplied.  The model input runs from the beta source to the contractum,
the opposite direction from `ModelBetaExpandT`. -/
theorem fundConvAt_beta_of_model_contractT (hL : ReadbackLaws E R)
    {M : CtxModelT E} {D body arg A : Expr Nat}
    (hpres : ∀ ρ c, M.Ap ρ (.app (.lam D body) arg) c →
      M.Ap ρ (instantiate0 arg body) c)
    (htarget : FundTyAt M R n Γ (instantiate0 arg body) A) :
    FundConvAt M R n Γ (.app (.lam D body) arg) (instantiate0 arg body) A := by
  have hread : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      CtxWfT E n Δ → RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
      RedR R Δ (substT σ (.app (.lam D body) arg))
        (substT σ (instantiate0 arg body)) := by
    intro Δ ρ ρ' σ σ' _ _
    simpa only [substT, substT_instantiate0] using
      (redR_single (hL.beta Δ (substT σ D) (substT σ.up body) (substT σ arg)))
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact fundConvAt_of_model_contractT hL (A := A) hpres hread htarget hΔ hS c hc

private theorem approxTK_function_body_realize {D f : Expr Nat}
    {us : List CptT} {c : CptT}
    (hreal : ∀ u ∈ us, ApproxTK E n Γ ρ f u)
    (hbody : ApproxTK E n (.assumption D :: Γ)
      (EnvT.cons (demandT us) ρ) (.app (.bvar 0) (.bvar 1)) c) :
    ApproxTK E n Γ ρ (.app f (.bvar 0)) c := by
  have hfun : ∀ {d : CptT}, ApproxTK E n (.assumption D :: Γ)
      (EnvT.cons (demandT us) ρ) (.bvar 0) d → ApproxTK E n Γ ρ f d := by
    intro d hd
    rcases approxTK_bvar_inv hd with hbot | hmem
    · rw [hbot]
      exact .bot _ _ _
    · exact hreal d hmem
  have harg : ∀ {d : CptT}, ApproxTK E n (.assumption D :: Γ)
      (EnvT.cons (demandT us) ρ) (.bvar 1) d →
        ApproxTK E n Γ ρ (.bvar 0) d := by
    intro d hd
    rcases approxTK_bvar_inv hd with hbot | hmem
    · rw [hbot]
      exact .bot _ _ _
    · exact (approxTK_bvar_iff 0 d).mpr (Or.inr hmem)
  rcases approxTK_app_inv hbody with hbot | ⟨g, s, he, hf, hs, hx⟩ |
    ⟨r, args, u, he, hf, hx⟩ | hsat
  · rw [hbot]
    exact .bot _ _ _
  · rw [he]
    exact .app (hfun hf) hs (fun u hu => harg (hx u hu))
  · rw [he]
    exact .appSpine (hfun hf) (harg hx)
  · exact (not_saturatedComputationTK_of_nonconst_head
      (fun _ _ he => Expr.noConfusion he) hsat).elim

/-- Every observation already present at a function-variable beta source
survives contraction.  This is uniform in the annotation, function argument,
native context, semantic environment and compact. -/
theorem approxTK_function_variable_beta_contract {D f : Expr Nat} {c : CptT}
    (h : ApproxTK E n Γ ρ (.app (.lam D (.app (.bvar 0) (.bvar 1))) f) c) :
    ApproxTK E n Γ ρ (.app f (.bvar 0)) c := by
  rcases approxTK_app_inv h with hbot | ⟨g, s, hec, hf, hs, hargs⟩ |
    ⟨r, args, u, _, hf, _⟩ | hsat
  · rw [hbot]
    exact .bot _ _ _
  · rcases approxTK_lam_inv hf with hbot | ⟨a, g', he, _, _, hb⟩
    · exact (CptT.noConfusion hbot : False).elim
    · injection he with hg
      subst g'
      rw [hec]
      exact approxTK_function_body_realize hargs (hb s hs).2
  · rcases approxTK_lam_inv hf with hbot | ⟨a, g, he, _⟩
    · exact (CptT.noConfusion hbot : False).elim
    · exact (CptT.noConfusion he : False).elim
  · exact (not_saturatedComputationTK_of_nonconst_head
      (fun _ _ he => Expr.noConfusion he) hsat).elim

/-- Even after removing every compact-typing requirement, no finite
demand realized by the proper Eq prefix can observe this variable-headed
body at `.prop`.  A change of demand typing alone cannot supply the
missing function compact while these observations stay fixed. -/
theorem no_eqGap_realized_beta_factorization (D : Expr Nat) :
    ¬ ∃ us : List CptT,
      (∀ u ∈ us, ApproxTK eqEnvT n Γ ρ eqGapPrefix u) ∧
      ApproxTK eqEnvT n (.assumption D :: Γ) (EnvT.cons (demandT us) ρ)
        (.app (.bvar 0) (.bvar 1)) .prop := by
  rintro ⟨us, hreal, hbody⟩
  have hfun : ∀ {c : CptT}, ApproxTK eqEnvT n (.assumption D :: Γ)
      (EnvT.cons (demandT us) ρ) (.bvar 0) c → c = .bot := by
    intro c hc
    rcases approxTK_bvar_inv hc with hbot | hmem
    · exact hbot
    · exact approxTK_eqGapPrefix_bot (hreal c hmem)
  exact CptT.noConfusion (approxTK_app_bot_of_function_bot
    (fun _ _ he => Expr.noConfusion he) hfun hbody)

/-- The complete direct Eq beta source contains only bottom, while its
contractum keeps the landed `.prop` observation. -/
theorem approxTK_eqGapDirectAlias_bot (A B : Expr Nat) {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ (eqGapDirectAlias A B) c) : c = .bot := by
  have htarget : ApproxTK eqEnvT n Γ ρ eqGapRedex c :=
    approxTK_function_variable_beta_contract h
  rcases eqGap_model_shape (approxTK_forget htarget) with hbot | hprop
  · exact hbot
  · subst c
    exact (not_approxTK_eqGapDirectAlias_prop A B h).elim

/-- The unchanged relation observes the beta source at `.prop`, by beta
expansion of the actual native CK2 readback of the contractum. -/
theorem eqGapDirectAlias_lrsCoreS_prop (n : Nat) (A B : Expr Nat) :
    LRSCoreS (WhStepCK2 eqEnvT n) eqEnvT n eqGapCtx
      (eqGapDirectAlias A B) eqGapRedex (.sort (.succ .zero)) .prop := by
  have htarget : LRSCoreS (WhStepCK2 eqEnvT n) eqEnvT n eqGapCtx
      eqGapRedex eqGapRedex (.sort (.succ .zero)) .prop := by
    rw [lrSCoreS_prop_iff]
    exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero,
      redR_whStepCK2_eqGap n, redR_whStepCK2_eqGap n⟩
  exact lrSCoreS_expand (readbackLaws_whStepCK2 eqEnvT n)
    ((readbackLaws_whStepCK2 eqEnvT n).beta eqGapCtx (.pi A B)
      (.app (.bvar 0) (.bvar 1)) eqGapPrefix) .prop htarget

/-- One actual native beta conversion witnesses all three directions:
model source-to-target preservation, failure of target-to-source model
transport, and positive relation expansion at the missing source compact. -/
theorem eqGapDirectAlias_beta_route_control (n : Nat) :
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx eqGapPrefix (.pi A B)) ∧
      Nonempty (ConvT eqEnvT n eqGapCtx (eqGapDirectAlias A B) eqGapRedex
        (.sort (.succ .zero))) ∧
      (∀ ρ c, ApproxTK eqEnvT n eqGapCtx ρ (eqGapDirectAlias A B) c →
        ApproxTK eqEnvT n eqGapCtx ρ eqGapRedex c) ∧
      (∀ ρ, ApproxTK eqEnvT n eqGapCtx ρ eqGapRedex .prop ∧
        ¬ ApproxTK eqEnvT n eqGapCtx ρ (eqGapDirectAlias A B) .prop) ∧
      LRSCoreS (WhStepCK2 eqEnvT n) eqEnvT n eqGapCtx
        (eqGapDirectAlias A B) eqGapRedex (.sort (.succ .zero)) .prop := by
  obtain ⟨A, B, hty, hbeta, _, hobs⟩ := eqGapDirectAlias_native_beta_control n
  exact ⟨A, B, hty, hbeta, fun _ _ h => approxTK_function_variable_beta_contract h,
    hobs, eqGapDirectAlias_lrsCoreS_prop n A B⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_PROPAGATION_ROOTS
#print axioms fundConvAt_of_model_contractT
#print axioms fundConvAt_beta_of_model_contractT
#print axioms approxTK_function_variable_beta_contract
#print axioms no_eqGap_realized_beta_factorization
#print axioms approxTK_eqGapDirectAlias_bot
#print axioms eqGapDirectAlias_lrsCoreS_prop
#print axioms eqGapDirectAlias_beta_route_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_PROPAGATION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit
