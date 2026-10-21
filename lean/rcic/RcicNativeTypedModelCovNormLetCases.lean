import rcic.RcicNativeTypedModelCovNormTyCases
import rcic.RcicNativeTypedModelSubst

/-!
# The genuine let-body child and a realized let substitution

`CovLetInput` isolates the exact structural boundary: the model observation
must reach the body under the full denotation of the value, and that full
valuation must carry the native let substitution, its guards, and its value
coherence.  Neither field states the let expression's relation conclusion.

The full input is supplied for an actual sort-valued let in `ApproxT` and in
every saturated model without indexed proposition recursors.  The control
has a native derivation, the complete related package, and a non-bottom
observation.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormTyCasesAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit
open TypedModelCovRelAudit TypedModelCovNormSubstAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit TypedModelKIndexFreeAudit
open ReadbackCKAudit ReadbackCK2Audit
open TypedModelAudit.TypingFin

variable {E : ResolvedEnv} {C : CovTyping E} {M : CtxModelT E}
  {R : Readback} {n : Nat}

/-- Full value denotation is needed here: a finite-demand assumption
extension alone does not establish a native let's model coherence. -/
structure CovLetInput (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (A value body : Expr Nat) : Prop where
  body : ∀ {ρ : EnvT} {c : CptT}, M.Ap ρ (.letE A value body) c →
    M.Ap (EnvT.cons (fun u => M.Ap ρ value u) ρ) body c
  subst : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
    RelSubstAtCov C M R n Δ
      (EnvT.cons (fun u => M.Ap ρ value u) ρ)
      (EnvT.cons (fun u => M.Ap ρ' value u) ρ')
      (SubstT.cons (substT σ value) σ) (SubstT.cons (substT σ' value) σ')
      (.letBinding A value :: Γ)

/-- Zeta readback reaches exactly the simultaneous substitution used by
the genuine body child. -/
theorem cov_let_subst_read (E : ResolvedEnv) (n : Nat) (Δ : LCtx)
    (σ : SubstT) (A value body : Expr Nat) :
    RedR (WhStepCK2 E n) Δ (substT σ (.letE A value body))
      (substT (SubstT.cons (substT σ value) σ) body) := by
  rw [← instantiate0_substT_up]
  exact redR_single (.ctx (.zeta _ _ _))

/-- The let case consumes the actual let-body motive.  Its source context
and value equation remain intact in the supplied extension. -/
theorem fundCov_letE_of_input (hL : ReadbackLaws E (WhStepCK2 E n))
    {Γ : LCtx} {A value body B : Expr Nat}
    (hInput : CovLetInput C M (WhStepCK2 E n) n Γ A value body)
    (ihb : FundTyAtCov C M (WhStepCK2 E n) n (.letBinding A value :: Γ) body B) :
    FundTyAtCov C M (WhStepCK2 E n) n Γ (.letE A value body) (instantiate0 value B) := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  have hbody := ihb hΔ (hInput.subst hΔ hSub) c
    (hc.elim (fun h => Or.inl (hInput.body h)) (fun h => Or.inr (hInput.body h)))
  have hres := lrSCoreCov_expand_red_both C hL
    (cov_let_subst_read E n Δ σ A value body)
    (cov_let_subst_read E n Δ σ' A value body) c hbody
  simpa only [substT_instantiate0, instantiate0_substT_up] using hres

theorem fundCov_letE_step_of_input (hL : ReadbackLaws E (WhStepCK2 E n))
    {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B)
    (hInput : CovLetInput C M (WhStepCK2 E n) n Γ A value body) :
    FundTyCovStep C M (WhStepCK2 E n) n
      (HasTyT.letE Γ A u value B body hA hv hb) := by
  intro hΓ ih
  have hlt : sizeOf hb < sizeOf (HasTyT.letE Γ A u value B body hA hv hb) := by
    simp; omega
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_letE_of_input hL hInput
    (ih.1 hb hlt (.letBinding Γ A u value hΓ hA hv)) hΔ hSub c hc

/-- This model-only field reuses the landed semantic zeta and substitution
theorems.  No typing or fundamental premise is involved. -/
theorem cov_let_body_approxT (E : ResolvedEnv) (A value body : Expr Nat)
    {ρ : EnvT} {c : CptT} (h : ApproxT E ρ (.letE A value body) c) :
    ApproxT E (EnvT.cons (fun u => ApproxT E ρ value u) ρ) body c :=
  (approxT_subst0_iff E ρ value body c).mp
    (covConv_zeta_fwd (covModelSubstFactorT_approxT E) ρ A value body h)

private theorem cov_sort_zero_core (C : CovTyping E) (R : Readback) (n : Nat)
    (Δ : LCtx) {c : CptT} (hc : c = .bot ∨ c = .prop) :
    LRSCoreCov C R n Δ (.sort .zero) (.sort .zero) (.sort (.succ .zero)) c := by
  rcases hc with rfl | rfl
  · exact lrSCoreCov_bot C _ _ _ _
  · rw [lrSCoreCov_prop_iff]
    exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero, .refl _, .refl _⟩

private theorem cov_sort_zero_env (C : CovTyping E) (hCS : CovTypingIncludesS C)
    (ρ : EnvT) :
    EnvTypedCovAtP C (ctxModelT_approxT E)
      [.letBinding (.sort (.succ .zero)) (.sort .zero)]
      (EnvT.cons (fun c => ApproxT E ρ (.sort .zero) c) ρ) := by
  constructor
  · intro i A hA c hc
    cases i with
    | zero =>
        have he : (.sort (.succ .zero) : Expr Nat) = A := Option.some.inj hA
        subst A
        refine ⟨.sort, ?_, ?_⟩
        · exact approxT_sort_code E _ (.succ .zero)
        · rcases approxT_sort_inv hc with rfl | hc
          · exact C.bot .sort
          · rw [sortCode_zero] at hc
            subst c
            exact hCS .sort .prop (ctyS_prop_sort E)
    | succ i => simp [lookupType] at hA
  · intro i value hv c
    cases i with
    | zero =>
        have he : (.sort .zero : Expr Nat) = value := Option.some.inj hv
        subst value
        change ApproxT E (EnvT.cons (fun c => ApproxT E ρ (.sort .zero) c) ρ)
          (.bvar 0) c ↔ ApproxT E (EnvT.cons (fun c => ApproxT E ρ (.sort .zero) c) ρ)
            (.sort .zero) c
        rw [approxT_bvar_iff]
        constructor
        · intro h
          rcases h with rfl | h
          · exact .bot _ _
          · rcases approxT_sort_inv h with rfl | hc
            · exact .bot _ _
            · rw [hc]; exact approxT_sort_code E _ .zero
        · intro h
          apply Or.inr
          rcases approxT_sort_inv h with rfl | hc
          · exact .bot _ _
          · rw [hc]; exact approxT_sort_code E _ .zero
    | succ i => simp [lookupValue] at hv

/-- An actual let substitution with arbitrary target, tail substitutions,
and source valuations.  It realizes both the guard and the value equation
for the non-bottom sort observation. -/
theorem relSubstAtCov_sortLet (C : CovTyping E) (hCS : CovTypingIncludesS C)
    (R : Readback) (n : Nat) (Δ : LCtx) (ρ ρ' : EnvT) (σ σ' : SubstT) :
    RelSubstAtCov C (ctxModelT_approxT E) R n Δ
      (EnvT.cons (fun c => ApproxT E ρ (.sort .zero) c) ρ)
      (EnvT.cons (fun c => ApproxT E ρ' (.sort .zero) c) ρ')
      (SubstT.cons (.sort .zero) σ) (SubstT.cons (.sort .zero) σ')
      [.letBinding (.sort (.succ .zero)) (.sort .zero)] := by
  have ht : ∀ τ : SubstT, TypedSubstT E n Δ (SubstT.cons (.sort .zero) τ)
      [.letBinding (.sort (.succ .zero)) (.sort .zero)] := by
    intro τ
    constructor
    · intro i A hA
      cases i with
      | zero =>
          have he : (.sort (.succ .zero) : Expr Nat) = A := Option.some.inj hA
          subst A
          exact ⟨.sort Δ .zero⟩
      | succ i => simp [lookupType] at hA
    · intro i value hv
      cases i with
      | zero =>
          have he : (.sort .zero : Expr Nat) = value := Option.some.inj hv
          subst value
          exact ⟨.sort (.succ .zero), rfl, ⟨.refl _ _ _ (.sort Δ .zero)⟩⟩
      | succ i => simp [lookupValue] at hv
  refine ⟨ht σ, ht σ', ?_, cov_sort_zero_env C hCS ρ,
    cov_sort_zero_env C hCS ρ', ?_, ?_⟩
  · intro i A hA
    cases i with
    | zero =>
        have he : (.sort (.succ .zero) : Expr Nat) = A := Option.some.inj hA
        subst A
        exact ⟨.refl _ _ _ (.sort Δ .zero)⟩
    | succ i => simp [lookupType] at hA
  · intro i A hA c hc
    cases i with
    | zero =>
        have he : (.sort (.succ .zero) : Expr Nat) = A := Option.some.inj hA
        subst A
        have hs : c = .bot ∨ c = .prop :=
          (hc.elim approxT_sort_inv approxT_sort_inv).imp_right
            (fun h => h.trans sortCode_zero)
        have hr := cov_sort_zero_core C R n Δ hs
        exact ⟨hr, hr, hr, hr⟩
    | succ i => simp [lookupType] at hA
  · intro i value A hv hA c hc
    cases i with
    | zero =>
        have he : (.sort (.succ .zero) : Expr Nat) = A := Option.some.inj hA
        have he' : (.sort .zero : Expr Nat) = value := Option.some.inj hv
        subst A
        subst value
        have hs : c = .bot ∨ c = .prop := by
          rcases hc with h | h | h | h
          all_goals exact (approxT_sort_inv h).imp_right (fun h => h.trans sortCode_zero)
        have hr := cov_sort_zero_core C R n Δ hs
        exact ⟨hr, hr, hr, hr⟩
    | succ i => simp [lookupValue] at hv

/-- A complete, non-vacuous supplier of both structural fields, for every
let body with this native sort value. -/
theorem covLetInput_sort_approxT (C : CovTyping E) (hCS : CovTypingIncludesS C)
    (R : Readback) (n : Nat) (body : Expr Nat) :
    CovLetInput C (ctxModelT_approxT E) R n []
      (.sort (.succ .zero)) (.sort .zero) body := by
  refine ⟨cov_let_body_approxT E _ _ _, ?_⟩
  intro Δ ρ ρ' σ σ' _ _
  exact relSubstAtCov_sortLet C hCS R n Δ ρ ρ' σ σ'

theorem covLetInput_sort_approxTK_of_no_indexed (C : CovTyping E)
    (hCS : CovTypingIncludesS C) (hE : ∀ r, ¬ IndexedPropRecT E r)
    (R : Readback) (n : Nat) (Ξ : LCtx) (body : Expr Nat) :
    CovLetInput C (ctxModelT_approxTK E n Ξ) R n []
      (.sort (.succ .zero)) (.sort .zero) body := by
  rw [ctxModelT_approxTK_eq_approxT_of_no_indexed hE]
  exact covLetInput_sort_approxT C hCS R n body

/-- The supplier yields the full let motive using the existing variable
case as the actual body motive. -/
theorem fundCov_sortLet (C : CovTyping E) (hCS : CovTypingIncludesS C)
    (hW : EnvWfT E) (hE : ∀ r, ¬ IndexedPropRecT E r) (n : Nat) (Ξ : LCtx) :
    FundTyAtCov C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n []
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0)) (.sort (.succ .zero)) := by
  apply fundCov_letE_of_input (B := .sort (.succ .zero)) (readbackLaws_whStepCK2 E n)
    (covLetInput_sort_approxTK_of_no_indexed C hCS hE _ n Ξ (.bvar 0))
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_bvar
    (Γ := [.letBinding (.sort (.succ .zero)) (.sort .zero)])
    (covAtomicModelLaws_approxTK E n Ξ) 0 (.sort (.succ .zero)) rfl hΔ hSub c hc

/-- A non-bottom native/model/related-substitution control for the exact
let input, including the result produced by its genuine body case. -/
theorem covLet_native_control (C : CovTyping E) (hCS : CovTypingIncludesS C)
    (hW : EnvWfT E) (hE : ∀ r, ¬ IndexedPropRecT E r) (n : Nat) :
    CovLetInput C (ctxModelT_approxTK E n []) (WhStepCK2 E n) n []
      (.sort (.succ .zero)) (.sort .zero) (.bvar 0) ∧
    Nonempty (HasTyT E n []
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0)) (.sort (.succ .zero))) ∧
    RelSubstAtCov C (ctxModelT_approxTK E n []) (WhStepCK2 E n) n
      [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    ApproxTK E n [] EnvT.bot
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0)) .prop ∧
    LRSCoreCov C (WhStepCK2 E n) n []
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0))
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0))
      (.sort (.succ .zero)) .prop ∧ (.prop : CptT) ≠ .bot := by
  have hSub := relSubstAtCov_nil C (ctxModelT_approxTK E n []) (WhStepCK2 E n)
    n [] EnvT.bot EnvT.bot SubstT.id SubstT.id
  have hobs : ApproxTK E n [] EnvT.bot
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0)) .prop := by
    apply ApproxTK.free ((kFreeT_letE_iff _ _ _).mpr
      (kFreeT_app (kFreeT_lam (kFreeT_sort E _) (kFreeT_bvar E _)) (kFreeT_sort E _)))
    refine .letE (.app (approxT_idSort1_polyIdOut0 E EnvT.bot)
      (List.mem_singleton.mpr rfl) ?_)
    intro u hu
    rcases List.mem_singleton.mp hu with rfl
    exact approxT_sort_code E EnvT.bot .zero
  refine ⟨covLetInput_sort_approxTK_of_no_indexed C hCS hE _ n [] _,
    ⟨.letE [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
      (.sort (.succ .zero)) (.bvar 0) (.sort _ _) (.sort _ _) (.bvar _ 0 _ rfl)⟩,
    hSub, hobs, ?_, fun h => CptT.noConfusion h⟩
  simpa only [substT_id] using fundCov_sortLet C hCS hW hE n [] .nil hSub .prop (Or.inl hobs)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_LET_CASES_ROOTS
#print axioms CovLetInput
#print axioms cov_let_subst_read
#print axioms fundCov_letE_of_input
#print axioms fundCov_letE_step_of_input
#print axioms cov_let_body_approxT
#print axioms relSubstAtCov_sortLet
#print axioms covLetInput_sort_approxT
#print axioms covLetInput_sort_approxTK_of_no_indexed
#print axioms fundCov_sortLet
#print axioms covLet_native_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_LET_CASES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormTyCasesAudit
