import rcic.RcicNativeTypedModelCovRelFundApp
import rcic.RcicNativeTypedModelCovRelPER
import rcic.RcicNativeTypedModelCovRelEqGap
import rcic.RcicNativeTypedModelCovNormSubst
import rcic.RcicNativeTypedModelCovNormConstCases
import rcic.RcicNativeTypedModelCovRelEscape
import rcic.RcicNativeTypedModelCovRelPERControl

/-!
# Native typing cases for the covariant relation

The literal row uses exactly its native expansion child.  Type conversion
uses exactly its typing and conversion children, with the observed declared
type code stated separately.  The latter input is a model realization fact,
not a renamed fundamental motive.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormTyCasesAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit
open TypedModelCovRelAudit TypedModelCovRelEqGapAudit
open TypedModelCovNormSubstAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit TypedModelKIndexFreeAudit
open ReadbackCKAudit ReadbackCK2Audit TypedModelCovPropagationAudit
open TypedModelCovRelEscapeAudit
open FamModelAudit TypedModelAudit.TypingFin TypedModelKFailureAudit
open TypedModelKTypedBetaAudit TypedModelCovRelPERControlAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M : CtxModelT E}
  {R : Readback} {n : Nat}

/-- Re-pair the two already guarded environments without changing either
native substitution.  Both variable and actual let-value observations are
drawn from the original package. -/
theorem relSubstAtCov_envs {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ)
    (ρ₁ ρ₂ : EnvT) (h₁ : ρ₁ = ρ ∨ ρ₁ = ρ') (h₂ : ρ₂ = ρ ∨ ρ₂ = ρ') :
    RelSubstAtCov C M R n Δ ρ₁ ρ₂ σ σ' Γ := by
  have hρ₁ : EnvTypedCovAtP C M Γ ρ₁ := by
    rcases h₁ with rfl | rfl
    · exact h.envL
    · exact h.envR
  have hρ₂ : EnvTypedCovAtP C M Γ ρ₂ := by
    rcases h₂ with rfl | rfl
    · exact h.envL
    · exact h.envR
  refine ⟨h.typedL, h.typedR, h.conv, hρ₁, hρ₂, ?_, ?_⟩
  · intro i A hA c hc
    apply h.vars i A hA c
    rcases hc with hc | hc
    · rcases h₁ with rfl | rfl
      · exact Or.inl hc
      · exact Or.inr hc
    · rcases h₂ with rfl | rfl
      · exact Or.inl hc
      · exact Or.inr hc
  · intro i v A hv hA c hc
    apply h.lets i v A hv hA c
    rcases hc with hc | hc | hc | hc
    · rcases h₁ with rfl | rfl
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    · rcases h₂ with rfl | rfl
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    · rcases h₁ with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr hc))
    · rcases h₂ with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr hc))

/-- Reuse the proved two-sided expansion operation after a semantic
contraction.  The supplied target motive is not obtained by recursing on a
generated native derivation. -/
theorem fundTyAtCov_of_contract (hL : ReadbackLaws E R)
    {Γ : LCtx} {src dst A : Expr Nat}
    (hpres : ∀ ρ c, M.Ap ρ src c → M.Ap ρ dst c)
    (hread : ∀ (Δ : LCtx) (σ : SubstT),
      RedR R Δ (substT σ src) (substT σ dst))
    (htarget : FundTyAtCov C M R n Γ dst A) :
    FundTyAtCov C M R n Γ src A := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact lrSCoreCov_expand_red_both C hL (hread Δ σ) (hread Δ σ') c
    (htarget hΔ hS c (hc.elim (fun h => Or.inl (hpres ρ c h))
      (fun h => Or.inr (hpres ρ' c h))))

/-- The Pi row reads only its Pi inversion and binder-lift observations.
In particular it does not request a three-arm application law. -/
structure CovPiModelFor (M : CtxModelT E) (A B : Expr Nat)
    extends CovLiftModelLaws M : Prop where
  inv : ∀ {ρ : EnvT} {c : CptT}, M.Ap ρ (.pi A B) c →
    c = .bot ∨ ∃ a f, c = .pi a f ∧ M.Ap ρ A a ∧
      ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) ∧
        M.Ap (EnvT.cons (demandT s.1) ρ) B s.2

/-- The lambda row's exact model input retains its actual domain
observation and the declared constructor's typed finite demands. -/
structure CovLamModelFor (M : CtxModelT E) (A b : Expr Nat)
    extends CovLiftModelLaws M : Prop where
  inv : ∀ {ρ : EnvT} {c : CptT}, M.Ap ρ (.lam A b) c →
    c = .bot ∨ ∃ a g, c = .lam g ∧ M.Ap ρ A a ∧ (∃ s ∈ g, s.2 ≠ .bot) ∧
      ∀ s ∈ g, (∀ u ∈ s.1, CTyS E u a) ∧
        M.Ap (EnvT.cons (demandT s.1) ρ) b s.2

theorem covPiModelFor_approxT (E : ResolvedEnv) (A B : Expr Nat) :
    CovPiModelFor (ctxModelT_approxT E) A B :=
  ⟨covLiftModelLaws_approxT E, fun h => approxT_pi_inv h⟩

theorem covLamModelFor_approxT (E : ResolvedEnv) (A b : Expr Nat) :
    CovLamModelFor (ctxModelT_approxT E) A b :=
  ⟨covLiftModelLaws_approxT E, fun h => approxT_lam_inv h⟩

/-- The complete lambda motive follows from its genuine domain and body
motives.  The observed environment is duplicated before extending it, so
both new environment guards use the constructor's actual domain code. -/
theorem fundCov_lam_realized (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    (hCS : CovTypingIncludesS C) {Γ : LCtx} {A b B : Expr Nat} {u : Level}
    (hM : CovLamModelFor M A b) (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (ihA : FundTyAtCov C M R n Γ A (.sort u))
    (ihb : FundTyAtCov C M R n (.assumption A :: Γ) b B) :
    FundTyAtCov C M R n Γ (.lam A b) (.pi A B) := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  obtain ⟨⟨hAσ⟩, _, ⟨hAc⟩⟩ := hSub.nativeInstances hW hcl hst hι hΓ hΔ hA
  have fromSide : ∀ θ, θ = ρ ∨ θ = ρ' → M.Ap θ (.lam A b) c →
      LRSCoreCov C R n Δ (substT σ (.lam A b)) (substT σ' (.lam A b))
        (substT σ (.pi A B)) c := by
    intro θ hθ hobs
    rcases hM.inv hobs with rfl | ⟨a, f, rfl, hAa, _, hrows⟩
    · exact lrSCoreCov_bot C _ _ _ _
    · have hPair := relSubstAtCov_envs hSub θ θ hθ hθ
      have hAA' := ihA hΔ hPair a (Or.inl hAa)
      have hAA := ihA hΔ hPair.diagL a (Or.inl hAa)
      rw [LRSCoreCov.eq_def]
      refine ⟨substT σ A, substT σ.up B, .refl _,
        ⟨.assumption Δ _ u hΔ hAσ⟩, ?_⟩
      intro s hs N N' hN hN' hNN' hdem
      obtain ⟨ht, hb⟩ := hrows s hs
      obtain ⟨hNN'⟩ := hNN'
      have hExt := relSubstAtCov_cons_realized hL hNU hW hS hT hM.toCovLiftModelLaws
        hΔ hPair hAa (fun c hc => hCS a c (ht c hc)) hAA' hAA hAc hN hN' hNN' hdem
      have hbody := ihb hΔ hExt s.2 (Or.inl hb)
      rw [← instantiate0_substT_up, ← instantiate0_substT_up,
        ← instantiate0_substT_up] at hbody
      exact lrSCoreCov_expand_red_both C hL
        (redR_single (hL.beta Δ (substT σ A) (substT σ.up b) N))
        (redR_single (hL.beta Δ (substT σ' A) (substT σ'.up b) N')) s.2 hbody
  exact hc.elim (fromSide ρ (Or.inl rfl)) (fromSide ρ' (Or.inr rfl))

/-- Pi formation uses the new relation's own demand gate.  Native
substitution supplies the domain/codomain conversions, and each output
comes from the genuine codomain child at the realized extension. -/
theorem fundCov_pi_realized (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hM : CovPiModelFor M A B) (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (ihA : FundTyAtCov C M R n Γ A (.sort u))
    (ihB : FundTyAtCov C M R n (.assumption A :: Γ) B (.sort v)) :
    FundTyAtCov C M R n Γ (.pi A B) (.sort (.imax u v)) := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  obtain ⟨⟨hAσ⟩, _, ⟨hAc⟩⟩ := hSub.nativeInstances hW hcl hst hι hΓ hΔ hA
  have hΔA : CtxWfT E n (.assumption (substT σ A) :: Δ) :=
    .assumption Δ _ u hΔ hAσ
  obtain ⟨hBc⟩ := convT_substT_pointwise hW hcl hst hι
    (.assumption Γ A u hΓ hA) hB hΔA
    (typedSubstT_up hcl hSub.typedL A)
    (typedSubstT_up_conv hcl hSub.typedR A u hAc)
    (convSubstT_up_decl hcl hSub.conv _ _ A rfl (.bvar _ 0 _ rfl))
  have fromSide : ∀ θ, θ = ρ ∨ θ = ρ' → M.Ap θ (.pi A B) c →
      LRSCoreCov C R n Δ (substT σ (.pi A B)) (substT σ' (.pi A B))
        (substT σ (.sort (.imax u v))) c := by
    intro θ hθ hobs
    rcases hM.inv hobs with rfl | ⟨a, f, rfl, hAa, hrows⟩
    · exact lrSCoreCov_bot C _ _ _ _
    · have hPair := relSubstAtCov_envs hSub θ θ hθ hθ
      have hAA' := ihA hΔ hPair a (Or.inl hAa)
      have hAA := ihA hΔ hPair.diagL a (Or.inl hAa)
      rw [LRSCoreCov.eq_def]
      refine ⟨⟨.imax u v, .refl _⟩,
        substT σ A, substT σ.up B, substT σ' A, substT σ'.up B,
        .refl _, .refl _, ⟨hΔA⟩, ⟨.of _ _ _ u hAc⟩,
        ⟨.of _ _ _ v hBc⟩, ⟨u, hAA'⟩, ?_⟩
      intro s hs hTyped N N' hN hN' hNN' hdem
      obtain ⟨hNN'⟩ := hNN'
      have hExt := relSubstAtCov_cons_realized hL hNU hW hS hT hM.toCovLiftModelLaws
        hΔ hPair hAa hTyped hAA' hAA hAc hN hN' hNN' hdem
      have hbody := ihB hΔ hExt s.2 (Or.inl (hrows s hs).2)
      rw [← instantiate0_substT_up, ← instantiate0_substT_up] at hbody
      exact ⟨v, hbody⟩
  exact hc.elim (fromSide ρ (Or.inl rfl)) (fromSide ρ' (Or.inr rfl))

theorem fundCov_pi_step_realized (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hM : CovPiModelFor M A B)
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)) :
    FundTyCovStep C M R n (HasTyT.pi Γ A u B v hA hB) := by
  intro hΓ ih
  have hltA : sizeOf hA < sizeOf (HasTyT.pi Γ A u B v hA hB) := by simp; omega
  have hltB : sizeOf hB < sizeOf (HasTyT.pi Γ A u B v hA hB) := by simp; omega
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_pi_realized hL hNU hW hcl hst hι hS hT hM hΓ hA hB
    (ih.1 hA hltA hΓ) (ih.1 hB hltB (.assumption Γ A u hΓ hA)) hΔ hSub c hc

theorem fundCov_lam_step_realized (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    (hCS : CovTypingIncludesS C) {Γ : LCtx} {A b B : Expr Nat} {u : Level}
    (hM : CovLamModelFor M A b)
    (hA : HasTyT E n Γ A (.sort u))
    (hb : HasTyT E n (.assumption A :: Γ) b B) :
    FundTyCovStep C M R n (HasTyT.lam Γ A u b B hA hb) := by
  intro hΓ ih
  have hltA : sizeOf hA < sizeOf (HasTyT.lam Γ A u b B hA hb) := by simp; omega
  have hltb : sizeOf hb < sizeOf (HasTyT.lam Γ A u b B hA hb) := by simp; omega
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_lam_realized hL hNU hW hcl hst hι hS hT hCS hM hΓ hA
    (ih.1 hA hltA hΓ) (ih.1 hb hltb (.assumption Γ A u hΓ hA)) hΔ hSub c hc

theorem cov_kFreeValues_assumption {Γ : LCtx} (hV : KFreeValuesT E Γ) (A : Expr Nat) :
    KFreeValuesT E (.assumption A :: Γ) := by
  intro i v hv
  cases i with
  | zero => simp [lookupValue] at hv
  | succ i =>
      rw [lookupValue_cons_succ] at hv
      cases hw : lookupValue Γ i with
      | none => rw [hw] at hv; exact Option.noConfusion hv
      | some w =>
          rw [hw] at hv
          have he : lift 0 1 w = v := Option.some.inj hv
          subst v
          exact kFreeT_lift (hV i w hw) 0 1

theorem cov_kFreeTypes_assumption {Γ : LCtx} {A : Expr Nat}
    (hT : KFreeTypesT E Γ) (hA : KFreeT E A) :
    KFreeTypesT E (.assumption A :: Γ) := by
  intro i B hB
  cases i with
  | zero =>
      have he : lift 0 1 A = B := Option.some.inj hB
      subst B
      exact kFreeT_lift hA 0 1
  | succ i =>
      rw [lookupType_cons_succ] at hB
      cases hD : lookupType Γ i with
      | none => rw [hD] at hB; exact Option.noConfusion hB
      | some D =>
          rw [hD] at hB
          have he : lift 0 1 D = B := Option.some.inj hB
          subst B
          exact kFreeT_lift (hT i D hD) 0 1

/-- K-free transport closes the native saturated-model Pi row from the
two genuine native children.  Both lookup types and let values are carried
through the model change, including under the binder. -/
theorem fundCov_pi_step_approxTK_of_kFree (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Ξ Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hV : KFreeValuesT E Γ) (hTypes : KFreeTypesT E Γ)
    (hAf : KFreeT E A) (hBf : KFreeT E B)
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)) :
    FundTyCovStep C (ctxModelT_approxTK E n Ξ) R n (HasTyT.pi Γ A u B v hA hB) := by
  intro hΓ ih
  have hltA : sizeOf hA < sizeOf (HasTyT.pi Γ A u B v hA hB) := by simp; omega
  have hltB : sizeOf hB < sizeOf (HasTyT.pi Γ A u B v hA hB) := by simp; omega
  have ihA : FundTyAtCov C (ctxModelT_approxT E) R n Γ A (.sort u) := by
    intro Δ ρ ρ' σ σ' hΔ hSub c hc
    exact (fundTyAtCov_approxTK_iff_of_kFree hV hTypes hAf).mp
      (ih.1 hA hltA hΓ) hΔ hSub c hc
  have ihB : FundTyAtCov C (ctxModelT_approxT E) R n (.assumption A :: Γ) B (.sort v) := by
    intro Δ ρ ρ' σ σ' hΔ hSub c hc
    exact (fundTyAtCov_approxTK_iff_of_kFree (cov_kFreeValues_assumption hV A)
      (cov_kFreeTypes_assumption hTypes hAf) hBf).mp
        (ih.1 hB hltB (.assumption Γ A u hΓ hA)) hΔ hSub c hc
  apply (fundTyAtCov_approxTK_iff_of_kFree hV hTypes (kFreeT_pi hAf hBf)).mpr
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_pi_realized hL hNU hW hcl hst hι hS hT
    (covPiModelFor_approxT E A B) hΓ hA hB ihA ihB hΔ hSub c hc

/-- The lambda K-free row retains the whole covariant related package at
each transport; its model's CTyS demands enter C only through `hCS`. -/
theorem fundCov_lam_step_approxTK_of_kFree (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n) (hCS : CovTypingIncludesS C)
    {Ξ Γ : LCtx} {A b B : Expr Nat} {u : Level}
    (hV : KFreeValuesT E Γ) (hTypes : KFreeTypesT E Γ)
    (hAf : KFreeT E A) (hbf : KFreeT E b)
    (hA : HasTyT E n Γ A (.sort u))
    (hb : HasTyT E n (.assumption A :: Γ) b B) :
    FundTyCovStep C (ctxModelT_approxTK E n Ξ) R n (HasTyT.lam Γ A u b B hA hb) := by
  intro hΓ ih
  have hltA : sizeOf hA < sizeOf (HasTyT.lam Γ A u b B hA hb) := by simp; omega
  have hltb : sizeOf hb < sizeOf (HasTyT.lam Γ A u b B hA hb) := by simp; omega
  have ihA : FundTyAtCov C (ctxModelT_approxT E) R n Γ A (.sort u) := by
    intro Δ ρ ρ' σ σ' hΔ hSub c hc
    exact (fundTyAtCov_approxTK_iff_of_kFree hV hTypes hAf).mp
      (ih.1 hA hltA hΓ) hΔ hSub c hc
  have ihb : FundTyAtCov C (ctxModelT_approxT E) R n (.assumption A :: Γ) b B := by
    intro Δ ρ ρ' σ σ' hΔ hSub c hc
    exact (fundTyAtCov_approxTK_iff_of_kFree (cov_kFreeValues_assumption hV A)
      (cov_kFreeTypes_assumption hTypes hAf) hbf).mp
        (ih.1 hb hltb (.assumption Γ A u hΓ hA)) hΔ hSub c hc
  apply (fundTyAtCov_approxTK_iff_of_kFree hV hTypes (kFreeT_lam hAf hbf)).mpr
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_lam_realized hL hNU hW hcl hst hι hS hT hCS
    (covLamModelFor_approxT E A b) hΓ hA ihA ihb hΔ hSub c hc

/-- When the admitted environment has no indexed proposition recursor,
the complete model equality supplies the exact binder input. -/
theorem covPiModelFor_approxTK_of_no_indexed {Ξ : LCtx}
    (hE : ∀ r, ¬ IndexedPropRecT E r) (A B : Expr Nat) :
    CovPiModelFor (ctxModelT_approxTK E n Ξ) A B := by
  rw [ctxModelT_approxTK_eq_approxT_of_no_indexed hE]
  exact covPiModelFor_approxT E A B

theorem covLamModelFor_approxTK_of_no_indexed {Ξ : LCtx}
    (hE : ∀ r, ¬ IndexedPropRecT E r) (A b : Expr Nat) :
    CovLamModelFor (ctxModelT_approxTK E n Ξ) A b := by
  rw [ctxModelT_approxTK_eq_approxT_of_no_indexed hE]
  exact covLamModelFor_approxT E A b

/-- The literal input is semantic contraction to the native constructor's
actual expansion child; it contains no relation conclusion. -/
def CovLiteralContract (M : CtxModelT E) (t : Nat) : Prop :=
  ∀ ρ c, M.Ap ρ (.lit t) c → M.Ap ρ (natExpand t) c

/-- Certified expansion syntax provides contraction in the saturated model,
including observations inherited through its `free` constructor. -/
theorem covLiteralContract_approxTK_of_kFree {Ξ : LCtx} {t : Nat}
    (ht : KFreeT E (natExpand t)) :
    CovLiteralContract (ctxModelT_approxTK E n Ξ) t := by
  intro ρ c hc
  apply ApproxTK.free ht
  have h := approxTK_forget hc
  cases h with
  | bot => exact .bot _ _
  | lit h => exact h

theorem cov_literal_subst_read (E : ResolvedEnv) (n : Nat) (t : Nat)
    (Δ : LCtx) (σ : SubstT) :
    RedR (WhStepCK2 E n) Δ (substT σ (.lit t)) (substT σ (natExpand t)) := by
  simpa only [substT, substT_natExpand] using
    (redR_single (show WhStepCK2 E n Δ (.lit t) (natExpand t) from .ctx (.lit t)))

theorem fundCov_lit_of_contract {Ξ Γ : LCtx} {t : Nat} {T : Expr Nat}
    (hM : CovLiteralContract (ctxModelT_approxTK E n Ξ) t)
    (ih : FundTyAtCov C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n Γ (natExpand t) T) :
    FundTyAtCov C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n Γ (.lit t) T :=
  fundTyAtCov_of_contract (readbackLaws_whStepCK2 E n) hM (cov_literal_subst_read E n t) ih

/-- The literal row calls the IH solely at its strict native expansion
child.  All target contexts, valuations and substitutions remain quantified. -/
theorem fundCov_lit_step_approxTK {Ξ Γ : LCtx} {t : Nat} {T : Expr Nat}
    (hM : CovLiteralContract (ctxModelT_approxTK E n Ξ) t)
    (h : HasTyT E n Γ (natExpand t) T) :
    FundTyCovStep C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n (HasTyT.lit Γ t T h) := by
  intro hΓ ih
  have hlt : sizeOf h < sizeOf (HasTyT.lit Γ t T h) := by simp; omega
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_lit_of_contract hM (ih.1 h hlt hΓ) hΔ hSub c hc

theorem fundCov_lit_step_approxTK_of_kFree {Ξ Γ : LCtx} {t : Nat} {T : Expr Nat}
    (ht : KFreeT E (natExpand t)) (h : HasTyT E n Γ (natExpand t) T) :
    FundTyCovStep C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n (HasTyT.lit Γ t T h) :=
  fundCov_lit_step_approxTK (covLiteralContract_approxTK_of_kFree ht) h

/-- The exact type observation consumed by a typing-conversion row.  Its
conclusion is a model observation and compact typing, with no relation or
fundamental-theorem conclusion. -/
def CovObservedTypeFor (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (e A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ e c ∨ M.Ap ρ' e c →
      ∃ a, (M.Ap ρ A a ∨ M.Ap ρ' A a) ∧ C.ty c a

/-- Type conversion consumes an actually observed source-type code and the
two genuine child motives.  The new typed PER transports the index. -/
theorem fundCov_conv_of_observedType (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (ih : FundTyAtCov C M R n Γ e A)
    (ihc : FundConvAtCov C M R n Γ A B (.sort u))
    (hTy : CovObservedTypeFor C M R n Γ e A) :
    FundTyAtCov C M R n Γ e B := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  obtain ⟨a, ha, hca⟩ := hTy hΔ hSub c hc
  have hAB : LRSCoreCov C R n Δ (substT σ A) (substT σ B) (.sort u) a := by
    rcases ha with ha | ha
    · exact ihc hΔ hSub.diagL a (Or.inl ha)
    · exact ihc hΔ (relSubstAtCov_envs hSub ρ' ρ' (Or.inr rfl) (Or.inr rfl)).diagL
        a (Or.inl ha)
  exact lrSCoreCov_irrel C hL hNU hW hS hT a c hΔ
    hAB hca
    (ih hΔ hSub c hc)

/-- The two recursive calls are to the actual `conv` constructor children. -/
theorem fundCov_conv_step_of_observedType (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (h : HasTyT E n Γ e A) (hc : ConvT E n Γ A B (.sort u))
    (hTy : CovObservedTypeFor C M R n Γ e A) :
    FundTyCovStep C M R n (HasTyT.conv Γ e A B u h hc) := by
  intro hΓ ih
  have hlt : sizeOf h < sizeOf (HasTyT.conv Γ e A B u h hc) := by simp; omega
  have hclt : sizeOf hc < sizeOf (HasTyT.conv Γ e A B u h hc) := by simp; omega
  intro Δ ρ ρ' σ σ' hΔ hSub c hobs
  exact fundCov_conv_of_observedType hL hNU hW hS hT
    (ih.1 h hlt hΓ) (ih.2 hc hclt hΓ) hTy hΔ hSub c hobs

/-- The model-only conversion input is actually supplied at every sort
observation in the saturated model. -/
theorem covObservedTypeFor_sort_approxTK (hCS : CovTypingIncludesS C)
    (Ξ Γ : LCtx) (l : Level) :
    CovObservedTypeFor C (ctxModelT_approxTK E n Ξ) R n Γ
      (.sort l) (.sort (.succ l)) := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  rcases hc.elim approxTK_sort_inv approxTK_sort_inv with rfl | rfl
  · exact ⟨.bot, Or.inl (ApproxTK.bot _ _ _), C.bot .bot⟩
  · refine ⟨.sort, Or.inl ?_, ?_⟩
    · simpa only [TypingFin.sortCode_succ] using approxTK_sort_code E n Ξ ρ (.succ l)
    · apply hCS
      rcases sortCode_prop_or_sort l with h | h
      · rw [h]; exact ctyS_prop_sort E
      · rw [h]; exact ctyS_sort_sort E

/-- The same precise conversion input fails at the actual Eq alias even
with the full identity related substitution, native typing and a non-bottom
term observation.  This refutes the input, not the conversion relation. -/
theorem covObservedTypeFor_alias_control (C : CovTyping eqEnvT) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx PiModelDeltaIotaAudit.idPiProp (eqGapDirectAlias A B)) ∧
      RelSubstAtCov C (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n) n
        eqGapCtx EnvT.bot EnvT.bot SubstT.id SubstT.id eqGapCtx ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot PiModelDeltaIotaAudit.idPiProp (.pi .bot []) ∧
      LRSCoreCov C (WhStepCK2 eqEnvT n) n eqGapCtx
        PiModelDeltaIotaAudit.idPiProp PiModelDeltaIotaAudit.idPiProp
        (eqGapDirectAlias A B) (.pi .bot []) ∧
      (.pi .bot [] : CptT) ≠ .bot ∧
      ¬ CovObservedTypeFor C (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n)
        n eqGapCtx PiModelDeltaIotaAudit.idPiProp (eqGapDirectAlias A B) := by
  obtain ⟨⟨hW⟩, ⟨hΓ⟩, _, A, B, ht, hm, hr, hno⟩ := alias_type_escape_counterexample C n
  have hSub := relSubstAtCov_eqGap_bot_diagonal C
    (typedSubstT_id (envClosed_of_envWfT hW) hΓ)
  refine ⟨⟨hW⟩, ⟨hΓ⟩, A, B, ht, hSub, hm, hr,
    (fun h => CptT.noConfusion h), ?_⟩
  intro hInput
  obtain ⟨a, ha, hca⟩ := hInput hΓ hSub (.pi .bot []) (Or.inl hm)
  exact hno ⟨a, ha.elim id id, hca⟩

/-- A complete native constant motive at the actual rigid zero constructor,
with all target contexts and both source environments retained. -/
theorem fundCov_natZero (C : CovTyping natEnvU) (n : Nat) (Ξ Γ : LCtx) :
    FundTyAtCov C (ctxModelT_approxTK natEnvU n Ξ) (WhStepCK2 natEnvU n) n Γ
      (.const 1 []) (.const 0 []) := by
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_const_of_spineInput (rfl : natEnvU.members 1 = some natZeroMember)
    (covConstSpineInput_ctor natEnvUWfT rfl rfl rigidConst_natEnvU_zero) hΔ hSub c hc

/-- The full literal-zero motive is obtained by actual model contraction
and the proved rigid-constructor motive. -/
theorem fundCov_litZero (C : CovTyping natEnvU) (n : Nat) (Ξ Γ : LCtx) :
    FundTyAtCov C (ctxModelT_approxTK natEnvU n Ξ) (WhStepCK2 natEnvU n) n Γ
      (.lit 0) (.const 0 []) := by
  apply fundCov_lit_of_contract (covLiteralContract_approxTK_of_kFree (kFreeT_natEnvU (natExpand 0)))
  exact fundCov_natZero C n Ξ Γ

/-- Constant and literal suppliers have a native, non-bottom control in the
actual saturated Nat model, with the whole related package present. -/
theorem covLiteral_native_control (C : CovTyping natEnvU) (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.lit 0) (.const 0 [])) ∧
    RelSubstAtCov C (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n) n
      [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    ApproxTK natEnvU n [] EnvT.bot (.lit 0) (.spine 1 []) ∧
    LRSCoreCov C (WhStepCK2 natEnvU n) n [] (.lit 0) (.lit 0) (.const 0 []) (.spine 1 []) ∧
    (.spine 1 [] : CptT) ≠ .bot := by
  have hSub := relSubstAtCov_nil C (ctxModelT_approxTK natEnvU n [])
    (WhStepCK2 natEnvU n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id
  have hm : ApproxTK natEnvU n [] EnvT.bot (.lit 0) (.spine 1 []) :=
    .lit (.free (kFreeT_natEnvU _) (.const _ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero))
  refine ⟨⟨natEnvUWfT⟩, ⟨.nil⟩,
    ⟨.lit [] 0 (.const 0 []) (hasTyT_natEnvU_zero n [])⟩, hSub, hm, ?_,
    fun h => CptT.noConfusion h⟩
  simpa only [substT_id] using fundCov_litZero C n [] [] .nil hSub (.spine 1 []) (Or.inl hm)

private theorem cov_no_indexed_emptyEnv (r : Nat) : ¬ IndexedPropRecT emptyEnv r := by
  rintro ⟨w, _, _, _⟩
  exact Option.noConfusion w.hrec

/-- Both binder model inputs hold in the real empty-environment saturated
model, which realizes a native identity and its Pi type at non-bottom
compacts.  This is a full native/model/related-substitution control. -/
theorem covBinder_native_control (C : CovTyping emptyEnv)
    (hCS : CovTypingIncludesS C) (n : Nat) :
    CovPiModelFor (ctxModelT_approxTK emptyEnv n [])
      (.sort (.succ .zero)) (.sort (.succ .zero)) ∧
    CovLamModelFor (ctxModelT_approxTK emptyEnv n [])
      (.sort (.succ .zero)) (.bvar 0) ∧
    Nonempty (HasTyT emptyEnv n [] idSort1 idSort1Ty) ∧
    RelSubstAtCov C (ctxModelT_approxTK emptyEnv n []) (WhStepCK2 emptyEnv n) n
      [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    ApproxTK emptyEnv n [] EnvT.bot idSort1Ty polyIdDom1 ∧
    ApproxTK emptyEnv n [] EnvT.bot idSort1 polyIdOut0 ∧
    polyIdDom1 ≠ .bot ∧ polyIdOut0 ≠ .bot ∧
    LRSCoreCov C (WhStepCK2 emptyEnv n) n [] idSort1 idSort1 idSort1Ty polyIdOut0 := by
  obtain ⟨ht, hm, hne, _, _, hr, _, _⟩ := idSort1_cov_per_control_emptyEnv C hCS n EnvT.bot
  refine ⟨covPiModelFor_approxTK_of_no_indexed cov_no_indexed_emptyEnv _ _,
    covLamModelFor_approxTK_of_no_indexed cov_no_indexed_emptyEnv _ _, ht,
    relSubstAtCov_nil C (ctxModelT_approxTK emptyEnv n []) (WhStepCK2 emptyEnv n)
      n [] EnvT.bot EnvT.bot SubstT.id SubstT.id, ?_, hm,
    (fun h => CptT.noConfusion h), hne, hr⟩
  exact .free (kFreeT_pi (kFreeT_sort emptyEnv _) (kFreeT_sort emptyEnv _))
    (approxT_idSort1Ty_polyIdDom1 emptyEnv EnvT.bot)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_TY_CASES_ROOTS
#print axioms relSubstAtCov_envs
#print axioms fundTyAtCov_of_contract
#print axioms CovPiModelFor
#print axioms CovLamModelFor
#print axioms covPiModelFor_approxT
#print axioms covLamModelFor_approxT
#print axioms fundCov_lam_realized
#print axioms fundCov_pi_realized
#print axioms fundCov_pi_step_realized
#print axioms fundCov_lam_step_realized
#print axioms cov_kFreeValues_assumption
#print axioms cov_kFreeTypes_assumption
#print axioms fundCov_pi_step_approxTK_of_kFree
#print axioms fundCov_lam_step_approxTK_of_kFree
#print axioms covPiModelFor_approxTK_of_no_indexed
#print axioms covLamModelFor_approxTK_of_no_indexed
#print axioms CovLiteralContract
#print axioms covLiteralContract_approxTK_of_kFree
#print axioms cov_literal_subst_read
#print axioms fundCov_lit_of_contract
#print axioms fundCov_lit_step_approxTK
#print axioms fundCov_lit_step_approxTK_of_kFree
#print axioms CovObservedTypeFor
#print axioms fundCov_conv_of_observedType
#print axioms fundCov_conv_step_of_observedType
#print axioms covObservedTypeFor_sort_approxTK
#print axioms covObservedTypeFor_alias_control
#print axioms fundCov_natZero
#print axioms fundCov_litZero
#print axioms covLiteral_native_control
#print axioms covBinder_native_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_TY_CASES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormTyCasesAudit
