import rcic.RcicNativeTypedModelCovRelCore
import rcic.RcicNativeTypedModelCovKTyping

/-!
# Related substitutions for the typing-parametric recursive relation

The environment guard is parametric in the same compact typing as
`LRSCoreCov`.  Its `CTyCov` specialization is definitionally the existing
`EnvTypedCovAtM`, including `CtxEnvM` let-value coherence.

`RelSubstAtCov` retains native typing and conversion of the substitutions,
both guarded environments, all four variable relations and all four
let-value relations.  Model transport reads lookup types, lookup values,
and the variable side of the let-coherence equation.  K-free transport
changes only those model observations; it does not identify `CTyCov` with
`CTyS` or identify the two recursive relations.

The bridge to the old related-substitution package explicitly requests
agreement of the recursive relations.  No global typing or Fundamental
supplier is inferred from a local model equivalence.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit
open Rcic.Declarative.NativeValleys.TypedModelCovKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit

variable {E : ResolvedEnv} {C : CovTyping E} {M N : CtxModelT E}
  {R : Readback} {n : Nat}

/-- A realized type observation, using the same compact typing as the relation. -/
def ElTCovP (C : CovTyping E) (M : CtxModelT E) (ρ : EnvT)
    (A : Expr Nat) (u : CptT) : Prop :=
  ∃ a, M.Ap ρ A a ∧ C.ty u a

/-- Pointwise compact typing and actual let-value coherence. -/
def EnvTypedCovAtP (C : CovTyping E) (M : CtxModelT E) (Γ : LCtx) (ρ : EnvT) : Prop :=
  (∀ i A, lookupType Γ i = some A → ∀ u, ρ i u → ElTCovP C M ρ A u) ∧
    CtxEnvM M Γ ρ

theorem elTCovP_ctyCov_iff (M : CtxModelT E) (ρ : EnvT) (A : Expr Nat) (u : CptT) :
    ElTCovP (covTypingCTyCov E) M ρ A u ↔ ElTCovM M ρ A u := Iff.rfl

theorem envTypedCovAtP_ctyCov_iff (M : CtxModelT E) (Γ : LCtx) (ρ : EnvT) :
    EnvTypedCovAtP (covTypingCTyCov E) M Γ ρ ↔ EnvTypedCovAtM M Γ ρ := Iff.rfl

theorem envTypedCovAtP_nil (C : CovTyping E) (M : CtxModelT E) (ρ : EnvT) :
    EnvTypedCovAtP C M [] ρ :=
  ⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩

/-- Assumption-only contexts admit the bottom valuation when the model retains
bottom observations.  The no-values premise is stated explicitly. -/
theorem envTypedCovAtP_bot_of_no_values (C : CovTyping E) {Γ : LCtx}
    (hbot : ∀ A, M.Ap EnvT.bot A .bot) (hV : ∀ i, lookupValue Γ i = none) :
    EnvTypedCovAtP C M Γ EnvT.bot := by
  refine ⟨?_, ?_⟩
  · intro i A _ u hu
    change u = .bot at hu
    subst u
    exact ⟨.bot, hbot A, C.bot .bot⟩
  · intro i v hv
    rw [hV i] at hv
    exact Option.noConfusion hv

/-- Transport of a realized type observation requires agreement at that type. -/
theorem elTCovP_congr {A : Expr Nat} (hA : ModelAgreementAtT M N A)
    (ρ : EnvT) (u : CptT) : ElTCovP C M ρ A u ↔ ElTCovP C N ρ A u := by
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, (hA ρ a).mp ha, hu⟩
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, (hA ρ a).mpr ha, hu⟩

/-- The two sides of a let-value equation both participate in model transport. -/
theorem ctxEnvM_cov_congr {Γ : LCtx} {ρ : EnvT}
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) : CtxEnvM M Γ ρ ↔ CtxEnvM N Γ ρ := by
  constructor
  · intro h i v hv c
    exact (hB i ρ c).symm.trans ((h i v hv c).trans (hV i v hv ρ c))
  · intro h i v hv c
    exact (hB i ρ c).trans ((h i v hv c).trans (hV i v hv ρ c).symm)

theorem envTypedCovAtP_congr {Γ : LCtx} {ρ : EnvT}
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ) :
    EnvTypedCovAtP C M Γ ρ ↔ EnvTypedCovAtP C N Γ ρ := by
  constructor
  · intro h
    exact ⟨fun i A hA u hu => (elTCovP_congr (hT i A hA) ρ u).mp (h.1 i A hA u hu),
      (ctxEnvM_cov_congr hB hV).mp h.2⟩
  · intro h
    exact ⟨fun i A hA u hu => (elTCovP_congr (hT i A hA) ρ u).mpr (h.1 i A hA u hu),
      (ctxEnvM_cov_congr hB hV).mpr h.2⟩

theorem envTypedCovAtP_approxTK_iff_of_kFree {Ξ Γ : LCtx} {ρ : EnvT}
    (hV : KFreeValuesT E Γ) (hT : KFreeTypesT E Γ) :
    EnvTypedCovAtP C (ctxModelT_approxTK E n Ξ) Γ ρ ↔
      EnvTypedCovAtP C (ctxModelT_approxT E) Γ ρ :=
  envTypedCovAtP_congr (fun i => modelAgreementAtT_kFree (kFreeT_bvar E i))
    (valueAgreementT_approxTK_of_kFree hV) (typeAgreementT_approxTK_of_kFree hT)

/-- Related substitutions retain native substitution evidence and both coherent,
typed semantic environments.  The let gate includes observations of the values. -/
structure RelSubstAtCov (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    (Δ : LCtx) (ρ ρ' : EnvT) (σ σ' : SubstT) (Γ : LCtx) : Prop where
  typedL : TypedSubstT E n Δ σ Γ
  typedR : TypedSubstT E n Δ σ' Γ
  conv : ConvSubstT E n Δ σ σ' Γ
  envL : EnvTypedCovAtP C M Γ ρ
  envR : EnvTypedCovAtP C M Γ ρ'
  vars : ∀ i A, lookupType Γ i = some A → ∀ c, ρ i c ∨ ρ' i c →
    LRSCoreCov C R n Δ (σ i) (σ' i) (substT σ A) c ∧
    LRSCoreCov C R n Δ (σ' i) (σ i) (substT σ' A) c ∧
    LRSCoreCov C R n Δ (σ i) (σ i) (substT σ A) c ∧
    LRSCoreCov C R n Δ (σ' i) (σ' i) (substT σ' A) c
  lets : ∀ i v A, lookupValue Γ i = some v → lookupType Γ i = some A →
    ∀ c, ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c →
    LRSCoreCov C R n Δ (σ i) (substT σ' v) (substT σ A) c ∧
    LRSCoreCov C R n Δ (σ' i) (substT σ v) (substT σ' A) c ∧
    LRSCoreCov C R n Δ (σ i) (substT σ v) (substT σ A) c ∧
    LRSCoreCov C R n Δ (σ' i) (substT σ' v) (substT σ' A) c

/-- Both actual let-coherence guards are available without a relation theorem. -/
theorem RelSubstAtCov.ctxEnvs {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ) :
    CtxEnvM M Γ ρ ∧ CtxEnvM M Γ ρ' := ⟨h.envL.2, h.envR.2⟩

/-- A complete diagonal package for an assumption-only source context, from
native substitution typing.  This is useful for testing fully quantified motives. -/
theorem relSubstAtCov_bot_diagonal_of_no_values (C : CovTyping E) {Δ Γ : LCtx}
    {σ : SubstT} (hT : TypedSubstT E n Δ σ Γ)
    (hbot : ∀ A, M.Ap EnvT.bot A .bot) (hV : ∀ i, lookupValue Γ i = none) :
    RelSubstAtCov C M R n Δ EnvT.bot EnvT.bot σ σ Γ := by
  have hρ := envTypedCovAtP_bot_of_no_values C hbot hV
  refine ⟨hT, hT, ?_, hρ, hρ, ?_, ?_⟩
  · intro i A hA
    obtain ⟨hi⟩ := hT.1 i A hA
    exact ⟨.refl _ _ _ hi⟩
  · intro i A _ c hc
    have he : c = .bot := hc.elim id id
    subst c
    have hr := lrSCoreCov_bot (R := R) (n := n) C Δ (σ i) (σ i) (substT σ A)
    exact ⟨hr, hr, hr, hr⟩
  · intro i v A hv
    rw [hV i] at hv
    exact Option.noConfusion hv

/-- The model changes only in the environment guards and in the let gate. -/
theorem RelSubstAtCov.modelMap {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ)
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ) :
    RelSubstAtCov C N R n Δ ρ ρ' σ σ' Γ where
  typedL := h.typedL
  typedR := h.typedR
  conv := h.conv
  envL := (envTypedCovAtP_congr hB hV hT).mp h.envL
  envR := (envTypedCovAtP_congr hB hV hT).mp h.envR
  vars := h.vars
  lets := by
    intro i v A hv hA c hc
    apply h.lets i v A hv hA c
    exact (or_congr Iff.rfl (or_congr Iff.rfl
      (or_congr (hV i v hv ρ c) (hV i v hv ρ' c)))).mpr hc

theorem relSubstAtCov_congr {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ) :
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ ↔
      RelSubstAtCov C N R n Δ ρ ρ' σ σ' Γ :=
  ⟨fun h => h.modelMap hB hV hT,
    fun h => h.modelMap (fun i => modelAgreementAtT_symm (hB i))
      (fun i v hv => modelAgreementAtT_symm (hV i v hv))
      (fun i A hA => modelAgreementAtT_symm (hT i A hA))⟩

theorem relSubstAtCov_approxTK_iff_of_kFree {Ξ Δ Γ : LCtx}
    {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hV : KFreeValuesT E Γ) (hT : KFreeTypesT E Γ) :
    RelSubstAtCov C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ ↔
      RelSubstAtCov C (ctxModelT_approxT E) R n Δ ρ ρ' σ σ' Γ :=
  relSubstAtCov_congr (fun i => modelAgreementAtT_kFree (kFreeT_bvar E i))
    (valueAgreementT_approxTK_of_kFree hV) (typeAgreementT_approxTK_of_kFree hT)

/-- Reuse of the old package is conditional on actual recursive-relation
agreement, in addition to the separately retained coherent environment guards. -/
theorem relSubstAtCov_iff_old_of_relation_iff {Δ Γ : LCtx}
    {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hrel : ∀ x y A c, LRSCoreCov C R n Δ x y A c ↔ LRSCoreS R E n Δ x y A c) :
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ ↔
      RelSubstAtT M R n Δ ρ ρ' σ σ' Γ ∧
        EnvTypedCovAtP C M Γ ρ ∧ EnvTypedCovAtP C M Γ ρ' := by
  constructor
  · intro h
    refine ⟨⟨h.typedL, h.typedR, h.conv, ?_, ?_⟩, h.envL, h.envR⟩
    · intro i A hA c hc
      exact (and_congr (hrel _ _ _ _) (and_congr (hrel _ _ _ _)
        (and_congr (hrel _ _ _ _) (hrel _ _ _ _)))).mp (h.vars i A hA c hc)
    · intro i v A hv hA c hc
      exact (and_congr (hrel _ _ _ _) (and_congr (hrel _ _ _ _)
        (and_congr (hrel _ _ _ _) (hrel _ _ _ _)))).mp (h.lets i v A hv hA c hc)
  · rintro ⟨⟨ht, ht', hc, hvars, hlets⟩, hρ, hρ'⟩
    refine ⟨ht, ht', hc, hρ, hρ', ?_, ?_⟩
    · intro i A hA c hc
      exact (and_congr (hrel _ _ _ _) (and_congr (hrel _ _ _ _)
        (and_congr (hrel _ _ _ _) (hrel _ _ _ _)))).mpr (hvars i A hA c hc)
    · intro i v A hv hA c hc
      exact (and_congr (hrel _ _ _ _) (and_congr (hrel _ _ _ _)
        (and_congr (hrel _ _ _ _) (hrel _ _ _ _)))).mpr (hlets i v A hv hA c hc)

private theorem cov_kFreeValues_zetaLocalSortCtx (E : ResolvedEnv) :
    KFreeValuesT E zetaLocalSortCtx := by
  intro i v hv
  cases i with
  | zero =>
    change some (.sort .zero) = some v at hv
    cases Option.some.inj hv
    exact kFreeT_sort E .zero
  | succ i => simp [zetaLocalSortCtx, lookupValue] at hv

private theorem cov_kFreeTypes_zetaLocalSortCtx (E : ResolvedEnv) :
    KFreeTypesT E zetaLocalSortCtx := by
  intro i A hA
  cases i with
  | zero =>
    change some (.sort (.succ .zero)) = some A at hA
    cases Option.some.inj hA
    exact kFreeT_sort E (.succ .zero)
  | succ i => simp [zetaLocalSortCtx, lookupType] at hA

/-- The canonical valuation of a genuine let context remains typed and coherent
after K-free transport to the saturated model. -/
theorem envTypedCovAtP_zetaLocalSortCtx_approxTK (E : ResolvedEnv) (n : Nat) (Ξ : LCtx) :
    EnvTypedCovAtP (covTypingCTyCov E) (ctxModelT_approxTK E n Ξ)
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) := by
  apply (envTypedCovAtP_approxTK_iff_of_kFree
    (cov_kFreeValues_zetaLocalSortCtx E) (cov_kFreeTypes_zetaLocalSortCtx E)).mpr
  change EnvTypedCovAtT E zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx)
  exact envTypedCovAtT_cons_letBinding (envTypedCovAtT_nil E EnvT.bot)
    (fun _ hu => covTyping_sort E EnvT.bot .zero hu)

private theorem cov_sort_zero_shape {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ (.sort .zero) c) : c = .bot ∨ c = .prop :=
  (approxT_sort_inv h).imp_right (fun hc => hc.trans sortCode_zero)

private theorem cov_zetaLocalSortCtx_relation (C : CovTyping E) (n : Nat)
    {y : Expr Nat} {c : CptT} (hy : y = .bvar 0 ∨ y = .sort .zero)
    (hc : c = .bot ∨ c = .prop) :
    LRSCoreCov C (WhStepCK2 E n) n zetaLocalSortCtx (.bvar 0) y
      (.sort (.succ .zero)) c := by
  rcases hc with rfl | rfl
  · rw [LRSCoreCov.eq_def]
    trivial
  · rw [LRSCoreCov.eq_def]
    have hz : RedR (WhStepCK2 E n) zetaLocalSortCtx (.bvar 0) (.sort .zero) :=
      redR_single (.ctx (.zetaLocal rfl))
    refine ⟨⟨.succ .zero, .refl _⟩, .zero, .zero, hz, ?_⟩
    rcases hy with rfl | rfl
    · exact hz
    · exact .refl _

/-- The full new package is inhabited at identity substitution in a native let
context.  The environment contains the bound sort's non-bottom observation. -/
theorem relSubstAtCov_zetaLocalSortCtx_approxTK (hW : EnvWfT E) (n : Nat) (Ξ : LCtx) :
    RelSubstAtCov (covTypingCTyCov E) (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx)
      SubstT.id SubstT.id zetaLocalSortCtx := by
  have ht := typedSubstT_id (envClosed_of_envWfT hW) (zetaLocalSortCtx_wf E n)
  have hρ := envTypedCovAtP_zetaLocalSortCtx_approxTK E n Ξ
  refine ⟨ht, ht, ?_, hρ, hρ, ?_, ?_⟩
  · intro i A hA
    obtain ⟨hi⟩ := ht.1 i A hA
    exact ⟨.refl _ _ _ hi⟩
  · intro i A hA c hc
    cases i with
    | zero =>
      change some (.sort (.succ .zero)) = some A at hA
      cases Option.some.inj hA
      have hs : c = .bot ∨ c = .prop := cov_sort_zero_shape (hc.elim id id)
      have hr := cov_zetaLocalSortCtx_relation (covTypingCTyCov E) n (Or.inl rfl) hs
      simpa only [SubstT.id, substT_id] using And.intro hr (And.intro hr (And.intro hr hr))
    | succ i => simp [zetaLocalSortCtx, lookupType] at hA
  · intro i v A hv hA c hc
    cases i with
    | zero =>
      change some (.sort .zero) = some v at hv
      cases Option.some.inj hv
      change some (.sort (.succ .zero)) = some A at hA
      cases Option.some.inj hA
      have hs : c = .bot ∨ c = .prop := by
        rcases hc with h | h | h | h
        · exact cov_sort_zero_shape h
        · exact cov_sort_zero_shape h
        · exact cov_sort_zero_shape (approxTK_forget h)
        · exact cov_sort_zero_shape (approxTK_forget h)
      have hr := cov_zetaLocalSortCtx_relation (covTypingCTyCov E) n (Or.inr rfl) hs
      simpa only [SubstT.id, substT_id] using And.intro hr (And.intro hr (And.intro hr hr))
    | succ i => simp [zetaLocalSortCtx, lookupValue] at hv

/-- Native let conversion, both guarded substitutions, and a shared non-bottom
observation all occur in the same nonempty context and canonical valuation. -/
theorem zetaLocalSortCtx_cov_related_control (hW : EnvWfT E) (n : Nat) (Ξ : LCtx) :
    Nonempty (CtxWfT E n zetaLocalSortCtx) ∧
    Nonempty (HasTyT E n zetaLocalSortCtx (.bvar 0) (.sort (.succ .zero))) ∧
    Nonempty (ConvT E n zetaLocalSortCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero))) ∧
    RelSubstAtCov (covTypingCTyCov E) (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      zetaLocalSortCtx (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx)
      SubstT.id SubstT.id zetaLocalSortCtx ∧
    ∃ c, c ≠ .bot ∧ ctxEnvT E zetaLocalSortCtx 0 c ∧
      ApproxTK E n Ξ (ctxEnvT E zetaLocalSortCtx) (.bvar 0) c ∧
      ApproxTK E n Ξ (ctxEnvT E zetaLocalSortCtx) (.sort .zero) c ∧
      LRSCoreCov (covTypingCTyCov E) (WhStepCK2 E n) n zetaLocalSortCtx
        (.bvar 0) (.sort .zero) (.sort (.succ .zero)) c := by
  have hS := relSubstAtCov_zetaLocalSortCtx_approxTK hW n Ξ
  have hp : ctxEnvT E zetaLocalSortCtx 0 .prop := by
    change ApproxT E EnvT.bot (.sort .zero) .prop
    rw [← sortCode_zero]
    exact approxT_sort_code E EnvT.bot .zero
  refine ⟨⟨zetaLocalSortCtx_wf E n⟩, ⟨.bvar _ 0 _ rfl⟩,
    ⟨zetaLocalSortCtx_conv E n⟩, hS, .prop, (fun h => CptT.noConfusion h), hp,
    (approxTK_bvar_iff 0 .prop).mpr (Or.inr hp), ?_, ?_⟩
  · rw [← sortCode_zero]
    exact approxTK_sort_code E n Ξ (ctxEnvT E zetaLocalSortCtx) .zero
  · simpa only [SubstT.id, substT_id] using
      (hS.lets 0 (.sort .zero) (.sort (.succ .zero)) rfl rfl .prop (Or.inl hp)).1

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_SUBST_ROOTS
#print axioms ElTCovP
#print axioms EnvTypedCovAtP
#print axioms elTCovP_ctyCov_iff
#print axioms envTypedCovAtP_ctyCov_iff
#print axioms envTypedCovAtP_nil
#print axioms envTypedCovAtP_bot_of_no_values
#print axioms elTCovP_congr
#print axioms ctxEnvM_cov_congr
#print axioms envTypedCovAtP_congr
#print axioms envTypedCovAtP_approxTK_iff_of_kFree
#print axioms RelSubstAtCov
#print axioms RelSubstAtCov.ctxEnvs
#print axioms relSubstAtCov_bot_diagonal_of_no_values
#print axioms RelSubstAtCov.modelMap
#print axioms relSubstAtCov_congr
#print axioms relSubstAtCov_approxTK_iff_of_kFree
#print axioms relSubstAtCov_iff_old_of_relation_iff
#print axioms envTypedCovAtP_zetaLocalSortCtx_approxTK
#print axioms relSubstAtCov_zetaLocalSortCtx_approxTK
#print axioms zetaLocalSortCtx_cov_related_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_SUBST_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelAudit
