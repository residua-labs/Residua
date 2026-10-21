import rcic.RcicNativeTypedModelCovNormCov2
import rcic.RcicNativeTypedModelCovRelFund
import rcic.RcicNativeTypedModelCovNormLetCases
import rcic.RcicNativeTypedModelCovNormConstCases
import rcic.RcicNativeTypedModelCovNormApp
import rcic.RcicNativeTypedModelCovNormSaturatedControl

/-!
# Native conversion cases and an actual eta obstruction

The unchanged conversion motive accepts an observation at either endpoint.
At the native eta conversion of `Nat.succ`, its right endpoint has the rigid
compact `spine 2 []`. The left endpoint is a weak-head-normal lambda, so it
cannot satisfy the recursive relation's rigid-spine leaf. This excludes a
complete `FundCovCases` supplier even after `CTyCov2` repairs the successor's
compact typing. The type is already normal and its `C2` realization exists.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormConvCasesAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelAudit.TypingFin ReadbackCKAudit ReadbackCK2Audit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelCovKAudit
open TypedModelCovRelAudit TypedModelCovRelWitnessAudit
open TypedModelCovRelRealizationAudit TypedModelCovNormCov2Audit
open TypedModelCovNormSubstAudit TypedModelCovNormTyCasesAudit
open TypedModelKIndexFreeAudit TypedModelKTransportAudit
open TypedModelCovNormAppAudit
open TypedModelCovNormSaturatedControlAudit
open ReadbackCK2InputsAudit ReadbackCK2IndexAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M : CtxModelT E}
  {R : Readback} {n : Nat}

/-- The semantic input for a forward computation case. It asserts only
preservation of actual observations and contains no fundamental conclusion. -/
def CovModelContractAt (M : CtxModelT E) (src dst : Expr Nat) : Prop :=
  ∀ ρ c, M.Ap ρ src c → M.Ap ρ dst c

/-- The exact model-side type witness for a conversion observation. This
port does not assert the relation conclusion of any conversion case. -/
def CovConvObservedTypeFor (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (x y A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ x c ∨ M.Ap ρ' y c →
      ∃ a, (M.Ap ρ A a ∨ M.Ap ρ' A a) ∧ C.ty c a

/-- Type diagonals and the reverse type comparison used by the typed PER.
The quantified code is an actual observation of this specific source type. -/
def CovTypeDiagonalsFor (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
    ∀ a, M.Ap ρ A a ∨ M.Ap ρ' A a → ∃ w,
      LRSCoreCov C R n Δ (substT σ A) (substT σ A) (.sort w) a ∧
      LRSCoreCov C R n Δ (substT σ' A) (substT σ' A) (.sort w) a ∧
      LRSCoreCov C R n Δ (substT σ' A) (substT σ A) (.sort w) a

/-- Transitivity needs an observation of the shared syntactic middle at the
same compact. Either actual source valuation is sufficient. -/
def CovMiddleObservationFor (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (x y z : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ x c ∨ M.Ap ρ' z c → M.Ap ρ y c ∨ M.Ap ρ' y c

/-- Finite binder factorization at one specified beta redex. All facts are
model observations and compact typing at the actual annotation. -/
def CovBetaFactorFor (C : CovTyping E) (M : CtxModelT E)
    (A body arg : Expr Nat) : Prop :=
  ∀ ρ c, M.Ap ρ (.app (.lam A body) arg) c ∨ M.Ap ρ (instantiate0 arg body) c →
    c = .bot ∨ ∃ a d, M.Ap ρ A a ∧ (∀ v ∈ d, C.ty v a) ∧
      (∀ v ∈ d, M.Ap ρ arg v) ∧ M.Ap (EnvT.cons (demandT d) ρ) body c

/-- Right-hand binder annotations must cover the finite demand in the raw
left-hand annotation model. This is separate from native type conversion. -/
def CovDomainDemandTransportFor (C : CovTyping E) (M : CtxModelT E)
    (A A' : Expr Nat) : Prop :=
  ∀ ρ a (d : List CptT), M.Ap ρ A' a → (∀ v ∈ d, CTyS E v a) →
    ∃ a', M.Ap ρ A a' ∧ ∀ v ∈ d, C.ty v a'

/-- Pull an instantiated-body observation back to the full value valuation.
Unlike finite demand extension, this can support a coherent let binding. -/
def CovInstObservation (M : CtxModelT E) (value body : Expr Nat) : Prop :=
  ∀ ρ c, M.Ap ρ (instantiate0 value body) c →
    M.Ap (EnvT.cons (fun u => M.Ap ρ value u) ρ) body c

/-- Proof irrelevance uses actual collapse of the observed proof compacts.
This statement contains no native conversion or relation conclusion. -/
def CovProofCollapseFor (M : CtxModelT E) (p q : Expr Nat) : Prop :=
  ∀ ρ ρ' c, M.Ap ρ p c ∨ M.Ap ρ' q c → c = .bot

/-- The native part of reversing the full related package is obtained from
the landed substitution theorem, independently of relation symmetry. -/
theorem relSubstAtCov_symm_native (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    {Γ Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hΓ : CtxWfT E n Γ) (hΔ : CtxWfT E n Δ)
    (h : RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ) :
    RelSubstAtCov C M R n Δ ρ' ρ σ' σ Γ := by
  refine ⟨h.typedR, h.typedL, ?_, h.envR, h.envL, ?_, ?_⟩
  · intro i A hA
    obtain ⟨hc⟩ := h.conv i A hA
    obtain ⟨w, ⟨ht⟩⟩ :=
      Rcic.Declarative.NativeValleys.TypedModelAudit.ctxWfT_lookupType_sort hcl hΓ hA
    obtain ⟨hAc⟩ := convT_substT_pointwise hW hcl hst hι hΓ ht hΔ
      h.typedL h.typedR h.conv
    exact ⟨.tyConv _ _ _ _ _ w (.symm _ _ _ _ hc) hAc⟩
  · intro i A hA c hc
    obtain ⟨h1, h2, h3, h4⟩ := h.vars i A hA c hc.symm
    exact ⟨h2, h1, h4, h3⟩
  · intro i v A hv hA c hc
    have hc' : ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c := by
      rcases hc with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    obtain ⟨h1, h2, h3, h4⟩ := h.lets i v A hv hA c hc'
    exact ⟨h2, h1, h4, h3⟩

/-- Symmetry uses the genuine conversion child, its reversed substitution
instance, and the exact observed-type/diagonal ports. -/
theorem fundCov_symm_step_of_inputs (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {x y A : Expr Nat} (h : ConvT E n Γ x y A)
    (hTy : CovConvObservedTypeFor C M R n Γ y x A)
    (hDiag : CovTypeDiagonalsFor C M R n Γ A) :
    FundConvCovStep C M R n (ConvT.symm Γ x y A h) := by
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  have hlt : sizeOf h < sizeOf (ConvT.symm Γ x y A h) := by simp; omega
  obtain ⟨a, ha, hca⟩ := hTy hΔ hSub c hc
  obtain ⟨w, _, hA'A', hA'A⟩ := hDiag hΔ hSub a ha
  have hRev := relSubstAtCov_symm_native hW hcl hst hι hΓ hΔ hSub
  have hxy := ih.2 h hlt hΓ hΔ hRev c hc.symm
  have hyx := lrSCoreCov_symm_tm C hL hNU hW hS hT a c hΔ hA'A' hca hxy
  exact lrSCoreCov_irrel C hL hNU hW hS hT a c hΔ hA'A hca hyx

/-- The two transitivity calls are made at the real conversion children.
Re-pairing the observed valuation keeps the syntactic middle at the left
substitution, so the recursive relation composes at one common expression. -/
theorem fundCov_trans_step_of_inputs (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {x y z A : Expr Nat}
    (h1 : ConvT E n Γ x y A) (h2 : ConvT E n Γ y z A)
    (hTy : CovConvObservedTypeFor C M R n Γ x z A)
    (hDiag : CovTypeDiagonalsFor C M R n Γ A)
    (hMid : CovMiddleObservationFor C M R n Γ x y z) :
    FundConvCovStep C M R n (ConvT.trans Γ x y z A h1 h2) := by
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  have hlt1 : sizeOf h1 < sizeOf (ConvT.trans Γ x y z A h1 h2) := by simp; omega
  have hlt2 : sizeOf h2 < sizeOf (ConvT.trans Γ x y z A h1 h2) := by simp; omega
  obtain ⟨a, ha, hca⟩ := hTy hΔ hSub c hc
  obtain ⟨w, hAA, _, _⟩ := hDiag hΔ hSub a ha
  have finish : ∀ θ, θ = ρ ∨ θ = ρ' → M.Ap θ y c →
      LRSCoreCov C R n Δ (substT σ x) (substT σ' z) (substT σ A) c := by
    intro θ hθ hm
    have hp := relSubstAtCov_envs hSub θ θ hθ hθ
    have hxy := ih.2 h1 hlt1 hΓ hΔ hp.diagL c (Or.inr hm)
    have hyz := ih.2 h2 hlt2 hΓ hΔ hp c (Or.inl hm)
    exact lrSCoreCov_trans_tm C hL hNU hW hS hT a c hΔ hAA hca hxy hyz
  exact (hMid hΔ hSub c hc).elim (finish ρ (Or.inl rfl)) (finish ρ' (Or.inr rfl))

/-- Type conversion uses exactly its two native conversion children. It
does not recurse on the generated typing of either endpoint. -/
theorem fundCov_tyConv_step_of_observedType (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Γ : LCtx} {x y A B : Expr Nat} {u : Level}
    (h : ConvT E n Γ x y A) (hA : ConvT E n Γ A B (.sort u))
    (hTy : CovConvObservedTypeFor C M R n Γ x y A) :
    FundConvCovStep C M R n (ConvT.tyConv Γ x y A B u h hA) := by
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  have hlt : sizeOf h < sizeOf (ConvT.tyConv Γ x y A B u h hA) := by simp; omega
  have hltA : sizeOf hA < sizeOf (ConvT.tyConv Γ x y A B u h hA) := by simp; omega
  obtain ⟨a, ha, hca⟩ := hTy hΔ hSub c hc
  have hAB : LRSCoreCov C R n Δ (substT σ A) (substT σ B) (.sort u) a := by
    rcases ha with ha | ha
    · exact ih.2 hA hltA hΓ hΔ hSub.diagL a (Or.inl ha)
    · exact ih.2 hA hltA hΓ hΔ
        (relSubstAtCov_envs hSub ρ' ρ' (Or.inr rfl) (Or.inr rfl)).diagL a (Or.inl ha)
  exact lrSCoreCov_irrel C hL hNU hW hS hT a c hΔ hAB hca
    (ih.2 h hlt hΓ hΔ hSub c hc)

/-- The proof-irrelevance residual has no recursive-relation premise and
requires no unsupported global typing theorem. -/
theorem fundCov_irr_step_of_collapse {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (hCollapse : CovProofCollapseFor M p q) :
    FundConvCovStep C M R n (ConvT.irr Γ P p q hP hp hq) := by
  intro _ _ Δ ρ ρ' σ σ' _ _ c hc
  obtain rfl := hCollapse ρ ρ' c hc
  exact lrSCoreCov_bot C _ _ _ _

/-- Beta factorization is consumed under a realized assumption extension.
Every recursive call is at one of the constructor's three genuine children. -/
theorem fundCov_beta_step_of_factor (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    (hM : CovLiftModelLaws M)
    {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hb : HasTyT E n (.assumption A :: Γ) body B)
    (ha : HasTyT E n Γ arg A)
    (hFactor : CovBetaFactorFor C M A body arg) :
    FundConvCovStep C M R n (ConvT.beta Γ A body arg B u hA hb ha) := by
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  have hltA : sizeOf hA < sizeOf (ConvT.beta Γ A body arg B u hA hb ha) := by simp; omega
  have hltb : sizeOf hb < sizeOf (ConvT.beta Γ A body arg B u hA hb ha) := by simp; omega
  have hlta : sizeOf ha < sizeOf (ConvT.beta Γ A body arg B u hA hb ha) := by simp; omega
  obtain ⟨_, _, ⟨hAc⟩⟩ := hSub.nativeInstances hW hcl hst hι hΓ hΔ hA
  obtain ⟨⟨harg⟩, ⟨harg'⟩, ⟨hargc⟩⟩ := hSub.nativeInstances hW hcl hst hι hΓ hΔ ha
  have fromSide : ∀ θ, θ = ρ ∨ θ = ρ' →
      (M.Ap θ (.app (.lam A body) arg) c ∨ M.Ap θ (instantiate0 arg body) c) →
      LRSCoreCov C R n Δ (substT σ (.app (.lam A body) arg))
        (substT σ' (instantiate0 arg body)) (substT σ (instantiate0 arg B)) c := by
    intro θ hθ ho
    rcases hFactor θ c ho with rfl | ⟨a, d, hAa, hd, hargObs, hbodyObs⟩
    · exact lrSCoreCov_bot C _ _ _ _
    · have hp := relSubstAtCov_envs hSub θ θ hθ hθ
      have hAA' := ih.1 hA hltA hΓ hΔ hp a (Or.inl hAa)
      have hAA := ih.1 hA hltA hΓ hΔ hp.diagL a (Or.inl hAa)
      have hdem : ∀ v ∈ d,
          LRSCoreCov C R n Δ (substT σ arg) (substT σ' arg) (substT σ A) v := by
        intro v hv
        exact ih.1 ha hlta hΓ hΔ hp v (Or.inl (hargObs v hv))
      have hext := relSubstAtCov_cons_realized hL hNU hW hS hT hM
        hΔ hp hAa hd hAA' hAA hAc harg harg' hargc hdem
      have hbody := ih.1 hb hltb (.assumption Γ A u hΓ hA)
        hΔ hext c (Or.inl hbodyObs)
      have htarget : LRSCoreCov C R n Δ (substT σ (instantiate0 arg body))
          (substT σ' (instantiate0 arg body)) (substT σ (instantiate0 arg B)) c := by
        simpa only [substT_instantiate0, instantiate0_substT_up] using hbody
      have hread : RedR R Δ (substT σ (.app (.lam A body) arg))
          (substT σ (instantiate0 arg body)) := by
        simpa only [substT, substT_instantiate0] using
          redR_single (hL.beta Δ (substT σ A) (substT σ.up body) (substT σ arg))
      exact lrSCoreCov_expand_red C hL hread c htarget
  exact hc.elim (fun h => fromSide ρ (Or.inl rfl) (Or.inl h))
    (fun h => fromSide ρ' (Or.inr rfl) (Or.inr h))

/-- Zeta uses the original let-body child and preserves its let-binding
context. The two semantic ports specify observation transport and coherence. -/
theorem fundCov_zeta_step_of_inputs (hL : ReadbackLaws E (WhStepCK2 E n))
    {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B)
    (hInput : CovLetInput C M (WhStepCK2 E n) n Γ A value body)
    (hInst : CovInstObservation M value body) :
    FundConvCovStep C M (WhStepCK2 E n) n (ConvT.zeta Γ A value body B u hA hv hb) := by
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  have hlt : sizeOf hb < sizeOf (ConvT.zeta Γ A value body B u hA hv hb) := by simp; omega
  have hbody := ih.1 hb hlt (.letBinding Γ A u value hΓ hA hv)
    hΔ (hInput.subst hΔ hSub) c
    (hc.elim (fun h => Or.inl (hInput.body h)) (fun h => Or.inr (hInst ρ' c h)))
  have hout := lrSCoreCov_expand_red C hL
    (cov_let_subst_read E n Δ σ A value body) c hbody
  simpa only [substT_instantiate0, instantiate0_substT_up] using hout

/-- Instantiation observation is supplied by the landed model substitution
theorem; no native typing or relation premise occurs here. -/
theorem covInstObservation_approxT (E : ResolvedEnv) (value body : Expr Nat) :
    CovInstObservation (ctxModelT_approxT E) value body := by
  intro ρ c hc
  exact (approxT_subst0_iff E ρ value body c).mp hc

theorem covInstObservation_approxTK_of_no_indexed
    (hE : ∀ r, ¬ IndexedPropRecT E r) (n : Nat) (Ξ : LCtx) (value body : Expr Nat) :
    CovInstObservation (ctxModelT_approxTK E n Ξ) value body := by
  rw [ctxModelT_approxTK_eq_approxT_of_no_indexed hE]
  exact covInstObservation_approxT E value body

/-- The identity-body control also works in indexed environments, because
the bvar observation equivalence is supplied independently of indexed rules. -/
theorem covInstObservation_bvar0_approxTK (E : ResolvedEnv) (n : Nat)
    (Ξ : LCtx) (value : Expr Nat) :
    CovInstObservation (ctxModelT_approxTK E n Ξ) value (.bvar 0) := by
  intro ρ c hc
  exact (approxTK_bvar_iff 0 c).mpr (Or.inr hc)

/-- The finite beta port is fully supplied for an actual sort-valued
identity application, at every source environment of the saturated model. -/
theorem covBetaFactorFor_sortIdentity (C : CovTyping E) (hCS : CovTypingIncludesS C)
    (n : Nat) (Ξ : LCtx) :
    CovBetaFactorFor C (ctxModelT_approxTK E n Ξ)
      (.sort (.succ .zero)) (.bvar 0) (.sort .zero) := by
  intro ρ c hc
  have hcSort : ApproxT E ρ (.sort .zero) c := by
    rcases hc with hc | hc
    · exact covConv_beta_fwd (covModelSubstFactorT_approxT E) ρ _ _ _ (approxTK_forget hc)
    · exact approxTK_forget hc
  have hs : c = .bot ∨ c = .prop := by
    simpa only [sortCode_zero] using approxT_sort_inv hcSort
  rcases hs with rfl | rfl
  · exact Or.inl rfl
  · refine Or.inr ⟨.sort, [.prop], ?_, ?_, ?_, ?_⟩
    · simpa only [sortCode_succ] using approxTK_sort_code E n Ξ ρ (.succ .zero)
    · intro v hv
      obtain rfl := List.mem_singleton.mp hv
      apply hCS .sort .prop
      rw [CTyS]
      exact Or.inr TyCodeCT.prop
    · intro v hv
      obtain rfl := List.mem_singleton.mp hv
      simpa only [sortCode_zero] using approxTK_sort_code E n Ξ ρ .zero
    · exact (approxTK_bvar_iff 0 .prop).mpr (Or.inr (List.mem_singleton.mpr rfl))

/-- The beta, zeta and binder-annotation ports have an actual native
non-bottom fixture in the admitted Nat environment. -/
theorem beta_zeta_semantic_ports_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    CovBetaFactorFor (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (.sort (.succ .zero)) (.bvar 0) (.sort .zero) ∧
    CovInstObservation (ctxModelT_approxTK natEnvU n []) (.sort .zero) (.bvar 0) ∧
    CovDomainDemandTransportFor (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (.sort (.succ .zero)) (.sort (.succ .zero)) ∧
    Nonempty (ConvT natEnvU n []
      (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
      (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (ConvT natEnvU n []
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0))
      (.sort .zero) (.sort (.succ .zero))) ∧
    ApproxTK natEnvU n [] EnvT.bot (.sort .zero) .prop ∧ CptT.prop ≠ .bot := by
  refine ⟨⟨natEnvUWfT⟩, ⟨.nil⟩,
    covBetaFactorFor_sortIdentity (C2 natEnvU) (C2_includesS natEnvU) n [],
    covInstObservation_bvar0_approxTK natEnvU n [] _,
    ?transport,
    ⟨?beta⟩, ⟨?zeta⟩, ?obs, fun h => CptT.noConfusion h⟩
  case transport =>
    intro ρ a d ha hd
    exact ⟨a, ha, fun v hv => C2_includesS natEnvU a v (hd v hv)⟩
  case beta =>
    exact .beta [] _ _ _ (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort [] _) (.bvar _ 0 _ rfl) (.sort [] .zero)
  case zeta =>
    exact .zeta [] _ _ _ (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort [] _) (.sort [] .zero) (.bvar _ 0 _ rfl)
  case obs =>
    simpa only [sortCode_zero] using approxTK_sort_code natEnvU n [] EnvT.bot .zero

/-- Native sort observations supply the pointwise type-code port at every
target context and pair of coherent source environments. -/
theorem covConvObservedTypeFor_sort (C : CovTyping E) (hCS : CovTypingIncludesS C)
    (R : Readback) (n : Nat) (Ξ Γ : LCtx) :
    CovConvObservedTypeFor C (ctxModelT_approxTK E n Ξ) R n Γ
      (.sort .zero) (.sort .zero) (.sort (.succ .zero)) := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  refine ⟨.sort, Or.inl ?_, ?_⟩
  · simpa only [sortCode_succ] using approxTK_sort_code E n Ξ ρ (.succ .zero)
  · have hs : c = .bot ∨ c = .prop := by
      have ho := hc.elim approxTK_sort_inv approxTK_sort_inv
      simpa only [sortCode_zero] using ho
    rcases hs with rfl | rfl
    · exact C.bot .sort
    · apply hCS .sort .prop
      rw [CTyS]
      exact Or.inr TyCodeCT.prop

/-- The corresponding type diagonals are fully supplied at every observed
compact of the sort, including its non-bottom `.sort` observation. -/
theorem covTypeDiagonalsFor_sort (C : CovTyping E) (R : Readback)
    (n : Nat) (Ξ Γ : LCtx) (l : Level) :
    CovTypeDiagonalsFor C (ctxModelT_approxTK E n Ξ) R n Γ (.sort l) := by
  intro Δ ρ ρ' σ σ' _ _ a ha
  have ho := ha.elim approxTK_sort_inv approxTK_sort_inv
  rcases ho with rfl | rfl
  · exact ⟨.succ l, lrSCoreCov_bot C _ _ _ _, lrSCoreCov_bot C _ _ _ _,
      lrSCoreCov_bot C _ _ _ _⟩
  · have hrel : LRSCoreCov C R n Δ (.sort l) (.sort l) (.sort (.succ l)) (sortCode l) := by
      rcases sortCode_prop_or_sort l with h | h
      · rw [h, lrSCoreCov_prop_iff]
        exact ⟨⟨.succ l, .refl _⟩, l, l, .refl _, .refl _⟩
      · rw [h, lrSCoreCov_sort_iff]
        exact ⟨⟨.succ l, .refl _⟩, l, l, .refl _, .refl _⟩
    exact ⟨.succ l, hrel, hrel, hrel⟩

theorem covMiddleObservationFor_refl (C : CovTyping E) (M : CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (x : Expr Nat) :
    CovMiddleObservationFor C M R n Γ x x x := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  exact hc

/-- Equal annotations supply the domain-demand transport port using only
the verified inclusion of the model's introduction typing. -/
theorem covDomainDemandTransportFor_refl (C : CovTyping E)
    (hCS : CovTypingIncludesS C) (M : CtxModelT E) (A : Expr Nat) :
    CovDomainDemandTransportFor C M A A := by
  intro ρ a d ha hd
  exact ⟨a, ha, fun v hv => hCS a v (hd v hv)⟩

/-- The existing admitted polymorphic proof supplies a non-vacuous collapse
port at the actual model. Its native type and bottom observation are inhabited. -/
theorem covProofCollapseFor_polyIdProof (E : ResolvedEnv) (n : Nat) (Ξ : LCtx) :
    CovProofCollapseFor (ctxModelT_approxTK E n Ξ) polyIdProof polyIdProof := by
  intro ρ ρ' c hc
  exact hc.elim (fun h => approxT_polyIdProof_bot E ρ (approxTK_forget h))
    (fun h => approxT_polyIdProof_bot E ρ' (approxTK_forget h))

/-- All typed-PER semantic ports occur with a concrete non-bottom sort
observation in either admitted environment, rather than an empty antecedent. -/
theorem covSort_semantic_ports_control (C : CovTyping E) (hCS : CovTypingIncludesS C)
    (hW : EnvWfT E) (n : Nat) :
    Nonempty (EnvWfT E) ∧
    CovConvObservedTypeFor C (ctxModelT_approxTK E n []) (WhStepCK2 E n) n []
      (.sort .zero) (.sort .zero) (.sort (.succ .zero)) ∧
    CovTypeDiagonalsFor C (ctxModelT_approxTK E n []) (WhStepCK2 E n) n []
      (.sort (.succ .zero)) ∧
    CovMiddleObservationFor C (ctxModelT_approxTK E n []) (WhStepCK2 E n) n []
      (.sort .zero) (.sort .zero) (.sort .zero) ∧
    Nonempty (CtxWfT E n []) ∧
    RelSubstAtCov C (ctxModelT_approxTK E n []) (WhStepCK2 E n) n []
      EnvT.bot EnvT.bot SubstT.id SubstT.id [] ∧
    ApproxTK E n [] EnvT.bot (.sort .zero) .prop ∧ CptT.prop ≠ .bot := by
  refine ⟨⟨hW⟩, covConvObservedTypeFor_sort C hCS _ n [] [],
    covTypeDiagonalsFor_sort C _ n [] [] _,
    covMiddleObservationFor_refl C _ _ n [] _, ⟨.nil⟩,
    relSubstAtCov_nil C _ _ n [] EnvT.bot EnvT.bot SubstT.id SubstT.id,
    ?_, fun h => CptT.noConfusion h⟩
  simpa only [sortCode_zero] using approxTK_sort_code E n [] EnvT.bot .zero

/-- Delta contraction is supplied in the actual saturated model whenever
its instantiated body is K-free. The source is not assumed K-free. -/
theorem covModelContractAt_delta_approxTK (hW : EnvWfT E) {Ξ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hfree : KFreeT E (instantiateLevels ls b)) :
    CovModelContractAt (ctxModelT_approxTK E n Ξ)
      (.const r ls) (instantiateLevels ls b) := by
  intro ρ c hc
  exact ApproxTK.free hfree ((covConv_delta hW hres hbody ρ c).mp (approxTK_forget hc))

/-- Literal contraction is a proved supply at every K-free expansion. -/
theorem covModelContractAt_lit_approxTK {Ξ : LCtx} (t : Nat)
    (hfree : KFreeT E (natExpand t)) :
    CovModelContractAt (ctxModelT_approxTK E n Ξ) (.lit t) (natExpand t) := by
  intro ρ c hc
  apply ApproxTK.free hfree
  have h := approxTK_forget hc
  cases h with
  | bot => exact .bot _ _
  | lit h => exact h

/-- The landed ordinary-iota model law supplies the contraction port on
a K-free RHS. This theorem remains conditional on that model law; the
saturated Nat control below does not manufacture a global iota law. -/
theorem covModelContractAt_iota_approxTK_of_modelIota
    (hI : ModelIotaStepT E (ctxModelT_approxT E)) {Ξ : LCtx}
    {lhs rhs : Expr Nat} (hi : DerivedIota E lhs rhs) (hfree : KFreeT E rhs) :
    CovModelContractAt (ctxModelT_approxTK E n Ξ) lhs rhs := by
  intro ρ c hc
  exact ApproxTK.free hfree ((hI hi ρ c).mp (approxTK_forget hc))

/-- The delta row recurses only on the body typing stored in its native
constructor. Member stability supplies the substituted readback step. -/
theorem fundCov_delta_step_of_contract (hst : EnvMembersSubstTStable E)
    {Ξ Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hcontract : CovModelContractAt (ctxModelT_approxTK E n Ξ)
      (.const r ls) (instantiateLevels ls b)) :
    FundConvCovStep C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      (ConvT.delta Γ r ls m b hres hbody htr hlen hwf hb) := by
  intro hΓ ih
  have hlt : sizeOf hb < sizeOf (ConvT.delta Γ r ls m b hres hbody htr hlen hwf hb) := by
    simp; omega
  have hread : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      CtxWfT E n Δ → RelSubstAtCov C (ctxModelT_approxTK E n Ξ)
        (WhStepCK2 E n) n Δ ρ ρ' σ σ' Γ →
      RedR (WhStepCK2 E n) Δ (substT σ (.const r ls))
        (substT σ (instantiateLevels ls b)) := by
    intro Δ ρ ρ' σ σ' _ _
    rw [substT, (hst r m hres).2 b hbody ls σ]
    exact redR_single (.ctx (.delta hres hbody))
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundConvAtCov_of_model_contract (readbackLaws_whStepCK2 E n) hcontract
    hread (ih.1 hb hlt hΓ) hΔ hSub c hc

/-- This delta adapter's semantic premise is fully supplied by the landed
model theorem at a K-free body. -/
theorem fundCov_delta_step_approxTK_of_kFree (hW : EnvWfT E)
    (hst : EnvMembersSubstTStable E)
    {Ξ Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hfree : KFreeT E (instantiateLevels ls b)) :
    FundConvCovStep C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      (ConvT.delta Γ r ls m b hres hbody htr hlen hwf hb) :=
  by
    intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
    exact fundCov_delta_step_of_contract hst hres hbody htr hlen hwf hb
      (covModelContractAt_delta_approxTK hW hres hbody hfree) hΓ ih hΔ hSub c hc

/-- Iota uses its actual RHS typing child. Its remaining semantic input is
the one-way observation contract at this exact iota pair. -/
theorem fundCov_iota_step_of_contract (hι : IotaSubstT E)
    {Ξ Γ : LCtx} {lhs rhs T : Expr Nat} (h : DerivedIota E lhs rhs)
    (hlhs : HasTyT E n Γ lhs T) (hrhs : HasTyT E n Γ rhs T)
    (hcontract : CovModelContractAt (ctxModelT_approxTK E n Ξ) lhs rhs) :
    FundConvCovStep C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      (ConvT.iota Γ lhs rhs T h hlhs hrhs) := by
  intro hΓ ih
  have hlt : sizeOf hrhs < sizeOf (ConvT.iota Γ lhs rhs T h hlhs hrhs) := by
    simp; omega
  have hread : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      CtxWfT E n Δ → RelSubstAtCov C (ctxModelT_approxTK E n Ξ)
        (WhStepCK2 E n) n Δ ρ ρ' σ σ' Γ →
      RedR (WhStepCK2 E n) Δ (substT σ lhs) (substT σ rhs) := by
    intro Δ ρ ρ' σ σ' _ _
    obtain ⟨hs⟩ := hι lhs rhs h σ
    exact redR_single (.ctx (.iota (derivedIotaU_ofDerivedIota hs)))
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundConvAtCov_of_model_contract (readbackLaws_whStepCK2 E n) hcontract
    hread (ih.1 hrhs hlt hΓ) hΔ hSub c hc

/-- The literal-conversion row consumes its exact expansion child. The
expansion witness is eliminated before the strict-size comparison. -/
theorem fundCov_litConv_step_of_contract {Ξ Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (h : LiteralExpansion t exp) (hexp : HasTyT E n Γ exp T)
    (hcontract : CovModelContractAt (ctxModelT_approxTK E n Ξ) (.lit t) exp) :
    FundConvCovStep C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      (ConvT.lit Γ t exp T h hexp) := by
  cases h
  intro hΓ ih
  have hlt : sizeOf hexp < sizeOf (ConvT.lit Γ t (natExpand t) T (.of t) hexp) := by
    simp
  have hread : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      CtxWfT E n Δ → RelSubstAtCov C (ctxModelT_approxTK E n Ξ)
        (WhStepCK2 E n) n Δ ρ ρ' σ σ' Γ →
      RedR (WhStepCK2 E n) Δ (substT σ (.lit t)) (substT σ (natExpand t)) := by
    intro Δ ρ ρ' σ σ' _ _
    simpa only [substT, substT_natExpand] using
      (redR_single (show WhStepCK2 E n Δ (.lit t) (natExpand t) from .ctx (.lit t)))
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundConvAtCov_of_model_contract (readbackLaws_whStepCK2 E n) hcontract
    hread (ih.1 hexp hlt hΓ) hΔ hSub c hc

/-- The literal-conversion model contract is supplied, not assumed, on the
K-free expansion fragment (in particular, on every Nat-environment term). -/
theorem fundCov_litConv_step_approxTK_of_kFree {Ξ Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (h : LiteralExpansion t exp) (hexp : HasTyT E n Γ exp T)
    (hfree : KFreeT E exp) :
    FundConvCovStep C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      (ConvT.lit Γ t exp T h hexp) := by
  cases h
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_litConv_step_of_contract (.of t) hexp
    (covModelContractAt_lit_approxTK t hfree) hΓ ih hΔ hSub c hc

/-- A non-bottom literal contract control in the admitted Nat environment.
Both observations and the native expansion conversion are concrete. -/
theorem literal_zero_contract_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT natEnvU) ∧
    CovModelContractAt (ctxModelT_approxTK natEnvU n []) (.lit 0) (natExpand 0) ∧
    Nonempty (ConvT natEnvU n [] (.lit 0) (natExpand 0) (.const 0 [])) ∧
    ApproxTK natEnvU n [] ρ (.lit 0) (.spine 1 []) ∧
    ApproxTK natEnvU n [] ρ (natExpand 0) (.spine 1 []) ∧
    (.spine 1 [] : CptT) ≠ .bot := by
  have hz : ApproxT natEnvU ρ (natExpand 0) (.spine 1 []) :=
    .const ρ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero
  exact ⟨⟨natEnvUWfT⟩, covModelContractAt_lit_approxTK 0 (kFreeT_natEnvU _),
    ⟨.lit [] 0 _ _ (.of 0) (hasTyT_natEnvU_zero n [])⟩,
    ApproxTK.free (kFreeT_natEnvU _) (.lit hz),
    ApproxTK.free (kFreeT_natEnvU _) hz, fun h => CptT.noConfusion h⟩

/-- Full contraction at every observation of an Eq call with the literal
`Sort 0` minor. This uses the landed Eq semantics, uniformly in all source
valuations and compacts; no global ordinary-iota law is assumed. -/
theorem covModelContractAt_eqRec_sort (n : Nat) (Ξ : LCtx) (ls : List Level)
    (A a motive b major : Expr Nat) :
    CovModelContractAt (ctxModelT_approxTK eqEnvT n Ξ)
      (recCall (.const 65 ls) [A, a, motive, .sort .zero, b] major)
      (.sort .zero) := by
  intro ρ c hc
  exact ApproxTK.free (kFreeT_sort eqEnvT .zero)
    (eqRec_model_minor_forward (approxTK_forget hc))

/-- The complete ordinary-iota contraction port is inhabited at an actual
closed Eq constructor call. Native conversion, the full empty related
substitution, and the non-bottom saturated-model observation are retained. -/
theorem ordinary_iota_eq_sort_contract_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n []) ∧
    CovModelContractAt (ctxModelT_approxTK eqEnvT n [])
      (iotaLhsOf (eqFnIndexW indexId binderIndexMot indexBinderBeta)) (.sort .zero) ∧
    Nonempty (ConvT eqEnvT n []
      (iotaLhsOf (eqFnIndexW indexId binderIndexMot indexBinderBeta))
      (.sort .zero) (.sort (.succ .zero))) ∧
    RelSubstAtCov (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n [])
      (WhStepCK2 eqEnvT n) n [] ρ ρ SubstT.id SubstT.id [] ∧
    ApproxTK eqEnvT n [] ρ
      (iotaLhsOf (eqFnIndexW indexId binderIndexMot indexBinderBeta)) .prop ∧
    ApproxTK eqEnvT n [] ρ (.sort .zero) .prop ∧ CptT.prop ≠ .bot := by
  let w := eqFnIndexW indexId binderIndexMot indexBinderBeta
  have hargs : ConvArgsT eqEnvT n [] (instantiateLevels [] eqFamT.mtype)
      [indexFn, indexId, indexId] [indexFn, indexId, indexBinderBeta] :=
    .cons _ _ _ _ _ _ ⟨.refl _ _ _ (indexFnTy eqEnvT n [])⟩
      (.cons _ _ _ _ _ _ ⟨.refl _ _ _ (indexIdTy eqEnvT n [])⟩
        (.cons _ _ _ _ _ _ ⟨.symm _ _ _ _ (indexBinderBetaConv eqEnvT n [])⟩ (.nil _)))
  obtain ⟨hfamily⟩ := FamModelAudit.convT_foldApps_of_convArgsT hargs
    (.refl [] (.const 63 []) _ (.const [] 63 [] eqFamT rfl rfl rfl))
  have hcanon : HasTyT eqEnvT n [] binderIndexCtor
      (binderIndexFamily indexBinderBeta) :=
    .conv _ _ _ _ _ (binderIndexCtorTy n []) hfamily
  have hnative : HasTyT eqEnvT n [] (iotaLhsOf w) (.sort (.succ .zero)) :=
    binderIndexRecTy n [] hcanon
  have hsort : ApproxTK eqEnvT n [] ρ (.sort .zero) .prop := by
    simpa only [sortCode_zero] using approxTK_sort_code eqEnvT n [] ρ .zero
  have hsource : ApproxT eqEnvT ρ (iotaLhsOf w) .prop :=
    eqRec_model_minor_backward (approxTK_forget hsort)
  obtain ⟨hi⟩ := derivedIotaT_of_iotaWitness_envWfT pinEqGroupWfT w
  obtain ⟨ws, hl, hr⟩ := derivedIotaT_inv hi
  have hobs : ApproxTK eqEnvT n [] ρ (iotaLhsOf w) .prop := by
    rw [← hl]
    apply ApproxTK.iota ws
    · exact hl.symm ▸ hsource
    · rw [hr]
      exact hsort
  exact ⟨⟨pinEqGroupWfT⟩, ⟨.nil⟩,
    covModelContractAt_eqRec_sort n [] _ indexFn indexId binderIndexMot
      indexBinderBeta binderIndexCtor,
    ⟨.iota [] _ _ _ (.of w) hnative (.sort [] .zero)⟩,
    relSubstAtCov_nil (C2 eqEnvT) _ _ n [] ρ ρ SubstT.id SubstT.id,
    hobs, hsort, fun h => CptT.noConfusion h⟩

/-- Native mixed substitution uses a substituted conversion and the
pointwise conversion of its right endpoint. The generated endpoint typing
is used only for native evidence, never as a recursive fundamental call. -/
theorem relSubstAtCov_nativeConvInstances (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    {Γ Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hΓ : CtxWfT E n Γ) (hΔ : CtxWfT E n Δ)
    (hSub : RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ)
    {x y A : Expr Nat} (h : ConvT E n Γ x y A) :
    Nonempty (ConvT E n Δ (substT σ x) (substT σ' y) (substT σ A)) := by
  obtain ⟨hxy⟩ := convT_substT hW hcl hst hι hΓ h hΔ hSub.typedL
  obtain ⟨_, _, ⟨hyy'⟩⟩ := hSub.nativeInstances hW hcl hst hι hΓ hΔ
    (convEnds hW hΓ h).2.1
  exact ⟨.trans _ _ _ _ _ hxy hyy'⟩

/-- Type PER composition at a common right endpoint supplies the exact
two domain relations used by finite assumption extension. -/
theorem covTypePair_from_common_right (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    {Δ : LCtx} (hΔ : CtxWfT E n Δ) {A A' B : Expr Nat} {u : Level} {a : CptT}
    (hAB : LRSCoreCov C R n Δ A B (.sort u) a)
    (hA'B : LRSCoreCov C R n Δ A' B (.sort u) a) :
    LRSCoreCov C R n Δ A A' (.sort u) a ∧
      LRSCoreCov C R n Δ A A (.sort u) a := by
  have hAA' := lrSCoreCov_trans C hL hNU hW hS hT a hΔ hAB
    (lrSCoreCov_symm C hL hNU hW hS hT a hΔ hA'B)
  exact ⟨hAA', lrSCoreCov_trans C hL hNU hW hS hT a hΔ hAA'
    (lrSCoreCov_symm C hL hNU hW hS hT a hΔ hAA')⟩

/-- Lambda congruence needs the raw left annotation to cover every finite
demand from a right annotation observation. Its relation calls are exactly
the domain and body conversion children. -/
theorem fundCov_lamConv_step_of_inputs (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    (hCS : CovTypingIncludesS C)
    {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hb : ConvT E n (.assumption A :: Γ) b b' B)
    (hML : CovLamModelFor M A b) (hMR : CovLamModelFor M A' b')
    (hDemand : CovDomainDemandTransportFor C M A A') :
    FundConvCovStep C M R n (ConvT.lam Γ A A' b b' B u hA hb) := by
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  have hltA : sizeOf hA < sizeOf (ConvT.lam Γ A A' b b' B u hA hb) := by simp; omega
  have hltb : sizeOf hb < sizeOf (ConvT.lam Γ A A' b b' B u hA hb) := by simp; omega
  have hAty := (convEnds hW hΓ hA).1
  have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hAty
  obtain ⟨⟨hAσ⟩, _, ⟨hAc⟩⟩ := hSub.nativeInstances hW hcl hst hι hΓ hΔ hAty
  have finish : ∀ θ, θ = ρ ∨ θ = ρ' → ∀ f,
      (∀ s ∈ f, ∃ a, M.Ap θ A a ∧ (∀ v ∈ s.1, C.ty v a) ∧
        (M.Ap (EnvT.cons (demandT s.1) θ) b s.2 ∨
         M.Ap (EnvT.cons (demandT s.1) θ) b' s.2)) →
      LRSCoreCov C R n Δ (substT σ (.lam A b)) (substT σ' (.lam A' b'))
        (substT σ (.pi A B)) (.lam f) := by
    intro θ hθ f hrows
    have hp := relSubstAtCov_envs hSub θ θ hθ hθ
    rw [LRSCoreCov.eq_def]
    refine ⟨substT σ A, substT σ.up B, .refl _,
      ⟨.assumption Δ _ u hΔ hAσ⟩, ?_⟩
    intro s hs N N' hN hN' hNN' hdem
    obtain ⟨a, hAa, hd, hbodyObs⟩ := hrows s hs
    obtain ⟨hAA', hAA⟩ := covTypePair_from_common_right hL hNU hW hS hT hΔ
      (ih.2 hA hltA hΓ hΔ hp a (Or.inl hAa))
      (ih.2 hA hltA hΓ hΔ hp.diagR a (Or.inl hAa))
    obtain ⟨hNN'⟩ := hNN'
    have hext := relSubstAtCov_cons_realized hL hNU hW hS hT hML.toCovLiftModelLaws
      hΔ hp hAa hd hAA' hAA hAc hN hN' hNN' hdem
    have hbody := ih.2 hb hltb hΓA hΔ hext s.2 hbodyObs
    rw [← instantiate0_substT_up, ← instantiate0_substT_up,
      ← instantiate0_substT_up] at hbody
    exact lrSCoreCov_expand_red_both C hL
      (redR_single (hL.beta Δ (substT σ A) (substT σ.up b) N))
      (redR_single (hL.beta Δ (substT σ' A') (substT σ'.up b') N')) s.2 hbody
  rcases hc with hc | hc
  · rcases hML.inv hc with rfl | ⟨a, f, rfl, hAa, _, hrows⟩
    · exact lrSCoreCov_bot C _ _ _ _
    · apply finish ρ (Or.inl rfl) f
      intro s hs
      exact ⟨a, hAa, fun v hv => hCS a v ((hrows s hs).1 v hv),
        Or.inl (hrows s hs).2⟩
  · rcases hMR.inv hc with rfl | ⟨a, f, rfl, hAa, _, hrows⟩
    · exact lrSCoreCov_bot C _ _ _ _
    · apply finish ρ' (Or.inr rfl) f
      intro s hs
      obtain ⟨a0, hA0, hd⟩ := hDemand ρ' a s.1 hAa (hrows s hs).1
      exact ⟨a0, hA0, hd, Or.inr (hrows s hs).2⟩

/-- Pi congruence retains both native domain/codomain conversions. The
actual compact domain relation comes from the real domain child; finite
extension is separately guarded at an observed raw left annotation. -/
theorem fundCov_piConv_step_of_inputs (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) (hW : EnvWfT E) (hcl : EnvClosed E)
    (hst : EnvMembersSubstTStable E) (hι : IotaSubstT E)
    (hS : ConvArgsSymmS E n) (hT : ConvArgsTransS E n)
    (hCS : CovTypingIncludesS C)
    {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v))
    (hML : CovPiModelFor M A B) (hMR : CovPiModelFor M A' B')
    (hDemand : CovDomainDemandTransportFor C M A A') :
    FundConvCovStep C M R n (ConvT.pi Γ A A' B B' u v hA hB) := by
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  have hltA : sizeOf hA < sizeOf (ConvT.pi Γ A A' B B' u v hA hB) := by simp; omega
  have hltB : sizeOf hB < sizeOf (ConvT.pi Γ A A' B B' u v hA hB) := by simp; omega
  have hAty := (convEnds hW hΓ hA).1
  have hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hAty
  obtain ⟨⟨hAσ⟩, _, ⟨hAc⟩⟩ := hSub.nativeInstances hW hcl hst hι hΓ hΔ hAty
  have hΔA : CtxWfT E n (.assumption (substT σ A) :: Δ) :=
    .assumption Δ _ u hΔ hAσ
  obtain ⟨hAmix⟩ := relSubstAtCov_nativeConvInstances hW hcl hst hι hΓ hΔ hSub hA
  obtain ⟨hBσ⟩ := convT_substT hW hcl hst hι hΓA hB hΔA
    (typedSubstT_up hcl hSub.typedL A)
  obtain ⟨hB'σ⟩ := convT_substT_pointwise hW hcl hst hι hΓA
    (convEnds hW hΓA hB).2.1 hΔA
    (typedSubstT_up hcl hSub.typedL A)
    (typedSubstT_up_conv hcl hSub.typedR A u hAc)
    (convSubstT_up_decl hcl hSub.conv _ _ A rfl (.bvar _ 0 _ rfl))
  have hBmix : ConvT E n (.assumption (substT σ A) :: Δ)
      (substT σ.up B) (substT σ'.up B') (.sort v) :=
    .trans _ _ _ _ _ hBσ hB'σ
  have finish : ∀ θ, θ = ρ ∨ θ = ρ' → ∀ a f,
      LRSCoreCov C R n Δ (substT σ A) (substT σ' A') (.sort u) a →
      (∀ s ∈ f, ∃ a0, M.Ap θ A a0 ∧ (∀ z ∈ s.1, C.ty z a0) ∧
        (M.Ap (EnvT.cons (demandT s.1) θ) B s.2 ∨
         M.Ap (EnvT.cons (demandT s.1) θ) B' s.2)) →
      LRSCoreCov C R n Δ (substT σ (.pi A B)) (substT σ' (.pi A' B'))
        (.sort (.imax u v)) (.pi a f) := by
    intro θ hθ a f hDom hrows
    have hp := relSubstAtCov_envs hSub θ θ hθ hθ
    rw [LRSCoreCov.eq_def]
    refine ⟨⟨.imax u v, .refl _⟩,
      substT σ A, substT σ.up B, substT σ' A', substT σ'.up B',
      .refl _, .refl _, ⟨hΔA⟩, ⟨.of _ _ _ u hAmix⟩,
      ⟨.of _ _ _ v hBmix⟩, ⟨u, hDom⟩, ?_⟩
    intro s hs _ N N' hN hN' hNN' hdem
    obtain ⟨a0, hAa, hd, hbodyObs⟩ := hrows s hs
    obtain ⟨hAA', hAA⟩ := covTypePair_from_common_right hL hNU hW hS hT hΔ
      (ih.2 hA hltA hΓ hΔ hp a0 (Or.inl hAa))
      (ih.2 hA hltA hΓ hΔ hp.diagR a0 (Or.inl hAa))
    obtain ⟨hNN'⟩ := hNN'
    have hext := relSubstAtCov_cons_realized hL hNU hW hS hT hML.toCovLiftModelLaws
      hΔ hp hAa hd hAA' hAA hAc hN hN' hNN' hdem
    have hbody := ih.2 hB hltB hΓA hΔ hext s.2 hbodyObs
    rw [← instantiate0_substT_up, ← instantiate0_substT_up] at hbody
    exact ⟨v, hbody⟩
  rcases hc with hc | hc
  · rcases hML.inv hc with rfl | ⟨a, f, rfl, hAa, hrows⟩
    · exact lrSCoreCov_bot C _ _ _ _
    · apply finish ρ (Or.inl rfl) a f (ih.2 hA hltA hΓ hΔ hSub a (Or.inl hAa))
      intro s hs
      exact ⟨a, hAa, fun z hz => hCS a z ((hrows s hs).1 z hz),
        Or.inl (hrows s hs).2⟩
  · rcases hMR.inv hc with rfl | ⟨a, f, rfl, hAa, hrows⟩
    · exact lrSCoreCov_bot C _ _ _ _
    · apply finish ρ' (Or.inr rfl) a f (ih.2 hA hltA hΓ hΔ hSub a (Or.inr hAa))
      intro s hs
      obtain ⟨a0, hA0, hd⟩ := hDemand ρ' a s.1 hAa (hrows s hs).1
      exact ⟨a0, hA0, hd, Or.inr (hrows s hs).2⟩

/-- Congruent lets need a coherent extension for the two actual value
denotations. The target source context remains the constructor's original
`.letBinding A value`; native value conversion alone does not assert this. -/
structure CovLetConvInput (C : CovTyping E) (M : CtxModelT E) (R : Readback)
    (n : Nat) (Γ : LCtx) (A A' value value' body body' : Expr Nat) : Prop where
  bodyL : ∀ {ρ : EnvT} {c : CptT}, M.Ap ρ (.letE A value body) c →
    M.Ap (EnvT.cons (fun u => M.Ap ρ value u) ρ) body c
  bodyR : ∀ {ρ : EnvT} {c : CptT}, M.Ap ρ (.letE A' value' body') c →
    M.Ap (EnvT.cons (fun u => M.Ap ρ value' u) ρ) body' c
  subst : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
    RelSubstAtCov C M R n Δ
      (EnvT.cons (fun u => M.Ap ρ value u) ρ)
      (EnvT.cons (fun u => M.Ap ρ' value' u) ρ')
      (SubstT.cons (substT σ value) σ) (SubstT.cons (substT σ' value') σ')
      (.letBinding A value :: Γ)

/-- The genuine body conversion is the only recursive call in this let
congruence supplier. Domain/value conversions provide native wellformedness. -/
theorem fundCov_letEConv_step_of_input (hW : EnvWfT E)
    (hL : ReadbackLaws E (WhStepCK2 E n))
    {Γ : LCtx} {A A' value value' body body' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ value value' A)
    (hb : ConvT E n (.letBinding A value :: Γ) body body' B)
    (hInput : CovLetConvInput C M (WhStepCK2 E n) n Γ A A' value value' body body') :
    FundConvCovStep C M (WhStepCK2 E n) n
      (ConvT.letE Γ A A' value value' body body' B u hA hv hb) := by
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  have hlt : sizeOf hb <
      sizeOf (ConvT.letE Γ A A' value value' body body' B u hA hv hb) := by simp; omega
  have hΓV : CtxWfT E n (.letBinding A value :: Γ) :=
    .letBinding Γ A u value hΓ (convEnds hW hΓ hA).1 (convEnds hW hΓ hv).1
  have hbody := ih.2 hb hlt hΓV hΔ (hInput.subst hΔ hSub) c
    (hc.elim (fun h => Or.inl (hInput.bodyL h)) (fun h => Or.inr (hInput.bodyR h)))
  have hout := lrSCoreCov_expand_red_both C hL
    (cov_let_subst_read E n Δ σ A value body)
    (cov_let_subst_read E n Δ σ' A' value' body') c hbody
  simpa only [substT_instantiate0, instantiate0_substT_up] using hout

/-- Equal-value let inputs reuse the complete coherent package already
proved for a genuine let. This supplies the new port, not merely its conclusion. -/
theorem covLetConvInput_of_same_value {Γ : LCtx} {A value body body' : Expr Nat}
    (hL : CovLetInput C M R n Γ A value body)
    (hR : CovLetInput C M R n Γ A value body') :
    CovLetConvInput C M R n Γ A A value value body body' :=
  ⟨hL.body, hR.body, hL.subst⟩

/-- A non-bottom coherent let-congruence fixture, with the full port and
an actual native congruence derivation in the admitted Nat environment. -/
theorem letConv_semantic_port_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧
    CovLetConvInput (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) n []
      (.sort (.succ .zero)) (.sort (.succ .zero)) (.sort .zero) (.sort .zero)
      (.bvar 0) (.bvar 0) ∧
    Nonempty (ConvT natEnvU n []
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0))
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0)) (.sort (.succ .zero))) ∧
    ApproxTK natEnvU n [] EnvT.bot
      (.letE (.sort (.succ .zero)) (.sort .zero) (.bvar 0)) .prop ∧ CptT.prop ≠ .bot := by
  obtain ⟨hInput, _, _, hobs, _, hne⟩ := covLet_native_control (C2 natEnvU)
    (C2_includesS natEnvU) natEnvUWfT not_indexedPropRecT_natEnvU n
  refine ⟨⟨natEnvUWfT⟩, covLetConvInput_of_same_value hInput hInput, ⟨?native⟩, hobs, hne⟩
  case native =>
    exact .letE [] _ _ _ _ _ _ (.sort (.succ .zero)) (.succ (.succ .zero))
      (.refl [] _ _ (.sort [] _)) (.refl [] _ _ (.sort [] .zero))
      (.refl _ _ _ (.bvar _ 0 _ rfl))

/-- Delta contraction is exercised by the already admitted transparent
definition `const 0 : Sort 1 := Sort 0`, including both non-bottom observations. -/
theorem delta_sort_contract_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT defSortEnv) ∧
    CovModelContractAt (ctxModelT_approxTK defSortEnv n []) (.const 0 []) (.sort .zero) ∧
    Nonempty (ConvT defSortEnv n [] (.const 0 []) (.sort .zero) (.sort (.succ .zero))) ∧
    ApproxTK defSortEnv n [] ρ (.const 0 []) .prop ∧
    ApproxTK defSortEnv n [] ρ (.sort .zero) .prop ∧ CptT.prop ≠ .bot := by
  have hd : DeltaConst defSortEnv 0
      ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ (.sort .zero) :=
    ⟨rfl, rfl, by decide, by decide⟩
  have hobs : ∀ θ, ApproxTK defSortEnv n [] θ (.sort .zero) .prop := by
    intro θ
    simpa only [sortCode_zero] using approxTK_sort_code defSortEnv n [] θ .zero
  refine ⟨⟨defSortEnvWfT⟩,
    covModelContractAt_delta_approxTK defSortEnvWfT hd.1 hd.2.1 (kFreeT_sort defSortEnv .zero),
    ⟨?native⟩, .delta hd (hobs EnvT.bot), hobs ρ, fun h => CptT.noConfusion h⟩
  case native =>
    exact .delta [] 0 [] _ _ hd.1 hd.2.1 rfl rfl rfl (.sort [] .zero)

/-- The collapse port is inhabited by a natively typed proof in the actual
model. Its type has a non-bottom Pi observation; the proof's observation
is bottom, exactly as required by proposition collapse. -/
theorem proof_collapse_semantic_port_control (E : ResolvedEnv) (hW : EnvWfT E) (n : Nat) :
    Nonempty (EnvWfT E) ∧
    CovProofCollapseFor (ctxModelT_approxTK E n []) polyIdProof polyIdProof ∧
    Nonempty (HasTyT E n [] polyIdProof polyIdProp) ∧
    EnvTypedCovAtP (C2 E) (ctxModelT_approxTK E n []) [] EnvT.bot ∧
    ApproxTK E n [] EnvT.bot polyIdProof .bot ∧
    ApproxTK E n [] EnvT.bot polyIdProp (.pi .bot []) ∧
    (.pi .bot [] : CptT) ≠ .bot := by
  exact ⟨⟨hW⟩, covProofCollapseFor_polyIdProof E n [], ⟨hasTyT_polyIdProof E n⟩,
    envTypedCovAtP_nil (C2 E) _ EnvT.bot, ApproxTK.bot _ _ _,
    approxTK_pi_bot_nil E n [] EnvT.bot _ _, fun h => CptT.noConfusion h⟩

/-- A saturated observation is handled at genuine one-step reducts of
both endpoints. The residual relation is at those reducts, not at the
original conversion conclusion; reflexive readbacks are not admitted. -/
def CovSaturatedReductAt (C : CovTyping E) (R : Readback) (n : Nat)
    (Δ : LCtx) (x y T : Expr Nat) (c : CptT) : Prop :=
  ∃ x' y', R Δ x x' ∧ R Δ y y' ∧ LRSCoreCov C R n Δ x' y' T c

/-- The conversion-app remainder has the same native telescope port as
typing application, together with the explicit saturated reduct relation.
The actual endpoint observations and complete related package are retained. -/
structure CovAppConvInputs (C : CovTyping E) (R : Readback) (n : Nat)
    (Ξ Γ : LCtx) (f g a b A B : Expr Nat) : Prop where
  spine : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ →
    ∀ (r : Nat) (args : List CptT) (u : CptT)
      (m : CheckedMember) (ls ls' : List Level) (xs xs' : List (Expr Nat)),
      E.members r = some m →
      RedR R Δ (substT σ f) (foldApps (.const r ls) xs) →
      RedR R Δ (substT σ' g) (foldApps (.const r ls') xs') →
      NormalR R Δ (foldApps (.const r ls) xs) →
      NormalR R Δ (foldApps (.const r ls') xs') → eqNList ls ls' →
      args.length ≤ xs.length → args.length ≤ xs'.length →
      ConvArgsT E n Δ (instantiateLevels ls m.mtype) xs xs' →
      CovSpineAppNativeAt E R n Δ r m ls ls' xs xs'
        (substT σ A) (substT σ (instantiate0 a B)) (substT σ a) (substT σ' b)
  saturated : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ →
    ∀ c, SaturatedComputationTK E n Ξ ρ (.app f a) c ∨
      SaturatedComputationTK E n Ξ ρ' (.app g b) c →
      CovSaturatedReductAt C R n Δ (substT σ (.app f a)) (substT σ' (.app g b))
        (substT σ (instantiate0 a B)) c

/-- Application congruence consumes exactly its function and argument
conversion children. The lambda arm is supplied by the landed recursive
action; native spine extension and saturated reducts remain explicit. -/
theorem fundCov_appConv_step_of_inputs (hL : ReadbackLaws E R)
    (hW : EnvWfT E) (hcl : EnvClosed E) (hst : EnvMembersSubstTStable E)
    (hι : IotaSubstT E) {Ξ Γ : LCtx} {f g a b A B : Expr Nat}
    (hf : ConvT E n Γ f g (.pi A B)) (ha : ConvT E n Γ a b A)
    (hInput : CovAppConvInputs C R n Ξ Γ f g a b A B) :
    FundConvCovStep C (ctxModelT_approxTK E n Ξ) R n (ConvT.app Γ f g a b A B hf ha) := by
  intro hΓ ih Δ ρ ρ' σ σ' hΔ hSub c hc
  have hltf : sizeOf hf < sizeOf (ConvT.app Γ f g a b A B hf ha) := by simp; omega
  have hlta : sizeOf ha < sizeOf (ConvT.app Γ f g a b A B hf ha) := by simp; omega
  obtain ⟨hab⟩ := relSubstAtCov_nativeConvInstances hW hcl hst hι hΓ hΔ hSub ha
  have hends := convEnds hW hΔ hab
  have hlam : ∀ g0 s, s ∈ g0 →
      ((ApproxTK E n Ξ ρ f (.lam g0) ∧ ∀ u ∈ s.1, ApproxTK E n Ξ ρ a u) ∨
       (ApproxTK E n Ξ ρ' g (.lam g0) ∧ ∀ u ∈ s.1, ApproxTK E n Ξ ρ' b u)) →
      LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app g b))
        (substT σ (instantiate0 a B)) s.2 := by
    intro g0 s hs ho
    have hfun := ih.2 hf hltf hΓ hΔ hSub (.lam g0)
      (ho.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
    have hdem : ∀ u ∈ s.1,
        LRSCoreCov C R n Δ (substT σ a) (substT σ' b) (substT σ A) u := by
      intro u hu
      exact ih.2 ha hlta hΓ hΔ hSub u
        (ho.elim (fun h => Or.inl (h.2 u hu)) (fun h => Or.inr (h.2 u hu)))
    simpa only [substT, substT_instantiate0] using
      lrSCoreCov_app C hL hfun hs hends.1 hends.2.1 ⟨hab⟩ hdem
  have hspine : ∀ r args u,
      ((ApproxTK E n Ξ ρ f (.spine r args) ∧ ApproxTK E n Ξ ρ a u) ∨
       (ApproxTK E n Ξ ρ' g (.spine r args) ∧ ApproxTK E n Ξ ρ' b u)) →
      LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app g b))
        (substT σ (instantiate0 a B)) (.spine r (args ++ [u])) := by
    intro r args u ho
    have hfun := ih.2 hf hltf hΓ hΔ hSub (.spine r args)
      (ho.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
    rw [lrSCoreCov_spine_iff] at hfun
    obtain ⟨m, ls, ls', xs, xs', hm, hr, hr', hn, hn', hls, hl, hl', hargs, _⟩ := hfun
    exact lrSCoreCov_spine_snoc_of_native C hL hm hr hr' hls hl hl' hargs hab
      (hInput.spine hΔ hSub r args u m ls ls' xs xs' hm hr hr' hn hn' hls hl hl' hargs)
  have hsat : ∀ c, SaturatedComputationTK E n Ξ ρ (.app f a) c ∨
      SaturatedComputationTK E n Ξ ρ' (.app g b) c →
      LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app g b))
        (substT σ (instantiate0 a B)) c := by
    intro c hs
    obtain ⟨x', y', hx, hy, hxy⟩ := hInput.saturated hΔ hSub c hs
    exact lrSCoreCov_expand_red_both C hL (redR_single hx) (redR_single hy) c hxy
  rcases hc with hc | hc
  · rcases approxTK_app_inv hc with rfl | ⟨g0, s, rfl, hh, hs, hd⟩ |
        ⟨r, args, u, rfl, hh, ha⟩ | hs
    · exact lrSCoreCov_bot C _ _ _ _
    · exact hlam g0 s hs (Or.inl ⟨hh, hd⟩)
    · exact hspine r args u (Or.inl ⟨hh, ha⟩)
    · exact hsat c (Or.inl hs)
  · rcases approxTK_app_inv hc with rfl | ⟨g0, s, rfl, hh, hs, hd⟩ |
        ⟨r, args, u, rfl, hh, ha⟩ | hs
    · exact lrSCoreCov_bot C _ _ _ _
    · exact hlam g0 s hs (Or.inr ⟨hh, hd⟩)
    · exact hspine r args u (Or.inr ⟨hh, ha⟩)
    · exact hsat c (Or.inr hs)

/-- Constant level congruence is fully supplied on the rigid non-family
fragment from actual observation and normality inputs at both level lists. -/
theorem fundCov_consts_step_of_spineInputs {Γ : LCtx} {r : Nat}
    {ls ls' : List Level} {m : CheckedMember} (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls')
    (hL : CovConstSpineInput M R r ls m) (hR : CovConstSpineInput M R r ls' m) :
    FundConvCovStep C M R n (ConvT.consts Γ r ls ls' m hres hlen hwf hwf' h) := by
  intro _ _ Δ ρ ρ' σ σ' _ _ c hc
  rcases hc.elim hL.observation hR.observation with rfl | rfl
  · exact lrSCoreCov_bot C _ _ _ _
  · rw [lrSCoreCov_spine_iff]
    refine ⟨m, ls, ls', [], [], hres, .refl _, .refl _,
      hL.normal Δ, hR.normal Δ, h, by decide, by decide, .nil _, ?_⟩
    intro _ hFamily
    exact (hL.nonFamily hFamily).elim

/-- A transparent consts row reduces to the explicit member-body pair.
That pair is an external declaration-semantics premise, because `consts`
has no body subderivation. Both model contracts are genuinely supplied. -/
theorem fundCov_consts_step_of_body_pair (hW : EnvWfT E)
    (hst : EnvMembersSubstTStable E) {Ξ Γ : LCtx} {r : Nat}
    {ls ls' : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hb : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls')
    (hfree : KFreeT E (instantiateLevels ls b))
    (hfree' : KFreeT E (instantiateLevels ls' b))
    (hBody : FundConvAtCov C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n Γ
      (instantiateLevels ls b) (instantiateLevels ls' b) (instantiateLevels ls m.mtype)) :
    FundConvCovStep C (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n
      (ConvT.consts Γ r ls ls' m hres hlen hwf hwf' h) := by
  intro _ _ Δ ρ ρ' σ σ' hΔ hSub c hc
  have hbody := hBody hΔ hSub c
    (hc.elim (fun ho => Or.inl (covModelContractAt_delta_approxTK hW hres hb hfree ρ c ho))
      (fun ho => Or.inr (covModelContractAt_delta_approxTK hW hres hb hfree' ρ' c ho)))
  have hread : ∀ τ : SubstT, ∀ us : List Level,
      RedR (WhStepCK2 E n) Δ (substT τ (.const r us))
        (substT τ (instantiateLevels us b)) := by
    intro τ us
    rw [substT, (hst r m hres).2 b hb us τ]
    exact redR_single (.ctx (.delta hres hb))
  exact lrSCoreCov_expand_red_both C (readbackLaws_whStepCK2 E n)
    (hread σ ls) (hread σ' ls') c hbody

/-- The rigid consts port and its native constructor are both inhabited
at zero, with the actual non-bottom model observation. -/
theorem consts_spine_semantic_port_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧
    CovConstSpineInput (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n)
      1 [] natZeroMember ∧
    Nonempty (ConvT natEnvU n [] (.const 1 []) (.const 1 []) (.const 0 [])) ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 1 []) (.spine 1 []) ∧
    (.spine 1 [] : CptT) ≠ .bot := by
  obtain ⟨hW, _, hInput, _, _, hobs, _, hne⟩ := covConst_native_control (C2 natEnvU) n
  exact ⟨hW, hInput, ⟨.consts [] 1 [] [] natZeroMember rfl rfl rfl rfl (eqNList_refl [])⟩,
    hobs, hne⟩

/-- The external body-pair motive needed by transparent consts is
inhabited for the actual admitted sort definition, at all substitutions. -/
theorem consts_sort_body_semantic_control (C : CovTyping defSortEnv) (n : Nat) :
    Nonempty (EnvWfT defSortEnv) ∧
    FundConvAtCov C (ctxModelT_approxTK defSortEnv n []) (WhStepCK2 defSortEnv n) n []
      (.sort .zero) (.sort .zero) (.sort (.succ .zero)) ∧
    ApproxTK defSortEnv n [] EnvT.bot (.const 0 []) .prop ∧ CptT.prop ≠ .bot := by
  obtain ⟨hW, _, _, hc, _, hne⟩ := delta_sort_contract_control n EnvT.bot
  refine ⟨hW, ?_, hc, hne⟩
  intro Δ ρ ρ' σ σ' hΔ hSub c hc
  exact fundCov_sort (covAtomicModelLaws_approxTK defSortEnv n []) .zero hΔ hSub c hc

/-- The one-step saturated reduct port is genuinely inhabited at the
typed Nat.rec call, with an actual non-bottom saturated observation. -/
theorem saturated_reduct_semantic_port_control (ρ : EnvT) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU 1 []) ∧
    Nonempty (ConvT natEnvU 1 [] (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) (.const 0 [])) ∧
    SaturatedComputationTK natEnvU 1 [] ρ (iotaLhsOf wSuccU1) (.spine 1 []) ∧
    CovSaturatedReductAt (C2 natEnvU) (WhStepCK2 natEnvU 1) 1 []
      (iotaLhsOf wSuccU1) (iotaLhsOf wSuccU1) (.const 0 []) (.spine 1 []) ∧
    ApproxTK natEnvU 1 [] ρ (iotaRhsOf wSuccU1) (.spine 1 []) ∧
    (.spine 1 [] : CptT) ≠ .bot := by
  exact ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, convT_natRec_good_iota,
    saturatedComputationTK_natRec_good_call ρ,
    ⟨iotaRhsOf wSuccU1, iotaRhsOf wSuccU1, .ctx (.iota (.ofU wSuccU1)),
      .ctx (.iota (.ofU wSuccU1)), lrSCoreCov_natRec_good_rhs (C2 natEnvU)⟩,
    approxTK_natRec_good_rhs ρ, fun h => CptT.noConfusion h⟩

/-!
## Exact fifteen-row inventory

The entries below refer to kernel propositions above, not additional axioms.
An adapter is a conditional proof of the unchanged native constructor step.
Its semantic port is not asserted for all native derivations.

| Native field | Strict native children consumed | Exact remaining port | Concrete control |
| --- | --- | --- | --- |
| symm | original conversion | CovConvObservedTypeFor, CovTypeDiagonalsFor | covSort_semantic_ports_control |
| trans | both conversions | preceding type ports, CovMiddleObservationFor | covSort_semantic_ports_control |
| beta | annotation, body, argument typings | CovBetaFactorFor, CovLiftModelLaws | beta_zeta_semantic_ports_control |
| zeta | original let-body typing | CovLetInput, CovInstObservation | covLet_native_control and beta_zeta_semantic_ports_control |
| delta | stored body typing | CovModelContractAt; supplied at K-free body | delta_sort_contract_control |
| iota | stored RHS typing | CovModelContractAt; global ordinary model-iota law remains explicit | ordinary_iota_eq_sort_contract_control supplies the full port at a native non-bottom Eq iota |
| litConv | stored expansion typing | CovModelContractAt; supplied at K-free expansion | literal_zero_contract_control |
| appConv | function and argument conversions | CovSpineAppNativeAt and CovSaturatedReductAt under CovAppConvInputs | covSpineAppNativeAt_natSucc_zero and saturated_reduct_semantic_port_control |
| lamConv | annotation and body conversions | CovLamModelFor and CovDomainDemandTransportFor | supplied equal-annotation transport and covBinder_native_control |
| piConv | annotation and codomain conversions | CovPiModelFor and CovDomainDemandTransportFor | supplied equal-annotation transport and covBinder_native_control |
| letEConv | original let-body conversion | CovLetConvInput | letConv_semantic_port_control |
| consts | no native children | CovConstSpineInput; or explicit instantiated member-body pair motive | consts_spine_semantic_port_control and consts_sort_body_semantic_control |
| eta | no supplier exists for the full package | refuted exact native motive below | natSucc_eta_C2_counterexample |
| irr | no recursive call | CovProofCollapseFor | proof_collapse_semantic_port_control |
| tyConv | original term and type conversions | CovConvObservedTypeFor | covSort_semantic_ports_control |

The constructor-constant supply is a fragment. General recursor declaration
semantics is not proved by the spine or transparent-body adapters. The native
spine and saturated controls inhabit their pointwise ports; they do not imply
the universally quantified CovAppConvInputs at all terms. No generated native
derivation is used as a smaller-child fundamental hypothesis.
-/

/-- Weak-head-normal lambdas cannot inhabit the unchanged rigid-spine leaf.
No compact typing or model assumption is used in this shape obstruction. -/
theorem not_lrSCoreCov_lam_spineCK2 (C : CovTyping E) (n : Nat) (Γ : LCtx)
    (D body y A : Expr Nat) (r : Nat) (args : List CptT) :
    ¬ LRSCoreCov C (WhStepCK2 E n) n Γ (.lam D body) y A (.spine r args) := by
  rw [lrSCoreCov_spine_iff]
  rintro ⟨m, ls, ls', xs, xs', _, hread, _⟩
  exact F8EtaK.foldApps_const_ne_lam_any
    (redR_of_normal (normalR_lamCK2 Γ D body) hread)

/-- The actual successor eta conversion retains native endpoint typings,
the coherent model environment and the non-bottom right-endpoint observation.
Its type is realized under the repaired typing, while the core relation fails. -/
theorem natSucc_eta_C2_counterexample (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    Nonempty (ConvT natEnvU n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    EnvTypedCovAtP (C2 natEnvU) (ctxModelT_approxTK natEnvU n []) [] EnvT.bot ∧
    ApproxTK natEnvU n [] EnvT.bot (.const 2 []) (.spine 2 []) ∧
    NormalizedCovRealization (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) [] EnvT.bot (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) ∧
    (.spine 2 [] : CptT) ≠ .bot ∧
    ¬ LRSCoreCov (C2 natEnvU) (WhStepCK2 natEnvU n) n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) := by
  exact ⟨⟨natEnvUWfT⟩, ⟨.nil⟩,
    ⟨(convEnds natEnvUWfT (CtxWfT.nil) (convT_eta_natSucc n [])).1⟩,
    ⟨hasTyT_natEnvU_succ n []⟩, ⟨convT_eta_natSucc n []⟩,
    envTypedCovAtP_nil (C2 natEnvU) _ EnvT.bot,
    ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine EnvT.bot),
    normalizedCovRealization_C2_natSucc n [] EnvT.bot,
    (fun h => CptT.noConfusion h),
    not_lrSCoreCov_lam_spineCK2 (C2 natEnvU) n [] _ _ _ _ 2 []⟩

/-- The exact landed conversion motive is false at the admitted successor
eta conversion, for every compact typing satisfying the landed interface. -/
theorem not_fundConvAtCov_eta_natSucc (C : CovTyping natEnvU) (n : Nat) :
    ¬ FundConvAtCov C (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n) n []
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 [])) := by
  intro h
  have hTyped : TypedSubstT natEnvU n [] SubstT.id [] :=
    ⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩
  have hSub : RelSubstAtCov C (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) n [] EnvT.bot EnvT.bot SubstT.id SubstT.id [] :=
    relSubstAtCov_bot_diagonal_of_no_values C hTyped
      (fun A => ApproxTK.bot _ _ _) (fun _ => rfl)
  have hRel := h (CtxWfT.nil) hSub (.spine 2 [])
    (Or.inr (ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine EnvT.bot)))
  apply not_lrSCoreCov_lam_spineCK2 C n [] _ _ _ _ 2 []
  simpa only [substT_id] using hRel

/-- Full conversion fundamentality would include the concrete native eta
derivation, so it is refuted without assuming any generated child motive. -/
theorem not_fundamentalCovAt_natSucc_eta (C : CovTyping natEnvU) (n : Nat) :
    ¬ FundamentalCovAt C (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n) n := by
  intro h
  exact not_fundConvAtCov_eta_natSucc C n (h.2 (CtxWfT.nil) (convT_eta_natSucc n []))

/-- The unchanged strong-induction assembler turns a full case package into
the refuted fundamental theorem. Hence the complete package is unavailable. -/
theorem not_fundCovCases_natSucc_eta (C : CovTyping natEnvU) (n : Nat) :
    ¬ FundCovCases C (ctxModelT_approxTK natEnvU n []) (WhStepCK2 natEnvU n) n := by
  intro h
  exact not_fundamentalCovAt_natSucc_eta C n (fundamentalCovAt_approxTK_of_cases h)

/-- Exact repaired-typing specialization: inclusion of the model's
introduction judgment coexists with the refuted full native case package. -/
theorem C2_conversion_fundamental_refuted (n : Nat) :
    CovTypingIncludesS (C2 natEnvU) ∧
    (¬ FundamentalCovAt (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) n) ∧
    (¬ FundCovCases (C2 natEnvU) (ctxModelT_approxTK natEnvU n [])
      (WhStepCK2 natEnvU n) n) :=
  ⟨C2_includesS natEnvU, not_fundamentalCovAt_natSucc_eta (C2 natEnvU) n,
    not_fundCovCases_natSucc_eta (C2 natEnvU) n⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_CONV_CASES_ROOTS
#print axioms CovModelContractAt
#print axioms CovConvObservedTypeFor
#print axioms CovTypeDiagonalsFor
#print axioms CovMiddleObservationFor
#print axioms CovBetaFactorFor
#print axioms CovDomainDemandTransportFor
#print axioms CovInstObservation
#print axioms CovProofCollapseFor
#print axioms relSubstAtCov_symm_native
#print axioms fundCov_symm_step_of_inputs
#print axioms fundCov_trans_step_of_inputs
#print axioms fundCov_tyConv_step_of_observedType
#print axioms fundCov_irr_step_of_collapse
#print axioms fundCov_beta_step_of_factor
#print axioms fundCov_zeta_step_of_inputs
#print axioms covInstObservation_approxT
#print axioms covInstObservation_approxTK_of_no_indexed
#print axioms covInstObservation_bvar0_approxTK
#print axioms covBetaFactorFor_sortIdentity
#print axioms beta_zeta_semantic_ports_control
#print axioms covConvObservedTypeFor_sort
#print axioms covTypeDiagonalsFor_sort
#print axioms covMiddleObservationFor_refl
#print axioms covDomainDemandTransportFor_refl
#print axioms covProofCollapseFor_polyIdProof
#print axioms covSort_semantic_ports_control
#print axioms covModelContractAt_delta_approxTK
#print axioms covModelContractAt_lit_approxTK
#print axioms covModelContractAt_iota_approxTK_of_modelIota
#print axioms fundCov_delta_step_of_contract
#print axioms fundCov_delta_step_approxTK_of_kFree
#print axioms fundCov_iota_step_of_contract
#print axioms fundCov_litConv_step_of_contract
#print axioms fundCov_litConv_step_approxTK_of_kFree
#print axioms literal_zero_contract_control
#print axioms covModelContractAt_eqRec_sort
#print axioms ordinary_iota_eq_sort_contract_control
#print axioms relSubstAtCov_nativeConvInstances
#print axioms covTypePair_from_common_right
#print axioms fundCov_lamConv_step_of_inputs
#print axioms fundCov_piConv_step_of_inputs
#print axioms CovLetConvInput
#print axioms fundCov_letEConv_step_of_input
#print axioms covLetConvInput_of_same_value
#print axioms letConv_semantic_port_control
#print axioms delta_sort_contract_control
#print axioms proof_collapse_semantic_port_control
#print axioms CovSaturatedReductAt
#print axioms CovAppConvInputs
#print axioms fundCov_appConv_step_of_inputs
#print axioms fundCov_consts_step_of_spineInputs
#print axioms fundCov_consts_step_of_body_pair
#print axioms consts_spine_semantic_port_control
#print axioms consts_sort_body_semantic_control
#print axioms saturated_reduct_semantic_port_control
#print axioms not_lrSCoreCov_lam_spineCK2
#print axioms natSucc_eta_C2_counterexample
#print axioms not_fundConvAtCov_eta_natSucc
#print axioms not_fundamentalCovAt_natSucc_eta
#print axioms not_fundCovCases_natSucc_eta
#print axioms C2_conversion_fundamental_refuted
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_CONV_CASES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormConvCasesAudit
