import rcic.RcicNativeTypedModelCovRelSubstAgreement
import rcic.RcicNativeTypedModelCovRelExpansion
import rcic.RcicNativeTypedModelCovPropagation

/-!
# Fundamental motives and native strong induction for the new relation

The motives retain every target context, both environments and substitutions,
native substitution evidence and both coherent typing guards.  Model transport
and recursive-gate transport are separate.  Old case proofs are reused only
with the explicit observed substitution gates and output gate agreement.

The conditional strong-induction assembler exposes the remaining native
constructor obligations individually; no instance of `FundCovCases` is
supplied here.  Its recursive hypotheses are indexed by strictly smaller
native derivation sizes.  The saturated application branch is an
explicit supplier, and the beta interfaces distinguish a supplied contractum
motive from the imported old adapter.  No escape or global typing law is a
field.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit
open Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit

variable {E : ResolvedEnv} {C : CovTyping E} {M N : CtxModelT E}
  {R : Readback} {n : Nat}

/-- The complete typing motive over the new related-substitution package. -/
def FundTyAtCov (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (e A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ e c ∨ M.Ap ρ' e c →
      LRSCoreCov C R n Δ (substT σ e) (substT σ' e) (substT σ A) c

/-- The complete conversion motive, with an observation at either endpoint. -/
def FundConvAtCov (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (a b A : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ a c ∨ M.Ap ρ' b c →
      LRSCoreCov C R n Δ (substT σ a) (substT σ' b) (substT σ A) c

def FundamentalCovAt (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {e A : Expr Nat},
    HasTyT E n Γ e A → FundTyAtCov C M R n Γ e A) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b A : Expr Nat},
    ConvT E n Γ a b A → FundConvAtCov C M R n Γ a b A)

def TyValidAtCov (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (A : Expr Nat) : Prop :=
  ∃ w, FundTyAtCov C M R n Γ A (.sort w)

def CtxValidAtCov (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) : Prop :=
  ∀ i A, lookupType Γ i = some A → TyValidAtCov C M R n Γ A

theorem FundTyAtCov.modelMap {Γ : LCtx} {e A : Expr Nat}
    (h : FundTyAtCov C M R n Γ e A)
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ)
    (he : ModelAgreementAtT M N e) : FundTyAtCov C N R n Γ e A := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact h hΔ ((relSubstAtCov_congr hB hV hT).mpr hS) c
    ((or_congr (he ρ c) (he ρ' c)).mpr hc)

theorem fundTyAtCov_congr {Γ : LCtx} {e A : Expr Nat}
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ)
    (he : ModelAgreementAtT M N e) :
    FundTyAtCov C M R n Γ e A ↔ FundTyAtCov C N R n Γ e A :=
  ⟨fun h => h.modelMap hB hV hT he,
    fun h => h.modelMap (fun i => modelAgreementAtT_symm (hB i))
      (fun i v hv => modelAgreementAtT_symm (hV i v hv))
      (fun i A hA => modelAgreementAtT_symm (hT i A hA)) (modelAgreementAtT_symm he)⟩

theorem FundConvAtCov.modelMap {Γ : LCtx} {a b A : Expr Nat}
    (h : FundConvAtCov C M R n Γ a b A)
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ)
    (ha : ModelAgreementAtT M N a) (hb : ModelAgreementAtT M N b) :
    FundConvAtCov C N R n Γ a b A := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact h hΔ ((relSubstAtCov_congr hB hV hT).mpr hS) c
    ((or_congr (ha ρ c) (hb ρ' c)).mpr hc)

theorem fundConvAtCov_congr {Γ : LCtx} {a b A : Expr Nat}
    (hB : ∀ i, ModelAgreementAtT M N (.bvar i))
    (hV : ValueAgreementT M N Γ) (hT : TypeAgreementT M N Γ)
    (ha : ModelAgreementAtT M N a) (hb : ModelAgreementAtT M N b) :
    FundConvAtCov C M R n Γ a b A ↔ FundConvAtCov C N R n Γ a b A :=
  ⟨fun h => h.modelMap hB hV hT ha hb,
    fun h => h.modelMap (fun i => modelAgreementAtT_symm (hB i))
      (fun i v hv => modelAgreementAtT_symm (hV i v hv))
      (fun i A hA => modelAgreementAtT_symm (hT i A hA))
      (modelAgreementAtT_symm ha) (modelAgreementAtT_symm hb)⟩

theorem fundTyAtCov_approxTK_iff_of_kFree {Ξ Γ : LCtx} {e A : Expr Nat}
    (hV : KFreeValuesT E Γ) (hT : KFreeTypesT E Γ) (he : KFreeT E e) :
    FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ e A ↔
      FundTyAtCov C (ctxModelT_approxT E) R n Γ e A :=
  fundTyAtCov_congr (fun i => modelAgreementAtT_kFree (kFreeT_bvar E i))
    (valueAgreementT_approxTK_of_kFree hV) (typeAgreementT_approxTK_of_kFree hT)
    (modelAgreementAtT_kFree he)

theorem fundConvAtCov_approxTK_iff_of_kFree {Ξ Γ : LCtx} {a b A : Expr Nat}
    (hV : KFreeValuesT E Γ) (hT : KFreeTypesT E Γ)
    (ha : KFreeT E a) (hb : KFreeT E b) :
    FundConvAtCov C (ctxModelT_approxTK E n Ξ) R n Γ a b A ↔
      FundConvAtCov C (ctxModelT_approxT E) R n Γ a b A :=
  fundConvAtCov_congr (fun i => modelAgreementAtT_kFree (kFreeT_bvar E i))
    (valueAgreementT_approxTK_of_kFree hV) (typeAgreementT_approxTK_of_kFree hT)
    (modelAgreementAtT_kFree ha) (modelAgreementAtT_kFree hb)

/-- Agreement is requested only on the observations read by an actual new
related substitution.  This is an explicit adapter input, not a typing law. -/
def CovSubstGateFor (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ → CovSubstGateAt C M Γ ρ ρ'

/-- Compatibility at a source observation consumed by one fundamental motive. -/
def CovObservationGateFor (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (a b : Expr Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
    ∀ c, M.Ap ρ a c ∨ M.Ap ρ' b c → CovGateAgreement C c

/-- Reuse an old typing proof under the exact substitution and result gates.
No converse or universal old/new equivalence is asserted. -/
theorem fundTyAtCov_of_old {Γ : LCtx} {e A : Expr Nat}
    (hGate : CovSubstGateFor C M R n Γ)
    (hOut : CovObservationGateFor C M R n Γ e e)
    (hOld : FundTyAt M R n Γ e A) : FundTyAtCov C M R n Γ e A := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact (lrSCoreCov_iff_coreS C c (hOut hS c hc) Δ _ _ _).mpr
    (hOld hΔ (hS.toOld (hGate hS)) c hc)

theorem fundConvAtCov_of_old {Γ : LCtx} {a b A : Expr Nat}
    (hGate : CovSubstGateFor C M R n Γ)
    (hOut : CovObservationGateFor C M R n Γ a b)
    (hOld : FundConvAt M R n Γ a b A) : FundConvAtCov C M R n Γ a b A := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact (lrSCoreCov_iff_coreS C c (hOut hS c hc) Δ _ _ _).mpr
    (hOld hΔ (hS.toOld (hGate hS)) c hc)

/-- K-free model transport composes with the separate finite-gate adapter. -/
theorem fundTyAtCov_approxTK_of_old_of_kFree {Ξ Γ : LCtx} {e A : Expr Nat}
    (hV : KFreeValuesT E Γ) (he : KFreeT E e)
    (hGate : CovSubstGateFor C (ctxModelT_approxTK E n Ξ) R n Γ)
    (hOut : CovObservationGateFor C (ctxModelT_approxTK E n Ξ) R n Γ e e)
    (hOld : FundTyAt (ctxModelT_approxT E) R n Γ e A) :
    FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ e A :=
  fundTyAtCov_of_old hGate hOut ((fundTyAt_approxTK_iff_of_kFree hV he).mpr hOld)

theorem fundConvAtCov_approxTK_of_old_of_kFree {Ξ Γ : LCtx} {a b A : Expr Nat}
    (hV : KFreeValuesT E Γ) (ha : KFreeT E a) (hb : KFreeT E b)
    (hGate : CovSubstGateFor C (ctxModelT_approxTK E n Ξ) R n Γ)
    (hOut : CovObservationGateFor C (ctxModelT_approxTK E n Ξ) R n Γ a b)
    (hOld : FundConvAt (ctxModelT_approxT E) R n Γ a b A) :
    FundConvAtCov C (ctxModelT_approxTK E n Ξ) R n Γ a b A :=
  fundConvAtCov_of_old hGate hOut ((fundConvAt_approxTK_iff_of_kFree hV ha hb).mpr hOld)

/-- Only atomic inversions are needed by the assembled base cases. -/
structure CovAtomicModelLaws (M : CtxModelT E) : Prop where
  bvar_inv : ∀ {ρ : EnvT} {i : Nat} {c : CptT}, M.Ap ρ (.bvar i) c → c = .bot ∨ ρ i c
  sort_inv : ∀ {ρ : EnvT} {l : Level} {c : CptT}, M.Ap ρ (.sort l) c →
    c = .bot ∨ c = sortCode l

theorem covAtomicModelLaws_of_old (hM : CtxModelTLaws M) : CovAtomicModelLaws M :=
  ⟨hM.bvar_inv, hM.sort_inv⟩

theorem covAtomicModelLaws_approxTK (E : ResolvedEnv) (n : Nat) (Ξ : LCtx) :
    CovAtomicModelLaws (ctxModelT_approxTK E n Ξ) :=
  ⟨fun h => approxTK_bvar_inv h, fun h => approxTK_sort_inv h⟩

theorem fundCov_bvar (hM : CovAtomicModelLaws M) {Γ : LCtx}
    (i : Nat) (A : Expr Nat) (hA : lookupType Γ i = some A) :
    FundTyAtCov C M R n Γ (.bvar i) A := by
  intro Δ ρ ρ' σ σ' _ hS c hc
  have hm : c = .bot ∨ (ρ i c ∨ ρ' i c) :=
    hc.elim (fun h => (hM.bvar_inv h).imp_right Or.inl)
      (fun h => (hM.bvar_inv h).imp_right Or.inr)
  exact hm.elim (fun h => by cases h; exact lrSCoreCov_bot C _ _ _ _)
    (fun h => (hS.vars i A hA c h).1)

/-- Where the observed substitution gates agree, the landed variable case
itself is reused through the exact adapter. -/
theorem fundCov_bvar_via_old (hM : CtxModelTLaws M) {Γ : LCtx}
    (hGate : CovSubstGateFor C M R n Γ)
    (i : Nat) (A : Expr Nat) (hA : lookupType Γ i = some A) :
    FundTyAtCov C M R n Γ (.bvar i) A := by
  have hOut : CovObservationGateFor C M R n Γ (.bvar i) (.bvar i) := by
    intro Δ ρ ρ' σ σ' hS c hc
    have hm : c = .bot ∨ (ρ i c ∨ ρ' i c) :=
      hc.elim (fun h => (hM.bvar_inv h).imp_right Or.inl)
        (fun h => (hM.bvar_inv h).imp_right Or.inr)
    exact hm.elim (fun h => by cases h; exact covGateAgreement_bot C)
      (fun h => (hGate hS).vars i A hA c h)
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact fundTyAtCov_of_old hGate hOut (fundT_bvar hM i A hA) hΔ hS c hc

private theorem cov_old_nil_subst {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT} :
    RelSubstAtT M R n Δ ρ ρ' σ σ' [] :=
  ⟨⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩,
    ⟨fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h⟩,
    fun _ _ h => Option.noConfusion h, fun _ _ h => Option.noConfusion h,
    fun _ _ _ h => Option.noConfusion h⟩

/-- The sort case reuses the landed sort proof in the empty source context.
Its result is context-independent, and its output gates are only prop/sort. -/
theorem fundCov_sort (hM : CovAtomicModelLaws M) {Γ : LCtx} (l : Level) :
    FundTyAtCov C M R n Γ (.sort l) (.sort (.succ l)) := by
  intro Δ ρ ρ' σ σ' hΔ _ c hc
  have hm : c = .bot ∨ c = sortCode l := hc.elim hM.sort_inv hM.sort_inv
  rcases hm with rfl | rfl
  · exact lrSCoreCov_bot C _ _ _ _
  · have hg : CovGateAgreement C (sortCode l) := by
      rcases sortCode_prop_or_sort l with h | h
      · rw [h]; exact covGateAgreement_prop C
      · rw [h]; exact covGateAgreement_sort C
    apply (lrSCoreCov_iff_coreS C (sortCode l) hg Δ _ _ _).mpr
    exact fundT_sort (ctxModelTLaws_approxT E) (Γ := []) l hΔ
      (cov_old_nil_subst (ρ := EnvT.bot) (ρ' := EnvT.bot) (σ := σ) (σ' := σ'))
      (sortCode l) (Or.inl (approxT_sort_code E EnvT.bot l))

theorem fundCov_refl {Γ : LCtx} {a A : Expr Nat}
    (h : FundTyAtCov C M R n Γ a A) : FundConvAtCov C M R n Γ a a A := h

/-- Both sort endpoints satisfy the unchanged sort clause.  This relation
does not inspect the equality proof between their universe levels. -/
theorem fundCov_sorts (hM : CovAtomicModelLaws M) {Γ : LCtx} (l₁ l₂ : Level) :
    FundConvAtCov C M R n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) := by
  intro Δ ρ ρ' σ σ' _ _ c hc
  have shape : ∀ {l : Level} {θ : EnvT}, M.Ap θ (.sort l) c →
      c = .bot ∨ c = .prop ∨ c = .sort := by
    intro l θ ho
    rcases hM.sort_inv ho with h | rfl
    · exact Or.inl h
    · exact Or.inr (sortCode_prop_or_sort l)
  have clause : SortClauseT R Δ (substT σ (.sort l₁)) (substT σ' (.sort l₂))
      (substT σ (.sort (.succ l₁))) :=
    ⟨⟨.succ l₁, .refl _⟩, l₁, l₂, .refl _, .refl _⟩
  rcases hc.elim shape shape with rfl | rfl | rfl
  · exact lrSCoreCov_bot C _ _ _ _
  · exact (lrSCoreCov_prop_iff C Δ _ _ _).mpr clause
  · exact (lrSCoreCov_sort_iff C Δ _ _ _).mpr clause

/-- Local zeta uses the let-coherence relation already retained by the full
new substitution package, for observations on either endpoint. -/
theorem fundCov_zetaLocal (hM : CovAtomicModelLaws M) {Γ : LCtx}
    {i : Nat} {v A : Expr Nat} (hv : lookupValue Γ i = some v)
    (hA : lookupType Γ i = some A) :
    FundConvAtCov C M R n Γ (.bvar i) v A := by
  intro Δ ρ ρ' σ σ' _ hS c hc
  rcases hc with ho | ho
  · rcases hM.bvar_inv ho with rfl | hvar
    · exact lrSCoreCov_bot C _ _ _ _
    · exact (hS.lets i v A hv hA c (Or.inl hvar)).1
  · exact (hS.lets i v A hv hA c (Or.inr (Or.inr (Or.inr ho)))).1

theorem fundCov_refl_via_old {Γ : LCtx} {a A : Expr Nat}
    (hGate : CovSubstGateFor C M R n Γ)
    (hOut : CovObservationGateFor C M R n Γ a a)
    (hOld : FundTyAt M R n Γ a A) : FundConvAtCov C M R n Γ a a A :=
  fundConvAtCov_of_old hGate hOut (fundT_refl hOld)

/-- Relation expansion consumes a supplied full contractum motive. -/
theorem fundConvAtCov_of_model_contract (hL : ReadbackLaws E R)
    {Γ : LCtx} {src dst A : Expr Nat}
    (hpres : ∀ ρ c, M.Ap ρ src c → M.Ap ρ dst c)
    (hread : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      CtxWfT E n Δ → RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
      RedR R Δ (substT σ src) (substT σ dst))
    (htarget : FundTyAtCov C M R n Γ dst A) :
    FundConvAtCov C M R n Γ src dst A := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact lrSCoreCov_expand_red C hL (hread hΔ hS) c
    (htarget hΔ hS c (hc.elim (fun h => Or.inl (hpres ρ c h)) Or.inr))

theorem fundConvAtCov_beta_of_model_contract (hL : ReadbackLaws E R)
    {Γ : LCtx} {D body arg A : Expr Nat}
    (hpres : ∀ ρ c, M.Ap ρ (.app (.lam D body) arg) c →
      M.Ap ρ (instantiate0 arg body) c)
    (htarget : FundTyAtCov C M R n Γ (instantiate0 arg body) A) :
    FundConvAtCov C M R n Γ (.app (.lam D body) arg) (instantiate0 arg body) A := by
  have hread : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
      CtxWfT E n Δ → RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ →
      RedR R Δ (substT σ (.app (.lam D body) arg)) (substT σ (instantiate0 arg body)) := by
    intro Δ ρ ρ' σ σ' _ _
    simpa only [substT, substT_instantiate0] using
      (redR_single (hL.beta Δ (substT σ D) (substT σ.up body) (substT σ arg)))
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  exact fundConvAtCov_of_model_contract hL hpres hread htarget hΔ hS c hc

/-- The imported beta adapter is called directly when its old contractum
motive is available and the actually consumed finite gates agree. -/
theorem fundConvAtCov_beta_via_old (hL : ReadbackLaws E R)
    {Γ : LCtx} {D body arg A : Expr Nat}
    (hGate : CovSubstGateFor C M R n Γ)
    (hOut : CovObservationGateFor C M R n Γ
      (.app (.lam D body) arg) (instantiate0 arg body))
    (hpres : ∀ ρ c, M.Ap ρ (.app (.lam D body) arg) c →
      M.Ap ρ (instantiate0 arg body) c)
    (htarget : FundTyAt M R n Γ (instantiate0 arg body) A) :
    FundConvAtCov C M R n Γ (.app (.lam D body) arg) (instantiate0 arg body) A :=
  fundConvAtCov_of_old hGate hOut
    (fundConvAt_beta_of_model_contractT hL hpres htarget)

/-- Exact four-arm elimination; the saturated alternative is passed to its
own supplier and is never discarded or folded into a three-arm model law. -/
theorem approxTK_app_elim_cov {Ξ : LCtx} {ρ : EnvT} {f a : Expr Nat}
    {P : CptT → Prop} (hbot : P .bot)
    (hlam : ∀ g s, ApproxTK E n Ξ ρ f (.lam g) → s ∈ g →
      (∀ u ∈ s.1, ApproxTK E n Ξ ρ a u) → P s.2)
    (hspine : ∀ r args u, ApproxTK E n Ξ ρ f (.spine r args) →
      ApproxTK E n Ξ ρ a u → P (.spine r (args ++ [u])))
    (hsaturated : ∀ c, SaturatedComputationTK E n Ξ ρ (.app f a) c → P c)
    {c : CptT} (hc : ApproxTK E n Ξ ρ (.app f a) c) : P c := by
  rcases approxTK_app_inv hc with rfl | ⟨g, s, rfl, hf, hs, ha⟩ |
    ⟨r, args, u, rfl, hf, ha⟩ | hsat
  · exact hbot
  · exact hlam g s hf hs ha
  · exact hspine r args u hf ha
  · exact hsaturated c hsat

/-- Relation suppliers for the three non-bottom application observations.
The fourth inversion arm is the named `saturated` field. -/
structure CovAppArms (C : CovTyping E) (R : Readback) (n : Nat)
    (Ξ Γ : LCtx) (f a T : Expr Nat) : Prop where
  lam : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ →
    ∀ g s, s ∈ g →
      ((ApproxTK E n Ξ ρ f (.lam g) ∧ ∀ u ∈ s.1, ApproxTK E n Ξ ρ a u) ∨
        (ApproxTK E n Ξ ρ' f (.lam g) ∧ ∀ u ∈ s.1, ApproxTK E n Ξ ρ' a u)) →
      LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app f a))
        (substT σ T) s.2
  spine : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ →
    ∀ r args u,
      ((ApproxTK E n Ξ ρ f (.spine r args) ∧ ApproxTK E n Ξ ρ a u) ∨
        (ApproxTK E n Ξ ρ' f (.spine r args) ∧ ApproxTK E n Ξ ρ' a u)) →
      LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app f a))
        (substT σ T) (.spine r (args ++ [u]))
  saturated : ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}, CtxWfT E n Δ →
    RelSubstAtCov C (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ →
    ∀ c, SaturatedComputationTK E n Ξ ρ (.app f a) c ∨
      SaturatedComputationTK E n Ξ ρ' (.app f a) c →
      LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app f a)) (substT σ T) c

theorem fundCov_app_approxTK_of_arms {Ξ Γ : LCtx} {f a T : Expr Nat}
    (hArms : CovAppArms C R n Ξ Γ f a T) :
    FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ (.app f a) T := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have fromSide : ∀ θ, θ = ρ ∨ θ = ρ' → ApproxTK E n Ξ θ (.app f a) c →
      LRSCoreCov C R n Δ (substT σ (.app f a)) (substT σ' (.app f a)) (substT σ T) c := by
    intro θ hθ hobs
    apply approxTK_app_elim_cov (lrSCoreCov_bot C _ _ _ _) ?_ ?_ ?_ hobs
    · intro g s hf hs ha
      apply hArms.lam hΔ hS g s hs
      rcases hθ with rfl | rfl
      · exact Or.inl ⟨hf, ha⟩
      · exact Or.inr ⟨hf, ha⟩
    · intro r args u hf ha
      apply hArms.spine hΔ hS r args u
      rcases hθ with rfl | rfl
      · exact Or.inl ⟨hf, ha⟩
      · exact Or.inr ⟨hf, ha⟩
    · intro u hu
      apply hArms.saturated hΔ hS u
      rcases hθ with rfl | rfl
      · exact Or.inl hu
      · exact Or.inr hu
  exact hc.elim (fromSide ρ (Or.inl rfl)) (fromSide ρ' (Or.inr rfl))

/-- Native derivations strictly below a size bound, in every source context. -/
def IHBelowFundCov (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n k : Nat) : Prop :=
  (∀ {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A), sizeOf d < k →
    CtxWfT E n Γ → FundTyAtCov C M R n Γ e A) ∧
  (∀ {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A), sizeOf d < k →
    CtxWfT E n Γ → FundConvAtCov C M R n Γ a b A)

def FundTyCovStep (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A) : Prop :=
  CtxWfT E n Γ → IHBelowFundCov C M R n (sizeOf d) → FundTyAtCov C M R n Γ e A

def FundConvCovStep (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat)
    {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A) : Prop :=
  CtxWfT E n Γ → IHBelowFundCov C M R n (sizeOf d) → FundConvAtCov C M R n Γ a b A

/-- Exact residual native constructor obligations.  Every row receives only
the fundamental motives at strictly smaller native derivations. -/
structure FundCovCases (C : CovTyping E) (M : CtxModelT E) (R : Readback) (n : Nat) : Prop where
  const : ∀ {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true),
    FundTyCovStep C M R n (HasTyT.const Γ r ls m hres hlen hwf)
  pi : ∀ {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)),
    FundTyCovStep C M R n (HasTyT.pi Γ A u B v hA hB)
  lam : ∀ {Γ : LCtx} {A body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hb : HasTyT E n (.assumption A :: Γ) body B),
    FundTyCovStep C M R n (HasTyT.lam Γ A u body B hA hb)
  app : ∀ {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A),
    FundTyCovStep C M R n (HasTyT.app Γ f a A B hf ha)
  letE : ∀ {Γ : LCtx} {A value B body : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B),
    FundTyCovStep C M R n (HasTyT.letE Γ A u value B body hA hv hb)
  lit : ∀ {Γ : LCtx} {t : Nat} {T : Expr Nat} (h : HasTyT E n Γ (natExpand t) T),
    FundTyCovStep C M R n (HasTyT.lit Γ t T h)
  conv : ∀ {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (h : HasTyT E n Γ e A) (hc : ConvT E n Γ A B (.sort u)),
    FundTyCovStep C M R n (HasTyT.conv Γ e A B u h hc)
  symm : ∀ {Γ : LCtx} {a b A : Expr Nat} (h : ConvT E n Γ a b A),
    FundConvCovStep C M R n (ConvT.symm Γ a b A h)
  trans : ∀ {Γ : LCtx} {a b c A : Expr Nat}
    (h1 : ConvT E n Γ a b A) (h2 : ConvT E n Γ b c A),
    FundConvCovStep C M R n (ConvT.trans Γ a b c A h1 h2)
  beta : ∀ {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hb : HasTyT E n (.assumption A :: Γ) body B)
    (ha : HasTyT E n Γ arg A),
    FundConvCovStep C M R n (ConvT.beta Γ A body arg B u hA hb ha)
  zeta : ∀ {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B),
    FundConvCovStep C M R n (ConvT.zeta Γ A value body B u hA hv hb)
  delta : ∀ {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b) (htr : transparent m.mclass = true)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hb : HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)),
    FundConvCovStep C M R n (ConvT.delta Γ r ls m b hres hbody htr hlen hwf hb)
  iota : ∀ {Γ : LCtx} {lhs rhs T : Expr Nat} (h : DerivedIota E lhs rhs)
    (hlhs : HasTyT E n Γ lhs T) (hrhs : HasTyT E n Γ rhs T),
    FundConvCovStep C M R n (ConvT.iota Γ lhs rhs T h hlhs hrhs)
  litConv : ∀ {Γ : LCtx} {t : Nat} {exp T : Expr Nat} (h : LiteralExpansion t exp)
    (hexp : HasTyT E n Γ exp T),
    FundConvCovStep C M R n (ConvT.lit Γ t exp T h hexp)
  appConv : ∀ {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : ConvT E n Γ f g (.pi A B)) (h2 : ConvT E n Γ a b A),
    FundConvCovStep C M R n (ConvT.app Γ f g a b A B h1 h2)
  lamConv : ∀ {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hb : ConvT E n (.assumption A :: Γ) b b' B),
    FundConvCovStep C M R n (ConvT.lam Γ A A' b b' B u hA hb)
  piConv : ∀ {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hB : ConvT E n (.assumption A :: Γ) B B' (.sort v)),
    FundConvCovStep C M R n (ConvT.pi Γ A A' B B' u v hA hB)
  letEConv : ∀ {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ v v' A)
    (hb : ConvT E n (.letBinding A v :: Γ) b b' B),
    FundConvCovStep C M R n (ConvT.letE Γ A A' v v' b b' B u hA hv hb)
  consts : ∀ {Γ : LCtx} {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls'),
    FundConvCovStep C M R n (ConvT.consts Γ r ls ls' m hres hlen hwf hwf' h)
  eta : ∀ {Γ : LCtx} {f A B : Expr Nat} (h : HasTyT E n Γ f (.pi A B)),
    FundConvCovStep C M R n (ConvT.eta Γ f A B h)
  irr : ∀ {Γ : LCtx} {P p q : Expr Nat} (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P),
    FundConvCovStep C M R n (ConvT.irr Γ P p q hP hp hq)
  tyConv : ∀ {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
    (h : ConvT E n Γ a b A) (hA : ConvT E n Γ A A' (.sort u)),
    FundConvCovStep C M R n (ConvT.tyConv Γ a b A A' u h hA)

/-- One native derivation step.  Base cases are discharged here; every
remaining constructor is routed to its exact named obligation. -/
theorem fundCov_step (hM : CovAtomicModelLaws M) (hCases : FundCovCases C M R n) :
    (∀ {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A), FundTyCovStep C M R n d) ∧
    (∀ {Γ : LCtx} {a b A : Expr Nat} (d : ConvT E n Γ a b A), FundConvCovStep C M R n d) := by
  constructor
  · intro Γ e A d hΓ ih
    cases d with
    | sort Γ l => exact fundCov_sort hM l
    | bvar Γ i A h => exact fundCov_bvar hM i A h
    | const Γ r ls m hres hlen hwf => exact hCases.const hres hlen hwf hΓ ih
    | pi Γ A u B v hA hB => exact hCases.pi hA hB hΓ ih
    | lam Γ A u b B hA hb => exact hCases.lam hA hb hΓ ih
    | app Γ f a A B hf ha => exact hCases.app hf ha hΓ ih
    | letE Γ A u v B b hA hv hb => exact hCases.letE hA hv hb hΓ ih
    | lit Γ t T h => exact hCases.lit h hΓ ih
    | conv Γ e A B u h hc => exact hCases.conv h hc hΓ ih
  · intro Γ a b A d hΓ ih
    cases d with
    | refl Γ a A ht =>
      have hlt : sizeOf ht < sizeOf (ConvT.refl Γ a A ht) := by simp; omega
      intro Δ ρ ρ' σ σ' hΔ hS c hc
      exact ih.1 ht hlt hΓ hΔ hS c hc
    | symm Γ a b A h => exact hCases.symm h hΓ ih
    | trans Γ a b c A h1 h2 => exact hCases.trans h1 h2 hΓ ih
    | beta Γ A body arg B u hA hb ha => exact hCases.beta hA hb ha hΓ ih
    | zeta Γ A value body B u hA hv hb => exact hCases.zeta hA hv hb hΓ ih
    | zetaLocal Γ i A v hv hA ht => exact fundCov_zetaLocal hM hv hA
    | delta Γ r ls m b hres hbody htr hlen hwf hb =>
      exact hCases.delta hres hbody htr hlen hwf hb hΓ ih
    | iota Γ lhs rhs T h hl hr => exact hCases.iota h hl hr hΓ ih
    | lit Γ t exp T h ht => exact hCases.litConv h ht hΓ ih
    | app Γ f g a b A B h1 h2 => exact hCases.appConv h1 h2 hΓ ih
    | lam Γ A A' b b' B u hA hb => exact hCases.lamConv hA hb hΓ ih
    | pi Γ A A' B B' u v hA hB => exact hCases.piConv hA hB hΓ ih
    | letE Γ A A' v v' b b' B u hA hv hb => exact hCases.letEConv hA hv hb hΓ ih
    | sorts Γ l₁ l₂ h => exact fundCov_sorts hM l₁ l₂
    | consts Γ r ls ls' m hres hlen hwf hwf' h => exact hCases.consts hres hlen hwf hwf' h hΓ ih
    | eta Γ f A B h => exact hCases.eta h hΓ ih
    | irr Γ P p q hP hp hq => exact hCases.irr hP hp hq hΓ ih
    | tyConv Γ a b A A' u h hA => exact hCases.tyConv h hA hΓ ih

/-- Strong recursion calls the step only after supplying all derivations of
strictly smaller native size.  The comparison is the premise `hd`. -/
theorem fundCov_strong (hM : CovAtomicModelLaws M) (hCases : FundCovCases C M R n)
    (k : Nat) : IHBelowFundCov C M R n k :=
  Nat.strongRecOn k (fun j ih =>
    ⟨fun {Γ e A} d hd hΓ => (fundCov_step hM hCases).1 d hΓ (ih (sizeOf d) hd),
      fun {Γ a b A} d hd hΓ => (fundCov_step hM hCases).2 d hΓ (ih (sizeOf d) hd)⟩)

theorem fundamentalCovAt_of_cases (hM : CovAtomicModelLaws M)
    (hCases : FundCovCases C M R n) : FundamentalCovAt C M R n := by
  constructor
  · intro Γ hΓ e A d
    exact (fundCov_strong hM hCases (sizeOf d + 1)).1 d (Nat.lt_succ_self _) hΓ
  · intro Γ hΓ a b A d
    exact (fundCov_strong hM hCases (sizeOf d + 1)).2 d (Nat.lt_succ_self _) hΓ

theorem fundamentalCovAt_approxTK_of_cases {Ξ : LCtx}
    (hCases : FundCovCases C (ctxModelT_approxTK E n Ξ) R n) :
    FundamentalCovAt C (ctxModelT_approxTK E n Ξ) R n :=
  fundamentalCovAt_of_cases (covAtomicModelLaws_approxTK E n Ξ) hCases

/-- Context validity follows from an already supplied full fundamental theorem
and native context well-formedness, without a model-typing escape. -/
theorem ctxValidAtCov_of_fundamental (hF : FundamentalCovAt C M R n) (hcl : EnvClosed E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) : CtxValidAtCov C M R n Γ := by
  intro i A hA
  obtain ⟨u, ⟨ht⟩⟩ :=
    Rcic.Declarative.NativeValleys.TypedModelAudit.ctxWfT_lookupType_sort hcl hΓ hA
  exact ⟨u, hF.1 hΓ ht⟩

/-- One concrete reuse of a landed `FundCases` row.  The native old IH and
context-validity inputs remain explicit; K-free transport supplies no such laws. -/
theorem fundCov_app_via_old_cases {Ξ Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A)
    (hΓ : CtxWfT E n Γ) (hValid : CtxValidAt (ctxModelT_approxT E) R n Γ)
    (hOldCases : FundCases (ctxModelT_approxT E) R n)
    (hIH : Rcic.Declarative.NativeValleys.TypedModelAudit.IHBelow
      (ctxModelT_approxT E) R n (sizeOf (HasTyT.app Γ f a A B hf ha)))
    (hV : KFreeValuesT E Γ) (he : KFreeT E (.app f a))
    (hGate : CovSubstGateFor C (ctxModelT_approxTK E n Ξ) R n Γ)
    (hOut : CovObservationGateFor C (ctxModelT_approxTK E n Ξ) R n Γ (.app f a) (.app f a)) :
    FundTyAtCov C (ctxModelT_approxTK E n Ξ) R n Γ (.app f a) (instantiate0 a B) :=
  fundTyAtCov_approxTK_of_old_of_kFree hV he hGate hOut
    (hOldCases.app hf ha hΓ hValid hIH).1

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_FUND_ROOTS
#print axioms FundTyAtCov
#print axioms FundConvAtCov
#print axioms FundamentalCovAt
#print axioms TyValidAtCov
#print axioms CtxValidAtCov
#print axioms FundTyAtCov.modelMap
#print axioms fundTyAtCov_congr
#print axioms FundConvAtCov.modelMap
#print axioms fundConvAtCov_congr
#print axioms fundTyAtCov_approxTK_iff_of_kFree
#print axioms fundConvAtCov_approxTK_iff_of_kFree
#print axioms CovSubstGateFor
#print axioms CovObservationGateFor
#print axioms fundTyAtCov_of_old
#print axioms fundConvAtCov_of_old
#print axioms fundTyAtCov_approxTK_of_old_of_kFree
#print axioms fundConvAtCov_approxTK_of_old_of_kFree
#print axioms CovAtomicModelLaws
#print axioms covAtomicModelLaws_of_old
#print axioms covAtomicModelLaws_approxTK
#print axioms fundCov_bvar
#print axioms fundCov_bvar_via_old
#print axioms fundCov_sort
#print axioms fundCov_refl
#print axioms fundCov_sorts
#print axioms fundCov_zetaLocal
#print axioms fundCov_refl_via_old
#print axioms fundConvAtCov_of_model_contract
#print axioms fundConvAtCov_beta_of_model_contract
#print axioms fundConvAtCov_beta_via_old
#print axioms approxTK_app_elim_cov
#print axioms CovAppArms
#print axioms fundCov_app_approxTK_of_arms
#print axioms IHBelowFundCov
#print axioms FundTyCovStep
#print axioms FundConvCovStep
#print axioms FundCovCases
#print axioms fundCov_step
#print axioms fundCov_strong
#print axioms fundamentalCovAt_of_cases
#print axioms fundamentalCovAt_approxTK_of_cases
#print axioms ctxValidAtCov_of_fundamental
#print axioms fundCov_app_via_old_cases
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_FUND_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelAudit
