import rcic.RcicNativeTypedModelCovRelSubst
import rcic.RcicNativeTypedModelCovRelAgreement

/-!
# Recursive-gate agreement at the observed substitution footprint

The old-package bridge below asks only for gate agreement at compact
observations consumed by the variable and let fields.  It does not require
agreement of the relations at every compact.  Both environment guards and
all native substitution evidence remain visible.

The diagonal operations use the diagonal relations already stored in the
package.  No native conversion symmetry or global typing supplier is needed.
The existing nonempty let-context control has the required gate agreement at
every observation of its bound sort.  `closure_claim = 0`.
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
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit

variable {E : ResolvedEnv} {C : CovTyping E} {M N : CtxModelT E}
  {R : Readback} {n : Nat}

/-- Gate agreement at precisely the observations inspected by a related
substitution.  Context lookup excludes unrelated environment entries. -/
structure CovSubstGateAt (C : CovTyping E) (M : CtxModelT E)
    (Γ : LCtx) (ρ ρ' : EnvT) : Prop where
  vars : ∀ i A, lookupType Γ i = some A → ∀ c, ρ i c ∨ ρ' i c →
    CovGateAgreement C c
  lets : ∀ i v A, lookupValue Γ i = some v → lookupType Γ i = some A →
    ∀ c, ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c → CovGateAgreement C c

/-- The finite gates actually read by `vars` and `lets` suffice to reuse the
old related-substitution package. -/
theorem RelSubstAtCov.toOld {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ)
    (hGate : CovSubstGateAt C M Γ ρ ρ') :
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ := by
  refine ⟨h.typedL, h.typedR, h.conv, ?_, ?_⟩
  · intro i A hA c hc
    have he := lrSCoreCov_iff_coreS (R := R) (n := n) C c (hGate.vars i A hA c hc) Δ
    exact (and_congr (he _ _ _) (and_congr (he _ _ _)
      (and_congr (he _ _ _) (he _ _ _)))).mp (h.vars i A hA c hc)
  · intro i v A hv hA c hc
    have he := lrSCoreCov_iff_coreS (R := R) (n := n) C c (hGate.lets i v A hv hA c hc) Δ
    exact (and_congr (he _ _ _) (and_congr (he _ _ _)
      (and_congr (he _ _ _) (he _ _ _)))).mp (h.lets i v A hv hA c hc)

/-- The converse retains the two coherent typed environments as separate
inputs; the old package does not provide them. -/
theorem RelSubstAtCov.ofOld {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtT M R n Δ ρ ρ' σ σ' Γ)
    (hρ : EnvTypedCovAtP C M Γ ρ) (hρ' : EnvTypedCovAtP C M Γ ρ')
    (hGate : CovSubstGateAt C M Γ ρ ρ') :
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ := by
  refine ⟨h.1, h.2.1, h.2.2.1, hρ, hρ', ?_, ?_⟩
  · intro i A hA c hc
    have he := lrSCoreCov_iff_coreS (R := R) (n := n) C c (hGate.vars i A hA c hc) Δ
    exact (and_congr (he _ _ _) (and_congr (he _ _ _)
      (and_congr (he _ _ _) (he _ _ _)))).mpr (h.2.2.2.1 i A hA c hc)
  · intro i v A hv hA c hc
    have he := lrSCoreCov_iff_coreS (R := R) (n := n) C c (hGate.lets i v A hv hA c hc) Δ
    exact (and_congr (he _ _ _) (and_congr (he _ _ _)
      (and_congr (he _ _ _) (he _ _ _)))).mpr (h.2.2.2.2 i v A hv hA c hc)

theorem relSubstAtCov_iff_old_of_gate {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (hGate : CovSubstGateAt C M Γ ρ ρ') :
    RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ ↔
      RelSubstAtT M R n Δ ρ ρ' σ σ' Γ ∧
        EnvTypedCovAtP C M Γ ρ ∧ EnvTypedCovAtP C M Γ ρ' :=
  ⟨fun h => ⟨h.toOld hGate, h.envL, h.envR⟩,
    fun h => RelSubstAtCov.ofOld h.1 h.2.1 h.2.2 hGate⟩

/-- The footprint guard reads the model only at lookup values. -/
theorem CovSubstGateAt.modelMap {Γ : LCtx} {ρ ρ' : EnvT}
    (h : CovSubstGateAt C M Γ ρ ρ') (hV : ValueAgreementT M N Γ) :
    CovSubstGateAt C N Γ ρ ρ' where
  vars := h.vars
  lets := by
    intro i v A hv hA c hc
    apply h.lets i v A hv hA c
    exact (or_congr Iff.rfl (or_congr Iff.rfl
      (or_congr (hV i v hv ρ c) (hV i v hv ρ' c)))).mpr hc

theorem covSubstGateAt_congr {Γ : LCtx} {ρ ρ' : EnvT}
    (hV : ValueAgreementT M N Γ) :
    CovSubstGateAt C M Γ ρ ρ' ↔ CovSubstGateAt C N Γ ρ ρ' :=
  ⟨fun h => h.modelMap hV,
    fun h => h.modelMap (fun i v hv => modelAgreementAtT_symm (hV i v hv))⟩

theorem covSubstGateAt_approxTK_iff_of_kFree_values {Ξ Γ : LCtx} {ρ ρ' : EnvT}
    (hV : KFreeValuesT E Γ) :
    CovSubstGateAt C (ctxModelT_approxTK E n Ξ) Γ ρ ρ' ↔
      CovSubstGateAt C (ctxModelT_approxT E) Γ ρ ρ' :=
  covSubstGateAt_congr (valueAgreementT_approxTK_of_kFree hV)

private theorem cov_or4_elim {p q r s t : Prop}
    (hp : p → t) (hq : q → t) (hr : r → t) (hs : s → t)
    (h : p ∨ q ∨ r ∨ s) : t :=
  h.elim hp (fun h => h.elim hq (fun h => h.elim hr hs))

private theorem cov_native_subst_diag {Δ Γ : LCtx} {σ : SubstT}
    (h : TypedSubstT E n Δ σ Γ) : ConvSubstT E n Δ σ σ Γ := by
  intro i A hA
  obtain ⟨ht⟩ := h.1 i A hA
  exact ⟨.refl _ _ _ ht⟩

/-- Select the stored left diagonal; no PER or native conversion flip is used. -/
theorem RelSubstAtCov.diagL {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ) :
    RelSubstAtCov C M R n Δ ρ ρ σ σ Γ := by
  refine ⟨h.typedL, h.typedL, cov_native_subst_diag h.typedL,
    h.envL, h.envL, ?_, ?_⟩
  · intro i A hA c hc
    have hr := (h.vars i A hA c (Or.inl (hc.elim id id))).2.2.1
    exact ⟨hr, hr, hr, hr⟩
  · intro i v A hv hA c hc
    have hm : ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c :=
      cov_or4_elim Or.inl Or.inl
        (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => Or.inr (Or.inr (Or.inl h))) hc
    have hr := (h.lets i v A hv hA c hm).2.2.1
    exact ⟨hr, hr, hr, hr⟩

/-- Select the stored right diagonal independently of native conversion symmetry. -/
theorem RelSubstAtCov.diagR {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT}
    (h : RelSubstAtCov C M R n Δ ρ ρ' σ σ' Γ) :
    RelSubstAtCov C M R n Δ ρ' ρ' σ' σ' Γ := by
  refine ⟨h.typedR, h.typedR, cov_native_subst_diag h.typedR,
    h.envR, h.envR, ?_, ?_⟩
  · intro i A hA c hc
    have hr := (h.vars i A hA c (Or.inr (hc.elim id id))).2.2.2
    exact ⟨hr, hr, hr, hr⟩
  · intro i v A hv hA c hc
    have hm : ρ i c ∨ ρ' i c ∨ M.Ap ρ v c ∨ M.Ap ρ' v c :=
      cov_or4_elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inl h))
        (fun h => Or.inr (Or.inr (Or.inr h)))
        (fun h => Or.inr (Or.inr (Or.inr h))) hc
    have hr := (h.lets i v A hv hA c hm).2.2.2
    exact ⟨hr, hr, hr, hr⟩

theorem CovSubstGateAt.diagL {Γ : LCtx} {ρ ρ' : EnvT}
    (h : CovSubstGateAt C M Γ ρ ρ') : CovSubstGateAt C M Γ ρ ρ where
  vars := fun i A hA c hc => h.vars i A hA c (Or.inl (hc.elim id id))
  lets := fun i v A hv hA c hc => h.lets i v A hv hA c
    (cov_or4_elim Or.inl Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))
      (fun h => Or.inr (Or.inr (Or.inl h))) hc)

theorem CovSubstGateAt.diagR {Γ : LCtx} {ρ ρ' : EnvT}
    (h : CovSubstGateAt C M Γ ρ ρ') : CovSubstGateAt C M Γ ρ' ρ' where
  vars := fun i A hA c hc => h.vars i A hA c (Or.inr (hc.elim id id))
  lets := fun i v A hv hA c hc => h.lets i v A hv hA c
    (cov_or4_elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inl h))
      (fun h => Or.inr (Or.inr (Or.inr h))) (fun h => Or.inr (Or.inr (Or.inr h))) hc)

private theorem cov_gate_of_sort_zero (C : CovTyping E) {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ (.sort .zero) c) : CovGateAgreement C c := by
  rcases approxT_sort_inv h with rfl | hc
  · exact covGateAgreement_bot C
  · rw [sortCode_zero] at hc
    subst c
    exact covGateAgreement_prop C

/-- The real let-context witness needs only the always-compatible bottom and
proposition observations; no global gate-agreement assumption is introduced. -/
theorem covSubstGateAt_zetaLocalSortCtx_approxTK (C : CovTyping E) (n : Nat) (Ξ : LCtx) :
    CovSubstGateAt C (ctxModelT_approxTK E n Ξ) zetaLocalSortCtx
      (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx) := by
  refine ⟨?_, ?_⟩
  · intro i A hA c hc
    cases i with
    | zero => exact cov_gate_of_sort_zero C (hc.elim id id)
    | succ i => simp [zetaLocalSortCtx, lookupType] at hA
  · intro i v A hv hA c hc
    cases i with
    | zero =>
      change some (.sort .zero) = some v at hv
      cases Option.some.inj hv
      exact cov_or4_elim (cov_gate_of_sort_zero C) (cov_gate_of_sort_zero C)
        (fun h => cov_gate_of_sort_zero C (approxTK_forget h))
        (fun h => cov_gate_of_sort_zero C (approxTK_forget h)) hc
    | succ i => simp [zetaLocalSortCtx, lookupValue] at hv

/-- The nonempty native let control exercises the observation-restricted bridge. -/
theorem relSubstAtCov_zetaLocalSortCtx_toOld (hW : EnvWfT E) (n : Nat) (Ξ : LCtx) :
    RelSubstAtT (ctxModelT_approxTK E n Ξ) (WhStepCK2 E n) n zetaLocalSortCtx
      (ctxEnvT E zetaLocalSortCtx) (ctxEnvT E zetaLocalSortCtx)
      SubstT.id SubstT.id zetaLocalSortCtx :=
  (relSubstAtCov_zetaLocalSortCtx_approxTK hW n Ξ).toOld
    (covSubstGateAt_zetaLocalSortCtx_approxTK (covTypingCTyCov E) n Ξ)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_SUBST_AGREEMENT_ROOTS
#print axioms CovSubstGateAt
#print axioms RelSubstAtCov.toOld
#print axioms RelSubstAtCov.ofOld
#print axioms relSubstAtCov_iff_old_of_gate
#print axioms CovSubstGateAt.modelMap
#print axioms covSubstGateAt_congr
#print axioms covSubstGateAt_approxTK_iff_of_kFree_values
#print axioms RelSubstAtCov.diagL
#print axioms RelSubstAtCov.diagR
#print axioms CovSubstGateAt.diagL
#print axioms CovSubstGateAt.diagR
#print axioms covSubstGateAt_zetaLocalSortCtx_approxTK
#print axioms relSubstAtCov_zetaLocalSortCtx_toOld
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_SUBST_AGREEMENT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelAudit
