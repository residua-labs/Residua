import rcic.RcicNativeTypedModelCovKTyping
import rcic.RcicNativeTypedModelCovPropagation

/-!
# Covariant typing and the landed relation: a precise boundary

`CTyCov` does not re-enter `CTyS`, even at the observed non-bottom compact
of the natively typed, closed polymorphic identity.  Both its term and type
are K-free, so the obstruction is realized by the unchanged `ApproxTK` as
well as `ApproxT`.  No untyped or unrealized compact is used to refute the
named re-entry port.

The envelope below pairs the imported covariant typing with the unchanged
`LRSCoreS`.  It is a bridge at a fixed type expression, not a replacement
recursive relation: both-sided readback expansion preserves the typing
conjunct, and the actual typed Eq alias gives a non-bottom instance.

The remaining interface is explicit.  `LRSCoreS` hardwires `CTyS` in its
Pi-demand gate.  Its `IrrelAtS`, `SymmTmAtS`, `TransTmAtS`, and `typedPERS`
therefore do not accept `CTyCov` by casting.  A relation with covariant
recursive gates needs a genuinely new relation name, corresponding PER
motives and proof, a relation-bearing substitution package, and new
`FundTyAt` / `FundConvAt` motives.  In particular, the landed pointwise
`relSubstAtT_cons_pointwise` still takes `CTyS` demands.  The envelope
below supplies none of these missing recursive interfaces.

This leaf makes no claim about the contents or delivery of an unavailable
escape brief.  All landed definitions and observations are unchanged.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit.TypingFin
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKFailureAudit
open Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit
open Rcic.Declarative.NativeValleys.TypedModelCovKAudit
open Rcic.Declarative.NativeValleys.TypedModelCovPropagationAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- The selected covering relation is strictly weaker at one actual type
code.  The rejected `CTyS` witness would inhabit the imported forbidden
`ElT` of the same polymorphic identity type. -/
theorem ctyCov_strict_polyId (E : ResolvedEnv) :
    CTyCov E polyIdCpt01 polyIdTyCpt01 ∧
      ¬ CTyS E polyIdCpt01 polyIdTyCpt01 :=
  ⟨ctyCov_polyIdCpt01_polyIdTyCpt01 E, fun h =>
    not_elT_polyId_cpt01 E EnvT.bot
      ⟨polyIdTyCpt01, approxT_cexPolyIdTy_cpt01 E EnvT.bot, h⟩⟩

/-- Unconditional re-entry into the old compact-typing interface, even
after requiring a well-formed native context, native term typing, a typed
valuation, and an actual model observation.  The output may choose any
realized type code; it is not forced to reuse the covariant witness. -/
def NativeCovToSReentryM (M : CtxModelT E) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {e A : Expr Nat}, CtxWfT E n Γ → HasTyT E n Γ e A →
    ∀ {ρ : EnvT} {u : CptT}, EnvTypedCovAtM M Γ ρ → M.Ap ρ e u →
      ElTCovM M ρ A u → ∃ a, M.Ap ρ A a ∧ CTyS E u a

/-- The old model realizes both non-bottom compacts at an actual native
typing, while no code of the declared type satisfies `CTyS`. -/
theorem polyId_cov_reentry_control_approxT (E : ResolvedEnv) (n : Nat) (ρ : EnvT) :
    Nonempty (HasTyT E n [] cexPolyId cexPolyIdTy) ∧
    EnvTypedCovAtM (ctxModelT_approxT E) [] ρ ∧
    ApproxT E ρ cexPolyId polyIdCpt01 ∧
    ApproxT E ρ cexPolyIdTy polyIdTyCpt01 ∧
    CTyCov E polyIdCpt01 polyIdTyCpt01 ∧
    polyIdCpt01 ≠ .bot ∧ polyIdTyCpt01 ≠ .bot ∧
    ¬ ElT E ρ cexPolyIdTy polyIdCpt01 :=
  ⟨⟨hasTyT_cexPolyId E n⟩, envTypedCovAtM_nil _ ρ,
    approxT_cexPolyId_cpt01 E ρ, approxT_cexPolyIdTy_cpt01 E ρ,
    ctyCov_polyIdCpt01_polyIdTyCpt01 E,
    (fun h => CptT.noConfusion h), (fun h => CptT.noConfusion h),
    not_elT_polyId_cpt01 E ρ⟩

private theorem kFreeT_polyId (E : ResolvedEnv) : KFreeT E cexPolyId :=
  kFreeT_lam (kFreeT_sort E _) (kFreeT_lam (kFreeT_bvar E 0) (kFreeT_bvar E 0))

private theorem kFreeT_polyIdTy (E : ResolvedEnv) : KFreeT E cexPolyIdTy :=
  kFreeT_pi (kFreeT_sort E _) (kFreeT_pi (kFreeT_bvar E 0) (kFreeT_bvar E 1))

/-- The same native typing and both non-bottom observations survive in the
unchanged saturated model.  Its forgetful projection refutes re-entry at
every possible type observation, not merely the displayed type code. -/
theorem polyId_cov_reentry_control_approxTK (E : ResolvedEnv) (n : Nat) (ρ : EnvT) :
    Nonempty (HasTyT E n [] cexPolyId cexPolyIdTy) ∧
    EnvTypedCovAtM (ctxModelT_approxTK E n []) [] ρ ∧
    ApproxTK E n [] ρ cexPolyId polyIdCpt01 ∧
    ApproxTK E n [] ρ cexPolyIdTy polyIdTyCpt01 ∧
    CTyCov E polyIdCpt01 polyIdTyCpt01 ∧
    polyIdCpt01 ≠ .bot ∧ polyIdTyCpt01 ≠ .bot ∧
    ¬ ∃ a, ApproxTK E n [] ρ cexPolyIdTy a ∧ CTyS E polyIdCpt01 a := by
  refine ⟨⟨hasTyT_cexPolyId E n⟩, envTypedCovAtM_nil _ ρ,
    ApproxTK.free (kFreeT_polyId E) (approxT_cexPolyId_cpt01 E ρ),
    ApproxTK.free (kFreeT_polyIdTy E) (approxT_cexPolyIdTy_cpt01 E ρ),
    ctyCov_polyIdCpt01_polyIdTyCpt01 E,
    (fun h => CptT.noConfusion h), (fun h => CptT.noConfusion h), ?_⟩
  rintro ⟨a, ha, hty⟩
  exact not_elT_polyId_cpt01 E ρ ⟨a, approxTK_forget ha, hty⟩

/-- Native typing and covariant environment typing do not provide an
unconditional return to the old `CTyS` consumers. -/
theorem not_nativeCovToSReentryM_approxT (E : ResolvedEnv) (n : Nat) :
    ¬ NativeCovToSReentryM (ctxModelT_approxT E) n := by
  intro h
  obtain ⟨⟨ht⟩, hρ, he, hA, hCov, _, _, hnot⟩ :=
    polyId_cov_reentry_control_approxT E n EnvT.bot
  exact hnot (h .nil ht hρ he ⟨polyIdTyCpt01, hA, hCov⟩)

/-- The same re-entry port fails for `ApproxTK`, entirely on K-free terms. -/
theorem not_nativeCovToSReentryM_approxTK (E : ResolvedEnv) (n : Nat) :
    ¬ NativeCovToSReentryM (ctxModelT_approxTK E n []) n := by
  intro h
  obtain ⟨⟨ht⟩, hρ, he, hA, hCov, _, _, hnot⟩ :=
    polyId_cov_reentry_control_approxTK E n EnvT.bot
  exact hnot (h .nil ht hρ he ⟨polyIdTyCpt01, hA, hCov⟩)

/-- A covariant typing envelope around the existing relation, at the
unchanged model type expression.  This definition deliberately retains
`LRSCoreS`; it is not a new covariant recursive relation. -/
def CovTypedEnvelopeT (M : CtxModelT E) (R : Readback) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (x y A : Expr Nat) (c : CptT) : Prop :=
  ElTCovM M ρ A c ∧ LRSCoreS R E n Γ x y A c

/-- Expansion on both relation endpoints preserves the fixed type
observation and the imported covariant compact typing without re-entry. -/
theorem covTypedEnvelopeT_expand_red (hL : ReadbackLaws E R)
    {M : CtxModelT E} {Γ : LCtx} {ρ : EnvT} {x x' y y' A : Expr Nat} {c : CptT}
    (hx : RedR R Γ x x') (hy : RedR R Γ y y')
    (h : CovTypedEnvelopeT M R n Γ ρ x' y' A c) :
    CovTypedEnvelopeT M R n Γ ρ x y A c :=
  ⟨h.1, lrSCoreS_expand_red hL hx c (lrSCoreS_expand_red_right hL hy c h.2)⟩

/-- The actual nonempty Eq context admits the covariant environment guard.
Its three entries are assumptions, so no let-value obligation is omitted. -/
theorem envTypedCovAtM_eqGap_bot (n : Nat) :
    EnvTypedCovAtM (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot := by
  apply envTypedCovAtM_of_envTypedAtT
    (envTypedAtT_approxTK_bot eqEnvT n eqGapCtx eqGapCtx)
  intro i v hv
  cases i with
  | zero => simp [eqGapCtx, lookupValue] at hv
  | succ i =>
    cases i with
    | zero => simp [eqGapCtx, lookupValue] at hv
    | succ i =>
      cases i with
      | zero => simp [eqGapCtx, lookupValue] at hv
      | succ i => simp [eqGapCtx, lookupValue] at hv

/-- The actual admitted Eq alias inhabits the bridge at the non-bottom
compact `.prop`, typed covariantly at the realized `.sort` code.  The
source still lacks that model observation, so the envelope is not a
model beta-expansion principle. -/
theorem eqGapDirectAlias_cov_envelope_control (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovAtM (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx eqGapPrefix (.pi A B)) ∧
      Nonempty (ConvT eqEnvT n eqGapCtx (eqGapDirectAlias A B) eqGapRedex
        (.sort (.succ .zero))) ∧
      ∀ ρ, CovTypedEnvelopeT (ctxModelT_approxTK eqEnvT n eqGapCtx)
          (WhStepCK2 eqEnvT n) n eqGapCtx ρ (eqGapDirectAlias A B)
          eqGapRedex (.sort (.succ .zero)) .prop ∧
        ApproxTK eqEnvT n eqGapCtx ρ eqGapRedex .prop ∧
        ¬ ApproxTK eqEnvT n eqGapCtx ρ (eqGapDirectAlias A B) .prop := by
  obtain ⟨A, B, hty, hbeta, _, hobs, hrel⟩ := eqGapDirectAlias_beta_route_control n
  refine ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, envTypedCovAtM_eqGap_bot n,
    A, B, hty, hbeta, ?_⟩
  intro ρ
  refine ⟨⟨?_, hrel⟩, (hobs ρ).1, (hobs ρ).2⟩
  exact ⟨.sort, approxTK_sort_code eqEnvT n eqGapCtx ρ (.succ .zero),
    by rw [CTyCov]; exact Or.inr TyCodeCT.prop⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_BOUNDARY_ROOTS
#print axioms ctyCov_strict_polyId
#print axioms NativeCovToSReentryM
#print axioms polyId_cov_reentry_control_approxT
#print axioms polyId_cov_reentry_control_approxTK
#print axioms not_nativeCovToSReentryM_approxT
#print axioms not_nativeCovToSReentryM_approxTK
#print axioms CovTypedEnvelopeT
#print axioms covTypedEnvelopeT_expand_red
#print axioms envTypedCovAtM_eqGap_bot
#print axioms eqGapDirectAlias_cov_envelope_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelBoundaryAudit
