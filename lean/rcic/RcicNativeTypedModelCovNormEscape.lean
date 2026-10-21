import rcic.RcicNativeTypedModelCovRelRealization
import rcic.RcicNativeTypedModelCovNormReadback
import rcic.RcicNativeTypedModelCovNormCov2
import rcic.RcicNativeTypedModelCovRelFund

/-!
# A normal Pi index retains the raw alias obstruction in its domain

The normalized target uses weak-head readback. A Pi expression is already
normal even when its domain is the actual Eq function-variable alias. The
identity lambda still has a non-bottom model demand at that domain, while
every model observation of the domain is bottom. The lambda alternative of
`CovTyping.pi_inv` therefore rules out compact typing, uniformly in the
compact typing implementation, including a rigid-spine extension.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovNormEscapeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open TypedModelCovKAudit TypedModelCovRelBoundaryAudit TypedModelCovRelAudit
open TypedModelCovRelEscapeAudit TypedModelCovRelWitnessAudit
open TypedModelCovRelRealizationAudit TypedModelCovNormReadbackAudit
open TypedModelCovPropagationAudit TypedModelCovNormCov2Audit

/-- The term's annotation remains `Sort 0`; native conversion changes its
declared Pi domain to the Eq alias. -/
def covNormAliasIdentity : Expr Nat := .lam (.sort .zero) (.bvar 0)

/-- A single actual identity row with the non-bottom proposition demand. -/
def covNormAliasIdentityCpt : CptT := .lam [([.pi .bot []], .pi .bot [])]

/-- Readback does not descend below the Pi head. -/
def covNormAliasPi (A B : Expr Nat) : Expr Nat :=
  .pi (eqGapDirectAlias A B) (.sort .zero)

private theorem cov_lam_row_not_bot_domain {E : ResolvedEnv}
    (C : CovTyping E) (f : List (List CptT × CptT)) :
    ¬ C.ty covNormAliasIdentityCpt (.pi .bot f) := by
  intro h
  rcases C.pi_inv h with hbot | hlam | hspine
  · exact CptT.noConfusion hbot
  · obtain ⟨g, heq, hdom, _⟩ := hlam
    have hg : [([CptT.pi .bot []], CptT.pi .bot [])] = g := CptT.lam.inj heq
    subst g
    have hbad := hdom ([.pi .bot []], .pi .bot [])
      (List.mem_singleton.mpr rfl) (.pi .bot []) (List.mem_singleton.mpr rfl)
    exact CptT.noConfusion (C.bot_inv hbad)
  · obtain ⟨r, args, heq⟩ := hspine
    exact CptT.noConfusion heq

/-- The exact compact-typing obstruction, exposed for model-interface
restatements without duplicating its constructor inversion proof. -/
theorem not_covNormAliasIdentityCpt_pi_bot {E : ResolvedEnv}
    (C : CovTyping E) (f : List (List CptT × CptT)) :
    ¬ C.ty covNormAliasIdentityCpt (.pi .bot f) :=
  cov_lam_row_not_bot_domain C f

/-- An actual term observation, for every model context and valuation. The
model's original `CTyS` demand introduction is discharged directly. -/
theorem covNormAliasIdentity_approxTK (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    ApproxTK E n Γ ρ covNormAliasIdentity covNormAliasIdentityCpt := by
  change ApproxTK E n Γ ρ (.lam (.sort .zero) (.bvar 0))
    (.lam [([.pi .bot []], .pi .bot [])])
  refine .lam (a := .prop) ?_ ?_ ?_ ?_
  · simpa only [sortCode_zero] using approxTK_sort_code E n Γ ρ .zero
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    obtain rfl := List.mem_singleton.mp hu
    rw [CTyS]
    exact Or.inr (.pi .bot (fun _ hs => (List.not_mem_nil _ hs).elim))
  · exact ⟨([.pi .bot []], .pi .bot []), List.mem_singleton.mpr rfl,
      fun h => CptT.noConfusion h⟩
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact (approxTK_bvar_iff 0 (.pi .bot [])).mpr
      (Or.inr (List.mem_singleton.mpr rfl))

/-- This type is already normal for CK2; the alias remains in its domain. -/
theorem covNormAliasPi_normal (n : Nat) (A B : Expr Nat) :
    NormalR (WhStepCK2 eqEnvT n) eqGapCtx (covNormAliasPi A B) :=
  normalR_piCK2 eqGapCtx (eqGapDirectAlias A B) (.sort .zero)

/-- The relation needs the alias's native sort typing to form its binder
context. Its only recursive row is supplied by the row's own demanded
relation, transported along the concrete alias readback and beta-expanded. -/
theorem covNormAliasIdentity_core (C : CovTyping eqEnvT) (n : Nat)
    (A B : Expr Nat)
    (hA : HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort (.succ .zero))) :
    LRSCoreCov C (WhStepCK2 eqEnvT n) n eqGapCtx
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  rw [covNormAliasIdentityCpt, LRSCoreCov.eq_def]
  refine ⟨eqGapDirectAlias A B, .sort .zero, .refl _,
    ⟨.assumption eqGapCtx (eqGapDirectAlias A B) (.succ .zero) hΓ hA⟩, ?_⟩
  intro s hs N N' hN hN' hconv hrel
  obtain rfl := List.mem_singleton.mp hs
  have hd := hrel (.pi .bot []) (List.mem_singleton.mpr rfl)
  have hd' := lrSCoreCov_sortIdx_irrel C (readbackLaws_whStepCK2 eqEnvT n)
    (normalUniqueR_whStepCK2 pinEqGroupWfT)
    ⟨.zero, eqGapAlias_type_read n A B⟩ ⟨.zero, .refl _⟩ (.pi .bot []) hd
  exact lrSCoreCov_expand_red_both C (readbackLaws_whStepCK2 eqEnvT n)
    (redR_single ((readbackLaws_whStepCK2 eqEnvT n).beta eqGapCtx
      (.sort .zero) (.bvar 0) N))
    (redR_single ((readbackLaws_whStepCK2 eqEnvT n).beta eqGapCtx
      (.sort .zero) (.bvar 0) N')) (.pi .bot []) hd'

/-- Every model observation of the normal Pi type has a bottom domain.
Only the imported Pi inversion and the actual alias observation theorem
are used; no backward model observation is assumed. -/
theorem covNormAliasPi_observation_shape (n : Nat) (Ξ : LCtx) (ρ : EnvT)
    (A B : Expr Nat) {a : CptT}
    (ha : ApproxTK eqEnvT n Ξ ρ (covNormAliasPi A B) a) :
    a = .bot ∨ ∃ f, a = .pi .bot f := by
  rcases approxTK_pi_inv ha with hbot | ⟨d, f, heq, hD, _⟩
  · exact Or.inl hbot
  · have hd := approxTK_eqGapDirectAlias_bot A B hD
    subst d
    exact Or.inr ⟨f, heq⟩

/-- The normal type cannot realize the actual identity compact for any
admissible compact typing, including an implementation allowing Pi spines. -/
theorem not_elTCovP_covNormAliasPi (C : CovTyping eqEnvT) (n : Nat)
    (Ξ : LCtx) (ρ : EnvT) (A B : Expr Nat) :
    ¬ ElTCovP C (ctxModelT_approxTK eqEnvT n Ξ) ρ
      (covNormAliasPi A B) covNormAliasIdentityCpt := by
  rintro ⟨a, ha, ht⟩
  rcases covNormAliasPi_observation_shape n Ξ ρ A B ha with hbot | ⟨f, heq⟩
  · subst a
    exact CptT.noConfusion (C.bot_inv ht)
  · subst a
    exact cov_lam_row_not_bot_domain C f ht

/-- Normalization cannot repair a domain hidden under an already normal
Pi head. This negative result is uniform in the model valuation and typing. -/
theorem not_normalizedCovRealization_covNormAliasPi (C : CovTyping eqEnvT)
    (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    ¬ NormalizedCovRealization C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) eqGapCtx ρ (covNormAliasPi A B)
      covNormAliasIdentityCpt := by
  intro h
  exact not_elTCovP_covNormAliasPi C n eqGapCtx ρ A B
    ((normalizedCovRealization_iff_at_normal C
      (ctxModelT_approxTK eqEnvT n eqGapCtx) (covNormAliasPi_normal n A B)).mp h)

/-- Actual native witnesses: the Eq alias is a type of level one, and Pi
congruence converts the annotated identity's domain from `Sort 0` to that
alias. The two conversion children are native derivations. -/
theorem covNormAliasIdentity_native (n : Nat) :
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx
        (eqGapDirectAlias A B) (.sort (.succ .zero))) ∧
      Nonempty (HasTyT eqEnvT n eqGapCtx
        covNormAliasIdentity (covNormAliasPi A B)) := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨A, B, _, ⟨hβ⟩, _⟩ := eqGapDirectAlias_native_beta_control n
  obtain ⟨hg⟩ := eqGap_conv n
  have hc : ConvT eqEnvT n eqGapCtx (.sort .zero) (eqGapDirectAlias A B)
      (.sort (.succ .zero)) :=
    .trans eqGapCtx (.sort .zero) eqGapRedex (eqGapDirectAlias A B)
      (.sort (.succ .zero)) hg (.symm _ _ _ _ hβ)
  have hA : HasTyT eqEnvT n eqGapCtx (eqGapDirectAlias A B) (.sort (.succ .zero)) :=
    (convEnds pinEqGroupWfT hΓ hc).2.1
  have hb : HasTyT eqEnvT n (.assumption (.sort .zero) :: eqGapCtx)
      (.bvar 0) (.sort .zero) := .bvar _ 0 _ rfl
  have hx : HasTyT eqEnvT n eqGapCtx covNormAliasIdentity
      (.pi (.sort .zero) (.sort .zero)) :=
    .lam eqGapCtx (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero) (.sort _ _) hb
  have hp : ConvT eqEnvT n eqGapCtx (.pi (.sort .zero) (.sort .zero))
      (covNormAliasPi A B) (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .pi eqGapCtx (.sort .zero) (eqGapDirectAlias A B) (.sort .zero) (.sort .zero)
      (.succ .zero) (.succ .zero) hc (.refl _ _ _ (.sort _ _))
  exact ⟨A, B, ⟨hA⟩, ⟨.conv eqGapCtx covNormAliasIdentity
    (.pi (.sort .zero) (.sort .zero)) (covNormAliasPi A B)
    (.imax (.succ .zero) (.succ .zero)) hx hp⟩⟩

/-- All strongest escape guards coexist at the actual normal type. The two
term endpoints coincide, so the displayed native typing and observation
supply both endpoint premises independently. -/
theorem covNormAliasPi_escape_counterexample (C : CovTyping eqEnvT) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx covNormAliasIdentity (covNormAliasPi A B)) ∧
      Nonempty (HasTyT eqEnvT n eqGapCtx (covNormAliasPi A B)
        (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot covNormAliasIdentity covNormAliasIdentityCpt ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot (covNormAliasPi A B) (.pi .bot []) ∧
      NormalR (WhStepCK2 eqEnvT n) eqGapCtx (covNormAliasPi A B) ∧
      LRSCoreCov C (WhStepCK2 eqEnvT n) n eqGapCtx
        covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
        covNormAliasIdentityCpt ∧
      covNormAliasIdentityCpt ≠ .bot ∧
      (.pi .bot [] : CptT) ≠ .bot ∧
      ¬ NormalizedCovRealization C (ctxModelT_approxTK eqEnvT n eqGapCtx)
        (WhStepCK2 eqEnvT n) eqGapCtx EnvT.bot (covNormAliasPi A B)
        covNormAliasIdentityCpt := by
  obtain ⟨A, B, ⟨hA⟩, hx⟩ := covNormAliasIdentity_native n
  exact ⟨⟨pinEqGroupWfT⟩, eqGapCtx_wf n, envTypedCovAtP_eqGap_bot C n,
    A, B, hx,
    ⟨.pi eqGapCtx (eqGapDirectAlias A B) (.succ .zero) (.sort .zero)
      (.succ .zero) hA (.sort _ _)⟩,
    covNormAliasIdentity_approxTK eqEnvT n eqGapCtx EnvT.bot,
    approxTK_pi_bot_nil eqEnvT n eqGapCtx EnvT.bot (eqGapDirectAlias A B) (.sort .zero),
    covNormAliasPi_normal n A B, covNormAliasIdentity_core C n A B hA,
    (fun h => CptT.noConfusion h), (fun h => CptT.noConfusion h),
    not_normalizedCovRealization_covNormAliasPi C n EnvT.bot A B⟩

/-- The strongest guarded normalized escape fails uniformly in `CovTyping`.
Both native endpoint typings and both actual observations are supplied.
This obstruction does not concern rigid-spine compact typing. -/
theorem not_normalizedCovEscape_covNormAliasPi (C : CovTyping eqEnvT) (n : Nat) :
    ¬ NormalizedCovEscape C n := by
  intro h
  obtain ⟨⟨hW⟩, ⟨hΓ⟩, hρ, A, B, ⟨hx⟩, _, hm, _, _, hr, _, _, hno⟩ :=
    covNormAliasPi_escape_counterexample C n
  exact hno (h hW hΓ hx hx hρ hm hm hr)

/-- The repaired rigid-spine typing satisfies inclusion and nevertheless
has the actual normal-Pi counterexample in the fixed model. -/
theorem C2_normalized_escape_refuted (n : Nat) :
    CovTypingIncludesS (C2 eqEnvT) ∧ ¬ NormalizedCovEscape (C2 eqEnvT) n :=
  ⟨C2_includesS eqEnvT, not_normalizedCovEscape_covNormAliasPi (C2 eqEnvT) n⟩

/-- At the original raw alias itself, normalization still succeeds. The
new counterexample is its occurrence below a Pi head; the imported positive
alias theorem and the new normal-Pi refutation therefore coexist. -/
theorem alias_normalization_boundary (C : CovTyping eqEnvT)
    (hS : CovTypingIncludesS C) (n : Nat) (ρ : EnvT) (A B : Expr Nat) :
    NormalizedCovRealization C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) eqGapCtx ρ (eqGapDirectAlias A B) (.pi .bot []) ∧
    ¬ NormalizedCovRealization C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) eqGapCtx ρ (covNormAliasPi A B)
      covNormAliasIdentityCpt :=
  ⟨normalizedCovRealization_eqGapAlias C hS n ρ A B,
    not_normalizedCovRealization_covNormAliasPi C n ρ A B⟩

/-- Local normalized typing at precisely the given native context and the
same valuation as the source term observation. This predicate does not
identify that valuation with either target environment of a substitution. -/
def LocalNormalizedTyAtCov {E : ResolvedEnv} (C : CovTyping E) (M : CtxModelT E)
    (R : Readback) (Γ : LCtx) (e A : Expr Nat) : Prop :=
  ∀ {ρ : EnvT} {c : CptT}, EnvTypedCovAtP C M Γ ρ → M.Ap ρ e c →
    NormalizedCovRealization C M R Γ ρ A c

/-- An explicit strengthened typing motive: the existing relation motive
is retained verbatim, and local normalized typing is an additional conjunct.
The additional conjunct uses source context `Γ` and source valuation `ρ`;
the original motive retains all of its distinct target contexts, paired
valuations, and substitutions. This definition supplies neither conjunct. -/
def NormalizedFundTyAtCov {E : ResolvedEnv} (C : CovTyping E) (M : CtxModelT E)
    (R : Readback) (n : Nat) (Γ : LCtx) (e A : Expr Nat) : Prop :=
  FundTyAtCov C M R n Γ e A ∧ LocalNormalizedTyAtCov C M R Γ e A

/-- The exact global strengthening at one fixed model: the typing branch
requests `NormalizedFundTyAtCov`, and the conversion branch is unchanged. -/
def NormalizedFundamentalCovAt {E : ResolvedEnv} (C : CovTyping E) (M : CtxModelT E)
    (R : Readback) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {e A : Expr Nat},
    HasTyT E n Γ e A → NormalizedFundTyAtCov C M R n Γ e A) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b A : Expr Nat},
    ConvT E n Γ a b A → FundConvAtCov C M R n Γ a b A)

/-- A fixed-model normalized typing claim before any relation premise is
requested. Native environment and context admission, source typing, actual
source observation, and the coherent environment guard all remain inputs. -/
def GuardedNormalizedCovTyping {E : ResolvedEnv} (C : CovTyping E) (n : Nat) : Prop :=
  EnvWfT E → ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {e A : Expr Nat},
    HasTyT E n Γ e A →
    LocalNormalizedTyAtCov C (ctxModelT_approxTK E n Γ) (WhStepCK2 E n) Γ e A

/-- The local normalized typing conjunct already fails at the actual
source model and valuation. No relation-motive supplier is assumed. -/
theorem not_localNormalizedTyAtCov_covNormAliasPi (C : CovTyping eqEnvT)
    (n : Nat) (A B : Expr Nat) :
    ¬ LocalNormalizedTyAtCov C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) eqGapCtx covNormAliasIdentity (covNormAliasPi A B) := by
  intro h
  exact not_normalizedCovRealization_covNormAliasPi C n EnvT.bot A B
    (h (envTypedCovAtP_eqGap_bot C n)
      (covNormAliasIdentity_approxTK eqEnvT n eqGapCtx EnvT.bot))

/-- The exact strengthened typing motive is refuted by its local typing
projection; this does not refute the original relation-only motive. -/
theorem not_normalizedFundTyAtCov_covNormAliasPi (C : CovTyping eqEnvT)
    (n : Nat) (A B : Expr Nat) :
    ¬ NormalizedFundTyAtCov C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) n eqGapCtx covNormAliasIdentity (covNormAliasPi A B) :=
  fun h => not_localNormalizedTyAtCov_covNormAliasPi C n A B h.2

/-- The admitted Eq fixture refutes guarded normalized native typing even
without asking for a relation premise; both normality and an actual
non-bottom type observation are present in the displayed control above. -/
theorem not_guardedNormalizedCovTyping_eq (C : CovTyping eqEnvT) (n : Nat) :
    ¬ GuardedNormalizedCovTyping C n := by
  intro h
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨A, B, _, ⟨hx⟩⟩ := covNormAliasIdentity_native n
  exact not_localNormalizedTyAtCov_covNormAliasPi C n A B
    (h pinEqGroupWfT hΓ hx)

/-- The new normalized Fundamental target is false at the actual fixed
model context. The native typing is constructed before this global claim
is instantiated; no substitution or model-soundness assumption is added. -/
theorem not_normalizedFundamentalCovAt_eq (C : CovTyping eqEnvT) (n : Nat) :
    ¬ NormalizedFundamentalCovAt C (ctxModelT_approxTK eqEnvT n eqGapCtx)
      (WhStepCK2 eqEnvT n) n := by
  intro h
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨A, B, _, ⟨hx⟩⟩ := covNormAliasIdentity_native n
  exact not_normalizedFundTyAtCov_covNormAliasPi C n A B (h.1 hΓ hx)

/-- The concrete repaired typing includes `CTyS`, but neither local
normalized native typing nor the exact strengthened Fundamental target is
a supplier at the fixed Eq model. -/
theorem C2_normalized_typing_and_fundamental_refuted (n : Nat) :
    CovTypingIncludesS (C2 eqEnvT) ∧
      (¬ GuardedNormalizedCovTyping (C2 eqEnvT) n) ∧
      ¬ NormalizedFundamentalCovAt (C2 eqEnvT)
        (ctxModelT_approxTK eqEnvT n eqGapCtx) (WhStepCK2 eqEnvT n) n :=
  ⟨C2_includesS eqEnvT, not_guardedNormalizedCovTyping_eq (C2 eqEnvT) n,
    not_normalizedFundamentalCovAt_eq (C2 eqEnvT) n⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_NORM_ESCAPE_ROOTS
#print axioms covNormAliasIdentity
#print axioms covNormAliasIdentityCpt
#print axioms covNormAliasPi
#print axioms not_covNormAliasIdentityCpt_pi_bot
#print axioms covNormAliasIdentity_approxTK
#print axioms covNormAliasPi_normal
#print axioms covNormAliasIdentity_core
#print axioms covNormAliasPi_observation_shape
#print axioms not_elTCovP_covNormAliasPi
#print axioms not_normalizedCovRealization_covNormAliasPi
#print axioms covNormAliasIdentity_native
#print axioms covNormAliasPi_escape_counterexample
#print axioms not_normalizedCovEscape_covNormAliasPi
#print axioms C2_normalized_escape_refuted
#print axioms alias_normalization_boundary
#print axioms LocalNormalizedTyAtCov
#print axioms NormalizedFundTyAtCov
#print axioms NormalizedFundamentalCovAt
#print axioms GuardedNormalizedCovTyping
#print axioms not_localNormalizedTyAtCov_covNormAliasPi
#print axioms not_normalizedFundTyAtCov_covNormAliasPi
#print axioms not_guardedNormalizedCovTyping_eq
#print axioms not_normalizedFundamentalCovAt_eq
#print axioms C2_normalized_typing_and_fundamental_refuted
-- END RCIC_NATIVE_TYPED_MODEL_COV_NORM_ESCAPE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovNormEscapeAudit
