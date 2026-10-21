import rcic.RcicNativeTypedModelCovRelSubst
import rcic.RcicNativeTypedModelCovPropagation

/-!
# Raw type realization is not an escape theorem of the new recursive core

The Eq function-variable alias is used as a TYPE.  It is natively
convertible to `Sort 0` and reads back to that sort, but its unchanged
`ApproxTK` interpretation contains only bottom.  The existing closed
proposition `idPiProp` is natively typed at this alias and is self-related
at the non-bottom probe `pi bot []`.  No compact typing with bottom
inversion can realize that probe at the raw alias type.

This obstruction is parametric in `CovTyping`; accepting rigid spines at
Pi types cannot remove it.  It refutes the requested unconditional raw
model escape even with native typing, actual model observations and the
coherent two-sided environment guard retained.  No backward model law is
assumed, and no new recursive-relation definition is weakened here.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelKAudit TypedModelKFailureAudit TypedModelKControlAudit TypedModelKTypedBetaAudit TypedModelCovKAudit
open TypedModelCovPropagationAudit TypedModelCovRelBoundaryAudit TypedModelCovRelAudit

/-- The actual CK2 readback at the type alias, including its outer beta step. -/
theorem eqGapAlias_type_read (n : Nat) (A B : Expr Nat) :
    RedR (WhStepCK2 eqEnvT n) eqGapCtx (eqGapDirectAlias A B) (.sort .zero) :=
  .step ((readbackLaws_whStepCK2 eqEnvT n).beta eqGapCtx (.pi A B)
    (.app (.bvar 0) (.bvar 1)) eqGapPrefix) (redR_whStepCK2_eqGap n)

/-- At bottom valuations, the actual assumption-only Eq context is coherently
typed for every compact typing with its required bottom introduction. -/
theorem envTypedCovAtP_eqGap_bot (C : CovTyping eqEnvT) (n : Nat) :
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot := by
  refine ⟨?_, (envTypedCovAtM_eqGap_bot n).2⟩
  intro i A hA u hu
  change u = .bot at hu
  subst u
  exact ⟨.bot, ApproxTK.bot _ _ _, C.bot .bot⟩

/-- The Pi probe's relation needs only the native alias readback; its domain
probe is bottom and its row list is empty. -/
theorem idPiProp_covRel_at_alias (C : CovTyping eqEnvT) (n : Nat) (A B : Expr Nat) :
    LRSCoreCov C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
      (eqGapDirectAlias A B) (.pi .bot []) := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  rw [LRSCoreCov.eq_def]
  refine ⟨⟨.zero, eqGapAlias_type_read n A B⟩, .sort .zero, .bvar 0,
    .sort .zero, .bvar 0, .refl _, .refl _,
    ⟨.assumption eqGapCtx (.sort .zero) (.succ .zero) hΓ (.sort _ _)⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩,
    ⟨.succ .zero, lrSCoreCov_bot C _ _ _ _⟩, ?_⟩
  intro s hs
  exact (List.not_mem_nil _ hs).elim

/-- The raw alias has no type observation that can type a non-bottom compact,
uniformly in native model context and valuation. -/
theorem not_elTCovP_at_eqGapAlias (C : CovTyping eqEnvT) (n : Nat)
    (Ξ : LCtx) (ρ : EnvT) (A B : Expr Nat) {c : CptT} (hc : c ≠ .bot) :
    ¬ ElTCovP C (ctxModelT_approxTK eqEnvT n Ξ) ρ (eqGapDirectAlias A B) c := by
  rintro ⟨a, ha, hty⟩
  have he := approxTK_eqGapDirectAlias_bot A B ha
  subst a
  exact hc (C.bot_inv hty)

/-- All native, model and relation premises of raw escape coexist.  The
failure is at the TYPE's observation, not at an unrealized term compact. -/
theorem alias_type_escape_counterexample (C : CovTyping eqEnvT) (n : Nat) :
    Nonempty (EnvWfT eqEnvT) ∧ Nonempty (CtxWfT eqEnvT n eqGapCtx) ∧
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n eqGapCtx) eqGapCtx EnvT.bot ∧
    ∃ A B : Expr Nat,
      Nonempty (HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B)) ∧
      ApproxTK eqEnvT n eqGapCtx EnvT.bot idPiProp (.pi .bot []) ∧
      LRSCoreCov C (WhStepCK2 eqEnvT n) n eqGapCtx idPiProp idPiProp
        (eqGapDirectAlias A B) (.pi .bot []) ∧
      ¬ ElTCovP C (ctxModelT_approxTK eqEnvT n eqGapCtx) EnvT.bot
        (eqGapDirectAlias A B) (.pi .bot []) := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨A, B, _, ⟨hβ⟩, _⟩ := eqGapDirectAlias_native_beta_control n
  obtain ⟨hg⟩ := eqGap_conv n
  have ht : HasTyT eqEnvT n eqGapCtx idPiProp (eqGapDirectAlias A B) :=
    .conv eqGapCtx idPiProp (.sort .zero) (eqGapDirectAlias A B) (.succ .zero)
      (apartLeft_ty n eqGapCtx)
      (.trans eqGapCtx (.sort .zero) eqGapRedex (eqGapDirectAlias A B)
        (.sort (.succ .zero)) hg (.symm _ _ _ _ hβ))
  exact ⟨⟨pinEqGroupWfT⟩, ⟨hΓ⟩, envTypedCovAtP_eqGap_bot C n,
    A, B, ⟨ht⟩, approxTK_pi_bot_nil eqEnvT n eqGapCtx EnvT.bot _ _,
    idPiProp_covRel_at_alias C n A B,
    not_elTCovP_at_eqGapAlias C n eqGapCtx EnvT.bot A B (fun h => CptT.noConfusion h)⟩

/-- The strongest guard set used in the counterexample still does not yield
raw model typing from the recursive relation.  Both term observations and
both native typings are required by this named port. -/
def RawCovEscape (C : CovTyping eqEnvT) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {ρ : EnvT} {x y A : Expr Nat} {c : CptT},
    CtxWfT eqEnvT n Γ → HasTyT eqEnvT n Γ x A → HasTyT eqEnvT n Γ y A →
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n Γ) Γ ρ →
    ApproxTK eqEnvT n Γ ρ x c → ApproxTK eqEnvT n Γ ρ y c →
    LRSCoreCov C (WhStepCK2 eqEnvT n) n Γ x y A c →
    ElTCovP C (ctxModelT_approxTK eqEnvT n Γ) ρ A c

theorem not_rawCovEscape (C : CovTyping eqEnvT) (n : Nat) : ¬ RawCovEscape C n := by
  intro h
  obtain ⟨_, ⟨hΓ⟩, hρ, A, B, ⟨ht⟩, hm, hr, hno⟩ :=
    alias_type_escape_counterexample C n
  exact hno (h hΓ ht ht hρ hm hm hr)

/-- The same fixture refutes global typing before any recursive-relation
premise is requested. This stronger guard set includes native context
well-formedness and the actual coherent covariant semantic environment. -/
def GuardedCovTyping (C : CovTyping eqEnvT) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {ρ : EnvT} {x A : Expr Nat} {c : CptT},
    CtxWfT eqEnvT n Γ → HasTyT eqEnvT n Γ x A →
    EnvTypedCovAtP C (ctxModelT_approxTK eqEnvT n Γ) Γ ρ →
    ApproxTK eqEnvT n Γ ρ x c →
    ElTCovP C (ctxModelT_approxTK eqEnvT n Γ) ρ A c

theorem not_guardedCovTyping (C : CovTyping eqEnvT) (n : Nat) :
    ¬ GuardedCovTyping C n := by
  intro h
  obtain ⟨_, ⟨hΓ⟩, hρ, A, B, ⟨ht⟩, hm, _, hno⟩ :=
    alias_type_escape_counterexample C n
  exact hno (h hΓ ht hρ hm)

/-- Exact restatement at the original observation boundary: a model retaining
the observed term compact and only-bottom alias types cannot type this native
conversion, for any compact typing that retains bottom inversion. -/
theorem not_alias_covTyping_of_observations (C : CovTyping eqEnvT)
    (M : CtxModelT eqEnvT) (A B : Expr Nat)
    (hm : M.Ap EnvT.bot idPiProp (.pi .bot []))
    (hA : ∀ a, M.Ap EnvT.bot (eqGapDirectAlias A B) a → a = .bot) :
    ¬ (∀ c, M.Ap EnvT.bot idPiProp c →
      ElTCovP C M EnvT.bot (eqGapDirectAlias A B) c) := by
  intro h
  obtain ⟨a, ha, hty⟩ := h (.pi .bot []) hm
  obtain rfl := hA a ha
  exact CptT.noConfusion (C.bot_inv hty)

/-- The imported fixed-model global typing statement is refuted at Eq as
well; the argument does not depend on the separate rigid-spine Pi gap. -/
theorem not_typingLemmaEnvCovM_approxTK_eqEnv (n : Nat) :
    ¬ TypingLemmaEnvCovM (ctxModelT_approxTK eqEnvT n eqGapCtx) n := by
  intro h
  obtain ⟨_, _, hρ, A, B, ⟨ht⟩, hm, _, hno⟩ :=
    alias_type_escape_counterexample (covTypingCTyCov eqEnvT) n
  exact hno (h ht hρ (.pi .bot []) hm)

/-- The requested escape into the imported envelope already implies the
refuted raw typing projection at the current CTyCov instance. -/
theorem not_raw_covTypedEnvelope_escape (n : Nat) :
    ¬ (∀ {Γ : LCtx} {ρ : EnvT} {x y A : Expr Nat} {c : CptT},
      CtxWfT eqEnvT n Γ → HasTyT eqEnvT n Γ x A → HasTyT eqEnvT n Γ y A →
      EnvTypedCovAtM (ctxModelT_approxTK eqEnvT n Γ) Γ ρ →
      ApproxTK eqEnvT n Γ ρ x c → ApproxTK eqEnvT n Γ ρ y c →
      LRSCoreCov (covTypingCTyCov eqEnvT) (WhStepCK2 eqEnvT n) n Γ x y A c →
      CovTypedEnvelopeT (ctxModelT_approxTK eqEnvT n Γ) (WhStepCK2 eqEnvT n)
        n Γ ρ x y A c) := by
  intro h
  apply not_rawCovEscape (covTypingCTyCov eqEnvT) n
  intro Γ ρ x y A c hΓ hx hy hρ hmx hmy hr
  exact (h hΓ hx hy hρ hmx hmy hr).1

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_ESCAPE_ROOTS
#print axioms eqGapAlias_type_read
#print axioms envTypedCovAtP_eqGap_bot
#print axioms idPiProp_covRel_at_alias
#print axioms not_elTCovP_at_eqGapAlias
#print axioms alias_type_escape_counterexample
#print axioms RawCovEscape
#print axioms not_rawCovEscape
#print axioms GuardedCovTyping
#print axioms not_guardedCovTyping
#print axioms not_alias_covTyping_of_observations
#print axioms not_typingLemmaEnvCovM_approxTK_eqEnv
#print axioms not_raw_covTypedEnvelope_escape
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_ESCAPE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelEscapeAudit
