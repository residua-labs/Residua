import rcic.RcicSubstTTyped
import rcic.RcicNativeTypedModelCovTSubstitution

/-!
# Closed native realizers of stage-bounded valuations

The semantic valuation is realized by an actual simultaneous native substitution
into the empty context.  Observations of its images are taken at `EnvT.bot`.
In particular the identity substitution under the original semantic valuation
does not inhabit this interface in general.  The semantic substitution theorem
below is a derivation induction and changes neither the compact nor its stage.
Only the final guarded-model introduction requires a K-free substituted term.

`closure_claim = 0`.  This module supplies neither observation soundness nor
general provenance views.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKTransportAudit

/-- A closed native realization of every demanded observation of a valuation.
The typing field also preserves local definitions, via `TypedSubstT`'s second
conjunct.  No realization is selected from an existential statement. -/
structure CovTRealized (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvT) (σ : SubstT) : Prop where
  typing : TypedSubstT E arity [] σ Γ
  observed : ∀ (i : Nat) (c : CptT), ρ i c →
    ApproxTKStage E arity stage [] EnvT.bot (σ i) c

/-- The same native images realize the valuation at any larger information stage. -/
theorem CovTRealized.mono {E : ResolvedEnv} {arity stage stage' : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT}
    (h : CovTRealized E arity stage Γ ρ σ) (hle : stage ≤ stage') :
    CovTRealized E arity stage' Γ ρ σ :=
  ⟨h.typing, fun i c hc => (h.observed i c hc).mono hle⟩

/-- Semantic simultaneous substitutions extend under a binder without choice. -/
theorem covU_approxT_substT_up {E : ResolvedEnv} {ρ τ : EnvT} {σ : SubstT}
    (hσ : ∀ i c, ρ i c → ApproxT E τ (σ i) c) (S : CptT → Prop) :
    ∀ i c, EnvT.cons S ρ i c →
      ApproxT E (EnvT.cons S τ) (σ.up i) c := by
  intro i c h
  cases i with
  | zero => exact .bvar h
  | succ i =>
      have hh := approxT_lift_intro (hσ i c h) 0 S
      simpa only [EnvT.insert_zero] using hh

/-- Forward simultaneous substitution, proved on the finite observation
derivation.  Recursor schemas remain in their own closed semantic environment. -/
theorem covU_approxT_substT {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxT E ρ e c) :
    ∀ (σ : SubstT) (τ : EnvT),
      (∀ i u, ρ i u → ApproxT E τ (σ i) u) →
      ApproxT E τ (substT σ e) c := by
  induction h with
  | bot => intro σ τ _; exact .bot _ _
  | bvar h => intro σ τ hσ; exact hσ _ _ h
  | sort => intro σ τ _; exact .sort _ _
  | pi _ hT _ ihA ihf =>
      intro σ τ hσ
      exact .pi (ihA σ τ hσ) hT
        (fun s hs => ihf s hs σ.up (EnvT.cons (demandT s.1) τ)
          (covU_approxT_substT_up hσ _))
  | lam _ hT hnt _ ihA ihb =>
      intro σ τ hσ
      exact .lam (ihA σ τ hσ) hT hnt
        (fun s hs => ihb s hs σ.up (EnvT.cons (demandT s.1) τ)
          (covU_approxT_substT_up hσ _))
  | app _ hs _ ihf iha =>
      intro σ τ hσ
      exact .app (ihf σ τ hσ) hs (fun u hu => iha u hu σ τ hσ)
  | const _ _ _ hrigid hnp => intro σ τ _; exact .const _ _ _ hrigid hnp
  | delta hdelta h _ => intro σ τ _; exact .delta hdelta h
  | recursor ls hnp hpre hflds h _ =>
      intro σ τ _; exact .recursor ls hnp hpre hflds h
  | recursorProp ls hP hpre h _ =>
      intro σ τ _; exact .recursorProp ls hP hpre h
  | appSpine _ _ ihf iha =>
      intro σ τ hσ
      exact .appSpine (ihf σ τ hσ) (iha σ τ hσ)
  | letE _ ih =>
      intro σ τ hσ
      exact .letE (ih σ τ hσ)
  | lit _ ih =>
      intro σ τ hσ
      exact .lit (by simpa only [substT_natExpand] using ih σ τ hσ)

/-- Realized valuations transport an old-model observation to the closed
native instance at exactly the same compact. -/
theorem CovTRealized.approxT {E : ResolvedEnv} {arity stage : Nat} {Γ : LCtx}
    {ρ : EnvT} {σ : SubstT} (hσ : CovTRealized E arity stage Γ ρ σ)
    {e : Expr Nat} {c : CptT} (h : ApproxT E ρ e c) :
    ApproxT E EnvT.bot (substT σ e) c :=
  covU_approxT_substT h σ EnvT.bot
    (fun i u hi => approxTK_forget (hσ.observed i u hi).1)

/-- K-free forward transport from an actual multi-variable realizer. -/
theorem CovTRealized.approxTK_of_kFree {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT}
    (hσ : CovTRealized E arity stage Γ ρ σ)
    {e : Expr Nat} {c : CptT} (hfree : KFreeT E (substT σ e))
    (h : ApproxTK E arity Γ ρ e c) :
    ApproxTK E arity [] EnvT.bot (substT σ e) c :=
  .free hfree (hσ.approxT (approxTK_forget h))

/-- The output observation budget is unchanged by the same transport. -/
theorem CovTRealized.stage_of_kFree {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT}
    (hσ : CovTRealized E arity stage Γ ρ σ)
    {e : Expr Nat} {c : CptT} (hfree : KFreeT E (substT σ e))
    (h : ApproxTKStage E arity stage Γ ρ e c) :
    ApproxTKStage E arity stage [] EnvT.bot (substT σ e) c :=
  ⟨hσ.approxTK_of_kFree hfree h.1, h.2⟩

/-- Bottom observations require no evaluation, but still require an actual
native typed substitution. -/
theorem covU_realized_bot_of_typed {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {σ : SubstT} (hσ : TypedSubstT E arity [] σ Γ) :
    CovTRealized E arity stage Γ EnvT.bot σ := by
  refine ⟨hσ, ?_⟩
  intro i c hc
  cases hc
  exact approxTKStage_bot E arity stage [] EnvT.bot (σ i)

/-- Every closed fixture at the bottom valuation has this explicit realizer. -/
theorem covU_realized_nil (E : ResolvedEnv) (arity stage : Nat) :
    CovTRealized E arity stage [] EnvT.bot SubstT.id := by
  apply covU_realized_bot_of_typed
  constructor
  · intro i A hi
    simp [lookupType] at hi
  · intro i v hi
    simp [lookupValue] at hi

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_U_REALIZED_ROOTS
#print axioms CovTRealized
#print axioms CovTRealized.mono
#print axioms covU_approxT_substT_up
#print axioms covU_approxT_substT
#print axioms CovTRealized.approxT
#print axioms CovTRealized.approxTK_of_kFree
#print axioms CovTRealized.stage_of_kFree
#print axioms covU_realized_bot_of_typed
#print axioms covU_realized_nil
-- END RCIC_NATIVE_TYPED_MODEL_COV_U_REALIZED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit
