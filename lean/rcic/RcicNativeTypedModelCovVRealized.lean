import rcic.RcicNativeTypedModelCovVAligned
import rcic.RcicNativeTypedModelCovURealized

/-!
# Realized valuations for the native-K-aligned model

Stages retain the landed finite compact budget. Simultaneous substitution
recurses on the finite aligned derivation and preserves its native eligibility
premise. The K-free introduction is explicit; general guarded-K substitution
is not assumed. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit TypedModelKTransportAudit
open TypedModelCovTAudit

/-- Native universe arity and finite compact budget remain separate. -/
def ApproxTKNStage (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvT) (e : Expr Nat) (c : CptT) : Prop :=
  ApproxTKN E arity Γ ρ e c ∧ covTObservationBudget c ≤ stage

theorem ApproxTKNStage.mono {E : ResolvedEnv} {arity k l : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTKNStage E arity k Γ ρ e c) (hkl : k ≤ l) :
    ApproxTKNStage E arity l Γ ρ e c := ⟨h.1, Nat.le_trans h.2 hkl⟩

theorem approxTKNStage_bot (E : ResolvedEnv) (arity stage : Nat)
    (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) :
    ApproxTKNStage E arity stage Γ ρ e .bot :=
  ⟨.bot _ _ _, by simp [covTObservationBudget]⟩

theorem covV_stage_of_native_heads {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (hE : CovVPropHeadsNative E) (h : ApproxTKStage E arity stage Γ ρ e c) :
    ApproxTKNStage E arity stage Γ ρ e c :=
  ⟨covV_approxTK_of_native_heads hE h.1, h.2⟩

/-- Constructive lifting preserves the same native recursor certificate. -/
theorem covV_approxTN_lift_intro {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTN E ρ e c) :
    ∀ (k : Nat) (S : CptT → Prop), ApproxTN E (EnvT.insert ρ k S) (lift k 1 e) c := by
  induction h with
  | bot => intro k S; exact .bot _ _
  | @bvar ρ i c h =>
      intro k S
      simp only [lift]
      by_cases hk : k ≤ i
      · rw [if_pos hk]
        refine .bvar ?_
        simp only [EnvT.insert]
        rw [if_neg (by omega), if_neg (by omega)]
        simpa using h
      · rw [if_neg hk]
        refine .bvar ?_
        simp only [EnvT.insert]
        rw [if_pos (by omega)]
        exact h
  | sort => intro k S; exact .sort _ _
  | pi _ hT _ ihA ihf =>
      intro k S
      simp only [lift]
      refine .pi (ihA k S) hT (fun s hs => ?_)
      rw [EnvT.cons_insert]
      exact ihf s hs (k + 1) S
  | lam _ hT hnt _ ihA ihb =>
      intro k S
      simp only [lift]
      refine .lam (ihA k S) hT hnt (fun s hs => ?_)
      rw [EnvT.cons_insert]
      exact ihb s hs (k + 1) S
  | app _ hs _ ihf iha =>
      intro k S
      simp only [lift]
      exact .app (ihf k S) hs (fun u hu => iha u hu k S)
  | const _ _ _ hrigid hnp => intro k S; simp only [lift]; exact .const _ _ _ hrigid hnp
  | delta hd h _ => intro k S; simp only [lift]; exact .delta hd h
  | recursor ls hnp hpre hflds h _ => intro k S; simp only [lift]; exact .recursor ls hnp hpre hflds h
  | recursorProp ls hP hn hpre h _ => intro k S; simp only [lift]; exact .recursorProp ls hP hn hpre h
  | appSpine _ _ ihf iha =>
      intro k S
      simp only [lift]
      exact .appSpine (ihf k S) (iha k S)
  | letE _ ih =>
      intro k S
      simp only [lift]
      exact .letE (by simpa [lift] using ih k S)
  | lit _ ih =>
      intro k S
      simp only [lift]
      exact .lit (by simpa [natExpand_lift] using ih k S)

/-- A closed native realization of every demanded observation of a valuation.
The typing field also preserves local definitions, via `TypedSubstT`'s second
conjunct.  No realization is selected from an existential statement. -/
structure CovVRealized (E : ResolvedEnv) (arity stage : Nat) (Γ : LCtx)
    (ρ : EnvT) (σ : SubstT) : Prop where
  typing : TypedSubstT E arity [] σ Γ
  observed : ∀ (i : Nat) (c : CptT), ρ i c →
    ApproxTKNStage E arity stage [] EnvT.bot (σ i) c

/-- The same native images realize the valuation at any larger information stage. -/
theorem CovVRealized.mono {E : ResolvedEnv} {arity stage stage' : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT}
    (h : CovVRealized E arity stage Γ ρ σ) (hle : stage ≤ stage') :
    CovVRealized E arity stage' Γ ρ σ :=
  ⟨h.typing, fun i c hc => (h.observed i c hc).mono hle⟩

/-- Semantic simultaneous substitutions extend under a binder without choice. -/
theorem covV_approxTN_substT_up {E : ResolvedEnv} {ρ τ : EnvT} {σ : SubstT}
    (hσ : ∀ i c, ρ i c → ApproxTN E τ (σ i) c) (S : CptT → Prop) :
    ∀ i c, EnvT.cons S ρ i c →
      ApproxTN E (EnvT.cons S τ) (σ.up i) c := by
  intro i c h
  cases i with
  | zero => exact .bvar h
  | succ i =>
      have hh := covV_approxTN_lift_intro (hσ i c h) 0 S
      simpa only [EnvT.insert_zero] using hh

/-- Forward simultaneous substitution, proved on the finite observation
derivation.  Recursor schemas remain in their own closed semantic environment. -/
theorem covV_approxTN_substT {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTN E ρ e c) :
    ∀ (σ : SubstT) (τ : EnvT),
      (∀ i u, ρ i u → ApproxTN E τ (σ i) u) →
      ApproxTN E τ (substT σ e) c := by
  induction h with
  | bot => intro σ τ _; exact .bot _ _
  | bvar h => intro σ τ hσ; exact hσ _ _ h
  | sort => intro σ τ _; exact .sort _ _
  | pi _ hT _ ihA ihf =>
      intro σ τ hσ
      exact .pi (ihA σ τ hσ) hT
        (fun s hs => ihf s hs σ.up (EnvT.cons (demandT s.1) τ)
          (covV_approxTN_substT_up hσ _))
  | lam _ hT hnt _ ihA ihb =>
      intro σ τ hσ
      exact .lam (ihA σ τ hσ) hT hnt
        (fun s hs => ihb s hs σ.up (EnvT.cons (demandT s.1) τ)
          (covV_approxTN_substT_up hσ _))
  | app _ hs _ ihf iha =>
      intro σ τ hσ
      exact .app (ihf σ τ hσ) hs (fun u hu => iha u hu σ τ hσ)
  | const _ _ _ hrigid hnp => intro σ τ _; exact .const _ _ _ hrigid hnp
  | delta hdelta h _ => intro σ τ _; exact .delta hdelta h
  | recursor ls hnp hpre hflds h _ =>
      intro σ τ _; exact .recursor ls hnp hpre hflds h
  | recursorProp ls hP hn hpre h _ =>
      intro σ τ _; exact .recursorProp ls hP hn hpre h
  | appSpine _ _ ihf iha =>
      intro σ τ hσ
      exact .appSpine (ihf σ τ hσ) (iha σ τ hσ)
  | letE _ ih =>
      intro σ τ hσ
      exact .letE (ih σ τ hσ)
  | lit _ ih =>
      intro σ τ hσ
      exact .lit (by simpa only [substT_natExpand] using ih σ τ hσ)

/-- Realized valuations transport an aligned-model observation to the closed
native instance at exactly the same compact. -/
theorem CovVRealized.approxTN {E : ResolvedEnv} {arity stage : Nat} {Γ : LCtx}
    {ρ : EnvT} {σ : SubstT} (hσ : CovVRealized E arity stage Γ ρ σ)
    {e : Expr Nat} {c : CptT} (h : ApproxTN E ρ e c) :
    ApproxTN E EnvT.bot (substT σ e) c :=
  covV_approxTN_substT h σ EnvT.bot
    (fun i u hi => approxTKN_forgetN (hσ.observed i u hi).1)

/-- K-free forward transport from an actual multi-variable realizer. -/
theorem CovVRealized.approxTKN_of_kFree {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT}
    (hσ : CovVRealized E arity stage Γ ρ σ)
    {e : Expr Nat} {c : CptT} (hfree : KFreeT E (substT σ e))
    (h : ApproxTKN E arity Γ ρ e c) :
    ApproxTKN E arity [] EnvT.bot (substT σ e) c :=
  .free hfree (hσ.approxTN (approxTKN_forgetN h))

/-- The output observation budget is unchanged by the same transport. -/
theorem CovVRealized.stage_of_kFree {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT}
    (hσ : CovVRealized E arity stage Γ ρ σ)
    {e : Expr Nat} {c : CptT} (hfree : KFreeT E (substT σ e))
    (h : ApproxTKNStage E arity stage Γ ρ e c) :
    ApproxTKNStage E arity stage [] EnvT.bot (substT σ e) c :=
  ⟨hσ.approxTKN_of_kFree hfree h.1, h.2⟩

/-- Bottom observations require no evaluation, but still require an actual
native typed substitution. -/
theorem covV_realized_bot_of_typed {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {σ : SubstT} (hσ : TypedSubstT E arity [] σ Γ) :
    CovVRealized E arity stage Γ EnvT.bot σ := by
  refine ⟨hσ, ?_⟩
  intro i c hc
  cases hc
  exact approxTKNStage_bot E arity stage [] EnvT.bot (σ i)

/-- Every closed fixture at the bottom valuation has this explicit realizer. -/
theorem covV_realized_nil (E : ResolvedEnv) (arity stage : Nat) :
    CovVRealized E arity stage [] EnvT.bot SubstT.id := by
  apply covV_realized_bot_of_typed
  constructor
  · intro i A hi
    simp [lookupType] at hi
  · intro i v hi
    simp [lookupValue] at hi


/-- No native images are selected: reuse an explicitly supplied old realizer. -/
theorem covV_realized_of_native_heads {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT} (hE : CovVPropHeadsNative E)
    (hσ : CovTRealized E arity stage Γ ρ σ) :
    CovVRealized E arity stage Γ ρ σ :=
  ⟨hσ.typing, fun i c hc => covV_stage_of_native_heads hE (hσ.observed i c hc)⟩

/-- The new realizer remains an actual closed native realization. -/
theorem CovVRealized.forget {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {σ : SubstT} (hσ : CovVRealized E arity stage Γ ρ σ) :
    CovTRealized E arity stage Γ ρ σ :=
  ⟨hσ.typing, fun i c hc => ⟨approxTKN_forget (hσ.observed i c hc).1,
    (hσ.observed i c hc).2⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_REALIZED_ROOTS
#print axioms ApproxTKNStage
#print axioms ApproxTKNStage.mono
#print axioms approxTKNStage_bot
#print axioms covV_stage_of_native_heads
#print axioms covV_approxTN_lift_intro
#print axioms CovVRealized
#print axioms CovVRealized.mono
#print axioms covV_approxTN_substT_up
#print axioms covV_approxTN_substT
#print axioms CovVRealized.approxTN
#print axioms CovVRealized.approxTKN_of_kFree
#print axioms CovVRealized.stage_of_kFree
#print axioms covV_realized_bot_of_typed
#print axioms covV_realized_nil
#print axioms covV_realized_of_native_heads
#print axioms CovVRealized.forget
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_REALIZED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit
