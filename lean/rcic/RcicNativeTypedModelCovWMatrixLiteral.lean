import rcic.RcicNativeTypedModelCovWIrrelFixtures

/-!
# Exact literal-head observations in the current grammar

Expanding a literal at the leftmost head preserves every raw and guarded
observation. The native typing helper strips `HasTyT.lit` and preserves
outer native conversions, including in a function position; it does not
assume that a literal cannot have a Pi type. This supplies the eta case of
the guarded derivation induction.

At the literal itself, the grammar's `lit` constructor supplies the reverse
direction, yielding equality of all observations. Under arbitrary trailing
applications the proved statement is only literal-to-expansion transport.
No app-argument or under-binder congruence is inferred. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKFragmentAudit TypedModelCovWIrrelAudit
open ReadbackCKAudit ReadbackCK2Audit

/-- Expand only a literal at the leftmost application head. Arguments and
all binder bodies are left unchanged. -/
def covWMatrixExpandHeadLit : Expr Nat → Expr Nat
  | .lit t => natExpand t
  | .app f x => .app (covWMatrixExpandHeadLit f) x
  | e => e

theorem covWMatrix_expandHead_foldApps (f : Expr Nat) (xs : List (Expr Nat)) :
    covWMatrixExpandHeadLit (foldApps f xs) =
      foldApps (covWMatrixExpandHeadLit f) xs := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

theorem covWMatrix_expandHead_lift (e : Expr Nat) (cutoff amount : Nat) :
    covWMatrixExpandHeadLit (lift cutoff amount e) =
      lift cutoff amount (covWMatrixExpandHeadLit e) := by
  induction e generalizing cutoff with
  | bvar i =>
      by_cases hi : cutoff ≤ i <;> simp [lift, covWMatrixExpandHeadLit, hi]
  | sort => rfl
  | const => rfl
  | app f x ihf ihx => simp only [lift, covWMatrixExpandHeadLit, ihf]
  | lam => rfl
  | pi => rfl
  | letE => rfl
  | lit t => exact (natExpand_lift cutoff amount t).symm

theorem covWMatrix_expandHead_occurs (r : Nat) (e : Expr Nat) :
    occursConst r (covWMatrixExpandHeadLit e) = occursConst r e := by
  induction e with
  | bvar => rfl
  | sort => rfl
  | const => rfl
  | app f x ihf ihx => simp only [covWMatrixExpandHeadLit, occursConst, ihf]
  | lam => rfl
  | pi => rfl
  | letE => rfl
  | lit t => exact litOccurs_natExpand r t

theorem covWMatrix_expandHead_kFree {E : ResolvedEnv} {e : Expr Nat}
    (h : KFreeT E e) : KFreeT E (covWMatrixExpandHeadLit e) :=
  kFreeT_support h (fun r hr => by
    simpa only [covWMatrix_expandHead_occurs] using hr)

/-- Every assigned native type is preserved. The literal arm returns the
actual expansion typing, and the conversion arm retains the native chain. -/
def covWMatrix_expandHead_hasTy {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A →
      HasTyT E n Γ (covWMatrixExpandHeadLit e) A
  | _, _, _, ht@(.sort _ _) => ht
  | _, _, _, ht@(.bvar _ _ _ _) => ht
  | _, _, _, ht@(.const _ _ _ _ _ _ _) => ht
  | _, _, _, ht@(.pi _ _ _ _ _ _ _) => ht
  | _, _, _, ht@(.lam _ _ _ _ _ _ _) => ht
  | Γ, _, _, .app _ f a A B hf ha =>
      .app Γ (covWMatrixExpandHeadLit f) a A B (covWMatrix_expandHead_hasTy hf) ha
  | _, _, _, ht@(.letE _ _ _ _ _ _ _ _ _) => ht
  | _, _, _, .lit _ _ _ hexp => hexp
  | Γ, _, _, .conv _ e A B u ht hc =>
      .conv Γ (covWMatrixExpandHeadLit e) A B u (covWMatrix_expandHead_hasTy ht) hc

theorem covWMatrix_raw_expandHead {E : ResolvedEnv} {n : Nat} {ρ : EnvWIrrel}
    {e : Expr Nat} {c : CptWIrrel} (h : ApproxTWIrrel E n ρ e c) :
    ApproxTWIrrel E n ρ (covWMatrixExpandHeadLit e) c := by
  induction h with
  | bot => exact .bot _ _
  | bvar h => exact .bvar h
  | sort ρ l => exact .sort ρ l
  | pi hA ht hb ihA ihb => exact .pi hA ht hb
  | lam hA ht hn hb ihA ihb => exact .lam hA ht hn hb
  | app hf hs ha ihf iha => exact .app ihf hs ha
  | const ρ r ls hr hn => exact .const ρ r ls hr hn
  | delta hd h ih => exact .delta hd h
  | recursor ls hn hp hf h ih => exact .recursor ls hn hp hf h
  | appSpine hf ha hs ihf iha => exact .appSpine ihf ha hs
  | letE h ih => exact .letE h
  | lit h ih => exact h

/-- Eta is handled by actual native typing transport and by the recursively
expanded fresh-variable application, without a no-Pi hypothesis. -/
theorem covWMatrix_guarded_expandHead {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWIrrel E n Γ ρ e c) :
    ApproxTKWIrrel E n Γ ρ (covWMatrixExpandHeadLit e) c := by
  induction h with
  | bot => exact .bot _ _ _
  | free hf h => exact .free (covWMatrix_expandHead_kFree hf) (covWMatrix_raw_expandHead h)
  | pi hA ht hb ihA ihb => exact .pi hA ht hb
  | lam hA ht hn hb ihA ihb => exact .lam hA ht hn hb
  | app hf hs ha ihf iha => exact .app ihf hs ha
  | appSpine hf ha hs ihf iha => exact .appSpine ihf ha hs
  | delta hd h ih => exact .delta hd h
  | letE h ih => exact .letE h
  | lit h ih => exact h
  | iota w hs hr ih =>
      simpa only [iotaLhsOfS, recCall, covWMatrix_expandHead_foldApps,
        covWMatrixExpandHeadLit] using ApproxTKWIrrel.iota w hs hr
  | recursorPropK w x hk hn hi hc hs hr ih =>
      simpa only [recCall, covWMatrix_expandHead_foldApps, covWMatrixExpandHeadLit] using
        ApproxTKWIrrel.recursorPropK w x hk hn hi hc hs hr
  | eta he hD ht hn hb ihD ihb =>
      refine .eta (covWMatrix_expandHead_hasTy he) hD ht hn ?_
      intro s hs
      simpa only [covWMatrixExpandHeadLit, covWMatrix_expandHead_lift] using ihb s hs

theorem covWMatrix_raw_literal_iff (E : ResolvedEnv) (n : Nat)
    (ρ : EnvWIrrel) (t : Nat) (c : CptWIrrel) :
    ApproxTWIrrel E n ρ (.lit t) c ↔ ApproxTWIrrel E n ρ (natExpand t) c :=
  ⟨covWMatrix_raw_expandHead, ApproxTWIrrel.lit⟩

theorem covWMatrix_guarded_literal_iff (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWIrrel) (t : Nat) (c : CptWIrrel) :
    ApproxTKWIrrel E n Γ ρ (.lit t) c ↔
      ApproxTKWIrrel E n Γ ρ (natExpand t) c :=
  ⟨covWMatrix_guarded_expandHead, ApproxTKWIrrel.lit⟩

theorem covWMatrix_literal_observation_iff (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : EnvWIrrel) (t : Nat) (c : CptT) :
    CovWIrrelObservation E n Γ ρ (.lit t) c ↔
      CovWIrrelObservation E n Γ ρ (natExpand t) c := by
  constructor
  · rintro ⟨d, he, hd⟩
    exact ⟨d, he, (covWMatrix_guarded_literal_iff E n Γ ρ t d).mp hd⟩
  · rintro ⟨d, he, hd⟩
    exact ⟨d, he, (covWMatrix_guarded_literal_iff E n Γ ρ t d).mpr hd⟩

/-- This function-position result is one-way, for arbitrary trailing arguments. -/
theorem covWMatrix_literal_appHead_transport {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvWIrrel} {t : Nat} {xs : List (Expr Nat)} {c : CptT}
    (h : CovWIrrelObservation E n Γ ρ (foldApps (.lit t) xs) c) :
    CovWIrrelObservation E n Γ ρ (foldApps (natExpand t) xs) c := by
  obtain ⟨d, he, hd⟩ := h
  refine ⟨d, he, ?_⟩
  simpa only [covWMatrix_expandHead_foldApps, covWMatrixExpandHeadLit] using
    covWMatrix_guarded_expandHead hd

theorem covWMatrix_literal_step (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (t : Nat) :
    WhStepCK2 E n Γ (.lit t) (natExpand t) := .ctx (.lit t)

def covWMatrix_literal_conversion {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {A : Expr Nat} (ht : HasTyT E n Γ (natExpand t) A) :
    ConvT E n Γ (.lit t) (natExpand t) A :=
  .lit Γ t (natExpand t) A (.of t) ht

/-- An actual closed literal supplies nonbottom information on both sides. -/
theorem covWMatrix_literal_one_supply (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.lit 1) (.const 0 [])) ∧
    Nonempty (ConvT natEnvU n [] (.lit 1) (natExpand 1) (.const 0 [])) ∧
    WhStepCK2 natEnvU n [] (.lit 1) (natExpand 1) ∧
    CovWIrrelRealized natEnvU n 1 [] EnvWIrrel.bot SubstT.id ∧
    CovWIrrelObservation natEnvU n [] EnvWIrrel.bot (.lit 1) (.spine 2 [.bot]) ∧
    CovWIrrelObservation natEnvU n [] EnvWIrrel.bot (natExpand 1) (.spine 2 [.bot]) := by
  have ht : HasTyT natEnvU n [] (natExpand 1) (.const 0 []) :=
    .app _ _ _ _ _ (.const _ 2 [] natSuccMember rfl rfl rfl)
      (.const _ 1 [] natZeroMember rfl rfl rfl)
  have ho : ApproxTKWIrrel natEnvU n [] EnvWIrrel.bot (natExpand 1)
      (.spine 2 [] [.bot]) :=
    covWIrrel_guarded_appSpine_bot (covWIrrel_succ_observed n [] EnvWIrrel.bot)
  exact ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, ⟨.lit [] 1 _ ht⟩,
    ⟨covWMatrix_literal_conversion ht⟩, covWMatrix_literal_step natEnvU n [] 1,
    covWIrrel_realized_nil natEnvU n 1,
    covWIrrel_observation_of (ApproxTKWIrrel.lit ho), covWIrrel_observation_of ho⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_LITERAL_ROOTS
#print axioms covWMatrixExpandHeadLit
#print axioms covWMatrix_expandHead_foldApps
#print axioms covWMatrix_expandHead_lift
#print axioms covWMatrix_expandHead_occurs
#print axioms covWMatrix_expandHead_kFree
#print axioms covWMatrix_expandHead_hasTy
#print axioms covWMatrix_raw_expandHead
#print axioms covWMatrix_guarded_expandHead
#print axioms covWMatrix_raw_literal_iff
#print axioms covWMatrix_guarded_literal_iff
#print axioms covWMatrix_literal_observation_iff
#print axioms covWMatrix_literal_appHead_transport
#print axioms covWMatrix_literal_step
#print axioms covWMatrix_literal_conversion
#print axioms covWMatrix_literal_one_supply
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_LITERAL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit
