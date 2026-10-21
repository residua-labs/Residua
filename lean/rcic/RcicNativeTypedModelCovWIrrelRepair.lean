import rcic.RcicNativeTypedModelCovWIrrelAligned
import rcic.RcicNativeTypedModelCovWIrrelPositionPins
import rcic.RcicNativeTypedModelCovWIrrelProofDemand

/-!
# Rigid proof-field erasure, including finite eta derivations

The head invariant below follows every finite eta alternative and every
graph application. It records the actual head's levels and the bottom
field at each native proof position. The concrete supplies repair the
proof-field beta/let examples and the old proof-demand application.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKFragmentAudit TypedModelCovUAudit TypedModelCovWAudit
open TypedModelCovWEtaAudit TypedModelCovSAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The syntax retains one exact constant head and counts its actual arguments. -/
inductive CovWIrrelHeadTerm (r : Nat) (ls : List Level) : Nat → Expr Nat → Prop
  | head : CovWIrrelHeadTerm r ls 0 (.const r ls)
  | app {k : Nat} {f x : Expr Nat} (hf : CovWIrrelHeadTerm r ls k f) :
      CovWIrrelHeadTerm r ls (k + 1) (.app f x)

theorem CovWIrrelHeadTerm.lift_one {r k : Nat} {ls : List Level} {e : Expr Nat}
    (h : CovWIrrelHeadTerm r ls k e) :
    CovWIrrelHeadTerm r ls k (lift 0 1 e) := by
  induction h with
  | head => exact .head
  | app _ ih => exact .app ih

theorem CovWIrrelHeadTerm.headConst {r k : Nat} {ls : List Level} {e : Expr Nat}
    (h : CovWIrrelHeadTerm r ls k e) : headConst e = some r := by
  induction h with
  | head => rfl
  | app _ ih => exact ih

private theorem headConst_fold (e : Expr Nat) (xs : List (Expr Nat)) :
    headConst (foldApps e xs) = headConst e := by
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih => exact ih (.app e x)

/-- Row outputs retain the same rigid head at the next application depth.
All proof positions in an emitted spine have already been erased. -/
def CovWIrrelHeadShape (E : ResolvedEnv) (n r : Nat) (ls : List Level)
    (k : Nat) (c : CptWIrrel) : Prop :=
  match c with
  | .bot => True
  | .spine r' ls' us => r' = r ∧ ls' = ls ∧ us.length = k ∧
      ∀ i (hi : i < us.length), CovWIrrelProofPosition E n r ls i → us[i] = .bot
  | .lam rows => ∀ s ∈ rows, CovWIrrelHeadShape E n r ls (k + 1) s.2
  | .prop => False
  | .sort => False
  | .pi _ _ => False
termination_by sizeOf c
decreasing_by
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ rows from ‹_›)
  have h₂ : sizeOf s.2 < sizeOf s := by cases s; simp; omega
  simp_wf
  omega

private theorem headShape_append {E : ResolvedEnv} {n r r' k : Nat}
    {ls ls' : List Level} {us : List CptWIrrel} {u : CptWIrrel}
    (h : CovWIrrelHeadShape E n r ls k (.spine r' ls' us))
    (hp : CovWIrrelProofPosition E n r' ls' us.length → u = .bot) :
    CovWIrrelHeadShape E n r ls (k + 1) (.spine r' ls' (us ++ [u])) := by
  rw [CovWIrrelHeadShape] at h ⊢
  obtain ⟨rfl, rfl, hk, hh⟩ := h
  refine ⟨rfl, rfl, by simp [hk], ?_⟩
  intro i hi hiP
  by_cases hl : i < us.length
  · simpa only [List.getElem_append_left hl] using hh i hl hiP
  · have he : i = us.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hp hiP

theorem covWIrrel_raw_head_shape {E : ResolvedEnv} {n r k : Nat}
    {ls : List Level} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (hr : RigidConst E r) (h : ApproxTWIrrel E n ρ e c)
    (he : CovWIrrelHeadTerm r ls k e) : CovWIrrelHeadShape E n r ls k c := by
  induction h generalizing k with
  | bot => rw [CovWIrrelHeadShape]; trivial
  | bvar => cases he
  | sort => cases he
  | pi => cases he
  | lam => cases he
  | app hf hs ha ihf iha =>
      cases he with
      | app hf =>
          have hh := ihf hf
          rw [CovWIrrelHeadShape] at hh
          exact hh _ hs
  | const => cases he; rw [CovWIrrelHeadShape]; exact ⟨rfl, rfl, rfl, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | delta hd _ _ =>
      cases he
      exact (not_rigidConst_of_deltaConst hd hr).elim
  | recursor ls hp hpre hf h ih =>
      cases he
      exact ((hr _ ‹IotaWitnessS E›.hrec).2 ‹IotaWitnessS E›.hrecK).elim
  | appSpine hf ha hp ihf iha =>
      cases he with
      | app hf => exact headShape_append (ihf hf) hp
  | letE => cases he
  | lit => cases he

theorem covWIrrel_guarded_head_shape {E : ResolvedEnv} {n r k : Nat}
    {ls : List Level} {Γ : LCtx} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (hr : RigidConst E r) (h : ApproxTKWIrrel E n Γ ρ e c)
    (he : CovWIrrelHeadTerm r ls k e) : CovWIrrelHeadShape E n r ls k c := by
  induction h generalizing k with
  | bot => rw [CovWIrrelHeadShape]; trivial
  | free _ h => exact covWIrrel_raw_head_shape hr h he
  | pi => cases he
  | lam => cases he
  | app hf hs ha ihf iha =>
      cases he with
      | app hf =>
          have hh := ihf hf
          rw [CovWIrrelHeadShape] at hh
          exact hh _ hs
  | appSpine hf ha hp ihf iha =>
      cases he with
      | app hf => exact headShape_append (ihf hf) hp
  | delta hd _ _ =>
      cases he
      exact (not_rigidConst_of_deltaConst hd hr).elim
  | letE => cases he
  | lit => cases he
  | iota w _ _ _ =>
      have heq := he.headConst
      rw [iotaLhsOfS, recCall, headConst_fold] at heq
      have heq : w.recRef = r := Option.some.inj heq
      subst r
      exact ((hr _ w.hrec).2 w.hrecK).elim
  | recursorPropK w x _ _ _ _ _ _ _ =>
      have heq := he.headConst
      rw [recCall, headConst_fold] at heq
      have heq : w.recRef = r := Option.some.inj heq
      subst r
      exact ((hr _ w.hrec).2 w.hrecK).elim
  | eta _ _ _ _ _ ihD ihb =>
      rw [CovWIrrelHeadShape]
      intro s hs
      exact ihb s hs (.app he.lift_one)

theorem covWIrrel_proof_field_shape {E : ResolvedEnv} {n r : Nat}
    {ls : List Level} {Γ : LCtx} {ρ : EnvWIrrel} {x : Expr Nat} {c : CptWIrrel}
    (hr : RigidConst E r) (hp : CovWIrrelProofPosition E n r ls 0)
    (h : ApproxTKWIrrel E n Γ ρ (.app (.const r ls) x) c)
    (ht : CTyS E (covWIrrelErase c) .prop) :
    c = .bot ∨ c = .spine r ls [.bot] := by
  have hs := covWIrrel_guarded_head_shape hr h (CovWIrrelHeadTerm.app .head)
  cases c with
  | bot => exact Or.inl rfl
  | prop => simp [CovWIrrelHeadShape] at hs
  | sort => simp [CovWIrrelHeadShape] at hs
  | pi => simp [CovWIrrelHeadShape] at hs
  | lam rows =>
      rcases ctyS_prop_inv ht with h | h
      · cases h
      · cases h
  | spine r' ls' us =>
      rw [CovWIrrelHeadShape] at hs
      obtain ⟨rfl, rfl, hl, hh⟩ := hs
      cases us with
      | nil => cases hl
      | cons u us =>
          have hlen : us = [] := List.length_eq_zero.mp (Nat.succ.inj hl)
          subst us
          have hu := hh 0 (by simp) hp
          have hu : u = .bot := hu
          subst u
          exact Or.inr rfl

def covWIrrelCoarse : CptWIrrel := .spine 5 [] [.bot]

theorem covWIrrel_family_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWIrrelEnv n Γ ρ covWIrrelFamily (.spine 5 [] []) :=
  .free (kFreeT_rigid_const covWIrrel_family_rigid [])
    (.const ρ 5 [] covWIrrel_family_rigid covWIrrel_family_not_propCtor)

theorem covWIrrel_left_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWIrrelEnv n Γ ρ covWIrrelLeft covWIrrelCoarse :=
  covWIrrel_guarded_appSpine_bot (covWIrrel_family_new n Γ ρ)

theorem covWIrrel_right_new (n : Nat) (Γ : LCtx) (ρ : EnvWIrrel) :
    ApproxTKWIrrel covWIrrelEnv n Γ ρ covWIrrelRight covWIrrelCoarse :=
  covWIrrel_guarded_appSpine_bot (covWIrrel_family_new n Γ ρ)

/-- All strictly typed result observations are shared, not only the supplied
coarse compact. No native normalization is a premise. -/
theorem covWIrrel_family_typed_observations_equal (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (c : CptWIrrel) (ht : CTyS covWIrrelEnv (covWIrrelErase c) .prop) :
    ApproxTKWIrrel covWIrrelEnv n Γ ρ covWIrrelLeft c ↔
      ApproxTKWIrrel covWIrrelEnv n Γ ρ covWIrrelRight c := by
  constructor <;> intro h
  · rcases covWIrrel_proof_field_shape covWIrrel_family_rigid
        (covWIrrel_family_proof_position n) h ht with rfl | rfl
    · exact .bot _ _ _
    · exact covWIrrel_right_new n Γ ρ
  · rcases covWIrrel_proof_field_shape covWIrrel_family_rigid
        (covWIrrel_family_proof_position n) h ht with rfl | rfl
    · exact .bot _ _ _
    · exact covWIrrel_left_new n Γ ρ

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_REPAIR_ROOTS
#print axioms CovWIrrelHeadTerm
#print axioms CovWIrrelHeadTerm.lift_one
#print axioms CovWIrrelHeadTerm.headConst
#print axioms CovWIrrelHeadShape
#print axioms covWIrrel_raw_head_shape
#print axioms covWIrrel_guarded_head_shape
#print axioms covWIrrel_proof_field_shape
#print axioms covWIrrelCoarse
#print axioms covWIrrel_family_new
#print axioms covWIrrel_left_new
#print axioms covWIrrel_right_new
#print axioms covWIrrel_family_typed_observations_equal
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_REPAIR_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
