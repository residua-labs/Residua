import rcic.RcicNativeValleyOf

/-!
# A derivation-size budget does not cover manufactured regularity

The constant-head conversion chain uses genuine subderivations.  A further
call to a fundamental lemma on the sort typing returned by `tySort` or
`convEnds` is different: those landed producers inspect the `CtxWfT` proof,
which is not part of the measured term/conversion derivation.

Here the global environment is empty, the context is always `[x : Sort 0]`,
and the variable, reflexivity, symmetry, and transitivity derivations are
fixed.  Only the context's stored proof of `Sort 0 : Sort 1` changes.  The
actual regularity producer returns its weakening, whose size is unbounded.
This refutes a context-independent budget for that manufactured recursive
call.  It does not refute strong induction with an enriched motive, and it
does not refute the bound on conversion nodes inside a constant derivation.

`closure_claim = 0`.  Composition over landed constructors and producers.
-/

namespace Rcic.Declarative.NativeValleys.PiCycleAudit

/-- Reflexive type conversions pad a proof without changing its judgment. -/
def regularityPad (Γ : LCtx) : Nat → HasTyT emptyEnv 0 Γ (.sort .zero) (.sort (.succ .zero))
  | 0 => .sort Γ .zero
  | k + 1 => .conv Γ (.sort .zero) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.succ (.succ .zero)) (regularityPad Γ k)
      (.refl Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) (.sort Γ (.succ .zero)))

def regularityCtx : LCtx := [.assumption (.sort .zero)]

def regularityCtxWf (k : Nat) : CtxWfT emptyEnv 0 regularityCtx :=
  .assumption [] (.sort .zero) (.succ .zero) .nil (regularityPad [] k)

def regularityVar : HasTyT emptyEnv 0 regularityCtx (.bvar 0) (.sort .zero) :=
  .bvar regularityCtx 0 (.sort .zero) rfl

def regularityRefl : ConvT emptyEnv 0 regularityCtx (.bvar 0) (.bvar 0) (.sort .zero) :=
  .refl regularityCtx (.bvar 0) (.sort .zero) regularityVar

def regularitySymm : ConvT emptyEnv 0 regularityCtx (.bvar 0) (.bvar 0) (.sort .zero) :=
  .symm regularityCtx (.bvar 0) (.bvar 0) (.sort .zero) regularityRefl

def regularityTrans : ConvT emptyEnv 0 regularityCtx (.bvar 0) (.bvar 0) (.sort .zero) :=
  .trans regularityCtx (.bvar 0) (.bvar 0) (.bvar 0) (.sort .zero) regularityRefl regularityRefl

theorem regularityPad_size (Γ : LCtx) (k : Nat) : k ≤ sizeOf (regularityPad Γ k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => simp only [regularityPad] at *; simp at *; omega

/-- The landed weakening preserves each padding node. -/
theorem regularityPad_weaken (hcl : EnvClosed emptyEnv) (Γ : LCtx) (k : Nat) :
    hasTyTWeaken (.assumption (.sort .zero)) hcl (c := 0) (regularityPad Γ k) =
      regularityPad (.assumption (.sort .zero) :: Γ) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change HasTyT.conv _ _ _ _ _
        (hasTyTWeaken (.assumption (.sort .zero)) hcl (c := 0) (regularityPad Γ k)) _ = _
      rw [ih]
      rfl

/-- This identifies the output of the actual landed `tySort` producer. -/
theorem tySort_regularityCtxWf (k : Nat) :
    tySort (.empty : EnvWfT emptyEnv) (regularityCtxWf k) regularityVar =
      ⟨.succ .zero, regularityPad regularityCtx k⟩ := by
  change (⟨.succ .zero,
    hasTyTWeaken (.assumption (.sort .zero))
      (envClosed_of_envWfT (.empty : EnvWfT emptyEnv)) (c := 0) (regularityPad [] k)⟩ :
    Σ' w, HasTyT emptyEnv 0 regularityCtx (.sort .zero) (.sort w)) = _
  rw [regularityPad_weaken]
  rfl

/-- The index-sort component of the actual endpoint producer has the same output. -/
theorem convEnds_regularityCtxWf (k : Nat) :
    (convEnds (.empty : EnvWfT emptyEnv) (regularityCtxWf k) regularityRefl).2.2 =
      ⟨.succ .zero, regularityPad regularityCtx k⟩ :=
  tySort_regularityCtxWf k

theorem tySort_regularity_unbounded (bound : Nat) :
    ∃ hΓ : CtxWfT emptyEnv 0 regularityCtx,
      bound < sizeOf (tySort (.empty : EnvWfT emptyEnv) hΓ regularityVar).2 := by
  refine ⟨regularityCtxWf (bound + 1), ?_⟩
  rw [tySort_regularityCtxWf]
  have h := regularityPad_size regularityCtx (bound + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self bound) h

theorem convEnds_index_unbounded (bound : Nat) :
    ∃ hΓ : CtxWfT emptyEnv 0 regularityCtx,
      bound < sizeOf (convEnds (.empty : EnvWfT emptyEnv) hΓ regularityRefl).2.2.2 := by
  refine ⟨regularityCtxWf (bound + 1), ?_⟩
  rw [convEnds_regularityCtxWf]
  have h := regularityPad_size regularityCtx (bound + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self bound) h

theorem not_tySort_below_input :
    ¬ ∀ hΓ : CtxWfT emptyEnv 0 regularityCtx,
      sizeOf (tySort (.empty : EnvWfT emptyEnv) hΓ regularityVar).2 < sizeOf regularityVar := by
  intro h
  obtain ⟨hΓ, hbig⟩ := tySort_regularity_unbounded (sizeOf regularityVar)
  exact Nat.lt_asymm hbig (h hΓ)

/-- The child conversion is strictly smaller; its manufactured regularity need not be. -/
theorem not_convEnds_index_below_symm :
    sizeOf regularityRefl < sizeOf regularitySymm ∧
    ¬ ∀ hΓ : CtxWfT emptyEnv 0 regularityCtx,
      sizeOf (convEnds (.empty : EnvWfT emptyEnv) hΓ regularityRefl).2.2.2 <
        sizeOf regularitySymm := by
  refine ⟨by simp [regularitySymm], ?_⟩
  intro h
  obtain ⟨hΓ, hbig⟩ := convEnds_index_unbounded (sizeOf regularitySymm)
  exact Nat.lt_asymm hbig (h hΓ)

theorem not_convEnds_index_below_trans :
    sizeOf regularityRefl < sizeOf regularityTrans ∧
    ¬ ∀ hΓ : CtxWfT emptyEnv 0 regularityCtx,
      sizeOf (convEnds (.empty : EnvWfT emptyEnv) hΓ regularityRefl).2.2.2 <
        sizeOf regularityTrans := by
  refine ⟨by simp [regularityTrans] <;> omega, ?_⟩
  intro h
  obtain ⟨hΓ, hbig⟩ := convEnds_index_unbounded (sizeOf regularityTrans)
  exact Nat.lt_asymm hbig (h hΓ)

-- BEGIN RCIC_PI_CYCLE_DERIVATION_ROOTS
#print axioms regularityPad
#print axioms regularityCtx
#print axioms regularityCtxWf
#print axioms regularityVar
#print axioms regularityRefl
#print axioms regularitySymm
#print axioms regularityTrans
#print axioms regularityPad_size
#print axioms regularityPad_weaken
#print axioms tySort_regularityCtxWf
#print axioms convEnds_regularityCtxWf
#print axioms tySort_regularity_unbounded
#print axioms convEnds_index_unbounded
#print axioms not_tySort_below_input
#print axioms not_convEnds_index_below_symm
#print axioms not_convEnds_index_below_trans
-- END RCIC_PI_CYCLE_DERIVATION_ROOTS

end Rcic.Declarative.NativeValleys.PiCycleAudit
