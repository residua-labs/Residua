import rcic.RcicF8DTileStep

/-!
# Actual D execution, G0

Implementation of §3 of ChatGPT's generated/transported provenance specification
(`research/rcic/j-tile/IMPLEMENTATION_D_GENERATED_PROVENANCE.md`, #7203).
Queries compute the already-landed D workers.  The run certificates record their
actual recursive calls, including the right-option branch of a strip; they do
not accept a completed trace or introduce a second D algorithm.  This is the G0
execution layer only.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure.DExecution

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- The three kinds of call made by the landed D worker. -/
inductive DQuery (R : List (Jd E n)) (Γ : LCtx) (T : Expr Nat) : Type where
  | step {a b c : Expr Nat} (s : DStep R Γ a b T) (t : DStep R Γ a c T)
  | strip {a b c : Expr Nat} (s : DStep R Γ a b T) (xs : DSpine R Γ T a c)
  | star {a b c : Expr Nat} (xs : DSpine R Γ T a b) (ys : DSpine R Γ T a c)

namespace DQuery

variable {Γ : LCtx} {T : Expr Nat}

/-- The result type, including the actual input leaf lists. -/
def Result : DQuery R Γ T → Type
  | .step (b := b) (c := c) s t => DOptJoin R Γ b c T (s.leaves ++ t.leaves)
  | .strip (b := b) (c := c) s xs => DSpineJoin R Γ b c T (s.leaves ++ xs.leaves)
  | .star (b := b) (c := c) xs ys => DSpineJoin R Γ b c T (xs.leaves ++ ys.leaves)

/-- Results are computed by the landed workers, never supplied by a caller. -/
def result (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) : (q : DQuery R Γ T) → q.Result
  | .step s t => dStepDiamondWf hW su hΓ s t
  | .strip s xs => dStripWf (dStepDiamondWf hW su) hΓ s xs
  | .star xs ys => dStarWf (dStepDiamondWf hW su) hΓ xs ys

theorem result_step (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) {a b c : Expr Nat}
    (s : DStep R Γ a b T) (t : DStep R Γ a c T) :
    result hW su hΓ (.step s t) = dStepDiamondWf hW su hΓ s t := rfl

theorem result_strip (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) {a b c : Expr Nat}
    (s : DStep R Γ a b T) (xs : DSpine R Γ T a c) :
    result hW su hΓ (.strip s xs) = dStripWf (dStepDiamondWf hW su) hΓ s xs := rfl

theorem result_star (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) {a b c : Expr Nat}
    (xs : DSpine R Γ T a b) (ys : DSpine R Γ T a c) :
    result hW su hΓ (.star xs ys) = dStarWf (dStepDiamondWf hW su) hΓ xs ys := rfl

end DQuery

section Runs

variable (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
variable {Γ : LCtx} (hΓ : CtxWfT E n Γ) {T : Expr Nat}

/-- A step call is bound to its whole actual diamond result. -/
inductive StepRun {a b c : Expr Nat} (s : DStep R Γ a b T) (t : DStep R Γ a c T) :
    DOptJoin R Γ b c T (s.leaves ++ t.leaves) → Type where
  | actual : StepRun s t (dStepDiamondWf hW su hΓ s t)

/-- A step run needs only the actual inputs. -/
def buildStepRun {a b c : Expr Nat} (s : DStep R Γ a b T) (t : DStep R Γ a c T) :
    StepRun hW su hΓ s t (dStepDiamondWf hW su hΓ s t) := .actual

theorem StepRun.result_eq {a b c : Expr Nat}
    {s : DStep R Γ a b T} {t : DStep R Γ a c T}
    {j : DOptJoin R Γ b c T (s.leaves ++ t.leaves)}
    (run : StepRun hW su hΓ s t j) : j = dStepDiamondWf hW su hΓ s t := by
  cases run
  rfl

def StepRun.result {a b c : Expr Nat}
    {s : DStep R Γ a b T} {t : DStep R Γ a c T}
    {j : DOptJoin R Γ b c T (s.leaves ++ t.leaves)}
    (_run : StepRun hW su hΓ s t j) : DOptJoin R Γ b c T (s.leaves ++ t.leaves) := j

theorem buildStepRun_result {a b c : Expr Nat}
    (s : DStep R Γ a b T) (t : DStep R Γ a c T) :
    StepRun.result hW su hΓ (buildStepRun hW su hΓ s t) =
      dStepDiamondWf hW su hΓ s t := rfl

/-- A strip follows the actual optional right leg of its step diamond.  A stay
has no recursive strip call.  A step recurses on exactly that generated step
and the original right tail. -/
inductive StripRun : {a b c : Expr Nat} →
    (s : DStep R Γ a b T) → (xs : DSpine R Γ T a c) → Type where
  | refl {a b : Expr Nat} (s : DStep R Γ a b T) (h : EvTy R Γ a T) :
      StripRun s (.refl h)
  | tailStay {a b c e : Expr Nat} (s : DStep R Γ a b T) (t : DStep R Γ a c T)
      (rest : DSpine R Γ T c e) (left : DOpt R Γ b c T) (h : EvTy R Γ c T)
      (sound : ∀ ℓ ∈ left.leaves ++ (DOpt.stay h).leaves,
        ∃ ℓ' ∈ s.leaves ++ t.leaves, SubEq ℓ ℓ')
      (diamond : StepRun hW su hΓ s t ⟨c, left, .stay h, sound⟩) :
      StripRun s (.tail t rest)
  | tailStep {a b c d e : Expr Nat} (s : DStep R Γ a b T) (t : DStep R Γ a c T)
      (rest : DSpine R Γ T c e) (left : DOpt R Γ b d T) (u : DStep R Γ c d T)
      (sound : ∀ ℓ ∈ left.leaves ++ (DOpt.step u).leaves,
        ∃ ℓ' ∈ s.leaves ++ t.leaves, SubEq ℓ ℓ')
      (diamond : StepRun hW su hΓ s t ⟨d, left, .step u, sound⟩)
      (next : StripRun u rest) : StripRun s (.tail t rest)

/-- Compute the certificate by inspecting the actual diamond result. -/
def buildStripRun : {a b c : Expr Nat} → (s : DStep R Γ a b T) →
    (xs : DSpine R Γ T a c) → StripRun hW su hΓ s xs
  | _, _, _, s, .refl h => .refl s h
  | _, _, _, s, .tail t rest => by
      generalize heq : dStepDiamondWf hW su hΓ s t = j
      have diamond : StepRun hW su hΓ s t j := heq ▸ buildStepRun hW su hΓ s t
      rcases j with ⟨d, left, right, sound⟩
      cases right with
      | stay h => exact .tailStay s t rest left h sound diamond
      | step u => exact .tailStep s t rest left u sound diamond (buildStripRun u rest)

/-- A strip certificate exposes only the landed worker's computed result. -/
def StripRun.result {a b c : Expr Nat} {s : DStep R Γ a b T} {xs : DSpine R Γ T a c}
    (_run : StripRun hW su hΓ s xs) : DSpineJoin R Γ b c T (s.leaves ++ xs.leaves) :=
  dStripWf (dStepDiamondWf hW su) hΓ s xs

theorem StripRun.result_eq {a b c : Expr Nat}
    {s : DStep R Γ a b T} {xs : DSpine R Γ T a c} (run : StripRun hW su hΓ s xs) :
    StripRun.result hW su hΓ run = dStripWf (dStepDiamondWf hW su) hΓ s xs := rfl

theorem buildStripRun_result {a b c : Expr Nat}
    (s : DStep R Γ a b T) (xs : DSpine R Γ T a c) :
    StripRun.result hW su hΓ (buildStripRun hW su hΓ s xs) =
      dStripWf (dStepDiamondWf hW su) hΓ s xs := rfl

/-- Each star tail first completes the exact strip call, then recurses on the
original left tail and that strip's actual left output. -/
inductive StarRun : {a b c : Expr Nat} →
    (xs : DSpine R Γ T a b) → (ys : DSpine R Γ T a c) → Type where
  | refl {a c : Expr Nat} (h : EvTy R Γ a T) (ys : DSpine R Γ T a c) :
      StarRun (.refl h) ys
  | tail {a b c e : Expr Nat} (s : DStep R Γ a b T) (rest : DSpine R Γ T b e)
      (ys : DSpine R Γ T a c) (strip : StripRun hW su hΓ s ys)
      (next : StarRun rest (StripRun.result hW su hΓ strip).left) :
      StarRun (.tail s rest) ys

/-- Build every strip and star child without an external trace. -/
def buildStarRun : {a b c : Expr Nat} → (xs : DSpine R Γ T a b) →
    (ys : DSpine R Γ T a c) → StarRun hW su hΓ xs ys
  | _, _, _, .refl h, ys => .refl h ys
  | _, _, _, .tail s rest, ys =>
      let strip := buildStripRun hW su hΓ s ys
      .tail s rest ys strip (buildStarRun rest (StripRun.result hW su hΓ strip).left)

/-- A star certificate exposes only the landed worker's computed result. -/
def StarRun.result {a b c : Expr Nat} {xs : DSpine R Γ T a b} {ys : DSpine R Γ T a c}
    (_run : StarRun hW su hΓ xs ys) : DSpineJoin R Γ b c T (xs.leaves ++ ys.leaves) :=
  dStarWf (dStepDiamondWf hW su) hΓ xs ys

theorem StarRun.result_eq {a b c : Expr Nat}
    {xs : DSpine R Γ T a b} {ys : DSpine R Γ T a c} (run : StarRun hW su hΓ xs ys) :
    StarRun.result hW su hΓ run = dStarWf (dStepDiamondWf hW su) hΓ xs ys := rfl

theorem buildStarRun_result {a b c : Expr Nat}
    (xs : DSpine R Γ T a b) (ys : DSpine R Γ T a c) :
    StarRun.result hW su hΓ (buildStarRun hW su hΓ xs ys) =
      dStarWf (dStepDiamondWf hW su) hΓ xs ys := rfl

/-- Forget only the leaf-contract proof, retaining the exact common endpoint
and both whole output spines. -/
def joinValue {b c : Expr Nat} {L : List (Jd E n)} (j : DSpineJoin R Γ b c T L) :
    Σ' d : Expr Nat, DSpine R Γ T b d × DSpine R Γ T c d :=
  ⟨j.d, j.left, j.right⟩

theorem stripRefl_exact {a b : Expr Nat} (s : DStep R Γ a b T) (h : EvTy R Γ a T) :
    joinValue (dStripWf (dStepDiamondWf hW su) hΓ s (.refl h)) =
      ⟨b, .refl s.rightTy, .tail s (.refl s.rightTy)⟩ := rfl

/-- The actual stay branch appends the original right tail to the optional
left output, and makes no recursive strip call. -/
theorem stripStay_exact {a b c e : Expr Nat}
    (s : DStep R Γ a b T) (t : DStep R Γ a c T) (rest : DSpine R Γ T c e)
    (left : DOpt R Γ b c T) (h : EvTy R Γ c T)
    (sound : ∀ ℓ ∈ left.leaves ++ (DOpt.stay h).leaves,
      ∃ ℓ' ∈ s.leaves ++ t.leaves, SubEq ℓ ℓ')
    (diamond : StepRun hW su hΓ s t ⟨c, left, .stay h, sound⟩) :
    joinValue (dStripWf (dStepDiamondWf hW su) hΓ s (.tail t rest)) =
      ⟨e, left.toSpine.append rest, .refl rest.rightTy⟩ := by
  have hj := (StepRun.result_eq hW su hΓ diamond).symm
  have hworker := dStripAt.eq_2 (dStepDiamondWf hW su hΓ) a b e s c t rest
  rw [hj] at hworker
  exact congrArg joinValue hworker

/-- The actual step branch recurses on exactly `u, rest`, then appends exactly
the optional left output and that recursive call's left spine. -/
theorem stripStep_exact {a b c d e : Expr Nat}
    (s : DStep R Γ a b T) (t : DStep R Γ a c T) (rest : DSpine R Γ T c e)
    (left : DOpt R Γ b d T) (u : DStep R Γ c d T)
    (sound : ∀ ℓ ∈ left.leaves ++ (DOpt.step u).leaves,
      ∃ ℓ' ∈ s.leaves ++ t.leaves, SubEq ℓ ℓ')
    (diamond : StepRun hW su hΓ s t ⟨d, left, .step u, sound⟩) :
    let next := dStripWf (dStepDiamondWf hW su) hΓ u rest
    joinValue (dStripWf (dStepDiamondWf hW su) hΓ s (.tail t rest)) =
      ⟨next.d, left.toSpine.append next.left, next.right⟩ := by
  have hj := (StepRun.result_eq hW su hΓ diamond).symm
  have hworker := dStripAt.eq_2 (dStepDiamondWf hW su hΓ) a b e s c t rest
  rw [hj] at hworker
  exact congrArg joinValue hworker

theorem starRefl_exact {a c : Expr Nat} (h : EvTy R Γ a T) (ys : DSpine R Γ T a c) :
    joinValue (dStarWf (dStepDiamondWf hW su) hΓ (.refl h) ys) =
      ⟨c, ys, .refl ys.rightTy⟩ := rfl

/-- The star worker uses the strip's actual left spine as its next right
input, and appends the strip's right output before that child's right output. -/
theorem starTail_exact {a b c e : Expr Nat}
    (s : DStep R Γ a b T) (rest : DSpine R Γ T b e) (ys : DSpine R Γ T a c) :
    let strip := dStripWf (dStepDiamondWf hW su) hΓ s ys
    let next := dStarWf (dStepDiamondWf hW su) hΓ rest strip.left
    joinValue (dStarWf (dStepDiamondWf hW su) hΓ (.tail s rest) ys) =
      ⟨next.d, next.left, strip.right.append next.right⟩ := rfl

end Runs

namespace DQuery

variable {Γ : LCtx} {T : Expr Nat}

/-- The execution certificate appropriate to a query's actual worker. -/
def Run (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) (hΓ : CtxWfT E n Γ) :
    DQuery R Γ T → Type
  | .step s t => StepRun hW su hΓ s t (dStepDiamondWf hW su hΓ s t)
  | .strip s xs => StripRun hW su hΓ s xs
  | .star xs ys => StarRun hW su hΓ xs ys

/-- Compute a run from only the frozen query and the worker's explicit inputs. -/
def buildRun (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) (hΓ : CtxWfT E n Γ) :
    (q : DQuery R Γ T) → Run hW su hΓ q
  | .step s t => buildStepRun hW su hΓ s t
  | .strip s xs => buildStripRun hW su hΓ s xs
  | .star xs ys => buildStarRun hW su hΓ xs ys

/-- A run's result is the whole actual result of its indexed query. -/
def Run.result (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) (hΓ : CtxWfT E n Γ)
    {q : DQuery R Γ T} (_run : Run hW su hΓ q) : q.Result := DQuery.result hW su hΓ q

theorem buildRun_result (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (hΓ : CtxWfT E n Γ) (q : DQuery R Γ T) :
    Run.result hW su hΓ (buildRun hW su hΓ q) = DQuery.result hW su hΓ q := rfl

end DQuery

end Rcic.Declarative.F8Measure.DExecution

#print axioms Rcic.Declarative.F8Measure.DExecution.DQuery.Result
#print axioms Rcic.Declarative.F8Measure.DExecution.DQuery.result
#print axioms Rcic.Declarative.F8Measure.DExecution.StepRun.result_eq
#print axioms Rcic.Declarative.F8Measure.DExecution.buildStepRun
#print axioms Rcic.Declarative.F8Measure.DExecution.buildStepRun_result
#print axioms Rcic.Declarative.F8Measure.DExecution.buildStripRun
#print axioms Rcic.Declarative.F8Measure.DExecution.StripRun.result_eq
#print axioms Rcic.Declarative.F8Measure.DExecution.buildStripRun_result
#print axioms Rcic.Declarative.F8Measure.DExecution.buildStarRun
#print axioms Rcic.Declarative.F8Measure.DExecution.StarRun.result_eq
#print axioms Rcic.Declarative.F8Measure.DExecution.buildStarRun_result
#print axioms Rcic.Declarative.F8Measure.DExecution.stripRefl_exact
#print axioms Rcic.Declarative.F8Measure.DExecution.stripStay_exact
#print axioms Rcic.Declarative.F8Measure.DExecution.stripStep_exact
#print axioms Rcic.Declarative.F8Measure.DExecution.starRefl_exact
#print axioms Rcic.Declarative.F8Measure.DExecution.starTail_exact
#print axioms Rcic.Declarative.F8Measure.DExecution.DQuery.buildRun
#print axioms Rcic.Declarative.F8Measure.DExecution.DQuery.buildRun_result
