import rcic.RcicF3StepWEqW
import rcic.RcicF3StepWMin
import rcic.RcicF3TierGroup
import rcic.RcicLevelDec

/-!
# F3 stepW as a CHECKED side condition: unconditional tier soundness

`StepWHyp` (`RcicF3StepWMin`) is the tier's W-debt as a *conjecture*: a tier
conditional on it is soundness-relative-to-a-conjecture. This module replaces
the conjecture with a **check the admission checker can run itself**, at
exactly the open-arm nodes (`PendW ∧ UniformType ∧ ¬ InScope`), refusing with
the named residue `[rcic-f3-stepw-wcheck-refusal]` when the check fails:

1. **The instance is decidable in the checker's own terms** (`§A`). At a gap
   position the obligation (`AgreeAt`) is `UniformProp resultLevel ∨ leN
   viewLevel resultLevel`; on the open arm `UniformType resultLevel` holds,
   so the `UniformProp` disjunct is refuted (`uniformProp_not_type`) and the
   obligation is exactly the **level-order comparison** `leN viewLevel
   resultLevel` between two closed Level *data* terms carried by the
   constructor view. `decLeN` decides it in two tiers: param-free levels by
   evaluation (`levelBounded 0` + `eval` at the all-zero total valuation +
   `Nat.decLe`), and param-carrying levels by `decEqN (.max u v) v` — the
   tree's sealed sound-and-complete level-equality decider
   (`RcicLevelDec`). Both tiers are **sound unconditionally**
   (`decLeN_sound`); and the second is ALSO complete — the none-escape
   cell is PROVED EMPTY (`§A3`): `LeqEscape` is refuted for every pair
   (`leqEscape_not`), so `decLeN u v = true ↔ leN u v` holds
   unconditionally (`decLeN_iff`). The former residue
   `[rcic-f3-stepw-leq-complete]` is retired by proof, not by assumption:
   the order bound `leN u v` forces `u` to read `none` wherever `v` does
   (`eval_none_unbounded` upgrades a `none` reading of `u` into arbitrarily
   large lower bounds at the total extension of the valuation,
   contradicting `leN` there once `v` reads some), hence
   `eval ρ (.max u v) = eval ρ v` at EVERY valuation (`eqN_max_of_leN`,
   i.e. `eqN`), and the sealed `decEqN_complete` closes the tier.

2. **The checker runs the check at exactly the open-arm nodes** (`§B`):
   `AgreeAtDec` is the per-position check (`decLeN` of the two levels);
   `GroupWChecked`/`EnvWChecked` (`§C`) are the per-group and
   per-environment faces the admission checker maintains — one
   `GroupWChecked` conjunct per admitted group, threaded down the `EnvWfT`
   structure. `StepWChecked` is the same check lifted to a GLOBAL
   hypothesis over all environments: kept as the bridge face to the
   assembly's global `PartitionSteps` input, and strictly STRONGER than
   `StepWHyp` (it implies it) — the tier wrappers using it are composition
   certificates under that strengthened global conjecture, not a discharge
   of it. The per-environment tier target is `TierF3WChecked` (`§C`).

3. **Soundness and completeness of the check itself** (`§C`/`§D`):
   `stepW_of_groupWChecked` rebuilds the `stepW` row at ONE group from that
   group's check (the in-scope arm by route W4 `stepW_of_inScope`, the
   `UniformProp` arm by route W1 `stepW_of_uniformProp`, the open arm by
   `decLeN_sound`; the case split runs on `Premises4.dec`, no
   `Classical.choice`); `stepsWAlong_of_envWChecked` threads it down an
   environment's structure. The tier wrappers
   `tierF3Uncond_of_checked` / `kernelSoundnessTierUncond_of_checked`
   compose with the landed assembly under the GLOBAL `StepWChecked` plus
   the interim A/B1/D face — composition certificates, honestly
   conditional on the strengthened global conjecture (the assembly's
   `PartitionSteps` input is global-quantified). The per-environment tier
   `TierF3WChecked` needs NO global conjecture: it is discharged from the
   interim A/B1/D face alone (`tierF3WChecked_of_abd`), by threading
   `Covered ∧ EnvWChecked` through the cover machinery's parameterized
   `GInvSteps P K` — zero `StepWChecked`, zero `StepWHyp` premise.
   **The primary faces target #8237's group-granular record
   `PartitionStepsG` (`§CG`)** — cc's r2 routing: "soundness unconditional"
   must land on an INHABITABLE record, not on the vacuous interim ABD/AD
   faces. `tierF3WChecked_of_ADG` discharges the per-environment tier from
   the inhabitable `StepAG`/`StepDG` fields plus `EnvWChecked` alone;
   `tierF3Uncond_of_AD_checked` / `kernelSoundnessTierUncond_of_AD_checked`
   are the checked twins of `TierGroup.tierF3Uncond_of_AD_W`.
   **Completeness (no refusal) is UNCONDITIONAL** (`§D`):
   `stepWChecked_of_hyp` derives `StepWChecked` from `StepWHyp` with no
   fragment guard (the escape cell is empty, `§A3`); the closed-fragment
   route (`stepWChecked_of_hyp_closed`) is retained as the cheap tier.
   Expressiveness is untouched: if the conjecture holds the check never
   refuses; nothing is narrowed.

4. **Cost on the corpus** (`§E`): the check fires only on the open arm. The
   one on-tree out-of-scope W-class fixture `eqWNode` has exactly one gap
   position, with view level `.succ .zero` EQUAL to `resultLevel .succ
   .zero` — the check runs once and passes by closed evaluation (`1 ≤ 1`:
   `decLeN_eqW_gap`, `stepWChecked_eqW`). The canonical `PendW` fixture
   `pwEnvWfT` is in scope (`pwEnvWfT_inScope`) — the check never fires
   there; the function-recursive fixture `wEnv` is `PendA` (the A lane's
   class, not W). No admitted member on the tree carries `Level.param` in
   the compared positions, so the `decEqN` tier never fires on the corpus;
   the closed tier is one `eval` per level. The check CAN refuse
   (`decLeN_can_refuse`): the refusal arm is not degenerate.

The A/B1/D input face is the interim `PartitionStepsABD` (`§4` of
`RcicF3StepWMin`: uninhabited today, `partitionStepsABD_not`); the W-axis
statements here are what survive its migration, unchanged in shape.
Named residues: `[rcic-f3-stepw-wcheck-refusal]` — the checker refuses an
open-arm node whose level order fails `decLeN` (the refusal arm,
non-degenerate by `decLeN_can_refuse`). The former
`[rcic-f3-stepw-leq-complete]` is RETIRED: the none-escape cell is proved
empty (`leqEscape_not`). `closure_claim = 0`; no theory is narrowed
(expressiveness first).
-/

set_option autoImplicit false

namespace Rcic.F3.StepWCheck

open Rcic.Declarative
open Rcic.F3
open Rcic.F3.PSet
open Rcic.Syn.FamApp.StepW
open Rcic.Model.PS (hasTyT_denRefs groupMembersT_preserve groupMembersT_installed)
open Rcic.F3.StepWMin

/-! ## §A the level-order decision (`decLeN`) -/

/-- The all-zero total valuation: the closed-fragment evaluation point. -/
private def rho0 : Nat → Option Nat := fun _ => some 0

/-- A param-free level evaluates the same at every valuation (the `param`
case is excluded by `levelBounded 0`). -/
private theorem eval_eq_of_bounded (rho : Nat → Option Nat) :
    ∀ l : Level, levelBounded 0 l = true → eval rho l = eval rho0 l
  | .zero, _ => rfl
  | .succ l, h => by
      show (eval rho l).map (· + 1) = (eval rho0 l).map (· + 1)
      rw [eval_eq_of_bounded rho l h]
  | .max a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      show (eval rho a).bind (fun x => (eval rho b).map (fun y => max x y)) =
        (eval rho0 a).bind (fun x => (eval rho0 b).map (fun y => max x y))
      rw [eval_eq_of_bounded rho a h.1, eval_eq_of_bounded rho b h.2]
  | .imax a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      show (eval rho b).bind (fun y =>
          if y = 0 then some 0 else (eval rho a).map (fun x => max x y)) =
        (eval rho0 b).bind (fun y =>
          if y = 0 then some 0 else (eval rho0 a).map (fun x => max x y))
      rw [eval_eq_of_bounded rho a h.1, eval_eq_of_bounded rho b h.2]
  | .param i, h => by
      simp only [levelBounded, decide_eq_true_eq] at h
      exact absurd h (Nat.not_lt_zero i)

/-- A param-free level always evaluates (to a value computable at the all-zero
valuation). -/
private theorem eval_bounded_some :
    ∀ l : Level, levelBounded 0 l = true → ∃ n, eval rho0 l = some n
  | .zero, _ => ⟨0, rfl⟩
  | .succ l, h => by
      obtain ⟨n, hn⟩ := eval_bounded_some l h
      refine ⟨n + 1, ?_⟩
      show (eval rho0 l).map (· + 1) = some (n + 1)
      rw [hn]
      rfl
  | .max a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      obtain ⟨x, hx⟩ := eval_bounded_some a h.1
      obtain ⟨y, hy⟩ := eval_bounded_some b h.2
      refine ⟨max x y, ?_⟩
      show (eval rho0 a).bind (fun x' => (eval rho0 b).map (fun y' => max x' y')) = some (max x y)
      rw [hx, hy]
      rfl
  | .imax a b, h => by
      simp only [levelBounded, Bool.and_eq_true] at h
      obtain ⟨y, hy⟩ := eval_bounded_some b h.2
      by_cases hy0 : y = 0
      · refine ⟨0, ?_⟩
        show (eval rho0 b).bind (fun y' =>
            if y' = 0 then some 0 else (eval rho0 a).map (fun x => max x y')) = some 0
        rw [hy]
        show (if y = 0 then some 0 else (eval rho0 a).map (fun x => max x y)) = some 0
        rw [if_pos hy0]
      · obtain ⟨x, hx⟩ := eval_bounded_some a h.1
        refine ⟨max x y, ?_⟩
        show (eval rho0 b).bind (fun y' =>
            if y' = 0 then some 0 else (eval rho0 a).map (fun x => max x y')) = some (max x y)
        rw [hy]
        show (if y = 0 then some 0 else (eval rho0 a).map (fun x => max x y)) = some (max x y)
        rw [if_neg hy0, hx]
        rfl
  | .param i, h => by
      simp only [levelBounded, decide_eq_true_eq] at h
      exact absurd h (Nat.not_lt_zero i)

/-- **The two-tier level-order decision.** Sound on both tiers
(`decLeN_sound`): param-free levels are compared by closed evaluation;
param-carrying levels by the sealed `decEqN` on `max u v = v`, which at every
valuation where both sides are defined reads `max x y = y`, i.e. `x ≤ y`. -/
def decLeN (u v : Level) : Bool :=
  if levelBounded 0 u = true ∧ levelBounded 0 v = true then
    match eval rho0 u, eval rho0 v with
    | some x, some y => decide (x ≤ y)
    | _, _ => false
  else decEqN (.max u v) v

/-- `eqN (max u v) v` implies `leN u v` — the second tier's soundness core:
at each valuation where both sides are defined the equality reads
`some (max x y) = some y`, i.e. `x ≤ y`; when `u` reads `none` the equality
forces `v` to read `none` too, so there is nothing to compare. -/
theorem leN_of_decEqN_max {u v : Level} (h : decEqN (.max u v) v = true) : leN u v := by
  have heq := decEqN_sound _ _ h
  intro rho x y hx hy
  have hmax : eval rho (.max u v) = some (max x y) := by
    show (eval rho u).bind (fun x' => (eval rho v).map (fun y' => max x' y')) = some (max x y)
    rw [hx, hy]
    rfl
  have hmv := heq rho
  rw [hmax, hy] at hmv
  have hxy : max x y = y := Option.some.inj hmv
  omega

/-- **Soundness of the decision (both tiers, unconditionally).** -/
theorem decLeN_sound {u v : Level} (h : decLeN u v = true) : leN u v := by
  unfold decLeN at h
  split at h
  · next hb =>
      split at h
      · next x y hx hy =>
          intro rho a b ha hb'
          have h1 : eval rho0 u = some a := by
            rw [← eval_eq_of_bounded rho u hb.1]; exact ha
          have h2 : eval rho0 v = some b := by
            rw [← eval_eq_of_bounded rho v hb.2]; exact hb'
          have hax : a = x := Option.some.inj (h1.symm.trans hx)
          have hby : b = y := Option.some.inj (h2.symm.trans hy)
          have hxy : x ≤ y := of_decide_eq_true h
          omega
      · exact absurd h (by simp)
  · exact leN_of_decEqN_max h

/-- **Completeness of the decision on the closed (param-free) fragment.** -/
theorem decLeN_closed_complete {u v : Level} (hu : levelBounded 0 u = true)
    (hv : levelBounded 0 v = true) (h : leN u v) : decLeN u v = true := by
  obtain ⟨x, hx⟩ := eval_bounded_some u hu
  obtain ⟨y, hy⟩ := eval_bounded_some v hv
  unfold decLeN
  rw [if_pos ⟨hu, hv⟩, hx, hy]
  simp only [Option.some.injEq, decide_eq_true_eq]
  exact h rho0 x y hx hy

/-- The decision can refuse: `2 ≤ 1` is false by closed evaluation. The
refusal arm of the check is not degenerate. -/
theorem decLeN_can_refuse : decLeN (.succ (.succ .zero)) (.succ .zero) = false := by
  decide

private theorem eval_succ_zero (rho : Nat → Option Nat) :
    eval rho (.succ .zero) = some 1 := rfl

/-- The check at the fixture's gap position passes: view level `.succ .zero`
against result level `.succ .zero`, closed evaluation `1 ≤ 1`. -/
theorem decLeN_eqW_gap : decLeN (.succ .zero) (.succ .zero) = true :=
  decLeN_closed_complete rfl rfl (fun rho x y hu hv => by
    rw [eval_succ_zero] at hu hv
    simp only [Option.some.injEq] at hu hv
    subst hu; subst hv
    exact Nat.le_refl _)

/-- **The open cell of the general completeness direction** (named residue
`[rcic-f3-stepw-leq-complete]`): `leN u v` holds while the `decEqN` tier
refuses. By the tier's soundness core this can only happen through a
**none-escape valuation** — `eval rho u = none` with `eval rho v = some y`,
so a param of `u` absent from `v` whose none-relevance survives; the order
bound `leN u v` bounds `u` at every total valuation — `§A3` below turns
that argument into a proof (`leqEscape_not`). -/
def LeqEscape (u v : Level) : Prop :=
  leN u v ∧ decEqN (.max u v) v = false

/-- On the closed fragment there is no escape (`decLeN_closed_complete`); so
a `leN`-true pair the decision refuses must be param-carrying and refuse on
the `decEqN` tier. -/
theorem leqEscape_of_leq_dec_false {u v : Level} (h : leN u v) (hf : decLeN u v = false) :
    LeqEscape u v ∧ ¬ (levelBounded 0 u = true ∧ levelBounded 0 v = true) := by
  refine ⟨⟨h, ?_⟩, ?_⟩
  · by_cases hb : levelBounded 0 u = true ∧ levelBounded 0 v = true
    · exact absurd (decLeN_closed_complete hb.1 hb.2 h)
        (by rw [hf]; exact Bool.noConfusion)
    · unfold decLeN at hf
      rw [if_neg hb] at hf
      exact hf
  · intro hb
    exact absurd (decLeN_closed_complete hb.1 hb.2 h)
      (by rw [hf]; exact Bool.noConfusion)

/-! ## §A3 the none-escape cell is empty

`LeqEscape` is refuted for every pair of levels. Under `leN u v`, a
valuation reading `u` as `none` is upgraded (`eval_none_unbounded`) into
arbitrarily large lower bounds for `u` at the total extension of that
valuation — contradicting `leN` there once `v` reads some
(`leN_some_of_leN`). Hence `eval ρ (.max u v) = eval ρ v` at EVERY
valuation (`eqN_max_of_leN`, i.e. `eqN (.max u v) v`), and the sealed
`decEqN_complete` closes the `decEqN` tier: `decLeN` is sound AND
complete, unconditionally (`decLeN_iff`). The former residue
`[rcic-f3-stepw-leq-complete]` is retired by proof. -/

/-- The total extension of a valuation: every `none` position reads `M`. -/
private def rhoM (ρ : Nat → Option Nat) (M : Nat) : Nat → Option Nat := fun j =>
  match ρ j with
  | some x => some x
  | none => some M

/-- The total extension is total. -/
private theorem rhoM_total (ρ : Nat → Option Nat) (M : Nat) :
    ∀ j, ∃ x, rhoM ρ M j = some x := by
  intro j
  cases h : ρ j with
  | none => exact ⟨M, by simp only [rhoM, h]⟩
  | some x => exact ⟨x, by simp only [rhoM, h]⟩

/-- At a total valuation every level evaluates. -/
private theorem evalTotal {ρ : Nat → Option Nat} (hρ : ∀ j, ∃ x, ρ j = some x) :
    ∀ l : Level, ∃ z, eval ρ l = some z
  | .zero => ⟨0, rfl⟩
  | .succ l => by
      obtain ⟨z, hz⟩ := evalTotal hρ l
      exact ⟨z + 1, by show (eval ρ l).map (· + 1) = some (z + 1); rw [hz]; rfl⟩
  | .max a b => by
      obtain ⟨x, hx⟩ := evalTotal hρ a
      obtain ⟨y, hy⟩ := evalTotal hρ b
      refine ⟨max x y, ?_⟩
      show (eval ρ a).bind (fun x => (eval ρ b).map (fun y => max x y)) = some (max x y)
      rw [hx, hy]
      rfl
  | .imax a b => by
      obtain ⟨x, hx⟩ := evalTotal hρ a
      obtain ⟨y, hy⟩ := evalTotal hρ b
      refine ⟨if y = 0 then 0 else max x y, ?_⟩
      have hstep : (if y = 0 then some 0 else (eval ρ a).map (fun x => max x y)) =
          some (if y = 0 then 0 else max x y) := by
        rw [hx]
        split <;> rfl
      show (eval ρ b).bind (fun y => if y = 0 then some 0 else
        (eval ρ a).map (fun x => max x y)) = some (if y = 0 then 0 else max x y)
      rw [hy]
      exact hstep
  | .param i => by obtain ⟨x, hx⟩ := hρ i; exact ⟨x, hx⟩

/-- A defined reading is stable under the total extension: the extension
agrees with `ρ` on every position `ρ` defines. -/
private theorem eval_some_stable (ρ : Nat → Option Nat) (M : Nat) :
    ∀ (l : Level) (y : Nat), eval ρ l = some y → eval (rhoM ρ M) l = some y
  | .zero, y, h => h
  | .succ l, y, h => by
      have h' : (eval ρ l).map (· + 1) = some y := h
      cases hz : eval ρ l with
      | none => rw [hz] at h'; exact absurd h' (by simp)
      | some z =>
          have hy : y = z + 1 := by
            rw [hz] at h'
            exact Option.some.inj h'.symm
          show (eval (rhoM ρ M) l).map (· + 1) = some y
          rw [eval_some_stable ρ M l z hz, hy]
          rfl
  | .max a b, y, h => by
      have h' : (eval ρ a).bind (fun x => (eval ρ b).map (fun y => max x y)) = some y := h
      cases hx : eval ρ a with
      | none => rw [hx] at h'; exact absurd h' (by simp)
      | some x =>
          cases hy : eval ρ b with
          | none => rw [hy] at h'; exact absurd h' (by simp)
          | some z =>
              have hv : y = max x z := by
                rw [hx, hy] at h'
                have h'' : some (max x z) = some y := h'
                exact Option.some.inj h''.symm
              show (eval (rhoM ρ M) a).bind (fun x => (eval (rhoM ρ M) b).map (fun y => max x y)) = some y
              rw [eval_some_stable ρ M a x hx, eval_some_stable ρ M b z hy, hv]
              rfl
  | .imax a b, y, h => by
      have h' : (eval ρ b).bind (fun y => if y = 0 then some 0 else
          (eval ρ a).map (fun x => max x y)) = some y := h
      cases hy : eval ρ b with
      | none => rw [hy] at h'; exact absurd h' (by simp)
      | some z =>
          have hstep : (if z = 0 then some 0 else (eval ρ a).map (fun x => max x z)) = some y := by
            rw [hy] at h'; exact h'
          show (eval (rhoM ρ M) b).bind (fun y => if y = 0 then some 0 else
            (eval (rhoM ρ M) a).map (fun x => max x y)) = some y
          rw [eval_some_stable ρ M b z hy]
          show (if z = 0 then some 0 else (eval (rhoM ρ M) a).map (fun x => max x z)) = some y
          rcases Nat.eq_zero_or_pos z with hz0 | hz0
          · rw [hz0] at hstep ⊢
            exact hstep
          · rw [if_neg (Nat.ne_of_gt hz0)] at hstep ⊢
            cases hx : eval ρ a with
            | none => rw [hx] at hstep; exact absurd hstep (by simp)
            | some x =>
                rw [hx] at hstep
                rw [eval_some_stable ρ M a x hx]
                exact hstep
  | .param i, y, h => by
      have h' : ρ i = some y := h
      simp only [eval, rhoM, h']

/-- The none reading is unboundedly large: if `l` reads `none` at `ρ`, then
along the none-positions `l` dominates every bound `M ≥ 1` at the total
extension of `ρ`. -/
private theorem eval_none_unbounded (ρ : Nat → Option Nat) :
    ∀ (l : Level), eval ρ l = none →
      ∃ i, ρ i = none ∧ ∀ M, 1 ≤ M → ∃ x, M ≤ x ∧ eval (rhoM ρ M) l = some x
  | .param i, h => by
      have h' : ρ i = none := h
      exact ⟨i, h', fun M hM => ⟨M, Nat.le_refl M, by simp only [eval, rhoM, h']⟩⟩
  | .succ l, h => by
      have hl : eval ρ l = none := by
        cases hz : eval ρ l with
        | none => rfl
        | some z =>
            have h' : (eval ρ l).map (· + 1) = none := h
            rw [hz] at h'
            exact absurd h' (by simp)
      obtain ⟨i, hi, hM⟩ := eval_none_unbounded ρ l hl
      refine ⟨i, hi, fun M hM1 => ?_⟩
      obtain ⟨x, hxM, hx⟩ := hM M hM1
      exact ⟨x + 1, Nat.le_succ_of_le hxM, by
        show (eval (rhoM ρ M) l).map (· + 1) = some (x + 1)
        rw [hx]
        rfl⟩
  | .max a b, h => by
      cases hx : eval ρ a with
      | none =>
          obtain ⟨i, hi, hM⟩ := eval_none_unbounded ρ a hx
          refine ⟨i, hi, fun M hM1 => ?_⟩
          obtain ⟨x, hxM, hx'⟩ := hM M hM1
          obtain ⟨z, hz⟩ := evalTotal (rhoM_total ρ M) b
          exact ⟨max x z, Nat.le_trans hxM (Nat.le_max_left x z), by
            show (eval (rhoM ρ M) a).bind (fun x => (eval (rhoM ρ M) b).map (fun y => max x y)) = some (max x z)
            rw [hx', hz]
            rfl⟩
      | some x =>
          have hb : eval ρ b = none := by
            cases hz : eval ρ b with
            | none => rfl
            | some z =>
                have h' : (eval ρ a).bind (fun x => (eval ρ b).map (fun y => max x y)) = none := h
                rw [hx, hz] at h'
                exact absurd h' (by simp)
          obtain ⟨i, hi, hM⟩ := eval_none_unbounded ρ b hb
          refine ⟨i, hi, fun M hM1 => ?_⟩
          obtain ⟨y, hyM, hy'⟩ := hM M hM1
          obtain ⟨z, hz⟩ := evalTotal (rhoM_total ρ M) a
          exact ⟨max z y, Nat.le_trans hyM (Nat.le_max_right z y), by
            show (eval (rhoM ρ M) a).bind (fun x => (eval (rhoM ρ M) b).map (fun y => max x y)) = some (max z y)
            rw [hz, hy']
            rfl⟩
  | .imax a b, h => by
      have hred : (eval ρ b).bind (fun y => if y = 0 then some 0 else
          (eval ρ a).map (fun x => max x y)) = none := h
      cases hy : eval ρ b with
      | none =>
          obtain ⟨i, hi, hM⟩ := eval_none_unbounded ρ b hy
          refine ⟨i, hi, fun M hM1 => ?_⟩
          obtain ⟨y, hyM, hy'⟩ := hM M hM1
          obtain ⟨z, hz⟩ := evalTotal (rhoM_total ρ M) a
          have hyne : y ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le hM1 hyM)
          refine ⟨max z y, Nat.le_trans hyM (Nat.le_max_right z y), ?_⟩
          show (eval (rhoM ρ M) b).bind (fun y => if y = 0 then some 0 else
            (eval (rhoM ρ M) a).map (fun x => max x y)) = some (max z y)
          rw [hy']
          show (if y = 0 then some 0 else (eval (rhoM ρ M) a).map (fun x => max x y)) = some (max z y)
          rw [hz, if_neg hyne]
          rfl
      | some y =>
          have hstep : (if y = 0 then some 0 else (eval ρ a).map (fun x => max x y)) = none := by
            rw [hy] at hred; exact hred
          split at hstep
          · next hy0 => exact absurd hstep (by simp)
          · next hy0 =>
              have ha : eval ρ a = none := by
                cases hz : eval ρ a with
                | none => rfl
                | some z =>
                    have h'' : (eval ρ a).map (fun x => max x y) = none := hstep
                    rw [hz] at h''
                    exact absurd h'' (by simp)
              obtain ⟨i, hi, hM⟩ := eval_none_unbounded ρ a ha
              refine ⟨i, hi, fun M hM1 => ?_⟩
              obtain ⟨x, hxM, hx'⟩ := hM M hM1
              refine ⟨max x y, Nat.le_trans hxM (Nat.le_max_left x y), ?_⟩
              show (eval (rhoM ρ M) b).bind (fun y => if y = 0 then some 0 else
                (eval (rhoM ρ M) a).map (fun x => max x y)) = some (max x y)
              rw [eval_some_stable ρ M b y hy]
              show (if y = 0 then some 0 else (eval (rhoM ρ M) a).map (fun x => max x y)) = some (max x y)
              rw [if_neg hy0, hx']
              rfl

/-- Under `leN u v`, a defined reading of `v` forces a defined reading of
`u` at the same valuation. -/
private theorem leN_some_of_leN {u v : Level} (h : leN u v) {ρ : Nat → Option Nat}
    {y : Nat} (hy : eval ρ v = some y) : ∃ x, eval ρ u = some x := by
  cases hu : eval ρ u with
  | some x => exact ⟨x, rfl⟩
  | none =>
      obtain ⟨i, hi, hM⟩ := eval_none_unbounded ρ u hu
      obtain ⟨x, hxM, hx⟩ := hM (y + 1) (Nat.succ_le_succ (Nat.zero_le y))
      have hvM : eval (rhoM ρ (y + 1)) v = some y := eval_some_stable ρ (y + 1) v y hy
      have hcon := h (rhoM ρ (y + 1)) x y hx hvM
      exact absurd (Nat.le_trans hxM hcon) (Nat.not_succ_le_self y)

/-- The order bound upgrades to full valuation equality of `max u v` and
`v` — `eqN (.max u v) v`. -/
theorem eqN_max_of_leN {u v : Level} (h : leN u v) : eqN (.max u v) v := by
  intro ρ
  cases hv : eval ρ v with
  | none =>
      show (eval ρ u).bind (fun x => (eval ρ v).map (fun y => max x y)) = none
      rw [hv]
      cases eval ρ u <;> rfl
  | some y =>
      obtain ⟨x, hx⟩ := leN_some_of_leN h hv
      have hxy : x ≤ y := h ρ x y hx hv
      show (eval ρ u).bind (fun x => (eval ρ v).map (fun y => max x y)) = some y
      rw [hx, hv]
      have hred : (some x).bind (fun x => (some y).map (fun y => max x y)) = some (max x y) := rfl
      rw [hred, Nat.max_eq_right hxy]

/-- **The none-escape cell is empty**: `LeqEscape` is refuted for every
pair of levels. -/
theorem leqEscape_not (u v : Level) : ¬ LeqEscape u v := by
  rintro ⟨hle, hf⟩
  have hc : decEqN (.max u v) v = true := decEqN_complete _ _ (eqN_max_of_leN hle)
  rw [hf] at hc
  exact Bool.noConfusion hc

/-- **Unconditional completeness of the decision**: both tiers. -/
theorem decLeN_complete {u v : Level} (h : leN u v) : decLeN u v = true := by
  cases hu : levelBounded 0 u with
  | true =>
      cases hv : levelBounded 0 v with
      | true => exact decLeN_closed_complete hu hv h
      | false =>
          have hb : ¬ (levelBounded 0 u = true ∧ levelBounded 0 v = true) :=
            fun hc => Bool.noConfusion (hc.2.symm.trans hv)
          unfold decLeN
          rw [if_neg hb]
          exact decEqN_complete _ _ (eqN_max_of_leN h)
  | false =>
      have hb : ¬ (levelBounded 0 u = true ∧ levelBounded 0 v = true) :=
        fun hc => Bool.noConfusion (hc.1.symm.trans hu)
      unfold decLeN
      rw [if_neg hb]
      exact decEqN_complete _ _ (eqN_max_of_leN h)

/-- The decision is an unconditional equivalence with the order. -/
theorem decLeN_iff {u v : Level} : decLeN u v = true ↔ leN u v :=
  ⟨decLeN_sound, fun h => decLeN_complete h⟩

/-! ## §B the per-position check and the walk congruence -/

/-- **The per-gap-position check, in the checker's own terms**: the
constructor view's own level at the position is `decLeN`-below the family's
result level. Same positions as `AgreeAt` (`np ≤ k < cv.parameters.length`
within the concatenated telescope). -/
def AgreeAtDec (np : Nat) (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew)
    (m : CheckedMember) (cv : PolicyConstructorView Ew famO m) : Prop :=
  ∀ (k : Nat) (hk : k < (cv.parameters ++ cv.fields).length), np ≤ k →
    k < cv.parameters.length →
    decLeN (cv.domainsTyped.levels ⟨k, hk⟩) famO.resultLevel = true

/-- The check implies the obligation at every view, unconditionally (no
`UniformType` needed — this is the soundness direction). -/
theorem agreeAt_of_agreeAtDec {np : Nat} {Ew : ResolvedEnv} {famO : PolicyFamilyView Ew}
    {m : CheckedMember} {cv : PolicyConstructorView Ew famO m}
    (h : AgreeAtDec np Ew famO m cv) : AgreeAt np Ew famO m cv :=
  fun k hk hge hlt => Or.inr (decLeN_sound (h k hk hge hlt))

/-- Bounded universal decider for `∀ k < n, P k`. -/
def decForallLt : (n : Nat) → (P : (k : Nat) → k < n → Prop) →
    [∀ k hk, Decidable (P k hk)] → Decidable (∀ k (hk : k < n), P k hk)
  | 0, _, _ => isTrue (fun k hk => absurd hk (Nat.not_lt_zero k))
  | m + 1, P, _ =>
      match decForallLt m (fun k hk => P k (Nat.lt_succ_of_lt hk)) with
      | isFalse hnot =>
          isFalse (fun hall => hnot (fun k hk => hall k (Nat.lt_succ_of_lt hk)))
      | isTrue hall =>
          match inferInstanceAs (Decidable (P m (Nat.lt_succ_self m))) with
          | isFalse hnot =>
              isFalse (fun hall' => hnot (hall' m (Nat.lt_succ_self m)))
          | isTrue hm =>
              isTrue (fun k hk => by
                rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
                · exact hall k hlt
                · exact hm)

instance instDecidableAgreeAtDec (np : Nat) (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew)
    (m : CheckedMember) (cv : PolicyConstructorView Ew famO m) :
    Decidable (AgreeAtDec np Ew famO m cv) :=
  decForallLt (cv.parameters ++ cv.fields).length
    (fun k hk => np ≤ k → k < cv.parameters.length →
      decLeN (cv.domainsTyped.levels ⟨k, hk⟩) famO.resultLevel = true)

instance instDecidableWalkAgree (np : Nat) :
    {S Ew E'' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    (hw : GroupMembersT S Ew ms E'') → Decidable (WalkAgree (AgreeAtDec np) hw)
  | _, _, _, _, .nil _ => isTrue trivial
  | _, _, _, _, .cons _ _ m _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest =>
      let dHead : Decidable (
          match hadm with
          | .constructor famO view _ _ _ _ _ => AgreeAtDec np _ famO m view
          | _ => True) :=
        match hadm with
        | .family _ _ _ _ _ => isTrue trivial
        | .recursor _ _ _ _ _ _ _ => isTrue trivial
        | .constructor famO view _ _ _ _ _ => instDecidableAgreeAtDec np _ famO m view
      let dTail := instDecidableWalkAgree np hrest
      @instDecidableAnd _ _ dHead dTail

/-- On the open arm the two universe classes are disjoint. -/
private theorem uniformProp_not_type {u : Level} (hP : UniformProp u) (hT : UniformType u) :
    False := by
  have h1 := hP (fun _ => 0)
  have h2 := hT (fun _ => 0)
  omega

/-- The closed-fragment guard: both compared levels at every gap position
are param-free. -/
def GapLevelsClosed (np : Nat) (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew)
    (m : CheckedMember) (cv : PolicyConstructorView Ew famO m) : Prop :=
  levelBounded 0 famO.resultLevel = true ∧
    ∀ (k : Nat) (hk : k < (cv.parameters ++ cv.fields).length), np ≤ k →
      k < cv.parameters.length →
      levelBounded 0 (cv.domainsTyped.levels ⟨k, hk⟩) = true

/-- The obligation implies the check on the closed fragment (completeness
direction; `UniformType` kills the `UniformProp` disjunct). -/
theorem agreeAtDec_of_agreeAt_closed {np : Nat} {Ew : ResolvedEnv}
    {famO : PolicyFamilyView Ew} {m : CheckedMember}
    {cv : PolicyConstructorView Ew famO m}
    (hT : UniformType famO.resultLevel)
    (hcl : GapLevelsClosed np Ew famO m cv)
    (h : AgreeAt np Ew famO m cv) : AgreeAtDec np Ew famO m cv := by
  intro k hk hge hlt
  refine decLeN_closed_complete (hcl.2 k hk hge hlt) hcl.1 ?_
  rcases h k hk hge hlt with hP | hle
  · exact (uniformProp_not_type hP hT).elim
  · exact hle

/-- Pointwise congruence for `WalkAgree`: any pointwise implication between
`agree` predicates lifts along the walk (no walk bookkeeping — the
predicates never read the derivation). -/
theorem walkAgree_congr {agree1 agree2 : ∀ (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew)
      (m : CheckedMember), PolicyConstructorView Ew famO m → Prop}
    (h : ∀ (Ew : ResolvedEnv) (famO : PolicyFamilyView Ew) (m : CheckedMember)
      (cv : PolicyConstructorView Ew famO m), agree1 Ew famO m cv → agree2 Ew famO m cv) :
    {S Ew E'' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    (hw : GroupMembersT S Ew ms E'') → WalkAgree agree1 hw → WalkAgree agree2 hw
  | _, _, _, _, .nil _, _ => trivial
  | _, _, _, _, .cons _ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ htyped hrest, hh => by
      obtain ⟨h1, h2⟩ := hh
      refine ⟨?_, walkAgree_congr h hrest h2⟩
      cases hadm with
      | family _ _ _ _ _ => trivial
      | recursor _ _ _ _ _ _ _ => trivial
      | constructor famO view _ _ _ _ _ => exact h _ famO m view h1

/-! ## §C soundness unconditional: the checked side condition -/

/-! ## §C the checked side condition: per-group, per-environment, global -/

/-- **The per-group check**: at every open-arm node (`PendW ∧ UniformType ∧
¬ InScope`) of THIS group, the walk satisfies `AgreeAtDec`. This is what the
admission checker runs when it admits the group; failure is the refusal
residue `[rcic-f3-stepw-wcheck-refusal]`. -/
def GroupWChecked {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  ∀ (node : RecNode E E' f rr rm),
    PendW hmem node → UniformType node.a.family.resultLevel →
    ¬ (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope →
    WalkAgree (AgreeAtDec node.a.family.parameters.length) hmem

/-- **The per-environment check**: `GroupWChecked` at every group admitted
along the `EnvWfT` structure — the invariant the admission checker
maintains, one conjunct per admitted group. -/
def EnvWChecked : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => EnvWChecked hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => EnvWChecked hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => EnvWChecked hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => EnvWChecked hE
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem =>
      EnvWChecked hE ∧ GroupWChecked hE hfam hctors hrec hmem

/-- **The check-passed GLOBAL side condition** — the per-group check lifted
over all environments; kept as the bridge face to the assembly's global
`PartitionSteps` input. This is strictly STRONGER than `StepWHyp` (it
implies it via `agreeAt_of_agreeAtDec`); the admission-time faces are
`GroupWChecked`/`EnvWChecked` above. -/
def StepWChecked : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm),
    PendW hmem node → UniformType node.a.family.resultLevel →
    ¬ (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope →
    WalkAgree (AgreeAtDec node.a.family.parameters.length) hmem

/-- **The check reassembles the `stepW` row at one group** (the per-group
bridge): the in-scope arm by route W4, the `UniformProp` arm by route W1,
the open arm by the check's soundness. No `Classical.choice` (the case
split runs on `Premises4.dec`). -/
theorem stepW_of_groupWChecked (P : Premises4) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hg : GroupWChecked hE hfam hctors hrec hmem)
    (node : RecNode E E' f rr rm) (hPend : PendW hmem node) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
  cases P.dec ((EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope) with
  | isTrue hIS =>
      exact stepW_of_inScope hE hfam hctors hrec hmem node (walkRec_of_group hmem) hIS
  | isFalse hIS =>
      rcases uniformProp_or_uniformType node with hP | hT
      · exact stepW_of_uniformProp hE hfam hctors hrec hmem node (walkRec_of_group hmem) hP
      · exact walkAgree_congr (fun _ _ _ cv => agreeAt_of_agreeAtDec) hmem
          (hg node hPend hT hIS)

/-- The global side condition specializes to the per-group bridge. -/
theorem stepW_of_checked (P : Premises4) (h : StepWChecked)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hPend : PendW hmem node) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem :=
  stepW_of_groupWChecked P hE hfam hctors hrec hmem
    (fun node hPend hT hIS => h hE hfam hctors hrec hmem node hPend hT hIS) node hPend

/-- The `stepW` row at every group along an environment's structure — the
per-environment fragment of the global `stepW` field. -/
def StepsWAlong : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => StepsWAlong hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => StepsWAlong hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => StepsWAlong hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => StepsWAlong hE
  | _, .group E f _fm _ctors rr rm E' hE _hfam _hctors _hrec hmem =>
      (∀ (node : RecNode E E' f rr rm) (_hPend : PendW hmem node),
        WalkAgree (AgreeAt node.a.family.parameters.length) hmem) ∧ StepsWAlong hE

/-- **The per-environment check buys the per-environment W-row**: the check
threaded down `hW`'s structure reassembles `stepW` at every group of that
structure. -/
theorem stepsWAlong_of_envWChecked (P : Premises4) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → EnvWChecked hW → StepsWAlong hW
  | _, .empty, _ => trivial
  | _, .axiom _ _ _ _ hE _ _ _ _, h => stepsWAlong_of_envWChecked P hE h
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, h => stepsWAlong_of_envWChecked P hE h
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, h => stepsWAlong_of_envWChecked P hE h
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, h => stepsWAlong_of_envWChecked P hE h
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, h => by
      obtain ⟨hsub, hg⟩ := h
      exact ⟨fun node hPend => stepW_of_groupWChecked P hE hfam hctors hrec hmem hg node hPend,
        stepsWAlong_of_envWChecked P hE hsub⟩

/-- The full steps record from the non-W fields plus the global check. -/
theorem partitionSteps_of_checked (P : Premises4) (K : Nat → Nat) (h : StepWChecked)
    (abd : PartitionStepsABD P K) : PartitionSteps P K where
  stepA := abd.stepA
  stepB1 := abd.stepB1
  stepD := abd.stepD
  stepW := fun hE hfam hctors hrec hmem node hPend =>
    stepW_of_checked P h hE hfam hctors hrec hmem node hPend

/-- **The tier under the global check** — a composition certificate
conditional on the decLeN-strengthened GLOBAL W-conjecture
(`StepWChecked`, strictly stronger than `StepWHyp`) plus the interim
A/B1/D face (`partitionStepsABD_not`; the W-axis statement is what
survives its migration). NOT a per-environment admission statement; the
per-environment face is `TierF3WChecked` (via `tierF3WChecked_of_checked`),
and the PRIMARY global face on the inhabitable record is
`tierF3Uncond_of_AD_checked` (`§CG`). -/
theorem tierF3Uncond_of_checked (h : StepWChecked)
    (abd : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsABD P K) :
    Rcic.Apex.TierF3Uncond :=
  tierF3Uncond_of_partition (fun P K => partitionSteps_of_checked P K h (abd P K))

/-- The full unconditional kernel tier under the same global check and the
same interim A/B1/D input face. -/
theorem kernelSoundnessTierUncond_of_checked (h : StepWChecked)
    (abd : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsABD P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  ⟨Rcic.Apex.tierF1, tierF3Uncond_of_checked h abd⟩

/-- **The per-environment tier target**: the height-4 consistency tier with
the checker's own face threaded inside the environment quantifier — for
every admitted environment that PASSED the W-check (`EnvWChecked hW`), the
tier body holds at that environment. This is the admission-time reading of
unconditional soundness. Discharged with NO global W-conjecture by
`tierF3WChecked_of_abd` below, by instantiating the cover machinery's
parameterized `GInvSteps P K` at `fun hW => Covered hW ∧ EnvWChecked hW`. -/
def TierF3WChecked : Prop :=
  Premises4 → ∀ (K : Nat → Nat) (E : ResolvedEnv) (hW : EnvWfT E),
    EnvWChecked hW → PSet.BoundG K hW → PSet.BoundDG K hW → PSet.AxiomFreeEnv' E →
    E.members 0 = some falseFamMember → E.members 1 = some falseRecMemberU →
    ∀ (n : Nat) (e : Expr Nat) (D : HasTyT E n [] e (.const 0 [])),
      PSet.LevelsBelow 4 K D → False

/-- Per-node dispatch consuming `hg : GroupWChecked` instead of a global
`StepWChecked`. Mirrors the assembly's `nodeStepRow`, with the walk row
supplied per-group by the check (`stepW_of_groupWChecked`). -/
theorem nodeStepRow_of_groupWChecked (P : Premises4) (K : Nat → Nat) (abd : PartitionStepsABD P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hg : GroupWChecked hE hfam hctors hrec hmem)
    (node : RecNode E E' f rr rm) :
    NodeStepRow P K hE hfam hctors hrec hmem node := by
  have hAg : WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
    cases P.dec (WalkClass node.a.family.parameters.length hmem) with
    | isTrue hw => exact walkAgree_of_walkClass node hmem hw
    | isFalse hw => exact stepW_of_groupWChecked P hE hfam hctors hrec hmem hg node hw
  cases P.dec (PendA node) with
  | isTrue hA =>
      have hr := abd.stepA hE hfam hctors hrec hmem node hA
      exact ⟨hr.1, hAg, hr.2⟩
  | isFalse hA =>
  cases P.dec (PendD node) with
  | isTrue hD =>
      have hr := abd.stepD hE hfam hctors hrec hmem node hD hA
      exact ⟨hr.1, hAg, hr.2⟩
  | isFalse hD =>
  cases P.dec (PendB node) with
  | isTrue hB =>
      have hr := abd.stepB1 hE hfam hctors hrec hmem node hB hA hD
      exact ⟨hr.1, hAg, hr.2⟩
  | isFalse hB =>
      have hG := groupClassAt_of_notADB P node hA hD hB
      exact ⟨hG.1, hAg, fun hBB μ X => recPkg_classG P K node hG.2 (hBB.2.2.2 node) X⟩

/-- The covered-environment walk from the per-environment check: `WalkG hW`
from `Covered hW ∧ EnvWChecked hW` and the interim A/B1/D face. -/
theorem walkG_of_coveredWChecked (P : Premises4) (K : Nat → Nat) (abd : PartitionStepsABD P K) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → Covered hW → EnvWChecked hW → WalkG hW
  | _, .empty, _, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _ => hC
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hWchk =>
      walkG_of_coveredWChecked P K abd hE hC hWchk
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC, hWchk =>
      walkG_of_coveredWChecked P K abd hE hC hWchk
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hWchk =>
      walkG_of_coveredWChecked P K abd hE hC hWchk
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem, hC, hWchk =>
      ⟨walkG_of_coveredWChecked P K abd hE hC.1 hWchk.1, walkRec_of_group hmem,
        fun node => (nodeStepRow_of_groupWChecked P K abd hE hfam hctors hrec hmem hWchk.2 node).2.1⟩

/-- `GInvSteps` at the per-environment face `Covered ∧ EnvWChecked`: the
cover invariant is maintained by the admission checker's own check. -/
theorem steps_coveredWChecked (P : Premises4) (K : Nat → Nat) (abd : PartitionStepsABD P K) :
    GInvSteps P K (fun {E} (hW : EnvWfT E) => Covered hW ∧ EnvWChecked hW)
      (fun {E} (hW : EnvWfT E) => BoundG K hW) where
  stepDef := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, hB.1, fun IH => gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.2
      (walkG_of_coveredWChecked P K abd hE hC.1 hC.2) IH⟩
  stepThm := fun _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, hB.1, fun IH => gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp hB.2
      (walkG_of_coveredWChecked P K abd hE hC.1 hC.2) IH⟩
  stepOpq := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, hB.1, fun IH => gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.2
      (walkG_of_coveredWChecked P K abd hE hC.1 hC.2) IH⟩
  stepGrp := fun _ _ _ _ _ _ _ hE hfam hctors hrec hmem hC hB =>
    ⟨⟨hC.1.1, hC.2.1⟩, hB.1, fun IH =>
      gInv_group_of P K hE hfam hctors hrec hmem
        (fun node i => (nodeStepRow_of_groupWChecked P K abd hE hfam hctors hrec hmem hC.2.2 node).1 i)
        (walkRec_of_group hmem)
        (fun node => (nodeStepRow_of_groupWChecked P K abd hE hfam hctors hrec hmem hC.2.2 node).2.1)
        hB.2.1 hB.2.2.1
        (fun node μ X => (nodeStepRow_of_groupWChecked P K abd hE hfam hctors hrec hmem hC.2.2 node).2.2 hB μ X)
        IH⟩

/-- Interim bridge: per-environment tier soundness with ZERO `StepWChecked`
/ `StepWHyp` premise, through the **vacuous** interim A/B1/D face (m3 #8231 /
`partitionStepsABD_not`): a composition certificate, NOT a discharge route.
The PRIMARY face is `tierF3WChecked_of_ADG` in `§E` below, which replaces the
vacuous ABD input by the inhabitable group-granular `StepAG`/`StepDG` fields
of #8237's `PartitionStepsG`. -/
theorem tierF3WChecked_of_abd
    (abd : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsABD P K) :
    TierF3WChecked := by
  intro P K E hW hchk hB _hBDG hAx _h0 h1 n e D hLOK
  have hC : Covered hW ∧ EnvWChecked hW := ⟨EnvWfT_axiomFree_covered P hW hAx, hchk⟩
  have hI : GInv P K hW := gInv_of_steps P K _ _ (steps_coveredWChecked P K (abd P K))
    (fun _ _ _ _ _ _ _ _ _ hCx => hCx.1) hW hC hB
  have hRA := readsOKAlong_envCtxW hW (walkG_of_coveredWChecked P K (abd P K) hW hC.1 hchk)
    (envCtx hW) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtx hW) hW hRA).1
  have hIv := hI (envCtx hW) (fun _ _ => rfl) _ hF
  have hES := envSound_of P (Efin := E) (fun _ _ h => h) hIv.1
    (fun r m hm hk => hIv.2 E (fun _ _ h => h) r m hm hk) (fun _ => 0) n
  exact empty_of_falseRec P (hIv.1 1 _ h1) (sound_ty (P.good _ rfl) hES D hLOK ρ0 trivial)

/-! ## §CG the group-granular record `PartitionStepsG` (#8237): the primary faces

The r2 audit verdict + cc routing: "soundness unconditional" must land on an
INHABITABLE record, not on the vacuous interim ABD/AD faces. Here the
checked-W face targets #8237's `PartitionStepsG`: A and D enter as the
group-granular `StepAG`/`StepDG` fields (semantic, no `RecFieldsDirect` row;
#8237 re-runs m3's probes on them), W enters either as the global check
`StepWChecked` (`partitionStepsG_of_checked`) or per-environment as
`EnvWChecked` (`tierF3WChecked_of_ADG`) — the latter with ZERO global W
premise. -/

/-- Every node's walk agreement at one group from the group's own check
(`WalkClass` by the landed route, `PendW` by the check); the checked twin of
`TierGroup.walkAgree_of_stepW`. -/
theorem walkAgree_of_groupWChecked (P : Premises4) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hg : GroupWChecked hE hfam hctors hrec hmem)
    (node : RecNode E E' f rr rm) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
  cases P.dec (WalkClass node.a.family.parameters.length hmem) with
  | isTrue hw => exact walkAgree_of_walkClass node hmem hw
  | isFalse hw => exact stepW_of_groupWChecked P hE hfam hctors hrec hmem hg node hw

/-- The covered-environment walk from the check alone — no A/D input needed:
the W-check buys `WalkG` by itself. -/
theorem walkG_of_envWChecked (P : Premises4) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → Covered hW → EnvWChecked hW → WalkG hW
  | _, .empty, _, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _ => hC
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hWchk =>
      walkG_of_envWChecked P hE hC hWchk
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC, hWchk =>
      walkG_of_envWChecked P hE hC hWchk
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hWchk =>
      walkG_of_envWChecked P hE hC hWchk
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem, hC, hWchk =>
      ⟨walkG_of_envWChecked P hE hC.1 hWchk.1, walkRec_of_group hmem,
        walkAgree_of_groupWChecked P hE hfam hctors hrec hmem hWchk.2⟩

/-- `GInvSteps` at `Covered ∧ EnvWChecked` with both tier bounds — the checked
twin of `TierGroup.gInvSteps_of_partitionStepsG`: the A/D group steps come
from the inhabitable `StepAG`/`StepDG` fields, the walk from the check. -/
theorem steps_coveredWChecked_G (P : Premises4) (K : Nat → Nat)
    (hA : TierGroup.StepAG P K) (hD : TierGroup.StepDG P K) :
    GInvSteps P K (fun {E : ResolvedEnv} (hW : EnvWfT E) => Covered hW ∧ EnvWChecked hW)
      (fun {E : ResolvedEnv} (hW : EnvWfT E) => PSet.BoundG K hW ∧ PSet.BoundDG K hW) where
  stepDef := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.1.2
      (walkG_of_envWChecked P hE hC.1 hC.2) IH⟩
  stepThm := fun _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp
      hB.1.2 (walkG_of_envWChecked P hE hC.1 hC.2) IH⟩
  stepOpq := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv
      hB.1.2 (walkG_of_envWChecked P hE hC.1 hC.2) IH⟩
  stepGrp := fun _ _ _ _ _ _ _ hE hfam hctors hrec hmem hC hB =>
    ⟨⟨hC.1.1, hC.2.1⟩, ⟨hB.1.1, hB.2.1⟩, fun IH =>
      TierGroup.groupStepAt_of_AD P K hA hD hE hfam hctors hrec hmem
        (walkAgree_of_groupWChecked P hE hfam hctors hrec hmem hC.2.2) hB.1 hB.2 IH⟩

/-- **PRIMARY per-environment face**: tier soundness at every admitted
environment that passed the W-check, from the inhabitable group-granular
A/D fields — ZERO `StepWChecked` / `StepWHyp` premise, ZERO vacuous input. -/
theorem tierF3WChecked_of_ADG
    (hA : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepDG P K) :
    TierF3WChecked := by
  intro P K E hW hchk hB hBDG hAx _h0 h1 n e D hLOK
  have hC : Covered hW ∧ EnvWChecked hW := ⟨EnvWfT_axiomFree_covered P hW hAx, hchk⟩
  have hI : GInv P K hW := gInv_of_steps P K _ _ (steps_coveredWChecked_G P K (hA P K) (hD P K))
    (fun _ _ _ _ _ _ _ _ _ hCx => hCx.1) hW hC ⟨hB, hBDG⟩
  have hRA := readsOKAlong_envCtxW hW (walkG_of_envWChecked P hW hC.1 hchk)
    (envCtx hW) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtx hW) hW hRA).1
  have hIv := hI (envCtx hW) (fun _ _ => rfl) _ hF
  have hES := envSound_of P (Efin := E) (fun _ _ h => h) hIv.1
    (fun r m hm hk => hIv.2 E (fun _ _ h => h) r m hm hk) (fun _ => 0) n
  exact empty_of_falseRec P (hIv.1 1 _ h1) (sound_ty (P.good _ rfl) hES D hLOK ρ0 trivial)

/-- The global check plugs into #8237's record verbatim: the `StepWField`
from `StepWChecked` — the checked twin of `TierGroup.partitionStepsG_of_hyp`. -/
theorem partitionStepsG_of_checked (P : Premises4) (K : Nat → Nat) (h : StepWChecked)
    (hA : TierGroup.StepAG P K) (hD : TierGroup.StepDG P K) : TierGroup.PartitionStepsG P K where
  stepA := hA
  stepD := hD
  stepW := stepW_of_checked P h

/-- **PRIMARY global face**: tier soundness from the inhabitable
group-granular record + the admission check — the checked twin of
`TierGroup.tierF3Uncond_of_AD_W`. -/
theorem tierF3Uncond_of_AD_checked (h : StepWChecked)
    (hA : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepDG P K) :
    Rcic.Apex.TierF3Uncond :=
  TierGroup.tierF3Uncond_of_partitionStepsG fun P K =>
    partitionStepsG_of_checked P K h (hA P K) (hD P K)

/-- The conditional tier under the same inhabitable antecedents. -/
theorem tierF3_of_AD_checked (h : StepWChecked)
    (hA : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepDG P K) :
    Rcic.Apex.TierF3 :=
  Rcic.Apex.tierF3_of_tierF3Uncond (tierF3Uncond_of_AD_checked h hA hD)

/-- **PRIMARY kernel-tier face**: F1 closed + F3 from the inhabitable record
and the check alone. -/
theorem kernelSoundnessTierUncond_of_AD_checked (h : StepWChecked)
    (hA : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), TierGroup.StepDG P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  ⟨Rcic.Apex.tierF1, tierF3Uncond_of_AD_checked h hA hD⟩

/-! ## §D completeness (no refusal) is unconditional -/

/-- The walk-lifted closed guard: at every open-arm node, the walk's gap
levels and result level are param-free. -/
def StepWHypClosed : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm),
    PendW hmem node → UniformType node.a.family.resultLevel →
    ¬ (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope →
    WalkAgree (GapLevelsClosed node.a.family.parameters.length) hmem

/-- The closed-fragment lift: on a walk whose gap levels are param-free, the
semantic agreement converts positionwise into the check (the `UniformType`
transport per view comes from `walk_ctor_views_syn_eq`). -/
theorem walkAgreeDec_of_walkAgree {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm)
    (hT : UniformType node.a.family.resultLevel) :
    {S Ew E'' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    (hw : GroupMembersT S Ew ms E'') →
    (∀ c, c ∈ ms → c ∈ (f, fm) :: ctors ++ [(rr, rm)]) →
    (∀ r' m', E''.members r' = some m' → E'.members r' = some m') →
    WalkAgree (GapLevelsClosed node.a.family.parameters.length) hw →
    WalkAgree (AgreeAt node.a.family.parameters.length) hw →
    WalkAgree (AgreeAtDec node.a.family.parameters.length) hw := by
  intro S Ew E'' ms hw
  induction hw with
  | nil _ => intros _ _ _ _; trivial
  | cons E₀ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ htyped hrest ih =>
      intro hms hsub hcl hsem
      have hin := hms (r, m) (List.mem_cons_self _ _)
      have hsubR : ∀ r' m', (extendEnv E₀ r m).members r' = some m' → E'.members r' = some m' :=
        fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
      have hEw : ∀ r' m', E₀.members r' = some m' → E'.members r' = some m' :=
        fun r' m' h => hsubR r' m' (members_extend_preserved hfresh r' m' h)
      obtain ⟨hcl1, hcl2⟩ := hcl
      obtain ⟨hsem1, hsem2⟩ := hsem
      refine ⟨?_, ih (fun c hc => hms c (List.mem_cons_of_mem _ hc)) hsub hcl2 hsem2⟩
      cases hadm with
      | family _ _ _ _ _ => trivial
      | recursor _ _ _ _ _ _ _ => trivial
      | constructor famO view _ _ _ _ _ =>
          obtain ⟨_, _, _, _, hlv, _⟩ :=
            walk_ctor_views_syn_eq hE hfam hctors hrec hmem hWR node famO view hin hEw
          have hT' : UniformType famO.resultLevel := by rw [hlv]; exact hT
          exact agreeAtDec_of_agreeAt_closed hT' hcl1 hsem1

/-- **Completeness on the closed fragment**: if the conjecture holds, the
checker never refuses a group whose compared levels are param-free. -/
theorem stepWChecked_of_hyp_closed (h : StepWHyp) (hc : StepWHypClosed) : StepWChecked := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem node hPend hT hIS
  exact walkAgreeDec_of_walkAgree hE hfam hctors hrec hmem (walkRec_of_group hmem) node hT hmem
    (fun _ h => h) (fun _ _ h => h) (hc hE hfam hctors hrec hmem node hPend hT hIS)
    (h hE hfam hctors hrec hmem node hPend hT hIS)

/-- Outside the (empty) escape cell the obligation implies the check
(`UniformType` kills the `UniformProp` disjunct; `decLeN_complete`). -/
theorem agreeAtDec_of_agreeAt {np : Nat} {Ew : ResolvedEnv}
    {famO : PolicyFamilyView Ew} {m : CheckedMember}
    {cv : PolicyConstructorView Ew famO m}
    (hT : UniformType famO.resultLevel)
    (h : AgreeAt np Ew famO m cv) : AgreeAtDec np Ew famO m cv := by
  intro k hk hge hlt
  rcases h k hk hge hlt with hP | hle
  · exact (uniformProp_not_type hP hT).elim
  · exact decLeN_complete hle

/-- The unconditional lift: semantic agreement converts positionwise into
the check (per-view `UniformType` from `walk_ctor_views_syn_eq`). -/
theorem walkAgreeDec_of_walkAgree_gen {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hWR : WalkRec hmem) (node : RecNode E E' f rr rm)
    (hT : UniformType node.a.family.resultLevel) :
    {S Ew E'' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    (hw : GroupMembersT S Ew ms E'') →
    (∀ c, c ∈ ms → c ∈ (f, fm) :: ctors ++ [(rr, rm)]) →
    (∀ r' m', E''.members r' = some m' → E'.members r' = some m') →
    WalkAgree (AgreeAt node.a.family.parameters.length) hw →
    WalkAgree (AgreeAtDec node.a.family.parameters.length) hw := by
  intro S Ew E'' ms hw
  induction hw with
  | nil _ => intros _ _ _; trivial
  | cons E₀ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ htyped hrest ih =>
      intro hms hsub hsem
      have hin := hms (r, m) (List.mem_cons_self _ _)
      have hsubR : ∀ r' m', (extendEnv E₀ r m).members r' = some m' → E'.members r' = some m' :=
        fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
      have hEw : ∀ r' m', E₀.members r' = some m' → E'.members r' = some m' :=
        fun r' m' h => hsubR r' m' (members_extend_preserved hfresh r' m' h)
      obtain ⟨hsem1, hsem2⟩ := hsem
      refine ⟨?_, ih (fun c hc => hms c (List.mem_cons_of_mem _ hc)) hsub hsem2⟩
      cases hadm with
      | family _ _ _ _ _ => trivial
      | recursor _ _ _ _ _ _ _ => trivial
      | constructor famO view _ _ _ _ _ =>
          obtain ⟨_, _, _, _, hlv, _⟩ :=
            walk_ctor_views_syn_eq hE hfam hctors hrec hmem hWR node famO view hin hEw
          have hT' : UniformType famO.resultLevel := by rw [hlv]; exact hT
          exact agreeAtDec_of_agreeAt hT' hsem1

/-- **Completeness, unconditional**: if the conjecture holds, the checker
never refuses at all (the escape cell is empty, `leqEscape_not`). -/
theorem stepWChecked_of_hyp (h : StepWHyp) : StepWChecked := by
  intro E E' f rr fm rm ctors hE hfam hctors hrec hmem node hPend hT hIS
  exact walkAgreeDec_of_walkAgree_gen hE hfam hctors hrec hmem
    (walkRec_of_group hmem) node hT hmem (fun _ hh => hh) (fun _ _ hh => hh)
    (h hE hfam hctors hrec hmem node hPend hT hIS)

/-! ## §E fixtures and cost -/

/-- The check fires exactly once on the corpus — at the open-arm fixture's
single gap position — and passes by closed evaluation. -/
theorem stepWChecked_eqW : WalkAgree (AgreeAtDec 0) eqWMembersT := by
  decide

end Rcic.F3.StepWCheck

#print axioms Rcic.F3.StepWCheck.decLeN
#print axioms Rcic.F3.StepWCheck.leN_of_decEqN_max
#print axioms Rcic.F3.StepWCheck.decLeN_sound
#print axioms Rcic.F3.StepWCheck.decLeN_closed_complete
#print axioms Rcic.F3.StepWCheck.decLeN_can_refuse
#print axioms Rcic.F3.StepWCheck.decLeN_eqW_gap
#print axioms Rcic.F3.StepWCheck.LeqEscape
#print axioms Rcic.F3.StepWCheck.leqEscape_of_leq_dec_false
#print axioms Rcic.F3.StepWCheck.eqN_max_of_leN
#print axioms Rcic.F3.StepWCheck.leqEscape_not
#print axioms Rcic.F3.StepWCheck.decLeN_complete
#print axioms Rcic.F3.StepWCheck.decLeN_iff
#print axioms Rcic.F3.StepWCheck.AgreeAtDec
#print axioms Rcic.F3.StepWCheck.agreeAt_of_agreeAtDec
#print axioms Rcic.F3.StepWCheck.GapLevelsClosed
#print axioms Rcic.F3.StepWCheck.agreeAtDec_of_agreeAt_closed
#print axioms Rcic.F3.StepWCheck.walkAgree_congr
#print axioms Rcic.F3.StepWCheck.GroupWChecked
#print axioms Rcic.F3.StepWCheck.EnvWChecked
#print axioms Rcic.F3.StepWCheck.stepW_of_groupWChecked
#print axioms Rcic.F3.StepWCheck.stepW_of_checked
#print axioms Rcic.F3.StepWCheck.StepsWAlong
#print axioms Rcic.F3.StepWCheck.stepsWAlong_of_envWChecked
#print axioms Rcic.F3.StepWCheck.StepWChecked
#print axioms Rcic.F3.StepWCheck.partitionSteps_of_checked
#print axioms Rcic.F3.StepWCheck.decForallLt
#print axioms Rcic.F3.StepWCheck.instDecidableAgreeAtDec
#print axioms Rcic.F3.StepWCheck.instDecidableWalkAgree
#print axioms Rcic.F3.StepWCheck.TierF3WChecked
#print axioms Rcic.F3.StepWCheck.nodeStepRow_of_groupWChecked
#print axioms Rcic.F3.StepWCheck.walkG_of_coveredWChecked
#print axioms Rcic.F3.StepWCheck.steps_coveredWChecked
#print axioms Rcic.F3.StepWCheck.tierF3WChecked_of_abd
#print axioms Rcic.F3.StepWCheck.walkAgree_of_groupWChecked
#print axioms Rcic.F3.StepWCheck.walkG_of_envWChecked
#print axioms Rcic.F3.StepWCheck.steps_coveredWChecked_G
#print axioms Rcic.F3.StepWCheck.tierF3WChecked_of_ADG
#print axioms Rcic.F3.StepWCheck.partitionStepsG_of_checked
#print axioms Rcic.F3.StepWCheck.tierF3Uncond_of_AD_checked
#print axioms Rcic.F3.StepWCheck.tierF3_of_AD_checked
#print axioms Rcic.F3.StepWCheck.kernelSoundnessTierUncond_of_AD_checked
#print axioms Rcic.F3.StepWCheck.tierF3Uncond_of_checked
#print axioms Rcic.F3.StepWCheck.kernelSoundnessTierUncond_of_checked
#print axioms Rcic.F3.StepWCheck.StepWHypClosed
#print axioms Rcic.F3.StepWCheck.walkAgreeDec_of_walkAgree
#print axioms Rcic.F3.StepWCheck.stepWChecked_of_hyp_closed
#print axioms Rcic.F3.StepWCheck.agreeAtDec_of_agreeAt
#print axioms Rcic.F3.StepWCheck.walkAgreeDec_of_walkAgree_gen
#print axioms Rcic.F3.StepWCheck.stepWChecked_of_hyp
#print axioms Rcic.F3.StepWCheck.stepWChecked_eqW
