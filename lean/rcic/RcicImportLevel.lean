/-
Importer level slice. Const arguments admitted here are the fragment of
`levelBounded` that legacy `HasTy.const` can certify, except one pinned
shape.

R-CIC (`docs/rcic/02_DECLARATIVE_THEORY.md` §2, `levelBounded`) accepts
`zero`, `succ`, `max`, and `imax` when their children are bounded, and
`param i` iff `i < k`. The previous checker run's 248
`[rcic_infer_const_levels_out_of_slice]` rows are all `levelBounded` at
the failing member's own universe arity. None is `param i` with `i ≥ k`.

`levelArgAdmitted k l` is that fragment at `k > 0`, except exactly
`.succ .zero`:

* `param i` with `i < k` (hence `k > 0`);
* `zero`, `max`, and `imax` when `0 < k` and `levelBounded k`;
* `succ l` when `l ≠ zero`, `0 < k`, and `levelBounded k`.

Two walls stay on the one existing residue `constLevelResidue`. Both
are `levelBounded`. They are not a second residue id.

1. Universe arity 0. Legacy `HasTy.const` asks `rawConstOK`. At `n = 0`
   the `m < n` disjunct is empty, and a closed level is not
   `eval (fun _ => none) = none` (`not_rawConstOK_zero_zero`). The
   landed pins `pin_inf_row08` and `pin_inf_row15` require
   `.const _ [.zero]` at univs 0 to refuse this residue before lookup.
   Passing a larger `n` would be a different judgment.
2. The const argument `.succ .zero` at every universe bound.
   `inferCert_const62_no` quantifies over every environment and every
   `n`, and its proof is `nomatch`, so this arm stays the literal
   `false`. `checkxNthBNilVa_n0` / `_n1` pin `BL.rec.{1}` to this
   residue at both bounds. `succ (succ zero)` and `succ (param i)` are
   not that shape.

`hwf` for an admitted nonempty list is the `n > 0` vacuity (`m = 0`),
not openness. An admitted `zero` is closed.

q stays the landed `Rcic.LeanImport.stmtQ` / `bodyQ`. This file does
not import them and does not write them. Proof-irrelevance
representation, universe cumulativity, and elaboration artefacts are
not inputs, so this slice does not put them into either identity.
`imax` is admitted only as a bounded const argument at `k > 0`. It is
not folded into q. The landed `encLevel` spelling is untouched.

`closure_claim = 0`. Emission of this def is requested from
`ResiduaRCCLeanToScm` (PR #7973). That emitter is absent on this base,
so `[chain_scm_not_emitted]`. No scm is written here.
-/
import rcic.RcicDeclarative

namespace Rcic.ImportLevel

open Rcic.Declarative

/-- Lean is the first frontend. A later frontend is another instance. -/
def frontend : String := "lean"

/-- Residue for a const level argument outside `constLevelsAdmitted`. -/
def constLevelResidue : String := "[rcic_infer_const_levels_out_of_slice]"

/-- Wall 2. `.succ .zero` is `levelBounded` and still refused, at every `k`. -/
def notSuccZero : Level → Bool
  | .succ .zero => false
  | .zero => true
  | .succ _ => true
  | .max _ _ => true
  | .imax _ _ => true
  | .param _ => true

/-- `k` is the declaration's universe-parameter count.
The first conjunct is wall 2, so `.succ .zero` reduces to `false`
at a symbolic `k` (`inferCert_const62_no`). -/
def levelArgAdmitted (k : Nat) (l : Level) : Bool :=
  notSuccZero l && decide (0 < k) && levelBounded k l

def constLevelsAdmitted (k : Nat) : List Level → Bool
  | [] => true
  | l :: ls => levelArgAdmitted k l && constLevelsAdmitted k ls

theorem zero_refused_at_zero : levelArgAdmitted 0 .zero = false := rfl

theorem zero_admitted : levelArgAdmitted 1 .zero = true := rfl

theorem succ_zero_refused (k : Nat) :
    levelArgAdmitted k (.succ .zero) = false := rfl

theorem param_hi_refused {k i : Nat} (h : k ≤ i) :
    levelArgAdmitted k (.param i) = false := by
  simp [levelArgAdmitted, notSuccZero, levelBounded,
    decide_eq_false (Nat.not_lt.mpr h)]

theorem param_admitted {k i : Nat} (h : i < k) :
    levelArgAdmitted k (.param i) = true := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le i) h
  simp [levelArgAdmitted, notSuccZero, levelBounded, hk, h]

/- Measured const-argument lists. Indices are the use site's own
parameter positions: Eq.refl is `[p0]` at arity 1, Eq.rec is `[p1]` at
arity 2, Prod.mk is `[p0,p1]` at arity 2, Prod.rec is `[p1,p2]` at arity 3.
List, HEq, Option match Eq. Sum matches Prod. -/

theorem frontend_lean : frontend = "lean" := rfl

theorem constLevelResidue_name :
    constLevelResidue = "[rcic_infer_const_levels_out_of_slice]" := rfl

theorem shape_eq_refl : constLevelsAdmitted 1 [.param 0] = true := rfl

theorem shape_eq_rec : constLevelsAdmitted 2 [.param 1] = true := rfl

theorem shape_prod_mk : constLevelsAdmitted 2 [.param 0, .param 1] = true := rfl

theorem shape_prod_rec : constLevelsAdmitted 3 [.param 1, .param 2] = true := rfl

theorem shape_zero_list : constLevelsAdmitted 1 [.zero] = true := rfl

theorem shape_zero_at_zero : constLevelsAdmitted 0 [.zero] = false := rfl

theorem shape_succ_zero : constLevelsAdmitted 1 [.succ .zero] = false := rfl

theorem shape_succ_zero_pos : constLevelsAdmitted 2 [.succ .zero] = false := rfl

theorem shape_succ_param : constLevelsAdmitted 2 [.succ (.param 0)] = true := rfl

theorem shape_imax : constLevelsAdmitted 2 [.imax (.param 0) (.param 1)] = true := rfl

theorem shape_max_succ :
    constLevelsAdmitted 2 [.max (.succ (.param 0)) (.succ (.param 1))] = true := rfl

theorem shape_imax_at_zero :
    constLevelsAdmitted 0 [.imax (.param 0) (.param 1)] = false := rfl

private theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl

private theorem and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => cases h
  | true => exact h

/-- Admitted arguments are inside `levelBounded`. The converse is the two walls. -/
theorem levelArg_bounded {k : Nat} {l : Level}
    (h : levelArgAdmitted k l = true) : levelBounded k l = true := by
  unfold levelArgAdmitted at h
  exact and_right h

theorem constLevels_bounded {k : Nat} {ls : List Level}
    (h : constLevelsAdmitted k ls = true) : levelsBounded k ls = true := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      simp only [constLevelsAdmitted, levelsBounded, Bool.and_eq_true] at h ⊢
      exact ⟨levelArg_bounded h.1, ih h.2⟩

theorem wall_arity_zero :
    levelBounded 0 .zero = true ∧ levelArgAdmitted 0 .zero = false :=
  ⟨rfl, zero_refused_at_zero⟩

theorem wall_succ_zero (k : Nat) :
    levelBounded k (.succ .zero) = true ∧ levelArgAdmitted k (.succ .zero) = false :=
  ⟨rfl, succ_zero_refused k⟩

theorem levelArgAdmitted_pos {k : Nat} {l : Level}
    (h : levelArgAdmitted k l = true) : 0 < k := by
  unfold levelArgAdmitted at h
  exact of_decide_eq_true (and_right (and_left h))

/-- Nonempty admitted lists have `k > 0`, so `m = 0` discharges `HasTy.const`.
An empty list is the separate `hwf_of_ls` arm. This is not `levelsOpen`:
an admitted `.zero` is closed. -/
theorem constLevels_hwf {k : Nat} {ls : List Level}
    (h : constLevelsAdmitted k ls = true) :
    ∀ l ∈ ls, ∃ m, eval (fun _ => none) l = none ∨ m < k := by
  cases ls with
  | nil =>
      intro l hl
      cases hl
  | cons hd tl =>
      simp only [constLevelsAdmitted] at h
      have hk : 0 < k := levelArgAdmitted_pos (and_left h)
      intro l hl
      exact ⟨0, Or.inr hk⟩

end Rcic.ImportLevel
