import Lean

/-!
# Checked syntax boundary for recursive universe relation indices

The two guarded declarations record the exact Lean kernel rejections of
recursion through a constructor's result relation index. Neither example
uses nested `Exists`, so the result is independent of Lean's separate
restriction on nested existential parameters.

The accepted fixed-carrier example then puts all recursive occurrences
in positive premises with an explicit relation-valued decoder. Its
induction theorem records the self-decoding obstruction at `none`.
These are restrictions of the proposed declaration methods, not a
refutation of expanded universes or the admitted source model class.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.InductiveUniverseSyntaxProbe

abbrev Value := Nat
abbrev Relation := Value → Value → Prop

namespace Direct

/--
error: (kernel) invalid return type for 'Rcic.Declarative.Ann.LR3.InductiveUniverseSyntaxProbe.Direct.CodeI.universe'
-/
#guard_msgs in
inductive CodeI : Option Nat → Value → Relation → Prop
  | universe (k : Option Nat) :
      CodeI (k.map Nat.succ) 0
        (fun x _ => CodeI k x (fun _ _ => True))

end Direct

namespace Mutual

/--
error: (kernel) invalid return type for 'Rcic.Declarative.Ann.LR3.InductiveUniverseSyntaxProbe.Mutual.CodeI.universe'
-/
#guard_msgs in
mutual
  inductive CodeI : Option Nat → Value → Relation → Prop
    | universe (k : Option Nat) : CodeI (k.map Nat.succ) 0 (UniverseI k)
  inductive UniverseI : Option Nat → Value → Value → Prop
    | pair {k : Option Nat} {x y : Value} {R : Relation}
        (hx : CodeI k x R) (hy : CodeI k y R) : UniverseI k x y
end

end Mutual

namespace Positive

/-- The proposed universe carrier is an external fixed parameter, and
the decoder relation is supplied explicitly rather than chosen from Prop. -/
inductive CodeU (U : Option Nat → Relation) : Option Nat → Value → Relation → Prop
  | atom {k : Option Nat} {x : Value} {R : Relation} (hx : x ≠ 0) : CodeU U k x R
  | univ (k : Option Nat) (decoded : Value → Relation)
      (decode : ∀ x, U k x x → CodeU U k x (decoded x)) :
      CodeU U (k.map Nat.succ) 0 (U k)

theorem no_code_at_none {U : Option Nat → Relation} (hself : U none 0 0)
    {k : Option Nat} {x : Value} {R : Relation} (h : CodeU U k x R) :
    k = none → x = 0 → False := by
  induction h with
  | atom hx =>
    intro _ hx0
    exact hx hx0
  | univ k decoded decode ih =>
    intro hk _
    cases k with
    | none => exact ih 0 hself rfl rfl
    | some n => cases hk

theorem none_universe_not_code {U : Option Nat → Relation}
    (hself : U none 0 0) {R : Relation} : ¬ CodeU U none 0 R := by
  intro h
  exact no_code_at_none hself h rfl rfl

/-- The positive inductive relation still has ordinary codes at `none`;
the obstruction specifically concerns its self-decoding universe value. -/
theorem ordinary_none_code (U : Option Nat → Relation) :
    CodeU U none 1 (fun _ _ => True) := .atom (by decide)

end Positive

end Rcic.Declarative.Ann.LR3.InductiveUniverseSyntaxProbe
