import rcic.RcicAnnLR3EnvironmentEvalComposition
import rcic.RcicAnnLR3UnitLevels
import rcic.RcicAnnKEqPositive

/-!
# Actual Eq evaluation for the tagged K coherence check

The hook is the inherited compositional Eq/refl/J interpretation. It
preserves both the open large-K conversion at the supplied proof-unit
environment and constructor-major iota. No special call lookup or constant
recursor result is introduced. The source major is stuck; its supplied
semantic realization is the nonbottom unit, not a semantic neutral.

This is a scoped evaluator control, not a general recursor supplier.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
namespace Rcic.Declarative.Ann.LR3.TaggedKEvaluation
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

def eqSyntax : EnvironmentEval.FamilySyntax :=
  fun _ r _ _ => constantTerm r

def LiteralFree : ExprA → Prop
  | .bvar _ | .sort _ | .const _ _ => True
  | .app f a => LiteralFree f ∧ LiteralFree a
  | .lam A _ b => LiteralFree A ∧ LiteralFree b
  | .pi A _ B _ => LiteralFree A ∧ LiteralFree B
  | .letE A v b => LiteralFree A ∧ LiteralFree v ∧ LiteralFree b
  | .lit _ => False

theorem definition_none (r : Nat) (ls : List Level) :
    EnvironmentEval.definitionBody EqLargeFixture.env r ls = none := by
  by_cases h65 : r = 65
  · subst r; rfl
  by_cases h64 : r = 64
  · subst r; rfl
  by_cases h63 : r = 63
  · subst r; rfl
  simp [EnvironmentEval.definitionBody, EqLargeFixture.env, EqLargeFixture.prefixEnv,
    EqLargeFixture.famEnv, extendEnvA, emptyEnvA, h65, h64, h63]

theorem rigid_image (ν : Valuation) (r : Nat) (ls : List Level) :
    EnvironmentEval.rigidTerm EqLargeFixture.env eqSyntax ν r ls = constantTerm r := by
  by_cases h65 : r = 65
  · subst r; rfl
  by_cases h64 : r = 64
  · subst r; rfl
  by_cases h63 : r = 63
  · subst r; rfl
  simp [EnvironmentEval.rigidTerm, EqLargeFixture.env, EqLargeFixture.prefixEnv,
    EqLargeFixture.famEnv, extendEnvA, emptyEnvA, h65, h64, h63, constantTerm]

theorem translation_below {ν : Valuation} {e : ExprA} {t : Expr Nat}
    (ht : EnvironmentEval.Translation EqLargeFixture.env eqSyntax ν e t) :
    LiteralFree e → EnvironmentEval.NativeBelow t (translate ν e) := by
  induction ht with
  | cut e => exact fun _ => .cut _
  | bvar i => exact fun _ => .refl _
  | sort l => exact fun _ => .refl _
  | constBody hb _ _ => rw [definition_none] at hb; cases hb
  | constRigid hr =>
      intro _
      rw [rigid_image]
      exact .refl _
  | app _ _ ihf iha => exact fun h => .app (ihf h.1) (iha h.2)
  | lam _ _ _ ihb => exact fun h => .lam (ihb h.2)
  | pi _ _ ihA ihB => exact fun h => .tagged _ (.pi (ihA h.1) (ihB h.2))
  | letE _ _ _ _ ihv ihb => exact fun h => .letE (ihv h.2.1) (ihb h.2.2)
  | lit _ _ => exact fun h => False.elim h

theorem full_translation (ν : Valuation) {e : ExprA} (he : LiteralFree e) :
    EnvironmentEval.Translation EqLargeFixture.env eqSyntax ν e (translate ν e) := by
  induction e with
  | bvar i => exact .bvar i
  | sort l => exact .sort l
  | const r ls =>
      simpa only [translate, rigid_image] using
        (EnvironmentEval.Translation.constRigid
          (E := EqLargeFixture.env) (F := eqSyntax) (ν := ν) (definition_none r ls))
  | app f a ihf iha => exact .app (ihf he.1) (iha he.2)
  | lam A u b ihA ihb => exact .lam (ihA he.1) (ihb he.2)
  | pi A u B v ihA ihB => exact .pi (ihA he.1) (ihB he.2)
  | letE A v b ihA ihv ihb => exact .letE (ihA he.1) (ihv he.2.1) (ihb he.2.2)
  | lit t => exact False.elim he

theorem denote_agrees (ν : Valuation) (ρ : EnvI) {e : ExprA} (he : LiteralFree e) :
    ValueEq (EnvironmentEval.denote EqLargeFixture.env eqSyntax ν ρ e)
      (UnitModel.denote ν ρ e) := by
  intro c
  constructor
  · rintro ⟨t, ht, hc⟩
    exact translation_below ht he ρ c hc
  · intro hc
    exact ⟨_, full_translation ν he, hc⟩

theorem call_literalFree : LiteralFree (EqLargeFixture.call (.bvar 0)) := by trivial
theorem result_literalFree : LiteralFree EqLargeFixture.result := by trivial
theorem parameter_literalFree : LiteralFree EqLargeFixture.parameter := by trivial
theorem canonical_literalFree :
    LiteralFree StrictProofModelBoundary.canonicalCallA3 := by trivial

abbrev image (ν : Valuation) (ρ : EnvI) (e : ExprA) : Value :=
  EnvironmentEval.denote EqLargeFixture.env eqSyntax ν ρ e

theorem open_call_image (ν : Valuation) :
    ValueEq (image ν fixtureEnv (EqLargeFixture.call (.bvar 0)))
      (image ν fixtureEnv EqLargeFixture.result) :=
  (denote_agrees ν fixtureEnv call_literalFree).trans
    ((open_conversion_sound (fixtureEnv_fits ν)).trans
      (denote_agrees ν fixtureEnv result_literalFree).symm)

theorem canonical_call_image (ν : Valuation) (ρ : EnvI) :
    ValueEq (image ν ρ StrictProofModelBoundary.canonicalCallA3)
      (image ν ρ EqLargeFixture.result) :=
  (denote_agrees ν ρ canonical_literalFree).trans
    ((canonical_iota_sound ν ρ).trans (denote_agrees ν ρ result_literalFree).symm)

theorem parameter_guard (ν : Valuation) :
    SortPER (some 0) (image ν fixtureEnv EqLargeFixture.parameter)
      (image ν fixtureEnv EqLargeFixture.parameter) := by
  have he := denote_agrees ν fixtureEnv parameter_literalFree
  exact ⟨sortMember_congr he.symm (fixture_parameter_member ν fixtureEnv),
    typeDefined_congr he.symm (fixture_parameter_defined ν fixtureEnv), ValueEq.refl _⟩

theorem result_level (ν : Valuation) :
    SortMember (some 1) (image ν fixtureEnv EqLargeFixture.result) :=
  sortMember_congr (denote_agrees ν fixtureEnv result_literalFree).symm
    (fixture_result_member ν fixtureEnv)

theorem result_defined (ν : Valuation) :
    TypeDefined (image ν fixtureEnv EqLargeFixture.result) :=
  typeDefined_congr (denote_agrees ν fixtureEnv result_literalFree).symm
    (fixture_result_defined ν fixtureEnv)

theorem call_level (ν : Valuation) :
    SortMember (some 1) (image ν fixtureEnv (EqLargeFixture.call (.bvar 0))) :=
  sortMember_congr (open_call_image ν).symm (result_level ν)

theorem call_defined (ν : Valuation) :
    TypeDefined (image ν fixtureEnv (EqLargeFixture.call (.bvar 0))) :=
  typeDefined_congr (open_call_image ν).symm (result_defined ν)

theorem major_is_unit (ν : Valuation) :
    ValueEq (image ν fixtureEnv (.bvar 0)) (unitValue fixtureEnv) :=
  (denote_agrees ν fixtureEnv (e := .bvar 0) True.intro).trans (major_unit (fixtureEnv_fits ν))

theorem major_nonbottom (ν : Valuation) :
    ¬ ValueEq (image ν fixtureEnv (.bvar 0)) bottom :=
  fun h => unit_nonbottom fixtureEnv ((major_is_unit ν).symm.trans h)

end Rcic.Declarative.Ann.LR3.TaggedKEvaluation
