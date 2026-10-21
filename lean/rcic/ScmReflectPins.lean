import rcic.ScmReflect
import rcic.ScmCore

/-!
# CT-012 pins — the shared `decideProp` corpus

The labelled rows below are the corpus contract shared with grok C's
scm `decideProp` (the scm side mirrors every label with the same
fixture and the same expected verdict — the `ScmAllow`-segment
convention). Three layers are pinned per row:

* `evalP` — the strict evaluator verdict (`some true`, `some false`,
  `none`),
* `decideProp` — the §14 decision bit (`true` iff defined-true),
* `denoteP`/`denoteProp` — the strict denotation (`none` iff undefined;
  defined rows carry their witness).

All rows are kernel-checkable (`rfl`/`decide`) — `evalP` is pure:
no `String.splitOn`-style extern step enters its reduction.

## Amendment teeth (cc on #6392)

`ct012_r30_not_overflow`, `ct012_r31_not_pcall_unknown` and
`ct012_r33_impl_undef` are the strict-partiality teeth:
`not (eq overflow 0)`, `not (pcall unknown)` and
`impl (eq overflow 0) X` must decide **false**, not true —
undefinedness propagates through negation and implication, even with a
defined-true consequent.
-/

namespace Rcic.Scm.Reflect.Pins
open Rcic.Scm.Reflect

/-! ## Fixtures -/

/-- Empty predicate environment. -/
def penv0 : PredEnv := fun _ => none

/-- The positive-int decider. -/
def posDec : List (Sigma denTy) → Bool
  | [⟨.int, n⟩] => decide (0 < n)
  | _ => false

/-- The positive-int denotation. -/
def posDen : List (Sigma denTy) → Prop
  | [⟨.int, n⟩] => (0 : Int) < n
  | _ => False

/-- The certificate: decider and denotation agree. -/
theorem posCert : ∀ a, posDec a = true ↔ posDen a := by
  intro a
  rcases a with _ | ⟨x, rest⟩
  · simp [posDec, posDen]
  rcases rest with _ | ⟨y, _rest2⟩
  · rcases x with ⟨T, v⟩
    cases T <;> simp [posDec, posDen]
  · simp [posDec, posDen]

/-- The certified positive-int predicate: 1 arg, `0 < n`. -/
def posPred : CertifiedPred where
  nargs := 1
  dec := posDec
  den := posDen
  cert := posCert

/-- A one-entry predicate environment: `"pos"` ↦ `posPred`. -/
def penv1 : PredEnv := fun q => if q = "pos" then some posPred else none

/-- Three-element int list fixture. -/
def xs123 : AssertTerm [] (.list .int) :=
  .cons (.litI 1) (.cons (.litI 2) (.cons (.litI 3) .nil))

/-- Two-element int list fixture. -/
def xs15 : AssertTerm [] (.list .int) :=
  .cons (.litI 1) (.cons (.litI 5) .nil)

/-- Int environment with `x₀ = 5` (for the `Γ = [.int]` rows). -/
def env5 : AEnv := [⟨.int, 5⟩]

/-- Mistagged environment (`Bool` where `int` is declared). -/
def envBad : AEnv := [⟨.bool, true⟩]

/-! ## Defined-true rows (`evalP = some true`, `decideProp = true`) -/

def r01 : AssertProp [] := .eq (.litI 3) (.litI 3)
def r02 : AssertProp [] := .lt (.litI 1) (.litI 2)
def r03 : AssertProp [] := .le (.litI 2) (.litI 2)
def r04 : AssertProp [] := .and (.eq (.litI 1) (.litI 1)) (.lt (.litI 1) (.litI 2))
def r05 : AssertProp [] := .or (.lt (.litI 2) (.litI 1)) (.eq (.litI 1) (.litI 1))
def r06 : AssertProp [] := .not (.lt (.litI 2) (.litI 1))
def r07 : AssertProp [] := .impl (.lt (.litI 2) (.litI 1)) (.eq (.litI 1) (.litI 1))
def r08 : AssertProp [.int] := .eq (.var 0 rfl) (.litI 5)
def r09 : AssertProp [] := .allIn xs123 (.le (.var 0 rfl) (.litI 3))
def r10 : AssertProp [] := .exIn xs123 (.eq (.var 0 rfl) (.litI 2))
def r11 : AssertProp [] := .isInl (.inl (b := .bool) (.litI 7))
def r12 : AssertProp [] := .isInr (.inr (a := .int) (.litB true))
def r13 : AssertProp [] := .pcall "pos" [⟨.int, .litI 4⟩]
def r14 : AssertProp [] := .eq (.litV (.i 5)) (.litV (.i 5))
def r15 : AssertProp [] := .eq (.litS "a") (.litS "a")
def r16 : AssertProp [] := .eq (.pair (.litI 1) (.litB true)) (.pair (.litI 1) (.litB true))
def r17 : AssertProp [] := .eq (.fst (.pair (.litI 7) (.litB true))) (.litI 7)
def r18 : AssertProp [] := .eq (.sub (.litI 5) (.litI 3)) (.litI 2)

/-! ## Defined-false rows (`evalP = some false`, `decideProp = false`) -/

def r19 : AssertProp [] := .eq (.litI 3) (.litI 4)
def r20 : AssertProp [] := .allIn xs15 (.le (.var 0 rfl) (.litI 3))
def r21 : AssertProp [] := .pcall "pos" [⟨.int, .litI (-3)⟩]
def r22 : AssertProp [] := .impl (.eq (.litI 1) (.litI 1)) (.lt (.litI 2) (.litI 1))

/-! ## Undefined rows (`evalP = none`, `denoteP = none`, `decideProp = false`) -/

def r23 : AssertProp [.int] := .eq (.var 0 rfl) (.litI 5)      -- env [] : lookup miss
def r24 : AssertProp [.int] := .eq (.var 0 rfl) (.litI 5)      -- envBad : tag mismatch
def r25 : AssertProp [] := .eq (.add (.litI i64Max) (.litI 1)) (.litI 0)
def r26 : AssertProp [] := .pcall "nope" []
def r27 : AssertProp [] := .pcall "pos" [⟨.int, .litI 4⟩, ⟨.int, .litI 4⟩]
def r28 : AssertProp [] := .pcall "pos" [⟨.bool, .litB true⟩]
def r29 : AssertProp [] :=
  .allIn xs123 (.lt (.var 0 rfl) (.add (.litI i64Max) (.litI 1)))
def r30 : AssertProp [] := .not (.eq (.add (.litI i64Max) (.litI 1)) (.litI 0))
def r31 : AssertProp [] := .not (.pcall "nope" [])
def r32 : AssertProp [] :=
  .exIn xs123 (.eq (.var 0 rfl) (.add (.litI i64Max) (.litI 1)))
def r33 : AssertProp [] :=
  .impl (.eq (.add (.litI i64Max) (.litI 1)) (.litI 0)) (.eq (.litI 1) (.litI 1))

/-! ## Verdict pins — `evalP` layer -/

theorem r01_eval : evalP r01 [] penv0 = some true := by decide
theorem r02_eval : evalP r02 [] penv0 = some true := by decide
theorem r03_eval : evalP r03 [] penv0 = some true := by decide
theorem r04_eval : evalP r04 [] penv0 = some true := by decide
theorem r05_eval : evalP r05 [] penv0 = some true := by decide
theorem r06_eval : evalP r06 [] penv0 = some true := by decide
theorem r07_eval : evalP r07 [] penv0 = some true := by decide
theorem r08_eval : evalP r08 env5 penv0 = some true := by decide
theorem r09_eval : evalP r09 [] penv0 = some true := by decide
theorem r10_eval : evalP r10 [] penv0 = some true := by decide
theorem r11_eval : evalP r11 [] penv0 = some true := rfl
theorem r12_eval : evalP r12 [] penv0 = some true := rfl
theorem r13_eval : evalP r13 [] penv1 = some true := by decide
theorem r14_eval : evalP r14 [] penv0 = some true := by decide
theorem r15_eval : evalP r15 [] penv0 = some true := by decide
theorem r16_eval : evalP r16 [] penv0 = some true := by decide
theorem r17_eval : evalP r17 [] penv0 = some true := by decide
theorem r18_eval : evalP r18 [] penv0 = some true := by decide

theorem r19_eval : evalP r19 [] penv0 = some false := by decide
theorem r20_eval : evalP r20 [] penv0 = some false := by decide
theorem r21_eval : evalP r21 [] penv1 = some false := by decide
theorem r22_eval : evalP r22 [] penv0 = some false := by decide

theorem r23_eval : evalP r23 [] penv0 = none := rfl
theorem r24_eval : evalP r24 envBad penv0 = none := rfl
theorem r25_eval : evalP r25 [] penv0 = none := rfl
theorem r26_eval : evalP r26 [] penv1 = none := rfl
theorem r27_eval : evalP r27 [] penv1 = none := rfl
theorem r28_eval : evalP r28 [] penv1 = some false := by decide
theorem r29_eval : evalP r29 [] penv0 = none := rfl
theorem r30_eval : evalP r30 [] penv0 = none := rfl
theorem r31_eval : evalP r31 [] penv1 = none := rfl
theorem r32_eval : evalP r32 [] penv0 = none := rfl
theorem r33_eval : evalP r33 [] penv0 = none := rfl

/-! ## Verdict pins — `decideProp` layer -/

theorem r01_dec : decideProp r01 [] penv0 = true := by decide
theorem r08_dec : decideProp r08 env5 penv0 = true := by decide
theorem r13_dec : decideProp r13 [] penv1 = true := by decide
theorem r19_dec : decideProp r19 [] penv0 = false := by decide
theorem r20_dec : decideProp r20 [] penv0 = false := by decide
theorem r21_dec : decideProp r21 [] penv1 = false := by decide
theorem r23_dec : decideProp r23 [] penv0 = false := by decide
theorem r25_dec : decideProp r25 [] penv0 = false := by decide
theorem r26_dec : decideProp r26 [] penv1 = false := by decide
/-- The amendment tooth: `not (eq overflow 0)` decides **false** —
    undefinedness propagates through negation. -/
theorem r30_dec : decideProp r30 [] penv0 = false := by decide
/-- The amendment tooth: `not (pcall unknown)` decides **false**. -/
theorem r31_dec : decideProp r31 [] penv1 = false := by decide
theorem r32_dec : decideProp r32 [] penv0 = false := by decide
/-- The amendment tooth: `impl (eq overflow 0) X` decides **false** —
    the undefined antecedent is not rescued by a true consequent. -/
theorem r33_dec : decideProp r33 [] penv0 = false := by decide

/-! ## Verdict pins — denotation layer -/

theorem r01_den : denoteProp r01 [] penv0 := ⟨3 = 3, rfl, rfl⟩
theorem r08_den : denoteProp r08 env5 penv0 := ⟨5 = 5, rfl, rfl⟩
theorem r09_den : denoteProp r09 [] penv0 :=
  ⟨∀ x ∈ [(1:Int), 2, 3], ∃ Q,
      denoteP (AssertProp.le (.var 0 rfl) (.litI 3) : AssertProp [.int])
          [⟨.int, x⟩] penv0 = some Q ∧ Q,
   rfl, fun x hx => by
    simp at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨(1:Int) ≤ 3, rfl, by decide⟩
    · exact ⟨(2:Int) ≤ 3, rfl, by decide⟩
    · exact ⟨(3:Int) ≤ 3, rfl, by decide⟩⟩
theorem r13_den : denoteProp r13 [] penv1 :=
  ⟨_, rfl, show (0:Int) < 4 by decide⟩
theorem r19_den : denoteP r19 [] penv0 = some ((3:Int) = 4) := rfl
theorem r21_den : denoteP r21 [] penv1 = some ((0:Int) < -3) := rfl
theorem r23_den : denoteP r23 [] penv0 = none := rfl
theorem r24_den : denoteP r24 envBad penv0 = none := rfl
theorem r25_den : denoteP r25 [] penv0 = none := rfl
theorem r26_den : denoteP r26 [] penv1 = none := rfl
theorem r27_den : denoteP r27 [] penv1 = none := rfl
theorem r30_den : denoteP r30 [] penv0 = none := rfl
theorem r31_den : denoteP r31 [] penv1 = none := rfl
theorem r33_den : denoteP r33 [] penv0 = none := rfl

/-! ## The corpus table (labels ↔ expected `decideProp` verdict) -/

/-- One corpus row's shared expectation: label + `decideProp` verdict.
    `false` covers both defined-false and undefined rows — the scm side
    can distinguish them on `evalP`, and the Lean side pins it in the
    `evalP`/`denoteP` theorem layers above. -/
def corpus : List (String × Bool) :=
  [ ("ct012_r01_eq_true", true)
  , ("ct012_r02_lt_true", true)
  , ("ct012_r03_le_true", true)
  , ("ct012_r04_and_true", true)
  , ("ct012_r05_or_true", true)
  , ("ct012_r06_not_true", true)
  , ("ct012_r07_impl_true", true)
  , ("ct012_r08_var_hit", true)
  , ("ct012_r09_allIn_true", true)
  , ("ct012_r10_exIn_true", true)
  , ("ct012_r11_isInl_true", true)
  , ("ct012_r12_isInr_true", true)
  , ("ct012_r13_pcall_ok", true)
  , ("ct012_r14_eqval_true", true)
  , ("ct012_r15_eqstr_true", true)
  , ("ct012_r16_prod_eq", true)
  , ("ct012_r17_fst_proj", true)
  , ("ct012_r18_sub_ok", true)
  , ("ct012_r19_eq_false", false)
  , ("ct012_r20_allIn_false", false)
  , ("ct012_r21_pcall_rej", false)
  , ("ct012_r22_impl_false", false)
  , ("ct012_r23_var_miss", false)
  , ("ct012_r24_var_mistag", false)
  , ("ct012_r25_overflow", false)
  , ("ct012_r26_pcall_unknown", false)
  , ("ct012_r27_pcall_arity", false)
  , ("ct012_r28_pcall_argty", false)
  , ("ct012_r29_allIn_undef", false)
  , ("ct012_r30_not_overflow", false)
  , ("ct012_r31_not_pcall_unknown", false)
  , ("ct012_r32_exIn_undef", false)
  , ("ct012_r33_impl_undef", false) ]

end Rcic.Scm.Reflect.Pins
