import rcic.ScmReflectPins

/-!
# Annex 26.29 step 3 — Lean ↔ scm agreement pins

The ten rows are `apps/rcic-decide-prop-arm/rcic_decide_prop_arm_corpus.json`.
`rcic.decide_prop_arm` answers `bit = 1` on the four defined-true rows
and `bit = 0` on the six undefined rows. `decideProp` is that bit.
`evalP = none` is what makes a `bit = 0` row undefined rather than
defined-false. `closure_claim` stays 0.

`field_mistag` reads the shared record `{d ↦ 0}` at `bool`. Lean `eq`
is homogeneous, so its right-hand side is `litB false`. The scm row's
right-hand side is `int 0`. Both are undefined because the field is `none`.
-/

namespace Rcic.Scm.Reflect.ArmPins
open Rcic.Scm.Reflect
open Rcic.Scm.Reflect.Pins

def list1 : AssertTerm [] (.list .int) := .cons (.litI 1) .nil

/-- Corpus `snoc_defined`: `[1] ++ [2] = [1, 2]`. -/
def snocDefined : AssertProp [] :=
  .eq (.snoc list1 (.litI 2)) (.cons (.litI 1) (.cons (.litI 2) .nil))

/-- Corpus `not_defined`: `not (0 = 1)`, the defined control. -/
def notDefined : AssertProp [] := .not (.eq (.litI 0) (.litI 1))

/-- The record `{d ↦ 0, out ↦ 1}`. -/
def recDO : AssertTerm [] .val :=
  .record ["d", "out"] [⟨.int, .litI 0⟩, ⟨.int, .litI 1⟩]

/-- Corpus `record_ok`. -/
def recordOk : AssertProp [] := .eq recDO recDO

/-- The record `{d ↦ 0}`. -/
def recD : AssertTerm [] .val := .record ["d"] [⟨.int, .litI 0⟩]

/-- Corpus `field_hit`: slot 0 at `int` is `0`. -/
def fieldHit : AssertProp [] := .eq (.field recD 0) (.litI 0)

/-- Corpus `record_dup`: key `d` twice. -/
def recordDup : AssertProp [] :=
  .eq (.record ["d", "d"] [⟨.int, .litI 0⟩, ⟨.int, .litI 1⟩]) recDO

/-- Corpus `record_arity`: one key, two fields. -/
def recordArity : AssertProp [] :=
  .eq (.record ["d"] [⟨.int, .litI 0⟩, ⟨.int, .litI 1⟩]) recDO

/-- Corpus `field_miss`: slot 1 of a one-field record. -/
def fieldMiss : AssertProp [] := .eq (.field recD 1) (.litI 0)

/-- Corpus `field_mistag`: slot 0 read at `bool`. -/
def fieldMistag : AssertProp [] := .eq (.field recD 0) (.litB false)

/-- Corpus `snoc_not_undef`: `not` of a snoc whose element overflows. -/
def snocNotUndef : AssertProp [] :=
  .not (.eq (.snoc list1 (.add (.litI i64Max) (.litI 1)))
    (.cons (.litI 1) (.cons (.litI 0) .nil)))

/-- Corpus `record_not_undef`: `not` of a record whose field overflows. -/
def recordNotUndef : AssertProp [] :=
  .not (.eq (.record ["d"] [⟨.int, .add (.litI i64Max) (.litI 1)⟩])
    (.record ["d"] [⟨.int, .litI 0⟩]))

theorem snocDefined_eval : evalP snocDefined [] penv0 = some true := by decide
theorem notDefined_eval : evalP notDefined [] penv0 = some true := by decide
theorem recordOk_eval : evalP recordOk [] penv0 = some true := by
  simp [recordOk, recDO, evalP, denoteTerm, denoteFields, packVal, packList, noDupKeys]
theorem fieldHit_eval : evalP fieldHit [] penv0 = some true := by
  simp [fieldHit, recD, evalP, denoteTerm, denoteFields, packVal, packList, unpackVal, noDupKeys]
theorem recordDup_eval : evalP recordDup [] penv0 = none := rfl
theorem recordArity_eval : evalP recordArity [] penv0 = none := rfl
theorem fieldMiss_eval : evalP fieldMiss [] penv0 = none := rfl
theorem fieldMistag_eval : evalP fieldMistag [] penv0 = none := by
  simp [fieldMistag, recD, evalP, denoteTerm, denoteFields, packVal, packList, unpackVal, noDupKeys]
theorem snocNotUndef_eval : evalP snocNotUndef [] penv0 = none := rfl
theorem recordNotUndef_eval : evalP recordNotUndef [] penv0 = none := rfl

theorem snocDefined_dec : decideProp snocDefined [] penv0 = true := by decide
theorem notDefined_dec : decideProp notDefined [] penv0 = true := by decide
theorem recordOk_dec : decideProp recordOk [] penv0 = true := by
  simp [decideProp, recordOk, recDO, evalP, denoteTerm, denoteFields, packVal, packList, noDupKeys]
theorem fieldHit_dec : decideProp fieldHit [] penv0 = true := by
  simp [decideProp, fieldHit, recD, evalP, denoteTerm, denoteFields, packVal, packList, unpackVal, noDupKeys]
theorem recordDup_dec : decideProp recordDup [] penv0 = false := by decide
theorem recordArity_dec : decideProp recordArity [] penv0 = false := by decide
theorem fieldMiss_dec : decideProp fieldMiss [] penv0 = false := by decide
theorem fieldMistag_dec : decideProp fieldMistag [] penv0 = false := by
  simp [decideProp, fieldMistag, recD, evalP, denoteTerm, denoteFields, packVal, packList, unpackVal, noDupKeys]
theorem snocNotUndef_dec : decideProp snocNotUndef [] penv0 = false := by decide
theorem recordNotUndef_dec : decideProp recordNotUndef [] penv0 = false := by decide

theorem snocDefined_den : denoteP snocDefined [] penv0 =
    some (([(1 : Int)] ++ [2]) = [1, 2]) := rfl
theorem notDefined_den : denoteP notDefined [] penv0 =
    some (¬ ((0 : Int) = 1)) := rfl
theorem recordOk_den : denoteP recordOk [] penv0 =
    some (Val.r [Val.i 0, Val.i 1] = Val.r [Val.i 0, Val.i 1]) := by
  simp [recordOk, recDO, denoteP, denoteTerm, denoteFields, packVal, packList, noDupKeys]
theorem fieldHit_den : denoteP fieldHit [] penv0 = some ((0 : Int) = 0) := by
  simp [fieldHit, recD, denoteP, denoteTerm, denoteFields, packVal, packList, unpackVal, noDupKeys]
theorem recordDup_den : denoteP recordDup [] penv0 = none := rfl
theorem recordArity_den : denoteP recordArity [] penv0 = none := rfl
theorem fieldMiss_den : denoteP fieldMiss [] penv0 = none := rfl
theorem fieldMistag_den : denoteP fieldMistag [] penv0 = none := by
  simp [fieldMistag, recD, denoteP, denoteTerm, denoteFields, packVal, packList, unpackVal, noDupKeys]
theorem snocNotUndef_den : denoteP snocNotUndef [] penv0 = none := rfl
theorem recordNotUndef_den : denoteP recordNotUndef [] penv0 = none := rfl

/-- Labels and the `decideProp` bit shared with the arm corpus. -/
def armCorpus : List (String × Bool) :=
  [ ("snoc_defined", true)
  , ("not_defined", true)
  , ("record_ok", true)
  , ("field_hit", true)
  , ("record_dup", false)
  , ("record_arity", false)
  , ("field_miss", false)
  , ("field_mistag", false)
  , ("snoc_not_undef", false)
  , ("record_not_undef", false) ]

#print axioms snocDefined_eval
#print axioms notDefined_eval
#print axioms recordOk_eval
#print axioms fieldHit_eval
#print axioms recordDup_eval
#print axioms recordArity_eval
#print axioms fieldMiss_eval
#print axioms fieldMistag_eval
#print axioms snocNotUndef_eval
#print axioms recordNotUndef_eval
#print axioms snocDefined_dec
#print axioms notDefined_dec
#print axioms recordOk_dec
#print axioms fieldHit_dec
#print axioms recordDup_dec
#print axioms recordArity_dec
#print axioms fieldMiss_dec
#print axioms fieldMistag_dec
#print axioms snocNotUndef_dec
#print axioms recordNotUndef_dec
#print axioms snocDefined_den
#print axioms notDefined_den
#print axioms recordOk_den
#print axioms fieldHit_den
#print axioms recordDup_den
#print axioms recordArity_den
#print axioms fieldMiss_den
#print axioms fieldMistag_den
#print axioms snocNotUndef_den
#print axioms recordNotUndef_den

end Rcic.Scm.Reflect.ArmPins
