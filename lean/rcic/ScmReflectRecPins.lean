import rcic.ScmReflectPins

/-!
# Annex 26.30 step 2 — Lean `evalP` pins

Shared with the scm images of a record element type, a `cons` whose
tail is a list variable, and `field` as an operand of `add`.
`closure_claim` stays 0.

A duplicate key is a walker refusal (`[rcic_fold_inv_tag]`), measured
on the fold-VC corpus. It is not an `ATy` value.
-/

namespace Rcic.Scm.Reflect.RecPins
open Rcic.Scm.Reflect
open Rcic.Scm.Reflect.Pins

/-- The instantiate token schema `(k : int, l : str, n : int)`. -/
private def tokSchema : ATy :=
  .rec_ [("k", .int), ("l", .str), ("n", .int)]

/-- `nil` at that schema equals itself. -/
private def nilTok : AssertProp [] :=
  .eq (.nil (a := tokSchema)) (.nil (a := tokSchema))

/-- `not` of that equation. -/
private def nilTokNot : AssertProp [] := .not nilTok

/-- `cons(1, var 0)` where the variable denotes `[2]`. -/
private def consVarTail : AssertProp [.list .int] :=
  .eq (.cons (.litI 1) (.var 0 rfl))
      (.cons (.litI 1) (.cons (.litI 2) .nil))

private def envOneList : AEnv := [⟨.list .int, [2]⟩]

/-- The record `{d ↦ 0}`. -/
private def recD0 : AssertTerm [] .val :=
  .record ["d"] [⟨.int, .litI 0⟩]

/-- `add` of slot 0 and `1`. -/
private def addFieldHit : AssertProp [] :=
  .eq (.add (.field recD0 0) (.litI 1)) (.litI 1)

/-- `add` of a missing slot and `1`. -/
private def addFieldMiss : AssertProp [] :=
  .eq (.add (.field recD0 1) (.litI 1)) (.litI 1)

/-- `not` of an `add` whose other operand overflows. -/
private def addFieldOverflow : AssertProp [] :=
  .not (.eq (.add (.field recD0 0) (.add (.litI i64Max) (.litI 1))) (.litI 0))

theorem tokSchema_neq :
    ATy.beq tokSchema (.rec_ [("k", .int)]) = false := rfl

theorem nilTok_eval : evalP nilTok [] penv0 = some true := by decide

theorem nilTokNot_eval : evalP nilTokNot [] penv0 = some false := by decide

theorem consVarTail_eval :
    evalP consVarTail envOneList penv0 = some true := by decide

theorem consMistag_eval :
    evalP consVarTail [⟨.int, (0 : Int)⟩] penv0 = none := rfl

theorem addFieldHit_eval : evalP addFieldHit [] penv0 = some true := by
  simp [addFieldHit, recD0, evalP, denoteTerm, denoteFields, packVal, packList,
    unpackVal, noDupKeys, inI64, i64Min, i64Max] <;> decide

theorem addFieldMiss_eval : evalP addFieldMiss [] penv0 = none := by
  simp [addFieldMiss, recD0, evalP, denoteTerm, denoteFields, packVal, packList,
    unpackVal, noDupKeys]

theorem addFieldOverflow_eval : evalP addFieldOverflow [] penv0 = none := by
  simp [addFieldOverflow, recD0, evalP, denoteTerm, denoteFields, packVal, packList,
    unpackVal, noDupKeys, inI64, i64Min, i64Max] <;> decide

theorem nilTok_dec : decideProp nilTok [] penv0 = true := by decide

theorem nilTokNot_dec : decideProp nilTokNot [] penv0 = false := by decide

theorem consVarTail_dec :
    decideProp consVarTail envOneList penv0 = true := by decide

theorem consMistag_dec :
    decideProp consVarTail [⟨.int, (0 : Int)⟩] penv0 = false := rfl

theorem addFieldHit_dec : decideProp addFieldHit [] penv0 = true := by
  simp [decideProp, addFieldHit, recD0, evalP, denoteTerm, denoteFields, packVal,
    packList, unpackVal, noDupKeys, inI64, i64Min, i64Max] <;> decide

theorem addFieldMiss_dec : decideProp addFieldMiss [] penv0 = false := by
  simp [decideProp, addFieldMiss, recD0, evalP, denoteTerm, denoteFields, packVal,
    packList, unpackVal, noDupKeys]

theorem addFieldOverflow_dec : decideProp addFieldOverflow [] penv0 = false := by
  simp [decideProp, addFieldOverflow, recD0, evalP, denoteTerm, denoteFields, packVal,
    packList, unpackVal, noDupKeys, inI64, i64Min, i64Max] <;> decide

#print axioms tokSchema_neq
#print axioms nilTok_eval
#print axioms nilTokNot_eval
#print axioms consVarTail_eval
#print axioms consMistag_eval
#print axioms addFieldHit_eval
#print axioms addFieldMiss_eval
#print axioms addFieldOverflow_eval
#print axioms nilTok_dec
#print axioms nilTokNot_dec
#print axioms consVarTail_dec
#print axioms consMistag_dec
#print axioms addFieldHit_dec
#print axioms addFieldMiss_dec
#print axioms addFieldOverflow_dec

end Rcic.Scm.Reflect.RecPins
