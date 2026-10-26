import rcic.RcicFamAppRevPiRow
import rcic.RcicFamAppRevFamRow
import rcic.RcicClassCRevealed

/-!
# RcicFamAppRevFixture — the class-B fixture is an instance of the generic revealed singleton

`riEnv` (`RI : Sort 0 → Sort 0`, `mk : Π X, RI X`, AnySort recursor) is the generic environment `RevEnv` at
`f = 0`, `I = Sort 0`, over the empty base: every field is `rfl` or vacuous. So the fixture's Π row has a
second basis, the generic theorem (`riPiRow_generic`), beside `RcicFamAppPiRow.riPiRow` (the hand-built
copy-only twin), and its three rows a second basis (`riTypedRowsWf_generic`) beside `riTypedRowsWf`. Two independent derivations of the same row agree — the evidence class the gate rule asks
for, at the fixture. closure_claim = 0.
-/

namespace Rcic.Syn.FamApp.Rev

open Rcic.Declarative
open Rcic.Syn.ClassC
open Rcic.Syn.FamApp.RevTwin

/-- the class-B fixture's base: the empty environment, index type `Sort 0`. -/
def riRevBase : RevBase where
  E₀ := emptyEnv
  hW₀ := .empty
  hP₀ := trivial
  f := 0
  hf0 := rfl
  hf2 := rfl
  hlow := fun _ _ h => Option.noConfusion h
  I := .sort .zero
  uI := .succ .zero
  hI := .sort [] .zero
  hclI := fun _ => rfl
  hlvlI := rfl
  huI := rfl

/-- **`riEnv` is a revealed singleton over the empty base**: the generic environment at `f = 0`, `I = Sort 0`. -/
def riRevEnv : RevEnv where
  toRevBase := riRevBase
  E := riEnv
  hW := riEnvWfT
  hbase := fun r hr => absurd hr (Nat.not_lt_zero r)
  hEf := rfl
  hEf1 := rfl
  hEf2 := rfl
  habove := fun r hr => by
    rw [riEnv_members, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- the fixture's Π row by the generic theorem: a second basis for `riPiRow`. -/
theorem riPiRow_generic (n : Nat) : PiRowField riEnv n := riRevEnv.revPiRow n

/-- the fixture's sort row by the generic theorem (a third basis beside `riSortRow` and the shadow). -/
theorem riSortRow_generic {n : Nat} {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {u v : Level}
    (h : TyConvT riEnv n Γ (.sort u) (.sort v)) : eqN u v :=
  riRevEnv.revSortRow hΓ h

/-- the fixture's three rows by the generic theorem: a second basis for `riTypedRowsWf`
    (`RcicFamAppPiRow`, through the hand-built twin and the landed reduction `riTypedRowsWf_of_piRow`). -/
theorem riTypedRowsWf_generic (n : Nat) : TypedRowsWf riEnv n := riRevEnv.revTypedRowsWf n

end Rcic.Syn.FamApp.Rev

#print axioms Rcic.Syn.FamApp.Rev.riRevEnv
#print axioms Rcic.Syn.FamApp.Rev.riPiRow_generic
#print axioms Rcic.Syn.FamApp.Rev.riTypedRowsWf_generic
