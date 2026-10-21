import rcic.RcicNativeTypedModelCovWConvCore

/-!
Regression for the public-code coverage premise of CTyWConvR.function.

Syntactically distinct raw universe labels that are equal under eqN cover the
same singleton public demand.  They therefore cannot disable the function
row's output-typing obligation.  This proves only the displayed row property;
it does not assert general transport of CTyWConvR across public-code equality.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

theorem covWConv_singleton_public_coverage {u v : Level} (h : eqN u v) :
    ∀ x ∈ [(.sort u : CptWConvR)],
      ∃ y ∈ [(.sort v : CptWConvR)], covWConvCode x = covWConvCode y := by
  intro x hx
  obtain rfl := List.mem_singleton.mp hx
  exact ⟨.sort v, List.mem_singleton.mpr rfl, (sort_code_exact u v).mpr h⟩

/--
The type-row input demand is covered by the function-row input demand even
when their raw level expressions differ.  The output obligation must fire.
-/
theorem covWConv_function_singleton_output {E : ResolvedEnv}
    {u v : Level} {a out T : CptWConvR}
    (hlevel : eqN u v)
    (h : CTyWConvR E (.lam [([.sort u], out)])
      (.pi a [([.sort v], T)])) :
    CTyWConvR E out T := by
  cases h with
  | function hc hi ho =>
      exact ho ([.sort u], out) (List.mem_singleton.mpr rfl)
        ([.sort v], T) (List.mem_singleton.mpr rfl)
        (covWConv_singleton_public_coverage (fun ρ => (hlevel ρ).symm))

/-- `imax 1 1` is a raw syntactic alias for level 1. -/
def covWConvInputAlias : Level := .imax levelOne levelOne

theorem covWConv_input_alias_eqN : eqN covWConvInputAlias levelOne :=
  fun _ => rfl

theorem covWConv_input_alias_raw_distinct :
    (.sort covWConvInputAlias : CptWConvR) ≠ .sort levelOne := by
  intro h
  cases h

/-- Raw inequality does not make the public coverage premise false. -/
theorem covWConv_alias_raw_distinct_but_covered :
    ((.sort covWConvInputAlias : CptWConvR) ≠ .sort levelOne) ∧
    (∀ x ∈ [(.sort covWConvInputAlias : CptWConvR)],
      ∃ y ∈ [(.sort levelOne : CptWConvR)],
        covWConvCode x = covWConvCode y) :=
  ⟨covWConv_input_alias_raw_distinct,
    covWConv_singleton_public_coverage covWConv_input_alias_eqN⟩

/-- The concrete alias case still requires the full raw output typing. -/
theorem covWConv_alias_row_output {E : ResolvedEnv} {a out T : CptWConvR}
    (h : CTyWConvR E (.lam [([.sort levelOne], out)])
      (.pi a [([.sort covWConvInputAlias], T)])) :
    CTyWConvR E out T :=
  covWConv_function_singleton_output
    (fun ρ => (covWConv_input_alias_eqN ρ).symm) h

#print axioms covWConv_singleton_public_coverage
#print axioms covWConv_function_singleton_output
#print axioms covWConv_input_alias_eqN
#print axioms covWConv_input_alias_raw_distinct
#print axioms covWConv_alias_raw_distinct_but_covered
#print axioms covWConv_alias_row_output

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
