import rcic.RcicNativeTypedModelRel

/-!
# Compact type-code descent, checked before the CovY relation

These named facts compose the landed compact size lemmas. Their parent is
the semantic TYPE code `pi a g`, never the term compact and never a native
type expression. The selected codomain comes from an actual row of `g`.
No recursive relation is defined in this module. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovYAudit

open TypedModelAudit

theorem covY_sizeOf_domain_lt (a : CptT) (g : List (List CptT × CptT)) :
    sizeOf a < sizeOf (CptT.pi a g) := sizeOf_dom_lt_pi a g

theorem covY_sizeOf_selected_codomain_lt {a : CptT}
    {g : List (List CptT × CptT)} {row : List CptT × CptT} (hrow : row ∈ g) :
    sizeOf row.2 < sizeOf (CptT.pi a g) := sizeOf_out_lt_pi hrow

theorem covY_sizeOf_demand_member_lt {a : CptT}
    {g : List (List CptT × CptT)} {row : List CptT × CptT} (hrow : row ∈ g)
    {u : CptT} (hu : u ∈ row.1) :
    sizeOf u < sizeOf (CptT.pi a g) := sizeOf_dem_lt_pi hrow hu

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Y_MEASURE_ROOTS
#print axioms covY_sizeOf_domain_lt
#print axioms covY_sizeOf_selected_codomain_lt
#print axioms covY_sizeOf_demand_member_lt
-- END RCIC_NATIVE_TYPED_MODEL_COV_Y_MEASURE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovYAudit
