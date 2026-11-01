import rcic.RcicF3PiRecPlan
import rcic.RcicF3Cover
/-! Consume the existing admission descriptor's normalized shapes.
This supplies operational depths, not semantic extraction or the universal
A-axis producer. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecPlan
universe u v
open Rcic.Declarative

def nodePlan {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : List (List FieldShape) :=
  (List.range node.a.constructors.length).map (fun j =>
    if hj : j < node.a.constructors.length then node.h14.shapesAt ⟨j, hj⟩ else [])

noncomputable def nodeCore (M : Interp.{u}) {E E' : ResolvedEnv}
    {f rr : Nat} {rm : CheckedMember} (node : RecNode E E' f rr rm)
    (ms : List PSet.{u}) : PSet.{u} → PSet.{u} :=
  core M f (nodePlan node) ms

/-- Exact admission slot, including its constructor field count.
This is elementary descriptor bookkeeping. -/
theorem nodePlan_spec {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length) :
    (nodePlan node)[i.val]? = some (node.h14.shapesAt i) ∧
      (node.h14.shapesAt i).length = (node.a.constructorViews i).fields.length := by
  refine ⟨?_, fieldShapesFuel_length _ _ _ _ _ _ _ _ _ (node.h14.analyzed i)⟩
  simp only [nodePlan, List.getElem?_map, List.getElem?_range i.isLt]
  change some (if hj : i.val < node.a.constructors.length then
    node.h14.shapesAt ⟨i.val, hj⟩ else []) = some (node.h14.shapesAt i)
  rw [dif_pos i.isLt]

/-- Admission-indexed constructor equation. Actual semantic field membership
is still an explicit input; extracting it from typed normalized syntax is
not claimed here. This is elementary composition. -/
theorem node_data_mem (M : Interp.{u}) {E E' : ResolvedEnv}
    {f rr : Nat} {rm : CheckedMember} (node : RecNode E E' f rr rm)
    (ms : List PSet.{u}) (i : Fin node.a.constructors.length)
    {xs : List PSet.{u}} (hm : FieldsMem.{u,v} M (node.h14.shapesAt i) xs) :
    Equiv (nodeCore M node ms (dataVal i.val xs))
      (fapps (ms.getD i.val pempty)
        (args (nodeCore M node ms) (node.h14.shapesAt i) xs)) := by
  exact core_data_mem M f (nodePlan node) ms (nodePlan_spec node i).1 hm

end Rcic.F3.PSet.RecPlan
