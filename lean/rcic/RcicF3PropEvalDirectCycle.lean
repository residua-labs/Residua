import rcic.RcicF3PropEval

/-!
# Direct recursive cycles have no finite evaluation

Every stored constructor in this face demands a direct recursive child.
The actual Eval/Inputs derivation therefore cannot be finite: at a direct
field, the executable reader has an empty telescope and the child at the
empty tuple is another Eval derivation. Mutual induction proves the
contradiction without a semantic callback or an environment restriction.

This is a producer for Prop groups refused by the old D propCorner check;
the old check, invariant and original whole-tier root are unchanged.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

/-- Every constructor demands a direct child in the literal admitted
shape descriptor. The condition concerns stored syntax, not semantics. -/
def DirectCycles (C : Context) : Prop :=
  ∀ j : Fin C.node.a.constructors.length,
    FieldShape.recursive 0 ∈ C.node.h14.shapesAt j

/-- No finite evaluation exists if each possible root constructor needs
a direct recursive child. The recursive premise is consumed at its actual
empty telescope, rather than assumed as a callback. -/
theorem Eval.false_of_direct_cycles {C : Context} (hcycle : DirectCycles C)
    {i : Index.{4}} {z : PSet.{4}} (h : Eval C i z) : False := by
  induction h using Eval.rec
      (motive_2 := fun _ _ _ ss _ _ _ _ _ _ => FieldShape.recursive 0 ∉ ss) with
  | root j ps xs ys fuel R out z hps hp hf hs hst hd hm hi hr ih =>
      exact ih (hcycle j)
  | done => exact List.not_mem_nil _
  | @plain fuel Mx acc A B ss ρ xs ys out x hx tail ih =>
      intro hm
      rcases List.mem_cons.mp hm with hhead | htail
      · cases hhead
      · exact ih htail
  | @recursive fuel Mx acc A B ss ρ xs ys out inner ihT hr x ih hx hih
      ds args hscan hdepth hargc hchildren tail ihchildren iht =>
      intro hm
      rcases List.mem_cons.mp hm with hhead | htail
      · have hzero : inner = 0 := (FieldShape.recursive.inj hhead).symm
        have hnil : ds = [] := List.length_eq_zero.mp (hdepth.trans hzero)
        exact ihchildren [] (by rw [hnil]; trivial)
      · exact iht htail

/-- A uniformly Prop large-elimination group has at most one constructor;
one actual direct child therefore certifies the whole direct-cycle face. -/
theorem directCycles_of_singleton (C : Context)
    (hone : C.node.a.constructors.length ≤ 1)
    (j : Fin C.node.a.constructors.length)
    (hj : FieldShape.recursive 0 ∈ C.node.h14.shapesAt j) : DirectCycles C := by
  intro k
  have hk : k = j := Fin.ext (by have := k.isLt; have := j.isLt; omega)
  subst k
  exact hj

end Rcic.F3.PSet.PropEval

#print axioms Rcic.F3.PSet.PropEval.Eval.false_of_direct_cycles
#print axioms Rcic.F3.PSet.PropEval.directCycles_of_singleton
