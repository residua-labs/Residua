import rcic.RcicF8OM23
import rcic.RcicF8XStruct

/-!
# `RcicF8XEdgeLex` — the lexicographic call edge (cc's 2026-10-14 ruling on E-X-LONE)

`S3D_EDGES_DESIGN.md` (#7026) §2, E-X-LONE: when the X tile's input is one `ofCv` node around a
single `ConvT` literal, X's J call keeps the atom multiset (`[.cv h] ++ Z` on both sides — X does
not split the literal, cc Q3) and only shrinks the argument. The sealed `OM3_edge` is a `DMStep`
on the atom multiset alone and cannot record that call. cc approved the additive sibling:

* `OM3_edgeLex caller callee` — `Prod.Lex DMStep (<)` on (atom multiset by weight, argument
  size): a `DMStep`, or the same multiset and a smaller size (the measure of S0 §6, `lexDM`);
* `om3_edgeLex_wf` — the measure is WELL-FOUNDED (`lexDM_wf` through the weight map);
* `om3_edgeLex_of_edge` — every sealed `DMStep` edge is a lex edge, for any sizes, so every
  sealed edge theorem transfers unchanged (`edgeContractLex_of_edgeContract` for a census);
* `om3_edgeLex_lone` — the E-X-LONE step itself; `om3_edgeLex_xJ_lone` is X's instance: the
  argument shrinks from the `ofCv` node to the literal node it wraps.

The sealed `OM3_edge` / `EdgeContract` are untouched; consumers that need the mutual's
termination use the lex form. The size component counts provenance constructors (`EvTc.size`,
`EvCv.size`), the second component of S0 §6's measure. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat}

/-- a call's measure: the atom bundle and the argument size. -/
abbrev CallMeasure (E : ResolvedEnv) (n : Nat) : Type := List (Jd E n) × Nat

/-- the weights the sealed `OM3_edge` compares, with the size. -/
def CallMeasure.key (m : CallMeasure E n) : List Nat × Nat := (m.1.map Jd.wt, m.2)

/-- the lexicographic edge: a `DMStep` on the atom multiset, or the same multiset and a strictly
    smaller argument. -/
def OM3_edgeLex (caller callee : CallMeasure E n) : Prop :=
  Prod.Lex DMStep (fun a b : Nat => a < b) callee.key caller.key

/-- the measure is well-founded: `lexDM_wf` through the key. -/
theorem om3_edgeLex_wf :
    WellFounded (fun callee caller : CallMeasure E n => OM3_edgeLex caller callee) :=
  InvImage.wf (CallMeasure.key (E := E) (n := n)) lexDM_wf

/-- every sealed `DMStep` edge is a lex edge, for any sizes. -/
theorem om3_edgeLex_of_edge {Rc Re : List (Jd E n)} (h : OM3_edge Rc Re) (sc se : Nat) :
    OM3_edgeLex (Rc, sc) (Re, se) :=
  Prod.Lex.left _ _ h

/-- E-X-LONE: the same atom multiset and a strictly smaller argument. -/
theorem om3_edgeLex_lone (R : List (Jd E n)) {sc se : Nat} (h : se < sc) :
    OM3_edgeLex (R, sc) (R, se) :=
  Prod.Lex.right _ h

/-- the lex census. -/
def EdgeContractLex (calls : List (CallMeasure E n × CallMeasure E n)) : Prop :=
  ∀ p ∈ calls, OM3_edgeLex p.1 p.2

/-- a sealed `DMStep` census transfers to the lex census with any size assignment. -/
theorem edgeContractLex_of_edgeContract (calls : List (List (Jd E n) × List (Jd E n)))
    (h : EdgeContract calls) (sz : List (Jd E n) × List (Jd E n) → Nat × Nat) :
    EdgeContractLex (calls.map (fun p => ((p.1, (sz p).1), (p.2, (sz p).2)))) := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
  exact om3_edgeLex_of_edge (h p hp) _ _

/-- a lex census is well-founded along any chain of recorded calls: there is no infinite
    descent through `OM3_edgeLex`. -/
theorem om3_edgeLex_acc (m : CallMeasure E n) :
    Acc (fun callee caller : CallMeasure E n => OM3_edgeLex caller callee) m :=
  om3_edgeLex_wf.apply m

/-! ### the X tile's instance -/

variable {R : List (Jd E n)}

/-- X's lone-literal J call (S3D §2): the input is one `ofCv` node around the conversion `c`
    (a literal, possibly under `symm`/`tyConv`), the bundles coincide, and the argument shrinks
    from the node to what it wraps. -/
theorem om3_edgeLex_xJ_lone {Γ : LCtx} {A B : Expr Nat} (u : Level) (c : EvCv R Γ A B (.sort u))
    (Z : List (Jd E n)) :
    OM3_edgeLex ((EvTc.ofCv u c).leaves ++ Z, (EvTc.ofCv u c).size)
      ((EvTc.ofCv u c).leaves ++ Z, c.size) :=
  om3_edgeLex_lone _ (by simp only [EvTc.size]; omega)

/-- the node's leaves ARE the literal's: nothing is dropped, which is why the DM component
    cannot move. -/
theorem ofCv_leaves_eq {Γ : LCtx} {A B : Expr Nat} (u : Level) (c : EvCv R Γ A B (.sort u)) :
    (EvTc.ofCv u c).leaves = c.leaves := by
  simp only [EvTc.leaves]

section Pins

/-- the β fixture's lone-literal input `piX ≡ redex` (S1's `betaRedexConv` under one `ofCv`):
    its J call is a lex edge with bundle `[.cv betaRedexConv] ++ Z` on both sides. -/
theorem pin_lone_beta (Z : List (Jd emptyEnv 0)) :
    OM3_edgeLex
      ((EvTc.ofCv (R := [Jd.cv betaRedexConv]) (.imax (.succ .zero) (.succ .zero))
        (EvCv.lit betaRedexConv ⟨.cv betaRedexConv, .head _, .inl rfl⟩)).leaves ++ Z, 2)
      ([Jd.cv betaRedexConv] ++ Z, 1) := by
  have h := om3_edgeLex_xJ_lone (R := [Jd.cv betaRedexConv]) (Γ := [])
    (.imax (.succ .zero) (.succ .zero)) (EvCv.lit betaRedexConv ⟨.cv betaRedexConv, .head _, .inl rfl⟩) Z
  simpa only [EvTc.leaves, EvCv.leaves, EvTc.size, EvCv.size] using h

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.CallMeasure
#print axioms Rcic.Declarative.F8Measure.CallMeasure.key
#print axioms Rcic.Declarative.F8Measure.OM3_edgeLex
#print axioms Rcic.Declarative.F8Measure.om3_edgeLex_wf
#print axioms Rcic.Declarative.F8Measure.om3_edgeLex_of_edge
#print axioms Rcic.Declarative.F8Measure.om3_edgeLex_lone
#print axioms Rcic.Declarative.F8Measure.EdgeContractLex
#print axioms Rcic.Declarative.F8Measure.edgeContractLex_of_edgeContract
#print axioms Rcic.Declarative.F8Measure.om3_edgeLex_acc
#print axioms Rcic.Declarative.F8Measure.om3_edgeLex_xJ_lone
#print axioms Rcic.Declarative.F8Measure.ofCv_leaves_eq
#print axioms Rcic.Declarative.F8Measure.pin_lone_beta
