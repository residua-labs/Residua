import rcic.RcicF3FamilyBetaPropTreeBounds
import rcic.RcicF3PointwiseRemainingPropOnlyFamilyBeta

/-!
# Actual admitted beta-hidden recursive fields at the original invariant

The fixture is admitted anew, including its stored hidden field, recursor,
typed iota descriptors and original BoundG/BoundDG. Its actual cache is
shown to contain Prop → F, whereas the source is the head-beta expression
`(fun _ : Prop => Prop → F) F`. The family-beta syntax certificate is proved
for every admitted node of this same group, and its new invariant producer
is applied directly.

The fixture is outside AllPlain, DirectCycle, SourceNormalized and
SourceNoBeta. Its parameters are empty and therefore match, so it is not
a witness of strict enlargement beyond the entire previous covered union.
Source-only draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwiseFamilyBetaPropTree
open Rcic.Declarative RawFamily PiValueRule
open Rcic.Declarative.FamilyBetaPropTree
open FamilyBetaPropTreeBounds (Node wft ctorClasses)

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup EnvWfT.empty (f := 4) (fm := fam)
    (ctors := [(5, leaf), (6, node)]) (rr := 7) (rm := recMem)
    rfl ctorClasses rfl membersT

theorem uniform_prop : UniformProp plan.node.a.family.resultLevel := by
  intro σ
  rw [(FamilyBetaPropTreeBounds.familyInfo plan.node).2.2]
  rfl

theorem leaf_fields (n : Node) :
    (n.a.constructorViews ⟨0, by rw [FamilyBetaPropTreeBounds.ctorCount n]; decide⟩).fields =
      [] := by
  rcases (FamilyBetaPropTreeBounds.views n
    ⟨0, by rw [FamilyBetaPropTreeBounds.ctorCount n]; decide⟩).2.2 with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · cases h

theorem recursive_fields (n : Node) :
    (n.a.constructorViews ⟨1, by rw [FamilyBetaPropTreeBounds.ctorCount n]; decide⟩).fields =
      [field] := by
  rcases (FamilyBetaPropTreeBounds.views n
    ⟨1, by rw [FamilyBetaPropTreeBounds.ctorCount n]; decide⟩).2.2 with ⟨_, h⟩ | ⟨h, _⟩
  · cases h
  · exact h

/-- Every successful actual fuel returns this exact normalized telescope. -/
theorem hidden_read {E : ResolvedEnv} {fuel : Nat}
    {ds : List (Expr Nat)} {b : Expr Nat}
    (hf : transparentBody E 4 [] = none)
    (hr : piTelescopeFuel E fuel field = some (ds, b)) :
    (ds, b) = ([.sort .zero], .const 4 []) := by
  cases fuel with
  | zero => cases hr
  | succ fuel =>
      cases fuel with
      | zero => cases hr
      | succ fuel =>
          cases fuel with
          | zero => cases hr
          | succ fuel =>
              have hc : piTelescopeFuel E (fuel + 1 + 1 + 1) field =
                  some ([.sort .zero], .const 4 []) := by
                simp only [piTelescopeFuel, whnfFuel, field, normalField, appsSpine,
                  instantiate0, instantiate, foldApps, hf, List.nil_append]
              exact Option.some.inj (hr.symm.trans hc)

theorem field_normalized (n : Node) {fuel np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape}
    (q : EvalPlan.Field n.E0 fuel n.a.family.ref n.a.family.member.arity
      np ni prior A s) (hA : A = field) :
    fieldExpr n.a.family.ref (canonL n.a.family.member.arity)
      (EvalPlanNormal.fieldSpec q) = normalField := by
  cases q with
  | plain hfree =>
      have ht : occursConst n.a.family.ref A = true := by rw [hA, n.fam]; rfl
      rw [hfree] at ht
      cases ht
  | recursive r =>
      have hf := transparentBody_family n.a.family (canonL n.a.family.member.arity)
      rw [n.fam, FamilyBetaPropTreeBounds.familyArity n] at hf
      have hr := (congrArg (piTelescopeFuel n.E0 fuel) hA).symm.trans r.read
      have he := hidden_read hf hr
      exact congrArg (fun p : List (Expr Nat) × Expr Nat => policyPi p.1 p.2) he

theorem specs_normalized (n : Node) {fuel np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (q : EvalPlan.Fields n.E0 fuel n.a.family.ref n.a.family.member.arity
      np ni prior ss Fs)
    (hFs : ∀ A ∈ Fs, A = field) :
    (EvalPlanNormal.specs q).map
        (fieldExpr n.a.family.ref (canonL n.a.family.member.arity)) =
      Fs.map (fun _ => normalField) := by
  revert hFs
  induction q with
  | nil => intro _; rfl
  | @cons prior s A ss Fs head tail ih =>
      intro hFs
      change fieldExpr n.a.family.ref (canonL n.a.family.member.arity)
          (EvalPlanNormal.fieldSpec head) :: _ = normalField :: _
      rw [field_normalized n head (hFs A (List.mem_cons_self _ _))]
      exact congrArg (List.cons normalField)
        (ih (fun B hB => hFs B (List.mem_cons_of_mem _ hB)))

theorem fields_normalized (n : Node) (j : Fin n.a.constructors.length) :
    EvalPlanNormal.fields (EvalPlan.ofNode n) j =
      (n.a.constructorViews j).fields.map (fun _ => normalField) := by
  apply specs_normalized n ((EvalPlan.ofNode n).constructors j).fields
  intro A hA
  change A ∈ (n.a.constructorViews j).fields at hA
  rcases (FamilyBetaPropTreeBounds.views n j).2.2 with ⟨hfields, _⟩ | ⟨hfields, _⟩
  · rw [hfields] at hA
    exact (List.not_mem_nil A hA).elim
  · rw [hfields] at hA
    exact List.mem_singleton.mp hA

theorem family_type (n : Node) :
    famType (EvalPlanNormal.fd (EvalPlan.ofNode n)) = .sort .zero := by
  change policyPi (n.a.family.parameters ++ n.a.family.indices)
    (.sort n.a.family.resultLevel) = .sort .zero
  rw [(FamilyBetaPropTreeBounds.familyInfo n).1,
    (FamilyBetaPropTreeBounds.familyInfo n).2.1,
    (FamilyBetaPropTreeBounds.familyInfo n).2.2]
  rfl

theorem mirror_source (n : Node) :
    FamilyBetaMirror.mirrors (EvalPlanNormal.fd (EvalPlan.ofNode n))
      n.a.family.member.arity 1 normalField = field := by
  change Expr.app (.lam (famType (EvalPlanNormal.fd (EvalPlan.ofNode n)))
    (Rcic.Declarative.lift 0 1 normalField))
    (.const n.a.family.ref (canonL n.a.family.member.arity)) = field
  rw [family_type n, n.fam, FamilyBetaPropTreeBounds.familyArity n]
  rfl

theorem source_familyBeta (n : Node) :
    PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta n := by
  intro j
  change PointwisePropOnlyFamilyBetaFields.Sources _ _
    (n.a.constructorViews j).fields (EvalPlanNormal.fields (EvalPlan.ofNode n) j)
  rw [fields_normalized]
  rcases (FamilyBetaPropTreeBounds.views n j).2.2 with ⟨hfields, _⟩ | ⟨hfields, _⟩
  · rw [hfields]
    exact .nil
  · rw [hfields]
    change PointwisePropOnlyFamilyBetaFields.Sources _ _ [field] [normalField]
    rw [← mirror_source n]
    exact .cons 1 normalField .nil

theorem not_sourceNormalized (n : Node) :
    ¬ PointwisePropOnlyNormalizedFields.SourceNormalized n := by
  intro h
  have he := h ⟨1, by rw [FamilyBetaPropTreeBounds.ctorCount n]; decide⟩
  rw [fields_normalized, recursive_fields] at he
  have hn : normalField = field := (List.cons.inj he).1
  exact Expr.noConfusion hn

theorem no_hidden_head {E : ResolvedEnv} {fuel : Nat} {e w : Expr Nat}
    (h : ReaderNoBeta.Head E fuel e w) (he : e = field) : False := by
  cases h with
  | stop fuel e hs =>
      have hf : False := by
        simpa only [he, ReaderNoBeta.Stops, field, appsSpine, List.nil_append] using hs
      exact hf
  | zeta hs _ =>
      exact Expr.noConfusion (congrArg Prod.fst ((congrArg appsSpine he).symm.trans hs))
  | delta hs _ _ =>
      exact Expr.noConfusion (congrArg Prod.fst ((congrArg appsSpine he).symm.trans hs))

theorem no_hidden_telescope {E : ResolvedEnv} {fuel : Nat} {e b : Expr Nat}
    {ds : List (Expr Nat)} (h : ReaderNoBeta.Telescope E fuel e ds b)
    (he : e = field) : False := by
  cases h with
  | leaf hh _ => exact no_hidden_head hh he
  | pi hh _ => exact no_hidden_head hh he

theorem not_sourceNoBeta (n : Node) : ¬ ReaderNoBeta.SourceNoBeta n := by
  intro h
  let j : Fin n.a.constructors.length :=
    ⟨1, by rw [FamilyBetaPropTreeBounds.ctorCount n]; decide⟩
  have hfs : (n.a.constructorViews j).fields = [field] := recursive_fields n
  have hk : 0 < (n.a.constructorViews j).fields.length := by rw [hfs]; decide
  obtain ⟨prior, s, q, _, _, hq⟩ := ReaderNoBeta.field_at
    ((EvalPlan.ofNode n).constructors j).fields (h j) 0 hk
  have hA : (n.a.constructorViews j).fields[0]'hk = field := by
    simp only [hfs, List.getElem_cons_zero]
  cases q with
  | plain hfree =>
      have ht : occursConst n.a.family.ref ((n.a.constructorViews j).fields[0]'hk) = true := by
        rw [hA, n.fam]
        rfl
      exact Bool.noConfusion (hfree.symm.trans ht)
  | recursive r => exact no_hidden_telescope hq hA

theorem not_all_plain (n : Node) : ¬ PropShapeCoverage.AllPlain n := by
  intro hplain
  have hf := PropShapeCoverage.all_plain_fields_free hplain
    ⟨1, by rw [FamilyBetaPropTreeBounds.ctorCount n]; decide⟩ field
    (by rw [recursive_fields n]; exact List.mem_singleton_self _)
  rw [n.fam] at hf
  change true = false at hf
  cases hf

theorem not_direct_cycle (n : Node) : ¬ PropShapeCoverage.DirectCycle n := by
  intro hcycle
  let j : Fin n.a.constructors.length :=
    ⟨0, by rw [FamilyBetaPropTreeBounds.ctorCount n]; decide⟩
  have hlen := Rcic.F3.PSet.fieldShapesFuel_length n.E0 (n.h14.fuelAt j)
    n.a.family.ref n.a.family.member.arity n.a.family.parameters.length
    n.a.family.indices.length (n.a.constructorViews j).fields
    n.a.family.parameters.length (n.h14.shapesAt j) (n.h14.analyzed j)
  have hfields : (n.a.constructorViews j).fields = [] := leaf_fields n
  rw [hfields] at hlen
  have hs : n.h14.shapesAt j = [] := List.eq_nil_of_length_eq_zero hlen
  have hc := hcycle j
  rw [hs] at hc
  exact List.not_mem_nil _ hc

theorem matching_parameters (n : Node) :
    PointwiseRemainingPropOnly.MatchingParameters n :=
  fun j => (FamilyBetaPropTreeBounds.views n j).1.trans
    (FamilyBetaPropTreeBounds.familyInfo n).1.symm

theorem invariant (P : Premises4) (K : Nat → Nat) : PointwiseRole.GInv P K wft :=
  PointwisePropOnlyFamilyBetaGroup.invariant_step P K EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT
    uniform_prop (FamilyBetaPropTreeBounds.policyPropOnly plan.node)
    (source_familyBeta plan.node) (FamilyBetaPropTreeBounds.boundG K)
    (FamilyBetaPropTreeBounds.boundDG K) (PointwiseRole.gInv_empty P K)

theorem env_sound (P : Premises4) (K σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P wft)) σ K eAll n :=
  PointwiseRole.envSound_of_gInv P K wft (invariant P K) σ n

def Witness (P : Premises4) : Prop :=
  FamilyBetaPropTreeBounds.Witness ∧
  (∀ n : Node, PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta n ∧
    ¬ PointwisePropOnlyNormalizedFields.SourceNormalized n ∧
    ¬ ReaderNoBeta.SourceNoBeta n ∧ ¬ PropShapeCoverage.AllPlain n ∧
    ¬ PropShapeCoverage.DirectCycle n ∧ PointwiseRemainingPropOnly.MatchingParameters n) ∧
  (∀ K : Nat → Nat, PointwiseRole.GInv P K wft)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨FamilyBetaPropTreeBounds.component_witness,
    fun n => ⟨source_familyBeta n, not_sourceNormalized n, not_sourceNoBeta n,
      not_all_plain n, not_direct_cycle n, matching_parameters n⟩,
    invariant P⟩

end Rcic.F3.PSet.PointwiseFamilyBetaPropTree

#print axioms Rcic.F3.PSet.PointwiseFamilyBetaPropTree.source_familyBeta
#print axioms Rcic.F3.PSet.PointwiseFamilyBetaPropTree.not_sourceNoBeta
#print axioms Rcic.F3.PSet.PointwiseFamilyBetaPropTree.invariant
#print axioms Rcic.F3.PSet.PointwiseFamilyBetaPropTree.component_witness
