import rcic.RcicF3PrefixBetaPropTreeBounds
import rcic.RcicF3PointwisePropOnlyPrefixBeta
import rcic.RcicF3PointwiseRemainingPropOnlyFamilyBeta

/-!
# A strict admitted enlargement by local-prefix beta reconstruction

The beta argument is the literal family parameter p. Its annotated Prop
membership is read from the available family prefix; the stored own
parameter type is the existing unequal beta mirror. The source/cache
certificate, both original bounds, and all six previous-route exclusions
refer to the same actual group and its admission-selected plan.
Source draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PointwisePrefixBetaPropTree
open Rcic.Declarative RawFamily PiValueRule
open Rcic.Declarative.PrefixBetaPropTree
open Rcic.Declarative.UnequalPropTree (ownParam fam leaf famApp)
open PrefixBetaPropTreeBounds (Node bound wft)

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup EnvWfT.empty (f := 4) (fm := fam)
    (ctors := [(5, leaf), (6, node)]) (rr := 7) (rm := recMem)
    rfl ctorClasses rfl membersT

theorem uniform_prop : UniformProp plan.node.a.family.resultLevel := by
  intro σ
  rw [(PrefixBetaPropTreeBounds.familyInfo plan.node).2.2]
  rfl

theorem leaf_fields (n : Node) :
    (n.a.constructorViews ⟨0, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩).fields =
      [] := by
  rcases (PrefixBetaPropTreeBounds.views n
    ⟨0, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩).2.2 with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · cases h

theorem recursive_fields (n : Node) :
    (n.a.constructorViews ⟨1, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩).fields =
      [field] := by
  rcases (PrefixBetaPropTreeBounds.views n
    ⟨1, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩).2.2 with ⟨_, h⟩ | ⟨h, _⟩
  · cases h
  · exact h

/-- Every successful actual cached-reader fuel gives this normal field.
The source head really contracts beta before exposing the Pi binder. -/
theorem hidden_read {E : ResolvedEnv} {fuel : Nat}
    {ds : List (Expr Nat)} {b : Expr Nat}
    (hf : transparentBody E 4 [] = none)
    (hr : piTelescopeFuel E fuel field = some (ds, b)) :
    (ds, b) = ([.sort .zero], famApp (.bvar 1)) := by
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
                  some ([.sort .zero], famApp (.bvar 1)) := by
                simp [piTelescopeFuel, whnfFuel, field, normalField,
                  UnequalPropTree.field, famApp, lift, appsSpine,
                  instantiate0, instantiate, foldApps, hf]
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
      rw [n.fam, PrefixBetaPropTreeBounds.familyArity n] at hf
      have hr := (congrArg (piTelescopeFuel n.E0 fuel) hA).symm.trans r.read
      exact congrArg (fun p : List (Expr Nat) × Expr Nat => policyPi p.1 p.2)
        (hidden_read hf hr)

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
  rcases (PrefixBetaPropTreeBounds.views n j).2.2 with ⟨hfields, _⟩ | ⟨hfields, _⟩
  · rw [hfields] at hA
    exact (List.not_mem_nil A hA).elim
  · rw [hfields] at hA
    exact List.mem_singleton.mp hA

/-- The new producer's required literal source/cache relation. The
local beta annotation is exactly the family prefix's lookup type. -/
theorem source_prefixBeta (n : Node) : ReaderPrefixBeta.SourcePrefixBeta n := by
  intro j k hk hkn
  change k < (n.a.constructorViews j).fields.length at hk
  change k < (EvalPlanNormal.fields (EvalPlan.ofNode n) j).length at hkn
  change ReaderPrefixBeta.Reduces (EvalPlan.ofNode n)
    (policyPrefixContext
      (n.a.family.parameters ++ (n.a.constructorViews j).fields)
      (n.a.family.parameters.length + k))
    ((n.a.constructorViews j).fields[k]'hk)
    ((EvalPlanNormal.fields (EvalPlan.ofNode n) j)[k]'hkn)
  rcases (PrefixBetaPropTreeBounds.views n j).2.2 with ⟨hf, _⟩ | ⟨hf, _⟩
  · rw [hf] at hk
    exact (Nat.not_lt_zero k hk).elim
  · have hk0 : k = 0 := by rw [hf] at hk; exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    have hΓ : policyPrefixContext
        (n.a.family.parameters ++ (n.a.constructorViews j).fields)
        (n.a.family.parameters.length + 0) = [.assumption (.sort .zero)] := by
      rw [(PrefixBetaPropTreeBounds.familyInfo n).1, hf]
      rfl
    have hsrc : (n.a.constructorViews j).fields[0]'hk = field := by
      simp only [hf, List.getElem_cons_zero]
    have hdst : (EvalPlanNormal.fields (EvalPlan.ofNode n) j)[0]'hkn = normalField := by
      simp only [fields_normalized, hf, List.map_cons, List.map_nil, List.getElem_cons_zero]
    rw [hΓ, hsrc, hdst]
    exact ReaderPrefixBeta.Reduces.localWrapper (EvalPlan.ofNode n)
      [.assumption (.sort .zero)] 0 (.sort .zero) normalField rfl

theorem not_sourceNormalized (n : Node) :
    ¬ PointwisePropOnlyNormalizedFields.SourceNormalized n := by
  intro h
  have he := h ⟨1, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩
  rw [fields_normalized, recursive_fields] at he
  exact Expr.noConfusion (List.cons.inj he).1

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
    ⟨1, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩
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

theorem sources_singleton {fd : FamData} {arity : Nat} {A B : Expr Nat}
    (h : PointwisePropOnlyFamilyBetaFields.Sources fd arity [A] [B]) :
    ∃ depth, A = FamilyBetaMirror.mirrors fd arity depth B := by
  cases h with
  | cons depth B tail => exact ⟨depth, rfl⟩

theorem not_sourceFamilyBeta (n : Node) :
    ¬ PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta n := by
  intro h
  let j : Fin n.a.constructors.length :=
    ⟨1, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩
  have hs := h j
  change PointwisePropOnlyFamilyBetaFields.Sources _ _
    (n.a.constructorViews _).fields (EvalPlanNormal.fields (EvalPlan.ofNode n) _) at hs
  rw [fields_normalized, recursive_fields] at hs
  obtain ⟨depth, he⟩ := sources_singleton hs
  cases depth with
  | zero => exact Expr.noConfusion he
  | succ depth =>
      change field = FamilyBetaMirror.mirror _ _ _ at he
      unfold field FamilyBetaMirror.mirror at he
      exact Expr.noConfusion (Expr.app.inj he).2

theorem not_matching_parameters (n : Node) :
    ¬ PointwiseRemainingPropOnly.MatchingParameters n := by
  intro h
  let j : Fin n.a.constructors.length :=
    ⟨0, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩
  have he := h j
  rw [(PrefixBetaPropTreeBounds.views n j).1,
    (PrefixBetaPropTreeBounds.familyInfo n).1] at he
  exact Expr.noConfusion (List.cons.inj he).1

theorem not_all_plain (n : Node) : ¬ PropShapeCoverage.AllPlain n := by
  intro hplain
  have hf := PropShapeCoverage.all_plain_fields_free hplain
    ⟨1, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩ field
    (by rw [recursive_fields n]; exact List.mem_singleton_self _)
  rw [n.fam] at hf
  change true = false at hf
  cases hf

theorem not_direct_cycle (n : Node) : ¬ PropShapeCoverage.DirectCycle n := by
  intro hcycle
  let j : Fin n.a.constructors.length :=
    ⟨0, by rw [PrefixBetaPropTreeBounds.ctorCount n]; decide⟩
  have hl := Rcic.F3.PSet.fieldShapesFuel_length n.E0 (n.h14.fuelAt j)
    n.a.family.ref n.a.family.member.arity n.a.family.parameters.length
    n.a.family.indices.length (n.a.constructorViews j).fields
    n.a.family.parameters.length (n.h14.shapesAt j) (n.h14.analyzed j)
  rw [leaf_fields n] at hl
  have hs : n.h14.shapesAt j = [] := List.eq_nil_of_length_eq_zero hl
  have hc := hcycle j
  rw [hs] at hc
  exact List.not_mem_nil _ hc

/-- Exclude the entire existing covered union, not just one syntax face. -/
theorem outside_previous_union :
    ¬ PointwiseRemainingPropOnlyFamilyBeta.Covered EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
      (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT := by
  intro h
  rcases h with (((hplain | hcycle) | hnorm | hmatch) | hnoBeta) | hfamilyBeta
  · exact not_all_plain plan.node hplain
  · exact not_direct_cycle plan.node hcycle
  · exact not_sourceNormalized plan.node hnorm
  · exact not_matching_parameters plan.node hmatch
  · exact not_sourceNoBeta plan.node hnoBeta
  · exact not_sourceFamilyBeta plan.node hfamilyBeta

theorem invariant (P : Premises4) : PointwiseRole.GInv P bound wft :=
  PointwisePropOnlyPrefixBeta.invariant_step P bound EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, leaf), (6, node)])
    (rr := 7) (rm := recMem) rfl ctorClasses rfl membersT
    uniform_prop (PrefixBetaPropTreeBounds.policyPropOnly plan.node)
    (source_prefixBeta plan.node) PrefixBetaPropTreeBounds.boundG
    PrefixBetaPropTreeBounds.boundDG (PointwiseRole.gInv_empty P bound)

theorem env_sound (P : Premises4) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (PointwiseRole.table P wft)) σ bound eAll n :=
  PointwiseRole.envSound_of_gInv P bound wft (invariant P) σ n

def Witness (P : Premises4) : Prop :=
  Nonempty (EnvWfT eAll) ∧ BoundG bound wft ∧ BoundDG bound wft ∧
  ReaderPrefixBeta.SourcePrefixBeta plan.node ∧
  (¬ PointwisePropOnlyNormalizedFields.SourceNormalized plan.node) ∧
  (¬ ReaderNoBeta.SourceNoBeta plan.node) ∧
  (¬ PointwisePropOnlyFamilyBetaFields.SourceFamilyBeta plan.node) ∧
  (¬ PointwiseRemainingPropOnly.MatchingParameters plan.node) ∧
  (¬ PropShapeCoverage.AllPlain plan.node) ∧
  (¬ PropShapeCoverage.DirectCycle plan.node) ∧ PointwiseRole.GInv P bound wft

theorem component_witness (P : Premises4) : Witness P :=
  ⟨⟨envWfT⟩, PrefixBetaPropTreeBounds.boundG, PrefixBetaPropTreeBounds.boundDG,
    source_prefixBeta plan.node, not_sourceNormalized plan.node,
    not_sourceNoBeta plan.node, not_sourceFamilyBeta plan.node,
    not_matching_parameters plan.node, not_all_plain plan.node,
    not_direct_cycle plan.node, invariant P⟩

end Rcic.F3.PSet.PointwisePrefixBetaPropTree

#print axioms Rcic.F3.PSet.PointwisePrefixBetaPropTree.source_prefixBeta
#print axioms Rcic.F3.PSet.PointwisePrefixBetaPropTree.outside_previous_union
#print axioms Rcic.F3.PSet.PointwisePrefixBetaPropTree.invariant
#print axioms Rcic.F3.PSet.PointwisePrefixBetaPropTree.component_witness
