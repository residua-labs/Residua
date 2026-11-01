import rcic.RcicF3PropOnlyEmptyMirrorBounds
import rcic.RcicF3ReaderBetaFitObstruction
import rcic.RcicF3BoundedParameterMirrorTransport
import rcic.RcicF3PointwisePropOnlyPlain

/-!
# The exact scope of the empty-field parameter-fit boundary

At the allowed recursor instance [3], W4's saturation makes Sort 4 and
Sort 5 denote the same universe. A universe code cannot belong to its
own element set: that would form a membership cycle. Consequently the
constructor-own beta expression denotes empty, while the family's Prop
parameter admits the empty-type code.

This file also produces the original PointwiseRole.GInv for the same
actual admitted group using its already covered AllPlain face. The
auxiliary failure is therefore explicitly a failure of a stronger
universal parameter-fit claim, not a failure of StepPropOnly, GInv, or
the original soundness root. No recursive-field example is asserted.

Source-only draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Rcic.F3.PSet.PropOnlyEmptyMirrorBoundary
open Rcic.Declarative Rcic.Declarative.PropOnlyEmptyMirror
open PropOnlyEmptyMirrorBounds
universe u

theorem code_not_member (S : PSet.{u}) : ¬ tyv S ∈ S := by
  have hn : ∀ s : PSet.{u}, ¬ MemT s s := by
    intro s
    induction s using memT_wf.induction with
    | h s ih =>
        intro hs
        exact ih s hs hs
  intro hcode
  have h1 : S ∈ pair tyTag S := mem_pair.mpr (Or.inr Equiv.rfl)
  have h2 : pair tyTag S ∈ tyv S := mem_pair.mpr (Or.inr Equiv.rfl)
  have hdown : MemT S (tyv S) := .tail (.single h1) h2
  exact hn S (hdown.trans (.single hcode))

def highSigma : Nat → Nat := σOf [3]

theorem argument_not_member (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ρ : Nat → PSet.{4}) :
    ¬ den (mkM P μ) highSigma ρ (.sort argLevel) ∈
      Ed (mkM P μ) (den (mkM P μ) highSigma ρ (.sort domLevel)) := by
  change ¬ tyv (U W4 4) ∈ Ed (mkM P μ) (tyv (U W4 5))
  intro h
  have hu := mem_congr_right (ed_tyv (mkM P μ) (U4_dich 5)) h
  change tyv (U W4 4) ∈ U W4 4 at hu
  exact code_not_member (U W4 4) hu

theorem own_parameter_empty (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ρ : Nat → PSet.{4}) :
    Equiv (den (mkM P μ) highSigma ρ ownParam) pempty :=
  ReaderBetaFit.application_empty_of_not_mem (mkM P μ) (argument_not_member P μ ρ)

theorem own_parameter_has_no_member (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ρ : Nat → PSet.{4}) (x : PSet.{4}) :
    ¬ x ∈ Ed (mkM P μ) (den (mkM P μ) highSigma ρ ownParam) := by
  intro hx
  exact not_mem_pempty (mem_congr_right
    ((ed_congr (mkM P μ) (own_parameter_empty P μ ρ)).trans
      (ed_pempty (mkM P μ))) hx)

theorem family_parameters_fit (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) :
    TelFits (mkM P μ) highSigma pNode.a.family.parameters ρ0 [tyv pempty] :=
  ⟨tyv_pempty_mem_sort P μ highSigma ρ0 .zero, True.intro⟩

theorem own_parameters_do_not_fit (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (j : Fin pNode.a.constructors.length) :
    ¬ TelFits (mkM P μ) highSigma (pNode.a.constructorViews j).parameters
      ρ0 [tyv pempty] := by
  rw [(views pNode j).1]
  intro h
  exact own_parameter_has_no_member P μ ρ0 (tyv pempty) h.1

theorem ctorClasses : ∀ c ∈ [(5, leaf), (6, leaf)], c.2.mclass = .constructorM := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · cases h; rfl
  · cases List.mem_singleton.mp h; rfl

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup EnvWfT.empty rfl ctorClasses rfl membersT

theorem all_plain (n : Node) : PropShapeCoverage.AllPlain n := by
  intro j s hs
  have hlen := fieldShapesFuel_length _ _ _ _ _ _ _ _ _ (n.h14.analyzed j)
  rw [(views n j).2.1] at hlen
  have hz : n.h14.shapesAt j = [] := List.eq_nil_of_length_eq_zero hlen
  rw [hz] at hs
  exact (List.not_mem_nil s hs).elim

/-- The original invariant is positively produced for this same group.
This makes the scope of the auxiliary parameter-fit failure explicit. -/
theorem invariant (P : Premises4) : PointwiseRole.GInv P bound envWfT :=
  PointwisePropOnlyPlainGroup.invariant_step P bound EnvWfT.empty rfl ctorClasses
    rfl membersT
    (fun σ => by
      change evalTotal σ plan.node.a.family.resultLevel = 0
      rw [(familyInfo plan.node).2.2]
      rfl)
    (policyPropOnly plan.node) (all_plain plan.node) boundG boundDG
    (PointwiseRole.gInv_empty P bound)

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PointwiseRole.table P envWfT

theorem actual_allSound (P : Premises4) : AllSound P (table P) bound eAll :=
  (invariant P (PointwiseRole.arities eAll) (PointwiseRole.arities_agree eAll)
    (NormRole.envCtx envWfT) (fun _ _ => rfl)
    (EvalRole.envPlan envWfT) (fun _ _ => rfl) (table P)
    (PointwiseRole.table_spec P envWfT).2.1).1

theorem family_environment_member (r : Nat) (m : CheckedMember)
    (hm : eFam.members r = some m) : r = 4 ∧ m = fam := by
  by_cases hr : r = 4
  · subst r
    have he : some fam = some m := hm
    exact ⟨rfl, (Option.some.inj he).symm⟩
  · rw [members_extend_ne emptyEnv 4 fam r hr] at hm
    change (none : Option CheckedMember) = some m at hm
    cases hm

/-- The sound constant prefix needed by the mirror utility is itself
produced from the original GInv and the actual pointwise table. -/
theorem family_environment_sound (P : Premises4) :
    EnvSound (mkM P (table P)) highSigma bound eFam 1 := by
  apply envSound_of_allSound P (E := eFam) (μ := table P) (K := bound) ?_ ?_
    highSigma 1
  · intro r m hm
    obtain ⟨rfl, rfl⟩ := family_environment_member r m hm
    exact actual_allSound P 4 fam rfl
  · intro r m hm
    obtain ⟨rfl, rfl⟩ := family_environment_member r m hm
    exact ⟨by decide, by decide⟩

/-- A bounded mirror in the exact preceding-own prefix would contradict
the fit failure. Thus the original bounds in this fixture cannot entail
that stronger certificate uniformly at recursor-bound instances. -/
theorem no_bounded_mirror (P : Premises4) :
    ¬ BoundedParameterMirrorTransport.Bounds eFam 1 highSigma 4 bound
      [ownParam] [.sort .zero] rfl := by
  intro hmir
  have hfit := BoundedParameterMirrorTransport.parameters_fit P (table P)
    highSigma bound (family_environment_sound P) [ownParam] [.sort .zero] rfl
    hmir [tyv pempty] (family_parameters_fit P (table P))
  exact own_parameter_has_no_member P (table P) ρ0 (tyv pempty) hfit.1

def Witness (P : Premises4) : Prop :=
  PropOnlyEmptyMirrorBounds.Witness ∧
  PointwiseRole.GInv P bound envWfT ∧
  TelFits (mkM P (table P)) highSigma pNode.a.family.parameters ρ0 [tyv pempty] ∧
  (∀ j, ¬ TelFits (mkM P (table P)) highSigma
    (pNode.a.constructorViews j).parameters ρ0 [tyv pempty]) ∧
  ¬ BoundedParameterMirrorTransport.Bounds eFam 1 highSigma 4 bound
    [ownParam] [.sort .zero] rfl

theorem witness (P : Premises4) : Witness P :=
  ⟨original_bounds_witness, invariant P, family_parameters_fit P (table P),
    own_parameters_do_not_fit P (table P), no_bounded_mirror P⟩

end Rcic.F3.PSet.PropOnlyEmptyMirrorBoundary

#print axioms Rcic.F3.PSet.PropOnlyEmptyMirrorBoundary.argument_not_member
#print axioms Rcic.F3.PSet.PropOnlyEmptyMirrorBoundary.invariant
#print axioms Rcic.F3.PSet.PropOnlyEmptyMirrorBoundary.no_bounded_mirror
#print axioms Rcic.F3.PSet.PropOnlyEmptyMirrorBoundary.witness
