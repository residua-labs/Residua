import rcic.RcicF3DataSeparatedFixture
import rcic.RcicF3PointwiseDataFiniteList
import rcic.RcicF3PointwiseRemainingDataSeparated

/-!
# A strict admitted witness for exact DATA first-field separation

The actual admitted family F : Prop → Type has the constructor
mk : (p q : Prop) → F q. The first index is the second field, bvar 0;
it is distinct from the first field, bvar 1. Thus this group lies outside
the complete preceding DATA covered union and inside the new union.

The original BoundG and BoundDG are produced. The complete new producer
returns original GInv and is applied to the actual pointwise table,
including its prescribed extension-stable iota conclusion. No imported
source, arbitrary DATA closure, or historical graph reduction is claimed.
Source-only draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.PointwiseDataSeparatedWitness
open Rcic.Declarative Rcic.Model.PS RawFamily
open Rcic.Declarative.DataSeparatedFixture

abbrev Node := RecNode emptyEnv eAll 4 6 recMem

def bound : Nat → Nat := fun _ => 1

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup EnvWfT.empty (f := 4) (fm := fam)
    (ctors := [(5, Rcic.Declarative.DataSeparatedFixture.mk)]) (rr := 6) (rm := recMem)
    rfl ctorClasses rfl membersT

theorem family_member (node : Node) : node.a.family.member = fam :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

theorem count (node : Node) : node.a.constructors.length = 1 :=
  node_ctors_length (ctors := [(5, Rcic.Declarative.DataSeparatedFixture.mk)]) node rfl

theorem constructor_member (node : Node) (i : Fin node.a.constructors.length) :
    node.a.constructors[i.val] = Rcic.Declarative.DataSeparatedFixture.mk := by
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 1 := count node ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact Option.some.inj (h.symm.trans rfl)

/-- Projection equality from the actual group scan; the proof does not
identify independent Type-valued nodes or typing derivations. -/
theorem selected_data : famDataOf plan.node.a = famDataOf recA := by
  have h := (groupNode EnvWfT.empty (f := 4) (fm := fam)
    (ctors := [(5, Rcic.Declarative.DataSeparatedFixture.mk)]) (rr := 6) (rm := recMem)
    rfl ctorClasses rfl membersT).property
  change some (famDataOf recA) = some (famDataOf plan.node.a) at h
  exact (Option.some.inj h).symm

theorem family_parameters : plan.node.a.family.parameters = [] :=
  congrArg FamData.params selected_data

theorem family_indices : plan.node.a.family.indices = [propTy] :=
  congrArg FamData.indices selected_data

theorem family_level : plan.node.a.family.resultLevel = one :=
  congrArg FamData.resLevel selected_data

theorem family_level_at (node : Node) : node.a.family.resultLevel = one :=
  (Rcic.F3.StepWGroup.nodeResult_unique node plan.node).trans family_level

theorem matching_parameters (j : Fin plan.node.a.constructors.length) :
    (plan.node.a.constructorViews j).parameters = plan.node.a.family.parameters := by
  have hl : (plan.node.a.constructorViews j).parameters.length = 0 := by
    rw [(plan.node.a.constructorViews j).parameterCount, family_parameters]
    rfl
  exact (List.eq_nil_of_length_eq_zero hl).trans family_parameters.symm

/-- Both lists are read from the same actual selected descriptor. -/
theorem constructor_data (j : Fin plan.node.a.constructors.length) :
    (plan.node.a.constructorViews j).fields = [propTy, propTy] ∧
      (plan.node.a.constructorViews j).resultIndices = [.bvar 0] := by
  have hc := famDataOf_ctor plan.node.a j
  rw [selected_data] at hc
  have hj : j.val < 1 := count plan.node ▸ j.isLt
  have h0 : j.val = 0 := by omega
  have hlookup : (famDataOf recA).ctors[j.val]? =
      some ([propTy, propTy], [Expr.bvar 0]) := by
    rw [h0]
    rfl
  have he := Option.some.inj (hlookup.symm.trans hc)
  exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- Successful literal zero-domain reads constrain the actual cache.
The reusable reader/cache proof is the one already used by List and Vec. -/
theorem no_fun : NoFunRec plan.node := by
  intro j s hs
  have hread : ∀ A ∈ (plan.node.a.constructorViews j).fields,
      ∃ readFuel, piTelescopeFuel plan.node.E0 readFuel A = some ([], A) := by
    intro A hA
    rw [(constructor_data j).1] at hA
    rcases List.mem_cons.mp hA with rfl | hA
    · exact ⟨2, rfl⟩
    · have he := List.mem_singleton.mp hA
      subst A
      exact ⟨2, rfl⟩
  have h := PointwiseDataFiniteList.fields_no_fun_of_readers
    (plan.constructors j).fields hread
  rw [(plan.constructors j).shapes_admitted] at h
  exact h s hs

theorem first_field_separated :
    PointwiseDataFiniteSeparated.FirstFieldSeparated plan.node := by
  intro j
  apply Or.inr
  rw [(constructor_data j).1, (constructor_data j).2]
  decide

theorem not_first_index_rigid :
    ¬ PointwiseDataFiniteRigid.FirstIndexRigid plan.node := by
  intro h
  let j : Fin plan.node.a.constructors.length :=
    ⟨0, by rw [count plan.node]; decide⟩
  have h0 := h j 0
  rw [(constructor_data j).2] at h0
  exact h0 rfl

theorem uniform_type : UniformType plan.node.a.family.resultLevel := by
  rw [family_level]
  exact family_type

/-- Stored constructor typing is in the original family-only scope.
All its levels are closed, and every constant instance is empty. -/
theorem stored_typed (K σ : Nat → Nat) (node : Node)
    (i : Fin node.a.constructors.length) :
    ∃ u : Level, ∃ d : HasTyT eFam node.a.family.member.arity []
      (node.a.constructors[i.val]).mtype (.sort u), LOKt σ 4 K d := by
  rw [family_member node, constructor_member node i]
  refine ⟨.imax one (.imax one one), mk_type_typed rfl, ?_⟩
  simp [mk_type_typed, famApp_typed, LOKt, LevelsOK, evalTotal, one]

theorem boundG (K : Nat → Nat) : BoundG K envWfT := by
  refine ⟨trivial, ?_, ?_, ?_⟩
  · intro node i vs _ _
    exact stored_typed K (σOf vs) node i
  · refine ⟨trivial, ?_, trivial, trivial⟩
    intro vs _ _ k
    obtain ⟨k, hk⟩ := k
    match k, hk with
    | 0, _ => exact ⟨HasTyT.sort [] .zero, by change 1 ≤ 4; decide⟩
    | 1, _ => exact ⟨HasTyT.sort [.assumption propTy] .zero,
        by change 1 ≤ 4; decide⟩
  · intro node hProp _ _ _ _ _
    have hz := hProp (fun _ => 0)
    rw [family_level_at node] at hz
    exact False.elim (Nat.noConfusion hz)

theorem boundDG : BoundDG bound envWfT := by
  apply boundDG_of_boundG bound envWfT ?_ (boundG bound)
  exact ⟨trivial, fun _ _ _ => Nat.le_refl 1⟩

/-- The complete original group invariant with its empty predecessor
paid by the existing empty-environment producer. -/
theorem invariant (P : Premises4) : PointwiseRole.GInv P bound envWfT :=
  PointwiseDataFiniteSeparated.invariant_step P bound EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, Rcic.Declarative.DataSeparatedFixture.mk)]) (rr := 6) (rm := recMem)
    rfl ctorClasses rfl membersT uniform_type no_fun matching_parameters
    first_field_separated (boundG bound) boundDG (PointwiseRole.gInv_empty P bound)

theorem actual_table (P : Premises4) :
    AllSound P (PointwiseRole.table P envWfT) bound eAll ∧
      ∀ Efin, (∀ r m, eAll.members r = some m → Efin.members r = some m) →
        ∀ r m, eAll.members r = some m → m.mclass = .recursorM →
          IotaAt P (PointwiseRole.table P envWfT) bound Efin r :=
  invariant P (PointwiseRole.arities eAll) (PointwiseRole.arities_agree eAll)
    (NormRole.envCtx envWfT) (fun _ _ => rfl)
    (EvalRole.envPlan envWfT) (fun _ _ => rfl) _
    (PointwiseRole.table_spec P envWfT).2.1

/-- The old complete union fails on this same admitted group: its
constructor list is nonempty, its stored family header is a Pi, and
its first result index is a bound variable. -/
theorem not_previously_covered :
    ¬ PointwiseRemainingDataRigid.DataCovered EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, Rcic.Declarative.DataSeparatedFixture.mk)]) (rr := 6) (rm := recMem)
      rfl ctorClasses rfl membersT := by
  intro h
  rcases h with hOld | ⟨_, _, hRigid⟩
  · rcases hOld with he | ⟨u, he, _⟩
    · cases he
    · cases he
  · exact not_first_index_rigid hRigid

theorem newly_covered :
    PointwiseRemainingDataSeparated.DataCovered EnvWfT.empty
      (f := 4) (fm := fam) (ctors := [(5, Rcic.Declarative.DataSeparatedFixture.mk)]) (rr := 6) (rm := recMem)
      rfl ctorClasses rfl membersT :=
  Or.inr ⟨matching_parameters, no_fun, first_field_separated⟩

def Witness (P : Premises4) : Prop :=
  Nonempty (EnvWfT eAll) ∧
  BoundG bound envWfT ∧ BoundDG bound envWfT ∧
  plan.node.a.family.parameters = [] ∧
  plan.node.a.family.indices = [propTy] ∧
  (∀ j : Fin plan.node.a.constructors.length,
    (plan.node.a.constructorViews j).fields = [propTy, propTy] ∧
      (plan.node.a.constructorViews j).resultIndices = [.bvar 0]) ∧
  NoFunRec plan.node ∧
  PointwiseDataFiniteSeparated.FirstFieldSeparated plan.node ∧
  ¬ PointwiseDataFiniteRigid.FirstIndexRigid plan.node ∧
  (PointwiseRemainingDataSeparated.DataCovered EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, Rcic.Declarative.DataSeparatedFixture.mk)]) (rr := 6) (rm := recMem)
    rfl ctorClasses rfl membersT) ∧
  (¬ PointwiseRemainingDataRigid.DataCovered EnvWfT.empty
    (f := 4) (fm := fam) (ctors := [(5, Rcic.Declarative.DataSeparatedFixture.mk)]) (rr := 6) (rm := recMem)
    rfl ctorClasses rfl membersT) ∧
  PointwiseRole.GInv P bound envWfT ∧
  AllSound P (PointwiseRole.table P envWfT) bound eAll

theorem witness (P : Premises4) : Witness P :=
  ⟨⟨envWfT⟩, boundG bound, boundDG, family_parameters, family_indices,
    constructor_data, no_fun, first_field_separated, not_first_index_rigid,
    newly_covered, not_previously_covered, invariant P, (actual_table P).1⟩

theorem component_nonrefutable (P : Premises4) : ¬ (Witness P → False) :=
  fun h => h (witness P)

end Rcic.F3.PSet.PointwiseDataSeparatedWitness

#print axioms Rcic.F3.PSet.PointwiseDataSeparatedWitness.no_fun
#print axioms Rcic.F3.PSet.PointwiseDataSeparatedWitness.boundG
#print axioms Rcic.F3.PSet.PointwiseDataSeparatedWitness.boundDG
#print axioms Rcic.F3.PSet.PointwiseDataSeparatedWitness.not_previously_covered
#print axioms Rcic.F3.PSet.PointwiseDataSeparatedWitness.invariant
#print axioms Rcic.F3.PSet.PointwiseDataSeparatedWitness.actual_table
#print axioms Rcic.F3.PSet.PointwiseDataSeparatedWitness.witness
#print axioms Rcic.F3.PSet.PointwiseDataSeparatedWitness.component_nonrefutable
