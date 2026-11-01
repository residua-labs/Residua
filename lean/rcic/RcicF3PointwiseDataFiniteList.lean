import rcic.RcicF3PointwiseDataFiniteRigid
import rcic.RcicF3CheckedCtorWorldListAttack
import rcic.RcicF3PointwiseNatInvariant
import rcic.RcicF3PointwiseRemainingRefined

/-!
# The admitted polymorphic List group has the original pointwise invariant

The producer is applied to the actual Nat-then-List admission, its selected
node and its pointwise table. Both original bound packages are produced at
the existing uneven bound (nil 2, cons 1, recursor 3). Literal parameter
matching comes from the stored telescopes. NoFunRec comes from successful
zero-domain reads of the actual fields, compared with the actual cache.

List has one term parameter and two constructors, so it lies strictly
outside the preceding DATA coverage (empty constructors or a literal sort
header). Its W agreement is produced by the new result-cut theorem. The
imported checked-world fixture supplies syntax and original bound lemmas;
its group-check theorem is not an input to this invariant.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.PointwiseDataFiniteList
open Rcic.Declarative Rcic.Model.PS RawFamily PosList
open CheckedCtorWorldListAttack
  (Node plan uneven ctorClasses family_member family_parameters family_level
   count constructor_member own_telescope matching_parameters selected_data
   stored_at_rec_bound)

/-- A successful literal zero-domain read bounds the actual cached depth,
even when the cache chose a different successful fuel. -/
theorem field_no_fun_of_reader
    {E : ResolvedEnv} {fuel f nu np ni prior readFuel : Nat}
    {A : Expr Nat} {s : FieldShape}
    (q : EvalPlan.Field E fuel f nu np ni prior A s)
    (hr : piTelescopeFuel E readFuel A = some ([], A)) :
    s = .nonrecursive ∨ s = .recursive 0 := by
  cases q with
  | plain => exact Or.inl rfl
  | @recursive inner r =>
      have he := Option.some.inj
        ((piTelescopeFuel_mono E (Nat.le_max_left fuel readFuel) r.read).symm.trans
          (piTelescopeFuel_mono E (Nat.le_max_right fuel readFuel) hr))
      have hd : r.domains = [] := congrArg Prod.fst he
      have hi : inner = 0 := r.depth.symm.trans (congrArg List.length hd)
      exact Or.inr (congrArg FieldShape.recursive hi)

theorem fields_no_fun_of_readers
    {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (q : EvalPlan.Fields E fuel f nu np ni prior ss Fs)
    (hr : ∀ A ∈ Fs, ∃ readFuel, piTelescopeFuel E readFuel A = some ([], A)) :
    ∀ s ∈ ss, s = .nonrecursive ∨ s = .recursive 0 := by
  revert hr
  induction q with
  | nil =>
      intro _ s hs
      exact (List.not_mem_nil s hs).elim
  | @cons prior s A ss Fs head tail ih =>
      intro hr t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · obtain ⟨readFuel, hread⟩ := hr A (List.mem_cons_self _ _)
        exact field_no_fun_of_reader head hread
      · exact ih (fun B hB => hr B (List.mem_cons_of_mem _ hB)) t ht

theorem no_indices : plan.node.a.family.indices = [] :=
  congrArg FamData.indices selected_data

theorem selected_fields (j : Fin plan.node.a.constructors.length) :
    (plan.node.a.constructorViews j).fields = [] ∨
      (plan.node.a.constructorViews j).fields = [hdField, tlField] := by
  have h := own_telescope plan.node j
  rw [matching_parameters j, family_parameters] at h
  rcases h with ⟨he, _⟩ | ⟨he, _⟩
  · exact Or.inl (List.cons.inj he).2
  · exact Or.inr (List.cons.inj he).2

/-- The finite hypothesis concerns the actual selected admission cache. -/
theorem no_fun : NoFunRec plan.node := by
  intro j s hs
  have hread : ∀ A ∈ (plan.node.a.constructorViews j).fields,
      ∃ readFuel, piTelescopeFuel plan.node.E0 readFuel A = some ([], A) := by
    intro A hA
    rcases selected_fields j with he | he
    · rw [he] at hA
      exact (List.not_mem_nil _ hA).elim
    · rw [he] at hA
      rcases List.mem_cons.mp hA with rfl | hA
      · exact ⟨2, rfl⟩
      · have he : A = tlField := List.mem_singleton.mp hA
        subst A
        have hb := transparentBody_family plan.node.a.family [.param 0]
        rw [plan.node.fam] at hb
        exact ⟨2, piTelescopeFuel_famApp [.bvar 1] hb (Nat.le_refl 2)⟩
  have h := fields_no_fun_of_readers (plan.constructors j).fields hread
  rw [(plan.constructors j).shapes_admitted] at h
  exact h s hs

theorem first_index_rigid : PointwiseDataFiniteRigid.FirstIndexRigid plan.node :=
  PointwiseDataFiniteRigid.firstIndexRigid_of_no_indices plan.node no_indices

theorem uniform_type : UniformType plan.node.a.family.resultLevel := by
  rw [family_level]
  exact uniformType_succ_param 0

theorem family_level_at (node : Node) :
    node.a.family.resultLevel = .succ (.param 0) :=
  (Rcic.F3.StepWGroup.nodeResult_unique node plan.node).trans family_level

theorem vector_head_le {vs : List Nat} {b : Nat}
    (hvs : ∀ v, v ∈ vs → v ≤ b) : σOf vs 0 ≤ b := by
  cases vs with
  | nil => exact Nat.zero_le b
  | cons v vs => exact hvs v (List.mem_cons_self _ _)

/-- This derives the original stored-type and own-walk bounds. It does
not strengthen the bound package or assume the checked-world guard. -/
theorem boundG : BoundG uneven listEnvUWfT := by
  refine ⟨natEnvUWfT_classG.2 uneven, ?_, ?_, ?_⟩
  · intro node i vs _ hvs
    apply stored_at_rec_bound node i vs
    intro v hv
    have hvc := hvs v hv
    rcases constructor_member node i with ⟨_, hi⟩ | ⟨_, hi⟩
    · rw [hi] at hvc
      exact Nat.le_trans hvc (by decide : uneven (8 + 1 + 0) ≤ uneven 11)
    · rw [hi] at hvc
      exact Nat.le_trans hvc (by decide : uneven (8 + 1 + 1) ≤ uneven 11)
  · refine ⟨trivial, ?_, ?_, trivial, trivial⟩
    · intro vs _ hvs k
      have h0 : σOf vs 0 ≤ 2 := vector_head_le hvs
      have hs : σOf vs 0 + 1 ≤ 4 := by omega
      obtain ⟨k, hk⟩ := k
      match k, hk with
      | 0, _ => exact ⟨HasTyT.sort [] (.param 0), hs⟩
    · intro vs _ hvs k
      have h0 : σOf vs 0 ≤ 1 := vector_head_le hvs
      have hs : σOf vs 0 + 1 ≤ 4 := by omega
      have hc : LevelsOK (σOf vs) (uneven 8) [.param 0] := by
        intro l hl
        rw [List.mem_singleton.mp hl]
        change σOf vs 0 ≤ 3
        omega
      obtain ⟨k, hk⟩ := k
      match k, hk with
      | 0, _ => exact ⟨HasTyT.sort [] (.param 0), hs⟩
      | 1, _ => exact ⟨HasTyT.bvar _ 0 _ rfl, True.intro⟩
      | 2, _ => exact ⟨listOfTyT (E := listFamNilU) (n := 1) rfl rfl
          (.bvar _ 1 _ rfl), hc, True.intro⟩
  · intro node hProp _ _ _ _ _
    have hz := hProp (fun _ => 0)
    rw [family_level_at node] at hz
    exact False.elim (Nat.noConfusion hz)

theorem boundDG : BoundDG uneven listEnvUWfT :=
  CheckedCtorWorldListAttack.boundDG

/-- Full original GInv, with the exact prior Nat invariant produced. -/
theorem invariant (P : Premises4) :
    PointwiseRole.GInv P uneven listEnvUWfT :=
  PointwiseDataFiniteRigid.invariant_step P uneven natEnvUWfT rfl
    ctorClasses rfl listMembersU uniform_type no_fun matching_parameters
    first_index_rigid boundG boundDG (PointwiseNatInvariant.gInv P uneven)

/-- The original pointwise installer and all its prescribed extensions
are retained. This is not an independently chosen List interpretation. -/
theorem actual_table (P : Premises4) :
    AllSound P (PointwiseRole.table P listEnvUWfT) uneven listEnvUT ∧
      ∀ Efin, (∀ r m, listEnvUT.members r = some m → Efin.members r = some m) →
        ∀ r m, listEnvUT.members r = some m → m.mclass = .recursorM →
          IotaAt P (PointwiseRole.table P listEnvUWfT) uneven Efin r :=
  invariant P (PointwiseRole.arities listEnvUT) (PointwiseRole.arities_agree listEnvUT)
    (NormRole.envCtx listEnvUWfT) (fun _ _ => rfl)
    (EvalRole.envPlan listEnvUWfT) (fun _ _ => rfl) _
    (PointwiseRole.table_spec P listEnvUWfT).2.1

/-- Strictly beyond the previous produced DATA domain. -/
theorem not_previously_covered :
    ¬ PointwiseRemainingRefined.DataCovered natEnvUWfT (fm := raisedFam)
      (ctors := [(9, listUNilMember), (10, listUConsMember)])
      (rr := 11) (rm := listURecMember) rfl ctorClasses rfl listMembersU := by
  intro h
  rcases h with he | ⟨u, he, _⟩
  · cases he
  · cases he

def Witness (P : Premises4) : Prop :=
  Nonempty (EnvWfT listEnvUT) ∧
  BoundG uneven listEnvUWfT ∧ BoundDG uneven listEnvUWfT ∧
  plan.node.a.family.parameters = [paramSort] ∧
  NoFunRec plan.node ∧ PointwiseDataFiniteRigid.FirstIndexRigid plan.node ∧
  (∀ j : Fin plan.node.a.constructors.length,
    (plan.node.a.constructorViews j).parameters = plan.node.a.family.parameters) ∧
  (¬ PointwiseRemainingRefined.DataCovered natEnvUWfT (fm := raisedFam)
    (ctors := [(9, listUNilMember), (10, listUConsMember)])
    (rr := 11) (rm := listURecMember) rfl ctorClasses rfl listMembersU) ∧
  PointwiseRole.GInv P uneven listEnvUWfT ∧
  AllSound P (PointwiseRole.table P listEnvUWfT) uneven listEnvUT

theorem witness (P : Premises4) : Witness P :=
  ⟨⟨listEnvUWfT⟩, boundG, boundDG, family_parameters, no_fun,
    first_index_rigid, matching_parameters, not_previously_covered,
    invariant P, (actual_table P).1⟩

end Rcic.F3.PSet.PointwiseDataFiniteList

#print axioms Rcic.F3.PSet.PointwiseDataFiniteList.boundG
#print axioms Rcic.F3.PSet.PointwiseDataFiniteList.no_fun
#print axioms Rcic.F3.PSet.PointwiseDataFiniteList.invariant
#print axioms Rcic.F3.PSet.PointwiseDataFiniteList.witness
