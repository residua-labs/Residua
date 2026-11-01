import rcic.RcicF3NormPendAW

/-!
# Exact production-endpoint compatibility at the admitted PendA W fixture

Successful admission forces the actual W plan to contain the two shapes
[] and [recursive 1]. This is proved from its reader certificates, without
identifying the Type-valued canonical node with the explicit fixture node.
For this fixture only, the new data endpoint is the existing raw recEnd.
The actual normalized installed recursor therefore has that abstraction.

The height-omega endpoint theorem uses the actual installed table and the
complete recursor input tuple. It states membership in tv True; it does
not assert that an arbitrary supplied motive or this whole tuple is typed.
Universal recursor typing, GInv, and StepAG remain unclaimed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPendAWValue
open Rcic.Declarative PiIndex NormPendAW

theorem node_family_body (node : PendAWGroup.Node) :
    transparentBody node.E0 4 [] = none := by
  have hm := node.a.family.present
  rw [node.fam, PendAWGroup.familyMember node] at hm
  unfold transparentBody
  rw [hm]
  rfl

theorem field_shape (E : ResolvedEnv) (hbody : transparentBody E 4 [] = none)
    {fuel f nu np ni prior : Nat} {s : FieldShape} (hf : f = 4)
    (p : EvalPlan.Field E fuel f nu np ni prior PendAW.field s) :
    s = .recursive 1 := by
  subst f
  cases p with
  | plain h => cases h
  | @recursive inner r =>
      have hd : r.domains = [.bvar 0] := congrArg Prod.fst
        (field_reader E hbody fuel r.domains
          (foldApps (.const 4 (canonL nu)) r.arguments) r.read)
      have hi : inner = 1 := r.depth.symm.trans (congrArg List.length hd)
      exact congrArg FieldShape.recursive hi

theorem singleton_shapes (E : ResolvedEnv) (hbody : transparentBody E 4 [] = none)
    {fuel f nu np ni prior : Nat} {ss : List FieldShape} (hf : f = 4)
    (p : EvalPlan.Fields E fuel f nu np ni prior ss [PendAW.field]) :
    ss = [.recursive 1] := by
  cases p with
  | cons head tail =>
      cases tail with
      | nil => exact congrArg (fun s => [s]) (field_shape E hbody hf head)

/-- Every actual constructor slot has its literal admitted shape. -/
theorem node_shapes (node : PendAWGroup.Node) (i : Fin node.a.constructors.length) :
    node.h14.shapesAt i = if i.val = 0 then [] else [.recursive 1] := by
  let c := EvalPlan.constructorOfNode node i
  have hc : c.shapes = node.h14.shapesAt i := c.shapes_admitted
  rcases (PendAWGroup.views node i).2.2 with ⟨hfields, hpos⟩ | ⟨hfields, hpos⟩
  · have hl := c.fields.length
    rw [hfields] at hl
    have hs : c.shapes = [] := List.eq_nil_of_length_eq_zero hl
    exact hc.symm.trans (hs.trans (if_pos hpos).symm)
  · have hp := c.fields
    rw [hfields] at hp
    have hs : c.shapes = [.recursive 1] :=
      singleton_shapes node.E0 (node_family_body node) node.fam hp
    have hn : i.val ≠ 0 := fun h => Nat.noConfusion (hpos.symm.trans h)
    exact hc.symm.trans (hs.trans (if_neg hn).symm)

theorem node_plan (node : PendAWGroup.Node) :
    RecPlan.nodePlan node = [[], [.recursive 1]] := by
  have hlen : node.a.constructors.length = 2 :=
    node_ctors_length (ctors := [(5, PendAW.leaf), (6, PendAW.node)]) node rfl
  apply List.ext_getElem
  · simpa only [RecPlan.nodePlan, List.length_map, List.length_range,
      List.length_cons, List.length_nil] using hlen
  · intro j hj hr
    have hi : j < node.a.constructors.length := by
      rw [hlen]
      exact hr
    let i : Fin node.a.constructors.length := ⟨j, hi⟩
    have hs := (RecPlan.nodePlan_spec node i).1
    rw [List.getElem?_eq_getElem hj] at hs
    refine (Option.some.inj hs).trans ((node_shapes node i).trans ?_)
    change (if j = 0 then [] else [.recursive 1]) =
      ([[], [.recursive 1]] : List (List FieldShape))[j]'hr
    rcases PendAWGroup.ctorInfo node i with ⟨_, hpos⟩ | ⟨_, hpos⟩
    · change j = 0 at hpos
      subst j
      rfl
    · change j = 1 at hpos
      subst j
      rfl

theorem raw_plan : RecPlan.rawPlan PendAWBridge.fd = [[], [.recursive 1]] := by
  rw [PendAWBridge.fdExact]
  rfl

/-- The actual endpoint equality holds for the full valuation and every
semantic input environment, rather than only on a bounded fixture slice. -/
theorem endpoint_eq (M : Interp.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    EvalPlanValue.endValue M σ plan ρ = recEnd M σ PendAWBridge.fd ρ := by
  have hn : evalTotal σ plan.node.a.family.resultLevel ≠ 0 := by
    rw [(PendAWGroup.familyInfo plan.node).2.2]
    change 1 ≠ 0
    decide
  rw [EvalPlanValue.endValue_fallback M σ plan ρ (fun h => hn h.1),
    raw_descriptor, node_plan plan.node, ← raw_plan]
  exact (RecPlanValue.laws M σ PendAWBridge.fd (RecPlan.rawPlan PendAWBridge.fd)).2 ρ

theorem member_value_eq (M : Interp.{4}) (σ : Nat → Nat) :
    EvalPlanValue.memberValue M σ plan PendAW.recMem =
      piLam M σ (recEnd M σ PendAWBridge.fd) ρ0 PendAW.recMem.mtype := by
  unfold EvalPlanValue.memberValue
  rw [funext (endpoint_eq M σ)]

theorem recursor_role : NormRole.envCtx PendAWGroup.wft 7 =
    .recursor (EvalPlanNormal.fd plan) := by
  change groupRoles (EvalPlanNormal.fd plan) 4 7 (NormRole.envCtx natEnvUWfT) 7 = _
  rw [groupRoles, if_neg (by decide : ¬ (7 = 4))]
  exact if_pos rfl

/-- The stored equation is at the actual normalized installed table. -/
theorem installed_recursor (P : Premises4) (vs : List Nat) :
    Equiv (table P 7 vs)
      (piLam (mkM P (table P)) (σOf vs)
        (recEnd (mkM P (table P)) (σOf vs) PendAWBridge.fd) ρ0 PendAW.recMem.mtype) := by
  have h := faithful P 7 PendAW.recMem rfl vs
  rw [recursor_role, canonical_plan] at h
  change Equiv (table P 7 vs)
    (EvalPlanValue.memberValue (mkM P (table P)) (σOf vs) plan PendAW.recMem) at h
  rw [member_value_eq] at h
  exact h

noncomputable def input (P : Premises4) (mo : PSet.{4}) : Nat → PSet.{4} :=
  push [tyv fxS, mo, pempty, pempty, fxZW P] ρ0

/-- Parameters, motive, both minors and the actual height-omega major are
retained. Only the data endpoint ignores the motive's value here. -/
theorem endpoint_nodeCore (P : Premises4) (M : Interp.{4}) (σ : Nat → Nat)
    (mo : PSet.{4}) :
    EvalPlanValue.endValue M σ plan (input P mo) =
      RecPlan.nodeCore M PendAW.pNode [pempty, pempty] (fxZW P) := by
  rw [endpoint_eq]
  have hn : evalTotal σ PendAWBridge.fd.resLevel ≠ 0 := by
    rw [PendAWBridge.fdExact]
    change 1 ≠ 0
    decide
  unfold recEnd
  rw [cond_neg hn]
  change recCore M PendAWBridge.fd [pempty, pempty] (fxZW P) =
    RecPlan.nodeCore M PendAW.pNode [pempty, pempty] (fxZW P)
  unfold RecPlan.nodeCore
  rw [node_plan PendAW.pNode, ← raw_plan]
  exact (RecPlan.core_raw M PendAWBridge.fd [pempty, pempty] (fxZW P)).symm

theorem endpoint_height_omega (P : Premises4) (σ : Nat → Nat) (mo : PSet.{4}) :
    EvalPlanValue.endValue (mkM P (table P)) σ plan (input P mo) ∈ tv True := by
  rw [endpoint_nodeCore]
  have he : RecPlan.nodeCore (mkM P (table P)) PendAW.pNode [pempty, pempty] (fxZW P) =
      RecPlan.nodeCore (RawFamilyRecAtAttack.model P) PendAW.pNode
        [pempty, pempty] (fxZW P) := by
    unfold RecPlan.nodeCore RecPlan.core
    rw [recCore_of_dec (M := mkM P (table P)) (M' := RawFamilyRecAtAttack.model P) rfl]
  rw [he]
  exact (RawFamilyRecAtAttack.inhabited P).1

def Witness (P : Premises4) : Prop :=
  NormPendAW.Witness P ∧
  RecPlan.nodePlan plan.node = [[], [.recursive 1]] ∧
  (∀ (M : Interp.{4}) σ ρ,
    EvalPlanValue.endValue M σ plan ρ = recEnd M σ PendAWBridge.fd ρ) ∧
  (∀ vs, Equiv (table P 7 vs)
    (piLam (mkM P (table P)) (σOf vs)
      (recEnd (mkM P (table P)) (σOf vs) PendAWBridge.fd) ρ0 PendAW.recMem.mtype)) ∧
  (∀ σ mo, EvalPlanValue.endValue (mkM P (table P)) σ plan (input P mo) ∈ tv True)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormPendAW.component_witness P, node_plan plan.node, endpoint_eq,
    installed_recursor P, endpoint_height_omega P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

/-- The recursive constructor's literal position in the scanned W plan. -/
noncomputable def recursiveSlot : Fin plan.node.a.constructors.length :=
  ⟨1, by
    rw [node_ctors_length (ctors := [(5, PendAW.leaf), (6, PendAW.node)])
      plan.node rfl]
    decide⟩

/-- The actual canonical constructor cache inhabits the singleton field
premise. Its fuel is the stored cache fuel, not an additional hypothesis. -/
theorem actual_fields_inhabited :
    Nonempty (EvalPlan.Fields plan.node.E0
      (plan.constructors recursiveSlot).fuel 4 0 1 0 0
      [.recursive 1] [PendAW.field]) := by
  have hfields : (plan.node.a.constructorViews recursiveSlot).fields =
      [PendAW.field] := by
    rcases (PendAWGroup.views plan.node recursiveSlot).2.2 with
      ⟨_, hzero⟩ | ⟨hfields, _⟩
    · have h10 : (1 : Nat) = 0 := hzero
      exact False.elim (Nat.noConfusion h10)
    · exact hfields
  have hnonzero : recursiveSlot.val ≠ 0 := fun h => Nat.noConfusion h
  have hshapes : (plan.constructors recursiveSlot).shapes = [.recursive 1] :=
    (plan.constructors recursiveSlot).shapes_admitted.trans
      ((node_shapes plan.node recursiveSlot).trans (if_neg hnonzero))
  have harity : plan.node.a.family.member.arity = 0 := by
    rw [PendAWGroup.familyMember plan.node]
  obtain ⟨hparams, hindices, _⟩ := PendAWGroup.familyInfo plan.node
  refine ⟨?_⟩
  simpa only [plan.node.fam, harity, hparams, hindices, hshapes, hfields,
    List.length_cons, List.length_nil] using
    (plan.constructors recursiveSlot).fields

/-- Project the recursive field from that same actual stored cache. This
inhabits both the normalized-field identity and shape-helper premises. -/
theorem actual_field_inhabited :
    Nonempty (EvalPlan.Field plan.node.E0
      (plan.constructors recursiveSlot).fuel 4 0 1 0 0
      PendAW.field (.recursive 1)) := by
  obtain ⟨fields⟩ := actual_fields_inhabited
  cases fields with
  | cons head tail => exact ⟨head⟩

end Rcic.F3.PSet.NormPendAWValue
