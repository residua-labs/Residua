import rcic.RcicF3NormPendAWValue
import rcic.RcicF3RawFamilyGroup

/-!
# The actual normalized W recursor package

The exact canonical W descriptor and endpoint agree with the proved raw
fixture. These equalities produce all current-group equations from the
new normalized faithful interpretation. The existing W recursor theorem
then supplies its stored-type membership and the complete literal RecPkg.
No old invariant or predecessor soundness premise is needed for this
recursor component, and K is arbitrary.

IotaAt retains the existing witness domain: the leaf has a direct row,
whereas the higher-order constructor has no legacy IotaWitness. This
module does not assert universal normalized-shape iota or StepAG.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPendAWRecPkg
open Rcic.Declarative Rcic.Model.PS RawFamilyGroup

/-- Actual normalized faithfulness supplies every current-group equation.
The context and plan functions may vary outside the admitted environment. -/
theorem values (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom PendAW.eAll r → ctx r = NormRole.envCtx PendAWGroup.wft r)
    (hplans : ∀ r, Dom PendAW.eAll r → plans r = EvalRole.envPlan PendAWGroup.wft r)
    (hF : EvalRole.Faithful RawFamily.role P μ ctx plans PendAW.eAll) :
    GroupValues P μ PendAW.fam PendAW.pNode := by
  have hTF := typeFacts_of_envWfT PendAWGroup.wft
  have hctxG : ∀ r, Dom PendAW.eAll r → ctx r =
      groupRoles PendAWBridge.fd 4 7 (NormRole.envCtx natEnvUWfT) r := by
    intro r hr
    rw [hctx r hr]
    change groupRoles (EvalPlanNormal.fd NormPendAW.plan) 4 7
      (NormRole.envCtx natEnvUWfT) r = _
    rw [NormPendAW.normalized_descriptor]
  have hty : PendAW.fam.mtype = famType PendAWBridge.fd := by
    rw [PendAWBridge.fdExact]
    rfl
  refine ⟨?_, ?_, ?_, hty, PendAWLim.Typed.bounded, ?_⟩
  · intro vs
    have h := hF 4 PendAW.fam rfl vs
    rw [hctxG 4 (dom_of_members (show PendAW.eAll.members 4 = some PendAW.fam from rfl)),
      groupRoles_at_f] at h
    exact h
  · intro i vs
    have hc := node_ctor_member PendAW.pNode i
    have h := hF _ _ hc vs
    have hi : 4 + 1 + i.val < 7 := by
      have hn : i.val < 2 := i.isLt
      exact Nat.add_lt_add_left hn 5
    rw [hctxG _ (dom_of_members hc), groupRoles_at_ctor _ _ hi] at h
    exact h
  · intro vs
    have hr : PendAW.eAll.members 7 = some PendAW.recMem := rfl
    have h := hF 7 PendAW.recMem hr vs
    rw [hctxG 7 (dom_of_members hr), groupRoles_at_rr _ (by decide : 4 < 7),
      hplans 7 (dom_of_members hr), NormPendAW.canonical_plan] at h
    change Equiv (μ 7 vs) (EvalPlanValue.memberValue (mkM P μ) (σOf vs)
      NormPendAW.plan PendAW.recMem) at h
    rw [NormPendAWValue.member_value_eq] at h
    exact h
  · intro i
    have h := (hTF _ _ (node_ctor_member PendAW.pNode i)).2.1
    rw [(PendAW.pNode.a.constructorViews i).arity] at h
    exact h

/-- Reuse the existing W recursor proof at its literal inputs. Its old
context record's unused scope field is not assumed or manufactured here. -/
theorem rec_pkg_of_values (P : Premises4) (K : Nat → Nat)
    (μ : Nat → List Nat → PSet.{4})
    (hV : GroupValues P μ PendAW.fam PendAW.pNode) :
    RecPkg P μ K PendAW.eAll 7 PendAW.recMem := by
  have hTF := typeFacts_of_envWfT PendAWGroup.wft
  have hlim : ∀ vs, Equiv (μ PendAW.recA.family.ref vs)
      (RawFamily.role P μ (famDataOf PendAW.recA) vs) := hV.fam
  have hG : GroupFaith P μ PendAW.fam PendAW.pNode :=
    hV.toLegacy P (RawWGeneral.fixed P μ hlim)
  have hr : PendAW.eAll.members 7 = some PendAW.recMem := rfl
  have hbody : PendAW.recMem.body = none := rfl
  constructor
  · have hcl := (hTF 7 PendAW.recMem hr).1
    have hlvl := (hTF 7 PendAW.recMem hr).2.1
    intro σ ls ρ hlen _
    refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
    rw [den_inst_canon (mkM P μ) σ ls ρ PendAW.recMem.mtype hcl (hlen ▸ hlvl)]
    refine mem_congr_left (hG.recur _).symm ?_
    exact recVal_mem_rec_KTA P μ PendAW.recA PendARoleW.groupA (ls.map (evalTotal σ))
      (PendAWLim.Typed.nonIR P μ) PendAWLim.Typed.fresh
      (fun vs => (hlim vs).trans (RawWGeneral.role_value P μ vs))
      (groupFaith_ctorAt P hG _) (PendAWLim.Typed.typeRead _)
  · intro Efin hsub
    exact RoleModel.iota_type_of_witness_row P hG hsub hr PendARoleW.witnessRow
      PendAWLim.Typed.typeRead hG.ctorBounded

theorem actual_values (P : Premises4) :
    GroupValues P (NormPendAW.table P) PendAW.fam PendAW.pNode :=
  values P (NormPendAW.table P) (NormRole.envCtx PendAWGroup.wft)
    (EvalRole.envPlan PendAWGroup.wft) (fun _ _ => rfl) (fun _ _ => rfl)
    (NormPendAW.faithful P)

/-- Both stored-type soundness and stable literal iota are produced at
the actual normalized installed table, for every bound function. -/
theorem actual_rec_pkg (P : Premises4) (K : Nat → Nat) :
    RecPkg P (NormPendAW.table P) K PendAW.eAll 7 PendAW.recMem :=
  rec_pkg_of_values P K (NormPendAW.table P) (actual_values P)

def Witness (P : Premises4) : Prop :=
  NormPendAWValue.Witness P ∧
  GroupValues P (NormPendAW.table P) PendAW.fam PendAW.pNode ∧
  (∀ K, RecPkg P (NormPendAW.table P) K PendAW.eAll 7 PendAW.recMem)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormPendAWValue.component_witness P, actual_values P, actual_rec_pkg P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPendAWRecPkg
