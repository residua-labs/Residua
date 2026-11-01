import rcic.RcicF3NormDataRecPkg
import rcic.RcicF3NormDataIotaRowAttack

/-!
# The complete small-frame DATA package at the exact PendA W environment

The new generic producer is instantiated with the canonical installed W
table, its produced Nat predecessor and exact small normalized candidate.
The witness retains the higher-order constructor, the height-omega member,
typed stored minors and nonempty actual nodeCore result. It also exercises
the actual-table application decoder and full-key original-case wrapper.

The stable iota conjunct has the literal legacy-witness scope; the leaf
row has a separate nonempty operational equation. No universal shape-iota
or universal small-frame existence is claimed. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataRecPkgAttack
open Rcic.Declarative Rcic.Model.PS PiIndex RawFamily PropEval
open RawDataRecAttack (base parameter σ)
open NormDataRecMemAttack (plan)

theorem rec_pkg (P : Premises4) (k : Nat) :
    RecPkg P (base P) (fun _ => k) PendAW.eAll 7 PendAW.recMem :=
  NormDataRecPkg.rec_pkg P (base P) (fun _ => k)
    natEnvUWfT (f := 4) (fm := PendAW.fam)
    (ctors := [(5, PendAW.leaf), (6, PendAW.node)])
    (rr := 7) (rm := PendAW.recMem)
    rfl PendAWGroup.ctorClasses rfl PendAW.membersT
    PendAWGroup.walkAgree (PendAWGroup.boundG _) (PendAWGroup.boundDG k)
    NormDataRecMemAttack.matching_parameters (NormNatInvariant.gInv P _)
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    (fun _ _ => rfl) (fun _ _ => rfl) (NormPendAW.faithful P)
    (NormDataRecMemAttack.small_closed P) NormDataRecMemAttack.type_family

theorem omega_decoded (P : Premises4) :
    TelFits (mkM P (base P)) σ (PendAWBridge.fd.params ++ PendAWBridge.fd.indices)
      ρ0 [parameter] ∧
    fxZW P ∈ frame P (base P) PendAWBridge.fd [] (key [parameter]) := by
  have hFamily : ∀ vs, Equiv (base P PendAWBridge.fd.fref vs)
      (ofFrame P (base P) PendAWBridge.fd
        (frame P (base P) PendAWBridge.fd) vs) := by
    intro vs
    have h := NormPendAW.family_value P vs
    rw [NormPendAW.normalized_descriptor] at h
    exact h
  exact NormDataIotaCases.application_mem P (base P) PendAWBridge.fd
    (frame P (base P) PendAWBridge.fd) 0 (RawWFrame.raw_admissible P (base P))
    PendAWLim.Typed.bounded hFamily σ [parameter] (fxZW P) rfl
    (NormPendAW.installed_height_omega P)

/-- The complete result key and actual model are retained by the newly
composed original-case wrapper, including the height-omega constructor. -/
theorem omega_original_cases (P : Premises4) :
    ∃ (j : Fin PendAW.pNode.a.constructors.length) (xs : List PSet.{4}),
      TelFits (mkM P (base P)) σ PendAW.pNode.a.family.parameters ρ0 [parameter] ∧
      TelFits (mkM P (base P)) σ (PendAW.pNode.a.constructorViews j).fields
        (push [parameter] ρ0) xs ∧
      key [parameter] = key ([parameter] ++ (PendAW.pNode.a.constructorViews j).resultIndices.map
        (den (mkM P (base P)) σ (push xs (push [parameter] ρ0)))) ∧
      Equiv (fxZW P) (dataVal j.val xs) := by
  let C := (RawDataRecAttack.context P).withModel (mkM P (base P))
  have hFamily : ∀ vs, Equiv (base P C.node.a.family.ref vs)
      (ofFrame P (base P) (famDataOf C.node.a)
        (frame P (base P) (EvalPlanNormal.fd (EvalPlan.ofNode C.node))) vs) := by
    change ∀ vs, Equiv (base P 4 vs)
      (ofFrame P (base P) PendAWBridge.fd
        (frame P (base P) (EvalPlanNormal.fd NormDataRecAttack.plan)) vs)
    rw [NormDataRecAttack.normalized_descriptor]
    intro vs
    have h := NormPendAW.family_value P vs
    rw [NormPendAW.normalized_descriptor] at h
    exact h
  exact NormDataIotaCases.original_cases_at P (base P) RawDataRecAttack.K C rfl
    PendAW.fam [(5, PendAW.leaf), (6, PendAW.node)] natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT
    (PendAWGroup.boundG _) (PendAWGroup.boundDG 1)
    NormDataRecAttack.matching_parameters (NormNatInvariant.gInv P _)
    (NormRole.envCtx PendAWGroup.wft) (EvalRole.envPlan PendAWGroup.wft)
    NormDataRecAttack.predecessor_context NormDataRecAttack.predecessor_plans
    (NormDataRecAttack.predecessor_faithful P) hFamily (NormDataRecAttack.small_closed P)
    (fun _ h => (List.not_mem_nil _ h).elim) (by change 1 ≠ 0; decide)
    (key [parameter]) (fxZW P) rfl (NormDataRecAttack.omega_mem P)

def Witness (P : Premises4) : Prop :=
  NormDataIotaRowAttack.Witness P ∧
  (∀ k, RecPkg P (base P) (fun _ => k) PendAW.eAll 7 PendAW.recMem) ∧
  (TelFits (mkM P (base P)) σ (PendAWBridge.fd.params ++ PendAWBridge.fd.indices)
      ρ0 [parameter] ∧
    fxZW P ∈ frame P (base P) PendAWBridge.fd [] (key [parameter])) ∧
  (∃ (j : Fin PendAW.pNode.a.constructors.length) (xs : List PSet.{4}),
    TelFits (mkM P (base P)) σ PendAW.pNode.a.family.parameters ρ0 [parameter] ∧
    TelFits (mkM P (base P)) σ (PendAW.pNode.a.constructorViews j).fields
      (push [parameter] ρ0) xs ∧
    key [parameter] = key ([parameter] ++ (PendAW.pNode.a.constructorViews j).resultIndices.map
      (den (mkM P (base P)) σ (push xs (push [parameter] ρ0)))) ∧
    Equiv (fxZW P) (dataVal j.val xs))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormDataIotaRowAttack.component_witness P, rec_pkg P,
    omega_decoded P, omega_original_cases P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormDataRecPkgAttack
