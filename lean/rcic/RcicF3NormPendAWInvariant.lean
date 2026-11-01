import rcic.RcicF3NormPendAWGroup
import rcic.RcicF3NormNatInvariant

/-!
# A full new invariant at the exact formerly refuting W fixture

The normalized Nat predecessor invariant is produced, as are this W
group's exact small closed data frame, original stored constructors and
complete recursor package. Their composition gives the new canonical
invariant and actual installed-table soundness for every bound function.

The exact height-omega element is in that sound table's family. This is
a full fixture certificate for the repaired interpretation, not universal
StepAG, checked W/D apex composition, or universal shape-schema iota.
The old finite-stage invariant and its literal refutation remain separate.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPendAWInvariant
open Rcic.Declarative Rcic.Model.PS

/-- The actual fixture needs no relation between constructor and recursor
bounds: its produced at-table composition consumes only BoundG. -/
theorem gInv (P : Premises4) (K : Nat → Nat) :
    NormRole.GInv P K PendAWGroup.wft := by
  intro ctx hctx plans hplans μ hF
  have hsubE : ∀ r m, natEnvU.members r = some m → PendAW.eAll.members r = some m :=
    groupMembersT_preserve PendAW.membersT
  have hctxE : ∀ r, Dom natEnvU r → ctx r = NormRole.envCtx natEnvUWfT r := by
    intro r hr
    exact (hctx r (dom_groupMembersT PendAW.membersT hr)).trans
      (NormRole.envCtx_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl
        PendAW.membersT r hr)
  have hplansE : ∀ r, Dom natEnvU r → plans r = EvalRole.envPlan natEnvUWfT r := by
    intro r hr
    exact (hplans r (dom_groupMembersT PendAW.membersT hr)).trans
      (EvalRole.envPlan_group_stable natEnvUWfT rfl PendAWGroup.ctorClasses rfl
        PendAW.membersT r hr)
  have hFE : EvalRole.Faithful RawFamily.role P μ ctx plans natEnvU :=
    fun r m hm => hF r m (hsubE r m hm)
  have hPrior := NormNatInvariant.gInv P K ctx hctxE plans hplansE μ hFE
  exact NormPendAWGroup.at_table P K μ PendAWGroup.walkAgree (PendAWGroup.boundG K)
    (NormPendAWRecPkg.values P μ ctx plans hctx hplans hF) hPrior.1
    (fun Efin hsub => hPrior.2 Efin (fun r m hm => hsub r m (hsubE r m hm)))

/-- Actual soundness and stable literal iota at the canonical new table. -/
theorem actual_invariant (P : Premises4) (K : Nat → Nat) :
    AllSound P (NormPendAW.table P) K PendAW.eAll ∧
      ∀ Efin, (∀ r m, PendAW.eAll.members r = some m → Efin.members r = some m) →
        ∀ r m, PendAW.eAll.members r = some m → m.mclass = .recursorM →
          IotaAt P (NormPendAW.table P) K Efin r :=
  gInv P K (NormRole.envCtx PendAWGroup.wft) (fun _ _ => rfl)
    (EvalRole.envPlan PendAWGroup.wft) (fun _ _ => rfl) (NormPendAW.table P)
    (NormPendAW.faithful P)

/-- A genuine repaired invariant at the same admitted environment whose
literal finite-stage invariant is refuted. -/
theorem invariant_nonrefutable (P : Premises4) (K : Nat → Nat) :
    ¬ (NormRole.GInv P K PendAWGroup.wft → (Premises4 → False)) :=
  fun h => h (gInv P K) P

def Witness (P : Premises4) : Prop :=
  NormNatInvariant.Witness P ∧
  NormPendAWGroup.Witness P ∧
  (∀ K, NormRole.GInv P K PendAWGroup.wft) ∧
  (∀ K, AllSound P (NormPendAW.table P) K PendAW.eAll ∧
    ∀ Efin, (∀ r m, PendAW.eAll.members r = some m → Efin.members r = some m) →
      ∀ r m, PendAW.eAll.members r = some m → m.mclass = .recursorM →
        IotaAt P (NormPendAW.table P) K Efin r) ∧
  (∀ K, RecPkg P (NormPendAW.table P) K PendAW.eAll 7 PendAW.recMem) ∧
  fxZW P ∈ Ed (mkM P (NormPendAW.table P))
    (fapps (NormPendAW.table P 4 []) [tyv fxS])

theorem component_witness (P : Premises4) : Witness P :=
  ⟨NormNatInvariant.component_witness P, NormPendAWGroup.component_witness P,
    gInv P, actual_invariant P, NormPendAWRecPkg.actual_rec_pkg P,
    NormPendAW.installed_height_omega P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.NormPendAWInvariant
