import rcic.RcicAnnLR3SemanticMemberReadback
import rcic.RcicAnnLR3SaturatedAliasControl
import rcic.RcicAnnLR3SaturatedTower

/-!
# The admitted alias fixture now has its exact const arm

The actual stored-type interpretation supplies both evaluator equations.
The exact source contract is then instantiated on the existing SortPER
control attachment. The same native member value also has an explicit
retained code in the new saturated universe zero.

This is a complete Ty_const control for this admitted two-member source
environment. It is not the general enriched-model Ty_const or a transfer
of the eleven legacy suppliers. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.SemanticMemberControl
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open SemanticMemberReadback.Alias

def equations : SaturatedAliasControl.Equations configuredView configuredHook :=
  ⟨alias_image, member_image⟩

def model : AnnSemantics := SaturatedAliasControl.model configuredView configuredHook

theorem configured_ty_const (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_const model ConfiguredAliasBoundary.env I n :=
  SaturatedAliasControl.ty_const_of_equations equations I n

theorem alias_type_ih (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    PairedTyGoal model ConfiguredAliasBoundary.env I n Γ
      (.const 94 []) (.sort ConfiguredAliasBoundary.one) :=
  SaturatedAliasControl.alias_type_goal equations I n Γ

theorem member_goal (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    PairedTyGoal model ConfiguredAliasBoundary.env I n Γ (.const 95 []) (.const 94 []) :=
  SaturatedAliasControl.member_goal equations I n Γ

theorem retained_member (ν : Valuation) (ρ : EnvI) :
    SaturatedTower.UniverseRel 0 (SaturatedTower.reflect 1 95)
      (SaturatedTower.reflect 1 95) ∧
    ValueEq (image ν ρ (.const 95 []))
      (StratifiedCandidates.erase 1 (SaturatedTower.reflect 1 95)) :=
  ⟨(SaturatedTower.universeBase 0).point_member 95, member_image ν ρ⟩

/-- All original source premises and the repaired exact rule supply are
inhabited. No caller-provided reflected membership appears in this control. -/
theorem positive_alias_control :
    Nonempty (EnvWfA (iotaIfaceA ConfiguredAliasBoundary.env) ConfiguredAliasBoundary.env) ∧
    Nonempty (CtxWfA ConfiguredAliasBoundary.env (iotaIfaceA ConfiguredAliasBoundary.env) 0 []) ∧
    Nonempty (HasTyA ConfiguredAliasBoundary.env (iotaIfaceA ConfiguredAliasBoundary.env)
      0 [] (.const 94 []) (.sort ConfiguredAliasBoundary.one)) ∧
    PairedTyGoal model ConfiguredAliasBoundary.env (iotaIfaceA ConfiguredAliasBoundary.env)
      0 [] (.const 94 []) (.sort ConfiguredAliasBoundary.one) ∧
    PairedArms.Ty_const model ConfiguredAliasBoundary.env
      (iotaIfaceA ConfiguredAliasBoundary.env) 0 ∧
    PairedTyGoal model ConfiguredAliasBoundary.env (iotaIfaceA ConfiguredAliasBoundary.env)
      0 [] (.const 95 []) (.const 94 []) :=
  ⟨⟨ConfiguredAliasBoundary.admitted⟩, ⟨.nil⟩,
    ⟨ConfiguredAliasBoundary.source_alias_type []⟩, alias_type_ih _ _ [],
    configured_ty_const _ _, member_goal _ _ []⟩

end Rcic.Declarative.Ann.LR3.SemanticMemberControl
