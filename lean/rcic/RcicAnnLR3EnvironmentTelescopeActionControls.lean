import rcic.RcicAnnLR3EnvironmentTelescopeAction
import rcic.RcicAnnAccFrecPin

/-!
# Admitted binary type-valued axiom action

The retained action is instantiated by the actual R member of the Acc
environment. Admission, source context well-formedness and source
constant typing are supplied. Its binary application preserves explicit
candidate-bearing result data for every pair of original proposition
codes. This is a concrete member control, not a uniform Ty_const arm.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentTelescopeActionControls

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open StratifiedCandidates EnvironmentTelescopeAction

def accAction (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    BinaryAction (Code 0) (fun C => (view 0 C).value) (CodeRelated 0)
      (Code 0) (fun C => (view 0 C).value) (CodeRelated 0) 0 :=
  propositionAction (E := pinAccGroupEnvA) (r := 9) (m := pinAccRelA) rfl rfl F ν ρ

def acc_typed (Γ : LCtxA) :
    HasTyA pinAccGroupEnvA noIotaA 0 Γ (.const 9 []) pinAccRelTyA := pinAccRelConstTy rfl

theorem acc_control (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (C D : Code 0) (name : Nat) :
    Nonempty (EnvWfA noIotaA pinAccGroupEnvA) ∧
    Nonempty (CtxWfA pinAccGroupEnvA noIotaA 0 []) ∧
    Nonempty (HasTyA pinAccGroupEnvA noIotaA 0 [] (.const 9 []) pinAccRelTyA) ∧
    BinaryRel (accAction F ν ρ) (accAction F ν ρ) ∧
    ValueEq (NeutralPi.applyValue
      (NeutralPi.applyValue
        (EnvironmentTelescopeInsertion.image pinAccGroupEnvA F ν ρ (.const 9 []))
        (view 0 C).value) (view 0 D).value) (NativeMemberValues.value (some 0) 9) ∧
    (((accAction F ν ρ).run C).run D).code = NativeMemberValues.neutralCode 0 9 ∧
    (view 0 (((accAction F ν ρ).run C).run D).code).relation
      (NeutralPER.neutralAtom name) (NeutralPER.neutralAtom name) :=
  ⟨⟨pinAccGroupWfA noIotaA⟩, ⟨.nil⟩, ⟨acc_typed []⟩, binaryRel_refl _,
    propositionAction_erased (E := pinAccGroupEnvA) (r := 9) (m := pinAccRelA)
      rfl rfl F ν ρ C D, rfl, EnvironmentTelescopeInsertion.proposition_result_neutral 9 name⟩

end Rcic.Declarative.Ann.LR3.EnvironmentTelescopeActionControls
