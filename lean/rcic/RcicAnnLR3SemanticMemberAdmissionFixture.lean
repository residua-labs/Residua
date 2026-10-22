import rcic.RcicAnnLR3SemanticMemberAdmissionDelta
import rcic.RcicAnnLR3SaturatedAliasControl

/-!
# Exact fixture Ty_const supplied by admission-tree readback

The new reader supplies both actual evaluator equations. The exact
existing arm proof is composed through ty_const_of_equations. This
is the admitted two-member fixture, not a new general source arm.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.AdmissionUniverseFixture
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements AdmissionUniverseReadback

abbrev configuredView := SemanticMemberEval.view ConfiguredAliasBoundary.env
abbrev configuredHook {I : IotaIfaceA}
    (hE : EnvWfA I ConfiguredAliasBoundary.env) :=
  hook hE EnvironmentEval.neutralFamilySyntax

theorem stored_read {I : IotaIfaceA}
    (hE : EnvWfA I ConfiguredAliasBoundary.env) (ν : Valuation) :
    readAdmitted hE ν (.const 94 []) = some (some 0) := by
  calc
    readAdmitted hE ν (.const 94 []) = readAdmitted hE ν (.sort .zero) :=
      readAdmitted_delta hE ν (by rfl)
    _ = some (some 0) := readAdmitted_sort hE ν .zero

theorem equations {I : IotaIfaceA}
    (hE : EnvWfA I ConfiguredAliasBoundary.env) :
    SaturatedAliasControl.Equations configuredView (configuredHook hE) where
  alias_image := fun ν ρ =>
    stored_type_image hE EnvironmentEval.neutralFamilySyntax ν ρ
      (.const 94 []) (some 0) (stored_read hE ν)
  member_image := fun ν ρ =>
    axiom_image hE (r := 95) (ls := []) (m := ConfiguredAliasBoundary.member)
      rfl rfl EnvironmentEval.neutralFamilySyntax ν ρ (some 0) (stored_read hE ν)

theorem ty_const_of_admission (I : IotaIfaceA)
    (hE : EnvWfA I ConfiguredAliasBoundary.env) (n : Nat) :
    PairedArms.Ty_const
      (SaturatedAliasControl.model configuredView (configuredHook hE))
      ConfiguredAliasBoundary.env I n :=
  SaturatedAliasControl.ty_const_of_equations (equations hE) I n

theorem configured_ty_const (n : Nat) :
    PairedArms.Ty_const
      (SaturatedAliasControl.model configuredView
        (configuredHook ConfiguredAliasBoundary.admitted))
      ConfiguredAliasBoundary.env (iotaIfaceA ConfiguredAliasBoundary.env) n :=
  ty_const_of_admission _ ConfiguredAliasBoundary.admitted n

end Rcic.Declarative.Ann.LR3.AdmissionUniverseFixture
