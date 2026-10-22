import rcic.RcicAnnLR3UnitArms
import rcic.RcicAnnLR3UnitConstructorArms

/-!
# Actual semantic membership at the Eq fixture's motive

Besides equality of the two requested endpoints, the call and the minor
inhabit the exact universe denoted by the fixture's motive. This is a
positive, concrete membership supply, not a global `EnvSem` or a theorem
about all source typings in the admitted environment. In particular the
constant motive used by the fixture does not establish dependent transport
for arbitrary motives. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Rcic.Declarative.Ann.LR3.UnitModel
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit

/-- Membership at an interpreted universe value. The carrier is a value,
not a source typing derivation; exact level membership and definedness are
part of this scoped relation. -/
def UniverseElement (ρ : EnvI) (x T : Value) : Prop :=
  ∃ i : Option Nat, ValueEq T (denI ρ (sortTerm i)) ∧ SortMember i x ∧ TypeDefined x

/-- The fixture's motive really denotes Sort 1, for arbitrary actual
endpoint and proof terms. Its two beta reductions are model equations. -/
theorem fixture_motive_value (ν : Valuation) (ρ : EnvI) (b p : ExprA) :
    InterpretedEq ν ρ (EqLargeFixture.motiveAt b p) (.sort EqLargeFixture.one) := by
  apply eq_of_betaRun (k := 4)
  rfl

/-- Both the open major and the constructor proof inhabit the same actual
singleton equality carrier, with its endpoint agreement supplied. -/
theorem fixture_proofs_member {ν : Valuation} {ρ : EnvI} (hρ : FitsFixture ν ρ) :
    EqProofMember ρ (translate ν EqLargeFixture.parameter) (translate ν EqLargeFixture.parameter)
      (denote ν ρ (.bvar 0)) ∧
    EqProofMember ρ (translate ν EqLargeFixture.parameter) (translate ν EqLargeFixture.parameter)
      (denote ν ρ (EqLargeFixture.reflAt EqLargeFixture.parameter)) :=
  ⟨⟨SemEqI.refl ρ _, major_unit hρ⟩, ⟨SemEqI.refl ρ _, refl_unit ν ρ⟩⟩

theorem fixture_minor_at_source_motive (ν : Valuation) (ρ : EnvI) (b p : ExprA) :
    UniverseElement ρ (denote ν ρ EqLargeFixture.result)
      (denote ν ρ (EqLargeFixture.motiveAt b p)) :=
  ⟨some 1, fixture_motive_value ν ρ b p, fixture_result_member ν ρ,
    fixture_result_defined ν ρ⟩

theorem fixture_open_at_motive {ν : Valuation} {ρ : EnvI} (hρ : FitsFixture ν ρ) :
    UniverseElement ρ (denote ν ρ (EqLargeFixture.call (.bvar 0)))
      (denote ν ρ (EqLargeFixture.motiveAt EqLargeFixture.parameter (.bvar 0))) :=
  ⟨some 1, fixture_motive_value ν ρ _ _, (fixture_open_member hρ).1,
    (fixture_open_member hρ).2⟩

theorem fixture_closed_at_motive (ν : Valuation) (ρ : EnvI) :
    UniverseElement ρ (denote ν ρ StrictProofModelBoundary.canonicalCallA3)
      (denote ν ρ (EqLargeFixture.motiveAt EqLargeFixture.parameter
        StrictProofModelBoundary.canonicalMajorA3)) :=
  ⟨some 1, fixture_motive_value ν ρ _ _, (fixture_closed_member ν ρ).1,
    (fixture_closed_member ν ρ).2⟩

/-- The value-level typed positive test, uniformly over every partial level
valuation. Admission and the exact source conversions are supplied by
`inhabited_unit_probe`; all semantic premises here are independently built. -/
theorem inhabited_typed_unit_probe (ν : Valuation) :
    FitsFixture ν fixtureEnv ∧
    SortMember (some 0) (denote ν fixtureEnv EqLargeFixture.domain) ∧
    TypeDefined (denote ν fixtureEnv EqLargeFixture.domain) ∧
    EqProofMember fixtureEnv (translate ν EqLargeFixture.parameter) (translate ν EqLargeFixture.parameter)
      (denote ν fixtureEnv (.bvar 0)) ∧
    InterpretedEq ν fixtureEnv (EqLargeFixture.call (.bvar 0)) EqLargeFixture.result ∧
    UniverseElement fixtureEnv (denote ν fixtureEnv (EqLargeFixture.call (.bvar 0)))
      (denote ν fixtureEnv (EqLargeFixture.motiveAt EqLargeFixture.parameter (.bvar 0))) ∧
    UniverseElement fixtureEnv (denote ν fixtureEnv EqLargeFixture.result)
      (denote ν fixtureEnv (EqLargeFixture.motiveAt EqLargeFixture.parameter (.bvar 0))) ∧
    InterpretedEq ν EnvI.bot StrictProofModelBoundary.canonicalCallA3 EqLargeFixture.result ∧
    UniverseElement EnvI.bot (denote ν EnvI.bot StrictProofModelBoundary.canonicalCallA3)
      (denote ν EnvI.bot (EqLargeFixture.motiveAt EqLargeFixture.parameter
        StrictProofModelBoundary.canonicalMajorA3)) :=
  ⟨fixtureEnv_fits ν, (fixture_domain_member ν fixtureEnv).1,
    (fixture_domain_member ν fixtureEnv).2,
    (fixture_proofs_member (fixtureEnv_fits ν)).1,
    open_conversion_sound (fixtureEnv_fits ν), fixture_open_at_motive (fixtureEnv_fits ν),
    fixture_minor_at_source_motive ν fixtureEnv _ _, canonical_iota_sound ν EnvI.bot,
    fixture_closed_at_motive ν EnvI.bot⟩

end Rcic.Declarative.Ann.LR3.UnitModel
