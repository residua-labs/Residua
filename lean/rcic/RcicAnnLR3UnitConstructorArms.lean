import rcic.RcicAnnLR3UnitLevels
import rcic.RcicAnnKEqPositive

/-!
# First unit-model constructor arms and actual source nodes

Beta is supplied for the full syntactic translation. Irrelevance is the
singleton PER law, with the actual fixture proof memberships supplied.
Eq iota and derived K have actual source nodes and interpreted endpoints.
The generic J membership lemma reads the motive at the actual endpoint;
it uses semantic endpoint equality, never source Pi injectivity or synthesis.

This does not assert that every source proof lies in the singleton PER or
that all source recursors have their stored telescope interpretation. Those
are global typing-soundness obligations, not hidden assumptions of the probe.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.UnitModel

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit

/-- Membership at an interpreted universe term, not merely an index chosen
by the caller. Definedness is recorded separately from membership. -/
def AtUniverseTerm (ρ : EnvI) (e T : Expr Nat) : Prop :=
  ∃ i, SemEqI ρ T (sortTerm i) ∧ SortMember i (denI ρ e) ∧ TypeDefined (denI ρ e)

theorem atUniverseTerm_transport {ρ : EnvI} {e e' T T' : Expr Nat}
    (he : SemEqI ρ e e') (hT : SemEqI ρ T T') (h : AtUniverseTerm ρ e T) :
    AtUniverseTerm ρ e' T' := by
  obtain ⟨i, hTi, hm, hd⟩ := h
  exact ⟨i, SemEqI.trans (SemEqI.symm hT) hTi,
    sortMember_congr he hm, typeDefined_congr he hd⟩

/-- Semantic endpoint equality transports the motive. It is a semantic
congruence theorem and does not reflect equality back into source syntax. -/
theorem motive_endpoint_transport {ρ : EnvI} (C a b p : Expr Nat)
    (hab : SemEqI ρ a b) (hp : SemEqI ρ p unitTerm) :
    SemEqI ρ (.app (.app C a) unitTerm) (.app (.app C b) p) :=
  semEqI_app (semEqI_app (SemEqI.refl ρ C) hab) (SemEqI.symm hp)

/-- J's generic scoped typing law: the minor is read at the motive's actual
value. This law is supplied from the concrete unit operation. -/
theorem j_motive_membership {ρ : EnvI} (C c a b p : Expr Nat)
    (hab : SemEqI ρ a b) (hp : SemEqI ρ p unitTerm)
    (hc : AtUniverseTerm ρ c (.app (.app C a) unitTerm)) :
    AtUniverseTerm ρ (jOperation C c b p) (.app (.app C b) p) :=
  atUniverseTerm_transport (SemEqI.symm (jOperation_unit C c b p hp))
    (motive_endpoint_transport C a b p hab hp) hc

/-- At refl, both the computation and motive-sensitive membership are
supplied. No bottom-proof or source-row hypothesis appears. -/
theorem j_iota_arm (ρ : EnvI) (C c a : Expr Nat)
    (hc : AtUniverseTerm ρ c (.app (.app C a) unitTerm)) :
    SemEqI ρ (jOperation C c a unitTerm) c ∧
    AtUniverseTerm ρ (jOperation C c a unitTerm) (.app (.app C a) unitTerm) :=
  ⟨jOperation_unit C c a unitTerm (SemEqI.refl ρ unitTerm),
    j_motive_membership C c a a unitTerm (SemEqI.refl ρ a) (SemEqI.refl ρ unitTerm) hc⟩

/-- The fixture supplies the generic J lemma's actual motive/minor premise. -/
theorem fixture_minor_at_motive (ν : Valuation) (ρ : EnvI) :
    AtUniverseTerm ρ (translate ν EqLargeFixture.result)
      (.app (.app (translate ν EqLargeFixture.motive)
        (translate ν EqLargeFixture.parameter)) unitTerm) :=
  ⟨some 1, fixture_motive_sound ν ρ, fixture_result_member ν ρ, fixture_result_defined ν ρ⟩

/-- A source `irr` arm consumes membership supplies for its two proofs.
The rule below is constructive and the fixture discharges both inputs. -/
theorem irr_arm {ν : Valuation} {ρ : EnvI} {p q : ExprA}
    (hp : ProofMember ρ (denote ν ρ p)) (hq : ProofMember ρ (denote ν ρ q)) :
    InterpretedEq ν ρ p q := proofPER_irr hp hq

theorem actual_irr_interpreted :
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 EqLargeFixture.context
      (.bvar 0) (EqLargeFixture.reflAt EqLargeFixture.parameter) EqLargeFixture.domain) ∧
    (∀ (ν : Valuation) (ρ : EnvI), FitsFixture ν ρ →
      InterpretedEq ν ρ (.bvar 0) (EqLargeFixture.reflAt EqLargeFixture.parameter)) :=
  ⟨⟨StrictProofModelBoundary.neutralReflIrrNodeA3⟩, fun _ _ hρ => irr_arm (major_unit hρ) (refl_unit _ _)⟩

theorem actual_beta_interpreted :
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 []
      (.app (.lam (.sort EqLargeFixture.one) EqLargeFixture.two (.bvar 0)) (.sort .zero))
      (.sort .zero) (.sort EqLargeFixture.one)) ∧
    (∀ (ν : Valuation) (ρ : EnvI), InterpretedEq ν ρ
      (.app (.lam (.sort EqLargeFixture.one) EqLargeFixture.two (.bvar 0)) (.sort .zero))
      (.sort .zero)) :=
  ⟨⟨idSort1_beta _ _ _⟩, fun ν ρ => beta_sound ν ρ _ _ _ _⟩

theorem actual_iota_interpreted :
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 []
      StrictProofModelBoundary.canonicalCallA3 EqLargeFixture.result (.sort EqLargeFixture.one)) ∧
    (∀ (ν : Valuation) (ρ : EnvI),
      InterpretedEq ν ρ StrictProofModelBoundary.canonicalCallA3 EqLargeFixture.result) :=
  ⟨StrictProofModelBoundary.canonicalIotaConversionA3, canonical_iota_sound⟩

/-- K is the landed stage-1 head, with its actual frame already supplied.
This theorem does not invent a new ConvA constructor or inspect its guard. -/
theorem actual_K_interpreted :
    KStage.Head EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 EqLargeFixture.context
      (EqLargeFixture.call (.bvar 0)) EqLargeFixture.result KEqPositive.eqShape.resultType ∧
    (∀ (ν : Valuation) (ρ : EnvI), FitsFixture ν ρ →
      InterpretedEq ν ρ (EqLargeFixture.call (.bvar 0)) EqLargeFixture.result) :=
  ⟨KEqPositive.eqHead, fun _ _ hρ => open_conversion_sound hρ⟩

end Rcic.Declarative.Ann.LR3.UnitModel
