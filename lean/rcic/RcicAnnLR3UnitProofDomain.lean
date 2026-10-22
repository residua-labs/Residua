import rcic.RcicAnnLR3UnitTypedEq

/-!
# The next irrelevance obligation is typed PER lifting, not raw equality

The requested Eq-major and closed-iota tests are positive. This file checks
what happens when the same raw applicative carrier is used at a proposition
function. Identity and the constant reflexivity function have an actual
closed `ConvA.irr` derivation. They agree on every semantically admitted
unit argument, but their unrestricted target observation sets differ: the
separator demands a raw sort from a proof argument. That demand does not
belong to the Eq proof carrier.

This refutes extending `InterpretedEq` unchanged to every source `irr` arm.
It does NOT refute the unit/PER candidate: restricted proof-domain action is
supplied positively, and a full type-indexed PER interpretation is a separate
construction. The raw map is kept as the scoped test interpreter, not
advertised as a full model. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Rcic.Declarative.Ann.LR3.UnitModel
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit

abbrev proofArrow : ExprA := .pi EqLargeFixture.domain .zero EqLargeFixture.domain .zero
abbrev proofId : ExprA := .lam EqLargeFixture.domain .zero (.bvar 0)
abbrev proofConst : ExprA := .lam EqLargeFixture.domain .zero
  (EqLargeFixture.reflAt EqLargeFixture.parameter)

def proofArrowTyped : HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 []
    proofArrow (.sort .zero) :=
  hasTyA_sortEqN
    (.pi [] EqLargeFixture.domain .zero EqLargeFixture.domain .zero
      (EqLargeFixture.eqTyped .nil EqLargeFixture.parameterTyped EqLargeFixture.parameterTyped)
      (EqLargeFixture.eqTyped EqLargeFixture.contextWf EqLargeFixture.parameterTyped EqLargeFixture.parameterTyped))
    (fun _ => rfl)

def proofIdTyped : HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 [] proofId proofArrow :=
  .lam [] EqLargeFixture.domain .zero (.bvar 0) EqLargeFixture.domain .zero
    (EqLargeFixture.eqTyped .nil EqLargeFixture.parameterTyped EqLargeFixture.parameterTyped)
    (EqLargeFixture.eqTyped EqLargeFixture.contextWf EqLargeFixture.parameterTyped EqLargeFixture.parameterTyped)
    EqLargeFixture.majorTyped

def proofConstTyped : HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 [] proofConst proofArrow :=
  .lam [] EqLargeFixture.domain .zero (EqLargeFixture.reflAt EqLargeFixture.parameter)
    EqLargeFixture.domain .zero
    (EqLargeFixture.eqTyped .nil EqLargeFixture.parameterTyped EqLargeFixture.parameterTyped)
    (EqLargeFixture.eqTyped EqLargeFixture.contextWf EqLargeFixture.parameterTyped EqLargeFixture.parameterTyped)
    (EqLargeFixture.reflTyped EqLargeFixture.contextWf EqLargeFixture.parameterTyped)

def proofArrowIrr : ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 []
    proofId proofConst proofArrow :=
  .irr [] proofArrow proofId proofConst proofArrowTyped proofIdTyped proofConstTyped

/-- This raw demand is not an observation of the semantic proof unit. -/
theorem unit_lacks_sort (ρ : EnvI) : ¬ unitValue ρ .sort := by
  intro h
  rcases approxI_lam_inv h with he | ⟨g, he, _⟩ <;> cases he

def proofFunctionProbe : CptI := .lam [([.sort], .sort)]

theorem proofId_observed (ν : Valuation) (ρ : EnvI) : denote ν ρ proofId proofFunctionProbe := by
  apply ApproxI.lam
  intro s hs
  obtain rfl := List.mem_singleton.mp hs
  exact .bvar (List.mem_singleton.mpr rfl)

theorem proofConst_not_observed (ν : Valuation) (ρ : EnvI) :
    ¬ denote ν ρ proofConst proofFunctionProbe := by
  intro h
  rcases approxI_lam_inv h with he | ⟨g, he, hg⟩
  · cases he
  · have heq : [([.sort], .sort)] = g := CptI.lam.inj he
    subst g
    have hb := hg ([.sort], .sort) (List.mem_singleton.mpr rfl)
    exact unit_lacks_sort (EnvI.cons (demand [.sort]) ρ)
      ((refl_unit ν (EnvI.cons (demand [.sort]) ρ) .sort).mp hb)

theorem proofArrow_not_raw_equal (ν : Valuation) (ρ : EnvI) :
    ¬ InterpretedEq ν ρ proofId proofConst :=
  fun h => proofConst_not_observed ν ρ ((h proofFunctionProbe).mp (proofId_observed ν ρ))

/-- Positive action on every admitted semantic proof argument. The
unrestricted graph counterexample uses an argument outside this domain. -/
theorem proofArrow_equal_on_units {ν : Valuation} {ρ : EnvI} (p : ExprA)
    (hp : ProofMember ρ (denote ν ρ p)) :
    InterpretedEq ν ρ (.app proofId p) (.app proofConst p) := by
  have hi : InterpretedEq ν ρ (.app proofId p) p :=
    beta_sound ν ρ EqLargeFixture.domain (.bvar 0) p .zero
  have hc : InterpretedEq ν ρ (.app proofConst p) (EqLargeFixture.reflAt EqLargeFixture.parameter) :=
    beta_sound ν ρ EqLargeFixture.domain (EqLargeFixture.reflAt EqLargeFixture.parameter) p .zero
  exact ValueEq.trans hi (ValueEq.trans (ValueEq.trans hp (ValueEq.symm (refl_unit ν ρ))) (ValueEq.symm hc))

/-- All source premises for the extra irr test, and both the negative raw
and positive restricted-action conclusions, are supplied together. -/
theorem inhabited_proof_domain_test :
    Nonempty (EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) ∧
    Nonempty (CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 []) ∧
    Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 [] proofArrow (.sort .zero)) ∧
    Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 [] proofId proofArrow) ∧
    Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 [] proofConst proofArrow) ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 [] proofId proofConst proofArrow) ∧
    ∀ (ν : Valuation) (ρ : EnvI),
      ¬ InterpretedEq ν ρ proofId proofConst ∧
      (∀ p : ExprA, ProofMember ρ (denote ν ρ p) →
        InterpretedEq ν ρ (.app proofId p) (.app proofConst p)) :=
  ⟨EqLargeFixture.wf, ⟨.nil⟩, ⟨proofArrowTyped⟩, ⟨proofIdTyped⟩, ⟨proofConstTyped⟩,
    ⟨proofArrowIrr⟩, fun ν ρ => ⟨proofArrow_not_raw_equal ν ρ, proofArrow_equal_on_units⟩⟩

end Rcic.Declarative.Ann.LR3.UnitModel
