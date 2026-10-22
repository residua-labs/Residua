import rcic.RcicAnnLR3TypedPER

/-!
# An admitted Eq context with no truth-valued unit realisation

The two indices are actual, closed proposition-valued source terms in the
accepted Eq environment. Their existing compositional images are separated
by a Pi-payload observation. The proof carrier of their equality is empty.
This is NOT a source conversion counterexample or a refutation of PER
soundness on realisable contexts. It rules out supplying all-context
realisation as the missing step to the unconditional sort-row consumers.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.UnitContextBoundary
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER

abbrev apartProp : ExprA := EqLargeFixture.eqAt EqLargeFixture.parameter EqLargeFixture.domain
abbrev apartContext : LCtxA := [.assumption apartProp]

def apartProp_typed {Γ : LCtxA}
    (hΓ : CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 Γ) :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 Γ apartProp (.sort .zero) :=
  EqLargeFixture.eqTyped hΓ EqLargeFixture.parameterTyped
    (EqLargeFixture.eqTyped hΓ EqLargeFixture.parameterTyped EqLargeFixture.parameterTyped)

def apartContext_wf :
    CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 apartContext :=
  .assumption .nil (apartProp_typed .nil)

def apartMajor_typed :
    HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 apartContext (.bvar 0) apartProp :=
  .bvar apartContext 0 apartProp .zero rfl (apartProp_typed apartContext_wf)

def piPayloadProbe : CptI := .spine 10 [.spine (levelRef (some 0)) [], .pi .bot []]

theorem parameter_has_pi_payload (ν : Valuation) (ρ : EnvI) :
    UnitModel.denote ν ρ EqLargeFixture.parameter piPayloadProbe := by
  change ApproxI ρ (foldApps (.const 10 []) [levelTerm (some 0),
    .pi (sortTerm (some 0)) (.bvar 0)])
    (.spine 10 [.spine (levelRef (some 0)) [], .pi .bot []])
  apply approxI_famApp 10 []
  refine .cons (.const ρ _ []) (.cons ?_ .nil)
  exact .pi (.bot _ _) (fun s hs => (List.not_mem_nil s hs).elim)

theorem domain_lacks_pi_payload (ν : Valuation) (ρ : EnvI) :
    ¬ UnitModel.denote ν ρ EqLargeFixture.domain piPayloadProbe := by
  intro h
  have ht := (fixture_domain_code ν ρ piPayloadProbe).mp h
  rcases approxI_foldApps_const_inv (r := 10) (ls := [])
      (xs := [levelTerm (some 0),
        .app (.app (.app (.const 12 []) (translate ν (.sort .zero)))
          (translate ν EqLargeFixture.parameter)) (translate ν EqLargeFixture.parameter)]) ht
      with hz | ⟨us, he, hu⟩
  · cases hz
  · cases hu with
    | cons htag hs =>
      cases hs with
      | cons hpay hs =>
        cases hs
        have heargs := (CptI.spine.inj he).2
        have epay := (List.cons.inj (List.cons.inj heargs).2).1
        have hpi := epay.symm ▸ hpay
        rcases approxI_foldApps_const_inv (r := 12) (ls := [])
          (xs := [translate ν (.sort .zero), translate ν EqLargeFixture.parameter,
            translate ν EqLargeFixture.parameter]) hpi with hb | ⟨vs, heq, hv⟩
        · cases hb
        · cases heq

theorem parameter_domain_separated (ν : Valuation) (ρ : EnvI) :
    ¬ ValueEq (UnitModel.denote ν ρ EqLargeFixture.parameter) (UnitModel.denote ν ρ EqLargeFixture.domain) :=
  fun h => domain_lacks_pi_payload ν ρ
    ((h piPayloadProbe).mp (parameter_has_pi_payload ν ρ))

/-- Both endpoints are legal members of the same exact Prop universe PER. -/
theorem endpoints_in_prop_universe (ν : Valuation) (ρ : EnvI) :
    Member (SortPER (some 0)) (UnitModel.denote ν ρ EqLargeFixture.parameter) ∧
    Member (SortPER (some 0)) (UnitModel.denote ν ρ EqLargeFixture.domain) :=
  ⟨⟨fixture_parameter_member ν ρ, fixture_parameter_defined ν ρ, ValueEq.refl _⟩,
    ⟨(fixture_domain_member ν ρ).1, (fixture_domain_member ν ρ).2, ValueEq.refl _⟩⟩

def ApartRealises (ν : Valuation) (ρ : EnvI) : Prop :=
  Member (EqPER (SortPER (some 0))
    (UnitModel.denote ν ρ EqLargeFixture.parameter) (UnitModel.denote ν ρ EqLargeFixture.domain)) (ρ 0)

theorem apartContext_no_realization (ν : Valuation) : ¬ ∃ ρ, ApartRealises ν ρ := by
  rintro ⟨ρ, hρ⟩
  exact parameter_domain_separated ν ρ hρ.1.2.2

/-- The literal fitting predicate of the accepted Eq probe fails as well;
this is not an artifact of the new exact-universe PER wrapper. -/
theorem no_eq_proof_member (ν : Valuation) (ρ : EnvI) (p : Value) :
    ¬ EqProofMember ρ (translate ν EqLargeFixture.parameter)
      (translate ν EqLargeFixture.domain) p :=
  fun h => parameter_domain_separated ν ρ h.1

/-- Over this context, every realised-context conclusion is vacuous. -/
theorem realised_conclusion_vacuous (ν : Valuation) (Q : EnvI → Prop) :
    ∀ ρ, ApartRealises ν ρ → Q ρ :=
  fun ρ hρ => False.elim (apartContext_no_realization ν ⟨ρ, hρ⟩)

/-- No extraction may silently select a realisation for every well-formed
context; this particular required selection already cannot exist. -/
theorem no_apart_representative :
    ¬ ∃ choose : Valuation → EnvI, ∀ ν, ApartRealises ν (choose ν) := by
  rintro ⟨choose, hc⟩
  exact apartContext_no_realization (fun _ => none) ⟨choose _, hc _⟩

theorem inhabited_empty_context_boundary :
    Nonempty (EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) ∧
    Nonempty (CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 apartContext) ∧
    Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 [] apartProp (.sort .zero)) ∧
    Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 apartContext (.bvar 0) apartProp) ∧
    Nonempty (HasTyA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 apartContext
      (.sort .zero) (.sort EqLargeFixture.one)) ∧
    (∀ ν ρ, Member (SortPER (some 0)) (UnitModel.denote ν ρ EqLargeFixture.parameter) ∧
      Member (SortPER (some 0)) (UnitModel.denote ν ρ EqLargeFixture.domain)) ∧
    (∀ ν, ¬ ∃ ρ, ApartRealises ν ρ) :=
  ⟨EqLargeFixture.wf, ⟨apartContext_wf⟩, ⟨apartProp_typed .nil⟩,
    ⟨apartMajor_typed⟩, ⟨.sort apartContext .zero⟩,
    endpoints_in_prop_universe, apartContext_no_realization⟩
end Rcic.Declarative.Ann.LR3.UnitContextBoundary
