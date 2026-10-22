import rcic.RcicAnnLR3UnitTranslate
import rcic.RcicAnnLR3StrictProofModelBoundary

/-!
# The two requested actual Eq conversions in the nonbottom-unit interpretation

The scope is exact: the admitted EqLargeFixture environment, its open proof
context, and its closed constructor-major iota call. All source derivations
are imported, not reconstructed with a changed statement. The interpretation
is compositional and independent of those derivations. The only open-context
semantic assumption is the concrete singleton equality carrier for its one
proof variable; an actual fitting environment is supplied.

The unit elimination equation is proved, not a model-record hypothesis.
The J operation may remain strict at bottom, since the proof unit is not
bottom. No general source typing/conversion soundness is claimed here.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Rcic.Declarative.Ann.LR3.UnitModel

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit

/-- Eliminating the nonbottom unit at a semantic type and inhabitant. -/
theorem unit_eliminate (ρ : EnvI) (T c : Expr Nat) :
    SemEqI ρ (.app (.app unitTerm T) c) c := by
  have hfirst : SemEqI ρ (.app unitTerm T) (.lam T (.bvar 0)) :=
    approxI_beta ρ (.sort .zero) (.lam (.bvar 0) (.bvar 0)) T
  exact SemEqI.trans (semEqI_app hfirst (SemEqI.refl ρ c))
    (approxI_beta ρ T (.bvar 0) c)

/-- The motive is read at the actual endpoint and proof. This is the body
of the closed recursor combinator, not a special-case lookup of a call. -/
def jOperation (C c b p : Expr Nat) : Expr Nat :=
  .app (.app p (.app (.app C b) p)) c

theorem jOperation_unit {ρ : EnvI} (C c b p : Expr Nat)
    (hp : SemEqI ρ p unitTerm) : SemEqI ρ (jOperation C c b p) c := by
  have hM := semEqI_app (SemEqI.refl ρ (.app C b)) hp
  have h := semEqI_app (semEqI_app hp hM) (SemEqI.refl ρ c)
  exact SemEqI.trans h (unit_eliminate ρ (.app (.app C b) unitTerm) c)

/-- A bottom-only function remains bottom under application. -/
theorem app_bottom {ρ : EnvI} {p a : Expr Nat}
    (hp : ∀ c, ApproxI ρ p c → c = .bot) :
    ∀ c, ApproxI ρ (.app p a) c → c = .bot := by
  intro c h
  rcases approxI_app_inv h with hb | ⟨g, s, _, hf, _, _⟩ | ⟨r, args, u, _, hf, _⟩
  · exact hb
  · exact CptI.noConfusion (hp (.lam g) hf)
  · exact CptI.noConfusion (hp (.spine r args) hf)

theorem jOperation_bottom {ρ : EnvI} (C c b p : Expr Nat)
    (hp : ∀ k, ApproxI ρ p k → k = .bot) :
    ValueEq (denI ρ (jOperation C c b p)) bottom := by
  intro k
  constructor
  · exact app_bottom (app_bottom hp) k
  · intro hk; subst k; exact .bot _ _

/-- Singleton Eq proof carrier: endpoint agreement and the common unit.
This carrier does not impose cumulative universe memberships. -/
def EqProofMember (ρ : EnvI) (a b : Expr Nat) (p : Value) : Prop :=
  SemEqI ρ a b ∧ ProofMember ρ p

def FitsFixture (ν : Valuation) (ρ : EnvI) : Prop :=
  EqProofMember ρ (translate ν EqLargeFixture.parameter)
    (translate ν EqLargeFixture.parameter) (ρ 0)

theorem unit_cons (ρ : EnvI) (S : Value) :
    ValueEq (unitValue (EnvI.cons S ρ)) (unitValue ρ) := by
  intro c
  change ApproxI (EnvI.cons S ρ) unitTerm c ↔ ApproxI ρ unitTerm c
  have hclosed : lift 0 1 unitTerm = unitTerm := rfl
  simpa only [hclosed] using approxI_cons_lift0_iff ρ S unitTerm c

/-- Supplied realization of the one proof binding, not an assumed fitting
semantic environment for every source constant. -/
def fixtureEnv : EnvI := EnvI.cons (unitValue EnvI.bot) EnvI.bot

theorem fixtureEnv_fits (ν : Valuation) : FitsFixture ν fixtureEnv := by
  refine ⟨SemEqI.refl fixtureEnv _, ?_⟩
  exact ValueEq.symm (unit_cons EnvI.bot (unitValue EnvI.bot))

theorem major_unit {ν : Valuation} {ρ : EnvI} (hρ : FitsFixture ν ρ) :
    ValueEq (denote ν ρ (.bvar 0)) (unitValue ρ) := by
  intro c
  change ApproxI ρ (.bvar 0) c ↔ ApproxI ρ unitTerm c
  constructor
  · intro h
    rcases approxI_bvar_inv h with rfl | hm
    · exact .bot _ _
    · exact (hρ.2 c).mp hm
  · intro h; exact .bvar ((hρ.2 c).mpr h)

/-- Reflexivity actually denotes the same unit under every valuation and
every term environment. Its two applications use the ordinary beta law. -/
theorem refl_unit (ν : Valuation) (ρ : EnvI) :
    ValueEq (denote ν ρ (EqLargeFixture.reflAt EqLargeFixture.parameter)) (unitValue ρ) := by
  exact eq_of_betaRun (k := 2) (ρ := ρ)
    (show betaRun 2 (translate ν (EqLargeFixture.reflAt EqLargeFixture.parameter)) = unitTerm from rfl)

/-- The actual canonical proof is not the bottom value of the old
refuted candidate, in any level valuation or term environment. -/
theorem refl_nonbottom (ν : Valuation) (ρ : EnvI) :
    ¬ ValueEq (denote ν ρ (EqLargeFixture.reflAt EqLargeFixture.parameter)) bottom := by
  intro h
  exact unit_nonbottom ρ (ValueEq.trans (ValueEq.symm (refl_unit ν ρ)) h)

/-- Soundness of the exact inhabited irrelevance node used by the fixture. -/
theorem fixture_irr_sound {ν : Valuation} {ρ : EnvI} (hρ : FitsFixture ν ρ) :
    InterpretedEq ν ρ (.bvar 0) (EqLargeFixture.reflAt EqLargeFixture.parameter) :=
  ValueEq.trans (major_unit hρ) (ValueEq.symm (refl_unit ν ρ))

/-- The motive's interpretation is the actual requested universe code. -/
theorem fixture_motive_sound (ν : Valuation) (ρ : EnvI) :
    SemEqI ρ
      (.app (.app (translate ν EqLargeFixture.motive) (translate ν EqLargeFixture.parameter)) unitTerm)
      (sortTerm (eval ν EqLargeFixture.one)) := by
  apply eq_of_betaRun (k := 4)
  rfl

/-- The actual prefix exposes the generic unit eliminator for ANY major
expression. This is six ordinary target beta steps, not call recognition. -/
theorem fixture_call_operation (ν : Valuation) (ρ : EnvI) (p : Expr Nat) :
    SemEqI ρ (.app (translate ν EqLargeFixture.recPrefix) p)
      (jOperation (translate ν EqLargeFixture.motive) (translate ν EqLargeFixture.result)
        (translate ν EqLargeFixture.parameter) p) := by
  apply eq_of_betaRun (k := 6)
  rfl

/-- The interpreted minor is returned by the supplied generic unit law. -/
theorem fixture_call_unit (ν : Valuation) (ρ : EnvI) :
    SemEqI ρ (.app (translate ν EqLargeFixture.recPrefix) unitTerm)
      (translate ν EqLargeFixture.result) :=
  SemEqI.trans (fixture_call_operation ν ρ unitTerm)
    (jOperation_unit _ _ _ _ (SemEqI.refl ρ unitTerm))

/-- First requested test: the open irr -> app -> iota conversion is sound
at every fitting realization of its real assumption context. -/
theorem open_conversion_sound {ν : Valuation} {ρ : EnvI} (hρ : FitsFixture ν ρ) :
    InterpretedEq ν ρ (EqLargeFixture.call (.bvar 0)) EqLargeFixture.result := by
  exact SemEqI.trans
    (semEqI_app (SemEqI.refl ρ (translate ν EqLargeFixture.recPrefix)) (major_unit hρ))
    (fixture_call_unit ν ρ)

/-- Second requested test: the actual closed `ConvA.iota` endpoints. -/
theorem canonical_iota_sound (ν : Valuation) (ρ : EnvI) :
    InterpretedEq ν ρ StrictProofModelBoundary.canonicalCallA3 EqLargeFixture.result := by
  exact SemEqI.trans
    (semEqI_app (SemEqI.refl ρ (translate ν EqLargeFixture.recPrefix)) (refl_unit ν ρ))
    (fixture_call_unit ν ρ)

/-- A simultaneous positive bundle: the exact admitted source derivations,
the supplied fitting environment, both semantic equalities for all partial
level valuations, and a proof unit unequal to bottom. -/
theorem inhabited_unit_probe :
    eraseEnv EqLargeFixture.env = eqEnvT ∧
    Nonempty (EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) ∧
    Nonempty (CtxWfA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 EqLargeFixture.context) ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 EqLargeFixture.context
      (EqLargeFixture.call (.bvar 0)) EqLargeFixture.result (.sort EqLargeFixture.one)) ∧
    Nonempty (ConvA EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) 0 []
      StrictProofModelBoundary.canonicalCallA3 EqLargeFixture.result (.sort EqLargeFixture.one)) ∧
    (∀ ν : Valuation, FitsFixture ν fixtureEnv ∧
      InterpretedEq ν fixtureEnv (EqLargeFixture.call (.bvar 0)) EqLargeFixture.result ∧
      InterpretedEq ν EnvI.bot StrictProofModelBoundary.canonicalCallA3 EqLargeFixture.result) ∧
    ¬ ValueEq (unitValue fixtureEnv) bottom :=
  ⟨EqLargeFixture.erase_env, EqLargeFixture.wf, ⟨EqLargeFixture.contextWf⟩,
    EqLargeFixture.conversion, StrictProofModelBoundary.canonicalIotaConversionA3,
    fun ν => ⟨fixtureEnv_fits ν, open_conversion_sound (fixtureEnv_fits ν), canonical_iota_sound ν EnvI.bot⟩,
    unit_nonbottom fixtureEnv⟩

end Rcic.Declarative.Ann.LR3.UnitModel
