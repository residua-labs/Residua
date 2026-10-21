import rcic.RcicF8PiRowPackaging
import rcic.RcicF8JTransportPins

set_option autoImplicit false

namespace Rcic.Declarative.F8Measure.PiRowPackaging.Pins

open Rcic.Syn PEqTProofFront PEqLeafTPropPins

def roots : List (Jd emptyEnv 0) := [.cv J3.Pins.aliasUp]

def sourceCert : ∃ r ∈ roots, SubEq (.cv J3.Pins.aliasUp) r :=
  ⟨_, .head _, .inl rfl⟩

/-- A nonidentity domain conversion, with the codomain still under the left domain. -/
def components : XOut roots [] P (.bvar 0) aliasP (.bvar 0) :=
  ⟨.ofCv .zero (.lit J3.Pins.aliasUp sourceCert), .refl [.assumption P] (.bvar 0)⟩

def componentBounds : ∀ ℓ ∈ XOut.leaves components, Below ℓ roots := by
  intro ℓ hℓ
  exact below_of_mem (by
    simpa only [components, XOut.leaves, EvTc.leaves, EvCv.leaves,
      List.append_nil] using hℓ)

/-- The generic fixture records a live J census; it is not the Via worker. -/
def returnedOut : SegOut roots [] P (.bvar 0) aliasP (.bvar 0) roots :=
  ⟨components, [], roots, componentBounds,
    fun C hC => absurd hC (List.not_mem_nil _),
    fun j hj => below_of_mem hj,
    fun j hj => by
      have hj' : j = .cv J3.Pins.aliasUp := by simpa only [roots, List.mem_singleton] using hj
      subst j
      exact ⟨[], P, aliasP, .sort .zero, J3.Pins.aliasUp, rfl⟩,
    fun hne => absurd rfl hne⟩

def fixtureAnswer : Option (SegOut roots [] P (.bvar 0) aliasP (.bvar 0) roots) :=
  some returnedOut

def materialized : MaterializedSegOut EnvWfT.empty fixtureAnswer :=
  materializeSegOut EnvWfT.empty fixtureAnswer returnedOut rfl

theorem domain_nonidentity : P ≠ aliasP := fun h => alias_nonliteral h.symm

theorem actual_returned_output : materialized.out = returnedOut := rfl

theorem actual_returned_option : fixtureAnswer = some materialized.out :=
  materialized.returned

theorem exact_domain_materialization : materialized.domain =
    TyConvT.of [] P aliasP .zero J3.Pins.aliasUp := rfl

theorem exact_codomain_materialization : materialized.codomain =
    TyConvT.refl [.assumption P] (.bvar 0) := rfl

theorem census_retained : materialized.out.2.2.1 = roots := rfl

theorem row_result : RowResult emptyEnv 0 [] P (.bvar 0) aliasP (.bvar 0) :=
  piRow_of_segOut_some EnvWfT.empty fixtureAnswer returnedOut rfl

/-- The mutant keeps the same components but silently erases the returned census. -/
def erasedCensus : SegOut roots [] P (.bvar 0) aliasP (.bvar 0) roots :=
  SegOut.ofA components componentBounds

def sameComponents (candidate : SegOut roots [] P (.bvar 0) aliasP (.bvar 0) roots) : Prop :=
  candidate.1 = returnedOut.1

def exactAnswer (candidate : SegOut roots [] P (.bvar 0) aliasP (.bvar 0) roots) : Prop :=
  fixtureAnswer = some candidate

theorem mutant_accepts_erased_census : sameComponents erasedCensus := rfl

theorem exact_answer_accepts_returned : exactAnswer returnedOut := rfl

theorem exact_answer_refuses_erased_census : ¬ exactAnswer erasedCensus := by
  intro h
  have ho : returnedOut = erasedCensus := Option.some.inj h
  have hj : roots = [] := congrArg (fun o => o.2.2.1) ho
  exact List.noConfusion hj

end Rcic.Declarative.F8Measure.PiRowPackaging.Pins
