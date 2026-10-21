import rcic.RcicF8XValleyStrict

/-!
# Successful segment answers at the plain row boundary

This module only materializes an actual successful `SegOut` answer. Its record
retains that answer, the equality to the supplied `Option`, and the complete call
census with its bounds. Only `rowResult` forgets the census. The codomain stays
under the left domain `A`, as in `XOut`.

The materializer is the existing `EvTc.val`; there is no new interpretation of
provenance, no worker availability result, and no claim of callback closure.
The Via front can instantiate this boundary when its implementation lands.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.F8Measure.PiRowPackaging

open Rcic.Syn

/-- The two plain weak-row components, with the codomain under the left domain. -/
abbrev RowResult (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B A' B' : Expr Nat) : Prop :=
  Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B')

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx}
  {A B A' B' : Expr Nat} {L : List (Jd E n)}

/-- An actual successful answer and the plain components of that same answer.
The full `out`, including its census and bounds, remains available. -/
structure MaterializedSegOut (hW : EnvWfT E)
    (answer : Option (SegOut R Γ A B A' B' L)) where
  out : SegOut R Γ A B A' B' L
  returned : answer = some out
  domain : TyConvT E n Γ A A'
  codomain : TyConvT E n (.assumption A :: Γ) B B'
  domain_eq : domain = out.1.1.val (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW)
  codomain_eq : codomain = out.1.2.val (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW)

/-- Materialize the two components of precisely the returned segment. -/
def materializeSegOut (hW : EnvWfT E) (answer : Option (SegOut R Γ A B A' B' L))
    (out : SegOut R Γ A B A' B' L) (returned : answer = some out) :
    MaterializedSegOut hW answer where
  out := out
  returned := returned
  domain := out.1.1.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
  codomain := out.1.2.val (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
  domain_eq := rfl
  codomain_eq := rfl

theorem materializeSegOut_out (hW : EnvWfT E)
    (answer : Option (SegOut R Γ A B A' B' L)) (out : SegOut R Γ A B A' B' L)
    (returned : answer = some out) : (materializeSegOut hW answer out returned).out = out := rfl

/-- The final projection; this is the only boundary here that drops the census. -/
def MaterializedSegOut.rowResult {hW : EnvWfT E}
    {answer : Option (SegOut R Γ A B A' B' L)} (m : MaterializedSegOut hW answer) :
    RowResult E n Γ A B A' B' :=
  ⟨⟨m.domain⟩, ⟨m.codomain⟩⟩

/-- Conditional weak-row projection from an actual successful segment answer.
It asserts no availability for the supplied worker answer. -/
theorem piRow_of_segOut_some (hW : EnvWfT E)
    (answer : Option (SegOut R Γ A B A' B' L)) (out : SegOut R Γ A B A' B' L)
    (returned : answer = some out) : RowResult E n Γ A B A' B' :=
  (materializeSegOut hW answer out returned).rowResult

end Rcic.Declarative.F8Measure.PiRowPackaging
