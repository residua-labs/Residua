import rcic.RcicNativeTypedModelCovTStage
import rcic.RcicNativeTypedModelCovTSpine
import rcic.RcicNativeTypedModelTypingFin
import rcic.RcicNativeTypedModelCovSTemplate

/-!
# Inductive type observations with native provenance

These are inductive families, not a Type-valued recursive decoder.
Universe-parameter arity and the finite information stage are separate.
Native sort typing is retained at every type node. Rigid and variable
arguments are term-observation records; a lambda argument is not asked to
have a type head. A native neutral recursor may have a computed semantic
observation, so a rigid readback does not require a matching compact head.
The readback-spine trace retains actual application alternatives and
demands producing the same compact at that head. Independently recorded
staged arguments are not substituted for the trace. Its internal
observations need not fit the enclosing result's information budget.
General transport from the original type observation to this readback
spine observation is part of the open supply obligation.

Pi row obligations are conditional on an actual typed argument observing
the demand. They do not require every stored row to have such an argument.
The constructor requires an actual function of child views. A pointwise
Nonempty supply alone does not construct that function; no choice principle
or such extraction is supplied here. This remains part of the general
constructive supply obligation.

The general view-supply interface is an OPEN port, not a theorem. All
suppliers in companion modules identify their actual fragment or fixture.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit ReadbackCK2Audit
open TypedModelAudit.TypingFin TypedModelCovSAudit

/-- Admissibility is indexed by the actual native argument. Native typing
and every demanded observation must be supplied at this very stage. -/
structure CovTAdmissible (E : ResolvedEnv) (arity stage : Nat)
    (Γ : LCtx) (ρ : EnvT) (D a : Expr Nat) (ds : List CptT) : Prop where
  typing : Nonempty (HasTyT E arity Γ a D)
  observed : ∀ u ∈ ds, ApproxTKStage E arity stage Γ ρ a u

/-- Finite records of actual term observations. These arguments need not
be native types; in particular their exact nonbottom lambda tables survive.
The source observation is recorded separately at the enclosing type node. -/
inductive TyObsArgs (E : ResolvedEnv) (arity stage : Nat) :
    LCtx → EnvT → List (Expr Nat) → List CptT → Type
  | nil (Γ : LCtx) (ρ : EnvT) : TyObsArgs E arity stage Γ ρ [] []
  | cons {Γ : LCtx} {ρ : EnvT}
      {a : Expr Nat} {c : CptT} {as : List (Expr Nat)} {cs : List CptT}
      (head : ApproxTKStage E arity stage Γ ρ a c)
      (tail : TyObsArgs E arity stage Γ ρ as cs) :
      TyObsArgs E arity stage Γ ρ (a :: as) (c :: cs)

/-- Native provenance paired with a finite observation. Every readback
field is a certificate; the inductive definition does not compute one. -/
inductive TyObsView (E : ResolvedEnv) (arity stage : Nat) :
    LCtx → EnvT → Expr Nat → CptT → Type
  | unknown {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} (u : Level)
      (typing : HasTyT E arity Γ A (.sort u)) :
      TyObsView E arity stage Γ ρ A .bot
  | var {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
      (u : Level) (typing : HasTyT E arity Γ A (.sort u))
      (i : Nat) (xs : List (Expr Nat)) (cs : List CptT)
      (read : RedR (WhStepCK2 E arity) Γ A (foldApps (.bvar i) xs))
      (normal : NormalR (WhStepCK2 E arity) Γ (foldApps (.bvar i) xs))
      (observed : ApproxTKStage E arity stage Γ ρ A c)
      (arguments : TyObsArgs E arity stage Γ ρ xs cs)
      (origin : CovTSpineProvenance E arity Γ ρ (.bvar i) xs c) :
      TyObsView E arity stage Γ ρ A c
  | sort {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
      (u : Level) (typing : HasTyT E arity Γ A (.sort u)) (l : Level)
      (read : RedR (WhStepCK2 E arity) Γ A (.sort l))
      (observed : ApproxTKStage E arity stage Γ ρ A c) :
      TyObsView E arity stage Γ ρ A c
  | pi {Γ : LCtx} {ρ : EnvT} {A D B : Expr Nat} {d : CptT}
      {rows : List (List CptT × CptT)}
      (u : Level) (typing : HasTyT E arity Γ A (.sort u))
      (read : RedR (WhStepCK2 E arity) Γ A (.pi D B))
      (observed : ApproxTKStage E arity stage Γ ρ A (.pi d rows))
      (domain : TyObsView E arity stage Γ ρ D d)
      (outputs : ∀ (s : {s // s ∈ rows}) (a : Expr Nat),
        CovTAdmissible E arity stage Γ ρ D a s.val.1 →
        TyObsView E arity stage Γ ρ (instantiate0 a B) s.val.2) :
      TyObsView E arity stage Γ ρ A (.pi d rows)
  | rigid {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
      (u : Level) (typing : HasTyT E arity Γ A (.sort u))
      (r : Nat) (ls : List Level) (xs : List (Expr Nat)) (cs : List CptT)
      (read : RedR (WhStepCK2 E arity) Γ A (foldApps (.const r ls) xs))
      (normal : NormalR (WhStepCK2 E arity) Γ (foldApps (.const r ls) xs))
      (observed : ApproxTKStage E arity stage Γ ρ A c)
      (arguments : TyObsArgs E arity stage Γ ρ xs cs)
      (origin : CovTSpineProvenance E arity Γ ρ (.const r ls) xs c) :
      TyObsView E arity stage Γ ρ A c

theorem TyObsArgs.length_eq {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {xs : List (Expr Nat)} {cs : List CptT}
    (v : TyObsArgs E arity stage Γ ρ xs cs) : xs.length = cs.length := by
  induction v with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The native universe is data carried by the view, not an external
semantic positivity tag. Its normalization is the existing decidable eqN. -/
def TyObsView.universe {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
    (v : TyObsView E arity stage Γ ρ A c) : Level :=
  match v with
  | .unknown u _ => u
  | .var u _ _ _ _ _ _ _ _ _ => u
  | .sort u _ _ _ _ => u
  | .pi u _ _ _ _ _ => u
  | .rigid u _ _ _ _ _ _ _ _ _ _ => u

def TyObsView.typing {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
    (v : TyObsView E arity stage Γ ρ A c) :
    HasTyT E arity Γ A (.sort v.universe) := by
  cases v <;> assumption

theorem TyObsView.observed {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
    (v : TyObsView E arity stage Γ ρ A c) :
    ApproxTKStage E arity stage Γ ρ A c := by
  cases v with
  | unknown => exact approxTKStage_bot _ _ _ _ _ _
  | var _ _ _ _ _ _ _ ho _ _ => exact ho
  | sort _ _ _ _ ho => exact ho
  | pi _ _ _ ho _ _ => exact ho
  | rigid _ _ _ _ _ _ _ _ ho _ _ => exact ho

def TyObsView.positive {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
    (v : TyObsView E arity stage Γ ρ A c) : Bool :=
  decEqN v.universe .zero

def TyObsView.positive_typing {E : ResolvedEnv} {arity stage : Nat}
    {Γ : LCtx} {ρ : EnvT} {A : Expr Nat} {c : CptT}
    (v : TyObsView E arity stage Γ ρ A c) (hp : v.positive = true) :
    HasTyT E arity Γ A (.sort .zero) := by
  apply HasTyT.conv Γ A (.sort v.universe) (.sort .zero) (.succ v.universe)
    v.typing
  exact .sorts Γ v.universe .zero (decEqN_sound _ _ hp)

/-- These are the strict structural decreases available at Pi view
children. Neither native readback syntax nor an application result is used. -/
theorem covT_view_pi_domain_decreases (d : CptT)
    (rows : List (List CptT × CptT)) :
    sizeOf d < sizeOf (CptT.pi d rows) := covS_pi_domain_size_lt d rows

theorem covT_view_pi_output_decreases (d : CptT)
    (rows : List (List CptT × CptT)) (s : List CptT × CptT) (hs : s ∈ rows) :
    sizeOf s.2 < sizeOf (CptT.pi d rows) := covS_pi_output_size_lt d rows s hs

/-- OPEN general supplier. It is deliberately a named proposition, not an
assumed field of an interpreter or a claimed fundamental result. -/
def CovTViewSupply (E : ResolvedEnv) (arity stage : Nat) : Prop :=
  ∀ (Γ : LCtx) (ρ : EnvT) (A : Expr Nat) (u : Level) (c : CptT),
    Nonempty (EnvWfT E) → Nonempty (CtxWfT E arity Γ) →
    Nonempty (HasTyT E arity Γ A (.sort u)) →
    EnvTypedFinAtT (ctxModelT_approxTK E arity Γ) Γ ρ →
    CtxEnvM (ctxModelT_approxTK E arity Γ) Γ ρ →
    ApproxTKStage E arity stage Γ ρ A c →
    Nonempty { v : TyObsView E arity stage Γ ρ A c // eqN v.universe u }

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_T_VIEW_ROOTS
#print axioms CovTAdmissible
#print axioms TyObsArgs
#print axioms TyObsView
#print axioms TyObsArgs.length_eq
#print axioms TyObsView.universe
#print axioms TyObsView.typing
#print axioms TyObsView.observed
#print axioms TyObsView.positive
#print axioms TyObsView.positive_typing
#print axioms covT_view_pi_domain_decreases
#print axioms covT_view_pi_output_decreases
#print axioms CovTViewSupply
-- END RCIC_NATIVE_TYPED_MODEL_COV_T_VIEW_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit
