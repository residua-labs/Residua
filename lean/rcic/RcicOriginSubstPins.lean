import rcic.RcicOriginSubst
import rcic.RcicPEqLeafTPropPins

set_option maxRecDepth 8192

/-!
A-1: three independent pins on an actual beta/structural peak.
The body index depends syntactically on the bound variable.
Measured old request 20, substituted request 896, outer peak 1827.
This witness is NOT a counterexample to that outer Nat bound. closure_claim = 0.
-/

namespace Rcic.Declarative.F8OriginSubst.Pins
open F8PiSourceOrigin PEqTProofFront
private def cl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
private def si : EnvMembersSubstStable emptyEnv := envWfT_subst_inst EnvWfT.empty

def binder : LCtx := [.assumption P]
def x : Expr Nat := .bvar 0
def y : Expr Nat := .app idP x
def family : Expr Nat := .lam P P
def bodyIndex : Expr Nat := .app family x

def familyTy (Γ : LCtx) : HasTyT emptyEnv 0 Γ family (.pi P (.sort .zero)) :=
  .lam Γ P .zero P (.sort .zero) (P_ty Γ) (P_ty (.assumption P :: Γ))
def xTy : HasTyT emptyEnv 0 binder x P := .bvar binder 0 P rfl
def yTy : HasTyT emptyEnv 0 binder y P := .app binder idP x P P (idP_ty binder) xTy
def bodyIndexTy : HasTyT emptyEnv 0 binder bodyIndex (.sort .zero) :=
  .app binder family x P (.sort .zero) (familyTy binder) xTy
def bodyIndexConv : ConvT emptyEnv 0 binder bodyIndex P (.sort .zero) :=
  .beta binder P P x (.sort .zero) .zero (P_ty binder)
    (P_ty (.assumption P :: binder)) xTy

def xAtIndex : HasTyT emptyEnv 0 binder x bodyIndex :=
  .conv binder x P bodyIndex .zero xTy (.symm _ _ _ _ bodyIndexConv)
def yAtIndex : HasTyT emptyEnv 0 binder y bodyIndex :=
  .conv binder y P bodyIndex .zero yTy (.symm _ _ _ _ bodyIndexConv)

def innerStep : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 binder x y bodyIndex :=
  .peq binder x y bodyIndex
    ⟨.proof binder x y P P (P_ty binder) (P_ty binder) xTy yTy, xAtIndex, yAtIndex⟩
def innerOrigin : OriginTrace innerStep :=
  .proof (P_ty binder) (P_ty binder) xTy yTy xAtIndex yAtIndex

def paddedN : Nat → HasTyT emptyEnv 0 [] p P
  | 0 => p_ty []
  | k+1 => .conv [] p P P .zero (paddedN k) (.refl [] P (.sort .zero) (P_ty []))

def argConv : ConvT emptyEnv 0 [] p q P :=
  .irr [] P p q (P_ty []) (p_ty []) (q_ty [])
def indexConv : ConvT emptyEnv 0 [] (instantiate0 p bodyIndex)
    (instantiate0 q bodyIndex) (.sort .zero) :=
  convT_inst0_pair_sort (P_ty []) bodyIndexTy argConv (p_ty []) (q_ty [])

def source : Expr Nat := .app (.lam P x) p
def target : Expr Nat := .app (.lam P y) q
def commonIndex : Expr Nat := instantiate0 p bodyIndex

def betaInput (k : Nat) :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] source p commonIndex :=
  .beta [] P x x p p bodyIndex .zero .zero .zero
    (P_ty []) bodyIndexTy (substTy0 cl si (paddedN k) bodyIndexTy)
    (.refl binder x bodyIndex xAtIndex) (.refl [] p P (paddedN k))
    (substTy0 cl si (paddedN k) xAtIndex)

def structuralInput (k : Nat) :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] source target commonIndex :=
  .peq [] source target commonIndex
    ⟨.app [] (.lam P x) (.lam P y) p q
      (.lam [] P P x y (PEqT.refl P)
        (.proof binder x y P P (P_ty binder) (P_ty binder) xTy yTy))
      (.proof [] p q P P (P_ty []) (P_ty []) (p_ty []) (q_ty [])),
      .app [] (.lam P x) p P bodyIndex
        (.lam [] P .zero x bodyIndex (P_ty []) xAtIndex) (paddedN k),
      .conv [] target (instantiate0 q bodyIndex) commonIndex .zero
        (.app [] (.lam P y) q P bodyIndex
          (.lam [] P .zero y bodyIndex (P_ty []) yAtIndex) (q_ty []))
        (.symm _ _ _ _ indexConv)⟩

/-- A1(a): two literal inner fields, bounded by the actual OUTER peak. -/
theorem pin_original_request_bound :
    innerOrigin.origin.cost < stepSize (betaInput 32) + stepSize (structuralInput 32) := by
  decide

/-- The local U callback is produced independently for the variable subject.
It is invoked BEFORE any substitution. This is not a global U supplier. -/
def originalAnswer : innerOrigin.origin.Answer :=
  let localU : SourceUniqueBelow emptyEnv 0 binder x
      (stepSize (betaInput 32) + stepSize (structuralInput 32)) :=
    fun hR hS _ => introTypeSpine_unique cl si (e := x) rfl hR hS
  localU innerOrigin.origin.originTyping innerOrigin.origin.proofTyping
    pin_original_request_bound

/-- A1(b): actual six-field substitution; the answer is the transported chain. -/
def pin_same_subst_answer :
    AnsweredOrigin (proof_root_subst0 cl si (P_ty binder) (P_ty binder)
      xTy yTy xAtIndex yAtIndex (paddedN 32)) :=
  proof_root_subst0_answer cl si (P_ty binder) (P_ty binder)
    xTy yTy xAtIndex yAtIndex (paddedN 32) originalAnswer

theorem pin_same_answer_is_transport : pin_same_subst_answer.2 =
    substChain0 cl si (paddedN 32) originalAnswer := rfl

/-- A1(c): distinct arguments and distinct result indices; real ConvT required. -/
def pin_mixed_subst_answer :
    Σ' h : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 [] p (.app idP q) commonIndex,
      AnsweredOrigin h ×' ConvT emptyEnv 0 [] p (.app idP q) commonIndex :=
  mixed_subst_answered cl si (P_ty []) bodyIndexTy (P_ty binder)
    xAtIndex yAtIndex (paddedN 32) (q_ty []) argConv originalAnswer

theorem pin_indices_nonliteral :
    instantiate0 p bodyIndex ≠ instantiate0 q bodyIndex := by
  intro h
  have hpq := (Expr.app.inj h).2
  cases hpq

theorem pin_arguments_differ : p ≠ q := by intro h; cases h

end Rcic.Declarative.F8OriginSubst.Pins
