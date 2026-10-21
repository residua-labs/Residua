import rcic.RcicParRedTSubstNoTC
import rcic.RcicDT0709EnvWf

/-!
# PIN — `parRedT_substSame'` on a real β step (W-X-SUBST S0, #7107)

`[x : N] ⊢ (λn. succ n) x ⇒ succ x : N` (a `ParRedT.beta` at `natEnvU`), substituted at `j = 0` by
`zero`, materializes to `[] ⊢ (λn. succ n) zero ⇒ succ zero : N`. Every premise is discharged by data:
`hcl`/`hinst`/`hS` from `natEnvUWfT` (the regularity supplier is `endpoints3_of_envWfT` on the
`refl` conversion), the `PEq` suppliers by elimination (`PEq := PEmpty`), the contexts' `CtxWfT` as
constructors. Nothing here is `sorry`/`Nonempty`-only. `closure_claim` 0.
-/

namespace Rcic.Declarative.SubstSamePins

/-- `N`. -/
def A : Expr Nat := .const 0 []
/-- `succ n` under `n : N`. -/
def body : Expr Nat := .app (.const 2 []) (.bvar 0)
/-- `λn. succ n`. -/
def f : Expr Nat := .lam A body
/-- `[x : N]`. -/
def Γ₁ : LCtx := [.assumption A]

/-- `N : Sort 1` in any context. -/
def natTyU {n : Nat} {Γ : LCtx} : HasTyT natEnvU n Γ A (.sort (.succ .zero)) :=
  .const _ 0 [] natFamMember rfl rfl rfl

/-- `zero : N` at `[]`. -/
def zeroTyU {n : Nat} : HasTyT natEnvU n [] (.const 1 []) A :=
  .const _ 1 [] natZeroMember rfl rfl rfl

/-- `succ x : N` under `x : N` (any prefix context). -/
def bodyTyU {n : Nat} {Γ : LCtx} : HasTyT natEnvU n (.assumption A :: Γ) body A :=
  .app _ (.const 2 []) (.bvar 0) A A (.const _ 2 [] natSuccMember rfl rfl rfl) (.bvar _ 0 _ rfl)

/-- the real step: `[x : N] ⊢ (λn. succ n) x ⇒ succ x : N` by `beta`. -/
def stepT {n : Nat} :
    ParRedT (fun _ _ _ _ => PEmpty) natEnvU n Γ₁ (.app f (.bvar 0)) body A :=
  .beta Γ₁ A body body (.bvar 0) (.bvar 0) A (.succ .zero) (.succ .zero) (.succ .zero)
    natTyU natTyU natTyU
    (.refl _ _ _ bodyTyU) (.refl _ _ _ (.bvar _ 0 _ rfl)) bodyTyU

/-- `[x : N]` is well-formed, as data. -/
def ctxWf₁ {n : Nat} : CtxWfT natEnvU n Γ₁ := .assumption [] A (.succ .zero) .nil natTyU

/-- the regularity supplier at `natEnvU`, conditional on context well-formedness. -/
def hSU {n : Nat} : ∀ {Γ : LCtx} {e T : Expr Nat}, CtxWfT natEnvU n Γ →
    HasTyT natEnvU n Γ e T → (u : Level) ×' HasTyT natEnvU n Γ T (.sort u) :=
  fun hΓ h =>
    (endpoints3_of_envWfT natEnvUWfT (substLetT_of_envWfT natEnvUWfT)
      (constsRightDataT_of_envWfT natEnvUWfT) hΓ (.refl _ _ _ h)).2.2

/-- PIN — `(λn. succ n) zero ⇒ succ zero : N` at `[]`, by substituting `zero` for `x` in `stepT`. -/
def pin_parRedT_substSame'_beta {n : Nat} :
    ParRedT (fun _ _ _ _ => PEmpty) natEnvU n []
      (.app f (.const 1 [])) (.app (.const 2 []) (.const 1 [])) A :=
  parRedT_substSame' (envClosed_of_envWfT natEnvUWfT)
    (envMembersSubstStable_of_envWfT natEnvUWfT)
    (fun h => nomatch h) (fun h => nomatch h) hSU (fun h => nomatch h)
    (j := 0) stepT rfl zeroTyU zeroTyU .nil ctxWf₁

end Rcic.Declarative.SubstSamePins

#print axioms Rcic.Declarative.SubstSamePins.stepT
#print axioms Rcic.Declarative.SubstSamePins.pin_parRedT_substSame'_beta
