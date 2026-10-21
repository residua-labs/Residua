import rcic.RcicAnnSemPrefixRows
import rcic.RcicAnnIotaSR
import rcic.RcicAnnSpineConv
import rcic.RcicTypedEnvEntry
import rcic.RcicTypedGroupPinsList

/-!
# M3-b GLM — DT009T-ScopeSupply: the seven endpoint supplies, discharged IN SCOPE

The conditional `DT009T_endpoints(S)` carries seven named endpoint debts. On
environments in the semantic-prefix bridge's scope (`EnvWfT + InScope`) those
debts need not be supplied from outside: the existing annotation proofs ALREADY
establish both endpoints, and this module composes them —

    EnvWfT + InScope
      → `annEnvA_of_envWfT_semPrefix` → an exactly-erasing `AnnEnvA`
      → `annCtxWfT'` + `annConvT'` → the annotated context and the same-type
        conversion on the copy
      → `convA_hasTy_left` / `convA_hasTy_right` → both endpoints' `HasTyA`
      → `hasTyT_of_hasTyA` → `Nonempty (HasTyT E n Γ a/b T)` on the formal
        judgment (the exact erasure substitutes the environment away).

The debt-carrying `DT009T_endpointsS` is NOT invoked — the unconditional
conclusion is derived directly; no `T1`/`T2`, `EnvSemA` or endpoint typing is
re-demanded of the caller. The generic conditional interface stays as-is for
out-of-scope environments.

Consumption pins (real inputs, none taking a supply parameter):
* `pin_inScope_zeta` — a conversion at a NON-sort type (a π): the zeta rule's
  right endpoint, the debt territory of `ConvTZetaRightT`, supplied in scope;
* `pin_inScope_zeta_symm` — its `.symm`, endpoints swapped;
* `pin_inScope_eta` — the η rule's LEFT endpoint (the `ConvTEtaLeftT` debt
  territory), supplied in scope on the identity function.

All on the REAL two-group environment `listEnvUT` through `listEnvUWfT` +
`listEnvUWfT_inScope`.
-/

namespace Rcic.Declarative

open Rcic.Declarative.Ann

/-- DT009T IN SCOPE: over every environment the semantic-prefix bridge admits,
    EVERY typed conversion determines BOTH its endpoints' typings — the seven
    named supplies of the conditional interface are discharged here by the
    annotation side's own endpoint theorems, consumed through the bridge. -/
theorem DT009T_endpoints_inScope {E : ResolvedEnv}
    (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (h : ConvT E n Γ a b T) :
    Nonempty (HasTyT E n Γ a T) ∧
    Nonempty (HasTyT E n Γ b T) := by
  obtain ⟨EA, rfl, C, hn⟩ := annEnvA_of_envWfT_semPrefix hW hP
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT' C hn hΓ
  obtain ⟨aA, bA, TA, ha, hb, hT, ⟨cA⟩⟩ := annConvT' C hn h hΓA hctx
  subst ha; subst hb; subst hT
  obtain ⟨hWA⟩ := C.wf
  have hl := hasTyT_of_hasTyA hWA (C.hNS hn) (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓA cA)
  have hr := hasTyT_of_hasTyA hWA (C.hNS hn) (convA_hasTy_right C.hE C.hI C.hR C.hIS hΓA cA)
  rw [hctx] at hl hr
  exact ⟨hl, hr⟩

/-! ## consumption pins on the two-group environment -/

section Pins

/-- the let whose zeta conversion is built: `let (x : Sort 1) := Sort 0 in
    λ (y : Sort 0), y` — the let's own type index is `Sort 0`'s sort... no: the
    zeta rule's conversion type is `instantiate0 value B`, here
    `Π (y : Sort 0), Sort 0` — a π, NOT a sort. -/
def pinZetaLetT (E : ResolvedEnv) (n : Nat) :
    HasTyT E n []
      (.letE (.sort (.succ .zero)) (.sort .zero)
        (.lam (.sort .zero) (.bvar 0)))
      (.pi (.sort .zero) (.sort .zero)) :=
  HasTyT.letE [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
    (.pi (.sort .zero) (.sort .zero))
    (.lam (.sort .zero) (.bvar 0))
    (HasTyT.sort [] (.succ .zero)) (HasTyT.sort [] .zero)
    (HasTyT.lam [LocalDecl.letBinding (.sort (.succ .zero)) (.sort .zero)]
      (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
      (HasTyT.sort _ .zero)
        (HasTyT.bvar [LocalDecl.assumption (.sort .zero),
          LocalDecl.letBinding (.sort (.succ .zero)) (.sort .zero)] 0 (.sort .zero) rfl))

/-- the zeta conversion at the π type — the right endpoint is
    `instantiate0 (Sort 0) (λ (y : Sort 0), y)`, the `ConvTZetaRightT`
    debt's territory. -/
def pinZetaConvT (E : ResolvedEnv) (n : Nat) :
    ConvT E n []
      (.letE (.sort (.succ .zero)) (.sort .zero) (.lam (.sort .zero) (.bvar 0)))
      (instantiate0 (.sort .zero) (.lam (.sort .zero) (.bvar 0)))
      (instantiate0 (.sort .zero) (.pi (.sort .zero) (.sort .zero))) :=
  ConvT.zeta [] (.sort (.succ .zero)) (.sort .zero) (.lam (.sort .zero) (.bvar 0))
    (.pi (.sort .zero) (.sort .zero)) (.succ (.succ .zero))
    (HasTyT.sort [] (.succ .zero)) (HasTyT.sort [] .zero)
    (HasTyT.lam [LocalDecl.letBinding (.sort (.succ .zero)) (.sort .zero)]
      (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
      (HasTyT.sort _ .zero)
        (HasTyT.bvar [LocalDecl.assumption (.sort .zero),
          LocalDecl.letBinding (.sort (.succ .zero)) (.sort .zero)] 0 (.sort .zero) rfl))

/-- PIN (zeta, non-sort type): in scope, the zeta conversion's RIGHT endpoint —
    `ConvTZetaRightT`'s debt territory — is typed, on the two-group
    environment, with NO supply parameter. -/
theorem pin_inScope_zeta {n : Nat} :
    Nonempty (HasTyT listEnvUT n []
      (instantiate0 (.sort .zero) (.lam (.sort .zero) (.bvar 0)))
      (.pi (.sort .zero) (.sort .zero))) :=
  (DT009T_endpoints_inScope listEnvUWfT listEnvUWfT_inScope CtxWfT.nil
    (pinZetaConvT listEnvUT n)).2

/-- PIN (symm at the same non-sort type): the symmetric conversion's endpoints
    are the same pair, swapped. -/
theorem pin_inScope_zeta_symm {n : Nat} :
    Nonempty (HasTyT listEnvUT n []
      (.letE (.sort (.succ .zero)) (.sort .zero) (.lam (.sort .zero) (.bvar 0)))
      (instantiate0 (.sort .zero) (.pi (.sort .zero) (.sort .zero)))) :=
  (DT009T_endpoints_inScope listEnvUWfT listEnvUWfT_inScope CtxWfT.nil
    (ConvT.symm _ _ _ _ (pinZetaConvT listEnvUT n))).2

/-- PIN (eta, the `ConvTEtaLeftT` debt territory): in scope, the eta rule's
    LEFT endpoint — the lam-expansion of the identity on sorts — is typed at
    the π. -/
theorem pin_inScope_eta {n : Nat} :
    Nonempty (HasTyT listEnvUT n []
      (.lam (.sort .zero) (.app (lift 0 1 (.lam (.sort .zero) (.bvar 0))) (.bvar 0)))
      (.pi (.sort .zero) (.sort .zero))) :=
  (DT009T_endpoints_inScope listEnvUWfT listEnvUWfT_inScope CtxWfT.nil
    (ConvT.eta [] (.lam (.sort .zero) (.bvar 0)) (.sort .zero) (.sort .zero)
      (pinEtaF0 listEnvUT n))).1

end Pins

end Rcic.Declarative

#print axioms Rcic.Declarative.DT009T_endpoints_inScope
#print axioms Rcic.Declarative.pin_inScope_zeta
#print axioms Rcic.Declarative.pin_inScope_zeta_symm
#print axioms Rcic.Declarative.pin_inScope_eta
