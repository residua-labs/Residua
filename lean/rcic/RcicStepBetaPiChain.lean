import rcic.RcicTypedInvert
import rcic.RcicTypedConv
import rcic.RcicTypedRowsWf
import rcic.RcicTypedEnvEntry

/-!
# Beta subject reduction from the existing Pi chain row

Application inversion and lambda inversion expose a `TyConvT` between
the lambda's own Pi type and the application's Pi type. The component
chains from `TypedRowsWf.piRow` suffice: retype the argument backwards
along the domain chain, retype the body forwards along the codomain
chain, and apply the existing typed substitution theorem. The outer
application-inversion chain then restores the original type index.

The core reads only the Pi row at the particular context and the two
environment properties used by `hasTyT_subst0S`. It needs no conversion
chain collapsed to a single sort-indexed `ConvT`, no codomain regularity
premise, and no second proof of type-chain substitution. In particular,
it does not consume the refuted, unguarded `PiRowInjT` contract.

The two wrappers use the existing `TypedRowsWf` interface. They remain
conditional on that interface; they do not supply the missing plain
Pi row or close the U/X/P recursion. The concrete pin supplies the rows
through the existing scope-check supplier in `emptyEnv`, where the
scope check is `True`. `closure_claim = 0`.
-/

namespace Rcic.Declarative

/-- Beta preserves the original type index, using only the Pi-chain
row at this context. The row's raw reflexivity case is permitted: its
outputs are type-conversion chains, not invented typed endpoints. -/
theorem step_beta_srT_of_piChain {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hpi : ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧
        Nonempty (TyConvT E n (.assumption A :: Γ) B B'))
    {A0 body arg S : Expr Nat}
    (h : HasTyT E n Γ (.app (.lam A0 body) arg) S) :
    Nonempty (HasTyT E n Γ (instantiate0 arg body) S) := by
  obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
  obtain ⟨_u, B_lam, _hA, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
  obtain ⟨⟨hdom⟩, ⟨hcod⟩⟩ := hpi hcv_lam
  have ha' : HasTyT E n Γ arg A0 :=
    hasTyT_of_tyConv ha (TyConvT.symmT hdom)
  have hb' : HasTyT E n (.assumption A0 :: Γ) body B1 :=
    hasTyT_of_tyConv hbody hcod
  exact ⟨hasTyT_of_tyConv (hasTyT_subst0S hcl hinst hb' ha') hcv⟩

/-- The same-type beta consumer of `TypedRowsWf`. Only `piRow` is read;
the well-formed context supplies that field's context premise. -/
theorem step_beta_srT_of_typedRowsWf {E : ResolvedEnv}
    (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A0 body arg S : Expr Nat}
    (h : HasTyT E n Γ (.app (.lam A0 body) arg) S) :
    Nonempty (HasTyT E n Γ (instantiate0 arg body) S) :=
  step_beta_srT_of_piChain
    (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
    (hrows.piRow hΓ) h

/-- Compatibility with the existential result of the existing Step
subject-reduction consumers. The same-type theorem permits `B = S`,
with a reflexive residual type chain. -/
theorem step_beta_srT_exists_of_typedRowsWf {E : ResolvedEnv}
    (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A0 body arg S : Expr Nat}
    (h : HasTyT E n Γ (.app (.lam A0 body) arg) S) :
    Nonempty (Σ' (B : Expr Nat),
      HasTyT E n Γ (instantiate0 arg body) B ×' TyConvT E n Γ S B) := by
  obtain ⟨hr⟩ := step_beta_srT_of_typedRowsWf hW hrows hΓ h
  exact ⟨S, hr, .refl Γ S⟩

/-! ## A non-reflexive conversion fixture in the empty environment -/

private def betaPiChainPinDomain : Expr Nat := .sort (.succ .zero)

private def betaPiChainPinDomain' : Expr Nat :=
  .sort (.max (.succ .zero) .zero)

/-- A beta expansion of `Sort 1`, used as the application's codomain. -/
private def betaPiChainPinCodomain : Expr Nat :=
  .app (.lam (.sort (.succ (.succ .zero))) (.bvar 0))
    (.sort (.succ .zero))

private def betaPiChainPinRedex : Expr Nat :=
  .app (.lam betaPiChainPinDomain (.bvar 0)) (.sort .zero)

/-- Both the function's Pi type and the application's final type are
converted. The function's domain changes by nonliteral level equality;
its codomain changes to a beta expansion of the original codomain. -/
private def betaPiChainPinTyping :
    HasTyT emptyEnv 0 [] betaPiChainPinRedex betaPiChainPinDomain' := by
  have hA : HasTyT emptyEnv 0 [] betaPiChainPinDomain
      (.sort (.succ (.succ .zero))) := .sort [] (.succ .zero)
  have hdom : ConvT emptyEnv 0 [] betaPiChainPinDomain betaPiChainPinDomain'
      (.sort (.succ (.succ .zero))) :=
    .sorts [] (.succ .zero) (.max (.succ .zero) .zero) (fun _ => rfl)
  have hbeta (Δ : LCtx) :
      ConvT emptyEnv 0 Δ betaPiChainPinCodomain betaPiChainPinDomain
        (.sort (.succ (.succ .zero))) :=
    .beta Δ (.sort (.succ (.succ .zero))) (.bvar 0)
      betaPiChainPinDomain (.sort (.succ (.succ .zero)))
      (.succ (.succ (.succ .zero)))
      (.sort Δ (.succ (.succ .zero))) (.bvar _ 0 _ rfl)
      (.sort Δ (.succ .zero))
  have hb : HasTyT emptyEnv 0 [.assumption betaPiChainPinDomain]
      (.bvar 0) betaPiChainPinDomain := .bvar _ 0 _ rfl
  have hlam : HasTyT emptyEnv 0 [] (.lam betaPiChainPinDomain (.bvar 0))
      (.pi betaPiChainPinDomain betaPiChainPinDomain) :=
    .lam [] betaPiChainPinDomain (.succ (.succ .zero)) (.bvar 0)
      betaPiChainPinDomain hA hb
  have hpi : ConvT emptyEnv 0 []
      (.pi betaPiChainPinDomain betaPiChainPinDomain)
      (.pi betaPiChainPinDomain' betaPiChainPinCodomain)
      (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
    .pi [] betaPiChainPinDomain betaPiChainPinDomain'
      betaPiChainPinDomain betaPiChainPinCodomain
      (.succ (.succ .zero)) (.succ (.succ .zero)) hdom
      (.symm _ _ _ _ (hbeta [.assumption betaPiChainPinDomain]))
  have hf : HasTyT emptyEnv 0 [] (.lam betaPiChainPinDomain (.bvar 0))
      (.pi betaPiChainPinDomain' betaPiChainPinCodomain) :=
    .conv [] _ _ _ (.imax (.succ (.succ .zero)) (.succ (.succ .zero))) hlam hpi
  have ha : HasTyT emptyEnv 0 [] (.sort .zero) betaPiChainPinDomain' :=
    .conv [] _ _ _ (.succ (.succ .zero)) (.sort [] .zero) hdom
  have happ : HasTyT emptyEnv 0 [] betaPiChainPinRedex betaPiChainPinCodomain :=
    .app [] (.lam betaPiChainPinDomain (.bvar 0)) (.sort .zero)
      betaPiChainPinDomain' betaPiChainPinCodomain hf ha
  exact .conv [] _ _ _ (.succ (.succ .zero)) happ
    (.trans [] betaPiChainPinCodomain betaPiChainPinDomain betaPiChainPinDomain'
      (.sort (.succ (.succ .zero))) (hbeta []) hdom)

/-- A real beta step consumes the existing empty-environment row
supplier. Its redex typing contains a converted Pi type and an outer
type conversion; the reduct keeps that exact final type. This pin
uses `empty.ScopeCheck = True`, not a row supplied as a hypothesis. -/
theorem pin_step_beta_piChain_empty :
    Nonempty (HasTyT emptyEnv 0 []
      (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
      (.sort (.max (.succ .zero) .zero))) ∧
    (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero) : Expr Nat)
      ≠ .sort .zero ∧
    Nonempty (HasTyT emptyEnv 0 [] (.sort .zero)
      (.sort (.max (.succ .zero) .zero))) := by
  refine ⟨⟨betaPiChainPinTyping⟩, ?_, ?_⟩
  · intro h
    cases h
  · have hrows : TypedRowsWf emptyEnv 0 :=
      typedRowsWf_of_scopeCheck EnvWfT.empty (by trivial) 0
    exact step_beta_srT_of_typedRowsWf EnvWfT.empty hrows CtxWfT.nil
      betaPiChainPinTyping

end Rcic.Declarative

#print axioms Rcic.Declarative.step_beta_srT_of_piChain
#print axioms Rcic.Declarative.step_beta_srT_of_typedRowsWf
#print axioms Rcic.Declarative.step_beta_srT_exists_of_typedRowsWf
#print axioms Rcic.Declarative.pin_step_beta_piChain_empty
