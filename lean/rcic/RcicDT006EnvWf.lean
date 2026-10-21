import rcic.RcicDTMetaTypedLiftSubst
import rcic.RcicTypedSubstLet

namespace Rcic.Declarative

/-!
# DT-006 at `EnvWfT` — the `InScope` premise discharged

`DT006T_let_substitution_preserves` (RcicDTMetaTypedLiftSubst.lean:60) is
sealed but pays the row only through `hW.InScope` — it reads the right
endpoint off `DT009T_endpoints_inScope`. #6329 landed the L1 let-binding
substitution, `hasTyT_substLet0_of_envWfT`, which discharges the same
statement directly at `EnvWfT`: `cases hΓ` yields the value's typing `hv`,
exactly the premise the L1 lemma wants.

The sealed row is untouched — this module adds the `EnvWfT`-only
restatement BESIDE it, per the counterpart convention. `closure_claim = 0`.
-/

/-- DT-006 at `EnvWfT`: let substitution preserves typing, no `InScope`.
    Same statement as `DT006T_let_substitution_preserves` with the scope
    premise dropped; the let cell's `CtxWfT` still supplies `hv`. -/
theorem DT006T_let_substitution_preserves_of_envWfT {E : ResolvedEnv}
    (hW : EnvWfT E) {n : Nat} {Γ : LCtx} {A v B e : Expr Nat}
    (hΓ : CtxWfT E n (LocalDecl.letBinding A v :: Γ))
    (he : HasTyT E n (LocalDecl.letBinding A v :: Γ) e B) :
    Nonempty (HasTyT E n Γ (instantiate0 v e) (instantiate0 v B)) := by
  cases hΓ with
  | letBinding _ _ _ _ _ hA hv =>
      exact ⟨hasTyT_substLet0_of_envWfT hW he hv⟩

/-- PIN: consumed at `listEnvUT` — `Sort 0`'s `bvar 0` under a
    `letBinding (Sort 1) (Sort 0)` head, instantiated, still typeable
    with no `InScope` anywhere. -/
theorem pin_DT006T_envWfT_listU {n : Nat} :
    Nonempty (HasTyT listEnvUT n []
      (instantiate0 (.sort .zero) (.bvar 0))
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  DT006T_let_substitution_preserves_of_envWfT listEnvUWfT
    (CtxWfT.letBinding [] (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort .zero) CtxWfT.nil (HasTyT.sort [] (.succ .zero))
      (HasTyT.sort [] .zero))
    (HasTyT.bvar [LocalDecl.letBinding (.sort (.succ .zero)) (.sort .zero)] 0
      (.sort (.succ .zero)) rfl)

#print axioms Rcic.Declarative.DT006T_let_substitution_preserves_of_envWfT
#print axioms Rcic.Declarative.pin_DT006T_envWfT_listU

end Rcic.Declarative
