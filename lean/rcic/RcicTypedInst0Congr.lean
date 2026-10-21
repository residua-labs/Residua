import rcic.RcicDeclarative

/-!
# DT-009 L2 — premise-based `instantiate0` conversion congruences

The two-replacement congruence the `app`/`letE` arms of the DT-009 endpoint
package need, in the only shape they need it: at a `sort` index.

The detour is the one `convTInst0ValueSort`
(`RcicParRedSRTyped.lean:275`) already uses: under a binder, an
`instantiate0` of a sort-typed body unfolds through β (or ζ for the
let-binding variant) so the value conversion can be applied at the rule
level:

    inst0 v body  ≈(β⁻¹)  app (lam A body) v  ≈(app-cong)  app (lam A body) v'
                  ≈(β)    inst0 v' body

The SRTyped original derives the two endpoint typings `v : A` / `v' : A`
from `DT009T_endpoints_inScope` (scope-gated). Here they are premises —
no `InScope`, no `EnvWfT`, no semantic bridge; the lemma is a pure
judgment-level term and stays available inside the DT-009 mutual where
the endpoints come from the induction hypotheses instead.
-/

namespace Rcic.Declarative

/-- the assumption-binder form: `instantiate0 v body ≈ instantiate0 v' body`
    at `sort w`, given the body's under-binder sort-typing, both endpoint
    typings and the value conversion. -/
def convT_inst0_sortCongr {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body v v' : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (LocalDecl.assumption A :: Γ) body (.sort w))
    (hv : HasTyT E n Γ v A) (hv' : HasTyT E n Γ v' A)
    (hc : ConvT E n Γ v v' A) :
    ConvT E n Γ (instantiate0 v body) (instantiate0 v' body) (.sort w) := by
  have l1 : ConvT E n Γ (instantiate0 v body) (.app (.lam A body) v) (.sort w) :=
    .symm _ _ _ _ (.beta _ A body v (.sort w) u hA hbody hv)
  have l2 : ConvT E n Γ (.app (.lam A body) v) (.app (.lam A body) v')
      (.sort w) :=
    .app _ _ _ _ _ _ _
      (.lam _ _ _ _ _ _ _
        (.refl _ _ _ hA) (.refl _ _ _ hbody))
      hc
  have l3 : ConvT E n Γ (.app (.lam A body) v') (instantiate0 v' body)
      (.sort w) :=
    .beta _ A body v' (.sort w) u hA hbody hv'
  exact .trans _ _ _ _ _ l1 (.trans _ _ _ _ _ l2 l3)

/-- the letBinding-binder form: same congruence, ζ-detour instead of β.
    `hB`/`hB'` are the body's sort-typings under the left and right bound
    values (the caller supplies both; moving `B` between let-bound values
    is the ctx transport `convTConvLetAt`, kept out of this lemma). -/
def convT_inst0_sortCongrLet {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A B v v' : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (LocalDecl.letBinding A v :: Γ) B (.sort w))
    (hB' : HasTyT E n (LocalDecl.letBinding A v' :: Γ) B (.sort w))
    (hv : HasTyT E n Γ v A) (hv' : HasTyT E n Γ v' A)
    (hc : ConvT E n Γ v v' A) :
    ConvT E n Γ (instantiate0 v B) (instantiate0 v' B) (.sort w) := by
  have l1 : ConvT E n Γ (instantiate0 v B) (.letE A v B) (.sort w) :=
    .symm _ _ _ _ (.zeta _ A v B (.sort w) u hA hv hB)
  have l2 : ConvT E n Γ (.letE A v B) (.letE A v' B) (.sort w) :=
    .letE _ _ _ _ _ _ _ _ u
      (.refl _ _ _ hA) hc (.refl _ _ _ hB)
  have l3 : ConvT E n Γ (.letE A v' B) (instantiate0 v' B) (.sort w) :=
    .zeta _ A v' B (.sort w) u hA hv' hB'
  exact .trans _ _ _ _ _ l1 (.trans _ _ _ _ _ l2 l3)

end Rcic.Declarative
