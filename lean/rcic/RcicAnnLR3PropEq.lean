import rcic.RcicAnnLR3Sort
import rcic.RcicAnnFamWk

/-!
# LR3 proposition structure and shape predicates

These are the head-dependent definition seeds below the logical-relation
tower. Their explicit certified `HeadLayerA3` parameter supplies positive
normality and the weak-head relation; the proposition key is relational
`IsPropTyA3` for that same layer. The syntactic
shape test, typed conversion and dependent parameter walks are shared.

`PropEqA3` preserves the landed structural proposition datum: products carry
domain conversion and codomain structure in every admissible world/binder;
families carry a two-sided declared-telescope walk; stuck types carry the
same shape exclusion. This module asserts no new PER or fundamental theorem.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- An LR3-normal type with no sort, product or declared-family head. -/
def StuckA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (N : ExprA) : Prop :=
  H.normal Γ N ∧ ¬ isShapeHeadA E (appsSpineA N).1

/-- The proposition/stuck shape used by the height-free proposition clause. -/
def TripleLikeA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (N : ExprA) : Prop :=
  H.normal Γ N ∧
    (IsPropTyA3 E I n H Γ N ∨ ¬ isShapeHeadA E (appsSpineA N).1)

/-- The structure of two propositions, using LR3 weak-head witnesses. -/
inductive PropEqA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) : LCtxA → ExprA → ExprA → Prop
  | pi {Γ : LCtxA} {a b D C D' C' : ExprA} {u v u' v' : Level}
      (ha : WhTyA3 E I n H Γ a (.pi D u C v)) (hb : WhTyA3 E I n H Γ b (.pi D' u' C' v'))
      (hu : eqN u u') (hv : eqN v v')
      (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
      (hD'ty : Nonempty (HasTyA E I n Γ D' (.sort u')))
      (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        Nonempty (TyConvA E I n (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D')))
      (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ D₀ : ExprA,
        Nonempty (CtxWfA E I n (.assumption D₀ :: wkCtxA ρ Γ)) →
        Nonempty (TyConvA E I n (wkCtxA ρ Γ) D₀ (wkExprA ρ D)) →
        PropEqA3 E I n H (.assumption D₀ :: wkCtxA ρ Γ)
          (wkExprA (WkSpecA.ub ρ) C) (wkExprA (WkSpecA.ub ρ) C'))
      (hc : Nonempty (TyConvA E I n Γ a b)) : PropEqA3 E I n H Γ a b
  | fam {Γ : LCtxA} {a b : ExprA} {r : Nat} {ls ls' : List Level} {xs xs' : List ExprA}
      {m : CheckedMemberA}
      (ha : WhTyA3 E I n H Γ a (foldAppsA (.const r ls) xs))
      (hb : WhTyA3 E I n H Γ b (foldAppsA (.const r ls') xs'))
      (hna : H.normal Γ (foldAppsA (.const r ls) xs))
      (hnb : H.normal Γ (foldAppsA (.const r ls') xs'))
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hls : eqNList ls ls')
      (hargs : ∀ lsX : List Level, eqNListB n ls lsX →
        ParConvA E I n Γ (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA) xs xs')
      (hc : Nonempty (TyConvA E I n Γ a b)) : PropEqA3 E I n H Γ a b
  | stuck {Γ : LCtxA} {a b N N' : ExprA}
      (ha : WhTyA3 E I n H Γ a N) (hb : WhTyA3 E I n H Γ b N')
      (hN : StuckA3 E I n H Γ N) (hN' : StuckA3 E I n H Γ N')
      (hc : Nonempty (TyConvA E I n Γ a b)) : PropEqA3 E I n H Γ a b

#print axioms StuckA3
#print axioms TripleLikeA3
#print axioms PropEqA3

end Rcic.Declarative.Ann.LR3
