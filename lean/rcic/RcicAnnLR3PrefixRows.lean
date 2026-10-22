import rcic.RcicAnnLR3PrefixQueryBoundary

/-!
# The Eq constructor prefix really supplies its own old rows

The environment below the Eq recursor has an inhabited semantic environment
for the landed logical relation. Its family has result sort zero, so the
small-index condition's positive-sort antecedent is impossible. Its recursor
profile is vacuous because no recursor has been admitted yet.

This settles the supply side of a possible prefix argument. The rows apply
to derivations *in that prefix*. They do not restrict a full-environment
derivation or normalize its generated Pi queries. The companion module
exhibits a genuine full-environment query with no unchanged prefix instance.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.PrefixRows

open Rcic.Declarative EqLargeFixture PrefixQuery

/-- The prefix has no recursor, so its own concrete interface agrees with no-iota. -/
theorem prefixLocalIfaceA3 : IfaceAgreeA prefixEnv noIotaA (iotaIfaceA prefixEnv) := by
  intro e _
  cases h : iotaFnA prefixEnv e with
  | none => exact h.symm
  | some e' =>
      obtain ⟨r, ls, m, _, hm, hc, _⟩ := iotaFnA_recHead prefixEnv e e' h
      exact False.elim (prefix_noRec r m hm hc)

/-- Actual prefix admission at the interface required by the landed row theorem. -/
def prefixConcreteWfA3 : EnvWfA (iotaIfaceA prefixEnv) prefixEnv :=
  .group emptyEnvA 63 fam famSort .empty rfl rfl (fun _ => rfl)
    famTyTyped rfl famView
    [reflGroup (iotaIfaceA prefixEnv)
      (hasTyIfaceA (prefixLocalIfaceA3.prefix fam_in_prefix) reflTyTyped)]
    ⟨rfl, rfl⟩

/-- Only positive-result families trigger the old small-index inequality. -/
theorem prefixSmallIndexA3 : SmallIndexProfileA prefixEnv := by
  intro r m u hm hind hbody v hv ρ x y hx hy hy0
  by_cases h64 : r = 64
  · subst r
    cases hm
    cases hind
  · by_cases h63 : r = 63
    · subst r
      cases hm
      change ExprA.sort .zero = .sort u at hbody
      cases hbody
      change some 0 = some y at hy
      cases hy
      omega
    · simp [prefixEnv, famEnv, extendEnvA, emptyEnvA, h64, h63] at hm

/-- There is no prefix recursor on which the elimination profile could fail. -/
theorem prefixPropElimA3 : PropElimStructA prefixEnv := by
  intro r rm D f ls fm u hr hc
  exact False.elim (prefix_noRec r rm hr hc)

/-- A semantic-environment supply, with neither an EnvSem premise nor full-env rows. -/
theorem prefixEnvSemA3 (n : Nat) (ρ₀ : Nat → Nat) (hρ : PosValA ρ₀) :
    EnvSemA prefixEnv (iotaIfaceA prefixEnv) n ρ₀ :=
  envSemA_of_envWfA_recStruct prefixConcreteWfA3 hρ prefixSmallIndexA3 prefixPropElimA3

/-- Type agreement is therefore available for arbitrary prefix derivations. -/
theorem prefixTypeAgreementA3 {n : Nat} {Γ : LCtxA}
    (hΓ : CtxWfA prefixEnv (iotaIfaceA prefixEnv) n Γ) {e A B : ExprA}
    (hA : HasTyA prefixEnv (iotaIfaceA prefixEnv) n Γ e A)
    (hB : HasTyA prefixEnv (iotaIfaceA prefixEnv) n Γ e B) :
    Nonempty (TyConvA prefixEnv (iotaIfaceA prefixEnv) n Γ A B) :=
  hasTyA_uniq_rec prefixConcreteWfA3 prefixSmallIndexA3 prefixPropElimA3 hΓ hA hB

/-- The sort row needed by the prefix type-agreement proof is also supplied. -/
theorem prefixSortUniquenessA3 {n : Nat} {Γ : LCtxA}
    (hΓ : CtxWfA prefixEnv (iotaIfaceA prefixEnv) n Γ) {e : ExprA} {u v : Level}
    (hu : HasTyA prefixEnv (iotaIfaceA prefixEnv) n Γ e (.sort u))
    (hv : HasTyA prefixEnv (iotaIfaceA prefixEnv) n Γ e (.sort v)) : eqN u v :=
  sortUniqA_rec prefixConcreteWfA3 prefixSmallIndexA3 prefixPropElimA3 hΓ hu hv

#print axioms prefixLocalIfaceA3
#print axioms prefixConcreteWfA3
#print axioms prefixSmallIndexA3
#print axioms prefixPropElimA3
#print axioms prefixEnvSemA3
#print axioms prefixTypeAgreementA3
#print axioms prefixSortUniquenessA3

end Rcic.Declarative.Ann.LR3.PrefixRows
