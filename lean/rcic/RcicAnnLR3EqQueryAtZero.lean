import rcic.RcicAnnLR3EqPropKey
import rcic.RcicAnnLR3Core

/-!
# The Eq proposition key and a concrete height-zero interpretation

This is a positive control for the minimal-query measurement. The actual
proposition `Eq Prop parameter parameter` at the recorded irrelevance node
has both a supplied relational key and an actual LR3 interpretation at
`Sort 0`, at every ambient height including zero. The proof constructs the
family's proposition structure from its declared telescope. It uses neither
an environment-semantics premise nor a lower-height interpretation of an
index. The enclosing inhabited K frame is the existing guard fixture.

The final bundle links a supplied key to an original `irr` premise of the
actual guard proof. Separately it supplies the semantic interpretation of
the concrete proposition `domain`; it does not identify the existentially
selected proposition with `domain`. No uniform key theorem for arbitrary
conversion derivations or generated sort/Π query is claimed.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3.EqQueryAtZero

open Rcic.Declarative EqLargeFixture

private abbrev H : HeadLayerA3 env (iotaIfaceA env) 0 :=
  contextualHeadLayerA3 env (iotaIfaceA env) 0

private theorem familyIotaNone {e : ExprA}
    (he : (appsSpineA e).1 = .const 63 []) : (iotaIfaceA env).fn e = none := by
  apply iotaFn_none_of_below (iotaFnA_recHead env) he (m := fam) rfl
  intro r ls m hh hm hc
  have hr : (63 : Nat) = r := (ExprA.const.inj (he.symm.trans hh)).1
  subst r
  cases hm
  cases hc

/-- The Eq family head is normal without inspecting its index arguments. -/
theorem eqAtNormalA3 (Γ : LCtxA) (a b : ExprA) : H.normal Γ (eqAt a b) := by
  exact .neutral (.appIdle
    (.appIdle
      (.appIdle (.rigid 63 [] fam rfl rfl) (.noGroup rfl rfl) rfl (familyIotaNone rfl) rfl)
      (.noGroup rfl rfl) rfl (familyIotaNone rfl) rfl)
    (.noGroup rfl rfl) rfl (familyIotaNone rfl) rfl)

private theorem domainWhTy {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    WhTyA3 env (iotaIfaceA env) 0 H Γ domain domain :=
  whTyA3_of_hasTy (eqTyped hΓ parameterTyped parameterTyped)
    (eqAtNormalA3 Γ parameter parameter)

/-- All three arguments are compared at the stored family telescope. -/
theorem domainArgumentsSelfA3 (Γ : LCtxA) :
    ConvArgsA env (iotaIfaceA env) 0 Γ famTy
      [.sort .zero, parameter, parameter] [.sort .zero, parameter, parameter] := by
  refine .cons _ _ _ _ _ _ _ _ ⟨.refl Γ _ _ (.sort Γ .zero)⟩ ?_
  refine .cons _ _ _ _ _ _ _ _ ⟨.refl Γ _ _ parameterTyped⟩ ?_
  exact .cons _ _ _ _ _ _ _ _ ⟨.refl Γ _ _ parameterTyped⟩ (.nil _)

/-- The proposition-structure datum is constructed, not inferred from a row. -/
theorem domainPropEqA3 {Γ : LCtxA}
    (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    PropEqA3 env (iotaIfaceA env) 0 H Γ domain domain := by
  refine .fam (r := 63) (ls := []) (ls' := [])
    (xs := [.sort .zero, parameter, parameter])
    (xs' := [.sort .zero, parameter, parameter]) (m := fam)
    (domainWhTy hΓ) (domainWhTy hΓ)
    (eqAtNormalA3 Γ parameter parameter) (eqAtNormalA3 Γ parameter parameter)
    rfl rfl (eqNList_refl []) ?_ ⟨.refl Γ domain⟩
  intro lsX hlX
  rw [eqNList_nil_left hlX.1]
  exact parConvA_refl (domainArgumentsSelfA3 Γ)

/-- The proposition queried by the actual irr node has a complete LR3
term relation at the proposition universe, even at ambient height zero. -/
theorem domainRelatedAtAnyHeightA3 (ρ₀ : Nat → Nat) (k : Nat)
    {Γ : LCtxA} (hΓ : CtxWfA env (iotaIfaceA env) 0 Γ) :
    LRRelA3 env (iotaIfaceA env) 0 H ρ₀ k Γ (.sort .zero) domain domain := by
  have hv : PropValidA3 env (iotaIfaceA env) 0 H Γ domain :=
    ⟨domain, domainWhTy hΓ, eqAtNormalA3 Γ parameter parameter,
      .inl (EqPropKey.eqAtIsPropTyA3 H Γ parameter parameter)⟩
  have ht := eqTyped hΓ parameterTyped parameterTyped
  let R : ExprA → ExprA → Prop := fun a b =>
    PropValidA3 env (iotaIfaceA env) 0 H Γ a ∧
    PropValidA3 env (iotaIfaceA env) 0 H Γ b ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ a (.sort .zero)) ∧
    Nonempty (HasTyA env (iotaIfaceA env) 0 Γ b (.sort .zero)) ∧
    Nonempty (ConvA env (iotaIfaceA env) 0 Γ a b (.sort .zero)) ∧
    PropEqA3 env (iotaIfaceA env) 0 H Γ a b
  refine ⟨R, ?_, ?_⟩
  · rw [LRTyA3_eq]
    exact .sortP (whTyA3_sort Γ .zero) rfl
  · exact ⟨hv, hv, ⟨ht⟩, ⟨ht⟩, ⟨.refl Γ domain (.sort .zero) ht⟩,
      domainPropEqA3 hΓ⟩

/-- The actual guard contains an original, positively keyed `irr` premise.
The concrete Eq proposition also has its relation at height zero. The
selected proposition is not asserted equal to this separate `domain`. -/
theorem inhabitedEqKeyAndZeroRelationA3 (ρ₀ : Nat → Nat) :
    Nonempty (EnvWfA (iotaIfaceA env) env) ∧
    Nonempty (CtxWfA env (iotaIfaceA env) 0 context) ∧
    (∃ hg : ConvA env (iotaIfaceA env) 0 context parameter
        GuardHeightBoundary.actualIndex (.sort .zero),
      GuardHeightBoundary.UsesEqCarrierIrr (.sort .zero) hg ∧
      Nonempty (KStage.Frame env (iotaIfaceA env) 0 context
        GuardHeightBoundary.outerShape) ∧
      ∃ (Δ : LCtxA) (P : ExprA)
        (hP : HasTyA env (iotaIfaceA env) 0 Δ P (.sort .zero)),
        EqPropKey.EqIrrSelectedA3 hP hg ∧
        (∃ x y : ExprA, P = eqAt x y) ∧
        IsPropTyA3 env (iotaIfaceA env) 0 H Δ P) ∧
    LRRelA3 env (iotaIfaceA env) 0 H ρ₀ 0 context (.sort .zero) domain domain ∧
    IsPropTyA3 env (iotaIfaceA env) 0 H context domain ∧
    ht ρ₀ .zero < ht ρ₀ one :=
  ⟨wf, ⟨contextWf⟩, EqPropKey.actualGuardHasKeyedOccurrenceA3 H,
    domainRelatedAtAnyHeightA3 ρ₀ 0 contextWf,
    EqPropKey.eqAtIsPropTyA3 H context parameter parameter, Nat.zero_lt_succ 0⟩

#print axioms eqAtNormalA3
#print axioms domainArgumentsSelfA3
#print axioms domainPropEqA3
#print axioms domainRelatedAtAnyHeightA3
#print axioms inhabitedEqKeyAndZeroRelationA3

end Rcic.Declarative.Ann.LR3.EqQueryAtZero
