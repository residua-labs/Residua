import rcic.RcicAnnLR3Core
import rcic.RcicAnnLR3FamilyKey
import rcic.RcicRouteCIndexFamilyFragment

/-!
# An actual LR3 semantic supplier for the large-index family

The admitted environment `pinFamFEnvA 0` has one family and no constructors.
The declarations below construct its interpretation in the landed LR3
tower, including the full Pi action in every admissible world. They use
typed conversion at the declared index telescope, never semantic validity
at the index's height. Constructor-field obligations are discharged by the
environment's inhabited empty constructor signature.

The final member theorem has the exact semantic-environment quantifiers and
concludes `LRRelA3` itself. It can therefore be composed with the scaffold's
environment name without a new bridge or a second logical relation.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

private abbrev pinE3 : ResolvedEnvA := pinFamFEnvA 0
private abbrev pinH3 (n : Nat) : HeadLayerA3 pinE3 noIotaA n :=
  contextualHeadLayerA3 pinE3 noIotaA n

/-- Family applications are positively normal for every index, including
indices that themselves reduce. The family head does not inspect them. -/
theorem pinFamilyNormalA3 (n : Nat) (Γ : LCtxA) (a : ExprA) :
    (contextualHeadLayerA3 (pinFamFEnvA 0) noIotaA n).normal Γ
      (.app (.const 0 []) a) := by
  exact .neutral (.appIdle
    (.rigid 0 [] (pinFamFA 0) (pinFamF_members 0) rfl)
    (.noGroup rfl rfl) rfl rfl rfl)

/-- The structural term carrier of the family, retaining LR3 reduction and
positive normality even though this environment has no constructors. -/
def PinFamilyCarrierA3 (n : Nat) (Γ : LCtxA) (A : ExprA) : ExprA → ExprA → Prop :=
  LfpWA (FamPhiWA3 (pinFamFEnvA 0) noIotaA n
    (contextualHeadLayerA3 (pinFamFEnvA 0) noIotaA n) Γ 0 (pinFamFA 0)
    RouteCIndex.emptyFieldRelsA RouteCIndex.emptyInnerRelsA) [] A

/-- Family formation in the actual new tower, at every carrier height and
for arbitrary lower-height interpretations. -/
theorem pinFamilyTyA3 {n k : Nat} (ρ₀ : Nat → Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) {Γ : LCtxA} {a : ExprA}
    (hΓ : CtxWfA (pinFamFEnvA 0) noIotaA n Γ)
    (ha : HasTyA (pinFamFEnvA 0) noIotaA n Γ a (.sort (.succ .zero))) :
    TyKA3 (pinFamFEnvA 0) noIotaA n
      (contextualHeadLayerA3 (pinFamFEnvA 0) noIotaA n) ρ₀ k LE LT Γ
      (.app (.const 0 []) a) (PinFamilyCarrierA3 n Γ (.app (.const 0 []) a)) := by
  have hn := pinFamilyNormalA3 n Γ a
  have hnp := not_isPropTyA3_of_sort (pinH3 n)
    (pinFamF0_sortOf_indexA3 n (pinH3 n) hΓ (.refl _ _ _ ha)) rfl
  refine .fam (r := 0) (ls := []) (ps := []) (is := [a]) (m := pinFamFA 0)
    (u := .succ .zero) (u₀ := .succ .zero)
    (whTyA3_of_hasTy (RouteCIndex.pinAppTy ha) hn) hn hnp
    (pinFamF_members 0) rfl rfl rfl rfl rfl
    RouteCIndex.emptyFieldRelsA RouteCIndex.emptyInnerRelsA
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try
    intros
    exact (RouteCIndex.pin_noCtor _ _ (by assumption) (by assumption) (by assumption)).elim
  · intro ρ _
    exact RouteCIndex.pin_indexDomains n (wkCtxA ρ Γ)
  · intro TF hTF
    cases hTF
    refine .cons _ _ _ _ _ _ _ _ _ _ ?_ (.nil _ _ _)
    exact ⟨.sort (.succ .zero), .succ (.succ .zero), .sort (.succ .zero),
      .succ (.succ .zero), rfl, ⟨.refl _ _ _ ha⟩⟩

/-- Convertible indices supply family equality in the actual new tower.
The cross-parameter obligations specialize to the empty parameter prefix. -/
theorem pinFamilyEqA3 {n k : Nat} (ρ₀ : Nat → Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) {Γ : LCtxA} {a b : ExprA}
    (ha : HasTyA (pinFamFEnvA 0) noIotaA n Γ a (.sort (.succ .zero)))
    (hb : HasTyA (pinFamFEnvA 0) noIotaA n Γ b (.sort (.succ .zero)))
    (hab : ConvA (pinFamFEnvA 0) noIotaA n Γ a b (.sort (.succ .zero))) :
    EqKA3 (pinFamFEnvA 0) noIotaA n
      (contextualHeadLayerA3 (pinFamFEnvA 0) noIotaA n) ρ₀ k LE LT Γ
      (.app (.const 0 []) a) (.app (.const 0 []) b) := by
  have hn := pinFamilyNormalA3 n Γ a
  have hn' := pinFamilyNormalA3 n Γ b
  have hc : ConvA pinE3 noIotaA n Γ (.app (.const 0 []) a)
      (.app (.const 0 []) b) (.sort (.succ .zero)) :=
    .app Γ _ _ _ _ _ _ _ _ (.refl _ _ _ (pinFamFConstTy (pinFamF_members 0) n Γ))
      hab (.sort _ (.succ .zero)) (RouteCIndex.pinAppTy hb)
  have ht : Nonempty (TyConvA pinE3 noIotaA n Γ
      (.app (.const 0 []) a) (.app (.const 0 []) b)) :=
    ⟨.of Γ _ _ (.succ .zero) (.succ .zero) (.succ .zero)
      (RouteCIndex.pinAppTy ha) (eqNA_refl _) (RouteCIndex.pinAppTy hb) (eqNA_refl _) hc⟩
  refine .fam (r := 0) (ls := []) (ls' := []) (ps := []) (ps' := [])
    (is := [a]) (is' := [b]) (m := pinFamFA 0) (u₀ := .succ .zero)
    (whTyA3_of_hasTy (RouteCIndex.pinAppTy ha) hn)
    (whTyA3_of_hasTy (RouteCIndex.pinAppTy hb) hn') hn hn'
    (pinFamF_members 0) rfl rfl trivial rfl rfl
    RouteCIndex.emptyFieldRelsA RouteCIndex.emptyInnerRelsA
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try
    intros
    exact (RouteCIndex.pin_noCtor _ _ (by assumption) (by assumption) (by assumption)).elim
  · intro ρ _
    exact RouteCIndex.pin_indexDomains n (wkCtxA ρ Γ)
  · intro ρ _ lsF TF TF' pre pre' D uD C vC D' uD' C' vC' _ hTF hTF' _ hD hD'
    cases hTF
    cases hTF'
    obtain ⟨_, rfl⟩ := RouteCIndex.pin_index_domain hD
    obtain ⟨_, rfl⟩ := RouteCIndex.pin_index_domain hD'
    exact ⟨.refl _ _⟩
  · intro TF hTF
    cases hTF
    refine .cons _ _ _ _ _ _ _ _ _ _ ?_ (.nil _ _ _)
    exact ⟨.sort (.succ .zero), .succ (.succ .zero), .sort (.succ .zero),
      .succ (.succ .zero), rfl, ⟨hab⟩⟩
  · intro ρ _ lsX _
    exact .nil _ _

/-- The exact relation selected by LR3's Type-sort clause at `Sort 1`.
Its carrier height is `1`; index domains are still compared syntactically. -/
def PinFamilySortRelationA3 (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA)
    (a b : ExprA) : Prop :=
  LREqA3 pinE3 noIotaA n (pinH3 n) ρ₀ 1 Γ a b ∧
  (∃ R, LRTyA3 pinE3 noIotaA n (pinH3 n) ρ₀ 1 Γ a R) ∧
  (∃ R, LRTyA3 pinE3 noIotaA n (pinH3 n) ρ₀ 1 Γ b R) ∧
  Nonempty (HasTyA pinE3 noIotaA n Γ a (.sort (.succ .zero))) ∧
  Nonempty (HasTyA pinE3 noIotaA n Γ b (.sort (.succ .zero))) ∧
  Nonempty (ConvA pinE3 noIotaA n Γ a b (.sort (.succ .zero)))

/-- The precise sort relation is supplied at every ambient height above 1. -/
theorem pinFamilySortRelationA3_valid (n k : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA)
    (hk : 1 < k) :
    LRTyA3 pinE3 noIotaA n (pinH3 n) ρ₀ k Γ (.sort (.succ .zero))
      (PinFamilySortRelationA3 n ρ₀ Γ) := by
  rw [LRTyA3_eq]
  exact .sortT (whTyA3_sort Γ (.succ .zero)) rfl hk

/-- The actual sort relation relates `F a` and `F b` from typed index
conversion alone, with both structural family interpretations supplied. -/
theorem pinFamilyApplicationPairA3 {n : Nat} (ρ₀ : Nat → Nat) {Γ : LCtxA} {a b : ExprA}
    (hΓ : CtxWfA pinE3 noIotaA n Γ)
    (ha : HasTyA pinE3 noIotaA n Γ a (.sort (.succ .zero)))
    (hb : HasTyA pinE3 noIotaA n Γ b (.sort (.succ .zero)))
    (hab : ConvA pinE3 noIotaA n Γ a b (.sort (.succ .zero))) :
    PinFamilySortRelationA3 n ρ₀ Γ (.app (.const 0 []) a) (.app (.const 0 []) b) := by
  have hc : ConvA pinE3 noIotaA n Γ (.app (.const 0 []) a)
      (.app (.const 0 []) b) (.sort (.succ .zero)) :=
    .app Γ _ _ _ _ _ _ _ _ (.refl _ _ _ (pinFamFConstTy (pinFamF_members 0) n Γ))
      hab (.sort _ (.succ .zero)) (RouteCIndex.pinAppTy hb)
  refine ⟨?_, ⟨PinFamilyCarrierA3 n Γ (.app (.const 0 []) a), ?_⟩,
    ⟨PinFamilyCarrierA3 n Γ (.app (.const 0 []) b), ?_⟩,
    ⟨RouteCIndex.pinAppTy ha⟩, ⟨RouteCIndex.pinAppTy hb⟩, ⟨hc⟩⟩
  · rw [LREqA3_eq]
    exact pinFamilyEqA3 ρ₀ _ _ ha hb hab
  · rw [LRTyA3_eq]
    exact pinFamilyTyA3 ρ₀ _ _ hΓ ha
  · rw [LRTyA3_eq]
    exact pinFamilyTyA3 ρ₀ _ _ hΓ hb

/-- A complete LR3 application result, closing the formerly refuted
large-index sort relation rather than a separate family fragment. -/
theorem pinFamilyApplicationRelA3 {n k : Nat} (ρ₀ : Nat → Nat) {Γ : LCtxA} {a b : ExprA}
    (hk : 1 < k) (hΓ : CtxWfA pinE3 noIotaA n Γ)
    (ha : HasTyA pinE3 noIotaA n Γ a (.sort (.succ .zero)))
    (hb : HasTyA pinE3 noIotaA n Γ b (.sort (.succ .zero)))
    (hab : ConvA pinE3 noIotaA n Γ a b (.sort (.succ .zero))) :
    LRRelA3 pinE3 noIotaA n (pinH3 n) ρ₀ k Γ (.sort (.succ .zero))
      (.app (.const 0 []) a) (.app (.const 0 []) b) :=
  ⟨PinFamilySortRelationA3 n ρ₀ Γ,
    pinFamilySortRelationA3_valid n k ρ₀ Γ hk,
    pinFamilyApplicationPairA3 ρ₀ hΓ ha hb hab⟩

/-- The family constant is related to itself at its full dependent-function
type. The action is supplied in every admissible world. -/
theorem pinFamilyConstantRelA3 (n k : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA)
    (hk : 1 < k) :
    LRRelA3 pinE3 noIotaA n (pinH3 n) ρ₀ k Γ (pinFamFA 0).mtypeA
      (.const 0 []) (.const 0 []) := by
  let RD : WkSpecA → ExprA → ExprA → Prop :=
    fun ρ => PinFamilySortRelationA3 n ρ₀ (wkCtxA ρ Γ)
  let RC : WkSpecA → ExprA → ExprA → ExprA → Prop :=
    fun ρ _ => PinFamilySortRelationA3 n ρ₀ (wkCtxA ρ Γ)
  have hnp : ¬ IsPropTyA3 pinE3 noIotaA n (pinH3 n) Γ (pinFamFA 0).mtypeA := by
    intro hp
    have hz := (isPropTyA3_pi_iff pinE3 noIotaA n (pinH3 n) Γ
      (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort (.succ .zero)) (.succ (.succ .zero))).1 hp
    exact Bool.noConfusion hz
  let R : ExprA → ExprA → Prop := fun f g =>
    (∀ ρ : WkSpecA, WkOkA pinE3 noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
    Nonempty (HasTyA pinE3 noIotaA n Γ f (pinFamFA 0).mtypeA) ∧
    Nonempty (HasTyA pinE3 noIotaA n Γ g (pinFamFA 0).mtypeA) ∧
    Nonempty (ConvA pinE3 noIotaA n Γ f g (pinFamFA 0).mtypeA)
  refine ⟨R, ?_, ?_⟩
  · rw [LRTyA3_eq]
    refine .pi (whTyA3_of_hasTy (pinFamFTypeTy 0 pinE3 n Γ)
      ((pinH3 n).normal_pi Γ (.sort (.succ .zero)) (.succ (.succ .zero))
        (.sort (.succ .zero)) (.succ (.succ .zero)))) hnp
      ⟨.sort _ (.succ .zero)⟩ ⟨.sort _ (.succ .zero)⟩ RD ?_ RC ?_ ?_
    · intro ρ _
      simpa only [wkExprA_sort] using
        (show TyKA3 pinE3 noIotaA n (pinH3 n) ρ₀ k
          (fun j _ => LREqA3 pinE3 noIotaA n (pinH3 n) ρ₀ j)
          (fun j _ => LRTyA3 pinE3 noIotaA n (pinH3 n) ρ₀ j)
          (wkCtxA ρ Γ) (.sort (.succ .zero)) (RD ρ) from
            .sortT (whTyA3_sort _ (.succ .zero)) rfl hk)
    · intro ρ _ a a' _
      simpa only [wkExprA_sort] using
        (show TyKA3 pinE3 noIotaA n (pinH3 n) ρ₀ k
          (fun j _ => LREqA3 pinE3 noIotaA n (pinH3 n) ρ₀ j)
          (fun j _ => LRTyA3 pinE3 noIotaA n (pinH3 n) ρ₀ j)
          (wkCtxA ρ Γ) (.sort (.succ .zero)) (RC ρ a) from
            .sortT (whTyA3_sort _ (.succ .zero)) rfl hk)
    · intro ρ _ a a' _
      simpa only [wkExprA_sort] using
        (show EqKA3 pinE3 noIotaA n (pinH3 n) ρ₀ k
          (fun j _ => LREqA3 pinE3 noIotaA n (pinH3 n) ρ₀ j)
          (fun j _ => LRTyA3 pinE3 noIotaA n (pinH3 n) ρ₀ j)
          (wkCtxA ρ Γ) (.sort (.succ .zero)) (.sort (.succ .zero)) from
            .sort (whTyA3_sort _ (.succ .zero)) (whTyA3_sort _ (.succ .zero))
              hk (eqNA_refl _) ⟨.refl _ _⟩)
  · refine ⟨?_, ⟨pinFamFConstTy (pinFamF_members 0) n Γ⟩,
      ⟨pinFamFConstTy (pinFamF_members 0) n Γ⟩,
      ⟨.refl _ _ _ (pinFamFConstTy (pinFamF_members 0) n Γ)⟩⟩
    intro ρ hρ a b hab
    obtain ⟨hΔ⟩ := hρ.2
    obtain ⟨ha⟩ := hab.2.2.2.1
    obtain ⟨hb⟩ := hab.2.2.2.2.1
    obtain ⟨hc⟩ := hab.2.2.2.2.2
    simpa only [wkExprA_const] using pinFamilyApplicationPairA3 ρ₀ hΔ ha hb hc

/-- Every member of the admitted large-index environment satisfies the
exact LR3 environment contract, uniformly above the explicit bound 2. -/
theorem pinFamilyAllMembersA3 (n : Nat) (ρ₀ : Nat → Nat) :
    ∀ r m, (pinFamFEnvA 0).members r = some m → ∀ ls ls' : List Level,
      ls.length = m.arity → levelsBounded n ls = true → levelsBounded n ls' = true →
      eqNList ls ls' → ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA,
        Nonempty (CtxWfA (pinFamFEnvA 0) noIotaA n Δ) →
        LRRelA3 (pinFamFEnvA 0) noIotaA n
          (contextualHeadLayerA3 (pinFamFEnvA 0) noIotaA n) ρ₀ k Δ
          (instantiateLevelsA ls m.mtypeA) (.const r ls) (.const r ls') := by
  intro r m hm ls ls' hlen _ _ hls
  by_cases hr : r = 0
  · subst hr
    cases hm
    have hnil : ls = [] := list_nil_of_length_zero ls hlen
    subst hnil
    have hnil' : ls' = [] := eqNList_nil_left hls
    subst hnil'
    exact ⟨2, fun k hk Δ _ => pinFamilyConstantRelA3 n k ρ₀ Δ (by omega)⟩
  · simp [pinFamFEnvA, extendEnvA, emptyEnvA, hr] at hm

/-- The formerly refuted closed application is related in LR3, with the
environment and typing premises inhabited in the same theorem. -/
theorem pinFamilyPositiveBundleA3 (n : Nat) (ρ₀ : Nat → Nat) :
    Nonempty (EnvWfA noIotaA (pinFamFEnvA 0)) ∧
    Nonempty (CtxWfA (pinFamFEnvA 0) noIotaA n []) ∧
    Nonempty (HasTyA (pinFamFEnvA 0) noIotaA n [] pinFamFAppA (.sort (.succ .zero))) ∧
    LRRelA3 (pinFamFEnvA 0) noIotaA n
      (contextualHeadLayerA3 (pinFamFEnvA 0) noIotaA n) ρ₀ 2 []
      (.sort (.succ .zero)) pinFamFAppA pinFamFAppA := by
  refine ⟨⟨pinFamFEnvWfA 0 pinFamF0ViewA⟩, ⟨.nil⟩,
    ⟨pinFamFAppTy (pinFamF_members 0) n []⟩, ?_⟩
  exact pinFamilyApplicationRelA3 ρ₀ (by decide) .nil (.sort [] .zero) (.sort [] .zero)
    (.refl _ _ _ (.sort [] .zero))

#print axioms pinFamilyNormalA3
#print axioms PinFamilyCarrierA3
#print axioms pinFamilyTyA3
#print axioms pinFamilyEqA3
#print axioms PinFamilySortRelationA3
#print axioms pinFamilySortRelationA3_valid
#print axioms pinFamilyApplicationPairA3
#print axioms pinFamilyApplicationRelA3
#print axioms pinFamilyConstantRelA3
#print axioms pinFamilyAllMembersA3
#print axioms pinFamilyPositiveBundleA3

end Rcic.Declarative.Ann.LR3
