import rcic.RcicAnnLRWk

/-!
# M2-e (0) — the pi arm measured against the relation's heights: refuted on the
# M1-d (iv) heights (PR #6113), PASSED after R-PropOutOfTower (M1-d (vi))

Before the fundamental theorem is written, its `pi` arm is measured on the
smallest term that crosses the Prop boundary from the Type side:

    P := ∀ (X : Sort 1), ∀ (Q : Sort 0), Q → Q        (a proposition, impredicative)
    T := ∀ (p : P), Sort 0                            (: Sort 1)

The arm must relate `T` to itself as an element of `Sort (imax uP 1)`, i.e. in
the sort clause at height `k`, whose relation drops to `lvlIdx ρ₀ k (imax uP 1)
= ht (imax uP 1) = 1`: `LREqA 1 [] T T`. That is `EqKA.pi` at height 1, whose
domain datum `hDeq` is `EqKA 1 [] P P`; `P` is a pi over `Sort 1`, so its own
`hD` is `TyKA 1 [] (Sort 1) _`, whose only clause (`sort`) needs `ht 1 < 1`.
On the M1-d (iv) heights that was refuted at EVERY height `k`
(`piArm_height_refuted`, PR #6113: `P`'s structure lived at the moving top
`k − 1`, `T`'s sort height was the fixed `1`, and the two never met). After
R-PropOutOfTower (M1-d (vi)) the same term PASSES at every height above `T`'s
sort: `piArm_height_passes`. `P`'s equality as a domain is `EqKA.stuck` on its
triple-like normal form (a proposition, convertible to itself), available at
height 1; `P`'s validity is the prop clause; the codomain `Sort 0` is
`EqKA.sort`/`TyKA.sortP`. The prediction that could have failed and did not —
the fourth kind of evidence (`CLAUDE.md` §0). Records:
`research/rcic/rows-m1/README.md` M2-e (0) and M1-d (vi), `M2_PLAN.md`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## the terms -/

/-- `∀ (Q : Sort 0), Q → Q`, in the context `X : Sort 1`. -/
def qqA : ExprA :=
  .pi (.sort .zero) (.succ .zero) (.pi (.bvar 0) .zero (.bvar 1) .zero) (.imax .zero .zero)

/-- `P := ∀ (X : Sort 1), ∀ (Q : Sort 0), Q → Q`. -/
def impPropA : ExprA :=
  .pi (.sort (.succ .zero)) (.succ (.succ .zero)) qqA (.imax (.succ .zero) (.imax .zero .zero))

/-- `P`'s sort, `imax 2 (imax 1 (imax 0 0))`, `=ₙ 0`. -/
def impPropSort : Level := .imax (.succ (.succ .zero)) (.imax (.succ .zero) (.imax .zero .zero))

/-- `T := ∀ (p : P), Sort 0`. -/
def propDomPiA : ExprA := .pi impPropA impPropSort (.sort .zero) (.succ .zero)

/-- `T`'s sort, `imax uP 1`, of height 1 under every valuation. -/
def propDomPiSort : Level := .imax impPropSort (.succ .zero)

section Typings
variable (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)

def qqA_ty : HasTyA E I n [.assumption (.sort (.succ .zero))] qqA (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  .pi _ (.sort .zero) (.succ .zero) (.pi (.bvar 0) .zero (.bvar 1) .zero) (.imax .zero .zero)
    (.sort _ .zero)
    (.pi _ (.bvar 0) .zero (.bvar 1) .zero
      (.bvar _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ .zero))
      (.bvar _ 1 (.sort .zero) (.succ .zero) rfl (.sort _ .zero)))

def impPropA_ty : HasTyA E I n [] impPropA (.sort impPropSort) :=
  .pi [] (.sort (.succ .zero)) (.succ (.succ .zero)) qqA (.imax (.succ .zero) (.imax .zero .zero))
    (.sort [] (.succ .zero)) (qqA_ty E I n)

def propDomPiA_ty : HasTyA E I n [] propDomPiA (.sort propDomPiSort) :=
  .pi [] impPropA impPropSort (.sort .zero) (.succ .zero) (impPropA_ty E I n) (.sort _ .zero)

theorem impPropA_isProp : IsPropTy E I [] impPropA := by
  rw [impPropA, isPropTy_pi_iff]; rfl

end Typings

/-! ## the heights -/

theorem ht_propDomPiSort (ρ₀ : Nat → Nat) : ht ρ₀ propDomPiSort = 1 := rfl
theorem isZero_propDomPiSort : isZero propDomPiSort = false := rfl

/-! ## `P` is closed: every world leaves it alone -/

theorem liftA_impPropA (c : Nat) : liftA c 1 impPropA = impPropA := by
  have h0 : ¬ (c + 2 ≤ 0) := by omega
  have h1 : ¬ (c + 3 ≤ 1) := by omega
  simp [impPropA, qqA, liftA, h0, h1]

theorem wkExprA_impPropA : (ρ : WkSpecA) → wkExprA ρ impPropA = impPropA
  | [] => rfl
  | (_, c) :: ρ => by
      show wkExprA ρ (liftA c 1 impPropA) = impPropA
      rw [liftA_impPropA]
      exact wkExprA_impPropA ρ

/-! ## the witness -/

section Passes
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the prop triple at `P`, in any world. -/
abbrev impPropRel (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ : WkSpecA) : ExprA → ExprA → Prop :=
  fun a b => Nonempty (HasTyA E I n (wkCtxA ρ []) a impPropA) ∧
    Nonempty (HasTyA E I n (wkCtxA ρ []) b impPropA) ∧
    Nonempty (ConvA E I n (wkCtxA ρ []) a b impPropA)

/-- the `sortP` relation of `Sort 0`, in a context. -/
abbrev sort0Rel (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) : ExprA → ExprA → Prop :=
  fun a b => PropValidA E I n Γ a ∧ PropValidA E I n Γ b ∧
    Nonempty (HasTyA E I n Γ a (.sort .zero)) ∧ Nonempty (HasTyA E I n Γ b (.sort .zero)) ∧
    Nonempty (ConvA E I n Γ a b (.sort .zero)) ∧ PropEqA E I n Γ a b

/-- the Kripke relation of `T`. -/
abbrev propDomPiRel (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : ExprA → ExprA → Prop :=
  fun f g =>
    (∀ ρ : WkSpecA, WkOkA E I n ρ [] → ∀ a a' : ExprA, impPropRel E I n ρ a a' →
      sort0Rel E I n (wkCtxA ρ []) (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
    Nonempty (HasTyA E I n [] f propDomPiA) ∧ Nonempty (HasTyA E I n [] g propDomPiA) ∧
    Nonempty (ConvA E I n [] f g propDomPiA)

def impPropA_ty_wk (hE : EnvClosedA E) (hI : IotaLiftA I) (ρ : WkSpecA) (hρ : WkSpecA.ok ρ []) :
    HasTyA E I n (wkCtxA ρ []) impPropA (.sort impPropSort) := by
  have h := hasTyA_wk hE hI [] ρ hρ (impPropA_ty E I n)
  rwa [wkExprA_sort, wkExprA_impPropA] at h

theorem impPropA_isProp_wk (hE : EnvClosedA E) (hI : IotaLiftA I) (ρ : WkSpecA) (hρ : WkSpecA.ok ρ []) :
    IsPropTy E I (wkCtxA ρ []) impPropA := by
  have h := (isPropTy_wk_iff hE hI [] ρ hρ impPropA).2 (impPropA_isProp E I)
  rwa [wkExprA_impPropA] at h

/-- `P` valid in every world, by the prop clause, at any height. -/
theorem impProp_tyKA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k}
    (ρ : WkSpecA) (hρ : WkSpecA.ok ρ []) :
    TyKA E I n ρ₀ k LE LT (wkCtxA ρ []) (wkExprA ρ impPropA) (impPropRel E I n ρ) := by
  rw [wkExprA_impPropA]
  exact .prop (whTyA_of_hasTy (impPropA_ty_wk hE hI ρ hρ)) (hStepFnA_pi _ _ _ _ _ _ _)
    (impPropA_isProp_wk hE hI ρ hρ)

/-- `P ≡ P` in every world, at any height: a triple-like normal form, convertible to itself. -/
theorem impProp_eqKA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k}
    (ρ : WkSpecA) (hρ : WkSpecA.ok ρ []) :
    EqKA E I n ρ₀ k LE LT (wkCtxA ρ []) (wkExprA ρ impPropA) (wkExprA ρ impPropA) := by
  rw [wkExprA_impPropA]
  have hw := whTyA_of_hasTy (impPropA_ty_wk (n := n) hE hI ρ hρ)
  have ht : TripleLikeA E I (wkCtxA ρ []) impPropA :=
    ⟨hStepFnA_pi _ _ _ _ _ _ _, Or.inl (impPropA_isProp_wk hE hI ρ hρ)⟩
  exact .stuck hw hw ht ht ⟨.refl _ _⟩

/-- `Sort 0 ≡ Sort 0` at height ≥ 1, in any context. -/
theorem sort0_eqKA {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} (hk : 0 < k) (Γ : LCtxA) :
    EqKA E I n ρ₀ k LE LT Γ (.sort .zero) (.sort .zero) :=
  .sort (whTyA_of_hasTy (.sort Γ .zero)) (whTyA_of_hasTy (.sort Γ .zero)) hk (eqNA_refl _) ⟨.refl _ _⟩

theorem propDomPiA_not_isProp : ¬ IsPropTy E I [] propDomPiA := by
  intro h
  rw [propDomPiA, isPropTy_pi_iff] at h
  cases h

/-- `T ≡ T` at any height ≥ 1. -/
theorem propDomPi_eqKA (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k}
    (hk1 : 0 < k) : EqKA E I n ρ₀ k LE LT [] propDomPiA propDomPiA := by
  have hT : WhTyA E I n [] propDomPiA propDomPiA := whTyA_of_hasTy (propDomPiA_ty E I n)
  refine .pi hT hT (eqNA_refl _) (eqNA_refl _) ⟨impPropA_ty E I n⟩ ⟨.sort _ .zero⟩
    ⟨impPropA_ty E I n⟩ ⟨.sort _ .zero⟩ (impPropRel E I n)
    (fun ρ hρ => impProp_tyKA_wk hE hI ρ hρ.1) (fun ρ hρ => impProp_eqKA_wk hE hI ρ hρ.1)
    (fun ρ _ _ _ _ => ?_) ⟨.refl _ _⟩
  rw [wkExprA_sort]
  exact sort0_eqKA hk1 _

/-- `T` valid at any height ≥ 1, with the Kripke relation. -/
theorem propDomPi_tyKA (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k}
    (hk1 : 0 < k) : TyKA E I n ρ₀ k LE LT [] propDomPiA (propDomPiRel E I n) := by
  have hT : WhTyA E I n [] propDomPiA propDomPiA := whTyA_of_hasTy (propDomPiA_ty E I n)
  refine .pi hT propDomPiA_not_isProp ⟨impPropA_ty E I n⟩ ⟨.sort _ .zero⟩ (impPropRel E I n)
    (fun ρ hρ => impProp_tyKA_wk hE hI ρ hρ.1) (fun ρ _ => sort0Rel E I n (wkCtxA ρ []))
    (fun ρ _ _ _ _ => ?_) (fun ρ _ _ _ _ => ?_)
  · rw [wkExprA_sort]
    exact .sortP (whTyA_of_hasTy (.sort _ .zero)) rfl
  · rw [wkExprA_sort]
    exact sort0_eqKA hk1 _

/-- **THE PI ARM PASSES.** At every height above `T`'s sort height, `T` is
    related to itself as an element of `Sort (imax uP 1)`. -/
theorem piArm_height_passes (hE : EnvClosedA E) (hI : IotaLiftA I) (k : Nat) (hk : 1 < k) :
    LRRelA E I n ρ₀ k [] (.sort propDomPiSort) propDomPiA propDomPiA := by
  have hS : WhTyA E I n [] (.sort propDomPiSort) (.sort propDomPiSort) :=
    whTyA_of_hasTy (.sort [] propDomPiSort)
  have hk' : ht ρ₀ propDomPiSort < k := by rw [ht_propDomPiSort]; exact hk
  have h01 : 0 < ht ρ₀ propDomPiSort := by rw [ht_propDomPiSort]; exact Nat.zero_lt_one
  refine ⟨_, by rw [LRTyA_eq]; exact .sortT hS isZero_propDomPiSort hk', ?_⟩
  exact ⟨by rw [LREqA_eq]; exact propDomPi_eqKA hE hI h01,
    ⟨propDomPiRel E I n, by rw [LRTyA_eq]; exact propDomPi_tyKA hE hI h01⟩,
    ⟨propDomPiRel E I n, by rw [LRTyA_eq]; exact propDomPi_tyKA hE hI h01⟩,
    ⟨propDomPiA_ty E I n⟩, ⟨propDomPiA_ty E I n⟩, ⟨.refl _ _ _ (propDomPiA_ty E I n)⟩⟩

end Passes

#print axioms impPropA_isProp
#print axioms piArm_height_passes

end Rcic.Declarative.Ann
