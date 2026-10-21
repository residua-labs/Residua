import rcic.RcicAnnLRFundBind

/-!
# M2-e (3) + M2-g — the theorem in the judgment's own context; the two Type-level rows

THE IDENTITY PAIR IS VALID (`ValidSubstA_id`): in a well-formed context `Γ`, the
identity substitution is related to itself above a height of the context's
derivation — by induction on `CtxWfA`, the fundamental theorem on each type,
pushed under the binders by `ValidSubstA_up` / `ValidSubstA_upLet`. Hence THE
COROLLARIES: every typed term is related to itself at its type in its own
context (`fund_self`), every conversion relates its sides (`fund_conv`), every
type conversion is a type equality (`fund_tyEq`) — at every height above the
derivations'.

THE ROWS, for `ConvA` under the fundamental theorem's hypotheses (`EnvClosedA`,
`IotaLiftA`, `IotaSubstA`, `IotaConstHeadA`, `EnvSemA`, `PosValA`):

* `sortConvCharA` — `ConvA Γ (sort l₁) (sort l₂) (sort u) → eqN l₁ l₂`
  (`EqKA.sort` carries `eqN`; the `pi` and `stuck` clauses are excluded at a sort).
* `piConvInjA` — at ANY codomain annotation (M2-g′):
  `ConvA Γ (pi D u C v) (pi D' u' C' v') (sort w) → eqN u u' ∧ eqN v v' ∧
  TyConvA Γ D D' ∧ TyConvA (D :: Γ) C C'`. At a Type-level annotation
  (`piConvInjA_type`): `EqKA.pi`'s `hDeq` at the empty world, its `hC` at the
  world pushing `D` and the argument `bvar 0`, which is self-related by
  reflection; the `stuck` clause is excluded because a Type-level pi is not
  triple-like. At a propositional one: the conversion's sort is `Prop`-level (a
  pi's typing converts from `sort (imax u v)`, `hasTyA_pi_sort`, and convertible
  sorts are `=ₙ` along any chain, `tyConvA_sorts_eqN`), where the relation
  carries the two pis' structure (`PropEqA`), inverted at the pi
  (`propEqA_pi_inv`).

The rows for the kernel's untyped `Conv` are M3's (the landing through the
annotation).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Rows
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-! ## (1) the identity pair -/

theorem ValidSubstA_ext {k : Nat} {Δ Γ : LCtxA} {σ τ σ' τ' : SubstA}
    (hσ : ∀ i, σ i = τ i) (hσ' : ∀ i, σ' i = τ' i) (h : ValidSubstA E I n ρ₀ k Δ σ σ' Γ) :
    ValidSubstA E I n ρ₀ k Δ τ τ' Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · have := h.1 i A hA
    rw [substA_ext hσ A, substA_ext hσ' A, hσ i, hσ' i] at this
    exact this
  · have := h.2 i A v hA hv
    rw [substA_ext hσ A, substA_ext hσ v, substA_ext hσ' v, hσ i] at this
    exact this

/-- the identity pair is valid in a well-formed context, above a height of its derivation. -/
theorem ValidSubstA_id (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀) :
    {Γ : LCtxA} → CtxWfA E I n Γ →
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ValidSubstA E I n ρ₀ k Γ SubstA.id SubstA.id Γ
  | _, .nil => ⟨0, fun _ _ => ValidSubstA_nil [] SubstA.id SubstA.id⟩
  | _, .assumption (Γ := Γ) (A := A) (u := u) hΓ hA => by
      obtain ⟨k₁, h₁⟩ := ValidSubstA_id hE hI hIS hEN hNC hR hS hρ hΓ
      obtain ⟨k₂, h₂⟩ := (fundA hE hI hIS hEN hNC hR hS hρ).1 hA
      refine ⟨max k₁ k₂, fun k hk => ?_⟩
      have hid := h₁ k (le_max_of_le₁ hk)
      have hAA := (h₂ k (le_max_of_le₂ hk) Γ SubstA.id SubstA.id ⟨hΓ⟩ hid).2
      simp only [substA_id] at hAA
      obtain ⟨heA, hvA, _, tA, _, _⟩ := LRRelA_sort_elim hAA
      have heA' : LREqA E I n ρ₀ k Γ (substA SubstA.id A) (substA SubstA.id A) := by
        rw [substA_id]; exact heA
      have hvA' : ∃ R, LRTyA E I n ρ₀ k Γ (substA SubstA.id A) R := by rw [substA_id]; exact hvA
      have tA' : Nonempty (HasTyA E I n Γ (substA SubstA.id A) (.sort u)) := by rw [substA_id]; exact tA
      have := ValidSubstA_up hE hI hEN hNC (iotaConstHeadA_of_recHead hR) ⟨hΓ⟩ hid heA' hvA' tA'
      rw [substA_id] at this
      exact ValidSubstA_ext SubstA.id_up SubstA.id_up this
  | _, .letBinding (Γ := Γ) (A := A) (v := v) (u := u) hΓ hA hv => by
      obtain ⟨k₁, h₁⟩ := ValidSubstA_id hE hI hIS hEN hNC hR hS hρ hΓ
      obtain ⟨k₂, h₂⟩ := (fundA hE hI hIS hEN hNC hR hS hρ).1 hA
      obtain ⟨k₃, h₃⟩ := (fundA hE hI hIS hEN hNC hR hS hρ).1 hv
      refine ⟨max k₁ (max k₂ k₃), fun k hk => ?_⟩
      have hid := h₁ k (le_max_of_le₁ hk)
      have hAA := (h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Γ SubstA.id SubstA.id ⟨hΓ⟩ hid).2
      have hvv := (h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Γ SubstA.id SubstA.id ⟨hΓ⟩ hid).2
      simp only [substA_id] at hAA hvv
      obtain ⟨heA, _, _, tA, _, _⟩ := LRRelA_sort_elim hAA
      have heA' : LREqA E I n ρ₀ k Γ (substA SubstA.id A) (substA SubstA.id A) := by
        rw [substA_id]; exact heA
      have hvv' : LRRelA E I n ρ₀ k Γ (substA SubstA.id A) (substA SubstA.id v) (substA SubstA.id v) := by
        rw [substA_id, substA_id]; exact hvv
      have tA' : Nonempty (HasTyA E I n Γ (substA SubstA.id A) (.sort u)) := by rw [substA_id]; exact tA
      have := ValidSubstA_upLet hE hI hEN hNC ⟨hΓ⟩ hid heA' hvv' tA'
      rw [substA_id, substA_id] at this
      exact ValidSubstA_ext SubstA.id_up SubstA.id_up this

/-! ## (2) the corollaries: the theorem in the judgment's own context -/

theorem fund_self (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀)
    {Γ : LCtxA} {e A : ExprA} (hΓ : CtxWfA E I n Γ) (h : HasTyA E I n Γ e A) :
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → LRRelA E I n ρ₀ k Γ A e e := by
  obtain ⟨k₁, h₁⟩ := ValidSubstA_id hE hI hIS hEN hNC hR hS hρ hΓ
  obtain ⟨k₂, h₂⟩ := (fundA hE hI hIS hEN hNC hR hS hρ).1 h
  refine ⟨max k₁ k₂, fun k hk => ?_⟩
  have := (h₂ k (le_max_of_le₂ hk) Γ SubstA.id SubstA.id ⟨hΓ⟩ (h₁ k (le_max_of_le₁ hk))).2
  simpa only [substA_id] using this

theorem fund_conv (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀)
    {Γ : LCtxA} {a b A : ExprA} (hΓ : CtxWfA E I n Γ) (h : ConvA E I n Γ a b A) :
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → LRRelA E I n ρ₀ k Γ A a b := by
  obtain ⟨k₁, h₁⟩ := ValidSubstA_id hE hI hIS hEN hNC hR hS hρ hΓ
  obtain ⟨k₂, h₂⟩ := (fundA hE hI hIS hEN hNC hR hS hρ).2 h
  refine ⟨max k₁ k₂, fun k hk => ?_⟩
  have := (h₂ k (le_max_of_le₂ hk) Γ SubstA.id SubstA.id ⟨hΓ⟩ (h₁ k (le_max_of_le₁ hk))).2
  simpa only [substA_id] using this

theorem fund_tyEq (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀)
    {Γ : LCtxA} {A B : ExprA} {u : Level} (hΓ : CtxWfA E I n Γ) (h : ConvA E I n Γ A B (.sort u)) :
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → LREqA E I n ρ₀ k Γ A B := by
  obtain ⟨k₀, hk⟩ := fund_conv hE hI hIS hEN hNC hR hS hρ hΓ h
  exact ⟨k₀, fun k hk' => LREqA_of_sortRel (hk k hk')⟩

/-! ## (3) inversion of the type equality at sorts and at Type-level pis -/

theorem eqKA_sort_inv {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {l₁ l₂ : Level}
    (h : EqKA E I n ρ₀ k LE LT Γ (.sort l₁) (.sort l₂)) : eqN l₁ l₂ := by
  cases h with
  | sort hA hB _ hl _ =>
      have e1 := whTyA_det hA (whTyA_self hA) (hStepFnA_sort E I.fn Γ _) (hStepFnA_sort E I.fn Γ l₁)
      have e2 := whTyA_det hB (whTyA_self hB) (hStepFnA_sort E I.fn Γ _) (hStepFnA_sort E I.fn Γ l₂)
      cases e1; cases e2
      exact hl
  | pi hA _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_pi E I.fn Γ _ _ _ _) (hStepFnA_sort E I.fn Γ l₁)
      cases e
  | fam hA _ hnA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hnA (hStepFnA_sort E I.fn Γ l₁)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | stuck hA _ hN _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hN.1 (hStepFnA_sort E I.fn Γ l₁)
      subst e
      exact (tripleLikeA_not_sort hN).elim

theorem eqKA_pi_inv {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA}
    {D : ExprA} {u : Level} {C : ExprA} {v : Level} {D' : ExprA} {u' : Level} {C' : ExprA} {v' : Level}
    (hz : isZero v = false) (h : EqKA E I n ρ₀ k LE LT Γ (.pi D u C v) (.pi D' u' C' v')) :
    eqN u u' ∧ eqN v v' ∧ Nonempty (HasTyA E I n Γ D (.sort u)) ∧
    (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D')) ∧
    ∃ RD : WkSpecA → ExprA → ExprA → Prop,
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ)) ∧
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C'))) := by
  cases h with
  | sort hA _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_sort E I.fn Γ _) (hStepFnA_pi E I.fn Γ D u C v)
      cases e
  | pi hA hB hu hv hDty _ _ _ RD hD hDeq hC _ =>
      have e1 := whTyA_det hA (whTyA_self hA) (hStepFnA_pi E I.fn Γ _ _ _ _) (hStepFnA_pi E I.fn Γ D u C v)
      have e2 := whTyA_det hB (whTyA_self hB) (hStepFnA_pi E I.fn Γ _ _ _ _) (hStepFnA_pi E I.fn Γ D' u' C' v')
      cases e1; cases e2
      exact ⟨hu, hv, hDty, hDeq, RD, hD, hC⟩
  | fam hA _ hnA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hnA (hStepFnA_pi E I.fn Γ D u C v)
      exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck hA _ hN _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hN.1 (hStepFnA_pi E I.fn Γ D u C v)
      subst e
      have := (isPropTy_pi_iff E I Γ D u C v).1 (tripleLikeA_pi_isProp hN)
      rw [this] at hz
      cases hz

/-! ## (3b) M2-g′: the sort of a pi's conversion; type conversions of sorts -/

/-- generation, the sort half: a pi's type converts from its own sort (`pi` after `conv`s). -/
def hasTyA_pi_sort : {Γ : LCtxA} → {D : ExprA} → {u : Level} → {C : ExprA} → {v : Level} →
    {T : ExprA} → HasTyA E I n Γ (.pi D u C v) T → TyConvA E I n Γ (.sort (.imax u v)) T
  | _, _, _, _, _, _, .pi Γ _ _ _ _ _ _ => .refl Γ _
  | _, _, _, _, _, _, .conv Γ _ A B l u h hAl hlu hB hc =>
      .trans Γ _ A B (hasTyA_pi_sort h) (.of Γ A B l u u hAl hlu hB (eqNA_refl u) hc)

/-- a type conversion is a syntactic identity or a type equality above some height. -/
theorem fund_tyConvA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) :
    {A B : ExprA} → TyConvA E I n Γ A B → A = B ∨ ∃ k₀, ∀ k, k₀ ≤ k → LREqA E I n ρ₀ k Γ A B
  | _, _, .refl _ _ => Or.inl rfl
  | _, _, .of _ _ _ _ _ _ _ _ _ _ h => Or.inr (fund_tyEq hE hI hIS hEN hNC hR hS hρ hΓ h)
  | _, _, .trans _ _ _ _ h1 h2 =>
      match fund_tyConvA hE hI hIS hEN hNC hR hS hρ hΓ h1, fund_tyConvA hE hI hIS hEN hNC hR hS hρ hΓ h2 with
      | Or.inl e1, Or.inl e2 => Or.inl (e1.trans e2)
      | Or.inl e1, Or.inr h => Or.inr (e1 ▸ h)
      | Or.inr h, Or.inl e2 => Or.inr (e2 ▸ h)
      | Or.inr ⟨k₁, h₁⟩, Or.inr ⟨k₂, h₂⟩ =>
          Or.inr ⟨max k₁ k₂, fun k hk => LREqA_trans hEN (h₁ k (le_max_of_le₁ hk)) (h₂ k (le_max_of_le₂ hk))⟩

/-- convertible sorts, through any chain of type conversions, are `=ₙ` (row 1 along the chain). -/
theorem tyConvA_sorts_eqN (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {l l' : Level} (h : TyConvA E I n Γ (.sort l) (.sort l')) : eqN l l' := by
  rcases fund_tyConvA hE hI hIS hEN hNC hR hS hρ hΓ h with e | ⟨k₀, hk⟩
  · injection e with e
    subst e
    exact eqNA_refl _
  · have := hk k₀ (Nat.le_refl _)
    rw [LREqA_eq] at this
    exact eqKA_sort_inv this

/-! ## (4) THE ROWS for `ConvA`, Type-level -/

/-- ROW 1 — `SortConvChar`: convertible sorts are `=ₙ`. -/
theorem sortConvCharA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀)
    {Γ : LCtxA} {l₁ l₂ u : Level} (hΓ : CtxWfA E I n Γ)
    (h : ConvA E I n Γ (.sort l₁) (.sort l₂) (.sort u)) : eqN l₁ l₂ := by
  obtain ⟨k₀, hk⟩ := fund_tyEq hE hI hIS hEN hNC hR hS hρ hΓ h
  have := hk k₀ (Nat.le_refl _)
  rw [LREqA_eq] at this
  exact eqKA_sort_inv this

/-- ROW 2, Type-level part — `PiConvInj` at a Type-level codomain annotation: `EqKA.pi`'s
    structure. -/
theorem piConvInjA_type (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀)
    {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level} {D' : ExprA} {u' : Level} {C' : ExprA}
    {v' w : Level} (hΓ : CtxWfA E I n Γ) (hz : isZero v = false)
    (h : ConvA E I n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) :
    eqN u u' ∧ eqN v v' ∧ Nonempty (TyConvA E I n Γ D D') ∧
    Nonempty (TyConvA E I n (.assumption D :: Γ) C C') := by
  obtain ⟨k₀, hk⟩ := fund_tyEq hE hI hIS hEN hNC hR hS hρ hΓ h
  have hEq := hk k₀ (Nat.le_refl _)
  rw [LREqA_eq] at hEq
  obtain ⟨hu, hv, hDty, hDeq, RD, hD, hC⟩ := eqKA_pi_inv hz hEq
  refine ⟨hu, hv, eqKA_tyConv (hDeq [] ⟨trivial, ⟨hΓ⟩⟩), ?_⟩
  have hΓD : Nonempty (CtxWfA E I n (.assumption D :: Γ)) := hDty.elim fun t => ⟨.assumption hΓ t⟩
  have hρ₁ : WkOkA E I n [(.assumption D, 0)] Γ := wkOkA_push _ Γ hΓD
  have hD₁ := hD _ hρ₁
  simp only [wkCtxA_push, wkExprA_push] at hD₁
  have hLR : LRTyA E I n ρ₀ k₀ (.assumption D :: Γ) (liftA 0 1 D) (RD [(.assumption D, 0)]) := by
    rw [LRTyA_eq]; exact hD₁
  have ht0 : Nonempty (HasTyA E I n (.assumption D :: Γ) (.bvar 0) (liftA 0 1 D)) :=
    hDty.elim fun t => ⟨.bvar (.assumption D :: Γ) 0 (liftA 0 1 D) u rfl
      (hasTyA_wk hE hI Γ [(.assumption D, 0)] hρ₁.1 t)⟩
  have h0 : LRRelA E I n ρ₀ k₀ (.assumption D :: Γ) (liftA 0 1 D) (.bvar 0) (.bvar 0) :=
    LRRelA_bvar hE hI (iotaConstHeadA_of_recHead hR) rfl ⟨_, hLR⟩ ht0
  have hr : RD [(.assumption D, 0)] (.bvar 0) (.bvar 0) := h0.at hLR
  have hC₁ := hC _ hρ₁ (.bvar 0) (.bvar 0) hr
  have e : ∀ X : ExprA, instantiate0A (.bvar 0) (wkExprA (WkSpecA.ub [(.assumption D, 0)]) X) = X :=
    fun X => instantiate0A_bvar0_liftA X
  simp only [wkCtxA_push, e] at hC₁
  exact eqKA_tyConv hC₁

/-- ROW 2 — `PiConvInj`, AT ANY CODOMAIN (M2-g′): convertible pis have `=ₙ` annotations,
    convertible domains and convertible codomains under the domain. A propositional pi's conversion
    sits at a `Prop`-level sort (its typing converts from `sort (imax u v)`, and convertible sorts
    are `=ₙ`, row 1), where the relation carries the two pis' STRUCTURE (`PropEqA`), inverted at
    the pi (`propEqA_pi_inv`); a Type-level one is `piConvInjA_type`. -/
theorem piConvInjA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀)
    (hρ : PosValA ρ₀)
    {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level} {D' : ExprA} {u' : Level} {C' : ExprA}
    {v' w : Level} (hΓ : CtxWfA E I n Γ)
    (h : ConvA E I n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) :
    eqN u u' ∧ eqN v v' ∧ Nonempty (TyConvA E I n Γ D D') ∧
    Nonempty (TyConvA E I n (.assumption D :: Γ) C C') := by
  cases hz : isZero v with
  | false => exact piConvInjA_type hE hI hIS hEN hNC hR hS hρ hΓ hz h
  | true =>
      obtain ⟨k₀, hk⟩ := fund_conv hE hI hIS hEN hNC hR hS hρ hΓ h
      have hrel := hk k₀ (Nat.le_refl _)
      obtain ⟨_, _, _, ⟨ht⟩, _, _⟩ := LRRelA_sort_elim hrel
      have hw : eqN (.imax u v) w := tyConvA_sorts_eqN hE hI hIS hEN hNC hR hS hρ hΓ (hasTyA_pi_sort ht)
      have hzw : isZero w = true := by rw [← isZero_eqN hw, isZero_imax]; exact hz
      obtain ⟨hu, hv, hD, hC⟩ := propEqA_pi_inv ⟨hΓ⟩ (LRRelA_sortP_elim hzw hrel).2.2.2.2.2
      exact ⟨hu, hv, hD, propEqA_tyConv hC⟩

end Rows

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.ValidSubstA_id
#print axioms Rcic.Declarative.Ann.fund_self
#print axioms Rcic.Declarative.Ann.fund_conv
#print axioms Rcic.Declarative.Ann.sortConvCharA
#print axioms Rcic.Declarative.Ann.tyConvA_sorts_eqN
#print axioms Rcic.Declarative.Ann.piConvInjA_type
#print axioms Rcic.Declarative.Ann.piConvInjA
