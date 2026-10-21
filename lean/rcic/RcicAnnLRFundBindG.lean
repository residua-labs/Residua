import rcic.RcicAnnLRFundBind
import rcic.RcicAnnLRFundG
/-!
# M2-e (2) — the binder arms of the fundamental theorem

The eleven arms `fund_of_binderArmsg` takes as hypotheses: typing `pi`, `lam`,
`app`, `letE`; conversion `beta`, `zeta`, `app`, `lam`, `pi`, `letE`, `eta`.
Infrastructure first:

* POSITIVITY. `isZero` is syntactic (`param _ ↦ false`) while heights are
  semantic, so under a valuation sending a level parameter to `0` a
  syntactically Type-level sort sits at height `0`, where nothing but
  propositions is valid: the `pi` arm would fail there. The binder arms assume
  `PosValA ρ₀ := ∀ i, 0 < ρ₀ i`; then `isZero l = false ↔ 0 < ht ρ₀ l`
  (`ht_pos_of_isZero_false`, `ht_zero_of_isZero`), and `ht (imax u v) =
  max (ht u) (ht v)` for Type-level `v` (`ht_imax_of_pos`). The rows need one
  valuation, not all.
* VALID PAIRS UNDER A BINDER AND IN WORLDS. `ValidSubstA_consg` (extension by a
  related pair of arguments), `ValidSubstA_consLetg` (by the substituted value),
  `ValidSubstA_wkg` (into a world), `ValidSubstA_upg` / `ValidSubstA_upLetg` (into
  the extended target context, variable `0` by reflection or by ζ-local
  expansion) — the last two are what give the BINDER TYPINGS the typed rules
  demand (`HasTyA (σA :: Δ) (σ⁺B) (sort v)`), from the IH.
* THE ONE IDENTITY of worlds under binders: `instantiate0A a (wkExprA (ub ρ)
  (substA σ.up B)) = substA (cons a (wkExprA ρ ∘ σ)) B` (`wk_ub_subst_up`), so
  the pi clause's Kripke data at world `ρ` are the IH under the pair extended
  at that world.
* `LRRelA_sort_elim'g`: the content of a sort relation at EVERY height from the
  sort's own (`ht u`) upward — the `pi` arm reads the domain's and codomain's
  data at the pi's sort height, which is below the IH's threshold.
* the canonical relation of a valid type is the knotted `LRRelAg` at it
  (`LRRelA_eq_canong`): the pi clause's `RD`/`RC` are chosen canonically, with
  no choice.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) positivity and the heights of `max`/`imax` -/

/-! ## (1) substitution identities under binders and worlds -/

section Bind
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-! ## (2) the canonical relation is the knotted one -/

theorem LRRelA_eq_canong (k : Nat) (Γ : LCtxA) (A : ExprA) :
    (fun a b => LRRelAg E I n ρ₀ k Γ A a b) =
      canonRelAg E I n ρ₀ k (fun j _ => LREqAg E I n ρ₀ j) (fun j _ => LRTyAg E I n ρ₀ j) Γ A := by
  funext a b
  unfold LRRelAg canonRelAg
  rw [LRTyA_eqg]

/-- a valid type is valid with its knotted relation. -/
theorem LRTyA_canong {k : Nat} {Γ : LCtxA} {A : ExprA} (h : ∃ R, LRTyAg E I n ρ₀ k Γ A R) :
    LRTyAg E I n ρ₀ k Γ A (fun a b => LRRelAg E I n ρ₀ k Γ A a b) := by
  rw [LRRelA_eq_canong, LRTyA_eqg]
  obtain ⟨R, hR⟩ := h
  rw [LRTyA_eqg] at hR
  exact tyKA_canong ⟨R, hR⟩

/-! ## (3) the content of a sort relation at every height from the sort's own -/

theorem LRRelA_sort_elim'g {k : Nat} {Γ : LCtxA} {u : Level} {A B : ExprA}
    (h : LRRelAg E I n ρ₀ k Γ (.sort u) A B) :
    (∀ k', ht ρ₀ u ≤ k' →
      LREqAg E I n ρ₀ k' Γ A B ∧ (∃ R, LRTyAg E I n ρ₀ k' Γ A R) ∧ (∃ R, LRTyAg E I n ρ₀ k' Γ B R)) ∧
    Nonempty (HasTyA E I n Γ A (.sort u)) ∧ Nonempty (HasTyA E I n Γ B (.sort u)) ∧
    Nonempty (ConvA E I n Γ A B (.sort u)) := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eqg] at hR
  rcases tyKA_sort_invg hR with ⟨_, hk, e⟩ | ⟨_, e⟩
  · subst e
    obtain ⟨hle, hva, hvb, hta, htb, hc⟩ := hab
    refine ⟨fun k' hk' => ⟨LREqA_monog hk' hle,
      hva.elim fun R h => ⟨R, LRTyA_monog hk' h⟩, hvb.elim fun R h => ⟨R, LRTyA_monog hk' h⟩⟩,
      hta, htb, hc⟩
  · subst e
    -- S1-g.2: the guarded `sortP` hands over key-propositions — the prop clause, no K here
    obtain ⟨⟨N, hNb, hnN, hPN⟩, ⟨M, hM, hnM, hPM⟩, hta, htb, hc, _⟩ := hab
    refine ⟨fun k' _ => ⟨?_, ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hNb hnN hPN⟩,
      ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hM hnM hPM⟩⟩, hta, htb, hc⟩
    rw [LREqA_eqg]
    exact .stuck hNb hM ⟨hnN, Or.inl hPN⟩ ⟨hnM, Or.inl hPM⟩
      (hta.elim fun ta => htb.elim fun tb => hc.elim fun c =>
        ⟨.of Γ A B u u u ta (eqNA_refl u) tb (eqNA_refl u) c⟩)
      ⟨fun _ => hPM, fun _ => hPN⟩

/-! ## (4) valid pairs: extension under a binder, weakening into worlds -/

theorem ValidSubstA_consg (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA} {A a a' : ExprA}
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (he : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A))
    (ha : LRRelAg E I n ρ₀ k Δ (substA σ A) a a') :
    ValidSubstAg E I n ρ₀ k Δ (SubstA.cons a σ) (SubstA.cons a' σ') (.assumption A :: Γ) := by
  refine ⟨fun i B hB => ?_, fun i B v hB hv => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_assumption] at hB
        cases hB
        simp only [substA_cons_liftA]
        exact ⟨he, ha⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            simp only [substA_cons_liftA]
            exact h.1 i A' hΓ
  · cases i with
    | zero => rw [lookupValueA_cons_zero_assumption] at hv; cases hv
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hv
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hv; cases hv
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hv
              cases hB; cases hv
              simp only [substA_cons_liftA]
              exact h.2 i A' v' hΓ hΓv

theorem ValidSubstA_consLetg (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA} {A v : ExprA}
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (he : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A))
    (hv : LRRelAg E I n ρ₀ k Δ (substA σ A) (substA σ v) (substA σ' v)) :
    ValidSubstAg E I n ρ₀ k Δ (SubstA.cons (substA σ v) σ) (SubstA.cons (substA σ' v) σ')
      (.letBinding A v :: Γ) := by
  refine ⟨fun i B hB => ?_, fun i B w hB hw => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        cases hB
        simp only [substA_cons_liftA]
        exact ⟨he, hv⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            simp only [substA_cons_liftA]
            exact h.1 i A' hΓ
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        rw [lookupValueA_cons_zero_let] at hw
        cases hB; cases hw
        simp only [substA_cons_liftA]
        exact ⟨LRRelA_refl_leftg hEN hv, hv⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hw
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hw; cases hw
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hw
              cases hB; cases hw
              simp only [substA_cons_liftA]
              exact h.2 i A' v' hΓ hΓv

theorem ValidSubstA_wkg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    {k : Nat} {Δ : LCtxA}
    {σ σ' : SubstA} {Γ : LCtxA} (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ) (ρ : WkSpecA)
    (hρ : WkOkA E I n ρ Δ) :
    ValidSubstAg E I n ρ₀ k (wkCtxA ρ Δ) (fun i => wkExprA ρ (σ i)) (fun i => wkExprA ρ (σ' i)) Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    have he' := LREqA_wkg hE hNC hI he ρ hρ
    have hr' := LRRelA_wkg hE hNC hI hr ρ hρ
    simp only [wkExprA_substA] at he' hr'
    exact ⟨he', hr'⟩
  · obtain ⟨h1, h2⟩ := h.2 i A v hA hv
    have h1' := LRRelA_wkg hE hNC hI h1 ρ hρ
    have h2' := LRRelA_wkg hE hNC hI h2 ρ hρ
    simp only [wkExprA_substA] at h1' h2'
    exact ⟨h1', h2'⟩

/-- into the extended target context whose binder is ANY type convertible to the substituted
    domain (M2-g′: `PropEqA`'s pi clause quantifies over such binders): variable `0` by reflection
    at the substituted domain, typed through the conversion; the rest weakened. -/
theorem ValidSubstA_upConvg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n)
    {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA} {A D : ExprA}
    (hΔD : Nonempty (CtxWfA E I n (.assumption D :: Δ)))
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (he : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A))
    (hvA : ∃ R, LRTyAg E I n ρ₀ k Δ (substA σ A) R)
    (hD : Nonempty (TyConvA E I n Δ D (substA σ A))) :
    ValidSubstAg E I n ρ₀ k (.assumption D :: Δ) σ.up σ'.up (.assumption A :: Γ) := by
  have hρ : WkOkA E I n [(.assumption D, 0)] Δ := wkOkA_push _ Δ hΔD
  have hw := ValidSubstA_wkg hE hI hEN hNC h [(.assumption D, 0)] hρ
  have he' := LREqA_wkg hE hNC hI he _ hρ
  have hD' := tyConvA_wk_ne hE hI [(.assumption D, 0)] hρ.1 hD
  simp only [wkExprA_push, wkCtxA_push] at hw he' hD'
  have hv' : ∃ R, LRTyAg E I n ρ₀ k (.assumption D :: Δ) (liftA 0 1 (substA σ A)) R :=
    hvA.elim fun R hR => (LRTyA_wkg hE hNC hI hR _ hρ).elim fun R' hR' => ⟨R', hR'.1⟩
  have ht0 : Nonempty (HasTyA E I n (.assumption D :: Δ) (.bvar 0) (liftA 0 1 (substA σ A))) :=
    hΔD.elim fun c => match c with
    | .assumption _ t => hD'.elim fun d =>
        ⟨hasTyA_of_tyConvA (.bvar (.assumption D :: Δ) 0 (liftA 0 1 D) _ rfl
          (hasTyA_wk hE hI Δ [(.assumption D, 0)] hρ.1 t)) d⟩
  refine ⟨fun i B hB => ?_, fun i B v hB hv => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_assumption] at hB
        cases hB
        simp only [substA_up_liftA]
        exact ⟨he', LRRelA_bvarg hE hI hIC hK hΔD rfl hv' ht0⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            have := hw.1 i A' hΓ
            simp only [substA_up_liftA, liftA_substA, SubstA.up_succ]
            exact this
  · cases i with
    | zero => rw [lookupValueA_cons_zero_assumption] at hv; cases hv
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hv
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hv; cases hv
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hv
              cases hB; cases hv
              have := hw.2 i A' v' hΓ hΓv
              simp only [substA_up_liftA, liftA_substA, SubstA.up_succ]
              exact this

/-- into the extended target context, under an assumption binder: variable `0` by
    reflection (it has no value), the rest weakened. -/
theorem ValidSubstA_upg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n)
    {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA} {A : ExprA} {u : Level}
    (hΔ : Nonempty (CtxWfA E I n Δ))
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (he : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A))
    (hvA : ∃ R, LRTyAg E I n ρ₀ k Δ (substA σ A) R)
    (htA : Nonempty (HasTyA E I n Δ (substA σ A) (.sort u))) :
    ValidSubstAg E I n ρ₀ k (.assumption (substA σ A) :: Δ) σ.up σ'.up (.assumption A :: Γ) :=
  ValidSubstA_upConvg hE hI hEN hNC hIC hK (hΔ.elim fun c => htA.elim fun t => ⟨.assumption c t⟩) h he hvA
    ⟨.refl _ _⟩

/-- into the extended target context, under a let binder: variable `0` by ζ-local
    expansion from the weakened value. -/
theorem ValidSubstA_upLetg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA} {A v : ExprA} {u : Level}
    (hΔ : Nonempty (CtxWfA E I n Δ))
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (he : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A))
    (hv : LRRelAg E I n ρ₀ k Δ (substA σ A) (substA σ v) (substA σ' v))
    (htA : Nonempty (HasTyA E I n Δ (substA σ A) (.sort u))) :
    ValidSubstAg E I n ρ₀ k (.letBinding (substA σ A) (substA σ v) :: Δ) σ.up σ'.up
      (.letBinding A v :: Γ) := by
  have htv : Nonempty (HasTyA E I n Δ (substA σ v) (substA σ A)) := (LRRelA_hasTyg hv).1
  have hΔ' : Nonempty (CtxWfA E I n (.letBinding (substA σ A) (substA σ v) :: Δ)) :=
    hΔ.elim fun c => htA.elim fun t => htv.elim fun tv => ⟨.letBinding c t tv⟩
  have hρ : WkOkA E I n [(.letBinding (substA σ A) (substA σ v), 0)] Δ := wkOkA_push _ Δ hΔ'
  have hw := ValidSubstA_wkg hE hI hEN hNC h [(.letBinding (substA σ A) (substA σ v), 0)] hρ
  have he' := LREqA_wkg hE hNC hI he _ hρ
  have hv' := LRRelA_wkg hE hNC hI hv _ hρ
  simp only [wkExprA_push, wkCtxA_push] at hw he' hv'
  -- the step bvar 0 ⇝ lift (σv) at lift (σA), typed
  have hs : StepAtA E I n (.letBinding (substA σ A) (substA σ v) :: Δ) (.bvar 0)
      (liftA 0 1 (substA σ v)) (liftA 0 1 (substA σ A)) :=
    ⟨htA.elim fun t => ⟨.bvar _ 0 _ u rfl (hasTyA_wk hE hI Δ _ hρ.1 t)⟩,
     htv.elim fun tv => ⟨.zetaLocal _ 0 _ _ rfl rfl (hasTyA_wk hE hI Δ _ hρ.1 tv)⟩⟩
  have h0 : LRRelAg E I n ρ₀ k (.letBinding (substA σ A) (substA σ v) :: Δ) (liftA 0 1 (substA σ A))
      (.bvar 0) (liftA 0 1 (substA σ v)) :=
    LRRelA_expand_leftg hE hI hs (LRRelA_refl_leftg hEN hv')
  refine ⟨fun i B hB => ?_, fun i B w hB hw => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        cases hB
        simp only [substA_up_liftA]
        exact ⟨he', LRRelA_expand_rightg hE hI hs h0⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            have := hw.1 i A' hΓ
            simp only [substA_up_liftA, liftA_substA, SubstA.up_succ]
            exact this
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        rw [lookupValueA_cons_zero_let] at hw
        cases hB; cases hw
        simp only [substA_up_liftA]
        exact ⟨h0, hv'⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hw
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hw; cases hw
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hw
              cases hB; cases hw
              have := hw.2 i A' v' hΓ hΓv
              simp only [substA_up_liftA, liftA_substA, SubstA.up_succ]
              exact this

/-! ## (5) generation for pis; inversion of the pi clause -/

/-- the relation of a Type-level pi is the pi clause's. -/
theorem tyKA_pi_invg {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {D : ExprA} {u : Level}
    {C : ExprA} {v : Level} {R : ExprA → ExprA → Prop}
    (h : TyKAg E I n ρ₀ k LE LT Γ (.pi D u C v) R) (hnp : ¬ IsPropTy E I Γ (.pi D u C v)) :
    ∃ (RD : WkSpecA → ExprA → ExprA → Prop) (RC : WkSpecA → ExprA → ExprA → ExprA → Prop),
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ)) ∧
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a)) ∧
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) ∧
      R = fun f g =>
        (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
          RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
        Nonempty (HasTyA E I n Γ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Γ g (.pi D u C v)) ∧
        Nonempty (ConvA E I n Γ f g (.pi D u C v)) := by
  cases h with
  | prop hA hn hP =>
      have e := whTyA_det hA (whTyA_self hA) hn (hStepFnA_pi E I.fn Γ D u C v)
      subst e
      exact absurd hP hnp
  | sortT hA _ _ =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_sort E I.fn Γ _) (hStepFnA_pi E I.fn Γ D u C v)
      cases e
  | sortP hA _ =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_sort E I.fn Γ _) (hStepFnA_pi E I.fn Γ D u C v)
      cases e
  | pi hA _ _ _ RD hD RC hC hCeq =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_pi E I.fn Γ _ _ _ _)
        (hStepFnA_pi E I.fn Γ D u C v)
      cases e
      exact ⟨RD, RC, hD, hC, hCeq, rfl⟩
  | fam hA hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hn (hStepFnA_pi E I.fn Γ D u C v)
      exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck hA hNC =>
      have e := whTyA_det hA (whTyA_self hA) hNC.1 (hStepFnA_pi E I.fn Γ D u C v)
      subst e
      exact (stuckA_not_pi hNC).elim

/-- the Kripke conjunct of relatedness at a Type-level pi. -/
theorem LRRelA_pi_elimg {k : Nat} {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    {f g : ExprA} (h : LRRelAg E I n ρ₀ k Γ (.pi D u C v) f g) (hnp : ¬ IsPropTy E I Γ (.pi D u C v)) :
    ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA,
      LRRelAg E I n ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ D) a a' →
      LRRelAg E I n ρ₀ k (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a') := by
  obtain ⟨R, hR, hfg⟩ := h
  rw [LRTyA_eqg] at hR
  obtain ⟨RD, RC, hD, hC, _, e⟩ := tyKA_pi_invg hR hnp
  subst e
  intro ρ hρ a a' hr
  have hr' : RD ρ a a' := hr.at (by rw [LRTyA_eqg]; exact hD ρ hρ)
  exact LRRelAg.of (by rw [LRTyA_eqg]; exact hC ρ hρ a a' hr') (hfg.1 ρ hρ a a' hr')

/-! ## (6) the pi clause from world-indexed data -/

section PiData
variable {k : Nat} {Δ : LCtxA} {D C D' C' : ExprA} {u v : Level}

/-- `pi D u C v ≡ pi D' u' C' v'` at height `k` (annotations `=ₙ`, R-TypedRules (6)) from:
    the domains' equality and validity in every world, the codomains' equality at every
    self-related argument in every world, the typings, and the conversion of the two pis. -/
theorem piEqA_of_datag (hEN : EnvNormCtorTypeA E) {u' v' : Level} (hu : eqN u u') (hv : eqN v v')
    (tD : HasTyA E I n Δ D (.sort u)) (tC : HasTyA E I n (.assumption D :: Δ) C (.sort v))
    (tD' : HasTyA E I n Δ D' (.sort u')) (tC' : HasTyA E I n (.assumption D' :: Δ) C' (.sort v'))
    (hDeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
      LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) (wkExprA ρ D'))
    (hDv : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∃ R, LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) R)
    (hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a : ExprA,
      LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a a →
      LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
    (hc : Nonempty (TyConvA E I n Δ (.pi D u C v) (.pi D' u' C' v'))) :
    LREqAg E I n ρ₀ k Δ (.pi D u C v) (.pi D' u' C' v') := by
  rw [LREqA_eqg]
  refine .pi (whTyA_of_hasTy (.pi Δ D u C v tD tC)) (whTyA_of_hasTy (.pi Δ D' u' C' v' tD' tC'))
    hu hv ⟨tD⟩ ⟨tC⟩ ⟨tD'⟩ ⟨tC'⟩
    (fun ρ a b => LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a b)
    (fun ρ hρ => ?_) (fun ρ hρ => ?_) (fun ρ hρ a a' hr => ?_) hc
  · have := LRTyA_canong (hDv ρ hρ); rw [LRTyA_eqg] at this; exact this
  · have := hDeq ρ hρ; rw [LREqA_eqg] at this; exact this
  · have := hCeq ρ hρ a (LRRelA_refl_leftg hEN hr); rw [LREqA_eqg] at this; exact this

/-- the pi relation at height `k` from the data, for a Type-level pi. -/
theorem piTyA_of_datag (hz : isZero v = false)
    (tD : HasTyA E I n Δ D (.sort u)) (tC : HasTyA E I n (.assumption D :: Δ) C (.sort v))
    (hDv : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∃ R, LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) R)
    (hCv : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA,
      LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a a' →
      ∃ R, LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) R)
    (hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA,
      LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a a' →
      LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) :
    LRTyAg E I n ρ₀ k Δ (.pi D u C v) (fun f g =>
      (∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA,
        LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a a' →
        LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      Nonempty (HasTyA E I n Δ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Δ g (.pi D u C v)) ∧
      Nonempty (ConvA E I n Δ f g (.pi D u C v))) := by
  rw [LRTyA_eqg]
  refine .pi (whTyA_of_hasTy (.pi Δ D u C v tD tC)) (fun h => ?_) ⟨tD⟩ ⟨tC⟩
    (fun ρ a b => LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a b) (fun ρ hρ => ?_)
    (fun ρ a x y => LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) x y)
    (fun ρ hρ a a' hr => ?_) (fun ρ hρ a a' hr => ?_)
  · rw [(isPropTy_pi_iff E I Δ D u C v).1 h] at hz; cases hz
  · have := LRTyA_canong (hDv ρ hρ); rw [LRTyA_eqg] at this; exact this
  · have := LRTyA_canong (hCv ρ hρ a a' hr); rw [LRTyA_eqg] at this; exact this
  · have := hCeq ρ hρ a a' hr; rw [LREqA_eqg] at this; exact this

end PiData

/-! ## (7) reading an IH at a world, plain and under a binder -/

section IHWorld

/-- an IH, read at a world `ρ` of `Δ` with the pair weakened there. -/
theorem fundArm_wkg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    {k₀ : Nat} {Γ : LCtxA} {e e' A : ExprA}
    (h : ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (σ σ' : SubstA), Nonempty (CtxWfA E I n Δ) →
      ValidSubstAg E I n ρ₀ k Δ σ σ' Γ →
      LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A) ∧
      LRRelAg E I n ρ₀ k Δ (substA σ A) (substA σ e) (substA σ' e'))
    {k : Nat} (hk : k₀ ≤ k) {Δ : LCtxA} {σ σ' : SubstA} (hσ : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (ρ : WkSpecA) (hρ : WkOkA E I n ρ Δ) :
    LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A)) ∧
    LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ e))
      (wkExprA ρ (substA σ' e')) := by
  have := h k hk _ _ _ hρ.2 (ValidSubstA_wkg hE hI hEN hNC hσ ρ hρ)
  simp only [wkExprA_substA]
  exact this

/-- the IH of a type judgment `A ≈ A' : sort u`, read at a world: the sort relation. -/
theorem fundArm_sort_wkg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    {k₀ : Nat} {Γ : LCtxA} {A A' : ExprA} {u : Level}
    (h : ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (σ σ' : SubstA), Nonempty (CtxWfA E I n Δ) →
      ValidSubstAg E I n ρ₀ k Δ σ σ' Γ →
      LREqAg E I n ρ₀ k Δ (substA σ (.sort u)) (substA σ' (.sort u)) ∧
      LRRelAg E I n ρ₀ k Δ (substA σ (.sort u)) (substA σ A) (substA σ' A'))
    {k : Nat} (hk : k₀ ≤ k) {Δ : LCtxA} {σ σ' : SubstA} (hσ : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (ρ : WkSpecA) (hρ : WkOkA E I n ρ Δ) :
    LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (.sort u) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A')) := by
  have := (h k hk _ _ _ hρ.2 (ValidSubstA_wkg hE hI hEN hNC hσ ρ hρ)).2
  simp only [wkExprA_substA]
  exact this

/-- the IH of a judgment under an assumption binder, read at a world of `Δ` with the pair
    extended by related arguments: the pi clause's codomain datum. -/
theorem fundArm_cons_wkg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    {k₀ : Nat} {Γ : LCtxA} {A e e' B : ExprA}
    (h : ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (σ σ' : SubstA), Nonempty (CtxWfA E I n Δ) →
      ValidSubstAg E I n ρ₀ k Δ σ σ' (.assumption A :: Γ) →
      LREqAg E I n ρ₀ k Δ (substA σ B) (substA σ' B) ∧
      LRRelAg E I n ρ₀ k Δ (substA σ B) (substA σ e) (substA σ' e'))
    {k : Nat} (hk : k₀ ≤ k) {Δ : LCtxA} {σ σ' : SubstA} (hσ : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (ρ : WkSpecA) (hρ : WkOkA E I n ρ Δ)
    (he : LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A)))
    {a a' : ExprA} (ha : LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) a a') :
    LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
      (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ'.up B))) ∧
    LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up e)))
      (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ'.up e'))) := by
  rw [wkExprA_substA, wkExprA_substA] at he
  rw [wkExprA_substA] at ha
  have hv := ValidSubstA_consg hEN (ValidSubstA_wkg hE hI hEN hNC hσ ρ hρ) he ha
  have := h k hk _ _ _ hρ.2 hv
  simp only [wk_ub_subst_up]
  exact this

/-- the same for a type judgment under the binder, `B ≈ B' : sort v`. -/
theorem fundArm_cons_wk_sortg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    {k₀ : Nat} {Γ : LCtxA} {A B B' : ExprA} {v : Level}
    (h : ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (σ σ' : SubstA), Nonempty (CtxWfA E I n Δ) →
      ValidSubstAg E I n ρ₀ k Δ σ σ' (.assumption A :: Γ) →
      LREqAg E I n ρ₀ k Δ (substA σ (.sort v)) (substA σ' (.sort v)) ∧
      LRRelAg E I n ρ₀ k Δ (substA σ (.sort v)) (substA σ B) (substA σ' B'))
    {k : Nat} (hk : k₀ ≤ k) {Δ : LCtxA} {σ σ' : SubstA} (hσ : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (ρ : WkSpecA) (hρ : WkOkA E I n ρ Δ)
    (he : LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A)))
    {a a' : ExprA} (ha : LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) a a') :
    LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (.sort v)
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
      (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ'.up B'))) := by
  rw [wkExprA_substA, wkExprA_substA] at he
  rw [wkExprA_substA] at ha
  have hv := ValidSubstA_consg hEN (ValidSubstA_wkg hE hI hEN hNC hσ ρ hρ) he ha
  have := (h k hk _ _ _ hρ.2 hv).2
  simp only [wk_ub_subst_up]
  exact this

end IHWorld

/-! ## (7b) M2-g′: `sortP` content at any Prop-level sort; the structure of two pis -/

theorem LRRelA_sortP_elimg {k : Nat} {Γ : LCtxA} {u : Level} {A B : ExprA} (hz : isZero u = true)
    (h : LRRelAg E I n ρ₀ k Γ (.sort u) A B) :
    PropValidKA E I n Γ A ∧ PropValidKA E I n Γ B ∧ Nonempty (HasTyA E I n Γ A (.sort u)) ∧
    Nonempty (HasTyA E I n Γ B (.sort u)) ∧ Nonempty (ConvA E I n Γ A B (.sort u)) ∧
    PropEqA E I n Γ A B := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyA_eqg] at hR
  rcases tyKA_sort_invg hR with ⟨hz', _, _⟩ | ⟨_, e⟩
  · rw [hz] at hz'; cases hz'
  · subst e; exact hab

/-- THE CODOMAIN DATUM OF `PropEqA.pi` from the theorem: at every world `ρ` and every binder `D₀`
    convertible to the left substituted domain there, the two substituted codomains have the same
    structure — the IH on the codomain (a proposition) under the pair weakened into `ρ` and pushed
    under `D₀` (`ValidSubstA_upConvg`: variable `0` by reflection at the substituted domain). -/
theorem propEqA_codom_of_fundg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n)
    {k₀ : Nat} {Γ : LCtxA} {A B B' : ExprA} {v : Level} (hz : isZero v = true)
    (hB : ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (σ σ' : SubstA), Nonempty (CtxWfA E I n Δ) →
      ValidSubstAg E I n ρ₀ k Δ σ σ' (.assumption A :: Γ) →
      LREqAg E I n ρ₀ k Δ (substA σ (.sort v)) (substA σ' (.sort v)) ∧
      LRRelAg E I n ρ₀ k Δ (substA σ (.sort v)) (substA σ B) (substA σ' B'))
    {k : Nat} (hk : k₀ ≤ k) {Δ : LCtxA} {σ σ' : SubstA} (hσ : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (heA : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A))
    (hvA : ∃ R, LRTyAg E I n ρ₀ k Δ (substA σ A) R) :
    ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ D₀ : ExprA,
      Nonempty (CtxWfA E I n (.assumption D₀ :: wkCtxA ρ Δ)) →
      Nonempty (TyConvA E I n (wkCtxA ρ Δ) D₀ (wkExprA ρ (substA σ A))) →
      PropEqA E I n (.assumption D₀ :: wkCtxA ρ Δ)
        (wkExprA (WkSpecA.ub ρ) (substA σ.up B)) (wkExprA (WkSpecA.ub ρ) (substA σ'.up B')) := by
  intro ρ hρ D₀ hctx hD₀
  have hσρ := ValidSubstA_wkg hE hI hEN hNC hσ ρ hρ
  have heAρ := LREqA_wkg hE hNC hI heA ρ hρ
  have hvAρ : ∃ R, LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) R :=
    hvA.elim fun R hR => (LRTyA_wkg hE hNC hI hR ρ hρ).elim fun R' hR' => ⟨R', hR'.1⟩
  rw [wkExprA_substA, wkExprA_substA] at heAρ
  rw [wkExprA_substA] at hvAρ hD₀
  have hup := ValidSubstA_upConvg hE hI hEN hNC hIC hK hctx hσρ heAρ hvAρ hD₀
  have hBr := (hB k hk _ _ _ hctx hup).2
  rw [wkExprA_ub_substA_up, wkExprA_ub_substA_up]
  exact (LRRelA_sortP_elimg hz hBr).2.2.2.2.2

/-! ## (8) THE PI ARM (typing) -/

theorem hasTyArmPiA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n)
    (hρ : PosValA ρ₀) : HasTyArmPiAg E I n ρ₀ := fun Γ A u B v _ _ ihA ihB => by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kB, hB⟩ := ihB
  refine ⟨max (max kA kB) (ht ρ₀ (.imax u v) + 1), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkB : kB ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkh : ht ρ₀ (.imax u v) < k := le_max_of_le₂ hk
  refine ⟨LREqA_sort_reflg Δ hkh, ?_⟩
  -- the domain at Δ
  have hAΔ : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ A) (substA σ' A) := (hA k hkA Δ σ σ' hΔ hσ).2
  obtain ⟨heA, hvA, hvA', tA, tA', cA⟩ := LRRelA_sort_elimg hAΔ
  have heA' : LREqAg E I n ρ₀ k Δ (substA σ' A) (substA σ' A) := LREqA_transg hEN (LREqA_symmg hEN heA) heA
  -- the codomain in the extended contexts
  have hup := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ hσ heA hvA tA
  have hup' := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ (ValidSubstA_refl_rightg hEN hσ) heA' hvA' tA'
  have hΔA : Nonempty (CtxWfA E I n (.assumption (substA σ A) :: Δ)) :=
    hΔ.elim fun c => tA.elim fun t => ⟨.assumption c t⟩
  have hΔA' : Nonempty (CtxWfA E I n (.assumption (substA σ' A) :: Δ)) :=
    hΔ.elim fun c => tA'.elim fun t => ⟨.assumption c t⟩
  have hBΔ : LRRelAg E I n ρ₀ k (.assumption (substA σ A) :: Δ) (.sort v)
      (substA σ.up B) (substA σ'.up B) := (hB k hkB _ σ.up σ'.up hΔA hup).2
  have hBΔ' : LRRelAg E I n ρ₀ k (.assumption (substA σ' A) :: Δ) (.sort v)
      (substA σ'.up B) (substA σ'.up B) := (hB k hkB _ σ'.up σ'.up hΔA' hup').2
  obtain ⟨_, _, _, tB, _, cB⟩ := LRRelA_sort_elimg hBΔ
  obtain ⟨_, _, _, tB', _, _⟩ := LRRelA_sort_elimg hBΔ'
  -- the two pis, typed and convertible
  have tpi : Nonempty (HasTyA E I n Δ (.pi (substA σ A) u (substA σ.up B) v) (.sort (.imax u v))) :=
    tA.elim fun a => tB.elim fun b => ⟨.pi Δ _ u _ v a b⟩
  have tpi' : Nonempty (HasTyA E I n Δ (.pi (substA σ' A) u (substA σ'.up B) v) (.sort (.imax u v))) :=
    tA'.elim fun a => tB'.elim fun b => ⟨.pi Δ _ u _ v a b⟩
  have cpi : Nonempty (ConvA E I n Δ (.pi (substA σ A) u (substA σ.up B) v)
      (.pi (substA σ' A) u (substA σ'.up B) v) (.sort (.imax u v))) :=
    cA.elim fun a => cB.elim fun b => tpi'.elim fun t =>
      ⟨.pi Δ _ _ _ _ u u v v (eqNA_refl u) (eqNA_refl v) a b t⟩
  have hS : WhTyA E I n Δ (.sort (.imax u v)) (.sort (.imax u v)) := whTyA_of_hasTy (.sort Δ _)
  cases hz : isZero v with
  | true =>
      -- a propositional pi: the sortP relation
      have hz' : isZero (.imax u v) = true := by rw [isZero_imax]; exact hz
      refine ⟨_, by rw [LRTyA_eqg]; exact .sortP hS hz', ?_⟩
      refine ⟨⟨_, tpi.elim fun t => whTyA_of_hasTy t, hStepFnA_pi _ _ _ _ _ _ _,
        (isPropTy_pi_iff E I Δ _ u _ v).2 hz⟩,
        ⟨_, tpi'.elim fun t => whTyA_of_hasTy t, hStepFnA_pi _ _ _ _ _ _ _,
        (isPropTy_pi_iff E I Δ _ u _ v).2 hz⟩, tpi, tpi', cpi, ?_⟩
      -- M2-g′: the structure of the two pis
      exact .pi (tpi.elim fun t => whTyA_of_hasTy t) (tpi'.elim fun t => whTyA_of_hasTy t)
        (eqNA_refl u) (eqNA_refl v) tA tA'
        (fun ρ hρ' => tyConvA_wk_ne hE hI ρ hρ'.1 (tA.elim fun a => tA'.elim fun a' => cA.elim fun c =>
          ⟨.of Δ _ _ u u u a (eqNA_refl u) a' (eqNA_refl u) c⟩))
        (propEqA_codom_of_fundg hE hI hEN hNC hIC hK hz hB hkB hσ heA hvA)
        (tpi.elim fun t => tpi'.elim fun t' => cpi.elim fun c =>
          ⟨.of Δ _ _ _ _ _ t (eqNA_refl _) t' (eqNA_refl _) c⟩)
  | false =>
      have hvpos : 0 < ht ρ₀ v := ht_pos_of_isZero_false hρ v hz
      have hh : ht ρ₀ (.imax u v) = max (ht ρ₀ u) (ht ρ₀ v) := ht_imax_of_pos hvpos
      have hz' : isZero (.imax u v) = false := by rw [isZero_imax]; exact hz
      have hu_le : ht ρ₀ u ≤ ht ρ₀ (.imax u v) := by rw [hh]; exact Nat.le_max_left _ _
      have hv_le : ht ρ₀ v ≤ ht ρ₀ (.imax u v) := by rw [hh]; exact Nat.le_max_right _ _
      have hhk : ht ρ₀ (.imax u v) ≤ k := Nat.le_of_lt hkh
      -- world-indexed data at the pi's sort height
      have dA : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
          LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A)) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) R) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ' A)) R) :=
        fun ρ hρ' => (LRRelA_sort_elim'g (fundArm_sort_wkg hE hI hEN hNC hA hkA hσ ρ hρ')).1 _ hu_le
      have eA : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
          LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A)) :=
        fun ρ hρ' => LREqA_of_sortRelg (fundArm_sort_wkg hE hI hEN hNC hA hkA hσ ρ hρ')
      have eA' : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
          LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ' A)) (wkExprA ρ (substA σ' A)) :=
        fun ρ hρ' => LREqA_transg hEN (LREqA_symmg hEN (eA ρ hρ')) (eA ρ hρ')
      have eA0 : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
          LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ A)) :=
        fun ρ hρ' => LREqA_transg hEN (eA ρ hρ') (LREqA_symmg hEN (eA ρ hρ'))
      -- codomain data: both sides, at height h
      have dB : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA,
          LRRelAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) a a' →
          LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ'.up B))) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) R) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ'.up B))) R) :=
        fun ρ hρ' a a' haa => (LRRelA_sort_elim'g (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB hσ ρ hρ'
          (eA ρ hρ') (LRRelA_monog hhk haa))).1 _ hv_le
      -- same side, two arguments
      have dB0 : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA,
          LRRelAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) a a' →
          LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) :=
        fun ρ hρ' a a' haa => (LRRelA_sort_elim'g (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB
          (ValidSubstA_refl_leftg hEN hσ) ρ hρ' (eA0 ρ hρ') (LRRelA_monog hhk haa))).1 _ hv_le |>.1
      have dB' : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA,
          LRRelAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ' A)) a a' →
          LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ'.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ'.up B))) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ'.up B))) R) :=
        fun ρ hρ' a a' haa =>
          let r := (LRRelA_sort_elim'g (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB
            (ValidSubstA_refl_rightg hEN hσ) ρ hρ' (eA' ρ hρ') (LRRelA_monog hhk haa))).1 _ hv_le
          ⟨r.1, r.2.1⟩
      have tyc : Nonempty (TyConvA E I n Δ (.pi (substA σ A) u (substA σ.up B) v)
          (.pi (substA σ' A) u (substA σ'.up B) v)) :=
        tpi.elim fun t => tpi'.elim fun t' => cpi.elim fun c =>
          ⟨.of Δ _ _ _ _ _ t (eqNA_refl _) t' (eqNA_refl _) c⟩
      have hT1 : ∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA σ A) u (substA σ.up B) v) R :=
        tA.elim fun a => tB.elim fun b =>
          ⟨_, piTyA_of_datag hz a b (fun ρ hρ' => (dA ρ hρ').2.1)
            (fun ρ hρ' a a' haa => (dB ρ hρ' a a' haa).2.1) dB0⟩
      have hT2 : ∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA σ' A) u (substA σ'.up B) v) R :=
        tA'.elim fun a' => tB'.elim fun b' =>
          ⟨_, piTyA_of_datag hz a' b' (fun ρ hρ' => (dA ρ hρ').2.2)
            (fun ρ hρ' a a' haa => (dB' ρ hρ' a a' haa).2)
            (fun ρ hρ' a a' haa => (dB' ρ hρ' a a' haa).1)⟩
      have hEq : LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA σ A) u (substA σ.up B) v)
          (.pi (substA σ' A) u (substA σ'.up B) v) :=
        tA.elim fun a => tB.elim fun b => tA'.elim fun a' => tB'.elim fun b' =>
          piEqA_of_datag hEN (eqNA_refl _) (eqNA_refl _) a b a' b' (fun ρ hρ' => (dA ρ hρ').1)
            (fun ρ hρ' => (dA ρ hρ').2.1) (fun ρ hρ' a haa => (dB ρ hρ' a a haa).1) tyc
      refine ⟨_, by rw [LRTyA_eqg]; exact .sortT hS hz' hkh, ?_⟩
      exact ⟨hEq, hT1, hT2, tpi, tpi', cpi⟩

/-! ## (9) one more helper: the β-step at a world -/

/-! ## (10) THE LAM ARM (typing) -/

theorem hasTyArmLamA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n) :
    HasTyArmLamAg E I n ρ₀ := fun Γ A u body B v _ _ _ ihA ihB ihb => by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kB, hB⟩ := ihB
  obtain ⟨kb, hb⟩ := ihb
  refine ⟨max kA (max kB kb), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ hk
  have hkB : kB ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkb : kb ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  have hAΔ : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ A) (substA σ' A) := (hA k hkA Δ σ σ' hΔ hσ).2
  obtain ⟨heA, hvA, hvA', tA, tA', cA⟩ := LRRelA_sort_elimg hAΔ
  have heA' : LREqAg E I n ρ₀ k Δ (substA σ' A) (substA σ' A) := LREqA_transg hEN (LREqA_symmg hEN heA) heA
  have hup := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ hσ heA hvA tA
  have hup' := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ (ValidSubstA_refl_rightg hEN hσ) heA' hvA' tA'
  have hΔA : Nonempty (CtxWfA E I n (.assumption (substA σ A) :: Δ)) :=
    hΔ.elim fun c => tA.elim fun t => ⟨.assumption c t⟩
  have hΔA' : Nonempty (CtxWfA E I n (.assumption (substA σ' A) :: Δ)) :=
    hΔ.elim fun c => tA'.elim fun t => ⟨.assumption c t⟩
  have hBΔ : LRRelAg E I n ρ₀ k (.assumption (substA σ A) :: Δ) (.sort v)
      (substA σ.up B) (substA σ'.up B) := (hB k hkB _ σ.up σ'.up hΔA hup).2
  have hBΔ' : LRRelAg E I n ρ₀ k (.assumption (substA σ' A) :: Δ) (.sort v)
      (substA σ'.up B) (substA σ'.up B) := (hB k hkB _ σ'.up σ'.up hΔA' hup').2
  obtain ⟨_, _, _, tB, _, cB⟩ := LRRelA_sort_elimg hBΔ
  obtain ⟨_, _, _, tB', _, _⟩ := LRRelA_sort_elimg hBΔ'
  have hbΔ : LRRelAg E I n ρ₀ k (.assumption (substA σ A) :: Δ) (substA σ.up B)
      (substA σ.up body) (substA σ'.up body) := (hb k hkb _ σ.up σ'.up hΔA hup).2
  have hbΔ' : LRRelAg E I n ρ₀ k (.assumption (substA σ' A) :: Δ) (substA σ'.up B)
      (substA σ'.up body) (substA σ'.up body) := (hb k hkb _ σ'.up σ'.up hΔA' hup').2
  obtain ⟨tbody, _⟩ := LRRelA_hasTyg hbΔ
  obtain ⟨tbody', _⟩ := LRRelA_hasTyg hbΔ'
  have cbody := LRRelA_convg hbΔ
  have tpi : Nonempty (HasTyA E I n Δ (.pi (substA σ A) u (substA σ.up B) v) (.sort (.imax u v))) :=
    tA.elim fun a => tB.elim fun b => ⟨.pi Δ _ u _ v a b⟩
  have tpi' : Nonempty (HasTyA E I n Δ (.pi (substA σ' A) u (substA σ'.up B) v) (.sort (.imax u v))) :=
    tA'.elim fun a => tB'.elim fun b => ⟨.pi Δ _ u _ v a b⟩
  have cpi : Nonempty (ConvA E I n Δ (.pi (substA σ A) u (substA σ.up B) v)
      (.pi (substA σ' A) u (substA σ'.up B) v) (.sort (.imax u v))) :=
    cA.elim fun a => cB.elim fun b => tpi'.elim fun t =>
      ⟨.pi Δ _ _ _ _ u u v v (eqNA_refl u) (eqNA_refl v) a b t⟩
  have tyc : Nonempty (TyConvA E I n Δ (.pi (substA σ A) u (substA σ.up B) v)
      (.pi (substA σ' A) u (substA σ'.up B) v)) :=
    tpi.elim fun t => tpi'.elim fun t' => cpi.elim fun c =>
      ⟨.of Δ _ _ _ _ _ t (eqNA_refl _) t' (eqNA_refl _) c⟩
  have tlam : Nonempty (HasTyA E I n Δ (.lam (substA σ A) u (substA σ.up body))
      (.pi (substA σ A) u (substA σ.up B) v)) :=
    tA.elim fun a => tB.elim fun b => tbody.elim fun t => ⟨.lam Δ _ u _ _ v a b t⟩
  have tlam' : Nonempty (HasTyA E I n Δ (.lam (substA σ' A) u (substA σ'.up body))
      (.pi (substA σ A) u (substA σ.up B) v)) :=
    tA'.elim fun a => tB'.elim fun b => tbody'.elim fun t => tyc.elim fun c =>
      ⟨hasTyA_of_tyConvA (.lam Δ _ u _ _ v a b t) c.symm⟩
  have clam : Nonempty (ConvA E I n Δ (.lam (substA σ A) u (substA σ.up body))
      (.lam (substA σ' A) u (substA σ'.up body)) (.pi (substA σ A) u (substA σ.up B) v)) :=
    cA.elim fun a => cbody.elim fun c => tlam'.elim fun t => ⟨.lam Δ _ _ _ _ _ u u v (eqNA_refl u) a c t⟩
  have eA : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
      LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A)) :=
    fun ρ hρ' => LREqA_of_sortRelg (fundArm_sort_wkg hE hI hEN hNC hA hkA hσ ρ hρ')
  have eA0 : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
      LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ A)) :=
    fun ρ hρ' => LREqA_transg hEN (eA ρ hρ') (LREqA_symmg hEN (eA ρ hρ'))
  have vA : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
      ∃ R, LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) R :=
    fun ρ hρ' => (LRRelA_sort_elimg (fundArm_sort_wkg hE hI hEN hNC hA hkA hσ ρ hρ')).2.1
  have hEq : LREqAg E I n ρ₀ k Δ (.pi (substA σ A) u (substA σ.up B) v)
      (.pi (substA σ' A) u (substA σ'.up B) v) :=
    tA.elim fun a => tB.elim fun b => tA'.elim fun a' => tB'.elim fun b' =>
      piEqA_of_datag hEN (eqNA_refl _) (eqNA_refl _) a b a' b' eA vA
        (fun ρ hρ' x hxx => LREqA_of_sortRelg
          (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB hσ ρ hρ' (eA ρ hρ') hxx)) tyc
  refine ⟨hEq, ?_⟩
  cases hz : isZero v with
  | true =>
      have hnf : TripleLikeA E I Δ (.pi (substA σ A) u (substA σ.up B) v) :=
        tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _) ((isPropTy_pi_iff E I Δ _ u _ v).2 hz)
      have hwh : WhTyA E I n Δ (.pi (substA σ A) u (substA σ.up B) v) (.pi (substA σ A) u (substA σ.up B) v) :=
        tpi.elim fun t => whTyA_of_hasTy t
      refine ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hwh hnf.1 ((isPropTy_pi_iff E I Δ _ u _ v).2 hz), ?_⟩
      exact ⟨tlam, tlam', clam⟩
  | false =>
      have vB : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ x x' : ExprA,
          LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) x x' →
          ∃ R, LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) R :=
        fun ρ hρ' x x' hxx =>
          (LRRelA_sort_elimg (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB hσ ρ hρ' (eA ρ hρ') hxx)).2.1
      have eB0 : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ x x' : ExprA,
          LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) x x' →
          LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
            (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) :=
        fun ρ hρ' x x' hxx => LREqA_of_sortRelg
          (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB (ValidSubstA_refl_leftg hEN hσ) ρ hρ' (eA0 ρ hρ') hxx)
      refine tA.elim fun a => tB.elim fun b =>
        LRRelAg.of (piTyA_of_datag hz a b vA vB eB0) ⟨fun ρ hρ' x x' hxx => ?_, tlam, tlam', clam⟩
      have ih := fundArm_cons_wkg hE hI hEN hNC hb hkb hσ ρ hρ' (eA ρ hρ') hxx
      obtain ⟨tx, tx'⟩ := LRRelA_hasTyg hxx
      obtain ⟨tred, tred'⟩ := LRRelA_hasTyg ih.2
      obtain ⟨R₁, hR₁⟩ := LRRelA_validg ih.2
      obtain ⟨w₁, tTy⟩ := LRTyA_hasTyg hR₁
      obtain ⟨R₂, hR₂⟩ := LREqA_validg hEN ih.1 ⟨R₁, hR₁⟩
      obtain ⟨w₂, tTy'⟩ := LRTyA_hasTyg hR₂
      have tc := LREqA_tyConvg ih.1
      have tcA := LREqA_tyConvg (eA ρ hρ')
      have hsL : StepAtA E I n (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam (substA σ A) u (substA σ.up body))) x)
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up body)))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) :=
        tx.elim fun t => tred.elim fun r => tTy.elim fun ty => tbody.elim fun tb =>
          stepAtA_beta_wk hE hI a b tb ρ hρ' t r ty
      have hsR : StepAtA E I n (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam (substA σ' A) u (substA σ'.up body))) x')
          (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA σ'.up body)))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) :=
        tA'.elim fun a' => tB'.elim fun b' => tbody'.elim fun tb' => tx'.elim fun t' =>
          tred'.elim fun r' => tTy'.elim fun ty' => tc.elim fun c => tcA.elim fun cA' =>
          stepAtA_tyConv (stepAtA_beta_wk hE hI a' b' tb' ρ hρ' (hasTyA_of_tyConvA t' cA')
            (hasTyA_of_tyConvA r' c) ty') ⟨c.symm⟩
      exact LRRelA_expand_leftg hE hI hsL (LRRelA_expand_rightg hE hI hsR ih.2)

/-! ## (11) THE APP ARM (typing) -/

theorem hasTyArmAppA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n) :
    HasTyArmAppAg E I n ρ₀ := fun Γ f a A B u v w _ _ _ _ ihB ihTy ihf iha => by
  obtain ⟨kB, hB⟩ := ihB
  obtain ⟨kT, hT⟩ := ihTy
  obtain ⟨kf, hf⟩ := ihf
  obtain ⟨ka, ha⟩ := iha
  refine ⟨max (max kB kT) (max kf ka), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkB : kB ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkT : kT ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkf : kf ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hka : ka ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨_, hTT⟩ := hT k hkT Δ σ σ' hΔ hσ
  have heT : LREqAg E I n ρ₀ k Δ (substA σ (instantiate0A a B)) (substA σ' (instantiate0A a B)) :=
    LREqA_of_sortRelg hTT
  refine ⟨heT, ?_⟩
  obtain ⟨heA, haa⟩ := ha k hka Δ σ σ' hΔ hσ
  obtain ⟨hepi, hff⟩ := hf k hkf Δ σ σ' hΔ hσ
  rw [substA_instantiate0A]
  cases hz : isZero v with
  | false =>
      have hnp : ¬ IsPropTy E I Δ (.pi (substA σ A) u (substA σ.up B) v) := fun h => by
        rw [(isPropTy_pi_iff E I Δ _ u _ v).1 h] at hz; cases hz
      exact LRRelA_pi_elimg hff hnp [] ⟨trivial, hΔ⟩ (substA σ a) (substA σ' a) haa
  | true =>
      have hv := ValidSubstA_consg hEN hσ heA haa
      have hBc := (hB k hkB Δ (SubstA.cons (substA σ a) σ) (SubstA.cons (substA σ' a) σ') hΔ hv).2
      rw [← instantiate0A_substA_up, ← instantiate0A_substA_up] at hBc
      obtain ⟨⟨N, hNb, hnN, hPN⟩, _, _, _, _⟩ := LRRelA_sortP_elimg hz hBc
      obtain ⟨tf, tf'⟩ := LRRelA_hasTyg hff
      obtain ⟨ta, ta'⟩ := LRRelA_hasTyg haa
      have cf := LRRelA_convg hff
      have ca := LRRelA_convg haa
      obtain ⟨RA, hRA⟩ := LRRelA_validg haa
      obtain ⟨uA, tA⟩ := LRTyA_hasTyg hRA
      have hup := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ hσ heA ⟨RA, hRA⟩ tA
      have hΔA : Nonempty (CtxWfA E I n (.assumption (substA σ A) :: Δ)) :=
        hΔ.elim fun c => tA.elim fun t => ⟨.assumption c t⟩
      have hBup : LRRelAg E I n ρ₀ k (.assumption (substA σ A) :: Δ) (.sort v)
          (substA σ.up B) (substA σ'.up B) := (hB k hkB _ σ.up σ'.up hΔA hup).2
      obtain ⟨_, _, _, tB, _, _⟩ := LRRelA_sort_elimg hBup
      -- B typed in the σ' context as well
      have heA' : LREqAg E I n ρ₀ k Δ (substA σ' A) (substA σ' A) := LREqA_transg hEN (LREqA_symmg hEN heA) heA
      obtain ⟨RA', hRA'⟩ := LREqA_validg hEN heA ⟨RA, hRA⟩
      obtain ⟨uA', tA'⟩ := LRTyA_hasTyg hRA'
      have hup' := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ (ValidSubstA_refl_rightg hEN hσ) heA' ⟨RA', hRA'⟩ tA'
      have hΔA' : Nonempty (CtxWfA E I n (.assumption (substA σ' A) :: Δ)) :=
        hΔ.elim fun c => tA'.elim fun t => ⟨.assumption c t⟩
      have hBup' : LRRelAg E I n ρ₀ k (.assumption (substA σ' A) :: Δ) (.sort v)
          (substA σ'.up B) (substA σ'.up B) := (hB k hkB _ σ'.up σ'.up hΔA' hup').2
      obtain ⟨_, _, _, tB', _, _⟩ := LRRelA_sort_elimg hBup'
      obtain ⟨tTy, tTy'⟩ := LRRelA_hasTyg hTT
      rw [substA_instantiate0A] at tTy tTy'
      have tcpi := LREqA_tyConvg hepi
      have tcA := LREqA_tyConvg heA
      have tcT := LREqA_tyConvg heT
      rw [substA_instantiate0A, substA_instantiate0A] at tcT
      have tapp : Nonempty (HasTyA E I n Δ (.app (substA σ f) (substA σ a))
          (instantiate0A (substA σ a) (substA σ.up B))) :=
        tB.elim fun b => tTy.elim fun t => tf.elim fun x => ta.elim fun y => ⟨.app Δ _ _ _ _ u v w b t x y⟩
      have tapp' : Nonempty (HasTyA E I n Δ (.app (substA σ' f) (substA σ' a))
          (instantiate0A (substA σ a) (substA σ.up B))) :=
        tB'.elim fun b => tTy'.elim fun t => tf'.elim fun x => ta'.elim fun y => tcpi.elim fun cp =>
          tcA.elim fun cA => tcT.elim fun cT =>
          ⟨hasTyA_of_tyConvA (.app Δ _ _ _ _ u v w b t (hasTyA_of_tyConvA x cp) (hasTyA_of_tyConvA y cA)) cT.symm⟩
      have capp : Nonempty (ConvA E I n Δ (.app (substA σ f) (substA σ a)) (.app (substA σ' f) (substA σ' a))
          (instantiate0A (substA σ a) (substA σ.up B))) :=
        cf.elim fun c1 => ca.elim fun c2 => tB.elim fun b => tapp'.elim fun t =>
          ⟨.app Δ _ _ _ _ _ _ u v c1 c2 b t⟩
      -- W-APP at a `Prop` codomain closes through `prop`: the guarded `sortP` hands over the
      -- codomain's key-proposition (S1-g.1's K1, read off the clause)
      refine ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hNb hnN hPN, ?_⟩
      obtain ⟨tc⟩ := whTyA_tyConv hNb
      exact ⟨tapp.elim fun t => ⟨hasTyA_of_tyConvA t tc⟩, tapp'.elim fun t => ⟨hasTyA_of_tyConvA t tc⟩,
        capp.elim fun c => ⟨convA_of_tyConvA c tc⟩⟩

/-! ## (12) THE LETE ARM (typing) -/

theorem hasTyArmLetEA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) :
    HasTyArmLetEAg E I n ρ₀ :=
  fun Γ A u w value B body _ _ _ _ ihA ihv ihTy ihb => by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kv, hv⟩ := ihv
  obtain ⟨kT, hT⟩ := ihTy
  obtain ⟨kb, hb⟩ := ihb
  refine ⟨max (max kA kv) (max kT kb), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkv : kv ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkT : kT ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkb : kb ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨_, hTT⟩ := hT k hkT Δ σ σ' hΔ hσ
  have heT : LREqAg E I n ρ₀ k Δ (substA σ (instantiate0A value B)) (substA σ' (instantiate0A value B)) :=
    LREqA_of_sortRelg hTT
  refine ⟨heT, ?_⟩
  have hAΔ : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ A) (substA σ' A) := (hA k hkA Δ σ σ' hΔ hσ).2
  obtain ⟨heA, hvA, hvA', tA, tA', cA⟩ := LRRelA_sort_elimg hAΔ
  have heA' : LREqAg E I n ρ₀ k Δ (substA σ' A) (substA σ' A) := LREqA_transg hEN (LREqA_symmg hEN heA) heA
  obtain ⟨_, hvv⟩ := hv k hkv Δ σ σ' hΔ hσ
  have hvv' : LRRelAg E I n ρ₀ k Δ (substA σ' A) (substA σ' value) (substA σ' value) :=
    LRRelA_transport'g hEN heA (LRRelA_refl_leftg hEN (LRRelA_symmg hEN hvv))
  obtain ⟨tv, tv'⟩ := LRRelA_hasTyg hvv
  have hcons := ValidSubstA_consLetg hEN hσ heA hvv
  have hbc := (hb k hkb Δ _ _ hΔ hcons).2
  rw [← instantiate0A_substA_up, ← instantiate0A_substA_up, ← instantiate0A_substA_up] at hbc
  rw [substA_instantiate0A]
  have hupL := ValidSubstA_upLetg hE hI hEN hNC hΔ hσ heA hvv tA
  have hupL' := ValidSubstA_upLetg hE hI hEN hNC hΔ (ValidSubstA_refl_rightg hEN hσ) heA' hvv' tA'
  have hΔL : Nonempty (CtxWfA E I n (.letBinding (substA σ A) (substA σ value) :: Δ)) :=
    hΔ.elim fun c => tA.elim fun t => tv.elim fun x => ⟨.letBinding c t x⟩
  have tv'' : Nonempty (HasTyA E I n Δ (substA σ' value) (substA σ' A)) := (LRRelA_hasTyg hvv').1
  have hΔL' : Nonempty (CtxWfA E I n (.letBinding (substA σ' A) (substA σ' value) :: Δ)) :=
    hΔ.elim fun c => tA'.elim fun t => tv''.elim fun x => ⟨.letBinding c t x⟩
  have hbΔ := (hb k hkb _ σ.up σ'.up hΔL hupL).2
  have hbΔ' := (hb k hkb _ σ'.up σ'.up hΔL' hupL').2
  obtain ⟨tbody, _⟩ := LRRelA_hasTyg hbΔ
  obtain ⟨tbody', _⟩ := LRRelA_hasTyg hbΔ'
  obtain ⟨tTy, tTy'⟩ := LRRelA_hasTyg hTT
  rw [substA_instantiate0A] at tTy tTy'
  obtain ⟨tred, tred'⟩ := LRRelA_hasTyg hbc
  have tcT := LREqA_tyConvg heT
  rw [substA_instantiate0A, substA_instantiate0A] at tcT
  have hsL : StepAtA E I n Δ (.letE (substA σ A) (substA σ value) (substA σ.up body))
      (instantiate0A (substA σ value) (substA σ.up body))
      (instantiate0A (substA σ value) (substA σ.up B)) :=
    ⟨tA.elim fun a => tv.elim fun x => tTy.elim fun t => tbody.elim fun b => ⟨.letE Δ _ u w _ _ _ a x t b⟩,
     tA.elim fun a => tv.elim fun x => tbody.elim fun b => tred.elim fun r => ⟨.zeta Δ _ _ _ _ u a x b r⟩⟩
  have hsR : StepAtA E I n Δ (.letE (substA σ' A) (substA σ' value) (substA σ'.up body))
      (instantiate0A (substA σ' value) (substA σ'.up body))
      (instantiate0A (substA σ value) (substA σ.up B)) :=
    tA'.elim fun a => tv''.elim fun x => tTy'.elim fun t => tbody'.elim fun b => tred'.elim fun r =>
      tcT.elim fun c =>
      stepAtA_tyConv ⟨⟨.letE Δ _ u w _ _ _ a x t b⟩, ⟨.zeta Δ _ _ _ _ u a x b (hasTyA_of_tyConvA r c)⟩⟩ ⟨c.symm⟩
  exact LRRelA_expand_leftg hE hI hsL (LRRelA_expand_rightg hE hI hsR hbc)

/-! ## (13) the η-expansion: its body's typing and its β-reduct -/

/-! ## (14) THE BETA AND ZETA ARMS -/

theorem convArmBetaA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n) :
    ConvArmBetaAg E I n ρ₀ := fun Γ A u body arg B _ _ _ _ ihA ihb iha ihr => by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kb, hb⟩ := ihb
  obtain ⟨ka, ha⟩ := iha
  obtain ⟨kr, hr⟩ := ihr
  refine ⟨max (max kA kb) (max ka kr), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkb : kb ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hka : ka ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨heT, _⟩ := hr k hkr Δ σ σ' hΔ hσ
  refine ⟨heT, ?_⟩
  obtain ⟨heA, haa⟩ := ha k hka Δ σ σ' hΔ hσ
  have hAΔ : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ A) (substA σ' A) := (hA k hkA Δ σ σ' hΔ hσ).2
  obtain ⟨_, hvA, _, tA, _, _⟩ := LRRelA_sort_elimg hAΔ
  have hup := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ hσ heA hvA tA
  have hΔA : Nonempty (CtxWfA E I n (.assumption (substA σ A) :: Δ)) :=
    hΔ.elim fun c => tA.elim fun t => ⟨.assumption c t⟩
  have hbup := (hb k hkb _ σ.up σ'.up hΔA hup).2
  obtain ⟨tbody, _⟩ := LRRelA_hasTyg hbup
  obtain ⟨RB, hRB⟩ := LRRelA_validg hbup
  obtain ⟨v', tB⟩ := LRTyA_hasTyg hRB
  have hv := ValidSubstA_consg hEN hσ heA haa
  have hbc := (hb k hkb Δ _ _ hΔ hv).2
  rw [← instantiate0A_substA_up, ← instantiate0A_substA_up, ← instantiate0A_substA_up] at hbc
  obtain ⟨tred, _⟩ := LRRelA_hasTyg hbc
  obtain ⟨RT, hRT⟩ := LRRelA_validg hbc
  obtain ⟨w, tTy⟩ := LRTyA_hasTyg hRT
  obtain ⟨targ, _⟩ := LRRelA_hasTyg haa
  rw [substA_instantiate0A, substA_instantiate0A]
  have hs : StepAtA E I n Δ (.app (.lam (substA σ A) u (substA σ.up body)) (substA σ arg))
      (instantiate0A (substA σ arg) (substA σ.up body)) (instantiate0A (substA σ arg) (substA σ.up B)) :=
    tA.elim fun a => tB.elim fun b => tbody.elim fun tb => targ.elim fun ta => tred.elim fun tr =>
      tTy.elim fun ty => stepAtA_beta_wk hE hI a b tb [] ⟨trivial, hΔ⟩ ta tr ty
  exact LRRelA_expand_leftg hE hI hs hbc

theorem convArmZetaA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) :
    ConvArmZetaAg E I n ρ₀ :=
  fun Γ A value body B u _ _ _ _ ihA ihv ihb ihr => by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kv, hv⟩ := ihv
  obtain ⟨kb, hb⟩ := ihb
  obtain ⟨kr, hr⟩ := ihr
  refine ⟨max (max kA kv) (max kb kr), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkv : kv ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkb : kb ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨heT, _⟩ := hr k hkr Δ σ σ' hΔ hσ
  refine ⟨heT, ?_⟩
  have hAΔ : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ A) (substA σ' A) := (hA k hkA Δ σ σ' hΔ hσ).2
  obtain ⟨heA, _, _, tA, _, _⟩ := LRRelA_sort_elimg hAΔ
  obtain ⟨_, hvv⟩ := hv k hkv Δ σ σ' hΔ hσ
  obtain ⟨tv, _⟩ := LRRelA_hasTyg hvv
  have hupL := ValidSubstA_upLetg hE hI hEN hNC hΔ hσ heA hvv tA
  have hΔL : Nonempty (CtxWfA E I n (.letBinding (substA σ A) (substA σ value) :: Δ)) :=
    hΔ.elim fun c => tA.elim fun t => tv.elim fun x => ⟨.letBinding c t x⟩
  have hbL := (hb k hkb _ σ.up σ'.up hΔL hupL).2
  obtain ⟨tbody, _⟩ := LRRelA_hasTyg hbL
  have hcons := ValidSubstA_consLetg hEN hσ heA hvv
  have hbc := (hb k hkb Δ _ _ hΔ hcons).2
  rw [← instantiate0A_substA_up, ← instantiate0A_substA_up, ← instantiate0A_substA_up] at hbc
  obtain ⟨tred, _⟩ := LRRelA_hasTyg hbc
  obtain ⟨RT, hRT⟩ := LRRelA_validg hbc
  obtain ⟨w, tTy⟩ := LRTyA_hasTyg hRT
  rw [substA_instantiate0A, substA_instantiate0A]
  have hs : StepAtA E I n Δ (.letE (substA σ A) (substA σ value) (substA σ.up body))
      (instantiate0A (substA σ value) (substA σ.up body))
      (instantiate0A (substA σ value) (substA σ.up B)) :=
    ⟨tA.elim fun a => tv.elim fun x => tTy.elim fun t => tbody.elim fun b => ⟨.letE Δ _ u w _ _ _ a x t b⟩,
     tA.elim fun a => tv.elim fun x => tbody.elim fun b => tred.elim fun r => ⟨.zeta Δ _ _ _ _ u a x b r⟩⟩
  exact LRRelA_expand_leftg hE hI hs hbc

/-! ## (15) THE APP ARM (conversion) -/

theorem convArmAppA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n) :
    ConvArmAppAg E I n ρ₀ := fun Γ f g a b A B u v _ _ _ _ ihfg ihab ihB ihrt => by
  obtain ⟨kf, hf⟩ := ihfg
  obtain ⟨ka, ha⟩ := ihab
  obtain ⟨kB, hB⟩ := ihB
  obtain ⟨kr, hr⟩ := ihrt
  refine ⟨max (max kf ka) (max kB kr), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkf : kf ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hka : ka ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkB : kB ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨heT, _⟩ := hr k hkr Δ σ σ' hΔ hσ
  refine ⟨heT, ?_⟩
  obtain ⟨hepi, hfg⟩ := hf k hkf Δ σ σ' hΔ hσ
  obtain ⟨heA, hab⟩ := ha k hka Δ σ σ' hΔ hσ
  rw [substA_instantiate0A]
  cases hz : isZero v with
  | false =>
      have hnp : ¬ IsPropTy E I Δ (.pi (substA σ A) u (substA σ.up B) v) := fun h => by
        rw [(isPropTy_pi_iff E I Δ _ u _ v).1 h] at hz; cases hz
      exact LRRelA_pi_elimg hfg hnp [] ⟨trivial, hΔ⟩ (substA σ a) (substA σ' b) hab
  | true =>
      have hv := ValidSubstA_consg hEN hσ heA hab
      have hBc := (hB k hkB Δ _ _ hΔ hv).2
      simp only [substA_sort, ← instantiate0A_substA_up] at hBc
      obtain ⟨⟨N, hNb, hnN, hPN⟩, _, tTy, tTy', _⟩ := LRRelA_sortP_elimg hz hBc
      have heBc := LREqA_of_sortRelg hBc
      obtain ⟨tf, tg⟩ := LRRelA_hasTyg hfg
      obtain ⟨ta, tb⟩ := LRRelA_hasTyg hab
      have cfg := LRRelA_convg hfg
      have cab := LRRelA_convg hab
      obtain ⟨RA, hRA⟩ := LRRelA_validg hab
      obtain ⟨uA, tA⟩ := LRTyA_hasTyg hRA
      have hup := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ hσ heA ⟨RA, hRA⟩ tA
      have hΔA : Nonempty (CtxWfA E I n (.assumption (substA σ A) :: Δ)) :=
        hΔ.elim fun c => tA.elim fun t => ⟨.assumption c t⟩
      have hBup : LRRelAg E I n ρ₀ k (.assumption (substA σ A) :: Δ) (.sort v)
          (substA σ.up B) (substA σ'.up B) := (hB k hkB _ σ.up σ'.up hΔA hup).2
      obtain ⟨_, _, _, tB, _, _⟩ := LRRelA_sort_elimg hBup
      have heA' : LREqAg E I n ρ₀ k Δ (substA σ' A) (substA σ' A) := LREqA_transg hEN (LREqA_symmg hEN heA) heA
      obtain ⟨RA', hRA'⟩ := LREqA_validg hEN heA ⟨RA, hRA⟩
      obtain ⟨uA', tA'⟩ := LRTyA_hasTyg hRA'
      have hup' := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ (ValidSubstA_refl_rightg hEN hσ) heA' ⟨RA', hRA'⟩ tA'
      have hΔA' : Nonempty (CtxWfA E I n (.assumption (substA σ' A) :: Δ)) :=
        hΔ.elim fun c => tA'.elim fun t => ⟨.assumption c t⟩
      have hBup' : LRRelAg E I n ρ₀ k (.assumption (substA σ' A) :: Δ) (.sort v)
          (substA σ'.up B) (substA σ'.up B) := (hB k hkB _ σ'.up σ'.up hΔA' hup').2
      obtain ⟨_, _, _, tB', _, _⟩ := LRRelA_sort_elimg hBup'
      have tcpi := LREqA_tyConvg hepi
      have tcA := LREqA_tyConvg heA
      have tcBc := LREqA_tyConvg heBc
      have tapp : Nonempty (HasTyA E I n Δ (.app (substA σ f) (substA σ a))
          (instantiate0A (substA σ a) (substA σ.up B))) :=
        tB.elim fun b' => tTy.elim fun t => tf.elim fun x => ta.elim fun y => ⟨.app Δ _ _ _ _ u v v b' t x y⟩
      have tapp' : Nonempty (HasTyA E I n Δ (.app (substA σ' g) (substA σ' b))
          (instantiate0A (substA σ a) (substA σ.up B))) :=
        tB'.elim fun b' => tTy'.elim fun t => tg.elim fun x => tb.elim fun y => tcpi.elim fun cp =>
          tcA.elim fun cA => tcBc.elim fun cB =>
          ⟨hasTyA_of_tyConvA (.app Δ _ _ _ _ u v v b' t (hasTyA_of_tyConvA x cp) (hasTyA_of_tyConvA y cA)) cB.symm⟩
      have capp : Nonempty (ConvA E I n Δ (.app (substA σ f) (substA σ a)) (.app (substA σ' g) (substA σ' b))
          (instantiate0A (substA σ a) (substA σ.up B))) :=
        cfg.elim fun c1 => cab.elim fun c2 => tB.elim fun b' => tapp'.elim fun t =>
          ⟨.app Δ _ _ _ _ _ _ u v c1 c2 b' t⟩
      -- W-APP at a `Prop` codomain closes through `prop`: the guarded `sortP` hands over the
      -- codomain's key-proposition (S1-g.1's K1, read off the clause)
      refine ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hNb hnN hPN, ?_⟩
      obtain ⟨tc⟩ := whTyA_tyConv hNb
      exact ⟨tapp.elim fun t => ⟨hasTyA_of_tyConvA t tc⟩, tapp'.elim fun t => ⟨hasTyA_of_tyConvA t tc⟩,
        capp.elim fun c => ⟨convA_of_tyConvA c tc⟩⟩

/-! ## (16) THE ETA ARM -/

theorem convArmEtaA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) :
    ConvArmEtaAg E I n ρ₀ :=
  fun Γ f A B u v _ _ ih ihrt => by
  obtain ⟨kf, hf⟩ := ih
  obtain ⟨kl, hl⟩ := ihrt
  refine ⟨max kf kl, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  obtain ⟨hepi, hff⟩ := hf k (le_max_of_le₁ hk) Δ σ σ' hΔ hσ
  obtain ⟨_, hll⟩ := hl k (le_max_of_le₂ hk) Δ σ σ' hΔ hσ
  refine ⟨hepi, ?_⟩
  have elam : ∀ τ : SubstA, substA τ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) =
      .lam (substA τ A) u (.app (liftA 0 1 (substA τ f)) (.bvar 0)) := fun τ => by
    simp only [substA_lam, substA_app, substA_up_liftA, substA_bvar, SubstA.up_zero]
  simp only [elam] at hll ⊢
  obtain ⟨tf, tf'⟩ := LRRelA_hasTyg hff
  obtain ⟨tlam, _⟩ := LRRelA_hasTyg hll
  have cff := LRRelA_convg hff
  obtain ⟨Rpi, hRpi⟩ := LRRelA_validg hff
  obtain ⟨upi, tpi⟩ := LRTyA_hasTyg hRpi
  have hAB := tpi.elim fun t => hasTyA_pi_inv t
  obtain ⟨tA, tB⟩ := hAB
  have ceta : Nonempty (ConvA E I n Δ (.lam (substA σ A) u (.app (liftA 0 1 (substA σ f)) (.bvar 0)))
      (substA σ' f) (.pi (substA σ A) u (substA σ.up B) v)) :=
    tf.elim fun x => tlam.elim fun l => cff.elim fun c => ⟨.trans Δ _ _ _ _ (.eta Δ _ _ _ u v x l) c⟩
  cases hz : isZero v with
  | true =>
      have hnf : TripleLikeA E I Δ (.pi (substA σ A) u (substA σ.up B) v) :=
        tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _) ((isPropTy_pi_iff E I Δ _ u _ v).2 hz)
      have hwh : WhTyA E I n Δ (.pi (substA σ A) u (substA σ.up B) v) (.pi (substA σ A) u (substA σ.up B) v) :=
        tpi.elim fun t => whTyA_of_hasTy t
      refine ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hwh hnf.1 ((isPropTy_pi_iff E I Δ _ u _ v).2 hz), ?_⟩
      exact ⟨tlam, tf', ceta⟩
  | false =>
      have hnp : ¬ IsPropTy E I Δ (.pi (substA σ A) u (substA σ.up B) v) := fun h => by
        rw [(isPropTy_pi_iff E I Δ _ u _ v).1 h] at hz; cases hz
      rw [LRTyA_eqg] at hRpi
      obtain ⟨RD, RC, hD, hC, _, e⟩ := tyKA_pi_invg hRpi hnp
      subst e
      have hRpi' : LRTyAg E I n ρ₀ k Δ (.pi (substA σ A) u (substA σ.up B) v) (fun f g =>
          (∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA, RD ρ a a' →
            RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
          Nonempty (HasTyA E I n Δ f (.pi (substA σ A) u (substA σ.up B) v)) ∧
          Nonempty (HasTyA E I n Δ g (.pi (substA σ A) u (substA σ.up B) v)) ∧
          Nonempty (ConvA E I n Δ f g (.pi (substA σ A) u (substA σ.up B) v))) := by
        rw [LRTyA_eqg]; exact hRpi
      refine LRRelAg.of hRpi' ⟨fun ρ hρ x x' hx => ?_, tlam, tf', ceta⟩
      have hK := (hff.at hRpi').1 ρ hρ x x' hx
      have hCx : LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
          (RC ρ x) := by rw [LRTyA_eqg]; exact hC ρ hρ x x' hx
      have hDx : LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (RD ρ) := by
        rw [LRTyA_eqg]; exact hD ρ hρ
      have hxx : LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) x x' := LRRelAg.of hDx hx
      obtain ⟨tx, _⟩ := LRRelA_hasTyg hxx
      have hK' : LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
          (.app (wkExprA ρ (substA σ f)) x) (.app (wkExprA ρ (substA σ' f)) x') := LRRelAg.of hCx hK
      obtain ⟨tred, _⟩ := LRRelA_hasTyg hK'
      obtain ⟨w, tTy⟩ := LRTyA_hasTyg hCx
      have tbody : Nonempty (HasTyA E I n (.assumption (substA σ A) :: Δ)
          (.app (liftA 0 1 (substA σ f)) (.bvar 0)) (substA σ.up B)) :=
        tA.elim fun a => tB.elim fun b => tf.elim fun x => ⟨hasTyA_eta_body hE hI a b x⟩
      have tred' : Nonempty (HasTyA E I n (wkCtxA ρ Δ)
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (.app (liftA 0 1 (substA σ f)) (.bvar 0))))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))) := by
        rw [eta_body_inst]; exact tred
      have hs : StepAtA E I n (wkCtxA ρ Δ)
          (.app (wkExprA ρ (.lam (substA σ A) u (.app (liftA 0 1 (substA σ f)) (.bvar 0)))) x)
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (.app (liftA 0 1 (substA σ f)) (.bvar 0))))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) :=
        tA.elim fun a => tB.elim fun b => tbody.elim fun tb => tx.elim fun t => tred'.elim fun r =>
          tTy.elim fun ty => stepAtA_beta_wk hE hI a b tb ρ hρ t r ty
      have hK'' : LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (.app (liftA 0 1 (substA σ f)) (.bvar 0))))
          (.app (wkExprA ρ (substA σ' f)) x') := by
        rw [eta_body_inst]; exact hK'
      exact (LRRelA_expand_leftg hE hI hs hK'').at hCx

/-! ## (17) a valid pair under a CONVERTIBLE domain; generation for `letE`; the β-step given the redex -/

/-- into the extended target context whose binder is any type convertible to the
    substituted domain (the two sides of a domain conversion). -/
theorem ValidSubstA_up'g (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n)
    {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA} {A D : ExprA} {u : Level}
    (hΔ : Nonempty (CtxWfA E I n Δ))
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (he : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A))
    (heD : LREqAg E I n ρ₀ k Δ D (substA σ A))
    (hvD : ∃ R, LRTyAg E I n ρ₀ k Δ D R)
    (htD : Nonempty (HasTyA E I n Δ D (.sort u))) :
    ValidSubstAg E I n ρ₀ k (.assumption D :: Δ) σ.up σ'.up (.assumption A :: Γ) :=
  ValidSubstA_upConvg hE hI hEN hNC hIC hK (hΔ.elim fun c => htD.elim fun t => ⟨.assumption c t⟩) h he
    (LREqA_validg hEN heD hvD) (LREqA_tyConvg heD)

/-- extension of a valid pair under a let binder by the value on the left and anything
    related to it on the right. -/
theorem ValidSubstA_consLet'g (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA} {A v a' : ExprA}
    (h : ValidSubstAg E I n ρ₀ k Δ σ σ' Γ)
    (he : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A))
    (ha : LRRelAg E I n ρ₀ k Δ (substA σ A) (substA σ v) a')
    (hv : LRRelAg E I n ρ₀ k Δ (substA σ A) (substA σ v) (substA σ' v)) :
    ValidSubstAg E I n ρ₀ k Δ (SubstA.cons (substA σ v) σ) (SubstA.cons a' σ') (.letBinding A v :: Γ) := by
  refine ⟨fun i B hB => ?_, fun i B w hB hw => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        cases hB
        simp only [substA_cons_liftA]
        exact ⟨he, ha⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            simp only [substA_cons_liftA]
            exact h.1 i A' hΓ
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        rw [lookupValueA_cons_zero_let] at hw
        cases hB; cases hw
        simp only [substA_cons_liftA]
        exact ⟨LRRelA_refl_leftg hEN hv, hv⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hw
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hw; cases hw
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hw
              cases hB; cases hw
              simp only [substA_cons_liftA]
              exact h.2 i A' v' hΓ hΓv

/-! ## (18) THE PI ARM (conversion) -/

theorem convArmPiA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n)
    (hρ : PosValA ρ₀) : ConvArmPiAg E I n ρ₀ := fun Γ A A' B B' u u' v v' hu hv _ _ _ ihA ihB ihrt => by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kB, hB⟩ := ihB
  obtain ⟨kr, hr⟩ := ihrt
  refine ⟨max (max kA kB) (max kr (ht ρ₀ (.imax u v) + 1)), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkB : kB ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkr : kr ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkh : ht ρ₀ (.imax u v) < k := le_max_of_le₂ (le_max_of_le₂ hk)
  refine ⟨LREqA_sort_reflg Δ hkh, ?_⟩
  have hAΔ : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ A) (substA σ' A') := (hA k hkA Δ σ σ' hΔ hσ).2
  have hAΔ' : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ' A) (substA σ' A') :=
    (hA k hkA Δ σ' σ' hΔ (ValidSubstA_refl_rightg hEN hσ)).2
  obtain ⟨heAA', hvA, hvA'', tA, tA'', cAA'⟩ := LRRelA_sort_elimg hAΔ
  obtain ⟨heA'A', hvA', _, _, _, _⟩ := LRRelA_sort_elimg hAΔ'
  have heA : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A) := LREqA_transg hEN heAA' (LREqA_symmg hEN heA'A')
  have heA' : LREqAg E I n ρ₀ k Δ (substA σ' A) (substA σ' A) := LREqA_transg hEN (LREqA_symmg hEN heA) heA
  have heD : LREqAg E I n ρ₀ k Δ (substA σ' A') (substA σ' A) := LREqA_symmg hEN heA'A'
  have hup := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ hσ heA hvA tA
  have hup' := ValidSubstA_up'g hE hI hEN hNC hIC hK hΔ (ValidSubstA_refl_rightg hEN hσ) heA' heD hvA'' tA''
  have hΔA : Nonempty (CtxWfA E I n (.assumption (substA σ A) :: Δ)) :=
    hΔ.elim fun c => tA.elim fun t => ⟨.assumption c t⟩
  have hΔA'' : Nonempty (CtxWfA E I n (.assumption (substA σ' A') :: Δ)) :=
    hΔ.elim fun c => tA''.elim fun t => ⟨.assumption c t⟩
  have hBΔ : LRRelAg E I n ρ₀ k (.assumption (substA σ A) :: Δ) (.sort v)
      (substA σ.up B) (substA σ'.up B') := (hB k hkB _ σ.up σ'.up hΔA hup).2
  have hBΔ' : LRRelAg E I n ρ₀ k (.assumption (substA σ' A') :: Δ) (.sort v)
      (substA σ'.up B) (substA σ'.up B') := (hB k hkB _ σ'.up σ'.up hΔA'' hup').2
  obtain ⟨_, _, _, tB, _, cB⟩ := LRRelA_sort_elimg hBΔ
  obtain ⟨_, _, _, _, tB', _⟩ := LRRelA_sort_elimg hBΔ'
  have tpi : Nonempty (HasTyA E I n Δ (.pi (substA σ A) u (substA σ.up B) v) (.sort (.imax u v))) :=
    tA.elim fun a => tB.elim fun b => ⟨.pi Δ _ u _ v a b⟩
  -- the right pi, at the LEFT's sort: the arm's own typing hypothesis, read at the pair
  have tpi' : Nonempty (HasTyA E I n Δ (.pi (substA σ' A') u' (substA σ'.up B') v') (.sort (.imax u v))) :=
    (LRRelA_hasTyg (hr k hkr Δ σ σ' hΔ hσ).2).2
  -- its components at THEIR sorts (`=ₙ` to the left's)
  have tA''u : Nonempty (HasTyA E I n Δ (substA σ' A') (.sort u')) :=
    tA''.elim fun a => ⟨hasTyA_of_tyConvA a (tyConvA_sorts Δ hu)⟩
  have tB'v : Nonempty (HasTyA E I n (.assumption (substA σ' A') :: Δ) (substA σ'.up B') (.sort v')) :=
    tB'.elim fun b => ⟨hasTyA_of_tyConvA b (tyConvA_sorts _ hv)⟩
  have cpi : Nonempty (ConvA E I n Δ (.pi (substA σ A) u (substA σ.up B) v)
      (.pi (substA σ' A') u' (substA σ'.up B') v') (.sort (.imax u v))) :=
    cAA'.elim fun a => cB.elim fun b => tpi'.elim fun t => ⟨.pi Δ _ _ _ _ u u' v v' hu hv a b t⟩
  have tyc : Nonempty (TyConvA E I n Δ (.pi (substA σ A) u (substA σ.up B) v)
      (.pi (substA σ' A') u' (substA σ'.up B') v')) :=
    tpi.elim fun t => tpi'.elim fun t' => cpi.elim fun c =>
      ⟨.of Δ _ _ _ _ _ t (eqNA_refl _) t' (eqNA_refl _) c⟩
  have hS : WhTyA E I n Δ (.sort (.imax u v)) (.sort (.imax u v)) := whTyA_of_hasTy (.sort Δ _)
  have hzv : isZero v' = isZero v := (isZero_eqN hv).symm
  cases hz : isZero v with
  | true =>
      have hz' : isZero (.imax u v) = true := by rw [isZero_imax]; exact hz
      have hzv' : isZero v' = true := by rw [hzv]; exact hz
      refine ⟨_, by rw [LRTyA_eqg]; exact .sortP hS hz', ?_⟩
      refine ⟨⟨_, tpi.elim fun t => whTyA_of_hasTy t, hStepFnA_pi _ _ _ _ _ _ _,
        (isPropTy_pi_iff E I Δ _ u _ v).2 hz⟩,
        ⟨_, tpi'.elim fun t => whTyA_of_hasTy t, hStepFnA_pi _ _ _ _ _ _ _,
        (isPropTy_pi_iff E I Δ _ u' _ v').2 hzv'⟩, tpi, tpi', cpi, ?_⟩
      -- M2-g′: the structure of the two pis
      exact .pi (tpi.elim fun t => whTyA_of_hasTy t) (tpi'.elim fun t => whTyA_of_hasTy t) hu hv tA tA''u
        (fun ρ hρ' => tyConvA_wk_ne hE hI ρ hρ'.1 (tA.elim fun a => tA''.elim fun a' => cAA'.elim fun c =>
          ⟨.of Δ _ _ u u u a (eqNA_refl u) a' (eqNA_refl u) c⟩))
        (propEqA_codom_of_fundg hE hI hEN hNC hIC hK hz hB hkB hσ heA hvA) tyc
  | false =>
      have hzv' : isZero v' = false := by rw [hzv]; exact hz
      have hvpos : 0 < ht ρ₀ v := ht_pos_of_isZero_false hρ v hz
      have hh : ht ρ₀ (.imax u v) = max (ht ρ₀ u) (ht ρ₀ v) := ht_imax_of_pos hvpos
      have hz' : isZero (.imax u v) = false := by rw [isZero_imax]; exact hz
      have hu_le : ht ρ₀ u ≤ ht ρ₀ (.imax u v) := by rw [hh]; exact Nat.le_max_left _ _
      have hv_le : ht ρ₀ v ≤ ht ρ₀ (.imax u v) := by rw [hh]; exact Nat.le_max_right _ _
      have hhk : ht ρ₀ (.imax u v) ≤ k := Nat.le_of_lt hkh
      -- world data for the domains
      have wAA' := fun (ρ : WkSpecA) (hρ' : WkOkA E I n ρ Δ) => fundArm_sort_wkg hE hI hEN hNC hA hkA hσ ρ hρ'
      have wA'A' := fun (ρ : WkSpecA) (hρ' : WkOkA E I n ρ Δ) =>
        fundArm_sort_wkg hE hI hEN hNC hA hkA (ValidSubstA_refl_rightg hEN hσ) ρ hρ'
      have eA : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
          LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A)) :=
        fun ρ hρ' => LREqA_transg hEN (LREqA_of_sortRelg (wAA' ρ hρ')) (LREqA_symmg hEN (LREqA_of_sortRelg (wA'A' ρ hρ')))
      have eA0 : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
          LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ A)) :=
        fun ρ hρ' => LREqA_transg hEN (eA ρ hρ') (LREqA_symmg hEN (eA ρ hρ'))
      have eA' : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
          LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ' A)) (wkExprA ρ (substA σ' A)) :=
        fun ρ hρ' => LREqA_transg hEN (LREqA_symmg hEN (eA ρ hρ')) (eA ρ hρ')
      have dA : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
          LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A')) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) R) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ' A')) R) :=
        fun ρ hρ' => (LRRelA_sort_elim'g (wAA' ρ hρ')).1 _ hu_le
      -- codomain data
      have dB : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA,
          LRRelAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) a a' →
          LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ'.up B'))) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) R) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ'.up B'))) R) :=
        fun ρ hρ' a a' haa => (LRRelA_sort_elim'g (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB hσ ρ hρ'
          (eA ρ hρ') (LRRelA_monog hhk haa))).1 _ hv_le
      -- same substitution σ, two arguments: B[a] ≡ B[a'] through B'
      have dB0 : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA,
          LRRelAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) a a' →
          LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) :=
        fun ρ hρ' a a' haa =>
          let r1 := ((LRRelA_sort_elim'g (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB (ValidSubstA_refl_leftg hEN hσ) ρ hρ'
            (eA0 ρ hρ') (LRRelA_monog hhk haa))).1 _ hv_le).1
          let r2 := ((LRRelA_sort_elim'g (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB (ValidSubstA_refl_leftg hEN hσ) ρ hρ'
            (eA0 ρ hρ') (LRRelA_monog hhk (LRRelA_refl_leftg hEN (LRRelA_symmg hEN haa))))).1 _ hv_le).1
          LREqA_transg hEN r1 (LREqA_symmg hEN r2)
      -- same substitution σ', two arguments, for B'
      have dB' : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA,
          LRRelAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA σ' A')) a a' →
          LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ'.up B')))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA σ'.up B'))) ∧
          (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA σ'.up B'))) R) :=
        fun ρ hρ' a a' haa =>
          let haa0 : LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ' A)) a a' :=
            LRRelA_transport'g hEN (LREqA_symmg hEN (LREqA_of_sortRelg (wA'A' ρ hρ'))) (LRRelA_monog hhk haa)
          let haa1 : LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ' A)) a a :=
            LRRelA_refl_leftg hEN haa0
          let r1 := (LRRelA_sort_elim'g (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB (ValidSubstA_refl_rightg hEN hσ) ρ hρ'
            (eA' ρ hρ') haa0)).1 _ hv_le
          let r2 := (LRRelA_sort_elim'g (fundArm_cons_wk_sortg hE hI hEN hNC hB hkB (ValidSubstA_refl_rightg hEN hσ) ρ hρ'
            (eA' ρ hρ') haa1)).1 _ hv_le
          ⟨LREqA_transg hEN (LREqA_symmg hEN r2.1) r1.1, r2.2.2⟩
      have hT1 : ∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA σ A) u (substA σ.up B) v) R :=
        tA.elim fun a => tB.elim fun b =>
          ⟨_, piTyA_of_datag hz a b (fun ρ hρ' => (dA ρ hρ').2.1)
            (fun ρ hρ' a a' haa => (dB ρ hρ' a a' haa).2.1) dB0⟩
      have hT2 : ∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA σ' A') u' (substA σ'.up B') v') R :=
        tA''u.elim fun a' => tB'v.elim fun b' =>
          ⟨_, piTyA_of_datag hzv' a' b' (fun ρ hρ' => (dA ρ hρ').2.2)
            (fun ρ hρ' a a' haa => (dB' ρ hρ' a a' haa).2)
            (fun ρ hρ' a a' haa => (dB' ρ hρ' a a' haa).1)⟩
      have hEq : LREqAg E I n ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA σ A) u (substA σ.up B) v)
          (.pi (substA σ' A') u' (substA σ'.up B') v') :=
        tA.elim fun a => tB.elim fun b => tA''u.elim fun a' => tB'v.elim fun b' =>
          piEqA_of_datag hEN hu hv a b a' b' (fun ρ hρ' => (dA ρ hρ').1) (fun ρ hρ' => (dA ρ hρ').2.1)
            (fun ρ hρ' a haa => (dB ρ hρ' a a haa).1) tyc
      refine ⟨_, by rw [LRTyA_eqg]; exact .sortT hS hz' hkh, ?_⟩
      exact ⟨hEq, hT1, hT2, tpi, tpi', cpi⟩

/-! ## (19) THE LAM ARM (conversion) -/

theorem convArmLamA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIC : IotaConstHeadA I) (hK : PropKeyA E I n) :
    ConvArmLamAg E I n ρ₀ := fun Γ A A' b b' B u u' v hu _ _ _ ihA ihb ihrt => by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kb, hb⟩ := ihb
  obtain ⟨kr, hr⟩ := ihrt
  refine ⟨max kA (max kb kr), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ hk
  have hkb : kb ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨hepi, hll⟩ := hr k hkr Δ σ σ' hΔ hσ
  refine ⟨hepi, ?_⟩
  have hAΔ : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ A) (substA σ' A') := (hA k hkA Δ σ σ' hΔ hσ).2
  have hAΔ' : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ' A) (substA σ' A') :=
    (hA k hkA Δ σ' σ' hΔ (ValidSubstA_refl_rightg hEN hσ)).2
  obtain ⟨heAA', hvA, hvA'', tA, tA'', cAA'⟩ := LRRelA_sort_elimg hAΔ
  obtain ⟨heA'A', _, _, _, _, _⟩ := LRRelA_sort_elimg hAΔ'
  have heA : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A) := LREqA_transg hEN heAA' (LREqA_symmg hEN heA'A')
  -- the pi's components
  obtain ⟨Rpi, hRpi⟩ := LRRelA_validg hll
  obtain ⟨upi, tpi⟩ := LRTyA_hasTyg hRpi
  obtain ⟨_, tB⟩ := tpi.elim fun t => hasTyA_pi_inv t
  -- the bodies, in both extended contexts
  have hup := ValidSubstA_upg hE hI hEN hNC hIC hK hΔ hσ heA hvA tA
  have hup' := ValidSubstA_up'g hE hI hEN hNC hIC hK hΔ hσ heA (LREqA_symmg hEN heAA') hvA'' tA''
  have hΔA : Nonempty (CtxWfA E I n (.assumption (substA σ A) :: Δ)) :=
    hΔ.elim fun c => tA.elim fun t => ⟨.assumption c t⟩
  have hΔA'' : Nonempty (CtxWfA E I n (.assumption (substA σ' A') :: Δ)) :=
    hΔ.elim fun c => tA''.elim fun t => ⟨.assumption c t⟩
  have hbΔ : LRRelAg E I n ρ₀ k (.assumption (substA σ A) :: Δ) (substA σ.up B)
      (substA σ.up b) (substA σ'.up b') := (hb k hkb _ σ.up σ'.up hΔA hup).2
  have hbΔ' : LRRelAg E I n ρ₀ k (.assumption (substA σ' A') :: Δ) (substA σ.up B)
      (substA σ.up b) (substA σ'.up b') := (hb k hkb _ σ.up σ'.up hΔA'' hup').2
  obtain ⟨tb, _⟩ := LRRelA_hasTyg hbΔ
  obtain ⟨_, tb'⟩ := LRRelA_hasTyg hbΔ'
  have cb := LRRelA_convg hbΔ
  have tlam : Nonempty (HasTyA E I n Δ (.lam (substA σ A) u (substA σ.up b))
      (.pi (substA σ A) u (substA σ.up B) v)) :=
    tA.elim fun a => tB.elim fun b₀ => tb.elim fun t => ⟨.lam Δ _ u _ _ v a b₀ t⟩
  have tlam' : Nonempty (HasTyA E I n Δ (.lam (substA σ' A') u' (substA σ'.up b'))
      (.pi (substA σ A) u (substA σ.up B) v)) := (LRRelA_hasTyg hll).2
  have clam : Nonempty (ConvA E I n Δ (.lam (substA σ A) u (substA σ.up b))
      (.lam (substA σ' A') u' (substA σ'.up b')) (.pi (substA σ A) u (substA σ.up B) v)) :=
    cAA'.elim fun a => cb.elim fun c => tlam'.elim fun t => ⟨.lam Δ _ _ _ _ _ u u' v hu a c t⟩
  -- the right domain at ITS sort (`=ₙ` to the left's), for the right β-redex
  have tA''u : Nonempty (HasTyA E I n Δ (substA σ' A') (.sort u')) :=
    tA''.elim fun a => ⟨hasTyA_of_tyConvA a (tyConvA_sorts Δ hu)⟩
  have eA : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
      LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A)) :=
    fun ρ hρ' => LREqA_transg hEN (LREqA_of_sortRelg (fundArm_sort_wkg hE hI hEN hNC hA hkA hσ ρ hρ'))
      (LREqA_symmg hEN (LREqA_of_sortRelg (fundArm_sort_wkg hE hI hEN hNC hA hkA (ValidSubstA_refl_rightg hEN hσ) ρ hρ')))
  have eAA' : ∀ ρ : WkSpecA, WkOkA E I n ρ Δ →
      LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (wkExprA ρ (substA σ' A')) :=
    fun ρ hρ' => LREqA_of_sortRelg (fundArm_sort_wkg hE hI hEN hNC hA hkA hσ ρ hρ')
  cases hz : isZero v with
  | true =>
      have hnf : TripleLikeA E I Δ (.pi (substA σ A) u (substA σ.up B) v) :=
        tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _) ((isPropTy_pi_iff E I Δ _ u _ v).2 hz)
      have hwh : WhTyA E I n Δ (.pi (substA σ A) u (substA σ.up B) v) (.pi (substA σ A) u (substA σ.up B) v) :=
        tpi.elim fun t => whTyA_of_hasTy t
      refine ⟨_, by rw [LRTyA_eqg]; exact tyKA_of_propNFg hwh hnf.1 ((isPropTy_pi_iff E I Δ _ u _ v).2 hz), ?_⟩
      exact ⟨tlam, tlam', clam⟩
  | false =>
      have hnp : ¬ IsPropTy E I Δ (.pi (substA σ A) u (substA σ.up B) v) := fun h => by
        rw [(isPropTy_pi_iff E I Δ _ u _ v).1 h] at hz; cases hz
      rw [LRTyA_eqg] at hRpi
      obtain ⟨RD, RC, hD, hC, hCeq, e⟩ := tyKA_pi_invg hRpi hnp
      subst e
      have hRpi' : LRTyAg E I n ρ₀ k Δ (.pi (substA σ A) u (substA σ.up B) v) (fun f g =>
          (∀ ρ : WkSpecA, WkOkA E I n ρ Δ → ∀ a a' : ExprA, RD ρ a a' →
            RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
          Nonempty (HasTyA E I n Δ f (.pi (substA σ A) u (substA σ.up B) v)) ∧
          Nonempty (HasTyA E I n Δ g (.pi (substA σ A) u (substA σ.up B) v)) ∧
          Nonempty (ConvA E I n Δ f g (.pi (substA σ A) u (substA σ.up B) v))) := by
        rw [LRTyA_eqg]; exact hRpi
      refine LRRelAg.of hRpi' ⟨fun ρ hρ' x x' hx => ?_, tlam, tlam', clam⟩
      have hDx : LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) (RD ρ) := by
        rw [LRTyA_eqg]; exact hD ρ hρ'
      have hxx : LRRelAg E I n ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA σ A)) x x' := LRRelAg.of hDx hx
      have hCx : LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
          (RC ρ x) := by rw [LRTyA_eqg]; exact hC ρ hρ' x x' hx
      have hCx' : LRTyAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
          (RC ρ x') := by rw [LRTyA_eqg]; exact hC ρ hρ' x' x' (hxx.at hDx |> fun _ => (LRRelA_refl_leftg hEN (LRRelA_symmg hEN hxx)).at hDx)
      have hCeqx : LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))
          (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) := by
        rw [LREqA_eqg]; exact hCeq ρ hρ' x x' hx
      have ih := fundArm_cons_wkg hE hI hEN hNC hb hkb hσ ρ hρ' (eA ρ hρ') hxx
      obtain ⟨tx, tx'⟩ := LRRelA_hasTyg hxx
      obtain ⟨tred, tred'⟩ := LRRelA_hasTyg ih.2
      obtain ⟨w₁, tTy⟩ := LRTyA_hasTyg hCx
      obtain ⟨w₂, tTy'⟩ := LRTyA_hasTyg hCx'
      have tcC := LREqA_tyConvg hCeqx
      have tcAA' := LREqA_tyConvg (eAA' ρ hρ')
      -- left β-step
      have hsL : StepAtA E I n (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam (substA σ A) u (substA σ.up b))) x)
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up b)))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) :=
        tx.elim fun t => tred.elim fun r => tTy.elim fun ty => tA.elim fun a => tB.elim fun b₀ => tb.elim fun t₀ =>
          stepAtA_beta_wk hE hI a b₀ t₀ ρ hρ' t r ty
      -- right β-step: the redex typed through the LEFT pi, the reduct through the codomain equality
      have tB_w : Nonempty (HasTyA E I n (.assumption (wkExprA ρ (substA σ A)) :: wkCtxA ρ Δ)
          (wkExprA (WkSpecA.ub ρ) (substA σ.up B)) (.sort v)) := hasTyA_wk_ne_binder hE hI ρ hρ'.1 tB
      have tlam'_w : Nonempty (HasTyA E I n (wkCtxA ρ Δ) (wkExprA ρ (.lam (substA σ' A') u' (substA σ'.up b')))
          (.pi (wkExprA ρ (substA σ A)) u (wkExprA (WkSpecA.ub ρ) (substA σ.up B)) v)) := by
        have := hasTyA_wk_ne hE hI ρ hρ'.1 tlam'
        rw [wkExprA_pi_ub] at this
        exact this
      have tredex : Nonempty (HasTyA E I n (wkCtxA ρ Δ)
          (.app (wkExprA ρ (.lam (substA σ' A') u' (substA σ'.up b'))) x')
          (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA σ.up B)))) :=
        tB_w.elim fun hB' => tTy'.elim fun ty' => tlam'_w.elim fun hf => tx'.elim fun t' =>
          ⟨.app _ _ _ _ _ u v w₂ hB' ty' hf t'⟩
      have hsR : StepAtA E I n (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam (substA σ' A') u' (substA σ'.up b'))) x')
          (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA σ'.up b')))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA σ.up B))) :=
        tA''u.elim fun a'' => tb'.elim fun t₁ => tx'.elim fun t' => tred'.elim fun r' => tredex.elim fun tr =>
          tcC.elim fun c => tcAA'.elim fun cA =>
          stepAtA_tyConv (stepAtA_beta_wk' hE hI a'' t₁ ρ hρ' (hasTyA_of_tyConvA t' cA)
            (hasTyA_of_tyConvA r' c) tr) ⟨c.symm⟩
      exact (LRRelA_expand_leftg hE hI hsL (LRRelA_expand_rightg hE hI hsR ih.2)).at hCx

/-! ## (20) THE LETE ARM (conversion) -/

theorem convArmLetEA_holdsg (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) :
    ConvArmLetEAg E I n ρ₀ :=
  fun Γ A A' v v' b b' B u _ _ _ _ ihA ihv ihb ihrt => by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kv, hv⟩ := ihv
  obtain ⟨kb, hb⟩ := ihb
  obtain ⟨kr, hr⟩ := ihrt
  refine ⟨max (max kA kv) (max kb kr), fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkv : kv ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkb : kb ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨heT, hrr⟩ := hr k hkr Δ σ σ' hΔ hσ
  refine ⟨heT, ?_⟩
  have hAΔ : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ A) (substA σ' A') := (hA k hkA Δ σ σ' hΔ hσ).2
  have hAΔ' : LRRelAg E I n ρ₀ k Δ (.sort u) (substA σ' A) (substA σ' A') :=
    (hA k hkA Δ σ' σ' hΔ (ValidSubstA_refl_rightg hEN hσ)).2
  obtain ⟨heAA', hvA, _, tA, _, _⟩ := LRRelA_sort_elimg hAΔ
  obtain ⟨heA'A', _, _, _, _, _⟩ := LRRelA_sort_elimg hAΔ'
  have heA : LREqAg E I n ρ₀ k Δ (substA σ A) (substA σ' A) := LREqA_transg hEN heAA' (LREqA_symmg hEN heA'A')
  obtain ⟨_, hvv'⟩ := hv k hkv Δ σ σ' hΔ hσ
  obtain ⟨_, hv'v'⟩ := hv k hkv Δ σ' σ' hΔ (ValidSubstA_refl_rightg hEN hσ)
  have hvv : LRRelAg E I n ρ₀ k Δ (substA σ A) (substA σ v) (substA σ' v) :=
    LRRelA_transg hEN hvv' (LRRelA_symmg hEN (LRRelA_transport'g hEN (LREqA_symmg hEN heA) hv'v'))
  obtain ⟨tv, _⟩ := LRRelA_hasTyg hvv
  -- the body under the extended pair (value on the left, the right value on the right)
  have hcons := ValidSubstA_consLet'g hEN hσ heA hvv' hvv
  have hbc := (hb k hkb Δ _ _ hΔ hcons).2
  simp only [← instantiate0A_substA_up] at hbc
  rw [substA_instantiate0A]
  -- left ζ-step
  have hupL := ValidSubstA_upLetg hE hI hEN hNC hΔ hσ heA hvv tA
  have hΔL : Nonempty (CtxWfA E I n (.letBinding (substA σ A) (substA σ v) :: Δ)) :=
    hΔ.elim fun c => tA.elim fun t => tv.elim fun x => ⟨.letBinding c t x⟩
  have hbL := (hb k hkb _ σ.up σ'.up hΔL hupL).2
  obtain ⟨tb, _⟩ := LRRelA_hasTyg hbL
  obtain ⟨tred, tred'⟩ := LRRelA_hasTyg hbc
  obtain ⟨RT, hRT⟩ := LRRelA_validg hbc
  obtain ⟨w, tTy⟩ := LRTyA_hasTyg hRT
  have hsL : StepAtA E I n Δ (.letE (substA σ A) (substA σ v) (substA σ.up b))
      (instantiate0A (substA σ v) (substA σ.up b)) (instantiate0A (substA σ v) (substA σ.up B)) :=
    ⟨tA.elim fun a => tv.elim fun x => tTy.elim fun t => tb.elim fun b₀ => ⟨.letE Δ _ u w _ _ _ a x t b₀⟩,
     tA.elim fun a => tv.elim fun x => tb.elim fun b₀ => tred.elim fun r => ⟨.zeta Δ _ _ _ _ u a x b₀ r⟩⟩
  -- right ζ-step: generation on the right let's typing
  have tR : Nonempty (HasTyA E I n Δ (.letE (substA σ' A') (substA σ' v') (substA σ'.up b'))
      (instantiate0A (substA σ v) (substA σ.up B))) := by
    have := (LRRelA_hasTyg hrr).2
    rw [substA_instantiate0A] at this
    exact this
  have hsR : StepAtA E I n Δ (.letE (substA σ' A') (substA σ' v') (substA σ'.up b'))
      (instantiate0A (substA σ' v') (substA σ'.up b')) (instantiate0A (substA σ v) (substA σ.up B)) :=
    tR.elim fun t => tred'.elim fun r =>
      match hasTyA_letE_inv t with
      | ⟨B₀, u₀, w₀, tA₀, tv₀, _, tb₀, tc₀⟩ =>
          tA₀.elim fun a₀ => tv₀.elim fun x₀ => tb₀.elim fun b₀ => tc₀.elim fun c₀ =>
            stepAtA_tyConv ⟨⟨hasTyA_of_tyConvA t c₀.symm⟩,
              ⟨.zeta Δ _ _ _ _ u₀ a₀ x₀ b₀ (hasTyA_of_tyConvA r c₀.symm)⟩⟩ ⟨c₀⟩
  exact LRRelA_expand_leftg hE hI hsL (LRRelA_expand_rightg hE hI hsR hbc)

/-! ## (21) THE FUNDAMENTAL THEOREM, all twenty-seven arms -/

/-- the two arm bundles at a member domain `D`: every arm but `const`/`consts`
    is unconditional, those two from the semantic clauses on `D` (M2-e (4)). -/
theorem fundArmsA_atg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hK : PropKeyA E I n) {D : Nat → Prop}
    (hS : EnvSemAtg E I n ρ₀ D) :
    FundHasTyArmsAg E I n ρ₀ D ∧ FundConvArmsAg E I n ρ₀ D :=
  have hIC : IotaConstHeadA I := iotaConstHeadA_of_recHead hR
  ⟨fundHasTyArmsA_ofg hE hI hEN hS (hasTyArmPiA_holdsg hE hI hEN hNC hIC hK hρ)
    (hasTyArmLamA_holdsg hE hI hEN hNC hIC hK) (hasTyArmAppA_holdsg hE hI hEN hNC hIC hK)
    (hasTyArmLetEA_holdsg hE hI hEN hNC),
   fundConvArmsA_ofg hE hI hIS hEN hR hS (convArmBetaA_holdsg hE hI hEN hNC hIC hK)
    (convArmZetaA_holdsg hE hI hEN hNC)
    (convArmAppA_holdsg hE hI hEN hNC hIC hK) (convArmLamA_holdsg hE hI hEN hNC hIC hK)
    (convArmPiA_holdsg hE hI hEN hNC hIC hK hρ)
    (convArmLetEA_holdsg hE hI hEN hNC) (convArmEtaA_holdsg hE hI hEN hNC)⟩

theorem fundAg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I)
    (hS : EnvSemAg E I n ρ₀) (hρ : PosValA ρ₀) (hK : PropKeyA E I n) :
    FundHasTyAg E I n ρ₀ ∧ FundConvAg E I n ρ₀ :=
  fundOfArmsAg (fundArmsA_atg hE hI hIS hEN hNC hR hρ hK (envSemAt_univg hS)).1
    (fundArmsA_atg hE hI hIS hEN hNC hR hρ hK (envSemAt_univg hS)).2

end Bind

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.LRTyA_canong
#print axioms Rcic.Declarative.Ann.LRRelA_sort_elim'g
#print axioms Rcic.Declarative.Ann.ValidSubstA_consg
#print axioms Rcic.Declarative.Ann.ValidSubstA_upg
#print axioms Rcic.Declarative.Ann.ValidSubstA_upLetg
#print axioms Rcic.Declarative.Ann.LRRelA_pi_elimg
#print axioms Rcic.Declarative.Ann.piEqA_of_datag
#print axioms Rcic.Declarative.Ann.piTyA_of_datag
#print axioms Rcic.Declarative.Ann.hasTyArmPiA_holdsg
#print axioms Rcic.Declarative.Ann.hasTyArmLamA_holdsg
#print axioms Rcic.Declarative.Ann.hasTyArmAppA_holdsg
#print axioms Rcic.Declarative.Ann.hasTyArmLetEA_holdsg
#print axioms Rcic.Declarative.Ann.convArmBetaA_holdsg
#print axioms Rcic.Declarative.Ann.convArmZetaA_holdsg
#print axioms Rcic.Declarative.Ann.convArmAppA_holdsg
#print axioms Rcic.Declarative.Ann.convArmEtaA_holdsg
#print axioms Rcic.Declarative.Ann.convArmPiA_holdsg
#print axioms Rcic.Declarative.Ann.convArmLamA_holdsg
#print axioms Rcic.Declarative.Ann.convArmLetEA_holdsg
#print axioms Rcic.Declarative.Ann.fundAg
