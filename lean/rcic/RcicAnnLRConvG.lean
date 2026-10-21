import rcic.RcicAnnLRConv
import rcic.RcicAnnLRWkG
/-!
# M2-b (ii) — type equality transports the term relation

`eqKA_transportg : EqKAg Γ A B → TyKAg Γ A R → TyKAg Γ B R' → R = R'`: the term
relation is a function of the type UP TO `EqKAg` (the kill criterion
`TyKA_uniqueg` is the diagonal). Abel–Öhman–Vezzosi's conversion lemmas
(`convTerm₁/₂`, `convEqTerm₁/₂`) in one statement. This module holds the
transport MINORS; since M2-f (3b) the induction is JOINT with PER
(`eqKA_transport_perg`, `RcicAnnLRPer`): at the `fam` clause the carrier moves
along related indices, which flips and composes the index walks by the index
relations' PER (`transMinor_famg`, with `idxPerA_ofg` / `ctorPerA_ofg` building
the walk calculus's hypotheses from the clause data and the induction
hypotheses). The pi case still uses no PER property — what the one-sided
codomain datum of `EqKAg.pi` buys (`RcicAnnLR`, header note 8).

Cases. `sort`: `=ₙ` levels have the same `ht` (`ht_of_eqN`), and the
typings and conversions at `sort l` re-sort to `sort l'` (`tyConvA_sorts`).
`pi`: the two induction hypotheses — `hDeq` for the domains, `hC` for the
codomains at ONE argument — and `TyKA_uniqueg` to identify the clause's own
domain relation with the two it meets; a prop pi meets a prop pi because
`IsPropTy` of a pi is `isZero` of its annotation (`isPropTy_pi_iff`) and
`isZero` is `=ₙ 0` (`isZero_iff_eqN_zero`), so it respects `=ₙ`. `stuck`, and
the prop clause at a neutral: the type conversion between the two normal
forms alone (`tripleA_eq_of_tyConv`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) `isZero` is `=ₙ 0`: moved to `RcicAnnFamPer` (M2-f (3b)) -/

/-! ## (2) casts between equal heights; the triple at convertible normal forms -/

section Casts
variable {k : Nat}

end Casts

section Triple
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end Triple

/-! ## (2b) the inner telescope of a function-recursive field is rigid (R-NoFunRec-1 step 1 (1b))

A field of shape `recursive (j + 1)` is, through erasure, a Π-telescope of `j + 1` domains ending in a
family application (`fieldShapeE`). Instantiating the levels, the parameters and the earlier fields, and
weakening, keep that: the domain a constructor telescope reaches at the field is a rigid telescope of
`j + 1` binders (`rigTel_of_shape`, `rigid_wkExprA`). An inner walk's Π on either side comes from here. -/

/-! ## (3) the transport, one height -/

section Transport
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

/-- the motive: whatever relations the two types get, they agree. -/
abbrev TransMotAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) (Γ : LCtxA) (A B : ExprA) : Prop :=
  ∀ R R' : ExprA → ExprA → Prop,
    TyKAg E I n ρ₀ k LE LT Γ A R → TyKAg E I n ρ₀ k LE LT Γ B R' → R = R'

theorem transMinor_sortg {Γ : LCtxA} {A B : ExprA} {l l' : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (hB : WhTyA E I n Γ B (.sort l')) (_hk : ht ρ₀ l < k)
    (hl : eqN l l') (_hc : Nonempty (TyConvA E I n Γ A B)) :
    TransMotAg E I n ρ₀ k LE LT Γ A B := by
  intro R R' tA tB
  have hz : isZero l = isZero l' := isZero_eqN hl
  cases tA with
  | prop hA₁ hn₁ hP₁ =>
      have e := whTyA_det hA hA₁ (hStepFnA_sort _ _ _ _) hn₁
      subst e
      exact absurd hP₁ (not_isPropTy_sort _ _ _ _)
  | pi hA₁ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA₁ (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
  | fam hA₁ hn₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA₁ (hStepFnA_sort _ _ _ _) hn₁
      exact absurd e.symm (foldAppsA_const_ne_sort _ _ _ _)
  | stuck hA₁ hN₁ =>
      have e := whTyA_det hA hA₁ (hStepFnA_sort _ _ _ _) hN₁.1
      subst e
      exact (stuckA_not_sort hN₁).elim
  | sortT hA₁ hz₁ hk₁ =>
      have e := whTyA_det hA hA₁ (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
      cases tB with
      | prop hB₁ hn₂ hP₂ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) hn₂
          subst e
          exact absurd hP₂ (not_isPropTy_sort _ _ _ _)
      | pi hB₁ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
      | fam hB₁ hn₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) hn₂
          exact absurd e.symm (foldAppsA_const_ne_sort _ _ _ _)
      | stuck hB₁ hN₂ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) hN₂.1
          subst e
          exact (stuckA_not_sort hN₂).elim
      | sortP hB₁ hz₂ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          rw [hz₁, hz₂] at hz
          cases hz
      | sortT hB₁ _ hk₂ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          have hidx : ht ρ₀ l = ht ρ₀ l' := ht_of_eqN hl
          funext a b
          apply propext
          constructor
          · rintro ⟨h1, h2, h3, h4, h5, h6⟩
            exact ⟨(lowEq_cast LE _ _ hidx Γ a b).1 h1, (lowTy_cast LT _ _ hidx Γ a).1 h2,
              (lowTy_cast LT _ _ hidx Γ b).1 h3, h4.elim fun t => ⟨hasTyA_retype_sort t hl⟩,
              h5.elim fun t => ⟨hasTyA_retype_sort t hl⟩,
              h6.elim fun c => ⟨convA_of_tyConvA c (tyConvA_sorts Γ hl)⟩⟩
          · rintro ⟨h1, h2, h3, h4, h5, h6⟩
            exact ⟨(lowEq_cast LE _ _ hidx Γ a b).2 h1, (lowTy_cast LT _ _ hidx Γ a).2 h2,
              (lowTy_cast LT _ _ hidx Γ b).2 h3,
              h4.elim fun t => ⟨hasTyA_retype_sort t (eqNA_symm hl)⟩,
              h5.elim fun t => ⟨hasTyA_retype_sort t (eqNA_symm hl)⟩,
              h6.elim fun c => ⟨convA_of_tyConvA c (tyConvA_sorts Γ (eqNA_symm hl))⟩⟩
  | sortP hA₁ hz₁ =>
      have e := whTyA_det hA hA₁ (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
      cases tB with
      | prop hB₁ hn₂ hP₂ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) hn₂
          subst e
          exact absurd hP₂ (not_isPropTy_sort _ _ _ _)
      | pi hB₁ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
      | fam hB₁ hn₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) hn₂
          exact absurd e.symm (foldAppsA_const_ne_sort _ _ _ _)
      | stuck hB₁ hN₂ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) hN₂.1
          subst e
          exact (stuckA_not_sort hN₂).elim
      | sortT hB₁ hz₂ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          rw [hz₁, hz₂] at hz
          cases hz
      | sortP hB₁ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          funext a b
          apply propext
          constructor
          · rintro ⟨h1, h2, h4, h5, h6, h7⟩
            exact ⟨h1, h2, h4.elim fun t => ⟨hasTyA_retype_sort t hl⟩,
              h5.elim fun t => ⟨hasTyA_retype_sort t hl⟩,
              h6.elim fun c => ⟨convA_of_tyConvA c (tyConvA_sorts Γ hl)⟩, h7⟩
          · rintro ⟨h1, h2, h4, h5, h6, h7⟩
            exact ⟨h1, h2, h4.elim fun t => ⟨hasTyA_retype_sort t (eqNA_symm hl)⟩,
              h5.elim fun t => ⟨hasTyA_retype_sort t (eqNA_symm hl)⟩,
              h6.elim fun c => ⟨convA_of_tyConvA c (tyConvA_sorts Γ (eqNA_symm hl))⟩, h7⟩

/-- DT-025/A-6 S1-g.2: the guarded stuck clause's chained quadruple is one relation at two
    convertible normal forms — the chains retype by `tyHRedStarA_retype`. -/
theorem quadA_eq_of_tyConvg {Γ : LCtxA} {N N' : ExprA} (hc : Nonempty (TyConvA E I n Γ N N')) :
    (fun a b : ExprA => Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
        Nonempty (ConvA E I n Γ a b N) ∧
        ∃ Na, TyHRedStarA E I n Γ a Na N ∧ hStepFnA E I.fn Γ Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ b Nb N ∧ hStepFnA E I.fn Γ Nb = none) =
    (fun a b : ExprA => Nonempty (HasTyA E I n Γ a N') ∧ Nonempty (HasTyA E I n Γ b N') ∧
        Nonempty (ConvA E I n Γ a b N') ∧
        ∃ Na, TyHRedStarA E I n Γ a Na N' ∧ hStepFnA E I.fn Γ Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ b Nb N' ∧ hStepFnA E I.fn Γ Nb = none) := by
  funext a b
  apply propext
  exact hc.elim fun c =>
    ⟨fun ⟨h1, h2, h3, Na, cha, hna, Nb, chb, hnb⟩ =>
      ⟨h1.elim fun t => ⟨hasTyA_of_tyConvA t c⟩, h2.elim fun t => ⟨hasTyA_of_tyConvA t c⟩,
        h3.elim fun t => ⟨convA_of_tyConvA t c⟩,
        Na, tyHRedStarA_retype ⟨c⟩ cha, hna, Nb, tyHRedStarA_retype ⟨c⟩ chb, hnb⟩,
     fun ⟨h1, h2, h3, Na, cha, hna, Nb, chb, hnb⟩ =>
      ⟨h1.elim fun t => ⟨hasTyA_of_tyConvA t c.symm⟩, h2.elim fun t => ⟨hasTyA_of_tyConvA t c.symm⟩,
        h3.elim fun t => ⟨convA_of_tyConvA t c.symm⟩,
        Na, tyHRedStarA_retype ⟨c.symm⟩ cha, hna, Nb, tyHRedStarA_retype ⟨c.symm⟩ chb, hnb⟩⟩

/-- DT-025/A-6 S1-g.2: at a triple-like normal form the guarded relation is the prop clause's
    triple (at a proposition) or the guarded stuck clause's chained quadruple (at a stuck
    non-proposition) — no other clause reaches it, and no `IsPropTy` decision is made. -/
theorem tyKA_tripleLike_casesg {Γ : LCtxA} {A N : ExprA} {R : ExprA → ExprA → Prop}
    (hA : WhTyA E I n Γ A N) (hN : TripleLikeA E I Γ N) (t : TyKAg E I n ρ₀ k LE LT Γ A R) :
    (IsPropTy E I Γ N ∧ R = fun a b => Nonempty (HasTyA E I n Γ a N) ∧
        Nonempty (HasTyA E I n Γ b N) ∧ Nonempty (ConvA E I n Γ a b N)) ∨
    (StuckA E I Γ N ∧ ¬ IsPropTy E I Γ N ∧ R = fun a b => Nonempty (HasTyA E I n Γ a N) ∧
        Nonempty (HasTyA E I n Γ b N) ∧ Nonempty (ConvA E I n Γ a b N) ∧
        ∃ Na, TyHRedStarA E I n Γ a Na N ∧ hStepFnA E I.fn Γ Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ b Nb N ∧ hStepFnA E I.fn Γ Nb = none) := by
  cases t with
  | prop hA₁ hn₁ hP₁ =>
      have e := whTyA_det hA hA₁ hN.1 hn₁
      subst e; exact .inl ⟨hP₁, rfl⟩
  | stuck hA₁ hN₁ hnp₁ =>
      have e := whTyA_det hA hA₁ hN.1 hN₁.1
      subst e; exact .inr ⟨hN₁, hnp₁, rfl⟩
  | sortT hA₁ _ _ =>
      have e := whTyA_det hA hA₁ hN.1 (hStepFnA_sort _ _ _ _)
      subst e
      exact (tripleLikeA_not_sort hN).elim
  | sortP hA₁ _ =>
      have e := whTyA_det hA hA₁ hN.1 (hStepFnA_sort _ _ _ _)
      subst e
      exact (tripleLikeA_not_sort hN).elim
  | pi hA₁ hnp₁ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA₁ hN.1 (hStepFnA_pi _ _ _ _ _ _ _)
      subst e
      exact (hnp₁ (tripleLikeA_pi_isProp hN)).elim
  | fam hA₁ hn₁ hnp₁ hm₁ hind₁ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA₁ hN.1 hn₁
      subst e
      exact (hnp₁ (tripleLikeA_famApp_isProp hm₁ hind₁ hN)).elim

/-- transport along the guarded `EqKAg.stuck`: the two normal forms are on the same side of the
    `IsPropTy` boundary (`hPP`, the clause's own datum), so the relations are both triples or
    both chained quadruples — the mixed cases contradict `hPP`. -/
theorem transMinor_stuckg {Γ : LCtxA} {A B N N' : ExprA}
    (hA : WhTyA E I n Γ A N) (hB : WhTyA E I n Γ B N')
    (hN : TripleLikeA E I Γ N) (hN' : TripleLikeA E I Γ N')
    (hc : Nonempty (TyConvA E I n Γ A B)) (hPP : IsPropTy E I Γ N ↔ IsPropTy E I Γ N') :
    TransMotAg E I n ρ₀ k LE LT Γ A B := by
  intro R R' tA tB
  have tc := tyConvA_nf hA hB hc
  rcases tyKA_tripleLike_casesg hA hN tA with ⟨hP, eA⟩ | ⟨_, hnp, eA⟩ <;>
    rcases tyKA_tripleLike_casesg hB hN' tB with ⟨hP', eB⟩ | ⟨_, hnp', eB⟩ <;>
    rw [eA, eB]
  · exact tripleA_eq_of_tyConv tc
  · exact absurd (hPP.1 hP) hnp'
  · exact absurd (hPP.2 hP') hnp
  · exact quadA_eq_of_tyConvg tc

theorem transMinor_pig {Γ : LCtxA} {A B D C D' C' : ExprA} {u v u' v' : Level}
    (hA : WhTyA E I n Γ A (.pi D u C v)) (hB : WhTyA E I n Γ B (.pi D' u' C' v'))
    (_hu : eqN u u') (hv : eqN v v')
    (_hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (_hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (_hD'ty : Nonempty (HasTyA E I n Γ D' (.sort u')))
    (_hC'ty : Nonempty (HasTyA E I n (.assumption D' :: Γ) C' (.sort v')))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (_hDeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (_hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
    (hc : Nonempty (TyConvA E I n Γ A B))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ), PerMotA (RD ρ))
    (ihDeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ),
      TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C'))) :
    TransMotAg E I n ρ₀ k LE LT Γ A B := by
  intro R R' tA tB
  have tc : Nonempty (TyConvA E I n Γ (.pi D u C v) (.pi D' u' C' v')) := tyConvA_nf hA hB hc
  cases tA with
  | sortT hA₁ _ _ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | sortP hA₁ _ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | stuck hA₁ hN₁ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) hN₁.1
      subst e
      exact (stuckA_not_pi hN₁).elim
  | fam hA₁ hn₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) hn₁
      exact absurd e.symm (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | prop hA₁ hn₁ hP₁ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) hn₁
      subst e
      cases tB with
      | sortT hB₁ _ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | sortP hB₁ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | stuck hB₁ hN₂ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) hN₂.1
          subst e
          exact (stuckA_not_pi hN₂).elim
      | fam hB₁ hn₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) hn₂
          exact absurd e.symm (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | prop hB₁ hn₂ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) hn₂
          subst e
          exact tripleA_eq_of_tyConv tc
      | pi hB₁ hnp₂ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
          exact (hnp₂ ((isPropTy_pi_eqN hv).1 hP₁)).elim
  | pi hA₁ hnp₁ _ _ RD₁ hD₁ RC₁ hC₁ _ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
      cases tB with
      | sortT hB₁ _ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | sortP hB₁ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | stuck hB₁ hN₂ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) hN₂.1
          subst e
          exact (stuckA_not_pi hN₂).elim
      | fam hB₁ hn₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) hn₂
          exact absurd e.symm (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | prop hB₁ hn₂ hP₂ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) hn₂
          subst e
          exact (hnp₁ ((isPropTy_pi_eqN hv).2 hP₂)).elim
      | pi hB₁ _ _ _ RD₂ hD₂ RC₂ hC₂ _ =>
          have e := whTyA_det hB hB₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
          -- the clause's own domain relation is the one both sides meet
          have hRD₁ : ∀ ρ (hρ : WkOkA E I n ρ Γ), RD ρ = RD₁ ρ :=
            fun ρ hρ => TyKA_uniqueg (hD ρ hρ) (hD₁ ρ hρ)
          have hRD : ∀ ρ (hρ : WkOkA E I n ρ Γ), RD₁ ρ = RD₂ ρ :=
            fun ρ hρ => ihDeq ρ hρ _ _ (hD₁ ρ hρ) (hD₂ ρ hρ)
          have hRC : ∀ ρ (hρ : WkOkA E I n ρ Γ) a a', RD₁ ρ a a' → RC₁ ρ a = RC₂ ρ a :=
            fun ρ hρ a a' hr =>
              ihC ρ hρ a a' (by rw [hRD₁ ρ hρ]; exact hr) _ _ (hC₁ ρ hρ a a' hr)
                (hC₂ ρ hρ a a' (by rw [← hRD ρ hρ]; exact hr))
          funext f g
          apply propext
          constructor
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨fun ρ hρ a a' hr => ?_,
              tc.elim fun c => h2.elim fun t => ⟨hasTyA_of_tyConvA t c⟩,
              tc.elim fun c => h3.elim fun t => ⟨hasTyA_of_tyConvA t c⟩,
              tc.elim fun c => h4.elim fun t => ⟨convA_of_tyConvA t c⟩⟩
            have hr₁ : RD₁ ρ a a' := by rw [hRD ρ hρ]; exact hr
            have h := h1 ρ hρ a a' hr₁
            rw [hRC ρ hρ a a' hr₁] at h
            exact h
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨fun ρ hρ a a' hr => ?_,
              tc.elim fun c => h2.elim fun t => ⟨hasTyA_of_tyConvA t c.symm⟩,
              tc.elim fun c => h3.elim fun t => ⟨hasTyA_of_tyConvA t c.symm⟩,
              tc.elim fun c => h4.elim fun t => ⟨convA_of_tyConvA t c.symm⟩⟩
            have h := h1 ρ hρ a a' (by rw [← hRD ρ hρ]; exact hr)
            rw [← hRC ρ hρ a a' hr] at h
            exact h

/-- the index walks of a family clause flip and compose on a fiber (`IdxPerA`), from the
    clause's data there: validity of the index domains, their PER, and transport along the
    domain equalities at `=ₙ` level lists and related prefixes (walks from the carrier's
    parameters, M2-f (3c)). -/
theorem idxPerA_ofg {Γ : LCtxA} {m : CheckedMemberA} {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    {RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop} {ps : List ExprA} {ls₀ : List Level}
    (hFldF : ∀ (lsF : List Level) (TF : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
        (C : ExprA) (vC : Level), eqNListB n ls₀ lsF →
        applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
        ArgsRelPA (RsF lsF) m.nparamsA ps TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        TyKAg E I n ρ₀ k LE LT Γ D (RsF lsF (m.nparamsA + pre.length) (ps ++ pre)))
    (ihFldF : ∀ (lsF : List Level) (TF : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
        (C : ExprA) (vC : Level), eqNListB n ls₀ lsF →
        applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
        ArgsRelPA (RsF lsF) m.nparamsA ps TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        PerMotA (RsF lsF (m.nparamsA + pre.length) (ps ++ pre)))
    (ihFldFeq : ∀ (lsF lsF' : List Level) (TF TF' : ExprA) (pre pre' : List ExprA) (D : ExprA)
        (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        eqNListB n ls₀ lsF → eqNListB n lsF lsF' →
        applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
        applyTelA ps (instantiateLevelsA lsF' m.mtypeA) = some TF' →
        ArgsRelPA (RsF lsF) m.nparamsA ps TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → TransMotAg E I n ρ₀ k LE LT Γ D D') :
    IdxPerA n RsF m ps ls₀ := by
  intro lsF lsF' TF TF' hl₀ hls hTF hTF'
  refine ⟨fun pre pre' A u B v hp hp' hT => ?_, fun p₁ p₂ p₃ A u B v h₁₂ h₂₃ _ hT => ?_⟩
  · have hlen := argsRelPA_length hp
    obtain ⟨A', u', B', v', hT'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) rfl hTF hTF' hlen hT
    refine ⟨A', u', B', v', hT', fun f f' hff => ?_⟩
    have heq : RsF lsF (m.nparamsA + pre.length) (ps ++ pre) =
        RsF lsF' (m.nparamsA + pre'.length) (ps ++ pre') :=
      ihFldFeq lsF lsF' TF TF' pre pre' A u B v A' u' B' v' hl₀ hls hTF hTF' hp hT hT' _ _
        (hFldF lsF TF pre pre' A u B v hl₀ hTF hp hT)
        (hFldF lsF' TF' pre' pre A' u' B' v' (eqNListB_trans hl₀ hls) hTF' hp' hT')
    have h := (ihFldF lsF TF pre pre' A u B v hl₀ hTF hp hT).1 f f' hff
    rw [heq, ← hlen] at h
    exact h
  · have hlen := argsRelPA_length h₁₂
    obtain ⟨A', u', B', v', hT'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) rfl hTF hTF' hlen hT
    refine ⟨A', u', B', v', hT', fun f₁ f₂ f₃ ha hb => ?_⟩
    have heq : RsF lsF (m.nparamsA + p₁.length) (ps ++ p₁) =
        RsF lsF' (m.nparamsA + p₂.length) (ps ++ p₂) :=
      ihFldFeq lsF lsF' TF TF' p₁ p₂ A u B v A' u' B' v' hl₀ hls hTF hTF' h₁₂ hT hT' _ _
        (hFldF lsF TF p₁ p₂ A u B v hl₀ hTF h₁₂ hT)
        (hFldF lsF' TF' p₂ p₃ A' u' B' v' (eqNListB_trans hl₀ hls) hTF' h₂₃ hT')
    rw [hlen, ← heq] at hb
    exact (ihFldF lsF TF p₁ p₂ A u B v hl₀ hTF h₁₂ hT).2 f₁ f₂ f₃ ha hb

/-- the constructor walks of a family clause flip and compose on a fiber (`CtorPerA`),
    from the clause's data there: validity and PER of the plain field domains, transport
    along their equalities across `=ₙ` level lists and related prefixes, and the directly
    recursive positions' related domains. At a function-recursive position (R-NoFunRec-1 step 1
    (1b)), at every extension of the world, the same one level down: the inner domains valid with
    their relations a PER, transport along their equalities, the codomains related; the inner
    telescopes are rigid (`rigTel_of_shape`), so a Π on one side is one on the other. -/
theorem ctorPerA_ofg {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    (hEN : EnvNormCtorTypeA E)
    {Rs : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RI : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {X : CRelA} {XF : WkSpecA → CRelA}
    {RsFX : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {ps : List ExprA}
    {ls₀ : List Level} (hps : ps.length = m.nparamsA)
    (hFld : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC : List Level) (kinds ksPre ks : List FieldShape)
        (T : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        TyKAg E I n ρ₀ k LE LT Γ D (Rs c lsC (m.nparamsA + ksPre.length) (ps ++ pre)))
    (ihFld : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC : List Level) (kinds ksPre ks : List FieldShape)
        (T : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        PerMotA (Rs c lsC (m.nparamsA + ksPre.length) (ps ++ pre)))
    (ihFldeq : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
        (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        TransMotAg E I n ρ₀ k LE LT Γ D D')
    (hFldRec : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
        (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        RecDomRelA E I n Γ r m RsF ls₀ ps D D')
    (hFldI : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC : List Level) (kinds ksPre ks : List FieldShape)
        (j : Nat) (T : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' Γ → ∀ (zs zs' : List ExprA) (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA)
          (v₁ : Level),
        ArgsRelPA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        TyKAg E I n ρ₀ k LE LT (wkCtxA ρ' Γ) D₁ (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ' zs.length zs))
    (ihFldI : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC : List Level) (kinds ksPre ks : List FieldShape)
        (j : Nat) (T : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' Γ → ∀ (zs zs' : List ExprA) (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA)
          (v₁ : Level),
        ArgsRelPA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        PerMotA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ' zs.length zs))
    (ihFldIeq : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA)
        (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' Γ → ∀ (zs zs' : List ExprA) (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA)
          (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ' Γ) D₁ D₁')
    (hFldIRec : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA)
        (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' Γ → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
        ArgsRelPA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
        zs.length = j + 1 → applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
        RecDomRelA E I n (wkCtxA ρ' Γ) r m (RsFX ρ') ls₀ (ps.map (wkExprA ρ')) C₁ C₁')
    (hFldIdom : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA)
        (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        Nonempty (TyConvA E I n Γ D D')) :
    CtorPerA E I n Γ r m Rs RsF RI X XF RsFX ps ls₀ := by
  intro c cm kinds lsA lsC lsC' T T' hcm hk hfam hkinds hl₀A hlAC hlsC hT hT' kd ksPre ks pre pre' q A u B v
    hsp hp hq hTA
  have hlen : pre.length = pre'.length := by
    rw [(argsRelA_length hp).1, (argsRelA_length hp).2]
  obtain ⟨A', u', B', v', hTA'⟩ := applyTelA_pi_cross (rigid_of_memberFamRefA_getD hEN hcm hk hfam) rfl hT hT' hlen hTA
  refine ⟨A', u', B', v', hTA', fun hkd => ?_, fun hkd => ?_, fun j hkd ρ' hρ' => ?_,
    fun j hkd => ?_⟩
  · subst hkd
    have heq : Rs c lsC (m.nparamsA + ksPre.length) (ps ++ pre) =
        Rs c lsC' (m.nparamsA + ksPre.length) (ps ++ pre') :=
      ihFldeq c cm lsA lsC lsC' kinds ksPre ks T T' pre pre' A u B v A' u' B' v' hcm hk hfam hkinds hsp
        hl₀A hlAC hlsC hT hT' hp hTA hTA' _ _
        (hFld c cm lsA lsC kinds ksPre ks T pre pre' A u B v hcm hk hfam hkinds hsp hl₀A hlAC hT hp hTA)
        (hFld c cm lsA lsC' kinds ksPre ks T' pre' q A' u' B' v' hcm hk hfam hkinds hsp hl₀A
          (eqNListB_trans hlAC hlsC) hT' hq hTA')
    have hper := ihFld c cm lsA lsC kinds ksPre ks T pre pre' A u B v hcm hk hfam hkinds hsp hl₀A hlAC
      hT hp hTA
    refine ⟨fun f f' h => ?_, fun f₁ f₂ f₃ h₁ h₂ => ?_⟩
    · have h' := hper.1 f f' h
      rw [heq] at h'
      exact h'
    · rw [← heq] at h₂
      exact hper.2 f₁ f₂ f₃ h₁ h₂
  · subst hkd
    exact hFldRec c cm lsA lsC lsC' kinds ksPre ks T T' pre pre' A u B v A' u' B' v' hcm hk hfam hkinds
      hsp hl₀A hlAC hlsC hT hT' hp hTA hTA'
  · subst hkd
    -- the two inner telescopes, weakened to the extension: rigid, of one Π-count
    have hrA := rigTel_of_shape hEN hcm hk hfam hkinds hsp hps (argsRelA_length hp).1 hT hTA
    have hrA' := rigTel_of_shape hEN hcm hk hfam hkinds hsp hps ((argsRelA_length hp).2) hT' hTA'
    have hwA := rigid_wkExprA ρ' A hrA.1
    have hwA' := rigid_wkExprA ρ' A' hrA'.1
    have hcnt : (piDomsA (wkExprA ρ' A)).length = (piDomsA (wkExprA ρ' A')).length := by
      rw [hwA.2, hwA'.2, hrA.2, hrA'.2]
    -- along a left inner walk and a right one from its right end, the two inner domains reached are
    -- equal types: the two relations are one (transport); and the left one is a PER
    have hone : ∀ (a b b₂ : List ExprA) (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₂ : ExprA)
        (u₂ : Level) (C₂ : ExprA) (v₂ : Level),
        ArgsRelPA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') 0 [] (wkExprA ρ' A) a b →
        ArgsRelPA (RI c lsC' (m.nparamsA + ksPre.length) (ps ++ pre') ρ') 0 [] (wkExprA ρ' A') b b₂ →
        applyTelA a (wkExprA ρ' A) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA b (wkExprA ρ' A') = some (.pi D₂ u₂ C₂ v₂) →
        RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ' a.length a =
          RI c lsC' (m.nparamsA + ksPre.length) (ps ++ pre') ρ' b.length b :=
      fun a b b₂ D₁ u₁ C₁ v₁ D₂ u₂ C₂ v₂ w1 w2 h1 h2 =>
        ihFldIeq c cm lsA lsC lsC' kinds ksPre ks j T T' pre pre' A u B v A' u' B' v' hcm hk hfam hkinds hsp
          hl₀A hlAC hlsC hT hT' hp hTA hTA' ρ' hρ' a b D₁ u₁ C₁ v₁ D₂ u₂ C₂ v₂ w1 h1 h2 _ _
          (hFldI c cm lsA lsC kinds ksPre ks j T pre pre' A u B v hcm hk hfam hkinds hsp hl₀A hlAC hT hp hTA
            ρ' hρ' a b D₁ u₁ C₁ v₁ w1 h1)
          (hFldI c cm lsA lsC' kinds ksPre ks j T' pre' q A' u' B' v' hcm hk hfam hkinds hsp hl₀A
            (eqNListB_trans hlAC hlsC) hT' hq hTA' ρ' hρ' b b₂ D₂ u₂ C₂ v₂ w2 h2)
    have hper : ∀ (a b : List ExprA) (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
        ArgsRelPA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') 0 [] (wkExprA ρ' A) a b →
        applyTelA a (wkExprA ρ' A) = some (.pi D₁ u₁ C₁ v₁) →
        PerMotA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ' a.length a) :=
      fun a b D₁ u₁ C₁ v₁ w1 h1 =>
        ihFldI c cm lsA lsC kinds ksPre ks j T pre pre' A u B v hcm hk hfam hkinds hsp hl₀A hlAC hT hp hTA
          ρ' hρ' a b D₁ u₁ C₁ v₁ w1 h1
    refine ⟨fun zs zs' hzs => ?_, fun zs zs' hzs => ?_, fun zs zs' C₁ C₁' hzs hl hC hC' =>
      hFldIRec c cm lsA lsC lsC' kinds ksPre ks j T T' pre pre' A u B v A' u' B' v' hcm hk hfam hkinds hsp
        hl₀A hlAC hlsC hT hT' hp hTA hTA' ρ' hρ' zs zs' C₁ C₁' hzs hl hC hC'⟩
    · -- a right inner walk flips to a left one
      have h := argsRelPA_flip (R := RI c lsC' (m.nparamsA + ksPre.length) (ps ++ pre') ρ')
        (R' := RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') (i₀ := 0) (prev₀ := []) (prev₀' := [])
        (T₀ := wkExprA ρ' A') (T₀' := wkExprA ρ' A)
        (fun p p' D₂ u₂ C₂ v₂ w2 w1 h2 => by
          have hl : p.length = p'.length := argsRelPA_length w2
          obtain ⟨D₁, u₁, C₁, v₁, h1⟩ := applyTelA_pi_transfer hwA'.1 hwA.1 hcnt.symm hl h2
          refine ⟨D₁, u₁, C₁, v₁, h1, fun f f' hff => ?_⟩
          simp only [Nat.zero_add, List.nil_append] at hff ⊢
          rw [← hone p' p p' D₁ u₁ C₁ v₁ D₂ u₂ C₂ v₂ w1 w2 h1 h2] at hff
          rw [hl]
          exact (hper p' p D₁ u₁ C₁ v₁ w1 h1).1 f f' hff)
        hzs [] [] (wkExprA ρ' A) (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
      simpa using h
    · -- a left inner walk relates its right arguments to themselves on the right
      have h := argsRelPA_rrefl (R := RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ')
        (R' := RI c lsC' (m.nparamsA + ksPre.length) (ps ++ pre') ρ') (i₀ := 0) (prev₀ := []) (prev₀' := [])
        (T₀ := wkExprA ρ' A) (T₀' := wkExprA ρ' A')
        (fun p p' D₁ u₁ C₁ v₁ w1 w2 h1 => by
          have hl : p.length = p'.length := argsRelPA_length w1
          obtain ⟨D₂, u₂, C₂, v₂, h2⟩ := applyTelA_pi_transfer hwA.1 hwA'.1 hcnt hl h1
          refine ⟨D₂, u₂, C₂, v₂, h2, fun f f' hff => ?_⟩
          simp only [Nat.zero_add, List.nil_append] at hff ⊢
          rw [hl, ← hone p p' p' D₁ u₁ C₁ v₁ D₂ u₂ C₂ v₂ w1 w2 h1 h2]
          have hP := hper p p' D₁ u₁ C₁ v₁ w1 h1
          exact hP.2 f' f f' (hP.1 f f' hff) hff)
        hzs [] [] (wkExprA ρ' A') (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
      simpa using h
  · subst hkd
    exact hFldIdom c cm lsA lsC lsC' kinds ksPre ks j T T' pre pre' A u B v A' u' B' v' hcm hk hfam hkinds
      hsp hl₀A hlAC hlsC hT hT' hp hTA hTA'

/-- **transport at the fam clause** (M2-f (3c)): the two family clauses' fixed points are
    one relation. The left type's own fixed point is identified with the type equality's
    on the left fiber (`lfpWA_le_of`, through `TyKA_uniqueg`); the carrier crosses to the
    right fiber and back along the type equality's cross-related carriers
    (`lfpWA_cross_fwd` / `lfpWA_cross_bwd`), the relation equalities supplied by the
    transport induction hypotheses on the cross data against the right type's own data;
    and a proposition on one side is one on the other (`isPropTy_famApp_congr`). -/
theorem transMinor_famg {Γ : LCtxA} {A B : ExprA} {r : Nat} {ls ls' : List Level} {ps ps' is is' :
    List ExprA} {m : CheckedMemberA} {u₀ : Level}
    (hEN : EnvNormCtorTypeA E)
    (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
    (hB : WhTyA E I n Γ B (foldAppsA (.const r ls') (ps' ++ is')))
    (hnA : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
    (hnB : hStepFnA E I.fn Γ (foldAppsA (.const r ls') (ps' ++ is')) = none)
    (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM)
    (hsh : piBodyA m.mtypeA = .sort u₀)
    (hls : eqNList ls ls')
    (hps : ps.length = m.nparamsA)
    (hps' : ps'.length = m.nparamsA)
    (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop) (RsI : InnerRelsA)
    (hFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
        (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), E.members c = some cm → cm.mclass =
        .constructorM → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        D (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
    (hFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → ArgsRelPA
        (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some
        (.pi D uD C vC) → TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
        (RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)))
    (_hFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some
        (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_hFldRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ (FieldShape.recursive 0) :: ks → eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some
        (.pi D' uD' C' vC') → RecDomRelA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) D
        D')
    (_hFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_hXFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some
        (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (hXRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ (FieldShape.recursive 0) :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some
        (.pi D' uD' C' vC') → RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ))
        (ps'.map (wkExprA ρ)) D D')
    (hXRes : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds : List FieldShape) (T T' : ExprA) (pre pre' : List ExprA)
        (R R' : ExprA), E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some
        r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        kinds pre pre' → applyTelA pre T = some R → applyTelA pre T' = some R' → RecDomRelXA E I n
        (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) R R')
    (hXResR : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds : List FieldShape) (T T' T'' : ExprA)
        (pre pre' : List ExprA) (R' R'' : ExprA), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → eqNList ls
        lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T'' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        kinds pre pre' → applyTelA pre' T' = some R' → applyTelA pre' T'' = some R'' → RecDomRelXA E
        I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) R' R'')
    (_hXFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF) m.nparamsA
        (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre
        TF' = some (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (hxs : ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF → ArgsRelPA
        (RsF [] ls) m.nparamsA ps TF is is')
    (hc : Nonempty (TyConvA E I n Γ A B))
    (hpar : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ lsX : List Level, eqNListB n ls lsX →
        ParConvA E I n (wkCtxA ρ Γ) (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA)
          (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)))
    (hFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        TyKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
          (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs))
    (_hFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        EqKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
    (_hFldIRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
        applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
        RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RsF (WkSpecA.comp ρ ρ')) ls
          ((ps.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁')
    (_hXFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        EqKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
    (hXRecI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
        applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs (wkExprA ρ' D') = some C₁' →
        RecDomRelXA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RsF (WkSpecA.comp ρ ρ')) ls
          ((ps.map (wkExprA ρ)).map (wkExprA ρ')) ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁')
    (_hFldIdom : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
    (hXFldIdom : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
        Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
    (_ihFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
        (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), E.members c = some cm → cm.mclass =
        .constructorM → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → PerMotA
        (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
    (ihFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → ArgsRelPA
        (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some
        (.pi D uD C vC) → PerMotA (RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)))
    (_ihFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some
        (.pi D' uD' C' vC') → TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (ihFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
        D')
    (ihXFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some
        (.pi D' uD' C' vC') → TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (ihXFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF) m.nparamsA
        (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre
        TF' = some (.pi D' uD' C' vC') → TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_ihFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        PerMotA
          (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs))
    (_ihFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
    (ihXFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁') :
    TransMotAg E I n ρ₀ k LE LT Γ A B := by
  intro R R' tA tB
  have tc := tyConvA_nf hA hB hc
  have w0 := wkOk₀A_nil E I n Γ
  -- the fiber's index walks flip and compose at every world
  have hI : IdxPerWA E I n Γ m RsF ps ls := fun ρ hρ =>
    idxPerA_ofg hsh (hFldF ρ hρ) (ihFldF ρ hρ) (ihFldFeq ρ hρ)
  cases tA with
  | fam hA₁ hn₁ hnp₁ hm₁ _ _ hps₁ hu₁ _ Rs₁ RsF₁ RsI₁ hFld₁ hFldF₁ _ _ _ _ hFldI₁ =>
      have e := whTyA_det hA hA₁ hnA hn₁
      obtain ⟨er, els, exs⟩ := foldAppsA_const_inj e
      subst er; subst els
      rw [hm] at hm₁
      injection hm₁ with em
      subst em
      obtain ⟨eps, eis⟩ := List.append_inj exs (by rw [hps, hps₁])
      subst eps; subst eis
      obtain ⟨TF, hTF, _⟩ := applyTelA_append_some hu₁
      cases tB with
      | fam hB₂ hn₂ _ hm₂ _ _ hps₂ hu₂ _ Rs₂ RsF₂ RsI₂ hFld₂ hFldF₂ _ _ _ _ hFldI₂ =>
          have e := whTyA_det hB hB₂ hnB hn₂
          obtain ⟨er, els, exs⟩ := foldAppsA_const_inj e
          subst er; subst els
          rw [hm] at hm₂
          injection hm₂ with em
          subst em
          obtain ⟨eps, eis⟩ := List.append_inj exs (by rw [hps', hps₂])
          subst eps; subst eis
          obtain ⟨TF', hTF', _⟩ := applyTelA_append_some hu₂
          -- the two carriers are cross-related by the type equality (at the identity world)
          have hK : RecDomRelXA E I n (wkCtxA [] Γ) r m (RsF []) ls (ps.map (wkExprA []))
              (ps'.map (wkExprA [])) (foldAppsA (.const r ls) (ps ++ is))
              (foldAppsA (.const r ls') (ps' ++ is')) := by
            rw [map_wkExprA_nil, map_wkExprA_nil]
            exact ⟨ls, ls', is, is', TF, TF', rfl, rfl, eqNListB_refl (whTyA_famApp_bounded hA),
              ⟨hls, whTyA_famApp_bounded hB⟩, hTF, hTF', hxs TF hTF, tc⟩
          -- what the carrier needs to cross, at every world: the cross data, the relation
          -- equalities from the transport induction hypotheses against the right type's data
          have hX : CrossWA E I n Γ r m Rs Rs₂ RsF RsF₂ RsI RsI₂ ps ps' ls ls' := by
            intro ρ hρ
            refine ⟨?_, ?_, ?_, ?_, ?_, hpar ρ hρ, ?_⟩
            · intro lsF TF₀ TF₀' pre pre' D uD C vC D' uD' C' vC' hl hT₀ hT₀' hw hw' hD hD'
              exact ihXFeq ρ hρ lsF TF₀ TF₀' pre pre' D uD C vC D' uD' C' vC' hl hT₀ hT₀' hw hD hD' _ _
                (hFldF ρ hρ lsF TF₀ pre pre' D uD C vC hl hT₀ hw hD)
                (hFldF₂ ρ hρ lsF TF₀' pre pre' D' uD' C' vC' ⟨eqNListA_trans (eqNListA_symm hls) hl.1, hl.2⟩
                  hT₀' hw' hD')
            · intro c cm lsA lsA' lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam
                hkinds hsp hlA hlAC hlA' hlA'C hT hT' hw hw' hD hD'
              exact ihXFld ρ hρ c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk
                hfam hkinds hsp hlA hlAC hT hT' hw hD hD' _ _
                (hFld ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlAC
                  hT hw hD)
                (hFld₂ ρ hρ c cm lsA' lsC kinds ksPre ks T' pre pre' D' uD' C' vC' hcm hk hfam hkinds hsp
                  hlA' hlA'C hT' hw' hD')
            · intro c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds
                hsp hlA hlAC hT hT' hw hD hD'
              exact hXRec ρ hρ c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk
                hfam hkinds hsp hlA hlAC hT hT' hw hD hD'
            · -- (I): the inner telescopes are rigid of one Π-count; along doubly-walked inner prefixes the
              -- two inner relations are one (transport against the right type's data); the codomains
              -- are cross-related
              intro c cm lsA lsA' lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam
                hkinds hsp hlA hlAC hlA' hlA'C hT hT' hw hw' hD hD' ρ' hρ'
              have hpsρ : (ps.map (wkExprA ρ)).length = m.nparamsA := by rw [List.length_map]; exact hps
              have hps'ρ : (ps'.map (wkExprA ρ)).length = m.nparamsA := by rw [List.length_map]; exact hps'
              have hrD := rigTel_of_shape hEN hcm hk hfam hkinds hsp hpsρ (argsRelA_length hw).1 hT hD
              have hrD' := rigTel_of_shape hEN hcm hk hfam hkinds hsp hps'ρ (argsRelA_length hw').1 hT' hD'
              have hwD := rigid_wkExprA ρ' D hrD.1
              have hwD' := rigid_wkExprA ρ' D' hrD'.1
              have hcnt : (piDomsA (wkExprA ρ' D)).length = (piDomsA (wkExprA ρ' D')).length := by
                rw [hwD.2, hwD'.2, hrD.2, hrD'.2]
              have hone : ∀ (q q' : List ExprA) (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA)
                  (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
                  ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ')
                    0 [] (wkExprA ρ' D) q q' →
                  ArgsRelPA (innerRelsA RsI₂ ρ c lsC (m.nparamsA + ksPre.length) (ps'.map (wkExprA ρ) ++ pre) ρ')
                    0 [] (wkExprA ρ' D') q q' →
                  applyTelA q (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
                  applyTelA q (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
                  innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' q.length q =
                    innerRelsA RsI₂ ρ c lsC (m.nparamsA + ksPre.length) (ps'.map (wkExprA ρ) ++ pre) ρ' q.length
                      q :=
                fun q q' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' wl wr h1 h1' =>
                  ihXFldI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam
                    hkinds hsp hlA hlAC hT hT' hw hD hD' ρ' hρ' q q' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' wl h1 h1' _ _
                    (hFldI ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlAC
                      hT hw hD ρ' hρ' q q' D₁ u₁ C₁ v₁ wl h1)
                    (hFldI₂ ρ hρ c cm lsA' lsC kinds ksPre ks j T' pre pre' D' uD' C' vC' hcm hk hfam hkinds hsp
                      hlA' hlA'C hT' hw' hD' ρ' hρ' q q' D₁' u₁' C₁' v₁' wr h1')
              exact innerCrossA_of_one hwD.1 hwD'.1 hcnt hone (fun zs zs' C₁ C₁' hzs hl hC hC' =>
                hXRecI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam
                  hkinds hsp hlA hlAC hT hT' hw hD hD' ρ' hρ' zs zs' C₁ C₁' hzs hl hC hC')
            · intro c cm lsA lsC lsC' kinds T T₁ T' T₁' pre pre' Rr Rr₁ Rr' Rr₁' hcm hk hfam hkinds hlA
                hlAC hlCC hT hT₁ hT' hT₁' hw hR hR₁ hR' hR₁'
              exact ⟨hXRes ρ hρ c cm lsA lsC kinds T T₁ pre pre' Rr Rr₁ hcm hk hfam hkinds hlA hlAC hT hT₁
                  hw hR hR₁,
                hXResR ρ hρ c cm lsA lsC lsC' kinds T T' T₁' pre pre' Rr' Rr₁' hcm hk hfam hkinds hlA hlAC
                  hlCC hT hT' hT₁' hw hR' hR₁'⟩
            · -- the declared domains of a function-recursive position are convertible
              intro c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds hsp
                hlA hlAC hT hT' hw hD hD'
              exact hXFldIdom ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk
                hfam hkinds hsp hlA hlAC hT hT' hw hD hD'
          have hAp : carrierParamsA m (foldAppsA (.const r ls) (ps ++ is)) = ps.map (wkExprA []) := by
            rw [map_wkExprA_nil]; exact carrierParamsA_famApp hps ls
          have hAl : eqNList ls (carrierLevelsA (foldAppsA (.const r ls) (ps ++ is))) := by
            rw [carrierLevelsA_foldAppsA]; exact eqNListA_refl ls
          funext a b
          apply propext
          constructor
          · intro h
            -- the left type's own fixed point is the type equality's (one fiber), then crosses
            have h1 := lfpWA_le_of (ps := ps) (ls₀ := ls)
              (fun ρ hρ c cm lsC lsA kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT
                  h1 h2 hTD =>
                TyKA_uniqueg
                  (hFld₁ ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h1 hTD)
                  (hFld ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h2 hTD))
              (fun ρ hρ lsF TF₀ pre pre' D uD C vC hlF hTF₀ h1 h2 hTD =>
                TyKA_uniqueg (hFldF₁ ρ hρ lsF TF₀ pre pre' D uD C vC hlF hTF₀ h1 hTD)
                  (hFldF ρ hρ lsF TF₀ pre pre' D uD C vC hlF hTF₀ h2 hTD))
              (fun ρ hρ c cm lsC lsA kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT
                  h1 h2 hTD ρ' hρ' ys ys' Bi uBi Ci vBi hy1 hy2 hB => by
                rw [Nat.zero_add, List.nil_append]
                exact TyKA_uniqueg
                  (hFldI₁ ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h1 hTD ρ' hρ' ys ys' Bi uBi Ci vBi hy1 hB)
                  (hFldI ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h2 hTD ρ' hρ' ys ys' Bi uBi Ci vBi hy2 hB))
              w0 hAp hAl h
            exact lfpWA_cross_fwd hsh hEN hI hX hps hps' hls w0 hAp hAl h1 hK
          · intro h
            have h1 := lfpWA_cross_bwd hsh hEN hI hX hps hps' hls w0
              (by rw [map_wkExprA_nil]; exact carrierParamsA_famApp hps' ls')
              (by rw [carrierLevelsA_foldAppsA]; exact eqNListA_refl ls') h hK
            exact lfpWA_le_of (ps := ps) (ls₀ := ls)
              (fun ρ hρ c cm lsC lsA kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT
                  h1 h2 hTD =>
                TyKA_uniqueg
                  (hFld ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h1 hTD)
                  (hFld₁ ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h2 hTD))
              (fun ρ hρ lsF TF₀ pre pre' D uD C vC hlF hTF₀ h1 h2 hTD =>
                TyKA_uniqueg (hFldF ρ hρ lsF TF₀ pre pre' D uD C vC hlF hTF₀ h1 hTD)
                  (hFldF₁ ρ hρ lsF TF₀ pre pre' D uD C vC hlF hTF₀ h2 hTD))
              (fun ρ hρ c cm lsC lsA kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC hT
                  h1 h2 hTD ρ' hρ' ys ys' Bi uBi Ci vBi hy1 hy2 hB => by
                rw [Nat.zero_add, List.nil_append]
                exact TyKA_uniqueg
                  (hFldI ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h1 hTD ρ' hρ' ys ys' Bi uBi Ci vBi hy1 hB)
                  (hFldI₁ ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlC
                    hT h2 hTD ρ' hρ' ys ys' Bi uBi Ci vBi hy2 hB))
              w0 hAp hAl h1
      | prop hB₂ hn₂ hP₂ =>
          have e := whTyA_det hB hB₂ hnB hn₂
          subst e
          have hlen : (ps ++ is).length = (ps' ++ is').length := by
            simp only [List.length_append, hps, hps', argsRelPA_length (hxs TF hTF)]
          exact absurd ((isPropTy_famApp_congr hm hsh hls hlen).2 hP₂) hnp₁
      | sortT hB₂ _ _ =>
          have e := whTyA_det hB hB₂ hnB (hStepFnA_sort _ _ _ _)
          exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
      | sortP hB₂ _ =>
          have e := whTyA_det hB hB₂ hnB (hStepFnA_sort _ _ _ _)
          exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
      | pi hB₂ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₂ hnB (hStepFnA_pi _ _ _ _ _ _ _)
          exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | stuck hB₂ hN₂ =>
          have e := whTyA_det hB hB₂ hnB hN₂.1
          exact (stuckA_not_fam hN₂ (by rw [← e, foldAppsA_const_head]) hm hind).elim
  | prop hA₁ hn₁ hP₁ =>
      have e := whTyA_det hA hA₁ hnA hn₁
      subst e
      cases tB with
      | prop hB₂ hn₂ _ =>
          have e := whTyA_det hB hB₂ hnB hn₂
          subst e
          exact tripleA_eq_of_tyConv tc
      | fam hB₂ hn₂ hnp₂ hm₂ _ _ hps₂ hu₂ _ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₂ hnB hn₂
          obtain ⟨er, els, exs⟩ := foldAppsA_const_inj e
          subst er; subst els
          rw [hm] at hm₂
          injection hm₂ with em
          subst em
          obtain ⟨eps, eis⟩ := List.append_inj exs (by rw [hps', hps₂])
          subst eps; subst eis
          obtain ⟨TF', hTF', _⟩ := applyTelA_append_some hu₂
          obtain ⟨TF, hTF⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) ls' ls
            (by rw [hps, hps']) hTF'
          have hlen : (ps ++ is).length = (ps' ++ is').length := by
            simp only [List.length_append, hps, hps', argsRelPA_length (hxs TF hTF)]
          exact absurd ((isPropTy_famApp_congr hm hsh hls hlen).1 hP₁) hnp₂
      | sortT hB₂ _ _ =>
          have e := whTyA_det hB hB₂ hnB (hStepFnA_sort _ _ _ _)
          exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
      | sortP hB₂ _ =>
          have e := whTyA_det hB hB₂ hnB (hStepFnA_sort _ _ _ _)
          exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
      | pi hB₂ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB hB₂ hnB (hStepFnA_pi _ _ _ _ _ _ _)
          exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | stuck hB₂ hN₂ =>
          have e := whTyA_det hB hB₂ hnB hN₂.1
          exact (stuckA_not_fam hN₂ (by rw [← e, foldAppsA_const_head]) hm hind).elim
  | sortT hA₁ _ _ =>
      have e := whTyA_det hA hA₁ hnA (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | sortP hA₁ _ =>
      have e := whTyA_det hA hA₁ hnA (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | pi hA₁ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA₁ hnA (hStepFnA_pi _ _ _ _ _ _ _)
      exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck hA₁ hN₁ =>
      have e := whTyA_det hA hA₁ hnA hN₁.1
      exact (stuckA_not_fam hN₁ (by rw [← e, foldAppsA_const_head]) hm hind).elim

end Transport

#print axioms idxPerA_ofg
#print axioms ctorPerA_ofg
#print axioms transMinor_famg

end Rcic.Declarative.Ann
