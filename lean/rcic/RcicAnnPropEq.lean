import rcic.RcicAnnFamWk

/-!
# M2-g′ — `PropEqA`: the structure of a proposition as an element of `Prop`, level-free

`TyKA.sortP` related two propositions as elements of a `Prop`-level sort by conversion alone
(R-PropOutOfTower, `RcicAnnLR` item 9), so the rows at `sort 0` could not be read off the relation.
M2-g′-0 measured the planned top layer (a separate conjunct proved after the tower) CIRCULAR at a
`Prop` variable: a valid pair relates `σX`, `σ'X` at `sort 0` by the relation's datum only, so the
conjunct's variable case is the row itself. `PropEqA` is the datum `sortP` carries instead: the
STRUCTURE of the two propositions, stated BELOW the logical relation — no height, no level of the
sort, no relation — so that validity carries it and the fundamental theorem's variable case is free.

* `pi`: both sides reduce (typed) to pis with `=ₙ` annotations, typed domains that convert in
  every world, and codomains with the same structure IN EVERY WORLD `ρ` UNDER EVERY BINDER `D₀`
  CONVERTIBLE TO THE LEFT DOMAIN. The quantification over binders replaces context conversion,
  which the copy proves only after the relation (`RcicAnnCtxConv` imports `RcicAnnLevels` →
  `RcicAnnLREnv`): symmetry and transitivity re-read the codomain datum across the domain
  conversion, weakening composes worlds, and the Kripke domain conversion keeps all three free of
  `EnvClosedA` (the PER runs inside `eqKA_transport_per`, which has none). Quantifying over typed
  arguments `a` instead (`C[a]`) fails at production: the fundamental theorem relates `σC[a]`,
  `σ'C[a]` only at a RELATED `a`. Production: the IH on the codomain under the pair weakened into
  `ρ` and pushed under `D₀`, variable `0` by reflection at the substituted domain and typed
  through the conversion (`ValidSubstA_upConv`, `propEqA_codom_of_fund`).
* `fam`: both sides reduce to applications of the same family of `E`, at `=ₙ` level lists, with
  the argument lists two-sided convertible (`ParConvA`) along the family's type at every bounded
  list `=ₙ` the left one — `EqKA.fam`'s `hpar` shape, over all the arguments: symmetric and
  transitive by `eqNListB` alone. Production: the families' clause at a `Prop` family
  (`famArgsParConvA`: `validSubstA_of_tel_lv` over the whole telescope, `parConvA_of_validSubst`).
* `stuck`: both sides reduce to stuck types (`StuckA`: normal, headed by no sort, pi or family).
  Production: reflection (`reflMinor_sortP`, `propEqA_stuck_refl`).

Every clause carries the conversion of the two sides, so soundness is a projection
(`propEqA_tyConv`). The calculus — symmetry, transitivity (the middle normal form is unique,
`whTyA_det`), weakening (worlds compose; no induction), head expansion on either side (a typed
step prepended to the chain) — is everything the relation's stack asks of the datum: PER,
transport (level-free, nothing to move), weakening, head expansion, reflection. The rows at
`sort 0` invert it at rigid normal forms (`propEqA_pi_inv`, `propEqA_famApp_inv`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- two propositions with the same STRUCTURE, below the logical relation (M2-g′). -/
inductive PropEqA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : LCtxA → ExprA → ExprA → Prop
  | pi {Γ : LCtxA} {a b D C D' C' : ExprA} {u v u' v' : Level}
      (ha : WhTyA E I n Γ a (.pi D u C v)) (hb : WhTyA E I n Γ b (.pi D' u' C' v'))
      (hu : eqN u u') (hv : eqN v v')
      (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
      (hD'ty : Nonempty (HasTyA E I n Γ D' (.sort u')))
      (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        Nonempty (TyConvA E I n (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D')))
      (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ D₀ : ExprA,
        Nonempty (CtxWfA E I n (.assumption D₀ :: wkCtxA ρ Γ)) →
        Nonempty (TyConvA E I n (wkCtxA ρ Γ) D₀ (wkExprA ρ D)) →
        PropEqA E I n (.assumption D₀ :: wkCtxA ρ Γ)
          (wkExprA (WkSpecA.ub ρ) C) (wkExprA (WkSpecA.ub ρ) C'))
      (hc : Nonempty (TyConvA E I n Γ a b)) : PropEqA E I n Γ a b
  | fam {Γ : LCtxA} {a b : ExprA} {r : Nat} {ls ls' : List Level} {xs xs' : List ExprA}
      {m : CheckedMemberA}
      (ha : WhTyA E I n Γ a (foldAppsA (.const r ls) xs))
      (hb : WhTyA E I n Γ b (foldAppsA (.const r ls') xs'))
      (hna : hStepFnA E I.fn Γ (foldAppsA (.const r ls) xs) = none)
      (hnb : hStepFnA E I.fn Γ (foldAppsA (.const r ls') xs') = none)
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hls : eqNList ls ls')
      (hargs : ∀ lsX : List Level, eqNListB n ls lsX →
        ParConvA E I n Γ (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA) xs xs')
      (hc : Nonempty (TyConvA E I n Γ a b)) : PropEqA E I n Γ a b
  | stuck {Γ : LCtxA} {a b N N' : ExprA}
      (ha : WhTyA E I n Γ a N) (hb : WhTyA E I n Γ b N')
      (hN : StuckA E I Γ N) (hN' : StuckA E I Γ N')
      (hc : Nonempty (TyConvA E I n Γ a b)) : PropEqA E I n Γ a b

section PropEq
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-! ## (0) two shape facts before the relation -/

/-- a chain's head is its own (empty) chain. -/
theorem whTyA_headRefl {Γ : LCtxA} {A N : ExprA} (h : WhTyA E I n Γ A N) : WhTyA E I n Γ A A :=
  (whTyA_hasTy_head h).elim fun _ t => t.elim fun t => whTyA_of_hasTy t

/-- a family application is not stuck. -/
theorem stuckA_not_famApp {Γ : LCtxA} {r : Nat} {ls : List Level} {xs : List ExprA}
    {m : CheckedMemberA} (h : StuckA E I Γ (foldAppsA (.const r ls) xs))
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) : False :=
  stuckA_not_fam h (by rw [foldAppsA_const_head]) hm hind

/-! ## (1) soundness, reflexivity at stuck types -/

theorem propEqA_tyConv {Γ : LCtxA} {a b : ExprA} :
    PropEqA E I n Γ a b → Nonempty (TyConvA E I n Γ a b)
  | .pi _ _ _ _ _ _ _ _ hc => hc
  | .fam _ _ _ _ _ _ _ _ hc => hc
  | .stuck _ _ _ _ hc => hc

/-- a typed stuck type has its own structure (the reflection lemma's `sortP` case). -/
theorem propEqA_stuck_refl {Γ : LCtxA} {a b : ExprA} {l : Level}
    (ha : Nonempty (HasTyA E I n Γ a (.sort l))) (hb : Nonempty (HasTyA E I n Γ b (.sort l)))
    (hna : StuckA E I Γ a) (hnb : StuckA E I Γ b) (hab : Nonempty (ConvA E I n Γ a b (.sort l))) :
    PropEqA E I n Γ a b :=
  .stuck (ha.elim fun t => whTyA_of_hasTy t) (hb.elim fun t => whTyA_of_hasTy t) hna hnb
    (ha.elim fun ta => hb.elim fun tb => hab.elim fun c =>
      ⟨.of Γ a b l l l ta (eqNA_refl l) tb (eqNA_refl l) c⟩)

/-! ## (2) symmetry and transitivity -/

theorem propEqA_symm {Γ : LCtxA} {a b : ExprA}
    (h : PropEqA E I n Γ a b) : PropEqA E I n Γ b a := by
  induction h with
  | pi ha hb hu hv hDty hD'ty hD _ hc ih =>
      refine .pi hb ha (eqNA_symm hu) (eqNA_symm hv) hD'ty hDty
        (fun ρ hρ => (hD ρ hρ).elim fun d => ⟨d.symm⟩)
        (fun ρ hρ D₀ hctx hD₀ => ih ρ hρ D₀ hctx ?_) (hc.elim fun c => ⟨c.symm⟩)
      exact hD₀.elim fun d₀ => (hD ρ hρ).elim fun d => ⟨.trans _ _ _ _ d₀ d.symm⟩
  | fam ha hb hna hnb hm hind hls hargs hc =>
      exact .fam hb ha hnb hna hm hind (eqNListA_symm hls)
        (fun lsX h => parConvA_symm (hargs lsX ⟨eqNListA_trans hls h.1, h.2⟩))
        (hc.elim fun c => ⟨c.symm⟩)
  | stuck ha hb hN hN' hc => exact .stuck hb ha hN' hN (hc.elim fun c => ⟨c.symm⟩)

theorem propEqA_trans {Γ : LCtxA} {a b c : ExprA}
    (h₁ : PropEqA E I n Γ a b) (h₂ : PropEqA E I n Γ b c) : PropEqA E I n Γ a c := by
  induction h₁ generalizing c with
  | @pi Γ a b D C D' C' u v u' v' ha hb hu hv hDty hD'ty hD _ hc ih =>
      cases h₂ with
      | pi hb₂ hc₂ hu₂ hv₂ _ hD'ty₂ hD₂ hC₂ hc₂' =>
          have e := whTyA_det hb hb₂ (hStepFnA_pi E I.fn Γ D' u' C' v') (hStepFnA_pi E I.fn Γ _ _ _ _)
          injection e with e1 e2 e3 e4
          subst e1 e2 e3 e4
          refine .pi ha hc₂ (eqNA_trans hu hu₂) (eqNA_trans hv hv₂) hDty hD'ty₂
            (fun ρ hρ => (hD ρ hρ).elim fun d => (hD₂ ρ hρ).elim fun d₂ => ⟨.trans _ _ _ _ d d₂⟩)
            (fun ρ hρ D₀ hctx hD₀ => ih ρ hρ D₀ hctx hD₀ (hC₂ ρ hρ D₀ hctx ?_))
            (hc.elim fun x => hc₂'.elim fun y => ⟨.trans _ _ _ _ x y⟩)
          exact hD₀.elim fun d₀ => (hD ρ hρ).elim fun d => ⟨.trans _ _ _ _ d₀ d⟩
      | fam hb₂ _ hnb₂ _ _ _ _ _ _ =>
          exact absurd (whTyA_det hb hb₂ (hStepFnA_pi E I.fn Γ D' u' C' v') hnb₂).symm
            (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | stuck hb₂ _ hN₂ _ _ =>
          have e := whTyA_det hb hb₂ (hStepFnA_pi E I.fn Γ D' u' C' v') hN₂.1
          subst e
          exact (stuckA_not_pi hN₂).elim
  | @fam Γ a b r ls ls' xs xs' m ha hb hna hnb hm hind hls hargs hc =>
      cases h₂ with
      | pi hb₂ _ _ _ _ _ _ _ _ =>
          exact absurd (whTyA_det hb hb₂ hnb (hStepFnA_pi E I.fn Γ _ _ _ _))
            (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | fam hb₂ hc₂ hnb₂ hnc₂ hm₂ _ hls₂ hargs₂ hc₂' =>
          obtain ⟨e1, e2, e3⟩ := foldAppsA_const_inj (whTyA_det hb hb₂ hnb hnb₂)
          subst e1 e2 e3
          rw [hm] at hm₂
          injection hm₂ with e4
          subst e4
          exact .fam ha hc₂ hna hnc₂ hm hind (eqNListA_trans hls hls₂)
            (fun lsX h => parConvA_trans (hargs lsX h)
              (hargs₂ lsX ⟨eqNListA_trans (eqNListA_symm hls) h.1, h.2⟩))
            (hc.elim fun x => hc₂'.elim fun y => ⟨.trans _ _ _ _ x y⟩)
      | stuck hb₂ _ hN₂ _ _ =>
          have e := whTyA_det hb hb₂ hnb hN₂.1
          rw [← e] at hN₂
          exact (stuckA_not_famApp hN₂ hm hind).elim
  | stuck ha hb hN hN' hc =>
      cases h₂ with
      | pi hb₂ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hb hb₂ hN'.1 (hStepFnA_pi E I.fn _ _ _ _ _)
          subst e
          exact (stuckA_not_pi hN').elim
      | fam hb₂ _ hnb₂ _ hm₂ hind₂ _ _ _ =>
          have e := whTyA_det hb hb₂ hN'.1 hnb₂
          subst e
          exact (stuckA_not_famApp hN' hm₂ hind₂).elim
      | stuck hb₂ hc₂ hN₂ hN₂' hc₂' =>
          exact .stuck ha hc₂ hN hN₂' (hc.elim fun x => hc₂'.elim fun y => ⟨.trans _ _ _ _ x y⟩)

/-! ## (3) weakening: worlds compose -/

theorem propEqA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {a b : ExprA}
    (h : PropEqA E I n Γ a b) (ρ : WkSpecA) (hρ : WkOkA E I n ρ Γ) :
    PropEqA E I n (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) := by
  cases h with
  | pi ha hb hu hv hDty hD'ty hD hC hc =>
      have ha' := whTyA_wk hE hI Γ ρ hρ.1 ha
      have hb' := whTyA_wk hE hI Γ ρ hρ.1 hb
      rw [wkExprA_pi_ub] at ha' hb'
      have hDty' := hasTyA_wk_ne hE hI ρ hρ.1 hDty
      have hD'ty' := hasTyA_wk_ne hE hI ρ hρ.1 hD'ty
      rw [wkExprA_sort] at hDty' hD'ty'
      refine .pi ha' hb' hu hv hDty' hD'ty' (fun ρ' hρ' => ?_)
        (fun ρ' hρ' D₀ hctx hD₀ => ?_) (tyConvA_wk_ne hE hI ρ hρ.1 hc)
      · have hD' := hD (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ')
        rw [wkCtxA_comp, wkExprA_comp, wkExprA_comp] at hD'
        exact hD'
      have hC' := hC (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ') D₀ (by rw [wkCtxA_comp]; exact hctx)
        (by rw [wkCtxA_comp, wkExprA_comp]; exact hD₀)
      rw [wkCtxA_comp, WkSpecA.ub_comp, wkExprA_comp, wkExprA_comp] at hC'
      exact hC'
  | @fam _ _ _ r ls ls' xs xs' m ha hb hna hnb hm hind hls hargs hc =>
      have ha' := whTyA_wk hE hI Γ ρ hρ.1 ha
      have hb' := whTyA_wk hE hI Γ ρ hρ.1 hb
      have hna' := hStepFnA_wk_none hE hI Γ ρ hρ.1 hna
      have hnb' := hStepFnA_wk_none hE hI Γ ρ hρ.1 hnb
      rw [wkExprA_foldAppsA, wkExprA_const] at ha' hb' hna' hnb'
      refine .fam ha' hb' hna' hnb' hm hind hls (fun lsX h => ?_) (tyConvA_wk_ne hE hI ρ hρ.1 hc)
      have hargs' := parConvA_wk hE hI ρ hρ.1 (hargs lsX h)
      rw [wkExprA_closed (liftA_instantiateLevelsA_closed (hE r m hm).1 lsX) ρ] at hargs'
      exact hargs'
  | stuck ha hb hN hN' hc =>
      exact .stuck (whTyA_wk hE hI Γ ρ hρ.1 ha) (whTyA_wk hE hI Γ ρ hρ.1 hb)
        (stuckA_wk hE hI Γ ρ hρ.1 hN) (stuckA_wk hE hI Γ ρ hρ.1 hN') (tyConvA_wk_ne hE hI ρ hρ.1 hc)

/-! ## (4) head expansion on either side: a typed step prepended to the chain -/

theorem whTyA_expand {Γ : LCtxA} {a a' N : ExprA} {l : Level}
    (ht : Nonempty (HasTyA E I n Γ a (.sort l))) (hs : Nonempty (TyHRedA E I n Γ a a' (.sort l)))
    (h : WhTyA E I n Γ a' N) : WhTyA E I n Γ a N :=
  ht.elim fun t => hs.elim fun s => whTyA_cons t s h

theorem tyConvA_of_step {Γ : LCtxA} {a a' : ExprA} {l : Level}
    (ht : Nonempty (HasTyA E I n Γ a (.sort l))) (hs : Nonempty (TyHRedA E I n Γ a a' (.sort l))) :
    Nonempty (TyConvA E I n Γ a a') :=
  ht.elim fun t => hs.elim fun s =>
    ⟨.of Γ a a' l l l t (eqNA_refl l) (tyHRedA_hasTy_right s) (eqNA_refl l) (tyHRedA_conv s)⟩

theorem propEqA_expand_left {Γ : LCtxA} {a a' b : ExprA} {l : Level}
    (ht : Nonempty (HasTyA E I n Γ a (.sort l))) (hs : Nonempty (TyHRedA E I n Γ a a' (.sort l)))
    (h : PropEqA E I n Γ a' b) : PropEqA E I n Γ a b := by
  have hc₀ := tyConvA_of_step ht hs
  cases h with
  | pi ha hb hu hv hDty hD'ty hD hC hc =>
      exact .pi (whTyA_expand ht hs ha) hb hu hv hDty hD'ty hD hC
        (hc₀.elim fun x => hc.elim fun y => ⟨.trans _ _ _ _ x y⟩)
  | fam ha hb hna hnb hm hind hls hargs hc =>
      exact .fam (whTyA_expand ht hs ha) hb hna hnb hm hind hls hargs
        (hc₀.elim fun x => hc.elim fun y => ⟨.trans _ _ _ _ x y⟩)
  | stuck ha hb hN hN' hc =>
      exact .stuck (whTyA_expand ht hs ha) hb hN hN'
        (hc₀.elim fun x => hc.elim fun y => ⟨.trans _ _ _ _ x y⟩)

theorem propEqA_expand_right {Γ : LCtxA} {a b b' : ExprA} {l : Level}
    (ht : Nonempty (HasTyA E I n Γ b (.sort l))) (hs : Nonempty (TyHRedA E I n Γ b b' (.sort l)))
    (h : PropEqA E I n Γ a b') : PropEqA E I n Γ a b := by
  have hc₀ := tyConvA_of_step ht hs
  cases h with
  | pi ha hb hu hv hDty hD'ty hD hC hc =>
      exact .pi ha (whTyA_expand ht hs hb) hu hv hDty hD'ty hD hC
        (hc₀.elim fun x => hc.elim fun y => ⟨.trans _ _ _ _ y x.symm⟩)
  | fam ha hb hna hnb hm hind hls hargs hc =>
      exact .fam ha (whTyA_expand ht hs hb) hna hnb hm hind hls hargs
        (hc₀.elim fun x => hc.elim fun y => ⟨.trans _ _ _ _ y x.symm⟩)
  | stuck ha hb hN hN' hc =>
      exact .stuck ha (whTyA_expand ht hs hb) hN hN'
        (hc₀.elim fun x => hc.elim fun y => ⟨.trans _ _ _ _ y x.symm⟩)

/-! ## (5) inversion at rigid normal forms: what the rows at `sort 0` read -/

/-- two pis with the same structure: `=ₙ` annotations, convertible domains, and the codomains'
    structure under the left domain. -/
theorem propEqA_pi_inv {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    {D' : ExprA} {u' : Level} {C' : ExprA} {v' : Level} (hΓ : Nonempty (CtxWfA E I n Γ))
    (h : PropEqA E I n Γ (.pi D u C v) (.pi D' u' C' v')) :
    eqN u u' ∧ eqN v v' ∧ Nonempty (TyConvA E I n Γ D D') ∧
    PropEqA E I n (.assumption D :: Γ) C C' := by
  cases h with
  | pi ha hb hu hv hDty _ hD hC _ =>
      have e1 := whTyA_det ha (whTyA_headRefl ha) (hStepFnA_pi E I.fn Γ _ _ _ _)
        (hStepFnA_pi E I.fn Γ D u C v)
      have e2 := whTyA_det hb (whTyA_headRefl hb) (hStepFnA_pi E I.fn Γ _ _ _ _)
        (hStepFnA_pi E I.fn Γ D' u' C' v')
      injection e1 with e11 e12 e13 e14
      injection e2 with e21 e22 e23 e24
      subst e11 e12 e13 e14 e21 e22 e23 e24
      refine ⟨hu, hv, hD [] ⟨trivial, hΓ⟩, ?_⟩
      exact hC [] ⟨trivial, hΓ⟩ _ (hΓ.elim fun c => hDty.elim fun t => ⟨.assumption c t⟩)
        ⟨.refl _ _⟩
  | fam ha _ hna _ _ _ _ _ _ =>
      exact absurd (whTyA_det ha (whTyA_headRefl ha) hna (hStepFnA_pi E I.fn Γ D u C v))
        (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck ha _ hN _ _ =>
      have e := whTyA_det ha (whTyA_headRefl ha) hN.1 (hStepFnA_pi E I.fn Γ D u C v)
      subst e
      exact (stuckA_not_pi hN).elim

/-- two family applications with the same structure: the same family, `=ₙ` level lists, the
    arguments two-sided convertible along the two telescope instances. -/
theorem propEqA_famApp_inv {Γ : LCtxA} {r r' : Nat} {ls ls' : List Level} {xs xs' : List ExprA}
    {m : CheckedMemberA} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) xs) = none)
    (hn' : hStepFnA E I.fn Γ (foldAppsA (.const r' ls') xs') = none)
    (h : PropEqA E I n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r' ls') xs')) :
    r = r' ∧ eqNList ls ls' ∧ ∀ lsX : List Level, eqNListB n ls lsX →
      ParConvA E I n Γ (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA) xs xs' := by
  cases h with
  | pi ha _ _ _ _ _ _ _ _ =>
      exact absurd (whTyA_det ha (whTyA_headRefl ha) (hStepFnA_pi E I.fn Γ _ _ _ _) hn).symm
        (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | fam ha hb hna hnb hm₀ _ hls hargs _ =>
      obtain ⟨e1, e2, e3⟩ := foldAppsA_const_inj (whTyA_det ha (whTyA_headRefl ha) hna hn)
      obtain ⟨e4, e5, e6⟩ := foldAppsA_const_inj (whTyA_det hb (whTyA_headRefl hb) hnb hn')
      subst e1 e2 e3 e4 e5 e6
      rw [hm] at hm₀
      injection hm₀ with e7
      subst e7
      exact ⟨rfl, hls, hargs⟩
  | stuck ha _ hN _ _ =>
      have e := whTyA_det ha (whTyA_headRefl ha) hN.1 hn
      rw [e] at hN
      exact (stuckA_not_famApp hN hm hind).elim

end PropEq

#print axioms propEqA_symm
#print axioms propEqA_trans
#print axioms propEqA_wk
#print axioms propEqA_expand_left
#print axioms propEqA_expand_right
#print axioms propEqA_pi_inv
#print axioms propEqA_famApp_inv

end Rcic.Declarative.Ann
