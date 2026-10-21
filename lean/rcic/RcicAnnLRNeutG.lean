import rcic.RcicAnnLRNeut
import rcic.RcicAnnLRExpG
/-!
# M2-c — reflection: extended neutrals are related whenever typed and convertible

L-RING C3-H's `NeutK`/`TyK_neutK_rel` (`research/rcic/lring-20261003`, the face
`RcicLRNeut.lean`) on the copy. `NeutKA Γ e`: weak-head normal for `hStepFnA`
under every world and every further application, and headed by neither a sort
nor a pi. The copy has no inductive families yet (they are stuck types until
M2-f), so the face's `¬ CtorHead` conjunct has nothing to exclude and is absent.

`reflectAg`: at a valid type, two extended neutrals typed at it and convertible
are related. Prop and stuck clauses: the relation IS typed-and-convertible at
the normal form. Sort clause: `EqKAg.stuck`/`TyKAg.stuck` at the lower height,
the neutrals being their own normal forms. Pi clause: under a world and applied
to related arguments the two sides are again extended neutrals (`neutKA_wk`,
`neutKA_app`), typed by `HasTyA.app` from the clause's data, convertible by
`ConvA.app` with the arguments' escaped conversion; the codomain's reflection
closes it (structural recursion through the clause's function-typed field, as
`TyK_neutK_rel` does on the face).

Where the extended neutrals come from: `neutKA_bvar` — a variable without a
value is one, under the hypothesis `IotaConstHeadA` (ι fires only on
constant-headed spines; `hStepFnA` consults the oracle on every application
whose head does not step). This is the fundamental theorem's variable arm
(`LRRelA_bvarg`): a typed variable is related to itself at its type by
`ConvA.refl`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) extended neutrality -/

section Neut
variable {E : ResolvedEnvA} {I : IotaIfaceA}

end Neut

/-! ## (2) where extended neutrals come from: variables, under `IotaConstHeadA` -/

section Bvar
variable {E : ResolvedEnvA} {I : IotaIfaceA}

end Bvar

/-! ## (3) reflection -/

section Reflect
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}

/-- DT-025/A-6 S1-g.2: reflection's motive in the guarded copy also reads the context's
    well-formedness — the guarded clauses' key data at a neutral TYPE come from S1-g.1's
    `PropKeyA`, which is stated in a well-formed context. -/
abbrev ReflMotKAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (A : ExprA)
    (R : ExprA → ExprA → Prop) : Prop :=
  Nonempty (CtxWfA E I n Γ) → ReflMotA E I n Γ A R

/-- DT-025/A-6 S1-g.2: the guarded stuck clause — typed-and-convertible at the normal form,
    and each neutral is its own chain. -/
theorem reflMinor_stuckg {Γ : LCtxA} {A N : ExprA} (hA : WhTyA E I n Γ A N) :
    ReflMotA E I n Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N) ∧
      ∃ Na, TyHRedStarA E I n Γ a Na N ∧ hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ b Nb N ∧ hStepFnA E I.fn Γ Nb = none) :=
  fun a b hna hnb hta htb hab => (whTyA_tyConv hA).elim fun cA =>
    ⟨hta.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩, htb.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩,
     hab.elim fun c => ⟨convA_of_tyConvA c cA⟩,
     a, hta.elim fun t => tyHRedStarA_refl (hasTyA_of_tyConvA t cA), neutKA_whnf hna,
     b, htb.elim fun t => tyHRedStarA_refl (hasTyA_of_tyConvA t cA), neutKA_whnf hnb⟩

/-- DT-025/A-6 S1-g.2: the guarded `Prop`-sort clause — two neutral propositions are their own
    normal forms, propositions for the key by K1 (`PropKeyA`, at the declared `Prop` sort). -/
theorem reflMinor_sortPg (hK : PropKeyA E I n) {Γ : LCtxA} {A : ExprA} {l : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (hz : isZero l = true) :
    ReflMotKAg E I n Γ A (fun a b =>
      PropValidKA E I n Γ a ∧ PropValidKA E I n Γ b ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA E I n Γ a b) := by
  intro hΓ a b hna hnb hta htb hab
  obtain ⟨hΓ'⟩ := hΓ
  obtain ⟨cA⟩ := whTyA_tyConv hA
  have hta' : Nonempty (HasTyA E I n Γ a (.sort l)) := hta.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have htb' : Nonempty (HasTyA E I n Γ b (.sort l)) := htb.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have hab' : Nonempty (ConvA E I n Γ a b (.sort l)) := hab.elim fun c => ⟨convA_of_tyConvA c cA⟩
  obtain ⟨ta⟩ := hta'
  obtain ⟨tb⟩ := htb'
  have hsa : WhTyA E I n Γ a a := whTyA_of_hasTy ta
  have hsb : WhTyA E I n Γ b b := whTyA_of_hasTy tb
  exact ⟨⟨a, hsa, neutKA_whnf hna, (hK.1 hΓ' ta hsa (neutKA_whnf hna)).2 hz⟩,
    ⟨b, hsb, neutKA_whnf hnb, (hK.1 hΓ' tb hsb (neutKA_whnf hnb)).2 hz⟩, ⟨ta⟩, ⟨tb⟩, hab',
    propEqA_stuck_refl ⟨ta⟩ ⟨tb⟩ (neutKA_stuck hna) (neutKA_stuck hnb) hab'⟩

/-- Type-sort clause: the neutrals are their own normal forms; `EqKAg.stuck`/
    `TyKAg.stuck` at the sort's height. -/
theorem reflMinor_sortTg (hK : PropKeyA E I n) {Γ : LCtxA} {A : ExprA} {l : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (hz : isZero l = false) (hk : ht ρ₀ l < k) :
    ReflMotKAg E I n Γ A (fun a b =>
      LREqAg E I n ρ₀ (ht ρ₀ l) Γ a b ∧
      (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ l) Γ a R) ∧
      (∃ R, LRTyAg E I n ρ₀ (ht ρ₀ l) Γ b R) ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l))) := by
  intro hΓ a b hna hnb hta htb hab
  obtain ⟨hΓ'⟩ := hΓ
  have _ := hk
  obtain ⟨cA⟩ := whTyA_tyConv hA
  have hta' : Nonempty (HasTyA E I n Γ a (.sort l)) := hta.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have htb' : Nonempty (HasTyA E I n Γ b (.sort l)) := htb.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have hab' : Nonempty (ConvA E I n Γ a b (.sort l)) := hab.elim fun c => ⟨convA_of_tyConvA c cA⟩
  have hsa : WhTyA E I n Γ a a := hta'.elim fun t => whTyA_of_hasTy t
  have hsb : WhTyA E I n Γ b b := htb'.elim fun t => whTyA_of_hasTy t
  -- K2 (S1-g.1, `PropKeyA`): a neutral TYPE declared at a non-`Prop` sort is no proposition
  have hnpa : ¬ IsPropTy E I Γ a := fun hP => by
    obtain ⟨ta⟩ := hta'
    have := (hK.1 hΓ' ta hsa (neutKA_whnf hna)).1 hP
    rw [hz] at this; cases this
  have hnpb : ¬ IsPropTy E I Γ b := fun hP => by
    obtain ⟨tb⟩ := htb'
    have := (hK.1 hΓ' tb hsb (neutKA_whnf hnb)).1 hP
    rw [hz] at this; cases this
  refine ⟨?_, ?_, ?_, hta', htb', hab'⟩
  · rw [LREqA_eqg]
    exact .stuck hsa hsb (tripleLikeA_of_stuck (neutKA_stuck hna))
      (tripleLikeA_of_stuck (neutKA_stuck hnb))
      (hta'.elim fun t => htb'.elim fun t' => hab'.elim fun c =>
        ⟨.of Γ a b l l l t (eqNA_refl l) t' (eqNA_refl l) c⟩)
      ⟨fun h => absurd h hnpa, fun h => absurd h hnpb⟩
  · exact ⟨_, by rw [LRTyA_eqg]; exact .stuck hsa (neutKA_stuck hna) hnpa⟩
  · exact ⟨_, by rw [LRTyA_eqg]; exact .stuck hsb (neutKA_stuck hnb) hnpb⟩

/-- pi clause: under a world and applied to related arguments the two sides are
    again extended neutrals, typed by `HasTyA.app` from the clause's data and
    convertible by `ConvA.app`; the codomain's reflection closes it. -/
theorem reflMinor_pig (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A D C : ExprA}
    {u v : Level} (hA : WhTyA E I n Γ A (.pi D u C v))
    (_hnp : ¬ IsPropTy E I Γ (.pi D u C v))
    (_hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKAg E I n ρ₀ k (fun j _ => LREqAg E I n ρ₀ j) (fun j _ => LRTyAg E I n ρ₀ j)
        (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
    (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      TyKAg E I n ρ₀ k (fun j _ => LREqAg E I n ρ₀ j) (fun j _ => LRTyAg E I n ρ₀ j) (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAg E I n ρ₀ k (fun j _ => LREqAg E I n ρ₀ j) (fun j _ => LRTyAg E I n ρ₀ j) (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C)))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ),
      ReflMotKAg E I n (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      ReflMotKAg E I n (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (_ihCeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'), True) :
    ReflMotKAg E I n Γ A (fun f g =>
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      Nonempty (HasTyA E I n Γ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Γ g (.pi D u C v)) ∧
      Nonempty (ConvA E I n Γ f g (.pi D u C v))) := by
  intro _ f g hnf hng htf htg hfg
  obtain ⟨cA⟩ := whTyA_tyConv hA
  have htf' : Nonempty (HasTyA E I n Γ f (.pi D u C v)) := htf.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have htg' : Nonempty (HasTyA E I n Γ g (.pi D u C v)) := htg.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have hfg' : Nonempty (ConvA E I n Γ f g (.pi D u C v)) := hfg.elim fun c => ⟨convA_of_tyConvA c cA⟩
  refine ⟨fun ρ hρ a a' hr => ?_, htf', htg', hfg'⟩
  have hfw := hasTyA_wk_ne hE hI ρ hρ.1 htf'
  have hgw := hasTyA_wk_ne hE hI ρ hρ.1 htg'
  have hcw := convA_wk_ne hE hI ρ hρ.1 hfg'
  rw [wkExprA_pi_ub] at hfw hgw hcw
  have hCw := hasTyA_wk_ne_binder hE hI ρ hρ.1 hCty
  obtain ⟨w, hTy⟩ := tyKA_hasTyg (hC ρ hρ a a' hr)
  have heq := hCeq ρ hρ a a' hr
  obtain ⟨w', hTy'⟩ := eqKA_hasTy_rightg heq
  have hargs := escapeA_hasTyg (hD ρ hρ) hr
  have caa := escapeAg (hD ρ hρ) hr
  have hta : Nonempty (HasTyA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ f) a)
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))) :=
    hCw.elim fun hB => hTy.elim fun hT => hfw.elim fun hf => hargs.1.elim fun ha =>
      ⟨.app _ _ _ _ _ u v w hB hT hf ha⟩
  have htb0 : Nonempty (HasTyA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ g) a')
      (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) :=
    hCw.elim fun hB => hTy'.elim fun hT => hgw.elim fun hg => hargs.2.elim fun ha =>
      ⟨.app _ _ _ _ _ u v w' hB hT hg ha⟩
  have htb : Nonempty (HasTyA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ g) a')
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))) :=
    (eqKA_tyConvg heq).elim fun tc => htb0.elim fun t => ⟨hasTyA_of_tyConvA t tc.symm⟩
  have capp : Nonempty (ConvA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))) :=
    hcw.elim fun cw => caa.elim fun c => hCw.elim fun hB => htb.elim fun t =>
      ⟨.app _ _ _ _ _ _ _ u v cw c hB t⟩
  exact ihC ρ hρ a a' hr hρ.2 _ _ (neutKA_app a (neutKA_wk ρ hρ.1 hnf))
    (neutKA_app a' (neutKA_wk ρ hρ.1 hng)) hta htb capp

/-- **extended neutrals typed at a valid type and convertible are related.**
    Stated at the tied lower heights, because the sort clause builds the
    lower-height relation. -/
theorem reflectAg (hE : EnvClosedA E) (hI : IotaLiftA I) (hK : PropKeyA E I n) :
    {Γ : LCtxA} → {A : ExprA} → {R : ExprA → ExprA → Prop} →
    TyKAg E I n ρ₀ k (fun j _ => LREqAg E I n ρ₀ j) (fun j _ => LRTyAg E I n ρ₀ j) Γ A R →
    Nonempty (CtxWfA E I n Γ) →
    ∀ {a b : ExprA}, NeutKA E I Γ a → NeutKA E I Γ b →
      Nonempty (HasTyA E I n Γ a A) → Nonempty (HasTyA E I n Γ b A) →
      Nonempty (ConvA E I n Γ a b A) → R a b :=
  fun {_Γ _A _R} h hΓ {a b} hna hnb hta htb hab =>
  TyKAg.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ A R _ => ReflMotKAg E I n Γ A R)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ => True.intro)
    (fun hA _ _ => fun _ => reflMinor_triple hA)
    (fun hA hz hk => reflMinor_sortTg hK hA hz hk)
    (fun hA hz => reflMinor_sortPg hK hA hz)
    (fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq =>
      reflMinor_pig hE hI hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq)
    (fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fun _ => reflMinor_fam hA)
    (fun hA _ _ => fun _ => reflMinor_stuckg hA)
    h hΓ a b hna hnb hta htb hab

/-- the knotted form. -/
theorem LRRelA_reflectg (hE : EnvClosedA E) (hI : IotaLiftA I) (hK : PropKeyA E I n)
    {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {A a b : ExprA}
    (hA : ∃ R, LRTyAg E I n ρ₀ k Γ A R) (hna : NeutKA E I Γ a) (hnb : NeutKA E I Γ b)
    (hta : Nonempty (HasTyA E I n Γ a A)) (htb : Nonempty (HasTyA E I n Γ b A))
    (hab : Nonempty (ConvA E I n Γ a b A)) : LRRelAg E I n ρ₀ k Γ A a b := by
  obtain ⟨R, hR⟩ := hA
  refine ⟨R, hR, ?_⟩
  rw [LRTyA_eqg] at hR
  exact reflectAg hE hI hK hR hΓ hna hnb hta htb hab

/-- the fundamental theorem's variable arm: a typed variable without a value is
    related to itself at its (valid) type. -/
theorem LRRelA_bvarg (hE : EnvClosedA E) (hI : IotaLiftA I) (hIC : IotaConstHeadA I)
    (hK : PropKeyA E I n) {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {A : ExprA} {i : Nat}
    (hv : lookupValueA Γ i = none)
    (hA : ∃ R, LRTyAg E I n ρ₀ k Γ A R) (ht : Nonempty (HasTyA E I n Γ (.bvar i) A)) :
    LRRelAg E I n ρ₀ k Γ A (.bvar i) (.bvar i) :=
  LRRelA_reflectg hE hI hK hΓ hA (neutKA_bvar hE hI hIC hv) (neutKA_bvar hE hI hIC hv) ht ht
    (ht.elim fun t => ⟨.refl Γ _ A t⟩)

end Reflect

#print axioms reflMinor_stuckg
#print axioms reflMinor_sortPg
#print axioms reflectAg
#print axioms LRRelA_reflectg
#print axioms LRRelA_bvarg

end Rcic.Declarative.Ann
