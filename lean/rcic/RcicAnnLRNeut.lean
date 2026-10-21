import rcic.RcicAnnLRExp

/-!
# M2-c — reflection: extended neutrals are related whenever typed and convertible

L-RING C3-H's `NeutK`/`TyK_neutK_rel` (`research/rcic/lring-20261003`, the face
`RcicLRNeut.lean`) on the copy. `NeutKA Γ e`: weak-head normal for `hStepFnA`
under every world and every further application, and headed by neither a sort
nor a pi. The copy has no inductive families yet (they are stuck types until
M2-f), so the face's `¬ CtorHead` conjunct has nothing to exclude and is absent.

`reflectA`: at a valid type, two extended neutrals typed at it and convertible
are related. Prop and stuck clauses: the relation IS typed-and-convertible at
the normal form. Sort clause: `EqKA.stuck`/`TyKA.stuck` at the lower height,
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
(`LRRelA_bvar`): a typed variable is related to itself at its type by
`ConvA.refl`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) extended neutrality -/

/-- weak-head normal under every world and every further application, not
    shape-headed, and not constructor-headed (M2-f (3b): a constructor application
    at a family is related by the `fam` clause's constructor disjunct, not as a
    neutral). -/
def NeutKA (E : ResolvedEnvA) (I : IotaIfaceA) (Γ : LCtxA) (e : ExprA) : Prop :=
  (∀ (ρ : WkSpecA), WkSpecA.ok ρ Γ → ∀ (xs : List ExprA),
      hStepFnA E I.fn (wkCtxA ρ Γ) (foldAppsA (wkExprA ρ e) xs) = none) ∧
  ¬ isShapeHeadA E (appsSpineA e).1 ∧ ¬ CtorHeadA E e

section Neut
variable {E : ResolvedEnvA} {I : IotaIfaceA}

theorem neutKA_whnf {Γ : LCtxA} {e : ExprA} (h : NeutKA E I Γ e) :
    hStepFnA E I.fn Γ e = none := h.1 [] trivial []

theorem neutKA_stuck {Γ : LCtxA} {e : ExprA} (h : NeutKA E I Γ e) : StuckA E I Γ e :=
  ⟨neutKA_whnf h, h.2.1⟩

/-- an extended neutral is a stuck TERM: normal and not constructor-headed. -/
theorem neutKA_stuckTm {Γ : LCtxA} {e : ExprA} (h : NeutKA E I Γ e) : StuckTmA E I Γ e :=
  ⟨neutKA_whnf h, h.2.2⟩

theorem ctorHeadA_of_app {f a : ExprA} (h : CtorHeadA E (.app f a)) : CtorHeadA E f := by
  obtain ⟨c, ls, m, hsp, hm, hk⟩ := h
  exact ⟨c, ls, m, by rw [← appsSpineA_app_fst f a]; exact hsp, hm, hk⟩

theorem isShapeHeadA_wk_rev : (ρ : WkSpecA) → (e : ExprA) →
    isShapeHeadA E (appsSpineA (wkExprA ρ e)).1 → isShapeHeadA E (appsSpineA e).1
  | [], _, h => h
  | (_, c) :: ρ, e, h => by
      have h' := isShapeHeadA_wk_rev ρ (liftA c 1 e) h
      rw [appsSpineA_liftA] at h'
      exact (isShapeHeadA_liftA E c _).1 h'

theorem neutKA_wk {Γ : LCtxA} {e : ExprA} (ρ : WkSpecA) (hρ : WkSpecA.ok ρ Γ)
    (h : NeutKA E I Γ e) : NeutKA E I (wkCtxA ρ Γ) (wkExprA ρ e) := by
  refine ⟨fun σ hσ xs => ?_, fun hs => h.2.1 (isShapeHeadA_wk_rev ρ e hs),
    fun hc => h.2.2 (ctorHeadA_wk_rev ρ hc)⟩
  have hw := h.1 (WkSpecA.comp ρ σ) (WkSpecA.ok_comp ρ σ Γ hρ hσ) xs
  rw [wkCtxA_comp, wkExprA_comp] at hw
  exact hw

theorem neutKA_app {Γ : LCtxA} {f : ExprA} (a : ExprA) (h : NeutKA E I Γ f) :
    NeutKA E I Γ (.app f a) := by
  refine ⟨fun ρ hρ xs => ?_, h.2.1, fun hc => h.2.2 (ctorHeadA_of_app hc)⟩
  rw [wkExprA_app]
  exact h.1 ρ hρ (wkExprA ρ a :: xs)

end Neut

/-! ## (2) where extended neutrals come from: variables, under `IotaConstHeadA` -/

/-- ι fires only on constant-headed spines. -/
def IotaConstHeadA (I : IotaIfaceA) : Prop :=
  ∀ e : ExprA, (∀ (r : Nat) (ls : List Level), (appsSpineA e).1 ≠ .const r ls) → I.fn e = none

theorem iotaConstHeadA_of_recHead {E : ResolvedEnvA} {I : IotaIfaceA} (h : IotaRecHeadA E I) :
    IotaConstHeadA I := fun e hne => by
  cases hfn : I.fn e with
  | none => rfl
  | some e' =>
      obtain ⟨r, ls, _, hsp, _, _, _⟩ := h e e' hfn
      exact absurd hsp (hne r ls)

section Bvar
variable {E : ResolvedEnvA} {I : IotaIfaceA}

/-- a spine whose head does not step, is not a λ and is not a constant is
    weak-head normal, whatever the arguments: no β, no step in the head, and
    the oracle refuses by `IotaConstHeadA`. -/
theorem hStepFnA_spine_none (hIC : IotaConstHeadA I) {Γ : LCtxA} :
    (xs : List ExprA) → {h : ExprA} → hStepFnA E I.fn Γ h = none →
    (∀ A u b, h ≠ .lam A u b) → (∀ r ls, (appsSpineA h).1 ≠ .const r ls) →
    hStepFnA E I.fn Γ (foldAppsA h xs) = none
  | [], _, hh, _, _ => hh
  | x :: xs, h, hh, hnl, hnc => by
      show hStepFnA E I.fn Γ (foldAppsA (.app h x) xs) = none
      refine hStepFnA_spine_none hIC xs ?_ (fun _ _ _ e => ExprA.noConfusion e) hnc
      exact hStepFnA_app_none E I.fn Γ hnl hh (hIC (.app h x) hnc)
        (recAtMajorA_of_head_not_const E hnc)

theorem wkExprA_bvar : (ρ : WkSpecA) → (i : Nat) → ∃ j, wkExprA ρ (.bvar i) = .bvar j
  | [], i => ⟨i, rfl⟩
  | (_, c) :: ρ, i => by
      show ∃ j, wkExprA ρ (liftA c 1 (.bvar i)) = .bvar j
      rw [liftA_bvar]
      exact wkExprA_bvar ρ _

/-- a variable without a value is an extended neutral. -/
theorem neutKA_bvar (hE : EnvClosedA E) (hI : IotaLiftA I) (hIC : IotaConstHeadA I)
    {Γ : LCtxA} {i : Nat} (hv : lookupValueA Γ i = none) : NeutKA E I Γ (.bvar i) := by
  refine ⟨fun ρ hρ xs => ?_, fun hs => by simp [appsSpineA, isShapeHeadA] at hs,
    fun ⟨_, _, _, hsp, _, _⟩ => ExprA.noConfusion hsp⟩
  obtain ⟨j, hj⟩ := wkExprA_bvar ρ i
  have hn : hStepFnA E I.fn (wkCtxA ρ Γ) (wkExprA ρ (.bvar i)) = none :=
    hStepFnA_wk_none hE hI Γ ρ hρ hv
  rw [hj] at hn ⊢
  exact hStepFnA_spine_none hIC xs hn (fun _ _ _ e => ExprA.noConfusion e)
    (fun _ _ e => ExprA.noConfusion e)

end Bvar

/-! ## (3) reflection -/

section Reflect
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}

/-- the motive: at this type, extended neutrals typed and convertible are related. -/
abbrev ReflMotA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (A : ExprA)
    (R : ExprA → ExprA → Prop) : Prop :=
  ∀ a b : ExprA, NeutKA E I Γ a → NeutKA E I Γ b →
    Nonempty (HasTyA E I n Γ a A) → Nonempty (HasTyA E I n Γ b A) →
    Nonempty (ConvA E I n Γ a b A) → R a b

/-- prop and stuck clauses: the relation IS typed-and-convertible at the normal form. -/
theorem reflMinor_triple {Γ : LCtxA} {A N : ExprA} (hA : WhTyA E I n Γ A N) :
    ReflMotA E I n Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N)) :=
  fun _ _ _ _ hta htb hab => (whTyA_tyConv hA).elim fun cA =>
    ⟨hta.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩, htb.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩,
     hab.elim fun c => ⟨convA_of_tyConvA c cA⟩⟩

/-- Type-sort clause: the neutrals are their own normal forms; `EqKA.stuck`/
    `TyKA.stuck` at the sort's height. -/
theorem reflMinor_sortT {Γ : LCtxA} {A : ExprA} {l : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (_hz : isZero l = false) (hk : ht ρ₀ l < k) :
    ReflMotA E I n Γ A (fun a b =>
      LREqA E I n ρ₀ (ht ρ₀ l) Γ a b ∧
      (∃ R, LRTyA E I n ρ₀ (ht ρ₀ l) Γ a R) ∧
      (∃ R, LRTyA E I n ρ₀ (ht ρ₀ l) Γ b R) ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l))) := by
  intro a b hna hnb hta htb hab
  have _ := hk
  obtain ⟨cA⟩ := whTyA_tyConv hA
  have hta' : Nonempty (HasTyA E I n Γ a (.sort l)) := hta.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have htb' : Nonempty (HasTyA E I n Γ b (.sort l)) := htb.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have hab' : Nonempty (ConvA E I n Γ a b (.sort l)) := hab.elim fun c => ⟨convA_of_tyConvA c cA⟩
  have hsa : WhTyA E I n Γ a a := hta'.elim fun t => whTyA_of_hasTy t
  have hsb : WhTyA E I n Γ b b := htb'.elim fun t => whTyA_of_hasTy t
  refine ⟨?_,
    ⟨fun x y => Nonempty (HasTyA E I n Γ x a) ∧ Nonempty (HasTyA E I n Γ y a) ∧
      Nonempty (ConvA E I n Γ x y a), ?_⟩,
    ⟨fun x y => Nonempty (HasTyA E I n Γ x b) ∧ Nonempty (HasTyA E I n Γ y b) ∧
      Nonempty (ConvA E I n Γ x y b), ?_⟩, hta', htb', hab'⟩
  · rw [LREqA_eq]
    exact .stuck hsa hsb (tripleLikeA_of_stuck (neutKA_stuck hna))
      (tripleLikeA_of_stuck (neutKA_stuck hnb))
      (hta'.elim fun t => htb'.elim fun t' => hab'.elim fun c =>
        ⟨.of Γ a b l l l t (eqNA_refl l) t' (eqNA_refl l) c⟩)
  · rw [LRTyA_eq]
    exact .stuck hsa (neutKA_stuck hna)
  · rw [LRTyA_eq]
    exact .stuck hsb (neutKA_stuck hnb)

/-- `Prop`-sort clause: two neutral propositions are their own triple-like
    normal forms, typed and convertible. -/
theorem reflMinor_sortP {Γ : LCtxA} {A : ExprA} {l : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (_hz : isZero l = true) :
    ReflMotA E I n Γ A (fun a b =>
      PropValidA E I n Γ a ∧ PropValidA E I n Γ b ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA E I n Γ a b) := by
  intro a b hna hnb hta htb hab
  obtain ⟨cA⟩ := whTyA_tyConv hA
  have hta' : Nonempty (HasTyA E I n Γ a (.sort l)) := hta.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have htb' : Nonempty (HasTyA E I n Γ b (.sort l)) := htb.elim fun t => ⟨hasTyA_of_tyConvA t cA⟩
  have hab' : Nonempty (ConvA E I n Γ a b (.sort l)) := hab.elim fun c => ⟨convA_of_tyConvA c cA⟩
  have hsa : WhTyA E I n Γ a a := hta'.elim fun t => whTyA_of_hasTy t
  have hsb : WhTyA E I n Γ b b := htb'.elim fun t => whTyA_of_hasTy t
  exact ⟨⟨a, hsa, tripleLikeA_of_stuck (neutKA_stuck hna)⟩,
    ⟨b, hsb, tripleLikeA_of_stuck (neutKA_stuck hnb)⟩, hta', htb', hab',
    propEqA_stuck_refl hta' htb' (neutKA_stuck hna) (neutKA_stuck hnb) hab'⟩

/-- pi clause: under a world and applied to related arguments the two sides are
    again extended neutrals, typed by `HasTyA.app` from the clause's data and
    convertible by `ConvA.app`; the codomain's reflection closes it. -/
theorem reflMinor_pi (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A D C : ExprA}
    {u v : Level} (hA : WhTyA E I n Γ A (.pi D u C v))
    (_hnp : ¬ IsPropTy E I Γ (.pi D u C v))
    (_hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j)
        (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
    (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      TyKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j) (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j) (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C)))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ),
      ReflMotA E I n (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      ReflMotA E I n (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (_ihCeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'), True) :
    ReflMotA E I n Γ A (fun f g =>
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      Nonempty (HasTyA E I n Γ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Γ g (.pi D u C v)) ∧
      Nonempty (ConvA E I n Γ f g (.pi D u C v))) := by
  intro f g hnf hng htf htg hfg
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
  obtain ⟨w, hTy⟩ := tyKA_hasTy (hC ρ hρ a a' hr)
  have heq := hCeq ρ hρ a a' hr
  obtain ⟨w', hTy'⟩ := eqKA_hasTy_right heq
  have hargs := escapeA_hasTy (hD ρ hρ) hr
  have caa := escapeA (hD ρ hρ) hr
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
    (eqKA_tyConv heq).elim fun tc => htb0.elim fun t => ⟨hasTyA_of_tyConvA t tc.symm⟩
  have capp : Nonempty (ConvA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))) :=
    hcw.elim fun cw => caa.elim fun c => hCw.elim fun hB => htb.elim fun t =>
      ⟨.app _ _ _ _ _ _ _ u v cw c hB t⟩
  exact ihC ρ hρ a a' hr _ _ (neutKA_app a (neutKA_wk ρ hρ.1 hnf))
    (neutKA_app a' (neutKA_wk ρ hρ.1 hng)) hta htb capp

/-- fam clause: two extended neutrals are stuck terms reducing to themselves, so the
    fixed point's stuck disjunct relates them (one folding). -/
theorem reflMinor_fam {Γ : LCtxA} {A C : ExprA} {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI : InnerRelsA} (hA : WhTyA E I n Γ A C) :
    ReflMotA E I n Γ A (fun a b => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) [] C a b) :=
  fun a b hna hnb hta htb hab => (whTyA_tyConv hA).elim fun cA =>
    LfpWA.fold famPhiWA_mono ⟨hab.elim fun c => ⟨convA_of_tyConvA c cA⟩,
      Or.inr ⟨a, b, hta.elim fun t => tyHRedStarA_refl (hasTyA_of_tyConvA t cA),
        htb.elim fun t => tyHRedStarA_refl (hasTyA_of_tyConvA t cA),
        neutKA_stuckTm hna, neutKA_stuckTm hnb⟩⟩

/-- **extended neutrals typed at a valid type and convertible are related.**
    Stated at the tied lower heights, because the sort clause builds the
    lower-height relation. -/
theorem reflectA (hE : EnvClosedA E) (hI : IotaLiftA I) :
    {Γ : LCtxA} → {A : ExprA} → {R : ExprA → ExprA → Prop} →
    TyKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j) Γ A R →
    ∀ {a b : ExprA}, NeutKA E I Γ a → NeutKA E I Γ b →
      Nonempty (HasTyA E I n Γ a A) → Nonempty (HasTyA E I n Γ b A) →
      Nonempty (ConvA E I n Γ a b A) → R a b :=
  fun {_Γ _A _R} h {a b} hna hnb hta htb hab =>
  TyKA.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ A R _ => ReflMotA E I n Γ A R)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro)
    (fun hA _ _ => reflMinor_triple hA)
    (fun hA hz hk => reflMinor_sortT hA hz hk)
    (fun hA hz => reflMinor_sortP hA hz)
    (fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq =>
      reflMinor_pi hE hI hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq)
    (fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => reflMinor_fam hA)
    (fun hA _ => reflMinor_triple hA)
    h a b hna hnb hta htb hab

/-- the knotted form. -/
theorem LRRelA_reflect (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A a b : ExprA}
    (hA : ∃ R, LRTyA E I n ρ₀ k Γ A R) (hna : NeutKA E I Γ a) (hnb : NeutKA E I Γ b)
    (hta : Nonempty (HasTyA E I n Γ a A)) (htb : Nonempty (HasTyA E I n Γ b A))
    (hab : Nonempty (ConvA E I n Γ a b A)) : LRRelA E I n ρ₀ k Γ A a b := by
  obtain ⟨R, hR⟩ := hA
  refine ⟨R, hR, ?_⟩
  rw [LRTyA_eq] at hR
  exact reflectA hE hI hR hna hnb hta htb hab

/-- the fundamental theorem's variable arm: a typed variable without a value is
    related to itself at its (valid) type. -/
theorem LRRelA_bvar (hE : EnvClosedA E) (hI : IotaLiftA I) (hIC : IotaConstHeadA I)
    {Γ : LCtxA} {A : ExprA} {i : Nat} (hv : lookupValueA Γ i = none)
    (hA : ∃ R, LRTyA E I n ρ₀ k Γ A R) (ht : Nonempty (HasTyA E I n Γ (.bvar i) A)) :
    LRRelA E I n ρ₀ k Γ A (.bvar i) (.bvar i) :=
  LRRelA_reflect hE hI hA (neutKA_bvar hE hI hIC hv) (neutKA_bvar hE hI hIC hv) ht ht
    (ht.elim fun t => ⟨.refl Γ _ A t⟩)

end Reflect

#print axioms neutKA_wk
#print axioms neutKA_bvar
#print axioms reflectA
#print axioms LRRelA_reflect
#print axioms LRRelA_bvar

end Rcic.Declarative.Ann
