import rcic.RcicAnnLRChain

/-!
# DT-025 / A-6 S1-g.1 (ruling R-A6-S1g) — the Prop key agrees with the declared sort

`IsPropTy` (`RcicAnnAlg.lean:272`) keys the `prop` clause on the INFERRED sort
(`inferSortA`, `∃ fuel`). R-A6-S1f's in-place guard measured that a guarded stuck
clause needs, at triple-like normal forms, the agreement of that key with the
DECLARED sort (#6262: 13 uses, K1/K2/K3). Under R-A6-S1g (route (a), two-pass) the
agreement is proved HERE, once, as ordinary theorems about typing, from pass 1 —
main's `fundA` through its corollaries `fund_tyConvA`, `eqKA_pi_inv`,
`tyConvA_pi_inj`, `codom_typeLevel`, `sortUniqA` (`RcicAnnSortUniq`, `RcicAnnLRRows`).
Nothing here is consumed by, or changes, the relation.

The route is the SPINE WALK of `spine_tyConv` (`RcicAnnSortUniq.lean:435`), run
against `inferA`: a normal type is a spine whose head is a variable, a constant, a
sort or a pi (a λ alone is no type, a let and a literal step). Along a spine typed at
a LARGE type every pi met is Type-level (`codom_typeLevel`), so the synthesized head
type's normal form IS a pi (the relation's type equality at a Type-level pi is
`EqKA.pi`, no other clause reaches it) and `tyConvA_pi_inj` moves the instance across.
At the end the synthesized type converts to the declared sort, whose normal form is a
sort `=ₙ` to it (`EqKA.sort`). So `inferSortA` is complete and sound at normal types
(`inferSortA_of_normal`), and:

* K1 — a declared-Prop type's normal form is `IsPropTy` (`propKey_K1`);
* K2 — a declared non-Prop type's normal form is not (`propKey_K2`);
* K3 — `IsPropTy` is invariant along `TyConvA` between normal forms (`propKey_K3`),
  through the zero-ness of the declared sort moving along the conversion
  (`tyConvA_sort_zero`, by `sortUniqA` at every node).

No countermodel at a neutral spine: K1/K2 hold at EVERY normal type, neutral spines
included, on the six environment hypotheses and a well-formed context.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section PropKey
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-! ## (1) the normal form of a type convertible to a Type-level pi / to a sort -/

/-- a type convertible to a Type-level pi computes (`whnfA`) to a pi it converts to. -/
theorem redTo_pi_of_tyConv (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {T A B : ExprA} {u v : Level} (hz : isZero v = false)
    (h : TyConvA E I n Γ T (.pi A u B v)) :
    ∃ A' u' B' v', RedTo E I Γ T (.pi A' u' B' v') ∧
      Nonempty (TyConvA E I n Γ T (.pi A' u' B' v')) := by
  rcases fund_tyConvA hE hI hIS hEN hNC hR hS hρ hΓ h with e | ⟨k₀, hk⟩
  · subst e
    exact ⟨A, u, B, v, ⟨0, whnfA_of_normal E I.fn Γ 0 _ (hStepFnA_pi _ _ _ _ _ _ _)⟩, ⟨.refl _ _⟩⟩
  · have hEq := hk k₀ (Nat.le_refl _)
    rw [LREqA_eq] at hEq
    cases hEq with
    | sort _ hB _ _ _ =>
        exact absurd (whTyA_det hB (whTyA_self hB) (hStepFnA_sort E I.fn Γ _)
          (hStepFnA_pi E I.fn Γ A u B v)) (fun e => ExprA.noConfusion e)
    | pi hA _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact ⟨_, _, _, _, whTyA_redTo hA (hStepFnA_pi _ _ _ _ _ _ _), whTyA_tyConv hA⟩
    | fam _ hB _ hnB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact absurd (whTyA_det hB (whTyA_self hB) hnB (hStepFnA_pi E I.fn Γ A u B v))
          (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
    | stuck _ hB _ hN' _ =>
        have e := whTyA_det hB (whTyA_self hB) hN'.1 (hStepFnA_pi E I.fn Γ A u B v)
        subst e
        have hP0 := (isPropTy_pi_iff E I Γ _ _ _ _).1 (tripleLikeA_pi_isProp hN')
        rw [hz] at hP0
        cases hP0

/-- a type convertible to a sort computes (`whnfA`) to a sort `=ₙ` to it. -/
theorem redTo_sort_of_tyConv (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {T : ExprA} {a : Level} (h : TyConvA E I n Γ T (.sort a)) :
    ∃ l, RedTo E I Γ T (.sort l) ∧ eqN l a := by
  rcases fund_tyConvA hE hI hIS hEN hNC hR hS hρ hΓ h with e | ⟨k₀, hk⟩
  · subst e
    exact ⟨a, ⟨0, whnfA_of_normal E I.fn Γ 0 _ (hStepFnA_sort _ _ _ _)⟩, eqNA_refl a⟩
  · have hEq := hk k₀ (Nat.le_refl _)
    rw [LREqA_eq] at hEq
    cases hEq with
    | sort hA hB _ hl _ =>
        have e := whTyA_det hB (whTyA_self hB) (hStepFnA_sort E I.fn Γ _) (hStepFnA_sort E I.fn Γ a)
        injection e with e
        subst e
        exact ⟨_, whTyA_redTo hA (hStepFnA_sort _ _ _ _), hl⟩
    | pi _ hB _ _ _ _ _ _ _ _ _ _ _ =>
        exact absurd (whTyA_det hB (whTyA_self hB) (hStepFnA_pi E I.fn Γ _ _ _ _)
          (hStepFnA_sort E I.fn Γ a)) (fun e => ExprA.noConfusion e)
    | fam _ hB _ hnB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact absurd (whTyA_det hB (whTyA_self hB) hnB (hStepFnA_sort E I.fn Γ a))
          (foldAppsA_const_ne_sort _ _ _ _)
    | stuck _ hB _ hN' _ =>
        have e := whTyA_det hB (whTyA_self hB) hN'.1 (hStepFnA_sort E I.fn Γ a)
        subst e
        exact (tripleLikeA_not_sort hN').elim

/-! ## (2) synthesis along a spine, at a large type -/

/-- a head whose synthesized type converts to every type it is given. -/
def HeadInferA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (h : ExprA) : Prop :=
  ∀ T, HasTyA E I n Γ h T →
    ∃ fuel T', inferA E I.fn fuel Γ h = some T' ∧ Nonempty (TyConvA E I n Γ T' T)

theorem headInferA_bvar (Γ : LCtxA) (i : Nat) : HeadInferA E I n Γ (.bvar i) := fun T hT => by
  obtain ⟨A, hA, ht⟩ := hasTyA_bvar_gen hT
  exact ⟨1, A, by simp only [inferA]; exact hA, ht⟩

theorem headInferA_const (Γ : LCtxA) (r : Nat) (ls : List Level) :
    HeadInferA E I n Γ (.const r ls) := fun T hT => by
  obtain ⟨m, hres, hlen, _, ht⟩ := hasTyA_const_full hT
  exact ⟨1, instantiateLevelsA ls m.mtypeA, by simp [inferA, hres, hlen], ht⟩

theorem headInferA_sort (Γ : LCtxA) (l : Level) : HeadInferA E I n Γ (.sort l) := fun _ hT =>
  ⟨1, .sort (.succ l), rfl, ⟨hasTyA_sort_gen hT⟩⟩

theorem headInferA_pi (Γ : LCtxA) (D : ExprA) (u : Level) (C : ExprA) (v : Level) :
    HeadInferA E I n Γ (.pi D u C v) := fun _ hT =>
  ⟨1, .sort (.imax u v), rfl, ⟨hasTyA_pi_sort hT⟩⟩

/-- THE SYNTHESIS WALK: along a spine with a synthesizing head, typed at a large type, `inferA`
    succeeds and its answer converts to the type. Every pi met is Type-level (`codom_typeLevel`),
    so the synthesized function type computes to a pi (`redTo_pi_of_tyConv`) and pi
    injectivity moves the argument's instance across. -/
theorem inferA_spine (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {h : ExprA} (hh : HeadInferA E I n Γ h) (xs : List ExprA) :
    ∀ {T : ExprA}, HasTyA E I n Γ (foldAppsA h xs) T → LargeA E I n Γ T →
      ∃ fuel T', inferA E I.fn fuel Γ (foldAppsA h xs) = some T' ∧
        Nonempty (TyConvA E I n Γ T' T) := by
  refine snocInduction (P := fun xs => ∀ {T : ExprA}, HasTyA E I n Γ (foldAppsA h xs) T →
      LargeA E I n Γ T → ∃ fuel T', inferA E I.fn fuel Γ (foldAppsA h xs) = some T' ∧
        Nonempty (TyConvA E I n Γ T' T)) (fun hT _ => hh _ hT) ?_ xs
  intro ys x ih T hT hL
  rw [foldAppsA_append] at hT ⊢
  simp only [foldAppsA] at hT ⊢
  obtain ⟨A, u, B, v, _, ⟨hf⟩, ⟨hx⟩, ⟨hB⟩, _, ⟨t⟩⟩ := hasTyA_app_gen hT
  have hz := codom_typeLevel hE hI hIS hEN hNC hR hS hρ hΓ hB hx ⟨t⟩ hL
  obtain ⟨f₁, TF, hinf, ⟨tF⟩⟩ := ih hf (Or.inr ⟨A, u, B, v, hz, ⟨.refl _ _⟩⟩)
  obtain ⟨A', u', B', v', ⟨f₂, hwh⟩, ⟨tP⟩⟩ := redTo_pi_of_tyConv hE hI hIS hEN hNC hR hS hρ hΓ hz tF
  obtain ⟨_, hcod⟩ := tyConvA_pi_inj hE hI hIS hEN hNC hR hS hρ hΓ hz (.trans _ _ _ _ tF.symm tP)
  obtain ⟨tc⟩ := hcod x hx
  refine ⟨max f₁ f₂ + 1, instantiate0A x B', ?_, ⟨.trans _ _ _ _ tc.symm t⟩⟩
  have h1 := inferA_mono_le E I.fn f₁ (max f₁ f₂) (Nat.le_max_left _ _) Γ _ _ hinf
  have h2 := whnfA_mono_le E I.fn Γ f₂ (max f₁ f₂) (Nat.le_max_right _ _) _ _ hwh
  simp only [inferA, h1, h2]

/-! ## (3) `inferSortA` is complete and sound at normal types -/

/-- **SYNTHESIS AT A NORMAL TYPE**: a normal type typed at `sort u` has a synthesized sort, and
    it is `=ₙ` to `u`. The head of its spine is a variable, a constant, a sort or a pi (as in
    `sortUniqA_normal`); the walk synthesizes a type converting to `sort u`, which computes
    to a sort `=ₙ` to `u`. -/
theorem inferSortA_of_normal (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {X : ExprA} {u : Level} (hX : HasTyA E I n Γ X (.sort u))
    (hn : hStepFnA E I.fn Γ X = none) :
    ∃ fuel l, inferSortA E I.fn fuel Γ X = some l ∧ eqN l u := by
  have hsp := foldAppsA_appsSpineA X
  have hna := appsSpineA_fst_not_app X
  rw [← hsp] at hX hn ⊢
  generalize (appsSpineA X).1 = H at hX hn hna ⊢
  generalize (appsSpineA X).2 = xs at hX hn ⊢
  have walk : HeadInferA E I n Γ H →
      ∃ fuel l, inferSortA E I.fn fuel Γ (foldAppsA H xs) = some l ∧ eqN l u := fun hh => by
    obtain ⟨f₁, T', hinf, ⟨t⟩⟩ := inferA_spine hE hI hIS hEN hNC hR hS hρ hΓ hh xs hX
      (Or.inl ⟨u, ⟨.refl _ _⟩⟩)
    obtain ⟨l, ⟨f₂, hwh⟩, hl⟩ := redTo_sort_of_tyConv hE hI hIS hEN hNC hR hS hρ hΓ t
    refine ⟨max f₁ f₂, l, ?_, hl⟩
    have h1 := inferA_mono_le E I.fn f₁ (max f₁ f₂) (Nat.le_max_left _ _) Γ _ _ hinf
    have h2 := whnfA_mono_le E I.fn Γ f₂ (max f₁ f₂) (Nat.le_max_right _ _) _ _ hwh
    simp only [inferSortA, h1, h2]
  have hshape := hStepFnA_foldApps_none E I.fn Γ H xs hn
  cases H with
  | bvar i => exact walk (headInferA_bvar Γ i)
  | sort l => exact walk (headInferA_sort Γ l)
  | const r ls => exact walk (headInferA_const Γ r ls)
  | pi D u' C v' => exact walk (headInferA_pi Γ D u' C v')
  | app f x => exact absurd rfl (hna f x)
  | lam A u' body =>
      rcases hshape with e | ⟨_, hnl⟩
      · subst e
        simp only [foldAppsA] at hX
        obtain ⟨_, _, _, _, _, ⟨t⟩⟩ := hasTyA_lam_gen hX
        exact (tyConvA_pi_sort_false hE hI hIS hEN hNC hR hS hρ hΓ t).elim
      · exact absurd rfl (hnl A u' body)
  | letE A v body =>
      rcases hshape with e | ⟨hhn, _⟩
      · subst e
        simp [foldAppsA, hStepFnA] at hn
      · simp [hStepFnA] at hhn
  | lit t =>
      rcases hshape with e | ⟨hhn, _⟩
      · subst e
        simp [foldAppsA, hStepFnA] at hn
      · simp [hStepFnA] at hhn

/-- **the Prop key at a normal type IS the zero-ness of its declared sort.** -/
theorem isPropTy_iff_of_normal (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {X : ExprA} {u : Level} (hX : HasTyA E I n Γ X (.sort u))
    (hn : hStepFnA E I.fn Γ X = none) : IsPropTy E I Γ X ↔ isZero u = true := by
  obtain ⟨f, l, hl, he⟩ := inferSortA_of_normal hE hI hIS hEN hNC hR hS hρ hΓ hX hn
  constructor
  · rintro ⟨f', l', hl', hz⟩
    have e := inferSortA_det E I.fn hl hl'
    subst e
    rw [← isZero_eqN he]
    exact hz
  · intro hz
    exact ⟨f, l, hl, by rw [isZero_eqN he]; exact hz⟩

/-! ## (4) K1, K2, K3 — at the normal form of a declared type -/

/-- **K1**: the normal form of a type declared at a `Prop`-level sort is a proposition for the
    key. -/
theorem propKey_K1 (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {X N : ExprA} {u : Level} (hX : HasTyA E I n Γ X (.sort u))
    (hz : isZero u = true) (hN : WhTyA E I n Γ X N) (hn : hStepFnA E I.fn Γ N = none) :
    IsPropTy E I Γ N := by
  obtain ⟨c⟩ := hN
  obtain ⟨hNu⟩ := whTyChainA_sort_end hE hI hIS hEN hNC hR hS hρ hΓ c ⟨hX⟩
  exact (isPropTy_iff_of_normal hE hI hIS hEN hNC hR hS hρ hΓ hNu hn).2 hz

/-- **K1 at a well-formed environment** — W2k DISCHARGED (R-NoDeltaRec-4d-iii, PR #6263):
    `propKey_K1`'s premise list minus `hEN`/`hNC`, which `envWfA_normCtorType`/`envWfA_normClosed`
    supply from any `EnvWfA` of the environment. -/
theorem propKey_K1_wf {J : IotaIfaceA} (hW : EnvWfA J E) (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {X N : ExprA} {u : Level} (hX : HasTyA E I n Γ X (.sort u))
    (hz : isZero u = true) (hN : WhTyA E I n Γ X N) (hn : hStepFnA E I.fn Γ N = none) :
    IsPropTy E I Γ N :=
  propKey_K1 hE hI hIS (envWfA_normCtorType hW) (envWfA_normClosed hW) hR hS hρ hΓ hX hz hN hn

/-- **K2**: the normal form of a type declared at a non-`Prop` sort is not a proposition for the
    key. -/
theorem propKey_K2 (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {X N : ExprA} {u : Level} (hX : HasTyA E I n Γ X (.sort u))
    (hz : isZero u = false) (hN : WhTyA E I n Γ X N) (hn : hStepFnA E I.fn Γ N = none) :
    ¬ IsPropTy E I Γ N := fun hP => by
  obtain ⟨c⟩ := hN
  obtain ⟨hNu⟩ := whTyChainA_sort_end hE hI hIS hEN hNC hR hS hρ hΓ c ⟨hX⟩
  have := (isPropTy_iff_of_normal hE hI hIS hEN hNC hR hS hρ hΓ hNu hn).1 hP
  rw [hz] at this
  cases this

/-- the zero-ness of a declared sort moves along a type conversion (sort uniqueness at every
    node of the chain). -/
theorem tyConvA_sort_zero (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) : {A B : ExprA} → TyConvA E I n Γ A B → ∀ {a : Level},
      HasTyA E I n Γ A (.sort a) → ∃ b, Nonempty (HasTyA E I n Γ B (.sort b)) ∧ isZero b = isZero a
  | _, _, .refl _ _, a, ha => ⟨a, ⟨ha⟩, rfl⟩
  | _, _, .of _ _ _ _ _ _ hAl hlw hBl hl'w _, _, ha =>
      ⟨_, ⟨hBl⟩, by
        rw [isZero_eqN hl'w, ← isZero_eqN hlw, ← isZero_eqN (sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ ha hAl)]⟩
  | _, _, .trans _ _ _ _ h1 h2, _, ha => by
      obtain ⟨m, ⟨hm⟩, e1⟩ := tyConvA_sort_zero hE hI hIS hEN hNC hR hS hρ hΓ h1 ha
      obtain ⟨b, hb, e2⟩ := tyConvA_sort_zero hE hI hIS hEN hNC hR hS hρ hΓ h2 hm
      exact ⟨b, hb, e2.trans e1⟩

/-- **K3**: the key is invariant along a type conversion between normal forms of types. -/
theorem propKey_K3 (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {A B N N' : ExprA} (hc : Nonempty (TyConvA E I n Γ A B))
    (hA : WhTyA E I n Γ A N) (hB : WhTyA E I n Γ B N')
    (hn : hStepFnA E I.fn Γ N = none) (hn' : hStepFnA E I.fn Γ N' = none) :
    IsPropTy E I Γ N ↔ IsPropTy E I Γ N' := by
  obtain ⟨a, ⟨ha⟩⟩ := whTyA_hasTy_head hA
  obtain ⟨b', ⟨hb'⟩⟩ := whTyA_hasTy_head hB
  obtain ⟨t⟩ := hc
  obtain ⟨b, ⟨hb⟩, e⟩ := tyConvA_sort_zero hE hI hIS hEN hNC hR hS hρ hΓ t ha
  have ebb := isZero_eqN (sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ hb hb')
  obtain ⟨cA⟩ := hA
  obtain ⟨cB⟩ := hB
  obtain ⟨hNa⟩ := whTyChainA_sort_end hE hI hIS hEN hNC hR hS hρ hΓ cA ⟨ha⟩
  obtain ⟨hNb⟩ := whTyChainA_sort_end hE hI hIS hEN hNC hR hS hρ hΓ cB ⟨hb'⟩
  rw [isPropTy_iff_of_normal hE hI hIS hEN hNC hR hS hρ hΓ hNa hn,
    isPropTy_iff_of_normal hE hI hIS hEN hNC hR hS hρ hΓ hNb hn', ← ebb, e]


/-- **S1-c's wall 1 falls**: `hfamkey` — the premise `lrRelA_chain_env` / `tyKA_chain_sub` /
    `hkey_of_sortTy` carry for the family-application face of the key, measured absent in S1-c
    (`RcicAnnLRChain.lean` module header, wall 1) — is K2 at that face, discharged in exactly the
    premise's shape. -/
theorem hfamkey_of_propKey (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) :
    ∀ {Γ' : LCtxA} {X' N' : ExprA} {v' : Level} {r : Nat} {ls : List Level}
      {xs : List ExprA} {m : CheckedMemberA}, CtxWfA E I n Γ' →
      HasTyA E I n Γ' X' (.sort v') → isZero v' = false → WhTyA E I n Γ' X' N' →
      hStepFnA E I.fn Γ' N' = none → N' = foldAppsA (.const r ls) xs →
      E.members r = some m → m.mclass = .inductiveM → ¬ IsPropTy E I Γ' N' :=
  fun hΓ hX hz hN hn _ _ _ => propKey_K2 hE hI hIS hEN hNC hR hS hρ hΓ hX hz hN hn

/-! ## (5) the pins — K1 and K2 at a NEUTRAL SPINE, against a second instrument

At the empty environment with no ι (all six hypotheses discharged by the stack's own
lemmas), in `Γ = [x : Sort 1, F : Π (_ : Sort 1), S]`, the neutral spine `F x` is typed
at `S`. With `S := Sort 0` K1 makes it a proposition for the key; with `S := Sort 1` K2
makes it not one. Each is checked a second time by evaluating `inferSortA` itself
(`decide`) — the theorem and the function must agree. -/

/-- the pin context: `x : Sort 1` innermost, `F : Π (_ : Sort 1), Sort s` outside it. -/
def pinKeyCtxA (s : Level) : LCtxA :=
  [.assumption (.sort (.succ .zero)), .assumption (.pi (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort s) (.succ s))]

/-- the neutral spine `F x`. -/
def pinKeySpineA : ExprA := .app (.bvar 1) (.bvar 0)

def pinKeyCtxA_wf (s : Level) : CtxWfA emptyEnvA noIotaA 0 (pinKeyCtxA s) :=
  .assumption (.assumption .nil (.pi [] _ _ _ _ (.sort [] _) (.sort _ _))) (.sort _ _)

def pinKeySpineA_ty (s : Level) :
    HasTyA emptyEnvA noIotaA 0 (pinKeyCtxA s) pinKeySpineA (instantiate0A (.bvar 0) (.sort s)) :=
  .app _ (.bvar 1) (.bvar 0) (.sort (.succ .zero)) (.sort s) (.succ (.succ .zero)) (.succ s) (.succ s)
    (.sort _ s) (.sort _ s)
    (.bvar _ 1 _ (.imax (.succ (.succ .zero)) (.succ s)) rfl (.pi _ _ _ _ _ (.sort _ _) (.sort _ _)))
    (.bvar _ 0 _ (.succ (.succ .zero)) rfl (.sort _ _))

theorem pinKeySpineA_normal (s : Level) :
    hStepFnA emptyEnvA noIotaA.fn (pinKeyCtxA s) pinKeySpineA = none := rfl

/-- **K1 at a neutral spine**: `F x : Sort 0` is a proposition for the key. -/
theorem pin_propKey_K1 : IsPropTy emptyEnvA noIotaA (pinKeyCtxA .zero) pinKeySpineA :=
  propKey_K1 emptyEnvA_closed noIotaA_lift noIotaA_subst (fun _ _ h => Option.noConfusion h)
    (fun _ _ h => Option.noConfusion h) (noIotaA_recHead _)
    (emptyEnvA_sem noIotaA 0 (fun _ => 1)) posValA_one (pinKeyCtxA_wf .zero)
    (pinKeySpineA_ty .zero) rfl (whTyA_of_hasTy (pinKeySpineA_ty .zero)) (pinKeySpineA_normal .zero)

/-- **K2 at a neutral spine**: `F x : Sort 1` is not a proposition for the key. -/
theorem pin_propKey_K2 : ¬ IsPropTy emptyEnvA noIotaA (pinKeyCtxA (.succ .zero)) pinKeySpineA :=
  propKey_K2 emptyEnvA_closed noIotaA_lift noIotaA_subst (fun _ _ h => Option.noConfusion h)
    (fun _ _ h => Option.noConfusion h) (noIotaA_recHead _)
    (emptyEnvA_sem noIotaA 0 (fun _ => 1)) posValA_one (pinKeyCtxA_wf (.succ .zero))
    (pinKeySpineA_ty (.succ .zero)) rfl (whTyA_of_hasTy (pinKeySpineA_ty (.succ .zero)))
    (pinKeySpineA_normal (.succ .zero))

/-- the second instrument: `inferSortA` evaluated at the two pins agrees with K1/K2. -/
example : inferSortA emptyEnvA noIotaA.fn 3 (pinKeyCtxA .zero) pinKeySpineA = some .zero := by decide
example : inferSortA emptyEnvA noIotaA.fn 3 (pinKeyCtxA (.succ .zero)) pinKeySpineA =
    some (.succ .zero) := by decide

end PropKey

#print axioms redTo_pi_of_tyConv
#print axioms redTo_sort_of_tyConv
#print axioms headInferA_bvar
#print axioms headInferA_const
#print axioms headInferA_sort
#print axioms headInferA_pi
#print axioms inferA_spine
#print axioms inferSortA_of_normal
#print axioms isPropTy_iff_of_normal
#print axioms propKey_K1
#print axioms propKey_K1_wf
#print axioms propKey_K2
#print axioms tyConvA_sort_zero
#print axioms propKey_K3
#print axioms hfamkey_of_propKey
#print axioms pinKeyCtxA_wf
#print axioms pin_propKey_K1
#print axioms pin_propKey_K2

end Rcic.Declarative.Ann
