import rcic.RcicAnnSortUniq

/-!
# M3-c0 — annotation coherence on the copy

The landing (M3) lifts `main`'s derivations to the copy. Each premise's lift picks its own
annotations for the terms the premise mentions, so two lifts of one `main` term can differ at the
`lam` / `pi` annotations. This module shows that such differences never matter: two well-typed
annotated terms with one erasure are convertible at the first one's type (`annCohA`), and their
types are convertible (`annTyA`). An annotation is a domain's or a codomain's sort, so sort
uniqueness (M3-a) identifies any two of them.

The proof recurses on the first term, and generates the second at the same head (erasure fixes
its shape: `erase_eq_*`).

* An application: the function and the argument by recursion. The right side is typed at the
  left's codomain through functionality (`hasTyA_func0`).
* A λ or a pi: the domain by recursion, its sorts `=ₙ` by sort uniqueness, the body under the left
  domain after context conversion, the codomain sorts `=ₙ` by type uniqueness, collapse and sort
  uniqueness, then congruence.
* A let: the type and the value by recursion, the body under the left binder after context
  conversion. The right side is typed at the left body's type through functionality at a let
  binder whose value is replaced by a convertible one (`convSubstA_cons_let`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) erasure inverted at each constructor -/

theorem erase_eq_bvar {e : ExprA} {i : Nat} (h : erase e = .bvar i) : e = .bvar i := by
  cases e <;> simp [erase] at h
  subst h; rfl

theorem erase_eq_sort {e : ExprA} {l : Level} (h : erase e = .sort l) : e = .sort l := by
  cases e <;> simp [erase] at h
  subst h; rfl

/-! (`erase_eq_const` lives in `RcicAnnLRConv` (2b), where the inner telescopes' rigidity needs it.) -/

theorem erase_eq_lit {e : ExprA} {t : Nat} (h : erase e = .lit t) : e = .lit t := by
  cases e <;> simp [erase] at h
  subst h; rfl

theorem erase_eq_app {e : ExprA} {f a : Expr Nat} (h : erase e = .app f a) :
    ∃ f' a', e = .app f' a' ∧ erase f' = f ∧ erase a' = a := by
  cases e <;> simp [erase] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem erase_eq_lam {e : ExprA} {A b : Expr Nat} (h : erase e = .lam A b) :
    ∃ A' u b', e = .lam A' u b' ∧ erase A' = A ∧ erase b' = b := by
  cases e <;> simp [erase] at h
  exact ⟨_, _, _, rfl, h.1, h.2⟩

theorem erase_eq_pi {e : ExprA} {A B : Expr Nat} (h : erase e = .pi A B) :
    ∃ A' u B' v, e = .pi A' u B' v ∧ erase A' = A ∧ erase B' = B := by
  cases e <;> simp [erase] at h
  exact ⟨_, _, _, _, rfl, h.1, h.2⟩

theorem erase_eq_letE {e : ExprA} {A v b : Expr Nat} (h : erase e = .letE A v b) :
    ∃ A' v' b', e = .letE A' v' b' ∧ erase A' = A ∧ erase v' = v ∧ erase b' = b := by
  cases e <;> simp [erase] at h
  exact ⟨_, _, _, rfl, h.1, h.2.1, h.2.2⟩

/-! ## (2) retyping, and a let binder's value replaced by a convertible one -/

section Tools
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a conversion of types at a sort, as a type conversion. -/
def tyConvA_ofConv (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A B : ExprA} {l : Level}
    (h : ConvA E I n Γ A B (.sort l)) : TyConvA E I n Γ A B :=
  .of Γ A B l l l (convA_hasTy_left hE hI hR hIS hΓ h) (eqNA_refl l)
    (convA_hasTy_right hE hI hR hIS hΓ h) (eqNA_refl l) h

/-- `0 ↦ t` over a let binder `A := v`, `t` of type `A` convertible to `v`; the identity on the
    tail. -/
def substTyA_cons_let_conv (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {v t A : ExprA}
    (hΓ : CtxWfA E I n Γ) (ht : HasTyA E I n Γ t A) (hc : ConvA E I n Γ t v A) :
    SubstTyA E I n Γ (SubstA.cons t SubstA.id) (.letBinding A v :: Γ) where
  ty := fun i B hlu => by
    cases i with
    | zero =>
        have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq hlu
        subst hB
        rw [SubstA.cons_zero, substA_cons_id_lift]
        exact ht
    | succ i =>
        let s := liftedTypeA (.letBinding A v) Γ hlu
        have hEq : B = liftA 0 1 s.orig := s.eq_lift
        rw [hEq]
        rw [SubstA.cons_succ, substA_cons_id_lift]
        have hty := (substTyA_id hE hI hΓ).ty i s.orig s.got
        rw [SubstA.id_apply, substA_id] at hty
        exact hty
  val := fun i B w hty hval => by
    cases i with
    | zero =>
        have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq hty
        have hw : w = liftA 0 1 v := lookupValueA_zero_let_eq hval
        subst hB; subst hw
        rw [SubstA.cons_zero, substA_cons_id_lift, substA_cons_id_lift]
        exact hc
    | succ i =>
        let sB := liftedTypeA (.letBinding A v) Γ hty
        let sv := liftedValueA (.letBinding A v) Γ hval
        have hB : B = liftA 0 1 sB.orig := sB.eq_lift
        have hw : w = liftA 0 1 sv.orig := sv.eq_lift
        rw [hB, hw]
        rw [SubstA.cons_succ, substA_cons_id_lift, substA_cons_id_lift]
        have hc' := (substTyA_id hE hI hΓ).val i sB.orig sv.orig sB.got sv.got
        rw [SubstA.id_apply, substA_id, substA_id] at hc'
        exact hc'

/-- two such substitutions over a let binder, their values convertible. -/
def convSubstA_cons_let (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {v t t' A : ExprA}
    (hΓ : CtxWfA E I n Γ) (ht : HasTyA E I n Γ t A) (hct : ConvA E I n Γ t v A)
    (ht' : HasTyA E I n Γ t' A) (hct' : ConvA E I n Γ t' v A) (hc : ConvA E I n Γ t t' A) :
    ConvSubstA E I n Γ (SubstA.cons t SubstA.id) (SubstA.cons t' SubstA.id)
      (.letBinding A v :: Γ) where
  left := substTyA_cons_let_conv hE hI hΓ ht hct
  right := substTyA_cons_let_conv hE hI hΓ ht' hct'
  conv := fun i B hlu => by
    cases i with
    | zero =>
        have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq hlu
        subst hB
        rw [SubstA.cons_zero, SubstA.cons_zero, substA_cons_id_lift]
        exact hc
    | succ i =>
        let s := liftedTypeA (.letBinding A v) Γ hlu
        have hEq : B = liftA 0 1 s.orig := s.eq_lift
        rw [hEq]
        rw [SubstA.cons_succ, SubstA.cons_succ, substA_cons_id_lift]
        have hty := (substTyA_id hE hI hΓ).ty i s.orig s.got
        rw [SubstA.id_apply, substA_id] at hty
        exact .refl _ _ _ hty

/-- functionality at a let binder: the body's type instantiated at convertible values. -/
def convA_inst0Let_func (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A v t t' e T : ExprA}
    (he : HasTyA E I n (.letBinding A v :: Γ) e T)
    (ht : HasTyA E I n Γ t A) (hct : ConvA E I n Γ t v A)
    (ht' : HasTyA E I n Γ t' A) (hct' : ConvA E I n Γ t' v A) (hc : ConvA E I n Γ t t' A) :
    ConvA E I n Γ (instantiate0A t e) (instantiate0A t' e) (instantiate0A t T) := by
  have h := hasTyA_func hE hI (iotaRecHeadTypedA_of hR) hIS (convSubstA_cons_let hE hI hΓ ht hct ht' hct' hc) he
  rw [substA_cons_id_instantiate0, substA_cons_id_instantiate0,
    substA_cons_id_instantiate0] at h
  exact h

end Tools

/-! ## (3) annotation coherence -/

section Coh
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- ANNOTATION COHERENCE (M3-c0): two well-typed annotated terms with one erasure are convertible
    at the first one's type. -/
theorem annCohA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) :
    (e₁ : ExprA) → {Γ : LCtxA} → CtxWfA E I n Γ → {e₂ T₁ T₂ : ExprA} → erase e₁ = erase e₂ →
      HasTyA E I n Γ e₁ T₁ → HasTyA E I n Γ e₂ T₂ → Nonempty (ConvA E I n Γ e₁ e₂ T₁)
  | .bvar _, Γ, _, _, _, _, he, h₁, _ => by
      obtain rfl := erase_eq_bvar he.symm
      exact ⟨.refl Γ _ _ h₁⟩
  | .sort _, Γ, _, _, _, _, he, h₁, _ => by
      obtain rfl := erase_eq_sort he.symm
      exact ⟨.refl Γ _ _ h₁⟩
  | .const _ _, Γ, _, _, _, _, he, h₁, _ => by
      obtain rfl := erase_eq_const he.symm
      exact ⟨.refl Γ _ _ h₁⟩
  | .lit _, Γ, _, _, _, _, he, h₁, _ => by
      obtain rfl := erase_eq_lit he.symm
      exact ⟨.refl Γ _ _ h₁⟩
  | .app f a, Γ, hΓ, _, _, _, he, h₁, h₂ => by
      obtain ⟨f₂, a₂, rfl, hf, ha⟩ := erase_eq_app he.symm
      obtain ⟨A₁, u₁, B₁, v₁, _, ⟨hf₁⟩, ⟨ha₁⟩, ⟨hB₁⟩, ⟨hTy₁⟩, ⟨t₁⟩⟩ := hasTyA_app_gen h₁
      obtain ⟨_, _, _, _, _, ⟨hf₂⟩, ⟨ha₂⟩, _, _, _⟩ := hasTyA_app_gen h₂
      obtain ⟨cf⟩ := annCohA hE hI hIS hEN hNC hR hS hρ f hΓ hf.symm hf₁ hf₂
      obtain ⟨ca⟩ := annCohA hE hI hIS hEN hNC hR hS hρ a hΓ ha.symm ha₁ ha₂
      have hf₂' := convA_hasTy_right hE hI hR hIS hΓ cf
      have ha₂' := convA_hasTy_right hE hI hR hIS hΓ ca
      have hBa₂ : HasTyA E I n Γ (instantiate0A a₂ B₁) (.sort v₁) :=
        hasTyA_inst0' hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hB₁ ha₂'
      have happ : HasTyA E I n Γ (.app f₂ a₂) (instantiate0A a₂ B₁) :=
        .app Γ f₂ a₂ A₁ B₁ u₁ v₁ v₁ hB₁ hBa₂ hf₂' ha₂'
      obtain ⟨_, hs⟩ := hasTyA_regular hE hI hR hIS hΓ ha₁
      have cB : ConvA E I n Γ (instantiate0A a₂ B₁) (instantiate0A a B₁) (.sort v₁) :=
        hasTyA_func0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hB₁ (.symm _ _ _ _ ca) hs
      have hrt := hasTyA_of_tyConvA happ (tyConvA_ofConv hE hI hR hIS hΓ cB)
      exact ⟨convA_of_tyConvA (.app Γ f f₂ a a₂ A₁ B₁ u₁ v₁ cf ca hB₁ hrt) t₁⟩
  | .lam A u b, Γ, hΓ, _, _, _, he, h₁, h₂ => by
      obtain ⟨A₂, u₂, b₂, rfl, hA, hb⟩ := erase_eq_lam he.symm
      obtain ⟨B, v, ⟨hA₁⟩, ⟨hB₁⟩, ⟨hb₁⟩, ⟨t₁⟩⟩ := hasTyA_lam_gen h₁
      obtain ⟨B₂, v₂, ⟨hA₂⟩, ⟨hB₂⟩, ⟨hb₂⟩, _⟩ := hasTyA_lam_gen h₂
      obtain ⟨cA⟩ := annCohA hE hI hIS hEN hNC hR hS hρ A hΓ hA.symm hA₁ hA₂
      have hA₂u := convA_hasTy_right hE hI hR hIS hΓ cA
      have hu : eqN u u₂ := sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ hA₂u hA₂
      have K : CtxConvA E I n (.assumption A₂ :: Γ) (.assumption A :: Γ) :=
        .assumption (ctxConvA_refl Γ) ⟨hA₂u⟩ ⟨hA₁⟩ ⟨.symm _ _ _ _ cA⟩
      have hRT := iotaRecHeadTypedA_of hR
      obtain ⟨hb₂'⟩ := hasTyA_ctxConv hE hI hRT K hb₂
      obtain ⟨hB₂'⟩ := hasTyA_ctxConv hE hI hRT K hB₂
      have hΓA : CtxWfA E I n (.assumption A :: Γ) := .assumption hΓ hA₁
      obtain ⟨cb⟩ := annCohA hE hI hIS hEN hNC hR hS hρ b hΓA hb.symm hb₁ hb₂'
      obtain ⟨tB⟩ := hasTyA_uniq hE hI hIS hEN hNC hR hS hρ hΓA (convA_hasTy_right hE hI hR hIS hΓA cb) hb₂'
      have cB := tyConvA_collapse hE hI hIS hEN hNC hR hS hρ hΓA tB hB₁
      have hv : eqN v v₂ :=
        sortUniqA hE hI hIS hEN hNC hR hS hρ hΓA (convA_hasTy_right hE hI hR hIS hΓA cB) hB₂'
      have heq : eqN (.imax u₂ v₂) (.imax u v) := eqNA_imax (eqNA_symm hu) (eqNA_symm hv)
      have hpi₂ : HasTyA E I n Γ (.pi A₂ u₂ B₂ v₂) (.sort (.imax u v)) :=
        .conv Γ _ _ _ _ _ (.pi Γ A₂ u₂ B₂ v₂ hA₂ hB₂) (.sort Γ _) (eqNA_succ heq) (.sort Γ _)
          (convA_sort_eqN (.sorts Γ _ _ heq) (eqNA_succ heq))
      have cpi : ConvA E I n Γ (.pi A u B v) (.pi A₂ u₂ B₂ v₂) (.sort (.imax u v)) :=
        .pi Γ A A₂ B B₂ u u₂ v v₂ hu hv cA cB hpi₂
      have hrt : HasTyA E I n Γ (.lam A₂ u₂ b₂) (.pi A u B v) :=
        hasTyA_of_tyConvA (.lam Γ A₂ u₂ b₂ B₂ v₂ hA₂ hB₂ hb₂)
          (tyConvA_ofConv hE hI hR hIS hΓ cpi).symm
      exact ⟨convA_of_tyConvA (.lam Γ A A₂ b b₂ B u u₂ v hu cA cb hrt) t₁⟩
  | .pi A u B v, Γ, hΓ, _, _, _, he, h₁, h₂ => by
      obtain ⟨A₂, u₂, B₂, v₂, rfl, hA, hB⟩ := erase_eq_pi he.symm
      obtain ⟨hA₁, hB₁⟩ := hasTyA_pi_parts h₁
      obtain ⟨hA₂, hB₂⟩ := hasTyA_pi_parts h₂
      obtain ⟨cA⟩ := annCohA hE hI hIS hEN hNC hR hS hρ A hΓ hA.symm hA₁ hA₂
      have hA₂u := convA_hasTy_right hE hI hR hIS hΓ cA
      have hu : eqN u u₂ := sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ hA₂u hA₂
      have K : CtxConvA E I n (.assumption A₂ :: Γ) (.assumption A :: Γ) :=
        .assumption (ctxConvA_refl Γ) ⟨hA₂u⟩ ⟨hA₁⟩ ⟨.symm _ _ _ _ cA⟩
      obtain ⟨hB₂'⟩ := hasTyA_ctxConv hE hI (iotaRecHeadTypedA_of hR) K hB₂
      have hΓA : CtxWfA E I n (.assumption A :: Γ) := .assumption hΓ hA₁
      obtain ⟨cB⟩ := annCohA hE hI hIS hEN hNC hR hS hρ B hΓA hB.symm hB₁ hB₂'
      have hv : eqN v v₂ :=
        sortUniqA hE hI hIS hEN hNC hR hS hρ hΓA (convA_hasTy_right hE hI hR hIS hΓA cB) hB₂'
      have heq : eqN (.imax u₂ v₂) (.imax u v) := eqNA_imax (eqNA_symm hu) (eqNA_symm hv)
      have hpi₂ : HasTyA E I n Γ (.pi A₂ u₂ B₂ v₂) (.sort (.imax u v)) :=
        .conv Γ _ _ _ _ _ (.pi Γ A₂ u₂ B₂ v₂ hA₂ hB₂) (.sort Γ _) (eqNA_succ heq) (.sort Γ _)
          (convA_sort_eqN (.sorts Γ _ _ heq) (eqNA_succ heq))
      exact ⟨convA_of_tyConvA (.pi Γ A A₂ B B₂ u u₂ v v₂ hu hv cA cB hpi₂) (hasTyA_pi_sort h₁)⟩
  | .letE A v b, Γ, hΓ, _, _, _, he, h₁, h₂ => by
      obtain ⟨A₂, v₂, b₂, rfl, hA, hv, hb⟩ := erase_eq_letE he.symm
      obtain ⟨u, _, B, ⟨hA₁⟩, ⟨hv₁⟩, ⟨hTy₁⟩, ⟨hb₁⟩, ⟨t₁⟩⟩ := hasTyA_letE_gen h₁
      obtain ⟨u₂, _, _, ⟨hA₂⟩, ⟨hv₂⟩, _, ⟨hb₂⟩, _⟩ := hasTyA_letE_gen h₂
      obtain ⟨cA⟩ := annCohA hE hI hIS hEN hNC hR hS hρ A hΓ hA.symm hA₁ hA₂
      have hA₂u := convA_hasTy_right hE hI hR hIS hΓ cA
      obtain ⟨cv⟩ := annCohA hE hI hIS hEN hNC hR hS hρ v hΓ hv.symm hv₁ hv₂
      have hv₂A := convA_hasTy_right hE hI hR hIS hΓ cv
      have tAA₂ : TyConvA E I n Γ A A₂ := tyConvA_ofConv hE hI hR hIS hΓ cA
      have cv' : ConvA E I n Γ v₂ v A₂ := convA_of_tyConvA (.symm _ _ _ _ cv) tAA₂
      have hRT := iotaRecHeadTypedA_of hR
      have K : CtxConvA E I n (.letBinding A₂ v₂ :: Γ) (.letBinding A v :: Γ) :=
        .letBinding (ctxConvA_refl Γ) ⟨hA₂u⟩ ⟨hA₁⟩ ⟨.symm _ _ _ _ cA⟩ ⟨hv₁⟩ ⟨cv'⟩
      obtain ⟨hb₂'⟩ := hasTyA_ctxConv hE hI hRT K hb₂
      have hΓv : CtxWfA E I n (.letBinding A v :: Γ) := .letBinding hΓ hA₁ hv₁
      obtain ⟨cb⟩ := annCohA hE hI hIS hEN hNC hR hS hρ b hΓv hb.symm hb₁ hb₂'
      have K' : CtxConvA E I n (.letBinding A v :: Γ) (.letBinding A₂ v₂ :: Γ) :=
        .letBinding (ctxConvA_refl Γ) ⟨hA₁⟩ ⟨hA₂u⟩ ⟨cA⟩ ⟨hv₂⟩ ⟨cv⟩
      obtain ⟨hb₂B⟩ := hasTyA_ctxConv hE hI hRT K' (convA_hasTy_right hE hI hR hIS hΓv cb)
      obtain ⟨s, hBs⟩ := hasTyA_regular hE hI hR hIS hΓv hb₁
      obtain ⟨hBs'⟩ := hasTyA_ctxConv hE hI hRT K' hBs
      have hlet : HasTyA E I n Γ (.letE A₂ v₂ b₂) (instantiate0A v₂ B) :=
        .letE Γ A₂ u₂ s v₂ B b₂ hA₂ hv₂ (hasTyA_inst0Let hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hBs' hv₂) hb₂B
      have cBv : ConvA E I n Γ (instantiate0A v₂ B) (instantiate0A v B) (.sort s) :=
        convA_inst0Let_func hE hI hR hIS hΓ hBs hv₂A (.symm _ _ _ _ cv) hv₁ (.refl Γ v A hv₁)
          (.symm _ _ _ _ cv)
      have hrt := hasTyA_of_tyConvA hlet (tyConvA_ofConv hE hI hR hIS hΓ cBv)
      exact ⟨convA_of_tyConvA (.letE Γ A A₂ v v₂ b b₂ B u cA cv cb hrt) t₁⟩

/-- type coherence: two well-typed annotated terms with one erasure have convertible types. -/
theorem annTyA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {e₁ e₂ T₁ T₂ : ExprA} (he : erase e₁ = erase e₂)
    (h₁ : HasTyA E I n Γ e₁ T₁) (h₂ : HasTyA E I n Γ e₂ T₂) :
    Nonempty (TyConvA E I n Γ T₁ T₂) := by
  obtain ⟨c⟩ := annCohA hE hI hIS hEN hNC hR hS hρ e₁ hΓ he h₁ h₂
  exact hasTyA_uniq hE hI hIS hEN hNC hR hS hρ hΓ (convA_hasTy_right hE hI hR hIS hΓ c) h₂

/-- annotation-blind sort uniqueness: two annotations of one type have `=ₙ` sorts. -/
theorem annSortA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {X₁ X₂ : ExprA} {a b : Level} (he : erase X₁ = erase X₂)
    (h₁ : HasTyA E I n Γ X₁ (.sort a)) (h₂ : HasTyA E I n Γ X₂ (.sort b)) : eqN a b := by
  obtain ⟨c⟩ := annCohA hE hI hIS hEN hNC hR hS hρ X₁ hΓ he h₁ h₂
  exact sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ (convA_hasTy_right hE hI hR hIS hΓ c) h₂

end Coh

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.annCohA
#print axioms Rcic.Declarative.Ann.annTyA
#print axioms Rcic.Declarative.Ann.annSortA
