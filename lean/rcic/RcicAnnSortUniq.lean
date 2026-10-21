import rcic.RcicAnnFamRow

/-!
# M3-a — DT-012 on the copy: sort uniqueness, chain collapse, type uniqueness

DT-012 (`02` §14, type uniqueness up to convertibility) is the coverage wall of the typed root edit
(R-ConvCollapse). This module proves it on the copy, from the logical relation, with no
algorithmic instance.

**(a1) Sort uniqueness of types** (`sortUniqA`): a type's sorts are `=ₙ`. The ingredients are:

* generation at every head (`hasTyA_*_gen`): the subject's type converts from the head's own;
* three refutations by the relation: a proposition is not convertible to a sort, nor to a
  Type-level pi, and a pi is not convertible to a sort (`EqKA` has no clause between them);
* injectivity at a Type-level pi through any chain (`tyConvA_pi_inj`): `EqKA.pi`'s codomain datum
  at the self-related argument;
* the spine walk (`spine_tyConv`): two typings of a spine headed by a variable, a constant, a sort
  or a pi, the first at a LARGE type (convertible to a sort or to a Type-level pi), have convertible
  types. Every pi met on the way is Type-level, so the walk stays at large types;
* subject reduction at a large type, one typed head step at a time (`tyHRedA_sr_large`), by
  recursion on the step;
* the induction along the type's weak-head chain to its normal form, which the relation supplies
  (`hasTyA_sort_whnf`). At the normal form the head is canonical, or the type is no type.

**(a2) Chain collapse** (`tyConvA_collapse`): a type conversion chain out of a type of sort `l` is one
conversion at `sort l`. Sort uniqueness identifies each piece's sort with `l`.

**(a3) Type uniqueness** (`hasTyA_uniq`): two types of one term are convertible. The proof recurses
on the first derivation and generates the second at the same head.

* At a λ, the codomains' sorts are `=ₙ` by collapse and sort uniqueness.
* At an application, `PiConvInj` at any codomain (M2-g′) gives the codomains.

The concrete-ι corollaries (`sortUniqA_rec`, `hasTyA_uniq_rec`) take the semantic hypotheses from
the environment's well-formedness under the profile.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) generation: the subject's type converts from the head's own -/

section Gen
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- a `conv` step appends one piece to the conversion closure of a typing's type. -/
def tyConvA_snoc_conv {Γ : LCtxA} {C A B : ExprA} {l u : Level} (h : TyConvA E I n Γ C A)
    (hAl : HasTyA E I n Γ A (.sort l)) (hlu : eqN l u) (hB : HasTyA E I n Γ B (.sort u))
    (hc : ConvA E I n Γ A B (.sort u)) : TyConvA E I n Γ C B :=
  .trans Γ C A B h (.of Γ A B l u u hAl hlu hB (eqNA_refl u) hc)

def hasTyA_sort_gen : {Γ : LCtxA} → {l : Level} → {T : ExprA} → HasTyA E I n Γ (.sort l) T →
    TyConvA E I n Γ (.sort (.succ l)) T
  | _, _, _, .sort Γ _ => .refl Γ _
  | _, _, _, .conv _ _ _ _ _ _ h hAl hlu hB hc => tyConvA_snoc_conv (hasTyA_sort_gen h) hAl hlu hB hc

/-- the variable's type converts from its context type. -/
theorem hasTyA_bvar_gen : {Γ : LCtxA} → {i : Nat} → {T : ExprA} → HasTyA E I n Γ (.bvar i) T →
    ∃ A, lookupTypeA Γ i = some A ∧ Nonempty (TyConvA E I n Γ A T)
  | _, _, _, .bvar Γ _ A _ h _ => ⟨A, h, ⟨.refl Γ A⟩⟩
  | _, _, _, .conv _ _ _ _ _ _ h hAl hlu hB hc => by
      obtain ⟨A, hA, ⟨t⟩⟩ := hasTyA_bvar_gen h
      exact ⟨A, hA, ⟨tyConvA_snoc_conv t hAl hlu hB hc⟩⟩

/-- a constant's type converts from its member's instantiated type. -/
theorem hasTyA_const_gen : {Γ : LCtxA} → {r : Nat} → {ls : List Level} → {T : ExprA} →
    HasTyA E I n Γ (.const r ls) T →
    ∃ m, E.members r = some m ∧ Nonempty (TyConvA E I n Γ (instantiateLevelsA ls m.mtypeA) T)
  | _, _, _, _, .const Γ _ _ m _ hres _ _ _ => ⟨m, hres, ⟨.refl Γ _⟩⟩
  | _, _, _, _, .conv _ _ _ _ _ _ h hAl hlu hB hc => by
      obtain ⟨m, hm, ⟨t⟩⟩ := hasTyA_const_gen h
      exact ⟨m, hm, ⟨tyConvA_snoc_conv t hAl hlu hB hc⟩⟩

/-- a λ's type converts from a pi over its annotated domain, at a codomain the body is typed at. -/
theorem hasTyA_lam_gen : {Γ : LCtxA} → {A : ExprA} → {u : Level} → {b T : ExprA} →
    HasTyA E I n Γ (.lam A u b) T →
    ∃ B v, Nonempty (HasTyA E I n Γ A (.sort u)) ∧
      Nonempty (HasTyA E I n (.assumption A :: Γ) B (.sort v)) ∧
      Nonempty (HasTyA E I n (.assumption A :: Γ) b B) ∧
      Nonempty (TyConvA E I n Γ (.pi A u B v) T)
  | _, _, _, _, _, .lam Γ A u _ B v hA hB hb => ⟨B, v, ⟨hA⟩, ⟨hB⟩, ⟨hb⟩, ⟨.refl Γ _⟩⟩
  | _, _, _, _, _, .conv _ _ _ _ _ _ h hAl hlu hB' hc => by
      obtain ⟨B, v, hA, hB, hb, ⟨t⟩⟩ := hasTyA_lam_gen h
      exact ⟨B, v, hA, hB, hb, ⟨tyConvA_snoc_conv t hAl hlu hB' hc⟩⟩

/-- an application's type converts from the function's codomain at the argument. -/
theorem hasTyA_app_gen : {Γ : LCtxA} → {f a T : ExprA} → HasTyA E I n Γ (.app f a) T →
    ∃ A u B v w, Nonempty (HasTyA E I n Γ f (.pi A u B v)) ∧ Nonempty (HasTyA E I n Γ a A) ∧
      Nonempty (HasTyA E I n (.assumption A :: Γ) B (.sort v)) ∧
      Nonempty (HasTyA E I n Γ (instantiate0A a B) (.sort w)) ∧
      Nonempty (TyConvA E I n Γ (instantiate0A a B) T)
  | _, _, _, _, .app Γ _ _ A B u v w hB hTy hf ha =>
      ⟨A, u, B, v, w, ⟨hf⟩, ⟨ha⟩, ⟨hB⟩, ⟨hTy⟩, ⟨.refl Γ _⟩⟩
  | _, _, _, _, .conv _ _ _ _ _ _ h hAl hlu hB' hc => by
      obtain ⟨A, u, B, v, w, hf, ha, hB, hTy, ⟨t⟩⟩ := hasTyA_app_gen h
      exact ⟨A, u, B, v, w, hf, ha, hB, hTy, ⟨tyConvA_snoc_conv t hAl hlu hB' hc⟩⟩

/-- a let's type converts from its body's type at the value. -/
theorem hasTyA_letE_gen : {Γ : LCtxA} → {A v b T : ExprA} → HasTyA E I n Γ (.letE A v b) T →
    ∃ u w B, Nonempty (HasTyA E I n Γ A (.sort u)) ∧ Nonempty (HasTyA E I n Γ v A) ∧
      Nonempty (HasTyA E I n Γ (instantiate0A v B) (.sort w)) ∧
      Nonempty (HasTyA E I n (.letBinding A v :: Γ) b B) ∧
      Nonempty (TyConvA E I n Γ (instantiate0A v B) T)
  | _, _, _, _, _, .letE Γ A u w _ B _ hA hv hTy hb => ⟨u, w, B, ⟨hA⟩, ⟨hv⟩, ⟨hTy⟩, ⟨hb⟩, ⟨.refl Γ _⟩⟩
  | _, _, _, _, _, .conv _ _ _ _ _ _ h hAl hlu hB' hc => by
      obtain ⟨u, w, B, hA, hv, hTy, hb, ⟨t⟩⟩ := hasTyA_letE_gen h
      exact ⟨u, w, B, hA, hv, hTy, hb, ⟨tyConvA_snoc_conv t hAl hlu hB' hc⟩⟩

/-- a literal is typed wherever its expansion is. -/
def hasTyA_lit_gen : {Γ : LCtxA} → {t : Nat} → {T : ExprA} → HasTyA E I n Γ (.lit t) T →
    HasTyA E I n Γ (natExpandA t) T
  | _, _, _, .lit _ _ _ h => h
  | _, _, _, .conv Γ _ A B l u h hAl hlu hB hc => .conv Γ _ A B l u (hasTyA_lit_gen h) hAl hlu hB hc

end Gen

/-! ## (2) the let binder instantiated -/

section LetInst
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- `0 ↦ v` over a let binder `A := v`, the identity on the tail. -/
def substTyA_cons_id_let (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {v A : ExprA}
    (hΓ : CtxWfA E I n Γ) (hv : HasTyA E I n Γ v A) :
    SubstTyA E I n Γ (SubstA.cons v SubstA.id) (.letBinding A v :: Γ) where
  ty := fun i B hlu => by
    cases i with
    | zero =>
        have hB : B = liftA 0 1 A := lookupTypeA_zero_let_eq hlu
        subst hB
        rw [SubstA.cons_zero, substA_cons_id_lift]
        exact hv
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
        exact .refl Γ v A hv
    | succ i =>
        let sB := liftedTypeA (.letBinding A v) Γ hty
        let sv := liftedValueA (.letBinding A v) Γ hval
        have hB : B = liftA 0 1 sB.orig := sB.eq_lift
        have hw : w = liftA 0 1 sv.orig := sv.eq_lift
        rw [hB, hw]
        rw [SubstA.cons_succ, substA_cons_id_lift, substA_cons_id_lift]
        have hc := (substTyA_id hE hI hΓ).val i sB.orig sv.orig sB.got sv.got
        rw [SubstA.id_apply, substA_id, substA_id] at hc
        exact hc

/-- the let body instantiated at its value. -/
def hasTyA_inst0Let (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} {e v A B : ExprA}
    (hΓ : CtxWfA E I n Γ) (he : HasTyA E I n (.letBinding A v :: Γ) e B)
    (hv : HasTyA E I n Γ v A) :
    HasTyA E I n Γ (instantiate0A v e) (instantiate0A v B) := by
  have hsub := hasTyA_substA hE hI hR hIS (substTyA_cons_id_let hE hI hΓ hv) he
  rw [substA_cons_id_instantiate0, substA_cons_id_instantiate0] at hsub
  exact hsub

end LetInst

/-! ## (3) large types, and three refutations by the relation -/

/-- a type convertible to a sort. -/
def SortLikeA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (T : ExprA) : Prop :=
  ∃ a, Nonempty (TyConvA E I n Γ T (.sort a))

/-- a type convertible to a Type-level pi. -/
def TyPiLikeA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (T : ExprA) : Prop :=
  ∃ A u B v, isZero v = false ∧ Nonempty (TyConvA E I n Γ T (.pi A u B v))

/-- a LARGE type: convertible to a sort or to a Type-level pi. -/
def LargeA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (T : ExprA) : Prop :=
  SortLikeA E I n Γ T ∨ TyPiLikeA E I n Γ T

section Refute
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- no type equality between a pi and a sort. -/
theorem eqKA_pi_sort_false {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA}
    {D : ExprA} {u : Level} {C : ExprA} {v a : Level}
    (h : EqKA E I n ρ₀ k LE LT Γ (.pi D u C v) (.sort a)) : False := by
  cases h with
  | sort hA _ _ _ _ =>
      exact absurd (whTyA_det hA (whTyA_self hA) (hStepFnA_sort E I.fn Γ _)
        (hStepFnA_pi E I.fn Γ D u C v)) (fun e => ExprA.noConfusion e)
  | pi _ hB _ _ _ _ _ _ _ _ _ _ _ =>
      exact absurd (whTyA_det hB (whTyA_self hB) (hStepFnA_pi E I.fn Γ _ _ _ _)
        (hStepFnA_sort E I.fn Γ a)) (fun e => ExprA.noConfusion e)
  | fam hA _ hnA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact absurd (whTyA_det hA (whTyA_self hA) hnA (hStepFnA_pi E I.fn Γ D u C v))
        (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck _ hB _ hN' _ =>
      have e := whTyA_det hB (whTyA_self hB) hN'.1 (hStepFnA_sort E I.fn Γ a)
      subst e
      exact tripleLikeA_not_sort hN'

/-- no type equality from a triple-like normal form to a sort. -/
theorem eqKA_tripleLike_sort_false {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA}
    {P N : ExprA} {a : Level} (hP : WhTyA E I n Γ P N) (hN : TripleLikeA E I Γ N)
    (h : EqKA E I n ρ₀ k LE LT Γ P (.sort a)) : False := by
  cases h with
  | sort hA _ _ _ _ =>
      have e := whTyA_det hP hA hN.1 (hStepFnA_sort E I.fn Γ _)
      subst e
      exact tripleLikeA_not_sort hN
  | pi _ hB _ _ _ _ _ _ _ _ _ _ _ =>
      exact absurd (whTyA_det hB (whTyA_self hB) (hStepFnA_pi E I.fn Γ _ _ _ _)
        (hStepFnA_sort E I.fn Γ a)) (fun e => ExprA.noConfusion e)
  | fam _ hB _ hnB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact absurd (whTyA_det hB (whTyA_self hB) hnB (hStepFnA_sort E I.fn Γ a)) (foldAppsA_const_ne_sort _ _ _ _)
  | stuck _ hB _ hN' _ =>
      have e := whTyA_det hB (whTyA_self hB) hN'.1 (hStepFnA_sort E I.fn Γ a)
      subst e
      exact tripleLikeA_not_sort hN'

/-- no type equality from a triple-like normal form to a Type-level pi. -/
theorem eqKA_tripleLike_typi_false {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA}
    {P N : ExprA} {D : ExprA} {u : Level} {C : ExprA} {v : Level} (hz : isZero v = false)
    (hP : WhTyA E I n Γ P N) (hN : TripleLikeA E I Γ N)
    (h : EqKA E I n ρ₀ k LE LT Γ P (.pi D u C v)) : False := by
  cases h with
  | sort _ hB _ _ _ =>
      exact absurd (whTyA_det hB (whTyA_self hB) (hStepFnA_sort E I.fn Γ _)
        (hStepFnA_pi E I.fn Γ D u C v)) (fun e => ExprA.noConfusion e)
  | pi hA hB _ hv _ _ _ _ _ _ _ _ _ =>
      have e1 := whTyA_det hP hA hN.1 (hStepFnA_pi E I.fn Γ _ _ _ _)
      have e2 := whTyA_det hB (whTyA_self hB) (hStepFnA_pi E I.fn Γ _ _ _ _) (hStepFnA_pi E I.fn Γ D u C v)
      subst e1
      injection e2 with _ _ _ e24
      subst e24
      have hP0 := (isPropTy_pi_iff E I Γ _ _ _ _).1 (tripleLikeA_pi_isProp hN)
      rw [isZero_eqN hv, hz] at hP0
      cases hP0
  | fam _ hB _ hnB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact absurd (whTyA_det hB (whTyA_self hB) hnB (hStepFnA_pi E I.fn Γ D u C v))
        (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck _ hB _ hN' _ =>
      have e := whTyA_det hB (whTyA_self hB) hN'.1 (hStepFnA_pi E I.fn Γ D u C v)
      subst e
      have hP0 := (isPropTy_pi_iff E I Γ _ _ _ _).1 (tripleLikeA_pi_isProp hN')
      rw [hz] at hP0
      cases hP0

/-- a pi is not convertible to a sort, through any chain. -/
theorem tyConvA_pi_sort_false (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {D : ExprA} {u : Level} {C : ExprA} {v a : Level}
    (h : TyConvA E I n Γ (.pi D u C v) (.sort a)) : False := by
  rcases fund_tyConvA hE hI hIS hEN hNC hR hS hρ hΓ h with e | ⟨k₀, hk⟩
  · exact ExprA.noConfusion e
  · have := hk k₀ (Nat.le_refl _)
    rw [LREqA_eq] at this
    exact eqKA_pi_sort_false this

/-- a proposition's normal form is triple-like (the `sortP` relation's validity). -/
theorem prop_whnf (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {P : ExprA} {v : Level} (hP : HasTyA E I n Γ P (.sort v))
    (hz : isZero v = true) : ∃ N, WhTyA E I n Γ P N ∧ TripleLikeA E I Γ N := by
  obtain ⟨k₀, hk⟩ := fund_self hE hI hIS hEN hNC hR hS hρ hΓ hP
  exact (LRRelA_sortP_elim hz (hk k₀ (Nat.le_refl _))).1

/-- a proposition is not convertible to a sort. -/
theorem tyConvA_prop_sort_false (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {P : ExprA} {v a : Level} (hP : HasTyA E I n Γ P (.sort v))
    (hz : isZero v = true) (h : TyConvA E I n Γ P (.sort a)) : False := by
  rcases fund_tyConvA hE hI hIS hEN hNC hR hS hρ hΓ h with e | ⟨k₀, hk⟩
  · subst e
    have hw := tyConvA_sorts_eqN hE hI hIS hEN hNC hR hS hρ hΓ (hasTyA_sort_gen hP)
    have := isZero_eqN hw
    rw [hz] at this
    cases this
  · obtain ⟨N, hN, hNt⟩ := prop_whnf hE hI hIS hEN hNC hR hS hρ hΓ hP hz
    have := hk k₀ (Nat.le_refl _)
    rw [LREqA_eq] at this
    exact eqKA_tripleLike_sort_false hN hNt this

/-- a proposition is not convertible to a Type-level pi. -/
theorem tyConvA_prop_typi_false (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {P : ExprA} {v : Level} (hP : HasTyA E I n Γ P (.sort v))
    (hz : isZero v = true) {D : ExprA} {u : Level} {C : ExprA} {w : Level} (hw : isZero w = false)
    (h : TyConvA E I n Γ P (.pi D u C w)) : False := by
  rcases fund_tyConvA hE hI hIS hEN hNC hR hS hρ hΓ h with e | ⟨k₀, hk⟩
  · subst e
    have he := tyConvA_sorts_eqN hE hI hIS hEN hNC hR hS hρ hΓ (hasTyA_pi_sort hP)
    have := isZero_eqN he
    rw [isZero_imax, hw, hz] at this
    cases this
  · obtain ⟨N, hN, hNt⟩ := prop_whnf hE hI hIS hEN hNC hR hS hρ hΓ hP hz
    have := hk k₀ (Nat.le_refl _)
    rw [LREqA_eq] at this
    exact eqKA_tripleLike_typi_false hw hN hNt this

/-- a proposition is not convertible to a large type. -/
theorem tyConvA_prop_large_false (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {P T : ExprA} {v : Level} (hP : HasTyA E I n Γ P (.sort v))
    (hz : isZero v = true) (h : Nonempty (TyConvA E I n Γ P T)) (hL : LargeA E I n Γ T) : False := by
  obtain ⟨t⟩ := h
  rcases hL with ⟨a, ⟨ta⟩⟩ | ⟨D, u, C, w, hw, ⟨tp⟩⟩
  · exact tyConvA_prop_sort_false hE hI hIS hEN hNC hR hS hρ hΓ hP hz (.trans _ _ _ _ t ta)
  · exact tyConvA_prop_typi_false hE hI hIS hEN hNC hR hS hρ hΓ hP hz hw (.trans _ _ _ _ t tp)

/-- a large type stays large along a type conversion into it. -/
theorem largeA_of_tyConv {Γ : LCtxA} {T T' : ExprA} (h : Nonempty (TyConvA E I n Γ T' T))
    (hL : LargeA E I n Γ T) : LargeA E I n Γ T' := by
  obtain ⟨t⟩ := h
  rcases hL with ⟨a, ⟨ta⟩⟩ | ⟨D, u, C, w, hw, ⟨tp⟩⟩
  · exact Or.inl ⟨a, ⟨.trans _ _ _ _ t ta⟩⟩
  · exact Or.inr ⟨D, u, C, w, hw, ⟨.trans _ _ _ _ t tp⟩⟩

end Refute

/-! ## (4) injectivity at a Type-level pi, through any chain -/

section PiInj
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a Type-level pi's conversion, through any chain: convertible domains, and codomains convertible
    at every argument of the left domain (`EqKA.pi`'s codomain datum at the self-related argument). -/
theorem tyConvA_pi_inj (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {A : ExprA} {u : Level} {B : ExprA} {v : Level} {A' : ExprA}
    {u' : Level} {B' : ExprA} {v' : Level} (hz : isZero v = false)
    (h : TyConvA E I n Γ (.pi A u B v) (.pi A' u' B' v')) :
    Nonempty (TyConvA E I n Γ A A') ∧
    ∀ x, HasTyA E I n Γ x A →
      Nonempty (TyConvA E I n Γ (instantiate0A x B) (instantiate0A x B')) := by
  rcases fund_tyConvA hE hI hIS hEN hNC hR hS hρ hΓ h with e | ⟨k₀, hk⟩
  · injection e with e1 _ e3 _
    subst e1; subst e3
    exact ⟨⟨.refl _ _⟩, fun _ _ => ⟨.refl _ _⟩⟩
  · have hρ₀ : WkOkA E I n [] Γ := ⟨trivial, ⟨hΓ⟩⟩
    have hEq := hk k₀ (Nat.le_refl _)
    rw [LREqA_eq] at hEq
    obtain ⟨_, _, _, hDeq, _, _, _⟩ := eqKA_pi_inv hz hEq
    refine ⟨eqKA_tyConv (hDeq [] hρ₀), fun x hx => ?_⟩
    obtain ⟨k₁, hk₁⟩ := fund_self hE hI hIS hEN hNC hR hS hρ hΓ hx
    have hEq' := hk (max k₀ k₁) (Nat.le_max_left _ _)
    rw [LREqA_eq] at hEq'
    obtain ⟨_, _, _, _, RD, hD, hC⟩ := eqKA_pi_inv hz hEq'
    have hLR : LRTyA E I n ρ₀ (max k₀ k₁) Γ A (RD []) := by
      rw [LRTyA_eq]; exact hD [] hρ₀
    have hr : RD [] x x := (hk₁ (max k₀ k₁) (Nat.le_max_right _ _)).at hLR
    exact eqKA_tyConv (hC [] hρ₀ x x hr)

/-- an argument substituted into a codomain typed under the domain. -/
def hasTyA_inst0' (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} {e t A B : ExprA}
    (hΓ : CtxWfA E I n Γ) (he : HasTyA E I n (.assumption A :: Γ) e B)
    (ht : HasTyA E I n Γ t A) :
    HasTyA E I n Γ (instantiate0A t e) (instantiate0A t B) := by
  have hsub := hasTyA_substA hE hI hR hIS (substTyA_cons_id hE hI hΓ ht) he
  rw [substA_cons_id_instantiate0, substA_cons_id_instantiate0] at hsub
  exact hsub

/-- a codomain whose instance converts to a large type is Type-level: at a propositional codomain
    the instance is a proposition, which no large type is convertible from. -/
theorem codom_typeLevel (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {A B : ExprA} {v : Level} {x T : ExprA}
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v)) (hx : HasTyA E I n Γ x A)
    (hc : Nonempty (TyConvA E I n Γ (instantiate0A x B) T)) (hL : LargeA E I n Γ T) :
    isZero v = false := by
  cases hz : isZero v with
  | false => rfl
  | true =>
      have hBx : HasTyA E I n Γ (instantiate0A x B) (.sort v) := hasTyA_inst0' hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hB hx
      exact (tyConvA_prop_large_false hE hI hIS hEN hNC hR hS hρ hΓ hBx hz hc hL).elim

end PiInj

/-! ## (5) canonical heads and the spine walk -/

/-- a head whose every type converts from one canonical type. -/
def HeadCanonA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (h : ExprA) : Prop :=
  ∃ C, ∀ T, HasTyA E I n Γ h T → Nonempty (TyConvA E I n Γ C T)

section Spine
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem headCanonA_bvar (Γ : LCtxA) (i : Nat) : HeadCanonA E I n Γ (.bvar i) := by
  cases hl : lookupTypeA Γ i with
  | none =>
      refine ⟨.bvar i, fun T hT => ?_⟩
      obtain ⟨A, hA, _⟩ := hasTyA_bvar_gen hT
      rw [hl] at hA
      cases hA
  | some A =>
      refine ⟨A, fun T hT => ?_⟩
      obtain ⟨A', hA', ht⟩ := hasTyA_bvar_gen hT
      rw [hl] at hA'
      cases hA'
      exact ht

theorem headCanonA_const (Γ : LCtxA) (r : Nat) (ls : List Level) :
    HeadCanonA E I n Γ (.const r ls) := by
  cases hm : E.members r with
  | none =>
      refine ⟨.const r ls, fun T hT => ?_⟩
      obtain ⟨m, hm', _⟩ := hasTyA_const_gen hT
      rw [hm] at hm'
      cases hm'
  | some m =>
      refine ⟨instantiateLevelsA ls m.mtypeA, fun T hT => ?_⟩
      obtain ⟨m', hm', ht⟩ := hasTyA_const_gen hT
      rw [hm] at hm'
      cases hm'
      exact ht

theorem headCanonA_sort (Γ : LCtxA) (l : Level) : HeadCanonA E I n Γ (.sort l) :=
  ⟨.sort (.succ l), fun _ hT => ⟨hasTyA_sort_gen hT⟩⟩

theorem headCanonA_pi (Γ : LCtxA) (D : ExprA) (u : Level) (C : ExprA) (v : Level) :
    HeadCanonA E I n Γ (.pi D u C v) :=
  ⟨.sort (.imax u v), fun _ hT => ⟨hasTyA_pi_sort hT⟩⟩

/-- THE SPINE WALK: two typings of a spine with a canonical head, the first at a large type, have
    convertible types. Every pi met on the way is Type-level (its codomain's instance converts to a
    large type), so the induction stays at large types and pi injectivity moves the instance across. -/
theorem spine_tyConv (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {h : ExprA} (hh : HeadCanonA E I n Γ h) (xs : List ExprA) :
    ∀ {T₁ T₂ : ExprA}, HasTyA E I n Γ (foldAppsA h xs) T₁ → HasTyA E I n Γ (foldAppsA h xs) T₂ →
      LargeA E I n Γ T₁ → Nonempty (TyConvA E I n Γ T₁ T₂) := by
  refine snocInduction (P := fun xs => ∀ {T₁ T₂ : ExprA}, HasTyA E I n Γ (foldAppsA h xs) T₁ →
      HasTyA E I n Γ (foldAppsA h xs) T₂ → LargeA E I n Γ T₁ → Nonempty (TyConvA E I n Γ T₁ T₂))
    ?_ ?_ xs
  · intro T₁ T₂ h₁ h₂ _
    obtain ⟨C, hC⟩ := hh
    obtain ⟨t₁⟩ := hC _ h₁
    obtain ⟨t₂⟩ := hC _ h₂
    exact ⟨.trans _ _ _ _ t₁.symm t₂⟩
  · intro ys x ih T₁ T₂ h₁ h₂ hL
    rw [foldAppsA_append] at h₁ h₂
    obtain ⟨A₁, u₁, B₁, v₁, _, ⟨hf₁⟩, ⟨hx₁⟩, ⟨hB₁⟩, _, ⟨t₁⟩⟩ := hasTyA_app_gen h₁
    obtain ⟨_, _, _, _, _, ⟨hf₂⟩, _, _, _, ⟨t₂⟩⟩ := hasTyA_app_gen h₂
    have hz := codom_typeLevel hE hI hIS hEN hNC hR hS hρ hΓ hB₁ hx₁ ⟨t₁⟩ hL
    obtain ⟨tp⟩ := ih hf₁ hf₂ (Or.inr ⟨A₁, u₁, B₁, v₁, hz, ⟨.refl _ _⟩⟩)
    obtain ⟨_, hcod⟩ := tyConvA_pi_inj hE hI hIS hEN hNC hR hS hρ hΓ hz tp
    obtain ⟨tc⟩ := hcod x hx₁
    exact ⟨.trans _ _ _ _ t₁.symm (.trans _ _ _ _ tc t₂)⟩

/-- a spine with a constant head, as a spine. -/
theorem spine_const_eq {e : ExprA} {r : Nat} {ls : List Level}
    (h : (appsSpineA e).1 = .const r ls) : foldAppsA (.const r ls) (appsSpineA e).2 = e := by
  have := foldAppsA_appsSpineA e
  rw [h] at this
  exact this

end Spine

/-! ## (6) subject reduction at a large type, one typed head step at a time -/

section SR
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- SUBJECT REDUCTION AT A LARGE TYPE: a typed head step's reduct keeps every large type of the
    redex. Each rule's redex is generated at its head; at a large type every pi crossed is
    Type-level, where the type equality is `EqKA.pi` and moves the instance across (β, the major
    step, a head step under an application); a ι-redex and the major step's function are spines
    with a constant head, whose large types the spine walk relates. -/
theorem tyHRedA_sr_large (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) :
    {X X' Ts : ExprA} → TyHRedA E I n Γ X X' Ts → ∀ {T : ExprA}, HasTyA E I n Γ X T →
      LargeA E I n Γ T → Nonempty (HasTyA E I n Γ X' T)
  | _, _, _, .beta _ A u _ arg _ hA _ _ _, _, hX, hL => by
      obtain ⟨_, _, _, _, _, ⟨hf⟩, ⟨ha⟩, ⟨hB₁⟩, _, ⟨t⟩⟩ := hasTyA_app_gen hX
      have hz₁ := codom_typeLevel hE hI hIS hEN hNC hR hS hρ hΓ hB₁ ha ⟨t⟩ hL
      obtain ⟨B₂, v₂, _, ⟨hB₂⟩, ⟨hb⟩, ⟨tl⟩⟩ := hasTyA_lam_gen hf
      have hz₂ : isZero v₂ = false := by
        cases hz : isZero v₂ with
        | false => rfl
        | true =>
            exact (tyConvA_prop_typi_false hE hI hIS hEN hNC hR hS hρ hΓ (.pi Γ A u B₂ v₂ hA hB₂)
              (by rw [isZero_imax]; exact hz) hz₁ tl).elim
      obtain ⟨⟨tA⟩, hcod⟩ := tyConvA_pi_inj hE hI hIS hEN hNC hR hS hρ hΓ hz₂ tl
      have ha' : HasTyA E I n Γ arg A := hasTyA_of_tyConvA ha tA.symm
      obtain ⟨tc⟩ := hcod arg ha'
      exact ⟨hasTyA_of_tyConvA (hasTyA_inst0' hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hb ha') (.trans _ _ _ _ tc t)⟩
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, hX, _ => by
      obtain ⟨_, _, _, _, ⟨hv⟩, _, ⟨hb⟩, ⟨t⟩⟩ := hasTyA_letE_gen hX
      exact ⟨hasTyA_of_tyConvA (hasTyA_inst0Let hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hb hv) t⟩
  | _, _, _, .zetaLocal _ _ _ _ _ hty hv, _, hX, _ => by
      obtain ⟨A₁, hA₁, ⟨t⟩⟩ := hasTyA_bvar_gen hX
      rw [hty] at hA₁
      cases hA₁
      exact ⟨hasTyA_of_tyConvA hv t⟩
  | _, _, _, .delta _ _ _ _ _ hres _ _ _ _ hb, _, hX, _ => by
      obtain ⟨m₁, hm₁, ⟨t⟩⟩ := hasTyA_const_gen hX
      rw [hres] at hm₁
      cases hm₁
      exact ⟨hasTyA_of_tyConvA hb t⟩
  | _, _, _, .iota _ _ _ _ hrel hlhs hrhs, _, hX, hL => by
      obtain ⟨r, ls, _, hhead, _⟩ := hR _ _ hrel.1
      have e := spine_const_eq hhead
      rw [← e] at hX hlhs
      obtain ⟨t⟩ := spine_tyConv hE hI hIS hEN hNC hR hS hρ hΓ (headCanonA_const Γ r ls) _ hX hlhs hL
      exact ⟨hasTyA_of_tyConvA hrhs t.symm⟩
  | _, _, _, .lit _ _ _ _, _, hX, _ => ⟨hasTyA_lit_gen hX⟩
  | _, _, _, .app _ _ f' a _ _ _ _ _ _ h _ _ _ _, _, hX, hL => by
      obtain ⟨A₁, u₁, B₁, v₁, w₁, ⟨hf⟩, ⟨ha⟩, ⟨hB₁⟩, ⟨hTy₁⟩, ⟨t⟩⟩ := hasTyA_app_gen hX
      have hz := codom_typeLevel hE hI hIS hEN hNC hR hS hρ hΓ hB₁ ha ⟨t⟩ hL
      obtain ⟨hf'⟩ := tyHRedA_sr_large hE hI hIS hEN hNC hR hS hρ hΓ h hf
        (Or.inr ⟨A₁, u₁, B₁, v₁, hz, ⟨.refl _ _⟩⟩)
      exact ⟨hasTyA_of_tyConvA (.app Γ f' a A₁ B₁ u₁ v₁ w₁ hB₁ hTy₁ hf' ha) t⟩
  | _, _, _, .conv _ _ _ _ _ h _, _, hX, hL => tyHRedA_sr_large hE hI hIS hEN hNC hR hS hρ hΓ h hX hL
  | _, _, _, .major _ _ a _ _ _ _ _ _ hrec _ _ _ _ _ _ hfTy _ hrt, _, hX, hL => by
      obtain ⟨A₁, u₁, B₁, v₁, _, ⟨hf₁⟩, ⟨ha₁⟩, ⟨hB₁⟩, _, ⟨t⟩⟩ := hasTyA_app_gen hX
      have hz := codom_typeLevel hE hI hIS hEN hNC hR hS hρ hΓ hB₁ ha₁ ⟨t⟩ hL
      obtain ⟨r, ls, _, hhead, _⟩ := recAtMajorA_true hrec
      have e := spine_const_eq hhead
      rw [← e] at hf₁ hfTy
      obtain ⟨tp⟩ := spine_tyConv hE hI hIS hEN hNC hR hS hρ hΓ (headCanonA_const Γ r ls) _ hf₁ hfTy
        (Or.inr ⟨A₁, u₁, B₁, v₁, hz, ⟨.refl _ _⟩⟩)
      obtain ⟨_, hcod⟩ := tyConvA_pi_inj hE hI hIS hEN hNC hR hS hρ hΓ hz tp
      obtain ⟨tc⟩ := hcod a ha₁
      exact ⟨hasTyA_of_tyConvA hrt (.trans _ _ _ _ tc.symm t)⟩
  | _, _, _, .kunit _ f a _ _ hrec _ _ _ hcv hrt, _, hX, hL => by
      -- O1-b-1: the K-unit redex is a recursor spine, whose large types the spine walk relates
      obtain ⟨r, ls, _, hhead, _⟩ := recAtMajorA_true hrec
      have hhead' : (appsSpineA (ExprA.app f a)).1 = .const r ls := hhead
      have e := spine_const_eq hhead'
      have hlhs := convA_hasTy_left hE hI hR hIS hΓ hcv
      rw [← e] at hX hlhs
      obtain ⟨t⟩ := spine_tyConv hE hI hIS hEN hNC hR hS hρ hΓ (headCanonA_const Γ r ls) _ hX hlhs hL
      exact ⟨hasTyA_of_tyConvA hrt t.symm⟩
  | _, _, _, .kstruct _ f a _ _ hrec _ _ hcv hrt, _, hX, hL => by
      -- W-1 (a): the struct redex is a recursor spine, whose large types the spine walk relates
      obtain ⟨r, ls, _, hhead, _⟩ := recAtMajorA_true hrec
      have hhead' : (appsSpineA (ExprA.app f a)).1 = .const r ls := hhead
      have e := spine_const_eq hhead'
      have hlhs := convA_hasTy_left hE hI hR hIS hΓ hcv
      rw [← e] at hX hlhs
      obtain ⟨t⟩ := spine_tyConv hE hI hIS hEN hNC hR hS hρ hΓ (headCanonA_const Γ r ls) _ hX hlhs hL
      exact ⟨hasTyA_of_tyConvA hrt t.symm⟩

end SR

/-! ## (7) sort uniqueness along the weak-head chain -/

section SortUniq
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- every clause of the relation reaches its type's normal form. -/
theorem tyKA_whnf {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ : LCtxA} {A : ExprA}
    {R : ExprA → ExprA → Prop} (h : TyKA E I n ρ₀ k LE LT Γ A R) :
    ∃ N, WhTyA E I n Γ A N ∧ hStepFnA E I.fn Γ N = none := by
  cases h with
  | prop hA hn _ => exact ⟨_, hA, hn⟩
  | sortT hA _ _ => exact ⟨_, hA, hStepFnA_sort _ _ _ _⟩
  | sortP hA _ => exact ⟨_, hA, hStepFnA_sort _ _ _ _⟩
  | pi hA _ _ _ _ _ _ _ _ => exact ⟨_, hA, hStepFnA_pi _ _ _ _ _ _ _⟩
  | fam hA hn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact ⟨_, hA, hn⟩
  | stuck hA hN => exact ⟨_, hA, hN.1⟩

/-- a type reaches a normal form along a typed weak-head chain (validity: the relation at its sort). -/
theorem hasTyA_sort_whnf (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {X : ExprA} {a : Level} (hX : HasTyA E I n Γ X (.sort a)) :
    ∃ N, WhTyA E I n Γ X N ∧ hStepFnA E I.fn Γ N = none := by
  obtain ⟨k₀, hk⟩ := fund_self hE hI hIS hEN hNC hR hS hρ hΓ hX
  obtain ⟨_, ⟨Rt, hRt⟩, _⟩ := LRRelA_sort_elim (hk k₀ (Nat.le_refl _))
  rw [LRTyA_eq] at hRt
  exact tyKA_whnf hRt

/-- a spine's head is never an application. -/
theorem appsSpineA_fst_not_app : (e : ExprA) → ∀ f x, (appsSpineA e).1 ≠ .app f x
  | .app f' _, f, x => appsSpineA_fst_not_app f' f x
  | .bvar _, _, _ => fun h => ExprA.noConfusion h
  | .sort _, _, _ => fun h => ExprA.noConfusion h
  | .const _ _, _, _ => fun h => ExprA.noConfusion h
  | .lam _ _ _, _, _ => fun h => ExprA.noConfusion h
  | .pi _ _ _ _, _, _ => fun h => ExprA.noConfusion h
  | .letE _ _ _, _, _ => fun h => ExprA.noConfusion h
  | .lit _, _, _ => fun h => ExprA.noConfusion h

/-- a normal spine is its head alone, or its head is normal and not a λ. -/
theorem hStepFnA_foldApps_none (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (h : ExprA)
    (xs : List ExprA) : hStepFnA E iota Γ (foldAppsA h xs) = none →
      xs = [] ∨ (hStepFnA E iota Γ h = none ∧ ∀ A u b, h ≠ .lam A u b) := by
  refine snocInduction (P := fun xs => hStepFnA E iota Γ (foldAppsA h xs) = none →
      xs = [] ∨ (hStepFnA E iota Γ h = none ∧ ∀ A u b, h ≠ .lam A u b))
    (fun _ => Or.inl rfl) ?_ xs
  intro ys x ih hn
  rw [foldAppsA_append] at hn
  simp only [foldAppsA] at hn
  rcases lamA_or_not (foldAppsA h ys) with ⟨A, u, b, hl⟩ | hnl
  · rw [hl, hStepFnA_app_lam] at hn
    exact Option.noConfusion hn
  · obtain ⟨hF, _⟩ := hStepFnA_app_none_inv E iota Γ hnl hn
    rcases ih hF with e | hr
    · subst e
      exact Or.inr ⟨hF, hnl⟩
    · exact Or.inr hr

/-- sort uniqueness at a normal type: its spine head is a variable, a constant, a sort or a pi
    (a λ alone is no type — a pi is not convertible to a sort; a λ applied, a let and a literal
    step), all canonical, and the spine walk relates the two sorts. -/
theorem sortUniqA_normal (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {X : ExprA} (hn : hStepFnA E I.fn Γ X = none) {a b : Level}
    (ha : HasTyA E I n Γ X (.sort a)) (hb : HasTyA E I n Γ X (.sort b)) : eqN a b := by
  have hsp := foldAppsA_appsSpineA X
  have hna := appsSpineA_fst_not_app X
  rw [← hsp] at ha hb hn
  generalize (appsSpineA X).1 = H at ha hb hn hna
  generalize (appsSpineA X).2 = xs at ha hb hn
  have hLa : LargeA E I n Γ (.sort a) := Or.inl ⟨a, ⟨.refl _ _⟩⟩
  have canon : HeadCanonA E I n Γ H → eqN a b := fun hh => by
    obtain ⟨t⟩ := spine_tyConv hE hI hIS hEN hNC hR hS hρ hΓ hh xs ha hb hLa
    exact tyConvA_sorts_eqN hE hI hIS hEN hNC hR hS hρ hΓ t
  have hshape := hStepFnA_foldApps_none E I.fn Γ H xs hn
  cases H with
  | bvar i => exact canon (headCanonA_bvar Γ i)
  | sort l => exact canon (headCanonA_sort Γ l)
  | const r ls => exact canon (headCanonA_const Γ r ls)
  | app f x => exact absurd rfl (hna f x)
  | pi D u C v => exact canon (headCanonA_pi Γ D u C v)
  | lam A u body =>
      rcases hshape with e | ⟨_, hnl⟩
      · subst e
        simp only [foldAppsA] at ha
        obtain ⟨_, _, _, _, _, ⟨t⟩⟩ := hasTyA_lam_gen ha
        exact (tyConvA_pi_sort_false hE hI hIS hEN hNC hR hS hρ hΓ t).elim
      · exact absurd rfl (hnl A u body)
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

/-- sort uniqueness along a typed weak-head chain to a normal form: subject reduction at each sort
    (a sort is large) moves both typings down the chain. -/
theorem sortUniqA_chain (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) :
    {X N : ExprA} → WhTyChainA E I n Γ X N → hStepFnA E I.fn Γ N = none →
      ∀ {a b : Level}, HasTyA E I n Γ X (.sort a) → HasTyA E I n Γ X (.sort b) → eqN a b
  | _, _, .refl _ _ _ _, hN, _, _, ha, hb => sortUniqA_normal hE hI hIS hEN hNC hR hS hρ hΓ hN ha hb
  | _, _, .cons _ _ _ _ _ _ hs t, hN, a, b, ha, hb => by
      obtain ⟨ha'⟩ := tyHRedA_sr_large hE hI hIS hEN hNC hR hS hρ hΓ hs ha (Or.inl ⟨a, ⟨.refl _ _⟩⟩)
      obtain ⟨hb'⟩ := tyHRedA_sr_large hE hI hIS hEN hNC hR hS hρ hΓ hs hb (Or.inl ⟨b, ⟨.refl _ _⟩⟩)
      exact sortUniqA_chain hE hI hIS hEN hNC hR hS hρ hΓ t hN ha' hb'

/-- SORT UNIQUENESS (M3-a1): a type's sorts are `=ₙ`. -/
theorem sortUniqA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {X : ExprA} {a b : Level} (ha : HasTyA E I n Γ X (.sort a))
    (hb : HasTyA E I n Γ X (.sort b)) : eqN a b := by
  obtain ⟨N, ⟨c⟩, hN⟩ := hasTyA_sort_whnf hE hI hIS hEN hNC hR hS hρ hΓ ha
  exact sortUniqA_chain hE hI hIS hEN hNC hR hS hρ hΓ c hN ha hb

end SortUniq

/-! ## (8) chain collapse -/

section Collapse
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem eqNA_imax {u u' v v' : Level} (hu : eqN u u') (hv : eqN v v') :
    eqN (.imax u v) (.imax u' v') := by
  intro ρ
  simp only [eval, hu ρ, hv ρ]

/-- a conversion at a sort, moved to an `=ₙ` sort. -/
def convA_sort_eqN {Γ : LCtxA} {a b : ExprA} {u l : Level} (h : ConvA E I n Γ a b (.sort u))
    (hul : eqN u l) : ConvA E I n Γ a b (.sort l) :=
  .tyConv Γ a b (.sort u) (.sort l) (.succ u) (.succ l) (.succ u) h (.sort Γ u) (eqNA_refl _)
    (.sort Γ l) (eqNA_succ (eqNA_symm hul)) (.sorts Γ u l hul)

/-- CHAIN COLLAPSE: a type conversion chain out of a type of sort `l` is ONE conversion at `sort l`.
    Each piece converts at a sort `=ₙ` to its left end's, which sort uniqueness identifies with `l`;
    the middle of a `trans` is typed at `sort l` by the first half's conversion. -/
def tyConvA_collapse (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) :
    {A B : ExprA} → TyConvA E I n Γ A B → {l : Level} → HasTyA E I n Γ A (.sort l) →
      ConvA E I n Γ A B (.sort l)
  | _, _, .refl _ A, _, hA => .refl Γ A _ hA
  | _, _, .of _ _ _ _ _ _ hAl₀ hlu _ _ h, _, hA =>
      convA_sort_eqN h (eqNA_trans (eqNA_symm hlu)
        (eqNA_symm (sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ hA hAl₀)))
  | _, _, .trans _ A B C h1 h2, _, hA =>
      let c1 := tyConvA_collapse hE hI hIS hEN hNC hR hS hρ hΓ h1 hA
      .trans Γ A B C _ c1
        (tyConvA_collapse hE hI hIS hEN hNC hR hS hρ hΓ h2 (convA_hasTy_right hE hI hR hIS hΓ c1))

end Collapse

/-! ## (9) DT-012 on the copy: type uniqueness up to convertibility -/

section Uniq
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a conversion under an assumption, instantiated at an argument. -/
def convA_inst0 (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A t a b T : ExprA}
    (h : ConvA E I n (.assumption A :: Γ) a b T) (ht : HasTyA E I n Γ t A) :
    ConvA E I n Γ (instantiate0A t a) (instantiate0A t b) (instantiate0A t T) := by
  have hsub := convA_substA hE hI (iotaRecHeadTypedA_of hR) hIS (substTyA_cons_id hE hI hΓ ht) h
  rw [substA_cons_id_instantiate0, substA_cons_id_instantiate0,
    substA_cons_id_instantiate0] at hsub
  exact hsub

/-- a conversion under a let binder, instantiated at its value. -/
def convA_inst0Let (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A v a b T : ExprA}
    (h : ConvA E I n (.letBinding A v :: Γ) a b T) (hv : HasTyA E I n Γ v A) :
    ConvA E I n Γ (instantiate0A v a) (instantiate0A v b) (instantiate0A v T) := by
  have hsub := convA_substA hE hI (iotaRecHeadTypedA_of hR) hIS (substTyA_cons_id_let hE hI hΓ hv) h
  rw [substA_cons_id_instantiate0, substA_cons_id_instantiate0,
    substA_cons_id_instantiate0] at hsub
  exact hsub

/-- a type conversion under an assumption, instantiated at an argument. -/
def tyConvA_inst0 (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A t : ExprA}
    (ht : HasTyA E I n Γ t A) : {B B' : ExprA} → TyConvA E I n (.assumption A :: Γ) B B' →
      TyConvA E I n Γ (instantiate0A t B) (instantiate0A t B')
  | _, _, .refl _ _ => .refl _ _
  | _, _, .of _ _ _ l l' u hBl hlu hB'l hl'u h =>
      .of Γ _ _ l l' u (hasTyA_inst0' hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hBl ht) hlu
        (hasTyA_inst0' hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hB'l ht) hl'u (convA_inst0 hE hI hR hIS hΓ h ht)
  | _, _, .trans _ _ _ _ h1 h2 =>
      .trans _ _ _ _ (tyConvA_inst0 hE hI hR hIS hΓ ht h1) (tyConvA_inst0 hE hI hR hIS hΓ ht h2)

/-- a type conversion under a let binder, instantiated at its value. -/
def tyConvA_inst0Let (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A v : ExprA}
    (hv : HasTyA E I n Γ v A) : {B B' : ExprA} → TyConvA E I n (.letBinding A v :: Γ) B B' →
      TyConvA E I n Γ (instantiate0A v B) (instantiate0A v B')
  | _, _, .refl _ _ => .refl _ _
  | _, _, .of _ _ _ l l' u hBl hlu hB'l hl'u h =>
      .of Γ _ _ l l' u (hasTyA_inst0Let hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hBl hv) hlu
        (hasTyA_inst0Let hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hB'l hv) hl'u (convA_inst0Let hE hI hR hIS hΓ h hv)
  | _, _, .trans _ _ _ _ h1 h2 =>
      .trans _ _ _ _ (tyConvA_inst0Let hE hI hR hIS hΓ hv h1)
        (tyConvA_inst0Let hE hI hR hIS hΓ hv h2)

/-- DT-012 ON THE COPY (M3-a3) — TYPE UNIQUENESS up to convertibility: two types of one term are
    convertible. By recursion on the first derivation, the second generated at the same head:
    variables, constants, sorts and pis are canonical; a λ's codomains are convertible by recursion,
    the chain collapses at the first codomain's sort, and sort uniqueness makes the two codomain
    sorts `=ₙ`, so the pis are congruent; an application's function types are convertible by
    recursion, collapse to one conversion, and `PiConvInj` at any codomain (M2-g′) gives the
    codomains under the domain, instantiated at the argument; a let instantiates the body's at the
    value; a literal and a `conv` recurse. -/
theorem hasTyA_uniq (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) :
    {Γ : LCtxA} → CtxWfA E I n Γ → {e T : ExprA} → HasTyA E I n Γ e T →
      ∀ {T' : ExprA}, HasTyA E I n Γ e T' → Nonempty (TyConvA E I n Γ T T')
  | _, _, _, _, .sort _ _, _, h₂ => ⟨hasTyA_sort_gen h₂⟩
  | _, _, _, _, .bvar _ _ _ _ hl _, _, h₂ => by
      obtain ⟨A', hA', ⟨t⟩⟩ := hasTyA_bvar_gen h₂
      rw [hl] at hA'
      cases hA'
      exact ⟨t⟩
  | _, _, _, _, .const _ _ _ _ _ hres _ _ _, _, h₂ => by
      obtain ⟨m', hm', ⟨t⟩⟩ := hasTyA_const_gen h₂
      rw [hres] at hm'
      cases hm'
      exact ⟨t⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _, _, h₂ => ⟨hasTyA_pi_sort h₂⟩
  | Γ, hΓ, _, _, .lam _ A u _ B v hA hB hb, _, h₂ => by
      obtain ⟨B₂, v₂, _, ⟨hB₂⟩, ⟨hb₂⟩, ⟨t⟩⟩ := hasTyA_lam_gen h₂
      have hΓA : CtxWfA E I n (.assumption A :: Γ) := .assumption hΓ hA
      obtain ⟨tB⟩ := hasTyA_uniq hE hI hIS hEN hNC hR hS hρ hΓA hb hb₂
      have cB : ConvA E I n (.assumption A :: Γ) B B₂ (.sort v) :=
        tyConvA_collapse hE hI hIS hEN hNC hR hS hρ hΓA tB hB
      have hv : eqN v v₂ :=
        sortUniqA hE hI hIS hEN hNC hR hS hρ hΓA (convA_hasTy_right hE hI hR hIS hΓA cB) hB₂
      have heq : eqN (.imax u v₂) (.imax u v) := eqNA_imax (eqNA_refl u) (eqNA_symm hv)
      have hpi₂ : HasTyA E I n Γ (.pi A u B₂ v₂) (.sort (.imax u v)) :=
        .conv Γ _ _ _ _ _ (.pi Γ A u B₂ v₂ hA hB₂) (.sort Γ _) (eqNA_succ heq) (.sort Γ _)
          (convA_sort_eqN (.sorts Γ _ _ heq) (eqNA_succ heq))
      have cpi : ConvA E I n Γ (.pi A u B v) (.pi A u B₂ v₂) (.sort (.imax u v)) :=
        .pi Γ A A B B₂ u u v v₂ (eqNA_refl u) hv (.refl Γ A _ hA) cB hpi₂
      exact ⟨.trans _ _ _ _ (.of Γ _ _ _ _ _ (.pi Γ A u B v hA hB) (eqNA_refl _) hpi₂ (eqNA_refl _)
        cpi) t⟩
  | _, hΓ, _, _, .app _ _ _ _ _ _ _ _ _ _ hf ha, _, h₂ => by
      obtain ⟨_, _, _, _, _, ⟨hf₂⟩, _, _, _, ⟨t⟩⟩ := hasTyA_app_gen h₂
      obtain ⟨tf⟩ := hasTyA_uniq hE hI hIS hEN hNC hR hS hρ hΓ hf hf₂
      obtain ⟨_, hs⟩ := hasTyA_regular hE hI hR hIS hΓ hf
      have cf := tyConvA_collapse hE hI hIS hEN hNC hR hS hρ hΓ tf hs
      obtain ⟨_, _, _, ⟨tB⟩⟩ := piConvInjA hE hI hIS hEN hNC hR hS hρ hΓ cf
      exact ⟨.trans _ _ _ _ (tyConvA_inst0 hE hI hR hIS hΓ ha tB) t⟩
  | Γ, hΓ, _, _, .letE _ A _ _ _ _ _ hA hv _ hb, _, h₂ => by
      obtain ⟨_, _, _, _, _, _, ⟨hb₂⟩, ⟨t⟩⟩ := hasTyA_letE_gen h₂
      have hΓv : CtxWfA E I n (.letBinding A _ :: Γ) := .letBinding hΓ hA hv
      obtain ⟨tB⟩ := hasTyA_uniq hE hI hIS hEN hNC hR hS hρ hΓv hb hb₂
      exact ⟨.trans _ _ _ _ (tyConvA_inst0Let hE hI hR hIS hΓ hv tB) t⟩
  | _, hΓ, _, _, .lit _ _ _ hexp, _, h₂ => hasTyA_uniq hE hI hIS hEN hNC hR hS hρ hΓ hexp (hasTyA_lit_gen h₂)
  | Γ, hΓ, _, _, .conv _ _ A B l u h hAl hlu hB hc, _, h₂ => by
      obtain ⟨t⟩ := hasTyA_uniq hE hI hIS hEN hNC hR hS hρ hΓ h h₂
      exact ⟨.trans _ _ _ _ (TyConvA.of Γ A B l u u hAl hlu hB (eqNA_refl u) hc).symm t⟩

end Uniq

/-! ## (10) at the concrete ι, from the environment's well-formedness under the profile -/

section Rec
variable {E : ResolvedEnvA} {n : Nat}

/-- sort uniqueness at the concrete ι: the semantic hypotheses from `EnvWfA` under the profile
    (`envSemA_of_envWfA_recStruct`), the height valuation `fun _ => 1`. -/
theorem sortUniqA_rec (hW : EnvWfA (iotaIfaceA E) E) (hS : SmallIndexProfileA E)
    (hPE : PropElimStructA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) {X : ExprA}
    {a b : Level} (ha : HasTyA E (iotaIfaceA E) n Γ X (.sort a))
    (hb : HasTyA E (iotaIfaceA E) n Γ X (.sort b)) : eqN a b :=
  sortUniqA (envWfA_closed hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW))
    (envWfA_normCtorType hW) (envWfA_normClosed hW) (iotaFnA_recHead E)
    (envSemA_of_envWfA_recStruct (ρ₀ := fun _ => 1) hW posValA_one hS hPE)
    posValA_one hΓ ha hb

/-- DT-012 at the concrete ι, under the profile. -/
theorem hasTyA_uniq_rec (hW : EnvWfA (iotaIfaceA E) E) (hS : SmallIndexProfileA E)
    (hPE : PropElimStructA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) {e T T' : ExprA}
    (h₁ : HasTyA E (iotaIfaceA E) n Γ e T) (h₂ : HasTyA E (iotaIfaceA E) n Γ e T') :
    Nonempty (TyConvA E (iotaIfaceA E) n Γ T T') :=
  hasTyA_uniq (envWfA_closed hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW))
    (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW)) (envWfA_normCtorType hW)
    (envWfA_normClosed hW) (iotaFnA_recHead E)
    (envSemA_of_envWfA_recStruct (ρ₀ := fun _ => 1) hW posValA_one hS hPE) posValA_one hΓ h₁ h₂

end Rec

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.tyConvA_pi_inj
#print axioms Rcic.Declarative.Ann.spine_tyConv
#print axioms Rcic.Declarative.Ann.tyHRedA_sr_large
#print axioms Rcic.Declarative.Ann.sortUniqA
#print axioms Rcic.Declarative.Ann.tyConvA_collapse
#print axioms Rcic.Declarative.Ann.hasTyA_uniq
#print axioms Rcic.Declarative.Ann.sortUniqA_rec
#print axioms Rcic.Declarative.Ann.hasTyA_uniq_rec
