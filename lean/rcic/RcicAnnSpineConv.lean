import rcic.RcicAnnSubstTy

/-!
# M2-f (6a-ii) — spine congruence, on the copy

`ConvArgsA` is a pointwise conversion along a telescope (`RcicAnnFam`).
`convA_spine` turns that, plus a conversion of the heads at the telescope,
into a conversion of the two applications, at the instance `applyTelA` reaches.

The three typing corollaries are identity substitution
(`hasTyA_type_subst` / `convA_left_subst` / `convA_right_subst` of `substTyA_id`,
then `substA_id`). All four environment premises are consumed: the identity
needs `EnvClosedA` and `IotaLiftA`, and those three lemmas need `IotaRecHeadA`
and `IotaSubstA`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section SpineConv
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def hasTyA_regular (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {e A : ExprA}
    (h : HasTyA E I n Γ e A) : Σ u : Level, HasTyA E I n Γ A (.sort u) := by
  have h' := hasTyA_type_subst hE hI (iotaRecHeadTypedA_of hR) hIS (substTyA_id hE hI hΓ) h
  rw [substA_id] at h'
  exact h'

def convA_hasTy_left (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {a b A : ExprA}
    (h : ConvA E I n Γ a b A) : HasTyA E I n Γ a A := by
  have h' := convA_left_subst hE hI (iotaRecHeadTypedA_of hR) hIS (substTyA_id hE hI hΓ) h
  rw [substA_id, substA_id] at h'
  exact h'

def convA_hasTy_right (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {a b A : ExprA}
    (h : ConvA E I n Γ a b A) : HasTyA E I n Γ b A := by
  have h' := convA_right_subst hE hI (iotaRecHeadTypedA_of hR) hIS (substTyA_id hE hI hΓ) h
  rw [substA_id, substA_id] at h'
  exact h'

theorem convA_spine (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) :
    ∀ {T : ExprA} {xs ys : List ExprA}, ConvArgsA E I n Γ T xs ys →
    ∀ {f g : ExprA}, Nonempty (ConvA E I n Γ f g T) →
      ∀ (U : ExprA), applyTelA xs T = some U →
        Nonempty (ConvA E I n Γ (foldAppsA f xs) (foldAppsA g ys) U)
  | _, _, _, .nil _, _, _, hfg, _, hU => by
      injection hU with hU
      subst hU
      simpa [foldAppsA] using hfg
  | _, _, _, .cons A u B v x y xs ys hx hs, f, g, hfg, U, hU => by
      have hApps : Nonempty (ConvA E I n Γ (.app f x) (.app g y) (instantiate0A x B)) :=
        hfg.elim fun h1 => hx.elim fun h2 => by
          have hf : HasTyA E I n Γ f (.pi A u B v) :=
            convA_hasTy_left hE hI hR hIS hΓ h1
          have hg : HasTyA E I n Γ g (.pi A u B v) :=
            convA_hasTy_right hE hI hR hIS hΓ h1
          have hxTy : HasTyA E I n Γ x A := convA_hasTy_left hE hI hR hIS hΓ h2
          have hy : HasTyA E I n Γ y A := convA_hasTy_right hE hI hR hIS hΓ h2
          have parts := hasTyA_pi_parts (hasTyA_regular hE hI hR hIS hΓ hf).2
          have hA : HasTyA E I n Γ A (.sort u) := parts.1
          have hB : HasTyA E I n (.assumption A :: Γ) B (.sort v) := parts.2
          have hTyY : HasTyA E I n Γ (instantiate0A y B) (.sort v) :=
            hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hB hy hA
          have hApp : HasTyA E I n Γ (.app g y) (instantiate0A y B) :=
            .app Γ g y A B u v v hB hTyY hg hy
          have hTyX : HasTyA E I n Γ (instantiate0A x B) (.sort v) :=
            hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hB hxTy hA
          have hc : ConvA E I n Γ (instantiate0A y B) (instantiate0A x B) (.sort v) :=
            .symm Γ (instantiate0A x B) (instantiate0A y B) (.sort v)
              (hasTyA_func0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hB h2 hA)
          have hOf : TyConvA E I n Γ (instantiate0A y B) (instantiate0A x B) :=
            .of Γ (instantiate0A y B) (instantiate0A x B) v v v
              hTyY (eqNA_refl v) hTyX (eqNA_refl v) hc
          exact ⟨.app Γ f g x y A B u v h1 h2 hB (hasTyA_of_tyConvA hApp hOf)⟩
      exact convA_spine hE hI hR hIS hΓ hs hApps U hU

/-! ## W-1 (c): substitutions over proof binders

A typed substitution extended by a typed image (`substTyA_cons`), read off a context's tail
(`substTyA_tail`), and pushed under target binders (`substTyA_wk1`, `substTyA_liftN`, the images
lifted by `liftNA`). Two typed substitutions that agree on a context's variables above a run of PROOF
binders — assumptions typed at a sort `=ₙ` zero (`PropExtA`) — are convertible
(`convSubstA_propExtA`): at each proof binder `irr` relates the two images at the left's type, the
right's retyped there by functionality on the binders below it. -/

/-- `m`-fold weakening at cutoff `0`, one binder at a time. -/
def liftNA : Nat → ExprA → ExprA
  | 0, e => e
  | m + 1, e => liftA 0 1 (liftNA m e)

theorem liftNA_add (a b : Nat) (e : ExprA) : liftNA a (liftNA b e) = liftNA (b + a) e := by
  induction a with
  | zero => rfl
  | succ a ih => show liftA 0 1 (liftNA a (liftNA b e)) = liftA 0 1 (liftNA (b + a) e); rw [ih]

theorem liftNA_substA (σ : SubstA) (e : ExprA) :
    (m : Nat) → liftNA m (substA σ e) = substA (fun i => liftNA m (σ i)) e
  | 0 => rfl
  | m + 1 => by
      show liftA 0 1 (liftNA m (substA σ e)) = _
      rw [liftNA_substA σ e m, liftA_substA]
      rfl

/-- an image for an assumption's variable, typed at the assumption's type under the substitution. -/
def substTyA_cons {Δ Γ : LCtxA} {σ : SubstA} {t A : ExprA} (hσ : SubstTyA E I n Δ σ Γ)
    (ht : HasTyA E I n Δ t (substA σ A)) :
    SubstTyA E I n Δ (SubstA.cons t σ) (.assumption A :: Γ) where
  ty := fun i B hlu => by
    cases i with
    | zero =>
        have hB : B = liftA 0 1 A := lookupTypeA_zero_assumption_eq hlu
        subst hB
        rw [SubstA.cons_zero, substA_cons_liftA]
        exact ht
    | succ i =>
        let s := liftedTypeA (.assumption A) Γ hlu
        have hEq : B = liftA 0 1 s.orig := s.eq_lift
        rw [hEq, SubstA.cons_succ, substA_cons_liftA]
        exact hσ.ty i s.orig s.got
  val := fun i B v hty hval => by
    cases i with
    | zero => exact (lookupValueA_zero_assumption_none hval).elim
    | succ i =>
        let sB := liftedTypeA (.assumption A) Γ hty
        let sv := liftedValueA (.assumption A) Γ hval
        have hB : B = liftA 0 1 sB.orig := sB.eq_lift
        have hv : v = liftA 0 1 sv.orig := sv.eq_lift
        rw [hB, hv, SubstA.cons_succ, substA_cons_liftA, substA_cons_liftA]
        exact hσ.val i sB.orig sv.orig sB.got sv.got

/-- the substitution read off a context's tail. -/
def substTyA_tail {Δ Γ : LCtxA} {σ : SubstA} {d : LocalDeclA} (hσ : SubstTyA E I n Δ σ (d :: Γ)) :
    SubstTyA E I n Δ (fun i => σ (i + 1)) Γ where
  ty := fun i B h => by
    have h' : lookupTypeA (d :: Γ) (i + 1) = some (liftA 0 1 B) := by
      rw [lookupTypeA_cons_succ, h]; rfl
    have ht := hσ.ty (i + 1) (liftA 0 1 B) h'
    rw [substA_liftA_succ] at ht
    exact ht
  val := fun i B v hB hv => by
    have h' : lookupTypeA (d :: Γ) (i + 1) = some (liftA 0 1 B) := by
      rw [lookupTypeA_cons_succ, hB]; rfl
    have hv' : lookupValueA (d :: Γ) (i + 1) = some (liftA 0 1 v) := by
      rw [lookupValueA_cons_succ, hv]; rfl
    have hc := hσ.val (i + 1) (liftA 0 1 B) (liftA 0 1 v) h' hv'
    rw [substA_liftA_succ, substA_liftA_succ] at hc
    exact hc

/-- a typed substitution into `Δ` is one into `d :: Δ`, its images lifted. -/
def substTyA_wk1 (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E I n Δ σ Γ) (d : LocalDeclA) :
    SubstTyA E I n (d :: Δ) (fun i => liftA 0 1 (σ i)) Γ where
  ty := fun i A h => by
    have hw := hasTyWeakenA hE hI d (Nat.zero_le _) (hσ.ty i A h)
    rw [liftA_substA] at hw
    exact hw
  val := fun i A v hA hv => by
    have hw := convWeakenA hE hI d (Nat.zero_le _) (hσ.val i A v hA hv)
    rw [liftA_substA, liftA_substA] at hw
    exact hw

/-- a typed substitution into `Δ` is one into `ds ++ Δ`, its images lifted by `ds.length`. -/
def substTyA_liftN (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E I n Δ σ Γ) :
    (ds : List LocalDeclA) → SubstTyA E I n (ds ++ Δ) (fun i => liftNA ds.length (σ i)) Γ
  | [] => hσ
  | d :: ds => substTyA_wk1 hE hI (substTyA_liftN hE hI hσ ds) d

/-- `Γ` is `Θ` under `m` PROOF binders: assumptions, each typed in the context below it at a sort
    `=ₙ` zero. -/
inductive PropExtA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Θ : LCtxA) : LCtxA → Nat → Type
  | base : PropExtA E I n Θ Θ 0
  | cons {Γ : LCtxA} {m : Nat} {D : ExprA} {u : Level} (tl : PropExtA E I n Θ Γ m)
      (hD : HasTyA E I n Γ D (.sort u)) (hz : eqN u .zero) :
      PropExtA E I n Θ (.assumption D :: Γ) (m + 1)

/-- PROOF BINDERS ARE IRRELEVANT TO A SUBSTITUTION: two typed substitutions into `Δ` that agree on
    every variable of `Γ` above its `m` proof binders are convertible — on each proof binder, `irr` at
    the left's image's type, the right's image retyped there by functionality on the binders below. -/
def convSubstA_propExtA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Δ Θ : LCtxA} :
    {Γ : LCtxA} → {m : Nat} → PropExtA E I n Θ Γ m → {σ σ' : SubstA} →
    SubstTyA E I n Δ σ Γ → SubstTyA E I n Δ σ' Γ →
    (∀ i A, m ≤ i → lookupTypeA Γ i = some A → σ i = σ' i) →
    ConvSubstA E I n Δ σ σ' Γ
  | _, _, .base, _, _, hσ, hσ', hag =>
      { left := hσ, right := hσ',
        conv := fun i A h => by
          rw [← hag i A (Nat.zero_le i) h]
          exact .refl _ _ _ (hσ.ty i A h) }
  | _, _, .cons (Γ := Γ) (D := D) (u := u) tl hD hz, σ, σ', hσ, hσ', hag =>
      have htl : ConvSubstA E I n Δ (fun i => σ (i + 1)) (fun i => σ' (i + 1)) Γ :=
        convSubstA_propExtA hE hI hR hIS tl (substTyA_tail hσ) (substTyA_tail hσ')
          (fun i A hi h => hag (i + 1) (liftA 0 1 A) (Nat.succ_le_succ hi)
            (by rw [lookupTypeA_cons_succ, h]; rfl))
      { left := hσ, right := hσ',
        conv := fun i B hlu => by
          cases i with
          | zero =>
              have hB : B = liftA 0 1 D := lookupTypeA_zero_assumption_eq hlu
              subst hB
              have t0 := hσ.ty 0 (liftA 0 1 D) hlu
              have t0' := hσ'.ty 0 (liftA 0 1 D) hlu
              rw [substA_liftA_succ] at t0 t0'
              have hDτ : HasTyA E I n Δ (substA (fun i => σ (i + 1)) D) (.sort u) :=
                hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS htl.left hD
              have hDτ' : HasTyA E I n Δ (substA (fun i => σ' (i + 1)) D) (.sort u) :=
                hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS htl.right hD
              have hc : ConvA E I n Δ (substA (fun i => σ (i + 1)) D) (substA (fun i => σ' (i + 1)) D)
                  (.sort u) := hasTyA_func hE hI (iotaRecHeadTypedA_of hR) hIS htl hD
              have t0'' : HasTyA E I n Δ (σ' 0) (substA (fun i => σ (i + 1)) D) :=
                .conv _ _ _ _ u u t0' hDτ' (eqNA_refl u) hDτ (.symm _ _ _ _ hc)
              rw [substA_liftA_succ]
              exact .irr _ _ _ _ (hasTyA_retype_sort hDτ hz) t0 t0''
          | succ i =>
              let s := liftedTypeA (.assumption D) Γ hlu
              have hEq : B = liftA 0 1 s.orig := s.eq_lift
              rw [hEq, substA_liftA_succ]
              exact htl.conv i s.orig s.got }

end SpineConv

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.hasTyA_regular
#print axioms Rcic.Declarative.Ann.convA_hasTy_left
#print axioms Rcic.Declarative.Ann.convA_hasTy_right
#print axioms Rcic.Declarative.Ann.convA_spine
#print axioms Rcic.Declarative.Ann.liftNA_add
#print axioms Rcic.Declarative.Ann.liftNA_substA
#print axioms Rcic.Declarative.Ann.substTyA_cons
#print axioms Rcic.Declarative.Ann.substTyA_tail
#print axioms Rcic.Declarative.Ann.substTyA_wk1
#print axioms Rcic.Declarative.Ann.substTyA_liftN
#print axioms Rcic.Declarative.Ann.convSubstA_propExtA
