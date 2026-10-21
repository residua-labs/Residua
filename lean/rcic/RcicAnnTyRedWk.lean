import rcic.RcicAnnTyRed

/-!
# M1-d (iv) b — typed head reduction and type conversion weaken

`TyConvA`, `TyHRedA` and `WhTyChainA` under one insertion (every premise is a
judgment, so each arm is `RcicAnnWeaken`'s weakening of its premises; ι rides
on `IotaLiftA` + `hStepFnA_liftA` as in `convWeakenA`), then along a
`WkSpecA`. These are the base data of the relation's clauses, so they are what
`RcicAnnLRWk` weakens the relation with.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section One
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def tyConvA_weaken (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) :
    {c : Nat} → {Γ : LCtxA} → c ≤ Γ.length → {A B : ExprA} →
    TyConvA E I n Γ A B → TyConvA E I n (insertAtA d c Γ) (liftA c 1 A) (liftA c 1 B)
  | _, _, _, _, _, .refl _ _ => .refl _ _
  | _, _, hc, _, _, .of _ _ _ l l' u hAl hlu hBl hl'u h =>
      .of _ _ _ l l' u (hasTyWeakenA hE hI d hc hAl) hlu (hasTyWeakenA hE hI d hc hBl) hl'u
        (convWeakenA hE hI d hc h)
  | _, _, hc, _, _, .trans _ _ _ _ h1 h2 =>
      .trans _ _ _ _ (tyConvA_weaken hE hI d hc h1) (tyConvA_weaken hE hI d hc h2)

def tyHRedA_weaken (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) :
    {c : Nat} → {Γ : LCtxA} → c ≤ Γ.length → {a b A : ExprA} →
    TyHRedA E I n Γ a b A →
    TyHRedA E I n (insertAtA d c Γ) (liftA c 1 a) (liftA c 1 b) (liftA c 1 A)
  | c, Γ, hc, _, _, _, .beta _ A u body arg B hA hbody harg hred => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      have hred' := hasTyWeakenA hE hI d hc hred
      rw [liftA_instantiate0A, liftA_instantiate0A] at hred'
      show TyHRedA E I n (insertAtA d c Γ)
        (.app (.lam (liftA c 1 A) u (liftA (c + 1) 1 body)) (liftA c 1 arg))
        (liftA c 1 (instantiate0A arg body)) (liftA c 1 (instantiate0A arg B))
      rw [liftA_instantiate0A, liftA_instantiate0A]
      exact .beta _ _ u _ _ _ (hasTyWeakenA hE hI d hc hA)
        (hasTyWeakenA hE hI d (c := c + 1) hc' hbody) (hasTyWeakenA hE hI d hc harg) hred'
  | c, Γ, hc, _, _, _, .zeta _ A value body B u hA hv hb hred => by
      have hc' : c + 1 ≤ (LocalDeclA.letBinding A value :: Γ).length := Nat.succ_le_succ hc
      have hred' := hasTyWeakenA hE hI d hc hred
      rw [liftA_instantiate0A, liftA_instantiate0A] at hred'
      show TyHRedA E I n (insertAtA d c Γ)
        (.letE (liftA c 1 A) (liftA c 1 value) (liftA (c + 1) 1 body))
        (liftA c 1 (instantiate0A value body)) (liftA c 1 (instantiate0A value B))
      rw [liftA_instantiate0A, liftA_instantiate0A]
      exact .zeta _ _ _ _ _ u (hasTyWeakenA hE hI d hc hA) (hasTyWeakenA hE hI d hc hv)
        (hasTyWeakenA hE hI d (c := c + 1) hc' hb) hred'
  | c, Γ, hc, _, _, _, .zetaLocal _ i A v hval hty hv => by
      rw [liftA_bvar]
      have hval' := lookupValueA_insertAtA d c Γ hc i
      rw [hval, Option.map_some'] at hval'
      have hty' := lookupTypeA_insertAtA d c Γ hc i
      rw [hty, Option.map_some'] at hty'
      exact .zetaLocal _ _ _ _ hval' hty' (hasTyWeakenA hE hI d hc hv)
  | c, _, hc, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb => by
      have hcl1 : liftA c 1 (instantiateLevelsA ls b) = instantiateLevelsA ls b := by
        rw [← instantiateLevelsA_liftA, (hE r m hres).2 b hbody c]
      have hcl2 : liftA c 1 (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA := by
        rw [← instantiateLevelsA_liftA, (hE r m hres).1 c]
      have hb' := hasTyWeakenA hE hI d hc hb
      rw [hcl1, hcl2] at hb'
      show TyHRedA E I n (insertAtA d c _) (.const r ls) (liftA c 1 (instantiateLevelsA ls b))
        (liftA c 1 (instantiateLevelsA ls m.mtypeA))
      rw [hcl1, hcl2]
      exact .delta _ r ls m b hres hbody htr hlen hwf hb'
  | c, Γ, hc, _, _, _, .iota _ lhs rhs T h hlhs hrhs =>
      .iota _ _ _ _
        ⟨by simp only [hI c lhs, h.1, Option.map_some'],
         by simp only [hStepFnA_liftA hE hI d c Γ hc lhs, h.2, Option.map_some']⟩
        (hasTyWeakenA hE hI d hc hlhs) (hasTyWeakenA hE hI d hc hrhs)
  | c, _, hc, _, _, _, .lit _ t T hexp => by
      have hexp' := hasTyWeakenA hE hI d hc hexp
      rw [liftA_natExpandA] at hexp'
      show TyHRedA E I n (insertAtA d c _) (.lit t) (liftA c 1 (natExpandA t)) (liftA c 1 T)
      rw [liftA_natExpandA]
      exact .lit _ t _ hexp'
  | c, Γ, hc, _, _, _, .app _ f f' a A B T₀ u v w h hcv hB hTy ha => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      have hTy' := hasTyWeakenA hE hI d hc hTy
      rw [liftA_instantiate0A] at hTy'
      show TyHRedA E I n (insertAtA d c Γ) (.app (liftA c 1 f) (liftA c 1 a))
        (.app (liftA c 1 f') (liftA c 1 a)) (liftA c 1 (instantiate0A a B))
      rw [liftA_instantiate0A]
      exact .app _ _ _ _ _ _ _ u v w (tyHRedA_weaken hE hI d hc h) (tyConvA_weaken hE hI d hc hcv)
        (hasTyWeakenA hE hI d (c := c + 1) hc' hB) hTy' (hasTyWeakenA hE hI d hc ha)
  | _, _, hc, _, _, _, .conv _ _ _ _ _ h hcv =>
      .conv _ _ _ _ _ (tyHRedA_weaken hE hI d hc h) (tyConvA_weaken hE hI d hc hcv)
  | c, Γ, hc, _, _, _, .major _ f a a' A B T₀ u v hrec hu hs hf hi h hcv hfTy hB hrt => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      have hrt' := hasTyWeakenA hE hI d hc hrt
      rw [liftA_instantiate0A] at hrt'
      have hfn : I.fn (.app (liftA c 1 f) (liftA c 1 a)) = none := by
        have := hI c (.app f a)
        rw [hi] at this
        exact this
      show TyHRedA E I n (insertAtA d c Γ) (.app (liftA c 1 f) (liftA c 1 a))
        (.app (liftA c 1 f) (liftA c 1 a')) (liftA c 1 (instantiate0A a B))
      rw [liftA_instantiate0A]
      exact .major _ _ _ _ _ _ _ u v (by rw [recAtMajorA_liftA]; exact hrec)
        (by rw [unitMinorA_liftA, hu]; rfl) (by rw [structHeadA_liftA, hs])
        (by rw [hStepFnA_liftA hE hI d c Γ hc f, hf]; rfl) hfn
        (tyHRedA_weaken hE hI d hc h) (tyConvA_weaken hE hI d hc hcv)
        (hasTyWeakenA hE hI d hc hfTy) (hasTyWeakenA hE hI d (c := c + 1) hc' hB) hrt'

  | c, Γ, hc, _, _, _, .kunit _ f a mn T hrec hu hf hi hcv hrt => by
      have hfn : I.fn (.app (liftA c 1 f) (liftA c 1 a)) = none := by
        have := hI c (.app f a)
        rw [hi] at this
        exact this
      exact .kunit _ _ _ _ _ (by rw [recAtMajorA_liftA]; exact hrec)
        (by rw [unitMinorA_liftA, hu]; rfl)
        (by rw [hStepFnA_liftA hE hI d c Γ hc f, hf]; rfl) hfn
        (convWeakenA hE hI d hc hcv) (hasTyWeakenA hE hI d hc hrt)
  | c, Γ, hc, _, _, _, .kstruct _ f a e T hrec hs hf hcv hrt => by
      exact .kstruct _ _ _ _ _ (by rw [recAtMajorA_liftA]; exact hrec)
        (by rw [structArmA_liftA hE, hs]; rfl)
        (by rw [hStepFnA_liftA hE hI d c Γ hc f, hf]; rfl)
        (convWeakenA hE hI d hc hcv) (hasTyWeakenA hE hI d hc hrt)

def whTyChainA_weaken (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) :
    {c : Nat} → {Γ : LCtxA} → c ≤ Γ.length → {A N : ExprA} →
    WhTyChainA E I n Γ A N →
    WhTyChainA E I n (insertAtA d c Γ) (liftA c 1 A) (liftA c 1 N)
  | _, _, hc, _, _, .refl _ _ u h => .refl _ _ u (hasTyWeakenA hE hI d hc h)
  | _, _, hc, _, _, .cons _ _ _ _ u hA hs t =>
      .cons _ _ _ _ u (hasTyWeakenA hE hI d hc hA) (tyHRedA_weaken hE hI d hc hs)
        (whTyChainA_weaken hE hI d hc t)

end One

/-! ## along a weakening spec -/

section Spec
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def tyConvA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {A B : ExprA} →
    TyConvA E I n Γ A B → TyConvA E I n (wkCtxA ρ Γ) (wkExprA ρ A) (wkExprA ρ B)
  | _, [], _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, h =>
      tyConvA_wk hE hI (insertAtA d c Γ) ρ hρ (tyConvA_weaken hE hI d hc h)

/-- a closed type conversion transports to any context (`hasTyClosedWeakenA`'s `TyConvA` twin,
    R-NoDeltaRec-4d-iii). -/
def tyConvA_closedWeaken (hE : EnvClosedA E) (hI : IotaLiftA I) {A B : ExprA}
    (hclA : ∀ k, liftA k 1 A = A) (hclB : ∀ k, liftA k 1 B = B) :
    (Γ : LCtxA) → TyConvA E I n [] A B → TyConvA E I n Γ A B
  | [], h => h
  | d :: Γ, h => by
      have hw := tyConvA_weaken hE hI d (c := 0) (Nat.zero_le _)
        (tyConvA_closedWeaken hE hI hclA hclB Γ h)
      rw [hclA 0, hclB 0] at hw
      exact hw

/-- typed steps weaken along a spec (M2-b's `RcicAnnLRExp` device, placed here since
    M2-f (3a) so that `RcicAnnFamWk` reads it too). -/
def tyHRedA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {a b A : ExprA} →
    TyHRedA E I n Γ a b A → TyHRedA E I n (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) (wkExprA ρ A)
  | _, [], _, _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, _, h =>
      tyHRedA_wk hE hI (insertAtA d c Γ) ρ hρ (tyHRedA_weaken hE hI d hc h)

theorem tyConvA_wk_ne (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (ρ : WkSpecA)
    (hρ : WkSpecA.ok ρ Γ) {A B : ExprA} (h : Nonempty (TyConvA E I n Γ A B)) :
    Nonempty (TyConvA E I n (wkCtxA ρ Γ) (wkExprA ρ A) (wkExprA ρ B)) :=
  h.elim fun h => ⟨tyConvA_wk hE hI Γ ρ hρ h⟩

theorem whTyA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {A N : ExprA} →
    WhTyA E I n Γ A N → WhTyA E I n (wkCtxA ρ Γ) (wkExprA ρ A) (wkExprA ρ N)
  | _, [], _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, h =>
      whTyA_wk hE hI (insertAtA d c Γ) ρ hρ (h.elim fun t => ⟨whTyChainA_weaken hE hI d hc t⟩)

theorem hasTyA_wk_ne (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (ρ : WkSpecA)
    (hρ : WkSpecA.ok ρ Γ) {e A : ExprA} (h : Nonempty (HasTyA E I n Γ e A)) :
    Nonempty (HasTyA E I n (wkCtxA ρ Γ) (wkExprA ρ e) (wkExprA ρ A)) :=
  h.elim fun h => ⟨hasTyA_wk hE hI Γ ρ hρ h⟩

theorem convA_wk_ne (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (ρ : WkSpecA)
    (hρ : WkSpecA.ok ρ Γ) {a b A : ExprA} (h : Nonempty (ConvA E I n Γ a b A)) :
    Nonempty (ConvA E I n (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) (wkExprA ρ A)) :=
  h.elim fun h => ⟨convA_wk hE hI Γ ρ hρ h⟩

/-- normality is stable along a spec. -/
theorem hStepFnA_wk_none (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {e : ExprA} →
    hStepFnA E I.fn Γ e = none → hStepFnA E I.fn (wkCtxA ρ Γ) (wkExprA ρ e) = none
  | _, [], _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, e, h =>
      hStepFnA_wk_none hE hI (insertAtA d c Γ) ρ hρ (by rw [hStepFnA_liftA hE hI d c Γ hc e, h]; rfl)

/-! ## the spec under a binder -/

theorem wkDeclA_assumption : (σ : WkSpecA) → (D : ExprA) →
    wkDeclA σ (.assumption D) = .assumption (wkExprA σ D)
  | [], _ => rfl
  | (_, c) :: σ, D => wkDeclA_assumption σ (liftA c 1 D)

theorem wkCtxA_ub_cons : (σ : WkSpecA) → (x : LocalDeclA) → (Γ : LCtxA) →
    wkCtxA (WkSpecA.ub σ) (x :: Γ) = wkDeclA σ x :: wkCtxA σ Γ
  | [], _, _ => rfl
  | (d, c) :: σ, x, Γ => wkCtxA_ub_cons σ (liftDeclA c x) (insertAtA d c Γ)

theorem WkSpecA.ok_ub : (σ : WkSpecA) → (x : LocalDeclA) → (Γ : LCtxA) →
    WkSpecA.ok σ Γ → WkSpecA.ok (WkSpecA.ub σ) (x :: Γ)
  | [], _, _, _ => trivial
  | (d, c) :: σ, x, Γ, ⟨hc, hσ⟩ =>
      ⟨Nat.succ_le_succ hc, WkSpecA.ok_ub σ (liftDeclA c x) (insertAtA d c Γ) hσ⟩

/-- a binder typing weakens along a spec, the binder's declaration weakened with it. -/
theorem hasTyA_wk_ne_binder (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (σ : WkSpecA)
    (hσ : WkSpecA.ok σ Γ) {D C : ExprA} {v : Level}
    (h : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v))) :
    Nonempty (HasTyA E I n (.assumption (wkExprA σ D) :: wkCtxA σ Γ) (wkExprA (WkSpecA.ub σ) C) (.sort v)) := by
  have h' := hasTyA_wk_ne hE hI (WkSpecA.ub σ) (WkSpecA.ok_ub σ _ Γ hσ) h
  rw [wkCtxA_ub_cons, wkDeclA_assumption, wkExprA_sort] at h'
  exact h'

end Spec

#print axioms tyHRedA_weaken
#print axioms whTyChainA_weaken
#print axioms tyConvA_wk
#print axioms whTyA_wk
#print axioms hStepFnA_wk_none
#print axioms hasTyA_wk_ne_binder

end Rcic.Declarative.Ann
