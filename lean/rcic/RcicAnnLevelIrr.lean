import rcic.RcicAnnCtxConv

/-!
# M2-e (8) — level irrelevance: two `=ₙ` instantiations of one typed term are convertible

    convA_levelIrr : eqNList ls ls' → CtxConvA (instCtxA ls' Γ) (instCtxA ls Γ) → HasTyA E I a Γ e A →
      Nonempty (ConvA E I n (instCtxA ls Γ) (instantiateLevelsA ls e) (instantiateLevelsA ls' e) (instantiateLevelsA ls A))

by induction on the typing derivation: `sort` by `sorts`, `const` by `consts`
(the right constant typed at the LEFT's instantiated type through `conv`, with the
induction hypothesis on the member's type), `pi`/`lam` by R-TypedRules (6)'s
congruences at `instLevel ls u =ₙ instLevel ls' u`, `app`/`letE` by the
congruences with the right side retyped along the induction hypothesis on the
type, `bvar`/`lit` by reflexivity, `conv` by `tyConv` with the instantiated
conversion. The right components are typed in the LEFT's instantiated context by
instantiating at `ls'` (`hasTyA_instLevels`) and converting the context
(`hasTyA_ctxConv`); the context conversion is extended under a binder by the
induction hypothesis on the binder's type, and built for a well-formed context by
the same lemma on its declarations (`ctxConvA_instLevels`, `convA_levelIrr_wf`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Irr
variable {E : ResolvedEnvA} {I : IotaIfaceA}

/-- a closed conversion at the empty context holds in every context. -/
def convA_closedWeakenA {n : Nat} (hE : EnvClosedA E) (hI : IotaLiftA I) {a b A : ExprA}
    (hcla : ∀ k, liftA k 1 a = a) (hclb : ∀ k, liftA k 1 b = b) (hclA : ∀ k, liftA k 1 A = A) :
    (Γ : LCtxA) → ConvA E I n [] a b A → ConvA E I n Γ a b A
  | [], h => h
  | d :: Γ, h => by
      have hw := convWeakenA hE hI d (c := 0) (Nat.zero_le _) (convA_closedWeakenA hE hI hcla hclb hclA Γ h)
      rw [hcla 0, hclb 0, hclA 0] at hw
      exact hw

/-- retyping at an `=ₙ` sort. -/
def hasTyA_sortEqN {n : Nat} {Γ : LCtxA} {A : ExprA} {l l' : Level} (h : HasTyA E I n Γ A (.sort l))
    (hll : eqN l l') : HasTyA E I n Γ A (.sort l') :=
  hasTyA_of_tyConvA h (tyConvA_sorts Γ hll)

/-- the `ls'`-instantiation of a derivation, read in the `ls`-instantiated context. -/
theorem rightTypedA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) {a n : Nat} {ls ls' : List Level}
    (hls' : levelsBounded n ls' = true) (hlen' : ls'.length = a)
    {Γ : LCtxA} (hcc : CtxConvA E I n (instCtxA ls' Γ) (instCtxA ls Γ)) {e A : ExprA}
    (h : HasTyA E I a Γ e A) :
    Nonempty (HasTyA E I n (instCtxA ls Γ) (instantiateLevelsA ls' e) (instantiateLevelsA ls' A)) :=
  hasTyA_ctxConv hE hI hR hcc (hasTyA_instLevels hEL hIL hls' hlen' h)

/-- …and a type among them, at the `ls`-instantiated sort. -/
theorem rightTypedSortA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) {a n : Nat} {ls ls' : List Level}
    (hls' : levelsBounded n ls' = true) (hlen' : ls'.length = a) (heq : eqNList ls ls')
    {Γ : LCtxA} (hcc : CtxConvA E I n (instCtxA ls' Γ) (instCtxA ls Γ)) {A : ExprA}
    {u : Level} (h : HasTyA E I a Γ A (.sort u)) :
    Nonempty (HasTyA E I n (instCtxA ls Γ) (instantiateLevelsA ls' A) (.sort (instLevel ls u))) :=
  (rightTypedA hE hI hR hEL hIL hls' hlen' hcc h).elim fun t =>
    ⟨hasTyA_sortEqN t (eqNA_symm (instLevel_eqNList heq u))⟩

/-- the context conversion extended under an assumption, from the induction
    hypothesis on the binder's type. -/
theorem ctxConvA_extAssump (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) {a n : Nat} {ls ls' : List Level} (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (hlen : ls.length = a) (hlen' : ls'.length = a)
    (heq : eqNList ls ls')
    {Γ : LCtxA} (hcc : CtxConvA E I n (instCtxA ls' Γ) (instCtxA ls Γ))
    {A : ExprA} {u : Level} (hA : HasTyA E I a Γ A (.sort u))
    (ih : Nonempty (ConvA E I n (instCtxA ls Γ) (instantiateLevelsA ls A) (instantiateLevelsA ls' A)
      (.sort (instLevel ls u)))) :
    CtxConvA E I n (instCtxA ls' (.assumption A :: Γ)) (instCtxA ls (.assumption A :: Γ)) :=
  .assumption hcc (rightTypedSortA hE hI hR hEL hIL hls' hlen' heq hcc hA)
    ⟨hasTyA_instLevels hEL hIL hls hlen hA⟩ (ih.elim fun c => ⟨.symm _ _ _ _ c⟩)

/-- …and under a let-binding. -/
theorem ctxConvA_extLet (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) {a n : Nat} {ls ls' : List Level} (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (hlen : ls.length = a) (hlen' : ls'.length = a)
    (heq : eqNList ls ls')
    {Γ : LCtxA} (hcc : CtxConvA E I n (instCtxA ls' Γ) (instCtxA ls Γ))
    {A v : ExprA} {u : Level} (hA : HasTyA E I a Γ A (.sort u)) (hv : HasTyA E I a Γ v A)
    (ihA : Nonempty (ConvA E I n (instCtxA ls Γ) (instantiateLevelsA ls A) (instantiateLevelsA ls' A)
      (.sort (instLevel ls u))))
    (ihv : Nonempty (ConvA E I n (instCtxA ls Γ) (instantiateLevelsA ls v) (instantiateLevelsA ls' v)
      (instantiateLevelsA ls A))) :
    CtxConvA E I n (instCtxA ls' (.letBinding A v :: Γ)) (instCtxA ls (.letBinding A v :: Γ)) :=
  .letBinding hcc (rightTypedSortA hE hI hR hEL hIL hls' hlen' heq hcc hA)
    ⟨hasTyA_instLevels hEL hIL hls hlen hA⟩ (ihA.elim fun c => ⟨.symm _ _ _ _ c⟩)
    ⟨hasTyA_instLevels hEL hIL hls hlen hv⟩
    (ihA.elim fun cA => ihv.elim fun cv => (rightTypedA hE hI hR hEL hIL hls' hlen' hcc hA).elim fun tA' =>
      ⟨.tyConv _ _ _ _ _ (instLevel ls u) (instLevel ls' u) (instLevel ls u) (.symm _ _ _ _ cv)
        (hasTyA_instLevels hEL hIL hls hlen hA) (eqNA_refl _) tA' (eqNA_symm (instLevel_eqNList heq u)) cA⟩)

/-- the two instantiated pis are convertible, and the right one is typed at the
    left's sort, from the induction hypotheses on the domain and the codomain. -/
theorem piIrrA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) {a n : Nat} {ls ls' : List Level}
    (hls' : levelsBounded n ls' = true) (hlen' : ls'.length = a) (heq : eqNList ls ls')
    {Γ : LCtxA} (hcc : CtxConvA E I n (instCtxA ls' Γ) (instCtxA ls Γ))
    {A B : ExprA} {u v : Level} (hA : HasTyA E I a Γ A (.sort u))
    (hB : HasTyA E I a (.assumption A :: Γ) B (.sort v))
    (ihA : Nonempty (ConvA E I n (instCtxA ls Γ) (instantiateLevelsA ls A) (instantiateLevelsA ls' A)
      (.sort (instLevel ls u))))
    (ihB : Nonempty (ConvA E I n (instCtxA ls (.assumption A :: Γ)) (instantiateLevelsA ls B)
      (instantiateLevelsA ls' B) (.sort (instLevel ls v)))) :
    Nonempty (HasTyA E I n (instCtxA ls Γ)
      (.pi (instantiateLevelsA ls' A) (instLevel ls' u) (instantiateLevelsA ls' B) (instLevel ls' v))
      (.sort (.imax (instLevel ls u) (instLevel ls v)))) ∧
    Nonempty (ConvA E I n (instCtxA ls Γ)
      (.pi (instantiateLevelsA ls A) (instLevel ls u) (instantiateLevelsA ls B) (instLevel ls v))
      (.pi (instantiateLevelsA ls' A) (instLevel ls' u) (instantiateLevelsA ls' B) (instLevel ls' v))
      (.sort (.imax (instLevel ls u) (instLevel ls v)))) := by
  have hrt : Nonempty (HasTyA E I n (instCtxA ls Γ)
      (.pi (instantiateLevelsA ls' A) (instLevel ls' u) (instantiateLevelsA ls' B) (instLevel ls' v))
      (.sort (.imax (instLevel ls u) (instLevel ls v)))) :=
    (rightTypedA hE hI hR hEL hIL hls' hlen' hcc (.pi Γ A u B v hA hB)).elim fun t =>
      ⟨hasTyA_sortEqN t (eqNA_symm (instLevel_eqNList heq (.imax u v)))⟩
  exact ⟨hrt, ihA.elim fun cA => ihB.elim fun cB => hrt.elim fun t =>
    ⟨.pi _ _ _ _ _ (instLevel ls u) (instLevel ls' u) (instLevel ls v) (instLevel ls' v)
      (instLevel_eqNList heq u) (instLevel_eqNList heq v) cA cB t⟩⟩

/-- LEVEL IRRELEVANCE. -/
theorem convA_levelIrr (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) {a n : Nat} {ls ls' : List Level} (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (hlen : ls.length = a) (hlen' : ls'.length = a)
    (heq : eqNList ls ls') :
    {Γ : LCtxA} → CtxConvA E I n (instCtxA ls' Γ) (instCtxA ls Γ) → {e A : ExprA} →
    HasTyA E I a Γ e A →
    Nonempty (ConvA E I n (instCtxA ls Γ) (instantiateLevelsA ls e) (instantiateLevelsA ls' e)
      (instantiateLevelsA ls A))
  | _, _, _, _, .sort Γ l => ⟨.sorts _ (instLevel ls l) (instLevel ls' l) (instLevel_eqNList heq l)⟩
  | Γ, _, _, _, .bvar _ i A u h hA =>
      ⟨.refl _ (.bvar i) _ (hasTyA_instLevels hEL hIL hls hlen (HasTyA.bvar Γ i A u h hA))⟩
  | Γ, hcc, _, _, .const _ r ms m u hres hlen₀ hwf hT => by
      have ih := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hT
      have hBl := hasTyA_instLevels hEL hIL hls hlen hT
      have hAr := hasTyA_ctxConv hE hI hR hcc (hasTyA_instLevels hEL hIL hls' hlen' hT)
      rw [instLevels_mtype hEL hres hlen₀ ls] at ih hBl
      rw [instLevels_mtype hEL hres hlen₀ ls'] at ih hAr
      show Nonempty (ConvA E I n (instCtxA ls Γ) (.const r (ms.map (instLevel ls)))
        (.const r (ms.map (instLevel ls'))) (instantiateLevelsA ls (instantiateLevelsA ms m.mtypeA)))
      rw [instLevels_mtype hEL hres hlen₀ ls]
      exact ih.elim fun c => hAr.elim fun tr =>
        ⟨.consts _ r _ _ m hres (length_map_arity hlen₀ _) (levelsBounded_inst hls hlen hwf)
          (levelsBounded_inst hls' hlen' hwf) (instLevel_eqNList_map heq ms)
          (.conv _ _ _ _ (instLevel ls' u) (instLevel ls u)
            (.const _ r _ m (instLevel ls' u) hres (length_map_arity hlen₀ _)
              (levelsBounded_inst hls' hlen' hwf) tr)
            tr (eqNA_symm (instLevel_eqNList heq u)) hBl (.symm _ _ _ _ c))⟩
  | Γ, hcc, _, _, .pi _ A u B v hA hB =>
      have ihA := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA
      have ihB := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq (ctxConvA_extAssump hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA ihA) hB
      (piIrrA hE hI hR hEL hIL hls' hlen' heq hcc hA hB ihA ihB).2
  | Γ, hcc, _, _, .lam _ A u body B v hA hB hbody => by
      have ihA := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA
      have hcc' := ctxConvA_extAssump hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA ihA
      have ihB := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc' hB
      have ihb := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc' hbody
      obtain ⟨hpir, hpic⟩ := piIrrA hE hI hR hEL hIL hls' hlen' heq hcc hA hB ihA ihB
      have hpil := hasTyA_instLevels hEL hIL hls hlen (.pi Γ A u B v hA hB)
      have hr := rightTypedA hE hI hR hEL hIL hls' hlen' hcc (.lam Γ A u body B v hA hB hbody)
      exact ihA.elim fun cA => ihb.elim fun cb => hpir.elim fun tpr => hpic.elim fun cpi => hr.elim fun tr =>
        ⟨.lam _ _ _ _ _ _ (instLevel ls u) (instLevel ls' u) (instLevel ls v) (instLevel_eqNList heq u) cA cb
          (.conv _ _ _ _ (.imax (instLevel ls u) (instLevel ls v)) (.imax (instLevel ls u) (instLevel ls v))
            tr tpr (eqNA_refl _) hpil (.symm _ _ _ _ cpi))⟩
  | Γ, hcc, _, _, .app _ f x A B u v w hB hTy hf ha => by
      have ihf := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hf
      have ihx := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc ha
      have ihTy := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hTy
      have hBl := hasTyA_instLevels hEL hIL hls hlen hB
      have hr := rightTypedA hE hI hR hEL hIL hls' hlen' hcc (.app Γ f x A B u v w hB hTy hf ha)
      have hTyl := hasTyA_instLevels hEL hIL hls hlen hTy
      have hTyr := rightTypedA hE hI hR hEL hIL hls' hlen' hcc hTy
      simp only [instantiateLevelsA_instantiate0A] at ihTy hr hTyr
      rw [instantiateLevelsA_instantiate0A] at hTyl
      show Nonempty (ConvA E I n (instCtxA ls Γ) (.app (instantiateLevelsA ls f) (instantiateLevelsA ls x))
        (.app (instantiateLevelsA ls' f) (instantiateLevelsA ls' x))
        (instantiateLevelsA ls (instantiate0A x B)))
      rw [instantiateLevelsA_instantiate0A]
      exact ihf.elim fun cf => ihx.elim fun cx => ihTy.elim fun cTy => hr.elim fun tr => hTyr.elim fun tTyr =>
        ⟨.app _ _ _ _ _ (instantiateLevelsA ls A) (instantiateLevelsA ls B) (instLevel ls u) (instLevel ls v)
          cf cx hBl
          (.conv _ _ _ _ (instLevel ls' w) (instLevel ls w) tr tTyr (eqNA_symm (instLevel_eqNList heq w)) hTyl
            (.symm _ _ _ _ cTy))⟩
  | Γ, hcc, _, _, .letE _ A u w value B body hA hv hTy hb => by
      have ihA := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA
      have ihv := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hv
      have ihTy := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hTy
      have hcc' := ctxConvA_extLet hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA hv ihA ihv
      have ihb := convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc' hb
      have hr := rightTypedA hE hI hR hEL hIL hls' hlen' hcc (.letE Γ A u w value B body hA hv hTy hb)
      have hTyl := hasTyA_instLevels hEL hIL hls hlen hTy
      have hTyr := rightTypedA hE hI hR hEL hIL hls' hlen' hcc hTy
      simp only [instantiateLevelsA_instantiate0A] at ihTy hr hTyr
      rw [instantiateLevelsA_instantiate0A] at hTyl
      show Nonempty (ConvA E I n (instCtxA ls Γ)
        (.letE (instantiateLevelsA ls A) (instantiateLevelsA ls value) (instantiateLevelsA ls body))
        (.letE (instantiateLevelsA ls' A) (instantiateLevelsA ls' value) (instantiateLevelsA ls' body))
        (instantiateLevelsA ls (instantiate0A value B)))
      rw [instantiateLevelsA_instantiate0A]
      exact ihA.elim fun cA => ihv.elim fun cv => ihb.elim fun cb => ihTy.elim fun cTy => hr.elim fun tr =>
        hTyr.elim fun tTyr =>
        ⟨.letE _ _ _ _ _ _ _ (instantiateLevelsA ls B) (instLevel ls u) cA cv cb
          (.conv _ _ _ _ (instLevel ls' w) (instLevel ls w) tr tTyr (eqNA_symm (instLevel_eqNList heq w)) hTyl
            (.symm _ _ _ _ cTy))⟩
  | Γ, _, _, _, .lit _ t T hexp =>
      ⟨.refl _ (.lit t) _ (hasTyA_instLevels hEL hIL hls hlen (HasTyA.lit Γ t T hexp))⟩
  | Γ, hcc, _, _, .conv _ e A B l u h hAl hlu hB hc =>
      (convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc h).elim fun c =>
        ⟨.tyConv _ _ _ _ _ (instLevel ls l) (instLevel ls u) (instLevel ls u) c
          (hasTyA_instLevels hEL hIL hls hlen hAl) (eqN_instLevel hlu ls)
          (hasTyA_instLevels hEL hIL hls hlen hB) (eqNA_refl _) (convA_instLevels hEL hIL hls hlen hc)⟩

/-- the two instantiations of a well-formed context are pointwise convertible. -/
theorem ctxConvA_instLevels (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) {a n : Nat} {ls ls' : List Level} (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (hlen : ls.length = a) (hlen' : ls'.length = a)
    (heq : eqNList ls ls') :
    {Γ : LCtxA} → CtxWfA E I a Γ → CtxConvA E I n (instCtxA ls' Γ) (instCtxA ls Γ)
  | _, .nil => .nil
  | _, .assumption hΓ hA =>
      have hcc := ctxConvA_instLevels hE hI hR hEL hIL hls hls' hlen hlen' heq hΓ
      ctxConvA_extAssump hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA
        (convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA)
  | _, .letBinding hΓ hA hv =>
      have hcc := ctxConvA_instLevels hE hI hR hEL hIL hls hls' hlen hlen' heq hΓ
      ctxConvA_extLet hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA hv
        (convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hA)
        (convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq hcc hv)

theorem convA_levelIrr_wf (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) {a n : Nat} {ls ls' : List Level} (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (hlen : ls.length = a) (hlen' : ls'.length = a)
    (heq : eqNList ls ls')
    {Γ : LCtxA} (hΓ : CtxWfA E I a Γ) {e A : ExprA} (h : HasTyA E I a Γ e A) :
    Nonempty (ConvA E I n (instCtxA ls Γ) (instantiateLevelsA ls e) (instantiateLevelsA ls' e)
      (instantiateLevelsA ls A)) :=
  convA_levelIrr hE hI hR hEL hIL hls hls' hlen hlen' heq (ctxConvA_instLevels hE hI hR hEL hIL hls hls' hlen hlen' heq hΓ) h

end Irr

#print axioms convA_closedWeakenA
#print axioms convA_levelIrr
#print axioms ctxConvA_instLevels
#print axioms convA_levelIrr_wf

end Rcic.Declarative.Ann
