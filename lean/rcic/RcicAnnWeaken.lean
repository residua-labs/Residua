import rcic.RcicAnnWkOps

/-!
# M2-s (2) — the judgments weaken, on the copy

`RcicWeaken`'s construction (`hasTyWeaken`/`convWeaken`) transcribed onto
`HasTyA`/`ConvA`: inserting a declaration at `c ≤ Γ.length` and lifting the
subject, the type and (for `ConvA`) both sides at `c` preserves every rule. The
typed rules carry more premises than the tree's — each is one more recursive
call. What the tree needed as `EnvWf` closedness is `EnvClosedA` here; the ι
rule rides on `IotaLiftA` and `hStepFnA_liftA` (the step the relation quotes
is a step in the extended context too); the variable rules read
`RcicAnnCtxMorph`; β/ζ/app/letE read `liftA_instantiate0A`; η reads
`liftA_zero_succ_swap`. Constructions in `Type`, chained as `def`s (the tree's
discipline: `Nonempty` is a terminal wrapper only).

Then along a whole `WkSpecA` (`hasTyA_wk`, `convA_wk`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Weaken
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

mutual

def convWeakenA (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) :
    {c : Nat} → {Γ : LCtxA} → c ≤ Γ.length → {a b A : ExprA} →
    ConvA E I n Γ a b A →
    ConvA E I n (insertAtA d c Γ) (liftA c 1 a) (liftA c 1 b) (liftA c 1 A)
  | _, _, hc, _, _, _, .refl _ _ _ h => .refl _ _ _ (hasTyWeakenA hE hI d hc h)
  | _, _, hc, _, _, _, .symm _ _ _ _ h => .symm _ _ _ _ (convWeakenA hE hI d hc h)
  | _, _, hc, _, _, _, .trans _ _ _ _ _ h1 h2 =>
      .trans _ _ _ _ _ (convWeakenA hE hI d hc h1) (convWeakenA hE hI d hc h2)
  | c, Γ, hc, _, _, _, .beta _ A u body arg B hA hbody harg hred => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      have hred' := hasTyWeakenA hE hI d hc hred
      rw [liftA_instantiate0A, liftA_instantiate0A] at hred'
      show ConvA E I n (insertAtA d c Γ)
        (.app (.lam (liftA c 1 A) u (liftA (c + 1) 1 body)) (liftA c 1 arg))
        (liftA c 1 (instantiate0A arg body)) (liftA c 1 (instantiate0A arg B))
      rw [liftA_instantiate0A, liftA_instantiate0A]
      exact .beta _ _ u _ _ _ (hasTyWeakenA hE hI d hc hA)
        (hasTyWeakenA hE hI d (c := c + 1) hc' hbody) (hasTyWeakenA hE hI d hc harg) hred'
  | c, Γ, hc, _, _, _, .zeta _ A value body B u hA hv hb hred => by
      have hc' : c + 1 ≤ (LocalDeclA.letBinding A value :: Γ).length := Nat.succ_le_succ hc
      have hred' := hasTyWeakenA hE hI d hc hred
      rw [liftA_instantiate0A, liftA_instantiate0A] at hred'
      show ConvA E I n (insertAtA d c Γ)
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
      show ConvA E I n (insertAtA d c _) (.const r ls) (liftA c 1 (instantiateLevelsA ls b))
        (liftA c 1 (instantiateLevelsA ls m.mtypeA))
      rw [hcl1, hcl2]
      exact .delta _ r ls m b hres hbody htr hlen hwf hb'
  | c, Γ, hc, _, _, _, .iota _ lhs rhs T h hlhs hrhs =>
      .iota _ _ _ _
        ⟨by simp only [hI c lhs, h.1, Option.map_some'],
         by simp only [hStepFnA_liftA hE hI d c Γ hc lhs, h.2, Option.map_some']⟩
        (hasTyWeakenA hE hI d hc hlhs) (hasTyWeakenA hE hI d hc hrhs)
  | c, _, hc, _, _, _, .structIota _ f a rhs e T hrec hs h hlhs hrhs hcv =>
      .structIota _ (liftA c 1 f) (liftA c 1 a) _ (liftA c 1 e) _
        (by rw [recAtMajorA_liftA]; exact hrec)
        (by rw [structArmA_liftA hE c f a, hs]; rfl)
        (by have h' := hI c (.app f a); rw [h] at h'; exact h')
        (hasTyWeakenA hE hI d hc hlhs) (hasTyWeakenA hE hI d hc hrhs) (convWeakenA hE hI d hc hcv)
  | c, _, hc, _, _, _, .lit _ t T hexp => by
      have hexp' := hasTyWeakenA hE hI d hc hexp
      rw [liftA_natExpandA] at hexp'
      show ConvA E I n (insertAtA d c _) (.lit t) (liftA c 1 (natExpandA t)) (liftA c 1 T)
      rw [liftA_natExpandA]
      exact .lit _ t _ hexp'
  | c, Γ, hc, _, _, _, .app _ f g a b A B u v h1 h2 hB hrt => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      have hB' := hasTyWeakenA hE hI d (c := c + 1) hc' hB
      have hrt' := hasTyWeakenA hE hI d hc hrt
      rw [liftA_instantiate0A] at hrt'
      show ConvA E I n (insertAtA d c _) (.app (liftA c 1 f) (liftA c 1 a))
        (.app (liftA c 1 g) (liftA c 1 b)) (liftA c 1 (instantiate0A a B))
      rw [liftA_instantiate0A]
      exact .app _ _ _ _ _ _ _ u v (convWeakenA hE hI d hc h1) (convWeakenA hE hI d hc h2) hB' hrt'
  | c, Γ, hc, _, _, _, .lam _ A A' b b' B u u' v hu hA hb hrt => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      exact .lam _ _ _ _ _ _ u u' v hu (convWeakenA hE hI d hc hA)
        (convWeakenA hE hI d (c := c + 1) hc' hb) (hasTyWeakenA hE hI d hc hrt)
  | c, Γ, hc, _, _, _, .pi _ A A' B B' u u' v v' hu hv hA hB hrt => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      exact .pi _ _ _ _ _ u u' v v' hu hv (convWeakenA hE hI d hc hA)
        (convWeakenA hE hI d (c := c + 1) hc' hB) (hasTyWeakenA hE hI d hc hrt)
  | c, Γ, hc, _, _, _, .letE _ A A' v v' b b' B u hA hv hb hrt => by
      have hc' : c + 1 ≤ (LocalDeclA.letBinding A v :: Γ).length := Nat.succ_le_succ hc
      have hrt' := hasTyWeakenA hE hI d hc hrt
      rw [liftA_instantiate0A] at hrt'
      show ConvA E I n (insertAtA d c Γ)
        (.letE (liftA c 1 A) (liftA c 1 v) (liftA (c + 1) 1 b))
        (.letE (liftA c 1 A') (liftA c 1 v') (liftA (c + 1) 1 b'))
        (liftA c 1 (instantiate0A v B))
      rw [liftA_instantiate0A]
      exact .letE _ _ _ _ _ _ _ _ u (convWeakenA hE hI d hc hA) (convWeakenA hE hI d hc hv)
        (convWeakenA hE hI d (c := c + 1) hc' hb) hrt'
  | _, _, _, _, _, _, .sorts _ l₁ l₂ h => .sorts _ l₁ l₂ h
  | c, _, hc, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h hrt => by
      have hcl : liftA c 1 (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA := by
        rw [← instantiateLevelsA_liftA, (hE r m hres).1 c]
      have hrt' := hasTyWeakenA hE hI d hc hrt
      rw [hcl] at hrt'
      show ConvA E I n (insertAtA d c _) (.const r ls) (.const r ls')
        (liftA c 1 (instantiateLevelsA ls m.mtypeA))
      rw [hcl]
      exact .consts _ r ls ls' m hres hlen hwf hwf' h hrt'
  | c, Γ, hc, _, _, _, .eta _ f A B u v h hrt => by
      have hrt' : HasTyA E I n (insertAtA d c Γ)
          (.lam (liftA c 1 A) u (.app (liftA (c + 1) 1 (liftA 0 1 f)) (liftA (c + 1) 1 (.bvar 0))))
          (.pi (liftA c 1 A) u (liftA (c + 1) 1 B) v) := hasTyWeakenA hE hI d hc hrt
      rw [liftA_bvar, shiftIdx_succ_zero, ← liftA_zero_succ_swap] at hrt'
      show ConvA E I n (insertAtA d c Γ)
        (.lam (liftA c 1 A) u (.app (liftA (c + 1) 1 (liftA 0 1 f)) (liftA (c + 1) 1 (.bvar 0))))
        (liftA c 1 f) (.pi (liftA c 1 A) u (liftA (c + 1) 1 B) v)
      rw [liftA_bvar, shiftIdx_succ_zero, ← liftA_zero_succ_swap]
      exact .eta _ _ _ _ u v (hasTyWeakenA hE hI d hc h) hrt'
  | _, _, hc, _, _, _, .irr _ P p q hP hp hq =>
      .irr _ _ _ _ (hasTyWeakenA hE hI d hc hP) (hasTyWeakenA hE hI d hc hp)
        (hasTyWeakenA hE hI d hc hq)
  | _, _, hc, _, _, _, .tyConv _ a b A A' l l' u h hAl hlu hA'l hl'u hA =>
      .tyConv _ _ _ _ _ l l' u (convWeakenA hE hI d hc h) (hasTyWeakenA hE hI d hc hAl) hlu
        (hasTyWeakenA hE hI d hc hA'l) hl'u (convWeakenA hE hI d hc hA)

def hasTyWeakenA (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) :
    {c : Nat} → {Γ : LCtxA} → c ≤ Γ.length → {e A : ExprA} →
    HasTyA E I n Γ e A → HasTyA E I n (insertAtA d c Γ) (liftA c 1 e) (liftA c 1 A)
  | _, _, _, _, _, .sort _ l => .sort _ l
  | c, Γ, hc, _, _, .bvar _ i A u h hA => by
      rw [liftA_bvar]
      have h' := lookupTypeA_insertAtA d c Γ hc i
      rw [h, Option.map_some'] at h'
      exact .bvar _ _ _ u h' (hasTyWeakenA hE hI d hc hA)
  | c, _, hc, _, _, .const _ r ls m u hres hlen hwf hT => by
      have hcl : liftA c 1 (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA := by
        rw [← instantiateLevelsA_liftA, (hE r m hres).1 c]
      have hT' := hasTyWeakenA hE hI d hc hT
      rw [hcl] at hT'
      show HasTyA E I n (insertAtA d c _) (.const r ls) (liftA c 1 (instantiateLevelsA ls m.mtypeA))
      rw [hcl]
      exact .const _ r ls m u hres hlen hwf hT'
  | c, Γ, hc, _, _, .pi _ A u B v hA hB => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      exact .pi _ _ u _ v (hasTyWeakenA hE hI d hc hA) (hasTyWeakenA hE hI d (c := c + 1) hc' hB)
  | c, Γ, hc, _, _, .lam _ A u body B v hA hB hbody => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      exact .lam _ _ u _ _ v (hasTyWeakenA hE hI d hc hA) (hasTyWeakenA hE hI d (c := c + 1) hc' hB)
        (hasTyWeakenA hE hI d (c := c + 1) hc' hbody)
  | c, Γ, hc, _, _, .app _ f a A B u v w hB hTy hf ha => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      have hTy' := hasTyWeakenA hE hI d hc hTy
      rw [liftA_instantiate0A] at hTy'
      show HasTyA E I n (insertAtA d c Γ) (.app (liftA c 1 f) (liftA c 1 a))
        (liftA c 1 (instantiate0A a B))
      rw [liftA_instantiate0A]
      exact .app _ _ _ _ _ u v w (hasTyWeakenA hE hI d (c := c + 1) hc' hB) hTy'
        (hasTyWeakenA hE hI d hc hf) (hasTyWeakenA hE hI d hc ha)
  | c, Γ, hc, _, _, .letE _ A u w value B body hA hv hTy hb => by
      have hc' : c + 1 ≤ (LocalDeclA.letBinding A value :: Γ).length := Nat.succ_le_succ hc
      have hTy' := hasTyWeakenA hE hI d hc hTy
      rw [liftA_instantiate0A] at hTy'
      show HasTyA E I n (insertAtA d c Γ)
        (.letE (liftA c 1 A) (liftA c 1 value) (liftA (c + 1) 1 body))
        (liftA c 1 (instantiate0A value B))
      rw [liftA_instantiate0A]
      exact .letE _ _ u w _ _ _ (hasTyWeakenA hE hI d hc hA) (hasTyWeakenA hE hI d hc hv) hTy'
        (hasTyWeakenA hE hI d (c := c + 1) hc' hb)
  | c, _, hc, _, _, .lit _ t T hexp => by
      have hexp' := hasTyWeakenA hE hI d hc hexp
      rw [liftA_natExpandA] at hexp'
      exact .lit _ t _ hexp'
  | _, _, hc, _, _, .conv _ e A B l u h hAl hlu hB hcv =>
      .conv _ _ _ _ l u (hasTyWeakenA hE hI d hc h) (hasTyWeakenA hE hI d hc hAl) hlu
        (hasTyWeakenA hE hI d hc hB) (convWeakenA hE hI d hc hcv)

end

/-! ## along a weakening spec -/

def hasTyA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {e A : ExprA} →
    HasTyA E I n Γ e A → HasTyA E I n (wkCtxA ρ Γ) (wkExprA ρ e) (wkExprA ρ A)
  | _, [], _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, h =>
      hasTyA_wk hE hI (insertAtA d c Γ) ρ hρ (hasTyWeakenA hE hI d hc h)

def convA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {a b A : ExprA} →
    ConvA E I n Γ a b A → ConvA E I n (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) (wkExprA ρ A)
  | _, [], _, _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, _, h =>
      convA_wk hE hI (insertAtA d c Γ) ρ hρ (convWeakenA hE hI d hc h)

/-- a closed typing in the empty context transports to any context (the
    tree's `hasTyClosedWeaken`). -/
def hasTyClosedWeakenA (hE : EnvClosedA E) (hI : IotaLiftA I) {e A : ExprA}
    (hcl : ∀ k, liftA k 1 e = e) (hclA : ∀ k, liftA k 1 A = A) :
    (Γ : LCtxA) → HasTyA E I n [] e A → HasTyA E I n Γ e A
  | [], h => h
  | d :: Γ, h => by
      have hw := hasTyWeakenA hE hI d (c := 0) (Nat.zero_le _) (hasTyClosedWeakenA hE hI hcl hclA Γ h)
      rw [hcl 0, hclA 0] at hw
      exact hw

end Weaken

#print axioms hasTyWeakenA
#print axioms convWeakenA
#print axioms hasTyA_wk
#print axioms convA_wk
#print axioms hasTyClosedWeakenA

end Rcic.Declarative.Ann
