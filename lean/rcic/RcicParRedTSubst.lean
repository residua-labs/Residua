import rcic.RcicParRedT
import rcic.RcicTypedWeaken
import rcic.RcicTypedSubst
import rcic.RcicTypedSubstLet
import rcic.RcicParRedSubst
import rcic.RcicIotaShape
import rcic.RcicParRedSRTyped

/-!
# RcicParRedTSubst — weakening and substitution for `ParRedT` (#6293)

The typed parallel reduction's two transports. D's β×β and ζ×letE
critical pairs consume them: β×β needs substitution under an
`assumption` hole (the `parRedT_subst` family), ζ×letE needs it under a
`letBinding` hole (`parRedT_substLet`); both rest on the weakening
(`parRedT_lift` family) for the hole case.

## The interface the transports carry

`ParRedT` packs endpoint typings into its constructors (F-ParRedT-3), so
the transports need premises the erased `parRed_weaken`/`parRed_instantiate_*`
did not:

* **`hcl`/`hinst`** — `EnvClosed`/`EnvMembersSubstStable`, the same
  fronts `hasTyTWeaken`/`hasTyT_substS` take (env-member invariance for
  `const`/`delta`).
* **`hPEqL`/`hPEqS`/`hPEqSL`** — `PEq`-leaf transport under weakening /
  either substitution. The leaf is stubbed (F-ParRedT-7); whatever lands
  for it must step the same way.
* **`hPEqT`** — the `peq` leaf's typing evidence, same shape
  `parRedT_typed` takes (needed to rebuild the carried right-endpoint
  typings whose subjects move `a → a'`).
* **`hTC`** — `ParRedT → ConvT` at the substitution pair, grokC's
  `parRedT_to_convT` item (#6293 12:30Z table, adjacent). Carried as an
  explicit hypothesis, not re-proved here: the right-endpoint typings at
  `T[v]` vs the value-side `T[v']` bridge through it.
* **`hS`** — sort-regularity as a `Σ'`-valued premise
  (`∀ Γ e T, HasTyT Γ e T → Σ' w, HasTyT Γ T (.sort w)`), discharged
  downstream by `regularT`/`endpoints3` (`RcicTypedValidity`) where the
  env fronts are met. `DT007T_typing_regularity`'s `∃`-`Nonempty` form
  cannot feed `Type`-valued construction.

Every premise is named and visible in the statement — nothing semantic
is silently assumed (conditional closure, the same idiom
`parRedT_typed` uses for `hPEq`).

No `sorry`, no new axiom.
-/

namespace Rcic.Declarative

section Lift

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
variable {E : ResolvedEnv} {n : Nat}

/-- `TyConvT` under one-declaration weakening — link-wise `convTWeaken`. -/
def tyConvTWeaken (d : LocalDecl) (hcl : EnvClosed E) :
    {c : Nat} → {Γ : LCtx} → {A A' : Expr Nat} →
    TyConvT E n Γ A A' →
    TyConvT E n (insertAt d c Γ) (lift c 1 A) (lift c 1 A')
  | _, _, _, _, .refl _ _ => .refl _ _
  | _, _, _, _, .of _ _ _ _ h => .of _ _ _ _ (convTWeaken d hcl h)
  | _, _, _, _, .trans _ _ _ _ h1 h2 =>
      .trans _ _ _ _ (tyConvTWeaken d hcl h1) (tyConvTWeaken d hcl h2)

/-- `ConvT` under prefix weakening — `convTWeaken` iterated head-first,
    `lift_zero_succ` merging the units (the `parRed_weaken_lctx`
    pattern). -/
def convT_lift_lctx (hcl : EnvClosed E) :
    (Δ : LCtx) → {Γ : LCtx} → {a b T : Expr Nat} →
    ConvT E n Γ a b T →
    ConvT E n (Δ ++ Γ) (lift 0 Δ.length a) (lift 0 Δ.length b)
      (lift 0 Δ.length T)
  | [], _, _, _, _, h => by
      simp only [List.nil_append, List.length_nil, lift_zero]
      exact h
  | d :: Δ, Γ, a, b, T, h => by
      have ih := convT_lift_lctx hcl Δ h
      have hw := convTWeaken d hcl (c := 0) ih
      simp only [List.cons_append, List.length_cons, insertAt_zero]
      have ha : lift 0 1 (lift 0 Δ.length a) = lift 0 (Δ.length + 1) a :=
        lift_zero_succ Δ.length a
      have hb : lift 0 1 (lift 0 Δ.length b) = lift 0 (Δ.length + 1) b :=
        lift_zero_succ Δ.length b
      have hT : lift 0 1 (lift 0 Δ.length T) = lift 0 (Δ.length + 1) T :=
        lift_zero_succ Δ.length T
      rw [← ha, ← hb, ← hT]
      exact hw

/-- `HasTyT` under prefix weakening — the same iteration. -/
def hasTyT_lift_lctx (hcl : EnvClosed E) :
    (Δ : LCtx) → {Γ : LCtx} → {e A : Expr Nat} →
    HasTyT E n Γ e A →
    HasTyT E n (Δ ++ Γ) (lift 0 Δ.length e) (lift 0 Δ.length A)
  | [], _, _, _, h => by
      simp only [List.nil_append, List.length_nil, lift_zero]
      exact h
  | d :: Δ, Γ, e, A, h => by
      have ih := hasTyT_lift_lctx hcl Δ h
      have hw := hasTyTWeaken d hcl (c := 0) ih
      simp only [List.cons_append, List.length_cons, insertAt_zero]
      have he : lift 0 1 (lift 0 Δ.length e) = lift 0 (Δ.length + 1) e :=
        lift_zero_succ Δ.length e
      have hA : lift 0 1 (lift 0 Δ.length A) = lift 0 (Δ.length + 1) A :=
        lift_zero_succ Δ.length A
      rw [← he, ← hA]
      exact hw

/-- `DerivedIotaU` under weakening — `liftWitness`/`liftWitnessS` plus
    the witness endpoint lemmas. -/
def derivedIotaU_lift (c : Nat) {lhs rhs : Expr Nat} :
    DerivedIotaU E lhs rhs →
    DerivedIotaU E (lift c 1 lhs) (lift c 1 rhs)
  | .ofU w => by
      rw [← iotaLhsOf_lift c w, ← iotaRhsOf_lift c w]
      exact .ofU (liftWitness c w)
  | .ofUS w => by
      rw [← iotaLhsOfS_lift c w, ← iotaRhsOfS_lift c w]
      exact .ofUS (liftWitnessS c w)

/-- The typed weakening theorem: `ParRedT` at `T` transports under
    `insertAt`. Every carried `HasTyT`/`ConvT`/`TyConvT` premise moves by
    `hasTyTWeaken`/`convTWeaken`; the `bvarZeta` arm splits on the
    insertion side exactly as `parRed_weaken` does. -/
def parRedT_lift (d : LocalDecl) (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :
    {c : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    ParRedT PEq E n Γ a b T →
    ParRedT PEq E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T)
  | c, _, _, _, _, .refl _ _ _ h =>
      .refl _ _ _ (hasTyTWeaken d hcl h)
  | c, _, _, _, _, .sortEq _ l₁ l₂ _ h hl hr => by
      simp only [lift]
      exact .sortEq _ _ _ _ h (hasTyTWeaken d hcl hl) (hasTyTWeaken d hcl hr)
  | c, _, _, _, _, .consts _ r ls ls' _ h hl hr => by
      simp only [lift]
      exact .consts _ _ _ _ _ h (hasTyTWeaken d hcl hl) (hasTyTWeaken d hcl hr)
  | c, Γ, _, _, _, .bvarZeta _ i A v v' T h hv hl hr => by
      by_cases hic : i < c
      · -- insert below the looked-up let: the stored decl lifts, the step
        -- recurses inside the tail.
        simp only [lift, if_neg (Nat.not_le_of_gt hic)]
        have hlen := get?_some_lt h
        have hg := insertAt_get?_lt d (Γ := Γ) hic h
        have hdrop := insertAt_drop_lt d (Γ := Γ) hic hlen
        have hv' := parRedT_lift d hcl hPEqL (c := c - i - 1) hv
        rw [← hdrop] at hv'
        have htgt :
            lift 0 (i + 1) (lift (c - i - 1) 1 v') =
              lift (i + 1 + (c - i - 1)) 1 (lift 0 (i + 1) v') :=
          lift_lift_permute (i + 1) 1 (c - i - 1) 0 (Nat.zero_le _) v'
        have hsum : i + 1 + (c - i - 1) = c := by omega
        rw [hsum] at htgt
        simp only [liftDecl] at hg
        have hl' := hasTyTWeaken d hcl (c := c) hl
        have hr' := hasTyTWeaken d hcl (c := c) hr
        simp only [lift, if_neg (Nat.not_le_of_gt hic)] at hl' hr'
        rw [← htgt] at hr'
        exact htgt ▸ .bvarZeta (insertAt d c Γ) i
          (lift (c - i - 1) 1 A) (lift (c - i - 1) 1 v) (lift (c - i - 1) 1 v')
          (lift c 1 T) hg hv' hl' hr'
      · -- insert at or above: index shifts, tail unchanged.
        have hge : c ≤ i := Nat.le_of_not_lt hic
        simp only [lift, if_pos hge]
        have hg := insertAt_get?_ge d (Γ := Γ) hge
        rw [h] at hg
        have hdrop := insertAt_drop_ge d (Γ := Γ) hge
        have htgt : lift 0 (i + 2) v' =
            lift c 1 (lift 0 (i + 1) v') :=
          (lift_lift_merge 1 (i + 1) 0 c (Nat.zero_le c)
            (by omega : c ≤ i + 1) v').symm
        have hl' := hasTyTWeaken d hcl (c := c) hl
        have hr' := hasTyTWeaken d hcl (c := c) hr
        simp only [lift, if_pos hge] at hl'
        rw [← htgt] at hr'
        exact htgt ▸ .bvarZeta (insertAt d c Γ) (i + 1) A v v' (lift c 1 T)
          hg (hdrop ▸ hv) hl' hr'
  | c, Γ, _, _, _, .delta _ r ls m b T hres hbody htr hlen hwf hl hr => by
      have hbc : lift c 1 b = b := (hcl r m hres).2 b hbody c
      have hl' := hasTyTWeaken d hcl (c := c) hl
      have hr' := hasTyTWeaken d hcl (c := c) hr
      simp only [lift, lift_instantiateLevels, hbc] at hr' ⊢
      exact .delta _ _ _ _ _ _ hres hbody htr hlen hwf hl' hr'
  | c, _, _, _, _, .app Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr => by
      have h := lift_instantiate_low 1 c 0 a (by omega) B
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hTy' := hasTyTWeaken d hcl (c := c) hTy
      have hr' := hasTyTWeaken d hcl (c := c) hr
      simp only [lift, instantiate0] at hTy' hr' ⊢
      rw [h] at hTy' hr' ⊢
      exact .app _ _ _ _ _ _ _ _ _ _
        (parRedT_lift d hcl hPEqL hf) (tyConvTWeaken d hcl hc) hB' hTy'
        (parRedT_lift d hcl hPEqL ha) hr'
  | c, _, _, _, _, .beta Γ A body body' arg arg' B u v w hA hB hTy hb ha hred => by
      have h := lift_instantiate_low 1 c 0 arg (by omega) B
      have h' := lift_instantiate_low 1 c 0 arg' (by omega) body'
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hTy' := hasTyTWeaken d hcl (c := c) hTy
      have hred' := hasTyTWeaken d hcl (c := c) hred
      have hb' := parRedT_lift d hcl hPEqL (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      simp only [lift, instantiate0] at hTy' hred' ⊢
      rw [h] at hTy' hred' ⊢
      rw [h'] at hred' ⊢
      exact .beta _ _ _ _ _ _ _ _ _ _
        (hasTyTWeaken d hcl hA) hB' hTy' hb'
        (parRedT_lift d hcl hPEqL ha) hred'
  | c, _, _, _, _, .lam Γ A A' body body' B u v hc hA hB hb hrt => by
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hb' := parRedT_lift d hcl hPEqL (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      have hrt' := hasTyTWeaken d hcl (c := c) hrt
      simp only [lift] at hrt' ⊢
      exact .lam _ _ _ _ _ _ _ _
        (convTWeaken d hcl hc) (hasTyTWeaken d hcl hA) hB' hb' hrt'
  | c, _, _, _, _, .pi Γ A A' B B' u v hA hc hB hcB hrt => by
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hcB' := convTWeaken d hcl (c := c + 1) hcB
      simp only [insertAt_succ_cons, liftDecl] at hcB'
      have hrt' := hasTyTWeaken d hcl (c := c) hrt
      simp only [lift] at hrt' ⊢
      exact .pi _ _ _ _ _ _ _
        (hasTyTWeaken d hcl hA) (convTWeaken d hcl hc) hB' hcB' hrt'
  | c, _, _, _, _, .letE Γ A A' value value' body body' B u w hc hA hv hB hTy
        hb hrt => by
      have h := lift_instantiate_low 1 c 0 value (by omega) B
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hTy' := hasTyTWeaken d hcl (c := c) hTy
      have hrt' := hasTyTWeaken d hcl (c := c) hrt
      have hb' := parRedT_lift d hcl hPEqL (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      simp only [lift, instantiate0] at hTy' hrt' ⊢
      rw [h] at hTy' hrt' ⊢
      exact .letE _ _ _ _ _ _ _ _ _ _
        (convTWeaken d hcl hc) (hasTyTWeaken d hcl hA)
        (parRedT_lift d hcl hPEqL hv) hB' hTy' hb' hrt'
  | c, _, _, _, _, .zeta Γ A value value' body body' B u w hA hv hB hTy
        hb hred => by
      have h := lift_instantiate_low 1 c 0 value (by omega) B
      have h' := lift_instantiate_low 1 c 0 value' (by omega) body'
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hTy' := hasTyTWeaken d hcl (c := c) hTy
      have hred' := hasTyTWeaken d hcl (c := c) hred
      have hb' := parRedT_lift d hcl hPEqL (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      simp only [lift, instantiate0] at hTy' hred' ⊢
      rw [h] at hTy' hred' ⊢
      rw [h'] at hred' ⊢
      exact .zeta _ _ _ _ _ _ _ _ _
        (hasTyTWeaken d hcl hA) (parRedT_lift d hcl hPEqL hv) hB' hTy'
        hb' hred'
  | c, _, _, _, _, .iotaSpine Γ lhs lhs' rhs T hstep hI hred hrhs => by
      exact .iotaSpine _ _ _ _ _
        (parRedT_lift d hcl hPEqL hstep) (derivedIotaU_lift c hI)
        (hasTyTWeaken d hcl hred) (hasTyTWeaken d hcl hrhs)
  | c, Γ, _, _, _, .iotaStarK _ w major Tm rhs T rl afs hrl hsel hfam hmajor
        hmk hTm0 hι hlι hlhs hrhs => by
      have hsrc :
          lift c 1 (recCall (.const w.recRef w.ls) w.preMajor major) =
          recCall (.const (liftWitness c w).recRef (liftWitness c w).ls)
            (liftWitness c w).preMajor (lift c 1 major) := by
        rw [recCall_lift]; rfl
      have hfam' : ∃ lsF, (appsSpine (lift c 1 Tm)).1 =
          .const (liftWitness c w).familyRef lsF := by
        obtain ⟨lsF, hlsF⟩ := hfam
        refine ⟨lsF, ?_⟩
        show (appsSpine (lift c 1 Tm)).1 = .const w.familyRef lsF
        rw [appsSpine_lift, hlsF]; rfl
      have hmk' := hasTyTWeaken d hcl (c := c) hmk
      have hlι' := hasTyTWeaken d hcl (c := c) hlι
      have hlhs' := hasTyTWeaken d hcl (c := c) hlhs
      rw [← ctorMajor_lift c w] at hmk'
      rw [← iotaLhsOf_lift c w] at hlι'
      rw [hsrc] at hlhs'
      have hι' : DerivedIotaU E (iotaLhsOf (liftWitness c w))
          (lift c 1 rhs) := by
        have h := derivedIotaU_lift c hι
        rwa [← iotaLhsOf_lift c w] at h
      rw [hsrc]
      exact .iotaStarK _ (liftWitness c w) _ _ _ _ _ _ hrl hsel hfam'
        (hasTyTWeaken d hcl hmajor) hmk' (hasTyTWeaken d hcl hTm0) hι' hlι'
        hlhs' (hasTyTWeaken d hcl hrhs)
  | c, Γ, _, _, _, .iotaStarKEta _ w f A B Tm rhs u rl afs happ hA hf
        hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs => by
      have hb0 : lift (c + 1) 1 (.bvar 0 : Expr Nat) = .bvar 0 := by
        simp only [lift, if_neg (Nat.not_le_of_gt (Nat.succ_pos c) : ¬ c + 1 ≤ 0)]
      have hsrc :
          lift (c + 1) 1 (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) =
          recCall (.const (liftWitness (c + 1) w).recRef (liftWitness (c + 1) w).ls)
            (liftWitness (c + 1) w).preMajor (.bvar 0) := by
        rw [recCall_lift, hb0]; rfl
      have e2 : lift (c + 1) 1 (lift 0 1 f) = lift 0 1 (lift c 1 f) := by
        rw [show c + 1 = 1 + c from by omega,
          ← lift_lift_permute 1 1 c 0 (Nat.zero_le c) f]
      have happ' :
          recCall (.const (liftWitness (c + 1) w).recRef (liftWitness (c + 1) w).ls)
            (liftWitness (c + 1) w).preMajor (.bvar 0) =
          .app (lift 0 1 (lift c 1 f)) (.bvar 0) := by
        rw [← hsrc, happ]
        change Expr.app (lift (c + 1) 1 (lift 0 1 f)) (lift (c + 1) 1 (.bvar 0)) = _
        rw [e2, hb0]
      have hfam' : ∃ lsF, (appsSpine (lift (c + 1) 1 Tm)).1 =
          .const (liftWitness (c + 1) w).familyRef lsF := by
        obtain ⟨lsF, hlsF⟩ := hfam
        refine ⟨lsF, ?_⟩
        show (appsSpine (lift (c + 1) 1 Tm)).1 = .const w.familyRef lsF
        rw [appsSpine_lift, hlsF]; rfl
      have hmajor' := hasTyTWeaken d hcl (c := c + 1) hmajor
      have hmk' := hasTyTWeaken d hcl (c := c + 1) hmk
      have hTm0' := hasTyTWeaken d hcl (c := c + 1) hTm0
      have hlι' := hasTyTWeaken d hcl (c := c + 1) hlι
      have hlhs' := hasTyTWeaken d hcl (c := c + 1) hlhs
      have hrhs' := hasTyTWeaken d hcl (c := c + 1) hrhs
      simp only [insertAt_succ_cons, liftDecl] at hmajor' hmk' hTm0' hlι' hlhs' hrhs'
      rw [hb0] at hmajor'
      rw [← ctorMajor_lift (c + 1) w] at hmk'
      rw [← iotaLhsOf_lift (c + 1) w] at hlι'
      rw [hsrc] at hlhs'
      have hι' : DerivedIotaU E (iotaLhsOf (liftWitness (c + 1) w))
          (lift (c + 1) 1 rhs) := by
        have h := derivedIotaU_lift (c + 1) hι
        rwa [← iotaLhsOf_lift (c + 1) w] at h
      have hA' := hasTyTWeaken d hcl (c := c) hA
      have hf' := hasTyTWeaken d hcl (c := c) hf
      simp only [lift] at hf' ⊢
      exact .iotaStarKEta _ (liftWitness (c + 1) w) _ _ _ _ _ _ _ _
        happ' hA' hf' hrl hsel hfam' hmajor' hmk' hTm0' hι' hlι' hlhs' hrhs'
  | c, Γ, _, _, _, .lit _ t T hexp => by
      have hexp' := hasTyTWeaken d hcl (c := c) hexp
      rw [natExpand_lift c 1 t] at hexp'
      simp only [lift]
      rw [natExpand_lift c 1 t]
      exact .lit _ _ _ hexp'
  | c, _, _, _, _, .eta _ f f' A B hf hl => by
      have hf' := parRedT_lift d hcl hPEqL (c := c) hf
      have hl' := hasTyTWeaken d hcl (c := c) hl
      simp only [lift,
        if_neg (Nat.not_le_of_gt (Nat.succ_pos c) : ¬ c + 1 ≤ 0)]
        at hf' hl' ⊢
      have e2 : lift (c + 1) 1 (lift 0 1 f) = lift 0 1 (lift c 1 f) := by
        rw [show c + 1 = 1 + c from by omega,
          ← lift_lift_permute 1 1 c 0 (Nat.zero_le c) f]
      rw [e2] at hl' ⊢
      exact .eta _ _ _ _ _ hf' hl'
  | _, _, _, _, _, .peq _ _ _ _ h => .peq _ _ _ _ (hPEqL h)
  | _, _, _, _, _, .conv _ _ _ _ _ h hc =>
      .conv _ _ _ _ _ (parRedT_lift d hcl hPEqL h) (tyConvTWeaken d hcl hc)

/-- Argument lists under the same weakening. -/
def parRedArgsT_lift (d : LocalDecl) (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :
    {c : Nat} → {Γ : LCtx} → {xs ys : List (Expr Nat)} →
    ParRedArgsT PEq E n Γ xs ys →
    ParRedArgsT PEq E n (insertAt d c Γ)
      (xs.map (lift c 1)) (ys.map (lift c 1))
  | _, _, _, _, .nil _ => .nil _
  | _, _, _, _, .cons h t =>
      .cons (parRedT_lift d hcl hPEqL h) (parRedArgsT_lift d hcl hPEqL t)

/-- Stars under the same weakening. -/
def parRedTStar_lift (d : LocalDecl) (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :
    {c : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    ParRedTStar PEq E n Γ a b T →
    ParRedTStar PEq E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b)
      (lift c 1 T)
  | _, _, _, _, _, .refl _ _ _ h => .refl _ _ _ (hasTyTWeaken d hcl h)
  | _, _, _, _, _, .tail h hs =>
      .tail (parRedT_lift d hcl hPEqL h) (parRedTStar_lift d hcl hPEqL hs)

/-- Prefix weakening: insert `Δ` fresh decls at the top of the context
    (cutoff 0, `Δ.length` units) — the `parRed_weaken_lctx` twin. -/
def parRedT_lift_lctx (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :
    (Δ : LCtx) → {Γ : LCtx} → {a b T : Expr Nat} →
    ParRedT PEq E n Γ a b T →
    ParRedT PEq E n (Δ ++ Γ) (lift 0 Δ.length a) (lift 0 Δ.length b)
      (lift 0 Δ.length T)
  | [], _, _, _, _, h => by
      simp only [List.nil_append, List.length_nil, lift_zero]
      exact h
  | d :: Δ, Γ, a, b, T, h => by
      have ih := parRedT_lift_lctx hcl hPEqL Δ h
      have hw := parRedT_lift d hcl hPEqL (c := 0) ih
      simp only [List.cons_append, List.length_cons, insertAt_zero]
      have ha : lift 0 1 (lift 0 Δ.length a) = lift 0 (Δ.length + 1) a :=
        lift_zero_succ Δ.length a
      have hb : lift 0 1 (lift 0 Δ.length b) = lift 0 (Δ.length + 1) b :=
        lift_zero_succ Δ.length b
      have hT : lift 0 1 (lift 0 Δ.length T) = lift 0 (Δ.length + 1) T :=
        lift_zero_succ Δ.length T
      rw [← ha, ← hb, ← hT]
      exact hw

/-- `lift`-by-`Δ.length` at cutoff 0 — the raw `parRed_lift_n` alias
    twin. -/
def parRedT_lift_n (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :=
  parRedT_lift_lctx (hcl := hcl) (PEq := PEq) (E := E) (n := n) hPEqL

end Lift

section Subst

variable {E : ResolvedEnv} {n : Nat}
variable (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)

/-! ### context-shape bridges

The typed `hasTyT_substS`/`convT_substS` family is stated against
`substRemove`; the parallel-reduction templates state contexts against
`instLCtx` + `assumpPad`/`letPad`. These lemmas bridge the two
spellings. -/

/-- The hole lookup for the `assumption` pad. -/
theorem getElem?_hole_assump (Δ base : LCtx) (V : Expr Nat) :
    (Δ ++ LocalDecl.assumption V :: base)[Δ.length]? =
      some (LocalDecl.assumption V) := by
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- The hole lookup for the `letBinding` pad. -/
theorem getElem?_hole_let (Δ base : LCtx) (A w : Expr Nat) :
    (Δ ++ LocalDecl.letBinding A w :: base)[Δ.length]? =
      some (LocalDecl.letBinding A w) := by
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- `substRemove` at an `assumption` hole computes to `instLCtx ++ base`.
    `substRemove`'s `instDecl` index decrements in step with `instLCtx`'s
    `c + tail.length`, so both spell `instantiate (entries between decl
    and hole)`. -/
theorem substRemove_instLCtx (v V : Expr Nat) :
    (Δ base : LCtx) →
    substRemove v Δ.length (List.append Δ (LocalDecl.assumption V :: base)) =
      instLCtx 0 v Δ ++ base
  | [], _ => rfl
  | d :: Δ, base => by
      have h0 : List.append (d :: Δ) (LocalDecl.assumption V :: base) =
          d :: List.append Δ (LocalDecl.assumption V :: base) := rfl
      rw [h0, List.length_cons, substRemove_succ_cons]
      rw [substRemove_instLCtx v V Δ base]
      cases d <;> simp only [instLCtx, instDecl, Nat.zero_add, List.cons_append]

/-- The `letBinding`-hole twin. -/
theorem substRemove_instLCtx_let (w A : Expr Nat) :
    (Δ base : LCtx) →
    substRemove w Δ.length (List.append Δ (LocalDecl.letBinding A w :: base)) =
      instLCtx 0 w Δ ++ base
  | [], _ => rfl
  | d :: Δ, base => by
      have h0 : List.append (d :: Δ) (LocalDecl.letBinding A w :: base) =
          d :: List.append Δ (LocalDecl.letBinding A w :: base) := rfl
      rw [h0, List.length_cons, substRemove_succ_cons]
      rw [substRemove_instLCtx_let w A Δ base]
      cases d <;> simp only [instLCtx, instDecl, Nat.zero_add, List.cons_append]

/-- `substRemove` at an inner `assumption` under a pushed binder: the
    `j+1` form `ctxWfT_instLCtx`'s binder recursion needs. -/
theorem substRemove_instLCtx_cons (v V : Expr Nat) (d : LocalDecl)
    (Δ base : LCtx) :
    substRemove v (Δ.length + 1)
        (d :: List.append Δ (LocalDecl.assumption V :: base)) =
      instDecl Δ.length v d :: instLCtx 0 v Δ ++ base := by
  show instDecl Δ.length v d ::
      substRemove v Δ.length (List.append Δ (.assumption V :: base)) = _
  rw [substRemove_instLCtx]
  rfl

/-- The `letBinding`-hole twin of `substRemove_instLCtx_cons`. -/
theorem substRemove_instLCtx_let_cons (w A : Expr Nat) (d : LocalDecl)
    (Δ base : LCtx) :
    substRemove w (Δ.length + 1)
        (d :: List.append Δ (LocalDecl.letBinding A w :: base)) =
      instDecl Δ.length w d :: instLCtx 0 w Δ ++ base := by
  show instDecl Δ.length w d ::
      substRemove w Δ.length (List.append Δ (.letBinding A w :: base)) = _
  rw [substRemove_instLCtx_let]
  rfl

/-! ### TyConvT substitution wrappers

`TyConvT` transports its two endpoints by the SAME substitution (the
index is a left-face object); `convT_substS` does the work arm by arm. -/

def tyConvT_substS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {A A' : Expr Nat} →
    TyConvT E n Γ A A' → Γ[j]? = some (.assumption t) →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    TyConvT E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) A) (instantiate j (lift 0 j v) A')
  | _, _, _, _, .refl _ _, _, _ => .refl _ _
  | _, _, _, _, .of _ _ _ u c, hget, hvty =>
      .of _ _ _ u (convT_substS hcl hinst v t c hget hvty)
  | _, _, _, _, .trans _ _ _ _ c1 c2, hget, hvty =>
      .trans _ _ _ _
        (tyConvT_substS hcl hinst v t c1 hget hvty)
        (tyConvT_substS hcl hinst v t c2 hget hvty)

/-- The `letBinding`-hole twin. -/
def tyConvT_substLetS (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (t w0 : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {A A' : Expr Nat} →
    TyConvT E n Γ A A' → Γ[j]? = some (.letBinding t w0) →
    HasTyT E n (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t) →
    TyConvT E n (substRemove w0 j Γ)
      (instantiate j (lift 0 j w0) A) (instantiate j (lift 0 j w0) A')
  | _, _, _, _, .refl _ _, _, _ => .refl _ _
  | _, _, _, _, .of _ _ _ u c, hget, hvty =>
      .of _ _ _ u (convT_substLetS hcl hinst t w0 c hget hvty)
  | _, _, _, _, .trans _ _ _ _ c1 c2, hget, hvty =>
      .trans _ _ _ _
        (tyConvT_substLetS hcl hinst t w0 c1 hget hvty)
        (tyConvT_substLetS hcl hinst t w0 c2 hget hvty)

/-! ### the instantiated-into-value congruence

`convT_inst0_pair_sort` is `convTInst0ValueSort` (`RcicParRedSRTyped`)
with the endpoints' typings taken as premises instead of read off
`EnvWfT`/`InScope` — the substitution contexts supply them directly.
`convT_inst0_arg` is the general-index corollary the beta/zeta arms
consume: instantiate a stepping value `a ⇒ a'` into an arbitrary body
typed `B` under the binder, landing at `instantiate0 a B`. -/

def convT_inst0_pair_sort {Γ : LCtx}
    {A body a a' : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body (.sort w))
    (hc : ConvT E n Γ a a' A)
    (ha : HasTyT E n Γ a A) (ha' : HasTyT E n Γ a' A) :
    ConvT E n Γ (instantiate0 a body) (instantiate0 a' body) (.sort w) :=
  have l1 : ConvT E n Γ (instantiate0 a body)
      (.app (.lam A body) a) (.sort w) :=
    ConvT.symm _ _ _ _
      (ConvT.beta Γ A body a (.sort w) u hA hbody ha)
  have l2 : ConvT E n Γ (.app (.lam A body) a)
      (.app (.lam A body) a') (.sort w) :=
    ConvT.app Γ (.lam A body) (.lam A body) a a' A (.sort w)
      (ConvT.lam Γ A A body body (.sort w) u
        (ConvT.refl Γ A (.sort u) hA)
        (ConvT.refl (.assumption A :: Γ) body (.sort w) hbody))
      hc
  have l3 : ConvT E n Γ (.app (.lam A body) a')
      (instantiate0 a' body) (.sort w) :=
    ConvT.beta Γ A body a' (.sort w) u hA hbody ha'
  ConvT.trans _ _ _ _ _ l1 (ConvT.trans _ _ _ _ _ l2 l3)

/-- `instantiate0` of a stepping value at an arbitrary codomain `B`
    (sort-typed under the binder): three-beta roundtrip, the last leg's
    index moved back to `instantiate0 a B` by `tyConv` at the sort. -/
def convT_inst0_arg {Γ : LCtx}
    {A body a a' B : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B)
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort w))
    (hc : ConvT E n Γ a a' A)
    (ha : HasTyT E n Γ a A) (ha' : HasTyT E n Γ a' A) :
    ConvT E n Γ (instantiate0 a body) (instantiate0 a' body)
      (instantiate0 a B) :=
  have l1 : ConvT E n Γ (instantiate0 a body)
      (.app (.lam A body) a) (instantiate0 a B) :=
    ConvT.symm _ _ _ _
      (ConvT.beta Γ A body a B u hA hbody ha)
  have l2 : ConvT E n Γ (.app (.lam A body) a)
      (.app (.lam A body) a') (instantiate0 a B) :=
    ConvT.app Γ (.lam A body) (.lam A body) a a' A B
      (ConvT.lam Γ A A body body B u
        (ConvT.refl Γ A (.sort u) hA)
        (ConvT.refl (.assumption A :: Γ) body B hbody))
      hc
  have hidx : ConvT E n Γ (instantiate0 a' B) (instantiate0 a B)
      (.sort w) :=
    ConvT.symm _ _ _ _
      (convT_inst0_pair_sort hA hB hc ha ha')
  have l3 : ConvT E n Γ (.app (.lam A body) a')
      (instantiate0 a' body) (instantiate0 a B) :=
    ConvT.tyConv _ _ _ _ _ _
      (ConvT.beta Γ A body a' B u hA hbody ha') hidx
  ConvT.trans _ _ _ _ _ l1 (ConvT.trans _ _ _ _ _ l2 l3)

/-! ### DerivedIotaU substitution -/

/-- The `DerivedIotaU` union is context-free; substitution instantiates
    the witness and rewrites both endpoints. The `iotaLhsOf`/`iotaRhsOf`
    instantiate commutes land it on the `instWitness`/`instWitnessS`
    pair. -/
def derivedIotaU_subst (j : Nat) (s : Expr Nat) {lhs rhs : Expr Nat} :
    DerivedIotaU E lhs rhs →
    DerivedIotaU E (instantiate j s lhs) (instantiate j s rhs)
  | .ofU w => by
      rw [← iotaLhsOf_instantiate, ← iotaRhsOf_instantiate]
      exact .ofU (instWitness j s w)
  | .ofUS w => by
      rw [← iotaLhsOfS_instantiate, ← iotaRhsOfS_instantiate]
      exact .ofUS (instWitnessS j s w)

/-! ### CtxWfT under the instantiated prefix -/

/-- `CtxWfT` survives `instLCtx`: each decl's stored type/value is
    `hasTyT_substS`-transported at its own depth. -/
def ctxWfT_instLCtx (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {base : LCtx} {v V : Expr Nat} (hvty : HasTyT E n base v V) :
    (Δ : LCtx) → CtxWfT E n (Δ ++ .assumption V :: base) →
    CtxWfT E n (instLCtx 0 v Δ ++ base)
  | [], .assumption _ _ _ hΓ _ => hΓ
  | .assumption A :: Δ', .assumption _ _ _ hΓ hA => by
      have hget : (Δ' ++ LocalDecl.assumption V :: base)[Δ'.length]? =
          some (.assumption V) := getElem?_hole_assump Δ' base V
      have hvty' : HasTyT E n
          (substRemove v Δ'.length
            (List.append Δ' (LocalDecl.assumption V :: base)))
          (lift 0 Δ'.length v) (lift 0 Δ'.length V) := by
        rw [substRemove_instLCtx]
        have h0 := hasTyT_lift_lctx hcl (instLCtx 0 v Δ') hvty
        rw [instLCtx_length] at h0
        exact h0
      have hA' := hasTyT_substS hcl hinst v V hA hget hvty'
      rw [substRemove_instLCtx] at hA'
      exact .assumption _ _ _
        (ctxWfT_instLCtx hcl hinst hvty Δ' hΓ)
        (by simpa only [Nat.zero_add, instantiate] using hA')
  | .letBinding A w :: Δ', .letBinding _ _ _ _ hΓ hA hw => by
      have hget : (Δ' ++ LocalDecl.assumption V :: base)[Δ'.length]? =
          some (.assumption V) := getElem?_hole_assump Δ' base V
      have hvty' : HasTyT E n
          (substRemove v Δ'.length
            (List.append Δ' (LocalDecl.assumption V :: base)))
          (lift 0 Δ'.length v) (lift 0 Δ'.length V) := by
        rw [substRemove_instLCtx]
        have h0 := hasTyT_lift_lctx hcl (instLCtx 0 v Δ') hvty
        rw [instLCtx_length] at h0
        exact h0
      have hA' := hasTyT_substS hcl hinst v V hA hget hvty'
      have hw' := hasTyT_substS hcl hinst v V hw hget hvty'
      rw [substRemove_instLCtx] at hA' hw'
      exact .letBinding _ _ _ _
        (ctxWfT_instLCtx hcl hinst hvty Δ' hΓ)
        (by simpa only [Nat.zero_add, instantiate] using hA')
        (by simpa only [Nat.zero_add, instantiate] using hw')

/-! ### the argument-instantiation engine

`parRedT_subst_arg` is the typed `parRed_instantiate_arg`: a term `e`
typed in the SOURCE context (hole at `j`, `.assumption t`) instantiated
at the stepping pair `v ⇒ v'` gives a `ParRedT` step at the instantiated
index. It discharges `.refl` directly, and `parRedT_typed`-right of its
result supplies every right-endpoint typing (`e[s'] : T[s]`) the mixed
substitution arms need — the `hrt`/`hr`/`hred`-style premises.

`hvw` is the stepping pair lifted into the substituted context; `hΓ'wf`
is the substituted context's well-formedness (grown per binder by
`CtxWfT`'s constructors over the `instDecl`-instantiated heads). -/

/-- `hvw` under one more binder: lift the stepping pair through the
    `instDecl`-instantiated head, `substRemove_succ_cons` to re-fold the
    context. -/
def subst_arg_step_wk (d : LocalDecl) (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    {v v' t : Expr Nat} {j : Nat} {Γ : LCtx}
    (hvw : ParRedT PEq E n (substRemove v j Γ)
      (lift 0 j v) (lift 0 j v') (lift 0 j t)) :
    ParRedT PEq E n (substRemove v (j + 1) (d :: Γ))
      (lift 0 (j + 1) v) (lift 0 (j + 1) v') (lift 0 (j + 1) t) := by
  have hw := parRedT_lift (instDecl j v d) hcl hPEqL (c := 0) hvw
  simp only [substRemove_succ_cons, insertAt_zero] at hw ⊢
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
      lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v',
      lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t] at hw
  exact hw

/-- the head-substituted context's well-formedness grows by one
    `instDecl`-instantiated binder — the `CtxWfT.assumption` arm. -/
def subst_arg_wf_assump (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {v t A : Expr Nat}
    {j : Nat} {Γ : LCtx} {u : Level}
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ'wf : CtxWfT E n (substRemove v j Γ))
    (hA : HasTyT E n Γ A (.sort u)) :
    CtxWfT E n (substRemove v (j + 1) (.assumption A :: Γ)) := by
  have hA' := hasTyT_substS hcl hinst v t hA hget hvty
  rw [substRemove_succ_cons, instDecl]
  exact .assumption _ _ _ hΓ'wf hA'

/-- the `letBinding` arm — type and stored value both instantiated. -/
def subst_arg_wf_let (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {v t A w : Expr Nat}
    {j : Nat} {Γ : LCtx} {u : Level}
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ'wf : CtxWfT E n (substRemove v j Γ))
    (hA : HasTyT E n Γ A (.sort u)) (hw : HasTyT E n Γ w A) :
    CtxWfT E n (substRemove v (j + 1) (.letBinding A w :: Γ)) := by
  have hA' := hasTyT_substS hcl hinst v t hA hget hvty
  have hw' := hasTyT_substS hcl hinst v t hw hget hvty
  rw [substRemove_succ_cons, instDecl]
  exact .letBinding _ _ _ _ hΓ'wf hA' hw'

/-- `hget` under one more binder — the cons-succ `getElem?`. -/
def subst_arg_get_succ (d : LocalDecl) {t : Expr Nat} {j : Nat}
    {Γ : LCtx} (hget : Γ[j]? = some (.assumption t)) :
    (d :: Γ)[j + 1]? = some (.assumption t) := by
  rw [List.getElem?_cons_succ]; exact hget

/-- `ConvT` congruence for the mixed instantiation of a `let`-bound
    codomain: `body[v] ≡ body[v']` at `sort w`, proven as the three-leg
    ζ-roundtrip `inst0 v body ≡ letE A v body ≡ letE A v' body ≡ inst0 v'
    body`. The let-analog of `convT_inst0_pair_sort` (which β-roundtrips
    `app (lam A body)` — valid for `assumption`-bound `inst0`s). -/
def convT_inst0_let_sort (hcl : EnvClosed E) {Γ : LCtx}
    {A body value value' : Expr Nat} {u w : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.letBinding A value :: Γ) body (.sort w))
    (hc : ConvT E n Γ value value' A)
    (hv : HasTyT E n Γ value A) (hv' : HasTyT E n Γ value' A) :
    ConvT E n Γ (instantiate0 value body) (instantiate0 value' body)
      (.sort w) := by
  have hbody' : HasTyT E n (.letBinding A value' :: Γ) body (.sort w) := by
    have h0 := hasTyTConvLetAt hcl
      (ConvT.refl _ _ _ hA) (ConvT.symm _ _ _ _ hc) hv'
      (Δ := []) (e := body) (T := .sort w) hbody
    simp only [List.nil_append] at h0
    exact h0
  have l1 : ConvT E n Γ (instantiate0 value body)
      (.letE A value body) (.sort w) :=
    ConvT.symm _ _ _ _ (ConvT.zeta _ _ _ _ _ _ hA hv hbody)
  have l2 : ConvT E n Γ (.letE A value body)
      (.letE A value' body) (.sort w) :=
    ConvT.letE _ _ _ _ _ _ _ _ _
      (ConvT.refl _ _ _ hA) hc (ConvT.refl _ _ _ hbody)
  have l3 : ConvT E n Γ (.letE A value' body)
      (instantiate0 value' body) (.sort w) :=
    ConvT.zeta _ _ _ _ _ _ hA hv' hbody'
  exact .trans _ _ _ _ _ (.trans _ _ _ _ _ l1 l2) l3

/-- The engine. `hvw : v ⇒ v'` at the hole's type in the substituted
    context; `hΓ'wf` supplies `parRedT_typed`'s premise for the
    right-endpoint typings consumed by `pi`/`app`'s `hrt`. `hS` is the
    sort-regularity premise (the `Σ'`-valued `regularT` shape — every
    inhabited type inhabits a sort). -/
def parRedT_subst_arg
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqT : ∀ {Γ : LCtx} {p q T : Expr Nat},
        PEq Γ p q T →
        HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hTC : ∀ {Γ : LCtx} {a b T : Expr Nat},
        ParRedT PEq E n Γ a b T → ConvT E n Γ a b T)
    (hS : ∀ {Γ : LCtx} {e T : Expr Nat},
        HasTyT E n Γ e T → Σ' (u : Level), HasTyT E n Γ T (.sort u))
    {v v' t : Expr Nat} :
    {j : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    HasTyT E n Γ e T →
    (hget : Γ[j]? = some (.assumption t)) →
    (hvw : ParRedT PEq E n (substRemove v j Γ)
      (lift 0 j v) (lift 0 j v') (lift 0 j t)) →
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) →
    ParRedT PEq E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v') e)
      (instantiate j (lift 0 j v) T)
  | _, _, _, _, .sort _Γ l, _, _, _ => by
      simp only [instantiate]
      exact .refl _ _ _ (.sort _ _)
  | j, Γ, _, _, .bvar _ i A h, hget, hvw, _ => by
      by_cases hij : i = j
      · subst i
        rw [lookupType_get_assumption hget] at h
        injection h with h
        subst h
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (j + 1) 0 j (lift 0 j v)
          (Nat.zero_le j) (Nat.lt_succ_self j)]
        exact hvw
      · by_cases hlt : i < j
        · have hl := lookupType_substRemove_lt (v := v) hlt h
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .refl _ _ _ (.bvar _ _ _ hl)
        · have hgt : j < i := by omega
          have hl := lookupType_substRemove_gt (v := v) hgt h
          simp only [instantiate, if_neg hij, if_pos hgt]
          exact .refl _ _ _ (.bvar _ _ _ hl)
  | j, _, _, _, .const _ r ls m hres hlen hwf, _, _, _ => by
      have hm := (hinst r m hres).1 ls (lift 0 j v) j
      rw [hm]
      exact .refl _ _ _ (.const _ r ls m hres hlen hwf)
  | j, Γ, _, _, .pi _ A u B w hA hB, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvw' := subst_arg_step_wk PEq (.assumption A) hcl hPEqL hvw
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hB' := hasTyT_substS hcl hinst v t hB hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      have hsA := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS hA hget hvw hΓ'
      have hsB := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS hB hget' hvw' hwf'
      have hcA := hTC hsA
      have hcB := hTC hsB
      have hAr := (parRedT_typed hPEqT hΓ' hsA).2
      have hBr := (parRedT_typed hPEqT hwf' hsB).2
      have hBr' := hasTyTConvAssumpAt hcl (ConvT.symm _ _ _ _ hcA) (Δ := [])
        (e := instantiate (j + 1) (lift 0 (j + 1) v') B)
        (T := .sort w) (Γ := substRemove v j Γ)
        (A := instantiate j (lift 0 j v) A)
        (A' := instantiate j (lift 0 j v') A) hBr
      simp only [List.nil_append] at hBr'
      have hrt := HasTyT.pi _ _ _ _ _
        hAr hBr'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v']
      exact .pi _ _ _ _ _ _ _ hA' hcA hB' hcB hrt
  | j, Γ, _, _, .lam _ A u body B hA hbody, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvw' := subst_arg_step_wk PEq (.assumption A) hcl hPEqL hvw
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hbody' := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS hbody
        hget' hvw' hwf'
      have hsA := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS hA hget hvw hΓ'
      have hcA := hTC hsA
      have hAr := (parRedT_typed hPEqT hΓ' hsA).2
      have ⟨w, hBw⟩ := hS hbody
      have hB' := hasTyT_substS hcl hinst v t hBw hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      have hbR := (parRedT_typed hPEqT hwf' hbody').2
      have hbR' := hasTyTConvAssumpAt hcl (ConvT.symm _ _ _ _ hcA) (Δ := [])
        (e := instantiate (j + 1) (lift 0 (j + 1) v') body)
        (T := instantiate (j + 1) (lift 0 (j + 1) v) B)
        (Γ := substRemove v j Γ)
        (A := instantiate j (lift 0 j v) A)
        (A' := instantiate j (lift 0 j v') A) hbR
      simp only [List.nil_append] at hbR'
      have hrt := HasTyT.lam _ _ _ _ _
        hAr hbR'
      have hBw0 := hasTyT_substS hcl hinst v t hBw hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      simp only [substRemove_succ_cons, instDecl] at hBw0
      have hBwA' := hasTyTConvAssumpAt hcl (ConvT.symm _ _ _ _ hcA) (Δ := [])
        (e := instantiate (j + 1) (lift 0 (j + 1) v) B)
        (T := .sort w) (Γ := substRemove v j Γ)
        (A := instantiate j (lift 0 j v) A)
        (A' := instantiate j (lift 0 j v') A) hBw0
      simp only [List.nil_append] at hBwA'
      have hconv : ConvT E n (substRemove v j Γ)
          (.pi (instantiate j (lift 0 j v') A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B))
          (.pi (instantiate j (lift 0 j v) A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B)) (.sort (.imax u w)) :=
        ConvT.pi _ _ _ _ _ _ _
          (ConvT.symm _ _ _ _ hcA)
          (ConvT.refl _ _ _ hBwA')
      have hrt' := HasTyT.conv _ _ _ _ _ hrt hconv
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v']
      exact .lam _ _ _ _ _ _ _ _ hcA hA' hB' hbody' hrt'
  | j, Γ, _, _, .app _ f a A B hf ha, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have ⟨u, w, hAu, hBw, _⟩ := hasTyTInv_pi (hS hf).2 rfl
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hAu
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvw' := subst_arg_step_wk PEq (.assumption A) hcl hPEqL hvw
      have hf' := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS hf hget hvw hΓ'
      have ha' := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS ha hget hvw hΓ'
      have hB' := hasTyT_substS hcl hinst v t hBw hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hTy0 := hasTyT_subst0S hcl hinst hBw ha
      have hTy := hasTyT_substS hcl hinst v t hTy0 hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 a B) =
          instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B
      simp only [instantiate] at hTy ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy
      have hfT := parRedT_typed hPEqT hΓ' hf'
      have haT := parRedT_typed hPEqT hΓ' ha'
      have hca := hTC ha'
      have hidx := convT_inst0_arg
        (hasTyT_substS hcl hinst v t hAu hget hvty)
        hB' (.sort _ _)
        hca haT.1 haT.2
      have happT := HasTyT.app _ _ _ _ _ hfT.2 haT.2
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at happT
      have hr := HasTyT.conv _ _ _ _ _ happT
        (ConvT.symm _ _ _ _ hidx)
      have hcc : TyConvT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v) (.pi A B))
          (.pi (instantiate j (lift 0 j v) A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B)) := by
        simp only [instantiate]
        rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        exact .refl _ _
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
      exact .app _ _ _ _ _ _ _ _ _ _
        hf' hcc hB' hTy ha' hr
  | j, Γ, _, _, .letE _ A u value B body hA hv hb, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have hwf' := subst_arg_wf_let hcl hinst hget hvty hΓ' hA hv
      have hget' := subst_arg_get_succ (.letBinding A value) hget
      have hvw' := subst_arg_step_wk PEq (.letBinding A value) hcl hPEqL hvw
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hv' := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS hv hget hvw hΓ'
      have hb' := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS hb hget' hvw' hwf'
      have hsA := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS hA hget hvw hΓ'
      have hcA := hTC hsA
      have ⟨w, hBw⟩ := hS hb
      have hB' := hasTyT_substS hcl hinst v t hBw hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hTy0 := hasTyT_substLetS hcl hinst A value hBw
        List.getElem?_cons_zero (by simp only [lift_zero_idx]; exact hv)
      have hTy := hasTyT_substS hcl hinst v t hTy0 hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate 0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) B
      simp only [instantiate0, instantiate, lift_zero_idx] at hTy ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy
      -- `hrt`: letE of s'-images, index conv-moved to the left's inst0.
      have hAr := (parRedT_typed hPEqT hΓ' hsA).2
      have hvT := parRedT_typed hPEqT hΓ' hv'
      have hcv := hTC hv'
      have hvR := HasTyT.conv _ _ _ _ _ hvT.2 hcA
      have hbT := parRedT_typed hPEqT hwf' hb'
      have hbT2 := hbT.2
      simp only [substRemove_succ_cons, instDecl] at hbT2
      have hswap : HasTyT E n
          (.letBinding (instantiate j (lift 0 j v') A)
            (instantiate j (lift 0 j v') value) :: substRemove v j Γ)
          (instantiate (j + 1) (lift 0 (j + 1) v') body)
          (instantiate (j + 1) (lift 0 (j + 1) v) B) := by
        have h0 := hasTyTConvLetAt hcl (ConvT.symm _ _ _ _ hcA)
          (ConvT.symm _ _ _ _ hcv) hvR (Δ := [])
          (e := instantiate (j + 1) (lift 0 (j + 1) v') body)
          (T := instantiate (j + 1) (lift 0 (j + 1) v) B)
          (Γ := substRemove v j Γ)
          (A := instantiate j (lift 0 j v) A)
          (v := instantiate j (lift 0 j v) value)
          (A' := instantiate j (lift 0 j v') A)
          (v' := instantiate j (lift 0 j v') value) hbT2
        simp only [List.nil_append] at h0
        exact h0
      have hrt0 := HasTyT.letE _ _ _ _ _ _ hAr hvR hswap
      have hidx := convT_inst0_let_sort hcl hA' hB'
        hcv hvT.1 hvT.2
      have hrt := HasTyT.conv _ _ _ _ _ hrt0
        (ConvT.symm _ _ _ _ hidx)
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v']
      exact .letE _ _ _ _ _ _ _ _ _ _ hcA hA' hv' hB' hTy hb' hrt
  | j, _, _, _, .lit _Γ tl _T hexp, hget, hvw, hΓ'wf => by
      have hexp' := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS hexp
        hget hvw hΓ'wf
      rw [natExpand_instantiate j (lift 0 j v) tl,
          natExpand_instantiate j (lift 0 j v') tl] at hexp'
      exact .refl _ _ _
        (.lit _ _ _ ((parRedT_typed hPEqT hΓ'wf hexp').2))
  | _, _, _, _, .conv _ e A B u h hc, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have h' := parRedT_subst_arg hcl hinst hPEqL hPEqT hTC hS h hget hvw hΓ'
      have hc' := convT_substS hcl hinst v t hc hget hvty
      exact .conv _ _ _ _ _ h' (.of _ _ _ u hc')
  termination_by j Γ e T h _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-! ### `parRedT_substSame` — the uniform-instantiate main theorem

The mixed pair-substitution `a[s] ⇒ b[s']` of `parRedT_subst` factors as
`a[s] ⇒ b[s]` (uniform `s` on both endpoints — `parRedT_substSame`,
proved here) followed by `b[s] ⇒ b[s']` (`parRedT_subst_arg` on the
right-endpoint typing). The factoring is forced: `iotaStarK`'s LHS
carries `w.preMajor` (an untyped argument list) — under a mixed pair the
s-side witness can't be synthesized, so no honest single-step exists;
the uniform version is one-step everywhere (`instWitness` covers the
iota arms) and `ParRedT`-valued, so the IHs feed the ctors directly. -/

/-- `substRemove` preserves length minus one when the index is in
    bounds. -/
theorem substRemove_length (v : Expr Nat) (j : Nat) (Γ : LCtx) :
    (substRemove v j Γ).length =
      if j < Γ.length then Γ.length - 1 else Γ.length := by
  induction Γ generalizing j with
  | nil => cases j <;> simp [substRemove]
  | cons x Γ ih =>
      cases j with
      | zero => simp [substRemove]
      | succ j =>
          rw [substRemove_succ_cons, List.length_cons, ih j]
          simp only [List.length_cons]
          split <;> split <;> omega

/-- `substRemove` commutes with `drop`: entries through position `j`
    keep their `instDecl` instantiation at the shifted index; deeper
    drops land below the removed slot entirely. -/
theorem substRemove_drop (v : Expr Nat) (j k : Nat) (Γ : LCtx) :
    (substRemove v j Γ).drop k =
      if k ≤ j then substRemove v (j - k) (Γ.drop k)
      else Γ.drop (k + 1) := by
  induction Γ generalizing j k with
  | nil =>
      have hnil : ∀ m, substRemove v m ([] : LCtx) = [] := by
        intro m; cases m <;> rfl
      simp only [hnil, List.drop_nil]
      split <;> simp [hnil]
  | cons x Γ ih =>
      cases k with
      | zero => simp
      | succ k =>
          cases j with
          | zero =>
              rw [substRemove_zero_cons]
              rw [if_neg (by omega : ¬ k + 1 ≤ 0)]
              rfl
          | succ j =>
              rw [substRemove_succ_cons, List.drop_succ_cons, ih j k]
              by_cases hk : k ≤ j
              · rw [if_pos (Nat.succ_le_succ hk), if_pos hk]
                congr 1
                omega
              · rw [if_neg (by omega : ¬ k + 1 ≤ j + 1), if_neg hk]
                rfl

/-- The substituted value's typing, in below-hole form, weakens into the
    `substRemove`-context form `substS`-family lemmas consume. -/
def subst_hvty_of_drop (hcl : EnvClosed E) {v t : Expr Nat} {j : Nat}
    {Γ : LCtx} (hget : Γ[j]? = some (.assumption t))
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t) :
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) := by
  have hlt : j < Γ.length := (List.getElem?_eq_some_iff.mp hget).1
  have h1 : (substRemove v j Γ).drop j = Γ.drop (j + 1) := by
    rw [substRemove_drop, if_pos (Nat.le_refl j), Nat.sub_self]
    have hd : substRemove v 0 (Γ.drop j) = (Γ.drop j).drop 1 := by
      cases Γ.drop j <;> simp [substRemove]
    rw [hd, List.drop_drop]
  have hsplit : substRemove v j Γ =
      (substRemove v j Γ).take j ++ Γ.drop (j + 1) := by
    have hs := (List.take_append_drop j (substRemove v j Γ)).symm
    rw [h1] at hs
    exact hs
  have htake : ((substRemove v j Γ).take j).length = j := by
    rw [List.length_take, substRemove_length, if_pos hlt]
    omega
  have hwk := hasTyT_lift_lctx hcl ((substRemove v j Γ).take j) hvt
  rw [htake] at hwk
  rw [hsplit]
  exact hwk

/-- `hvty` under one more binder — `hasTyTWeaken` through the
    `instDecl`-instantiated head, lift merges re-folded. -/
def subst_hvty_wk (d : LocalDecl) (hcl : EnvClosed E)
    {v t : Expr Nat} {j : Nat} {Γ : LCtx}
    (h : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    HasTyT E n (substRemove v (j + 1) (d :: Γ))
      (lift 0 (j + 1) v) (lift 0 (j + 1) t) := by
  have hw := hasTyTWeaken (instDecl j v d) hcl (c := 0) h
  simp only [substRemove_succ_cons, insertAt_zero] at hw ⊢
  rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
      lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t] at hw
  exact hw

/-- THE UNIFORM TYPED SUBSTITUTION: `a ⇒ b` at `T` over an assumption
    hole at `j`, with `v`'s typing at the lifted domain in the
    substituted context, steps to `a[s] ⇒ b[s]` at `T[s]`. All sixteen
    arms are single steps — `iotaStarK` included (`instWitness`
    transports the witness uniformly). -/
def parRedT_substSame
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqT : ∀ {Γ : LCtx} {p q T : Expr Nat},
        PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hTC : ∀ {Γ : LCtx} {a b T : Expr Nat},
        ParRedT PEq E n Γ a b T → ConvT E n Γ a b T)
    (hS : ∀ {Γ : LCtx} {e T : Expr Nat},
        HasTyT E n Γ e T → (u : Level) ×' HasTyT E n Γ T (.sort u))
    (hPEqSub : ∀ {Γ : LCtx} {p q T : Expr Nat} {v t : Expr Nat}
        {j : Nat},
        PEq Γ p q T → Γ[j]? = some (.assumption t) →
        HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
        PEq (substRemove v j Γ) (instantiate j (lift 0 j v) p)
          (instantiate j (lift 0 j v) q)
          (instantiate j (lift 0 j v) T))
    {v t : Expr Nat} :
    {j : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    ParRedT PEq E n Γ a b T →
    (hget : Γ[j]? = some (.assumption t)) →
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) →
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t) →
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) →
    (hΓwf : CtxWfT E n Γ) →
    ParRedT PEq E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v) b)
      (instantiate j (lift 0 j v) T)
  | _,  _,  _,  _, _, ParRedT.refl _ _ _ h, hget, hvty, _, _, _ =>
      .refl _ _ _ (hasTyT_substS hcl hinst v t h hget hvty)
  | _,  _,  _,  _, _, .sortEq _ _ _ _ h hl hr, hget, hvty, _, _, _ => by
      exact .sortEq _ _ _ _ h
        (hasTyT_substS hcl hinst v t hl hget hvty)
        (hasTyT_substS hcl hinst v t hr hget hvty)
  | _,  _,  _,  _, _, .consts _ _ _ _ _ h hl hr, hget, hvty, _, _, _ => by
      exact .consts _ _ _ _ _ h
        (hasTyT_substS hcl hinst v t hl hget hvty)
        (hasTyT_substS hcl hinst v t hr hget hvty)
  | j,  Γ,  _,  _, _, .delta _ r ls m b T hres hbody htr hlen hwf hl hr,
      hget, hvty, _, _, _ => by
      have hid := (hinst r m hres).2 b hbody ls (lift 0 j v) j
      simp only [instantiate]
      rw [hid]
      have hr' := hasTyT_substS hcl hinst v t hr hget hvty
      rw [hid] at hr'
      exact .delta _ _ _ _ _ _ hres hbody htr hlen hwf
        (hasTyT_substS hcl hinst v t hl hget hvty) hr'
  | j,  Γ,  _,  _, _, .conv _ a b A A' h hc, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have h' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        h hget hvty hvt hΓ'wf hΓwf
      have hc' := tyConvT_substS hcl hinst v t hc hget hvty
      exact .conv _ _ _ _ _ h' hc'
  | j,  Γ,  _,  _, _, .lit _ tl _ hexp, hget, hvty, _, _, _ => by
      have hexp' := hasTyT_substS hcl hinst v t hexp hget hvty
      rw [natExpand_instantiate j (lift 0 j v) tl] at hexp'
      rw [natExpand_instantiate j (lift 0 j v) tl]
      exact .lit _ _ _ hexp'
  | j,  Γ,  _,  _, _, .eta _ f f' A B hf hl, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hf' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        hf hget hvty hvt hΓ'wf hΓwf
      have hl' := hasTyT_substS hcl hinst v t hl hget hvty
      simp only [instantiate,
        if_neg (Ne.symm (Nat.succ_ne_zero j) : (0 : Nat) ≠ j + 1),
        if_neg (Nat.not_lt_zero (j + 1) : ¬ j + 1 < 0)]
        at hf' hl' ⊢
      have e2 : instantiate (j + 1) (lift 0 1 (lift 0 j v)) (lift 0 1 f)
          = lift 0 1 (instantiate j (lift 0 j v) f) := by
        rw [show j + 1 = 1 + j from by omega,
          ← lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) f]
      rw [e2] at hl' ⊢
      exact .eta _ _ _ _ _ hf' hl'
  | j,  Γ,  _,  _, _, .peq _ p q _ h, hget, hvty, _, _, _ =>
      .peq _ _ _ _ (hPEqSub h hget hvty)
  | j,  Γ,  _,  _, _, .iotaSpine _ lhs lhs' rhs _ hstep hI hred hrhs,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hstep' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS
        hPEqSub hstep hget hvty hvt hΓ'wf hΓwf
      have hI' := derivedIotaU_subst j (lift 0 j v) hI
      exact .iotaSpine _ _ _ _ _ hstep' hI'
        (hasTyT_substS hcl hinst v t hred hget hvty)
        (hasTyT_substS hcl hinst v t hrhs hget hvty)
  | j,  Γ,  _,  _, _, .iotaStarK _ w major Tm rhs _ rl afs hrl hsel hfam
      hmajor hmk hTm0 hι hlι hlhs hrhs, hget, hvty, hvt, hΓ'wf, _ => by
      have hI' := derivedIotaU_subst j (lift 0 j v) hι
      rw [← iotaLhsOf_instantiate] at hI'
      have hlι' := hasTyT_substS hcl hinst v t hlι hget hvty
      rw [← iotaLhsOf_instantiate] at hlι'
      have hlhs' := hasTyT_substS hcl hinst v t hlhs hget hvty
      rw [recCall_instantiate] at hlhs'
      simp only [instantiate] at hlhs'
      rw [recCall_instantiate]
      simp only [instantiate]
      have hmk' := hasTyT_substS hcl hinst v t hmk hget hvty
      rw [← ctorMajor_instantiate] at hmk'
      have hfam' : ∃ lsF, (appsSpine (instantiate j (lift 0 j v) Tm)).1 =
          .const (instWitness j (lift 0 j v) w).familyRef lsF := by
        obtain ⟨lsF, hf⟩ := hfam
        exact ⟨lsF, by
          have := congrArg Prod.fst
            (appsSpine_instantiate_const j (lift 0 j v)
              w.familyRef lsF Tm hf)
          simp only [instWitness] at this
          exact this⟩
      exact .iotaStarK _ (instWitness j (lift 0 j v) w) _ _ _ _ _ _
        hrl hsel hfam'
        (hasTyT_substS hcl hinst v t hmajor hget hvty)
        hmk'
        (hasTyT_substS hcl hinst v t hTm0 hget hvty)
        hI' hlι' hlhs'
        (hasTyT_substS hcl hinst v t hrhs hget hvty)
  | j,  Γ,  _,  _, _, .iotaStarKEta _ w f A B Tm rhs u rl afs happ hA hf
      hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs, hget, hvty, hvt, hΓ'wf, _ => by
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hb0 : instantiate (j + 1) (lift 0 (j + 1) v) (.bvar 0 : Expr Nat) = .bvar 0 := by
        simp only [instantiate,
          if_neg (Ne.symm (Nat.succ_ne_zero j) : (0 : Nat) ≠ j + 1),
          if_neg (Nat.not_lt_zero (j + 1) : ¬ j + 1 < 0)]
      have hsrc :
          instantiate (j + 1) (lift 0 (j + 1) v)
            (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) =
          recCall (.const (instWitness (j + 1) (lift 0 (j + 1) v) w).recRef
              (instWitness (j + 1) (lift 0 (j + 1) v) w).ls)
            (instWitness (j + 1) (lift 0 (j + 1) v) w).preMajor (.bvar 0) := by
        rw [recCall_instantiate, hb0]; rfl
      have e2 : instantiate (j + 1) (lift 0 (j + 1) v) (lift 0 1 f)
          = lift 0 1 (instantiate j (lift 0 j v) f) := by
        rw [← lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          show j + 1 = 1 + j from by omega,
          ← lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) f]
      have happ' :
          recCall (.const (instWitness (j + 1) (lift 0 (j + 1) v) w).recRef
              (instWitness (j + 1) (lift 0 (j + 1) v) w).ls)
            (instWitness (j + 1) (lift 0 (j + 1) v) w).preMajor (.bvar 0) =
          .app (lift 0 1 (instantiate j (lift 0 j v) f)) (.bvar 0) := by
        rw [← hsrc, happ]
        change Expr.app (instantiate (j + 1) (lift 0 (j + 1) v) (lift 0 1 f))
          (instantiate (j + 1) (lift 0 (j + 1) v) (.bvar 0)) = _
        rw [e2, hb0]
      have hfam' : ∃ lsF, (appsSpine (instantiate (j + 1) (lift 0 (j + 1) v) Tm)).1 =
          .const (instWitness (j + 1) (lift 0 (j + 1) v) w).familyRef lsF := by
        obtain ⟨lsF, hlsF⟩ := hfam
        exact ⟨lsF, by
          have := congrArg Prod.fst
            (appsSpine_instantiate_const (j + 1) (lift 0 (j + 1) v)
              w.familyRef lsF Tm hlsF)
          simp only [instWitness] at this
          exact this⟩
      have hI' := derivedIotaU_subst (j + 1) (lift 0 (j + 1) v) hι
      rw [← iotaLhsOf_instantiate] at hI'
      have hmajor' := hasTyT_substS hcl hinst v t hmajor hget' hvty'
      have hmk' := hasTyT_substS hcl hinst v t hmk hget' hvty'
      have hTm0' := hasTyT_substS hcl hinst v t hTm0 hget' hvty'
      have hlι' := hasTyT_substS hcl hinst v t hlι hget' hvty'
      have hlhs' := hasTyT_substS hcl hinst v t hlhs hget' hvty'
      have hrhs' := hasTyT_substS hcl hinst v t hrhs hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hmajor' hmk' hTm0' hlι' hlhs' hrhs'
      rw [hb0] at hmajor'
      rw [← ctorMajor_instantiate] at hmk'
      rw [← iotaLhsOf_instantiate] at hlι'
      rw [hsrc] at hlhs'
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hf' := hasTyT_substS hcl hinst v t hf hget hvty
      simp only [instantiate] at hf' ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hf' ⊢
      exact .iotaStarKEta _ (instWitness (j + 1) (lift 0 (j + 1) v) w) _ _ _ _ _ _ _ _
        happ' hA' hf' hrl hsel hfam' hmajor' hmk' hTm0' hI' hlι' hlhs' hrhs'
  | j, Γ, _, _, _, .app _ f f' a a' A B T₀ u w hf hc hB hTy ha hr,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hf' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        hf hget hvty hvt hΓ' hΓwf
      have ha' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        ha hget hvty hvt hΓ' hΓwf
      have hpi := (hS (hasTyT_of_tyConvT
        (parRedT_typed hPEqT hΓwf hf).1 hc)).2
      have ⟨u₀, w₀, hAu, hBw, _⟩ := hasTyTInv_pi hpi rfl
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hAu
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hc' := tyConvT_substS hcl hinst v t hc hget hvty
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hTy0 := hasTyT_subst0S hcl hinst hBw
        (parRedT_typed hPEqT hΓwf ha).1
      have hTy' := hasTyT_substS hcl hinst v t hTy0 hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 a B) =
          instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B
      simp only [instantiate] at hTy' ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy' ⊢
      have happT := HasTyT.app _ _ _ _ _
        (hasTyT_of_tyConvT (parRedT_typed hPEqT hΓ' hf').2 hc')
        (parRedT_typed hPEqT hΓ' ha').2
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at happT
      have hr' := hasTyT_substS hcl hinst v t hr hget hvty
      simp only [instantiate] at hr'
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hr'
      have hcc : TyConvT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v) T₀)
          (.pi (instantiate j (lift 0 j v) A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B)) := by
        have h0 := tyConvT_substS hcl hinst v t hc hget hvty
        simp only [instantiate] at h0 ⊢
        rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
          at h0
        exact h0
      exact .app _ _ _ _ _ _ _ _ _ _ hf' hcc hB' hTy' ha' hr'
  | j,  Γ,  _,  _, _, .beta _ A body body' arg arg' B u v' w hA hB hTy hb ha
      hred, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        hb hget' hvty' hvt hwf' (.assumption _ _ _ hΓwf hA)
      have ha' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        ha hget hvty hvt hΓ' hΓwf
      have hTy' := hasTyT_substS hcl hinst v t hTy hget hvty
      have hred' := hasTyT_substS hcl hinst v t hred hget hvty
      have hcommB : instantiate j (lift 0 j v) (instantiate0 arg B) =
          instantiate0 (instantiate j (lift 0 j v) arg)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j arg (lift 0 j v)
          (Nat.zero_le j) B
      have hcommBody : instantiate j (lift 0 j v) (instantiate0 arg' body') =
          instantiate0 (instantiate j (lift 0 j v) arg')
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) body') := by
        unfold instantiate0
        exact instantiate_instantiate 0 j arg' (lift 0 j v)
          (Nat.zero_le j) body'
      simp only [instantiate] at hTy' hred' ⊢
      rw [hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy'
      rw [hcommBody, hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hred'
      rw [hcommBody, hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
      exact .beta _ _ _ _ _ _ _ _ _ _ hA' hB' hTy' hb' ha' hred'
  | j,  Γ,  _,  _, _, .lam _ A A' body body' B u v' hc hA hB hb hrt,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hcA := convT_substS hcl hinst v t hc hget hvty
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        hb hget' hvty' hvt hwf' (.assumption _ _ _ hΓwf hA)
      have hrt' := hasTyT_substS hcl hinst v t hrt hget hvty
      simp only [instantiate] at hrt' ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hrt' ⊢
      exact .lam _ _ _ _ _ _ _ _ hcA hA' hB' hb' hrt'
  | j,  Γ,  _,  _, _, .pi _ A A' B B' u v' hA hc hB hcB hrt,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hwf' := subst_arg_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := subst_arg_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hcA := convT_substS hcl hinst v t hc hget hvty
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hcB' := convT_substS hcl hinst v t hcB hget' hvty'
      have hrt' := hasTyT_substS hcl hinst v t hrt hget hvty
      simp only [instantiate, substRemove_succ_cons, instDecl]
        at hcB' hB' hrt' ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hrt' ⊢
      exact .pi _ _ _ _ _ _ _ hA' hcA hB' hcB' hrt'
  | j,  Γ,  _,  _, _, .letE _ A A' value value' body body' B u w hc hA hv hB
      hTy hb hrt, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hvl := (parRedT_typed hPEqT hΓwf hv).1
      have hwf' := subst_arg_wf_let hcl hinst hget hvty hΓ' hA hvl
      have hget' := subst_arg_get_succ (.letBinding A value) hget
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hcA := convT_substS hcl hinst v t hc hget hvty
      have hv' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        hv hget hvty hvt hΓ' hΓwf
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        hb hget' hvty' hvt hwf' (.letBinding _ _ _ _ hΓwf hA hvl)
      have hTy' := hasTyT_substS hcl hinst v t hTy hget hvty
      have hrt' := hasTyT_substS hcl hinst v t hrt hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v)
          (Nat.zero_le j) B
      simp only [instantiate] at hTy' hrt' ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy' hrt' ⊢
      exact .letE _ _ _ _ _ _ _ _ _ _ hcA hA' hv' hB' hTy' hb' hrt'
  | j,  Γ,  _,  _, _, .zeta _ A value value' body body' B u w hA hv hB hTy hb
      hred, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hvl := (parRedT_typed hPEqT hΓwf hv).1
      have hwf' := subst_arg_wf_let hcl hinst hget hvty hΓ' hA hvl
      have hget' := subst_arg_get_succ (.letBinding A value) hget
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hA' := hasTyT_substS hcl hinst v t hA hget hvty
      have hv' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        hv hget hvty hvt hΓ' hΓwf
      have hB' := hasTyT_substS hcl hinst v t hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS hPEqSub
        hb hget' hvty' hvt hwf' (.letBinding _ _ _ _ hΓwf hA hvl)
      have hTy' := hasTyT_substS hcl hinst v t hTy hget hvty
      have hred' := hasTyT_substS hcl hinst v t hred hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v)
          (Nat.zero_le j) B
      have hcomm' : instantiate j (lift 0 j v) (instantiate0 value' body') =
          instantiate0 (instantiate j (lift 0 j v) value')
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) body') := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value' (lift 0 j v)
          (Nat.zero_le j) body'
      simp only [instantiate] at hTy' hred' ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy'
      rw [hcomm', hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hred'
      rw [hcomm', hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
      exact .zeta _ _ _ _ _ _ _ _ _ hA' hv' hB' hTy' hb' hred'
  | j,  Γ,  _,  _, _, .bvarZeta _ i A val val' T h hv hl hr,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      by_cases hij : i = j
      · subst hij
        have h' : Γ[i]? = some (.letBinding A val) :=
          (List.get?_eq_getElem? Γ i).symm ▸ h
        rw [h'] at hget
        exact nomatch hget
      · by_cases hlt : i < j
        · -- the let slot sits above the hole: index keeps `i`, the
          -- stored decl is `instDecl`-instantiated, and the value step
          -- recurses in the dropped tail at the shifted hole `j-i-1`.
          simp only [instantiate, if_neg hij,
            if_neg (by omega : ¬ j < i)]
          have hlkV := lookupValue_of_get?_let h
          have hmap := lookupValue_substRemove_lt (v := v) hlt hlkV
          obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hsΓ : lift 0 (i + 1) (lift 0 (j - i - 1) v) =
              lift 0 j v := by
            have hc := lift_zero_comp (i + 1) (j - i - 1) v
            rw [show i + 1 + (j - i - 1) = j from by omega] at hc
            exact hc
          have hcomm (e : Expr Nat) :
              instantiate j (lift 0 j v) (lift 0 (i + 1) e) =
                lift 0 (i + 1)
                  (instantiate (j - i - 1) (lift 0 (j - i - 1) v) e) := by
            have h1 := lift_instantiate_high (i + 1) 0 (j - i - 1)
              (lift 0 (j - i - 1) v) (Nat.zero_le _) e
            rw [show i + 1 + (j - i - 1) = j from by omega, hsΓ] at h1
            exact h1.symm
          have hstored : stored =
              instantiate (j - i - 1) (lift 0 (j - i - 1) v) val :=
            lift_zero_amount_inj (i + 1) (heq.symm.trans (hcomm val))
          have hdrop : (substRemove v j Γ).drop (i + 1) =
              substRemove v (j - i - 1) (Γ.drop (i + 1)) := by
            rw [substRemove_drop, if_pos (by omega : i + 1 ≤ j)]
            congr 1
          have hgetD : (Γ.drop (i + 1))[j - i - 1]? =
              some (.assumption t) := by
            rw [← List.get?_eq_getElem?, get?_drop,
              show j - i - 1 + (i + 1) = j from by omega]
            exact (List.get?_eq_getElem? Γ j).symm ▸ hget
          have hvtD : HasTyT E n
              ((Γ.drop (i + 1)).drop (j - i - 1 + 1)) v t := by
            have hd : (Γ.drop (i + 1)).drop (j - i - 1 + 1) =
                Γ.drop (j + 1) := by
              rw [List.drop_drop]
              congr 1
              omega
            rw [hd]; exact hvt
          have hvtyD := subst_hvty_of_drop hcl hgetD hvtD
          have hΓwfD := ctxWfT_drop hΓwf (i + 1)
          have hΓ'wfD : CtxWfT E n
              (substRemove v (j - i - 1) (Γ.drop (i + 1))) :=
            hdrop ▸ ctxWfT_drop hΓ'wf (i + 1)
          have hv' := parRedT_substSame hcl hinst hPEqL hPEqT hTC hS
            hPEqSub hv hgetD hvtyD hvtD hΓ'wfD hΓwfD
          rw [← hdrop] at hv'
          have hA' : A' =
              instantiate (j - i - 1) (lift 0 (j - i - 1) v) A := by
            have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by
              simp only [lookupType, h]
            have hltTy := lookupType_substRemove_lt (v := v) hlt hsrc
            have hsrcTy : lookupType (substRemove v j Γ) i =
                some (lift 0 (i + 1) A') := by
              simp only [lookupType, hg']
            rw [hsrcTy] at hltTy
            have hinj := Option.some.inj hltTy
            exact lift_zero_amount_inj (i + 1)
              (hinj.trans (hcomm A))
          rw [← hstored, ← hA'] at hv'
          have hl' := hasTyT_substS hcl hinst v t hl hget hvty
          have hr' := hasTyT_substS hcl hinst v t hr hget hvty
          simp only [instantiate, if_neg hij,
            if_neg (by omega : ¬ j < i)] at hl' hr'
          rw [hcomm val'] at hr'
          exact (hcomm val') ▸
            .bvarZeta _ i A' stored
              (instantiate (j - i - 1) (lift 0 (j - i - 1) v) val') _
              hg' hv' hl' hr'
        · -- the let slot sits below the hole: index drops to `i-1`,
          -- the stored decl passes through untouched, `hv` needs no
          -- recursion (the hole is gone from the dropped tail).
          have hgt : j < i := by omega
          simp only [instantiate, if_neg hij, if_pos hgt]
          have hlkV := lookupValue_of_get?_let h
          have hmap := lookupValue_substRemove_gt (v := v) hgt hlkV
          obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hcan (e : Expr Nat) :
              instantiate j (lift 0 j v) (lift 0 (i + 1) e) =
                lift 0 i e :=
            instantiate_lift_cancel (i + 1) 0 j (lift 0 j v)
              (Nat.zero_le j) (by omega) e
          have hi1 : i - 1 + 1 = i := by omega
          have hstored : stored = val := by
            have heq' : lift 0 i stored = lift 0 i val := by
              have h1 := heq.symm.trans (hcan val)
              rwa [hi1] at h1
            exact lift_zero_amount_inj i heq'
          have hA' : A' = A := by
            have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by
              simp only [lookupType, h]
            have hltTy := lookupType_substRemove_gt (v := v) hgt hsrc
            have hsrcTy : lookupType (substRemove v j Γ) (i - 1) =
                some (lift 0 ((i - 1) + 1) A') := by
              simp only [lookupType, hg']
            rw [hsrcTy] at hltTy
            have hinj := Option.some.inj hltTy
            have heq' : lift 0 i A' = lift 0 i A := by
              have h1 := hinj.trans (hcan A)
              rwa [hi1] at h1
            exact lift_zero_amount_inj i heq'
          have hdrop : (substRemove v j Γ).drop i =
              Γ.drop (i + 1) := by
            rw [substRemove_drop, if_neg (by omega : ¬ i ≤ j)]
          have hv' : ParRedT PEq E n
              ((substRemove v j Γ).drop (i - 1 + 1)) val val' A := by
            rw [hi1]; exact hdrop ▸ hv
          have hl' := hasTyT_substS hcl hinst v t hl hget hvty
          have hr' := hasTyT_substS hcl hinst v t hr hget hvty
          simp only [instantiate, if_neg hij, if_pos hgt] at hl' hr'
          rw [hcan val'] at hr'
          have hr'' : HasTyT E n (substRemove v j Γ)
              (lift 0 (i - 1 + 1) val')
              (instantiate j (lift 0 j v) T) := by
            rw [hi1]; exact hr'
          have htgt : lift 0 i val' =
              instantiate j (lift 0 j v) (lift 0 (i + 1) val') :=
            (hcan val').symm
          rw [← hstored, ← hA'] at hv'
          exact htgt ▸ (hi1 ▸
            .bvarZeta _ (i - 1) A' stored val' _ hg' hv' hl' hr'')
  termination_by j Γ a b T h _ _ _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-- THE PAIR-SUBSTITUTION: `a ⇒ b` at `T` over an assumption hole `j`,
    with the substituted pair `v ⇒ v'`, steps to `a[s] ⇒* b[s']` at
    `T[s]` — a star because `iotaStarK`'s left endpoint is `w.preMajor`
    (untyped): no honest single-step mixed-substitute exists, so the
    honest packaging is `a[s] ⇒ b[s]` (`substSame`) then
    `b[s] ⇒ b[s']` (`subst_arg` on `b`'s carried typing). -/
def parRedT_subst
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqT : ∀ {Γ : LCtx} {p q T : Expr Nat},
        PEq Γ p q T →
        HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hTC : ∀ {Γ : LCtx} {a b T : Expr Nat},
        ParRedT PEq E n Γ a b T → ConvT E n Γ a b T)
    (hS : ∀ {Γ : LCtx} {e T : Expr Nat},
        HasTyT E n Γ e T → Σ' (u : Level), HasTyT E n Γ T (.sort u))
    (hPEqSub : ∀ {Γ : LCtx} {p q T : Expr Nat} {v t : Expr Nat}
        {j : Nat},
        PEq Γ p q T → Γ[j]? = some (.assumption t) →
        HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
        PEq (substRemove v j Γ) (instantiate j (lift 0 j v) p)
          (instantiate j (lift 0 j v) q)
          (instantiate j (lift 0 j v) T))
    {v v' t : Expr Nat}
    {j : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : ParRedT PEq E n Γ a b T)
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t)
    (hvw : ParRedT PEq E n (substRemove v j Γ)
      (lift 0 j v) (lift 0 j v') (lift 0 j t))
    (hΓ'wf : CtxWfT E n (substRemove v j Γ))
    (hΓwf : CtxWfT E n Γ) :
    ParRedTStar PEq E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v') b)
      (instantiate j (lift 0 j v) T) :=
  .tail
    (parRedT_substSame PEq hcl hinst hPEqL hPEqT hTC hS hPEqSub
      h hget hvty hvt hΓ'wf hΓwf)
    (parRedTStar_of hPEqT hΓ'wf
      (parRedT_subst_arg PEq hcl hinst hPEqL hPEqT hTC hS
        (parRedT_typed hPEqT hΓwf h).2 hget hvw hΓ'wf))

/-! ## the letBinding-hole twins

The zeta-cross-letE critical pair substitutes through a `letBinding`
hole: the removed entry IS the zeta target. The three theorems
mirror their assumption-hole siblings; `bvarZeta`'s `i = j` arm is
productive (the removed let's stored value collapses onto `v`) —
the other two cases share the same drop-surgery. -/

/-- the head-substituted context's well-formedness grows by one
    `instDecl`-instantiated binder — the `CtxWfT.assumption` arm. -/
def substLet_wf_assump (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {v t A : Expr Nat}
    {j : Nat} {Γ : LCtx} {u : Level}
    (hget : Γ[j]? = some (.letBinding t v))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ'wf : CtxWfT E n (substRemove v j Γ))
    (hA : HasTyT E n Γ A (.sort u)) :
    CtxWfT E n (substRemove v (j + 1) (.assumption A :: Γ)) := by
  have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
  rw [substRemove_succ_cons, instDecl]
  exact .assumption _ _ _ hΓ'wf hA'

/-- the `letBinding` arm — type and stored value both instantiated. -/
def substLet_wf_let (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {v t A w : Expr Nat}
    {j : Nat} {Γ : LCtx} {u : Level}
    (hget : Γ[j]? = some (.letBinding t v))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hΓ'wf : CtxWfT E n (substRemove v j Γ))
    (hA : HasTyT E n Γ A (.sort u)) (hw : HasTyT E n Γ w A) :
    CtxWfT E n (substRemove v (j + 1) (.letBinding A w :: Γ)) := by
  have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
  have hw' := hasTyT_substLetS hcl hinst t v hw hget hvty
  rw [substRemove_succ_cons, instDecl]
  exact .letBinding _ _ _ _ hΓ'wf hA' hw'

/-- `hget` under one more binder — the cons-succ `getElem?`. -/
def substLet_get_succ (d : LocalDecl) {t : Expr Nat} {j : Nat}
    {Γ : LCtx} (hget : Γ[j]? = some (.letBinding t v)) :
    (d :: Γ)[j + 1]? = some (.letBinding t v) := by
  rw [List.getElem?_cons_succ]; exact hget


/-- The substituted value's typing, in below-hole form, weakens into the
    `substRemove`-context form `substS`-family lemmas consume. -/
def subst_hvty_of_drop_let (hcl : EnvClosed E) {v t : Expr Nat} {j : Nat}
    {Γ : LCtx} (hget : Γ[j]? = some (.letBinding t v))
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t) :
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) := by
  have hlt : j < Γ.length := (List.getElem?_eq_some_iff.mp hget).1
  have h1 : (substRemove v j Γ).drop j = Γ.drop (j + 1) := by
    rw [substRemove_drop, if_pos (Nat.le_refl j), Nat.sub_self]
    have hd : substRemove v 0 (Γ.drop j) = (Γ.drop j).drop 1 := by
      cases Γ.drop j <;> simp [substRemove]
    rw [hd, List.drop_drop]
  have hsplit : substRemove v j Γ =
      (substRemove v j Γ).take j ++ Γ.drop (j + 1) := by
    have hs := (List.take_append_drop j (substRemove v j Γ)).symm
    rw [h1] at hs
    exact hs
  have htake : ((substRemove v j Γ).take j).length = j := by
    rw [List.length_take, substRemove_length, if_pos hlt]
    omega
  have hwk := hasTyT_lift_lctx hcl ((substRemove v j Γ).take j) hvt
  rw [htake] at hwk
  rw [hsplit]
  exact hwk


/-- The engine. `hvw : v ⇒ v'` at the hole's type in the substituted
    context; `hΓ'wf` supplies `parRedT_typed`'s premise for the
    right-endpoint typings consumed by `pi`/`app`'s `hrt`. `hS` is the
    sort-regularity premise (the `Σ'`-valued `regularT` shape — every
    inhabited type inhabits a sort). -/
def parRedT_substLet_arg
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqT : ∀ {Γ : LCtx} {p q T : Expr Nat},
        PEq Γ p q T →
        HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hTC : ∀ {Γ : LCtx} {a b T : Expr Nat},
        ParRedT PEq E n Γ a b T → ConvT E n Γ a b T)
    (hS : ∀ {Γ : LCtx} {e T : Expr Nat},
        HasTyT E n Γ e T → Σ' (u : Level), HasTyT E n Γ T (.sort u))
    {v v' t : Expr Nat} :
    {j : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    HasTyT E n Γ e T →
    (hget : Γ[j]? = some (.letBinding t v)) →
    (hvw : ParRedT PEq E n (substRemove v j Γ)
      (lift 0 j v) (lift 0 j v') (lift 0 j t)) →
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) →
    ParRedT PEq E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v') e)
      (instantiate j (lift 0 j v) T)
  | _, _, _, _, .sort _Γ l, _, _, _ => by
      simp only [instantiate]
      exact .refl _ _ _ (.sort _ _)
  | j, Γ, _, _, .bvar _ i A h, hget, hvw, _ => by
      by_cases hij : i = j
      · subst i
        rw [lookupType_get_letBinding hget] at h
        injection h with h
        subst h
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (j + 1) 0 j (lift 0 j v)
          (Nat.zero_le j) (Nat.lt_succ_self j)]
        exact hvw
      · by_cases hlt : i < j
        · have hl := lookupType_substRemove_lt (v := v) hlt h
          simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          exact .refl _ _ _ (.bvar _ _ _ hl)
        · have hgt : j < i := by omega
          have hl := lookupType_substRemove_gt (v := v) hgt h
          simp only [instantiate, if_neg hij, if_pos hgt]
          exact .refl _ _ _ (.bvar _ _ _ hl)
  | j, _, _, _, .const _ r ls m hres hlen hwf, _, _, _ => by
      have hm := (hinst r m hres).1 ls (lift 0 j v) j
      rw [hm]
      exact .refl _ _ _ (.const _ r ls m hres hlen hwf)
  | j, Γ, _, _, .pi _ A u B w hA hB, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have hwf' := substLet_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := substLet_get_succ (.assumption A) hget
      have hvw' := subst_arg_step_wk PEq (.assumption A) hcl hPEqL hvw
      have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
      have hB' := hasTyT_substLetS hcl hinst t v hB hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      have hsA := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS hA hget hvw hΓ'
      have hsB := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS hB hget' hvw' hwf'
      have hcA := hTC hsA
      have hcB := hTC hsB
      have hAr := (parRedT_typed hPEqT hΓ' hsA).2
      have hBr := (parRedT_typed hPEqT hwf' hsB).2
      have hBr' := hasTyTConvAssumpAt hcl (ConvT.symm _ _ _ _ hcA) (Δ := [])
        (e := instantiate (j + 1) (lift 0 (j + 1) v') B)
        (T := .sort w) (Γ := substRemove v j Γ)
        (A := instantiate j (lift 0 j v) A)
        (A' := instantiate j (lift 0 j v') A) hBr
      simp only [List.nil_append] at hBr'
      have hrt := HasTyT.pi _ _ _ _ _
        hAr hBr'
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v']
      exact .pi _ _ _ _ _ _ _ hA' hcA hB' hcB hrt
  | j, Γ, _, _, .lam _ A u body B hA hbody, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have hwf' := substLet_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := substLet_get_succ (.assumption A) hget
      have hvw' := subst_arg_step_wk PEq (.assumption A) hcl hPEqL hvw
      have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
      have hbody' := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS hbody
        hget' hvw' hwf'
      have hsA := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS hA hget hvw hΓ'
      have hcA := hTC hsA
      have hAr := (parRedT_typed hPEqT hΓ' hsA).2
      have ⟨w, hBw⟩ := hS hbody
      have hB' := hasTyT_substLetS hcl hinst t v hBw hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      have hbR := (parRedT_typed hPEqT hwf' hbody').2
      have hbR' := hasTyTConvAssumpAt hcl (ConvT.symm _ _ _ _ hcA) (Δ := [])
        (e := instantiate (j + 1) (lift 0 (j + 1) v') body)
        (T := instantiate (j + 1) (lift 0 (j + 1) v) B)
        (Γ := substRemove v j Γ)
        (A := instantiate j (lift 0 j v) A)
        (A' := instantiate j (lift 0 j v') A) hbR
      simp only [List.nil_append] at hbR'
      have hrt := HasTyT.lam _ _ _ _ _
        hAr hbR'
      have hBw0 := hasTyT_substLetS hcl hinst t v hBw hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      simp only [substRemove_succ_cons, instDecl] at hBw0
      have hBwA' := hasTyTConvAssumpAt hcl (ConvT.symm _ _ _ _ hcA) (Δ := [])
        (e := instantiate (j + 1) (lift 0 (j + 1) v) B)
        (T := .sort w) (Γ := substRemove v j Γ)
        (A := instantiate j (lift 0 j v) A)
        (A' := instantiate j (lift 0 j v') A) hBw0
      simp only [List.nil_append] at hBwA'
      have hconv : ConvT E n (substRemove v j Γ)
          (.pi (instantiate j (lift 0 j v') A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B))
          (.pi (instantiate j (lift 0 j v) A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B)) (.sort (.imax u w)) :=
        ConvT.pi _ _ _ _ _ _ _
          (ConvT.symm _ _ _ _ hcA)
          (ConvT.refl _ _ _ hBwA')
      have hrt' := HasTyT.conv _ _ _ _ _ hrt hconv
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v']
      exact .lam _ _ _ _ _ _ _ _ hcA hA' hB' hbody' hrt'
  | j, Γ, _, _, .app _ f a A B hf ha, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have ⟨u, w, hAu, hBw, _⟩ := hasTyTInv_pi (hS hf).2 rfl
      have hwf' := substLet_wf_assump hcl hinst hget hvty hΓ' hAu
      have hget' := substLet_get_succ (.assumption A) hget
      have hvw' := subst_arg_step_wk PEq (.assumption A) hcl hPEqL hvw
      have hf' := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS hf hget hvw hΓ'
      have ha' := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS ha hget hvw hΓ'
      have hB' := hasTyT_substLetS hcl hinst t v hBw hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hTy0 := hasTyT_subst0S hcl hinst hBw ha
      have hTy := hasTyT_substLetS hcl hinst t v hTy0 hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 a B) =
          instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B
      simp only [instantiate] at hTy ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy
      have hfT := parRedT_typed hPEqT hΓ' hf'
      have haT := parRedT_typed hPEqT hΓ' ha'
      have hca := hTC ha'
      have hidx := convT_inst0_arg
        (hasTyT_substLetS hcl hinst t v hAu hget hvty)
        hB' (.sort _ _)
        hca haT.1 haT.2
      have happT := HasTyT.app _ _ _ _ _ hfT.2 haT.2
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at happT
      have hr := HasTyT.conv _ _ _ _ _ happT
        (ConvT.symm _ _ _ _ hidx)
      have hcc : TyConvT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v) (.pi A B))
          (.pi (instantiate j (lift 0 j v) A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B)) := by
        simp only [instantiate]
        rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        exact .refl _ _
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
      exact .app _ _ _ _ _ _ _ _ _ _
        hf' hcc hB' hTy ha' hr
  | j, Γ, _, _, .letE _ A u value B body hA hv hb, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have hwf' := substLet_wf_let hcl hinst hget hvty hΓ' hA hv
      have hget' := substLet_get_succ (.letBinding A value) hget
      have hvw' := subst_arg_step_wk PEq (.letBinding A value) hcl hPEqL hvw
      have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
      have hv' := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS hv hget hvw hΓ'
      have hb' := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS hb hget' hvw' hwf'
      have hsA := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS hA hget hvw hΓ'
      have hcA := hTC hsA
      have ⟨w, hBw⟩ := hS hb
      have hB' := hasTyT_substLetS hcl hinst t v hBw hget'
        ((parRedT_typed hPEqT hwf' hvw').1)
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hTy0 := hasTyT_substLetS hcl hinst A value hBw
        List.getElem?_cons_zero (by simp only [lift_zero_idx]; exact hv)
      have hTy := hasTyT_substLetS hcl hinst t v hTy0 hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate 0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) B
      simp only [instantiate0, instantiate, lift_zero_idx] at hTy ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hTy
      -- `hrt`: letE of s'-images, index conv-moved to the left's inst0.
      have hAr := (parRedT_typed hPEqT hΓ' hsA).2
      have hvT := parRedT_typed hPEqT hΓ' hv'
      have hcv := hTC hv'
      have hvR := HasTyT.conv _ _ _ _ _ hvT.2 hcA
      have hbT := parRedT_typed hPEqT hwf' hb'
      have hbT2 := hbT.2
      simp only [substRemove_succ_cons, instDecl] at hbT2
      have hswap : HasTyT E n
          (.letBinding (instantiate j (lift 0 j v') A)
            (instantiate j (lift 0 j v') value) :: substRemove v j Γ)
          (instantiate (j + 1) (lift 0 (j + 1) v') body)
          (instantiate (j + 1) (lift 0 (j + 1) v) B) := by
        have h0 := hasTyTConvLetAt hcl (ConvT.symm _ _ _ _ hcA)
          (ConvT.symm _ _ _ _ hcv) hvR (Δ := [])
          (e := instantiate (j + 1) (lift 0 (j + 1) v') body)
          (T := instantiate (j + 1) (lift 0 (j + 1) v) B)
          (Γ := substRemove v j Γ)
          (A := instantiate j (lift 0 j v) A)
          (v := instantiate j (lift 0 j v) value)
          (A' := instantiate j (lift 0 j v') A)
          (v' := instantiate j (lift 0 j v') value) hbT2
        simp only [List.nil_append] at h0
        exact h0
      have hrt0 := HasTyT.letE _ _ _ _ _ _ hAr hvR hswap
      have hidx := convT_inst0_let_sort hcl hA' hB'
        hcv hvT.1 hvT.2
      have hrt := HasTyT.conv _ _ _ _ _ hrt0
        (ConvT.symm _ _ _ _ hidx)
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v']
      exact .letE _ _ _ _ _ _ _ _ _ _ hcA hA' hv' hB' hTy hb' hrt
  | j, _, _, _, .lit _Γ tl _T hexp, hget, hvw, hΓ'wf => by
      have hexp' := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS hexp
        hget hvw hΓ'wf
      rw [natExpand_instantiate j (lift 0 j v) tl,
          natExpand_instantiate j (lift 0 j v') tl] at hexp'
      exact .refl _ _ _
        (.lit _ _ _ ((parRedT_typed hPEqT hΓ'wf hexp').2))
  | _, _, _, _, .conv _ e A B u h hc, hget, hvw, hΓ'wf => by
      have hΓ' := hΓ'wf
      have hvty := (parRedT_typed hPEqT hΓ' hvw).1
      have h' := parRedT_substLet_arg hcl hinst hPEqL hPEqT hTC hS h hget hvw hΓ'
      have hc' := convT_substLetS hcl hinst t v hc hget hvty
      exact .conv _ _ _ _ _ h' (.of _ _ _ u hc')
  termination_by j Γ e T h _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)
/-- THE UNIFORM TYPED SUBSTITUTION: `a ⇒ b` at `T` over a letBinding
    hole at `j`, with `v`'s typing at the lifted domain in the
    substituted context, steps to `a[s] ⇒ b[s]` at `T[s]`. All sixteen
    arms are single steps — `iotaStarK` included (`instWitness`
    transports the witness uniformly). -/
def parRedT_substLetSame
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqT : ∀ {Γ : LCtx} {p q T : Expr Nat},
        PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hTC : ∀ {Γ : LCtx} {a b T : Expr Nat},
        ParRedT PEq E n Γ a b T → ConvT E n Γ a b T)
    (hS : ∀ {Γ : LCtx} {e T : Expr Nat},
        HasTyT E n Γ e T → (u : Level) ×' HasTyT E n Γ T (.sort u))
    (hPEqSubLet : ∀ {Γ : LCtx} {p q T : Expr Nat} {v t : Expr Nat}
        {j : Nat},
        PEq Γ p q T → Γ[j]? = some (.letBinding t v) →
        HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
        PEq (substRemove v j Γ) (instantiate j (lift 0 j v) p)
          (instantiate j (lift 0 j v) q)
          (instantiate j (lift 0 j v) T))
    {v t : Expr Nat} :
    {j : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    ParRedT PEq E n Γ a b T →
    (hget : Γ[j]? = some (.letBinding t v)) →
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) →
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t) →
    (hΓ'wf : CtxWfT E n (substRemove v j Γ)) →
    (hΓwf : CtxWfT E n Γ) →
    ParRedT PEq E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v) b)
      (instantiate j (lift 0 j v) T)
  | _,  _,  _,  _, _, ParRedT.refl _ _ _ h, hget, hvty, _, _, _ =>
      .refl _ _ _ (hasTyT_substLetS hcl hinst t v h hget hvty)
  | _,  _,  _,  _, _, .sortEq _ _ _ _ h hl hr, hget, hvty, _, _, _ => by
      exact .sortEq _ _ _ _ h
        (hasTyT_substLetS hcl hinst t v hl hget hvty)
        (hasTyT_substLetS hcl hinst t v hr hget hvty)
  | _,  _,  _,  _, _, .consts _ _ _ _ _ h hl hr, hget, hvty, _, _, _ => by
      exact .consts _ _ _ _ _ h
        (hasTyT_substLetS hcl hinst t v hl hget hvty)
        (hasTyT_substLetS hcl hinst t v hr hget hvty)
  | j,  Γ,  _,  _, _, .delta _ r ls m b T hres hbody htr hlen hwf hl hr,
      hget, hvty, _, _, _ => by
      have hid := (hinst r m hres).2 b hbody ls (lift 0 j v) j
      simp only [instantiate]
      rw [hid]
      have hr' := hasTyT_substLetS hcl hinst t v hr hget hvty
      rw [hid] at hr'
      exact .delta _ _ _ _ _ _ hres hbody htr hlen hwf
        (hasTyT_substLetS hcl hinst t v hl hget hvty) hr'
  | j,  Γ,  _,  _, _, .conv _ a b A A' h hc, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have h' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        h hget hvty hvt hΓ'wf hΓwf
      have hc' := tyConvT_substLetS hcl hinst t v hc hget hvty
      exact .conv _ _ _ _ _ h' hc'
  | j,  Γ,  _,  _, _, .lit _ tl _ hexp, hget, hvty, _, _, _ => by
      have hexp' := hasTyT_substLetS hcl hinst t v hexp hget hvty
      rw [natExpand_instantiate j (lift 0 j v) tl] at hexp'
      rw [natExpand_instantiate j (lift 0 j v) tl]
      exact .lit _ _ _ hexp'
  | j,  Γ,  _,  _, _, .eta _ f f' A B hf hl, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hf' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS
        hPEqSubLet hf hget hvty hvt hΓ'wf hΓwf
      have hl' := hasTyT_substLetS hcl hinst t v hl hget hvty
      simp only [instantiate,
        if_neg (Ne.symm (Nat.succ_ne_zero j) : (0 : Nat) ≠ j + 1),
        if_neg (Nat.not_lt_zero (j + 1) : ¬ j + 1 < 0)]
        at hf' hl' ⊢
      have e2 : instantiate (j + 1) (lift 0 1 (lift 0 j v)) (lift 0 1 f)
          = lift 0 1 (instantiate j (lift 0 j v) f) := by
        rw [show j + 1 = 1 + j from by omega,
          ← lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) f]
      rw [e2] at hl' ⊢
      exact .eta _ _ _ _ _ hf' hl'
  | j,  Γ,  _,  _, _, .peq _ p q _ h, hget, hvty, _, _, _ =>
      .peq _ _ _ _ (hPEqSubLet h hget hvty)
  | j,  Γ,  _,  _, _, .iotaSpine _ lhs lhs' rhs _ hstep hI hred hrhs,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hstep' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS
        hPEqSubLet hstep hget hvty hvt hΓ'wf hΓwf
      have hI' := derivedIotaU_subst j (lift 0 j v) hI
      exact .iotaSpine _ _ _ _ _ hstep' hI'
        (hasTyT_substLetS hcl hinst t v hred hget hvty)
        (hasTyT_substLetS hcl hinst t v hrhs hget hvty)
  | j,  Γ,  _,  _, _, .iotaStarK _ w major Tm rhs _ rl afs hrl hsel hfam
      hmajor hmk hTm0 hι hlι hlhs hrhs, hget, hvty, hvt, hΓ'wf, _ => by
      have hI' := derivedIotaU_subst j (lift 0 j v) hι
      rw [← iotaLhsOf_instantiate] at hI'
      have hlι' := hasTyT_substLetS hcl hinst t v hlι hget hvty
      rw [← iotaLhsOf_instantiate] at hlι'
      have hlhs' := hasTyT_substLetS hcl hinst t v hlhs hget hvty
      rw [recCall_instantiate] at hlhs'
      simp only [instantiate] at hlhs'
      rw [recCall_instantiate]
      simp only [instantiate]
      have hmk' := hasTyT_substLetS hcl hinst t v hmk hget hvty
      rw [← ctorMajor_instantiate] at hmk'
      have hfam' : ∃ lsF, (appsSpine (instantiate j (lift 0 j v) Tm)).1 =
          .const (instWitness j (lift 0 j v) w).familyRef lsF := by
        obtain ⟨lsF, hf⟩ := hfam
        exact ⟨lsF, by
          have := congrArg Prod.fst
            (appsSpine_instantiate_const j (lift 0 j v)
              w.familyRef lsF Tm hf)
          simp only [instWitness] at this
          exact this⟩
      exact .iotaStarK _ (instWitness j (lift 0 j v) w) _ _ _ _ _ _
        hrl hsel hfam'
        (hasTyT_substLetS hcl hinst t v hmajor hget hvty)
        hmk'
        (hasTyT_substLetS hcl hinst t v hTm0 hget hvty)
        hI' hlι' hlhs'
        (hasTyT_substLetS hcl hinst t v hrhs hget hvty)
  | j,  Γ,  _,  _, _, .iotaStarKEta _ w f A B Tm rhs u rl afs happ hA hf
      hrl hsel hfam hmajor hmk hTm0 hι hlι hlhs hrhs, hget, hvty, hvt, hΓ'wf, _ => by
      have hget' := substLet_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hb0 : instantiate (j + 1) (lift 0 (j + 1) v) (.bvar 0 : Expr Nat) = .bvar 0 := by
        simp only [instantiate,
          if_neg (Ne.symm (Nat.succ_ne_zero j) : (0 : Nat) ≠ j + 1),
          if_neg (Nat.not_lt_zero (j + 1) : ¬ j + 1 < 0)]
      have hsrc :
          instantiate (j + 1) (lift 0 (j + 1) v)
            (recCall (.const w.recRef w.ls) w.preMajor (.bvar 0)) =
          recCall (.const (instWitness (j + 1) (lift 0 (j + 1) v) w).recRef
              (instWitness (j + 1) (lift 0 (j + 1) v) w).ls)
            (instWitness (j + 1) (lift 0 (j + 1) v) w).preMajor (.bvar 0) := by
        rw [recCall_instantiate, hb0]; rfl
      have e2 : instantiate (j + 1) (lift 0 (j + 1) v) (lift 0 1 f)
          = lift 0 1 (instantiate j (lift 0 j v) f) := by
        rw [← lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v,
          show j + 1 = 1 + j from by omega,
          ← lift_instantiate_high 1 0 j (lift 0 j v) (Nat.zero_le j) f]
      have happ' :
          recCall (.const (instWitness (j + 1) (lift 0 (j + 1) v) w).recRef
              (instWitness (j + 1) (lift 0 (j + 1) v) w).ls)
            (instWitness (j + 1) (lift 0 (j + 1) v) w).preMajor (.bvar 0) =
          .app (lift 0 1 (instantiate j (lift 0 j v) f)) (.bvar 0) := by
        rw [← hsrc, happ]
        change Expr.app (instantiate (j + 1) (lift 0 (j + 1) v) (lift 0 1 f))
          (instantiate (j + 1) (lift 0 (j + 1) v) (.bvar 0)) = _
        rw [e2, hb0]
      have hfam' : ∃ lsF, (appsSpine (instantiate (j + 1) (lift 0 (j + 1) v) Tm)).1 =
          .const (instWitness (j + 1) (lift 0 (j + 1) v) w).familyRef lsF := by
        obtain ⟨lsF, hlsF⟩ := hfam
        exact ⟨lsF, by
          have := congrArg Prod.fst
            (appsSpine_instantiate_const (j + 1) (lift 0 (j + 1) v)
              w.familyRef lsF Tm hlsF)
          simp only [instWitness] at this
          exact this⟩
      have hI' := derivedIotaU_subst (j + 1) (lift 0 (j + 1) v) hι
      rw [← iotaLhsOf_instantiate] at hI'
      have hmajor' := hasTyT_substLetS hcl hinst t v hmajor hget' hvty'
      have hmk' := hasTyT_substLetS hcl hinst t v hmk hget' hvty'
      have hTm0' := hasTyT_substLetS hcl hinst t v hTm0 hget' hvty'
      have hlι' := hasTyT_substLetS hcl hinst t v hlι hget' hvty'
      have hlhs' := hasTyT_substLetS hcl hinst t v hlhs hget' hvty'
      have hrhs' := hasTyT_substLetS hcl hinst t v hrhs hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hmajor' hmk' hTm0' hlι' hlhs' hrhs'
      rw [hb0] at hmajor'
      rw [← ctorMajor_instantiate] at hmk'
      rw [← iotaLhsOf_instantiate] at hlι'
      rw [hsrc] at hlhs'
      have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
      have hf' := hasTyT_substLetS hcl hinst t v hf hget hvty
      simp only [instantiate] at hf' ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v] at hf' ⊢
      exact .iotaStarKEta _ (instWitness (j + 1) (lift 0 (j + 1) v) w) _ _ _ _ _ _ _ _
        happ' hA' hf' hrl hsel hfam' hmajor' hmk' hTm0' hI' hlι' hlhs' hrhs'
  | j, Γ, _, _, _, .app _ f f' a a' A B T₀ u w hf hc hB hTy ha hr,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hf' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        hf hget hvty hvt hΓ' hΓwf
      have ha' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        ha hget hvty hvt hΓ' hΓwf
      have hpi := (hS (hasTyT_of_tyConvT
        (parRedT_typed hPEqT hΓwf hf).1 hc)).2
      have ⟨u₀, w₀, hAu, hBw, _⟩ := hasTyTInv_pi hpi rfl
      have hwf' := substLet_wf_assump hcl hinst hget hvty hΓ' hAu
      have hget' := substLet_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hc' := tyConvT_substLetS hcl hinst t v hc hget hvty
      have hB' := hasTyT_substLetS hcl hinst t v hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hTy0 := hasTyT_subst0S hcl hinst hBw
        (parRedT_typed hPEqT hΓwf ha).1
      have hTy' := hasTyT_substLetS hcl hinst t v hTy0 hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 a B) =
          instantiate0 (instantiate j (lift 0 j v) a)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j a (lift 0 j v) (Nat.zero_le j) B
      simp only [instantiate] at hTy' ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy' ⊢
      have happT := HasTyT.app _ _ _ _ _
        (hasTyT_of_tyConvT (parRedT_typed hPEqT hΓ' hf').2 hc')
        (parRedT_typed hPEqT hΓ' ha').2
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at happT
      have hr' := hasTyT_substLetS hcl hinst t v hr hget hvty
      simp only [instantiate] at hr'
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hr'
      have hcc : TyConvT E n (substRemove v j Γ)
          (instantiate j (lift 0 j v) T₀)
          (.pi (instantiate j (lift 0 j v) A)
            (instantiate (j + 1) (lift 0 (j + 1) v) B)) := by
        have h0 := tyConvT_substLetS hcl hinst t v hc hget hvty
        simp only [instantiate] at h0 ⊢
        rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
          at h0
        exact h0
      exact .app _ _ _ _ _ _ _ _ _ _ hf' hcc hB' hTy' ha' hr'
  | j,  Γ,  _,  _, _, .beta _ A body body' arg arg' B u v' w hA hB hTy hb ha
      hred, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hwf' := substLet_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := substLet_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
      have hB' := hasTyT_substLetS hcl hinst t v hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        hb hget' hvty' hvt hwf' (.assumption _ _ _ hΓwf hA)
      have ha' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        ha hget hvty hvt hΓ' hΓwf
      have hTy' := hasTyT_substLetS hcl hinst t v hTy hget hvty
      have hred' := hasTyT_substLetS hcl hinst t v hred hget hvty
      have hcommB : instantiate j (lift 0 j v) (instantiate0 arg B) =
          instantiate0 (instantiate j (lift 0 j v) arg)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j arg (lift 0 j v)
          (Nat.zero_le j) B
      have hcommBody : instantiate j (lift 0 j v) (instantiate0 arg' body') =
          instantiate0 (instantiate j (lift 0 j v) arg')
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) body') := by
        unfold instantiate0
        exact instantiate_instantiate 0 j arg' (lift 0 j v)
          (Nat.zero_le j) body'
      simp only [instantiate] at hTy' hred' ⊢
      rw [hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy'
      rw [hcommBody, hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hred'
      rw [hcommBody, hcommB,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
      exact .beta _ _ _ _ _ _ _ _ _ _ hA' hB' hTy' hb' ha' hred'
  | j,  Γ,  _,  _, _, .lam _ A A' body body' B u v' hc hA hB hb hrt,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hwf' := substLet_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := substLet_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
      have hcA := convT_substLetS hcl hinst t v hc hget hvty
      have hB' := hasTyT_substLetS hcl hinst t v hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        hb hget' hvty' hvt hwf' (.assumption _ _ _ hΓwf hA)
      have hrt' := hasTyT_substLetS hcl hinst t v hrt hget hvty
      simp only [instantiate] at hrt' ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hrt' ⊢
      exact .lam _ _ _ _ _ _ _ _ hcA hA' hB' hb' hrt'
  | j,  Γ,  _,  _, _, .pi _ A A' B B' u v' hA hc hB hcB hrt,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hwf' := substLet_wf_assump hcl hinst hget hvty hΓ' hA
      have hget' := substLet_get_succ (.assumption A) hget
      have hvty' := subst_hvty_wk (.assumption A) hcl hvty
      have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
      have hcA := convT_substLetS hcl hinst t v hc hget hvty
      have hB' := hasTyT_substLetS hcl hinst t v hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hcB' := convT_substLetS hcl hinst t v hcB hget' hvty'
      have hrt' := hasTyT_substLetS hcl hinst t v hrt hget hvty
      simp only [instantiate, substRemove_succ_cons, instDecl]
        at hcB' hB' hrt' ⊢
      rw [lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hrt' ⊢
      exact .pi _ _ _ _ _ _ _ hA' hcA hB' hcB' hrt'
  | j,  Γ,  _,  _, _, .letE _ A A' value value' body body' B u w hc hA hv hB
      hTy hb hrt, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hvl := (parRedT_typed hPEqT hΓwf hv).1
      have hwf' := substLet_wf_let hcl hinst hget hvty hΓ' hA hvl
      have hget' := substLet_get_succ (.letBinding A value) hget
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
      have hcA := convT_substLetS hcl hinst t v hc hget hvty
      have hv' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        hv hget hvty hvt hΓ' hΓwf
      have hB' := hasTyT_substLetS hcl hinst t v hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        hb hget' hvty' hvt hwf' (.letBinding _ _ _ _ hΓwf hA hvl)
      have hTy' := hasTyT_substLetS hcl hinst t v hTy hget hvty
      have hrt' := hasTyT_substLetS hcl hinst t v hrt hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v)
          (Nat.zero_le j) B
      simp only [instantiate] at hTy' hrt' ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy' hrt' ⊢
      exact .letE _ _ _ _ _ _ _ _ _ _ hcA hA' hv' hB' hTy' hb' hrt'
  | j,  Γ,  _,  _, _, .zeta _ A value value' body body' B u w hA hv hB hTy hb
      hred, hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      have hvl := (parRedT_typed hPEqT hΓwf hv).1
      have hwf' := substLet_wf_let hcl hinst hget hvty hΓ' hA hvl
      have hget' := substLet_get_succ (.letBinding A value) hget
      have hvty' := subst_hvty_wk (.letBinding A value) hcl hvty
      have hA' := hasTyT_substLetS hcl hinst t v hA hget hvty
      have hv' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        hv hget hvty hvt hΓ' hΓwf
      have hB' := hasTyT_substLetS hcl hinst t v hB hget' hvty'
      simp only [substRemove_succ_cons, instDecl] at hB'
      have hb' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
        hb hget' hvty' hvt hwf' (.letBinding _ _ _ _ hΓwf hA hvl)
      have hTy' := hasTyT_substLetS hcl hinst t v hTy hget hvty
      have hred' := hasTyT_substLetS hcl hinst t v hred hget hvty
      have hcomm : instantiate j (lift 0 j v) (instantiate0 value B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) B) := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value (lift 0 j v)
          (Nat.zero_le j) B
      have hcomm' : instantiate j (lift 0 j v) (instantiate0 value' body') =
          instantiate0 (instantiate j (lift 0 j v) value')
            (instantiate (j + 1) (lift 0 1 (lift 0 j v)) body') := by
        unfold instantiate0
        exact instantiate_instantiate 0 j value' (lift 0 j v)
          (Nat.zero_le j) body'
      simp only [instantiate] at hTy' hred' ⊢
      rw [hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hTy'
      rw [hcomm', hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
        at hred'
      rw [hcomm', hcomm,
          lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v]
      exact .zeta _ _ _ _ _ _ _ _ _ hA' hv' hB' hTy' hb' hred'
  | j,  Γ,  _,  _, _, .bvarZeta _ i A val val' T h hv hl hr,
      hget, hvty, hvt, hΓ'wf, hΓwf => by
      have hΓ' := hΓ'wf
      by_cases hij : i = j
      · -- the removed letBinding IS this zeta step's target: `bvar i`
        -- collapses onto the substituted stored value `v`, and the
        -- stored-value step `hv` lifts over the instantiated head
        -- prefix. The type index lands on `T[s]` via the `bvar`-
        -- inversion's `TyConvT`, substituted.
        subst hij
        have hge : Γ[i]? = some (.letBinding A val) :=
          (List.get?_eq_getElem? Γ i).symm ▸ h
        rw [hget] at hge
        injection hge with hge'
        injection hge' with hA' hv0'
        subst hA' hv0'
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (i + 1) 0 i (lift 0 i v)
          (Nat.zero_le i) (Nat.lt_succ_self i)]
        have hdrop : (substRemove v i Γ).drop i = Γ.drop (i + 1) := by
          rw [substRemove_drop, if_pos (Nat.le_refl i), Nat.sub_self]
          have hd : substRemove v 0 (Γ.drop i) = (Γ.drop i).drop 1 := by
            cases Γ.drop i <;> simp [substRemove]
          rw [hd, List.drop_drop]
        have hpre : (substRemove v i Γ).take i ++ Γ.drop (i + 1) =
            substRemove v i Γ := by
          rw [← hdrop]; exact List.take_append_drop _ _
        have hlt0 : i < Γ.length := (List.getElem?_eq_some_iff.mp hget).1
        have hlen : ((substRemove v i Γ).take i).length = i := by
          rw [List.length_take, substRemove_length, if_pos hlt0]
          omega
        have hvL := parRedT_lift_lctx hcl hPEqL
          ((substRemove v i Γ).take i) hv
        rw [hlen] at hvL
        obtain ⟨A0, hlk0, hcv⟩ := hasTyTInv_bvar hl rfl
        have hlk : lookupType Γ i = some (lift 0 (i + 1) t) :=
          lookupType_get_letBinding hget
        rw [hlk] at hlk0
        injection hlk0 with hA0
        subst hA0
        have hcv' := tyConvT_substLetS hcl hinst t v hcv hget hvty
        rw [instantiate_lift_cancel (i + 1) 0 i (lift 0 i v)
          (Nat.zero_le i) (Nat.lt_succ_self i)] at hcv'
        rw [← hpre] at hcv'
        rw [← hpre]
        exact .conv _ _ _ _ _ hvL hcv'
      · by_cases hlt : i < j
        · -- the let slot sits above the hole: index keeps `i`, the
          -- stored decl is `instDecl`-instantiated, and the value step
          -- recurses in the dropped tail at the shifted hole `j-i-1`.
          simp only [instantiate, if_neg hij,
            if_neg (by omega : ¬ j < i)]
          have hlkV := lookupValue_of_get?_let h
          have hmap := lookupValue_substRemove_lt (v := v) hlt hlkV
          obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hsΓ : lift 0 (i + 1) (lift 0 (j - i - 1) v) =
              lift 0 j v := by
            have hc := lift_zero_comp (i + 1) (j - i - 1) v
            rw [show i + 1 + (j - i - 1) = j from by omega] at hc
            exact hc
          have hcomm (e : Expr Nat) :
              instantiate j (lift 0 j v) (lift 0 (i + 1) e) =
                lift 0 (i + 1)
                  (instantiate (j - i - 1) (lift 0 (j - i - 1) v) e) := by
            have h1 := lift_instantiate_high (i + 1) 0 (j - i - 1)
              (lift 0 (j - i - 1) v) (Nat.zero_le _) e
            rw [show i + 1 + (j - i - 1) = j from by omega, hsΓ] at h1
            exact h1.symm
          have hstored : stored =
              instantiate (j - i - 1) (lift 0 (j - i - 1) v) val :=
            lift_zero_amount_inj (i + 1) (heq.symm.trans (hcomm val))
          have hdrop : (substRemove v j Γ).drop (i + 1) =
              substRemove v (j - i - 1) (Γ.drop (i + 1)) := by
            rw [substRemove_drop, if_pos (by omega : i + 1 ≤ j)]
            congr 1
          have hgetD : (Γ.drop (i + 1))[j - i - 1]? =
              some (.letBinding t v) := by
            rw [← List.get?_eq_getElem?, get?_drop,
              show j - i - 1 + (i + 1) = j from by omega]
            exact (List.get?_eq_getElem? Γ j).symm ▸ hget
          have hvtD : HasTyT E n
              ((Γ.drop (i + 1)).drop (j - i - 1 + 1)) v t := by
            have hd : (Γ.drop (i + 1)).drop (j - i - 1 + 1) =
                Γ.drop (j + 1) := by
              rw [List.drop_drop]
              congr 1
              omega
            rw [hd]; exact hvt
          have hvtyD := subst_hvty_of_drop_let hcl hgetD hvtD
          have hΓwfD := ctxWfT_drop hΓwf (i + 1)
          have hΓ'wfD : CtxWfT E n
              (substRemove v (j - i - 1) (Γ.drop (i + 1))) :=
            hdrop ▸ ctxWfT_drop hΓ'wf (i + 1)
          have hv' := parRedT_substLetSame hcl hinst hPEqL hPEqT hTC hS
            hPEqSubLet hv hgetD hvtyD hvtD hΓ'wfD hΓwfD
          rw [← hdrop] at hv'
          have hA' : A' =
              instantiate (j - i - 1) (lift 0 (j - i - 1) v) A := by
            have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by
              simp only [lookupType, h]
            have hltTy := lookupType_substRemove_lt (v := v) hlt hsrc
            have hsrcTy : lookupType (substRemove v j Γ) i =
                some (lift 0 (i + 1) A') := by
              simp only [lookupType, hg']
            rw [hsrcTy] at hltTy
            have hinj := Option.some.inj hltTy
            exact lift_zero_amount_inj (i + 1)
              (hinj.trans (hcomm A))
          rw [← hstored, ← hA'] at hv'
          have hl' := hasTyT_substLetS hcl hinst t v hl hget hvty
          have hr' := hasTyT_substLetS hcl hinst t v hr hget hvty
          simp only [instantiate, if_neg hij,
            if_neg (by omega : ¬ j < i)] at hl' hr'
          rw [hcomm val'] at hr'
          exact (hcomm val') ▸
            .bvarZeta _ i A' stored
              (instantiate (j - i - 1) (lift 0 (j - i - 1) v) val') _
              hg' hv' hl' hr'
        · -- the let slot sits below the hole: index drops to `i-1`,
          -- the stored decl passes through untouched, `hv` needs no
          -- recursion (the hole is gone from the dropped tail).
          have hgt : j < i := by omega
          simp only [instantiate, if_neg hij, if_pos hgt]
          have hlkV := lookupValue_of_get?_let h
          have hmap := lookupValue_substRemove_gt (v := v) hgt hlkV
          obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
          have hcan (e : Expr Nat) :
              instantiate j (lift 0 j v) (lift 0 (i + 1) e) =
                lift 0 i e :=
            instantiate_lift_cancel (i + 1) 0 j (lift 0 j v)
              (Nat.zero_le j) (by omega) e
          have hi1 : i - 1 + 1 = i := by omega
          have hstored : stored = val := by
            have heq' : lift 0 i stored = lift 0 i val := by
              have h1 := heq.symm.trans (hcan val)
              rwa [hi1] at h1
            exact lift_zero_amount_inj i heq'
          have hA' : A' = A := by
            have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by
              simp only [lookupType, h]
            have hltTy := lookupType_substRemove_gt (v := v) hgt hsrc
            have hsrcTy : lookupType (substRemove v j Γ) (i - 1) =
                some (lift 0 ((i - 1) + 1) A') := by
              simp only [lookupType, hg']
            rw [hsrcTy] at hltTy
            have hinj := Option.some.inj hltTy
            have heq' : lift 0 i A' = lift 0 i A := by
              have h1 := hinj.trans (hcan A)
              rwa [hi1] at h1
            exact lift_zero_amount_inj i heq'
          have hdrop : (substRemove v j Γ).drop i =
              Γ.drop (i + 1) := by
            rw [substRemove_drop, if_neg (by omega : ¬ i ≤ j)]
          have hv' : ParRedT PEq E n
              ((substRemove v j Γ).drop (i - 1 + 1)) val val' A := by
            rw [hi1]; exact hdrop ▸ hv
          have hl' := hasTyT_substLetS hcl hinst t v hl hget hvty
          have hr' := hasTyT_substLetS hcl hinst t v hr hget hvty
          simp only [instantiate, if_neg hij, if_pos hgt] at hl' hr'
          rw [hcan val'] at hr'
          have hr'' : HasTyT E n (substRemove v j Γ)
              (lift 0 (i - 1 + 1) val')
              (instantiate j (lift 0 j v) T) := by
            rw [hi1]; exact hr'
          have htgt : lift 0 i val' =
              instantiate j (lift 0 j v) (lift 0 (i + 1) val') :=
            (hcan val').symm
          rw [← hstored, ← hA'] at hv'
          exact htgt ▸ (hi1 ▸
            .bvarZeta _ (i - 1) A' stored val' _ hg' hv' hl' hr'')
  termination_by j Γ a b T h _ _ _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)
/-- THE PAIR-SUBSTITUTION: `a ⇒ b` at `T` over a letBinding hole `j`,
    with the substituted pair `v ⇒ v'`, steps to `a[s] ⇒* b[s']` at
    `T[s]` — a star because `iotaStarK`'s left endpoint is `w.preMajor`
    (untyped): no honest single-step mixed-substitute exists, so the
    honest packaging is `a[s] ⇒ b[s]` (`substLetSame`) then
    `b[s] ⇒ b[s']` (`substLet_arg` on `b`'s carried typing). -/
def parRedT_substLet
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqT : ∀ {Γ : LCtx} {p q T : Expr Nat},
        PEq Γ p q T →
        HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hTC : ∀ {Γ : LCtx} {a b T : Expr Nat},
        ParRedT PEq E n Γ a b T → ConvT E n Γ a b T)
    (hS : ∀ {Γ : LCtx} {e T : Expr Nat},
        HasTyT E n Γ e T → Σ' (u : Level), HasTyT E n Γ T (.sort u))
    (hPEqSubLet : ∀ {Γ : LCtx} {p q T : Expr Nat} {v t : Expr Nat}
        {j : Nat},
        PEq Γ p q T → Γ[j]? = some (.letBinding t v) →
        HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
        PEq (substRemove v j Γ) (instantiate j (lift 0 j v) p)
          (instantiate j (lift 0 j v) q)
          (instantiate j (lift 0 j v) T))
    {v v' t : Expr Nat}
    {j : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : ParRedT PEq E n Γ a b T)
    (hget : Γ[j]? = some (.letBinding t v))
    (hvty : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvt : HasTyT E n (Γ.drop (j + 1)) v t)
    (hvw : ParRedT PEq E n (substRemove v j Γ)
      (lift 0 j v) (lift 0 j v') (lift 0 j t))
    (hΓ'wf : CtxWfT E n (substRemove v j Γ))
    (hΓwf : CtxWfT E n Γ) :
    ParRedTStar PEq E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v') b)
      (instantiate j (lift 0 j v) T) :=
  .tail
    (parRedT_substLetSame PEq hcl hinst hPEqL hPEqT hTC hS hPEqSubLet
      h hget hvty hvt hΓ'wf hΓwf)
    (parRedTStar_of hPEqT hΓ'wf
      (parRedT_substLet_arg PEq hcl hinst hPEqL hPEqT hTC hS
        (parRedT_typed hPEqT hΓwf h).2 hget hvw hΓ'wf))


end Subst

end Rcic.Declarative

