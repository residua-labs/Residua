import rcic.RcicAnnRecPins
import rcic.RcicAnnFamHeight
import rcic.RcicAnnSortUniq
import rcic.RcicAnnTyRed

/-!
# Arc D — the group's built member types, typed from the views

`ctorTypeA` and `groupRecTypeA` are typed from `FamViewA` / `CtorViewA` / `FieldsTyA`,
by the copy's substitution (`hasTyA_substA`), Π-inversion (`hasTyA_pi_parts`) and
weakening. The mirror conversion is collapsed in the base environment, before the
extension. That collapse asks only for sort uniqueness (`ViewTySortUniqA`).
`ctorViewA_hasTy` and `groupRecTypeA_hasTy` obtain it from `sortUniqA` at the
interface `I`, and still take `EnvSemA` and `PosValA`. No premise is a typing of
the built constructor type or of `groupRecTypeA`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) a Π-spine ending in a sort -/

/-! ## (2) canonical levels are the identity; the level context weakens -/

section LevelWk
variable {E : ResolvedEnvA} {I : IotaIfaceA}

mutual

/-- the level context is read only by `const`, `δ` and `consts`, as a bound.
    The same walk is `hasTyA_lvlWk` in `RcicAnnEnvBridge`; this arc does not import
    that module (it treats these typings as hypotheses). -/
def viewTy_lvlWk {a b : Nat} (hab : a ≤ b) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E I a Γ e A → HasTyA E I b Γ e A
  | _, _, _, .sort Γ l => .sort Γ l
  | _, _, _, .bvar Γ i A u h hA => .bvar Γ i A u h (viewTy_lvlWk hab hA)
  | _, _, _, .const Γ r ls m u hres hlen hwf hT =>
      .const Γ r ls m u hres hlen (viewTy_levelsBounded_mono hab ls hwf) (viewTy_lvlWk hab hT)
  | _, _, _, .pi Γ A u B v hA hB =>
      .pi Γ A u B v (viewTy_lvlWk hab hA) (viewTy_lvlWk hab hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      .lam Γ A u body B v (viewTy_lvlWk hab hA) (viewTy_lvlWk hab hB) (viewTy_lvlWk hab hbody)
  | _, _, _, .app Γ f x A B u v w hB hTy hf ha =>
      .app Γ f x A B u v w (viewTy_lvlWk hab hB) (viewTy_lvlWk hab hTy) (viewTy_lvlWk hab hf)
        (viewTy_lvlWk hab ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb =>
      .letE Γ A u w value B body (viewTy_lvlWk hab hA) (viewTy_lvlWk hab hv)
        (viewTy_lvlWk hab hTy) (viewTy_lvlWk hab hb)
  | _, _, _, .lit Γ t T hexp => .lit Γ t T (viewTy_lvlWk hab hexp)
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hc =>
      .conv Γ e A B l u (viewTy_lvlWk hab h) (viewTy_lvlWk hab hAl) hlu (viewTy_lvlWk hab hB)
        (viewTy_convLvlWk hab hc)

def viewTy_convLvlWk {a b : Nat} (hab : a ≤ b) :
    {Γ : LCtxA} → {x y A : ExprA} → ConvA E I a Γ x y A → ConvA E I b Γ x y A
  | _, _, _, _, .refl Γ x A h => .refl Γ x A (viewTy_lvlWk hab h)
  | _, _, _, _, .symm Γ x y A h => .symm Γ x y A (viewTy_convLvlWk hab h)
  | _, _, _, _, .trans Γ x y z A h1 h2 =>
      .trans Γ x y z A (viewTy_convLvlWk hab h1) (viewTy_convLvlWk hab h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred =>
      .beta Γ A u body arg B (viewTy_lvlWk hab hA) (viewTy_lvlWk hab hbody)
        (viewTy_lvlWk hab harg) (viewTy_lvlWk hab hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred =>
      .zeta Γ A value body B u (viewTy_lvlWk hab hA) (viewTy_lvlWk hab hv) (viewTy_lvlWk hab hb)
        (viewTy_lvlWk hab hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      .zetaLocal Γ i A v hval hty (viewTy_lvlWk hab hv)
  | _, _, _, _, .delta Γ r ls m b' hres hbody htr hlen hwf hb =>
      .delta Γ r ls m b' hres hbody htr hlen (viewTy_levelsBounded_mono hab ls hwf)
        (viewTy_lvlWk hab hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota Γ lhs rhs T h (viewTy_lvlWk hab hlhs) (viewTy_lvlWk hab hrhs)
  | _, _, _, _, .structIota Γ f x rhs e T hrec hs h hlhs hrhs hcv =>
      .structIota Γ f x rhs e T hrec hs h (viewTy_lvlWk hab hlhs) (viewTy_lvlWk hab hrhs)
        (viewTy_convLvlWk hab hcv)
  | _, _, _, _, .lit Γ t T hexp => .lit Γ t T (viewTy_lvlWk hab hexp)
  | _, _, _, _, .app Γ f g x y A B u v h1 h2 hB hrt =>
      .app Γ f g x y A B u v (viewTy_convLvlWk hab h1) (viewTy_convLvlWk hab h2)
        (viewTy_lvlWk hab hB) (viewTy_lvlWk hab hrt)
  | _, _, _, _, .lam Γ A A' b₁ b₂ B u u' v hu hA hb hrt =>
      .lam Γ A A' b₁ b₂ B u u' v hu (viewTy_convLvlWk hab hA) (viewTy_convLvlWk hab hb)
        (viewTy_lvlWk hab hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      .pi Γ A A' B B' u u' v v' hu hv (viewTy_convLvlWk hab hA) (viewTy_convLvlWk hab hB)
        (viewTy_lvlWk hab hrt)
  | _, _, _, _, .letE Γ A A' v v' b₁ b₂ B u hA hv hb hrt =>
      .letE Γ A A' v v' b₁ b₂ B u (viewTy_convLvlWk hab hA) (viewTy_convLvlWk hab hv)
        (viewTy_convLvlWk hab hb) (viewTy_lvlWk hab hrt)
  | _, _, _, _, .sorts Γ l₁ l₂ h => .sorts Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h hrt =>
      .consts Γ r ls ls' m hres hlen (viewTy_levelsBounded_mono hab ls hwf)
        (viewTy_levelsBounded_mono hab ls' hwf') h (viewTy_lvlWk hab hrt)
  | _, _, _, _, .eta Γ f A B u v h hrt =>
      .eta Γ f A B u v (viewTy_lvlWk hab h) (viewTy_lvlWk hab hrt)
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr Γ P p q (viewTy_lvlWk hab hP) (viewTy_lvlWk hab hp) (viewTy_lvlWk hab hq)
  | _, _, _, _, .tyConv Γ x y A A' l l' u h hAl hlu hA'l hl'u hA =>
      .tyConv Γ x y A A' l l' u (viewTy_convLvlWk hab h) (viewTy_lvlWk hab hAl) hlu
        (viewTy_lvlWk hab hA'l) hl'u (viewTy_convLvlWk hab hA)

end

end LevelWk

/-! ## (3) one binder that is not a plain variable; the parameter-local step -/

section SubstShift
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end SubstShift

/-! ## (4) domains, and moving a derivation into a larger environment -/

section Dom
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end Dom

section EnvMove
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end EnvMove

/-! ## (5) a constant, or a term already at a Π, applied along the telescope -/

section Fold
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end Fold

/-! ## (6) mirror conversions, collapsed in the base, then the identity substitution -/

/-- sort uniqueness at one interface. The mirror walk uses `EnvSemA` only to obtain this. -/
abbrev ViewTySortUniqA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ {Γ : LCtxA} {X : ExprA} {a b : Level},
    CtxWfA E I n Γ → HasTyA E I n Γ X (.sort a) → HasTyA E I n Γ X (.sort b) → eqN a b

section Mirrors
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- a type on the left of a `TyConvA`, typed at a sort `=ₙ` the right-hand sort.
    `Prod` cannot pair the derivation (`Type`) with `eqN` (`Prop`). -/
structure ViewTyLeftA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA)
    (A : ExprA) (lb : Level) : Type where
  la : Level
  ty : HasTyA E I n Γ A (.sort la)
  heq : eqN la lb

/-- `tyConvA_collapse`, with `sortUniqA` replaced by the uniqueness it was called for. -/
def viewTy_collapse (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (huniq : ViewTySortUniqA E I n) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) :
    {A B : ExprA} → TyConvA E I n Γ A B → {l : Level} → HasTyA E I n Γ A (.sort l) →
      ConvA E I n Γ A B (.sort l)
  | _, _, .refl _ A, _, hA => .refl Γ A _ hA
  | _, _, .of _ _ _ _ _ _ hAl₀ hlu _ _ h, _, hA =>
      convA_sort_eqN h (eqNA_trans (eqNA_symm hlu)
        (eqNA_symm (huniq hΓ hA hAl₀)))
  | _, _, .trans _ A B C h1 h2, _, hA =>
      let c1 := viewTy_collapse hE hI hIS hR huniq hΓ h1 hA
      .trans Γ A B C _ c1
        (viewTy_collapse hE hI hIS hR huniq hΓ h2 (convA_hasTy_right hE hI hR hIS hΓ c1))

def viewTy_leftSort (huniq : ViewTySortUniqA E I n) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) :
    {A B : ExprA} → TyConvA E I n Γ A B → {lb : Level} → HasTyA E I n Γ B (.sort lb) →
    ViewTyLeftA E I n Γ A lb
  | _, _, .refl _ _, lb, hB => ⟨lb, hB, eqNA_refl _⟩
  | _, _, .of _ _ _ l _ _ hAl hlu hBl hl'u _, _, hB =>
      ⟨l, hAl, eqNA_trans hlu (eqNA_trans (eqNA_symm hl'u) (huniq hΓ hBl hB))⟩
  | _, _, .trans _ _ _ _ h1 h2, _, hC =>
      let s2 := viewTy_leftSort huniq hΓ h2 hC
      let s1 := viewTy_leftSort huniq hΓ h1 s2.ty
      ⟨s1.la, s1.ty, eqNA_trans s1.heq s2.heq⟩

/-- `id` extended by one convertible pair. The new variable is the mirror, converted
    to the parameter it stands for (`SubstA.id_up`, no function extensionality). -/
def viewTy_idCons (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {M P : ExprA}
    {um : Level} (hσ : SubstTyA E I n Δ SubstA.id Γ)
    (hM : HasTyA E I n Δ M (.sort um)) (hP : HasTyA E I n Δ P (.sort um))
    (hc : ConvA E I n Δ M P (.sort um)) :
    SubstTyA E I n (.assumption M :: Δ) SubstA.id (.assumption P :: Γ) where
  ty := fun i B hlu => by
    cases i with
    | zero =>
        have hB : B = liftA 0 1 P := lookupTypeA_zero_assumption_eq hlu
        subst hB
        rw [SubstA.id_apply, substA_id]
        exact .conv _ (.bvar 0) (liftA 0 1 M) (liftA 0 1 P) um um
          (.bvar _ 0 _ um (lookupTypeA_cons_zero_assumption M Δ)
            (hasTyWeakenA hE hI (.assumption M) (Nat.zero_le _) hM))
          (hasTyWeakenA hE hI (.assumption M) (Nat.zero_le _) hM) (eqNA_refl _)
          (hasTyWeakenA hE hI (.assumption M) (Nat.zero_le _) hP)
          (convWeakenA hE hI (.assumption M) (Nat.zero_le _) hc)
    | succ i =>
        have hs := substTyA_succ hE hI hσ (.assumption M) (.assumption P) i B hlu
        rw [SubstA.id_up, substA_ext SubstA.id_up] at hs
        exact hs
  val := fun i B v hty hval => by
    cases i with
    | zero => exact (lookupValueA_zero_assumption_none hval).elim
    | succ i =>
        have hv := substTyA_succ_val hE hI hσ (.assumption M) (.assumption P) i B v hty hval
        rw [SubstA.id_up, substA_ext SubstA.id_up, substA_ext SubstA.id_up] at hv
        exact hv

structure MirrorPackA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Δ Γ : LCtxA)
    (ms ps : List (ExprA × Level)) (B : ExprA) : Type where
  substTy : SubstTyA E I n (telCtxA ms ++ Δ) SubstA.id (telCtxA ps ++ Γ)
  ctxM : CtxWfA E I n (telCtxA ms ++ Δ)
  ctxP : CtxWfA E I n (telCtxA ps ++ Γ)
  body : Σ s : Level, HasTyA E I n (telCtxA ps ++ Γ) B (.sort s)
  dom : DomTyA E I n Δ ms

def viewTy_mirrors (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (huniq : ViewTySortUniqA E I n) {Γ Δ : LCtxA}
    {B : ExprA} {wb u : Level} {ms ps : List (ExprA × Level)}
    (hσ : SubstTyA E I n Δ SubstA.id Γ)
    (hΓ : CtxWfA E I n Γ) (hΔ : CtxWfA E I n Δ)
    (hT : HasTyA E I n Γ (piTelA ps B wb).1 (.sort u))
    (hm : MirrorsConvA E I n Γ ms ps) :
    MirrorPackA E I n Δ Γ ms ps B :=
  match ms, ps, hm with
  | [], [], .nil _ => ⟨hσ, hΔ, hΓ, ⟨u, by simpa [piTelA, telCtxA] using hT⟩, .nil _⟩
  | (M, um) :: ms, (P, up) :: ps, .cons _ _ _ _ _ _ _ hc hl tl => by
      obtain ⟨tP, tRest⟩ := hasTyA_pi_parts hT
      let left := viewTy_leftSort huniq hΓ hc tP
      have hM : HasTyA E I n Γ M (.sort um) :=
        hasTyA_retype_sort left.ty (eqNA_trans left.heq (eqNA_symm hl))
      have hPum : HasTyA E I n Γ P (.sort um) := hasTyA_retype_sort tP (eqNA_symm hl)
      have hcv : ConvA E I n Γ M P (.sort um) :=
        viewTy_collapse hE hI hIS hR huniq hΓ hc hM
      have hMΔ : HasTyA E I n Δ M (.sort um) := by
        have h := hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ hM
        rw [substA_id, substA_sort] at h
        exact h
      have hPΔ : HasTyA E I n Δ P (.sort um) := by
        have h := hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ hPum
        rw [substA_id, substA_sort] at h
        exact h
      have hcvΔ : ConvA E I n Δ M P (.sort um) := by
        have h := convA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ hcv
        rw [substA_id, substA_id, substA_sort] at h
        exact h
      have hσ' := viewTy_idCons hE hI hσ hMΔ hPΔ hcvΔ
      have hΓ' : CtxWfA E I n (.assumption P :: Γ) := .assumption hΓ tP
      have hΔ' : CtxWfA E I n (.assumption M :: Δ) := .assumption hΔ hMΔ
      have ih := viewTy_mirrors hE hI hIS hR huniq hσ' hΓ' hΔ' tRest tl
      exact ⟨
        (telCtxA_cons_append (M, um) ms Δ).symm ▸
          ((telCtxA_cons_append (P, up) ps Γ).symm ▸ ih.substTy),
        (telCtxA_cons_append (M, um) ms Δ).symm ▸ ih.ctxM,
        (telCtxA_cons_append (P, up) ps Γ).symm ▸ ih.ctxP,
        ⟨ih.body.1, (telCtxA_cons_append (P, up) ps Γ).symm ▸ ih.body.2⟩,
        .cons _ M um ms hMΔ ih.dom⟩

end Mirrors

/-! ## (7) one plain binder: the family application and the index telescope step together -/

section IdxStep
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end IdxStep

/-! ## (8) the fields, in the telescope context, by the plain substitution -/

section Fields
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end Fields

/-! ## (8) T1: a constructor view's built type is typed in the family's extension -/

section T1
variable {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm cm : CheckedMemberA}

theorem ctorViewA_hasTy_ofUniq {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm) {u : Level}
    (hFam : HasTyA E I fm.arity [] fm.mtypeA (.sort u)) (hfr : E.members f = none)
    (hE : EnvClosedA E) (hEx : EnvClosedA (extendEnvA E f fm))
    (hIl : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hRx : IotaRecHeadA (extendEnvA E f fm) I)
    (huniq : ViewTySortUniqA E I fm.arity) :
    ∃ w : Level, Nonempty (HasTyA (extendEnvA E f fm) I fm.arity []
      (ctorTypeA f (canonLevelsA fm.arity) fv.sort v.mirrors v.fields v.res) (.sort w)) := by
  -- the stored type converts to the normed one (`v.normConv`) and the normed side is typed
  -- (`v.normTyped`, assembled at the bridge); the raw side follows by `tyConvA_typed_left`
  -- (R-NoDeltaRec-4d-iii — `.drecD` is no longer vacuous).
  obtain ⟨_, ⟨hN⟩⟩ := v.normTyped
  obtain ⟨tc⟩ := v.normConv
  exact tyConvA_typed_left tc hN

theorem ctorViewA_hasTy_der {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm) {u : Level}
    (hFam : HasTyA E I fm.arity [] fm.mtypeA (.sort u)) (hfr : E.members f = none)
    (hE : EnvClosedA E) (hEx : EnvClosedA (extendEnvA E f fm))
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIl : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hRx : IotaRecHeadA (extendEnvA E f fm) I)
    {ρ₀ : Nat → Nat} (hS : EnvSemA E I fm.arity ρ₀) (hρ : PosValA ρ₀) :
    ∃ w : Level, Nonempty (HasTyA (extendEnvA E f fm) I fm.arity []
      (ctorTypeA f (canonLevelsA fm.arity) fv.sort v.mirrors v.fields v.res) (.sort w)) :=
  ctorViewA_hasTy_ofUniq v hFam hfr hE hEx hIl hIS hR hRx (by
    intro Γ X a b hΓ ha hb
    exact sortUniqA hE hIl hIS hEN hNC hR hS hρ hΓ ha hb)

theorem ctorViewA_hasTy {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm) {u : Level}
    (hFam : HasTyA E I fm.arity [] fm.mtypeA (.sort u)) (hfr : E.members f = none)
    (hE : EnvClosedA E) (hEx : EnvClosedA (extendEnvA E f fm))
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hIl : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hRx : IotaRecHeadA (extendEnvA E f fm) I)
    {ρ₀ : Nat → Nat} (hS : EnvSemA E I fm.arity ρ₀) (hρ : PosValA ρ₀) :
    ∃ w, Nonempty (HasTyA (extendEnvA E f fm) I fm.arity []
      (ctorTypeA f (canonLevelsA fm.arity) fv.sort v.mirrors v.fields v.res) (.sort w)) :=
  ctorViewA_hasTy_der v hFam hfr hE hEx hEN hNC hIl hIS hR hRx hS hρ

end T1

/-! ## (9) T1's teeth. Each conclusion is the member's stored type. None cites
    `pinBoxCtorTy`, `pinSuccPiTy`, or a `GroupCtorA.hT`. -/

section Teeth
variable (I : IotaIfaceA)

theorem viewTy_natFamClosed : EnvClosedA (extendEnvA emptyEnvA 10 pinNatFamA) := by
  intro r m hm
  by_cases hr : r = 10
  · subst hr
    cases hm
    exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  · rw [members_extendEnvA_ne emptyEnvA 10 pinNatFamA hr] at hm
    exact Option.noConfusion hm

def viewTy_natFamTy (E : ResolvedEnvA) (n : Nat) (Γ : LCtxA) :
    HasTyA E noIotaA n Γ pinNatFamA.mtypeA (.sort (.succ (.succ .zero))) :=
  .sort Γ (.succ .zero)

end Teeth

theorem ctorViewA_box_tooth :
    ∃ w, Nonempty (HasTyA (extendEnvA emptyEnvA 0 (pinFamFA 1)) noIotaA (pinFamFA 1).arity []
      pinBoxCtorA.mtypeA (.sort w)) := by
  obtain ⟨w, ⟨d⟩⟩ := ctorViewA_hasTy_der pinBoxViewA (pinFamFTypeTy 1 emptyEnvA 0 []) rfl
    emptyEnvA_closed (pinFamF_closed 1) (fun _ _ h => Option.noConfusion h)
    (fun _ _ h => Option.noConfusion h) noIotaA_lift noIotaA_subst
    (noIotaA_recHead emptyEnvA) (noIotaA_recHead (extendEnvA emptyEnvA 0 (pinFamFA 1)))
    (emptyEnvA_sem noIotaA 0 (fun _ => 1)) posValA_one
  exact ⟨w, ⟨pinBoxViewA.stored.symm ▸ d⟩⟩

theorem ctorViewA_succ_tooth :
    ∃ w, Nonempty (HasTyA (extendEnvA emptyEnvA 10 pinNatFamA) noIotaA pinNatFamA.arity []
      pinSuccA.mtypeA (.sort w)) := by
  obtain ⟨w, ⟨d⟩⟩ := ctorViewA_hasTy_der (pinNatSuccViewA noIotaA) (viewTy_natFamTy emptyEnvA 0 []) rfl
    emptyEnvA_closed viewTy_natFamClosed (fun _ _ h => Option.noConfusion h)
    (fun _ _ h => Option.noConfusion h) noIotaA_lift noIotaA_subst
    (noIotaA_recHead emptyEnvA) (noIotaA_recHead (extendEnvA emptyEnvA 10 pinNatFamA))
    (emptyEnvA_sem noIotaA 0 (fun _ => 1)) posValA_one
  exact ⟨w, ⟨(pinNatSuccViewA noIotaA).stored.symm ▸ d⟩⟩

/-! one index, one directly recursive field `F (Sort 0)`, result `F (Sort 0)`. -/

def viewTy_idxArgs : ArgsTyA emptyEnvA noIotaA 0 [] pinFamF0ViewA.idxTelA [.sort .zero] :=
  .cons (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort .zero) [] (.sort [] .zero) (.nil (.succ .zero))

def viewTy_idxCtorA : CheckedMemberA where
  mclass := .constructorM
  arity := 0
  mtypeA := ctorTypeA 0 (canonLevelsA (pinFamFA 0).arity) pinFamF0ViewA.sort []
    [.drec [.sort .zero]] [.sort .zero]
  bodyA := none
  nparamsA := 0
  normA := some (ctorTypeA 0 (canonLevelsA (pinFamFA 0).arity) pinFamF0ViewA.sort []
    [.drec [.sort .zero]] [.sort .zero])

/-- the idx constructor's stored type, typed: `F (Sort 0) → F (Sort 0)`. It has no δ-reached field,
    so it is also the normed type — `viewTy_idxViewA.normTyped` and `viewTy_idxGroupCtorA.hT` share
    this derivation. -/
def viewTy_idxCtorTy : HasTyA (extendEnvA emptyEnvA 0 (pinFamFA 0)) noIotaA (pinFamFA 0).arity []
    viewTy_idxCtorA.mtypeA (.sort (.imax (.succ .zero) (.succ .zero))) :=
  HasTyA.pi [] _ _ _ _
    (pinFamFAppTy (members_extendEnvA_self emptyEnvA 0 (pinFamFA 0)) (pinFamFA 0).arity [])
    (pinFamFAppTy (members_extendEnvA_self emptyEnvA 0 (pinFamFA 0)) (pinFamFA 0).arity
      [.assumption _])

def viewTy_idxViewA : CtorViewA emptyEnvA noIotaA 0 (pinFamFA 0) pinFamF0ViewA viewTy_idxCtorA where
  mirrors := []
  fields := [.drec [.sort .zero]]
  res := [.sort .zero]
  stored := rfl
  mirrorsConv := .nil []
  typed := .drec [] 0 [.sort .zero] [] [.sort .zero]
    ((liftA_zero 0 pinFamF0ViewA.idxTelA).symm ▸ viewTy_idxArgs)
    (.nil [] 0 [.sort .zero] ((liftA_zero 0 pinFamF0ViewA.idxTelA).symm ▸ viewTy_idxArgs))
  univI := fun _ _ _ _ h => by cases List.mem_singleton.mp h
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => by cases List.mem_singleton.mp h; trivial)
  univ := fun _ _ h => by
      simp only [List.mem_singleton] at h
      exact FieldA.noConfusion h
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨viewTy_idxCtorTy⟩⟩

theorem ctorViewA_idx_tooth :
    ∃ w, Nonempty (HasTyA (extendEnvA emptyEnvA 0 (pinFamFA 0)) noIotaA (pinFamFA 0).arity []
      viewTy_idxCtorA.mtypeA (.sort w)) := by
  obtain ⟨w, ⟨d⟩⟩ := ctorViewA_hasTy_der viewTy_idxViewA (pinFamFTypeTy 0 emptyEnvA 0 []) rfl
    emptyEnvA_closed (pinFamF_closed 0) (fun _ _ h => Option.noConfusion h)
    (fun _ _ h => Option.noConfusion h) noIotaA_lift noIotaA_subst
    (noIotaA_recHead emptyEnvA) (noIotaA_recHead (extendEnvA emptyEnvA 0 (pinFamFA 0)))
    (emptyEnvA_sem noIotaA 0 (fun _ => 1)) posValA_one
  exact ⟨w, ⟨viewTy_idxViewA.stored.symm ▸ d⟩⟩

/-! ## (10) telescope algebra: lift, substitution, parameter locals, domain transport -/

section TelAlg

theorem viewTy_paramLocals_add (ni : Nat) :
    (np : Nat) → paramLocalsA (np + ni) = (paramLocalsA np).map (liftA 0 ni) ++ paramLocalsA ni
  | 0 => by simp [paramLocalsA, Nat.zero_add]
  | np + 1 => by
      rw [show np + 1 + ni = np + ni + 1 by omega]
      simp only [paramLocalsA, List.map_cons, List.cons_append, viewTy_paramLocals_add ni np,
        liftA, Nat.zero_le, ite_true]

theorem viewTy_famLocals_eq (f : Nat) (ls : List Level) (np ni : Nat) :
    famLocalsA f ls np ni = foldAppsA (.const f ls) (paramLocalsA (np + ni)) := by
  rw [famLocalsA, ← viewTy_paramLocals_add ni np]

theorem viewTy_piTel_snd {w : Level} (B B' : ExprA) :
    (ds ds' : List (ExprA × Level)) → ds.map Prod.snd = ds'.map Prod.snd →
      (piTelA ds B w).2 = (piTelA ds' B' w).2
  | [], [], _ => rfl
  | (_d, u) :: ds, (_d', u') :: ds', h => by
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [piTelA, h.1, viewTy_piTel_snd B B' ds ds' h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem viewTy_liftDoms_snd (c a : Nat) :
    (ds : List (ExprA × Level)) → (liftDomsA c a ds).map Prod.snd = ds.map Prod.snd
  | [] => rfl
  | _ :: ds => by simp only [liftDomsA, List.map_cons, viewTy_liftDoms_snd (c + 1) a ds]

theorem viewTy_lift_piTel (c a : Nat) (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) →
      liftA c a (piTelA ds B w).1 =
        (piTelA (liftDomsA c a ds) (liftA (c + ds.length) a B) w).1
  | [] => by simp [piTelA, liftDomsA]
  | (_D, _u) :: ds => by
      simp only [piTelA, liftDomsA, List.length_cons, liftA_pi]
      rw [viewTy_lift_piTel (c + 1) a B w ds]
      have hlen : c + 1 + ds.length = c + (ds.length + 1) := by omega
      rw [hlen]
      exact congrArg (fun v => ExprA.pi _ _ _ v)
        (viewTy_piTel_snd (w := w) B (liftA (c + (ds.length + 1)) a B) ds
          (liftDomsA (c + 1) a ds) (viewTy_liftDoms_snd (c + 1) a ds).symm)

/-- `σ` walked under a telescope's binders. -/
def viewTy_shiftUp : Nat → SubstA → SubstA
  | 0, σ => σ
  | k + 1, σ => (viewTy_shiftUp k σ).up

theorem viewTy_shiftUp_up (k : Nat) (σ : SubstA) :
    viewTy_shiftUp k σ.up = (viewTy_shiftUp k σ).up := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [viewTy_shiftUp, ih]

def viewTy_substDoms (σ : SubstA) : List (ExprA × Level) → List (ExprA × Level)
  | [] => []
  | (D, u) :: ds => (substA σ D, u) :: viewTy_substDoms σ.up ds

theorem viewTy_substDoms_snd (σ : SubstA) :
    (ds : List (ExprA × Level)) → (viewTy_substDoms σ ds).map Prod.snd = ds.map Prod.snd
  | [] => rfl
  | _ :: ds => by simp only [viewTy_substDoms, List.map_cons, viewTy_substDoms_snd σ.up ds]

theorem viewTy_subst_piTel (σ : SubstA) (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) →
      substA σ (piTelA ds B w).1 =
        (piTelA (viewTy_substDoms σ ds) (substA (viewTy_shiftUp ds.length σ) B) w).1
  | [] => rfl
  | (_D, _u) :: ds => by
      simp only [piTelA, viewTy_substDoms, substA_pi, List.length_cons, viewTy_shiftUp]
      rw [viewTy_subst_piTel σ.up B w ds, viewTy_shiftUp_up ds.length σ]
      exact congrArg (fun v => ExprA.pi _ _ _ v)
        (viewTy_piTel_snd (w := w) B _ ds (viewTy_substDoms σ.up ds)
          (viewTy_substDoms_snd σ.up ds).symm)

theorem viewTy_liftDoms_append (c a : Nat) :
    (xs ys : List (ExprA × Level)) →
      liftDomsA c a (xs ++ ys) = liftDomsA c a xs ++ liftDomsA (c + xs.length) a ys
  | [], _ => by simp [liftDomsA]
  | (_D, _u) :: xs, ys => by
      simp only [liftDomsA, List.cons_append, List.length_cons]
      refine congrArg (fun t => (liftA c a _D, _u) :: t) ?_
      rw [show c + (xs.length + 1) = c + 1 + xs.length by omega]
      exact viewTy_liftDoms_append (c + 1) a xs ys

end TelAlg

/-! ## (11) a derivation moved to a larger level context, and a domain weakened -/

section LvlAux
variable {E : ResolvedEnvA} {I : IotaIfaceA}

def viewTy_ctxLvl {a b : Nat} (hab : a ≤ b) : {Γ : LCtxA} → CtxWfA E I a Γ → CtxWfA E I b Γ
  | _, .nil => .nil
  | _, .assumption hΓ hA => .assumption (viewTy_ctxLvl hab hΓ) (viewTy_lvlWk hab hA)
  | _, .letBinding hΓ hA hv =>
      .letBinding (viewTy_ctxLvl hab hΓ) (viewTy_lvlWk hab hA) (viewTy_lvlWk hab hv)

def viewTy_substLvl {a b : Nat} (hab : a ≤ b) {Δ Γ : LCtxA} {σ : SubstA}
    (h : SubstTyA E I a Δ σ Γ) : SubstTyA E I b Δ σ Γ where
  ty := fun i A hlu => viewTy_lvlWk hab (h.ty i A hlu)
  val := fun i A v hty hval => viewTy_convLvlWk hab (h.val i A v hty hval)

def viewTy_argsLvl {a b : Nat} (hab : a ≤ b) : {Γ : LCtxA} → {T : ExprA} → {as : List ExprA} →
    ArgsTyA E I a Γ T as → ArgsTyA E I b Γ T as
  | _, _, _, .nil l => .nil l
  | _, _, _, .cons A u B v x xs ha tl =>
      .cons A u B v x xs (viewTy_lvlWk hab ha) (viewTy_argsLvl hab tl)

def viewTy_fieldsLvl {a b : Nat} (hab : a ≤ b) {idxTel : Nat → ExprA} :
    {Γ : LCtxA} → {k : Nat} → {fs : List FieldA} → {res : List ExprA} →
    FieldsTyA E I a idxTel Γ k fs res → FieldsTyA E I b idxTel Γ k fs res
  | _, _, _, _, .nil Γ k res h => .nil Γ k res (viewTy_argsLvl hab h)
  | _, _, _, _, .plain Γ k D u fs res hD tl =>
      .plain Γ k D u fs res (viewTy_lvlWk hab hD) (viewTy_fieldsLvl hab tl)
  | _, _, _, _, .drec Γ k idx fs res hidx tl =>
      .drec Γ k idx fs res (viewTy_argsLvl hab hidx) (viewTy_fieldsLvl hab tl)
  | _, _, _, _, .frec Γ k B uB Bs idx fs res hdom tl =>
      .frec Γ k B uB Bs idx fs res (viewTy_fieldsLvl hab hdom) (viewTy_fieldsLvl hab tl)
  | _, _, _, _, .drecD Γ k D idx fs res hidx tl =>
      .drecD Γ k D idx fs res (viewTy_argsLvl hab hidx) (viewTy_fieldsLvl hab tl)

def viewTy_domLvl {a b : Nat} (hab : a ≤ b) : {Γ : LCtxA} → {ds : List (ExprA × Level)} →
    DomTyA E I a Γ ds → DomTyA E I b Γ ds
  | _, _, .nil Γ => .nil Γ
  | _, _, .cons Γ D u ds hD tl =>
      .cons Γ D u ds (viewTy_lvlWk hab hD) (viewTy_domLvl hab tl)

end LvlAux

section DomWk
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def viewTy_wkFront (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) {Γ : LCtxA}
    {e A : ExprA} (h : HasTyA E I n Γ e A) :
    HasTyA E I n (d :: Γ) (liftA 0 1 e) (liftA 0 1 A) :=
  hasTyWeakenA hE hI d (Nat.zero_le _) h

/-- inserting one declaration at cutoff `c` lifts every domain of a telescope. -/
def viewTy_dom_wkAt (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA)
    {c : Nat} {Γ : LCtxA} (hc : c ≤ Γ.length) :
    {ds : List (ExprA × Level)} → DomTyA E I n Γ ds →
      DomTyA E I n (insertAtA d c Γ) (liftDomsA c 1 ds)
  | _, .nil _ => .nil _
  | _, .cons _ D u ds hD tl =>
      .cons (insertAtA d c Γ) (liftA c 1 D) u (liftDomsA (c + 1) 1 ds)
        (by
          simpa only [liftA] using hasTyWeakenA hE hI d hc hD)
        (viewTy_dom_wkAt hE hI d (c := c + 1) (Γ := .assumption D :: Γ)
          (show c + 1 ≤ List.length (.assumption D :: Γ) from Nat.succ_le_succ hc) tl)

def viewTy_dom_append : {Γ : LCtxA} → {xs ys : List (ExprA × Level)} →
    DomTyA E I n Γ xs → DomTyA E I n (telCtxA xs ++ Γ) ys → DomTyA E I n Γ (xs ++ ys)
  | _, _, _, .nil _, hys => hys
  | _, _, ys, .cons Γ D u ds hD tl, hys =>
      .cons Γ D u (ds ++ ys) hD
        (viewTy_dom_append tl ((telCtxA_cons_append (D, u) ds Γ).symm ▸ hys))

end DomWk

/-! ## (12) a term applied along the domain spine it shares with an index telescope -/

section Peel
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- `T` and `U` bind the same domains; `T` ends at a sort and `U` ends at `rest`. -/
inductive SameDoms : ExprA → ExprA → Type
  | done (s : Level) (rest : ExprA) : SameDoms (.sort s) rest
  | step (A : ExprA) (u v u' v' : Level) (B C : ExprA) (h : SameDoms B C) :
      SameDoms (.pi A u B v) (.pi A u' C v')

def sameDoms_instAt (k : Nat) (a : ExprA) : {T U : ExprA} → SameDoms T U →
    SameDoms (instantiateA k a T) (instantiateA k a U)
  | _, _, .done s rest => by
      simp only [instantiateA]
      exact .done s (instantiateA k a rest)
  | _, _, .step A u v u' v' B C h => by
      simp only [instantiateA]
      exact .step (instantiateA k a A) u v u' v' _ _
        (sameDoms_instAt (k + 1) (liftA 0 1 a) h)

def sameDoms_piTel (s : Level) (rest : ExprA) (wr : Level) :
    (ds : List (ExprA × Level)) →
      SameDoms (piTelA ds (.sort s) (.succ s)).1 (piTelA ds rest wr).1
  | [] => by
      simp only [piTelA]
      exact .done s rest
  | (D, u) :: ds => by
      simp only [piTelA]
      exact .step D u _ _ _ _ _ (sameDoms_piTel s rest wr ds)

def sameDoms_lift (c a : Nat) : {T U : ExprA} → SameDoms T U →
    SameDoms (liftA c a T) (liftA c a U)
  | _, _, .done s rest => by
      simp only [liftA]
      exact .done s (liftA c a rest)
  | _, _, .step A u v u' v' B C h => by
      simp only [liftA]
      exact .step (liftA c a A) u v u' v' _ _ (sameDoms_lift (c + 1) a h)

/-- instantiate a spine, the way `applyTelA` does: each argument opens one `Π`. -/
def instSpine : List ExprA → ExprA → ExprA
  | [], T => T
  | a :: as, .pi _ _ B _ => instSpine as (instantiate0A a B)
  | _ :: _, T => T

theorem instSpine_piTel (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → (as : List ExprA) → (τ : SubstA) → as.length = ds.length →
      instSpine as (substA τ (piTelA ds B w).1) = substA (consListA as τ) B
  | [], [], _, _ => by simp [instSpine, piTelA, consListA]
  | (_M, _u) :: ds, a :: as, τ, h => by
      simp only [piTelA, substA_pi, instSpine, List.length_cons, Nat.succ.injEq] at h ⊢
      rw [instantiate0A_substA_up]
      exact instSpine_piTel B w ds as (SubstA.cons a τ) h
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

/-- apply `f : U` to arguments typed along `T`, while `T` and `U` share domains.
    What remains is `instSpine as U`: `U`'s tail, instantiated by those arguments. -/
def viewTy_peelApps (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) :
    {T U : ExprA} → SameDoms T U → {sT sU : Level} →
    HasTyA E I n Γ T (.sort sT) → HasTyA E I n Γ U (.sort sU) →
    {f : ExprA} → HasTyA E I n Γ f U → {as : List ExprA} → ArgsTyA E I n Γ T as →
    HasTyA E I n Γ (foldAppsA f as) (instSpine as U)
  | _, _, .done _ _, _, _, _, _, _, hf, _, .nil _ => by
      simpa [instSpine, foldAppsA] using hf
  | _, _, .step A u _ u' v' B C hsp, _, _, hT, hU, f, hf, _, .cons _ _ _ _ a as ha tl => by
      obtain ⟨_, tB⟩ := hasTyA_pi_parts hT
      obtain ⟨tA, tC⟩ := hasTyA_pi_parts hU
      have hInstT := hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ tB ha tA
      have hInstU := hasTyA_inst0 hE hI (iotaRecHeadTypedA_of hR) hIS hΓ tC ha tA
      have hInstU' : HasTyA E I n Γ (instantiate0A a C) (.sort v') :=
        instantiate0A_sort a v' ▸ hInstU
      have hApp := HasTyA.app Γ f a A C u' v' v' tC hInstU' hf ha
      have hsp' := sameDoms_instAt 0 a hsp
      rw [show instantiateA 0 a B = instantiate0A a B from rfl,
        show instantiateA 0 a C = instantiate0A a C from rfl] at hsp'
      simpa [instSpine, foldAppsA] using
        viewTy_peelApps hE hI hR hIS hΓ hsp' hInstT hInstU' hApp tl

end Peel

/-! ## (13) splitting a domain telescope, and weakening it by a front context -/

section DomSplit
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

theorem viewTy_liftDoms_zero (c : Nat) :
    (ds : List (ExprA × Level)) → liftDomsA c 0 ds = ds
  | [] => rfl
  | (_D, _) :: ds => by
      simp only [liftDomsA]
      rw [liftA_zero, viewTy_liftDoms_zero (c + 1) ds]

theorem viewTy_liftDoms_succ (c a : Nat) :
    (ds : List (ExprA × Level)) →
      liftDomsA c 1 (liftDomsA c a ds) = liftDomsA c (a + 1) ds
  | [] => rfl
  | (_D, _) :: ds => by
      simp only [liftDomsA]
      rw [liftA_liftA_merge 1 a c c (Nat.le_refl _) (Nat.le_add_left c a),
        viewTy_liftDoms_succ (c + 1) a ds]

def viewTy_dom_wkBy (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Δ : LCtxA) → {Γ : LCtxA} → {ds : List (ExprA × Level)} →
    DomTyA E I n Γ ds → DomTyA E I n (Δ ++ Γ) (liftDomsA 0 Δ.length ds)
  | [], _, _, h => by
      rw [List.nil_append, List.length_nil, viewTy_liftDoms_zero]
      exact h
  | d :: Δ, _, _, h => by
      have ih := viewTy_dom_wkBy hE hI Δ h
      have hw := viewTy_dom_wkAt hE hI d (c := 0) (Nat.zero_le _) ih
      rw [viewTy_liftDoms_succ 0 Δ.length] at hw
      simpa [List.cons_append, List.length_cons, insertAtA] using hw

/-- `Δ`, innermost first, spliced in at cutoff `c`: the head of `Δ` lands closest to the
    `c` inner binders. -/
def viewTy_splice : LCtxA → Nat → LCtxA → LCtxA
  | [], _, Γ => Γ
  | d :: Δ, c, Γ => insertAtA d c (viewTy_splice Δ c Γ)

theorem viewTy_splice_length (Δ : LCtxA) {c : Nat} {Γ : LCtxA} (hc : c ≤ Γ.length) :
    (viewTy_splice Δ c Γ).length = Δ.length + Γ.length := by
  induction Δ generalizing Γ with
  | nil => simp [viewTy_splice, List.length_nil]
  | cons d Δ ih =>
      simp only [viewTy_splice, List.length_cons]
      have hlen := ih hc
      rw [insertAtA_length d c (viewTy_splice Δ c Γ)
          (by rw [hlen]; exact Nat.le_trans hc (Nat.le_add_left _ _)), hlen]
      omega

def viewTy_wkCut (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Δ : LCtxA) → {c : Nat} → {Γ : LCtxA} → (hc : c ≤ Γ.length) → {e A : ExprA} →
    HasTyA E I n Γ e A →
    HasTyA E I n (viewTy_splice Δ c Γ) (liftA c Δ.length e) (liftA c Δ.length A)
  | [], _, _, _, _, _, h => by
      simpa [viewTy_splice, List.length_nil, liftA_zero] using h
  | d :: Δ, c, Γ, hc, _, _, h => by
      have ih := viewTy_wkCut hE hI Δ hc h
      have hc' : c ≤ (viewTy_splice Δ c Γ).length := by
        rw [viewTy_splice_length Δ hc]
        exact Nat.le_trans hc (Nat.le_add_left _ _)
      have hw := hasTyWeakenA hE hI d hc' ih
      simp only [viewTy_splice, List.length_cons] at hw ⊢
      rw [liftA_liftA_merge 1 Δ.length c c (Nat.le_refl _) (Nat.le_add_left _ _),
        liftA_liftA_merge 1 Δ.length c c (Nat.le_refl _) (Nat.le_add_left _ _)] at hw
      exact hw

theorem viewTy_lookup_mid (Δ : LCtxA) (A : ExprA) (Γ : LCtxA) :
    lookupTypeA (Δ ++ (.assumption A :: Γ)) Δ.length = some (liftA 0 (Δ.length + 1) A) := by
  induction Δ with
  | nil =>
      simp only [List.nil_append, List.length_nil, lookupTypeA, List.get?]
  | cons _d Δ ih =>
      simp only [List.cons_append, List.length_cons]
      rw [lookupTypeA_cons_succ, ih, Option.map_some',
        liftA_liftA_merge 1 (Δ.length + 1) 0 0 (Nat.le_refl _) (Nat.zero_le _)]

/-- arguments typed along a telescope stay typed after a plain substitution.
    Every argument lives in the same context, so the substitution is not extended:
    `σ.up` appears only inside the instantiated codomain. -/
def viewTy_args_subst (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Δ Γ : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Δ σ Γ) :
    {T : ExprA} → {as : List ExprA} → ArgsTyA E I n Γ T as →
      ArgsTyA E I n Δ (substA σ T) (as.map (substA σ))
  | _, _, .nil _ => .nil _
  | _, _, .cons A u B v a as ha tl =>
      .cons (substA σ A) u (substA σ.up B) v (substA σ a) _
        (hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσ ha)
        (substA_instantiate0A σ a B ▸ viewTy_args_subst hE hI hR hIS hσ tl)

/-- one extra binder: the telescope and the arguments lift together. -/
def viewTy_args_wk (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) :
    {Γ : LCtxA} → {T : ExprA} → {as : List ExprA} → ArgsTyA E I n Γ T as →
      ArgsTyA E I n (d :: Γ) (liftA 0 1 T) (as.map (liftA 0 1))
  | _, _, _, .nil l => by
      simpa [liftA] using (ArgsTyA.nil (Γ := d :: _) l : ArgsTyA E I n (d :: _) (.sort l) [])
  | _, _, _, .cons A u B v a as ha tl => by
      have ha' := hasTyWeakenA hE hI d (Nat.zero_le _) ha
      have tl' := viewTy_args_wk hE hI d tl
      rw [liftA_instantiate0A] at tl'
      exact ArgsTyA.cons (liftA 0 1 A) u (liftA 1 1 B) v (liftA 0 1 a) _
        (by simpa [insertAtA] using ha') (by simpa [liftA] using tl')

end DomSplit

/-! ## (14) the field builder commutes with a substitution, pointwise (no `funext`) -/

section CtorShift

theorem viewTy_ctorFields_substExt (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ τ : SubstA) → (pl' : List ExprA) →
    (σ' : SubstA) → (hpl : pl.map (substA τ) = pl') → (hσ : ∀ i, substA τ (σ i) = σ' i) →
    substA τ (ctorFieldsA f ls w pl σ fs res).1 =
      (ctorFieldsA f ls w pl' σ' fs res).1
  | [], pl, σ, τ, pl', σ', hpl, hσ => by
      simp only [ctorFieldsA, substA_foldAppsA, substA_const, List.map_append]
      refine congrArg (foldAppsA (.const f ls)) ?_
      rw [hpl]
      congr 1
      induction res with
      | nil => rfl
      | cons e res ih =>
          simp only [List.map_cons, ih]
          refine congrArg (fun z => z :: res.map (substA σ')) ?_
          rw [substA_substA]
          exact substA_ext hσ e
  | .plain D u :: fs, pl, σ, τ, pl', σ', hpl, hσ => by
      simp only [ctorFieldsA, substA_pi]
      have hpl' : (pl.map (liftA 0 1)).map (substA τ.up) = pl'.map (liftA 0 1) := by
        rw [map_substA_up_liftA, hpl]
      have hσ' : ∀ i, substA τ.up (σ.up i) = σ'.up i := by
        intro i
        cases i with
        | zero => simp [SubstA.up_zero]
        | succ i =>
            rw [SubstA.up_succ, SubstA.up_succ, substA_up_liftA, hσ i]
      rw [ctorFieldsA_snd f ls w res fs (pl.map (liftA 0 1)) σ.up,
        ctorFieldsA_snd f ls w res fs (pl'.map (liftA 0 1)) σ'.up,
        viewTy_ctorFields_substExt f ls w res fs (pl.map (liftA 0 1)) σ.up τ.up _ σ'.up hpl' hσ',
        substA_substA, substA_ext hσ]
  | .drec idx :: fs, pl, σ, τ, pl', σ', hpl, hσ => by
      simp only [ctorFieldsA, substA_pi, substA_foldAppsA, substA_const, List.map_append]
      have hpl' : (pl.map (liftA 0 1)).map (substA τ.up) = pl'.map (liftA 0 1) := by
        rw [map_substA_up_liftA, hpl]
      have hσ' : ∀ i, substA τ.up (σ.shift1 i) = σ'.shift1 i := by
        intro i
        rw [show σ.shift1 i = liftA 0 1 (σ i) from rfl, substA_up_liftA, hσ i]
        rfl
      have hidx : (idx.map (substA σ)).map (substA τ) = idx.map (substA σ') := by
        induction idx with
        | nil => rfl
        | cons e idx ih =>
            simp only [List.map_cons, ih]
            refine congrArg (fun z => z :: idx.map (substA σ')) ?_
            rw [substA_substA]
            exact substA_ext hσ e
      rw [ctorFieldsA_snd f ls w res fs (pl.map (liftA 0 1)) σ.shift1,
        ctorFieldsA_snd f ls w res fs (pl'.map (liftA 0 1)) σ'.shift1,
        viewTy_ctorFields_substExt f ls w res fs (pl.map (liftA 0 1)) σ.shift1 τ.up
          _ σ'.shift1 hpl' hσ', hpl, hidx]
  | .drecD D idx :: fs, pl, σ, τ, pl', σ', hpl, hσ => by
      simp only [ctorFieldsA, substA_pi]
      have hpl' : (pl.map (liftA 0 1)).map (substA τ.up) = pl'.map (liftA 0 1) := by
        rw [map_substA_up_liftA, hpl]
      have hσ' : ∀ i, substA τ.up (σ.shift1 i) = σ'.shift1 i := by
        intro i
        rw [show σ.shift1 i = liftA 0 1 (σ i) from rfl, substA_up_liftA, hσ i]
        rfl
      rw [ctorFieldsA_snd f ls w res fs (pl.map (liftA 0 1)) σ.shift1,
        ctorFieldsA_snd f ls w res fs (pl'.map (liftA 0 1)) σ'.shift1,
        viewTy_ctorFields_substExt f ls w res fs (pl.map (liftA 0 1)) σ.shift1 τ.up
          _ σ'.shift1 hpl' hσ', substA_substA, substA_ext hσ]
  | .frec B uB Bs idx :: fs, pl, σ, τ, pl', σ', hpl, hσ => by
      simp only [ctorFieldsA, substA_pi]
      have hpl' : (pl.map (liftA 0 1)).map (substA τ.up) = pl'.map (liftA 0 1) := by
        rw [map_substA_up_liftA, hpl]
      have hσ' : ∀ i, substA τ.up (σ.shift1 i) = σ'.shift1 i := by
        intro i
        rw [show σ.shift1 i = liftA 0 1 (σ i) from rfl, substA_up_liftA, hσ i]
        rfl
      rw [ctorFieldsA_snd f ls w res fs (pl.map (liftA 0 1)) σ.shift1,
        ctorFieldsA_snd f ls w res fs (pl'.map (liftA 0 1)) σ'.shift1,
        viewTy_ctorFields_substExt f ls w res fs (pl.map (liftA 0 1)) σ.shift1 τ.up
          _ σ'.shift1 hpl' hσ', substA_frecDomA, hpl, show (fun i => substA τ (σ i)) = σ' from funext hσ]
      simp only [frecDomA_snd]

/-- one binder the plain substitution does not name: the field telescope lifts. -/
theorem viewTy_ctorFields_shift1 (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (fs : List FieldA) (pl : List ExprA) (σ : SubstA) :
    liftA 0 1 (ctorFieldsA f ls w pl σ fs res).1 =
      (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).1 := by
  have hid : substA SubstA.id (ctorFieldsA f ls w pl σ fs res).1 =
      (ctorFieldsA f ls w pl σ fs res).1 := substA_id _
  rw [← hid, ← viewTy_subst_shift1 SubstA.id]
  refine viewTy_ctorFields_substExt f ls w res fs pl σ SubstA.id.shift1
    (pl.map (liftA 0 1)) σ.shift1 ?hpl ?hσ
  · induction pl with
    | nil => rfl
    | cons p pl ih =>
        simp only [List.map, viewTy_subst_shift1, substA_id, ih]
  · intro i
    rw [viewTy_subst_shift1, substA_id]
    rfl

theorem viewTy_recBody_locals :
    (ni : Nat) → (paramLocalsA ni).map (liftA 0 1) ++ [.bvar 0] = paramLocalsA (ni + 1)
  | 0 => by simp [paramLocalsA]
  | ni + 1 => by
      simp only [paramLocalsA, List.map_cons, List.cons_append, liftA, Nat.zero_le, ite_true,
        viewTy_recBody_locals ni]

/-- the motive, lifted past `a` binders, is the index telescope plus the major. -/
theorem viewTy_mot_eq (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (a : Nat) :
    liftA 0 a (motTyA f ls params indices wF wM).1 =
      (piTelA (liftDomsA 0 a indices ++
          [(liftA indices.length a (famLocalsA f ls params.length indices.length), wF)])
        (.sort wM) (.succ wM)).1 := by
  rw [motTyA, viewTy_lift_piTel 0 a
      (.pi (famLocalsA f ls params.length indices.length) wF (.sort wM) (.succ wM))
      (.imax wF (.succ wM)) indices, liftA_pi, Nat.zero_add]
  have hs : liftA (indices.length + 1) a (.sort wM) = .sort wM := rfl
  rw [hs]
  have hsing : piTelA
      [(liftA indices.length a (famLocalsA f ls params.length indices.length), wF)]
      (.sort wM) (.succ wM) =
      ((liftA indices.length a (famLocalsA f ls params.length indices.length)).pi wF
        (.sort wM) (.succ wM), wF.imax (.succ wM)) := by
    simp [piTelA]
  have hfst : (piTelA
        [(liftA indices.length a (famLocalsA f ls params.length indices.length), wF)]
        (.sort wM) (.succ wM)).1 =
      (liftA indices.length a (famLocalsA f ls params.length indices.length)).pi wF
        (.sort wM) (.succ wM) := by
    simpa using congrArg Prod.fst hsing
  have hsnd : (piTelA
        [(liftA indices.length a (famLocalsA f ls params.length indices.length), wF)]
        (.sort wM) (.succ wM)).2 = wF.imax (.succ wM) := by
    simpa using congrArg Prod.snd hsing
  rw [← hfst, ← hsnd]
  exact congrArg Prod.fst
    (piTelA_append (liftDomsA 0 a indices)
      [(liftA indices.length a (famLocalsA f ls params.length indices.length), wF)]
      (.sort wM) (.succ wM)).symm

/-- a variable shifted past `ni` binders comes back when those binders are instantiated. -/
theorem viewTy_bvar_inst (ni : Nat) (as : List ExprA) (j : Nat) (hlen : as.length = ni) :
    substA (consListA as SubstA.id) (liftA 0 ni (.bvar j)) = .bvar j := by
  simp only [liftA, Nat.zero_le, ite_true, substA_bvar]
  have h := consListA_add as SubstA.id j
  rw [hlen] at h
  rw [h, SubstA.id_apply]

theorem viewTy_pl_inst (ni : Nat) (as : List ExprA) (hlen : as.length = ni) :
    (js : List Nat) →
      ((js.map ExprA.bvar).map (liftA 0 ni)).map (substA (consListA as SubstA.id)) =
        js.map ExprA.bvar
  | [] => rfl
  | j :: js => by
      simp only [List.map_cons, viewTy_bvar_inst ni as j hlen, viewTy_pl_inst ni as hlen js]

end CtorShift

/-! ## (15) lengths, lifted bvars, the motive's type under extra binders -/

section MinorAlg
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

theorem viewTy_substDoms_length (σ : SubstA) :
    (ds : List (ExprA × Level)) → (viewTy_substDoms σ ds).length = ds.length
  | [] => rfl
  | _ :: ds => by
      simp only [viewTy_substDoms, List.length_cons, viewTy_substDoms_length σ.up ds]

/-- arguments that consume a sort-telescope are as many as its domains.
    Instantiating a `piTelA` is a `piTelA` of the same length (`viewTy_subst_piTel`),
    so the count does not depend on `piCountA` of an arbitrary instantiation. -/
def viewTy_args_piTel_length {w s : Level} :
    {ds : List (ExprA × Level)} → {as : List ExprA} → {Γ : LCtxA} →
      ArgsTyA E I n Γ (piTelA ds (.sort w) s).1 as → as.length = ds.length
  | [], _, _, .nil _ => rfl
  | (_D, _u) :: ds, _, _, .cons _ _ _ _ a _ _ tl => by
      rw [instantiate0A_eq_substA_cons, viewTy_subst_piTel (SubstA.cons a SubstA.id) (.sort w) s ds,
        show substA (viewTy_shiftUp ds.length (SubstA.cons a SubstA.id)) (.sort w) = .sort w from rfl]
        at tl
      simp only [List.length_cons]
      rw [viewTy_args_piTel_length tl, viewTy_substDoms_length]

theorem viewTy_js_lift : (js : List Nat) →
    (js.map ExprA.bvar).map (liftA 0 1) = (js.map (· + 1)).map ExprA.bvar
  | [] => rfl
  | j :: js => by
      simp only [List.map_cons, liftA, Nat.zero_le, ite_true, viewTy_js_lift js]

theorem viewTy_js_lift2 : (js : List Nat) →
    (js.map ExprA.bvar).map (liftA 0 2) = (js.map (· + 2)).map ExprA.bvar
  | [] => rfl
  | j :: js => by
      simp only [List.map_cons, liftA, Nat.zero_le, ite_true, viewTy_js_lift2 js]

theorem viewTy_paramLocals_fix (ni : Nat) :
    (paramLocalsA ni).map (liftA ni 1) = paramLocalsA ni := by
  have go : (k : Nat) → k ≤ ni → (paramLocalsA k).map (liftA ni 1) = paramLocalsA k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [paramLocalsA, List.map_cons, liftA]
        rw [if_neg (show ¬ ni ≤ k from
          Nat.not_le_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk))]
        exact congrArg (fun t => .bvar k :: t) (ih (Nat.le_of_succ_le hk))
  exact go ni (Nat.le_refl _)

theorem viewTy_paramLocals_fix2 (ni : Nat) :
    (paramLocalsA ni).map (liftA ni 2) = paramLocalsA ni := by
  have go : (k : Nat) → k ≤ ni → (paramLocalsA k).map (liftA ni 2) = paramLocalsA k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [paramLocalsA, List.map_cons, liftA]
        rw [if_neg (show ¬ ni ≤ k from Nat.not_le_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk))]
        exact congrArg (fun t => .bvar k :: t) (ih (Nat.le_of_succ_le hk))
  exact go ni (Nat.le_refl _)

theorem viewTy_famHere_lift1 (f : Nat) (ls : List Level) (ni : Nat) (pl : List ExprA) :
    liftA ni 1 (foldAppsA (.const f ls) (pl.map (liftA 0 ni) ++ paramLocalsA ni)) =
      foldAppsA (.const f ls)
        ((pl.map (liftA 0 1)).map (liftA 0 ni) ++ paramLocalsA ni) := by
  rw [liftA_foldAppsA]
  have hc : liftA ni 1 (.const f ls) = .const f ls := rfl
  have hpl : (pl.map (liftA 0 ni)).map (liftA ni 1) =
      (pl.map (liftA 0 1)).map (liftA 0 ni) := by
    induction pl with
    | nil => rfl
    | cons p pl ih =>
        simp only [List.map_cons, ih]
        exact congrArg (fun z => z :: _)
          (liftA_liftA_permute ni 1 0 0 (Nat.le_refl _) p).symm
  rw [hc, List.map_append, viewTy_paramLocals_fix ni, hpl]

theorem viewTy_famHere_lift2 (f : Nat) (ls : List Level) (ni : Nat) (pl : List ExprA) :
    liftA ni 2 (foldAppsA (.const f ls) (pl.map (liftA 0 ni) ++ paramLocalsA ni)) =
      foldAppsA (.const f ls)
        ((pl.map (liftA 0 2)).map (liftA 0 ni) ++ paramLocalsA ni) := by
  rw [liftA_foldAppsA]
  have hc : liftA ni 2 (.const f ls) = .const f ls := rfl
  have hpl : (pl.map (liftA 0 ni)).map (liftA ni 2) =
      (pl.map (liftA 0 2)).map (liftA 0 ni) := by
    induction pl with
    | nil => rfl
    | cons p pl ih =>
        simp only [List.map_cons, ih]
        exact congrArg (fun z => z :: _)
          (liftA_liftA_permute ni 2 0 0 (Nat.le_refl _) p).symm
  rw [hc, List.map_append, viewTy_paramLocals_fix2 ni, hpl]

/-- the motive's type, lifted past `a` binders that sit outside its indices. -/
theorem viewTy_motTy_lift (a : Nat) (idxDoms : List (ExprA × Level)) (famHere : ExprA)
    (wF wM : Level) :
    liftA 0 a (piTelA idxDoms
        (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1 =
      (piTelA (liftDomsA 0 a idxDoms)
        (.pi (liftA idxDoms.length a famHere) wF (.sort wM) (.succ wM))
        (.imax wF (.succ wM))).1 := by
  rw [viewTy_lift_piTel 0 a
      (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM)) idxDoms, liftA_pi,
      Nat.zero_add]
  have hs : liftA (idxDoms.length + 1) a (.sort wM) = .sort wM := rfl
  rw [hs]

theorem viewTy_idxTy_lift (a : Nat) (idxDoms : List (ExprA × Level)) (wF : Level) :
    liftA 0 a (piTelA idxDoms (.sort wF) (.succ wF)).1 =
      (piTelA (liftDomsA 0 a idxDoms) (.sort wF) (.succ wF)).1 := by
  rw [viewTy_lift_piTel 0 a (.sort wF) (.succ wF) idxDoms, Nat.zero_add]
  have hs : liftA idxDoms.length a (.sort wF) = .sort wF := rfl
  rw [hs]

theorem viewTy_tel_up (σ : SubstA) (k : Nat) (idxBase : ExprA) :
    substA σ.up (liftA 0 (k + 1) idxBase) = liftA 0 1 (substA σ (liftA 0 k idxBase)) := by
  have hm : liftA 0 (k + 1) idxBase = liftA 0 1 (liftA 0 k idxBase) := by
    rw [liftA_liftA_merge 1 k 0 0 (Nat.le_refl _) (Nat.zero_le _)]
  rw [hm, substA_up_liftA]

theorem viewTy_tel_shift2 (σ : SubstA) (k : Nat) (idxBase : ExprA) :
    substA σ.shift1.shift1 (liftA 0 k idxBase) = liftA 0 2 (substA σ (liftA 0 k idxBase)) := by
  rw [viewTy_subst_shift1, viewTy_subst_shift1]
  rw [liftA_liftA_merge 1 1 0 0 (Nat.le_refl _) (Nat.zero_le _)]

end MinorAlg

/-! ## (16) identity from the mirror context into the parameter context.

    `viewTy_mirrors` sends the parameter context to the mirror context (T1 builds the
    constructor type there). The minor applies the constructor to the parameter locals,
    so the same conversions run the other way: `ConvA.symm`, still `SubstA.id`. -/

section MirrorId
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def viewTy_mirrorId (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (huniq : ViewTySortUniqA E I n)
    {Δ Γ : LCtxA} (hσ : SubstTyA E I n Δ SubstA.id Γ) (hΔ : CtxWfA E I n Δ)
    {B : ExprA} {wb u : Level} :
    {ms ps : List (ExprA × Level)} → MirrorsConvA E I n Δ ms ps →
      HasTyA E I n Δ (piTelA ps B wb).1 (.sort u) →
      SubstTyA E I n (telCtxA ps ++ Δ) SubstA.id (telCtxA ms ++ Γ)
  | [], [], .nil _, _ => by
      simpa [telCtxA] using hσ
  | (M, um) :: ms, (P, up) :: ps, .cons _ _ _ _ _ _ _ hc hl tl, hT => by
      obtain ⟨tP, tRest⟩ := hasTyA_pi_parts hT
      let left := viewTy_leftSort huniq hΔ hc tP
      have hMir : HasTyA E I n Δ M (.sort um) :=
        hasTyA_retype_sort left.ty (eqNA_trans left.heq (eqNA_symm hl))
      have hPum : HasTyA E I n Δ P (.sort um) := hasTyA_retype_sort tP (eqNA_symm hl)
      have hcv : ConvA E I n Δ M P (.sort um) :=
        viewTy_collapse hE hI hIS hR huniq hΔ hc hMir
      have hback : ConvA E I n Δ P M (.sort um) := ConvA.symm _ M P _ hcv
      have hσ' := viewTy_idCons hE hI hσ hPum hMir hback
      have hΔ' : CtxWfA E I n (.assumption P :: Δ) := .assumption hΔ tP
      have ih := viewTy_mirrorId hE hI hIS hR huniq hσ' hΔ' tl tRest
      exact (telCtxA_cons_append (P, up) ps Δ).symm ▸
        ((telCtxA_cons_append (M, um) ms Γ).symm ▸ ih)

end MirrorId

/-! ## (17) the motive applied to its indices and its major -/

section MotApply
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

theorem viewTy_here_inst (f : Nat) (ls : List Level) (ni : Nat) (pl as : List ExprA)
    (hlen : as.length = ni) :
    substA (consListA as SubstA.id)
        (foldAppsA (.const f ls) (pl.map (liftA 0 ni) ++ paramLocalsA ni)) =
      foldAppsA (.const f ls) (pl ++ as) := by
  rw [substA_foldAppsA, substA_const, List.map_append]
  have hpl : (pl.map (liftA 0 ni)).map (substA (consListA as SubstA.id)) = pl := by
    induction pl with
    | nil => rfl
    | cons p pl ih =>
        simp only [List.map_cons, ih]
        refine congrArg (fun z => z :: pl) ?_
        have hcut : ni = as.length := hlen.symm
        rw [hcut, substA_consListA_liftA as SubstA.id p, substA_id]
  have has : (paramLocalsA ni).map (substA (consListA as SubstA.id)) = as := by
    have h := paramLocalsA_consListA as SubstA.id
    rw [hlen] at h
    exact h
  rw [hpl, has]

/-- `mot`, typed at `Π idxDoms, Π (_ : famHere), Sort wM`, applied to `as` and `major`. -/
def viewTy_applyMot (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {mot famHere : ExprA} {wF wM : Level} {idxDoms : List (ExprA × Level)}
    (hMot : HasTyA E I n Γ mot
      (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1)
    (hU : HasTyA E I n Γ
      (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1
      (.sort (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).2))
    (hT : HasTyA E I n Γ (piTelA idxDoms (.sort wF) (.succ wF)).1
      (.sort (piTelA idxDoms (.sort wF) (.succ wF)).2))
    {as : List ExprA}
    (hArgs : ArgsTyA E I n Γ (piTelA idxDoms (.sort wF) (.succ wF)).1 as)
    {major : ExprA}
    (hMaj : HasTyA E I n Γ major (substA (consListA as SubstA.id) famHere)) :
    HasTyA E I n Γ (foldAppsA mot (as ++ [major])) (.sort wM) := by
  have hlen : as.length = idxDoms.length := viewTy_args_piTel_length hArgs
  have hsp := sameDoms_piTel wF (.pi famHere wF (.sort wM) (.succ wM))
    (.imax wF (.succ wM)) idxDoms
  have hPeel := viewTy_peelApps hE hI hR hIS hΓ hsp hT hU hMot hArgs
  have hEq : instSpine as
      (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1 =
      .pi (substA (consListA as SubstA.id) famHere) wF (.sort wM) (.succ wM) := by
    have h0 := instSpine_piTel (.pi famHere wF (.sort wM) (.succ wM))
      (.imax wF (.succ wM)) idxDoms as SubstA.id hlen
    rw [substA_id] at h0
    rw [h0, substA_pi, substA_sort]
  have hf := hEq ▸ hPeel
  have hApp := HasTyA.app Γ (foldAppsA mot as) major
    (substA (consListA as SubstA.id) famHere) (.sort wM) wF (.succ wM) (.succ wM)
    (.sort (.assumption (substA (consListA as SubstA.id) famHere) :: Γ) wM)
    ((instantiate0A_sort major wM).symm ▸ .sort Γ wM) hf hMaj
  rw [instantiate0A_sort] at hApp
  have hfold : foldAppsA mot (as ++ [major]) = .app (foldAppsA mot as) major := by
    rw [foldAppsA_append]; rfl
  exact hfold ▸ hApp

theorem viewTy_eta_fold (c : Nat) (ls : List Level) (pl fl : List ExprA) :
    .app (liftA 0 1 (foldAppsA (.const c ls) (pl ++ fl))) (.bvar 0) =
      foldAppsA (.const c ls)
        (pl.map (liftA 0 1) ++ (fl.map (liftA 0 1) ++ [.bvar 0])) := by
  have hrhs :
      foldAppsA (.const c ls)
          (pl.map (liftA 0 1) ++ (fl.map (liftA 0 1) ++ [.bvar 0])) =
        .app (foldAppsA (.const c ls) (pl.map (liftA 0 1) ++ fl.map (liftA 0 1)))
          (.bvar 0) := by
    rw [← List.append_assoc, foldAppsA_append]
    rfl
  rw [hrhs, liftA_foldAppsA, show liftA 0 1 (.const c ls) = .const c ls from rfl, List.map_append]


theorem viewTy_eta_fold2 (c : Nat) (ls : List Level) (pl fl : List ExprA) :
    liftA 0 1 (.app (liftA 0 1 (foldAppsA (.const c ls) (pl ++ fl))) (.bvar 0)) =
      foldAppsA (.const c ls)
        (pl.map (liftA 0 2) ++ (fl.map (liftA 0 2) ++ [.bvar 1])) := by
  rw [viewTy_eta_fold, liftA_foldAppsA, show liftA 0 1 (.const c ls) = .const c ls from rfl,
    List.map_append, List.map_append, List.map_cons, List.map_nil]
  rw [show liftA 0 1 (.bvar 0) = .bvar 1 by simp [liftA]]
  rw [viewTy_map_lift_add 1 1 pl, viewTy_map_lift_add 1 1 fl]

/-- the major of an induction hypothesis: the recursive argument, one binder in. -/
theorem viewTy_drec_major (f : Nat) (ls : List Level) (ni : Nat) (pl as : List ExprA)
    (famHere : ExprA) (hlen : as.length = ni)
    (hHere : famHere =
      foldAppsA (.const f ls) (pl.map (liftA 0 ni) ++ paramLocalsA ni)) :
    liftA 0 1 (foldAppsA (.const f ls) (pl ++ as)) =
      substA (consListA (as.map (liftA 0 1)) SubstA.id) (liftA ni 1 famHere) := by
  rw [hHere, viewTy_famHere_lift1 f ls ni pl]
  rw [viewTy_here_inst f ls ni (pl.map (liftA 0 1)) (as.map (liftA 0 1))
      (by rw [List.length_map]; exact hlen)]
  rw [liftA_foldAppsA, show liftA 0 1 (.const f ls) = .const f ls from rfl, List.map_append]

end MotApply

/-! ## (18) one minor: the constructor's fields, with an induction hypothesis
    after each directly recursive one. The field domains are `ctorFieldsA`'s. -/

section Minor
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- R-NoFunRec-1 step 1 (1c-ε2c): THE CONTEXT EXTENSION OF A PLAIN FIELD, shared by the minor's walk and
    the induction hypothesis's: one more binder (the field's domain under the substitution) extends the
    plain context, the substitution, the motive and the index data. -/
structure ViewTyPlainExt (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (f : Nat) (ls : List Level)
    (wF wM : Level) (idxBase : ExprA) (ni : Nat) (Γp Γ : LCtxA) (σ : SubstA) (k : Nat)
    (pl : List ExprA) (mot famHere : ExprA) (idxDoms : List (ExprA × Level)) (D : ExprA) (u : Level) :
    Type where
  hσ' : SubstTyA E I n (.assumption (substA σ D) :: Γ) σ.up (.assumption D :: Γp)
  hΓp' : CtxWfA E I n (.assumption D :: Γp)
  hΓ' : CtxWfA E I n (.assumption (substA σ D) :: Γ)
  hni' : (liftDomsA 0 1 idxDoms).length = ni
  hHere' : liftA idxDoms.length 1 famHere =
    foldAppsA (.const f ls) ((pl.map (liftA 0 1)).map (liftA 0 ni) ++ paramLocalsA ni)
  hTel' : substA σ.up (liftA 0 (k + 1) idxBase) =
    (piTelA (liftDomsA 0 1 idxDoms) (.sort wF) (.succ wF)).1
  hMot' : HasTyA E I n (.assumption (substA σ D) :: Γ) (liftA 0 1 mot)
    (piTelA (liftDomsA 0 1 idxDoms) (.pi (liftA idxDoms.length 1 famHere) wF (.sort wM) (.succ wM))
      (.imax wF (.succ wM))).1
  hMotTy' : HasTyA E I n (.assumption (substA σ D) :: Γ)
    (piTelA (liftDomsA 0 1 idxDoms) (.pi (liftA idxDoms.length 1 famHere) wF (.sort wM) (.succ wM))
      (.imax wF (.succ wM))).1
    (.sort (piTelA (liftDomsA 0 1 idxDoms) (.pi (liftA idxDoms.length 1 famHere) wF (.sort wM) (.succ wM))
      (.imax wF (.succ wM))).2)
  hIdx' : HasTyA E I n (.assumption (substA σ D) :: Γ)
    (piTelA (liftDomsA 0 1 idxDoms) (.sort wF) (.succ wF)).1
    (.sort (piTelA (liftDomsA 0 1 idxDoms) (.sort wF) (.succ wF)).2)

def viewTy_plainExt (hE : EnvClosedA E) (hI : IotaLiftA I) {f : Nat} {ls : List Level} {wF wM : Level}
    {idxBase : ExprA} {ni : Nat} {Γp Γ : LCtxA} {σ : SubstA} {k : Nat} {pl : List ExprA}
    {mot famHere : ExprA} {idxDoms : List (ExprA × Level)} {D : ExprA} {u : Level}
    (hσ : SubstTyA E I n Γ σ Γp) (hΓp : CtxWfA E I n Γp) (hΓ : CtxWfA E I n Γ)
    (tD : HasTyA E I n Γ (substA σ D) (.sort u)) (hD : HasTyA E I n Γp D (.sort u))
    (hni : idxDoms.length = ni)
    (hHere : famHere = foldAppsA (.const f ls) (pl.map (liftA 0 ni) ++ paramLocalsA ni))
    (hTelEq : substA σ (liftA 0 k idxBase) = (piTelA idxDoms (.sort wF) (.succ wF)).1)
    (hMot : HasTyA E I n Γ mot
      (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1)
    (hMotTy : HasTyA E I n Γ
      (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1
      (.sort (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
        (.imax wF (.succ wM))).2))
    (hIdxTy : HasTyA E I n Γ (piTelA idxDoms (.sort wF) (.succ wF)).1
      (.sort (piTelA idxDoms (.sort wF) (.succ wF)).2)) :
    ViewTyPlainExt E I n f ls wF wM idxBase ni Γp Γ σ k pl mot famHere idxDoms D u := by
      have hσ' := substTyA_up hE hI hσ tD
      have hΓp' : CtxWfA E I n (.assumption D :: Γp) := .assumption hΓp hD
      have hΓ' : CtxWfA E I n (.assumption (substA σ D) :: Γ) := .assumption hΓ tD
      let idx' := liftDomsA 0 1 idxDoms
      have hni' : idx'.length = ni := by rw [liftDomsA_length, hni]
      have hHere' : liftA idxDoms.length 1 famHere =
          foldAppsA (.const f ls)
            ((pl.map (liftA 0 1)).map (liftA 0 ni) ++ paramLocalsA ni) := by
        rw [hni, hHere]
        exact viewTy_famHere_lift1 f ls ni pl
      have hTel' : substA σ.up (liftA 0 (k + 1) idxBase) =
          (piTelA idx' (.sort wF) (.succ wF)).1 := by
        rw [viewTy_tel_up, hTelEq, viewTy_idxTy_lift]
      have hMotW := viewTy_wkFront hE hI (.assumption (substA σ D)) hMot
      have hMotEq := viewTy_motTy_lift 1 idxDoms famHere wF wM
      have hMot' := hMotEq ▸ hMotW
      have hMotTyW := viewTy_wkFront hE hI (.assumption (substA σ D)) hMotTy
      have hSnd : (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 =
          (piTelA idx' (.pi (liftA idxDoms.length 1 famHere) wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 :=
        viewTy_piTel_snd _ _ idxDoms idx' (viewTy_liftDoms_snd 0 1 idxDoms).symm
      have hMotTy' := congrArg ExprA.sort hSnd ▸ (hMotEq ▸ hMotTyW)
      have hIdxW := viewTy_wkFront hE hI (.assumption (substA σ D)) hIdxTy
      have hIdxEq := viewTy_idxTy_lift 1 idxDoms wF
      have hIdxSnd : (piTelA idxDoms (.sort wF) (.succ wF)).2 =
          (piTelA idx' (.sort wF) (.succ wF)).2 :=
        viewTy_piTel_snd _ _ idxDoms idx' (viewTy_liftDoms_snd 0 1 idxDoms).symm
      have hIdx' := congrArg ExprA.sort hIdxSnd ▸ (hIdxEq ▸ hIdxW)
      exact ⟨hσ', hΓp', hΓ', hni', hHere', hTel', hMot', hMotTy', hIdx'⟩

/-- the field applied to the first `j` inner variables, one binder further: the η-step's major
    (R-NoFunRec-1 step 1 (1c-ε2c)). -/
theorem viewTy_eta_major (j : Nat) :
    .app (liftA 0 1 (foldAppsA (.bvar j) ((List.range j).reverse.map ExprA.bvar))) (.bvar 0) =
      foldAppsA (.bvar (j + 1)) ((List.range (j + 1)).reverse.map ExprA.bvar) := by
  have hlist : (List.range (j + 1)).reverse.map ExprA.bvar =
      ((List.range j).reverse.map ExprA.bvar).map (liftA 0 1) ++ [ExprA.bvar 0] := by
    rw [List.range_succ_eq_map]
    simp [List.map_reverse, List.map_map, Function.comp_def, liftA]
  have e : liftA 0 1 (.bvar j) = (.bvar (j + 1) : ExprA) := by simp [liftA]
  rw [liftA_foldAppsA, hlist, foldAppsA_append, e]
  rfl

/-- R-NoFunRec-1 step 1 (1c-ε2c): THE INDUCTION HYPOTHESIS AT A FUNCTION-RECURSIVE FIELD IS A TYPE. The
    binders of `frecIHA` are the field's inner domains, typed as plain fields (`FieldsTyA.frec`'s
    `hdom`), each under the earlier ones, so the walk is the plain arm's: each binder extends the
    context, the substitution, the motive and the index data as in `viewTy_minor`. The base is the motive
    applied to the field's indices and to the field applied to all the inner variables, whose type is the
    family application at the substituted indices (the field's own type, peeled by `hasTyA_eta_body`). -/
def viewTy_frecIH (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {f : Nat} {ls : List Level} {wF wM : Level}
    {idxBase : ExprA} {ni : Nat} {Γp Γ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E I n Γ σ Γp) (hΓp : CtxWfA E I n Γp) (hΓ : CtxWfA E I n Γ) :
    {k j m : Nat} → {pl : List ExprA} → {mot famHere : ExprA} →
    {idxDoms : List (ExprA × Level)} →
    (hni : idxDoms.length = ni) →
    (hHere : famHere =
      foldAppsA (.const f ls) (pl.map (liftA 0 ni) ++ paramLocalsA ni)) →
    (hTelEq : substA σ (liftA 0 k idxBase) =
      (piTelA idxDoms (.sort wF) (.succ wF)).1) →
    (hMot : HasTyA E I n Γ mot
      (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1) →
    (hMotTy : HasTyA E I n Γ
      (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1
      (.sort (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
        (.imax wF (.succ wM))).2)) →
    (hIdxTy : HasTyA E I n Γ (piTelA idxDoms (.sort wF) (.succ wF)).1
      (.sort (piTelA idxDoms (.sort wF) (.succ wF)).2)) →
    {ds : List (ExprA × Level)} → {res : List ExprA} → (hjm : j + ds.length = m) →
    (hM : HasTyA E I n Γ (foldAppsA (.bvar j) ((List.range j).reverse.map ExprA.bvar))
      (ctorFieldsA f ls wF pl σ (ds.map plainA) res).1) →
    (hCTy : HasTyA E I n Γ (ctorFieldsA f ls wF pl σ (ds.map plainA) res).1
      (.sort (ctorFieldsA f ls wF pl σ (ds.map plainA) res).2)) →
    FieldsTyA E I n (fun j => liftA 0 j idxBase) Γp k (ds.map plainA) res →
    HasTyA E I n Γ (frecIHA wM mot j σ ds res m).1 (.sort (frecIHA wM mot j σ ds res m).2)
  | _, j, m, pl, _, famHere, idxDoms, hni, hHere, hTelEq, hMot, hMotTy, hIdxTy, [], res, hjm, hM, _,
      .nil _ _ _ hres => by
      have hmj : m = j := by simpa using hjm.symm
      subst hmj
      have hArgs0 := viewTy_args_subst hE hI hR hIS hσ hres
      have hArgs : ArgsTyA E I n Γ (piTelA idxDoms (.sort wF) (.succ wF)).1
          (res.map (substA σ)) := hTelEq ▸ hArgs0
      have hlen : (res.map (substA σ)).length = ni :=
        (viewTy_args_piTel_length hArgs).trans hni
      have hDom : substA (consListA (res.map (substA σ)) SubstA.id) famHere =
          foldAppsA (.const f ls) (pl ++ res.map (substA σ)) := by
        rw [hHere, viewTy_here_inst f ls ni pl (res.map (substA σ)) hlen]
      have hM0 : HasTyA E I n Γ (foldAppsA (.bvar m) ((List.range m).reverse.map ExprA.bvar))
          (foldAppsA (.const f ls) (pl ++ res.map (substA σ))) := by
        simpa [ctorFieldsA] using hM
      have hM' := hDom.symm ▸ hM0
      have hFin := viewTy_applyMot hE hI hR hIS hΓ hMot hMotTy hIdxTy hArgs hM'
      simpa [frecIHA] using hFin
  | k, j, m, pl, mot, famHere, idxDoms, hni, hHere, hTelEq, hMot, hMotTy, hIdxTy,
      (D, u) :: ds, res, hjm, hM, hCTy, .plain _ _ _ _ _ _ hD tl => by
      obtain ⟨tD, tRest⟩ := hasTyA_pi_parts hCTy
      have hη := hasTyA_eta_body hE hI tD tRest hM
      have hM' : HasTyA E I n (.assumption (substA σ D) :: Γ)
          (foldAppsA (.bvar (j + 1)) ((List.range (j + 1)).reverse.map ExprA.bvar))
          (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.up (ds.map plainA) res).1 :=
        viewTy_eta_major j ▸ hη
      obtain ⟨hσ', hΓp', hΓ', hni', hHere', hTel', hMot', hMotTy', hIdx'⟩ :=
        viewTy_plainExt hE hI hσ hΓp hΓ tD hD hni hHere hTelEq hMot hMotTy hIdxTy
      have ih := viewTy_frecIH hE hI hR hIS hσ' hΓp' hΓ' (j := j + 1) (m := m) hni' hHere' hTel' hMot'
        hMotTy' hIdx' (by simp only [List.length_cons] at hjm; omega) hM' tRest tl
      simpa [frecIHA] using (HasTyA.pi Γ (substA σ D) u _ _ tD ih)

theorem viewTy_minor (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {f c : Nat} {ls : List Level} {wF wM : Level}
    {idxBase : ExprA} {ni : Nat}
    {fsAll : List FieldA} {np0 : Nat} {Γp0 : LCtxA}
    -- the δ-reached fields' evidence, position-indexed as in `ctorFieldsA_conv_norm`
    -- (R-NoDeltaRec-4d-iii): `D` is typed and converts to the family application at
    -- the field's indices in the plain context before it.
    (hdd : ∀ fsPre D idx fsRest,
      fsAll = fsPre ++ FieldA.drecD D idx :: fsRest →
      Nonempty (HasTyA E I n (plainCtxA fsPre Γp0) D (.sort wF)) ∧
      Nonempty (ConvA E I n (plainCtxA fsPre Γp0) D
        (foldAppsA (.const f ls)
          ((paramLocalsA np0).map (liftA 0 (plainIdxA fsPre 0)) ++ idx)) (.sort wF)))
    {Γp Γ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E I n Γ σ Γp) (hΓp : CtxWfA E I n Γp) (hΓ : CtxWfA E I n Γ) :
    {k : Nat} → {pl fl : List ExprA} → {mot famHere : ExprA} →
    {idxDoms : List (ExprA × Level)} →
    (hni : idxDoms.length = ni) →
    (hHere : famHere =
      foldAppsA (.const f ls) (pl.map (liftA 0 ni) ++ paramLocalsA ni)) →
    (hTelEq : substA σ (liftA 0 k idxBase) =
      (piTelA idxDoms (.sort wF) (.succ wF)).1) →
    (hMot : HasTyA E I n Γ mot
      (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1) →
    (hMotTy : HasTyA E I n Γ
      (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1
      (.sort (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
        (.imax wF (.succ wM))).2)) →
    (hIdxTy : HasTyA E I n Γ (piTelA idxDoms (.sort wF) (.succ wF)).1
      (.sort (piTelA idxDoms (.sort wF) (.succ wF)).2)) →
    {fs fsPre : List FieldA} → {jp d : Nat} → {res : List ExprA} →
    (hApp : HasTyA E I n Γ (foldAppsA (.const c ls) (pl ++ fl))
      (ctorFieldsA f ls wF pl σ fs res).1) →
    (hCTy : HasTyA E I n Γ (ctorFieldsA f ls wF pl σ fs res).1
      (.sort (ctorFieldsA f ls wF pl σ fs res).2)) →
    FieldsTyA E I n (fun j => liftA 0 j idxBase) Γp k fs res →
    (hsplit : fsAll = fsPre ++ fs) → (hΓpe : Γp = plainCtxA fsPre Γp0) →
    (hj : jp = plainIdxA fsPre 0) → (hplN : pl = (paramLocalsA np0).map (liftA 0 d)) →
    (hσge : ∀ t, σ (jp + t) = .bvar (t + d)) →
    Nonempty (HasTyA E I n Γ (minorFieldsA f c ls wF wM pl mot fl σ fs res).1
      (.sort (minorFieldsA f c ls wF wM pl mot fl σ fs res).2))
  | _, pl, fl, _, famHere, idxDoms, hni, hHere, hTelEq, hMot, hMotTy, hIdxTy, _, _, _, _,
      res, hApp, _, .nil _ _ _ hres, _, _, _, _, _ => by
      have hArgs0 := viewTy_args_subst hE hI hR hIS hσ hres
      have hArgs : ArgsTyA E I n Γ (piTelA idxDoms (.sort wF) (.succ wF)).1
          (res.map (substA σ)) := hTelEq ▸ hArgs0
      have hlen : (res.map (substA σ)).length = ni :=
        (viewTy_args_piTel_length hArgs).trans hni
      have hDom : substA (consListA (res.map (substA σ)) SubstA.id) famHere =
          foldAppsA (.const f ls) (pl ++ res.map (substA σ)) := by
        rw [hHere, viewTy_here_inst f ls ni pl (res.map (substA σ)) hlen]
      have hApp0 : HasTyA E I n Γ (foldAppsA (.const c ls) (pl ++ fl))
          (foldAppsA (.const f ls) (pl ++ res.map (substA σ))) := by
        simpa [ctorFieldsA] using hApp
      have hApp' := hDom.symm ▸ hApp0
      have hFin := viewTy_applyMot hE hI hR hIS hΓ hMot hMotTy hIdxTy hArgs hApp'
      exact ⟨by simpa [minorFieldsA] using hFin⟩
  | k, pl, fl, mot, famHere, idxDoms, hni, hHere, hTelEq, hMot, hMotTy, hIdxTy,
      .plain D u :: fs, fsPre, jp, d, res, hApp, hCTy, .plain _ _ _ _ _ _ hD tl,
      hsplit, hΓpe, hj, hplN, hσge => by
      obtain ⟨tD, tRest⟩ := hasTyA_pi_parts hCTy
      have hη := hasTyA_eta_body hE hI tD tRest hApp
      have hApp' : HasTyA E I n (.assumption (substA σ D) :: Γ)
          (foldAppsA (.const c ls)
            (pl.map (liftA 0 1) ++ (fl.map (liftA 0 1) ++ [.bvar 0])))
          (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.up fs res).1 :=
        viewTy_eta_fold c ls pl fl ▸ hη
      obtain ⟨hσ', hΓp', hΓ', hni', hHere', hTel', hMot', hMotTy', hIdx'⟩ :=
        viewTy_plainExt hE hI hσ hΓp hΓ tD hD hni hHere hTelEq hMot hMotTy hIdxTy
      have hsplit' : fsAll = (fsPre ++ [.plain D u]) ++ fs := by
        rw [List.append_assoc]; exact hsplit
      have hΓpe' : .assumption D :: Γp = plainCtxA (fsPre ++ [.plain D u]) Γp0 := by
        rw [plainCtxA_append, ← hΓpe]; rfl
      have hj' : jp + 1 = plainIdxA (fsPre ++ [.plain D u]) 0 := by
        rw [plainIdxA_append, ← hj]; rfl
      have hplN' : pl.map (liftA 0 1) = (paramLocalsA np0).map (liftA 0 (d + 1)) := by
        rw [hplN, List.map_map]
        exact List.map_congr_left fun x _ =>
          liftA_liftA_merge 1 d 0 0 (Nat.le_refl 0) (Nat.zero_le _) x
      have hσge' : ∀ t, σ.up (jp + 1 + t) = .bvar (t + (d + 1)) := (substA_walk_ge hσge).1
      obtain ⟨ih⟩ := viewTy_minor hE hI hR hIS hdd hσ' hΓp' hΓ' hni' hHere' hTel' hMot' hMotTy'
        hIdx' hApp' tRest tl hsplit' hΓpe' hj' hplN' hσge'
      exact ⟨by simpa [minorFieldsA] using (HasTyA.pi Γ (substA σ D) u _ _ tD ih)⟩
  | k, pl, fl, mot, famHere, idxDoms, hni, hHere, hTelEq, hMot, hMotTy, hIdxTy,
      .drec idx :: fs, fsPre, jp, d, res, hApp, hCTy, .drec _ _ _ _ _ hidx tl,
      hsplit, hΓpe, hj, hplN, hσge => by
      obtain ⟨tD, tRest⟩ := hasTyA_pi_parts hCTy
      have hη := hasTyA_eta_body hE hI tD tRest hApp
      let dDom : ExprA := foldAppsA (.const f ls) (pl ++ idx.map (substA σ))
      have hΓ1 : CtxWfA E I n (.assumption dDom :: Γ) := .assumption hΓ tD
      have hArgs0 := viewTy_args_subst hE hI hR hIS hσ hidx
      have hArgs : ArgsTyA E I n Γ (piTelA idxDoms (.sort wF) (.succ wF)).1
          (idx.map (substA σ)) := hTelEq ▸ hArgs0
      have hArgs1 := viewTy_args_wk hE hI (.assumption dDom) hArgs
      have hIdxEq1 := viewTy_idxTy_lift 1 idxDoms wF
      have hArgs1' : ArgsTyA E I n (.assumption dDom :: Γ)
          (piTelA (liftDomsA 0 1 idxDoms) (.sort wF) (.succ wF)).1
          ((idx.map (substA σ)).map (liftA 0 1)) := hIdxEq1 ▸ hArgs1
      have hlen : (idx.map (substA σ)).length = ni :=
        (viewTy_args_piTel_length hArgs).trans hni
      have hMotW := viewTy_wkFront hE hI (.assumption dDom) hMot
      have hMotEq := viewTy_motTy_lift 1 idxDoms famHere wF wM
      have hMot1 := hMotEq ▸ hMotW
      have hMotTyW := viewTy_wkFront hE hI (.assumption dDom) hMotTy
      have hSnd1 : (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 =
          (piTelA (liftDomsA 0 1 idxDoms)
            (.pi (liftA idxDoms.length 1 famHere) wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 :=
        viewTy_piTel_snd _ _ idxDoms (liftDomsA 0 1 idxDoms)
          (viewTy_liftDoms_snd 0 1 idxDoms).symm
      have hMotTy1 := congrArg ExprA.sort hSnd1 ▸ (hMotEq ▸ hMotTyW)
      have hIdxW := viewTy_wkFront hE hI (.assumption dDom) hIdxTy
      have hIdxSnd1 : (piTelA idxDoms (.sort wF) (.succ wF)).2 =
          (piTelA (liftDomsA 0 1 idxDoms) (.sort wF) (.succ wF)).2 :=
        viewTy_piTel_snd _ _ idxDoms (liftDomsA 0 1 idxDoms)
          (viewTy_liftDoms_snd 0 1 idxDoms).symm
      have hIdx1 := congrArg ExprA.sort hIdxSnd1 ▸ (hIdxEq1 ▸ hIdxW)
      have hHere1 : liftA idxDoms.length 1 famHere =
          foldAppsA (.const f ls)
            ((pl.map (liftA 0 1)).map (liftA 0 ni) ++ paramLocalsA ni) := by
        rw [hni, hHere]; exact viewTy_famHere_lift1 f ls ni pl
      have hMajEq := hni.symm ▸
        viewTy_drec_major f ls ni pl (idx.map (substA σ)) famHere hlen hHere
      have hb0 : HasTyA E I n (.assumption dDom :: Γ) (.bvar 0) (liftA 0 1 dDom) :=
        .bvar _ 0 _ wF (lookupTypeA_cons_zero_assumption dDom Γ)
          (viewTy_wkFront hE hI (.assumption dDom) tD)
      have hMaj := hMajEq ▸ hb0
      have hIH := viewTy_applyMot hE hI hR hIS hΓ1 hMot1 hMotTy1 hIdx1 hArgs1' hMaj
      let ihDom : ExprA := foldAppsA (liftA 0 1 mot)
        ((idx.map (substA σ)).map (liftA 0 1) ++ [.bvar 0])
      have hΓ2 : CtxWfA E I n (.assumption ihDom :: .assumption dDom :: Γ) :=
        .assumption hΓ1 hIH
      let idx2 := liftDomsA 0 2 idxDoms
      have hni2 : idx2.length = ni := by rw [liftDomsA_length, hni]
      have hHere2 : liftA ni 2 famHere =
          foldAppsA (.const f ls)
            (((pl.map (liftA 0 2))).map (liftA 0 ni) ++ paramLocalsA ni) := by
        rw [hHere]; exact viewTy_famHere_lift2 f ls ni pl
      have hTel2 : substA σ.shift1.shift1 (liftA 0 k idxBase) =
          (piTelA idx2 (.sort wF) (.succ wF)).1 := by
        rw [viewTy_tel_shift2, hTelEq]
        exact viewTy_idxTy_lift 2 idxDoms wF
      have hMot2W := viewTy_wkBy hE hI [.assumption ihDom, .assumption dDom] hMot
      have hMotEq2 := viewTy_motTy_lift 2 idxDoms famHere wF wM
      have hMot2 := hMotEq2 ▸ hMot2W
      have hMotTy2W := viewTy_wkBy hE hI [.assumption ihDom, .assumption dDom] hMotTy
      have hSnd2 : (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 =
          (piTelA idx2 (.pi (liftA idxDoms.length 2 famHere) wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 :=
        viewTy_piTel_snd _ _ idxDoms idx2 (viewTy_liftDoms_snd 0 2 idxDoms).symm
      have hMotTy2 := congrArg ExprA.sort hSnd2 ▸ (hMotEq2 ▸ hMotTy2W)
      have hIdx2W := viewTy_wkBy hE hI [.assumption ihDom, .assumption dDom] hIdxTy
      have hIdxEq2 := viewTy_idxTy_lift 2 idxDoms wF
      have hIdxSnd2 : (piTelA idxDoms (.sort wF) (.succ wF)).2 =
          (piTelA idx2 (.sort wF) (.succ wF)).2 :=
        viewTy_piTel_snd _ _ idxDoms idx2 (viewTy_liftDoms_snd 0 2 idxDoms).symm
      have hIdx2 := congrArg ExprA.sort hIdxSnd2 ▸ (hIdxEq2 ▸ hIdx2W)
      have hApp1 : HasTyA E I n (.assumption dDom :: Γ)
          (.app (liftA 0 1 (foldAppsA (.const c ls) (pl ++ fl))) (.bvar 0))
          (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 fs res).1 := hη
      have hApp2W := viewTy_wkFront hE hI (.assumption ihDom) hApp1
      have hShift := viewTy_ctorFields_shift1 f ls wF res fs (pl.map (liftA 0 1)) σ.shift1
      have hpl2 : ((pl.map (liftA 0 1)).map (liftA 0 1)) = pl.map (liftA 0 2) :=
        viewTy_map_lift_add 1 1 pl
      have hLv : (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 fs res).2 =
          (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).2 :=
        (ctorFieldsA_snd f ls wF res fs (pl.map (liftA 0 1)) σ.shift1).trans
          (ctorFieldsA_snd f ls wF res fs (pl.map (liftA 0 2)) σ.shift1.shift1).symm
      have hApp2 : HasTyA E I n (.assumption ihDom :: .assumption dDom :: Γ)
          (foldAppsA (.const c ls)
            (pl.map (liftA 0 2) ++ (fl.map (liftA 0 2) ++ [.bvar 1])))
          (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).1 :=
        viewTy_eta_fold2 c ls pl fl ▸ (hpl2 ▸ (hShift ▸ hApp2W))
      have hRestW := viewTy_wkFront hE hI (.assumption ihDom) tRest
      have hRest : HasTyA E I n (.assumption ihDom :: .assumption dDom :: Γ)
          (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).1
          (.sort (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).2) :=
        congrArg ExprA.sort hLv ▸ (hpl2 ▸ (hShift ▸ hRestW))
      have hσ2 := substTyA_shift1 hE hI (substTyA_shift1 hE hI hσ dDom) ihDom
      have hHere2' : liftA idxDoms.length 2 famHere =
          foldAppsA (.const f ls)
            ((pl.map (liftA 0 2)).map (liftA 0 ni) ++ paramLocalsA ni) := by
        rw [hni]; exact hHere2
      have hsplit' : fsAll = (fsPre ++ [.drec idx]) ++ fs := by
        rw [List.append_assoc]; exact hsplit
      have hΓpe' : Γp = plainCtxA (fsPre ++ [.drec idx]) Γp0 := by
        rw [plainCtxA_append, ← hΓpe]; rfl
      have hj' : jp = plainIdxA (fsPre ++ [.drec idx]) 0 := by
        rw [plainIdxA_append, ← hj]; rfl
      have hplN' : pl.map (liftA 0 2) = (paramLocalsA np0).map (liftA 0 (d + 2)) := by
        rw [hplN, List.map_map]
        exact List.map_congr_left fun x _ =>
          liftA_liftA_merge 2 d 0 0 (Nat.le_refl 0) (Nat.zero_le _) x
      have hσge' : ∀ t, σ.shift1.shift1 (jp + t) = .bvar (t + (d + 2)) :=
        (substA_walk_ge (substA_walk_ge hσge).2).2
      obtain ⟨ih⟩ := viewTy_minor hE hI hR hIS hdd hσ2 hΓp hΓ2 hni2 hHere2' hTel2 hMot2 hMotTy2
        hIdx2 hApp2 hRest tl hsplit' hΓpe' hj' hplN' hσge'
      have hInner := HasTyA.pi (.assumption dDom :: Γ) ihDom wM _ _ hIH ih
      have hOuter := HasTyA.pi Γ dDom wF _ _ tD hInner
      unfold minorFieldsA
      exact ⟨hOuter⟩
  | k, pl, fl, mot, famHere, idxDoms, hni, hHere, hTelEq, hMot, hMotTy, hIdxTy,
      .frec B uB Bs idx :: fs, fsPre, jp, d, res, hApp, hCTy, .frec _ _ _ _ _ _ _ _ hdom tl,
      hsplit, hΓpe, hj, hplN, hσge => by
      obtain ⟨tD, tRest⟩ := hasTyA_pi_parts hCTy
      have hη := hasTyA_eta_body hE hI tD tRest hApp
      let dd := frecDomA f ls wF pl σ ((B, uB) :: Bs) idx
      let dDom : ExprA := dd.1
      have hΓ1 : CtxWfA E I n (.assumption dDom :: Γ) := .assumption hΓ tD
      have hIdxEq1 := viewTy_idxTy_lift 1 idxDoms wF
      have hMotW := viewTy_wkFront hE hI (.assumption dDom) hMot
      have hMotEq := viewTy_motTy_lift 1 idxDoms famHere wF wM
      have hMot1 := hMotEq ▸ hMotW
      have hMotTyW := viewTy_wkFront hE hI (.assumption dDom) hMotTy
      have hSnd1 : (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 =
          (piTelA (liftDomsA 0 1 idxDoms)
            (.pi (liftA idxDoms.length 1 famHere) wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 :=
        viewTy_piTel_snd _ _ idxDoms (liftDomsA 0 1 idxDoms)
          (viewTy_liftDoms_snd 0 1 idxDoms).symm
      have hMotTy1 := congrArg ExprA.sort hSnd1 ▸ (hMotEq ▸ hMotTyW)
      have hIdxW := viewTy_wkFront hE hI (.assumption dDom) hIdxTy
      have hIdxSnd1 : (piTelA idxDoms (.sort wF) (.succ wF)).2 =
          (piTelA (liftDomsA 0 1 idxDoms) (.sort wF) (.succ wF)).2 :=
        viewTy_piTel_snd _ _ idxDoms (liftDomsA 0 1 idxDoms)
          (viewTy_liftDoms_snd 0 1 idxDoms).symm
      have hIdx1 := congrArg ExprA.sort hIdxSnd1 ▸ (hIdxEq1 ▸ hIdxW)
      have hHere1 : liftA idxDoms.length 1 famHere =
          foldAppsA (.const f ls)
            ((pl.map (liftA 0 1)).map (liftA 0 ni) ++ paramLocalsA ni) := by
        rw [hni, hHere]; exact viewTy_famHere_lift1 f ls ni pl
      have hdEq := frecDomA_eq f ls wF idx ((B, uB) :: Bs) pl σ
      have hb0 : HasTyA E I n (.assumption dDom :: Γ) (.bvar 0) (liftA 0 1 dDom) :=
        .bvar _ 0 _ dd.2 (lookupTypeA_cons_zero_assumption dDom Γ)
          (viewTy_wkFront hE hI (.assumption dDom) tD)
      have hShiftD := viewTy_ctorFields_shift1 f ls wF idx (((B, uB) :: Bs).map plainA) pl σ
      have hdEq1 : dDom = (ctorFieldsA f ls wF pl σ (((B, uB) :: Bs).map plainA) idx).1 :=
        congrArg Prod.fst hdEq
      have hlift : liftA 0 1 dDom =
          (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 (((B, uB) :: Bs).map plainA) idx).1 := by
        rw [hdEq1]; exact hShiftD
      have hLvD : dd.2 = (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1
          (((B, uB) :: Bs).map plainA) idx).2 :=
        (congrArg Prod.snd hdEq).trans
          ((ctorFieldsA_snd f ls wF idx (((B, uB) :: Bs).map plainA) pl σ).trans
            (ctorFieldsA_snd f ls wF idx (((B, uB) :: Bs).map plainA) (pl.map (liftA 0 1)) σ.shift1).symm)
      have hM0 : HasTyA E I n (.assumption dDom :: Γ)
          (foldAppsA (.bvar 0) ((List.range 0).reverse.map ExprA.bvar))
          (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 (((B, uB) :: Bs).map plainA) idx).1 := by
        have h := hb0
        rw [hlift] at h
        exact h
      have hCTyD : HasTyA E I n (.assumption dDom :: Γ)
          (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 (((B, uB) :: Bs).map plainA) idx).1
          (.sort (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 (((B, uB) :: Bs).map plainA) idx).2) := by
        have h : HasTyA E I n (.assumption dDom :: Γ) (liftA 0 1 dDom) (.sort dd.2) :=
          viewTy_wkFront hE hI (.assumption dDom) tD
        rw [hlift, hLvD] at h
        exact h
      have hTel1 : substA σ.shift1 (liftA 0 k idxBase) =
          (piTelA (liftDomsA 0 1 idxDoms) (.sort wF) (.succ wF)).1 := by
        rw [viewTy_subst_shift1, hTelEq]
        exact hIdxEq1
      have hIH := viewTy_frecIH hE hI hR hIS (substTyA_shift1 hE hI hσ dDom) hΓp hΓ1 (j := 0)
        (m := Bs.length + 1) (by rw [liftDomsA_length]; exact hni) hHere1 hTel1 hMot1 hMotTy1 hIdx1
        (ds := (B, uB) :: Bs) (res := idx) (by simp) hM0 hCTyD hdom
      let ihDom : ExprA := (frecIHA wM (liftA 0 1 mot) 0 σ.shift1 ((B, uB) :: Bs) idx (Bs.length + 1)).1
      let ihLv : Level := (frecIHA wM (liftA 0 1 mot) 0 σ.shift1 ((B, uB) :: Bs) idx (Bs.length + 1)).2
      have hΓ2 : CtxWfA E I n (.assumption ihDom :: .assumption dDom :: Γ) :=
        .assumption hΓ1 hIH
      let idx2 := liftDomsA 0 2 idxDoms
      have hni2 : idx2.length = ni := by rw [liftDomsA_length, hni]
      have hHere2 : liftA ni 2 famHere =
          foldAppsA (.const f ls)
            (((pl.map (liftA 0 2))).map (liftA 0 ni) ++ paramLocalsA ni) := by
        rw [hHere]; exact viewTy_famHere_lift2 f ls ni pl
      have hTel2 : substA σ.shift1.shift1 (liftA 0 k idxBase) =
          (piTelA idx2 (.sort wF) (.succ wF)).1 := by
        rw [viewTy_tel_shift2, hTelEq]
        exact viewTy_idxTy_lift 2 idxDoms wF
      have hMot2W := viewTy_wkBy hE hI [.assumption ihDom, .assumption dDom] hMot
      have hMotEq2 := viewTy_motTy_lift 2 idxDoms famHere wF wM
      have hMot2 := hMotEq2 ▸ hMot2W
      have hMotTy2W := viewTy_wkBy hE hI [.assumption ihDom, .assumption dDom] hMotTy
      have hSnd2 : (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 =
          (piTelA idx2 (.pi (liftA idxDoms.length 2 famHere) wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 :=
        viewTy_piTel_snd _ _ idxDoms idx2 (viewTy_liftDoms_snd 0 2 idxDoms).symm
      have hMotTy2 := congrArg ExprA.sort hSnd2 ▸ (hMotEq2 ▸ hMotTy2W)
      have hIdx2W := viewTy_wkBy hE hI [.assumption ihDom, .assumption dDom] hIdxTy
      have hIdxEq2 := viewTy_idxTy_lift 2 idxDoms wF
      have hIdxSnd2 : (piTelA idxDoms (.sort wF) (.succ wF)).2 =
          (piTelA idx2 (.sort wF) (.succ wF)).2 :=
        viewTy_piTel_snd _ _ idxDoms idx2 (viewTy_liftDoms_snd 0 2 idxDoms).symm
      have hIdx2 := congrArg ExprA.sort hIdxSnd2 ▸ (hIdxEq2 ▸ hIdx2W)
      have hApp1 : HasTyA E I n (.assumption dDom :: Γ)
          (.app (liftA 0 1 (foldAppsA (.const c ls) (pl ++ fl))) (.bvar 0))
          (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 fs res).1 := hη
      have hApp2W := viewTy_wkFront hE hI (.assumption ihDom) hApp1
      have hShift := viewTy_ctorFields_shift1 f ls wF res fs (pl.map (liftA 0 1)) σ.shift1
      have hpl2 : ((pl.map (liftA 0 1)).map (liftA 0 1)) = pl.map (liftA 0 2) :=
        viewTy_map_lift_add 1 1 pl
      have hLv : (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 fs res).2 =
          (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).2 :=
        (ctorFieldsA_snd f ls wF res fs (pl.map (liftA 0 1)) σ.shift1).trans
          (ctorFieldsA_snd f ls wF res fs (pl.map (liftA 0 2)) σ.shift1.shift1).symm
      have hApp2 : HasTyA E I n (.assumption ihDom :: .assumption dDom :: Γ)
          (foldAppsA (.const c ls)
            (pl.map (liftA 0 2) ++ (fl.map (liftA 0 2) ++ [.bvar 1])))
          (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).1 :=
        viewTy_eta_fold2 c ls pl fl ▸ (hpl2 ▸ (hShift ▸ hApp2W))
      have hRestW := viewTy_wkFront hE hI (.assumption ihDom) tRest
      have hRest : HasTyA E I n (.assumption ihDom :: .assumption dDom :: Γ)
          (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).1
          (.sort (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).2) :=
        congrArg ExprA.sort hLv ▸ (hpl2 ▸ (hShift ▸ hRestW))
      have hσ2 := substTyA_shift1 hE hI (substTyA_shift1 hE hI hσ dDom) ihDom
      have hHere2' : liftA idxDoms.length 2 famHere =
          foldAppsA (.const f ls)
            ((pl.map (liftA 0 2)).map (liftA 0 ni) ++ paramLocalsA ni) := by
        rw [hni]; exact hHere2
      have hsplit' : fsAll = (fsPre ++ [.frec B uB Bs idx]) ++ fs := by
        rw [List.append_assoc]; exact hsplit
      have hΓpe' : Γp = plainCtxA (fsPre ++ [.frec B uB Bs idx]) Γp0 := by
        rw [plainCtxA_append, ← hΓpe]; rfl
      have hj' : jp = plainIdxA (fsPre ++ [.frec B uB Bs idx]) 0 := by
        rw [plainIdxA_append, ← hj]; rfl
      have hplN' : pl.map (liftA 0 2) = (paramLocalsA np0).map (liftA 0 (d + 2)) := by
        rw [hplN, List.map_map]
        exact List.map_congr_left fun x _ =>
          liftA_liftA_merge 2 d 0 0 (Nat.le_refl 0) (Nat.zero_le _) x
      have hσge' : ∀ t, σ.shift1.shift1 (jp + t) = .bvar (t + (d + 2)) :=
        (substA_walk_ge (substA_walk_ge hσge).2).2
      obtain ⟨ih⟩ := viewTy_minor hE hI hR hIS hdd hσ2 hΓp hΓ2 hni2 hHere2' hTel2 hMot2 hMotTy2
        hIdx2 hApp2 hRest tl hsplit' hΓpe' hj' hplN' hσge'
      have hInner := HasTyA.pi (.assumption dDom :: Γ) ihDom ihLv _ _ hIH ih
      have hOuter := HasTyA.pi Γ dDom dd.2 _ _ tD hInner
      unfold minorFieldsA
      exact ⟨hOuter⟩
  | k, pl, fl, mot, famHere, idxDoms, hni, hHere, hTelEq, hMot, hMotTy, hIdxTy,
      .drecD D idx :: fs, fsPre, jp, d, res, hApp, hCTy, .drecD _ _ _ _ _ _ hidx tl,
      hsplit, hΓpe, hj, hplN, hσge => by
      obtain ⟨tD, tRest⟩ := hasTyA_pi_parts hCTy
      have hη := hasTyA_eta_body hE hI tD tRest hApp
      let dDom : ExprA := substA σ D
      have hΓ1 : CtxWfA E I n (.assumption dDom :: Γ) := .assumption hΓ tD
      have hArgs0 := viewTy_args_subst hE hI hR hIS hσ hidx
      have hArgs : ArgsTyA E I n Γ (piTelA idxDoms (.sort wF) (.succ wF)).1
          (idx.map (substA σ)) := hTelEq ▸ hArgs0
      have hArgs1 := viewTy_args_wk hE hI (.assumption dDom) hArgs
      have hIdxEq1 := viewTy_idxTy_lift 1 idxDoms wF
      have hArgs1' : ArgsTyA E I n (.assumption dDom :: Γ)
          (piTelA (liftDomsA 0 1 idxDoms) (.sort wF) (.succ wF)).1
          ((idx.map (substA σ)).map (liftA 0 1)) := hIdxEq1 ▸ hArgs1
      have hlen : (idx.map (substA σ)).length = ni :=
        (viewTy_args_piTel_length hArgs).trans hni
      have hMotW := viewTy_wkFront hE hI (.assumption dDom) hMot
      have hMotEq := viewTy_motTy_lift 1 idxDoms famHere wF wM
      have hMot1 := hMotEq ▸ hMotW
      have hMotTyW := viewTy_wkFront hE hI (.assumption dDom) hMotTy
      have hSnd1 : (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 =
          (piTelA (liftDomsA 0 1 idxDoms)
            (.pi (liftA idxDoms.length 1 famHere) wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 :=
        viewTy_piTel_snd _ _ idxDoms (liftDomsA 0 1 idxDoms)
          (viewTy_liftDoms_snd 0 1 idxDoms).symm
      have hMotTy1 := congrArg ExprA.sort hSnd1 ▸ (hMotEq ▸ hMotTyW)
      have hIdxW := viewTy_wkFront hE hI (.assumption dDom) hIdxTy
      have hIdxSnd1 : (piTelA idxDoms (.sort wF) (.succ wF)).2 =
          (piTelA (liftDomsA 0 1 idxDoms) (.sort wF) (.succ wF)).2 :=
        viewTy_piTel_snd _ _ idxDoms (liftDomsA 0 1 idxDoms)
          (viewTy_liftDoms_snd 0 1 idxDoms).symm
      have hIdx1 := congrArg ExprA.sort hIdxSnd1 ▸ (hIdxEq1 ▸ hIdxW)
      -- the δ evidence at this position, substituted along σ into Γ (R-NoDeltaRec-4d-iii):
      -- the surface domain converts to the family application at the field's indices.
      obtain ⟨-, ⟨hCT⟩⟩ := hdd fsPre D idx fs hsplit
      have hσp : SubstTyA E I n Γ σ (plainCtxA fsPre Γp0) := hΓpe ▸ hσ
      have hcσ : ConvA E I n Γ (substA σ D)
          (foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) (.sort wF) := by
        have hc := convA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσp hCT
        rw [substA_sort, substA_foldAppsA, substA_const, List.map_append] at hc
        rw [← hj, substA_walk_paramLocals hσge] at hc
        rw [← hplN] at hc
        exact hc
      let dDom0 : ExprA := foldAppsA (.const f ls) (pl ++ idx.map (substA σ))
      have hDomN0 : HasTyA E I n Γ dDom0 (.sort wF) :=
        convA_hasTy_right hE hI hR hIS hΓ hcσ
      have hMajEq : liftA 0 1 dDom0 =
          substA (consListA ((idx.map (substA σ)).map (liftA 0 1)) SubstA.id)
            (liftA idxDoms.length 1 famHere) :=
        hni ▸ viewTy_drec_major f ls ni pl (idx.map (substA σ)) famHere hlen hHere
      have hB : HasTyA E I n (.assumption dDom :: Γ)
          (substA (consListA ((idx.map (substA σ)).map (liftA 0 1)) SubstA.id)
            (liftA idxDoms.length 1 famHere)) (.sort wF) :=
        hMajEq ▸ viewTy_wkFront hE hI (.assumption dDom) hDomN0
      have hcL : ConvA E I n (.assumption dDom :: Γ) (liftA 0 1 dDom)
          (liftA 0 1 dDom0) (.sort wF) :=
        convWeakenA hE hI (.assumption dDom) (Nat.zero_le _) hcσ
      have hcMaj : ConvA E I n (.assumption dDom :: Γ) (liftA 0 1 dDom)
          (substA (consListA ((idx.map (substA σ)).map (liftA 0 1)) SubstA.id)
            (liftA idxDoms.length 1 famHere)) (.sort wF) := hMajEq ▸ hcL
      have hb0 : HasTyA E I n (.assumption dDom :: Γ) (.bvar 0) (liftA 0 1 dDom) :=
        .bvar _ 0 _ wF (lookupTypeA_cons_zero_assumption dDom Γ)
          (viewTy_wkFront hE hI (.assumption dDom) tD)
      have hMaj : HasTyA E I n (.assumption dDom :: Γ) (.bvar 0)
          (substA (consListA ((idx.map (substA σ)).map (liftA 0 1)) SubstA.id)
            (liftA idxDoms.length 1 famHere)) :=
        .conv _ _ _ _ _ _ hb0 (viewTy_wkFront hE hI (.assumption dDom) tD) (eqNA_refl wF)
          hB hcMaj
      have hIH := viewTy_applyMot hE hI hR hIS hΓ1 hMot1 hMotTy1 hIdx1 hArgs1' hMaj
      let ihDom : ExprA := foldAppsA (liftA 0 1 mot)
        ((idx.map (substA σ)).map (liftA 0 1) ++ [.bvar 0])
      have hΓ2 : CtxWfA E I n (.assumption ihDom :: .assumption dDom :: Γ) :=
        .assumption hΓ1 hIH
      let idx2 := liftDomsA 0 2 idxDoms
      have hni2 : idx2.length = ni := by rw [liftDomsA_length, hni]
      have hHere2 : liftA ni 2 famHere =
          foldAppsA (.const f ls)
            (((pl.map (liftA 0 2))).map (liftA 0 ni) ++ paramLocalsA ni) := by
        rw [hHere]; exact viewTy_famHere_lift2 f ls ni pl
      have hTel2 : substA σ.shift1.shift1 (liftA 0 k idxBase) =
          (piTelA idx2 (.sort wF) (.succ wF)).1 := by
        rw [viewTy_tel_shift2, hTelEq]
        exact viewTy_idxTy_lift 2 idxDoms wF
      have hMot2W := viewTy_wkBy hE hI [.assumption ihDom, .assumption dDom] hMot
      have hMotEq2 := viewTy_motTy_lift 2 idxDoms famHere wF wM
      have hMot2 := hMotEq2 ▸ hMot2W
      have hMotTy2W := viewTy_wkBy hE hI [.assumption ihDom, .assumption dDom] hMotTy
      have hSnd2 : (piTelA idxDoms (.pi famHere wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 =
          (piTelA idx2 (.pi (liftA idxDoms.length 2 famHere) wF (.sort wM) (.succ wM))
            (.imax wF (.succ wM))).2 :=
        viewTy_piTel_snd _ _ idxDoms idx2 (viewTy_liftDoms_snd 0 2 idxDoms).symm
      have hMotTy2 := congrArg ExprA.sort hSnd2 ▸ (hMotEq2 ▸ hMotTy2W)
      have hIdx2W := viewTy_wkBy hE hI [.assumption ihDom, .assumption dDom] hIdxTy
      have hIdxEq2 := viewTy_idxTy_lift 2 idxDoms wF
      have hIdxSnd2 : (piTelA idxDoms (.sort wF) (.succ wF)).2 =
          (piTelA idx2 (.sort wF) (.succ wF)).2 :=
        viewTy_piTel_snd _ _ idxDoms idx2 (viewTy_liftDoms_snd 0 2 idxDoms).symm
      have hIdx2 := congrArg ExprA.sort hIdxSnd2 ▸ (hIdxEq2 ▸ hIdx2W)
      have hApp1 : HasTyA E I n (.assumption dDom :: Γ)
          (.app (liftA 0 1 (foldAppsA (.const c ls) (pl ++ fl))) (.bvar 0))
          (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 fs res).1 := hη
      have hApp2W := viewTy_wkFront hE hI (.assumption ihDom) hApp1
      have hShift := viewTy_ctorFields_shift1 f ls wF res fs (pl.map (liftA 0 1)) σ.shift1
      have hpl2 : ((pl.map (liftA 0 1)).map (liftA 0 1)) = pl.map (liftA 0 2) :=
        viewTy_map_lift_add 1 1 pl
      have hLv : (ctorFieldsA f ls wF (pl.map (liftA 0 1)) σ.shift1 fs res).2 =
          (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).2 :=
        (ctorFieldsA_snd f ls wF res fs (pl.map (liftA 0 1)) σ.shift1).trans
          (ctorFieldsA_snd f ls wF res fs (pl.map (liftA 0 2)) σ.shift1.shift1).symm
      have hApp2 : HasTyA E I n (.assumption ihDom :: .assumption dDom :: Γ)
          (foldAppsA (.const c ls)
            (pl.map (liftA 0 2) ++ (fl.map (liftA 0 2) ++ [.bvar 1])))
          (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).1 :=
        viewTy_eta_fold2 c ls pl fl ▸ (hpl2 ▸ (hShift ▸ hApp2W))
      have hRestW := viewTy_wkFront hE hI (.assumption ihDom) tRest
      have hRest : HasTyA E I n (.assumption ihDom :: .assumption dDom :: Γ)
          (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).1
          (.sort (ctorFieldsA f ls wF (pl.map (liftA 0 2)) σ.shift1.shift1 fs res).2) :=
        congrArg ExprA.sort hLv ▸ (hpl2 ▸ (hShift ▸ hRestW))
      have hσ2 := substTyA_shift1 hE hI (substTyA_shift1 hE hI hσ dDom) ihDom
      have hHere2' : liftA idxDoms.length 2 famHere =
          foldAppsA (.const f ls)
            ((pl.map (liftA 0 2)).map (liftA 0 ni) ++ paramLocalsA ni) := by
        rw [hni]; exact hHere2
      have hsplit' : fsAll = (fsPre ++ [.drecD D idx]) ++ fs := by
        rw [List.append_assoc]; exact hsplit
      have hΓpe' : Γp = plainCtxA (fsPre ++ [.drecD D idx]) Γp0 := by
        rw [plainCtxA_append, ← hΓpe]; rfl
      have hj' : jp = plainIdxA (fsPre ++ [.drecD D idx]) 0 := by
        rw [plainIdxA_append, ← hj]; rfl
      have hplN' : pl.map (liftA 0 2) = (paramLocalsA np0).map (liftA 0 (d + 2)) := by
        rw [hplN, List.map_map]
        exact List.map_congr_left fun x _ =>
          liftA_liftA_merge 2 d 0 0 (Nat.le_refl 0) (Nat.zero_le _) x
      have hσge' : ∀ t, σ.shift1.shift1 (jp + t) = .bvar (t + (d + 2)) :=
        (substA_walk_ge (substA_walk_ge hσge).2).2
      obtain ⟨ih⟩ := viewTy_minor hE hI hR hIS hdd hσ2 hΓp hΓ2 hni2 hHere2' hTel2 hMot2 hMotTy2
        hIdx2 hApp2 hRest tl hsplit' hΓpe' hj' hplN' hσge'
      have hInner := HasTyA.pi (.assumption dDom :: Γ) ihDom wM _ _ hIH ih
      have hOuter := HasTyA.pi Γ dDom wF _ _ tD hInner
      unfold minorFieldsA
      exact ⟨hOuter⟩

end Minor

/-! ## (19) equations the recursor's telescope reuses -/

section RecAlg

theorem viewTy_instAt_bvar (k c : Nat) (B : ExprA) :
    instantiateA c (.bvar (k + c)) (liftA (c + 1) (k + 1) B) = liftA c k B := by
  induction B generalizing c with
  | bvar _ => bvarA_leaves
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app _ _ ihf ihx => simp only [instantiateA, liftA, ihf, ihx]
  | lam _ _ _ iha ihb =>
      simp only [instantiateA, liftA, iha]
      have hr : (if 0 ≤ k + c then ExprA.bvar (k + c + 1) else ExprA.bvar (k + c)) =
          ExprA.bvar (k + (c + 1)) := by
        simp only [Nat.zero_le, ite_true]
        exact congrArg ExprA.bvar (by omega)
      rw [hr, ihb]
  | pi _ _ _ _ iha ihb =>
      simp only [instantiateA, liftA, iha]
      have hr : (if 0 ≤ k + c then ExprA.bvar (k + c + 1) else ExprA.bvar (k + c)) =
          ExprA.bvar (k + (c + 1)) := by
        simp only [Nat.zero_le, ite_true]
        exact congrArg ExprA.bvar (by omega)
      rw [hr, ihb]
  | letE _ _ _ iha ihw ihb =>
      simp only [instantiateA, liftA, iha, ihw]
      have hr : (if 0 ≤ k + c then ExprA.bvar (k + c + 1) else ExprA.bvar (k + c)) =
          ExprA.bvar (k + (c + 1)) := by
        simp only [Nat.zero_le, ite_true]
        exact congrArg ExprA.bvar (by omega)
      rw [hr, ihb]

theorem viewTy_inst0_lift (k : Nat) (B : ExprA) :
    instantiate0A (.bvar k) (liftA 1 (k + 1) B) = liftA 0 k B := by
  simpa [instantiate0A, Nat.zero_add] using viewTy_instAt_bvar k 0 B

theorem viewTy_telCtx_length (ds : List (ExprA × Level)) :
    (telCtxA ds).length = ds.length := by
  simp [telCtxA, List.length_reverse, List.length_map]

theorem viewTy_liftDoms_add (c a b : Nat) :
    (ds : List (ExprA × Level)) →
      liftDomsA c a (liftDomsA c b ds) = liftDomsA c (b + a) ds
  | [] => rfl
  | (D, u) :: ds => by
      simp only [liftDomsA]
      rw [liftA_liftA_merge a b c c (Nat.le_refl _) (Nat.le_add_left c b) D]
      exact congrArg (fun t => (liftA c (b + a) D, u) :: t)
        (viewTy_liftDoms_add (c + 1) a b ds)

theorem viewTy_minorDoms_append_one (f : Nat) (ls : List Level) (wF wM : Level) (np j : Nat)
    (xs : List MinorDataA) (cd : MinorDataA) :
    minorDomsA f ls wF wM np j (xs ++ [cd]) =
      minorDomsA f ls wF wM np j xs ++
        [(liftA 0 (j + xs.length) (minorTyA f ls wF wM np cd).1,
          (minorTyA f ls wF wM np cd).2)] := by
  induction xs generalizing j with
  | nil =>
      simp only [List.nil_append, minorDomsA, List.length_nil, Nat.add_zero, List.append_nil]
  | cons x xs ih =>
      simp only [List.cons_append, minorDomsA, List.length_cons]
      refine congrArg (fun t => _ :: t) ?_
      have h := ih (j + 1)
      change minorDomsA f ls wF wM np (j + 1) (xs ++ [cd]) = _
      rw [h]
      exact congrArg (fun z => minorDomsA f ls wF wM np (j + 1) xs ++
        [(liftA 0 z (minorTyA f ls wF wM np cd).1, (minorTyA f ls wF wM np cd).2)])
        (by omega)

end RecAlg

/-! ## (20) parameter locals typed along their own telescope -/

section ParamArgs
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def viewTy_paramArgs (hE : EnvClosedA E) (hI : IotaLiftA I) {w : Level} :
    {Γ : LCtxA} → {ds : List (ExprA × Level)} → DomTyA E I n Γ ds →
    ArgsTyA E I n (telCtxA ds ++ Γ)
      (liftA 0 ds.length (piTelA ds (.sort w) (.succ w)).1) (paramLocalsA ds.length)
  | _, [], .nil _ => by
      simp only [piTelA, telCtxA, paramLocalsA, List.length_nil, List.map, List.reverse_nil,
        liftA, List.nil_append]
      exact ArgsTyA.nil w
  | Γ, (D, u) :: ds, .cons _ _ _ _ hD tl => by
      have ih := viewTy_paramArgs (w := w) hE hI tl
      simp only [List.length_cons, piTelA, paramLocalsA]
      rw [telCtxA_cons_append (D, u) ds Γ]
      have hlen : (telCtxA ((D, u) :: ds)).length = ds.length + 1 := by
        rw [viewTy_telCtx_length, List.length_cons]
      have hDW := viewTy_wkBy hE hI (telCtxA ((D, u) :: ds)) hD
      rw [hlen, telCtxA_cons_append (D, u) ds Γ] at hDW
      have hlu := viewTy_lookup_mid (telCtxA ds) D Γ
      rw [viewTy_telCtx_length] at hlu
      have hHead : HasTyA E I n (telCtxA ds ++ (.assumption D :: Γ))
          (.bvar ds.length) (liftA 0 (ds.length + 1) D) :=
        .bvar _ ds.length _ u hlu hDW
      have hInst := viewTy_inst0_lift ds.length (piTelA ds (.sort w) (.succ w)).1
      simp only [liftA]
      exact ArgsTyA.cons (liftA 0 (ds.length + 1) D) u
        (liftA 1 (ds.length + 1) (piTelA ds (.sort w) (.succ w)).1)
        (piTelA ds (.sort w) (.succ w)).2 (.bvar ds.length) (paramLocalsA ds.length) hHead
        (hInst.symm ▸ ih)

end ParamArgs

/-! ## (21) the family, opened at the judgment's level in the group's environment -/

section OpenFam
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end OpenFam

/-! ## (22) the motive, lifted past the minors, the indices and the major, is the
    tail telescope lifted under itself. -/

section RecMot

theorem viewTy_recMot_ty (f : Nat) (ls : List Level) (params indices : List (ExprA × Level))
    (wF wM : Level) (k : Nat) :
    liftA 0 (indices.length + k + 2) (motTyA f ls params indices wF wM).1 =
      liftA 0 (indices.length + 1)
        (piTelA (liftDomsA 0 (k + 1) indices ++
            [(liftA indices.length (k + 1) (famLocalsA f ls params.length indices.length), wF)])
          (.sort wM) (.succ wM)).1 := by
  let ni := indices.length
  have hni : ni = indices.length := rfl
  let fam := famLocalsA f ls params.length ni
  let tail := liftDomsA 0 (k + 1) indices ++ [(liftA ni (k + 1) fam, wF)]
  have hL := viewTy_mot_eq f ls params indices wF wM (ni + k + 2)
  have hlen : tail.length = ni + 1 := by
    show (liftDomsA 0 (k + 1) indices ++ [(liftA ni (k + 1) fam, wF)]).length = ni + 1
    simp only [List.length_append, List.length_singleton, liftDomsA_length]
  have hR : liftA 0 (ni + 1) (piTelA tail (.sort wM) (.succ wM)).1 =
      (piTelA (liftDomsA 0 (ni + 1) tail) (.sort wM) (.succ wM)).1 := by
    rw [viewTy_lift_piTel 0 (ni + 1) (.sort wM) (.succ wM) tail]
    rw [show 0 + tail.length = ni + 1 from by rw [hlen]; omega]
    rfl
  have hdom : liftDomsA 0 (ni + k + 2) indices ++ [(liftA ni (ni + k + 2) fam, wF)] =
      liftDomsA 0 (ni + 1) tail := by
    show liftDomsA 0 (ni + k + 2) indices ++ [(liftA ni (ni + k + 2) fam, wF)] =
      liftDomsA 0 (ni + 1)
        (liftDomsA 0 (k + 1) indices ++ [(liftA ni (k + 1) fam, wF)])
    rw [viewTy_liftDoms_append 0 (ni + 1), viewTy_liftDoms_add 0 (ni + 1) (k + 1)]
    have hlenI : (liftDomsA 0 (k + 1) indices).length = ni := by
      rw [liftDomsA_length, hni]
    rw [hlenI, Nat.zero_add]
    simp only [liftDomsA, List.nil_append]
    have hsum : (k + 1) + (ni + 1) = ni + k + 2 := by omega
    rw [hsum]
    refine congrArg (fun z => liftDomsA 0 (ni + k + 2) indices ++ [(z, wF)]) ?_
    rw [liftA_liftA_merge (ni + 1) (k + 1) ni ni (Nat.le_refl _) (Nat.le_add_left ni (k + 1))]
    exact congrArg (fun z => liftA ni z fam) (by omega)
  have hpi : (piTelA (liftDomsA 0 (ni + k + 2) indices ++ [(liftA ni (ni + k + 2) fam, wF)])
      (.sort wM) (.succ wM)).1 =
      (piTelA (liftDomsA 0 (ni + 1) tail) (.sort wM) (.succ wM)).1 :=
    congrArg (fun ds => (piTelA ds (.sort wM) (.succ wM)).1) hdom
  simpa [hni, fam, Nat.add_assoc] using hL.trans (hpi.trans hR.symm)

end RecMot

/-! ## (23) T2. A constructor applied to the parameter locals, then one minor,
    then the minors' telescope, then the recursor type. -/

section RecType
variable {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm : CheckedMemberA}
variable {fv : FamViewA fm}
variable {cs : List (GroupCtorA I E f fm fv)} {elim : RecElimA}

structure ViewTyCtorAtA (gc : GroupCtorA I E f fm fv) : Type where
  app : HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra)
    (telCtxA fv.params)
    (foldAppsA (.const gc.ref (canonLevelsA fm.arity)) (paramLocalsA fv.params.length))
    (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA fv.params.length) SubstA.id
      gc.view.fields gc.view.res).1
  cty : HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra)
    (telCtxA fv.params)
    (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA fv.params.length) SubstA.id
      gc.view.fields gc.view.res).1
    (.sort (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA fv.params.length)
      SubstA.id gc.view.fields gc.view.res).2)
  fld : FieldsTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra)
    (fun k => liftA 0 k fv.idxTelA) (telCtxA fv.params) 0
    gc.view.fields gc.view.res

theorem viewTy_ctorAt {u : Level}
    (hFam : HasTyA E I fm.arity [] fm.mtypeA (.sort u))
    (hfresh : GroupFreshA E f fm (cs.map GroupCtorA.entry))
    (hE : EnvClosedA E)
    (hG : EnvClosedA (groupEnvA E f fm (cs.map GroupCtorA.entry)))
    (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I)
    (hRG : IotaRecHeadA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I)
    (huniq : ViewTySortUniqA E I fm.arity)
    (gc : GroupCtorA I E f fm fv) (hgc : gc ∈ cs)
    (pack : ViewTyOpenA (E := groupEnvA E f fm (cs.map GroupCtorA.entry)) (I := I)
      (n := fm.arity + elim.extra) f fm fv (elim.motiveLevel fm.arity)) :
    Nonempty (ViewTyCtorAtA (cs := cs) (elim := elim) gc) := by
  let G := groupEnvA E f fm (cs.map GroupCtorA.entry)
  let n := fm.arity + elim.extra
  have hab : fm.arity ≤ n := Nat.le_add_right _ _
  have hpreE : PrefixA E G := prefixA_groupEnvA hfresh
  have hpreX : PrefixA (extendEnvA E f fm) G := prefixA_extend_groupEnvA hfresh
  have hFamPi : HasTyA E I fm.arity []
      (piTelA fv.params fv.idxTelA (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2).1
      (.sort u) := by
    have h := fv.stored ▸ hFam
    simpa [FamViewA.idxTelA, piTelA_append] using h
  have hσ0 := viewTy_mirrorId (n := fm.arity) hE hI hIS hR huniq
    (substTyA_id hE hI CtxWfA.nil) CtxWfA.nil gc.view.mirrorsConv hFamPi
  have hσ2 := viewTy_subst_env hpreE (viewTy_substLvl hab hσ0)
  have hnilP : telCtxA fv.params ++ [] = telCtxA fv.params := List.append_nil _
  have hnilM : telCtxA gc.view.mirrors ++ [] = telCtxA gc.view.mirrors := List.append_nil _
  have hσ : SubstTyA G I n (telCtxA fv.params) SubstA.id (telCtxA gc.view.mirrors) :=
    hnilP ▸ (hnilM ▸ hσ2)
  have hT : HasTyA G I n [] gc.member.mtypeA (.sort gc.u) :=
    viewTy_lvlWk hab (gc.harity ▸ hasTyEnvA hpreX gc.hT)
  have hnC : gc.member.arity ≤ n := by rw [gc.harity]; exact hab
  have hmem := members_groupEnvA_ctor hfresh hgc
  have hConst := gc.harity ▸ viewTy_famConst hnC hmem hT
  have hStored : HasTyA G I n []
      (ctorTypeA f (canonLevelsA fm.arity) fv.sort gc.view.mirrors gc.view.fields gc.view.res)
      (.sort gc.u) := gc.view.stored ▸ hT
  have hTyPi : HasTyA G I n []
      (piTelA gc.view.mirrors
        (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA gc.view.mirrors.length)
          SubstA.id gc.view.fields gc.view.res).1
        (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA gc.view.mirrors.length)
          SubstA.id gc.view.fields gc.view.res).2).1
      (.sort gc.u) := by
    simpa [ctorTypeA] using hStored
  have hConstStored : HasTyA G I n [] (.const gc.ref (canonLevelsA fm.arity))
      (ctorTypeA f (canonLevelsA fm.arity) fv.sort gc.view.mirrors gc.view.fields gc.view.res) :=
    gc.view.stored ▸ hConst
  have hConstPi : HasTyA G I n [] (.const gc.ref (canonLevelsA fm.arity))
      (piTelA gc.view.mirrors
        (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA gc.view.mirrors.length)
          SubstA.id gc.view.fields gc.view.res).1
        (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA gc.view.mirrors.length)
          SubstA.id gc.view.fields gc.view.res).2).1 := by
    simpa [ctorTypeA] using hConstStored
  have hApp0 := viewTy_applyParams hG hI (Γ := []) CtxWfA.nil hTyPi hConstPi
  have hApp1 := hnilM ▸ hApp0
  have hSub := hasTyA_substA hG hI (iotaRecHeadTypedA_of hRG) hIS hσ hApp1
  have hlen : gc.view.mirrors.length = fv.params.length := gc.view.mirrorsConv.length
  have app0 := hlen ▸ hSub
  have app : HasTyA G I n (telCtxA fv.params)
      (foldAppsA (.const gc.ref (canonLevelsA fm.arity)) (paramLocalsA fv.params.length))
      (ctorFieldsA f (canonLevelsA fm.arity) fv.sort (paramLocalsA fv.params.length) SubstA.id
        gc.view.fields gc.view.res).1 := by
    simpa [substA_id] using app0
  have fld := viewTy_fields_env hpreE (viewTy_fieldsLvl hab gc.view.typed)
  have hσId := substTyA_id hG hI pack.ctxP
  have hpl : paramLocalsA fv.params.length =
      (paramLocalsA fv.params.length).map (substA SubstA.id) := (map_substA_id _).symm
  have hFp := (liftA_zero 0 fv.idxTelA).symm ▸ pack.atParams
  have hIdx := (liftA_zero 0 fv.idxTelA).symm ▸ pack.idxTy
  have hTel : IsIdxTel (liftA 0 0 fv.idxTelA) fv.sort :=
    (liftA_zero 0 fv.idxTelA).symm ▸ isIdxTel_piTel fv.sort (.succ fv.sort) fv.indices
  -- the δ-reached fields' evidence, transported into the group scope at this level
  -- (R-NoDeltaRec-4d-iii): `drecD_typed` lives at the family's extension.
  have hdd : ∀ fsPre D idx fsRest,
      gc.view.fields = fsPre ++ FieldA.drecD D idx :: fsRest →
      Nonempty (HasTyA G I n (plainCtxA fsPre (telCtxA fv.params)) D (.sort fv.sort)) ∧
      Nonempty (ConvA G I n (plainCtxA fsPre (telCtxA fv.params)) D
        (foldAppsA (.const f (canonLevelsA fm.arity))
          ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idx))
        (.sort fv.sort)) :=
    fun fsPre D idx fsRest hsplt =>
      match gc.view.drecD_typed fsPre D idx fsRest hsplt with
      | ⟨⟨hd⟩, ⟨hc⟩, _⟩ =>
          ⟨⟨viewTy_lvlWk hab (hasTyEnvA hpreX hd)⟩,
            ⟨viewTy_convLvlWk hab (convEnvA hpreX hc)⟩⟩
  obtain ⟨hconv⟩ := ctorFieldsA_conv_norm (n := fm.arity + elim.extra) hG hI
    (iotaRecHeadTypedA_of hRG) hIS
    rfl hdd hσId pack.ctxP pack.ctxP (k := 0)
    hpl (map_liftA_zero _).symm substA_walk_ge_id hFp hIdx hTel
    (List.nil_append _).symm rfl rfl rfl fld
  have cty := convA_hasTy_left hG hI hRG hIS pack.ctxP hconv
  exact ⟨{ app := app, cty := cty, fld := fld }⟩

theorem viewTy_oneMinor {u : Level}
    (hFam : HasTyA E I fm.arity [] fm.mtypeA (.sort u))
    (hfresh : GroupFreshA E f fm (cs.map GroupCtorA.entry))
    (hE : EnvClosedA E) (hG : EnvClosedA (groupEnvA E f fm (cs.map GroupCtorA.entry)))
    (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hRG : IotaRecHeadA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I)
    (huniq : ViewTySortUniqA E I fm.arity)
    (gc : GroupCtorA I E f fm fv) (hgc : gc ∈ cs)
    (pack : ViewTyOpenA (E := (groupEnvA E f fm (cs.map GroupCtorA.entry))) (I := I) (n := (fm.arity + elim.extra)) f fm fv (elim.motiveLevel fm.arity)) :
    Nonempty (HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra)
      (.assumption (motTyA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort (elim.motiveLevel fm.arity)).1 ::
        telCtxA fv.params)
      (minorTyA f (canonLevelsA fm.arity) fv.sort (elim.motiveLevel fm.arity) fv.params.length gc.minorData).1
      (.sort (minorTyA f (canonLevelsA fm.arity) fv.sort (elim.motiveLevel fm.arity) fv.params.length
        gc.minorData).2)) := by
  let ls := canonLevelsA fm.arity
  let wM := (elim.motiveLevel fm.arity)
  let mot := motTyA f ls fv.params fv.indices fv.sort wM
  let np := fv.params.length
  let ni := fv.indices.length
  let Γ0 : LCtxA := .assumption mot.1 :: telCtxA fv.params
  let pl := (paramLocalsA np).map (liftA 0 1)
  obtain ⟨cat⟩ := viewTy_ctorAt hFam hfresh hE hG hI hIS hR hRG huniq gc hgc pack
  have hΓ : CtxWfA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra) Γ0 := CtxWfA.assumption pack.ctxP pack.mot
  have hσ := substTyA_shift1 hG hI (substTyA_id hG hI pack.ctxP) mot.1
  have hAppW := viewTy_wkFront hG hI (.assumption mot.1) cat.app
  have hShift := viewTy_ctorFields_shift1 f ls fv.sort gc.view.res gc.view.fields
    (paramLocalsA np) SubstA.id
  have hApp1 := hShift ▸ (liftA_foldAppsA 0 1 (.const gc.ref ls) (paramLocalsA np) ▸ hAppW)
  have hApp := (List.append_nil ((paramLocalsA np).map (liftA 0 1))).symm ▸ hApp1
  have hCW := hShift ▸ viewTy_wkFront hG hI (.assumption mot.1) cat.cty
  have hSndC : (ctorFieldsA f ls fv.sort pl SubstA.id.shift1 gc.view.fields gc.view.res).2 =
      (ctorFieldsA f ls fv.sort (paramLocalsA np) SubstA.id gc.view.fields gc.view.res).2 := by
    rw [ctorFieldsA_snd, ctorFieldsA_snd]
  have hCTy := congrArg ExprA.sort hSndC.symm ▸ hCW
  let famHere := liftA ni 1 (famLocalsA f ls np ni)
  let idxDoms := liftDomsA 0 1 fv.indices
  have hni : idxDoms.length = ni := by simp [idxDoms, ni, liftDomsA_length]
  have hHere : famHere =
      foldAppsA (.const f ls) (pl.map (liftA 0 ni) ++ paramLocalsA ni) := by
    simpa [famHere, pl] using viewTy_famHere_lift1 f ls ni (paramLocalsA np)
  have hTelEq : substA SubstA.id.shift1 (liftA 0 0 fv.idxTelA) =
      (piTelA idxDoms (.sort fv.sort) (.succ fv.sort)).1 := by
    rw [liftA_zero, viewTy_subst_shift1, substA_id]
    simpa [idxDoms, FamViewA.idxTelA] using viewTy_idxTy_lift 1 fv.indices fv.sort
  have hMotW := viewTy_wkFront hG hI (.assumption mot.1) pack.mot
  have hBvar : HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra) Γ0 (.bvar 0) (liftA 0 1 mot.1) :=
    HasTyA.bvar _ 0 _ mot.2 rfl hMotW
  have hMotEq := viewTy_motTy_lift 1 fv.indices (famLocalsA f ls np ni) fv.sort wM
  have hMot := hMotEq ▸ hBvar
  have hSnds :
      (piTelA fv.indices
        (.pi (famLocalsA f ls np ni) fv.sort (.sort wM) (.succ wM))
        (.imax fv.sort (.succ wM))).2 =
      (piTelA idxDoms
        (.pi famHere fv.sort (.sort wM) (.succ wM))
        (.imax fv.sort (.succ wM))).2 :=
    viewTy_piTel_snd (w := .imax fv.sort (.succ wM))
      (.pi (famLocalsA f ls np ni) fv.sort (.sort wM) (.succ wM))
      (.pi famHere fv.sort (.sort wM) (.succ wM))
      fv.indices idxDoms (viewTy_liftDoms_snd 0 1 fv.indices).symm
  have hMotTy := congrArg ExprA.sort hSnds ▸ (hMotEq ▸ hMotW)
  have hIdxW := viewTy_wkFront hG hI (.assumption mot.1) pack.idxTy
  have hIdxEq := viewTy_idxTy_lift 1 fv.indices fv.sort
  have hIdxSnd :
      (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2 =
      (piTelA idxDoms (.sort fv.sort) (.succ fv.sort)).2 :=
    viewTy_piTel_snd (w := .succ fv.sort) (.sort fv.sort) (.sort fv.sort) fv.indices idxDoms
      (viewTy_liftDoms_snd 0 1 fv.indices).symm
  have hIdxTy := congrArg ExprA.sort hIdxSnd ▸ (hIdxEq ▸ hIdxW)
  have hApp' : HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra) Γ0
      (foldAppsA (.const gc.ref ls) (pl ++ []))
      (ctorFieldsA f ls fv.sort pl SubstA.id.shift1 gc.view.fields gc.view.res).1 := by
    simpa [liftA, pl, Γ0] using hApp
  have hCTy' : HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra) Γ0
      (ctorFieldsA f ls fv.sort pl SubstA.id.shift1 gc.view.fields gc.view.res).1
      (.sort (ctorFieldsA f ls fv.sort pl SubstA.id.shift1 gc.view.fields gc.view.res).2) := by
    simpa [liftA, pl, Γ0] using hCTy
  -- the δ-reached fields' evidence, transported into the group scope at this level
  -- (R-NoDeltaRec-4d-iii): `drecD_typed` lives at the family's extension.
  have habM : fm.arity ≤ fm.arity + elim.extra := Nat.le_add_right _ _
  have hpreXM : PrefixA (extendEnvA E f fm)
      (groupEnvA E f fm (cs.map GroupCtorA.entry)) := prefixA_extend_groupEnvA hfresh
  have hddM : ∀ fsPre D idx fsRest,
      gc.view.fields = fsPre ++ FieldA.drecD D idx :: fsRest →
      Nonempty (HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I
          (fm.arity + elim.extra) (plainCtxA fsPre (telCtxA fv.params)) D (.sort fv.sort)) ∧
      Nonempty (ConvA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I
          (fm.arity + elim.extra) (plainCtxA fsPre (telCtxA fv.params)) D
          (foldAppsA (.const f ls)
            ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idx))
          (.sort fv.sort)) :=
    fun fsPre D idx fsRest hsplt =>
      match gc.view.drecD_typed fsPre D idx fsRest hsplt with
      | ⟨⟨hd⟩, ⟨hc⟩, _⟩ =>
          ⟨⟨viewTy_lvlWk habM (hasTyEnvA hpreXM hd)⟩,
            ⟨viewTy_convLvlWk habM (convEnvA hpreXM hc)⟩⟩
  obtain ⟨hMin⟩ := viewTy_minor hG hI hRG hIS (fsAll := gc.view.fields)
    (np0 := fv.params.length) (Γp0 := telCtxA fv.params) hddM hσ pack.ctxP hΓ
    (k := 0) (pl := pl) (fl := [])
    (mot := ExprA.bvar 0) (famHere := famHere) (idxDoms := idxDoms) hni hHere hTelEq hMot
    hMotTy hIdxTy (fs := gc.view.fields) (fsPre := []) (jp := 0) (d := 1)
    (res := gc.view.res) hApp' hCTy' cat.fld
    (List.nil_append _).symm rfl rfl rfl (substA_walk_ge substA_walk_ge_id).2
  exact ⟨by simpa [minorTyA, GroupCtorA.minorData, ls, wM] using hMin⟩

theorem viewTy_minorDoms {u : Level}
    (hFam : HasTyA E I fm.arity [] fm.mtypeA (.sort u))
    (hfresh : GroupFreshA E f fm (cs.map GroupCtorA.entry))
    (hE : EnvClosedA E) (hG : EnvClosedA (groupEnvA E f fm (cs.map GroupCtorA.entry)))
    (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hRG : IotaRecHeadA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I)
    (huniq : ViewTySortUniqA E I fm.arity)
    (pack : ViewTyOpenA (E := (groupEnvA E f fm (cs.map GroupCtorA.entry))) (I := I) (n := (fm.arity + elim.extra)) f fm fv (elim.motiveLevel fm.arity)) :
    (earlier cds : List (GroupCtorA I E f fm fv)) →
    (hmem : ∀ c, c ∈ cds → c ∈ cs) →
    Nonempty (DomTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra)
      (telCtxA (minorDomsA f (canonLevelsA fm.arity) fv.sort (elim.motiveLevel fm.arity) fv.params.length 0
        (earlier.map GroupCtorA.minorData)) ++
        (.assumption (motTyA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort (elim.motiveLevel fm.arity)).1 ::
          telCtxA fv.params))
      (minorDomsA f (canonLevelsA fm.arity) fv.sort (elim.motiveLevel fm.arity) fv.params.length earlier.length
        (cds.map GroupCtorA.minorData)))
  | earlier, [], _ => by
      simp only [List.map_nil, minorDomsA]
      exact ⟨DomTyA.nil _⟩
  | earlier, c :: cds, hmem => by
      let ls := canonLevelsA fm.arity
      let wM := (elim.motiveLevel fm.arity)
      let wF := fv.sort
      let np := fv.params.length
      let mot := motTyA f ls fv.params fv.indices wF wM
      let Γ0 : LCtxA := .assumption mot.1 :: telCtxA fv.params
      obtain ⟨hOne⟩ := viewTy_oneMinor hFam hfresh hE hG hI hIS hR hRG huniq c
        (hmem c (List.mem_cons_self c cds)) pack
      have hW0 := viewTy_wkBy hG hI
        (telCtxA (minorDomsA f ls wF wM np 0 (earlier.map GroupCtorA.minorData))) hOne
      have hlen : (telCtxA (minorDomsA f ls wF wM np 0 (earlier.map GroupCtorA.minorData))).length =
          earlier.length := by
        rw [viewTy_telCtx_length, minorDomsA_length, List.length_map]
      have hW := hlen ▸ hW0
      have hmem' : ∀ c', c' ∈ cds → c' ∈ cs := fun c' hm => hmem c' (List.mem_cons_of_mem _ hm)
      obtain ⟨ih0⟩ := viewTy_minorDoms hFam hfresh hE hG hI hIS hR hRG huniq pack
        (earlier ++ [c]) cds hmem'
      have ih : DomTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I (fm.arity + elim.extra)
          (telCtxA (minorDomsA f ls wF wM np 0 ((earlier ++ [c]).map GroupCtorA.minorData)) ++ Γ0)
          (minorDomsA f ls wF wM np (earlier.length + 1) (cds.map GroupCtorA.minorData)) := by
        simpa [ls, wF, wM, np, Γ0, mot, List.length_append, List.length_singleton] using ih0
      have hctx :
          telCtxA (minorDomsA f ls wF wM np 0 ((earlier ++ [c]).map GroupCtorA.minorData)) ++ Γ0 =
          .assumption (liftA 0 earlier.length (minorTyA f ls wF wM np c.minorData).1) ::
            (telCtxA (minorDomsA f ls wF wM np 0 (earlier.map GroupCtorA.minorData)) ++ Γ0) := by
        rw [List.map_append, show [c].map GroupCtorA.minorData = [c.minorData] from rfl,
          viewTy_minorDoms_append_one, telCtxA_snoc]
        simp [List.length_map, Nat.zero_add, List.cons_append]
      exact ⟨DomTyA.cons _
        (liftA 0 earlier.length (minorTyA f ls wF wM np c.minorData).1)
        (minorTyA f ls wF wM np c.minorData).2
        (minorDomsA f ls wF wM np (earlier.length + 1) (cds.map GroupCtorA.minorData))
        hW (hctx ▸ ih)⟩

/-- a parameter-local vector is fixed by a lift whose cutoff is its own length. -/
theorem viewTy_paramLocals_high (a ni : Nat) :
    (paramLocalsA ni).map (liftA ni a) = paramLocalsA ni := by
  have go : (j : Nat) → j ≤ ni → (paramLocalsA j).map (liftA ni a) = paramLocalsA j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [paramLocalsA, List.map_cons, liftA]
        rw [if_neg (show ¬ ni ≤ j from
          Nat.not_le_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj))]
        exact congrArg (fun t => .bvar j :: t) (ih (Nat.le_of_succ_le hj))
  exact go ni (Nat.le_refl _)

/-- the major's subject: the family, lifted past the motive and the minors, applied to the
    index locals, is the family's local application lifted past those same binders. -/
theorem viewTy_recMajor_subj (f : Nat) (ls : List Level) (np ni k : Nat) :
    foldAppsA (liftA 0 ni (liftA 0 (k + 1)
        (foldAppsA (.const f ls) (paramLocalsA np)))) (paramLocalsA ni) =
      liftA ni (k + 1) (famLocalsA f ls np ni) := by
  have hcomm : liftA 0 ni (liftA 0 (k + 1) (foldAppsA (.const f ls) (paramLocalsA np))) =
      liftA 0 (ni + (k + 1)) (foldAppsA (.const f ls) (paramLocalsA np)) := by
    rw [liftA_liftA_merge ni (k + 1) 0 0 (Nat.le_refl _) (Nat.zero_le _)]
    exact congrArg (fun z => liftA 0 z _) (by omega)
  rw [hcomm]
  have hpull := (liftA_foldAppsA ni (k + 1)
      (liftA 0 ni (foldAppsA (.const f ls) (paramLocalsA np))) (paramLocalsA ni)).symm
  rw [viewTy_paramLocals_high (k + 1) ni] at hpull
  rw [liftA_liftA_merge (k + 1) ni 0 ni (Nat.zero_le _) (Nat.le_refl _)] at hpull
  rw [hpull, viewTy_double_apply (f := .const f ls) (fun _ => rfl) np ni]
  rfl

/-- the body's subject: the motive, past the minors, applied to the index locals and the
    major, is `recBodyA`. -/
theorem viewTy_recBody_eq (ni k : Nat) :
    foldAppsA (liftA 0 (ni + 1) (.bvar k)) (paramLocalsA (ni + 1)) = recBodyA ni k := by
  simp only [liftA, Nat.zero_le, ite_true, recBodyA]
  rw [← viewTy_recBody_locals]
  exact congrArg (fun i => foldAppsA (.bvar i) _) (by omega)

/-! `IotaSubstA`, `EnvSemA` and `PosValA` are not in the dispatch's parenthetical. The
    substitution lemma and the mirror collapse take them, so they are premises of
    `groupRecTypeA_hasTy`. The collapse itself takes only sort uniqueness. `CtxWfA` of
    the empty context is built (`.nil`), not hypothesized. The judgment is at
    `fm.arity + elim.extra`; derivations stated at `fm.arity` are walked by
    `viewTy_lvlWk`. -/

theorem groupRecTypeA_hasTy_ofUniq {u : Level}
    (hFam : HasTyA E I fm.arity [] fm.mtypeA (.sort u))
    (hfresh : GroupFreshA E f fm (cs.map GroupCtorA.entry))
    (hE : EnvClosedA E)
    (hG : EnvClosedA (groupEnvA E f fm (cs.map GroupCtorA.entry)))
    (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I)
    (hRG : IotaRecHeadA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I)
    (huniq : ViewTySortUniqA E I fm.arity) :
    ∃ w : Level, Nonempty (HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I
      (fm.arity + elim.extra) [] (groupRecTypeA fv cs elim) (.sort w)) := by
  let G := groupEnvA E f fm (cs.map GroupCtorA.entry)
  let n := fm.arity + elim.extra
  let ls := canonLevelsA fm.arity
  let wF := fv.sort
  let wM := elim.motiveLevel fm.arity
  let params := fv.params
  let indices := fv.indices
  let cds := cs.reverse.map GroupCtorA.minorData
  let k := cds.length
  let ni := indices.length
  let mot := motTyA f ls params indices wF wM
  let minors := minorDomsA f ls wF wM params.length 0 cds
  let front := (params ++ [mot]) ++ minors
  let liftIdx := liftDomsA 0 (k + 1) indices
  let major : ExprA × Level :=
    (liftA ni (k + 1) (famLocalsA f ls params.length ni), wF)
  let tail := liftIdx ++ [major]
  let Δ := telCtxA minors ++ [.assumption mot.1]
  let Γmid := telCtxA minors ++ (.assumption mot.1 :: telCtxA params)
  have hab : fm.arity ≤ n := Nat.le_add_right _ _
  have hpre : PrefixA E G := prefixA_groupEnvA hfresh
  have hFamG : HasTyA G I n [] fm.mtypeA (.sort u) :=
    viewTy_lvlWk hab (hasTyEnvA hpre hFam)
  have hmem : G.members f = some fm :=
    groupEnvA_family (cs.map GroupCtorA.entry) hfresh
  let pack := viewTy_openFam (E := G) (I := I) (n := n) (fv := fv) hG hI hFamG hmem hab wM
  have hMot : HasTyA G I n (telCtxA params) mot.1 (.sort mot.2) := by
    simpa [mot, ls, wF, wM, params, indices] using pack.mot
  have hCtxPM : telCtxA (params ++ [mot]) = .assumption mot.1 :: telCtxA params := by
    simp only [telCtxA, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  have domMot : DomTyA G I n (telCtxA params) [mot] :=
    .cons (telCtxA params) mot.1 mot.2 [] hMot (.nil _)
  have domPM : DomTyA G I n [] (params ++ [mot]) :=
    viewTy_dom_append (by simpa [params] using pack.domP)
      ((List.append_nil (telCtxA params)).symm ▸ domMot)
  obtain ⟨domMin0⟩ := viewTy_minorDoms hFam hfresh hE hG hI hIS hR hRG huniq pack
    [] cs.reverse (fun _ hm => List.mem_reverse.mp hm)
  have domMin : DomTyA G I n (telCtxA (params ++ [mot])) minors := by
    have h := hCtxPM.symm ▸ domMin0
    simpa [minors, mot, ls, wF, wM, params, cds, List.map_nil, List.length_nil,
      minorDomsA, telCtxA, List.nil_append] using h
  have domFront : DomTyA G I n [] front := by
    have domMinApp : DomTyA G I n (telCtxA (params ++ [mot]) ++ []) minors := by
      rw [List.append_nil]
      exact domMin
    simpa [front] using viewTy_dom_append domPM domMinApp
  have hlenΔ : Δ.length = k + 1 := by
    simp only [Δ, k, minors, List.length_append, List.length_singleton,
      viewTy_telCtx_length, minorDomsA_length]
  have hΓΔ : Γmid = Δ ++ telCtxA params := by
    simp only [Γmid, Δ, List.append_assoc, List.singleton_append]
  have hΓmid : CtxWfA G I n Γmid := by
    have hΓ0 : CtxWfA G I n (telCtxA (params ++ [mot])) := by
      rw [hCtxPM]
      exact .assumption (by simpa [params] using pack.ctxP) hMot
    have h0 := viewTy_ctxOfDom domMin hΓ0
    simpa [Γmid, hCtxPM, minors] using h0
  have domIdx : DomTyA G I n Γmid liftIdx := by
    have h0 := viewTy_dom_wkBy hG hI Δ (by simpa [params, indices] using pack.domI)
    have h1 := hΓΔ.symm ▸ (hlenΔ ▸ h0)
    simpa [liftIdx, indices] using h1
  have hIdxLift := viewTy_idxTy_lift (k + 1) indices wF
  have hIdxTy : HasTyA G I n Γmid (piTelA liftIdx (.sort wF) (.succ wF)).1
      (.sort (piTelA indices (.sort wF) (.succ wF)).2) := by
    have h0 := viewTy_wkBy hG hI Δ (by simpa [params] using pack.idxTy)
    have h1 := hΓΔ.symm ▸ (hlenΔ ▸ h0)
    simpa [liftIdx, indices, wF, FamViewA.idxTelA, hIdxLift] using h1
  have hAt : HasTyA G I n Γmid
      (liftA 0 (k + 1) (foldAppsA (.const f ls) (paramLocalsA params.length)))
      (piTelA liftIdx (.sort wF) (.succ wF)).1 := by
    have h0 := viewTy_wkBy hG hI Δ (by simpa [params, ls] using pack.atParams)
    have h1 := hΓΔ.symm ▸ (hlenΔ ▸ h0)
    simpa [liftIdx, indices, wF, ls, params, FamViewA.idxTelA, hIdxLift] using h1
  have hAppIdx := viewTy_applyParams hG hI hΓmid hIdxTy hAt
  have hlenI : liftIdx.length = ni := by
    simp [liftIdx, ni, indices, liftDomsA_length]
  have hMaj : HasTyA G I n (telCtxA liftIdx ++ Γmid) major.1 (.sort wF) := by
    have h := hlenI ▸ hAppIdx
    simpa [major, ni, k, ls, params, viewTy_recMajor_subj f ls params.length ni k] using h
  have domTail : DomTyA G I n Γmid tail := by
    have h := viewTy_dom_append domIdx
      (.cons _ major.1 major.2 [] hMaj (.nil _))
    simpa [tail] using h
  have hPiTail := viewTy_pi domTail (.sort (telCtxA tail ++ Γmid) wM)
  have hMotEq := viewTy_mot_eq f ls params indices wF wM (k + 1)
  have hEqTail : (piTelA (liftDomsA 0 (k + 1) indices ++
      [(liftA indices.length (k + 1)
        (famLocalsA f ls params.length indices.length), wF)])
      (.sort wM) (.succ wM)).1 = (piTelA tail (.sort wM) (.succ wM)).1 := by
    simp [tail, major, liftIdx, ni, k, indices, params]
  have hLu : lookupTypeA Γmid k = some (liftA 0 (k + 1) mot.1) := by
    have h0 := viewTy_lookup_mid (telCtxA minors) mot.1 (telCtxA params)
    have hlenM : (telCtxA minors).length = k := by
      simp [minors, k, viewTy_telCtx_length, minorDomsA_length]
    simpa [Γmid, mot, hlenM] using h0
  have hALift : HasTyA G I n Γmid (liftA 0 (k + 1) mot.1)
      (.sort (piTelA tail (.sort wM) (.succ wM)).2) :=
    hMotEq.symm ▸ (hEqTail.symm ▸ hPiTail)
  have hBvar : HasTyA G I n Γmid (.bvar k) (piTelA tail (.sort wM) (.succ wM)).1 :=
    hEqTail ▸ (hMotEq ▸ .bvar Γmid k (liftA 0 (k + 1) mot.1)
      (piTelA tail (.sort wM) (.succ wM)).2 hLu hALift)
  have hBody0 := viewTy_applyParams hG hI hΓmid hPiTail hBvar
  have hlenT : tail.length = ni + 1 := by
    simp [tail, liftIdx, ni, indices, List.length_append, List.length_singleton,
      liftDomsA_length]
  have hBody : HasTyA G I n (telCtxA tail ++ Γmid) (recBodyA ni k) (.sort wM) :=
    viewTy_recBody_eq ni k ▸ (hlenT ▸ hBody0)
  have hΓfront : Γmid = telCtxA front := by
    simp only [front, Γmid, telCtxA_append, hCtxPM]
  have hBodyAll : HasTyA G I n (telCtxA (front ++ tail) ++ []) (recBodyA ni k)
      (.sort wM) := by
    rw [telCtxA_append, List.append_nil, ← hΓfront]
    exact hBody
  have domAll : DomTyA G I n [] (front ++ tail) :=
    viewTy_dom_append domFront
      ((List.append_nil _).symm ▸ (hΓfront.symm ▸ domTail))
  have hDoms : front ++ tail = recDomsA f ls params indices wF wM cds := by
    simp only [front, tail, major, liftIdx, minors, mot, ni, k, ls, wF, wM, params,
      indices, recDomsA, List.append_assoc]
  have hPi := hDoms ▸ viewTy_pi domAll hBodyAll
  exact ⟨(piTelA (recDomsA f ls params indices wF wM cds) (recBodyA ni k) wM).2,
    ⟨by simpa [groupRecTypeA, recTypeA, ls, wF, wM, params, indices, cds, ni, k] using hPi⟩⟩

theorem groupRecTypeA_hasTy_der {u : Level} {ρ₀ : Nat → Nat}
    (hFam : HasTyA E I fm.arity [] fm.mtypeA (.sort u))
    (hfresh : GroupFreshA E f fm (cs.map GroupCtorA.entry))
    (hE : EnvClosedA E)
    (hG : EnvClosedA (groupEnvA E f fm (cs.map GroupCtorA.entry)))
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I)
    (hRG : IotaRecHeadA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I)
    (hS : EnvSemA E I fm.arity ρ₀) (hρ : PosValA ρ₀) :
    ∃ w : Level, Nonempty (HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I
      (fm.arity + elim.extra) [] (groupRecTypeA fv cs elim) (.sort w)) :=
  groupRecTypeA_hasTy_ofUniq hFam hfresh hE hG hI hIS hR hRG (by
    intro Γ X a b hΓ ha hb
    exact sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ ha hb)

theorem groupRecTypeA_hasTy {u : Level} {ρ₀ : Nat → Nat}
    (hFam : HasTyA E I fm.arity [] fm.mtypeA (.sort u))
    (hfresh : GroupFreshA E f fm (cs.map GroupCtorA.entry))
    (hE : EnvClosedA E)
    (hG : EnvClosedA (groupEnvA E f fm (cs.map GroupCtorA.entry)))
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I)
    (hRG : IotaRecHeadA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I)
    (hS : EnvSemA E I fm.arity ρ₀) (hρ : PosValA ρ₀) :
    ∃ w, Nonempty (HasTyA (groupEnvA E f fm (cs.map GroupCtorA.entry)) I
      (fm.arity + elim.extra) [] (groupRecTypeA fv cs elim) (.sort w)) :=
  groupRecTypeA_hasTy_der hFam hfresh hE hG hEN hNC hI hIS hR hRG hS hρ

end RecType

/-! ## (24) T2's teeth. Nat's `.anySort` recursor is the stored member. There is no
    stored `.propOnly` member, and the indexed family has no stored recursor, so those
    three teeth conclude at `groupRecTypeA` itself. None names `pinBoxCtorTy`,
    `pinSuccPiTy`, or `pinNatGroupRecA.hT`. -/

def viewTy_idxGroupCtorA : GroupCtorA noIotaA emptyEnvA 0 (pinFamFA 0) pinFamF0ViewA :=
  { ref := 1
    member := viewTy_idxCtorA
    hcls := rfl
    hnobody := rfl
    harity := rfl
    hnp := rfl
    hclT := fun _ => rfl
    u := .imax (.succ .zero) (.succ .zero)
    hT := viewTy_idxCtorTy
    hlvl := rfl
    view := viewTy_idxViewA
    hnorm := rfl
    hclN := fun _ => rfl
    hlvlN := rfl }

theorem viewTy_idxGroup_fresh :
    GroupFreshA emptyEnvA 0 (pinFamFA 0) [viewTy_idxGroupCtorA.entry] := by
  show emptyEnvA.members 0 = none ∧ (extendEnvA emptyEnvA 0 (pinFamFA 0)).members 1 = none
  refine ⟨rfl, ?_⟩
  rw [members_extendEnvA_ne emptyEnvA 0 (pinFamFA 0) Nat.one_ne_zero]
  rfl

theorem viewTy_idxGroupClosed :
    EnvClosedA (groupEnvA emptyEnvA 0 (pinFamFA 0) [viewTy_idxGroupCtorA.entry]) := by
  intro r m hm
  have hm : (extendEnvA (extendEnvA emptyEnvA 0 (pinFamFA 0)) 1 viewTy_idxCtorA).members r =
      some m := by
    simpa [groupEnvA, GroupCtorA.entry, viewTy_idxGroupCtorA] using hm
  by_cases h1 : r = 1
  · subst h1
    rw [members_extendEnvA_self] at hm
    cases hm
    exact ⟨viewTy_idxGroupCtorA.hclT, fun _ hb => Option.noConfusion hb⟩
  · rw [members_extendEnvA_ne _ 1 viewTy_idxCtorA h1] at hm
    by_cases h0 : r = 0
    · subst h0
      rw [members_extendEnvA_self] at hm
      cases hm
      exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
    · rw [members_extendEnvA_ne emptyEnvA 0 (pinFamFA 0) h0, emptyEnvA] at hm
      exact Option.noConfusion hm

theorem viewTy_natGroupClosed (I : IotaIfaceA) :
    EnvClosedA (groupEnvA emptyEnvA 10 pinNatFamA ((pinNatCs I).map GroupCtorA.entry)) := by
  rw [pinNatGroupEnv_eq]
  intro r m hm
  by_cases h12 : r = 12
  · subst h12
    rw [pinNatGroupEnv_succ] at hm
    cases hm
    exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  by_cases h11 : r = 11
  · subst h11
    rw [pinNatGroupEnv_zero] at hm
    cases hm
    exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  by_cases h10 : r = 10
  · subst h10
    rw [pinNatGroupEnv_fam] at hm
    cases hm
    exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  · have hnone : pinNatGroupEnvA.members r = none := by
      rw [pinNatGroupEnvA, members_extendEnvA_ne _ 12 pinSuccA h12,
        members_extendEnvA_ne _ 11 pinZeroA h11, pinNatFamEnvA,
        members_extendEnvA_ne emptyEnvA 10 pinNatFamA h10]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

private theorem viewTy_natRecDer (elim : RecElimA) :
    ∃ w, Nonempty (HasTyA
      (groupEnvA emptyEnvA 10 pinNatFamA ((pinNatCs noIotaA).map GroupCtorA.entry))
      noIotaA (pinNatFamA.arity + elim.extra) []
      (groupRecTypeA pinNatFamViewA (pinNatCs noIotaA) elim) (.sort w)) :=
  groupRecTypeA_hasTy_der (cs := pinNatCs noIotaA) (elim := elim)
    (viewTy_natFamTy emptyEnvA 0 []) (pinNatGroup_fresh noIotaA)
    emptyEnvA_closed (viewTy_natGroupClosed noIotaA) (fun _ _ h => Option.noConfusion h)
    (fun _ _ h => Option.noConfusion h) noIotaA_lift noIotaA_subst
    (noIotaA_recHead emptyEnvA)
    (noIotaA_recHead (groupEnvA emptyEnvA 10 pinNatFamA
      ((pinNatCs noIotaA).map GroupCtorA.entry)))
    (emptyEnvA_sem noIotaA 0 (fun _ => 1)) posValA_one

theorem groupRecTypeA_nat_any_tooth :
    ∃ w, Nonempty (HasTyA
      (groupEnvA emptyEnvA 10 pinNatFamA ((pinNatCs noIotaA).map GroupCtorA.entry))
      noIotaA (pinNatFamA.arity + RecElimA.anySort.extra) []
      (pinNatGroupRecA noIotaA).member.mtypeA (.sort w)) := by
  obtain ⟨w, ⟨d⟩⟩ := viewTy_natRecDer .anySort
  exact ⟨w, ⟨(pinNatGroupRec_stored noIotaA).symm ▸ d⟩⟩

/-- no stored `.propOnly` member exists (`pinNatGroupRecA` is `.anySort` only), so the
    conclusion is the built type itself. -/
theorem groupRecTypeA_nat_prop_tooth :
    ∃ w, Nonempty (HasTyA
      (groupEnvA emptyEnvA 10 pinNatFamA ((pinNatCs noIotaA).map GroupCtorA.entry))
      noIotaA (pinNatFamA.arity + RecElimA.propOnly.extra) []
      (groupRecTypeA pinNatFamViewA (pinNatCs noIotaA) .propOnly) (.sort w)) := by
  exact viewTy_natRecDer .propOnly

private theorem viewTy_idxRecDer (elim : RecElimA) :
    ∃ w, Nonempty (HasTyA
      (groupEnvA emptyEnvA 0 (pinFamFA 0) [viewTy_idxGroupCtorA.entry])
      noIotaA ((pinFamFA 0).arity + elim.extra) []
      (groupRecTypeA pinFamF0ViewA [viewTy_idxGroupCtorA] elim) (.sort w)) :=
  groupRecTypeA_hasTy_der (cs := [viewTy_idxGroupCtorA]) (elim := elim)
    (pinFamFTypeTy 0 emptyEnvA 0 []) viewTy_idxGroup_fresh
    emptyEnvA_closed viewTy_idxGroupClosed (fun _ _ h => Option.noConfusion h)
    (fun _ _ h => Option.noConfusion h) noIotaA_lift noIotaA_subst
    (noIotaA_recHead emptyEnvA)
    (noIotaA_recHead (groupEnvA emptyEnvA 0 (pinFamFA 0) [viewTy_idxGroupCtorA.entry]))
    (emptyEnvA_sem noIotaA 0 (fun _ => 1)) posValA_one

theorem groupRecTypeA_idx_any_tooth :
    ∃ w, Nonempty (HasTyA
      (groupEnvA emptyEnvA 0 (pinFamFA 0) [viewTy_idxGroupCtorA.entry])
      noIotaA ((pinFamFA 0).arity + RecElimA.anySort.extra) []
      (groupRecTypeA pinFamF0ViewA [viewTy_idxGroupCtorA] .anySort) (.sort w)) := by
  exact viewTy_idxRecDer .anySort

theorem groupRecTypeA_idx_prop_tooth :
    ∃ w, Nonempty (HasTyA
      (groupEnvA emptyEnvA 0 (pinFamFA 0) [viewTy_idxGroupCtorA.entry])
      noIotaA ((pinFamFA 0).arity + RecElimA.propOnly.extra) []
      (groupRecTypeA pinFamF0ViewA [viewTy_idxGroupCtorA] .propOnly) (.sort w)) := by
  exact viewTy_idxRecDer .propOnly

#print axioms ctorViewA_hasTy
#print axioms ctorViewA_box_tooth
#print axioms ctorViewA_succ_tooth
#print axioms ctorViewA_idx_tooth
#print axioms groupRecTypeA_hasTy
#print axioms groupRecTypeA_nat_any_tooth
#print axioms groupRecTypeA_nat_prop_tooth
#print axioms groupRecTypeA_idx_any_tooth
#print axioms groupRecTypeA_idx_prop_tooth
#print axioms viewTy_eta_major
#print axioms viewTy_plainExt
#print axioms viewTy_frecIH

end Rcic.Declarative.Ann
