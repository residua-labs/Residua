import rcic.RcicF3Core

/-!
# F3 S3: soundness of R-CIC typing and conversion in the set model

`sound_ty` / `sound_conv`, by mutual induction on `HasTyT` / `ConvT`: in any
interpretation whose universe stages satisfy `Good M N Lvl`, whose constants
satisfy `EnvSound` (membership of constants, δ and ι), at any level
valuation `σ` and any environment fitting the context, a typed term's
denotation is an element of its type's denotation, and convertible terms
denote `≈`-equal values.

The level bound is a property of the derivation (`LOKt` / `LOKc`): every
`sort`, `sorts` and `pi` level evaluates to at most `N` (`sort` and `sorts`
need one level of headroom), and every level instance of a constant `r`
evaluates to at most `K r`. The per-constant instance bound lets an
environment interpret each member only at the instances its own levels can
afford (a member may use an earlier one at a raised level). Unique typing and
regularity are not used: Prop-ness is decided semantically and element sets
are normalized to be dichotomous (`Ed`). closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

-- the level bound `LevelsOK` / `LOKt` / `LOKc` is defined in `RcicF3Defs`

section Hereditary

variable {E : ResolvedEnv} {n : Nat} (M : Interp.{T}) (σ : Nat → Nat)

/-- The root claim of a typing derivation. -/
def RootT {Γ : LCtx} {e A : Expr Nat} (_ : HasTyT E n Γ e A) : Prop :=
  ∀ ρ, Fits M σ Γ ρ → den M σ ρ e ∈ Ed M (den M σ ρ A)

/-- The root claim of a conversion derivation. -/
def RootC {Γ : LCtx} {a b A : Expr Nat} (_ : ConvT E n Γ a b A) : Prop :=
  ∀ ρ, Fits M σ Γ ρ → Equiv (den M σ ρ a) (den M σ ρ b) ∧ den M σ ρ a ∈ Ed M (den M σ ρ A)

mutual
/-- Hereditary soundness: the root claim holds at every node of the derivation. -/
def HSoundT : {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → Prop
  | _, _, _, h@(.sort _ _) => RootT M σ h
  | _, _, _, h@(.bvar _ _ _ _) => RootT M σ h
  | _, _, _, h@(.const _ _ _ _ _ _ _) => RootT M σ h
  | _, _, _, h@(.pi _ _ _ _ _ hA hB) => RootT M σ h ∧ HSoundT hA ∧ HSoundT hB
  | _, _, _, h@(.lam _ _ _ _ _ hA hb) => RootT M σ h ∧ HSoundT hA ∧ HSoundT hb
  | _, _, _, h@(.app _ _ _ _ _ hf ha) => RootT M σ h ∧ HSoundT hf ∧ HSoundT ha
  | _, _, _, h@(.letE _ _ _ _ _ _ hA hv hb) => RootT M σ h ∧ HSoundT hA ∧ HSoundT hv ∧ HSoundT hb
  | _, _, _, h@(.lit _ _ _ hexp) => RootT M σ h ∧ HSoundT hexp
  | _, _, _, h@(.conv _ _ _ _ _ h1 hc) => RootT M σ h ∧ HSoundT h1 ∧ HSoundC hc

/-- Hereditary soundness of a conversion derivation. -/
def HSoundC : {Γ : LCtx} → {a b A : Expr Nat} → ConvT E n Γ a b A → Prop
  | _, _, _, _, h@(.refl _ _ _ h1) => RootC M σ h ∧ HSoundT h1
  | _, _, _, _, h@(.symm _ _ _ _ h1) => RootC M σ h ∧ HSoundC h1
  | _, _, _, _, h@(.trans _ _ _ _ _ h1 h2) => RootC M σ h ∧ HSoundC h1 ∧ HSoundC h2
  | _, _, _, _, h@(.beta _ _ _ _ _ _ hA hb ha) => RootC M σ h ∧ HSoundT hA ∧ HSoundT hb ∧ HSoundT ha
  | _, _, _, _, h@(.zeta _ _ _ _ _ _ hA hv hb) => RootC M σ h ∧ HSoundT hA ∧ HSoundT hv ∧ HSoundT hb
  | _, _, _, _, h@(.zetaLocal _ _ _ _ _ _ hv) => RootC M σ h ∧ HSoundT hv
  | _, _, _, _, h@(.delta _ _ _ _ _ _ _ _ _ _ hb) => RootC M σ h ∧ HSoundT hb
  | _, _, _, _, h@(.iota _ _ _ _ _ hl hr) => RootC M σ h ∧ HSoundT hl ∧ HSoundT hr
  | _, _, _, _, h@(.lit _ _ _ _ _ hexp) => RootC M σ h ∧ HSoundT hexp
  | _, _, _, _, h@(.app _ _ _ _ _ _ _ h1 h2) => RootC M σ h ∧ HSoundC h1 ∧ HSoundC h2
  | _, _, _, _, h@(.lam _ _ _ _ _ _ _ hA hb) => RootC M σ h ∧ HSoundC hA ∧ HSoundC hb
  | _, _, _, _, h@(.pi _ _ _ _ _ _ _ hA hB) => RootC M σ h ∧ HSoundC hA ∧ HSoundC hB
  | _, _, _, _, h@(.letE _ _ _ _ _ _ _ _ _ hA hv hb) => RootC M σ h ∧ HSoundC hA ∧ HSoundC hv ∧ HSoundC hb
  | _, _, _, _, h@(.sorts _ _ _ _) => RootC M σ h
  | _, _, _, _, h@(.consts _ _ _ _ _ _ _ _ _ _) => RootC M σ h
  | _, _, _, _, h@(.eta _ _ _ _ h1) => RootC M σ h ∧ HSoundT h1
  | _, _, _, _, h@(.irr _ _ _ _ hP hp hq) => RootC M σ h ∧ HSoundT hP ∧ HSoundT hp ∧ HSoundT hq
  | _, _, _, _, h@(.tyConv _ _ _ _ _ _ h1 hA) => RootC M σ h ∧ HSoundC h1 ∧ HSoundC hA
end

end Hereditary

theorem HSoundT.root {E : ResolvedEnv} {n : Nat} {M : Interp.{T}} {σ : Nat → Nat} {Γ : LCtx}
    {e A : Expr Nat} {h : HasTyT E n Γ e A} (hs : HSoundT M σ h) : RootT M σ h := by
  cases h <;> first | exact hs | exact hs.1

theorem HSoundC.root {E : ResolvedEnv} {n : Nat} {M : Interp.{T}} {σ : Nat → Nat} {Γ : LCtx}
    {a b A : Expr Nat} {h : ConvT E n Γ a b A} (hs : HSoundC M σ h) : RootC M σ h := by
  cases h <;> first | exact hs | exact hs.1

/-- What the core proof needs from the interpretation of the environment's
constants: their membership in their types, δ for transparent definitions,
and ι (which may read the hereditary soundness of both sides' derivations,
for the memberships of the redex's arguments, and the left-hand side's level
bound, at a level `N` where the interpretation is `Good`). -/
structure EnvSound (M : Interp.{T}) (σ : Nat → Nat) (K : Nat → Nat) (E : ResolvedEnv) (n : Nat) : Prop where
  const : ∀ (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember) (ρ : Nat → PSet.{T}),
    E.members r = some m → ls.length = m.arity → LevelsOK σ (K r) ls → Fits M σ Γ ρ →
    M.μ r (ls.map (evalTotal σ)) ∈ Ed M (den M σ ρ (instantiateLevels ls m.mtype))
  delta : ∀ (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember) (b : Expr Nat)
    (ρ : Nat → PSet.{T}), E.members r = some m → m.body = some b → transparent m.mclass = true →
    ls.length = m.arity → LevelsOK σ (K r) ls → Fits M σ Γ ρ →
    Equiv (M.μ r (ls.map (evalTotal σ))) (den M σ ρ (instantiateLevels ls b))
  iota : ∀ (Γ : LCtx) (lhs rhs T : Expr Nat) (ρ : Nat → PSet.{T}), DerivedIota E lhs rhs →
    (hl : HasTyT E n Γ lhs T) → (hr : HasTyT E n Γ rhs T) → HSoundT M σ hl → HSoundT M σ hr →
    (∃ (N : Nat) (Lv : Nat → PSet.{T} → Prop), Good M N Lv ∧ LOKt σ N K hl) → Fits M σ Γ ρ →
    den M σ ρ lhs ∈ Ed M (den M σ ρ T) → den M σ ρ rhs ∈ Ed M (den M σ ρ T) →
    Equiv (den M σ ρ lhs) (den M σ ρ rhs)

theorem insρ_zero (a : PSet.{T}) (ρ : Nat → PSet.{T}) : insρ 0 a ρ = vcons a ρ := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      show (if i + 1 = 0 then a else if 0 < i + 1 then ρ (i + 1 - 1) else ρ (i + 1)) = ρ i
      rw [if_neg (Nat.succ_ne_zero i), if_pos (Nat.succ_pos i)]
      rfl

theorem den_inst0 (M : Interp.{T}) (σ : Nat → Nat) (ρ : Nat → PSet.{T}) (a B : Expr Nat) :
    den M σ ρ (instantiate0 a B) = den M σ (vcons (den M σ ρ a) ρ) B := by
  show den M σ ρ (instantiate 0 a B) = _
  rw [den_instantiate, insρ_zero]

theorem shiftρ_one_vcons (x : PSet.{T}) (ρ : Nat → PSet.{T}) : shiftρ 1 (vcons x ρ) = ρ := rfl

theorem tyv_congr' {S S' : PSet.{T}} (h : Equiv S S') : Equiv S S' := h

theorem den_resp (M : Interp.{T}) (σ : Nat → Nat) (ρ : Nat → PSet.{T}) (B : Expr Nat) :
    ∀ x x', Equiv x x' → Equiv (den M σ (vcons x ρ) B) (den M σ (vcons x' ρ) B) :=
  fun _ _ h => den_congr M σ B (vcons_congr h (fun _ => Equiv.rfl))

section Soundness

variable {M : Interp.{T}} {N : Nat} {Lvl : Nat → PSet.{T} → Prop} (hG : Good M N Lvl)
  {σ : Nat → Nat} {K : Nat → Nat} {E : ResolvedEnv} {n : Nat} (hE : EnvSound M σ K E n)

theorem fits_cons_assumption {Γ : LCtx} {A : Expr Nat} {ρ : Nat → PSet.{T}} {x : PSet.{T}}
    (hf : Fits M σ Γ ρ) (hx : x ∈ Ed M (den M σ ρ A)) : Fits M σ (.assumption A :: Γ) (vcons x ρ) :=
  ⟨hf, hx⟩

theorem fits_cons_let {Γ : LCtx} {A v : Expr Nat} {ρ : Nat → PSet.{T}}
    (hf : Fits M σ Γ ρ) (hv : den M σ ρ v ∈ Ed M (den M σ ρ A)) :
    Fits M σ (.letBinding A v :: Γ) (vcons (den M σ ρ v) ρ) :=
  ⟨hf, hv, Equiv.rfl⟩

include hG in
theorem mem_sort_U {ρ : Nat → PSet.{T}} {u : Level} (hu : evalTotal σ u ≤ N) {x : PSet.{T}}
    (hx : x ∈ Ed M (den M σ ρ (.sort u))) : x ∈ M.U (evalTotal σ u) :=
  mem_congr_right (ed_sortU hG hu) hx

include hG in
theorem sort_U_mem {ρ : Nat → PSet.{T}} {u : Level} (hu : evalTotal σ u ≤ N) {x : PSet.{T}}
    (hx : x ∈ M.U (evalTotal σ u)) : x ∈ Ed M (den M σ ρ (.sort u)) :=
  mem_congr_right (ed_sortU hG hu).symm hx

include hG in
theorem pi_sound {A B : Expr Nat} {u v : Level} {ρ : Nat → PSet.{T}}
    (hu : evalTotal σ u ≤ N) (hv : evalTotal σ v ≤ N)
    (hA : den M σ ρ A ∈ Ed M (den M σ ρ (.sort u)))
    (hB : ∀ x, x ∈ Ed M (den M σ ρ A) → den M σ (vcons x ρ) B ∈ Ed M (den M σ (vcons x ρ) (.sort v))) :
    den M σ ρ (.pi A B) ∈ Ed M (den M σ ρ (.sort (.imax u v))) := by
  have hm : evalTotal σ (.imax u v) ≤ N := imax_le hu hv
  refine sort_U_mem hG hm ?_
  exact pi_mem hG hu hv (den_resp M σ ρ B) (mem_sort_U hG hu hA)
    (fun x hx => mem_sort_U hG (ρ := vcons x ρ) hv (hB x hx))


include hG hE in
mutual
/-- Hereditary soundness of typing: every node of a bounded derivation is sound. -/
theorem hsound_ty : {Γ : LCtx} → {e A : Expr Nat} → (h : HasTyT E n Γ e A) → LOKt σ N K h →
    HSoundT M σ h
  | _, _, _, .sort _ l, hl => fun _ _ => sort_mem hG hl
  | Γ, _, _, .bvar _ i A hi, _ => fun ρ hf => fits_lookupType M σ Γ ρ hf i A hi
  | Γ, _, _, .const _ r ls m hres hlen _, hl => fun ρ hf => hE.const Γ r ls m ρ hres hlen hl hf
  | Γ, _, _, .pi _ A u B v hA hB, lk => by
      obtain ⟨hu, hv, lA, lB⟩ := lk
      have iA := hsound_ty hA lA
      have iB := hsound_ty hB lB
      exact ⟨fun ρ hf => pi_sound hG hu hv (iA.root ρ hf)
          (fun x hx => iB.root (vcons x ρ) (fits_cons_assumption hf hx)), iA, iB⟩
  | Γ, _, _, .lam _ A u body B hA hbody, lk => by
      obtain ⟨lA, lb⟩ := lk
      have iA := hsound_ty hA lA
      have ib := hsound_ty hbody lb
      exact ⟨fun ρ hf => lam_mem M (den_resp M σ ρ body) (den_resp M σ ρ B)
          (fun x hx => ib.root (vcons x ρ) (fits_cons_assumption hf hx)), iA, ib⟩
  | Γ, _, _, .app _ f a A B hf' ha, lk => by
      obtain ⟨lf, la⟩ := lk
      have i1 := hsound_ty hf' lf
      have i2 := hsound_ty ha la
      refine ⟨fun ρ hf => ?_, i1, i2⟩
      show den M σ ρ (.app f a) ∈ Ed M (den M σ ρ (instantiate0 a B))
      rw [den_inst0]
      exact app_mem M (den_resp M σ ρ B) (i1.root ρ hf) (i2.root ρ hf)
  | Γ, _, _, .letE _ A u v B body hA hv hb, lk => by
      obtain ⟨lA, lv, lb⟩ := lk
      have iA := hsound_ty hA lA
      have iv := hsound_ty hv lv
      have ib := hsound_ty hb lb
      refine ⟨fun ρ hf => ?_, iA, iv, ib⟩
      show den M σ ρ (.letE A v body) ∈ Ed M (den M σ ρ (instantiate0 v B))
      rw [den_inst0]
      exact ib.root _ (fits_cons_let hf (iv.root ρ hf))
  | Γ, _, _, .lit _ t T hexp, l => by
      have ie := hsound_ty hexp l
      refine ⟨fun ρ hf => ?_, ie⟩
      have := ie.root ρ hf
      rw [den_natExpand] at this
      exact this
  | Γ, _, _, .conv _ e A B u h hc, lk => by
      obtain ⟨l1, l2⟩ := lk
      have i1 := hsound_ty h l1
      have ic := hsound_conv hc l2
      exact ⟨fun ρ hf => mem_congr_right (ed_congr M (ic.root ρ hf).1) (i1.root ρ hf), i1, ic⟩
  termination_by _ _ _ h => sizeOf h

/-- Hereditary soundness of conversion. -/
theorem hsound_conv : {Γ : LCtx} → {a b A : Expr Nat} → (h : ConvT E n Γ a b A) → LOKc σ N K h →
    HSoundC M σ h
  | _, _, _, _, .refl _ _ _ h, l => by
      have i := hsound_ty h l
      exact ⟨fun ρ hf => ⟨Equiv.rfl, i.root ρ hf⟩, i⟩
  | _, _, _, _, .symm _ _ _ _ h, l => by
      have i := hsound_conv h l
      exact ⟨fun ρ hf => let ⟨e, m⟩ := i.root ρ hf; ⟨e.symm, mem_congr_left e m⟩, i⟩
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, lk => by
      obtain ⟨l1, l2⟩ := lk
      have i1 := hsound_conv h1 l1
      have i2 := hsound_conv h2 l2
      exact ⟨fun ρ hf => let ⟨e1, m1⟩ := i1.root ρ hf; let ⟨e2, _⟩ := i2.root ρ hf; ⟨e1.trans e2, m1⟩,
        i1, i2⟩
  | _, _, _, _, .beta _ A body arg B u hA hbody harg, lk => by
      obtain ⟨lA, lb, la⟩ := lk
      have iA := hsound_ty hA lA
      have ib := hsound_ty hbody lb
      have ia := hsound_ty harg la
      refine ⟨fun ρ hf => ?_, iA, ib, ia⟩
      have ha := ia.root ρ hf
      have hb := ib.root (vcons (den M σ ρ arg) ρ) (fits_cons_assumption hf ha)
      have e : Equiv (den M σ ρ (.app (.lam A body) arg)) (den M σ ρ (instantiate0 arg body)) := by
        rw [den_inst0]
        exact beta_val M (den_resp M σ ρ body) ha
      refine ⟨e, mem_congr_left e.symm ?_⟩
      rw [den_inst0, den_inst0]
      exact hb
  | _, _, _, _, .zeta _ A v body B u hA hv hb, lk => by
      obtain ⟨lA, lv, lb⟩ := lk
      have iA := hsound_ty hA lA
      have iv := hsound_ty hv lv
      have ib := hsound_ty hb lb
      refine ⟨fun ρ hf => ?_, iA, iv, ib⟩
      have hbm := ib.root _ (fits_cons_let hf (iv.root ρ hf))
      refine ⟨?_, ?_⟩
      · rw [den_inst0]; exact Equiv.rfl
      · rw [den_inst0]; exact hbm
  | Γ, _, _, _, .zetaLocal _ i A v hval hty hv, l => by
      have iv := hsound_ty hv l
      exact ⟨fun ρ hf => ⟨fits_lookupValue M σ Γ ρ hf i v hval, fits_lookupType M σ Γ ρ hf i A hty⟩, iv⟩
  | Γ, _, _, _, .delta _ r ls m b hres hbody htr hlen _ hb, lk => by
      obtain ⟨hl, lb⟩ := lk
      have ib := hsound_ty hb lb
      exact ⟨fun ρ hf => let e := hE.delta Γ r ls m b ρ hres hbody htr hlen hl hf
        ⟨e, mem_congr_left e.symm (ib.root ρ hf)⟩, ib⟩
  | Γ, _, _, _, .iota _ lhs rhs T h hl hr, lk => by
      obtain ⟨ll, lr⟩ := lk
      have il := hsound_ty hl ll
      have ir := hsound_ty hr lr
      exact ⟨fun ρ hf => let ml := il.root ρ hf
        ⟨hE.iota Γ lhs rhs T ρ h hl hr il ir ⟨_, _, hG, ll⟩ hf ml (ir.root ρ hf), ml⟩, il, ir⟩
  | _, _, _, _, .lit _ t exp T h hexp, l => by
      have ie := hsound_ty hexp l
      refine ⟨fun ρ hf => ?_, ie⟩
      have m := ie.root ρ hf
      cases h
      refine ⟨?_, ?_⟩
      · show Equiv (denLit M t) _
        rw [den_natExpand]
        exact Equiv.rfl
      · show denLit M t ∈ _
        rw [← den_natExpand M σ ρ]
        exact m
  | _, _, _, _, .app _ f g a b A B h1 h2, lk => by
      obtain ⟨l1, l2⟩ := lk
      have i1 := hsound_conv h1 l1
      have i2 := hsound_conv h2 l2
      refine ⟨fun ρ hf => ?_, i1, i2⟩
      obtain ⟨e1, m1⟩ := i1.root ρ hf
      obtain ⟨e2, m2⟩ := i2.root ρ hf
      refine ⟨fapp_congr e1 e2, ?_⟩
      show den M σ ρ (.app f a) ∈ Ed M (den M σ ρ (instantiate0 a B))
      rw [den_inst0]
      exact app_mem M (den_resp M σ ρ B) m1 m2
  | _, _, _, _, .lam _ A A' b b' B u hA hb, lk => by
      obtain ⟨lA, lb⟩ := lk
      have iA := hsound_conv hA lA
      have ib := hsound_conv hb lb
      refine ⟨fun ρ hf => ?_, iA, ib⟩
      obtain ⟨eA, _⟩ := iA.root ρ hf
      have hbx : ∀ x, x ∈ Ed M (den M σ ρ A) →
          Equiv (den M σ (vcons x ρ) b) (den M σ (vcons x ρ) b') ∧
            den M σ (vcons x ρ) b ∈ Ed M (den M σ (vcons x ρ) B) :=
        fun x hx => ib.root (vcons x ρ) (fits_cons_assumption hf hx)
      exact ⟨lamVal_congr_on M eA (den_resp M σ ρ b) (fun x hx => (hbx x hx).1),
        lam_mem M (den_resp M σ ρ b) (den_resp M σ ρ B) (fun x hx => (hbx x hx).2)⟩
  | _, _, _, _, .pi _ A A' B B' u v hA hB, lk => by
      obtain ⟨hu, hv, lA, lB⟩ := lk
      have iA := hsound_conv hA lA
      have iB := hsound_conv hB lB
      refine ⟨fun ρ hf => ?_, iA, iB⟩
      obtain ⟨eA, mA⟩ := iA.root ρ hf
      have hBx : ∀ x, x ∈ Ed M (den M σ ρ A) →
          Equiv (den M σ (vcons x ρ) B) (den M σ (vcons x ρ) B') ∧
            den M σ (vcons x ρ) B ∈ Ed M (den M σ (vcons x ρ) (.sort v)) :=
        fun x hx => iB.root (vcons x ρ) (fits_cons_assumption hf hx)
      exact ⟨tyv_congr' (piVal_congr_on M eA (den_resp M σ ρ B) (den_resp M σ ρ B')
          (fun x hx => (hBx x hx).1)),
        pi_sound hG hu hv mA (fun x hx => (hBx x hx).2)⟩
  | _, _, _, _, .letE _ A A' v v' b b' B u hA hv hb, lk => by
      obtain ⟨lA, lv, lb⟩ := lk
      have iA := hsound_conv hA lA
      have iv := hsound_conv hv lv
      have ib := hsound_conv hb lb
      refine ⟨fun ρ hf => ?_, iA, iv, ib⟩
      obtain ⟨ev, mv⟩ := iv.root ρ hf
      obtain ⟨eb, mb⟩ := ib.root _ (fits_cons_let hf mv)
      refine ⟨eb.trans (den_congr M σ b' (vcons_congr ev (fun _ => Equiv.rfl))), ?_⟩
      show den M σ ρ (.letE A v b) ∈ Ed M (den M σ ρ (instantiate0 v B))
      rw [den_inst0]
      exact mb
  | _, _, _, _, .sorts _ l₁ l₂ h, hl => by
      refine fun ρ _ => ⟨?_, sort_mem hG hl⟩
      have e : evalTotal σ l₁ = evalTotal σ l₂ := evalTotal_eq_of_eqN σ h
      show Equiv (tyv (M.U (evalTotal σ l₁))) (tyv (M.U (evalTotal σ l₂)))
      rw [e]
      exact Equiv.rfl
  | Γ, _, _, _, .consts _ r ls ls' m hres hlen _ _ h, lk => by
      obtain ⟨hl, _⟩ := lk
      refine fun ρ hf => ⟨?_, hE.const Γ r ls m ρ hres hlen hl hf⟩
      show Equiv (M.μ r (ls.map (evalTotal σ))) (M.μ r (ls'.map (evalTotal σ)))
      rw [map_evalTotal_of_eqNList σ h]
      exact Equiv.rfl
  | _, _, _, _, .eta _ f A B h, l => by
      have i := hsound_ty h l
      refine ⟨fun ρ hf => ?_, i⟩
      have mf := i.root ρ hf
      have hbody : (fun x => den M σ (vcons x ρ) (.app (Rcic.Declarative.lift 0 1 f) (.bvar 0))) =
          (fun x => fapp (den M σ ρ f) x) := by
        funext x
        show fapp (den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 f)) x = _
        rw [den_lift_shift]
        rfl
      have e : Equiv (den M σ ρ (.lam A (.app (Rcic.Declarative.lift 0 1 f) (.bvar 0)))) (den M σ ρ f) := by
        show Equiv (lamVal M (den M σ ρ A) _) _
        rw [hbody]
        exact eta_val M (den_resp M σ ρ B) mf
      exact ⟨e, mem_congr_left e.symm mf⟩
  | _, _, _, _, .irr _ P p q hP hp hq, lk => by
      obtain ⟨lP, lp, lq⟩ := lk
      have iP := hsound_ty hP lP
      have ip := hsound_ty hp lp
      have iq := hsound_ty hq lq
      refine ⟨fun ρ hf => ?_, iP, ip, iq⟩
      have hPU := mem_sort_U hG (u := .zero) (Nat.zero_le N) (iP.root ρ hf)
      obtain ⟨S, hS, hPe⟩ := (hG.U_iff (Nat.zero_le N) _).mp hPU
      have eP : Equiv (Ed M (den M σ ρ P)) S := ed_of_lvl hG hS hPe
      have mp := ip.root ρ hf
      have mq := iq.root ρ hf
      have p0 := hG.lvl0.mp hS _ (mem_congr_right eP mp)
      have q0 := hG.lvl0.mp hS _ (mem_congr_right eP mq)
      exact ⟨p0.trans q0.symm, mp⟩
  | _, _, _, _, .tyConv _ a b A A' u h hA, lk => by
      obtain ⟨l1, l2⟩ := lk
      have i1 := hsound_conv h l1
      have i2 := hsound_conv hA l2
      exact ⟨fun ρ hf => let ⟨e, m⟩ := i1.root ρ hf
        ⟨e, mem_congr_right (ed_congr M (i2.root ρ hf).1) m⟩, i1, i2⟩
  termination_by _ _ _ _ h => sizeOf h
end

include hG hE in
/-- Soundness of typing: a typed term denotes an element of its type, at every
fitting environment. -/
theorem sound_ty {Γ : LCtx} {e A : Expr Nat} (h : HasTyT E n Γ e A) (hl : LOKt σ N K h) :
    ∀ ρ, Fits M σ Γ ρ → den M σ ρ e ∈ Ed M (den M σ ρ A) :=
  (hsound_ty hG hE h hl).root

include hG hE in
/-- Soundness of conversion: convertible terms denote `≈`-equal values. -/
theorem sound_conv {Γ : LCtx} {a b A : Expr Nat} (h : ConvT E n Γ a b A) (hl : LOKc σ N K h) :
    ∀ ρ, Fits M σ Γ ρ → Equiv (den M σ ρ a) (den M σ ρ b) ∧ den M σ ρ a ∈ Ed M (den M σ ρ A) := by
  exact (hsound_conv hG hE h hl).root


end Soundness

end PSet

end Rcic.F3
