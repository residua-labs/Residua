/-
S1 — the postponement route class, sealed-refuted at the Loop fixture.

`research/rcic/irr-postponement/S0_RECORD.md` (PR #6363, S0) measured that the
cyclic conversion `X := rec.{1} M m t ≡ X → X` at `eraseEnv pinLoopEnvA` is
derivable in `ConvT` — `irr` on `Loop`, application congruence at the recursor
major, `tyConv` (`M t ≡ sort 0` by β), ι on the constructor-shaped major, β —
while `ParRed`, which has no `irr` arm, cannot join `X` and `X → X`: both are
`ParRed`-normal and their reduct classes are disjoint. This file turns that
measurement into sealed theorems:

* `pinLoopConv_erased` — the cyclic `ConvT` at the erased environment,
  discharged from `pinLoopConv` through `convT_of_convA` and the
  `iotaErasesA_of_envWfA` correspondence (`EnvNoFunA`/`EnvNormEraseA`
  discharged for the pin env below).
* `parRed_pinLoop_spine` — TOTAL ParRed inversion on `const 62`-headed
  spines whose arguments are not constructor-headed spines: pointwise
  congruence or nothing (δ dead — the recursor member is opaque and
  `body = none`; ι dead — the major would have to be a constructor-headed
  spine, i.e. a `foldApps (const ..)`, which `hnf` excludes; β dead — the
  head is not a λ).
* `parRedStar_pinLoopX_class` / `parRedStar_pi_class` — the two reduct
  classes stay in their outer-constructor class.
* `parRedJoinable_pinLoop_false` — `¬ Joinable` against `ParRedStar`
  (cc's S1 ruling shape).
* `postponeJoinable_false_at_loop` — the pair: the cyclic `ConvT` exists
  AND the erased `ParRedStar` join does not. Postponement is not a
  factorization: the `irr` leaf is consumed by ι's syntactic major premise.

The F05b rows (`piRow`, `famAppRow`) are UNPROVED, not refuted — this file
seals only the refutation of the postponement lemma class. `W-F05b-PiRow`
stands.
-/

import rcic.RcicAnnRecPins
import rcic.RcicAnnErase
import rcic.RcicParRedCore
import rcic.RcicParRedIota
import rcic.RcicIota

namespace Rcic.Declarative.Ann

/-- The erased environment's recursor member, at ref 62. -/
theorem pinLoopEnvA_mem62 :
    (eraseEnv pinLoopEnvA).members 62 = some (eraseMember pinLoopRecMemberA) :=
  rfl

/-- `EnvNoFunA` for the pin env: the only constructor (`mk` at 61) has the
single field shape `.recursive 0` — direct, never function-recursive. -/
theorem pinLoopEnvA_noFun : EnvNoFunA pinLoopEnvA := by
  intro c cm f fm shapes hc hcm hfm hf hshapes s hs j h
  rcases pinLoop_mem hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases hcm
  · have hf60 : memberFamRefA pinLoopMkA = some 60 := rfl
    rw [hf60] at hfm
    cases hfm
    rcases pinLoop_mem hf with ⟨_, rfl⟩ | ⟨hbad, _⟩ | ⟨hbad, _⟩
    · have hshape_val : ctorShapesA 60 pinLoopFamA.nparamsA
          (pinLoopMkA.normA.getD pinLoopMkA.mtypeA) = some [.recursive 0] := by
        decide
      rw [hshape_val] at hshapes
      cases hshapes
      rcases List.mem_singleton.mp hs with rfl
      injection h with h0
      exact Nat.noConfusion h0
    · exact absurd hbad (by decide)
    · exact absurd hbad (by decide)
  · cases hcm

/-- `EnvNormEraseA` for the pin env: `mk`'s `normA` is its `mtypeA`
literally, so the erasure reads coincide. -/
theorem pinLoopEnvA_normErase : EnvNormEraseA pinLoopEnvA := by
  intro r m hm hmc T hT
  rcases pinLoop_mem hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases hmc
  · cases hT
    rfl
  · cases hmc

/-- The typed-landing ι correspondence for the pin env, discharged. -/
def pinLoopEnvA_iotaErases : IotaErasesA pinLoopEnvA :=
  iotaErasesA_of_envWfA pinLoop_wf pinLoopEnvA_noFun pinLoopEnvA_normErase

/-- The cyclic conversion in the TYPED judgment at the erased environment:
`rec.{1} M m t ≡ rec.{1} M m t → rec.{1} M m t` at `sort 0`. -/
theorem pinLoopConv_erased {n : Nat} :
    Nonempty (ConvT (eraseEnv pinLoopEnvA) n [.assumption (.const 60 [])]
      (erase pinLoopA) (erase pinLoopArrow) (.sort .zero)) :=
  convT_of_convA pinLoop_wf pinLoopEnvA_iotaErases
    (pinLoopConv (E := pinLoopEnvA) (I := iotaIfaceA pinLoopEnvA) (Γ := [])
      rfl rfl rfl ⟨by decide, by decide⟩)

/-- A `const`-headed spine is never an expression whose spine head is not a
constant: sort, lam, pi, letE, lit, bvar, and any `app` whose spine head is
lam/letE (the β/ζ redex shapes). -/
theorem foldApps_const_ne_of_spine {r : Nat} {ls : List Level} {xs : List (Expr Nat)}
    {e hd : Expr Nat} {tl : List (Expr Nat)}
    (he : appsSpine e = (hd, tl)) (hne : ∀ r0 ls0, hd ≠ .const r0 ls0) :
    e ≠ foldApps (.const r ls) xs := fun h => by
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const, he] at hs
  exact hne _ _ (congrArg Prod.fst hs)

theorem foldApps_app_ne_bvar (f a : Expr Nat) :
    (xs : List (Expr Nat)) → {i : Nat} → foldApps (.app f a) xs ≠ .bvar i
  | [], _, h => nomatch h
  | x :: xs, _, h => foldApps_app_ne_bvar (.app f a) x xs h

theorem foldApps_const_ne_bvar {r i : Nat} {ls : List Level} :
    (xs : List (Expr Nat)) → foldApps (.const r ls) xs ≠ .bvar i
  | [], h => nomatch h
  | x :: xs, h => foldApps_app_ne_bvar (.const r ls) x xs h

/-- TOTAL ParRed inversion on a `const 62`-headed spine at the erased pin
environment, for argument lists that contain no constructor-headed spine
(`hnf`). Every step is pointwise congruence: the δ arm dies on the
recursor's opacity, the ι arm dies on `hnf` (its major IS a
`foldApps (const ..)`), β and every other head dies on the const spine
head. -/
def parRed_pinLoop_spine {n : Nat} {Γ : LCtx} {ls : List Level} :
    {e t : Expr Nat} → ParRed (eraseEnv pinLoopEnvA) n Γ e t →
    (xs : List (Expr Nat)) → e = foldApps (.const 62 ls) xs →
    (∀ x, x ∈ xs → ∀ (r : Nat) (ls' : List Level) (ys : List (Expr Nat)),
      foldApps (.const r ls') ys ≠ x) →
    Σ' (ls' : List Level) (xs' : List (Expr Nat)),
      (t = foldApps (.const 62 ls') xs') ×'
      ParRedArgs (eraseEnv pinLoopEnvA) n Γ xs xs'
  | _, _, .refl _ _, xs, heq, _ => ⟨ls, xs, heq, parRedArgs_refl xs⟩
  | _, _, .sortEq _ _ _ _, _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .consts _ r0 ls0 ls' _, xs, heq, _ => by
      have hc : appsSpine (.const r0 ls0) = (.const r0 ls0, []) := rfl
      have hs := congrArg appsSpine heq
      rw [hc, appsSpine_foldApps_const] at hs
      have hfst : (Expr.const r0 ls0) = (Expr.const 62 ls) := congrArg Prod.fst hs
      have hsnd : ([] : List (Expr Nat)) = xs := congrArg Prod.snd hs
      injection hfst with hr0 _
      subst hr0
      subst xs
      exact ⟨ls', [], rfl, .nil _⟩
  | _, _, .bvarZeta _ _ _ _ _ _ _, _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .delta _ r0 ls0 m0 _ hres _ htr, _, heq, _ => by
      have hc : appsSpine (.const r0 ls0) = (.const r0 ls0, []) := rfl
      have hs := congrArg appsSpine heq
      rw [hc, appsSpine_foldApps_const] at hs
      have hfst : (Expr.const r0 ls0) = (Expr.const 62 ls) := congrArg Prod.fst hs
      injection hfst with hr0 _
      subst hr0
      rw [pinLoopEnvA_mem62] at hres
      cases hres
      have htr' : transparent (eraseMember pinLoopRecMemberA).mclass = false := rfl
      rw [htr'] at htr
      nomatch htr
  | _, _, .app _ f0 f0' a0 a0' hf ha, xs, heq, hnf => by
      have happ : appsSpine (.app f0 a0) =
          ((appsSpine f0).1, (appsSpine f0).2 ++ [a0]) := rfl
      have hs := congrArg appsSpine heq
      rw [happ, appsSpine_foldApps_const] at hs
      have hhead : (appsSpine f0).1 = .const 62 ls := congrArg Prod.fst hs
      have hargs : (appsSpine f0).2 ++ [a0] = xs := congrArg Prod.snd hs
      obtain ⟨ls', ys', hf'eq, hys⟩ :=
        parRed_pinLoop_spine hf ((appsSpine f0).2)
          (by rw [← hhead]; exact (foldApps_appsSpine f0).symm)
          (fun x hx r ls0 ys0 => hnf x (hargs ▸ List.mem_append.mpr (.inl hx)) r ls0 ys0)
      refine ⟨ls', ys' ++ [a0'], ?_, ?_⟩
      · rw [hf'eq]
        exact (foldApps_snoc _ _ _).symm
      · rw [← hargs]
        exact parRedArgs_snoc hys ha
  | _, _, .beta .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .lam .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .pi .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .letE .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .zeta .., _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))
  | _, _, .iotaSpine _ w2 lsR lsC _ _ pre _ fields _ _ _ _ _ _, xs, heq, hnf => by
      have hsrc : recCall (.const w2.recRef lsR) pre
          (foldApps (.const w2.ctorRef lsC) fields) =
          foldApps (.const w2.recRef lsR)
            (pre ++ [foldApps (.const w2.ctorRef lsC) fields]) := rfl
      have hs := congrArg appsSpine heq
      rw [hsrc, appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
      have hargs : pre ++ [foldApps (.const w2.ctorRef lsC) fields] = xs :=
        congrArg Prod.snd hs
      have hmem : foldApps (.const w2.ctorRef lsC) fields ∈ xs :=
        hargs ▸ List.mem_append.mpr (.inr (List.mem_singleton_self _))
      exact absurd rfl (hnf _ hmem _ _ _)
  | _, _, .lit _ _, _, heq, _ =>
      absurd heq (foldApps_const_ne_of_spine rfl (fun _ _ h => nomatch h))

/-- A λ is a head-normal form of one-step `ParRed`. -/
def parRed_lam_normal {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} :
    {e t : Expr Nat} → ParRed E n Γ e t → e = .lam A B →
    Σ' A' B', t = .lam A' B'
  | _, _, .refl _ _, heq => ⟨A, B, heq⟩
  | _, _, .lam _ _ _ _ _ _ _, _ => ⟨_, _, rfl⟩
  | _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, heq =>
      absurd heq (foldApps_const_ne_lam _)
  | _, _, .sortEq _ _ _ _, heq => nomatch heq
  | _, _, .consts _ _ _ _ _, heq => nomatch heq
  | _, _, .bvarZeta _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .delta .., heq => nomatch heq
  | _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .beta .., heq => nomatch heq
  | _, _, .pi .., heq => nomatch heq
  | _, _, .letE .., heq => nomatch heq
  | _, _, .zeta .., heq => nomatch heq
  | _, _, .lit _ _, heq => nomatch heq

/-- A Π is a head-normal form of one-step `ParRed`. -/
def parRed_pi_class {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} :
    {e t : Expr Nat} → ParRed E n Γ e t → e = .pi A B →
    Σ' A' B', t = .pi A' B'
  | _, _, .refl _ _, heq => ⟨A, B, heq⟩
  | _, _, .pi _ _ _ _ _ _ _, _ => ⟨_, _, rfl⟩
  | _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, heq =>
      absurd heq (foldApps_snoc_ne_pi _ _ _)
  | _, _, .sortEq _ _ _ _, heq => nomatch heq
  | _, _, .consts _ _ _ _ _, heq => nomatch heq
  | _, _, .bvarZeta _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .delta .., heq => nomatch heq
  | _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .beta .., heq => nomatch heq
  | _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .letE .., heq => nomatch heq
  | _, _, .zeta .., heq => nomatch heq
  | _, _, .lit _ _, heq => nomatch heq

/-- A free variable whose context slot is not a `letBinding` is a normal
form of one-step `ParRed` (the `bvarZeta` arm dies on the declaration
class). -/
def parRed_bvar_normal {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat}
    (hz : ∀ A v, Γ.get? i ≠ some (.letBinding A v)) :
    {e t : Expr Nat} → ParRed E n Γ e t → e = .bvar i → t = .bvar i
  | _, _, .refl _ _, heq => heq
  | _, _, .bvarZeta _ _ _ _ _ hg _, heq => by
      cases heq
      exact absurd hg (hz _ _)
  | _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, heq =>
      absurd heq (foldApps_snoc_ne_bvar _ _ _)
  | _, _, .sortEq _ _ _ _, heq => nomatch heq
  | _, _, .consts _ _ _ _ _, heq => nomatch heq
  | _, _, .delta .., heq => nomatch heq
  | _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .beta .., heq => nomatch heq
  | _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, .letE .., heq => nomatch heq
  | _, _, .zeta .., heq => nomatch heq
  | _, _, .lit _ _, heq => nomatch heq

/-- `bvar 0` in the Loop context is an assumption slot, never a
`letBinding`. -/
theorem pinLoopΓ_noLet (A v : Expr Nat) :
    ([.assumption (.const 60 [])] : LCtx).get? 0 ≠ some (.letBinding A v) :=
  fun h => LocalDecl.noConfusion (Option.some.inj h)

/-- Three-element pointwise inversion of `ParRedArgs`. -/
def parRedArgs_three {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b c : Expr Nat} {ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ [a, b, c] ys) :
    Σ' y1 y2 y3, (ys = [y1, y2, y3]) ×' ParRed E n Γ a y1 ×'
      ParRed E n Γ b y2 ×' ParRed E n Γ c y3 := by
  cases h with
  | cons h1 t1 =>
      cases t1 with
      | cons h2 t2 =>
          cases t2 with
          | cons h3 t3 =>
              cases t3
              exact ⟨_, _, _, rfl, h1, h2, h3⟩

/-- The Loop `X`-form's `hnf` side condition: λ-heads and `bvar` are never
constructor-headed spines. -/
theorem pinLoopX_hnf {A₁ B₁ A₂ B₂ : Expr Nat} :
    ∀ x ∈ [.lam A₁ B₁, .lam A₂ B₂, .bvar 0],
      ∀ (r : Nat) (ls' : List Level) (ys : List (Expr Nat)),
        foldApps (.const r ls') ys ≠ x := by
  intro x hx r ls' ys
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact foldApps_const_ne_lam ys
  · exact foldApps_const_ne_lam ys
  · exact foldApps_const_ne_bvar ys

/-- The `X`-class: every `ParRedStar` reduct of the recursor-application
shape `rec.{u} M m t` (`const 62` head, λ motive, λ minor, `bvar` major)
keeps the shape. Each step is congruence on the spine; the λ's stay λ, the
major stays `bvar`. -/
def parRedStar_pinLoopX_class {n : Nat} {Γ : LCtx} {c : Expr Nat}
    (hz : ∀ A v, Γ.get? 0 ≠ some (.letBinding A v))
    {ls : List Level} {A₁ B₁ A₂ B₂ : Expr Nat} :
    {a : Expr Nat} → ParRedStar (eraseEnv pinLoopEnvA) n Γ a c →
    a = .app (.app (.app (.const 62 ls) (.lam A₁ B₁)) (.lam A₂ B₂)) (.bvar 0) →
    Σ' (ls' : List Level) (A₁' B₁' A₂' B₂' : Expr Nat),
      c = .app (.app (.app (.const 62 ls') (.lam A₁' B₁')) (.lam A₂' B₂')) (.bvar 0)
  | _, .refl _ _, heq => ⟨ls, A₁, B₁, A₂, B₂, heq⟩
  | _, .tail h s, heq => by
      obtain ⟨ls', xs', hteq, hargs⟩ := parRed_pinLoop_spine h
        [.lam A₁ B₁, .lam A₂ B₂, .bvar 0] heq pinLoopX_hnf
      obtain ⟨y1, y2, y3, hxs, h1, h2, h3⟩ := parRedArgs_three hargs
      obtain ⟨A₁', B₁', hy1⟩ := parRed_lam_normal h1 rfl
      obtain ⟨A₂', B₂', hy2⟩ := parRed_lam_normal h2 rfl
      have hy3 : y3 = .bvar 0 := parRed_bvar_normal hz h3 rfl
      subst hxs
      subst hy1
      subst hy2
      subst hy3
      exact parRedStar_pinLoopX_class hz s hteq

/-- The Π-class: every `ParRedStar` reduct of a Π keeps the outer `pi`. -/
def parRedStar_pi_class {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B c : Expr Nat} :
    {a : Expr Nat} → ParRedStar E n Γ a c → a = .pi A B →
    Σ' A' B', c = .pi A' B'
  | _, .refl _ _, heq => ⟨A, B, heq⟩
  | _, .tail h s, heq => by
      obtain ⟨A1, B1, hy⟩ := parRed_pi_class h heq
      exact parRedStar_pi_class s hy

/-- Route-P1's joinability predicate: a common `ParRedStar` reduct. -/
def Joinable (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b : Expr Nat) : Prop :=
  ∃ c, Nonempty (ParRedStar E n Γ a c) ∧ Nonempty (ParRedStar E n Γ b c)

/-- THE REFUTATION, cc's S1 shape: `X` and `X → X` have no common
`ParRedStar` reduct at the erased Loop environment. The X-class is
application-shaped, the Π-class is Π-shaped, and the classes are disjoint
at every common reduct. -/
theorem parRedJoinable_pinLoop_false {n : Nat} :
    ¬ Joinable (eraseEnv pinLoopEnvA) n [.assumption (.const 60 [])]
      (erase pinLoopA) (erase pinLoopArrow) := by
  rintro ⟨c, ⟨hX⟩, ⟨hP⟩⟩
  obtain ⟨ls', A₁', B₁', A₂', B₂', hc⟩ :=
    parRedStar_pinLoopX_class pinLoopΓ_noLet hX rfl
  obtain ⟨A', B', hc'⟩ := parRedStar_pi_class hP rfl
  rw [hc] at hc'
  exact nomatch hc'

/-- The postponement route class, sealed-refuted at the Loop fixture: the
cyclic `ConvT` exists while the `ParRedStar` join does not. -/
theorem postponeJoinable_false_at_loop {n : Nat} :
    Nonempty (ConvT (eraseEnv pinLoopEnvA) n [.assumption (.const 60 [])]
        (erase pinLoopA) (erase pinLoopArrow) (.sort .zero)) ∧
    ¬ Joinable (eraseEnv pinLoopEnvA) n [.assumption (.const 60 [])]
        (erase pinLoopA) (erase pinLoopArrow) :=
  ⟨pinLoopConv_erased, parRedJoinable_pinLoop_false⟩

#print axioms pinLoopEnvA_noFun
#print axioms pinLoopEnvA_normErase
#print axioms pinLoopEnvA_iotaErases
#print axioms pinLoopConv_erased
#print axioms parRed_pinLoop_spine
#print axioms parRedStar_pinLoopX_class
#print axioms parRedStar_pi_class
#print axioms parRedJoinable_pinLoop_false
#print axioms postponeJoinable_false_at_loop

end Rcic.Declarative.Ann
