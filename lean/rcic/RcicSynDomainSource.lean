/-
# Syntactic sortRow — failed-reader domain decoders (BELOWC_FAILED_READERS_AND_LET_BODY §2)

Structural source decoders behind the failed readers. `readPi`/`readLam`/
`readRedex` answer semantic questions and decline spines they cannot push
(`lsub`, `cctx`, a substitution-born λ). The decoders here are different:
they walk the derivation and select the *original field* at the matching
head, re-applying the same transport frame on the way out. They are total
(no `Classical.choose`), and each selected typing is strictly lighter than
the owner it was read from.

1. **`TyP.piDomSrc_subject`** — the landed `piDomSrc` returns a typing of
   the Π node's own domain `A`.

2. **`DomainSource` / `AppSource`** — typed outputs: a `domain : sort u`
   typing and the `f : Π A B`, `a : A` pair of an application.

3. **Bounds and AP** — `wt` strictly below the owner (`appDomain` below
   `hf` below `D`), `AssumpPref` preserved fieldwise.

4. **Reader compatibility** — when `readLam`/`readRedex` do answer, the
   structural decoder's level is the reader's level.

5. **§6 controls** — kernel fixtures: `cctx`-wrapped Π (`readPi = .no`,
   source `6 < 8`), `lsub`-wrapped Π (`4 < 6`), and the substitution-born
   β redex (`readRedex = .no`, selected source is the replacement's own
   `hA`, weight `1`).
-/

import rcic.RcicSynIotaRoutePlan
import rcic.RcicSynHeadView
import rcic.RcicSynRedex
import rcic.RcicSynPiLamRight
import rcic.RcicSynLetInline

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 output structures and cast invariance -/

/-- A sort-typing of a domain expression `A`, with the sort's level.
    Carries the selected subject/type (`e' : T'`) plus equations, so the
    decoder never casts a derivation — `wt`/`AssumpPref` are direct. -/
structure DomainSource (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A : Expr Nat) : Type where
  u : Level
  e' : Expr Nat
  T' : Expr Nat
  H : TyP E n Γ e' T'
  hT : T' = .sort u
  he' : e' = A

/-- The function/argument pair of a typing of `.app f a`: the function's
    ascribed Π and the argument's typing at the recorded domain. -/
structure AppSource (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (f a : Expr Nat) : Type where
  A : Expr Nat
  B : Expr Nat
  f' : Expr Nat
  a' : Expr Nat
  hf : TyP E n Γ f' (.pi A B)
  ha : TyP E n Γ a' A
  feq : f' = f
  aeq : a' = a

/-- The level stored in a `.sort` head (`.zero` elsewhere). -/
def sortLvl : Expr Nat → Level
  | .sort u => u
  | _ => .zero

theorem sortLvl_eq_of_isSort {e : Expr Nat} (h : ∃ u, e = .sort u) :
    e = .sort (sortLvl e) := by
  rcases h with ⟨u, rfl⟩
  rfl

/-- Weight is index-insensitive: subject casts preserve it. -/
theorem TyP.wt_castS (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {T e e' : Expr Nat} (h : e = e') (D : TyP E n Γ e T) :
    (h ▸ D).wt Aw = D.wt Aw := by
  cases h
  rfl

/-- Weight is index-insensitive: type casts preserve it. -/
theorem TyP.wt_castT (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T T' : Expr Nat} (h : T = T') (D : TyP E n Γ e T) :
    (h ▸ D).wt Aw = D.wt Aw := by
  cases h
  rfl

/-- `AssumpPref` is index-insensitive: subject casts preserve it. -/
theorem TyP.ap_castS {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T e e' : Expr Nat} (h : e = e') (D : TyP E n Γ e T) :
    (h ▸ D).AssumpPref = D.AssumpPref := by
  cases h
  rfl

/-- `AssumpPref` is index-insensitive: type casts preserve it. -/
theorem TyP.ap_castT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T T' : Expr Nat} (h : T = T') (D : TyP E n Γ e T) :
    (h ▸ D).AssumpPref = D.AssumpPref := by
  cases h
  rfl

/-! ## §2 `piDomSrc` subject and `piDomain` -/

/-- The landed `piDomSrc` selects a typing of the Π node's own domain `A`. -/
theorem TyP.piDomSrc_subject : {E : ResolvedEnv} → {n : Nat} →
    {Γ : LCtx} → {e T A B : Expr Nat} →
    (D : TyP E n Γ e T) → (he : e = .pi A B) →
    (TyP.piDomSrc D he).1 = A
  | _, _, _, _, _, _, _, .sort .., he => by cases he
  | _, _, _, _, _, _, _, .bvar .., he => by cases he
  | _, _, _, _, _, _, _, .const .., he => by cases he
  | _, _, _, _, _, _, _, .pi _ _ _ _ _ _ _ hA _, he => by
      cases he
      rfl
  | _, _, _, _, _, _, _, .lam .., he => by cases he
  | _, _, _, _, _, _, _, .app .., he => by cases he
  | _, _, _, _, _, _, _, .letE .., he => by cases he
  | _, _, _, _, _, _, _, .lit .., he => by cases he
  | _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, he =>
      TyP.piDomSrc_subject h he
  | _, _, _, _, _, _, _, .wk _ _ _ _ _ _ _ inner, he => by
      dsimp only [TyP.piDomSrc]
      cases lift_eq_pi he with
      | mk _ _ he₀ hAe _ =>
          simp only [TyP.piDomSrc]
          rw [TyP.piDomSrc_subject inner he₀]
          exact hAe
  | _, _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [TyP.piDomSrc]
      cases instantiate_eq_pi he with
      | under _ _ he₀ hAe _ =>
          simp only [TyP.piDomSrc]
          rw [TyP.piDomSrc_subject inner he₀]
          exact hAe
      | here _ hr => exact TyP.piDomSrc_subject hv hr
  | _, _, _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [TyP.piDomSrc]
      cases instantiate_eq_pi he with
      | under _ _ he₀ hAe _ =>
          simp only [TyP.piDomSrc]
          rw [TyP.piDomSrc_subject inner he₀]
          exact hAe
      | here _ hr => exact TyP.piDomSrc_subject hv hr
  | _, _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ inner, he => by
      dsimp only [TyP.piDomSrc]
      cases instantiateLevels_eq_pi he with
      | mk _ _ he₀ hAe _ =>
          simp only [TyP.piDomSrc]
          rw [TyP.piDomSrc_subject inner he₀]
          exact hAe
  | _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ inner, he =>
      TyP.piDomSrc_subject inner he
  | _, _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner _, he =>
      TyP.piDomSrc_subject inner he

/-- `piDomain`: the domain typing of a Π typing, packaged as a sort-typing
    of `A`. -/
def TyP.piDomain {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A B : Expr Nat}
    (D : TyP E n Γ e T) (he : e = .pi A B) : DomainSource E n Γ A :=
  ⟨sortLvl (TyP.piDomSrc D he).2.1, (TyP.piDomSrc D he).1,
    (TyP.piDomSrc D he).2.1, (TyP.piDomSrc D he).2.2,
    sortLvl_eq_of_isSort (TyP.piDomSrc_isSort D he),
    TyP.piDomSrc_subject D he⟩

/-- `AssumpPref` of the `piDomSrc` walk. -/
theorem TyP.piDomSrc_ap : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T A B : Expr Nat} → (D : TyP E n Γ e T) → (he : e = .pi A B) →
    D.AssumpPref → (TyP.piDomSrc D he).2.2.AssumpPref
  | _, _, _, _, _, _, _, .sort .., he, _ => by cases he
  | _, _, _, _, _, _, _, .bvar .., he, _ => by cases he
  | _, _, _, _, _, _, _, .const .., he, _ => by cases he
  | _, _, _, _, _, _, _, .pi _ _ _ _ _ _ _ hA _, _, hAP => hAP.1
  | _, _, _, _, _, _, _, .lam .., he, _ => by cases he
  | _, _, _, _, _, _, _, .app .., he, _ => by cases he
  | _, _, _, _, _, _, _, .letE .., he, _ => by cases he
  | _, _, _, _, _, _, _, .lit .., he, _ => by cases he
  | _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, he, hAP =>
      TyP.piDomSrc_ap h he hAP.1
  | _, _, _, _, _, _, _, .wk _ _ _ _ _ _ _ inner, he, hAP => by
      dsimp only [TyP.piDomSrc]
      cases lift_eq_pi he with
      | mk _ _ he₀ _ _ =>
          simp only [TyP.piDomSrc]
          exact ⟨hAP.1, TyP.piDomSrc_ap inner he₀ hAP.2⟩
  | _, _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner _ hv hvT, he, hAP => by
      dsimp only [TyP.piDomSrc]
      cases instantiate_eq_pi he with
      | under _ _ he₀ _ _ =>
          simp only [TyP.piDomSrc]
          exact ⟨hAP.1, TyP.piDomSrc_ap inner he₀ hAP.2.1,
            hAP.2.2.1, hAP.2.2.2⟩
      | here _ hr => exact TyP.piDomSrc_ap hv hr hAP.2.2.1
  | _, _, _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ inner _ hv hvT, he, hAP => by
      dsimp only [TyP.piDomSrc]
      cases instantiate_eq_pi he with
      | under _ _ he₀ _ _ =>
          simp only [TyP.piDomSrc]
          exact ⟨hAP.1, TyP.piDomSrc_ap inner he₀ hAP.2.1,
            hAP.2.2.1, hAP.2.2.2⟩
      | here _ hr => exact TyP.piDomSrc_ap hv hr hAP.2.2.1
  | _, _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ inner, he, hAP => by
      dsimp only [TyP.piDomSrc]
      cases instantiateLevels_eq_pi he with
      | mk _ _ he₀ _ _ =>
          simp only [TyP.piDomSrc]
          exact TyP.piDomSrc_ap inner he₀ hAP
  | _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ inner, he, hAP =>
      TyP.piDomSrc_ap inner he hAP
  | _, _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner _, he, hAP =>
      ⟨TyP.piDomSrc_ap inner he hAP.1, hAP.2⟩

/-- `wt` of the packaged `piDomain` view is strictly below the owner. -/
theorem TyP.piDomain_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T A B : Expr Nat}
    (D : TyP E n Γ e T) (he : e = .pi A B) :
    (TyP.piDomain D he).H.wt Aw < D.wt Aw := by
  unfold TyP.piDomain
  exact TyP.piDomSrc_wt_lt Aw D he

/-- `AssumpPref` of `piDomain`. -/
theorem TyP.piDomain_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A B : Expr Nat} (D : TyP E n Γ e T) (he : e = .pi A B)
    (hAP : D.AssumpPref) : (TyP.piDomain D he).H.AssumpPref := by
  unfold TyP.piDomain
  exact TyP.piDomSrc_ap D he hAP

/-! ## §3 `lamDomain`: the domain of a λ typing -/

/-- Total structural decoder for a typing of `.lam A b`: the `A : sort u`
    field, re-framed under each transport. `lsub`/`cctx` are decoded too —
    the readers decline them, the structure does not. -/
def lamDomain {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A b : Expr Nat} :
    (D : TyP E n Γ e T) → e = .lam A b → DomainSource E n Γ A
  | .sort .., he => by cases he
  | .bvar .., he => by cases he
  | .const .., he => by cases he
  | .pi .., he => by cases he
  | .lam _ _ _ _ u _ _ _ hA _ _, he => by
      cases he
      exact ⟨u, _, _, hA, rfl, rfl⟩
  | .app .., he => by cases he
  | .letE .., he => by cases he
  | .lit .., he => by cases he
  | .conv _ _ _ _ _ _ _ h _, he => lamDomain h he
  | .wk _ _ _ _ _ d c inner, he =>
      match lift_eq_lam he with
      | .mk _ _ he₀ hAe _ =>
          let r := lamDomain inner he₀
          ⟨r.u, lift c 1 r.e', lift c 1 r.T',
            .wk _ _ _ _ _ d c r.H,
            congrArg (lift c 1) r.hT,
            (congrArg (lift c 1) r.he').trans hAe⟩
  | .esub _ _ _ _ _ _ v j _ inner hget hv hvT, he =>
      match instantiate_eq_lam he with
      | .under _ _ he₀ hAe _ =>
          let r := lamDomain inner he₀
          ⟨r.u, instantiate j (lift 0 j v) r.e',
            instantiate j (lift 0 j v) r.T',
            .esub _ _ _ _ _ _ _ _ _ r.H hget hv hvT,
            congrArg (instantiate j (lift 0 j v)) r.hT,
            (congrArg (instantiate j (lift 0 j v)) r.he').trans hAe⟩
      | .here _ hr => lamDomain hv hr
  | .lsub _ _ _ _ _ _ v j _ inner hget hv hvT, he =>
      match instantiate_eq_lam he with
      | .under _ _ he₀ hAe _ =>
          let r := lamDomain inner he₀
          ⟨r.u, instantiate j (lift 0 j v) r.e',
            instantiate j (lift 0 j v) r.T',
            .lsub _ _ _ _ _ _ _ _ _ r.H hget hv hvT,
            congrArg (instantiate j (lift 0 j v)) r.hT,
            (congrArg (instantiate j (lift 0 j v)) r.he').trans hAe⟩
      | .here _ hr => lamDomain hv hr
  | .linst _ _ _ _ _ _ ls hls hlen inner, he =>
      match instantiateLevels_eq_lam he with
      | .mk _ _ he₀ hAe _ =>
          let r := lamDomain inner he₀
          ⟨instLevel ls r.u, instantiateLevels ls r.e',
            instantiateLevels ls r.T',
            .linst _ _ _ _ _ _ _ hls hlen r.H,
            congrArg (instantiateLevels ls) r.hT,
            (congrArg (instantiateLevels ls) r.he').trans hAe⟩
  | .ewk _ _ _ _ _ _ hext inner, he =>
      let r := lamDomain inner he
      ⟨r.u, r.e', r.T', .ewk _ _ _ _ _ _ hext r.H, r.hT, r.he'⟩
  | .cctx _ _ _ _ _ _ _ _ inner hconv, he =>
      let r := lamDomain inner he
      ⟨r.u, r.e', r.T', .cctx _ _ _ _ _ _ _ _ r.H hconv, r.hT, r.he'⟩

/-- `lamDomain` strictly descends in weight. -/
theorem lamDomain_wt_lt (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} →
    {Γ : LCtx} → {e T A b : Expr Nat} →
    (D : TyP E n Γ e T) → (he : e = .lam A b) →
    (lamDomain D he).H.wt Aw < D.wt Aw
  | _, _, _, _, _, _, _, .sort .., he => by cases he
  | _, _, _, _, _, _, _, .bvar .., he => by cases he
  | _, _, _, _, _, _, _, .const .., he => by cases he
  | _, _, _, _, _, _, _, .pi .., he => by cases he
  | _, _, _, _, _, _, _, .lam .., he => by
      cases he
      simp only [lamDomain, TyP.wt]
      omega
  | _, _, _, _, _, _, _, .app .., he => by cases he
  | _, _, _, _, _, _, _, .letE .., he => by cases he
  | _, _, _, _, _, _, _, .lit .., he => by cases he
  | _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, he =>
      Nat.lt_of_lt_of_le (lamDomain_wt_lt Aw h he)
        (by simp only [TyP.wt]; omega)
  | _, _, _, _, _, _, _, .wk _ _ _ _ _ _ _ inner, he => by
      dsimp only [lamDomain]
      cases lift_eq_lam he with
      | mk _ _ he₀ _ _ =>
          have ih := lamDomain_wt_lt Aw inner he₀
          simp only [lamDomain, TyP.wt]
          omega
  | _, _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [lamDomain]
      cases instantiate_eq_lam he with
      | under _ _ he₀ _ _ =>
          have ih := lamDomain_wt_lt Aw inner he₀
          simp only [lamDomain, TyP.wt]
          omega
      | here _ hr =>
          have ih := lamDomain_wt_lt Aw hv hr
          simp only [TyP.wt]
          omega
  | _, _, _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [lamDomain]
      cases instantiate_eq_lam he with
      | under _ _ he₀ _ _ =>
          have ih := lamDomain_wt_lt Aw inner he₀
          simp only [lamDomain, TyP.wt]
          omega
      | here _ hr =>
          have ih := lamDomain_wt_lt Aw hv hr
          simp only [TyP.wt]
          omega
  | _, _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ inner, he => by
      dsimp only [lamDomain]
      cases instantiateLevels_eq_lam he with
      | mk _ _ he₀ _ _ =>
          have ih := lamDomain_wt_lt Aw inner he₀
          simp only [lamDomain, TyP.wt]
          omega
  | _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ inner, he => by
      have ih := lamDomain_wt_lt Aw inner he
      simp only [lamDomain, TyP.wt]
      omega
  | _, _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner _, he => by
      have ih := lamDomain_wt_lt Aw inner he
      simp only [lamDomain, TyP.wt]
      omega

/-- `lamDomain` preserves `AssumpPref`. -/
theorem lamDomain_ap : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T A b : Expr Nat} → (D : TyP E n Γ e T) → (he : e = .lam A b) →
    D.AssumpPref → (lamDomain D he).H.AssumpPref
  | _, _, _, _, _, _, _, .sort .., he, _ => by cases he
  | _, _, _, _, _, _, _, .bvar .., he, _ => by cases he
  | _, _, _, _, _, _, _, .const .., he, _ => by cases he
  | _, _, _, _, _, _, _, .pi .., he, _ => by cases he
  | _, _, _, _, _, _, _, .lam .., he, hAP => by
      cases he
      simp only [lamDomain]
      exact hAP.1
  | _, _, _, _, _, _, _, .app .., he, _ => by cases he
  | _, _, _, _, _, _, _, .letE .., he, _ => by cases he
  | _, _, _, _, _, _, _, .lit .., he, _ => by cases he
  | _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, he, hAP =>
      lamDomain_ap h he hAP.1
  | _, _, _, _, _, _, _, .wk _ _ _ _ _ _ _ inner, he, hAP => by
      dsimp only [lamDomain]
      cases lift_eq_lam he with
      | mk _ _ he₀ _ _ =>
          simp only [lamDomain, TyP.AssumpPref]
          exact ⟨hAP.1, lamDomain_ap inner he₀ hAP.2⟩
  | _, _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner _ hv hvT, he, hAP => by
      dsimp only [lamDomain]
      cases instantiate_eq_lam he with
      | under _ _ he₀ _ _ =>
          simp only [lamDomain, TyP.AssumpPref]
          exact ⟨hAP.1, lamDomain_ap inner he₀ hAP.2.1,
            hAP.2.2.1, hAP.2.2.2⟩
      | here _ hr => exact lamDomain_ap hv hr hAP.2.2.1
  | _, _, _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ inner _ hv hvT, he, hAP => by
      dsimp only [lamDomain]
      cases instantiate_eq_lam he with
      | under _ _ he₀ _ _ =>
          simp only [lamDomain, TyP.AssumpPref]
          exact ⟨hAP.1, lamDomain_ap inner he₀ hAP.2.1,
            hAP.2.2.1, hAP.2.2.2⟩
      | here _ hr => exact lamDomain_ap hv hr hAP.2.2.1
  | _, _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ inner, he, hAP => by
      dsimp only [lamDomain]
      cases instantiateLevels_eq_lam he with
      | mk _ _ he₀ _ _ =>
          simp only [lamDomain, TyP.AssumpPref]
          exact lamDomain_ap inner he₀ hAP
  | _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ inner, he, hAP =>
      lamDomain_ap inner he hAP
  | _, _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner _, he, hAP =>
      ⟨lamDomain_ap inner he hAP.1, hAP.2⟩

/-- The selected level does not depend on which lam-equation is passed. -/
theorem lamDomain_u_of_he {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A₁ b₁ A₂ b₂ : Expr Nat} (D : TyP E n Γ e T)
    (he₁ : e = Expr.lam A₁ b₁) (he₂ : e = Expr.lam A₂ b₂) :
    (lamDomain D he₁).u = (lamDomain D he₂).u := by
  have hAB : Expr.lam A₁ b₁ = Expr.lam A₂ b₂ := he₁.symm.trans he₂
  injection hAB with hA hb
  subst hA
  subst hb
  rfl

/-- Casting a derivation to a lam subject preserves the decoded level. -/
theorem lamDomain_u_cast {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T' f' f A b A₀ b₀ : Expr Nat} (feq : f' = f)
    (hf' : TyP E n Γ f' T') (he : f = Expr.lam A b) (he₀ : f' = Expr.lam A₀ b₀) :
    (lamDomain (feq ▸ hf') he).u = (lamDomain hf' he₀).u := by
  cases feq
  have hAB : Expr.lam A b = Expr.lam A₀ b₀ := he.symm.trans he₀
  injection hAB with hA hb
  subst hA
  subst hb
  rfl

/-- Casting a derivation to a lam subject preserves the decoded weight. -/
theorem lamDomain_wt_cast (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {T' f' f A b A₀ b₀ : Expr Nat} (feq : f' = f)
    (hf' : TyP E n Γ f' T') (he : f = Expr.lam A b) (he₀ : f' = Expr.lam A₀ b₀) :
    (lamDomain (feq ▸ hf') he).H.wt Aw = (lamDomain hf' he₀).H.wt Aw := by
  cases feq
  have hAB : Expr.lam A b = Expr.lam A₀ b₀ := he.symm.trans he₀
  injection hAB with hA hb
  subst hA
  subst hb
  rfl

/-! ## §4 `appSrc` / `appSource` / `appDomain` -/

/-- The function/argument pair of an application typing, at the actual
    (possibly transported) sub-expressions, plus the equations back to `f a`.
    Keeping the fields uncast is what lets `lamDomain` descend through the
    re-applied frames. -/
structure AppSrcRes (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (f a : Expr Nat) : Type where
  f' : Expr Nat
  a' : Expr Nat
  A' : Expr Nat
  B' : Expr Nat
  hf : TyP E n Γ f' (.pi A' B')
  ha : TyP E n Γ a' A'
  feq : f' = f
  aeq : a' = a

/-- Total structural decoder for a typing of `.app f a`. -/
def TyP.appSrc {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T f a : Expr Nat} :
    (D : TyP E n Γ e T) → e = .app f a → AppSrcRes E n Γ f a
  | .sort .., he => by cases he
  | .bvar .., he => by cases he
  | .const .., he => by cases he
  | .pi .., he => by cases he
  | .lam .., he => by cases he
  | .app _ _ _ _ _ _ _ _ hf ha _, he => by
      cases he
      exact ⟨f, a, _, _, hf, ha, rfl, rfl⟩
  | .letE .., he => by cases he
  | .lit .., he => by cases he
  | .conv _ _ _ _ _ _ _ h _, he => TyP.appSrc h he
  | .wk _ _ _ _ _ d c inner, he =>
      match lift_eq_app he with
      | .mk _ _ he₀ hf₀ ha₀ =>
          let r := TyP.appSrc inner he₀
          ⟨lift c 1 r.f', lift c 1 r.a', lift c 1 r.A', lift (c + 1) 1 r.B',
            .wk _ _ _ _ _ d c r.hf, .wk _ _ _ _ _ d c r.ha,
            (congrArg (lift c 1) r.feq).trans hf₀,
            (congrArg (lift c 1) r.aeq).trans ha₀⟩
  | .esub _ _ _ _ _ _ v j _ inner hget hv hvT, he =>
      match instantiate_eq_app he with
      | .under _ _ he₀ hf₀ ha₀ =>
          let r := TyP.appSrc inner he₀
          ⟨instantiate j (lift 0 j v) r.f', instantiate j (lift 0 j v) r.a',
            instantiate j (lift 0 j v) r.A',
            instantiate (j + 1) (lift 0 1 (lift 0 j v)) r.B',
            .esub _ _ _ _ _ _ _ _ _ r.hf hget hv hvT,
            .esub _ _ _ _ _ _ _ _ _ r.ha hget hv hvT,
            (congrArg (instantiate j (lift 0 j v)) r.feq).trans hf₀,
            (congrArg (instantiate j (lift 0 j v)) r.aeq).trans ha₀⟩
      | .here _ hr => TyP.appSrc hv hr
  | .lsub _ _ _ _ _ _ v j _ inner hget hv hvT, he =>
      match instantiate_eq_app he with
      | .under _ _ he₀ hf₀ ha₀ =>
          let r := TyP.appSrc inner he₀
          ⟨instantiate j (lift 0 j v) r.f', instantiate j (lift 0 j v) r.a',
            instantiate j (lift 0 j v) r.A',
            instantiate (j + 1) (lift 0 1 (lift 0 j v)) r.B',
            .lsub _ _ _ _ _ _ _ _ _ r.hf hget hv hvT,
            .lsub _ _ _ _ _ _ _ _ _ r.ha hget hv hvT,
            (congrArg (instantiate j (lift 0 j v)) r.feq).trans hf₀,
            (congrArg (instantiate j (lift 0 j v)) r.aeq).trans ha₀⟩
      | .here _ hr => TyP.appSrc hv hr
  | .linst _ _ _ _ _ _ ls hls hlen inner, he =>
      match instantiateLevels_eq_app he with
      | .mk _ _ he₀ hf₀ ha₀ =>
          let r := TyP.appSrc inner he₀
          ⟨instantiateLevels ls r.f', instantiateLevels ls r.a',
            instantiateLevels ls r.A', instantiateLevels ls r.B',
            .linst _ _ _ _ _ _ _ hls hlen r.hf,
            .linst _ _ _ _ _ _ _ hls hlen r.ha,
            (congrArg (instantiateLevels ls) r.feq).trans hf₀,
            (congrArg (instantiateLevels ls) r.aeq).trans ha₀⟩
  | .ewk _ _ _ _ _ _ hext inner, he =>
      let r := TyP.appSrc inner he
      ⟨r.f', r.a', r.A', r.B', .ewk _ _ _ _ _ _ hext r.hf,
        .ewk _ _ _ _ _ _ hext r.ha, r.feq, r.aeq⟩
  | .cctx _ _ _ _ _ _ _ _ inner hconv, he =>
      let r := TyP.appSrc inner he
      ⟨r.f', r.a', r.A', r.B', .cctx _ _ _ _ _ _ _ _ r.hf hconv,
        .cctx _ _ _ _ _ _ _ _ r.ha hconv, r.feq, r.aeq⟩

/-- Both components of `appSrc` are strictly lighter than the owner. -/
theorem TyP.appSrc_wt (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} →
    {Γ : LCtx} → {e T f a : Expr Nat} →
    (D : TyP E n Γ e T) → (he : e = .app f a) →
    (TyP.appSrc D he).hf.wt Aw < D.wt Aw ∧ (TyP.appSrc D he).ha.wt Aw < D.wt Aw
  | _, _, _, _, _, _, _, .sort .., he => by cases he
  | _, _, _, _, _, _, _, .bvar .., he => by cases he
  | _, _, _, _, _, _, _, .const .., he => by cases he
  | _, _, _, _, _, _, _, .pi .., he => by cases he
  | _, _, _, _, _, _, _, .lam .., he => by cases he
  | _, _, _, _, _, _, _, .app .., he => by
      cases he
      refine ⟨?_, ?_⟩ <;> (simp only [TyP.appSrc, TyP.wt]; omega)
  | _, _, _, _, _, _, _, .letE .., he => by cases he
  | _, _, _, _, _, _, _, .lit .., he => by cases he
  | _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, he =>
      have ih := TyP.appSrc_wt Aw h he
      ⟨Nat.lt_of_lt_of_le ih.1 (by simp only [TyP.wt]; omega),
        Nat.lt_of_lt_of_le ih.2 (by simp only [TyP.wt]; omega)⟩
  | _, _, _, _, _, _, _, .wk _ _ _ _ _ _ _ inner, he => by
      dsimp only [TyP.appSrc]
      cases lift_eq_app he with
      | mk _ _ he₀ _ _ =>
          have ih := TyP.appSrc_wt Aw inner he₀
          refine ⟨?_, ?_⟩ <;> (simp only [TyP.appSrc, TyP.wt]; omega)
  | _, _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [TyP.appSrc]
      cases instantiate_eq_app he with
      | under _ _ he₀ _ _ =>
          have ih := TyP.appSrc_wt Aw inner he₀
          refine ⟨?_, ?_⟩ <;> (simp only [TyP.appSrc, TyP.wt]; omega)
      | here _ hr =>
          have ih := TyP.appSrc_wt Aw hv hr
          refine ⟨?_, ?_⟩ <;> (simp only [TyP.wt]; omega)
  | _, _, _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [TyP.appSrc]
      cases instantiate_eq_app he with
      | under _ _ he₀ _ _ =>
          have ih := TyP.appSrc_wt Aw inner he₀
          refine ⟨?_, ?_⟩ <;> (simp only [TyP.appSrc, TyP.wt]; omega)
      | here _ hr =>
          have ih := TyP.appSrc_wt Aw hv hr
          refine ⟨?_, ?_⟩ <;> (simp only [TyP.wt]; omega)
  | _, _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ inner, he => by
      dsimp only [TyP.appSrc]
      cases instantiateLevels_eq_app he with
      | mk _ _ he₀ _ _ =>
          have ih := TyP.appSrc_wt Aw inner he₀
          refine ⟨?_, ?_⟩ <;> (simp only [TyP.appSrc, TyP.wt]; omega)
  | _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ inner, he => by
      have ih := TyP.appSrc_wt Aw inner he
      refine ⟨?_, ?_⟩ <;> (simp only [TyP.appSrc, TyP.wt]; omega)
  | _, _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner _, he => by
      have ih := TyP.appSrc_wt Aw inner he
      refine ⟨?_, ?_⟩ <;> (simp only [TyP.appSrc, TyP.wt]; omega)

/-- `appSrc` preserves `AssumpPref` fieldwise. -/
theorem TyP.appSrc_ap : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T f a : Expr Nat} → (D : TyP E n Γ e T) → (he : e = .app f a) →
    D.AssumpPref →
    (TyP.appSrc D he).hf.AssumpPref ∧ (TyP.appSrc D he).ha.AssumpPref
  | _, _, _, _, _, _, _, .sort .., he, _ => by cases he
  | _, _, _, _, _, _, _, .bvar .., he, _ => by cases he
  | _, _, _, _, _, _, _, .const .., he, _ => by cases he
  | _, _, _, _, _, _, _, .pi .., he, _ => by cases he
  | _, _, _, _, _, _, _, .lam .., he, _ => by cases he
  | _, _, _, _, _, _, _, .app .., he, hAP => by
      cases he
      simp only [TyP.appSrc]
      exact ⟨hAP.1, hAP.2.1⟩
  | _, _, _, _, _, _, _, .letE .., he, _ => by cases he
  | _, _, _, _, _, _, _, .lit .., he, _ => by cases he
  | _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, he, hAP =>
      TyP.appSrc_ap h he hAP.1
  | _, _, _, _, _, _, _, .wk _ _ _ _ _ _ _ inner, he, hAP => by
      dsimp only [TyP.appSrc]
      cases lift_eq_app he with
      | mk _ _ he₀ _ _ =>
          have ⟨ihf, iha⟩ := TyP.appSrc_ap inner he₀ hAP.2
          simp only [TyP.appSrc, TyP.AssumpPref]
          exact ⟨⟨hAP.1, ihf⟩, ⟨hAP.1, iha⟩⟩
  | _, _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner _ hv hvT, he, hAP => by
      dsimp only [TyP.appSrc]
      cases instantiate_eq_app he with
      | under _ _ he₀ _ _ =>
          have ⟨ihf, iha⟩ := TyP.appSrc_ap inner he₀ hAP.2.1
          simp only [TyP.appSrc, TyP.AssumpPref]
          exact ⟨⟨hAP.1, ihf, hAP.2.2.1, hAP.2.2.2⟩,
            ⟨hAP.1, iha, hAP.2.2.1, hAP.2.2.2⟩⟩
      | here _ hr => exact TyP.appSrc_ap hv hr hAP.2.2.1
  | _, _, _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ inner _ hv hvT, he, hAP => by
      dsimp only [TyP.appSrc]
      cases instantiate_eq_app he with
      | under _ _ he₀ _ _ =>
          have ⟨ihf, iha⟩ := TyP.appSrc_ap inner he₀ hAP.2.1
          simp only [TyP.appSrc, TyP.AssumpPref]
          exact ⟨⟨hAP.1, ihf, hAP.2.2.1, hAP.2.2.2⟩,
            ⟨hAP.1, iha, hAP.2.2.1, hAP.2.2.2⟩⟩
      | here _ hr => exact TyP.appSrc_ap hv hr hAP.2.2.1
  | _, _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ inner, he, hAP => by
      dsimp only [TyP.appSrc]
      cases instantiateLevels_eq_app he with
      | mk _ _ he₀ _ _ =>
          have ⟨ihf, iha⟩ := TyP.appSrc_ap inner he₀ hAP
          simp only [TyP.appSrc, TyP.AssumpPref]
          exact ⟨ihf, iha⟩
  | _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ inner, he, hAP =>
      TyP.appSrc_ap inner he hAP
  | _, _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner _, he, hAP =>
      have ⟨ihf, iha⟩ := TyP.appSrc_ap inner he hAP.1
      ⟨⟨ihf, hAP.2⟩, ⟨iha, hAP.2⟩⟩

/-- The packaged `AppSource`: the `appSrc` fields, equations carried. -/
def appSource {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T f a : Expr Nat}
    (D : TyP E n Γ e T) (he : e = .app f a) : AppSource E n Γ f a :=
  ⟨(TyP.appSrc D he).A', (TyP.appSrc D he).B', (TyP.appSrc D he).f',
    (TyP.appSrc D he).a', (TyP.appSrc D he).hf, (TyP.appSrc D he).ha,
    (TyP.appSrc D he).feq, (TyP.appSrc D he).aeq⟩

theorem appSource_hf_wt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T f a : Expr Nat}
    (D : TyP E n Γ e T) (he : e = .app f a) :
    (appSource D he).hf.wt Aw < D.wt Aw := by
  unfold appSource
  exact (TyP.appSrc_wt Aw D he).1

theorem appSource_ha_wt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T f a : Expr Nat}
    (D : TyP E n Γ e T) (he : e = .app f a) :
    (appSource D he).ha.wt Aw < D.wt Aw := by
  unfold appSource
  exact (TyP.appSrc_wt Aw D he).2

theorem appSource_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T f a : Expr Nat} (D : TyP E n Γ e T) (he : e = .app f a)
    (hAP : D.AssumpPref) :
    (appSource D he).hf.AssumpPref ∧ (appSource D he).ha.AssumpPref := by
  unfold appSource
  exact TyP.appSrc_ap D he hAP

/-- `appDomain`: `piDomain` of the application function's regularity —
    the application's recorded domain typing. -/
def appDomain {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T f a : Expr Nat}
    (D : TyP E n Γ e T) (he : e = .app f a) :
    DomainSource E n Γ (appSource D he).A :=
  TyP.piDomain (appSource D he).hf.reg.2 rfl

theorem appDomain_wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T f a : Expr Nat}
    (D : TyP E n Γ e T) (he : e = .app f a) :
    (appDomain D he).H.wt Aw < (appSource D he).hf.wt Aw := by
  unfold appDomain
  exact Nat.lt_of_lt_of_le (TyP.piDomain_wt_lt Aw _ _)
    (TyP.wt_reg_le Aw _)

theorem appDomain_lt_D (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T f a : Expr Nat}
    (D : TyP E n Γ e T) (he : e = .app f a) :
    (appDomain D he).H.wt Aw < D.wt Aw :=
  Nat.lt_trans (appDomain_wt_lt Aw D he) (appSource_hf_wt Aw D he)

theorem appDomain_ap {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T f a : Expr Nat} (D : TyP E n Γ e T) (he : e = .app f a)
    (hAP : D.AssumpPref) : (appDomain D he).H.AssumpPref := by
  unfold appDomain
  exact TyP.piDomain_ap _ rfl
    (assumpPref_reg (appSource_ap D he hAP).1)

/-! ## §5 reader compatibility -/

/-- When `readLam` answers, its level is the structural domain's level. -/
theorem lamDomain_u_of_readLam {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {A body : Expr Nat} → (he : e = .lam A body) →
    {g : LamGot Aw (D.wt Aw) E n Γ A body} →
    readLam hext Aw D he = .yes g → (lamDomain D he).u = g.u
  | _, _, _, _, .sort .., _, _, he, _, _ => by cases he
  | _, _, _, _, .bvar .., _, _, he, _, _ => by cases he
  | _, _, _, _, .const .., _, _, he, _, _ => by cases he
  | _, _, _, _, .pi .., _, _, he, _, _ => by cases he
  | _, _, _, _, .lam .., _, _, he, g, hr => by
      cases he
      simp only [readLam] at hr
      cases hr
      rfl
  | _, _, _, _, .app .., _, _, he, _, _ => by cases he
  | _, _, _, _, .letE .., _, _, he, _, _ => by cases he
  | _, _, _, _, .lit .., _, _, he, _, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner _, _, _, he, g, hr => by
      unfold readLam at hr
      simp only [LamRead.raise] at hr
      cases hri : readLam hext Aw inner he with
      | no => rw [hri] at hr; cases hr
      | yes g₀ =>
          rw [hri] at hr
          cases hr
          dsimp only [lamDomain]
          exact lamDomain_u_of_readLam hext Aw inner he hri
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he, g, hr => by
      unfold readLam at hr
      dsimp only [lamDomain]
      cases hscr : lift_eq_lam he with
      | mk _ _ he₀ hAe hb₀ =>
          rw [hscr] at hr
          simp only [pushLamWk, LamRead.raise] at hr
          cases hri : readLam hext Aw inner he₀ with
          | no => rw [hri] at hr; cases hr
          | yes g₀ =>
              rw [hri] at hr
              cases hr
              exact lamDomain_u_of_readLam hext Aw inner he₀ hri
  | _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner hget hv hvT, _, _, he, g, hr => by
      unfold readLam at hr
      dsimp only [lamDomain]
      cases hscr : instantiate_eq_lam he with
      | under _ _ he₀ hAe hb₀ =>
          simp only [hscr] at hr
          simp only [pushLamEsub] at hr
          cases hri : readLam hext Aw inner he₀ with
          | no => rw [hri] at hr; cases hr
          | yes g₀ =>
              rw [hri] at hr
              cases hr
              simp only []
              exact lamDomain_u_of_readLam hext Aw inner he₀ hri
      | here _ hr₂ =>
          simp only [hscr] at hr
          simp only [LamRead.raise] at hr
          cases hri : readLam hext Aw hv hr₂ with
          | no => rw [hri] at hr; cases hr
          | yes g₀ =>
              rw [hri] at hr
              cases hr
              simp only []
              exact lamDomain_u_of_readLam hext Aw hv hr₂ hri
  | _, _, _, _, .lsub .., _, _, he, _, hr => by
      unfold readLam at hr
      cases hr
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he, g, hr => by
      unfold readLam at hr
      dsimp only [lamDomain]
      cases hscr : instantiateLevels_eq_lam he with
      | mk _ _ he₀ hAe hb₀ =>
          rw [hscr] at hr
          simp only [pushLamLinst, LamRead.raise] at hr
          cases hri : readLam hext Aw inner he₀ with
          | no => rw [hri] at hr; cases hr
          | yes g₀ =>
              rw [hri] at hr
              cases hr
              exact congrArg (instLevel ls)
                (lamDomain_u_of_readLam hext Aw inner he₀ hri)
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, he, g, hr => by
      unfold readLam at hr
      simp only [LamRead.raise] at hr
      cases hri : readLam (envExt_trans hext' hext) Aw inner he with
      | no => rw [hri] at hr; cases hr
      | yes g₀ =>
          rw [hri] at hr
          cases hr
          dsimp only [lamDomain]
          exact lamDomain_u_of_readLam (envExt_trans hext' hext) Aw inner he hri
  | _, _, _, _, .cctx .., _, _, he, _, hr => by
      unfold readLam at hr
      cases hr

/-- Reader compatibility at the uncast `appSrc`, with independent decoder
    equations. The decoder's own instantiation analysis may pick `.under`
    or `.here` on a different scrutinee than the reader's — the statement
    only needs `u` agreement, and the mismatched `.here` combinations are
    shown contradictory. -/
theorem appSrc_domain_u {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    {A b arg : Expr Nat} → (he : e = .app (.lam A b) arg) →
    {g : RedexGot Aw (D.wt Aw) E n Γ A b arg} →
    readRedex hext Aw D he = .yes g →
    {f a A' b' : Expr Nat} → (he' : e = .app f a) →
    (hef : f = .lam A' b') →
    (lamDomain (TyP.appSrc D he').hf
      ((TyP.appSrc D he').feq.trans hef)).u = g.u
  | _, _, _, _, .sort .., _, _, _, he, _, _, _, _, _, _, _, _ => by cases he
  | _, _, _, _, .bvar .., _, _, _, he, _, _, _, _, _, _, _, _ => by cases he
  | _, _, _, _, .const .., _, _, _, he, _, _, _, _, _, _, _, _ => by cases he
  | _, _, _, _, .pi .., _, _, _, he, _, _, _, _, _, _, _, _ => by cases he
  | _, _, _, _, .lam .., _, _, _, he, _, _, _, _, _, _, _, _ => by cases he
  | _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _, _, _, _, he, g, hr, _, _, _, _, he', hef => by
      cases he
      cases he'
      cases hef
      simp only [TyP.appSrc]
      simp only [readRedex] at hr
      cases hri : readLam hext Aw hf rfl with
      | no => rw [hri] at hr; cases hr
      | yes g₀ =>
          rw [hri] at hr
          cases hr
          exact (lamDomain_u_of_he hf _ rfl).trans
            (lamDomain_u_of_readLam hext Aw hf rfl hri)
  | _, _, _, _, .letE .., _, _, _, he, _, _, _, _, _, _, _, _ => by cases he
  | _, _, _, _, .lit .., _, _, _, he, _, _, _, _, _, _, _, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ inner _, _, _, _, he, g, hr, _, _, _, _, he', hef => by
      simp only [readRedex] at hr
      simp only [RedexRead.raise] at hr
      cases hri : readRedex hext Aw inner he with
      | no => rw [hri] at hr; cases hr
      | yes g₀ =>
          rw [hri] at hr
          cases hr
          dsimp only [TyP.appSrc]
          exact appSrc_domain_u hext Aw inner he hri he' hef
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, _, he, g, hr, _, _, _, _, he', hef => by
      simp only [readRedex] at hr
      dsimp only [TyP.appSrc]
      cases hA : lift_eq_app he with
      | mk f₀ a₀ he₀ hf₀ ha₀ =>
          rw [hA] at hr
          cases hL : lift_eq_lam hf₀ with
          | mk A₀ b₀ heLam hAe hb₀ =>
              dsimp only [] at hr
              rw [hL] at hr
              dsimp only [] at hr
              cases hri : readRedex hext Aw inner (app_of_lam he₀ heLam) with
              | no => rw [hri] at hr; cases hr
              | yes g₀ =>
                  rw [hri] at hr
                  cases hr
                  cases hA' : lift_eq_app he' with
                  | mk f₀' a₀' he₀' hf₀' ha₀' =>
                      simp only [TyP.appSrc]
                      dsimp only [lamDomain]
                      cases hLL : lift_eq_lam
                        ((congrArg (lift c 1) (TyP.appSrc inner he₀').feq).trans
                          hf₀' |>.trans hef) with
                      | mk _ _ heLam'' _ _ =>
                          simp only [lamDomain]
                          cases hL2 : lift_eq_lam (hf₀'.trans hef) with
                          | mk _ _ heLam' _ _ =>
                              exact (lamDomain_u_of_he _
                                heLam''
                                ((TyP.appSrc inner he₀').feq.trans heLam')).trans
                                  (appSrc_domain_u hext Aw inner
                                    (app_of_lam he₀ heLam) hri he₀' heLam')
  | _, _, _, _, .esub _ _ _ _ _ _ v j _ inner hget hv hvT, _, _, _, he, g, hr, _, _, _, _, he', hef => by
      simp only [readRedex] at hr
      dsimp only [TyP.appSrc]
      cases hA : instantiate_eq_app he with
      | under f₀ a₀ he₀ hf₀ ha₀ =>
          simp only [hA] at hr
          cases hL : instantiate_eq_lam hf₀ with
          | under A₀ b₀ heLam hAe hb₀ =>
              simp only [hL] at hr
              simp only [pushRedexEsub] at hr
              cases hri : readRedex hext Aw inner (app_of_lam he₀ heLam) with
              | no => rw [hri] at hr; cases hr
              | yes g₀ =>
                  rw [hri] at hr
                  cases hr
                  cases hA' : instantiate_eq_app he' with
                  | under f₀' a₀' he₀' hf₀' ha₀' =>
                      simp only [TyP.appSrc]
                      dsimp only [lamDomain]
                      cases hLL : instantiate_eq_lam
                        ((congrArg (instantiate j (lift 0 j v))
                          (TyP.appSrc inner he₀').feq).trans hf₀' |>.trans hef) with
                      | under _ _ heLam'' _ _ =>
                          simp only [lamDomain]
                          cases hL2 : instantiate_eq_lam (hf₀'.trans hef) with
                          | under _ _ heLam' _ _ =>
                              exact (lamDomain_u_of_he _
                                heLam''
                                ((TyP.appSrc inner he₀').feq.trans heLam')).trans
                                  (appSrc_domain_u hext Aw inner
                                    (app_of_lam he₀ heLam) hri he₀' heLam')
                          | here hs' _ =>
                              have hfinj : f₀' = f₀ := by
                                have hxy := he₀'.symm.trans he₀
                                injection hxy
                              exact Expr.noConfusion
                                (hs'.symm.trans (hfinj.trans heLam))
                      | here hs _ =>
                          have hfinj : f₀' = f₀ := by
                            have hxy := he₀'.symm.trans he₀
                            injection hxy
                          exact Expr.noConfusion
                            (hs.symm.trans
                              ((TyP.appSrc inner he₀').feq.trans
                                (hfinj.trans heLam)))
                  | here hs' _ =>
                      simp only [TyP.appSrc]
                      exact Expr.noConfusion (he₀.symm.trans hs')
          | here _ _ =>
              simp only [hL] at hr
              cases hr
      | here hs₂ hr₂ =>
          simp only [hA] at hr
          simp only [RedexRead.raise] at hr
          cases hri : readRedex hext Aw hv hr₂ with
          | no => rw [hri] at hr; cases hr
          | yes g₀ =>
              rw [hri] at hr
              cases hr
              cases hA' : instantiate_eq_app he' with
              | under f₀' a₀' he₀' hf₀' ha₀' =>
                  simp only [TyP.appSrc]
                  exact Expr.noConfusion (he₀'.symm.trans hs₂)
              | here _ hr₂' =>
                  simp only [TyP.appSrc]
                  exact appSrc_domain_u hext Aw hv hr₂ hri hr₂' hef
  | _, _, _, _, .lsub .., _, _, _, he, _, hr, _, _, _, _, _, _ => by
      simp only [readRedex] at hr
      cases hr
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, _, he, g, hr, _, _, _, _, he', hef => by
      simp only [readRedex] at hr
      dsimp only [TyP.appSrc]
      cases hA : instantiateLevels_eq_app he with
      | mk f₀ a₀ he₀ hf₀ ha₀ =>
          rw [hA] at hr
          cases hL : instantiateLevels_eq_lam hf₀ with
          | mk A₀ b₀ heLam hAe hb₀ =>
              dsimp only [] at hr
              rw [hL] at hr
              dsimp only [] at hr
              cases hri : readRedex hext Aw inner (app_of_lam he₀ heLam) with
              | no => rw [hri] at hr; cases hr
              | yes g₀ =>
                  rw [hri] at hr
                  cases hr
                  cases hA' : instantiateLevels_eq_app he' with
                  | mk _ _ he₀' hf₀' ha₀' =>
                      simp only [TyP.appSrc]
                      dsimp only [lamDomain]
                      cases hLL : instantiateLevels_eq_lam
                        ((congrArg (instantiateLevels ls)
                          (TyP.appSrc inner he₀').feq).trans hf₀' |>.trans hef) with
                      | mk _ _ heLam'' _ _ =>
                          simp only [lamDomain]
                          cases hL2 : instantiateLevels_eq_lam (hf₀'.trans hef) with
                          | mk _ _ heLam' _ _ =>
                              exact congrArg (instLevel ls)
                                ((lamDomain_u_of_he _
                                  heLam''
                                  ((TyP.appSrc inner he₀').feq.trans heLam')).trans
                                    (appSrc_domain_u hext Aw inner
                                      (app_of_lam he₀ heLam) hri he₀' heLam'))
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, _, he, g, hr, _, _, _, _, he', hef => by
      simp only [readRedex] at hr
      simp only [RedexRead.raise] at hr
      cases hri : readRedex (envExt_trans hext' hext) Aw inner he with
      | no => rw [hri] at hr; cases hr
      | yes g₀ =>
          rw [hri] at hr
          cases hr
          dsimp only [TyP.appSrc]
          exact appSrc_domain_u (envExt_trans hext' hext) Aw inner he hri he' hef
  | _, _, _, _, .cctx .., _, _, _, he, _, hr, _, _, _, _, _, _ => by
      simp only [readRedex] at hr
      cases hr

/-- When `readRedex` answers, its level is the structural domain's level
    of the application function. -/
theorem readRedex_domain_u {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) {n : Nat} {Γ : LCtx} {e T A b arg : Expr Nat}
    (D : TyP Ei n Γ e T) (he : e = .app (.lam A b) arg)
    {g : RedexGot Aw (D.wt Aw) E n Γ A b arg}
    (hr : readRedex hext Aw D he = .yes g) :
    (lamDomain (appSource D he).hf (appSource D he).feq).u = g.u := by
  unfold appSource
  exact (lamDomain_u_of_he (TyP.appSrc D he).hf
      ((TyP.appSrc D he).feq.trans rfl) (TyP.appSrc D he).feq).symm.trans
    (appSrc_domain_u hext Aw D he hr he rfl)

/-! ## §6 controls (kernel fixtures) -/

namespace Controls

private def l0 : Level := .zero
private def l1 : Level := .succ l0
private def l2 : Level := .succ l1

private def sort0 (Γ : LCtx) : TyP emptyEnv 0 Γ (.sort l0) (.sort l1) :=
  TyP.sort _ _ _ _ _ (eqN_refl _)

private def sort1 (Γ : LCtx) : TyP emptyEnv 0 Γ (.sort l1) (.sort l2) :=
  TyP.sort _ _ _ _ _ (eqN_refl _)

/-- An `ewk`-stacked `.sort l0` typing — weight `1 + 5 = 6`. -/
private def ewk5sort0 (Γ : LCtx) : TyP emptyEnv 0 Γ (.sort l0) (.sort l1) :=
  TyP.ewk _ _ _ _ _ _ (envExt_refl _)
    (TyP.ewk _ _ _ _ _ _ (envExt_refl _)
      (TyP.ewk _ _ _ _ _ _ (envExt_refl _)
        (TyP.ewk _ _ _ _ _ _ (envExt_refl _)
          (TyP.ewk _ _ _ _ _ _ (envExt_refl _) (sort0 Γ)))))

/-- An `ewk`-stacked `.sort l0` typing — weight `1 + 3 = 4`. -/
private def ewk3sort0 (Γ : LCtx) : TyP emptyEnv 0 Γ (.sort l0) (.sort l1) :=
  TyP.ewk _ _ _ _ _ _ (envExt_refl _)
    (TyP.ewk _ _ _ _ _ _ (envExt_refl _)
      (TyP.ewk _ _ _ _ _ _ (envExt_refl _) (sort0 Γ)))

/-! ### cctx-wrapped Π -/

/-- The inner Π at `[.assumption (.sort l0)]`, with a weight-`6` domain
    typing: `wt = 1 + 6 + 1 = 8`. -/
def cctxPiInner : TyP emptyEnv 0 [.assumption (.sort l0)]
    (.pi (.sort l0) (.sort l1)) (.sort (.imax l1 l2)) :=
  TyP.pi _ _ _ _ _ _ _ (ewk5sort0 _) (sort1 _)

/-- The context-binder conversion `.sort l0 ≡ .sort l0`. -/
def cctxPiConv : CvP emptyEnv 0 [] (.sort l0) (.sort l0) (.sort l1) :=
  CvP.sorts _ _ _ _ _ (eqN_refl _) (sort0 _) (sort0 _)

/-- A `cctx`-wrapped Π typing — `wt = 1 + 8 + 3 = 12`. -/
def cctxPi : TyP emptyEnv 0 [.assumption (.sort l0)]
    (.pi (.sort l0) (.sort l1)) (.sort (.imax l1 l2)) :=
  TyP.cctx _ _ _ _ _ _ _ _ cctxPiInner cctxPiConv

/-- `readPi` declines the `cctx` spine. -/
theorem readPi_cctxPi (Aw : Nat → Nat) :
    readPi (envExt_refl emptyEnv) Aw (cctxPi.wt Aw + 1) cctxPi rfl
      (fun y hy => atoms_lt_of_wt_lt Aw cctxPi (Nat.lt_succ_self _) y hy)
      = .no := rfl

/-- The transported structural source — the `cctx`-reapplied domain,
    weight `1 + 6 + 3 = 10`. -/
theorem cctxPi_source_wt (Aw : Nat → Nat) :
    (TyP.piDomain cctxPi rfl).H.wt Aw = 10 := by
  unfold TyP.piDomain
  rfl

/-- The pre-transport domain the decoder selected — weight `6`. -/
theorem cctxPi_inner_source_wt (Aw : Nat → Nat) :
    (TyP.piDomain cctxPiInner rfl).H.wt Aw = 6 := by
  unfold TyP.piDomain
  rfl

/-- The selected domain sits below the Π node it was taken from —
    `6 < 8`. -/
theorem cctxPiInner_wt (Aw : Nat → Nat) : cctxPiInner.wt Aw = 8 := rfl

theorem cctxPi_source_lt_inner (Aw : Nat → Nat) :
    (TyP.piDomain cctxPiInner rfl).H.wt Aw < cctxPiInner.wt Aw := by
  rw [cctxPi_inner_source_wt, cctxPiInner_wt]
  decide

/-- And the transported source sits below the wrapped owner — `10 < 12`. -/
theorem cctxPi_owner_wt (Aw : Nat → Nat) : cctxPi.wt Aw = 12 := rfl

theorem cctxPi_source_lt_owner (Aw : Nat → Nat) :
    (TyP.piDomain cctxPi rfl).H.wt Aw < cctxPi.wt Aw := by
  rw [cctxPi_source_wt, cctxPi_owner_wt]
  decide

/-! ### lsub-wrapped Π -/

/-- The inner Π at `[.letBinding (.sort l1) (.sort l0)]`, with a weight-`4`
    domain typing: `wt = 1 + 4 + 1 = 6`. -/
def lsubPiInner : TyP emptyEnv 0 [.letBinding (.sort l1) (.sort l0)]
    (.pi (.sort l0) (.sort l1)) (.sort (.imax l1 l2)) :=
  TyP.pi _ _ _ _ _ _ _ (ewk3sort0 _) (sort1 _)

/-- The let-inlined Π typing (`v := .sort l0`, `t := .sort l1`) —
    `wt = 1 + 6 + 1 + 1 = 9`. -/
def lsubPi : TyP emptyEnv 0 []
    (.pi (.sort l0) (.sort l1)) (.sort (.imax l1 l2)) :=
  TyP.lsub _ _ _ _ _ _ _ 0 _ lsubPiInner rfl (sort0 _) (sort1 _)

/-- `readPi` declines the `lsub` spine. -/
theorem readPi_lsubPi (Aw : Nat → Nat) :
    readPi (envExt_refl emptyEnv) Aw (lsubPi.wt Aw + 1) lsubPi rfl
      (fun y hy => atoms_lt_of_wt_lt Aw lsubPi (Nat.lt_succ_self _) y hy)
      = .no := rfl

/-- The transported structural source — the `lsub`-reapplied domain,
    weight `1 + 4 + 1 + 1 = 7`. -/
theorem lsubPi_source_wt (Aw : Nat → Nat) :
    (TyP.piDomain lsubPi rfl).H.wt Aw = 7 := by
  unfold TyP.piDomain
  rfl

/-- The pre-transport domain the decoder selected — weight `4`. -/
theorem lsubPiInner_source_wt (Aw : Nat → Nat) :
    (TyP.piDomain lsubPiInner rfl).H.wt Aw = 4 := by
  unfold TyP.piDomain
  rfl

/-- The selected domain sits below the Π node it was taken from —
    `4 < 6`. -/
theorem lsubPiInner_wt (Aw : Nat → Nat) : lsubPiInner.wt Aw = 6 := rfl

theorem lsubPi_source_lt_inner (Aw : Nat → Nat) :
    (TyP.piDomain lsubPiInner rfl).H.wt Aw < lsubPiInner.wt Aw := by
  rw [lsubPiInner_source_wt, lsubPiInner_wt]
  decide

/-- And the transported source sits below the wrapped owner — `7 < 9`. -/
theorem lsubPi_owner_wt (Aw : Nat → Nat) : lsubPi.wt Aw = 9 := rfl

theorem lsubPi_source_lt_owner (Aw : Nat → Nat) :
    (TyP.piDomain lsubPi rfl).H.wt Aw < lsubPi.wt Aw := by
  rw [lsubPi_source_wt, lsubPi_owner_wt]
  decide

/-! ### substitution-born β redex -/

private def esubΓ : LCtx :=
  [.assumption (.pi (.sort l0) (.sort l1)), .assumption (.sort l0)]

private def esubPi : TyP emptyEnv 0 esubΓ
    (.pi (.sort l0) (.sort l1)) (.sort (.imax l1 l2)) :=
  TyP.pi _ _ _ _ _ _ _ (sort0 _) (sort1 _)

/-- `f = .bvar 0`, ascribed the Π by `lookupType`. -/
private def esubHf : TyP emptyEnv 0 esubΓ (.bvar 0)
    (.pi (.sort l0) (.sort l1)) :=
  TyP.bvar _ _ _ 0 _ _ rfl esubPi

/-- `a = .bvar 1`, ascribed `.sort l0`. -/
private def esubHa : TyP emptyEnv 0 esubΓ (.bvar 1) (.sort l0) :=
  TyP.bvar _ _ _ 1 _ _ rfl (sort0 _)

/-- The inner application `.app (.bvar 0) (.bvar 1)`. -/
private def esubInner : TyP emptyEnv 0 esubΓ
    (.app (.bvar 0) (.bvar 1)) (.sort l1) :=
  TyP.app _ _ _ _ _ _ _ _ esubHf esubHa (sort1 _)

/-- The replacement λ `λ(.sort l0).(.sort l0)` at the reduced context. -/
private def vlam : TyP emptyEnv 0 [.assumption (.sort l0)]
    (.lam (.sort l0) (.sort l0)) (.pi (.sort l0) (.sort l1)) :=
  TyP.lam _ _ _ _ _ _ _ _ (sort0 _) (sort0 _) (sort1 _)

/-- `hvT` for the esub: the assumption's type `.pi (.sort l0)(.sort l1)`
    is a sort at the reduced context. -/
private def esubHvT : TyP emptyEnv 0 [.assumption (.sort l0)]
    (.pi (.sort l0) (.sort l1)) (.sort (.imax l1 l2)) :=
  TyP.pi _ _ _ _ _ _ _ (sort0 _) (sort1 _)

/-- `esub` at index `0` over `esubInner`, replacing `.bvar 0` with the λ:
    the redex `.app (.lam (.sort l0) (.sort l0)) (.bvar 0)` is born from
    the substitution, not present in the pre-subst subject. -/
def esubD : TyP emptyEnv 0 [.assumption (.sort l0)]
    (.app (.lam (.sort l0) (.sort l0)) (.bvar 0)) (.sort l1) :=
  TyP.esub _ _ _ _ _ _ (.lam (.sort l0) (.sort l0)) 0 _
    esubInner rfl vlam esubHvT

/-- `readRedex` declines the substitution-born λ. -/
theorem esub_redex_no (Aw : Nat → Nat) :
    readRedex (envExt_refl emptyEnv) Aw esubD rfl = .no := rfl

/-- The structural decoder still selects a domain — literally the
    replacement's own `hA` (`vlam`'s domain typing). -/
theorem esub_domain_H :
    (lamDomain (appSource esubD rfl).hf (appSource esubD rfl).feq).H
      = sort0 _ := by
  unfold appSource
  rfl

/-- Its weight is `1`. -/
theorem esub_domain_wt (Aw : Nat → Nat) :
    (lamDomain (appSource esubD rfl).hf (appSource esubD rfl).feq).H.wt Aw
      = 1 := by
  unfold appSource
  rfl

theorem esub_domain_u :
    (lamDomain (appSource esubD rfl).hf (appSource esubD rfl).feq).u = l1 := by
  unfold appSource
  rfl

end Controls

end Rcic.Syn
