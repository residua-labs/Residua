import rcic.RcicF3MinorRec

/-! Transport the full hereditary environment contract across pointwise
set equivalence of constant tables. In particular, iota keeps both hereditary
premises and its Good/level-bound witness. closure_claim = 0. -/
set_option autoImplicit false

namespace Rcic.F3.PSet.TableSound
open Rcic.Declarative

variable (P : Premises4) {μ ν : Nat → List Nat → PSet.{4}}
  (h : ∀ r ls, Equiv (μ r ls) (ν r ls)) (σ : Nat → Nat)
include h

theorem value_mem_iff (A : Expr Nat) (ρ : Nat → PSet.{4}) (x : PSet.{4}) :
    x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ A) ↔
      x ∈ Ed (mkM P ν) (den (mkM P ν) σ ρ A) := by
  have he := ed_congr (mkM P ν) (den_tables P h σ A (ρ := ρ) (fun _ => Equiv.rfl))
  exact ⟨mem_congr_right he, mem_congr_right he.symm⟩

theorem den_mem_iff (e A : Expr Nat) (ρ : Nat → PSet.{4}) :
    den (mkM P μ) σ ρ e ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ A) ↔
      den (mkM P ν) σ ρ e ∈ Ed (mkM P ν) (den (mkM P ν) σ ρ A) := by
  have he := den_tables P h σ e (ρ := ρ) (fun _ => Equiv.rfl)
  exact ⟨fun hm => mem_congr_left he ((value_mem_iff P h σ A ρ _).mp hm),
    fun hm => (value_mem_iff P h σ A ρ _).mpr (mem_congr_left he.symm hm)⟩

theorem den_equiv_iff (a b : Expr Nat) (ρ : Nat → PSet.{4}) :
    Equiv (den (mkM P μ) σ ρ a) (den (mkM P μ) σ ρ b) ↔
      Equiv (den (mkM P ν) σ ρ a) (den (mkM P ν) σ ρ b) := by
  have ha := den_tables P h σ a (ρ := ρ) (fun _ => Equiv.rfl)
  have hb := den_tables P h σ b (ρ := ρ) (fun _ => Equiv.rfl)
  exact ⟨fun he => ha.symm.trans (he.trans hb), fun he => ha.trans (he.trans hb.symm)⟩

theorem fits_iff (Γ : LCtx) (ρ : Nat → PSet.{4}) :
    Fits (mkM P μ) σ Γ ρ ↔ Fits (mkM P ν) σ Γ ρ := by
  induction Γ generalizing ρ with
  | nil => exact Iff.rfl
  | cons d Γ ih =>
    cases d with
    | assumption A => exact and_congr (ih _) (value_mem_iff P h σ A (tl ρ) (ρ 0))
    | letBinding A v =>
      have he := den_tables P h σ v (ρ := tl ρ) (fun _ => Equiv.rfl)
      exact and_congr (ih _) (and_congr (value_mem_iff P h σ A (tl ρ) (ρ 0))
        ⟨fun hv => hv.trans he, fun hv => hv.trans he.symm⟩)

theorem rootT_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (d : HasTyT E n Γ e A) : RootT (mkM P μ) σ d ↔ RootT (mkM P ν) σ d := by
  constructor
  · intro hd ρ hf
    exact (den_mem_iff P h σ e A ρ).mp (hd ρ ((fits_iff P h σ Γ ρ).mpr hf))
  · intro hd ρ hf
    exact (den_mem_iff P h σ e A ρ).mpr (hd ρ ((fits_iff P h σ Γ ρ).mp hf))

theorem rootC_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A : Expr Nat}
    (d : ConvT E n Γ a b A) : RootC (mkM P μ) σ d ↔ RootC (mkM P ν) σ d := by
  constructor
  · intro hd ρ hf
    have hs := hd ρ ((fits_iff P h σ Γ ρ).mpr hf)
    exact ⟨(den_equiv_iff P h σ a b ρ).mp hs.1, (den_mem_iff P h σ a A ρ).mp hs.2⟩
  · intro hd ρ hf
    have hs := hd ρ ((fits_iff P h σ Γ ρ).mp hf)
    exact ⟨(den_equiv_iff P h σ a b ρ).mpr hs.1, (den_mem_iff P h σ a A ρ).mpr hs.2⟩

variable {E : ResolvedEnv} {n : Nat}

mutual
theorem hereditaryT_iff : {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) →
    (HSoundT (mkM P μ) σ d ↔ HSoundT (mkM P ν) σ d)
  | _, _, _, d@(.sort _ _) => rootT_iff P h σ d
  | _, _, _, d@(.bvar _ _ _ _) => rootT_iff P h σ d
  | _, _, _, d@(.const _ _ _ _ _ _ _) => rootT_iff P h σ d
  | _, _, _, d@(.pi _ _ _ _ _ hA hB) =>
      and_congr (rootT_iff P h σ d) (and_congr (hereditaryT_iff hA) (hereditaryT_iff hB))
  | _, _, _, d@(.lam _ _ _ _ _ hA hb) =>
      and_congr (rootT_iff P h σ d) (and_congr (hereditaryT_iff hA) (hereditaryT_iff hb))
  | _, _, _, d@(.app _ _ _ _ _ hf ha) =>
      and_congr (rootT_iff P h σ d) (and_congr (hereditaryT_iff hf) (hereditaryT_iff ha))
  | _, _, _, d@(.letE _ _ _ _ _ _ hA hv hb) =>
      and_congr (rootT_iff P h σ d) (and_congr (hereditaryT_iff hA)
        (and_congr (hereditaryT_iff hv) (hereditaryT_iff hb)))
  | _, _, _, d@(.lit _ _ _ he) => and_congr (rootT_iff P h σ d) (hereditaryT_iff he)
  | _, _, _, d@(.conv _ _ _ _ _ hd hc) =>
      and_congr (rootT_iff P h σ d) (and_congr (hereditaryT_iff hd) (hereditaryC_iff hc))

theorem hereditaryC_iff : {Γ : LCtx} → {a b A : Expr Nat} → (d : ConvT E n Γ a b A) →
    (HSoundC (mkM P μ) σ d ↔ HSoundC (mkM P ν) σ d)
  | _, _, _, _, d@(.refl _ _ _ ht) => and_congr (rootC_iff P h σ d) (hereditaryT_iff ht)
  | _, _, _, _, d@(.symm _ _ _ _ hc) => and_congr (rootC_iff P h σ d) (hereditaryC_iff hc)
  | _, _, _, _, d@(.trans _ _ _ _ _ h1 h2) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryC_iff h1) (hereditaryC_iff h2))
  | _, _, _, _, d@(.beta _ _ _ _ _ _ hA hb ha) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryT_iff hA)
        (and_congr (hereditaryT_iff hb) (hereditaryT_iff ha)))
  | _, _, _, _, d@(.zeta _ _ _ _ _ _ hA hv hb) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryT_iff hA)
        (and_congr (hereditaryT_iff hv) (hereditaryT_iff hb)))
  | _, _, _, _, d@(.zetaLocal _ _ _ _ _ _ hv) =>
      and_congr (rootC_iff P h σ d) (hereditaryT_iff hv)
  | _, _, _, _, d@(.delta _ _ _ _ _ _ _ _ _ _ hb) =>
      and_congr (rootC_iff P h σ d) (hereditaryT_iff hb)
  | _, _, _, _, d@(.iota _ _ _ _ _ hl hr) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryT_iff hl) (hereditaryT_iff hr))
  | _, _, _, _, d@(.lit _ _ _ _ _ he) => and_congr (rootC_iff P h σ d) (hereditaryT_iff he)
  | _, _, _, _, d@(.app _ _ _ _ _ _ _ h1 h2) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryC_iff h1) (hereditaryC_iff h2))
  | _, _, _, _, d@(.lam _ _ _ _ _ _ _ hA hb) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryC_iff hA) (hereditaryC_iff hb))
  | _, _, _, _, d@(.pi _ _ _ _ _ _ _ hA hB) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryC_iff hA) (hereditaryC_iff hB))
  | _, _, _, _, d@(.letE _ _ _ _ _ _ _ _ _ hA hv hb) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryC_iff hA)
        (and_congr (hereditaryC_iff hv) (hereditaryC_iff hb)))
  | _, _, _, _, d@(.sorts _ _ _ _) => rootC_iff P h σ d
  | _, _, _, _, d@(.consts _ _ _ _ _ _ _ _ _ _) => rootC_iff P h σ d
  | _, _, _, _, d@(.eta _ _ _ _ ht) => and_congr (rootC_iff P h σ d) (hereditaryT_iff ht)
  | _, _, _, _, d@(.irr _ _ _ _ hp ht hq) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryT_iff hp)
        (and_congr (hereditaryT_iff ht) (hereditaryT_iff hq)))
  | _, _, _, _, d@(.tyConv _ _ _ _ _ _ hc hA) =>
      and_congr (rootC_iff P h σ d) (and_congr (hereditaryC_iff hc) (hereditaryC_iff hA))
end

/-- Full environment soundness, including the hereditary iota contract. -/
theorem environment {K : Nat → Nat} (hE : EnvSound (mkM P μ) σ K E n) :
    EnvSound (mkM P ν) σ K E n where
  const := by
    intro Γ r ls m ρ hm hlen hl hf
    exact mem_congr_left (h r _) ((value_mem_iff P h σ _ ρ _).mp
      (hE.const Γ r ls m ρ hm hlen hl ((fits_iff P h σ Γ ρ).mpr hf)))
  delta := by
    intro Γ r ls m b ρ hm hb ht hlen hl hf
    exact (h r _).symm.trans
      ((hE.delta Γ r ls m b ρ hm hb ht hlen hl ((fits_iff P h σ Γ ρ).mpr hf)).trans
        (den_tables P h σ _ (ρ := ρ) (fun _ => Equiv.rfl)))
  iota := by
    intro Γ lhs rhs T ρ hi hl hr il ir hg hf ml mr
    have hg' : ∃ (N : Nat) (Lv : Nat → PSet.{4} → Prop),
        Good (mkM P μ) N Lv ∧ LOKt σ N K hl := by
      obtain ⟨N, Lv, hGood, hL⟩ := hg
      exact ⟨N, Lv, ⟨hGood.congr, hGood.dich, hGood.lvl0, hGood.U_iff,
        hGood.univ, hGood.prop, hGood.mono, hGood.pi⟩, hL⟩
    exact (den_equiv_iff P h σ lhs rhs ρ).mp
      (hE.iota Γ lhs rhs T ρ hi hl hr
        ((hereditaryT_iff P h σ hl).mpr il) ((hereditaryT_iff P h σ hr).mpr ir)
        hg' ((fits_iff P h σ Γ ρ).mpr hf)
        ((den_mem_iff P h σ lhs T ρ).mpr ml) ((den_mem_iff P h σ rhs T ρ).mpr mr))

end Rcic.F3.PSet.TableSound
