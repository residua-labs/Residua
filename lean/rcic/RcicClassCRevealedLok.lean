import rcic.RcicClassCRevealedRows
import rcic.RcicF3Defs

/-!
# cc-classc — `ri_inj_internal` with its level bound (gap α, syntactic side)

`ri_inj_internal` (`RcicClassCRevealedRows`) reads `x ≡ x' : Sort 0` off a type-conversion chain
`RI x ≡* RI x'` through `RI`'s own recursor. Here the same script (retype, ι, irr, ι, β) is built again
without the cast that the landed proof uses, and its F3 level bound `LOKc σ N K` (`RcicF3Defs`) is proved:
the output is within the bound of the inputs (`hx`, `hx'` and the chain's legs), plus the literal
constants the script introduces. Those are `Sort 0`, `Sort 1` (so `N ≥ 2`) and `rec.{1}` (so `K 2 ≥ 1`).
Nothing in the output depends on any other level.

`ri_inj_internalB` is the new construction; `ri_inj_internalB_lok` is the bound; the unchanged
`ri_inj_internal` stays as it is. closure_claim = 0.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Syn.ClassC

open Rcic.Declarative Rcic.F3.PSet

/-- the bound on a `TyConvT` chain: its legs. -/
def LOKtc {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtx} → {a b : Expr Nat} → TyConvT E n Γ a b → Prop
  | _, _, _, .refl _ _ => True
  | _, _, _, .of _ _ _ _ h => LOKc σ N K h
  | _, _, _, .trans _ _ _ _ h1 h2 => LOKtc σ N K h1 ∧ LOKtc σ N K h2

/-- a conversion retyped along an equality of its type (no content). -/
def castT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T T' : Expr Nat} (h : T = T')
    (c : ConvT E n Γ a b T) : ConvT E n Γ a b T' := h ▸ c

theorem LOKc_castT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T T' : Expr Nat} (σ : Nat → Nat)
    (N : Nat) (K : Nat → Nat) (h : T = T') (c : ConvT E n Γ a b T) :
    LOKc σ N K (castT h c) ↔ LOKc σ N K c := by
  subst h; exact Iff.rfl

/-- the type index of a typing, rewritten along an equality. -/
def castHT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T T' : Expr Nat} (h : T = T')
    (d : HasTyT E n Γ e T) : HasTyT E n Γ e T' := h ▸ d

theorem LOKt_castHT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T T' : Expr Nat} (σ : Nat → Nat)
    (N : Nat) (K : Nat → Nat) (h : T = T') (d : HasTyT E n Γ e T) :
    LOKt σ N K (castHT h d) ↔ LOKt σ N K d := by
  subst h; exact Iff.rfl

theorem LOKt_of_tyConv {E : ResolvedEnv} {n : Nat} {a : Expr Nat} (σ : Nat → Nat) (N : Nat)
    (K : Nat → Nat) :
    ∀ {Γ : LCtx} {A B : Expr Nat} (d : HasTyT E n Γ a A) (c : TyConvT E n Γ A B),
      LOKt σ N K d → LOKtc σ N K c → LOKt σ N K (hasTyT_of_tyConv d c)
  | _, _, _, d, .refl _ _, hd, _ => by simp only [hasTyT_of_tyConv]; exact hd
  | _, _, _, d, .of _ _ _ u c, hd, hc => by
      simp only [hasTyT_of_tyConv, LOKt]; simp only [LOKtc] at hc; exact ⟨hd, hc⟩
  | _, _, _, d, .trans _ _ _ _ c₁ c₂, hd, hc => by
      simp only [hasTyT_of_tyConv]; simp only [LOKtc] at hc
      exact LOKt_of_tyConv σ N K _ c₂ (LOKt_of_tyConv σ N K d c₁ hd hc.1) hc.2

section helpers

variable {n : Nat} {Γ : LCtx} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)

@[simp] theorem levelsOK_nil (b : Nat) : LevelsOK σ b [] := fun _ h => by cases h

theorem lok_hS0 (hN : 2 ≤ N) : LOKt σ N K (hS0 (n := n) Γ) := by
  have : 1 ≤ N := by omega
  simp [hS0, LOKt, evalTotal, this]

variable {σ N K}

theorem lok_hRIApp {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) (h : LOKt σ N K ha) :
    LOKt σ N K (hRIApp ha) := by
  simp [hRIApp, LOKt, h]

theorem lok_hMkApp {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) (h : LOKt σ N K ha) :
    LOKt σ N K (hMkApp ha) := by
  simp [hMkApp, LOKt, h]

theorem lok_hM0Body (hN : 2 ≤ N) : LOKt σ N K (hM0Body (n := n) Γ) := by
  have : 1 ≤ N := by omega
  simp [hM0Body, LOKt, evalTotal, hRIApp, this]

theorem lok_hM0 (hN : 2 ≤ N) : LOKt σ N K (hM0 (n := n) Γ) := by
  have : 1 ≤ N := by omega
  simp [hM0, LOKt, hS0, hM0Body, hRIApp, evalTotal, this]

theorem lok_m0Beta {a t : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero))
    (ht : HasTyT riEnv n Γ t (riApp a)) (hN : 2 ≤ N) (h1 : LOKt σ N K ha) (h2 : LOKt σ N K ht) :
    LOKc σ N K (m0Beta ha ht) := by
  have : 1 ≤ N := by omega
  simp [m0Beta, LOKc, LOKt, hS0, hM0Body, hRIApp, evalTotal, h1, h2, this]

theorem lok_hm0 (hN : 2 ≤ N) : LOKt σ N K (hm0 (n := n) Γ) := by
  have h1N : 1 ≤ N := by omega
  have hm := lok_m0Beta (σ := σ) (N := N) (K := K)
    (HasTyT.bvar (n := n) (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)
    (hMkApp (HasTyT.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)) hN trivial
    (by simp [hMkApp, LOKt])
  simp [hm0, LOKt, LOKc, hS0, evalTotal, hm, h1N]

theorem lok_m0AppBeta {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) (hN : 2 ≤ N)
    (h : LOKt σ N K ha) : LOKc σ N K (m0AppBeta ha) := by
  have : 1 ≤ N := by omega
  simp [m0AppBeta, LOKc, LOKt, hS0, evalTotal, h, this]

theorem lok_hm0App {a : Expr Nat} (ha : HasTyT riEnv n Γ a (.sort .zero)) (hN : 2 ≤ N)
    (h : LOKt σ N K ha) : LOKt σ N K (hm0App ha) := by
  have h1 := lok_m0Beta (σ := σ) (N := N) (K := K) ha (hMkApp ha) hN h
    (by simp [hMkApp, LOKt, h])
  have h2 := lok_hm0 (σ := σ) (N := N) (K := K) (n := n) (Γ := Γ) hN
  simp only [hm0App, LOKt]
  exact ⟨⟨h2, h⟩, h1⟩

theorem lok_hRecM0m (hN : 2 ≤ N) (hK : 1 ≤ K 2) : LOKt σ N K (hRecM0m (n := n) Γ) := by
  have h1 := lok_hM0 (σ := σ) (N := N) (K := K) (n := n) (Γ := Γ) hN
  have h2 := lok_hm0 (σ := σ) (N := N) (K := K) (n := n) (Γ := Γ) hN
  simp only [hRecM0m, LOKt]
  refine ⟨⟨?_, h1⟩, h2⟩
  simp [LevelsOK, evalTotal, hK]

theorem lok_hRecM0mY {y : Expr Nat} (hy : HasTyT riEnv n Γ y (.sort .zero)) (hN : 2 ≤ N)
    (hK : 1 ≤ K 2) (h : LOKt σ N K hy) : LOKt σ N K (hRecM0mY hy) := by
  exact (⟨lok_hRecM0m hN hK, h⟩ : LOKt σ N K (HasTyT.app _ _ _ _ _ (hRecM0m Γ) hy))

end helpers


/-! ## the script, without casts hidden in tactic blocks -/

section script

variable {n : Nat} {Γ : LCtx}

theorem inst_riM0 (y q : Expr Nat) :
    instantiate0 q (.app (.app riM0 (lift 0 1 y)) (.bvar 0)) = .app (.app riM0 y) q := by
  show Expr.app (.app (instantiate 0 q riM0) (instantiate 0 q (lift 0 1 y))) q = _
  rw [inst0_lift1]; rfl

/-- `hRecFull` with its type rewrite named. -/
def hRecFullB {y q : Expr Nat} (hy : HasTyT riEnv n Γ y (.sort .zero))
    (hq : HasTyT riEnv n Γ q (riApp y)) :
    HasTyT riEnv n Γ (.app (.app riRecM0m y) q) (.sort .zero) :=
  .conv _ _ _ _ _ (castHT (inst_riM0 y q) (HasTyT.app _ _ _ _ _ (hRecM0mY hy) hq)) (m0Beta hy hq)

def riIotaGB {x y : Expr Nat} (hx : HasTyT riEnv n Γ x (.sort .zero))
    (hy : HasTyT riEnv n Γ y (.sort .zero)) (hq : HasTyT riEnv n Γ (mkApp x) (riApp y)) :
    ConvT riEnv n Γ (.app (.app riRecM0m y) (mkApp x)) (.app riM0m x) (.sort .zero) :=
  .iota _ _ _ _ (.of (riWG y x)) (hRecFullB hy hq) (hm0App hx)

def hcongB {x x' : Expr Nat} (hx' : HasTyT riEnv n Γ x' (.sort .zero))
    (hq : HasTyT riEnv n Γ (mkApp x) (riApp x')) (hq' : HasTyT riEnv n Γ (mkApp x') (riApp x')) :
    ConvT riEnv n Γ (.app (.app riRecM0m x') (mkApp x)) (.app (.app riRecM0m x') (mkApp x'))
      (.sort .zero) :=
  .tyConv _ _ _ _ _ (.succ .zero)
    (castT (inst_riM0 x' (mkApp x))
      (ConvT.app Γ (.app riRecM0m x') (.app riRecM0m x') (mkApp x) (mkApp x')
        (riApp x') (.app (.app riM0 (lift 0 1 x')) (.bvar 0))
        (.refl _ _ _ (hRecM0mY hx')) (.irr _ _ _ _ (hRIApp hx') hq hq')))
    (m0Beta hx' hq)

/-- **`ri_inj_internal`, rebuilt without the cast in a tactic block.** -/
def ri_inj_internalB {x x' : Expr Nat} (hx : HasTyT riEnv n Γ x (.sort .zero))
    (hx' : HasTyT riEnv n Γ x' (.sort .zero)) (hc : TyConvT riEnv n Γ (riApp x) (riApp x')) :
    ConvT riEnv n Γ x x' (.sort .zero) :=
  let hq : HasTyT riEnv n Γ (mkApp x) (riApp x') := hasTyT_of_tyConv (hMkApp hx) hc
  let hq' : HasTyT riEnv n Γ (mkApp x') (riApp x') := hMkApp hx'
  .trans _ _ _ _ _ (.symm _ _ _ _ (m0AppBeta hx))
    (.trans _ _ _ _ _ (.symm _ _ _ _ (riIotaGB hx hx' hq))
      (.trans _ _ _ _ _ (hcongB hx' hq hq')
        (.trans _ _ _ _ _ (riIotaGB hx' hx' hq') (m0AppBeta hx'))))

end script

section scriptLok

variable {n : Nat} {Γ : LCtx} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}

theorem lok_hRecFullB {y q : Expr Nat} (hy : HasTyT riEnv n Γ y (.sort .zero))
    (hq : HasTyT riEnv n Γ q (riApp y)) (hN : 2 ≤ N) (hK : 1 ≤ K 2)
    (h1 : LOKt σ N K hy) (h2 : LOKt σ N K hq) : LOKt σ N K (hRecFullB hy hq) := by
  have a := lok_hRecM0mY (σ := σ) (N := N) (K := K) hy hN hK h1
  have b := lok_m0Beta (σ := σ) (N := N) (K := K) hy hq hN h1 h2
  simp only [hRecFullB, LOKt]
  refine ⟨?_, b⟩
  rw [LOKt_castHT]
  exact ⟨a, h2⟩

theorem lok_riIotaGB {x y : Expr Nat} (hx : HasTyT riEnv n Γ x (.sort .zero))
    (hy : HasTyT riEnv n Γ y (.sort .zero)) (hq : HasTyT riEnv n Γ (mkApp x) (riApp y))
    (hN : 2 ≤ N) (hK : 1 ≤ K 2) (h1 : LOKt σ N K hx) (h2 : LOKt σ N K hy) (h3 : LOKt σ N K hq) :
    LOKc σ N K (riIotaGB hx hy hq) :=
  ⟨lok_hRecFullB hy hq hN hK h2 h3, lok_hm0App hx hN h1⟩

theorem lok_hcongB {x x' : Expr Nat} (hx' : HasTyT riEnv n Γ x' (.sort .zero))
    (hq : HasTyT riEnv n Γ (mkApp x) (riApp x')) (hq' : HasTyT riEnv n Γ (mkApp x') (riApp x'))
    (hN : 2 ≤ N) (hK : 1 ≤ K 2) (h1 : LOKt σ N K hx') (h2 : LOKt σ N K hq)
    (h3 : LOKt σ N K hq') : LOKc σ N K (hcongB hx' hq hq') := by
  refine ⟨?_, lok_m0Beta hx' hq hN h1 h2⟩
  rw [LOKc_castT]
  exact ⟨lok_hRecM0mY hx' hN hK h1, lok_hRIApp hx' h1, h2, h3⟩

/-- **The level bound of the internal injectivity.** The output is within the bound of the two sort
    typings and the chain's legs, given `N ≥ 2` (the script's `Sort 0`, `Sort 1`) and `K 2 ≥ 1`
    (`rec.{1}`). -/
theorem ri_inj_internalB_lok {x x' : Expr Nat} (hx : HasTyT riEnv n Γ x (.sort .zero))
    (hx' : HasTyT riEnv n Γ x' (.sort .zero)) (hc : TyConvT riEnv n Γ (riApp x) (riApp x'))
    (hN : 2 ≤ N) (hK : 1 ≤ K 2)
    (h1 : LOKt σ N K hx) (h2 : LOKt σ N K hx') (h3 : LOKtc σ N K hc) :
    LOKc σ N K (ri_inj_internalB hx hx' hc) := by
  have hq : LOKt σ N K (hasTyT_of_tyConv (hMkApp hx) hc) :=
    LOKt_of_tyConv σ N K _ hc (lok_hMkApp hx h1) h3
  have hq' : LOKt σ N K (hMkApp hx') := lok_hMkApp hx' h2
  simp only [ri_inj_internalB, LOKc]
  exact ⟨lok_m0AppBeta hx hN h1, lok_riIotaGB hx hx' _ hN hK h1 h2 hq,
    lok_hcongB hx' _ _ hN hK h2 hq hq', lok_riIotaGB hx' hx' _ hN hK h2 h2 hq',
    lok_m0AppBeta hx' hN h2⟩

/-- the form gap α asks for: a conversion exists within the bound (the unchanged
    `ri_inj_internal` is the unbounded statement of the same fact). -/
theorem ri_inj_internal_bounded {x x' : Expr Nat} (hx : HasTyT riEnv n Γ x (.sort .zero))
    (hx' : HasTyT riEnv n Γ x' (.sort .zero)) (hc : TyConvT riEnv n Γ (riApp x) (riApp x'))
    (hN : 2 ≤ N) (hK : 1 ≤ K 2)
    (h1 : LOKt σ N K hx) (h2 : LOKt σ N K hx') (h3 : LOKtc σ N K hc) :
    ∃ c : ConvT riEnv n Γ x x' (.sort .zero), LOKc σ N K c :=
  ⟨ri_inj_internalB hx hx' hc, ri_inj_internalB_lok hx hx' hc hN hK h1 h2 h3⟩

end scriptLok

#print axioms ri_inj_internalB_lok
#print axioms ri_inj_internal_bounded

end Rcic.Syn.ClassC
