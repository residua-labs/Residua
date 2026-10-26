import rcic.RcicFamAppTwinLokFund
import rcic.RcicFamAppRevLok
import rcic.RcicFamAppRevFamRow
import rcic.RcicFamAppRevFixture
import rcic.RcicF3Sound
import rcic.RcicF3EnvSound

/-!
# RcicFamAppRevB1Height4 — Height-4 `TwinConvAt4OvershootK` Split, `RevSortLe` Side Condition, and Annotated Twin Producer

Per `cc`'s 2026-10-25 10:05Z and 12:00Z addenda:
`agy-pendwx` (#8084 §5.5) showed that the height-4 model `mkM P μ` (`P : Premises4`) needs only
`TwinConvAt4OvershootK` on the twin (sort/Π height `≤ 4`, arbitrary constant-instance ceiling `K'`)
because `EnvSound (mkM P μ) σ K' R.twin₁ n` holds for **every** `K' : Nat → Nat` (`glm-f3eq`'s
`envSound_twin₁` is polymorphic in `K'`).

## Exact inventory of what is proved vs. defined only in this module

1. **§1 Sort/Π height vs. Constant-instance ceiling & `TwinConvAtNOvershootK` / `TwinConvAt4OvershootK`**:
   - Exact separation of `LOKt σ N K` / `LOKc σ N K` into sort/Π height (`boundTySort σ d ≤ N`,
     `boundConvSort σ c ≤ N`) and constant-instance ceiling (`boundTyConst σ d`, `boundConvConst σ c`).
   - `twinConvAtNOvershootK_iff` and `twinConvAt4OvershootK_iff`:
     `TwinConvAt4OvershootK E_twin n σ Γ a b A ↔ ∃ c : ConvT E_twin n Γ a b A, boundConvSort σ c ≤ 4`.
   - Consumer-side semantic bridges `den_equiv_of_twinConvAt4OvershootK`, context-translation
     equivalence `fits_trCtx_iff_of_den_tr`, and `den_equiv_of_trTwinConvAt4OvershootK` (taking
     `hConv : TwinConvAt4OvershootK E_twin ...` as a **hypothesis**).

2. **§2 Exact side condition on `R.uI` (`RevSortLe` / `RevBaseSortLe`) and refutation when `evalTotal σ R.uI > 4`**:
   - `RevBaseSortLe σ N B := 1 ≤ N ∧ evalTotal σ B.uI ≤ N ∧ boundTySort σ B.hI ≤ N`, and
     `RevSortLe σ N R := 1 ≤ N ∧ evalTotal σ R.uI ≤ N ∧ ∃ K_I : Nat → Nat, ∀ (n : Nat) (Γ : LCtx), LOKt σ N K_I (R.hIEB n Γ)`.
   - Discharged unconditionally at `N = 4` for `riRevBase` / `riRevEnv` (`revBaseSortLe_riRevBase`,
     `revSortLe_riRevEnv`, `revSortLe_four_riRevEnv`) and for any `Nat`-indexed `B : RevBase` /
     `R : RevEnv` such as `glm-f3eq`'s `RcicF3EqFooRev.fooRevBase` / `fooRevEnv`
     (`revBaseSortLe_of_natConst`, `revBaseSortLe_four_of_natConst`, `revSortLe_of_natConst`;
     no duplicate `fooRevBase` is defined here).
   - **Exact refutation when `evalTotal σ R.uI > N` (`not_lokt_revFamTy_of_uI_gt`,
     `not_lokt_revCtorTy_of_uI_gt`, `exists_lokt_famTyT_iff_revBaseSortLe`)**: if
     `N < evalTotal σ R.uI`, then the canonical Π-typings of `(revFamM R.I).mtype` and
     `revCtorTy R.f R.I` have `boundTySort σ > N`, so `∀ K', ¬ LOKt σ N K' d`.

3. **§3 What concludes `TwinConvAt4OvershootK` (and from which premises) vs. what is defined only**:
   - **§3.1 Internal injectivity in `R.E` (not `R.twin₁`)**:
     `RevEnv.rev_inj_internal_overshootK` and `RevEnv.rev_inj_internal_at4_overshootK` conclude
     `TwinConvAt4OvershootK R.E n σ Γ x x' R.I` (in the source environment `R.E`, using an
     off-diagonal ι step at `R.f + 2`) **from premises** `hR : RevSortLe σ 4 R`,
     `hx : HasTyT R.E n Γ x R.I`, `hx' : HasTyT R.E n Γ x' R.I`,
     `hc : TyConvT R.E n Γ (R.revFamApp x) (R.revFamApp x')`, and their `LOK` bounds `h1`, `h2`, `h3`
     (specialized at `riRevEnv` in `ri_inj_internal_at4_overshootK` and at `Nat`-indexed `RevEnv` in
     `RevEnv.rev_inj_internal_at4_overshootK_of_natConst`).
     `RevEnv.twinIdxConv_overshootK` and `RevEnv.twinIdxConv_at4_overshootK` take
     `hTwin : TwinConvAt4OvershootK R.twin₁ n σ Γ (tr R.f R.I x) (tr R.f R.I x') R.I` as a **premise**
     and transport it to `R.E` with `DiagRecIota (R.f + 2)`.
   - **§3.2–§3.3 Twin family-row producer in `R.twin₁` (from an ANNOTATED copy conversion `ConvA` + `CtxWfA`)**:
     `RevEnv.revTwin₁A_famAppConvInj_overshootK` and `RevEnv.revTwin₁A_famAppConvInj_at4_overshootK`
     conclude `TwinConvAt4OvershootK R.twin₁ n σ (eraseCtx ΓA) (erase xA) (erase x'A) R.I` **from premises**:
     (a) annotated `E₀A`, `IA` erasing to `R.E₀`, `R.I` with `EnvClosedA E₀A`, `hclIA`, `hinstIA`,
     (b) annotated typing/LR validity `tIA`, `vIA` of `IA` and `EnvSemClauseAL` on base members `hbase`,
     (c) annotated context well-formedness `hΓA : CtxWfA (R.twin₁A E₀A IA) noIotaA n ΓA` with `LOKctxA σ 4 K hΓA`, and
     (d) annotated conversion `h : ConvA (R.twin₁A E₀A IA) noIotaA n ΓA (.app (.const R.f []) xA) (.app (.const R.f []) x'A) (.sort w)` with `LOKcA σ 4 K h`.
     `riRevTwin₁_famAppConvInj_at4_overshootK` discharges (a) and (b) at `riRevEnv`, still requiring
     the annotated `hΓA`, `hdΓA`, `h`, `hd`.
   - **§3.4 `RevTwinRowAtNOvershootK` / `RevTwinRowAt4OvershootK` — DEFINITION ONLY**:
     `RevTwinRowAtNOvershootK` and `RevTwinRowAt4OvershootK` state the unannotated ι-witness row
     property in `R.twin₁` starting from `hl : HasTyT E' n Γ (iotaLhsOf w) T` (`LOKt σ 4 K hl`, no
     `CtxWfT`). **No theorem in this module proves `RevTwinRowAt4OvershootK` or
     `RevTwinRowAtNOvershootK`** (neither generically nor at `riRevEnv` / `fooRevEnv`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Syn.FamApp.Rev

open Rcic.Declarative
open Rcic.Declarative.Ann
open Rcic.Declarative.Ann.Lok
open Rcic.F3
open Rcic.F3.PSet
open Rcic.Syn.ClassC
open Rcic.Syn.FamApp.RevTwin

/-! ## §1 Sort/Π height vs. Constant-instance ceiling & `TwinConvAtNOvershootK` / `TwinConvAt4OvershootK` -/

/-- Maximum evaluated level in a constant's level-argument list. -/
def boundLevels (σ : Nat → Nat) : List Level → Nat
  | [] => 0
  | l :: ls => max (evalTotal σ l) (boundLevels σ ls)

theorem levelsOK_of_boundLevels_le (σ : Nat → Nat) (ls : List Level) (M : Nat)
    (h : boundLevels σ ls ≤ M) : LevelsOK σ M ls := by
  induction ls with
  | nil => intro l hl; cases hl
  | cons l ls ih =>
      simp only [boundLevels, Nat.max_le] at h
      intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact h.1
      · exact ih h.2 l' hl'

theorem boundLevels_le_of_levelsOK (σ : Nat → Nat) (ls : List Level) (M : Nat)
    (h : LevelsOK σ M ls) : boundLevels σ ls ≤ M := by
  induction ls with
  | nil => exact Nat.zero_le M
  | cons l ls ih =>
      simp only [boundLevels, Nat.max_le]
      exact ⟨h l (List.Mem.head _), ih (fun l' hl' => h l' (List.Mem.tail _ hl'))⟩

theorem levelsOK_mono {σ : Nat → Nat} {M M' : Nat} {ls : List Level}
    (hM : M ≤ M') (h : LevelsOK σ M ls) : LevelsOK σ M' ls :=
  fun l hl => Nat.le_trans (h l hl) hM

mutual
/-- Minimum sort/Π height `N` required by a typing derivation `d` under valuation `σ`. -/
def boundTySort {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → Nat
  | _, _, _, .sort _ l => evalTotal σ l + 1
  | _, _, _, .bvar _ _ _ _ => 0
  | _, _, _, .const _ _ _ _ _ _ _ => 0
  | _, _, _, .pi _ _ u _ v hA hB =>
      max (max (evalTotal σ u) (evalTotal σ v)) (max (boundTySort σ hA) (boundTySort σ hB))
  | _, _, _, .lam _ _ _ _ _ hA hb => max (boundTySort σ hA) (boundTySort σ hb)
  | _, _, _, .app _ _ _ _ _ hf ha => max (boundTySort σ hf) (boundTySort σ ha)
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb =>
      max (boundTySort σ hA) (max (boundTySort σ hv) (boundTySort σ hb))
  | _, _, _, .lit _ _ _ hexp => boundTySort σ hexp
  | _, _, _, .conv _ _ _ _ _ h hc => max (boundTySort σ h) (boundConvSort σ hc)

/-- Minimum sort/Π height `N` required by a conversion derivation `c` under valuation `σ`. -/
def boundConvSort {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) :
    {Γ : LCtx} → {a b A : Expr Nat} → ConvT E n Γ a b A → Nat
  | _, _, _, _, .refl _ _ _ h => boundTySort σ h
  | _, _, _, _, .symm _ _ _ _ h => boundConvSort σ h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => max (boundConvSort σ h1) (boundConvSort σ h2)
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha =>
      max (boundTySort σ hA) (max (boundTySort σ hb) (boundTySort σ ha))
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb =>
      max (boundTySort σ hA) (max (boundTySort σ hv) (boundTySort σ hb))
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => boundTySort σ hv
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => boundTySort σ hb
  | _, _, _, _, .iota _ _ _ _ _ hl hr => max (boundTySort σ hl) (boundTySort σ hr)
  | _, _, _, _, .lit _ _ _ _ _ hexp => boundTySort σ hexp
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => max (boundConvSort σ h1) (boundConvSort σ h2)
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => max (boundConvSort σ hA) (boundConvSort σ hb)
  | _, _, _, _, .pi _ _ _ _ _ u v hA hB =>
      max (max (evalTotal σ u) (evalTotal σ v)) (max (boundConvSort σ hA) (boundConvSort σ hB))
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb =>
      max (boundConvSort σ hA) (max (boundConvSort σ hv) (boundConvSort σ hb))
  | _, _, _, _, .sorts _ l1 _ _ => evalTotal σ l1 + 1
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ => 0
  | _, _, _, _, .eta _ _ _ _ h => boundTySort σ h
  | _, _, _, _, .irr _ _ _ _ hP hp hq =>
      max (boundTySort σ hP) (max (boundTySort σ hp) (boundTySort σ hq))
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => max (boundConvSort σ h) (boundConvSort σ hA)
end

mutual
/-- Maximum constant-instance level occurring anywhere in a typing derivation `d` under `σ`. -/
def boundTyConst {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → Nat
  | _, _, _, .sort _ _ => 0
  | _, _, _, .bvar _ _ _ _ => 0
  | _, _, _, .const _ _ ls _ _ _ _ => boundLevels σ ls
  | _, _, _, .pi _ _ _ _ _ hA hB => max (boundTyConst σ hA) (boundTyConst σ hB)
  | _, _, _, .lam _ _ _ _ _ hA hb => max (boundTyConst σ hA) (boundTyConst σ hb)
  | _, _, _, .app _ _ _ _ _ hf ha => max (boundTyConst σ hf) (boundTyConst σ ha)
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb =>
      max (boundTyConst σ hA) (max (boundTyConst σ hv) (boundTyConst σ hb))
  | _, _, _, .lit _ _ _ hexp => boundTyConst σ hexp
  | _, _, _, .conv _ _ _ _ _ h hc => max (boundTyConst σ h) (boundConvConst σ hc)

/-- Maximum constant-instance level occurring anywhere in a conversion derivation `c` under `σ`. -/
def boundConvConst {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) :
    {Γ : LCtx} → {a b A : Expr Nat} → ConvT E n Γ a b A → Nat
  | _, _, _, _, .refl _ _ _ h => boundTyConst σ h
  | _, _, _, _, .symm _ _ _ _ h => boundConvConst σ h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => max (boundConvConst σ h1) (boundConvConst σ h2)
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha =>
      max (boundTyConst σ hA) (max (boundTyConst σ hb) (boundTyConst σ ha))
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb =>
      max (boundTyConst σ hA) (max (boundTyConst σ hv) (boundTyConst σ hb))
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => boundTyConst σ hv
  | _, _, _, _, .delta _ _ ls _ _ _ _ _ _ _ hb => max (boundLevels σ ls) (boundTyConst σ hb)
  | _, _, _, _, .iota _ _ _ _ _ hl hr => max (boundTyConst σ hl) (boundTyConst σ hr)
  | _, _, _, _, .lit _ _ _ _ _ hexp => boundTyConst σ hexp
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => max (boundConvConst σ h1) (boundConvConst σ h2)
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => max (boundConvConst σ hA) (boundConvConst σ hb)
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => max (boundConvConst σ hA) (boundConvConst σ hB)
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb =>
      max (boundConvConst σ hA) (max (boundConvConst σ hv) (boundConvConst σ hb))
  | _, _, _, _, .sorts _ _ _ _ => 0
  | _, _, _, _, .consts _ _ ls ls' _ _ _ _ _ _ => max (boundLevels σ ls) (boundLevels σ ls')
  | _, _, _, _, .eta _ _ _ _ h => boundTyConst σ h
  | _, _, _, _, .irr _ _ _ _ hP hp hq =>
      max (boundTyConst σ hP) (max (boundTyConst σ hp) (boundTyConst σ hq))
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => max (boundConvConst σ h) (boundConvConst σ hA)
end

mutual
/-- Monotonicity of `LOKt` in both the sort height `N` and the constant-instance ceiling `K`. -/
theorem lokt_mono {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N N' : Nat} {K K' : Nat → Nat}
    (hN : N ≤ N') (hK : ∀ r, K r ≤ K' r) :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) → LOKt σ N K d → LOKt σ N' K' d
  | _, _, _, .sort _ _, h => Nat.le_trans h hN
  | _, _, _, .bvar _ _ _ _, _ => trivial
  | _, _, _, .const _ r _ _ _ _ _, h => levelsOK_mono (hK r) h
  | _, _, _, .pi _ _ _ _ _ hA hB, h =>
      ⟨Nat.le_trans h.1 hN, Nat.le_trans h.2.1 hN, lokt_mono hN hK hA h.2.2.1, lokt_mono hN hK hB h.2.2.2⟩
  | _, _, _, .lam _ _ _ _ _ hA hb, h => ⟨lokt_mono hN hK hA h.1, lokt_mono hN hK hb h.2⟩
  | _, _, _, .app _ _ _ _ _ hf ha, h => ⟨lokt_mono hN hK hf h.1, lokt_mono hN hK ha h.2⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb, h =>
      ⟨lokt_mono hN hK hA h.1, lokt_mono hN hK hv h.2.1, lokt_mono hN hK hb h.2.2⟩
  | _, _, _, .lit _ _ _ hexp, h => lokt_mono hN hK hexp h
  | _, _, _, .conv _ _ _ _ _ h hc, hl => ⟨lokt_mono hN hK h hl.1, lokc_mono hN hK hc hl.2⟩

/-- Monotonicity of `LOKc` in both the sort height `N` and the constant-instance ceiling `K`. -/
theorem lokc_mono {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N N' : Nat} {K K' : Nat → Nat}
    (hN : N ≤ N') (hK : ∀ r, K r ≤ K' r) :
    {Γ : LCtx} → {a b A : Expr Nat} → (c : ConvT E n Γ a b A) → LOKc σ N K c → LOKc σ N' K' c
  | _, _, _, _, .refl _ _ _ h, hl => lokt_mono hN hK h hl
  | _, _, _, _, .symm _ _ _ _ h, hl => lokc_mono hN hK h hl
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, hl =>
      ⟨lokc_mono hN hK h1 hl.1, lokc_mono hN hK h2 hl.2⟩
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha, hl =>
      ⟨lokt_mono hN hK hA hl.1, lokt_mono hN hK hb hl.2.1, lokt_mono hN hK ha hl.2.2⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb, hl =>
      ⟨lokt_mono hN hK hA hl.1, lokt_mono hN hK hv hl.2.1, lokt_mono hN hK hb hl.2.2⟩
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv, hl => lokt_mono hN hK hv hl
  | _, _, _, _, .delta _ r _ _ _ _ _ _ _ _ hb, hl =>
      ⟨levelsOK_mono (hK r) hl.1, lokt_mono hN hK hb hl.2⟩
  | _, _, _, _, .iota _ _ _ _ _ hl hr, h =>
      ⟨lokt_mono hN hK hl h.1, lokt_mono hN hK hr h.2⟩
  | _, _, _, _, .lit _ _ _ _ _ hexp, hl => lokt_mono hN hK hexp hl
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, hl =>
      ⟨lokc_mono hN hK h1 hl.1, lokc_mono hN hK h2 hl.2⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb, hl =>
      ⟨lokc_mono hN hK hA hl.1, lokc_mono hN hK hb hl.2⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, hl =>
      ⟨Nat.le_trans hl.1 hN, Nat.le_trans hl.2.1 hN, lokc_mono hN hK hA hl.2.2.1, lokc_mono hN hK hB hl.2.2.2⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb, hl =>
      ⟨lokc_mono hN hK hA hl.1, lokc_mono hN hK hv hl.2.1, lokc_mono hN hK hb hl.2.2⟩
  | _, _, _, _, .sorts _ _ _ _, hl => Nat.le_trans hl hN
  | _, _, _, _, .consts _ r _ _ _ _ _ _ _ _, hl =>
      ⟨levelsOK_mono (hK r) hl.1, levelsOK_mono (hK r) hl.2⟩
  | _, _, _, _, .eta _ _ _ _ h, hl => lokt_mono hN hK h hl
  | _, _, _, _, .irr _ _ _ _ hP hp hq, hl =>
      ⟨lokt_mono hN hK hP hl.1, lokt_mono hN hK hp hl.2.1, lokt_mono hN hK hq hl.2.2⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, hl =>
      ⟨lokc_mono hN hK h hl.1, lokc_mono hN hK hA hl.2⟩
end

/-- Monotonicity of `LOKtc` in both `N` and `K`. -/
theorem loktc_mono {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N N' : Nat} {K K' : Nat → Nat}
    (hN : N ≤ N') (hK : ∀ r, K r ≤ K' r) :
    {Γ : LCtx} → {A B : Expr Nat} → (hc : TyConvT E n Γ A B) → LOKtc σ N K hc → LOKtc σ N' K' hc
  | _, _, _, .refl _ _, _ => by simp only [LOKtc]
  | _, _, _, .of _ _ _ _ h, hl => by simp only [LOKtc] at hl ⊢; exact lokc_mono hN hK h hl
  | _, _, _, .trans _ _ _ _ h1 h2, hl => by
      simp only [LOKtc] at hl ⊢
      exact ⟨loktc_mono hN hK h1 hl.1, loktc_mono hN hK h2 hl.2⟩

mutual
/-- `LOKt σ N K d` implies `boundTySort σ d ≤ N`. -/
theorem boundTySort_le_of_lokt {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat} :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) → LOKt σ N K d → boundTySort σ d ≤ N
  | _, _, _, .sort _ _, h => h
  | _, _, _, .bvar _ _ _ _, _ => Nat.zero_le N
  | _, _, _, .const _ _ _ _ _ _ _, _ => Nat.zero_le N
  | _, _, _, .pi _ _ _ _ _ hA hB, h => by
      simp only [boundTySort, Nat.max_le]
      exact ⟨⟨h.1, h.2.1⟩, ⟨boundTySort_le_of_lokt hA h.2.2.1, boundTySort_le_of_lokt hB h.2.2.2⟩⟩
  | _, _, _, .lam _ _ _ _ _ hA hb, h => by
      simp only [boundTySort, Nat.max_le]
      exact ⟨boundTySort_le_of_lokt hA h.1, boundTySort_le_of_lokt hb h.2⟩
  | _, _, _, .app _ _ _ _ _ hf ha, h => by
      simp only [boundTySort, Nat.max_le]
      exact ⟨boundTySort_le_of_lokt hf h.1, boundTySort_le_of_lokt ha h.2⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb, h => by
      simp only [boundTySort, Nat.max_le]
      exact ⟨boundTySort_le_of_lokt hA h.1, boundTySort_le_of_lokt hv h.2.1, boundTySort_le_of_lokt hb h.2.2⟩
  | _, _, _, .lit _ _ _ hexp, h => boundTySort_le_of_lokt hexp h
  | _, _, _, .conv _ _ _ _ _ h hc, hl => by
      simp only [boundTySort, Nat.max_le]
      exact ⟨boundTySort_le_of_lokt h hl.1, boundConvSort_le_of_lokc hc hl.2⟩

/-- `LOKc σ N K c` implies `boundConvSort σ c ≤ N`. -/
theorem boundConvSort_le_of_lokc {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat} :
    {Γ : LCtx} → {a b A : Expr Nat} → (c : ConvT E n Γ a b A) → LOKc σ N K c → boundConvSort σ c ≤ N
  | _, _, _, _, .refl _ _ _ h, hl => boundTySort_le_of_lokt h hl
  | _, _, _, _, .symm _ _ _ _ h, hl => boundConvSort_le_of_lokc h hl
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, hl => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨boundConvSort_le_of_lokc h1 hl.1, boundConvSort_le_of_lokc h2 hl.2⟩
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha, hl => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨boundTySort_le_of_lokt hA hl.1, boundTySort_le_of_lokt hb hl.2.1, boundTySort_le_of_lokt ha hl.2.2⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb, hl => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨boundTySort_le_of_lokt hA hl.1, boundTySort_le_of_lokt hv hl.2.1, boundTySort_le_of_lokt hb hl.2.2⟩
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv, hl => boundTySort_le_of_lokt hv hl
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb, hl => boundTySort_le_of_lokt hb hl.2
  | _, _, _, _, .iota _ _ _ _ _ hl hr, h => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨boundTySort_le_of_lokt hl h.1, boundTySort_le_of_lokt hr h.2⟩
  | _, _, _, _, .lit _ _ _ _ _ hexp, hl => boundTySort_le_of_lokt hexp hl
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, hl => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨boundConvSort_le_of_lokc h1 hl.1, boundConvSort_le_of_lokc h2 hl.2⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb, hl => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨boundConvSort_le_of_lokc hA hl.1, boundConvSort_le_of_lokc hb hl.2⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, hl => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨⟨hl.1, hl.2.1⟩, ⟨boundConvSort_le_of_lokc hA hl.2.2.1, boundConvSort_le_of_lokc hB hl.2.2.2⟩⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb, hl => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨boundConvSort_le_of_lokc hA hl.1, boundConvSort_le_of_lokc hv hl.2.1, boundConvSort_le_of_lokc hb hl.2.2⟩
  | _, _, _, _, .sorts _ _ _ _, hl => hl
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _, _ => Nat.zero_le N
  | _, _, _, _, .eta _ _ _ _ h, hl => boundTySort_le_of_lokt h hl
  | _, _, _, _, .irr _ _ _ _ hP hp hq, hl => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨boundTySort_le_of_lokt hP hl.1, boundTySort_le_of_lokt hp hl.2.1, boundTySort_le_of_lokt hq hl.2.2⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, hl => by
      simp only [boundConvSort, Nat.max_le]
      exact ⟨boundConvSort_le_of_lokc h hl.1, boundConvSort_le_of_lokc hA hl.2⟩
end

mutual
/-- `boundTySort σ d ≤ N` and `∀ r, boundTyConst σ d ≤ K r` give `LOKt σ N K d`. -/
theorem lokt_of_bounds {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat} :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) →
    boundTySort σ d ≤ N → (∀ r, boundTyConst σ d ≤ K r) → LOKt σ N K d
  | _, _, _, .sort _ _, hN, _ => hN
  | _, _, _, .bvar _ _ _ _, _, _ => trivial
  | _, _, _, .const _ r ls _ _ _ _, _, hK => levelsOK_of_boundLevels_le σ ls (K r) (hK r)
  | _, _, _, .pi _ _ _ _ _ hA hB, hN, hK => by
      simp only [boundTySort, Nat.max_le] at hN
      refine ⟨hN.1.1, hN.1.2, lokt_of_bounds hA hN.2.1 ?_, lokt_of_bounds hB hN.2.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
  | _, _, _, .lam _ _ _ _ _ hA hb, hN, hK => by
      simp only [boundTySort, Nat.max_le] at hN
      refine ⟨lokt_of_bounds hA hN.1 ?_, lokt_of_bounds hb hN.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
  | _, _, _, .app _ _ _ _ _ hf ha, hN, hK => by
      simp only [boundTySort, Nat.max_le] at hN
      refine ⟨lokt_of_bounds hf hN.1 ?_, lokt_of_bounds ha hN.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb, hN, hK => by
      simp only [boundTySort, Nat.max_le] at hN
      refine ⟨lokt_of_bounds hA hN.1 ?_, lokt_of_bounds hv hN.2.1 ?_, lokt_of_bounds hb hN.2.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (hK r)
  | _, _, _, .lit _ _ _ hexp, hN, hK => lokt_of_bounds hexp hN hK
  | _, _, _, .conv _ _ _ _ _ h hc, hN, hK => by
      simp only [boundTySort, Nat.max_le] at hN
      refine ⟨lokt_of_bounds h hN.1 ?_, lokc_of_bounds hc hN.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)

/-- `boundConvSort σ c ≤ N` and `∀ r, boundConvConst σ c ≤ K r` give `LOKc σ N K c`. -/
theorem lokc_of_bounds {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat} :
    {Γ : LCtx} → {a b A : Expr Nat} → (c : ConvT E n Γ a b A) →
    boundConvSort σ c ≤ N → (∀ r, boundConvConst σ c ≤ K r) → LOKc σ N K c
  | _, _, _, _, .refl _ _ _ h, hN, hK => lokt_of_bounds h hN hK
  | _, _, _, _, .symm _ _ _ _ h, hN, hK => lokc_of_bounds h hN hK
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨lokc_of_bounds h1 hN.1 ?_, lokc_of_bounds h2 hN.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨lokt_of_bounds hA hN.1 ?_, lokt_of_bounds hb hN.2.1 ?_, lokt_of_bounds ha hN.2.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (hK r)
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨lokt_of_bounds hA hN.1 ?_, lokt_of_bounds hv hN.2.1 ?_, lokt_of_bounds hb hN.2.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (hK r)
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv, hN, hK => lokt_of_bounds hv hN hK
  | _, _, _, _, .delta _ r ls _ _ _ _ _ _ _ hb, hN, hK =>
      ⟨levelsOK_of_boundLevels_le σ ls (K r) (Nat.le_trans (Nat.le_max_left _ _) (hK r)),
       lokt_of_bounds hb hN (fun r' => Nat.le_trans (Nat.le_max_right _ _) (hK r'))⟩
  | _, _, _, _, .iota _ _ _ _ _ hl hr, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨lokt_of_bounds hl hN.1 ?_, lokt_of_bounds hr hN.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
  | _, _, _, _, .lit _ _ _ _ _ hexp, hN, hK => lokt_of_bounds hexp hN hK
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨lokc_of_bounds h1 hN.1 ?_, lokc_of_bounds h2 hN.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨lokc_of_bounds hA hN.1 ?_, lokc_of_bounds hb hN.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨hN.1.1, hN.1.2, lokc_of_bounds hA hN.2.1 ?_, lokc_of_bounds hB hN.2.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨lokc_of_bounds hA hN.1 ?_, lokc_of_bounds hv hN.2.1 ?_, lokc_of_bounds hb hN.2.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (hK r)
  | _, _, _, _, .sorts _ _ _ _, hN, _ => hN
  | _, _, _, _, .consts _ r ls ls' _ _ _ _ _ _, _, hK =>
      ⟨levelsOK_of_boundLevels_le σ ls (K r) (Nat.le_trans (Nat.le_max_left _ _) (hK r)),
       levelsOK_of_boundLevels_le σ ls' (K r) (Nat.le_trans (Nat.le_max_right _ _) (hK r))⟩
  | _, _, _, _, .eta _ _ _ _ h, hN, hK => lokt_of_bounds h hN hK
  | _, _, _, _, .irr _ _ _ _ hP hp hq, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨lokt_of_bounds hP hN.1 ?_, lokt_of_bounds hp hN.2.1 ?_, lokt_of_bounds hq hN.2.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (hK r)
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, hN, hK => by
      simp only [boundConvSort, Nat.max_le] at hN
      refine ⟨lokc_of_bounds h hN.1 ?_, lokc_of_bounds hA hN.2 ?_⟩
      · intro r; exact Nat.le_trans (Nat.le_max_left _ _) (hK r)
      · intro r; exact Nat.le_trans (Nat.le_max_right _ _) (hK r)
end

theorem exists_lokt_iff_boundTySort_le {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat}
    {Γ : LCtx} {e A : Expr Nat} (d : HasTyT E n Γ e A) :
    (∃ K' : Nat → Nat, LOKt σ N K' d) ↔ boundTySort σ d ≤ N :=
  ⟨fun ⟨_, hl⟩ => boundTySort_le_of_lokt d hl,
   fun hN => ⟨fun _ => boundTyConst σ d, lokt_of_bounds d hN (fun _ => Nat.le_refl _)⟩⟩

theorem exists_lokc_iff_boundConvSort_le {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat}
    {Γ : LCtx} {a b A : Expr Nat} (c : ConvT E n Γ a b A) :
    (∃ K' : Nat → Nat, LOKc σ N K' c) ↔ boundConvSort σ c ≤ N :=
  ⟨fun ⟨_, hl⟩ => boundConvSort_le_of_lokc c hl,
   fun hN => ⟨fun _ => boundConvConst σ c, lokc_of_bounds c hN (fun _ => Nat.le_refl _)⟩⟩

/-- **Height-`N` twin conversion with arbitrary constant-instance overshoot `K'`**:
    a conversion `c : ConvT E_twin n Γ a b A` whose sort/Π levels stay `≤ N` (`LOKc σ N K' c` for
    some `K' : Nat → Nat`). -/
def TwinConvAtNOvershootK (E_twin : ResolvedEnv) (n : Nat) (σ : Nat → Nat) (N : Nat)
    (Γ : LCtx) (a b A : Expr Nat) : Prop :=
  ∃ (c : ConvT E_twin n Γ a b A) (K' : Nat → Nat), LOKc σ N K' c

/-- **Height-`4` twin conversion with arbitrary constant-instance overshoot `K'`**
    (matching `agy-pendwx` #8084 §5.5 `TwinConvAt4OvershootK`):
    a conversion `c : ConvT E_twin n Γ a b A` whose sort/Π levels stay `≤ 4` (`LOKc σ 4 K' c` for
    some `K' : Nat → Nat`). -/
def TwinConvAt4OvershootK (E_twin : ResolvedEnv) (n : Nat) (σ : Nat → Nat)
    (Γ : LCtx) (a b A : Expr Nat) : Prop :=
  ∃ (c : ConvT E_twin n Γ a b A) (K' : Nat → Nat), LOKc σ 4 K' c

theorem twinConvAt4OvershootK_eq_atN (E_twin : ResolvedEnv) (n : Nat) (σ : Nat → Nat)
    (Γ : LCtx) (a b A : Expr Nat) :
    TwinConvAt4OvershootK E_twin n σ Γ a b A = TwinConvAtNOvershootK E_twin n σ 4 Γ a b A := rfl

theorem twinConvAtNOvershootK_iff (E_twin : ResolvedEnv) (n : Nat) (σ : Nat → Nat) (N : Nat)
    (Γ : LCtx) (a b A : Expr Nat) :
    TwinConvAtNOvershootK E_twin n σ N Γ a b A ↔
      ∃ c : ConvT E_twin n Γ a b A, boundConvSort σ c ≤ N :=
  ⟨fun ⟨c, _, hl⟩ => ⟨c, boundConvSort_le_of_lokc c hl⟩,
   fun ⟨c, hN⟩ => ⟨c, (exists_lokc_iff_boundConvSort_le c).mpr hN⟩⟩

theorem twinConvAt4OvershootK_iff (E_twin : ResolvedEnv) (n : Nat) (σ : Nat → Nat)
    (Γ : LCtx) (a b A : Expr Nat) :
    TwinConvAt4OvershootK E_twin n σ Γ a b A ↔
      ∃ c : ConvT E_twin n Γ a b A, boundConvSort σ c ≤ 4 :=
  twinConvAtNOvershootK_iff E_twin n σ 4 Γ a b A

theorem twinConvAtNOvershootK_mono {E_twin : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N N' : Nat}
    (hN : N ≤ N') {Γ : LCtx} {a b A : Expr Nat}
    (h : TwinConvAtNOvershootK E_twin n σ N Γ a b A) :
    TwinConvAtNOvershootK E_twin n σ N' Γ a b A := by
  obtain ⟨c, K', hl⟩ := h
  exact ⟨c, K', lokc_mono hN (fun _ => Nat.le_refl _) c hl⟩

/-- **Semantic bridge at height 4 (`den_equiv_of_twinConvAt4OvershootK`)**:
    In any height-4 set model `mkM P μ` (`P : Premises4`), if `E_twin` satisfies `EnvSound` at
    every constant-instance ceiling `K'` (`glm-f3eq`'s `envSound_twin₁` has this exact polymorphism),
    then `TwinConvAt4OvershootK E_twin n σ Γ a b A` implies `⟦a⟧ ≈ ⟦b⟧` and `⟦a⟧ ∈ Ed ⟦A⟧` at every
    fitting environment `ρ`. -/
theorem den_equiv_of_twinConvAt4OvershootK (P : Premises4)
    {μ : Nat → List Nat → PSet.{4}} {E_twin : ResolvedEnv} {n : Nat} {σ : Nat → Nat}
    {Γ : LCtx} {a b A : Expr Nat}
    (hTwinSound : ∀ K' : Nat → Nat, EnvSound (mkM P μ) σ K' E_twin n)
    (hConv : TwinConvAt4OvershootK E_twin n σ Γ a b A)
    (ρ : Nat → PSet.{4}) (hfit : Fits (mkM P μ) σ Γ ρ) :
    Equiv (den (mkM P μ) σ ρ a) (den (mkM P μ) σ ρ b) ∧
      den (mkM P μ) σ ρ a ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ A) := by
  obtain ⟨c, K', hlc⟩ := hConv
  exact sound_conv (P.good (mkM P μ) rfl) (hTwinSound K') c hlc ρ hfit

/-- Context-fitting invariance under `trCtx f I`: if `tr f I` preserves denotations in `M`, then
    `Fits M σ (trCtx f I Γ) ρ ↔ Fits M σ Γ ρ`. -/
theorem fits_trCtx_iff_of_den_tr {M : Interp.{4}} {σ : Nat → Nat} {f : Nat} {I : Expr Nat}
    (hden_tr : ∀ (e : Expr Nat) (ρ' : Nat → PSet.{4}), Equiv (den M σ ρ' (tr f I e)) (den M σ ρ' e)) :
    ∀ (Γ : LCtx) (ρ : Nat → PSet.{4}), Fits M σ (trCtx f I Γ) ρ ↔ Fits M σ Γ ρ
  | [], _ => Iff.rfl
  | .assumption A :: Γ, ρ => by
      simp only [trCtx, trDecl, Fits]
      have ih := fits_trCtx_iff_of_den_tr hden_tr Γ (tl ρ)
      have hA : Equiv (Ed M (den M σ (tl ρ) (tr f I A))) (Ed M (den M σ (tl ρ) A)) :=
        ed_congr M (hden_tr A (tl ρ))
      exact ⟨fun ⟨h1, h2⟩ => ⟨ih.mp h1, mem_congr_right hA h2⟩,
             fun ⟨h1, h2⟩ => ⟨ih.mpr h1, mem_congr_right hA.symm h2⟩⟩
  | .letBinding A v :: Γ, ρ => by
      simp only [trCtx, trDecl, Fits]
      have ih := fits_trCtx_iff_of_den_tr hden_tr Γ (tl ρ)
      have hA : Equiv (Ed M (den M σ (tl ρ) (tr f I A))) (Ed M (den M σ (tl ρ) A)) :=
        ed_congr M (hden_tr A (tl ρ))
      have hv : Equiv (den M σ (tl ρ) (tr f I v)) (den M σ (tl ρ) v) := hden_tr v (tl ρ)
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨ih.mp h1, mem_congr_right hA h2, h3.trans hv⟩,
             fun ⟨h1, h2, h3⟩ => ⟨ih.mpr h1, mem_congr_right hA.symm h2, h3.trans hv.symm⟩⟩

/-- **Discharged B1 semantic index agreement from `TwinConvAt4OvershootK` in `trCtx`**:
    if `TwinConvAt4OvershootK E_twin n σ (trCtx f I Γ) (tr f I a) (tr f I b) I` holds and `tr f I`
    preserves denotations (`den_tr` in `glm-f3eq`), then `⟦a⟧ ≈ ⟦b⟧` at every environment `ρ`
    fitting `Γ`. -/
theorem den_equiv_of_trTwinConvAt4OvershootK (P : Premises4)
    {μ : Nat → List Nat → PSet.{4}} {E_twin : ResolvedEnv} {n : Nat} {σ : Nat → Nat}
    {f : Nat} {I : Expr Nat} {Γ : LCtx} {a b : Expr Nat}
    (hTwinSound : ∀ K' : Nat → Nat, EnvSound (mkM P μ) σ K' E_twin n)
    (hden_tr : ∀ (e : Expr Nat) (ρ' : Nat → PSet.{4}),
      Equiv (den (mkM P μ) σ ρ' (tr f I e)) (den (mkM P μ) σ ρ' e))
    (hConv : TwinConvAt4OvershootK E_twin n σ (trCtx f I Γ) (tr f I a) (tr f I b) I)
    (ρ : Nat → PSet.{4}) (hfit : Fits (mkM P μ) σ Γ ρ) :
    Equiv (den (mkM P μ) σ ρ a) (den (mkM P μ) σ ρ b) := by
  have hfit' : Fits (mkM P μ) σ (trCtx f I Γ) ρ :=
    (fits_trCtx_iff_of_den_tr hden_tr Γ ρ).mpr hfit
  have htr := (den_equiv_of_twinConvAt4OvershootK P hTwinSound hConv ρ hfit').1
  exact (hden_tr a ρ).symm.trans (htr.trans (hden_tr b ρ))

/-! ## §2 Exact side condition on `R.uI` (`RevSortLe` / `RevBaseSortLe`) and refutation when `evalTotal σ R.uI > N` -/

mutual
/-- `hasTyTExt` preserves `LOKt` identically. -/
theorem lokt_hasTyTExt {E E' : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx} → {a A : Expr Nat} → (d : HasTyT E n Γ a A) →
    (LOKt σ N K (hasTyTExt hext d) ↔ LOKt σ N K d)
  | _, _, _, .bvar _ _ _ _ => Iff.rfl
  | _, _, _, .sort _ _ => Iff.rfl
  | _, _, _, .const _ _ _ _ _ _ _ => Iff.rfl
  | _, _, _, .app _ _ _ _ _ hf ha => by
      simp only [hasTyTExt, LOKt, lokt_hasTyTExt hext hf, lokt_hasTyTExt hext ha]
  | _, _, _, .lam _ _ _ _ _ hA hbody => by
      simp only [hasTyTExt, LOKt, lokt_hasTyTExt hext hA, lokt_hasTyTExt hext hbody]
  | _, _, _, .pi _ _ _ _ _ hA hB => by
      simp only [hasTyTExt, LOKt, lokt_hasTyTExt hext hA, lokt_hasTyTExt hext hB]
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => by
      simp only [hasTyTExt, LOKt, lokt_hasTyTExt hext hA, lokt_hasTyTExt hext hv, lokt_hasTyTExt hext hb]
  | _, _, _, .lit _ _ _ h => lokt_hasTyTExt hext h
  | _, _, _, .conv _ _ _ _ _ hA hc => by
      simp only [hasTyTExt, LOKt, lokt_hasTyTExt hext hA, lokc_convTExt hext hc]

/-- `convTExt` preserves `LOKc` identically. -/
theorem lokc_convTExt {E E' : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx} → {a b T : Expr Nat} → (c : ConvT E n Γ a b T) →
    (LOKc σ N K (convTExt hext c) ↔ LOKc σ N K c)
  | _, _, _, _, .refl _ _ _ hA => lokt_hasTyTExt hext hA
  | _, _, _, _, .symm _ _ _ _ h => lokc_convTExt hext h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => by
      simp only [convTExt, LOKc, lokc_convTExt hext h1, lokc_convTExt hext h2]
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg => by
      simp only [convTExt, LOKc, lokt_hasTyTExt hext hA, lokt_hasTyTExt hext hbody, lokt_hasTyTExt hext harg]
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb => by
      simp only [convTExt, LOKc, lokt_hasTyTExt hext hA, lokt_hasTyTExt hext hv, lokt_hasTyTExt hext hb]
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => lokt_hasTyTExt hext hv
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => by
      simp only [convTExt, LOKc, lokt_hasTyTExt hext hb]
  | _, _, _, _, .iota _ _ _ _ _ hl hr => by
      simp only [convTExt, LOKc, lokt_hasTyTExt hext hl, lokt_hasTyTExt hext hr]
  | _, _, _, _, .lit _ _ _ _ _ hexp => lokt_hasTyTExt hext hexp
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => by
      simp only [convTExt, LOKc, lokc_convTExt hext h1, lokc_convTExt hext h2]
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => by
      simp only [convTExt, LOKc, lokc_convTExt hext hA, lokc_convTExt hext hb]
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => by
      simp only [convTExt, LOKc, lokc_convTExt hext hA, lokc_convTExt hext hB]
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb => by
      simp only [convTExt, LOKc, lokc_convTExt hext hA, lokc_convTExt hext hv, lokc_convTExt hext hb]
  | _, _, _, _, .sorts _ _ _ _ => Iff.rfl
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ => Iff.rfl
  | _, _, _, _, .eta _ _ _ _ h => lokt_hasTyTExt hext h
  | _, _, _, _, .irr _ _ _ _ hP hp hq => by
      simp only [convTExt, LOKc, lokt_hasTyTExt hext hP, lokt_hasTyTExt hext hp, lokt_hasTyTExt hext hq]
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => by
      simp only [convTExt, LOKc, lokc_convTExt hext h, lokc_convTExt hext hA]
end

/-- **The exact side condition on a revealed-singleton base `B : RevBase` at sort height `N`**:
    1. `1 ≤ N` (so `Sort 0 : Sort 1` is within height `N`),
    2. `evalTotal σ B.uI ≤ N` (so `Π (_ : B.I), ...` has domain sort `≤ N`),
    3. `boundTySort σ B.hI ≤ N` (so the closed index type's own derivation `B.hI : HasTyT B.E₀ 0 [] B.I (.sort B.uI)` stays within sort height `N`). -/
def RevBaseSortLe (σ : Nat → Nat) (N : Nat) (B : RevBase) : Prop :=
  1 ≤ N ∧ evalTotal σ B.uI ≤ N ∧ boundTySort σ B.hI ≤ N

/-- **The exact side condition on `R : RevEnv` at sort height `N`**:
    `1 ≤ N`, `evalTotal σ R.uI ≤ N`, and there is a constant-instance ceiling `K_I` bounding
    `R.hIEB n Γ` across contexts (equivalently `boundTySort σ (R.hIEB n Γ) ≤ N` with uniform constant
    ceiling `K_I`). -/
def RevSortLe (σ : Nat → Nat) (N : Nat) (R : RevEnv) : Prop :=
  1 ≤ N ∧ evalTotal σ R.uI ≤ N ∧ ∃ K_I : Nat → Nat, ∀ (n : Nat) (Γ : LCtx), LOKt σ N K_I (R.hIEB n Γ)

/-- **Unconditional height-4 discharge at `riRevBase` / `riRevEnv`** (`I = Sort 0`, `uI = 1`):
    `evalTotal σ riRevEnv.uI = 1 ≤ 4` and `boundTySort σ riRevEnv.hI = 1 ≤ 4` for **every** `σ`. -/
theorem revBaseSortLe_riRevBase (σ : Nat → Nat) {N : Nat} (hN : 1 ≤ N) :
    RevBaseSortLe σ N riRevBase := by
  refine ⟨hN, ?_, ?_⟩
  · show 0 + 1 ≤ N; omega
  · show 0 + 1 ≤ N; omega

theorem revSortLe_riRevEnv (σ : Nat → Nat) {N : Nat} (hN : 1 ≤ N) :
    RevSortLe σ N riRevEnv := by
  refine ⟨hN, ?_, ⟨fun _ => 0, fun n Γ => ?_⟩⟩
  · show 0 + 1 ≤ N; omega
  · rw [riRevEnv_hIEB_eq]
    simp only [LOKt, evalTotal]
    omega

theorem revSortLe_four_riRevEnv (σ : Nat → Nat) :
    RevSortLe σ 4 riRevEnv :=
  revSortLe_riRevEnv σ (by decide)

/-- `hasTyTWeakenClosedB` on `natConstTyT` is definitionally `natConstTyT` in every context `Γ'`. -/
theorem hasTyTWeakenClosedB_natConst {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    (h : E.members 0 = some natFamMember) (Γ' : LCtx) :
    RevEnv.hasTyTWeakenClosedB hcl rfl rfl (natConstTyT (E := E) (n := n) (Γ := []) h) Γ' =
      natConstTyT (E := E) (n := n) (Γ := Γ') h := by
  induction Γ' with
  | nil => rfl
  | cons d Γ ih =>
      unfold RevEnv.hasTyTWeakenClosedB
      rw [ih]
      rfl

/-- **Unconditional height-`N` discharge for any `Nat`-indexed `B : RevBase`**
    (`B.uI = .succ .zero`, `boundTySort σ B.hI = 0`, such as `glm-f3eq`'s
    `RcicF3EqFooRev.fooRevBase`, where both hypotheses are `rfl`):
    `evalTotal σ B.uI = 1 ≤ N` and `boundTySort σ B.hI = 0 ≤ N` for **every** `σ`. -/
theorem revBaseSortLe_of_natConst (B : RevBase) {σ : Nat → Nat}
    (huI : B.uI = .succ .zero) (hsort : boundTySort σ B.hI = 0) {N : Nat} (hN : 1 ≤ N) :
    RevBaseSortLe σ N B := by
  refine ⟨hN, ?_, ?_⟩
  · rw [huI]; show 0 + 1 ≤ N; omega
  · rw [hsort]; exact Nat.zero_le N

theorem revBaseSortLe_four_of_natConst (B : RevBase) {σ : Nat → Nat}
    (huI : B.uI = .succ .zero) (hsort : boundTySort σ B.hI = 0) :
    RevBaseSortLe σ 4 B :=
  revBaseSortLe_of_natConst B huI hsort (by decide)

/-- Any `R : RevEnv` whose index type is `.const 0 []` (`Nat : Sort 1`, typed by `natConstTyT`,
    such as `glm-f3eq`'s `RcicF3EqFooRev.fooRevEnv`, where `hmem`, `hI`, `huI`, `hhI` are `rfl` /
    `HEq.rfl`) satisfies `RevSortLe σ N R` for every `N ≥ 1` (in particular `N = 4`) and every `σ`. -/
theorem revSortLe_of_natConst (R : RevEnv)
    (hmem : R.E₀.members 0 = some natFamMember)
    (hI : R.I = .const 0 []) (huI : R.uI = .succ .zero)
    (hhI : HEq R.hI (natConstTyT (E := R.E₀) (n := 0) (Γ := []) hmem))
    (σ : Nat → Nat) {N : Nat} (hN : 1 ≤ N) :
    RevSortLe σ N R := by
  rcases R with ⟨⟨E₀, hW₀, hP₀, f, hf0, hf2, hlow, I, uI, dI, hclI, hlvlI, huI_p⟩,
    E, hW, hbase_eq, hEf, hEf1, hEf2, habove⟩
  dsimp at hmem hI huI hhI
  subst hI; subst huI
  cases hhI
  refine ⟨hN, by show 0 + 1 ≤ N; omega, ⟨fun _ => 0, fun n Γ => ?_⟩⟩
  change LOKt σ N (fun _ => 0)
    (RevEnv.hasTyTWeakenClosedB _ (hclI 0) rfl
      (natConstTyT (E := E) (n := n) (Γ := []) _) Γ)
  rw [hasTyTWeakenClosedB_natConst]
  simp only [natConstTyT, LOKt, levelsOK_nil]

/-- **Exact refutation when `evalTotal σ uI > N` (`not_lokt_revFamTy_of_uI_gt`)**:
    if the index type's sort `uI` evaluates above `N` (e.g. `4 < evalTotal σ R.uI`), then the
    canonical Π-typing of the family type `Π (_ : I), Sort 0` has `boundTySort σ > N` and fails
    `LOKt σ N K'` for **every** constant-instance ceiling `K'`. -/
theorem not_lokt_revFamTy_of_uI_gt {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat}
    {Γ : LCtx} {I : Expr Nat} {uI : Level}
    (hI : HasTyT E n Γ I (.sort uI)) (huI : N < evalTotal σ uI) :
    N < boundTySort σ (HasTyT.pi Γ I uI (.sort .zero) (.succ .zero) hI (.sort (.assumption I :: Γ) .zero)) ∧
      ∀ K' : Nat → Nat,
        ¬ LOKt σ N K' (HasTyT.pi Γ I uI (.sort .zero) (.succ .zero) hI (.sort (.assumption I :: Γ) .zero)) := by
  refine ⟨?_, fun _ hlok => Nat.not_le_of_gt huI hlok.1⟩
  simp only [boundTySort]
  exact Nat.lt_of_lt_of_le huI (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))

/-- **Exact refutation on the constructor/axiom Π-type `Π (x : I), F x` when `evalTotal σ uI > N`**:
    any canonical Π-typing `.pi Γ I uI B .zero hI hB` fails `LOKt σ N K'` for every `K'` whenever
    `N < evalTotal σ uI`. -/
theorem not_lokt_revCtorTy_of_uI_gt {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat}
    {Γ : LCtx} {I B : Expr Nat} {uI : Level}
    (hI : HasTyT E n Γ I (.sort uI)) (hB : HasTyT E n (.assumption I :: Γ) B (.sort .zero))
    (huI : N < evalTotal σ uI) :
    N < boundTySort σ (HasTyT.pi Γ I uI B .zero hI hB) ∧
      ∀ K' : Nat → Nat, ¬ LOKt σ N K' (HasTyT.pi Γ I uI B .zero hI hB) := by
  refine ⟨?_, fun _ hlok => Nat.not_le_of_gt huI hlok.1⟩
  simp only [boundTySort]
  exact Nat.lt_of_lt_of_le huI (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))

/-- Specializing `not_lokt_revFamTy_of_uI_gt` to `B.famTyT` on any `B : RevBase`:
    `∃ K', LOKt σ N K' B.famTyT` holds **if and only if** `RevBaseSortLe σ N B`. -/
theorem exists_lokt_famTyT_iff_revBaseSortLe {σ : Nat → Nat} {N : Nat} (B : RevBase) :
    (∃ K' : Nat → Nat, LOKt σ N K' B.famTyT) ↔ RevBaseSortLe σ N B := by
  rw [exists_lokt_iff_boundTySort_le B.famTyT]
  have hI_ext : boundTySort σ (hasTyTExt B.famEnv_ext B.hI) = boundTySort σ B.hI := by
    apply Nat.le_antisymm
    · rw [← exists_lokt_iff_boundTySort_le]
      obtain ⟨K', hK'⟩ := (exists_lokt_iff_boundTySort_le B.hI).mpr (Nat.le_refl _)
      exact ⟨K', (lokt_hasTyTExt B.famEnv_ext B.hI).mpr hK'⟩
    · rw [← exists_lokt_iff_boundTySort_le]
      obtain ⟨K', hK'⟩ := (exists_lokt_iff_boundTySort_le (hasTyTExt B.famEnv_ext B.hI)).mpr (Nat.le_refl _)
      exact ⟨K', (lokt_hasTyTExt B.famEnv_ext B.hI).mp hK'⟩
  unfold RevBase.famTyT RevBaseSortLe
  simp only [boundTySort, evalTotal, hI_ext, Nat.max_le, Nat.zero_add]
  exact ⟨fun ⟨⟨huI, h1⟩, ⟨hI, _⟩⟩ => ⟨h1, huI, hI⟩,
         fun ⟨h1, huI, hI⟩ => ⟨⟨huI, h1⟩, ⟨hI, h1⟩⟩⟩

/-! ## §3 Generic `R : RevEnv` height-`N` / height-`4` twin conversion and internal injectivity -/

section GenericHeight4

variable (R : RevEnv) {n : Nat} {Γ : LCtx} {σ : Nat → Nat} {K : Nat → Nat}

/-- **Generic height-`N` internal injectivity with `K'` overshoot (`rev_inj_internal_overshootK`)**:
    For ANY `R : RevEnv` satisfying `RevSortLe σ N R`, if `x, x' : R.I` and `F x ≡* F x'` have
    derivations at sort height `N` and constant ceiling `K`, then `R.rev_inj_internalB hx hx' hc`
    is a conversion `ConvT R.E n Γ x x' R.I` at the **same sort height `N`** with some bumped
    constant ceiling `K'`. -/
theorem RevEnv.rev_inj_internal_overshootK {N : Nat} (hR : RevSortLe σ N R)
    {x x' : Expr Nat} (hx : HasTyT R.E n Γ x R.I) (hx' : HasTyT R.E n Γ x' R.I)
    (hc : TyConvT R.E n Γ (R.revFamApp x) (R.revFamApp x'))
    (h1 : LOKt σ N K hx) (h2 : LOKt σ N K hx') (h3 : LOKtc σ N K hc) :
    ∃ K' : Nat → Nat, LOKc σ N K' (R.rev_inj_internalB hx hx' hc) := by
  obtain ⟨_, huIN, K_I, hKI⟩ := hR
  let K' : Nat → Nat := fun r => max (K r) (max (K_I r) (evalTotal σ R.uI))
  have hK_le : ∀ r, K r ≤ K' r := fun r => Nat.le_max_left _ _
  have hKI_le : ∀ r, K_I r ≤ K' r := fun r => Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have huI_le : evalTotal σ R.uI ≤ K' (R.f + 2) :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact ⟨K', R.rev_inj_internalB_lok hx hx' hc huIN huI_le
    (fun Γ' => lokt_mono (Nat.le_refl N) hKI_le _ (hKI n Γ'))
    (lokt_mono (Nat.le_refl N) hK_le hx h1)
    (lokt_mono (Nat.le_refl N) hK_le hx' h2)
    (loktc_mono (Nat.le_refl N) hK_le hc h3)⟩

/-- **Generic height-`4` internal injectivity with `K'` overshoot (`rev_inj_internal_at4_overshootK`)**:
    Under `RevSortLe σ 4 R`, `F x ≡* F x'` at height 4 gives `TwinConvAt4OvershootK R.E n σ Γ x x' R.I`
    via `R.rev_inj_internalB hx hx' hc`. -/
theorem RevEnv.rev_inj_internal_at4_overshootK (hR : RevSortLe σ 4 R)
    {x x' : Expr Nat} (hx : HasTyT R.E n Γ x R.I) (hx' : HasTyT R.E n Γ x' R.I)
    (hc : TyConvT R.E n Γ (R.revFamApp x) (R.revFamApp x'))
    (h1 : LOKt σ 4 K hx) (h2 : LOKt σ 4 K hx') (h3 : LOKtc σ 4 K hc) :
    TwinConvAt4OvershootK R.E n σ Γ x x' R.I := by
  obtain ⟨K', hK'⟩ := R.rev_inj_internal_overshootK hR hx hx' hc h1 h2 h3
  exact ⟨R.rev_inj_internalB hx hx' hc, K', hK'⟩

/-- **Unconditional height-`4` internal injectivity with `K'` overshoot for `riRevEnv`** (`I = Sort 0`). -/
theorem ri_inj_internal_at4_overshootK
    {x x' : Expr Nat} (hx : HasTyT riRevEnv.E n Γ x (.sort .zero)) (hx' : HasTyT riRevEnv.E n Γ x' (.sort .zero))
    (hc : TyConvT riRevEnv.E n Γ (riRevEnv.revFamApp x) (riRevEnv.revFamApp x'))
    (h1 : LOKt σ 4 K hx) (h2 : LOKt σ 4 K hx') (h3 : LOKtc σ 4 K hc) :
    TwinConvAt4OvershootK riRevEnv.E n σ Γ x x' (.sort .zero) :=
  riRevEnv.rev_inj_internal_at4_overshootK (revSortLe_four_riRevEnv σ) hx hx' hc h1 h2 h3

/-- **Unconditional height-`4` internal injectivity with `K'` overshoot for any `Nat`-indexed `R : RevEnv`**
    (such as `glm-f3eq`'s `RcicF3EqFooRev.fooRevEnv`, where `hmem`, `hI`, `huI`, `hhI` are `rfl` / `HEq.rfl`).
    Note: this produces a conversion in `R.E` (not `R.twin₁`), using an off-diagonal ι step at `R.f + 2`. -/
theorem RevEnv.rev_inj_internal_at4_overshootK_of_natConst
    (hmem : R.E₀.members 0 = some natFamMember)
    (hI : R.I = .const 0 []) (huI : R.uI = .succ .zero)
    (hhI : HEq R.hI (natConstTyT (E := R.E₀) (n := 0) (Γ := []) hmem))
    {x x' : Expr Nat} (hx : HasTyT R.E n Γ x R.I) (hx' : HasTyT R.E n Γ x' R.I)
    (hc : TyConvT R.E n Γ (R.revFamApp x) (R.revFamApp x'))
    (h1 : LOKt σ 4 K hx) (h2 : LOKt σ 4 K hx') (h3 : LOKtc σ 4 K hc) :
    TwinConvAt4OvershootK R.E n σ Γ x x' R.I :=
  R.rev_inj_internal_at4_overshootK (revSortLe_of_natConst R hmem hI huI hhI σ (by decide)) hx hx' hc h1 h2 h3

/-- **Generic twin-round-trip index conversion at height `N` with `K'` overshoot**:
    Because `R.bkConvB` has zero `K (R.f + 2) + 1 ≤ N` requirement (`R.lok_bkConvB`), ANY
    `TwinConvAtNOvershootK R.twin₁ n σ N Γ (tr R.f R.I x) (tr R.f R.I x') R.I` in the twin
    (with an arbitrarily large constant ceiling `KT`) combines with `trConv_selfB hx` and
    `trConv_selfB hx'` (`K (R.f + 2) + 1 ≤ N` on the input `K`) to produce `ConvT R.E n Γ x x' R.I`
    at sort height `N` with only diagonal ι steps at `R.f + 2`. -/
theorem RevEnv.twinIdxConv_overshootK {N : Nat} (h1N : 1 ≤ N) (huIN : evalTotal σ R.uI ≤ N)
    {x x' : Expr Nat} (hx : HasTyT R.E n Γ x R.I) (hx' : HasTyT R.E n Γ x' R.I)
    (hKN : K (R.f + 2) + 1 ≤ N)
    (hI_lok : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (hI_diag : ∀ Γ', DiagRecIotaTy (R.f + 2) (R.hIEB n Γ'))
    (hlok_x : LOKt σ N K hx) (hlok_x' : LOKt σ N K hx')
    (hdiag_x : DiagRecIotaTy (R.f + 2) hx) (hdiag_x' : DiagRecIotaTy (R.f + 2) hx')
    (hTwin : TwinConvAtNOvershootK R.twin₁ n σ N Γ (tr R.f R.I x) (tr R.f R.I x') R.I) :
    ∃ (c : ConvT R.E n Γ x x' R.I) (K' : Nat → Nat),
      LOKc σ N K' c ∧ DiagRecIota (R.f + 2) c := by
  obtain ⟨cT, KT, hlcT⟩ := hTwin
  let K' : Nat → Nat := fun r => max (K r) (KT r)
  have hK_le : ∀ r, K r ≤ K' r := fun r => Nat.le_max_left _ _
  have hKT_le : ∀ r, KT r ≤ K' r := fun r => Nat.le_max_right _ _
  have htr_x : LOKc σ N K' (R.trConv_selfB hx) :=
    lokc_mono (Nat.le_refl N) hK_le _ (R.lok_trConv_selfB h1N huIN hKN hI_lok hx hlok_x)
  have htr_x' : LOKc σ N K' (R.trConv_selfB hx') :=
    lokc_mono (Nat.le_refl N) hK_le _ (R.lok_trConv_selfB h1N huIN hKN hI_lok hx' hlok_x')
  have hbk_cT : LOKc σ N K' (R.bkConvB cT) :=
    lokc_mono (Nat.le_refl N) hKT_le _ ((R.lok_bkConvB cT).mpr hlcT)
  refine ⟨R.twinIdxConvB hx hx' cT, K', ⟨htr_x, hbk_cT, htr_x'⟩,
    ⟨R.diagRecIota_trConv_selfB hI_diag hx hdiag_x,
     diagRecIota_of_noRecIota (R.bkConvB cT) (R.noRecIota_bkConvB cT),
     R.diagRecIota_trConv_selfB hI_diag hx' hdiag_x'⟩⟩

/-- **Generic twin-round-trip index conversion at height `4` with `K'` overshoot**:
    specialization of `twinIdxConv_overshootK` to `N = 4` (`TwinConvAt4OvershootK`). -/
theorem RevEnv.twinIdxConv_at4_overshootK (huI4 : evalTotal σ R.uI ≤ 4)
    {x x' : Expr Nat} (hx : HasTyT R.E n Γ x R.I) (hx' : HasTyT R.E n Γ x' R.I)
    (hK4 : K (R.f + 2) + 1 ≤ 4)
    (hI_lok : ∀ Γ', LOKt σ 4 K (R.hIEB n Γ'))
    (hI_diag : ∀ Γ', DiagRecIotaTy (R.f + 2) (R.hIEB n Γ'))
    (hlok_x : LOKt σ 4 K hx) (hlok_x' : LOKt σ 4 K hx')
    (hdiag_x : DiagRecIotaTy (R.f + 2) hx) (hdiag_x' : DiagRecIotaTy (R.f + 2) hx')
    (hTwin : TwinConvAt4OvershootK R.twin₁ n σ Γ (tr R.f R.I x) (tr R.f R.I x') R.I) :
    ∃ (c : ConvT R.E n Γ x x' R.I) (K' : Nat → Nat),
      LOKc σ 4 K' c ∧ DiagRecIota (R.f + 2) c :=
  R.twinIdxConv_overshootK (by decide) huI4 hx hx' hK4 hI_lok hI_diag hlok_x hlok_x' hdiag_x hdiag_x' hTwin

/-! ### §3.2 Generic annotated twin `R.twin₁A` over `RcicFamAppTwinLokFund` -/

/-- Annotated family member `F : Π (x : IA), Sort 0` for `R : RevEnv`. -/
def RevEnv.revFamMA (R : RevEnv) (IA : ExprA) : CheckedMemberA :=
  ⟨.inductiveM, 0, .pi IA R.uI (.sort .zero) (.succ .zero), none, 0, none⟩

/-- Annotated constructor-axiom member `mk : Π (x : IA), F x` for `R : RevEnv`. -/
def RevEnv.revAxMA (R : RevEnv) (IA : ExprA) : CheckedMemberA :=
  ⟨.axiomM, 0, .pi IA R.uI (.app (.const R.f []) (.bvar 0)) .zero, none, 0, none⟩

/-- Annotated copy of `R.twin₁` over an annotated base `E₀A` and index type `IA`. -/
def RevEnv.twin₁A (R : RevEnv) (E₀A : ResolvedEnvA) (IA : ExprA) : ResolvedEnvA :=
  extendEnvA (extendEnvA E₀A R.f (R.revFamMA IA)) (R.f + 1) (R.revAxMA IA)

theorem RevEnv.twin₁A_members (R : RevEnv) (E₀A : ResolvedEnvA) (IA : ExprA) (r : Nat) :
    (R.twin₁A E₀A IA).members r =
      if r = R.f + 1 then some (R.revAxMA IA)
      else if r = R.f then some (R.revFamMA IA)
      else E₀A.members r := rfl

theorem RevEnv.twin₁A_f (R : RevEnv) (E₀A : ResolvedEnvA) (IA : ExprA) :
    (R.twin₁A E₀A IA).members R.f = some (R.revFamMA IA) := by
  rw [R.twin₁A_members, if_neg (by omega), if_pos rfl]

theorem RevEnv.twin₁A_f1 (R : RevEnv) (E₀A : ResolvedEnvA) (IA : ExprA) :
    (R.twin₁A E₀A IA).members (R.f + 1) = some (R.revAxMA IA) := by
  rw [R.twin₁A_members, if_pos rfl]

theorem RevEnv.eraseEnv_twin₁A (R : RevEnv) (E₀A : ResolvedEnvA) (IA : ExprA)
    (hE₀ : eraseEnv E₀A = R.E₀) (hIA : erase IA = R.I) :
    eraseEnv (R.twin₁A E₀A IA) = R.twin₁ := by
  unfold RevEnv.twin₁A RevEnv.twin₁ RevBase.twinAt RevBase.famEnv
  rw [eraseEnv_extend, eraseEnv_extend, hE₀]
  have hmF : eraseMember (R.revFamMA IA) = revFamM R.I := by
    show (⟨.inductiveM, 0, .pi (erase IA) (.sort .zero), none⟩ : CheckedMember) = revFamM R.I
    rw [hIA]; rfl
  have hmA : eraseMember (R.revAxMA IA) = revAxM R.f R.I := by
    show (⟨.axiomM, 0, .pi (erase IA) (.app (.const R.f []) (.bvar 0)), none⟩ : CheckedMember) =
      revAxM R.f R.I
    rw [hIA]; rfl
  rw [hmF, hmA]

theorem RevEnv.twin₁A_closed (R : RevEnv) (E₀A : ResolvedEnvA) (IA : ExprA)
    (hE₀ : EnvClosedA E₀A) (hclIA : ∀ c, liftA c 1 IA = IA) :
    EnvClosedA (R.twin₁A E₀A IA) := by
  intro r m hm
  rw [R.twin₁A_members] at hm
  by_cases h1 : r = R.f + 1
  · rw [if_pos h1] at hm
    obtain rfl := Option.some.inj hm
    refine ⟨fun c => ?_, fun _ hb => Option.noConfusion hb⟩
    have h0 : ¬ (c + 1 ≤ 0) := by omega
    simp only [RevEnv.revAxMA, liftA, hclIA c, h0, ite_false]
  · rw [if_neg h1] at hm
    by_cases h0 : r = R.f
    · rw [if_pos h0] at hm
      obtain rfl := Option.some.inj hm
      refine ⟨fun c => ?_, fun _ hb => Option.noConfusion hb⟩
      simp only [RevEnv.revFamMA, liftA, hclIA c]
    · rw [if_neg h0] at hm
      exact hE₀ r m hm

/-- **Generic `EnvSemAL` for `R.twin₁A E₀A IA` (`revTwin₁A_semAL`)**:
    holds for EVERY `N` and `K` with ZERO bound on `N` or `K` for the Prop family `F` and its
    constructor-axiom `mk`. -/
theorem RevEnv.revTwin₁A_semAL (R : RevEnv) (E₀A : ResolvedEnvA) (IA : ExprA)
    {N : Nat} {ρ₀ : Nat → Nat}
    (hE₀ : EnvClosedA E₀A) (hclIA : ∀ c, liftA c 1 IA = IA)
    (hinstIA : instantiateLevelsA [] IA = IA)
    (tIA : ∀ Δ : LCtxA, Nonempty (HasTyA (R.twin₁A E₀A IA) noIotaA n Δ IA (.sort R.uI)))
    (vIA : ∃ kIA : Nat, ∀ k, kIA ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA (R.twin₁A E₀A IA) noIotaA n Δ) →
      ∃ Rel, LRTyAL (R.twin₁A E₀A IA) n σ N K ρ₀ k Δ IA Rel)
    (hbase : ∀ r m, E₀A.members r = some m → r ≠ R.f → r ≠ R.f + 1 →
      EnvSemClauseAL (R.twin₁A E₀A IA) n σ N K ρ₀ r m) :
    EnvSemAL (R.twin₁A E₀A IA) n σ N K ρ₀ := by
  have hmFT : instantiateLevelsA [] (R.revFamMA IA).mtypeA = .pi IA R.uI (.sort .zero) (.succ .zero) := by
    show ExprA.pi (instantiateLevelsA [] IA) (instLevel [] R.uI) (.sort .zero) (.succ .zero) = _
    rw [hinstIA, Rcic.Syn.instLevel_of_paramFree [] R.uI R.huI]
  have hmAT : instantiateLevelsA [] (R.revAxMA IA).mtypeA =
      .pi IA R.uI (.app (.const R.f []) (.bvar 0)) .zero := by
    show ExprA.pi (instantiateLevelsA [] IA) (instLevel [] R.uI)
      (.app (.const R.f []) (.bvar 0)) .zero = _
    rw [hinstIA, Rcic.Syn.instLevel_of_paramFree [] R.uI R.huI]
  refine twinEnvSemAL (R.twin₁A_closed E₀A IA hE₀ hclIA)
    (R.twin₁A_f E₀A IA) rfl rfl hmFT
    (R.twin₁A_f1 E₀A IA) rfl rfl hmAT
    hclIA tIA vIA ?_
  intro r m hm hf hf1
  rw [R.twin₁A_members, if_neg hf1, if_neg hf] at hm
  exact hbase r m hm hf hf1

/-- **Generic `TwinConvAtNOvershootK` on `R.twin₁` from `famAppConvInjAL_prop1` (`revTwin₁A_famAppConvInj_overshootK`)**:
    For ANY `R : RevEnv`, any `LOKcA σ N K'`-bounded annotated conversion
    `h : ConvA (R.twin₁A E₀A IA) noIotaA n ΓA (.app (.const R.f []) xA) (.app (.const R.f []) x'A) (.sort w)`
    (`isZero w = true`) yields `TwinConvAtNOvershootK R.twin₁ n σ N (eraseCtx ΓA) (erase xA) (erase x'A) R.I`. -/
theorem RevEnv.revTwin₁A_famAppConvInj_overshootK (R : RevEnv) (E₀A : ResolvedEnvA) (IA : ExprA)
    {N : Nat} {ρ₀ : Nat → Nat} (hρ : PosValA ρ₀)
    (hE₀_erase : eraseEnv E₀A = R.E₀) (hIA_erase : erase IA = R.I)
    (hE₀_closed : EnvClosedA E₀A) (hclIA : ∀ c, liftA c 1 IA = IA)
    (hinstIA : instantiateLevelsA [] IA = IA)
    (tIA : ∀ Δ : LCtxA, Nonempty (HasTyA (R.twin₁A E₀A IA) noIotaA n Δ IA (.sort R.uI)))
    (vIA : ∃ kIA : Nat, ∀ k, kIA ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA (R.twin₁A E₀A IA) noIotaA n Δ) →
      ∃ Rel, LRTyAL (R.twin₁A E₀A IA) n σ N K ρ₀ k Δ IA Rel)
    (hbase : ∀ r m, E₀A.members r = some m → r ≠ R.f → r ≠ R.f + 1 →
      EnvSemClauseAL (R.twin₁A E₀A IA) n σ N K ρ₀ r m)
    {ΓA : LCtxA} {xA x'A : ExprA} {w : Level}
    (hΓA : CtxWfA (R.twin₁A E₀A IA) noIotaA n ΓA) (hdΓA : LOKctxA σ N K hΓA)
    (hz : isZero w = true)
    (h : ConvA (R.twin₁A E₀A IA) noIotaA n ΓA (.app (.const R.f []) xA) (.app (.const R.f []) x'A) (.sort w))
    (hd : LOKcA σ N K h) :
    TwinConvAtNOvershootK R.twin₁ n σ N (eraseCtx ΓA) (erase xA) (erase x'A) R.I := by
  have hmFT : instantiateLevelsA [] (R.revFamMA IA).mtypeA = .pi IA R.uI (.sort .zero) (.succ .zero) := by
    show ExprA.pi (instantiateLevelsA [] IA) (instLevel [] R.uI) (.sort .zero) (.succ .zero) = _
    rw [hinstIA, Rcic.Syn.instLevel_of_paramFree [] R.uI R.huI]
  have hsem := R.revTwin₁A_semAL E₀A IA hE₀_closed hclIA hinstIA tIA vIA hbase
  have hconvAL : ConvAL (R.twin₁A E₀A IA) n σ N K ΓA xA x'A IA :=
    (famAppConvInjAL_prop1 (R.twin₁A_closed E₀A IA hE₀_closed hclIA) hsem hρ hΓA hdΓA
      (r := R.f) (ls := []) (ls' := []) (m := R.revFamMA IA)
      (R.twin₁A_f E₀A IA) rfl rfl hmFT hz h hd).2
  obtain ⟨c, hlc⟩ := hconvAL.2
  have hE_eq : eraseEnv (R.twin₁A E₀A IA) = R.twin₁ := R.eraseEnv_twin₁A E₀A IA hE₀_erase hIA_erase
  rw [← hE_eq, ← hIA_erase]
  exact ⟨c, K, hlc⟩

/-- **Generic `TwinConvAt4OvershootK` on `R.twin₁` at height `4` (`revTwin₁A_famAppConvInj_at4_overshootK`)**:
    specialization of `revTwin₁A_famAppConvInj_overshootK` to `N = 4`. -/
theorem RevEnv.revTwin₁A_famAppConvInj_at4_overshootK (R : RevEnv) (E₀A : ResolvedEnvA) (IA : ExprA)
    {ρ₀ : Nat → Nat} (hρ : PosValA ρ₀)
    (hE₀_erase : eraseEnv E₀A = R.E₀) (hIA_erase : erase IA = R.I)
    (hE₀_closed : EnvClosedA E₀A) (hclIA : ∀ c, liftA c 1 IA = IA)
    (hinstIA : instantiateLevelsA [] IA = IA)
    (tIA : ∀ Δ : LCtxA, Nonempty (HasTyA (R.twin₁A E₀A IA) noIotaA n Δ IA (.sort R.uI)))
    (vIA : ∃ kIA : Nat, ∀ k, kIA ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA (R.twin₁A E₀A IA) noIotaA n Δ) →
      ∃ Rel, LRTyAL (R.twin₁A E₀A IA) n σ 4 K ρ₀ k Δ IA Rel)
    (hbase : ∀ r m, E₀A.members r = some m → r ≠ R.f → r ≠ R.f + 1 →
      EnvSemClauseAL (R.twin₁A E₀A IA) n σ 4 K ρ₀ r m)
    {ΓA : LCtxA} {xA x'A : ExprA} {w : Level}
    (hΓA : CtxWfA (R.twin₁A E₀A IA) noIotaA n ΓA) (hdΓA : LOKctxA σ 4 K hΓA)
    (hz : isZero w = true)
    (h : ConvA (R.twin₁A E₀A IA) noIotaA n ΓA (.app (.const R.f []) xA) (.app (.const R.f []) x'A) (.sort w))
    (hd : LOKcA σ 4 K h) :
    TwinConvAt4OvershootK R.twin₁ n σ (eraseCtx ΓA) (erase xA) (erase x'A) R.I :=
  R.revTwin₁A_famAppConvInj_overshootK E₀A IA hρ hE₀_erase hIA_erase hE₀_closed hclIA hinstIA
    tIA vIA hbase hΓA hdΓA hz h hd

/-! ### §3.3 Unconditional specialization at `riRevEnv.twin₁` (`I = .sort .zero`, `uI = .succ .zero`) -/

/-- Annotated copy of `riRevEnv.twin₁` (`E₀A = emptyEnvA`, `IA = .sort .zero`). -/
abbrev riRevTwin₁A : ResolvedEnvA :=
  riRevEnv.twin₁A emptyEnvA (.sort .zero)

theorem eraseEnv_riRevTwin₁A : eraseEnv riRevTwin₁A = riRevEnv.twin₁ :=
  riRevEnv.eraseEnv_twin₁A emptyEnvA (.sort .zero) rfl rfl

theorem riRevTwin₁A_closed : EnvClosedA riRevTwin₁A :=
  riRevEnv.twin₁A_closed emptyEnvA (.sort .zero)
    (fun _ _ hm => Option.noConfusion hm) (fun _ => rfl)

/-- `EnvSemAL` for `riRevTwin₁A` holds for every `N` and every `K`! -/
theorem riRevTwin₁A_semAL {N : Nat} {ρ₀ : Nat → Nat} :
    EnvSemAL riRevTwin₁A n σ N K ρ₀ :=
  riRevEnv.revTwin₁A_semAL emptyEnvA (.sort .zero)
    (fun _ _ hm => Option.noConfusion hm) (fun _ => rfl) rfl
    (fun Δ => ⟨.sort Δ .zero⟩)
    ⟨ht ρ₀ .zero + 1, fun _ hk Δ _ => LRTyAL_sort_valid Δ hk⟩
    (fun _ _ hm _ _ => Option.noConfusion hm)

/-- **Unconditional `TwinConvAt4OvershootK` on `riRevEnv.twin₁`** from any height-4 annotated
    conversion `RI x ≡ RI x'`. -/
theorem riRevTwin₁_famAppConvInj_at4_overshootK {ρ₀ : Nat → Nat} (hρ : PosValA ρ₀)
    {ΓA : LCtxA} {xA x'A : ExprA} {w : Level}
    (hΓA : CtxWfA riRevTwin₁A noIotaA n ΓA) (hdΓA : LOKctxA σ 4 K hΓA)
    (hz : isZero w = true)
    (h : ConvA riRevTwin₁A noIotaA n ΓA (.app (.const 0 []) xA) (.app (.const 0 []) x'A) (.sort w))
    (hd : LOKcA σ 4 K h) :
    TwinConvAt4OvershootK riRevEnv.twin₁ n σ (eraseCtx ΓA) (erase xA) (erase x'A) (.sort .zero) :=
  riRevEnv.revTwin₁A_famAppConvInj_at4_overshootK emptyEnvA (.sort .zero) hρ rfl rfl
    (fun _ _ hm => Option.noConfusion hm) (fun _ => rfl) rfl
    (fun Δ => ⟨.sort Δ .zero⟩)
    ⟨ht ρ₀ .zero + 1, fun _ hk Δ _ => LRTyAL_sort_valid Δ hk⟩
    (fun _ _ hm _ _ => Option.noConfusion hm)
    hΓA hdΓA hz h hd

/-! ### §3.4 Named consumer premise for `glm-f3eq` (`RevTwinRowAtNOvershootK` / `RevTwinRowAt4OvershootK` — definitions only) -/

/-- **Sort-height-`N`, `K'`-overshoot version of `glm-f3eq`'s `RevTwinRowBounded` (definition only)**:
    below `Efin`, at every ι witness `w` of `R.f + 2` whose left-hand side is typed within bounds
    `(N, K)`, at every field `k` and index position `p` with recursor index argument `idx`, the
    recursor-free twin `R.twin₁` admits
    `TwinConvAtNOvershootK R.twin₁ n σ N Γ (tr R.f R.I (w.fields[k]'hk)) (tr R.f R.I idx) R.I`
    (sort/Π height `≤ N`, arbitrary constant-instance ceiling `K'`).
    **Note:** No theorem in this module proves `RevTwinRowAtNOvershootK` or `RevTwinRowAt4OvershootK`
    (neither generically nor at `riRevEnv` / `fooRevEnv`). -/
def RevTwinRowAtNOvershootK (R : RevEnv) (N : Nat) (K : Nat → Nat) (Efin : ResolvedEnv) : Prop :=
  ∀ (E' : ResolvedEnv), (∀ r' m', E'.members r' = some m' → Efin.members r' = some m') →
    ∀ (w : IotaWitness E'), w.recRef = R.f + 2 →
      ∀ (σ : Nat → Nat) (n : Nat) (Γ : LCtx) (T : Expr Nat)
        (hl : HasTyT E' n Γ (iotaLhsOf w) T), LOKt σ N K hl →
        ∀ (k p : Nat) (hk : k < w.fields.length), p < w.nindices →
          ∀ idx : Expr Nat, w.preMajor[w.nparams + 1 + w.nMinors + p]? = some idx →
            TwinConvAtNOvershootK R.twin₁ n σ N Γ (tr R.f R.I (w.fields[k]'hk)) (tr R.f R.I idx) R.I

/-- **Height-`4`, `K'`-overshoot version of `glm-f3eq`'s `RevTwinRowBounded` (`RevTwinRowAt4OvershootK` — `abbrev` only)**:
    `RevTwinRowAtNOvershootK R 4 K Efin`. -/
abbrev RevTwinRowAt4OvershootK (R : RevEnv) (K : Nat → Nat) (Efin : ResolvedEnv) : Prop :=
  RevTwinRowAtNOvershootK R 4 K Efin

end GenericHeight4

end Rcic.Syn.FamApp.Rev
