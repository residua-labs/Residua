import rcic.RcicSynTable

/-!
# Syntactic sortRow, build step 4f — `DMStep` Combinators, the `TyP.isSortOrPiHead` Regularity Dichotomy, and Unconditional `SortCoh` / `BitCoh` / `CTS` at Pack Measures

`research/rcic/semantic/S3_ES_ARMS.md` §55 and `S0_SORTROW_SYNTACTIC.md` §4.

This module establishes the regularity-measure dichotomy on `TyP` and the endpoint-measure
steps on `CvP`, discharging `CL(D.reg.2, TyP.sort)`, `SortCoh`, `BitCoh`, and `CTS` directly
at their mutual-pack `LexDM` measures (`tyMeas`, `tyPairMeas`, `cvTyMeas`):

1. **§1 Multiset (`DMStep` / `LexDM`) structural combinators**:
   - `dmStep_perm_left`, `dmStep_perm_right`, `dmStep_append_right`, `dmStep_append_left`,
     `dmStep_drop_right`, `dmStep_drop_left`.

2. **§2 `TyP.isSortOrPiHead` and the Regularity Dichotomy (`TyP.reg`)**:
   - `ETm.isSortOrPi`, `ETm.ne_star_of_isSortOrPi`, `ETm.isSortOrPi_lift_of_true`,
     `ETm.isSortOrPi_inst_of_true`.
   - `TyP.isSortOrPiHead`: `true` when the head leaf (under transports `.wk`, `.esub`, `.lsub`,
     `.linst`, `.ewk`, `.cctx`) is `.sort` or `.pi`; `false` on `.bvar`, `.const`, `.lam`,
     `.app`, `.letE`, `.lit`, `.conv`.
   - **Branch 1 (`D.isSortOrPiHead = true`)**:
     - `isSortOrPi_eps_of_isSortOrPiHead` and `eps_ne_star_of_isSortOrPiHead`: `D.eps σ ρ ≠ .star`.
     - `reg_fst_succ_of_isSortOrPiHead`: `∃ w, D.reg.1 = .succ w`.
     - `pbit_reg_of_isSortOrPiHead`: `PBit σ ρ D D.reg.2` holds with **zero `Below` hypotheses**.
     - `reg_eps_of_isSortOrPiHead`, `reg_eps_sort_of_isSortOrPiHead`, and
       `cl_reg_sort_of_isSortOrPiHead`: for `D : TyP E n Γ T (.sort u)`,
       `D.reg.2.eps σ ρ = .sort (σ u)` holds **by computation** (zero `Below`, zero `DispFor`).
   - **Branch 2 (`D.isSortOrPiHead = false`)**:
     - `dmStep_reg_nonTransport` and `dmStep_reg_of_not_isSortOrPiHead`: for any `Y` with
       `∀ y ∈ Y, y ≤ 1`, `DMStep (D.reg.2.atoms Aw ++ Y) (D.atoms Aw)`.
     - `dmStep_reg_atoms`, `dmStep_reg_sort_pair`, `lexDM_reg_pair_left`,
       `lexDM_reg_sort_of_tyMeas`, `lexDM_reg_sort_of_pair_left`,
       `lexDM_reg_sort_of_pair_right`.

3. **§3 Unconditional `CL(D.reg.2, TyP.sort)`, `SortCoh`, `BitCoh`, `PBit`, and `CTS` at Pack Measures**:
   - `cl_reg_sort_of_below_ty`, `cl_reg_sort_of_below_pair_left`,
     `cl_reg_sort_of_below_pair_right`.
   - `sortCoh_of_below_and_eut` and `bitCoh_of_below_and_eut`: prove `SortCoh σ D₁ D₂` and
     `BitCoh σ D₁ D₂` directly from `Below Aw tbl (tyPairMeas Aw D₁ D₂)` and `EUT tbl σ ρ D₁ D₂`.
   - `sortCoh_of_below_lex` and `bitCoh_of_below_lex`.
   - `pbit_of_below_not_isSortOrPiHead`.
   - `dmStep_cvp_dl`, `dmStep_cvp_dr`, `dmStep_cvp_dl_reg`, `dmStep_cvp_dr_reg`,
     `dmStep_cts_pair`, `lexDM_cts_pair`, `cl_reg_sort_of_below_cts_left`,
     `cl_reg_sort_of_below_cts_right`, and `cts_of_below`: prove `CTS h DX` (`eqN s w`)
     directly from `Below Aw tbl (cvTyMeas Aw h DX)` alone.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Multiset (`DMStep` / `LexDM`) Structural Combinators -/

theorem dmStep_perm_left {M₁ M₂ M : List Nat} (hp : M₁.Perm M₂) (h : DMStep M₁ M) :
    DMStep M₂ M := by
  obtain ⟨X, Y, Z, hX, hM, hM₁, hlt⟩ := h
  exact ⟨X, Y, Z, hX, hM, hp.symm.trans hM₁, hlt⟩

theorem dmStep_perm_right {M' M₁ M₂ : List Nat} (hp : M₁.Perm M₂) (h : DMStep M' M₁) :
    DMStep M' M₂ := by
  obtain ⟨X, Y, Z, hX, hM₁, hM', hlt⟩ := h
  exact ⟨X, Y, Z, hX, hp.symm.trans hM₁, hM', hlt⟩

theorem dmStep_append_right {M' M : List Nat} (h : DMStep M' M) (W : List Nat) :
    DMStep (M' ++ W) (M ++ W) := by
  obtain ⟨X, Y, Z, hX, hM, hM', hlt⟩ := h
  refine ⟨X, Y, Z ++ W, hX, ?_, ?_, hlt⟩
  · rw [← List.append_assoc]
    exact hM.append_right W
  · rw [← List.append_assoc]
    exact hM'.append_right W

theorem dmStep_append_left {M' M : List Nat} (h : DMStep M' M) (W : List Nat) :
    DMStep (W ++ M') (W ++ M) :=
  dmStep_perm_left List.perm_append_comm
    (dmStep_perm_right List.perm_append_comm (dmStep_append_right h W))

theorem dmStep_drop_right {M' M : List Nat} (h : DMStep M' M) (W : List Nat) :
    DMStep M' (M ++ W) := by
  obtain ⟨X, Y, Z, hX, hM, hM', hlt⟩ := h
  have hperm : (M ++ W).Perm ((X ++ W) ++ Z) := by
    refine (hM.append_right W).trans ?_
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left X List.perm_append_comm
  refine ⟨X ++ W, Y, Z, ?_, hperm, hM', ?_⟩
  · intro hnil
    exact hX (List.append_eq_nil.mp hnil).1
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := hlt y hy
    exact ⟨x, List.mem_append_left W hx, hyx⟩

theorem dmStep_drop_left {M' M : List Nat} (h : DMStep M' M) (W : List Nat) :
    DMStep M' (W ++ M) :=
  dmStep_perm_right List.perm_append_comm (dmStep_drop_right h W)

/-! ## §2 `TyP.isSortOrPiHead` and the Regularity Dichotomy (`TyP.reg`) -/

/-- Erased terms whose outer constructor is `.sort` or `.pi`. -/
def ETm.isSortOrPi : ETm → Bool
  | .sort _ => true
  | .pi _ _ => true
  | _ => false

theorem ETm.ne_star_of_isSortOrPi {e : ETm} (h : e.isSortOrPi = true) : e ≠ .star := by
  intro hs
  subst hs
  exact Bool.noConfusion h

theorem ETm.isSortOrPi_lift_of_true (c k : Nat) {e : ETm}
    (h : e.isSortOrPi = true) : (e.lift c k).isSortOrPi = true := by
  cases e with
  | sort _ | pi _ _ => rfl
  | bvar _ | star | const _ _ | app _ _ | lam _ => exact Bool.noConfusion h

theorem ETm.isSortOrPi_inst_of_true (j : Nat) (r : ETm) {e : ETm}
    (h : e.isSortOrPi = true) : (ETm.inst j r e).isSortOrPi = true := by
  cases e with
  | sort _ | pi _ _ => rfl
  | bvar _ | star | const _ _ | app _ _ | lam _ => exact Bool.noConfusion h

/-- Whether the head leaf of `D : TyP E n Γ e T` (under the 6 transport constructors
    `.wk`, `.esub`, `.lsub`, `.linst`, `.ewk`, `.cctx`) is `.sort` or `.pi`. -/
def TyP.isSortOrPiHead : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → Bool
  | _, _, _, _, _, .sort .. => true
  | _, _, _, _, _, .pi .. => true
  | _, _, _, _, _, .bvar .. => false
  | _, _, _, _, _, .const .. => false
  | _, _, _, _, _, .lam .. => false
  | _, _, _, _, _, .app .. => false
  | _, _, _, _, _, .letE .. => false
  | _, _, _, _, _, .lit .. => false
  | _, _, _, _, _, .conv .. => false
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => D.isSortOrPiHead
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ _ _ => D.isSortOrPiHead
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ _ _ => D.isSortOrPiHead
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => D.isSortOrPiHead
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.isSortOrPiHead
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.isSortOrPiHead

/-- Every derivation with `D.isSortOrPiHead = true` erases to a `.sort` or `.pi` term. -/
theorem isSortOrPi_eps_of_isSortOrPiHead :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortOrPiHead = true →
    (σ : Level → Level) → (ρ : List Disp) → (D.eps σ ρ).isSortOrPi = true
  | _, _, _, _, _, .sort .., _, _, _ => rfl
  | _, _, _, _, _, .pi _ _ _ _ u _ _ _ _, _, σ, _ => by
      simp only [TyP.eps]
      cases levelIsZero (σ u) <;> rfl
  | _, _, _, _, _, .bvar .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .const .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .lam .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .app .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .letE .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .lit .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .conv .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D, h, σ, ρ => by
      have ih := isSortOrPi_eps_of_isSortOrPiHead D h σ (removeAt ρ c)
      by_cases hk : ρ[c]? = some .keep
      · rw [eps_wk_keep hk]
        exact ETm.isSortOrPi_lift_of_true _ _ ih
      · rw [eps_wk_not_keep_of_ne hk]
        exact ih
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ hv _, h, σ, ρ => by
      simp only [TyP.eps]
      cases levelIsZero (σ u) with
      | true => exact isSortOrPi_eps_of_isSortOrPiHead D h σ (insertDisp .drop j ρ)
      | false =>
          exact ETm.isSortOrPi_inst_of_true _ _
            (isSortOrPi_eps_of_isSortOrPiHead D h σ (insertDisp .keep j ρ))
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D hget hv hvT, h, σ, ρ => by
      rw [lsub_eps_eq D hget hv hvT]
      exact isSortOrPi_eps_of_isSortOrPiHead D h σ
        (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, h, σ, ρ =>
      isSortOrPi_eps_of_isSortOrPiHead D h (fun l => σ (instLevel ls l)) ρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, h, σ, ρ =>
      isSortOrPi_eps_of_isSortOrPiHead D h σ ρ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, h, σ, ρ =>
      isSortOrPi_eps_of_isSortOrPiHead D h σ ρ

/-- Every derivation with `D.isSortOrPiHead = true` erases to a non-`★` term. -/
theorem eps_ne_star_of_isSortOrPiHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {D : TyP E n Γ e T} (h : D.isSortOrPiHead = true) (σ : Level → Level) (ρ : List Disp) :
    D.eps σ ρ ≠ .star :=
  ETm.ne_star_of_isSortOrPi (isSortOrPi_eps_of_isSortOrPiHead D h σ ρ)

/-- Whenever `D.isSortOrPiHead = true`, `D.reg.1` is a successor level `.succ w`. -/
theorem reg_fst_succ_of_isSortOrPiHead :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortOrPiHead = true → ∃ w : Level, D.reg.1 = .succ w
  | _, _, _, _, _, .sort _ _ _ _ k _, _ => ⟨k, rfl⟩
  | _, _, _, _, _, .pi _ _ _ _ u _ v _ _, _ => ⟨.imax u v, rfl⟩
  | _, _, _, _, _, .bvar .., h => Bool.noConfusion h
  | _, _, _, _, _, .const .., h => Bool.noConfusion h
  | _, _, _, _, _, .lam .., h => Bool.noConfusion h
  | _, _, _, _, _, .app .., h => Bool.noConfusion h
  | _, _, _, _, _, .letE .., h => Bool.noConfusion h
  | _, _, _, _, _, .lit .., h => Bool.noConfusion h
  | _, _, _, _, _, .conv .., h => Bool.noConfusion h
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D, h => reg_fst_succ_of_isSortOrPiHead D h
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ _ _, h => reg_fst_succ_of_isSortOrPiHead D h
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ _ _, h => reg_fst_succ_of_isSortOrPiHead D h
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, h => by
      obtain ⟨w₀, hw₀⟩ := reg_fst_succ_of_isSortOrPiHead D h
      refine ⟨instLevel ls w₀, ?_⟩
      simp only [TyP.reg, hw₀, instLevel_succ]
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, h => reg_fst_succ_of_isSortOrPiHead D h
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, h => reg_fst_succ_of_isSortOrPiHead D h

/-- Whenever `D.isSortOrPiHead = true`, `PBit σ ρ D D.reg.2` holds unconditionally
    for any `LevelSub σ` and any `ρ` (with **zero `Below` hypotheses**). -/
theorem pbit_reg_of_isSortOrPiHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {D : TyP E n Γ e T} (h : D.isSortOrPiHead = true)
    {σ : Level → Level} (hσ : LevelSub σ) (ρ : List Disp) :
    PBit σ ρ D D.reg.2 := by
  unfold PBit
  have hne := eps_ne_star_of_isSortOrPiHead h σ ρ
  obtain ⟨w, hw⟩ := reg_fst_succ_of_isSortOrPiHead D h
  have hbit : levelIsZero (σ D.reg.1) = false := by
    rw [hw]
    exact hσ.succ_bit w
  exact ⟨fun hs => absurd hs hne, fun ht => by rw [hbit] at ht; exact Bool.noConfusion ht⟩

/-- Whenever `D.isSortOrPiHead = true` on `D : TyP E n Γ e S`, the ascribed type `S` is
    `.sort w` for some level `w` and `D.reg.2.eps σ ρ = .sort (σ w)` holds identically
    for all `σ` and `ρ`. -/
theorem reg_eps_of_isSortOrPiHead :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e S : Expr Nat} →
    (D : TyP E n Γ e S) → D.isSortOrPiHead = true →
    ∃ w : Level, S = .sort w ∧ ∀ (σ : Level → Level) (ρ : List Disp),
      D.reg.2.eps σ ρ = .sort (σ w)
  | _, _, _, _, _, .sort _ _ _ _ k _, _ => ⟨k, rfl, fun _ _ => rfl⟩
  | _, _, _, _, _, .pi _ _ _ _ u _ v _ _, _ => ⟨.imax u v, rfl, fun _ _ => rfl⟩
  | _, _, _, _, _, .bvar .., h => Bool.noConfusion h
  | _, _, _, _, _, .const .., h => Bool.noConfusion h
  | _, _, _, _, _, .lam .., h => Bool.noConfusion h
  | _, _, _, _, _, .app .., h => Bool.noConfusion h
  | _, _, _, _, _, .letE .., h => Bool.noConfusion h
  | _, _, _, _, _, .lit .., h => Bool.noConfusion h
  | _, _, _, _, _, .conv .., h => Bool.noConfusion h
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D, h => by
      obtain ⟨w, rfl, heps⟩ := reg_eps_of_isSortOrPiHead D h
      refine ⟨w, rfl, fun σ ρ => ?_⟩
      simp only [TyP.reg]
      by_cases hk : ρ[c]? = some .keep
      · rw [eps_wk_keep hk, heps σ (removeAt ρ c)]
        rfl
      · rw [eps_wk_not_keep_of_ne hk, heps σ (removeAt ρ c)]
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ _ _, h => by
      obtain ⟨w, rfl, heps⟩ := reg_eps_of_isSortOrPiHead D h
      refine ⟨w, rfl, fun σ ρ => ?_⟩
      simp only [TyP.reg, TyP.eps]
      cases levelIsZero (σ u) with
      | true => exact heps σ (insertDisp .drop j ρ)
      | false =>
          rw [heps σ (insertDisp .keep j ρ)]
          rfl
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D hget hv hvT, h => by
      obtain ⟨w, rfl, heps⟩ := reg_eps_of_isSortOrPiHead D h
      refine ⟨w, rfl, fun σ ρ => ?_⟩
      simp only [TyP.reg]
      rw [lsub_eps_eq D.reg.2 hget hv hvT]
      exact heps σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, h => by
      obtain ⟨w₀, rfl, heps⟩ := reg_eps_of_isSortOrPiHead D h
      refine ⟨instLevel ls w₀, rfl, fun σ ρ => ?_⟩
      simp only [TyP.reg, TyP.eps]
      exact heps (fun l => σ (instLevel ls l)) ρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, h => by
      obtain ⟨w, rfl, heps⟩ := reg_eps_of_isSortOrPiHead D h
      exact ⟨w, rfl, fun σ ρ => heps σ ρ⟩
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, h => by
      obtain ⟨w, rfl, heps⟩ := reg_eps_of_isSortOrPiHead D h
      exact ⟨w, rfl, fun σ ρ => heps σ ρ⟩

/-- Specialization of `reg_eps_of_isSortOrPiHead` to `D : TyP E n Γ T (.sort u)`:
    when `D.isSortOrPiHead = true`, `D.reg.2.eps σ ρ = .sort (σ u)` holds identically. -/
theorem reg_eps_sort_of_isSortOrPiHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T : Expr Nat} {u : Level} (D : TyP E n Γ T (.sort u))
    (h : D.isSortOrPiHead = true) (σ : Level → Level) (ρ : List Disp) :
    D.reg.2.eps σ ρ = .sort (σ u) := by
  obtain ⟨w, hw, heps⟩ := reg_eps_of_isSortOrPiHead D h
  cases Expr.sort.inj hw
  exact heps σ ρ

/-- When `D : TyP E n Γ T (.sort u)` has `D.isSortOrPiHead = true`,
    `CL tbl σ ρ D.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _))` holds by `ConvMod.refl`
    (with **zero `Below` and zero `DispFor` hypotheses**). -/
theorem cl_reg_sort_of_isSortOrPiHead (tbl : List CRule) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T : Expr Nat} {u : Level} (D : TyP E n Γ T (.sort u))
    (h : D.isSortOrPiHead = true) (σ : Level → Level) (ρ : List Disp) :
    CL tbl σ ρ D.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)) := by
  unfold CL
  rw [reg_eps_sort_of_isSortOrPiHead D h σ ρ, eps_sort]
  exact .refl _

/-- Inserting `W` before `Y` in the left-hand side of `DMStep (A ++ Y) B` and at the right of `B`
    preserves `DMStep`. Used by `.cctx` transport steps when carrying a trailing atom list `Y`. -/
theorem dmStep_append_middle {A B W Y : List Nat} (h : DMStep (A ++ Y) B) :
    DMStep (A ++ W ++ Y) (B ++ W) := by
  have h1 : DMStep ((A ++ Y) ++ W) (B ++ W) := dmStep_append_right h W
  refine dmStep_perm_left ?_ h1
  rw [List.append_assoc A W Y, List.append_assoc A Y W]
  exact List.Perm.append_left A List.perm_append_comm

/-- Two-list variant of `dmStep_append_middle`, used by `.esub` and `.lsub` transport steps. -/
theorem dmStep_append_middle2 {A B W₁ W₂ Y : List Nat} (h : DMStep (A ++ Y) B) :
    DMStep (A ++ W₁ ++ W₂ ++ Y) (B ++ W₁ ++ W₂) :=
  dmStep_append_middle (dmStep_append_middle h)

/-- Helper for non-transport leaves with `D.isSortOrPiHead = false` (`1 < D.wt Aw` and
    `D.reg.2.wt Aw < D.wt Aw`). -/
theorem dmStep_reg_nonTransport (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T)
    (hw1 : 1 < D.wt Aw) (hreg : D.reg.2.wt Aw < D.wt Aw)
    (heq : D.atoms Aw = [D.wt Aw])
    {Y : List Nat} (hY : ∀ y ∈ Y, y ≤ 1) :
    DMStep (D.reg.2.atoms Aw ++ Y) (D.atoms Aw) := by
  rw [heq, ← List.append_nil (D.reg.2.atoms Aw ++ Y)]
  refine dmStep_of_below ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw D.reg.2 hreg y hy
  · exact Nat.lt_of_le_of_lt (hY y hy) hw1

/-- When `D.isSortOrPiHead = false`, `D.reg.2.atoms Aw ++ Y` is a `DMStep` strictly below
    `D.atoms Aw` for any list `Y` with `∀ y ∈ Y, y ≤ 1`. -/
theorem dmStep_reg_of_not_isSortOrPiHead (Aw : Nat → Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortOrPiHead = false →
    {Y : List Nat} → (∀ y ∈ Y, y ≤ 1) →
    DMStep (D.reg.2.atoms Aw ++ Y) (D.atoms Aw)
  | _, _, _, _, _, .sort .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .pi .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .bvar E n Γ i A u hget hA, _, _, hY => by
      have hp := TyP.wt_pos Aw hA
      exact dmStep_reg_nonTransport Aw (.bvar E n Γ i A u hget hA)
        (by simp only [TyP.wt]; omega)
        (by simp only [TyP.reg, TyP.wt]; omega)
        rfl hY
  | _, _, _, _, _, .const E n Γ r ls m ls₀ u hres hlen hwf hwf₀ hT, _, _, hY => by
      have hp := TyP.wt_pos Aw hT
      exact dmStep_reg_nonTransport Aw (.const E n Γ r ls m ls₀ u hres hlen hwf hwf₀ hT)
        (by simp only [TyP.wt]; omega)
        (by simp only [TyP.reg, TyP.wt]; omega)
        rfl hY
  | _, _, _, _, _, .lam E n Γ A body B u v hA hb hB, _, _, hY => by
      have hp := TyP.wt_pos Aw hb
      exact dmStep_reg_nonTransport Aw (.lam E n Γ A body B u v hA hb hB)
        (by simp only [TyP.wt]; omega)
        (by simp only [TyP.reg, TyP.wt]; omega)
        rfl hY
  | _, _, _, _, _, .app E n Γ f a A B u hf ha hT, _, _, hY => by
      have hp := TyP.wt_pos Aw hT
      exact dmStep_reg_nonTransport Aw (.app E n Γ f a A B u hf ha hT)
        (by simp only [TyP.wt]; omega)
        (by simp only [TyP.reg, TyP.wt]; omega)
        rfl hY
  | _, _, _, _, _, .letE E n Γ A value body B u v hA hv hb hT, _, _, hY => by
      have hp := TyP.wt_pos Aw hT
      exact dmStep_reg_nonTransport Aw (.letE E n Γ A value body B u v hA hv hb hT)
        (by simp only [TyP.wt]; omega)
        (by simp only [TyP.reg, TyP.wt]; omega)
        rfl hY
  | _, _, _, _, _, .lit E n Γ t A hexp, _, _, hY => by
      have hp := TyP.wt_pos Aw hexp
      have hle := TyP.wt_reg_le Aw hexp
      exact dmStep_reg_nonTransport Aw (.lit E n Γ t A hexp)
        (by simp only [TyP.wt]; omega)
        (by simp only [TyP.reg, TyP.wt]; omega)
        rfl hY
  | _, _, _, _, _, .conv E n Γ e A B u hd hc, _, _, hY => by
      have hp := CvP.wt_pos Aw hc
      have hlt := CvP.wt_dr_lt Aw hc
      exact dmStep_reg_nonTransport Aw (.conv E n Γ e A B u hd hc)
        (by simp only [TyP.wt]; omega)
        (by simp only [TyP.reg, TyP.wt]; omega)
        rfl hY
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D', h, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw D' h hY
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D' _ _ _, h, _, hY =>
      dmStep_append_middle2 (dmStep_reg_of_not_isSortOrPiHead Aw D' h hY)
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D' _ _ _, h, _, hY =>
      dmStep_append_middle2 (dmStep_reg_of_not_isSortOrPiHead Aw D' h hY)
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D', h, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw D' h hY
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D', h, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw D' h hY
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D' _, h, _, hY =>
      dmStep_append_middle (dmStep_reg_of_not_isSortOrPiHead Aw D' h hY)

/-- Specialization of `dmStep_reg_of_not_isSortOrPiHead` to `Y = []`:
    when `D.isSortOrPiHead = false`, `DMStep (D.reg.2.atoms Aw) (D.atoms Aw)`. -/
theorem dmStep_reg_atoms (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (h : D.isSortOrPiHead = false) :
    DMStep (D.reg.2.atoms Aw) (D.atoms Aw) := by
  simpa only [List.append_nil] using
    dmStep_reg_of_not_isSortOrPiHead Aw D h (Y := []) (fun _ hy => nomatch hy)

/-- Specialization of `dmStep_reg_of_not_isSortOrPiHead` to `Y = [1]`:
    when `D.isSortOrPiHead = false`, pairing `D.reg.2` with a canonical `TyP.sort` node
    is a `DMStep` strictly below `D.atoms Aw`. -/
theorem dmStep_reg_sort_pair (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T : Expr Nat} {u : Level} (D : TyP E n Γ T (.sort u)) (h : D.isSortOrPiHead = false) :
    DMStep
      (D.reg.2.atoms Aw ++ (TyP.sort E n Γ u (.succ u) (eqN_refl _)).atoms Aw)
      (D.atoms Aw) := by
  refine dmStep_reg_of_not_isSortOrPiHead Aw D h ?_
  intro y hy
  simp only [TyP.atoms, List.mem_singleton] at hy
  subst hy
  exact Nat.le_refl 1

theorem lexDM_reg_pair_left (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (h : D.isSortOrPiHead = false)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat}
    (DT : TyP E' n' Γ' e' T') :
    LexDM (tyPairMeas Aw D.reg.2 DT) (tyPairMeas Aw D DT) :=
  lex_of_dm (dmStep_append_right (dmStep_reg_atoms Aw D h) (DT.atoms Aw))

theorem lexDM_reg_sort_of_tyMeas (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T : Expr Nat} {u : Level} (D : TyP E n Γ T (.sort u)) (h : D.isSortOrPiHead = false) :
    LexDM (tyPairMeas Aw D.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _))) (tyMeas Aw D) :=
  lex_of_dm (dmStep_reg_sort_pair Aw D h)

theorem lexDM_reg_sort_of_pair_left (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T : Expr Nat} {u : Level} (D₁ : TyP E n Γ T (.sort u)) (h : D₁.isSortOrPiHead = false)
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂) :
    LexDM
      (tyPairMeas Aw D₁.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
      (tyPairMeas Aw D₁ D₂) :=
  lex_of_dm (dmStep_drop_right (dmStep_reg_sort_pair Aw D₁ h) (D₂.atoms Aw))

theorem lexDM_reg_sort_of_pair_right (Aw : Nat → Nat)
    {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e₁ T₁ : Expr Nat}
    (D₁ : TyP E₁ n₁ Γ₁ e₁ T₁)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {v : Level}
    (D₂ : TyP E n Γ T (.sort v)) (h : D₂.isSortOrPiHead = false) :
    LexDM
      (tyPairMeas Aw D₂.reg.2 (TyP.sort E n Γ v (.succ v) (eqN_refl _)))
      (tyPairMeas Aw D₁ D₂) :=
  lex_of_dm (dmStep_drop_left (dmStep_reg_sort_pair Aw D₂ h) (D₁.atoms Aw))

/-! ## §3 Unconditional `CL(D.reg.2, TyP.sort)`, `SortCoh`, `BitCoh`, `PBit`, and `CTS` at Pack Measures -/

/-- For **every** `D : TyP E n Γ T (.sort u)`, `Below Aw tbl (tyMeas Aw D)` and `DispFor σ E n Γ ρ`
    discharge `CL tbl σ ρ D.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _))`:
    when `D.isSortOrPiHead = true`, `cl_reg_sort_of_isSortOrPiHead` closes by computation;
    when `D.isSortOrPiHead = false`, `Bel.cl` closes via `lexDM_reg_sort_of_tyMeas`. -/
theorem cl_reg_sort_of_below_ty (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u : Level}
    (D : TyP E n Γ T (.sort u)) (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyMeas Aw D)) :
    CL tbl σ ρ D.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)) := by
  cases h : D.isSortOrPiHead with
  | true => exact cl_reg_sort_of_isSortOrPiHead tbl D h σ ρ
  | false =>
      exact Bel.cl D.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)) σ ρ hρ
        (lexDM_reg_sort_of_tyMeas Aw D h)

/-- Left-pair variant of `cl_reg_sort_of_below_ty` at `tyPairMeas Aw D₁ D₂`. -/
theorem cl_reg_sort_of_below_pair_left (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u : Level}
    (D₁ : TyP E n Γ T (.sort u))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw D₁ D₂)) :
    CL tbl σ ρ D₁.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)) := by
  cases h : D₁.isSortOrPiHead with
  | true => exact cl_reg_sort_of_isSortOrPiHead tbl D₁ h σ ρ
  | false =>
      exact Bel.cl D₁.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)) σ ρ hρ
        (lexDM_reg_sort_of_pair_left Aw D₁ h D₂)

/-- Right-pair variant of `cl_reg_sort_of_below_ty` at `tyPairMeas Aw D₁ D₂`. -/
theorem cl_reg_sort_of_below_pair_right (Aw : Nat → Nat) (tbl : List CRule)
    {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e₁ T₁ : Expr Nat}
    (D₁ : TyP E₁ n₁ Γ₁ e₁ T₁)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {v : Level}
    (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw D₁ D₂)) :
    CL tbl σ ρ D₂.reg.2 (TyP.sort E n Γ v (.succ v) (eqN_refl _)) := by
  cases h : D₂.isSortOrPiHead with
  | true => exact cl_reg_sort_of_isSortOrPiHead tbl D₂ h σ ρ
  | false =>
      exact Bel.cl D₂.reg.2 (TyP.sort E n Γ v (.succ v) (eqN_refl _)) σ ρ hρ
        (lexDM_reg_sort_of_pair_right Aw D₁ D₂ h)

/-- `SortCoh σ D₁ D₂` (`eqN (σ u) (σ v)`) directly at the pair measure `tyPairMeas Aw D₁ D₂`,
    from `Below Aw tbl (tyPairMeas Aw D₁ D₂)` and `EUT tbl σ ρ D₁ D₂`. -/
theorem sortCoh_of_below_and_eut (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw D₁ D₂))
    (heut : EUT tbl σ ρ D₁ D₂) :
    SortCoh σ D₁ D₂ :=
  sortCoh_of_eut_cl hW D₁ D₂ σ ρ heut
    (cl_reg_sort_of_below_pair_left Aw tbl D₁ D₂ σ ρ hρ Bel)
    (cl_reg_sort_of_below_pair_right Aw tbl D₁ D₂ σ ρ hρ Bel)

/-- `BitCoh σ D₁ D₂` (`levelIsZero (σ u) = levelIsZero (σ v)`) directly at the pair measure
    `tyPairMeas Aw D₁ D₂`, from `Below Aw tbl (tyPairMeas Aw D₁ D₂)` and `EUT tbl σ ρ D₁ D₂`. -/
theorem bitCoh_of_below_and_eut (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw D₁ D₂))
    (heut : EUT tbl σ ρ D₁ D₂) :
    BitCoh σ D₁ D₂ :=
  bitCoh_of_sortCoh (sortCoh_of_below_and_eut Aw hW D₁ D₂ σ ρ hρ Bel heut)

theorem sortCoh_of_below_lex (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    {bound : List Nat × Nat} (hlex : LexDM (tyPairMeas Aw D₁ D₂) bound)
    (Bel : Below Aw tbl bound) (Bel_pair : Below Aw tbl (tyPairMeas Aw D₁ D₂)) :
    SortCoh σ D₁ D₂ :=
  sortCoh_of_below_and_eut Aw hW D₁ D₂ σ ρ hρ Bel_pair (Bel.eut D₁ D₂ σ ρ hρ hlex)

theorem bitCoh_of_below_lex (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    {bound : List Nat × Nat} (hlex : LexDM (tyPairMeas Aw D₁ D₂) bound)
    (Bel : Below Aw tbl bound) (Bel_pair : Below Aw tbl (tyPairMeas Aw D₁ D₂)) :
    BitCoh σ D₁ D₂ :=
  bitCoh_of_sortCoh (sortCoh_of_below_lex Aw hW D₁ D₂ σ ρ hρ hlex Bel Bel_pair)

/-- When `D.isSortOrPiHead = false`, `PBit σ ρ D DT` follows from `PBit σ ρ D D.reg.2`
    and `Below Aw tbl (tyPairMeas Aw D DT)` alone (since `lexDM_reg_pair_left` supplies
    `BitCoh σ D.reg.2 DT` via `Bel.bitCoh`). -/
theorem pbit_of_below_not_isSortOrPiHead (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (h : D.isSortOrPiHead = false) (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hpb_reg : PBit σ ρ D D.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw D DT)) :
    PBit σ ρ D DT :=
  pbit_of_reg_and_bitCoh D DT hpb_reg
    (Bel.bitCoh D.reg.2 DT σ ρ hρ (lexDM_reg_pair_left Aw D h DT))

/-- Helper for rule nodes of `CvP`: `1 < h.wt Aw` and `D.wt Aw < h.wt Aw` give
    `DMStep (D.atoms Aw ++ Y) (h.atoms Aw)` for any `Y` with `∀ y ∈ Y, y ≤ 1`. -/
theorem dmStep_cvp_rule_with_list (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CvP E n Γ a b T) (ht : h.isTransport = false)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat}
    (D : TyP E' n' Γ' e' T') (hlt : D.wt Aw < h.wt Aw)
    {Y : List Nat} (hY : ∀ y ∈ Y, y ≤ 1) :
    DMStep (D.atoms Aw ++ Y) (h.atoms Aw) := by
  have hp := TyP.wt_pos Aw D
  have hw1 : 1 < h.wt Aw := by omega
  rw [CvP.atoms_rule Aw h ht, ← List.append_nil (D.atoms Aw ++ Y)]
  refine dmStep_of_below ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw D hlt y hy
  · exact Nat.lt_of_le_of_lt (hY y hy) hw1

/-- Structural induction principle for `CvP` that groups all 19 rule nodes (`h.isTransport = false`)
    into a single base obligation `hrule` and recurses only on the 5 transport constructors. -/
theorem CvP.elab_transports
    {P : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} → CvP E n Γ a b T → Prop}
    (hrule : ∀ {E n Γ a b T} (h : CvP E n Γ a b T), h.isTransport = false → P h)
    (hwk : ∀ {E n Γ a b T d c} (h : CvP E n Γ a b T), P h → P (.wk E n Γ a b T d c h))
    (hesub : ∀ {E n Γ a b T t v j u} (h : CvP E n Γ a b T) (hget hv hvT),
      P h → P (.esub E n Γ a b T t v j u h hget hv hvT))
    (hlinst : ∀ {E a' n Γ a b T ls hls hlen} (h : CvP E a' Γ a b T),
      P h → P (.linst E a' n Γ a b T ls hls hlen h))
    (hewk : ∀ {E₀ E n Γ a b T hext} (h : CvP E₀ n Γ a b T),
      P h → P (.ewk E₀ E n Γ a b T hext h))
    (hcctx : ∀ {E n Γ a b T A A' u} (h : CvP E n (.assumption A :: Γ) a b T) (hA),
      P h → P (.cctx E n Γ a b T A A' u h hA)) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    (h : CvP E n Γ a b T) → P h
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h =>
      hwk h (CvP.elab_transports hrule hwk hesub hlinst hewk hcctx h)
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h hget hv hvT =>
      hesub h hget hv hvT (CvP.elab_transports hrule hwk hesub hlinst hewk hcctx h)
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h =>
      hlinst h (CvP.elab_transports hrule hwk hesub hlinst hewk hcctx h)
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h =>
      hewk h (CvP.elab_transports hrule hwk hesub hlinst hewk hcctx h)
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA =>
      hcctx h hA (CvP.elab_transports hrule hwk hesub hlinst hewk hcctx h)
  | _, _, _, _, _, _, .refl E n Γ a A ht dl dr =>
      hrule (CvP.refl E n Γ a A ht dl dr) rfl
  | _, _, _, _, _, _, .symm E n Γ a b A h dl dr =>
      hrule (CvP.symm E n Γ a b A h dl dr) rfl
  | _, _, _, _, _, _, .trans E n Γ a b c A h1 h2 dl dr =>
      hrule (CvP.trans E n Γ a b c A h1 h2 dl dr) rfl
  | _, _, _, _, _, _, .beta E n Γ A body arg B u hA hbody harg dl dr =>
      hrule (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) rfl
  | _, _, _, _, _, _, .zeta E n Γ A value body B u hA hv hb dl dr =>
      hrule (CvP.zeta E n Γ A value body B u hA hv hb dl dr) rfl
  | _, _, _, _, _, _, .zetaLocal E n Γ i A v hval hty hv dl dr =>
      hrule (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) rfl
  | _, _, _, _, _, _, .delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr =>
      hrule (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) rfl
  | _, _, _, _, _, _, .iota E n Γ lhs rhs T h hlhs hrhs dl dr =>
      hrule (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) rfl
  | _, _, _, _, _, _, .lit E n Γ t exp T h hexp dl dr =>
      hrule (CvP.lit E n Γ t exp T h hexp dl dr) rfl
  | _, _, _, _, _, _, .app E n Γ f g a b A B h1 h2 dl dr =>
      hrule (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl
  | _, _, _, _, _, _, .lam E n Γ A A' b b' B u hA hb dl dr =>
      hrule (CvP.lam E n Γ A A' b b' B u hA hb dl dr) rfl
  | _, _, _, _, _, _, .pi E n Γ A A' B B' u v hA hB dl dr =>
      hrule (CvP.pi E n Γ A A' B B' u v hA hB dl dr) rfl
  | _, _, _, _, _, _, .letE E n Γ A A' v v' b b' B u hA hv hb dl dr =>
      hrule (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) rfl
  | _, _, _, _, _, _, .sorts E n Γ l₁ l₂ h dl dr =>
      hrule (CvP.sorts E n Γ l₁ l₂ h dl dr) rfl
  | _, _, _, _, _, _, .consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr =>
      hrule (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr) rfl
  | _, _, _, _, _, _, .eta E n Γ f A B h dl dr =>
      hrule (CvP.eta E n Γ f A B h dl dr) rfl
  | _, _, _, _, _, _, .irr E n Γ P p q hP hp hq dl dr =>
      hrule (CvP.irr E n Γ P p q hP hp hq dl dr) rfl
  | _, _, _, _, _, _, .tyConv E n Γ a b A A' u h hA dl dr =>
      hrule (CvP.tyConv E n Γ a b A A' u h hA dl dr) rfl
  | _, _, _, _, _, _, .fsub E n Γ A B S a b u hB hA hab dl dr =>
      hrule (CvP.fsub E n Γ A B S a b u hB hA hab dl dr) rfl

/-- For **every** `h : CvP E n Γ a b T` (all 24 constructors, including all 5 transports),
    `DMStep (h.dl.atoms Aw) (h.atoms Aw)` holds unconditionally. -/
theorem dmStep_cvp_dl (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) : DMStep (h.dl.atoms Aw) (h.atoms Aw) :=
  CvP.elab_transports
    (P := fun k => DMStep (k.dl.atoms Aw) (k.atoms Aw))
    (fun k ht => dmStep_ty_below Aw k ht k.dl (CvP.wt_dl_lt Aw k))
    (fun _ ih => ih)
    (fun _ _ hv hvT ih =>
      dmStep_append_right (dmStep_append_right ih (hv.atoms Aw)) (hvT.atoms Aw))
    (fun _ ih => ih)
    (fun _ ih => ih)
    (fun _ hA ih => dmStep_append_right ih (hA.atoms Aw))
    h

/-- For **every** `h : CvP E n Γ a b T` (all 24 constructors, including all 5 transports),
    `DMStep (h.dr.atoms Aw) (h.atoms Aw)` holds unconditionally. -/
theorem dmStep_cvp_dr (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) : DMStep (h.dr.atoms Aw) (h.atoms Aw) :=
  CvP.elab_transports
    (P := fun k => DMStep (k.dr.atoms Aw) (k.atoms Aw))
    (fun k ht => dmStep_ty_below Aw k ht k.dr (CvP.wt_dr_lt Aw k))
    (fun _ ih => ih)
    (fun _ _ hv hvT ih =>
      dmStep_append_right (dmStep_append_right ih (hv.atoms Aw)) (hvT.atoms Aw))
    (fun _ ih => ih)
    (fun _ ih => ih)
    (fun _ hA ih => dmStep_append_right ih (hA.atoms Aw))
    h

/-- For **every** `h : CvP E n Γ a b T` and any `Y` with `∀ y ∈ Y, y ≤ 1`,
    `DMStep (h.dl.reg.2.atoms Aw ++ Y) (h.atoms Aw)` holds unconditionally. -/
theorem dmStep_cvp_dl_reg (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) {Y : List Nat} (hY : ∀ y ∈ Y, y ≤ 1) :
    DMStep (h.dl.reg.2.atoms Aw ++ Y) (h.atoms Aw) :=
  CvP.elab_transports
    (P := fun k => DMStep (k.dl.reg.2.atoms Aw ++ Y) (k.atoms Aw))
    (fun k ht => dmStep_cvp_rule_with_list Aw k ht k.dl.reg.2
      (Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw k.dl) (CvP.wt_dl_lt Aw k)) hY)
    (fun _ ih => ih)
    (fun _ _ _ _ ih => dmStep_append_middle2 ih)
    (fun _ ih => ih)
    (fun _ ih => ih)
    (fun _ _ ih => dmStep_append_middle ih)
    h

/-- For **every** `h : CvP E n Γ a b T` and any `Y` with `∀ y ∈ Y, y ≤ 1`,
    `DMStep (h.dr.reg.2.atoms Aw ++ Y) (h.atoms Aw)` holds unconditionally. -/
theorem dmStep_cvp_dr_reg (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) {Y : List Nat} (hY : ∀ y ∈ Y, y ≤ 1) :
    DMStep (h.dr.reg.2.atoms Aw ++ Y) (h.atoms Aw) :=
  CvP.elab_transports
    (P := fun k => DMStep (k.dr.reg.2.atoms Aw ++ Y) (k.atoms Aw))
    (fun k ht => dmStep_cvp_rule_with_list Aw k ht k.dr.reg.2
      (Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw k.dr) (CvP.wt_dr_lt Aw k)) hY)
    (fun _ ih => ih)
    (fun _ _ _ _ ih => dmStep_append_middle2 ih)
    (fun _ ih => ih)
    (fun _ ih => ih)
    (fun _ _ ih => dmStep_append_middle ih)
    h

/-- For any `h : CvP E n Γ a b T` and `D : TyP E' n' Γ' e' T'`,
    `DMStep (h.dl.atoms Aw ++ D.atoms Aw) (h.atoms Aw ++ D.atoms Aw)`. -/
theorem dmStep_cts_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} (h : CvP E n Γ a b T)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat} (D : TyP E' n' Γ' e' T') :
    DMStep (h.dl.atoms Aw ++ D.atoms Aw) (h.atoms Aw ++ D.atoms Aw) :=
  dmStep_append_right (dmStep_cvp_dl Aw h) (D.atoms Aw)

/-- `tyPairMeas Aw h.dl DX` is strictly `LexDM`-below `cvTyMeas Aw h DX` for every `h` and `DX`. -/
theorem lexDM_cts_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} (h : CvP E n Γ a b T)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat} (D : TyP E' n' Γ' e' T') :
    LexDM (tyPairMeas Aw h.dl D) (cvTyMeas Aw h D) :=
  lex_of_dm (dmStep_cts_pair Aw h D)

/-- Left-endpoint `CL(h.dl.reg.2, TyP.sort)` is strictly `LexDM`-below `cvTyMeas Aw h DX`
    for **every** `h : CvP E n Γ X Y (.sort w)` and `DX : TyP E n Γ X (.sort s)`. -/
theorem cl_reg_sort_of_below_cts_left (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvTyMeas Aw h DX)) :
    CL tbl σ ρ h.dl.reg.2 (TyP.sort E n Γ w (.succ w) (eqN_refl _)) := by
  have hstep : DMStep
      (h.dl.reg.2.atoms Aw ++ (TyP.sort E n Γ w (.succ w) (eqN_refl _)).atoms Aw)
      (h.atoms Aw) := by
    refine dmStep_cvp_dl_reg Aw h ?_
    intro y hy
    simp only [TyP.atoms, List.mem_singleton] at hy
    subst hy
    exact Nat.le_refl 1
  exact Bel.cl h.dl.reg.2 (TyP.sort E n Γ w (.succ w) (eqN_refl _)) σ ρ hρ
    (lex_of_dm (dmStep_drop_right hstep (DX.atoms Aw)))

/-- Right-typing `CL(DX.reg.2, TyP.sort)` at `cvTyMeas Aw h DX`. -/
theorem cl_reg_sort_of_below_cts_right (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvTyMeas Aw h DX)) :
    CL tbl σ ρ DX.reg.2 (TyP.sort E n Γ s (.succ s) (eqN_refl _)) := by
  cases hDX : DX.isSortOrPiHead with
  | true => exact cl_reg_sort_of_isSortOrPiHead tbl DX hDX σ ρ
  | false =>
      exact Bel.cl DX.reg.2 (TyP.sort E n Γ s (.succ s) (eqN_refl _)) σ ρ hρ
        (lex_of_dm (dmStep_drop_left (dmStep_reg_sort_pair Aw DX hDX) (h.atoms Aw)))

/-- `CTS h DX` (`eqN s w`) directly at its pack measure `cvTyMeas Aw h DX`, discharged
    from `Below Aw tbl (cvTyMeas Aw h DX)`, `TableWF tbl`, and `DispFor id E n Γ ρ`. -/
theorem cts_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (ρ : List Disp) (hρ : DispFor id E n Γ ρ)
    (Bel : Below Aw tbl (cvTyMeas Aw h DX)) :
    CTS h DX :=
  cts_of_eut_cl hW h DX ρ
    (Bel.eut h.dl DX id ρ hρ (lexDM_cts_pair Aw h DX))
    (cl_reg_sort_of_below_cts_left Aw tbl h DX id ρ hρ Bel)
    (cl_reg_sort_of_below_cts_right Aw tbl h DX id ρ hρ Bel)

/-- Whether the head leaf of `D : TyP E n Γ e T` (under the 6 transport constructors) is `.sort`.
    Unlike `isSortOrPiHead`, `.pi` has `isSortHead = false` because `(TyP.pi ... hA hB).wt Aw ≥ 3 > 1 =
    (TyP.pi ... hA hB).reg.2.wt Aw`. -/
def TyP.isSortHead : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → Bool
  | _, _, _, _, _, .sort .. => true
  | _, _, _, _, _, .pi .. => false
  | _, _, _, _, _, .bvar .. => false
  | _, _, _, _, _, .const .. => false
  | _, _, _, _, _, .lam .. => false
  | _, _, _, _, _, .app .. => false
  | _, _, _, _, _, .letE .. => false
  | _, _, _, _, _, .lit .. => false
  | _, _, _, _, _, .conv .. => false
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => D.isSortHead
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ _ _ => D.isSortHead
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ _ _ => D.isSortHead
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => D.isSortHead
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.isSortHead
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.isSortHead

/-- When `D.isSortHead = false` (all 8 non-`.sort` leaves under transports, **including `.pi`**),
    `D.reg.2.atoms Aw ++ Y` is a `DMStep` strictly below `D.atoms Aw` for any `Y` with `∀ y ∈ Y, y ≤ 1`. -/
theorem dmStep_reg_of_not_isSortHead (Aw : Nat → Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortHead = false →
    {Y : List Nat} → (∀ y ∈ Y, y ≤ 1) →
    DMStep (D.reg.2.atoms Aw ++ Y) (D.atoms Aw)
  | _, _, _, _, _, .sort .., h, _, _ => Bool.noConfusion h
  | _, _, _, _, _, .pi E n Γ A u B v hA hB, _, _, hY => by
      have hp := TyP.wt_pos Aw hA
      exact dmStep_reg_nonTransport Aw (.pi E n Γ A u B v hA hB)
        (by simp only [TyP.wt]; omega)
        (by simp only [TyP.reg, TyP.wt]; omega)
        rfl hY
  | _, _, _, _, _, .bvar E n Γ i A u hget hA, _, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw (.bvar E n Γ i A u hget hA) rfl hY
  | _, _, _, _, _, .const E n Γ r ls m ls₀ u hres hlen hwf hwf₀ hT, _, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw (.const E n Γ r ls m ls₀ u hres hlen hwf hwf₀ hT) rfl hY
  | _, _, _, _, _, .lam E n Γ A body B u v hA hb hB, _, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw (.lam E n Γ A body B u v hA hb hB) rfl hY
  | _, _, _, _, _, .app E n Γ f a A B u hf ha hT, _, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw (.app E n Γ f a A B u hf ha hT) rfl hY
  | _, _, _, _, _, .letE E n Γ A value body B u v hA hv hb hT, _, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw (.letE E n Γ A value body B u v hA hv hb hT) rfl hY
  | _, _, _, _, _, .lit E n Γ t A hexp, _, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw (.lit E n Γ t A hexp) rfl hY
  | _, _, _, _, _, .conv E n Γ e A B u hd hc, _, _, hY =>
      dmStep_reg_of_not_isSortOrPiHead Aw (.conv E n Γ e A B u hd hc) rfl hY
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D', h, _, hY =>
      dmStep_reg_of_not_isSortHead Aw D' h hY
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D' _ _ _, h, _, hY =>
      dmStep_append_middle2 (dmStep_reg_of_not_isSortHead Aw D' h hY)
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D' _ _ _, h, _, hY =>
      dmStep_append_middle2 (dmStep_reg_of_not_isSortHead Aw D' h hY)
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D', h, _, hY =>
      dmStep_reg_of_not_isSortHead Aw D' h hY
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D', h, _, hY =>
      dmStep_reg_of_not_isSortHead Aw D' h hY
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D' _, h, _, hY =>
      dmStep_append_middle (dmStep_reg_of_not_isSortHead Aw D' h hY)

theorem dmStep_reg_atoms_of_not_isSortHead (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (h : D.isSortHead = false) :
    DMStep (D.reg.2.atoms Aw) (D.atoms Aw) := by
  simpa only [List.append_nil] using
    dmStep_reg_of_not_isSortHead Aw D h (Y := []) (fun _ hy => nomatch hy)

theorem lexDM_reg_pair_left_of_not_isSortHead (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (h : D.isSortHead = false)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat}
    (DT : TyP E' n' Γ' e' T') :
    LexDM (tyPairMeas Aw D.reg.2 DT) (tyPairMeas Aw D DT) :=
  lex_of_dm (dmStep_append_right (dmStep_reg_atoms_of_not_isSortHead Aw D h) (DT.atoms Aw))

/-- When `D.isSortHead = false` (every leaf except `.sort`, **including `.pi`**),
    `PBit σ ρ D DT` follows from `PBit σ ρ D D.reg.2` and `Below Aw tbl (tyPairMeas Aw D DT)` alone. -/
theorem pbit_of_below_not_isSortHead (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (h : D.isSortHead = false) (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hpb_reg : PBit σ ρ D D.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw D DT)) :
    PBit σ ρ D DT :=
  pbit_of_reg_and_bitCoh D DT hpb_reg
    (Bel.bitCoh D.reg.2 DT σ ρ hρ (lexDM_reg_pair_left_of_not_isSortHead Aw D h DT))

/-- For any `D : TyP E n Γ e T` whose head leaf is `.pi` (`D.isSortOrPiHead = true` and
    `D.isSortHead = false`), `PBit σ ρ D DT` follows from `Below Aw tbl (tyPairMeas Aw D DT)`
    and `DispFor σ E n Γ ρ` alone (with zero `PBit` recursive calls). -/
theorem pbit_of_below_piHead (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (hsp : D.isSortOrPiHead = true) (hs : D.isSortHead = false)
    (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw D DT)) :
    PBit σ ρ D DT :=
  pbit_of_below_not_isSortHead Aw tbl D hs DT σ ρ hρ
    (pbit_reg_of_isSortOrPiHead hsp hρ.levelSub ρ) Bel

end Rcic.Syn
