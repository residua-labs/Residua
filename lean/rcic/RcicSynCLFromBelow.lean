import rcic.RcicSynAppBvarPBit

/-!
# Syntactic sortRow, build step 4i — Same-Constructor and Transport `CL` & `EUT` Discharged from `Below`

`research/rcic/semantic/S3_ES_ARMS.md` §58. Building on `RcicSynPiWalk`,
`RcicSynLetTransportCL`, `RcicSynSortRow`, and `RcicSynAppBvarPBit`, this module
discharges the same-constructor and same-transport `CL` and `EUT` obligations
across `TyP` directly from `Below Aw tbl (tyPairMeas Aw D₁ D₂)`:

1. **§1 `DMStep` Pair-Decrease Combinators and `LevelHom` `eqN`-Congruences**:
   - `dmStep_append_both`, `dmStep_wt_lt_singleton`, `dmStep_wt_lt_pair`,
     `lexDM_wt_lt_pair`, `dmStep_both_wt_lt_singleton`, `lexDM_both_wt_lt_left`,
     `lexDM_both_wt_lt_right`, `dmStep_drop_right_nonempty`, `getElem?_keep_or_not_keep`.
   - `LevelHom.succ_eqN`, `LevelHom.max_eqN`, `LevelHom.imax_eqN`.

2. **§2 Same-Constructor `CL` and `EUT` from `Below` (`sort`, `bvar`, `const`, `pi`, `lam`, `app`, `letE`, `lit`, `conv`)**:
   - `cl_sort_of_below`, `eut_sort_of_below`: `TyP.sort` `CL` and `EUT`.
   - `cl_bvar_of_below`, `eut_bvar_of_below`: `TyP.bvar` `CL` and `EUT` from `Bel` alone.
   - `cl_const_of_below_eq`, `eut_const_of_below_eq`, `cl_const_canon_of_below`,
     `eut_const_canon_of_below`: `TyP.const` `CL` and `EUT` from `Bel`.
   - `cl_pi_of_below`, `eut_pi_of_below`: `TyP.pi` `CL` and `EUT` from `Bel`.
   - `cl_lam_of_below_bit`, `cl_lam_same_cod_of_below`, `eut_lam_of_below`:
     `TyP.lam` `CL` and `EUT` from `Bel` (`eut_lam_of_below` holds for **arbitrary**
     codomain expressions `B₁, B₂` with zero `B₁ = B₂` or `TableWF` hypothesis).
   - `cl_app_of_below_bits`, `cl_app_same_pi_of_below`, `eut_app_same_pi_of_below`,
     `eut_app_of_below_got_drop`, `eut_app_of_below_got_keep`: `TyP.app` `CL` and `EUT` from `Bel`.
   - `cl_letE_of_below`, `eut_letE_of_below`: `TyP.letE` `CL` and `EUT` from `Bel`
     via Option L-inline-at-0 (`letSub`) in `Γ` for **arbitrary** `B₁, B₂` with
     zero `.letBinding` context extension and zero `TableWF` hypothesis.
   - `cl_lit_of_below`, `eut_lit_of_below`: `TyP.lit` `CL` and `EUT` from `Bel`
     for arbitrary `T₁, T₂`.
   - `cl_conv_left_of_below`, `cl_conv_right_of_below`, `eut_conv_left_of_below`,
     `eut_conv_right_of_below`: `TyP.conv` `CL` and `EUT` against any `D₂` / `D₁`
     from `Bel` alone.

3. **§3 Same-Transport `CL` and `EUT` from `Below` (`ewk`, `linst`, `wk`, `cctx`, `esub`)**:
   - `cl_ewk_both_of_below`, `eut_ewk_both_of_below`, `cl_linst_both_of_below`,
     `eut_linst_both_of_below`, `cl_wk_both_of_below`, `eut_wk_both_of_below`,
     `cl_cctx_both_of_below`, `eut_cctx_both_of_below`, `cl_esub_both_of_below`,
     `eut_esub_both_of_below`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `DMStep` Pair-Decrease Combinators and `LevelHom` `eqN`-Congruences -/

/-- Two-sided `DMStep` composition: if `DMStep as₁ bs₁` and `DMStep as₂ bs₂`,
    then `DMStep (as₁ ++ as₂) (bs₁ ++ bs₂)`. -/
theorem dmStep_append_both {as₁ bs₁ as₂ bs₂ : List Nat}
    (h₁ : DMStep as₁ bs₁) (h₂ : DMStep as₂ bs₂) :
    DMStep (as₁ ++ as₂) (bs₁ ++ bs₂) := by
  obtain ⟨X₁, Y₁, Z₁, hne₁, hpB₁, hpA₁, hlt₁⟩ := h₁
  obtain ⟨X₂, Y₂, Z₂, _, hpB₂, hpA₂, hlt₂⟩ := h₂
  refine ⟨X₁ ++ X₂, Y₁ ++ Y₂, Z₁ ++ Z₂, ?_, ?_, ?_, ?_⟩
  · intro hnil
    exact hne₁ (List.append_eq_nil.mp hnil).1
  · refine (hpB₁.append hpB₂).trans ?_
    rw [List.append_assoc, List.append_assoc]
    refine List.Perm.append_left X₁ ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right Z₂ List.perm_append_comm
  · refine (hpA₁.append hpA₂).trans ?_
    rw [List.append_assoc, List.append_assoc]
    refine List.Perm.append_left Y₁ ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right Z₂ List.perm_append_comm
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨x, hx, hlt⟩ := hlt₁ y hy
      exact ⟨x, List.mem_append_left X₂ hx, hlt⟩
    · obtain ⟨x, hx, hlt⟩ := hlt₂ y hy
      exact ⟨x, List.mem_append_right X₁ hx, hlt⟩

/-- Dropping a non-empty suffix `Y` from `X ++ Y` is a `DMStep`. -/
theorem dmStep_drop_right_nonempty (X : List Nat) {Y : List Nat} (hY : Y ≠ []) :
    DMStep X (X ++ Y) :=
  dmStep_perm_right List.perm_append_comm (dmStep_drop hY)

/-- Any typing `X` with `X.wt Aw < D.wt Aw` has `DMStep (X.atoms Aw) (D.atoms Aw)`
    whenever `D.atoms Aw = [D.wt Aw]`. -/
theorem dmStep_wt_lt_singleton (Aw : Nat → Nat)
    {E₁ E₂ : ResolvedEnv} {n₁ n₂ : Nat} {Γ₁ Γ₂ : LCtx} {e₁ T₁ e₂ T₂ : Expr Nat}
    (X : TyP E₁ n₁ Γ₁ e₁ T₁) (D : TyP E₂ n₂ Γ₂ e₂ T₂)
    (hat : D.atoms Aw = [D.wt Aw]) (hw : X.wt Aw < D.wt Aw) :
    DMStep (X.atoms Aw) (D.atoms Aw) := by
  rw [hat, ← List.append_nil (X.atoms Aw)]
  exact dmStep_of_below (atoms_lt_of_wt_lt Aw X hw)

/-- Any pair `(X₁, X₂)` with `X₁.wt Aw < D₁.wt Aw` and `X₂.wt Aw < D₂.wt Aw`
    satisfies `DMStep (X₁.atoms Aw ++ X₂.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw)`
    whenever `D₁` and `D₂` are single-atom nodes. -/
theorem dmStep_wt_lt_pair (Aw : Nat → Nat)
    {E₁ E₂ E₃ E₄ : ResolvedEnv} {n₁ n₂ n₃ n₄ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ : LCtx}
    {e₁ T₁ e₂ T₂ e₃ T₃ e₄ T₄ : Expr Nat}
    (X₁ : TyP E₁ n₁ Γ₁ e₁ T₁) (X₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (D₁ : TyP E₃ n₃ Γ₃ e₃ T₃) (D₂ : TyP E₄ n₄ Γ₄ e₄ T₄)
    (hat₁ : D₁.atoms Aw = [D₁.wt Aw]) (hat₂ : D₂.atoms Aw = [D₂.wt Aw])
    (hw₁ : X₁.wt Aw < D₁.wt Aw) (hw₂ : X₂.wt Aw < D₂.wt Aw) :
    DMStep (X₁.atoms Aw ++ X₂.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) :=
  dmStep_append_both
    (dmStep_wt_lt_singleton Aw X₁ D₁ hat₁ hw₁)
    (dmStep_wt_lt_singleton Aw X₂ D₂ hat₂ hw₂)

theorem lexDM_wt_lt_pair (Aw : Nat → Nat)
    {E₁ E₂ E₃ E₄ : ResolvedEnv} {n₁ n₂ n₃ n₄ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ : LCtx}
    {e₁ T₁ e₂ T₂ e₃ T₃ e₄ T₄ : Expr Nat}
    (X₁ : TyP E₁ n₁ Γ₁ e₁ T₁) (X₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (D₁ : TyP E₃ n₃ Γ₃ e₃ T₃) (D₂ : TyP E₄ n₄ Γ₄ e₄ T₄)
    (hat₁ : D₁.atoms Aw = [D₁.wt Aw]) (hat₂ : D₂.atoms Aw = [D₂.wt Aw])
    (hw₁ : X₁.wt Aw < D₁.wt Aw) (hw₂ : X₂.wt Aw < D₂.wt Aw) :
    LexDM (tyPairMeas Aw X₁ X₂) (tyPairMeas Aw D₁ D₂) :=
  lex_of_dm (dmStep_wt_lt_pair Aw X₁ X₂ D₁ D₂ hat₁ hat₂ hw₁ hw₂)

/-- When both `X₁.wt Aw < D.wt Aw` and `X₂.wt Aw < D.wt Aw` for a single-atom node `D`,
    `DMStep (X₁.atoms Aw ++ X₂.atoms Aw) (D.atoms Aw)` holds. -/
theorem dmStep_both_wt_lt_singleton (Aw : Nat → Nat)
    {E₁ E₂ E₃ : ResolvedEnv} {n₁ n₂ n₃ : Nat} {Γ₁ Γ₂ Γ₃ : LCtx}
    {e₁ T₁ e₂ T₂ e₃ T₃ : Expr Nat}
    (X₁ : TyP E₁ n₁ Γ₁ e₁ T₁) (X₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (D : TyP E₃ n₃ Γ₃ e₃ T₃)
    (hat : D.atoms Aw = [D.wt Aw])
    (hw₁ : X₁.wt Aw < D.wt Aw) (hw₂ : X₂.wt Aw < D.wt Aw) :
    DMStep (X₁.atoms Aw ++ X₂.atoms Aw) (D.atoms Aw) := by
  rw [hat, ← List.append_nil (X₁.atoms Aw ++ X₂.atoms Aw)]
  refine dmStep_of_below ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw X₁ hw₁ y hy
  · exact atoms_lt_of_wt_lt Aw X₂ hw₂ y hy

theorem lexDM_both_wt_lt_left (Aw : Nat → Nat)
    {E₁ E₂ E₃ E₄ : ResolvedEnv} {n₁ n₂ n₃ n₄ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ : LCtx}
    {e₁ T₁ e₂ T₂ e₃ T₃ e₄ T₄ : Expr Nat}
    (X₁ : TyP E₁ n₁ Γ₁ e₁ T₁) (X₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (D₁ : TyP E₃ n₃ Γ₃ e₃ T₃) (D₂ : TyP E₄ n₄ Γ₄ e₄ T₄)
    (hat₁ : D₁.atoms Aw = [D₁.wt Aw])
    (hw₁ : X₁.wt Aw < D₁.wt Aw) (hw₂ : X₂.wt Aw < D₁.wt Aw) :
    LexDM (tyPairMeas Aw X₁ X₂) (tyPairMeas Aw D₁ D₂) :=
  lex_of_dm (dmStep_drop_right (dmStep_both_wt_lt_singleton Aw X₁ X₂ D₁ hat₁ hw₁ hw₂) (D₂.atoms Aw))

theorem lexDM_both_wt_lt_right (Aw : Nat → Nat)
    {E₁ E₂ E₃ E₄ : ResolvedEnv} {n₁ n₂ n₃ n₄ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ : LCtx}
    {e₁ T₁ e₂ T₂ e₃ T₃ e₄ T₄ : Expr Nat}
    (X₁ : TyP E₁ n₁ Γ₁ e₁ T₁) (X₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (D₁ : TyP E₃ n₃ Γ₃ e₃ T₃) (D₂ : TyP E₄ n₄ Γ₄ e₄ T₄)
    (hat₂ : D₂.atoms Aw = [D₂.wt Aw])
    (hw₁ : X₁.wt Aw < D₂.wt Aw) (hw₂ : X₂.wt Aw < D₂.wt Aw) :
    LexDM (tyPairMeas Aw X₁ X₂) (tyPairMeas Aw D₁ D₂) :=
  lex_of_dm (dmStep_drop_left (dmStep_both_wt_lt_singleton Aw X₁ X₂ D₂ hat₂ hw₁ hw₂) (D₁.atoms Aw))

/-- Every index `c` in `ρ : List Disp` either has `ρ[c]? = some .keep` or
    `ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v)`. -/
theorem getElem?_keep_or_not_keep (ρ : List Disp) (c : Nat) :
    ρ[c]? = some .keep ∨
      (ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v)) := by
  cases h : ρ[c]? with
  | none => exact Or.inr (Or.inl rfl)
  | some d =>
      cases d with
      | keep => exact Or.inl rfl
      | drop => exact Or.inr (Or.inr (Or.inl rfl))
      | inline v => exact Or.inr (Or.inr (Or.inr ⟨v, rfl⟩))

/-- `LevelHom.succ_eqN`: if `eqN (σ u₁) (σ u₂)`, then `eqN (σ (.succ u₁)) (σ (.succ u₂))`. -/
theorem LevelHom.succ_eqN {σ : Level → Level} (hσ : LevelHom σ)
    {u₁ u₂ : Level} (hu : eqN (σ u₁) (σ u₂)) :
    eqN (σ (.succ u₁)) (σ (.succ u₂)) := by
  intro val
  simp only [hσ.map_succ, eval, hu val]

/-- `LevelHom.max_eqN`: if `eqN (σ u₁) (σ u₂)` and `eqN (σ v₁) (σ v₂)`,
    then `eqN (σ (.max u₁ v₁)) (σ (.max u₂ v₂))`. -/
theorem LevelHom.max_eqN {σ : Level → Level} (hσ : LevelHom σ)
    {u₁ u₂ v₁ v₂ : Level} (hu : eqN (σ u₁) (σ u₂)) (hv : eqN (σ v₁) (σ v₂)) :
    eqN (σ (.max u₁ v₁)) (σ (.max u₂ v₂)) := by
  intro val
  simp only [hσ.map_max, eval, hu val, hv val]

/-- `LevelHom.imax_eqN`: if `eqN (σ u₁) (σ u₂)` and `eqN (σ v₁) (σ v₂)`,
    then `eqN (σ (.imax u₁ v₁)) (σ (.imax u₂ v₂))`. -/
theorem LevelHom.imax_eqN {σ : Level → Level} (hσ : LevelHom σ)
    {u₁ u₂ v₁ v₂ : Level} (hu : eqN (σ u₁) (σ u₂)) (hv : eqN (σ v₁) (σ v₂)) :
    eqN (σ (.imax u₁ v₁)) (σ (.imax u₂ v₂)) := by
  intro val
  simp only [hσ.map_imax, eval, hu val, hv val]

/-! ## §2 Same-Constructor `CL` and `EUT` from `Below` -/

/-- `CL` on two `TyP.sort` nodes at the same `l`. -/
theorem cl_sort_of_below (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k₁ k₂ : Level}
    (h₁ : eqN k₁ (.succ l)) (h₂ : eqN k₂ (.succ l)) :
    CL tbl σ ρ (TyP.sort E n Γ l k₁ h₁) (TyP.sort E n Γ l k₂ h₂) :=
  cl_sort_nodes tbl σ ρ h₁ h₂

/-- `EUT` on two `TyP.sort` nodes at the same `l` from `DispFor σ E n Γ ρ`. -/
theorem eut_sort_of_below (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k₁ k₂ : Level}
    (h₁ : eqN k₁ (.succ l)) (h₂ : eqN k₂ (.succ l))
    (hρ : DispFor σ E n Γ ρ) :
    EUT tbl σ ρ (TyP.sort E n Γ l k₁ h₁) (TyP.sort E n Γ l k₂ h₂) :=
  eut_sort_nodes tbl hρ.levelSub ρ h₁ h₂

/-- `CL` on two `TyP.bvar` nodes at the same index `i` from `Below` alone. -/
theorem cl_bvar_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A₁ A₂ : Expr Nat} {u₁ u₂ : Level}
    (hlook₁ : lookupType Γ i = some A₁) (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hlook₂ : lookupType Γ i = some A₂) (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁) (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂))) :
    CL tbl σ ρ (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁) (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂) := by
  have hAeq : A₁ = A₂ := Option.some.inj (hlook₁.symm.trans hlook₂)
  subst hAeq
  have hw₁ : hA₁.wt Aw < (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hbit : BitCoh σ hA₁ hA₂ :=
    Bel.bitCoh hA₁ hA₂ σ ρ hρ
      (lexDM_wt_lt_pair Aw hA₁ hA₂
        (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁) (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂)
        rfl rfl hw₁ hw₂)
  exact cl_bvar_nodes tbl σ ρ hlook₁ hA₁ hlook₂ hA₂ hbit

/-- `EUT` on two `TyP.bvar` nodes at the same index `i` from `Below` alone. -/
theorem eut_bvar_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A₁ A₂ : Expr Nat} {u₁ u₂ : Level}
    (hlook₁ : lookupType Γ i = some A₁) (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hlook₂ : lookupType Γ i = some A₂) (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁) (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂))) :
    EUT tbl σ ρ (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁) (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂) := by
  have hAeq : A₁ = A₂ := Option.some.inj (hlook₁.symm.trans hlook₂)
  subst hAeq
  have hw₁ : hA₁.wt Aw < (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hcl : CL tbl σ ρ hA₁ hA₂ :=
    Bel.cl hA₁ hA₂ σ ρ hρ
      (lexDM_wt_lt_pair Aw hA₁ hA₂
        (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁) (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂)
        rfl rfl hw₁ hw₂)
  exact eut_bvar_nodes tbl σ ρ hlook₁ hA₁ hlook₂ hA₂ hcl

/-- `CL` on two `TyP.const` nodes at `(r, ls)` with `ls₁ = ls₂`, from `Below` alone. -/
theorem cl_const_of_below_eq (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₁ ls₂ : List Level}
    {m₁ m₂ : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁))
    (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m₂.mtype) (.sort u₂))
    (heq : ls₁ = ls₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂))) :
    CL tbl σ ρ
      (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
      (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) := by
  have hmeq : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
  subst hmeq
  subst heq
  have hw₁ : hT₁.wt Aw < (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hT₂.wt Aw < (TyP.const E n Γ r ls ls₁ m₁ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hbit : BitCoh σ hT₁ hT₂ :=
    Bel.bitCoh hT₁ hT₂ σ ρ hρ
      (lexDM_wt_lt_pair Aw hT₁ hT₂
        (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₁ m₁ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂)
        rfl rfl hw₁ hw₂)
  exact cl_const_nodes tbl σ ρ hres₁ hlen₁ hwf₁ hls₁ hT₁ hres₂ hlen₂ hwf₂ hls₂ hT₂ hbit

/-- `EUT` on two `TyP.const` nodes at `(r, ls)` with `ls₁ = ls₂`, from `Below` alone. -/
theorem eut_const_of_below_eq (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₁ ls₂ : List Level}
    {m₁ m₂ : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m₁.mtype) (.sort u₁))
    (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m₂.mtype) (.sort u₂))
    (heq : ls₁ = ls₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂))) :
    EUT tbl σ ρ
      (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
      (TyP.const E n Γ r ls ls₂ m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) := by
  have hmeq : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
  subst hmeq
  subst heq
  have hw₁ : hT₁.wt Aw < (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hT₂.wt Aw < (TyP.const E n Γ r ls ls₁ m₁ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hcl : CL tbl σ ρ hT₁ hT₂ :=
    Bel.cl hT₁ hT₂ σ ρ hρ
      (lexDM_wt_lt_pair Aw hT₁ hT₂
        (TyP.const E n Γ r ls ls₁ m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₁ m₁ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂)
        rfl rfl hw₁ hw₂)
  exact eut_const_nodes tbl σ ρ hres₁ hlen₁ hwf₁ hls₁ hT₁ hres₂ hlen₂ hwf₂ hls₂ hT₂ hcl

/-- Canonical specialization (`ls₁ = ls = ls₂`, as produced by `enrichHasTyT`) of `cl_const_of_below_eq`. -/
theorem cl_const_canon_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m₁ m₂ : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls)
    (hT₁ : TyP E n Γ (instantiateLevels ls m₁.mtype) (.sort u₁))
    (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls)
    (hT₂ : TyP E n Γ (instantiateLevels ls m₂.mtype) (.sort u₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.const E n Γ r ls ls m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂))) :
    CL tbl σ ρ
      (TyP.const E n Γ r ls ls m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
      (TyP.const E n Γ r ls ls m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) :=
  cl_const_of_below_eq Aw tbl hres₁ hlen₁ hwf₁ hls₁ hT₁ hres₂ hlen₂ hwf₂ hls₂ hT₂ rfl σ ρ hρ Bel

/-- Canonical specialization (`ls₁ = ls = ls₂`) of `eut_const_of_below_eq`. -/
theorem eut_const_canon_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m₁ m₂ : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m₁) (hlen₁ : ls.length = m₁.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls)
    (hT₁ : TyP E n Γ (instantiateLevels ls m₁.mtype) (.sort u₁))
    (hres₂ : E.members r = some m₂) (hlen₂ : ls.length = m₂.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls)
    (hT₂ : TyP E n Γ (instantiateLevels ls m₂.mtype) (.sort u₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.const E n Γ r ls ls m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂))) :
    EUT tbl σ ρ
      (TyP.const E n Γ r ls ls m₁ u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
      (TyP.const E n Γ r ls ls m₂ u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) :=
  eut_const_of_below_eq Aw tbl hres₁ hlen₁ hwf₁ hls₁ hT₁ hres₂ hlen₂ hwf₂ hls₂ hT₂ rfl σ ρ hρ Bel

/-- `CL` on two `TyP.pi` nodes on `(A, B)` from `Below` alone. -/
theorem cl_pi_of_below (Aw : Nat → Nat) (tbl : List CRule) (hTC : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂))) :
    CL tbl σ ρ (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂) := by
  let D₁ := TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁
  let D₂ := TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂
  have hwA₁ : hA₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwA₂ : hA₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwB₁ : hB₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwB₂ : hB₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hlexA := lexDM_wt_lt_pair Aw hA₁ hA₂ D₁ D₂ rfl rfl hwA₁ hwA₂
  have hlexB := lexDM_wt_lt_pair Aw hB₁ hB₂ D₁ D₂ rfl rfl hwB₁ hwB₂
  exact cl_pi_nodes tbl hTC σ ρ hA₁ hB₁ hA₂ hB₂
    (Bel.bitCoh hA₁ hA₂ σ ρ hρ hlexA)
    (Bel.cl hA₁ hA₂ σ ρ hρ hlexA)
    (Bel.cl hB₁ hB₂ σ (binderDisp (levelIsZero (σ u₁)) :: ρ) (hρ.assumption hA₁) hlexB)

/-- `EUT` on two `TyP.pi` nodes on `(A, B)` from `Below`, `TableWF tbl`, and `LevelHom σ`. -/
theorem eut_pi_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)))
    (Bel_A : Below Aw tbl (tyPairMeas Aw hA₁ hA₂))
    (Bel_B : Below Aw tbl (tyPairMeas Aw hB₁ hB₂)) :
    EUT tbl σ ρ (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂) := by
  let D₁ := TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁
  let D₂ := TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂
  have hwA₁ : hA₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwA₂ : hA₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwB₁ : hB₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwB₂ : hB₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hlexA := lexDM_wt_lt_pair Aw hA₁ hA₂ D₁ D₂ rfl rfl hwA₁ hwA₂
  have hlexB := lexDM_wt_lt_pair Aw hB₁ hB₂ D₁ D₂ rfl rfl hwB₁ hwB₂
  have hcohA : eqN (σ u₁) (σ u₂) :=
    sortCoh_of_below_lex Aw hW hA₁ hA₂ σ ρ hρ hlexA Bel Bel_A
  have hcohB : eqN (σ v₁) (σ v₂) :=
    sortCoh_of_below_lex Aw hW hB₁ hB₂ σ (binderDisp (levelIsZero (σ u₁)) :: ρ)
      (hρ.assumption hA₁) hlexB Bel Bel_B
  exact eut_pi_nodes tbl σ ρ hA₁ hB₁ hA₂ hB₂ (hσ.imax_eqN hcohA hcohB)

/-- `CL` on two `TyP.lam` nodes on `(A, body)` from `Below` and
    `hv_bit : levelIsZero (σ v₁) = levelIsZero (σ v₂)`. -/
theorem cl_lam_of_below_bit (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hv_bit : levelIsZero (σ v₁) = levelIsZero (σ v₂))
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂))) :
    CL tbl σ ρ
      (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) := by
  let D₁ := TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁
  let D₂ := TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂
  have hwA₁ : hA₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwA₂ : hA₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwb₁ : hb₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwb₂ : hb₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwB₁ : hB₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwB₂ : hB₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hlexA := lexDM_wt_lt_pair Aw hA₁ hA₂ D₁ D₂ rfl rfl hwA₁ hwA₂
  have hlexb := lexDM_wt_lt_pair Aw hb₁ hb₂ D₁ D₂ rfl rfl hwb₁ hwb₂
  have hbitA : BitCoh σ hA₁ hA₂ := Bel.bitCoh hA₁ hA₂ σ ρ hρ hlexA
  cases hu₁ : levelIsZero (σ u₁) with
  | true =>
      have hρ_drop : DispFor σ E n (.assumption A :: Γ) (.drop :: ρ) := by
        simpa only [hu₁, binderDisp] using hρ.assumption hA₁
      have hclb := Bel.cl hb₁ hb₂ σ (.drop :: ρ) hρ_drop hlexb
      exact cl_lam_nodes_drop tbl σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ hu₁ hbitA hclb
  | false =>
      have hρ_keep : DispFor σ E n (.assumption A :: Γ) (.keep :: ρ) := by
        simpa only [hu₁, binderDisp] using hρ.assumption hA₁
      have hpb₁ := Bel.pb hb₁ hB₁ σ (.keep :: ρ) hρ_keep
        (lexDM_both_wt_lt_left Aw hb₁ hB₁ D₁ D₂ rfl hwb₁ hwB₁)
      have hpb₂ := Bel.pb hb₂ hB₂ σ (.keep :: ρ) hρ_keep
        (lexDM_both_wt_lt_right Aw hb₂ hB₂ D₁ D₂ rfl hwb₂ hwB₂)
      cases hv₁ : levelIsZero (σ v₁) with
      | true =>
          have hv₂ : levelIsZero (σ v₂) = true := hv_bit.symm.trans hv₁
          exact cl_lam_nodes_keep_star tbl σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ hu₁ hbitA
            (hpb₁.mpr hv₁) (hpb₂.mpr hv₂)
      | false =>
          have hv₂ : levelIsZero (σ v₂) = false := hv_bit.symm.trans hv₁
          have hne₁ : hb₁.eps σ (.keep :: ρ) ≠ .star := by
            intro hs; exact Bool.noConfusion (hv₁.symm.trans (hpb₁.mp hs))
          have hne₂ : hb₂.eps σ (.keep :: ρ) ≠ .star := by
            intro hs; exact Bool.noConfusion (hv₂.symm.trans (hpb₂.mp hs))
          have hclb := Bel.cl hb₁ hb₂ σ (.keep :: ρ) hρ_keep hlexb
          exact cl_lam_nodes_keep tbl σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ hu₁ hbitA hne₁ hne₂ hclb

/-- When two `TyP.lam` nodes have the same codomain expression `B`, `Bel.bitCoh hB₁ hB₂`
    automatically supplies `levelIsZero (σ v₁) = levelIsZero (σ v₂)`, discharging
    `CL` from `Below` alone. -/
theorem cl_lam_same_cod_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B)
    (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B)
    (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.lam E n Γ A u₁ body B v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B v₂ hA₂ hb₂ hB₂))) :
    CL tbl σ ρ
      (TyP.lam E n Γ A u₁ body B v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B v₂ hA₂ hb₂ hB₂) := by
  let D₁ := TyP.lam E n Γ A u₁ body B v₁ hA₁ hb₁ hB₁
  let D₂ := TyP.lam E n Γ A u₂ body B v₂ hA₂ hb₂ hB₂
  have hwB₁ : hB₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwB₂ : hB₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hv_bit : BitCoh σ hB₁ hB₂ :=
    Bel.bitCoh hB₁ hB₂ σ (binderDisp (levelIsZero (σ u₁)) :: ρ) (hρ.assumption hA₁)
      (lexDM_wt_lt_pair Aw hB₁ hB₂ D₁ D₂ rfl rfl hwB₁ hwB₂)
  exact cl_lam_of_below_bit Aw tbl hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ σ ρ hρ hv_bit Bel

/-- `EUT` on **any** two `TyP.lam` nodes on `(A, body)` (even with distinct codomain
    expressions `B₁, B₂`!) from `Below` alone, chaining `Bel.cl hB₁ hb₁.reg.2`,
    `Bel.eut hb₁ hb₂`, and `Bel.cl hb₂.reg.2 hB₂`. -/
theorem eut_lam_of_below (Aw : Nat → Nat) (tbl : List CRule) (hTC : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂))) :
    EUT tbl σ ρ
      (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
      (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) := by
  let D₁ := TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁
  let D₂ := TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂
  have hwA₁ : hA₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwA₂ : hA₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwb₁ : hb₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwb₂ : hb₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwB₁ : hB₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwB₂ : hB₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwreg₁ : hb₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hb₁) hwb₁
  have hwreg₂ : hb₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hb₂) hwb₂
  have hlexA := lexDM_wt_lt_pair Aw hA₁ hA₂ D₁ D₂ rfl rfl hwA₁ hwA₂
  have hlexb := lexDM_wt_lt_pair Aw hb₁ hb₂ D₁ D₂ rfl rfl hwb₁ hwb₂
  let ρ' := binderDisp (levelIsZero (σ u₁)) :: ρ
  have hρ' := hρ.assumption hA₁
  have hcl₁ : CL tbl σ ρ' hB₁ hb₁.reg.2 :=
    Bel.cl hB₁ hb₁.reg.2 σ ρ' hρ'
      (lexDM_both_wt_lt_left Aw hB₁ hb₁.reg.2 D₁ D₂ rfl hwB₁ hwreg₁)
  have heut_b : EUT tbl σ ρ' hb₁ hb₂ :=
    Bel.eut hb₁ hb₂ σ ρ' hρ' hlexb
  have hcl₂ : CL tbl σ ρ' hb₂.reg.2 hB₂ :=
    Bel.cl hb₂.reg.2 hB₂ σ ρ' hρ'
      (lexDM_both_wt_lt_right Aw hb₂.reg.2 hB₂ D₁ D₂ rfl hwreg₂ hwB₂)
  exact eut_lam_nodes tbl hTC σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂
    (Bel.bitCoh hA₁ hA₂ σ ρ hρ hlexA)
    (Bel.cl hA₁ hA₂ σ ρ hρ hlexA)
    (hcl₁.trans (heut_b.trans hcl₂))

/-- `CL` on two `TyP.app` nodes on `(f, a)` from `Below` and
    `hf_bit : levelIsZero (σ hf₁.reg.1) = levelIsZero (σ hf₂.reg.1)` and
    `ha_bit : levelIsZero (σ ha₁.reg.1) = levelIsZero (σ ha₂.reg.1)`. -/
theorem cl_app_of_below_bits (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hf_bit : levelIsZero (σ hf₁.reg.1) = levelIsZero (σ hf₂.reg.1))
    (ha_bit : levelIsZero (σ ha₁.reg.1) = levelIsZero (σ ha₂.reg.1))
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂))) :
    CL tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  let D₁ := TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁
  let D₂ := TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂
  have hwf₁ : hf₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwf₂ : hf₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwa₁ : ha₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwa₂ : ha₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwf_reg₁ : hf₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hf₁) hwf₁
  have hwf_reg₂ : hf₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hf₂) hwf₂
  have hwa_reg₁ : ha₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw ha₁) hwa₁
  have hwa_reg₂ : ha₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw ha₂) hwa₂
  have hpbf₁ := Bel.pb hf₁ hf₁.reg.2 σ ρ hρ
    (lexDM_both_wt_lt_left Aw hf₁ hf₁.reg.2 D₁ D₂ rfl hwf₁ hwf_reg₁)
  have hpbf₂ := Bel.pb hf₂ hf₂.reg.2 σ ρ hρ
    (lexDM_both_wt_lt_right Aw hf₂ hf₂.reg.2 D₁ D₂ rfl hwf₂ hwf_reg₂)
  have hclf := Bel.cl hf₁ hf₂ σ ρ hρ (lexDM_wt_lt_pair Aw hf₁ hf₂ D₁ D₂ rfl rfl hwf₁ hwf₂)
  cases hzf₁ : levelIsZero (σ hf₁.reg.1) with
  | true =>
      have hzf₂ : levelIsZero (σ hf₂.reg.1) = true := hf_bit.symm.trans hzf₁
      exact cl_app_nodes_fun_star tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂
        (hpbf₁.mpr hzf₁) (hpbf₂.mpr hzf₂)
  | false =>
      have hzf₂ : levelIsZero (σ hf₂.reg.1) = false := hf_bit.symm.trans hzf₁
      have hpba₁ := Bel.pb ha₁ ha₁.reg.2 σ ρ hρ
        (lexDM_both_wt_lt_left Aw ha₁ ha₁.reg.2 D₁ D₂ rfl hwa₁ hwa_reg₁)
      have hpba₂ := Bel.pb ha₂ ha₂.reg.2 σ ρ hρ
        (lexDM_both_wt_lt_right Aw ha₂ ha₂.reg.2 D₁ D₂ rfl hwa₂ hwa_reg₂)
      cases hza₁ : levelIsZero (σ ha₁.reg.1) with
      | true =>
          have hza₂ : levelIsZero (σ ha₂.reg.1) = true := ha_bit.symm.trans hza₁
          exact cl_app_nodes_arg_star tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂
            (hpba₁.mpr hza₁) (hpba₂.mpr hza₂) hclf
      | false =>
          have hza₂ : levelIsZero (σ ha₂.reg.1) = false := ha_bit.symm.trans hza₁
          have hf_ne₁ : hf₁.eps σ ρ ≠ .star := by
            intro hs; exact Bool.noConfusion (hzf₁.symm.trans (hpbf₁.mp hs))
          have hf_ne₂ : hf₂.eps σ ρ ≠ .star := by
            intro hs; exact Bool.noConfusion (hzf₂.symm.trans (hpbf₂.mp hs))
          have ha_ne₁ : ha₁.eps σ ρ ≠ .star := by
            intro hs; exact Bool.noConfusion (hza₁.symm.trans (hpba₁.mp hs))
          have ha_ne₂ : ha₂.eps σ ρ ≠ .star := by
            intro hs; exact Bool.noConfusion (hza₂.symm.trans (hpba₂.mp hs))
          have hcla := Bel.cl ha₁ ha₂ σ ρ hρ (lexDM_wt_lt_pair Aw ha₁ ha₂ D₁ D₂ rfl rfl hwa₁ hwa₂)
          exact cl_app_nodes_rel tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂
            hf_ne₁ ha_ne₁ hf_ne₂ ha_ne₂ hclf hcla

/-- When two `TyP.app` nodes share the same Π-type `(A, B)`, `Bel.bitCoh` automatically
    discharges `hf_bit` and `ha_bit`, closing `CL` from `Below` alone. -/
theorem cl_app_same_pi_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A B)) (ha₁ : TyP E n Γ a A)
    (hT₁ : TyP E n Γ (instantiate0 a B) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A B)) (ha₂ : TyP E n Γ a A)
    (hT₂ : TyP E n Γ (instantiate0 a B) (.sort w₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.app E n Γ f a A B w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A B w₂ hf₂ ha₂ hT₂))) :
    CL tbl σ ρ
      (TyP.app E n Γ f a A B w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A B w₂ hf₂ ha₂ hT₂) := by
  let D₁ := TyP.app E n Γ f a A B w₁ hf₁ ha₁ hT₁
  let D₂ := TyP.app E n Γ f a A B w₂ hf₂ ha₂ hT₂
  have hwf₁ : hf₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwf₂ : hf₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwa₁ : ha₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwa₂ : ha₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwf_reg₁ : hf₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hf₁) hwf₁
  have hwf_reg₂ : hf₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hf₂) hwf₂
  have hwa_reg₁ : ha₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw ha₁) hwa₁
  have hwa_reg₂ : ha₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw ha₂) hwa₂
  have hf_bit : BitCoh σ hf₁.reg.2 hf₂.reg.2 :=
    Bel.bitCoh hf₁.reg.2 hf₂.reg.2 σ ρ hρ
      (lexDM_wt_lt_pair Aw hf₁.reg.2 hf₂.reg.2 D₁ D₂ rfl rfl hwf_reg₁ hwf_reg₂)
  have ha_bit : BitCoh σ ha₁.reg.2 ha₂.reg.2 :=
    Bel.bitCoh ha₁.reg.2 ha₂.reg.2 σ ρ hρ
      (lexDM_wt_lt_pair Aw ha₁.reg.2 ha₂.reg.2 D₁ D₂ rfl rfl hwa_reg₁ hwa_reg₂)
  exact cl_app_of_below_bits Aw tbl hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ σ ρ hρ hf_bit ha_bit Bel

/-- When two `TyP.app` nodes share the same Π-type `(A, B)`, `Bel.cl hT₁ hT₂`
    discharges `EUT` from `Below` alone. -/
theorem eut_app_same_pi_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A B)) (ha₁ : TyP E n Γ a A)
    (hT₁ : TyP E n Γ (instantiate0 a B) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A B)) (ha₂ : TyP E n Γ a A)
    (hT₂ : TyP E n Γ (instantiate0 a B) (.sort w₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.app E n Γ f a A B w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A B w₂ hf₂ ha₂ hT₂))) :
    EUT tbl σ ρ
      (TyP.app E n Γ f a A B w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A B w₂ hf₂ ha₂ hT₂) := by
  let D₁ := TyP.app E n Γ f a A B w₁ hf₁ ha₁ hT₁
  let D₂ := TyP.app E n Γ f a A B w₂ hf₂ ha₂ hT₂
  have hwT₁ : hT₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwT₂ : hT₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  exact Bel.cl hT₁ hT₂ σ ρ hρ (lexDM_wt_lt_pair Aw hT₁ hT₂ D₁ D₂ rfl rfl hwT₁ hwT₂)

/-- `EUT` on two `TyP.app` nodes with arbitrary Π-types `(A₁, B₁)` and `(A₂, B₂)` on
    a proof domain (`levelIsZero (σ g₁.u) = true` and `levelIsZero (σ g₂.u) = true`),
    from `Below` and `TableWF tbl` via Π-injectivity in E (`eut_app_nodes_drop`). -/
theorem eut_app_of_below_got_drop (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (g₁ : PiGot Aw ((TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw) E n Γ A₁ B₁)
    (g₂ : PiGot Aw ((TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw) E n Γ A₂ B₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hpi₁ : hf₁.reg.2.eps σ ρ = piClauseOf g₁ σ ρ)
    (hpi₂ : hf₂.reg.2.eps σ ρ = piClauseOf g₂ σ ρ)
    (hu₁ : levelIsZero (σ g₁.u) = true) (hu₂ : levelIsZero (σ g₂.u) = true)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂))) :
    EUT tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  let D₁ := TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁
  let D₂ := TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂
  have hwf₁ : hf₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwf₂ : hf₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have heut_f : EUT tbl σ ρ hf₁ hf₂ :=
    Bel.eut hf₁ hf₂ σ ρ hρ (lexDM_wt_lt_pair Aw hf₁ hf₂ D₁ D₂ rfl rfl hwf₁ hwf₂)
  have hcl_T₁ : CL tbl σ ρ hT₁ (instEnd g₁.hB ha₁ g₁.hA) := by
    have h := Bel.cl (instEnd g₁.hB ha₁ g₁.hA) hT₁ σ ρ hρ
      (lexDM_app_instEnd_pair Aw hf₁ ha₁ hT₁ g₁ D₂)
    exact ConvMod.symm' LvlEq.symm' h
  have hcl_T₂ : CL tbl σ ρ (instEnd g₂.hB ha₂ g₂.hA) hT₂ :=
    Bel.cl (instEnd g₂.hB ha₂ g₂.hA) hT₂ σ ρ hρ
      (lex_of_dm (dmStep_drop_left (dmStep_app_instEnd_pair Aw hf₂ ha₂ hT₂ g₂) (D₁.atoms Aw)))
  have hcl_pi₁ : CL tbl σ ρ hf₁.reg.2 (TyP.pi E n Γ A₁ g₁.u B₁ g₁.v g₁.hA g₁.hB) := by
    unfold CL
    rw [hpi₁, piClauseOf, eps_pi_clause]
    exact .refl _
  have hcl_pi₂ : CL tbl σ ρ (TyP.pi E n Γ A₂ g₂.u B₂ g₂.v g₂.hA g₂.hB) hf₂.reg.2 := by
    unfold CL
    rw [hpi₂, piClauseOf, eps_pi_clause]
    exact .refl _
  exact eut_app_nodes_drop hW σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ g₁.hA g₁.hB g₂.hA g₂.hB
    hu₁ (hu₁.trans hu₂.symm) heut_f hcl_pi₁ hcl_pi₂ hcl_T₁ hcl_T₂

/-- `EUT` on two `TyP.app` nodes with arbitrary Π-types `(A₁, B₁)` and `(A₂, B₂)` on
    a relevant domain (`levelIsZero (σ g₁.u) = false` and `levelIsZero (σ g₂.u) = false`),
    from `Below` and `TableWF tbl` via Π-injectivity in E (`eut_app_nodes_keep`). -/
theorem eut_app_of_below_got_keep (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (g₁ : PiGot Aw ((TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw) E n Γ A₁ B₁)
    (g₂ : PiGot Aw ((TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw) E n Γ A₂ B₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hpi₁ : hf₁.reg.2.eps σ ρ = piClauseOf g₁ σ ρ)
    (hpi₂ : hf₂.reg.2.eps σ ρ = piClauseOf g₂ σ ρ)
    (hu₁ : levelIsZero (σ g₁.u) = false) (hu₂ : levelIsZero (σ g₂.u) = false)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂))) :
    EUT tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  let D₁ := TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁
  let D₂ := TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂
  have hwf₁ : hf₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwf₂ : hf₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwa₁ : ha₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwa₂ : ha₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have heut_f : EUT tbl σ ρ hf₁ hf₂ :=
    Bel.eut hf₁ hf₂ σ ρ hρ (lexDM_wt_lt_pair Aw hf₁ hf₂ D₁ D₂ rfl rfl hwf₁ hwf₂)
  have hcl_a : CL tbl σ ρ ha₁ ha₂ :=
    Bel.cl ha₁ ha₂ σ ρ hρ (lexDM_wt_lt_pair Aw ha₁ ha₂ D₁ D₂ rfl rfl hwa₁ hwa₂)
  have hcl_T₁ : CL tbl σ ρ hT₁ (instEnd g₁.hB ha₁ g₁.hA) := by
    have h := Bel.cl (instEnd g₁.hB ha₁ g₁.hA) hT₁ σ ρ hρ
      (lexDM_app_instEnd_pair Aw hf₁ ha₁ hT₁ g₁ D₂)
    exact ConvMod.symm' LvlEq.symm' h
  have hcl_T₂ : CL tbl σ ρ (instEnd g₂.hB ha₂ g₂.hA) hT₂ :=
    Bel.cl (instEnd g₂.hB ha₂ g₂.hA) hT₂ σ ρ hρ
      (lex_of_dm (dmStep_drop_left (dmStep_app_instEnd_pair Aw hf₂ ha₂ hT₂ g₂) (D₁.atoms Aw)))
  have hcl_pi₁ : CL tbl σ ρ hf₁.reg.2 (TyP.pi E n Γ A₁ g₁.u B₁ g₁.v g₁.hA g₁.hB) := by
    unfold CL
    rw [hpi₁, piClauseOf, eps_pi_clause]
    exact .refl _
  have hcl_pi₂ : CL tbl σ ρ (TyP.pi E n Γ A₂ g₂.u B₂ g₂.v g₂.hA g₂.hB) hf₂.reg.2 := by
    unfold CL
    rw [hpi₂, piClauseOf, eps_pi_clause]
    exact .refl _
  exact eut_app_nodes_keep hW σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ g₁.hA g₁.hB g₂.hA g₂.hB
    hu₁ (hu₁.trans hu₂.symm) heut_f hcl_a hcl_pi₁ hcl_pi₂ hcl_T₁ hcl_T₂

/-- `CL` on **any** two `TyP.letE` nodes on `.letE A v b` (even with distinct body types
    `B₁, B₂`!) from `Below` alone, in `Γ` via Option L-inline-at-0 (`letSub`) with
    **zero `.letBinding` context extension**. -/
theorem cl_letE_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂))) :
    CL tbl σ ρ
      (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
      (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) := by
  let D₁ := TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁
  let D₂ := TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂
  have hw₁ : (letSub hb₁ hv₁ hA₁).wt Aw < D₁.wt Aw := by
    have := TyP.wt_pos Aw hT₁
    rw [letSub_wt]; simp only [D₁, TyP.wt]; omega
  have hw₂ : (letSub hb₂ hv₂ hA₂).wt Aw < D₂.wt Aw := by
    have := TyP.wt_pos Aw hT₂
    rw [letSub_wt]; simp only [D₂, TyP.wt]; omega
  exact (cl_letE_nodes_iff_letSub tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂).mpr
    (Bel.cl (letSub hb₁ hv₁ hA₁) (letSub hb₂ hv₂ hA₂) σ ρ hρ
      (lexDM_wt_lt_pair Aw (letSub hb₁ hv₁ hA₁) (letSub hb₂ hv₂ hA₂) D₁ D₂ rfl rfl hw₁ hw₂))

/-- `EUT` on **any** two `TyP.letE` nodes on `.letE A v b` (even with distinct body types
    `B₁, B₂`!) from `Below` alone, chaining `Bel.cl hT₁ (letSub hb₁ hv₁ hA₁).reg.2`,
    `Bel.eut (letSub hb₁ hv₁ hA₁) (letSub hb₂ hv₂ hA₂)`, and
    `Bel.cl (letSub hb₂ hv₂ hA₂).reg.2 hT₂` in `Γ` with **zero `.letBinding` context extension**. -/
theorem eut_letE_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat} {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂))) :
    EUT tbl σ ρ
      (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
      (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) := by
  let D₁ := TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁
  let D₂ := TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂
  let L₁ := letSub hb₁ hv₁ hA₁
  let L₂ := letSub hb₂ hv₂ hA₂
  have hwL₁ : L₁.wt Aw < D₁.wt Aw := by
    have := TyP.wt_pos Aw hT₁
    simp only [L₁, letSub_wt, D₁, TyP.wt]; omega
  have hwL₂ : L₂.wt Aw < D₂.wt Aw := by
    have := TyP.wt_pos Aw hT₂
    simp only [L₂, letSub_wt, D₂, TyP.wt]; omega
  have hwT₁ : hT₁.wt Aw < D₁.wt Aw := by simp only [D₁, TyP.wt]; omega
  have hwT₂ : hT₂.wt Aw < D₂.wt Aw := by simp only [D₂, TyP.wt]; omega
  have hwreg₁ : L₁.reg.2.wt Aw < D₁.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw L₁) hwL₁
  have hwreg₂ : L₂.reg.2.wt Aw < D₂.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw L₂) hwL₂
  have hcl₁ : CL tbl σ ρ hT₁ L₁.reg.2 :=
    Bel.cl hT₁ L₁.reg.2 σ ρ hρ
      (lexDM_both_wt_lt_left Aw hT₁ L₁.reg.2 D₁ D₂ rfl hwT₁ hwreg₁)
  have heut_L : EUT tbl σ ρ L₁ L₂ :=
    Bel.eut L₁ L₂ σ ρ hρ (lexDM_wt_lt_pair Aw L₁ L₂ D₁ D₂ rfl rfl hwL₁ hwL₂)
  have hcl₂ : CL tbl σ ρ L₂.reg.2 hT₂ :=
    Bel.cl L₂.reg.2 hT₂ σ ρ hρ
      (lexDM_both_wt_lt_right Aw L₂.reg.2 hT₂ D₁ D₂ rfl hwreg₂ hwT₂)
  exact eut_letE_nodes tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂
    (hcl₁.trans (heut_L.trans hcl₂))

/-- `CL` on two `TyP.lit` nodes from `Below` alone (for arbitrary `T₁, T₂`). -/
theorem cl_lit_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T₁ T₂ : Expr Nat}
    (hexp₁ : TyP E n Γ (natExpand t) T₁) (hexp₂ : TyP E n Γ (natExpand t) T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂))) :
    CL tbl σ ρ (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂) := by
  let D₁ := TyP.lit E n Γ t T₁ hexp₁
  let D₂ := TyP.lit E n Γ t T₂ hexp₂
  have hw₁ : hexp₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hw₂ : hexp₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  exact (cl_lit_nodes tbl σ ρ hexp₁ hexp₂).mpr
    (Bel.cl hexp₁ hexp₂ σ ρ hρ (lexDM_wt_lt_pair Aw hexp₁ hexp₂ D₁ D₂ rfl rfl hw₁ hw₂))

/-- `EUT` on two `TyP.lit` nodes from `Below` alone (for arbitrary `T₁, T₂`). -/
theorem eut_lit_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T₁ T₂ : Expr Nat}
    (hexp₁ : TyP E n Γ (natExpand t) T₁) (hexp₂ : TyP E n Γ (natExpand t) T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂))) :
    EUT tbl σ ρ (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂) := by
  let D₁ := TyP.lit E n Γ t T₁ hexp₁
  let D₂ := TyP.lit E n Γ t T₂ hexp₂
  have hw₁ : hexp₁.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hw₂ : hexp₂.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  exact (eut_lit_nodes tbl σ ρ hexp₁ hexp₂).mpr
    (Bel.eut hexp₁ hexp₂ σ ρ hρ (lexDM_wt_lt_pair Aw hexp₁ hexp₂ D₁ D₂ rfl rfl hw₁ hw₂))

/-- `CL` on `TyP.conv` on the left against **any** `D₂ : TyP E n Γ e T₂`, from `Below` alone. -/
theorem cl_conv_left_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B T₂ : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) (D₂ : TyP E n Γ e T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) D₂)) :
    CL tbl σ ρ (TyP.conv E n Γ e A B u h hc) D₂ := by
  let D₁ := TyP.conv E n Γ e A B u h hc
  have hwh : h.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hstep : DMStep (h.atoms Aw ++ D₂.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) :=
    dmStep_append_right (dmStep_wt_lt_singleton Aw h D₁ rfl hwh) (D₂.atoms Aw)
  exact Bel.cl h D₂ σ ρ hρ (lex_of_dm hstep)

/-- `CL` on `TyP.conv` on the right against **any** `D₁ : TyP E n Γ e T₁`, from `Below` alone. -/
theorem cl_conv_right_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ A B : Expr Nat} {u : Level}
    (D₁ : TyP E n Γ e T₁) (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw D₁ (TyP.conv E n Γ e A B u h hc))) :
    CL tbl σ ρ D₁ (TyP.conv E n Γ e A B u h hc) := by
  let D₂ := TyP.conv E n Γ e A B u h hc
  have hwh : h.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hstep : DMStep (D₁.atoms Aw ++ h.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) :=
    dmStep_append_left (dmStep_wt_lt_singleton Aw h D₂ rfl hwh) (D₁.atoms Aw)
  exact Bel.cl D₁ h σ ρ hρ (lex_of_dm hstep)

/-- `EUT` on `TyP.conv` on the left against **any** `D₂ : TyP E n Γ e T₂`, from `Below` alone. -/
theorem eut_conv_left_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B T₂ : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) (D₂ : TyP E n Γ e T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) D₂)) :
    EUT tbl σ ρ (TyP.conv E n Γ e A B u h hc) D₂ := by
  let D₁ := TyP.conv E n Γ e A B u h hc
  have hwh : h.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwc : hc.wt Aw < D₁.wt Aw := by simp only [TyP.wt]; omega
  have hwdl : hc.dl.wt Aw < D₁.wt Aw := Nat.lt_of_lt_of_le (CvP.wt_dl_lt Aw hc) (Nat.le_of_lt hwc)
  have hwreg : h.reg.2.wt Aw < D₁.wt Aw := Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw h) hwh
  have hstep_c : DMStep (hc.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) := by
    refine dmStep_drop_right ?_ (D₂.atoms Aw)
    change DMStep (hc.atoms Aw) [D₁.wt Aw]
    rw [← List.append_nil (hc.atoms Aw)]
    exact dmStep_of_below (cvp_atoms_lt_of_wt_lt Aw hc hwc)
  have hes : ES tbl σ ρ hc := Bel.es hc σ ρ hρ (lex_of_dm hstep_c)
  have hcl : CL tbl σ ρ hc.dl h.reg.2 :=
    Bel.cl hc.dl h.reg.2 σ ρ hρ
      (lexDM_both_wt_lt_left Aw hc.dl h.reg.2 D₁ D₂ rfl hwdl hwreg)
  have hstep_h : DMStep (h.atoms Aw ++ D₂.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) :=
    dmStep_append_right (dmStep_wt_lt_singleton Aw h D₁ rfl hwh) (D₂.atoms Aw)
  have heut : EUT tbl σ ρ h D₂ := Bel.eut h D₂ σ ρ hρ (lex_of_dm hstep_h)
  exact eut_conv_left tbl σ ρ h hc D₂ hes hcl heut

/-- `EUT` on `TyP.conv` on the right against **any** `D₁ : TyP E n Γ e T₁`, from `Below` alone. -/
theorem eut_conv_right_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ A B : Expr Nat} {u : Level}
    (D₁ : TyP E n Γ e T₁) (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw D₁ (TyP.conv E n Γ e A B u h hc))) :
    EUT tbl σ ρ D₁ (TyP.conv E n Γ e A B u h hc) := by
  let D₂ := TyP.conv E n Γ e A B u h hc
  have hwh : h.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwc : hc.wt Aw < D₂.wt Aw := by simp only [TyP.wt]; omega
  have hwdl : hc.dl.wt Aw < D₂.wt Aw := Nat.lt_of_lt_of_le (CvP.wt_dl_lt Aw hc) (Nat.le_of_lt hwc)
  have hwreg : h.reg.2.wt Aw < D₂.wt Aw := Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw h) hwh
  have hstep_c : DMStep (hc.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) := by
    refine dmStep_drop_left ?_ (D₁.atoms Aw)
    change DMStep (hc.atoms Aw) [D₂.wt Aw]
    rw [← List.append_nil (hc.atoms Aw)]
    exact dmStep_of_below (cvp_atoms_lt_of_wt_lt Aw hc hwc)
  have hes : ES tbl σ ρ hc := Bel.es hc σ ρ hρ (lex_of_dm hstep_c)
  have hcl : CL tbl σ ρ h.reg.2 hc.dl :=
    Bel.cl h.reg.2 hc.dl σ ρ hρ
      (lexDM_both_wt_lt_right Aw h.reg.2 hc.dl D₁ D₂ rfl hwreg hwdl)
  have hstep_h : DMStep (D₁.atoms Aw ++ h.atoms Aw) (D₁.atoms Aw ++ D₂.atoms Aw) :=
    dmStep_append_left (dmStep_wt_lt_singleton Aw h D₂ rfl hwh) (D₁.atoms Aw)
  have heut : EUT tbl σ ρ D₁ h := Bel.eut D₁ h σ ρ hρ (lex_of_dm hstep_h)
  exact eut_conv_right tbl σ ρ D₁ h hc heut hcl hes

/-! ## §3 Same-Transport `CL` and `EUT` from `Below` (`ewk`, `linst`, `wk`, `cctx`, `esub`) -/

/-- `CL` on two `TyP.ewk` nodes at the same `E₀` from `Below`. -/
theorem cl_ewk_both_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (hext₁ hext₂ : EnvExt E₀ E) (D₁ : TyP E₀ n Γ e T₁) (D₂ : TyP E₀ n Γ e T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ₀ : DispFor σ E₀ n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.ewk E₀ E n Γ e T₁ hext₁ D₁) (TyP.ewk E₀ E n Γ e T₂ hext₂ D₂))) :
    CL tbl σ ρ (TyP.ewk E₀ E n Γ e T₁ hext₁ D₁) (TyP.ewk E₀ E n Γ e T₂ hext₂ D₂) := by
  have hlex : LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.ewk E₀ E n Γ e T₁ hext₁ D₁) (TyP.ewk E₀ E n Γ e T₂ hext₂ D₂)) := by
    apply Prod.Lex.right
    simp only [tyPairMeas, TyP.wt]; omega
  exact Bel.cl D₁ D₂ σ ρ hρ₀ hlex

/-- `EUT` on two `TyP.ewk` nodes at the same `E₀` from `Below`. -/
theorem eut_ewk_both_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (hext₁ hext₂ : EnvExt E₀ E) (D₁ : TyP E₀ n Γ e T₁) (D₂ : TyP E₀ n Γ e T₂)
    (σ : Level → Level) (ρ : List Disp) (hρ₀ : DispFor σ E₀ n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.ewk E₀ E n Γ e T₁ hext₁ D₁) (TyP.ewk E₀ E n Γ e T₂ hext₂ D₂))) :
    EUT tbl σ ρ (TyP.ewk E₀ E n Γ e T₁ hext₁ D₁) (TyP.ewk E₀ E n Γ e T₂ hext₂ D₂) := by
  have hlex : LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.ewk E₀ E n Γ e T₁ hext₁ D₁) (TyP.ewk E₀ E n Γ e T₂ hext₂ D₂)) := by
    apply Prod.Lex.right
    simp only [tyPairMeas, TyP.wt]; omega
  exact Bel.eut D₁ D₂ σ ρ hρ₀ hlex

/-- `CL` on two `TyP.linst` nodes at the same `ls` from `Below`. -/
theorem cl_linst_both_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    {ls : List Level} (hls₁ hls₂ : levelsBounded n ls = true) (hlen₁ hlen₂ : ls.length = a')
    (D₁ : TyP E a' Γ e T₁) (D₂ : TyP E a' Γ e T₂)
    (σ : Level → Level) (ρ : List Disp)
    (hρ₀ : DispFor (fun l => σ (instLevel ls l)) E a' Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.linst E a' n Γ e T₁ ls hls₁ hlen₁ D₁)
        (TyP.linst E a' n Γ e T₂ ls hls₂ hlen₂ D₂))) :
    CL tbl σ ρ
      (TyP.linst E a' n Γ e T₁ ls hls₁ hlen₁ D₁)
      (TyP.linst E a' n Γ e T₂ ls hls₂ hlen₂ D₂) := by
  have hlex : LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw
        (TyP.linst E a' n Γ e T₁ ls hls₁ hlen₁ D₁)
        (TyP.linst E a' n Γ e T₂ ls hls₂ hlen₂ D₂)) := by
    apply Prod.Lex.right
    simp only [tyPairMeas, TyP.wt]; omega
  exact Bel.cl D₁ D₂ (fun l => σ (instLevel ls l)) ρ hρ₀ hlex

/-- `EUT` on two `TyP.linst` nodes at the same `ls` from `Below`. -/
theorem eut_linst_both_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    {ls : List Level} (hls₁ hls₂ : levelsBounded n ls = true) (hlen₁ hlen₂ : ls.length = a')
    (D₁ : TyP E a' Γ e T₁) (D₂ : TyP E a' Γ e T₂)
    (σ : Level → Level) (ρ : List Disp)
    (hρ₀ : DispFor (fun l => σ (instLevel ls l)) E a' Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.linst E a' n Γ e T₁ ls hls₁ hlen₁ D₁)
        (TyP.linst E a' n Γ e T₂ ls hls₂ hlen₂ D₂))) :
    EUT tbl σ ρ
      (TyP.linst E a' n Γ e T₁ ls hls₁ hlen₁ D₁)
      (TyP.linst E a' n Γ e T₂ ls hls₂ hlen₂ D₂) := by
  have hlex : LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw
        (TyP.linst E a' n Γ e T₁ ls hls₁ hlen₁ D₁)
        (TyP.linst E a' n Γ e T₂ ls hls₂ hlen₂ D₂)) := by
    apply Prod.Lex.right
    simp only [tyPairMeas, TyP.wt]; omega
  exact Bel.eut D₁ D₂ (fun l => σ (instLevel ls l)) ρ hρ₀ hlex

/-- `CL` on two `TyP.wk` nodes at the same `(d, c)` from `Below` and `TableClosed tbl`. -/
theorem cl_wk_both_of_below (Aw : Nat → Nat) {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (σ : Level → Level) (ρ : List Disp)
    (hρ₀ : DispFor σ E n Γ (removeAt ρ c))
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂))) :
    CL tbl σ ρ (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂) := by
  have hlex : LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂)) := by
    apply Prod.Lex.right
    simp only [tyPairMeas, TyP.wt]; omega
  have ih := Bel.cl D₁ D₂ σ (removeAt ρ c) hρ₀ hlex
  rcases getElem?_keep_or_not_keep ρ c with hk | hnk
  · exact cl_wk_keep_both hcl D₁ D₂ hk ih
  · exact cl_wk_not_keep_both D₁ D₂ hnk ih

/-- `EUT` on two `TyP.wk` nodes at the same `(d, c)` from `Below` and `TableClosed tbl`. -/
theorem eut_wk_both_of_below (Aw : Nat → Nat) {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (σ : Level → Level) (ρ : List Disp)
    (hρ₀ : DispFor σ E n Γ (removeAt ρ c))
    (Bel : Below Aw tbl
      (tyPairMeas Aw (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂))) :
    EUT tbl σ ρ (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂) := by
  have hlex : LexDM (tyPairMeas Aw D₁ D₂)
      (tyPairMeas Aw (TyP.wk E n Γ e T₁ d c D₁) (TyP.wk E n Γ e T₂ d c D₂)) := by
    apply Prod.Lex.right
    simp only [tyPairMeas, TyP.wt]; omega
  have ih := Bel.eut D₁ D₂ σ (removeAt ρ c) hρ₀ hlex
  rcases getElem?_keep_or_not_keep ρ c with hk | hnk
  · exact eut_wk_keep_both hcl D₁ D₂ hk ih
  · exact eut_wk_not_keep_both D₁ D₂ hnk ih

/-- `CL` on two `TyP.cctx` nodes at the same `(A, A')` from `Below`. -/
theorem cl_cctx_both_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
    (σ : Level → Level) (ρ' : List Disp)
    (hρ₀ : DispFor σ E n (.assumption A :: Γ) ρ')
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂))) :
    CL tbl σ ρ'
      (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
      (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) := by
  have hstep₁ : DMStep (D₁.atoms Aw) ((TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁).atoms Aw) :=
    dmStep_drop_right_nonempty (D₁.atoms Aw) (CvP.atoms_ne_nil Aw hA₁)
  have hstep₂ : DMStep (D₂.atoms Aw) ((TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂).atoms Aw) :=
    dmStep_drop_right_nonempty (D₂.atoms Aw) (CvP.atoms_ne_nil Aw hA₂)
  exact Bel.cl D₁ D₂ σ ρ' hρ₀ (lex_of_dm (dmStep_append_both hstep₁ hstep₂))

/-- `EUT` on two `TyP.cctx` nodes at the same `(A, A')` from `Below`. -/
theorem eut_cctx_both_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ A A' : Expr Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n (.assumption A :: Γ) e T₁) (hA₁ : CvP E n Γ A A' (.sort u₁))
    (D₂ : TyP E n (.assumption A :: Γ) e T₂) (hA₂ : CvP E n Γ A A' (.sort u₂))
    (σ : Level → Level) (ρ' : List Disp)
    (hρ₀ : DispFor σ E n (.assumption A :: Γ) ρ')
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
        (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂))) :
    EUT tbl σ ρ'
      (TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁)
      (TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂) := by
  have hstep₁ : DMStep (D₁.atoms Aw) ((TyP.cctx E n Γ e T₁ A A' u₁ D₁ hA₁).atoms Aw) :=
    dmStep_drop_right_nonempty (D₁.atoms Aw) (CvP.atoms_ne_nil Aw hA₁)
  have hstep₂ : DMStep (D₂.atoms Aw) ((TyP.cctx E n Γ e T₂ A A' u₂ D₂ hA₂).atoms Aw) :=
    dmStep_drop_right_nonempty (D₂.atoms Aw) (CvP.atoms_ne_nil Aw hA₂)
  exact Bel.eut D₁ D₂ σ ρ' hρ₀ (lex_of_dm (dmStep_append_both hstep₁ hstep₂))

/-- `CL` on two `TyP.esub` nodes at the same `(t, v, j)` from `Below` and `TableClosed tbl`. -/
theorem cl_esub_both_of_below (Aw : Nat → Nat) {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ t v : Expr Nat} {j : Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n Γ e T₁) (hget₁ : Γ[j]? = some (.assumption t))
    (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₁))
    (D₂ : TyP E n Γ e T₂) (hget₂ : Γ[j]? = some (.assumption t))
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n (substRemove v j Γ) ρ)
    (hρ_ins : DispFor σ E n Γ (insertDisp (binderDisp (levelIsZero (σ u₁))) j ρ))
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
        (TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂))) :
    CL tbl σ ρ
      (TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
      (TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂) := by
  let E₁ := TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁
  let E₂ := TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂
  have hstepD₁ : DMStep (D₁.atoms Aw) (E₁.atoms Aw) :=
    dmStep_drop_right (dmStep_drop_right_nonempty (D₁.atoms Aw) (TyP.atoms_ne_nil Aw hv₁))
      (hvT₁.atoms Aw)
  have hstepD₂ : DMStep (D₂.atoms Aw) (E₂.atoms Aw) :=
    dmStep_drop_right (dmStep_drop_right_nonempty (D₂.atoms Aw) (TyP.atoms_ne_nil Aw hv₂))
      (hvT₂.atoms Aw)
  have hstepv₁ : DMStep (hv₁.atoms Aw) (E₁.atoms Aw) :=
    dmStep_drop_right (dmStep_drop (TyP.atoms_ne_nil Aw D₁)) (hvT₁.atoms Aw)
  have hstepv₂ : DMStep (hv₂.atoms Aw) (E₂.atoms Aw) :=
    dmStep_drop_right (dmStep_drop (TyP.atoms_ne_nil Aw D₂)) (hvT₂.atoms Aw)
  have hstepT₁ : DMStep (hvT₁.atoms Aw) (E₁.atoms Aw) := by
    change DMStep (hvT₁.atoms Aw) ((D₁.atoms Aw ++ hv₁.atoms Aw) ++ hvT₁.atoms Aw)
    exact dmStep_drop (by simp [TyP.atoms_ne_nil Aw D₁])
  have hstepT₂ : DMStep (hvT₂.atoms Aw) (E₂.atoms Aw) := by
    change DMStep (hvT₂.atoms Aw) ((D₂.atoms Aw ++ hv₂.atoms Aw) ++ hvT₂.atoms Aw)
    exact dmStep_drop (by simp [TyP.atoms_ne_nil Aw D₂])
  have hbit : BitCoh σ hvT₁ hvT₂ :=
    Bel.bitCoh hvT₁ hvT₂ σ ρ hρ (lex_of_dm (dmStep_append_both hstepT₁ hstepT₂))
  have ihD := Bel.cl D₁ D₂ σ (insertDisp (binderDisp (levelIsZero (σ u₁))) j ρ) hρ_ins
    (lex_of_dm (dmStep_append_both hstepD₁ hstepD₂))
  cases hu₁ : levelIsZero (σ u₁) with
  | true =>
      have hu₂ : levelIsZero (σ u₂) = true := hbit.symm.trans hu₁
      rw [hu₁, binderDisp_drop] at ihD
      exact cl_esub_drop_both D₁ hget₁ hv₁ hvT₁ D₂ hget₂ hv₂ hvT₂ hu₁ hu₂ ihD
  | false =>
      have hu₂ : levelIsZero (σ u₂) = false := hbit.symm.trans hu₁
      rw [hu₁, binderDisp_keep] at ihD
      have ihv := Bel.cl hv₁ hv₂ σ ρ hρ (lex_of_dm (dmStep_append_both hstepv₁ hstepv₂))
      exact cl_esub_keep_both hcl D₁ hget₁ hv₁ hvT₁ D₂ hget₂ hv₂ hvT₂ hu₁ hu₂ ihD ihv

/-- `EUT` on two `TyP.esub` nodes at the same `(t, v, j)` from `Below` and `TableClosed tbl`. -/
theorem eut_esub_both_of_below (Aw : Nat → Nat) {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ t v : Expr Nat} {j : Nat} {u₁ u₂ : Level}
    (D₁ : TyP E n Γ e T₁) (hget₁ : Γ[j]? = some (.assumption t))
    (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₁))
    (D₂ : TyP E n Γ e T₂) (hget₂ : Γ[j]? = some (.assumption t))
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u₂))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n (substRemove v j Γ) ρ)
    (hρ_ins : DispFor σ E n Γ (insertDisp (binderDisp (levelIsZero (σ u₁))) j ρ))
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
        (TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂))) :
    EUT tbl σ ρ
      (TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁)
      (TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂) := by
  let E₁ := TyP.esub E n Γ e T₁ t v j u₁ D₁ hget₁ hv₁ hvT₁
  let E₂ := TyP.esub E n Γ e T₂ t v j u₂ D₂ hget₂ hv₂ hvT₂
  have hstepD₁ : DMStep (D₁.atoms Aw) (E₁.atoms Aw) :=
    dmStep_drop_right (dmStep_drop_right_nonempty (D₁.atoms Aw) (TyP.atoms_ne_nil Aw hv₁))
      (hvT₁.atoms Aw)
  have hstepD₂ : DMStep (D₂.atoms Aw) (E₂.atoms Aw) :=
    dmStep_drop_right (dmStep_drop_right_nonempty (D₂.atoms Aw) (TyP.atoms_ne_nil Aw hv₂))
      (hvT₂.atoms Aw)
  have hstepv₁ : DMStep (hv₁.atoms Aw) (E₁.atoms Aw) :=
    dmStep_drop_right (dmStep_drop (TyP.atoms_ne_nil Aw D₁)) (hvT₁.atoms Aw)
  have hstepv₂ : DMStep (hv₂.atoms Aw) (E₂.atoms Aw) :=
    dmStep_drop_right (dmStep_drop (TyP.atoms_ne_nil Aw D₂)) (hvT₂.atoms Aw)
  have hstepT₁ : DMStep (hvT₁.atoms Aw) (E₁.atoms Aw) := by
    change DMStep (hvT₁.atoms Aw) ((D₁.atoms Aw ++ hv₁.atoms Aw) ++ hvT₁.atoms Aw)
    exact dmStep_drop (by simp [TyP.atoms_ne_nil Aw D₁])
  have hstepT₂ : DMStep (hvT₂.atoms Aw) (E₂.atoms Aw) := by
    change DMStep (hvT₂.atoms Aw) ((D₂.atoms Aw ++ hv₂.atoms Aw) ++ hvT₂.atoms Aw)
    exact dmStep_drop (by simp [TyP.atoms_ne_nil Aw D₂])
  have hbit : BitCoh σ hvT₁ hvT₂ :=
    Bel.bitCoh hvT₁ hvT₂ σ ρ hρ (lex_of_dm (dmStep_append_both hstepT₁ hstepT₂))
  have ihD := Bel.eut D₁ D₂ σ (insertDisp (binderDisp (levelIsZero (σ u₁))) j ρ) hρ_ins
    (lex_of_dm (dmStep_append_both hstepD₁ hstepD₂))
  cases hu₁ : levelIsZero (σ u₁) with
  | true =>
      have hu₂ : levelIsZero (σ u₂) = true := hbit.symm.trans hu₁
      rw [hu₁, binderDisp_drop] at ihD
      exact eut_esub_drop_both D₁ hget₁ hv₁ hvT₁ D₂ hget₂ hv₂ hvT₂ hu₁ hu₂ ihD
  | false =>
      have hu₂ : levelIsZero (σ u₂) = false := hbit.symm.trans hu₁
      rw [hu₁, binderDisp_keep] at ihD
      have ihv := Bel.cl hv₁ hv₂ σ ρ hρ (lex_of_dm (dmStep_append_both hstepv₁ hstepv₂))
      exact eut_esub_keep_both hcl D₁ hget₁ hv₁ hvT₁ D₂ hget₂ hv₂ hvT₂ hu₁ hu₂ ihD ihv

end Rcic.Syn

#print axioms Rcic.Syn.dmStep_append_both
#print axioms Rcic.Syn.dmStep_drop_right_nonempty
#print axioms Rcic.Syn.dmStep_wt_lt_singleton
#print axioms Rcic.Syn.dmStep_wt_lt_pair
#print axioms Rcic.Syn.lexDM_wt_lt_pair
#print axioms Rcic.Syn.dmStep_both_wt_lt_singleton
#print axioms Rcic.Syn.lexDM_both_wt_lt_left
#print axioms Rcic.Syn.lexDM_both_wt_lt_right
#print axioms Rcic.Syn.getElem?_keep_or_not_keep
#print axioms Rcic.Syn.LevelHom.succ_eqN
#print axioms Rcic.Syn.LevelHom.max_eqN
#print axioms Rcic.Syn.LevelHom.imax_eqN
#print axioms Rcic.Syn.cl_sort_of_below
#print axioms Rcic.Syn.eut_sort_of_below
#print axioms Rcic.Syn.cl_bvar_of_below
#print axioms Rcic.Syn.eut_bvar_of_below
#print axioms Rcic.Syn.cl_const_of_below_eq
#print axioms Rcic.Syn.eut_const_of_below_eq
#print axioms Rcic.Syn.cl_const_canon_of_below
#print axioms Rcic.Syn.eut_const_canon_of_below
#print axioms Rcic.Syn.cl_pi_of_below
#print axioms Rcic.Syn.eut_pi_of_below
#print axioms Rcic.Syn.cl_lam_of_below_bit
#print axioms Rcic.Syn.cl_lam_same_cod_of_below
#print axioms Rcic.Syn.eut_lam_of_below
#print axioms Rcic.Syn.cl_app_of_below_bits
#print axioms Rcic.Syn.cl_app_same_pi_of_below
#print axioms Rcic.Syn.eut_app_same_pi_of_below
#print axioms Rcic.Syn.eut_app_of_below_got_drop
#print axioms Rcic.Syn.eut_app_of_below_got_keep
#print axioms Rcic.Syn.cl_letE_of_below
#print axioms Rcic.Syn.eut_letE_of_below
#print axioms Rcic.Syn.cl_lit_of_below
#print axioms Rcic.Syn.eut_lit_of_below
#print axioms Rcic.Syn.cl_conv_left_of_below
#print axioms Rcic.Syn.cl_conv_right_of_below
#print axioms Rcic.Syn.eut_conv_left_of_below
#print axioms Rcic.Syn.eut_conv_right_of_below
#print axioms Rcic.Syn.cl_ewk_both_of_below
#print axioms Rcic.Syn.eut_ewk_both_of_below
#print axioms Rcic.Syn.cl_linst_both_of_below
#print axioms Rcic.Syn.eut_linst_both_of_below
#print axioms Rcic.Syn.cl_wk_both_of_below
#print axioms Rcic.Syn.eut_wk_both_of_below
#print axioms Rcic.Syn.cl_cctx_both_of_below
#print axioms Rcic.Syn.eut_cctx_both_of_below
#print axioms Rcic.Syn.cl_esub_both_of_below
#print axioms Rcic.Syn.eut_esub_both_of_below
