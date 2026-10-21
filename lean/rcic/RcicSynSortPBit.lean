import rcic.RcicSynTable
import rcic.RcicSynRegStep

/-!
# Syntactic sortRow, build step 4g — `LevelHom` properties, `.sort` / `.pi` / `.const` / `.lit` / `.conv` / `.lam` / `.letE` `PBit` from `Below`, `Below.cts` (`CTS h DX`), and unified `CvP.delta` `ES`

`research/rcic/semantic/S3_ES_ARMS.md` §56. Building on `RcicSynTable` (step 4e)
and `RcicSynRegStep` (step 4f), this module establishes:

1. **§1 `LevelHom` evaluation, automatic `LevelSub`, and `imax_bit` / `max_bit`
   (`eval_levelHom`, `LevelHom.eqN_map`, `LevelHom.zero_bit`, `LevelHom.succ_bit`,
   `LevelHom.levelSub`, `LevelHom.imax_bit`, `LevelHom.max_bit`, `DispForHom`)**:
   - Every `LevelHom σ` (`id` and compositions with `instLevel ls`) satisfies
     `eval val (σ l) = eval (fun i => eval val (σ (.param i))) l` for all `l`,
     and therefore automatically satisfies `LevelSub σ`,
     `levelIsZero (σ (.imax u v)) = levelIsZero (σ v)`, and
     `levelIsZero (σ (.max u v)) = (levelIsZero (σ u) && levelIsZero (σ v))`.

2. **§2 Structural invariants of `TyP.isSortHead` and `TyP.isSortOrPiHead`, and
   zero-recursion `PBit` discharge for `.sort` and `.pi` (`isSortHead_expr_and_type`,
   `isPiHead_expr`, `isSortHead_of_isSortOrPiHead_sort_subject`,
   `levelIsZero_false_of_isSortOrPiHead_sort_subject`,
   `pbit_of_isSortHead_and_isSortOrPiHead`, `isSortOrPiHead_of_isSortHead`,
   `atoms_reg_of_isSortHead`, `wt_reg_of_isSortHead`,
   `tyPairMeas_reg_of_isSortHead`, `pbit_of_below_and_eut_isSortHead`,
   `pbit_of_below_lex_isSortHead`, `pbit_of_below_lex_isSortOrPiHead`)**:
   - Whenever `D.isSortHead = true`, `D` has subject `.sort l`, ascribed type
     `.sort k` with `eqN k (.succ l')`, and `tyPairMeas Aw D.reg.2 DT = tyPairMeas Aw D DT`.
   - When both `D.isSortHead = true` and `DT.isSortOrPiHead = true`, `PBit σ ρ D DT`
     holds from `LevelSub σ` alone with **zero `Below` hypotheses**.
   - For arbitrary `DT` with `LexDM (tyPairMeas Aw D DT) bound`, `pbit_of_below_lex_isSortOrPiHead`
     discharges `PBit σ ρ D DT` for all `.sort`- and `.pi`-headed derivations `D`
     with **zero `PBit` recursive calls**.

3. **§3 Unconditional `Below.cts` (`CTS h DX`) and `PBit` on `.const`, `.lit`,
   `.conv`, `.lam`, and `.letE` from `Below` (`dmStep_cvTy_pair`, `lexDM_cvTy_pair`,
   `sortCoh_cvp_dl_of_below`, `cts_pack_of_below`, `pbit_const_of_below`,
   `pbit_lit_of_below`, `pbit_conv_of_below`, `pbit_lam_of_below`,
   `pbit_letE_of_below`)**:
   - `cts_pack_of_below` unconditionally discharges `CTS h DX` (`eqN s w`, the
     `Below.cts` field of `RcicSynPack`) across all 24 `CvP` constructors and all `DX`.
   - `pbit_const_of_below`, `pbit_lit_of_below`, `pbit_conv_of_below`,
     `pbit_lam_of_below`, and `pbit_letE_of_below` discharge `PBit` at arbitrary `DT`
     from `Below Aw tbl (tyPairMeas Aw D DT)` (using Option L-inline-at-0
     `letSub_eps` for `.letE` in `Γ` with zero `.letBinding` context extension).

4. **§4 Unified `CvP.delta` `ES` (`es_of_below_delta_all`, `es_of_below_delta_all_id`)**:
   - Combines `es_of_below_delta_proof` (`levelIsZero (σ hb.reg.1) = true`) and
     `es_of_below_delta_crule_eqN` (`levelIsZero (σ hb.reg.1) = false`) into a single
     branch-free theorem for `ES tbl σ ρ (CvP.delta ...)`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `LevelHom` evaluation, automatic `LevelSub`, and `imax_bit` / `max_bit` -/

/-- For any `LevelHom σ` and valuation `val : Nat → Option Nat`, evaluating `σ l`
    at `val` is identical to evaluating `l` at the pulled-back valuation
    `fun i => eval val (σ (.param i))`. -/
theorem eval_levelHom {σ : Level → Level} (hσ : LevelHom σ) (val : Nat → Option Nat) :
    (l : Level) → eval val (σ l) = eval (fun i => eval val (σ (.param i))) l
  | .zero => by
      rw [hσ.map_zero]
      rfl
  | .succ l => by
      rw [hσ.map_succ]
      simp only [eval, eval_levelHom hσ val l]
  | .max a b => by
      rw [hσ.map_max]
      simp only [eval, eval_levelHom hσ val a, eval_levelHom hσ val b]
  | .imax a b => by
      rw [hσ.map_imax]
      simp only [eval, eval_levelHom hσ val a, eval_levelHom hσ val b]
  | .param _ => rfl

/-- Every `LevelHom σ` preserves `eqN`. -/
theorem LevelHom.eqN_map {σ : Level → Level} (hσ : LevelHom σ) {l l' : Level}
    (h : eqN l l') : eqN (σ l) (σ l') := by
  intro val
  rw [eval_levelHom hσ val l, eval_levelHom hσ val l']
  exact h (fun i => eval val (σ (.param i)))

theorem LevelHom.zero_bit {σ : Level → Level} (hσ : LevelHom σ) :
    levelIsZero (σ .zero) = true := by
  rw [hσ.map_zero]
  rfl

theorem LevelHom.succ_bit {σ : Level → Level} (hσ : LevelHom σ) (l : Level) :
    levelIsZero (σ (.succ l)) = false := by
  rw [hσ.map_succ]
  rfl

/-- Every `LevelHom σ` is automatically a `LevelSub σ`. -/
theorem LevelHom.levelSub {σ : Level → Level} (hσ : LevelHom σ) : LevelSub σ where
  eqN_map := hσ.eqN_map
  zero_bit := hσ.zero_bit
  succ_bit := hσ.succ_bit

/-- For any `LevelHom σ`, `levelIsZero (σ (.imax u v)) = levelIsZero (σ v)`. -/
theorem LevelHom.imax_bit {σ : Level → Level} (hσ : LevelHom σ) (u v : Level) :
    levelIsZero (σ (.imax u v)) = levelIsZero (σ v) := by
  rw [hσ.map_imax]
  rfl

/-- For any `LevelHom σ`, `levelIsZero (σ (.max u v)) = (levelIsZero (σ u) && levelIsZero (σ v))`. -/
theorem LevelHom.max_bit {σ : Level → Level} (hσ : LevelHom σ) (u v : Level) :
    levelIsZero (σ (.max u v)) = (levelIsZero (σ u) && levelIsZero (σ v)) := by
  rw [hσ.map_max]
  rfl

/-- `DispFor` paired with `LevelHom σ` (`id` and compositions with `instLevel`). -/
structure DispForHom (σ : Level → Level) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (ρ : List Disp) : Prop where
  dispFor : DispFor σ E n Γ ρ
  levelHom : LevelHom σ

theorem dispForHom_nil {σ : Level → Level} (hσ : LevelHom σ) (E : ResolvedEnv) (n : Nat) :
    DispForHom σ E n [] [] :=
  ⟨.nil hσ.levelSub, hσ⟩

theorem dispForHom_id (E : ResolvedEnv) (n : Nat) :
    DispForHom id E n [] [] :=
  dispForHom_nil levelHom_id E n

theorem DispForHom.assumption {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A : Expr Nat} {u : Level}
    (h : DispForHom σ E n Γ ρ) (hA : TyP E n Γ A (.sort u)) :
    DispForHom σ E n (.assumption A :: Γ) (binderDisp (levelIsZero (σ u)) :: ρ) :=
  ⟨.assumption h.dispFor hA, h.levelHom⟩

theorem DispForHom.letDrop {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u : Level}
    (h : DispForHom σ E n Γ ρ) (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A)
    (hstar : hv.eps σ ρ = .star) :
    DispForHom σ E n (.letBinding A v :: Γ) (.drop :: ρ) :=
  ⟨.letDrop h.dispFor hA hv hstar, h.levelHom⟩

theorem DispForHom.letInline {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u : Level}
    (h : DispForHom σ E n Γ ρ) (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A) :
    DispForHom σ E n (.letBinding A v :: Γ) (.inline (hv.eps σ ρ) :: ρ) :=
  ⟨.letInline h.dispFor hA hv, h.levelHom⟩

theorem DispForHom.linst {σ : Level → Level} (hσ : LevelHom σ)
    {E : ResolvedEnv} {a n : Nat}
    {Γ : LCtx} {ρ : List Disp} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (hρ : DispFor (fun l => σ (instLevel ls l)) E a Γ ρ) :
    DispForHom σ E n (instLvlsCtx ls Γ) ρ :=
  ⟨dispFor_instLvlsCtx hσ.levelSub hls hlen hρ, hσ⟩

theorem dispForHom_of_ctxP {σ : Level → Level} (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hΓ : CtxP E n Γ) :
    DispForHom σ E n Γ (hΓ.disp σ) :=
  ⟨dispFor_of_ctxP hσ.levelSub hΓ, hσ⟩

/-! ## §2 Structural invariants of `TyP.isSortHead` and `TyP.isSortOrPiHead`, and `.sort` / `.pi` `PBit` -/

theorem isSortOrPiHead_of_isSortHead :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortHead = true → D.isSortOrPiHead = true
  | _, _, _, _, _, .sort .., _ => rfl
  | _, _, _, _, _, .bvar .., h => nomatch h
  | _, _, _, _, _, .const .., h => nomatch h
  | _, _, _, _, _, .pi .., h => nomatch h
  | _, _, _, _, _, .lam .., h => nomatch h
  | _, _, _, _, _, .app .., h => nomatch h
  | _, _, _, _, _, .letE .., h => nomatch h
  | _, _, _, _, _, .lit .., h => nomatch h
  | _, _, _, _, _, .conv .., h => nomatch h
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D₀ _, h =>
      isSortOrPiHead_of_isSortHead D₀ h
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D₀, h =>
      isSortOrPiHead_of_isSortHead D₀ h
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D₀, h =>
      isSortOrPiHead_of_isSortHead D₀ h
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D₀, h =>
      isSortOrPiHead_of_isSortHead D₀ h
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h =>
      isSortOrPiHead_of_isSortHead D₀ h
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h =>
      isSortOrPiHead_of_isSortHead D₀ h

/-- Whenever `D : TyP E n Γ e T` has `D.isSortHead = true`, its subject `e` is
    `.sort l` and its ascribed type `T` is `.sort k` with `eqN k (.succ l')`. -/
theorem isSortHead_expr_and_type :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortHead = true →
    (∃ l : Level, e = .sort l) ∧ (∃ k l' : Level, T = .sort k ∧ eqN k (.succ l'))
  | _, _, _, _, _, .sort _ _ _ l k h, _ =>
      ⟨⟨l, rfl⟩, ⟨k, l, rfl, h⟩⟩
  | _, _, _, _, _, .bvar .., h => nomatch h
  | _, _, _, _, _, .const .., h => nomatch h
  | _, _, _, _, _, .pi .., h => nomatch h
  | _, _, _, _, _, .lam .., h => nomatch h
  | _, _, _, _, _, .app .., h => nomatch h
  | _, _, _, _, _, .letE .., h => nomatch h
  | _, _, _, _, _, .lit .., h => nomatch h
  | _, _, _, _, _, .conv .., h => nomatch h
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D₀ _, h =>
      isSortHead_expr_and_type D₀ h
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D₀, h =>
      isSortHead_expr_and_type D₀ h
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D₀, h => by
      obtain ⟨⟨l₀, rfl⟩, ⟨k₀, l'₀, rfl, hk⟩⟩ := isSortHead_expr_and_type D₀ h
      exact ⟨⟨instLevel ls l₀, rfl⟩,
        ⟨instLevel ls k₀, instLevel ls l'₀, rfl, eqN_instLevel hk ls⟩⟩
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D₀, h => by
      obtain ⟨⟨l₀, rfl⟩, ⟨k₀, l'₀, rfl, hk⟩⟩ := isSortHead_expr_and_type D₀ h
      exact ⟨⟨l₀, rfl⟩, ⟨k₀, l'₀, rfl, hk⟩⟩
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h => by
      obtain ⟨⟨l₀, rfl⟩, ⟨k₀, l'₀, rfl, hk⟩⟩ := isSortHead_expr_and_type D₀ h
      exact ⟨⟨l₀, rfl⟩, ⟨k₀, l'₀, rfl, hk⟩⟩
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h => by
      obtain ⟨⟨l₀, rfl⟩, ⟨k₀, l'₀, rfl, hk⟩⟩ := isSortHead_expr_and_type D₀ h
      exact ⟨⟨l₀, rfl⟩, ⟨k₀, l'₀, rfl, hk⟩⟩

/-- Whenever `D : TyP E n Γ e T` has `D.isSortOrPiHead = true` and `D.isSortHead = false`,
    its subject `e` is `.pi A B`. -/
theorem isPiHead_expr :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortOrPiHead = true → D.isSortHead = false →
    ∃ A B : Expr Nat, e = .pi A B
  | _, _, _, _, _, .sort .., _, hsh => nomatch hsh
  | _, _, _, _, _, .pi _ _ _ A _ B _ _ _, _, _ => ⟨A, B, rfl⟩
  | _, _, _, _, _, .bvar .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .const .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .lam .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .app .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .letE .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .lit .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .conv .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D₀ _, hsp, hsh =>
      isPiHead_expr D₀ hsp hsh
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D₀, hsp, hsh =>
      isPiHead_expr D₀ hsp hsh
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D₀, hsp, hsh => by
      obtain ⟨A₀, B₀, rfl⟩ := isPiHead_expr D₀ hsp hsh
      exact ⟨instantiateLevels ls A₀, instantiateLevels ls B₀, rfl⟩
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D₀, hsp, hsh => by
      obtain ⟨A₀, B₀, rfl⟩ := isPiHead_expr D₀ hsp hsh
      exact ⟨lift c 1 A₀, lift (c + 1) 1 B₀, rfl⟩
  | _, _, _, _, _, .esub _ _ _ _ _ _ v j _ D₀ _ _ _, hsp, hsh => by
      obtain ⟨A₀, B₀, rfl⟩ := isPiHead_expr D₀ hsp hsh
      exact ⟨instantiate j (lift 0 j v) A₀, instantiate (j + 1) (lift 0 1 (lift 0 j v)) B₀, rfl⟩
  | _, _, _, _, _, .lsub _ _ _ _ _ _ v j _ D₀ _ _ _, hsp, hsh => by
      obtain ⟨A₀, B₀, rfl⟩ := isPiHead_expr D₀ hsp hsh
      exact ⟨instantiate j (lift 0 j v) A₀, instantiate (j + 1) (lift 0 1 (lift 0 j v)) B₀, rfl⟩

/-- Any typing `DT : TyP E n Γ (.sort k) U` with `DT.isSortOrPiHead = true` has
    `DT.isSortHead = true` (since `.sort k ≠ .pi A B`). -/
theorem isSortHead_of_isSortOrPiHead_sort_subject {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {k : Level} {U : Expr Nat} (DT : TyP E n Γ (.sort k) U)
    (hsp : DT.isSortOrPiHead = true) :
    DT.isSortHead = true := by
  cases hsh : DT.isSortHead with
  | true => rfl
  | false =>
      obtain ⟨A, B, habs⟩ := isPiHead_expr DT hsp hsh
      exact Expr.noConfusion habs

/-- Any typing `DT : TyP E n Γ (.sort k) (.sort s)` with `DT.isSortOrPiHead = true`
    forces `levelIsZero (σ s) = false` under any `LevelSub σ` (zero `Below` hypotheses). -/
theorem levelIsZero_false_of_isSortOrPiHead_sort_subject {σ : Level → Level} (hσ : LevelSub σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {k s : Level}
    (DT : TyP E n Γ (.sort k) (.sort s)) (hsp : DT.isSortOrPiHead = true) :
    levelIsZero (σ s) = false := by
  have hsh := isSortHead_of_isSortOrPiHead_sort_subject DT hsp
  obtain ⟨_, ⟨k', l', hsort, heq⟩⟩ := isSortHead_expr_and_type DT hsh
  injection hsort with hs
  subst hs
  rw [levelIsZero_congr (hσ.eqN_map heq)]
  exact hσ.succ_bit l'

/-- When both `D.isSortHead = true` and `DT.isSortOrPiHead = true`, `PBit σ ρ D DT`
    holds unconditionally from `LevelSub σ` alone (zero `Below` hypotheses). -/
theorem pbit_of_isSortHead_and_isSortOrPiHead {σ : Level → Level} (hσ : LevelSub σ)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (hD : D.isSortHead = true)
    (DT : TyP E n Γ T (.sort s)) (hDT : DT.isSortOrPiHead = true) :
    PBit σ ρ D DT := by
  obtain ⟨_, ⟨k, _, rfl, _⟩⟩ := isSortHead_expr_and_type D hD
  have hne : D.eps σ ρ ≠ .star :=
    eps_ne_star_of_isSortOrPiHead (isSortOrPiHead_of_isSortHead D hD) σ ρ
  have hz : levelIsZero (σ s) = false :=
    levelIsZero_false_of_isSortOrPiHead_sort_subject hσ DT hDT
  unfold PBit
  rw [hz]
  exact ⟨fun h0 => absurd h0 hne, fun h0 => Bool.noConfusion h0⟩

/-- Whenever `D.isSortHead = true`, `D.reg.2` has the exact same atom list as `D`. -/
theorem atoms_reg_of_isSortHead (Aw : Nat → Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortHead = true →
    D.reg.2.atoms Aw = D.atoms Aw
  | _, _, _, _, _, .sort .., _ => rfl
  | _, _, _, _, _, .bvar .., h => nomatch h
  | _, _, _, _, _, .const .., h => nomatch h
  | _, _, _, _, _, .pi .., h => nomatch h
  | _, _, _, _, _, .lam .., h => nomatch h
  | _, _, _, _, _, .app .., h => nomatch h
  | _, _, _, _, _, .letE .., h => nomatch h
  | _, _, _, _, _, .lit .., h => nomatch h
  | _, _, _, _, _, .conv .., h => nomatch h
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D₀ _, h => by
      dsimp only [TyP.reg, TyP.atoms]
      rw [atoms_reg_of_isSortHead Aw D₀ h]
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D₀, h => by
      dsimp only [TyP.reg, TyP.atoms]
      exact atoms_reg_of_isSortHead Aw D₀ h
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D₀, h => by
      dsimp only [TyP.reg, TyP.atoms]
      exact atoms_reg_of_isSortHead Aw D₀ h
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D₀, h => by
      dsimp only [TyP.reg, TyP.atoms]
      exact atoms_reg_of_isSortHead Aw D₀ h
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h => by
      dsimp only [TyP.reg, TyP.atoms]
      rw [atoms_reg_of_isSortHead Aw D₀ h]
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h => by
      dsimp only [TyP.reg, TyP.atoms]
      rw [atoms_reg_of_isSortHead Aw D₀ h]

/-- Whenever `D.isSortHead = true`, `D.reg.2` has the exact same weight as `D`. -/
theorem wt_reg_of_isSortHead (Aw : Nat → Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortHead = true →
    D.reg.2.wt Aw = D.wt Aw
  | _, _, _, _, _, .sort .., _ => rfl
  | _, _, _, _, _, .bvar .., h => nomatch h
  | _, _, _, _, _, .const .., h => nomatch h
  | _, _, _, _, _, .pi .., h => nomatch h
  | _, _, _, _, _, .lam .., h => nomatch h
  | _, _, _, _, _, .app .., h => nomatch h
  | _, _, _, _, _, .letE .., h => nomatch h
  | _, _, _, _, _, .lit .., h => nomatch h
  | _, _, _, _, _, .conv .., h => nomatch h
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D₀ _, h => by
      dsimp only [TyP.reg, TyP.wt]
      rw [wt_reg_of_isSortHead Aw D₀ h]
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D₀, h => by
      dsimp only [TyP.reg, TyP.wt]
      rw [wt_reg_of_isSortHead Aw D₀ h]
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D₀, h => by
      dsimp only [TyP.reg, TyP.wt]
      rw [wt_reg_of_isSortHead Aw D₀ h]
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D₀, h => by
      dsimp only [TyP.reg, TyP.wt]
      rw [wt_reg_of_isSortHead Aw D₀ h]
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h => by
      dsimp only [TyP.reg, TyP.wt]
      rw [wt_reg_of_isSortHead Aw D₀ h]
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D₀ _ _ _, h => by
      dsimp only [TyP.reg, TyP.wt]
      rw [wt_reg_of_isSortHead Aw D₀ h]

/-- Whenever `D.isSortHead = true`, `tyPairMeas Aw D.reg.2 DT = tyPairMeas Aw D DT`. -/
theorem tyPairMeas_reg_of_isSortHead (Aw : Nat → Nat)
    {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e₁ T₁ : Expr Nat}
    (D : TyP E₁ n₁ Γ₁ e₁ T₁) (h : D.isSortHead = true)
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (DT : TyP E₂ n₂ Γ₂ e₂ T₂) :
    tyPairMeas Aw D.reg.2 DT = tyPairMeas Aw D DT := by
  unfold tyPairMeas
  rw [atoms_reg_of_isSortHead Aw D h, wt_reg_of_isSortHead Aw D h]

/-- When `D.isSortHead = true`, `PBit σ ρ D DT` follows from `Below Aw tbl (tyPairMeas Aw D DT)`
    and `EUT tbl σ ρ D.reg.2 DT`. -/
theorem pbit_of_below_and_eut_isSortHead (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (h : D.isSortHead = true) (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw D DT))
    (heut : EUT tbl σ ρ D.reg.2 DT) :
    PBit σ ρ D DT := by
  have hBel_reg : Below Aw tbl (tyPairMeas Aw D.reg.2 DT) := by
    rw [tyPairMeas_reg_of_isSortHead Aw D h DT]
    exact Bel
  exact pbit_of_reg_and_bitCoh D DT
    (pbit_reg_of_isSortOrPiHead (isSortOrPiHead_of_isSortHead D h) hρ.levelSub ρ)
    (bitCoh_of_below_and_eut Aw hW D.reg.2 DT σ ρ hρ hBel_reg heut)

/-- When `D.isSortHead = true` and `LexDM (tyPairMeas Aw D DT) bound`, `PBit σ ρ D DT`
    follows from `Below Aw tbl bound` and `Below Aw tbl (tyPairMeas Aw D DT)` with
    **zero `PBit` recursive calls**. -/
theorem pbit_of_below_lex_isSortHead (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (h : D.isSortHead = true) (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    {bound : List Nat × Nat} (hlex : LexDM (tyPairMeas Aw D DT) bound)
    (Bel : Below Aw tbl bound) (Bel_pair : Below Aw tbl (tyPairMeas Aw D DT)) :
    PBit σ ρ D DT := by
  have hlex_reg : LexDM (tyPairMeas Aw D.reg.2 DT) bound := by
    rw [tyPairMeas_reg_of_isSortHead Aw D h DT]
    exact hlex
  exact pbit_of_below_and_eut_isSortHead Aw hW D h DT σ ρ hρ Bel_pair
    (Bel.eut D.reg.2 DT σ ρ hρ hlex_reg)

/-- For **every** `D` with `D.isSortOrPiHead = true` (both `.sort` and `.pi` heads),
    `PBit σ ρ D DT` is discharged from `Below Aw tbl bound` and
    `Below Aw tbl (tyPairMeas Aw D DT)` with **zero `PBit` recursive calls**. -/
theorem pbit_of_below_lex_isSortOrPiHead (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (hsp : D.isSortOrPiHead = true) (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    {bound : List Nat × Nat} (hlex : LexDM (tyPairMeas Aw D DT) bound)
    (Bel : Below Aw tbl bound) (Bel_pair : Below Aw tbl (tyPairMeas Aw D DT)) :
    PBit σ ρ D DT := by
  cases hsh : D.isSortHead with
  | true =>
      exact pbit_of_below_lex_isSortHead Aw hW D hsh DT σ ρ hρ hlex Bel Bel_pair
  | false =>
      exact pbit_of_below_piHead Aw tbl D hsp hsh DT σ ρ hρ Bel_pair

/-! ## §3 Unconditional `Below.cts` (`CTS h DX`) and `PBit` on `.const`, `.lit`, `.conv`, `.lam`, and `.letE` -/

/-- `h.dl.atoms Aw ++ DX.atoms Aw` is strictly `DMStep`-below `h.atoms Aw ++ DX.atoms Aw`. -/
theorem dmStep_cvTy_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat}
    (DX : TyP E' n' Γ' e' T') :
    DMStep (h.dl.atoms Aw ++ DX.atoms Aw) (h.atoms Aw ++ DX.atoms Aw) :=
  dmStep_append_right (dmStep_cvp_dl Aw h) (DX.atoms Aw)

/-- `tyPairMeas Aw h.dl DX` is strictly `LexDM`-below `cvTyMeas Aw h DX`. -/
theorem lexDM_cvTy_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat}
    (DX : TyP E' n' Γ' e' T') :
    LexDM (tyPairMeas Aw h.dl DX) (cvTyMeas Aw h DX) :=
  lex_of_dm (dmStep_cvTy_pair Aw h DX)

/-- For any `h : CvP E n Γ X Y (.sort w)` and `DX : TyP E n Γ X (.sort s)`,
    `Below Aw tbl (cvTyMeas Aw h DX)` and `Below Aw tbl (tyPairMeas Aw h.dl DX)`
    prove `SortCoh σ h.dl DX` (`eqN (σ w) (σ s)`). -/
theorem sortCoh_cvp_dl_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvTyMeas Aw h DX))
    (Bel_dl : Below Aw tbl (tyPairMeas Aw h.dl DX)) :
    SortCoh σ h.dl DX :=
  sortCoh_of_below_lex Aw hW h.dl DX σ ρ hρ (lexDM_cvTy_pair Aw h DX) Bel Bel_dl

/-- Unconditional discharge of the `Below.cts` field (`CTS h DX`, i.e. `eqN s w`)
    for **all 24 `CvP` constructors** and all `DX : TyP E n Γ X (.sort s)`. -/
theorem cts_pack_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (ρ : List Disp) (hρ : DispFor id E n Γ ρ)
    (Bel : Below Aw tbl (cvTyMeas Aw h DX))
    (Bel_dl : Below Aw tbl (tyPairMeas Aw h.dl DX)) :
    CTS h DX :=
  cts_of_sortCoh_id h DX (sortCoh_cvp_dl_of_below Aw hW h DX id ρ hρ Bel Bel_dl)

/-- `PBit` on `TyP.const` at any `DT` from `Below Aw tbl (tyPairMeas Aw (TyP.const ...) DT)`
    alone (zero `PBit` recursive calls). -/
theorem pbit_const_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀ : List Level}
    {m : CheckedMember} {u s : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
    (hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u))
    (DT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) DT)) :
    PBit σ ρ (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) DT :=
  pbit_of_below_not_isSortHead Aw tbl
    (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) rfl DT σ ρ hρ
    (pbit_const_reg σ ρ hres hlen hwf hls hT) Bel

/-- `DMStep` decrease for `TyP.lit`'s inner regularity pair `(hexp, hexp.reg.2)`. -/
theorem dmStep_lit_reg_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (hexp : TyP E n Γ (natExpand t) T) :
    DMStep (hexp.atoms Aw ++ hexp.reg.2.atoms Aw)
      ((TyP.lit E n Γ t T hexp).atoms Aw) := by
  let D := TyP.lit E n Γ t T hexp
  have hw1 : hexp.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  have hw2 : hexp.reg.2.wt Aw < D.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hexp) hw1
  change DMStep (hexp.atoms Aw ++ hexp.reg.2.atoms Aw) [D.wt Aw]
  rw [← List.append_nil (hexp.atoms Aw ++ hexp.reg.2.atoms Aw)]
  refine dmStep_of_below ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw hexp hw1 y hy
  · exact atoms_lt_of_wt_lt Aw hexp.reg.2 hw2 y hy

theorem lexDM_lit_reg_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (hexp : TyP E n Γ (natExpand t) T)
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (DT : TyP E₂ n₂ Γ₂ e₂ T₂) :
    LexDM (tyPairMeas Aw hexp hexp.reg.2)
      (tyPairMeas Aw (TyP.lit E n Γ t T hexp) DT) :=
  lex_of_dm (dmStep_drop_right (dmStep_lit_reg_pair Aw hexp) (DT.atoms Aw))

theorem pbit_lit_reg_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat} {s : Level}
    (hexp : TyP E n Γ (natExpand t) T) (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.lit E n Γ t T hexp) DT)) :
    PBit σ ρ (TyP.lit E n Γ t T hexp) (TyP.lit E n Γ t T hexp).reg.2 :=
  (pbit_lit_iff σ ρ hexp hexp.reg.2).mpr
    (Bel.pb hexp hexp.reg.2 σ ρ hρ (lexDM_lit_reg_pair Aw hexp DT))

/-- `PBit` on `TyP.lit` at any `DT` from `Below Aw tbl (tyPairMeas Aw (TyP.lit ...) DT)` alone. -/
theorem pbit_lit_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat} {s : Level}
    (hexp : TyP E n Γ (natExpand t) T) (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.lit E n Γ t T hexp) DT)) :
    PBit σ ρ (TyP.lit E n Γ t T hexp) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.lit E n Γ t T hexp) rfl DT σ ρ hρ
    (pbit_lit_reg_of_below Aw tbl hexp DT σ ρ hρ Bel) Bel

/-- `DMStep` decrease for `TyP.conv`'s inner pair `(h, hc.dl)`. -/
theorem dmStep_conv_inner_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) :
    DMStep (h.atoms Aw ++ hc.dl.atoms Aw)
      ((TyP.conv E n Γ e A B u h hc).atoms Aw) := by
  let D := TyP.conv E n Γ e A B u h hc
  have hw1 : h.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  have hwc : hc.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  have hw2 : hc.dl.wt Aw < D.wt Aw :=
    Nat.lt_trans (CvP.wt_dl_lt Aw hc) hwc
  change DMStep (h.atoms Aw ++ hc.dl.atoms Aw) [D.wt Aw]
  rw [← List.append_nil (h.atoms Aw ++ hc.dl.atoms Aw)]
  refine dmStep_of_below ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw h hw1 y hy
  · exact atoms_lt_of_wt_lt Aw hc.dl hw2 y hy

theorem lexDM_conv_inner_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (DT : TyP E₂ n₂ Γ₂ e₂ T₂) :
    LexDM (tyPairMeas Aw h hc.dl)
      (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) DT) :=
  lex_of_dm (dmStep_drop_right (dmStep_conv_inner_pair Aw h hc) (DT.atoms Aw))

theorem pbit_conv_reg_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u s : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (DT : TyP E n Γ B (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) DT)) :
    PBit σ ρ (TyP.conv E n Γ e A B u h hc) (TyP.conv E n Γ e A B u h hc).reg.2 :=
  pbit_conv_of_inner σ ρ h hc hc.dr
    (Bel.pb h hc.dl σ ρ hρ (lexDM_conv_inner_pair Aw h hc DT))
    rfl

/-- `PBit` on `TyP.conv` at any `DT` from `Below Aw tbl (tyPairMeas Aw (TyP.conv ...) DT)` alone. -/
theorem pbit_conv_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u s : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (DT : TyP E n Γ B (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) DT)) :
    PBit σ ρ (TyP.conv E n Γ e A B u h hc) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.conv E n Γ e A B u h hc) rfl DT σ ρ hρ
    (pbit_conv_reg_of_below Aw tbl h hc DT σ ρ hρ Bel) Bel

/-- `DMStep` decrease for `TyP.lam`'s body pair `(hbody, hB)`. -/
theorem dmStep_lam_body_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B : Expr Nat} {u v : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
    DMStep (hbody.atoms Aw ++ hB.atoms Aw)
      ((TyP.lam E n Γ A u body B v hA hbody hB).atoms Aw) := by
  let D := TyP.lam E n Γ A u body B v hA hbody hB
  have hw1 : hbody.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  have hw2 : hB.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  change DMStep (hbody.atoms Aw ++ hB.atoms Aw) [D.wt Aw]
  rw [← List.append_nil (hbody.atoms Aw ++ hB.atoms Aw)]
  refine dmStep_of_below ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw hbody hw1 y hy
  · exact atoms_lt_of_wt_lt Aw hB hw2 y hy

theorem lexDM_lam_body_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B : Expr Nat} {u v : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (DT : TyP E₂ n₂ Γ₂ e₂ T₂) :
    LexDM (tyPairMeas Aw hbody hB)
      (tyPairMeas Aw (TyP.lam E n Γ A u body B v hA hbody hB) DT) :=
  lex_of_dm (dmStep_drop_right (dmStep_lam_body_pair Aw hA hbody hB) (DT.atoms Aw))

theorem pbit_lam_reg_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B : Expr Nat} {u v s : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (DT : TyP E n Γ (.pi A B) (.sort s))
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.lam E n Γ A u body B v hA hbody hB) DT)) :
    PBit σ ρ (TyP.lam E n Γ A u body B v hA hbody hB)
      (TyP.lam E n Γ A u body B v hA hbody hB).reg.2 :=
  pbit_lam_of_body σ ρ hA hbody hB
    (TyP.pi E n Γ A u B v hA hB)
    (Bel.pb hbody hB σ (binderDisp (levelIsZero (σ u)) :: ρ)
      (.assumption hρ hA) (lexDM_lam_body_pair Aw hA hbody hB DT))
    (hσ.imax_bit u v).symm

/-- `PBit` on `TyP.lam` at any `DT` from `Below Aw tbl (tyPairMeas Aw (TyP.lam ...) DT)`
    and `LevelHom σ` alone. -/
theorem pbit_lam_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B : Expr Nat} {u v s : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (DT : TyP E n Γ (.pi A B) (.sort s))
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.lam E n Γ A u body B v hA hbody hB) DT)) :
    PBit σ ρ (TyP.lam E n Γ A u body B v hA hbody hB) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.lam E n Γ A u body B v hA hbody hB) rfl DT σ ρ hρ
    (pbit_lam_reg_of_below Aw tbl hA hbody hB DT hσ ρ hρ Bel) Bel

/-- `DMStep` decrease for `TyP.letE`'s Option L-inline-at-0 `letSub` pair
    `(letSub hb hv hA, hT)` in `Γ` (zero `.letBinding` context extension). -/
theorem dmStep_letE_letSub_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value B body : Expr Nat} {u w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w)) :
    DMStep ((letSub hb hv hA).atoms Aw ++ hT.atoms Aw)
      ((TyP.letE E n Γ A u value B body w hA hv hb hT).atoms Aw) := by
  let D := TyP.letE E n Γ A u value B body w hA hv hb hT
  have hwSub : (letSub hb hv hA).wt Aw < D.wt Aw := by
    have _hpos := TyP.wt_pos Aw hT
    rw [letSub_wt]
    simp only [TyP.wt]
    omega
  have hwT : hT.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  change DMStep ((letSub hb hv hA).atoms Aw ++ hT.atoms Aw) [D.wt Aw]
  rw [← List.append_nil ((letSub hb hv hA).atoms Aw ++ hT.atoms Aw)]
  refine dmStep_of_below ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw (letSub hb hv hA) hwSub y hy
  · exact atoms_lt_of_wt_lt Aw hT hwT y hy

theorem lexDM_letE_letSub_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value B body : Expr Nat} {u w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (DT : TyP E₂ n₂ Γ₂ e₂ T₂) :
    LexDM (tyPairMeas Aw (letSub hb hv hA) hT)
      (tyPairMeas Aw (TyP.letE E n Γ A u value B body w hA hv hb hT) DT) :=
  lex_of_dm (dmStep_drop_right (dmStep_letE_letSub_pair Aw hA hv hb hT) (DT.atoms Aw))

theorem pbit_letE_reg_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value B body : Expr Nat} {u w s : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (DT : TyP E n Γ (instantiate0 value B) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.letE E n Γ A u value B body w hA hv hb hT) DT)) :
    PBit σ ρ (TyP.letE E n Γ A u value B body w hA hv hb hT)
      (TyP.letE E n Γ A u value B body w hA hv hb hT).reg.2 := by
  have hpb := Bel.pb (letSub hb hv hA) hT σ ρ hρ (lexDM_letE_letSub_pair Aw hA hv hb hT DT)
  unfold PBit at hpb ⊢
  rw [letSub_eps hb hv hA σ ρ] at hpb
  rw [eps_let_clause]
  exact hpb

/-- `PBit` on `TyP.letE` at any `DT` from `Below Aw tbl (tyPairMeas Aw (TyP.letE ...) DT)`
    alone (via Option L-inline-at-0 `letSub_eps` in `Γ`, with zero `.letBinding`
    context extension). -/
theorem pbit_letE_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value B body : Expr Nat} {u w s : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (DT : TyP E n Γ (instantiate0 value B) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.letE E n Γ A u value B body w hA hv hb hT) DT)) :
    PBit σ ρ (TyP.letE E n Γ A u value B body w hA hv hb hT) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.letE E n Γ A u value B body w hA hv hb hT) rfl DT σ ρ hρ
    (pbit_letE_reg_of_below Aw tbl hA hv hb hT DT σ ρ hρ Bel) Bel

/-- `PBit` on `TyP.ewk` at its own regularity typing `D.reg.2` is identical to `PBit` on `D₀`. -/
theorem pbit_ewk_reg_iff (σ : Level → Level) (ρ : List Disp)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (hext : EnvExt E₀ E) (D₀ : TyP E₀ n Γ e A) :
    PBit σ ρ (TyP.ewk E₀ E n Γ e A hext D₀)
      (TyP.ewk E₀ E n Γ e A hext D₀).reg.2 ↔
      PBit σ ρ D₀ D₀.reg.2 :=
  Iff.rfl

/-- `PBit` on `TyP.cctx` at its own regularity typing `D.reg.2` is identical to `PBit` on `D₀`. -/
theorem pbit_cctx_reg_iff (σ : Level → Level) (ρ' : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A A' : Expr Nat} {u : Level}
    (D₀ : TyP E n (.assumption A :: Γ) e T) (hA : CvP E n Γ A A' (.sort u)) :
    PBit σ ρ' (TyP.cctx E n Γ e T A A' u D₀ hA)
      (TyP.cctx E n Γ e T A A' u D₀ hA).reg.2 ↔
      PBit σ ρ' D₀ D₀.reg.2 :=
  Iff.rfl

/-- `PBit` on `TyP.wk` at its own regularity typing `D.reg.2` from `PBit σ (removeAt ρ c) D₀ D₀.reg.2`. -/
theorem pbit_wk_reg_of_inner (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl} {c : Nat}
    (D₀ : TyP E n Γ e A)
    (hpb : PBit σ (removeAt ρ c) D₀ D₀.reg.2) :
    PBit σ ρ (TyP.wk E n Γ e A d c D₀) (TyP.wk E n Γ e A d c D₀).reg.2 :=
  pbit_wk_of_inner σ ρ D₀ D₀.reg.2 (TyP.wk E n Γ e A d c D₀).reg.2 hpb rfl

/-- `PBit` on `TyP.esub` (proof hole) at its own regularity typing `D.reg.2`. -/
theorem pbit_esub_drop_reg_of_inner (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hu : levelIsZero (σ u) = true)
    (hpb : PBit σ (insertDisp .drop j ρ) D₀ D₀.reg.2) :
    PBit σ ρ (TyP.esub E n Γ e A t v j u D₀ hget hv hvT)
      (TyP.esub E n Γ e A t v j u D₀ hget hv hvT).reg.2 :=
  pbit_esub_drop_of_inner σ ρ D₀ hget hv hvT D₀.reg.2
    (TyP.esub E n Γ e A t v j u D₀ hget hv hvT).reg.2 hu hpb rfl

/-- `DMStep` decrease for `TyP.esub`'s replacement pair `(hv, hvT)`. -/
theorem dmStep_esub_val_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    DMStep (hv.atoms Aw ++ hvT.atoms Aw)
      ((TyP.esub E n Γ e A t v j u D₀ hget hv hvT).atoms Aw) := by
  change DMStep (hv.atoms Aw ++ hvT.atoms Aw) (D₀.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw)
  rw [List.append_assoc]
  exact ⟨D₀.atoms Aw, [], hv.atoms Aw ++ hvT.atoms Aw, D₀.atoms_ne_nil Aw,
    List.Perm.refl _, List.Perm.refl _, fun _ hy => nomatch hy⟩

theorem lexDM_esub_val_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (DT : TyP E₂ n₂ Γ₂ e₂ T₂) :
    LexDM (tyPairMeas Aw hv hvT)
      (tyPairMeas Aw (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT) :=
  lex_of_dm (dmStep_drop_right (dmStep_esub_val_pair Aw D₀ hget hv hvT) (DT.atoms Aw))

/-- `PBit` on `TyP.esub` (relevant hole) at its own regularity typing `D.reg.2`, discharging
    the replacement obligation `PBit σ ρ hv hvT` from `Below Aw tbl (tyPairMeas Aw (TyP.esub ...) DT)`
    in the outer context `substRemove v j Γ` at `hρ`. -/
theorem pbit_esub_keep_reg_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u s : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s))
    (σ : Level → Level) (ρ : List Disp)
    (hρ : DispFor σ E n (substRemove v j Γ) ρ)
    (hu : levelIsZero (σ u) = false)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT))
    (hpb : PBit σ (insertDisp .keep j ρ) D₀ D₀.reg.2) :
    PBit σ ρ (TyP.esub E n Γ e A t v j u D₀ hget hv hvT)
      (TyP.esub E n Γ e A t v j u D₀ hget hv hvT).reg.2 :=
  pbit_esub_keep_of_inner σ ρ D₀ hget hv hvT D₀.reg.2
    (TyP.esub E n Γ e A t v j u D₀ hget hv hvT).reg.2 hu
    (Bel.pb hv hvT σ ρ hρ (lexDM_esub_val_pair Aw D₀ hget hv hvT DT))
    hpb rfl

/-- `PBit` on `TyP.lsub` at its own regularity typing `D.reg.2`. -/
theorem pbit_lsub_reg_of_inner (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hpb : PBit σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ)
      D₀ D₀.reg.2) :
    PBit σ ρ (TyP.lsub E n Γ e A t v j u D₀ hget hv hvT)
      (TyP.lsub E n Γ e A t v j u D₀ hget hv hvT).reg.2 :=
  pbit_lsub_of_inner σ ρ D₀ hget hv hvT D₀.reg.2
    (TyP.lsub E n Γ e A t v j u D₀ hget hv hvT).reg.2 hpb rfl

/-! ## §4 Unified `CvP.delta` `ES` (combining proof and relevant branches) -/

/-- Branch-free `ES` for `CvP.delta`: combines `es_of_below_delta_proof`
    (`levelIsZero (σ hb.reg.1) = true`) and `es_of_below_delta_crule_eqN`
    (`levelIsZero (σ hb.reg.1) = false`). -/
theorem es_of_below_delta_all (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (hDb_wt : D_b.wt Aw ≤ Aw r) (hDb_cl : D_b.ClosedWf)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hmem : deltaRule r D_b ∈ tbl)
    (hσ : ∀ l, eqN (instLevel (ls.map σ) l) (σ (instLevel ls l)))
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) := by
  cases hu : levelIsZero (σ hb.reg.1) with
  | true =>
      exact es_of_below_delta_proof Aw tbl hres hbody htrp hlen hwf hb dl dr σ ρ hρ hu Bel
  | false =>
      exact es_of_below_delta_crule_eqN Aw tbl hE hres hbody htrp hlen hwf hb dl dr
        D_b hDb_wt hDb_cl σ ρ hρ hu hmem hσ Bel

/-- At `σ = id`, `deltaRule r D_b ∈ tbl` and `D_b.ClosedWf` discharge `ES` for `CvP.delta`
    across both proof and relevant branches with zero `hu` or `hσ` hypotheses. -/
theorem es_of_below_delta_all_id (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (hDb_wt : D_b.wt Aw ≤ Aw r) (hDb_cl : D_b.ClosedWf)
    (ρ : List Disp) (hρ : DispFor id E n Γ ρ)
    (hmem : deltaRule r D_b ∈ tbl)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ES tbl id ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) := by
  cases hu : levelIsZero (id hb.reg.1) with
  | true =>
      exact es_of_below_delta_proof Aw tbl hres hbody htrp hlen hwf hb dl dr id ρ hρ hu Bel
  | false =>
      exact es_of_below_delta_crule_id Aw tbl hE hres hbody htrp hlen hwf hb dl dr
        D_b hDb_wt hDb_cl ρ hρ hu hmem Bel

end Rcic.Syn
