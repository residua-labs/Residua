import rcic.RcicSynZetaMeasureRefute
import rcic.RcicSynLetSub

/-!
# Syntactic sortRow, build step 3aq — Spine-aligned `PBit(.bvar)` (`combMeas` call table) & `letE` transport narrowing instances

`research/rcic/semantic/S3_ES_ARMS.md` §43.

This module seals the two obligations from the coordinator's `Q11` ruling on
PR #6938 (`issuecomment-6160812603`):

1. **Obligation 2 — Wall C removed, not moved (`pbit_bvar_spine`, `combMeas` call table)**:
   - `CtxP.entrySort C i` reads the sort level `u₀` recorded at index `i` of a context
     derivation spine `C : CtxP E n Γ`.
   - `DispForC σ C ρ` indexes `DispFor` directly by the spine `C : CtxP E n Γ`
     (`dispForC_of_ctxP`, `dispForC_ctxP_id`, `DispForC.toDispFor`).
   - `resolve_eq_star_iff_of_dispForC` and `pbit_bvar_spine` prove that when
     `D = TyP.bvar E n Γ i A u hlook hA` is spine-aligned (`C.entrySort i = some u`),
     `PBit σ ρ D DT` is determined by:
     (a) `BitCoh σ hA DT` on `(C, hA, DT)` (no `wk_i hA₀` copy!), and
     (b) when index `i` of `C` is `.letBinding E n Γ₀ A₀ u v₀ C₀ hA₀ hv₀`,
         `PBit σ ρ₀ hv₀ hA₀` on the tail spine `(C₀, hv₀, hA₀)`.
   - Both calls strictly decrease under `combMeas`:
     - `combLexDM_pbit_bvar_sort`: `combMeas Aw C (tyPairMeas Aw hA DT) < combMeas Aw C (tyPairMeas Aw D DT)`;
       in particular, on Wall C's `pbitWallCtxP`, `pbitVar`, `pbitSort`, the call
       measure is `([6, 1, 1], 8) < ([6, 2, 1], 9)` (`combLexDM_pbit_bvar_wall_removed`).
     - `combLexDM_pbit_bvar_let_zero`: `combMeas Aw C₀ (tyPairMeas Aw hv₀ hA₀) <
       combMeas Aw (.letBinding E n Γ₀ A₀ u₀ v₀ C₀ hA₀ hv₀) (tyPairMeas Aw D DT)`
       because `hv₀.atoms ++ hA₀.atoms ++ C₀.atoms` is Already in `C.atoms`, so
       dropping `D.atoms ++ DT.atoms` is a `DMStep`.
   - Section §2 seals the remaining `combMeas` call-table witnesses for rule calls,
     `.letBinding`-extending rules, and `wk`/`esub`/`lsub`/`ewk`/`linst` transport strips.

2. **Obligation 1 — Stop-and-report instances where `j = 0` / `c = 0` over `TyP.letE`
   crosses `.letBinding` at `1` (`AssumptionPrefix`, `not_cl_esub_letBody`, `not_cl_wk_letBody`)**:
   - `AssumptionPrefix Γ c` (`∀ d ∈ Γ.take c, ∃ A, d = .assumption A`) holds vacuously
     at cutoff `0` (`assumptionPrefix_zero`), so every top-level `wkAtZero` (`c = 0`) and
     `instEnd` (`j = 0`) emitted by `O6` / `ES` satisfies the guard at its outer boundary.
   - However, when a plain `ConvT.beta` or `ConvT.eta` derivation has a `letE` body:
     - **Instance A (`ConvT.beta` / `instEnd` at `j = 0` over `TyP.letE`, `LetHead.esub_let`)**:
       At the top context `[.assumption (.sort 1)]`, `D₁ := instEnd (betaLetBody E n) harg hA`
       uses `TyP.esub` only at `j = 0` (satisfying `AssumptionPrefix`), `D₂ := betaLetReduct E n`
       has zero transports, and `CL tbl id [.keep] D₁ D₂` holds (`cl_instEnd_letE_top`).
       Yet `letHead D₁` is `LetHead.esub_let` at `j = 0`; pushing `esub` one step into the
       let-body (`j = 1` in `esubZetaPreCtx`) violates `AssumptionPrefix esubZetaPreCtx 1`
       (`not_assumptionPrefix_esubZetaPreCtx_one`) AND falsifies `CL` against `D₂`'s let-body
       at `(zetaLetCtxP E n).disp id` for every `TableWF tbl` (`not_cl_esub_letBody`).
     - **Instance B (`ConvT.eta` / `wkAtZero` at `c = 0` over `TyP.letE`, `LetHead.wk`)**:
       At `[.assumption (.sort 1), .assumption (.sort 1)]`, `D₁ := wkAtZero (betaLetReduct E n)`
       uses `TyP.wk` only at `c = 0` (satisfying `AssumptionPrefix`), `D₂ := betaLetBody E n`
       has zero transports, and `CL tbl id [.keep, .keep] D₁ D₂` holds (`cl_wkAtZero_letE_top`).
       Yet `letHead D₁` is `LetHead.wk` at `c = 0`; pushing `wk` one step into the let-body
       (`c = 1` in `zetaLetCtx`) violates `AssumptionPrefix zetaLetCtx 1`
       (`not_assumptionPrefix_zetaLetCtx_one`) AND falsifies `CL` against `D₂`'s let-body
       at `(wkZetaCtxP E n).disp id` for every `TableWF tbl` (`not_cl_wk_letBody`).
     - `letSub_eps_eq_letE` shows that `letSub hb hv hA` (`TyP.lsub` at `j = 0`) has the
       exact same erasure as `TyP.letE` at every `σ, ρ`.
   `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Obligation 2: Spine-aligned `DispForC`, `PBit(.bvar)` from the spine, and Wall C removal -/

/-- The sort level `u₀` recorded at index `i` of a context derivation spine `C : CtxP E n Γ`. -/
def CtxP.entrySort : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    CtxP E n Γ → Nat → Option Level
  | _, _, _, .nil _ _, _ => none
  | _, _, _, .assumption _ _ _ _ u₀ _ _, 0 => some u₀
  | _, _, _, .assumption _ _ _ _ _ C _, i + 1 => C.entrySort i
  | _, _, _, .letBinding _ _ _ _ u₀ _ _ _ _, 0 => some u₀
  | _, _, _, .letBinding _ _ _ _ _ _ C _ _, i + 1 => C.entrySort i

/-- `DispFor` indexed by a fixed context derivation spine `C : CtxP E n Γ`. -/
inductive DispForC (σ : Level → Level) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → CtxP E n Γ → List Disp → Prop
  | nil {E : ResolvedEnv} {n : Nat} (hσ : LevelSub σ) :
      DispForC σ (.nil E n) []
  | assumption {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A : Expr Nat} {u₀ : Level} {C : CtxP E n Γ} (hA₀ : TyP E n Γ A (.sort u₀))
      (hC : DispForC σ C ρ) :
      DispForC σ (.assumption E n Γ A u₀ C hA₀) (binderDisp (levelIsZero (σ u₀)) :: ρ)
  | letDrop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A v : Expr Nat} {u₀ : Level} {C : CtxP E n Γ}
      (hA₀ : TyP E n Γ A (.sort u₀)) (hv₀ : TyP E n Γ v A)
      (hC : DispForC σ C ρ) (hstar : hv₀.eps σ ρ = .star) :
      DispForC σ (.letBinding E n Γ A u₀ v C hA₀ hv₀) (.drop :: ρ)
  | letInline {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ : List Disp}
      {A v : Expr Nat} {u₀ : Level} {C : CtxP E n Γ}
      (hA₀ : TyP E n Γ A (.sort u₀)) (hv₀ : TyP E n Γ v A)
      (hC : DispForC σ C ρ) :
      DispForC σ (.letBinding E n Γ A u₀ v C hA₀ hv₀) (.inline (hv₀.eps σ ρ) :: ρ)

theorem DispForC.levelSub {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    (h : DispForC σ C ρ) : LevelSub σ := by
  induction h with
  | nil hσ => exact hσ
  | assumption _ _ ih => exact ih
  | letDrop _ _ _ _ ih => exact ih
  | letInline _ _ _ ih => exact ih

theorem DispForC.toDispFor {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    (h : DispForC σ C ρ) : DispFor σ E n Γ ρ := by
  induction h with
  | nil hσ => exact .nil hσ
  | assumption hA₀ _ ih => exact .assumption ih hA₀
  | letDrop hA₀ hv₀ _ hstar ih => exact .letDrop ih hA₀ hv₀ hstar
  | letInline hA₀ hv₀ _ ih => exact .letInline ih hA₀ hv₀

theorem dispForC_of_ctxP {σ : Level → Level} (hσ : LevelSub σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (C : CtxP E n Γ) :
    DispForC σ C (C.disp σ) := by
  induction C with
  | nil => exact .nil hσ
  | assumption Γ₀ A u₀ C₀ hA₀ ih =>
      have hd : CtxP.disp σ (.assumption E n Γ₀ A u₀ C₀ hA₀) =
          binderDisp (levelIsZero (σ u₀)) :: C₀.disp σ := by
        cases hzu : levelIsZero (σ u₀) <;> simp only [CtxP.disp, binderDisp, hzu]
      rw [hd]
      exact .assumption hA₀ ih
  | letBinding _ _ _ _ _ hA₀ hv₀ ih =>
      exact .letInline hA₀ hv₀ ih

theorem dispForC_ctxP_id {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (C : CtxP E n Γ) :
    DispForC id C (C.disp id) :=
  dispForC_of_ctxP levelSub_id C

/-- The spine's value-bit obligation at index `i`: `True` when entry `i` is `.assumption`,
    and `PBit σ ρ₀ hv₀ hA₀` (in the tail spine `C₀`) when entry `i` is `.letBinding`. -/
def SpineLetPBit (σ : Level → Level) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    CtxP E n Γ → List Disp → Nat → Prop
  | _, _, _, .nil _ _, _, _ => True
  | _, _, _, .assumption _ _ _ _ _ _ _, _, 0 => True
  | _, _, _, .assumption _ _ _ _ _ C _, _ :: ρ, i + 1 => SpineLetPBit σ C ρ i
  | _, _, _, .assumption _ _ _ _ _ _ _, [], _ + 1 => True
  | _, _, _, .letBinding _ _ _ _ _ _ _ hA₀ hv₀, _ :: ρ, 0 => PBit σ ρ hv₀ hA₀
  | _, _, _, .letBinding _ _ _ _ _ _ _ _ _, [], 0 => True
  | _, _, _, .letBinding _ _ _ _ _ _ C _ _, _ :: ρ, i + 1 => SpineLetPBit σ C ρ i
  | _, _, _, .letBinding _ _ _ _ _ _ _ _ _, [], _ + 1 => True

private theorem lift_eq_star_iff (c k : Nat) (t : ETm) :
    t.lift c k = .star ↔ t = .star :=
  ⟨lift_eq_star, fun h => by subst h; rfl⟩

/-- Along any `DispForC σ C ρ`, `resolve ρ i = .star` iff the spine's recorded sort `u₀`
    at index `i` has `levelIsZero (σ u₀) = true`, given `SpineLetPBit σ C ρ i`. -/
theorem resolve_eq_star_iff_of_dispForC {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    (hC : DispForC σ C ρ) :
    ∀ {i : Nat} {u₀ : Level},
      SpineLetPBit σ C ρ i → C.entrySort i = some u₀ →
      (resolve ρ i = .star ↔ levelIsZero (σ u₀) = true) := by
  induction hC with
  | nil =>
      intro i u₀ _ hsort
      cases i <;> nomatch hsort
  | @assumption _ ρ₀ _ u_head C₀ _ _ ih =>
      intro i u₀ hlet hsort
      cases i with
      | zero =>
          injection hsort with hu
          subst hu
          cases hzu : levelIsZero (σ u_head) with
          | true =>
              exact Iff.intro (fun _ => rfl) (fun _ => rfl)
          | false =>
              exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)
      | succ i =>
          change SpineLetPBit σ C₀ ρ₀ i at hlet
          change C₀.entrySort i = some u₀ at hsort
          cases hzu : levelIsZero (σ u_head) with
          | true =>
              simpa only [binderDisp, resolve] using ih hlet hsort
          | false =>
              simp only [binderDisp, resolve, lift_eq_star_iff]
              exact ih hlet hsort
  | @letDrop _ ρ₀ _ _ u_head C₀ hA₀ hv₀ _ hstar ih =>
      intro i u₀ hlet hsort
      cases i with
      | zero =>
          injection hsort with hu
          subst hu
          change PBit σ ρ₀ hv₀ hA₀ at hlet
          have hzu : levelIsZero (σ u_head) = true := hlet.mp hstar
          simp only [resolve, hzu]
      | succ i =>
          change SpineLetPBit σ C₀ ρ₀ i at hlet
          change C₀.entrySort i = some u₀ at hsort
          simpa only [resolve] using ih hlet hsort
  | @letInline _ ρ₀ _ _ u_head C₀ hA₀ hv₀ _ ih =>
      intro i u₀ hlet hsort
      cases i with
      | zero =>
          injection hsort with hu
          subst hu
          change PBit σ ρ₀ hv₀ hA₀ at hlet
          simpa only [resolve] using hlet
      | succ i =>
          change SpineLetPBit σ C₀ ρ₀ i at hlet
          change C₀.entrySort i = some u₀ at hsort
          simpa only [resolve] using ih hlet hsort

/-- Spine-aligned `PBit(.bvar)`: when `C.entrySort i = some u`, `PBit` on
    `TyP.bvar E n Γ i A u hlook hA` and `DT` follows from `SpineLetPBit σ C ρ i`
    and `BitCoh σ hA DT`, with **zero** `BitCoh` call on `(wk_i hA₀, hA)`. -/
theorem pbit_bvar_spine {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {A : Expr Nat} {u s : Level}
    {hlook : lookupType Γ i = some A}
    {hA : TyP E n Γ A (.sort u)} {DT : TyP E n Γ A (.sort s)}
    (hC : DispForC σ C ρ)
    (hsort : C.entrySort i = some u)
    (hlet : SpineLetPBit σ C ρ i)
    (hcoh : BitCoh σ hA DT) :
    PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) DT := by
  unfold PBit
  unfold BitCoh at hcoh
  rw [← hcoh]
  cases hzu : levelIsZero (σ u) with
  | true =>
      rw [eps_bvar_proof hzu]
      exact ⟨fun _ => rfl, fun _ => rfl⟩
  | false =>
      rw [eps_bvar_rel hzu]
      have hres := resolve_eq_star_iff_of_dispForC hC hlet hsort
      rw [hzu] at hres
      exact hres

/-- Specialization at `i = 0` on `.assumption`: `PBit` needs only `BitCoh σ hA DT`. -/
theorem pbit_bvar_zero_assumption {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp}
    {A₀ A : Expr Nat} {u s : Level}
    (hA₀ : TyP E n Γ₀ A₀ (.sort u))
    {hlook : lookupType (.assumption A₀ :: Γ₀) 0 = some A}
    {hA : TyP E n (.assumption A₀ :: Γ₀) A (.sort u)}
    {DT : TyP E n (.assumption A₀ :: Γ₀) A (.sort s)}
    (hC₀ : DispForC σ C₀ ρ₀)
    (hcoh : BitCoh σ hA DT) :
    PBit σ (binderDisp (levelIsZero (σ u)) :: ρ₀)
      (TyP.bvar E n (.assumption A₀ :: Γ₀) 0 A u hlook hA) DT :=
  pbit_bvar_spine (.assumption hA₀ hC₀) rfl trivial hcoh

/-- Specialization at `i = 0` on `.letBinding`: `PBit` needs only `PBit σ ρ₀ hv₀ hA₀`
    in the tail spine `C₀` and `BitCoh σ hA DT`. -/
theorem pbit_bvar_zero_letBinding {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {d₀ : Disp} {ρ₀ : List Disp}
    {A₀ v₀ A : Expr Nat} {u s : Level}
    {hA₀ : TyP E n Γ₀ A₀ (.sort u)} {hv₀ : TyP E n Γ₀ v₀ A₀}
    {hlook : lookupType (.letBinding A₀ v₀ :: Γ₀) 0 = some A}
    {hA : TyP E n (.letBinding A₀ v₀ :: Γ₀) A (.sort u)}
    {DT : TyP E n (.letBinding A₀ v₀ :: Γ₀) A (.sort s)}
    (hC : DispForC σ (.letBinding E n Γ₀ A₀ u v₀ C₀ hA₀ hv₀) (d₀ :: ρ₀))
    (hpb₀ : PBit σ ρ₀ hv₀ hA₀)
    (hcoh : BitCoh σ hA DT) :
    PBit σ (d₀ :: ρ₀)
      (TyP.bvar E n (.letBinding A₀ v₀ :: Γ₀) 0 A u hlook hA) DT :=
  pbit_bvar_spine hC rfl hpb₀ hcoh

/-! ## §2 `combMeas` call-table witnesses (Wall C removed + all rule/transport arms) -/

private theorem dmStep_append_right' (Z : List Nat) {M' M : List Nat} (h : DMStep M' M) :
    DMStep (M' ++ Z) (M ++ Z) := by
  rcases h with ⟨X, Y, W, hX, hMW, hYW, hlt⟩
  refine ⟨X, Y, W ++ Z, hX, ?_, ?_, hlt⟩
  · rw [← List.append_assoc]
    exact hMW.append_right Z
  · rw [← List.append_assoc]
    exact hYW.append_right Z

private theorem dmStep_append_left' (Z : List Nat) {M' M : List Nat} (h : DMStep M' M) :
    DMStep (Z ++ M') (Z ++ M) := by
  rcases dmStep_append_right' Z h with ⟨X, Y, W, hX, hMW, hYW, hlt⟩
  exact ⟨X, Y, W, hX, List.perm_append_comm.trans hMW, List.perm_append_comm.trans hYW, hlt⟩

private theorem dmStep_of_perm {M₁ M₂ N₁ N₂ : List Nat}
    (hM : M₂.Perm M₁) (hN : N₂.Perm N₁) (h : DMStep N₁ M₁) :
    DMStep N₂ M₂ := by
  rcases h with ⟨X, Y, Z, hX, hMX, hNY, hlt⟩
  exact ⟨X, Y, Z, hX, hM.trans hMX, hN.trans hNY, hlt⟩

/-- Call-table witness for `PBit(.bvar)`'s `BitCoh σ hA DT` call:
    `hA` is a strict subderivation of `D = TyP.bvar E n Γ i A u hlook hA`
    (`hA.wt < D.wt`), so `(C, (hA, DT))` strictly decreases under `combMeas`. -/
theorem combLexDM_pbit_bvar_sort (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat} {u s : Level}
    (C : CtxP E n Γ) (hlook : lookupType Γ i = some A)
    (hA : TyP E n Γ A (.sort u)) (DT : TyP E n Γ A (.sort s)) :
    LexDM
      (combMeas Aw C (tyPairMeas Aw hA DT))
      (combMeas Aw C (tyPairMeas Aw (TyP.bvar E n Γ i A u hlook hA) DT)) := by
  let D := TyP.bvar E n Γ i A u hlook hA
  have hlt : ∀ y ∈ hA.atoms Aw, y < D.wt Aw :=
    atoms_lt_of_wt_lt Aw hA (by simp only [D, TyP.wt]; omega)
  have hdm0 : DMStep (hA.atoms Aw) (D.atoms Aw) := by
    change DMStep (hA.atoms Aw) [D.wt Aw]
    rw [← List.append_nil (hA.atoms Aw)]
    exact dmStep_of_below hlt
  have hdm1 : DMStep (hA.atoms Aw ++ DT.atoms Aw) (D.atoms Aw ++ DT.atoms Aw) :=
    dmStep_append_right' (DT.atoms Aw) hdm0
  exact lex_of_dm (dmStep_append_left' (C.atoms Aw) hdm1)

/-- On Wall C's concrete instance (`pbitWallCtxP`, `pbitVar`, `pbitSort`), the
    spine-aligned `BitCoh` call on `(pbitSort, pbitSort)` strictly decreases under
    `combMeas` (`[6, 1, 1] < [6, 2, 1]`). -/
theorem combLexDM_pbit_bvar_wall_removed (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    LexDM
      (combMeas Aw (pbitWallCtxP E n) (tyPairMeas Aw (pbitSort E n) (pbitSort E n)))
      (combMeas Aw (pbitWallCtxP E n) (tyPairMeas Aw (pbitVar E n) (pbitSort E n))) :=
  combLexDM_pbit_bvar_sort Aw (pbitWallCtxP E n) pbit_lookup (pbitSort E n) (pbitSort E n)

/-- Call-table witness for `PBit(.bvar)`'s `PBit σ ρ₀ hv₀ hA₀` call on a `.letBinding`
    spine entry: `hv₀.atoms ++ hA₀.atoms ++ C₀.atoms` is a permutation of `C.atoms`,
    so passing from `(C, (D, DT))` to `(C₀, (hv₀, hA₀))` drops `D.atoms ++ DT.atoms`
    and is a `DMStep` under `combMeas`. -/
theorem combLexDM_pbit_bvar_let_zero (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A₀ v₀ e T : Expr Nat} {u₀ s : Level}
    (C₀ : CtxP E n Γ₀) (hA₀ : TyP E n Γ₀ A₀ (.sort u₀)) (hv₀ : TyP E n Γ₀ v₀ A₀)
    (D : TyP E n (.letBinding A₀ v₀ :: Γ₀) e T)
    (DT : TyP E n (.letBinding A₀ v₀ :: Γ₀) T (.sort s)) :
    LexDM
      (combMeas Aw C₀ (tyPairMeas Aw hv₀ hA₀))
      (combMeas Aw (.letBinding E n Γ₀ A₀ u₀ v₀ C₀ hA₀ hv₀) (tyPairMeas Aw D DT)) := by
  have hne : D.atoms Aw ++ DT.atoms Aw ≠ [] := by
    intro hnil
    exact TyP.atoms_ne_nil Aw D (List.append_eq_nil.mp hnil).1
  have hdrop :
      DMStep (hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw)
        ((D.atoms Aw ++ DT.atoms Aw) ++ (hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw)) :=
    dmStep_drop hne
  have hpermM :
      ((hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw) ++ (D.atoms Aw ++ DT.atoms Aw)).Perm
        ((D.atoms Aw ++ DT.atoms Aw) ++ (hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw)) :=
    List.perm_append_comm
  have hpermN :
      (C₀.atoms Aw ++ (hv₀.atoms Aw ++ hA₀.atoms Aw)).Perm
        (hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw) := by
    have hp1 :
        (C₀.atoms Aw ++ (hv₀.atoms Aw ++ hA₀.atoms Aw)).Perm
          ((hv₀.atoms Aw ++ hA₀.atoms Aw) ++ C₀.atoms Aw) :=
      List.perm_append_comm
    have hp2 :
        ((hv₀.atoms Aw ++ hA₀.atoms Aw) ++ C₀.atoms Aw).Perm
          ((hA₀.atoms Aw ++ hv₀.atoms Aw) ++ C₀.atoms Aw) :=
      List.Perm.append_right (C₀.atoms Aw) List.perm_append_comm
    exact hp1.trans hp2
  exact lex_of_dm (dmStep_of_perm hpermM hpermN hdrop)

/-- Call-table witness for a rule node `hnode` (`isTransport = false`) calling `ES`
    on a lighter conversion `k` in the same context spine `C`. -/
theorem combLexDM_rule_cv (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T a' b' T' : Expr Nat}
    (C : CtxP E n Γ) (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (k : CvP E n Γ a' b' T') (hw : k.wt Aw < hnode.wt Aw) :
    LexDM (combMeas Aw C (cvMeas Aw k)) (combMeas Aw C (cvMeas Aw hnode)) :=
  lex_of_dm (dmStep_append_left' (C.atoms Aw) (dmStep_cv_below Aw hnode ht k hw))

/-- Call-table witness for a rule node `hnode` (`isTransport = false`) calling
    `CL` / `EUT` / `PBit` / `SortCoh` / `BitCoh` on two lighter typings `(D₁, D₂)`
    in the same context spine `C`. -/
theorem combLexDM_rule_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T e₁ T₁ e₂ T₂ : Expr Nat}
    (C : CtxP E n Γ) (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (D₁ : TyP E n Γ e₁ T₁) (D₂ : TyP E n Γ e₂ T₂)
    (hw₁ : D₁.wt Aw < hnode.wt Aw) (hw₂ : D₂.wt Aw < hnode.wt Aw) :
    LexDM (combMeas Aw C (tyPairMeas Aw D₁ D₂)) (combMeas Aw C (cvMeas Aw hnode)) :=
  lex_of_dm (dmStep_append_left' (C.atoms Aw) (dmStep_pair_below Aw hnode ht D₁ D₂ hw₁ hw₂))

/-- Call-table witness for `.letBinding`-extending rule arms (`CvP.letE`, `CvP.zeta`):
    extending `C` by `.letBinding E n Γ A u v C hA hv` with `hA.wt < hnode.wt`,
    `hv.wt < hnode.wt`, and inner atoms `< hnode.wt` strictly decreases under `combMeas`. -/
theorem combLexDM_let_rule (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v a b T : Expr Nat} {u : Level}
    (C : CtxP E n Γ) (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A)
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (hwA : hA.wt Aw < hnode.wt Aw) (hwv : hv.wt Aw < hnode.wt Aw)
    {Y : List Nat} {wY : Nat} (hY : ∀ y ∈ Y, y < hnode.wt Aw) :
    LexDM (combMeas Aw (.letBinding E n Γ A u v C hA hv) (Y, wY))
      (combMeas Aw C (cvMeas Aw hnode)) := by
  have hsub : ∀ y ∈ (hA.atoms Aw ++ hv.atoms Aw) ++ Y, y < hnode.wt Aw := by
    intro y hy
    rcases List.mem_append.mp hy with hyAv | hyY
    · rcases List.mem_append.mp hyAv with hyA | hyv
      · exact atoms_lt_of_wt_lt Aw hA hwA y hyA
      · exact atoms_lt_of_wt_lt Aw hv hwv y hyv
    · exact hY y hyY
  have hdm0 : DMStep ((hA.atoms Aw ++ hv.atoms Aw) ++ Y) (hnode.atoms Aw) :=
    dmStep_under_rule Aw hnode ht hsub
  have hdm1 :
      DMStep (C.atoms Aw ++ ((hA.atoms Aw ++ hv.atoms Aw) ++ Y))
        (C.atoms Aw ++ hnode.atoms Aw) :=
    dmStep_append_left' (C.atoms Aw) hdm0
  have hperm :
      (((hA.atoms Aw ++ hv.atoms Aw) ++ C.atoms Aw) ++ Y).Perm
        (C.atoms Aw ++ ((hA.atoms Aw ++ hv.atoms Aw) ++ Y)) := by
    rw [← List.append_assoc]
    exact List.perm_append_comm.append_right Y
  exact lex_of_dm (dmStep_of_perm (List.Perm.refl _) hperm hdm1)

/-- Call-table witness for stripping `wk` at `c = 0`: the weakened assumption `hA`
    is dropped from the context spine `C_out = .assumption E n Γ A u C₀ hA`, while
    `D.atoms` is unchanged (`DMStep` via `dmStep_drop`). -/
theorem combLexDM_wk_strip (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    (C₀ : CtxP E n Γ) (hA : TyP E n Γ A (.sort u))
    (M : List Nat) (w w' : Nat) :
    LexDM (combMeas Aw C₀ (M, w'))
      (combMeas Aw (.assumption E n Γ A u C₀ hA) (M, w)) := by
  have hdrop : DMStep (C₀.atoms Aw ++ M) (hA.atoms Aw ++ (C₀.atoms Aw ++ M)) :=
    dmStep_drop (TyP.atoms_ne_nil Aw hA)
  have hperm :
      ((hA.atoms Aw ++ C₀.atoms Aw) ++ M).Perm (hA.atoms Aw ++ (C₀.atoms Aw ++ M)) := by
    rw [List.append_assoc]
  exact lex_of_dm (dmStep_of_perm hperm (List.Perm.refl _) hdrop)

/-- Call-table witness for stripping `esub` at `j = 0`: `hvT.atoms` moves into the
    extended context spine `.assumption E n Γ t u C₀ hvT` and `hv.atoms` (non-empty)
    is dropped (`DMStep` via `dmStep_drop`). -/
theorem combLexDM_esub_strip (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {u : Level}
    (C₀ : CtxP E n Γ)
    (D : TyP E n (.assumption t :: Γ) e A)
    (hv : TyP E n (substRemove v 0 (.assumption t :: Γ)) (lift 0 0 v) (lift 0 0 t))
    (hvT : TyP E n Γ t (.sort u))
    (Z : List Nat) (w w' : Nat) :
    LexDM
      (combMeas Aw (.assumption E n Γ t u C₀ hvT) (D.atoms Aw ++ Z, w'))
      (combMeas Aw C₀ ((D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw) ++ Z, w)) := by
  have hdrop :
      DMStep ((hvT.atoms Aw ++ C₀.atoms Aw) ++ (D.atoms Aw ++ Z))
        (hv.atoms Aw ++ ((hvT.atoms Aw ++ C₀.atoms Aw) ++ (D.atoms Aw ++ Z))) :=
    dmStep_drop (TyP.atoms_ne_nil Aw hv)
  have hperm :
      (C₀.atoms Aw ++ ((D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw) ++ Z)).Perm
        (hv.atoms Aw ++ ((hvT.atoms Aw ++ C₀.atoms Aw) ++ (D.atoms Aw ++ Z))) := by
    have hp1 :
        ((D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw) ++ Z).Perm
          ((hv.atoms Aw ++ hvT.atoms Aw) ++ (D.atoms Aw ++ Z)) := by
      have hp0 :
          (D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw).Perm
            ((hv.atoms Aw ++ hvT.atoms Aw) ++ D.atoms Aw) := by
        rw [List.append_assoc (D.atoms Aw)]
        exact List.perm_append_comm
      rw [← List.append_assoc]
      exact hp0.append_right Z
    have hp2 :
        (C₀.atoms Aw ++ ((D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw) ++ Z)).Perm
          (C₀.atoms Aw ++ ((hv.atoms Aw ++ hvT.atoms Aw) ++ (D.atoms Aw ++ Z))) :=
      List.Perm.append_left (C₀.atoms Aw) hp1
    have hp3 :
        (C₀.atoms Aw ++ ((hv.atoms Aw ++ hvT.atoms Aw) ++ (D.atoms Aw ++ Z))).Perm
          ((C₀.atoms Aw ++ (hv.atoms Aw ++ hvT.atoms Aw)) ++ (D.atoms Aw ++ Z)) := by
      rw [← List.append_assoc (C₀.atoms Aw)]
    have hp4 :
        (C₀.atoms Aw ++ (hv.atoms Aw ++ hvT.atoms Aw)).Perm
          (hv.atoms Aw ++ (hvT.atoms Aw ++ C₀.atoms Aw)) := by
      rw [← List.append_assoc (hv.atoms Aw)]
      exact List.perm_append_comm
    have hp5 :
        ((C₀.atoms Aw ++ (hv.atoms Aw ++ hvT.atoms Aw)) ++ (D.atoms Aw ++ Z)).Perm
          (hv.atoms Aw ++ ((hvT.atoms Aw ++ C₀.atoms Aw) ++ (D.atoms Aw ++ Z))) := by
      rw [← List.append_assoc (hv.atoms Aw)]
      exact hp4.append_right (D.atoms Aw ++ Z)
    exact hp2.trans (hp3.trans hp5)
  exact lex_of_dm (dmStep_of_perm hperm (List.Perm.refl _) hdrop)

/-- Call-table witness for `esub`'s replacement-bit call `(C₀, (hv, hvT))`:
    `D.atoms ++ Z` is dropped while `C₀.atoms ++ (hv.atoms ++ hvT.atoms)` is kept (`DMStep`). -/
theorem combLexDM_esub_repl (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {u : Level}
    (C₀ : CtxP E n Γ)
    (D : TyP E n (.assumption t :: Γ) e A)
    (hv : TyP E n Γ v t)
    (hvT : TyP E n Γ t (.sort u))
    (Z : List Nat) (w w' : Nat) :
    LexDM
      (combMeas Aw C₀ (hv.atoms Aw ++ hvT.atoms Aw, w'))
      (combMeas Aw C₀ ((D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw) ++ Z, w)) := by
  have hne : D.atoms Aw ++ Z ≠ [] := by
    intro hnil
    exact TyP.atoms_ne_nil Aw D (List.append_eq_nil.mp hnil).1
  have hdrop :
      DMStep (hv.atoms Aw ++ hvT.atoms Aw)
        ((D.atoms Aw ++ Z) ++ (hv.atoms Aw ++ hvT.atoms Aw)) :=
    dmStep_drop hne
  have hperm :
      ((D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw) ++ Z).Perm
        ((D.atoms Aw ++ Z) ++ (hv.atoms Aw ++ hvT.atoms Aw)) := by
    have hp0 :
        (D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw).Perm
          (D.atoms Aw ++ (hv.atoms Aw ++ hvT.atoms Aw)) := by
      rw [List.append_assoc]
    have hp1 :
        ((D.atoms Aw ++ (hv.atoms Aw ++ hvT.atoms Aw)) ++ Z).Perm
          (D.atoms Aw ++ ((hv.atoms Aw ++ hvT.atoms Aw) ++ Z)) := by
      rw [List.append_assoc]
    have hp2 :
        (D.atoms Aw ++ ((hv.atoms Aw ++ hvT.atoms Aw) ++ Z)).Perm
          (D.atoms Aw ++ (Z ++ (hv.atoms Aw ++ hvT.atoms Aw))) :=
      List.Perm.append_left (D.atoms Aw) List.perm_append_comm
    have hp3 :
        (D.atoms Aw ++ (Z ++ (hv.atoms Aw ++ hvT.atoms Aw))).Perm
          ((D.atoms Aw ++ Z) ++ (hv.atoms Aw ++ hvT.atoms Aw)) := by
      rw [List.append_assoc]
    exact (hp0.append_right Z).trans (hp1.trans (hp2.trans hp3))
  have hdm0 :
      DMStep (hv.atoms Aw ++ hvT.atoms Aw)
        ((D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw) ++ Z) :=
    dmStep_of_perm hperm (List.Perm.refl _) hdrop
  exact lex_of_dm (dmStep_append_left' (C₀.atoms Aw) hdm0)

/-- Call-table witness for stripping `ewk` or `linst` (weight drops while the
    combined atom multiset is identical, `Prod.Lex.right`). -/
theorem combLexDM_ewk_strip (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (C : CtxP E n Γ) (M : List Nat) {w w' : Nat} (hw : w' < w) :
    LexDM (combMeas Aw C (M, w')) (combMeas Aw C (M, w)) :=
  Prod.Lex.right _ (Nat.add_lt_add_left hw (C.wt Aw))

/-- Synonym for `linst` strip (`Prod.Lex.right` when the atom multiset is preserved). -/
theorem combLexDM_linst_strip (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (C : CtxP E n Γ) (M : List Nat) {w w' : Nat} (hw : w' < w) :
    LexDM (combMeas Aw C (M, w')) (combMeas Aw C (M, w)) :=
  combLexDM_ewk_strip Aw C M hw

/-! ## §3 Obligation 1: `.assumption`-only prefix guard & `j = 0` / `c = 0` over `TyP.letE` narrowing instances -/

/-- The `.assumption`-only prefix guard on transport cutoffs/indices (`Q11`). -/
def AssumptionPrefix (Γ : LCtx) (c : Nat) : Prop :=
  ∀ d ∈ Γ.take c, ∃ A, d = .assumption A

/-- At cutoff/index `0`, `Γ.take 0 = []`, so `AssumptionPrefix Γ 0` holds for every `Γ`. -/
theorem assumptionPrefix_zero (Γ : LCtx) : AssumptionPrefix Γ 0 := by
  intro d hd
  nomatch hd

/-- `zetaLetCtx.take 1 = [.letBinding (.sort 1) (.bvar 0)]` violates `AssumptionPrefix` at `1`. -/
theorem not_assumptionPrefix_zetaLetCtx_one : ¬ AssumptionPrefix zetaLetCtx 1 := by
  intro h
  rcases h (.letBinding (.sort (.succ .zero)) (.bvar 0)) (.head _) with ⟨A, hA⟩
  nomatch hA

/-- `esubZetaPreCtx.take 1 = [.letBinding (.sort 1) (.bvar 1)]` violates `AssumptionPrefix` at `1`. -/
theorem not_assumptionPrefix_esubZetaPreCtx_one : ¬ AssumptionPrefix esubZetaPreCtx 1 := by
  intro h
  rcases h (.letBinding (.sort (.succ .zero)) (.bvar 1)) (.head _) with ⟨A, hA⟩
  nomatch hA

/-- Plain, transport-free typing of `let z : sort 1 := x₁ in z` in
    `[.assumption (.sort 1), .assumption (.sort 1)]` (`x₁ : sort 1, x₀ : sort 1`). -/
def betaLetBody (E : ResolvedEnv) (n : Nat) :
    TyP E n [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]
      (.letE (.sort (.succ .zero)) (.bvar 1) (.bvar 0)) (.sort (.succ .zero)) :=
  let Γ₂ : LCtx := [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]
  TyP.letE E n Γ₂
    (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 1)
    (.sort (.succ .zero)) (.bvar 0) (.succ (.succ .zero))
    (TyP.sort E n Γ₂ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.bvar E n Γ₂ 1 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n Γ₂ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (esubZetaPreNode E n).dl
    (TyP.sort E n Γ₂ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- Plain, transport-free typing of the β-reduct `let z : sort 1 := x₀ in z` in
    `[.assumption (.sort 1)]` (`x₀ : sort 1`). -/
def betaLetReduct (E : ResolvedEnv) (n : Nat) :
    TyP E n [.assumption (.sort (.succ .zero))]
      (.letE (.sort (.succ .zero)) (.bvar 0) (.bvar 0)) (.sort (.succ .zero)) :=
  let Γ₁ : LCtx := [.assumption (.sort (.succ .zero))]
  TyP.letE E n Γ₁
    (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)
    (.sort (.succ .zero)) (.bvar 0) (.succ (.succ .zero))
    (TyP.sort E n Γ₁ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.bvar E n Γ₁ 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n Γ₁ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (zetaLetNode E n).dl
    (TyP.sort E n Γ₁ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- **Instance A (top level, `j = 0`)**: `instEnd` at `j = 0` of `betaLetBody`
    (which satisfies `AssumptionPrefix _ 0`) and `betaLetReduct` (zero transports)
    satisfy `CL` at `ρ = [.keep]`. -/
theorem cl_instEnd_letE_top (tbl : List CRule) (E : ResolvedEnv) (n : Nat) :
    let Γ₁ : LCtx := [.assumption (.sort (.succ .zero))]
    let harg := TyP.sort E n Γ₁ .zero (.succ .zero) (eqN_refl _)
    let hA := TyP.sort E n Γ₁ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)
    CL tbl id [.keep] (instEnd (betaLetBody E n) harg hA) (betaLetReduct E n) := by
  intro Γ₁ harg hA
  have hl : (instEnd (betaLetBody E n) harg hA).eps id [.keep] = .bvar 0 := rfl
  have hr : (betaLetReduct E n).eps id [.keep] = .bvar 0 := rfl
  unfold CL
  rw [hl, hr]
  exact .refl _

/-- **Instance A (pushed 1 step into the let-body by `LetHead.esub_let`, `j = 1`)**:
    pushing `esub` at `j = 0` under `.letBinding` produces `(esubZetaNode E n).dl`
    (`TyP.esub` at `j = 1` over `(esubZetaPreNode E n).dl`, violating
    `AssumptionPrefix esubZetaPreCtx 1`), which falsifies `CL` against
    `betaLetReduct`'s let-body `(zetaLetNode E n).dl` at `(zetaLetCtxP E n).disp id`
    for every `TableWF tbl`. -/
theorem not_cl_esub_letBody (tbl : List CRule) (hW : TableWF tbl) (E : ResolvedEnv) (n : Nat) :
    ¬ CL tbl id ((zetaLetCtxP E n).disp id) (esubZetaNode E n).dl (zetaLetNode E n).dl := by
  intro h
  have hl : (esubZetaNode E n).dl.eps id ((zetaLetCtxP E n).disp id) = .sort .zero := rfl
  have hr : (zetaLetNode E n).dl.eps id ((zetaLetCtxP E n).disp id) = .bvar 0 := rfl
  unfold CL at h
  rw [hl, hr] at h
  exact not_convMod_sort_bvar hW .zero 0 h

/-- **Instance B (top level, `c = 0`)**: `wkAtZero` at `c = 0` of `betaLetReduct`
    (which satisfies `AssumptionPrefix _ 0`) and `betaLetBody` (zero transports)
    satisfy `CL` at `ρ = [.keep, .keep]`. -/
theorem cl_wkAtZero_letE_top (tbl : List CRule) (E : ResolvedEnv) (n : Nat) :
    CL tbl id [.keep, .keep]
      (wkAtZero (A := .sort (.succ .zero)) (betaLetReduct E n))
      (betaLetBody E n) := by
  have hl :
      (wkAtZero (A := .sort (.succ .zero)) (betaLetReduct E n)).eps id [.keep, .keep] =
        .bvar 1 := rfl
  have hr : (betaLetBody E n).eps id [.keep, .keep] = .bvar 1 := rfl
  unfold CL
  rw [hl, hr]
  exact .refl _

/-- **Instance B (pushed 1 step into the let-body by `LetHead.wk`, `c = 1`)**:
    pushing `wk` at `c = 0` under `.letBinding` produces `(wkZetaNode E n).dl`
    (`TyP.wk` at `c = 1` over `(zetaLetNode E n).dl`, violating
    `AssumptionPrefix zetaLetCtx 1`), which falsifies `CL` against
    `betaLetBody`'s let-body `(esubZetaPreNode E n).dl` at `(wkZetaCtxP E n).disp id`
    for every `TableWF tbl`. -/
theorem not_cl_wk_letBody (tbl : List CRule) (hW : TableWF tbl) (E : ResolvedEnv) (n : Nat) :
    ¬ CL tbl id ((wkZetaCtxP E n).disp id) (wkZetaNode E n).dl (esubZetaPreNode E n).dl := by
  intro h
  have hl : (wkZetaNode E n).dl.eps id ((wkZetaCtxP E n).disp id) = .bvar 2 := rfl
  have hr : (esubZetaPreNode E n).dl.eps id ((wkZetaCtxP E n).disp id) = .bvar 1 := rfl
  unfold CL at h
  rw [hl, hr] at h
  exact not_convMod_bvar_ne hW (by decide) h

/-- Every `TyP.letE` has the exact same erasure as `letSub` (`TyP.lsub` at `j = 0`,
    which satisfies `AssumptionPrefix Γ 0`) at every `σ` and `ρ`. -/
theorem letSub_eps_eq_letE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value B body : Expr Nat} {u w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (letSub hb hv hA).eps σ ρ =
      (TyP.letE E n Γ A u value B body w hA hv hb hT).eps σ ρ :=
  letSub_eps hb hv hA σ ρ

end Rcic.Syn

#print axioms Rcic.Syn.CtxP.entrySort
#print axioms Rcic.Syn.DispForC
#print axioms Rcic.Syn.DispForC.levelSub
#print axioms Rcic.Syn.DispForC.toDispFor
#print axioms Rcic.Syn.dispForC_of_ctxP
#print axioms Rcic.Syn.dispForC_ctxP_id
#print axioms Rcic.Syn.SpineLetPBit
#print axioms Rcic.Syn.resolve_eq_star_iff_of_dispForC
#print axioms Rcic.Syn.pbit_bvar_spine
#print axioms Rcic.Syn.pbit_bvar_zero_assumption
#print axioms Rcic.Syn.pbit_bvar_zero_letBinding
#print axioms Rcic.Syn.combLexDM_pbit_bvar_sort
#print axioms Rcic.Syn.combLexDM_pbit_bvar_wall_removed
#print axioms Rcic.Syn.combLexDM_pbit_bvar_let_zero
#print axioms Rcic.Syn.combLexDM_rule_cv
#print axioms Rcic.Syn.combLexDM_rule_pair
#print axioms Rcic.Syn.combLexDM_let_rule
#print axioms Rcic.Syn.combLexDM_wk_strip
#print axioms Rcic.Syn.combLexDM_esub_strip
#print axioms Rcic.Syn.combLexDM_esub_repl
#print axioms Rcic.Syn.combLexDM_ewk_strip
#print axioms Rcic.Syn.combLexDM_linst_strip
#print axioms Rcic.Syn.AssumptionPrefix
#print axioms Rcic.Syn.assumptionPrefix_zero
#print axioms Rcic.Syn.not_assumptionPrefix_zetaLetCtx_one
#print axioms Rcic.Syn.not_assumptionPrefix_esubZetaPreCtx_one
#print axioms Rcic.Syn.betaLetBody
#print axioms Rcic.Syn.betaLetReduct
#print axioms Rcic.Syn.cl_instEnd_letE_top
#print axioms Rcic.Syn.not_cl_esub_letBody
#print axioms Rcic.Syn.cl_wkAtZero_letE_top
#print axioms Rcic.Syn.not_cl_wk_letBody
#print axioms Rcic.Syn.letSub_eps_eq_letE
