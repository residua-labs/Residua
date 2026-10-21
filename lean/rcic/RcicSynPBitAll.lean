import rcic.RcicSynSpineComb
import rcic.RcicSynPiLamRight

/-!
# Syntactic sortRow, build step 3au — All 15 `PBit` constructors, plus `SortCoh`, `BitCoh`, and `CTS` from `EUT` + `CL`

`research/rcic/semantic/S3_ES_ARMS.md` §47. After `pbit_bvar_spine`
(`RcicSynSpineComb` §1) discharged `PBit(.bvar)` along the context spine, this
module proves `PBit` across the remaining 14 `TyP` constructors and proves the
sort-agreement claims `SortCoh`, `BitCoh`, and `CTS` from `EUT` + `CL`:

1. **Clause `★`-invertibility (`appClause_eq_star_iff`, `lamClause_eq_star_iff`,
   `lamErasure_eq_star_iff`, `etm_lift_eq_star_iff`, `etm_inst_eq_star_iff`)**:
   - `appClause ef ea = .star ↔ ef = .star`.
   - `lamClause eb = .star ↔ eb = .star` and `lamErasure bit eb = .star ↔ eb = .star`.
   - `t.lift c k = .star ↔ t = .star` and (for `r ≠ .star`) `ETm.inst j r t = .star ↔ t = .star`.

2. **Regularity bridge (`pbit_of_reg_and_bitCoh`) and all 14 remaining `PBit`
   constructors**:
   - `pbit_of_reg_and_bitCoh`: for any `D : TyP E n Γ e T` and `DT : TyP E n Γ T (.sort s)`,
     `PBit σ ρ D D.reg.2` and `BitCoh σ D.reg.2 DT` immediately give `PBit σ ρ D DT`.
   - `pbit_sort_reg`, `pbit_sort_of_bitCoh`: `.sort` erases to `.sort (σ l) ≠ .star`,
     and `LevelSub.succ_bit` gives `levelIsZero (σ (.succ k)) = false` (zero recursive
     calls for `pbit_sort_reg`).
   - `pbit_const_reg`, `pbit_const_of_bitCoh`: `.const` erases to `.star` iff
     `levelIsZero (σ u) = true` by definition (zero recursive calls for `pbit_const_reg`).
   - `pbit_pi_reg`, `pbit_pi_of_bitCoh`: `.pi` erases to `.pi ... ≠ .star`, and
     `LevelSub.succ_bit` gives `levelIsZero (σ (.succ (.imax u v))) = false` (zero
     recursive calls for `pbit_pi_reg`).
   - `pbit_lam_of_body`: `.lam` erases to `.star` iff `hbody` erases to `.star` at
     `binderDisp (levelIsZero (σ u)) :: ρ`, reducing to `PBit` on `(hbody, hB)` and
     `BitCoh σ hB DT'`.
   - `pbit_app_of_fun`: `.app` erases to `.star` iff `hf` erases to `.star`
     (`appClause_eq_star_iff`), reducing to `PBit` on `(hf, hPi)` and `BitCoh`.
   - `pbit_letE_of_body`: `.letE` erases to `hb.eps` at the let-clause disposition,
     reducing to `PBit` on `(hb, hB)` and `BitCoh`.
   - `pbit_lit_iff`, `pbit_conv_of_inner`: `.lit` and `.conv` preserve erasure (`rfl`).
   - `pbit_wk_of_inner`, `pbit_esub_drop_of_inner`, `pbit_esub_keep_of_inner`,
     `pbit_lsub_of_inner`, `pbit_linst_iff`, `pbit_ewk_iff`, `pbit_cctx_iff`:
     all 7 transport constructors of `TyP`.

3. **`SortCoh`, `BitCoh`, and `CTS` from `EUT` + `CL` (`sortCoh_of_eut_cl`,
   `bitCoh_of_eut_cl`, `cts_of_sortCoh_id`, `cts_of_eut_cl`)**:
   - Given `D₁ : TyP E n Γ T (.sort u)` and `D₂ : TyP E n Γ T (.sort v)`,
     `EUT tbl σ ρ D₁ D₂` and `CL` of `D₁.reg.2`, `D₂.reg.2` against canonical
     `TyP.sort` nodes yield `SortCoh σ D₁ D₂` (`eqN (σ u) (σ v)`) and
     `BitCoh σ D₁ D₂` (`levelIsZero (σ u) = levelIsZero (σ v)`) via
     `eqN_of_convE_sort_wf`.
   - At `σ = id`, `SortCoh id h.dl DX` yields `CTS h DX` (`eqN s w`).

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Clause `★`-invertibility -/

theorem appClause_eq_star_iff (ef ea : ETm) :
    appClause ef ea = .star ↔ ef = .star := by
  cases ef <;> cases ea <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => ETm.noConfusion h, fun h => ETm.noConfusion h⟩

theorem lamClause_eq_star_iff (eb : ETm) :
    lamClause eb = .star ↔ eb = .star := by
  cases eb <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => ETm.noConfusion h, fun h => ETm.noConfusion h⟩

theorem lamErasure_eq_star_iff (proofDom : Bool) (eb : ETm) :
    lamErasure proofDom eb = .star ↔ eb = .star := by
  cases proofDom <;> cases eb <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => ETm.noConfusion h, fun h => ETm.noConfusion h⟩

theorem etm_lift_eq_star_iff (c k : Nat) (t : ETm) :
    t.lift c k = .star ↔ t = .star :=
  ⟨lift_eq_star, fun h => by rw [h]; rfl⟩

theorem etm_inst_eq_star_iff (j : Nat) {r : ETm} (hr : r ≠ .star) (t : ETm) :
    ETm.inst j r t = .star ↔ t = .star :=
  ⟨inst_eq_star hr, fun h => by rw [h]; rfl⟩

/-! ## §2 `pbit_of_reg_and_bitCoh` and all 14 remaining `PBit` constructors -/

/-- Regularity bridge: for any `D : TyP E n Γ e T` and `DT : TyP E n Γ T (.sort s)`,
    `PBit σ ρ D D.reg.2` and `BitCoh σ D.reg.2 DT` yield `PBit σ ρ D DT`. -/
theorem pbit_of_reg_and_bitCoh {σ : Level → Level} {ρ : List Disp}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    (hreg : PBit σ ρ D D.reg.2)
    (hcoh : BitCoh σ D.reg.2 DT) :
    PBit σ ρ D DT := by
  unfold PBit at hreg ⊢
  unfold BitCoh at hcoh
  rw [← hcoh]
  exact hreg

/-- `PBit` on `TyP.sort` at its own regularity typing `D.reg.2` holds unconditionally
    from `LevelSub σ` (zero recursive calls). -/
theorem pbit_sort_reg {σ : Level → Level} (hσ : LevelSub σ) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k : Level} (h : eqN k (.succ l)) :
    PBit σ ρ (TyP.sort E n Γ l k h) (TyP.sort E n Γ l k h).reg.2 := by
  unfold PBit
  rw [eps_sort]
  change (ETm.sort (σ l) = .star) ↔ levelIsZero (σ (.succ k)) = true
  rw [hσ.succ_bit k]
  exact ⟨fun h0 => ETm.noConfusion h0, fun h0 => Bool.noConfusion h0⟩

/-- `PBit` on `TyP.sort` against any `DT : TyP E n Γ (.sort k) (.sort s)` from
    `BitCoh σ (TyP.sort E n Γ l k h).reg.2 DT`. -/
theorem pbit_sort_of_bitCoh {σ : Level → Level} (hσ : LevelSub σ) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k s : Level} (h : eqN k (.succ l))
    (DT : TyP E n Γ (.sort k) (.sort s))
    (hcoh : BitCoh σ (TyP.sort E n Γ l k h).reg.2 DT) :
    PBit σ ρ (TyP.sort E n Γ l k h) DT :=
  pbit_of_reg_and_bitCoh (TyP.sort E n Γ l k h) DT (pbit_sort_reg hσ ρ h) hcoh

/-- `PBit` on `TyP.const` at its own regularity typing `hT` holds unconditionally
    (zero recursive calls). -/
theorem pbit_const_reg (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀ : List Level}
    {m : CheckedMember} {u : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
    (hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)) :
    PBit σ ρ (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) hT := by
  unfold PBit
  cases hzu : levelIsZero (σ u)
  · rw [eps_const_rel hzu]
    exact ⟨fun h0 => ETm.noConfusion h0, fun h0 => Bool.noConfusion h0⟩
  · rw [eps_const_proof hzu]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- `PBit` on `TyP.const` against any `DT` from `BitCoh σ hT DT`. -/
theorem pbit_const_of_bitCoh (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀ : List Level}
    {m : CheckedMember} {u s : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
    (hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u))
    (DT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort s))
    (hcoh : BitCoh σ hT DT) :
    PBit σ ρ (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) DT :=
  pbit_of_reg_and_bitCoh
    (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) DT
    (pbit_const_reg σ ρ hres hlen hwf hls hT) hcoh

/-- `PBit` on `TyP.pi` at its own regularity typing `D.reg.2` holds unconditionally
    from `LevelSub σ` (zero recursive calls). -/
theorem pbit_pi_reg {σ : Level → Level} (hσ : LevelSub σ) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hA : TyP E n Γ A (.sort u)) (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
    PBit σ ρ (TyP.pi E n Γ A u B v hA hB) (TyP.pi E n Γ A u B v hA hB).reg.2 := by
  unfold PBit
  rw [eps_pi_clause]
  change (ETm.pi (hA.eps σ ρ) (piSlot (levelIsZero (σ u)) (hB.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))) = .star) ↔
    levelIsZero (σ (.succ (.imax u v))) = true
  rw [hσ.succ_bit (.imax u v)]
  exact ⟨fun h0 => ETm.noConfusion h0, fun h0 => Bool.noConfusion h0⟩

/-- `PBit` on `TyP.pi` against any `DT` from `BitCoh σ (TyP.pi ...).reg.2 DT`. -/
theorem pbit_pi_of_bitCoh {σ : Level → Level} (hσ : LevelSub σ) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u v s : Level}
    (hA : TyP E n Γ A (.sort u)) (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (DT : TyP E n Γ (.sort (.imax u v)) (.sort s))
    (hcoh : BitCoh σ (TyP.pi E n Γ A u B v hA hB).reg.2 DT) :
    PBit σ ρ (TyP.pi E n Γ A u B v hA hB) DT :=
  pbit_of_reg_and_bitCoh (TyP.pi E n Γ A u B v hA hB) DT (pbit_pi_reg hσ ρ hA hB) hcoh

/-- `PBit` on `TyP.lam`: since `lamErasure bit eb = .star ↔ eb = .star`, `PBit` on
    `TyP.lam E n Γ A u body B v hA hbody hB` and `DT` follows from `PBit` on
    `(hbody, hB)` at `binderDisp (levelIsZero (σ u)) :: ρ` and `levelIsZero (σ v) = levelIsZero (σ s)`. -/
theorem pbit_lam_of_body (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B : Expr Nat} {u v s : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (DT : TyP E n Γ (.pi A B) (.sort s))
    (hpb : PBit σ (binderDisp (levelIsZero (σ u)) :: ρ) hbody hB)
    (hbit : levelIsZero (σ v) = levelIsZero (σ s)) :
    PBit σ ρ (TyP.lam E n Γ A u body B v hA hbody hB) DT := by
  unfold PBit at hpb ⊢
  rw [eps_lam_clause, lamErasure_eq_star_iff, ← hbit]
  exact hpb

/-- `PBit` on `TyP.app`: since `appClause ef ea = .star ↔ ef = .star`, `PBit` on
    `TyP.app E n Γ f a A B w hf ha hT` and `DT` follows from `PBit` on `hf`
    against a sort typing `hPi : TyP E n Γ (.pi A B) (.sort uPi)` with
    `levelIsZero (σ uPi) = levelIsZero (σ s)`. -/
theorem pbit_app_of_fun (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w uPi s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (hPi : TyP E n Γ (.pi A B) (.sort uPi))
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    (hpb : PBit σ ρ hf hPi)
    (hbit : levelIsZero (σ uPi) = levelIsZero (σ s)) :
    PBit σ ρ (TyP.app E n Γ f a A B w hf ha hT) DT := by
  unfold PBit at hpb ⊢
  rw [eps_app_appClause, appClause_eq_star_iff, ← hbit]
  exact hpb

/-- `PBit` on `TyP.letE`: follows from `PBit` on `hb` at the let-clause disposition
    and `levelIsZero (σ uB) = levelIsZero (σ s)`. -/
theorem pbit_letE_of_body (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A value B body : Expr Nat} {u w uB s : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (hB : TyP E n (.letBinding A value :: Γ) B (.sort uB))
    (DT : TyP E n Γ (instantiate0 value B) (.sort s))
    (hpb : PBit σ ((match hv.eps σ ρ with | .star => .drop | ev => .inline ev) :: ρ) hb hB)
    (hbit : levelIsZero (σ uB) = levelIsZero (σ s)) :
    PBit σ ρ (TyP.letE E n Γ A u value B body w hA hv hb hT) DT := by
  unfold PBit at hpb ⊢
  rw [eps_let_clause, ← hbit]
  revert hpb
  cases hv.eps σ ρ <;> intro hpb <;> exact hpb

/-- `PBit` on `TyP.lit` is identical to `PBit` on `hexp`. -/
theorem pbit_lit_iff (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat} {s : Level}
    (hexp : TyP E n Γ (natExpand t) T)
    (DT : TyP E n Γ T (.sort s)) :
    PBit σ ρ (TyP.lit E n Γ t T hexp) DT ↔ PBit σ ρ hexp DT :=
  Iff.rfl

/-- `PBit` on `TyP.conv` follows from `PBit σ ρ h hc.dl` and `BitCoh σ hc.dr DT`. -/
theorem pbit_conv_of_inner (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u s : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (DT : TyP E n Γ B (.sort s))
    (hpb : PBit σ ρ h hc.dl)
    (hcoh : BitCoh σ hc.dr DT) :
    PBit σ ρ (TyP.conv E n Γ e A B u h hc) DT := by
  unfold PBit at hpb ⊢
  unfold BitCoh at hcoh
  rw [eps_conv, ← hcoh]
  exact hpb

/-- `PBit` on `TyP.wk` follows from `PBit σ (removeAt ρ c) D₀ DT₀` and `levelIsZero (σ s₀) = levelIsZero (σ s)`
    across every disposition at `c` (`keep`, `drop`, `inline`, `none`). -/
theorem pbit_wk_of_inner (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl} {c : Nat}
    {s₀ s : Level}
    (D₀ : TyP E n Γ e A) (DT₀ : TyP E n Γ A (.sort s₀))
    (DT : TyP E n (insertAt d c Γ) (lift c 1 A) (.sort s))
    (hpb : PBit σ (removeAt ρ c) D₀ DT₀)
    (hbit : levelIsZero (σ s₀) = levelIsZero (σ s)) :
    PBit σ ρ (TyP.wk E n Γ e A d c D₀) DT := by
  unfold PBit at hpb ⊢
  rw [← hbit]
  cases hk : ρ[c]? with
  | none =>
      rw [eps_wk_not_keep (.inl hk)]
      exact hpb
  | some disp =>
      cases disp with
      | keep =>
          rw [eps_wk_keep hk, etm_lift_eq_star_iff]
          exact hpb
      | drop =>
          rw [eps_wk_not_keep (.inr (.inl hk))]
          exact hpb
      | inline ev =>
          rw [eps_wk_not_keep (.inr (.inr ⟨ev, hk⟩))]
          exact hpb

/-- `PBit` on `TyP.esub` on the proof-hole path (`levelIsZero (σ u) = true`). -/
theorem pbit_esub_drop_of_inner (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
    {u s₀ s : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (DT₀ : TyP E n Γ A (.sort s₀))
    (DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s))
    (hu : levelIsZero (σ u) = true)
    (hpb : PBit σ (insertDisp .drop j ρ) D₀ DT₀)
    (hbit : levelIsZero (σ s₀) = levelIsZero (σ s)) :
    PBit σ ρ (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT := by
  unfold PBit at hpb ⊢
  rw [eps_esub_drop (hu := hu), ← hbit]
  exact hpb

/-- `PBit` on `TyP.esub` on the relevant-hole path (`levelIsZero (σ u) = false`):
    `PBit σ ρ hv hvT` gives `hv.eps σ ρ ≠ .star`, so `etm_inst_eq_star_iff`
    reduces `(TyP.esub ...).eps σ ρ = .star` to `D₀.eps σ (insertDisp .keep j ρ) = .star`. -/
theorem pbit_esub_keep_of_inner (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
    {u s₀ s : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (DT₀ : TyP E n Γ A (.sort s₀))
    (DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s))
    (hu : levelIsZero (σ u) = false)
    (hpb_v : PBit σ ρ hv hvT)
    (hpb : PBit σ (insertDisp .keep j ρ) D₀ DT₀)
    (hbit : levelIsZero (σ s₀) = levelIsZero (σ s)) :
    PBit σ ρ (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT := by
  have hv_ne : hv.eps σ ρ ≠ .star := by
    intro hstar
    have htrue := hpb_v.mp hstar
    rw [hu] at htrue
    exact Bool.noConfusion htrue
  unfold PBit at hpb ⊢
  rw [eps_esub_keep (hu := hu), etm_inst_eq_star_iff _ hv_ne, ← hbit]
  exact hpb

/-- `PBit` on `TyP.lsub`: reduces to `PBit` on `D₀` at `insertDisp` of the let-clause disposition. -/
theorem pbit_lsub_of_inner (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
    {u s₀ s : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (DT₀ : TyP E n Γ A (.sort s₀))
    (DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s))
    (hpb : PBit σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ)
        D₀ DT₀)
    (hbit : levelIsZero (σ s₀) = levelIsZero (σ s)) :
    PBit σ ρ (TyP.lsub E n Γ e A t v j u D₀ hget hv hvT) DT := by
  unfold PBit at hpb ⊢
  rw [← hbit]
  simp only [TyP.eps]
  revert hpb
  cases hv.eps σ ρ <;> intro hpb <;> exact hpb

/-- `PBit` on `TyP.linst` at its own regularity typing is identical to `PBit` on `D₀` at `σ ∘ instLevel ls`. -/
theorem pbit_linst_iff (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e A : Expr Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (D₀ : TyP E a Γ e A) :
    PBit σ ρ (TyP.linst E a n Γ e A ls hls hlen D₀)
      (TyP.linst E a n Γ e A ls hls hlen D₀).reg.2 ↔
      PBit (fun l => σ (instLevel ls l)) ρ D₀ D₀.reg.2 :=
  Iff.rfl

/-- `PBit` on `TyP.ewk` is identical to `PBit` on `D₀`. -/
theorem pbit_ewk_iff (σ : Level → Level) (ρ : List Disp)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {s : Level}
    (hext : EnvExt E₀ E) (D₀ : TyP E₀ n Γ e A)
    (DT₀ : TyP E₀ n Γ A (.sort s)) (DT : TyP E n Γ A (.sort s)) :
    PBit σ ρ (TyP.ewk E₀ E n Γ e A hext D₀) DT ↔ PBit σ ρ D₀ DT₀ :=
  Iff.rfl

/-- `PBit` on `TyP.cctx` is identical to `PBit` on `D₀`. -/
theorem pbit_cctx_iff (σ : Level → Level) (ρ' : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A A' : Expr Nat} {u s : Level}
    (D₀ : TyP E n (.assumption A :: Γ) e T) (hA : CvP E n Γ A A' (.sort u))
    (DT₀ : TyP E n (.assumption A :: Γ) T (.sort s))
    (DT : TyP E n (.assumption A' :: Γ) T (.sort s)) :
    PBit σ ρ' (TyP.cctx E n Γ e T A A' u D₀ hA) DT ↔ PBit σ ρ' D₀ DT₀ :=
  Iff.rfl

/-! ## §3 `SortCoh`, `BitCoh`, and `CTS` from `EUT` + `CL` -/

/-- For any two sort typings `D₁ : TyP E n Γ T (.sort u)` and `D₂ : TyP E n Γ T (.sort v)`
    under a `TableWF` table, `EUT tbl σ ρ D₁ D₂` and `CL` of `D₁.reg.2`, `D₂.reg.2`
    against canonical `TyP.sort` nodes prove `SortCoh σ D₁ D₂` (`eqN (σ u) (σ v)`). -/
theorem sortCoh_of_eut_cl {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (heut : EUT tbl σ ρ D₁ D₂)
    (hL : CL tbl σ ρ D₁.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
    (hR : CL tbl σ ρ D₂.reg.2 (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    SortCoh σ D₁ D₂ := by
  have hL' : ConvMod (EStep tbl) LvlEq (D₁.reg.2.eps σ ρ) (.sort (σ u)) := by
    simpa only [CL, eps_sort] using hL
  have hR' : ConvMod (EStep tbl) LvlEq (D₂.reg.2.eps σ ρ) (.sort (σ v)) := by
    simpa only [CL, eps_sort] using hR
  exact eqN_of_convE_sort_wf hW
    ((ConvMod.symm' LvlEq.symm' hL').trans (heut.trans hR'))

/-- `BitCoh` corollary of `sortCoh_of_eut_cl`. -/
theorem bitCoh_of_eut_cl {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (heut : EUT tbl σ ρ D₁ D₂)
    (hL : CL tbl σ ρ D₁.reg.2 (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
    (hR : CL tbl σ ρ D₂.reg.2 (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    BitCoh σ D₁ D₂ :=
  bitCoh_of_sortCoh (sortCoh_of_eut_cl hW D₁ D₂ σ ρ heut hL hR)

/-- `CTS h DX` (`eqN s w`) follows directly from `SortCoh id h.dl DX` (`eqN w s`). -/
theorem cts_of_sortCoh_id {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (hcoh : SortCoh id h.dl DX) :
    CTS h DX :=
  eqN_symm hcoh

/-- `CTS h DX` from `EUT tbl id ρ h.dl DX` and `CL` of `h.dl.reg.2`, `DX.reg.2`
    against canonical `TyP.sort` nodes. -/
theorem cts_of_eut_cl {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (ρ : List Disp)
    (heut : EUT tbl id ρ h.dl DX)
    (hL : CL tbl id ρ h.dl.reg.2 (TyP.sort E n Γ w (.succ w) (eqN_refl _)))
    (hR : CL tbl id ρ DX.reg.2 (TyP.sort E n Γ s (.succ s) (eqN_refl _))) :
    CTS h DX :=
  cts_of_sortCoh_id h DX (sortCoh_of_eut_cl hW h.dl DX id ρ heut hL hR)

end Rcic.Syn
