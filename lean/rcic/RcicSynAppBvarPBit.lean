import rcic.RcicSynSortPBit

/-!
# Syntactic sortRow, build step 4h — `TyP.bvar`, `TyP.app`, and Transport `PBit` from `Below`, plus `isPiHead_type_sort` and `readPi_sort_eq_of_isSortOrPiHead`

`research/rcic/semantic/S3_ES_ARMS.md` §57. Building on `RcicSynSortPBit` (step 4g),
this module discharges the remaining `PBit` constructor families from `Below`:

1. **§1 `TyP.bvar` `PBit` from `Below` (`pbit_bvar_proof_reg`,
   `pbit_bvar_proof_of_below`, `DispEntry`, `resolve_eq_star_iff_of_dispEntry`,
   `pbit_bvar_reg_of_dispEntry`, `pbit_bvar_of_below_dispEntry`,
   `pbit_bvar_reg_of_dispForC`, `pbit_bvar_of_below_dispForC`)**:
   - On a proof variable (`levelIsZero (σ u) = true`), `pbit_bvar_proof_reg`
     proves `PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) hA` with **zero hypotheses
     on `ρ` and zero `Below`**, and `pbit_bvar_proof_of_below` extends it to any
     `DT` from `Below Aw tbl (tyPairMeas Aw (TyP.bvar ...) DT)`.
   - On a general variable, `DispEntry σ E n Γ ρ i u₀` (an inductive entry witness
     in `Prop`) and `DispForC σ C ρ` prove `resolve ρ i = .star ↔ levelIsZero (σ u₀) = true`,
     yielding `pbit_bvar_of_below_dispEntry` and `pbit_bvar_of_below_dispForC`
     at any `DT` from `Below`.

2. **§2 `isPiHead_type_sort`, `readPi_sort_eq_of_isSortOrPiHead`, and `TyP.app`
   `PBit` from `Below` (`not_bvar_of_isSortOrPiHead`, `isSortHead_false_of_pi_expr`,
   `isPiHead_type_sort`, `readPi_sort_eq_of_isSortOrPiHead`,
   `readPi_sort_level_eq_of_isSortOrPiHead`, `atoms_castLift0`, `atoms_sortLift0`,
   `atoms_instEnd`, `dmStep_app_fun_reg_pair`, `lexDM_app_fun_reg_pair`,
   `pbit_app_fun_reg_of_below`, `dmStep_app_instEnd_pair`, `lexDM_app_instEnd_pair`,
   `sortCoh_app_instEnd_of_below`, `bitCoh_app_instEnd_of_below`,
   `pbit_app_reg_of_below_got`, `pbit_app_of_below_got`,
   `pbit_app_reg_of_below_readPi`, `pbit_app_of_below_readPi`,
   `pbit_app_reg_of_below_lam`, `pbit_app_of_below_lam`)**:
   - `readPi_sort_eq_of_isSortOrPiHead` proves that whenever `D : TyP Ei n Γ e T`
     has `D.isSortOrPiHead = true` and `readPi hext Aw src D he hAt = .yes g`,
     `T = .sort (.imax g.u g.v)` and `D.reg.1 = .succ (.imax g.u g.v)` hold with
     **zero `Below` hypotheses**.
   - In `TyP.app E n Γ f a A B w hf ha hT`, `instEnd g.hB ha g.hA` has atoms
     `g.hB.atoms Aw ++ ha.atoms Aw ++ g.hA.atoms Aw`, every one of which is
     `< (TyP.app ...).wt Aw`. Thus `(instEnd g.hB ha g.hA, hT)` is strictly
     `DMStep`-below `TyP.app`, so `Bel.bitCoh` supplies
     `levelIsZero (σ g.v) = levelIsZero (σ w)` and `LevelHom.imax_bit` chains it
     with `PBit σ ρ hf hf.reg.2` to discharge `PBit` on `TyP.app` at any `DT`.

3. **§3 Transport `PBit` against any `DT` from `Below`
   (`pbit_of_below_lex_and_reg`, `pbit_ewk_of_below`, `pbit_cctx_of_below`,
   `pbit_linst_reg_of_inner`, `pbit_linst_of_below`, `pbit_wk_of_below`,
   `pbit_esub_drop_of_below`, `pbit_esub_keep_of_below`, `pbit_esub_of_below`,
   `pbit_lsub_of_below`)**:
   - Discharges `PBit` across all 6 transport constructors (`ewk`, `cctx`,
     `linst`, `wk`, `esub`, `lsub`) against any `DT` from `Below`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `TyP.bvar` `PBit` from `Below` -/

/-- On a proof variable (`levelIsZero (σ u) = true`), `PBit` on `TyP.bvar E n Γ i A u hlook hA`
    at its own regularity typing `hA` holds with **zero hypotheses on `ρ` and zero `Below`**. -/
theorem pbit_bvar_proof_reg (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat} {u : Level}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (hu : levelIsZero (σ u) = true) :
    PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) hA := by
  unfold PBit
  rw [eps_bvar_proof hu]
  change (ETm.star = .star) ↔ levelIsZero (σ u) = true
  rw [hu]
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- On a proof variable (`levelIsZero (σ u) = true`), `PBit` on `TyP.bvar E n Γ i A u hlook hA`
    against any `DT : TyP E n Γ A (.sort s)` follows from
    `Below Aw tbl (tyPairMeas Aw (TyP.bvar E n Γ i A u hlook hA) DT)` alone. -/
theorem pbit_bvar_proof_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat} {u s : Level}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (DT : TyP E n Γ A (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = true)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.bvar E n Γ i A u hlook hA) DT)) :
    PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) DT :=
  pbit_of_below_not_isSortOrPiHead Aw tbl (TyP.bvar E n Γ i A u hlook hA) rfl DT σ ρ hρ
    (pbit_bvar_proof_reg σ ρ hlook hA hu) Bel

/-- Inductive entry witness in `Prop` recording that index `i` of `(Γ, ρ)` under `σ`
    has sort level `u₀` and (when entry `i` is a `.letBinding`) satisfies the value-bit
    `PBit σ ρ₀ hv₀ hA₀`. -/
inductive DispEntry (σ : Level → Level) (E : ResolvedEnv) (n : Nat) :
    LCtx → List Disp → Nat → Level → Prop where
  | zero_assumption {Γ : LCtx} {ρ : List Disp} {A : Expr Nat} {u₀ : Level}
      (hA : TyP E n Γ A (.sort u₀)) :
      DispEntry σ E n (.assumption A :: Γ) (binderDisp (levelIsZero (σ u₀)) :: ρ) 0 u₀
  | zero_letDrop {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u₀ : Level}
      (hA : TyP E n Γ A (.sort u₀)) (hv : TyP E n Γ v A)
      (hstar : hv.eps σ ρ = .star) (hpb : PBit σ ρ hv hA) :
      DispEntry σ E n (.letBinding A v :: Γ) (.drop :: ρ) 0 u₀
  | zero_letInline {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u₀ : Level}
      (hA : TyP E n Γ A (.sort u₀)) (hv : TyP E n Γ v A)
      (hpb : PBit σ ρ hv hA) :
      DispEntry σ E n (.letBinding A v :: Γ) (.inline (hv.eps σ ρ) :: ρ) 0 u₀
  | succ_assumption {Γ : LCtx} {ρ : List Disp} {A : Expr Nat} {u_head u₀ : Level} {i : Nat}
      (h : DispEntry σ E n Γ ρ i u₀) :
      DispEntry σ E n (.assumption A :: Γ) (binderDisp (levelIsZero (σ u_head)) :: ρ) (i + 1) u₀
  | succ_letDrop {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u₀ : Level} {i : Nat}
      (h : DispEntry σ E n Γ ρ i u₀) :
      DispEntry σ E n (.letBinding A v :: Γ) (.drop :: ρ) (i + 1) u₀
  | succ_letInline {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {ev : ETm} {u₀ : Level} {i : Nat}
      (h : DispEntry σ E n Γ ρ i u₀) :
      DispEntry σ E n (.letBinding A v :: Γ) (.inline ev :: ρ) (i + 1) u₀

/-- Any `DispEntry σ E n Γ ρ i u₀` determines `resolve ρ i = .star ↔ levelIsZero (σ u₀) = true`. -/
theorem resolve_eq_star_iff_of_dispEntry {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {i : Nat} {u₀ : Level}
    (h : DispEntry σ E n Γ ρ i u₀) :
    resolve ρ i = .star ↔ levelIsZero (σ u₀) = true := by
  induction h with
  | @zero_assumption _ _ _ u₀ _ =>
      cases hzu : levelIsZero (σ u₀) with
      | true => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | false => exact ⟨fun h0 => ETm.noConfusion h0, fun h0 => Bool.noConfusion h0⟩
  | zero_letDrop _ _ hstar hpb =>
      have hzu : levelIsZero (σ _) = true := hpb.mp hstar
      simp only [resolve, hzu]
  | zero_letInline _ _ hpb =>
      simpa only [resolve] using hpb
  | @succ_assumption _ _ _ u_head _ _ _ ih =>
      cases hzu : levelIsZero (σ u_head) with
      | true => simpa only [binderDisp, resolve] using ih
      | false =>
          simp only [binderDisp, resolve, etm_lift_eq_star_iff]
          exact ih
  | succ_letDrop _ ih =>
      simpa only [resolve] using ih
  | succ_letInline _ ih =>
      simpa only [resolve] using ih

/-- `PBit` on `TyP.bvar` at its own regularity typing `hA` from `DispEntry σ E n Γ ρ i u₀`
    and `levelIsZero (σ u₀) = levelIsZero (σ u)`. -/
theorem pbit_bvar_reg_of_dispEntry {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {i : Nat} {A : Expr Nat} {u₀ u : Level}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (hent : DispEntry σ E n Γ ρ i u₀)
    (hbit : levelIsZero (σ u₀) = levelIsZero (σ u)) :
    PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) hA := by
  cases hzu : levelIsZero (σ u) with
  | true =>
      exact pbit_bvar_proof_reg σ ρ hlook hA hzu
  | false =>
      unfold PBit
      rw [eps_bvar_rel hzu]
      have hres := resolve_eq_star_iff_of_dispEntry hent
      rw [hbit] at hres
      exact hres

/-- `PBit` on `TyP.bvar` against any `DT` from `Below Aw tbl (tyPairMeas Aw (TyP.bvar ...) DT)`,
    `DispEntry σ E n Γ ρ i u₀`, and `levelIsZero (σ u₀) = levelIsZero (σ u)`. -/
theorem pbit_bvar_of_below_dispEntry (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat} {u₀ u s : Level}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (DT : TyP E n Γ A (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hent : DispEntry σ E n Γ ρ i u₀)
    (hbit : levelIsZero (σ u₀) = levelIsZero (σ u))
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.bvar E n Γ i A u hlook hA) DT)) :
    PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) DT :=
  pbit_of_below_not_isSortOrPiHead Aw tbl (TyP.bvar E n Γ i A u hlook hA) rfl DT σ ρ hρ
    (pbit_bvar_reg_of_dispEntry hlook hA hent hbit) Bel

/-- `PBit` on `TyP.bvar` at its own regularity typing `hA` from `DispForC σ C ρ`. -/
theorem pbit_bvar_reg_of_dispForC {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {A : Expr Nat} {u : Level}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (hC : DispForC σ C ρ)
    (hsort : C.entrySort i = some u)
    (hlet : SpineLetPBit σ C ρ i) :
    PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) hA :=
  pbit_bvar_spine hC hsort hlet rfl

/-- `PBit` on `TyP.bvar` against any `DT` from `Below Aw tbl (tyPairMeas Aw (TyP.bvar ...) DT)`
    and `DispForC σ C ρ`. -/
theorem pbit_bvar_of_below_dispForC (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ}
    {i : Nat} {A : Expr Nat} {u s : Level}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (DT : TyP E n Γ A (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hC : DispForC σ C ρ)
    (hsort : C.entrySort i = some u)
    (hlet : SpineLetPBit σ C ρ i)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.bvar E n Γ i A u hlook hA) DT)) :
    PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) DT :=
  pbit_of_below_not_isSortOrPiHead Aw tbl (TyP.bvar E n Γ i A u hlook hA) rfl DT σ ρ hC.toDispFor
    (pbit_bvar_reg_of_dispForC hlook hA hC hsort hlet) Bel

/-! ## §2 `isPiHead_type_sort`, `readPi_sort_eq_of_isSortOrPiHead`, and `TyP.app` `PBit` from `Below` -/

/-- No derivation `D : TyP E n Γ e T` with `D.isSortOrPiHead = true` can have
    subject `e = .bvar j` (since its subject is `.sort l` or `.pi A B`). -/
theorem not_bvar_of_isSortOrPiHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : TyP E n Γ e T) (hsp : D.isSortOrPiHead = true)
    (j : Nat) (hs : e = .bvar j) : False := by
  cases hsh : D.isSortHead with
  | true =>
      obtain ⟨⟨l, hl⟩, _⟩ := isSortHead_expr_and_type D hsh
      rw [hs] at hl
      exact Expr.noConfusion hl
  | false =>
      obtain ⟨A₀, B₀, hpi⟩ := isPiHead_expr D hsp hsh
      rw [hs] at hpi
      exact Expr.noConfusion hpi

/-- Any derivation `D : TyP E n Γ e T` whose subject is `.pi A B` has `D.isSortHead = false`. -/
theorem isSortHead_false_of_pi_expr {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A B : Expr Nat} (D : TyP E n Γ e T) (he : e = .pi A B) :
    D.isSortHead = false := by
  cases hsh : D.isSortHead with
  | false => rfl
  | true =>
      obtain ⟨⟨l, hl⟩, _⟩ := isSortHead_expr_and_type D hsh
      rw [he] at hl
      exact Expr.noConfusion hl

/-- Every derivation `D : TyP E n Γ e T` with `D.isSortOrPiHead = true` and
    `D.isSortHead = false` has ascribed type `T = .sort (.imax u v)` and
    `D.reg.1 = .succ (.imax u v)` for some levels `u, v`. -/
theorem isPiHead_type_sort :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.isSortOrPiHead = true → D.isSortHead = false →
    ∃ u v : Level, T = .sort (.imax u v) ∧ D.reg.1 = .succ (.imax u v)
  | _, _, _, _, _, .sort .., _, hsh => nomatch hsh
  | _, _, _, _, _, .pi _ _ _ _ u _ v _ _, _, _ => ⟨u, v, rfl, rfl⟩
  | _, _, _, _, _, .bvar .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .const .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .lam .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .app .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .letE .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .lit .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .conv .., hsp, _ => nomatch hsp
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D₀ _, hsp, hsh =>
      isPiHead_type_sort D₀ hsp hsh
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D₀, hsp, hsh =>
      isPiHead_type_sort D₀ hsp hsh
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D₀, hsp, hsh => by
      obtain ⟨u₀, v₀, rfl, hreg⟩ := isPiHead_type_sort D₀ hsp hsh
      refine ⟨instLevel ls u₀, instLevel ls v₀, rfl, ?_⟩
      simp only [TyP.reg, hreg, instLevel, lvlSubst]
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D₀, hsp, hsh => by
      obtain ⟨u₀, v₀, rfl, hreg⟩ := isPiHead_type_sort D₀ hsp hsh
      exact ⟨u₀, v₀, rfl, hreg⟩
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D₀ _ _ _, hsp, hsh => by
      obtain ⟨u₀, v₀, rfl, hreg⟩ := isPiHead_type_sort D₀ hsp hsh
      exact ⟨u₀, v₀, rfl, hreg⟩
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D₀ _ _ _, hsp, hsh => by
      obtain ⟨u₀, v₀, rfl, hreg⟩ := isPiHead_type_sort D₀ hsp hsh
      exact ⟨u₀, v₀, rfl, hreg⟩

set_option maxHeartbeats 800000 in
/-- Whenever `D : TyP Ei n Γ e T` has `D.isSortOrPiHead = true` and
    `readPi hext Aw src D he hAt = .yes g`, the ascribed type `T` of `D` is
    **syntactically equal** to `.sort (.imax g.u g.v)` and `D.reg.1 = .succ (.imax g.u g.v)`
    (with **zero `Below` hypotheses**). -/
theorem readPi_sort_eq_of_isSortOrPiHead {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    (hsp : D.isSortOrPiHead = true) →
    {A B : Expr Nat} → (he : e = .pi A B) →
    (hAt : ∀ y ∈ D.atoms Aw, y < src) →
    {g : PiGot Aw src E n Γ A B} →
    readPi hext Aw src D he hAt = .yes g →
    T = .sort (.imax g.u g.v) ∧ D.reg.1 = .succ (.imax g.u g.v)
  | _, _, _, _, .sort .., _, _, _, he, _, _, _ => by cases he
  | _, _, _, _, .bvar .., hsp, _, _, _, _, _, _ => nomatch hsp
  | _, _, _, _, .const .., hsp, _, _, _, _, _, _ => nomatch hsp
  | _, _, _, _, .pi _ _ _ A₀ u B₀ v hA hB, _, _, _, he, hAt, g, hr => by
      cases he
      unfold readPi at hr
      injection hr with hg
      subst hg
      exact ⟨rfl, rfl⟩
  | _, _, _, _, .lam .., hsp, _, _, _, _, _, _ => nomatch hsp
  | _, _, _, _, .app .., hsp, _, _, _, _, _, _ => nomatch hsp
  | _, _, _, _, .letE .., hsp, _, _, _, _, _, _ => nomatch hsp
  | _, _, _, _, .lit .., hsp, _, _, _, _, _, _ => nomatch hsp
  | _, _, _, _, .conv .., hsp, _, _, _, _, _, _ => nomatch hsp
  | _, _, _, _, .wk _ _ _ _ _ d c inner, hsp, _, _, he, hAt, g, hr => by
      unfold readPi at hr
      cases hF : lift_eq_pi he with
      | mk A₀ B₀ he₀ hAe hBe =>
          rw [hF] at hr
          dsimp at hr
          cases hri : readPi hext Aw src inner he₀ (wk_atom_src Aw inner hAt) with
          | no =>
              rw [hri] at hr
              nomatch hr
          | yes g₀ =>
              rw [hri] at hr
              dsimp [pushPiWk] at hr
              injection hr with hg
              subst hg
              obtain ⟨hT₀, hreg₀⟩ :=
                readPi_sort_eq_of_isSortOrPiHead hext Aw src inner hsp he₀
                  (wk_atom_src Aw inner hAt) hri
              refine ⟨?_, hreg₀⟩
              rw [hT₀]
              rfl
  | _, _, _, _, .esub _ _ _ _ _ t repl j uE inner hget hv hvT, hsp, _, _, he, hAt, g, hr => by
      unfold readPi at hr
      cases hF : instantiate_eq_pi he with
      | under A₀ B₀ he₀ hAe hBe =>
          rw [hF] at hr
          dsimp at hr
          cases hri : readPi hext Aw src inner he₀
              (esub_inner_src Aw inner hget hv hvT hAt) with
          | no =>
              rw [hri] at hr
              nomatch hr
          | yes g₀ =>
              rw [hri] at hr
              dsimp [pushPiEsub] at hr
              injection hr with hg
              subst hg
              obtain ⟨hT₀, hreg₀⟩ :=
                readPi_sort_eq_of_isSortOrPiHead hext Aw src inner hsp he₀
                  (esub_inner_src Aw inner hget hv hvT hAt) hri
              exact ⟨congrArg (instantiate j (lift 0 j repl)) hT₀, hreg₀⟩
      | here hs _ =>
          exact (not_bvar_of_isSortOrPiHead inner hsp j hs).elim
  | _, _, _, _, .lsub .., _, _, _, _, _, _, hr => by
      unfold readPi at hr
      nomatch hr
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, hsp, _, _, he, hAt, g, hr => by
      unfold readPi at hr
      cases hF : instantiateLevels_eq_pi he with
      | mk A₀ B₀ he₀ hAe hBe =>
          rw [hF] at hr
          dsimp at hr
          cases hri : readPi hext Aw src inner he₀ (linst_atom_src Aw hls hlen inner hAt) with
          | no =>
              rw [hri] at hr
              nomatch hr
          | yes g₀ =>
              rw [hri] at hr
              dsimp [pushPiLinst] at hr
              injection hr with hg
              subst hg
              obtain ⟨hT₀, hreg₀⟩ :=
                readPi_sort_eq_of_isSortOrPiHead hext Aw src inner hsp he₀
                  (linst_atom_src Aw hls hlen inner hAt) hri
              refine ⟨?_, ?_⟩
              · rw [hT₀]
                rfl
              · simp only [TyP.reg, hreg₀, instLevel, lvlSubst]
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, hsp, _, _, he, hAt, g, hr => by
      unfold readPi at hr
      exact readPi_sort_eq_of_isSortOrPiHead (envExt_trans hext' hext) Aw src inner
        hsp he (ewk_atom_src Aw hext' inner hAt) hr
  | _, _, _, _, .cctx .., _, _, _, _, _, _, hr => by
      unfold readPi at hr
      nomatch hr

/-- Specialization of `readPi_sort_eq_of_isSortOrPiHead` to `D : TyP Ei n Γ (.pi A B) (.sort s)`:
    when `D.isSortOrPiHead = true` and `readPi hext Aw src D rfl hAt = .yes g`,
    `s = .imax g.u g.v` holds syntactically. -/
theorem readPi_sort_level_eq_of_isSortOrPiHead {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (Aw : Nat → Nat) (src : Nat) {n : Nat} {Γ : LCtx} {A B : Expr Nat} {s : Level}
    (D : TyP Ei n Γ (.pi A B) (.sort s)) (hsp : D.isSortOrPiHead = true)
    (hAt : ∀ y ∈ D.atoms Aw, y < src) {g : PiGot Aw src E n Γ A B}
    (hr : readPi hext Aw src D rfl hAt = .yes g) :
    s = .imax g.u g.v := by
  obtain ⟨hT, _⟩ := readPi_sort_eq_of_isSortOrPiHead hext Aw src D hsp rfl hAt hr
  injection hT

theorem atoms_castLift0 (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v t : Expr Nat} (D : TyP E n Γ v t) :
    (castLift0 D).atoms Aw = D.atoms Aw :=
  atoms_tyCast Aw _ _ D

theorem atoms_sortLift0 (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} (hA : TyP E n Γ A (.sort u)) :
    (sortLift0 hA).atoms Aw = hA.atoms Aw := by
  rw [sortLift0, atoms_tyCast, atoms_castLift0]

/-- The atom list of `instEnd hB hv hA` is `hB.atoms Aw ++ hv.atoms Aw ++ hA.atoms Aw`. -/
theorem atoms_instEnd (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hv : TyP E n Γ v A)
    (hA : TyP E n Γ A (.sort u)) :
    (instEnd hB hv hA).atoms Aw = hB.atoms Aw ++ hv.atoms Aw ++ hA.atoms Aw := by
  rw [instEnd, atoms_tyCast, atoms_esub, atoms_castLift0, atoms_sortLift0]

/-- `DMStep` decrease for `TyP.app`'s function regularity pair `(hf, hf.reg.2)`. -/
theorem dmStep_app_fun_reg_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w)) :
    DMStep (hf.atoms Aw ++ hf.reg.2.atoms Aw)
      ((TyP.app E n Γ f a A B w hf ha hT).atoms Aw) := by
  let D := TyP.app E n Γ f a A B w hf ha hT
  have hw1 : hf.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  have hw2 : hf.reg.2.wt Aw < D.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hf) hw1
  change DMStep (hf.atoms Aw ++ hf.reg.2.atoms Aw) [D.wt Aw]
  rw [← List.append_nil (hf.atoms Aw ++ hf.reg.2.atoms Aw)]
  refine dmStep_of_below ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw hf hw1 y hy
  · exact atoms_lt_of_wt_lt Aw hf.reg.2 hw2 y hy

theorem lexDM_app_fun_reg_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (DT : TyP E₂ n₂ Γ₂ e₂ T₂) :
    LexDM (tyPairMeas Aw hf hf.reg.2)
      (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) DT) :=
  lex_of_dm (dmStep_drop_right (dmStep_app_fun_reg_pair Aw hf ha hT) (DT.atoms Aw))

/-- `PBit σ ρ hf hf.reg.2` from `Below Aw tbl (tyPairMeas Aw (TyP.app ...) DT)`. -/
theorem pbit_app_fun_reg_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) DT)) :
    PBit σ ρ hf hf.reg.2 :=
  Bel.pb hf hf.reg.2 σ ρ hρ (lexDM_app_fun_reg_pair Aw hf ha hT DT)

/-- `DMStep` decrease for `TyP.app`'s instantiated codomain pair `(instEnd g.hB ha g.hA, hT)`
    under any `g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B`. -/
theorem dmStep_app_instEnd_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B) :
    DMStep ((instEnd g.hB ha g.hA).atoms Aw ++ hT.atoms Aw)
      ((TyP.app E n Γ f a A B w hf ha hT).atoms Aw) := by
  let D := TyP.app E n Γ f a A B w hf ha hT
  have hwa : ha.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  have hwT : hT.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  change DMStep ((instEnd g.hB ha g.hA).atoms Aw ++ hT.atoms Aw) [D.wt Aw]
  rw [← List.append_nil ((instEnd g.hB ha g.hA).atoms Aw ++ hT.atoms Aw)]
  refine dmStep_of_below ?_
  intro y hy
  rw [atoms_instEnd] at hy
  rcases List.mem_append.mp hy with hy | hyT
  · rcases List.mem_append.mp hy with hy | hyA
    · rcases List.mem_append.mp hy with hyB | hya
      · exact g.ltB y hyB
      · exact atoms_lt_of_wt_lt Aw ha hwa y hya
    · exact g.ltA y hyA
  · exact atoms_lt_of_wt_lt Aw hT hwT y hyT

theorem lexDM_app_instEnd_pair (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B)
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (DT : TyP E₂ n₂ Γ₂ e₂ T₂) :
    LexDM (tyPairMeas Aw (instEnd g.hB ha g.hA) hT)
      (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) DT) :=
  lex_of_dm (dmStep_drop_right (dmStep_app_instEnd_pair Aw hf ha hT g) (DT.atoms Aw))

/-- `SortCoh σ (instEnd g.hB ha g.hA) hT` (`eqN (σ g.v) (σ w)`) from `Below`. -/
theorem sortCoh_app_instEnd_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B)
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) DT))
    (Bel_inst : Below Aw tbl (tyPairMeas Aw (instEnd g.hB ha g.hA) hT)) :
    SortCoh σ (instEnd g.hB ha g.hA) hT :=
  sortCoh_of_below_lex Aw hW (instEnd g.hB ha g.hA) hT σ ρ hρ
    (lexDM_app_instEnd_pair Aw hf ha hT g DT) Bel Bel_inst

/-- `BitCoh σ (instEnd g.hB ha g.hA) hT` (`levelIsZero (σ g.v) = levelIsZero (σ w)`) from `Below`. -/
theorem bitCoh_app_instEnd_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B)
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) DT)) :
    BitCoh σ (instEnd g.hB ha g.hA) hT :=
  Bel.bitCoh (instEnd g.hB ha g.hA) hT σ ρ hρ (lexDM_app_instEnd_pair Aw hf ha hT g DT)

/-- `PBit` on `TyP.app` at its own regularity typing `hT`, given any
    `g : PiGot Aw ((TyP.app ...).wt Aw) E n Γ A B` with
    `levelIsZero (σ hf.reg.1) = levelIsZero (σ (.imax g.u g.v))`. -/
theorem pbit_app_reg_of_below_got (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B)
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hbit : levelIsZero (σ hf.reg.1) = levelIsZero (σ (.imax g.u g.v)))
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) DT)) :
    PBit σ ρ (TyP.app E n Γ f a A B w hf ha hT) hT := by
  have hpb_f : PBit σ ρ hf hf.reg.2 :=
    pbit_app_fun_reg_of_below Aw tbl hf ha hT DT σ ρ hρ Bel
  have hcoh_inst : levelIsZero (σ g.v) = levelIsZero (σ w) :=
    bitCoh_app_instEnd_of_below Aw tbl hf ha hT g DT σ ρ hρ Bel
  have hbit_w : levelIsZero (σ hf.reg.1) = levelIsZero (σ w) := by
    rw [hbit, hσ.imax_bit g.u g.v, hcoh_inst]
  exact pbit_app_of_fun σ ρ hf ha hT hf.reg.2 hT hpb_f hbit_w

/-- `PBit` on `TyP.app` against any `DT` from `Below`, `LevelHom σ`, and any
    `g : PiGot Aw ((TyP.app ...).wt Aw) E n Γ A B` with
    `levelIsZero (σ hf.reg.1) = levelIsZero (σ (.imax g.u g.v))`. -/
theorem pbit_app_of_below_got (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B)
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hbit : levelIsZero (σ hf.reg.1) = levelIsZero (σ (.imax g.u g.v)))
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) DT)) :
    PBit σ ρ (TyP.app E n Γ f a A B w hf ha hT) DT :=
  pbit_of_below_not_isSortOrPiHead Aw tbl (TyP.app E n Γ f a A B w hf ha hT) rfl DT σ ρ hρ
    (pbit_app_reg_of_below_got Aw tbl hf ha hT g DT hσ ρ hρ hbit Bel) Bel

/-- Helper: every atom of `hf.reg.2` is strictly below `(TyP.app E n Γ f a A B w hf ha hT).wt Aw`. -/
theorem app_fun_reg_atom_src (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w)) :
    ∀ y ∈ hf.reg.2.atoms Aw, y < (TyP.app E n Γ f a A B w hf ha hT).wt Aw := by
  let D := TyP.app E n Γ f a A B w hf ha hT
  have hw1 : hf.wt Aw < D.wt Aw := by simp only [TyP.wt]; omega
  have hw2 : hf.reg.2.wt Aw < D.wt Aw :=
    Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hf) hw1
  exact atoms_lt_of_wt_lt Aw hf.reg.2 hw2

/-- When `hf.reg.2.isSortOrPiHead = true` and `readPi` on `hf.reg.2` returns `.yes g`,
    `readPi_sort_level_eq_of_isSortOrPiHead` automatically supplies `hf.reg.1 = .imax g.u g.v`,
    discharging `PBit σ ρ (TyP.app ...) hT` from `Below` and `LevelHom σ` alone. -/
theorem pbit_app_reg_of_below_readPi (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    (hsp : hf.reg.2.isSortOrPiHead = true)
    {g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B}
    (hr : readPi (envExt_refl E) Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw)
      hf.reg.2 rfl (app_fun_reg_atom_src Aw hf ha hT) = .yes g)
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) DT)) :
    PBit σ ρ (TyP.app E n Γ f a A B w hf ha hT) hT := by
  have hs := readPi_sort_level_eq_of_isSortOrPiHead (envExt_refl E) Aw
    ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) hf.reg.2 hsp
    (app_fun_reg_atom_src Aw hf ha hT) hr
  exact pbit_app_reg_of_below_got Aw tbl hf ha hT g DT hσ ρ hρ (by rw [hs]) Bel

/-- `PBit` on `TyP.app` against any `DT` when `hf.reg.2.isSortOrPiHead = true` and
    `readPi` on `hf.reg.2` returns `.yes g`. -/
theorem pbit_app_of_below_readPi (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    (hsp : hf.reg.2.isSortOrPiHead = true)
    {g : PiGot Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw) E n Γ A B}
    (hr : readPi (envExt_refl E) Aw ((TyP.app E n Γ f a A B w hf ha hT).wt Aw)
      hf.reg.2 rfl (app_fun_reg_atom_src Aw hf ha hT) = .yes g)
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.app E n Γ f a A B w hf ha hT) DT)) :
    PBit σ ρ (TyP.app E n Γ f a A B w hf ha hT) DT :=
  pbit_of_below_not_isSortOrPiHead Aw tbl (TyP.app E n Γ f a A B w hf ha hT) rfl DT σ ρ hρ
    (pbit_app_reg_of_below_readPi Aw tbl hf ha hT DT hsp hr hσ ρ hρ Bel) Bel

/-- Specialization when `hf = TyP.lam E n Γ A u body B v hA hbody hB`:
    `hf.reg.2` is `TyP.pi E n Γ A u B v hA hB`, so `readPi` on `hf.reg.2`
    is `.yes (piOfNode ...)` by `rfl`. -/
theorem pbit_app_reg_of_below_lam (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B a : Expr Nat} {u v w s : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.app E n Γ (.lam A body) a A B w
          (TyP.lam E n Γ A u body B v hA hbody hB) ha hT) DT)) :
    PBit σ ρ
      (TyP.app E n Γ (.lam A body) a A B w
        (TyP.lam E n Γ A u body B v hA hbody hB) ha hT) hT :=
  pbit_app_reg_of_below_readPi Aw tbl
    (TyP.lam E n Γ A u body B v hA hbody hB) ha hT DT rfl rfl hσ ρ hρ Bel

/-- `PBit` on `TyP.app` of a `TyP.lam` against any `DT` from `Below` and `LevelHom σ` alone. -/
theorem pbit_app_of_below_lam (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B a : Expr Nat} {u v w s : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (DT : TyP E n Γ (instantiate0 a B) (.sort s))
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (tyPairMeas Aw
        (TyP.app E n Γ (.lam A body) a A B w
          (TyP.lam E n Γ A u body B v hA hbody hB) ha hT) DT)) :
    PBit σ ρ
      (TyP.app E n Γ (.lam A body) a A B w
        (TyP.lam E n Γ A u body B v hA hbody hB) ha hT) DT :=
  pbit_of_below_not_isSortOrPiHead Aw tbl
    (TyP.app E n Γ (.lam A body) a A B w
      (TyP.lam E n Γ A u body B v hA hbody hB) ha hT)
    rfl DT σ ρ hρ
    (pbit_app_reg_of_below_lam Aw tbl hA hbody hB ha hT DT hσ ρ hρ Bel) Bel

/-! ## §3 Transport `PBit` against any `DT` from `Below` -/

/-- General dichotomy combinator for `PBit σ ρ D DT`:
    - when `D.isSortOrPiHead = true`, `pbit_of_below_lex_isSortOrPiHead` closes
      `PBit σ ρ D DT` with **zero `PBit` recursive calls**;
    - when `D.isSortOrPiHead = false`, `pbit_of_below_not_isSortOrPiHead` closes
      `PBit σ ρ D DT` from `PBit σ ρ D D.reg.2` and `Below Aw tbl (tyPairMeas Aw D DT)`. -/
theorem pbit_of_below_lex_and_reg (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    {bound : List Nat × Nat} (hlex : LexDM (tyPairMeas Aw D DT) bound)
    (Bel_bound : Below Aw tbl bound) (Bel_pair : Below Aw tbl (tyPairMeas Aw D DT))
    (hreg : D.isSortOrPiHead = false → PBit σ ρ D D.reg.2) :
    PBit σ ρ D DT := by
  cases hsp : D.isSortOrPiHead with
  | true =>
      exact pbit_of_below_lex_isSortOrPiHead Aw hW D hsp DT σ ρ hρ hlex Bel_bound Bel_pair
  | false =>
      exact pbit_of_below_not_isSortOrPiHead Aw tbl D hsp DT σ ρ hρ (hreg hsp) Bel_pair

/-- `PBit` on `TyP.ewk` against any `DT` when `D₀.isSortHead = false`, from
    `PBit σ ρ D₀ D₀.reg.2` and `Below Aw tbl (tyPairMeas Aw (TyP.ewk ...) DT)`. -/
theorem pbit_ewk_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {s : Level}
    (hext : EnvExt E₀ E) (D₀ : TyP E₀ n Γ e A) (hsh : D₀.isSortHead = false)
    (DT : TyP E n Γ A (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hpb₀ : PBit σ ρ D₀ D₀.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.ewk E₀ E n Γ e A hext D₀) DT)) :
    PBit σ ρ (TyP.ewk E₀ E n Γ e A hext D₀) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.ewk E₀ E n Γ e A hext D₀) hsh DT σ ρ hρ
    ((pbit_ewk_reg_iff σ ρ hext D₀).mpr hpb₀) Bel

/-- `PBit` on `TyP.cctx` against any `DT` when `D₀.isSortHead = false`, from
    `PBit σ ρ' D₀ D₀.reg.2` and `Below Aw tbl (tyPairMeas Aw (TyP.cctx ...) DT)`. -/
theorem pbit_cctx_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A A' : Expr Nat} {u s : Level}
    (D₀ : TyP E n (.assumption A :: Γ) e T) (hA : CvP E n Γ A A' (.sort u))
    (hsh : D₀.isSortHead = false)
    (DT : TyP E n (.assumption A' :: Γ) T (.sort s))
    (σ : Level → Level) (ρ' : List Disp) (hρ' : DispFor σ E n (.assumption A' :: Γ) ρ')
    (hpb₀ : PBit σ ρ' D₀ D₀.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.cctx E n Γ e T A A' u D₀ hA) DT)) :
    PBit σ ρ' (TyP.cctx E n Γ e T A A' u D₀ hA) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.cctx E n Γ e T A A' u D₀ hA) hsh DT σ ρ' hρ'
    ((pbit_cctx_reg_iff σ ρ' D₀ hA).mpr hpb₀) Bel

/-- `PBit` on `TyP.linst` at its own regularity typing `D.reg.2` from
    `PBit (fun l => σ (instLevel ls l)) ρ D₀ D₀.reg.2`. -/
theorem pbit_linst_reg_of_inner (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e A : Expr Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (D₀ : TyP E a Γ e A)
    (hpb₀ : PBit (fun l => σ (instLevel ls l)) ρ D₀ D₀.reg.2) :
    PBit σ ρ (TyP.linst E a n Γ e A ls hls hlen D₀)
      (TyP.linst E a n Γ e A ls hls hlen D₀).reg.2 :=
  (pbit_linst_iff σ ρ hls hlen D₀).mpr hpb₀

/-- `PBit` on `TyP.linst` against any `DT` when `D₀.isSortHead = false`, from
    `PBit (fun l => σ (instLevel ls l)) ρ D₀ D₀.reg.2` and `Below`. -/
theorem pbit_linst_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {e A : Expr Nat} {ls : List Level} {s : Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (D₀ : TyP E a Γ e A) (hsh : D₀.isSortHead = false)
    (DT : TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls A) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n (instLvlsCtx ls Γ) ρ)
    (hpb₀ : PBit (fun l => σ (instLevel ls l)) ρ D₀ D₀.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.linst E a n Γ e A ls hls hlen D₀) DT)) :
    PBit σ ρ (TyP.linst E a n Γ e A ls hls hlen D₀) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.linst E a n Γ e A ls hls hlen D₀) hsh DT σ ρ hρ
    (pbit_linst_reg_of_inner σ ρ hls hlen D₀ hpb₀) Bel

/-- `PBit` on `TyP.wk` against any `DT` when `D₀.isSortHead = false`, from
    `PBit σ (removeAt ρ c) D₀ D₀.reg.2` and `Below`. -/
theorem pbit_wk_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat} {d : LocalDecl} {c : Nat} {s : Level}
    (D₀ : TyP E n Γ e A) (hsh : D₀.isSortHead = false)
    (DT : TyP E n (insertAt d c Γ) (lift c 1 A) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n (insertAt d c Γ) ρ)
    (hpb₀ : PBit σ (removeAt ρ c) D₀ D₀.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.wk E n Γ e A d c D₀) DT)) :
    PBit σ ρ (TyP.wk E n Γ e A d c D₀) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.wk E n Γ e A d c D₀) hsh DT σ ρ hρ
    (pbit_wk_reg_of_inner σ ρ D₀ hpb₀) Bel

/-- `PBit` on `TyP.esub` (proof hole, `levelIsZero (σ u) = true`) against any `DT`
    when `D₀.isSortHead = false`, from `PBit σ (insertDisp .drop j ρ) D₀ D₀.reg.2` and `Below`. -/
theorem pbit_esub_drop_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u s : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hsh : D₀.isSortHead = false)
    (DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n (substRemove v j Γ) ρ)
    (hu : levelIsZero (σ u) = true)
    (hpb₀ : PBit σ (insertDisp .drop j ρ) D₀ D₀.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT)) :
    PBit σ ρ (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) hsh DT σ ρ hρ
    (pbit_esub_drop_reg_of_inner σ ρ D₀ hget hv hvT hu hpb₀) Bel

/-- `PBit` on `TyP.esub` (relevant hole, `levelIsZero (σ u) = false`) against any `DT`
    when `D₀.isSortHead = false`, discharging `PBit σ ρ hv hvT` from `Bel` and using
    `PBit σ (insertDisp .keep j ρ) D₀ D₀.reg.2`. -/
theorem pbit_esub_keep_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u s : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hsh : D₀.isSortHead = false)
    (DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n (substRemove v j Γ) ρ)
    (hu : levelIsZero (σ u) = false)
    (hpb₀ : PBit σ (insertDisp .keep j ρ) D₀ D₀.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT)) :
    PBit σ ρ (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) hsh DT σ ρ hρ
    (pbit_esub_keep_reg_of_below Aw tbl D₀ hget hv hvT DT σ ρ hρ hu Bel hpb₀) Bel

/-- Unified `PBit` on `TyP.esub` against any `DT` when `D₀.isSortHead = false`:
    combines `pbit_esub_drop_of_below` and `pbit_esub_keep_of_below` via `binderDisp (levelIsZero (σ u))`. -/
theorem pbit_esub_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u s : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hsh : D₀.isSortHead = false)
    (DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n (substRemove v j Γ) ρ)
    (hpb₀ : PBit σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ) D₀ D₀.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT)) :
    PBit σ ρ (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT := by
  cases hu : levelIsZero (σ u) with
  | true =>
      rw [hu, binderDisp_drop] at hpb₀
      exact pbit_esub_drop_of_below Aw tbl D₀ hget hv hvT hsh DT σ ρ hρ hu hpb₀ Bel
  | false =>
      rw [hu, binderDisp_keep] at hpb₀
      exact pbit_esub_keep_of_below Aw tbl D₀ hget hv hvT hsh DT σ ρ hρ hu hpb₀ Bel

/-- `PBit` on `TyP.lsub` against any `DT` when `D₀.isSortHead = false`, from
    `PBit` on `D₀` at the let-clause disposition and `Below`. -/
theorem pbit_lsub_of_below (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u s : Level}
    (D₀ : TyP E n Γ e A) (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hsh : D₀.isSortHead = false)
    (DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n (substRemove v j Γ) ρ)
    (hpb₀ : PBit σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ)
      D₀ D₀.reg.2)
    (Bel : Below Aw tbl (tyPairMeas Aw (TyP.lsub E n Γ e A t v j u D₀ hget hv hvT) DT)) :
    PBit σ ρ (TyP.lsub E n Γ e A t v j u D₀ hget hv hvT) DT :=
  pbit_of_below_not_isSortHead Aw tbl (TyP.lsub E n Γ e A t v j u D₀ hget hv hvT) hsh DT σ ρ hρ
    (pbit_lsub_reg_of_inner σ ρ D₀ hget hv hvT hpb₀) Bel

end Rcic.Syn
