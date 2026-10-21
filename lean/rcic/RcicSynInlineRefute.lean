import rcic.RcicSynBelowRho

/-!
# Syntactic sortRow, build step 3ao — Q9 non-vacuity pin & inline transport refutations

`research/rcic/semantic/S3_ES_ARMS.md` §40–§41.

1. **Q9.3 Non-vacuity (`below_pinSortP`, `dispFor_pinBetaP`)**:
   - Every atom of every `TyP` and `CvP` is at least `1` (`atoms_pos_ty`, `atoms_pos_cv`).
   - Since atom lists are non-empty (`TyP.atoms_ne_nil`, `CvP.atoms_ne_nil`), no positive
     multiset steps below `[1]` (`not_dmStep_singleton_one`), and no pair or conversion has
     weight `< 1`. Hence `below_pinSortP : Below Aw tbl (tyMeas Aw pinSortP)` holds
     unconditionally for every `Aw` and `tbl`.
   - At `pinBetaP`'s context `[]`, `dispFor_pinBetaP : DispFor id emptyEnv 0 [] []` inhabits
     `DispFor`.
   - `not_pbit_const_zero`: without `LevelSub.succ_bit` (`∀ l, levelIsZero (σ (.succ l)) = false`),
     even in `Γ = []` at `ρ = []`, `σ := fun _ => .zero` refutes `PBit` on `pinSortP`
     (`sort 0 : sort 1` erases to `.sort .zero ≠ ★`, while `σ 1 = 0`).

2. **Refutation of `insertDisp` at `j = 1`, `CvP.wk` at `c = 1`, and `CvP.esub` at `j = 1`
   across a `.letBinding` at `0`**:
   - `not_es_insertDisp_keep`: in `zetaLetCtx = [.letBinding (.sort 1) (.bvar 0), .assumption (.sort 1)]`
     (`x₁ : Type, x₀ : Type := x₁`), `substRemove (.sort 0) 1 zetaLetCtx = zetaCtx`, whose
     canonical Entry disposition is `(zetaCtxP E n).disp id = [.inline (.sort .zero)]`
     (`dispFor_ctxP_id`). Yet `insertDisp .keep 1 [.inline (.sort .zero)] = [.inline (.sort .zero), .keep]`,
     under which `zetaLetNode` (`CvP.zetaLocal` at `0`, `.bvar 0 ≡ .bvar 1`) erases its left
     endpoint to `.sort .zero` (already post-substitution) and its right endpoint to `.bvar 0`
     (pre-substitution), refuting `ES` for every `TableWF tbl`.
   - `not_es_wk_inline`, `below_false_of_wk_inline`, `below_false_pinBetaP`: weakening `zetaLetNode`
     by `CvP.wk` at `c = 1` with `.assumption (.sort 1)` gives `wkZetaNode` (atoms `[7]`) in
     `wkZetaCtx = [.letBinding (.sort 1) (.bvar 1), .assumption (.sort 1), .assumption (.sort 1)]`.
     At the **canonical Entry disposition** `(wkZetaCtxP E n).disp id = [.inline (.bvar 1), .keep, .keep]`
     (which satisfies `DispFor` by `dispFor_ctxP_id`), `removeAt` does not un-lift `.inline (.bvar 1)`
     at `0 < 1`, so `TyP.eps`'s outer `.lift 0 1` lifts `.bvar 1` a second time to `.bvar 2` on
     the left while the right erases to `.bvar 1`. Since `.bvar 2` and `.bvar 1` are `EStep tbl`-normal
     and `¬ LvlEq (.bvar 2) (.bvar 1)`, `ES` is false on `wkZetaNode` for every `TableWF tbl`, and
     `Below Aw tbl (cvMeas Aw hnode)` is `False` at every rule node of weight `> 7` (in particular
     `pinBetaP`, weight `22`).
   - `not_es_esub_inline`: wrapping `CvP.zetaLocal` at `0` in `esubZetaPreCtx` in `CvP.esub` at
     `j = 1` with `v = .sort 0` gives `esubZetaNode` in `zetaLetCtx`. At the canonical Entry
     disposition `(zetaLetCtxP E n).disp id = [.inline (.bvar 0), .keep]`, `insertDisp .keep 1`
     does not lift `.inline (.bvar 0)`, so `ETm.inst 0 (.sort .zero)` substitutes `.sort .zero`
     into the left erasure while the right erases to `.bvar 0`.
   `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Q9.3 Non-vacuity at `pinSortP` and `pinBetaP`'s context -/

/-- `DispFor` is inhabited at `pinBetaP`'s context `[]` with `σ = id`. -/
def dispFor_pinBetaP : DispFor id emptyEnv 0 [] [] :=
  dispFor_ctxP_id (.nil emptyEnv 0)

mutual

theorem atoms_pos_ty (Aw : Nat → Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → ∀ y ∈ D.atoms Aw, 1 ≤ y
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => fun y hy => by
      simp only [TyP.atoms] at hy
      exact atoms_pos_ty Aw D y hy
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv hvT => fun y hy => by
      simp only [TyP.atoms] at hy
      cases List.mem_append.mp hy with
      | inl hy =>
          cases List.mem_append.mp hy with
          | inl hyD => exact atoms_pos_ty Aw D y hyD
          | inr hyv => exact atoms_pos_ty Aw hv y hyv
      | inr hyT => exact atoms_pos_ty Aw hvT y hyT
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv hvT => fun y hy => by
      simp only [TyP.atoms] at hy
      cases List.mem_append.mp hy with
      | inl hy =>
          cases List.mem_append.mp hy with
          | inl hyD => exact atoms_pos_ty Aw D y hyD
          | inr hyv => exact atoms_pos_ty Aw hv y hyv
      | inr hyT => exact atoms_pos_ty Aw hvT y hyT
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => fun y hy => by
      simp only [TyP.atoms] at hy
      exact atoms_pos_ty Aw D y hy
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => fun y hy => by
      simp only [TyP.atoms] at hy
      exact atoms_pos_ty Aw D y hy
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA => fun y hy => by
      simp only [TyP.atoms] at hy
      cases List.mem_append.mp hy with
      | inl hyD => exact atoms_pos_ty Aw D y hyD
      | inr hyA => exact atoms_pos_cv Aw hA y hyA
  | _, _, _, _, _, .sort .. | _, _, _, _, _, .bvar .. | _, _, _, _, _, .const ..
  | _, _, _, _, _, .pi .. | _, _, _, _, _, .lam .. | _, _, _, _, _, .app ..
  | _, _, _, _, _, .letE .. | _, _, _, _, _, .lit .. | _, _, _, _, _, .conv .. =>
      fun y hy => by
        simp only [TyP.atoms, List.mem_singleton] at hy
        subst hy
        exact TyP.wt_pos Aw _

theorem atoms_pos_cv (Aw : Nat → Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    (h : CvP E n Γ a b T) → ∀ y ∈ h.atoms Aw, 1 ≤ y
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h => fun y hy => by
      simp only [CvP.atoms] at hy
      exact atoms_pos_cv Aw h y hy
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ hv hvT => fun y hy => by
      simp only [CvP.atoms] at hy
      cases List.mem_append.mp hy with
      | inl hy =>
          cases List.mem_append.mp hy with
          | inl hyh => exact atoms_pos_cv Aw h y hyh
          | inr hyv => exact atoms_pos_ty Aw hv y hyv
      | inr hyT => exact atoms_pos_ty Aw hvT y hyT
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h => fun y hy => by
      simp only [CvP.atoms] at hy
      exact atoms_pos_cv Aw h y hy
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h => fun y hy => by
      simp only [CvP.atoms] at hy
      exact atoms_pos_cv Aw h y hy
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA => fun y hy => by
      simp only [CvP.atoms] at hy
      cases List.mem_append.mp hy with
      | inl hyh => exact atoms_pos_cv Aw h y hyh
      | inr hyA => exact atoms_pos_cv Aw hA y hyA
  | _, _, _, _, _, _, .refl .. | _, _, _, _, _, _, .symm .. | _, _, _, _, _, _, .trans ..
  | _, _, _, _, _, _, .beta .. | _, _, _, _, _, _, .zeta .. | _, _, _, _, _, _, .zetaLocal ..
  | _, _, _, _, _, _, .delta .. | _, _, _, _, _, _, .iota .. | _, _, _, _, _, _, .lit ..
  | _, _, _, _, _, _, .app .. | _, _, _, _, _, _, .lam .. | _, _, _, _, _, _, .pi ..
  | _, _, _, _, _, _, .letE .. | _, _, _, _, _, _, .sorts .. | _, _, _, _, _, _, .consts ..
  | _, _, _, _, _, _, .eta .. | _, _, _, _, _, _, .irr .. | _, _, _, _, _, _, .tyConv ..
  | _, _, _, _, _, _, .fsub .. =>
      fun y hy => by
        simp only [CvP.atoms, List.mem_singleton] at hy
        subst hy
        exact CvP.wt_pos Aw _

end

theorem not_dmStep_singleton_one {M : List Nat} (hne : M ≠ []) (hpos : ∀ y ∈ M, 1 ≤ y) :
    ¬ DMStep M [1] := by
  intro ⟨X, Y, Z, hXne, hMX, hYZ, hlt⟩
  have hlen : (X ++ Z).length = 1 := hMX.length_eq.symm.trans rfl
  rw [List.length_append] at hlen
  have hXpos : 0 < X.length := List.length_pos.mpr hXne
  have hZ0 : Z.length = 0 := by omega
  have hZnil : Z = [] := List.eq_nil_of_length_eq_zero hZ0
  subst hZnil
  rw [List.append_nil] at hMX hYZ
  cases M with
  | nil => exact hne rfl
  | cons m ms =>
      have hm1 : 1 ≤ m := hpos m (.head _)
      have hmY : m ∈ Y := hYZ.subset (.head _)
      obtain ⟨x, hxX, hmx⟩ := hlt m hmY
      have hx1 : x = 1 := List.mem_singleton.mp (hMX.symm.subset hxX)
      omega

private theorem not_lex_one {M : List Nat} {w : Nat}
    (hne : M ≠ []) (hpos : ∀ y ∈ M, 1 ≤ y) (hw : 1 ≤ w) :
    ¬ Prod.Lex DMStep (fun x y : Nat => x < y) (M, w) ([1], 1) := by
  intro hlt
  cases hlt with
  | left _ _ hdm => exact not_dmStep_singleton_one hne hpos hdm
  | right _ hltw => omega

private theorem atoms_pair_ne_nil (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e₁ T₁ e₂ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e₁ T₁) (D₂ : TyP E n Γ e₂ T₂) :
    D₁.atoms Aw ++ D₂.atoms Aw ≠ [] := by
  intro hnil
  exact TyP.atoms_ne_nil Aw D₁ (List.append_eq_nil.mp hnil).1

private theorem atoms_pair_pos (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e₁ T₁ e₂ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e₁ T₁) (D₂ : TyP E n Γ e₂ T₂) :
    ∀ y ∈ D₁.atoms Aw ++ D₂.atoms Aw, 1 ≤ y := by
  intro y hy
  cases List.mem_append.mp hy with
  | inl h1 => exact atoms_pos_ty Aw D₁ y h1
  | inr h2 => exact atoms_pos_ty Aw D₂ y h2

/-- Q9.3 Non-vacuity pin: `Below Aw tbl (tyMeas Aw pinSortP)` is inhabited for every `Aw` and `tbl`. -/
def below_pinSortP (Aw : Nat → Nat) (tbl : List CRule) :
    Below Aw tbl (tyMeas Aw pinSortP) where
  es h _ _ _ hlt :=
    False.elim (not_lex_one (CvP.atoms_ne_nil Aw h) (atoms_pos_cv Aw h) (CvP.wt_pos Aw h) hlt)
  cl D₁ D₂ _ _ _ hlt := by
    have hp1 := TyP.wt_pos Aw D₁
    have hp2 := TyP.wt_pos Aw D₂
    exact False.elim
      (not_lex_one (atoms_pair_ne_nil Aw D₁ D₂) (atoms_pair_pos Aw D₁ D₂) (by omega) hlt)
  eut D₁ D₂ _ _ _ hlt := by
    have hp1 := TyP.wt_pos Aw D₁
    have hp2 := TyP.wt_pos Aw D₂
    exact False.elim
      (not_lex_one (atoms_pair_ne_nil Aw D₁ D₂) (atoms_pair_pos Aw D₁ D₂) (by omega) hlt)
  cts h DX hlt := by
    have hp1 := CvP.wt_pos Aw h
    have hp2 := TyP.wt_pos Aw DX
    have hne : h.atoms Aw ++ DX.atoms Aw ≠ [] := by
      intro hnil
      exact CvP.atoms_ne_nil Aw h (List.append_eq_nil.mp hnil).1
    have hpos : ∀ y ∈ h.atoms Aw ++ DX.atoms Aw, 1 ≤ y := by
      intro y hy
      cases List.mem_append.mp hy with
      | inl h1 => exact atoms_pos_cv Aw h y h1
      | inr h2 => exact atoms_pos_ty Aw DX y h2
    exact False.elim (not_lex_one hne hpos (by omega) hlt)
  pb D DT _ _ _ hlt := by
    have hp1 := TyP.wt_pos Aw D
    have hp2 := TyP.wt_pos Aw DT
    exact False.elim
      (not_lex_one (atoms_pair_ne_nil Aw D DT) (atoms_pair_pos Aw D DT) (by omega) hlt)
  bitCoh D₁ D₂ _ _ _ hlt := by
    have hp1 := TyP.wt_pos Aw D₁
    have hp2 := TyP.wt_pos Aw D₂
    exact False.elim
      (not_lex_one (atoms_pair_ne_nil Aw D₁ D₂) (atoms_pair_pos Aw D₁ D₂) (by omega) hlt)

/-- Without `LevelSub.succ_bit`, `σ = fun _ => .zero` refutes `PBit` even in `[]` at `ρ = []`. -/
theorem not_pbit_const_zero :
    ¬ PBit (fun _ => .zero) [] pinSortP
      (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)) := by
  intro h
  have hstar : pinSortP.eps (fun _ => .zero) [] = .star := h.mpr rfl
  exact ETm.noConfusion hstar

/-! ## §2 `bvar` normal form under `EStep` and `ConvMod` -/

theorem eStep_bvar_normal (tbl : List CRule) (i : Nat) (u : ETm) :
    ¬ EStep tbl (.bvar i) u
  | .inl h => rStep_bvar_normal tbl i u h
  | .inr h => etaStep_bvar_normal i u h

theorem rstar_bvar_eq {tbl : List CRule} {i : Nat} {u : ETm}
    (h : RStar (EStep tbl) (.bvar i) u) : u = .bvar i :=
  rstar_of_normal (eStep_bvar_normal tbl i) h

theorem lvlEq_bvar_left {i : Nat} {u : ETm} (h : LvlEq (.bvar i) u) : u = .bvar i := by
  cases h
  rfl

theorem not_convMod_bvar_ne {tbl : List CRule} (hW : TableWF tbl) {i j : Nat} (hne : i ≠ j) :
    ¬ ConvMod (EStep tbl) LvlEq (.bvar i) (.bvar j) := by
  intro hc
  obtain ⟨u, v, hu, hq, hv⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) hc
  have hu' : u = .bvar i := rstar_bvar_eq hu
  have hv' : v = .bvar j := rstar_bvar_eq hv
  subst hu' hv'
  have heq : ETm.bvar j = .bvar i := lvlEq_bvar_left hq
  exact hne (ETm.bvar.inj heq).symm

theorem not_convMod_sort_bvar {tbl : List CRule} (hW : TableWF tbl) (l : Level) (i : Nat) :
    ¬ ConvMod (EStep tbl) LvlEq (.sort l) (.bvar i) := by
  intro hc
  obtain ⟨u, v, hu, hq, hv⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) hc
  have hu' : u = .sort l := rstar_of_normal (eStep_sort_normal tbl l) hu
  have hv' : v = .bvar i := rstar_bvar_eq hv
  subst hu' hv'
  nomatch hq

/-! ## §3 Refutation 1: `insertDisp .keep 1` across `.letBinding` at `0` -/

/-- `x₁ : sort 1, x₀ : sort 1 := x₁`. -/
def zetaLetCtx : LCtx :=
  [.letBinding (.sort (.succ .zero)) (.bvar 0), .assumption (.sort (.succ .zero))]

/-- `CtxP` for `zetaCtx = [.letBinding (.sort 1) (.sort 0)]`. -/
def zetaCtxP (E : ResolvedEnv) (n : Nat) : CtxP E n zetaCtx :=
  CtxP.letBinding E n [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
    (CtxP.nil E n)
    (TyP.sort E n [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.sort E n [] .zero (.succ .zero) (eqN_refl _))

/-- `CtxP` for `zetaLetCtx`. -/
def zetaLetCtxP (E : ResolvedEnv) (n : Nat) : CtxP E n zetaLetCtx :=
  CtxP.letBinding E n [.assumption (.sort (.succ .zero))]
    (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)
    (CtxP.assumption E n [] (.sort (.succ .zero)) (.succ (.succ .zero))
      (CtxP.nil E n)
      (TyP.sort E n [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (TyP.sort E n [.assumption (.sort (.succ .zero))]
      (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.bvar E n [.assumption (.sort (.succ .zero))] 0
      (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n [.assumption (.sort (.succ .zero))]
        (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))

/-- `x₀ ≡ x₁ : sort 1` in `zetaLetCtx` by `CvP.zetaLocal` at index `0`. -/
def zetaLetNode (E : ResolvedEnv) (n : Nat) :
    CvP E n zetaLetCtx (.bvar 0) (.bvar 1) (.sort (.succ .zero)) :=
  CvP.zetaLocal E n zetaLetCtx 0 (.sort (.succ .zero)) (.bvar 1) rfl rfl
    (TyP.bvar E n zetaLetCtx 1 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n zetaLetCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (TyP.bvar E n zetaLetCtx 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n zetaLetCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (TyP.bvar E n zetaLetCtx 1 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n zetaLetCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))

/-- Even when `ρ = (zetaCtxP E n).disp id` is the canonical Entry disposition of
    `substRemove (.sort 0) 1 zetaLetCtx = zetaCtx`, `insertDisp .keep 1 ρ` makes `ES`
    false on `zetaLetNode`. -/
theorem not_es_insertDisp_keep (tbl : List CRule) (hW : TableWF tbl) (E : ResolvedEnv) (n : Nat) :
    ¬ ES tbl id (insertDisp .keep 1 ((zetaCtxP E n).disp id)) (zetaLetNode E n) := by
  intro h
  have hdisp : insertDisp .keep 1 ((zetaCtxP E n).disp id) = [.inline (.sort .zero), .keep] := rfl
  have hl : (zetaLetNode E n).dl.eps id [.inline (.sort .zero), .keep] = .sort .zero := rfl
  have hr : (zetaLetNode E n).dr.eps id [.inline (.sort .zero), .keep] = .bvar 0 := rfl
  unfold ES at h
  rw [hdisp, hl, hr] at h
  exact not_convMod_sort_bvar hW .zero 0 h

/-! ## §4 Refutation 2: `CvP.wk` at `c = 1` over `zetaLetNode`, at `CtxP.disp id` -/

/-- `x₂ : sort 1, x₁ : sort 1, x₀ : sort 1 := x₂`, the weakened context `insertAt (.assumption (.sort 1)) 1 zetaLetCtx`. -/
def wkZetaCtx : LCtx :=
  [.letBinding (.sort (.succ .zero)) (.bvar 1),
   .assumption (.sort (.succ .zero)),
   .assumption (.sort (.succ .zero))]

/-- `CtxP` for `wkZetaCtx`. Its canonical Entry disposition `(wkZetaCtxP E n).disp id` is
    `[.inline (.bvar 1), .keep, .keep]`, which satisfies `DispFor` by `dispFor_ctxP_id`. -/
def wkZetaCtxP (E : ResolvedEnv) (n : Nat) : CtxP E n wkZetaCtx :=
  CtxP.letBinding E n [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]
    (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 1)
    (CtxP.assumption E n [.assumption (.sort (.succ .zero))]
      (.sort (.succ .zero)) (.succ (.succ .zero))
      (CtxP.assumption E n [] (.sort (.succ .zero)) (.succ (.succ .zero))
        (CtxP.nil E n)
        (TyP.sort E n [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
      (TyP.sort E n [.assumption (.sort (.succ .zero))]
        (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (TyP.sort E n [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]
      (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.bvar E n [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))] 1
      (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]
        (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))

/-- `CvP.wk` at cutoff `c = 1` over `zetaLetNode`. Its atom list is `[7]`. -/
def wkZetaNode (E : ResolvedEnv) (n : Nat) :
    CvP E n wkZetaCtx (lift 1 1 (.bvar 0)) (lift 1 1 (.bvar 1))
      (lift 1 1 (.sort (.succ .zero))) :=
  CvP.wk E n zetaLetCtx (.bvar 0) (.bvar 1) (.sort (.succ .zero))
    (.assumption (.sort (.succ .zero))) 1 (zetaLetNode E n)

/-- At the canonical Entry disposition `(wkZetaCtxP E n).disp id` (which satisfies `DispFor`
    by `dispFor_ctxP_id`), `wkZetaNode`'s left endpoint erases to `.bvar 2` while its right
    endpoint erases to `.bvar 1`. -/
theorem not_es_wk_inline (tbl : List CRule) (hW : TableWF tbl) (E : ResolvedEnv) (n : Nat) :
    ¬ ES tbl id ((wkZetaCtxP E n).disp id) (wkZetaNode E n) := by
  intro h
  have hl : (wkZetaNode E n).dl.eps id ((wkZetaCtxP E n).disp id) = .bvar 2 := rfl
  have hr : (wkZetaNode E n).dr.eps id ((wkZetaCtxP E n).disp id) = .bvar 1 := rfl
  unfold ES at h
  rw [hl, hr] at h
  exact not_convMod_bvar_ne hW (by decide) h

/-- Every non-transport `CvP` node of weight `> 7` has `Below Aw tbl (cvMeas Aw hnode) → False`,
    even with `Below` restricted to `DispFor`, because `wkZetaNode` has atoms `[7]` and
    `dispFor_ctxP_id (wkZetaCtxP E n)` inhabits `DispFor`. -/
theorem below_false_of_wk_inline (Aw : Nat → Nat) (tbl : List CRule) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (hw : 7 < hnode.wt Aw) (B : Below Aw tbl (cvMeas Aw hnode)) : False := by
  have hY : ∀ y ∈ (wkZetaNode E n).atoms Aw, y < hnode.wt Aw := by
    intro y hy
    have hat : (wkZetaNode E n).atoms Aw = [7] := rfl
    rw [hat] at hy
    rw [List.mem_singleton.mp hy]
    exact hw
  exact not_es_wk_inline tbl hW E n
    (B.es (wkZetaNode E n) id ((wkZetaCtxP E n).disp id)
      (dispFor_ctxP_id (wkZetaCtxP E n))
      (lex_of_dm (dmStep_under_rule Aw hnode ht hY)))

/-- `pinBetaP` has weight `> 7`, so `Below Aw tbl (cvMeas Aw pinBetaP) → False` for every `TableWF tbl`. -/
theorem below_false_pinBetaP (Aw : Nat → Nat) (tbl : List CRule) (hW : TableWF tbl)
    (B : Below Aw tbl (cvMeas Aw pinBetaP)) : False :=
  below_false_of_wk_inline Aw tbl hW pinBetaP rfl
    (by simp only [pinBetaP, pinForallP, pinSortP, CvP.wt, TyP.wt]; omega) B

/-! ## §5 Refutation 3: `CvP.esub` at `j = 1` over `zetaLocal` at `0`, at `CtxP.disp id` -/

/-- `x₂ : sort 1, x₁ : sort 1, x₀ : sort 1 := x₂`. -/
def esubZetaPreCtx : LCtx := wkZetaCtx

/-- `x₀ ≡ x₂ : sort 1` in `esubZetaPreCtx` by `CvP.zetaLocal` at `0`. -/
def esubZetaPreNode (E : ResolvedEnv) (n : Nat) :
    CvP E n esubZetaPreCtx (.bvar 0) (.bvar 2) (.sort (.succ .zero)) :=
  CvP.zetaLocal E n esubZetaPreCtx 0 (.sort (.succ .zero)) (.bvar 2) rfl rfl
    (TyP.bvar E n esubZetaPreCtx 2 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n esubZetaPreCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (TyP.bvar E n esubZetaPreCtx 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n esubZetaPreCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
    (TyP.bvar E n esubZetaPreCtx 2 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (TyP.sort E n esubZetaPreCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))

/-- `CvP.esub` at `j = 1` with `v = .sort 0` over `esubZetaPreNode`, landing in `zetaLetCtx`. -/
def esubZetaNode (E : ResolvedEnv) (n : Nat) :
    CvP E n zetaLetCtx
      (instantiate 1 (lift 0 1 (.sort .zero)) (.bvar 0))
      (instantiate 1 (lift 0 1 (.sort .zero)) (.bvar 2))
      (instantiate 1 (lift 0 1 (.sort .zero)) (.sort (.succ .zero))) :=
  CvP.esub E n esubZetaPreCtx (.bvar 0) (.bvar 2) (.sort (.succ .zero))
    (.sort (.succ .zero)) (.sort .zero) 1 (.succ (.succ .zero))
    (esubZetaPreNode E n) rfl
    (TyP.sort E n zetaLetCtx .zero (.succ .zero) (eqN_refl _))
    (TyP.sort E n zetaLetCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- At the canonical Entry disposition `(zetaLetCtxP E n).disp id` (which satisfies `DispFor`
    by `dispFor_ctxP_id`), `esubZetaNode`'s left endpoint erases to `.sort .zero` while its
    right endpoint erases to `.bvar 0`. -/
theorem not_es_esub_inline (tbl : List CRule) (hW : TableWF tbl) (E : ResolvedEnv) (n : Nat) :
    ¬ ES tbl id ((zetaLetCtxP E n).disp id) (esubZetaNode E n) := by
  intro h
  have hl : (esubZetaNode E n).dl.eps id ((zetaLetCtxP E n).disp id) = .sort .zero := rfl
  have hr : (esubZetaNode E n).dr.eps id ((zetaLetCtxP E n).disp id) = .bvar 0 := rfl
  unfold ES at h
  rw [hl, hr] at h
  exact not_convMod_sort_bvar hW .zero 0 h

end Rcic.Syn

#print axioms Rcic.Syn.dispFor_pinBetaP
#print axioms Rcic.Syn.atoms_pos_ty
#print axioms Rcic.Syn.atoms_pos_cv
#print axioms Rcic.Syn.not_dmStep_singleton_one
#print axioms Rcic.Syn.below_pinSortP
#print axioms Rcic.Syn.not_pbit_const_zero
#print axioms Rcic.Syn.eStep_bvar_normal
#print axioms Rcic.Syn.rstar_bvar_eq
#print axioms Rcic.Syn.lvlEq_bvar_left
#print axioms Rcic.Syn.not_convMod_bvar_ne
#print axioms Rcic.Syn.not_convMod_sort_bvar
#print axioms Rcic.Syn.zetaLetCtx
#print axioms Rcic.Syn.zetaCtxP
#print axioms Rcic.Syn.zetaLetCtxP
#print axioms Rcic.Syn.zetaLetNode
#print axioms Rcic.Syn.not_es_insertDisp_keep
#print axioms Rcic.Syn.wkZetaCtx
#print axioms Rcic.Syn.wkZetaCtxP
#print axioms Rcic.Syn.wkZetaNode
#print axioms Rcic.Syn.not_es_wk_inline
#print axioms Rcic.Syn.below_false_of_wk_inline
#print axioms Rcic.Syn.below_false_pinBetaP
#print axioms Rcic.Syn.esubZetaPreCtx
#print axioms Rcic.Syn.esubZetaPreNode
#print axioms Rcic.Syn.esubZetaNode
#print axioms Rcic.Syn.not_es_esub_inline
