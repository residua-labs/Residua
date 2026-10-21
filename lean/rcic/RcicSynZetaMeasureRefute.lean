import rcic.RcicSynInlineRefute
import rcic.RcicSynStarLift

/-!
# Syntactic sortRow, build step 3ap — R-inline-B `zetaLocal` refutations & pair/combined measure walls

`research/rcic/semantic/S3_ES_ARMS.md` §42.

This module seals two sets of machine-checked obstructions requested by the
coordinator's ruling on PR #6938 (`issuecomment-6160348810`):

1. **Refutation of R-inline-B (`Disp` without `.inline`) on `CvP.zetaLocal`**:
   - On `zetaNode : CvP E n zetaCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero))`
     (`CvP.zetaLocal` at index `0` in `zetaCtx = [.letBinding (.sort 1) (.sort 0)]`),
     the canonical `.inline` disposition `(zetaCtxP E n).disp id = [.inline (.sort .zero)]`
     satisfies `ES` (`es_zetaNode_inline`).
   - Under R-inline-B (`Disp` restricted to `.keep` and `.drop`, i.e.
     `∀ d ∈ ρ, d = .keep ∨ d = .drop`), `resolve ρ i` is always `.star` or `.bvar k`
     (`resolve_keep_drop`), so `(zetaNode E n).dl.eps id ρ` is `.star` or `.bvar k`
     while `(zetaNode E n).dr.eps id ρ = .sort .zero`. Since `.star`, `.bvar k`,
     and `.sort .zero` are `EStep tbl`-normal and not `LvlEq`,
     `not_es_zetaLocal_keep_drop` proves `¬ ES tbl id ρ (zetaNode E n)` for every
     `TableWF tbl` and every `.keep`/`.drop`-only `ρ`.
   - **Representation-independent impossibility (`not_es_zetaLocal_same_disp`)**:
     Even if `ETm` is extended with `letE` and `EStep.zeta` (`letE v b → inst 0 v b`),
     `CvP.zetaLocal` converts `.bvar 0 ≡ v` in an open context where neither endpoint
     is a `letE`. In `zetaCtx = [.letBinding (.sort 1) (.sort 0)]` (`zetaNode`) and
     `zetaOneCtx = [.letBinding (.sort 2) (.sort 1)]` (`zetaOneNode`), both
     let-bindings have relevant (non-`Prop`) types and non-`★` values. For **any**
     disposition `d₀ : Disp` shared by both contexts (such as `.keep` under R-inline-B),
     `ES tbl id [d₀] (zetaNode E n)` and `ES tbl id [d₀] (zetaOneNode E n)` cannot
     both hold for a `TableWF tbl`, because both left endpoints erase to the same term
     `resolve [d₀] 0` while the right endpoints erase to `.sort .zero` and
     `.sort (.succ .zero)`, which would force `eqN (.succ .zero) .zero` by symmetry,
     transitivity, and `eqN_of_convE_sort_wf`.

2. **Exact measure walls for `(ctxMeas, nodeMeas)` (`PairLexDM`) and `combMeas` (`LexDM`)**:
   - **Wall A (`not_pairLexDM_binder_extend`, `not_pairLexDM_let_extend`)**:
     Under the lexicographic pair `(ctxMeas, nodeMeas)` (`PairLexDM`), extending a
     context spine `C : CtxP E n Γ` by `.assumption` or `.letBinding` (as in `CvP.pi`,
     `CvP.lam`, `CvP.letE`, `CvP.beta`, `CvP.zeta`, `CvP.fsub`) strictly **increases**
     `ctxMeas` (`lexDM_ctxMeas_assumption`, `lexDM_ctxMeas_letBinding`), so the pair
     measure never decreases.
   - **Wall B (`not_pairLexDM_cctx` vs `combLexDM_cctx_inner`, `combLexDM_cctx_bitCoh`)**:
     On `cctx`, replacing the outer context spine `C_out = .assumption C₀ hA'` with
     `C_in = .assumption C₀ hA.dl` fails `PairLexDM` whenever `hA.dl` is heavier than
     `hA'` (`not_pairLexDM_cctx`). By contrast, under the **combined** multiset
     `combMeas Aw C m = (C.atoms Aw ++ m.1, C.wt Aw + m.2)`, **both** recursive calls
     of `cctx` — the inner call at `(C_in, h)` and the `BitCoh` call at `(C₀, (hA', hA.dr))`
     in the tail context `C₀` — strictly decrease in `LexDM` (`combLexDM_cctx_inner`,
     `combLexDM_cctx_bitCoh`), as do all binder-extending arms (`combLexDM_binder_rule`).
   - **Wall C (`not_pairLexDM_pbit_bvar`, `not_combLexDM_pbit_bvar`)**:
     At `PBit` on `D = TyP.bvar E n Γ 0 A u hty hA` and `DT`, relating the context
     spine's entry typing `hA₀` to `D`'s typing `hA` via `BitCoh σ (wkAtZero hA₀) hA`
     in context `C` fails **both** `PairLexDM` and `combMeas` when `hA₀` in `C` is
     heavier than `D` (`pbitWallHeavySort` of weight `6` vs `pbitVar` of weight `2`),
     because `hA₀` remains in `C` while being duplicated into the `BitCoh` node pair.
   `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Refutation of R-inline-B (`Disp` without `.inline`) on `CvP.zetaLocal` -/

/-- At the canonical `.inline` disposition `(zetaCtxP E n).disp id = [.inline (.sort .zero)]`,
    `zetaNode` (`CvP.zetaLocal` at `0` in `zetaCtx`) satisfies `ES`. -/
theorem es_zetaNode_inline (tbl : List CRule) (E : ResolvedEnv) (n : Nat) :
    ES tbl id ((zetaCtxP E n).disp id) (zetaNode E n) := by
  have hl : (zetaNode E n).dl.eps id ((zetaCtxP E n).disp id) = .sort .zero := rfl
  have hr : (zetaNode E n).dr.eps id ((zetaCtxP E n).disp id) = .sort .zero := rfl
  unfold ES
  rw [hl, hr]
  exact .refl _

/-- If `ρ` contains only `.keep` and `.drop` (R-inline-B), then `resolve ρ i` is
    always `.star` or `.bvar k` for some `k`. -/
theorem resolve_keep_drop :
    ∀ (ρ : List Disp), (∀ d ∈ ρ, d = .keep ∨ d = .drop) → ∀ (i : Nat),
      resolve ρ i = .star ∨ ∃ k : Nat, resolve ρ i = .bvar k
  | [], _, i => Or.inr ⟨i, rfl⟩
  | d :: rest, hρ, 0 => by
      cases hρ d (.head _) with
      | inl hk =>
          subst hk
          exact Or.inr ⟨0, rfl⟩
      | inr hd =>
          subst hd
          exact Or.inl rfl
  | d :: rest, hρ, i + 1 => by
      have hrest : ∀ d' ∈ rest, d' = .keep ∨ d' = .drop :=
        fun d' hm => hρ d' (.tail _ hm)
      cases hρ d (.head _) with
      | inl hk =>
          subst hk
          cases resolve_keep_drop rest hrest i with
          | inl hstar =>
              left
              simp only [resolve, hstar, ETm.lift]
          | inr hbvar =>
              rcases hbvar with ⟨k, hk⟩
              right
              refine ⟨k + 1, ?_⟩
              simp only [resolve, hk, ETm.lift, Nat.zero_le, ↓reduceIte]
      | inr hd =>
          subst hd
          simpa only [resolve] using resolve_keep_drop rest hrest i

theorem not_convMod_star_sort {tbl : List CRule} (hW : TableWF tbl) (l : Level) :
    ¬ ConvMod (EStep tbl) LvlEq .star (.sort l) := by
  intro hc
  obtain ⟨u, v, hu, hq, hv⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) hc
  have hu' : u = .star := rstar_of_normal (eStep_star_normal tbl) hu
  have hv' : v = .sort l := rstar_of_normal (eStep_sort_normal tbl l) hv
  subst hu' hv'
  nomatch hq

theorem not_convMod_bvar_sort {tbl : List CRule} (hW : TableWF tbl) (k : Nat) (l : Level) :
    ¬ ConvMod (EStep tbl) LvlEq (.bvar k) (.sort l) := by
  intro hc
  exact not_convMod_sort_bvar hW l k (ConvMod.symm' LvlEq.symm' hc)

/-- Under R-inline-B (`∀ d ∈ ρ, d = .keep ∨ d = .drop`), `ES` is false on `zetaNode`
    (`CvP.zetaLocal` at `0` in `zetaCtx = [.letBinding (.sort 1) (.sort 0)]`) for
    every `TableWF tbl` and every such `ρ`. -/
theorem not_es_zetaLocal_keep_drop (tbl : List CRule) (hW : TableWF tbl)
    (E : ResolvedEnv) (n : Nat) (ρ : List Disp)
    (hρ : ∀ d ∈ ρ, d = .keep ∨ d = .drop) :
    ¬ ES tbl id ρ (zetaNode E n) := by
  intro hes
  unfold ES at hes
  have hdl : (zetaNode E n).dl.eps id ρ = resolve ρ 0 := by
    have hdl' : (zetaNode E n).dl = zetaVar E n := rfl
    rw [hdl']
    unfold zetaVar
    rw [eps_bvar_rel (σ := id) (ρ := ρ)
      (show levelIsZero (id (Level.succ (.succ .zero))) = false from rfl)]
  have hdr : (zetaNode E n).dr.eps id ρ = .sort .zero := rfl
  rw [hdl, hdr] at hes
  cases resolve_keep_drop ρ hρ 0 with
  | inl hstar =>
      rw [hstar] at hes
      exact not_convMod_star_sort hW .zero hes
  | inr hbvar =>
      rcases hbvar with ⟨k, hk⟩
      rw [hk] at hes
      exact not_convMod_bvar_sort hW k .zero hes

/-- `x₀ : sort 2 := sort 1` at position `0`. -/
def zetaOneCtx : LCtx :=
  [.letBinding (.sort (.succ (.succ .zero))) (.sort (.succ .zero))]

/-- `x₀ ≡ sort 1 : sort 2` in `zetaOneCtx` by `CvP.zetaLocal` at index `0`. -/
def zetaOneNode (E : ResolvedEnv) (n : Nat) :
    CvP E n zetaOneCtx (.bvar 0) (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  CvP.zetaLocal E n zetaOneCtx 0
    (.sort (.succ (.succ .zero))) (.sort (.succ .zero)) rfl rfl
    (TyP.sort E n zetaOneCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.bvar E n zetaOneCtx 0
      (.sort (.succ (.succ .zero))) (.succ (.succ (.succ .zero))) rfl
      (TyP.sort E n zetaOneCtx (.succ (.succ .zero)) (.succ (.succ (.succ .zero))) (eqN_refl _)))
    (TyP.sort E n zetaOneCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- Representation-independent impossibility of a value-independent let disposition:
    for **any** `d₀ : Disp` shared between `zetaCtx` (`x₀ : sort 1 := sort 0`) and
    `zetaOneCtx` (`x₀ : sort 2 := sort 1`), `ES` cannot hold on both `zetaNode` and
    `zetaOneNode` at `[d₀]` for any `TableWF tbl`. -/
theorem not_es_zetaLocal_same_disp (tbl : List CRule) (hW : TableWF tbl)
    (E : ResolvedEnv) (n : Nat) (d₀ : Disp)
    (h0 : ES tbl id [d₀] (zetaNode E n)) :
    ¬ ES tbl id [d₀] (zetaOneNode E n) := by
  intro h1
  unfold ES at h0 h1
  have hl0 : (zetaNode E n).dl.eps id [d₀] = resolve [d₀] 0 := by
    have hdl0 : (zetaNode E n).dl = zetaVar E n := rfl
    rw [hdl0]
    unfold zetaVar
    rw [eps_bvar_rel (σ := id) (ρ := [d₀])
      (show levelIsZero (id (Level.succ (.succ .zero))) = false from rfl)]
  have hr0 : (zetaNode E n).dr.eps id [d₀] = .sort .zero := rfl
  have hl1 : (zetaOneNode E n).dl.eps id [d₀] = resolve [d₀] 0 := by
    change (TyP.bvar E n zetaOneCtx 0
      (.sort (.succ (.succ .zero))) (.succ (.succ (.succ .zero))) rfl
      (TyP.sort E n zetaOneCtx (.succ (.succ .zero)) (.succ (.succ (.succ .zero))) (eqN_refl _))).eps
      id [d₀] = resolve [d₀] 0
    rw [eps_bvar_rel (σ := id) (ρ := [d₀])
      (show levelIsZero (id (Level.succ (.succ (.succ .zero)))) = false from rfl)]
  have hr1 : (zetaOneNode E n).dr.eps id [d₀] = .sort (.succ .zero) := rfl
  rw [hl0, hr0] at h0
  rw [hl1, hr1] at h1
  have hconv : ConvMod (EStep tbl) LvlEq (.sort (.succ .zero)) (.sort .zero) :=
    (ConvMod.symm' LvlEq.symm' h1).trans h0
  exact not_eqN_one_zero (eqN_of_convE_sort_wf hW hconv)

/-! ## §2 Context-spine measures (`ctxMeas`, `PairLexDM`, `combMeas`) and the three measure walls -/

/-- Atom multiset of a context derivation spine `CtxP`. -/
def CtxP.atoms (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    CtxP E n Γ → List Nat
  | _, _, _, .nil _ _ => []
  | _, _, _, .assumption _ _ _ _ _ C hA => hA.atoms Aw ++ C.atoms Aw
  | _, _, _, .letBinding _ _ _ _ _ _ C hA hv => hA.atoms Aw ++ hv.atoms Aw ++ C.atoms Aw

/-- Total weight of a context derivation spine `CtxP`. -/
def CtxP.wt (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    CtxP E n Γ → Nat
  | _, _, _, .nil _ _ => 0
  | _, _, _, .assumption _ _ _ _ _ C hA => hA.wt Aw + C.wt Aw
  | _, _, _, .letBinding _ _ _ _ _ _ C hA hv => hA.wt Aw + hv.wt Aw + C.wt Aw

/-- A context spine `C : CtxP E n Γ` as a point of `LexDM`. -/
def ctxMeas (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (C : CtxP E n Γ) : List Nat × Nat :=
  (C.atoms Aw, C.wt Aw)

/-- The lexicographic pair order on `(context-spine measure, node measure)`. -/
abbrev PairLexDM := Prod.Lex LexDM LexDM

/-- The combined multiset measure `(C.atoms ++ m.1, C.wt + m.2)`. -/
def combMeas (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (C : CtxP E n Γ) (m : List Nat × Nat) : List Nat × Nat :=
  (C.atoms Aw ++ m.1, C.wt Aw + m.2)

theorem acc_asymm {α : Type u} {r : α → α → Prop} {a : α} (h : Acc r a) :
    ∀ {b : α}, r a b → ¬ r b a := by
  induction h with
  | intro x _ ih =>
      intro b hxb hbx
      exact ih b hbx hbx hxb

theorem lexDM_asymm {a b : List Nat × Nat} (hab : LexDM a b) : ¬ LexDM b a :=
  acc_asymm (lexDM_wf.apply a) hab

theorem pairLexDM_wf : WellFounded PairLexDM :=
  ⟨fun ⟨c, m⟩ => Prod.lexAccessible (lexDM_wf.apply c) (fun b => lexDM_wf.apply b) m⟩

theorem pairLexDM_asymm {p q : (List Nat × Nat) × (List Nat × Nat)}
    (hpq : PairLexDM p q) : ¬ PairLexDM q p :=
  acc_asymm (pairLexDM_wf.apply p) hpq

private theorem dmStep_append_right (Z : List Nat) {M' M : List Nat} (h : DMStep M' M) :
    DMStep (M' ++ Z) (M ++ Z) := by
  rcases h with ⟨X, Y, W, hX, hMW, hYW, hlt⟩
  refine ⟨X, Y, W ++ Z, hX, ?_, ?_, hlt⟩
  · rw [← List.append_assoc]
    exact hMW.append_right Z
  · rw [← List.append_assoc]
    exact hYW.append_right Z

private theorem dmStep_append_left (Z : List Nat) {M' M : List Nat} (h : DMStep M' M) :
    DMStep (Z ++ M') (Z ++ M) := by
  rcases dmStep_append_right Z h with ⟨X, Y, W, hX, hMW, hYW, hlt⟩
  exact ⟨X, Y, W, hX, List.perm_append_comm.trans hMW, List.perm_append_comm.trans hYW, hlt⟩

/-! ### §2.1 Wall A: Binder-extending arms (`pi`, `lam`, `letE`, `beta`, `zeta`, `fsub`) fail `PairLexDM` -/

/-- Pushing `.assumption` onto `C` strictly **increases** `ctxMeas` in `LexDM`. -/
theorem lexDM_ctxMeas_assumption (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    (C : CtxP E n Γ) (hA : TyP E n Γ A (.sort u)) :
    LexDM (ctxMeas Aw C) (ctxMeas Aw (.assumption E n Γ A u C hA)) :=
  lex_of_dm (dmStep_drop (TyP.atoms_ne_nil Aw hA))

/-- Pushing `.letBinding` onto `C` strictly **increases** `ctxMeas` in `LexDM`. -/
theorem lexDM_ctxMeas_letBinding (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v : Expr Nat} {u : Level}
    (C : CtxP E n Γ) (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A) :
    LexDM (ctxMeas Aw C) (ctxMeas Aw (.letBinding E n Γ A u v C hA hv)) := by
  have hne : hA.atoms Aw ++ hv.atoms Aw ≠ [] := by
    intro hnil
    exact TyP.atoms_ne_nil Aw hA (List.append_eq_nil.mp hnil).1
  have hdm : DMStep (C.atoms Aw) ((hA.atoms Aw ++ hv.atoms Aw) ++ C.atoms Aw) :=
    dmStep_drop hne
  exact lex_of_dm hdm

/-- Wall A (`.assumption`): for every binder-extending arm (`CvP.pi`, `CvP.lam`,
    `CvP.beta`, `CvP.fsub`), the recursive call in the extended context
    `.assumption A :: Γ` never decreases under `PairLexDM`. -/
theorem not_pairLexDM_binder_extend (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    (C : CtxP E n Γ) (hA : TyP E n Γ A (.sort u))
    (m m' : List Nat × Nat) :
    ¬ PairLexDM (ctxMeas Aw (.assumption E n Γ A u C hA), m') (ctxMeas Aw C, m) :=
  pairLexDM_asymm (Prod.Lex.left _ _ (lexDM_ctxMeas_assumption Aw C hA))

/-- Wall A (`.letBinding`): for `CvP.letE` and `CvP.zeta`, the recursive call in
    the extended context `.letBinding A v :: Γ` never decreases under `PairLexDM`. -/
theorem not_pairLexDM_let_extend (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v : Expr Nat} {u : Level}
    (C : CtxP E n Γ) (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A)
    (m m' : List Nat × Nat) :
    ¬ PairLexDM (ctxMeas Aw (.letBinding E n Γ A u v C hA hv), m') (ctxMeas Aw C, m) :=
  pairLexDM_asymm (Prod.Lex.left _ _ (lexDM_ctxMeas_letBinding Aw C hA hv))

/-- By contrast, under `combMeas`, any binder-extending call from a rule node `hnode`
    whose binder typing `hA` and body `Y` have weights `< hnode.wt Aw` strictly decreases. -/
theorem combLexDM_binder_rule (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A a b T : Expr Nat} {u : Level}
    (C : CtxP E n Γ) (hA : TyP E n Γ A (.sort u))
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (hwA : hA.wt Aw < hnode.wt Aw)
    {Y : List Nat} {wY : Nat} (hY : ∀ y ∈ Y, y < hnode.wt Aw) :
    LexDM (combMeas Aw (.assumption E n Γ A u C hA) (Y, wY))
      (combMeas Aw C (cvMeas Aw hnode)) := by
  have hsub : ∀ y ∈ hA.atoms Aw ++ Y, y < hnode.wt Aw := by
    intro y hy
    rcases List.mem_append.mp hy with hyA | hyY
    · exact atoms_lt_of_wt_lt Aw hA hwA y hyA
    · exact hY y hyY
  have hdm0 : DMStep (hA.atoms Aw ++ Y) (hnode.atoms Aw) :=
    dmStep_under_rule Aw hnode ht hsub
  have hdm1 : DMStep (C.atoms Aw ++ (hA.atoms Aw ++ Y)) (C.atoms Aw ++ hnode.atoms Aw) :=
    dmStep_append_left (C.atoms Aw) hdm0
  rcases hdm1 with ⟨X, Y', W, hX, hMW, hYW, hlt⟩
  have hperm : ((hA.atoms Aw ++ C.atoms Aw) ++ Y).Perm (C.atoms Aw ++ (hA.atoms Aw ++ Y)) := by
    rw [← List.append_assoc]
    exact List.perm_append_comm.append_right Y
  exact lex_of_dm ⟨X, Y', W, hX, hMW, hperm.trans hYW, hlt⟩

/-! ### §2.2 Wall B: `cctx` fails `PairLexDM` when `hA.dl` is heavier than `hA'`, but succeeds under `combMeas` -/

/-- A sort typing of weight `6 > 1` (`TyP.conv` over `CvP.refl` on `.sort 0 : .sort 1`). -/
def pbitWallHeavySort (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  let s01 := TyP.sort E n [] .zero (.succ .zero) (eqN_refl _)
  let s12 := TyP.sort E n [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)
  TyP.conv E n [] (.sort .zero) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)) s01
    (CvP.refl E n [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) s12 s12 s12)

/-- `hA : CvP E n [] (.sort 0) (.sort 0) (.sort 1)` whose left endpoint `hA.dl` is
    `pbitWallHeavySort` (weight `6`) and whose right endpoint `hA.dr` has weight `1`. -/
def cctxWallDomCv (E : ResolvedEnv) (n : Nat) :
    CvP E n [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  let s01 := TyP.sort E n [] .zero (.succ .zero) (eqN_refl _)
  CvP.refl E n [] (.sort .zero) (.sort (.succ .zero)) s01 (pbitWallHeavySort E n) s01

/-- Outer context spine for `cctx`: `.assumption` with `(cctxWallDomCv E n).dr` (weight `1`). -/
def cctxWallOutCtxP (E : ResolvedEnv) (n : Nat) : CtxP E n pbitCtx :=
  CtxP.assumption E n [] (.sort .zero) (.succ .zero) (.nil E n) (cctxWallDomCv E n).dr

/-- Inner context spine for `cctx`: `.assumption` with `(cctxWallDomCv E n).dl` (weight `6`). -/
def cctxWallInCtxP (E : ResolvedEnv) (n : Nat) : CtxP E n pbitCtx :=
  CtxP.assumption E n [] (.sort .zero) (.succ .zero) (.nil E n) (cctxWallDomCv E n).dl

/-- Wall B: in `cctx`, replacing the outer context spine `cctxWallOutCtxP` (weight `1`)
    with the inner context spine `cctxWallInCtxP` (weight `6`) strictly **increases**
    `ctxMeas`, so `PairLexDM` fails to decrease for every `m, m'`. -/
theorem not_pairLexDM_cctx (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat)
    (m m' : List Nat × Nat) :
    ¬ PairLexDM (ctxMeas Aw (cctxWallInCtxP E n), m') (ctxMeas Aw (cctxWallOutCtxP E n), m) := by
  have hdm : DMStep ((cctxWallOutCtxP E n).atoms Aw) ((cctxWallInCtxP E n).atoms Aw) := by
    change DMStep [1] [6]
    exact ⟨[6], [1], [], by decide, List.Perm.refl _, List.Perm.refl _,
      fun y hy => ⟨6, .head _, by rw [List.mem_singleton.mp hy]; decide⟩⟩
  exact pairLexDM_asymm (Prod.Lex.left _ _ (lex_of_dm hdm))

/-- Under `combMeas`, the inner call of `CvP.cctx` at `C_in = .assumption C₀ hA.dl`
    strictly decreases in `LexDM`. -/
theorem combLexDM_cctx_inner (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' a b B : Expr Nat} {u u' : Level}
    (C₀ : CtxP E n Γ) (hA' : TyP E n Γ A' (.sort u'))
    (h : CvP E n (.assumption A :: Γ) a b B)
    (hA : CvP E n Γ A A' (.sort u)) (htA : hA.isTransport = false) :
    LexDM
      (combMeas Aw (.assumption E n Γ A u C₀ hA.dl) (cvMeas Aw h))
      (combMeas Aw (.assumption E n Γ A' u' C₀ hA')
        (cvMeas Aw (.cctx E n Γ a b B A A' u h hA))) := by
  have hlt : ∀ y ∈ hA.dl.atoms Aw, y < hA.wt Aw :=
    atoms_lt_of_wt_lt Aw hA.dl (CvP.wt_dl_lt Aw hA)
  have hdmA : DMStep (hA.dl.atoms Aw) (hA'.atoms Aw ++ hA.atoms Aw) := by
    refine ⟨hA'.atoms Aw ++ hA.atoms Aw, hA.dl.atoms Aw, [], ?_,
      by rw [List.append_nil], by rw [List.append_nil], ?_⟩
    · intro hnil
      exact TyP.atoms_ne_nil Aw hA' (List.append_eq_nil.mp hnil).1
    · intro y hy
      refine ⟨hA.wt Aw, List.mem_append.mpr (Or.inr ?_), hlt y hy⟩
      rw [CvP.atoms_rule Aw hA htA]
      exact .head _
  rcases dmStep_append_right (C₀.atoms Aw ++ h.atoms Aw) hdmA with
    ⟨X, Y, W, hX, hMW, hYW, hdom⟩
  have hpermOut :
      (((hA'.atoms Aw ++ C₀.atoms Aw) ++ (h.atoms Aw ++ hA.atoms Aw))).Perm
        ((hA'.atoms Aw ++ hA.atoms Aw) ++ (C₀.atoms Aw ++ h.atoms Aw)) := by
    rw [List.append_assoc (hA'.atoms Aw), List.append_assoc (hA'.atoms Aw)]
    refine List.Perm.append_left (hA'.atoms Aw) ?_
    rw [← List.append_assoc (C₀.atoms Aw)]
    exact List.perm_append_comm
  have hpermIn :
      ((hA.dl.atoms Aw ++ C₀.atoms Aw) ++ h.atoms Aw).Perm
        (hA.dl.atoms Aw ++ (C₀.atoms Aw ++ h.atoms Aw)) := by
    rw [List.append_assoc]
  exact lex_of_dm ⟨X, Y, W, hX, hpermOut.trans hMW, hpermIn.trans hYW, hdom⟩

/-- Under `combMeas`, the `BitCoh` call of `CvP.cctx` on `(hA', hA.dr)` in the tail
    context `C₀` also strictly decreases in `LexDM`. -/
theorem combLexDM_cctx_bitCoh (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' a b B : Expr Nat} {u u' : Level}
    (C₀ : CtxP E n Γ) (hA' : TyP E n Γ A' (.sort u'))
    (h : CvP E n (.assumption A :: Γ) a b B)
    (hA : CvP E n Γ A A' (.sort u)) (htA : hA.isTransport = false) :
    LexDM
      (combMeas Aw C₀ (tyPairMeas Aw hA' hA.dr))
      (combMeas Aw (.assumption E n Γ A' u' C₀ hA')
        (cvMeas Aw (.cctx E n Γ a b B A A' u h hA))) := by
  have hlt : ∀ y ∈ hA.dr.atoms Aw, y < hA.wt Aw :=
    atoms_lt_of_wt_lt Aw hA.dr (CvP.wt_dr_lt Aw hA)
  have hdmA : DMStep (hA.dr.atoms Aw) (h.atoms Aw ++ hA.atoms Aw) := by
    refine ⟨h.atoms Aw ++ hA.atoms Aw, hA.dr.atoms Aw, [], ?_,
      by rw [List.append_nil], by rw [List.append_nil], ?_⟩
    · intro hnil
      exact CvP.atoms_ne_nil Aw h (List.append_eq_nil.mp hnil).1
    · intro y hy
      refine ⟨hA.wt Aw, List.mem_append.mpr (Or.inr ?_), hlt y hy⟩
      rw [CvP.atoms_rule Aw hA htA]
      exact .head _
  rcases dmStep_append_left (C₀.atoms Aw ++ hA'.atoms Aw) hdmA with
    ⟨X, Y, W, hX, hMW, hYW, hdom⟩
  have hpermOut :
      ((hA'.atoms Aw ++ C₀.atoms Aw) ++ (h.atoms Aw ++ hA.atoms Aw)).Perm
        ((C₀.atoms Aw ++ hA'.atoms Aw) ++ (h.atoms Aw ++ hA.atoms Aw)) :=
    List.Perm.append_right _ List.perm_append_comm
  have hpermIn :
      (C₀.atoms Aw ++ (hA'.atoms Aw ++ hA.dr.atoms Aw)).Perm
        ((C₀.atoms Aw ++ hA'.atoms Aw) ++ hA.dr.atoms Aw) := by
    rw [List.append_assoc]
  exact lex_of_dm ⟨X, Y, W, hX, hpermOut.trans hMW, hpermIn.trans hYW, hdom⟩

/-! ### §2.3 Wall C: `PBit(.bvar)` fails BOTH `PairLexDM` and `combMeas` when `C`'s entry is heavier than `D` -/

/-- Context spine for `pbitCtx = [.assumption (.sort .zero)]` whose entry typing is
    `pbitWallHeavySort` (weight `6`, atoms `[6]`). -/
def pbitWallCtxP (E : ResolvedEnv) (n : Nat) : CtxP E n pbitCtx :=
  CtxP.assumption E n [] (.sort .zero) (.succ .zero) (.nil E n) (pbitWallHeavySort E n)

/-- Weakening `pbitWallHeavySort` by `wkAtZero` into `pbitCtx` (weight `6`, atoms `[6]`). -/
def pbitWallWkHeavy (E : ResolvedEnv) (n : Nat) :
    TyP E n pbitCtx (.sort .zero) (.sort (.succ .zero)) :=
  wkAtZero (A := .sort .zero) (pbitWallHeavySort E n)

/-- Wall C (`PairLexDM`): at `PBit` on `pbitVar` (weight `2`) and `pbitSort` (weight `1`)
    in `pbitWallCtxP`, calling `BitCoh` on `(pbitWallWkHeavy, pbitSort)` strictly
    **increases** the node measure from `([2, 1], 3)` to `([6, 1], 7)` while leaving
    `ctxMeas` unchanged, so `PairLexDM` fails to decrease. -/
theorem not_pairLexDM_pbit_bvar (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    ¬ PairLexDM
      (ctxMeas Aw (pbitWallCtxP E n),
        tyPairMeas Aw (pbitWallWkHeavy E n) (pbitSort E n))
      (ctxMeas Aw (pbitWallCtxP E n),
        tyPairMeas Aw (pbitVar E n) (pbitSort E n)) := by
  have hat1 : (tyPairMeas Aw (pbitVar E n) (pbitSort E n)).1 = [2, 1] := rfl
  have hat2 : (tyPairMeas Aw (pbitWallWkHeavy E n) (pbitSort E n)).1 = [6, 1] := by
    simp only [tyPairMeas, pbitWallWkHeavy, wkAtZero, atoms_tyCastCtx, TyP.atoms,
      pbitWallHeavySort, pbitSort, TyP.wt, CvP.wt]
    rfl
  have hdm : DMStep
      ((tyPairMeas Aw (pbitVar E n) (pbitSort E n)).1)
      ((tyPairMeas Aw (pbitWallWkHeavy E n) (pbitSort E n)).1) := by
    rw [hat1, hat2]
    exact dmStep_append_right [1]
      ⟨[6], [2], [], by decide, List.Perm.refl _, List.Perm.refl _,
        fun y hy => ⟨6, .head _, by rw [List.mem_singleton.mp hy]; decide⟩⟩
  exact pairLexDM_asymm (Prod.Lex.right _ (lex_of_dm hdm))

/-- Wall C (`combMeas`): under the combined multiset `combMeas`, calling `BitCoh` on
    `(pbitWallWkHeavy, pbitSort)` in `pbitWallCtxP` strictly **increases** the measure
    from `([6, 2, 1], 9)` to `([6, 6, 1], 13)` because `pbitWallHeavySort` remains in
    `pbitWallCtxP` while being duplicated into the `BitCoh` pair. -/
theorem not_combLexDM_pbit_bvar (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    ¬ LexDM
      (combMeas Aw (pbitWallCtxP E n)
        (tyPairMeas Aw (pbitWallWkHeavy E n) (pbitSort E n)))
      (combMeas Aw (pbitWallCtxP E n)
        (tyPairMeas Aw (pbitVar E n) (pbitSort E n))) := by
  have hat1 :
      (combMeas Aw (pbitWallCtxP E n)
        (tyPairMeas Aw (pbitVar E n) (pbitSort E n))).1 = [6] ++ ([2] ++ [1]) := rfl
  have hat2 :
      (combMeas Aw (pbitWallCtxP E n)
        (tyPairMeas Aw (pbitWallWkHeavy E n) (pbitSort E n))).1 = [6] ++ ([6] ++ [1]) := by
    simp only [combMeas, CtxP.atoms, tyPairMeas, pbitWallCtxP, pbitWallWkHeavy, wkAtZero,
      atoms_tyCastCtx, TyP.atoms, pbitWallHeavySort, pbitSort, TyP.wt, CvP.wt]
    rfl
  have hdm : DMStep
      ((combMeas Aw (pbitWallCtxP E n)
        (tyPairMeas Aw (pbitVar E n) (pbitSort E n))).1)
      ((combMeas Aw (pbitWallCtxP E n)
        (tyPairMeas Aw (pbitWallWkHeavy E n) (pbitSort E n))).1) := by
    rw [hat1, hat2]
    exact dmStep_append_left [6]
      (dmStep_append_right [1]
        ⟨[6], [2], [], by decide, List.Perm.refl _, List.Perm.refl _,
          fun y hy => ⟨6, .head _, by rw [List.mem_singleton.mp hy]; decide⟩⟩)
  exact lexDM_asymm (lex_of_dm hdm)

end Rcic.Syn

#print axioms Rcic.Syn.es_zetaNode_inline
#print axioms Rcic.Syn.resolve_keep_drop
#print axioms Rcic.Syn.not_convMod_star_sort
#print axioms Rcic.Syn.not_convMod_bvar_sort
#print axioms Rcic.Syn.not_es_zetaLocal_keep_drop
#print axioms Rcic.Syn.zetaOneCtx
#print axioms Rcic.Syn.zetaOneNode
#print axioms Rcic.Syn.not_es_zetaLocal_same_disp
#print axioms Rcic.Syn.CtxP.atoms
#print axioms Rcic.Syn.CtxP.wt
#print axioms Rcic.Syn.ctxMeas
#print axioms Rcic.Syn.PairLexDM
#print axioms Rcic.Syn.combMeas
#print axioms Rcic.Syn.acc_asymm
#print axioms Rcic.Syn.lexDM_asymm
#print axioms Rcic.Syn.pairLexDM_wf
#print axioms Rcic.Syn.pairLexDM_asymm
#print axioms Rcic.Syn.lexDM_ctxMeas_assumption
#print axioms Rcic.Syn.lexDM_ctxMeas_letBinding
#print axioms Rcic.Syn.not_pairLexDM_binder_extend
#print axioms Rcic.Syn.not_pairLexDM_let_extend
#print axioms Rcic.Syn.combLexDM_binder_rule
#print axioms Rcic.Syn.pbitWallHeavySort
#print axioms Rcic.Syn.cctxWallDomCv
#print axioms Rcic.Syn.cctxWallOutCtxP
#print axioms Rcic.Syn.cctxWallInCtxP
#print axioms Rcic.Syn.not_pairLexDM_cctx
#print axioms Rcic.Syn.combLexDM_cctx_inner
#print axioms Rcic.Syn.combLexDM_cctx_bitCoh
#print axioms Rcic.Syn.pbitWallCtxP
#print axioms Rcic.Syn.pbitWallWkHeavy
#print axioms Rcic.Syn.not_pairLexDM_pbit_bvar
#print axioms Rcic.Syn.not_combLexDM_pbit_bvar
