import rcic.RcicTypedSubstLet
import rcic.RcicSynClause
import rcic.RcicERPiSlotConv
import rcic.RcicSynSpineComb

/-!
# Syntactic sortRow, build step 3ar — Option L-inline-at-0, Q7 `letE` `AssumpPref`, and `zeta`/`letE`/`zetaLocal` `ES` arms

`research/rcic/semantic/S3_ES_ARMS.md` §44. Per cc's ruling on `Q11`
Obligation 1 (**Option L-inline-at-0**, `issuecomment-6161495965`):

1. **Plain `HasTyT` / `ConvT` `.letBinding`-at-`0` discharge**:
   `hasTyT_substLet0_of_envWfT` (`RcicTypedSubstLet.lean:380`) and its `ConvT`
   counterpart `convT_substLet0_of_envWfT` discharge `.letBinding t w0` at
   index `0` (`hasTyT_letE_inline0_of_envWfT`, `convT_letE_inline0_of_envWfT`).

2. **Q7 Obligation 2 (`TyP.AssumpPref`, `CvP.AssumpPref`)**:
   `TyP.AssumpPref` and `CvP.AssumpPref` verify recursively that every
   `TyP.wk` / `CvP.wk` at cutoff `c` and every `TyP.esub` / `CvP.esub` /
   `TyP.lsub` at cutoff `j` in the derivation tree satisfies
   `AssumptionPrefix Γ c` (resp. `AssumptionPrefix Γ j`).
   Preservation is proved for `tyCast`, `tyCastCtx`, `cvCast`, `cvCastCtx`,
   `castLift0`, `sortLift0`, `CvP.dl`, `CvP.dr`, `TyP.reg`, `wkAtZero`,
   `wkLetAtZero`, `wkFront`, `cvFront`, `instEnd`, `letSub`, `pushBodyEsub`,
   the Q7 `letE` / `zeta` translations `trLetNorm`, `trLetE`, `trZeta`, and the
   `letSub`-normalised Instances A and B (`assumpPref_instEnd_betaLetBody_norm`,
   `assumpPref_wkAtZero_betaLetReduct_norm`).

3. **Q11 Obligation 1 (Instance 3: `ConvT.letE` under Option L-inline-at-0)**:
   With both endpoints `letSub`-normalised at `0` (`letEndL`, `letEndR`, with
   surface counterparts `letSurfL`, `letSurfR` having identical erasures by
   `letSub_eps_eq_letE`), `cvpLetDecomp` decomposes `ConvT.letE` at `j = 0`
   through `trZeta` (left), the `j = 0` let-substituted body conversion
   `hb_sub`, `CvP.fsub` on `v ≡ v' : A`, and `CvP.symm (CvP.tyConv (trZeta ...))`
   (right), satisfying `CvP.AssumpPref` with **zero** let-binding `cctx`.

4. **`ES` arms for `zeta`, `letE`, and spine-aligned `zetaLocal`**:
   `es_of_below_zeta`, `letE_body_es`, `es_of_below_letE_of_dr`,
   `zetaLocal_dr`, `es_of_below_zetaLocal_of_lhs`,
   `es_of_below_zetaLocal_zero_drop`, and `es_of_below_zetaLocal_zero_inline`.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Plain `HasTyT` / `ConvT` `.letBinding`-at-`0` elimination -/

/-- `ConvT` counterpart of `hasTyT_substLet0_of_envWfT` (`RcicTypedSubstLet.lean:380`):
    head `.letBinding` substitution at `j = 0`. -/
def convT_substLet0_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {t w0 : Expr Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n (LocalDecl.letBinding t w0 :: Γ) a b T)
    (hv : HasTyT E n Γ w0 t) :
    ConvT E n Γ (instantiate0 w0 a) (instantiate0 w0 b) (instantiate0 w0 T) := by
  have h0 := convT_substLet_of_envWfT hW t w0 (j := 0) h (by simp)
    (by rw [lift_zero, lift_zero]; exact hv)
  rw [lift_zero] at h0
  exact h0

/-- Discharging `.letBinding A value` at `0` on `HasTyT.letE`'s body premise via
    `hasTyT_substLet0_of_envWfT` produces the `letSub`-normalised typing in `Γ`. -/
def hasTyT_letE_inline0_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} {A : Expr Nat} {u : Level} {value B body : Expr Nat}
    (_hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B) :
    HasTyT E n Γ (instantiate0 value body) (instantiate0 value B) :=
  hasTyT_substLet0_of_envWfT hW hb hv

/-- Discharging `.letBinding A v` at `0` on `ConvT.letE`'s body conversion via
    `convT_substLet0_of_envWfT` produces `instantiate0 v b ≡ instantiate0 v b'`
    at `instantiate0 v B` directly in `Γ`. -/
def convT_letE_inline0_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (_hA : ConvT E n Γ A A' (.sort u)) (_hv : ConvT E n Γ v v' A)
    (hvl : HasTyT E n Γ v A)
    (hb : ConvT E n (.letBinding A v :: Γ) b b' B) :
    ConvT E n Γ (instantiate0 v b) (instantiate0 v b') (instantiate0 v B) :=
  convT_substLet0_of_envWfT hW hb hvl

/-! ## §2 `TyP.AssumpPref` and `CvP.AssumpPref` (Q7 Obligation 2) -/

/-- Extending the context by `.assumption A` preserves `AssumptionPrefix` at `c + 1`. -/
theorem assumptionPrefix_succ_assumption (A : Expr Nat) (Γ : LCtx) (c : Nat)
    (h : AssumptionPrefix Γ c) :
    AssumptionPrefix (.assumption A :: Γ) (c + 1) := by
  intro d hd
  simp only [List.take_succ_cons, List.mem_cons] at hd
  cases hd with
  | inl hd0 =>
      cases hd0
      exact ⟨A, rfl⟩
  | inr hdt =>
      exact h d hdt

mutual

/-- Every transport node (`wk` at `c`, `esub` at `j`, `lsub` at `j`) in `D`
    satisfies `AssumptionPrefix` at its cutoff, recursively through all children. -/
def TyP.AssumpPref : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → Prop
  | _, _, _, _, _, .sort .. => True
  | _, _, _, _, _, .bvar _ _ _ _ _ _ _ hA => hA.AssumpPref
  | _, _, _, _, _, .const _ _ _ _ _ _ _ _ _ _ _ _ hT => hT.AssumpPref
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => hA.AssumpPref ∧ hB.AssumpPref
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ hA hb hB =>
      hA.AssumpPref ∧ hb.AssumpPref ∧ hB.AssumpPref
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha hT =>
      hf.AssumpPref ∧ ha.AssumpPref ∧ hT.AssumpPref
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT =>
      hA.AssumpPref ∧ hv.AssumpPref ∧ hb.AssumpPref ∧ hT.AssumpPref
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.AssumpPref
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h hc => h.AssumpPref ∧ hc.AssumpPref
  | _, _, _, _, _, .wk _ _ Γ _ _ _ c D =>
      AssumptionPrefix Γ c ∧ D.AssumpPref
  | _, _, _, _, _, .esub _ _ Γ _ _ _ _ j _ D _ hv hvT =>
      AssumptionPrefix Γ j ∧ D.AssumpPref ∧ hv.AssumpPref ∧ hvT.AssumpPref
  | _, _, _, _, _, .lsub _ _ Γ _ _ _ _ j _ D _ hv hvT =>
      AssumptionPrefix Γ j ∧ D.AssumpPref ∧ hv.AssumpPref ∧ hvT.AssumpPref
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => D.AssumpPref
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.AssumpPref
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA => D.AssumpPref ∧ hA.AssumpPref

/-- Every transport node (`wk` at `c`, `esub` at `j`) in `h` satisfies
    `AssumptionPrefix` at its cutoff, recursively through all children. -/
def CvP.AssumpPref : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvP E n Γ a b T → Prop
  | _, _, _, _, _, _, .refl _ _ _ _ _ h dl dr =>
      h.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ h dl dr =>
      h.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ h1 h2 dl dr =>
      h1.AssumpPref ∧ h2.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .beta _ _ _ _ _ _ _ _ hA hbody harg dl dr =>
      hA.AssumpPref ∧ hbody.AssumpPref ∧ harg.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ hA hv hb dl dr =>
      hA.AssumpPref ∧ hv.AssumpPref ∧ hb.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .zetaLocal _ _ _ _ _ _ _ _ hv dl dr =>
      hv.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ hb dl dr =>
      hb.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .iota _ _ _ _ _ _ _ hlhs hrhs dl dr =>
      hlhs.AssumpPref ∧ hrhs.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .lit _ _ _ _ _ _ _ hexp dl dr =>
      hexp.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 dl dr =>
      h1.AssumpPref ∧ h2.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hA hb dl dr =>
      hA.AssumpPref ∧ hb.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ hA hB dl dr =>
      hA.AssumpPref ∧ hB.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ hA hv hb dl dr =>
      hA.AssumpPref ∧ hv.AssumpPref ∧ hb.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .sorts _ _ _ _ _ _ dl dr =>
      dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ _ dl dr =>
      dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .eta _ _ _ _ _ _ h dl dr =>
      h.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .irr _ _ _ _ _ _ hP hp hq dl dr =>
      hP.AssumpPref ∧ hp.AssumpPref ∧ hq.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h hA dl dr =>
      h.AssumpPref ∧ hA.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref
  | _, _, _, _, _, _, .wk _ _ Γ _ _ _ _ c h =>
      AssumptionPrefix Γ c ∧ h.AssumpPref
  | _, _, _, _, _, _, .esub _ _ Γ _ _ _ _ _ j _ h _ hv hvT =>
      AssumptionPrefix Γ j ∧ h.AssumpPref ∧ hv.AssumpPref ∧ hvT.AssumpPref
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h => h.AssumpPref
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h => h.AssumpPref
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA =>
      h.AssumpPref ∧ hA.AssumpPref
  | _, _, _, _, _, _, .fsub _ _ _ _ _ _ _ _ _ hB hA hab dl dr =>
      hB.AssumpPref ∧ hA.AssumpPref ∧ hab.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref

end

theorem assumpPref_tyCast {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e e' T T' : Expr Nat} (he : e = e') (hT : T = T') {D : TyP E n Γ e T}
    (hD : D.AssumpPref) : (tyCast he hT D).AssumpPref := by
  cases he
  cases hT
  exact hD

theorem assumpPref_tyCastCtx {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx}
    {e T : Expr Nat} (hΓ : Γ = Γ') {D : TyP E n Γ e T}
    (hD : D.AssumpPref) : (tyCastCtx hΓ D).AssumpPref := by
  cases hΓ
  exact hD

theorem assumpPref_cvCast {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a a' b b' T T' : Expr Nat} (ha : a = a') (hb : b = b') (hT : T = T')
    {h : CvP E n Γ a b T} (hh : h.AssumpPref) :
    (cvCast ha hb hT h).AssumpPref := by
  cases ha
  cases hb
  cases hT
  exact hh

theorem assumpPref_cvCastCtx {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx}
    {a b T : Expr Nat} (hΓ : Γ = Γ') {h : CvP E n Γ a b T}
    (hh : h.AssumpPref) : (cvCastCtx hΓ h).AssumpPref := by
  cases hΓ
  exact hh

theorem assumpPref_castLift0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v t : Expr Nat} {D : TyP E n Γ v t} (hD : D.AssumpPref) :
    (castLift0 D).AssumpPref :=
  assumpPref_tyCast _ _ hD

theorem assumpPref_sortLift0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {hA : TyP E n Γ A (.sort u)}
    (hD : hA.AssumpPref) : (sortLift0 hA).AssumpPref :=
  assumpPref_tyCast _ _ (assumpPref_castLift0 hD)

theorem assumpPref_dl : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → {h : CvP E n Γ a b T} → h.AssumpPref → h.dl.AssumpPref
  | _, _, _, _, _, _, .refl .., hh => hh.2.1
  | _, _, _, _, _, _, .symm .., hh => hh.2.1
  | _, _, _, _, _, _, .trans .., hh => hh.2.2.1
  | _, _, _, _, _, _, .beta .., hh => hh.2.2.2.1
  | _, _, _, _, _, _, .zeta .., hh => hh.2.2.2.1
  | _, _, _, _, _, _, .zetaLocal .., hh => hh.2.1
  | _, _, _, _, _, _, .delta .., hh => hh.2.1
  | _, _, _, _, _, _, .iota .., hh => hh.2.2.1
  | _, _, _, _, _, _, .lit .., hh => hh.2.1
  | _, _, _, _, _, _, .app .., hh => hh.2.2.1
  | _, _, _, _, _, _, .lam .., hh => hh.2.2.1
  | _, _, _, _, _, _, .pi .., hh => hh.2.2.1
  | _, _, _, _, _, _, .letE .., hh => hh.2.2.2.1
  | _, _, _, _, _, _, .sorts .., hh => hh.1
  | _, _, _, _, _, _, .consts .., hh => hh.1
  | _, _, _, _, _, _, .eta .., hh => hh.2.1
  | _, _, _, _, _, _, .irr .., hh => hh.2.2.2.1
  | _, _, _, _, _, _, .tyConv .., hh => hh.2.2.1
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h, hh => ⟨hh.1, assumpPref_dl (h := h) hh.2⟩
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ _ _, hh =>
      ⟨hh.1, assumpPref_dl (h := h) hh.2.1, hh.2.2.1, hh.2.2.2⟩
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h, hh => assumpPref_dl (h := h) hh
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h, hh => assumpPref_dl (h := h) hh
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h _, hh =>
      ⟨assumpPref_dl (h := h) hh.1, hh.2⟩
  | _, _, _, _, _, _, .fsub .., hh => hh.2.2.2.1

theorem assumpPref_dr : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → {h : CvP E n Γ a b T} → h.AssumpPref → h.dr.AssumpPref
  | _, _, _, _, _, _, .refl .., hh => hh.2.2
  | _, _, _, _, _, _, .symm .., hh => hh.2.2
  | _, _, _, _, _, _, .trans .., hh => hh.2.2.2
  | _, _, _, _, _, _, .beta .., hh => hh.2.2.2.2
  | _, _, _, _, _, _, .zeta .., hh => hh.2.2.2.2
  | _, _, _, _, _, _, .zetaLocal .., hh => hh.2.2
  | _, _, _, _, _, _, .delta .., hh => hh.2.2
  | _, _, _, _, _, _, .iota .., hh => hh.2.2.2
  | _, _, _, _, _, _, .lit .., hh => hh.2.2
  | _, _, _, _, _, _, .app .., hh => hh.2.2.2
  | _, _, _, _, _, _, .lam .., hh => hh.2.2.2
  | _, _, _, _, _, _, .pi .., hh => hh.2.2.2
  | _, _, _, _, _, _, .letE .., hh => hh.2.2.2.2
  | _, _, _, _, _, _, .sorts .., hh => hh.2
  | _, _, _, _, _, _, .consts .., hh => hh.2
  | _, _, _, _, _, _, .eta .., hh => hh.2.2
  | _, _, _, _, _, _, .irr .., hh => hh.2.2.2.2
  | _, _, _, _, _, _, .tyConv .., hh => hh.2.2.2
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h, hh => ⟨hh.1, assumpPref_dr (h := h) hh.2⟩
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ _ _, hh =>
      ⟨hh.1, assumpPref_dr (h := h) hh.2.1, hh.2.2.1, hh.2.2.2⟩
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h, hh => assumpPref_dr (h := h) hh
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h, hh => assumpPref_dr (h := h) hh
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h _, hh =>
      ⟨assumpPref_dr (h := h) hh.1, hh.2⟩
  | _, _, _, _, _, _, .fsub .., hh => hh.2.2.2.2

theorem assumpPref_reg : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → {D : TyP E n Γ e T} → D.AssumpPref → D.reg.2.AssumpPref
  | _, _, _, _, _, .sort .., _ => trivial
  | _, _, _, _, _, .bvar .., hD => hD
  | _, _, _, _, _, .const .., hD => hD
  | _, _, _, _, _, .pi .., _ => trivial
  | _, _, _, _, _, .lam .., hD => ⟨hD.1, hD.2.2⟩
  | _, _, _, _, _, .app .., hD => hD.2.2
  | _, _, _, _, _, .letE .., hD => hD.2.2.2
  | _, _, _, _, _, .lit _ _ _ _ _ hexp, hD => assumpPref_reg (D := hexp) hD
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ _ hc, hD => assumpPref_dr (h := hc) hD.2
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D, hD => ⟨hD.1, assumpPref_reg (D := D) hD.2⟩
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ _ _, hD =>
      ⟨hD.1, assumpPref_reg (D := D) hD.2.1, hD.2.2.1, hD.2.2.2⟩
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ _ _, hD =>
      ⟨hD.1, assumpPref_reg (D := D) hD.2.1, hD.2.2.1, hD.2.2.2⟩
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D, hD => assumpPref_reg (D := D) hD
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, hD => assumpPref_reg (D := D) hD
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, hD =>
      ⟨assumpPref_reg (D := D) hD.1, hD.2⟩

theorem assumpPref_wkAtZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A : Expr Nat} {D : TyP E n Γ e T} (hD : D.AssumpPref) :
    (wkAtZero (A := A) D).AssumpPref :=
  assumpPref_tyCastCtx _ ⟨assumptionPrefix_zero Γ, hD⟩

/-- Weaken into a new `.letBinding A v` at position 0. -/
def wkLetAtZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A v : Expr Nat}
    (D : TyP E n Γ e T) :
    TyP E n (.letBinding A v :: Γ) (lift 0 1 e) (lift 0 1 T) :=
  tyCastCtx (insertAt_zero (.letBinding A v) Γ)
    (TyP.wk E n Γ e T (.letBinding A v) 0 D)

theorem assumpPref_wkLetAtZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A v : Expr Nat} {D : TyP E n Γ e T} (hD : D.AssumpPref) :
    (wkLetAtZero (A := A) (v := v) D).AssumpPref :=
  assumpPref_tyCastCtx _ ⟨assumptionPrefix_zero Γ, hD⟩

theorem assumpPref_instEnd {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S v : Expr Nat} {u : Level}
    {hB : TyP E n (.assumption A :: Γ) B S} {hv : TyP E n Γ v A}
    {hA : TyP E n Γ A (.sort u)}
    (hBP : hB.AssumpPref) (hvP : hv.AssumpPref) (hAP : hA.AssumpPref) :
    (instEnd hB hv hA).AssumpPref :=
  assumpPref_tyCast _ _
    ⟨assumptionPrefix_zero (.assumption A :: Γ),
      hBP, assumpPref_castLift0 hvP, assumpPref_sortLift0 hAP⟩

theorem assumpPref_letSub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body B value : Expr Nat} {u : Level}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    {hv : TyP E n Γ value A} {hA : TyP E n Γ A (.sort u)}
    (hbP : hb.AssumpPref) (hvP : hv.AssumpPref) (hAP : hA.AssumpPref) :
    (letSub hb hv hA).AssumpPref :=
  assumpPref_tyCast _ _
    ⟨assumptionPrefix_zero (.letBinding A value :: Γ),
      hbP, assumpPref_castLift0 hvP, assumpPref_sortLift0 hAP⟩

theorem assumpPref_pushBodyEsub {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {A₀ b₀ B₀ t repl : Expr Nat} {j : Nat} {uE : Level}
    {hbody : TyP E n (.assumption A₀ :: Γ₀) b₀ B₀}
    (hget : Γ₀[j]? = some (.assumption t))
    {hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t)}
    {hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE)}
    {A body : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) b₀ = body)
    (hj : AssumptionPrefix Γ₀ j)
    (hbP : hbody.AssumpPref) (hvP : hv.AssumpPref) (hvTP : hvT.AssumpPref) :
    (pushBodyEsub hbody hget hv hvT hAe hBe).AssumpPref := by
  unfold pushBodyEsub
  refine assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ ⟨?_, hbP, ?_, ?_⟩)
  · exact assumptionPrefix_succ_assumption A₀ Γ₀ j hj
  · exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
      ⟨assumptionPrefix_zero (substRemove repl j Γ₀), hvP⟩)
  · exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
      ⟨assumptionPrefix_zero (substRemove repl j Γ₀), hvTP⟩)

/-- Q7 `letSub`-normalised translation of `HasTyT.letE` at `j = 0`:
    discharges `.letBinding A value` at `0` immediately via `letSub`. -/
def trLetNorm {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B) :
    TyP E n Γ (instantiate0 value body) (instantiate0 value B) :=
  letSub hb hv hA

/-- Q7 surface `TyP.letE` translation of `HasTyT.letE`: uses `letSub` at `j = 0`
    on `hb.reg.2` for the ascribed type's sort-typing `hT`. -/
def trLetE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B) :
    TyP E n Γ (.letE A value body) (instantiate0 value B) :=
  TyP.letE E n Γ A u value B body hb.reg.1 hA hv hb (letSub hb.reg.2 hv hA)

/-- Q7 translation of `ConvT.zeta`: connects `trLetE` and `trLetNorm` at `j = 0`. -/
def trZeta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B) :
    CvP E n Γ (.letE A value body) (instantiate0 value body) (instantiate0 value B) :=
  CvP.zeta E n Γ A value body B u hA hv hb (trLetE hA hv hb) (trLetNorm hA hv hb)

/-- Q7 Obligation 2 (normalised form): `trLetNorm` preserves `TyP.AssumpPref`. -/
theorem assumpPref_trLetNorm {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    (hAP : hA.AssumpPref) (hvP : hv.AssumpPref) (hbP : hb.AssumpPref) :
    (trLetNorm hA hv hb).AssumpPref :=
  assumpPref_letSub hbP hvP hAP

/-- Q7 Obligation 2 (surface `TyP.letE` form): `trLetE` preserves `TyP.AssumpPref`. -/
theorem assumpPref_trLetE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    (hAP : hA.AssumpPref) (hvP : hv.AssumpPref) (hbP : hb.AssumpPref) :
    (trLetE hA hv hb).AssumpPref :=
  ⟨hAP, hvP, hbP, assumpPref_letSub (assumpPref_reg hbP) hvP hAP⟩

/-- Q7 Obligation 2 (`ConvT.zeta`): `trZeta` preserves `CvP.AssumpPref`. -/
theorem assumpPref_trZeta {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    (hAP : hA.AssumpPref) (hvP : hv.AssumpPref) (hbP : hb.AssumpPref) :
    (trZeta hA hv hb).AssumpPref :=
  ⟨hAP, hvP, hbP, assumpPref_trLetE hAP hvP hbP, assumpPref_trLetNorm hAP hvP hbP⟩

/-- `trLetNorm` and `trLetE` have identical erasures at every `σ, ρ`. -/
theorem trLetNorm_eps_eq_trLetE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (σ : Level → Level) (ρ : List Disp) :
    (trLetNorm hA hv hb).eps σ ρ = (trLetE hA hv hb).eps σ ρ :=
  letSub_eps_eq_letE hA hv hb (letSub hb.reg.2 hv hA) σ ρ

/-- Instance A under Option L-inline-at-0: `letSub`-normalising `betaLetBody`'s
    `TyP.letE` head at `j = 0` before `instEnd` descends yields a derivation
    whose `instEnd` at `j = 0` satisfies `TyP.AssumpPref` and never crosses
    `.letBinding`. -/
theorem assumpPref_instEnd_betaLetBody_norm (E : ResolvedEnv) (n : Nat) :
    (instEnd
      (trLetNorm
        (TyP.sort E n [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]
          (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
        (TyP.bvar E n [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]
          1 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
          (TyP.sort E n [.assumption (.sort (.succ .zero)), .assumption (.sort (.succ .zero))]
            (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
        (esubZetaPreNode E n).dl)
      (TyP.sort E n [.assumption (.sort (.succ .zero))] .zero (.succ .zero) (eqN_refl _))
      (TyP.sort E n [.assumption (.sort (.succ .zero))]
        (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))).AssumpPref := by
  refine assumpPref_instEnd ?_ trivial trivial
  exact assumpPref_trLetNorm trivial trivial trivial

/-- Instance B under Option L-inline-at-0: `letSub`-normalising `betaLetReduct`'s
    `TyP.letE` head at `j = 0` before `wkAtZero` descends yields a derivation
    whose `wkAtZero` at `c = 0` satisfies `TyP.AssumpPref` and never crosses
    `.letBinding`. -/
theorem assumpPref_wkAtZero_betaLetReduct_norm (E : ResolvedEnv) (n : Nat) :
    (wkAtZero (A := .sort (.succ .zero))
      (trLetNorm
        (TyP.sort E n [.assumption (.sort (.succ .zero))]
          (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
        (TyP.bvar E n [.assumption (.sort (.succ .zero))]
          0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
          (TyP.sort E n [.assumption (.sort (.succ .zero))]
            (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)))
        (zetaLetNode E n).dl)).AssumpPref := by
  refine assumpPref_wkAtZero ?_
  exact assumpPref_trLetNorm trivial trivial trivial

/-! ## §3 Obligation 1: Instance 3 (`ConvT.letE`) under Option L-inline-at-0 -/

/-- Left `letSub`-normalised endpoint of `ConvT.letE` at `j = 0`. -/
def letEndL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb_l : TyP E n (.letBinding A v :: Γ) b B) :
    TyP E n Γ (instantiate0 v b) (instantiate0 v B) :=
  trLetNorm hA.dl hv.dl hb_l

/-- Left surface `.letE` endpoint of `ConvT.letE`. -/
def letSurfL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb_l : TyP E n (.letBinding A v :: Γ) b B) :
    TyP E n Γ (.letE A v b) (instantiate0 v B) :=
  trLetE hA.dl hv.dl hb_l

/-- Right `letSub`-normalised endpoint of `ConvT.letE` at `j = 0`, retyped to
    `instantiate0 v B` along `hcongr_symm` without any let-binding `cctx`. -/
def letEndR {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b' B : Expr Nat} {u w : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb_r' : TyP E n (.letBinding A' v' :: Γ) b' B)
    (hcongr_symm : CvP E n Γ (instantiate0 v' B) (instantiate0 v B) (.sort w)) :
    TyP E n Γ (instantiate0 v' b') (instantiate0 v B) :=
  TyP.conv E n Γ (instantiate0 v' b') (instantiate0 v' B) (instantiate0 v B) w
    (trLetNorm hA.dr (TyP.conv E n Γ v' A A' u hv.dr hA) hb_r')
    hcongr_symm

/-- Right surface `.letE` endpoint of `ConvT.letE`, retyped to `instantiate0 v B`
    along `hcongr_symm` without any let-binding `cctx`. -/
def letSurfR {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b' B : Expr Nat} {u w : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb_r' : TyP E n (.letBinding A' v' :: Γ) b' B)
    (hcongr_symm : CvP E n Γ (instantiate0 v' B) (instantiate0 v B) (.sort w)) :
    TyP E n Γ (.letE A' v' b') (instantiate0 v B) :=
  TyP.conv E n Γ (.letE A' v' b') (instantiate0 v' B) (instantiate0 v B) w
    (trLetE hA.dr (TyP.conv E n Γ v' A A' u hv.dr hA) hb_r')
    hcongr_symm

theorem letEndL_eps_eq_letSurfL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb_l : TyP E n (.letBinding A v :: Γ) b B)
    (σ : Level → Level) (ρ : List Disp) :
    (letEndL hA hv hb_l).eps σ ρ = (letSurfL hA hv hb_l).eps σ ρ :=
  trLetNorm_eps_eq_trLetE hA.dl hv.dl hb_l σ ρ

theorem letEndR_eps_eq_letSurfR {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b' B : Expr Nat} {u w : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb_r' : TyP E n (.letBinding A' v' :: Γ) b' B)
    (hcongr_symm : CvP E n Γ (instantiate0 v' B) (instantiate0 v B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (letEndR hA hv hb_r' hcongr_symm).eps σ ρ =
      (letSurfR hA hv hb_r' hcongr_symm).eps σ ρ :=
  trLetNorm_eps_eq_trLetE hA.dr (TyP.conv E n Γ v' A A' u hv.dr hA) hb_r' σ ρ

theorem assumpPref_letEndL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b B : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb_l : TyP E n (.letBinding A v :: Γ) b B}
    (hAP : hA.AssumpPref) (hvP : hv.AssumpPref) (hblP : hb_l.AssumpPref) :
    (letEndL hA hv hb_l).AssumpPref :=
  assumpPref_trLetNorm (assumpPref_dl hAP) (assumpPref_dl hvP) hblP

theorem assumpPref_letSurfL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b B : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb_l : TyP E n (.letBinding A v :: Γ) b B}
    (hAP : hA.AssumpPref) (hvP : hv.AssumpPref) (hblP : hb_l.AssumpPref) :
    (letSurfL hA hv hb_l).AssumpPref :=
  assumpPref_trLetE (assumpPref_dl hAP) (assumpPref_dl hvP) hblP

theorem assumpPref_letEndR {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b' B : Expr Nat} {u w : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb_r' : TyP E n (.letBinding A' v' :: Γ) b' B}
    {hcongr_symm : CvP E n Γ (instantiate0 v' B) (instantiate0 v B) (.sort w)}
    (hAP : hA.AssumpPref) (hvP : hv.AssumpPref) (hbrP : hb_r'.AssumpPref)
    (hcP : hcongr_symm.AssumpPref) :
    (letEndR hA hv hb_r' hcongr_symm).AssumpPref :=
  ⟨assumpPref_trLetNorm (assumpPref_dr hAP) ⟨assumpPref_dr hvP, hAP⟩ hbrP, hcP⟩

theorem assumpPref_letSurfR {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b' B : Expr Nat} {u w : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb_r' : TyP E n (.letBinding A' v' :: Γ) b' B}
    {hcongr_symm : CvP E n Γ (instantiate0 v' B) (instantiate0 v B) (.sort w)}
    (hAP : hA.AssumpPref) (hvP : hv.AssumpPref) (hbrP : hb_r'.AssumpPref)
    (hcP : hcongr_symm.AssumpPref) :
    (letSurfR hA hv hb_r' hcongr_symm).AssumpPref :=
  ⟨assumpPref_trLetE (assumpPref_dr hAP) ⟨assumpPref_dr hvP, hAP⟩ hbrP, hcP⟩

/-- Option L-inline-at-0 decomposition of `ConvT.letE`: both endpoints are
    `letSub`-normalised at `0` via `trZeta`, connected in `Γ` by the `j = 0`
    substituted body conversion `hb_sub` and `CvP.fsub` on `v ≡ v' : A`.
    No let-binding `cctx` is used anywhere. -/
def cvpLetDecomp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u w : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb_l : TyP E n (.letBinding A v :: Γ) b B)
    (hb_r' : TyP E n (.letBinding A' v' :: Γ) b' B)
    (hb_assump : TyP E n (.assumption A :: Γ) b' B)
    (hb_sub : CvP E n Γ (instantiate0 v b) (instantiate0 v b') (instantiate0 v B))
    (hcongr_symm : CvP E n Γ (instantiate0 v' B) (instantiate0 v B) (.sort w)) :
    CvP E n Γ (.letE A v b) (.letE A' v' b') (instantiate0 v B) :=
  let stepL := trZeta hA.dl hv.dl hb_l
  let endR := letEndR hA hv hb_r' hcongr_symm
  let surfR := letSurfR hA hv hb_r' hcongr_symm
  let stepFsub := CvP.fsub E n Γ A b' B v v' u hb_assump hA.dl hv hb_sub.dr endR
  let stepMid := CvP.trans E n Γ (instantiate0 v b) (instantiate0 v b') (instantiate0 v' b')
    (instantiate0 v B) hb_sub stepFsub hb_sub.dl endR
  let stepL2 := CvP.trans E n Γ (.letE A v b) (instantiate0 v b) (instantiate0 v' b')
    (instantiate0 v B) stepL stepMid stepL.dl endR
  let hv_rA' := TyP.conv E n Γ v' A A' u hv.dr hA
  let zetaR := trZeta hA.dr hv_rA' hb_r'
  let zetaR_conv := CvP.tyConv E n Γ (.letE A' v' b') (instantiate0 v' b')
    (instantiate0 v' B) (instantiate0 v B) w zetaR hcongr_symm surfR endR
  let stepR := CvP.symm E n Γ (.letE A' v' b') (instantiate0 v' b') (instantiate0 v B)
    zetaR_conv endR surfR
  CvP.trans E n Γ (.letE A v b) (instantiate0 v' b') (.letE A' v' b')
    (instantiate0 v B) stepL2 stepR stepL.dl surfR

/-- `cvpLetDecomp` satisfies `CvP.AssumpPref`: every transport in the
    decomposition (`letSub` at `0`) satisfies `AssumptionPrefix`. -/
theorem assumpPref_cvpLetDecomp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u w : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {hb_l : TyP E n (.letBinding A v :: Γ) b B}
    {hb_r' : TyP E n (.letBinding A' v' :: Γ) b' B}
    {hb_assump : TyP E n (.assumption A :: Γ) b' B}
    {hb_sub : CvP E n Γ (instantiate0 v b) (instantiate0 v b') (instantiate0 v B)}
    {hcongr_symm : CvP E n Γ (instantiate0 v' B) (instantiate0 v B) (.sort w)}
    (hAP : hA.AssumpPref) (hvP : hv.AssumpPref) (hblP : hb_l.AssumpPref)
    (hbrP : hb_r'.AssumpPref) (hbaP : hb_assump.AssumpPref)
    (hbsP : hb_sub.AssumpPref) (hcP : hcongr_symm.AssumpPref) :
    (cvpLetDecomp hA hv hb_l hb_r' hb_assump hb_sub hcongr_symm).AssumpPref := by
  have hstepL : (trZeta hA.dl hv.dl hb_l).AssumpPref :=
    assumpPref_trZeta (assumpPref_dl hAP) (assumpPref_dl hvP) hblP
  have hendR : (letEndR hA hv hb_r' hcongr_symm).AssumpPref :=
    assumpPref_letEndR hAP hvP hbrP hcP
  have hsurfR : (letSurfR hA hv hb_r' hcongr_symm).AssumpPref :=
    assumpPref_letSurfR hAP hvP hbrP hcP
  have hFsub : (CvP.fsub E n Γ A b' B v v' u hb_assump hA.dl hv hb_sub.dr
      (letEndR hA hv hb_r' hcongr_symm)).AssumpPref :=
    ⟨hbaP, assumpPref_dl hAP, hvP, assumpPref_dr hbsP, hendR⟩
  have hzetaR : (trZeta hA.dr (TyP.conv E n Γ v' A A' u hv.dr hA) hb_r').AssumpPref :=
    assumpPref_trZeta (assumpPref_dr hAP) ⟨assumpPref_dr hvP, hAP⟩ hbrP
  unfold cvpLetDecomp
  dsimp only [CvP.AssumpPref]
  exact ⟨⟨hstepL, ⟨hbsP, hFsub, assumpPref_dl hbsP, hendR⟩, assumpPref_dl hstepL, hendR⟩,
    ⟨⟨hzetaR, hcP, hsurfR, hendR⟩, hendR, hsurfR⟩,
    assumpPref_dl hstepL, hsurfR⟩

/-! ## §4 `ES` arms for `zeta`, `letE`, and spine-aligned `zetaLocal` -/

/-- `ES` for `CvP.zeta`: combines `zeta_dl` (`RcicSynClause.lean:159`) and
    `zeta_dr` (`RcicSynLetSub.lean:68`) via `es_zeta` (`RcicSynES.lean:477`). -/
theorem es_of_below_zeta (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.zeta E n Γ A value body B u hA hv hb dl dr))) :
    ES tbl σ ρ (CvP.zeta E n Γ A value body B u hA hv hb dl dr) :=
  es_zeta hA hv hb dl dr
    (zeta_dl Aw tbl hA hv hb dl dr σ ρ hρ Bel)
    (zeta_dr Aw tbl hA hv hb dl dr σ ρ hρ Bel)

/-- The body conversion `hb` of `CvP.letE` under the let-clause disposition
    `dispFor_letClause hρ hA.dl hv.dl`. -/
theorem letE_body_es (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr))) :
    ConvMod (EStep tbl) LvlEq
      (match hv.dl.eps σ ρ with
        | .star => hb.dl.eps σ (.drop :: ρ)
        | ev => hb.dl.eps σ (.inline ev :: ρ))
      (match hv.dl.eps σ ρ with
        | .star => hb.dr.eps σ (.drop :: ρ)
        | ev => hb.dr.eps σ (.inline ev :: ρ)) := by
  let hnode := CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hρ_let := dispFor_letClause hρ hA.dl hv.dl
  have hes := Bel.es hb σ
    ((match hv.dl.eps σ ρ with
      | .star => .drop
      | ev => .inline ev) :: ρ)
    hρ_let (lex_of_dm (dmStep_cv_below Aw hnode ht hb hwb))
  cases hve : hv.dl.eps σ ρ <;>
    (simp only [hve] at hes ⊢; exact hes)

/-- `ES` for `CvP.letE`: combines `letE_dl`, `letE_body_es`, and the right
    endpoint's coherence against the let-substituted body. -/
theorem es_of_below_letE_of_dr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)))
    (hR : ConvMod (EStep tbl) LvlEq
      (match hv.dl.eps σ ρ with
        | .star => hb.dr.eps σ (.drop :: ρ)
        | ev => hb.dr.eps σ (.inline ev :: ρ))
      (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) :=
  es_letE hA hv hb dl dr
    (letE_body_es Aw tbl hA hv hb dl dr σ ρ hρ Bel)
    (letE_dl Aw tbl hA hv hb dl dr σ ρ hρ Bel)
    hR

/-- `zetaLocal`'s right endpoint `dr` and premise `hv` both type `v` at `A`
    and sit strictly under the `zetaLocal` node, so `CL(hv, dr)` comes from `Bel`. -/
theorem zetaLocal_dr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.zetaLocal E n Γ i A v hval hty hv dl dr))) :
    ConvMod (EStep tbl) LvlEq (hv.eps σ ρ) (dr.eps σ ρ) := by
  let hnode := CvP.zetaLocal E n Γ i A v hval hty hv dl dr
  have ht : hnode.isTransport = false := rfl
  have hwv : hv.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  simpa only [CL] using cl_under Aw tbl hnode ht Bel hv dr σ ρ hρ hwv hwr

/-- `ES` for `CvP.zetaLocal` from `Bel` once `dl.eps σ ρ` is coherent with `hv.eps σ ρ`. -/
theorem es_of_below_zetaLocal_of_lhs (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.zetaLocal E n Γ i A v hval hty hv dl dr)))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hv.eps σ ρ)) :
    ES tbl σ ρ (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) :=
  es_zetaLocal hval hty hv dl dr
    (hL.trans (zetaLocal_dr Aw tbl hval hty hv dl dr σ ρ hρ Bel))

/-- At `i = 0` under `.drop :: ρ₀` (from `DispFor.letDrop` where `hv₀.eps σ ρ₀ = .star`),
    a spine-aligned `zetaLocal` with `hv = wkLetAtZero hv₀` has
    `hv.eps σ (.drop :: ρ₀) = .star`, so `ES` holds with zero context-spine `CL` calls. -/
theorem es_of_below_zetaLocal_zero_drop (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A₀ v₀ : Expr Nat} {u : Level}
    (hv₀ : TyP E n Γ₀ v₀ A₀)
    (hval : lookupValue (.letBinding A₀ v₀ :: Γ₀) 0 = some (lift 0 1 v₀))
    (hty : lookupType (.letBinding A₀ v₀ :: Γ₀) 0 = some (lift 0 1 A₀))
    (hA : TyP E n (.letBinding A₀ v₀ :: Γ₀) (lift 0 1 A₀) (.sort u))
    (dr : TyP E n (.letBinding A₀ v₀ :: Γ₀) (lift 0 1 v₀) (lift 0 1 A₀))
    (σ : Level → Level) (ρ₀ : List Disp)
    (hρ : DispFor σ E n (.letBinding A₀ v₀ :: Γ₀) (.drop :: ρ₀))
    (hv_star : hv₀.eps σ ρ₀ = .star)
    (Bel : Below Aw tbl
      (cvMeas Aw
        (CvP.zetaLocal E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) (lift 0 1 v₀)
          hval hty (wkLetAtZero (A := A₀) (v := v₀) hv₀)
          (TyP.bvar E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) u hty hA) dr))) :
    ES tbl σ (.drop :: ρ₀)
      (CvP.zetaLocal E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) (lift 0 1 v₀)
        hval hty (wkLetAtZero (A := A₀) (v := v₀) hv₀)
        (TyP.bvar E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) u hty hA) dr) := by
  refine es_of_below_zetaLocal_of_lhs Aw tbl hval hty
    (wkLetAtZero (A := A₀) (v := v₀) hv₀)
    (TyP.bvar E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) u hty hA)
    dr σ (.drop :: ρ₀) hρ Bel ?_
  have hwk : (wkLetAtZero (A := A₀) (v := v₀) hv₀).eps σ (.drop :: ρ₀) = .star := by
    rw [wkLetAtZero, eps_tyCastCtx,
      eps_wk_not_keep (hk := Or.inr (Or.inl (disp_drop_zero ρ₀))),
      removeAt_zero, hv_star]
  have hdl : (TyP.bvar E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) u hty hA).eps σ (.drop :: ρ₀) = .star := by
    simp only [TyP.eps, resolve]
    cases levelIsZero (σ u) <;> rfl
  rw [hdl, hwk]
  exact .refl _

/-- At `i = 0` under `.inline (hv₀.eps σ ρ₀) :: ρ₀` (from `DispFor.letInline`)
    on a relevant variable (`levelIsZero (σ u) = false`), a spine-aligned
    `zetaLocal` with `hv = wkLetAtZero hv₀` has
    `dl.eps = hv₀.eps σ ρ₀ = hv.eps` definitionally, so `ES` holds with zero
    context-spine `CL` calls. -/
theorem es_of_below_zetaLocal_zero_inline (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A₀ v₀ : Expr Nat} {u : Level}
    (hv₀ : TyP E n Γ₀ v₀ A₀)
    (hval : lookupValue (.letBinding A₀ v₀ :: Γ₀) 0 = some (lift 0 1 v₀))
    (hty : lookupType (.letBinding A₀ v₀ :: Γ₀) 0 = some (lift 0 1 A₀))
    (hA : TyP E n (.letBinding A₀ v₀ :: Γ₀) (lift 0 1 A₀) (.sort u))
    (dr : TyP E n (.letBinding A₀ v₀ :: Γ₀) (lift 0 1 v₀) (lift 0 1 A₀))
    (σ : Level → Level) (ρ₀ : List Disp)
    (hρ : DispFor σ E n (.letBinding A₀ v₀ :: Γ₀) (.inline (hv₀.eps σ ρ₀) :: ρ₀))
    (hu : levelIsZero (σ u) = false)
    (Bel : Below Aw tbl
      (cvMeas Aw
        (CvP.zetaLocal E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) (lift 0 1 v₀)
          hval hty (wkLetAtZero (A := A₀) (v := v₀) hv₀)
          (TyP.bvar E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) u hty hA) dr))) :
    ES tbl σ (.inline (hv₀.eps σ ρ₀) :: ρ₀)
      (CvP.zetaLocal E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) (lift 0 1 v₀)
        hval hty (wkLetAtZero (A := A₀) (v := v₀) hv₀)
        (TyP.bvar E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) u hty hA) dr) := by
  refine es_of_below_zetaLocal_of_lhs Aw tbl hval hty
    (wkLetAtZero (A := A₀) (v := v₀) hv₀)
    (TyP.bvar E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) u hty hA)
    dr σ (.inline (hv₀.eps σ ρ₀) :: ρ₀) hρ Bel ?_
  have hwk : (wkLetAtZero (A := A₀) (v := v₀) hv₀).eps σ (.inline (hv₀.eps σ ρ₀) :: ρ₀) =
      hv₀.eps σ ρ₀ := by
    rw [wkLetAtZero, eps_tyCastCtx,
      eps_wk_not_keep (hk := Or.inr (Or.inr ⟨hv₀.eps σ ρ₀, by simp [List.get?_cons_zero]⟩)),
      removeAt_zero]
  have hdl : (TyP.bvar E n (.letBinding A₀ v₀ :: Γ₀) 0 (lift 0 1 A₀) u hty hA).eps σ
      (.inline (hv₀.eps σ ρ₀) :: ρ₀) = hv₀.eps σ ρ₀ := by
    simp only [TyP.eps, hu, resolve]
  rw [hdl, hwk]
  exact .refl _

/-! ## §5 `ES` arms for `pi`, `lam`, `app`, `beta`, `delta`, and `iota` from `Below` -/

/-- The domain conversion `hA` of `CvP.pi` under `Bel`. -/
theorem pi_dom_es (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    ConvMod (EStep tbl) LvlEq (hA.dl.eps σ ρ) (hA.dr.eps σ ρ) := by
  let hnode := CvP.pi E n Γ A A' B B' u v hA hB dl dr
  have ht : hnode.isTransport = false := rfl
  have hwA : hA.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact Bel.es hA σ ρ hρ (lex_of_dm (dmStep_cv_below Aw hnode ht hA hwA))

/-- The codomain conversion `hB` of `CvP.pi` under `dispFor_binderDisp hρ hA.dl` and `Bel`. -/
theorem pi_cod_es (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    ConvMod (EStep tbl) LvlEq
      (hB.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))
      (hB.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)) := by
  let hnode := CvP.pi E n Γ A A' B B' u v hA hB dl dr
  have ht : hnode.isTransport = false := rfl
  have hwB : hB.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact Bel.es hB σ (binderDisp (levelIsZero (σ u)) :: ρ)
    (dispFor_binderDisp hρ hA.dl)
    (lex_of_dm (dmStep_cv_below Aw hnode ht hB hwB))

/-- `ES` for `CvP.pi`: combines `pi_dl` (`RcicSynClause.lean:94`), `pi_dom_es`,
    `pi_cod_es`, and the right endpoint's coherence via `es_pi`. -/
theorem es_of_below_pi_of_dr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hTC : TableClosed tbl)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr)))
    (hR : ConvMod (EStep tbl) LvlEq
      (.pi (hA.dr.eps σ ρ) (piSlot (levelIsZero (σ u))
        (hB.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))))
      (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.pi E n Γ A A' B B' u v hA hB dl dr) := by
  have hLraw := pi_dl Aw tbl hA hB dl dr σ ρ hρ Bel
  have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (.pi (hA.dl.eps σ ρ) (piSlot (levelIsZero (σ u))
        (hB.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)))) := by
    cases hzu : levelIsZero (σ u) <;>
      simpa only [hzu, binderDisp, piSlot] using hLraw
  have hBd : ConvMod (EStep tbl) LvlEq
      (piSlot (levelIsZero (σ u)) (hB.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)))
      (piSlot (levelIsZero (σ u)) (hB.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))) :=
    convMod_piSlot hTC _ (pi_cod_es Aw tbl hA hB dl dr σ ρ hρ Bel)
  exact es_pi hA hB dl dr
    (pi_dom_es Aw tbl hA hB dl dr σ ρ hρ Bel)
    hBd hL hR

/-- The body conversion `hb` of `CvP.lam` under `dispFor_binderDisp hρ hA.dl` and `Bel`. -/
theorem lam_body_es (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr))) :
    ConvMod (EStep tbl) LvlEq
      (hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))
      (hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)) := by
  let hnode := CvP.lam E n Γ A A' b b' B u hA hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact Bel.es hb σ (binderDisp (levelIsZero (σ u)) :: ρ)
    (dispFor_binderDisp hρ hA.dl)
    (lex_of_dm (dmStep_cv_below Aw hnode ht hb hwb))

/-- `ES` for `CvP.lam` on a proof domain (`levelIsZero (σ u) = true`). -/
theorem es_of_below_lam_drop (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = true)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr)))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hb.dl.eps σ (.drop :: ρ)))
    (hR : ConvMod (EStep tbl) LvlEq (hb.dr.eps σ (.drop :: ρ)) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  have hbody := lam_body_es Aw tbl hA hb dl dr σ ρ hρ Bel
  rw [hu, binderDisp_drop] at hbody
  exact es_lam_drop hA hb dl dr hbody hL hR

/-- `ES` for `CvP.lam` on a relevant domain (`levelIsZero (σ u) = false`). -/
theorem es_of_below_lam_keep (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B))
    (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = false)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr)))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.lam (hb.dl.eps σ (.keep :: ρ))))
    (hR : ConvMod (EStep tbl) LvlEq (.lam (hb.dr.eps σ (.keep :: ρ))) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  have hbody := lam_body_es Aw tbl hA hb dl dr σ ρ hρ Bel
  rw [hu, binderDisp_keep] at hbody
  exact es_lam_keep hA hb dl dr hbody hL hR

/-- The function conversion `h1` of `CvP.app` under `Bel`. -/
theorem app_fun_es (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr))) :
    ConvMod (EStep tbl) LvlEq (h1.dl.eps σ ρ) (h1.dr.eps σ ρ) := by
  let hnode := CvP.app E n Γ f g a b A B h1 h2 dl dr
  have ht : hnode.isTransport = false := rfl
  have hw1 : h1.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact Bel.es h1 σ ρ hρ (lex_of_dm (dmStep_cv_below Aw hnode ht h1 hw1))

/-- The argument conversion `h2` of `CvP.app` under `Bel`. -/
theorem app_arg_es (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr))) :
    ConvMod (EStep tbl) LvlEq (h2.dl.eps σ ρ) (h2.dr.eps σ ρ) := by
  let hnode := CvP.app E n Γ f g a b A B h1 h2 dl dr
  have ht : hnode.isTransport = false := rfl
  have hw2 : h2.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact Bel.es h2 σ ρ hρ (lex_of_dm (dmStep_cv_below Aw hnode ht h2 hw2))

/-- `ES` for `CvP.app` when neither `h1.dl.eps` nor `h2.dl.eps` is `★`:
    combines `app_dl` (`RcicSynClause.lean:62`), `app_fun_es`, `app_arg_es`,
    and the right endpoint's coherence via `es_app`. -/
theorem es_of_below_app_of_dr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hf_ne : h1.dl.eps σ ρ ≠ .star) (ha_ne : h2.dl.eps σ ρ ≠ .star)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr)))
    (hR : ConvMod (EStep tbl) LvlEq (.app (h1.dr.eps σ ρ) (h2.dr.eps σ ρ)) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.app E n Γ f g a b A B h1 h2 dl dr) := by
  have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (appClause (h1.dl.eps σ ρ) (h2.dl.eps σ ρ)) :=
    app_dl Aw tbl h1 h2 dl dr σ ρ hρ Bel
  rw [appClause_app hf_ne ha_ne] at hL
  exact es_app h1 h2 dl dr
    (app_fun_es Aw tbl h1 h2 dl dr σ ρ hρ Bel)
    (app_arg_es Aw tbl h1 h2 dl dr σ ρ hρ Bel)
    hL hR

/-- `ES` for `CvP.app` when `h2.dl.eps = ★` (proof argument deleted by `appClause`):
    combines `app_dl`, `app_fun_es`, and the right endpoint's coherence via `es_app_star`. -/
theorem es_of_below_app_star_of_dr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (ha_star : h2.dl.eps σ ρ = .star)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr)))
    (hR : ConvMod (EStep tbl) LvlEq (h1.dr.eps σ ρ) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.app E n Γ f g a b A B h1 h2 dl dr) := by
  have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (appClause (h1.dl.eps σ ρ) (h2.dl.eps σ ρ)) :=
    app_dl Aw tbl h1 h2 dl dr σ ρ hρ Bel
  rw [ha_star, appClause_right_star] at hL
  exact es_app_star h1 h2 dl dr
    (app_fun_es Aw tbl h1 h2 dl dr σ ρ hρ Bel)
    hL hR

/-- `ES` for `CvP.beta` on a proof domain (`levelIsZero (σ u) = true`):
    combines `beta_dr_drop` (`RcicSynInstEnd.lean:184`) with `es_beta_drop`. -/
theorem es_of_below_beta_drop (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = true)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr)))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hbody.eps σ (.drop :: ρ))) :
    ES tbl σ ρ (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) :=
  es_beta_drop hA hbody harg dl dr hL
    (beta_dr_drop Aw tbl hA hbody harg dl dr σ ρ hρ hu Bel)

/-- `ES` for `CvP.beta` on a relevant domain (`levelIsZero (σ u) = false`):
    combines `beta_dr_keep` (`RcicSynInstEnd.lean:210`) with `es_beta_rel`. -/
theorem es_of_below_beta_keep (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = false)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr)))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (.app (.lam (hbody.eps σ (.keep :: ρ))) (harg.eps σ ρ))) :
    ES tbl σ ρ (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) :=
  es_beta_rel hA hbody harg dl dr hL
    (beta_dr_keep Aw tbl hA hbody harg dl dr σ ρ hρ hu Bel)

/-- `ES` for `CvP.delta`: combines `delta_dr` (`RcicSynClause.lean:216`) with
    `es_delta` (`RcicSynES.lean:499`) once the constant step and `hb` level-instantiation
    bridge are given. -/
theorem es_of_below_delta_of_lhs (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr)))
    {lhs rhs : ETm}
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) lhs)
    (hstep : EStep tbl lhs rhs)
    (hrhs : ConvMod (EStep tbl) LvlEq rhs (hb.eps σ ρ)) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) :=
  es_delta hres hbody htrp hlen hwf hb dl dr hL hstep
    (hrhs.trans (delta_dr Aw tbl hres hbody htrp hlen hwf hb dl dr σ ρ hρ Bel))

/-- `ES` for `CvP.iota`: combines `iota_dl` (`RcicSynClause.lean:189`) and
    `iota_dr` (`RcicSynClause.lean:202`) with `es_iota` (`RcicSynES.lean:514`). -/
theorem es_of_below_iota_of_step (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr)))
    {el er : ETm}
    (hl : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ) el)
    (hstep : EStep tbl el er)
    (hr : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)) :
    ES tbl σ ρ (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) :=
  es_iota h hlhs hrhs dl dr
    ((iota_dl Aw tbl h hlhs hrhs dl dr σ ρ hρ Bel).trans hl)
    hstep
    (hr.trans (iota_dr Aw tbl h hlhs hrhs dl dr σ ρ hρ Bel))

end Rcic.Syn

#print axioms Rcic.Syn.convT_substLet0_of_envWfT
#print axioms Rcic.Syn.hasTyT_letE_inline0_of_envWfT
#print axioms Rcic.Syn.convT_letE_inline0_of_envWfT
#print axioms Rcic.Syn.assumptionPrefix_succ_assumption
#print axioms Rcic.Syn.TyP.AssumpPref
#print axioms Rcic.Syn.CvP.AssumpPref
#print axioms Rcic.Syn.assumpPref_tyCast
#print axioms Rcic.Syn.assumpPref_tyCastCtx
#print axioms Rcic.Syn.assumpPref_cvCast
#print axioms Rcic.Syn.assumpPref_cvCastCtx
#print axioms Rcic.Syn.assumpPref_castLift0
#print axioms Rcic.Syn.assumpPref_sortLift0
#print axioms Rcic.Syn.assumpPref_dl
#print axioms Rcic.Syn.assumpPref_dr
#print axioms Rcic.Syn.assumpPref_reg
#print axioms Rcic.Syn.assumpPref_wkAtZero
#print axioms Rcic.Syn.wkLetAtZero
#print axioms Rcic.Syn.assumpPref_wkLetAtZero
#print axioms Rcic.Syn.assumpPref_instEnd
#print axioms Rcic.Syn.assumpPref_letSub
#print axioms Rcic.Syn.assumpPref_pushBodyEsub
#print axioms Rcic.Syn.trLetNorm
#print axioms Rcic.Syn.trLetE
#print axioms Rcic.Syn.trZeta
#print axioms Rcic.Syn.assumpPref_trLetNorm
#print axioms Rcic.Syn.assumpPref_trLetE
#print axioms Rcic.Syn.assumpPref_trZeta
#print axioms Rcic.Syn.trLetNorm_eps_eq_trLetE
#print axioms Rcic.Syn.assumpPref_instEnd_betaLetBody_norm
#print axioms Rcic.Syn.assumpPref_wkAtZero_betaLetReduct_norm
#print axioms Rcic.Syn.letEndL
#print axioms Rcic.Syn.letSurfL
#print axioms Rcic.Syn.letEndR
#print axioms Rcic.Syn.letSurfR
#print axioms Rcic.Syn.letEndL_eps_eq_letSurfL
#print axioms Rcic.Syn.letEndR_eps_eq_letSurfR
#print axioms Rcic.Syn.assumpPref_letEndL
#print axioms Rcic.Syn.assumpPref_letSurfL
#print axioms Rcic.Syn.assumpPref_letEndR
#print axioms Rcic.Syn.assumpPref_letSurfR
#print axioms Rcic.Syn.cvpLetDecomp
#print axioms Rcic.Syn.assumpPref_cvpLetDecomp
#print axioms Rcic.Syn.es_of_below_zeta
#print axioms Rcic.Syn.letE_body_es
#print axioms Rcic.Syn.es_of_below_letE_of_dr
#print axioms Rcic.Syn.zetaLocal_dr
#print axioms Rcic.Syn.es_of_below_zetaLocal_of_lhs
#print axioms Rcic.Syn.es_of_below_zetaLocal_zero_drop
#print axioms Rcic.Syn.es_of_below_zetaLocal_zero_inline
#print axioms Rcic.Syn.pi_dom_es
#print axioms Rcic.Syn.pi_cod_es
#print axioms Rcic.Syn.es_of_below_pi_of_dr
#print axioms Rcic.Syn.lam_body_es
#print axioms Rcic.Syn.es_of_below_lam_drop
#print axioms Rcic.Syn.es_of_below_lam_keep
#print axioms Rcic.Syn.app_fun_es
#print axioms Rcic.Syn.app_arg_es
#print axioms Rcic.Syn.es_of_below_app_of_dr
#print axioms Rcic.Syn.es_of_below_app_star_of_dr
#print axioms Rcic.Syn.es_of_below_beta_drop
#print axioms Rcic.Syn.es_of_below_beta_keep
#print axioms Rcic.Syn.es_of_below_delta_of_lhs
#print axioms Rcic.Syn.es_of_below_iota_of_step
