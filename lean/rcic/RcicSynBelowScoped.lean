import rcic.RcicSynAllBelow
import rcic.RcicSynSortPBit

/-!
# Step 4c-S1a: scoped mutual-pack interface and conditional extraction

Implements the interface approved in `research/rcic/sortrow/S1_BELOW_SCOPED.md`.
Every query carries native admission/context witnesses and inclusion in one
ambient environment. Its disposition is fixed by those witnesses. This module
does not construct `AllBelowScoped` or close native `hcoh`; `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- An admitted native context whose members belong to the fixed ambient environment. -/
structure ScopedCtx (Eₐ E : ResolvedEnv) (n : Nat) (Γ : LCtx) where
  env : EnvWfT E
  ext : EnvExt E Eₐ
  ctx : CtxWfT E n Γ

/-- The disposition of the actual native witnesses retained in the scope. -/
noncomputable def ScopedCtx.can {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) : List Disp :=
  (enrichCtxWfT_of_envWfT S.env S.ctx).disp σ

/-- Canonical scoped dispositions satisfy the existing homogeneous validity contract. -/
theorem ScopedCtx.canDispForHom {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (S : ScopedCtx Eₐ E n Γ) {σ : Level → Level} (hσ : LevelHom σ) :
    DispForHom σ E n Γ (S.can σ) :=
  dispForHom_of_ctxP hσ (enrichCtxWfT_of_envWfT S.env S.ctx)

/-- The six strict-below obligations, restricted to admitted scopes and canonical dispositions. -/
structure BelowScoped (Eₐ : ResolvedEnv) (Aw : Nat → Nat) (tbl : List CRule)
    (bound : List Nat × Nat) : Prop where
  es : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T), h.AssumpPref →
    ∀ (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (cvMeas Aw h) bound → ES tbl σ (S.can σ) h
  cl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂), D₁.AssumpPref → D₂.AssumpPref →
    ∀ (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (tyPairMeas Aw D₁ D₂) bound → CL tbl σ (S.can σ) D₁ D₂
  eut : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂), D₁.AssumpPref → D₂.AssumpPref →
    ∀ (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (tyPairMeas Aw D₁ D₂) bound → EUT tbl σ (S.can σ) D₁ D₂
  cts : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s)),
    h.AssumpPref → DX.AssumpPref → ScopedCtx Eₐ E n Γ →
    LexDM (cvTyMeas Aw h DX) bound → CTS h DX
  pb : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)), D.AssumpPref → DT.AssumpPref →
    ∀ (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (tyPairMeas Aw D DT) bound → PBit σ (S.can σ) D DT
  bitCoh : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v)),
    D₁.AssumpPref → D₂.AssumpPref →
    ∀ (_S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (tyPairMeas Aw D₁ D₂) bound → BitCoh σ D₁ D₂

/-- Scoped mutual-pack validity at every strict bound; no producer is asserted here. -/
def AllBelowScoped (Eₐ : ResolvedEnv) (Aw : Nat → Nat) (tbl : List CRule) : Prop :=
  ∀ bound : List Nat × Nat, BelowScoped Eₐ Aw tbl bound

variable {Eₐ E : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
  {n : Nat} {Γ : LCtx} {σ : Level → Level}

/-- Extract a guarded conversion query at its successor bound. -/
theorem es_of_allBelowScoped (hBel : AllBelowScoped Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {a b T : Expr Nat}
    (h : CvP E n Γ a b T) (hAP : h.AssumpPref) : ES tbl σ (S.can σ) h :=
  (hBel ((cvMeas Aw h).1, (cvMeas Aw h).2 + 1)).es h hAP S σ hσ
    (lexDM_succ_snd (cvMeas Aw h))

/-- Extract a guarded same-term erasure query at its successor bound. -/
theorem cl_of_allBelowScoped (hBel : AllBelowScoped Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) : CL tbl σ (S.can σ) D₁ D₂ :=
  (hBel ((tyPairMeas Aw D₁ D₂).1, (tyPairMeas Aw D₁ D₂).2 + 1)).cl
    D₁ D₂ h₁ h₂ S σ hσ (lexDM_succ_snd (tyPairMeas Aw D₁ D₂))

/-- Extract a guarded erased-type uniqueness query at its successor bound. -/
theorem eut_of_allBelowScoped (hBel : AllBelowScoped Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) : EUT tbl σ (S.can σ) D₁ D₂ :=
  (hBel ((tyPairMeas Aw D₁ D₂).1, (tyPairMeas Aw D₁ D₂).2 + 1)).eut
    D₁ D₂ h₁ h₂ S σ hσ (lexDM_succ_snd (tyPairMeas Aw D₁ D₂))

/-- Extract conversion-of-types sort preservation under the same native scope guard. -/
theorem cts_of_allBelowScoped (hBel : AllBelowScoped Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (hAP : h.AssumpPref) (hDX : DX.AssumpPref) : CTS h DX :=
  (hBel ((cvTyMeas Aw h DX).1, (cvTyMeas Aw h DX).2 + 1)).cts
    h DX hAP hDX S (lexDM_succ_snd (cvTyMeas Aw h DX))

/-- Extract a guarded propositional-bit query at its successor bound. -/
theorem pbit_of_allBelowScoped (hBel : AllBelowScoped Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    (hD : D.AssumpPref) (hDT : DT.AssumpPref) : PBit σ (S.can σ) D DT :=
  (hBel ((tyPairMeas Aw D DT).1, (tyPairMeas Aw D DT).2 + 1)).pb
    D DT hD hDT S σ hσ (lexDM_succ_snd (tyPairMeas Aw D DT))

/-- Extract guarded sort-bit coherence at its successor bound. -/
theorem bitCoh_of_allBelowScoped (hBel : AllBelowScoped Eₐ Aw tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) : BitCoh σ D₁ D₂ :=
  (hBel ((tyPairMeas Aw D₁ D₂).1, (tyPairMeas Aw D₁ D₂).2 + 1)).bitCoh
    D₁ D₂ h₁ h₂ S σ hσ (lexDM_succ_snd (tyPairMeas Aw D₁ D₂))

/-- Conditional sort coherence by the existing EUT-plus-two-CL composition.
All three queries use exactly the same native scope and canonical disposition. -/
theorem sortCoh_of_allBelowScoped (hBel : AllBelowScoped Eₐ Aw tbl) (hW : TableWF tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ) {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) : SortCoh σ D₁ D₂ :=
  sortCoh_of_eut_cl hW D₁ D₂ σ (S.can σ)
    (eut_of_allBelowScoped hBel S hσ D₁ D₂ h₁ h₂)
    (cl_of_allBelowScoped hBel S hσ D₁.reg.2
      (TyP.sort E n Γ u (.succ u) (eqN_refl _)) (assumpPref_reg h₁) trivial)
    (cl_of_allBelowScoped hBel S hσ D₂.reg.2
      (TyP.sort E n Γ v (.succ v) (eqN_refl _)) (assumpPref_reg h₂) trivial)

end Rcic.Syn
