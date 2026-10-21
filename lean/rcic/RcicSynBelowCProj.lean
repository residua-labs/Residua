import rcic.RcicSynSpineComb
import rcic.RcicSynBelowScopedPins

/-!
# 4c §8 — the conditional `CompleteCAt → AllBelowScoped` projection

Design: ChatGPT's approved S0
`research/rcic/sortrow/S0_BELOWC_ALLBELOW_ASSEMBLY.md`
(§8 "The exact projection `BelowC → AllBelowScoped`", on `main` via #7303).

**This layer is conditional.** No `CompleteCAt` producer exists yet — §10
keeps the producer, the six recursive `BelowC` closure steps and arbitrary
coverage open. What this module proves is only the projection half: *if* a
completed internal pack is supplied at every frame `p` and bound `B`, then
`AllBelowScoped` follows.

Each of the six public `BelowScoped` fields is filled individually: the public
input is packaged as a `QueryC` (carrying its own `ScopedCtx` `S` and the
original ambient frame), the pack is consulted at that query's own canonical
spine `C = enrichCtxWfT_of_envWfT S.env S.ctx`, own raw measure `m`, combined
point `k = combMeas Aw C m`, and successor combined bound
`Bq = (k.1, k.2 + 1)` via `lexDM_succ_snd`. There is **no** fixed-bound
`BelowC B → BelowScoped B` coercion: the public raw `< bound` hypothesis of
each field is dropped, because the internal combined `< Bq` obligation is a
different measure (`combMeas` includes the spine's atoms and weight).

`CompleteCAt` is parameterized by the pack's *bound key* so that the real and
mutant instances share one definition: the S0's pack is keyed by
`QueryC.combBound`. `allBelowScoped_of_completeC` is the §8 theorem;
`allBelowScoped_of_keyed` is the one mechanism; the §9 tooth
`rawComb_succ_tooth` pins that the raw successor bound of a real pair measure
admits the raw-keyed pack call while the combined-bound control refuses it at
`pbitWallCtxP` (atoms `[6]`, weight `6` vs raw atoms `[1,1]`, weight `2`).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The six public queries packaged as a finite tagged union (S0 §2). Each
    constructor carries exactly the public `BelowScoped` field inputs — the
    enriched witnesses, their `AssumpPref` fields, the `ScopedCtx` `S`
    (admitted environment + ambient inclusion + context) and, where the public
    conclusion uses one, `σ` with `LevelHom σ` (`cts` has no `σ`; its internal
    spine uses `id`) — plus `frame`, the original ambient frame the query's
    receipts index into (for a public query `frame = Γ`). The conclusion
    `Goal` is computed from the tag, never supplied by the caller. -/
inductive QueryC (Eₐ : ResolvedEnv) (Aw : Nat → Nat) (tbl : List CRule) : Type where
  | es {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      (h : CvP E n Γ a b T) (hAP : h.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ)
      (frame : LCtx) : QueryC Eₐ Aw tbl
  | cl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
      (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
      (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ)
      (frame : LCtx) : QueryC Eₐ Aw tbl
  | eut {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
      (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
      (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ)
      (frame : LCtx) : QueryC Eₐ Aw tbl
  | cts {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
      (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
      (hAP : h.AssumpPref) (hDX : DX.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (frame : LCtx) : QueryC Eₐ Aw tbl
  | pb {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
      (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
      (hD : D.AssumpPref) (hDT : DT.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ)
      (frame : LCtx) : QueryC Eₐ Aw tbl
  | bitCoh {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
      (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
      (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
      (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ)
      (frame : LCtx) : QueryC Eₐ Aw tbl

variable {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}

/-- The frame index `p` of the completed pack: the original ambient frame's
    length (S0 §2/§3). -/
def QueryC.frameLen : QueryC Eₐ Aw tbl → Nat
  | .es _ _ _ _ _ f => f.length
  | .cl _ _ _ _ _ _ _ f => f.length
  | .eut _ _ _ _ _ _ _ f => f.length
  | .cts _ _ _ _ _ f => f.length
  | .pb _ _ _ _ _ _ _ f => f.length
  | .bitCoh _ _ _ _ _ _ _ f => f.length

/-- The query's own raw public measure — the same `m` the public field
    signatures guard with `LexDM m bound` (`cvMeas`/`tyPairMeas`/`cvTyMeas`
    of the tag's inputs). Never identified with the combined measure (S0 §8). -/
def QueryC.rawMeasure : QueryC Eₐ Aw tbl → List Nat × Nat
  | .es h _ _ _ _ _ => cvMeas Aw h
  | .cl D₁ D₂ _ _ _ _ _ _ => tyPairMeas Aw D₁ D₂
  | .eut D₁ D₂ _ _ _ _ _ _ => tyPairMeas Aw D₁ D₂
  | .cts h DX _ _ _ _ => cvTyMeas Aw h DX
  | .pb D DT _ _ _ _ _ _ => tyPairMeas Aw D DT
  | .bitCoh D₁ D₂ _ _ _ _ _ _ => tyPairMeas Aw D₁ D₂

/-- The query's own canonical combined bound point:
    `combMeas Aw C m` at `C = enrichCtxWfT_of_envWfT S.env S.ctx` and
    `m = q.rawMeasure`. Each field's `C` is derived from that field's own
    `ScopedCtx`; no spine is shared or fixed across queries (S0 §8). -/
noncomputable def QueryC.combBound : QueryC Eₐ Aw tbl → List Nat × Nat
  | .es h _ S _ _ _ => combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (cvMeas Aw h)
  | .cl D₁ D₂ _ _ S _ _ _ =>
      combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyPairMeas Aw D₁ D₂)
  | .eut D₁ D₂ _ _ S _ _ _ =>
      combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyPairMeas Aw D₁ D₂)
  | .cts h DX _ _ S _ =>
      combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (cvTyMeas Aw h DX)
  | .pb D DT _ _ S _ _ _ =>
      combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyPairMeas Aw D DT)
  | .bitCoh D₁ D₂ _ _ S _ _ _ =>
      combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) (tyPairMeas Aw D₁ D₂)

/-- The conclusion of the query, computed from the tag (S0 §2): the public
    field's goal — `ES`/`CL`/`EUT`/`PBit` at the canonical disposition
    `ρ = S.can σ` of that field's own `ScopedCtx`; `CTS`/`BitCoh` carry no
    disposition argument. -/
noncomputable def QueryC.Goal : QueryC Eₐ Aw tbl → Prop
  | .es h _ S σ _ _ => ES tbl σ (S.can σ) h
  | .cl D₁ D₂ _ _ S σ _ _ => CL tbl σ (S.can σ) D₁ D₂
  | .eut D₁ D₂ _ _ S σ _ _ => EUT tbl σ (S.can σ) D₁ D₂
  | .cts h DX _ _ _ _ => CTS h DX
  | .pb D DT _ _ S σ _ _ => PBit σ (S.can σ) D DT
  | .bitCoh D₁ D₂ _ _ _ σ _ _ => BitCoh σ D₁ D₂

/-- The conditional `ReadyC` (S0 §2): the construction/provenance evidence the
    completed pack returns for a query — here, the canonical-disposition
    derivation `DispForC σ C ρ` at the query's own canonical spine
    `C = enrichCtxWfT_of_envWfT S.env S.ctx` and `ρ = S.can σ`
    (`cts`: `DispForC id`). It carries no `Goal` conclusion and no supplier
    for one. The producer (§10) is expected to extend this pack with the full
    evidence list: the original-frame receipt and root identity, the
    environment-origin `GroupStageAt` path, the `DispForPath` forest and the
    three slot-origin classes with their receipts. -/
noncomputable def ReadyC : QueryC Eₐ Aw tbl → Prop
  | .es _ _ S σ _ _ => DispForC σ (enrichCtxWfT_of_envWfT S.env S.ctx) (S.can σ)
  | .cl _ _ _ _ S σ _ _ => DispForC σ (enrichCtxWfT_of_envWfT S.env S.ctx) (S.can σ)
  | .eut _ _ _ _ S σ _ _ => DispForC σ (enrichCtxWfT_of_envWfT S.env S.ctx) (S.can σ)
  | .cts _ _ _ _ S _ => DispForC id (enrichCtxWfT_of_envWfT S.env S.ctx) (S.can id)
  | .pb _ _ _ _ S σ _ _ => DispForC σ (enrichCtxWfT_of_envWfT S.env S.ctx) (S.can σ)
  | .bitCoh _ _ _ _ S σ _ _ =>
      DispForC σ (enrichCtxWfT_of_envWfT S.env S.ctx) (S.can σ)

/-- §3 coverage half, at bound-key `key`: every query in the independent input
    domain — **all** of `QueryC` at frame `p`, guarded by `LexDM (key q) B` —
    is supplied its `ReadyC`. The domain is the full tagged union; it is never
    "the queries that have a `ReadyC`" (S0 §3 vacuity check). -/
def CoverageCAt (key : QueryC Eₐ Aw tbl → List Nat × Nat)
    (p : Nat) (B : List Nat × Nat) : Prop :=
  ∀ q : QueryC Eₐ Aw tbl, q.frameLen = p →
    LexDM (key q) B → Nonempty (ReadyC q)

/-- §3 below half, at bound-key `key`: queries at frame `p` that have a
    `ReadyC` get their six conclusions when `LexDM (key q) B` holds. -/
def BelowCAt (key : QueryC Eₐ Aw tbl → List Nat × Nat)
    (p : Nat) (B : List Nat × Nat) : Prop :=
  ∀ q : QueryC Eₐ Aw tbl, q.frameLen = p → Nonempty (ReadyC q) →
    LexDM (key q) B → q.Goal

/-- §3: the completed full-domain internal pack
    `CompleteCAt key p B = CoverageCAt key p B ∧ BelowCAt key p B`. The §8
    instance is `key = QueryC.combBound`; no producer is supplied here. -/
def CompleteCAt (key : QueryC Eₐ Aw tbl → List Nat × Nat)
    (p : Nat) (B : List Nat × Nat) : Prop :=
  CoverageCAt key p B ∧ BelowCAt key p B

/-- One query discharged from a `key`-keyed pack at its own successor bound
    `Bq = ((key q).1, (key q).2 + 1)` (S0 §8's `lexDM_succ_snd` call). -/
private theorem goalOfKeyPack {key : QueryC Eₐ Aw tbl → List Nat × Nat}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) key p B)
    (q : QueryC Eₐ Aw tbl) : q.Goal :=
  (hcomp q.frameLen ((key q).1, (key q).2 + 1)).2 q rfl
    ((hcomp q.frameLen ((key q).1, (key q).2 + 1)).1 q rfl
      (lexDM_succ_snd (key q)))
    (lexDM_succ_snd (key q))

/-- §8's projection, factored over the pack's bound-key. For each public field
    the tagged query is discharged by `goalOfKeyPack` at that query's own
    successor bound — per-field canonical `C`, per-field `m`, no shared bound,
    no `BelowC → BelowScoped` coercion. The public `LexDM … bound` hypothesis
    of each field is unused (`_hlt`): the internal obligation lives at the
    combined bound. -/
theorem allBelowScoped_of_keyed
    (key : QueryC Eₐ Aw tbl → List Nat × Nat)
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) key p B) :
    AllBelowScoped Eₐ Aw tbl := fun _bound =>
  { es := fun {_E} {_n} {Γ} {_a} {_b} {_T} h hAP S σ hσ _hlt =>
        goalOfKeyPack hcomp (.es h hAP S σ hσ Γ)
    cl := fun {_E} {_n} {Γ} {_e} {_T₁} {_T₂} D₁ D₂ h₁ h₂ S σ hσ _hlt =>
        goalOfKeyPack hcomp (.cl D₁ D₂ h₁ h₂ S σ hσ Γ)
    eut := fun {_E} {_n} {Γ} {_e} {_T₁} {_T₂} D₁ D₂ h₁ h₂ S σ hσ _hlt =>
        goalOfKeyPack hcomp (.eut D₁ D₂ h₁ h₂ S σ hσ Γ)
    cts := fun {_E} {_n} {Γ} {_X} {_Y} {_w} {_s} h DX hAP hDX S _hlt =>
        goalOfKeyPack hcomp (.cts h DX hAP hDX S Γ)
    pb := fun {_E} {_n} {Γ} {_e} {_T} {_s} D DT hD hDT S σ hσ _hlt =>
        goalOfKeyPack hcomp (.pb D DT hD hDT S σ hσ Γ)
    bitCoh := fun {_E} {_n} {Γ} {_T} {_u} {_v} D₁ D₂ h₁ h₂ S σ hσ _hlt =>
        goalOfKeyPack hcomp (.bitCoh D₁ D₂ h₁ h₂ S σ hσ Γ) }

/-- **§8 — the conditional projection.**
    `(∀ p B, CompleteCAt combBound p B) → AllBelowScoped`, where the pack is
    keyed by each query's own canonical combined bound `combMeas Aw C m`.
    CONDITIONAL until a `CompleteCAt` producer exists (§10); nothing here
    asserts an `AllBelowScoped` inhabitant or constructs one
    unconditionally. -/
theorem allBelowScoped_of_completeC {Eₐ : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) QueryC.combBound p B) :
    AllBelowScoped Eₐ Aw tbl :=
  allBelowScoped_of_keyed QueryC.combBound hcomp

/-- The intended consumer (S0 §8's final native call, conditional form):
    the completed pack plus `TableWF` gives `SortCoh` through the existing
    `sortCoh_of_allBelowScoped`. -/
theorem sortCoh_of_completeC {Eₐ E : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule} {n : Nat} {Γ : LCtx} {σ : Level → Level}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) QueryC.combBound p B)
    (hW : TableWF tbl)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ)
    {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) : SortCoh σ D₁ D₂ :=
  sortCoh_of_allBelowScoped (allBelowScoped_of_completeC hcomp) hW S hσ
    D₁ D₂ h₁ h₂

/-! ### Per-field extractors (parallel to `*_of_allBelowScoped`) -/

theorem es_of_completeC {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) QueryC.combBound p B)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) (hAP : h.AssumpPref)
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
    ES tbl σ (S.can σ) h :=
  es_of_allBelowScoped (allBelowScoped_of_completeC hcomp) S hσ h hAP

theorem cl_of_completeC {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) QueryC.combBound p B)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
    CL tbl σ (S.can σ) D₁ D₂ :=
  cl_of_allBelowScoped (allBelowScoped_of_completeC hcomp) S hσ D₁ D₂ h₁ h₂

theorem eut_of_completeC {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) QueryC.combBound p B)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
    EUT tbl σ (S.can σ) D₁ D₂ :=
  eut_of_allBelowScoped (allBelowScoped_of_completeC hcomp) S hσ D₁ D₂ h₁ h₂

theorem cts_of_completeC {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) QueryC.combBound p B)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (hAP : h.AssumpPref) (hDX : DX.AssumpPref) (S : ScopedCtx Eₐ E n Γ) :
    CTS h DX :=
  cts_of_allBelowScoped (allBelowScoped_of_completeC hcomp) S h DX hAP hDX

theorem pb_of_completeC {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) QueryC.combBound p B)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    (hD : D.AssumpPref) (hDT : DT.AssumpPref)
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
    PBit σ (S.can σ) D DT :=
  pbit_of_allBelowScoped (allBelowScoped_of_completeC hcomp) S hσ D DT hD hDT

theorem bitCoh_of_completeC {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAt (Eₐ := Eₐ) (Aw := Aw)
      (tbl := tbl) QueryC.combBound p B)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref)
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (hσ : LevelHom σ) :
    BitCoh σ D₁ D₂ :=
  bitCoh_of_allBelowScoped (allBelowScoped_of_completeC hcomp) S hσ D₁ D₂ h₁ h₂

/-! ### §9 tooth — the raw-bound-keyed pack (mutant) -/

/-- **MUTANT.** The §9 tooth "the same raw bound reused for a canonical spine
    of different weight": instantiating `CompleteCAt` at `QueryC.rawMeasure`
    keys the internal pack by the raw public measure, so the successor-bound
    call below is authorized at `(m.1, m.2 + 1)` — a bound that never pays the
    canonical spine's atoms/weight. The projection compiles unchanged, which is
    exactly the wrong acceptance; `rawComb_succ_tooth` shows the real
    combined-bound control refuses that same bound on a concrete canonical
    spine. -/
def CompleteCAtMut (Eₐ : ResolvedEnv) (Aw : Nat → Nat) (tbl : List CRule)
    (p : Nat) (B : List Nat × Nat) : Prop :=
  CompleteCAt (Eₐ := Eₐ) (Aw := Aw) (tbl := tbl) QueryC.rawMeasure p B

/-- Mutant projection: `CompleteCAtMut` still yields `AllBelowScoped` — the
    weak check wrongly accepts the raw-keyed pack. -/
theorem allBelowScoped_of_completeCMut {Eₐ : ResolvedEnv} {Aw : Nat → Nat}
    {tbl : List CRule}
    (hcomp : ∀ (p : Nat) (B : List Nat × Nat), CompleteCAtMut Eₐ Aw tbl p B) :
    AllBelowScoped Eₐ Aw tbl :=
  allBelowScoped_of_keyed QueryC.rawMeasure hcomp

/-- The successor combined-bound control refuses what the raw-keyed mutant
    accepts, on the same real input: for the real pair measure
    `m = tyPairMeas Aw (pbitSort E n) (pbitSort E n) = ([1,1], 2)` the raw
    successor bound `(m.1, m.2+1) = ([1,1], 3)` does satisfy `LexDM m ·`
    (`lexDM_succ_snd`), but at the canonical spine `pbitWallCtxP E n`
    (atoms `[6]`, weight `6`) the combined point is `([6,1,1], 8)` and
    `LexDM ([6,1,1], 8) ([1,1], 3)` fails — the mutant's bound is cheaper than
    the bound the canonical spine obliges. -/
theorem rawComb_succ_tooth (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    LexDM (tyPairMeas Aw (pbitSort E n) (pbitSort E n))
        ((tyPairMeas Aw (pbitSort E n) (pbitSort E n)).1,
         (tyPairMeas Aw (pbitSort E n) (pbitSort E n)).2 + 1)
      ∧ ¬ LexDM (combMeas Aw (pbitWallCtxP E n)
            (tyPairMeas Aw (pbitSort E n) (pbitSort E n)))
          ((tyPairMeas Aw (pbitSort E n) (pbitSort E n)).1,
           (tyPairMeas Aw (pbitSort E n) (pbitSort E n)).2 + 1) := by
  refine ⟨lexDM_succ_snd _, ?_⟩
  intro hlt
  have hcomb : combMeas Aw (pbitWallCtxP E n)
      (tyPairMeas Aw (pbitSort E n) (pbitSort E n)) = ([6, 1, 1], 8) := rfl
  have hraw : tyPairMeas Aw (pbitSort E n) (pbitSort E n) = ([1, 1], 2) := rfl
  rw [hcomb, hraw] at hlt
  cases hlt with
  | left _ _ hdm =>
      rcases hdm with ⟨X, Y, Z, hX, hM, hN, hdom⟩
      -- `hM : [1,1].Perm (X ++ Z)`, `hN : [6,1,1].Perm (Y ++ Z)`,
      -- `hX : X ≠ []`, `hdom : ∀ y ∈ Y, ∃ x ∈ X, y < x`.
      have h6 : (6 : Nat) ∈ Y ++ Z :=
        hN.subset (by decide : (6 : Nat) ∈ [6, 1, 1])
      rcases List.mem_append.mp h6 with h6Y | h6Z
      · obtain ⟨x, hxX, hx6⟩ := hdom 6 h6Y
        have hxM : x ∈ ([1, 1] : List Nat) :=
          hM.symm.subset (List.mem_append_left Z hxX)
        have hx1 : x = 1 := by
          rcases List.mem_cons.mp hxM with h | h
          · exact h
          · exact List.mem_singleton.mp h
        omega
      · have h6M : (6 : Nat) ∈ ([1, 1] : List Nat) :=
          hM.symm.subset (List.mem_append_right X h6Z)
        have : (6 : Nat) = 1 := by
          rcases List.mem_cons.mp h6M with h | h
          · exact h
          · exact List.mem_singleton.mp h
        omega
  -- the `Prod.Lex.right` case is impossible: it would need
  -- `[6,1,1] = [1,1]` as the shared first component, so `cases` discharged it.

#print axioms Rcic.Syn.allBelowScoped_of_completeC
#print axioms Rcic.Syn.sortCoh_of_completeC
#print axioms Rcic.Syn.allBelowScoped_of_completeCMut
#print axioms Rcic.Syn.rawComb_succ_tooth

end Rcic.Syn
