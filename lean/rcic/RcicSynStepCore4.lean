import rcic.RcicSynStepSkeleton
import rcic.RcicSynEutPair
import rcic.RcicSynPiWalk
import rcic.RcicSynLetTransportCL
import rcic.RcicSynPBitAll
import rcic.RcicSynSpineComb
import rcic.RcicSynRouteSlot
import rcic.RcicSynMixedBitFinish
import rcic.RcicSynLetSub
import rcic.RcicSynConstEutAdm

/-!
# Syntactic sortRow — the four open core `StepSuppliers` cases (`cl`/`eut`/`pb`/`mixed`)

`research/rcic/sortrow/STEP_SUPPLIERS.md` §2, `BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §10;
brief `~/.residua-lean/briefs/core4-cases.md`.  **Measure first, then assemble.**

## Measured inventory

The `Issues` grammar (≈60 constructors) is an *indexed demand table*, not a `Below`
functor: `StepIH` answers only demanded, `Before`-ordered queries.  The four open
fields issue:

* `.cl` → `cl_mixed` (the same-pair `.mixed` move) + the six `occ_*` rows.
* `.eut` → `eut_mixed` + `occ_*`.
* `.pb` → `pb_bvar_bitCoh` (the bvar's stored sort-typing `hA` against `DT`),
  `pb_letValue` (a frame let-entry's value `PBit` at the *smaller* tail scope,
  `letValue_before`), and `occ_*`.
* `.mixed` → `occ_*` only.

### Same-site coverage and the named gaps

`occ_*` rows take `subAt`-positioned subnodes *of the same (E,n,Γ)* — this is exactly
what `StepIH` can reach (`Before` proofs here are `lexDM_combMeas_mono` over
`tyPairMeas`/`cvMeas` descents).  The gaps are all of one kind: an obligation whose
objects are *not* `subAt`-positioned (regularity surfaces `h.reg.2`, binder-crossed
bodies at `binderDisp … :: ρ`, `letSub`-rebuilt nodes, or cross-subject pairs where
`occ_*`'s same-`e` side condition fails).  Every such gap is a named port here —
never restated as the goal itself.

Per-branch coverage (verified against the landed helpers):

* `conv`: `.cl (conv h hc) D₂ ≡ CL h D₂` (`eps_conv`) — issuable.  `.eut` needs
  `ES hc` + `EUT h D₂` (issuable) and `CL hc.dl h.reg.2` — `h.reg.2` is regularity-
  built, not positioned: port `EutConvLPorts.regCl` / `EutConvRPorts.regCl`.
* `lit`: `TyP.lit`'s subject is `.lit t` while `hexp` types `natExpand t`, so
  lit-vs-anything-else is cross-subject and *unissuable*; lit-vs-lit issues
  `.cl/.eut hexp₁ hexp₂` (`eut_lit_nodes`/`cl_lit_nodes` are `Iff.rfl`).
* `bvar`: `CL` needs `levelIsZero (σ u₁) = levelIsZero (σ u₂)` — `BitCoh` at the
  stored sort-typings, issuable via `occ_bitCoh` after `A₁ = A₂` is recovered from
  the shared `lookupType`.  `EUT` needs `ConvMod` of the `hA.eps` (not `reg.2.eps`):
  port `EutBvarPorts.sortConv`.
* `pi`: domain `BitCoh`/`CL` issuable; the codomain obligation sits at
  `binderDisp (levelIsZero (σ u₁)) :: ρ` — port `ClPiPorts.bodyCl`
  (`cl_pi_nodes` also wants `TableClosed`).  `EUT` needs the `imax` coherence
  `eqN (σ (imax u₁ v₁)) (σ (imax u₂ v₂))` — port `EutPiPorts.imaxCoh`.
* `lam`: domain bit + body obligations analogous; `cl_lam_nodes_*` splits on
  `levelIsZero (σ u₁)` and the body's `★`-status — ports `ClLamPorts`.
  `EUT` needs `hTC`, domain `BitCoh`+`CL` (issuable), and the codomain `ConvMod`
  at the binder display — port `EutLamPorts.convB`.
* `app`: fun/arg `CL`s are positioned and issuable; the `★`-shape case split is
  `ClAppPorts.shape`.  `EUT` needs `ConvMod` of the result-sort typings — different
  subjects (`instantiate0 a B₁` vs `B₂`), unissuable — `EutAppPorts.typeSortConv`.
* `letE`: `CL` reduces to the `letSub` pair (`cl_letE_nodes_iff_letSub`); `letSub`
  nodes are re-built, not positioned — `ClLetEPorts.letSubCl`.  `EUT` needs
  `ConvMod` of the result sorts — `EutLetEPorts.typeSortConv`.
* `const`: `hT₁`/`hT₂` type `instantiateLevels ls₁/ls₂ m.mtype` — cross-subject;
  `ConvMod` port (`EutConstPorts.typeSortConv`).  `cl_const_nodes` is the helper.
* `.pb`: the bvar spine is fully assembled (`PbBvarSpinePorts` +
  `pb_bvar_bitCoh`/`pbit_bvar_spine`); the generic decomposition is `PbPorts`
  (`PBit D D.reg.2` + `BitCoh σ D.reg.2 DT` → `pbit_of_reg_and_bitCoh`); the
  let-value row is issued (`pb_issued_letValue`).
* `.mixed`: `occ_*` only; the same-subject `CL∧EUT` residuals at the same rank
  are `Before`-refuted (`cl_not_before_mixed`/`eut_not_before_mixed`), so no
  honest port exists below the field — `mixed_step` composition is in-flight
  (#7498, `fable/mixed-worker-step`) and out of this file's scope.  Only the
  controls are delivered.

## Rank controls

`Before` is a `Prod.Lex` on `(originalPrefixLength, localKey)`; the mixed-move rows
and the cross-family pairs (`.cl`↔`.eut`, `.bitCoh`↔`.eut` on the same operands)
keep the key *equal* (`movedMeas`/`tyPairMeas` coincide), so they are dead edges —
`keyLT_irrefl`-refuted.  `cl_occ_self`/`mixed_occ_cl_self` show the grammar *does*
issue self-denominating requests which `Before` then refuses: the demand side is
responsible for not needing them.
-/

open Rcic.Declarative

namespace Rcic.Syn

/-! ## §1 Rank controls -/

/-- The rank key is irreflexive: no query is `Before` itself.  Same-site
occurrence requests issued against the *whole* operand (`subAt` at `[]`) have
equal local keys, hence are unanswerable — the demand side must never rely on
them. -/
theorem before_irrefl (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) :
    ¬ Before Aw q q := by
  intro h
  cases h with
  | left _ _ hlt => exact (Nat.lt_irrefl _) hlt
  | right _ hlt => exact lexDM_irrefl hlt

/-- `.mixed`'s local key is `.cl`'s on the same pair (`movedMeas` is `tyPairMeas`). -/
theorem cl_mixed_sameRank (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.rank Aw (.mixed D₁ D₂ S σ ρ) = P2Query.rank Aw (.cl D₁ D₂ S σ ρ) := rfl

/-- `cl_mixed`'s target is not `Before` its issuer — the move is a delegation, not a
descent. -/
theorem mixed_not_before_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ Before Aw (.mixed D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) :=
  by
  intro h
  cases h with
  | left _ _ hlt => exact absurd hlt (Nat.lt_irrefl _)
  | right _ hlt => exact lexDM_irrefl hlt

/-- `.cl` cannot issue back into its own `.mixed` — same rank, dead edge. -/
theorem cl_not_before_mixed (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ Before Aw (.cl D₁ D₂ S σ ρ) (.mixed D₁ D₂ S σ ρ) :=
  by
  intro h
  cases h with
  | left _ _ hlt => exact absurd hlt (Nat.lt_irrefl _)
  | right _ hlt => exact lexDM_irrefl hlt

theorem eut_mixed_sameRank (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.rank Aw (.mixed D₁ D₂ S σ ρ) = P2Query.rank Aw (.eut D₁ D₂ S σ ρ) := rfl

theorem mixed_not_before_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ Before Aw (.mixed D₁ D₂ S σ ρ) (.eut D₁ D₂ S σ ρ) :=
  by
  intro h
  cases h with
  | left _ _ hlt => exact absurd hlt (Nat.lt_irrefl _)
  | right _ hlt => exact lexDM_irrefl hlt

theorem eut_not_before_mixed (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ Before Aw (.eut D₁ D₂ S σ ρ) (.mixed D₁ D₂ S σ ρ) :=
  by
  intro h
  cases h with
  | left _ _ hlt => exact absurd hlt (Nat.lt_irrefl _)
  | right _ hlt => exact lexDM_irrefl hlt

/-- `.cl` and `.eut` share `tyPairMeas`: neither can issue the other — the same-rank
dead edge the `eut`/`cl` split relies on. -/
theorem cl_eut_sameRank (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.rank Aw (.eut D₁ D₂ S σ ρ) = P2Query.rank Aw (.cl D₁ D₂ S σ ρ) := rfl

theorem eut_not_before_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ Before Aw (.eut D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) :=
  by
  intro h
  cases h with
  | left _ _ hlt => exact absurd hlt (Nat.lt_irrefl _)
  | right _ hlt => exact lexDM_irrefl hlt

theorem cl_not_before_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ Before Aw (.cl D₁ D₂ S σ ρ) (.eut D₁ D₂ S σ ρ) :=
  by
  intro h
  cases h with
  | left _ _ hlt => exact absurd hlt (Nat.lt_irrefl _)
  | right _ hlt => exact lexDM_irrefl hlt

/-- `.bitCoh` and `.eut` on the same operands are same-rank — `bitCoh_eut` is a dead
edge in both directions. -/
theorem bitCoh_eut_sameRank (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    P2Query.rank Aw (.eut D₁ D₂ S σ ρ) = P2Query.rank Aw (.bitCoh D₁ D₂ S σ ρ) := rfl

theorem eut_not_before_bitCoh (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ Before Aw (.eut D₁ D₂ S σ ρ) (.bitCoh D₁ D₂ S σ ρ) :=
  by
  intro h
  cases h with
  | left _ _ hlt => exact absurd hlt (Nat.lt_irrefl _)
  | right _ hlt => exact lexDM_irrefl hlt

theorem bitCoh_not_before_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ¬ Before Aw (.bitCoh D₁ D₂ S σ ρ) (.eut D₁ D₂ S σ ρ) :=
  by
  intro h
  cases h with
  | left _ _ hlt => exact absurd hlt (Nat.lt_irrefl _)
  | right _ hlt => exact lexDM_irrefl hlt

/-- The grammar *does* let `.cl` issue itself (occurrence at the root paths
`(0,[])`,`(1,[])` — `subAt []` is the node itself). -/
theorem cl_occ_self {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T₁ T₂ : Expr Nat} {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    Issues (.cl D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) :=
  Issues.occ_cl (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂

/-- …and `Before` refuses it — the demanded self-call is expressible but
unanswerable.  `.mixed`'s root-`.cl` issue is the same phenomenon across fields. -/
theorem cl_occ_self_unanswerable (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    Issues (.cl D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) ∧
      ¬ Before Aw (.cl D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) :=
  ⟨cl_occ_self S σ ρ hap₁ hap₂, before_irrefl Aw _⟩

theorem mixed_occ_cl_self {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {e T₁ T₂ : Expr Nat} {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    Issues (.mixed D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) ∧
      ¬ Before Aw (.cl D₁ D₂ S σ ρ) (.mixed D₁ D₂ S σ ρ) :=
  ⟨Issues.occ_cl (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂,
    cl_not_before_mixed Aw D₁ D₂ S σ ρ⟩

/-! ## §2 `pb` — `pb_bvar_bitCoh`, `pb_letValue`, and the generic decomposition -/

/-- The bvar's `BitCoh` request is `Before` its `.pb` issuer — **only** when the
query's scope is the derivation's own context (`S : ScopedCtx Eₐ E n Γ`, the
`localKey`'s `enrichCtxWfT` frame): the landed `bvar_bit_request_below`.  For a
proper prefix scope `Γ₀ ≠ Γ` the descent is not derivable — the row's caller must
issue `.pb` at the current context. -/
theorem pb_bvar_bitCoh_before (Aw : Nat → Nat)
    {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u s : Level}
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (ρ : List Disp)
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (DT : TyP E n Γ A (.sort s)) :
    Before Aw (.bitCoh hA DT S σ ρ)
      (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ) :=
  bvar_bit_request_below Aw S σ ρ hlook hA DT

/-- A demanded `.pb` on a `bvar` supplies the `BitCoh` of its stored sort-typing
against the table derivation — the `pb_bvar_bitCoh` row, answered. -/
theorem pb_issued_bvar_bitCoh (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u s : Level}
    {S : ScopedCtx Eₐ E n Γ} {σ : Level → Level} {ρ : List Disp}
    {hlook : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
    {DT : TyP E n Γ A (.sort s)}
    (hq : Demand (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ))
    (ih : StepIH Aw tbl (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ)) :
    BitCoh σ hA DT :=
  ih_issue Aw tbl hq ih _ Issues.pb_bvar_bitCoh
    (pb_bvar_bitCoh_before Aw S σ ρ hlook hA DT)

/-- The non-issuable residuals of `pb`'s bvar branch: the context display, the entry
sort receipt, and the let-spine `PBit` feed of `pbit_bvar_spine`. -/
structure PbBvarSpinePorts {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat}
    {A : Expr Nat} {u : Level} (hlook : lookupType Γ i = some A)
    (hA : TyP E n Γ A (.sort u)) (σ : Level → Level) (ρ : List Disp) : Type where
  C : CtxP E n Γ
  dispC : DispForC σ C ρ
  sortAt : C.entrySort i = some u
  spineLet : SpineLetPBit σ C ρ i

/-- `pb`'s bvar branch, assembled: `pb_bvar_bitCoh` supplies the `BitCoh`; the
display/sort/spine residuals come in as named ports; `pbit_bvar_spine` closes it. -/
theorem pb_bvar_caseStep_of_spine (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u s : Level}
    {S : ScopedCtx Eₐ E n Γ} {σ : Level → Level} {ρ : List Disp}
    {hlook : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
    {DT : TyP E n Γ A (.sort s)}
    (ports : PbBvarSpinePorts hlook hA σ ρ) :
    CaseStep Aw tbl (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ) := fun hq ih =>
  pbit_bvar_spine ports.dispC ports.sortAt ports.spineLet
    (pb_issued_bvar_bitCoh Aw tbl hq ih)

/-- A demanded `.pb` supplies the frame let-entry's value `PBit` at the tail scope —
the `pb_letValue` row, answered (`letValue_before` pays the prefix descent). -/
theorem pb_issued_letValue (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E : ResolvedEnv} {n : Nat} {Γ Γ₀ : LCtx} {e T : Expr Nat} {s : Level}
    {D : TyP E n Γ e T} {DT : TyP E n Γ T (.sort s)}
    {S : ScopedCtx Eₐ E n Γ₀} {σ : Level → Level} {ρ : List Disp}
    {k i : Nat} (hframe : Γ.drop k = Γ₀)
    {Γ' : LCtx} {A₀ : Expr Nat} {u₀ : Level} {v₀ : Expr Nat}
    {hΓ' : CtxWfT E n Γ'} {hA : HasTyT E n Γ' A₀ (.sort u₀)} {hv : HasTyT E n Γ' v₀ A₀}
    (hsel : LetEntryAt S.ctx i hΓ' hA hv)
    (hapA : (enrichHasTyT_of_envWfT S.env hΓ' hA).AssumpPref)
    (hapv : (enrichHasTyT_of_envWfT S.env hΓ' hv).AssumpPref)
    (hq : Demand (.pb D DT S σ ρ)) (ih : StepIH Aw tbl (.pb D DT S σ ρ)) :
    PBit σ ((S.tail hΓ').can σ)
      (enrichHasTyT_of_envWfT S.env hΓ' hv) (enrichHasTyT_of_envWfT S.env hΓ' hA) :=
  ih_issue Aw tbl hq ih _ (Issues.pb_letValue hframe hsel hapA hapv)
    (letValue_before Aw D DT S σ σ ρ ((S.tail hΓ').can σ) hsel)

/-- The generic `pb` decomposition: `PBit σ ρ D D.reg.2` (per-head residual — the
sort and const specials are `pbit_sort_reg`/`pbit_const_reg`) plus sort coherence
against the table derivation.  `pbit_of_reg_and_bitCoh` glues them. -/
structure PbPorts {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    (σ : Level → Level) (ρ : List Disp) : Prop where
  pbReg : PBit σ ρ D D.reg.2
  pbCoh : BitCoh σ D.reg.2 DT

theorem pb_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e T : Expr Nat} {s : Level}
    {D : TyP E n Γ e T} {DT : TyP E n Γ T (.sort s)}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (ports : PbPorts D DT σ ρ) :
    CaseStep Aw tbl (.pb D DT S σ ρ) :=
  fun _ _ => pbit_of_reg_and_bitCoh D DT ports.pbReg ports.pbCoh

/-! ## §3 `cl` — peels, issuable rows, and named residual ports -/

/-- `conv`-left peel: `CL (conv h hc) D₂` is definitionally `CL h D₂`
(`eps_conv`), and `h` is `subAt`-positioned at `(0,[0])`. -/
theorem cl_conv_left_caseStep (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e A B T₂ : Expr Nat}
    {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl (.cl (TyP.conv E n Γ e A B u h hc) D₂ S σ ρ) := fun hq ih => by
  have hw : h.wt Aw < (TyP.conv E n Γ e A B u h hc).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw h D₂)
      (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) D₂) :=
    lex_of_dm (dmStep_append_right
      (dmStep_wt_lt_singleton Aw h (TyP.conv E n Γ e A B u h hc) rfl hw) (D₂.atoms Aw))
  have hcl := ih_local Aw tbl hq ih (.cl h D₂ S σ ρ)
    (Issues.occ_cl (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := []) rfl rfl
      hq.ap.1.1 hq.ap.2) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  exact hcl

/-- `conv`-right peel, symmetric. -/
theorem cl_conv_right_caseStep (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e T₁ A B : Expr Nat}
    {u : Level}
    (D₁ : TyP E n Γ e T₁) (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl (.cl D₁ (TyP.conv E n Γ e A B u h hc) S σ ρ) := fun hq ih => by
  have hw : h.wt Aw < (TyP.conv E n Γ e A B u h hc).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw D₁ h)
      (tyPairMeas Aw D₁ (TyP.conv E n Γ e A B u h hc)) :=
    lex_of_dm (dmStep_append_left
      (dmStep_wt_lt_singleton Aw h (TyP.conv E n Γ e A B u h hc) rfl hw) (D₁.atoms Aw))
  have hcl := ih_local Aw tbl hq ih (.cl D₁ h S σ ρ)
    (Issues.occ_cl (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := [0]) rfl rfl
      hq.ap.1 hq.ap.2.1) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  exact hcl

/-- lit-vs-lit: both expansions type `natExpand t`, so `.cl hexp₁ hexp₂` is a real
query, positioned at `(0,[0])×(1,[0])`; `cl_lit_nodes` is `Iff.rfl`.
(lit-vs-other is cross-subject — `.lit t` vs `natExpand t` — and stays a port.) -/
theorem cl_lit_lit_caseStep (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {t : Nat}
    {T₁ T₂ : Expr Nat}
    (hexp₁ : TyP E n Γ (natExpand t) T₁) (hexp₂ : TyP E n Γ (natExpand t) T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.cl (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂) S σ ρ) :=
  fun hq ih => by
  have hw : hexp₁.wt Aw < (TyP.lit E n Γ t T₁ hexp₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hexp₂.wt Aw < (TyP.lit E n Γ t T₂ hexp₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hexp₁ hexp₂)
      (tyPairMeas Aw (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂)) :=
    lexDM_wt_lt_pair Aw hexp₁ hexp₂ _ _ rfl rfl hw hw₂
  have hcl := ih_local Aw tbl hq ih (.cl hexp₁ hexp₂ S σ ρ)
    (Issues.occ_cl (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hq.ap.1 hq.ap.2) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  exact hcl

/-- sort-vs-sort: zero recursive calls — the node's own `eqN` receipts close it. -/
theorem cl_sort_sort_caseStep (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {l k₁ k₂ : Level}
    (h₁ : eqN k₁ (.succ l)) (h₂ : eqN k₂ (.succ l))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.cl (TyP.sort E n Γ l k₁ h₁) (TyP.sort E n Γ l k₂ h₂) S σ ρ) :=
  fun _ _ => cl_sort_nodes tbl σ ρ h₁ h₂

/-- bvar-vs-bvar: `BitCoh σ hA₁ hA₂` (the `levelIsZero` gate bit, definitionally) is
issuable via `occ_bitCoh` at `(0,[0])×(1,[0])` once the shared lookup gives
`A₁ = A₂`; `cl_bvar_nodes` closes. -/
theorem cl_bvar_bvar_caseStep (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {i : Nat}
    {A₁ A₂ : Expr Nat} {u₁ u₂ : Level}
    (hlook₁ : lookupType Γ i = some A₁) (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hlook₂ : lookupType Γ i = some A₂) (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.cl (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁)
        (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂) S σ ρ) := fun hq ih => by
  have hAeq : A₁ = A₂ := Option.some.inj (hlook₁.symm.trans hlook₂)
  subst hAeq
  have hw₁ : hA₁.wt Aw < (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hA₁ hA₂)
      (tyPairMeas Aw (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁)
        (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂)) :=
    lexDM_wt_lt_pair Aw hA₁ hA₂ _ _ rfl rfl hw₁ hw₂
  have hbit := ih_local Aw tbl hq ih (.bitCoh hA₁ hA₂ S σ ρ)
    (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hq.ap.1 hq.ap.2) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  exact cl_bvar_nodes tbl σ ρ hlook₁ hA₁ hlook₂ hA₂ hbit

/-- `pi`-`pi` residuals: `TableClosed` and the codomain `CL` at the binder-extended
display — the binder crosses the context, so `hB₁`/`hB₂` are not `subAt`-positioned
children of the `.cl` query's same-`Γ` payload. -/
structure ClPiPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    (u₁ : Level) {v₁ v₂ : Level}
    (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂)) : Prop where
  hTC : TableClosed tbl
  bodyCl : CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hB₁ hB₂

theorem cl_pi_pi_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A B : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : ClPiPorts tbl σ ρ u₁ hB₁ hB₂) :
    CaseStep Aw tbl
      (.cl (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)
        S σ ρ) := fun hq ih => by
  have hw₁ : hA₁.wt Aw < (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hA₁ hA₂)
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁)
        (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)) :=
    lexDM_wt_lt_pair Aw hA₁ hA₂ _ _ rfl rfl hw₁ hw₂
  have hap : hA₁.AssumpPref ∧ hA₂.AssumpPref := ⟨hq.ap.1.1, hq.ap.2.1⟩
  have hbit := ih_local Aw tbl hq ih (.bitCoh hA₁ hA₂ S σ ρ)
    (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hap.1 hap.2) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  have hclA := ih_local Aw tbl hq ih (.cl hA₁ hA₂ S σ ρ)
    (Issues.occ_cl (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hap.1 hap.2) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  exact cl_pi_nodes tbl ports.hTC σ ρ hA₁ hB₁ hA₂ hB₂ hbit hclA ports.bodyCl

/-- `lam`-`lam` residuals: the `levelIsZero (σ u₁)`/`★` shape split plus the body
`CL` at `binderDisp … :: ρ`.  `cl_lam_nodes_drop`/`keep`/`keep_star` cover the
three shapes; domain `BitCoh` is issuable. -/
structure ClLamPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body : Expr Nat}
    {B₁ B₂ : Expr Nat} (u₁ : Level)
    (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hb₂ : TyP E n (.assumption A :: Γ) body B₂) : Prop where
  bodyCl : CL tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hb₁ hb₂
  shape : (hb₁.eps σ (.keep :: ρ) = .star ∧ hb₂.eps σ (.keep :: ρ) = .star) ∨
      (hb₁.eps σ (.keep :: ρ) ≠ .star ∧ hb₂.eps σ (.keep :: ρ) ≠ .star)

theorem cl_lam_lam_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A body : Expr Nat}
    {B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : ClLamPorts tbl σ ρ u₁ hb₁ hb₂) :
    CaseStep Aw tbl
      (.cl (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ) := fun hq ih => by
  have hw₁ : hA₁.wt Aw < (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hA₁ hA₂)
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂)) :=
    lexDM_wt_lt_pair Aw hA₁ hA₂ _ _ rfl rfl hw₁ hw₂
  have hbit := ih_local Aw tbl hq ih (.bitCoh hA₁ hA₂ S σ ρ)
    (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hq.ap.1.1 hq.ap.2.1) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  cases hu₁ : levelIsZero (σ u₁)
  · rcases ports.shape with ⟨hs₁, hs₂⟩ | ⟨hne₁, hne₂⟩
    · exact cl_lam_nodes_keep_star tbl σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ hu₁ hbit hs₁ hs₂
    · have hclb : CL tbl σ (.keep :: ρ) hb₁ hb₂ := by
        have := ports.bodyCl
        rwa [hu₁] at this
      exact cl_lam_nodes_keep tbl σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ hu₁ hbit hne₁ hne₂ hclb
  · have hclb : CL tbl σ (.drop :: ρ) hb₁ hb₂ := by
      have := ports.bodyCl
      rwa [hu₁] at this
    exact cl_lam_nodes_drop tbl σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ hu₁ hbit hclb

/-- `app`-`app`: the `★`-shape case split — fun/arg `CL`s themselves are positioned
and issuable; only the shape decision (which pair contributes) is a port. -/
structure ClAppPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂) : Prop where
  shape : (hf₁.eps σ ρ = .star ∧ hf₂.eps σ ρ = .star) ∨
      (ha₁.eps σ ρ = .star ∧ ha₂.eps σ ρ = .star) ∨
      (hf₁.eps σ ρ ≠ .star ∧ ha₁.eps σ ρ ≠ .star ∧
        hf₂.eps σ ρ ≠ .star ∧ ha₂.eps σ ρ ≠ .star)

theorem cl_app_app_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {f a A₁ B₁ A₂ B₂ : Expr Nat} {w₁ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : ClAppPorts tbl σ ρ hf₁ ha₁ hf₂ ha₂) :
    CaseStep Aw tbl
      (.cl (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) S σ ρ) := fun hq ih => by
  have hwf₁ : hf₁.wt Aw < (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hwf₂ : hf₂.wt Aw < (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hwa₁ : ha₁.wt Aw < (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hwa₂ : ha₂.wt Aw < (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlexf : LexDM (tyPairMeas Aw hf₁ hf₂)
      (tyPairMeas Aw (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂)) :=
    lexDM_wt_lt_pair Aw hf₁ hf₂ _ _ rfl rfl hwf₁ hwf₂
  have hlexa : LexDM (tyPairMeas Aw ha₁ ha₂)
      (tyPairMeas Aw (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂)) :=
    lexDM_wt_lt_pair Aw ha₁ ha₂ _ _ rfl rfl hwa₁ hwa₂
  rcases ports.shape with ⟨hf_s₁, hf_s₂⟩ | ⟨ha_s₁, ha_s₂⟩ |
      ⟨hf_ne₁, ha_ne₁, hf_ne₂, ha_ne₂⟩
  · exact cl_app_nodes_fun_star tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ hf_s₁ hf_s₂
  · have hclf := ih_local Aw tbl hq ih (.cl hf₁ hf₂ S σ ρ)
      (Issues.occ_cl (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
        hq.ap.1.1 hq.ap.2.1) rfl
      (lexDM_combMeas_mono Aw _ hlexf)
    exact cl_app_nodes_arg_star tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ ha_s₁ ha_s₂ hclf
  · have hclf := ih_local Aw tbl hq ih (.cl hf₁ hf₂ S σ ρ)
      (Issues.occ_cl (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
        hq.ap.1.1 hq.ap.2.1) rfl
      (lexDM_combMeas_mono Aw _ hlexf)
    have hcla := ih_local Aw tbl hq ih (.cl ha₁ ha₂ S σ ρ)
      (Issues.occ_cl (k₁ := 0) (p₁ := [1]) (k₂ := 1) (p₂ := [1]) rfl rfl
        hq.ap.1.2.1 hq.ap.2.2.1) rfl
      (lexDM_combMeas_mono Aw _ hlexa)
    exact cl_app_nodes_rel tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂
      hf_ne₁ ha_ne₁ hf_ne₂ ha_ne₂ hclf hcla

/-- `letE`-`letE`: the value `eps` shape dichotomy plus the body `CL`s at the
display routed by that shape. `CL` of the `letSub` pair is *not* a port — by
`letSub_eps_eq_letE` it is definitionally the cell's own goal. The positioned
value/type pairs `hv`/`hA` carry no `CL` obligation for the letE composition
(the `cl_letE_nodes_*` closers consume only shape + routed body). -/
structure ClLetEPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
    (hv₁ : TyP E n Γ v A) (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂) (hv₂ : TyP E n Γ v A) :
    Prop where
  shape : (hv₁.eps σ ρ = .star ∧ hv₂.eps σ ρ = .star) ∨
      (∃ ev : ETm, ev ≠ .star ∧ hv₁.eps σ ρ = ev ∧ hv₂.eps σ ρ = ev)
  bodyDrop : hv₁.eps σ ρ = .star → hv₂.eps σ ρ = .star →
    CL tbl σ (.drop :: ρ) hb₁ hb₂
  bodyInline : ∀ {ev : ETm}, ev ≠ .star → hv₁.eps σ ρ = ev →
    hv₂.eps σ ρ = ev → CL tbl σ (.inline ev :: ρ) hb₁ hb₂

theorem cl_letE_letE_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
    {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : ClLetEPorts tbl σ ρ hv₁ hb₁ hb₂ hv₂) :
    CaseStep Aw tbl
      (.cl (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) S σ ρ) :=
  fun _ _ => by
    cases ports.shape with
    | inl hstar =>
        exact cl_letE_nodes_drop tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂
          hstar.1 hstar.2 (ports.bodyDrop hstar.1 hstar.2)
    | inr h =>
        obtain ⟨ev, hne, hev₁, hev₂⟩ := h
        exact cl_letE_nodes_inline_eq tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂
          hev₁ hev₂ hne (ports.bodyInline hne hev₁ hev₂)

/-- `const`-`const`: the gate bit `levelIsZero (σ u₁) = levelIsZero (σ u₂)`
(definitionally `BitCoh σ hT₁ hT₂`).  When `ls₁ = ls₂` the `hT`s share the
subject `instantiateLevels ls₁ m.mtype` and the bit is class (a) — issuable via
`occ_bitCoh` at `(0,[0])×(1,[0])` with strict weight drop.  Only the
cross-subject `ls₁ ≠ ls₂` case (no `Issues` row — the two type subjects
`instantiateLevels ls₁ m.mtype` / `instantiateLevels ls₂ m.mtype` differ) is
the named port.  The structure binds the actual sort-typings `hT₁ hT₂` at the
shared member `m`, so the bit cannot be requested for unrelated levels. -/
structure ClConstPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂)) : Prop where
  hbit : ls₁ ≠ ls₂ → levelIsZero (σ u₁) = levelIsZero (σ u₂)

theorem cl_const_const_caseStep_of_port (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {r : Nat}
    {ls ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hres₂ : E.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : ClConstPorts tbl σ ρ hT₁ hT₂) :
    CaseStep Aw tbl
      (.cl (TyP.const E n Γ r ls ls₁ m u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S σ ρ) :=
  fun hq ih => by
    have hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂) := by
      by_cases hls : ls₁ = ls₂
      · subst hls
        exact ih_local Aw tbl hq ih (.bitCoh hT₁ hT₂ S σ ρ)
          (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
            hq.ap.1 hq.ap.2) rfl
          (lexDM_combMeas_mono Aw _
            (lexDM_wt_lt_pair Aw hT₁ hT₂ _ _ rfl rfl
              (by simp only [TyP.wt]; omega) (by simp only [TyP.wt]; omega)))
      · exact ports.hbit hls
    exact cl_const_nodes tbl σ ρ hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ hbit

/-! ## §4 `eut` — the same discipline: issuable requests plus named ports -/

/-- `eut` conv-left: `ES hc` and `EUT h D₂` are issuable (positioned at `(0,[1])`
and `(0,[0])×(1,[])`); `CL hc.dl h.reg.2` is the named port — `h.reg.2` is
regularity-built, not a `subAt` position. -/
structure EutConvLPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) : Prop where
  regCl : CL tbl σ ρ hc.dl h.reg.2

theorem eut_conv_left_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e A B T₂ : Expr Nat}
    {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : EutConvLPorts tbl σ ρ h hc) :
    CaseStep Aw tbl (.eut (TyP.conv E n Γ e A B u h hc) D₂ S σ ρ) := fun hq ih => by
  have hwh : h.wt Aw < (TyP.conv E n Γ e A B u h hc).wt Aw := by
    simp only [TyP.wt]; omega
  have hwc : hc.wt Aw < (TyP.conv E n Γ e A B u h hc).wt Aw := by
    simp only [TyP.wt]; omega
  have hlexE : LexDM (tyPairMeas Aw h D₂)
      (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) D₂) :=
    lex_of_dm (dmStep_append_right
      (dmStep_wt_lt_singleton Aw h (TyP.conv E n Γ e A B u h hc) rfl hwh) (D₂.atoms Aw))
  have hbase : DMStep (hc.atoms Aw) [(TyP.conv E n Γ e A B u h hc).wt Aw] := by
    rw [← List.append_nil (hc.atoms Aw)]
    exact dmStep_of_below
      (fun y hy => Nat.lt_of_le_of_lt (CvP.atoms_le Aw hc y hy) hwc)
  have hlexC : LexDM (cvMeas Aw hc)
      (tyPairMeas Aw (TyP.conv E n Γ e A B u h hc) D₂) :=
    lex_of_dm (dmStep_drop_right hbase (D₂.atoms Aw))
  have hap : h.AssumpPref ∧ hc.AssumpPref := ⟨hq.ap.1.1, hq.ap.1.2⟩
  have hes := ih_local Aw tbl hq ih (.es hc S σ ρ)
    (Issues.occ_es (k := 0) (p := [1]) rfl hap.2) rfl
    (lexDM_combMeas_mono Aw _ hlexC)
  have heut := ih_local Aw tbl hq ih (.eut h D₂ S σ ρ)
    (Issues.occ_eut (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := []) rfl rfl
      hap.1 hq.ap.2) rfl
    (lexDM_combMeas_mono Aw _ hlexE)
  exact eut_conv_left tbl σ ρ h hc D₂ hes ports.regCl heut

/-- `eut` conv-right: `EUT D₁ h` at `(0,[])×(1,[0])`, `ES hc` at `(1,[1])`; the
port is `CL h.reg.2 hc.dl`. -/
structure EutConvRPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u)) : Prop where
  regCl : CL tbl σ ρ h.reg.2 hc.dl

theorem eut_conv_right_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e T₁ A B : Expr Nat}
    {u : Level}
    (D₁ : TyP E n Γ e T₁) (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : EutConvRPorts tbl σ ρ h hc) :
    CaseStep Aw tbl (.eut D₁ (TyP.conv E n Γ e A B u h hc) S σ ρ) := fun hq ih => by
  have hwh : h.wt Aw < (TyP.conv E n Γ e A B u h hc).wt Aw := by
    simp only [TyP.wt]; omega
  have hwc : hc.wt Aw < (TyP.conv E n Γ e A B u h hc).wt Aw := by
    simp only [TyP.wt]; omega
  have hlexE : LexDM (tyPairMeas Aw D₁ h)
      (tyPairMeas Aw D₁ (TyP.conv E n Γ e A B u h hc)) :=
    lex_of_dm (dmStep_append_left
      (dmStep_wt_lt_singleton Aw h (TyP.conv E n Γ e A B u h hc) rfl hwh) (D₁.atoms Aw))
  have hlexC : LexDM (cvMeas Aw hc)
      (tyPairMeas Aw D₁ (TyP.conv E n Γ e A B u h hc)) := by
    apply lex_of_dm
    refine ⟨(TyP.conv E n Γ e A B u h hc).wt Aw :: D₁.atoms Aw, hc.atoms Aw, [],
      List.cons_ne_nil _ _, ?_, ?_, ?_⟩
    · rw [List.append_nil]
      exact List.perm_append_comm
    · rw [List.append_nil]
    · intro y hy
      exact ⟨(TyP.conv E n Γ e A B u h hc).wt Aw,
        List.mem_cons_self _ _,
        Nat.lt_of_le_of_lt (CvP.atoms_le Aw hc y hy) hwc⟩
  have hap : h.AssumpPref ∧ hc.AssumpPref := ⟨hq.ap.2.1, hq.ap.2.2⟩
  have heut := ih_local Aw tbl hq ih (.eut D₁ h S σ ρ)
    (Issues.occ_eut (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := [0]) rfl rfl
      hq.ap.1 hap.1) rfl
    (lexDM_combMeas_mono Aw _ hlexE)
  have hes := ih_local Aw tbl hq ih (.es hc S σ ρ)
    (Issues.occ_es (k := 1) (p := [1]) rfl hap.2) rfl
    (lexDM_combMeas_mono Aw _ hlexC)
  exact eut_conv_right tbl σ ρ D₁ h hc heut ports.regCl hes

/-- `eut` bvar-bvar: zero ports — `hlook₁`/`hlook₂` agree on `A`, and
`CL tbl σ ρ hA₁ hA₂` (which the `EUT` goal is, `bvar.reg.2` being `hA`) is an
issued `occ_cl` request at `(0,[0])×(1,[0])`, strictly smaller. -/
theorem eut_bvar_bvar_caseStep (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {i : Nat}
    {A₁ A₂ : Expr Nat} {u₁ u₂ : Level}
    (hlook₁ : lookupType Γ i = some A₁) (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hlook₂ : lookupType Γ i = some A₂) (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.eut (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁)
        (TyP.bvar E n Γ i A₂ u₂ hlook₂ hA₂) S σ ρ) := fun hq ih => by
  have hAeq : A₁ = A₂ := Option.some.inj (hlook₁.symm.trans hlook₂)
  subst hAeq
  have hw₁ : hA₁.wt Aw < (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hA₁ hA₂)
      (tyPairMeas Aw (TyP.bvar E n Γ i A₁ u₁ hlook₁ hA₁)
        (TyP.bvar E n Γ i A₁ u₂ hlook₂ hA₂)) :=
    lexDM_wt_lt_pair Aw hA₁ hA₂ _ _ rfl rfl hw₁ hw₂
  have hcl := ih_local Aw tbl hq ih (.cl hA₁ hA₂ S σ ρ)
    (Issues.occ_cl (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hq.ap.1 hq.ap.2) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  exact eut_bvar_nodes tbl σ ρ hlook₁ hA₁ hlook₂ hA₂ hcl

/-- `eut` lit-lit: `EUT hexp₁ hexp₂` positioned at `(0,[0])×(1,[0])`;
`eut_lit_nodes` is `Iff.rfl`. -/
theorem eut_lit_lit_caseStep (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {t : Nat}
    {T₁ T₂ : Expr Nat}
    (hexp₁ : TyP E n Γ (natExpand t) T₁) (hexp₂ : TyP E n Γ (natExpand t) T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.eut (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂) S σ ρ) :=
  fun hq ih => by
  have hw₁ : hexp₁.wt Aw < (TyP.lit E n Γ t T₁ hexp₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hexp₂.wt Aw < (TyP.lit E n Γ t T₂ hexp₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hexp₁ hexp₂)
      (tyPairMeas Aw (TyP.lit E n Γ t T₁ hexp₁) (TyP.lit E n Γ t T₂ hexp₂)) :=
    lexDM_wt_lt_pair Aw hexp₁ hexp₂ _ _ rfl rfl hw₁ hw₂
  have heut := ih_local Aw tbl hq ih (.eut hexp₁ hexp₂ S σ ρ)
    (Issues.occ_eut (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hq.ap.1 hq.ap.2) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  exact heut

/-- `eut` sort-sort: zero ports — `LevelSub σ` is `hq.hom.levelSub` (every
demanded query is `Hom`). -/
theorem eut_sort_sort_caseStep (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {l k₁ k₂ : Level}
    (h₁ : eqN k₁ (.succ l)) (h₂ : eqN k₂ (.succ l))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.eut (TyP.sort E n Γ l k₁ h₁) (TyP.sort E n Γ l k₂ h₂) S σ ρ) :=
  fun hq _ => eut_sort_nodes tbl hq.hom.levelSub ρ h₁ h₂

/-- `eut` pi-pi: the `imax` coherence is assembled, not assumed —
`EUT hA₁ hA₂` is issued via `occ_eut` at `(0,[0])×(1,[0])`, `sortCoh_of_eut_cl`
lifts it to `SortCoh σ hA₁ hA₂` through the two reg-`CL` edges (a port when the
head isn't sort/pi-shaped; `cl_reg_sort_of_isSortOrPiHead` when it is), the
codomain `SortCoh σ hB₁ hB₂` is the named port (bodies live one binder up, not
at payload positions), and `LevelHom.imax_eqN` from `hq.hom` combines them. -/
structure EutPiPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u₁ u₂ v₁ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁))
    (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂))
    (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂)) : Prop where
  hW : TableWF tbl
  edgeL : hA₁.isSortOrPiHead = false →
    CL tbl σ ρ hA₁.reg.2 (sortNode E n Γ u₁)
  edgeR : hA₂.isSortOrPiHead = false →
    CL tbl σ ρ hA₂.reg.2 (sortNode E n Γ u₂)
  cohB : SortCoh σ hB₁ hB₂

theorem eut_pi_pi_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A B : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hB₁ : TyP E n (.assumption A :: Γ) B (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hB₂ : TyP E n (.assumption A :: Γ) B (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : EutPiPorts tbl σ ρ hA₁ hB₁ hA₂ hB₂) :
    CaseStep Aw tbl
      (.eut (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁) (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)
        S σ ρ) := fun hq ih => by
  have hw₁ : hA₁.wt Aw < (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hA₁ hA₂)
      (tyPairMeas Aw (TyP.pi E n Γ A u₁ B v₁ hA₁ hB₁)
        (TyP.pi E n Γ A u₂ B v₂ hA₂ hB₂)) :=
    lexDM_wt_lt_pair Aw hA₁ hA₂ _ _ rfl rfl hw₁ hw₂
  have heutA := ih_local Aw tbl hq ih (.eut hA₁ hA₂ S σ ρ)
    (Issues.occ_eut (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hq.ap.1.1 hq.ap.2.1) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  have hL : CL tbl σ ρ hA₁.reg.2 (sortNode E n Γ u₁) := by
    cases hs : hA₁.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl hA₁ hs σ ρ
    | false => exact ports.edgeL hs
  have hR : CL tbl σ ρ hA₂.reg.2 (sortNode E n Γ u₂) := by
    cases hs : hA₂.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl hA₂ hs σ ρ
    | false => exact ports.edgeR hs
  have hcohA : SortCoh σ hA₁ hA₂ :=
    sortCoh_of_eut_cl ports.hW hA₁ hA₂ σ ρ heutA hL hR
  exact eut_pi_nodes tbl σ ρ hA₁ hB₁ hA₂ hB₂
    (hq.hom.imax_eqN hcohA ports.cohB)

/-- `eut` lam-lam: `hTC`, the positioned domain `BitCoh`/`CL`, and the named
codomain `ConvMod` port at the binder display. -/
structure EutLamPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B₁ B₂ : Expr Nat}
    (u₁ : Level) {v₁ v₂ : Level}
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂)) : Prop where
  hTC : TableClosed tbl
  convB : ConvMod (EStep tbl) LvlEq
    (hB₁.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
    (hB₂.eps σ (binderDisp (levelIsZero (σ u₁)) :: ρ))

theorem eut_lam_lam_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A body B₁ B₂ : Expr Nat}
    {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hb₂ : TyP E n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : EutLamPorts tbl σ ρ u₁ hB₁ hB₂) :
    CaseStep Aw tbl
      (.eut (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂) S σ ρ) := fun hq ih => by
  have hw₁ : hA₁.wt Aw < (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hw₂ : hA₂.wt Aw < (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlex : LexDM (tyPairMeas Aw hA₁ hA₂)
      (tyPairMeas Aw (TyP.lam E n Γ A u₁ body B₁ v₁ hA₁ hb₁ hB₁)
        (TyP.lam E n Γ A u₂ body B₂ v₂ hA₂ hb₂ hB₂)) :=
    lexDM_wt_lt_pair Aw hA₁ hA₂ _ _ rfl rfl hw₁ hw₂
  have hap : hA₁.AssumpPref ∧ hA₂.AssumpPref := ⟨hq.ap.1.1, hq.ap.2.1⟩
  have hbit := ih_local Aw tbl hq ih (.bitCoh hA₁ hA₂ S σ ρ)
    (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hap.1 hap.2) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  have hclA := ih_local Aw tbl hq ih (.cl hA₁ hA₂ S σ ρ)
    (Issues.occ_cl (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hap.1 hap.2) rfl
    (lexDM_combMeas_mono Aw _ hlex)
  exact eut_lam_nodes tbl ports.hTC σ ρ hA₁ hb₁ hB₁ hA₂ hb₂ hB₂ hbit hclA ports.convB

/-- `eut` app-app: the result-sort `ConvMod` is the cell's own goal (each
`app`'s `reg.2` is its `hT`), so it is never a port. What IS issuable:
`EUT hf₁ hf₂` at `(0,[0])×(1,[0])` and — on the relevant-domain branch —
`CL ha₁ ha₂` at `(0,[1])×(1,[1])`. The named ports are the Π-surface and
`instEnd` bridges plus the domain-bit coherence and `TableWF`, which `reg.2`/
`instEnd` composites keep off the payload grid. -/
structure EutAppPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a A₁ B₁ A₂ B₂ : Expr Nat} {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂)) : Prop where
  hW : TableWF tbl
  hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂)
  piL : CL tbl σ ρ hf₁.reg.2 (TyP.pi E n Γ A₁ u₁ B₁ v₁ hA₁ hB₁)
  piR : CL tbl σ ρ (TyP.pi E n Γ A₂ u₂ B₂ v₂ hA₂ hB₂) hf₂.reg.2
  instL : CL tbl σ ρ hT₁ (instEnd hB₁ ha₁ hA₁)
  instR : CL tbl σ ρ (instEnd hB₂ ha₂ hA₂) hT₂

theorem eut_app_app_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {f a A₁ B₁ A₂ B₂ : Expr Nat} {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁))
    (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A₂ (.sort u₂))
    (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : EutAppPorts tbl σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂ hA₁ hB₁ hA₂ hB₂) :
    CaseStep Aw tbl
      (.eut (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) S σ ρ) := fun hq ih => by
  have hwf₁ : hf₁.wt Aw < (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hwf₂ : hf₂.wt Aw < (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hwa₁ : ha₁.wt Aw < (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw := by
    simp only [TyP.wt]; omega
  have hwa₂ : ha₂.wt Aw < (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw := by
    simp only [TyP.wt]; omega
  have hlexf : LexDM (tyPairMeas Aw hf₁ hf₂)
      (tyPairMeas Aw (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂)) :=
    lexDM_wt_lt_pair Aw hf₁ hf₂ _ _ rfl rfl hwf₁ hwf₂
  have hlexa : LexDM (tyPairMeas Aw ha₁ ha₂)
      (tyPairMeas Aw (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
        (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂)) :=
    lexDM_wt_lt_pair Aw ha₁ ha₂ _ _ rfl rfl hwa₁ hwa₂
  have heutf := ih_local Aw tbl hq ih (.eut hf₁ hf₂ S σ ρ)
    (Issues.occ_eut (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
      hq.ap.1.1 hq.ap.2.1) rfl
    (lexDM_combMeas_mono Aw _ hlexf)
  cases hu : levelIsZero (σ u₁) with
  | true =>
      exact eut_app_nodes_drop ports.hW σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂
        hA₁ hB₁ hA₂ hB₂ hu ports.hbit heutf ports.piL ports.piR
        ports.instL ports.instR
  | false =>
      have hcla := ih_local Aw tbl hq ih (.cl ha₁ ha₂ S σ ρ)
        (Issues.occ_cl (k₁ := 0) (p₁ := [1]) (k₂ := 1) (p₂ := [1]) rfl rfl
          hq.ap.1.2.1 hq.ap.2.2.1) rfl
        (lexDM_combMeas_mono Aw _ hlexa)
      exact eut_app_nodes_keep ports.hW σ ρ hf₁ ha₁ hT₁ hf₂ ha₂ hT₂
        hA₁ hB₁ hA₂ hB₂ hu ports.hbit heutf hcla ports.piL ports.piR
        ports.instL ports.instR

/-- `eut` letE-letE: the result-sort `ConvMod` is the cell's goal (each
`letE`'s `reg.2` is its `hT`), so it is never a port. Decomposed through
`Lᵢ := letSub hbᵢ hvᵢ hAᵢ` (the zeta-reduct typings): the two regularity links
`CL hTᵢ Lᵢ.reg.2` and the reduct `EUT L₁ L₂` are the named ports — `letSub`
nodes are rebuilt `lsub` composites, not `subAt` positions, so no `occ_*` row
can issue them. -/
structure EutLetEPorts (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
    {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂)) : Prop where
  linkL : CL tbl σ ρ hT₁ (letSub hb₁ hv₁ hA₁).reg.2
  mid : EUT tbl σ ρ (letSub hb₁ hv₁ hA₁) (letSub hb₂ hv₂ hA₂)
  linkR : CL tbl σ ρ (letSub hb₂ hv₂ hA₂).reg.2 hT₂

theorem eut_letE_letE_caseStep_of_ports (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {A v b B₁ B₂ : Expr Nat}
    {u₁ w₁ u₂ w₂ : Level}
    (hA₁ : TyP E n Γ A (.sort u₁)) (hv₁ : TyP E n Γ v A)
    (hb₁ : TyP E n (.letBinding A v :: Γ) b B₁)
    (hT₁ : TyP E n Γ (instantiate0 v B₁) (.sort w₁))
    (hA₂ : TyP E n Γ A (.sort u₂)) (hv₂ : TyP E n Γ v A)
    (hb₂ : TyP E n (.letBinding A v :: Γ) b B₂)
    (hT₂ : TyP E n Γ (instantiate0 v B₂) (.sort w₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : EutLetEPorts tbl σ ρ hA₁ hv₁ hb₁ hT₁ hA₂ hv₂ hb₂ hT₂) :
    CaseStep Aw tbl
      (.eut (TyP.letE E n Γ A u₁ v B₁ b w₁ hA₁ hv₁ hb₁ hT₁)
        (TyP.letE E n Γ A u₂ v B₂ b w₂ hA₂ hv₂ hb₂ hT₂) S σ ρ) :=
  fun _ _ => by
    show ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ) (hT₂.eps σ ρ)
    exact ports.linkL.trans (ports.mid.trans ports.linkR)

/-- `eut` const-const: the result-sort `ConvMod` is the cell's goal (each
`const`'s `reg.2` is its `hT`), so it is never a port. The named ports are the
admission cell `TypeAdm E Aw r m` — a premise of the `const` judgment, not a
payload node — and the two admission-view bridges `q₁`/`q₂` relating each
instantiated typing's `eps` to `A.hT`'s (levels re-routed by `aliasᵢ`, context
prefix lifted). `LevelHom σ` is `hq.hom`. -/
structure EutConstPorts (Aw : Nat → Nat) (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (r : Nat)
    {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂)) : Type where
  adm : TypeAdm E Aw r m
  q₁ : ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ)
    (contextLift (ρ.take Γ.length)
      (adm.hT.eps (fun l => σ (instLevel ls₁ l)) (ρ.drop Γ.length)))
  q₂ : ConvMod (EStep tbl) LvlEq (hT₂.eps σ ρ)
    (contextLift (ρ.take Γ.length)
      (adm.hT.eps (fun l => σ (instLevel ls₂ l)) (ρ.drop Γ.length)))

theorem eut_const_const_caseStep_of_port (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {r : Nat}
    {ls ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hres₂ : E.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : EutConstPorts Aw tbl σ ρ r hT₁ hT₂) :
    CaseStep Aw tbl
      (.eut (TyP.const E n Γ r ls ls₁ m u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S σ ρ) :=
  fun hq _ =>
    eut_const_of_admission_views tbl ports.adm hres₁ hlen₁ hwf₁ hls₁ hT₁
      hres₂ hlen₂ hwf₂ hls₂ hT₂ hq.hom ρ ports.q₁ ports.q₂

/-! ## §5 `mixed` — measured, honest wall

`.mixed` issues `occ_*` only.  Its goal `CL ∧ EUT` on the moved pair sits at the
*same* rank as the pair's own `.cl`/`.eut` queries (`cl_not_before_mixed`,
`eut_not_before_mixed`), so no `Before`-orderable request can name the residuals —
the only honest port would be the goal itself, which the discipline forbids.
The composition is `mixed_step` (in-flight, #7498 `fable/mixed-worker-step`); this
file ships the controls, not the field. -/

/-- `.mixed` can issue the pair's `.cl` at the root paths — and `Before` refuses
it.  The two halves of the `mixed` goal are exactly the rank-equals its demand
cannot reach. -/
theorem mixed_occ_cl_dead_edge (Aw : Nat → Nat)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat}
    {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    Issues (.mixed D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) ∧
      ¬ Before Aw (.cl D₁ D₂ S σ ρ) (.mixed D₁ D₂ S σ ρ) ∧
      Issues (.mixed D₁ D₂ S σ ρ) (.eut D₁ D₂ S σ ρ) ∧
      ¬ Before Aw (.eut D₁ D₂ S σ ρ) (.mixed D₁ D₂ S σ ρ) :=
  ⟨Issues.occ_cl (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂,
    cl_not_before_mixed Aw D₁ D₂ S σ ρ,
    Issues.occ_eut (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂,
    eut_not_before_mixed Aw D₁ D₂ S σ ρ⟩

end Rcic.Syn
