import rcic.RcicSynStepSkeleton

/-!
# Design point A — whole-operand occurrence requests are same-rank local dependencies

Brief `~/.residua-devin-below/BRIEF.md` item 1, after the #7564 measure
(`cl_occ_self_unanswerable`, `mixed_occ_cl_self`, the eight same-rank `*_not_before_*` controls):
the landed grammar (`RcicSynP2Shared`) lets an `occ_*` row issue a request over the issuer's
**whole** operands (`subAt` at `(0,[])`/`(1,[])`), and such a request is never `Before` its
issuer. #7564 recorded these as "issuable but unanswerable" dead edges. `closure_claim = 0`.

**Verdict (compiled here): the edges are not dead, and the grammar needs no restriction.**
An issued edge can be consumed in exactly two ways, and the measure decides which:

* `Before Aw q' q` — through the IH (`ih_issue`); every landed IH call names such an edge.
* `q'.rank Aw = q.rank Aw` — never through the IH (`not_before_of_rank_eq`), but **as a
  same-rank local dependency**: the issuer's own `StepIH` *is* the target's
  (`stepIH_of_rank_eq`), so the target's `CaseStep` can be called directly
  (`SameRankDep.goal`). This is exactly how the landed skeleton already consumes the
  same-rank row `bitCoh_eut` (`step_of_suppliers`, `RcicSynStepSkeleton` §7, the `.bitCoh`
  arm; re-derived as `eut_of_bitCoh_sameRank`).

Every edge #7564 lists is the second kind (`SameRankDep`): `cl_mixed`, `eut_mixed`,
`bitCoh_eut`, and the whole-operand `occ_cl`/`occ_eut` rows out of `.mixed`/`.cl`/`.eut`/
`.bitCoh`. The only edge with no use at all is the literal self-loop
(`sameRankDep_cl_self`, target = issuer): consuming it needs the issuer's own case step, i.e.
the field itself, and it adds nothing to `Demand` (its target is already demanded).

**Consequence — the pair obligation is ONE object.** `cl_mixed`/`eut_mixed` issue `.mixed`
for EVERY demanded `.cl`/`.eut` pair (no premise), and the whole-operand rows issue `.cl` and
`.eut` back from `.mixed`. So on a pair `(D₁, D₂)` at one site, `.cl`, `.eut`, `.mixed` are one
same-rank strongly connected component of `Demand`, and the three `StepSuppliers` fields are
inter-derivable (`mixedField_iff`):

* `mixedField_of_cl_eut : ClField → EutField → MixedField`;
* `clField_of_mixed`, `eutField_of_mixed : MixedField → ClField / EutField`.

So `mixed_case` is not an independent obligation, and it is not "the moved pair's" obligation
either: it owes `CL ∧ EUT` on every demanded pair. A builder supplies the pair once — either
`cl_case` + `eut_case` (then `mixed_case := mixedField_of_cl_eut …`), or a full-pair `mixed_case`
(then the other two derive) — never both from each other (Lean refuses the cycle; the self-loop
is its degenerate case). `step_of_suppliers` still dispatches unchanged, with `mixed_case`
derived (`step_of_suppliers_derivedMixed`, `allBelowScoped_of_suppliers_derivedMixed`).

**Why not restrict `occ_*` to proper paths (brief option 1).** Not adopted, for three
reasons. (i) The restriction deletes the edges the pair reduction is proved with:
`mixedField_of_cl_eut` gets `Demand (.cl …)`/`Demand (.eut …)` from `Demand (.mixed …)` through the
whole-operand `occ_cl`/`occ_eut`; without them, a `.mixed` reached through `eut_mixed` would need a
separate derivation of its pair's `Demand (.cl …)`. None is given here. By inspection of the
`Issues` constructors (not compiled): the only row with an `.eut`/`.mixed` issuer and a `.cl` target
is `occ_cl`, and with both paths proper it cannot return the issuer's own two operands, since a
proper `subAt` is strictly lighter (`DNode.subAt_wt_lt`). (ii) A restricted relation defines a
different, smaller `Demand`; every
landed `CaseStep` closer consumes `StepIH` over the landed `Demand`, so none of them would transfer
(the restricted step would need a forked supplier layer). (iii) A path being proper does not decide
descent: the rank reads atom multisets, and a transport node (`wk`/`esub`/`lsub`/`linst`/`ewk`/
`cctx`) flattens its children's atoms into its own (`TyP.atoms`), so two proper occurrences taken
from one transport operand can outweigh the issuer. Descent is a property of the measure, which is
what `Before` and `SameRankDep` already state. (iii) is recorded, not compiled.

Nothing here edits a landed declaration; nothing is a producer of any field.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 rank-equal edges: never through the IH, always as a local dependency -/

/-- A query whose rank equals its issuer's is never `Before` it: `KeyLT` is irreflexive
    (`Nat.lt_irrefl` on the frame length, `lexDM_irrefl` on the local key). Generalises the
    #7564 controls (`before_irrefl`, the eight `*_not_before_*`) to every rank-equal pair. -/
theorem not_before_of_rank_eq (Aw : Nat → Nat) {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ}
    (h : q'.rank Aw = q.rank Aw) : ¬ Before Aw q' q := by
  intro hb
  have hk : KeyLT (q'.rank Aw) (q.rank Aw) := hb
  rw [h] at hk
  revert hk
  generalize q.rank Aw = k
  obtain ⟨a, b⟩ := k
  intro hk
  cases hk with
  | left _ _ hlt => exact Nat.lt_irrefl _ hlt
  | right _ hlt => exact lexDM_irrefl hlt

/-- **IH transfer.** `StepIH` reads only the rank of its query (`Before` is `KeyLT` of ranks), so
    a query of equal rank has the issuer's IH verbatim. -/
theorem stepIH_of_rank_eq (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    {q q' : P2Query Eₐ} (h : q'.rank Aw = q.rank Aw) (ih : StepIH Aw tbl q) :
    StepIH Aw tbl q' := by
  intro q'' hd hb
  apply ih q'' hd
  have hk : KeyLT (q''.rank Aw) (q'.rank Aw) := hb
  rw [h] at hk
  exact hk

/-- **A same-rank local dependency**: an actual `Issues` row whose target has the issuer's rank.
    Answer-free like `Issues`; the rank equation is a theorem of the two queries' objects. -/
structure SameRankDep (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q q' : P2Query Eₐ) : Prop where
  issues : Issues q q'
  rank_eq : q'.rank Aw = q.rank Aw

/-- The target of a same-rank dependency of a demanded query is demanded. -/
theorem SameRankDep.demand {Aw : Nat → Nat} {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ}
    (d : SameRankDep Aw q q') (hq : Demand q) : Demand q' :=
  .issued q q' hq d.issues

/-- A same-rank dependency is never an IH edge. -/
theorem SameRankDep.not_before {Aw : Nat → Nat} {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ}
    (d : SameRankDep Aw q q') : ¬ Before Aw q' q :=
  not_before_of_rank_eq Aw d.rank_eq

/-- The issuer's IH is the target's IH. -/
theorem SameRankDep.ih {Aw : Nat → Nat} {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ}
    (tbl : List CRule) (d : SameRankDep Aw q q') (ih : StepIH Aw tbl q) : StepIH Aw tbl q' :=
  stepIH_of_rank_eq Aw tbl d.rank_eq ih

/-- **Consumption of a same-rank dependency**: the target's case step, called at the target's
    derived demand with the issuer's own IH — the landed `bitCoh_eut` pattern, for any such
    edge. No `Before` is needed and none is claimed. -/
theorem SameRankDep.goal {Aw : Nat → Nat} {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ}
    (tbl : List CRule) (d : SameRankDep Aw q q') (step : CaseStep Aw tbl q')
    (hq : Demand q) (ih : StepIH Aw tbl q) : Goal tbl q' :=
  step (d.demand hq) (d.ih tbl ih)

/-! ## §2 the same-rank edges on one pair at one site (every #7564 "dead edge") -/

/-- `cl_mixed` (S17 moved pair). -/
theorem sameRankDep_cl_mixed (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    SameRankDep Aw (.cl D₁ D₂ S σ ρ) (.mixed D₁ D₂ S σ ρ) :=
  ⟨Issues.cl_mixed, rfl⟩

/-- `eut_mixed` (S17 moved pair). -/
theorem sameRankDep_eut_mixed (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    SameRankDep Aw (.eut D₁ D₂ S σ ρ) (.mixed D₁ D₂ S σ ρ) :=
  ⟨Issues.eut_mixed, rfl⟩

/-- `bitCoh_eut` (S9 §5 local data dependency). -/
theorem sameRankDep_bitCoh_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    SameRankDep Aw (.bitCoh D₁ D₂ S σ ρ) (.eut D₁ D₂ S σ ρ) :=
  ⟨Issues.bitCoh_eut, rfl⟩

/-- Whole-operand `occ_cl` out of `.mixed` (#7564 `mixed_occ_cl_self`). -/
theorem sameRankDep_mixed_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    SameRankDep Aw (.mixed D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) :=
  ⟨Issues.occ_cl (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂, rfl⟩

/-- Whole-operand `occ_eut` out of `.mixed`. -/
theorem sameRankDep_mixed_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    SameRankDep Aw (.mixed D₁ D₂ S σ ρ) (.eut D₁ D₂ S σ ρ) :=
  ⟨Issues.occ_eut (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂, rfl⟩

/-- Whole-operand `occ_cl` out of `.eut`: a demanded `EUT` pair demands its `CL`. -/
theorem sameRankDep_eut_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    SameRankDep Aw (.eut D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) :=
  ⟨Issues.occ_cl (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂, rfl⟩

/-- Whole-operand `occ_eut` out of `.cl`: a demanded `CL` pair demands its `EUT`. -/
theorem sameRankDep_cl_eut (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    SameRankDep Aw (.cl D₁ D₂ S σ ρ) (.eut D₁ D₂ S σ ρ) :=
  ⟨Issues.occ_eut (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂, rfl⟩

/-- Whole-operand `occ_cl` out of `.bitCoh`. -/
theorem sameRankDep_bitCoh_cl (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    SameRankDep Aw (.bitCoh D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) :=
  ⟨Issues.occ_cl (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂, rfl⟩

/-- **The degenerate case** (#7564 `cl_occ_self`): the literal self-loop. Its `SameRankDep.goal`
    is `CaseStep q → Demand q → StepIH q → Goal q` — the field itself, so it never supplies
    anything; and its target is the issuer, so it adds nothing to `Demand`. -/
theorem sameRankDep_cl_self (Aw : Nat → Nat) {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat}
    {Γ₀ Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref) :
    SameRankDep Aw (.cl D₁ D₂ S σ ρ) (.cl D₁ D₂ S σ ρ) :=
  ⟨Issues.occ_cl (k₁ := 0) (p₁ := []) (k₂ := 1) (p₂ := []) rfl rfl hap₁ hap₂, rfl⟩

/-- The skeleton's `.bitCoh` arm (`step_of_suppliers`, the `bitCoh_eut` local data dependency)
    is an instance of `SameRankDep.goal`: the dispatch already consumes a same-rank edge this way. -/
theorem eut_of_bitCoh_sameRank {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (step : CaseStep Aw tbl (.eut D₁ D₂ S σ ρ))
    (hq : Demand (.bitCoh D₁ D₂ S σ ρ)) (ih : StepIH Aw tbl (.bitCoh D₁ D₂ S σ ρ)) :
    EUT tbl σ ρ D₁ D₂ :=
  (sameRankDep_bitCoh_eut Aw D₁ D₂ S σ ρ).goal tbl step hq ih

/-! ## §3 the pair fields are one obligation -/

/-- The `StepSuppliers.cl_case` field statement (pinned by `StepSuppliers.clField`). -/
abbrev ClField (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.cl D₁ D₂ S σ ρ)

/-- The `StepSuppliers.eut_case` field statement (pinned by `StepSuppliers.eutField`). -/
abbrev EutField (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.eut D₁ D₂ S σ ρ)

/-- The `StepSuppliers.mixed_case` field statement (pinned by `StepSuppliers.mixedField`). -/
abbrev MixedField (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.mixed D₁ D₂ S σ ρ)

/-- Drift pin: `ClField` is the landed `cl_case` field. -/
theorem StepSuppliers.clField {Aw : Nat → Nat} {tbl : List CRule} {Eₐ : ResolvedEnv}
    (W : StepSuppliers Aw tbl Eₐ) : ClField Aw tbl Eₐ := W.cl_case

/-- Drift pin: `EutField` is the landed `eut_case` field. -/
theorem StepSuppliers.eutField {Aw : Nat → Nat} {tbl : List CRule} {Eₐ : ResolvedEnv}
    (W : StepSuppliers Aw tbl Eₐ) : EutField Aw tbl Eₐ := W.eut_case

/-- Drift pin: `MixedField` is the landed `mixed_case` field. -/
theorem StepSuppliers.mixedField {Aw : Nat → Nat} {tbl : List CRule} {Eₐ : ResolvedEnv}
    (W : StepSuppliers Aw tbl Eₐ) : MixedField Aw tbl Eₐ := W.mixed_case

/-- **`mixed_case` from `cl_case` and `eut_case`.** A demanded `.mixed` demands its own `.cl`
    and `.eut` through the whole-operand rows, at its own rank; their case steps are called with
    the `.mixed` query's IH. -/
theorem mixedField_of_cl_eut (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (hcl : ClField Aw tbl Eₐ) (heut : EutField Aw tbl Eₐ) : MixedField Aw tbl Eₐ := by
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ ρ hq ih
  have hap : D₁.AssumpPref ∧ D₂.AssumpPref := hq.ap
  show CL tbl σ ρ D₁ D₂ ∧ EUT tbl σ ρ D₁ D₂
  exact ⟨(sameRankDep_mixed_cl Aw D₁ D₂ S σ ρ hap.1 hap.2).goal tbl (hcl D₁ D₂ S σ ρ) hq ih,
    (sameRankDep_mixed_eut Aw D₁ D₂ S σ ρ hap.1 hap.2).goal tbl (heut D₁ D₂ S σ ρ) hq ih⟩

/-- **`cl_case` from a full-pair `mixed_case`** (row `cl_mixed`, no premise). -/
theorem clField_of_mixed (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (hmix : MixedField Aw tbl Eₐ) : ClField Aw tbl Eₐ := by
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ ρ hq ih
  have h : CL tbl σ ρ D₁ D₂ ∧ EUT tbl σ ρ D₁ D₂ :=
    (sameRankDep_cl_mixed Aw D₁ D₂ S σ ρ).goal tbl (hmix D₁ D₂ S σ ρ) hq ih
  exact h.1

/-- **`eut_case` from a full-pair `mixed_case`** (row `eut_mixed`, no premise). -/
theorem eutField_of_mixed (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (hmix : MixedField Aw tbl Eₐ) : EutField Aw tbl Eₐ := by
  intro E₀ n₀ Γ₀ E n Γ e T₁ T₂ D₁ D₂ S σ ρ hq ih
  have h : CL tbl σ ρ D₁ D₂ ∧ EUT tbl σ ρ D₁ D₂ :=
    (sameRankDep_eut_mixed Aw D₁ D₂ S σ ρ).goal tbl (hmix D₁ D₂ S σ ρ) hq ih
  exact h.2

/-- The three pair fields carry one obligation. -/
theorem mixedField_iff (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) :
    MixedField Aw tbl Eₐ ↔ ClField Aw tbl Eₐ ∧ EutField Aw tbl Eₐ :=
  ⟨fun hmix => ⟨clField_of_mixed Aw tbl hmix, eutField_of_mixed Aw tbl hmix⟩,
    fun h => mixedField_of_cl_eut Aw tbl h.1 h.2⟩

/-- A supplier record whose `mixed_case` is the derived one — the reduction's statement fills the
    landed field exactly. -/
theorem StepSuppliers.withDerivedMixed {Aw : Nat → Nat} {tbl : List CRule} {Eₐ : ResolvedEnv}
    (W : StepSuppliers Aw tbl Eₐ) : StepSuppliers Aw tbl Eₐ :=
  { W with mixed_case := mixedField_of_cl_eut Aw tbl W.cl_case W.eut_case }

/-- `step_of_suppliers` still dispatches, with `mixed_case` derived from `cl_case`/`eut_case`. -/
theorem step_of_suppliers_derivedMixed {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ) : Step Aw tbl Eₐ :=
  step_of_suppliers Aw tbl hTbl W.withDerivedMixed

/-- The S15 §6 chain with `mixed_case` derived. Conditional on `W`'s other fields. -/
theorem allBelowScoped_of_suppliers_derivedMixed {Eₐ : ResolvedEnv} (Aw : Nat → Nat)
    (tbl : List CRule) (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ) :
    AllBelowScoped Eₐ Aw tbl :=
  allBelowScoped_of_suppliers Aw tbl hTbl W.withDerivedMixed

end Rcic.Syn
