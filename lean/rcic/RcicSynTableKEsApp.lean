import rcic.RcicSynTableKCompat
import rcic.RcicSynClosedEsapp
import rcic.RcicSynStepFields2
import rcic.RcicSynSRClEutTransport

/-!
# `es_app` row 8 at `tableOfK` — `leftCl` issued, `drClause` measured (cc 22:52Z)

The `es_app` supplier's landed residue is `EsAppClosedPorts`
(`RcicSynClosedEsapp`): twelve fields, eleven already weakened to `∨`
receipts. This module takes the two remaining walls cc named — `leftCl`
(`CL[dl, appLeftSurface]`) and `drClause` (`AppClauseNeed(dr)`) — under the
`tableOfK` retarget (`RcicSynTableKCompat`).

## `leftCl` — DISCHARGED as an IH query

`appLeftSurface h1 h2 dl` is a fresh node (no `subAt` path — the reason
`occ_cl` could never serve it), but the `.cl` kind does not need `subAt`
membership: it is a **same-subject** pair (`dl` and the surface both type
`.app f a` at `instantiate0 a B`), and `appLeftSurface_wt_lt` already proves
the surface strictly lighter than the `CvP.app` node. The row
`IssuesCTK.cl_app_leftSurface` issues `.cl dl (appLeftSurface h1 h2 dl)` in
the issuer's own frame; `IssuesCTK.ap` discharges the issued pair's
`AssumpPref` by `appLeftSurface_ap` from the node's own; `dmStep_pair_below`
(whose premises are weight bounds only, not `subAt` receipts) + `hwdl` +
`appLeftSurface_wt_lt` give the `Before` edge. The issued `Goal` *is* the
`leftCl` `.inl` — so `EsAppKPorts` drops the field entirely.

## `drClause` — retained as the named wall

`dr.eps σ ρ = appClause (R.hf.eps σ ρ) (R.ha.eps σ ρ)` is a literal `ETm`
equation — the same wall class as `letCl`'s `shape`: **no query kind answers
`Eq`**. `appSource` decodes through the full transport spine
(`wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx`/`conv`), so the equation is only
*proved* on the `DrAppHead` region (`drAppHead_clause`: bare `TyP.app` or
one `.conv`, where `eps` peels and the decoder returns the stored fields).
Off that region the clause is `tbl`-independent but not known to hold:
`esub`-keep spines whose value erases to `★` falsify the shape
(`inst_appClause_star_ne`'s counterexample class). The `∨ DrAppHead`
weakening is kept verbatim — the measured honest wall.

## Table transfer

Every lemma here is `tbl`-parametric (or uses `tableOfK`-specific facts via
`RcicSynTableKCompat`); `es_app_caseStepCTK_tableK` pins the cell at
`tableOfK hW`. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `IssuesCTK` — `IssuesCT` plus the `appLeftSurface` CL row -/

/-- `IssuesCT` plus the row-8 `es_app` left-surface issue: the `.cl` query on
    `dl` against the reconstructed `appLeftSurface`. The pair is same-subject
    (`.app f a`), the surface's `AssumpPref`/`wt` bounds are landed
    (`appLeftSurface_ap`, `appLeftSurface_wt_lt`), and the display is the
    issuer's own (`S`, `σ`, `ρ`) — no `subAt` membership is required since the
    `.cl` kind takes derivations by weight, not by occurrence. -/
inductive IssuesCTK {Eₐ : ResolvedEnv} : P2Query Eₐ → P2Query Eₐ → Prop where
  | old {q q' : P2Query Eₐ} (h : IssuesCT q q') : IssuesCTK q q'
  | cl_app_leftSurface {E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
      {f g a b A B : Expr Nat}
      (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
      (dl : TyP E n Γ (.app f a) (instantiate0 a B))
      (dr : TyP E n Γ (.app g b) (instantiate0 a B))
      (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
      IssuesCTK (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        (.cl dl (appLeftSurface h1 h2 dl) S σ ρ)

/-- The demand closure under `IssuesCTK`. -/
inductive DemandCTK {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop where
  | old {q : P2Query Eₐ} (h : DemandCT q) : DemandCTK q
  | issued (issuer target : P2Query Eₐ) :
      DemandCTK issuer → IssuesCTK issuer target → DemandCTK target

/-- `cl_app_leftSurface`'s issued pair is `AssumpPref` once the issuer's is:
    `dl`'s from the node's own `AssumpPref`, the surface's by
    `appLeftSurface_ap` over the `h1`/`h2`/`dl` components. -/
theorem IssuesCTK.ap {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.AP)
    (e : IssuesCTK q q') : q'.AP := by
  cases e with
  | old h => exact IssuesCT.ap hi h
  | cl_app_leftSurface h1 h2 dl dr _ _ _ =>
      exact ⟨hi.2.2.1, appLeftSurface_ap h1 h2 dl hi.1 hi.2.1 hi.2.2.1⟩

/-- The issued query keeps the issuer's level map. -/
theorem IssuesCTK.hom {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hi : q.Hom)
    (e : IssuesCTK q q') : q'.Hom := by
  cases e with
  | old h => exact IssuesCT.hom hi h
  | _ => exact hi

/-- The issued query keeps the issuer's display verbatim — same `ρ`. -/
theorem IssuesCTK.routed {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hr : q.Routed)
    (e : IssuesCTK q q') : q'.Routed := by
  cases e with
  | old h => exact IssuesCT.routed hr h
  | _ => exact hr

/-- The CTK closure preserves `AP`. -/
theorem DemandCTK.ap {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandCTK q) :
    q.AP := by
  induction hq with
  | old h => exact DemandCT.ap h
  | issued _ _ _ e ih => exact IssuesCTK.ap ih e

/-- The CTK closure preserves `LevelHom`. -/
theorem DemandCTK.hom {Eₐ : ResolvedEnv} {q : P2Query Eₐ} (hq : DemandCTK q) :
    q.Hom := by
  induction hq with
  | old h => exact DemandCT.hom h
  | issued _ _ _ e ih => exact IssuesCTK.hom ih e

/-- The CTK closure preserves routedness. -/
theorem DemandCTK.routed {Eₐ : ResolvedEnv} {q : P2Query Eₐ}
    (hq : DemandCTK q) : q.Routed := by
  induction hq with
  | old h => exact DemandCT.routed h
  | issued _ _ _ e ih => exact IssuesCTK.routed ih e

/-! ## §2 the CTK step obligation -/

/-- `StepIH` over the K demand closure. -/
abbrev StepIHCTK (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  ∀ q' : P2Query Eₐ, DemandCTK q' → Before Aw q' q → Goal tbl q'

/-- The per-case step obligation over the K closure. -/
abbrev CaseStepCTK (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv}
    (q : P2Query Eₐ) : Prop :=
  DemandCTK q → StepIHCTK Aw tbl q → Goal tbl q

/-- The semantic answer of a K-issued strictly-smaller sub-request. -/
theorem ih_issueCTK {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {q : P2Query Eₐ} (hq : DemandCTK q) (ih : StepIHCTK Aw tbl q)
    (q' : P2Query Eₐ) (e : IssuesCTK q q') (hb : Before Aw q' q) :
    Goal tbl q' :=
  ih q' (.issued q q' hq e) hb

/-- An IH call on a K-issued sub-request in the same frame at a strictly
    smaller local key. -/
theorem ih_localCTK {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {q : P2Query Eₐ} (hq : DemandCTK q) (ih : StepIHCTK Aw tbl q)
    (q' : P2Query Eₐ) (e : IssuesCTK q q')
    (hp : q'.originalPrefixLength = q.originalPrefixLength)
    (hk : LexDM (q'.localKey Aw) (q.localKey Aw)) : Goal tbl q' :=
  ih_issueCTK Aw tbl hq ih q' e (before_of_same_prefix Aw hp hk)

/-- The fixpoint lift over the K closure — `solve_of_stepCT` verbatim over
    `DemandCTK`. -/
theorem solve_of_stepCTK {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : ∀ q : P2Query Eₐ, DemandCTK q →
      (∀ q' : P2Query Eₐ, DemandCTK q' → Before Aw q' q → Goal tbl q') →
      Goal tbl q) :
    ∀ q : P2Query Eₐ, DemandCTK q → Goal tbl q := by
  have allAt : ∀ k : Key, ∀ q : P2Query Eₐ, q.rank Aw = k →
      DemandCTK q → Goal tbl q :=
    keyLT_wf.fix (fun k ih q hkey hq =>
      step q hq (fun q' hq' hlt =>
        ih (q'.rank Aw) (by unfold Before at hlt; rwa [hkey] at hlt) q' rfl hq'))
  intro q hq
  exact allAt (q.rank Aw) q rfl hq

/-! ## §3 CTK mirrors of the `ih`-consuming helpers -/

/-- `es_issued_occ_cl` at the K closure: the `occ_cl` row is `Issues` and
    rides the `.old` chain; the `Before` discharge is unchanged. -/
theorem es_issued_occ_cl_CTK (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : CvP E n Γ a b T) (hc : c.isTransport = false)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (p₁ p₂ : List Nat)
    (hocc₁ : P2Query.subAt (.es c S σ ρ) 0 p₁ = some (.ty D₁))
    (hocc₂ : P2Query.subAt (.es c S σ ρ) 0 p₂ = some (.ty D₂))
    (hap₁ : D₁.AssumpPref) (hap₂ : D₂.AssumpPref)
    (hq : DemandCTK (.es c S σ ρ)) (ih : StepIHCTK Aw tbl (.es c S σ ρ)) :
    CL tbl σ ρ D₁ D₂ := by
  have hp₁ : p₁ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₁
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₁
    exact DNode.noConfusion (Option.some.inj hocc₁)
  have hp₂ : p₂ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₂
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₂
    exact DNode.noConfusion (Option.some.inj hocc₂)
  have hw₁ : D₁.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₁ hp₁ _ _ hocc₁
  have hw₂ : D₂.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₂ hp₂ _ _ hocc₂
  exact ih_issueCTK Aw tbl hq ih (.cl D₁ D₂ S σ ρ)
    (.old (.old (.old (Issues.occ_cl hocc₁ hocc₂ hap₁ hap₂))))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw c hc D₁ D₂ hw₁ hw₂))))

/-- `es_issued_occ_pb` at the K closure. -/
theorem es_issued_occ_pb_CTK (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : CvP E n Γ a b T) (hc : c.isTransport = false)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {e T' : Expr Nat} {u : Level}
    (D : TyP E n Γ e T') (DT : TyP E n Γ T' (.sort u))
    (p₁ p₂ : List Nat)
    (hocc₁ : P2Query.subAt (.es c S σ ρ) 0 p₁ = some (.ty D))
    (hocc₂ : P2Query.subAt (.es c S σ ρ) 0 p₂ = some (.ty DT))
    (hap₁ : D.AssumpPref) (hap₂ : DT.AssumpPref)
    (hq : DemandCTK (.es c S σ ρ)) (ih : StepIHCTK Aw tbl (.es c S σ ρ)) :
    PBit σ ρ D DT := by
  have hp₁ : p₁ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₁
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₁
    exact DNode.noConfusion (Option.some.inj hocc₁)
  have hp₂ : p₂ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₂
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₂
    exact DNode.noConfusion (Option.some.inj hocc₂)
  have hw₁ : D.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₁ hp₁ _ _ hocc₁
  have hw₂ : DT.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₂ hp₂ _ _ hocc₂
  exact ih_issueCTK Aw tbl hq ih (.pb D DT S σ ρ)
    (.old (.old (.old (Issues.occ_pb hocc₁ hocc₂ hap₁ hap₂))))
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw c hc D DT hw₁ hw₂))))

/-- `es_app_ih_fun` at the K closure: `app_es1` issues `h1`'s `ES` request. -/
theorem es_app_ih_fun_CTK (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : DemandCTK (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ))
    (ih : StepIHCTK Aw tbl
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)) :
    ES tbl σ ρ h1 :=
  ih_issueCTK Aw tbl hq ih (.es h1 S σ ρ)
    (.old (.old (.old .app_es1)))
    (rule_sub_before Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl h1
      (by simp only [CvP.wt]; omega) S σ ρ ρ)

/-- `es_app_ih_arg` at the K closure. -/
theorem es_app_ih_arg_CTK (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : DemandCTK (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ))
    (ih : StepIHCTK Aw tbl
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)) :
    ES tbl σ ρ h2 :=
  ih_issueCTK Aw tbl hq ih (.es h2 S σ ρ)
    (.old (.old (.old .app_es2)))
    (rule_sub_before Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl h2
      (by simp only [CvP.wt]; omega) S σ ρ ρ)

/-! ## §4 the K port record and the issued `leftCl` -/

/-- `EsAppClosedPorts` minus `leftCl` — the `cl_app_leftSurface` row issues
    it. Every remaining field keeps its `∨`-receipt weakening verbatim. -/
structure EsAppKPorts (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Prop where
  occH1 : (∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty h1.dr)) ∨ h1.isTransport = false
  occH2 : (∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty h2.dr)) ∨ h2.isTransport = false
  occF : (∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty (appSource dr rfl).hf)) ∨ DrAppHead dr
  occA : (∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty (appSource dr rfl).ha)) ∨ DrAppHead dr
  pbFunL : PBit σ ρ h1.dl h1.dl.reg.2 ∨
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h1.dl) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h1.dl.reg.2)
  pbFunR : PBit σ ρ h1.dr h1.dl.reg.2 ∨
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h1.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h1.dl.reg.2)
  pbArgL : PBit σ ρ h2.dl h2.dl.reg.2 ∨
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h2.dl) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h2.dl.reg.2)
  pbArgR : PBit σ ρ h2.dr h2.dl.reg.2 ∨
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h2.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h2.dl.reg.2)
  funTag : TagCoh σ ρ σ ρ h1.dr ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) ∨
    ∃ pD pF pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h1.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pF = some (.ty ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h1.dl.reg.2) ∧
      A = (appSource dr rfl).A ∧ B = (appSource dr rfl).B
  argTag : TagCoh σ ρ σ ρ h2.dr ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) ∨
    ∃ pD pA pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h2.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pA = some (.ty ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h2.dl.reg.2) ∧
      A = (appSource dr rfl).A
  /-- the retained wall: `AppClauseNeed(dr)` or `dr` application-headed. The
      `.inl` is a raw `ETm` equation — no query kind answers `Eq` — so the
      `∨ DrAppHead` weakening stays verbatim. -/
  drClause : dr.eps σ ρ = appClause ((appSource dr rfl).hf.eps σ ρ)
      ((appSource dr rfl).ha.eps σ ρ) ∨ DrAppHead dr

/-- `EsAppClosedPorts → EsAppKPorts` — the K record is the closed record with
    `leftCl` dropped: the premise is weakened, never strengthened. -/
theorem esAppKPorts_of_closed (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (c : EsAppClosedPorts Aw tbl h1 h2 dl dr S σ ρ) :
    EsAppKPorts Aw tbl h1 h2 dl dr S σ ρ where
  occH1 := c.occH1
  occH2 := c.occH2
  occF := c.occF
  occA := c.occA
  pbFunL := c.pbFunL
  pbFunR := c.pbFunR
  pbArgL := c.pbArgL
  pbArgR := c.pbArgR
  funTag := c.funTag
  argTag := c.argTag
  drClause := c.drClause

/-- `es_app_field`'s tail at the K closure — identical clause chain, but the
    issued pieces come from `ih_issueCTK`. The `AppPorts` fields `leftCl`/
    `drClause` are supplied; everything else re-derives. -/
theorem es_app_field_CTK (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : AppPorts Aw tbl h1 h2 dl dr S σ ρ) :
    CaseStepCTK Aw tbl (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) := by
  intro hq ih
  obtain ⟨hap1, hap2, hapdl, hapdr⟩ := hq.ap
  obtain ⟨pH1, occH1⟩ := ports.occH1
  obtain ⟨pH2, occH2⟩ := ports.occH2
  obtain ⟨pF, occF⟩ := ports.occF
  obtain ⟨pA, occA⟩ := ports.occA
  have hapF : ((appSource dr rfl).feq ▸ (appSource dr rfl).hf).AssumpPref :=
    TyP.ap_castS (appSource dr rfl).feq (appSource dr rfl).hf ▸
      (appSource_ap dr rfl hapdr).1
  have occF' :
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 pF =
        some (.ty ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)) := by
    rw [dnode_ty_castS (appSource dr rfl).feq (appSource dr rfl).hf]
    exact occF
  have hclF : CL tbl σ ρ h1.dr
      ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) :=
    es_issued_occ_cl_CTK Aw tbl (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl
      S σ ρ h1.dr _ pH1 pF occH1 occF' (assumpPref_dr hap1) hapF hq ih
  have hapA : ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha).AssumpPref :=
    TyP.ap_castS (appSource dr rfl).aeq (appSource dr rfl).ha ▸
      (appSource_ap dr rfl hapdr).2
  have occA' :
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 pA =
        some (.ty ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)) := by
    rw [dnode_ty_castS (appSource dr rfl).aeq (appSource dr rfl).ha]
    exact occA
  have hclA : CL tbl σ ρ h2.dr
      ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) :=
    es_issued_occ_cl_CTK Aw tbl (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl
      S σ ρ h2.dr _ pH2 pA occH2 occA' (assumpPref_dr hap2) hapA hq ih
  have hf_es : ConvMod (EStep tbl) LvlEq (h1.dl.eps σ ρ) (h1.dr.eps σ ρ) :=
    es_app_ih_fun_CTK Aw tbl h1 h2 dl dr S σ ρ hq ih
  have ha_es : ConvMod (EStep tbl) LvlEq (h2.dl.eps σ ρ) (h2.dr.eps σ ρ) :=
    es_app_ih_arg_CTK Aw tbl h1 h2 dl dr S σ ρ hq ih
  have hsf : (h1.dl.eps σ ρ = .star) ↔ (h1.dr.eps σ ρ = .star) :=
    ports.pbFunL.trans ports.pbFunR.symm
  have hsa : (h2.dl.eps σ ρ = .star) ↔ (h2.dr.eps σ ρ = .star) :=
    ports.pbArgL.trans ports.pbArgR.symm
  have hsf' : (h1.dr.eps σ ρ = .star) ↔
      (((appSource dr rfl).feq ▸ (appSource dr rfl).hf).eps σ ρ = .star) :=
    ports.funTag
  have hsa' : (h2.dr.eps σ ρ = .star) ↔
      (((appSource dr rfl).aeq ▸ (appSource dr rfl).ha).eps σ ρ = .star) :=
    ports.argTag
  have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (appClause (h1.dl.eps σ ρ) (h2.dl.eps σ ρ)) :=
    appLeftSurface_eps h1 h2 dl σ ρ ▸ ports.leftCl
  have hMid : ConvMod (EStep tbl) LvlEq
      (appClause (h1.dl.eps σ ρ) (h2.dl.eps σ ρ))
      (appClause (h1.dr.eps σ ρ) (h2.dr.eps σ ρ)) :=
    convMod_appClause hf_es ha_es hsf hsa
  have hMidR : ConvMod (EStep tbl) LvlEq
      (appClause (h1.dr.eps σ ρ) (h2.dr.eps σ ρ))
      (appClause (((appSource dr rfl).feq ▸ (appSource dr rfl).hf).eps σ ρ)
        (((appSource dr rfl).aeq ▸ (appSource dr rfl).ha).eps σ ρ)) :=
    convMod_appClause hclF hclA hsf' hsa'
  have hR : ConvMod (EStep tbl) LvlEq
      (appClause (((appSource dr rfl).feq ▸ (appSource dr rfl).hf).eps σ ρ)
        (((appSource dr rfl).aeq ▸ (appSource dr rfl).ha).eps σ ρ))
      (dr.eps σ ρ) := by
    rw [TyP.eps_castS (appSource dr rfl).feq (appSource dr rfl).hf,
      TyP.eps_castS (appSource dr rfl).aeq (appSource dr rfl).ha,
      ← ports.drClause]
    exact .refl _
  exact hL.trans (hMid.trans (hMidR.trans hR))

/-- `es_app` under `EsAppKPorts` at the K closure: `leftCl` is issued via
    `cl_app_leftSurface` + `ih_localCTK` (`dl.wt` and `appLeftSurface_wt_lt`
    give the `Before`); the remaining ports discharge exactly as in
    `es_app_field_closed`, and `drClause` stays the named `∨ DrAppHead`
    wall. -/
theorem es_app_caseStepCTK (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (c : EsAppKPorts Aw tbl h1 h2 dl dr S σ ρ) :
    CaseStepCTK Aw tbl (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) := by
  intro hq ih
  obtain ⟨hap1, hap2, hapdl, hapdr⟩ := hq.ap
  have hleftCl : CL tbl σ ρ dl (appLeftSurface h1 h2 dl) := by
    have hwdl : dl.wt Aw <
        (CvP.app E n Γ f g a b A B h1 h2 dl dr).wt Aw := by
      simp only [CvP.wt]; omega
    exact ih_localCTK Aw tbl hq ih (.cl dl (appLeftSurface h1 h2 dl) S σ ρ)
      (.cl_app_leftSurface h1 h2 dl dr S σ ρ) rfl
      (lexDM_combMeas_mono Aw _ (lex_of_dm
        (dmStep_pair_below Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl
          dl (appLeftSurface h1 h2 dl) hwdl
          (appLeftSurface_wt_lt Aw h1 h2 dl dr))))
  have hoccH1 : ∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty h1.dr) := by
    rcases c.occH1 with h | ht
    · exact h
    · exact es_app_occH1_closed h1 h2 dl dr S σ ρ ht
  have hoccH2 : ∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty h2.dr) := by
    rcases c.occH2 with h | ht
    · exact h
    · exact es_app_occH2_closed h1 h2 dl dr S σ ρ ht
  have hoccF : ∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty (appSource dr rfl).hf) := by
    rcases c.occF with h | hd
    · exact h
    · exact drAppHead_occF h1 h2 dl hd S σ ρ
  have hoccA : ∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty (appSource dr rfl).ha) := by
    rcases c.occA with h | hd
    · exact h
    · exact drAppHead_occA h1 h2 dl hd S σ ρ
  have hpbFunL : PBit σ ρ h1.dl h1.dl.reg.2 := by
    rcases c.pbFunL with h | ⟨pD, pT, hD, hT'⟩
    · exact h
    · exact es_issued_occ_pb_CTK Aw tbl
        (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
        h1.dl h1.dl.reg.2 pD pT hD hT' (assumpPref_dl hap1)
        (assumpPref_reg (assumpPref_dl hap1)) hq ih
  have hpbFunR : PBit σ ρ h1.dr h1.dl.reg.2 := by
    rcases c.pbFunR with h | ⟨pD, pT, hD, hT'⟩
    · exact h
    · exact es_issued_occ_pb_CTK Aw tbl
        (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
        h1.dr h1.dl.reg.2 pD pT hD hT' (assumpPref_dr hap1)
        (assumpPref_reg (assumpPref_dl hap1)) hq ih
  have hpbArgL : PBit σ ρ h2.dl h2.dl.reg.2 := by
    rcases c.pbArgL with h | ⟨pD, pT, hD, hT'⟩
    · exact h
    · exact es_issued_occ_pb_CTK Aw tbl
        (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
        h2.dl h2.dl.reg.2 pD pT hD hT' (assumpPref_dl hap2)
        (assumpPref_reg (assumpPref_dl hap2)) hq ih
  have hpbArgR : PBit σ ρ h2.dr h2.dl.reg.2 := by
    rcases c.pbArgR with h | ⟨pD, pT, hD, hT'⟩
    · exact h
    · exact es_issued_occ_pb_CTK Aw tbl
        (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
        h2.dr h2.dl.reg.2 pD pT hD hT' (assumpPref_dr hap2)
        (assumpPref_reg (assumpPref_dl hap2)) hq ih
  have hfunTag : TagCoh σ ρ σ ρ h1.dr
      ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) := by
    rcases c.funTag with h | ⟨pD, pF, pT, hD, hF, hT', hAA, hBB⟩
    · exact h
    · have hPi : Expr.pi A B =
          Expr.pi (appSource dr rfl).A (appSource dr rfl).B :=
        congr (congrArg Expr.pi hAA) hBB
      have pbR : PBit σ ρ h1.dr h1.dl.reg.2 :=
        es_issued_occ_pb_CTK Aw tbl
          (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
          h1.dr h1.dl.reg.2 pD pT hD hT' (assumpPref_dr hap1)
          (assumpPref_reg (assumpPref_dl hap1)) hq ih
      have pbF : PBit σ ρ ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)
          (hPi ▸ h1.dl.reg.2 : TyP E n Γ
            (.pi (appSource dr rfl).A (appSource dr rfl).B)
            (.sort h1.dl.reg.1)) :=
        es_issued_occ_pb_CTK Aw tbl
          (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
          ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)
          (hPi ▸ h1.dl.reg.2 : TyP E n Γ
            (.pi (appSource dr rfl).A (appSource dr rfl).B)
            (.sort h1.dl.reg.1))
          pF pT hF
          (hT'.trans (congrArg some (dnode_ty_castS hPi h1.dl.reg.2).symm))
          (Eq.mpr (TyP.ap_castS (appSource dr rfl).feq (appSource dr rfl).hf)
            (appSource_ap dr rfl hapdr).1)
          (Eq.mpr (TyP.ap_castS hPi h1.dl.reg.2)
            (assumpPref_reg (assumpPref_dl hap1))) hq ih
      exact pbR.trans pbF.symm
  have hargTag : TagCoh σ ρ σ ρ h2.dr
      ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) := by
    rcases c.argTag with h | ⟨pD, pA, pT, hD, hA', hT', hAA⟩
    · exact h
    · have pbR : PBit σ ρ h2.dr h2.dl.reg.2 :=
        es_issued_occ_pb_CTK Aw tbl
          (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
          h2.dr h2.dl.reg.2 pD pT hD hT' (assumpPref_dr hap2)
          (assumpPref_reg (assumpPref_dl hap2)) hq ih
      have pbA : PBit σ ρ ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)
          (hAA ▸ h2.dl.reg.2 : TyP E n Γ (appSource dr rfl).A
            (.sort h2.dl.reg.1)) :=
        es_issued_occ_pb_CTK Aw tbl
          (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
          ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)
          (hAA ▸ h2.dl.reg.2 : TyP E n Γ (appSource dr rfl).A
            (.sort h2.dl.reg.1))
          pA pT hA'
          (hT'.trans (congrArg some (dnode_ty_castS hAA h2.dl.reg.2).symm))
          (Eq.mpr (TyP.ap_castS (appSource dr rfl).aeq (appSource dr rfl).ha)
            (appSource_ap dr rfl hapdr).2)
          (Eq.mpr (TyP.ap_castS hAA h2.dl.reg.2)
            (assumpPref_reg (assumpPref_dl hap2))) hq ih
      exact pbR.trans pbA.symm
  have hdrClause : dr.eps σ ρ = appClause ((appSource dr rfl).hf.eps σ ρ)
      ((appSource dr rfl).ha.eps σ ρ) := by
    rcases c.drClause with h | hd
    · exact h
    · exact drAppHead_clause hd σ ρ
  exact es_app_field_CTK Aw tbl h1 h2 dl dr S σ ρ
    { leftCl := hleftCl
      occH1 := hoccH1
      occH2 := hoccH2
      occF := hoccF
      occA := hoccA
      pbFunL := hpbFunL
      pbFunR := hpbFunR
      pbArgL := hpbArgL
      pbArgR := hpbArgR
      funTag := hfunTag
      argTag := hargTag
      drClause := hdrClause } hq ih

/-! ## §5 fixture and `tableOfK` pins -/

/-- `EsAppKPorts` is inhabited at the `esapp` fixture with **every** field's
    `.inr` receipt — `leftCl` needs no receipt at all (it is issued). -/
theorem esAppKPorts_fixture :
    EsAppKPorts (fun _ => 0) [] esappH1 esappH2 esappDl esappDl
      nilScope id [.keep, .keep] where
  occH1 := .inr rfl
  occH2 := .inr rfl
  occF := .inr esappDrHead
  occA := .inr esappDrHead
  pbFunL := .inr ⟨[0, 1], [0, 1, 0], rfl, rfl⟩
  pbFunR := .inr ⟨[0, 2], [0, 1, 0], rfl, rfl⟩
  pbArgL := .inr ⟨[1, 1], [1, 1, 0], rfl, rfl⟩
  pbArgR := .inr ⟨[1, 2], [1, 1, 0], rfl, rfl⟩
  funTag := .inr ⟨[0, 2], [3, 0], [0, 1, 0], rfl, rfl, rfl, rfl, rfl⟩
  argTag := .inr ⟨[1, 2], [3, 1], [1, 1, 0], rfl, rfl, rfl, rfl⟩
  drClause := .inr esappDrHead

/-- The assembled `CaseStepCTK` at the fixture: `leftCl` issued, every other
    port on `.inr` receipts, `drClause` on `esappDrHead`. -/
theorem es_app_caseStepCTK_fixture :
    CaseStepCTK (fun _ => 0) []
      (.es (CvP.app emptyEnv 0 esappFixtureΓ (.bvar 1) (.bvar 1) (.bvar 0)
        (.bvar 0) (.sort .zero) (.sort .zero) esappH1 esappH2 esappDl esappDl)
        nilScope id [.keep, .keep]) :=
  es_app_caseStepCTK (fun _ => 0) [] esappH1 esappH2 esappDl esappDl
    nilScope id [.keep, .keep] esAppKPorts_fixture

/-- The `es_app` cell pinned at `tableOfK`: the cell is `tbl`-parametric, so
    the K target is instantiation — the `es_*`/`convMod`/`appClause` layer
    carries `EStep (tableOfK hW)`. -/
theorem es_app_caseStepCTK_tableK {E : ResolvedEnv} (hW : EnvWfT E)
    (Aw : Nat → Nat)
    {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (c : EsAppKPorts Aw (tableOfK hW) h1 h2 dl dr S σ ρ) :
    CaseStepCTK Aw (tableOfK hW)
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) :=
  es_app_caseStepCTK Aw (tableOfK hW) h1 h2 dl dr S σ ρ c

/-- The retained wall named: `drClause`'s `.inl` is a raw `ETm` equation —
    unissuable in every `Issues*` layer (no kind answers `Eq`), and the
    `.inr` receipt region is `DrAppHead`. The wall is inhabited at the
    fixture (`esappDrHead`). `closure_claim = 0`. -/
theorem es_app_drClause_wall_inhabited :
    esappDl.eps id [.keep, .keep] =
      appClause ((appSource esappDl rfl).hf.eps id [.keep, .keep])
        ((appSource esappDl rfl).ha.eps id [.keep, .keep]) ∨
      DrAppHead esappDl :=
  .inr esappDrHead

end Rcic.Syn

#print axioms Rcic.Syn.IssuesCTK
#print axioms Rcic.Syn.DemandCTK
#print axioms Rcic.Syn.IssuesCTK.ap
#print axioms Rcic.Syn.IssuesCTK.hom
#print axioms Rcic.Syn.IssuesCTK.routed
#print axioms Rcic.Syn.DemandCTK.ap
#print axioms Rcic.Syn.DemandCTK.hom
#print axioms Rcic.Syn.DemandCTK.routed
#print axioms Rcic.Syn.ih_issueCTK
#print axioms Rcic.Syn.ih_localCTK
#print axioms Rcic.Syn.solve_of_stepCTK
#print axioms Rcic.Syn.es_issued_occ_cl_CTK
#print axioms Rcic.Syn.es_issued_occ_pb_CTK
#print axioms Rcic.Syn.es_app_ih_fun_CTK
#print axioms Rcic.Syn.es_app_ih_arg_CTK
#print axioms Rcic.Syn.EsAppKPorts
#print axioms Rcic.Syn.esAppKPorts_of_closed
#print axioms Rcic.Syn.es_app_field_CTK
#print axioms Rcic.Syn.es_app_caseStepCTK
#print axioms Rcic.Syn.esAppKPorts_fixture
#print axioms Rcic.Syn.es_app_caseStepCTK_fixture
#print axioms Rcic.Syn.es_app_caseStepCTK_tableK
#print axioms Rcic.Syn.es_app_drClause_wall_inhabited
