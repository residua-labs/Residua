import rcic.RcicSynSRBetaZetaStepWRows
import rcic.RcicSynStepPortsConstLit
import rcic.RcicSynStepFields5

/-!
# `IssuesSR` — the issuance rows the reduction arms owe (cc 23:55Z redirect)

The shared principle (cc 2026-10-20 23:55Z): a port that is a CL/EUT fact
about two typings of ONE (smaller-in-measure) subject at a routed display is
not a global lemma to supply and not a pair-induction coherence to prove — it
is an induction-hypothesis edge the closer must ISSUE as an existing query
kind (`.cl`/`.eut`/`.es`), with the rank decreasing. Type uniqueness for the
sortRow closer comes only from its own IH.

The landed table already carries the three shapes these rows need:
`sorts_clL`/`iota_pbL` (arbitrary endpoint against a freshly synthesized
canonical), `delta_cl`/`lit_cl` (canonical reduct/expansion against the
arbitrary `dr`), `lam_esB`/`pi_esB` (the body one binder up at the binder's
display). `RcicSynP2Shared` is landed, so the rows live here as `IssuesSR`,
an answer-free extension relation; `DemandSR` closes the demand graph under
it exactly as `Demand` closes under `Issues` (no caller-presented
`AP`/`Hom`/`Routed` witnesses — those are theorems of the edge, §2). The
fields (§4) are proven from the issued edges at `StepIHSR`; landing the rows
in `RcicSynP2Shared` (a landed-file edit this lane cannot make) would turn
them into plain `CaseStepW` fields. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 the extension relation: one row per (a)-classified wall -/

/-- The issuance extension: every landed row, plus the reduction-arm rows the
    sortRow census walls measure. Each target's objects are read from the
    issuer's own fields (the read receipt `g` for `beta_cl_body` mirrors
    `letE_esB_drop`'s computed side premise; the canonical surfaces mirror
    `sortNode`/`piLeftSurface`). -/
inductive IssuesSR {Eₐ : ResolvedEnv} : P2Query Eₐ → P2Query Eₐ → Prop where
  | emb {q q' : P2Query Eₐ} : Issues q q' → IssuesSR q q'
  /-- row 2 wall 1: the read's body typing against the node's, one binder up
      at the binder's display (the `lam_esB` shape, `RedexGot`-sourced). -/
  | beta_cl_body {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
      (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
      (harg : TyP E n Γ arg A)
      (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
      (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
      (Aw : Nat → Nat) (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      IssuesSR (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)
        (.cl g.hbody hbody S σ (binderDisp (levelIsZero (σ u)) :: ρ))
  /-- row 2 wall 3: the canonical reduct against the arbitrary `dr` (the
      `delta_cl` shape). -/
  | beta_cl_reduct {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
      (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
      (harg : TyP E n Γ arg A)
      (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
      (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      IssuesSR (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)
        (.cl (instEnd hbody harg hA) dr S σ ρ)
  /-- row 3 wall 1: the arbitrary `dl` against the freshly built letE surface
      (the `sorts_clL` shape). -/
  | zeta_cl_surface {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A value body B : Expr Nat} {u : Level}
      (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
      (hb : TyP E n (.letBinding A value :: Γ) body B)
      (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
      (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      IssuesSR (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ)
        (.cl dl (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2) S σ ρ)
  /-- row 3 wall 2: the canonical reduct against the arbitrary `dr`. -/
  | zeta_cl_reduct {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A value body B : Expr Nat} {u : Level}
      (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
      (hb : TyP E n (.letBinding A value :: Γ) body B)
      (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
      (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      IssuesSR (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ)
        (.cl (letSub hb hv hA) dr S σ ρ)
  /-- row 4 surface: the arbitrary `dl` against the canonical bvar surface. -/
  | zetaLocal_cl_surface {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
      (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
      (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      IssuesSR (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
        (.cl dl (zetaLocalBvarSurface hty dl) S σ ρ)
  /-- row 7: the arbitrary `dl` against the canonical lit surface (the landed
      `lit_cl` already issues the expansion against `dr`). -/
  | lit_cl_surface {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
      (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
      (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      IssuesSR (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ)
        (.cl dl (litSurface hlit hexp) S σ ρ)
  /-- row 10 left: the arbitrary `dl` against `piLeftSurface` (the
      `sorts_clL` shape; the measure edge is the landed `piLeftSurface_wt_lt`). -/
  | pi_cl_surfaceL {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
      (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
      (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      IssuesSR (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ)
        (.cl dl (piLeftSurface hA hB) S σ ρ)
  /-- row 10 right: the canonical right surface (read off `dr`'s own recorded
      domain) against the arbitrary `dr`. -/
  | pi_cl_surfaceR {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
      (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
      (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
      (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
      {σ : Level → Level} {ρ : List Disp} :
      IssuesSR (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ)
        (.cl (piRightSurface hA hB dr) dr S σ ρ)

/-! ## §1 the demand extension and the SR issue read -/

/-- `Demand` closed under `IssuesSR`: the roots unchanged, issuance only
    through an actual edge. -/
inductive DemandSR {Eₐ : ResolvedEnv} : P2Query Eₐ → Prop where
  | ofDemand {q : P2Query Eₐ} : Demand q → DemandSR q
  | issuedSR (issuer q : P2Query Eₐ) : DemandSR issuer → IssuesSR issuer q → DemandSR q

/-- The strict-below hypothesis at the extended demand. -/
abbrev StepIHSR (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : Prop :=
  ∀ q' : P2Query Eₐ, DemandSR q' → Before Aw q' q → AnswerW Aw tbl q'

/-- The SR-issue read: the semantic answer of an issued, strictly smaller
    sub-request, off the extended IH. -/
theorem ih_issueSR {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule) {q : P2Query Eₐ}
    (hq : Demand q) (ih : StepIHSR Aw tbl q) {q' : P2Query Eₐ} (e : IssuesSR q q')
    (hb : Before Aw q' q) : GoalW tbl q' :=
  (ih q' (DemandSR.issuedSR q q' (DemandSR.ofDemand hq) e) hb).2

/-- The extended IH implies the landed one: an SR field is exactly the landed
    field plus the issued edges. -/
theorem StepIHSR.toStepIHW {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {q : P2Query Eₐ} (h : StepIHSR Aw tbl q) : StepIHW Aw tbl q :=
  fun q' hd hb => h q' (DemandSR.ofDemand hd) hb

/-- The field shape at the extended demand: the landed `CaseStepW` premise on
    the demand, the IH strengthened by exactly the issued edges. -/
abbrev CaseStepWSR (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : Prop :=
  Demand q → StepIHSR Aw tbl q → GoalW tbl q

/-! ## §2 the edge side conditions are theorems, never supplied -/

/-- Every `IssuesSR` target keeps the issuer's level map. -/
theorem IssuesSR.hom {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hσ : q.Hom) (e : IssuesSR q q') :
    q'.Hom := by
  cases e with
  | emb e => exact Issues.hom hσ e
  | _ => exact hσ

/-- Every `IssuesSR` target's display is routed: the one binder-crossing row
    routes across the assumption exactly as `lam_esB` does; every other row
    keeps the display. -/
theorem IssuesSR.routed {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ} (hr : q.Routed) (e : IssuesSR q q') :
    q'.Routed := by
  cases e with
  | emb e => exact Issues.routed hr e
  | @beta_cl_body E n Γ A body arg B u hA hbody harg dl dr Aw g E₀ n₀ Γ₀ S σ ρ =>
      exact RoutedDisp.assumption hr hA
  | _ => exact hr

/-! ## §3 the rank edges: each issued query is `Before` its issuer -/

/-- Row 2 wall 1: the body `CL` one binder up is below the β node — the
    read's atoms by `g.ltB` (all under `dl.wt`), the node field's by
    `TyP.atoms_le`. -/
theorem betaSRbody_before {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl g.hbody hbody S σ (binderDisp (levelIsZero (σ u)) :: ρ))
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) := by
  refine before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _ (lex_of_dm ?_))
  refine dmStep_under_rule Aw (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) rfl ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact Nat.lt_trans (g.ltB y hy) (by simp only [CvP.wt]; omega)
  · exact Nat.lt_of_le_of_lt (TyP.atoms_le Aw hbody y hy) (by simp only [CvP.wt]; omega)

/-- Row 2 wall 3: the reduct `CL` is below the β node — `instEnd_wt` against
    the node's own field sum (the `delta_cl` descent). -/
theorem betaSRreduct_before {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl (instEnd hbody harg hA) dr S σ ρ)
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) := by
  have hw : (instEnd hbody harg hA).wt Aw <
      (CvP.beta E n Γ A body arg B u hA hbody harg dl dr).wt Aw := by
    rw [instEnd_wt Aw hbody harg hA]
    have h1 := TyP.wt_pos Aw dl
    have h2 := TyP.wt_pos Aw dr
    simp only [CvP.wt]
    omega
  exact before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
    (lex_of_dm (dmStep_pair_below Aw
      (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) rfl
      (instEnd hbody harg hA) dr hw (by simp only [CvP.wt]; omega))))

/-- Row 3 wall 1: the fresh letE surface `CL` is below the ζ node —
    `dl.reg.2.wt ≤ dl.wt` (`TyP.wt_reg_le`) against the node's field sum. -/
theorem zetaSRsurface_before {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl dl (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2) S σ ρ)
      (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ) := by
  have hreg : dl.reg.2.wt Aw ≤ dl.wt Aw := TyP.wt_reg_le Aw dl
  have hw : (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2).wt Aw <
      (CvP.zeta E n Γ A value body B u hA hv hb dl dr).wt Aw := by
    have h1 := TyP.wt_pos Aw dr
    simp only [TyP.wt, CvP.wt]
    omega
  exact before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
    (lex_of_dm (dmStep_pair_below Aw
      (CvP.zeta E n Γ A value body B u hA hv hb dl dr) rfl dl
      (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2)
      (by simp only [CvP.wt]; omega) hw)))

/-- Row 3 wall 2: the reduct `CL` is below the ζ node — `letSub_wt` against
    the node's own field sum. -/
theorem zetaSRreduct_before {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl (letSub hb hv hA) dr S σ ρ)
      (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ) := by
  have hw : (letSub hb hv hA).wt Aw <
      (CvP.zeta E n Γ A value body B u hA hv hb dl dr).wt Aw := by
    rw [letSub_wt Aw hb hv hA]
    have h1 := TyP.wt_pos Aw dl
    have h2 := TyP.wt_pos Aw dr
    simp only [CvP.wt]
    omega
  exact before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
    (lex_of_dm (dmStep_pair_below Aw
      (CvP.zeta E n Γ A value body B u hA hv hb dl dr) rfl
      (letSub hb hv hA) dr hw (by simp only [CvP.wt]; omega))))

/-- Row 4 surface: below the ζLocal node by the landed
    `zetaLocalBvarSurface_wt_lt`. -/
theorem zetaLocalSRsurface_before {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv}
    {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl dl (zetaLocalBvarSurface hty dl) S σ ρ)
      (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) := by
  exact before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
    (lex_of_dm (dmStep_pair_below Aw
      (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) rfl
      dl (zetaLocalBvarSurface hty dl)
      (by simp only [CvP.wt]; omega) (zetaLocalBvarSurface_wt_lt Aw hval hty hv dl dr))))

/-- Row 7: the lit surface `CL` is below the lit node — `litSurface` is the
    `TyP.lit` node over the field's own `hexp`. -/
theorem litSRsurface_before {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl dl (litSurface hlit hexp) S σ ρ)
      (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ) := by
  have hw : (litSurface hlit hexp).wt Aw <
      (CvP.lit E n Γ t exp T hlit hexp dl dr).wt Aw := by
    cases hlit
    have h1 := TyP.wt_pos Aw dl
    have h2 := TyP.wt_pos Aw dr
    simp only [litSurface, TyP.wt, CvP.wt]
    omega
  exact before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
    (lex_of_dm (dmStep_pair_below Aw
      (CvP.lit E n Γ t exp T hlit hexp dl dr) rfl
      dl (litSurface hlit hexp) (by simp only [CvP.wt]; omega) hw)))

/-- Row 10 left: below the Π node by the landed `piLeftSurface_wt_lt`. -/
theorem piSRsurfaceL_before {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl dl (piLeftSurface hA hB) S σ ρ)
      (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) :=
  before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
    (lex_of_dm (dmStep_pair_below Aw
      (CvP.pi E n Γ A A' B B' u v hA hB dl dr) rfl
      dl (piLeftSurface hA hB)
      (by simp only [CvP.wt]; omega) (piLeftSurface_wt_lt Aw hA hB dl dr))))

/-- Row 10 right: below the Π node GIVEN the decoded domain's weight bound —
    the named residual `piDomain_H_wt_le : (dr.piDomain rfl).H.wt Aw ≤ dr.wt Aw`
    (a wrapper-spine induction on the `piDomSrc` decoder, not on this branch). -/
theorem piSRsurfaceR_before_of {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (hHRwt : (dr.piDomain rfl).H.wt Aw ≤ dr.wt Aw)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl (piRightSurface hA hB dr) dr S σ ρ)
      (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) := by
  have hw : (piRightSurface hA hB dr).wt Aw <
      (CvP.pi E n Γ A A' B B' u v hA hB dl dr).wt Aw := by
    have h1 := TyP.wt_pos Aw dl
    have hdr := CvP.wt_dr_lt Aw hB
    simp only [piRightSurface, piRightSurfaceSrc, TyP.wt, CvP.wt, wt_tyCast]
    omega
  exact before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
    (lex_of_dm (dmStep_pair_below Aw
      (CvP.pi E n Γ A A' B B' u v hA hB dl dr) rfl
      (piRightSurface hA hB dr) dr hw (by simp only [CvP.wt]; omega))))

/-! ## §4 the fields from the issued edges -/

/-- Row 3 at the extended demand: the `es_zeta` field, premise-free — both
    `(d)` walls are issued edges, not global lemmas. -/
theorem esW_zeta_fieldSR {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ))
    (ih : StepIHSR Aw tbl (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ)) :
    GoalW tbl (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ) :=
  zeta_caseStepW_of_port_cls hA hv hb dl dr S σ ρ
    (ih_issueSR Aw tbl hq ih (IssuesSR.zeta_cl_surface hA hv hb dl dr)
      (zetaSRsurface_before Aw hA hv hb dl dr S σ ρ))
    (ih_issueSR Aw tbl hq ih (IssuesSR.zeta_cl_reduct hA hv hb dl dr)
      (zetaSRreduct_before Aw hA hv hb dl dr S σ ρ))
    hq (StepIHSR.toStepIHW Aw tbl ih)

/-- Row 7 at the extended demand: the `es_lit` field, premise-free — the
    surface leg is the new `lit_cl_surface` edge, the reduct leg is the
    LANDED `lit_cl` edge (its own rank edge included). -/
theorem litSRcl_edge {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.cl hexp dr S σ ρ) (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ) :=
  before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
    (lex_of_dm (dmStep_pair_below Aw
      (CvP.lit E n Γ t exp T hlit hexp dl dr) rfl hexp dr
      (by simp only [CvP.wt]; omega) (by simp only [CvP.wt]; omega))))

theorem litSRsurface_epsW {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (σ : Level → Level) (ρ : List Disp) :
    (litSurface hlit hexp).epsW σ ρ = hexp.epsW σ ρ := by
  cases hlit
  rfl

/-- Row 7 at the extended demand: the `es_lit` field, premise-free. -/
theorem esW_lit_fieldSR {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ))
    (ih : StepIHSR Aw tbl (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ)) :
    GoalW tbl (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ) := by
  have h1 : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ)
      ((litSurface hlit hexp).epsW σ ρ) :=
    ih_issueSR Aw tbl hq ih (IssuesSR.lit_cl_surface hlit hexp dl dr)
      (litSRsurface_before Aw hlit hexp dl dr S σ ρ)
  have h2 : CLW tbl σ ρ hexp dr :=
    ih_issueSR Aw tbl hq ih
      (IssuesSR.emb (@Issues.lit_cl Eₐ E n Γ t exp T hlit hexp dl dr E₀ n₀ Γ₀ S σ ρ))
      (litSRcl_edge Aw hlit hexp dl dr S σ ρ)
  show ESW tbl σ ρ (CvP.lit E n Γ t exp T hlit hexp dl dr)
  rw [litSRsurface_epsW hlit hexp σ ρ] at h1
  exact h1.trans h2

/-- Row 4 at the extended demand: the surface leg is the new edge; the
    occurrence leg is the landed (eps-free) `subAt` receipt; the res-conv leg
    is the cross-subject residual (c) — `ClwBvarValueConeW`-shaped, NOT an
    issuance (no query kind relates a display resolution to an erasure). -/
theorem esW_zetaLocal_fieldSR {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hregOcc : levelIsZero (σ dl.reg.1) = true →
      ∃ pReg : List Nat,
        P2Query.subAt (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
          0 pReg = some (.ty dl.reg.2))
    (hres : levelIsZero (σ dl.reg.1) = false →
      ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.epsW σ ρ)) :
    CaseStepWSR Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ) :=
  fun hq ih =>
    esW_zetaLocal_field_portsW Aw tbl hval hty hv dl dr S σ ρ
      (ih_issueSR Aw tbl hq ih (IssuesSR.zetaLocal_cl_surface hval hty hv dl dr)
        (zetaLocalSRsurface_before Aw hval hty hv dl dr S σ ρ))
      hregOcc hres hq (StepIHSR.toStepIHW Aw tbl ih)

end Rcic.Syn
