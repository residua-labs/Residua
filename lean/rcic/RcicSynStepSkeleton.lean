import rcic.RcicSynBelowCFix
import rcic.RcicSynP2CctxIota
import rcic.RcicSynCtsLocal

/-!
# S15 §6 — the top-down `step` skeleton: `StepSuppliers` and `step_of_suppliers`

`research/rcic/sortrow/S15_BELOWC_DISPLAY_FIXPOINT.md` §6–§8, assembled top-down
against the landed `Step` of `RcicSynBelowCFix` over the repaired shared layer
`RcicSynP2Shared` (frame scope, explicit routed display, `Demand` carrying the
public roots' `AssumpPref` / `LevelHom` — fable-step ITEM 2; issuance as the
answer-free edge `Issues`, the `esub` route tied to the node's `hv`/`hvT` — fable-step
ITEM 3, the Q267 repair; observations as individual positions of the receipt's own
admission derivation, `cts`/`bitCoh` on their finite original ports, the let-value
`pb` edge bound to the frame receipt — fable-step ITEM 4, the Q269 repair; the
observation rows answer-free and the layer registered in `RcicFoundationSeal` —
fable-step ITEM 5, the Q270 repair, 2026-10-17). Design table:
`research/rcic/sortrow/STEP_SUPPLIERS.md`. `closure_claim = 0`.

What this module does:

* `StepSuppliers Aw tbl Eₐ` — one field per **genuinely missing** per-case step
  obligation. Every field has the shape "for this `Demand` case / sub-case, given
  the strict-below answers (`StepIH`), the current case's goal holds". Nothing in
  it is `Step`, `∀ q, Answer q`, `hcoh`, or a universal `SortCoh`.
* `step_of_suppliers` — the full case split over the ten `P2Query` tags and, inside
  `.es`, the 24 `CvP` constructors. Closed from the IH by landed lemmas and **not**
  fields: `refl`/`symm`/`trans`/`tyConv` (`es_*` + `below_*`); `irr` and `sorts`
  (the `LevelHom σ` every demanded query carries); `iota`'s proof-result branch
  (`iota_q{L,R}_below` + `es_iota_proof_of_pbits`); the five transports
  `wk`/`esub`/`linst`/`ewk`/`cctx` (the child is a genuine `P2Query` at the parent's
  transformed display, issued by the transport row, strictly below by
  `lexDM_cvMeas_*`, finished by the landed `es_wk_*`/`es_esub_*`/`es_linst`/
  `es_ewk`/`es_cctx`); `.cts` and `.bitCoh` (`cts_goal_of_ports` /
  `bitCoh_goal_of_ports`: the landed `cts_of_eut_cl` / `bitCoh_of_eut_cl` fed by IH
  calls on exactly the issuer's finite original ports — `cts_eut_dlX`, `cts_cl_regL`,
  `cts_cl_regX`, `bitCoh_cl_regL/R` — with the sort/Π-headed `reg` free by
  `cl_reg_sort_of_isSortOrPiHead`; `bitCoh` re-runs the `.eut` case at the **same**
  rank through the `bitCoh_eut` row, a local data dependency, S9 §5); `.head`
  (every demanded `head` is issued by a row binding its kind sources to the path's
  endpoints, so its bit equation is the composition of the two same-subject
  `BitCoh` legs through the shared `u` — `KindTrace.edge` in bit form, each leg one
  `DMStep` below). `.slot` has **no issuing row** (its kind source is the open
  W-IOTA-SLOT-KIND-SOURCE; a row with free `uD`/`ls` would be a free kind source
  again): its demand is empty (`slot_not_demanded`), which is a vacuity, not a
  closure — counted separately in the table. `.observation` is **open** (Q270,
  fable-step ITEM 5): its only issuing rows `delta_obs_out`/`delta_obs_gate` issue
  every actual OUT/GATE position of the receipt's own admission derivation under the
  δ maps and carry **no** certificate, so the answer is the field `delta_obs`;
  `observation_goal_of_demand` only inverts the demand to the issuing δ node and
  calls that field (W-TABLE-DELTA-OBSERVATION-STABILITY).
* `allBelowScoped_of_step` / `allBelowScoped_of_suppliers` / `sortCoh_of_suppliers`
  — the S15 §6 chain. The public `BelowScoped` conclusions are literally the `Goal`s
  of the six demanded roots, so the chain needs no `CompleteCAt` detour.
* `rule_sub_before` / `binder_body_before` — the rank edge the frame repair buys;
  `letValue_before` (a strict original-receipt suffix, `LetEntryAt.length_lt`) and
  `delta_obs_before` (the issued admission observation under the receipt's own
  admission weights, `delta_adm_below`) — the rank edges of the Q269 rows.

Frozen controls (every finding stays measurable against the definitions it refuted):

1. `binder_body_not_before` — under the pre-repair first coordinate a binder-body
   sub-request is never `Before` its parent.
2. `step_refuted_const_zero` — the `Step` over the ITEM 1 `DemandWide` is refuted by
   the landed `not_pbit_const_zero`.
3. `Q267HeadInjection` / `Q267RoutedEsub` — the two kernel-checked Q267
   countermodels, reproduced verbatim against the ITEM 2 shapes `DemandFree` /
   `RoutedDispFree` (`no_stepFree`), and their rejection by the repaired layer:
   `q_not_demanded` (no `Demand` at all for the injected head; `Demand.head_bound`),
   `issuer_not_issues` (the audit's exact edge does not exist), and
   `routed_drop_needs_prop_sort` (the repaired `esub` arm prices the wrong display
   at a typing `sort 0 : sort 0`). **Not claimed:** `¬ Demand` of the routed-esub
   `pb` query and `¬ RoutedDisp … [.drop]` outright — that is display validity of
   `SortCoh` strength (a sort-typing inversion through `conv` that is not on the
   tree), see `STEP_SUPPLIERS.md` §6.
4. `Q269ObservationAudit` / `Q269DeltaObservationIndependent` — the two kernel-checked
   Q269 countermodels, reproduced verbatim against the ITEM 3 observation shapes
   (`P2Query.obsPair`, `IssuesObsFree`, `DemandObsFree`, `StepObsFree`:
   `no_stepObsFree`), and their rejection: the two-derivation observation is not
   demanded at all (`obsPair_not_demanded`), and the repaired δ rows issue only
   single positions of the receipt's own admission derivation.

Nothing here is a producer of any field; `StepSuppliers` is the exact, countable
object the brief asked for.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 the induction hypothesis, the trivial view, issuing a sub-request -/

/-- The strict-below hypothesis `Step` hands to a case: answers to every demanded
    query `Before` `q`. Definitionally the premise of `Step`. -/
abbrev StepIH (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : Prop :=
  ∀ q' : P2Query Eₐ, Demand q' → Before Aw q' q → Answer Aw tbl q'

/-- The per-case step obligation at `q`: given the demand and the strict-below
    answers, the computed `Goal`. Every `StepSuppliers` field is a `CaseStep`. -/
abbrev CaseStep (Aw : Nat → Nat) (tbl : List CRule) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : Prop :=
  Demand q → StepIH Aw tbl q → Goal tbl q

/-- The `ResolvedView` half of `Answer` is inhabited by the empty plan for every query.
    This carries no information: the skeleton's content is the `Goal` half. -/
def trivialView (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : ResolvedView Aw q :=
  ⟨ViewPlan.empty Eₐ, .ambientView, []⟩

/-- The semantic answer of an issued, strictly smaller sub-request, read off the IH:
    the only way a case obtains a smaller answer. The edge `e` is an actual row of
    `Issues`; its `AssumpPref`/`LevelHom`/`RoutedDisp` are theorems, never supplied. -/
theorem ih_issue {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule) {q : P2Query Eₐ}
    (hq : Demand q) (ih : StepIH Aw tbl q) (q' : P2Query Eₐ) (e : Issues q q')
    (hb : Before Aw q' q) : Goal tbl q' :=
  (ih q' (.issued q q' hq e) hb).2

/-! ## §1 edges of the rank order -/

/-- `combMeas` is monotone in its raw measure: a `DMStep` on the atoms survives the
    common spine prefix (`dmStep_append_left`), a weight drop survives the common
    spine weight. -/
theorem lexDM_combMeas_mono (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (C : CtxP E n Γ) {m' m : List Nat × Nat} (h : LexDM m' m) :
    LexDM (combMeas Aw C m') (combMeas Aw C m) := by
  cases h with
  | left _ _ hdm => exact Prod.Lex.left _ _ (dmStep_append_left hdm (C.atoms Aw))
  | right _ hlt => exact Prod.Lex.right _ (Nat.add_lt_add_left hlt _)

/-- Same frame, strictly smaller local key: `Before`. -/
theorem before_of_same_prefix {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {q' q : P2Query Eₐ}
    (hp : q'.originalPrefixLength = q.originalPrefixLength)
    (hk : LexDM (q'.localKey Aw) (q.localKey Aw)) : Before Aw q' q := by
  show Prod.Lex (fun p' p : Nat => p' < p) LexDM
    (q'.originalPrefixLength, q'.localKey Aw) (q.originalPrefixLength, q.localKey Aw)
  rw [hp]
  exact Prod.Lex.right _ hk

/-- Strictly shorter frame: `Before`, whatever the local keys. -/
theorem before_of_lt_prefix {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {q' q : P2Query Eₐ}
    (hp : q'.originalPrefixLength < q.originalPrefixLength) : Before Aw q' q := by
  show Prod.Lex (fun p' p : Nat => p' < p) LexDM
    (q'.originalPrefixLength, q'.localKey Aw) (q.originalPrefixLength, q.localKey Aw)
  exact Prod.Lex.left _ _ hp

theorem prodLex_fst_le {β : Type} {s : β → β → Prop} {p' p : Nat} {b' b : β}
    (h : Prod.Lex (fun x y : Nat => x < y) s (p', b') (p, b)) : p' ≤ p := by
  cases h with
  | left _ _ h => exact Nat.le_of_lt h
  | right _ _ => exact Nat.le_refl _

/-- A query in a strictly longer frame is never `Before` one in a shorter frame,
    whatever the local keys. -/
theorem not_before_of_prefix_gt {Eₐ : ResolvedEnv} (Aw : Nat → Nat) {q' q : P2Query Eₐ}
    (hp : q.originalPrefixLength < q'.originalPrefixLength) : ¬ Before Aw q' q := by
  intro h
  have hle := prodLex_fst_le (show Prod.Lex (fun p' p : Nat => p' < p) LexDM
    (q'.originalPrefixLength, q'.localKey Aw) (q.originalPrefixLength, q.localKey Aw) from h)
  omega

/-- An IH call on an issued sub-request in the **same frame** at a strictly smaller
    local key. -/
theorem ih_local {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule) {q : P2Query Eₐ}
    (hq : Demand q) (ih : StepIH Aw tbl q) (q' : P2Query Eₐ) (e : Issues q q')
    (hp : q'.originalPrefixLength = q.originalPrefixLength)
    (hk : LexDM (q'.localKey Aw) (q.localKey Aw)) : Goal tbl q' :=
  ih_issue Aw tbl hq ih q' e (before_of_same_prefix Aw hp hk)

/-! ### raw-measure descents: sub-conversions of rule nodes, transport children -/

/-- Any conversion of strictly smaller weight than a rule node is `LexDM`-below it:
    every atom of the sub-conversion lies under the node's weight (`CvP.atoms_le`),
    and a rule node's atom list is its own weight (`dmStep_under_rule`). -/
theorem lexDM_cvMeas_sub_rule (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (node : CvP E n Γ a b T) (hnode : node.isTransport = false)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {a' b' T' : Expr Nat} (h' : CvP E' n' Γ' a' b' T')
    (hwt : h'.wt Aw < node.wt Aw) : LexDM (cvMeas Aw h') (cvMeas Aw node) :=
  lex_of_dm (dmStep_under_rule Aw node hnode
    (fun y hy => Nat.lt_of_le_of_lt (CvP.atoms_le Aw h' y hy) hwt))

/-- Dropping a non-empty tail of atoms is a `DMStep` (local form of
    `dmStep_drop_right_nonempty`, which lives outside this module's imports). -/
theorem dmStep_drop_tail (X : List Nat) {Y : List Nat} (hY : Y ≠ []) : DMStep X (X ++ Y) :=
  dmStep_perm_right List.perm_append_comm (dmStep_drop hY)

/-- `wk`: same atoms, one less weight. -/
theorem lexDM_cvMeas_wk (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CvP E n Γ a b T) (d : LocalDecl) (c : Nat) :
    LexDM (cvMeas Aw h) (cvMeas Aw (CvP.wk E n Γ a b T d c h)) := by
  simp only [cvMeas, CvP.atoms, CvP.wt]
  exact Prod.Lex.right _ (by omega)

/-- `esub`: the child's atoms are a strict sub-multiset (the substituted value's
    atoms are dropped; atom lists are never empty). -/
theorem lexDM_cvMeas_esub (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T t v : Expr Nat} {j : Nat} {u : Level} (h : CvP E n Γ a b T)
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    LexDM (cvMeas Aw h) (cvMeas Aw (CvP.esub E n Γ a b T t v j u h hget hv hvT)) := by
  simp only [cvMeas, CvP.atoms]
  exact Prod.Lex.left _ _
    (dmStep_drop_right (dmStep_drop_tail (h.atoms Aw) (TyP.atoms_ne_nil Aw hv))
      (hvT.atoms Aw))

/-- `linst`: same atoms, one less weight. -/
theorem lexDM_cvMeas_linst (Aw : Nat → Nat) {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {ls : List Level} (hls : levelsBounded n ls = true)
    (hlen : ls.length = a') (h : CvP E a' Γ a b T) :
    LexDM (cvMeas Aw h) (cvMeas Aw (CvP.linst E a' n Γ a b T ls hls hlen h)) := by
  simp only [cvMeas, CvP.atoms, CvP.wt]
  exact Prod.Lex.right _ (by omega)

/-- `ewk`: same atoms, one less weight. -/
theorem lexDM_cvMeas_ewk (Aw : Nat → Nat) {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (hext : EnvExt E₀ E) (h : CvP E₀ n Γ a b T) :
    LexDM (cvMeas Aw h) (cvMeas Aw (CvP.ewk E₀ E n Γ a b T hext h)) := by
  simp only [cvMeas, CvP.atoms, CvP.wt]
  exact Prod.Lex.right _ (by omega)

/-- `cctx`: the bridge's atoms are dropped (never empty). -/
theorem lexDM_cvMeas_cctx (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T A A' : Expr Nat} {u : Level} (h : CvP E n (.assumption A :: Γ) a b T)
    (hA : CvP E n Γ A A' (.sort u)) :
    LexDM (cvMeas Aw h) (cvMeas Aw (CvP.cctx E n Γ a b T A A' u h hA)) := by
  simp only [cvMeas, CvP.atoms]
  exact Prod.Lex.left _ _ (dmStep_drop_tail (h.atoms Aw) (CvP.atoms_ne_nil Aw hA))

/-! ### the `head` legs: one `DMStep` below the head measure -/

/-- The left leg `BitCoh dL c.dl` of a bound head: `c.dl`'s atoms replace `c`'s
    (`dmStep_cvp_dl`) and `dR`'s atoms are dropped — one `DMStep`. -/
theorem head_legL_dm (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} {u uL uR : Level} (c : CvP E n Γ A A' (.sort u))
    (dL : TyP E n Γ A (.sort uL)) (dR : TyP E n Γ A' (.sort uR)) :
    DMStep (dL.atoms Aw ++ c.dl.atoms Aw) (c.atoms Aw ++ dL.atoms Aw ++ dR.atoms Aw) :=
  dmStep_perm_right (List.Perm.append_right _ List.perm_append_comm)
    (dmStep_drop_right (dmStep_append_left (dmStep_cvp_dl Aw c) (dL.atoms Aw)) (dR.atoms Aw))

/-- The right leg `BitCoh c.dr dR` of a bound head: `c.dr`'s atoms replace `c`'s
    (`dmStep_cvp_dr`) and `dL`'s atoms are dropped — one `DMStep`. -/
theorem head_legR_dm (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} {u uL uR : Level} (c : CvP E n Γ A A' (.sort u))
    (dL : TyP E n Γ A (.sort uL)) (dR : TyP E n Γ A' (.sort uR)) :
    DMStep (c.dr.atoms Aw ++ dR.atoms Aw) (c.atoms Aw ++ dL.atoms Aw ++ dR.atoms Aw) :=
  dmStep_perm_right
    (by simp only [List.append_assoc]; exact List.Perm.append_left _ List.perm_append_comm)
    (dmStep_drop_right (dmStep_append_right (dmStep_cvp_dr Aw c) (dR.atoms Aw)) (dL.atoms Aw))

/-! ### the frame repair, measured -/

/-- **The edge the frame buys (S15 §6).** A sub-conversion of a rule node, issued in
    the parent's frame at any display, is `Before` the parent: same first coordinate,
    strict `LexDM` on the local key. The derivation's own context plays no role. -/
theorem rule_sub_before {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (node : CvP E n Γ a b T) (hnode : node.isTransport = false)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {a' b' T' : Expr Nat} (h' : CvP E' n' Γ' a' b' T')
    (hwt : h'.wt Aw < node.wt Aw)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ ρ' : List Disp) :
    Before Aw (.es h' S σ ρ') (.es node S σ ρ) :=
  before_of_same_prefix Aw rfl
    (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_sub_rule Aw node hnode h' hwt))

/-- **Finding 1, repaired (`binder_body_before`).** The body `ES` request of a `pi`
    node — one binder up, at the binder's display — is `Before` the node: it keeps the
    parent's frame and descends by `LexDM`. Compare the frozen
    `binder_body_not_before` below. -/
theorem binder_body_before {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level} (Aw : Nat → Nat)
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v))) (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw (.es hB S σ (binderDisp (levelIsZero (σ u)) :: ρ))
      (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) :=
  rule_sub_before Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr) rfl hB
    (by simp only [CvP.wt]; omega) S σ ρ _

/-- The pre-repair rank: the derivation's **own** context length first. -/
noncomputable abbrev rankOwn (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : Key :=
  (q.ownPrefixLength, q.localKey Aw)

/-- The pre-repair `Before`. -/
abbrev BeforeOwn (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q' q : P2Query Eₐ) : Prop :=
  KeyLT (rankOwn Aw q') (rankOwn Aw q)

/-- **Frozen control (finding 1).** Under the pre-repair rank the same body request is
    **not** before its parent, for every local key and every display: its own context
    is one longer. -/
theorem binder_body_not_before {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level} (Aw : Nat → Nat)
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v))) (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ ρ' : List Disp) :
    ¬ BeforeOwn Aw (.es hB S σ ρ') (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ) := by
  intro hlt
  have hle : (LocalDecl.assumption A :: Γ).length ≤ Γ.length := prodLex_fst_le hlt
  rw [List.length_cons] at hle
  omega

/-! ## §2 Frozen control (finding 2): the pre-repair `Demand` refutes its `Step` -/

/-- `Step` over the pre-repair `DemandWide`. -/
abbrev StepWide (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ q : P2Query Eₐ, DemandWide q →
    (∀ q' : P2Query Eₐ, DemandWide q' → Before Aw q' q → Answer Aw tbl q') →
    Answer Aw tbl q

/-- The wrapper over `DemandWide` (the same well-founded induction as `solve_of_step`). -/
theorem solve_of_stepWide {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : StepWide Aw tbl Eₐ) : ∀ q : P2Query Eₐ, DemandWide q → Answer Aw tbl q := by
  have allAt : ∀ k : Key, ∀ q : P2Query Eₐ, q.rank Aw = k → DemandWide q → Answer Aw tbl q :=
    keyLT_wf.fix (fun k ih q hkey hq =>
      step q hq (fun q' hq' hlt =>
        ih (q'.rank Aw) (by unfold Before at hlt; rwa [hkey] at hlt) q' rfl hq'))
  intro q hq
  exact allAt (q.rank Aw) q rfl hq

/-- The empty scope over the empty environment. -/
def nilScope : ScopedCtx emptyEnv emptyEnv 0 [] :=
  ⟨.empty, envExt_refl _, .nil⟩

/-- **Frozen control (finding 2).** The pre-repair demand admits the `pb` root
    `pinSortP` at `σ := fun _ => .zero` with the empty display; the landed
    `not_pbit_const_zero` refutes the answer the wrapper would return. `Demand` (the
    repaired one) cannot demand this query: `LevelHom (fun _ => .zero)` is false. -/
theorem step_refuted_const_zero (Aw : Nat → Nat) (tbl : List CRule) :
    ¬ StepWide Aw tbl emptyEnv := by
  intro step
  have h : PBit (fun _ => Level.zero) [] pinSortP
      (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)) :=
    (solve_of_stepWide Aw tbl step
      (.pb pinSortP (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
        nilScope (fun _ => .zero) [])
      (.publicRoot _ rfl)).2
  exact not_pbit_const_zero h

/-! ## §3 the supplier record -/

/-- **The countable object.** One field per genuinely missing per-case step
    obligation of the BelowC fixpoint. Fields are per `P2Query` tag and, inside `.es`,
    per `CvP` constructor; a (sub-)case that landed code closes from the IH is absent.
    Every field is a plain `CaseStep … q`: the whole (sub-)case is open, at the query's
    frame `S`, level map `σ`, and routed display `ρ` (all three are read from the
    demand; `AssumpPref`, `LevelHom σ`, `RoutedDisp` are available to the supplier
    through `Demand.ap`/`.hom`/`.routed`; smaller answers only through `Issues` rows
    and `ih_issue`).

    Residue names in the docstrings are the design docs' (S15–S21); `R2` marks fields
    whose `eps` reading changes with the erasure switch (#7390) and must be re-pinned.
    Body sub-requests one binder up are reachable through `rule_sub_before` and the
    `lam_esB`/`pi_esB`/`letE_esB_*` rows. -/
structure StepSuppliers (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop where
  -- ### `.es` — rule nodes (S15 §8)
  /-- `consts`: both endpoint erasures against the recorded alias views; needs the
      level-view correspondence of `ls`/`ls'` under `σ` and the proof-bit of the
      recorded sort. No field row serves it (the natural `TyP.const` needs the member
      type's sort typing, which the node does not carry): occurrence rows only.
      S21 §2 **W-COV-CONST-ASCRIPTION-LEVELS**. -/
  es_consts : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true) (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)
  /-- `beta`: the stored endpoints against the real `λ`/app clause and the
      instantiated body (`es_beta_drop`/`es_beta_rel`). No field row (the app clause's
      natural typing needs `TyP.app`'s `hT`): occurrence rows only. S15 §8 β,
      S15_REDEX_VIEW_ELIMINATION. R2. -/
  es_beta : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)
  /-- `zeta`: the let clause's inline/drop display of `hb` against `dr` (`es_zeta`);
      the stored value's `PB` is issued by `zeta_pb`. S15 §8 ζ,
      **W-ER2-SHIFTED-VALUE-SCOPE**. R2 (`localize`). -/
  es_zeta : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ)
  /-- `zetaLocal`: `dl` (the variable) against `dr` (the stored value) — different
      subjects, so not a `CL`; `zetaLocal_cl` issues `hv` against `dr`; needs the real
      stored-value `PB` and the inline correspondence of the routed display. S15 §8,
      S16 §2.3, **W-ER2-SHIFTED-VALUE-SCOPE**. R2. -/
  es_zetaLocal : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
  /-- `delta`: the admitted T1 rule's root `EStep`, the constant's erasure and the
      body `CL` (`es_delta`); `delta_cl` issues `hb` against `dr`; `delta_obs_out` /
      `delta_obs_gate` issue every actual OUT/GATE observation of the receipt's own
      admission derivation under the δ maps — answered by the `delta_obs` field below
      (the landed `obsLvlEq_eps_delta` then turns those answers into the δ-exchange).
      This field's own obligations: the `D_b` adapter and the selected rule's membership
      (observation doc §2.1), and the admission-weight adequacy of the ranking
      (`delta_obs_before` holds under the receipt's own `admW`; another `Aw` needs
      `AgreeOn`, §7.3). S15 §8 δ, S11s δ/ι ES construction, S7 T3. -/
  es_delta : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)
  /-- `iota`, retained-result branch (`levelIsZero (σ hlhs.reg.1) = false`): the
      original T6 spine, slot/kind, rule match, RHS β* and endpoint `CL`s. The
      proof-result branch is closed by `es_iota_proof_of_pbits`. The slot kind has
      **no issuing row** (`.slot`'s demand is empty): the kind source is this field's
      own obligation. S16 §4.3–4.5, **W-IOTA-GENERATED-CHAIN-BOUND**,
      **W-IOTA-CANONICAL-SPINE-BUDGET**, **W-IOTA-SLOT-KIND-SOURCE**. -/
  es_iota_retained : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    levelIsZero (σ hlhs.reg.1) = false →
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)
  /-- `lit`: `dl` (the literal) against the expansion's typing — different subjects;
      `lit_cl` issues `hexp` against `dr`. S15 §8 lit. -/
  es_lit : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ)
  /-- `app`: both endpoints against the exact app clause, the function's star status
      (`TagCoh`) and the argument's proof status; `app_es1`/`app_es2` issue `h1`/`h2`.
      S15 §8 app, S20_TAGCOH_STEP §3 **P2-TAG-DERIVED-REQUEST**. -/
  es_app : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
  /-- `lam`: domain `ES` (`lam_esA`), the body `ES` one binder up (`lam_esB`,
      `rule_sub_before`) under the real binder display, the λ clause's star status.
      S15 §8 λ, S20_TAGCOH_STEP **P2-TAG-DERIVED-REQUEST**. -/
  es_lam : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
  /-- `pi`: domain `ES` (`pi_esA`), body `ES` one binder up (`pi_esB`,
      `binder_body_before`), the piSlot/lift composition under `TableClosed`.
      S15 §8 Π, S12 (piSlot). R2. -/
  es_pi : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ)
  /-- `letE`: domain/value/body `ES` (`letE_esA`/`letE_esV`/`letE_esB_drop`/
      `letE_esB_inline`) with the body one let-binder up under the real inline/drop
      views; different inline values are never judged equal. S15 §8 let,
      **W-ER2-SHIFTED-VALUE-SCOPE**. R2. -/
  es_letE : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
  /-- `eta`: `dl` (the expanded λ) against `dr` through the real η path (`es_eta`
      with the erased function `F`); `eta_cl` issues `hf` against `dr`. S15 §8 η. -/
  es_eta : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)
  /-- `fsub`: the two instantiations of `hB` (one binder up) and the endpoint reads
      (`es_fsub_drop`/`es_fsub_keep`); `fsub_es` issues `hab`. S15 §8 fsub. R2. -/
  es_fsub : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ)
  -- ### the other tags (`.cts`, `.bitCoh`, `.head` are closed; `.observation` is open —
  -- `delta_obs`; `.slot` has no demand; the frozen `.obsPair` has no demand)
  /-- `.cl`: the same-subject pair dispatch (strip `conv`, strip transports, then
      same-head rules); sub-requests through `occ_*`, `cl_mixed`. S10s CL pair dispatch,
      S19 qType MixedCL. -/
  cl_case : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.cl D₁ D₂ S σ ρ)
  /-- `.eut`: the same-subject EUT pair dispatch; sub-requests through `occ_*`,
      `eut_mixed`. S10s EUT pair dispatch, S18 variable hit
      (`mixedEUT_hit_conv_compose`), S20_NESTED_EXPOSURE_HE. -/
  eut_case : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.eut D₁ D₂ S σ ρ)
  /-- `.pb`: the head proof-bit of `D` against `DT`. S16 §2 bvar
      (`pbit_of_reg_and_bitCoh`, **P2-PREPAID-CONTEXT**; `pb_bvar_bitCoh` issues the
      bvar's `hA` against `DT`, `pb_letValue` the frame receipt's own let-entry value `PB`
      at the entry's tail scope — `LetEntryAt`, `letValue_before`; an entry introduced
      above the frame, or read through `ewk`/`linst`, has no row and is this field's
      own obligation), S17 A6. -/
  pb_case : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {s : Level} (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.pb D DT S σ ρ)
  /-- `.mixed`: the moved same-subject pair's `CL ∧ EUT` (issued at the same rank by
      `cl_mixed`/`eut_mixed`). S17 (`mixedBit_finish`, **P2-MIXED-PEER-EUT**), S18, S19,
      S20_NESTED_EXPOSURE_HE. -/
  mixed_case : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStep Aw tbl (.mixed D₁ D₂ S σ ρ)
  /-- `.observation` — **the δ admission observations (Q270, fable-step ITEM 5).** For a
      demanded δ node, the receipt's own admission of `r`
      (`((enrichEnvWfT S.env).defAdm hres hbody htr).hv`, S7 T3 `DefAdm`) observed at ONE
      position `pos` of its observer lists under the δ-exchange maps
      `instLevel (ls.map σ)` / `fun l => σ (instLevel ls l)`: `eqN` of the two images at an
      OUT position, equal `levelIsZero` bits at a GATE position (`ObsGoal` — the premise
      shape of the landed `obsLvlEq_eps_delta`; vacuous off the lists). Issued by
      `delta_obs_out`/`delta_obs_gate` with **no** certificate: the S7 §3 routes
      (`ObsCert`, `AdmObsPlan`) are tools a supplier may use inside this proof, never a
      premise of the demand, and a position no route supplies
      (`PendingActualObservation`) is exactly what is owed here. The IH is empty for an
      observation (no row has an observation issuer): this is a semantic producer. The
      δ node's demand (`_hδ`) is the case context — it fixes the node's data (`hlen`,
      `hwf`, `hb`, `dl`, `dr`, `ρ`) and ties the request to a demanded issuer.
      BELOWC_OBSERVATION_REQUESTS.md §1.1, §2.1, §6; S4 §5
      **W-TABLE-DELTA-OBSERVATION-STABILITY**. -/
  delta_obs : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (_hδ : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (pos : ObsPos),
    CaseStep Aw tbl (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) pos S σ [])

/-! ## §4 `.cts` and `.bitCoh` from their finite original ports (Q269 P2) -/

/-- `CTS h DX` from exactly the three original ports of the `.cts` node, each an IH call in
    the same frame one `LexDM` step below: the `EUT` of `h.dl` against `DX`
    (`cts_eut_dlX`, `lexDM_cts_pair`), the reg-`CL` of `h.dl` at `sortNode w`
    (`cts_cl_regL`, `dmStep_cvp_dl_reg`), and — unless `DX` is sort/Π-headed, where it is
    free (`cl_reg_sort_of_isSortOrPiHead`) — the reg-`CL` of `DX` at `sortNode s`
    (`cts_cl_regX`, `dmStep_reg_sort_pair`); composed by the landed `cts_of_eut_cl`. The
    universal S9 `CLBelowHere`/`EUTBelowHere` interfaces are not requested. -/
theorem cts_goal_of_ports {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {X Y : Expr Nat}
    {w s : Level} (Aw : Nat → Nat) (tbl : List CRule) (hTbl : TableWF tbl)
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (ρ : List Disp)
    (hq : Demand (.cts h DX S ρ)) (ih : StepIH Aw tbl (.cts h DX S ρ)) : CTS h DX := by
  have heut : EUT tbl id ρ h.dl DX :=
    ih_local Aw tbl hq ih (.eut h.dl DX S id ρ) Issues.cts_eut_dlX rfl
      (lexDM_combMeas_mono Aw _ (lexDM_cts_pair Aw h DX))
  have hL : CL tbl id ρ h.dl.reg.2 (sortNode E n Γ w) := by
    have hd : DMStep (h.dl.reg.2.atoms Aw ++ (sortNode E n Γ w).atoms Aw) (h.atoms Aw) := by
      refine dmStep_cvp_dl_reg Aw h ?_
      intro y hy
      simp only [sortNode, TyP.atoms, List.mem_singleton] at hy
      subst y
      exact Nat.le_refl 1
    exact ih_local Aw tbl hq ih (.cl h.dl.reg.2 (sortNode E n Γ w) S id ρ) Issues.cts_cl_regL rfl
      (lexDM_combMeas_mono Aw _ (lex_of_dm (dmStep_drop_right hd (DX.atoms Aw))))
  have hR : CL tbl id ρ DX.reg.2 (sortNode E n Γ s) := by
    cases hs : DX.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl DX hs id ρ
    | false =>
        exact ih_local Aw tbl hq ih (.cl DX.reg.2 (sortNode E n Γ s) S id ρ)
          (Issues.cts_cl_regX hs) rfl
          (lexDM_combMeas_mono Aw _
            (lex_of_dm (dmStep_drop_left (dmStep_reg_sort_pair Aw DX hs) (h.atoms Aw))))
  exact cts_of_eut_cl hTbl h DX ρ heut hL hR

/-- `BitCoh σ D₁ D₂` from the current pair's `EUT` (a same-rank local dependency, row
    `bitCoh_eut`) and exactly the two original reg-`CL` ports (`bitCoh_cl_regL/R`,
    `lexDM_reg_sort_of_pair_left/right`), each free when its operand is sort/Π-headed;
    composed by the landed `bitCoh_of_eut_cl`. -/
theorem bitCoh_goal_of_ports {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {T : Expr Nat}
    {u v : Level} (Aw : Nat → Nat) (tbl : List CRule) (hTbl : TableWF tbl)
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.bitCoh D₁ D₂ S σ ρ)) (ih : StepIH Aw tbl (.bitCoh D₁ D₂ S σ ρ))
    (heut : EUT tbl σ ρ D₁ D₂) : BitCoh σ D₁ D₂ := by
  have hL : CL tbl σ ρ D₁.reg.2 (sortNode E n Γ u) := by
    cases hs : D₁.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl D₁ hs σ ρ
    | false =>
        exact ih_local Aw tbl hq ih (.cl D₁.reg.2 (sortNode E n Γ u) S σ ρ)
          (Issues.bitCoh_cl_regL hs) rfl
          (lexDM_combMeas_mono Aw _ (lexDM_reg_sort_of_pair_left Aw D₁ hs D₂))
  have hR : CL tbl σ ρ D₂.reg.2 (sortNode E n Γ v) := by
    cases hs : D₂.isSortOrPiHead with
    | true => exact cl_reg_sort_of_isSortOrPiHead tbl D₂ hs σ ρ
    | false =>
        exact ih_local Aw tbl hq ih (.cl D₂.reg.2 (sortNode E n Γ v) S σ ρ)
          (Issues.bitCoh_cl_regR hs) rfl
          (lexDM_combMeas_mono Aw _ (lexDM_reg_sort_of_pair_right Aw D₁ D₂ hs))
  exact bitCoh_of_eut_cl hTbl D₁ D₂ σ ρ heut hL hR

/-! ## §5 the `.es` case: full split over the 24 `CvP` constructors -/

/-- The `.es` case of the step. Closed from the IH: `refl`, `symm`, `trans`, `tyConv`,
    `irr`, `sorts`, `iota` (proof result), and the five transports; everything else
    is read from `W`. Every IH call names its `Issues` row. -/
theorem es_goal_of_suppliers {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat}
    (h : CvP E n Γ a b T) (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es h S σ ρ)) (ih : StepIH Aw tbl (.es h S σ ρ)) :
    Goal tbl (.es h S σ ρ) := by
  have hσ : LevelHom σ := hq.hom
  show ES tbl σ ρ h
  cases h with
  | refl E n Γ a A ht dl dr =>
      refine es_refl ht dl dr ?_
      exact ih_local Aw tbl hq ih (.cl dl dr S σ ρ) Issues.refl_cl rfl
        (lexDM_combMeas_mono Aw _ (lex_of_dm (below_refl Aw ht dl dr)))
  | symm E n Γ a b A h dl dr =>
      have steps := below_symm Aw h dl dr
      refine es_symm h dl dr ?_ ?_ ?_
      · exact ih_local Aw tbl hq ih (.es h S σ ρ) Issues.symm_es rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.1))
      · exact ih_local Aw tbl hq ih (.cl dl h.dr S σ ρ) Issues.symm_clL rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.1))
      · exact ih_local Aw tbl hq ih (.cl h.dl dr S σ ρ) Issues.symm_clR rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2))
  | trans E n Γ a b c A h1 h2 dl dr =>
      have steps := below_trans Aw h1 h2 dl dr
      refine es_trans h1 h2 dl dr ?_ ?_ ?_ ?_ ?_
      · exact ih_local Aw tbl hq ih (.es h1 S σ ρ) Issues.trans_es1 rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.1))
      · exact ih_local Aw tbl hq ih (.es h2 S σ ρ) Issues.trans_es2 rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.1))
      · exact ih_local Aw tbl hq ih (.cl dl h1.dl S σ ρ) Issues.trans_clL rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2.1))
      · exact ih_local Aw tbl hq ih (.cl h1.dr h2.dl S σ ρ) Issues.trans_clM rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2.2.1))
      · exact ih_local Aw tbl hq ih (.cl h2.dr dr S σ ρ) Issues.trans_clR rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2.2.2))
  | beta E n Γ A body arg B u hA hbody harg dl dr =>
      exact W.es_beta hA hbody harg dl dr S σ ρ hq ih
  | zeta E n Γ A value body B u hA hv hb dl dr =>
      exact W.es_zeta hA hv hb dl dr S σ ρ hq ih
  | zetaLocal E n Γ i A v hval hty hv dl dr =>
      exact W.es_zetaLocal hval hty hv dl dr S σ ρ hq ih
  | delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr =>
      exact W.es_delta hres hbody htr hlen hwf hb dl dr S σ ρ hq ih
  | iota E n Γ lhs rhs T w hlhs hrhs dl dr =>
      cases hu : levelIsZero (σ hlhs.reg.1) with
      | true =>
          have pL : PBit σ ρ dl hlhs.reg.2 :=
            ih_local Aw tbl hq ih (.pb dl hlhs.reg.2 S σ ρ) Issues.iota_pbL rfl
              (lexDM_combMeas_mono Aw _ (iota_qL_below Aw w hlhs hrhs dl dr))
          have pR : PBit σ ρ dr hlhs.reg.2 :=
            ih_local Aw tbl hq ih (.pb dr hlhs.reg.2 S σ ρ) Issues.iota_pbR rfl
              (lexDM_combMeas_mono Aw _ (iota_qR_below Aw w hlhs hrhs dl dr))
          exact es_iota_proof_of_pbits tbl σ ρ w hlhs hrhs dl dr hu pL pR
      | false => exact W.es_iota_retained w hlhs hrhs dl dr S σ ρ hu hq ih
  | lit E n Γ t exp T hlit hexp dl dr =>
      exact W.es_lit hlit hexp dl dr S σ ρ hq ih
  | app E n Γ f g a b A B h1 h2 dl dr =>
      exact W.es_app h1 h2 dl dr S σ ρ hq ih
  | lam E n Γ A A' b b' B u hA hb dl dr =>
      exact W.es_lam hA hb dl dr S σ ρ hq ih
  | pi E n Γ A A' B B' u v hA hB dl dr =>
      exact W.es_pi hA hB dl dr S σ ρ hq ih
  | letE E n Γ A A' v v' b b' B u hA hv hb dl dr =>
      exact W.es_letE hA hv hb dl dr S σ ρ hq ih
  | sorts E n Γ l₁ l₂ hl dl dr =>
      have hnode : (CvP.sorts E n Γ l₁ l₂ hl dl dr).isTransport = false := rfl
      have hwl : dl.wt Aw < (CvP.sorts E n Γ l₁ l₂ hl dl dr).wt Aw := by
        simp only [CvP.wt]; omega
      have hwr : dr.wt Aw < (CvP.sorts E n Γ l₁ l₂ hl dl dr).wt Aw := by
        simp only [CvP.wt]; omega
      have hpos := TyP.wt_pos Aw dl
      have hw1 : (sortNode E n Γ l₁).wt Aw < (CvP.sorts E n Γ l₁ l₂ hl dl dr).wt Aw := by
        simp only [sortNode, TyP.wt, CvP.wt]; omega
      have hw2 : (sortNode E n Γ l₂).wt Aw < (CvP.sorts E n Γ l₁ l₂ hl dl dr).wt Aw := by
        simp only [sortNode, TyP.wt, CvP.wt]; omega
      have c1 : CL tbl σ ρ dl (sortNode E n Γ l₁) :=
        ih_local Aw tbl hq ih (.cl dl (sortNode E n Γ l₁) S σ ρ) Issues.sorts_clL rfl
          (lexDM_combMeas_mono Aw _
            (lex_of_dm (dmStep_pair_below Aw (CvP.sorts E n Γ l₁ l₂ hl dl dr) hnode
              dl (sortNode E n Γ l₁) hwl hw1)))
      have c2 : CL tbl σ ρ dr (sortNode E n Γ l₂) :=
        ih_local Aw tbl hq ih (.cl dr (sortNode E n Γ l₂) S σ ρ) Issues.sorts_clR rfl
          (lexDM_combMeas_mono Aw _
            (lex_of_dm (dmStep_pair_below Aw (CvP.sorts E n Γ l₁ l₂ hl dl dr) hnode
              dr (sortNode E n Γ l₂) hwr hw2)))
      have c1' : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.sort (σ l₁)) := c1
      have c2' : ConvMod (EStep tbl) LvlEq (dr.eps σ ρ) (.sort (σ l₂)) := c2
      show ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)
      exact c1'.trans ((ConvMod.eqv (LvlEq.sort (hσ.eqN_map hl))).trans
        (ConvMod.symm' LvlEq.symm' c2'))
  | consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr =>
      exact W.es_consts hres hlen hwf hwf' hls dl dr S σ ρ hq ih
  | eta E n Γ f A B hf dl dr =>
      exact W.es_eta hf dl dr S σ ρ hq ih
  | irr E n Γ P p q' hP hp hqq dl dr =>
      have steps := below_irr Aw hP hp hqq dl dr
      have pL : PBit σ ρ dl hP :=
        ih_local Aw tbl hq ih (.pb dl hP S σ ρ) Issues.irr_pbL rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.1))
      have pR : PBit σ ρ dr hP :=
        ih_local Aw tbl hq ih (.pb dr hP S σ ρ) Issues.irr_pbR rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.1))
      exact es_irr_star hP hp hqq dl dr (pL.mpr hσ.zero_bit) (pR.mpr hσ.zero_bit)
  | tyConv E n Γ a b A A' u h hA dl dr =>
      have steps := below_tyConv Aw h hA dl dr
      refine es_tyConv h hA dl dr ?_ ?_ ?_
      · exact ih_local Aw tbl hq ih (.es h S σ ρ) Issues.tyConv_es rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.1))
      · exact ih_local Aw tbl hq ih (.cl dl h.dl S σ ρ) Issues.tyConv_clL rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.1))
      · exact ih_local Aw tbl hq ih (.cl h.dr dr S σ ρ) Issues.tyConv_clR rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2))
  | wk E n Γ a b T d c h =>
      have hbody : ES tbl σ (removeAt ρ c) h :=
        ih_local Aw tbl hq ih (.es h S σ (removeAt ρ c)) Issues.wk_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_wk Aw h d c))
      cases hρc : ρ[c]? with
      | none => exact es_wk_not_keep h (Or.inl hρc) hbody
      | some dsp =>
          cases dsp with
          | keep => exact es_wk_keep hTbl.closed h hρc hbody
          | drop => exact es_wk_not_keep h (Or.inr (Or.inl hρc)) hbody
          | inline v => exact es_wk_not_keep h (Or.inr (Or.inr ⟨v, hρc⟩)) hbody
  | esub E n Γ a b T t v j u h hget hv hvT =>
      have hbody : ES tbl σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ) h :=
        ih_local Aw tbl hq ih (.es h S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ))
          Issues.esub_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_esub Aw h hget hv hvT))
      cases hu : levelIsZero (σ u) with
      | true =>
          rw [hu, binderDisp_drop] at hbody
          exact es_esub_drop h hget hv hvT hu hbody
      | false =>
          rw [hu, binderDisp_keep] at hbody
          exact es_esub_keep hTbl.closed h hget hv hvT hu hbody
  | linst E a' n Γ a b T ls hls hlen h =>
      exact es_linst h
        (ih_local Aw tbl hq ih (.es h S (fun l => σ (instLevel ls l)) ρ) Issues.linst_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_linst Aw hls hlen h)))
  | ewk E₀' E n Γ a b T hext h =>
      exact es_ewk h
        (ih_local Aw tbl hq ih (.es h S σ ρ) Issues.ewk_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_ewk Aw hext h)))
  | cctx E n Γ a b T A A' u h hA =>
      exact es_cctx h hA
        (ih_local Aw tbl hq ih (.es h S σ ρ) Issues.cctx_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_cctx Aw h hA)))
  | fsub E n Γ A B Sx a b u hB hA hab dl dr =>
      exact W.es_fsub hB hA hab dl dr S σ ρ hq ih

/-! ## §6 the `.head` case and the empty `.slot` demand -/

/-- A **bound** head — `dL` types the path's left endpoint, `dR` its right endpoint —
    closes from the IH: the two same-subject `BitCoh` legs `head_legL`/`head_legR`,
    each one `DMStep` below (`head_legL_dm`/`head_legR_dm`), compose through the
    shared `u` (`KindTrace.edge`, S7 T12, in bit form). -/
theorem head_goal_bound {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {u uL uR : Level}
    (c : CvP E n Γ A A' (.sort u)) (dL : TyP E n Γ A (.sort uL)) (dR : TyP E n Γ A' (.sort uR))
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level)
    (ρ : List Disp)
    (hq : Demand (.head c uL uR dL dR S σ ρ)) (ih : StepIH Aw tbl (.head c uL uR dL dR S σ ρ)) :
    levelIsZero (σ uL) = levelIsZero (σ uR) := by
  have l1 : levelIsZero (σ uL) = levelIsZero (σ u) :=
    ih_local Aw tbl hq ih (.bitCoh dL c.dl S σ ρ) Issues.head_legL rfl
      (lexDM_combMeas_mono Aw _ (Prod.Lex.left _ _ (head_legL_dm Aw c dL dR)))
  have l2 : levelIsZero (σ u) = levelIsZero (σ uR) :=
    ih_local Aw tbl hq ih (.bitCoh c.dr dR S σ ρ) Issues.head_legR rfl
      (lexDM_combMeas_mono Aw _ (Prod.Lex.left _ _ (head_legR_dm Aw c dL dR)))
  exact l1.trans l2

/-- The `.head` case, closed: every demanded head is issued by a bound row
    (`tyConv_head`, `occ_head` — no root is a head), and a bound head closes by
    `head_goal_bound`. -/
theorem head_goal_of_ih {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat} {u : Level} {A A' : Expr Nat}
    {uL uR : Level}
    (c : CvP E n Γ a b (.sort u)) (dL : TyP E n Γ A (.sort uL)) (dR : TyP E n Γ A' (.sort uR))
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level)
    (ρ : List Disp)
    (hq : Demand (.head c uL uR dL dR S σ ρ)) (ih : StepIH Aw tbl (.head c uL uR dL dR S σ ρ)) :
    Goal tbl (.head c uL uR dL dR S σ ρ) := by
  cases hq with
  | issued issuer _ hiss e =>
    -- after unification the head's sources are the row's bound ones; every other
    -- row is dismissed by the constructor clash on the target
    cases e with
    | tyConv_head =>
        exact head_goal_bound Aw tbl _ _ _ _ _ _ (.issued _ _ hiss Issues.tyConv_head) ih
    | occ_head hocc hapD hapc =>
        exact head_goal_bound Aw tbl _ _ _ _ _ _
          (.issued _ _ hiss (Issues.occ_head hocc hapD hapc)) ih

/-- **Vacuity, not closure.** No root is a `slot` and no `Issues` row issues one (the
    slot kind's source is the open W-IOTA-SLOT-KIND-SOURCE; a row with free `uD`/`ls`
    would re-admit a free kind source), so the `.slot` demand is empty. The `step`
    therefore owes nothing at `.slot` today — counted separately in the table. -/
theorem slot_not_demanded {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {m : CheckedMember}
    {T : Expr Nat} {u uD : Level} {hres : E.members r = some m} {dSlot : TyP E n Γ T (.sort u)}
    {ls : List Level} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
    {σ : Level → Level} {ρ : List Disp}
    (hq : Demand (.slot u uD hres dSlot ls S σ ρ)) : False := by
  cases hq with
  | issued _ _ _ e => cases e

/-- **The `.observation` case, dispatched to its field (Q270).** Every demanded
    observation is issued by `delta_obs_out` / `delta_obs_gate` — one actual position of
    the receipt's own admission derivation under the δ maps, issued by a demanded δ node
    with **no** certificate — so the case is exactly the `delta_obs` field at that node
    and position. Nothing is read off the row but the issuing node; no root is an
    observation and no other row issues one. -/
theorem observation_goal_of_demand {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (W : StepSuppliers Aw tbl Eₐ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} (D : TyP E n Γ e T)
    (θ φ ψ : Level → Level) (pos : ObsPos)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level)
    (ρ : List Disp) (hq : Demand (.observation D θ φ ψ pos S σ ρ))
    (ih : StepIH Aw tbl (.observation D θ φ ψ pos S σ ρ)) :
    Goal tbl (.observation D θ φ ψ pos S σ ρ) := by
  have hq' := hq
  cases hq with
  | issued issuer _ hiss e =>
    cases e with
    | delta_obs_out hk hap => exact W.delta_obs hiss _ hq' ih
    | delta_obs_gate hk hap => exact W.delta_obs hiss _ hq' ih

/-- **Rejection (Q269).** No live `Issues` row targets the frozen two-derivation
    `obsPair`, and no root is one: it is never demanded. -/
theorem obsPair_not_demanded {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {D₁ D₂ : TyP E n Γ e T} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
    {θ : Level → Level} {ρ : List Disp} (hq : Demand (.obsPair D₁ D₂ S θ ρ)) : False := by
  cases hq with
  | issued _ _ _ e => cases e

/-! ### the rank edges of the two receipt-bound rows -/

/-- The let-value `pb` request of `pb_letValue` is `Before` its issuer: the selected
    tail is a strict suffix of the frame receipt (`LetEntryAt.length_lt`), whatever the
    level map and display. -/
theorem letValue_before {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (Aw : Nat → Nat) (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n Γ₀) (σ σ' : Level → Level) (ρ ρ' : List Disp)
    {i : Nat} {Γ' : LCtx} {A₀ : Expr Nat} {u₀ : Level} {v₀ : Expr Nat}
    {hΓ' : CtxWfT E n Γ'} {hA : HasTyT E n Γ' A₀ (.sort u₀)} {hv : HasTyT E n Γ' v₀ A₀}
    (hsel : LetEntryAt S.ctx i hΓ' hA hv) :
    Before Aw
      (.pb (enrichHasTyT_of_envWfT S.env hΓ' hv) (enrichHasTyT_of_envWfT S.env hΓ' hA)
        (S.tail hΓ') σ' ρ')
      (.pb D DT S σ ρ) :=
  before_of_lt_prefix Aw hsel.length_lt

/-- The δ admission observation of `delta_obs_out`/`delta_obs_gate` is `Before` its
    issuer **under the receipt's own admission weights**: same frame, and every atom of
    the selected `Db` lies under the δ node's weight (`delta_adm_below`, the landed S1
    δ row). For another `Aw` the descent needs `AgreeOn` (§7.3) — the `es_delta`
    field's retained payment obligation. -/
theorem delta_obs_before {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E n₀ Γ₀) (σ θ φ ψ : Level → Level)
    (pos : ObsPos) (ρ ρ' : List Disp) :
    Before (enrichEnvWfT S.env).admW
      (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv θ φ ψ pos S σ ρ')
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ) :=
  before_of_same_prefix _ rfl
    (lexDM_combMeas_mono _ _ (lex_of_dm
      (dmStep_under_rule (enrichEnvWfT S.env).admW
        (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) rfl
        (delta_adm_below (enrichEnvWfT S.env) hres hbody htr hlen hwf hb dl dr))))

/-! ## §7 the step, by full dispatch over the ten tags -/

/-- **`Step` from the suppliers.** The `ResolvedView` half is the trivial view; the
    `Goal` half dispatches on the tag. `.cts`, `.bitCoh` and `.head` are closed from the
    IH; `.observation` is the `delta_obs` field at the issuing δ node
    (`observation_goal_of_demand`); `.slot` and the frozen `.obsPair` are not demanded. -/
theorem step_of_suppliers {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ) : Step Aw tbl Eₐ := by
  intro q hq ih
  refine ⟨⟨trivialView Aw q⟩, ?_⟩
  cases q with
  | es h S σ ρ => exact es_goal_of_suppliers Aw tbl hTbl W h S σ ρ hq ih
  | cl D₁ D₂ S σ ρ => exact W.cl_case D₁ D₂ S σ ρ hq ih
  | eut D₁ D₂ S σ ρ => exact W.eut_case D₁ D₂ S σ ρ hq ih
  | cts h DX S ρ => exact cts_goal_of_ports Aw tbl hTbl h DX S ρ hq ih
  | pb D DT S σ ρ => exact W.pb_case D DT S σ ρ hq ih
  | bitCoh D₁ D₂ S σ ρ =>
      -- the `.eut` case at the SAME rank (row `bitCoh_eut`): a local data dependency,
      -- not an IH edge (S9 §5)
      have heut : EUT tbl σ ρ D₁ D₂ :=
        W.eut_case D₁ D₂ S σ ρ (.issued _ _ hq Issues.bitCoh_eut) (fun q' hd hb => ih q' hd hb)
      exact bitCoh_goal_of_ports Aw tbl hTbl D₁ D₂ S σ ρ hq ih heut
  | mixed D₁ D₂ S σ ρ => exact W.mixed_case D₁ D₂ S σ ρ hq ih
  | head c uL uR dL dR S σ ρ => exact head_goal_of_ih Aw tbl c dL dR S σ ρ hq ih
  | slot u uD hres dSlot ls S σ ρ => exact (slot_not_demanded hq).elim
  | observation D θ φ ψ pos S σ ρ =>
      exact observation_goal_of_demand Aw tbl W D θ φ ψ pos S σ ρ hq ih
  | obsPair D₁ D₂ S θ ρ => exact (obsPair_not_demanded hq).elim

/-! ## §8 the S15 §6 chain: `Step → AllBelowScoped → SortCoh` -/

/-- Every public `BelowScoped` conclusion is the `Goal` of a demanded root (the root
    constructors of `Demand` take exactly the public fields' `AssumpPref` and
    `LevelHom`), so `solve_of_step` projects `Step` straight onto `AllBelowScoped`. -/
theorem allBelowScoped_of_step {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : Step Aw tbl Eₐ) : AllBelowScoped Eₐ Aw tbl := fun _bound =>
  { es := fun h hAP S σ hσ _hlt =>
        (solve_of_step Aw tbl step (.es h S σ (S.can σ)) (.rootEs h hAP S σ hσ)).2
    cl := fun D₁ D₂ h₁ h₂ S σ hσ _hlt =>
        (solve_of_step Aw tbl step (.cl D₁ D₂ S σ (S.can σ)) (.rootCl D₁ D₂ h₁ h₂ S σ hσ)).2
    eut := fun D₁ D₂ h₁ h₂ S σ hσ _hlt =>
        (solve_of_step Aw tbl step (.eut D₁ D₂ S σ (S.can σ)) (.rootEut D₁ D₂ h₁ h₂ S σ hσ)).2
    cts := fun h DX hAP hDX S _hlt =>
        (solve_of_step Aw tbl step (.cts h DX S (S.can id)) (.rootCts h DX hAP hDX S)).2
    pb := fun D DT hD hDT S σ hσ _hlt =>
        (solve_of_step Aw tbl step (.pb D DT S σ (S.can σ)) (.rootPb D DT hD hDT S σ hσ)).2
    bitCoh := fun D₁ D₂ h₁ h₂ S σ hσ _hlt =>
        (solve_of_step Aw tbl step (.bitCoh D₁ D₂ S σ (S.can σ))
          (.rootBitCoh D₁ D₂ h₁ h₂ S σ hσ)).2 }

/-- The S15 §6 chain from the suppliers: `step_of_suppliers` → `solve_of_step` →
    `AllBelowScoped`. Conditional on `W`; nothing here produces a field. -/
theorem allBelowScoped_of_suppliers {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ) : AllBelowScoped Eₐ Aw tbl :=
  allBelowScoped_of_step Aw tbl (step_of_suppliers Aw tbl hTbl W)

/-- The intended native consumer (`sortCoh_at_call`'s shape), conditional on `W`. -/
theorem sortCoh_of_suppliers {Eₐ E : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    {n : Nat} {Γ : LCtx} {σ : Level → Level}
    (hTbl : TableWF tbl) (W : StepSuppliers Aw tbl Eₐ)
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ)
    {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (h₁ : D₁.AssumpPref) (h₂ : D₂.AssumpPref) : SortCoh σ D₁ D₂ :=
  sortCoh_of_allBelowScoped (allBelowScoped_of_suppliers Aw tbl hTbl W) hTbl S hσ D₁ D₂ h₁ h₂

/-! ## §9 Q267 — the two countermodels as frozen controls, and their rejection

The Codex gpt-6.1-sol re-audit of #7430 (Q267) refuted the ITEM 2 layer with two
kernel-checked demanded-query countermodels. Both are reproduced here **verbatim**
against the frozen ITEM 2 shapes (`DemandFree`, `RoutedDispFree`, `StepFree`), and
each is shown to be rejected by the repaired layer as far as the repaired
definitions decide it. -/

/-- `Step` over the frozen `DemandFree` (the Q267 shape of issuance). -/
abbrev StepFree (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ q : P2Query Eₐ, DemandFree q →
    (∀ q' : P2Query Eₐ, DemandFree q' → Before Aw q' q → Answer Aw tbl q') →
    Answer Aw tbl q

/-- The wrapper over `DemandFree` (the same well-founded induction as `solve_of_step`). -/
theorem solve_of_stepFree {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : StepFree Aw tbl Eₐ) : ∀ q : P2Query Eₐ, DemandFree q → Answer Aw tbl q := by
  have allAt : ∀ k : Key, ∀ q : P2Query Eₐ, q.rank Aw = k → DemandFree q → Answer Aw tbl q :=
    keyLT_wf.fix (fun k ih q hkey hq =>
      step q hq (fun q' hq' hlt =>
        ih (q'.rank Aw) (by unfold Before at hlt; rwa [hkey] at hlt) q' rfl hq'))
  intro q hq
  exact allAt (q.rank Aw) q rfl hq

namespace Q267HeadInjection

/-- the genuine context `[x : sort 0]` -/
def Γ : LCtx := [.assumption (.sort .zero)]

def C : CtxP emptyEnv 0 Γ :=
  .assumption emptyEnv 0 [] (.sort .zero) (.succ .zero) (.nil emptyEnv 0) pinSortP

def dR : TyP emptyEnv 0 Γ (.sort .zero) (.sort (.succ .zero)) :=
  .sort emptyEnv 0 Γ .zero (.succ .zero) (eqN_refl _)

def dL : TyP emptyEnv 0 Γ (.bvar 0) (.sort .zero) :=
  .bvar emptyEnv 0 Γ 0 (.sort .zero) (.succ .zero) rfl dR

def c : CvP emptyEnv 0 Γ (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .refl emptyEnv 0 Γ (.sort .zero) (.sort (.succ .zero)) dR dR dR

/-- the injected head: a reflexive path on `sort 0` with **unrelated** kind sources
    `bvar 0 : sort 0` and `sort 0 : sort 1`, under the empty frame `nilScope` -/
noncomputable def q : P2Query emptyEnv :=
  .head c .zero (.succ .zero) dL dR nilScope id (C.disp id)

/-- a genuine admitted canonical public issuer -/
noncomputable def issuer : P2Query emptyEnv :=
  .pb pinSortP
    (.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    nilScope id (nilScope.can id)

theorem issuer_demandedFree : DemandFree issuer :=
  .rootPb pinSortP
    (.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    trivial trivial nilScope id levelHom_id

theorem q_ap : q.AP := ⟨⟨trivial, trivial, trivial⟩, trivial, trivial⟩

theorem q_hom : q.Hom := levelHom_id

theorem q_routedFree : q.RoutedFree := RoutedDispFree.canon C

/-- **Frozen (Q267 P1).** Under the ITEM 2 shape nothing ties `q` to its issuer. -/
theorem q_demandedFree : DemandFree q :=
  .issued issuer q issuer_demandedFree (.levelMap id) q_ap q_hom q_routedFree

/-- `Goal` ignores `c`, `dL`, `dR` and reads the arbitrary bits: `true = false`. -/
theorem q_goal_false (tbl : List CRule) : ¬ Goal tbl q := fun h =>
  Bool.noConfusion (h : true = false)

/-- **Frozen control.** The `Step` over the ITEM 2 shape is refuted, for every `Aw`
    and every `tbl`. -/
theorem no_stepFree (Aw : Nat → Nat) (tbl : List CRule) : ¬ StepFree Aw tbl emptyEnv :=
  fun step => q_goal_false tbl (solve_of_stepFree Aw tbl step q q_demandedFree).2

/-- **Rejected by the repaired layer.** The audit's exact edge does not exist: no row
    of `Issues` lets the `pb` root issue `q`. -/
theorem issuer_not_issues : ¬ Issues issuer q := fun e => by
  dsimp only [issuer, q] at e
  cases e

/-- **Rejected by the repaired layer, outright.** `q` is not demanded at all: every
    demanded head has its sources bound to the path's endpoints
    (`Demand.head_bound`), and `q`'s left source types `bvar 0`, not the path's
    endpoint `sort 0`. -/
theorem q_not_demanded : ¬ Demand q := fun h =>
  Expr.noConfusion (Demand.head_bound h).1

end Q267HeadInjection

namespace Q267RoutedEsub

def Γ : LCtx := [.assumption (.sort .zero)]

def dR : TyP emptyEnv 0 Γ (.sort .zero) (.sort (.succ .zero)) :=
  .sort emptyEnv 0 Γ .zero (.succ .zero) (eqN_refl _)

def dL : TyP emptyEnv 0 Γ (.bvar 0) (.sort .zero) :=
  .bvar emptyEnv 0 Γ 0 (.sort .zero) (.succ .zero) rfl dR

/-- **Frozen (Q267 P1, esub).** `Γ`'s genuine canonical display is `[keep]`; the
    free-`u` arm inserts `drop` from `u := .zero` without any replacement / type
    certificate. -/
theorem routed_bad_free : RoutedDispFree id emptyEnv 0 Γ [.drop] :=
  RoutedDispFree.esub (σ := id) (E := emptyEnv) (n := 0)
    (Γ := Γ) (ρ := []) (t := .sort .zero) (v := .sort .zero) (j := 0)
    .zero rfl (RoutedDispFree.canon (CtxP.nil emptyEnv 0))

/-- the ordinary `pb` query at the wrong display -/
noncomputable def q : P2Query emptyEnv := .pb dL dR nilScope id [.drop]

noncomputable def issuer : P2Query emptyEnv :=
  .pb pinSortP
    (.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    nilScope id (nilScope.can id)

theorem issuer_demandedFree : DemandFree issuer :=
  .rootPb pinSortP
    (.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    trivial trivial nilScope id levelHom_id

theorem q_demandedFree : DemandFree q :=
  .issued issuer q issuer_demandedFree (.levelMap id)
    ⟨trivial, trivial⟩ levelHom_id routed_bad_free

/-- at `[.drop]` the variable erases to `star` while its type's kind bit is `false`:
    `false = true`. -/
theorem q_goal_false (tbl : List CRule) : ¬ Goal tbl q := fun h =>
  Bool.noConfusion (h.mp rfl : false = true)

/-- **Frozen control.** The `Step` over the ITEM 2 shape is refuted, for every `Aw`
    and every `tbl`. -/
theorem no_stepFree (Aw : Nat → Nat) (tbl : List CRule) : ¬ StepFree Aw tbl emptyEnv :=
  fun step => q_goal_false tbl (solve_of_stepFree Aw tbl step q q_demandedFree).2

/-- **Rejected by the repaired layer.** The audit's exact edge does not exist: no row
    of `Issues` lets the `pb` root issue `q`. -/
theorem issuer_not_issues : ¬ Issues issuer q := fun e => by
  dsimp only [issuer, q] at e
  cases e

/-- **Rejected by the repaired layer, as far as the definitions decide it.** The only
    `esub` arm left prices the display `[.drop]` at this site at the node's actual
    `hv`/`hvT` — here both are a typing `sort 0 : sort 0` in the empty context, a
    Prop-sorted sort. The audit's `routed_bad` term no longer elaborates. What is
    **not** claimed: `¬ RoutedDisp id emptyEnv 0 Γ [.drop]` outright (and hence
    `¬ Demand q`) — that is the display-validity statement of `SortCoh` strength: a
    sort-typing inversion through `conv` which is not on the tree. -/
theorem routed_drop_needs_prop_sort (hv : TyP emptyEnv 0 [] (.sort .zero) (.sort .zero)) :
    RoutedDisp id emptyEnv 0 Γ [.drop] :=
  RoutedDisp.esub (σ := id) (E := emptyEnv) (n := 0)
    (Γ := Γ) (ρ := []) (t := .sort .zero) (v := .sort .zero) (j := 0) (u := .zero)
    rfl hv hv (RoutedDisp.canon (CtxP.nil emptyEnv 0))

end Q267RoutedEsub

/-! ## §10 Q269 — the two observation countermodels as frozen controls, and their rejection

The Codex gpt-6.1-sol re-audit of #7430 (Q269) refuted the ITEM 3 layer with two
kernel-checked countermodels against the two-derivation observation request: `occ_obs`
on a `rootCl` whose two payload leaves are the direct `sort 0 : sort 1` typing and the same
judgment through an `esub` into an unused assumption (`outLevels` `[0]` vs `[0, 0]`,
`gateLevels` `[]` vs `[2]`), and `delta_obs` on a real δ root (`hb` against `dr`, the
same two derivations). Both are reproduced **verbatim** against the frozen shapes
(`P2Query.obsPair`, `IssuesObsFree`, `DemandObsFree`, `StepObsFree`) and rejected by the
repaired layer. -/

/-- `Step` over the frozen `DemandObsFree` (the Q269 shape of observation issuance). -/
abbrev StepObsFree (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop :=
  ∀ q : P2Query Eₐ, DemandObsFree q →
    (∀ q' : P2Query Eₐ, DemandObsFree q' → Before Aw q' q → Answer Aw tbl q') →
    Answer Aw tbl q

/-- The wrapper over `DemandObsFree` (the same well-founded induction as `solve_of_step`). -/
theorem solve_of_stepObsFree {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : StepObsFree Aw tbl Eₐ) : ∀ q : P2Query Eₐ, DemandObsFree q → Answer Aw tbl q := by
  have allAt : ∀ k : Key, ∀ q : P2Query Eₐ, q.rank Aw = k → DemandObsFree q → Answer Aw tbl q :=
    keyLT_wf.fix (fun k ih q hkey hq =>
      step q hq (fun q' hq' hlt =>
        ih (q'.rank Aw) (by unfold Before at hlt; rwa [hkey] at hlt) q' rfl hq'))
  intro q hq
  exact allAt (q.rank Aw) q rfl hq

namespace Q269ObservationAudit

abbrev s0 : Expr Nat := .sort .zero
abbrev s1 : Expr Nat := .sort (.succ .zero)
abbrev s2 : Expr Nat := .sort (.succ (.succ .zero))
abbrev sourceCtx : LCtx := [.assumption s1]

/-- the direct `sort 0 : sort 1` typing -/
def direct : TyP emptyEnv 0 [] s0 s1 :=
  .sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)

def source : TyP emptyEnv 0 sourceCtx s0 s1 :=
  .sort emptyEnv 0 sourceCtx .zero (.succ .zero) (eqN_refl _)

def replacementType : TyP emptyEnv 0 [] s1 s2 :=
  .sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- the same judgment through an `esub` into an unused assumption -/
def padded : TyP emptyEnv 0 [] s0 s1 :=
  .esub emptyEnv 0 sourceCtx s0 s1 s1 s0 0 (.succ (.succ .zero))
    source rfl direct replacementType

theorem padded_ap : padded.AssumpPref :=
  ⟨assumptionPrefix_zero _, trivial, trivial, trivial⟩

noncomputable def issuer : P2Query emptyEnv :=
  .cl direct padded nilScope id (nilScope.can id)

/-- the frozen two-derivation observation the ITEM 3 `occ_obs` issued -/
noncomputable def observation : P2Query emptyEnv :=
  .obsPair direct padded nilScope id (nilScope.can id)

theorem issuer_demanded : Demand issuer :=
  .rootCl direct padded trivial padded_ap nilScope id levelHom_id

theorem issue : IssuesObsFree issuer observation :=
  .occ_obs (k₁ := 0) (k₂ := 1) (p₁ := []) (p₂ := []) rfl rfl trivial padded_ap

theorem observation_demandedObsFree : DemandObsFree observation :=
  .issued issuer observation (.live issuer issuer_demanded) issue

theorem direct_out : direct.outLevels id = [.zero] := rfl
theorem padded_out : padded.outLevels id = [.zero, .zero] := rfl
theorem direct_gates : direct.gateLevels id = [] := rfl
theorem padded_gates : padded.gateLevels id = [.succ (.succ .zero)] := rfl

/-- the zipped gate goal is definitionally `False` -/
theorem observation_goal_false (tbl : List CRule) : ¬ Goal tbl observation := fun h => h.2

/-- **Frozen control:** the `Step` over the ITEM 3 observation rows is refuted. -/
theorem no_stepObsFree (Aw : Nat → Nat) (tbl : List CRule) : ¬ StepObsFree Aw tbl emptyEnv :=
  fun step => observation_goal_false tbl
    (solve_of_stepObsFree Aw tbl step observation observation_demandedObsFree).2

/-- **Rejected by the repaired layer:** the two-derivation observation is not demanded. -/
theorem observation_not_demanded : ¬ Demand observation := fun h => obsPair_not_demanded h

end Q269ObservationAudit

namespace Q269DeltaObservationIndependent

abbrev u0 : Level := .zero
abbrev u1 : Level := .succ u0
abbrev u2 : Level := .succ u1

/-- a transparent arity-zero definition with body `sort 0` and type `sort 1` -/
def member : CheckedMember := ⟨.definitionM, 0, .sort u1, some (.sort u0)⟩
def E : ResolvedEnv := extendEnv emptyEnv 0 member

def ewf : EnvWfT E :=
  EnvWfT.definition emptyEnv 0 (.sort u1) (.sort u0) u2 .empty rfl
    (HasTyT.sort [] u1) (HasTyT.sort [] u0)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

def scope : ScopedCtx E E 0 [] := ⟨ewf, envExt_refl E, .nil⟩

def H : TyP E 0 [] (.sort u0) (.sort u1) :=
  .sort E 0 [] u0 u1 (eqN_refl _)

def W : TyP E 0 [] (.sort u1) (.sort u2) :=
  .sort E 0 [] u1 u2 (eqN_refl _)

def D : TyP E 0 [.assumption (.sort u1)] (.sort u0) (.sort u1) :=
  .sort E 0 [.assumption (.sort u1)] u0 u1 (eqN_refl _)

def Hs : TyP E 0 [] (.sort u0) (.sort u1) :=
  .esub E 0 [.assumption (.sort u1)]
    (.sort u0) (.sort u1) (.sort u1) (.sort u0) 0 u2 D rfl H W

theorem hs_ap : Hs.AssumpPref :=
  ⟨assumptionPrefix_zero _, trivial, trivial, trivial⟩

def left : TyP E 0 [] (.const 0 []) (.sort u1) :=
  .const E 0 [] 0 [] [] member u2 rfl rfl rfl trivial W

/-- the real AP δ root: `hb = H`, `dr = Hs` -/
def conversion : CvP E 0 [] (.const 0 []) (.sort u0) (.sort u1) :=
  .delta E 0 [] 0 [] member (.sort u0) rfl rfl rfl rfl rfl H left Hs

theorem conversion_ap : conversion.AssumpPref :=
  ⟨trivial, trivial, hs_ap⟩

noncomputable def issuer : P2Query E :=
  .es conversion scope id (scope.can id)

/-- the frozen two-derivation observation the ITEM 3 `delta_obs` issued directly -/
noncomputable def q : P2Query E :=
  .obsPair H Hs scope id (scope.can id)

theorem issuer_demanded : Demand issuer :=
  .rootEs conversion conversion_ap scope id levelHom_id

theorem edge : IssuesObsFree issuer q := IssuesObsFree.delta_obs

theorem q_demandedObsFree : DemandObsFree q :=
  .issued issuer q (.live issuer issuer_demanded) edge

/-- `H.gateLevels id = []`, `Hs.gateLevels id = [u2]`: the zipped gate goal is `False`. -/
theorem q_goal_false (tbl : List CRule) : ¬ Goal tbl q := fun h => (h.2 : False)

/-- **Frozen control:** refuted without `occ_obs`, by the δ row alone. -/
theorem no_stepObsFree (Aw : Nat → Nat) (tbl : List CRule) : ¬ StepObsFree Aw tbl E :=
  fun step => q_goal_false tbl (solve_of_stepObsFree Aw tbl step q q_demandedObsFree).2

/-- **Rejected by the repaired layer:** not demanded. The repaired δ rows issue only single
    positions of `((enrichEnvWfT scope.env).defAdm …).hv` — the receipt's own admission of
    member `0` — never `H` against `Hs`. -/
theorem q_not_demanded : ¬ Demand q := fun h => obsPair_not_demanded h

end Q269DeltaObservationIndependent

end Rcic.Syn

#print axioms Rcic.Syn.lexDM_combMeas_mono
#print axioms Rcic.Syn.rule_sub_before
#print axioms Rcic.Syn.binder_body_before
#print axioms Rcic.Syn.binder_body_not_before
#print axioms Rcic.Syn.step_refuted_const_zero
#print axioms Rcic.Syn.Issues.ap
#print axioms Rcic.Syn.Issues.hom
#print axioms Rcic.Syn.Issues.routed
#print axioms Rcic.Syn.Demand.head_bound
#print axioms Rcic.Syn.head_goal_of_ih
#print axioms Rcic.Syn.slot_not_demanded
#print axioms Rcic.Syn.es_goal_of_suppliers
#print axioms Rcic.Syn.step_of_suppliers
#print axioms Rcic.Syn.allBelowScoped_of_step
#print axioms Rcic.Syn.allBelowScoped_of_suppliers
#print axioms Rcic.Syn.sortCoh_of_suppliers
#print axioms Rcic.Syn.Q267HeadInjection.no_stepFree
#print axioms Rcic.Syn.Q267HeadInjection.issuer_not_issues
#print axioms Rcic.Syn.Q267HeadInjection.q_not_demanded
#print axioms Rcic.Syn.Q267RoutedEsub.no_stepFree
#print axioms Rcic.Syn.Q267RoutedEsub.issuer_not_issues
#print axioms Rcic.Syn.Q267RoutedEsub.routed_drop_needs_prop_sort
#print axioms Rcic.Syn.LetEntryAt.drop_eq
#print axioms Rcic.Syn.LetEntryAt.length_lt
#print axioms Rcic.Syn.cts_goal_of_ports
#print axioms Rcic.Syn.bitCoh_goal_of_ports
#print axioms Rcic.Syn.observation_goal_of_demand
#print axioms Rcic.Syn.obsPair_not_demanded
#print axioms Rcic.Syn.letValue_before
#print axioms Rcic.Syn.delta_obs_before
#print axioms Rcic.Syn.Q269ObservationAudit.padded_ap
#print axioms Rcic.Syn.Q269ObservationAudit.padded_gates
#print axioms Rcic.Syn.Q269ObservationAudit.no_stepObsFree
#print axioms Rcic.Syn.Q269ObservationAudit.observation_not_demanded
#print axioms Rcic.Syn.Q269DeltaObservationIndependent.ewf
#print axioms Rcic.Syn.Q269DeltaObservationIndependent.no_stepObsFree
#print axioms Rcic.Syn.Q269DeltaObservationIndependent.q_not_demanded
