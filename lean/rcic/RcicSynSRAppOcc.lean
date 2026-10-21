/- Author: GLM 5.3 (via kilo) — sortRow row 8 `es_app` closure attempt.

Row 8 of `RcicSynTableOfICensus` lists three missing lemma groups for the
`es_app` supplier: `app_leftSurface_cl`, `app_drClause` (`AppClauseNeed`), and
`es_app_occ*_transport` (the `subAt` occurrence receipts for transport-headed
conversions/endpoints).

This module kernel-refutes the `es_app_occ*_transport` arm: for a
transport-headed `h1` (here `CvP.ewk` over the `RcicSynClosedEsapp`
fixture), `h1.dr` is a freshly re-wrapped transport typing — the same
phenomenon `RcicSynClosedEsbeta` documents for `es_beta` — and never occurs
inside the step payload's `dchildren` forest. The missing occurrence lemma is
stated once as `EsAppOccTransportWall` and refuted at the `esAppEwk`
fixture, so the receipt route cannot supply `EsAppClosedPorts.occH1`.

`app_leftSurface_cl` and `app_drClause` remain the row's open requirements:
`drClause` is consistent (the `esub` `inst`-composition and the `Prop`
`levelIsZero` gate propagate identically to both sides of the clause
equation), and `leftCl` is the named surface-`CL` wall.

§4 restates the row-8 residual wall as exactly what the landed closer
`es_app_field_closed` consumes — `EsAppSortRowWall`, the ∀-quantified
`EsAppClosedPorts` obligation — refutes it at the same `.ewk` fixture (the
ports structure is uninhabitable there since both `occH1` disjuncts die),
and ships `es_app_tableI`, the conditional field pin at `tableOfI hW`
consuming only that wall + `hW` + field data. -/

import rcic.RcicSynClosedEsapp
import rcic.RcicSynTableBuildI

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 occurrence-forest membership -/

/-- `DNode.Reach d t`: `t` lies in `d`'s transitive `children` forest
    (reflexive). The payload occurrence receipts of `es_app`'s ports are
    exactly `subAt`-hits, i.e. `Reach` hits. -/
inductive DNode.Reach : DNode → DNode → Prop
  | self {d : DNode} : DNode.Reach d d
  | step {d c t : DNode} (hc : c ∈ d.children) (r : DNode.Reach c t) :
      DNode.Reach d t

/-- `subAt` lands only on forest members. -/
theorem DNode.subAt_reach {d t : DNode} {p : List Nat}
    (h : d.subAt p = some t) : DNode.Reach d t := by
  induction p generalizing d with
  | nil =>
      simp only [DNode.subAt, Option.some.injEq] at h
      subst h; exact .self
  | cons i rest ih =>
      simp only [DNode.subAt, Option.bind_eq_some] at h
      obtain ⟨c, hc, hrest⟩ := h
      exact .step (List.getElem?_mem hc) (ih hrest)

/-- One-step unfold of `Reach`: either the node itself or a child that
    reaches. -/
theorem DNode.Reach.unfold {d t : DNode} (h : DNode.Reach d t) :
    t = d ∨ ∃ c ∈ d.children, DNode.Reach c t := by
  cases h with
  | self => exact .inl rfl
  | step hc hr => exact .inr ⟨_, hc, hr⟩

/-! ## §2 the transport fixture -/

/-- An `.ewk`-headed function conversion: the reflexive `esappH1` carried
    through the identity environment extension. -/
def esAppEwkH1 : CvP emptyEnv 0 esappFixtureΓ (.bvar 1) (.bvar 1)
    (.pi (.sort .zero) (.sort .zero)) :=
  .ewk emptyEnv emptyEnv 0 esappFixtureΓ (.bvar 1) (.bvar 1)
    (.pi (.sort .zero) (.sort .zero)) (envExt_refl emptyEnv) esappH1

/-- `esAppEwkH1` is transport-headed. -/
theorem esAppEwkH1_isTransport : esAppEwkH1.isTransport = true := rfl

/-- The `.es` step whose function leg is `esAppEwkH1`. -/
def esAppEwkCvp : CvP emptyEnv 0 esappFixtureΓ
    (.app (.bvar 1) (.bvar 0)) (.app (.bvar 1) (.bvar 0))
    (instantiate0 (.bvar 0) (.sort .zero)) :=
  .app emptyEnv 0 esappFixtureΓ (.bvar 1) (.bvar 1) (.bvar 0) (.bvar 0)
    (.sort .zero) (.sort .zero) esAppEwkH1 esappH2 esappDl esappDl

/-! ## §3 leaf and subtree exclusions -/

/-- A node with empty `children` reaches only itself; the `.ewk` target never
    equals a non-`.ewk`-headed node. -/
theorem esApp_notReach_leaf {d : DNode}
    (hr : DNode.Reach d (.ty esAppEwkH1.dr)) (hd : d.children = [])
    (hne : .ty esAppEwkH1.dr ≠ d) : False := by
  obtain h | ⟨c, hc, -⟩ := hr.unfold
  · exact hne h
  · rw [hd] at hc; exact absurd hc (List.not_mem_nil _)

/-- `esappS0` is a `.sort` leaf. -/
theorem esappS0_notReach
    (hr : DNode.Reach (.ty esappS0) (.ty esAppEwkH1.dr)) : False :=
  esApp_notReach_leaf hr rfl (by intro e; cases e)

/-- `esappPiT`'s children are the two `.sort` typings. -/
theorem esappPiT_notReach
    (hr : DNode.Reach (.ty esappPiT) (.ty esAppEwkH1.dr)) : False := by
  obtain h | ⟨c, hc, hr⟩ := hr.unfold
  · cases h
  · simp only [esappPiT, DNode.children, TyP.dchildren, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact esappS0_notReach hr
    · exact esApp_notReach_leaf hr rfl (by intro e; cases e)

/-- `esappHf` (a `.bvar`) reaches only `esappPiT`. -/
theorem esappHf_notReach
    (hr : DNode.Reach (.ty esappHf) (.ty esAppEwkH1.dr)) : False := by
  obtain h | ⟨c, hc, hr⟩ := hr.unfold
  · cases h
  · simp only [esappHf, DNode.children, TyP.dchildren, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl
    exact esappPiT_notReach hr

/-- `esappHa` (a `.bvar`) reaches only `esappS0`. -/
theorem esappHa_notReach
    (hr : DNode.Reach (.ty esappHa) (.ty esAppEwkH1.dr)) : False := by
  obtain h | ⟨c, hc, hr⟩ := hr.unfold
  · cases h
  · simp only [esappHa, DNode.children, TyP.dchildren, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl
    exact esappS0_notReach hr

/-- `esappDl`'s app children are `esappHf`, `esappHa`, `esappS0`. -/
theorem esappDl_notReach
    (hr : DNode.Reach (.ty esappDl) (.ty esAppEwkH1.dr)) : False := by
  obtain h | ⟨c, hc, hr⟩ := hr.unfold
  · cases h
  · simp only [esappDl, DNode.children, TyP.dchildren, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact esappHf_notReach hr
    · exact esappHa_notReach hr
    · exact esappS0_notReach hr

/-- `esappH1` (`.refl`) reaches only `.ty esappHf`. -/
theorem esappH1_notReach
    (hr : DNode.Reach (.cv esappH1) (.ty esAppEwkH1.dr)) : False := by
  obtain h | ⟨c, hc, hr⟩ := hr.unfold
  · exact DNode.noConfusion h
  · simp only [esappH1, DNode.children, CvP.dchildren, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      exact esappHf_notReach hr

/-- `esappH2` (`.refl`) reaches only `.ty esappHa`. -/
theorem esappH2_notReach
    (hr : DNode.Reach (.cv esappH2) (.ty esAppEwkH1.dr)) : False := by
  obtain h | ⟨c, hc, hr⟩ := hr.unfold
  · exact DNode.noConfusion h
  · simp only [esappH2, DNode.children, CvP.dchildren, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      exact esappHa_notReach hr

/-- `esAppEwkH1` (`.ewk`) reaches only `.cv esappH1`. -/
theorem esAppEwkH1_notReach
    (hr : DNode.Reach (.cv esAppEwkH1) (.ty esAppEwkH1.dr)) : False := by
  obtain h | ⟨c, hc, hr⟩ := hr.unfold
  · exact DNode.noConfusion h
  · simp only [esAppEwkH1, DNode.children, CvP.dchildren, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl
    exact esappH1_notReach hr

/-- `.ty esAppEwkH1.dr` — the `.ewk`-re-wrapped `esappHf` — is not a
    `dchildren` descendant of the step's payload node. -/
theorem esAppEwk_dr_notReach :
    ¬ DNode.Reach (.cv esAppEwkCvp) (.ty esAppEwkH1.dr) := by
  intro h
  obtain h | ⟨c, hc, hr⟩ := h.unfold
  · exact DNode.noConfusion h
  · simp only [esAppEwkCvp, DNode.children, CvP.dchildren, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact esAppEwkH1_notReach hr
    · exact esappH2_notReach hr
    · exact esappDl_notReach hr
    · exact esappDl_notReach hr

/-! ## §4 the query-level refutation and the wall -/

/-- The occurrence receipt the ports require for `occH1` does not exist at
    this step: no child path resolves to `.ty esAppEwkH1.dr`. -/
theorem es_app_occH1_ewk_ne :
    ¬ ∃ p, P2Query.subAt
      (.es esAppEwkCvp nilScope id [.keep, .keep]) 0 p =
        some (.ty esAppEwkH1.dr) := by
  rintro ⟨p, hp⟩
  exact esAppEwk_dr_notReach (DNode.subAt_reach hp)

/-- The refuted `.inl` receipt fragment (row 8 `es_app`, transport arms):
    the `occH1`-family receipt exists for **every** `CvP.app` step including
    transport-headed `h1`. Kernel-refuted at `esAppEwkH1`. This is the dead
    disjunct, not the row-8 residual wall — the wall is `EsAppSortRowWall`
    below, stated as exactly what `es_app_field_closed` consumes. -/
def EsAppOccTransportWall : Prop :=
  ∀ {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    {σ : Level → Level} {ρ : List Disp}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B)),
    h1.isTransport = true →
    ∃ p, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty h1.dr)

/-- Kernel refutation: `EsAppOccTransportWall` fails at the `esAppEwk`
    fixture with every premise inhabited. -/
theorem es_app_occWall_refuted : ¬ EsAppOccTransportWall := fun hw =>
  es_app_occH1_ewk_ne
    (hw (S := nilScope) (σ := id) (ρ := [.keep, .keep])
      esAppEwkH1 esappH2 esappDl esappDl rfl)

/-! ## §4 The closer's actual need — restated wall, refutation, conditional pin -/

/-- The row-8 residual wall stated as exactly what the landed closer
    `es_app_field_closed` consumes: for every conversion pair, endpoint
    typings, scoped context, level map and display list, the
    `EsAppClosedPorts` structure at the supplier's table. The closer is
    table-generic, so the wall quantifies `tbl`; `es_app_tableI` instantiates
    `tbl := tableOfI hW`. -/
def EsAppSortRowWall (Aw : Nat → Nat) : Prop :=
  ∀ (tbl : List CRule) {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    EsAppClosedPorts Aw tbl h1 h2 dl dr S σ ρ

/-- At the `.ewk` fixture the closer's ports structure is uninhabitable:
    `occH1`'s `.inl` receipt is `es_app_occH1_ewk_ne` and its `.inr` escape
    `isTransport = false` is refuted by `esAppEwkH1_isTransport`. -/
theorem es_app_closedPorts_ewk_uninhabitable (Aw : Nat → Nat) (tbl : List CRule) :
    ¬ EsAppClosedPorts Aw tbl esAppEwkH1 esappH2 esappDl esappDl
      nilScope id [.keep, .keep] := fun c => by
  cases c.occH1 with
  | inl h => exact es_app_occH1_ewk_ne h
  | inr h => rw [esAppEwkH1_isTransport] at h; exact Bool.noConfusion h

/-- The restated wall is refuted on the same fixture — the `.ewk` instance is
    one the ∀-quantified closer genuinely feeds. -/
theorem es_app_sortRowWall_refuted (Aw : Nat → Nat) : ¬ EsAppSortRowWall Aw :=
  fun hw => es_app_closedPorts_ewk_uninhabitable Aw []
    (hw [] esAppEwkH1 esappH2 esappDl esappDl nilScope id [.keep, .keep])

/-- The conditional field pin at `tableOfI hW`: given the restated ports wall
    plus the field data, the landed closer yields the `CvP.app` `CaseStep`
    at the `tableOfI` table. -/
theorem es_app_tableI (Aw : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E)
    (wall : EsAppSortRowWall Aw)
    {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E' n Γ f g (.pi A B)) (h2 : CvP E' n Γ a b A)
    (dl : TyP E' n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E' n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw (tableOfI hW)
      (.es (CvP.app E' n Γ f g a b A B h1 h2 dl dr) S σ ρ) :=
  es_app_field_closed Aw (tableOfI hW) h1 h2 dl dr S σ ρ
    (wall (tableOfI hW) h1 h2 dl dr S σ ρ)

end Rcic.Syn

#print axioms Rcic.Syn.DNode.subAt_reach
#print axioms Rcic.Syn.DNode.Reach.unfold
#print axioms Rcic.Syn.esAppEwkH1_isTransport
#print axioms Rcic.Syn.esApp_notReach_leaf
#print axioms Rcic.Syn.esappS0_notReach
#print axioms Rcic.Syn.esappPiT_notReach
#print axioms Rcic.Syn.esappHf_notReach
#print axioms Rcic.Syn.esappHa_notReach
#print axioms Rcic.Syn.esappDl_notReach
#print axioms Rcic.Syn.esappH1_notReach
#print axioms Rcic.Syn.esappH2_notReach
#print axioms Rcic.Syn.esAppEwkH1_notReach
#print axioms Rcic.Syn.esAppEwk_dr_notReach
#print axioms Rcic.Syn.es_app_occH1_ewk_ne
#print axioms Rcic.Syn.es_app_occWall_refuted
#print axioms Rcic.Syn.es_app_closedPorts_ewk_uninhabitable
#print axioms Rcic.Syn.es_app_sortRowWall_refuted
#print axioms Rcic.Syn.es_app_tableI
