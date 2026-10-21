import rcic.RcicSynTableOfIFull
import rcic.RcicSynClosedLete

/-!
# `RcicSynSortRowLetE` — sortRow row 11 (`es_letE`) at `tableOfI`

sr-letE lane (`briefs/sortrow-glm-common.md`, census row 11 `es_letE`).
Closes `StepSuppliers.es_letE` at `tbl := tableOfI hW`: ports already
provable are discharged, the residual is exactly one named `Prop`
(`LetESortRowWalls`), and the `occA` occurrence receipt is kernel-refuted
at a `wk`-headed `hA` (`not_letE_occA_wk`). `closure_claim = 0`.

## Discharge table (this branch)

| port | class | evidence |
|---|---|---|
| `w : CvWalkHyp E` | (a) | `cvWalkHyp_of_envWfT hE` (inside `es_letE_closed`) |
| `tableClosed` | (a) | `tableWF_tableOfI_full hE` (`RcicSynTableOfIFull`) |
| `displayFits` | **(a) new** | `displayFits_of_routedDisp hq.routed` — every `RoutedDisp` ctor preserves `DisplayFits`; `wk`/`esub`/`linst` reuse `displayFits_removeAt` (`RcicSynLetTrace:211`), `displayFits_insertDisp_assump` (`:246`), `displayFits_of_instLvlsCtx` (`RcicSynLetBridge:90`); `canon` via `dispShape_of_ctxP` + `DisplayFits.of_dispShape` |
| `leftSurfaceCl`, `body`, `rightSurfaceCl` | (d) | `LetESortRowWalls` — `CL`/`BodyAnswers` demand, no producer on this branch |
| `pA pvL pvR` + `occA occvL occvR` | (d) + refuted | `occA` absent at transport heads: `CvP.dchildren` of `.wk` is `[.cv h]` — `hA.dl = TyP.wk …` is wrapped, never a forest node; kernel countermodel `not_letE_occA_wk` at the real `let x : sort 0 := x; sort 0` node `srwkNode` |
-/

open Rcic.Declarative

namespace Rcic.Syn

/-- `canon` shape: `CtxP.disp` emits only `keep`/`drop`/`inline`, each at
    the matching declaration kind. -/
theorem displayFits_ctxP_disp (σ : Level → Level) {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → (C : CtxP E n Γ) → DisplayFits Γ (C.disp σ)
  | _, .nil _ _ => .nil []
  | _, .assumption _ _ _ _ u hC _ => by
      simp only [CtxP.disp]
      cases levelIsZero (σ u) with
      | true => exact .assumptionDrop (displayFits_ctxP_disp σ hC)
      | false => exact .assumptionKeep (displayFits_ctxP_disp σ hC)
  | _, .letBinding _ _ _ _ _ _ hC _ _ =>
      .letInline (displayFits_ctxP_disp σ hC)

/-- Every routed display fits its context: each `RoutedDisp` constructor
    keeps per-entry declaration-kind/disposition alignment. This is the
    `Demand.routed` side of `displayFits` — the port no longer needs to
    be a premise. -/
theorem displayFits_of_routedDisp {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} (h : RoutedDisp σ E n Γ ρ) : DisplayFits Γ ρ := by
  induction h with
  | canon C => exact displayFits_ctxP_disp _ C
  | assumption _ _ ih =>
      cases levelIsZero _ with
      | true => exact .assumptionDrop ih
      | false => exact .assumptionKeep ih
  | letDrop _ _ _ _ ih => exact .letDrop ih
  | letInline _ _ _ ih => exact .letInline ih
  | wk d c _ ih => exact displayFits_removeAt d c ih
  | esub hget _ _ _ ih =>
      have hget' := (List.get?_eq_getElem? _ _).symm ▸ hget
      refine displayFits_insertDisp_assump _ _ hget' ih _ ?_
      cases levelIsZero _ with
      | true => exact Or.inr rfl
      | false => exact Or.inl rfl
  | linst ls _ _ _ ih => exact displayFits_of_instLvlsCtx ls _ ih
  | ewk _ _ ih => exact ih
  | cctx _ _ ih =>
      cases ih with
      | assumptionKeep h₀ => exact .assumptionKeep h₀
      | assumptionDrop h₀ => exact .assumptionDrop h₀

/-! ## §1 the named wall and the field -/

/-- The residual per-node walls of `es_letE` at `tableOfI hE`, compressed
    to one named `Prop`: the two surface `CL` obligations, the
    `BodyAnswers` per-node demand on the body leg, and the three
    occurrence receipts `occA`/`occvL`/`occvR` for the transported
    `hA.dl`/`hv.dl`/`hv.dr` typings. `occA` is genuinely absent at
    transport heads — `not_letE_occA_wk`. -/
def LetESortRowWalls {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (tbl : List CRule) (hE : EnvWfT E) : Prop :=
  ∃ pA pvL pvR : List Nat,
    P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pA = some (.ty hA.dl) ∧
    P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvL = some (.ty hv.dl) ∧
    P2Query.subAt (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
        0 pvR = some (.ty hv.dr) ∧
    CL tbl σ ρ dl (letLeftSurface hA hv hb dl) ∧
    BodyAnswers (cvWalkHyp_of_envWfT hE) (iotaPack_of_cvWalkHyp (cvWalkHyp_of_envWfT hE))
      (fun hext' h => derivedIotaExt hext' h) tbl σ (envExt_refl E) hb.dr
      (packNilL (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv)
      (letDisp (hv.dl.eps σ ρ) :: ρ) [] .nil
      (letDisp (hv.dr.eps σ ρ) :: ρ) ∧
    CL tbl σ ρ (letRightSurface (cvWalkHyp_of_envWfT hE) hA hv hb.dr hb.dr.reg.1
      hb.dr.reg.2) dr

/-- Row 11's field at `tableOfI`: `es_letE` with `w`/`tableClosed`
    discharged by the `EnvWfT`/`TableWF` assembly data and `displayFits`
    discharged by `hq.routed`. The residual is `walls` alone. -/
theorem es_letE_sortRow
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hE : EnvWfT E) (walls : LetESortRowWalls hA hv hb dl dr S σ ρ (tableOfI hE) hE) :
    CaseStep Aw (tableOfI hE)
      (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ) :=
  fun hq ih =>
    let ⟨pA, pvL, pvR, occA, occvL, occvR, lcl, bdy, rcl⟩ := walls
    es_letE_closed Aw (tableOfI hE) hA hv hb dl dr S σ ρ hE
      (tableWF_tableOfI_full hE) (displayFits_of_routedDisp hq.routed)
      lcl pA pvL pvR occA occvL occvR bdy rcl hq ih

/-! ## §2 kernel refutation — `occA` at a `wk`-headed `hA`

At `hA = CvP.wk …`, `CvP.dchildren` lists only `[.cv h]`: the transported
typing `hA.dl = TyP.wk …` is wrapped inside the node and never appears in
the query's own forest, so `∃ pA, subAt q 0 pA = .ty hA.dl` is FALSE — the
`occA` route cannot produce the receipt in general. The countermodel is a
real `let` node (`let x : sort 0 := x; sort 0`) at `Γ = [x : sort 0]`,
not `emptyEnv`. -/

/-- `x : sort 0` — the weakening's inserted assumption. -/
def srwkΓ0 : LCtx := [.assumption lefixS0]

/-- `sort 0 : sort 1` at `srwkΓ0` (leaf `TyP.sort`). -/
def srwkS0T : TyP emptyEnv 0 srwkΓ0 lefixS0 lefixS1 :=
  TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _)

/-- `sort 1 : sort 2` at `srwkΓ0` (leaf `TyP.sort`). -/
def srwkS1T : TyP emptyEnv 0 srwkΓ0 lefixS1 lefixS2 :=
  TyP.sort emptyEnv 0 _ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- `sort 0 : sort 1` at `x : sort 0` over `srwkΓ0` — the `bvar`'s `hA`
    leaf. -/
def srwkS0T2 : TyP emptyEnv 0 (.assumption lefixS0 :: srwkΓ0) lefixS0 lefixS1 :=
  TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _)

/-- `x : sort 0` — leaf `TyP.bvar`. -/
def srwkBvarT : TyP emptyEnv 0 srwkΓ0 (.bvar 0) lefixS0 :=
  TyP.bvar emptyEnv 0 srwkΓ0 0 lefixS0 (.succ .zero) rfl srwkS0T

/-- the `v := x` conversion leg — `x ≡ x` at `sort 0`. -/
def srwkHv : CvP emptyEnv 0 srwkΓ0 (.bvar 0) (.bvar 0) lefixS0 :=
  CvP.refl emptyEnv 0 srwkΓ0 (.bvar 0) lefixS0 srwkBvarT srwkBvarT srwkBvarT

/-- `sort 0 : sort 1` under the fixture let-binding. -/
def srwkS0Tb : TyP emptyEnv 0 (.letBinding lefixS0 (.bvar 0) :: srwkΓ0)
    lefixS0 lefixS1 :=
  TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _)

/-- the body leg — `sort 0 ≡ sort 0` at `sort 1` under the let-binding. -/
def srwkHb : CvP emptyEnv 0 (.letBinding lefixS0 (.bvar 0) :: srwkΓ0)
    lefixS0 lefixS0 lefixS1 :=
  CvP.refl emptyEnv 0 _ lefixS0 lefixS1 srwkS0Tb srwkS0Tb srwkS0Tb

/-- `sort 0 ≡ sort 0` at `sort 1`, empty context — the `wk`-wrapped
    base. -/
def srwkH0 : CvP emptyEnv 0 [] lefixS0 lefixS0 lefixS1 :=
  CvP.refl emptyEnv 0 [] lefixS0 lefixS1 lefixH0 lefixH0 lefixH0

/-- **the `wk`-headed `hA`**: `sort 0 ≡ sort 0` weakened under
    `x : sort 0`. -/
def srwkHa : CvP emptyEnv 0 srwkΓ0 lefixS0 lefixS0 lefixS1 :=
  CvP.wk emptyEnv 0 [] lefixS0 lefixS0 lefixS1 (.assumption lefixS0) 0 srwkH0

/-- `let x : sort 0 := x; sort 0` at `sort 2` — both `dl` and `dr`
    (`instantiate0 (bvar 0) (sort 1) = sort 1`, typed at `sort 2`). -/
def srwkDl : TyP emptyEnv 0 srwkΓ0 (.letE lefixS0 (.bvar 0) lefixS0)
    (instantiate0 (.bvar 0) lefixS1) :=
  TyP.letE emptyEnv 0 srwkΓ0 lefixS0 (.succ .zero) (.bvar 0) lefixS1 lefixS0
    (.succ (.succ .zero)) srwkS0T srwkBvarT srwkS0Tb srwkS1T

/-- the `es` query node: `let x : sort 0 := x; sort 0 ≡ itself`. -/
def srwkNode : CvP emptyEnv 0 srwkΓ0
    (.letE lefixS0 (.bvar 0) lefixS0) (.letE lefixS0 (.bvar 0) lefixS0)
    (instantiate0 (.bvar 0) lefixS1) :=
  CvP.letE emptyEnv 0 srwkΓ0 lefixS0 lefixS0 (.bvar 0) (.bvar 0) lefixS0 lefixS0
    lefixS1 (.succ .zero) srwkHa srwkHv srwkHb srwkDl srwkDl

/-- head-shape test: is this `.ty` node headed by `TyP.wk`? Deciding on
    the constructor shape avoids the `lift`-indexed equalities that
    `DNode.noConfusion`/`cases` cannot solve (`lift c 1 e' = sort l`). -/
def DNode.isTyWk : DNode → Bool
  | .ty (TyP.wk _ _ _ _ _ _ _ _) => true
  | _ => false

/-- hereditary head-shape invariant: `d` and every descendant avoid a
    `.ty (TyP.wk …)` node. -/
inductive SubAtNoWk : DNode → Prop where
  | mk {d : DNode} : d.isTyWk = false →
      (∀ {c'}, c' ∈ d.children → SubAtNoWk c') → SubAtNoWk d

/-- `subAt` results of a `SubAtNoWk` tree are never `.ty (TyP.wk …)`. -/
theorem subAt_isTyWk_false {d : DNode} (h : SubAtNoWk d) :
    ∀ {p : List Nat} {d' : DNode}, d.subAt p = some d' → d'.isTyWk = false := by
  intro p d' hsub
  induction p generalizing d d' with
  | nil =>
      obtain ⟨h0, _⟩ := h
      have h' : some d = some d' := hsub
      rw [← Option.some.inj h']
      exact h0
  | cons i rest ih =>
      obtain ⟨_, hc⟩ := h
      have hsub' : (d.children[i]?).bind (fun x => x.subAt rest) = some d' := hsub
      cases hget : d.children[i]? with
      | none =>
          rw [hget] at hsub'
          exact Option.noConfusion hsub'
      | some c' =>
          rw [hget] at hsub'
          have hsub'' : c'.subAt rest = some d' := hsub'
          exact ih (hc (List.getElem?_mem hget)) hsub''

/-- a `TyP.sort` leaf: not a `wk` head, no children. -/
theorem subAtNoWk_leafSort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k : Level}
    {h : eqN k (.succ l)} : SubAtNoWk (.ty (TyP.sort E n Γ l k h)) := by
  refine .mk rfl ?_
  intro c' hmem
  rw [show (DNode.ty (TyP.sort E n Γ l k h)).children = [] from rfl] at hmem
  exact absurd hmem (List.not_mem_nil _)

/-- a `TyP.bvar` node: not a `wk` head; its single child is the entry
    typing. -/
theorem subAtNoWk_bvar {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat}
    {A : Expr Nat} {u : Level} {h : lookupType Γ i = some A}
    {hA : TyP E n Γ A (.sort u)} (hc : SubAtNoWk (.ty hA)) :
    SubAtNoWk (.ty (TyP.bvar E n Γ i A u h hA)) := by
  refine .mk rfl ?_
  intro c' hmem
  rw [show (DNode.ty (TyP.bvar E n Γ i A u h hA)).children = [.ty hA] from rfl] at hmem
  rcases List.mem_singleton.mp hmem with rfl
  exact hc

/-- a `TyP.letE` node: not a `wk` head; children are the four typing
    subderivations. -/
theorem subAtNoWk_letETy {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat}
    {u : Level} {value B body : Expr Nat} {w : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    {hT : TyP E n Γ (instantiate0 value B) (.sort w)}
    (c1 : SubAtNoWk (.ty hA)) (c2 : SubAtNoWk (.ty hv)) (c3 : SubAtNoWk (.ty hb))
    (c4 : SubAtNoWk (.ty hT)) :
    SubAtNoWk (.ty (TyP.letE E n Γ A u value B body w hA hv hb hT)) := by
  refine .mk rfl ?_
  intro c' hmem
  rw [show (DNode.ty (TyP.letE E n Γ A u value B body w hA hv hb hT)).children =
      [.ty hA, .ty hv, .ty hb, .ty hT] from rfl] at hmem
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | h
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact h.elim

/-- `.cv` nodes are never `.ty` heads; children inherited. -/
theorem subAtNoWk_cv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : CvP E n Γ a b T) (hc : ∀ {c'}, c' ∈ (DNode.cv c).children → SubAtNoWk c') :
    SubAtNoWk (.cv c) :=
  .mk rfl hc

/-- forest check: every node reachable from `.cv srwkNode` is `.cv` or a
    non-`wk` `TyP`. The children lists are concrete; `rfl` computes them. -/
theorem srwkLeaf_nwk : SubAtNoWk (.ty lefixH0) := subAtNoWk_leafSort

theorem srwkS0T_nwk : SubAtNoWk (.ty srwkS0T) := subAtNoWk_leafSort

theorem srwkS1T_nwk : SubAtNoWk (.ty srwkS1T) := subAtNoWk_leafSort

theorem srwkS0Tb_nwk : SubAtNoWk (.ty srwkS0Tb) := subAtNoWk_leafSort

theorem srwkBvarT_nwk : SubAtNoWk (.ty srwkBvarT) := subAtNoWk_bvar srwkS0T_nwk

theorem srwkH0_nwk : SubAtNoWk (.cv srwkH0) :=
  subAtNoWk_cv srwkH0 (fun {c'} hmem => by
    have : (DNode.cv srwkH0).children = [.ty lefixH0, .ty lefixH0, .ty lefixH0] := rfl
    rw [this] at hmem
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil] at hmem
    rcases hmem with rfl | rfl | rfl | h
    · exact srwkLeaf_nwk
    · exact srwkLeaf_nwk
    · exact srwkLeaf_nwk
    · exact h.elim)

theorem srwkHa_nwk : SubAtNoWk (.cv srwkHa) :=
  subAtNoWk_cv srwkHa (fun {c'} hmem => by
    have : (DNode.cv srwkHa).children = [.cv srwkH0] := rfl
    rw [this] at hmem
    rcases List.mem_singleton.mp hmem with rfl
    exact srwkH0_nwk)

theorem srwkHv_nwk : SubAtNoWk (.cv srwkHv) :=
  subAtNoWk_cv srwkHv (fun {c'} hmem => by
    have : (DNode.cv srwkHv).children = [.ty srwkBvarT, .ty srwkBvarT, .ty srwkBvarT] := rfl
    rw [this] at hmem
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil] at hmem
    rcases hmem with rfl | rfl | rfl | h
    · exact srwkBvarT_nwk
    · exact srwkBvarT_nwk
    · exact srwkBvarT_nwk
    · exact h.elim)

theorem srwkHb_nwk : SubAtNoWk (.cv srwkHb) :=
  subAtNoWk_cv srwkHb (fun {c'} hmem => by
    have : (DNode.cv srwkHb).children = [.ty srwkS0Tb, .ty srwkS0Tb, .ty srwkS0Tb] := rfl
    rw [this] at hmem
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil] at hmem
    rcases hmem with rfl | rfl | rfl | h
    · exact srwkS0Tb_nwk
    · exact srwkS0Tb_nwk
    · exact srwkS0Tb_nwk
    · exact h.elim)

theorem srwkDl_nwk : SubAtNoWk (.ty srwkDl) :=
  subAtNoWk_letETy srwkS0T_nwk srwkBvarT_nwk srwkS0Tb_nwk srwkS1T_nwk

theorem srwkNode_nwk : SubAtNoWk (.cv srwkNode) :=
  subAtNoWk_cv srwkNode (fun {c'} hmem => by
    have : (DNode.cv srwkNode).children =
        [.cv srwkHa, .cv srwkHv, .cv srwkHb, .ty srwkDl, .ty srwkDl] := rfl
    rw [this] at hmem
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | h
    · exact srwkHa_nwk
    · exact srwkHv_nwk
    · exact srwkHb_nwk
    · exact srwkDl_nwk
    · exact srwkDl_nwk
    · exact h.elim)

/-- **Kernel countermodel**: at the real `let x : sort 0 := x; sort 0` node
    `srwkNode` (nonempty context `[x : sort 0]`, `hA` headed by `CvP.wk`),
    no path `p` reaches `.ty hA.dl` — `CvP.wk`'s forest children are
    `[.cv h]`, so the transported `TyP.wk` typing is not an occurrence.
    The `occA` port is therefore not derivable in general and stays inside
    the named wall `LetESortRowWalls`. -/
theorem not_letE_occA_wk {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) (p : List Nat) :
    P2Query.subAt (.es srwkNode S σ ρ) 0 p ≠ some (.ty srwkHa.dl) := by
  intro hsub
  have hdl : srwkHa.dl = TyP.wk emptyEnv 0 [] lefixS0 lefixS1 (.assumption lefixS0)
      0 lefixH0 := rfl
  change (DNode.cv srwkNode).subAt p = some (.ty srwkHa.dl) at hsub
  rw [hdl] at hsub
  have hwk := subAt_isTyWk_false srwkNode_nwk hsub
  exact absurd hwk (by decide)

#print axioms Rcic.Syn.es_letE_sortRow
#print axioms Rcic.Syn.not_letE_occA_wk
#print axioms Rcic.Syn.displayFits_of_routedDisp
