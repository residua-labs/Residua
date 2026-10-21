import rcic.RcicSynContextView

/-!
# C5 layer 2 — `ViewPlan`: original nodes, displayed nodes, context ops, level maps, requests

`research/rcic/sortrow/S7_COMPLETE_WORKING_VIEWS.md` §1 (ChatGPT S7 #7330).
`closure_claim` stays 0.

`ViewPlan` is the second layer's computed record: the original nodes covered,
the displayed working nodes, the recorded context operations, the level maps
actually composed and the needed alignment requests. A `ViewPlan` holds **no**
pending ES/CL/EUT goal, kind equation or full-domain supplier: without source
readiness, what stays is a `pending` node for that original request — never a
deleted request or a modified input domain. A function that always returns a
`ViewPlan` completes structural enumeration, not C5.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- A needed alignment the plan computed but did not itself discharge. -/
inductive AlignRequest : Type where
  /-- a typing view that must be resolved into usable evidence -/
  | tyView {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} :
      TyView E n Γ e T → AlignRequest
  /-- a context-side source/working operation whose evidence is still owed -/
  | ctxOp : ContextView → AlignRequest
  /-- a level map whose endpoints still need a recorded correspondence -/
  | levelMap (θ : Level → Level) : AlignRequest

/-- The working-view plan over the ambient admitted environment `Eₐ`. -/
structure ViewPlan (Eₐ : ResolvedEnv) : Type where
  /-- the original nodes covered by the plan -/
  original : List RawForest
  /-- the displayed working nodes -/
  displayed : List (Σ' (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T : Expr Nat),
    TyView E n Γ e T)
  /-- the context operations recorded -/
  contextOps : List ContextView
  /-- the level maps actually composed -/
  levelMaps : List (Level → Level)
  /-- the needed alignment requests -/
  alignRequests : List AlignRequest
  /-- original requests kept as pending nodes — never deleted -/
  pending : List RawForest

/-- The empty plan over `Eₐ`: nothing computed, nothing pending. -/
def ViewPlan.empty (Eₐ : ResolvedEnv) : ViewPlan Eₐ where
  original := []
  displayed := []
  contextOps := []
  levelMaps := []
  alignRequests := []
  pending := []

/-- The plan of a single original node with no display operations: the node's
    identity view is displayed and no request is owed. -/
def ViewPlan.ofNode {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (Eₐ : ResolvedEnv) (nd : TyNode E n Γ e T) : ViewPlan Eₐ where
  original := [.ty nd]
  displayed := [⟨E, n, Γ, e, T, .atOriginal E n Γ e T nd⟩]
  contextOps := []
  levelMaps := []
  alignRequests := []
  pending := []

/-- Keep an unresolved original request: the node stays in `pending` (§1 —
    a pending node for that original request, never a deleted request). -/
def ViewPlan.keepPending {Eₐ : ResolvedEnv} (P : ViewPlan Eₐ) (nd : RawForest) :
    ViewPlan Eₐ :=
  { P with pending := nd :: P.pending }

end Rcic.Syn
