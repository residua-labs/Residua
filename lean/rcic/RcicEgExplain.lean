import Lean

/-!
Same shapes as `apps/assay-egraph`. `by simp` is attempted on each goal.
A goal this file proves some other way is one `simp` did not close.
`eg_fwd` is that goal: its premise is a cited rule, and `simp` made no progress.
`closure_claim = 0`.
-/

namespace Rcic.Assay.Egraph

inductive T where
  | atom (i : Nat)
  | app (f : Nat) (a b : T)

theorem eg_refl (a : T) : a = a := by simp

/-- Forward use of a cited rule. `hcite` is the lookup `rules[i]? = some (a, b)`.
    `hsound` says a pair stored in `rules` is an equation. Neither hypothesis is `a = b`.
    `by simp` does not close this; the proof is the citation. -/
theorem eg_fwd (rules : List (T × T)) (i : Nat) (a b : T)
    (hcite : rules[i]? = some (a, b))
    (hsound : ∀ l r, (l, r) ∈ rules → l = r) : a = b :=
  hsound a b (List.getElem?_mem hcite)

theorem eg_flip (a b : T) (h : a = b) : b = a := by simp [h]

theorem eg_trans (a b c : T) (h1 : a = b) (h2 : b = c) : a = c := by simp [h1, h2]

theorem eg_order (a b c : T) (h1 : a = b) (h2 : b = c) : c = a := by simp [h1, h2]

theorem eg_cong (f : Nat) (a b z : T) (h : a = b) : T.app f a z = T.app f b z := by simp [h]

theorem eg_cong_trans (f : Nat) (a b c z : T) (h1 : a = b) (h2 : b = c) :
    T.app f a z = T.app f c z := by simp [h1, h2]

/-!
One `Kernel.check` per stored proof. Node count is a local `exprSize`.
This clock is not the scm step count. `eg_fwd` is not a `simp` proof.
-/

open Lean

private def exprSize : Expr → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .mvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ d b _ => 1 + exprSize d + exprSize b
  | .forallE _ d b _ => 1 + exprSize d + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .lit _ => 1
  | .mdata _ e => 1 + exprSize e
  | .proj _ _ e => 1 + exprSize e

private def simpGoals : List Name := [
  ``eg_refl, ``eg_fwd, ``eg_flip, ``eg_trans, ``eg_order, ``eg_cong, ``eg_cong_trans
]

open Elab.Command in
run_cmd do
  let env ← getEnv
  let mut nodes : Array Nat := #[]
  let mut times : Array Nat := #[]
  for n in simpGoals do
    let some ci := env.find? n | throwError "[assay_eg_cost] missing {n}"
    let some e := ci.value? | throwError "[assay_eg_cost] no value {n}"
    let t0 ← IO.monoNanosNow
    match Kernel.check env {} e with
    | .ok _ =>
      let t1 ← IO.monoNanosNow
      nodes := nodes.push (exprSize e)
      times := times.push (t1 - t0)
    | .error _ =>
      throwError "[assay_eg_cost] kernel check failed {n}"
  let line := s!"[assay_eg_cost] n=7 simp_nodes={nodes} simp_ns={times}"
  logInfo line
  IO.println line

end Rcic.Assay.Egraph
