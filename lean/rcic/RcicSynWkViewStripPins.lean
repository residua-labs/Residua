import rcic.RcicSynWkViewStrip

/-!
# S6 §5 positive control — the `wk` view-strip adapter on a sort fixture

`D` is the direct `sort 0 : sort 1` typing in the empty context (`wt = 1`,
`at(D) = [1]`), and `H = wk D` inserts `x : sort 0` at cutoff `0`, so
`at(H) = [1]` and `H.wt = 2`. The adapter's edge runs `(K ++ [1], 1) → (K ++ [1], 2)`
with `K = [3]` kept in order — the lex's right branch. On the view side, `ρ = [.keep]`
lifts the source erasure at the original cutoff (`countKeep (take 0 ρ) = 0`) and
`ρ = [.drop]` keeps it; both compute to `★` by the kernel. All numbers are
kernel-checked by `rfl`; nothing is recomputed by hand. `closure_claim = 0`.
-/

namespace Rcic.Syn.WkViewStripPins

open Rcic.Declarative

/-- `D`: `sort 0 : sort 1` in the empty context — `wt = 1`, `at(D) = [1]`. -/
def pinD : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) := pinSortP

/-- `H`: `wk pinD` inserting `x : sort 0` at cutoff `0` — `wt = 2`, `at(H) = [1]`. -/
def pinH : TyP emptyEnv 0 (insertAt (.assumption (.sort .zero)) 0 [])
    (lift 0 1 (.sort .zero)) (lift 0 1 (.sort (.succ .zero))) :=
  .wk _ _ _ _ _ (.assumption (.sort .zero)) 0 pinD

theorem pinD_atoms : pinD.atoms (fun _ => 0) = [1] := rfl

theorem pinD_wt : pinD.wt (fun _ => 0) = 1 := rfl

theorem pinH_atoms : pinH.atoms (fun _ => 0) = [1] := rfl

theorem pinH_wt : pinH.wt (fun _ => 0) = 2 := rfl

/-- The measure edge with `K = [3]` kept in order: `([3,1], 1) → ([3,1], 2)`. -/
theorem pin_edge :
    LexDM ([3] ++ pinD.atoms (fun _ => 0), pinD.wt (fun _ => 0))
      ([3] ++ pinH.atoms (fun _ => 0), pinH.wt (fun _ => 0)) :=
  lexDM_wk_view_strip_tbl (fun _ => 0) pinD [3]

/-- The adapter at `σ = id`, `ρ = [.keep]`, `K = [3]` — `keep` at the inserted
    slot: the source erasure is lifted at the original cutoff
    (`countKeep (take 0 [.keep]) = 0`). -/
theorem pin_keep :
    pinH.eps id [.keep] = (pinD.eps id []).lift (countKeep (List.take 0 [.keep])) 1 :=
  (wkViewStrip (fun _ => 0) (d := .assumption (.sort .zero)) (c := 0)
    (σ := id) (ρ := [.keep]) pinD [3]).eps_keep rfl

/-- The adapter at `ρ = [.drop]` — the source erasure is kept. -/
theorem pin_drop : pinH.eps id [.drop] = pinD.eps id [] :=
  (wkViewStrip (fun _ => 0) (d := .assumption (.sort .zero)) (c := 0)
    (σ := id) (ρ := [.drop]) pinD [3]).eps_not_keep (by simp)

/-- Both view branches evaluate to `sort 0` — kernel-checked, no fixture adjusted. -/
theorem pin_eps_vals :
    pinH.eps id [.keep] = ETm.sort .zero ∧ pinH.eps id [.drop] = ETm.sort .zero :=
  ⟨rfl, rfl⟩

#print axioms Rcic.Syn.WkViewStripPins.pin_edge
#print axioms Rcic.Syn.WkViewStripPins.pin_keep
#print axioms Rcic.Syn.WkViewStripPins.pin_eps_vals

end Rcic.Syn.WkViewStripPins
