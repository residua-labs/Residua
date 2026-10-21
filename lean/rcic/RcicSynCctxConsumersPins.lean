import rcic.RcicSynCctxConsumers

/-!
# S6 §4.2 positive control — the `cctx` consumers on a minimal sort fixture

J, D and `c`'s three endpoint typings are all direct `TyP.sort` nodes, so
`c.wt = 4` and `at(c) = [4]`; the gate edge runs `[1,1,4] → [1,1]` (the
`tyPairMeas J c.dr` pair sits below `at(J) ++ at(D) ++ at(c)`) and the body edge
runs `[1,1,4] → [1,1,1]` (`K ++ at(c.dl)` below `K ++ at(c)` with
`K = at(J) ++ at(D)`). Both edges are the generic consumer lemmas instantiated
at these fixtures; nothing is recomputed by hand. `closure_claim = 0`.
-/

namespace Rcic.Syn.CctxConsumersPins

open Rcic.Declarative

/-- `c`: `sort 0 ≡ sort 0 : sort 1` by `refl` over three `sort`-typings — wt 4. -/
def pinC : CvP emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .refl _ _ _ _ _ pinSortP pinSortP pinSortP

/-- `J`: the target binder typing `sort 0 : sort 1`. -/
def pinJ : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) := pinSortP

/-- `D`: `sort 0 : sort 1` under the source binder `x : sort 0`. -/
def pinD : TyP emptyEnv 0 [.assumption (.sort .zero)] (.sort .zero) (.sort (.succ .zero)) :=
  .sort _ _ _ _ _ (eqN_refl _)

theorem pinC_wt : (pinC.wt fun _ => 0) = 4 := rfl

theorem pinC_atoms : pinC.atoms (fun _ => 0) = [4] := rfl

/-- Gate: caller `[1,1,4]` (`at(J) ++ at(D) ++ at(c)`), callee `[1,1]`
    (`at(J) ++ at(c.dr)`). -/
theorem pin_gate_edge :
    DMStep (pinJ.atoms (fun _ => 0) ++ pinC.dr.atoms (fun _ => 0))
      ([] ++ pinJ.atoms (fun _ => 0) ++ pinD.atoms (fun _ => 0) ++
        pinC.atoms (fun _ => 0)) :=
  dmStep_cctx_gate (fun _ => 0) [] pinJ pinD pinC

theorem pin_gate_atoms :
    (pinJ.atoms (fun _ => 0) ++ pinC.dr.atoms (fun _ => 0)) = [1, 1] ∧
      (pinJ.atoms (fun _ => 0) ++ pinD.atoms (fun _ => 0) ++ pinC.atoms (fun _ => 0))
        = [1, 1, 4] :=
  ⟨rfl, rfl⟩

/-- Body: caller `[1,1,4]` (`K ++ at(c)` with `K = at(J) ++ at(D) = [1,1]`),
    callee `[1,1,1]` (`K ++ at(c.dl)`). -/
theorem pin_body_edge :
    DMStep ([1, 1] ++ pinC.dl.atoms (fun _ => 0)) ([1, 1] ++ pinC.atoms (fun _ => 0)) :=
  dmStep_cctx_body (fun _ => 0) [1, 1] pinC

theorem pin_body_atoms :
    ([1, 1] ++ pinC.dl.atoms (fun _ => 0)) = [1, 1, 1] ∧
      ([1, 1] ++ pinC.atoms (fun _ => 0)) = [1, 1, 4] :=
  ⟨rfl, rfl⟩

/-- The source context `Cs = .assumption .nil c.dl` — `x : sort 0` formed by
    `c`'s left endpoint. -/
def pinCs : CtxP emptyEnv 0 [.assumption (.sort .zero)] :=
  cctxSourceCtx (.nil _ _) pinC

/-- The aligned source disposition at `σ = id`, `ρ = []`: the target binder bit
    `levelIsZero (id (.succ .zero)) = false` gives `binderDisp false = .keep`. -/
theorem pin_source_disp :
    DispFor id emptyEnv 0 [.assumption (.sort .zero)]
      (binderDisp (levelIsZero (id (.succ .zero))) :: []) :=
  dispFor_cctx_source (.nil levelSub_id) pinC rfl

end Rcic.Syn.CctxConsumersPins
