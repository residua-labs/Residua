import rcic.RcicSynSRClEutEswW
import rcic.RcicSynCensusCorePortRefutations

/-!
# RcicSynSRClEutEswEut — row 15 (`eut_case`) under `epsW`: the lamP wall

cc 2026-10-20 20:00Z brief, lane glm-sr3. #7800 refutes the gated lamP
supply on-cone at `σ := id` (a `LevelHom`) with `eps`. Question: does the
same fixture refute the epsW version? Answer, kernel-checked: YES —
`EutLamPortsW` (convB at `epsW`) is FALSE at the same closed fixtures
`hs0s`/`hs1s`. The wall is NOT an erasure artifact: both fixture
derivations are `.sort` leaves, whose `epsW` arm is verbatim `eps`
(`hs0s_epsW_eq_eps`/`hs1s_epsW_eq_eps` are `rfl`), so the refuting
conversion is the SAME computation under both erasures. `closure_claim = 0`.

The real obstruction (per the brief's follow-up): the port reduces to
`convB` alone (`eutLamPortsW_iff` — `hTC` is supplied by `tableWF`), and
`convB` is the codomain-typing conversion at the binder display — the
binder-crossed position `occ_eut` cannot issue (not `subAt`-positioned;
`RcicSynStepCore4.lean:51` records the gap class). The landed field's
lam-lam cell has exactly one route (`lamP _ _`,
`RcicSynStepPortsClEut.lean:351`); no different supply route exists below
the field. The surviving wall is the common-body shape, gated, restated at
epsW (`eut_case_wallW`), satisfiable at identical instances.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins

variable {E : ResolvedEnv}

/-- `EutLamPorts` restated at the display-aware erasure: `convB` computes
    both codomain typings with `epsW` at the binder display. -/
structure EutLamPortsW (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B₁ B₂ : Expr Nat}
    (u₁ : Level) {v₁ v₂ : Level}
    (hB₁ : TyP E n (.assumption A :: Γ) B₁ (.sort v₁))
    (hB₂ : TyP E n (.assumption A :: Γ) B₂ (.sort v₂)) : Prop where
  hTC : TableClosed tbl
  convB : ConvMod (EStep tbl) LvlEq
    (hB₁.epsW σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
    (hB₂.epsW σ (binderDisp (levelIsZero (σ u₁)) :: ρ))

/-- The fixture computations are IDENTICAL under both erasures: `.sort`
    leaves carry no display sensitivity (`rfl`, no transfer needed). -/
theorem hs0s_epsW_eq_eps (ρ' : List Disp) :
    (hs0s : TyP emptyEnv 0 [.assumption s1] s0 (.sort one)).epsW id ρ' =
      hs0s.eps id ρ' := rfl

theorem hs1s_epsW_eq_eps (ρ' : List Disp) :
    (hs1s : TyP emptyEnv 0 [.assumption s1] s1 (.sort two)).epsW id ρ' =
      hs1s.eps id ρ' := rfl

/-- **Row 15 gated verdict under epsW: the gated `lamP` supply is FALSE**
    at every `TableWF` table — the refuting σ is `id`, a `LevelHom`; every
    input a closed inhabited term; the refuting conversion is
    `ConvMod (.sort 0) (.sort 1)`, exactly as under `eps`. -/
theorem eutLamPortsW_sort_zero_one_refuted {tbl : List CRule}
    (hW : TableWF tbl) :
    ¬ EutLamPortsW tbl id [] two hs0s hs1s := by
  rintro ⟨_, hsort : ConvMod (EStep tbl) LvlEq (.sort .zero) (.sort (.succ .zero))⟩
  exact Rcic.Syn.not_eqN_zero_succ .zero (eqN_of_convE_sort_wf hW hsort)

/-- At `tableOf` the epsW refutation stands on the same closed instance
    as the landed `eps` one (`eutLamPorts_tableOf_empty_refuted`). -/
theorem eutLamPortsW_tableOf_empty_refuted :
    ¬ EutLamPortsW (tableOf EnvWfT.empty) id [] two hs0s hs1s :=
  eutLamPortsW_sort_zero_one_refuted (tableWF_build EnvWfT.empty)

/-- At the row's own table `tableOfI hW` the same fixture refutes the
    epsW supply — NOT a strawman, and NOT an erasure artifact. -/
theorem eutLamPortsW_tableOfI_empty_refuted :
    ¬ EutLamPortsW (tableOfI EnvWfT.empty) id [] two hs0s hs1s :=
  eutLamPortsW_sort_zero_one_refuted (tableWF_tableOfI_full EnvWfT.empty)

/-- The obstruction is `convB` alone: at a well-formed `tableOfI` the
    port is the conversion, nothing more (`hTC` is the table's closure). -/
theorem eutLamPortsW_iff (hW : EnvWfT E)
    {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B₁ B₂ : Expr Nat}
    {u₁ : Level} {v₁ v₂ : Level}
    (hB₁ : TyP E' n (.assumption A :: Γ) B₁ (.sort v₁))
    (hB₂ : TyP E' n (.assumption A :: Γ) B₂ (.sort v₂))
    {σ : Level → Level} {ρ : List Disp} :
    EutLamPortsW (tableOfI hW) σ ρ u₁ hB₁ hB₂ ↔
      ConvMod (EStep (tableOfI hW)) LvlEq
        (hB₁.epsW σ (binderDisp (levelIsZero (σ u₁)) :: ρ))
        (hB₂.epsW σ (binderDisp (levelIsZero (σ u₁)) :: ρ)) :=
  ⟨fun p => p.convB, fun h => ⟨(tableWF_tableOfI_full hW).closed, h⟩⟩

/-- Row 15's surviving wall under epsW, ONE named Prop: the `.eut` lam-lam
    cell's common-body shape at `tableOfI hW`, gated at the `LevelHom σ`
    every demanded `.eut` cell carries. This is #7800's gated restatement
    of `eut_case_wall` with `convB` at `epsW`. -/
def eut_case_wallW (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body B₁ B₂ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E' n Γ A (.sort u₁))
    (hb₁ : TyP E' n (.assumption A :: Γ) body B₁)
    (hB₁ : TyP E' n (.assumption A :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E' n Γ A (.sort u₂))
    (hb₂ : TyP E' n (.assumption A :: Γ) body B₂)
    (hB₂ : TyP E' n (.assumption A :: Γ) B₂ (.sort v₂))
    {σ : Level → Level} {ρ : List Disp}, LevelHom σ →
    EutLamPortsW (tableOfI hW) σ ρ u₁ hB₁ hB₂

/-- The restated W-wall is not vacuously false: at an identical cell
    instance its conclusion is inhabited — `hTC` from `tableWF_tableOfI_full`,
    `convB` reflexive (the epsW computation is deterministic in the
    derivation, so identical typings erase identically). -/
theorem eut_case_wallW_ident_sat (hW : EnvWfT E) {E' : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A body B₁ : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : TyP E' n Γ A (.sort u₁))
    (hb : TyP E' n (.assumption A :: Γ) body B₁)
    (hB : TyP E' n (.assumption A :: Γ) B₁ (.sort v₁))
    {σ : Level → Level} {ρ : List Disp} :
    EutLamPortsW (tableOfI hW) σ ρ u₁ hB hB :=
  ⟨(tableWF_tableOfI_full hW).closed, ConvMod.refl _⟩

#print axioms EutLamPortsW
#print axioms hs0s_epsW_eq_eps
#print axioms hs1s_epsW_eq_eps
#print axioms eutLamPortsW_sort_zero_one_refuted
#print axioms eutLamPortsW_tableOf_empty_refuted
#print axioms eutLamPortsW_tableOfI_empty_refuted
#print axioms eutLamPortsW_iff
#print axioms eut_case_wallW
#print axioms eut_case_wallW_ident_sat

end Rcic.Syn
