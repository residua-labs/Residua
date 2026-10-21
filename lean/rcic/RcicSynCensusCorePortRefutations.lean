import rcic.RcicSynStepPortsClEut
import rcic.RcicSynDispForPathPins
import rcic.RcicSynTableWF
import rcic.RcicSynSharedRank
import rcic.RcicSynPiLamRight

/-!
# False raw core-port contracts

These are counterexamples to the ungated port-function contracts, not
implementations of `cl_case`, `eut_case`, or `pb_case`.

The landed `no_typeAdm_zero` makes `TypeAdm` at the zero weight function
empty.  Its port-level consequence does not refute admission at the actual
canonical weights of a resolved member.

For a native well-formed environment with an actual resolved member,
`AgreeOn` cannot identify those canonical weights with the zero function:
the existing admission transport would then produce zero-weight admission.

The global `lamP` argument of `es_eut_field` receives two arbitrary
codomain sort typings, without common-body lambda typings or `Demand`.
The original landed `hs0s` and `hs1s` are valid inputs to that raw port,
but its requested codomain conversion would equate erased sorts zero and
one.  This does not refute a demanded lambda CaseStep, whose original
common-body typings impose additional conditions.

`closure_claim = 0`.
-/

namespace Rcic.Syn.CensusCorePortRefutations

open Rcic.Declarative
open DispForPathPins

theorem typeAdm_zero_empty {E : ResolvedEnv} {r : Nat} {m : CheckedMember} :
    ¬ Nonempty (TypeAdm E (fun _ => 0) r m) := by
  rintro ⟨adm⟩
  exact Rcic.Syn.no_typeAdm_zero adm

theorem eutConstPorts_zero_empty (tbl : List CRule) (σ : Level → Level)
    (ρ : List Disp) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (r : Nat)
    {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂)) :
    ¬ Nonempty (EutConstPorts (fun _ => 0) tbl σ ρ r hT₁ hT₂) := by
  rintro ⟨ports⟩
  exact typeAdm_zero_empty ⟨ports.adm⟩

theorem agreeOn_zero_admW_refuted {E : ResolvedEnv} (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} (hres : E.members r = some m) :
    ¬ AgreeOn E (fun _ => 0) (enrichEnvWfT hW).admW := by
  intro hag
  exact Rcic.Syn.no_typeAdm_zero
    (((enrichEnvWfT hW).typeAdm hres).lift' (envExt_refl E) hag (hag r m hres))

theorem eutLamPorts_sort_zero_one_refuted {tbl : List CRule}
    (hW : TableWF tbl) :
    ¬ EutLamPorts tbl id [] two hs0s hs1s := by
  intro ports
  have hsort : ConvMod (EStep tbl) LvlEq (.sort .zero) (.sort (.succ .zero)) :=
    ports.convB
  exact Rcic.Syn.not_eqN_zero_succ .zero (eqN_of_convE_sort_wf hW hsort)

theorem eutLamPorts_tableOf_empty_refuted :
    ¬ EutLamPorts (tableOf EnvWfT.empty) id [] two hs0s hs1s :=
  eutLamPorts_sort_zero_one_refuted (tableWF_build EnvWfT.empty)

#print axioms typeAdm_zero_empty
#print axioms eutConstPorts_zero_empty
#print axioms agreeOn_zero_admW_refuted
#print axioms eutLamPorts_sort_zero_one_refuted
#print axioms eutLamPorts_tableOf_empty_refuted

end Rcic.Syn.CensusCorePortRefutations
