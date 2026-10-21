import rcic.RcicAnnAnnotateG
import rcic.RcicAnnIotaSRPins

/-!
# DT-025 / A-6 E2 — the payoff pin: `hstuck` at a recursor redex, with no semantic hypothesis

At the Nat environment `pinNatBuiltEnvA` (`annEnvA_pinNat`: a real `EnvWfA` environment, with the
recursor `13`), both semantic environments are discharged from `AnnEnvA` alone — main's by
`AnnEnvA.hS`, the guarded one by `AnnEnvA.hSg` (E2). So `chain_of_fund_stuckg_wf` holds there with
no semantic hypothesis left. Read at the ι redex `rec [.param 0] P mz ms (succ zero) : P (succ zero)`
(`RcicAnnIotaSRPins`: `lhs₀`, typed by `hlhs`, in `Γ₀ = ctxMs []`), whose type is stuck (a
variable-headed motive application) and not a proposition (its sort is `Sort (param 0)`): the
theorem hands the redex a head chain to a normal form, and that normal form is the predicted
`ms zero (rec [.param 0] P mz ms zero)` (`rhs₀`) — read back through determinism, and checked a
second time by evaluating `whnfA` itself (`decide`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- **the guarded semantic environment at Nat**, from `AnnEnvA` alone. -/
theorem pinNat_envSemAg (n : Nat) :
    EnvSemAg pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n (fun _ => 1) :=
  annEnvA_pinNat.hSg n

/-- `P (succ zero)` is stuck: the motive is a variable. -/
theorem pinNat_T0_stuck : StuckA pinNatBuiltEnvA pinSRIface Γ₀ T₀ :=
  ⟨by decide, by simp [T₀, appsSpineA, isShapeHeadA]⟩

/-- `P (succ zero) : Sort (param 0)` is not a proposition for the key. -/
theorem pinNat_T0_notProp : ¬ IsPropTy pinNatBuiltEnvA pinSRIface Γ₀ T₀ :=
  not_isPropTy_of_inferSortA (fuel := 3) (l := .param 0) (by decide) rfl

/-- the second instrument: `whnfA` computes the ι reduct, and stops there. -/
theorem pinNat_whnf : whnfA pinNatBuiltEnvA pinSRIface.fn Γ₀ 1 lhs₀ = some rhs₀ := by decide

/-- **THE PAYOFF PIN**: at the real `EnvWfA` environment with a recursor, with no semantic
    hypothesis, the recursor redex `rec P mz ms (succ zero)` gets a head chain from
    `chain_of_fund_stuckg_wf`, and its normal form is `ms zero (rec P mz ms zero)`. -/
theorem pin_chain_of_fund_stuckg_nat (n : Nat) (hn : 0 < n) :
    ∃ Ne, TyHRedStarA pinNatBuiltEnvA pinSRIface n Γ₀ lhs₀ Ne T₀ ∧
      hStepFnA pinNatBuiltEnvA pinSRIface.fn Γ₀ Ne = none ∧ Ne = rhs₀ := by
  have C := annEnvA_pinNat
  obtain ⟨hW⟩ := C.wf
  obtain ⟨Ne, ch, hNe⟩ := chain_of_fund_stuckg_wf hW C.hE C.hI C.hIS C.hR (C.hS n) (C.hSg n)
    posValA_one (hΓ₀ n) (hlhs n hn) (whTyA_of_hasTy (pinSR_T0Ty n)) pinNat_T0_stuck pinNat_T0_notProp
  refine ⟨Ne, ch, hNe, ?_⟩
  obtain ⟨c⟩ := ch
  exact RedTo_det (tmChainA_redTo c hNe) ⟨1, pinNat_whnf⟩

#print axioms pinNat_envSemAg
#print axioms pinNat_T0_stuck
#print axioms pinNat_T0_notProp
#print axioms pinNat_whnf
#print axioms pin_chain_of_fund_stuckg_nat

end Rcic.Declarative.Ann
