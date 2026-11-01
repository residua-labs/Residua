import rcic.RcicF3PropEvalValue
import rcic.RcicF3PropEvalCandidateStepAttack

/-!
# Actual bounded value and iota at the admitted AccR fixture

The new value obtains existence from the public candidate constructor step,
the independently proved AccR frame closure/monotonicity and leastness.
Its IH is the literal indexedIH over the stored normalized domain and full
argument list, using this same new value at every reached complete key.
The actual AccR child domain is empty at the selected parameter; a separate
inhabited depth-three fixture checks nonempty recursive application domains.

The actual typed minor consumes its field and generated IH, and its complete
application equals the new value. The old planned Prop endpoint remains
outside that same motive type for every old depth-only plan. This is AccR,
not an imported Acc-on-Nat.lt environment or universal StepAG.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEvalValueAttack
open Rcic.Declarative PiIndex PlanPropEndAttack
open PropEvalUniqueAttack (ctx)

noncomputable def result (P : Premises4) : PSet.{4} :=
  PropEvalValue.result (ctx P) (.param 0) (key [parameter])

/-- Existence is supplied by the newly produced closed candidate, not a prior
inhabited-evaluation fixture or an evaluation callback. -/
theorem result_spec (P : Premises4) :
    result P ∈ PropEval.childCarrier (ctx P) (.param 0) (key [parameter]) ∧
      PropEval.Eval (ctx P) (key [parameter]) (result P) :=
  PropEvalValue.result_spec (ctx P) (.param 0) (key [parameter])
    (PropEvalCandidateStepAttack.produced P)
    (fun _ he => PropEvalMotiveGuardAttack.guarded P he)
    (fun _ _ he he' => PropEvalAttack.functional P he he')

/-- Exercise the generic dependent-motive endpoint typing theorem. -/
theorem result_typed (P : Premises4) :
    result P ∈ Ed (ctx P).M (fapp (motive P (installed P)) pempty) := by
  exact PropEvalValue.result_mem_motive (ctx P) (.param 0) [] pempty rfl rfl
    (motive_mem P (installed P)) True.intro
    (major_mem P (installed P) (installed_family P)) Equiv.rfl (result_spec P).1

theorem result_domain (P : Premises4) : result P ∈ domain :=
  PropEvalAttack.eval_typed P (result_spec P).2

theorem result_nonempty (P : Premises4) : ¬ Equiv (result P) pempty := by
  intro he
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp (result_domain P)).symm.trans he)

/-- The literal retained telescope is used, not a depth-only marker. -/
noncomputable def ihValue (P : Premises4) : PSet.{4} :=
  (tel (ctx P).M (ctx P).σ [.bvar 2] [.bvar 3]
    (vcons pempty (start P (installed P)))).indexedIH (ctx P).M
      (fun i _ => PropEvalValue.result (ctx P) (.param 0) i) pempty

/-- This particular stored recursive field has no fitting argument tuple. -/
theorem no_children (P : Premises4) (zs : List PSet.{4}) :
    ¬ TelFits (ctx P).M (ctx P).σ [.bvar 2]
      (vcons pempty (start P (installed P))) zs := by
  intro hz
  cases zs with
  | nil => exact hz.elim
  | cons z zs =>
      have hz0 : z ∈ Ed (ctx P).M parameter := hz.1
      exact not_mem_pempty (mem_congr_right (parameter_empty P (installed P)) hz0)

/-- The indexed abstraction still consumes the real normalized domain. -/
theorem ih_empty (P : Premises4) : Equiv (ihValue P) pempty := by
  let M := (ctx P).M
  have he : Equiv (Ed M (tyv (Ed M parameter))) pempty :=
    (ed_tyv M (dich_ed M parameter)).trans (parameter_empty P (installed P))
  have hLam : ∀ F : PSet.{4} → PSet.{4},
      Equiv (lamVal M (tyv (Ed M parameter)) F) pempty := by
    intro F
    have hp : LamProof M (tyv (Ed M parameter)) F := by
      intro x hx
      exact (not_mem_pempty (mem_congr_right he hx)).elim
    unfold lamVal
    rw [cond_pos hp]
    exact Equiv.rfl
  change Equiv (lamVal M (tyv (Ed M parameter)) _) pempty
  exact hLam _

theorem ih_typed (P : Premises4) :
    ihValue P ∈ Ed (ctx P).M (den (ctx P).M (ctx P).σ
      (vcons pempty (start P (installed P))) accIhTy) :=
  mem_congr_left (ih_empty P).symm (ih_mem P (installed P))

noncomputable def generatedOut (P : Premises4) : PSet.{4} :=
  den (ctx P).M (ctx P).σ
    (vcons (ihValue P) (vcons pempty (start P (installed P))))
    (.app (.bvar 2) PropEvalAttack.tailAcc)

/-- The executable typed IH and its actual normalized scan compose with the
stored minor's input spine. No child-evaluation existence is assumed. -/
theorem generated_inputs (P : Premises4) :
    PropEval.Inputs (ctx P) 8 (.bvar 0) (.app (.const 1 []) (.bvar 1))
      [.recursive 1] (.pi accFieldMinor (accApp (.bvar 2)))
      (start P (installed P)) [pempty] [pempty, ihValue P] (generatedOut P) := by
  refine PropEval.Inputs.recursive 1 accIhTy ?_
    pempty (ihValue P) (field_mem P (installed P)) (ih_typed P)
    [.bvar 2] [.bvar 3] ?_ rfl rfl ?_ ?_
  · change funIHType accPrefix 8 1 accFieldMinor (.bvar 0) 1 = some accIhTy
    rfl
  · change piTelescopeFuel accPrefix 8 (Rcic.Declarative.lift 0 1 accFieldMinor) =
      some ([.bvar 2], foldApps (.const 0 []) [.bvar 3])
    rfl
  · intro zs hz
    exact (no_children P zs hz).elim
  · change PropEval.Inputs (ctx P) 8 (.bvar 2) PropEvalAttack.tailAcc []
      (accApp (.bvar 3)) (vcons (ihValue P) (vcons pempty (start P (installed P))))
      [] [] (generatedOut P)
    exact PropEval.Inputs.done 8 (.bvar 2) PropEvalAttack.tailAcc (accApp (.bvar 3))
      (vcons (ihValue P) (vcons pempty (start P (installed P))))

/-- Construct the root evaluation of the actual complete minor application. -/
theorem generated_eval (P : Premises4) :
    PropEval.Eval (ctx P) (key [parameter])
      (fapps (minor P (installed P)) [pempty, ihValue P]) := by
  refine PropEval.Eval.root ⟨0, by change 0 < 1; decide⟩ [parameter] [pempty]
    [pempty, ihValue P] 8 accMinorTy (generatedOut P)
    (fapps (minor P (installed P)) [pempty, ihValue P]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact PropEvalAttack.parameters_fit P (installed P)
  · exact ⟨Equiv.rfl, True.intro⟩
  · exact PropEvalAttack.original_field_fit P (installed P)
  · rfl
  · rfl
  · rfl
  · exact minor_mem P (installed P) (installed_family P) (installed_constructor P)
  · exact generated_inputs P
  · exact Equiv.rfl

/-- Iota consumes both the ordinary field and the generated indexed IH. -/
theorem iota (P : Premises4) :
    Equiv (result P) (fapps (minor P (installed P)) [pempty, ihValue P]) :=
  PropEvalValue.result_equiv (generated_eval P)
    (PropEvalMotiveGuardAttack.guarded P (generated_eval P))
    (fun _ _ he he' => PropEvalAttack.functional P he he')

/-- Retaining the parameter prefix does not license an extra index suffix. -/
theorem invalid_key (P : Premises4) :
    Equiv (PropEvalValue.result (ctx P) (.param 0) (key [parameter, datum])) pempty ∧
      PropEvalValue.result (ctx P) (.param 0) (key [parameter, datum]) ∉ domain := by
  have he := PropEvalValue.result_empty (ctx P) (.param 0) (key [parameter, datum])
    (fun z => (PropEvalAttack.suffix_rejected P z).2)
  refine ⟨he, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp h).symm.trans he)

/-- The literal pre-plan operation is still outside the same motive type. -/
theorem old_recEnd_not_mem (P : Premises4) :
    recEnd (ctx P).M (ctx P).σ fd (input P (installed P)) ∉
      Ed (ctx P).M (fapp (motive P (installed P)) pempty) := by
  have hn := endpoint_not_mem P (installed P) (installed_family P) (RecPlan.rawPlan fd)
  change RecPlanValue.endValue (ctx P).M (ctx P).σ fd (RecPlan.rawPlan fd)
    (input P (installed P)) ∉ Ed (ctx P).M (fapp (motive P (installed P)) pempty) at hn
  rw [(RecPlanValue.laws (ctx P).M (ctx P).σ fd []).2 (input P (installed P))] at hn
  exact hn

def Witness (P : Premises4) : Prop :=
  PropEvalCandidateStepAttack.Witness P ∧
  (ctx P).σ 0 = 1 ∧
  piTelescopeFuel accPrefix 8 (Rcic.Declarative.lift 0 1 accFieldMinor) =
    some ([.bvar 2], foldApps (.const 0 []) [.bvar 3]) ∧
  funIHType accPrefix 8 1 accFieldMinor (.bvar 0) 1 = some accIhTy ∧
  (∀ zs, ¬ TelFits (ctx P).M (ctx P).σ [.bvar 2]
    (vcons pempty (start P (installed P))) zs) ∧
  ihValue P ∈ Ed (ctx P).M (den (ctx P).M (ctx P).σ
    (vcons pempty (start P (installed P))) accIhTy) ∧
  PropEval.Eval (ctx P) (key [parameter]) (result P) ∧
  result P ∈ PropEval.childCarrier (ctx P) (.param 0) (key [parameter]) ∧
  result P ∈ Ed (ctx P).M (fapp (motive P (installed P)) pempty) ∧
  Equiv (result P) (fapps (minor P (installed P)) [pempty, ihValue P]) ∧
  ¬ Equiv (result P) pempty ∧
  recEnd (ctx P).M (ctx P).σ fd (input P (installed P)) ∉
    Ed (ctx P).M (fapp (motive P (installed P)) pempty) ∧
  (∀ plan : List (List FieldShape),
    RecPlanValue.endValue (ctx P).M (ctx P).σ fd plan (input P (installed P)) ∉
      Ed (ctx P).M (fapp (motive P (installed P)) pempty)) ∧
  ¬ PlanRole.StepAG RawFamily.role P (fun _ => 1)

/-- The complete new-value/iota statement coexists with the literal old refutation. -/
theorem component_witness (P : Premises4) : Witness P := by
  exact ⟨PropEvalCandidateStepAttack.component_witness P, rfl, rfl, rfl,
    no_children P, ih_typed P, (result_spec P).2, (result_spec P).1, result_typed P,
    iota P, result_nonempty P, old_recEnd_not_mem P,
    fun plan => endpoint_not_mem P (installed P) (installed_family P) plan,
    PlanPropStepAttack.stepAG_false P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalValueAttack
