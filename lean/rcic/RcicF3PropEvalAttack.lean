import rcic.RcicF3PropEval
import rcic.RcicF3PiTypedExt
import rcic.RcicF3PlanPropStepAttack

/-!
# Indexed evaluation at the actual admitted AccR group

The canonical installed table pays family and constructor equations.
The actual stored minor consumes both its field and its typed IH. Empty
normalized domains discharge the child clause without an evaluation axiom.
This fixture is local; universal repaired StepAG remains open.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEvalAttack
open Rcic.Declarative PiIndex PlanPropEndAttack

noncomputable def context (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    PropEval.Context where
  E := emptyEnv
  E' := accEnv
  f := 0
  rr := 2
  rm := accRecMember
  node := PlanPropStepAttack.pNode
  M := mkM P μ
  σ := PlanPropEndAttack.σ
  parameters := [parameter]
  motive := motive P μ
  minors := [minor P μ]
  minor_length := rfl

def tailAcc : Expr Nat := .app (.app (.const 1 []) (.bvar 3)) (.bvar 1)

def endpoint (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : PSet.{4} :=
  den (mkM P μ) PlanPropEndAttack.σ
    (vcons pempty (vcons pempty (start P μ))) (.app (.bvar 2) tailAcc)

theorem parameters_fit (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    TelFits (mkM P μ) PlanPropEndAttack.σ [.sort .zero] ρ0 [parameter] := by
  exact ⟨mem_congr_right (ed_tyv (mkM P μ) (U4_dich 0)).symm (parameter_mem P), True.intro⟩

theorem original_field_fit (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    TelFits (mkM P μ) PlanPropEndAttack.σ [accField] (push [parameter] ρ0) [pempty] := by
  refine ⟨?_, True.intro⟩
  have h := field_mem P μ
  change pempty ∈ Ed (mkM P μ) (den (mkM P μ) PlanPropEndAttack.σ
    (vcons (motive P μ) (push [parameter] ρ0)) (Rcic.Declarative.lift 0 1 accField)) at h
  rw [den_lift01] at h
  exact h

theorem inputs (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    PropEval.Inputs (context P μ) 8 (.bvar 0) (.app (.const 1 []) (.bvar 1))
      [.recursive 1] (.pi accFieldMinor (accApp (.bvar 2))) (start P μ)
      [pempty] [pempty, pempty] (endpoint P μ) := by
  refine PropEval.Inputs.recursive 1 accIhTy ?_
    pempty pempty (field_mem P μ) (ih_mem P μ) [.bvar 2] [.bvar 3] ?_ rfl rfl ?_ ?_
  · change funIHType accPrefix 8 1 accFieldMinor (.bvar 0) 1 = some accIhTy
    rfl
  · change piTelescopeFuel accPrefix 8 (Rcic.Declarative.lift 0 1 accFieldMinor) =
      some ([.bvar 2], foldApps (.const 0 []) [.bvar 3])
    rfl
  · intro zs hz
    cases zs with
    | nil => exact hz.elim
    | cons z zs =>
        have hz0 : z ∈ Ed (mkM P μ) parameter := hz.1
        exact (not_mem_pempty (mem_congr_right (parameter_empty P μ) hz0)).elim
  · change PropEval.Inputs (context P μ) 8 (.bvar 2) tailAcc [] (accApp (.bvar 3))
      (vcons pempty (vcons pempty (start P μ))) [] [] (endpoint P μ)
    exact PropEval.Inputs.done 8 (.bvar 2) tailAcc (accApp (.bvar 3))
      (vcons pempty (vcons pempty (start P μ)))

theorem minor_result (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (fapps (minor P μ) [pempty, pempty]) datum :=
  (fapps_congr (first_application P μ) [pempty]).trans (second_application P μ)

/-- The actual node, stored minor, typed IH and normalized scan jointly inhabit Eval. -/
theorem inhabited (P : Premises4) :
    PropEval.Eval (context P (installed P)) (key [parameter]) datum := by
  let μ := installed P
  change PropEval.Eval (context P μ) (key [parameter]) datum
  refine PropEval.Eval.root ⟨0, by change 0 < 1; decide⟩ [parameter] [pempty] [pempty, pempty]
    8 accMinorTy (endpoint P μ) datum ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact parameters_fit P μ
  · exact ⟨Equiv.rfl, True.intro⟩
  · exact original_field_fit P μ
  · rfl
  · rfl
  · rfl
  · exact minor_mem P μ (installed_family P) (installed_constructor P)
  · exact inputs P μ
  · exact (minor_result P μ).symm

theorem inhabited_data (P : Premises4) :
    PropEval.Eval (context P (installed P)) (key [parameter]) datum ∧
      ¬ Equiv datum pempty :=
  ⟨inhabited P, dataVal_ne_pempty _ _⟩

/-- At this installed fixture, each evaluation lies in the actual singleton motive. -/
theorem eval_typed (P : Premises4) {i : Index.{4}} {z : PSet.{4}}
    (h : PropEval.Eval (context P (installed P)) i z) : z ∈ domain := by
  obtain ⟨⟨j, hj⟩, ps, xs, _, _, _, _, ht⟩ := h.result_typed
  have hj0 : j = 0 := by change j < 1 at hj; omega
  subst j
  let M := mkM P (installed P)
  change z ∈ Ed M (fapp (motive P (installed P))
    (fapps (installed P 1 []) (ps ++ xs))) at ht
  have hc := (fapps_congr (installed_constructor P) (ps ++ xs)).trans (fapps_pempty (ps ++ xs))
  have he := (fapp_congr (Equiv.refl (motive P (installed P))) hc).trans
    (motive_empty P (installed P) (installed_family P))
  exact mem_congr_right (ed_tyv M PiRawIHAnyAttack.domain_dich)
    (mem_congr_right (ed_congr M he) ht)

/-- Functionality is proved here from produced endpoint typing, not assumed. -/
theorem functional (P : Premises4) {i : Index.{4}} {z z' : PSet.{4}}
    (h : PropEval.Eval (context P (installed P)) i z)
    (h' : PropEval.Eval (context P (installed P)) i z') : Equiv z z' :=
  (mem_singleton.mp (eval_typed P h)).trans (mem_singleton.mp (eval_typed P h')).symm

noncomputable def canonical (P : Premises4) : PSet.{4} :=
  PropEvalExtract.value domain (PropEval.Eval (context P (installed P)) (key [parameter]))

/-- Existence, functionality, typing and output congruence compose at the actual node. -/
theorem canonical_spec (P : Premises4) :
    canonical P ∈ domain ∧
      PropEval.Eval (context P (installed P)) (key [parameter]) (canonical P) := by
  exact PropEvalExtract.value_spec_of_output_congr
    ⟨datum, mem_singleton.mpr Equiv.rfl, inhabited P⟩
    (fun _ _ _ _ hx hy => functional P hx hy)
    (fun _ _ hx => eval_typed P hx)
    (fun _ _ he hx => hx.output_congr he.symm)

theorem canonical_equiv (P : Premises4) : Equiv (canonical P) datum :=
  mem_singleton.mp (canonical_spec P).1

/-- A nonempty data result is produced by the repaired local evaluation component. -/
theorem component_witness (P : Premises4) :
    PropEval.Eval (context P (installed P)) (key [parameter]) (canonical P) ∧
      canonical P ∈ domain ∧ ¬ Equiv (canonical P) pempty := by
  refine ⟨(canonical_spec P).2, (canonical_spec P).1, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((canonical_equiv P).symm.trans h)

theorem component_nonrefutable (P : Premises4) :
    ¬ ((PropEval.Eval (context P (installed P)) (key [parameter]) (canonical P) ∧
        canonical P ∈ domain ∧ ¬ Equiv (canonical P) pempty) → (Premises4 → False)) :=
  fun h => h (component_witness P) P

/-- At this fixture the full result key is exactly the single parameter key. -/
theorem eval_key (P : Premises4) {i : Index.{4}} {z : PSet.{4}}
    (h : PropEval.Eval (context P (installed P)) i z) : i = key [parameter] := by
  obtain ⟨⟨j, hj⟩, ps, xs, hi, hp, _, _, _⟩ := h.result_typed
  have hj0 : j = 0 := by change j < 1 at hj; omega
  subst j
  change i = key (ps ++ []) at hi
  rw [List.append_nil] at hi
  exact hi.trans ((key_eq_iff _ _).mpr hp)

/-- Agreement of parameter prefixes does not permit a spurious index suffix. -/
theorem suffix_rejected (P : Premises4) (z : PSet.{4}) :
    RawFamilyRec.paramKey 1 (key [parameter, datum]) = key [parameter] ∧
      ¬ PropEval.Eval (context P (installed P)) (key [parameter, datum]) z := by
  refine ⟨rfl, ?_⟩
  intro h
  have hl := LEq.length ((key_eq_iff _ _).mp (eval_key P h))
  change 2 = 1 at hl
  omega

theorem missing_parameter_rejected (P : Premises4) (z : PSet.{4}) :
    ¬ PropEval.Eval (context P (installed P)) (key []) z := by
  intro h
  have hl := LEq.length ((key_eq_iff _ _).mp (eval_key P h))
  change 0 = 1 at hl
  omega

/-- The residual lambda from the old operation is not a result of this relation. -/
theorem residual_rejected (P : Premises4) (i : Index.{4}) :
    ¬ PropEval.Eval (context P (installed P)) i (inner P (installed P)) := by
  intro h
  exact inner_ne_datum P (installed P) (mem_singleton.mp (eval_typed P h))

/-- The literal planned Prop operation fails while the new local result is typed. -/
theorem repaired_vs_planned (P : Premises4) (plan : List (List FieldShape)) :
    canonical P ∈ Ed (mkM P (installed P)) (fapp (motive P (installed P)) pempty) ∧
    ¬ PropEval.Eval (context P (installed P)) (key [parameter])
      (RecPlanValue.endValue (mkM P (installed P)) PlanPropEndAttack.σ fd plan
        (input P (installed P))) := by
  refine ⟨?_, ?_⟩
  · exact mem_congr_right
      ((ed_congr (mkM P (installed P)) (motive_empty P (installed P) (installed_family P))).trans
        (ed_tyv (mkM P (installed P)) PiRawIHAnyAttack.domain_dich)).symm
      (canonical_spec P).1
  · intro h
    exact residual_rejected P _
      (h.output_congr (PlanPropEndAttack.endpoint P (installed P) plan).symm)

/-- A different proposition parameter cannot enter this fixed parameter slice. -/
theorem different_parameter_rejected (P : Premises4) (z : PSet.{4}) :
    ¬ PropEval.Eval (context P (installed P)) (key [tyv (tv True)]) z := by
  intro h
  have hp : Equiv (tyv (tv True)) parameter := ((key_eq_iff _ _).mp (eval_key P h)).1
  let M := mkM P (installed P)
  have ht : pempty ∈ Ed M (tyv (tv True)) :=
    mem_congr_right (ed_tyv M (dich_tv True)).symm (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  exact not_mem_pempty (mem_congr_right (parameter_empty P (installed P))
    (mem_congr_right (ed_congr M hp) ht))

/-- At a rejected complete key, extraction is empty and cannot inhabit the data motive. -/
theorem invalid_extraction (P : Premises4) :
    let bad := PropEvalExtract.value domain
      (PropEval.Eval (context P (installed P)) (key [parameter, datum]))
    Equiv bad pempty ∧ bad ∉ domain := by
  dsimp only
  have he := PropEvalExtract.value_empty (T := domain) (fun z => (suffix_rejected P z).2)
  refine ⟨he, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp h).symm.trans he)

/-- The actual empty-domain IH is unique even at the extra data-motive universe. -/
theorem empty_ih_unique (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {ih : PSet.{4}}
    (hih : ih ∈ Ed (mkM P μ) (den (mkM P μ) PlanPropEndAttack.σ
      (vcons pempty (start P μ)) accIhTy)) : Equiv ih pempty := by
  apply typed_tel_ext (mkM P μ) PlanPropEndAttack.σ [.bvar 2]
    (.app (.bvar 2) (.app (.bvar 1) (.bvar 0))) (vcons pempty (start P μ)) hih (ih_mem P μ)
  intro zs hz
  cases zs with
  | nil => exact hz.elim
  | cons z zs =>
    have hz0 : z ∈ Ed (mkM P μ) parameter := hz.1
    exact (not_mem_pempty (mem_congr_right (parameter_empty P μ) hz0)).elim

theorem empty_ih_comparison_witness (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    pempty ∈ Ed (mkM P μ) (den (mkM P μ) PlanPropEndAttack.σ
      (vcons pempty (start P μ)) accIhTy) ∧
    ∀ ih, ih ∈ Ed (mkM P μ) (den (mkM P μ) PlanPropEndAttack.σ
      (vcons pempty (start P μ)) accIhTy) → Equiv ih pempty :=
  ⟨ih_mem P μ, fun _ h => empty_ih_unique P μ h⟩

end Rcic.F3.PSet.PropEvalAttack
