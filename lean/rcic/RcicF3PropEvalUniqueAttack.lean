import rcic.RcicF3PropEvalUnique
import rcic.RcicF3PropEvalAttack

/-!
# Actual AccR extraction using the generic mutual comparison

The fixed parameter slice supplies proof-field comparison, the actual
constructor census is a singleton, and the admitted AccR evaluation supplies
existence. The extractor now consumes the generic mutual uniqueness proof.
This local fixture does not supply universal evaluation existence or the
general constructor/field-typing adapter. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalUniqueAttack
open Rcic.Declarative PiIndex PlanPropEndAttack

noncomputable def ctx (P : Premises4) : PropEval.Context :=
  PropEvalAttack.context P (installed P)

/-- At the selected parameter slice the actual recursive field has an empty domain. -/
theorem fixed_proof_fields (P : Premises4)
    (j : Fin (ctx P).node.a.constructors.length) (ps : List PSet.{4})
    (_ : TelFits (ctx P).M (ctx P).σ (ctx P).node.a.family.parameters ρ0 ps)
    (hp : LEq ps (ctx P).parameters) :
    PropTel (ctx P).M (ctx P).σ ((ctx P).node.a.constructorViews j).fields (push ps ρ0) := by
  rcases j with ⟨j, hj⟩
  have hj0 : j = 0 := by change j < 1 at hj; omega
  subst j
  cases ps with
  | nil => exact False.elim hp
  | cons a ps =>
      cases ps with
      | cons b ps => exact False.elim hp.2
      | nil =>
          let M := (ctx P).M
          have ha : Equiv a parameter := hp.1
          have he : Equiv (Ed M a) pempty :=
            (ed_congr M ha).trans (parameter_empty P (installed P))
          have hPi : PiProp M a (fun _ => fapp (M.μ 0 []) a) := by
            intro x hx
            exact (not_mem_pempty (mem_congr_right he hx)).elim
          change PropTel M PlanPropEndAttack.σ [accField] (push [a] ρ0)
          refine ⟨?_, fun _ => True.intro⟩
          intro y hy
          change y ∈ Ed M (piVal M a (fun _ => fapp (M.μ 0 []) a)) at hy
          exact (mem_tv.mp (mem_congr_right (ed_piVal_of_prop M hPi) hy)).2

/-- Literal premises and consequences of the mutual-comparison extraction component. -/
def Witness (P : Premises4) : Prop :=
  (ctx P).node.a.constructors.length ≤ 1 ∧
  (∀ (j : Fin (ctx P).node.a.constructors.length) ps,
    TelFits (ctx P).M (ctx P).σ (ctx P).node.a.family.parameters ρ0 ps →
    LEq ps (ctx P).parameters →
    PropTel (ctx P).M (ctx P).σ ((ctx P).node.a.constructorViews j).fields (push ps ρ0)) ∧
  PropEval.Eval (ctx P) (key [parameter]) datum ∧
  (∀ i z z', PropEval.Eval (ctx P) i z → PropEval.Eval (ctx P) i z' → Equiv z z') ∧
  PropEvalAttack.canonical P ∈ domain ∧
  PropEval.Eval (ctx P) (key [parameter]) (PropEvalAttack.canonical P) ∧
  ¬ Equiv (PropEvalAttack.canonical P) pempty

theorem component_witness (P : Premises4) : Witness P := by
  have hone : (ctx P).node.a.constructors.length ≤ 1 := by change 1 ≤ 1; decide
  have hfun : ∀ i z z', PropEval.Eval (ctx P) i z →
      PropEval.Eval (ctx P) i z' → Equiv z z' :=
    fun _ _ _ h h' => h.functional_of_proof_fields (ctx P) hone (fixed_proof_fields P) h'
  have hex : ∃ z, z ∈ domain ∧ PropEval.Eval (ctx P) (key [parameter]) z :=
    ⟨datum, mem_singleton.mpr Equiv.rfl, PropEvalAttack.inhabited P⟩
  have hv : PropEvalAttack.canonical P ∈ domain ∧
      PropEval.Eval (ctx P) (key [parameter]) (PropEvalAttack.canonical P) :=
    PropEvalExtract.value_spec_of_output_congr hex
      (fun _ _ _ _ h h' => hfun _ _ _ h h')
      (fun _ _ h => PropEvalAttack.eval_typed P h)
      (fun _ _ he h => h.output_congr he.symm)
  refine ⟨hone, fixed_proof_fields P, PropEvalAttack.inhabited P, hfun, hv.1, hv.2, ?_⟩
  intro h
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp hv.1).symm.trans h)

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalUniqueAttack
