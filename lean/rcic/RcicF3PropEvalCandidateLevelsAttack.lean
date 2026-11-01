import rcic.RcicF3PropEvalCandidateLevels
import rcic.RcicF3PropEvalCandidateParamsAttack

/-!
# The real AccR candidate keeps the recursor's extra motive universe

The family has arity zero, while the actual recursor valuation sends slot
zero to one. The candidate constructor is initially witnessed at the empty
family vector. Bounded-family transport produces its full parameter and
field slice at that different recursor valuation, with no equality of the
two valuations outside the family arity. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidateLevelsAttack
open Rcic.Declarative PiIndex RawFamily PlanPropEndAttack
open PropEvalUniqueAttack (ctx)
open PropEvalCandidateAttack (X)

theorem family_bounded : FamBounded fd 0 := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro e he
    change e ∈ [(.sort .zero : Expr Nat)] at he
    have heq := List.mem_singleton.mp he
    subst e
    rfl
  · intro e he
    change e ∈ ([] : List (Expr Nat)) at he
    exact (List.not_mem_nil _ he).elim
  · intro c hc
    change c ∈ [([accField], ([] : List (Expr Nat)))] at hc
    have heq := List.mem_singleton.mp hc
    subst c
    constructor
    · intro e he
      have heq : e = accField := List.mem_singleton.mp he
      subst e
      rfl
    · intro e he
      exact (List.not_mem_nil _ he).elim

def Witness (P : Premises4) : Prop :=
  PropEvalCandidateParamsAttack.Witness P ∧
  (ctx P).σ 0 = 1 ∧ σOf [] 0 = 0 ∧
  (let M := mkM P (table P (installed P) fd (X P))
   ∃ (j : Fin fd.ctors.length) (xs : List PSet.{4}),
    TelFits M (ctx P).σ fd.params ρ0 [parameter] ∧
    TelFits M (ctx P).σ (fd.ctors.get j).1 (push [parameter] ρ0) xs ∧
    key [parameter] = key ([parameter] ++ (fd.ctors.get j).2.map
      (den M (ctx P).σ (push xs (push [parameter] ρ0)))) ∧
    Equiv (pempty : PSet.{4}) pempty)

theorem component_witness (P : Premises4) : Witness P := by
  refine ⟨PropEvalCandidateParamsAttack.component_witness P, rfl, rfl, ?_⟩
  exact PropEvalCandidate.ctorAt_parameters_at P (installed P) fd (X P)
    0 family_bounded [] (ctx P).σ (fun u hu => (Nat.not_lt_zero u hu).elim)
    (key [parameter]) pempty (PropEvalCandidateParamsAttack.constructor P)
    [parameter] rfl rfl

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalCandidateLevelsAttack
