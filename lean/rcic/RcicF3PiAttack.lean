import rcic.RcicF3PiAcc
import rcic.RcicF3PiW

/-!
# Adversarial semantic fixtures for dependent Pi signatures

These tests exercise semantic telescopes, including three dependent
binders, a dependent result, beta/delta/zeta-hidden presentations and
arbitrary numerical relabelling. They do not test extraction from raw
R-CIC syntax or prove the typed group step. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PiAttack

/-- Later argument types depend on earlier arguments at two levels. -/
def nested : PiTel.{0} 3 :=
  .cons Nat (fun n => .cons (Fin (n + 1))
    (fun i => .cons (Fin (i.val + 1)) (fun _ => .nil)))

/-- The result type depends on the second argument. -/
def Result (p : nested.Path) : Type := Fin (p.2.1.val + 1)

/-- An actual inhabitant, with no premise about the telescope. -/
def value : nested.Value Result := fun _ _ j => j

/-- A deliberately hidden presentation of the entire telescope. -/
def hidden : PiTel.{0} 3 :=
  (fun t : PiTel.{0} 3 => let q := t; q) nested

-- Computation pins: all are deliberately trivial definitional checks.
theorem hidden_eq : hidden = nested := rfl

theorem dependent_evaluation (n : Nat) (i : Fin (n + 1))
    (j : Fin (i.val + 1)) : nested.flatten value ⟨n, ⟨i, ⟨j, .unit⟩⟩⟩ = j := rfl

theorem nested_roundtrip : nested.unflatten (nested.flatten value) = value := by
  exact PiTel.unflatten_flatten nested value

theorem dependent_relation :
    nested.All (fun p z => z = p.2.2.1) value := by
  exact (PiTel.all_iff nested _ value).mpr (fun _ => rfl)

theorem hidden_relation :
    hidden.All (fun p z => z = p.2.2.1) value := by
  exact dependent_relation

/-- Relabelling by any offset does not remove accessible points. -/
def renamedLt (offset : Nat) (a b : Nat) : Prop := a + offset < b + offset

theorem renamed_inhabited (offset x : Nat) :
    ∃ z, z ∈ PiAcc.fiber (renamedLt offset) x := by
  apply (PiAcc.fiber_inhabited_iff (renamedLt offset) x).mpr
  have hx := Nat.lt_wfRel.wf.apply x
  induction hx with
  | intro y _ ih =>
    exact Acc.intro y (fun z hz => ih z (Nat.lt_of_add_lt_add_right hz))

end Rcic.F3.PSet.PiAttack
