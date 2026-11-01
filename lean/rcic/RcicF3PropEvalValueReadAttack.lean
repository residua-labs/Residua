import rcic.RcicF3EvalPlanScope
import rcic.RcicF3PropEvalValueAttack

/-!
# Actual AccR read congruence across distinct tables and representatives

The admitted group supplies its entire read certificate. The recursor's
fresh table entry is replaced arbitrarily, while every fixed parameter,
motive and minor is replaced by an equivalent union/singleton presentation.
The candidate-produced nonempty result survives all these changes. Two
explicit replacements disagree extensionally at the fresh entry, so the
witness does not rely on global table agreement. An extra index suffix is
still rejected. The selected AccR parameter retains the empty recursive
child domain recorded by the underlying value witness. This is the admitted
AccR fixture. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEvalValueReadAttack
open Rcic.Declarative PiIndex PlanPropEndAttack PropEval
open PropEvalUniqueAttack (ctx)

def representative (x : PSet.{4}) : PSet.{4} := sUnion (singleton x)

theorem representative_equiv (x : PSet.{4}) : Equiv x (representative x) :=
  (PropEvalExtract.union_eq_of_mem (mem_singleton.mpr (Equiv.refl x))
    (fun _ hx => mem_singleton.mp hx)).symm

theorem representatives_equiv : (xs : List PSet.{4}) → LEq xs (xs.map representative)
  | [] => True.intro
  | x :: xs => ⟨representative_equiv x, representatives_equiv xs⟩

theorem representative_minor_length (C : Context) :
    (C.minors.map representative).length = C.node.a.constructors.length := by
  rw [List.length_map]
  exact C.minor_length

/-- Every scope conjunct is obtained from the actual admitted group. -/
theorem scope (P : Premises4) : EndpointReads (Dom (ctx P).node.E0) (ctx P) :=
  EvalPlanScope.endpointReads_of_group (ctx P) accFamMember [(1, accIntroMember)]
    .empty rfl (fun c hc => by cases List.mem_singleton.mp hc; rfl) rfl AccEnv.accMembersT

noncomputable def table (P : Premises4) (X : List Nat → PSet.{4}) :
    Nat → List Nat → PSet.{4} := upd (installed P) (ctx P).rr X

noncomputable def altered (P : Premises4) (X : List Nat → PSet.{4}) : Context :=
  ((ctx P).withModel (mkM P (table P X))).withValues
    ((ctx P).parameters.map representative) (representative (ctx P).motive)
    ((ctx P).minors.map representative) (representative_minor_length (ctx P))

noncomputable def value (P : Premises4) (X : List Nat → PSet.{4}) (i : Index.{4}) :
    PSet.{4} := PropEvalValue.result (altered P X) (.param 0) i

theorem value_same (P : Premises4) (X : List Nat → PSet.{4}) (i : Index.{4}) :
    Equiv (PropEvalValue.result (ctx P) (.param 0) i) (value P X i) :=
  PropEvalValue.result_read_congr (C := ctx P) P (installed P) (table P X)
    (Dom (ctx P).node.E0) rfl (agreeOn_upd (ctx P).node.fresh (installed P) X)
    (scope P) ((ctx P).parameters.map representative) (representative (ctx P).motive)
    ((ctx P).minors.map representative) (representative_minor_length (ctx P))
    (representatives_equiv (ctx P).parameters) (representative_equiv (ctx P).motive)
    (representatives_equiv (ctx P).minors) (.param 0) i

theorem evaluation_iff (P : Premises4) (X : List Nat → PSet.{4})
    (i : Index.{4}) (z : PSet.{4}) : Eval (ctx P) i z ↔ Eval (altered P X) i z :=
  Eval.read_iff (C := ctx P) P (installed P) (table P X) (Dom (ctx P).node.E0)
    rfl (agreeOn_upd (ctx P).node.fresh (installed P) X) (scope P).toNodeReads
    ((ctx P).parameters.map representative) (representative (ctx P).motive)
    ((ctx P).minors.map representative) (representative_minor_length (ctx P))
    (representatives_equiv (ctx P).parameters) (representative_equiv (ctx P).motive)
    (representatives_equiv (ctx P).minors) i z

/-- This occurrence of Eval is obtained from the public constructor producer
through the bounded value, then transported by the full read law. -/
theorem produced (P : Premises4) (X : List Nat → PSet.{4}) :
    Eval (altered P X) (key [parameter]) (value P X (key [parameter])) := by
  have he := (evaluation_iff P X (key [parameter]) (PropEvalValueAttack.result P)).mp
    (PropEvalValueAttack.result_spec P).2
  exact he.output_congr (value_same P X (key [parameter])).symm

theorem typed (P : Premises4) (X : List Nat → PSet.{4}) :
    value P X (key [parameter]) ∈ domain :=
  mem_congr_left (value_same P X (key [parameter])) (PropEvalValueAttack.result_domain P)

theorem nonempty (P : Premises4) (X : List Nat → PSet.{4}) :
    ¬ Equiv (value P X (key [parameter])) pempty :=
  fun h => PropEvalValueAttack.result_nonempty P ((value_same P X (key [parameter])).trans h)

/-- Keeping the parameter prefix never erases a surplus index suffix. -/
theorem suffix_rejected (P : Premises4) (X : List Nat → PSet.{4}) :
    Equiv (value P X (key [parameter, datum])) pempty ∧
      value P X (key [parameter, datum]) ∉ domain := by
  have he := (value_same P X (key [parameter, datum])).symm.trans
    (PropEvalValueAttack.invalid_key P).1
  refine ⟨he, ?_⟩
  intro ht
  exact dataVal_ne_pempty _ _ ((mem_singleton.mp ht).symm.trans he)

/-- The two test tables really disagree at the fresh recursor entry. -/
theorem tables_different (P : Premises4) :
    ¬ Equiv (table P (fun _ => pempty) (ctx P).rr [])
      (table P (fun _ => singleton pempty) (ctx P).rr []) := by
  unfold table
  rw [upd_eq, upd_eq]
  intro h
  exact not_mem_pempty (mem_congr_right h.symm (mem_singleton.mpr Equiv.rfl))

theorem different_tables_same_value (P : Premises4) (i : Index.{4}) :
    Equiv (value P (fun _ => pempty) i) (value P (fun _ => singleton pempty) i) :=
  (value_same P (fun _ => pempty) i).symm.trans (value_same P (fun _ => singleton pempty) i)

def Witness (P : Premises4) : Prop :=
  PropEvalValueAttack.Witness P ∧
  EndpointReads (Dom (ctx P).node.E0) (ctx P) ∧
  (ctx P).σ 0 = 1 ∧
  (¬ Equiv (table P (fun _ => pempty) (ctx P).rr [])
    (table P (fun _ => singleton pempty) (ctx P).rr [])) ∧
  (∀ i, Equiv (value P (fun _ => pempty) i) (value P (fun _ => singleton pempty) i)) ∧
  ∀ X : List Nat → PSet.{4},
    Eval (altered P X) (key [parameter]) (value P X (key [parameter])) ∧
    value P X (key [parameter]) ∈ domain ∧
    ¬ Equiv (value P X (key [parameter])) pempty ∧
    Equiv (value P X (key [parameter, datum])) pempty ∧
    value P X (key [parameter, datum]) ∉ domain

/-- Literal composition and a nonempty real-fixture witness for both read faces. -/
theorem component_witness (P : Premises4) : Witness P := by
  refine ⟨PropEvalValueAttack.component_witness P, scope P, rfl, tables_different P,
    different_tables_same_value P, ?_⟩
  intro X
  exact ⟨produced P X, typed P X, nonempty P X, (suffix_rejected P X).1,
    (suffix_rejected P X).2⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalValueReadAttack
