import rcic.RcicF3PropEvalSafeIndex

/-!
# Typed Prop family memberships do not determine a semantic index key

This separate semantic attack uses a concrete resolved signature and an
explicit interpretation of a family Prop → Prop whose every fiber is true.
Two index constants denote the distinct data codes False and True. Both
family applications have actual HasTyT and HSoundT derivations, and the
same proof value inhabits both fibers, but their complete index keys differ.

This refutes extracting index injectivity from those semantic memberships.
It does not refute the full IotaAt premise: no typed recursor redex or
admitted whole group is claimed here. Actual hereditary conversion nodes
of a recursor redex may carry more information and remain to be analyzed.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false


namespace Rcic.F3.PSet.PropFamilyKeyAttack
open Rcic.Declarative Rcic.Model.PS PiIndex
open PropEvalSafeIndex (witnessTable falseCode trueCode)

noncomputable def familyMember : CheckedMember :=
  ⟨.inductiveM, 0, .pi (.sort .zero) (.sort .zero), none⟩

noncomputable def indexMember : CheckedMember := ⟨.axiomM, 0, .sort .zero, none⟩

/-- A resolved signature, not an asserted admitted environment. -/
noncomputable def signature : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv emptyEnv 0 familyMember) 1 indexMember) 2 indexMember

noncomputable def valuation : Nat → Nat := fun _ => 0
noncomputable def bound : Nat → Nat := fun _ => 0

noncomputable def familyValue (P : Premises4) : PSet.{4} :=
  piLam (mkM P witnessTable) valuation (fun _ => trueCode) ρ0 familyMember.mtype

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4}
  | 0, _ => familyValue P
  | 1, _ => falseCode
  | 2, _ => trueCode
  | _ + 3, _ => pempty

noncomputable def familyTyped : HasTyT signature 0 [] (.const 0 []) familyMember.mtype :=
  .const [] 0 [] familyMember rfl rfl rfl

noncomputable def falseTyped : HasTyT signature 0 [] (.const 1 []) (.sort .zero) :=
  .const [] 1 [] indexMember rfl rfl rfl

noncomputable def trueTyped : HasTyT signature 0 [] (.const 2 []) (.sort .zero) :=
  .const [] 2 [] indexMember rfl rfl rfl

noncomputable def atFalseTyped : HasTyT signature 0 [] (.app (.const 0 []) (.const 1 [])) (.sort .zero) :=
  .app [] (.const 0 []) (.const 1 []) (.sort .zero) (.sort .zero)
    familyTyped falseTyped

noncomputable def atTrueTyped : HasTyT signature 0 [] (.app (.const 0 []) (.const 2 [])) (.sort .zero) :=
  .app [] (.const 0 []) (.const 2 []) (.sort .zero) (.sort .zero)
    familyTyped trueTyped

theorem family_mem (P : Premises4) :
    familyValue P ∈ Ed (mkM P (table P))
      (den (mkM P (table P)) valuation ρ0 familyMember.mtype) := by
  change piLam (mkM P witnessTable) valuation (fun _ => trueCode) ρ0 familyMember.mtype ∈
    Ed (mkM P witnessTable) (den (mkM P witnessTable) valuation ρ0 familyMember.mtype)
  apply piLam_mem (mkM P witnessTable) valuation (envResp_const trueCode) _ ρ0
  intro x hx
  exact (PropEvalSafeIndex.true_fits P valuation).1

theorem family_hereditary (P : Premises4) :
    HSoundT (mkM P (table P)) valuation familyTyped :=
  fun _ _ => family_mem P

theorem false_hereditary (P : Premises4) :
    HSoundT (mkM P (table P)) valuation falseTyped :=
  fun _ _ => (PropEvalSafeIndex.false_fits P valuation).1

theorem true_hereditary (P : Premises4) :
    HSoundT (mkM P (table P)) valuation trueTyped :=
  fun _ _ => (PropEvalSafeIndex.true_fits P valuation).1

private theorem app_hereditary (M : Interp.{4}) (σ : Nat → Nat)
    {f a A B : Expr Nat}
    (hf : HasTyT signature 0 [] f (.pi A B))
    (ha : HasTyT signature 0 [] a A)
    (hsf : HSoundT M σ hf) (hsa : HSoundT M σ ha) :
    HSoundT M σ (.app [] f a A B hf ha) := by
  refine ⟨?_, hsf, hsa⟩
  intro ρ hρ
  change fapp (den M σ ρ f) (den M σ ρ a) ∈ Ed M (den M σ ρ (instantiate0 a B))
  rw [den_inst0]
  exact app_mem M (den_resp M σ ρ B) (hsf.root ρ hρ) (hsa.root ρ hρ)

theorem atFalse_hereditary (P : Premises4) :
    HSoundT (mkM P (table P)) valuation atFalseTyped :=
  app_hereditary (mkM P (table P)) valuation familyTyped falseTyped
    (family_hereditary P) (false_hereditary P)

theorem atTrue_hereditary (P : Premises4) :
    HSoundT (mkM P (table P)) valuation atTrueTyped :=
  app_hereditary (mkM P (table P)) valuation familyTyped trueTyped
    (family_hereditary P) (true_hereditary P)

theorem typed_bounds :
    LOKt valuation 4 bound atFalseTyped ∧ LOKt valuation 4 bound atTrueTyped :=
  ⟨⟨fun _ h => (List.not_mem_nil _ h).elim,
      fun _ h => (List.not_mem_nil _ h).elim⟩,
    ⟨fun _ h => (List.not_mem_nil _ h).elim,
      fun _ h => (List.not_mem_nil _ h).elim⟩⟩

theorem at_false (P : Premises4) :
    Equiv (den (mkM P (table P)) valuation ρ0
      (.app (.const 0 []) (.const 1 []))) trueCode :=
  beta_val (mkM P witnessTable) (fun _ _ _ => Equiv.rfl)
    (PropEvalSafeIndex.false_fits P valuation).1

theorem at_true (P : Premises4) :
    Equiv (den (mkM P (table P)) valuation ρ0
      (.app (.const 0 []) (.const 2 []))) trueCode :=
  beta_val (mkM P witnessTable) (fun _ _ _ => Equiv.rfl)
    (PropEvalSafeIndex.true_fits P valuation).1

theorem same_proof (P : Premises4) :
    pempty ∈ Ed (mkM P (table P)) (den (mkM P (table P)) valuation ρ0
      (.app (.const 0 []) (.const 1 []))) ∧
    pempty ∈ Ed (mkM P (table P)) (den (mkM P (table P)) valuation ρ0
      (.app (.const 0 []) (.const 2 []))) := by
  have hm : pempty ∈ Ed (mkM P (table P)) trueCode :=
    mem_congr_right (ed_tyv (mkM P (table P)) (dich_tv True)).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  exact ⟨mem_congr_right (ed_congr _ (at_false P)).symm hm,
    mem_congr_right (ed_congr _ (at_true P)).symm hm⟩

/-- These are full keys, with an empty parameter prefix and one data index. -/
theorem unequal_keys (P : Premises4) : key [falseCode] ≠ key [trueCode] := by
  intro hk
  exact PropEvalSafeIndex.distinct_codes P ((key_eq_iff _ _).mp hk).1

/-- The membership-only injectivity route is literally false, even on
fitting data indices. This is not the stronger hereditary-redex target. -/
theorem membership_key_injectivity_refuted (P : Premises4) :
    ¬ (∀ x y : PSet.{4},
      x ∈ Ed (mkM P (table P)) (den (mkM P (table P)) valuation ρ0 (.sort .zero)) →
      y ∈ Ed (mkM P (table P)) (den (mkM P (table P)) valuation ρ0 (.sort .zero)) →
      pempty ∈ Ed (mkM P (table P)) (fapp (table P 0 []) x) →
      pempty ∈ Ed (mkM P (table P)) (fapp (table P 0 []) y) →
      key [x] = key [y]) := by
  intro h
  exact unequal_keys P (h falseCode trueCode
    (PropEvalSafeIndex.false_fits P valuation).1
    (PropEvalSafeIndex.true_fits P valuation).1 (same_proof P).1 (same_proof P).2)

noncomputable def Witness (P : Premises4) : Prop :=
  HSoundT (mkM P (table P)) valuation atFalseTyped ∧
  HSoundT (mkM P (table P)) valuation atTrueTyped ∧
  LOKt valuation 4 bound atFalseTyped ∧ LOKt valuation 4 bound atTrueTyped ∧
  Fits (mkM P (table P)) valuation [] ρ0 ∧
  Equiv (den (mkM P (table P)) valuation ρ0 (.app (.const 0 []) (.const 1 [])))
    (den (mkM P (table P)) valuation ρ0 (.app (.const 0 []) (.const 2 []))) ∧
  (pempty ∈ Ed (mkM P (table P)) (den (mkM P (table P)) valuation ρ0
    (.app (.const 0 []) (.const 1 []))) ∧
  pempty ∈ Ed (mkM P (table P)) (den (mkM P (table P)) valuation ρ0
    (.app (.const 0 []) (.const 2 [])))) ∧
  key [falseCode] ≠ key [trueCode]

theorem component_witness (P : Premises4) : Witness P :=
  ⟨atFalse_hereditary P, atTrue_hereditary P, typed_bounds.1, typed_bounds.2,
    True.intro, (at_false P).trans (at_true P).symm, same_proof P, unequal_keys P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropFamilyKeyAttack

#print axioms Rcic.F3.PSet.PropFamilyKeyAttack.atFalse_hereditary
#print axioms Rcic.F3.PSet.PropFamilyKeyAttack.atTrue_hereditary
#print axioms Rcic.F3.PSet.PropFamilyKeyAttack.same_proof
#print axioms Rcic.F3.PSet.PropFamilyKeyAttack.unequal_keys
#print axioms Rcic.F3.PSet.PropFamilyKeyAttack.membership_key_injectivity_refuted
#print axioms Rcic.F3.PSet.PropFamilyKeyAttack.component_witness
#print axioms Rcic.F3.PSet.PropFamilyKeyAttack.component_nonrefutable
