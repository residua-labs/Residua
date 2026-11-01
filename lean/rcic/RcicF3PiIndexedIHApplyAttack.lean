import rcic.RcicF3PiIndexedIHApply
import rcic.RcicF3PiIndexedIHBuilderAttack

/-!
# Executable-builder computation on an inhabited normalized telescope

The existing depth-three proof-field fixture supplies its actual field,
arbitrary-sort motive and builder type. The new computation theorem now
applies to every fitting argument list; a concrete fitting list witnesses
that its domain is inhabited. Complete dependent argument keys are also
observed by a separate key-length map. No complete raw group is asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiIndexedIHApplyAttack
open Rcic.Declarative PiIndex
open PiRawIHAttack (model ds args field ihExpr)
open PiRawIHAnyAttack (datum σ assignment)
open PiIndexedIHBuilderAttack (indexedValue)

/-- Computation uses the same value whose executable IH type is already produced. -/
theorem apply_on_fitting (P : Premises4) (f : Nat)
    (xs : List PSet.{4}) (hxs : TelFits (model P f) σ (ds f) (assignment P f) xs) :
    Equiv (fapps (indexedValue P f) xs) datum :=
  PiIndexedIHApply.indexed_apply (model P f) σ (ds f) args (assignment P f)
    (fun _ _ => datum) (fun _ _ _ _ => Equiv.rfl) pempty xs hxs

/-- Literal conjunction for the produced executable computation component. -/
def Witness (P : Premises4) (f : Nat) : Prop :=
    ∃ xs : List PSet.{4},
      TelFits (model P f) σ (ds f) (assignment P f) xs ∧
      funIHType emptyEnv 32 0 (field f) (.bvar 0) 3 = some (ihExpr f) ∧
      pempty ∈ Ed (model P f) (den (model P f) σ (assignment P f) (field f)) ∧
      indexedValue P f ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) ∧
      (∀ zs, TelFits (model P f) σ (ds f) (assignment P f) zs →
        Equiv (fapps (indexedValue P f) zs) datum) ∧
      ihAtN (fun _ => datum) 3 pempty ∉
        Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f))

/-- Actual builder membership, inhabited application and uniform computation compose. -/
theorem component_witness (P : Premises4) (f : Nat) : Witness P f := by
  obtain ⟨hb, hf, hi, _, ho⟩ := PiIndexedIHBuilderAttack.inhabited P f
  exact ⟨[PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum],
    (PiRawIHAnyAttack.inhabited P f).2.1, hb, hf, hi, apply_on_fitting P f, ho⟩

/-- Non-refutability of the same literal component, under the supplied P. -/
theorem component_nonrefutable (P : Premises4) (f : Nat) :
    ¬ (Witness P f → (Premises4 → False)) :=
  fun h => h (component_witness P f) P

/-- This leaf map distinguishes complete-key arities; it does not inspect the erased major. -/
def keyMap (i : Index.{4}) (_ : PSet.{4}) : PSet.{4} := dataVal (arity i) []

/-- Three actual argument binders retain both selected dependent arguments. -/
theorem full_key_application (P : Premises4) (f : Nat)
    (xs : List PSet.{4}) (hxs : TelFits (model P f) σ (ds f) (assignment P f) xs) :
    Equiv
      (fapps ((tel (model P f) σ (ds f) [.bvar 1, .bvar 0] (assignment P f)).indexedIH
        (model P f) keyMap pempty) xs)
      (dataVal 2 []) := by
  have h := PiIndexedIHApply.indexed_apply (model P f) σ (ds f)
    [.bvar 1, .bvar 0] (assignment P f) keyMap
    (fun _ _ _ _ => Equiv.rfl) pempty xs hxs
  exact h

/-- An erased or prefix-only key gives a different result on the inhabited domain. -/
theorem truncated_key_rejected (P : Premises4) (f : Nat) :
    ∃ xs : List PSet.{4},
      TelFits (model P f) σ (ds f) (assignment P f) xs ∧
      ¬ Equiv
        (fapps ((tel (model P f) σ (ds f) [.bvar 1, .bvar 0] (assignment P f)).indexedIH
          (model P f) keyMap pempty) xs)
        (keyMap (key [PiPropPrefixAttack.datum]) pempty) := by
  let xs := [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum]
  have hx := (PiRawIHAnyAttack.inhabited P f).2.1
  refine ⟨xs, hx, ?_⟩
  intro h
  have he : Equiv (dataVal 2 []) (dataVal 1 []) :=
    (full_key_application P f xs hx).symm.trans h
  have hn : 2 = 1 := (dataVal_inj rfl he).1
  omega


/-- Hidden readers and renumbering compose with the same inhabited computation
witness. Delta aliases here are reader fixtures, not fully typed environments. -/
def HiddenWitness (P : Premises4) : Prop :=
  ∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, PiRawIHAttack.beta f, PiRawIHAttack.delta f, PiRawIHAttack.zeta f],
      funIHType (PiRawIHAttack.env f) 32 0 A (.bvar 0) 3 = some (ihExpr f) ∧ Witness P f

theorem hidden_component_witness (P : Premises4) : HiddenWitness P :=
  fun f hf A hA => ⟨(PiIndexedIHBuilderAttack.hidden_values P f hf A hA).1,
    component_witness P f⟩

theorem hidden_component_nonrefutable (P : Premises4) :
    ¬ (HiddenWitness P → (Premises4 → False)) :=
  fun h => h (hidden_component_witness P) P

end Rcic.F3.PSet.PiIndexedIHApplyAttack
