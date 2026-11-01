import rcic.RcicF3PropEvalSafeIndex
import rcic.RcicF3ReaderDeltaAttack
import rcic.RcicF3EvalPlanNormalAttack

/-!
# Full-key and dependent-row attacks for safe-index comparison

The new concrete telescope has one Sort-0 parameter, a revealed Sort-0
data field, and an unrevealed proof field depending on that data field.
Both parameter choices and the complete field tuple fit. The index-only
keys coincide while the full parameter/index keys differ. The revealed
value is not equivalent to the empty proof value, so an all-proof erasure
of this telescope is false. The unrevealed row has an actual bounded
HasTyT derivation in its parameter-and-field prefix.

The universal mixed-tuple comparator below invokes the new producer with
that concrete bound package. Its fitting-tuple and full-key hypotheses
remain explicit. A separate theorem executes it on the inhabited tuple.

The same-P conjunction also retains the existing named reader executions:
ReaderDeltaAttack.Witness includes the admitted stored delta body and
ReaderProvenanceAttack's inhabited beta/zeta-hidden depth-three telescope
with a height-omega W member. EvalPlanNormalAttack.Witness includes the
actual AccR normalized constructor and the existing beta/delta/zeta
normalization fixtures at family labels 1, 2, and 987. These are separate
fixtures; no new admitted alias environment or evaluation on the mixed
telescope is asserted. The AccR witness does not claim an imported
Acc-on-Nat.lt environment or an inhabited recursive child domain.

This module changes no BoundG clause, D check, or checked-tier antecedent.
The component and its non-refutability theorem use the same Premises4
value throughout. Native verification is recorded in the accompanying receipt.
closure_claim = 0; scope_closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PropEvalSafeIndexAttack

open Rcic.Declarative PiIndex PropEvalSafeIndex

def mixedParameters : List (Expr Nat) := [.sort .zero]
def mixedFields : List (Expr Nat) := [.sort .zero, .bvar 0]
def mixedIndices : List (Expr Nat) := [.bvar 1]

/-- The second field is typed in the actual prefix containing the parameter
and the first field. Its type is Prop, for every valuation. -/
noncomputable def proofRow : HasTyT emptyEnv 0
    [.assumption (.sort .zero), .assumption (.sort .zero)]
    (.bvar 0) (.sort .zero) :=
  .bvar _ 0 (.sort .zero) rfl

/-- The first field is revealed; the second has a produced bounded row.
Thus this bound package is not vacuous at every field position. -/
theorem mixed_bounds (K σ : Nat → Nat) :
    UnrevealedBounds emptyEnv 0 σ K mixedParameters mixedFields mixedIndices := by
  intro j hnot
  have hj : j.val = 0 ∨ j.val = 1 := by
    have h := j.isLt
    simp only [mixedFields, List.length_cons, List.length_nil] at h
    omega
  rcases hj with hj | hj
  · apply False.elim
    apply hnot
    change Expr.bvar (2 - 1 - j.val) ∈ [Expr.bvar 1]
    rw [hj]
    exact List.mem_singleton.mpr rfl
  · have he : j = (⟨1, by decide⟩ : Fin mixedFields.length) := Fin.ext hj
    subst j
    exact ⟨.zero, rfl, proofRow, True.intro⟩

theorem proof_row_unrevealed :
    Expr.bvar (mixedFields.length - 1 - 1) ∉ mixedIndices := by decide

theorem parameters_false_fit (P : Premises4) (σ : Nat → Nat) :
    TelFits (mkM P witnessTable) σ mixedParameters ρ0 [falseCode] :=
  PropEvalSafeIndex.false_fits P σ

theorem parameters_true_fit (P : Premises4) (σ : Nat → Nat) :
    TelFits (mkM P witnessTable) σ mixedParameters ρ0 [trueCode] :=
  PropEvalSafeIndex.true_fits P σ

/-- The first actual value is a data code; the second is its proof. -/
theorem mixed_tuple_fits (P : Premises4) (σ : Nat → Nat)
    (ps : List PSet.{4}) :
    TelFits (mkM P witnessTable) σ mixedFields (push ps ρ0) [trueCode, pempty] := by
  refine ⟨?_, ?_, True.intro⟩
  · exact (PropEvalSafeIndex.true_fits P σ).1
  · exact mem_congr_right (ed_tyv (mkM P witnessTable) (dich_tv True)).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)

theorem revealed_value_not_proof : ¬ Equiv trueCode pempty :=
  tyv_ne_pempty (tv True)

/-- The old all-proof telescope condition is false on this fitting fixture. -/
theorem mixed_not_all_proofs (P : Premises4) (σ : Nat → Nat)
    (ps : List PSet.{4}) :
    ¬ PropTel (mkM P witnessTable) σ mixedFields (push ps ρ0) := by
  intro h
  exact revealed_value_not_proof (h.1 trueCode (mixed_tuple_fits P σ ps).1)

noncomputable def indicesKey (P : Premises4) (σ : Nat → Nat) (ps xs : List PSet.{4}) : Index.{4} :=
  key (mixedIndices.map (den (mkM P witnessTable) σ (push xs (push ps ρ0))))

noncomputable def fullKey (P : Premises4) (σ : Nat → Nat) (ps xs : List PSet.{4}) : Index.{4} :=
  key (ps ++ mixedIndices.map (den (mkM P witnessTable) σ (push xs (push ps ρ0))))

/-- Deleting the parameter segment identifies two actual fitting instances. -/
theorem indices_only_alias (P : Premises4) (σ : Nat → Nat) :
    indicesKey P σ [falseCode] [trueCode, pempty] =
      indicesKey P σ [trueCode] [trueCode, pempty] := rfl

/-- The complete key distinguishes exactly those two parameter instances. -/
theorem full_key_separates_parameters (P : Premises4) (σ : Nat → Nat) :
    fullKey P σ [falseCode] [trueCode, pempty] ≠
      fullKey P σ [trueCode] [trueCode, pempty] := by
  change key [falseCode, trueCode] ≠ key [trueCode, trueCode]
  intro he
  have hl : LEq [falseCode, trueCode] [trueCode, trueCode] :=
    (key_eq_iff _ _).mp he
  exact PropEvalSafeIndex.distinct_codes P hl.1

/-- A produced comparator at a fixed dependent telescope. Fitting values
and equality of the full key remain the literal conditional inputs. -/
theorem mixed_comparison (P : Premises4) (K σ : Nat → Nat)
    (ps ps' xs xs' : List PSet.{4})
    (hps : TelFits (mkM P witnessTable) σ mixedParameters ρ0 ps)
    (hps' : TelFits (mkM P witnessTable) σ mixedParameters ρ0 ps')
    (hx : TelFits (mkM P witnessTable) σ mixedFields (push ps ρ0) xs)
    (hx' : TelFits (mkM P witnessTable) σ mixedFields (push ps' ρ0) xs')
    (hkey : fullKey P σ ps xs = fullKey P σ ps' xs') : LEq xs xs' :=
  PropEvalSafeIndex.fields_equiv_of_bounds P witnessTable K σ
    mixedParameters mixedFields mixedIndices
    (witness_prefix_sound P K σ 0) (mixed_bounds K σ)
    ps ps' xs xs' hps hps' hx hx' hkey

/-- An inhabited execution of the public comparator, including its actual
dependent proof-row branch and nonempty parameter segment. -/
theorem mixed_comparison_at_tuple (P : Premises4) (K σ : Nat → Nat) :
    LEq [trueCode, pempty] [trueCode, pempty] :=
  mixed_comparison P K σ [falseCode] [falseCode]
    [trueCode, pempty] [trueCode, pempty]
    (parameters_false_fit P σ) (parameters_false_fit P σ)
    (mixed_tuple_fits P σ [falseCode]) (mixed_tuple_fits P σ [falseCode]) rfl

def MixedWitness (P : Premises4) : Prop :=
  (∀ K σ, UnrevealedBounds emptyEnv 0 σ K mixedParameters mixedFields mixedIndices) ∧
  Expr.bvar (mixedFields.length - 1 - 1) ∉ mixedIndices ∧
  (∀ σ, TelFits (mkM P witnessTable) σ mixedParameters ρ0 [falseCode] ∧
    TelFits (mkM P witnessTable) σ mixedParameters ρ0 [trueCode] ∧
    TelFits (mkM P witnessTable) σ mixedFields (push [falseCode] ρ0) [trueCode, pempty] ∧
    TelFits (mkM P witnessTable) σ mixedFields (push [trueCode] ρ0) [trueCode, pempty]) ∧
  ¬ Equiv trueCode pempty ∧
  (∀ σ ps, ¬ PropTel (mkM P witnessTable) σ mixedFields (push ps ρ0)) ∧
  (∀ σ, indicesKey P σ [falseCode] [trueCode, pempty] =
      indicesKey P σ [trueCode] [trueCode, pempty] ∧
    fullKey P σ [falseCode] [trueCode, pempty] ≠
      fullKey P σ [trueCode] [trueCode, pempty]) ∧
  (∀ (K σ : Nat → Nat) ps ps' xs xs',
    TelFits (mkM P witnessTable) σ mixedParameters ρ0 ps →
    TelFits (mkM P witnessTable) σ mixedParameters ρ0 ps' →
    TelFits (mkM P witnessTable) σ mixedFields (push ps ρ0) xs →
    TelFits (mkM P witnessTable) σ mixedFields (push ps' ρ0) xs' →
    fullKey P σ ps xs = fullKey P σ ps' xs' → LEq xs xs') ∧
  (∀ K σ : Nat → Nat, LEq [trueCode, pempty] [trueCode, pempty])

theorem mixed_witness (P : Premises4) : MixedWitness P :=
  ⟨mixed_bounds, proof_row_unrevealed,
    fun σ => ⟨parameters_false_fit P σ, parameters_true_fit P σ,
      mixed_tuple_fits P σ [falseCode], mixed_tuple_fits P σ [trueCode]⟩,
    revealed_value_not_proof, mixed_not_all_proofs P,
    fun σ => ⟨indices_only_alias P σ, full_key_separates_parameters P σ⟩,
    mixed_comparison P, mixed_comparison_at_tuple P⟩

def Witness (P : Premises4) : Prop :=
  MixedWitness P ∧
  PropEvalSafeIndex.Witness P ∧
  ReaderDeltaAttack.Witness P ∧
  EvalPlanNormalAttack.Witness P

/-- Composition of the mixed safe-index execution and the existing concrete
hidden/depth-three/height-omega/AccR witnesses, all at the same P. -/
theorem component_witness (P : Premises4) : Witness P :=
  ⟨mixed_witness P, PropEvalSafeIndex.component_witness P,
    ReaderDeltaAttack.component_witness P, EvalPlanNormalAttack.component_witness P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalSafeIndexAttack

#print axioms Rcic.F3.PSet.PropEvalSafeIndexAttack.mixed_bounds
#print axioms Rcic.F3.PSet.PropEvalSafeIndexAttack.full_key_separates_parameters
#print axioms Rcic.F3.PSet.PropEvalSafeIndexAttack.mixed_comparison
#print axioms Rcic.F3.PSet.PropEvalSafeIndexAttack.mixed_not_all_proofs
#print axioms Rcic.F3.PSet.PropEvalSafeIndexAttack.component_witness
#print axioms Rcic.F3.PSet.PropEvalSafeIndexAttack.component_nonrefutable
