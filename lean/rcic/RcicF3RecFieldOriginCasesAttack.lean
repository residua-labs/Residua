import rcic.RcicF3RecFieldOriginCases
import rcic.RcicF3RecFieldOriginAttack
import rcic.RcicF3BoundedBetaOriginAttack

/-!
# Bounded origin conversion at the actual higher-order W prefix

The actual W recursive lookup has a nonempty value: applying it at the
inhabited ord1 branch produces a DATA member. An actual bounded beta
conversion changes its expected type to a syntactically hidden copy. The
new conversion-rule producer transports the Origin with the same value
and full key, and the actual reader still reports the original Pi depth.

Any bounded retyping of this actual lookup at a family-free expected type
is ruled out by extracting its real lookup-conversion chain, transporting
the Origin and invoking the new clean-expected case. Separately, the real
bounded typing of the recursive field TYPE rules out a sort-valued Origin.
Both original source/enlarged contexts, the extra valuation slot, the
height-omega W value and the dependent beta-provenance witness are retained.
These are auxiliary local judgments at the admitted W prefix, not a
universal domain mask or a modification of the admitted W group.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldOriginCasesAttack
open Rcic.Declarative RawFamily PiIndex RecFieldOrigin
open NormFreshHeadAttack (base C D model σ admissible_C admissible_D prefix_sound)
open RecFieldOriginAttack (Γ ρ field)
open PendAWBridge (fd)

def fieldLevel : Level := .imax (.succ .zero) (.succ .zero)
def hiddenField : Expr Nat := .app (.lam (.sort fieldLevel) (.bvar 0)) field

noncomputable def field_typed : HasTyT PendAW.eFam 0 Γ field (.sort fieldLevel) :=
  .pi Γ (.bvar 4) (.succ .zero) (.app (.const 4 []) (.bvar 5)) (.succ .zero)
    (.bvar _ 4 _ rfl)
    (.app _ (.const 4 []) (.bvar 5) (.sort (.succ .zero)) (.sort (.succ .zero))
      (.const _ 4 [] PendAW.fam rfl rfl rfl) (.bvar _ 5 _ rfl))

theorem field_bound (τ K : Nat → Nat) : LOKt τ 4 K field_typed := by
  change 1 ≤ 4 ∧ 1 ≤ 4 ∧ True ∧
    ((∀ l, l ∈ ([] : List Level) → evalTotal τ l ≤ K 4) ∧ True)
  exact ⟨by decide, by decide, True.intro,
    (fun l hl => (List.not_mem_nil l hl).elim), True.intro⟩

noncomputable def hidden_reduct : ConvT PendAW.eFam 0 Γ hiddenField field
    (.sort fieldLevel) :=
  .beta Γ (.sort fieldLevel) (.bvar 0) field (.sort fieldLevel)
    (.succ fieldLevel) (.sort Γ fieldLevel) (.bvar _ 0 _ rfl) field_typed

theorem hidden_bound (τ K : Nat → Nat) : LOKc τ 4 K hidden_reduct :=
  ⟨by change 2 ≤ 4; decide, True.intro, field_bound τ K⟩

noncomputable def field_conversion : ConvT PendAW.eFam 0 Γ field hiddenField
    (.sort fieldLevel) :=
  .symm Γ hiddenField field (.sort fieldLevel) hidden_reduct

noncomputable def hidden_head_typed : HasTyT PendAW.eFam 0 Γ (.bvar 3) hiddenField :=
  .conv Γ (.bvar 3) field hiddenField fieldLevel
    RecFieldOriginAttack.head_typed field_conversion

theorem hidden_head_bound (τ K : Nat → Nat) : LOKt τ 4 K hidden_head_typed :=
  ⟨True.intro, hidden_bound τ K⟩

theorem field_different : field ≠ hiddenField := by
  intro h
  cases h

theorem hidden_reader : piTelescopeFuel PendAW.eFam 16 hiddenField =
    some ([.bvar 4], foldApps (.const 4 (canonL 0)) [.bvar 5]) := rfl

/-- Actual bounded conversion changes only the expected type; the
recursive value and the complete reader key are not reconstructed. -/
theorem hidden_origin (P : Premises4) (K : Nat → Nat) :
    Origin (mkM P (base P)) fd (C P) 1
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) hiddenField))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) hiddenField))
      (RawFamilyIHBuilderAttack.x P) :=
  RecFieldOriginCases.conversion_rule P
    (table P (base P) fd (C P)) (table P (base P) fd (D P)) σ K
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0)
    (ρ P) (ρ P) (RecFieldOriginAttack.contexts_fit P).1
    (RecFieldOriginAttack.contexts_fit P).2 RecFieldOriginAttack.head_typed
    field_conversion (hidden_head_bound σ K) (RecFieldOriginAttack.lookup_origin P K)

/-- The branch function is nonempty because its actual inhabited branch
application is a nonempty DATA value in the source family. -/
theorem field_nonempty (P : Premises4) (K : Nat → Nat) :
    ¬ Equiv (RawFamilyIHBuilderAttack.x P) pempty := by
  intro he
  apply RecFieldOriginAttack.result_nonempty P K
  change Equiv (fapp (RawFamilyIHBuilderAttack.x P) (ord 1)) pempty
  exact (fapp_congr he Equiv.rfl).trans (fapp_pempty (ord 1))

/-- The conversion chain is extracted from the proposed actual typing;
the clean expected-type theorem consumes the resulting converted Origin. -/
theorem no_clean_retyping (P : Premises4) (K : Nat → Nat)
    (A : Expr Nat) (hfree : occursConst 4 A = false)
    (d : HasTyT PendAW.eFam 0 Γ (.bvar 3) A) (hd : LOKt σ 4 K d) : False := by
  obtain ⟨c, hc⟩ := BoundedBVar.extract_of_lookup σ 4 K
    (show lookupType Γ 3 = some field from rfl) d hd
  have ho := RecFieldOriginCases.bounded_conversion P
    (table P (base P) fd (C P)) (table P (base P) fd (D P)) σ K
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (prefix_sound P (D P) (admissible_D P) σ K 0)
    (ρ P) (ρ P) (RecFieldOriginAttack.contexts_fit P).1
    (RecFieldOriginAttack.contexts_fit P).2 c hc
    (RecFieldOriginAttack.lookup_origin P K)
  exact field_nonempty P K (RecFieldOriginCases.clean_expected P (base P) fd (C P)
    σ K (prefix_sound P (C P) (admissible_C P) σ K 0)
    (ρ P) (RecFieldOriginAttack.contexts_fit P).1 hfree d hd ho)

/-- The actual recursive-field type has an actual bounded sort derivation.
The tainted case at that sort is excluded by the generic produced case. -/
theorem no_sort_origin (P : Premises4) (K : Nat → Nat) (m : Nat) :
    ¬ Origin (mkM P (base P)) fd (C P) m
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) (.sort fieldLevel)))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) (.sort fieldLevel)))
      (den (model P (C P)) σ (ρ P) field) := by
  intro ho
  exact RecFieldOriginCases.sort_exclusion P (base P) fd (C P) σ K
    (prefix_sound P (C P) (admissible_C P) σ K 0)
    (ρ P) (RecFieldOriginAttack.contexts_fit P).1 field_typed (field_bound σ K) ho

def Witness (P : Premises4) : Prop :=
  RecFieldOriginAttack.Witness P ∧ BoundedBetaOriginAttack.Witness P ∧
  field ≠ hiddenField ∧
  piTelescopeFuel PendAW.eFam 16 hiddenField =
    some ([.bvar 4], foldApps (.const 4 (canonL 0)) [.bvar 5]) ∧
  Nonempty (HasTyT PendAW.eFam 0 Γ (.bvar 3) hiddenField) ∧
  (∀ K, LOKt σ 4 K hidden_head_typed ∧
    Origin (mkM P (base P)) fd (C P) 1
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) hiddenField))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) hiddenField))
      (RawFamilyIHBuilderAttack.x P) ∧
    ¬ Equiv (RawFamilyIHBuilderAttack.x P) pempty ∧
    (∀ (A : Expr Nat), occursConst 4 A = false →
      ∀ d : HasTyT PendAW.eFam 0 Γ (.bvar 3) A, LOKt σ 4 K d → False) ∧
    (∀ m, ¬ Origin (mkM P (base P)) fd (C P) m
      (Ed (model P (C P)) (den (model P (C P)) σ (ρ P) (.sort fieldLevel)))
      (Ed (model P (D P)) (den (model P (D P)) σ (ρ P) (.sort fieldLevel)))
      (den (model P (C P)) σ (ρ P) field)))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨RecFieldOriginAttack.component_witness P, BoundedBetaOriginAttack.component_witness P,
    field_different, hidden_reader, ⟨hidden_head_typed⟩,
    fun K => ⟨hidden_head_bound σ K, hidden_origin P K, field_nonempty P K,
      no_clean_retyping P K, no_sort_origin P K⟩⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.RecFieldOriginCasesAttack
