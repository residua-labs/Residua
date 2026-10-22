import rcic.RcicAnnLR3Sort
import rcic.RcicAnnSortUniq
import rcic.RcicAnnTyRedWk

/-!
# Relational Prop-key coherence already contains a zero-sort row

The `irr` rule supplies `HasTyA P (sort 0)`. A direct relational-key
bridge is `TypedPropKeyA3`: that typing supplies `IsPropTyA3 P`. This
contains two obligations, stated separately here: existence of a finite
relational sort-synthesis witness, and agreement of its Boolean Prop key.

Full `eqN` coherence is stronger data than Boolean coherence. A fresh
variable of declared type `sort u`, retyped along an arbitrary conversion
to `sort v`, shows that the former supplies the full annotated sort row;
the latter supplies only the Boolean/zero-sort row. Exact converse
reductions are proved for the fresh-variable probes. No converse for
general expressions assumes an unnamed principal-inference theorem.

These are kernel-checked reductions of obligations. They do not supply
any of the coherence predicates for the contextual head layer, and they
do not claim the Eq separation or environment theorem. `closure_claim = 0`.
The direct bridge is not asserted necessary for every semantic irrelevance
arm: the existing fundamental arm also has its semantic induction hypotheses,
and the logical relation's proposition clause keys its terminal normal form.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- Agreement of a declarative sort with an already supplied relational
sort witness, at the full level relation. This contains no existence claim. -/
def TypedSortCoherenceA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ (A : ExprA) (u v : Level),
    HasTyA E I n Γ A (.sort u) → SortOfA3 E I n H Γ A v → eqN u v

/-- Agreement only of the two Boolean proposition keys. -/
def TypedSortKeyCoherenceA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ (A : ExprA) (u v : Level),
    HasTyA E I n Γ A (.sort u) → SortOfA3 E I n H Γ A v →
      isZero u = isZero v

/-- The exact zero-sort agreement needed after a synthesized sort is
already available in an irrelevance arm. -/
def PropKeyCoherenceA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ (P : ExprA) (v : Level),
    HasTyA E I n Γ P (.sort .zero) → SortOfA3 E I n H Γ P v →
      isZero v = true

/-- Existence alone at the proposition typings consumed by `ConvA.irr`. -/
def PropSynthesisA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ P : ExprA,
    HasTyA E I n Γ P (.sort .zero) → ∃ v, SortOfA3 E I n H Γ P v

/-- A direct typing-to-relational-Prop-key bridge for irrelevance. -/
def TypedPropKeyA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ P : ExprA,
    HasTyA E I n Γ P (.sort .zero) → IsPropTyA3 E I n H Γ P

theorem typedSortKeyCoherenceA3_of_full
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (h : TypedSortCoherenceA3 E I n H) : TypedSortKeyCoherenceA3 E I n H :=
  fun Γ hΓ A u v ht hs => isZero_eqN (h Γ hΓ A u v ht hs)

theorem propKeyCoherenceA3_of_key
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (h : TypedSortKeyCoherenceA3 E I n H) : PropKeyCoherenceA3 E I n H :=
  fun Γ hΓ P v ht hs => (h Γ hΓ P .zero v ht hs).symm

/-- Determinism splits this direct irrelevance-key bridge into a genuine
existence obligation and a separate coherence obligation. -/
theorem typedPropKeyA3_iff_synthesis_coherence
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n} :
    TypedPropKeyA3 E I n H ↔
      PropSynthesisA3 E I n H ∧ PropKeyCoherenceA3 E I n H := by
  constructor
  · intro h
    constructor
    · intro Γ hΓ P ht
      obtain ⟨v, hs, _⟩ := h Γ hΓ P ht
      exact ⟨v, hs⟩
    · intro Γ hΓ P v ht hs
      exact (isPropTyA3_iff_of_sort H hs).mp (h Γ hΓ P ht)
  · rintro ⟨hex, hcoh⟩ Γ hΓ P ht
    obtain ⟨v, hs⟩ := hex Γ hΓ P ht
    exact ⟨v, hs, hcoh Γ hΓ P v ht hs⟩

/-- Full annotated sort injectivity, restricted to well-formed contexts. -/
def SortConvRowA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ u v : Level,
    TyConvA E I n Γ (.sort u) (.sort v) → eqN u v

/-- Only the proposition-key part of the sort row. -/
def SortKeyRowA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ u v : Level,
    TyConvA E I n Γ (.sort u) (.sort v) → isZero u = isZero v

/-- The zero-sort slice: conversion to `sort 0` forces a zero level. -/
def SortZeroRowA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ u : Level,
    TyConvA E I n Γ (.sort u) (.sort .zero) → isZero u = true

theorem sortKeyRowA3_of_full {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (h : SortConvRowA3 E I n) : SortKeyRowA3 E I n :=
  fun Γ hΓ u v hc => isZero_eqN (h Γ hΓ u v hc)

theorem sortZeroRowA3_of_key {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (h : SortKeyRowA3 E I n) : SortZeroRowA3 E I n :=
  fun Γ hΓ u hc => h Γ hΓ u .zero hc

/-- The Boolean row is exactly its zero slice, using only the existing
level calculus and type-conversion composition. This is not full `eqN`. -/
theorem sortKeyRowA3_of_zero {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (h : SortZeroRowA3 E I n) : SortKeyRowA3 E I n := by
  intro Γ hΓ u v hc
  cases hu : isZero u <;> cases hv : isZero v
  · rfl
  · have hz := h Γ hΓ u (.trans Γ _ _ _ hc
      (tyConvA_sorts Γ ((isZero_iff_eqN_zero v).mp hv)))
    rw [hu] at hz
    cases hz
  · have hz := h Γ hΓ v (.trans Γ _ _ _ hc.symm
      (tyConvA_sorts Γ ((isZero_iff_eqN_zero u).mp hu)))
    rw [hv] at hz
    cases hz
  · rfl

theorem sortKeyRowA3_iff_zero {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    SortKeyRowA3 E I n ↔ SortZeroRowA3 E I n :=
  ⟨sortZeroRowA3_of_key, sortKeyRowA3_of_zero⟩

/-- A fresh variable has this relational sort independently of rows. -/
theorem sortOfA3_sortProbe {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (H : HeadLayerA3 E I n) (Γ : LCtxA) (u : Level) :
    SortOfA3 E I n H (.assumption (.sort u) :: Γ) (.bvar 0) u :=
  ⟨.sort u, .bvar rfl, whTyA3_sort _ u⟩

/-- The probe also has its declared sort by an explicit typing. -/
def sortProbeTypedA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (Γ : LCtxA) (u : Level) :
    HasTyA E I n (.assumption (.sort u) :: Γ) (.bvar 0) (.sort u) :=
  .bvar _ 0 (.sort u) (.succ u) rfl (.sort _ u)

/-- An arbitrary sort conversion retypes the probe after one ordinary
weakening. This is the entire reduction from coherence to a sort row. -/
def sortProbeRetypedA3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {u v : Level}
    (hc : TyConvA E I n Γ (.sort u) (.sort v)) :
    HasTyA E I n (.assumption (.sort u) :: Γ) (.bvar 0) (.sort v) :=
  hasTyA_of_tyConvA (sortProbeTypedA3 Γ u)
    (tyConvA_weaken hE hI (.assumption (.sort u)) (c := 0) (Nat.zero_le _) hc)

def ProbeSortCoherenceA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ u v : Level,
    HasTyA E I n (.assumption (.sort u) :: Γ) (.bvar 0) (.sort v) → eqN u v

def ProbeKeyCoherenceA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ u v : Level,
    HasTyA E I n (.assumption (.sort u) :: Γ) (.bvar 0) (.sort v) →
      isZero u = isZero v

def ProbeZeroCoherenceA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : Prop :=
  ∀ (Γ : LCtxA), CtxWfA E I n Γ → ∀ u : Level,
    HasTyA E I n (.assumption (.sort u) :: Γ) (.bvar 0) (.sort .zero) →
      isZero u = true

private theorem sortProbeTypeConversion {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {u v : Level}
    (ht : HasTyA E I n (.assumption (.sort u) :: Γ) (.bvar 0) (.sort v)) :
    Nonempty (TyConvA E I n (.assumption (.sort u) :: Γ) (.sort u) (.sort v)) := by
  obtain ⟨T, hT, hc⟩ := hasTyA_bvar_gen ht
  have he : T = .sort u := Option.some.inj hT.symm
  cases he
  exact hc

theorem probeSortCoherenceA3_of_row {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (h : SortConvRowA3 E I n) : ProbeSortCoherenceA3 E I n := by
  intro Γ hΓ u v ht
  obtain ⟨hc⟩ := sortProbeTypeConversion ht
  exact h _ (.assumption hΓ (.sort Γ u)) u v hc

theorem probeKeyCoherenceA3_of_row {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (h : SortKeyRowA3 E I n) : ProbeKeyCoherenceA3 E I n := by
  intro Γ hΓ u v ht
  obtain ⟨hc⟩ := sortProbeTypeConversion ht
  exact h _ (.assumption hΓ (.sort Γ u)) u v hc

theorem probeZeroCoherenceA3_of_row {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (h : SortZeroRowA3 E I n) : ProbeZeroCoherenceA3 E I n := by
  intro Γ hΓ u ht
  obtain ⟨hc⟩ := sortProbeTypeConversion ht
  exact h _ (.assumption hΓ (.sort Γ u)) u hc

theorem sortConvRowA3_of_probe {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (h : ProbeSortCoherenceA3 E I n) :
    SortConvRowA3 E I n :=
  fun Γ hΓ u v hc => h Γ hΓ u v (sortProbeRetypedA3 hE hI hc)

theorem sortKeyRowA3_of_probe {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (h : ProbeKeyCoherenceA3 E I n) :
    SortKeyRowA3 E I n :=
  fun Γ hΓ u v hc => h Γ hΓ u v (sortProbeRetypedA3 hE hI hc)

theorem sortZeroRowA3_of_probe {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (h : ProbeZeroCoherenceA3 E I n) :
    SortZeroRowA3 E I n :=
  fun Γ hΓ u hc => h Γ hΓ u (sortProbeRetypedA3 hE hI hc)

theorem sortConvRowA3_iff_probe {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) :
    SortConvRowA3 E I n ↔ ProbeSortCoherenceA3 E I n :=
  ⟨probeSortCoherenceA3_of_row, sortConvRowA3_of_probe hE hI⟩

theorem sortKeyRowA3_iff_probe {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) :
    SortKeyRowA3 E I n ↔ ProbeKeyCoherenceA3 E I n :=
  ⟨probeKeyCoherenceA3_of_row, sortKeyRowA3_of_probe hE hI⟩

theorem sortZeroRowA3_iff_probe {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) :
    SortZeroRowA3 E I n ↔ ProbeZeroCoherenceA3 E I n :=
  ⟨probeZeroCoherenceA3_of_row, sortZeroRowA3_of_probe hE hI⟩

theorem sortConvRowA3_of_typedSortCoherence
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I)
    (h : TypedSortCoherenceA3 E I n H) : SortConvRowA3 E I n := by
  apply sortConvRowA3_of_probe hE hI
  intro Γ hΓ u v ht
  exact eqNA_symm (h _ (.assumption hΓ (.sort Γ u)) (.bvar 0) v u ht
    (sortOfA3_sortProbe H Γ u))

theorem sortKeyRowA3_of_typedSortKeyCoherence
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I)
    (h : TypedSortKeyCoherenceA3 E I n H) : SortKeyRowA3 E I n := by
  apply sortKeyRowA3_of_probe hE hI
  intro Γ hΓ u v ht
  exact (h _ (.assumption hΓ (.sort Γ u)) (.bvar 0) v u ht
    (sortOfA3_sortProbe H Γ u)).symm

theorem sortZeroRowA3_of_propKeyCoherence
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I)
    (h : PropKeyCoherenceA3 E I n H) : SortZeroRowA3 E I n := by
  apply sortZeroRowA3_of_probe hE hI
  intro Γ hΓ u ht
  exact h _ (.assumption hΓ (.sort Γ u)) (.bvar 0) u ht
    (sortOfA3_sortProbe H Γ u)

/-- Even this direct, Prop-only key bridge supplies a zero-sort row.
No claim that it supplies full `eqN` sort uniqueness is made. -/
theorem sortZeroRowA3_of_typedPropKey
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {H : HeadLayerA3 E I n}
    (hE : EnvClosedA E) (hI : IotaLiftA I)
    (h : TypedPropKeyA3 E I n H) : SortZeroRowA3 E I n :=
  sortZeroRowA3_of_propKeyCoherence hE hI
    (typedPropKeyA3_iff_synthesis_coherence.mp h).2

/-- A level-calculus control: identical non-Prop keys do not determine
level equality. This is not a countermodel between the universal row laws. -/
theorem positiveSortKeys_do_not_determine_eqN3 :
    isZero (.succ .zero) = isZero (.succ (.succ .zero)) ∧
      ¬ eqN (.succ .zero) (.succ (.succ .zero)) := by
  refine ⟨rfl, ?_⟩
  intro h
  have he := h (fun _ => some 0)
  change (some 1 : Option Nat) = some 2 at he
  cases he

#print axioms TypedSortCoherenceA3
#print axioms TypedSortKeyCoherenceA3
#print axioms PropKeyCoherenceA3
#print axioms PropSynthesisA3
#print axioms TypedPropKeyA3
#print axioms typedSortKeyCoherenceA3_of_full
#print axioms propKeyCoherenceA3_of_key
#print axioms typedPropKeyA3_iff_synthesis_coherence
#print axioms SortConvRowA3
#print axioms SortKeyRowA3
#print axioms SortZeroRowA3
#print axioms sortKeyRowA3_of_full
#print axioms sortZeroRowA3_of_key
#print axioms sortKeyRowA3_of_zero
#print axioms sortKeyRowA3_iff_zero
#print axioms sortOfA3_sortProbe
#print axioms sortProbeTypedA3
#print axioms sortProbeRetypedA3
#print axioms ProbeSortCoherenceA3
#print axioms ProbeKeyCoherenceA3
#print axioms ProbeZeroCoherenceA3
#print axioms probeSortCoherenceA3_of_row
#print axioms probeKeyCoherenceA3_of_row
#print axioms probeZeroCoherenceA3_of_row
#print axioms sortConvRowA3_of_probe
#print axioms sortKeyRowA3_of_probe
#print axioms sortZeroRowA3_of_probe
#print axioms sortConvRowA3_iff_probe
#print axioms sortKeyRowA3_iff_probe
#print axioms sortZeroRowA3_iff_probe
#print axioms sortConvRowA3_of_typedSortCoherence
#print axioms sortKeyRowA3_of_typedSortKeyCoherence
#print axioms sortZeroRowA3_of_propKeyCoherence
#print axioms sortZeroRowA3_of_typedPropKey
#print axioms positiveSortKeys_do_not_determine_eqN3

end Rcic.Declarative.Ann.LR3
