import rcic.RcicAnnLR3GuardedConversionUniverse
import rcic.RcicAnnLR3EnvironmentArmSupply
import rcic.RcicAnnLR3GuardDecision

/-!
# The raw and retained parts of arm transport

Raw evaluator equations transport every predicate on the erased result.
They do not construct a retained code, conversion of two retained codes,
or a decoded-membership premise. The separate relation below keeps that
conversion premise explicit, and its algebra uses the existing kernel
conversion and decoded-PER proofs. In particular it uses the conversion
universe rather than the retained strong-tag universe.

This module does not claim that any missing source arm has been supplied.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.RetainedArmTransfer

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open GuardedTaggedCode

universe u v

/-- Erasure transports an arbitrary raw predicate, independently of how
the enriched semantic result stores its other components. -/
theorem raw_predicate_transport {S : Type u} (erase : S → Value)
    {s : S} {x : Value} (h : ValueEq (erase s) x)
    (P : Value → Prop) : P (erase s) ↔ P x := by
  rw [NeutralCodes.valueEq_eq h]

/-- Both term arguments can be transported, with the candidate fixed.
This theorem intentionally supplies no comparison of candidate codes. -/
theorem raw_relation_transport {S : Type u} {T : Type v}
    (eraseS : S → Value) (eraseT : T → Value)
    {s : S} {t : T} {x y : Value}
    (hs : ValueEq (eraseS s) x) (ht : ValueEq (eraseT t) y)
    (R : Relation) : R (eraseS s) (eraseT t) ↔ R x y := by
  rw [NeutralCodes.valueEq_eq hs, NeutralCodes.valueEq_eq ht]

/-- A paired candidate records conversion of the retained type codes and
the raw term relation interpreted by the left code. This is fixed-candidate
term algebra, not a retained universe judgment: the latter must also retain
the actual codes denoted by its term arguments. -/
def Related {k : Nat} (C : Code.{u} k) (D : Code.{v} k)
    (x y : Value) : Prop :=
  Converts C D ∧ Decoded C.kernel x y

theorem related_left_member {k : Nat} {C : Code.{u} k} {D : Code.{v} k}
    {x y : Value} (h : Related C D x y) : Decoded C.kernel x x :=
  (decoded_laws C.kernel).trans h.2 ((decoded_laws C.kernel).symm h.2)

theorem related_right_member {k : Nat} {C : Code.{u} k} {D : Code.{v} k}
    {x y : Value} (h : Related C D x y) : Decoded D.kernel y y :=
  (converts_decoded_same h.1 y y).mp
    ((decoded_laws C.kernel).trans ((decoded_laws C.kernel).symm h.2) h.2)

theorem related_diagonal {k : Nat} {C : Code.{u} k} {x : Value}
    (hx : Decoded C.kernel x x) : Related C C x x :=
  ⟨converts_refl C, hx⟩

theorem related_symm {k : Nat} {C : Code.{u} k} {D : Code.{v} k}
    {x y : Value} (h : Related C D x y) : Related D C y x :=
  ⟨converts_symm h.1,
    (converts_decoded_same h.1 y x).mp ((decoded_laws C.kernel).symm h.2)⟩

theorem related_trans {k : Nat} {C D E : Code.{u} k}
    {x y z : Value} (h : Related C D x y) (j : Related D E y z) :
    Related C E x z :=
  ⟨converts_trans h.1 j.1,
    (decoded_laws C.kernel).trans h.2 ((converts_decoded_same h.1 y z).mpr j.2)⟩

/-- A type-conversion arm uses a retained kernel conversion. Equality of
the two raw type images would not be a replacement for this premise. -/
theorem related_change_codes {k : Nat} {C D C' D' : Code.{u} k}
    {x y : Value} (hC : Converts C C') (hD : Converts D D')
    (h : Related C D x y) : Related C' D' x y :=
  ⟨converts_trans (converts_symm hC) (converts_trans h.1 hD),
    (converts_decoded_same hC x y).mp h.2⟩

/-- Raw value equality changes a term argument while retaining the type
codes and their conversion evidence. This is the delta-arm operation. -/
theorem related_replace_values {k : Nat} {C : Code.{u} k} {D : Code.{v} k}
    {x x' y y' : Value} (hx : ValueEq x x') (hy : ValueEq y y') :
    Related C D x y ↔ Related C D x' y' := by
  rw [NeutralCodes.valueEq_eq hx, NeutralCodes.valueEq_eq hy]

/-- Decoding the conversion universe returns exactly kernel conversion.
This is the retained premise required by type-changing arm algebra. -/
theorem conversion_universe_change_codes {k : Nat} {C D C' D' : Code.{u} k}
    {x y : Value}
    (hC : (GuardedConversionUniverse.conversionUniverse k).view.relation
      (GuardedConversionUniverse.encode k C) (GuardedConversionUniverse.encode k C'))
    (hD : (GuardedConversionUniverse.conversionUniverse k).view.relation
      (GuardedConversionUniverse.encode k D) (GuardedConversionUniverse.encode k D'))
    (h : Related C D x y) : Related C' D' x y :=
  related_change_codes hC hD h

/-- Level-zero irrelevance transfers from actual retained elements to
their raw decoded members without selecting representatives as data. -/
theorem decoded_irrelevant_zero (K : TaggedSaturatedTower.Kernel.{u} 0)
    {x y : Value} (hx : Decoded K x x) (hy : Decoded K y y) :
    Decoded K x y := by
  obtain ⟨a, ha, ea⟩ := (decoded_good hx).1
  obtain ⟨b, hb, eb⟩ := (decoded_good hy).1
  exact .forward ⟨a, b, K.per.irrelevant rfl a b ha hb, ea, eb⟩

theorem related_irrelevant_zero {C : Code.{u} 0} {D : Code.{v} 0}
    {x y : Value} (hC : Converts C D)
    (hx : Decoded C.kernel x x) (hy : Decoded D.kernel y y) :
    Related C D x y :=
  ⟨hC, decoded_irrelevant_zero C.kernel hx
    ((converts_decoded_same hC y y).mpr hy)⟩

/-- The older proposition examples distinguish kernel conversion too:
their tags already agree, so removing tag equality loses no information
in this particular example. -/
theorem proposition_converts_iff (P Q : Prop) :
    Converts (Code.legacy (GuardDecision.propCode P))
      (Code.legacy (GuardDecision.propCode Q)) ↔ (P ↔ Q) :=
  ⟨fun h => (GuardDecision.propCode_related_iff P Q).mp
    ⟨GuardDecision.propCode_same_tag P Q, h⟩,
    fun h => ((GuardDecision.propCode_related_iff P Q).mpr h).2⟩

/-- A raw universe decoder cannot recover conversion of the particular
retained term codes. The two codes have the same erased image, while their
actual element PERs distinguish False from True. -/
theorem raw_universe_relation_not_retained_conversion :
    Decoded (GuardedConversionUniverse.conversionUniverse.{0} 0).kernel
      (Code.legacy (GuardDecision.propCode False)).view.value
      (Code.legacy (GuardDecision.propCode True)).view.value ∧
    ¬ Converts (Code.legacy (GuardDecision.propCode False))
      (Code.legacy (GuardDecision.propCode True)) := by
  constructor
  · refine .forward ⟨Code.legacy (GuardDecision.propCode False),
      Code.legacy (GuardDecision.propCode False),
      GuardedConversionUniverse.member 0 _, ?_, ?_⟩
    · exact ValueEq.refl _
    · intro c
      rfl
  · intro h
    exact ((proposition_converts_iff False True).mp h).mpr True.intro

end Rcic.Declarative.Ann.LR3.RetainedArmTransfer
