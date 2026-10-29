import rcic.RcicAnnLR3EqTracer
import rcic.RcicAnnLR3NeutralK

/-!
# Positive control: a K-edge completion realizes the stuck J without collapse

`EqTracer.stuck_j_boundary_congr` shows that no head-separating relation
(exact on closed values, a congruence on stuck calls) realizes the
Scott-encoded J over proof-irrelevant proofs. This module constructs the
repair that the K-aware literature uses (Carneiro's K-like rule;
`NeutralK.Path` in this tree): generate by the exact relation plus the
K edge from the computing call at refl to the stuck call at the neutral
major, and take the PER completion.

`k_completion_repairs`: the completion is a saturated PER, it realizes the
call over the irrelevant proofs, it is not head-separating, and it does not
collapse (the minor is not related to the bottom value). In the real design
the K edge is guarded by the Eq proof's index relation; here the single
edge is that guard's true case. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EqKRepair

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open EqTracer
open NeutralK (Path path_laws)

def kEdge (S : Value) : Relation := fun x y =>
  ValueEq x (call S reflV) ∧ ValueEq y (call S stuckMajor)

def kGen (S : Value) : Relation := fun x y => exactRel x y ∨ kEdge S x y

/-- The PER completion of the exact relation and the K edge. -/
def kRel (S : Value) : Relation := Path (kGen S)

theorem kRel_laws (S : Value) : Laws (kRel S) :=
  ⟨(path_laws _).symm, (path_laws _).trans⟩

theorem call_bot (S h : Value) : call S h .bot := Or.inl rfl

theorem kRel_bot (S : Value) {x y : Value} (h : kRel S x y) : x .bot := by
  induction h with
  | forward h =>
      rcases h with ⟨_, hx⟩ | ⟨hx, _⟩
      · exact hx
      · exact (hx .bot).mpr (call_bot _ _)
  | backward h =>
      rcases h with ⟨he, hy⟩ | ⟨_, hx⟩
      · exact (he .bot).mp hy
      · exact (hx .bot).mpr (call_bot _ _)
  | append _ _ ih _ => exact ih

theorem kRel_sat (S : Value) : CandidateTowerProbe.Sat (kRel S) :=
  ⟨kRel_laws S, fun _ _ h => kRel_bot S h⟩

theorem kRel_refl_call (S h : Value) : kRel S (call S h) (call S h) :=
  .forward (.inl ⟨ValueEq.refl _, call_bot _ _⟩)

/-- The completion realizes the call over the irrelevant proofs. -/
theorem kRel_realizes (S : Value) : ∀ h h', proofs h h' → kRel S (call S h) (call S h') := by
  rintro h h' ⟨hh | hh, hh' | hh'⟩ <;>
    rw [NeutralCodes.valueEq_eq hh, NeutralCodes.valueEq_eq hh']
  · exact kRel_refl_call S _
  · exact .forward (.inr ⟨ValueEq.refl _, ValueEq.refl _⟩)
  · exact .backward (.inr ⟨ValueEq.refl _, ValueEq.refl _⟩)
  · exact kRel_refl_call S _

/-- The class of the minor: the minor and the stuck call. -/
def Cls (S x : Value) : Prop := ValueEq x minorV ∨ ValueEq x (call S stuckMajor)

theorem cls_congr {S x y : Value} (h : ValueEq x y) : Cls S x ↔ Cls S y := by
  rw [NeutralCodes.valueEq_eq h]

theorem kEdge_cls {S x y : Value} (h : kEdge S x y) : Cls S x ∧ Cls S y :=
  ⟨.inl (h.1.trans (reflV_call S)), .inr h.2⟩

theorem kRel_cls {S x y : Value} (h : kRel S x y) : Cls S x ↔ Cls S y := by
  induction h with
  | forward h =>
      rcases h with ⟨he, _⟩ | he
      · exact cls_congr he
      · exact ⟨fun _ => (kEdge_cls he).2, fun _ => (kEdge_cls he).1⟩
  | backward h =>
      rcases h with ⟨he, _⟩ | he
      · exact (cls_congr he).symm
      · exact ⟨fun _ => (kEdge_cls he).1, fun _ => (kEdge_cls he).2⟩
  | append _ _ ih ig => exact ih.trans ig

theorem bottom_not_cls (S : Value) (hS : S .bot) : ¬ Cls S bottom := by
  rintro (h | h)
  · have hm : minorV (.spine 1 []) := NeutralPER.neutralAtom_observed 1
    have hb := (h _).mpr hm
    cases hb
  · have hb := (h _).mpr (GuardedNeutralBoundary.atom_application_observed 7 S hS)
    cases hb

/-- **Repair.** The K-edge completion is a saturated PER that realizes the
call over irrelevant proofs, is not head-separating, and does not relate the
minor with the bottom value. -/
theorem k_completion_repairs (S : Value) (hS : S .bot) :
    CandidateTowerProbe.Sat (kRel S) ∧
    (∀ h h', proofs h h' → kRel S (call S h) (call S h')) ∧
    ¬ HeadSeparating (kRel S) ∧ ¬ kRel S minorV bottom := by
  refine ⟨kRel_sat S, kRel_realizes S, fun hN => stuck_j_boundary_congr S hS _ hN
    (kRel_realizes S), fun h => ?_⟩
  exact bottom_not_cls S hS ((kRel_cls h).mp (.inl (ValueEq.refl _)))

end Rcic.Declarative.Ann.LR3.EqKRepair
