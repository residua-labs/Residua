import rcic.RcicAnnLR3GuardedKernel

/-!
# Constructive gluing of type-directed reflected elements

The two branches may have different reified values. Their conditional value
gives an actual element of the existing guarded carrier, without an equality
between branch erasures or a decision of the guard. The reification equations
and the PER law are branchwise and conjunctive.

This is the gluing operation used after branch reflection has been constructed;
it does not claim to construct a missing branch reflector. In particular the
membership hypotheses below concern already constructed elements, not a new
interface asserted to be inhabited. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedEtaGluing

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER NeutralDataFamily StratifiedCandidates TaggedSaturatedTower

universe u v

/-- Reification into the existing raw semantic language. -/
def reify {k : Nat} (K : Kernel.{u} k) (x : K.Element) : Value := K.erase x

/-- Branch erasures need not agree: the guard is retained in their value. -/
def glue (G : Prop) {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (m : M.Element) (f : F.Element) : GuardedKernel.Element G M F where
  value := GuardedKernel.conditionalValue G (reify M m) (reify F f)
  yes := fun _ => m
  no := fun _ => f
  yes_image := fun h => (GuardedKernel.conditionalValue_true G _ _ h).symm
  no_image := fun h => (GuardedKernel.conditionalValue_false G _ _ h).symm

theorem glue_yes {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (m : M.Element) (f : F.Element) (hG : G) :
    (glue G m f).yes hG = m := rfl

theorem glue_no {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (m : M.Element) (f : F.Element) (hG : ¬ G) :
    (glue G m f).no hG = f := rfl

theorem glue_reify {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : GuardedKernel.TypeImage G M F) (m : M.Element) (f : F.Element) :
    reify (GuardedKernel.kernel G M F I) (glue G m f) =
      GuardedKernel.conditionalValue G (reify M m) (reify F f) := rfl

theorem glue_reify_true {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : GuardedKernel.TypeImage G M F) (m : M.Element) (f : F.Element) (hG : G) :
    ValueEq (reify (GuardedKernel.kernel G M F I) (glue G m f)) (reify M m) :=
  GuardedKernel.conditionalValue_true G _ _ hG

theorem glue_reify_false {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : GuardedKernel.TypeImage G M F) (m : M.Element) (f : F.Element) (hG : ¬ G) :
    ValueEq (reify (GuardedKernel.kernel G M F I) (glue G m f)) (reify F f) :=
  GuardedKernel.conditionalValue_false G _ _ hG

/-- The semantic relation retains both implications, with no branch selection. -/
theorem glue_relation_iff {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (m m' : M.Element) (f f' : F.Element) :
    GuardedKernel.Relation (glue G m f) (glue G m' f') ↔
      (G → M.per.relation m m') ∧ (¬ G → F.per.relation f f') := Iff.rfl

theorem glue_member {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (m : M.Element) (f : F.Element)
    (hm : M.per.relation m m) (hf : F.per.relation f f) :
    GuardedKernel.Relation (glue G m f) (glue G m f) :=
  ⟨fun _ => hm, fun _ => hf⟩

/-- Conditional branch membership also suffices; the data already exist. -/
theorem glue_member_conditional {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (m : M.Element) (f : F.Element)
    (hm : G → M.per.relation m m) (hf : ¬ G → F.per.relation f f) :
    GuardedKernel.Relation (glue G m f) (glue G m f) := ⟨hm, hf⟩

theorem glue_transport_true {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : GuardedKernel.TypeImage G M F) (m : M.Element) (f : F.Element) (hG : G) :
    (GuardedKernel.isoTrue I hG).forward (glue G m f) = m := rfl

theorem glue_transport_false {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : GuardedKernel.TypeImage G M F) (m : M.Element) (f : F.Element) (hG : ¬ G) :
    (GuardedKernel.isoFalse I hG).forward (glue G m f) = f := rfl

/-- The existing designated point is one instance of the gluing operation. -/
theorem glue_points (G : Prop) {k : Nat} (M : Kernel.{u} k) (F : Kernel.{v} k)
    (name : Nat) :
    glue G (M.per.point name) (F.per.point name) = GuardedKernel.point G M F name := rfl

end Rcic.Declarative.Ann.LR3.GuardedEtaGluing
