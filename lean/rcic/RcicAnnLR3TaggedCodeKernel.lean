import rcic.RcicAnnLR3SaturatedPiElements
import rcic.RcicAnnLR3SaturatedFamilyNative

/-!
# Heterogeneous interpreted fibres and constructive transport

This internal kernel retains the actual element carrier, its erasure and
its pointed PER. Public tagged codes are constructed in TaggedCarrier;
an arbitrary kernel is not a certified code. Carrier transport retains
both actual type and element images, and never recovers a fibre from
equality of raw type images. Host-universe raising is explicit.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.TaggedSaturatedTower
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements NeutralDataFamily StratifiedCandidates

universe u v w

structure Kernel (k : Nat) where
  Element : Type u
  erase : Element → Value
  per : PointedPER k Element

structure KernelIso {k : Nat} (A : Kernel.{u} k) (B : Kernel.{v} k) where
  forward : A.Element → B.Element
  backward : B.Element → A.Element
  left_inv : ∀ x, backward (forward x) = x
  right_inv : ∀ y, forward (backward y) = y
  type_image : ValueEq A.per.value B.per.value
  element_image : ∀ x, ValueEq (B.erase (forward x)) (A.erase x)
  point_image : ∀ name, forward (A.per.point name) = B.per.point name
  relation : ∀ x y, A.per.relation x y ↔ B.per.relation (forward x) (forward y)

namespace KernelIso

def refl {k : Nat} (A : Kernel.{u} k) : KernelIso A A where
  forward := fun x => x
  backward := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  type_image := ValueEq.refl _
  element_image := fun _ => ValueEq.refl _
  point_image := fun _ => rfl
  relation := fun _ _ => Iff.rfl

def symm {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (e : KernelIso A B) : KernelIso B A where
  forward := e.backward
  backward := e.forward
  left_inv := e.right_inv
  right_inv := e.left_inv
  type_image := e.type_image.symm
  element_image := fun y => by
    have h := e.element_image (e.backward y)
    rw [e.right_inv y] at h
    exact h.symm
  point_image := fun name => by
    rw [← e.point_image name]
    exact e.left_inv (A.per.point name)
  relation := fun y z => by
    have h := e.relation (e.backward y) (e.backward z)
    rw [e.right_inv y, e.right_inv z] at h
    exact h.symm

def trans {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    {C : Kernel.{w} k} (e : KernelIso A B) (f : KernelIso B C) : KernelIso A C where
  forward := fun x => f.forward (e.forward x)
  backward := fun z => e.backward (f.backward z)
  left_inv := fun x => by simp only [f.left_inv, e.left_inv]
  right_inv := fun z => by simp only [e.right_inv, f.right_inv]
  type_image := e.type_image.trans f.type_image
  element_image := fun x => (f.element_image (e.forward x)).trans (e.element_image x)
  point_image := fun name => by
    change f.forward (e.forward (A.per.point name)) = C.per.point name
    rw [e.point_image name, f.point_image name]
  relation := fun x y => (e.relation x y).trans (f.relation (e.forward x) (e.forward y))

end KernelIso

def KernelRelated {k : Nat} (A : Kernel.{u} k) (B : Kernel.{v} k) : Prop :=
  Nonempty (KernelIso A B)

theorem kernelRelated_refl {k : Nat} (A : Kernel.{u} k) : KernelRelated A A :=
  ⟨KernelIso.refl A⟩

theorem kernelRelated_symm {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (h : KernelRelated A B) : KernelRelated B A := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

theorem kernelRelated_trans {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    {C : Kernel.{w} k} (h : KernelRelated A B) (h' : KernelRelated B C) :
    KernelRelated A C := by
  rcases h with ⟨e⟩
  rcases h' with ⟨f⟩
  exact ⟨e.trans f⟩

/-- Host-universe raising changes only the representation of elements. -/
def raiseKernel {k : Nat} (A : Kernel.{u} k) : Kernel.{max u v} k where
  Element := ULift.{v} A.Element
  erase := fun x => A.erase x.down
  per := {
    value := A.per.value
    level := A.per.level
    defined := A.per.defined
    relation := fun x y => A.per.relation x.down y.down
    lawful := ⟨fun h => A.per.lawful.symm h,
      fun h h' => A.per.lawful.trans h h'⟩
    point := fun name => ⟨A.per.point name⟩
    point_member := fun name => A.per.point_member name
    irrelevant := fun hk x y hx hy => A.per.irrelevant hk x.down y.down hx hy }

def raiseIso {k : Nat} (A : Kernel.{u} k) :
    KernelIso A (raiseKernel.{u, v} A) where
  forward := ULift.up
  backward := ULift.down
  left_inv := fun _ => rfl
  right_inv := fun y => by cases y; rfl
  type_image := ValueEq.refl _
  element_image := fun _ => ValueEq.refl _
  point_image := fun _ => rfl
  relation := fun _ _ => Iff.rfl

theorem kernelRelated_raise {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (h : KernelRelated A B) :
    KernelRelated (raiseKernel.{u, w} A) (raiseKernel.{v, w} B) := by
  rcases h with ⟨e⟩
  exact ⟨(raiseIso.{u, w} A).symm.trans (e.trans (raiseIso.{v, w} B))⟩

theorem kernelRelated_point_image {k : Nat} {A : Kernel.{u} k} {B : Kernel.{v} k}
    (h : KernelRelated A B) (name : Nat) :
    ValueEq (A.erase (A.per.point name)) (B.erase (B.per.point name)) := by
  rcases h with ⟨e⟩
  have hp := e.element_image (A.per.point name)
  rw [e.point_image name] at hp
  exact hp.symm

end Rcic.Declarative.Ann.LR3.TaggedSaturatedTower
