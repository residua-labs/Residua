import rcic.RcicAnnLR3GuardedKernel

/-!
# Constructive transport of suspended heterogeneous kernels

Guard equivalence and actual branch KernelIso data transport the coherent
sections. The raw member value is retained exactly. The resulting KernelIso
also preserves designated points and requires an actual equation of type
images; this is not inferred from conditional equalities alone. Conditional
type-image constructions have that equation by conditionalValue_congr.
No source conversion invariance or full reader is assumed. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedKernelTransport

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TaggedSaturatedTower GuardedKernel

universe u v w z

theorem conditionalValue_congr {G H : Prop} {V W V' W' : Value}
    (hG : G ↔ H) (hV : ValueEq V V') (hW : ValueEq W W') :
    ValueEq (conditionalValue G V W) (conditionalValue H V' W') := by
  intro c
  constructor
  · intro h
    exact ⟨fun hh => (hV c).mp (h.1 (hG.mpr hh)),
      fun hn => (hW c).mp (h.2 (fun hg => hn (hG.mp hg)))⟩
  · intro h
    exact ⟨fun hg => (hV c).mpr (h.1 (hG.mp hg)),
      fun hn => (hW c).mpr (h.2 (fun hh => hn (hG.mpr hh)))⟩

/-- Conditional sections are transported as retained data. Their stored
raw member value is unchanged, including when neither guard is decided. -/
def map {G H : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    {M' : Kernel.{w} k} {F' : Kernel.{z} k}
    (hG : G ↔ H) (eM : KernelIso M M') (eF : KernelIso F F')
    (x : Element G M F) : Element H M' F' where
  value := x.value
  yes := fun h => eM.forward (x.yes (hG.mpr h))
  no := fun h => eF.forward (x.no (fun hg => h (hG.mp hg)))
  yes_image := fun h =>
    (eM.element_image (x.yes (hG.mpr h))).trans (x.yes_image (hG.mpr h))
  no_image := fun h =>
    (eF.element_image (x.no (fun hg => h (hG.mp hg)))).trans
      (x.no_image (fun hg => h (hG.mp hg)))

theorem map_value {G H : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    {M' : Kernel.{w} k} {F' : Kernel.{z} k}
    (hG : G ↔ H) (eM : KernelIso M M') (eF : KernelIso F F')
    (x : Element G M F) : (map hG eM eF x).value = x.value := rfl

theorem map_left_inv {G H : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    {M' : Kernel.{w} k} {F' : Kernel.{z} k}
    (hG : G ↔ H) (eM : KernelIso M M') (eF : KernelIso F F')
    (x : Element G M F) :
    map hG.symm eM.symm eF.symm (map hG eM eF x) = x := by
  apply Element.ext
  · rfl
  · funext hg
    change eM.backward (eM.forward (x.yes hg)) = x.yes hg
    exact eM.left_inv _
  · funext hg
    change eF.backward (eF.forward (x.no hg)) = x.no hg
    exact eF.left_inv _

theorem map_right_inv {G H : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    {M' : Kernel.{w} k} {F' : Kernel.{z} k}
    (hG : G ↔ H) (eM : KernelIso M M') (eF : KernelIso F F')
    (y : Element H M' F') :
    map hG eM eF (map hG.symm eM.symm eF.symm y) = y := by
  apply Element.ext
  · rfl
  · funext hh
    change eM.forward (eM.backward (y.yes hh)) = y.yes hh
    exact eM.right_inv _
  · funext hh
    change eF.forward (eF.backward (y.no hh)) = y.no hh
    exact eF.right_inv _

theorem map_relation {G H : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    {M' : Kernel.{w} k} {F' : Kernel.{z} k}
    (hG : G ↔ H) (eM : KernelIso M M') (eF : KernelIso F F')
    (x y : Element G M F) :
    Relation x y ↔ Relation (map hG eM eF x) (map hG eM eF y) := by
  constructor
  · intro h
    exact ⟨fun hh => (eM.relation _ _).mp (h.1 (hG.mpr hh)),
      fun hn => (eF.relation _ _).mp (h.2 (fun hg => hn (hG.mp hg)))⟩
  · intro h
    exact ⟨fun hg => (eM.relation _ _).mpr (h.1 (hG.mp hg)),
      fun hn => (eF.relation _ _).mpr (h.2 (fun hh => hn (hG.mpr hh)))⟩

/-- Point erasures may differ between the two branches. Transport uses the
actual point and element-image laws of both branch isomorphisms. -/
theorem map_point {G H : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    {M' : Kernel.{w} k} {F' : Kernel.{z} k}
    (hG : G ↔ H) (eM : KernelIso M M') (eF : KernelIso F F') (name : Nat) :
    map hG eM eF (point G M F name) = point H M' F' name := by
  have hm : ValueEq (M.erase (M.per.point name)) (M'.erase (M'.per.point name)) := by
    have h := eM.element_image (M.per.point name)
    rw [eM.point_image name] at h
    exact h.symm
  have hf : ValueEq (F.erase (F.per.point name)) (F'.erase (F'.per.point name)) := by
    have h := eF.element_image (F.per.point name)
    rw [eF.point_image name] at h
    exact h.symm
  apply Element.ext
  · exact NeutralCodes.valueEq_eq (conditionalValue_congr hG hm hf)
  · funext _
    exact eM.point_image name
  · funext _
    exact eF.point_image name

/-- Congruence retaining heterogeneous carriers, PERs, both images and
designated points. The explicit type-image premise cannot be dropped for
arbitrary TypeImage records merely because both conditional laws hold. -/
def iso {G H : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    {M' : Kernel.{w} k} {F' : Kernel.{z} k}
    (I : TypeImage G M F) (J : TypeImage H M' F')
    (hG : G ↔ H) (eM : KernelIso M M') (eF : KernelIso F F')
    (hV : ValueEq I.value J.value) :
    KernelIso (kernel G M F I) (kernel H M' F' J) where
  forward := map hG eM eF
  backward := map hG.symm eM.symm eF.symm
  left_inv := map_left_inv hG eM eF
  right_inv := map_right_inv hG eM eF
  type_image := hV
  element_image := fun _ => ValueEq.refl _
  point_image := map_point hG eM eF
  relation := map_relation hG eM eF

/-- For the conditional type image, its congruence follows constructively
from guard equivalence and the actual branch type images. -/
def isoConditional {G H : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    {M' : Kernel.{w} k} {F' : Kernel.{z} k}
    (I : TypeImage G M F) (J : TypeImage H M' F')
    (hI : I.value = conditionalValue G M.per.value F.per.value)
    (hJ : J.value = conditionalValue H M'.per.value F'.per.value)
    (hG : G ↔ H) (eM : KernelIso M M') (eF : KernelIso F F') :
    KernelIso (kernel G M F I) (kernel H M' F' J) :=
  iso I J hG eM eF (by
    rw [hI, hJ]
    exact conditionalValue_congr hG eM.type_image eF.type_image)

theorem related {G H : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    {M' : Kernel.{w} k} {F' : Kernel.{z} k}
    (I : TypeImage G M F) (J : TypeImage H M' F') (hG : G ↔ H)
    (hM : KernelRelated M M') (hF : KernelRelated F F')
    (hV : ValueEq I.value J.value) :
    KernelRelated (kernel G M F I) (kernel H M' F' J) := by
  obtain ⟨eM⟩ := hM
  obtain ⟨eF⟩ := hF
  exact ⟨iso I J hG eM eF hV⟩

end Rcic.Declarative.Ann.LR3.GuardedKernelTransport
