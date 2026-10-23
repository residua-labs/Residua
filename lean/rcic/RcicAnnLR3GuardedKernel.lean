import rcic.RcicAnnLR3TaggedSaturatedTower

/-!
# Constructive suspended kernels with retained raw members

The carrier retains a raw value and a coherent section of each conditional
branch. Its PER is the conjunction of the two conditional branch PERs.
No branch is selected and no decision for the guard is used. Under either
guard the carrier is genuinely isomorphic to the corresponding heterogeneous
branch, including type images, member erasure and designated points.

The raw type image remains an explicit certified input with conditional
branch equations. A common-image constructor is supplied, but no common
image of the actual Pi minor and native neutral fallback is asserted.
Exact neutral reflection uses supplied data-producing branch reflectors.
This does not extend the sealed Code/Witness constructors or identify this
implication PER with the disjunctive PER. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.GuardedKernel

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER NeutralDataFamily StratifiedCandidates TaggedSaturatedTower

universe u v

/-- A raw conditional value. Its branch equations are constructive. This
operation alone does not give unconditional reflection of a common value. -/
def conditionalValue (G : Prop) (V W : Value) : Value :=
  fun c => (G → V c) ∧ (¬ G → W c)

theorem conditionalValue_true (G : Prop) (V W : Value) (hG : G) :
    ValueEq (conditionalValue G V W) V := by
  intro c
  exact ⟨fun h => h.1 hG,
    fun h => ⟨fun _ => h, fun hn => False.elim (hn hG)⟩⟩

theorem conditionalValue_false (G : Prop) (V W : Value) (hG : ¬ G) :
    ValueEq (conditionalValue G V W) W := by
  intro c
  exact ⟨fun h => h.2 hG,
    fun h => ⟨fun hp => False.elim (hG hp), fun _ => h⟩⟩

/-- Retaining the raw member makes exact reflection possible without
recovering data from conditional existential propositions. -/
structure Element (G : Prop) {k : Nat}
    (M : Kernel.{u} k) (F : Kernel.{v} k) where
  value : Value
  yes : G → M.Element
  no : ¬ G → F.Element
  yes_image : ∀ h, ValueEq (M.erase (yes h)) value
  no_image : ∀ h, ValueEq (F.erase (no h)) value

theorem Element.ext {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k} {x y : Element G M F}
    (hv : x.value = y.value) (hy : x.yes = y.yes) (hn : x.no = y.no) :
    x = y := by
  cases x
  cases y
  cases hv
  cases hy
  cases hn
  rfl

def Relation {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (x y : Element G M F) : Prop :=
  (∀ h, M.per.relation (x.yes h) (y.yes h)) ∧
    (∀ h, F.per.relation (x.no h) (y.no h))

theorem relation_laws (G : Prop) {k : Nat}
    (M : Kernel.{u} k) (F : Kernel.{v} k) :
    RelLaws (@Relation G k M F) := by
  constructor
  · intro x y h
    exact ⟨fun hg => M.per.lawful.symm (h.1 hg),
      fun hg => F.per.lawful.symm (h.2 hg)⟩
  · intro x y z h j
    exact ⟨fun hg => M.per.lawful.trans (h.1 hg) (j.1 hg),
      fun hg => F.per.lawful.trans (h.2 hg) (j.2 hg)⟩

/-- No common erasure of branch points is assumed. The retained raw value
has the required image under each guard. -/
def point (G : Prop) {k : Nat} (M : Kernel.{u} k) (F : Kernel.{v} k)
    (name : Nat) : Element G M F where
  value := conditionalValue G
    (M.erase (M.per.point name)) (F.erase (F.per.point name))
  yes := fun _ => M.per.point name
  no := fun _ => F.per.point name
  yes_image := fun h => (conditionalValue_true G _ _ h).symm
  no_image := fun h => (conditionalValue_false G _ _ h).symm

theorem point_member (G : Prop) {k : Nat}
    (M : Kernel.{u} k) (F : Kernel.{v} k) (name : Nat) :
    Relation (point G M F name) (point G M F name) :=
  ⟨fun _ => M.per.point_member name, fun _ => F.per.point_member name⟩

/-- This is a type-image obligation, not a common-erasure condition on
members and not a raw-image-only choice of their PER. -/
structure TypeImage (G : Prop) {k : Nat}
    (M : Kernel.{u} k) (F : Kernel.{v} k) where
  value : Value
  level : SortMember (some k) value
  defined : TypeDefined value
  yes_image : G → ValueEq value M.per.value
  no_image : ¬ G → ValueEq value F.per.value

def TypeImage.ofCommon (G : Prop) {k : Nat}
    (M : Kernel.{u} k) (F : Kernel.{v} k)
    (h : ValueEq M.per.value F.per.value) : TypeImage G M F where
  value := M.per.value
  level := M.per.level
  defined := M.per.defined
  yes_image := fun _ => ValueEq.refl _
  no_image := fun _ => h

def per (G : Prop) {k : Nat} (M : Kernel.{u} k) (F : Kernel.{v} k)
    (I : TypeImage G M F) : PointedPER k (Element G M F) where
  value := I.value
  level := I.level
  defined := I.defined
  relation := Relation
  lawful := relation_laws G M F
  point := point G M F
  point_member := point_member G M F
  irrelevant := fun hk _ _ hx hy =>
    ⟨fun hg => M.per.irrelevant hk _ _ (hx.1 hg) (hy.1 hg),
      fun hg => F.per.irrelevant hk _ _ (hx.2 hg) (hy.2 hg)⟩

/-- A total data construction from certified type-image data. No decision
for G is a parameter. This is a kernel, not a new sealed Code constructor. -/
def kernel (G : Prop) {k : Nat} (M : Kernel.{u} k) (F : Kernel.{v} k)
    (I : TypeImage G M F) : Kernel.{max u v} k where
  Element := Element G M F
  erase := Element.value
  per := per G M F I

def fromTrue {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (hG : G) (x : M.Element) : Element G M F where
  value := M.erase x
  yes := fun _ => x
  no := fun hn => False.elim (hn hG)
  yes_image := fun _ => ValueEq.refl _
  no_image := fun hn => False.elim (hn hG)

def fromFalse {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (hG : ¬ G) (x : F.Element) : Element G M F where
  value := F.erase x
  yes := fun hp => False.elim (hG hp)
  no := fun _ => x
  yes_image := fun hp => False.elim (hG hp)
  no_image := fun _ => ValueEq.refl _

theorem fromTrue_eval {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k} (hG : G) (x : Element G M F) :
    fromTrue hG (x.yes hG) = x := by
  apply Element.ext
  · exact NeutralCodes.valueEq_eq (x.yes_image hG)
  · funext h
    rfl
  · funext h
    exact False.elim (h hG)

theorem fromFalse_eval {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k} (hG : ¬ G) (x : Element G M F) :
    fromFalse hG (x.no hG) = x := by
  apply Element.ext
  · exact NeutralCodes.valueEq_eq (x.no_image hG)
  · funext h
    exact False.elim (hG h)
  · funext h
    rfl

/-- Genuine heterogeneous carrier, PER, point, type-image and member-image
transport to the true branch. -/
def isoTrue {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : TypeImage G M F) (hG : G) : KernelIso (kernel G M F I) M where
  forward := fun x => x.yes hG
  backward := fromTrue hG
  left_inv := fromTrue_eval hG
  right_inv := fun _ => rfl
  type_image := I.yes_image hG
  element_image := fun x => x.yes_image hG
  point_image := fun _ => rfl
  relation := fun _ _ =>
    ⟨fun h => h.1 hG,
      fun h => ⟨fun _ => h, fun hn => False.elim (hn hG)⟩⟩

/-- Genuine heterogeneous transport to the false branch. -/
def isoFalse {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : TypeImage G M F) (hG : ¬ G) : KernelIso (kernel G M F I) F where
  forward := fun x => x.no hG
  backward := fromFalse hG
  left_inv := fromFalse_eval hG
  right_inv := fun _ => rfl
  type_image := I.no_image hG
  element_image := fun x => x.no_image hG
  point_image := fun _ => rfl
  relation := fun _ _ =>
    ⟨fun h => h.2 hG,
      fun h => ⟨fun hp => False.elim (hG hp), fun _ => h⟩⟩

theorem related_true {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : TypeImage G M F) (hG : G) : KernelRelated (kernel G M F I) M :=
  ⟨isoTrue I hG⟩

theorem related_false {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : TypeImage G M F) (hG : ¬ G) : KernelRelated (kernel G M F I) F :=
  ⟨isoFalse I hG⟩

/-- This hypothesis retains reflection as data. It is not inferred by
choosing elements from conditional existential membership statements. -/
structure Reflector {k : Nat} (K : Kernel.{u} k) where
  reflect : (x : Value) → CandidatePi.Neutral x → K.Element
  member : ∀ x hx, K.per.relation (reflect x hx) (reflect x hx)
  image : ∀ x hx, ValueEq (K.erase (reflect x hx)) x

def reflect {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (rM : Reflector M) (rF : Reflector F)
    (x : Value) (hx : CandidatePi.Neutral x) : Element G M F where
  value := x
  yes := fun _ => rM.reflect x hx
  no := fun _ => rF.reflect x hx
  yes_image := fun _ => rM.image x hx
  no_image := fun _ => rF.image x hx

theorem reflect_member {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (rM : Reflector M) (rF : Reflector F)
    (x : Value) (hx : CandidatePi.Neutral x) :
    Relation (reflect (G := G) rM rF x hx) (reflect (G := G) rM rF x hx) :=
  ⟨fun _ => rM.member x hx, fun _ => rF.member x hx⟩

theorem reflect_image {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (rM : Reflector M) (rF : Reflector F)
    (x : Value) (hx : CandidatePi.Neutral x) :
    (reflect (G := G) rM rF x hx).value = x := rfl

/-- Unconditional exact neutral reflection of the constructed kernel. -/
def reflector {G : Prop} {k : Nat} {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : TypeImage G M F) (rM : Reflector M) (rF : Reflector F) :
    Reflector (kernel G M F I) where
  reflect := reflect rM rF
  member := reflect_member rM rF
  image := fun _ _ => ValueEq.refl _

def nativeNeutralReflector (k name : Nat) :
    Reflector (Code.neutral.{u} k name).kernel where
  reflect := neutralReflect k name
  member := neutral_cr3 k name
  image := fun _ _ => ValueEq.refl _

def propositionReflector (C : CandidatePi.Element) :
    Reflector (Code.proposition.{u} C).kernel where
  reflect := fun x _ => ⟨x⟩
  member := proposition_cr3.{u} C
  image := fun _ _ => ValueEq.refl _

/-- Witnesses for both sides are supplied before any guard proof is used.
This yields exact raw membership without deciding G. -/
theorem reflected_member_exists {G : Prop} {k : Nat}
    {M : Kernel.{u} k} {F : Kernel.{v} k}
    (I : TypeImage G M F) (rM : Reflector M) (rF : Reflector F)
    (x : Value) (hx : CandidatePi.Neutral x) :
    ∃ a : (kernel G M F I).Element,
      (kernel G M F I).per.relation a a ∧
      ValueEq ((kernel G M F I).erase a) x :=
  ⟨reflect rM rF x hx, reflect_member rM rF x hx, ValueEq.refl _⟩

end Rcic.Declarative.Ann.LR3.GuardedKernel
