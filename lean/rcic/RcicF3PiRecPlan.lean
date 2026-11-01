import rcic.RcicF3PiRecBridge
/-!
# Recursor field plans

Use normalized admission depths, independent of raw type presentations.
The literal marker expressions below are operational descriptors only;
they are never asserted to be types or used in denotation. Reuse the
existing well-founded recursor through its descriptor fields.
This component does not assemble a normalized raw group. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecPlan
universe u v
open Rcic.Declarative

/-- Operational marker with exactly the specified IH depth. -/
def recursiveMarker (f : Nat) : Nat → Expr Nat
  | 0 => .const f []
  | m + 1 => .pi (.sort .zero) (recursiveMarker f m)

def marker (f : Nat) : FieldShape → Expr Nat
  | .nonrecursive => .sort .zero
  | .recursive m => recursiveMarker f m

/-- Every field keeps its value; recursive fields emit the depth-based IH. -/
def args (g : PSet.{u} → PSet.{u}) : List FieldShape → List PSet.{u} → List PSet.{u}
  | .nonrecursive :: ss, x :: xs => x :: args g ss xs
  | .recursive m :: ss, x :: xs => x :: ihAtN g m x :: args g ss xs
  | _, _ => []

/-- The old core consumes only field occurrence/depth, counts and tags. -/
def descriptor (f : Nat) (plan : List (List FieldShape)) : FamData where
  fref := f
  params := []
  indices := []
  resLevel := .succ .zero
  ctors := plan.map (fun ss => (ss.map (marker f), []))
  policy := .anySort

noncomputable def core (M : Interp.{u}) (f : Nat) (plan : List (List FieldShape))
    (ms : List PSet.{u}) : PSet.{u} → PSet.{u} := recCore M (descriptor f plan) ms

/-- The legacy operation reads this plan from raw syntax. This is not
admission's normalized plan. -/
def rawShape (f : Nat) (A : Expr Nat) : FieldShape :=
  if occursConst f A then .recursive (ihDepth A) else .nonrecursive

theorem recursiveMarker_spec (f m : Nat) :
    occursConst f (recursiveMarker f m) = true ∧ ihDepth (recursiveMarker f m) = m := by
  induction m with
  | zero => exact ⟨by simp [recursiveMarker, occursConst], rfl⟩
  | succ m ih => exact ⟨ih.1, congrArg Nat.succ ih.2⟩

/-- Exact adapter to the existing core's argument function. -/
theorem args_markers (f : Nat) (g : PSet.{u} → PSet.{u})
    (ss : List FieldShape) (xs : List PSet.{u}) :
    ihArgs f g (ss.map (marker f)) xs = args g ss xs := by
  induction ss generalizing xs with
  | nil => rfl
  | cons s ss ih =>
    cases xs with
    | nil => cases s <;> rfl
    | cons x xs =>
      cases s with
      | nonrecursive => exact congrArg (List.cons x) (ih xs)
      | recursive m =>
        change (if occursConst f (recursiveMarker f m) = true then
          x :: ihAt g (recursiveMarker f m) x :: ihArgs f g (ss.map (marker f)) xs
          else x :: ihArgs f g (ss.map (marker f)) xs) = _
        rw [(recursiveMarker_spec f m).1, if_pos rfl, ihAt_eq_ihAtN,
          (recursiveMarker_spec f m).2, ih xs]
        rfl

/-- Legacy fidelity at every raw field, including hidden presentations. -/
theorem args_raw (f : Nat) (g : PSet.{u} → PSet.{u})
    (Fs : List (Expr Nat)) (xs : List PSet.{u}) :
    args g (Fs.map (rawShape f)) xs = ihArgs f g Fs xs := by
  induction Fs generalizing xs with
  | nil => rfl
  | cons A Fs ih =>
    cases xs with
    | nil =>
      unfold List.map rawShape
      split <;> rfl
    | cons x xs =>
      unfold List.map rawShape
      split <;> rename_i ho
      · change x :: ihAtN g (ihDepth A) x :: args g (Fs.map (rawShape f)) xs = _
        rw [ihArgs, if_pos ho, ihAt_eq_ihAtN, ih xs]
      · change x :: args g (Fs.map (rawShape f)) xs = _
        rw [ihArgs, if_neg ho, ih xs]

/-- An admitted slot retains its exact field count and constructor index. -/
theorem descriptor_slot (f : Nat) (plan : List (List FieldShape)) (j : Nat)
    (ss : List FieldShape) (hj : plan[j]? = some ss) :
    ctorFieldsOf (descriptor f plan) j = ss.map (marker f) ∧
    nfOf (descriptor f plan) j = ss.length ∧ j < (descriptor f plan).ctors.length := by
  have hc : (descriptor f plan).ctors[j]? = some (ss.map (marker f), []) := by
    simp only [descriptor, List.getElem?_map, hj]
    rfl
  have hf : ctorFieldsOf (descriptor f plan) j = ss.map (marker f) := by
    unfold ctorFieldsOf
    rw [List.getD_eq_getElem?_getD, hc]
    rfl
  refine ⟨hf, ?_, ?_⟩
  · rw [nfOf_eq, hf, List.length_map]
  · exact List.getElem?_eq_some_iff.mp hc |>.1

/-- Well-founded childness at every planned recursive position. -/
def Children (f : Nat) (z : PSet.{u}) (ss : List FieldShape) (xs : List PSet.{u}) : Prop :=
  ihChildL f z (ss.map (marker f)) xs

/-- Elementary composition with the existing recursor unfolding. -/
theorem core_data (M : Interp.{u}) (f : Nat) (plan : List (List FieldShape))
    (ms : List PSet.{u}) {j : Nat} {ss : List FieldShape} (hj : plan[j]? = some ss)
    {xs : List PSet.{u}} {z : PSet.{u}} (hz : Equiv z (dataVal j xs))
    (hl : xs.length = ss.length) (hch : Children f z ss xs) :
    Equiv (core M f plan ms z) (fapps (ms.getD j pempty) (args (core M f plan ms) ss xs)) := by
  have hd := descriptor_slot f plan j ss hj
  have hch' : ihChildL (descriptor f plan).fref z (ctorFieldsOf (descriptor f plan) j) xs := by
    rw [hd.1]
    exact hch
  have h := recCore_data M (descriptor f plan) ms hz hd.2.2 (hl.trans hd.2.1.symm) hch'
  rw [hd.1] at h
  change Equiv (core M f plan ms z)
    (fapps (ms.getD j pempty) (ihArgs f (core M f plan ms) (ss.map (marker f)) xs)) at h
  rw [args_markers] at h
  exact h

/-- Actual product membership at a planned recursive field. The telescope
retains all dependent domains and its recursive result index. -/
def FieldMem (M : Interp.{u}) : FieldShape → PSet.{u} → Prop
  | .nonrecursive, _ => True
  | .recursive m, x => ∃ (I : Type v) (t : RecTel.{u,v} I m) (X : I → PSet.{u}),
      t.DomainsDich ∧ x ∈ Ed M (t.erasedType M X)

/-- Product membership at every recursive field; length mismatches are refused. -/
def FieldsMem (M : Interp.{u}) : List FieldShape → List PSet.{u} → Prop
  | [], [] => True
  | s :: ss, x :: xs => FieldMem.{u,v} M s x ∧ FieldsMem M ss xs
  | _, _ => False

/-- Semantic product membership discharges the operational child condition. -/
theorem children_of_mem (M : Interp.{u}) (f : Nat) (z : PSet.{u})
    (ss : List FieldShape) (xs : List PSet.{u}) (hm : FieldsMem.{u,v} M ss xs)
    (hb : ∀ x, x ∈ xs → MemT x z) : Children f z ss xs := by
  induction ss generalizing xs with
  | nil => cases xs with
    | nil => trivial
    | cons x xs => exact hm.elim
  | cons s ss ih =>
    cases xs with
    | nil => exact hm.elim
    | cons x xs =>
      have ht := ih xs hm.2 (fun y hy => hb y (List.mem_cons_of_mem x hy))
      change (occursConst f (marker f s) = true → ihChild z (marker f s) x) ∧ _
      refine ⟨?_, ht⟩
      cases s with
      | nonrecursive => intro _; trivial
      | recursive m =>
        intro _
        obtain ⟨I, t, X, hd, hx⟩ := hm.1
        exact t.ihChild_of_erased_mem M hd X hx (hb x (List.mem_cons_self x xs))
          (marker f (.recursive m)) (recursiveMarker_spec f m).2

/-- Original raw syntax plan, used only for the compatibility theorem. -/
def rawPlan (fd : FamData) : List (List FieldShape) :=
  fd.ctors.map (fun c => c.1.map (rawShape fd.fref))

/-- Exact one-step compatibility with the legacy recursor on every value. -/
theorem body_raw (M : Interp.{u}) (fd : FamData) (ms : List PSet.{u})
    (z : PSet.{u}) (g : PSet.{u} → PSet.{u}) :
    recBody M (descriptor fd.fref (rawPlan fd)) ms z g = recBody M fd ms z g := by
  have hf (j : Nat) : ctorFieldsOf (descriptor fd.fref (rawPlan fd)) j =
      ((ctorFieldsOf fd j).map (rawShape fd.fref)).map (marker fd.fref) := by
    simp only [ctorFieldsOf, descriptor, rawPlan, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases fd.ctors[j]? <;> rfl
  have hn (j : Nat) : nfOf (descriptor fd.fref (rawPlan fd)) j = nfOf fd j := by
    rw [nfOf_eq, hf, List.length_map, List.length_map, nfOf_eq]
  have hc : (descriptor fd.fref (rawPlan fd)).ctors.length = fd.ctors.length := by
    simp only [descriptor, rawPlan, List.length_map]
  unfold recBody
  rw [hc]
  split
  · rename_i j _
    rw [hn, hf]
    change fapps (ms.getD j pempty)
      (ihArgs fd.fref g (((ctorFieldsOf fd j).map (rawShape fd.fref)).map
        (marker fd.fref)) (untup (nfOf fd j) (payload z))) = _
    rw [args_markers, args_raw]
  · rfl

/-- The complete well-founded operation is exactly legacy-compatible
when supplied with its legacy raw-syntax plan, at every major. -/
theorem core_raw (M : Interp.{u}) (fd : FamData) (ms : List PSet.{u})
    (z : PSet.{u}) : core M fd.fref (rawPlan fd) ms z = recCore M fd ms z := by
  induction z using memT_wf.induction with
  | h z ih =>
    change recCore M (descriptor fd.fref (rawPlan fd)) ms z = recCore M fd ms z
    rw [recCore_eq M (descriptor fd.fref (rawPlan fd)), recCore_eq M fd,
      body_raw]
    congr 1
    funext x
    cases M.dec (MemT x z) with
    | isTrue hx => exact ih x hx
    | isFalse hx => rfl

/-- At an actual constructor, semantic field membership pays both the
length and well-founded child obligations of the recursor equation. -/
theorem core_data_mem (M : Interp.{u}) (f : Nat) (plan : List (List FieldShape))
    (ms : List PSet.{u}) {j : Nat} {ss : List FieldShape} (hj : plan[j]? = some ss)
    {xs : List PSet.{u}} (hm : FieldsMem.{u,v} M ss xs) :
    Equiv (core M f plan ms (dataVal j xs))
      (fapps (ms.getD j pempty) (args (core M f plan ms) ss xs)) := by
  have hl : xs.length = ss.length := by
    clear hj
    induction ss generalizing xs with
    | nil => cases xs with
      | nil => rfl
      | cons x xs => exact hm.elim
    | cons s ss ih => cases xs with
      | nil => exact hm.elim
      | cons x xs => exact congrArg Nat.succ (ih hm.2)
  exact core_data M f plan ms hj Equiv.rfl hl
    (children_of_mem M f (dataVal j xs) ss xs hm (fun _ hx => memT_dataVal hx))

end Rcic.F3.PSet.RecPlan
