import rcic.RcicF3Ctor

/-!
# F3 S5b-3a: the recursor of a recursive group, by well-founded recursion

Membership is well-founded on `PSet` (`mem_wf`, S1), hence so is its transitive
closure `MemT`. `recCore M fd ms` decodes a data value `dataVal j xs` and
applies minor `j` to its fields, inserting after each recursive field (one
whose type mentions the family) the recursor's value at that field: a call
on a component of the major, so the recursion is well-founded.

- `recCore_resp`: it respects `≈`;
- `recCore_data`: at a data value it is the minor applied to the fields and
  the recursive values (`ihArgs`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- The number of fields of constructor `j`. -/
def nfOf (fd : FamData) (j : Nat) : Nat :=
  match fd.ctors[j]? with
  | some c => c.1.length
  | none => 0

theorem findIdx_congr (M : Interp.{T}) {p p' : Nat → Prop} (h : ∀ i, p i ↔ p' i) :
    ∀ k, findIdx M p k = findIdx M p' k
  | 0 => rfl
  | k + 1 => by
      show (match findIdx M p k with
        | some i => some i
        | none => findIdx.cond' M p k) = (match findIdx M p' k with
        | some i => some i
        | none => findIdx.cond' M p' k)
      rw [findIdx_congr M h k]
      cases findIdx M p' k with
      | some _ => rfl
      | none =>
          show findIdx.cond' M p k = findIdx.cond' M p' k
          unfold findIdx.cond'
          cases M.dec (p k) with
          | isTrue hp =>
              cases M.dec (p' k) with
              | isTrue _ => rfl
              | isFalse hn => exact absurd ((h k).mp hp) hn
          | isFalse hn =>
              cases M.dec (p' k) with
              | isTrue hp => exact absurd ((h k).mpr hp) hn
              | isFalse _ => rfl

theorem untup_congr' (m : Nat) {t t' : PSet.{T}} (h : Equiv t t') : LEq (untup m t) (untup m t') :=
  untup_tup.untup_congr m h

/-! ### well-founded membership -/

/-- Transitive membership. -/
def MemT (x z : PSet.{T}) : Prop := Relation.TransGen elemOf x z

theorem memT_wf : WellFounded (fun x z : PSet.{T} => MemT x z) := mem_wf.transGen

theorem MemT.congr_right {x z z' : PSet.{T}} (h : MemT x z) (e : Equiv z z') : MemT x z' := by
  cases h with
  | single h => exact .single (mem_congr_right e h)
  | tail h hb => exact .tail h (mem_congr_right e hb)

theorem MemT.congr_left {x x' z : PSet.{T}} (e : Equiv x x') (h : MemT x z) : MemT x' z := by
  induction h with
  | single h => exact .single (mem_congr_left e h)
  | tail _ hb ih => exact .tail ih hb

theorem memT_tup : {xs : List PSet.{T}} → {x : PSet.{T}} → x ∈ xs → MemT x (tup xs)
  | x :: xs, y, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact .tail (.single (mem_singleton.mpr Equiv.rfl)) (mem_pair.mpr (Or.inl Equiv.rfl))
      · have h1 : MemT (tup xs) (ordPair x (tup xs)) :=
          .tail (.single (mem_pair.mpr (Or.inr Equiv.rfl))) (mem_pair.mpr (Or.inr Equiv.rfl))
        exact Relation.TransGen.trans (memT_tup h) h1

theorem memT_dataVal {j : Nat} {xs : List PSet.{T}} {x : PSet.{T}} (h : x ∈ xs) : MemT x (dataVal j xs) := by
  have h1 : MemT (tup xs) (ordPair (ord j) (tup xs)) :=
    .tail (.single (mem_pair.mpr (Or.inr Equiv.rfl))) (mem_pair.mpr (Or.inr Equiv.rfl))
  have h2 : MemT (ordPair (ord j) (tup xs)) (dataVal j xs) :=
    .tail (.single (mem_pair.mpr (Or.inr Equiv.rfl))) (mem_pair.mpr (Or.inr Equiv.rfl))
  exact (memT_tup h).trans (h1.trans h2)

/-! ### the recursion -/

/-- The field types of constructor `j`. -/
def ctorFieldsOf (fd : FamData) (j : Nat) : List (Expr Nat) := (fd.ctors.getD j ([], [])).1

theorem nfOf_eq (fd : FamData) (j : Nat) : nfOf fd j = (ctorFieldsOf fd j).length := by
  unfold nfOf ctorFieldsOf
  rw [List.getD_eq_getElem?_getD]
  cases fd.ctors[j]? with
  | none => rfl
  | some c => rfl

/-- The arguments of a minor: each field, followed for a recursive field (one
whose type mentions the family `f`) by `g` at the field. -/
def ihArgs (f : Nat) (g : PSet.{T} → PSet.{T}) : List (Expr Nat) → List PSet.{T} → List PSet.{T}
  | A :: As, x :: xs => if occursConst f A = true then x :: g x :: ihArgs f g As xs else x :: ihArgs f g As xs
  | _, _ => []

/-- One step of the recursor at the major `z`, with `g` for the recursive values. -/
def recBody (M : Interp.{T}) (fd : FamData) (ms : List PSet.{T}) (z : PSet.{T}) (g : PSet.{T} → PSet.{T}) :
    PSet.{T} :=
  match findIdx M (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length with
  | some j => fapps (ms.getD j pempty) (ihArgs fd.fref g (ctorFieldsOf fd j) (untup (nfOf fd j) (payload z)))
  | none => pempty

/-- The recursor's value at a major, for the minors `ms`. -/
noncomputable def recCore (M : Interp.{T}) (fd : FamData) (ms : List PSet.{T}) : PSet.{T} → PSet.{T} :=
  WellFounded.fix memT_wf fun z IH => recBody M fd ms z fun x => @dite _ (MemT x z) (M.dec _) (fun h => IH x h) (fun _ => pempty)

theorem recCore_eq (M : Interp.{T}) (fd : FamData) (ms : List PSet.{T}) (z : PSet.{T}) :
    recCore M fd ms z =
      recBody M fd ms z fun x => @dite _ (MemT x z) (M.dec _) (fun _ => recCore M fd ms x) (fun _ => pempty) :=
  WellFounded.fix_eq _ _ z

theorem ihArgs_congr (f : Nat) {g g' : PSet.{T} → PSet.{T}} : (As : List (Expr Nat)) →
    {xs xs' : List PSet.{T}} → LEq xs xs' → (∀ x x', x' ∈ xs' → Equiv x x' → Equiv (g x) (g' x')) →
    LEq (ihArgs f g As xs) (ihArgs f g' As xs')
  | [], [], [], _, _ => trivial
  | [], _ :: _, _ :: _, _, _ => trivial
  | _ :: _, [], [], _, _ => trivial
  | A :: As, x :: xs, x' :: xs', ⟨hx, hxs⟩, hg => by
      have ih := ihArgs_congr f As hxs fun y y' hy' hy => hg y y' (List.mem_cons_of_mem _ hy') hy
      unfold ihArgs
      split
      · exact ⟨hx, hg x x' (List.mem_cons_self _ _) hx, ih⟩
      · exact ⟨hx, ih⟩

theorem LEq_getD : {ms ms' : List PSet.{T}} → LEq ms ms' → (j : Nat) → Equiv (ms.getD j pempty) (ms'.getD j pempty)
  | [], [], _, _ => Equiv.rfl
  | _ :: _, _ :: _, ⟨h, _⟩, 0 => h
  | _ :: _, _ :: _, ⟨_, hs⟩, j + 1 => LEq_getD hs j

theorem recBody_congr (M : Interp.{T}) (fd : FamData) {ms ms' : List PSet.{T}} (hms : LEq ms ms')
    {z z' : PSet.{T}} (hz : Equiv z z')
    {g g' : PSet.{T} → PSet.{T}} (hg : ∀ x x', Equiv x x' → Equiv (g x) (g' x')) :
    Equiv (recBody M fd ms z g) (recBody M fd ms' z' g') := by
  unfold recBody
  rw [findIdx_congr M (p' := fun j => Equiv (tagOf z') (ord j))
    (fun i => ⟨fun h => (tagOf_congr hz).symm.trans h, fun h => (tagOf_congr hz).trans h⟩)]
  cases findIdx M (fun j => Equiv (tagOf z') (ord j)) fd.ctors.length with
  | none => exact Equiv.rfl
  | some j =>
      exact (fapps_congr (LEq_getD hms j) _).trans
        (fapps_congr_args _ (ihArgs_congr fd.fref _ (untup_congr' _ (payload_congr hz)) fun x x' _ h => hg x x' h))

/-- The recursor's value respects `≈` in the minors and the major. -/
theorem recCore_congr (M : Interp.{T}) (fd : FamData) {ms ms' : List PSet.{T}} (hms : LEq ms ms') (z : PSet.{T}) :
    ∀ z', Equiv z z' → Equiv (recCore M fd ms z) (recCore M fd ms' z') := by
  refine WellFounded.induction memT_wf
    (C := fun z => ∀ z', Equiv z z' → Equiv (recCore M fd ms z) (recCore M fd ms' z')) z ?_
  intro z IH z' hz
  rw [recCore_eq M fd ms z, recCore_eq M fd ms' z']
  refine recBody_congr M fd hms hz fun x x' hx => ?_
  cases h1 : M.dec (MemT x z) with
  | isTrue m1 =>
      have m2 : MemT x' z' := (m1.congr_left hx).congr_right hz
      cases h2 : M.dec (MemT x' z') with
      | isTrue _ => exact IH x m1 x' hx
      | isFalse n2 => exact absurd m2 n2
  | isFalse n1 =>
      cases h2 : M.dec (MemT x' z') with
      | isTrue m2 => exact absurd ((m2.congr_left hx.symm).congr_right hz.symm) n1
      | isFalse _ => exact Equiv.rfl

theorem recCore_resp (M : Interp.{T}) (fd : FamData) (ms : List PSet.{T}) (z : PSet.{T}) :
    ∀ z', Equiv z z' → Equiv (recCore M fd ms z) (recCore M fd ms z') :=
  recCore_congr M fd (LEq.refl ms) z

/-- **At a data value**, the recursor applies minor `j` to the fields and the
recursive values. -/
theorem recCore_data (M : Interp.{T}) (fd : FamData) (ms : List PSet.{T}) {z : PSet.{T}} {j : Nat}
    {xs : List PSet.{T}} (hz : Equiv z (dataVal j xs)) (hj : j < fd.ctors.length) (hl : xs.length = nfOf fd j) :
    Equiv (recCore M fd ms z) (fapps (ms.getD j pempty) (ihArgs fd.fref (recCore M fd ms) (ctorFieldsOf fd j) xs)) := by
  refine (recCore_resp M fd ms z _ hz).trans ?_
  rw [recCore_eq]
  unfold recBody
  rw [findIdx_eq M _ (tagOf_dataVal j xs) (fun i hi => (ord_inj ((tagOf_dataVal j xs).symm.trans hi)).symm) _ hj]
  refine fapps_congr_args _ (ihArgs_congr fd.fref _ ?_ fun x x' hx' hx => ?_)
  · rw [← hl]
    exact LEq.trans (untup_congr' _ (payload_dataVal j xs)) (untup_tup xs)
  · have m : MemT x (dataVal j xs) := (memT_dataVal hx').congr_left hx.symm
    cases h1 : M.dec (MemT x (dataVal j xs)) with
    | isTrue _ => exact recCore_resp M fd ms x x' hx
    | isFalse n => exact absurd m n

theorem findIdx_of_dec {M M' : Interp.{T}} (h : M.dec = M'.dec) (p : Nat → Prop) :
    ∀ k, findIdx M p k = findIdx M' p k
  | 0 => rfl
  | k + 1 => by
      show (match findIdx M p k with
        | some i => some i
        | none => findIdx.cond' M p k) = (match findIdx M' p k with
        | some i => some i
        | none => findIdx.cond' M' p k)
      rw [findIdx_of_dec h p k]
      unfold findIdx.cond'
      rw [h]

/-- The recursor reads the interpretation only through its decision procedure. -/
theorem recCore_of_dec {M M' : Interp.{T}} (h : M.dec = M'.dec) (fd : FamData) (ms : List PSet.{T}) (z : PSet.{T}) :
    recCore M fd ms z = recCore M' fd ms z := by
  refine WellFounded.induction memT_wf (C := fun z => recCore M fd ms z = recCore M' fd ms z) z ?_
  intro z IH
  rw [recCore_eq M fd ms z, recCore_eq M' fd ms z]
  unfold recBody
  rw [findIdx_of_dec h]
  have hg : (fun x => @dite _ (MemT x z) (M.dec _) (fun _ => recCore M fd ms x) (fun _ => pempty)) =
      (fun x => @dite _ (MemT x z) (M'.dec _) (fun _ => recCore M' fd ms x) (fun _ => pempty)) := by
    funext x
    rw [h]
    cases M'.dec (MemT x z) with
    | isTrue hm => exact IH x hm
    | isFalse _ => rfl
  rw [hg]

/-- Without recursive fields the minor's arguments are the fields. -/
theorem ihArgs_free (f : Nat) (g : PSet.{T} → PSet.{T}) : (As : List (Expr Nat)) → (xs : List PSet.{T}) →
    (∀ A, A ∈ As → occursConst f A = false) → xs.length = As.length → ihArgs f g As xs = xs
  | [], [], _, _ => rfl
  | A :: As, x :: xs, h, hl => by
      unfold ihArgs
      rw [h A (List.mem_cons_self _ _), if_neg (by decide),
        ihArgs_free f g As xs (fun B hB => h B (List.mem_cons_of_mem _ hB)) (Nat.succ.inj hl)]

end PSet

end Rcic.F3
