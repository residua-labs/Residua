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

/-- The induction hypothesis emitted at one recursive field: for a
Π-recursive field `Π (y : D'), B` (the family occurring in the codomain),
the function `fun y ↦ g (fapp x y)` recursing into the codomain — the
semantic counterpart of `lamTelescope` in `iotaArgs`; for a directly
recursive field, `g x`.

The λ's domain is the field's own graph domain `sImage pfst x`: when `x`
is a functional graph on `Ed M (den M σ ρ D')` (e.g. `x ∈ piSet …`), the
two agree (`sImage_pfst_of_isFuncOnDep`), so no ambient denotation
environment is needed. -/
def ihAt (g : PSet.{T} → PSet.{T}) : Expr Nat → PSet.{T} → PSet.{T}
  | .pi _ B, x => mkLam (fun y => ihAt g B (fapp x y)) (sImage pfst x)
  | _, x => g x

/-- `ihAt` with the recursion depth given explicitly (the `inner` of
`FieldShape.recursive inner`). -/
def ihAtN (g : PSet.{T} → PSet.{T}) : Nat → PSet.{T} → PSet.{T}
  | 0, x => g x
  | n + 1, x => mkLam (fun y => ihAtN g n (fapp x y)) (sImage pfst x)

/-- The number of leading `pi`s — the recursion depth `ihAt` uses. -/
def ihDepth : Expr Nat → Nat
  | .pi _ B => ihDepth B + 1
  | _ => 0

theorem ihAt_eq_ihAtN (g : PSet.{T} → PSet.{T}) :
    (A : Expr Nat) → ∀ x, ihAt g A x = ihAtN g (ihDepth A) x
  | .pi _ B, x => by
      show mkLam (fun y => ihAt g B (fapp x y)) (sImage pfst x) =
          mkLam (fun y => ihAtN g (ihDepth B) (fapp x y)) (sImage pfst x)
      unfold mkLam
      rw [show (fun a => ordPair a (ihAt g B (fapp x a))) =
          (fun a => ordPair a (ihAtN g (ihDepth B) (fapp x a))) from
        funext fun y => congrArg (ordPair y) (ihAt_eq_ihAtN g B _)]
  | .bvar _, _ => rfl | .sort _, _ => rfl | .const _ _, _ => rfl
  | .app _ _, _ => rfl | .lam _ _, _ => rfl | .letE _ _ _, _ => rfl
  | .lit _, _ => rfl

/-- `ihAt` reads only the field's leading-`pi` depth. -/
theorem ihAt_eq_of_depth {g : PSet.{T} → PSet.{T}} {A A' : Expr Nat}
    (h : ihDepth A = ihDepth A') (x : PSet.{T}) : ihAt g A x = ihAt g A' x := by
  rw [ihAt_eq_ihAtN, ihAt_eq_ihAtN, h]

/-- At a non-`pi` `foldApps` (the `RecHead`/`DirectRec` shape) the IH is
`g x` — needed because the match is stuck on a `foldApps` application. -/
theorem ihAt_foldApps {e : Expr Nat} (he : ∀ D B, e ≠ .pi D B) (g : PSet.{T} → PSet.{T}) :
    (args : List (Expr Nat)) → ∀ x, ihAt g (foldApps e args) x = g x
  | [], x => by
      show ihAt g e x = g x
      cases e with
      | pi D B => exact absurd rfl (he D B)
      | _ => rfl
  | a :: as, x =>
      ihAt_foldApps (e := .app e a) (fun _ _ h => Expr.noConfusion h) g as x

/-- `ihDepth` of a `foldApps` whose head is not `pi` is `0`. -/
theorem ihDepth_foldApps {e : Expr Nat} (he : ∀ D B, e ≠ .pi D B) :
    (args : List (Expr Nat)) → ihDepth (foldApps e args) = 0
  | [] => by
      show ihDepth e = 0
      cases e with
      | pi D B => exact absurd rfl (he D B)
      | _ => rfl
  | a :: as => ihDepth_foldApps (e := .app e a) (fun _ _ h => Expr.noConfusion h) as

/-- A field of nonzero `ihDepth` is a literal `pi`. -/
theorem ihDepth_ne_zero {A : Expr Nat} (h : ihDepth A ≠ 0) : ∃ D B, A = .pi D B :=
  match A, h with
  | .pi D B, _ => ⟨D, B, rfl⟩
  | .bvar _, h => absurd rfl h
  | .sort _, h => absurd rfl h
  | .const _ _, h => absurd rfl h
  | .app _ _, h => absurd rfl h
  | .lam _ _, h => absurd rfl h
  | .letE _ _ _, h => absurd rfl h
  | .lit _, h => absurd rfl h

/-- `mkLam` congruence, pairwise on domain elements (no self-congruence
premise needed). -/
theorem mkLam_congr' {g g' : PSet.{T} → PSet.{T}} {A A' : PSet.{T}}
    (hA : Equiv A A')
    (hgg : ∀ a a', a ∈ A → a' ∈ A' → Equiv a a' → Equiv (g a) (g' a')) :
    Equiv (mkLam g A) (mkLam g' A') := by
  apply ext; intro p; constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hij⟩ := hA.exists_mem_left i
    refine ⟨j, Equiv.trans ?_ hi⟩
    exact (ordPair_congr hij (hgg _ _ ⟨i, Equiv.refl _⟩ ⟨j, Equiv.refl _⟩ hij)).symm
  · rintro ⟨j, hj⟩
    obtain ⟨i, hij⟩ := hA.exists_mem_right j
    refine ⟨i, Equiv.trans ?_ hj⟩
    exact ordPair_congr hij (hgg _ _ ⟨i, Equiv.refl _⟩ ⟨j, Equiv.refl _⟩ hij)

/-- The guarded pointwise obligation for `ihAt` congruence across `g`/`g'`:
at a `pi`, `g ≈ g'` at every pair of applications on the two graph
domains; at a non-`pi`, at the value. -/
def ihAtOk (g g' : PSet.{T} → PSet.{T}) : Expr Nat → PSet.{T} → PSet.{T} → Prop
  | .pi _ B, x, x' =>
      ∀ y, y ∈ sImage pfst x → ∀ y', y' ∈ sImage pfst x' → Equiv y y' →
        ihAtOk g g' B (fapp x y) (fapp x' y')
  | _, x, x' => Equiv (g x) (g' x')

/-- `ihAt` congruence: `g ≈ g'` where the emitted λs are read. -/
theorem ihAt_congr {g g' : PSet.{T} → PSet.{T}} :
    (A : Expr Nat) → ∀ {x x' : PSet.{T}}, Equiv x x' →
      ihAtOk g g' A x x' → Equiv (ihAt g A x) (ihAt g' A x')
  | .pi _ B, _, _, hx, h =>
      mkLam_congr' (sImage_congr (fun a a' ha => pfst_congr ha) hx)
        fun a a' ha ha' haa' => ihAt_congr B (fapp_congr hx haa') (h a ha a' ha' haa')
  | .bvar _, _, _, _, h => h
  | .sort _, _, _, _, h => h
  | .const _ _, _, _, _, h => h
  | .app _ _, _, _, _, h => h
  | .lam _ _, _, _, _, h => h
  | .letE _ _ _, _, _, _, h => h
  | .lit _, _, _, _, h => h

/-- `ihAtOk` from a global congruence premise on `g`/`g'`. -/
theorem ihAtOk_of_equiv {g g' : PSet.{T} → PSet.{T}}
    (hg : ∀ v v', Equiv v v' → Equiv (g v) (g' v')) :
    (A : Expr Nat) → ∀ {x x' : PSet.{T}}, Equiv x x' → ihAtOk g g' A x x'
  | .pi _ B, _, _, hx =>
      fun y _ y' _ hyy' => ihAtOk_of_equiv hg B (fapp_congr hx hyy')
  | .bvar _, _, _, hx => hg _ _ hx
  | .sort _, _, _, hx => hg _ _ hx
  | .const _ _, _, _, hx => hg _ _ hx
  | .app _ _, _, _, hx => hg _ _ hx
  | .lam _ _, _, _, hx => hg _ _ hx
  | .letE _ _ _, _, _, hx => hg _ _ hx
  | .lit _, _, _, hx => hg _ _ hx

/-- The guarded pointwise obligation for `ihArgs` congruence across
`g`/`g'`: at each recursive position, `ihAtOk`. -/
def ihArgsOk (g g' : PSet.{T} → PSet.{T}) (f : Nat) :
    List (Expr Nat) → List PSet.{T} → List PSet.{T} → Prop
  | A :: As, x :: xs, x' :: xs' =>
      (occursConst f A = true → ihAtOk g g' A x x') ∧ ihArgsOk g g' f As xs xs'
  | _, _, _ => True

/-- `ihArgsOk` from a global congruence premise on `g`/`g'`. -/
theorem ihArgsOk_of_equiv {g g' : PSet.{T} → PSet.{T}}
    (hg : ∀ v v', Equiv v v' → Equiv (g v) (g' v')) (f : Nat) :
    (As : List (Expr Nat)) → {xs xs' : List PSet.{T}} → LEq xs xs' →
      ihArgsOk g g' f As xs xs'
  | [], _, _, _ => trivial
  | _ :: _, [], [], _ => trivial
  | _ :: _, _ :: _, [], _ => trivial
  | A :: As, _ :: xs, _ :: xs', ⟨hx, hxs⟩ =>
      ⟨fun _ => ihAtOk_of_equiv hg A hx, ihArgsOk_of_equiv hg f As hxs⟩

/-- At a `pi`-typed field whose type mentions the family, `fapp`-applications
on the field's graph domain are transitive members of the major — the
well-founded shield is transparent exactly where `ihAt` calls `g`. This is
the semantic content that the unfolding `recCore_data` needs at Π-recursive
fields; it follows from `x ∈ piSet …` (functionality) plus `MemT x z`. -/
def ihChild (z : PSet.{T}) : Expr Nat → PSet.{T} → Prop
  | .pi _ B, x => ∀ y, y ∈ sImage pfst x → MemT (fapp x y) z ∧ ihChild z B (fapp x y)
  | _, _ => True

/-- `ihChild` at every recursive position of a field list. -/
def ihChildL (f : Nat) (z : PSet.{T}) : List (Expr Nat) → List PSet.{T} → Prop
  | A :: As, x :: xs => (occursConst f A = true → ihChild z A x) ∧ ihChildL f z As xs
  | _, _ => True

theorem ihChild_congr {z x x' : PSet.{T}} (e : Equiv x x') :
    (A : Expr Nat) → ihChild z A x → ihChild z A x'
  | .pi _ B, h => fun y' hy' =>
      have hy : y' ∈ sImage pfst x :=
        mem_congr_right (sImage_congr (fun a a' ha => pfst_congr ha) e).symm hy'
      ⟨MemT.congr_left (fapp_congr e Equiv.rfl) (h y' hy).1,
       ihChild_congr (fapp_congr e Equiv.rfl) B (h y' hy).2⟩
  | .bvar _, _ => trivial | .sort _, _ => trivial | .const _ _, _ => trivial
  | .app _ _, _ => trivial | .lam _ _, _ => trivial | .letE _ _ _, _ => trivial
  | .lit _, _ => trivial

/-- `ihChild` reads the major only through `≈`. -/
theorem ihChild_congr' {z z' : PSet.{T}} (hz : Equiv z z') :
    (A : Expr Nat) → ∀ {x}, ihChild z A x → ihChild z' A x
  | .pi _ B, _, h => fun y hy => ⟨(h y hy).1.congr_right hz, ihChild_congr' hz B (h y hy).2⟩
  | .bvar _, _, _ => trivial | .sort _, _, _ => trivial | .const _ _, _, _ => trivial
  | .app _ _, _, _ => trivial | .lam _ _, _, _ => trivial
  | .letE _ _ _, _, _ => trivial | .lit _, _, _ => trivial

theorem ihChildL_congr (f : Nat) (z : PSet.{T}) : (As : List (Expr Nat)) →
    {xs xs' : List PSet.{T}} → LEq xs xs' → ihChildL f z As xs → ihChildL f z As xs'
  | [], _, _, _, _ => trivial
  | _ :: _, [], [], _, _ => trivial
  | _ :: _, _ :: _, [], _, _ => trivial
  | A :: As, _ :: xs, _ :: xs', ⟨hx, hxs⟩, ⟨hch, hL⟩ =>
      ⟨fun hocc => ihChild_congr hx A (hch hocc), ihChildL_congr f z As hxs hL⟩

theorem ihChildL_congr' {f : Nat} {z z' : PSet.{T}} (hz : Equiv z z') :
    (As : List (Expr Nat)) → (xs : List PSet.{T}) →
    ihChildL f z As xs → ihChildL f z' As xs
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | A :: As, x :: xs, ⟨hch, hL⟩ =>
      ⟨fun hocc => ihChild_congr' hz A (hch hocc), ihChildL_congr' hz As xs hL⟩

/-- At a non-`pi` `foldApps` field, `ihChild` is vacuous. -/
theorem ihChild_foldApps (z : PSet.{T}) {e : Expr Nat} (he : ∀ D B, e ≠ .pi D B) :
    (args : List (Expr Nat)) → ∀ x, ihChild z (foldApps e args) x
  | [], x => by
      show ihChild z e x
      cases e with
      | pi D B => exact absurd rfl (he D B)
      | _ => trivial
  | a :: as, x =>
      ihChild_foldApps z (e := .app e a) (fun _ _ h => Expr.noConfusion h) as x

/-- At a field whose leading-`pi` depth is `0`, `ihChild` is vacuous. -/
theorem ihChild_of_depth0 (z : PSet.{T}) {A : Expr Nat} (h : ihDepth A = 0) (x : PSet.{T}) :
    ihChild z A x := by
  cases A with
  | pi D B => simp [ihDepth] at h
  | _ => trivial

/-- `ihChildL` when every `occursConst`-true field has `ihDepth` `0` —
the `RecHead`/`DirectRec`/`ShapesNorm` discharge. -/
theorem ihChildL_of_depth0 (f : Nat) (z : PSet.{T}) :
    (As : List (Expr Nat)) → (xs : List PSet.{T}) →
    (∀ A, A ∈ As → occursConst f A = true → ihDepth A = 0) → ihChildL f z As xs
  | [], _, _ => trivial
  | A :: As, [], _ => trivial
  | A :: As, x :: xs, h =>
      ⟨fun hocc => ihChild_of_depth0 z (h A (List.mem_cons_self _ _) hocc) x,
       ihChildL_of_depth0 f z As xs (fun B hB => h B (List.mem_cons_of_mem _ hB))⟩

/-- `ihChildL` when no field mentions the family. -/
theorem ihChildL_of_free (f : Nat) (z : PSet.{T}) :
    (As : List (Expr Nat)) → (xs : List PSet.{T}) →
    (∀ A, A ∈ As → occursConst f A = false) → ihChildL f z As xs
  | [], _, _ => trivial
  | A :: As, [], _ => trivial
  | A :: As, x :: xs, h =>
      ⟨fun hocc => by simp [h A (List.mem_cons_self _ _)] at hocc,
       ihChildL_of_free f z As xs (fun B hB => h B (List.mem_cons_of_mem _ hB))⟩

/-- The arguments of a minor: each field, followed for a recursive field (one
whose type mentions the family `f`) by its induction hypothesis `ihAt` —
`g x` at a directly recursive field, the curried `fun y ↦ g (fapp x y)` at
a Π-recursive field. -/
def ihArgs (f : Nat) (g : PSet.{T} → PSet.{T}) : List (Expr Nat) → List PSet.{T} → List PSet.{T}
  | A :: As, x :: xs => if occursConst f A = true then x :: ihAt g A x :: ihArgs f g As xs else x :: ihArgs f g As xs
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
    {xs xs' : List PSet.{T}} → LEq xs xs' → ihArgsOk g g' f As xs xs' →
    LEq (ihArgs f g As xs) (ihArgs f g' As xs')
  | [], [], [], _, _ => trivial
  | [], _ :: _, _ :: _, _, _ => trivial
  | _ :: _, [], [], _, _ => trivial
  | A :: As, x :: xs, x' :: xs', ⟨hx, hxs⟩, hok => by
      have ih := ihArgs_congr f As hxs hok.2
      unfold ihArgs
      split <;> rename_i h
      · exact ⟨hx, ihAt_congr A hx (hok.1 h), ih⟩
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
      have hle : LEq (untup (nfOf fd j) (payload z)) (untup (nfOf fd j) (payload z')) :=
        untup_congr' _ (payload_congr hz)
      exact (fapps_congr (LEq_getD hms j) _).trans
        (fapps_congr_args _ (ihArgs_congr fd.fref _ hle (ihArgsOk_of_equiv hg fd.fref _ hle)))

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

/-- Elements of `untup n t` are transitive members of `t` when `t` is a
tuple and `n` is within bounds. -/
theorem memT_untup {t : PSet.{T}} {ys : List PSet.{T}} (ht : Equiv t (tup ys)) :
    ∀ {n}, n ≤ ys.length → ∀ {x}, x ∈ untup n t → MemT x t
  | 0, _, _, hx => absurd hx (List.not_mem_nil _)
  | n + 1, hn, x, hx => by
      cases ys with
      | nil => exact absurd hn (by simp)
      | cons y ys' =>
          have hx' : x ∈ pfst t :: untup n (psnd t) := hx
          have ht' : Equiv t (ordPair y (tup ys')) := ht
          rcases List.mem_cons.mp hx' with rfl | h
          · exact MemT.congr_left ((pfst_congr ht').trans pfst_pair).symm (MemT.congr_right
              (Relation.TransGen.tail (.single (mem_singleton.mpr Equiv.rfl))
                (mem_pair.mpr (Or.inl Equiv.rfl))) ht'.symm)
          · have hps : Equiv (psnd t) (tup ys') := (psnd_congr ht').trans psnd_pair
            have hxs : MemT x (psnd t) :=
              memT_untup hps (Nat.le_of_succ_le_succ hn) h
            have hpt : MemT (psnd t) t := MemT.congr_left hps.symm (MemT.congr_right
              (Relation.TransGen.tail (.single (mem_pair.mpr (Or.inr Equiv.rfl)))
                (mem_pair.mpr (Or.inr Equiv.rfl))) ht'.symm)
            exact hxs.trans hpt

/-- The payload is a transitive member of the data value. -/
theorem memT_payload {z : PSet.{T}} {j : Nat} {xs : List PSet.{T}}
    (hz : Equiv z (dataVal j xs)) : MemT (payload z) z :=
  MemT.congr_left ((payload_dataVal j xs).symm.trans (payload_congr hz).symm)
    (MemT.congr_right
      (Relation.TransGen.trans
        (Relation.TransGen.tail (.single (mem_pair.mpr (Or.inr Equiv.rfl)))
          (mem_pair.mpr (Or.inr Equiv.rfl)))
        (Relation.TransGen.tail (.single (mem_pair.mpr (Or.inr Equiv.rfl)))
          (mem_pair.mpr (Or.inr Equiv.rfl))))
      hz.symm)

/-- The shielded `g` of `recCore`'s unfolding agrees with `recCore` where
`ihAt` reads it — on the graph-domain applications of a Π-recursive field
whose applications are children of the major (`ihChild`). -/
theorem ihAtOk_shield (M : Interp.{T}) (fd : FamData) (ms : List PSet.{T})
    {z x x' : PSet.{T}} (hxz : MemT x z) (hx : Equiv x x') :
    (A : Expr Nat) → ihChild z A x →
      ihAtOk (fun v => @dite _ (MemT v z) (M.dec _) (fun _ => recCore M fd ms v) (fun _ => pempty))
        (recCore M fd ms) A x x'
  | .pi _ B, hch => fun y hy y' _ hyy' =>
      ihAtOk_shield M fd ms ((hch y hy).1) (fapp_congr hx hyy') B ((hch y hy).2)
  | .bvar _, _ => shield_at hxz hx
  | .sort _, _ => shield_at hxz hx
  | .const _ _, _ => shield_at hxz hx
  | .app _ _, _ => shield_at hxz hx
  | .lam _ _, _ => shield_at hxz hx
  | .letE _ _ _, _ => shield_at hxz hx
  | .lit _, _ => shield_at hxz hx
where
  shield_at {z x x' : PSet.{T}} (hxz : MemT x z) (hx : Equiv x x') :
      Equiv (@dite _ (MemT x z) (M.dec _) (fun _ => recCore M fd ms x) (fun _ => pempty))
        (recCore M fd ms x') := by
    rw [dif_pos hxz]
    exact recCore_resp M fd ms x x' hx

/-- `ihArgsOk` for the shielded-vs-unshielded `g` at a data value. -/
theorem ihArgsOk_shield (M : Interp.{T}) (fd : FamData) (ms : List PSet.{T}) {z : PSet.{T}} :
    (As : List (Expr Nat)) → {xs xs' : List PSet.{T}} → LEq xs xs' →
    (∀ x, x ∈ xs → MemT x z) → ihChildL fd.fref z As xs →
      ihArgsOk (fun v => @dite _ (MemT v z) (M.dec _) (fun _ => recCore M fd ms v) (fun _ => pempty))
        (recCore M fd ms) fd.fref As xs xs'
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], [], _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _, _ => trivial
  | A :: As, _ :: xs, _ :: xs', ⟨hx, hxs⟩, hmem, hch =>
      ⟨fun hocc => ihAtOk_shield M fd ms (hmem _ (List.mem_cons_self _ _)) hx A (hch.1 hocc),
       ihArgsOk_shield M fd ms As hxs (fun y hy => hmem y (List.mem_cons_of_mem _ hy)) hch.2⟩

/-- **At a data value**, the recursor applies minor `j` to the fields and the
recursive values. `ihChildL` is the childness premise that makes the
well-founded shield transparent at Π-recursive fields (`ihChild`); at
fields that are not `pi`-headed it is vacuous (`ihChild_foldApps`, and
`ihChildL_of_fieldsClass` discharges it for `FieldsClass` fields). -/
theorem recCore_data (M : Interp.{T}) (fd : FamData) (ms : List PSet.{T}) {z : PSet.{T}} {j : Nat}
    {xs : List PSet.{T}} (hz : Equiv z (dataVal j xs)) (hj : j < fd.ctors.length) (hl : xs.length = nfOf fd j)
    (hch : ihChildL fd.fref z (ctorFieldsOf fd j) xs) :
    Equiv (recCore M fd ms z) (fapps (ms.getD j pempty) (ihArgs fd.fref (recCore M fd ms) (ctorFieldsOf fd j) xs)) := by
  refine (recCore_resp M fd ms z _ hz).trans ?_
  rw [recCore_eq]
  unfold recBody
  rw [findIdx_eq M _ (tagOf_dataVal j xs) (fun i hi => (ord_inj ((tagOf_dataVal j xs).symm.trans hi)).symm) _ hj]
  have hle : LEq (untup (nfOf fd j) (payload (dataVal j xs))) xs := by
    rw [← hl]
    exact LEq.trans (untup_congr' _ (payload_dataVal j xs)) (untup_tup xs)
  refine fapps_congr_args _ (ihArgs_congr fd.fref _ hle (ihArgsOk_shield M fd ms _ hle ?_ ?_))
  · intro x hx
    exact (memT_untup (payload_dataVal j xs) (Nat.le_of_eq hl.symm) hx).trans
      (memT_payload (Equiv.refl (dataVal j xs)))
  · exact ihChildL_congr fd.fref _ _ hle.symm (ihChildL_congr' hz _ _ hch)

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
