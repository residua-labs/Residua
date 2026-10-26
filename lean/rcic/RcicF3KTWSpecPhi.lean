import rcic.RcicF3KTWSpec

/-!
# F3 S7 KT-2b-3b: the semantic one-step operator is W-shaped

`Sem.InPhi` is the `okW` guard read as a *membership condition* on the big
universe: a tuple `xs` is one-step derivable from the candidate set `X` when
plain fields satisfy `nonrecOk`, direct recursive fields are members of `X`
with the required result tuple, and function-recursive fields are graphs in
`piSet (domBig k pre) (fib X k pre)`, `fib` being the `X`-members whose result
tuple is the required one.  `phiSpec L Sm B X` cuts the so-described data
values out of a bound `B`.

`SpecCover` collects the interface a concrete layout owes: every derivable
tuple is in the bound (`covers`), the non-recursive data determine a shape
(`shape`), a shape's small domains match the big domains on its own prefixes
(`domCons`), and non-recursive positions have no branches (`domEmpty`).

- `phiSpec_sub`: `Φ(lift X) ⊆ lift (gphi (L.sig Sm) X)` — choose children
  classwise with the explicit `Choice` premise (`tgt` is the `childAtV`
  canonical value, no quotient representatives);
- `lift_gphi_sub`: `lift (gphi …) ⊆ Φ(lift X)` — a valid tree *is* a
  derivation (`inPhi_of_okW`);
- `wshaped_phiSpec`: `WShaped (phiSpec L Sm B) (L.sig Sm)`;
- `phiSpec_mono`: the operator is monotone in the candidate.

Theory-agnostic (ADR #8005 §7b).  closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w T

namespace PSet

/-! ### `lift` preserves the small set constructors -/

theorem lift_pempty_equiv : Equiv (lift.{u, v} pempty) pempty :=
  ext fun z => ⟨fun ⟨a, _⟩ => a.down.elim, fun h => (not_mem_pempty h).elim⟩

theorem lift_singleton_equiv (a : PSet.{u}) :
    Equiv (lift.{u, v} (singleton a)) (singleton (lift.{u, v} a)) :=
  ext fun z => ⟨fun ⟨_, h⟩ => mem_singleton.mpr h.symm,
    fun h => ⟨ULift.up PUnit.unit, (mem_singleton.mp h).symm⟩⟩

theorem lift_pair_equiv (a b : PSet.{u}) :
    Equiv (lift.{u, v} (pair a b)) (pair (lift.{u, v} a) (lift.{u, v} b)) := by
  apply ext; intro z; constructor
  · rintro ⟨⟨⟨i⟩⟩, h⟩
    cases i with
    | true => exact mem_pair.mpr (Or.inl h.symm)
    | false => exact mem_pair.mpr (Or.inr h.symm)
  · intro h
    rcases mem_pair.mp h with h | h
    · exact ⟨⟨⟨true⟩⟩, h.symm⟩
    · exact ⟨⟨⟨false⟩⟩, h.symm⟩

theorem lift_ordPair_equiv (a b : PSet.{u}) :
    Equiv (lift.{u, v} (ordPair a b)) (ordPair (lift.{u, v} a) (lift.{u, v} b)) :=
  (lift_pair_equiv (singleton a) (pair a b)).trans
    (pair_congr (lift_singleton_equiv a) (lift_pair_equiv a b))

theorem insert_congr {a a' s s' : PSet.{T}} (ha : Equiv a a') (hs : Equiv s s') :
    Equiv (insert a s) (insert a' s') := by
  apply ext; intro z; constructor
  · intro h
    rcases mem_insert.mp h with h | h
    · exact mem_insert.mpr (Or.inl (h.trans ha))
    · exact mem_insert.mpr (Or.inr (mem_congr_right hs h))
  · intro h
    rcases mem_insert.mp h with h | h
    · exact mem_insert.mpr (Or.inl (h.trans ha.symm))
    · exact mem_insert.mpr (Or.inr (mem_congr_right hs.symm h))

theorem lift_insert_equiv (x s : PSet.{u}) :
    Equiv (lift.{u, v} (insert x s)) (insert (lift.{u, v} x) (lift.{u, v} s)) := by
  apply ext; intro z; constructor
  · rintro ⟨⟨i⟩, h⟩
    cases i with
    | none => exact mem_insert.mpr (Or.inl h.symm)
    | some a => exact mem_insert.mpr (Or.inr (mem_lift.mpr ⟨s.Func a, ⟨a, Equiv.refl _⟩, h.symm⟩))
  · intro h
    rcases mem_insert.mp h with h | h
    · exact ⟨⟨none⟩, h.symm⟩
    · obtain ⟨y, ⟨i, hi⟩, hy⟩ := mem_lift.mp h
      exact ⟨⟨some i⟩, (lift_equiv hi).trans hy.symm⟩

theorem lift_ord_equiv : (n : Nat) → Equiv (lift.{u, v} (ord n)) (ord n)
  | 0 => lift_pempty_equiv
  | n + 1 => (lift_insert_equiv (ord n) (ord n)).trans
      (insert_congr (lift_ord_equiv n) (lift_ord_equiv n))

theorem lift_tup_equiv : (xs : List PSet.{u}) →
    Equiv (lift.{u, v} (tup xs)) (tup (xs.map lift.{u, v}))
  | [] => lift_pempty_equiv
  | x :: xs => (lift_ordPair_equiv x (tup xs)).trans
      (ordPair_congr Equiv.rfl (lift_tup_equiv xs))

theorem lift_dataVal_equiv (j : Nat) (xs : List PSet.{u}) :
    Equiv (lift.{u, v} (dataVal j xs)) (dataVal j (xs.map lift.{u, v})) :=
  (lift_ordPair_equiv pempty (ordPair (ord j) (tup xs))).trans
    (ordPair_congr lift_pempty_equiv
      ((lift_ordPair_equiv (ord j) (tup xs)).trans
        (ordPair_congr (lift_ord_equiv j) (lift_tup_equiv xs))))

/-! ### Lowering a function-field branch class through `lift` -/

/-- The index type of a lifted set, lowered. -/
def liftIdxDown : (A : PSet.{u}) → (lift.{u, v} A).Idx → A.Idx
  | mk _ _ => fun i => i.down

theorem liftIdxDown_eq (A : PSet.{u}) (i : (lift.{u, v} A).Idx) :
    Equiv ((lift.{u, v} A).Func i) (lift.{u, v} (A.Func (liftIdxDown A i))) := by
  cases A with | mk α f => exact Equiv.rfl

/-- Map a class of the lifted domain down to a class of the domain. -/
def FBrDown : (A : PSet.{u}) → FBr (lift.{u, v} A) → FBr A
  | mk α f => Quotient.lift (fun i => Quotient.mk (FSetoid (mk α f)) (ULift.down i))
      (fun i j h => Quotient.sound (equiv_of_lift h))

theorem FBrDown_mk (A : PSet.{u}) (i : (lift.{u, v} A).Idx) :
    FBrDown A (Quotient.mk (FSetoid (lift.{u, v} A)) i) =
      Quotient.mk (FSetoid A) (liftIdxDown A i) := by
  cases A with | mk α f => rfl

/-- `graphOf` lifts to a `graphOf` on the lifted domain. -/
theorem graphOf_lift (A : PSet.{u}) (g : FBr A → PSet.{u}) :
    Equiv (lift.{u, v} (graphOf A g))
      (graphOf (lift.{u, v} A) (fun q => lift.{u, v} (g (FBrDown A q)))) := by
  cases A with | mk α f =>
  exact ⟨fun a => ⟨a, lift_ordPair_equiv (f a.down) (g (Quotient.mk (FSetoid (mk α f)) a.down))⟩,
    fun a => ⟨a, lift_ordPair_equiv (f a.down) (g (Quotient.mk (FSetoid (mk α f)) a.down))⟩⟩

/-! ### The canonical child of a class, without quotients -/

/-- Union of the `fapp`-values at indices `≈ y`; equal to `childOf` of the
class containing `y`. -/
def childAtV (A F y : PSet.{T}) : PSet.{T} :=
  sUnion (mk {i : A.Idx // Equiv (A.Func i) y} (fun i => fapp F (A.Func i.1)))

theorem childAtV_mem {A F y z : PSet.{T}} :
    z ∈ childAtV A F y ↔ ∃ i : A.Idx, Equiv (A.Func i) y ∧ z ∈ fapp F (A.Func i) := by
  constructor
  · intro hz
    obtain ⟨t, ⟨⟨i, hi⟩, ht⟩, hzt⟩ := mem_sUnion.mp hz
    exact ⟨i, hi, mem_congr_right ht.symm hzt⟩
  · rintro ⟨i, hi, hzi⟩
    exact mem_sUnion.mpr ⟨fapp F (A.Func i), ⟨⟨i, hi⟩, Equiv.refl _⟩, hzi⟩

theorem childAtV_congr {A F : PSet.{T}} {y y' : PSet.{T}} (h : Equiv y y') :
    Equiv (childAtV A F y) (childAtV A F y') :=
  ext fun z =>
    ⟨fun hz => let ⟨i, hi, hzi⟩ := childAtV_mem.mp hz
      childAtV_mem.mpr ⟨i, hi.trans h, hzi⟩,
     fun hz => let ⟨i, hi, hzi⟩ := childAtV_mem.mp hz
      childAtV_mem.mpr ⟨i, hi.trans h.symm, hzi⟩⟩

theorem childOf_eq_childAtV (A F : PSet.{T}) (i₀ : A.Idx) :
    Equiv (childOf A F (Quotient.mk (FSetoid A) i₀)) (childAtV A F (A.Func i₀)) := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨t, ⟨⟨i, hi⟩, ht⟩, hzt⟩ := mem_sUnion.mp hz
    exact childAtV_mem.mpr ⟨i, Quotient.exact hi, mem_congr_right ht.symm hzt⟩
  · intro hz
    obtain ⟨i, hi, hzi⟩ := childAtV_mem.mp hz
    exact mem_sUnion.mpr ⟨fapp F (A.Func i), ⟨⟨i, Quotient.sound hi⟩, Equiv.refl _⟩, hzi⟩

/-- If every member of `s` is `≈ v` and `v ∈ s`, then `⋃ s ≈ v`. -/
theorem sUnion_equiv_of_const {s v : PSet.{T}}
    (hall : ∀ t, t ∈ s → Equiv t v) (hv : v ∈ s) : Equiv (sUnion s) v := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := mem_sUnion.mp hz
    exact mem_congr_right (hall t ht) hzt
  · intro hz
    exact mem_sUnion.mpr ⟨v, hv, hz⟩

/-! ### Assembling a prefix -/

/-- The `nr` list left after walking `ps`. -/
def nrDrop : List PKind → List PSet.{u} → List PSet.{u}
  | [], nr => nr
  | p :: ps, nr => nrDrop ps (nrTail p nr)

theorem nrDrop_append (ps₁ ps₂ : List PKind) (nr : List PSet.{u}) :
    nrDrop (ps₁ ++ ps₂) nr = nrDrop ps₂ (nrDrop ps₁ nr) := by
  induction ps₁ generalizing nr with
  | nil => rfl
  | cons p ps₁ ih => exact ih (nrTail p nr)

theorem Layout.asm_length {Sh : Type u} (L : Layout Sh) (s : Sh) (h : L.Br s → PSet.{u}) :
    (ps : List PKind) → (k : Nat) → (nr : List PSet.{u}) →
    (L.asm s h ps k nr).length = ps.length
  | [], _, _ => rfl
  | p :: ps, k, nr => congrArg Nat.succ (L.asm_length s h ps (k + 1) (nrTail p nr))

theorem Layout.asm_append {Sh : Type u} (L : Layout Sh) (s : Sh) (h : L.Br s → PSet.{u}) :
    (ps₁ ps₂ : List PKind) → (k : Nat) → (nr : List PSet.{u}) →
    L.asm s h (ps₁ ++ ps₂) k nr =
      L.asm s h ps₁ k nr ++ L.asm s h ps₂ (k + ps₁.length) (nrDrop ps₁ nr)
  | [], _, _, _ => rfl
  | p :: ps₁, ps₂, k, nr => by
      show L.fieldVal s h p k (nr.headD pempty) :: L.asm s h (ps₁ ++ ps₂) (k + 1) (nrTail p nr) =
        (L.fieldVal s h p k (nr.headD pempty) :: L.asm s h ps₁ (k + 1) (nrTail p nr)) ++
          L.asm s h ps₂ (k + (p :: ps₁).length) (nrDrop (p :: ps₁) nr)
      rw [L.asm_append s h ps₁ ps₂ (k + 1) (nrTail p nr), Nat.add_right_comm,
        List.cons_append]
      rfl

/-- The prefix of an assembled list is the assembly of the prefix. -/
theorem Layout.asm_take {Sh : Type u} (L : Layout Sh) (s : Sh) (h : L.Br s → PSet.{u})
    (k : Nat) (nr : List PSet.{u}) :
    (L.asm s h L.kinds 0 nr).take k = L.asm s h (L.kinds.take k) 0 nr := by
  rcases Nat.le_total k L.kinds.length with hk | hk
  · have happ := L.asm_append s h (L.kinds.take k) (L.kinds.drop k) 0 nr
    rw [List.take_append_drop] at happ
    rw [happ, List.take_left' (by rw [L.asm_length, List.length_take]; omega)]
  · rw [List.take_of_length_le (by rw [L.asm_length]; exact hk),
      List.take_of_length_le hk]

/-! ### Field values at the plain positions -/

/-- The values sitting at `plain` positions of a field-value list. -/
def plainVals : List PKind → List PSet.{T} → List PSet.{T}
  | .plain :: ps, x :: xs => x :: plainVals ps xs
  | .direct :: ps, _ :: xs => plainVals ps xs
  | .fn :: ps, _ :: xs => plainVals ps xs
  | _, _ => []

theorem plainVals_plain (ps : List PKind) (x : PSet.{T}) (xs : List PSet.{T}) :
    plainVals (.plain :: ps) (x :: xs) = x :: plainVals ps xs := rfl

theorem plainVals_rec (p : PKind) (hp : p ≠ .plain) (ps : List PKind)
    (x : PSet.{T}) (xs : List PSet.{T}) :
    plainVals (p :: ps) (x :: xs) = plainVals ps xs := by
  cases p with
  | plain => exact absurd rfl hp
  | direct => rfl
  | fn => rfl

theorem LEq_map_lift {xs ys : List PSet.{u}} (h : LEq xs ys) :
    LEq (xs.map lift.{u, v}) (ys.map lift.{u, v}) := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => trivial
    | cons _ _ => exact absurd h id
  | cons x xs ih => cases ys with
    | nil => exact absurd h id
    | cons y ys => exact ⟨lift_equiv h.1, ih h.2⟩

theorem LEq_take {xs ys : List PSet.{T}} (h : LEq xs ys) :
    ∀ k, LEq (xs.take k) (ys.take k)
  | 0 => trivial
  | k + 1 => by
      cases xs with
      | nil => cases ys with
        | nil => trivial
        | cons _ _ => exact absurd h id
      | cons x xs => cases ys with
        | nil => exact absurd h id
        | cons y ys => exact ⟨h.1, LEq_take h.2 k⟩

/-! ### The one-step operator -/

/-- The fibre of `X` at result tuple `t`: `X`-members whose `resTup` is `t`. -/
def Sem.fib (Sm : Sem.{w}) (X : PSet.{w}) (k : Nat)
    (pre : List PSet.{w}) (y : PSet.{w}) : PSet.{w} :=
  sep (fun z => Equiv (Sm.resTup z) (Sm.recTup k pre y)) X

theorem Sem.fib_congr (Sm : Sem.{w}) (X : PSet.{w}) (k : Nat)
    {pre pre' : List PSet.{w}} {y y' : PSet.{w}}
    (hp : LEq pre pre') (hy : Equiv y y') : Equiv (Sm.fib X k pre y) (Sm.fib X k pre' y') :=
  sep_congr
    (fun a b hab h => ((Sm.resTup_congr _ _ hab).symm.trans h).trans
      (Sm.recTup_congr k pre pre' _ _ hp hy))
    (fun a b hab h => ((Sm.resTup_congr _ _ hab).symm.trans h).trans
      (Sm.recTup_congr k pre' pre _ _ (LEq.symm hp) hy.symm))
    Equiv.rfl

theorem Sem.fib_resp (Sm : Sem.{w}) (X : PSet.{w}) (k : Nat)
    (pre : List PSet.{w}) {y y' : PSet.{w}} (hy : Equiv y y') :
    Equiv (Sm.fib X k pre y) (Sm.fib X k pre y') :=
  Sm.fib_congr X k (LEq.refl pre) hy

theorem Sem.fib_sub {Sm : Sem.{w}} {X Y : PSet.{w}} (hXY : Sub X Y) (k : Nat)
    (pre : List PSet.{w}) (y : PSet.{w}) : Sub (Sm.fib X k pre y) (Sm.fib Y k pre y) := by
  intro z hz
  obtain ⟨i, hi, hiz⟩ := mem_sep.mp hz
  obtain ⟨j, hj⟩ := hXY _ ⟨i, hiz⟩
  exact mem_sep.mpr ⟨j,
    ((Sm.resTup_congr _ _ hj).trans ((Sm.resTup_congr _ _ hiz).symm.trans hi)), hj⟩

/-- The `okW` guard read as a membership condition on the big universe. -/
def Sem.InPhi (Sm : Sem.{w}) (X : PSet.{w}) :
    List PKind → List PSet.{w} → Nat → List PSet.{w} → Prop
  | [], [], _, _ => True
  | .plain :: ps, x :: xs, k, pre =>
      Sm.nonrecOk k pre x ∧ Sm.InPhi X ps xs (k + 1) (pre ++ [x])
  | .direct :: ps, x :: xs, k, pre =>
      (x ∈ X ∧ Equiv (Sm.resTup x) (Sm.recTup k pre pempty)) ∧
        Sm.InPhi X ps xs (k + 1) (pre ++ [x])
  | .fn :: ps, x :: xs, k, pre =>
      (x ∈ piSet (Sm.domBig k pre) (Sm.fib X k pre)) ∧
        Sm.InPhi X ps xs (k + 1) (pre ++ [x])
  | _, _, _, _ => False

theorem isFuncOnDep_sub {A : PSet.{T}} {B₁ B₂ : PSet.{T} → PSet.{T}}
    (hsub : ∀ a, Sub (B₁ a) (B₂ a)) {g : PSet.{T}}
    (h : isFuncOnDep A B₁ g) : isFuncOnDep A B₂ g := by
  refine ⟨fun a ha => ?_, fun p hp => ?_, h.2.2⟩
  · obtain ⟨b, hb, hab⟩ := h.1 a ha
    exact ⟨b, hsub _ _ hb, hab⟩
  · obtain ⟨a, ha, b, hb, he⟩ := h.2.1 p hp
    exact ⟨a, ha, b, hsub _ _ hb, he⟩

theorem piSet_sub {A : PSet.{T}} {B₁ B₂ : PSet.{T} → PSet.{T}}
    (hB₁ : ∀ x x', Equiv x x' → Equiv (B₁ x) (B₁ x'))
    (hB₂ : ∀ x x', Equiv x x' → Equiv (B₂ x) (B₂ x'))
    (hsub : ∀ a, Sub (B₁ a) (B₂ a)) : Sub (piSet A B₁) (piSet A B₂) := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := mem_sep.mp hx
  exact mem_piSet_of_dep hB₂ (isFuncOnDep_equiv (Equiv.refl _) hB₂ hix
    (isFuncOnDep_sub hsub hi))

/-- `InPhi` is monotone in the candidate set. -/
theorem Sem.InPhi.mono (Sm : Sem.{w}) {X Y : PSet.{w}} (hXY : Sub X Y) :
    (ps : List PKind) → (xs : List PSet.{w}) → (k : Nat) →
    (pre : List PSet.{w}) → Sm.InPhi X ps xs k pre → Sm.InPhi Y ps xs k pre
  | [], [], _, _, h => h
  | .plain :: ps, x :: xs, k, pre, ⟨hp, h⟩ =>
      ⟨hp, Sem.InPhi.mono Sm hXY ps xs (k + 1) (pre ++ [x]) h⟩
  | .direct :: ps, x :: xs, k, pre, ⟨⟨hx, hr⟩, h⟩ =>
      ⟨⟨hXY _ hx, hr⟩, Sem.InPhi.mono Sm hXY ps xs (k + 1) (pre ++ [x]) h⟩
  | .fn :: ps, x :: xs, k, pre, ⟨hp, h⟩ =>
      ⟨piSet_sub (fun y y' hy => Sm.fib_resp X k pre hy)
        (fun y y' hy => Sm.fib_resp Y k pre hy)
        (fun a => Sm.fib_sub hXY k pre a) _ hp,
        Sem.InPhi.mono Sm hXY ps xs (k + 1) (pre ++ [x]) h⟩
  | p :: _, [], _, _, h => by cases p <;> exact False.elim h
  | [], _ :: _, _, _, h => False.elim h

/-- `InPhi` transports along prefix agreement (the big-domain domains and
result tuples only see `pre` up to `LEq`). -/
theorem Sem.InPhi_congr_pre (Sm : Sem.{w}) {X : PSet.{w}}
    {pre pre' : List PSet.{w}} (hpre : LEq pre pre') :
    (ps : List PKind) → (xs : List PSet.{w}) → (k : Nat) →
    Sm.InPhi X ps xs k pre → Sm.InPhi X ps xs k pre'
  | [], [], _, h => h
  | .plain :: ps, x :: xs, k, ⟨hp, h⟩ =>
      ⟨Sm.nonrecOk_congr _ _ _ _ _ hpre (Equiv.refl _) hp,
        InPhi_congr_pre Sm (LEq_append hpre (LEq.refl _)) ps xs (k + 1) h⟩
  | .direct :: ps, x :: xs, k, ⟨⟨hx, hr⟩, h⟩ =>
      ⟨⟨hx, hr.trans (Sm.recTup_congr _ _ _ _ _ hpre (Equiv.refl _))⟩,
        InPhi_congr_pre Sm (LEq_append hpre (LEq.refl _)) ps xs (k + 1) h⟩
  | .fn :: ps, x :: xs, k, ⟨hp, h⟩ =>
      ⟨by
        obtain ⟨g, hg_dep, hxg⟩ := mem_sep.mp hp
        exact mem_piSet_of_dep (fun y y' hy => Sm.fib_resp X k pre' hy)
          (isFuncOnDep_equiv (Sm.domBig_congr _ _ _ hpre)
            (fun y y' hy => Sm.fib_congr X k hpre hy) hxg hg_dep),
        InPhi_congr_pre Sm (LEq_append hpre (LEq.refl _)) ps xs (k + 1) h⟩
  | p :: _, [], _, h => by cases p <;> exact False.elim h
  | [], _ :: _, _, h => False.elim h

/-- The one-step operator: derivable data values cut out of `B`. -/
def phiSpec {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v})
    (B X : PSet.{max u v}) : PSet.{max u v} :=
  sep (fun z => ∃ xs, Equiv z (dataVal L.tag xs) ∧ Sm.InPhi X L.kinds xs 0 []) B

/-- `phiSpec` only reads the tag and the kinds of the layout. -/
def phiK (tag : Nat) (kinds : List PKind) (Sm : Sem.{w}) (B X : PSet.{w}) : PSet.{w} :=
  sep (fun z => ∃ xs, Equiv z (dataVal tag xs) ∧ Sm.InPhi X kinds xs 0 []) B

theorem phiSpec_eq_phiK {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v}) (B X : PSet.{max u v}) :
    phiSpec L Sm B X = phiK L.tag L.kinds Sm B X := rfl


theorem phiSpec_mono {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v}) (B : PSet.{max u v})
    {X Y : PSet.{max u v}} (hXY : Sub X Y) : Sub (phiSpec L Sm B X) (phiSpec L Sm B Y) := by
  intro z hz
  obtain ⟨i, ⟨xs, hi, hin⟩, hiz⟩ := mem_sep.mp hz
  exact mem_sep.mpr ⟨i, ⟨xs, hi, Sem.InPhi.mono Sm hXY L.kinds xs 0 [] hin⟩, hiz⟩

/-- The non-recursive values consumed by the first `ps` fields, padded like `asm`. -/
def takePlain : List PKind → List PSet.{u} → List PSet.{u}
  | .plain :: ps, nr => nr.headD pempty :: takePlain ps (nrTail .plain nr)
  | .direct :: ps, nr => takePlain ps nr
  | .fn :: ps, nr => takePlain ps nr
  | _, _ => []

/-- How many `plain` fields `ps` has. -/
def plainCount : List PKind → Nat
  | .plain :: ps => plainCount ps + 1
  | _ :: ps => plainCount ps
  | [] => 0

theorem plainCount_append : (ps₁ ps₂ : List PKind) →
    plainCount (ps₁ ++ ps₂) = plainCount ps₁ + plainCount ps₂
  | .plain :: ps₁, ps₂ => (congrArg (· + 1) (plainCount_append ps₁ ps₂)).trans
      (Nat.add_right_comm _ _ _)
  | .direct :: ps₁, ps₂ => plainCount_append ps₁ ps₂
  | .fn :: ps₁, ps₂ => plainCount_append ps₁ ps₂
  | [], _ => (Nat.zero_add _).symm

theorem takePlain_length : (ps : List PKind) → (nr : List PSet.{u}) →
    (takePlain ps nr).length = plainCount ps
  | .plain :: ps, nr => congrArg (· + 1) (takePlain_length ps (nrTail .plain nr))
  | .direct :: ps, nr => takePlain_length ps nr
  | .fn :: ps, nr => takePlain_length ps nr
  | [], _ => rfl

theorem takePlain_take : (ps : List PKind) → (nr : List PSet.{u}) →
    plainCount ps ≤ nr.length → takePlain ps nr = nr.take (plainCount ps)
  | .plain :: ps, x :: xs, h =>
      congrArg ((x :: xs).headD pempty :: ·)
        (takePlain_take ps xs (Nat.le_of_succ_le_succ h))
  | .direct :: ps, nr, h => takePlain_take ps nr h
  | .fn :: ps, nr, h => takePlain_take ps nr h
  | [], _, _ => rfl
  | .plain :: _, [], h => False.elim (Nat.not_succ_le_zero _ h)

theorem takePlain_append : (ps₁ ps₂ : List PKind) → (nr : List PSet.{u}) →
    takePlain (ps₁ ++ ps₂) nr = takePlain ps₁ nr ++ takePlain ps₂ (nrDrop ps₁ nr)
  | [], _, _ => rfl
  | .plain :: ps₁, ps₂, nr =>
      congrArg (nr.headD pempty :: ·) (takePlain_append ps₁ ps₂ (nrTail .plain nr))
  | .direct :: ps₁, ps₂, nr => takePlain_append ps₁ ps₂ nr
  | .fn :: ps₁, ps₂, nr => takePlain_append ps₁ ps₂ nr

/-- `asm`'s plain entries are `takePlain` of the `nr` list. -/
theorem plainVals_asm {Sh : Type u} (L : Layout Sh) (s : Sh) (h : L.Br s → PSet.{u}) :
    (ps : List PKind) → (k : Nat) → (nr : List PSet.{u}) →
    plainVals ps (L.asm s h ps k nr) = takePlain ps nr
  | .plain :: ps, k, nr => by
      show plainVals (.plain :: ps)
          (L.fieldVal s h .plain k (nr.headD pempty) ::
            L.asm s h ps (k + 1) (nrTail .plain nr)) = _
      rw [plainVals_plain]
      exact congrArg (nr.headD pempty :: ·)
        (plainVals_asm L s h ps (k + 1) (nrTail .plain nr))
  | .direct :: ps, k, nr => by
      show plainVals (.direct :: ps)
          (L.fieldVal s h .direct k (nr.headD pempty) ::
            L.asm s h ps (k + 1) (nrTail .direct nr)) = takePlain (.direct :: ps) nr
      rw [plainVals_rec .direct (fun e => PKind.noConfusion e)]
      exact plainVals_asm L s h ps (k + 1) nr
  | .fn :: ps, k, nr => by
      show plainVals (.fn :: ps)
          (L.fieldVal s h .fn k (nr.headD pempty) ::
            L.asm s h ps (k + 1) (nrTail .fn nr)) = takePlain (.fn :: ps) nr
      rw [plainVals_rec .fn (fun e => PKind.noConfusion e)]
      exact plainVals_asm L s h ps (k + 1) nr
  | [], _, _ => rfl

theorem plainVals_map_lift : (ps : List PKind) → (xs : List PSet.{u}) →
    plainVals ps (xs.map lift.{u, v}) = (plainVals ps xs).map lift.{u, v}
  | .plain :: ps, x :: xs => congrArg (lift.{u, v} x :: ·) (plainVals_map_lift ps xs)
  | .direct :: ps, _ :: xs => plainVals_map_lift ps xs
  | .fn :: ps, _ :: xs => plainVals_map_lift ps xs
  | [], _ => rfl
  | p :: _, [] => by cases p <;> rfl

theorem plainVals_append : (ps₁ ps₂ : List PKind) → (xs₁ xs₂ : List PSet.{T}) →
    xs₁.length = ps₁.length →
    plainVals (ps₁ ++ ps₂) (xs₁ ++ xs₂) = plainVals ps₁ xs₁ ++ plainVals ps₂ xs₂
  | [], _, xs₁, _, hl => by
      cases xs₁ with
      | nil => rfl
      | cons x xs => exact Nat.noConfusion hl
  | p :: ps₁, ps₂, x :: xs₁, xs₂, hl => by
      cases p with
      | plain =>
          rw [List.cons_append, plainVals_plain, List.cons_append, plainVals_plain]
          exact congrArg (x :: ·) (plainVals_append ps₁ ps₂ xs₁ xs₂ (Nat.succ.inj hl))
      | direct =>
          rw [List.cons_append, plainVals_rec .direct (fun e => PKind.noConfusion e),
            List.cons_append, plainVals_rec .direct (fun e => PKind.noConfusion e)]
          exact plainVals_append ps₁ ps₂ xs₁ xs₂ (Nat.succ.inj hl)
      | fn =>
          rw [List.cons_append, plainVals_rec .fn (fun e => PKind.noConfusion e),
            List.cons_append, plainVals_rec .fn (fun e => PKind.noConfusion e)]
          exact plainVals_append ps₁ ps₂ xs₁ xs₂ (Nat.succ.inj hl)

theorem plainVals_length : (ps : List PKind) → (xs : List PSet.{T}) →
    xs.length = ps.length → (plainVals ps xs).length = plainCount ps
  | .plain :: ps, x :: xs, h => congrArg (· + 1)
      (plainVals_length ps xs (Nat.succ.inj h))
  | .direct :: ps, _ :: xs, h => plainVals_length ps xs (Nat.succ.inj h)
  | .fn :: ps, _ :: xs, h => plainVals_length ps xs (Nat.succ.inj h)
  | [], _, _ => rfl
  | _ :: _, [], h => Nat.noConfusion h

theorem LEq_plainVals : (ps : List PKind) → (xs ys : List PSet.{T}) →
    LEq xs ys → LEq (plainVals ps xs) (plainVals ps ys)
  | .plain :: ps, x :: xs, y :: ys, h => ⟨h.1, LEq_plainVals ps xs ys h.2⟩
  | .direct :: ps, _ :: xs, _ :: ys, h => LEq_plainVals ps xs ys h.2
  | .fn :: ps, _ :: xs, _ :: ys, h => LEq_plainVals ps xs ys h.2
  | _, [], [], _ => LEq.refl _
  | _, [], _ :: _, h => False.elim h
  | _ :: _, _ :: _, [], h => False.elim h
  | [], _ :: _, _ :: _, _ => LEq.refl _

/-! ### `InPhi` bookkeeping -/

theorem Sem.InPhi.length (Sm : Sem.{w}) {X : PSet.{w}} :
    (ps : List PKind) → (xs : List PSet.{w}) → (k : Nat) →
    (pre : List PSet.{w}) → Sm.InPhi X ps xs k pre → xs.length = ps.length
  | [], [], _, _, _ => rfl
  | .plain :: ps, _ :: xs, k, pre, ⟨_, h⟩ =>
      congrArg Nat.succ (Sem.InPhi.length Sm ps xs (k + 1) (pre ++ [_]) h)
  | .direct :: ps, _ :: xs, k, pre, ⟨_, h⟩ =>
      congrArg Nat.succ (Sem.InPhi.length Sm ps xs (k + 1) (pre ++ [_]) h)
  | .fn :: ps, _ :: xs, k, pre, ⟨_, h⟩ =>
      congrArg Nat.succ (Sem.InPhi.length Sm ps xs (k + 1) (pre ++ [_]) h)
  | p :: _, [], _, _, h => by cases p <;> exact False.elim h
  | [], _ :: _, _, _, h => False.elim h

/-- The suffix of a derivation is a derivation at its prefix. -/
theorem Sem.InPhi.drop (Sm : Sem.{w}) {X : PSet.{w}}
    {ks : List PKind} {xs : List PSet.{w}}
    (h : Sm.InPhi X ks xs 0 []) :
    ∀ k, Sm.InPhi X (ks.drop k) (xs.drop k) k (xs.take k) := by
  intro k; induction k with
  | zero => simpa using h
  | succ k ih =>
    match hd : ks.drop k with
    | [] =>
      have hxs : xs.drop k = [] := by
        apply List.drop_of_length_le
        have hlen := Sem.InPhi.length Sm ks xs 0 [] h
        have h0 : (ks.drop k).length = 0 := congrArg (·.length) hd
        rw [List.length_drop] at h0
        omega
      have hk1 : ks.drop (k + 1) = [] := by
        apply List.drop_of_length_le
        have h0 : (ks.drop k).length = 0 := congrArg (·.length) hd
        rw [List.length_drop] at h0; omega
      have hx1 : xs.drop (k + 1) = [] := by
        apply List.drop_of_length_le
        have h0 : (xs.drop k).length = 0 := congrArg (·.length) hxs
        rw [List.length_drop] at h0; omega
      rw [hk1, hx1]; trivial
    | p :: rest =>
      obtain ⟨x, xsS', hx⟩ : ∃ x xs', xs.drop k = x :: xs' := by
        refine List.exists_cons_of_ne_nil (fun he => ?_)
        have : Sm.InPhi X (p :: rest) [] k (xs.take k) := he ▸ (hd ▸ ih)
        cases p <;> exact False.elim this
      have hk1 : ks.drop (k + 1) = rest :=
        (List.drop_drop 1 k ks).symm.trans (congrArg (·.drop 1) hd)
      have hx1 : xs.drop (k + 1) = xsS' :=
        (List.drop_drop 1 k xs).symm.trans (congrArg (·.drop 1) hx)
      have ht : xs.take (k + 1) = xs.take k ++ [x] := by
        have hxe : xs = xs.take k ++ x :: xsS' := by
          conv => lhs; rw [← List.take_append_drop k xs, hx]
        have hlen : (xs.take k).length = k := by
          rw [List.length_take]
          have hd' : (xs.drop k).length = xsS'.length + 1 := by
            rw [hx, List.length_cons]
          rw [List.length_drop] at hd'; omega
        conv => lhs; rw [hxe]
        show (xs.take k ++ ([x] ++ xsS')).take (k + 1) = xs.take k ++ [x]
        rw [← List.append_assoc]
        exact List.take_left' (by rw [List.length_append, List.length_singleton, hlen])
      rw [hk1, hx1, ht]
      cases p <;> exact ((hx ▸ (hd ▸ ih))).2

/-- Recursive positions of the telescope. -/
def Layout.isRec {Sh : Type u} (L : Layout Sh) (k : Nat) : Prop :=
  L.kinds[k]? = some .direct ∨ L.kinds[k]? = some .fn

/-- The canonical set-value for a recursive field's class of index `i₀`. -/
def specChildOf {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v})
    (xs : List PSet.{max u v}) (s : Sh) (k : Nat) (i₀ : (L.dom k s).Idx) :
    PSet.{max u v} :=
  match L.kinds[k]? with
  | some .direct => xs.getD k pempty
  | some .fn => childAtV (Sm.domBig k (xs.take k)) (xs.getD k pempty)
      (lift.{u, v} ((L.dom k s).Func i₀))
  | _ => pempty

theorem specChildOf_direct {Sh : Type u} {L : Layout Sh} {Sm : Sem.{max u v}}
    {xs : List PSet.{max u v}} {s : Sh} {k : Nat} {i₀ : (L.dom k s).Idx}
    (hk : L.kinds[k]? = some .direct) :
    specChildOf L Sm xs s k i₀ = xs.getD k pempty := by
  unfold specChildOf; rw [hk]

theorem specChildOf_fn {Sh : Type u} {L : Layout Sh} {Sm : Sem.{max u v}}
    {xs : List PSet.{max u v}} {s : Sh} {k : Nat} {i₀ : (L.dom k s).Idx}
    (hk : L.kinds[k]? = some .fn) :
    specChildOf L Sm xs s k i₀ =
      childAtV (Sm.domBig k (xs.take k)) (xs.getD k pempty)
        (lift.{u, v} ((L.dom k s).Func i₀)) := by
  unfold specChildOf; rw [hk]

/-- What a concrete layout owes for `WShaped` to hold. -/
structure SpecCover {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v})
    (B : PSet.{max u v}) : Prop where
  covers : ∀ (X : PSet.{u}) (xs : List PSet.{max u v}),
    Sm.InPhi (lift.{u, v} X) L.kinds xs 0 [] → dataVal L.tag xs ∈ B
  shape : ∀ (X : PSet.{u}) (xs : List PSet.{max u v}),
    Sm.InPhi (lift.{u, v} X) L.kinds xs 0 [] →
      ∃ s : Sh, LEq (List.map lift.{u, v} (L.nr s)) (plainVals L.kinds xs) ∧
        ∀ k, L.kinds[k]? = some .direct → (L.pt k s).isSome
  domCons : ∀ (s : Sh) (k : Nat) (pre : List PSet.{max u v}), L.isRec k → pre.length = k →
    LEq (List.map lift.{u, v} (takePlain (L.kinds.take k) (L.nr s)))
      (plainVals (L.kinds.take k) pre) →
      Equiv (lift.{u, v} (L.dom k s)) (Sm.domBig k pre)
  domEmpty : ∀ (s : Sh) (k : Nat), ¬ L.isRec k → (L.dom k s).Idx → False

/-! ### Branch children chosen classwise -/

/-- The canonical child of a `piSet`-member at a domain member lands in the fibre. -/
theorem childAtV_mem_fib (Sm : Sem.{w}) {X : PSet.{w}} (k : Nat)
    (pre : List PSet.{w}) {domB F y : PSet.{w}}
    (hF : F ∈ piSet domB (Sm.fib X k pre)) (hy : y ∈ domB) :
    childAtV domB F y ∈ X ∧
      Equiv (Sm.resTup (childAtV domB F y)) (Sm.recTup k pre y) := by
  obtain ⟨j, hj⟩ := hy
  obtain ⟨hch, _⟩ := exists_graph_of_mem_piSet
    (fun y y' hy => Sm.fib_resp X k pre hy) hF
  obtain ⟨i, hi, hic⟩ := mem_sep.mp (hch j)
  have hcv : Equiv (childAtV domB F y)
      (childOf domB F (Quotient.mk (FSetoid domB) j)) :=
    (childAtV_congr hj.symm).trans (childOf_eq_childAtV domB F j).symm
  exact ⟨⟨i, hic.trans hcv.symm⟩,
    ((Sm.resTup_congr _ _ hcv).trans ((Sm.resTup_congr _ _ hic).symm.trans
      (hi.trans (Sm.recTup_congr k pre pre _ _ (LEq.refl pre) hj))))⟩

/-- From the `shape` agreement, the small domain matches `domBig` on the
real prefix. -/
theorem SpecCover.domAt {Sh : Type u} {L : Layout Sh} {Sm : Sem.{max u v}}
    {B : PSet.{max u v}} (cov : SpecCover L Sm B) {X : PSet.{u}}
    {xs : List PSet.{max u v}} (hin : Sm.InPhi (lift.{u, v} X) L.kinds xs 0 [])
    (s : Sh) (hnr0 : LEq (List.map lift.{u, v} (L.nr s)) (plainVals L.kinds xs))
    (k : Nat) :
    LEq (List.map lift.{u, v} (takePlain (L.kinds.take k) (L.nr s)))
      (plainVals (L.kinds.take k) (xs.take k)) := by
  have hlen : xs.length = L.kinds.length := Sem.InPhi.length Sm L.kinds xs 0 [] hin
  have hl1 : (xs.take k).length = (L.kinds.take k).length := by
    rw [List.length_take, List.length_take, hlen]
  have happ : plainVals L.kinds xs =
      plainVals (L.kinds.take k) (xs.take k) ++
        plainVals (L.kinds.drop k) (xs.drop k) := by
    conv => lhs; rw [← List.take_append_drop k L.kinds, ← List.take_append_drop k xs]
    exact plainVals_append _ _ _ _ hl1
  have hP1 : (plainVals (L.kinds.take k) (xs.take k)).length =
      plainCount (L.kinds.take k) := plainVals_length _ _ hl1
  have hnrL : (L.nr s).length = plainCount L.kinds := by
    have h2 := LEq.length hnr0
    rw [List.length_map, plainVals_length L.kinds xs hlen] at h2
    exact h2
  have hle : plainCount (L.kinds.take k) ≤ (L.nr s).length := by
    rw [hnrL]
    conv => rhs; rw [← List.take_append_drop k L.kinds, plainCount_append]
    exact Nat.le_add_right _ _
  have h2 := LEq_take hnr0 (plainCount (L.kinds.take k))
  rw [happ, List.take_left' hP1, ← List.map_take, ← takePlain_take _ _ hle] at h2
  exact h2

/-- For every branch class of the chosen shape, pick a representative child in
`X`.  This is the only place `Choice` is used. -/
theorem SpecCover.ex {Sh : Type u} {L : Layout Sh} {Sm : Sem.{max u v}}
    {B : PSet.{max u v}} (cov : SpecCover L Sm B) (ch : Choice.{u}) {X : PSet.{u}}
    {xs : List PSet.{max u v}} (hin : Sm.InPhi (lift.{u, v} X) L.kinds xs 0 [])
    (s : Sh) (hnr0 : LEq (List.map lift.{u, v} (L.nr s)) (plainVals L.kinds xs)) :
    ∃ i : L.Br s → X.Idx, ∀ (b : L.Br s) (i₀ : (L.dom b.1 s).Idx),
      Quotient.mk (FSetoid (L.dom b.1 s)) i₀ = b.2 →
        Equiv (lift.{u, v} (X.Func (i b))) (specChildOf L Sm xs s b.1 i₀) := by
  have hdrop := Sem.InPhi.drop.{max u v} Sm hin
  have sel : ∀ b : L.Br s, ∃ j : X.Idx, ∀ i₀ : (L.dom b.1 s).Idx,
      Quotient.mk (FSetoid (L.dom b.1 s)) i₀ = b.2 →
        Equiv (lift.{u, v} (X.Func j)) (specChildOf L Sm xs s b.1 i₀) := by
    rintro ⟨k, q⟩
    by_cases hr : L.kinds[k]? = some .direct ∨ L.kinds[k]? = some .fn
    · rcases hr with hk | hk
      · -- `.direct`: the field value itself is the child.
        have hd := hdrop k
        have hhead : (L.kinds.drop k).head? = some .direct := by
          rw [List.head?_drop, hk]
        obtain ⟨rest, hkd⟩ : ∃ rest, L.kinds.drop k = .direct :: rest := by
          obtain ⟨x₀, rest, hx⟩ := List.exists_cons_of_ne_nil
            (l := L.kinds.drop k) fun (e : L.kinds.drop k = []) => by
              rw [e] at hhead; exact Option.noConfusion hhead
          rw [hx] at hhead
          exact ⟨rest, Option.some.inj hhead ▸ hx⟩
        rw [hkd] at hd
        obtain ⟨x, xsS', hx⟩ : ∃ x xs', xs.drop k = x :: xs' := by
          refine List.exists_cons_of_ne_nil (l := xs.drop k) fun (he : xs.drop k = []) => ?_
          exact False.elim ((he ▸ hd) : Sm.InPhi _ (.direct :: rest) [] _ _)
        rw [hx] at hd
        obtain ⟨⟨hxm, _⟩, _⟩ := hd
        obtain ⟨y, ⟨j₀, hj₀⟩, hy⟩ := mem_lift.mp hxm
        have hxk : xs[k]? = some x := by
          rw [← List.head?_drop, hx]; rfl
        have hxd : xs.getD k pempty = x := by
          rw [List.getD_eq_getElem?_getD, hxk]; rfl
        refine ⟨j₀, fun i₀ _ => ?_⟩
        rw [specChildOf_direct hk, hxd]
        exact (lift_equiv.{u, v} hj₀).trans hy.symm
      · -- `.fn`: the canonical child of the representative's class.
        have hd := hdrop k
        have hhead : (L.kinds.drop k).head? = some .fn := by
          rw [List.head?_drop, hk]
        obtain ⟨rest, hkd⟩ : ∃ rest, L.kinds.drop k = .fn :: rest := by
          obtain ⟨x₀, rest, hx⟩ := List.exists_cons_of_ne_nil
            (l := L.kinds.drop k) fun (e : L.kinds.drop k = []) => by
              rw [e] at hhead; exact Option.noConfusion hhead
          rw [hx] at hhead
          exact ⟨rest, Option.some.inj hhead ▸ hx⟩
        rw [hkd] at hd
        obtain ⟨x, xsS', hx⟩ : ∃ x xs', xs.drop k = x :: xs' := by
          refine List.exists_cons_of_ne_nil (l := xs.drop k) fun (he : xs.drop k = []) => ?_
          exact False.elim ((he ▸ hd) : Sm.InPhi _ (.fn :: rest) [] _ _)
        rw [hx] at hd
        obtain ⟨hxpi, _⟩ := hd
        have hxk : xs[k]? = some x := by
          rw [← List.head?_drop, hx]; rfl
        have hxd : xs.getD k pempty = x := by
          rw [List.getD_eq_getElem?_getD, hxk]; rfl
        have hdomC : Equiv (lift.{u, v} (L.dom k s))
            (Sm.domBig k (xs.take k)) :=
          cov.domCons s k (xs.take k) (Or.inr hk)
            (by
              have hlen : xs.length = L.kinds.length :=
                Sem.InPhi.length Sm L.kinds xs 0 [] hin
              rw [List.length_take, hlen]
              exact Nat.min_eq_left (Nat.le_of_lt (List.getElem?_eq_some.mp hk).1))
            (cov.domAt hin s hnr0 k)
        obtain ⟨a, ha⟩ := Quotient.exists_rep q
        have hy0 : lift.{u, v} ((L.dom k s).Func a) ∈ Sm.domBig k (xs.take k) :=
          mem_congr_right hdomC (lift_mem_lift.mpr ⟨a, Equiv.refl _⟩)
        obtain ⟨hm, _⟩ := childAtV_mem_fib Sm k (xs.take k) hxpi hy0
        obtain ⟨y', ⟨j₀, hj₀⟩, hy'⟩ := mem_lift.mp hm
        refine ⟨j₀, fun i₀ hqi => ?_⟩
        rw [specChildOf_fn hk, hxd]
        have hqia : Equiv ((L.dom k s).Func i₀) ((L.dom k s).Func a) :=
          Quotient.exact (hqi.trans ha.symm)
        exact (lift_equiv.{u, v} hj₀).trans
          (hy'.symm.trans (childAtV_congr (lift_equiv.{u, v} hqia)).symm)
    · obtain ⟨i₀, _⟩ := Quotient.exists_rep q
      exact False.elim (cov.domEmpty s k hr i₀)
  have selSet : ∀ b : L.Br s, {j : ULift.{u + 1} X.Idx // ∀ i₀ : (L.dom b.1 s).Idx,
      Quotient.mk (FSetoid (L.dom b.1 s)) i₀ = b.2 →
        Equiv (lift.{u, v} (X.Func j.down)) (specChildOf L Sm xs s b.1 i₀)} :=
    fun b => ch _ (let ⟨j, hj⟩ := sel b; ⟨ULift.up j, hj⟩)
  exact ⟨fun b => (selSet b).1.down, fun b i₀ hq => (selSet b).2 i₀ hq⟩

/-! ### The two walks -/

/-- The field value of `asm` at a direct position is the branch child. -/
theorem Layout.fieldVal_direct {Sh : Type u} (L : Layout Sh) (s : Sh)
    (h : L.Br s → PSet.{u}) (k : Nat) (x : PSet.{u}) (q : FBr (L.dom k s))
    (hq : L.pt k s = some q) :
    L.fieldVal s h .direct k x = h ⟨k, q⟩ := by
  unfold Layout.fieldVal; rw [hq]

/-- The field value of `asm` at a function position is the child graph. -/
theorem Layout.fieldVal_fn {Sh : Type u} (L : Layout Sh) (s : Sh)
    (h : L.Br s → PSet.{u}) (k : Nat) (x : PSet.{u}) :
    L.fieldVal s h .fn k x =
      graphOf (L.dom k s) (fun q => h ⟨k, q⟩) := rfl

/-- The `domCons` antecedent evaluated on the `asm` prefix itself. -/
theorem SpecCover.domAt' {Sh : Type u} {L : Layout Sh} {Sm : Sem.{max u v}}
    {B : PSet.{max u v}} {X : PSet.{u}}
    (s : Sh) {i : L.Br s → X.Idx} {ps done : List PKind} {nrs : List PSet.{u}}
    {pre : List PSet.{max u v}}
    (hk : L.kinds = done ++ ps) (hnr : nrs = nrDrop done (L.nr s))
    (hpre : LEq (List.map lift.{u, v}
      (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s))) pre) :
    LEq (List.map lift.{u, v} (takePlain (L.kinds.take done.length) (L.nr s)))
      (plainVals (L.kinds.take done.length) pre) := by
  have htk : L.kinds.take done.length = done := by
    rw [hk]; exact List.take_left _ _
  rw [htk]
  have h1 : LEq (List.map lift.{u, v} (takePlain done (L.nr s)))
      (plainVals done (List.map lift.{u, v}
        (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s)))) := by
    rw [plainVals_map_lift, plainVals_asm]
    exact LEq.refl _
  exact h1.trans (LEq_plainVals done _ _ hpre)

/-- A one-step derivation decomposes into a lifted `asm`-image and a valid
`okW` guard. -/
theorem SpecCover.walk_le {Sh : Type u} {L : Layout Sh} {Sm : Sem.{max u v}}
    {B : PSet.{max u v}} (cov : SpecCover L Sm B) {X : PSet.{u}}
    {xs : List PSet.{max u v}}
    (s : Sh) (hnr0 : LEq (List.map lift.{u, v} (L.nr s)) (plainVals L.kinds xs))
    (hpt : ∀ k, L.kinds[k]? = some .direct → (L.pt k s).isSome)
    (i : L.Br s → X.Idx)
    (hi : ∀ (b : L.Br s) (i₀ : (L.dom b.1 s).Idx),
      Quotient.mk (FSetoid (L.dom b.1 s)) i₀ = b.2 →
      Equiv (lift.{u, v} (X.Func (i b))) (specChildOf L Sm xs s b.1 i₀)) :
    ∀ (done : List PKind) (ps : List PKind) (nrs : List PSet.{u}),
    L.kinds = done ++ ps →
    nrs = nrDrop done (L.nr s) →
    LEq (List.map lift.{u, v} nrs) (plainVals ps (xs.drop done.length)) →
    LEq (List.map lift.{u, v}
        (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s))) (xs.take done.length) →
    Sm.InPhi (lift.{u, v} X) ps (xs.drop done.length) done.length
      (xs.take done.length) →
    LEq (List.map lift.{u, v}
        (L.asm s (fun b => X.Func (i b)) ps done.length nrs)) (xs.drop done.length) ∧
      L.okW Sm s (fun b => X.Func (i b)) ps done.length nrs
        (List.map lift.{u, v} (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s)))
  | done, [], nrs, hk, hnr, hnrL, hpre, hin => by
      have hlen : (xs.drop done.length).length = 0 :=
        Sem.InPhi.length Sm [] (xs.drop done.length) done.length
          (xs.take done.length) hin
      rw [List.length_eq_zero.mp hlen]
      exact ⟨trivial, trivial⟩
  | done, p :: ps', nrs, hk, hnr, hnrL, hpre, hin => by
    obtain ⟨x, xsS', hxs⟩ : ∃ x xs', xs.drop done.length = x :: xs' := by
      refine List.exists_cons_of_ne_nil fun he => ?_
      rw [he] at hin; cases p <;> exact False.elim hin
    rw [hxs] at hin hnrL ⊢
    have hx1 : xs.drop (done.length + 1) = xsS' :=
      (List.drop_drop 1 done.length xs).symm.trans (congrArg (·.drop 1) hxs)
    have ht : xs.take (done.length + 1) = xs.take done.length ++ [x] := by
      have hxe : xs = xs.take done.length ++ x :: xsS' := by
        conv => lhs; rw [← List.take_append_drop done.length xs, hxs]
      have hlen : (xs.take done.length).length = done.length := by
        rw [List.length_take]
        have hd' : (xs.drop done.length).length = xsS'.length + 1 := by
          rw [hxs, List.length_cons]
        rw [List.length_drop] at hd'; omega
      conv => lhs; rw [hxe]
      show (xs.take done.length ++ ([x] ++ xsS')).take (done.length + 1) =
        xs.take done.length ++ [x]
      rw [← List.append_assoc]
      exact List.take_left' (by rw [List.length_append, List.length_singleton, hlen])
    have hk' : L.kinds[done.length]? = some p := by
      rw [hk, List.getElem?_append_right (Nat.le.refl), Nat.sub_self,
        List.getElem?_cons_zero]
    have hl : (done ++ [p]).length = done.length + 1 := by
      rw [List.length_append, List.length_singleton]
    have hx1' : xs.drop (done ++ [p]).length = xsS' := hl.symm ▸ hx1
    have ht' : xs.take (done ++ [p]).length = xs.take done.length ++ [x] :=
      hl.symm ▸ ht
    have hnrD : nrTail p nrs = nrDrop (done ++ [p]) (L.nr s) := by
      rw [nrDrop_append, ← hnr]; cases p <;> rfl
    have hpreEq : List.map lift.{u, v}
          (L.asm s (fun b => X.Func (i b)) (done ++ [p]) 0 (L.nr s)) =
        List.map lift.{u, v} (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s)) ++
          [lift.{u, v} (L.fieldVal s (fun b => X.Func (i b)) p done.length
            (nrs.headD pempty))] := by
      rw [L.asm_append, Nat.zero_add, List.map_append, ← hnr]; rfl
    cases p with
    | plain =>
      obtain ⟨v, nrs', hnv, hvx, hnrL'⟩ : ∃ v nrs', nrs = v :: nrs' ∧
          Equiv (lift.{u, v} v) x ∧
          LEq (List.map lift.{u, v} nrs') (plainVals ps' xsS') := by
        cases nrs with
        | nil => rw [plainVals_plain] at hnrL; exact absurd hnrL id
        | cons v nrs' =>
          rw [plainVals_plain] at hnrL
          exact ⟨v, nrs', rfl, hnrL.1, hnrL.2⟩
      subst hnv
      have hpre' : LEq (List.map lift.{u, v}
          (L.asm s (fun b => X.Func (i b)) (done ++ [PKind.plain]) 0 (L.nr s)))
          (xs.take (done ++ [PKind.plain]).length) := by
        rw [hpreEq, ht']
        exact LEq_append hpre ⟨hvx, trivial⟩
      have hfok : Sm.nonrecOk done.length
          (List.map lift.{u, v} (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s)))
          (lift.{u, v} ((v :: nrs').headD pempty)) := by
        show Sm.nonrecOk done.length _ (lift.{u, v} v)
        exact Sm.nonrecOk_congr done.length _ _ _ _ hpre.symm hvx.symm hin.1
      have hin' : Sm.InPhi (lift.{u, v} X) ps' (xs.drop (done ++ [PKind.plain]).length)
          (done ++ [PKind.plain]).length (xs.take (done ++ [PKind.plain]).length) :=
        hx1'.symm ▸ (ht'.symm ▸ (hl.symm ▸ hin.2))
      obtain ⟨h1, h2⟩ := SpecCover.walk_le cov s hnr0 hpt i hi
        (done ++ [PKind.plain]) ps' nrs'
        (by rw [hk]; exact (List.append_assoc done [PKind.plain] ps').symm)
        hnrD (hx1'.symm ▸ hnrL') hpre' hin'
      exact ⟨⟨hvx, hl ▸ (hx1' ▸ h1)⟩, hfok, hpreEq ▸ (hl ▸ h2)⟩
    | direct =>
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hpt _ hk')
      obtain ⟨i₀, hqi⟩ := Quotient.exists_rep q
      have hhead : Equiv (lift.{u, v} (X.Func (i ⟨done.length, q⟩))) x := by
        have h1 := hi ⟨done.length, q⟩ i₀ hqi
        rwa [specChildOf_direct hk', List.getD_eq_getElem?_getD,
          show xs[done.length]? = some x from by
            rw [← List.head?_drop, hxs]; rfl] at h1
      have hpre' : LEq (List.map lift.{u, v}
          (L.asm s (fun b => X.Func (i b)) (done ++ [PKind.direct]) 0 (L.nr s)))
          (xs.take (done ++ [PKind.direct]).length) := by
        rw [hpreEq, ht']
        refine LEq_append hpre ⟨?_, trivial⟩
        rw [L.fieldVal_direct _ _ _ _ _ hq]
        exact hhead
      have hnrL' : LEq (List.map lift.{u, v} nrs) (plainVals ps' xsS') := hnrL
      have hfok : Equiv (Sm.resTup
          (lift.{u, v} (X.Func (i ⟨done.length, q⟩))))
          (Sm.recTup done.length
            (List.map lift.{u, v}
              (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s))) pempty) := by
        refine (Sm.resTup_congr _ _ hhead).trans (hin.1.2.trans ?_)
        exact Sm.recTup_congr done.length _ _ _ _ hpre.symm (Equiv.refl _)
      have hin' : Sm.InPhi (lift.{u, v} X) ps' (xs.drop (done ++ [PKind.direct]).length)
          (done ++ [PKind.direct]).length (xs.take (done ++ [PKind.direct]).length) :=
        hx1'.symm ▸ (ht'.symm ▸ (hl.symm ▸ hin.2))
      obtain ⟨h1, h2⟩ := SpecCover.walk_le cov s hnr0 hpt i hi
        (done ++ [PKind.direct]) ps' nrs
        (by rw [hk]; exact (List.append_assoc done [PKind.direct] ps').symm)
        hnrD (hx1'.symm ▸ hnrL') hpre' hin'
      refine ⟨⟨?_, hl ▸ (hx1' ▸ h1)⟩, ?_, hpreEq ▸ (hl ▸ h2)⟩
      · rw [L.fieldVal_direct _ _ _ _ _ hq]
        exact hhead
      · simp only [Layout.fieldOk]
        rw [hq]
        exact hfok
    | fn =>
      have hnrL' : LEq (List.map lift.{u, v} nrs) (plainVals ps' xsS') := hnrL
      have hxk : xs[done.length]? = some x := by
        rw [← List.head?_drop, hxs]; rfl
      have hxd : xs.getD done.length pempty = x := by
        rw [List.getD_eq_getElem?_getD, hxk]; rfl
      have hdomC : Equiv (lift.{u, v} (L.dom done.length s))
          (Sm.domBig done.length (xs.take done.length)) :=
        cov.domCons s done.length (xs.take done.length) (Or.inr hk')
          (by
            have h1 := LEq.length hpre
            rw [List.length_map, L.asm_length] at h1
            exact h1.symm)
          (SpecCover.domAt' (Sm := Sm) (B := B) s hk hnr hpre)
      have hchild (a : (lift.{u, v} (L.dom done.length s)).Idx)
          (b : (Sm.domBig done.length (xs.take done.length)).Idx)
          (hab : Equiv ((lift.{u, v} (L.dom done.length s)).Func a)
            ((Sm.domBig done.length (xs.take done.length)).Func b)) :
          Equiv (lift.{u, v} (X.Func (i ⟨done.length,
              FBrDown _ (Quotient.mk _ a)⟩)))
            (childOf _ x (Quotient.mk _ b)) := by
        rw [FBrDown_mk]
        have h1 := hi ⟨done.length,
          Quotient.mk (FSetoid (L.dom done.length s)) (liftIdxDown _ a)⟩
          (liftIdxDown _ a) rfl
        rw [specChildOf_fn hk', hxd] at h1
        have h2 : Equiv (lift.{u, v} ((L.dom done.length s).Func (liftIdxDown _ a)))
            ((lift.{u, v} (L.dom done.length s)).Func a) :=
          (liftIdxDown_eq _ a).symm
        exact h1.trans
          ((childAtV_congr h2).trans
            ((childAtV_congr hab).trans (childOf_eq_childAtV _ _ b).symm))
      have hc : Equiv (graphOf (lift.{u, v} (L.dom done.length s))
            (fun q => lift.{u, v}
              (X.Func (i ⟨done.length, FBrDown _ q⟩))))
          (graphOf (Sm.domBig done.length (xs.take done.length))
            (childOf _ x)) := by
        refine ⟨fun a => ?_, fun b => ?_⟩
        · obtain ⟨b, hb⟩ := hdomC.exists_mem_left a
          exact ⟨b, ordPair_congr hb (hchild a b hb)⟩
        · obtain ⟨a, ha⟩ := hdomC.exists_mem_right b
          exact ⟨a, ordPair_congr ha (hchild a b ha)⟩
      obtain ⟨_, hgr⟩ := exists_graph_of_mem_piSet
        (fun y y' hy => Sm.fib_resp _ _ _ hy) hin.1
      have hhead : Equiv
          (lift.{u, v} (graphOf (L.dom done.length s)
            (fun q => X.Func (i ⟨done.length, q⟩)))) x := by
        exact (graphOf_lift _ _).trans (hc.trans hgr.symm)
      have hpre' : LEq (List.map lift.{u, v}
          (L.asm s (fun b => X.Func (i b)) (done ++ [PKind.fn]) 0 (L.nr s)))
          (xs.take (done ++ [PKind.fn]).length) := by
        rw [hpreEq, ht']
        refine LEq_append hpre ⟨?_, trivial⟩
        rw [L.fieldVal_fn]
        exact hhead
      have hfok : ∀ i' : (L.dom done.length s).Idx,
          Equiv (Sm.resTup (lift.{u, v}
            (X.Func (i ⟨done.length, Quotient.mk _ i'⟩))))
            (Sm.recTup done.length
              (List.map lift.{u, v}
                (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s)))
              (lift.{u, v} ((L.dom done.length s).Func i'))) := by
        intro i'
        have h1 := hi ⟨done.length, Quotient.mk (FSetoid (L.dom done.length s)) i'⟩
          i' rfl
        rw [specChildOf_fn hk', hxd] at h1
        have hy0 : lift.{u, v} ((L.dom done.length s).Func i') ∈
            Sm.domBig done.length (xs.take done.length) :=
          mem_congr_right hdomC (lift_mem_lift.mpr ⟨i', Equiv.refl _⟩)
        obtain ⟨_, htr⟩ := childAtV_mem_fib Sm done.length (xs.take done.length)
          hin.1 hy0
        exact (Sm.resTup_congr _ _ h1).trans (htr.trans
          (Sm.recTup_congr done.length _ _ _ _ hpre.symm (Equiv.refl _)))
      have hin' : Sm.InPhi (lift.{u, v} X) ps' (xs.drop (done ++ [PKind.fn]).length)
          (done ++ [PKind.fn]).length (xs.take (done ++ [PKind.fn]).length) :=
        hx1'.symm ▸ (ht'.symm ▸ (hl.symm ▸ hin.2))
      obtain ⟨h1, h2⟩ := SpecCover.walk_le cov s hnr0 hpt i hi
        (done ++ [PKind.fn]) ps' nrs
        (by rw [hk]; exact (List.append_assoc done [PKind.fn] ps').symm)
        hnrD (hx1'.symm ▸ hnrL') hpre' hin'
      refine ⟨⟨?_, hl ▸ (hx1' ▸ h1)⟩, ?_, hpreEq ▸ (hl ▸ h2)⟩
      · rw [L.fieldVal_fn]
        exact hhead
      · exact hfok

/-- A valid `okW` guard is a one-step derivation. -/
theorem SpecCover.walk_ge {Sh : Type u} {L : Layout Sh} {Sm : Sem.{max u v}}
    {B : PSet.{max u v}} (cov : SpecCover L Sm B) {X : PSet.{u}}
    (s : Sh) (i : L.Br s → X.Idx) :
    ∀ (done : List PKind) (ps : List PKind) (nrs : List PSet.{u})
      (pre : List PSet.{max u v}),
    L.kinds = done ++ ps →
    nrs = nrDrop done (L.nr s) →
    LEq (List.map lift.{u, v}
        (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s))) pre →
    L.okW Sm s (fun b => X.Func (i b)) ps done.length nrs pre →
    Sm.InPhi (lift.{u, v} X) ps
      (List.map lift.{u, v}
        (L.asm s (fun b => X.Func (i b)) ps done.length nrs))
      done.length pre
  | done, [], nrs, pre, hk, hnr, hpre, hok => trivial
  | done, p :: ps', nrs, pre, hk, hnr, hpre, hok => by
    obtain ⟨hf, hok'⟩ := hok
    have hl : (done ++ [p]).length = done.length + 1 := by
      rw [List.length_append, List.length_singleton]
    have hpreEq : List.map lift.{u, v}
          (L.asm s (fun b => X.Func (i b)) (done ++ [p]) 0 (L.nr s)) =
        List.map lift.{u, v} (L.asm s (fun b => X.Func (i b)) done 0 (L.nr s)) ++
          [lift.{u, v} (L.fieldVal s (fun b => X.Func (i b)) p done.length
            (nrs.headD pempty))] := by
      simp [L.asm_append, Layout.asm, ← hnr]
    have hnrD' : nrDrop (done ++ [p]) (L.nr s) = nrTail p nrs := by
      rw [nrDrop_append, ← hnr]; cases p <;> rfl
    have hin' := SpecCover.walk_ge cov s i (done ++ [p]) ps' (nrTail p nrs)
      (pre ++ [lift.{u, v} (L.fieldVal s (fun b => X.Func (i b)) p done.length
        (nrs.headD pempty))])
      (by rw [hk]; exact (List.append_assoc done [p] ps').symm)
      (by rw [hnrD'])
      (by rw [hpreEq]; exact LEq_append hpre ⟨Equiv.refl _, trivial⟩)
      (hl.symm ▸ hok')
    cases p with
    | plain =>
      exact ⟨hf, hl ▸ hin'⟩
    | direct =>
      simp only [Layout.fieldOk] at hf
      cases hq : L.pt done.length s with
      | none => rw [hq] at hf; exact False.elim hf
      | some q =>
        rw [hq] at hf
        have hmem : lift.{u, v} (X.Func (i ⟨done.length, q⟩)) ∈ lift.{u, v} X :=
          lift_mem_lift.mpr ⟨i ⟨done.length, q⟩, Equiv.refl _⟩
        refine ⟨⟨?_, ?_⟩, hl ▸ hin'⟩
        · rw [L.fieldVal_direct _ _ _ _ _ hq]
          exact hmem
        · rw [L.fieldVal_direct _ _ _ _ _ hq]
          exact hf
    | fn =>
      have hdomC : Equiv (lift.{u, v} (L.dom done.length s))
          (Sm.domBig done.length pre) :=
        cov.domCons s done.length pre (Or.inr (by
          rw [hk, List.getElem?_append_right (Nat.le.refl), Nat.sub_self,
            List.getElem?_cons_zero]))
          (by
            have h1 := LEq.length hpre
            rw [List.length_map, L.asm_length] at h1
            exact h1.symm)
          (SpecCover.domAt' (Sm := Sm) (B := B) s hk hnr hpre)
      have hfunc : isFuncOnDep (Sm.domBig done.length pre)
          (Sm.fib (lift.{u, v} X) done.length pre)
          (lift.{u, v} (graphOf (L.dom done.length s)
            (fun q => X.Func (i ⟨done.length, q⟩)))) := by
        refine ⟨?_, ?_, ?_⟩
        · intro y hy
          obtain ⟨y₀, hy₀, hye⟩ := mem_lift.mp
            (mem_congr_right hdomC.symm hy)
          obtain ⟨i₀, hi₀⟩ := hy₀
          have hyi : Equiv y (lift.{u, v} ((L.dom done.length s).Func i₀)) :=
            hye.trans ((lift_equiv.{u, v} hi₀).symm)
          refine ⟨lift.{u, v} (X.Func (i ⟨done.length,
              Quotient.mk (FSetoid (L.dom done.length s)) i₀⟩)), ?_, ?_⟩
          · obtain ⟨ix, hix⟩ := lift_mem_lift.{u, v}.mpr
                ⟨i ⟨done.length, Quotient.mk _ i₀⟩, Equiv.refl _⟩
            exact mem_sep.mpr ⟨ix,
              (Sm.resTup_congr _ _ hix).trans
                ((hf i₀).trans
                  (Sm.recTup_congr done.length _ _ _ _ (LEq.refl _) hyi.symm)),
              hix⟩
          · exact mem_lift.mpr
              ⟨ordPair ((L.dom done.length s).Func i₀)
                (X.Func (i ⟨done.length, Quotient.mk _ i₀⟩)),
                ⟨i₀, Equiv.refl _⟩,
                (ordPair_congr hyi (Equiv.refl _)).trans
                  (lift_ordPair_equiv _ _).symm⟩
        · intro p hp
          obtain ⟨p', hp'F, hpp⟩ := mem_lift.mp hp
          obtain ⟨i₀, hi₀⟩ := hp'F
          have ha : lift.{u, v} ((L.dom done.length s).Func i₀) ∈
              Sm.domBig done.length pre :=
            mem_congr_right hdomC (lift_mem_lift.mpr ⟨i₀, Equiv.refl _⟩)
          refine ⟨lift.{u, v} ((L.dom done.length s).Func i₀), ha,
            lift.{u, v} (X.Func (i ⟨done.length,
              Quotient.mk (FSetoid (L.dom done.length s)) i₀⟩)), ?_, ?_⟩
          · obtain ⟨ix, hix⟩ := lift_mem_lift.{u, v}.mpr
                ⟨i ⟨done.length, Quotient.mk _ i₀⟩, Equiv.refl _⟩
            exact mem_sep.mpr ⟨ix,
              (Sm.resTup_congr _ _ hix).trans (hf i₀), hix⟩
          · exact hpp.trans ((lift_equiv.{u, v} hi₀).symm.trans
              (lift_ordPair_equiv _ _))
        · intro a b b' hab hab'
          obtain ⟨p₁, ⟨i₁, hp₁⟩, hab₁⟩ := mem_lift.mp hab
          obtain ⟨p₂, ⟨i₂, hp₂⟩, hab₂⟩ := mem_lift.mp hab'
          have e₁ := hab₁.trans ((lift_equiv.{u, v} hp₁).symm.trans
            (lift_ordPair_equiv _ _))
          have e₂ := hab₂.trans ((lift_equiv.{u, v} hp₂).symm.trans
            (lift_ordPair_equiv _ _))
          obtain ⟨ha₁, hb₁⟩ := ordPair_equiv e₁
          obtain ⟨ha₂, hb₂⟩ := ordPair_equiv e₂
          have hmk : Quotient.mk (FSetoid (L.dom done.length s)) i₁ =
              Quotient.mk (FSetoid (L.dom done.length s)) i₂ :=
            Quotient.sound (equiv_of_lift (ha₁.symm.trans ha₂))
          have hge : Equiv (X.Func (i ⟨done.length,
              Quotient.mk (FSetoid (L.dom done.length s)) i₁⟩))
              (X.Func (i ⟨done.length,
                Quotient.mk (FSetoid (L.dom done.length s)) i₂⟩)) := by
            rw [hmk]; exact Equiv.refl _
          exact hb₁.trans ((lift_equiv.{u, v} hge).trans hb₂.symm)
      refine ⟨?_, hl ▸ hin'⟩
      rw [L.fieldVal_fn]
      exact mem_piSet_of_dep (fun y y' hy => Sm.fib_resp (lift.{u, v} X) _ _ hy) hfunc

/-- Forward direction: derivable values are decoded valid trees. -/
theorem phiSpec_sub {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v})
    {B : PSet.{max u v}} (cov : SpecCover L Sm B) (ch : Choice.{u})
    (X : PSet.{u}) :
    Sub (phiSpec L Sm B (lift.{u, v} X)) (lift.{u, v} (gphi (L.sig Sm) X)) := by
  intro z hz
  obtain ⟨j, ⟨xs, hjB, hin⟩, hjz⟩ := mem_sep.mp hz
  obtain ⟨s, hnr0, hpt⟩ := cov.shape X xs hin
  obtain ⟨i, hi⟩ := cov.ex ch hin s hnr0
  obtain ⟨hLEq, hok⟩ := SpecCover.walk_le cov s hnr0 hpt i hi
    [] L.kinds (L.nr s) rfl rfl hnr0 trivial hin
  have hze : Equiv z (lift.{u, v}
      ((L.sig Sm).code s (fun b => X.Func (i b)))) := by
    have e1 : Equiv z (dataVal L.tag xs) := hjz.symm.trans hjB
    have e2 : Equiv (dataVal L.tag xs)
        (dataVal L.tag (List.map lift.{u, v}
          (L.asm s (fun b => X.Func (i b)) L.kinds 0 (L.nr s)))) :=
      dataVal_congr L.tag (LEq.symm hLEq)
    have e3 : Equiv (dataVal L.tag (List.map lift.{u, v}
          (L.asm s (fun b => X.Func (i b)) L.kinds 0 (L.nr s))))
        (lift.{u, v} (dataVal L.tag
          (L.asm s (fun b => X.Func (i b)) L.kinds 0 (L.nr s)))) :=
      (lift_dataVal_equiv L.tag _).symm
    exact e1.trans (e2.trans e3)
  exact mem_lift.mpr ⟨(L.sig Sm).code s (fun b => X.Func (i b)),
    ⟨⟨s, i, hok⟩, Equiv.refl _⟩, hze⟩

/-- Backward direction: decoded valid trees are derivable. -/
theorem lift_gphi_sub {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v})
    {B : PSet.{max u v}} (cov : SpecCover L Sm B) (X : PSet.{u}) :
    Sub (lift.{u, v} (gphi (L.sig Sm) X)) (phiSpec L Sm B (lift.{u, v} X)) := by
  intro z hz
  obtain ⟨y, ⟨p, hp⟩, hz⟩ := mem_lift.mp hz
  obtain ⟨s, i, hok⟩ := p
  have hin : Sm.InPhi (lift.{u, v} X) L.kinds
      (List.map lift.{u, v}
        (L.asm s (fun b => X.Func (i b)) L.kinds 0 (L.nr s))) 0 [] :=
    SpecCover.walk_ge cov s i [] L.kinds (L.nr s) [] rfl rfl trivial hok
  obtain ⟨j, hj⟩ := cov.covers X _ hin
  refine mem_sep.mpr ⟨j, ?_, ?_⟩
  · exact ⟨List.map lift.{u, v}
      (L.asm s (fun b => X.Func (i b)) L.kinds 0 (L.nr s)), hj, hin⟩
  · exact hj.trans ((lift_dataVal_equiv L.tag _).symm.trans
      ((lift_equiv.{u, v} hp).trans hz.symm))

/-- The semantic operator is W-shaped: its action on a lifted small set is the
lift of the guarded signature's operator. -/
theorem wshaped_phiSpec {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v})
    {B : PSet.{max u v}} (cov : SpecCover L Sm B) (ch : Choice.{u}) :
    WShaped (phiSpec L Sm B) (L.sig Sm) :=
  ⟨fun X => ext fun z =>
    ⟨phiSpec_sub L Sm cov ch X z, lift_gphi_sub L Sm cov X z⟩⟩

end PSet

end Rcic.F3
