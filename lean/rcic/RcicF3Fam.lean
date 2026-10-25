import rcic.RcicF3Data
import rcic.RcicF3EnvSound

/-!
# F3 S5a-2: the family of an inductive group

`FamData` is the syntactic data of a group read off its recursor's admission:
the family's parameters and indices, its result level, and for each
constructor its fields and result indices.

- `PropFib`: for a `Prop` family, the truth value that some constructor's
  fields fit with the given result indices;
- `TypeFib`: for a `Type` family at level `k`, the set of data values
  `dataVal j xs` whose fields fit constructor `j` with the given result
  indices, cut out of a bounding set `BoundT` built from the field sets
  truncated to the stage `W k` (`truncW`). The truncation makes the fibre
  small unconditionally; for an admitted group it is never active (the
  field types lie in universes at most `k`), which the constructor proof
  uses;
- `famEnd` / `famVal`: the family's value, the telescope abstraction over
  parameters and indices ending in the fibre's type value;
- `famVal_mem`: the family's value is an element of its type, with no
  typing premise.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- The syntactic data of an inductive group. -/
structure FamData where
  fref : Nat
  params : List (Expr Nat)
  indices : List (Expr Nat)
  resLevel : Level
  ctors : List (List (Expr Nat) × List (Expr Nat))
  policy : EliminationPolicy

/-- `S` if it is an element of the stage `W k`, `∅` otherwise. -/
def truncW (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (S : PSet.{T}) : PSet.{T} :=
  cond M.dec (S ∈ W k) S pempty

/-- The tuples of fitting field values, each field set truncated to `W k`. -/
def FitSetT (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) :
    List (Expr Nat) → (Nat → PSet.{T}) → PSet.{T}
  | [], _ => singleton pempty
  | A :: Ds, ρ => sUnion (sImage (fun x => sImage (fun t => ordPair x t) (FitSetT M W k σ Ds (vcons x ρ)))
      (truncW M W k (Ed M (den M σ ρ A))))

/-- The data values of constructor `j` with tuple `t`. -/
def dataOfTup (j : Nat) (t : PSet.{T}) : PSet.{T} := ordPair pempty (ordPair (ord j) t)

/-- The bounding set of a `Type` fibre, constructors from index `j` on. -/
def BoundT (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) (ρp : Nat → PSet.{T}) :
    Nat → List (List (Expr Nat) × List (Expr Nat)) → PSet.{T}
  | _, [] => pempty
  | j, c :: cs => sUnion (pair (sImage (dataOfTup j) (FitSetT M W k σ c.1 ρp)) (BoundT M W k σ ρp (j + 1) cs))

/-- Constructor `j`'s fields `xs` fit at the parameter environment `ρp` with
result indices `is`. -/
def CtorFits (M : Interp.{T}) (σ : Nat → Nat) (cs : List (List (Expr Nat) × List (Expr Nat)))
    (ρp : Nat → PSet.{T}) (is : List PSet.{T}) (j : Nat) (xs : List PSet.{T}) : Prop :=
  ∃ c, cs[j]? = some c ∧ TelFits M σ c.1 ρp xs ∧ LEq (c.2.map (den M σ (push xs ρp))) is

/-- The fibre of a `Type` family. -/
def TypeFib (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat)
    (cs : List (List (Expr Nat) × List (Expr Nat))) (ρp : Nat → PSet.{T}) (is : List PSet.{T}) :
    PSet.{T} :=
  sep (fun z => ∃ j xs, CtorFits M σ cs ρp is j xs ∧ Equiv z (dataVal j xs)) (BoundT M W k σ ρp 0 cs)

/-- The fibre of a `Prop` family. -/
def PropFib (M : Interp.{T}) (σ : Nat → Nat) (cs : List (List (Expr Nat) × List (Expr Nat)))
    (ρp : Nat → PSet.{T}) (is : List PSet.{T}) : PSet.{T} :=
  tv (∃ j xs, CtorFits M σ cs ρp is j xs)

/-- No constructor of the family fits, at any parameters and indices. -/
def PropEmpty (M : Interp.{T}) (σ : Nat → Nat) (fd : FamData) : Prop :=
  ∀ ρp is j xs, ¬ CtorFits M σ fd.ctors ρp is j xs

/-- The values of the last `q` bindings, outermost first. -/
def lastVals (q : Nat) (ρ : Nat → PSet.{T}) : List PSet.{T} := (List.range q).reverse.map ρ

/-- The end value of the family at the environment after parameters and indices. -/
def famEnd (M : Interp.{T}) (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData)
    (ρ : Nat → PSet.{T}) : PSet.{T} :=
  cond M.dec (evalTotal σ fd.resLevel = 0)
    (tyv (PropFib M σ fd.ctors (shiftρ fd.indices.length ρ) (lastVals fd.indices.length ρ)))
    (tyv (TypeFib M W (evalTotal σ fd.resLevel) σ fd.ctors (shiftρ fd.indices.length ρ)
      (lastVals fd.indices.length ρ)))

/-- The family's type, as its data records it. -/
def famType (fd : FamData) : Expr Nat := policyPi (fd.params ++ fd.indices) (.sort fd.resLevel)

/-- The family's value. -/
def famVal (M : Interp.{T}) (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData) : PSet.{T} :=
  piLam M σ (famEnd M W σ fd) (fun _ => pempty) (famType fd)

/-! ### congruence -/

theorem truncW_congr (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) {S S' : PSet.{T}}
    (h : Equiv S S') : Equiv (truncW M W k S) (truncW M W k S') :=
  cond_congr ⟨fun hS => mem_congr_left h hS, fun hS => mem_congr_left h.symm hS⟩ h Equiv.rfl

theorem FitSetT_congr (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → ∀ {ρ ρ' : Nat → PSet.{T}}, (∀ i, Equiv (ρ i) (ρ' i)) →
      Equiv (FitSetT M W k σ Ds ρ) (FitSetT M W k σ Ds ρ')
  | [], _, _, _ => Equiv.rfl
  | A :: Ds, ρ, ρ', h => sUnion_congr (sImage_congr
      (fun x x' hx => sImage_congr (fun t t' ht => ordPair_congr hx ht)
        (FitSetT_congr M W k σ Ds (vcons_congr hx h)))
      (truncW_congr M W k (ed_congr M (den_congr M σ A h))))

theorem TelFits_congr (M : Interp.{T}) (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → ∀ {ρ ρ' : Nat → PSet.{T}}, (∀ i, Equiv (ρ i) (ρ' i)) →
      ∀ {xs xs' : List PSet.{T}}, LEq xs xs' → TelFits M σ Ds ρ xs → TelFits M σ Ds ρ' xs'
  | [], _, _, _, [], [], _, h => h
  | A :: Ds, ρ, ρ', hρ, x :: xs, x' :: xs', ⟨hx, hxs⟩, ⟨hm, h⟩ =>
      ⟨mem_congr_left hx (mem_congr_right (ed_congr M (den_congr M σ A hρ)) hm),
        TelFits_congr M σ Ds (vcons_congr hx hρ) hxs h⟩

theorem push_congr : {xs xs' : List PSet.{T}} → LEq xs xs' → ∀ {ρ ρ' : Nat → PSet.{T}},
    (∀ i, Equiv (ρ i) (ρ' i)) → ∀ i, Equiv (push xs ρ i) (push xs' ρ' i)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, ⟨hx, hs⟩, _, _, h => push_congr hs (vcons_congr hx h)

theorem LEq_map_den (M : Interp.{T}) (σ : Nat → Nat) {ρ ρ' : Nat → PSet.{T}}
    (h : ∀ i, Equiv (ρ i) (ρ' i)) : (es : List (Expr Nat)) → LEq (es.map (den M σ ρ)) (es.map (den M σ ρ'))
  | [] => trivial
  | e :: es => ⟨den_congr M σ e h, LEq_map_den M σ h es⟩

theorem CtorFits_congr (M : Interp.{T}) (σ : Nat → Nat) (cs : List (List (Expr Nat) × List (Expr Nat)))
    {ρp ρp' : Nat → PSet.{T}} (hρ : ∀ i, Equiv (ρp i) (ρp' i)) {is is' : List PSet.{T}}
    (his : LEq is is') (j : Nat) {xs xs' : List PSet.{T}} (hxs : LEq xs xs')
    (h : CtorFits M σ cs ρp is j xs) : CtorFits M σ cs ρp' is' j xs' := by
  obtain ⟨c, hc, hf, hi⟩ := h
  have e : LEq (c.2.map (den M σ (push xs' ρp'))) (c.2.map (den M σ (push xs ρp))) :=
    LEq_map_den M σ (push_congr hxs.symm (fun i => (hρ i).symm)) c.2
  exact ⟨c, hc, TelFits_congr M σ c.1 hρ hxs hf, LEq.trans e (LEq.trans hi his)⟩

theorem lastVals_congr (q : Nat) {ρ ρ' : Nat → PSet.{T}} (h : ∀ i, Equiv (ρ i) (ρ' i)) :
    LEq (lastVals q ρ) (lastVals q ρ') := by
  unfold lastVals
  induction (List.range q).reverse with
  | nil => trivial
  | cons i is ih => exact ⟨h i, ih⟩

theorem dataOfTup_congr (j : Nat) {t t' : PSet.{T}} (h : Equiv t t') :
    Equiv (dataOfTup j t) (dataOfTup j t') :=
  ordPair_congr Equiv.rfl (ordPair_congr Equiv.rfl h)

theorem BoundT_congr (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat)
    {ρp ρp' : Nat → PSet.{T}} (h : ∀ i, Equiv (ρp i) (ρp' i)) :
    (j : Nat) → (cs : List (List (Expr Nat) × List (Expr Nat))) →
      Equiv (BoundT M W k σ ρp j cs) (BoundT M W k σ ρp' j cs)
  | _, [] => Equiv.rfl
  | j, c :: cs => sUnion_congr (pair_congr
      (sImage_congr (fun _ _ ht => dataOfTup_congr j ht) (FitSetT_congr M W k σ c.1 h))
      (BoundT_congr M W k σ h (j + 1) cs))

theorem tv_congr {φ ψ : Prop} (h : φ ↔ ψ) : Equiv (tv.{T} φ) (tv.{T} ψ) :=
  sep_congr (fun _ _ _ hp => h.mp hp) (fun _ _ _ hp => h.mpr hp) Equiv.rfl

theorem TypeFib_congr (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat)
    (cs : List (List (Expr Nat) × List (Expr Nat))) {ρp ρp' : Nat → PSet.{T}}
    (h : ∀ i, Equiv (ρp i) (ρp' i)) {is is' : List PSet.{T}} (his : LEq is is') :
    Equiv (TypeFib M W k σ cs ρp is) (TypeFib M W k σ cs ρp' is') :=
  sep_congr
    (fun _ _ hab ⟨j, xs, hc, he⟩ => ⟨j, xs, CtorFits_congr M σ cs h his j (LEq.refl xs) hc, hab.symm.trans he⟩)
    (fun _ _ hab ⟨j, xs, hc, he⟩ => ⟨j, xs, CtorFits_congr M σ cs (fun i => (h i).symm) his.symm j
      (LEq.refl xs) hc, hab.symm.trans he⟩)
    (BoundT_congr M W k σ h 0 cs)

theorem PropFib_congr (M : Interp.{T}) (σ : Nat → Nat)
    (cs : List (List (Expr Nat) × List (Expr Nat))) {ρp ρp' : Nat → PSet.{T}}
    (h : ∀ i, Equiv (ρp i) (ρp' i)) {is is' : List PSet.{T}} (his : LEq is is') :
    Equiv (PropFib M σ cs ρp is) (PropFib M σ cs ρp' is') :=
  tv_congr ⟨fun ⟨j, xs, hc⟩ => ⟨j, xs, CtorFits_congr M σ cs h his j (LEq.refl xs) hc⟩,
    fun ⟨j, xs, hc⟩ => ⟨j, xs, CtorFits_congr M σ cs (fun i => (h i).symm) his.symm j (LEq.refl xs) hc⟩⟩

theorem famEnd_resp (M : Interp.{T}) (W : Nat → PSet.{T}) (σ : Nat → Nat) (fd : FamData) :
    EnvResp (famEnd M W σ fd) := fun ρ ρ' h => by
  have hs : ∀ i, Equiv (shiftρ fd.indices.length ρ i) (shiftρ fd.indices.length ρ' i) :=
    fun i => h (i + fd.indices.length)
  have hl := lastVals_congr fd.indices.length h
  exact cond_congr Iff.rfl (tyv_congr (PropFib_congr M σ fd.ctors hs hl))
    (tyv_congr (TypeFib_congr M W _ σ fd.ctors hs hl))

/-! ### smallness -/

theorem ord_mem_stage {W : PSet.{T}} (hW : Stage W) : (j : Nat) → ord j ∈ W
  | 0 => hW.empty
  | j + 1 => hW.subset (hW.sUnion (hW.pair (hW.singleton_mem (ord_mem_stage hW j)) (ord_mem_stage hW j)))
      fun z hz => by
        rcases mem_insert.mp hz with h | h
        · exact mem_sUnion.mpr ⟨singleton (ord j), mem_pair.mpr (Or.inl Equiv.rfl), mem_singleton.mpr h⟩
        · exact mem_sUnion.mpr ⟨ord j, mem_pair.mpr (Or.inr Equiv.rfl), h⟩

theorem truncW_mem (M : Interp.{T}) {W : Nat → PSet.{T}} {k : Nat} (S : PSet.{T}) (hW : Stage (W k)) :
    truncW M W k S ∈ W k := by
  unfold truncW cond
  cases M.dec (S ∈ W k) with
  | isTrue h => exact h
  | isFalse _ => exact hW.empty

theorem FitSetT_mem (M : Interp.{T}) {W : Nat → PSet.{T}} {k : Nat} (σ : Nat → Nat) (hW : Stage (W k)) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → FitSetT M W k σ Ds ρ ∈ W k
  | [], _ => hW.singleton_mem hW.empty
  | A :: Ds, ρ => by
      refine hW.sUnion (hW.image ?_ (truncW_mem M _ hW) fun x hx => ?_)
      · intro x x' hx
        exact sImage_congr (fun t t' ht => ordPair_congr hx ht)
          (FitSetT_congr M W k σ Ds (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl)))
      · have hxW : x ∈ W k := hW.trans (truncW_mem M _ hW) hx
        have hF := FitSetT_mem M σ hW Ds (vcons x ρ)
        exact hW.image (fun t t' ht => ordPair_congr Equiv.rfl ht) hF
          fun t ht => hW.ordPair_mem hxW (hW.trans hF ht)

theorem BoundT_mem (M : Interp.{T}) {W : Nat → PSet.{T}} {k : Nat} (σ : Nat → Nat) (hW : Stage (W k))
    (ρp : Nat → PSet.{T}) : (j : Nat) → (cs : List (List (Expr Nat) × List (Expr Nat))) →
      BoundT M W k σ ρp j cs ∈ W k
  | _, [] => hW.empty
  | j, c :: cs => by
      have hF := FitSetT_mem M σ hW c.1 ρp
      refine hW.sUnion (hW.pair ?_ (BoundT_mem M σ hW ρp (j + 1) cs))
      exact hW.image (fun _ _ ht => dataOfTup_congr j ht) hF
        fun t ht => hW.ordPair_mem hW.empty (hW.ordPair_mem (ord_mem_stage hW j) (hW.trans hF ht))

theorem TypeFib_mem (M : Interp.{T}) {W : Nat → PSet.{T}} {k : Nat} (σ : Nat → Nat) (hW : Stage (W k))
    (cs : List (List (Expr Nat) × List (Expr Nat))) (ρp : Nat → PSet.{T}) (is : List PSet.{T}) :
    TypeFib M W k σ cs ρp is ∈ W k :=
  hW.subset (BoundT_mem M σ hW ρp 0 cs) fun _ hz => mem_sep_subset hz

theorem TypeFib_dich (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat)
    (cs : List (List (Expr Nat) × List (Expr Nat))) (ρp : Nat → PSet.{T}) (is : List PSet.{T}) :
    Dich (TypeFib M W k σ cs ρp is) := Or.inr fun h => by
  obtain ⟨_, ⟨j, xs, _, he⟩, hi⟩ := mem_sep.mp h
  exact dataVal_ne_pempty j xs (he.symm.trans hi)

/-- The stages of the height-4 table. -/
theorem stage4 (P : Premises4) : ∀ k, Stage (W4 (k + 1))
  | 0 => stage_univIn.{0, 4} P.c0
  | 1 => stage_univIn.{1, 4} P.c1
  | 2 => stage_univIn.{2, 4} P.c2
  | k + 3 => stage_univIn.{3, 4} P.c3

/-- **The family's value is an element of its type**, with no typing premise. -/
theorem famVal_mem (P : Premises4) (M : Interp.{4}) (hU : M.U = U W4) (σ : Nat → Nat) (fd : FamData)
    (ρ : Nat → PSet.{4}) :
    piLam M σ (famEnd M W4 σ fd) ρ (famType fd) ∈ Ed M (den M σ ρ (famType fd)) := by
  refine piLam_mem M σ (famEnd_resp M W4 σ fd) _ ρ ?_
  unfold famType
  apply piGood_policyPi
  intro ρ'
  show famEnd M W4 σ fd ρ' ∈ Ed M (tyv (M.U (evalTotal σ fd.resLevel)))
  rw [hU]
  refine mem_congr_right (ed_tyv M (U4_dich _)).symm ?_
  unfold famEnd cond
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue h0 =>
      show tyv _ ∈ U W4 (evalTotal σ fd.resLevel)
      rw [h0]
      exact (mem_sImage_tyv).mpr ⟨_, mem_propSets.mpr fun _ hy => (mem_tv.mp hy).2, Equiv.rfl⟩
  | isFalse h0 =>
      show tyv _ ∈ U W4 (evalTotal σ fd.resLevel)
      obtain ⟨k, hk⟩ : ∃ k, evalTotal σ fd.resLevel = k + 1 := ⟨evalTotal σ fd.resLevel - 1, by omega⟩
      rw [hk]
      have hmem := TypeFib_mem M σ (stage4 P k) fd.ctors (shiftρ fd.indices.length ρ')
        (lastVals fd.indices.length ρ')
      obtain ⟨i, hi⟩ := hmem
      show _ ∈ sImage tyv (sep Dich (W4 (k + 1)))
      refine (mem_sImage_tyv).mpr ⟨_, mem_sep.mpr ⟨i, ?_, hi⟩, Equiv.rfl⟩
      exact (dich_congr hi.symm).mp (TypeFib_dich M W4 _ σ fd.ctors _ _)

/-! ### environments after a telescope -/

theorem push_append : (xs ys : List PSet.{T}) → (ρ : Nat → PSet.{T}) →
    push (xs ++ ys) ρ = push ys (push xs ρ)
  | [], _, _ => rfl
  | x :: xs, ys, ρ => push_append xs ys (vcons x ρ)

theorem push_ge : (ys : List PSet.{T}) → (ρ : Nat → PSet.{T}) → (i : Nat) →
    push ys ρ (i + ys.length) = ρ i
  | [], _, _ => rfl
  | y :: ys, ρ, i => by
      show push ys (vcons y ρ) (i + (ys.length + 1)) = ρ i
      rw [show i + (ys.length + 1) = (i + 1) + ys.length by omega, push_ge ys (vcons y ρ) (i + 1)]
      rfl

theorem shiftρ_push (ys : List PSet.{T}) (ρ : Nat → PSet.{T}) : shiftρ ys.length (push ys ρ) = ρ :=
  funext fun i => push_ge ys ρ i

theorem push_lt : (ys : List PSet.{T}) → (ρ : Nat → PSet.{T}) → (i : Nat) → (h : i < ys.length) →
    push ys ρ i = ys[ys.length - 1 - i]'(by omega)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | y :: ys, ρ, i, h => by
      show push ys (vcons y ρ) i = _
      by_cases hi : i < ys.length
      · rw [push_lt ys (vcons y ρ) i hi]
        have : (y :: ys).length - 1 - i = (ys.length - 1 - i) + 1 := by simp; omega
        simp only [this, List.getElem_cons_succ]
      · have hi' : i = ys.length := by simp at h; omega
        subst hi'
        have := push_ge ys (vcons y ρ) 0
        rw [Nat.zero_add] at this
        rw [this]
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self, List.getElem_cons_zero]
        rfl

theorem lastVals_push (ys : List PSet.{T}) (ρ : Nat → PSet.{T}) : lastVals ys.length (push ys ρ) = ys := by
  apply List.ext_getElem
  · simp [lastVals]
  · intro i h1 h2
    simp only [lastVals, List.length_map, List.length_reverse, List.length_range] at h1
    simp only [lastVals, List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    rw [push_lt ys ρ _ (by omega)]
    congr 1
    omega

/-! ### applications that are not `∅` -/

theorem fapps_equiv_pempty {F : PSet.{T}} (h : Equiv F pempty) (xs : List PSet.{T}) :
    Equiv (fapps F xs) pempty :=
  (fapps_congr h xs).trans (fapps_pempty xs)

/-- If an application of a telescope abstraction is not `∅`, the arguments fit. -/
theorem fits_of_fapps_ne (M : Interp.{T}) (σ : Nat → Nat) {g : (Nat → PSet.{T}) → PSet.{T}}
    (hg : EnvResp g) (b : Expr Nat) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → (xs : List PSet.{T}) → xs.length = Ds.length →
      ¬ Equiv (fapps (piLam M σ g ρ (policyPi Ds b)) xs) pempty → TelFits M σ Ds ρ xs
  | [], _, [], _, _ => trivial
  | A :: Ds, ρ, x :: xs, hl, hne => by
      have hl' : xs.length = Ds.length := by simpa using hl
      have hb : ∀ y y', Equiv y y' → Equiv (piLam M σ g (vcons y ρ) (policyPi Ds b))
          (piLam M σ g (vcons y' ρ) (policyPi Ds b)) :=
        fun y y' hy => piLam_congr M σ hg _ (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl))
      cases hm : M.dec (x ∈ Ed M (den M σ ρ A)) with
      | isTrue hx =>
          refine ⟨hx, fits_of_fapps_ne M σ hg b Ds (vcons x ρ) xs hl' fun h0 => hne ?_⟩
          show Equiv (fapps (fapp (lamVal M (den M σ ρ A) _) x) xs) pempty
          exact (fapps_congr (beta_val M hb hx) xs).trans h0
      | isFalse hx =>
          exfalso; apply hne
          show Equiv (fapps (fapp (lamVal M (den M σ ρ A) _) x) xs) pempty
          refine fapps_equiv_pempty ?_ xs
          unfold lamVal cond
          cases M.dec (LamProof M (den M σ ρ A) fun y => piLam M σ g (vcons y ρ) (policyPi Ds b)) with
          | isTrue _ => exact fapp_pempty x
          | isFalse _ => exact fapp_mkLam_out hx

/-- An element of a product applied to a value outside the domain is `∅`. -/
theorem mem_dom_of_fapp_ne (M : Interp.{T}) {A f a : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x')) (hf : f ∈ Ed M (piVal M A B))
    (hne : ¬ Equiv (fapp f a) pempty) : a ∈ Ed M A := by
  have hf' := mem_congr_right (ed_piVal M A B hB) hf
  unfold cond at hf'
  cases hd : M.dec (PiProp M A B) with
  | isTrue hP =>
      rw [hd] at hf'
      obtain ⟨_, hz⟩ := mem_tv.mp hf'
      exact absurd ((fapp_congr hz Equiv.rfl).trans (fapp_pempty a)) hne
  | isFalse hP =>
      rw [hd] at hf'
      obtain ⟨hdom, _, _⟩ := isFuncOnDep_of_mem_piSet (fun x x' h => ed_congr M (hB x x' h)) hf'
      cases hm : M.dec (a ∈ Ed M A) with
      | isTrue h => exact h
      | isFalse ha =>
          exfalso; apply hne
          refine ext fun z => ⟨fun hz => ?_, fun hz => (not_mem_pempty hz).elim⟩
          obtain ⟨w, hw, _⟩ := mem_sUnion.mp hz
          obtain ⟨_, hp, _⟩ := mem_sep.mp hw
          obtain ⟨a', ha', _, _, he⟩ := (isFuncOnDep_of_mem_piSet (fun x x' h => ed_congr M (hB x x' h)) hf').2.1 _ hp
          exact (ha (mem_congr_left (ordPair_equiv he).1.symm ha')).elim

end PSet

end Rcic.F3
