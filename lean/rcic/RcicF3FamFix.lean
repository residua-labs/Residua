import rcic.RcicF3StageN
import rcic.RcicF3Ctor

/-!
# F3 S5b-2: fibres under growing field sets

`mem_TypeFib` characterizes the members of a `Type` fibre: data values of a
constructor whose fields fit and whose field sets lie in the stage. With it,
a fibre is monotone in its field sets (`TypeFib_mono`, `PropFib_mono`), and
the fibre at the limit of a growing sequence of field sets is the union of
the fibres along it (`TypeFib_lim`, `PropFib_lim`): a data value has
finitely many fields, so it appears at a finite step.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-! ### membership -/

theorem SmallAlong_congr (M : Interp.{T}) (σ : Nat → Nat) (W : PSet.{T}) :
    (Ds : List (Expr Nat)) → ∀ {ρ ρ' : Nat → PSet.{T}}, (∀ i, Equiv (ρ i) (ρ' i)) →
      ∀ {xs xs' : List PSet.{T}}, LEq xs xs' → SmallAlong M σ W Ds ρ xs → SmallAlong M σ W Ds ρ' xs'
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: _, _, _, _, [], [], _, _ => trivial
  | A :: Ds, _, _, hρ, _ :: _, _ :: _, ⟨hx, hxs⟩, ⟨hW, h⟩ =>
      ⟨mem_congr_left (ed_congr M (den_congr M σ A hρ)) hW, SmallAlong_congr M σ W Ds (vcons_congr hx hρ) hxs h⟩

theorem FitSetT_inv (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → ∀ t, t ∈ FitSetT M W k σ Ds ρ →
      ∃ ys, Equiv t (tup ys) ∧ TelFits M σ Ds ρ ys ∧ SmallAlong M σ (W k) Ds ρ ys
  | [], _, t, ht => ⟨[], mem_singleton.mp ht, trivial, trivial⟩
  | A :: Ds, ρ, t, ht => by
      obtain ⟨s, hs, hts⟩ := mem_sUnion.mp ht
      obtain ⟨i, hi⟩ := mem_sImage.mp hs
      obtain ⟨x, hx, hix⟩ : ∃ x, x ∈ truncW M W k (Ed M (den M σ ρ A)) ∧
          Equiv (sImage (fun t => ordPair x t) (FitSetT M W k σ Ds (vcons x ρ))) s := ⟨_, ⟨i, Equiv.refl _⟩, hi⟩
      obtain ⟨i', hi'⟩ := mem_sImage.mp (mem_congr_right hix.symm hts)
      obtain ⟨t', ht', ht'e⟩ : ∃ t', t' ∈ FitSetT M W k σ Ds (vcons x ρ) ∧ Equiv (ordPair x t') t :=
        ⟨_, ⟨i', Equiv.refl _⟩, hi'⟩
      obtain ⟨ys, hys, hf, hsm⟩ := FitSetT_inv M W k σ Ds (vcons x ρ) t' ht'
      have hxS : x ∈ Ed M (den M σ ρ A) ∧ Ed M (den M σ ρ A) ∈ W k := by
        revert hx
        unfold truncW cond
        cases M.dec (Ed M (den M σ ρ A) ∈ W k) with
        | isTrue h => exact fun hx => ⟨hx, h⟩
        | isFalse _ => exact fun hx => absurd hx not_mem_pempty
      exact ⟨x :: ys, ht'e.symm.trans (ordPair_congr Equiv.rfl hys), ⟨hxS.1, hf⟩, ⟨hxS.2, hsm⟩⟩

theorem BoundT_inv (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) (ρp : Nat → PSet.{T})
    {z : PSet.{T}} : (j : Nat) → (cs : List (List (Expr Nat) × List (Expr Nat))) →
    z ∈ BoundT M W k σ ρp j cs → ∃ i c t, cs[i]? = some c ∧ t ∈ FitSetT M W k σ c.1 ρp ∧
      Equiv z (dataOfTup (j + i) t)
  | _, [], h => absurd h not_mem_pempty
  | j, c :: cs, h => by
      rcases mem_sUnion_pair.mp h with h | h
      · obtain ⟨i, hi⟩ := mem_sImage.mp h
        exact ⟨0, c, _, List.getElem?_cons_zero, ⟨i, Equiv.refl _⟩, hi.symm⟩
      · obtain ⟨i, c', t, hc, ht, he⟩ := BoundT_inv M W k σ ρp (j + 1) cs h
        exact ⟨i + 1, c', t, by rw [List.getElem?_cons_succ]; exact hc, ht, by rw [show j + (i + 1) = j + 1 + i by omega]; exact he⟩

/-- The members of a `Type` fibre. -/
theorem mem_TypeFib {M : Interp.{T}} {W : Nat → PSet.{T}} {k : Nat} {σ : Nat → Nat}
    {cs : List (List (Expr Nat) × List (Expr Nat))} {ρp : Nat → PSet.{T}} {is : List PSet.{T}} {z : PSet.{T}} :
    z ∈ TypeFib M W k σ cs ρp is ↔ ∃ j xs c, cs[j]? = some c ∧ CtorFits M σ cs ρp is j xs ∧
      Equiv z (dataVal j xs) ∧ SmallAlong M σ (W k) c.1 ρp xs := by
  constructor
  · intro h
    obtain ⟨i, ⟨j, xs, hcf, he⟩, hiz⟩ := mem_sep.mp h
    have hB : (BoundT M W k σ ρp 0 cs).Func i ∈ BoundT M W k σ ρp 0 cs := ⟨i, Equiv.refl _⟩
    obtain ⟨j', c', t, hc', ht, hte⟩ := BoundT_inv M W k σ ρp 0 cs hB
    obtain ⟨ys, hys, hyf, hysm⟩ := FitSetT_inv M W k σ c'.1 ρp t ht
    obtain ⟨c, hc, hxf, hix⟩ := hcf
    have e1 : Equiv (dataVal j xs) (dataVal j' ys) := by
      refine he.symm.trans (hte.trans ?_)
      rw [Nat.zero_add]
      exact ordPair_congr Equiv.rfl (ordPair_congr Equiv.rfl hys)
    have hjj : j = j' := by
      have h2 := ordPair_equiv (ordPair_equiv e1).2
      exact ord_inj h2.1
    subst hjj
    rw [hc] at hc'
    have hcc := Option.some.inj hc'
    subst hcc
    obtain ⟨_, hl⟩ := dataVal_inj (by rw [hxf.length, hyf.length]) e1
    exact ⟨j, xs, c, hc, ⟨c, hc, hxf, hix⟩, hiz.symm.trans he,
      SmallAlong_congr M σ (W k) c.1 (fun _ => Equiv.rfl) hl.symm hysm⟩
  · rintro ⟨j, xs, c, hc, hcf, hz, hsm⟩
    obtain ⟨c', hc', hxf, hri⟩ := hcf
    rw [hc] at hc'
    have hcc := Option.some.inj hc'
    subst hcc
    have hcf : CtorFits M σ cs ρp is j xs := ⟨c, hc, hxf, hri⟩
    have hB := mem_BoundT M W k σ ρp 0 cs j c hc (mem_FitSetT M W k σ c.1 ρp xs hxf hsm)
    rw [Nat.zero_add] at hB
    obtain ⟨i, hi⟩ := hB
    exact mem_sep.mpr ⟨i, ⟨j, xs, hcf, hi⟩, hi.trans hz.symm⟩

/-! ### monotonicity -/

theorem mem_of_getElem?' {α : Type} {a : α} : {l : List α} → {i : Nat} → l[i]? = some a → a ∈ l
  | [], _, h => by simp at h
  | b :: l, 0, h => by
      rw [List.getElem?_cons_zero] at h
      rw [Option.some.inj h]
      exact List.mem_cons_self _ _
  | b :: l, i + 1, h => by
      rw [List.getElem?_cons_succ] at h
      exact List.mem_cons_of_mem _ (mem_of_getElem?' h)

/-- Field sets grow from `M₁` to `M₂` along a telescope. -/
def FieldsLE (M₁ M₂ : Interp.{T}) (σ : Nat → Nat) (Ds : List (Expr Nat)) : Prop :=
  ∀ A, A ∈ Ds → ∀ ρ z, z ∈ Ed M₁ (den M₁ σ ρ A) → z ∈ Ed M₂ (den M₂ σ ρ A)

theorem TelFits_mono {M₁ M₂ : Interp.{T}} {σ : Nat → Nat} : (Ds : List (Expr Nat)) → FieldsLE M₁ M₂ σ Ds →
    ∀ ρ xs, TelFits M₁ σ Ds ρ xs → TelFits M₂ σ Ds ρ xs
  | [], _, _, [], h => h
  | A :: Ds, hD, ρ, x :: xs, ⟨hx, h⟩ =>
      ⟨hD A (List.mem_cons_self _ _) ρ x hx,
        TelFits_mono Ds (fun B hB => hD B (List.mem_cons_of_mem _ hB)) (vcons x ρ) xs h⟩

theorem SmallAlong_mono {M₁ M₂ : Interp.{T}} {σ : Nat → Nat} {W : PSet.{T}} : (Ds : List (Expr Nat)) →
    (∀ A, A ∈ Ds → ∀ ρ, Ed M₁ (den M₁ σ ρ A) ∈ W → Ed M₂ (den M₂ σ ρ A) ∈ W) →
    ∀ ρ xs, SmallAlong M₁ σ W Ds ρ xs → SmallAlong M₂ σ W Ds ρ xs
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, [], _ => trivial
  | A :: Ds, hD, ρ, x :: xs, ⟨hW, h⟩ =>
      ⟨hD A (List.mem_cons_self _ _) ρ hW,
        SmallAlong_mono Ds (fun B hB => hD B (List.mem_cons_of_mem _ hB)) (vcons x ρ) xs h⟩

/-- Fibres grow from `M₁` to `M₂`: field sets grow, stay in the stage, and the
result indices denote the same. -/
structure FamLE (M₁ M₂ : Interp.{T}) (W : PSet.{T}) (σ : Nat → Nat)
    (cs : List (List (Expr Nat) × List (Expr Nat))) : Prop where
  fields : ∀ c, c ∈ cs → FieldsLE M₁ M₂ σ c.1
  small : ∀ c, c ∈ cs → ∀ A, A ∈ c.1 → ∀ ρ, Ed M₁ (den M₁ σ ρ A) ∈ W → Ed M₂ (den M₂ σ ρ A) ∈ W
  ri : ∀ c, c ∈ cs → ∀ e, e ∈ c.2 → ∀ ρ, Equiv (den M₁ σ ρ e) (den M₂ σ ρ e)

theorem LEq_map_den_tables {M₁ M₂ : Interp.{T}} {σ : Nat → Nat} {ρ : Nat → PSet.{T}} :
    (es : List (Expr Nat)) → (∀ e, e ∈ es → Equiv (den M₁ σ ρ e) (den M₂ σ ρ e)) →
      LEq (es.map (den M₁ σ ρ)) (es.map (den M₂ σ ρ))
  | [], _ => trivial
  | e :: es, h => ⟨h e (List.mem_cons_self _ _), LEq_map_den_tables es fun e' he' => h e' (List.mem_cons_of_mem _ he')⟩

theorem CtorFits_mono {M₁ M₂ : Interp.{T}} {W : PSet.{T}} {σ : Nat → Nat}
    {cs : List (List (Expr Nat) × List (Expr Nat))} (h : FamLE M₁ M₂ W σ cs) {ρp : Nat → PSet.{T}}
    {is : List PSet.{T}} {j : Nat} {xs : List PSet.{T}} (hc : CtorFits M₁ σ cs ρp is j xs) :
    CtorFits M₂ σ cs ρp is j xs := by
  obtain ⟨c, hcj, hf, hi⟩ := hc
  have hmem : c ∈ cs := mem_of_getElem?' hcj
  exact ⟨c, hcj, TelFits_mono c.1 (h.fields c hmem) ρp xs hf,
    LEq.trans (LEq_map_den_tables c.2 fun e he => (h.ri c hmem e he _).symm) hi⟩

theorem TypeFib_mono {M₁ M₂ : Interp.{T}} {W : Nat → PSet.{T}} {k : Nat} {σ : Nat → Nat}
    {cs : List (List (Expr Nat) × List (Expr Nat))} (h : FamLE M₁ M₂ (W k) σ cs) {ρp : Nat → PSet.{T}}
    {is : List PSet.{T}} {z : PSet.{T}} (hz : z ∈ TypeFib M₁ W k σ cs ρp is) : z ∈ TypeFib M₂ W k σ cs ρp is := by
  obtain ⟨j, xs, c, hc, hcf, he, hsm⟩ := mem_TypeFib.mp hz
  have hmem : c ∈ cs := mem_of_getElem?' hc
  exact mem_TypeFib.mpr ⟨j, xs, c, hc, CtorFits_mono h hcf, he,
    SmallAlong_mono c.1 (h.small c hmem) ρp xs hsm⟩

theorem PropFib_mono {M₁ M₂ : Interp.{T}} {W : PSet.{T}} {σ : Nat → Nat}
    {cs : List (List (Expr Nat) × List (Expr Nat))} (h : FamLE M₁ M₂ W σ cs) {ρp : Nat → PSet.{T}}
    {is : List PSet.{T}} {z : PSet.{T}} (hz : z ∈ PropFib M₁ σ cs ρp is) : z ∈ PropFib M₂ σ cs ρp is := by
  obtain ⟨⟨j, xs, hcf⟩, he⟩ := mem_tv.mp hz
  exact mem_tv.mpr ⟨⟨j, xs, CtorFits_mono h hcf⟩, he⟩


/-! ### limits -/

/-- A growing sequence of field sets `Mn n` with limit `Mi`. -/
structure FamChain (Mn : Nat → Interp.{T}) (Mi : Interp.{T}) (W : PSet.{T}) (σ : Nat → Nat)
    (cs : List (List (Expr Nat) × List (Expr Nat))) : Prop where
  step : ∀ n, FamLE (Mn n) (Mn (n + 1)) W σ cs
  toLim : ∀ n, FamLE (Mn n) Mi W σ cs
  lim : ∀ c, c ∈ cs → ∀ A, A ∈ c.1 → ∀ ρ z, z ∈ Ed Mi (den Mi σ ρ A) → ∃ n, z ∈ Ed (Mn n) (den (Mn n) σ ρ A)
  limSmall : ∀ c, c ∈ cs → ∀ A, A ∈ c.1 → ∀ ρ, Ed Mi (den Mi σ ρ A) ∈ W →
    ∀ n, Ed (Mn n) (den (Mn n) σ ρ A) ∈ W

section Lim

variable {Mn : Nat → Interp.{T}} {Mi : Interp.{T}} {W : PSet.{T}} {σ : Nat → Nat}
  {cs : List (List (Expr Nat) × List (Expr Nat))} (h : FamChain Mn Mi W σ cs)
include h

theorem FamChain.le {c : List (Expr Nat) × List (Expr Nat)} (hc : c ∈ cs) {A : Expr Nat} (hA : A ∈ c.1)
    (ρ : Nat → PSet.{T}) (z : PSet.{T}) {n m : Nat} (hnm : n ≤ m)
    (hz : z ∈ Ed (Mn n) (den (Mn n) σ ρ A)) : z ∈ Ed (Mn m) (den (Mn m) σ ρ A) := by
  induction hnm with
  | refl => exact hz
  | step _ ih => exact (h.step _).fields c hc A hA ρ z ih

theorem FamChain.telFits {c : List (Expr Nat) × List (Expr Nat)} (hc : c ∈ cs) :
    (Ds : List (Expr Nat)) → (∀ A, A ∈ Ds → A ∈ c.1) → ∀ ρ xs, TelFits Mi σ Ds ρ xs →
      ∃ N, ∀ m, N ≤ m → TelFits (Mn m) σ Ds ρ xs
  | [], _, _, [], _ => ⟨0, fun _ _ => trivial⟩
  | A :: Ds, hD, ρ, x :: xs, ⟨hx, hr⟩ => by
      obtain ⟨n0, hn0⟩ := h.lim c hc A (hD A (List.mem_cons_self _ _)) ρ x hx
      obtain ⟨N1, hN1⟩ := FamChain.telFits hc Ds (fun B hB => hD B (List.mem_cons_of_mem _ hB)) (vcons x ρ) xs hr
      refine ⟨max n0 N1, fun m hm => ⟨?_, hN1 m (Nat.le_trans (Nat.le_max_right _ _) hm)⟩⟩
      exact h.le hc (hD A (List.mem_cons_self _ _)) ρ x (Nat.le_trans (Nat.le_max_left _ _) hm) hn0

theorem FamChain.ctorFits {ρp : Nat → PSet.{T}} {is : List PSet.{T}} {j : Nat} {xs : List PSet.{T}}
    {c : List (Expr Nat) × List (Expr Nat)} (hc : cs[j]? = some c) (hcf : CtorFits Mi σ cs ρp is j xs) :
    ∃ N, CtorFits (Mn N) σ cs ρp is j xs := by
  obtain ⟨c', hc', hxf, hri⟩ := hcf
  rw [hc] at hc'
  have hcc := Option.some.inj hc'
  subst hcc
  have hmem : c ∈ cs := mem_of_getElem?' hc
  obtain ⟨N, hN⟩ := h.telFits hmem c.1 (fun _ hA => hA) ρp xs hxf
  exact ⟨N, c, hc, hN N (Nat.le_refl _),
    LEq.trans (LEq_map_den_tables c.2 fun e he => (h.toLim N).ri c hmem e he _) hri⟩

theorem TypeFib_lim {W' : Nat → PSet.{T}} {k : Nat} (hW : W' k = W) {ρp : Nat → PSet.{T}}
    {is : List PSet.{T}} {z : PSet.{T}} :
    z ∈ TypeFib Mi W' k σ cs ρp is ↔ ∃ n, z ∈ TypeFib (Mn n) W' k σ cs ρp is := by
  subst hW
  constructor
  · intro hz
    obtain ⟨j, xs, c, hc, hcf, he, hsm⟩ := mem_TypeFib.mp hz
    obtain ⟨N, hN⟩ := h.ctorFits hc hcf
    have hmem : c ∈ cs := mem_of_getElem?' hc
    exact ⟨N, mem_TypeFib.mpr ⟨j, xs, c, hc, hN, he,
      SmallAlong_mono c.1 (fun A hA ρ hW => h.limSmall c hmem A hA ρ hW N) ρp xs hsm⟩⟩
  · rintro ⟨n, hz⟩
    exact TypeFib_mono (h.toLim n) hz

theorem PropFib_lim {ρp : Nat → PSet.{T}} {is : List PSet.{T}} {z : PSet.{T}} :
    z ∈ PropFib Mi σ cs ρp is ↔ ∃ n, z ∈ PropFib (Mn n) σ cs ρp is := by
  constructor
  · intro hz
    obtain ⟨⟨j, xs, hcf⟩, he⟩ := mem_tv.mp hz
    rcases id hcf with ⟨c, hc, _⟩
    obtain ⟨N, hN⟩ := h.ctorFits hc hcf
    exact ⟨N, mem_tv.mpr ⟨⟨j, xs, hN⟩, he⟩⟩
  · rintro ⟨n, hz⟩
    exact PropFib_mono (h.toLim n) hz

end Lim

end PSet

end Rcic.F3
