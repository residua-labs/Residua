import rcic.RcicF3PiSmallMaskShape
import rcic.RcicF3RawFamilyRec
import rcic.RcicF3StepDGOrder

/-!
# Small fibres assembled without parameter representatives

Each parameter list has its own produced small signature. The candidate
intersects those fibres over every list representing the full key's
parameter prefix. A representative is exposed only in a Prop proof of
smallness; no representative is selected as data, and no equality between
independently compiled signatures is assumed.

Universe vectors are canonicalized at the family arity. This handles
short and extra vectors as well as full vectors. Constructor closure is
separate: it must supply the reached domain-mask predicate to the actual
signature producer. No frame or mask is added to an apex premise here.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallFrame
open Rcic.Declarative PiIndex RawFamily RawFamilyRec

/-- Select the actual small signature at the exact resulting stage. The
zero branch is empty; the data constructor producer uses a positive stage. -/
noncomputable def fibre (P : Premises4) (N : Interp.{4}) (σ : Nat → Nat)
    (cs : List PiValueRule.Constructor) (ps : List PSet.{4}) :
    Nat → Index.{4} → PSet.{4}
  | 0 => fun _ => pempty
  | 1 => PiSmallKeyProducerAt.family N
      (PiSmallMaskShape.signature.{0,4} N P.c0 σ cs ps)
  | 2 => PiSmallKeyProducerAt.family N
      (PiSmallMaskShape.signature.{1,4} N P.c1 σ cs ps)
  | 3 => PiSmallKeyProducerAt.family N
      (PiSmallMaskShape.signature.{2,4} N P.c2 σ cs ps)
  | _ + 4 => PiSmallKeyProducerAt.family N
      (PiSmallMaskShape.signature.{3,4} N P.c3 σ cs ps)

theorem fibre_small (P : Premises4) (N : Interp.{4}) (σ : Nat → Nat)
    (cs : List PiValueRule.Constructor) (ps : List PSet.{4}) :
    ∀ k i, fibre P N σ cs ps k i ∈ W4 k ∧
      ¬ pempty ∈ fibre P N σ cs ps k i
  | 0, _ => ⟨(stageW4 P 0).empty, not_mem_pempty⟩
  | 1, i => (PiSmallMaskShape.component_stage_one P N σ cs ps).2 i
  | 2, i => (PiSmallMaskShape.component_stage_two P N σ cs ps).2 i
  | 3, i => (PiSmallMaskShape.component_stage_three P N σ cs ps).2 i
  | k + 4, i => (PiSmallMaskShape.component_stage_four_plus P N σ cs ps k).2 i

/-- The complete constructor code and complete output key are preserved
by selection of the exact stage's Choice data. -/
theorem fibre_produce (P : Premises4) (M N : Interp.{4})
    (hdec : M.dec = N.dec) (σ : Nat → Nat)
    (cs : List PiValueRule.Constructor) (ps : List PSet.{4})
    (f : Nat) (ls : List Level) (j : Fin cs.length) (xs : List PSet.{4})
    (k : Nat) (hk : k ≠ 0)
    (hx : TelFits M σ ((cs[j]).fields.map (PiValueRule.fieldExpr f ls))
      (push ps ρ0) xs)
    (hs : SmallAlong M σ (W4 k)
      ((cs[j]).fields.map (PiValueRule.fieldExpr f ls)) (push ps ρ0) xs)
    (hm : PiSmallMaskShape.TupleMask M N σ (cs[j]).fields
      (push ps ρ0) (push ps ρ0) xs)
    (hl : PiSmallMaskShape.Leaves M N σ f ls (fibre P N σ cs ps k)
      (cs[j]).fields (push ps ρ0) xs) :
    dataVal j.val xs ∈ fibre P N σ cs ps k
      (key (ps ++ (cs[j]).result.map (den N σ (push xs (push ps ρ0))))) := by
  cases k with
  | zero => exact (hk rfl).elim
  | succ k =>
      cases k with
      | zero =>
          exact PiSmallMaskShape.produce.{0,4} M N P.c0 hdec σ
            cs ps f ls j xs hx hs hm hl
      | succ k =>
          cases k with
          | zero =>
              exact PiSmallMaskShape.produce.{1,4} M N P.c1 hdec σ
                cs ps f ls j xs hx hs hm hl
          | succ k =>
              cases k with
              | zero =>
                  exact PiSmallMaskShape.produce.{2,4} M N P.c2 hdec σ
                    cs ps f ls j xs hx hs hm hl
              | succ k =>
                  exact PiSmallMaskShape.produce.{3,4} M N P.c3 hdec σ
                    cs ps f ls j xs hx hs hm hl

noncomputable def canonical (ar : Nat) (vs : List Nat) : List Nat :=
  (canonL ar).map (evalTotal (σOf vs))

theorem canonical_length (ar : Nat) (vs : List Nat) :
    (canonical ar vs).length = ar := by
  simp only [canonical, canonL, List.length_map, List.length_range]

theorem canonical_idem (ar : Nat) (vs : List Nat) :
    canonical ar (canonical ar vs) = canonical ar vs := by
  change (canonL ar).map (evalTotal (σOf (canonical ar vs))) = canonical ar vs
  simpa only [canonical_length] using
    StepDGOrder.canonL_map_σOf (canonical ar vs)

theorem canonical_agree (ar : Nat) (vs : List Nat) :
    ∀ i, i < ar → σOf vs i = σOf (canonical ar vs) i :=
  fun i hi => (σOf_canon (σOf vs) ar i hi).symm

/-- This intersection retains the original complete key. The bound is
only a carrier for separation; its exact smallness follows from one of
the universally required per-parameter fibres. -/
noncomputable def candidate (P : Premises4) (N : Interp.{4})
    (fd : FamData) (ar : Nat) (cs : List PiValueRule.Constructor) : Frame :=
  fun vs i =>
    let σ := σOf (canonical ar vs)
    let k := evalTotal σ fd.resLevel
    sep (fun z => ∀ ps : List PSet.{4}, key ps = paramKey fd.params.length i →
      z ∈ fibre P N σ cs ps k i) (W4 k)

theorem candidate_canonical (P : Premises4) (N : Interp.{4})
    (fd : FamData) (ar : Nat) (cs : List PiValueRule.Constructor)
    (vs : List Nat) (i : Index.{4}) :
    candidate P N fd ar cs (canonical ar vs) i = candidate P N fd ar cs vs i := by
  simp only [candidate, canonical_idem]

/-- Projection selects a supplied parameter list, never a chosen quotient
representative. No relationship between two compiled signatures is used. -/
theorem candidate_sub (P : Premises4) (N : Interp.{4})
    (fd : FamData) (ar : Nat) (cs : List PiValueRule.Constructor)
    (vs : List Nat) (i : Index.{4}) (ps : List PSet.{4})
    (hp : key ps = paramKey fd.params.length i) :
    Sub (candidate P N fd ar cs vs i)
      (fibre P N (σOf (canonical ar vs)) cs ps
        (evalTotal (σOf (canonical ar vs)) fd.resLevel) i) := by
  intro z hz
  dsimp only [candidate] at hz
  obtain ⟨a, h, he⟩ := mem_sep.mp hz
  exact mem_congr_left he (h ps hp)

/-- Eliminate the separating bound using one representative only inside
Prop. The converse therefore retains every parameter representative. -/
theorem candidate_mem_iff (P : Premises4) (N : Interp.{4})
    (fd : FamData) (ar : Nat) (cs : List PiValueRule.Constructor)
    (vs : List Nat) (i : Index.{4}) (z : PSet.{4}) :
    z ∈ candidate P N fd ar cs vs i ↔
      ∀ ps : List PSet.{4}, key ps = paramKey fd.params.length i →
        z ∈ fibre P N (σOf (canonical ar vs)) cs ps
          (evalTotal (σOf (canonical ar vs)) fd.resLevel) i := by
  constructor
  · intro hz ps hp
    exact candidate_sub P N fd ar cs vs i ps hp z hz
  · refine Quotient.inductionOn i ?_
    intro qs h
    have hz := h (qs.take fd.params.length) rfl
    obtain ⟨a, ha⟩ := (stageW4 P _).trans
      (fibre_small P N (σOf (canonical ar vs)) cs
        (qs.take fd.params.length) _ (key qs)).1 hz
    dsimp only [candidate]
    exact mem_sep.mpr ⟨a, fun ps hp => mem_congr_left ha.symm (h ps hp), ha⟩

/-- All universe vectors and all complete keys are admitted. Short and
extra universe vectors use the produced family-level bound. -/
theorem candidate_admissible (P : Premises4) (N : Interp.{4})
    (fd : FamData) (ar : Nat) (cs : List PiValueRule.Constructor)
    (hB : FamBounded fd ar) : Admissible fd (candidate P N fd ar cs) := by
  intro vs i
  have hk := evalTotal_agree (canonical_agree ar vs) fd.resLevel hB.res
  refine Quotient.inductionOn i ?_
  intro qs
  have hs := fibre_small P N (σOf (canonical ar vs)) cs
    (qs.take fd.params.length) (evalTotal (σOf (canonical ar vs)) fd.resLevel) (key qs)
  have hsub := candidate_sub P N fd ar cs vs (key qs) (qs.take fd.params.length) rfl
  refine ⟨?_, ?_⟩
  · rw [hk]
    exact (stageW4 P _).subset hs.1 hsub
  · by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
    · rw [if_pos h0]
      intro z hz
      have hzero : evalTotal (σOf (canonical ar vs)) fd.resLevel = 0 := hk.symm.trans h0
      have hz' := hsub z hz
      rw [hzero] at hz'
      exact (not_mem_pempty hz').elim
    · rw [if_neg h0]
      intro z hz he
      exact hs.2 (mem_congr_left he (hsub z hz))

universe u

/-- SmallAlong has the same family-level transport as TelFits. The
actual previous field values are retained at every dependent domain. -/
theorem smallAlong_levels (M : Interp.{u}) {σ τ : Nat → Nat} {ar : Nat}
    (h : ∀ i, i < ar → σ i = τ i) (W : PSet.{u}) :
    (ds : List (Expr Nat)) → ExprsBounded ar ds →
    (ρ : Nat → PSet.{u}) → (xs : List PSet.{u}) →
    (SmallAlong M σ W ds ρ xs ↔ SmallAlong M τ W ds ρ xs)
  | [], _, _, _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | A :: ds, hb, ρ, x :: xs => by
      change (Ed M (den M σ ρ A) ∈ W ∧ _) ↔
        (Ed M (den M τ ρ A) ∈ W ∧ _)
      rw [den_levels_agree M h A (hb A (List.mem_cons_self _ _)) ρ,
        smallAlong_levels M h W ds
          (fun e he => hb e (List.mem_cons_of_mem _ he)) (vcons x ρ) xs]

/-- The literal constructor record transports to the canonical family
world at every original vector; no full-vector length premise is needed. -/
theorem ctorAt_canonical (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar) (C : Frame)
    (vs : List Nat) (i : Index.{4}) (z : PSet.{4})
    (hz : CtorAt P μ fd C vs i z) :
    CtorAt P μ fd C (canonical ar vs) i z := by
  obtain ⟨j, ps, xs, hp, hx, hs, hi, he⟩ := hz
  let M := mkM P (table P μ fd C)
  have hσ := canonical_agree ar vs
  have hk := evalTotal_agree hσ fd.resLevel hB.res
  have hc : fd.ctors.get j ∈ fd.ctors := List.getElem_mem j.isLt
  have hb := hB.ctors _ hc
  refine ⟨j, ps, xs, (TelFits_levels M hσ _ hB.params ρ0 ps).mp hp,
    (TelFits_levels M hσ _ hb.1 (push ps ρ0) xs).mp hx, ?_, ?_, ?_⟩
  · by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
    · have hzero := hk.symm.trans h0
      rw [if_pos hzero]
      trivial
    · have hn : evalTotal (σOf (canonical ar vs)) fd.resLevel ≠ 0 :=
        fun h => h0 (hk.trans h)
      rw [if_neg h0] at hs
      rw [if_neg hn]
      rw [hk] at hs
      exact (smallAlong_levels M hσ _ _ hb.1 (push ps ρ0) xs).mp hs
  · rw [← map_den_levels M hσ _ hb.2]
    exact hi
  · rw [← hk]
    exact he

end Rcic.F3.PSet.PiSmallFrame
