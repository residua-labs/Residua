import rcic.RcicF3KTWFamSem

/-!
# F3 S7 KT-2b-3c-3a part C: `TypeFib` as truncated fits

`TelFitsT` is `TelFits` with each field's `Ed` domain truncated to the stage
`W k`; `mem_FitSetT_iff`/`mem_BoundT_iff`/`mem_TypeFib_iff` read the bounding
sets as truncated fits.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe T

namespace PSet

open Rcic.Declarative

/-- `TelFits` with every field's `Ed` domain truncated to `W k`. -/
def TelFitsT (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) :
    List (Expr Nat) → (Nat → PSet.{T}) → List PSet.{T} → Prop
  | [], _, [] => True
  | A :: Ds, ρ, x :: xs =>
      x ∈ truncW M W k (Ed M (den M σ ρ A)) ∧ TelFitsT M W k σ Ds (vcons x ρ) xs
  | _, _, _ => False

/-- Membership in the truncated set is membership in the untruncated set. -/
theorem truncW_sub {M : Interp.{T}} {W : Nat → PSet.{T}} {k : Nat} {S x : PSet.{T}}
    (h : x ∈ truncW M W k S) : x ∈ S := by
  unfold truncW cond at h
  split at h
  · exact h
  · exact absurd h not_mem_pempty

theorem TelFitsT.length {M : Interp.{T}} {W : Nat → PSet.{T}} {k : Nat} {σ : Nat → Nat} :
    {Ds : List (Expr Nat)} → {ρ : Nat → PSet.{T}} → {xs : List PSet.{T}} →
    TelFitsT M W k σ Ds ρ xs → xs.length = Ds.length
  | [], _, [], _ => rfl
  | _ :: _, _, _ :: _, ⟨_, h⟩ => congrArg Nat.succ (TelFitsT.length h)

theorem TelFitsT.telFits {M : Interp.{T}} {W : Nat → PSet.{T}} {k : Nat} {σ : Nat → Nat} :
    {Ds : List (Expr Nat)} → {ρ : Nat → PSet.{T}} → {xs : List PSet.{T}} →
    TelFitsT M W k σ Ds ρ xs → TelFits M σ Ds ρ xs
  | [], _, [], _ => trivial
  | _ :: _, _, _ :: _, ⟨hx, h⟩ => ⟨truncW_sub hx, TelFitsT.telFits h⟩

/-- `TelFitsT` transports along `≈` environments and `LEq` value lists. -/
theorem TelFitsT_congr (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → {ρ ρ' : Nat → PSet.{T}} → (∀ i, Equiv (ρ i) (ρ' i)) →
    {xs xs' : List PSet.{T}} → LEq xs xs' →
    TelFitsT M W k σ Ds ρ xs → TelFitsT M W k σ Ds ρ' xs'
  | [], _, _, _, [], [], _, h => h
  | A :: Ds, ρ, ρ', hρ, x :: xs, x' :: xs', ⟨hx, hxs⟩, ⟨hm, h⟩ =>
      ⟨mem_congr_left hx (mem_congr_right (truncW_congr M W k
          (ed_congr M (den_congr M σ A hρ))) hm),
       TelFitsT_congr M W k σ Ds (vcons_congr hx hρ) hxs h⟩

/-- `FitSetT` is the set of truncated-fit tuples. -/
theorem mem_FitSetT_iff (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → {t : PSet.{T}} →
    (t ∈ FitSetT M W k σ Ds ρ ↔ ∃ xs, Equiv t (tup xs) ∧ TelFitsT M W k σ Ds ρ xs)
  | [], ρ, t => by
      constructor
      · intro h; exact ⟨[], mem_singleton.mp h, trivial⟩
      · rintro ⟨xs, hx, h⟩
        cases xs with
        | nil => exact mem_singleton.mpr hx
        | cons _ _ => exact False.elim h
  | A :: Ds, ρ, t => by
      constructor
      · intro h
        obtain ⟨s, hs, ht⟩ := mem_sUnion.mp h
        obtain ⟨i, hseq⟩ := mem_sImage.mp hs
        obtain ⟨j, hte⟩ := mem_sImage.mp (mem_congr_right hseq.symm ht)
        obtain ⟨xs, hxs, hfit⟩ := (mem_FitSetT_iff M W k σ Ds
          (vcons ((truncW M W k (Ed M (den M σ ρ A))).Func i) ρ)).mp ⟨j, Equiv.refl _⟩
        exact ⟨(truncW M W k (Ed M (den M σ ρ A))).Func i :: xs,
          hte.symm.trans (ordPair_congr Equiv.rfl hxs), ⟨⟨i, Equiv.refl _⟩, hfit⟩⟩
      · rintro ⟨xs, hx, h⟩
        cases xs with
        | nil => exact False.elim h
        | cons x xs =>
            obtain ⟨hxtr, hfit⟩ := h
            obtain ⟨ix, hix⟩ := hxtr
            obtain ⟨it, hit⟩ : tup xs ∈ FitSetT M W k σ Ds (vcons x ρ) :=
              (mem_FitSetT_iff M W k σ Ds (vcons x ρ)).mpr ⟨xs, Equiv.rfl, hfit⟩
            refine mem_sUnion.mpr
              ⟨sImage (fun t => ordPair x t) (FitSetT M W k σ Ds (vcons x ρ)), ⟨ix, ?_⟩, ⟨it, ?_⟩⟩
            · exact sImage_congr
                (fun a a' haa => ordPair_congr hix haa)
                (FitSetT_congr M W k σ Ds (vcons_congr hix (fun _ => Equiv.rfl)))
            · exact (ordPair_congr Equiv.rfl hit).trans hx.symm

/-- `BoundT` decomposes: membership means a data value of some constructor `j0 + i`. -/
theorem mem_BoundT_iff (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat)
    (ρp : Nat → PSet.{T}) : (j0 : Nat) →
    (cs : List (List (Expr Nat) × List (Expr Nat))) → {z : PSet.{T}} →
    (z ∈ BoundT M W k σ ρp j0 cs ↔ ∃ i c t, cs[i]? = some c ∧
      t ∈ FitSetT M W k σ c.1 ρp ∧ Equiv z (dataOfTup (j0 + i) t))
  | _, [], _ => by
      constructor
      · intro h; exact absurd h not_mem_pempty
      · rintro ⟨i, c, t, hc, -, -⟩; exact Option.noConfusion hc
  | j0, c' :: cs, _ => by
      constructor
      · intro h
        obtain ⟨s, hs, hz⟩ := mem_sUnion.mp h
        rcases mem_pair.mp hs with hl | hr
        · obtain ⟨i, hts⟩ := mem_sImage.mp (mem_congr_right hl hz)
          refine ⟨0, c', _, ?_, ⟨i, Equiv.refl _⟩, hts.symm⟩
          rw [List.getElem?_cons_zero]
        · obtain ⟨i, c, t, hc, ht, hze⟩ :=
            (mem_BoundT_iff M W k σ ρp (j0 + 1) cs).mp (mem_congr_right hr hz)
          refine ⟨i + 1, c, t, ?_, ht, ?_⟩
          · rw [List.getElem?_cons_succ]; exact hc
          · have heq : j0 + (i + 1) = j0 + 1 + i := by omega
            rw [heq]; exact hze
      · rintro ⟨i, c, t, hc, ht, hze⟩
        cases i with
        | zero =>
            have hcc : c' = c := by
              have hh := hc
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hh
              exact hh
            subst hcc
            obtain ⟨i', hi'⟩ := ht
            exact mem_sUnion.mpr ⟨_, mem_pair.mpr (Or.inl Equiv.rfl),
              mem_congr_left hze.symm ⟨i', dataOfTup_congr j0 hi'⟩⟩
        | succ i =>
            have hc' : cs[i]? = some c := by
              rw [List.getElem?_cons_succ] at hc; exact hc
            have heq : j0 + 1 + i = j0 + (i + 1) := by omega
            rw [← heq] at hze
            exact mem_sUnion.mpr ⟨_, mem_pair.mpr (Or.inr Equiv.rfl),
              (mem_BoundT_iff M W k σ ρp (j0 + 1) cs).mpr ⟨i, c, t, hc', ht, hze⟩⟩

/-- `TypeFib` read as truncated fits with exact result indices. -/
theorem mem_TypeFib_iff (M : Interp.{T}) (W : Nat → PSet.{T}) (k : Nat) (σ : Nat → Nat)
    (cs : List (List (Expr Nat) × List (Expr Nat))) (ρp : Nat → PSet.{T})
    (is : List PSet.{T}) {z : PSet.{T}} :
    z ∈ TypeFib M W k σ cs ρp is ↔
    ∃ j c xs, cs[j]? = some c ∧ TelFitsT M W k σ c.1 ρp xs ∧
      LEq (c.2.map (den M σ (push xs ρp))) is ∧ Equiv z (dataVal j xs) := by
  unfold TypeFib
  constructor
  · intro h
    obtain ⟨i, ⟨j, xs, ⟨c, hc, htf, hle⟩, hiz'⟩, hiz⟩ := mem_sep.mp h
    obtain ⟨i', c', t, hc', ht', hmem⟩ :=
      (mem_BoundT_iff M W k σ ρp 0 cs).mp ⟨i, Equiv.refl _⟩
    rw [Nat.zero_add] at hmem
    have h1 : Equiv (dataOfTup i' t) (dataOfTup j (tup xs)) := hmem.symm.trans hiz'
    obtain ⟨_, h2⟩ := ordPair_equiv h1
    obtain ⟨hjtag, htup⟩ := ordPair_equiv h2
    have hij : i' = j := ord_inj hjtag
    subst hij
    obtain ⟨xs', hts', hfit'⟩ := (mem_FitSetT_iff M W k σ c'.1 ρp).mp ht'
    have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
    subst hcc
    have hlen : xs'.length = xs.length :=
      (TelFitsT.length hfit').trans (TelFits.length htf).symm
    have hxs : LEq xs' xs := tup_inj hlen (hts'.symm.trans htup)
    exact ⟨_, _, _, hc', TelFitsT_congr M W k σ _ (fun _ => Equiv.rfl) hxs hfit',
      hle, hiz.symm.trans (hmem.trans (dataOfTup_congr _ htup))⟩
  · rintro ⟨j, c, xs, hc, hfit, hle, hze⟩
    obtain ⟨i, hi⟩ : dataVal j xs ∈ BoundT M W k σ ρp 0 cs := by
      refine (mem_BoundT_iff M W k σ ρp 0 cs).mpr ⟨j, c, tup xs, hc,
        (mem_FitSetT_iff M W k σ c.1 ρp).mpr ⟨xs, Equiv.rfl, hfit⟩, ?_⟩
      rw [Nat.zero_add]; exact Equiv.rfl
    exact mem_sep.mpr ⟨i, ⟨j, xs, ⟨c, hc, hfit.telFits, hle⟩, hi⟩, hi.trans hze.symm⟩

end PSet

end Rcic.F3
