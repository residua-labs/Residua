import rcic.RcicF3Denote

/-!
# F3 S3: semantic lemmas for soundness

Graph application against dependent products (`fapp_mem_piSet`,
`mkLam_mem_piSet`), dichotomy of the element sets the model builds
(`dich_piSet`, `dich_tv`, `dich_ed`), and the normalized element sets of
products (`ed_piVal`). closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- A functional graph applies to the unique partner. -/
theorem fapp_eq_of_uniq {F a b : PSet.{T}}
    (hu : ∀ a b b', ordPair a b ∈ F → ordPair a b' ∈ F → Equiv b b')
    (hab : ordPair a b ∈ F) : Equiv (fapp F a) b := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨t, ht, hz'⟩ := mem_sUnion.mp hz
    obtain ⟨⟨i, hi⟩, ht'⟩ := ht
    have hb : Equiv ((sUnion (sUnion F)).Func i) b := hu a _ b hi hab
    exact mem_congr_right (ht'.symm.trans hb) hz'
  · intro hz
    obtain ⟨i, hi⟩ := mem_sUnion_sUnion_of_pair hab
    have hQi : ordPair a ((sUnion (sUnion F)).Func i) ∈ F :=
      mem_congr_left (ordPair_congr Equiv.rfl hi.symm) hab
    refine mem_sUnion.mpr ⟨(sUnion (sUnion F)).Func i, ⟨⟨i, hQi⟩, Equiv.refl _⟩, ?_⟩
    exact mem_congr_right hi.symm hz

theorem isFuncOnDep_of_mem_piSet {A f : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a')) (hf : f ∈ piSet A B) : isFuncOnDep A B f := by
  obtain ⟨i, hp, hi⟩ := mem_sep.mp hf
  exact isFuncOnDep_equiv Equiv.rfl hB hi hp

/-- **The λ-IH graph domain is the denoted domain.** A member of a dependent
product is a functional graph on `A`, so `sImage pfst f` — the domain `ihAt`'s
pi-case puts inside `mkLam` — is `≈ A`. For a pi field, `piVal`'s functional
branch is `piSet (Ed M (den D')) _`, so this is `sImage pfst x ≈ Ed M (den D')`. -/
theorem sImage_pfst_of_mem_piSet {A f : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a')) (hf : f ∈ piSet A B) :
    Equiv (sImage pfst f) A :=
  sImage_pfst_of_isFuncOnDep (isFuncOnDep_of_mem_piSet hB hf)

/-- Application of a member of a dependent product lands in the fibre. -/
theorem fapp_mem_piSet {A f a : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a')) (hf : f ∈ piSet A B) (ha : a ∈ A) :
    fapp f a ∈ B a := by
  have hF := isFuncOnDep_of_mem_piSet hB hf
  obtain ⟨b, hb, hab⟩ := hF.1 a ha
  exact mem_congr_left (fapp_eq_of_uniq hF.2.2 hab).symm hb

/-- A graph of a fibre-valued, `≈`-respecting map is a member of the
dependent product. -/
theorem mkLam_mem_piSet {A : PSet.{T}} {B g : PSet.{T} → PSet.{T}}
    (hg : ∀ a a', Equiv a a' → Equiv (g a) (g a')) (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a'))
    (hval : ∀ x, x ∈ A → g x ∈ B x) : mkLam g A ∈ piSet A B := by
  have hfun : isFuncOnDep A B (mkLam g A) := by
    refine ⟨fun a ha => ?_, fun p hp => ?_, fun a b b' h1 h2 => ?_⟩
    · obtain ⟨i, hi⟩ := ha
      exact ⟨g a, hval a ⟨i, hi⟩, ⟨i, ordPair_congr hi (hg _ _ hi)⟩⟩
    · obtain ⟨i, hi⟩ := hp
      exact ⟨A.Func i, ⟨i, Equiv.refl _⟩, g (A.Func i), hval _ ⟨i, Equiv.refl _⟩, hi.symm⟩
    · obtain ⟨i, hi⟩ := h1
      obtain ⟨j, hj⟩ := h2
      obtain ⟨hai, hbi⟩ := ordPair_equiv hi
      obtain ⟨haj, hbj⟩ := ordPair_equiv hj
      exact hbi.symm.trans ((hg _ _ (hai.trans haj.symm)).trans hbj)
  have hpow : mkLam g A ∈ powerset (prod A (sUnion (sImage B A))) := by
    refine Subset_mem_powerset fun p hp => ?_
    obtain ⟨a, ha, b, hb, hpe⟩ := hfun.2.1 p hp
    obtain ⟨i, hi⟩ := ha
    refine mem_prod.mpr ⟨a, ⟨i, hi⟩, b, mem_sUnion.mpr ⟨B (A.Func i), ⟨i, Equiv.refl _⟩,
      mem_congr_right (hB _ _ hi.symm) hb⟩, hpe⟩
  obtain ⟨i, hi⟩ := hpow
  exact mem_sep.mpr ⟨i, isFuncOnDep_equiv Equiv.rfl hB hi.symm hfun, hi⟩
where
  Subset_mem_powerset {x s : PSet.{T}} (h : ∀ y, y ∈ x → y ∈ s) : x ∈ powerset s :=
    mem_powerset.mpr h

theorem dich_tv (φ : Prop) : Dich (tv.{T} φ) := Or.inl fun _ hy => (mem_tv.mp hy).2

/-- Dependent products are dichotomous: over an inhabited domain no member
is `∅`, over an empty one the only member is `∅`. -/
theorem dich_piSet (dec : ∀ p : Prop, Decidable p) {A : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a')) : Dich (piSet A B) := by
  by_cases hA : ∃ a, a ∈ A
  · obtain ⟨a, ha⟩ := hA
    refine Or.inr fun h0 => ?_
    obtain ⟨b, _, hab⟩ := (isFuncOnDep_of_mem_piSet hB h0).1 a ha
    exact not_mem_pempty hab
  · refine Or.inl fun f hf => ext fun z => ⟨fun hz => ?_, fun hz => (not_mem_pempty hz).elim⟩
    obtain ⟨a, ha, _, _, _⟩ := (isFuncOnDep_of_mem_piSet hB hf).2.1 z hz
    exact (hA ⟨a, ha⟩).elim

theorem ed_of_dich (M : Interp.{T}) {t : PSet.{T}} (h : Dich (El t)) : Ed M t = El t :=
  cond_pos h _ _

theorem dich_ed (M : Interp.{T}) (t : PSet.{T}) : Dich (Ed M t) := by
  haveI := M.dec
  by_cases h : Dich (El t)
  · rw [ed_of_dich M h]; exact h
  · show Dich (cond M.dec (Dich (El t)) (El t) pempty)
    rw [cond_neg h]
    exact Or.inr not_mem_pempty

theorem ed_tyv (M : Interp.{T}) {S : PSet.{T}} (h : Dich S) : Equiv (Ed M (tyv S)) S := by
  have h' : Dich (El (tyv S)) := (dich_congr el_tyv).mpr h
  rw [ed_of_dich M h']
  exact el_tyv

/-- The normalized element set of a product's value. -/
theorem ed_piVal (M : Interp.{T}) (A : PSet.{T}) (B : PSet.{T} → PSet.{T})
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a')) :
    Equiv (Ed M (piVal M A B)) (cond M.dec (PiProp M A B)
      (tv (∀ x, x ∈ Ed M A → pempty ∈ Ed M (B x))) (piSet (Ed M A) (fun x => Ed M (B x)))) := by
  apply ed_tyv
  haveI := M.dec
  by_cases h : PiProp M A B
  · rw [cond_pos h]; exact dich_tv _
  · rw [cond_neg h]; exact dich_piSet M.dec (fun a a' e => ed_congr M (hB a a' e))

end PSet

end Rcic.F3
