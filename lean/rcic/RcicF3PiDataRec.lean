import rcic.RcicF3PiSmallProducer
import rcic.RcicF3PiRecBridge
/-!
# Data recursor soundness for small indexed signatures

Membership well-founded induction produces mapping soundness from local
constructor equations and typed minors. The motive retains the actual major
and result index. `produce_depth` connects semantic IHs to the existing
`ihAtN` at arbitrary depths, discharging leaf erasure from the data face.

The signature must encode every recursive field below its constructor;
literal dataVal payloads supply this structural condition. The constructor
equation and typed minors are local contracts, not global recursive-map
premises. Raw signature/minor extraction and group production remain open.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiDataRec
universe v
open PiSmallCompile PiSmallField PiSmallProducer

theorem produce {I : Type v} (M : Interp.{4}) (S : Sig I)
    (hS : CodeDich S) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hchild : ∀ s f k, MemT (f k) (S.code s f))
    (C : I → PSet.{4} → PSet.{4}) (hC : ∀ i z, Dich (C i z))
    (hresp : ∀ i x y, Equiv x y → Equiv (C i x) (C i y))
    (g : PSet.{4} → PSet.{4}) (hg : ∀ x y, Equiv x y → Equiv (g x) (g y))
    (minor : (s : S.Sh) → (S.Field s → PSet.{4}) →
      (S.Field s → PSet.{4}) → PSet.{4})
    (hminor : ∀ s f ih,
      (∀ k, f k ∈ Ed M ((widen (S.tel s k)).erasedType M (family M S))) →
      (∀ k, ih k ∈ Ed M ((widen (S.tel s k)).erasedIHType M C (f k))) →
      minor s f ih ∈ C (S.out s) (S.code s f))
    (heq : ∀ s f,
      (∀ k, f k ∈ Ed M ((widen (S.tel s k)).erasedType M (family M S))) →
      Equiv (g (S.code s f))
        (minor s f (fun k => (widen (S.tel s k)).erasedIH M g (f k)))) :
    ∀ i z, z ∈ family M S i → g z ∈ C i z := by
  have key : ∀ z i, z ∈ family M S i → g z ∈ C i z := by
    intro z
    induction z using memT_wf.induction with
    | h z ih =>
      intro i hz
      obtain ⟨s, f, hf, he, hi⟩ := cases_mem M S hS hD i hz
      subst i
      have hih : ∀ k, (widen (S.tel s k)).erasedIH M g (f k) ∈
          Ed M ((widen (S.tel s k)).erasedIHType M C (f k)) := by
        intro k
        exact (widen (S.tel s k)).erasedIH_mem_below M
          (widen_dich (S.tel s k) (hD s k))
          (family M S) (family_dich M S hS) C hC g z
          (fun j y hy hj => ih y hy j hj) (hf k)
          ((hchild s f k).congr_right he.symm)
      have hm := hminor s f
        (fun k => (widen (S.tel s k)).erasedIH M g (f k)) hf hih
      exact mem_congr_right (hresp (S.out s) (S.code s f) z he.symm)
        (mem_congr_left ((hg z (S.code s f) he).trans (heq s f hf)).symm hm)
  intro i z hz
  exact key z i hz

theorem produce_depth {I : Type v} (M : Interp.{4}) (S : Sig I)
    (hData : ∀ s f, ¬ Equiv (S.code s f) pempty)
    (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hchild : ∀ s f k, MemT (f k) (S.code s f))
    (C : I → PSet.{4} → PSet.{4}) (hC : ∀ i z, Dich (C i z))
    (hresp : ∀ i x y, Equiv x y → Equiv (C i x) (C i y))
    (g : PSet.{4} → PSet.{4}) (hg : ∀ x y, Equiv x y → Equiv (g x) (g y))
    (minor : (s : S.Sh) → (S.Field s → PSet.{4}) →
      (S.Field s → PSet.{4}) → PSet.{4})
    (hminorResp : ∀ s f a b, (∀ k, Equiv (a k) (b k)) →
      Equiv (minor s f a) (minor s f b))
    (hminor : ∀ s f ih,
      (∀ k, f k ∈ Ed M ((widen (S.tel s k)).erasedType M (family M S))) →
      (∀ k, ih k ∈ Ed M ((widen (S.tel s k)).erasedIHType M C (f k))) →
      minor s f ih ∈ C (S.out s) (S.code s f))
    (heq : ∀ s f,
      (∀ k, f k ∈ Ed M ((widen (S.tel s k)).erasedType M (family M S))) →
      Equiv (g (S.code s f))
        (minor s f (fun k => ihAtN g (S.depth s k) (f k)))) :
    ∀ i z, z ∈ family M S i → g z ∈ C i z := by
  have hp : ∀ i, pempty ∈ family M S i → Equiv (g pempty) pempty := by
    intro i hz
    obtain ⟨s, f, _, he, _⟩ := cases_mem M S (Or.inr hData) hD i hz
    exact (hData s f he.symm).elim
  apply produce M S (Or.inr hData) hD hchild C hC hresp g hg minor hminor
  intro s f hf
  exact (heq s f hf).trans (hminorResp s f _ _ (fun k =>
    ((widen (S.tel s k)).erasedIH_eq_ihAtN M
      (widen_dich (S.tel s k) (hD s k)) (family M S)
      (family_dich M S (Or.inr hData)) g hg hp (hf k)).symm))
end Rcic.F3.PSet.PiDataRec
