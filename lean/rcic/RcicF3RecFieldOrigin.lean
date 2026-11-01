import rcic.RcicF3PiGraphInversion
import rcic.RcicF3DataNotPi

/-!
# A proof-valued recursive origin relation

The relation records the decoded source and enlarged type, the SAME actual
value, and its remaining Pi depth. Its Pi constructor retains actual
semantic Pi types and a proof for every reached child. It selects no
per-argument telescope, and its empty case permits erased branches.

Type-set equality forces an origin value to be empty. In the Pi case this
uses actual product membership and dichotomy of every decoded codomain:
empty function outputs force PiProp, hence the erased member is empty.
Raw graph eta alone would not justify that conclusion.

The application theorem consumes actual Pi membership and argument fit.
It is a case of the planned bounded masking induction, not that induction
or an all-vector admitted domain-mask producer. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldOrigin
open Rcic.Declarative RawFamily PiIndex

inductive Origin (M : Interp.{4}) (fd : FamData) (C : Frame) :
    Nat → PSet.{4} → PSet.{4} → PSet.{4} → Prop where
  | empty {m S T z} (h : Equiv z pempty) : Origin M fd C m S T z
  | leaf {S T z} (vs : List Nat) (i : Index.{4})
      (h0 : evalTotal (σOf vs) fd.resLevel ≠ 0)
      (hS : Equiv S (C vs i))
      (hT : Equiv T (RawFamilyEnlarge.enlarge fd C vs i)) :
      Origin M fd C 0 S T z
  | pi {m S T z} (A : PSet.{4}) (B B' : PSet.{4} → PSet.{4})
      (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a'))
      (hB' : ∀ a a', Equiv a a' → Equiv (B' a) (B' a'))
      (hS : Equiv S (Ed M (piVal M A B)))
      (hT : Equiv T (Ed M (piVal M A B')))
      (children : ∀ a, a ∈ Ed M A →
        Origin M fd C m (Ed M (B a)) (Ed M (B' a)) (fapp z a)) :
      Origin M fd C (m + 1) S T z

/-- Conversion changes the type representatives, not the complete leaf
key. Equivalent values have equivalent applications at every reached a. -/
theorem Origin.transport {M : Interp.{4}} {fd : FamData} {C : Frame}
    {m : Nat} {S T z S' T' z' : PSet.{4}}
    (h : Origin M fd C m S T z)
    (eS : Equiv S S') (eT : Equiv T T') (ez : Equiv z z') :
    Origin M fd C m S' T' z' := by
  induction h generalizing S' T' z' with
  | empty h => exact .empty (ez.symm.trans h)
  | leaf vs i h0 hS hT =>
      exact .leaf vs i h0 (eS.symm.trans hS) (eT.symm.trans hT)
  | pi A B B' hB hB' hS hT children ih =>
      apply Origin.pi A B B' hB hB' (eS.symm.trans hS) (eT.symm.trans hT)
      intro a ha
      exact ih a ha Equiv.rfl Equiv.rfl (fapp_congr ez Equiv.rfl)

/-- Equality of decoded source and enlarged types eliminates every
nonempty recursive origin, including arbitrarily deep erased products. -/
theorem separator {M : Interp.{4}} {fd : FamData} {C : Frame}
    {m : Nat} {S T z : PSet.{4}}
    (h : Origin M fd C m S T z) (hz : z ∈ S) (e : Equiv S T) :
    Equiv z pempty := by
  revert hz e
  induction h with
  | empty h => intro _ _; exact h
  | leaf vs i h0 hS hT =>
      intro _ e
      exact (RawFamilyEnlarge.strict fd C vs i h0
        (hS.symm.trans (e.trans hT))).elim
  | @pi m S T z A B B' hB hB' hS hT children ih =>
      intro hz e
      cases M.dec (Equiv z pempty) with
      | isTrue hz0 => exact hz0
      | isFalse hz0 =>
          have hg : z ∈ Ed M (piVal M A B) := mem_congr_right hS hz
          have he := PiGraphInversion.elements M A A z B B' hB hB'
            (hS.symm.trans (e.trans hT)) hg hz0
          have hp : PiProp M A B := by
            intro a ha y hy
            have hv := app_mem M hB hg ha
            have hv0 := ih a ha hv (he.2 a ha)
            have hzero : pempty ∈ Ed M (B a) := mem_congr_left hv0 hv
            rcases dich_ed M (B a) with hprop | hdata
            · exact hprop y hy
            · exact (hdata hzero).elim
          have hmem := mem_congr_right (ed_piVal M A B hB) hg
          rw [cond_pos hp] at hmem
          exact (mem_tv.mp hmem).2

/-- A depth-zero DATA origin cannot have a Pi type in the enlarged
model. Its explicit spike rules out every target Pi, including Prop Pi. -/
theorem zero_application_empty {M : Interp.{4}} {fd : FamData} {C : Frame}
    {S T z : PSet.{4}} (h : Origin M fd C 0 S T z)
    (A : PSet.{4}) (B : PSet.{4} → PSet.{4})
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a'))
    (he : Equiv T (Ed M (piVal M A B))) : Equiv z pempty := by
  cases h with
  | empty hz => exact hz
  | leaf vs i h0 hS hT =>
      have hz : RawFamilyEnlarge.spike (C vs i) ∈
          RawFamilyEnlarge.enlarge fd C vs i := by
        rw [RawFamilyEnlarge.enlarge, if_neg h0]
        exact mem_insert.mpr (Or.inl Equiv.rfl)
      exact (DataNotPi.dataVal_not_piVal M 0 [C vs i] A B hB
        (mem_congr_right he (mem_congr_right hT.symm hz))).elim

/-- The actual argument reaches the same origin domain in both models.
Pi inversion transports the child relation to the two expected codomains. -/
theorem successor_application {M : Interp.{4}} {fd : FamData} {C : Frame}
    {m : Nat} {A A' z a : PSet.{4}} {B B' : PSet.{4} → PSet.{4}}
    (hB : ∀ x y, Equiv x y → Equiv (B x) (B y))
    (hB' : ∀ x y, Equiv x y → Equiv (B' x) (B' y))
    (h : Origin M fd C (m + 1)
      (Ed M (piVal M A B)) (Ed M (piVal M A' B')) z)
    (hz : z ∈ Ed M (piVal M A B))
    (hz' : z ∈ Ed M (piVal M A' B')) (ha : a ∈ Ed M A) :
    Origin M fd C m (Ed M (B a)) (Ed M (B' a)) (fapp z a) := by
  cases h with
  | empty h0 =>
      exact .empty ((fapp_congr h0 Equiv.rfl).trans (fapp_pempty a))
  | pi A0 C0 D0 hC0 hD0 hS hT children =>
      cases M.dec (Equiv z pempty) with
      | isTrue h0 =>
          exact .empty ((fapp_congr h0 Equiv.rfl).trans (fapp_pempty a))
      | isFalse h0 =>
          have hleft := PiGraphInversion.elements M A0 A z C0 B hC0 hB
            hS.symm (mem_congr_right hS hz) h0
          have hright := PiGraphInversion.elements M A0 A' z D0 B' hD0 hB'
            hT.symm (mem_congr_right hT hz') h0
          have ha0 : a ∈ Ed M A0 := mem_congr_right hleft.1.symm ha
          exact (children a ha0).transport (hleft.2 a ha0) (hright.2 a ha0) Equiv.rfl

/-- This is the origin-head application case at every remaining depth.
Neither the argument's mask nor its child/result key is restricted. -/
theorem application {M : Interp.{4}} {fd : FamData} {C : Frame}
    {m : Nat} {A A' z a : PSet.{4}} {B B' : PSet.{4} → PSet.{4}}
    (hB : ∀ x y, Equiv x y → Equiv (B x) (B y))
    (hB' : ∀ x y, Equiv x y → Equiv (B' x) (B' y))
    (h : Origin M fd C m
      (Ed M (piVal M A B)) (Ed M (piVal M A' B')) z)
    (hz : z ∈ Ed M (piVal M A B))
    (hz' : z ∈ Ed M (piVal M A' B')) (ha : a ∈ Ed M A) :
    Origin M fd C (m - 1) (Ed M (B a)) (Ed M (B' a)) (fapp z a) := by
  cases m with
  | zero =>
      have h0 := zero_application_empty h A' B' hB' Equiv.rfl
      exact .empty ((fapp_congr h0 Equiv.rfl).trans (fapp_pempty a))
  | succ m => exact successor_application hB hB' h hz hz' ha

end Rcic.F3.PSet.RecFieldOrigin
