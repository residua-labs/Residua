import rcic.RcicF3PiDataRec
import rcic.RcicF3PiRecPlan
import rcic.RcicF3PiSmallAttack
import rcic.RcicF3PiPropRec
/-! Actual W recursor with a typed recursive-copy minor. The proof pays
field and IH membership at the height-omega witness, at every reference label.
Wrong constructor tags are excluded for every payload. This is a semantic
component, not the universal raw-group producer. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiDataRecAttack
open Rcic.Declarative PiSmallCompile PiSmallProducer PiSmallAttack

def wMinor (ms : List PSet.{4}) : (s : wSig.Sh) →
    (wSig.Field s → PSet.{4}) → (wSig.Field s → PSet.{4}) → PSet.{4}
  | ⟨.leaf⟩, _, _ => ms.getD 0 pempty
  | ⟨.node⟩, f, ih => fapps (ms.getD 1 pempty) [f .unit, ih .unit]

theorem w_core_sound (M : Interp.{4}) (r : Nat) (ms : List PSet.{4})
    (C : PUnit.{1} → PSet.{4} → PSet.{4}) (hC : ∀ i z, Dich (C i z))
    (hresp : ∀ i x y, Equiv x y → Equiv (C i x) (C i y))
    (hLeaf : ms.getD 0 pempty ∈ C .unit (dataVal 0 []))
    (hNode : ∀ f ih,
      f ∈ Ed M ((widen wTel).erasedType M (family M wSig)) →
      ih ∈ Ed M ((widen wTel).erasedIHType M C f) →
      fapps (ms.getD 1 pempty) [f, ih] ∈ C .unit (dataVal 1 [f])) :
    ∀ z, z ∈ family M wSig .unit →
      RecPlan.core M r [[], [.recursive 1]] ms z ∈ C .unit z := by
  have hdata : ∀ s f, ¬ Equiv (wSig.code s f) pempty := by
    intro ⟨s⟩ f
    cases s <;> exact dataVal_ne_pempty _ _
  have hchild : ∀ s f k, MemT (f k) (wSig.code s f) := by
    intro ⟨s⟩ f k
    cases s with
    | leaf => exact PEmpty.elim k
    | node => cases k; exact memT_dataVal (by simp)
  have hmResp : ∀ s f a b, (∀ k, Equiv (a k) (b k)) →
      Equiv (wMinor ms s f a) (wMinor ms s f b) := by
    intro ⟨s⟩ f a b h
    cases s with
    | leaf => exact Equiv.rfl
    | node => exact fapps_congr_args _ ⟨Equiv.rfl, h .unit, trivial⟩
  have hm : ∀ s f ih,
      (∀ k, f k ∈ Ed M ((widen (wSig.tel s k)).erasedType M (family M wSig))) →
      (∀ k, ih k ∈ Ed M ((widen (wSig.tel s k)).erasedIHType M C (f k))) →
      wMinor ms s f ih ∈ C (wSig.out s) (wSig.code s f) := by
    intro ⟨s⟩ f ih hf hh
    cases s with
    | leaf => exact hLeaf
    | node => exact hNode _ _ (hf .unit) (hh .unit)
  have heq : ∀ s f,
      (∀ k, f k ∈ Ed M ((widen (wSig.tel s k)).erasedType M (family M wSig))) →
      Equiv (RecPlan.core M r [[], [.recursive 1]] ms (wSig.code s f))
        (wMinor ms s f (fun k => ihAtN (RecPlan.core M r [[], [.recursive 1]] ms)
          (wSig.depth s k) (f k))) := by
    intro ⟨s⟩ f hf
    cases s with
    | leaf => exact RecPlan.core_data_mem.{4,0} M r [[], [.recursive 1]] ms (j := 0) (ss := []) (xs := []) rfl trivial
    | node =>
      have hm : RecPlan.FieldsMem.{4,0} M [.recursive 1] [f .unit] :=
        ⟨⟨PUnit, widen wTel, family M wSig,
          PiSmallField.widen_dich wTel (wInvariants.2 ⟨.node⟩ .unit), hf .unit⟩, trivial⟩
      exact RecPlan.core_data_mem.{4,0} M r [[], [.recursive 1]] ms (j := 1) (ss := [.recursive 1]) (xs := [f .unit]) rfl hm
  intro z hz
  exact PiDataRec.produce_depth M wSig hdata wInvariants.2 hchild C hC hresp
    (RecPlan.core M r [[], [.recursive 1]] ms)
    (recCore_resp M (RecPlan.descriptor r [[], [.recursive 1]]) ms)
    (wMinor ms) hmResp hm heq .unit z hz

def wA (M : Interp.{4}) : PSet.{4} :=
  (widen wTel).erasedType M (family M wSig)
def wCopyMinor (M : Interp.{4}) : PSet.{4} :=
  lamVal M (wA M) (fun _ => lamVal M (wA M) (fun ih => dataVal 1 [ih]))
def wCopyMinors (M : Interp.{4}) : List PSet.{4} := [dataVal 0 [], wCopyMinor M]

theorem w_copy_node (P : Premises4) (M : Interp.{4}) (f ih : PSet.{4})
    (hf : f ∈ Ed M (wA M))
    (hih : ih ∈ Ed M ((widen wTel).erasedIHType M (fun i _ => family M wSig i) f)) :
    fapps ((wCopyMinors M).getD 1 pempty) [f, ih] ∈ family M wSig .unit := by
  rw [RecTel.erasedIHType_const] at hih
  have hfirst : Equiv (fapp (wCopyMinor M) f)
      (lamVal M (wA M) (fun ih => dataVal 1 [ih])) :=
    beta_val M (fun _ _ _ => Equiv.rfl) hf
  have hsecond : Equiv (fapp (lamVal M (wA M) (fun ih => dataVal 1 [ih])) ih)
      (dataVal 1 [ih]) :=
    beta_val M (fun _ _ h => dataVal_congr 1 ⟨h, trivial⟩) hih
  have he : Equiv (fapps ((wCopyMinors M).getD 1 pempty) [f, ih])
      (dataVal 1 [ih]) :=
    (fapp_congr hfirst Equiv.rfl).trans hsecond
  have hc := PiSmallProducer.produce M P.c3 wSig wInvariants.1 wInvariants.2
    ⟨.node⟩ (fun _ => ih) (fun _ => hih)
  exact mem_congr_left he.symm hc

theorem w_copy_sound (P : Premises4) (M : Interp.{4}) (r : Nat) :
    ∀ z, z ∈ family M wSig .unit →
      RecPlan.core M r [[], [.recursive 1]] (wCopyMinors M) z ∈ family M wSig .unit := by
  have hleaf : dataVal 0 [] ∈ family M wSig .unit :=
    PiSmallProducer.produce M P.c3 wSig wInvariants.1 wInvariants.2
      ⟨.leaf⟩ (fun k => PEmpty.elim k) (fun k => PEmpty.elim k)
  exact w_core_sound M r (wCopyMinors M) (fun i _ => family M wSig i)
    (fun i _ => family_dich M wSig wInvariants.1 i)
    (fun _ _ _ _ => Equiv.rfl) hleaf (w_copy_node P M)

theorem w_omega_copy (P : Premises4) (M : Interp.{4}) (r : Nat) :
    ∃ f : PUnit.{4} → PSet.{4},
      (∀ k, f k ∈ Ed M (wA M)) ∧
      (∀ k, ihAtN (RecPlan.core M r [[], [.recursive 1]] (wCopyMinors M)) 1 (f k) ∈
        Ed M ((widen wTel).erasedIHType M (fun i _ => family M wSig i) (f k))) ∧
      wSig.code ⟨.node⟩ f ∈ family M wSig .unit ∧
      Equiv (wSig.code ⟨.node⟩ f) (decode M wSig wOmega) ∧
      RecPlan.core M r [[], [.recursive 1]] (wCopyMinors M) (wSig.code ⟨.node⟩ f) ∈
        family M wSig .unit ∧ (∀ n, ¬ wBound n wOmega) := by
  obtain ⟨f, hf, hc, he⟩ := w_produced P M
  have hdata : ∀ s f, ¬ Equiv (wSig.code s f) pempty := by
    intro ⟨s⟩ f
    cases s <;> exact dataVal_ne_pempty _ _
  have hp : ∀ i, pempty ∈ family M wSig i →
      Equiv (RecPlan.core M r [[], [.recursive 1]] (wCopyMinors M) pempty) pempty := by
    intro i hi
    obtain ⟨s, f, _, he, _⟩ := cases_mem M wSig wInvariants.1 wInvariants.2 i hi
    exact (hdata s f he.symm).elim
  refine ⟨f, hf, ?_, hc, he, w_copy_sound P M r _ hc, wOmega_bound_refuted⟩
  intro k
  exact (widen wTel).ihAtN_mem M
    (PiSmallField.widen_dich wTel (wInvariants.2 ⟨.node⟩ .unit))
    (family M wSig) (family_dich M wSig wInvariants.1)
    (fun i _ => family M wSig i) (fun i _ => family_dich M wSig wInvariants.1 i)
    (RecPlan.core M r [[], [.recursive 1]] (wCopyMinors M))
    (recCore_resp M (RecPlan.descriptor r [[], [.recursive 1]]) (wCopyMinors M))
    (fun i z hz => by cases i; exact w_copy_sound P M r z hz) hp (hf k)
theorem w_wrong_tag (M : Interp.{4}) (j : Nat) (hj : 2 ≤ j)
    (xs : List PSet.{4}) : dataVal j xs ∉ family M wSig .unit := by
  intro hz
  obtain ⟨⟨s⟩, f, _, he, _⟩ := cases_mem M wSig wInvariants.1 wInvariants.2 .unit hz
  cases s with
  | leaf =>
    have h : j = 0 := ord_inj ((tagOf_dataVal j xs).symm.trans
      ((tagOf_congr he).trans (tagOf_dataVal 0 [])))
    omega
  | node =>
    have h : j = 1 := ord_inj ((tagOf_dataVal j xs).symm.trans
      ((tagOf_congr he).trans (tagOf_dataVal 1 [f .unit])))
    omega
end Rcic.F3.PSet.PiDataRecAttack
