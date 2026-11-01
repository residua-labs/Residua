import rcic.RcicF3PiPropRec
import rcic.RcicF3PiPropAttack
import rcic.RcicF3PiPropField
import rcic.RcicF3Iota
/-!
# Proof recursor non-vacuity and attacks

The Acc minor reads its dependent IH at each predecessor. Nat.lt supplies
actual constructor fields and a proof major; the literal propOnly recursor
end is typed by composing the semantic producer with recEnd_propOnly.
The raw signature, motive and minor extraction bridge is not asserted.

A data motive satisfies every other semantic premise while refusing the
erased result. Actual proof fields also refute membership descent from
field to erased major. Numeric output indices and data tags are arbitrary.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiPropRecAttack
open Rcic.Declarative
def accMotive (R : Nat → Nat → Prop) (i : Nat) (_z : PSet.{0}) : PSet.{0} := tv (Acc R i)
theorem acc_minor (M : Interp.{0}) (R : Nat → Nat → Prop) (s : Nat)
    (f ih : PUnit → PSet.{0})
    (hih : ∀ k, ih k ∈ Ed M (((PiPropAttack.accSig R).tel s k).erasedIHType M
      (accMotive R) (f k))) : pempty ∈ accMotive R s pempty := by
  apply mem_tv.mpr
  refine ⟨Acc.intro s ?_, Equiv.rfl⟩
  intro y hy
  have hr := ((PiPropAttack.accSig R).tel s PUnit.unit).erasedIH_read M
    (PiEraseFixture.accDomainsDich R s PUnit.unit) (accMotive R)
    (fun _ _ => Or.inl (fun _ h => (mem_tv.mp h).2))
    (f PUnit.unit) (ih PUnit.unit) (hih PUnit.unit)
  have hm := (PiTel.all_iff _ _ _).mp hr
    ⟨PiEraseFixture.natCls y, ⟨Quotient.mk _ ⟨hy⟩, PUnit.unit⟩⟩
  exact (mem_tv.mp hm).1
theorem acc_recEnd (M : Interp.{0}) (R : Nat → Nat → Prop)
    (σ : Nat → Nat) (fd : FamData) (ρ : Nat → PSet.{0})
    (h0 : evalTotal σ fd.resLevel = 0) (hp : fd.policy = .propOnly)
    (i : Nat) (z : PSet.{0}) (hz : z ∈ PiPropProducer.family (PiPropAttack.accSig R) i) :
    recEnd M σ fd ρ ∈ accMotive R i z := by
  rw [recEnd_propOnly M σ fd ρ h0 hp]
  exact PiPropRec.produce M (PiPropAttack.accSig R) (PiEraseFixture.accDomainsDich R)
    (accMotive R) (fun _ _ => Or.inl (fun _ h => (mem_tv.mp h).2))
    (fun _ _ _ _ => Equiv.rfl) (fun _ _ _ h => (mem_tv.mp h).2)
    (fun _ _ _ => pempty) (fun s f ih _ hih => acc_minor M R s f ih hih) i z hz
theorem natLt_recEnd_fields (M : Interp.{0})
    (σ : Nat → Nat) (fd : FamData) (ρ : Nat → PSet.{0})
    (h0 : evalTotal σ fd.resLevel = 0) (hp : fd.policy = .propOnly) (i : Nat) :
    ∃ f : PUnit → PSet.{0},
      (∀ k, f k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel i k).erasedType M
        (PiPropProducer.family (PiPropAttack.accSig Nat.lt)))) ∧
      pempty ∈ PiPropProducer.family (PiPropAttack.accSig Nat.lt) i ∧
      recEnd M σ fd ρ ∈ accMotive Nat.lt i pempty := by
  obtain ⟨f, hf, hz⟩ := PiPropAttack.natLt_produced M i
  exact ⟨f, hf, hz, acc_recEnd M Nat.lt σ fd ρ h0 hp i pempty hz⟩
def dataMotive (tag i : Nat) (_z : PSet.{0}) : PSet.{0} :=
  singleton (dataVal tag [ord i])
def dataMinor (tag s : Nat) (_f _ih : PUnit → PSet.{0}) : PSet.{0} :=
  dataVal tag [ord s]
theorem data_motive_counterexample (M : Interp.{0}) (tag i : Nat) :
    (∀ s k, ((PiPropAttack.accSig Nat.lt).tel s k).DomainsDich) ∧
    (∀ j z, Dich (dataMotive tag j z)) ∧
    (∀ j x y, Equiv x y → Equiv (dataMotive tag j x) (dataMotive tag j y)) ∧
    (∀ s f ih,
      (∀ k, f k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel s k).erasedType M
        (PiPropProducer.family (PiPropAttack.accSig Nat.lt)))) →
      (∀ k, ih k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel s k).erasedIHType M
        (dataMotive tag) (f k))) →
      dataMinor tag s f ih ∈ dataMotive tag s pempty) ∧
    pempty ∈ PiPropProducer.family (PiPropAttack.accSig Nat.lt) i ∧
    pempty ∉ dataMotive tag i pempty ∧
    ¬ (∀ j x y, y ∈ dataMotive tag j x → Equiv y pempty) := by
  refine ⟨PiEraseFixture.accDomainsDich Nat.lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j z
    exact Or.inr (fun h => dataVal_ne_pempty tag [ord j] (mem_singleton.mp h).symm)
  · intro j x y _
    exact Equiv.rfl
  · intro s f ih _ _
    exact mem_singleton.mpr Equiv.rfl
  · exact (PiPropAttack.acc_exact Nat.lt i).mpr (Nat.lt_wfRel.wf.apply i)
  · intro h
    exact dataVal_ne_pempty tag [ord i] (mem_singleton.mp h).symm
  · intro h
    exact dataVal_ne_pempty tag [ord i]
      (h i pempty (dataVal tag [ord i]) (mem_singleton.mpr Equiv.rfl))
theorem erased_descent_refuted (M : Interp.{0}) (i : Nat) :
    ∃ f : PUnit → PSet.{0},
      (∀ k, f k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel i k).erasedType M
        (PiPropProducer.family (PiPropAttack.accSig Nat.lt)))) ∧
      pempty ∈ PiPropProducer.family (PiPropAttack.accSig Nat.lt) i ∧
      (∀ k, Equiv (f k) pempty ∧ ¬ MemT (f k) pempty) := by
  obtain ⟨f, hf, hz⟩ := PiPropAttack.natLt_produced M i
  refine ⟨f, hf, hz, ?_⟩
  intro k
  have he := PiPropField.member_empty M ((PiPropAttack.accSig Nat.lt).tel i k)
    (PiEraseFixture.accDomainsDich Nat.lt i k)
    (PiPropProducer.family (PiPropAttack.accSig Nat.lt))
    (fun j y h => ((PiPropProducer.family_iff _ j y).mp h).2) (hf k)
  refine ⟨he, ?_⟩
  intro h
  have hno : ∀ z : PSet.{0}, ¬ MemT z z :=
    fun z => memT_wf.induction (C := fun y => ¬ MemT y y) z (fun y ih hy => ih y hy hy)
  exact hno pempty (MemT.congr_left he h)
/-- Nat.lt pays both actual field and dependent-IH membership. The
IH assignment is explicitly encoded; the recEnd conclusion is composition. -/
theorem natLt_recEnd_IHs (M : Interp.{0})
    (σ : Nat → Nat) (fd : FamData) (ρ : Nat → PSet.{0})
    (h0 : evalTotal σ fd.resLevel = 0) (hp : fd.policy = .propOnly) (i : Nat) :
    ∃ f ih : PUnit → PSet.{0},
      (∀ k, f k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel i k).erasedType M
        (PiPropProducer.family (PiPropAttack.accSig Nat.lt)))) ∧
      (∀ k, ih k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel i k).erasedIHType M
        (accMotive Nat.lt) (f k))) ∧
      pempty ∈ PiPropProducer.family (PiPropAttack.accSig Nat.lt) i ∧
      recEnd M σ fd ρ ∈ accMotive Nat.lt i pempty := by
  obtain ⟨f, hf, hz⟩ := PiPropAttack.natLt_produced M i
  let ih : PUnit → PSet.{0} := fun k =>
    ((PiPropAttack.accSig Nat.lt).tel i k).erasedEncode M
      (((PiPropAttack.accSig Nat.lt).tel i k).tel.unflatten (fun _ => pempty))
  refine ⟨f, ih, hf, ?_, hz, acc_recEnd M Nat.lt σ fd ρ h0 hp i pempty hz⟩
  intro k
  change ih k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel i k).erasedIHType M
    (fun j _ => tv (Acc Nat.lt j)) (f k))
  rw [RecTel.erasedIHType_const]
  apply RecTel.erasedEncode_mem _ _ (PiEraseFixture.accDomainsDich Nat.lt i k)
    (fun j => tv (Acc Nat.lt j)) (fun _ => Or.inl (fun _ h => (mem_tv.mp h).2))
  apply (PiTel.all_iff _ _ _).mpr
  intro p
  change pempty ∈ tv (Acc Nat.lt _)
  exact mem_tv.mpr ⟨Nat.lt_wfRel.wf.apply _, Equiv.rfl⟩
/-- Refusal with actual fields and actual typed IHs, for every index/tag.
Thus the data-motive minor antecedent is inhabited at the attacked group. -/
theorem data_motive_IHs (M : Interp.{0}) (tag i : Nat) :
    ∃ f ih : PUnit → PSet.{0},
      (∀ k, f k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel i k).erasedType M
        (PiPropProducer.family (PiPropAttack.accSig Nat.lt)))) ∧
      (∀ k, ih k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel i k).erasedIHType M
        (dataMotive tag) (f k))) ∧
      dataMinor tag i f ih ∈ dataMotive tag i pempty ∧
      pempty ∈ PiPropProducer.family (PiPropAttack.accSig Nat.lt) i ∧
      pempty ∉ dataMotive tag i pempty ∧
      ¬ (∀ j x y, y ∈ dataMotive tag j x → Equiv y pempty) := by
  obtain ⟨f, hf, _⟩ := PiPropAttack.natLt_produced M i
  obtain ⟨_, hC, _, hm, hz, hn, hp⟩ := data_motive_counterexample M tag i
  let ih : PUnit → PSet.{0} := fun k =>
    ((PiPropAttack.accSig Nat.lt).tel i k).erasedEncode M
      (((PiPropAttack.accSig Nat.lt).tel i k).tel.unflatten
        (fun p => dataVal tag [ord (((PiPropAttack.accSig Nat.lt).tel i k).result p)]))
  have hi : ∀ k, ih k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel i k).erasedIHType M
      (dataMotive tag) (f k)) := by
    intro k
    change ih k ∈ Ed M (((PiPropAttack.accSig Nat.lt).tel i k).erasedIHType M
      (fun j _ => singleton (dataVal tag [ord j])) (f k))
    rw [RecTel.erasedIHType_const]
    apply ((PiPropAttack.accSig Nat.lt).tel i k).erasedEncode_mem M
      (PiEraseFixture.accDomainsDich Nat.lt i k)
      (fun j => singleton (dataVal tag [ord j])) (fun j => hC j pempty)
    apply (PiTel.all_iff _ _ _).mpr
    intro p
    rw [PiTel.flatten_unflatten]
    exact mem_singleton.mpr Equiv.rfl
  exact ⟨f, ih, hf, hi, hm i f ih hf hi, hz, hn, hp⟩
end Rcic.F3.PSet.PiPropRecAttack
