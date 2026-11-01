import rcic.RcicF3PiPropProducer
import rcic.RcicF3PiEraseFixture
import rcic.RcicF3PiLiveAttack
/-! Choice-free proof-family fixtures: exact accessibility, paid Nat.lt
constructor fields, mixed-loop refusal and an actually non-small domain.
These are semantic signatures, not a raw-group model. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiPropAttack
open PiPropProducer PiFieldFixture

def accSig (R : Nat → Nat → Prop) : Sig.{0,0,0} Nat where
  Sh := Nat
  Field := fun _ => PUnit
  depth := fun _ _ => 2
  tel := fun x _ => PiEraseFixture.accTel R x
  out := id

theorem acc_valid_iff (R : Nat → Nat → Prop) (x : Nat) :
    Valid (accSig R) x ↔ Acc R x := by
  constructor
  · intro h
    induction h with
    | sup s hg ih =>
      exact Acc.intro s (fun y hy => ih .unit
        ⟨PiEraseFixture.natCls y, ⟨Quotient.mk _ ⟨hy⟩, .unit⟩⟩)
  · intro h
    induction h with
    | intro x hx ih =>
      apply Valid.sup (S := accSig R) x
      intro k p
      exact ih (PiEraseFixture.natOf p.1) (proofOf _ p.2.1)

theorem acc_exact (R : Nat → Nat → Prop) (x : Nat) :
    pempty ∈ family (accSig R) x ↔ Acc R x := by
  exact ⟨fun h => (acc_valid_iff R x).mp ((family_iff _ _ _).mp h).1,
    fun h => (family_iff _ _ _).mpr ⟨(acc_valid_iff R x).mpr h, Equiv.rfl⟩⟩

theorem natLt_produced (M : Interp.{0}) (x : Nat) :
    ∃ f : PUnit → PSet.{0},
      (∀ k, f k ∈ Ed M (((accSig Nat.lt).tel x k).erasedType M
        (family (accSig Nat.lt)))) ∧ pempty ∈ family (accSig Nat.lt) x := by
  let v : PiTel.Value.{0,1} (PiEraseFixture.accTel Nat.lt x).tel (fun _ => PSet.{0}) :=
    fun _ _ => pempty
  have hr : (PiEraseFixture.accTel Nat.lt x).Rel (family (accSig Nat.lt)) v :=
    fun q _ => (acc_exact Nat.lt (PiEraseFixture.natOf q)).mpr (Nat.lt_wfRel.wf.apply _)
  let f : PUnit → PSet.{0} := fun _ => (PiEraseFixture.accTel Nat.lt x).erasedEncode M v
  have hD := PiEraseFixture.accDomainsDich Nat.lt
  have hf := fun k => ((accSig Nat.lt).tel x k).erasedEncode_mem M
    (hD x k) _ (family_dich (accSig Nat.lt)) v hr
  exact ⟨f, hf, produce M (accSig Nat.lt) hD x f hf⟩

theorem mixed_indices_refused :
    pempty ∈ family (accSig PiEraseFixture.loopRel) 1 ∧
      pempty ∉ family (accSig PiEraseFixture.loopRel) 0 := by
  constructor
  · apply (acc_exact PiEraseFixture.loopRel 1).mpr
    exact Acc.intro 1 (fun _ h => Nat.noConfusion h.2)
  · intro h
    exact PiEraseFixture.loop_not_accessible ((acc_exact _ _).mp h)

def largeSig : Sig.{4,0,0} Nat where
  Sh := Bool
  Field := fun s => match s with | false => PEmpty | true => PUnit
  depth := fun _ _ => 1
  tel := fun s k => match s with
    | false => PEmpty.elim k
    | true => .pi PiLiveAttack.largeDomain (fun _ => .ret 0)
  out := fun s => if s then 1 else 0

theorem large_produced (M : Interp.{4}) :
    ¬ Small.{3,4} PiLiveAttack.largeDomain ∧
    ∃ f : PUnit → PSet.{4},
      (∀ k, f k ∈ Ed M ((largeSig.tel true k).erasedType M (family largeSig))) ∧
      pempty ∈ family largeSig 1 := by
  have hv : Valid largeSig 0 := Valid.sup (S := largeSig) false (fun k => PEmpty.elim k)
  have hz : pempty ∈ family largeSig 0 := (family_iff _ _ _).mpr ⟨hv, Equiv.rfl⟩
  have hD : ∀ s k, (largeSig.tel s k).DomainsDich := by
    intro s k
    cases s with
    | false => exact PEmpty.elim k
    | true => exact ⟨PiLiveAttack.large_domain_invariants.1, fun _ => trivial⟩
  let v : PiTel.Value.{4,5} (largeSig.tel true PUnit.unit).tel (fun _ => PSet.{4}) :=
    fun _ => pempty
  let f : PUnit → PSet.{4} := fun _ => (largeSig.tel true PUnit.unit).erasedEncode M v
  have hf : ∀ k, f k ∈ Ed M ((largeSig.tel true k).erasedType M (family largeSig)) :=
    fun k => (largeSig.tel true k).erasedEncode_mem M (hD true k)
      (family largeSig) (family_dich largeSig) v (fun _ => hz)
  exact ⟨PiLiveAttack.large_domain_invariants.2, f, hf, produce M largeSig hD true f hf⟩

end Rcic.F3.PSet.PiPropAttack
