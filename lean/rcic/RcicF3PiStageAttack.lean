import rcic.RcicF3PiStageValue
/-! Empty dependent branches bound erased types without staging every
binder domain or target leaf. The field is inhabited, even though its
complete path space is empty. No universal family producer is claimed.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiStageAttack
universe u
def emptyInner (A : PSet.{u}) : RecTel.{u,0} PUnit.{1} 2 :=
  .pi A (fun _ => .pi pempty (fun _ => .ret .unit))
theorem empty_inner_stage (M : Interp.{u}) (W : PSet.{u}) (hW : Stage W)
    (A : PSet.{u}) (hA : Dich A) (X Y : PUnit.{1} → PSet.{u})
    (hX : ∀ i, Dich (X i)) (hY : ∀ i, Dich (Y i)) :
    ∃ f, Equiv f pempty ∧ f ∈ W ∧
      f ∈ Ed M ((emptyInner A).erasedType M X) ∧
      Ed M ((emptyInner A).erasedType M Y) ∈ W := by
  have hd : (emptyInner A).DomainsDich :=
    ⟨hA, fun _ => ⟨Or.inr not_mem_pempty, fun _ => trivial⟩⟩
  have hn : ∀ _p : (emptyInner A).tel.Path, False := by
    intro p
    exact Quotient.inductionOn p.2.1 (fun i => PEmpty.elim i)
  let v : PiTel.Value.{u,u+1} (emptyInner A).tel (fun _ => PSet.{u}) :=
    fun _ r => Quotient.lift (fun i => PEmpty.elim i)
      (fun i => PEmpty.elim i) r
  have hr : (emptyInner A).Rel X v := by
    intro q r
    exact Quotient.inductionOn r (fun i => PEmpty.elim i)
  let f := (emptyInner A).erasedEncode M v
  have hf := (emptyInner A).erasedEncode_mem M hd X hX v hr
  have he := (emptyInner A).member_empty_of_no_paths M hd X hX hn hf
  have hs : f ∈ W := mem_congr_left he.symm hW.empty
  exact ⟨f, he, hs, hf, (emptyInner A).erasedType_stage_from_value M hW hd X Y hX hY
    (fun p => (hn p).elim) (fun p => (hn p).elim) hf hs⟩
end Rcic.F3.PSet.PiStageAttack
