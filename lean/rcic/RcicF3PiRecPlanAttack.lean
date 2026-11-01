import rcic.RcicF3PiRecNode
import rcic.RcicF3PendAWFixture
import rcic.RcicF3PiSmallAttack
/-! Operational recursor plan attacks. The W node is the actual producer
constructor. Acc and dependent/empty fixtures pay field membership only;
we do not identify data wrappers with proof-erased Acc constructors.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRecPlanAttack
open Rcic.Declarative RecPlan PiSmallCompile PiSmallProducer

/- Exact normalized operational plan at the original admitted PendA
W fixture. This is a kernel computation pin, not a producer. -/
kernel_rfl_theorem w_node_plan :
  nodePlan Rcic.Declarative.PendAW.pNode = [[], [.recursive 1]]

/-- The actual height-omega W producer feeds the normalized-plan core,
at every reference label and for arbitrary minors. Elementary composition. -/
theorem w_core (P : Premises4) (M : Interp.{4}) (r : Nat) (ms : List PSet.{4}) :
    ∃ f : PUnit.{4} → PSet.{4},
      PiSmallAttack.wSig.code ⟨.node⟩ f ∈ family M PiSmallAttack.wSig .unit ∧
      Equiv (core M r [[], [.recursive 1]] ms (PiSmallAttack.wSig.code ⟨.node⟩ f))
        (fapps (ms.getD 1 pempty) [f .unit,
          ihAtN (core M r [[], [.recursive 1]] ms) 1 (f .unit)]) := by
  obtain ⟨f, hf, hc, _⟩ := PiSmallAttack.w_produced P M
  refine ⟨f, hc, ?_⟩
  have ht := PiSmallField.widen_dich PiSmallAttack.wTel
    (PiSmallAttack.wInvariants.2 ⟨.node⟩ .unit)
  have hm : FieldsMem.{4,0} M [.recursive 1] [f .unit] :=
    ⟨⟨PUnit, widen PiSmallAttack.wTel, family M PiSmallAttack.wSig, ht, hf .unit⟩, trivial⟩
  exact core_data_mem M r [[], [.recursive 1]] ms rfl hm

/-- Actual Acc/Nat.lt, dependent depth-three and nested-empty field
members occur together in one planned constructor. The data wrapper is
an operational test, not the erased Acc constructor. -/
theorem mixed_fields (P : Premises4) (M : Interp.{4}) (x offset r : Nat)
    (ms : List PSet.{4}) :
    ∃ a d e, a ∈ Ed M ((widen (PiSmallAttack.accTel Nat.lt x)).erasedType M
        (family M (PiSmallAttack.accSig Nat.lt))) ∧ FieldsMem.{4,0} M
        [.nonrecursive, .recursive 2, .recursive 3, .recursive 2]
        [ord 7, a, d, e] ∧
      Equiv (core M r [[.nonrecursive, .recursive 2, .recursive 3, .recursive 2]] ms
        (dataVal 0 [ord 7, a, d, e]))
        (fapps (ms.getD 0 pempty)
          [ord 7, a, ihAtN (core M r [[.nonrecursive, .recursive 2, .recursive 3, .recursive 2]] ms) 2 a,
            d, ihAtN (core M r [[.nonrecursive, .recursive 2, .recursive 3, .recursive 2]] ms) 3 d,
            e, ihAtN (core M r [[.nonrecursive, .recursive 2, .recursive 3, .recursive 2]] ms) 2 e]) := by
  obtain ⟨a, ha, _⟩ := PiSmallAttack.natLt_produced P M x
  obtain ⟨d, hd⟩ := PiSmallAttack.nested_product M offset
  obtain ⟨e, he⟩ := PiSmallAttack.empty_product M
  have ha' : FieldMem.{4,0} M (.recursive 2) (a .unit) :=
    ⟨Nat, widen (PiSmallAttack.accTel Nat.lt x), family M (PiSmallAttack.accSig Nat.lt),
      PiSmallField.widen_dich _ ((PiSmallAttack.accInvariants Nat.lt).2 ⟨x⟩ .unit), ha .unit⟩
  have hd' : FieldMem.{4,0} M (.recursive 3) d :=
    ⟨Nat, widen (PiSmallAttack.nestedTel offset), PiSmallAttack.nestedFibre,
      PiSmallField.widen_dich _ (PiSmallAttack.nestedInvariants offset).1, hd⟩
  have heD : PiSmallAttack.emptyTel.DomainsDich :=
    ⟨Or.inr (fun h => tyv_ne_pempty _ (mem_singleton.mp h).symm),
      fun _ => ⟨Or.inr not_mem_pempty, fun _ => trivial⟩⟩
  have he' : FieldMem.{4,0} M (.recursive 2) e :=
    ⟨PUnit, widen PiSmallAttack.emptyTel, PiSmallAttack.emptyFibre,
      PiSmallField.widen_dich _ heD, he⟩
  have hm : FieldsMem.{4,0} M
      [.nonrecursive, .recursive 2, .recursive 3, .recursive 2] [ord 7, a .unit, d, e] :=
    ⟨trivial, ha', hd', he', trivial⟩
  exact ⟨a .unit, d, e, ha .unit, hm, core_data_mem M r _ ms rfl hm⟩

/-- The actual admitted W node consumes the actual producer constructor.
This is elementary composition; it does not pay arbitrary normalized
semantic field extraction. -/
theorem w_node_core (P : Premises4) (M : Interp.{4}) (ms : List PSet.{4}) :
    ∃ f : PUnit.{4} → PSet.{4},
      PiSmallAttack.wSig.code ⟨.node⟩ f ∈ family M PiSmallAttack.wSig .unit ∧
      Equiv (nodeCore M Rcic.Declarative.PendAW.pNode ms
        (PiSmallAttack.wSig.code ⟨.node⟩ f))
        (fapps (ms.getD 1 pempty) [f .unit,
          ihAtN (nodeCore M Rcic.Declarative.PendAW.pNode ms) 1 (f .unit)]) := by
  unfold nodeCore
  rw [w_node_plan]
  exact w_core P M 4 ms

end Rcic.F3.PSet.PiRecPlanAttack
