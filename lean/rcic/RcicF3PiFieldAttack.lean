import rcic.RcicF3PiFieldFixture

/-!
# Presentation and relabelling attacks on the field interpretation

These are semantic tests, not raw syntax extraction theorems.
The hidden telescope uses beta, delta and let reduction; every offset is
quantified, and the result index depends on two distinct arguments.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.F3.PSet.PiFieldAttack
open PiFieldFixture

def labelled (offset : Nat) : RecTel Nat 3 :=
  .pi fnDom (fun q => .pi (proofDom (natOf q < natOf q + 1))
    (fun _ => .pi fnDom (fun r => .ret (offset + natOf q + natOf r))))

def hidden (offset : Nat) : RecTel Nat 3 :=
  (fun t : RecTel Nat 3 => let q := t; q) (labelled offset)

-- Deliberately trivial computation pin.
theorem hidden_eq (offset : Nat) : hidden offset = labelled offset := rfl

/-- Inhabit the actual product after arbitrary numerical relabelling. -/
theorem labelled_product (offset : Nat) :
    ∃ f, f ∈ (hidden offset).denote (fun i => singleton (ord i)) := by
  apply ((hidden offset).inhabited_iff (fun i => singleton (ord i))).mpr
  exact ⟨fun q _ r => ord (offset + natOf q + natOf r),
    fun _ _ _ => mem_singleton.mpr Equiv.rfl⟩

/-- Forgetting the relabelled, dependent result is detected at a real path. -/
theorem stale_index_refused (offset : Nat) :
    ¬ (hidden (offset + 1)).Rel (fun i => singleton (ord i))
      (fun q _ r => ord (offset + natOf q + natOf r)) := by
  intro h
  have he := mem_singleton.mp
    (h (fnCls 0) (Quotient.mk _ ⟨Nat.zero_lt_succ 0⟩) (fnCls 0))
  have hn : offset = offset + 1 := ord_inj he
  exact (Nat.ne_of_lt (Nat.lt_succ_self offset)) hn

/-- A shifted relation retains every accessible point and its field product. -/
theorem shifted_acc_product (offset x : Nat) :
    ∃ f, f ∈ (accTel (fun a b => a + offset < b + offset) x).denote
      (PiAcc.fiber (fun a b => a + offset < b + offset)) := by
  have hx : Acc (fun a b => a + offset < b + offset) x := by
    induction Nat.lt_wfRel.wf.apply x with
    | intro y _ ih =>
      exact Acc.intro y (fun z hz => ih z (Nat.lt_of_add_lt_add_right hz))
  exact ⟨_, (accTel _ x).encode_mem _ _ (acc_related _ x hx)⟩

end Rcic.F3.PSet.PiFieldAttack
