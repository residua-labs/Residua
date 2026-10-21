import rcic.RcicMulLT
import rcic.RcicSynOrder

/-!
# Foundation multiset order: reuse the single DMStep well-foundedness owner

The original MulLT and MulSizeLT contracts are unchanged. MulLT is exactly
Rcic.Syn.DMStep, with the common remainder written on the other side of ++.
The former private histogram/rankLex proof has been retired: the three public
well-foundedness entry points now depend on Rcic.Syn.dmStep_wf.

MulSizeLT retains PERMUTATION, not literal equality, in its secondary branch.
A small accessibility adapter handles that existing quotient convention; it
does not re-prove the DM order. No fan-out bound or new numeric measure.
No actual U/X/P call admissibility or global closure is asserted.
-/

namespace Rcic.S3

/-- Same multiset step, with the removed/inserted part before the remainder. -/
theorem dmStep_of_mulLT {m n : List Nat} (h : MulLT m n) : Rcic.Syn.DMStep m n := by
  obtain ⟨Z, Y, X, hm, hn, hX, hdom⟩ := h
  exact ⟨X, Y, Z, hX, hn.trans List.perm_append_comm,
    hm.trans List.perm_append_comm, hdom⟩

/-- Reverse bridge: no weakening and no fixed fan-out assumption. -/
theorem mulLT_of_dmStep {m n : List Nat} (h : Rcic.Syn.DMStep m n) : MulLT m n := by
  obtain ⟨X, Y, Z, hX, hn, hm, hdom⟩ := h
  exact ⟨Z, Y, X, hm.trans List.perm_append_comm,
    hn.trans List.perm_append_comm, hX, hdom⟩

theorem mulLT_iff_dmStep {m n : List Nat} : MulLT m n ↔ Rcic.Syn.DMStep m n :=
  ⟨dmStep_of_mulLT, mulLT_of_dmStep⟩

/-- The old public name now delegates to the landed, single DM owner. -/
theorem mulLT_wf : WellFounded MulLT :=
  ⟨fun m => Rcic.Syn.subrel_acc (fun h => dmStep_of_mulLT h)
    (Rcic.Syn.dmStep_wf.apply m)⟩

/-- Unchanged legacy contract: equal primary multisets means List.Perm. -/
def MulSizeLT (p q : List Nat × Nat) : Prop :=
  MulLT p.1 q.1 ∨ p.1.Perm q.1 ∧ p.2 < q.2

private theorem mulSizeLT_perm_right {p : List Nat × Nat} {m m' : List Nat} {k : Nat}
    (hp : m.Perm m') (h : MulSizeLT p (m, k)) : MulSizeLT p (m', k) := by
  rcases h with h | ⟨hq, hs⟩
  · obtain ⟨Z, Y, X, h1, h2, hx, hd⟩ := h
    exact .inl ⟨Z, Y, X, h1, hp.symm.trans h2, hx, hd⟩
  · exact .inr ⟨hq.trans hp, hs⟩

private theorem mulSizeLT_acc_perm {m m' : List Nat} {k : Nat}
    (hp : m.Perm m') (h : Acc MulSizeLT (m, k)) : Acc MulSizeLT (m', k) :=
  .intro _ (fun _ hq => h.inv (mulSizeLT_perm_right hp.symm hq))

/-- Lift primary accessibility, respecting permutation in the secondary branch. -/
private theorem mulSizeLT_acc_of_mulLT {m : List Nat} (h : Acc MulLT m) :
    ∀ k : Nat, Acc MulSizeLT (m, k) := by
  induction h with
  | intro m _ ih =>
    intro k
    induction k using Nat.strongRecOn with
    | _ k ihk =>
      refine Acc.intro (m, k) ?_
      intro q hq
      rcases hq with hm | ⟨hp, hs⟩
      · exact ih q.1 hm q.2
      · exact mulSizeLT_acc_perm hp.symm (ihk q.2 hs)

/-- Unbounded multiset/size well-foundedness, through the common DM proof. -/
theorem mulSizeLT_wf : WellFounded MulSizeLT :=
  ⟨fun p => mulSizeLT_acc_of_mulLT (mulLT_wf.apply p.1) p.2⟩

/-- Unchanged generic bundle comparison; ranks carry no semantic assumptions. -/
def muLtUnbounded (f d : α → Nat) (m n : List α) : Prop :=
  MulLT (FM f m) (FM f n) ∨ (FM f m).Perm (FM f n) ∧ S d m < S d n

theorem muLtUnbounded_wf (f d : α → Nat) :
    WellFounded (muLtUnbounded f d) :=
  InvImage.wf (fun m : List α => (FM f m, S d m)) mulSizeLT_wf

end Rcic.S3
