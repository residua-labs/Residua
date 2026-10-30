import rcic.RcicF3PiTel
import rcic.RcicF3FamKTFnObstr

/-!
# An inhabited W fixture for dependent Pi signatures

The leaf has no recursive fields; the node has one function field over an
infinite domain. The landed height-omega witness embeds with the same set
code. Thus telescope compilation neither removes the leaf nor restricts
well-founded trees to finite height. This is a semantic fixture, not a
typed R-CIC group-step producer. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PiW

universe u

/-- A genuine nullary leaf and one higher-order recursive field. -/
def Field : Fn2Sh.{u} → Type u
  | .leaf => PEmpty
  | .node => PUnit

/-- Reuse the landed graph code, with its extensional branch quotient. -/
def sig : PiSig.{u} where
  Sh := Fn2Sh
  Field := Field
  depth := fun _ _ => 1
  tel := fun s k => match s with
    | .leaf => PEmpty.elim k
    | .node => .cons (FBr fnDom) (fun _ => .nil)
  code := fun s f => match s with
    | .leaf => dataVal 0 []
    | .node => dataVal 1 [graphOf fnDom (fun q => f .unit q)]
  ok := fun _ _ => True
  code_congr := by
    intro s f g h
    cases s with
    | leaf => exact Equiv.rfl
    | node => exact dataVal_congr 1 ⟨graphOf_congr (fun q => h .unit ⟨q, .unit⟩), trivial⟩
  ok_congr := fun _ _ _ _ h => h

/-- Retain every branch of the original W tree. -/
def embed : GT Fn2GSig.{u} → GT sig.toGSig
  | .sup .leaf _ => .sup .leaf (fun p => PEmpty.elim p.1)
  | .sup .node g => .sup .node (fun p => embed (g p.2.1))

/-- Re-indexing branches preserves the set-theoretic constructor code. -/
theorem embed_decode (w : GT Fn2GSig.{u}) :
    Equiv (decG sig.toGSig (embed w)) (decG Fn2GSig w) := by
  induction w with
  | sup s g ih =>
    cases s with
    | leaf => exact Equiv.rfl
    | node => exact dataVal_congr 1 ⟨graphOf_congr ih, trivial⟩

/-- The semantic guard accepts every well-founded tree of this W type. -/
theorem embed_valid (w : GT Fn2GSig.{u}) : ValidW sig.toGSig (embed w) := by
  induction w with
  | sup s g ih =>
    cases s with
    | leaf => exact ValidW.sup (S := sig.toGSig) Fn2Sh.leaf _ (fun p => PEmpty.elim p.1) trivial
    | node => exact ValidW.sup (S := sig.toGSig) Fn2Sh.node _ (fun p => ih p.2.1) trivial

/-- In particular the semantic W family contains its nullary leaf. -/
theorem leaf_mem : dataVal 0 [] ∈ gSet sig.toGSig.{u} := by
  exact ⟨⟨embed fnLeafT, embed_valid fnLeafT⟩, Equiv.rfl⟩

/-- The compiled family retains the landed height-omega counterexample
to the union of finite stages, with the same set code. -/
theorem heightOmega_mem_not_finite :
    decG sig.{u}.toGSig (embed fnW) ∈ gSet sig.{u}.toGSig ∧
    decG sig.{u}.toGSig (embed fnW) ∉ gUnion.{u} := by
  constructor
  · exact ⟨⟨embed fnW, embed_valid fnW⟩, Equiv.rfl⟩
  · intro h
    exact fnW_not_mem_union (mem_congr_left (embed_decode fnW) h)

end Rcic.F3.PSet.PiW
