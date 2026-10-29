import rcic.RcicF3KTWSpec
import rcic.RcicF3StageN

/-!
# F3: the `.fn` bridge obstruction — the height-`ω` tree counter-model

`RcicF3FamKTBridge` names residue `[rcic-f3-famkt-bridge-fn-cont]`: the `≥`
direction of `famLim ≈ famKT` needs the union of `PsiF`-iterates to be
pre-fixed, and at `.fn` fields the guard reads the field value pointwise
(`x ∈ piSet (domBig) (fib X)`), so "fib-continuity over `iUnionN`" was named
but not proved.  This module CLOSES that question the other way:

**fib-continuity is REFUTED, not open.**  At the guarded-W level (`GSig`,
`gphi`, `gSet` — the shape `PsiF`/`DStar` are dispatched to), the ω-union of
`gphi`-iterates is NOT pre-fixed for a leaf-ful `.fn` signature over an
infinite domain: the height-`ω` tree `fnW` (one node whose function field
carries a depth-`n` child for every `n`) is a VALID tree, hence in `gSet`
(the initial algebra — the reading `DStar` dispatches to), and it is in
`gphi` of the union (its children are all finitely ranked), but it is in NO
finite stage.  Classically: the closure ordinal of an infinitely-branching
function-recursive signature is above `ω`; the finitely-ranked trees (the
`⋃` of iterates, the `famLim` reading) are a proper subset of the
well-founded trees (the `gSet`/`DStar` reading).

- `fnContGSig_false`: the generic continuity claim is refuted at `Fn2GSig`.
- `fnW_diverges`: `decG fnW ∈ gSet Fn2GSig ∧ decG fnW ∉ gUnion` (the
  divergence witness).
- `gSet_empty_of_all_branching`: the exemption clause — a signature whose
  EVERY shape branches (no leaf; the W fixture's shape: one ctor, one `.fn`
  field, no base case) has `gSet ≈ ∅`, so both readings collapse to empty
  and the divergence cannot arise there.

Transfer status (named, not proved here): `PsiF` at a `.fn` field reads the
same pointwise graph guard as `gphi`'s node branch (`InPhi`'s `.fn` arm =
`piSet (domBig) (fib X)`; `Layout.fieldVal` at `.fn` = `graphOf`), so the
refutation transfers to any `FamData` whose derived signature realizes
`Fn2GSig` (two ctors: a leaf and a `.fn` node over an infinite domain).  The
realizability fixture is DONE — `Rcic.F3.FamKTFnReal.fnContUnion_false`
closes residue `[rcic-f3-famkt-bridge-fn-cont]` (see the bridge module's
header note).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet

open Rcic.Declarative

universe u

/-! ### §1 the leaf-ful `.fn` signature over an infinite domain -/

/-- The infinite domain: the finite ordinals, as a set.  Distinct numerals
sit in distinct `FBr` classes. -/
def fnDom : PSet.{u} := mk (ULift.{u} Nat) (fun n => ord n.down)

theorem fnDom_func (n : ULift.{u} Nat) : fnDom.Func n = ord n.down := rfl

/-- Two shapes: a leaf (no branches) and a `.fn` node (branching over the
quotient of `fnDom`). -/
inductive Fn2Sh : Type u where
  | leaf | node

def Fn2br : Fn2Sh → Type u
  | .leaf => PEmpty
  | .node => FBr fnDom

def Fn2code (s : Fn2Sh) (h : Fn2br s → PSet.{u}) : PSet.{u} :=
  match s with
  | .leaf => dataVal 0 []
  | .node => dataVal 1 [graphOf fnDom h]

/-- The counter-model signature: guard trivially true (zero indices), so
validity is well-foundedness alone. -/
def Fn2GSig : GSig.{u} where
  Sh := Fn2Sh
  br := Fn2br
  code := Fn2code
  ok := fun _ _ => True
  code_congr := by
    intro s h h' e
    cases s with
    | leaf => exact Equiv.rfl
    | node =>
        show Equiv (dataVal 1 [graphOf fnDom h]) (dataVal 1 [graphOf fnDom h'])
        exact dataVal_congr 1 ⟨graphOf_congr e, trivial⟩
  ok_congr := fun _ _ _ _ h => h

/-! ### §2 the trees: finite depths, and the height-`ω` tree -/

def fnLeafT : GT Fn2GSig := .sup .leaf (fun q => PEmpty.elim q)

def fnSuccT (t : GT Fn2GSig) : GT Fn2GSig := .sup .node (fun _ => t)

def fnT : Nat → GT Fn2GSig
  | 0 => fnLeafT
  | n + 1 => fnSuccT (fnT n)

/-- The branch assignment: the class of numeral `n` carries the depth-`n`
tree. -/
def fnDepth : FBr fnDom → GT Fn2GSig :=
  Quotient.lift (fun n : ULift.{u} Nat => fnT n.down)
    (fun n m h => congrArg fnT (ord_inj h))

/-- The height-`ω` tree: one node whose children have unbounded finite
depths. -/
def fnW : GT Fn2GSig := .sup .node fnDepth

theorem decG_leaf : decG Fn2GSig fnLeafT = dataVal 0 [] := rfl

theorem decG_succ (t : GT Fn2GSig) :
    decG Fn2GSig (fnSuccT t) = dataVal 1 [graphOf fnDom (fun _ => decG Fn2GSig t)] := rfl

theorem decG_fnT_succ (n : Nat) :
    decG Fn2GSig (fnT (n + 1)) = dataVal 1 [graphOf fnDom (fun _ => decG Fn2GSig (fnT n))] := rfl

theorem decG_W :
    decG Fn2GSig fnW = dataVal 1 [graphOf fnDom (fun b => decG Fn2GSig (fnDepth b))] := rfl

theorem fnDepth_mk (n : ULift.{u} Nat) :
    fnDepth (Quotient.mk (FSetoid fnDom) n) = fnT n.down := rfl

/-- The class of numeral `n` in `fnDom`'s branch quotient. -/
def fnCls (n : Nat) : FBr fnDom := Quotient.mk (FSetoid fnDom) (⟨n⟩ : ULift.{u} Nat)

theorem fnDepth_cls (n : Nat) : fnDepth (fnCls n) = fnT n := rfl

/-! ### §3 `graphOf` injectivity (the guard extraction) -/

/-- Equal graphs have pointwise-equal values: from `graphOf A hf ≈ graphOf A
kf` read, at any class `q`, an `≈`-witness `hf q ≈ kf q`. -/
theorem graphOf_inj {A : PSet.{u}} {hf kf : FBr A → PSet.{u}}
    (he : Equiv (graphOf A hf) (graphOf A kf)) (q : FBr A) : Equiv (hf q) (kf q) := by
  induction q using Quotient.inductionOn with
  | h i =>
    have hmem : ordPair (A.Func i) (hf (Quotient.mk (FSetoid A) i)) ∈ graphOf A hf :=
      ⟨i, Equiv.rfl⟩
    obtain ⟨j, hj⟩ := mem_congr_right he hmem
    obtain ⟨hij, hkj⟩ := ordPair_equiv hj.symm
    have hq : Quotient.mk (FSetoid A) i = Quotient.mk (FSetoid A) j :=
      Quotient.sound hij
    rw [← hq] at hkj
    exact hkj

/-! ### §4 the stages -/

/-- The `gphi`-iteration from `∅`, generic form (for the continuity claim). -/
def gIterOf (S : GSig.{u}) : Nat → PSet.{u}
  | 0 => pempty
  | n + 1 => gphi S (gIterOf S n)

/-- The stages at the counter-model signature. -/
abbrev gIter2 : Nat → PSet.{u} := gIterOf Fn2GSig

/-- The witness index of stage `n`: where `decG (fnT n)` sits in `gIter2 (n+1)`. -/
def fnIdx : (n : Nat) → (gIter2 (n + 1)).Idx
  | 0 => ⟨.leaf, ⟨fun q => PEmpty.elim q, trivial⟩⟩
  | n + 1 => ⟨.node, ⟨fun _ => fnIdx n, trivial⟩⟩

theorem fnIdx_func_node (n : Nat) :
    (gIter2 (n + 2)).Func (fnIdx (n + 1)) =
      dataVal 1 [graphOf fnDom (fun _ => (gIter2 (n + 1)).Func (fnIdx n))] := rfl

theorem fnIdx_func : ∀ n, Equiv ((gIter2 (n + 1)).Func (fnIdx n)) (decG Fn2GSig (fnT n))
  | 0 => Equiv.rfl
  | n + 1 => by
      rw [fnIdx_func_node, decG_fnT_succ]
      exact dataVal_congr 1 ⟨graphOf_congr (fun _ => fnIdx_func n), trivial⟩

/-- Every finite-depth tree is in its own stage. -/
theorem fnT_mem (n : Nat) : decG Fn2GSig (fnT n) ∈ gIter2 (n + 1) :=
  ⟨fnIdx n, fnIdx_func n⟩

/-- The tag-disjointness of the two shapes. -/
theorem leafNode_absurd {g : PSet.{u}} (h : Equiv (dataVal 0 []) (dataVal 1 [g])) : False := by
  have h2 := (ordPair_equiv h).2
  obtain ⟨h1, _⟩ := ordPair_equiv h2
  exact absurd (ord_inj h1) (by omega)

/-- No finite-depth tree is in its own-minus-one stage: the exclusion
induction. -/
theorem fnT_not_mem : ∀ n, decG Fn2GSig (fnT n) ∉ gIter2 n
  | 0, hz => not_mem_pempty hz
  | n + 1, hz => by
      obtain ⟨p, hp⟩ := hz
      cases p with
      | mk s hsub =>
          cases s with
          | leaf =>
              have hp'' : Equiv (dataVal 0 []) (dataVal 1 [graphOf fnDom
                (fun _ => decG Fn2GSig (fnT n))]) := hp
              exact leafNode_absurd hp''
          | node =>
              have hp'' : Equiv (dataVal 1 [graphOf fnDom
                  ((gIter2 n).Func ∘ (hsub.1 : FBr fnDom → (gIter2 n).Idx))])
                  (dataVal 1 [graphOf fnDom (fun _ => decG Fn2GSig (fnT n))]) := hp
              obtain ⟨_, hgt⟩ := ordPair_equiv (ordPair_equiv hp'').2
              have hge : LEq [graphOf fnDom ((gIter2 n).Func ∘
                  (hsub.1 : FBr fnDom → (gIter2 n).Idx))]
                  [graphOf fnDom (fun _ => decG Fn2GSig (fnT n))] :=
                tup_inj (by simp) hgt
              obtain ⟨hge, _⟩ := hge
              have hx : decG Fn2GSig (fnT n) ∈ gIter2 n := by
                refine ⟨(hsub.1 : FBr fnDom → (gIter2 n).Idx) (fnCls n), ?_⟩
                exact graphOf_inj hge _
              exact fnT_not_mem n hx

/-! ### §5 the union and the divergence -/

/-- The union of the nonempty stages: the finitely-ranked trees. -/
def gUnion : PSet.{u} := iUnionN fun n => gIter2 (n + 1)

theorem fnW_not_mem_union : decG Fn2GSig fnW ∉ gUnion := by
  intro hz
  obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
  obtain ⟨p, hp⟩ := hn
  cases p with
  | mk s hsub =>
      cases s with
      | leaf =>
          have hp'' : Equiv (dataVal 0 []) (decG Fn2GSig fnW) := hp
          rw [decG_W] at hp''
          exact leafNode_absurd hp''
      | node =>
          have hp'' : Equiv (dataVal 1 [graphOf fnDom
              ((gIter2 n).Func ∘ (hsub.1 : FBr fnDom → (gIter2 n).Idx))])
              (dataVal 1 [graphOf fnDom (fun b => decG Fn2GSig (fnDepth b))]) := hp
          obtain ⟨_, hgt⟩ := ordPair_equiv (ordPair_equiv hp'').2
          have hge : LEq [graphOf fnDom ((gIter2 n).Func ∘
              (hsub.1 : FBr fnDom → (gIter2 n).Idx))]
              [graphOf fnDom (fun b => decG Fn2GSig (fnDepth b))] :=
            tup_inj (by simp) hgt
          obtain ⟨hge, _⟩ := hge
          have hx : decG Fn2GSig (fnT n) ∈ gIter2 n := by
            refine ⟨(hsub.1 : FBr fnDom → (gIter2 n).Idx) (fnCls n), ?_⟩
            have hxi := graphOf_inj hge (fnCls n)
            rw [fnDepth_cls] at hxi
            exact hxi
          exact fnT_not_mem n hx

theorem fnW_valid : ValidW Fn2GSig fnW := by
  have hval : ∀ (n : Nat), ValidW Fn2GSig (fnT n) := by
    intro n
    induction n with
    | zero => exact ValidW.sup _ _ (fun q => PEmpty.elim q) trivial
    | succ n ih => exact ValidW.sup _ _ (fun _ => ih) trivial
  exact ValidW.sup _ _ (fun q => by
    induction q using Quotient.inductionOn with
    | h n => have := fnDepth_mk n; rw [this]; exact hval n.down) trivial

/-- The divergence witness: in `gSet` (the initial-algebra reading, where
`DStar` dispatches to), in no finite stage. -/
theorem fnW_diverges :
    decG Fn2GSig fnW ∈ gSet Fn2GSig ∧ decG Fn2GSig fnW ∉ gUnion :=
  ⟨⟨⟨fnW, fnW_valid⟩, Equiv.rfl⟩, fnW_not_mem_union⟩

/-! ### §6 the pre-fixedness refutation -/

/-- The union-index: where `decG (fnDepth q)` sits in the union. -/
def fnUIdx : FBr fnDom → gUnion.Idx :=
  Quotient.lift (fun n : ULift.{u} Nat => (⟨n.down, fnIdx n.down⟩ : gUnion.Idx))
    (fun n m h => by
      have hd : n.down = m.down := ord_inj h
      show (⟨n.down, fnIdx n.down⟩ : gUnion.Idx) = ⟨m.down, fnIdx m.down⟩
      rw [hd])

theorem fnUIdx_func (q : FBr fnDom) :
    Equiv (gUnion.Func (fnUIdx q)) (decG Fn2GSig (fnDepth q)) := by
  induction q using Quotient.inductionOn with
  | h n =>
      have h1 : fnUIdx (Quotient.mk (FSetoid fnDom) n) =
          (⟨n.down, fnIdx n.down⟩ : gUnion.Idx) := rfl
      have h2 : gUnion.Func (⟨n.down, fnIdx n.down⟩ : gUnion.Idx) =
          (gIter2 (n.down + 1)).Func (fnIdx n.down) := rfl
      show Equiv (gUnion.Func (fnUIdx (Quotient.mk (FSetoid fnDom) n)))
        (decG Fn2GSig (fnDepth (Quotient.mk (FSetoid fnDom) n)))
      rw [h1, h2]
      have h3 := fnDepth_mk n
      rw [h3]
      exact fnIdx_func n.down

theorem gphi_func_node :
    (gphi Fn2GSig gUnion).Func (⟨Fn2Sh.node, ⟨fnUIdx, trivial⟩⟩ :
        (gphi Fn2GSig gUnion).Idx) =
      dataVal 1 [graphOf fnDom (fun b => gUnion.Func (fnUIdx b))] := rfl

theorem fnW_mem_gphi_union : decG Fn2GSig fnW ∈ gphi Fn2GSig gUnion := by
  refine ⟨⟨Fn2Sh.node, ⟨fnUIdx, trivial⟩⟩, ?_⟩
  rw [gphi_func_node, decG_W]
  exact dataVal_congr 1 ⟨graphOf_congr (fun q => fnUIdx_func q), trivial⟩

/-- The generic fib-continuity claim at the guarded-W level. -/
def FnContGSig : Prop :=
  ∀ (S : GSig.{u}),
    Sub (gphi S (iUnionN fun n => gIterOf S (n + 1))) (iUnionN fun n => gIterOf S (n + 1))

/-- **The refutation**: fib-continuity is false.  The height-`ω` tree is in
`gphi` of the union but not in the union. -/
theorem fnContGSig_false : ¬ FnContGSig := by
  intro h
  exact fnW_not_mem_union (h Fn2GSig _ fnW_mem_gphi_union)

/-! ### §7 the exemption: signatures with no leaf are empty -/

/-- A signature whose every shape branches has no trees at all. -/
theorem gt_empty (S : GSig.{u}) (hbr : ∀ s : S.Sh, Nonempty (S.br s)) :
    ∀ w : GT S, False := by
  intro w
  induction w with
  | sup s g ih => obtain ⟨b⟩ := hbr s; exact ih b

/-- Hence both readings collapse to empty: no divergence is possible at a
leafless `.fn` signature (the W fixture's shape — one constructor, one `.fn`
field, no base case). -/
theorem gSet_empty_of_all_branching (S : GSig.{u}) (hbr : ∀ s : S.Sh, Nonempty (S.br s)) :
    Equiv (gSet S) pempty := by
  apply ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, _⟩ := hz
    exact (gt_empty S hbr p.1).elim
  · intro hz
    exact (not_mem_pempty hz).elim

end Rcic.F3.PSet

-- audit of record (replayed builds hide this: touch the file or read the log)
open Rcic.F3.PSet in
#print axioms Rcic.F3.PSet.graphOf_inj
#print axioms Rcic.F3.PSet.fnIdx_func
#print axioms Rcic.F3.PSet.fnT_mem
#print axioms Rcic.F3.PSet.fnT_not_mem
#print axioms Rcic.F3.PSet.fnW_not_mem_union
#print axioms Rcic.F3.PSet.fnW_valid
#print axioms Rcic.F3.PSet.fnW_diverges
#print axioms Rcic.F3.PSet.fnUIdx_func
#print axioms Rcic.F3.PSet.fnW_mem_gphi_union
#print axioms Rcic.F3.PSet.fnContGSig_false
#print axioms Rcic.F3.PSet.gt_empty
#print axioms Rcic.F3.PSet.gSet_empty_of_all_branching
