import rcic.RcicAnnLR3IndexedAccControl

/-!
# A supplied major-dependent eliminator on the indexed decoder

All motive, neutral, constructor and transport data are constructed for
the indexed Acc-shaped semantic signature. The motive counts a selected
explicit child path, so its fibres vary with the major tree. The quotient
and paired eliminators are supplied, including constructor computation.

The selected position is actual retained data and requires no choice of
a label representative. This construction is independent of the separate
old raw-policy source guard boundary. It supplies a semantic indexed
eliminator; source Conv_iota/Conv_structIota and the source guard's
interpretation require their evaluator connection. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.IndexedFamilyElimination

open UnitModel TypedInductive NeutralDataFamily DependentFamily IndexedAccControl

def selected (i : Index) (r : signature.Rule i) : signature.Premise i r :=
  ⟨indexLabel True, NeutralPER.neutralAtom 7,
    NeutralCodes.reflectDescriptor_member (.proof False) 7⟩

abbrev Legal (i : Index) := LegalTree signature (fun _ => Nat) leafRel i
abbrev QuotientMajor (i : Index) :=
  FamilyQuotient (S := signature) (Leaf := fun _ => Nat) leaf_laws i

noncomputable def depth {i : Index} (q : QuotientMajor i) : Nat :=
  quotientFold (Result := fun _ => Nat) leaf_laws
    (fun _ _ => 0) (fun i r children => children (selected i r) + 1)
    (fun _ _ _ _ => rfl) q

noncomputable def Motive (i : Index) (q : QuotientMajor i) : Type := Fin (depth q + 1)

noncomputable def neutralResult (i : Index) (a : Nat) (ha : leafRel i a a) :
    Motive i (treeClass leaf_laws (legalNeutral signature (fun _ => Nat) leafRel i a ha)) :=
  ⟨0, Nat.zero_lt_succ 0⟩

noncomputable def nodeResult (i : Index) (r : signature.Rule i)
    (children : ∀ p : signature.Premise i r, Legal (signature.child i r p))
    (results : ∀ p, Motive (signature.child i r p) (treeClass leaf_laws (children p))) :
    Motive i (treeClass leaf_laws (legalNode signature (fun _ => Nat) leafRel i r children)) :=
  (results (selected i r)).succ

theorem neutralResult_respects (i : Index) (a b : Nat)
    (ha : leafRel i a a) (hb : leafRel i b b) (hab : leafRel i a b) :
    FibreRelation leaf_laws Motive
      (legalNeutral signature (fun _ => Nat) leafRel i a ha)
      (legalNeutral signature (fun _ => Nat) leafRel i b hb)
      (neutralResult i a ha) (neutralResult i b hb) := by
  have related : Bisim signature (fun _ => Nat) leafRel
      (.neutral i a) (.neutral i b) :=
    Bisim.neutral (S := signature) (Leaf := fun _ => Nat) (RN := leafRel) i a b hab
  have classEq :
      treeClass leaf_laws (legalNeutral signature (fun _ => Nat) leafRel i a ha) =
      treeClass leaf_laws (legalNeutral signature (fun _ => Nat) leafRel i b hb) :=
    Quotient.sound related
  refine ⟨related, Fin.ext ?_⟩
  exact transport_fin_val (fun q : QuotientMajor i => depth q + 1) classEq (neutralResult i a ha)

theorem nodeResult_respects (i : Index) (r : signature.Rule i)
    (xs ys : ∀ p : signature.Premise i r, Legal (signature.child i r p))
    (us : ∀ p, Motive (signature.child i r p) (treeClass leaf_laws (xs p)))
    (vs : ∀ p, Motive (signature.child i r p) (treeClass leaf_laws (ys p)))
    (hchildren : ∀ p, Bisim signature (fun _ => Nat) leafRel (xs p).1 (ys p).1)
    (hresults : ∀ p, FibreRelation leaf_laws Motive (xs p) (ys p) (us p) (vs p)) :
    FibreRelation leaf_laws Motive
      (legalNode signature (fun _ => Nat) leafRel i r xs)
      (legalNode signature (fun _ => Nat) leafRel i r ys)
      (nodeResult i r xs us) (nodeResult i r ys vs) := by
  have related : Bisim signature (fun _ => Nat) leafRel
      (legalNode signature (fun _ => Nat) leafRel i r xs).1
      (legalNode signature (fun _ => Nat) leafRel i r ys).1 :=
    Bisim.node (S := signature) (Leaf := fun _ => Nat) (RN := leafRel)
      i r (fun p => (xs p).1) (fun p => (ys p).1) hchildren
  have classEq :
      treeClass leaf_laws (legalNode signature (fun _ => Nat) leafRel i r xs) =
      treeClass leaf_laws (legalNode signature (fun _ => Nat) leafRel i r ys) :=
    Quotient.sound related
  obtain ⟨childRelated, childTransport⟩ := hresults (selected i r)
  have childEq : treeClass leaf_laws (xs (selected i r)) =
      treeClass leaf_laws (ys (selected i r)) := Quotient.sound childRelated
  have childVals : (us (selected i r)).val = (vs (selected i r)).val :=
    (transport_fin_val
      (fun q : QuotientMajor (signature.child i r (selected i r)) => depth q + 1)
      childEq (us (selected i r))).symm.trans (congrArg Fin.val childTransport)
  refine ⟨related, Fin.ext ?_⟩
  exact (transport_fin_val (fun q : QuotientMajor i => depth q + 1)
    classEq (nodeResult i r xs us)).trans (congrArg Nat.succ childVals)

/-- Every compatibility premise is supplied above for this varying motive. -/
noncomputable def quotientPosition {i : Index} (q : QuotientMajor i) : Motive i q :=
  quotientEliminate leaf_laws Motive neutralResult nodeResult
    neutralResult_respects nodeResult_respects q

theorem quotientPosition_neutral (i : Index) (a : Nat) (ha : leafRel i a a) :
    (quotientPosition (treeClass leaf_laws
      (legalNeutral signature (fun _ => Nat) leafRel i a ha))).val = 0 := rfl

theorem quotientPosition_node (i : Index) (r : signature.Rule i)
    (children : ∀ p : signature.Premise i r, Legal (signature.child i r p)) :
    (quotientPosition (treeClass leaf_laws
      (legalNode signature (fun _ => Nat) leafRel i r children))).val =
    (quotientPosition (treeClass leaf_laws (children (selected i r)))).val + 1 := rfl

noncomputable def pairedPosition
    {leafValue : ∀ i : Index, Nat → Value} {ctor : NeutralFamily.ConstructorOp signature}
    {i : Index} (p : Paired signature (fun _ => Nat) leafRel leafValue ctor i) :
    Motive i (pairedClass leaf_laws p) :=
  pairedEliminate leaf_laws Motive neutralResult nodeResult p

theorem pairedPosition_transport
    {leafValue : ∀ i : Index, Nat → Value} {ctor : NeutralFamily.ConstructorOp signature}
    {i : Index} {p q : Paired signature (fun _ => Nat) leafRel leafValue ctor i}
    (h : PairPER p q) :
    transport (Motive i) (Quotient.sound h) (pairedPosition p) = pairedPosition q :=
  pairedEliminate_transport leaf_laws Motive neutralResult nodeResult
    neutralResult_respects nodeResult_respects h

/-- Forward computation on an actual retained constructor tree. No
completed-relation converse or source normalization is used. -/
theorem pairedPosition_node
    (leafValue : ∀ i : Index, Nat → Value) (ctor : NeutralFamily.ConstructorOp signature)
    (i : Index) (r : signature.Rule i)
    (children : ∀ p : signature.Premise i r, Legal (signature.child i r p)) :
    (pairedPosition (pair leafValue ctor
      (legalNode signature (fun _ => Nat) leafRel i r children))).val =
    (pairedPosition (pair leafValue ctor (children (selected i r)))).val + 1 := rfl

def leafValue (_i : Index) (name : Nat) : Value := NeutralPER.neutralAtom name
def constructorValue : NeutralFamily.ConstructorOp signature :=
  fun i r children => NeutralFamily.unarySpine 11 (children (selected i r))

def pairedMajor : Paired signature (fun _ => Nat) leafRel leafValue constructorValue (index False) :=
  pair leafValue constructorValue major

/-- Distinct root and recursive indices, an inhabited explicit major,
and the actual varying-motive paired computation hold together. -/
theorem indexed_eliminator_control :
    index False ≠ index True ∧
    depth (treeClass leaf_laws major) = 1 ∧
    (quotientPosition (treeClass leaf_laws major)).val = 1 ∧
    (pairedPosition pairedMajor).val = 1 ∧ PairPER pairedMajor pairedMajor :=
  ⟨indices_distinct, rfl, rfl, rfl, major.2⟩

end Rcic.Declarative.Ann.LR3.IndexedFamilyElimination
