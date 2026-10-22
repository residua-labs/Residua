import rcic.RcicAnnLR3DependentFamily

/-!
# A supplied varying-motive eliminator for an indexed signature

A selected recursive position is explicit data at each rule. The depth
along that path descends to the legal-tree quotient, and Fin(depth + 1)
is a major-dependent motive. Both algebra-respect proofs are supplied,
so quotient and paired elimination and forward constructor computation
follow without any further eliminator premise. The signature need not
be unindexed, and no tree or position is selected from a proposition.

This reusable semantic producer is independent of the source evaluator.
It does not claim an arbitrary source recursor arm. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.SelectedFamilyElimination

open UnitModel TypedInductive NeutralDataFamily DependentFamily

universe u v w l

variable {Index : Type u} {S : Signature.{u,v,w} Index}
  {Leaf : Index → Type l} {RN : ∀ i, Leaf i → Leaf i → Prop}
  (hRN : ∀ i, RelLaws (RN i))
  (selected : ∀ i (r : S.Rule i), S.Premise i r)

abbrev QuotientMajor (i : Index) := FamilyQuotient (S := S) (Leaf := Leaf) hRN i

noncomputable def depth {i : Index} (q : QuotientMajor (S := S) hRN i) : Nat :=
  quotientFold (Result := fun _ => Nat) hRN
    (fun _ _ => 0) (fun i r children => children (selected i r) + 1)
    (fun _ _ _ _ => rfl) q

noncomputable def Motive (i : Index) (q : QuotientMajor (S := S) hRN i) : Type :=
  Fin (depth hRN selected q + 1)

noncomputable def neutralResult (i : Index) (a : Leaf i) (ha : RN i a a) :
    Motive hRN selected i (treeClass hRN (legalNeutral S Leaf RN i a ha)) :=
  ⟨0, Nat.zero_lt_succ 0⟩

noncomputable def nodeResult (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p))
    (results : ∀ p, Motive hRN selected (S.child i r p) (treeClass hRN (children p))) :
    Motive hRN selected i (treeClass hRN (legalNode S Leaf RN i r children)) :=
  (results (selected i r)).succ

theorem neutralResult_respects (i : Index) (a b : Leaf i)
    (ha : RN i a a) (hb : RN i b b) (hab : RN i a b) :
    FibreRelation hRN (Motive hRN selected)
      (legalNeutral S Leaf RN i a ha) (legalNeutral S Leaf RN i b hb)
      (neutralResult hRN selected i a ha) (neutralResult hRN selected i b hb) := by
  have related : Bisim S Leaf RN (.neutral i a) (.neutral i b) :=
    Bisim.neutral (S := S) (Leaf := Leaf) (RN := RN) i a b hab
  have classEq : treeClass hRN (legalNeutral S Leaf RN i a ha) =
      treeClass hRN (legalNeutral S Leaf RN i b hb) := Quotient.sound related
  refine ⟨related, Fin.ext ?_⟩
  exact transport_fin_val (fun q : QuotientMajor hRN i => depth hRN selected q + 1)
    classEq (neutralResult hRN selected i a ha)

theorem nodeResult_respects (i : Index) (r : S.Rule i)
    (xs ys : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p))
    (us : ∀ p, Motive hRN selected (S.child i r p) (treeClass hRN (xs p)))
    (vs : ∀ p, Motive hRN selected (S.child i r p) (treeClass hRN (ys p)))
    (hchildren : ∀ p, Bisim S Leaf RN (xs p).1 (ys p).1)
    (hresults : ∀ p, FibreRelation hRN (Motive hRN selected) (xs p) (ys p) (us p) (vs p)) :
    FibreRelation hRN (Motive hRN selected)
      (legalNode S Leaf RN i r xs) (legalNode S Leaf RN i r ys)
      (nodeResult hRN selected i r xs us) (nodeResult hRN selected i r ys vs) := by
  have related : Bisim S Leaf RN
      (legalNode S Leaf RN i r xs).1 (legalNode S Leaf RN i r ys).1 :=
    Bisim.node (S := S) (Leaf := Leaf) (RN := RN)
      i r (fun p => (xs p).1) (fun p => (ys p).1) hchildren
  have classEq : treeClass hRN (legalNode S Leaf RN i r xs) =
      treeClass hRN (legalNode S Leaf RN i r ys) := Quotient.sound related
  obtain ⟨childRelated, childTransport⟩ := hresults (selected i r)
  have childEq : treeClass hRN (xs (selected i r)) =
      treeClass hRN (ys (selected i r)) := Quotient.sound childRelated
  have childVals : (us (selected i r)).val = (vs (selected i r)).val :=
    (transport_fin_val
      (fun q : QuotientMajor hRN (S.child i r (selected i r)) => depth hRN selected q + 1)
      childEq (us (selected i r))).symm.trans (congrArg Fin.val childTransport)
  refine ⟨related, Fin.ext ?_⟩
  exact (transport_fin_val (fun q : QuotientMajor hRN i => depth hRN selected q + 1)
    classEq (nodeResult hRN selected i r xs us)).trans (congrArg Nat.succ childVals)

noncomputable def quotientPosition {i : Index} (q : QuotientMajor hRN i) :
    Motive hRN selected i q :=
  quotientEliminate hRN (Motive hRN selected)
    (neutralResult hRN selected) (nodeResult hRN selected)
    (neutralResult_respects hRN selected) (nodeResult_respects hRN selected) q

theorem quotientPosition_neutral (i : Index) (a : Leaf i) (ha : RN i a a) :
    (quotientPosition hRN selected
      (treeClass hRN (legalNeutral S Leaf RN i a ha))).val = 0 := rfl

theorem quotientPosition_node (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)) :
    (quotientPosition hRN selected
      (treeClass hRN (legalNode S Leaf RN i r children))).val =
    (quotientPosition hRN selected
      (treeClass hRN (children (selected i r)))).val + 1 := rfl

noncomputable def pairedPosition
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    {i : Index} (p : Paired S Leaf RN leafValue ctor i) :
    Motive hRN selected i (pairedClass hRN p) :=
  pairedEliminate hRN (Motive hRN selected)
    (neutralResult hRN selected) (nodeResult hRN selected) p

theorem pairedPosition_transport
    {leafValue : ∀ i, Leaf i → Value} {ctor : NeutralFamily.ConstructorOp S}
    {i : Index} {p q : Paired S Leaf RN leafValue ctor i} (h : PairPER p q) :
    transport (Motive hRN selected i) (Quotient.sound h)
      (pairedPosition hRN selected p) = pairedPosition hRN selected q :=
  pairedEliminate_transport hRN (Motive hRN selected)
    (neutralResult hRN selected) (nodeResult hRN selected)
    (neutralResult_respects hRN selected) (nodeResult_respects hRN selected) h

theorem pairedPosition_node
    (leafValue : ∀ i, Leaf i → Value) (ctor : NeutralFamily.ConstructorOp S)
    (i : Index) (r : S.Rule i)
    (children : ∀ p : S.Premise i r, LegalTree S Leaf RN (S.child i r p)) :
    (pairedPosition hRN selected
      (pair leafValue ctor (legalNode S Leaf RN i r children))).val =
    (pairedPosition hRN selected (pair leafValue ctor (children (selected i r)))).val + 1 := rfl

end Rcic.Declarative.Ann.LR3.SelectedFamilyElimination
