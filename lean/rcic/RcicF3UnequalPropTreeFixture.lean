import rcic.RcicIndGroupAdmitExec
import rcic.RcicTypedFunRecPins
import rcic.RcicF3Cover

/-!
# An actual parameterized PropOnly tree with unequal parameter syntax

F : (p : Prop) → Prop has a leaf/base row and a recursive-1 node row.
Both constructors store the beta-expanded parameter type
`(fun _ : Sort 1 => Prop) Prop`, while the family stores Prop itself.
The original recursive field is literally `Prop → F p`.

Actual views, the recursor and the original GroupMembersT chain are
constructed explicitly: the convenience view builder only supports literal
parameter equality. Typed beta conversion and original source typing
derivations supply the nonliteral mirror; the typed iota schema is checked.
There is no cumulativity premise. Source-only draft; root owns native
validation. closure_claim = 0.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option autoImplicit false

namespace Rcic.Declarative.UnequalPropTree
open Rcic.Scm.SrcG

-- Explicit noncomputable declarations retain kernel terms without compiler helpers.
noncomputable section

noncomputable abbrev ownParam : Expr Nat :=
  .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)
noncomputable abbrev fam : CheckedMember :=
  ⟨.inductiveM, 0, .pi (.sort .zero) (.sort .zero), none⟩
noncomputable abbrev famApp (p : Expr Nat) : Expr Nat := .app (.const 4 []) p
noncomputable abbrev leaf : CheckedMember :=
  ⟨.constructorM, 0, .pi ownParam (famApp (.bvar 0)), none⟩
noncomputable abbrev field : Expr Nat := .pi (.sort .zero) (famApp (.bvar 1))
noncomputable abbrev node : CheckedMember :=
  ⟨.constructorM, 0, .pi ownParam (.pi field (famApp (.bvar 1))), none⟩

/-- The nonliteral parameter mirror is an explicit typed beta conversion. -/
noncomputable def ownParam_typed (E : ResolvedEnv) (Γ : LCtx) :
    HasTyT E 0 Γ ownParam (.sort (.succ .zero)) :=
  .app Γ (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)
    (.sort (.succ .zero)) (.sort (.succ .zero))
    (.lam Γ (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort .zero) (.sort (.succ .zero))
      (.sort Γ (.succ .zero))
      (.sort (.assumption (.sort (.succ .zero)) :: Γ) .zero))
    (.sort Γ .zero)

noncomputable def ownParam_beta (E : ResolvedEnv) (Γ : LCtx) :
    ConvT E 0 Γ ownParam (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.sort (.succ .zero)) (.sort .zero) (.sort .zero)
    (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort Γ (.succ .zero))
    (.sort (.assumption (.sort (.succ .zero)) :: Γ) .zero)
    (.sort Γ .zero)

noncomputable def ownParam_mirror (E : ResolvedEnv) (Γ : LCtx) :
    TyConvT E 0 Γ ownParam (.sort .zero) :=
  .of Γ ownParam (.sort .zero) (.succ .zero) (ownParam_beta E Γ)

noncomputable def parameter_typed {E : ResolvedEnv} (Γ : LCtx) (k : Nat)
    (hk : lookupType Γ k = some ownParam) :
    HasTyT E 0 Γ (.bvar k) (.sort .zero) :=
  .conv Γ (.bvar k) ownParam (.sort .zero) (.succ .zero)
    (.bvar Γ k ownParam hk) (ownParam_beta E Γ)

noncomputable def famApp_typed {E : ResolvedEnv}
    (hF : E.members 4 = some fam) (Γ : LCtx) (k : Nat)
    (hk : lookupType Γ k = some ownParam) :
    HasTyT E 0 Γ (famApp (.bvar k)) (.sort .zero) :=
  .app Γ (.const 4 []) (.bvar k) (.sort .zero) (.sort .zero)
    (.const Γ 4 [] fam hF rfl rfl) (parameter_typed Γ k hk)

noncomputable def field_typed {E : ResolvedEnv}
    (hF : E.members 4 = some fam) :
    HasTyT E 0 [.assumption ownParam] field (.sort (.imax (.succ .zero) .zero)) :=
  .pi [.assumption ownParam] (.sort .zero) (.succ .zero)
    (famApp (.bvar 1)) .zero (.sort [.assumption ownParam] .zero)
    (famApp_typed hF [.assumption (.sort .zero), .assumption ownParam] 1 rfl)

noncomputable def leaf_type_typed {E : ResolvedEnv}
    (hF : E.members 4 = some fam) :
    HasTyT E 0 [] leaf.mtype (.sort (.imax (.succ .zero) .zero)) :=
  .pi [] ownParam (.succ .zero) (famApp (.bvar 0)) .zero
    (ownParam_typed E []) (famApp_typed hF [.assumption ownParam] 0 rfl)

noncomputable def node_type_typed {E : ResolvedEnv}
    (hF : E.members 4 = some fam) :
    HasTyT E 0 [] node.mtype
      (.sort (.imax (.succ .zero) (.imax (.imax (.succ .zero) .zero) .zero))) :=
  .pi [] ownParam (.succ .zero) (.pi field (famApp (.bvar 1)))
    (.imax (.imax (.succ .zero) .zero) .zero) (ownParam_typed E [])
    (.pi [.assumption ownParam] field (.imax (.succ .zero) .zero)
      (famApp (.bvar 1)) .zero (field_typed hF)
      (famApp_typed hF [.assumption field, .assumption ownParam] 1 rfl))

/-- Legacy evidence used only by the original admission records. The
same beta step has the explicit typed witness `ownParam_beta` above. -/
noncomputable def ownParam_legacy (E : ResolvedEnv) (Γ : LCtx) :
    HasTy E 0 Γ ownParam (.sort (.succ .zero)) :=
  .app Γ (.lam (.sort (.succ .zero)) (.sort .zero)) (.sort .zero)
    (.sort (.succ .zero)) (.sort (.succ .zero))
    (.lam Γ (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort .zero) (.sort (.succ .zero))
      (.sort Γ (.succ .zero))
      (.sort (.assumption (.sort (.succ .zero)) :: Γ) .zero))
    (.sort Γ .zero)

noncomputable def ownParam_legacy_beta (E : ResolvedEnv) (Γ : LCtx) :
    Conv E 0 Γ ownParam (.sort .zero) :=
  .step Γ ownParam (.sort .zero)
    (.beta Γ (.sort (.succ .zero)) (.sort .zero) (.sort .zero))

noncomputable def field_legacy {E : ResolvedEnv}
    (hF : E.members 4 = some fam) :
    HasTy E 0 [.assumption ownParam] field (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ (.sort .zero) (.succ .zero) (famApp (.bvar 1)) .zero
    (.sort _ .zero)
    (.app _ (.const 4 []) (.bvar 1) (.sort .zero) (.sort .zero)
      (.const _ 4 [] fam hF rfl (fun _ h => nomatch h))
      (.conv _ (.bvar 1) ownParam (.sort .zero)
        (.bvar _ 1 ownParam rfl) (ownParam_legacy_beta E _)))

noncomputable def familyView (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    PolicyFamilyView E where
  ref := 4
  member := fam
  present := hF
  hasClass := rfl
  parameters := [.sort .zero]
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => by
      rcases i with ⟨i, hi⟩
      have hzero : i = 0 := by change i < 1 at hi; omega
      subst i
      exact HasTy.sort [] .zero }

noncomputable def leafView (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    PolicyConstructorView E (familyView E hF) leaf where
  hasClass := rfl
  arity := rfl
  parameters := [ownParam]
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => by
      rcases i with ⟨i, hi⟩
      have hzero : i = 0 := by change i < 1 at hi; omega
      subst i
      exact ownParam_legacy E [] }
  parameterMirrors := fun i => by
    rcases i with ⟨i, hi⟩
    have hzero : i = 0 := by change i < 1 at hi; omega
    subst i
    exact ownParam_legacy_beta E []
  noFamilyInIndices := fun _ h => nomatch h

noncomputable def nodeView (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    PolicyConstructorView E (familyView E hF) node where
  hasClass := rfl
  arity := rfl
  parameters := [ownParam]
  fields := [field]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun i => if i.val = 0 then .succ .zero else .imax (.succ .zero) .zero
    bounded := fun i => by
      change levelBounded 0
        (if i.val = 0 then .succ .zero else .imax (.succ .zero) .zero) = true
      by_cases hzero : i.val = 0
      · rw [if_pos hzero]
        rfl
      · rw [if_neg hzero]
        rfl
    hasType := fun i => by
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => exact ownParam_legacy E []
      | succ i =>
          cases i with
          | zero => exact field_legacy hF
          | succ i =>
              have h : i + 1 + 1 < 2 := hi
              exact (by omega : False).elim }
  parameterMirrors := fun i => by
    rcases i with ⟨i, hi⟩
    have hzero : i = 0 := by change i < 1 at hi; omega
    subst i
    exact ownParam_legacy_beta E []
  noFamilyInIndices := fun _ h => nomatch h

/-- Explicit minors keep the declared family parameter in the recursor;
constructor-own parameters are related by the actual beta mirror. -/
noncomputable abbrev motiveTy : Expr Nat := .pi (famApp (.bvar 0)) (.sort .zero)
noncomputable abbrev leafMinor : Expr Nat :=
  .app (.bvar 0) (.app (.const 5 []) (.bvar 1))
noncomputable abbrev nodeFieldMinor : Expr Nat :=
  .pi (.sort .zero) (famApp (.bvar 3))
noncomputable abbrev nodeIH : Expr Nat :=
  .pi (.sort .zero) (.app (.bvar 3) (.app (.bvar 1) (.bvar 0)))
noncomputable abbrev nodeMinor : Expr Nat :=
  .pi nodeFieldMinor (.pi nodeIH
    (.app (.bvar 3) (.app (.app (.const 6 []) (.bvar 4)) (.bvar 1))))
noncomputable def recTy : Expr Nat :=
  .pi (.sort .zero) (.pi motiveTy (.pi leafMinor (.pi nodeMinor
    (.pi (famApp (.bvar 3)) (.app (.bvar 3) (.bvar 0))))))
noncomputable def recMem : CheckedMember := ⟨.recursorM, 0, recTy, none⟩
noncomputable def preSlots : List (Nat × CheckedMember) := [(4, fam), (5, leaf), (6, node)]
theorem prefixNd : (preSlots.map (·.1)).Nodup := by decide
noncomputable def slots : List (Nat × CheckedMember) := preSlots ++ [(7, recMem)]
theorem slotsNd : (slots.map (·.1)).Nodup := by decide

noncomputable abbrev famSlots : List (Nat × CheckedMember) := [(4, fam)]
noncomputable abbrev leafSlots : List (Nat × CheckedMember) := [(4, fam), (5, leaf)]
noncomputable abbrev eFam := extendEnv emptyEnv 4 fam
noncomputable abbrev eLeaf := extendEnv eFam 5 leaf
noncomputable abbrev ePre := extendEnv eLeaf 6 node
noncomputable abbrev eAll := extendEnv ePre 7 recMem

noncomputable def familyAdm : IndGroupAdmitted emptyEnv 4 fam :=
  .family rfl (familyView eFam rfl) rfl rfl (Or.inl (fun _ => rfl))

noncomputable def leafAdm : IndGroupAdmitted eFam 5 leaf :=
  .constructor (familyView eFam rfl) (leafView eFam rfl) rfl
    ⟨4, rfl, noRecursorForB_sound (by decide)
      (show noRecursorForB famSlots 4 = true from rfl)⟩
    (ctorContiguousB_sound (by decide)
      (show ctorContiguousB famSlots 5 leaf = true from rfl))
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)

noncomputable def nodeAdm : IndGroupAdmitted eLeaf 6 node :=
  .constructor (familyView eLeaf rfl) (nodeView eLeaf rfl) rfl
    ⟨4, rfl, noRecursorForB_sound (by decide)
      (show noRecursorForB leafSlots 4 = true from rfl)⟩
    (ctorContiguousB_sound (by decide)
      (show ctorContiguousB leafSlots 6 node = true from rfl))
    (fun _ => Or.inl (fun _ => rfl))
    (fun | ⟨0, _⟩ => ⟨.recursive 1, admitFuel, [], rfl⟩)

noncomputable def recA : RecursorEliminationAdmitted ePre 7 recMem where
  family := familyView ePre rfl
  constructors := [leaf, node]
  constructorViews := fun i => by
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => exact leafView ePre rfl
    | succ i =>
        cases i with
        | zero => exact nodeView ePre rfl
        | succ i =>
            have h : i + 1 + 1 < 2 := hi
            exact (by omega : False).elim
  constructorsPresent := fun i => by
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ i =>
        cases i with
        | zero => rfl
        | succ i =>
            have h : i + 1 + 1 < 2 := hi
            exact (by omega : False).elim
  recursorRef := rfl
  minorTypes := [leafMinor, nodeMinor]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

kernel_rfl_theorem family_parameters : recA.family.parameters = [.sort .zero]
kernel_rfl_theorem family_indices : recA.family.indices = []
kernel_rfl_theorem family_result : recA.family.resultLevel = .zero
kernel_rfl_theorem family_arity : recA.family.member.arity = 0
kernel_rfl_theorem rec_policy : recA.policy = .propOnly
kernel_rfl_theorem constructor_count : recA.constructors.length = 2

noncomputable def recShapes (i : Fin recA.constructors.length) : List FieldShape :=
  if i.val = 0 then [] else [.recursive 1]

kernel_rfl_theorem analyzed0 :
  fieldShapesFuel ePre admitFuel recA.family.ref recA.family.member.arity
    recA.family.parameters.length recA.family.indices.length recA.family.parameters.length
    (recA.constructorViews ⟨0, by decide⟩).fields = some []
kernel_rfl_theorem analyzed1 :
  fieldShapesFuel ePre admitFuel recA.family.ref recA.family.member.arity
    recA.family.parameters.length recA.family.indices.length recA.family.parameters.length
    (recA.constructorViews ⟨1, by decide⟩).fields = some [.recursive 1]

theorem recAnalyzed : ∀ i, shapesWitness admitFuel recA.constructorViews recShapes i := by
  intro ⟨i, hi⟩
  cases i with
  | zero => exact analyzed0
  | succ i =>
    cases i with
    | zero => exact analyzed1
    | succ i =>
      have h : i + 1 + 1 < 2 := hi
      exact (by omega : False).elim

kernel_rfl_theorem recMinorB : minorsMatchB recA admitFuel recShapes = true
noncomputable def recMinor : MinorPremisesMatch recA := minorsMatch_of recAnalyzed recMinorB
kernel_rfl_theorem recIotaHit :
  (iotaClause? recA admitFuel recShapes recAnalyzed rfl).isSome = true
noncomputable def recIota : IotaDescriptorClause ePre recA :=
  (iotaClause? recA admitFuel recShapes recAnalyzed rfl).get recIotaHit

theorem recUniverse : ∀ i, FieldUniverseAdmitted (recA.constructorViews i) := by
  intro i j
  exact Or.inl (fun σ => by rw [family_result]; rfl)

kernel_rfl_theorem recFieldsB :
  finAllB recA.constructors.length
    (fun i hi => ctorFieldsPermittedB (recA.constructorViews ⟨i, hi⟩) admitFuel) = true
kernel_rfl_theorem recCensusB : ctorCensusB preSlots 4 7 = true
noncomputable def recCensus : CtorCensus ePre recA.family.ref 7 :=
  ctorCensusB_sound prefixNd recCensusB

noncomputable def recAdm : IndGroupAdmitted ePre 7 recMem :=
  .recursor recA rfl recCensus recUniverse
    (fun i => ctorFieldsPermitted_of_B _ admitFuel (finAllB_sound recFieldsB i))
    recMinor recIota

noncomputable def family_type_typed :
    HasTyT emptyEnv 0 [] fam.mtype (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort [] .zero) (.sort [.assumption (.sort .zero)] .zero)

kernel_rfl_theorem recSortHit :
  (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).isSome = true
noncomputable def recSort := (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).get recSortHit

theorem familyTyped (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    FamilyTypedT (familyView E hF) :=
  fun | ⟨0, _⟩ => ⟨HasTyT.sort [] .zero⟩

theorem leafTyped (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    CtorTypedT (leafView E hF) :=
  ⟨(fun | ⟨0, _⟩ => ⟨ownParam_typed E []⟩),
    (fun | ⟨0, _⟩ => ⟨ownParam_mirror E []⟩)⟩

theorem nodeTyped (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    CtorTypedT (nodeView E hF) :=
  ⟨(fun | ⟨0, _⟩ => ⟨ownParam_typed E []⟩ | ⟨1, _⟩ => ⟨field_typed hF⟩),
    (fun | ⟨0, _⟩ => ⟨ownParam_mirror E []⟩)⟩

theorem familyAdmTyped : IndGroupTypedT familyAdm := familyTyped eFam rfl
theorem leafAdmTyped : IndGroupTypedT leafAdm :=
  ⟨familyTyped eFam rfl, leafTyped eFam rfl⟩
theorem nodeAdmTyped : IndGroupTypedT nodeAdm :=
  ⟨familyTyped eLeaf rfl, nodeTyped eLeaf rfl⟩

theorem recAdmTyped : IndGroupTypedT recAdm :=
  ⟨familyTyped ePre rfl,
    (fun | ⟨0, _⟩ => leafTyped ePre rfl | ⟨1, _⟩ => nodeTyped ePre rfl),
    (fun i => by
      match i with
      | ⟨0, _⟩ =>
          exact iotaEquationTypedT_of_check
            (fun Γ e T => tyAtC _ _ admitFuel Γ e T) (by with_unfolding_all rfl)
      | ⟨1, _⟩ =>
          exact iotaEquationTypedT_of_check
            (fun Γ e T => tyAtC _ _ admitFuel Γ e T) (by with_unfolding_all rfl))⟩

noncomputable def recIdx : RecursorGroupIdxAdmittedT recA recIota :=
  .ofCheck recA recIota (by with_unfolding_all rfl)

/-- Actual original group admission, with the unequal typed mirror supplied
explicitly. No literal-equality convenience builder is used for a view. -/
noncomputable def membersT : GroupMembersT eFam emptyEnv slots eAll :=
  .cons _ 4 fam _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    familyAdm PUnit.unit _ family_type_typed (fun h => absurd h (by decide)) familyAdmTyped
    (.cons _ 5 leaf _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      leafAdm PUnit.unit _ (leaf_type_typed rfl) (fun _ => ⟨leaf_type_typed rfl⟩) leafAdmTyped
      (.cons _ 6 node _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        nodeAdm PUnit.unit _ (node_type_typed rfl) (fun _ => ⟨node_type_typed rfl⟩) nodeAdmTyped
        (.cons _ 7 recMem [] _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
          recAdm recIdx recSort.1 recSort.2 (fun h => absurd h (by decide))
          recAdmTyped (.nil _))))

noncomputable def envWfT : EnvWfT eAll :=
  .group emptyEnv 4 fam [(5, leaf), (6, node)] 7 recMem eAll .empty rfl
    (fun c hc => by
      rcases List.mem_cons.mp hc with h | h
      · cases h; rfl
      · cases List.mem_singleton.mp h; rfl)
    rfl membersT

noncomputable def pNode : Rcic.F3.PSet.RecNode emptyEnv eAll 4 7 recMem where
  E0 := ePre
  a := recA
  h14 := recIota
  fam := rfl
  fresh := rfl
  sub := fun _ _ h => h
  base := fun _ _ h => by cases h
  h04 := recCensus
  h07 := recUniverse
  h12 := recMinor
  famTyped := recAdmTyped.1
  ctorsTyped := recAdmTyped.2.1
  u := recSort.1
  hT := recSort.2

kernel_rfl_theorem nodeShape :
  (pNode.h14.shapesAt ⟨1, by decide⟩)[0]? = some (.recursive 1)

theorem pendA : Rcic.F3.PSet.PendA pNode :=
  ⟨⟨1, by decide⟩, 0, 0, nodeShape⟩

/-- This is literal admission of the unequal mirror, with a separately
constructed TyConvT equality rather than an asserted cumulative inclusion. -/
def Witness : Prop :=
  Nonempty (EnvWfT eAll) ∧ recA.family.parameters = [.sort .zero] ∧
  recA.family.indices = [] ∧ recA.policy = .propOnly ∧
  Rcic.F3.PSet.PendA pNode ∧
  Nonempty (TyConvT ePre 0 [] ownParam (.sort .zero)) ∧
  (∀ i, CtorTypedT (recA.constructorViews i))

theorem component_witness : Witness :=
  ⟨⟨envWfT⟩, family_parameters, family_indices, rec_policy, pendA,
    ⟨ownParam_mirror ePre []⟩, recAdmTyped.2.1⟩

end
end Rcic.Declarative.UnequalPropTree

#print axioms Rcic.Declarative.UnequalPropTree.ownParam_mirror
#print axioms Rcic.Declarative.UnequalPropTree.envWfT
#print axioms Rcic.Declarative.UnequalPropTree.component_witness
