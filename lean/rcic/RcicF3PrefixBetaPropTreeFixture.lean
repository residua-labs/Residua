import rcic.RcicF3UnequalPropTreeFixture

/-!
# Unequal mirrors with a local-parameter beta reader

The family and leaf are the existing UnequalPropTree declarations, including
their actual original admissions and typed parameter-mirror proofs. Only
the node field and the recursor change. The stored recursive field is
`(fun _ : Prop => Prop → F p) p`, with de Bruijn shifts explicit below.

The beta argument is the family parameter, not the fresh family constant.
This module supplies original GroupMembersT/EnvWfT data. It does not assert
universal PropOnly coverage. Source draft; root owns native validation.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

namespace Rcic.Declarative.PrefixBetaPropTree
open Rcic.Scm.SrcG
open UnequalPropTree (ownParam fam famApp leaf eFam eLeaf famSlots leafSlots
  familyView leafView familyAdm leafAdm ownParam_typed ownParam_mirror
  ownParam_beta ownParam_legacy ownParam_legacy_beta parameter_typed
  famApp_typed family_type_typed leaf_type_typed familyTyped leafTyped
  familyAdmTyped leafAdmTyped)

noncomputable section

noncomputable abbrev normalField : Expr Nat := UnequalPropTree.field
noncomputable abbrev field : Expr Nat :=
  .app (.lam (.sort .zero) (lift 0 1 normalField)) (.bvar 0)
noncomputable abbrev node : CheckedMember :=
  ⟨.constructorM, 0, .pi ownParam (.pi field (famApp (.bvar 1))), none⟩

/-- Source typing is in the actual constructor-own parameter context;
the existing typed mirror pays the argument's Prop typing. -/
noncomputable def field_typed {E : ResolvedEnv} (hF : E.members 4 = some fam) :
    HasTyT E 0 [.assumption ownParam] field (.sort (.imax (.succ .zero) .zero)) :=
  .app _ (.lam (.sort .zero) (lift 0 1 normalField)) (.bvar 0)
    (.sort .zero) (.sort (.imax (.succ .zero) .zero))
    (.lam _ (.sort .zero) (.succ .zero) (lift 0 1 normalField)
      (.sort (.imax (.succ .zero) .zero)) (.sort _ .zero)
      (.pi _ (.sort .zero) (.succ .zero) (famApp (.bvar 2)) .zero
        (.sort _ .zero)
        (famApp_typed hF [.assumption (.sort .zero),
          .assumption (.sort .zero), .assumption ownParam] 2 rfl)))
    (parameter_typed [.assumption ownParam] 0 rfl)

noncomputable def field_legacy {E : ResolvedEnv} (hF : E.members 4 = some fam) :
    HasTy E 0 [.assumption ownParam] field (.sort (.imax (.succ .zero) .zero)) :=
  .app _ (.lam (.sort .zero) (lift 0 1 normalField)) (.bvar 0)
    (.sort .zero) (.sort (.imax (.succ .zero) .zero))
    (.lam _ (.sort .zero) (.succ .zero) (lift 0 1 normalField)
      (.sort (.imax (.succ .zero) .zero)) (.sort _ .zero)
      (.pi _ (.sort .zero) (.succ .zero) (famApp (.bvar 2)) .zero
        (.sort _ .zero)
        (.app _ (.const 4 []) (.bvar 2) (.sort .zero) (.sort .zero)
          (.const _ 4 [] fam hF rfl (fun _ h => nomatch h))
          (.conv _ (.bvar 2) ownParam (.sort .zero)
            (.bvar _ 2 ownParam rfl) (ownParam_legacy_beta E _)))))
    (.conv _ (.bvar 0) ownParam (.sort .zero)
      (.bvar _ 0 ownParam rfl) (ownParam_legacy_beta E _))

noncomputable def node_type_typed {E : ResolvedEnv} (hF : E.members 4 = some fam) :
    HasTyT E 0 [] node.mtype
      (.sort (.imax (.succ .zero) (.imax (.imax (.succ .zero) .zero) .zero))) :=
  .pi [] ownParam (.succ .zero) (.pi field (famApp (.bvar 1)))
    (.imax (.imax (.succ .zero) .zero) .zero) (ownParam_typed E [])
    (.pi [.assumption ownParam] field (.imax (.succ .zero) .zero)
      (famApp (.bvar 1)) .zero (field_typed hF)
      (famApp_typed hF [.assumption field, .assumption ownParam] 1 rfl))

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
      split <;> rfl
    hasType := fun i => by
      rcases i with ⟨i, hi⟩
      change i < 2 at hi
      cases i with
      | zero => exact ownParam_legacy E []
      | succ i =>
          cases i with
          | zero => exact field_legacy hF
          | succ i => exact (by omega : False).elim }
  parameterMirrors := (UnequalPropTree.nodeView E hF).parameterMirrors
  noFamilyInIndices := fun _ h => nomatch h

noncomputable abbrev motiveTy := UnequalPropTree.motiveTy
noncomputable abbrev leafMinor := UnequalPropTree.leafMinor
noncomputable abbrev nodeFieldMinor : Expr Nat := lift 0 2 field
noncomputable abbrev nodeIH := UnequalPropTree.nodeIH
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
noncomputable abbrev ePre := extendEnv eLeaf 6 node
noncomputable abbrev eAll := extendEnv ePre 7 recMem

noncomputable def nodeAdm : IndGroupAdmitted eLeaf 6 node :=
  .constructor (familyView eLeaf rfl) (nodeView eLeaf rfl) rfl
    ⟨4, rfl, noRecursorForB_sound (by decide)
      (show noRecursorForB leafSlots 4 = true from rfl)⟩
    (ctorContiguousB_sound (by decide)
      (show ctorContiguousB leafSlots 6 node = true from rfl))
    (fun _ => Or.inl (fun _ => rfl))
    (fun i => by
      rcases i with ⟨i, hi⟩
      have hz : i = 0 := by change i < 1 at hi; omega
      subst i
      exact ⟨.recursive 1, admitFuel, [], rfl⟩)

noncomputable def recA : RecursorEliminationAdmitted ePre 7 recMem where
  family := familyView ePre rfl
  constructors := [leaf, node]
  constructorViews := fun i => by
    rcases i with ⟨i, hi⟩
    change i < 2 at hi
    cases i with
    | zero => exact leafView ePre rfl
    | succ i =>
        cases i with
        | zero => exact nodeView ePre rfl
        | succ i => exact (by omega : False).elim
  constructorsPresent := fun i => by
    rcases i with ⟨i, hi⟩
    change i < 2 at hi
    cases i with
    | zero => rfl
    | succ i =>
        cases i with
        | zero => rfl
        | succ i => exact (by omega : False).elim
  recursorRef := rfl
  minorTypes := [leafMinor, nodeMinor]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

noncomputable def recShapes (i : Fin recA.constructors.length) : List FieldShape :=
  if i.val = 0 then [] else [.recursive 1]

kernel_rfl_theorem analyzed0 :
  fieldShapesFuel ePre admitFuel 4 0 1 0 1
    (recA.constructorViews ⟨0, by decide⟩).fields = some []
kernel_rfl_theorem analyzed1 :
  fieldShapesFuel ePre admitFuel 4 0 1 0 1
    (recA.constructorViews ⟨1, by decide⟩).fields = some [.recursive 1]

theorem recAnalyzed : ∀ i, shapesWitness admitFuel recA.constructorViews recShapes i := by
  intro ⟨i, hi⟩
  change i < 2 at hi
  cases i with
  | zero => exact analyzed0
  | succ i =>
      cases i with
      | zero => exact analyzed1
      | succ i => exact (by omega : False).elim

kernel_rfl_theorem recMinorB : minorsMatchB recA admitFuel recShapes = true
noncomputable def recMinor : MinorPremisesMatch recA := minorsMatch_of recAnalyzed recMinorB

/-- The signature equation uses the family parameter context. Its field
is shifted past the motive and both minors, exactly as equationDoms does. -/
noncomputable abbrev leafIotaCtx : LCtx :=
  [.assumption nodeMinor, .assumption leafMinor, .assumption motiveTy,
    .assumption (.sort .zero)]
noncomputable abbrev nodeIotaCtx : LCtx := .assumption (lift 0 3 field) :: leafIotaCtx
noncomputable abbrev nodeCall : Expr Nat :=
  .lam (.sort .zero)
    (.app (.app (.app (.app (.app (.const 7 []) (.bvar 5))
      (.bvar 4)) (.bvar 3)) (.bvar 2)) (.app (.bvar 1) (.bvar 0)))
noncomputable abbrev nodeSchema : Expr Nat := .app (.app (.bvar 1) (.bvar 0)) nodeCall
noncomputable abbrev nodeEqType : Expr Nat :=
  .app (.bvar 3) (.app (.app (.const 6 []) (.bvar 4)) (.bvar 0))

kernel_rfl_theorem leafEquation_doms :
  equationDoms recA ⟨0, by decide⟩ =
    some [.sort .zero, motiveTy, leafMinor, nodeMinor]
kernel_rfl_theorem leafSchema_derived :
  iotaSchemaAt recA ⟨0, by decide⟩ admitFuel [] = some (.bvar 1)
kernel_rfl_theorem leafEquation_type :
  iotaEquationType recA ⟨0, by decide⟩ =
    .app (.bvar 2) (.app (.const 5 []) (.bvar 3))
kernel_rfl_theorem nodeEquation_doms :
  equationDoms recA ⟨1, by decide⟩ =
    some [.sort .zero, motiveTy, leafMinor, nodeMinor, lift 0 3 field]
kernel_rfl_theorem nodeSchema_derived :
  iotaSchemaAt recA ⟨1, by decide⟩ admitFuel [.recursive 1] = some nodeSchema
kernel_rfl_theorem nodeEquation_type :
  iotaEquationType recA ⟨1, by decide⟩ = nodeEqType

/-- The existing conversion-free legacy iota checker does not insert this
beta conversion. Supply the original judgment's derivation directly. -/
noncomputable def nodeIota_legacy : HasTy eAll 0 nodeIotaCtx nodeSchema nodeEqType := by
  let Γ := .assumption (.sort .zero) :: nodeIotaCtx
  have hM : HasTy eAll 0 nodeIotaCtx (.bvar 1) (lift 0 2 nodeMinor) :=
    .bvar _ 1 _ rfl
  have hF : HasTy eAll 0 nodeIotaCtx (.bvar 0) (lift 0 4 field) :=
    .bvar _ 0 _ rfl
  have hP' : HasTy eAll 0 Γ (.bvar 5) (.sort .zero) := .bvar _ 5 _ rfl
  have hMot' : HasTy eAll 0 Γ (.bvar 4) (lift 0 5 motiveTy) := .bvar _ 4 _ rfl
  have hLeaf' : HasTy eAll 0 Γ (.bvar 3) (lift 0 4 leafMinor) := .bvar _ 3 _ rfl
  have hNode' : HasTy eAll 0 Γ (.bvar 2) (lift 0 3 nodeMinor) := .bvar _ 2 _ rfl
  have hF' : HasTy eAll 0 Γ (.bvar 1) (lift 0 5 field) := .bvar _ 1 _ rfl
  have hFN' : HasTy eAll 0 Γ (.bvar 1) (lift 0 5 normalField) :=
    .conv _ _ _ _ hF' (.step _ _ _
      (.beta Γ (.sort .zero) (lift 0 6 normalField) (.bvar 5)))
  have hX : HasTy eAll 0 Γ (.bvar 0) (.sort .zero) := .bvar _ 0 _ rfl
  have hRec : HasTy eAll 0 Γ (.const 7 []) recTy :=
    .const _ 7 [] recMem rfl rfl (fun _ h => nomatch h)
  exact HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ hM hF)
    (HasTy.lam _ (.sort .zero) (.succ .zero) _ _ (HasTy.sort _ .zero)
      (HasTy.app _ _ _ _ _
        (HasTy.app _ _ _ _ _
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ hRec hP') hMot')
              hLeaf') hNode')
        (HasTy.app _ _ _ _ _ hFN' hX)))

noncomputable def leafIota_legacy : IotaEquationTyped recA ⟨0, by decide⟩ admitFuel [] := by
  unfold IotaEquationTyped
  rw [leafEquation_doms, leafSchema_derived, leafEquation_type]
  exact HasTy.bvar leafIotaCtx 1 _ rfl

noncomputable def nodeIota_legacy_at :
    IotaEquationTyped recA ⟨1, by decide⟩ admitFuel [.recursive 1] := by
  unfold IotaEquationTyped
  rw [nodeEquation_doms, nodeSchema_derived, nodeEquation_type]
  exact nodeIota_legacy

noncomputable def recIota : IotaDescriptorClause ePre recA where
  signatureOnly := rfl
  shapesAt := recShapes
  fuelAt := fun _ => admitFuel
  analyzed := recAnalyzed
  typed := fun i => by
    rcases i with ⟨i, hi⟩
    change i < 2 at hi
    cases i with
    | zero => exact leafIota_legacy
    | succ i =>
        cases i with
        | zero => exact nodeIota_legacy_at
        | succ i => exact (by omega : False).elim

theorem recUniverse : ∀ i, FieldUniverseAdmitted (recA.constructorViews i) :=
  fun _ _ => Or.inl (fun _ => rfl)
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

theorem nodeTyped (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    CtorTypedT (nodeView E hF) := by
  refine ⟨?_, ?_⟩
  · intro i
    rcases i with ⟨i, hi⟩
    change i < 2 at hi
    cases i with
    | zero => exact ⟨ownParam_typed E []⟩
    | succ i =>
        cases i with
        | zero => exact ⟨field_typed hF⟩
        | succ i => exact (by omega : False).elim
  · intro i
    rcases i with ⟨i, hi⟩
    have hz : i = 0 := by change i < 1 at hi; omega
    subst i
    exact ⟨ownParam_mirror E []⟩
theorem nodeAdmTyped : IndGroupTypedT nodeAdm :=
  ⟨familyTyped eLeaf rfl, nodeTyped eLeaf rfl⟩
theorem recAdmTyped : IndGroupTypedT recAdm := by
  refine ⟨familyTyped ePre rfl, ?_, ?_⟩
  · intro i
    rcases i with ⟨i, hi⟩
    change i < 2 at hi
    cases i with
    | zero => exact leafTyped ePre rfl
    | succ i =>
        cases i with
        | zero => exact nodeTyped ePre rfl
        | succ i => exact (by omega : False).elim
  · intro i
    rcases i with ⟨i, hi⟩
    change i < 2 at hi
    cases i with
    | zero =>
        exact iotaEquationTypedT_of_check
          (fun Γ e T => tyAtC _ _ admitFuel Γ e T) (by with_unfolding_all rfl)
    | succ i =>
        cases i with
        | zero =>
            exact iotaEquationTypedT_of_check
              (fun Γ e T => tyAtC _ _ admitFuel Γ e T) (by with_unfolding_all rfl)
        | succ i => exact (by omega : False).elim
noncomputable def recIdx : RecursorGroupIdxAdmittedT recA recIota :=
  .ofCheck recA recIota (by with_unfolding_all rfl)
kernel_rfl_theorem recSortHit :
  (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).isSome = true
noncomputable def recSort := (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).get recSortHit

/-- Reuse the unchanged original family and leaf admissions verbatim. -/
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

theorem ctorClasses : ∀ c ∈ [(5, leaf), (6, node)], c.2.mclass = .constructorM := by
  intro c hc
  rcases List.mem_cons.mp hc with h | h
  · cases h; rfl
  · cases List.mem_singleton.mp h; rfl
noncomputable def envWfT : EnvWfT eAll :=
  .group emptyEnv 4 fam [(5, leaf), (6, node)] 7 recMem eAll
    .empty rfl ctorClasses rfl membersT
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

end
end Rcic.Declarative.PrefixBetaPropTree

#print axioms Rcic.Declarative.PrefixBetaPropTree.field_typed
#print axioms Rcic.Declarative.PrefixBetaPropTree.nodeIota_legacy
#print axioms Rcic.Declarative.PrefixBetaPropTree.recAdmTyped
#print axioms Rcic.Declarative.PrefixBetaPropTree.envWfT
