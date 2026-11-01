import rcic.RcicIndGroupAdmitExec
import rcic.RcicTypedFunRecPins
import rcic.RcicF3Cover

/-!
# A universe-polymorphic empty-field parameter mirror

This is an auxiliary boundary fixture, not a refutation of StepPropOnly.
The family has two nullary constructors, so its original policy is
PropOnly and every field is plain. The constructors' own parameter is
`(fun _ : Sort (u+2) => Prop) (Sort (u+1))`; the family parameter is Prop.
All parameter conversions below are actual typed beta derivations.

The separate bounds module asks the original constructor bounds only at
u = 0, while the recursor may be instantiated at u = 3. The empty fields
make original BoundDG vacuous. This isolates the quantifier mismatch in
an overstrong universal own-parameter-fit lemma. It does not claim any
failure of the original group invariant, which is already covered by
the AllPlain producer.

Source-only draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

namespace Rcic.Declarative.PropOnlyEmptyMirror
open Rcic.Scm.SrcG
noncomputable section

noncomputable abbrev ul : Level := .param 0
noncomputable abbrev argLevel : Level := .succ ul
noncomputable abbrev domLevel : Level := .succ argLevel
noncomputable abbrev ownParam : Expr Nat :=
  .app (.lam (.sort domLevel) (.sort .zero)) (.sort argLevel)
noncomputable abbrev fam : CheckedMember :=
  ⟨.inductiveM, 1, .pi (.sort .zero) (.sort .zero), none⟩
noncomputable abbrev famApp (p : Expr Nat) : Expr Nat := .app (.const 4 [ul]) p
noncomputable abbrev leaf : CheckedMember :=
  ⟨.constructorM, 1, .pi ownParam (famApp (.bvar 0)), none⟩

noncomputable def ownParam_typed (E : ResolvedEnv) (Γ : LCtx) :
    HasTyT E 1 Γ ownParam (.sort (.succ .zero)) :=
  .app Γ (.lam (.sort domLevel) (.sort .zero)) (.sort argLevel)
    (.sort domLevel) (.sort (.succ .zero))
    (.lam Γ (.sort domLevel) (.succ domLevel)
      (.sort .zero) (.sort (.succ .zero))
      (.sort Γ domLevel)
      (.sort (.assumption (.sort domLevel) :: Γ) .zero))
    (.sort Γ argLevel)

noncomputable def ownParam_beta (E : ResolvedEnv) (Γ : LCtx) :
    ConvT E 1 Γ ownParam (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.sort domLevel) (.sort .zero) (.sort argLevel)
    (.sort (.succ .zero)) (.succ domLevel)
    (.sort Γ domLevel)
    (.sort (.assumption (.sort domLevel) :: Γ) .zero)
    (.sort Γ argLevel)

noncomputable def ownParam_mirror (E : ResolvedEnv) (Γ : LCtx) :
    TyConvT E 1 Γ ownParam (.sort .zero) :=
  .of Γ ownParam (.sort .zero) (.succ .zero) (ownParam_beta E Γ)

noncomputable def parameter_typed {E : ResolvedEnv} (Γ : LCtx) (k : Nat)
    (hk : lookupType Γ k = some ownParam) :
    HasTyT E 1 Γ (.bvar k) (.sort .zero) :=
  .conv Γ (.bvar k) ownParam (.sort .zero) (.succ .zero)
    (.bvar Γ k ownParam hk) (ownParam_beta E Γ)

noncomputable def famApp_typed {E : ResolvedEnv}
    (hF : E.members 4 = some fam) (Γ : LCtx) (k : Nat)
    (hk : lookupType Γ k = some ownParam) :
    HasTyT E 1 Γ (famApp (.bvar k)) (.sort .zero) :=
  .app Γ (.const 4 [ul]) (.bvar k) (.sort .zero) (.sort .zero)
    (.const Γ 4 [ul] fam hF rfl rfl) (parameter_typed Γ k hk)

noncomputable def leaf_type_typed {E : ResolvedEnv}
    (hF : E.members 4 = some fam) :
    HasTyT E 1 [] leaf.mtype (.sort (.imax (.succ .zero) .zero)) :=
  .pi [] ownParam (.succ .zero) (famApp (.bvar 0)) .zero
    (ownParam_typed E []) (famApp_typed hF [.assumption ownParam] 0 rfl)

noncomputable def ownParam_legacy (E : ResolvedEnv) (Γ : LCtx) :
    HasTy E 1 Γ ownParam (.sort (.succ .zero)) :=
  .app Γ (.lam (.sort domLevel) (.sort .zero)) (.sort argLevel)
    (.sort domLevel) (.sort (.succ .zero))
    (.lam Γ (.sort domLevel) (.succ domLevel)
      (.sort .zero) (.sort (.succ .zero))
      (.sort Γ domLevel)
      (.sort (.assumption (.sort domLevel) :: Γ) .zero))
    (.sort Γ argLevel)

noncomputable def ownParam_legacy_beta (E : ResolvedEnv) (Γ : LCtx) :
    Conv E 1 Γ ownParam (.sort .zero) :=
  .step Γ ownParam (.sort .zero)
    (.beta Γ (.sort domLevel) (.sort .zero) (.sort argLevel))

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
    hasType := by
      intro i
      obtain ⟨k, hk⟩ := i
      have hk0 : k = 0 := by change k < 1 at hk; omega
      subst k
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
    hasType := by
      intro i
      obtain ⟨k, hk⟩ := i
      have hk0 : k = 0 := by change k < 1 at hk; omega
      subst k
      exact ownParam_legacy E [] }
  parameterMirrors := by
    intro i
    obtain ⟨k, hk⟩ := i
    have hk0 : k = 0 := by change k < 1 at hk; omega
    subst k
    exact ownParam_legacy_beta E []
  noFamilyInIndices := by
    intro e he
    exact (List.not_mem_nil e he).elim

noncomputable abbrev motiveTy : Expr Nat := .pi (famApp (.bvar 0)) (.sort .zero)
noncomputable abbrev leafMinor : Expr Nat := .app (.bvar 0) (.app (.const 5 [ul]) (.bvar 1))
noncomputable abbrev leaf2Minor : Expr Nat := .app (.bvar 1) (.app (.const 6 [ul]) (.bvar 2))
noncomputable def recTy : Expr Nat :=
  .pi (.sort .zero) (.pi motiveTy (.pi leafMinor (.pi leaf2Minor
    (.pi (famApp (.bvar 3)) (.app (.bvar 3) (.bvar 0))))))
noncomputable def recMem : CheckedMember := ⟨.recursorM, 1, recTy, none⟩
noncomputable def preSlots : List (Nat × CheckedMember) := [(4, fam), (5, leaf), (6, leaf)]
theorem prefixNd : (preSlots.map (·.1)).Nodup := by decide
noncomputable def slots : List (Nat × CheckedMember) := preSlots ++ [(7, recMem)]
theorem slotsNd : (slots.map (·.1)).Nodup := by decide
noncomputable abbrev famSlots : List (Nat × CheckedMember) := [(4, fam)]
noncomputable abbrev leafSlots : List (Nat × CheckedMember) := [(4, fam), (5, leaf)]
noncomputable abbrev eFam := extendEnv emptyEnv 4 fam
noncomputable abbrev eLeaf := extendEnv eFam 5 leaf
noncomputable abbrev ePre := extendEnv eLeaf 6 leaf
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

noncomputable def leaf2Adm : IndGroupAdmitted eLeaf 6 leaf :=
  .constructor (familyView eLeaf rfl) (leafView eLeaf rfl) rfl
    ⟨4, rfl, noRecursorForB_sound (by decide)
      (show noRecursorForB leafSlots 4 = true from rfl)⟩
    (ctorContiguousB_sound (by decide)
      (show ctorContiguousB leafSlots 6 leaf = true from rfl))
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)

noncomputable def recA : RecursorEliminationAdmitted ePre 7 recMem where
  family := familyView ePre rfl
  constructors := [leaf, leaf]
  constructorViews := by
    intro i
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => exact leafView ePre rfl
    | succ k =>
        have hk0 : k = 0 := by change k + 1 < 2 at hk; omega
        subst k
        exact leafView ePre rfl
  constructorsPresent := by
    intro i
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => rfl
    | succ k =>
        have hk0 : k = 0 := by change k + 1 < 2 at hk; omega
        subst k
        rfl
  recursorRef := rfl
  minorTypes := [leafMinor, leaf2Minor]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem family_parameters : recA.family.parameters = [.sort .zero] := rfl
theorem family_indices : recA.family.indices = [] := rfl
theorem family_result : recA.family.resultLevel = .zero := rfl
theorem family_arity : recA.family.member.arity = 1 := rfl
theorem rec_policy : recA.policy = .propOnly := rfl
theorem constructor_count : recA.constructors.length = 2 := rfl
noncomputable def recShapes (_i : Fin recA.constructors.length) : List FieldShape := []

theorem recAnalyzed : ∀ i, shapesWitness admitFuel recA.constructorViews recShapes i := by
  intro ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl

theorem recMinorB : minorsMatchB recA admitFuel recShapes = true := by
  with_unfolding_all rfl
noncomputable def recMinor : MinorPremisesMatch recA := minorsMatch_of recAnalyzed recMinorB
theorem recIotaHit :
    (iotaClause? recA admitFuel recShapes recAnalyzed rfl).isSome = true := by
  with_unfolding_all rfl
noncomputable def recIota : IotaDescriptorClause ePre recA :=
  (iotaClause? recA admitFuel recShapes recAnalyzed rfl).get recIotaHit

theorem recUniverse : ∀ i, FieldUniverseAdmitted (recA.constructorViews i) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact fun j => Fin.elim0 j
  | ⟨1, _⟩ => exact fun j => Fin.elim0 j
theorem recFieldsB :
    finAllB recA.constructors.length
      (fun i hi => ctorFieldsPermittedB (recA.constructorViews ⟨i, hi⟩) admitFuel) = true := by
  with_unfolding_all rfl
theorem recCensusB : ctorCensusB preSlots 4 7 = true := by with_unfolding_all rfl
noncomputable def recCensus : CtorCensus ePre recA.family.ref 7 :=
  ctorCensusB_sound prefixNd recCensusB
noncomputable def recAdm : IndGroupAdmitted ePre 7 recMem :=
  .recursor recA rfl recCensus recUniverse
    (fun i => ctorFieldsPermitted_of_B _ admitFuel (finAllB_sound recFieldsB i))
    recMinor recIota

noncomputable def family_type_typed :
    HasTyT emptyEnv 1 [] fam.mtype (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort [] .zero) (.sort [.assumption (.sort .zero)] .zero)
theorem recSortHit :
    (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).isSome = true := by
  with_unfolding_all rfl
noncomputable def recSort := (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).get recSortHit

theorem familyTyped (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    FamilyTypedT (familyView E hF) :=
  fun | ⟨0, _⟩ => ⟨HasTyT.sort [] .zero⟩
theorem leafTyped (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    CtorTypedT (leafView E hF) :=
  ⟨(fun | ⟨0, _⟩ => ⟨ownParam_typed E []⟩),
    (fun | ⟨0, _⟩ => ⟨ownParam_mirror E []⟩)⟩
theorem familyAdmTyped : IndGroupTypedT familyAdm := familyTyped eFam rfl
theorem leafAdmTyped : IndGroupTypedT leafAdm :=
  ⟨familyTyped eFam rfl, leafTyped eFam rfl⟩
theorem leaf2AdmTyped : IndGroupTypedT leaf2Adm :=
  ⟨familyTyped eLeaf rfl, leafTyped eLeaf rfl⟩

theorem recAdmTyped : IndGroupTypedT recAdm :=
  ⟨familyTyped ePre rfl,
    (fun | ⟨0, _⟩ => leafTyped ePre rfl | ⟨1, _⟩ => leafTyped ePre rfl),
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

noncomputable def membersT : GroupMembersT eFam emptyEnv slots eAll :=
  .cons _ 4 fam _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    familyAdm PUnit.unit _ family_type_typed (fun h => absurd h (by decide)) familyAdmTyped
    (.cons _ 5 leaf _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      leafAdm PUnit.unit _ (leaf_type_typed rfl) (fun _ => ⟨leaf_type_typed rfl⟩) leafAdmTyped
      (.cons _ 6 leaf _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        leaf2Adm PUnit.unit _ (leaf_type_typed rfl) (fun _ => ⟨leaf_type_typed rfl⟩) leaf2AdmTyped
        (.cons _ 7 recMem [] _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
          recAdm recIdx recSort.1 recSort.2 (fun h => absurd h (by decide))
          recAdmTyped (.nil _))))

noncomputable def envWfT : EnvWfT eAll :=
  .group emptyEnv 4 fam [(5, leaf), (6, leaf)] 7 recMem eAll .empty rfl
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

noncomputable def Witness : Prop :=
  Nonempty (EnvWfT eAll) ∧ recA.policy = .propOnly ∧
  recA.family.parameters = [.sort .zero] ∧
  (∀ i, (recA.constructorViews i).parameters = [ownParam] ∧
    (recA.constructorViews i).fields = []) ∧
  Nonempty (TyConvT ePre 1 [] ownParam (.sort .zero))

theorem component_witness : Witness :=
  ⟨⟨envWfT⟩, rfl, rfl,
    (fun | ⟨0, _⟩ => ⟨rfl, rfl⟩ | ⟨1, _⟩ => ⟨rfl, rfl⟩),
    ⟨ownParam_mirror ePre []⟩⟩

end
end Rcic.Declarative.PropOnlyEmptyMirror

#print axioms Rcic.Declarative.PropOnlyEmptyMirror.envWfT
#print axioms Rcic.Declarative.PropOnlyEmptyMirror.component_witness
