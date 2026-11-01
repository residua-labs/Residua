import rcic.RcicIndGroupAdmitExec
import rcic.RcicTypedFunRecPins
import rcic.RcicF3Cover

/-!
# An admitted DATA constructor indexed by its second field

The actual group is F : Prop → Type, with constructor
mk : (p q : Prop) → F q. Its selected parameter list is empty, its field
list has length two, and its first result index is bvar 0. Therefore it
fails FirstIndexRigid but satisfies the exact first-field separation
condition: the first field would have been bvar 1.

This file constructs the original family/constructor/recursor admission
and typed environment. Bounds and the full original pointwise invariant
are supplied by the separate consumer file. No imported source is claimed.
Source draft for root's native validation. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

namespace Rcic.Declarative.DataSeparatedFixture
open Rcic.Scm.SrcG
noncomputable section

noncomputable abbrev one : Level := .succ .zero
noncomputable abbrev ul : Level := .param 0
noncomputable abbrev propTy : Expr Nat := .sort .zero
noncomputable abbrev fam : CheckedMember :=
  ⟨.inductiveM, 0, .pi propTy (.sort one), none⟩
noncomputable abbrev famApp (p : Expr Nat) : Expr Nat := .app (.const 4 []) p
noncomputable abbrev mk : CheckedMember :=
  ⟨.constructorM, 0, .pi propTy (.pi propTy (famApp (.bvar 0))), none⟩

noncomputable def famApp_typed {E : ResolvedEnv} {n : Nat}
    (hF : E.members 4 = some fam) (Γ : LCtx) (k : Nat)
    (hk : lookupType Γ k = some propTy) :
    HasTyT E n Γ (famApp (.bvar k)) (.sort one) :=
  .app Γ (.const 4 []) (.bvar k) propTy (.sort one)
    (.const Γ 4 [] fam hF rfl rfl) (.bvar Γ k propTy hk)

noncomputable def mk_type_typed {E : ResolvedEnv} (hF : E.members 4 = some fam) :
    HasTyT E 0 [] mk.mtype (.sort (.imax one (.imax one one))) :=
  .pi [] propTy one (.pi propTy (famApp (.bvar 0))) (.imax one one)
    (.sort [] .zero)
    (.pi [.assumption propTy] propTy one (famApp (.bvar 0)) one
      (.sort [.assumption propTy] .zero)
      (famApp_typed hF [.assumption propTy, .assumption propTy] 0 rfl))

noncomputable def familyView (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    PolicyFamilyView E where
  ref := 4
  member := fam
  present := hF
  hasClass := rfl
  parameters := []
  indices := [propTy]
  resultLevel := one
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => one
    bounded := fun _ => rfl
    hasType := by
      intro i
      obtain ⟨k, hk⟩ := i
      have hk0 : k = 0 := by change k < 1 at hk; omega
      subst k
      exact HasTy.sort [] .zero }

noncomputable def mkView (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    PolicyConstructorView E (familyView E hF) mk where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [propTy, propTy]
  resultIndices := [.bvar 0]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => one
    bounded := fun _ => rfl
    hasType := by
      intro i
      obtain ⟨k, hk⟩ := i
      cases k with
      | zero => exact HasTy.sort [] .zero
      | succ k =>
          have hk0 : k = 0 := by change k + 1 < 2 at hk; omega
          subst k
          exact HasTy.sort [.assumption propTy] .zero }
  parameterMirrors := fun i => Fin.elim0 i
  noFamilyInIndices := fun e h => by
    have he := List.mem_singleton.mp h
    subst e
    rfl

noncomputable abbrev motiveTy : Expr Nat :=
  .pi propTy (.pi (famApp (.bvar 0)) (.sort ul))
noncomputable abbrev minorTy : Expr Nat :=
  .pi propTy (.pi propTy
    (.app (.app (.bvar 2) (.bvar 0))
      (.app (.app (.const 5 []) (.bvar 1)) (.bvar 0))))
noncomputable def recTy : Expr Nat :=
  .pi motiveTy (.pi minorTy
    (.pi propTy (.pi (famApp (.bvar 0))
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))
noncomputable def recMem : CheckedMember := ⟨.recursorM, 1, recTy, none⟩
noncomputable def preSlots : List (Nat × CheckedMember) := [(4, fam), (5, mk)]
theorem prefixNd : (preSlots.map (·.1)).Nodup := by decide
noncomputable def slots : List (Nat × CheckedMember) := preSlots ++ [(6, recMem)]
noncomputable abbrev famSlots : List (Nat × CheckedMember) := [(4, fam)]
noncomputable abbrev eFam := extendEnv emptyEnv 4 fam
noncomputable abbrev ePre := extendEnv eFam 5 mk
noncomputable abbrev eAll := extendEnv ePre 6 recMem

theorem family_type : UniformType one := fun _ => Nat.zero_lt_succ 0

noncomputable def familyAdm : IndGroupAdmitted emptyEnv 4 fam :=
  .family rfl (familyView eFam rfl) rfl rfl (Or.inr family_type)

theorem mkUniverse (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    FieldUniverseAdmitted (mkView E hF) :=
  fun _ => Or.inr ⟨family_type, leN_refl one⟩

theorem mkFieldsB (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    ctorFieldsPermittedB (mkView E hF) admitFuel = true := by
  with_unfolding_all rfl

noncomputable def mkAdm : IndGroupAdmitted eFam 5 mk :=
  .constructor (familyView eFam rfl) (mkView eFam rfl) rfl
    ⟨4, rfl, noRecursorForB_sound (by decide)
      (show noRecursorForB famSlots 4 = true from rfl)⟩
    (ctorContiguousB_sound (by decide)
      (show ctorContiguousB famSlots 5 mk = true from rfl))
    (mkUniverse eFam rfl)
    (ctorFieldsPermitted_of_B _ admitFuel (mkFieldsB eFam rfl))

noncomputable def recA : RecursorEliminationAdmitted ePre 6 recMem where
  family := familyView ePre rfl
  constructors := [mk]
  constructorViews := by
    intro i
    obtain ⟨k, hk⟩ := i
    have hk0 : k = 0 := by change k < 1 at hk; omega
    subst k
    exact mkView ePre rfl
  constructorsPresent := by
    intro i
    obtain ⟨k, hk⟩ := i
    have hk0 : k = 0 := by change k < 1 at hk; omega
    subst k
    rfl
  recursorRef := rfl
  minorTypes := [minorTy]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType family_type
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

noncomputable def recShapes (_i : Fin recA.constructors.length) : List FieldShape :=
  [.nonrecursive, .nonrecursive]

theorem recAnalyzed : ∀ i, shapesWitness admitFuel recA.constructorViews recShapes i := by
  intro ⟨i, hi⟩
  match i, hi with
  | 0, _ => rfl

theorem recMinorB : minorsMatchB recA admitFuel recShapes = true := by
  with_unfolding_all rfl
noncomputable def recMinor : MinorPremisesMatch recA := minorsMatch_of recAnalyzed recMinorB
theorem recIotaHit :
    (iotaClause? recA admitFuel recShapes recAnalyzed rfl).isSome = true := by
  with_unfolding_all rfl
noncomputable def recIota : IotaDescriptorClause ePre recA :=
  (iotaClause? recA admitFuel recShapes recAnalyzed rfl).get recIotaHit

theorem recUniverse : ∀ i, FieldUniverseAdmitted (recA.constructorViews i) := by
  intro ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact mkUniverse ePre rfl
theorem recCensusB : ctorCensusB preSlots 4 6 = true := by
  with_unfolding_all rfl
noncomputable def recCensus : CtorCensus ePre recA.family.ref 6 :=
  ctorCensusB_sound prefixNd recCensusB
noncomputable def recAdm : IndGroupAdmitted ePre 6 recMem :=
  .recursor recA rfl recCensus recUniverse
    (fun | ⟨0, _⟩ => ctorFieldsPermitted_of_B _ admitFuel (mkFieldsB ePre rfl))
    recMinor recIota

noncomputable def family_type_typed :
    HasTyT emptyEnv 0 [] fam.mtype (.sort (.imax one (.succ one))) :=
  .pi [] propTy one (.sort one) (.succ one)
    (.sort [] .zero) (.sort [.assumption propTy] one)
theorem recSortHit :
    (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).isSome = true := by
  with_unfolding_all rfl
noncomputable def recSort := (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).get recSortHit

theorem familyTyped (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    FamilyTypedT (familyView E hF) :=
  fun | ⟨0, _⟩ => ⟨HasTyT.sort [] .zero⟩
theorem mkTyped (E : ResolvedEnv) (hF : E.members 4 = some fam) :
    CtorTypedT (mkView E hF) :=
  ⟨(fun
      | ⟨0, _⟩ => ⟨HasTyT.sort [] .zero⟩
      | ⟨1, _⟩ => ⟨HasTyT.sort [.assumption propTy] .zero⟩),
    (fun i => Fin.elim0 i)⟩
theorem familyAdmTyped : IndGroupTypedT familyAdm := familyTyped eFam rfl
theorem mkAdmTyped : IndGroupTypedT mkAdm :=
  ⟨familyTyped eFam rfl, mkTyped eFam rfl⟩
theorem recAdmTyped : IndGroupTypedT recAdm :=
  ⟨familyTyped ePre rfl, (fun | ⟨0, _⟩ => mkTyped ePre rfl),
    (fun i => by
      match i with
      | ⟨0, _⟩ =>
          exact iotaEquationTypedT_of_check
            (fun Γ e T => tyAtC _ _ admitFuel Γ e T) (by with_unfolding_all rfl))⟩
noncomputable def recIdx : RecursorGroupIdxAdmittedT recA recIota :=
  .ofCheck recA recIota (by with_unfolding_all rfl)

noncomputable def membersT : GroupMembersT eFam emptyEnv slots eAll :=
  .cons _ 4 fam _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    familyAdm PUnit.unit _ family_type_typed (fun h => absurd h (by decide))
    familyAdmTyped
    (.cons _ 5 mk _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      mkAdm PUnit.unit _ (mk_type_typed rfl) (fun _ => ⟨mk_type_typed rfl⟩) mkAdmTyped
      (.cons _ 6 recMem [] _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        recAdm recIdx recSort.1 recSort.2 (fun h => absurd h (by decide))
        recAdmTyped (.nil _)))

theorem ctorClasses : ∀ c ∈ [(5, mk)], c.2.mclass = .constructorM := by
  intro c hc
  cases List.mem_singleton.mp hc
  rfl

noncomputable def envWfT : EnvWfT eAll :=
  .group emptyEnv 4 fam [(5, mk)] 6 recMem eAll .empty rfl ctorClasses rfl membersT

noncomputable def pNode : Rcic.F3.PSet.RecNode emptyEnv eAll 4 6 recMem where
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

end
end Rcic.Declarative.DataSeparatedFixture

#print axioms Rcic.Declarative.DataSeparatedFixture.envWfT
#print axioms Rcic.Declarative.DataSeparatedFixture.recAdmTyped
