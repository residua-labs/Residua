import rcic.RcicIndGroupAdmitExec
import rcic.RcicTypedFunRecPins
import rcic.RcicF3Cover

/-!
# A typed, inhabited parameterized PendA W group

`closure_claim = 0`.

Over the landed typed Nat environment, references 4–7 declare
`W (A : Sort 1) : Sort 1`, `leaf : W A`, `node : (A → W A) → W A`,
and the rebuilt recursor. All stored types, constructor scopes, positivity,
census, minor premises and typed iota equations are paid by the existing
admission rules. `pNode` is a named `PendA` node and `leafNat_typed` is a
closed object-language inhabitant at the actual Nat parameter.

The executable `fieldUnivB` is conservative: its syntactic `leNB` does not
recognize `imax 1 1 ≤ 1`. Only that Bool leaf is bypassed, by the landed
semantic universe inequality `leN_imax_succ_zero_self` in `nodeUniverse` /
`recUniverse`; all other admission leaves still run. Kernel-only reflexivity
pins use the landed `kernel_rfl_theorem` command, which checks an `Eq.refl`
proof in the kernel without elaborator reduction. No native proof oracle.

This is typed non-vacuity infrastructure. It proves neither `StepAG_PendA`
nor a bridge from the guarded W interpretation to the fold's `famLim`.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option autoImplicit false

namespace Rcic.Declarative.PendAW

abbrev fam : CheckedMember := ⟨.inductiveM, 0,
  .pi (.sort (.succ .zero)) (.sort (.succ .zero)), none⟩
abbrev leaf : CheckedMember := ⟨.constructorM, 0,
  .pi (.sort (.succ .zero)) (.app (.const 4 []) (.bvar 0)), none⟩
abbrev field : Expr Nat := .pi (.bvar 0) (.app (.const 4 []) (.bvar 1))
abbrev node : CheckedMember := ⟨.constructorM, 0,
  .pi (.sort (.succ .zero)) (.pi field (.app (.const 4 []) (.bvar 1))), none⟩
def preSlots : List (Nat × CheckedMember) := [(4, fam), (5, leaf), (6, node)]
theorem prefixNd : (preSlots.map (·.1)).Nodup := by decide

def recTy : Expr Nat := (rebuiltType? admitFuel preSlots prefixNd 4 fam
  [(5, leaf), (6, node)] 1).getD (.sort .zero)
def recMem : CheckedMember := ⟨.recursorM, 1, recTy, none⟩
def slots : List (Nat × CheckedMember) := preSlots ++ [(7, recMem)]
theorem slotsNd : (slots.map (·.1)).Nodup := by decide

open Rcic.Scm.SrcG
abbrev baseSlots : List (Nat × CheckedMember) :=
  [(0, natFamMember), (1, natZeroMember), (2, natSuccMember), (3, natRecMemberU)]
abbrev famSlots := baseSlots ++ [(4, fam)]
abbrev leafSlots := baseSlots ++ [(4, fam), (5, leaf)]
abbrev preTable := baseSlots ++ preSlots
theorem preTableNd : (preTable.map (·.1)).Nodup := by decide
abbrev eFam := extendEnv natEnvU 4 fam
abbrev eLeaf := extendEnv eFam 5 leaf
abbrev ePre := extendEnv eLeaf 6 node
abbrev eAll := extendEnv ePre 7 recMem

kernel_rfl_theorem familyHit : (familyAdmitted? admitFuel natEnvU 4 fam 1).isSome = true
def familyAdm : IndGroupAdmitted natEnvU 4 fam :=
  (familyAdmitted? admitFuel natEnvU 4 fam 1).get familyHit
kernel_rfl_theorem leafHit :
  (ctorAdmitted? admitFuel eFam famSlots rfl (by decide) 5 leaf 1 4 fam).isSome = true
def leafAdm : IndGroupAdmitted eFam 5 leaf :=
  (ctorAdmitted? admitFuel eFam famSlots rfl (by decide) 5 leaf 1 4 fam).get leafHit

kernel_rfl_theorem familyViewHit : (familyViewAt eLeaf admitFuel 1 4 fam).isSome = true
def familyView : PolicyFamilyView eLeaf :=
  (familyViewAt eLeaf admitFuel 1 4 fam).get familyViewHit
kernel_rfl_theorem nodeViewHit : (buildCtorView? admitFuel familyView node).isSome = true
def nodeView : PolicyConstructorView eLeaf familyView node :=
  (buildCtorView? admitFuel familyView node).get nodeViewHit

theorem nodeUniverse : FieldUniverseAdmitted nodeView := by
  intro j
  rcases j with ⟨j, hj⟩
  change j < 1 at hj
  have hz : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
  subst hz
  exact Or.inr ⟨uniformType_succ_zero, leN_imax_succ_zero_self⟩

kernel_rfl_theorem nodeFieldsB : ctorFieldsPermittedB nodeView admitFuel = true
kernel_rfl_theorem nodeBeforeB : noRecursorForB leafSlots 4 = true
kernel_rfl_theorem nodeContigB : ctorContiguousB leafSlots 6 node = true

def nodeAdm : IndGroupAdmitted eLeaf 6 node :=
  .constructor familyView nodeView rfl
    ⟨4, rfl, noRecursorForB_sound (by decide) nodeBeforeB⟩
    (ctorContiguousB_sound (by decide) nodeContigB) nodeUniverse
    (ctorFieldsPermitted_of_B nodeView admitFuel nodeFieldsB)

kernel_rfl_theorem recHit :
  (buildRecAdmitted? admitFuel ePre preSlots prefixNd 4 fam [(5,leaf),(6,node)] 7 recMem 1).isSome = true
def recA : RecursorEliminationAdmitted ePre 7 recMem :=
  (buildRecAdmitted? admitFuel ePre preSlots prefixNd 4 fam [(5,leaf),(6,node)] 7 recMem 1).get recHit

def recShapes (i : Fin recA.constructors.length) : List FieldShape :=
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
def recMinor : MinorPremisesMatch recA := minorsMatch_of recAnalyzed recMinorB
kernel_rfl_theorem recIotaHit : (iotaClause? recA admitFuel recShapes recAnalyzed rfl).isSome = true
def recIota : IotaDescriptorClause ePre recA :=
  (iotaClause? recA admitFuel recShapes recAnalyzed rfl).get recIotaHit

theorem recUniverse : ∀ i, FieldUniverseAdmitted (recA.constructorViews i) := by
  intro ⟨i, hi⟩
  cases i with
  | zero => exact fun j => Fin.elim0 j
  | succ i =>
    cases i with
    | zero =>
      intro ⟨j, hj⟩
      change j < 1 at hj
      have hz : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj)
      subst hz
      exact Or.inr ⟨uniformType_succ_zero, leN_imax_succ_zero_self⟩
    | succ i =>
      have h : i + 1 + 1 < 2 := hi
      exact (by omega : False).elim

kernel_rfl_theorem recFieldsB :
  finAllB recA.constructors.length (fun i hi => ctorFieldsPermittedB (recA.constructorViews ⟨i, hi⟩) admitFuel) = true
kernel_rfl_theorem recCensusB : ctorCensusB preTable 4 7 = true

def recCensus : CtorCensus ePre recA.family.ref 7 :=
  ctorCensusB_sound preTableNd recCensusB

def recAdm : IndGroupAdmitted ePre 7 recMem :=
  .recursor recA rfl recCensus recUniverse
    (fun i => ctorFieldsPermitted_of_B _ admitFuel (finAllB_sound recFieldsB i))
    recMinor recIota

kernel_rfl_theorem famSortHit : (sortTyAtC natEnvU fam.arity admitFuel [] fam.mtype).isSome = true
kernel_rfl_theorem leafSortHit : (sortTyAtC eFam leaf.arity admitFuel [] leaf.mtype).isSome = true
kernel_rfl_theorem nodeSortHit : (sortTyAtC eLeaf node.arity admitFuel [] node.mtype).isSome = true
kernel_rfl_theorem recSortHit : (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).isSome = true

def famSort := (sortTyAtC natEnvU fam.arity admitFuel [] fam.mtype).get famSortHit
def leafSort := (sortTyAtC eFam leaf.arity admitFuel [] leaf.mtype).get leafSortHit
def nodeSort := (sortTyAtC eLeaf node.arity admitFuel [] node.mtype).get nodeSortHit
def recSort := (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).get recSortHit

kernel_rfl_theorem famAcceptB : memberAcceptB eFam natEnvU admitFuel familyAdm famSort.1 = true
kernel_rfl_theorem leafAcceptB : memberAcceptB eFam eFam admitFuel leafAdm leafSort.1 = true
kernel_rfl_theorem nodeAcceptB : memberAcceptB eFam eLeaf admitFuel nodeAdm nodeSort.1 = true
kernel_rfl_theorem recAcceptB : memberAcceptB eFam ePre admitFuel recAdm recSort.1 = true

def chain : GroupAcceptChain eFam admitFuel natEnvU slots eAll :=
  .cons natEnvU 4 fam _ eAll familyAdm famSortHit famAcceptB
    (.cons eFam 5 leaf _ eAll leafAdm leafSortHit leafAcceptB
      (.cons eLeaf 6 node _ eAll nodeAdm nodeSortHit nodeAcceptB
        (.cons ePre 7 recMem [] eAll recAdm recSortHit recAcceptB (.nil eAll))))

def membersT : GroupMembersT eFam natEnvU slots eAll := groupMembersT_of_chain chain

def envWfT : EnvWfT eAll :=
  EG010T_group_accepted natEnvUWfT admitFuel (by decide) chain

kernel_rfl_theorem recContentB : memberContentB ePre admitFuel recAdm = true
def recPaid := memberContentB_of recAdm recContentB

theorem basePreserved : ∀ r m, natEnvU.members r = some m → ePre.members r = some m := by
  intro r m h
  have h4 : r ≠ 4 := by intro e; subst e; cases h
  have h5 : r ≠ 5 := by intro e; subst e; cases h
  have h6 : r ≠ 6 := by intro e; subst e; cases h
  change (extendEnv (extendEnv (extendEnv natEnvU 4 fam) 5 leaf) 6 node).members r = some m
  rw [extendEnv_members_ne h6, extendEnv_members_ne h5, extendEnv_members_ne h4]
  exact h

def pNode : Rcic.F3.PSet.RecNode natEnvU eAll 4 7 recMem where
  E0 := ePre
  a := recA
  h14 := recIota
  fam := rfl
  fresh := rfl
  sub := fun _ _ h => h
  base := basePreserved
  h04 := recCensus
  h07 := recUniverse
  h12 := recMinor
  famTyped := recPaid.2.1
  ctorsTyped := recPaid.2.2.1
  u := recSort.1
  hT := recSort.2

kernel_rfl_theorem nodeShape :
  (pNode.h14.shapesAt ⟨1, by decide⟩)[0]? = some (.recursive 1)

theorem pendA : Rcic.F3.PSet.PendA pNode := by
  exact ⟨⟨1, by decide⟩, 0, 0, nodeShape⟩

/-- A closed object-level leaf at the actual landed Nat parameter. -/
def leafNat : Expr Nat := .app (.const 5 []) (.const 0 [])
def wNatTy : Expr Nat := .app (.const 4 []) (.const 0 [])

def leafNat_typed : HasTyT eAll 0 [] leafNat wNatTy := by
  exact HasTyT.app [] (.const 5 []) (.const 0 []) (.sort (.succ .zero))
    (.app (.const 4 []) (.bvar 0))
    (HasTyT.const [] 5 [] leaf rfl rfl rfl)
    (HasTyT.const [] 0 [] natFamMember rfl rfl rfl)

end Rcic.Declarative.PendAW
