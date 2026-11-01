import rcic.RcicUntypedConvCollapse
import rcic.RcicIndGroupAdmitExec
import rcic.RcicTypedFunRecPins
import rcic.RcicF3Cover

/-!
# A typed PendA W fixture with a beta-hidden recursive field

The stored node field is a beta redex whose normal form is `A → W A`.
Admission retains the normalized depth 1. Both iota equations are checked
in HasTyT by tyAtC, and the complete group inhabits EnvWfT and PendA.
The convenience synCheck group builder is not used for the recursor:
it compares written types, whereas this fixture needs typed conversion.

The legacy descriptor still asks for HasTy. The local legacy adapter
copies the typed derivation and uses the already landed untyped-conversion
collapse only for that legacy obligation; both typed equations are paid
independently. This does not use untyped conversion to establish EnvWfT.
The manual FieldUniverseAdmitted inequality is the same semantic imax
inequality used by PendAW; no executable leaf is asserted to pass falsely.
No group soundness or universal StepAG is claimed. `closure_claim = 0`.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option autoImplicit false

noncomputable section
namespace Rcic.Declarative.PendAWHidden
noncomputable def legacy {E : ResolvedEnv} {n : Nat} (hn : 0 < n) {Γ : LCtx} {e A : Expr Nat}
 (h : HasTyT E n Γ e A) : HasTy E n Γ e A := by
  induction h using HasTyT.rec (motive_2 := fun _ _ _ _ _ => PUnit)
  case sort Γ l => exact .sort Γ l
  case bvar Γ i A h => exact .bvar Γ i A h
  case const Γ r ls m hres hlen hwf =>
      exact .const Γ r ls m hres hlen (fun _ _ => ⟨0, Or.inr hn⟩)
  case pi Γ A u B v hA hB ihA ihB => exact .pi Γ A u B v ihA ihB
  case lam Γ A u body B hA hb ihA ihb => exact .lam Γ A u body B ihA ihb
  case app Γ f a A B hf ha ihf iha => exact .app Γ f a A B ihf iha
  case letE Γ A u v B body hA hv hb ihA ihv ihb => exact .letE Γ A u v B ihA ihv ihb
  case lit Γ t T h ih => exact .lit Γ t T ih
  case conv Γ e A B u h hc ih ihc => exact UntypedConvCollapse.retypeAny ih B
  all_goals intros; exact PUnit.unit


abbrev fam : CheckedMember := ⟨.inductiveM, 0,
  .pi (.sort (.succ .zero)) (.sort (.succ .zero)), none⟩
abbrev leaf : CheckedMember := ⟨.constructorM, 0,
  .pi (.sort (.succ .zero)) (.app (.const 4 []) (.bvar 0)), none⟩
abbrev rawField : Expr Nat := .pi (.bvar 0) (.app (.const 4 []) (.bvar 1))
abbrev field : Expr Nat := .app (.lam (.sort (.succ .zero)) (lift 0 1 rawField)) (.sort .zero)
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
def typedIotaCheck (i : Fin recA.constructors.length) : Bool :=
 match equationDoms recA i, iotaSchemaAt recA i admitFuel (recShapes i) with
 | some doms, some rhs => (tyAtC eAll 1 128 (assumptionCtx doms) rhs (iotaEquationType recA i)).isSome
 | _, _ => false
kernel_rfl_theorem typedIotaAll :
  finAllB recA.constructors.length (fun i hi => typedIotaCheck ⟨i, hi⟩) = true
noncomputable def legacyIota (i : Fin recA.constructors.length) :
    IotaEquationTyped recA i admitFuel (recShapes i) := by
  have h := finAllB_sound typedIotaAll i
  unfold typedIotaCheck at h
  unfold IotaEquationTyped
  revert h
  rcases equationDoms recA i with _ | doms <;>
    rcases iotaSchemaAt recA i admitFuel (recShapes i) with _ | rhs
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; exact legacy (by decide) ((tyAtC eAll 1 128 _ _ _).get h)

def recIota : IotaDescriptorClause ePre recA :=
  ⟨rfl, recShapes, (fun _ => admitFuel), recAnalyzed, legacyIota⟩

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
kernel_rfl_theorem recStructB : memberStructB ePre recMem = true
kernel_rfl_theorem recFamTypedB : famTypedB ePre admitFuel recA.family = true
kernel_rfl_theorem recCtorsTypedB : ctorTypedAllB admitFuel recA = true
kernel_rfl_theorem recIdxB : recIdxAdmittedTB recA recIota = true

def recTyped : IndGroupTypedT recAdm :=
  ⟨famTypedT_of _ recFamTypedB, ctorTypedAll_of recCtorsTypedB,
    fun i => iotaEquationTypedT_of_check (tyAtC eAll 1 128)
      (finAllB_sound typedIotaAll i)⟩

def recLink : GroupMembersT eFam ePre [(7, recMem)] eAll := by
  obtain ⟨hb, hcl, har, hlvl, hcan, hcoh⟩ := memberStructB_of recStructB
  exact .cons ePre 7 recMem [] eAll rfl hb hcl har hlvl hcan hcoh
    recAdm (idxT_of _ recIdxB) recSort.1 recSort.2
    (fun h => by cases h) recTyped (.nil eAll)

-- This copies the paid link used by groupMembersT_of_chain and permits
-- a directly derived typed-recursion link as the tail.
def checkedLink {S E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {rest : List (Nat × CheckedMember)} (hadm : IndGroupAdmitted E r m)
    (hsort : (sortTyAtC E m.arity admitFuel [] m.mtype).isSome = true)
    (hleaf : memberAcceptB S E admitFuel hadm
      ((sortTyAtC E m.arity admitFuel [] m.mtype).get hsort).1 = true)
    (hrest : GroupMembersT S (extendEnv E r m) rest E') :
    GroupMembersT S E ((r, m) :: rest) E' := by
  have hl := hleaf
  simp only [memberAcceptB, Bool.and_eq_true] at hl
  obtain ⟨hb, hcl, har, hlvl, hcan, hcoh⟩ := memberStructB_of hl.1.1
  have hc := memberContentB_of hadm hl.2
  exact .cons E r m rest E' hadm.fresh hb hcl har hlvl hcan hcoh hadm hc.1
    ((sortTyAtC E m.arity admitFuel [] m.mtype).get hsort).1
    ((sortTyAtC E m.arity admitFuel [] m.mtype).get hsort).2
    (memberScopeB_of hl.1.2) hc.2 hrest

def membersT : GroupMembersT eFam natEnvU slots eAll :=
  checkedLink familyAdm famSortHit famAcceptB
    (checkedLink leafAdm leafSortHit leafAcceptB
      (checkedLink nodeAdm nodeSortHit nodeAcceptB recLink))
def envWfT : EnvWfT eAll :=
  .group natEnvU 4 fam [(5, leaf), (6, node)] 7 recMem eAll
    natEnvUWfT rfl (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl)
    rfl membersT

def recPaid : PProd (IdxAdmittedT recAdm) (IndGroupTypedT recAdm) :=
  ⟨idxT_of _ recIdxB, recTyped⟩

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

end Rcic.Declarative.PendAWHidden
