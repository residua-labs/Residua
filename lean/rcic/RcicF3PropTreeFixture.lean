import rcic.RcicIndGroupAdmitExec
import rcic.RcicTypedFunRecPins
import rcic.RcicF3Cover

/-!
# An admitted inhabited higher-order Prop-only group

Over the empty environment, references 4--7 declare `F : Prop`,
`leaf : F`, `node : (Prop → F) → F`, and the rebuilt recursor.
The two constructors select the literal `propOnly` policy. The second
constructor's field is analyzed as `recursive 1`, and its branch domain
is inhabited by the actual object-language proposition `F`.

Every member, stored type, minor and typed iota descriptor is supplied
by the existing executable group admission chain. The final component
also retains the typed leaf, the typed constant-leaf function, its
application at `F`, and the typed node using that function. It does not
assert a semantic group invariant or a universal recursor producer.
closure_claim = 0.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option autoImplicit false

namespace Rcic.Declarative.PropTree
open Rcic.Scm.SrcG

-- Explicit noncomputable declarations retain kernel terms without compiler helpers.
noncomputable section

noncomputable abbrev fam : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
noncomputable abbrev leaf : CheckedMember := ⟨.constructorM, 0, .const 4 [], none⟩
noncomputable abbrev field : Expr Nat := .pi (.sort .zero) (.const 4 [])
noncomputable abbrev node : CheckedMember := ⟨.constructorM, 0, .pi field (.const 4 []), none⟩

noncomputable def preSlots : List (Nat × CheckedMember) := [(4, fam), (5, leaf), (6, node)]
theorem prefixNd : (preSlots.map (·.1)).Nodup := by decide

noncomputable def recTy : Expr Nat :=
  (rebuiltType? admitFuel preSlots prefixNd 4 fam [(5, leaf), (6, node)] 0).getD
    (.sort .zero)
noncomputable def recMem : CheckedMember := ⟨.recursorM, 0, recTy, none⟩
noncomputable def slots : List (Nat × CheckedMember) := preSlots ++ [(7, recMem)]
theorem slotsNd : (slots.map (·.1)).Nodup := by decide

noncomputable abbrev famSlots : List (Nat × CheckedMember) := [(4, fam)]
noncomputable abbrev leafSlots : List (Nat × CheckedMember) := [(4, fam), (5, leaf)]
noncomputable abbrev eFam := extendEnv emptyEnv 4 fam
noncomputable abbrev eLeaf := extendEnv eFam 5 leaf
noncomputable abbrev ePre := extendEnv eLeaf 6 node
noncomputable abbrev eAll := extendEnv ePre 7 recMem

kernel_rfl_theorem familyHit : (familyAdmitted? admitFuel emptyEnv 4 fam 0).isSome = true
noncomputable def familyAdm : IndGroupAdmitted emptyEnv 4 fam :=
  (familyAdmitted? admitFuel emptyEnv 4 fam 0).get familyHit

kernel_rfl_theorem leafHit :
  (ctorAdmitted? admitFuel eFam famSlots rfl (by decide) 5 leaf 0 4 fam).isSome = true
noncomputable def leafAdm : IndGroupAdmitted eFam 5 leaf :=
  (ctorAdmitted? admitFuel eFam famSlots rfl (by decide) 5 leaf 0 4 fam).get leafHit

kernel_rfl_theorem nodeHit :
  (ctorAdmitted? admitFuel eLeaf leafSlots rfl (by decide) 6 node 0 4 fam).isSome = true
noncomputable def nodeAdm : IndGroupAdmitted eLeaf 6 node :=
  (ctorAdmitted? admitFuel eLeaf leafSlots rfl (by decide) 6 node 0 4 fam).get nodeHit

kernel_rfl_theorem recHit :
  (buildRecAdmitted? admitFuel ePre preSlots prefixNd 4 fam
    [(5, leaf), (6, node)] 7 recMem 0).isSome = true
noncomputable def recA : RecursorEliminationAdmitted ePre 7 recMem :=
  (buildRecAdmitted? admitFuel ePre preSlots prefixNd 4 fam
    [(5, leaf), (6, node)] 7 recMem 0).get recHit

kernel_rfl_theorem family_parameters : recA.family.parameters = []
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

kernel_rfl_theorem famSortHit :
  (sortTyAtC emptyEnv fam.arity admitFuel [] fam.mtype).isSome = true
kernel_rfl_theorem leafSortHit :
  (sortTyAtC eFam leaf.arity admitFuel [] leaf.mtype).isSome = true
kernel_rfl_theorem nodeSortHit :
  (sortTyAtC eLeaf node.arity admitFuel [] node.mtype).isSome = true
kernel_rfl_theorem recSortHit :
  (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).isSome = true

noncomputable def famSort := (sortTyAtC emptyEnv fam.arity admitFuel [] fam.mtype).get famSortHit
noncomputable def leafSort := (sortTyAtC eFam leaf.arity admitFuel [] leaf.mtype).get leafSortHit
noncomputable def nodeSort := (sortTyAtC eLeaf node.arity admitFuel [] node.mtype).get nodeSortHit
noncomputable def recSort := (sortTyAtC ePre recMem.arity admitFuel [] recMem.mtype).get recSortHit

kernel_rfl_theorem famAcceptB : memberAcceptB eFam emptyEnv admitFuel familyAdm famSort.1 = true
kernel_rfl_theorem leafAcceptB : memberAcceptB eFam eFam admitFuel leafAdm leafSort.1 = true
kernel_rfl_theorem nodeAcceptB : memberAcceptB eFam eLeaf admitFuel nodeAdm nodeSort.1 = true
kernel_rfl_theorem recAcceptB : memberAcceptB eFam ePre admitFuel recAdm recSort.1 = true

noncomputable def chain : GroupAcceptChain eFam admitFuel emptyEnv slots eAll :=
  .cons emptyEnv 4 fam _ eAll familyAdm famSortHit famAcceptB
    (.cons eFam 5 leaf _ eAll leafAdm leafSortHit leafAcceptB
      (.cons eLeaf 6 node _ eAll nodeAdm nodeSortHit nodeAcceptB
        (.cons ePre 7 recMem [] eAll recAdm recSortHit recAcceptB (.nil eAll))))

noncomputable def membersT : GroupMembersT eFam emptyEnv slots eAll := groupMembersT_of_chain chain
noncomputable def envWfT : EnvWfT eAll :=
  EG010T_group_accepted EnvWfT.empty admitFuel (by decide) chain

kernel_rfl_theorem recContentB : memberContentB ePre admitFuel recAdm = true
noncomputable def recPaid := memberContentB_of recAdm recContentB

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
  famTyped := recPaid.2.1
  ctorsTyped := recPaid.2.2.1
  u := recSort.1
  hT := recSort.2

kernel_rfl_theorem nodeShape :
  (pNode.h14.shapesAt ⟨1, by decide⟩)[0]? = some (.recursive 1)

theorem pendA : Rcic.F3.PSet.PendA pNode :=
  ⟨⟨1, by decide⟩, 0, 0, nodeShape⟩

/-- The recursive telescope's domain contains the actual proposition F. -/
noncomputable def branch_arg_typed : HasTyT eAll 0 [] (.const 4 []) (.sort .zero) :=
  .const [] 4 [] fam rfl rfl rfl

noncomputable def leaf_typed : HasTyT eAll 0 [] (.const 5 []) (.const 4 []) :=
  .const [] 5 [] leaf rfl rfl rfl

noncomputable abbrev branch : Expr Nat := .lam (.sort .zero) (.const 5 [])
noncomputable def branch_typed : HasTyT eAll 0 [] branch field :=
  .lam [] (.sort .zero) (.succ .zero) (.const 5 []) (.const 4 [])
    (.sort [] .zero) (.const [.assumption (.sort .zero)] 5 [] leaf rfl rfl rfl)

noncomputable abbrev nodeTerm : Expr Nat := .app (.const 6 []) branch
noncomputable def node_typed : HasTyT eAll 0 [] nodeTerm (.const 4 []) :=
  .app [] (.const 6 []) branch field (.const 4 [])
    (.const [] 6 [] node rfl rfl rfl) branch_typed

noncomputable def branch_beta : ConvT eAll 0 [] (.app branch (.const 4 [])) (.const 5 []) (.const 4 []) :=
  .beta [] (.sort .zero) (.const 5 []) (.const 4 []) (.const 4 []) (.succ .zero)
    (.sort [] .zero) (.const [.assumption (.sort .zero)] 5 [] leaf rfl rfl rfl)
    branch_arg_typed

/-- Literal admission and inhabited higher-order object-language data.
No semantic GInv or recursor-soundness hypothesis occurs in this component. -/
noncomputable def Witness : Prop :=
  Nonempty (EnvWfT eAll) ∧
  recA.family.parameters = [] ∧ recA.family.indices = [] ∧
  recA.policy = .propOnly ∧ Rcic.F3.PSet.PendA pNode ∧
  Nonempty (HasTyT eAll 0 [] (.const 4 []) (.sort .zero)) ∧
  Nonempty (HasTyT eAll 0 [] (.const 5 []) (.const 4 [])) ∧
  Nonempty (HasTyT eAll 0 [] branch field) ∧
  Nonempty (HasTyT eAll 0 [] nodeTerm (.const 4 [])) ∧
  Nonempty (ConvT eAll 0 [] (.app branch (.const 4 [])) (.const 5 []) (.const 4 []))

theorem component_witness : Witness :=
  ⟨⟨envWfT⟩, family_parameters, family_indices, rec_policy, pendA,
    ⟨branch_arg_typed⟩, ⟨leaf_typed⟩, ⟨branch_typed⟩, ⟨node_typed⟩, ⟨branch_beta⟩⟩

theorem component_nonrefutable : ¬ (Witness → False) :=
  fun h => h component_witness

end

end Rcic.Declarative.PropTree
