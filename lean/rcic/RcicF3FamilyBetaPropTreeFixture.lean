import rcic.RcicIndGroupAdmitExec
import rcic.RcicTypedFunRecPins
import rcic.RcicF3Cover

/-!
# An admitted PropOnly tree with an actual head-beta recursive field

The four-member group has F : Prop, a leaf, and a node whose stored field
is `(fun _ : Prop => Prop → F) F`. The field cache reads the Pi telescope
Prop → F only after contracting the head beta redex. The original member
acceptance chain, typed recursor and iota descriptor are rebuilt here.

The typed constant-leaf branch is converted to that exact stored hidden
field before it is supplied to the node. This file supplies syntax and
actual admission, not a semantic invariant. The following bounds and
coverage module use this same group. Source-only draft; no local native
validation is claimed. closure_claim = 0.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option autoImplicit false

namespace Rcic.Declarative.FamilyBetaPropTree
open Rcic.Scm.SrcG

-- Explicit noncomputable declarations retain kernel terms without compiler helpers.
noncomputable section

noncomputable abbrev fam : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
noncomputable abbrev leaf : CheckedMember := ⟨.constructorM, 0, .const 4 [], none⟩
noncomputable abbrev normalField : Expr Nat := .pi (.sort .zero) (.const 4 [])
noncomputable abbrev field : Expr Nat :=
  .app (.lam (.sort .zero) normalField) (.const 4 [])
noncomputable abbrev node : CheckedMember := ⟨.constructorM, 0, .pi field (.const 4 []), none⟩

/-- The bounded field derivations are constructed explicitly, independently
of the executable admission checks. -/
noncomputable def normalField_typed {E : ResolvedEnv}
    (hF : E.members 4 = some fam) (Γ : LCtx) :
    HasTyT E 0 Γ normalField (.sort (.imax (.succ .zero) .zero)) :=
  .pi Γ (.sort .zero) (.succ .zero) (.const 4 []) .zero
    (.sort Γ .zero) (.const (.assumption (.sort .zero) :: Γ) 4 [] fam hF rfl rfl)

noncomputable def field_typed {E : ResolvedEnv}
    (hF : E.members 4 = some fam) (Γ : LCtx) :
    HasTyT E 0 Γ field (.sort (.imax (.succ .zero) .zero)) :=
  .app Γ (.lam (.sort .zero) normalField) (.const 4 []) (.sort .zero)
    (.sort (.imax (.succ .zero) .zero))
    (.lam Γ (.sort .zero) (.succ .zero) normalField
      (.sort (.imax (.succ .zero) .zero)) (.sort Γ .zero)
      (normalField_typed hF (.assumption (.sort .zero) :: Γ)))
    (.const Γ 4 [] fam hF rfl rfl)

noncomputable def field_beta {E : ResolvedEnv}
    (hF : E.members 4 = some fam) (Γ : LCtx) :
    ConvT E 0 Γ field normalField (.sort (.imax (.succ .zero) .zero)) :=
  .beta Γ (.sort .zero) normalField (.const 4 [])
    (.sort (.imax (.succ .zero) .zero)) (.succ .zero)
    (.sort Γ .zero) (normalField_typed hF (.assumption (.sort .zero) :: Γ))
    (.const Γ 4 [] fam hF rfl rfl)

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

/- The convenience `iotaClause?` uses the conversion-free legacy
`exprCheck`, which cannot apply a variable at the stored head-beta field
type. Supply the actual legacy equation derivation, including that beta
conversion. The typed equation is still required by the group below. -/
noncomputable abbrev motiveTy : Expr Nat := .pi (.const 4 []) (.sort .zero)
noncomputable abbrev leafMinor : Expr Nat := .app (.bvar 0) (.const 5 [])
noncomputable abbrev nodeIH : Expr Nat :=
  .pi (.sort .zero) (.app (.bvar 3) (.app (.bvar 1) (.bvar 0)))
noncomputable abbrev nodeMinor : Expr Nat :=
  .pi field (.pi nodeIH (.app (.bvar 3) (.app (.const 6 []) (.bvar 1))))
noncomputable abbrev recTypeView : Expr Nat :=
  .pi motiveTy (.pi leafMinor (.pi nodeMinor
    (.pi (.const 4 []) (.app (.bvar 3) (.bvar 0)))))

kernel_rfl_theorem recType_eq : recMem.mtype = recTypeView

noncomputable abbrev leafIotaCtx : LCtx :=
  [.assumption nodeMinor, .assumption leafMinor, .assumption motiveTy]
noncomputable abbrev nodeIotaCtx : LCtx :=
  .assumption field :: leafIotaCtx
noncomputable abbrev nodeCall : Expr Nat :=
  .lam (.sort .zero)
    (.app (.app (.app (.app (.const 7 []) (.bvar 4)) (.bvar 3)) (.bvar 2))
      (.app (.bvar 1) (.bvar 0)))
noncomputable abbrev nodeSchema : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) nodeCall
noncomputable abbrev nodeEqType : Expr Nat :=
  .app (.bvar 3) (.app (.const 6 []) (.bvar 0))

kernel_rfl_theorem leafEquation_doms :
  equationDoms recA ⟨0, by decide⟩ = some [motiveTy, leafMinor, nodeMinor]
kernel_rfl_theorem leafSchema_derived :
  iotaSchemaAt recA ⟨0, by decide⟩ admitFuel [] = some (.bvar 1)
kernel_rfl_theorem leafEquation_type :
  iotaEquationType recA ⟨0, by decide⟩ = .app (.bvar 2) (.const 5 [])
kernel_rfl_theorem nodeEquation_doms :
  equationDoms recA ⟨1, by decide⟩ = some [motiveTy, leafMinor, nodeMinor, field]
kernel_rfl_theorem nodeSchema_derived :
  iotaSchemaAt recA ⟨1, by decide⟩ admitFuel [.recursive 1] = some nodeSchema
kernel_rfl_theorem nodeEquation_type :
  iotaEquationType recA ⟨1, by decide⟩ = nodeEqType

noncomputable def field_beta_legacy (Γ : LCtx) :
    Conv eAll 0 Γ field normalField :=
  .step Γ field normalField
    (.beta Γ (.sort .zero) normalField (.const 4 []))

noncomputable def nodeIota_legacy :
    HasTy eAll 0 nodeIotaCtx nodeSchema nodeEqType := by
  let Γ := .assumption (.sort .zero) :: nodeIotaCtx
  have hM : HasTy eAll 0 nodeIotaCtx (.bvar 1) (lift 0 2 nodeMinor) :=
    .bvar _ 1 _ rfl
  have hF : HasTy eAll 0 nodeIotaCtx (.bvar 0) field := .bvar _ 0 _ rfl
  have hMot' : HasTy eAll 0 Γ (.bvar 4) motiveTy := .bvar _ 4 _ rfl
  have hLeaf' : HasTy eAll 0 Γ (.bvar 3) (lift 0 4 leafMinor) := .bvar _ 3 _ rfl
  have hNode' : HasTy eAll 0 Γ (.bvar 2) (lift 0 3 nodeMinor) := .bvar _ 2 _ rfl
  have hF' : HasTy eAll 0 Γ (.bvar 1) field := .bvar _ 1 _ rfl
  have hFN' : HasTy eAll 0 Γ (.bvar 1) normalField :=
    .conv _ _ _ _ hF' (field_beta_legacy Γ)
  have hX : HasTy eAll 0 Γ (.bvar 0) (.sort .zero) := .bvar _ 0 _ rfl
  have hRec : HasTy eAll 0 Γ (.const 7 []) recTypeView := by
    rw [← recType_eq]
    exact .const _ 7 [] recMem rfl rfl (fun _ h => nomatch h)
  exact HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ hM hF)
    (HasTy.lam _ (.sort .zero) (.succ .zero) _ _
      (HasTy.sort _ .zero)
      (HasTy.app _ _ _ _ _
        (HasTy.app _ _ _ _ _
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _ hRec hMot') hLeaf') hNode')
        (HasTy.app _ _ _ _ _ hFN' hX)))

noncomputable def leafIota_legacy :
    IotaEquationTyped recA ⟨0, by decide⟩ admitFuel [] := by
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
    cases i with
    | zero => exact leafIota_legacy
    | succ i =>
        cases i with
        | zero => exact nodeIota_legacy_at
        | succ i =>
            have h : i + 1 + 1 < 2 := hi
            exact (by omega : False).elim

/-- The original typed equation, with the same explicit beta conversion.
The conversion-free `synCheck` used by `memberContentB` cannot synthesize
this derivation, but the original `IndGroupTypedT` premise accepts it. -/
noncomputable def nodeIota_typed :
    HasTyT eAll 0 nodeIotaCtx nodeSchema nodeEqType := by
  let Γ := .assumption (.sort .zero) :: nodeIotaCtx
  have hM : HasTyT eAll 0 nodeIotaCtx (.bvar 1) (lift 0 2 nodeMinor) :=
    .bvar _ 1 _ rfl
  have hF : HasTyT eAll 0 nodeIotaCtx (.bvar 0) field := .bvar _ 0 _ rfl
  have hMot' : HasTyT eAll 0 Γ (.bvar 4) motiveTy := .bvar _ 4 _ rfl
  have hLeaf' : HasTyT eAll 0 Γ (.bvar 3) (lift 0 4 leafMinor) := .bvar _ 3 _ rfl
  have hNode' : HasTyT eAll 0 Γ (.bvar 2) (lift 0 3 nodeMinor) := .bvar _ 2 _ rfl
  have hF' : HasTyT eAll 0 Γ (.bvar 1) field := .bvar _ 1 _ rfl
  have hFN' : HasTyT eAll 0 Γ (.bvar 1) normalField :=
    .conv _ _ _ _ (.imax (.succ .zero) .zero) hF' (field_beta rfl Γ)
  have hX : HasTyT eAll 0 Γ (.bvar 0) (.sort .zero) := .bvar _ 0 _ rfl
  have hRec : HasTyT eAll 0 Γ (.const 7 []) recTypeView := by
    rw [← recType_eq]
    exact .const _ 7 [] recMem rfl rfl rfl
  exact HasTyT.app _ _ _ _ _
    (HasTyT.app _ _ _ _ _ hM hF)
    (HasTyT.lam _ (.sort .zero) (.succ .zero) _ _
      (HasTyT.sort _ .zero)
      (HasTyT.app _ _ _ _ _
        (HasTyT.app _ _ _ _ _
          (HasTyT.app _ _ _ _ _
            (HasTyT.app _ _ _ _ _ hRec hMot') hLeaf') hNode')
        (HasTyT.app _ _ _ _ _ hFN' hX)))

theorem leafIota_typed_at :
    IotaEquationTypedT recA ⟨0, by decide⟩ admitFuel [] := by
  unfold IotaEquationTypedT
  rw [leafEquation_doms, leafSchema_derived, leafEquation_type]
  exact ⟨HasTyT.bvar leafIotaCtx 1 _ rfl⟩

theorem nodeIota_typed_at :
    IotaEquationTypedT recA ⟨1, by decide⟩ admitFuel [.recursive 1] := by
  unfold IotaEquationTypedT
  rw [nodeEquation_doms, nodeSchema_derived, nodeEquation_type]
  exact ⟨nodeIota_typed⟩

kernel_rfl_theorem nodeIota_syn_refused :
  (synCheck eAll 0 nodeIotaCtx nodeSchema nodeEqType).isSome = false

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

/- The executable route really refuses: its final iota check is
`synCheck`, which cannot introduce the required type conversion. -/
kernel_rfl_theorem recContentB_refused : memberContentB ePre admitFuel recAdm = false
kernel_rfl_theorem recAcceptB_refused :
  memberAcceptB eFam ePre admitFuel recAdm recSort.1 = false

/- All other original recursor gates are paid independently. -/
kernel_rfl_theorem recStructB : memberStructB ePre recMem = true
kernel_rfl_theorem recFamilyB : famTypedB ePre admitFuel recA.family = true
kernel_rfl_theorem recCtorsB : ctorTypedAllB admitFuel recA = true
kernel_rfl_theorem recIdxB : recIdxAdmittedTB recA recIota = true

noncomputable def recPaid : PProd (IdxAdmittedT recAdm) (IndGroupTypedT recAdm) :=
  ⟨RecursorGroupIdxAdmittedT.ofCheck recA recIota recIdxB,
    ⟨famTypedT_of recA.family recFamilyB, ctorTypedAll_of recCtorsB,
      (fun | ⟨0, _⟩ => leafIota_typed_at | ⟨1, _⟩ => nodeIota_typed_at)⟩⟩

/-- The same original checked-member step for the first three members.
It merely exposes the existing soundness construction so the final
recursor can carry its explicit typed equation. -/
noncomputable def checkedCons {S E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {rest : List (Nat × CheckedMember)} {u : Level}
    (adm : IndGroupAdmitted E r m) (hT : HasTyT E m.arity [] m.mtype (.sort u))
    (hacc : memberAcceptB S E admitFuel adm u = true)
    (tail : GroupMembersT S (extendEnv E r m) rest E') :
    GroupMembersT S E ((r, m) :: rest) E' := by
  have h := hacc
  simp only [memberAcceptB, Bool.and_eq_true] at h
  obtain ⟨hb, hcl, har, hlvl, hcan, hcoh⟩ := memberStructB_of h.1.1
  have hc := memberContentB_of adm h.2
  exact .cons E r m rest E' adm.fresh hb hcl har hlvl hcan hcoh adm hc.1 u hT
    (memberScopeB_of h.1.2) hc.2 tail

noncomputable def recMembersT : GroupMembersT eFam ePre [(7, recMem)] eAll := by
  obtain ⟨hb, hcl, har, hlvl, hcan, hcoh⟩ := memberStructB_of recStructB
  exact .cons ePre 7 recMem [] eAll recAdm.fresh hb hcl har hlvl hcan hcoh
    recAdm recPaid.1 recSort.1 recSort.2 (fun h => absurd h (by decide))
    recPaid.2 (.nil eAll)

/-- Actual original membership: every structural, scope, typing, mirror,
iota and index premise of GroupMembersT is retained. -/
noncomputable def membersT : GroupMembersT eFam emptyEnv slots eAll :=
  checkedCons familyAdm famSort.2 famAcceptB
    (checkedCons leafAdm leafSort.2 leafAcceptB
      (checkedCons nodeAdm nodeSort.2 nodeAcceptB recMembersT))

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
noncomputable def branch_normal_typed : HasTyT eAll 0 [] branch normalField :=
  .lam [] (.sort .zero) (.succ .zero) (.const 5 []) (.const 4 [])
    (.sort [] .zero) (.const [.assumption (.sort .zero)] 5 [] leaf rfl rfl rfl)

noncomputable def branch_typed : HasTyT eAll 0 [] branch field :=
  .conv [] branch normalField field (.imax (.succ .zero) .zero)
    branch_normal_typed
    (.symm [] field normalField (.sort (.imax (.succ .zero) .zero))
      (field_beta rfl []))

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

end Rcic.Declarative.FamilyBetaPropTree

#print axioms Rcic.Declarative.FamilyBetaPropTree.nodeIota_typed
#print axioms Rcic.Declarative.FamilyBetaPropTree.recContentB_refused
#print axioms Rcic.Declarative.FamilyBetaPropTree.recPaid
#print axioms Rcic.Declarative.FamilyBetaPropTree.envWfT
#print axioms Rcic.Declarative.FamilyBetaPropTree.component_witness
