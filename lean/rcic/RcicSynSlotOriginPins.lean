import rcic.RcicSynSlotOrigin

/-!
Native witnesses and executable acceptance/mutant pairs for S1C.
The global substitution holes are at index 1; their surviving slot's domain
witness is transported at relative tail index 0. Metadata is read from the
actual indexed endpoint, and never substitutes for the native typing below.
These pins do not assert arbitrary-AP coverage. `closure_claim = 0`.
-/

namespace Rcic.Syn.SlotOriginPins

open Rcic.Declarative

private def closed : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
private def stable : EnvMembersSubstStable emptyEnv :=
  envMembersSubstStable_of_envWfT EnvWfT.empty
private def levels : EnvLevelsT emptyEnv := envWfT_levels EnvWfT.empty
private def iotaLevels : IotaLevelsT emptyEnv := iotaLevelsT_of_envWfT EnvWfT.empty

def one : Level := .succ .zero
def two : Level := .succ one
def s0 : Expr Nat := .sort .zero
def s1 : Expr Nat := .sort one

def sourceTail : LCtx := [.assumption s1]
def sourceRoot : LCtx := [.assumption (.bvar 0), .assumption s1]
def outputRoot : LCtx := [.assumption s0]

def sourceDomain : HasTyT emptyEnv 0 sourceTail (.bvar 0) (.sort one) :=
  .bvar sourceTail 0 (.sort one) rfl

def sourceWf : CtxWfT emptyEnv 0 sourceRoot :=
  .assumption sourceTail (.bvar 0) one
    (.assumption [] s1 two .nil (.sort [] one)) sourceDomain

def sourceReceipt : AmbientReceipt emptyEnv 0 sourceRoot :=
  (AmbientReceipt.ofCtx sourceWf 0 (by decide)).val

def sourceAmbient : TransportedAmbient emptyEnv 0 sourceRoot 0 sourceTail
    (.bvar 0) one :=
  ⟨sourceReceipt, .refl⟩

def replacement : HasTyT emptyEnv 0 [] s0 s1 := .sort [] .zero

/-- Global j=1 really changes the surviving slot's stored domain. -/
theorem pin_esub_global_context : substRemove s0 1 sourceRoot = outputRoot := rfl

def sourceLookup : HasTyT emptyEnv 0 sourceRoot (.bvar 0) (.bvar 1) :=
  .bvar sourceRoot 0 (.bvar 1) rfl

def globalEsubNative : HasTyT emptyEnv 0 outputRoot (.bvar 0) s0 :=
  hasTyT_substS closed stable s0 s1 (j := 1) sourceLookup rfl
    (.sort outputRoot .zero)

/-- The same surviving domain uses tail cutoff j-i-1 = 0. -/
def esubAmbient : TransportedAmbient emptyEnv 0 sourceRoot 0 [] s0 one :=
  sourceAmbient.esub s0 s1 0 closed stable rfl replacement

def esubNative : HasTyT emptyEnv 0 [] s0 (.sort one) :=
  esubAmbient.materialize.native

theorem pin_esub_materialize_eq : esubAmbient.materialize.native =
    hasTyT_substS closed stable s0 s1 (j := 0) sourceDomain rfl replacement := rfl

theorem pin_esub_sort_exact :
    instantiate 0 (lift 0 0 s0) (.sort one) = .sort one := rfl

theorem pin_esub_original : esubAmbient.original = sourceReceipt := rfl

theorem pin_esub_prefix :
    esubAmbient.original.index = 0 ∧
    (sourceRoot.drop (esubAmbient.original.index + 1)).length = 1 ∧
    (sourceRoot.drop (esubAmbient.original.index + 1)).length < sourceRoot.length := by
  decide

/-- Exercise the recursive selector, as well as the head selector used above. -/
theorem pin_recursive_original_index :
    (AmbientReceipt.ofCtx sourceWf 1 (by decide)).val.index = 1 :=
  (AmbientReceipt.ofCtx sourceWf 1 (by decide)).property

def letTail : LCtx := [.letBinding s1 s0]
def letRoot : LCtx := [.assumption (.bvar 0), .letBinding s1 s0]

def letDomain : HasTyT emptyEnv 0 letTail (.bvar 0) (.sort one) :=
  .bvar letTail 0 (.sort one) rfl

def letWf : CtxWfT emptyEnv 0 letRoot :=
  .assumption letTail (.bvar 0) one
    (.letBinding [] s1 two s0 .nil (.sort [] one) replacement) letDomain

def letReceipt : AmbientReceipt emptyEnv 0 letRoot :=
  (AmbientReceipt.ofCtx letWf 0 (by decide)).val

def letAmbient : TransportedAmbient emptyEnv 0 letRoot 0 letTail (.bvar 0) one :=
  ⟨letReceipt, .refl⟩

theorem pin_lsub_global_context : substRemove s0 1 letRoot = outputRoot := rfl

def globalLsubNative : HasTyT emptyEnv 0 outputRoot (.bvar 0) s0 :=
  hasTyT_substLetS closed stable s1 s0 (j := 1)
    (.bvar letRoot 0 (.bvar 1) rfl) rfl (.sort outputRoot .zero)

def lsubAmbient : TransportedAmbient emptyEnv 0 letRoot 0 [] s0 one :=
  ⟨letReceipt, .lsub .refl s1 s0 0 closed stable rfl replacement⟩

def lsubNative : HasTyT emptyEnv 0 [] s0 (.sort one) :=
  lsubAmbient.materialize.native

theorem pin_lsub_materialize_eq : lsubAmbient.materialize.native =
    hasTyT_substLetS closed stable s1 s0 (j := 0) letDomain rfl replacement := rfl

theorem pin_lsub_sort_exact :
    instantiate 0 (lift 0 0 s0) (.sort one) = .sort one := rfl

theorem pin_lsub_original : lsubAmbient.original = letReceipt := rfl

def weakenedTail : LCtx := [.assumption s0, .assumption s1]

def wkAmbient : TransportedAmbient emptyEnv 0 sourceRoot 0 weakenedTail
    (.bvar 1) one :=
  ⟨sourceReceipt, .wk .refl (.assumption s0) 0 closed⟩

def wkNative : HasTyT emptyEnv 0 weakenedTail (.bvar 1) (.sort one) :=
  wkAmbient.materialize.native

theorem pin_wk_materialize_eq : wkAmbient.materialize.native =
    hasTyTWeaken (.assumption s0) closed (c := 0) sourceDomain := rfl

theorem pin_wk_sort_exact : lift 0 1 (.sort one : Expr Nat) = .sort one := rfl

theorem pin_wk_original : wkAmbient.original = sourceReceipt := rfl

/-- Append a second real operation after substitution: the current tail grows. -/
def esubWkStep : SortTyTransport emptyEnv 0 [] s0 one 0 sourceTail s0 one :=
  .wk .refl (.assumption s1) 0 closed

def esubWkAmbient : TransportedAmbient emptyEnv 0 sourceRoot 0 sourceTail s0 one :=
  esubAmbient.extend esubWkStep

def esubWkNative : HasTyT emptyEnv 0 sourceTail s0 (.sort one) :=
  esubWkAmbient.materialize.native

theorem pin_esub_wk_chain :
    esubWkAmbient.chain = esubAmbient.chain.append esubWkStep := rfl

theorem pin_esub_wk_materialize_eq : esubWkAmbient.materialize.native =
    hasTyTWeaken (.assumption s1) closed (c := 0) esubAmbient.materialize.native :=
  esubAmbient.extend_materialize esubWkStep

theorem pin_esub_wk_original : esubWkAmbient.original = sourceReceipt := rfl

theorem pin_esub_wk_prefix :
    esubWkAmbient.original.index = 0 ∧
    (sourceRoot.drop (esubWkAmbient.original.index + 1)).length = 1 ∧
    (sourceRoot.drop (esubWkAmbient.original.index + 1)).length < sourceRoot.length ∧
    esubAmbient.chain.length = 1 ∧ esubWkAmbient.chain.length = 2 ∧
    ([] : LCtx).length < sourceTail.length := by decide

def levelTail : LCtx := [.assumption (.sort (.param 0))]
def levelRoot : LCtx := [.assumption (.bvar 0), .assumption (.sort (.param 0))]

def levelDomain : HasTyT emptyEnv 1 levelTail (.bvar 0) (.sort (.param 0)) :=
  .bvar levelTail 0 (.sort (.param 0)) rfl

def levelWf : CtxWfT emptyEnv 1 levelRoot :=
  .assumption levelTail (.bvar 0) (.param 0)
    (.assumption [] (.sort (.param 0)) (.succ (.param 0)) .nil
      (.sort [] (.param 0))) levelDomain

def levelReceipt : AmbientReceipt emptyEnv 1 levelRoot :=
  (AmbientReceipt.ofCtx levelWf 0 (by decide)).val

def linstAmbient : TransportedAmbient emptyEnv 1 levelRoot 0
    [.assumption s0] (.bvar 0) .zero :=
  ⟨levelReceipt, .linst .refl 0 [.zero] rfl rfl levels iotaLevels⟩

def linstNative : HasTyT emptyEnv 0 [.assumption s0] (.bvar 0) (.sort .zero) :=
  linstAmbient.materialize.native

theorem pin_linst_materialize_eq : linstAmbient.materialize.native =
    hasTyT_instLevels levels iotaLevels (ls := [.zero]) (n := 0)
      rfl rfl levelDomain := rfl

/-- This changes the recorded sort AND the sort's proof/relevance bit. -/
theorem pin_linst_sort_reflection :
    instLevel [.zero] (.param 0) = .zero ∧
    levelIsZero (.param 0) = false ∧
    levelIsZero (instLevel [.zero] (.param 0)) = true := by
  decide

theorem pin_linst_original : linstAmbient.original = levelReceipt := rfl

/-- A nonidentity map: its action on parameter zero changes the proof bit. -/
def adapterMap : Level → Level := instLevel [.zero]

def adapterMapHom : LevelHom adapterMap := levelHom_id.linst [.zero]

/-- The mapped-list adapter is invoked with a nonidentity map and actual bound. -/
theorem pin_linst_map_bit :
    levelIsZero (instLevel ([.param 0].map adapterMap) (.param 0)) =
      levelIsZero (adapterMap (instLevel [.param 0] (.param 0))) :=
  sortTransport_linst_map_bit adapterMapHom [.param 0] (.param 0) rfl

theorem pin_linst_map_changes_bit :
    adapterMap (.param 0) = .zero ∧
    adapterMap (.param 0) ≠ (.param 0) ∧
    levelIsZero (instLevel [.param 0] (.param 0)) = false ∧
    levelIsZero (instLevel ([.param 0].map adapterMap) (.param 0)) = true := by decide

/-- Both the mapped sort and its reflected bit must agree with the actual map. -/
structure AdapterClaim where
  mappedSort : Level
  proofBit : Bool
  deriving DecidableEq

def adapterClaim : AdapterClaim :=
  ⟨instLevel ([.param 0].map adapterMap) (.param 0),
    levelIsZero (adapterMap (instLevel [.param 0] (.param 0)))⟩

def adapterAccepts (c : AdapterClaim) : Bool := decide (c = adapterClaim)

/-- Deliberately wrong: checks the mapped sort but omits the reflected bit. -/
def mutantIgnoreAdapterBit (c : AdapterClaim) : Bool :=
  decide (c.mappedSort = adapterClaim.mappedSort)

def staleAdapterBit : AdapterClaim :=
  { adapterClaim with proofBit := levelIsZero (instLevel [.param 0] (.param 0)) }

theorem pin_linst_map_acceptance_mutant :
    adapterAccepts adapterClaim = true ∧
    adapterAccepts staleAdapterBit = false ∧
    mutantIgnoreAdapterBit staleAdapterBit = true := by decide

/-- A claim about one actual typed endpoint and its original prefix receipt. -/
structure EndpointClaim where
  context : LCtx
  expression : Expr Nat
  sort : Level
  originalRoot : LCtx
  originalIndex : Nat
  originalTail : LCtx
  deriving DecidableEq

def endpointClaim {E : ResolvedEnv} {a n : Nat} {root Γ : LCtx}
    {A : Expr Nat} {u : Level} (p : TransportedAmbient E a root n Γ A u) : EndpointClaim :=
  ⟨Γ, A, u, root, p.original.index, root.drop (p.original.index + 1)⟩

def accepts {E : ResolvedEnv} {a n : Nat} {root Γ : LCtx}
    {A : Expr Nat} {u : Level} (p : TransportedAmbient E a root n Γ A u)
    (claim : EndpointClaim) : Bool :=
  decide (claim = endpointClaim p)

/-- Deliberately wrong: accepts an old expression with all other fields fresh. -/
def mutantIgnoreExpression {E : ResolvedEnv} {a n : Nat} {root Γ : LCtx}
    {A : Expr Nat} {u : Level} (p : TransportedAmbient E a root n Γ A u)
    (c : EndpointClaim) : Bool :=
  decide (c.context = Γ ∧ c.sort = u ∧ c.originalRoot = root ∧
    c.originalIndex = p.original.index ∧ c.originalTail = root.drop (p.original.index + 1))

/-- Deliberately wrong: retains the old sort after a level instantiation. -/
def mutantIgnoreSort {E : ResolvedEnv} {a n : Nat} {root Γ : LCtx}
    {A : Expr Nat} {u : Level} (p : TransportedAmbient E a root n Γ A u)
    (c : EndpointClaim) : Bool :=
  decide (c.context = Γ ∧ c.expression = A ∧ c.originalRoot = root ∧
    c.originalIndex = p.original.index ∧ c.originalTail = root.drop (p.original.index + 1))

/-- Deliberately wrong: treats a current endpoint as a new ambient root. -/
def mutantIgnoreOriginal {E : ResolvedEnv} {a n : Nat} {root Γ : LCtx}
    {A : Expr Nat} {u : Level} (_p : TransportedAmbient E a root n Γ A u)
    (c : EndpointClaim) : Bool :=
  decide (c.context = Γ ∧ c.expression = A ∧ c.sort = u)

def staleEsubExpression : EndpointClaim :=
  { endpointClaim esubAmbient with expression := .bvar 0 }
def staleLsubExpression : EndpointClaim :=
  { endpointClaim lsubAmbient with expression := .bvar 0 }
def staleWkExpression : EndpointClaim :=
  { endpointClaim wkAmbient with expression := .bvar 0 }
def staleLinstSort : EndpointClaim :=
  { endpointClaim linstAmbient with sort := .param 0 }
def rebasedEsubReceipt : EndpointClaim :=
  { endpointClaim esubAmbient with originalRoot := outputRoot, originalTail := [] }
def staleOriginalIndex : EndpointClaim :=
  { endpointClaim esubAmbient with originalIndex := 1, originalTail := [] }
def staleEsubWkExpression : EndpointClaim :=
  { endpointClaim esubWkAmbient with expression := .bvar 0 }
def rebasedEsubWkReceipt : EndpointClaim :=
  { endpointClaim esubWkAmbient with originalRoot := sourceTail, originalTail := [] }

/-- Every negative fixture is wrongly ACCEPTED by its named omission mutant. -/
theorem pin_esub_acceptance_mutant :
    accepts esubAmbient (endpointClaim esubAmbient) = true ∧
    accepts esubAmbient staleEsubExpression = false ∧
    mutantIgnoreExpression esubAmbient staleEsubExpression = true := by decide

theorem pin_lsub_acceptance_mutant :
    accepts lsubAmbient (endpointClaim lsubAmbient) = true ∧
    accepts lsubAmbient staleLsubExpression = false ∧
    mutantIgnoreExpression lsubAmbient staleLsubExpression = true := by decide

theorem pin_wk_acceptance_mutant :
    accepts wkAmbient (endpointClaim wkAmbient) = true ∧
    accepts wkAmbient staleWkExpression = false ∧
    mutantIgnoreExpression wkAmbient staleWkExpression = true := by decide

theorem pin_linst_acceptance_mutant :
    accepts linstAmbient (endpointClaim linstAmbient) = true ∧
    accepts linstAmbient staleLinstSort = false ∧
    mutantIgnoreSort linstAmbient staleLinstSort = true := by decide

theorem pin_original_prefix_acceptance_mutant :
    accepts esubAmbient rebasedEsubReceipt = false ∧
    mutantIgnoreOriginal esubAmbient rebasedEsubReceipt = true ∧
    accepts esubAmbient staleOriginalIndex = false ∧
    mutantIgnoreOriginal esubAmbient staleOriginalIndex = true := by decide

theorem pin_esub_wk_acceptance_mutant :
    accepts esubWkAmbient (endpointClaim esubWkAmbient) = true ∧
    accepts esubWkAmbient staleEsubWkExpression = false ∧
    mutantIgnoreExpression esubWkAmbient staleEsubWkExpression = true ∧
    accepts esubWkAmbient rebasedEsubWkReceipt = false ∧
    mutantIgnoreOriginal esubWkAmbient rebasedEsubWkReceipt = true := by decide

end Rcic.Syn.SlotOriginPins
