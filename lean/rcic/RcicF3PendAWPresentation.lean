import rcic.RcicF3PendAWFixture

/-!
# Checked boundaries of wrapped W admission

`closure_claim = 0`. These are negative executable-checker controls, not
admitted wrapped groups or refutations of object-language typing. The
beta wrapper reaches shape analysis but fails typed-iota construction;
the let wrapper fails constructor-view construction. No rule is changed.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

namespace Rcic.Declarative.PendAWPresentation
open PendAW

namespace Beta
abbrev baseField : Expr Nat := .pi (.bvar 0) (.app (.const 4 []) (.bvar 1))
abbrev field : Expr Nat := .app (.lam (.sort (.imax (.succ .zero) (.succ .zero))) (.bvar 0)) baseField
abbrev node : CheckedMember := ⟨.constructorM, 0,
  .pi (.sort (.succ .zero)) (.pi field (.app (.const 4 []) (.bvar 1))), none⟩
def preSlots : List (Nat × CheckedMember) := [(4, fam), (5, leaf), (6, node)]
theorem prefixNd : (preSlots.map (·.1)).Nodup := by decide

def recTy : Expr Nat := (rebuiltType? admitFuel preSlots prefixNd 4 fam
  [(5, leaf), (6, node)] 1).getD (.sort .zero)
def recMem : CheckedMember := ⟨.recursorM, 1, recTy, none⟩

abbrev ePre := extendEnv PendAW.eLeaf 6 node

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

kernel_rfl_theorem iotaRejected :
  (iotaClause? recA admitFuel recShapes recAnalyzed rfl).isSome = false
end Beta

abbrev zetaField : Expr Nat :=
  .letE (.sort (.imax (.succ .zero) (.succ .zero))) PendAW.field (.bvar 0)
abbrev zetaNode : CheckedMember := ⟨.constructorM, 0,
  .pi (.sort (.succ .zero)) (.pi zetaField (.app (.const 4 []) (.bvar 1))), none⟩
kernel_rfl_theorem zetaViewRejected :
  (buildCtorView? admitFuel PendAW.familyView zetaNode).isSome = false
end Rcic.Declarative.PendAWPresentation
