import Lean
import rcic.RcicF8JTrans
import rcic.RcicF8JTransportPins
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.J5a.Pins
open PEqTProofFront PEqLeafTPropPins F8Occurrences

def cl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
def ss : EnvMembersSubstStable emptyEnv := envMembersSubstStable_of_envWfT EnvWfT.empty

def tyP : HasTyT emptyEnv 0 [] P (.sort .zero) := P_ty []
def typ : HasTyT emptyEnv 0 [] p P := p_ty []
def tyq : HasTyT emptyEnv 0 [] q P := q_ty []
/-- Third proof differs from p and q (q already is identity applied to p). -/
def third : Expr Nat := .app (.lam P (.bvar 0)) q
def tyThird : HasTyT emptyEnv 0 [] third P :=
  .app [] (.lam P (.bvar 0)) q P P
    (.lam [] P .zero (.bvar 0) P tyP (.bvar [.assumption P] 0 P rfl)) tyq

def pq : ConvT emptyEnv 0 [] p q P := .irr [] P p q tyP typ tyq
def ps : ConvT emptyEnv 0 [] p third P := .irr [] P p third tyP typ tyThird
def up : ConvT emptyEnv 0 [] P aliasP (.sort .zero) := J3.Pins.aliasUp
def pqAt : ConvT emptyEnv 0 [] p q aliasP := .tyConv [] p q P aliasP .zero pq up
def psAt : ConvT emptyEnv 0 [] p third aliasP := .tyConv [] p third P aliasP .zero ps up
def h₁ : ConvT emptyEnv 0 [] q p aliasP := .symm [] p q aliasP pqAt
def h₂ : ConvT emptyEnv 0 [] p third aliasP := psAt
def input : ConvT emptyEnv 0 [] q third aliasP := .trans [] q p third aliasP h₁ h₂
def wrapper : ConvT emptyEnv 0 [] third q aliasP := .symm [] q third aliasP input
def roots : List (Jd emptyEnv 0) := [.cv wrapper]
def cert : ∃ r ∈ roots, SubEq (.cv input) r := ⟨_, .head _, .inr (.child (.head _))⟩
def cert₁ := certOfChild (x := Jd.cv h₁) (y := .cv input) (.head _) cert
def cert₂ := certOfChild (x := Jd.cv h₂) (y := .cv input) (.tail _ (.head _)) cert
def certPQAt := certOfChild (x := Jd.cv pqAt) (y := .cv h₁) (.head _) cert₁
def certPQ := certOfChild (x := Jd.cv pq) (y := .cv pqAt) (.head _) certPQAt
def certPS := certOfChild (x := Jd.cv ps) (y := .cv h₂) (.head _) cert₂

def first : J3.Result EnvWfT.empty roots h₁ :=
  ((J3.irrResult .empty tyP typ tyq certPQ).reindex .zero up certPQAt).swap
def second : J3.Result EnvWfT.empty roots h₂ :=
  (J3.irrResult .empty tyP typ tyThird certPS).reindex .zero up cert₂

def firstIndex : EvTc roots [] P aliasP := J3.indexField (h := pq) .zero up certPQAt
def secondIndex : EvTc roots [] P aliasP := J3.indexField (h := ps) .zero up cert₂
def firstBase : EvPar roots [] p q P := J1.irrStep tyP typ tyq certPQ
def secondBase : EvPar roots [] p third P := J1.irrStep tyP typ tyThird certPS
def firstRead : EvPar roots [] p q aliasP := firstBase.readConv firstIndex
def secondRead : EvPar roots [] p third aliasP := secondBase.readConv secondIndex
def firstPayload : ProofIndexPayload roots [] p q aliasP :=
  match firstRead with | .proofIndex x => x
/-- The concrete D-owned closing producer, with no sort uniqueness supplied. -/
def closingStep : EvPar roots [] q third aliasP :=
  proofIndexJoin firstPayload secondRead.rightTy

def groundD : Σ' d : Expr Nat,
    EvParStar roots [] q d aliasP × EvParStar roots [] third d aliasP :=
  ⟨third,
    .trans (.tail closingStep (.refl closingStep.rightTy)) (.refl secondRead.rightTy),
    .refl secondRead.rightTy⟩

/-- Actual D chooses exactly this branch for EVERY explicit su; su is not constructed. -/
theorem actual_D_branch (su : F8A2Support.SortUnique emptyEnv 0) :
    callD EnvWfT.empty su CtxWfT.nil first second = groundD := rfl

def groundValley : Valley roots [] q third aliasP where
  N := groundD.1
  left := .trans first.valley.left (readOutput groundD.2.1)
  right := .trans second.valley.right (readOutput groundD.2.2)
  ty₁ := first.valley.ty₁
  ty₂ := second.valley.ty₂

theorem actual_valley (su : F8A2Support.SortUnique emptyEnv 0) :
    (transResult EnvWfT.empty su CtxWfT.nil first second).valley = groundValley := rfl

theorem admissible_input : fragment input = true := rfl

theorem actual_worker (su : F8A2Support.SortUnique emptyEnv 0) :
    (buildFragment EnvWfT.empty su roots CtxWfT.nil input admissible_input cert).valley =
      groundValley := rfl

theorem actual_dispatch (su : F8A2Support.SortUnique emptyEnv 0) :
    (dispatchWf EnvWfT.empty su roots CtxWfT.nil input cert).isSome = true :=
  dispatchWf_coverage EnvWfT.empty su roots CtxWfT.nil input cert

theorem literal_not_in_roots : (Jd.cv input) ∉ roots := by
  intro hm
  have heq : (Jd.cv input) = .cv wrapper := by simpa [roots] using hm
  have hlt := child_wt_lt (x := Jd.cv input) (y := Jd.cv wrapper) (.head _)
  rw [heq] at hlt
  exact Nat.lt_irrefl _ hlt

theorem p_ne_q : p ≠ q := IrrPins.nonidentity
theorem q_ne_third : q ≠ third := by decide
theorem p_ne_third : p ≠ third := by decide
theorem index_nonidentity : aliasP ≠ P := alias_nonliteral

def tile : DTile roots := closingStep.toDTile cl ss [.cv input]
theorem tile_exact : tile = (baseCertificate cl ss [.cv input] closingStep).tile :=
  (baseCertificate_exact cl ss [.cv input] closingStep).symm

theorem closing_occurrence_live : (occurrences tile.step).length = 1 := rfl

theorem source_pair_is_generated :
    (q, third) ≠ (p, q) ∧ (q, third) ≠ (p, third) := by
  constructor <;> intro h <;> have hq := congrArg Prod.fst h <;> exact p_ne_q hq.symm

-- No J4/general generated-origin supplier is built from this observation.
end Rcic.Declarative.F8Measure.J5a.Pins

#eval Rcic.Declarative.F8Measure.J5a.Pins.groundValley.leaves.length

namespace Rcic.Declarative.F8Measure.J5a.Pins
open PEqTProofFront PEqLeafTPropPins F8Occurrences

theorem ground_inventory : groundValley.leaves =
    [Jd.ty tyq, .cv up, .ty tyP, .cv up, .ty tyq, .cv up,
     .ty tyThird, .cv up, .ty tyThird, .cv up,
     .ty tyThird, .cv up, .ty tyThird, .cv up,
     .ty tyq, .cv up, .ty tyThird, .cv up] := rfl

theorem ground_eighteen : groundValley.leaves.length = 18 := rfl

theorem prop_below : SubOf (Jd.ty tyP) (.cv input) := by
  apply SubOf.trans (y := Jd.cv ps)
  · exact .child (.head _)
  · apply SubOf.trans (y := Jd.cv h₂)
    · exact .child (.head _)
    · exact .child (.tail _ (.head _))

theorem q_below : SubOf (Jd.ty tyq) (.cv input) := by
  apply SubOf.trans (y := Jd.cv pq)
  · exact .child (.tail _ (.tail _ (.head _)))
  · apply SubOf.trans (y := Jd.cv pqAt)
    · exact .child (.head _)
    · apply SubOf.trans (y := Jd.cv h₁)
      · exact .child (.head _)
      · exact .child (.head _)

theorem third_below : SubOf (Jd.ty tyThird) (.cv input) := by
  apply SubOf.trans (y := Jd.cv ps)
  · exact .child (.tail _ (.tail _ (.head _)))
  · apply SubOf.trans (y := Jd.cv h₂)
    · exact .child (.head _)
    · exact .child (.tail _ (.head _))

theorem index_below : SubOf (Jd.cv up) (.cv input) := by
  apply SubOf.trans (y := Jd.cv h₂)
  · exact .child (.tail _ (.head _))
  · exact .child (.tail _ (.head _))

/-- Closed fixture: even its all-leaf clause does NOT assume SortUnique. -/
theorem ground_strict : ∀ l ∈ groundValley.leaves, SubOf l (.cv input) := by
  intro l hl
  rw [ground_inventory] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact q_below | exact prop_below | exact third_below | exact index_below

def groundResult : J3.Result EnvWfT.empty roots input where
  valley := groundValley
  leftTiles := ⟨baseCertificate cl ss [.cv input] closingStep, PUnit.unit⟩
  rightTiles := PUnit.unit
  strict := ground_strict

theorem actual_result_valley (su : F8A2Support.SortUnique emptyEnv 0) :
    (transResult EnvWfT.empty su CtxWfT.nil first second).valley = groundResult.valley := rfl

theorem actual_result_step (su : F8A2Support.SortUnique emptyEnv 0) :
    (transResult EnvWfT.empty su CtxWfT.nil first second).leftTiles.1.tile.step = tile.step := rfl

theorem actual_result_caller (su : F8A2Support.SortUnique emptyEnv 0) :
    (transResult EnvWfT.empty su CtxWfT.nil first second).leftTiles.1.tile.X = [.cv input] := rfl

theorem ground_return_edge (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([.cv input] ++ Z) (groundValley.leaves ++ Z) :=
  J3.result_edge groundResult Z

theorem original_child_call (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([Jd.cv input] ++ Z) ([.cv h₁, .cv h₂] ++ Z) := children_edge h₁ h₂ Z

theorem original_D_call (Z : List (Jd emptyEnv 0)) :
    OM3_edge ([Jd.cv input] ++ Z)
      ((first.valley.right.leaves ++ second.valley.left.leaves) ++ Z) :=
  d_call_edge first second Z

/-! Live wrong-ACCEPT controls. Each bad candidate is actual typed data.
No mutant or its rejection assumes su; the production worker keeps su explicit. -/

structure DCallCandidate where
  middle : Expr Nat
  center₁ : Expr Nat
  center₂ : Expr Nat
  left : EvParStar roots [] middle center₁ aliasP
  right : EvParStar roots [] middle center₂ aliasP

def actualCall : DCallCandidate :=
  ⟨p, first.valley.N, second.valley.N, first.valley.right, second.valley.left⟩
def wrongCall : DCallCandidate :=
  ⟨q, q, q, first.valley.left, first.valley.left⟩

def WeakCall (c : DCallCandidate) : Prop :=
  Nonempty (EvParStar roots [] c.middle c.center₁ aliasP) ∧
  Nonempty (EvParStar roots [] c.middle c.center₂ aliasP)
def ExactCall (c : DCallCandidate) : Prop :=
  c.middle = p ∧ HEq c.left first.valley.right ∧ HEq c.right second.valley.left

theorem actual_call_accepts : ExactCall actualCall := ⟨rfl, HEq.rfl, HEq.rfl⟩
theorem mutant_call_accepts : WeakCall wrongCall := ⟨⟨wrongCall.left⟩, ⟨wrongCall.right⟩⟩
theorem exact_call_refuses : ¬ ExactCall wrongCall :=
  fun h => p_ne_q h.1.symm

/-- Same indexed endpoints are not the same raw step object. -/
def wrappedStep : DStep roots [] p q aliasP := .conv (.base firstBase) firstIndex
def wrappedTile : DTile roots :=
  (J3.StepCertificate.reindex (baseCertificate cl ss [.cv input] firstBase)
    (firstIndex.val cl ss)).tile
def readTile : DTile roots := wrappedStep.toDTile cl ss [.cv input]
def emittedSpine : DSpine roots [] aliasP p q :=
  .tail wrappedStep (.refl firstRead.rightTy)

theorem emitted_read_exact : readSpine emittedSpine =
    EvParStar.tail firstRead (.refl firstRead.rightTy) := rfl

theorem emitted_tile_exact :
    (readSpine_certified cl ss [.cv input] emittedSpine).1.tile = readTile := rfl

def SameHeader (t₁ t₂ : DTile roots) : Prop :=
  t₁.Γ = t₂.Γ ∧ t₁.a = t₂.a ∧ t₁.b = t₂.b ∧ t₁.T = t₂.T
def ExactStep (t : DTile roots) : Prop := HEq t.step readTile.step

theorem mutant_step_accepts : SameHeader wrappedTile readTile := ⟨rfl, rfl, rfl, rfl⟩
theorem exact_step_refuses : ¬ ExactStep wrappedTile := by
  intro h
  have he := eq_of_heq h
  cases he

def badCaller : DTile roots := closingStep.toDTile cl ss roots
def WeakCaller (t : DTile roots) : Prop := HEq t.step tile.step
def ExactCaller (t : DTile roots) : Prop := t.X = [Jd.cv input]

theorem mutant_caller_accepts : WeakCaller badCaller := HEq.rfl
theorem exact_caller_refuses : ¬ ExactCaller badCaller := by
  intro h
  change roots = [Jd.cv input] at h
  apply literal_not_in_roots
  rw [h]
  exact List.mem_cons_self ..

def badInventory : List (Jd emptyEnv 0) := groundValley.leaves.take 6
def WeakInventory (reported : List (Jd emptyEnv 0)) : Prop :=
  ∀ l ∈ reported, SubOf l (.cv input)
def ExactInventory (reported : List (Jd emptyEnv 0)) : Prop :=
  reported = groundValley.leaves

theorem mutant_inventory_accepts : WeakInventory badInventory :=
  fun l hl => ground_strict l (List.mem_of_mem_take hl)
theorem exact_inventory_refuses : ¬ ExactInventory badInventory := by
  intro h
  have hl := congrArg List.length h
  change 6 = 18 at hl
  cases hl

/-- The mutation changes only unsupported admission to unconditional success. -/
def mutantAdmissible {Γ : LCtx} {a b T : Expr Nat}
    (_h : ConvT emptyEnv 0 Γ a b T) : Bool := true

theorem bad_grammar_input_live :
    Nonempty (ConvT emptyEnv 0 [] aliasP P (.sort .zero)) := ⟨J3.Pins.aliasDown⟩
theorem mutant_coverage_accepts : mutantAdmissible J3.Pins.aliasDown = true := rfl
theorem exact_coverage_refuses : fragment J3.Pins.aliasDown = false := rfl

theorem live_mutants :
    (WeakCall wrongCall ∧ ¬ ExactCall wrongCall) ∧
    (SameHeader wrappedTile readTile ∧ ¬ ExactStep wrappedTile) ∧
    (WeakCaller badCaller ∧ ¬ ExactCaller badCaller) ∧
    (WeakInventory badInventory ∧ ¬ ExactInventory badInventory) ∧
    (mutantAdmissible J3.Pins.aliasDown = true ∧ fragment J3.Pins.aliasDown = false) :=
  ⟨⟨mutant_call_accepts, exact_call_refuses⟩,
   ⟨mutant_step_accepts, exact_step_refuses⟩,
   ⟨mutant_caller_accepts, exact_caller_refuses⟩,
   ⟨mutant_inventory_accepts, exact_inventory_refuses⟩,
   ⟨mutant_coverage_accepts, exact_coverage_refuses⟩⟩

end Rcic.Declarative.F8Measure.J5a.Pins
