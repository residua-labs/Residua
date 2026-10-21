import rcic.RcicNativeTypedModelCovWIrrelPositions

/-!
# Finite compacts retaining a rigid head's universe instance

Universe vectors are carried by every spine, including spines inside row
demands and outputs. They are introduced at the actual native constant and
preserved by rigid application. Erasure is structural and returns the
landed compact. No decoder, native normalization, or choice is used.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys TypedModelAudit

inductive CptWIrrel where
  | bot
  | prop
  | sort
  | pi (a : CptWIrrel) (rows : List (List CptWIrrel × CptWIrrel))
  | lam (rows : List (List CptWIrrel × CptWIrrel))
  | spine (r : Nat) (ls : List Level) (args : List CptWIrrel)

mutual
  def covWIrrelErase : CptWIrrel → CptT
    | .bot => .bot
    | .prop => .prop
    | .sort => .sort
    | .pi a rows => .pi (covWIrrelErase a) (covWIrrelEraseRows rows)
    | .lam rows => .lam (covWIrrelEraseRows rows)
    | .spine r _ args => .spine r (covWIrrelEraseArgs args)
  def covWIrrelEraseRows : List (List CptWIrrel × CptWIrrel) → List (List CptT × CptT)
    | [] => []
    | (us, c) :: rows => (covWIrrelEraseArgs us, covWIrrelErase c) :: covWIrrelEraseRows rows
  def covWIrrelEraseArgs : List CptWIrrel → List CptT
    | [] => []
    | u :: us => covWIrrelErase u :: covWIrrelEraseArgs us
end

@[simp] theorem covWIrrel_erase_args (us : List CptWIrrel) :
    covWIrrelEraseArgs us = us.map covWIrrelErase := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [covWIrrelEraseArgs, List.map_cons, ih]

@[simp] theorem covWIrrel_erase_rows (rows : List (List CptWIrrel × CptWIrrel)) :
    covWIrrelEraseRows rows =
      rows.map (fun s => (s.1.map covWIrrelErase, covWIrrelErase s.2)) := by
  induction rows with
  | nil => rfl
  | cons s rows ih => cases s; simp only [covWIrrelEraseRows, List.map_cons,
      covWIrrel_erase_args, ih]

def covWIrrelRowErase (s : List CptWIrrel × CptWIrrel) : List CptT × CptT :=
  (s.1.map covWIrrelErase, covWIrrelErase s.2)

theorem covWIrrel_erase_bot_iff (c : CptWIrrel) :
    covWIrrelErase c = .bot ↔ c = .bot := by
  cases c <;> simp [covWIrrelErase]

def sortCodeWIrrel (l : Level) : CptWIrrel :=
  if decEqN l .zero then .prop else .sort

theorem covWIrrel_erase_sortCode (l : Level) :
    covWIrrelErase (sortCodeWIrrel l) = sortCode l := by
  unfold sortCodeWIrrel sortCode
  split <;> rfl

abbrev EnvWIrrel : Type := Nat → CptWIrrel → Prop

def EnvWIrrel.bot : EnvWIrrel := fun _ c => c = .bot

def EnvWIrrel.cons (S : CptWIrrel → Prop) (ρ : EnvWIrrel) : EnvWIrrel
  | 0 => S
  | i + 1 => ρ i

def demandWIrrel (us : List CptWIrrel) : CptWIrrel → Prop := fun c => c ∈ us

def EnvWIrrel.pushArgs : List (CptWIrrel → Prop) → EnvWIrrel → EnvWIrrel
  | [], ρ => ρ
  | S :: Ss, ρ => EnvWIrrel.pushArgs Ss (EnvWIrrel.cons S ρ)

def covWIrrelEnvErase (ρ : EnvWIrrel) : EnvT :=
  fun i c => ∃ d, ρ i d ∧ covWIrrelErase d = c

theorem covWIrrel_env_erase_bot : covWIrrelEnvErase EnvWIrrel.bot = EnvT.bot := by
  funext i c
  apply propext
  constructor
  · rintro ⟨d, rfl, rfl⟩
    rfl
  · intro h
    exact ⟨.bot, rfl, h.symm⟩

theorem covWIrrel_env_erase_cons (us : List CptWIrrel) (ρ : EnvWIrrel) :
    covWIrrelEnvErase (EnvWIrrel.cons (demandWIrrel us) ρ) =
      EnvT.cons (demandT (us.map covWIrrelErase)) (covWIrrelEnvErase ρ) := by
  funext i c
  cases i with
  | zero =>
      apply propext
      exact List.mem_map.symm
  | succ i => rfl

theorem covWIrrel_env_erase_push (uss : List (List CptWIrrel)) (ρ : EnvWIrrel) :
    covWIrrelEnvErase (EnvWIrrel.pushArgs (uss.map demandWIrrel) ρ) =
      EnvT.pushArgs ((uss.map (List.map covWIrrelErase)).map demandT)
        (covWIrrelEnvErase ρ) := by
  induction uss generalizing ρ with
  | nil => rfl
  | cons us uss ih =>
      simp only [List.map_cons, EnvWIrrel.pushArgs, EnvT.pushArgs]
      rw [ih, covWIrrel_env_erase_cons]

def curryStepWIrrel : List (List CptWIrrel) → CptWIrrel → CptWIrrel
  | [], c => c
  | us :: uss, c => .lam [(us, curryStepWIrrel uss c)]

def fieldDemandVectorsWIrrel : List (List CptWIrrel) → List (List CptWIrrel)
  | [] => []
  | us :: uss =>
      us.map (fun u => u :: List.replicate uss.length .bot) ++
        (fieldDemandVectorsWIrrel uss).map (fun vec => .bot :: vec)

def ctorDemandWIrrel (r : Nat) (ls : List Level) (np : Nat)
    (uss : List (List CptWIrrel)) : List CptWIrrel :=
  .spine r ls (List.replicate np .bot ++ List.replicate uss.length .bot) ::
    (fieldDemandVectorsWIrrel uss).map
      (fun vec => .spine r ls (List.replicate np .bot ++ vec))

theorem covWIrrel_erase_curry (uss : List (List CptWIrrel)) (c : CptWIrrel) :
    covWIrrelErase (curryStepWIrrel uss c) =
      curryStepT (uss.map (List.map covWIrrelErase)) (covWIrrelErase c) := by
  induction uss with
  | nil => rfl
  | cons us uss ih =>
      simp [curryStepWIrrel, covWIrrelErase, curryStepT, ih]

theorem covWIrrel_erase_vectors (uss : List (List CptWIrrel)) :
    (fieldDemandVectorsWIrrel uss).map (List.map covWIrrelErase) =
      fieldDemandVectorsT (uss.map (List.map covWIrrelErase)) := by
  induction uss with
  | nil => rfl
  | cons us uss ih =>
      simp [fieldDemandVectorsWIrrel, fieldDemandVectorsT, List.map_map,
        Function.comp_def, covWIrrelErase, ← ih]

theorem covWIrrel_erase_ctorDemand (r : Nat) (ls : List Level) (np : Nat)
    (uss : List (List CptWIrrel)) :
    (ctorDemandWIrrel r ls np uss).map covWIrrelErase =
      ctorDemandT r np (uss.map (List.map covWIrrelErase)) := by
  simp [ctorDemandWIrrel, ctorDemandT, covWIrrelErase, List.map_map,
    ← covWIrrel_erase_vectors, Function.comp_def]

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_COMPACT_ROOTS
#print axioms CptWIrrel
#print axioms covWIrrelErase
#print axioms covWIrrelEraseRows
#print axioms covWIrrelEraseArgs
#print axioms covWIrrel_erase_args
#print axioms covWIrrel_erase_rows
#print axioms covWIrrelRowErase
#print axioms covWIrrel_erase_bot_iff
#print axioms sortCodeWIrrel
#print axioms covWIrrel_erase_sortCode
#print axioms EnvWIrrel
#print axioms EnvWIrrel.bot
#print axioms EnvWIrrel.cons
#print axioms demandWIrrel
#print axioms EnvWIrrel.pushArgs
#print axioms covWIrrelEnvErase
#print axioms covWIrrel_env_erase_bot
#print axioms covWIrrel_env_erase_cons
#print axioms covWIrrel_env_erase_push
#print axioms curryStepWIrrel
#print axioms fieldDemandVectorsWIrrel
#print axioms ctorDemandWIrrel
#print axioms covWIrrel_erase_curry
#print axioms covWIrrel_erase_vectors
#print axioms covWIrrel_erase_ctorDemand
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_COMPACT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
