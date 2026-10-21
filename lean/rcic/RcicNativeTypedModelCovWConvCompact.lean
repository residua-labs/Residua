import rcic.RcicNativeTypedModelCovWConvLevels
import rcic.RcicNativeTypedModelCovWConvK

/-! A raw presentation retains source universe vectors. Public codes quotient
all universe labels by eqN without selecting representatives. The old compact
is used only for its already checked strict coverage constraints. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
open TypedModelAudit TypedModelCovWIrrelAudit TypedModelCovWNativeAudit

inductive CptWConvR where
  | bot
  | sort (l : Level)
  | pi (a : CptWConvR) (rows : List (List CptWConvR × CptWConvR))
  | lam (rows : List (List CptWConvR × CptWConvR))
  | spine (r : Nat) (ls : List Level) (args : List CptWConvR)

mutual
  def covWConvRawErase : CptWConvR → CptWIrrel
    | .bot => .bot
    | .sort l => sortCodeWIrrel l
    | .pi a rows => .pi (covWConvRawErase a) (covWConvRawEraseRows rows)
    | .lam rows => .lam (covWConvRawEraseRows rows)
    | .spine r ls args => .spine r ls (covWConvRawEraseArgs args)
  def covWConvRawEraseRows : List (List CptWConvR × CptWConvR) → List (List CptWIrrel × CptWIrrel)
    | [] => []
    | (us, c) :: rows => (covWConvRawEraseArgs us, covWConvRawErase c) :: covWConvRawEraseRows rows
  def covWConvRawEraseArgs : List CptWConvR → List CptWIrrel
    | [] => []
    | u :: us => covWConvRawErase u :: covWConvRawEraseArgs us
end

@[simp] theorem covWConvRaw_erase_args (us : List CptWConvR) :
    covWConvRawEraseArgs us = us.map covWConvRawErase := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [covWConvRawEraseArgs, List.map_cons, ih]

@[simp] theorem covWConvRaw_erase_rows (rows : List (List CptWConvR × CptWConvR)) :
    covWConvRawEraseRows rows =
      rows.map (fun s => (s.1.map covWConvRawErase, covWConvRawErase s.2)) := by
  induction rows with
  | nil => rfl
  | cons s rows ih => cases s; simp only [covWConvRawEraseRows, List.map_cons,
      covWConvRaw_erase_args, ih]

def covWConvRawRowErase (s : List CptWConvR × CptWConvR) : List CptWIrrel × CptWIrrel :=
  (s.1.map covWConvRawErase, covWConvRawErase s.2)

theorem covWConvRaw_erase_bot_iff (c : CptWConvR) :
    covWConvRawErase c = .bot ↔ c = .bot := by
  cases c <;> simp [covWConvRawErase, sortCodeWIrrel]
  split <;> simp

def sortCodeWConvR (l : Level) : CptWConvR :=
  .sort l

theorem covWConvRaw_erase_sortCode (l : Level) :
    covWConvRawErase (sortCodeWConvR l) = sortCodeWIrrel l := rfl

abbrev EnvWConvR : Type := Nat → CptWConvR → Prop

def EnvWConvR.bot : EnvWConvR := fun _ c => c = .bot

def EnvWConvR.cons (S : CptWConvR → Prop) (ρ : EnvWConvR) : EnvWConvR
  | 0 => S
  | i + 1 => ρ i

def demandWConvR (us : List CptWConvR) : CptWConvR → Prop := fun c => c ∈ us

def EnvWConvR.pushArgs : List (CptWConvR → Prop) → EnvWConvR → EnvWConvR
  | [], ρ => ρ
  | S :: Ss, ρ => EnvWConvR.pushArgs Ss (EnvWConvR.cons S ρ)

def covWConvRawEnvErase (ρ : EnvWConvR) : EnvWIrrel :=
  fun i c => ∃ d, ρ i d ∧ covWConvRawErase d = c

theorem covWConvRaw_env_erase_bot : covWConvRawEnvErase EnvWConvR.bot = EnvWIrrel.bot := by
  funext i c
  apply propext
  constructor
  · rintro ⟨d, rfl, rfl⟩
    rfl
  · intro h
    exact ⟨.bot, rfl, h.symm⟩

theorem covWConvRaw_env_erase_cons (us : List CptWConvR) (ρ : EnvWConvR) :
    covWConvRawEnvErase (EnvWConvR.cons (demandWConvR us) ρ) =
      EnvWIrrel.cons (demandWIrrel (us.map covWConvRawErase)) (covWConvRawEnvErase ρ) := by
  funext i c
  cases i with
  | zero =>
      apply propext
      exact List.mem_map.symm
  | succ i => rfl

theorem covWConvRaw_env_erase_push (uss : List (List CptWConvR)) (ρ : EnvWConvR) :
    covWConvRawEnvErase (EnvWConvR.pushArgs (uss.map demandWConvR) ρ) =
      EnvWIrrel.pushArgs ((uss.map (List.map covWConvRawErase)).map demandWIrrel)
        (covWConvRawEnvErase ρ) := by
  induction uss generalizing ρ with
  | nil => rfl
  | cons us uss ih =>
      simp only [List.map_cons, EnvWConvR.pushArgs, EnvWIrrel.pushArgs]
      rw [ih, covWConvRaw_env_erase_cons]

def curryStepWConvR : List (List CptWConvR) → CptWConvR → CptWConvR
  | [], c => c
  | us :: uss, c => .lam [(us, curryStepWConvR uss c)]

def fieldDemandVectorsWConvR : List (List CptWConvR) → List (List CptWConvR)
  | [] => []
  | us :: uss =>
      us.map (fun u => u :: List.replicate uss.length .bot) ++
        (fieldDemandVectorsWConvR uss).map (fun vec => .bot :: vec)

def ctorDemandWConvR (r : Nat) (ls : List Level) (np : Nat)
    (uss : List (List CptWConvR)) : List CptWConvR :=
  .spine r ls (List.replicate np .bot ++ List.replicate uss.length .bot) ::
    (fieldDemandVectorsWConvR uss).map
      (fun vec => .spine r ls (List.replicate np .bot ++ vec))

theorem covWConvRaw_erase_curry (uss : List (List CptWConvR)) (c : CptWConvR) :
    covWConvRawErase (curryStepWConvR uss c) =
      curryStepWIrrel (uss.map (List.map covWConvRawErase)) (covWConvRawErase c) := by
  induction uss with
  | nil => rfl
  | cons us uss ih =>
      simp [curryStepWConvR, covWConvRawErase, curryStepWIrrel, ih]

theorem covWConvRaw_erase_vectors (uss : List (List CptWConvR)) :
    (fieldDemandVectorsWConvR uss).map (List.map covWConvRawErase) =
      fieldDemandVectorsWIrrel (uss.map (List.map covWConvRawErase)) := by
  induction uss with
  | nil => rfl
  | cons us uss ih =>
      simp [fieldDemandVectorsWConvR, fieldDemandVectorsWIrrel, List.map_map,
        Function.comp_def, covWConvRawErase, ← ih]

theorem covWConvRaw_erase_ctorDemand (r : Nat) (ls : List Level) (np : Nat)
    (uss : List (List CptWConvR)) :
    (ctorDemandWConvR r ls np uss).map covWConvRawErase =
      ctorDemandWIrrel r ls np (uss.map (List.map covWConvRawErase)) := by
  simp [ctorDemandWConvR, ctorDemandWIrrel, covWConvRawErase, List.map_map,
    ← covWConvRaw_erase_vectors, Function.comp_def]


mutual
  def covWConvCode : CptWConvR → CptWConv
    | .bot => .bot
    | .sort l => .sort (LevelCode.ofLevel l)
    | .pi a rows => .pi (covWConvCode a) (covWConvCodeRows rows)
    | .lam rows => .lam (covWConvCodeRows rows)
    | .spine r ls args => .spine r (ls.map LevelCode.ofLevel) (covWConvCodeArgs args)
  def covWConvCodeRows : List (List CptWConvR × CptWConvR) → List (List CptWConv × CptWConv)
    | [] => []
    | (us, c) :: rows => (covWConvCodeArgs us, covWConvCode c) :: covWConvCodeRows rows
  def covWConvCodeArgs : List CptWConvR → List CptWConv
    | [] => []
    | u :: us => covWConvCode u :: covWConvCodeArgs us
end

@[simp] theorem covWConv_code_args (us : List CptWConvR) :
    covWConvCodeArgs us = us.map covWConvCode := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [covWConvCodeArgs, List.map_cons, ih]

@[simp] theorem covWConv_code_rows (rows : List (List CptWConvR × CptWConvR)) :
    covWConvCodeRows rows = rows.map (fun s => (s.1.map covWConvCode, covWConvCode s.2)) := by
  induction rows with
  | nil => rfl
  | cons s rows ih => cases s; simp only [covWConvCodeRows, List.map_cons, covWConv_code_args, ih]

theorem covWConv_code_bot_iff (c : CptWConvR) : covWConvCode c = .bot ↔ c = .bot := by
  cases c <;> simp [covWConvCode]

abbrev covWConvCoarse (c : CptWConvR) : CptT := covWIrrelErase (covWConvRawErase c)

mutual
  /-- Universe formation retains succ and imax, including the Prop universe. -/
  inductive UniverseWConv (E : ResolvedEnv) : CptWConvR → Level → Prop
    | bot (l : Level) : UniverseWConv E .bot l
    | sort (u v : Level) (h : eqN (.succ u) v) : UniverseWConv E (.sort u) v
    | pi {a : CptWConvR} {rows : List (List CptWConvR × CptWConvR)} {u v l : Level}
        (hA : UniverseWConv E a u)
        (ht : ∀ s ∈ rows, ∀ c ∈ s.1, CTyWConvR E c a)
        (hb : ∀ s ∈ rows, UniverseWConv E s.2 v)
        (hl : eqN (.imax u v) l) : UniverseWConv E (.pi a rows) l
    | spine (r : Nat) (ls : List Level) (args : List CptWConvR)
        (m : CheckedMember) (u l : Level) (hm : E.members r = some m)
        (hu : piBody (instantiateLevels ls m.mtype) = .sort u)
        (hl : eqN u l) : UniverseWConv E (.spine r ls args) l
  /-- Strict finite rows plus level-respecting universe formation. -/
  inductive CTyWConvR (E : ResolvedEnv) : CptWConvR → CptWConvR → Prop
    | bot (a : CptWConvR) : CTyWConvR E .bot a
    | sortTy {c : CptWConvR} {l : Level}
        (hu : UniverseWConv E c l)
        (hc : CTyS E (covWConvCoarse c) (sortCode l)) : CTyWConvR E c (.sort l)
    | function {a : CptWConvR} {f g : List (List CptWConvR × CptWConvR)}
        (hc : CTyS E (covWConvCoarse (.lam f)) (covWConvCoarse (.pi a g)))
        (hi : ∀ s ∈ f, ∀ u ∈ s.1, CTyWConvR E u a)
        (ho : ∀ s ∈ f, ∀ t ∈ g,
          (∀ u ∈ t.1, ∃ v ∈ s.1, covWConvCode u = covWConvCode v) →
          CTyWConvR E s.2 t.2) :
        CTyWConvR E (.lam f) (.pi a g)
    | spine {r s : Nat} {ls ks : List Level} {args vals : List CptWConvR}
        (hc : CTyS E (covWConvCoarse (.spine r ls args))
          (covWConvCoarse (.spine s ks vals))) :
        CTyWConvR E (.spine r ls args) (.spine s ks vals)
end

theorem covWConv_typing_forget {E : ResolvedEnv} {c a : CptWConvR}
    (h : CTyWConvR E c a) : CTyS E (covWConvCoarse c) (covWConvCoarse a) := by
  cases h with
  | bot => exact ctyS_bot _
  | sortTy hu hc => simpa only [covWConvCoarse, covWConvRawErase, covWIrrel_erase_sortCode] using hc
  | function hc _ _ => exact hc
  | spine hc => exact hc

/-- Public typing uses raw witnesses; no quotient representative is chosen. -/
def CTySConv (E : ResolvedEnv) (c a : CptWConv) : Prop :=
  ∃ d b, covWConvCode d = c ∧ covWConvCode b = a ∧ CTyWConvR E d b

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_COMPACT_ROOTS
#print axioms CptWConvR
#print axioms covWConvRawErase
#print axioms covWConvRaw_erase_bot_iff
#print axioms covWConvRaw_env_erase_bot
#print axioms covWConvRaw_env_erase_cons
#print axioms covWConvRaw_env_erase_push
#print axioms covWConvRaw_erase_curry
#print axioms covWConvRaw_erase_ctorDemand
#print axioms covWConvCode
#print axioms covWConv_code_bot_iff
#print axioms UniverseWConv
#print axioms CTyWConvR
#print axioms covWConv_typing_forget
#print axioms CTySConv
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_COMPACT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
