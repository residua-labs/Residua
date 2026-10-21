import rcic.RcicF8XValleyStrict
import rcic.RcicF8JBase

/-!
Distinct-index consumers for the S3e pending-chain repair. The raw typing, both
conversion literals, J1 valley, pending result and accepting mutant are closed
witnesses. Only integration with the existing global `Suppliers` interface takes
its named `SepAll` hypothesis. Credit: Devin desktop's `SRes.toValley` boundary
(#7115), and the concrete consumer in the #7097 delta audit. closure_claim=0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.XIndexPins
open Rcic.Syn

abbrev innerLevel : Level := .imax (.succ .zero) (.succ .zero)
abbrev innerT : Expr Nat := .sort innerLevel
abbrev targetT : Expr Nat := .sort (.max innerLevel .zero)
abbrev P : Expr Nat := .pi (.sort .zero) (.sort .zero)

def piTy : HasTyT emptyEnv 0 [] P innerT := pinPiT emptyEnv 0
def reflCv : ConvT emptyEnv 0 [] P P innerT := .refl [] P innerT piTy
def indexCv : ConvT emptyEnv 0 [] innerT targetT (.sort (.succ innerLevel)) :=
  .sorts [] innerLevel (.max innerLevel .zero) (fun _ => rfl)
abbrev roots : List (Jd emptyEnv 0) := [.cv reflCv, .cv indexCv]
def reflCert : ∃ r ∈ roots, SubEq (Jd.cv reflCv) r :=
  ⟨.cv reflCv, .head _, .inl rfl⟩
def indexCert : ∃ r ∈ roots, SubEq (Jd.cv indexCv) r :=
  ⟨.cv indexCv, .tail _ (.head _), .inl rfl⟩

def body : EvCv roots [] P P innerT := .lit reflCv reflCert
def indexEv : EvCv roots [] innerT targetT (.sort (.succ innerLevel)) :=
  .lit indexCv indexCert
def pending : EvTc roots [] innerT targetT := .ofCv (.succ innerLevel) indexEv
def viaTyConv : EvCv roots [] P P targetT := .tyConv (.succ innerLevel) body indexEv
def viaRety : EvCv roots [] P P targetT := .rety body pending
def core : Valley roots [] P P innerT := J1.reflValley piTy reflCert

/-- The two indices have equal universe values but different syntax. -/
theorem pin_indices_distinct : innerT ≠ targetT := by decide

theorem pin_core_leaves : core.leaves = [.ty piTy, .ty piTy, .ty piTy, .ty piTy] := rfl

/-- A real J1 answer, with its original literal's strict provenance. -/
theorem pin_core_strict (ℓ : Jd emptyEnv 0) (hℓ : ℓ ∈ core.leaves) :
    SubOf ℓ (.cv reflCv) := J1.reflValley_strict piTy reflCert ℓ hℓ

def pendingResult : SRes roots [] P P targetT := .val core pending
def trivialResult : SRes roots [] P P targetT :=
  .triv (J1.reflEndpoint piTy reflCert) pending

/-- The type of the consumer itself requires the requested index. -/
def restored : Valley roots [] P P targetT := pendingResult.toValley
def restoredTrivial : Valley roots [] P P targetT := trivialResult.toValley

def demandedTag {T : Expr Nat} (_ : Valley roots [] P P T) : Expr Nat := T

theorem pin_restored_index : demandedTag restored = targetT := rfl
theorem pin_restored_trivial_index : demandedTag restoredTrivial = targetT := rfl

/-- Both endpoint typings have the requested index, with one transport apiece. -/
theorem pin_restored_left_typing :
    restored.ty₁ = .rety (J1.reflEndpoint piTy reflCert) pending := rfl
theorem pin_restored_right_typing :
    restored.ty₂ = .rety (J1.reflEndpoint piTy reflCert) pending := rfl

/-- Four ordered conversion occurrences, one in each component: no deduplication
and no repeated restoration of the pending chain. -/
theorem pin_restored_once : restored.leaves =
    [.ty piTy, .cv indexCv, .ty piTy, .cv indexCv,
     .ty piTy, .cv indexCv, .ty piTy, .cv indexCv] := rfl

theorem pin_restored_trivial_once : restoredTrivial.leaves =
    [.ty piTy, .cv indexCv, .ty piTy, .cv indexCv,
     .ty piTy, .cv indexCv, .ty piTy, .cv indexCv] := rfl

abbrev Candidate := Σ' T : Expr Nat, Valley roots [] P P T

/-- The old defect as an executable mutant: expose the inner valley and drop its
pending chain. All returned valleys remain genuine typed objects. -/
def skipRestoration {T : Expr Nat} : SRes roots [] P P T → Candidate
  | .triv D _ => ⟨_, ⟨P, .refl D, .refl D, D, D⟩⟩
  | .val V _ => ⟨_, V⟩

def malformed : Candidate := skipRestoration pendingResult

/-- This mutant accepts the producer's result without restoring/checking the
requested index; it reproduces the actual existential-index exposure. -/
def mutantConsumer (r : SRes roots [] P P targetT) : Option Candidate :=
  some (skipRestoration r)

def requestedConsumer (c : Candidate) : Option Candidate :=
  if c.1 = targetT then some c else none

theorem pin_mutant_wrongly_accepts : (mutantConsumer pendingResult).isSome = true := rfl
theorem pin_mutant_same_malformed : mutantConsumer pendingResult = some malformed := rfl
theorem pin_mutant_returns_inner : malformed.1 = innerT := rfl
theorem pin_mutant_wrong_requested_index : malformed.1 ≠ targetT := pin_indices_distinct
theorem pin_same_malformed_rejected : requestedConsumer malformed = none := rfl
theorem pin_restored_accepted :
    (requestedConsumer ⟨targetT, restored⟩).isSome = true := rfl

/-- An actual original-literal refl supplier. Other constructors decline. -/
def jRefl (R : List (Jd emptyEnv 0)) : {Γ : LCtx} → {a b T : Expr Nat} →
    (h : ConvT emptyEnv 0 Γ a b T) → (∃ r ∈ R, SubEq (Jd.cv h) r) →
    Option (Valley R Γ a b T)
  | _, _, _, _, .refl _ _ _ d, hs => some (J1.reflValley d hs)
  | _, _, _, _, _, _ => none

theorem jRefl_contract : JContractWfP
    (fun R {_ _ _ _} _ h hs => jRefl R h hs) := by
  intro R Γ a b T hΓ h hs V hV ℓ hℓ
  cases h <;> simp only [jRefl] at hV <;> try exact Option.noConfusion hV
  rename_i d
  rw [Option.some.injEq] at hV
  subst V
  exact J1.reflValley_strict d hs ℓ hℓ

def suppliers (hsep : SepAll emptyEnv 0) : Suppliers emptyEnv 0 :=
  { Suppliers.declining hsep with
    J := fun R {_ _ _ _} _ h hs => jRefl R h hs
    hJ := jRefl_contract }

/-- These consumers exercise the two actual wrapper arms, not a caller-supplied
replacement for the worker's result. -/
def routeTyConv (hsep : SepAll emptyEnv 0) : Option (Valley roots [] P P targetT) :=
  (svalleyCv (suppliers hsep) viaTyConv CtxWfT.nil rfl).map
    (fun r => r.1.res.toValley)

def routeRety (hsep : SepAll emptyEnv 0) : Option (Valley roots [] P P targetT) :=
  (svalleyCv (suppliers hsep) viaRety CtxWfT.nil rfl).map
    (fun r => r.1.res.toValley)

theorem pin_tyConv_requested_index (hsep : SepAll emptyEnv 0) :
    (routeTyConv hsep).map demandedTag = some targetT := rfl
theorem pin_rety_requested_index (hsep : SepAll emptyEnv 0) :
    (routeRety hsep).map demandedTag = some targetT := rfl

theorem pin_tyConv_restores_once (hsep : SepAll emptyEnv 0) :
    (routeTyConv hsep).map Valley.leaves = some
      [.ty piTy, .cv indexCv, .ty piTy, .cv indexCv,
       .ty piTy, .cv indexCv, .ty piTy, .cv indexCv] := rfl
theorem pin_rety_restores_once (hsep : SepAll emptyEnv 0) :
    (routeRety hsep).map Valley.leaves = some
      [.ty piTy, .cv indexCv, .ty piTy, .cv indexCv,
       .ty piTy, .cv indexCv, .ty piTy, .cv indexCv] := rfl

/-- Appending either pending chain makes no new U/D calls and leaves the single
original J call unchanged. -/
theorem pin_tyConv_calls_unchanged (hsep : SepAll emptyEnv 0) :
    (svalleyCv (suppliers hsep) viaTyConv CtxWfT.nil rfl).map
      (fun r => (r.1.calls, r.1.jcalls)) = some ([], [.cv reflCv]) := rfl
theorem pin_rety_calls_unchanged (hsep : SepAll emptyEnv 0) :
    (svalleyCv (suppliers hsep) viaRety CtxWfT.nil rfl).map
      (fun r => (r.1.calls, r.1.jcalls)) = some ([], [.cv reflCv]) := rfl

/-- Reading the restored legs ignores the outer index conversion. This concrete
refl fixture asks no S supplier before or after restoration. -/
theorem pin_core_no_S (X : Suppliers emptyEnv 0) :
    (readValleyC X core).map (fun r => r.2.1) = some [] := by
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp [core, J1.reflValley, readValleyC, readStarC, ValleyOps.readValleyC,
    ValleyOps.readStarC, Suppliers.toValleyOps, reduceAnd]
theorem pin_restored_no_S (X : Suppliers emptyEnv 0) :
    (readValleyC X restored).map (fun r => r.2.1) = some [] := by
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp [restored, pendingResult, SRes.toValley, Valley.conv, core,
    J1.reflValley, readValleyC, readStarC, ValleyOps.readValleyC,
    ValleyOps.readStarC, Suppliers.toValleyOps, reduceAnd]

end Rcic.Declarative.F8Measure.XIndexPins

#print axioms Rcic.Declarative.F8Measure.XIndexPins.innerLevel
#print axioms Rcic.Declarative.F8Measure.XIndexPins.innerT
#print axioms Rcic.Declarative.F8Measure.XIndexPins.targetT
#print axioms Rcic.Declarative.F8Measure.XIndexPins.P
#print axioms Rcic.Declarative.F8Measure.XIndexPins.piTy
#print axioms Rcic.Declarative.F8Measure.XIndexPins.reflCv
#print axioms Rcic.Declarative.F8Measure.XIndexPins.indexCv
#print axioms Rcic.Declarative.F8Measure.XIndexPins.roots
#print axioms Rcic.Declarative.F8Measure.XIndexPins.reflCert
#print axioms Rcic.Declarative.F8Measure.XIndexPins.indexCert
#print axioms Rcic.Declarative.F8Measure.XIndexPins.body
#print axioms Rcic.Declarative.F8Measure.XIndexPins.indexEv
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pending
#print axioms Rcic.Declarative.F8Measure.XIndexPins.viaTyConv
#print axioms Rcic.Declarative.F8Measure.XIndexPins.viaRety
#print axioms Rcic.Declarative.F8Measure.XIndexPins.core
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_indices_distinct
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_core_leaves
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_core_strict
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pendingResult
#print axioms Rcic.Declarative.F8Measure.XIndexPins.trivialResult
#print axioms Rcic.Declarative.F8Measure.XIndexPins.restored
#print axioms Rcic.Declarative.F8Measure.XIndexPins.restoredTrivial
#print axioms Rcic.Declarative.F8Measure.XIndexPins.demandedTag
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_restored_index
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_restored_trivial_index
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_restored_left_typing
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_restored_right_typing
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_restored_once
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_restored_trivial_once
#print axioms Rcic.Declarative.F8Measure.XIndexPins.Candidate
#print axioms Rcic.Declarative.F8Measure.XIndexPins.skipRestoration
#print axioms Rcic.Declarative.F8Measure.XIndexPins.malformed
#print axioms Rcic.Declarative.F8Measure.XIndexPins.mutantConsumer
#print axioms Rcic.Declarative.F8Measure.XIndexPins.requestedConsumer
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_mutant_wrongly_accepts
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_mutant_same_malformed
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_mutant_returns_inner
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_mutant_wrong_requested_index
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_same_malformed_rejected
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_restored_accepted
#print axioms Rcic.Declarative.F8Measure.XIndexPins.jRefl
#print axioms Rcic.Declarative.F8Measure.XIndexPins.jRefl_contract
#print axioms Rcic.Declarative.F8Measure.XIndexPins.suppliers
#print axioms Rcic.Declarative.F8Measure.XIndexPins.routeTyConv
#print axioms Rcic.Declarative.F8Measure.XIndexPins.routeRety
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_tyConv_requested_index
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_rety_requested_index
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_tyConv_restores_once
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_rety_restores_once
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_tyConv_calls_unchanged
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_rety_calls_unchanged
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_core_no_S
#print axioms Rcic.Declarative.F8Measure.XIndexPins.pin_restored_no_S
