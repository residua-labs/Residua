/-
RCIC context morphisms — the context-insertion infrastructure for 02's
remaining preservation theorems (DT-003..007, DT-010..012).

The knife-2 lane named the wall precisely: under the stored-unlifted /
lookup-lifts-(i+1) convention, inserting a declaration at position c must
RENAME the stored types of the entries below it — each entry j < c gets its
stored expressions lifted at cutoff c-1-j. `insertAt` carries exactly that,
and its recursive equation
    insertAt d (c+1) (x :: Γ) = liftDecl c x :: insertAt d c Γ
is what makes the binder cases of a weakening proof go through unchanged:
weakening HasTy.lam's extended context (assumption A :: Γ) at c+1 yields
(assumption (lift c 1 A) :: insertAt d c Γ) — precisely the context the
weakened derivation needs.

INFRASTRUCTURE, not interface mechanization (M-010): the weakening /
substitution DT theorems remain the batch's delivery. Everything here rides
on SubstCalc's P1/P2, which is the layering working as intended.

M-002a: lift / instantiate / lookupType / lookupValue are the pinned entry
set of RcicDeclarative's carrier guards.
-/
import rcic.RcicDeclarative
import rcic.RcicSubstCalc

namespace Rcic.Declarative

/-- Rename one stored declaration at cutoff k. -/
def liftDecl (k : Nat) : LocalDecl → LocalDecl
  | .assumption A => .assumption (lift k 1 A)
  | .letBinding A v => .letBinding (lift k 1 A) (lift k 1 v)

/-- Insert `d` at position `c`, renaming the entries below it. -/
def insertAt (d : LocalDecl) : Nat → LCtx → LCtx
  | 0, Γ => d :: Γ
  | _+1, [] => [d]
  | c+1, x :: Γ => liftDecl c x :: insertAt d c Γ

@[simp] theorem insertAt_zero (d : LocalDecl) (Γ : LCtx) :
    insertAt d 0 Γ = d :: Γ := rfl

@[simp] theorem insertAt_succ_cons (d x : LocalDecl) (c : Nat) (Γ : LCtx) :
    insertAt d (c+1) (x :: Γ) = liftDecl c x :: insertAt d c Γ := rfl

/-! ### Tail lookups compose with a 0-cutoff lift (rides on P2 merge). -/

theorem lookupType_cons_succ (y : LocalDecl) (Δ : LCtx) (i : Nat) :
    lookupType (y :: Δ) (i+1) = (lookupType Δ i).map (lift 0 1) := by
  simp only [lookupType, List.get?_cons_succ]
  match h : Δ.get? i with
  | none => simp
  | some (.assumption a) =>
      simp only [Option.map_some']
      rw [lift_lift_merge 1 (i+1) 0 0 (by omega) (by omega)]
  | some (.letBinding a v) =>
      simp only [Option.map_some']
      rw [lift_lift_merge 1 (i+1) 0 0 (by omega) (by omega)]

theorem lookupValue_cons_succ (y : LocalDecl) (Δ : LCtx) (i : Nat) :
    lookupValue (y :: Δ) (i+1) = (lookupValue Δ i).map (lift 0 1) := by
  simp only [lookupValue, List.get?_cons_succ]
  match h : Δ.get? i with
  | none => simp
  | some (.assumption a) => simp
  | some (.letBinding a v) =>
      simp only [Option.map_some']
      rw [lift_lift_merge 1 (i+1) 0 0 (by omega) (by omega)]

/-! ### The four commutation lemmas a weakening proof consumes. -/

/-- Below the insertion point: same index, looked-up type lifts at c. -/
theorem lookupType_insertAt_lt (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    {A : Expr Nat} (hic : i < c) (h : lookupType Γ i = some A) :
    lookupType (insertAt d c Γ) i = some (lift c 1 A) := by
  induction c generalizing i Γ A with
  | zero => omega
  | succ c ih =>
    match Γ with
    | [] => simp [lookupType] at h
    | x :: Γ' =>
      match i with
      | 0 =>
        match x with
        | .assumption a =>
            simp only [lookupType, List.get?_cons_zero] at h
            cases h
            simp only [insertAt_succ_cons, lookupType, List.get?_cons_zero,
              liftDecl, Option.some.injEq]
            rw [lift_lift_permute 1 1 c 0 (by omega),
                show 1 + c = c + 1 from by omega]
        | .letBinding a v =>
            simp only [lookupType, List.get?_cons_zero] at h
            cases h
            simp only [insertAt_succ_cons, lookupType, List.get?_cons_zero,
              liftDecl, Option.some.injEq]
            rw [lift_lift_permute 1 1 c 0 (by omega),
                show 1 + c = c + 1 from by omega]
      | i' + 1 =>
        rw [lookupType_cons_succ] at h
        match h' : lookupType Γ' i' with
        | none => rw [h'] at h; simp at h
        | some A' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            rw [insertAt_succ_cons, lookupType_cons_succ,
                ih (by omega) h', Option.map_some']
            congr 1
            rw [lift_lift_permute 1 1 c 0 (by omega),
                show 1 + c = c + 1 from by omega]

/-- At or above the insertion point: index shifts by one, type lifts at c. -/
theorem lookupType_insertAt_ge (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    {A : Expr Nat} (hic : c ≤ i) (h : lookupType Γ i = some A) :
    lookupType (insertAt d c Γ) (i+1) = some (lift c 1 A) := by
  induction c generalizing i Γ A with
  | zero =>
      rw [insertAt_zero, lookupType_cons_succ, h, Option.map_some']
  | succ c ih =>
    match Γ with
    | [] => simp [lookupType] at h
    | x :: Γ' =>
      match i with
      | 0 => omega
      | i' + 1 =>
        rw [lookupType_cons_succ] at h
        match h' : lookupType Γ' i' with
        | none => rw [h'] at h; simp at h
        | some A' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            rw [insertAt_succ_cons, lookupType_cons_succ,
                ih (by omega) h', Option.map_some']
            congr 1
            rw [lift_lift_permute 1 1 c 0 (by omega),
                show 1 + c = c + 1 from by omega]

/-- Value analogue, below. -/
theorem lookupValue_insertAt_lt (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    {v : Expr Nat} (hic : i < c) (h : lookupValue Γ i = some v) :
    lookupValue (insertAt d c Γ) i = some (lift c 1 v) := by
  induction c generalizing i Γ v with
  | zero => omega
  | succ c ih =>
    match Γ with
    | [] => simp [lookupValue] at h
    | x :: Γ' =>
      match i with
      | 0 =>
        match x with
        | .assumption a => simp [lookupValue, List.get?_cons_zero] at h
        | .letBinding a v' =>
            simp only [lookupValue, List.get?_cons_zero] at h
            cases h
            simp only [insertAt_succ_cons, lookupValue, List.get?_cons_zero,
              liftDecl, Option.some.injEq]
            rw [lift_lift_permute 1 1 c 0 (by omega),
                show 1 + c = c + 1 from by omega]
      | i' + 1 =>
        rw [lookupValue_cons_succ] at h
        match h' : lookupValue Γ' i' with
        | none => rw [h'] at h; simp at h
        | some v' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            rw [insertAt_succ_cons, lookupValue_cons_succ,
                ih (by omega) h', Option.map_some']
            congr 1
            rw [lift_lift_permute 1 1 c 0 (by omega),
                show 1 + c = c + 1 from by omega]

/-- Value analogue, at or above. -/
theorem lookupValue_insertAt_ge (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    {v : Expr Nat} (hic : c ≤ i) (h : lookupValue Γ i = some v) :
    lookupValue (insertAt d c Γ) (i+1) = some (lift c 1 v) := by
  induction c generalizing i Γ v with
  | zero =>
      rw [insertAt_zero, lookupValue_cons_succ, h, Option.map_some']
  | succ c ih =>
    match Γ with
    | [] => simp [lookupValue] at h
    | x :: Γ' =>
      match i with
      | 0 => omega
      | i' + 1 =>
        rw [lookupValue_cons_succ] at h
        match h' : lookupValue Γ' i' with
        | none => rw [h'] at h; simp at h
        | some v' =>
            rw [h'] at h
            simp only [Option.map_some', Option.some.injEq] at h
            subst h
            rw [insertAt_succ_cons, lookupValue_cons_succ,
                ih (by omega) h', Option.map_some']
            congr 1
            rw [lift_lift_permute 1 1 c 0 (by omega),
                show 1 + c = c + 1 from by omega]

end Rcic.Declarative
