/-
RM-023: the levelEqual entry configuration carries encoded levels.

`LevelKind.encode` is a variable-width record. `toCore` accepts `.r`
only at one fixed field list, so no `CoreTy` holds every level.
`stepI` therefore receives `encLevel` (`decLevel_self`), which is a
constructor recursion and does not call `decEqN`.

`.zero` and `.max .zero .zero` both decide equal to `.zero`, and their
entry values differ. An answer bit would not.

`closure_claim` stays 0.
-/
import rcic.ScmMachine
import rcic.RcicLevelKind
import rcic.ScmInstantiate
import rcic.RcicLevelDec

namespace Rcic.LevelEqnStep

open Rcic.Scm
open Rcic.Declarative
open Rcic.LevelKind
open Rcic.Scm.Inst

private theorem toCoreVals_len :
    ∀ {ts : List CoreTy} {xs : List Val} {v : CoreVals ts},
      toCoreVals ts xs = some v → xs.length = ts.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [toCoreVals] at h
  | _ :: _, [], _, h => by simp [toCoreVals] at h
  | t :: ts, x :: xs, _, h => by
      simp only [toCoreVals] at h
      split at h
      · rename_i _ xs' _ hxs
        simp [toCoreVals_len hxs, List.length_cons]
      · simp at h

private theorem toCore_record (fs : List (String × CoreTy)) (xs : List Val) :
    toCore (.record fs) (.r xs) =
      (toCoreVals (fs.map Prod.snd) xs).map CoreVal.recordV := rfl

private theorem toCore_record_len {fs : List (String × CoreTy)} {xs : List Val}
    (h : (toCore (.record fs) (.r xs)).isSome = true) :
    xs.length = fs.length := by
  rw [toCore_record] at h
  cases htv : toCoreVals (fs.map Prod.snd) xs with
  | none => simp [htv] at h
  | some v =>
      have hl := toCoreVals_len htv
      simpa [List.length_map] using hl

private theorem toCore_not_record {t : CoreTy} (xs : List Val)
    (hn : ∀ fs, t ≠ .record fs) : toCore t (.r xs) = none := by
  cases t with
  | i64 => rfl
  | bool => rfl
  | str => rfl
  | bytes => rfl
  | list _ => rfl
  | pair _ _ => rfl
  | sum _ => rfl
  | record fs => exact absurd rfl (hn fs)

private theorem kind_zero_false {t : CoreTy}
    (hn : ∀ fs, t ≠ .record fs)
    (h : (toCore t (encode .zero)).isSome = true) : False := by
  rw [show encode .zero = .r [Val.i 0] from rfl] at h
  rw [toCore_not_record _ hn] at h
  cases h

/-- No single core type accepts every kind-record. -/
theorem kindRecord_not_uniform (t : CoreTy) :
    ¬ ∀ l : Level, (toCore t (encode l)).isSome = true := by
  intro h
  have hz := h .zero
  have hs := h (.succ .zero)
  cases t with
  | record fs =>
      have lz : [Val.i 0].length = fs.length :=
        toCore_record_len (by simpa [encode] using hz)
      have ls : [Val.i 1, Val.r [Val.i 0]].length = fs.length :=
        toCore_record_len (by simpa [encode] using hs)
      have heq : (1 : Nat) = 2 := by
        have h1 : [Val.i 0].length = 1 := rfl
        have h2 : [Val.i 1, Val.r [Val.i 0]].length = 2 := rfl
        rw [← h1, lz, ← ls, h2]
      exact absurd heq (by decide)
  | i64 => exact kind_zero_false (fun _ h => by cases h) hz
  | bool => exact kind_zero_false (fun _ h => by cases h) hz
  | str => exact kind_zero_false (fun _ h => by cases h) hz
  | bytes => exact kind_zero_false (fun _ h => by cases h) hz
  | list _ => exact kind_zero_false (fun _ h => by cases h) hz
  | pair _ _ => exact kind_zero_false (fun _ h => by cases h) hz
  | sum _ => exact kind_zero_false (fun _ h => by cases h) hz

def levelTy : CoreTy := .str

def levelStr (l : Level) : CoreVal levelTy := .strV (encLevel l)

theorem levelStr_injective {l1 l2 : Level} (h : levelStr l1 = levelStr l2) :
    l1 = l2 := by
  have hs : encLevel l1 = encLevel l2 := by injection h
  have h1 := decLevel_self l1
  rw [hs] at h1
  exact Option.some.inj (h1.symm.trans (decLevel_self l2))

/-- Both decide equal to `.zero`. The strings do not. -/
theorem levelStr_zero_ne_max_zero :
    decEqN .zero .zero = true ∧
    decEqN (.max .zero .zero) .zero = true ∧
    levelStr .zero ≠ levelStr (.max .zero .zero) := by
  refine ⟨decEqN_complete .zero .zero (fun _ => rfl),
          decEqN_complete _ _ (eqN_max_zero_left .zero), ?_⟩
  intro h
  cases levelStr_injective h

def h0 : inI64 0 := ⟨by decide, by decide⟩

def entryEnv (l1 l2 : Level) : CoreVals [levelTy, levelTy, .i64] :=
  .cons (levelStr l1) (.cons (levelStr l2) (.cons (.i64V 0 h0) .nil))

def S0 : Sig := ⟨[⟨[levelTy, levelTy, .i64], levelTy⟩], [], []⟩

def readL : CoreExpr S0 [levelTy, levelTy, .i64] levelTy := .var 0 rfl

def progRead : Bodies S0 S0.fns := .cons readL .nil

/-- The entry reads the encoded level. It does not hold a verdict bit. -/
def entryCfg (l1 l2 : Level) : Config S0 levelTy :=
  ⟨levelTy, .evalC (entryEnv l1 l2) readL, .nil⟩

theorem entry_steps (l1 l2 : Level) :
    stepI progRead (entryCfg l1 l2) =
      .next ⟨levelTy, .retC (levelStr l1), .nil⟩ := rfl

theorem entry_returns_level (l1 _l2 : Level) :
    stepI progRead ⟨levelTy, .retC (levelStr l1), .nil⟩ =
      .final (.returned (levelStr l1)) := rfl

/-- Erasure of the value a next-step returns. -/
def stepVal : StepResult S0 levelTy → Option Val
  | .next c =>
    match c.ctl with
    | .retC v => some v.erase
    | _ => none
  | _ => none

private theorem stepVal_entry (l1 l2 : Level) :
    stepVal (stepI progRead (entryCfg l1 l2)) = some (levelStr l1).erase := by
  rw [entry_steps]
  rfl

theorem entry_zero_ne_max_zero :
    entryCfg .zero .zero ≠ entryCfg (.max .zero .zero) .zero := by
  intro h
  have hstep :
      stepVal (stepI progRead (entryCfg .zero .zero)) =
        stepVal (stepI progRead (entryCfg (.max .zero .zero) .zero)) :=
    congrArg (fun (c : Config S0 levelTy) => stepVal (stepI progRead c)) h
  rw [stepVal_entry, stepVal_entry] at hstep
  injection hstep with hs
  injection hs with henc
  have h1 := decLevel_self .zero
  rw [henc] at h1
  exact Level.noConfusion (Option.some.inj (h1.symm.trans (decLevel_self _)))

#print axioms Rcic.LevelEqnStep.kindRecord_not_uniform
#print axioms Rcic.LevelEqnStep.levelStr_injective
#print axioms Rcic.LevelEqnStep.levelStr_zero_ne_max_zero
#print axioms Rcic.LevelEqnStep.entry_steps
#print axioms Rcic.LevelEqnStep.entry_returns_level
#print axioms Rcic.LevelEqnStep.entry_zero_ne_max_zero

end Rcic.LevelEqnStep
