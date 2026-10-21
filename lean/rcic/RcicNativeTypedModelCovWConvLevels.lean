import rcic.RcicNativeTypedModelCovWNativeFollowupSeal

namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

/-! Universe labels and a finite universe/Pi fragment.  This file does not
define the full guarded observation model or its completeness theorem. -/

def levelSetoid : Setoid Level where
  r := eqN
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ρ => (h ρ).symm
    trans := fun h₁ h₂ ρ => (h₁ ρ).trans (h₂ ρ)
  }

abbrev LevelCode := Quotient levelSetoid

namespace LevelCode

def ofLevel (u : Level) : LevelCode := Quotient.mk levelSetoid u

def eval (ρ : Nat → Option Nat) (q : LevelCode) : Option Nat :=
  Quotient.lift (Rcic.Declarative.eval ρ)
    (fun a b (h : eqN a b) => h ρ) q

def succ (q : LevelCode) : LevelCode :=
  Quotient.lift (fun u => ofLevel (.succ u))
    (fun _ _ h => Quotient.sound (eqN_congr_succ h)) q

def imax (q r : LevelCode) : LevelCode :=
  Quotient.liftOn₂ q r (fun u v => ofLevel (.imax u v))
    (by
      intro _ _ _ _ h₁ h₂
      exact Quotient.sound (eqN_congr_imax h₁ h₂))

@[simp] theorem eval_ofLevel (ρ : Nat → Option Nat) (u : Level) :
    eval ρ (ofLevel u) = Rcic.Declarative.eval ρ u := rfl

@[simp] theorem succ_ofLevel (u : Level) :
    succ (ofLevel u) = ofLevel (.succ u) := rfl

@[simp] theorem imax_ofLevel (u v : Level) :
    imax (ofLevel u) (ofLevel v) = ofLevel (.imax u v) := rfl

theorem ofLevel_eq_iff (u v : Level) :
    ofLevel u = ofLevel v ↔ eqN u v := by
  constructor
  · intro h ρ
    exact congrArg (eval ρ) h
  · intro h
    exact Quotient.sound h

end LevelCode

/- All trees and tables are finite.  Only their universe labels are quotiented;
terms and observation trees are not quotiented by conversion. -/
inductive CptWConv where
  | bot
  | sort : LevelCode → CptWConv
  | pi : CptWConv → List (List CptWConv × CptWConv) → CptWConv
  | lam : List (List CptWConv × CptWConv) → CptWConv
  | spine : Nat → List LevelCode → List CptWConv → CptWConv

theorem sort_code_exact (u v : Level) :
    CptWConv.sort (LevelCode.ofLevel u) =
      CptWConv.sort (LevelCode.ofLevel v) ↔ eqN u v := by
  constructor
  · intro h
    exact (LevelCode.ofLevel_eq_iff u v).mp (CptWConv.sort.inj h)
  · intro h
    exact congrArg CptWConv.sort ((LevelCode.ofLevel_eq_iff u v).mpr h)

/- Universe-formation fragment only.  The full guarded typing relation must
add its source derivations, occurrence discipline, and other code forms. -/
inductive CTyU : CptWConv → CptWConv → Prop where
  | sort (u : LevelCode) :
      CTyU (.sort u) (.sort (LevelCode.succ u))
  | pi {a : CptWConv} {rows : List (List CptWConv × CptWConv)}
      {u v : LevelCode} :
      CTyU a (.sort u) →
      (∀ row ∈ rows, ∀ c ∈ row.1, CTyU c a) →
      (∀ row ∈ rows, CTyU row.2 (.sort v)) →
      CTyU (.pi a rows) (.sort (LevelCode.imax u v))

theorem CTyU.pi_const {a b : CptWConv} {u v : LevelCode}
    (ha : CTyU a (.sort u)) (hb : CTyU b (.sort v)) :
    CTyU (.pi a [([], b)]) (.sort (LevelCode.imax u v)) := by
  apply CTyU.pi ha
  · intro row hrow c hc
    have hr : row = ([], b) := List.mem_singleton.mp hrow
    subst row
    cases hc
  · intro row hrow
    have hr : row = ([], b) := List.mem_singleton.mp hrow
    subst row
    exact hb

/- Exact structural observations of the sort/Pi fragment.  There is no
reduction closure, proof-erasure rule, or full guarded-model claim here. -/
inductive UniversePiFragmentObs : Expr Nat → CptWConv → Prop where
  | sort (u : Level) :
      UniversePiFragmentObs (.sort u) (.sort (LevelCode.ofLevel u))
  | pi {A B : Expr Nat} {a b : CptWConv} :
      UniversePiFragmentObs A a → UniversePiFragmentObs B b →
      UniversePiFragmentObs (.pi A B) (.pi a [([], b)])

def SameUniversePiFragmentObs (A B : Expr Nat) : Prop :=
  ∀ c, UniversePiFragmentObs A c ↔ UniversePiFragmentObs B c

theorem sort_fragment_obs_iff (u : Level) (c : CptWConv) :
    UniversePiFragmentObs (.sort u) c ↔
      c = .sort (LevelCode.ofLevel u) := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst c
    exact .sort u

theorem same_sort_fragment_obs_iff (u v : Level) :
    SameUniversePiFragmentObs (.sort u) (.sort v) ↔ eqN u v := by
  constructor
  · intro h
    have hv := (h (.sort (LevelCode.ofLevel u))).mp
      (UniversePiFragmentObs.sort u)
    exact (sort_code_exact u v).mp ((sort_fragment_obs_iff v _).mp hv)
  · intro h c
    have he := (LevelCode.ofLevel_eq_iff u v).mpr h
    constructor
    · intro hc
      apply (sort_fragment_obs_iff v c).mpr
      exact ((sort_fragment_obs_iff u c).mp hc).trans (congrArg CptWConv.sort he)
    · intro hc
      apply (sort_fragment_obs_iff u c).mpr
      exact ((sort_fragment_obs_iff v c).mp hc).trans (congrArg CptWConv.sort he.symm)

/- Completeness is asserted only for the sort row of this fragment. -/
def sort_fragment_complete {E} {n} {Γ} {u v : Level}
    (h : SameUniversePiFragmentObs (.sort u) (.sort v)) :
    ConvT E n Γ (.sort u) (.sort v) (.sort (.succ u)) :=
  .sorts Γ u v ((same_sort_fragment_obs_iff u v).mp h)

def levelOne : Level := .succ .zero
def levelTwo : Level := .succ levelOne
def levelThree : Level := .succ levelTwo

theorem levelOne_code_ne_levelTwo :
    LevelCode.ofLevel levelOne ≠ LevelCode.ofLevel levelTwo := by
  intro h
  have he := congrArg (LevelCode.eval (fun _ => some 0)) h
  have h12 : (some (1 : Nat)) = some 2 := he
  cases h12

theorem imax_two_three :
    LevelCode.imax (LevelCode.ofLevel levelTwo) (LevelCode.ofLevel levelThree) =
      LevelCode.ofLevel levelThree := by
  apply Quotient.sound
  intro ρ
  rfl

theorem imax_three_three :
    LevelCode.imax (LevelCode.ofLevel levelThree) (LevelCode.ofLevel levelThree) =
      LevelCode.ofLevel levelThree := by
  apply Quotient.sound
  intro ρ
  rfl

def universePiA : Expr Nat := .pi (.sort levelOne) (.sort levelTwo)
def universePiB : Expr Nat := .pi (.sort levelTwo) (.sort levelTwo)
def universePiACode : CptWConv :=
  .pi (.sort (LevelCode.ofLevel levelOne)) [([], .sort (LevelCode.ofLevel levelTwo))]
def universePiBCode : CptWConv :=
  .pi (.sort (LevelCode.ofLevel levelTwo)) [([], .sort (LevelCode.ofLevel levelTwo))]

theorem universePiA_CTyu :
    CTyU universePiACode (.sort (LevelCode.ofLevel levelThree)) := by
  change CTyU (.pi (.sort (LevelCode.ofLevel levelOne))
    [([], .sort (LevelCode.ofLevel levelTwo))]) (.sort (LevelCode.ofLevel levelThree))
  rw [← imax_two_three]
  exact CTyU.pi_const (CTyU.sort _) (CTyU.sort _)

theorem universePiB_CTyu :
    CTyU universePiBCode (.sort (LevelCode.ofLevel levelThree)) := by
  change CTyU (.pi (.sort (LevelCode.ofLevel levelTwo))
    [([], .sort (LevelCode.ofLevel levelTwo))]) (.sort (LevelCode.ofLevel levelThree))
  rw [← imax_three_three]
  exact CTyU.pi_const (CTyU.sort _) (CTyU.sort _)

theorem universePiA_has_obs : UniversePiFragmentObs universePiA universePiACode :=
  .pi (.sort _) (.sort _)

theorem universePiB_has_obs : UniversePiFragmentObs universePiB universePiBCode :=
  .pi (.sort _) (.sort _)

theorem universePiB_lacks_A_obs :
    ¬ UniversePiFragmentObs universePiB universePiACode := by
  intro h
  cases h with
  | pi hdom _ =>
    have he := (sort_fragment_obs_iff levelTwo _).mp hdom
    exact levelOne_code_ne_levelTwo (CptWConv.sort.inj he)

theorem universePi_fragment_separated :
    ¬ SameUniversePiFragmentObs universePiA universePiB := by
  intro h
  exact universePiB_lacks_A_obs ((h universePiACode).mp universePiA_has_obs)

#print axioms LevelCode.ofLevel_eq_iff
#print axioms sort_fragment_complete
#print axioms universePiA_CTyu
#print axioms universePiB_CTyu
#print axioms universePi_fragment_separated

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
