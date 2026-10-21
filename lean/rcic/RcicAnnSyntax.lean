import rcic.RcicDeclarative
import rcic.RcicLevelCalc

/-!
# M1-a — annotated syntax: `ExprA`, erasure, the §5 operations, the context and environment twins

Rows program M1 (`research/rcic/rows-m1/README.md`), slice (a). The Pujet–Tabareau
shape, as measured on the copy at I-3e-38 (Annex 23 R-RingAnnotated): `pi` carries
BOTH binder sorts (`.pi A u B v`) and `lam` its DOMAIN sort (`.lam A u body`); every
other constructor is `Expr Nat`'s verbatim. §(1)–(1b) are `RcicProbeAnn.lean`
(`wip/rcic-face`) re-based on `main`'s `RcicDeclarative` alone — reuse, not a
rewrite; `instantiateLevelsA` (§5's fourth operation, which the probe lacked) and
the environment twin §(1c) are new. Nothing landed is edited: `ExprA` sits beside
`Expr`, `ResolvedEnvA` beside `ResolvedEnv`, and `erase` is the only bridge.

What this slice does NOT contain, by design: no typing, no reduction, no
conversion, no logical relation. Those are M1-b (`hStepFnA`, `inferA`), M1-c
(`ConvAlgA`) and M1-d (`LR_A`, the irrelevance lemma — the kill criterion).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) `ExprA`: the annotated copy, and `erase` -/

/-- `Expr Nat` constructor for constructor, with the two binder sorts on `pi`
    and the domain sort on `lam`. -/
inductive ExprA : Type
  | bvar : Nat → ExprA
  | sort : Level → ExprA
  | const : Nat → List Level → ExprA
  | app : ExprA → ExprA → ExprA
  | lam : ExprA → Level → ExprA → ExprA
  | pi : ExprA → Level → ExprA → Level → ExprA
  | letE : ExprA → ExprA → ExprA → ExprA
  | lit : Nat → ExprA
  deriving DecidableEq

/-- the annotation is FORGOTTEN: `erase` drops `u` at `lam` and `u`, `v` at `pi`,
    and is the identity on every other constructor. -/
def erase : ExprA → Expr Nat
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f x => .app (erase f) (erase x)
  | .lam a _u b => .lam (erase a) (erase b)
  | .pi a _u b _v => .pi (erase a) (erase b)
  | .letE a v b => .letE (erase a) (erase v) (erase b)
  | .lit t => .lit t

/-- `lift` (`RcicDeclarative`) twin: the annotation is carried through untouched. -/
def liftA (cutoff amount : Nat) : ExprA → ExprA
  | .bvar i => if cutoff ≤ i then .bvar (i + amount) else .bvar i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f x => .app (liftA cutoff amount f) (liftA cutoff amount x)
  | .lam a u b => .lam (liftA cutoff amount a) u (liftA (cutoff+1) amount b)
  | .pi a u b v =>
      .pi (liftA cutoff amount a) u (liftA (cutoff+1) amount b) v
  | .letE a w b =>
      .letE (liftA cutoff amount a) (liftA cutoff amount w)
        (liftA (cutoff+1) amount b)
  | .lit t => .lit t

theorem erase_liftA (e : ExprA) (c k : Nat) :
    erase (liftA c k e) = lift c k (erase e) := by
  induction e generalizing c with
  | bvar i =>
      by_cases h : c ≤ i
      · simp only [liftA, lift, erase, if_pos h]
      · simp only [liftA, lift, erase, if_neg h]
  | sort _ => rfl
  | const _ _ => rfl
  | app _ _ ihf ihx => simp only [liftA, lift, erase, ihf, ihx]
  | lam _ _ _ iha ihb => simp only [liftA, lift, erase, iha, ihb]
  | pi _ _ _ _ iha ihb => simp only [liftA, lift, erase, iha, ihb]
  | letE _ _ _ iha ihw ihb => simp only [liftA, lift, erase, iha, ihw, ihb]
  | lit _ => rfl

/-- `instantiate` (02 §5) twin. -/
def instantiateA (index : Nat) (replacement : ExprA) : ExprA → ExprA
  | .bvar i =>
      if i = index then replacement
      else if index < i then .bvar (i - 1)
      else .bvar i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app f x =>
      .app (instantiateA index replacement f)
        (instantiateA index replacement x)
  | .lam a u b =>
      .lam (instantiateA index replacement a) u
        (instantiateA (index+1) (liftA 0 1 replacement) b)
  | .pi a u b v =>
      .pi (instantiateA index replacement a) u
        (instantiateA (index+1) (liftA 0 1 replacement) b) v
  | .letE a w b =>
      .letE (instantiateA index replacement a)
        (instantiateA index replacement w)
        (instantiateA (index+1) (liftA 0 1 replacement) b)
  | .lit t => .lit t

/-- `instantiate0` twin. -/
def instantiate0A (replacement : ExprA) (e : ExprA) : ExprA :=
  instantiateA 0 replacement e

theorem erase_instantiateA (e : ExprA) (idx : Nat) (r : ExprA) :
    erase (instantiateA idx r e) = instantiate idx (erase r) (erase e) := by
  induction e generalizing idx r with
  | bvar i =>
      by_cases h1 : i = idx
      · simp only [instantiateA, instantiate, erase, if_pos h1]
      · by_cases h2 : idx < i
        · simp only [instantiateA, instantiate, erase, if_neg h1,
            if_pos h2]
        · simp only [instantiateA, instantiate, erase, if_neg h1,
            if_neg h2]
  | sort _ => rfl
  | const _ _ => rfl
  | app _ _ ihf ihx => simp only [instantiateA, instantiate, erase, ihf, ihx]
  | lam _ _ _ iha ihb =>
      simp only [instantiateA, instantiate, erase, iha, ihb, erase_liftA]
  | pi _ _ _ _ iha ihb =>
      simp only [instantiateA, instantiate, erase, iha, ihb, erase_liftA]
  | letE _ _ _ iha ihw ihb =>
      simp only [instantiateA, instantiate, erase, iha, ihw, ihb, erase_liftA]
  | lit _ => rfl

theorem erase_instantiate0A (e r : ExprA) :
    erase (instantiate0A r e) = instantiate0 (erase r) (erase e) :=
  erase_instantiateA e 0 r

/-- §5's FOURTH operation on the copy. The annotation sorts are levels, so they
    are instantiated with the rest (a `param` in a binder sort is a level
    parameter like any other); every constructor is traversed, `bvar`/`lit`
    are the identity, exactly as `instantiateLevels`. -/
def instantiateLevelsA (levels : List Level) : ExprA → ExprA
  | .bvar i => .bvar i
  | .sort l => .sort (instLevel levels l)
  | .const r ms => .const r (ms.map (instLevel levels))
  | .app f x => .app (instantiateLevelsA levels f) (instantiateLevelsA levels x)
  | .lam a u b =>
      .lam (instantiateLevelsA levels a) (instLevel levels u)
        (instantiateLevelsA levels b)
  | .pi a u b v =>
      .pi (instantiateLevelsA levels a) (instLevel levels u)
        (instantiateLevelsA levels b) (instLevel levels v)
  | .letE a w b =>
      .letE (instantiateLevelsA levels a) (instantiateLevelsA levels w)
        (instantiateLevelsA levels b)
  | .lit t => .lit t

theorem erase_instantiateLevelsA (e : ExprA) (ls : List Level) :
    erase (instantiateLevelsA ls e) = instantiateLevels ls (erase e) := by
  induction e with
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app _ _ ihf ihx =>
      simp only [instantiateLevelsA, instantiateLevels, erase, ihf, ihx]
  | lam _ _ _ iha ihb =>
      simp only [instantiateLevelsA, instantiateLevels, erase, iha, ihb]
  | pi _ _ _ _ iha ihb =>
      simp only [instantiateLevelsA, instantiateLevels, erase, iha, ihb]
  | letE _ _ _ iha ihw ihb =>
      simp only [instantiateLevelsA, instantiateLevels, erase, iha, ihw, ihb]
  | lit _ => rfl

/-! ## (1b) the context copy -/

/-- `LocalDecl` on `ExprA`. NOTHING is annotated here: the annotation lives on
    `pi`/`lam` only. -/
inductive LocalDeclA : Type
  | assumption : ExprA → LocalDeclA
  | letBinding : ExprA → ExprA → LocalDeclA
  deriving DecidableEq

abbrev LCtxA := List LocalDeclA

def eraseDecl : LocalDeclA → LocalDecl
  | .assumption a => .assumption (erase a)
  | .letBinding a v => .letBinding (erase a) (erase v)

def eraseCtx (Γ : LCtxA) : LCtx := Γ.map eraseDecl

def lookupTypeA (Γ : LCtxA) (i : Nat) : Option ExprA :=
  match Γ.get? i with
  | some (.assumption a) => some (liftA 0 (i+1) a)
  | some (.letBinding a _) => some (liftA 0 (i+1) a)
  | none => none

def lookupValueA (Γ : LCtxA) (i : Nat) : Option ExprA :=
  match Γ.get? i with
  | some (.letBinding _ v) => some (liftA 0 (i+1) v)
  | _ => none

theorem get?_eraseCtx (Γ : LCtxA) (i : Nat) :
    (eraseCtx Γ).get? i = (Γ.get? i).map eraseDecl := by
  induction Γ generalizing i with
  | nil => cases i <;> rfl
  | cons d Γ ih => cases i with
    | zero => rfl
    | succ j => exact ih j

theorem lookupType_eraseCtx (Γ : LCtxA) (i : Nat) :
    lookupType (eraseCtx Γ) i = (lookupTypeA Γ i).map erase := by
  have hg := get?_eraseCtx Γ i
  match hh : Γ.get? i with
  | none =>
      simp only [lookupType, lookupTypeA, hg, hh, Option.map_none']
  | some (.assumption a) =>
      simp only [lookupType, lookupTypeA, hg, hh, eraseDecl,
        Option.map_some', erase_liftA]
  | some (.letBinding a v) =>
      simp only [lookupType, lookupTypeA, hg, hh, eraseDecl,
        Option.map_some', erase_liftA]

theorem lookupValue_eraseCtx (Γ : LCtxA) (i : Nat) :
    lookupValue (eraseCtx Γ) i = (lookupValueA Γ i).map erase := by
  have hg := get?_eraseCtx Γ i
  match hh : Γ.get? i with
  | none =>
      simp only [lookupValue, lookupValueA, hg, hh, Option.map_none']
  | some (.assumption a) =>
      simp only [lookupValue, lookupValueA, hg, hh, eraseDecl,
        Option.map_some', Option.map_none']
  | some (.letBinding a v) =>
      simp only [lookupValue, lookupValueA, hg, hh, eraseDecl,
        Option.map_some', erase_liftA]

/-! ## (1c) the environment twin

`CheckedMember.mtype` is an `Expr Nat`; the probe carried an erasure EQUATION
at every `const` instead of re-typing the environment and reported that as a
cost. M1 pays it here once: members carry annotated types and bodies, and the
tree's environment is the erasure of the twin. -/

structure CheckedMemberA where
  mclass : MemberClass
  arity : Nat
  mtypeA : ExprA
  bodyA : Option ExprA
  /-- the number of leading telescope binders that are PARAMETERS (M2-f (4a)):
      read by the family clause, which fixes them by the carrier (L-RING D2); `0`
      for every member that is not an inductive family. Erased away (main's
      `CheckedMember` keeps parameters in the 05 family view, not the member). -/
  nparamsA : Nat
  /-- a constructor's type with each δ-reached field read as the family application at its indices
      (R-NoDeltaRec-3a): the form ι's analysis reads. `none` is `mtypeA` itself. Erased away. -/
  normA : Option ExprA := none

def eraseMember (m : CheckedMemberA) : CheckedMember :=
  { mclass := m.mclass, arity := m.arity, mtype := erase m.mtypeA,
    body := m.bodyA.map erase }

structure ResolvedEnvA where
  members : Nat → Option CheckedMemberA

def eraseEnv (E : ResolvedEnvA) : ResolvedEnv where
  members := fun r => (E.members r).map eraseMember

theorem members_eraseEnv (E : ResolvedEnvA) (r : Nat) :
    (eraseEnv E).members r = (E.members r).map eraseMember := rfl

def emptyEnvA : ResolvedEnvA where
  members := fun _ => none

theorem members_eraseEnv_empty (r : Nat) :
    (eraseEnv emptyEnvA).members r = emptyEnv.members r := rfl

def extendEnvA (E : ResolvedEnvA) (r : Nat) (m : CheckedMemberA) : ResolvedEnvA where
  members := fun r' => if r' = r then some m else E.members r'

theorem members_eraseEnv_extend (E : ResolvedEnvA) (r : Nat) (m : CheckedMemberA)
    (r' : Nat) :
    (eraseEnv (extendEnvA E r m)).members r'
      = (extendEnv (eraseEnv E) r (eraseMember m)).members r' := by
  simp only [eraseEnv, extendEnvA, extendEnv]
  by_cases h : r' = r
  · simp only [if_pos h, Option.map_some']
  · simp only [if_neg h]

/-- transparency is a property of the class and is unchanged by annotation. -/
theorem transparent_eraseMember (m : CheckedMemberA) :
    transparent (eraseMember m).mclass = transparent m.mclass := rfl

/-! ## (1d) non-vacuity pins and `erase_blind` -/

/-- `Π (x : Sort 0), Sort 0`, annotated: domain sort 1, codomain sort 1. -/
def pinPiA : ExprA := .pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)

example : erase pinPiA = .pi (.sort .zero) (.sort .zero) := rfl

/-- `erase_blind` (I-3e-38): two annotated pis with DIFFERENT domain sorts erase
    to the SAME term — the annotation is information the tree's syntax lacks. -/
def pinPiAlt : ExprA := .pi (.sort .zero) .zero (.sort .zero) (.succ .zero)

theorem erase_blind : erase pinPiA = erase pinPiAlt := rfl

theorem pinPiA_ne_pinPiAlt : pinPiA ≠ pinPiAlt := by decide

/-- `piA_inj`: on the copy, equal pis have equal domain sorts — the datum
    `piP_inj` cannot deliver (I-3e-38). -/
theorem piA_inj {A B A' B' : ExprA} {u v u' v' : Level}
    (h : ExprA.pi A u B v = ExprA.pi A' u' B' v') :
    A = A' ∧ u = u' ∧ B = B' ∧ v = v' := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## de Bruijn scope — `boundOkB` and `liftA`-fixpoints

`boundOkB` moved up from `RcicAnnRecPins` (R-NoDeltaRec-4d): the norm-side closure lemmas
(`envWfA_normClosed`/`normLevels`) need it below `RcicAnnRecView` in the import graph. -/

/-- every de Bruijn index sits strictly under the binders that reach it. -/
def boundOkB (c : Nat) : ExprA → Bool
  | .bvar i => decide (i < c)
  | .sort _ => true
  | .const _ _ => true
  | .app f x => boundOkB c f && boundOkB c x
  | .lam a _ b => boundOkB c a && boundOkB (c + 1) b
  | .pi a _ b _ => boundOkB c a && boundOkB (c + 1) b
  | .letE a w b => boundOkB c a && boundOkB c w && boundOkB (c + 1) b
  | .lit _ => true

theorem liftA_app (c amount : Nat) (f x : ExprA) :
    liftA c amount (.app f x) = .app (liftA c amount f) (liftA c amount x) := rfl

theorem liftA_lam (c amount : Nat) (a : ExprA) (u : Level) (b : ExprA) :
    liftA c amount (.lam a u b) = .lam (liftA c amount a) u (liftA (c + 1) amount b) := rfl

theorem liftA_pi (c amount : Nat) (a : ExprA) (u : Level) (b : ExprA) (v : Level) :
    liftA c amount (.pi a u b v) =
      .pi (liftA c amount a) u (liftA (c + 1) amount b) v := rfl

theorem liftA_letE (c amount : Nat) (a w b : ExprA) :
    liftA c amount (.letE a w b) =
      .letE (liftA c amount a) (liftA c amount w) (liftA (c + 1) amount b) := rfl

theorem liftA_of_boundOkB (amount : Nat) :
    ∀ c e, boundOkB c e = true → liftA c amount e = e
  | c, .bvar i, h => by
      simp only [boundOkB] at h
      simp only [liftA, if_neg (Nat.not_le.mpr (of_decide_eq_true h))]
  | _, .sort _, _ => rfl
  | _, .const _ _, _ => rfl
  | c, .app f x, h => by
      rw [liftA_app, liftA_of_boundOkB amount c f (boolAnd_left h),
        liftA_of_boundOkB amount c x (boolAnd_right h)]
  | c, .lam a u b, h => by
      rw [liftA_lam, liftA_of_boundOkB amount c a (boolAnd_left h),
        liftA_of_boundOkB amount (c + 1) b (boolAnd_right h)]
  | c, .pi a u b v, h => by
      rw [liftA_pi, liftA_of_boundOkB amount c a (boolAnd_left h),
        liftA_of_boundOkB amount (c + 1) b (boolAnd_right h)]
  | c, .letE a w b, h => by
      have hab := boolAnd_left h
      rw [liftA_letE, liftA_of_boundOkB amount c a (boolAnd_left hab),
        liftA_of_boundOkB amount c w (boolAnd_right hab),
        liftA_of_boundOkB amount (c + 1) b (boolAnd_right h)]
  | _, .lit _, _ => rfl

/-- the converse: if lifting at cutoff `c` is the identity, every free `bvar` sits below `c`
    (R-NoDeltaRec-4d-iii — the consumer-side replacement for `map_norm_self`'s collapse). -/
theorem boundOkB_of_liftA : ∀ (c : Nat) (e : ExprA), liftA c 1 e = e → boundOkB c e = true
  | c, .bvar i, h => by
      simp only [liftA] at h
      by_cases hi : c ≤ i
      · simp only [if_pos hi] at h; exact absurd h (by simp)
      · exact decide_eq_true (Nat.lt_of_not_ge hi)
  | _, .sort _, _ => rfl
  | _, .const _ _, _ => rfl
  | c, .app f x, h => by
      rw [liftA_app] at h
      obtain ⟨h1, h2⟩ := ExprA.app.injEq .. ▸ h
      show (boundOkB c f && boundOkB c x) = true
      rw [boundOkB_of_liftA c f h1, boundOkB_of_liftA c x h2]; rfl
  | c, .lam a _ b, h => by
      rw [liftA_lam] at h
      obtain ⟨h1, _, h2⟩ := ExprA.lam.injEq .. ▸ h
      show (boundOkB c a && boundOkB (c + 1) b) = true
      rw [boundOkB_of_liftA c a h1, boundOkB_of_liftA (c + 1) b h2]; rfl
  | c, .pi a _ b _, h => by
      rw [liftA_pi] at h
      obtain ⟨h1, _, h2, _⟩ := ExprA.pi.injEq .. ▸ h
      show (boundOkB c a && boundOkB (c + 1) b) = true
      rw [boundOkB_of_liftA c a h1, boundOkB_of_liftA (c + 1) b h2]; rfl
  | c, .letE a w b, h => by
      rw [liftA_letE] at h
      obtain ⟨h1, h2, h3⟩ := ExprA.letE.injEq .. ▸ h
      show (boundOkB c a && boundOkB c w && boundOkB (c + 1) b) = true
      rw [boundOkB_of_liftA c a h1, boundOkB_of_liftA c w h2, boundOkB_of_liftA (c + 1) b h3]; rfl
  | _, .lit _, _ => rfl

theorem boundOkB_add (k : Nat) :
    ∀ c e, boundOkB c e = true → boundOkB (k + c) e = true
  | c, .bvar i, h => by
      simp only [boundOkB] at h ⊢
      exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) (Nat.le_add_left c k))
  | _, .sort _, _ => rfl
  | _, .const _ _, _ => rfl
  | c, .app f x, h => by
      show (boundOkB (k + c) f && boundOkB (k + c) x) = true
      rw [boundOkB_add k c f (boolAnd_left h), boundOkB_add k c x (boolAnd_right h)]
      rfl
  | c, .lam a _ b, h => by
      show (boundOkB (k + c) a && boundOkB ((k + c) + 1) b) = true
      rw [boundOkB_add k c a (boolAnd_left h), Nat.add_assoc,
        boundOkB_add k (c + 1) b (boolAnd_right h)]
      rfl
  | c, .pi a _ b _, h => by
      show (boundOkB (k + c) a && boundOkB ((k + c) + 1) b) = true
      rw [boundOkB_add k c a (boolAnd_left h), Nat.add_assoc,
        boundOkB_add k (c + 1) b (boolAnd_right h)]
      rfl
  | c, .letE a w b, h => by
      have hab := boolAnd_left h
      show (boundOkB (k + c) a && boundOkB (k + c) w && boundOkB ((k + c) + 1) b) = true
      rw [boundOkB_add k c a (boolAnd_left hab), boundOkB_add k c w (boolAnd_right hab),
        Nat.add_assoc, boundOkB_add k (c + 1) b (boolAnd_right h)]
      rfl
  | _, .lit _, _ => rfl

#print axioms erase_liftA
#print axioms erase_instantiateA
#print axioms erase_instantiateLevelsA
#print axioms lookupType_eraseCtx
#print axioms lookupValue_eraseCtx
#print axioms members_eraseEnv_extend
#print axioms erase_blind
#print axioms piA_inj
#print axioms boundOkB_add
#print axioms liftA_of_boundOkB

end Rcic.Declarative.Ann
