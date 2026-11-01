import rcic.RcicEGTypedAccept

/-!
Shared singleton admission producers, extracted from RcicGraphAdmittedBlind §5.
Definitions keep their original names and bodies. Both graph admission and the
Lean importer consume this one module; no duplicate admission predicate exists.
The target rules remain EG010T_*_accepted. closure_claim = 0.
-/
namespace Rcic.GraphAdmitted.Blind
open Rcic.Declarative Rcic.Machine

/-- `o.isNone = true` gives `o = none`. -/
theorem isNone_eq_none {α : Type} {o : Option α} (h : o.isNone = true) : o = none := by
  cases o with
  | none => rfl
  | some _ => cases h

/-- One singleton declaration step (04 §6): the four non-group member classes
    (`axiomM`, `definitionM`, `theoremM`, `opaqueM`) together with the machine
    step budgets at which `typedRun` checks their type and body. -/
inductive SingletonDecl where
  | axiomD (r : Nat) (k : Nat) (A : Expr Nat)
  | definitionD (r : Nat) (k k' : Nat) (A v : Expr Nat)
  | theoremD (r : Nat) (k k' : Nat) (A p : Expr Nat)
  | opaqueD (r : Nat) (k k' : Nat) (A v : Expr Nat)
  deriving DecidableEq

/-- Extend `E` by one singleton declaration. -/
def applySingleton (E : ResolvedEnv) : SingletonDecl → ResolvedEnv
  | .axiomD r _ A => extendEnv E r ⟨.axiomM, 0, A, none⟩
  | .definitionD r _ _ A v => extendEnv E r ⟨.definitionM, 0, A, some v⟩
  | .theoremD r _ _ A p => extendEnv E r ⟨.theoremM, 0, A, some p⟩
  | .opaqueD r _ _ A v => extendEnv E r ⟨.opaqueM, 0, A, some v⟩

/-- Extend `E` left-to-right across a telescope of singleton declarations. -/
def applySingletons (E : ResolvedEnv) : List SingletonDecl → ResolvedEnv
  | [] => E
  | d :: ds => applySingletons (applySingleton E d) ds

/-- Executable Bool typing check for one singleton declaration over the REAL
    typed machine (`typedRun` via `inferSortAcceptedB` and `checkAcceptedB`
    from `RcicEGTypedAccept`), plus freshness, closedness (`lift 0 1 X = X`),
    and level bounds (`exprLevelsBounded 0 X`). -/
def admitSingletonB (E : ResolvedEnv) : SingletonDecl → Bool
  | .axiomD r k A =>
      (E.members r).isNone &&
      inferSortAcceptedB E k A &&
      decide (lift 0 1 A = A) &&
      exprLevelsBounded 0 A
  | .definitionD r k k' A v =>
      (E.members r).isNone &&
      inferSortAcceptedB E k A &&
      checkAcceptedB E k' v A &&
      decide (lift 0 1 A = A) &&
      decide (lift 0 1 v = v) &&
      exprLevelsBounded 0 A &&
      exprLevelsBounded 0 v
  | .theoremD r k k' A p =>
      (E.members r).isNone &&
      checkAcceptedB E k A (.sort .zero) &&
      checkAcceptedB E k' p A &&
      decide (lift 0 1 A = A) &&
      decide (lift 0 1 p = p) &&
      exprLevelsBounded 0 A &&
      exprLevelsBounded 0 p
  | .opaqueD r k k' A v =>
      (E.members r).isNone &&
      inferSortAcceptedB E k A &&
      checkAcceptedB E k' v A &&
      decide (lift 0 1 A = A) &&
      decide (lift 0 1 v = v) &&
      exprLevelsBounded 0 A &&
      exprLevelsBounded 0 v

/-- Executable Bool typing stage for a telescope of singleton declarations,
    threading the extended environment left-to-right. -/
def admitSingletonsB : ResolvedEnv → List SingletonDecl → Bool
  | _, [] => true
  | E, d :: ds => admitSingletonB E d && admitSingletonsB (applySingleton E d) ds

/-- Soundness of one singleton step: `admitSingletonB E d = true` constructs
    the `EnvWfT` successor from the machine runs (`EG010T_*_accepted`). -/
def admitSingletonWfT {E : ResolvedEnv} (hE : EnvWfT E) :
    (d : SingletonDecl) → admitSingletonB E d = true →
    EnvWfT (applySingleton E d)
  | .axiomD r k A, h => by
      simp only [admitSingletonB, Bool.and_eq_true] at h
      exact EG010T_axiom_accepted hE (isNone_eq_none h.1.1.1) h.1.1.2
        (of_decide_eq_true h.1.2) h.2
  | .definitionD r k k' A v, h => by
      simp only [admitSingletonB, Bool.and_eq_true] at h
      exact EG010T_definition_accepted hE (isNone_eq_none h.1.1.1.1.1.1)
        h.1.1.1.1.1.2 h.1.1.1.1.2
        (of_decide_eq_true h.1.1.1.2) (of_decide_eq_true h.1.1.2) h.1.2 h.2
  | .theoremD r k k' A p, h => by
      simp only [admitSingletonB, Bool.and_eq_true] at h
      exact EG010T_theorem_accepted hE (isNone_eq_none h.1.1.1.1.1.1)
        h.1.1.1.1.1.2 h.1.1.1.1.2
        (of_decide_eq_true h.1.1.1.2) (of_decide_eq_true h.1.1.2) h.1.2 h.2
  | .opaqueD r k k' A v, h => by
      simp only [admitSingletonB, Bool.and_eq_true] at h
      exact EG010T_opaque_accepted hE (isNone_eq_none h.1.1.1.1.1.1)
        h.1.1.1.1.1.2 h.1.1.1.1.2
        (of_decide_eq_true h.1.1.1.2) (of_decide_eq_true h.1.1.2) h.1.2 h.2

/-- Soundness of the telescope typing stage: `admitSingletonsB E ds = true`
    constructs the composite `EnvWfT (applySingletons E ds)`. -/
def admitSingletonsWfT {E : ResolvedEnv} (hE : EnvWfT E) :
    (ds : List SingletonDecl) → admitSingletonsB E ds = true →
    EnvWfT (applySingletons E ds)
  | [], _ => hE
  | d :: ds, h => by
      simp only [admitSingletonsB, Bool.and_eq_true] at h
      exact admitSingletonsWfT (admitSingletonWfT hE d h.1) ds h.2

/-- Prop-level soundness of the singleton typing stage. -/
theorem admitSingletons_sound {E : ResolvedEnv} (hE : EnvWfT E)
    {ds : List SingletonDecl} (h : admitSingletonsB E ds = true) :
    Nonempty (EnvWfT (applySingletons E ds)) :=
  ⟨admitSingletonsWfT hE ds h⟩

#print axioms admitSingletonWfT
#print axioms admitSingletonsWfT
end Rcic.GraphAdmitted.Blind
