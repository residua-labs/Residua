import rcic.RcicF3RecFieldOriginSyntax
import rcic.RcicF3RecFieldOriginCases
import rcic.RcicF3DTransfer

/-!
# The bounded recursive-local masking relation

A syntactic mode fixes the remaining recursive depth before semantic
arguments are supplied. Ordinary locals have mode none; recursive locals
carry their actual reader depth. Application consumes one level from its
head's mode, and a lambda adds one level to its body's fixed mode.

The relation compares an original assignment with a masked assignment in
the source model. Its Origin evidence compares the two actual family
models at the SAME original assignment. Only that original assignment is
later required to fit. The masked assignment is not asserted to fit.

These definitions are an internal induction interface. They are not an
admission-to-mask theorem or an additional premise of the checked apex.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMask
open Rcic.Declarative RawFamily RecFieldOrigin

abbrev Marks := Nat → Option Nat

/-- A binder introduced by the syntax receives the same ordinary value in
the two local assignments, rather than a newly selected recursive value. -/
def ordinary (marks : Marks) : Marks
  | 0 => none
  | i + 1 => marks i

/-- The alternative and recursive depth do not vary with a reached
semantic argument. The typing induction must prove the selected case. -/
def mode (marks : Marks) : Expr Nat → Option Nat
  | .bvar i => marks i
  | .sort _ => none
  | .const _ _ => none
  | .app f _ => (mode marks f).map (fun m => m - 1)
  | .lam _ body => (mode (ordinary marks) body).map (fun m => m + 1)
  | .pi _ _ => none
  | .letE _ _ body => mode (ordinary marks) body
  | .lit _ => none

/-- Type-set information is needed only in the recursive-origin case. -/
def Value (M : Interp.{4}) (fd : FamData) (C : Frame)
    (q : Option Nat) (S T z masked : PSet.{4}) : Prop :=
  match q with
  | none => Equiv z masked
  | some m => Equiv masked pempty ∧ Origin M fd C m S T z

/-- The two models see the same original local assignment. -/
def Holds (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (ρ η : Nat → PSet.{4}) (e A : Expr Nat) : Prop :=
  Value (mkM P μ) fd C (mode marks e)
    (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρ A))
    (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
      (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ A))
    (den (mkM P (table P μ fd C)) σ ρ e)
    (den (mkM P (table P μ fd C)) σ η e)

/-- The actual lookup type is retained at every recursive local. This
relation imposes no typing or fit condition on the masked assignment. -/
def Context (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (Γ : LCtx) (ρ η : Nat → PSet.{4}) : Prop :=
  ∀ i A, lookupType Γ i = some A →
    Value (mkM P μ) fd C (marks i)
      (Ed (mkM P (table P μ fd C)) (den (mkM P (table P μ fd C)) σ ρ A))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρ A))
      (ρ i) (η i)

theorem Value.transport {M : Interp.{4}} {fd : FamData} {C : Frame}
    {q : Option Nat} {S T z masked S' T' z' masked' : PSet.{4}}
    (h : Value M fd C q S T z masked)
    (hS : Equiv S S') (hT : Equiv T T')
    (hz : Equiv z z') (hm : Equiv masked masked') :
    Value M fd C q S' T' z' masked' := by
  cases q with
  | none => exact hz.symm.trans (h.trans hm)
  | some m => exact ⟨hm.symm.trans h.1, h.2.transport hS hT hz⟩

/-- The variable case is the literal lookup component of the relation. -/
theorem bvar (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (Γ : LCtx) (ρ η : Nat → PSet.{4})
    (h : Context P μ fd C σ marks Γ ρ η)
    (i : Nat) (A : Expr Nat) (hi : lookupType Γ i = some A) :
    Holds P μ fd C σ marks ρ η (.bvar i) A := h i A hi

/-- Actual bounded typehood rules out the recursive-origin alternative.
The resulting denotation equality is at the original and masked values,
with no soundness invocation at the masked assignment. -/
theorem typed_type (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (marks : Marks) (ρ η : Nat → PSet.{4})
    (hρ : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    {e : Expr Nat} {l : Level}
    (d : HasTyT E n Γ e (.sort l)) (hd : LOKt σ 4 K d)
    (h : Holds P μ fd C σ marks ρ η e (.sort l)) :
    Equiv (den (mkM P (table P μ fd C)) σ ρ e)
      (den (mkM P (table P μ fd C)) σ η e) := by
  cases hm : mode marks e with
  | none => simpa only [Holds, Value, hm] using h
  | some m =>
      have ho := (show Equiv (den (mkM P (table P μ fd C)) σ η e) pempty ∧
          Origin (mkM P μ) fd C m
            (Ed (mkM P (table P μ fd C))
              (den (mkM P (table P μ fd C)) σ ρ (.sort l)))
            (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
              (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
                σ ρ (.sort l)))
            (den (mkM P (table P μ fd C)) σ ρ e) from by
        simpa only [Holds, Value, hm] using h).2
      exact (RecFieldOriginCases.sort_exclusion P μ fd C σ K hE ρ hρ d hd ho).elim

end Rcic.F3.PSet.RecFieldMask
