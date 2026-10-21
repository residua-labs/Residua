import rcic.RcicNativeTypedModelCovROpaqueArrow

/-!
# A finite lexical type template with opaque candidate variables

This is a displayed normal-type fragment, not an evaluator for arbitrary
native type-level applications. Ordinary arrows retain a fixed semantic
row and recurse into their two finite syntax children. Only sort binders
quantify over predicates; a bound type variable returns its valuation
entry without unfolding that predicate or its native type.

Every interpretation of this syntax is proved to be a candidate. This is
candidate adequacy for every represented fixed template, not a general
native fundamental theorem or a normalization assumption. A separate
native readback certificate is required to use a template for another type.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovPAudit ReadbackCK2Audit

/-- Closed atomic native heads and the nondependent ordinary-arrow fragment
are enough for the requested towers. Ordinary dependent family application
is intentionally not an opaque fallback constructor. -/
inductive CovRSyntax (E : ResolvedEnv) : Type where
  | prop
  | sort
  | atom (r : Nat) (notProp : ¬ IsPropCTP E (.spine r []))
  | var (i : Nat)
  | arrow (domain codomain : CovRSyntax E)
  | allProp (body : CovRSyntax E)
  | allSort (u : Level) (body : CovRSyntax E)

/-- The valuation stores both the actual native type and its relation. -/
structure CovRVal where
  native : Nat → Expr Nat
  relation : Nat → CovRRel

def covRCons {α : Type} (x : α) (xs : Nat → α) : Nat → α
  | 0 => x
  | i + 1 => xs i

def CovRVal.cons (T : Expr Nat) (S : CovRRel) (v : CovRVal) : CovRVal :=
  ⟨covRCons T v.native, covRCons S v.relation⟩

/-- Sort 0 binds a positive proposition; a successor sort binds a data
candidate. Tags of ordinary arrows are their codomain tags. -/
def covRTag {E : ResolvedEnv} (t : CovRSyntax E) (sig : Nat → Bool) : Bool :=
  match t with
  | .prop | .sort | .atom _ _ => false
  | .var i => sig i
  | .arrow _ B => covRTag B sig
  | .allProp B => covRTag B (covRCons true sig)
  | .allSort _ B => covRTag B (covRCons false sig)

/-- Reification is lexical. Entering an ordinary arrow shifts its closed
codomain expression; entering a type binder introduces native bvar 0. -/
def covRNative {E : ResolvedEnv} (t : CovRSyntax E) (σ : Nat → Expr Nat) : Expr Nat :=
  match t with
  | .prop => .sort .zero
  | .sort => .sort (.succ .zero)
  | .atom r _ => .const r []
  | .var i => σ i
  | .arrow D B => .pi (covRNative D σ) (lift 0 1 (covRNative B σ))
  | .allProp B => .pi (.sort .zero)
      (covRNative B (covRCons (.bvar 0) (fun i => lift 0 1 (σ i))))
  | .allSort u B => .pi (.sort (.succ u))
      (covRNative B (covRCons (.bvar 0) (fun i => lift 0 1 (σ i))))

def CovRValValid (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (sig : Nat → Bool) (v : CovRVal) : Prop :=
  ∀ i, CandidateCov E (WhStepCK2 E n) Γ (sig i) (v.relation i)

theorem covRVal_cons_valid {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {sig : Nat → Bool} {v : CovRVal} {p : Bool} {S : CovRRel}
    (hS : CandidateCov E (WhStepCK2 E n) Γ p S)
    (hv : CovRValValid E n Γ sig v) (T : Expr Nat) :
    CovRValValid E n Γ (covRCons p sig) (v.cons T S) := by
  intro i
  cases i with
  | zero => exact hS
  | succ i => exact hv i

/-- Only a variable supplied by the semantic valuation uses the opaque
domain rule. A concrete ordinary domain keeps the stored-row gate. -/
def covRDomainOpaque {E : ResolvedEnv} (D : CovRSyntax E) : Bool :=
  match D with
  | .var _ => true
  | _ => false

def covRArrowAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (opaqueDomain positive : Bool) (Dty : Expr Nat) (D B : CovRRel) : CovRRel :=
  if opaqueDomain then covROpaqueArrow E n Γ positive Dty D B
  else covRArrow E n Γ positive Dty D B

theorem covRArrowAt_isCandidate {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {p q : Bool} {Dty : Expr Nat} {D B : CovRRel}
    (opaqueDomain : Bool)
    (hD : CandidateCov E (WhStepCK2 E n) Γ p D)
    (hB : CandidateCov E (WhStepCK2 E n) Γ q B) :
    CandidateCov E (WhStepCK2 E n) Γ q
      (covRArrowAt E n Γ opaqueDomain q Dty D B) := by
  cases opaqueDomain with
  | false => exact covRArrow_isCandidate hD hB
  | true => exact covROpaqueArrow_isCandidate hD hB

/-- Lean accepts structural recursion on the finite lexical template. The
candidate quantifier occurs in Prop and the variable case is a lookup. -/
def covRInterpret (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (t : CovRSyntax E) (sig : Nat → Bool) (v : CovRVal) : CovRRel :=
  match t with
  | .prop => covRCodeRel E .prop
  | .sort => covRCodeRel E .sort
  | .atom r _ => covRCodeRel E (.spine r [])
  | .var i => v.relation i
  | .arrow D B => covRArrowAt E n Γ (covRDomainOpaque D)
      (covRTag B sig) (covRNative D v.native)
      (covRInterpret E n Γ D sig v) (covRInterpret E n Γ B sig v)
  | .allProp B => covRForall E n Γ .zero true (covRTag B (covRCons true sig))
      (fun T S => covRInterpret E n Γ B (covRCons true sig) (v.cons T S))
  | .allSort u B => covRForall E n Γ (.succ u) false
      (covRTag B (covRCons false sig))
      (fun T S => covRInterpret E n Γ B (covRCons false sig) (v.cons T S))

theorem covRInterpret_var (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (i : Nat) (sig : Nat → Bool) (v : CovRVal) :
    covRInterpret E n Γ (.var i) sig v = v.relation i := rfl

theorem covRInterpret_bound_var (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (sig : Nat → Bool) (v : CovRVal) (p : Bool) (T : Expr Nat) (S : CovRRel) :
    covRInterpret E n Γ (.var 0) (covRCons p sig) (v.cons T S) = S := rfl

/-- Actual candidate adequacy for every fixed template, including a
universally quantified sort binder with an arbitrary valid input candidate. -/
theorem covRInterpret_isCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (t : CovRSyntax E) (sig : Nat → Bool) (v : CovRVal)
    (hv : CovRValValid E n Γ sig v) :
    CandidateCov E (WhStepCK2 E n) Γ (covRTag t sig)
      (covRInterpret E n Γ t sig v) := by
  induction t generalizing sig v with
  | prop => exact covRProp_isCandidate E _ Γ
  | sort => exact covRSort_isCandidate E _ Γ
  | atom r hn => exact covRSpine_isCandidate E _ Γ r [] hn
  | var i => exact hv i
  | arrow D B ihD ihB =>
      exact covRArrowAt_isCandidate _ (ihD sig v hv) (ihB sig v hv)
  | allProp B ih =>
      apply covRForall_isCandidate
      intro T S hS
      exact ih _ _ (covRVal_cons_valid hS hv T)
  | allSort u B ih =>
      apply covRForall_isCandidate
      intro T S hS
      exact ih _ _ (covRVal_cons_valid hS hv T)

/-- The free valuation has an explicit native and semantic inhabitant. -/
def covRBaseVal (E : ResolvedEnv) : CovRVal :=
  ⟨fun _ => .sort .zero, fun _ => covRCodeRel E .prop⟩

theorem covRBaseVal_valid (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovRValValid E n Γ (fun _ => false) (covRBaseVal E) :=
  fun _ => covRProp_isCandidate E _ Γ

/-- This fresh joint target contains only the new interpretation. The two
self-related endpoint witnesses are derived from its PER, not from CoreY. -/
def CovRJoint (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (t : CovRSyntax E) (sig : Nat → Bool) (v : CovRVal)
    (x y : Expr Nat) (c : CptT) : Prop :=
  covRInterpret E n Γ t sig v x y c ∧
  covRInterpret E n Γ t sig v x x c ∧
  covRInterpret E n Γ t sig v y y c

theorem covRJoint_of_related (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (t : CovRSyntax E) (sig : Nat → Bool) (v : CovRVal)
    (hv : CovRValValid E n Γ sig v) {x y : Expr Nat} {c : CptT}
    (h : covRInterpret E n Γ t sig v x y c) :
    CovRJoint E n Γ t sig v x y c := by
  have hc := covRInterpret_isCandidate E n Γ t sig v hv
  exact ⟨h, hc.self_left h, hc.self_right h⟩

/-- Fixed semantic type and valuation: no code join is needed. This does
not supply transitivity across different type templates or valuations. -/
theorem covRJoint_trans (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (t : CovRSyntax E) (sig : Nat → Bool) (v : CovRVal)
    (hv : CovRValValid E n Γ sig v) {x y z : Expr Nat} {c : CptT}
    (hxy : CovRJoint E n Γ t sig v x y c)
    (hyz : CovRJoint E n Γ t sig v y z c) :
    CovRJoint E n Γ t sig v x z c :=
  covRJoint_of_related E n Γ t sig v hv
    ((covRInterpret_isCandidate E n Γ t sig v hv).trans hxy.1 hyz.1)

/-- A template may be used for a native type after an actual normal
readback certificate. This is a boundary interface, not a readback supply. -/
def CovRTemplateWellFormed {E : ResolvedEnv} (t : CovRSyntax E) : Prop :=
  match t with
  | .prop | .sort | .atom _ _ | .var _ => True
  | .arrow D B =>
      (match D with | .prop | .sort => False | _ => True) ∧
      CovRTemplateWellFormed D ∧ CovRTemplateWellFormed B
  | .allProp B | .allSort _ B => CovRTemplateWellFormed B

def CovRNativeView (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A : Expr Nat) (t : CovRSyntax E) (v : CovRVal) : Prop :=
  CovRTemplateWellFormed t ∧
  RedR (WhStepCK2 E n) Γ A (covRNative t v.native) ∧
  NormalR (WhStepCK2 E n) Γ (covRNative t v.native)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_R_SYNTAX_ROOTS
#print axioms CovRSyntax
#print axioms CovRVal
#print axioms covRCons
#print axioms CovRVal.cons
#print axioms covRTag
#print axioms covRNative
#print axioms CovRValValid
#print axioms covRVal_cons_valid
#print axioms covRDomainOpaque
#print axioms covRArrowAt
#print axioms covRArrowAt_isCandidate
#print axioms covRInterpret
#print axioms covRInterpret_var
#print axioms covRInterpret_bound_var
#print axioms covRInterpret_isCandidate
#print axioms covRBaseVal
#print axioms covRBaseVal_valid
#print axioms CovRJoint
#print axioms covRJoint_of_related
#print axioms covRJoint_trans
#print axioms CovRTemplateWellFormed
#print axioms CovRNativeView
-- END RCIC_NATIVE_TYPED_MODEL_COV_R_SYNTAX_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRAudit
