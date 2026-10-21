import rcic.RcicNativeTypedModelCovWMatrixCore

/-!
# Raw observation equality is a congruence; literal conversion preserves it

Equality here quantifies over every valuation and every tagged compact.
Constructor inversion and reconstruction preserve the exact observations,
including the compact-dependent typing and proof-position side conditions.
This stronger relation descends to erased observations and to the shared
type-code invariant. It concerns only `ApproxTWIrrel`.

The syntax contexts below describe holes at their own binder depth. Since
literal expansions are closed, the literal context theorem is independent
of any convention for lifting an open expression when filling a hole.
No guarded congruence, native confluence, or normalization is assumed.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovWIrrelAudit

def CovWMatrixRawEq (E : ResolvedEnv) (n : Nat) (left right : Expr Nat) : Prop :=
  ∀ ρ c, ApproxTWIrrel E n ρ left c ↔ ApproxTWIrrel E n ρ right c

theorem covWMatrix_raw_eq_refl (E : ResolvedEnv) (n : Nat) (e : Expr Nat) :
    CovWMatrixRawEq E n e e := fun _ _ => Iff.rfl

theorem covWMatrix_raw_eq_symm {E : ResolvedEnv} {n : Nat} {left right : Expr Nat}
    (h : CovWMatrixRawEq E n left right) : CovWMatrixRawEq E n right left :=
  fun ρ c => (h ρ c).symm

theorem covWMatrix_raw_eq_trans {E : ResolvedEnv} {n : Nat}
    {left middle right : Expr Nat}
    (h₁ : CovWMatrixRawEq E n left middle) (h₂ : CovWMatrixRawEq E n middle right) :
    CovWMatrixRawEq E n left right := fun ρ c => (h₁ ρ c).trans (h₂ ρ c)

theorem covWMatrix_raw_app_congr {E : ResolvedEnv} {n : Nat}
    {f f' a a' : Expr Nat} (hf : CovWMatrixRawEq E n f f')
    (ha : CovWMatrixRawEq E n a a') :
    CovWMatrixRawEq E n (.app f a) (.app f' a') := by
  intro ρ c
  constructor
  · intro h
    cases h with
    | bot => exact .bot _ _
    | app hfun hs harg =>
        exact .app ((hf _ _).mp hfun) hs (fun u hu => (ha _ _).mp (harg u hu))
    | appSpine hfun harg hslot =>
        exact .appSpine ((hf _ _).mp hfun) ((ha _ _).mp harg) hslot
  · intro h
    cases h with
    | bot => exact .bot _ _
    | app hfun hs harg =>
        exact .app ((hf _ _).mpr hfun) hs (fun u hu => (ha _ _).mpr (harg u hu))
    | appSpine hfun harg hslot =>
        exact .appSpine ((hf _ _).mpr hfun) ((ha _ _).mpr harg) hslot

theorem covWMatrix_raw_lam_congr {E : ResolvedEnv} {n : Nat}
    {A A' b b' : Expr Nat} (hA : CovWMatrixRawEq E n A A')
    (hb : CovWMatrixRawEq E n b b') :
    CovWMatrixRawEq E n (.lam A b) (.lam A' b') := by
  intro ρ c
  constructor
  · intro h
    cases h with
    | bot => exact .bot _ _
    | lam hdom ht hne hbody =>
        exact .lam ((hA _ _).mp hdom) ht hne (fun s hs => (hb _ _).mp (hbody s hs))
  · intro h
    cases h with
    | bot => exact .bot _ _
    | lam hdom ht hne hbody =>
        exact .lam ((hA _ _).mpr hdom) ht hne (fun s hs => (hb _ _).mpr (hbody s hs))

theorem covWMatrix_raw_pi_congr {E : ResolvedEnv} {n : Nat}
    {A A' B B' : Expr Nat} (hA : CovWMatrixRawEq E n A A')
    (hB : CovWMatrixRawEq E n B B') :
    CovWMatrixRawEq E n (.pi A B) (.pi A' B') := by
  intro ρ c
  constructor
  · intro h
    cases h with
    | bot => exact .bot _ _
    | pi hdom ht hbody =>
        exact .pi ((hA _ _).mp hdom) ht (fun s hs => (hB _ _).mp (hbody s hs))
  · intro h
    cases h with
    | bot => exact .bot _ _
    | pi hdom ht hbody =>
        exact .pi ((hA _ _).mpr hdom) ht (fun s hs => (hB _ _).mpr (hbody s hs))

/-- Let is observed through its displayed lambda application. This is not zeta. -/
theorem covWMatrix_raw_let_desugar (E : ResolvedEnv) (n : Nat) (A v b : Expr Nat) :
    CovWMatrixRawEq E n (.letE A v b) (.app (.lam A b) v) := by
  intro ρ c
  constructor
  · intro h
    cases h with
    | bot => exact .bot _ _
    | letE h => exact h
  · exact ApproxTWIrrel.letE

theorem covWMatrix_raw_let_congr {E : ResolvedEnv} {n : Nat}
    {A A' v v' b b' : Expr Nat} (hA : CovWMatrixRawEq E n A A')
    (hv : CovWMatrixRawEq E n v v') (hb : CovWMatrixRawEq E n b b') :
    CovWMatrixRawEq E n (.letE A v b) (.letE A' v' b') :=
  covWMatrix_raw_eq_trans (covWMatrix_raw_let_desugar E n A v b)
    (covWMatrix_raw_eq_trans (covWMatrix_raw_app_congr (covWMatrix_raw_lam_congr hA hb) hv)
      (covWMatrix_raw_eq_symm (covWMatrix_raw_let_desugar E n A' v' b')))

theorem covWMatrix_raw_app_function_congr {E : ResolvedEnv} {n : Nat}
    {f f' : Expr Nat} (a : Expr Nat) (h : CovWMatrixRawEq E n f f') :
    CovWMatrixRawEq E n (.app f a) (.app f' a) :=
  covWMatrix_raw_app_congr h (covWMatrix_raw_eq_refl E n a)

theorem covWMatrix_raw_app_argument_congr {E : ResolvedEnv} {n : Nat}
    {a a' : Expr Nat} (f : Expr Nat) (h : CovWMatrixRawEq E n a a') :
    CovWMatrixRawEq E n (.app f a) (.app f a') :=
  covWMatrix_raw_app_congr (covWMatrix_raw_eq_refl E n f) h

theorem covWMatrix_raw_lam_annotation_congr {E : ResolvedEnv} {n : Nat}
    {A A' : Expr Nat} (b : Expr Nat) (h : CovWMatrixRawEq E n A A') :
    CovWMatrixRawEq E n (.lam A b) (.lam A' b) :=
  covWMatrix_raw_lam_congr h (covWMatrix_raw_eq_refl E n b)

theorem covWMatrix_raw_lam_body_congr {E : ResolvedEnv} {n : Nat}
    {b b' : Expr Nat} (A : Expr Nat) (h : CovWMatrixRawEq E n b b') :
    CovWMatrixRawEq E n (.lam A b) (.lam A b') :=
  covWMatrix_raw_lam_congr (covWMatrix_raw_eq_refl E n A) h

theorem covWMatrix_raw_pi_domain_congr {E : ResolvedEnv} {n : Nat}
    {A A' : Expr Nat} (B : Expr Nat) (h : CovWMatrixRawEq E n A A') :
    CovWMatrixRawEq E n (.pi A B) (.pi A' B) :=
  covWMatrix_raw_pi_congr h (covWMatrix_raw_eq_refl E n B)

theorem covWMatrix_raw_pi_codomain_congr {E : ResolvedEnv} {n : Nat}
    {B B' : Expr Nat} (A : Expr Nat) (h : CovWMatrixRawEq E n B B') :
    CovWMatrixRawEq E n (.pi A B) (.pi A B') :=
  covWMatrix_raw_pi_congr (covWMatrix_raw_eq_refl E n A) h

theorem covWMatrix_raw_let_annotation_congr {E : ResolvedEnv} {n : Nat}
    {A A' : Expr Nat} (v b : Expr Nat) (h : CovWMatrixRawEq E n A A') :
    CovWMatrixRawEq E n (.letE A v b) (.letE A' v b) :=
  covWMatrix_raw_let_congr h (covWMatrix_raw_eq_refl E n v) (covWMatrix_raw_eq_refl E n b)

theorem covWMatrix_raw_let_value_congr {E : ResolvedEnv} {n : Nat}
    {v v' : Expr Nat} (A b : Expr Nat) (h : CovWMatrixRawEq E n v v') :
    CovWMatrixRawEq E n (.letE A v b) (.letE A v' b) :=
  covWMatrix_raw_let_congr (covWMatrix_raw_eq_refl E n A) h (covWMatrix_raw_eq_refl E n b)

theorem covWMatrix_raw_let_body_congr {E : ResolvedEnv} {n : Nat}
    {b b' : Expr Nat} (A v : Expr Nat) (h : CovWMatrixRawEq E n b b') :
    CovWMatrixRawEq E n (.letE A v b) (.letE A v b') :=
  covWMatrix_raw_let_congr (covWMatrix_raw_eq_refl E n A) (covWMatrix_raw_eq_refl E n v) h

/-- Every raw derivation of a literal is bottom or its expansion derivation. -/
theorem covWMatrix_raw_literal_eq (E : ResolvedEnv) (n t : Nat) :
    CovWMatrixRawEq E n (.lit t) (natExpand t) := by
  intro ρ c
  constructor
  · intro h
    cases h with
    | bot => exact .bot _ _
    | lit h => exact h
  · exact ApproxTWIrrel.lit

inductive CovWMatrixRawContext : Type
  | hole
  | appFunction (inner : CovWMatrixRawContext) (arg : Expr Nat)
  | appArgument (fn : Expr Nat) (inner : CovWMatrixRawContext)
  | lamAnnotation (inner : CovWMatrixRawContext) (body : Expr Nat)
  | lamBody (domain : Expr Nat) (inner : CovWMatrixRawContext)
  | piDomain (inner : CovWMatrixRawContext) (body : Expr Nat)
  | piCodomain (domain : Expr Nat) (inner : CovWMatrixRawContext)
  | letAnnotation (inner : CovWMatrixRawContext) (value body : Expr Nat)
  | letValue (domain : Expr Nat) (inner : CovWMatrixRawContext) (body : Expr Nat)
  | letBody (domain value : Expr Nat) (inner : CovWMatrixRawContext)

def covWMatrixRawFill (C : CovWMatrixRawContext) (e : Expr Nat) : Expr Nat :=
  match C with
  | .hole => e
  | .appFunction D a => .app (covWMatrixRawFill D e) a
  | .appArgument f D => .app f (covWMatrixRawFill D e)
  | .lamAnnotation D b => .lam (covWMatrixRawFill D e) b
  | .lamBody A D => .lam A (covWMatrixRawFill D e)
  | .piDomain D B => .pi (covWMatrixRawFill D e) B
  | .piCodomain A D => .pi A (covWMatrixRawFill D e)
  | .letAnnotation D v b => .letE (covWMatrixRawFill D e) v b
  | .letValue A D b => .letE A (covWMatrixRawFill D e) b
  | .letBody A v D => .letE A v (covWMatrixRawFill D e)

theorem covWMatrix_raw_context_congr {E : ResolvedEnv} {n : Nat}
    {left right : Expr Nat} (C : CovWMatrixRawContext) (h : CovWMatrixRawEq E n left right) :
    CovWMatrixRawEq E n (covWMatrixRawFill C left) (covWMatrixRawFill C right) := by
  induction C with
  | hole => exact h
  | appFunction C a ih => exact covWMatrix_raw_app_function_congr a ih
  | appArgument f C ih => exact covWMatrix_raw_app_argument_congr f ih
  | lamAnnotation C b ih => exact covWMatrix_raw_lam_annotation_congr b ih
  | lamBody A C ih => exact covWMatrix_raw_lam_body_congr A ih
  | piDomain C B ih => exact covWMatrix_raw_pi_domain_congr B ih
  | piCodomain A C ih => exact covWMatrix_raw_pi_codomain_congr A ih
  | letAnnotation C v b ih => exact covWMatrix_raw_let_annotation_congr v b ih
  | letValue A C b ih => exact covWMatrix_raw_let_value_congr A b ih
  | letBody A v C ih => exact covWMatrix_raw_let_body_congr A v ih

theorem covWMatrix_raw_literal_context_eq (E : ResolvedEnv) (n t : Nat)
    (C : CovWMatrixRawContext) :
    CovWMatrixRawEq E n (covWMatrixRawFill C (.lit t)) (covWMatrixRawFill C (natExpand t)) :=
  covWMatrix_raw_context_congr C (covWMatrix_raw_literal_eq E n t)

theorem covWMatrix_raw_eq_erased {E : ResolvedEnv} {n : Nat} {left right : Expr Nat}
    (h : CovWMatrixRawEq E n left right) (ρ : EnvWIrrel) (c : CptT) :
    CovWIrrelRawObservation E n ρ left c ↔ CovWIrrelRawObservation E n ρ right c := by
  constructor
  · rintro ⟨d, hd, ho⟩
    exact ⟨d, hd, (h ρ d).mp ho⟩
  · rintro ⟨d, hd, ho⟩
    exact ⟨d, hd, (h ρ d).mpr ho⟩

theorem covWMatrix_raw_eq_typed_invariant {E : ResolvedEnv} {n : Nat}
    {left right : Expr Nat} (h : CovWMatrixRawEq E n left right)
    (ρ : EnvWIrrel) (A : Expr Nat) :
    CovWMatrixRawTypedInvariant E n ρ A left right :=
  fun _ c _ _ => covWMatrix_raw_eq_erased h ρ c

/-- The raw literal-conversion row under every finite displayed context.
The type code is any actual observation of the supplied type expression. -/
theorem covWMatrix_raw_literal_context_invariant (E : ResolvedEnv) (n t : Nat)
    (C : CovWMatrixRawContext) (ρ : EnvWIrrel) (A : Expr Nat) :
    CovWMatrixRawTypedInvariant E n ρ A
      (covWMatrixRawFill C (.lit t)) (covWMatrixRawFill C (natExpand t)) :=
  covWMatrix_raw_eq_typed_invariant (covWMatrix_raw_literal_context_eq E n t C) ρ A

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_RAW_CONGRUENCE_ROOTS
#print axioms CovWMatrixRawEq
#print axioms covWMatrix_raw_eq_refl
#print axioms covWMatrix_raw_eq_symm
#print axioms covWMatrix_raw_eq_trans
#print axioms covWMatrix_raw_app_congr
#print axioms covWMatrix_raw_lam_congr
#print axioms covWMatrix_raw_pi_congr
#print axioms covWMatrix_raw_let_desugar
#print axioms covWMatrix_raw_let_congr
#print axioms covWMatrix_raw_app_function_congr
#print axioms covWMatrix_raw_app_argument_congr
#print axioms covWMatrix_raw_lam_annotation_congr
#print axioms covWMatrix_raw_lam_body_congr
#print axioms covWMatrix_raw_pi_domain_congr
#print axioms covWMatrix_raw_pi_codomain_congr
#print axioms covWMatrix_raw_let_annotation_congr
#print axioms covWMatrix_raw_let_value_congr
#print axioms covWMatrix_raw_let_body_congr
#print axioms covWMatrix_raw_literal_eq
#print axioms CovWMatrixRawContext
#print axioms covWMatrixRawFill
#print axioms covWMatrix_raw_context_congr
#print axioms covWMatrix_raw_literal_context_eq
#print axioms covWMatrix_raw_eq_erased
#print axioms covWMatrix_raw_eq_typed_invariant
#print axioms covWMatrix_raw_literal_context_invariant
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_RAW_CONGRUENCE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit
