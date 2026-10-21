import rcic.RcicNativeTypedModelCovWIrrelAligned

/-!
# Native fields at an actual application occurrence

The domain is carried by native typing of the displayed function and argument.
It is not reconstructed from a compact prefix. Proof domains permit only bottom;
domains natively convertible to a Pi permit only bottom or a graph. The predicate
does not inspect observation derivations and uses no classifier or choice.

The domain witness is explicit occurrence evidence. Independence of alternative
native typing witnesses is a separate native transport question, not an axiom of
this predicate. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovWIrrelAudit

def CovWNativeOccurrence (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (f a D B : Expr Nat) : Prop :=
  Nonempty (HasTyT E n Γ f (.pi D B)) ∧ Nonempty (HasTyT E n Γ a D)

def CovWNativeFunctionDomain (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (D : Expr Nat) : Prop :=
  ∃ A B, Nonempty (TyConvT E n Γ D (.pi A B))

def CovWNativeFunctionCompact (u : CptWIrrel) : Prop :=
  u = .bot ∨ ∃ rows, u = .lam rows

def CovWNativeField (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (f a : Expr Nat) (u : CptWIrrel) : Prop :=
  ∃ D B, CovWNativeOccurrence E n Γ f a D B ∧
    (Nonempty (HasTyT E n Γ D (.sort .zero)) → u = .bot) ∧
    (CovWNativeFunctionDomain E n Γ D → CovWNativeFunctionCompact u)

theorem covWNative_field_bot {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a D B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi D B)) (ha : HasTyT E n Γ a D) :
    CovWNativeField E n Γ f a .bot :=
  ⟨D, B, ⟨⟨hf⟩, ⟨ha⟩⟩, fun _ => rfl, fun _ => Or.inl rfl⟩

theorem covWNative_field_mk {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a D B : Expr Nat} {u : CptWIrrel}
    (hf : HasTyT E n Γ f (.pi D B)) (ha : HasTyT E n Γ a D)
    (hp : Nonempty (HasTyT E n Γ D (.sort .zero)) → u = .bot)
    (hfun : CovWNativeFunctionDomain E n Γ D → CovWNativeFunctionCompact u) :
    CovWNativeField E n Γ f a u :=
  ⟨D, B, ⟨⟨hf⟩, ⟨ha⟩⟩, hp, hfun⟩

theorem covWNative_function_compact_no_spine {r : Nat} {ls : List Level}
    {args : List CptWIrrel} :
    ¬ CovWNativeFunctionCompact (.spine r ls args) := by
  rintro (h | ⟨rows, h⟩) <;> cases h

theorem covWNative_syntactic_function {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (A B : Expr Nat) :
    CovWNativeFunctionDomain E n Γ (.pi A B) :=
  ⟨A, B, ⟨.refl Γ (.pi A B)⟩⟩

/-- The selected native occurrence, retained explicitly for local reasoning.
Variables in eta bodies use this same predicate in their extended context. -/
def CovWNativeFieldAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (f a D B : Expr Nat) (u : CptWIrrel) : Prop :=
  CovWNativeOccurrence E n Γ f a D B ∧
    (Nonempty (HasTyT E n Γ D (.sort .zero)) → u = .bot) ∧
    (CovWNativeFunctionDomain E n Γ D → CovWNativeFunctionCompact u)

theorem covWNative_field_iff_at {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a : Expr Nat} {u : CptWIrrel} :
    CovWNativeField E n Γ f a u ↔
      ∃ D B, CovWNativeFieldAt E n Γ f a D B u := Iff.rfl

theorem covWNative_fieldAt_proof {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a D B : Expr Nat} {u : CptWIrrel}
    (h : CovWNativeFieldAt E n Γ f a D B u)
    (hp : HasTyT E n Γ D (.sort .zero)) : u = .bot :=
  h.2.1 ⟨hp⟩

theorem covWNative_fieldAt_function {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a D B A C : Expr Nat} {u : CptWIrrel}
    (h : CovWNativeFieldAt E n Γ f a D B u)
    (hc : TyConvT E n Γ D (.pi A C)) : CovWNativeFunctionCompact u :=
  h.2.2 ⟨A, C, ⟨hc⟩⟩

/-- At every other positively certified domain, the field is unchanged.
No classification decision is postulated for arbitrary native domains. -/
theorem covWNative_fieldAt_other {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a D B : Expr Nat} (u : CptWIrrel)
    (hf : HasTyT E n Γ f (.pi D B)) (ha : HasTyT E n Γ a D)
    (hp : ¬ Nonempty (HasTyT E n Γ D (.sort .zero)))
    (hn : ¬ CovWNativeFunctionDomain E n Γ D) :
    CovWNativeFieldAt E n Γ f a D B u :=
  ⟨⟨⟨hf⟩, ⟨ha⟩⟩, fun h => (hp h).elim, fun h => (hn h).elim⟩

theorem covWNative_fieldAt_no_function_atom {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f a D B A C : Expr Nat} {r : Nat} {ls : List Level}
    {args : List CptWIrrel}
    (h : CovWNativeFieldAt E n Γ f a D B (.spine r ls args))
    (hc : TyConvT E n Γ D (.pi A C)) : False :=
  covWNative_function_compact_no_spine (covWNative_fieldAt_function h hc)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_FIELDS_ROOTS
#print axioms CovWNativeOccurrence
#print axioms CovWNativeFunctionDomain
#print axioms CovWNativeFunctionCompact
#print axioms CovWNativeField
#print axioms covWNative_field_bot
#print axioms covWNative_field_mk
#print axioms covWNative_function_compact_no_spine
#print axioms covWNative_syntactic_function
#print axioms CovWNativeFieldAt
#print axioms covWNative_field_iff_at
#print axioms covWNative_fieldAt_proof
#print axioms covWNative_fieldAt_function
#print axioms covWNative_fieldAt_other
#print axioms covWNative_fieldAt_no_function_atom
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_NATIVE_FIELDS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWNativeAudit
