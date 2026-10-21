import rcic.RcicF8JEndpoints

/-!
The stored declaration behind an original local-zeta lookup, its exact
context-carried tail typing, and the raw typed local-zeta constructor.
No D carrier or star is supplied here.  closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JLocalStored

open Rcic.Syn
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
variable {Γ : LCtx} {i : Nat} {A v : Expr Nat}

/-- The unlifted objects are recovered from the actual context entry. -/
structure StoredLetAt (Γ : LCtx) (i : Nat) (A v : Expr Nat) where
  storedType : Expr Nat
  storedValue : Expr Nat
  entry : Γ.get? i = some (.letBinding storedType storedValue)
  type_eq : A = lift 0 (i + 1) storedType
  value_eq : v = lift 0 (i + 1) storedValue

/-- Recover the stored value from lookup, independently of any typing of the
ambient value.  The original type lookup fixes the stored type's lift. -/
def recoverStoredLet (hval : lookupValue Γ i = some v)
    (hty : lookupType Γ i = some A) : StoredLetAt Γ i A v :=
  let found := get?_of_lookupValue hval
  { storedType := found.1
    storedValue := found.2.1
    entry := found.2.2.1
    type_eq := Option.some.inj
      (hty.symm.trans (lookupType_getQ_letBinding found.2.2.1))
    value_eq := found.2.2.2 }

/-- The actual recovered entry is the one returned by the existing inverse. -/
theorem stored_lookup_exact (hval : lookupValue Γ i = some v)
    (hty : lookupType Γ i = some A) :
    (recoverStoredLet hval hty).entry = (get?_of_lookupValue hval).2.2.1 := rfl

theorem stored_data_exact (hval : lookupValue Γ i = some v)
    (hty : lookupType Γ i = some A) :
    (recoverStoredLet hval hty).storedType = (get?_of_lookupValue hval).1 ∧
      (recoverStoredLet hval hty).storedValue = (get?_of_lookupValue hval).2.1 :=
  ⟨rfl, rfl⟩

/-- The stored type is aligned with the original lookup, not inferred from
an ambient derivation of the value. -/
theorem stored_type_exact (hval : lookupValue Γ i = some v)
    (hty : lookupType Γ i = some A) :
    (recoverStoredLet hval hty).type_eq =
      Option.some.inj (hty.symm.trans
        (lookupType_getQ_letBinding (recoverStoredLet hval hty).entry)) := rfl

/-- The typing is the real context field below this binder, with its full
derivation retained rather than merely another proof of its judgment. -/
structure StoredLetTyping (hΓ : CtxWfT E n Γ) (s : StoredLetAt Γ i A v) where
  hvt : HasTyT E n (Γ.drop (i + 1)) s.storedValue s.storedType
  hvt_exact : hvt = ctxWfTLookupValueAtDrop hΓ i s.entry

def StoredLetTyping.lookup (hΓ : CtxWfT E n Γ) (s : StoredLetAt Γ i A v) :
    StoredLetTyping hΓ s where
  hvt := ctxWfTLookupValueAtDrop hΓ i s.entry
  hvt_exact := rfl

theorem stored_typing_exact (hΓ : CtxWfT E n Γ) (s : StoredLetAt Γ i A v)
    (t : StoredLetTyping hΓ s) :
    t.hvt = ctxWfTLookupValueAtDrop hΓ i s.entry := t.hvt_exact

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- The only child reduction is reflexivity on the actual stored-tail field. -/
def storedRefl {hΓ : CtxWfT E n Γ} {s : StoredLetAt Γ i A v}
    (t : StoredLetTyping hΓ s) :
    ParRedT PEq E n (Γ.drop (i + 1)) s.storedValue s.storedValue s.storedType :=
  .refl (Γ.drop (i + 1)) s.storedValue s.storedType t.hvt

theorem stored_refl_exact {hΓ : CtxWfT E n Γ} {s : StoredLetAt Γ i A v}
    (t : StoredLetTyping hΓ s) :
    storedRefl (PEq := PEq) t =
      ParRedT.refl (Γ.drop (i + 1)) s.storedValue s.storedType
        (ctxWfTLookupValueAtDrop hΓ i s.entry) := by
  rw [storedRefl, t.hvt_exact]

/-- The original left endpoint typing of J2's local-zeta packet. -/
def localZetaLeft (hty : lookupType Γ i = some A) : HasTyT E n Γ (.bvar i) A :=
  .bvar Γ i A hty

/-- Only the target expression changes here: the entire original ambient
typing derivation is transported along the recovered lookup equation. -/
def localZetaRight (s : StoredLetAt Γ i A v) (hv : HasTyT E n Γ v A) :
    HasTyT E n Γ (lift 0 (i + 1) s.storedValue) A :=
  Eq.mp (congrArg (fun w => HasTyT E n Γ w A) s.value_eq) hv

/-- The raw constructor before aligning its lifted stored target to `v`.
The support certificate belongs to the original J2 packet; the raw relation
has no leaf-certificate field to replace or enlarge. -/
def localZetaPlain (hΓ : CtxWfT E n Γ) (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (_hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    ParRedT PEq E n Γ (.bvar i)
      (lift 0 (i + 1) (recoverStoredLet hval hty).storedValue) A :=
  let s := recoverStoredLet hval hty
  .bvarZeta Γ i s.storedType s.storedValue s.storedValue A s.entry
    (storedRefl (StoredLetTyping.lookup hΓ s))
    (localZetaLeft hty) (localZetaRight s hv)

/-- The original target is restored by its exact lookup equation. -/
def localZeta (hΓ : CtxWfT E n Γ) (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    ParRedT PEq E n Γ (.bvar i) v A :=
  Eq.mp (congrArg (fun w => ParRedT PEq E n Γ (.bvar i) w A)
    (recoverStoredLet hval hty).value_eq.symm)
    (localZetaPlain hΓ i A v hval hty hv hs)

/-- Equality of the actual raw reduction, including the exact stored field,
child reflexivity, and both original endpoint typing arguments. -/
theorem localZeta_plain_exact (hΓ : CtxWfT E n Γ) (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    localZetaPlain (PEq := PEq) hΓ i A v hval hty hv hs =
      ParRedT.bvarZeta Γ i (recoverStoredLet hval hty).storedType
        (recoverStoredLet hval hty).storedValue
        (recoverStoredLet hval hty).storedValue A
        (recoverStoredLet hval hty).entry
        (.refl (Γ.drop (i + 1)) (recoverStoredLet hval hty).storedValue
          (recoverStoredLet hval hty).storedType
          (ctxWfTLookupValueAtDrop hΓ i (recoverStoredLet hval hty).entry))
        (HasTyT.bvar Γ i A hty)
        (Eq.mp (congrArg (fun w => HasTyT E n Γ w A)
          (recoverStoredLet hval hty).value_eq) hv) := rfl

/-- The exact left constructor argument is J2's original packet typing. -/
theorem localZeta_left_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    localZetaLeft hty =
      (JEndpoints.zetaLocalPacket i A v hval hty hv hs).left.val hcl hinst := rfl

/-- The exact right constructor argument is the original packet typing,
transported only by the stored-value lookup equation. -/
theorem localZeta_right_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    localZetaRight (recoverStoredLet hval hty) hv =
      Eq.mp (congrArg (fun w => HasTyT E n Γ w A)
        (recoverStoredLet hval hty).value_eq)
        ((JEndpoints.zetaLocalPacket i A v hval hty hv hs).right.val hcl hinst) := rfl

end Rcic.Declarative.F8Measure.JLocalStored
