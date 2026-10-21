import rcic.RcicNativeWallLetVariable
import rcic.RcicNativeValleyOf

/-!
# Context data for induction on an original native conversion

`closure_claim = 0`.

This file constructs value-only context packages. A package carries the native
context conversion, exact lookup types, and certified valleys comparing each
original looked-up value with its target looked-up value in the WHOLE target
context. The constructors below produce this data; they require no diamond and
no generic parallel-to-native back-lift. The later native conversion producer
is a separate construction.

Dependency pin: `4d3b74e05355f478a03a44166399794a0a68d2a4`.
-/

namespace Rcic.Declarative.NativeValleys.ContextAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- A native context conversion preserving every lookup type exactly. Its
value certificates live in the complete target context at that exact type. -/
structure Pack (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type)
    (Γ Γ' : LCtx) where
  native : CtxConvT E n Γ Γ'
  types : ∀ i, lookupType Γ i = lookupType Γ' i
  values : ∀ {i : Nat} {A v : Expr Nat},
    lookupValue Γ i = some v → lookupType Γ i = some A →
    Σ' v', lookupValue Γ' i = some v' ×' CValley E n PEq Γ' v v' A

/-- A lookup valley weakens under any single target declaration. -/
def valley_weaken_head (hcl : EnvClosed E) (L : LeafIface E n PEq)
    (d : LocalDecl) {Γ : LCtx} {a b T : Expr Nat}
    (V : CValley E n PEq Γ a b T) :
    CValley E n PEq (d :: Γ) (lift 0 1 a) (lift 0 1 b) (lift 0 1 T) :=
  ⟨lift 0 1 V.centre,
    LetVariableAudit.star_weaken_head hcl L d V.left,
    LetVariableAudit.star_weaken_head hcl L d V.right⟩

/-- Successor lookups depend only on the tail. The original type and value
equations each expose their lifted tail data; the target valley is then
weakened under the target declaration, even when the two heads differ. -/
def lookupValue_succ_valley (hcl : EnvClosed E) (L : LeafIface E n PEq)
    {Γ Γ' : LCtx} (K : Pack E n PEq Γ Γ') (d d' : LocalDecl)
    {i : Nat} {A v : Expr Nat}
    (hv : lookupValue (d :: Γ) (i + 1) = some v)
    (hA : lookupType (d :: Γ) (i + 1) = some A) :
    Σ' v', lookupValue (d' :: Γ') (i + 1) = some v' ×'
      CValley E n PEq (d' :: Γ') v v' A := by
  rw [lookupValue_cons_succ] at hv
  rw [lookupType_cons_succ] at hA
  cases hv₀ : lookupValue Γ i with
  | none =>
      rw [hv₀] at hv
      cases hv
  | some v₀ =>
      rw [hv₀] at hv
      cases hv
      cases hA₀ : lookupType Γ i with
      | none =>
          rw [hA₀] at hA
          cases hA
      | some A₀ =>
          rw [hA₀] at hA
          cases hA
          obtain ⟨v', hv', V⟩ := K.values hv₀ hA₀
          exact ⟨lift 0 1 v',
            by rw [lookupValue_cons_succ, hv']; rfl,
            valley_weaken_head hcl L d' V⟩

namespace Pack

/-- Read a preserved lookup type in the target context. -/
def typeAt {Γ Γ' : LCtx} (K : Pack E n PEq Γ Γ')
    {i : Nat} {A : Expr Nat} (h : lookupType Γ i = some A) :
    lookupType Γ' i = some A := by
  rw [← K.types i]
  exact h

/-- The empty package contains no value lookup obligations. -/
def nil : Pack E n PEq [] [] where
  native := .nil
  types := fun _ => rfl
  values := by
    intro i A v hv hA
    cases i <;> cases hv

/-- Extend both contexts by the same assumption. No typing of this head is
needed to construct the package; the caller supplies target well-formedness
when using it in a native conversion producer. -/
def assumption (hcl : EnvClosed E) (L : LeafIface E n PEq)
    {Γ Γ' : LCtx} (K : Pack E n PEq Γ Γ') (A : Expr Nat) :
    Pack E n PEq (.assumption A :: Γ) (.assumption A :: Γ') where
  native := .same (.assumption A) K.native
  types := by
    intro i
    cases i with
    | zero => rfl
    | succ i => simp only [lookupType_cons_succ, K.types i]
  values := by
    intro i A₀ v₀ hv hA
    cases i with
    | zero => cases hv
    | succ i =>
        exact lookupValue_succ_valley hcl L K
          (.assumption A) (.assumption A) hv hA

/-- Extend by a changed let value, using a supplied native certified star in
the target tail. The head lookup valley is the weakening of that star plus a
reflexive right leg; all older lookup valleys weaken under the NEW head. -/
def letBinding (hcl : EnvClosed E) (L : LeafIface E n PEq)
    {Γ Γ' : LCtx} (K : Pack E n PEq Γ Γ')
    {A v vc : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ' A (.sort u))
    (s : CStar E n PEq Γ' v vc A) :
    Pack E n PEq (.letBinding A v :: Γ) (.letBinding A vc :: Γ') where
  native := .letBinding K.native hA hA (.refl Γ' A _ hA)
    s.rightTyped s.toConvT
  types := by
    intro i
    cases i with
    | zero => rfl
    | succ i => simp only [lookupType_cons_succ, K.types i]
  values := by
    intro i A₀ v₀ hv hT
    cases i with
    | zero =>
        cases hv
        cases hT
        let V : CValley E n PEq Γ' v vc A :=
          ⟨vc, s, .refl Γ' vc A s.rightTyped⟩
        exact ⟨lift 0 1 vc, rfl,
          valley_weaken_head hcl L (.letBinding A vc) V⟩
    | succ i =>
        exact lookupValue_succ_valley hcl L K
          (.letBinding A v) (.letBinding A vc) hv hT

/-- Every well-formed context has an identity package, constructed by induction
on its well-formedness derivation. Let declarations use their actual stored
value typing to supply the reflexive head valley. -/
def refl (hcl : EnvClosed E) (L : LeafIface E n PEq) :
    {Γ : LCtx} → CtxWfT E n Γ → Pack E n PEq Γ Γ
  | _, .nil => nil
  | _, .assumption _ A _ hΓ _ =>
      assumption hcl L (refl hcl L hΓ) A
  | _, .letBinding Γ A _ v hΓ hA hv =>
      letBinding hcl L (refl hcl L hΓ) hA (.refl Γ v A hv)

end Pack

#print axioms valley_weaken_head
#print axioms lookupValue_succ_valley
#print axioms Pack.typeAt
#print axioms Pack.nil
#print axioms Pack.assumption
#print axioms Pack.letBinding
#print axioms Pack.refl

end Rcic.Declarative.NativeValleys.ContextAudit
