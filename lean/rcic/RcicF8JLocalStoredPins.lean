import rcic.RcicF8JLocalStored
import rcic.RcicF8JEndpointPins

/-!
Concrete context-read and raw local-ζ pins.  Context provenance is not an
original-literal leaf.  The detached-star and caller controls below are raw
boundary fixtures: they implement no EvPar/Valley embedding, and make no
shared-carrier completion claim.  closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JLocalStored.Pins
open F8Occurrences

abbrev Γ : LCtx := JEndpoints.Pins.localCtx
abbrev hΓ : CtxWfT emptyEnv 0 Γ := JEndpoints.Pins.localCtxWf
abbrev ambientTy := JEndpoints.Pins.localValueTy
abbrev original := JEndpoints.Pins.localSource
abbrev packet := JEndpoints.Pins.localPacket
abbrev one : Level := JEndpoints.Pins.one

def storedTy : HasTyT emptyEnv 0 [] (.sort .zero) (.sort one) := .sort [] .zero

def stored : StoredLetAt Γ 0 (.sort one) (.sort .zero) :=
  recoverStoredLet rfl rfl

def receipt : StoredLetTyping hΓ stored := StoredLetTyping.lookup hΓ stored

theorem actual_stored_object :
    stored.storedType = .sort one ∧ stored.storedValue = .sort .zero := ⟨rfl, rfl⟩

theorem actual_context_read : receipt.hvt = storedTy := rfl

theorem original_leaf_inventory : packet.leaves = [Jd.ty ambientTy] := rfl

theorem stored_context_differs : ([] : LCtx) ≠ Γ := by
  intro h
  cases h

/-- The context field is correct, but is not a subderivation of this literal.
The only immediate typing field is ambientTy; a longer path is ruled out by
its exact existing derivation weights. -/
theorem stored_not_original_leaf : ¬ SubOf (Jd.ty storedTy) (.cv original) := by
  intro h
  cases h with
  | child hc =>
      change Jd.ty storedTy ∈ [Jd.ty ambientTy] at hc
      have he := List.mem_singleton.mp hc
      cases he
  | trans h₁ h₂ =>
      have hw₁ := subOf_wt_lt h₁
      have hw₂ := subOf_wt_lt h₂
      change 1 < _ at hw₁
      change _ < 2 at hw₂
      omega

/-! Nontrivial value lift: the stored bvar0 becomes ambient bvar1. -/
def tailCtx : LCtx := [.assumption (.sort one)]
def tailWf : CtxWfT emptyEnv 0 tailCtx :=
  .assumption [] (.sort one) (.succ one) .nil (.sort [] one)
def tailValueTy : HasTyT emptyEnv 0 tailCtx (.bvar 0) (.sort one) :=
  .bvar tailCtx 0 (.sort one) rfl

def liftedCtx : LCtx := .letBinding (.sort one) (.bvar 0) :: tailCtx
def liftedWf : CtxWfT emptyEnv 0 liftedCtx :=
  .letBinding tailCtx (.sort one) (.succ one) (.bvar 0) tailWf
    (.sort tailCtx one) tailValueTy

def liftedAmbientTy : HasTyT emptyEnv 0 liftedCtx (.bvar 1) (.sort one) :=
  .bvar liftedCtx 1 (.sort one) rfl

def liftedStored : StoredLetAt liftedCtx 0 (.sort one) (.bvar 1) :=
  recoverStoredLet rfl rfl

def liftedReceipt : StoredLetTyping liftedWf liftedStored :=
  StoredLetTyping.lookup liftedWf liftedStored

theorem actual_nontrivial_value_lift :
    liftedStored.storedValue = .bvar 0 ∧
      lift 0 1 liftedStored.storedValue = .bvar 1 := ⟨rfl, rfl⟩

theorem actual_lifted_context_read : liftedReceipt.hvt = tailValueTy := rfl

def WeakStoredValue (w : Expr Nat) : Prop :=
  Nonempty (HasTyT emptyEnv 0 liftedCtx w (.sort one))
def ExactStoredValue (w : Expr Nat) : Prop := w = liftedStored.storedValue

theorem mutant_ambient_value_accepts : WeakStoredValue (.bvar 1) := ⟨liftedAmbientTy⟩
theorem exact_stored_value_refuses : ¬ ExactStoredValue (.bvar 1) := by
  intro h
  cases h

def WeakTail (Δ : LCtx) : Prop := Nonempty (CtxWfT emptyEnv 0 Δ)
def ExactTail (Δ : LCtx) : Prop := Δ = Γ.drop (0 + 1)

theorem mutant_drop_i_accepts : WeakTail (Γ.drop 0) := ⟨hΓ⟩
theorem exact_drop_succ_refuses : ¬ ExactTail (Γ.drop 0) := by
  intro h
  cases h

/-- Same judgment, different derivation: an identity conversion wrapper
is not the field actually read from hΓ. -/
def alternativeStoredTy : HasTyT emptyEnv 0 tailCtx (.bvar 0) (.sort one) :=
  .conv tailCtx (.bvar 0) (.sort one) (.sort one) (.succ one) tailValueTy
    (.refl tailCtx (.sort one) (.sort (.succ one)) (.sort tailCtx one))

def SameStoredJudgment {Δ : LCtx} {w A : Expr Nat}
    (_ : HasTyT emptyEnv 0 Δ w A) : Prop :=
  Δ = tailCtx ∧ w = .bvar 0 ∧ A = .sort one

def ExactContextField (h : HasTyT emptyEnv 0 tailCtx (.bvar 0) (.sort one)) : Prop :=
  HEq h liftedReceipt.hvt

theorem mutant_same_judgment_accepts : SameStoredJudgment alternativeStoredTy :=
  ⟨rfl, rfl, rfl⟩
theorem exact_context_field_refuses : ¬ ExactContextField alternativeStoredTy := by
  intro h
  have he : alternativeStoredTy = tailValueTy := eq_of_heq h
  cases he

def fakeLeaves : List (Jd emptyEnv 0) := packet.leaves ++ [.ty storedTy]
def MergedContextBudget (ls : List (Jd emptyEnv 0)) : Prop :=
  ∀ l ∈ ls, SubOf l (.cv original) ∨ l = .ty storedTy

def ExactOriginalBudget (ls : List (Jd emptyEnv 0)) : Prop :=
  ∀ l ∈ ls, SubOf l (.cv original)

theorem mutant_context_leaf_accepts : MergedContextBudget fakeLeaves := by
  intro l hl
  change l ∈ [Jd.ty ambientTy, Jd.ty storedTy] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact .inl (.child (.head _))
  · exact .inr rfl

theorem exact_original_leaf_refuses : ¬ ExactOriginalBudget fakeLeaves := by
  intro h
  apply stored_not_original_leaf
  exact h (.ty storedTy) (List.mem_append.mpr (.inr (.head _)))

/-! Standalone raw boundary controls.  They do not assert that a payload has
entered EvParStar or Valley.  Empty actual raw-star entries refute the weak
inference from materialization alone. -/
def raw : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ
    (.bvar 0) (.sort .zero) (.sort one) :=
  localZeta hΓ 0 (.sort one) (.sort .zero) rfl rfl ambientTy
    (R := JEndpoints.Pins.localRoot) ⟨_, .head _, .inl rfl⟩

def canonicalRaw : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ
    (.bvar 0) (.sort .zero) (.sort one) :=
  .bvarZeta Γ 0 (.sort one) (.sort .zero) (.sort .zero) (.sort one) rfl
    (.refl [] (.sort .zero) (.sort one) storedTy)
    (.bvar Γ 0 (.sort one) rfl) ambientTy

theorem actual_raw_constructor : raw = canonicalRaw := rfl

def rawEntries : {Δ : LCtx} → {a b T : Expr Nat} →
    ParRedTStar (PEqLeafT emptyEnv 0) emptyEnv 0 Δ a b T → List (Jd emptyEnv 0)
  | _, _, _, _, .refl .. => []
  | _, _, _, _, .tail h hs => .pr h :: rawEntries hs

def unconnectedStar : ParRedTStar (PEqLeafT emptyEnv 0) emptyEnv 0 Γ
    (.bvar 0) (.bvar 0) (.sort one) :=
  .refl Γ (.bvar 0) (.sort one) (.bvar Γ 0 (.sort one) rfl)

def WeakMaterialized (p : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ
    (.bvar 0) (.sort .zero) (.sort one)) : Prop := p = canonicalRaw

def EnteredActualStar (p : ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 Γ
    (.bvar 0) (.sort .zero) (.sort one)) : Prop :=
  Jd.pr p ∈ rawEntries unconnectedStar

theorem mutant_detached_payload_accepts : WeakMaterialized raw := actual_raw_constructor
theorem exact_star_entry_refuses : ¬ EnteredActualStar raw := by
  simp only [EnteredActualStar, unconnectedStar, rawEntries, List.not_mem_nil, not_false_eq_true]

/-- A proper-parent ambient root distinguishes caller X from R, while both
standalone tiles retain exactly the same canonical raw producer. -/
def parent : ConvT emptyEnv 0 Γ (.sort .zero) (.bvar 0) (.sort one) :=
  .symm Γ (.bvar 0) (.sort .zero) (.sort one) original

def ambientRoots : List (Jd emptyEnv 0) := [.cv parent]

def boundaryTile (X : List (Jd emptyEnv 0)) : DTile ambientRoots where
  X := X
  step := canonicalRaw
  status := fun o => nomatch o
  om2 := by intro o; exact nomatch o

def callerTile : DTile ambientRoots := boundaryTile [.cv original]
def ambientCallerTile : DTile ambientRoots := boundaryTile ambientRoots

def WeakCaller (t : DTile ambientRoots) : Prop := HEq t.step callerTile.step
def ExactCaller (t : DTile ambientRoots) : Prop := t.X = [.cv original]

theorem mutant_ambient_caller_accepts : WeakCaller ambientCallerTile := HEq.rfl
theorem exact_original_caller_refuses : ¬ ExactCaller ambientCallerTile := by
  intro h
  change [Jd.cv parent] = [Jd.cv original] at h
  have he := List.cons.inj h
  cases he.1

end Rcic.Declarative.F8Measure.JLocalStored.Pins
