/-
# Untyped conversion escape on the exact main presentation

Research witness against main ff535da69714a6b74b2fcd4d0af0f188ed539f76.
This file imports the production definitions unchanged.  It does not
state a result about the typed Conv/TyConv on wip/rcic-face.

The outer environment and context can both be well formed.  Two
untyped let congruences carry an irrelevance proof out of unchecked
let bindings, and ordinary zeta reduction then separates the sorts.
-/
import rcic.RcicRefutations
import rcic.RcicArity

namespace Rcic.Declarative.UntypedConvCollapse

def propType : Expr Nat := refutFamC

def innerCtx (Γ : LCtx) : LCtx :=
  .letBinding propType (.sort (.succ .zero)) ::
    .letBinding propType (.sort .zero) :: Γ

def boxedLeft : Expr Nat :=
  .letE propType (.sort .zero)
    (.letE propType (.sort (.succ .zero)) (.bvar 1))

def boxedRight : Expr Nat :=
  .letE propType (.sort .zero)
    (.letE propType (.sort (.succ .zero)) (.bvar 0))

def bodyConv {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    Conv E n (innerCtx Γ) (.bvar 1) (.bvar 0) :=
  .irr _ propType _ _ (refutFamC_isProp _)
    (.bvar _ 1 propType rfl) (.bvar _ 0 propType rfl)

def boxedConv {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    Conv E n Γ boxedLeft boxedRight :=
  .letE Γ propType propType (.sort .zero) (.sort .zero) _ _
    (.refl _ _) (.refl _ _)
    (.letE _ propType propType (.sort (.succ .zero)) (.sort (.succ .zero)) _ _
      (.refl _ _) (.refl _ _) (bodyConv Γ))

def leftZeta {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    Conv E n Γ boxedLeft (.sort .zero) :=
  .trans _ _ (.letE propType (.sort (.succ .zero)) (.sort .zero)) _
    (.step _ _ _ (.zeta _ _ _ _))
    (.step _ _ _ (.zeta _ _ _ _))

def rightZeta {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    Conv E n Γ boxedRight (.sort (.succ .zero)) :=
  .trans _ _ (.letE propType (.sort (.succ .zero)) (.bvar 0)) _
    (.step _ _ _ (.zeta _ _ _ _))
    (.step _ _ _ (.zeta _ _ _ _))

/-- No row hypothesis, no environment hypothesis, and no local hypothesis. -/
def sortsConv {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    Conv E n Γ (.sort .zero) (.sort (.succ .zero)) :=
  .trans _ _ _ _ (.symm _ _ _ (leftZeta Γ))
    (.trans _ _ _ _ (boxedConv Γ) (rightZeta Γ))

/-- Frozen literal statement of the current empty-environment row.
This remains a statement about these raw rules if a shared row is revised. -/
theorem sortConvChar_shape_false (n : Nat)
    (h : EnvWf emptyEnv n →
      ∀ Γ u v, CtxWf emptyEnv n Γ →
        Conv emptyEnv n Γ (.sort u) (.sort v) → eqN u v) : False :=
  refutEqN_zero_succ_false
    (h (.empty n) [] .zero (.succ .zero) .nil (sortsConv []))

/-- The CURRENT main SortConvChar is false even at the empty environment. -/
theorem sortConvChar_empty_false (n : Nat) :
    ¬ SortConvChar emptyEnv n := by
  intro h
  exact refutEqN_zero_succ_false
    (h (.empty n) [] .zero (.succ .zero) .nil (sortsConv []))

/-- More generally, its own EnvWf premise cannot rescue the current row. -/
theorem sortConvChar_false {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) : ¬ SortConvChar E n := by
  intro h
  exact refutEqN_zero_succ_false
    (h hE [] .zero (.succ .zero) .nil (sortsConv []))

def propSelfTyped {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTy E n Γ (.sort .zero) (.sort .zero) :=
  .conv _ _ _ _ (.sort Γ .zero) (.symm _ _ _ (sortsConv Γ))

/-- The former junk-context exclusion also fails on this presentation. -/
def junkLetCtxWf {E : ResolvedEnv} {n : Nat} :
    CtxWf E n junkLetCtx :=
  .letBinding [] (.sort .zero) (.succ .zero) (.sort .zero)
    .nil (.sort [] .zero) (propSelfTyped [])


/-! A second, independent route uses only proof irrelevance,
application congruence and beta.  Every context in the seed proof is
an extension by a well-formed assumption; no unchecked let is used. -/

def selectorType : Expr Nat := .pi propType (.pi propType propType)
def selectLeft : Expr Nat := .lam propType (.lam propType (.bvar 1))
def selectRight : Expr Nat := .lam propType (.lam propType (.bvar 0))

def selectorType_isProp {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTy E n Γ selectorType (.sort .zero) :=
  refutPiIsProp Γ propType .zero (.pi propType propType)
    (refutFamC_isProp Γ)
    (refutPiIsProp _ propType .zero propType
      (refutFamC_isProp _) (refutFamC_isProp _))

def selectLeft_typed {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTy E n Γ selectLeft selectorType :=
  .lam Γ propType .zero _ _ (refutFamC_isProp Γ)
    (.lam _ propType .zero _ _ (refutFamC_isProp _)
      (.bvar _ 1 propType rfl))

def selectRight_typed {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTy E n Γ selectRight selectorType :=
  .lam Γ propType .zero _ _ (refutFamC_isProp Γ)
    (.lam _ propType .zero _ _ (refutFamC_isProp _)
      (.bvar _ 0 propType rfl))

/-- The two assumption contexts used in the seed can themselves be wf. -/
def selectorCtxWf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hΓ : CtxWf E n Γ) :
    CtxWf E n (.assumption propType :: .assumption propType :: Γ) :=
  .assumption _ propType .zero
    (.assumption Γ propType .zero hΓ (refutFamC_isProp Γ))
    (refutFamC_isProp _)

def selectorsConv {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    Conv E n Γ selectLeft selectRight :=
  .irr Γ selectorType _ _ (selectorType_isProp Γ)
    (selectLeft_typed Γ) (selectRight_typed Γ)

def selectLeftBeta {E : ResolvedEnv} {n : Nat}
    (Γ : LCtx) (a b : Expr Nat) :
    Conv E n Γ (.app (.app selectLeft a) b) a := by
  have hfirst : Conv E n Γ (.app selectLeft a)
      (.lam propType (lift 0 1 a)) :=
    .step _ _ _ (.beta Γ propType (.lam propType (.bvar 1)) a)
  have hsecond : Conv E n Γ (.app (.lam propType (lift 0 1 a)) b) a := by
    have h : Conv E n Γ (.app (.lam propType (lift 0 1 a)) b)
        (instantiate0 b (lift 0 1 a)) :=
      .step _ _ _ (.beta Γ propType (lift 0 1 a) b)
    simpa only [instantiate0, instantiate_lift_id] using h
  exact .trans _ _ _ _ (.app Γ _ _ b b hfirst (.refl Γ b)) hsecond

def selectRightBeta {E : ResolvedEnv} {n : Nat}
    (Γ : LCtx) (a b : Expr Nat) :
    Conv E n Γ (.app (.app selectRight a) b) b :=
  .trans _ _ (.app (.lam propType (.bvar 0)) b) _
    (.app Γ _ _ b b
      (.step _ _ _ (.beta Γ propType (.lam propType (.bvar 0)) a))
      (.refl Γ b))
    (.step _ _ _ (.beta Γ propType (.bvar 0) b))

/-- On the current untyped presentation conversion is the total relation.
The application arguments have no typing premises in Conv.app/Step.beta. -/
def totalConv {E : ResolvedEnv} {n : Nat}
    (Γ : LCtx) (a b : Expr Nat) : Conv E n Γ a b :=
  .trans _ _ _ _ (.symm _ _ _ (selectLeftBeta Γ a b))
    (.trans _ _ _ _
      (.app Γ _ _ b b
        (.app Γ _ _ a a (selectorsConv Γ) (.refl Γ a)) (.refl Γ b))
      (selectRightBeta Γ a b))

/-- Thus the current PiConvInj does not express injectivity of a
discriminating relation: its conclusions can be supplied independently. -/
def piConvInj_trivial (E : ResolvedEnv) (n : Nat) : PiConvInj E n :=
  fun _ Γ A B A' B' _ _ =>
    ⟨totalConv Γ A A', totalConv (.assumption A :: Γ) B B'⟩

/-- Every already-typable subject can be assigned every type.
This does not assert that every raw subject has a typing derivation. -/
def retypeAny {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (h : HasTy E n Γ e A) (B : Expr Nat) :
    HasTy E n Γ e B :=
  .conv Γ e A B h (totalConv Γ A B)

/-- `EnvWf.indMember` requires `IndGroupAdmitted`. The production
inhabitant is `pinFamEnv_envWf`. -/
def familyEnvWf (n : Nat) : EnvWf pinFamEnv n :=
  pinFamEnv_envWf n

/-- Both family endpoints also have ordinary typings at the same sort.
These use a closed level list of the correct length, at n = 1. -/
def familyLeft_typed :
    HasTy pinFamEnv 1 [] (.const 0 [.zero]) (.sort .zero) :=
  .const [] 0 [.zero] ⟨.inductiveM, 1, .sort .zero, none⟩
    rfl rfl (fun _ _ => ⟨0, Or.inr (Nat.zero_lt_succ 0)⟩)

def familyRight_typed :
    HasTy pinFamEnv 1 [] (.const 0 [.succ .zero]) (.sort .zero) :=
  .const [] 0 [.succ .zero] ⟨.inductiveM, 1, .sort .zero, none⟩
    rfl rfl (fun _ _ => ⟨0, Or.inr (Nat.zero_lt_succ 0)⟩)

/-- A separating target relation cannot reflect ALL raw conversions.
For annotation lifting, R is conversion between the corresponding lifts. -/
theorem no_sort_separating_reflection {E : ResolvedEnv} {n : Nat}
    (R : Expr Nat → Expr Nat → Prop)
    (reflects : ∀ a b, Conv E n [] a b → R a b)
    (separates : ¬ R (.sort .zero) (.sort (.succ .zero))) : False :=
  separates (reflects _ _ (sortsConv []))

/-- Frozen literal shape of the current family row at this prefix. -/
theorem famAppConvInj_shape_false (n : Nat)
    (h : EnvWf pinFamEnv n →
      ∀ (Γ : LCtx) (r : Nat) (m : CheckedMember) (ls ls' : List Level)
        (xs xs' : List (Expr Nat)),
        CtxWf pinFamEnv n Γ →
        pinFamEnv.members r = some m →
        m.mclass = .inductiveM →
        Conv pinFamEnv n Γ (foldApps (.const r ls) xs)
          (foldApps (.const r ls') xs') →
        eqNList ls ls' ×' ConvArgs pinFamEnv n Γ xs xs') : False := by
  have hh := h (familyEnvWf n) [] 0 ⟨.inductiveM, 1, .sort .zero, none⟩
    [.zero] [.succ .zero] [] [] .nil rfl rfl
    (totalConv [] (.const 0 [.zero]) (.const 0 [.succ .zero]))
  exact refutEqN_zero_succ_false hh.1.1

/-- Unlike PiConvInj, the family row exports genuine level equality,
which totalConv cannot supply. The family and outer context are wf. -/
theorem famAppConvInj_false (n : Nat) :
    ¬ Nonempty (FamAppConvInj pinFamEnv n) := by
  intro ⟨h⟩
  exact famAppConvInj_shape_false n h

#print axioms sortConvChar_shape_false
#print axioms selectorCtxWf
#print axioms familyLeft_typed
#print axioms familyRight_typed
#print axioms no_sort_separating_reflection
#print axioms selectorType_isProp
#print axioms selectLeft_typed
#print axioms selectRight_typed
#print axioms selectorsConv
#print axioms selectLeftBeta
#print axioms selectRightBeta
#print axioms totalConv
#print axioms piConvInj_trivial
#print axioms retypeAny
#print axioms familyEnvWf
#print axioms famAppConvInj_shape_false
#print axioms famAppConvInj_false

#print axioms bodyConv
#print axioms boxedConv
#print axioms leftZeta
#print axioms rightZeta
#print axioms sortsConv
#print axioms sortConvChar_empty_false
#print axioms sortConvChar_false
#print axioms propSelfTyped
#print axioms junkLetCtxWf

end Rcic.Declarative.UntypedConvCollapse
