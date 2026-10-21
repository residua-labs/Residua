import rcic.RcicHeadStepT
import rcic.RcicNativeValleyDecoTransfer

set_option autoImplicit false

/-!
# Native finite Pi observations and their composition

This module constructs one native logical-relation component, on `Expr Nat`
and the existing `HeadStepT`. Its inputs and outputs remain in `Type`.

`PiHeadObs E n Γ s t` stores finite observations of both endpoints at Pi
heads, independent native `TyConvT` certificates from the endpoints to those
heads, and native conversions of the two domains and codomains. Keeping the
certificates independent is essential: `headStepT_sound` lands in `ParRedT`,
and no raw-reduction-to-native-conversion theorem is used here.

The new work is symmetry, transitivity, and finite head expansion. The two
observations of a shared middle term have the same Pi head by the existing
single-step determinism theorem. Codomain conversions are moved to the left
binder by `tyConvT_assump_dom`, which consumes `EnvWfT` and `CtxWfT`, with no
type uniqueness or injectivity premise.

Recursion is explicit and bounded by already supplied finite traces:

* `HeadTrace.trans` calls itself on the original first trace's tail.
* `HeadTrace.normal_det` compares the original two trace tails after their
  immediate targets have been identified by `headStepT_det`.
* The observation operations make no recursive calls.

This is a partial relation. It does not assert that every native conversion
produces an observation. `HeadStepT` contracts roots only; no application
spine closure or normalization theorem is supplied. The independent native
certificates are never inferred from the trace. Semantic stages, smaller
validity clauses, and endpoint sorting are not part of this component;
literal-Pi reflection permits untyped Pis, just as `TyConvT.refl` does.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativePiHeadObs

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- A finite sequence of the existing native root contractions. Each step
retains its own type index. No common sorting or decoration is required. -/
inductive HeadTrace (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Type where
  | refl (e : Expr Nat) : HeadTrace E n Γ e e
  | cons {e m z T : Expr Nat} (step : HeadStepT E n Γ e m T)
      (tail : HeadTrace E n Γ m z) : HeadTrace E n Γ e z

/-- Normality for this root-contraction relation, with every type index
quantified independently. -/
def HeadNormal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) : Prop :=
  ∀ {z T : Expr Nat}, HeadStepT E n Γ e z T → False

namespace HeadTrace

/-- Concatenation recurses only on the original first trace's tail. -/
def trans {e m z : Expr Nat} :
    HeadTrace E n Γ e m → HeadTrace E n Γ m z → HeadTrace E n Γ e z
  | .refl _, right => right
  | .cons step tail, right => .cons step (trans tail right)

/-- A trace from an already normal source is empty at the level of terms.
The derivation itself is not equated with any other derivation. -/
theorem eq_of_normal {e z : Expr Nat} (h : HeadTrace E n Γ e z)
    (hn : HeadNormal E n Γ e) : e = z := by
  cases h with
  | refl => rfl
  | cons step tail => exact (hn step).elim

/-- Two finite traces from the same source ending at normal terms have
the same terminal term. The recursive call uses the original two tails. -/
theorem normal_det {e a b : Expr Nat}
    (left : HeadTrace E n Γ e a) (right : HeadTrace E n Γ e b)
    (ha : HeadNormal E n Γ a) (hb : HeadNormal E n Γ b) : a = b := by
  induction left generalizing b with
  | refl e => exact eq_of_normal right ha
  | cons step tail ih =>
      cases right with
      | refl => exact (hb step).elim
      | cons step' tail' =>
          have hm := headStepT_det step step'
          cases hm
          exact ih tail' ha hb

end HeadTrace

/-- A written Pi admits none of the existing root contractions. -/
theorem pi_headNormal (A B : Expr Nat) : HeadNormal E n Γ (.pi A B) := by
  intro z T h
  exact headStepT_inv_rigid h
    (fun _ _ he => Expr.noConfusion he)
    (fun _ _ he => Expr.noConfusion he)
    (fun _ _ _ he => Expr.noConfusion he)
    (fun _ he => Expr.noConfusion he)

/-- A pair of finite native Pi observations. The native endpoint
certificates are separate from the traces, while the component evidence
is retained at the exact left binder. -/
structure PiHeadObs (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (s t : Expr Nat) : Type where
  leftDom : Expr Nat
  leftCod : Expr Nat
  rightDom : Expr Nat
  rightCod : Expr Nat
  leftTrace : HeadTrace E n Γ s (.pi leftDom leftCod)
  rightTrace : HeadTrace E n Γ t (.pi rightDom rightCod)
  leftCert : TyConvT E n Γ s (.pi leftDom leftCod)
  rightCert : TyConvT E n Γ t (.pi rightDom rightCod)
  domains : TyConvT E n Γ leftDom rightDom
  codomains : TyConvT E n (.assumption leftDom :: Γ) leftCod rightCod

namespace PiHeadObs

/-- Direct reflection of the literal Pi head, with no termination
or global self-relatedness premise. -/
def refl (A B : Expr Nat) : PiHeadObs E n Γ (.pi A B) (.pi A B) where
  leftDom := A
  leftCod := B
  rightDom := A
  rightCod := B
  leftTrace := .refl _
  rightTrace := .refl _
  leftCert := .refl _ _
  rightCert := .refl _ _
  domains := .refl _ _
  codomains := .refl _ _

/-- Native component evidence forms an observation at literal Pi heads. -/
def of_components {A B A' B' : Expr Nat}
    (hA : TyConvT E n Γ A A')
    (hB : TyConvT E n (.assumption A :: Γ) B B') :
    PiHeadObs E n Γ (.pi A B) (.pi A' B') where
  leftDom := A
  leftCod := B
  rightDom := A'
  rightCod := B'
  leftTrace := .refl _
  rightTrace := .refl _
  leftCert := .refl _ _
  rightCert := .refl _ _
  domains := hA
  codomains := hB

/-- Symmetry moves the reversed codomain certificate from the original
left binder to the original right binder along the reversed domain chain. -/
def symm (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) {s t : Expr Nat}
    (h : PiHeadObs E n Γ s t) : PiHeadObs E n Γ t s where
  leftDom := h.rightDom
  leftCod := h.rightCod
  rightDom := h.leftDom
  rightCod := h.leftCod
  leftTrace := h.rightTrace
  rightTrace := h.leftTrace
  leftCert := h.rightCert
  rightCert := h.leftCert
  domains := h.domains.symmT
  codomains := tyConvT_assump_dom hW hΓ h.domains.symmT h.codomains.symmT

/-- Composition aligns the two independently observed middle Pi heads.
The second codomain certificate is transported along the first domain
chain before it is composed with the first codomain certificate. -/
def trans (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) {s t u : Expr Nat}
    (left : PiHeadObs E n Γ s t) (right : PiHeadObs E n Γ t u) :
    PiHeadObs E n Γ s u := by
  cases left with
  | mk A B M N hl hm cl cm hA hB =>
      cases right with
      | mk M' N' C D hm' hr cm' cr hA' hB' =>
          have he := HeadTrace.normal_det hm hm'
            (pi_headNormal M N) (pi_headNormal M' N')
          obtain ⟨heA, heB⟩ := Expr.pi.inj he
          cases heA
          cases heB
          exact {
            leftDom := A
            leftCod := B
            rightDom := C
            rightCod := D
            leftTrace := hl
            rightTrace := hr
            leftCert := cl
            rightCert := cr
            domains := .trans _ _ _ _ hA hA'
            codomains := .trans _ _ _ _ hB
              (tyConvT_assump_dom hW hΓ hA hB') }

/-- Finite left expansion consumes both the actual trace and its
independent native certificate. Concatenation inspects only this trace. -/
def expand_left {s s' t : Expr Nat} (trace : HeadTrace E n Γ s s')
    (cert : TyConvT E n Γ s s') (h : PiHeadObs E n Γ s' t) :
    PiHeadObs E n Γ s t where
  leftDom := h.leftDom
  leftCod := h.leftCod
  rightDom := h.rightDom
  rightCod := h.rightCod
  leftTrace := trace.trans h.leftTrace
  rightTrace := h.rightTrace
  leftCert := .trans _ _ _ _ cert h.leftCert
  rightCert := h.rightCert
  domains := h.domains
  codomains := h.codomains

/-- Finite right expansion keeps the codomain certificate at the same
left binder and consumes a separate native certificate on the right. -/
def expand_right {s t t' : Expr Nat} (trace : HeadTrace E n Γ t t')
    (cert : TyConvT E n Γ t t') (h : PiHeadObs E n Γ s t') :
    PiHeadObs E n Γ s t where
  leftDom := h.leftDom
  leftCod := h.leftCod
  rightDom := h.rightDom
  rightCod := h.rightCod
  leftTrace := h.leftTrace
  rightTrace := trace.trans h.rightTrace
  leftCert := h.leftCert
  rightCert := .trans _ _ _ _ cert h.rightCert
  domains := h.domains
  codomains := h.codomains

/-- Extraction at literal Pi endpoints. This consumes an observation,
not an arbitrary native conversion between the two Pi expressions. -/
def components {A B A' B' : Expr Nat}
    (h : PiHeadObs E n Γ (.pi A B) (.pi A' B')) :
    TyConvT E n Γ A A' × TyConvT E n (.assumption A :: Γ) B B' := by
  cases h with
  | mk X Y X' Y' hl hr cl cr hA hB =>
      have heL := HeadTrace.eq_of_normal hl (pi_headNormal A B)
      have heR := HeadTrace.eq_of_normal hr (pi_headNormal A' B')
      obtain ⟨hAX, hBY⟩ := Expr.pi.inj heL
      obtain ⟨hAX', hBY'⟩ := Expr.pi.inj heR
      cases hAX
      cases hBY
      cases hAX'
      cases hBY'
      exact ⟨hA, hB⟩

end PiHeadObs

/-! ## A typed native beta observation

All data in this fixture is constructed. It uses only native sorts, Pi
formation, beta conversion, and the actual `HeadStepT.beta` constructor.
-/

private abbrev one : Level := .succ .zero
private abbrev two : Level := .succ one
private abbrev piSort : Level := .imax one one

def betaPiHead : Expr Nat := .pi (.sort .zero) (.sort .zero)

def betaPiSource : Expr Nat :=
  .app (.lam (.sort one) betaPiHead) (.sort .zero)

def betaPiHeadTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ betaPiHead (.sort piSort) :=
  .pi Γ (.sort .zero) one (.sort .zero) one (.sort _ _) (.sort _ _)

def betaPiStep (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HeadStepT E n Γ betaPiSource betaPiHead (.sort piSort) :=
  .beta Γ (.sort one) betaPiHead (.sort .zero) (.sort piSort)
    two (.succ piSort) (.succ piSort)
    (.sort _ _) (.sort _ _) (.sort _ _)
    (betaPiHeadTy E n (.assumption (.sort one) :: Γ))
    (.sort _ _) (betaPiHeadTy E n Γ)

def betaPiCert (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    TyConvT E n Γ betaPiSource betaPiHead :=
  .of Γ betaPiSource betaPiHead piSort
    (.beta Γ (.sort one) betaPiHead (.sort .zero) (.sort piSort) two
      (.sort _ _) (betaPiHeadTy E n (.assumption (.sort one) :: Γ)) (.sort _ _))

/-- A nonempty native root-contraction trace feeds the new relation.
No model, normalization supplier, Pi row, or conversion-closure premise
is assumed. -/
def betaPiObservation (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    PiHeadObs E n Γ betaPiSource betaPiHead :=
  PiHeadObs.expand_left (.cons (betaPiStep E n Γ) (.refl _))
    (betaPiCert E n Γ) (PiHeadObs.refl (.sort .zero) (.sort .zero))

#print axioms HeadTrace.trans
#print axioms HeadTrace.normal_det
#print axioms pi_headNormal
#print axioms PiHeadObs.symm
#print axioms PiHeadObs.trans
#print axioms PiHeadObs.expand_left
#print axioms PiHeadObs.expand_right
#print axioms PiHeadObs.components
#print axioms betaPiStep
#print axioms betaPiCert
#print axioms betaPiObservation

end Rcic.Declarative.NativeValleys.NativePiHeadObs
