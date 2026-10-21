import rcic.RcicNativePiProbeComputation

/-!
# Pi-probe congruence measurement: application and mixed substitution

The index-erased probe observes no lambda body. Thus its two native
application IHs alone do not supply the result observations. The closed
typed counterexample below refutes application congruence for *bare*
`ProbeEquivT`, even with both functions typed at the same Pi and both
arguments typed at its domain. It does not assume a native conversion
between the functions, and does not refute `ConvT.app`.

For the remaining native application arm, `AppHeadActionT` and
`AppArgActionT` name two open contextual observation facts: change a native
converted head at a fixed typed argument, then change native converted
arguments at a fixed typed function. They are explicitly unproved inputs;
no global witness or strictness claim is made for them.

There is a sharper computational measurement for syntactic lambda heads
and for both endpoints of every native `letE`: the desired motive is
equivalent to the observation on the two instantiated bodies. The latter
can be split into body change at the left value and value change in the
right body. `MixedSubstEdgesT` records these two residual edges, rather
than asserting the entire application/let constructor as a model fact.
Their reflexive and binder-independent instances are supplied below.

No arbitrary mixed-substitution law or arbitrary application action is
proved. The conditional wrappers do not close these native arms globally.
`closure_claim = 0`. No new axiom, no `sorry`, no `Classical.choice`.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeCongruenceAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiCycleAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeComputationAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ## Open contextual action, with the native premises retained -/

/-- Open operational input at one native function conversion: preserve
the probes after fixing an actually typed argument. The bare head IH is
not a witness of this statement. -/
def AppHeadActionT (R : Readback) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g A B : Expr Nat} (_hf : ConvT E n Γ f g (.pi A B)) : Prop :=
  ∀ {a : Expr Nat}, HasTyT E n Γ a A →
    ProbeEquivT R E n Γ (.app f a) (.app g a)

/-- Open operational input at one actually typed function: preserve the
probes while replacing its argument by a native-convertible argument. -/
def AppArgActionT (R : Readback) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {g A B : Expr Nat} (_hg : HasTyT E n Γ g (.pi A B)) : Prop :=
  ∀ {a b : Expr Nat}, ConvT E n Γ a b A →
    ProbeEquivT R E n Γ (.app g a) (.app g b)

/-- The two contextual inputs compose to the native application arm.
This conditional theorem supplies no witness of either open input. -/
theorem convProbe_app_of_actionsT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {f g a b A B : Expr Nat}
    (hf : ConvT E n Γ f g (.pi A B)) (ha : ConvT E n Γ a b A)
    (hhead : AppHeadActionT R hf)
    (harg : AppArgActionT R (convEnds hW hΓ hf).2.1) :
    ConvProbeMotiveT R (.app Γ f g a b A B hf ha) :=
  probeEquiv_transT hW hΓ (hhead (convEnds hW hΓ ha).1) (harg ha)

/-! ## Computation exposes the exact substitution residue -/

/-- Replace both endpoints by already related computational representatives. -/
theorem probeEquiv_iff_of_endsT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {M N M' N' : Expr Nat}
    (hM : ProbeEquivT R E n Γ M M') (hN : ProbeEquivT R E n Γ N N') :
    ProbeEquivT R E n Γ M N ↔ ProbeEquivT R E n Γ M' N' := by
  constructor
  · intro h
    exact probeEquiv_transT hW hΓ (probeEquiv_symmT hM)
      (probeEquiv_transT hW hΓ h hN)
  · intro h
    exact probeEquiv_transT hW hΓ hM
      (probeEquiv_transT hW hΓ h (probeEquiv_symmT hN))

/-- At syntactic lambda heads, beta removes both applications exactly at
the observations used by this motive. -/
theorem probeEquiv_app_lam_iff_substT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) (D D' body body' a b : Expr Nat) :
    ProbeEquivT (WhStepK E n) E n Γ
        (.app (.lam D body) a) (.app (.lam D' body') b) ↔
      ProbeEquivT (WhStepK E n) E n Γ
        (instantiate0 a body) (instantiate0 b body') :=
  probeEquiv_iff_of_endsT hW hΓ
    (probeEquiv_beta hW D body a) (probeEquiv_beta hW D' body' b)

/-- Every pair of lets has the same exact two-body substitution residue. -/
theorem probeEquiv_letE_iff_substT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) (A A' value value' body body' : Expr Nat) :
    ProbeEquivT (WhStepK E n) E n Γ
        (.letE A value body) (.letE A' value' body') ↔
      ProbeEquivT (WhStepK E n) E n Γ
        (instantiate0 value body) (instantiate0 value' body') :=
  probeEquiv_iff_of_endsT hW hΓ
    (probeEquiv_zeta hW A value body) (probeEquiv_zeta hW A' value' body')

/-- Two localized, open substitution edges. The first changes only the
body; the second changes only the value. Native typed wrappers below
fix these terms to the corresponding native constructor premises. -/
structure MixedSubstEdgesT (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (value value' body body' : Expr Nat) : Prop where
  bodyAtValue : ProbeEquivT R E n Γ
    (instantiate0 value body) (instantiate0 value body')
  valueInBody : ProbeEquivT R E n Γ
    (instantiate0 value body') (instantiate0 value' body')

theorem probeEquiv_subst_of_edgesT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {value value' body body' : Expr Nat}
    (h : MixedSubstEdgesT R E n Γ value value' body body') :
    ProbeEquivT R E n Γ (instantiate0 value body) (instantiate0 value' body') :=
  probeEquiv_transT hW hΓ h.bodyAtValue h.valueInBody

/-- The exact native application measurement, retaining its actual
function and argument conversion premises. It is restricted to syntactic
lambda endpoints, where the computation equivalence is proved. -/
theorem convProbe_app_lam_iff_substT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {D D' body body' a b A B : Expr Nat}
    (hf : ConvT E n Γ (.lam D body) (.lam D' body') (.pi A B))
    (ha : ConvT E n Γ a b A) :
    ConvProbeMotiveT (WhStepK E n)
        (.app Γ (.lam D body) (.lam D' body') a b A B hf ha) ↔
      ProbeEquivT (WhStepK E n) E n Γ (instantiate0 a body) (instantiate0 b body') :=
  probeEquiv_app_lam_iff_substT hW hΓ D D' body body' a b

theorem convProbe_app_lam_of_mixedSubstT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {D D' body body' a b A B : Expr Nat}
    (hf : ConvT E n Γ (.lam D body) (.lam D' body') (.pi A B))
    (ha : ConvT E n Γ a b A)
    (hsubst : MixedSubstEdgesT (WhStepK E n) E n Γ a b body body') :
    ConvProbeMotiveT (WhStepK E n)
      (.app Γ (.lam D body) (.lam D' body') a b A B hf ha) :=
  (convProbe_app_lam_iff_substT hW hΓ hf ha).mpr
    (probeEquiv_subst_of_edgesT hW hΓ hsubst)

/-- The exact native let-congruence measurement. Its residual includes
both the body conversion at the old let binder and the changed value. -/
theorem convProbe_letE_iff_substT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A A' value value' body body' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ value value' A)
    (hb : ConvT E n (.letBinding A value :: Γ) body body' B) :
    ConvProbeMotiveT (WhStepK E n)
        (.letE Γ A A' value value' body body' B u hA hv hb) ↔
      ProbeEquivT (WhStepK E n) E n Γ
        (instantiate0 value body) (instantiate0 value' body') :=
  probeEquiv_letE_iff_substT hW hΓ A A' value value' body body'

theorem convProbe_letE_of_mixedSubstT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {A A' value value' body body' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u)) (hv : ConvT E n Γ value value' A)
    (hb : ConvT E n (.letBinding A value :: Γ) body body' B)
    (hsubst : MixedSubstEdgesT (WhStepK E n) E n Γ value value' body body') :
    ConvProbeMotiveT (WhStepK E n)
      (.letE Γ A A' value value' body body' B u hA hv hb) :=
  (convProbe_letE_iff_substT hW hΓ hA hv hb).mpr
    (probeEquiv_subst_of_edgesT hW hΓ hsubst)

/-- A constructive local residual witness at an unchanged body and value. -/
theorem mixedSubstEdges_reflT (Γ : LCtx) (value body : Expr Nat) :
    MixedSubstEdgesT R E n Γ value value body body :=
  ⟨probeEquiv_reflT _ _, probeEquiv_reflT _ _⟩

/-- If both bodies ignore the new binder, substitution exposes the
already known relation on the original bodies. This is a proved class
of the residual, without a universal substitution premise. -/
theorem mixedSubstEdges_liftT {Γ : LCtx} {M N : Expr Nat}
    (hMN : ProbeEquivT R E n Γ M N) (value value' : Expr Nat) :
    MixedSubstEdgesT R E n Γ value value' (lift 0 1 M) (lift 0 1 N) := by
  have hcancel (v X : Expr Nat) : instantiate0 v (lift 0 1 X) = X := by
    simpa only [instantiate0, Nat.sub_self, lift_zero] using
      (instantiate_lift_cancel 1 0 0 v (Nat.le_refl 0) (by decide) X)
  constructor
  · simpa only [hcancel] using hMN
  · simp only [hcancel]
    exact probeEquiv_reflT Γ N

/-- An actual witness of the entire local head-action port: native
reflexivity acts reflexively at every typed argument. -/
theorem appHeadAction_reflT {Γ : LCtx} {f A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) :
    AppHeadActionT R (.refl Γ f (.pi A B) hf) := by
  intro a _
  exact probeEquiv_reflT Γ (.app f a)

/-- An actual witness of the entire local argument-action port for a
typed lambda whose body ignores its binder. It covers every native
converted argument pair, not only the reflexive instance. -/
theorem appArgAction_lam_liftT (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {D M A B : Expr Nat}
    (hf : HasTyT E n Γ (.lam D (lift 0 1 M)) (.pi A B)) :
    AppArgActionT (WhStepK E n) hf := by
  intro a b _
  apply (probeEquiv_app_lam_iff_substT hW hΓ D D (lift 0 1 M) (lift 0 1 M) a b).mpr
  exact probeEquiv_subst_of_edgesT hW hΓ
    (mixedSubstEdges_liftT (probeEquiv_reflT Γ M) a b)

/-! ## A closed typed counterexample to bare application congruence -/

def appCounterDomain : Expr Nat := .sort (.succ .zero)
def appCounterArgument : Expr Nat := .sort .zero
def appCounterPi : Expr Nat := .pi (.sort .zero) (.sort .zero)
def appCounterLeft : Expr Nat := .lam appCounterDomain appCounterArgument
def appCounterRight : Expr Nat := .lam appCounterDomain appCounterPi

def appCounterPiTyping (Γ : LCtx) :
    HasTyT emptyEnv 0 Γ appCounterPi appCounterDomain :=
  .conv Γ appCounterPi (.sort (.imax (.succ .zero) (.succ .zero)))
    appCounterDomain (.succ (.imax (.succ .zero) (.succ .zero)))
    (.pi Γ (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
      (.sort Γ .zero) (.sort _ .zero))
    (.sorts Γ (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun _ => rfl))

def appCounterArgumentTyping : HasTyT emptyEnv 0 [] appCounterArgument appCounterDomain :=
  .sort [] .zero

def appCounterLeftTyping :
    HasTyT emptyEnv 0 [] appCounterLeft (.pi appCounterDomain appCounterDomain) :=
  .lam [] appCounterDomain (.succ (.succ .zero)) appCounterArgument appCounterDomain
    (.sort [] (.succ .zero)) (.sort _ .zero)

def appCounterRightTyping :
    HasTyT emptyEnv 0 [] appCounterRight (.pi appCounterDomain appCounterDomain) :=
  .lam [] appCounterDomain (.succ (.succ .zero)) appCounterPi appCounterDomain
    (.sort [] (.succ .zero)) (appCounterPiTyping _)

def appCounterLeftAppTyping :
    HasTyT emptyEnv 0 [] (.app appCounterLeft appCounterArgument) appCounterDomain :=
  .app [] appCounterLeft appCounterArgument appCounterDomain appCounterDomain
    appCounterLeftTyping appCounterArgumentTyping

def appCounterRightAppTyping :
    HasTyT emptyEnv 0 [] (.app appCounterRight appCounterArgument) appCounterDomain :=
  .app [] appCounterRight appCounterArgument appCounterDomain appCounterDomain
    appCounterRightTyping appCounterArgumentTyping

/-- The fixed typed left function inhabits the whole local argument
action: all native-convertible arguments are admitted by this witness. -/
theorem appCounterLeft_appArgAction :
    AppArgActionT (WhStepK emptyEnv 0) appCounterLeftTyping :=
  appArgAction_lam_liftT .empty .nil (M := appCounterArgument) appCounterLeftTyping

/-- Its native reflexive conversion inhabits the whole local head action. -/
theorem appCounterLeft_appHeadAction :
    AppHeadActionT (WhStepK emptyEnv 0)
      (.refl [] appCounterLeft (.pi appCounterDomain appCounterDomain) appCounterLeftTyping) :=
  appHeadAction_reflT appCounterLeftTyping

/-- Both heads are normal lambdas, so the head-only motive observes no
body information, even though the two functions share a native Pi type. -/
theorem appCounter_heads_related :
    ProbeEquivT (WhStepK emptyEnv 0) emptyEnv 0 [] appCounterLeft appCounterRight :=
  probeEquiv_lam appCounterDomain appCounterDomain appCounterArgument appCounterPi

theorem appCounter_argument_related :
    ProbeEquivT (WhStepK emptyEnv 0) emptyEnv 0 [] appCounterArgument appCounterArgument :=
  probeEquiv_reflT [] appCounterArgument

theorem appCounter_left_reads_sort :
    RedR (WhStepK emptyEnv 0) [] (.app appCounterLeft appCounterArgument) (.sort .zero) :=
  redR_single (.ctx (.beta appCounterDomain appCounterArgument appCounterArgument))

theorem appCounter_right_reads_pi :
    RedR (WhStepK emptyEnv 0) [] (.app appCounterRight appCounterArgument) appCounterPi :=
  redR_single (.ctx (.beta appCounterDomain appCounterPi appCounterArgument))

theorem appCounter_right_not_sort (u : Level) :
    ¬ RedR (WhStepK emptyEnv 0) [] (.app appCounterRight appCounterArgument) (.sort u) := by
  intro hread
  have hnormal : NormalR (WhStepK emptyEnv 0) [] (.sort u) :=
    fun _ hs => (readbackLaws_whStepK emptyEnv 0).sort_normal _ _ _ hs
  have hpi : RedR (WhStepK emptyEnv 0) [] appCounterPi (.sort u) :=
    (redR_beta_iff (.empty : EnvWfT emptyEnv) hnormal).mp hread
  exact Expr.noConfusion (redR_pi_eq (readbackLaws_whStepK emptyEnv 0) hpi)

theorem appCounter_applications_not_related :
    ¬ ProbeEquivT (WhStepK emptyEnv 0) emptyEnv 0 []
      (.app appCounterLeft appCounterArgument) (.app appCounterRight appCounterArgument) := by
  intro h
  obtain ⟨u, hread⟩ := h.1.sorts ⟨.zero, appCounter_left_reads_sort⟩
  exact appCounter_right_not_sort u hread

/-- The left application has an active sort probe. -/
theorem appCounter_left_sort_probe :
    LRSCoreT (WhStepK emptyEnv 0) emptyEnv 0 []
      (.app appCounterLeft appCounterArgument) (.app appCounterLeft appCounterArgument)
      appCounterDomain .sort := by
  rw [lrSCoreT_sort_iff]
  exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero,
    appCounter_left_reads_sort, appCounter_left_reads_sort⟩

/-- The right application has an active, well-formed Pi probe. -/
theorem appCounter_right_pi_probe :
    LRSCoreT (WhStepK emptyEnv 0) emptyEnv 0 []
      (.app appCounterRight appCounterArgument) (.app appCounterRight appCounterArgument)
      appCounterDomain (.pi .bot []) := by
  have hseed := piProbe_diagT_of_typing (R := WhStepK emptyEnv 0)
    (.nil : CtxWfT emptyEnv 0 [])
    (appCounterPiTyping [])
  have hrel := piProbe_of_transportT
    (probeEquiv_beta (.empty : EnvWfT emptyEnv)
      appCounterDomain appCounterPi appCounterArgument).2 hseed
  exact piProbe_right_diagonalT_noUnique .empty .nil hrel

/-- The deliberately too-weak congruence assertion: it retains native
typing but replaces native conversion premises by the bare head motive. -/
def BareTypedAppCongruenceT (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f g a b A B : Expr Nat},
    HasTyT E n Γ f (.pi A B) → HasTyT E n Γ g (.pi A B) →
    HasTyT E n Γ a A → HasTyT E n Γ b A →
    ProbeEquivT R E n Γ f g → ProbeEquivT R E n Γ a b →
    ProbeEquivT R E n Γ (.app f a) (.app g b)

/-- Kernel counterexample to bare-motive application congruence. No
native `ConvT` between the two functions is asserted or used. -/
theorem not_bareTypedAppCongruenceT :
    ¬ BareTypedAppCongruenceT (WhStepK emptyEnv 0) emptyEnv 0 := by
  intro h
  exact appCounter_applications_not_related
    (h .nil appCounterLeftTyping appCounterRightTyping
      appCounterArgumentTyping appCounterArgumentTyping
      appCounter_heads_related appCounter_argument_related)

/-- Closed admitted environment, well-formed context, common native
function type, typed applications, and genuinely present output probes. -/
theorem appCounter_typed_nonvacuity :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv 0 []) ∧
    Nonempty (HasTyT emptyEnv 0 [] appCounterLeft (.pi appCounterDomain appCounterDomain)) ∧
    Nonempty (HasTyT emptyEnv 0 [] appCounterRight (.pi appCounterDomain appCounterDomain)) ∧
    Nonempty (HasTyT emptyEnv 0 [] appCounterArgument appCounterDomain) ∧
    Nonempty (HasTyT emptyEnv 0 [] (.app appCounterLeft appCounterArgument) appCounterDomain) ∧
    Nonempty (HasTyT emptyEnv 0 [] (.app appCounterRight appCounterArgument) appCounterDomain) ∧
    ProbeEquivT (WhStepK emptyEnv 0) emptyEnv 0 [] appCounterLeft appCounterRight ∧
    ProbeEquivT (WhStepK emptyEnv 0) emptyEnv 0 [] appCounterArgument appCounterArgument ∧
    ¬ ProbeEquivT (WhStepK emptyEnv 0) emptyEnv 0 []
      (.app appCounterLeft appCounterArgument) (.app appCounterRight appCounterArgument) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨appCounterLeftTyping⟩, ⟨appCounterRightTyping⟩,
    ⟨appCounterArgumentTyping⟩, ⟨appCounterLeftAppTyping⟩, ⟨appCounterRightAppTyping⟩,
    appCounter_heads_related, appCounter_argument_related, appCounter_applications_not_related⟩

/-! ## Native typed instances of the conditional substitution consumers -/

def selfLambdaAppConversion : ConvT emptyEnv 0 []
    (.app appCounterLeft appCounterArgument) (.app appCounterLeft appCounterArgument)
    appCounterDomain :=
  .app [] appCounterLeft appCounterLeft appCounterArgument appCounterArgument
    appCounterDomain appCounterDomain
    (.refl [] appCounterLeft _ appCounterLeftTyping)
    (.refl [] appCounterArgument _ appCounterArgumentTyping)

theorem selfLambdaApp_motive :
    ConvProbeMotiveT (WhStepK emptyEnv 0) selfLambdaAppConversion :=
  convProbe_app_lam_of_mixedSubstT .empty .nil
    (.refl [] appCounterLeft _ appCounterLeftTyping)
    (.refl [] appCounterArgument _ appCounterArgumentTyping)
    (mixedSubstEdges_reflT [] appCounterArgument appCounterArgument)

/-- The same native application also composes the two full local action
ports exhibited above; neither port is supplied merely at this argument. -/
theorem selfLambdaApp_motive_of_actions :
    ConvProbeMotiveT (WhStepK emptyEnv 0) selfLambdaAppConversion :=
  convProbe_app_of_actionsT .empty .nil
    (.refl [] appCounterLeft _ appCounterLeftTyping)
    (.refl [] appCounterArgument _ appCounterArgumentTyping)
    appCounterLeft_appHeadAction appCounterLeft_appArgAction

def selfLetConversion : ConvT emptyEnv 0 []
    (.letE appCounterDomain appCounterArgument appCounterArgument)
    (.letE appCounterDomain appCounterArgument appCounterArgument) appCounterDomain :=
  .letE [] appCounterDomain appCounterDomain appCounterArgument appCounterArgument
    appCounterArgument appCounterArgument appCounterDomain (.succ (.succ .zero))
    (.refl [] appCounterDomain _ (.sort [] (.succ .zero)))
    (.refl [] appCounterArgument _ appCounterArgumentTyping)
    (.refl [.letBinding appCounterDomain appCounterArgument] appCounterArgument _ (.sort _ .zero))

theorem selfLet_motive : ConvProbeMotiveT (WhStepK emptyEnv 0) selfLetConversion :=
  convProbe_letE_of_mixedSubstT .empty .nil
    (.refl [] appCounterDomain _ (.sort [] (.succ .zero)))
    (.refl [] appCounterArgument _ appCounterArgumentTyping)
    (.refl [.letBinding appCounterDomain appCounterArgument] appCounterArgument _ (.sort _ .zero))
    (mixedSubstEdges_reflT [] appCounterArgument appCounterArgument)

theorem selfLet_sort_probe :
    LRSCoreT (WhStepK emptyEnv 0) emptyEnv 0 []
      (.letE appCounterDomain appCounterArgument appCounterArgument)
      (.letE appCounterDomain appCounterArgument appCounterArgument) appCounterDomain .sort := by
  have hread : RedR (WhStepK emptyEnv 0) []
      (.letE appCounterDomain appCounterArgument appCounterArgument) (.sort .zero) :=
    redR_single (.ctx (.zeta appCounterDomain appCounterArgument appCounterArgument))
  rw [lrSCoreT_sort_iff]
  exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero, hread, hread⟩

-- BEGIN RCIC_PI_PROBE_CONGRUENCE_ROOTS
#print axioms AppHeadActionT
#print axioms AppArgActionT
#print axioms convProbe_app_of_actionsT
#print axioms probeEquiv_iff_of_endsT
#print axioms probeEquiv_app_lam_iff_substT
#print axioms probeEquiv_letE_iff_substT
#print axioms MixedSubstEdgesT
#print axioms probeEquiv_subst_of_edgesT
#print axioms convProbe_app_lam_iff_substT
#print axioms convProbe_app_lam_of_mixedSubstT
#print axioms convProbe_letE_iff_substT
#print axioms convProbe_letE_of_mixedSubstT
#print axioms mixedSubstEdges_reflT
#print axioms mixedSubstEdges_liftT
#print axioms appHeadAction_reflT
#print axioms appArgAction_lam_liftT
#print axioms appCounterDomain
#print axioms appCounterArgument
#print axioms appCounterPi
#print axioms appCounterLeft
#print axioms appCounterRight
#print axioms appCounterPiTyping
#print axioms appCounterArgumentTyping
#print axioms appCounterLeftTyping
#print axioms appCounterRightTyping
#print axioms appCounterLeftAppTyping
#print axioms appCounterRightAppTyping
#print axioms appCounterLeft_appArgAction
#print axioms appCounterLeft_appHeadAction
#print axioms appCounter_heads_related
#print axioms appCounter_argument_related
#print axioms appCounter_left_reads_sort
#print axioms appCounter_right_reads_pi
#print axioms appCounter_right_not_sort
#print axioms appCounter_applications_not_related
#print axioms appCounter_left_sort_probe
#print axioms appCounter_right_pi_probe
#print axioms BareTypedAppCongruenceT
#print axioms not_bareTypedAppCongruenceT
#print axioms appCounter_typed_nonvacuity
#print axioms selfLambdaAppConversion
#print axioms selfLambdaApp_motive
#print axioms selfLambdaApp_motive_of_actions
#print axioms selfLetConversion
#print axioms selfLet_motive
#print axioms selfLet_sort_probe
-- END RCIC_PI_PROBE_CONGRUENCE_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeCongruenceAudit
