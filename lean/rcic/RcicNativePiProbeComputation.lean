import rcic.RcicNativePiProbeAlgebra
import rcic.RcicNativePiModelBetaObstruction

/-!
# Pi-probe computation audit: local readback cancellation

The beta, zeta, local-zeta, delta and literal cases preserve each specified
normal readback.  Reverse expansion composes one readback step.  Forward
contraction cancels that step using source-local uniqueness: the extra K
rules are excluded by the source shape, and the remaining step is pinned
by the landed context-readback determinism theorem.

No global `NormalUniqueR`, confluence or approximation transport is used.
The eta case of the index-erased motive has a separate, explicit typed
head-exclusion input.  Its native constructor at an actual sort index is
already excluded by its Pi-shaped index.  Lambda instances below inhabit
the local head-exclusion input; they do not supply its universal version.

All declarations are additive.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeComputationAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelTermDFundAudit
open Rcic.Declarative.NativeValleys.PiCycleAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-- A source outside the constant-application shapes of the extra K rules.
This includes a bare constant, which may still unfold by delta. -/
def NotConstApplication (M : Expr Nat) : Prop :=
  ∀ (r : Nat) (ls : List Level) (pre : List (Expr Nat)) (x : Expr Nat),
    M ≠ .app (foldApps (.const r ls) pre) x

/-- At these sources every K step is an existing context-readback step.
The application case only moves this syntactic restriction to the head. -/
theorem whStepK_to_ctx_of_notConstApplication {Γ : LCtx} {M N : Expr Nat}
    (hs : WhStepK E n Γ M N) :
    NotConstApplication M → WhStepCtx E Γ M N := by
  induction hs with
  | ctx hs => exact fun _ => hs
  | @pmajor r ls pre canon x rhs P hI hP hcanon hx =>
      intro hshape
      exact (hshape r ls pre x (by simp only [recCall, foldApps_snoc])).elim
  | @recArg r ls m pre x x' hm hrec hs ih =>
      intro hshape
      exact (hshape r ls pre x (by simp only [foldApps_snoc])).elim
  | @appHead f f' a hs ih =>
      intro hshape
      apply WhStepCtx.appHead
      apply ih
      intro r ls pre x heq
      apply hshape r ls (pre ++ [x]) a
      simpa only [foldApps_snoc] using congrArg (fun t => Expr.app t a) heq

/-- Cancel a specified first step from a normal readback.  The uniqueness
input concerns this one source, rather than all normal forms of `R`. -/
theorem redR_contract_of_source_unique {Γ : LCtx} {M N X : Expr Nat}
    (hs : R Γ M N) (hunique : ∀ Y, R Γ M Y → Y = N)
    (hX : NormalR R Γ X) (hread : RedR R Γ M X) : RedR R Γ N X := by
  cases hread with
  | refl => exact (hX N hs).elim
  | step hs' htail =>
      have heq := hunique _ hs'
      cases heq
      exact htail

/-- The readback of each permitted context computation is unchanged at
every specified normal endpoint.  Only the forward direction uses the
landed deterministic context readback. -/
theorem redR_ctx_iff_of_notConstApplication (hW : EnvWfT E)
    {Γ : LCtx} {M N X : Expr Nat} (hs : WhStepCtx E Γ M N)
    (hshape : NotConstApplication M) (hX : NormalR (WhStepK E n) Γ X) :
    RedR (WhStepK E n) Γ M X ↔ RedR (WhStepK E n) Γ N X := by
  constructor
  · exact redR_contract_of_source_unique (.ctx hs)
      (fun Y hY => (whDetCtx_of_envWfT hW Γ hs
        (whStepK_to_ctx_of_notConstApplication hY hshape)).symm) hX
  · exact fun hread => .step (.ctx hs) hread

theorem redR_beta_iff (hW : EnvWfT E) {Γ : LCtx} {A body arg X : Expr Nat}
    (hX : NormalR (WhStepK E n) Γ X) :
    RedR (WhStepK E n) Γ (.app (.lam A body) arg) X ↔
      RedR (WhStepK E n) Γ (instantiate0 arg body) X := by
  apply redR_ctx_iff_of_notConstApplication hW (.beta A body arg) _ hX
  intro r ls pre x heq
  exact F8EtaK.foldApps_const_ne_lam_any (Expr.app.inj heq).1.symm

theorem redR_zeta_iff (hW : EnvWfT E) {Γ : LCtx} {A value body X : Expr Nat}
    (hX : NormalR (WhStepK E n) Γ X) :
    RedR (WhStepK E n) Γ (.letE A value body) X ↔
      RedR (WhStepK E n) Γ (instantiate0 value body) X := by
  apply redR_ctx_iff_of_notConstApplication hW (.zeta A value body) _ hX
  intro r ls pre x heq
  exact Expr.noConfusion heq

theorem redR_zetaLocal_iff (hW : EnvWfT E) {Γ : LCtx} {i : Nat} {value X : Expr Nat}
    (hv : lookupValue Γ i = some value) (hX : NormalR (WhStepK E n) Γ X) :
    RedR (WhStepK E n) Γ (.bvar i) X ↔ RedR (WhStepK E n) Γ value X := by
  apply redR_ctx_iff_of_notConstApplication hW (.zetaLocal hv) _ hX
  intro r ls pre x heq
  exact Expr.noConfusion heq

theorem redR_delta_iff (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {body X : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some body)
    (hX : NormalR (WhStepK E n) Γ X) :
    RedR (WhStepK E n) Γ (.const r ls) X ↔
      RedR (WhStepK E n) Γ (instantiateLevels ls body) X := by
  apply redR_ctx_iff_of_notConstApplication hW (.delta hm hb) _ hX
  intro r' ls' pre x heq
  exact Expr.noConfusion heq

theorem redR_lit_iff (hW : EnvWfT E) {Γ : LCtx} {t : Nat} {X : Expr Nat}
    (hX : NormalR (WhStepK E n) Γ X) :
    RedR (WhStepK E n) Γ (.lit t) X ↔ RedR (WhStepK E n) Γ (natExpand t) X := by
  apply redR_ctx_iff_of_notConstApplication hW (.lit t) _ hX
  intro r ls pre x heq
  exact Expr.noConfusion heq

/-- Native literal expansion has the same exact endpoint as readback. -/
theorem redR_literalExpansion_iff (hW : EnvWfT E) {Γ : LCtx} {t : Nat}
    {exp X : Expr Nat} (hexp : LiteralExpansion t exp)
    (hX : NormalR (WhStepK E n) Γ X) :
    RedR (WhStepK E n) Γ (.lit t) X ↔ RedR (WhStepK E n) Γ exp X := by
  cases hexp
  exact redR_lit_iff hW hX

/-! ## Bidirectional probe observations for primitive computation -/

theorem probeEquiv_beta (hW : EnvWfT E) {Γ : LCtx} (A body arg : Expr Nat) :
    ProbeEquivT (WhStepK E n) E n Γ (.app (.lam A body) arg) (instantiate0 arg body) :=
  probeEquiv_of_readback_iffT (readbackLaws_whStepK E n)
    (fun _ hX => redR_beta_iff hW hX)

theorem probeEquiv_zeta (hW : EnvWfT E) {Γ : LCtx} (A value body : Expr Nat) :
    ProbeEquivT (WhStepK E n) E n Γ (.letE A value body) (instantiate0 value body) :=
  probeEquiv_of_readback_iffT (readbackLaws_whStepK E n)
    (fun _ hX => redR_zeta_iff hW hX)

theorem probeEquiv_zetaLocal (hW : EnvWfT E) {Γ : LCtx} {i : Nat} {value : Expr Nat}
    (hv : lookupValue Γ i = some value) :
    ProbeEquivT (WhStepK E n) E n Γ (.bvar i) value :=
  probeEquiv_of_readback_iffT (readbackLaws_whStepK E n)
    (fun _ hX => redR_zetaLocal_iff hW hv hX)

theorem probeEquiv_delta (hW : EnvWfT E) {Γ : LCtx} {r : Nat} (ls : List Level)
    {m : CheckedMember} {body : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some body) :
    ProbeEquivT (WhStepK E n) E n Γ (.const r ls) (instantiateLevels ls body) :=
  probeEquiv_of_readback_iffT (readbackLaws_whStepK E n)
    (fun _ hX => redR_delta_iff hW hm hb hX)

theorem probeEquiv_lit (hW : EnvWfT E) {Γ : LCtx} {t : Nat} {exp : Expr Nat}
    (hexp : LiteralExpansion t exp) :
    ProbeEquivT (WhStepK E n) E n Γ (.lit t) exp :=
  probeEquiv_of_readback_iffT (readbackLaws_whStepK E n)
    (fun _ hX => redR_literalExpansion_iff hW hexp hX)

theorem convProbe_beta (hW : EnvWfT E) {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B) (harg : HasTyT E n Γ arg A) :
    ConvProbeMotiveT (WhStepK E n) (.beta Γ A body arg B u hA hbody harg) :=
  probeEquiv_beta hW A body arg

theorem convProbe_zeta (hW : EnvWfT E) {Γ : LCtx} {A value body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hbody : HasTyT E n (.letBinding A value :: Γ) body B) :
    ConvProbeMotiveT (WhStepK E n) (.zeta Γ A value body B u hA hv hbody) :=
  probeEquiv_zeta hW A value body

theorem convProbe_zetaLocal (hW : EnvWfT E) {Γ : LCtx} {i : Nat} {A value : Expr Nat}
    (hv : lookupValue Γ i = some value) (hA : lookupType Γ i = some A)
    (hty : HasTyT E n Γ value A) :
    ConvProbeMotiveT (WhStepK E n) (.zetaLocal Γ i A value hv hA hty) :=
  probeEquiv_zetaLocal hW hv

theorem convProbe_delta (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {body : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some body)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hty : HasTyT E n Γ (instantiateLevels ls body) (instantiateLevels ls m.mtype)) :
    ConvProbeMotiveT (WhStepK E n)
      (.delta Γ r ls m body hm hb htr hlen hwf hty) :=
  probeEquiv_delta hW ls hm hb

theorem convProbe_lit (hW : EnvWfT E) {Γ : LCtx} {t : Nat} {exp T : Expr Nat}
    (hexp : LiteralExpansion t exp) (hty : HasTyT E n Γ exp T) :
    ConvProbeMotiveT (WhStepK E n) (.lit Γ t exp T hexp hty) :=
  probeEquiv_lit hW hexp

/-! ## Lambda observation and the exact eta input -/

/-- A lambda remains normal for K readback: its source excludes every
additional K rule, then the landed context-readback result applies. -/
theorem whStepK_lam_false {Γ : LCtx} {A body X : Expr Nat}
    (hs : WhStepK E n Γ (.lam A body) X) : False := by
  apply whStepRecCtx_lam_false
  apply whStepCtx_to_whStepRecCtx
  apply whStepK_to_ctx_of_notConstApplication hs
  intro r ls pre x heq
  exact Expr.noConfusion heq

theorem normalR_lam {Γ : LCtx} (A body : Expr Nat) :
    NormalR (WhStepK E n) Γ (.lam A body) :=
  fun _ hs => whStepK_lam_false hs

theorem redR_lam_eq {Γ : LCtx} {A body X : Expr Nat}
    (hread : RedR (WhStepK E n) Γ (.lam A body) X) : X = .lam A body :=
  redR_of_normal (normalR_lam A body) hread

theorem not_redR_lam_sort {Γ : LCtx} {A body : Expr Nat} (u : Level) :
    ¬ RedR (WhStepK E n) Γ (.lam A body) (.sort u) :=
  fun hread => Expr.noConfusion (redR_lam_eq hread)

theorem not_redR_lam_pi {Γ : LCtx} {A body : Expr Nat} (C D : Expr Nat) :
    ¬ RedR (WhStepK E n) Γ (.lam A body) (.pi C D) :=
  fun hread => Expr.noConfusion (redR_lam_eq hread)

/-- Both lambda endpoints have no type probe, independently of their
annotation and body conversions. -/
theorem probeEquiv_lam {Γ : LCtx} (A A' body body' : Expr Nat) :
    ProbeEquivT (WhStepK E n) E n Γ (.lam A body) (.lam A' body') :=
  probeEquiv_of_no_probesT not_redR_lam_sort not_redR_lam_pi
    not_redR_lam_sort not_redR_lam_pi

theorem convProbe_lam {Γ : LCtx} {A A' body body' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hbody : ConvT E n (.assumption A :: Γ) body body' B) :
    ConvProbeMotiveT (WhStepK E n) (.lam Γ A A' body body' B u hA hbody) :=
  probeEquiv_lam A A' body body'

/-- Local absence of exactly the sort and well-formed-Pi observations
consumed by the index-erased probe algebra. -/
def FunctionNoTypeProbeAtT (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (f : Expr Nat) : Prop :=
  (∀ u, ¬ RedR R Γ f (.sort u)) ∧
  ∀ A B, RedR R Γ f (.pi A B) → CtxWfT E n (.assumption A :: Γ) → False

/-- The remaining typed-local input for reverse eta after the conversion
index has been erased.  It is a premise, not a proved canonical-form law. -/
def FunctionNoTypeProbeT (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f A B : Expr Nat},
    HasTyT E n Γ f (.pi A B) → FunctionNoTypeProbeAtT R E n Γ f

/-- Constructive local nonvacuity for the eta input: every syntactic lambda
has neither of the two observations, in any context. -/
theorem functionNoTypeProbeAt_lam {Γ : LCtx} (A body : Expr Nat) :
    FunctionNoTypeProbeAtT (WhStepK E n) E n Γ (.lam A body) := by
  exact ⟨not_redR_lam_sort, fun A' B' hread _ => not_redR_lam_pi A' B' hread⟩

/-- Exact characterization of the extra eta obligation in the erased
motive.  Reverse transport has no possible lambda-head observation, so
it is equivalent to the stated local exclusion fact for `f`. -/
theorem probeEquiv_eta_iff_functionNoTypeProbeAt {Γ : LCtx} (A f : Expr Nat) :
    ProbeEquivT (WhStepK E n) E n Γ
        (.lam A (.app (lift 0 1 f) (.bvar 0))) f ↔
      FunctionNoTypeProbeAtT (WhStepK E n) E n Γ f := by
  constructor
  · intro h
    constructor
    · intro u hread
      obtain ⟨v, hlam⟩ := h.2.sorts ⟨u, hread⟩
      exact not_redR_lam_sort v hlam
    · intro C D hread hΓC
      obtain ⟨C', D', hlam, _, _⟩ := h.2.pis hread hΓC
      exact not_redR_lam_pi C' D' hlam
  · intro hno
    exact ⟨probeTransport_of_no_probesT not_redR_lam_sort not_redR_lam_pi,
      probeTransport_of_no_wf_probesT hno.1 hno.2⟩

theorem probeEquiv_eta_of_functionNoTypeProbeAt {Γ : LCtx} (A : Expr Nat)
    {f : Expr Nat} (hno : FunctionNoTypeProbeAtT (WhStepK E n) E n Γ f) :
    ProbeEquivT (WhStepK E n) E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f :=
  (probeEquiv_eta_iff_functionNoTypeProbeAt A f).mpr hno

theorem convProbe_eta_of_functionNoTypeProbe
    (hno : FunctionNoTypeProbeT (WhStepK E n) E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) :
    ConvProbeMotiveT (WhStepK E n) (.eta Γ f A B hf) :=
  probeEquiv_eta_of_functionNoTypeProbeAt A (hno hΓ hf)

/-- A native eta conversion at the landed, closed lambda fixture. -/
def etaLambdaConversion (E : ResolvedEnv) (n : Nat) :
    ConvT E n []
      (.lam (.sort .zero) (.app (lift 0 1 etaIdPiPropFn) (.bvar 0)))
      etaIdPiPropFn (.pi (.sort .zero) (.sort .zero)) :=
  .eta [] etaIdPiPropFn (.sort .zero) (.sort .zero) (hasTyT_etaIdPiPropFn E n)

/-- The eta local input is inhabited by the same actually function-typed
endpoint; this uses no universal exclusion field. -/
theorem etaLambdaInput (E : ResolvedEnv) (n : Nat) :
    FunctionNoTypeProbeAtT (WhStepK E n) E n [] etaIdPiPropFn :=
  functionNoTypeProbeAt_lam (.sort .zero) idPiProp

/-- A closed native typed family demonstrating that the local eta input
and the corresponding motive hold together without a global premise. -/
theorem etaLambda_nonvacuity (E : ResolvedEnv) (n : Nat) :
    Nonempty (CtxWfT E n []) ∧
    Nonempty (HasTyT E n [] etaIdPiPropFn (.pi (.sort .zero) (.sort .zero))) ∧
    FunctionNoTypeProbeAtT (WhStepK E n) E n [] etaIdPiPropFn ∧
    ConvProbeMotiveT (WhStepK E n) (etaLambdaConversion E n) :=
  ⟨⟨.nil⟩, ⟨hasTyT_etaIdPiPropFn E n⟩, etaLambdaInput E n,
    probeEquiv_eta_of_functionNoTypeProbeAt (.sort .zero) (etaLambdaInput E n)⟩

/-! ## Active typed computation fixtures -/

/-- Starting from an inhabited target probe, the proved equivalence
supplies the source diagonal and both oriented links without uniqueness. -/
theorem piProbe_active_from_target (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {M N I : Expr Nat} (he : ProbeEquivT R E n Γ M N)
    (hNN : LRSCoreT R E n Γ N N I (.pi .bot [])) :
    LRSCoreT R E n Γ M M I (.pi .bot []) ∧
    LRSCoreT R E n Γ M N I (.pi .bot []) ∧
    LRSCoreT R E n Γ N M I (.pi .bot []) := by
  have hNM := piProbe_of_transportT he.2 hNN
  have hMM := piProbe_right_diagonalT_noUnique hW hΓ hNM
  exact ⟨hMM, piProbe_of_transportT he.1 hMM, hNM⟩

theorem sortProbe_active_from_target {Γ : LCtx} {M N I : Expr Nat}
    (he : ProbeEquivT R E n Γ M N) (hNN : LRSCoreT R E n Γ N N I .sort) :
    LRSCoreT R E n Γ M M I .sort ∧
    LRSCoreT R E n Γ M N I .sort ∧ LRSCoreT R E n Γ N M I .sort := by
  have hNM := sortProbe_of_transportT he.2 hNN
  have hMM := sortProbe_right_diagonalT hNM
  exact ⟨hMM, sortProbe_of_transportT he.1 hMM, hNM⟩

/- The landed dependent-beta obstruction fixture has a successful typed
Pi probe on both sides of its actual native beta conversion. -/
open PiModelBetaObstructionAudit in
theorem betaPi_active :
    Nonempty (ConvT emptyEnv 0 [] betaSource betaTarget (.sort betaResultLevel)) ∧
    LRSCoreT (WhStepK emptyEnv 0) emptyEnv 0 [] betaSource betaSource
      (.sort betaResultLevel) (.pi .bot []) ∧
    LRSCoreT (WhStepK emptyEnv 0) emptyEnv 0 [] betaSource betaTarget
      (.sort betaResultLevel) (.pi .bot []) ∧
    LRSCoreT (WhStepK emptyEnv 0) emptyEnv 0 [] betaTarget betaSource
      (.sort betaResultLevel) (.pi .bot []) := by
  have he : ProbeEquivT (WhStepK emptyEnv 0) emptyEnv 0 [] betaSource betaTarget :=
    probeEquiv_beta nativeEmptyEnvWf (.sort betaUniverse) betaBody betaArgument
  exact ⟨⟨betaConversion⟩, piProbe_active_from_target nativeEmptyEnvWf .nil he
    (piProbe_diagT_of_typing .nil betaTargetTyping)⟩

/-- A local let returning its stored Pi value. -/
def zetaPiSource : Expr Nat := .letE (.sort idPiPropSort) idPiProp (.bvar 0)

/-- Actual native zeta, using the landed closed-Pi typing and local lookup. -/
def zetaPiConversion (E : ResolvedEnv) (n : Nat) :
    ConvT E n [] zetaPiSource idPiProp (.sort idPiPropSort) :=
  .zeta [] (.sort idPiPropSort) idPiProp (.bvar 0) (.sort idPiPropSort)
    (.succ idPiPropSort) (.sort [] idPiPropSort) (hasTyT_idPiProp_at E n [])
    (.bvar zetaLocalPiCtx 0 (.sort idPiPropSort) rfl)

theorem zetaPi_active (hW : EnvWfT E) :
    Nonempty (ConvT E n [] zetaPiSource idPiProp (.sort idPiPropSort)) ∧
    LRSCoreT (WhStepK E n) E n [] zetaPiSource zetaPiSource
      (.sort idPiPropSort) (.pi .bot []) ∧
    LRSCoreT (WhStepK E n) E n [] zetaPiSource idPiProp
      (.sort idPiPropSort) (.pi .bot []) ∧
    LRSCoreT (WhStepK E n) E n [] idPiProp zetaPiSource
      (.sort idPiPropSort) (.pi .bot []) := by
  have he : ProbeEquivT (WhStepK E n) E n [] zetaPiSource idPiProp :=
    probeEquiv_zeta hW (.sort idPiPropSort) idPiProp (.bvar 0)
  exact ⟨⟨zetaPiConversion E n⟩, piProbe_active_from_target hW .nil he
    (piProbe_diagT_of_typing .nil (hasTyT_idPiProp_at E n []))⟩

/-- The existing well-formed local-let fixture exercises the bvar readback
with an inhabited Pi probe, rather than a vacuous closed context. -/
theorem zetaLocalPi_active (hW : EnvWfT E) :
    Nonempty (CtxWfT E n zetaLocalPiCtx) ∧
    Nonempty (ConvT E n zetaLocalPiCtx (.bvar 0) idPiProp (.sort idPiPropSort)) ∧
    LRSCoreT (WhStepK E n) E n zetaLocalPiCtx (.bvar 0) (.bvar 0)
      (.sort idPiPropSort) (.pi .bot []) ∧
    LRSCoreT (WhStepK E n) E n zetaLocalPiCtx (.bvar 0) idPiProp
      (.sort idPiPropSort) (.pi .bot []) ∧
    LRSCoreT (WhStepK E n) E n zetaLocalPiCtx idPiProp (.bvar 0)
      (.sort idPiPropSort) (.pi .bot []) := by
  have he : ProbeEquivT (WhStepK E n) E n zetaLocalPiCtx (.bvar 0) idPiProp :=
    probeEquiv_zetaLocal hW rfl
  have hΓ := zetaLocalPiCtx_wf E n
  exact ⟨⟨hΓ⟩, ⟨zetaLocalPiCtx_conv E n⟩, piProbe_active_from_target hW hΓ he
    (piProbe_diagT_of_typing hΓ (hasTyT_idPiProp_at E n zetaLocalPiCtx))⟩

/-- The landed transparent-sort definition exercises the sort observation
at an admitted, actually inhabited delta equation. -/
theorem deltaSort_active (n : Nat) :
    Nonempty (ConvT defSortEnv n [] (.const 0 []) (.sort .zero) (.sort (.succ .zero))) ∧
    LRSCoreT (WhStepK defSortEnv n) defSortEnv n [] (.const 0 []) (.const 0 [])
      (.sort (.succ .zero)) .sort ∧
    LRSCoreT (WhStepK defSortEnv n) defSortEnv n [] (.const 0 []) (.sort .zero)
      (.sort (.succ .zero)) .sort ∧
    LRSCoreT (WhStepK defSortEnv n) defSortEnv n [] (.sort .zero) (.const 0 [])
      (.sort (.succ .zero)) .sort := by
  have he : ProbeEquivT (WhStepK defSortEnv n) defSortEnv n []
      (.const 0 []) (.sort .zero) :=
    probeEquiv_delta defSortEnvWfT (r := 0) []
      (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩) rfl rfl
  exact ⟨(defSortEnv_delta_step_and_raw_refuted n EnvI.bot).1,
    sortProbe_active_from_target he (sortProbe_diagT [] .zero (.succ .zero))⟩

/-- Ref 1 aliases the landed transparent sort definition at ref 0. The
native literal expansion of zero therefore has an active sort probe. -/
def literalSortMember : CheckedMember :=
  ⟨.definitionM, 0, .sort (.succ .zero), some (.const 0 [])⟩

def literalSortEnv : ResolvedEnv := extendEnv defSortEnv 1 literalSortMember

/-- The alias is admitted by the native environment judgment, with its
body typed using the already admitted ref 0. -/
def literalSortEnvWfT : EnvWfT literalSortEnv :=
  .definition defSortEnv 1 (.sort (.succ .zero)) (.const 0 []) (.succ (.succ .zero))
    defSortEnvWfT rfl (.sort [] (.succ .zero))
    (.const [] 0 [] ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ rfl rfl rfl)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

def literalSortExpansionTyping (n : Nat) :
    HasTyT literalSortEnv n [] (.const 1 []) (.sort (.succ .zero)) :=
  .const [] 1 [] literalSortMember rfl rfl rfl

def literalSortConversion (n : Nat) :
    ConvT literalSortEnv n [] (.lit 0) (.const 1 []) (.sort (.succ .zero)) :=
  .lit [] 0 (.const 1 []) (.sort (.succ .zero)) (.of 0) (literalSortExpansionTyping n)

/-- The literal case is exercised where its native sort typing and both
sort probes are inhabited. No literal-profile or judgment is modified. -/
theorem literalSort_active (n : Nat) :
    Nonempty (EnvWfT literalSortEnv) ∧
    Nonempty (ConvT literalSortEnv n [] (.lit 0) (.const 1 []) (.sort (.succ .zero))) ∧
    LRSCoreT (WhStepK literalSortEnv n) literalSortEnv n [] (.lit 0) (.lit 0)
      (.sort (.succ .zero)) .sort ∧
    LRSCoreT (WhStepK literalSortEnv n) literalSortEnv n [] (.lit 0) (.const 1 [])
      (.sort (.succ .zero)) .sort ∧
    LRSCoreT (WhStepK literalSortEnv n) literalSortEnv n [] (.const 1 []) (.lit 0)
      (.sort (.succ .zero)) .sort := by
  have hzero : ProbeEquivT (WhStepK literalSortEnv n) literalSortEnv n []
      (.const 0 []) (.sort .zero) :=
    probeEquiv_delta literalSortEnvWfT (r := 0) []
      (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩) rfl rfl
  have hzeroDiag := (sortProbe_active_from_target hzero
    (sortProbe_diagT [] .zero (.succ .zero))).1
  have hone : ProbeEquivT (WhStepK literalSortEnv n) literalSortEnv n []
      (.const 1 []) (.const 0 []) :=
    probeEquiv_delta literalSortEnvWfT (r := 1) [] (m := literalSortMember) rfl rfl
  have honeDiag := (sortProbe_active_from_target hone hzeroDiag).1
  have hlit : ProbeEquivT (WhStepK literalSortEnv n) literalSortEnv n []
      (.lit 0) (.const 1 []) := probeEquiv_lit literalSortEnvWfT (.of 0)
  exact ⟨⟨literalSortEnvWfT⟩, ⟨literalSortConversion n⟩,
    sortProbe_active_from_target hlit honeDiag⟩

-- BEGIN RCIC_PI_PROBE_COMPUTATION_ROOTS
#print axioms NotConstApplication
#print axioms whStepK_to_ctx_of_notConstApplication
#print axioms redR_contract_of_source_unique
#print axioms redR_ctx_iff_of_notConstApplication
#print axioms redR_beta_iff
#print axioms redR_zeta_iff
#print axioms redR_zetaLocal_iff
#print axioms redR_delta_iff
#print axioms redR_lit_iff
#print axioms redR_literalExpansion_iff
#print axioms probeEquiv_beta
#print axioms probeEquiv_zeta
#print axioms probeEquiv_zetaLocal
#print axioms probeEquiv_delta
#print axioms probeEquiv_lit
#print axioms convProbe_beta
#print axioms convProbe_zeta
#print axioms convProbe_zetaLocal
#print axioms convProbe_delta
#print axioms convProbe_lit
#print axioms whStepK_lam_false
#print axioms normalR_lam
#print axioms redR_lam_eq
#print axioms not_redR_lam_sort
#print axioms not_redR_lam_pi
#print axioms probeEquiv_lam
#print axioms convProbe_lam
#print axioms FunctionNoTypeProbeAtT
#print axioms FunctionNoTypeProbeT
#print axioms functionNoTypeProbeAt_lam
#print axioms probeEquiv_eta_iff_functionNoTypeProbeAt
#print axioms probeEquiv_eta_of_functionNoTypeProbeAt
#print axioms convProbe_eta_of_functionNoTypeProbe
#print axioms etaLambdaConversion
#print axioms etaLambdaInput
#print axioms etaLambda_nonvacuity
#print axioms piProbe_active_from_target
#print axioms sortProbe_active_from_target
#print axioms betaPi_active
#print axioms zetaPiSource
#print axioms zetaPiConversion
#print axioms zetaPi_active
#print axioms zetaLocalPi_active
#print axioms deltaSort_active
#print axioms literalSortMember
#print axioms literalSortEnv
#print axioms literalSortEnvWfT
#print axioms literalSortExpansionTyping
#print axioms literalSortConversion
#print axioms literalSort_active
-- END RCIC_PI_PROBE_COMPUTATION_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeComputationAudit
