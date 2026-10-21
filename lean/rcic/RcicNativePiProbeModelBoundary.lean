import rcic.RcicNativePiProbeComputation
import rcic.RcicNativeTypedModelTyping

/-!
# Typed head exclusions and the exact model-comparison boundary

The probe proof itself does not transport approximants. Its erased
conversion consumers nevertheless use head exclusions at function and
proposition types for eta and irrelevance. We state the latter below and
compose the native irr case from it. The former is stated in Computation.

The comparison section is only an implication between named inputs:
the landed `TypingLemmaT` plus typed, pointwise realization of the two
observed heads supplies both exclusions. Neither global input is supplied
here. This is not an implementation of `FundamentalSAtT` or of the other
seat's typed expansion/transport ports. Concrete typed local instances are
checked separately; their existence does not prove a universal supplier.

`closure_claim = 0`. Composition only, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiCycleAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeComputationAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-- At a proof endpoint the required local absence is the same two-head
predicate as at a function endpoint; its typing precondition differs. -/
def PropNoTypeProbeT (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {P p : Expr Nat},
    HasTyT E n Γ P (.sort .zero) → HasTyT E n Γ p P →
      FunctionNoTypeProbeAtT R E n Γ p

/-- Exact local obligations at the two proof endpoints suffice; neither
Pi injectivity nor a proposition-sort separation theorem is assumed. -/
theorem convProbe_irr_of_local_exclusions {Γ : LCtx} {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P)
    (hq : HasTyT E n Γ q P)
    (hnoP : FunctionNoTypeProbeAtT R E n Γ p)
    (hnoQ : FunctionNoTypeProbeAtT R E n Γ q) :
    ConvProbeMotiveT R (.irr Γ P p q hP hp hq) :=
  ⟨probeTransport_of_no_wf_probesT hnoP.1 hnoP.2,
    probeTransport_of_no_wf_probesT hnoQ.1 hnoQ.2⟩

theorem convProbe_irr_of_propNoTypeProbe (hno : PropNoTypeProbeT R E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {P p q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P)
    (hq : HasTyT E n Γ q P) : ConvProbeMotiveT R (.irr Γ P p q hP hp hq) :=
  convProbe_irr_of_local_exclusions hP hp hq (hno hΓ hP hp) (hno hΓ hP hq)

/-! ## Conditional comparison with the typed model -/

/-- Pointwise realization of an observed type head. Sort zero is realized
by `.prop`, not `.sort`; `sortCode` records that distinction. The Pi input
retains exactly the domain-context guard used by the probe. -/
def ProbeRealizedAtT (R : Readback) (E : ResolvedEnv) (n : Nat)
    (Γ : LCtx) (M : Expr Nat) : Prop :=
  (∀ u, RedR R Γ M (.sort u) → ApproxT E (ctxEnvT E Γ) M (sortCode u)) ∧
    ∀ A B, RedR R Γ M (.pi A B) → CtxWfT E n (.assumption A :: Γ) →
      ApproxT E (ctxEnvT E Γ) M (.pi .bot [])

/-- A candidate shared supplier, restricted to native typed sources in
well-formed contexts. No raw backward-transport statement occurs here. -/
def TypedProbeRealizationT (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M I : Expr Nat}, HasTyT E n Γ M I →
    ProbeRealizedAtT R E n Γ M

theorem sortCode_ne_bot (u : Level) : sortCode u ≠ .bot := by
  rcases sortCode_prop_or_sort u with h | h <;> rw [h] <;> intro h0 <;> cases h0

/-- The existing Pi-code and strict-element inversions expose the whole
possible element shape, so neither observed type-head compact fits. -/
theorem elT_pi_element_shape {ρ : EnvT} {A B : Expr Nat} {c : CptT}
    (h : ElT E ρ (.pi A B) c) : c = .bot ∨ ∃ g, c = .lam g := by
  obtain ⟨a, ha, hc⟩ := h
  rcases approxT_pi_inv ha with rfl | ⟨a, g, rfl, _, _⟩
  · exact Or.inl (ctyS_bot_inv hc)
  · rcases ctyS_pi_inv hc with h0 | ⟨g, hg, _⟩
    · exact Or.inl h0
    · exact Or.inr ⟨g, hg⟩

theorem not_elT_pi_sortCode {ρ : EnvT} {A B : Expr Nat} (u : Level) :
    ¬ ElT E ρ (.pi A B) (sortCode u) := by
  intro h
  rcases elT_pi_element_shape h with h0 | ⟨g, hg⟩
  · exact sortCode_ne_bot u h0
  · rcases sortCode_prop_or_sort u with hu | hu <;> rw [hu] at hg <;> cases hg

theorem not_elT_pi_piProbe {ρ : EnvT} {A B : Expr Nat} :
    ¬ ElT E ρ (.pi A B) (.pi .bot []) := by
  intro h
  rcases elT_pi_element_shape h with h0 | ⟨g, hg⟩
  · cases h0
  · cases hg

theorem functionNoTypeProbe_of_typing_realization
    (hty : TypingLemmaT E n) (hreal : TypedProbeRealizationT R E n) :
    FunctionNoTypeProbeT R E n := by
  intro Γ hΓ f A B hf
  have hr := hreal hΓ hf
  constructor
  · intro u hu
    exact not_elT_pi_sortCode u (hty hΓ hf _ (hr.1 u hu))
  · intro C D hread hΓC
    exact not_elT_pi_piProbe (hty hΓ hf _ (hr.2 C D hread hΓC))

theorem propNoTypeProbe_of_typing_realization
    (hty : TypingLemmaT E n) (hreal : TypedProbeRealizationT R E n) :
    PropNoTypeProbeT R E n := by
  intro Γ hΓ P p hP hp
  have hprop : ∀ a, ApproxT E (ctxEnvT E Γ) P a → IsPropCT E a := by
    intro a ha
    rcases (elT_sort_zero_iff E (ctxEnvT E Γ) a).mp (hty hΓ hP a ha) with rfl | h
    · exact .bot
    · exact h
  have hbot : ∀ c, ApproxT E (ctxEnvT E Γ) p c → c = .bot := by
    intro c hc
    exact elT_bot_of_propIdeal hprop (hty hΓ hp c hc)
  have hr := hreal hΓ hp
  constructor
  · intro u hu
    exact sortCode_ne_bot u (hbot _ (hr.1 u hu))
  · intro A B hread hΓA
    exact CptT.noConfusion (hbot _ (hr.2 A B hread hΓA))

/-! ## Actual typed local witnesses, independently of either global input -/

theorem probeRealizedAt_sort (Γ : LCtx) (u : Level) :
    ProbeRealizedAtT (WhStepK E n) E n Γ (.sort u) := by
  constructor
  · intro v hread
    have heq := Expr.sort.inj (redR_sort_eq (readbackLaws_whStepK E n) hread)
    subst v
    exact .sort _ _
  · intro A B hread _
    exact (Expr.noConfusion (redR_sort_eq (readbackLaws_whStepK E n) hread) : False).elim

theorem probeRealizedAt_pi (Γ : LCtx) (A B : Expr Nat) :
    ProbeRealizedAtT (WhStepK E n) E n Γ (.pi A B) := by
  constructor
  · intro u hread
    exact (Expr.noConfusion (redR_pi_eq (readbackLaws_whStepK E n) hread) : False).elim
  · intro _ _ _ _
    exact approxT_pi_bot_nil _ _ _ _

theorem probeRealizedAt_lam (Γ : LCtx) (A body : Expr Nat) :
    ProbeRealizedAtT (WhStepK E n) E n Γ (.lam A body) := by
  constructor
  · intro u hread
    exact (not_redR_lam_sort u hread).elim
  · intro C D hread _
    exact (not_redR_lam_pi C D hread).elim

/-- Both observation arms have typed, observed local instances. This
proves no universal realization field, and assumes no model typing lemma. -/
theorem probeRealization_typed_nonvacuity (E : ResolvedEnv) (n : Nat) :
    Nonempty (CtxWfT E n []) ∧
    Nonempty (HasTyT E n [] (.sort .zero) (.sort (.succ .zero))) ∧
    ProbeRealizedAtT (WhStepK E n) E n [] (.sort .zero) ∧
    ApproxT E (ctxEnvT E []) (.sort .zero) .prop ∧
    Nonempty (HasTyT E n [] (.pi (.sort .zero) (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
    ProbeRealizedAtT (WhStepK E n) E n [] (.pi (.sort .zero) (.sort .zero)) ∧
    ApproxT E (ctxEnvT E []) (.pi (.sort .zero) (.sort .zero)) (.pi .bot []) :=
  ⟨⟨.nil⟩, ⟨.sort [] .zero⟩, probeRealizedAt_sort [] .zero,
    sortCode_zero ▸ approxT_sort_code E (ctxEnvT E []) .zero,
    ⟨pinPiT E n⟩, probeRealizedAt_pi [] (.sort .zero) (.sort .zero),
    approxT_pi_bot_nil _ _ _ _⟩

/-- Control against choosing the wrong compact even on typed realized
sources. The generic sort readback must retain `sortCode`, including Prop. -/
theorem typed_sort_zero_not_sort_compact (E : ResolvedEnv) (n : Nat) :
    Nonempty (HasTyT E n [] (.sort .zero) (.sort (.succ .zero))) ∧
    RedR (WhStepK E n) [] (.sort .zero) (.sort .zero) ∧
    ¬ ApproxT E (ctxEnvT E []) (.sort .zero) .sort := by
  refine ⟨⟨.sort [] .zero⟩, .refl _, ?_⟩
  intro h
  rcases approxT_sort_inv h with h0 | h0
  · cases h0
  · rw [sortCode_zero] at h0
    cases h0

/-- A closed proposition with a native proof, using only the landed
poly-identity fixture and native Pi/sort constructors. -/
def polyIdPropAtZero (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] polyIdProp (.sort .zero) := by
  apply HasTyT.conv [] polyIdProp (.sort (.imax (.succ .zero) .zero))
    (.sort .zero) (.succ (.imax (.succ .zero) .zero))
  · apply HasTyT.pi [] (.sort .zero) (.succ .zero) (.pi (.bvar 0) (.bvar 1)) .zero
    · exact .sort [] .zero
    · apply HasTyT.conv _ _ (.sort (.imax .zero .zero)) (.sort .zero)
        (.succ (.imax .zero .zero))
      · exact .pi _ _ .zero _ .zero (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl)
      · exact .sorts _ _ _ (fun _ => rfl)
  · exact .sorts [] _ _ (fun _ => rfl)

def polyIdIrrConversion (E : ResolvedEnv) (n : Nat) :
    ConvT E n [] polyIdProof polyIdProof polyIdProp :=
  .irr [] polyIdProp polyIdProof polyIdProof (polyIdPropAtZero E n)
    (hasTyT_polyIdProof E n) (hasTyT_polyIdProof E n)

theorem propExclusion_typed_nonvacuity (E : ResolvedEnv) (n : Nat) :
    Nonempty (CtxWfT E n []) ∧
    Nonempty (HasTyT E n [] polyIdProp (.sort .zero)) ∧
    Nonempty (HasTyT E n [] polyIdProof polyIdProp) ∧
    FunctionNoTypeProbeAtT (WhStepK E n) E n [] polyIdProof ∧
    ProbeRealizedAtT (WhStepK E n) E n [] polyIdProof ∧
    ConvProbeMotiveT (WhStepK E n) (polyIdIrrConversion E n) :=
  ⟨⟨.nil⟩, ⟨polyIdPropAtZero E n⟩, ⟨hasTyT_polyIdProof E n⟩,
    functionNoTypeProbeAt_lam _ _, probeRealizedAt_lam _ _ _, probeEquiv_reflT _ _⟩

-- BEGIN RCIC_PI_PROBE_MODEL_BOUNDARY_ROOTS
#print axioms PropNoTypeProbeT
#print axioms convProbe_irr_of_local_exclusions
#print axioms convProbe_irr_of_propNoTypeProbe
#print axioms ProbeRealizedAtT
#print axioms TypedProbeRealizationT
#print axioms sortCode_ne_bot
#print axioms elT_pi_element_shape
#print axioms not_elT_pi_sortCode
#print axioms not_elT_pi_piProbe
#print axioms functionNoTypeProbe_of_typing_realization
#print axioms propNoTypeProbe_of_typing_realization
#print axioms probeRealizedAt_sort
#print axioms probeRealizedAt_pi
#print axioms probeRealizedAt_lam
#print axioms probeRealization_typed_nonvacuity
#print axioms typed_sort_zero_not_sort_compact
#print axioms polyIdPropAtZero
#print axioms polyIdIrrConversion
#print axioms propExclusion_typed_nonvacuity
-- END RCIC_PI_PROBE_MODEL_BOUNDARY_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit
