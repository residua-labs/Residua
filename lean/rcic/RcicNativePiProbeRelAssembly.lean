import rcic.RcicNativePiProbeRelApp
import rcic.RcicNativePiProbeRelSubst
import rcic.RcicNativePiProbeConstants

/-!
# Assembly of typed-relation adapters and specified-witness chains

This module assembles probe constructor arms, not FundamentalSAtT cases.
The application and let inputs are the existing action ports supplied by
the companion relation adapters. The two remaining head exclusions are
the existing typed-model boundary inputs from #7723. Every computation
uses the exact deterministic CK readback.

Only symm, trans, and tyConv recurse. Every recursive call uses an actual
child conversion derivation; its size decrease is checked explicitly.
The TyConvT chain and Pi-row read-off are imported composition consumers.

No global adapter-input package, FundamentalSAtT, or Pi row is asserted.
In particular the current CK Eq gap refutes a global supplier at eqEnvT.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeRelAssemblyAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeComputationAudit
open Rcic.Declarative.NativeValleys.PiProbeConstantsAudit
open Rcic.Declarative.NativeValleys.PiProbeCongruenceAudit
open Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit
open Rcic.Declarative.NativeValleys.PiProbeRelBridgeAudit
open Rcic.Declarative.NativeValleys.PiProbeRelAppAudit
open Rcic.Declarative.NativeValleys.PiProbeRelIotaAudit
open Rcic.Declarative.NativeValleys.PiProbeRelSubstAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit

variable {E : ResolvedEnv} {n : Nat}

/-- The existing absence-of-probes boundary is inhabited at every lambda
for the selected CK readback, by its imported source-shape inversion. -/
theorem functionNoTypeProbeAt_lamCK {Γ : LCtx} (A body : Expr Nat) :
    FunctionNoTypeProbeAtT (WhStepCK E) E n Γ (.lam A body) := by
  have hnormal : NormalR (WhStepCK E) Γ (.lam A body) :=
    fun _ hs => whStepCK_lam_false_aux hs rfl
  constructor
  · intro u hr
    exact Expr.noConfusion (redR_of_normal hnormal hr)
  · intro C D hr _
    exact Expr.noConfusion (redR_of_normal hnormal hr)

/-- The two old head-exclusion ports have an actual native function/proof
instance at the exact CK readback. This is a local witness, not a claim
of the universally quantified function or proposition exclusion. -/
theorem headExclusions_typed_nonvacuityCK (E : ResolvedEnv) (n : Nat) :
    Nonempty (CtxWfT E n []) ∧
    Nonempty (HasTyT E n [] polyIdProof polyIdProp) ∧
    Nonempty (HasTyT E n [] polyIdProp (.sort .zero)) ∧
    FunctionNoTypeProbeAtT (WhStepCK E) E n [] polyIdProof ∧
    ConvProbeMotiveT (WhStepCK E) (polyIdIrrConversion E n) := by
  have hno : FunctionNoTypeProbeAtT (WhStepCK E) E n [] polyIdProof :=
    functionNoTypeProbeAt_lamCK (n := n) (.sort .zero) (.lam (.bvar 0) (.bvar 0))
  exact ⟨⟨.nil⟩, ⟨hasTyT_polyIdProof E n⟩, ⟨polyIdPropAtZero E n⟩, hno,
    convProbe_irr_of_local_exclusions (polyIdPropAtZero E n)
      (hasTyT_polyIdProof E n) (hasTyT_polyIdProof E n) hno hno⟩

/-- No new K rule has a bare-constant source; the remaining case is the
landed opaque-constant context-step exclusion. -/
theorem normalR_const_opaqueCK {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hb : m.body = none) (ls : List Level) :
    NormalR (WhStepCK E) Γ (.const r ls) := by
  intro N hs
  have haux : ∀ {X Y : Expr Nat}, WhStepCK E Γ X Y → X = .const r ls → False := by
    intro X Y h
    cases h with
    | ctx hc =>
        intro heq
        cases heq
        exact whStepCtx_const_opaque_false hm hb ls hc
    | kStar _ _ _ =>
        intro heq
        rw [recCall_eq_app] at heq
        exact Expr.noConfusion heq
    | kProj _ _ _ _ =>
        intro heq
        rw [recCall_eq_app] at heq
        exact Expr.noConfusion heq
    | recMajor _ _ _ _ _ _ =>
        intro heq
        rw [recCall_eq_app] at heq
        exact Expr.noConfusion heq
    | appHead _ =>
        intro heq
        exact Expr.noConfusion heq
  exact haux hs rfl

/-- The #7723 constant argument transfers to CK by composing its stored
body invariant with CK context-step cancellation. No new body law is used. -/
theorem probeEquiv_constsCK (hW : EnvWfT E) {Γ : LCtx} {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (ls ls' : List Level) :
    ProbeEquivT (WhStepCK E) E n Γ (.const r ls) (.const r ls') := by
  cases hb : m.body with
  | none =>
      apply probeEquiv_of_no_probesT
      · intro u hr
        exact Expr.noConfusion (redR_of_normal (normalR_const_opaqueCK hm hb ls) hr)
      · intro A B hr
        exact Expr.noConfusion (redR_of_normal (normalR_const_opaqueCK hm hb ls) hr)
      · intro u hr
        exact Expr.noConfusion (redR_of_normal (normalR_const_opaqueCK hm hb ls') hr)
      · intro A B hr
        exact Expr.noConfusion (redR_of_normal (normalR_const_opaqueCK hm hb ls') hr)
  | some body =>
      apply probeEquiv_of_readback_iffT (readbackLaws_whStepCK E)
      intro X hX
      rw [redR_ctx_whStepCK_iff hW (WhStepCtx.delta hm hb (ls := ls)) hX,
        redR_ctx_whStepCK_iff hW (WhStepCtx.delta hm hb (ls := ls')) hX,
        instantiateLevels_stored_body hW hm hb ls,
        instantiateLevels_stored_body hW hm hb ls']

/-- The exact residual ports of the constructor assembly. The first
three fields are outputs of the typed-relation adapters. The last two
are the named typed-model head-exclusion facts from #7723. This record
is not given a universal inhabitant. -/
structure ProbeAdapterInputsCKT (E : ResolvedEnv) (n : Nat) : Prop where
  head : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f g A B : Expr Nat}
    (hf : ConvT E n Γ f g (.pi A B)), AppHeadActionT (WhStepCK E) hf
  argument : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {g A B : Expr Nat}
    (hg : HasTyT E n Γ g (.pi A B)), AppArgActionT (WhStepCK E) hg
  letSubstitution : ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A A' value value' body body' B : Expr Nat} {u : Level},
    ConvT E n Γ A A' (.sort u) → ConvT E n Γ value value' A →
    ConvT E n (.letBinding A value :: Γ) body body' B →
    MixedSubstEdgesT (WhStepCK E) E n Γ value value' body body'
  functions : FunctionNoTypeProbeT (WhStepCK E) E n
  proofs : PropNoTypeProbeT (WhStepCK E) E n

/-- All 18 native constructor arms. The only recursion is on symm's
child, trans's two children, and tyConv's term-conversion child. -/
theorem convProbe_of_adapterInputsCKT (hW : EnvWfT E) (h : ProbeAdapterInputsCKT E n) :
    ∀ {Γ : LCtx} {M N A : Expr Nat} (hc : ConvT E n Γ M N A),
      CtxWfT E n Γ → ConvProbeMotiveT (WhStepCK E) hc
  | _, _, _, _, .refl _ _ _ ht, _ => convProbe_reflT ht
  | _, _, _, _, .symm _ _ _ _ hc, hΓ =>
      convProbe_symmT hc (convProbe_of_adapterInputsCKT hW h hc hΓ)
  | _, _, _, _, .trans _ _ _ _ _ hc hd, hΓ =>
      convProbe_transT hW hΓ hc hd
        (convProbe_of_adapterInputsCKT hW h hc hΓ)
        (convProbe_of_adapterInputsCKT hW h hd hΓ)
  | _, _, _, _, .beta _ D body arg _ _ _ _ _, _ =>
      probeEquiv_ctx_whStepCK hW (.beta D body arg)
  | _, _, _, _, .zeta _ D value body _ _ _ _ _, _ =>
      probeEquiv_ctx_whStepCK hW (.zeta D value body)
  | _, _, _, _, .zetaLocal _ _ _ _ hv _ _, _ =>
      probeEquiv_ctx_whStepCK hW (.zetaLocal hv)
  | _, _, _, _, .delta _ _ _ _ _ hm hb _ _ _ _, _ =>
      probeEquiv_ctx_whStepCK hW (.delta hm hb)
  | _, _, _, _, .iota _ _ _ _ hi hl hr, _ =>
      (native_iota_motive_iff_forwardCK hi hl hr).mpr (native_iota_forwardCK hW hi hl hr)
  | _, _, _, _, .lit _ t _ _ (.of _) _, _ =>
      probeEquiv_ctx_whStepCK hW (.lit t)
  | _, _, _, _, .app _ _ _ _ _ _ _ hf ha, hΓ =>
      convProbe_app_of_actionsT hW hΓ hf ha (h.head hΓ hf)
        (h.argument hΓ (convEnds hW hΓ hf).2.1)
  | _, _, _, _, .lam _ D D' body body' _ _ _ _, _ =>
      ⟨probeTransport_of_no_wf_probesT (functionNoTypeProbeAt_lamCK (n := n) D body).1
        (functionNoTypeProbeAt_lamCK (n := n) D body).2,
       probeTransport_of_no_wf_probesT (functionNoTypeProbeAt_lamCK (n := n) D' body').1
        (functionNoTypeProbeAt_lamCK (n := n) D' body').2⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, hΓ =>
      convProbe_piT (readbackLaws_whStepCK E) hW hΓ hA hB
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb, hΓ =>
      convProbe_letE_of_mixedSubst_whStepCK hW hΓ hA hv hb (h.letSubstitution hΓ hA hv hb)
  | _, _, _, _, .sorts Γ u v heq, _ =>
      convProbe_sortsT (readbackLaws_whStepCK E) Γ u v heq
  | _, _, _, _, .consts _ _ ls ls' _ hm _ _ _ _, _ =>
      probeEquiv_constsCK hW hm ls ls'
  | _, _, _, _, .eta _ f D _ hf, hΓ =>
      ⟨probeTransport_of_no_wf_probesT
        (functionNoTypeProbeAt_lamCK (n := n) D (.app (lift 0 1 f) (.bvar 0))).1
        (functionNoTypeProbeAt_lamCK (n := n) D (.app (lift 0 1 f) (.bvar 0))).2,
       probeTransport_of_no_wf_probesT (h.functions hΓ hf).1 (h.functions hΓ hf).2⟩
  | _, _, _, _, .irr _ _ _ _ hP hp hq, hΓ =>
      convProbe_irr_of_propNoTypeProbe h.proofs hΓ hP hp hq
  | _, _, _, _, .tyConv _ _ _ _ _ _ hc hA, hΓ =>
      convProbe_tyConvT hc hA (convProbe_of_adapterInputsCKT hW h hc hΓ)
termination_by _ _ _ _ hc _ => sizeOf hc
decreasing_by all_goals simp_wf; omega

/-- The action assembly supplies all the strengthened sort-indexed links. -/
theorem probeConvLinks_of_adapterInputsCKT (hW : EnvWfT E)
    (h : ProbeAdapterInputsCKT E n) : ProbeConvLinksT (WhStepCK E) E n := by
  intro Γ hΓ M N u hc
  exact convProbe_of_adapterInputsCKT hW h hc hΓ

/-- The requested final composition consumes the existing chain theorem.
No new chain transport, Pi-row principle, or model equation is assumed. -/
theorem piRowField_of_adapterInputsCKT (hW : EnvWfT E)
    (h : ProbeAdapterInputsCKT E n) : PiRowField E n :=
  piRowField_of_probeConvLinksT (readbackLaws_whStepCK E) hW
    (probeConvLinks_of_adapterInputsCKT hW h)

/-- Model-side resources for the conditional end-to-end wiring. These
are the explicit identity, realization, and let-substitution inputs of
the local adapters, together with the two old head exclusions. No global
inhabitant is asserted. The concrete local controls live in App/Subst. -/
structure ProbeAdapterModelInputsCKT (E : ResolvedEnv) (n : Nat) : Prop where
  identity : ∀ {Γ : LCtx}, CtxWfT E n Γ →
    RelSubstIdT (ctxModelT_approxT E) (WhStepCK E) n Γ (ctxEnvT E Γ)
  realization : TypedProbeRealizationT (WhStepCK E) E n
  lets : ∀ {Γ : LCtx}, CtxWfT E n Γ →
    ∀ {A A' value value' body body' B : Expr Nat} {u : Level},
    ConvT E n Γ A A' (.sort u) → ConvT E n Γ value value' A →
    ConvT E n (.letBinding A value :: Γ) body body' B →
    ∃ ρ ρ' : EnvT,
      RelSubstAtT (ctxModelT_approxT E) (WhStepCK E) n Γ ρ ρ
        (SubstT.cons value SubstT.id) (SubstT.cons value SubstT.id)
        (.letBinding A value :: Γ) ∧
      RelSubstAtT (ctxModelT_approxT E) (WhStepCK E) n Γ ρ ρ'
        (SubstT.cons value SubstT.id) (SubstT.cons value' SubstT.id)
        (.letBinding A value :: Γ) ∧
      ModelProbeAtSubstT (ctxModelT_approxT E) (WhStepCK E) n Γ ρ
        (SubstT.cons value SubstT.id) body ∧
      ModelProbeAtSubstT (ctxModelT_approxT E) (WhStepCK E) n Γ ρ
        (SubstT.cons value SubstT.id) body' ∧
      ModelProbeAtSubstT (ctxModelT_approxT E) (WhStepCK E) n Γ ρ'
        (SubstT.cons value' SubstT.id) body'
  functions : FunctionNoTypeProbeT (WhStepCK E) E n
  proofs : PropNoTypeProbeT (WhStepCK E) E n

/-- This is the exact relation-facts -> actions adapter wiring. Head
uses hF.2/hF.1, argument uses hF.1/hF.2, and let uses hF.2 on the body
and hF.1 on its right endpoint. All native typings produced by convEnds
are used as inputs, never as recursive arguments. -/
theorem probeAdapterInputs_of_fundamentalSAtT (hW : EnvWfT E)
    (hF : FundamentalSAtT (ctxModelT_approxT E) (WhStepCK E) n)
    (hM : ProbeAdapterModelInputsCKT E n) : ProbeAdapterInputsCKT E n := by
  refine ⟨?_, ?_, ?_, hM.functions, hM.proofs⟩
  · intro Γ hΓ f g A B hf
    apply appHeadAction_of_fundamentalSAtT_whStepCK hW hΓ hf (hM.identity hΓ) hF
    intro a ha
    exact ⟨hM.realization hΓ (.app Γ f a A B (convEnds hW hΓ hf).1 ha),
      hM.realization hΓ (.app Γ g a A B (convEnds hW hΓ hf).2.1 ha)⟩
  · intro Γ hΓ g A B hg
    apply appArgAction_of_fundamentalSAtT_whStepCK hW hΓ hg (hM.identity hΓ) hF
    intro a ha
    exact hM.realization hΓ (.app Γ g a A B hg ha)
  · intro Γ hΓ A A' value value' body body' B u hA hv hb
    obtain ⟨ρ, ρ', hSame, hMixed, hleft, hmiddle, hright⟩ := hM.lets hΓ hA hv hb
    exact mixedSubstEdges_letE_of_fundamentalSAtT (readbackLaws_whStepCK E)
      (normalUniqueR_whStepCK hW) hW hF hΓ hA hv hb
      hSame hMixed hleft hmiddle hright

/-- Conditional complete conversion-link wiring; the Fundamental cases
remain wholly with their supplier. -/
theorem probeConvLinks_of_fundamentalSAtT_adapters (hW : EnvWfT E)
    (hF : FundamentalSAtT (ctxModelT_approxT E) (WhStepCK E) n)
    (hM : ProbeAdapterModelInputsCKT E n) : ProbeConvLinksT (WhStepCK E) E n :=
  probeConvLinks_of_adapterInputsCKT hW (probeAdapterInputs_of_fundamentalSAtT hW hF hM)

/-- The full requested pipeline is composition of the adapter wiring
and the existing specified-witness TyConvT chain consumer. Its universal
Fundamental input is explicitly refuted for the current CK Eq example. -/
theorem piRowField_of_fundamentalSAtT_adapters (hW : EnvWfT E)
    (hF : FundamentalSAtT (ctxModelT_approxT E) (WhStepCK E) n)
    (hM : ProbeAdapterModelInputsCKT E n) : PiRowField E n :=
  piRowField_of_probeConvLinksT (readbackLaws_whStepCK E) hW
    (probeConvLinks_of_fundamentalSAtT_adapters hW hF hM)

/-- The current CK Eq gap also refutes this assembly's global input
package. It does not refute any of the local composition theorems. -/
theorem not_probeAdapterInputsCKT_eqEnv (n : Nat) : ¬ ProbeAdapterInputsCKT eqEnvT n := by
  intro h
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  obtain ⟨hc⟩ := eqGap_conv n
  obtain ⟨u, hr⟩ := (probeConvLinks_of_adapterInputsCKT pinEqGroupWfT h hΓ hc).1.sorts
    ⟨.zero, .refl _⟩
  exact Expr.noConfusion (whRedCK_eqGapRedex_eq hr)

-- BEGIN RCIC_PI_PROBE_REL_ASSEMBLY_ROOTS
#print axioms functionNoTypeProbeAt_lamCK
#print axioms headExclusions_typed_nonvacuityCK
#print axioms normalR_const_opaqueCK
#print axioms probeEquiv_constsCK
#print axioms ProbeAdapterInputsCKT
#print axioms convProbe_of_adapterInputsCKT
#print axioms probeConvLinks_of_adapterInputsCKT
#print axioms piRowField_of_adapterInputsCKT
#print axioms ProbeAdapterModelInputsCKT
#print axioms probeAdapterInputs_of_fundamentalSAtT
#print axioms probeConvLinks_of_fundamentalSAtT_adapters
#print axioms piRowField_of_fundamentalSAtT_adapters
#print axioms not_probeAdapterInputsCKT_eqEnv
-- END RCIC_PI_PROBE_REL_ASSEMBLY_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeRelAssemblyAudit
