import rcic.RcicNativeTypedModelKPositive
import rcic.RcicNativeTypedModelKIndexFree
import rcic.RcicNativeTypedModelKTypedBeta
import rcic.RcicNativeTypedModelKInherited

/-!
# ApproxTK: measured construction and exact failed interfaces

## Outcome

This is a checked, context-indexed, demand-sensitive refinement candidate,
not a complete native K model.  It removes the original apart-index `.prop`
observation, retains the beta and delta controls, and agrees exactly with
ApproxT on a dependency-closed fragment.  Three independent obstructions
prevent presenting it as a full repair:

1. Exact K-free reuse inherits a closed-lambda typing obstruction from the
   landed `RcicNativeTypedModelFundSymmCex`.  For ANY model on the existing
   CptT/CTyS interface, agreement at just `cexTerm` and `cexType` refutes
   `TypingLemmaEnvT`.  Both expressions have no constants.  The counterexample
   has an actual closed native derivation, a true EnvTypedAtT guard and a
   non-bottom observation.  `not_typingLemmaEnvT_of_cex_agreement` states this
   boundary without mentioning ApproxTK or its K guard.
2. The positive DI certificate added to the imported native index gate is
   strictly stronger.  Native eta passes every native typing condition but
   fails this certificate.  `not_nativeKIndexComplete_eqEnv` and the stronger
   model-level `not_typedNativeKForwardTK_eqEnv` are unconditional refutations.
3. A proper Eq.rec prefix has only bottom, while its directly saturated call
   has `.prop`.  This contradicts the old application inversion and prevents
   a finite realized demand from transmitting that observation through a
   function variable.  The actual prefix's native type is extracted from
   eqGap's existing derivation.  Both ordinary native beta conversion and the
   joint semantic typing premise hold.  `not_modelBetaExpandTypedTK_eqEnv`
   and `not_native_conversion_sound_approxTK` record the exact failures.

The inherited closed typed beta disagreement also survives exact K-free
reuse.  Separately, at Nat the complete carrier agrees with ApproxT, so the
landed `FundCases` refutation transports as `not_fundCases_approxTK_natEnvU`.
The extra DI and prefix failures alone are not used to infer that result.
No refutation or complete supplier of `FundamentalSAtT` is claimed: its
conclusion is the landed LRSCoreS relation, not equality of model denotations.
No impossibility result for a future neutral/provenance compact model is
claimed either.

## Exact construction boundary

The saturated K constructor carries `KCanonW`, non-constructor-major,
the unchanged `KIndexConvAt`, the independent `IndexAgreementDI`, and the
unchanged `KCommonAt`.  Its recursive premise is the RHS observation.
The separate old ApproxT source observation makes the whole model a
refinement; it is explicitly constructed at the positive Eq controls.
Neither certificate mentions ApproxTK.  All inductive uses recurse on
actual children of the new derivation; no native typing derivation produced
by inversion or regularity is used as a smaller recursive call.

Removing the DI conjunct gives a native-gated refinement, but the apart
exclusion then still needs an unconditional native separation proof.
The Fundamental-dependent separation in CK2 does not supply it.  Removing
the old source filter additionally requires a genuine native computation
closure theorem.  `TypedNativeKForwardTK` states that theorem exactly with
admitted environment, well-formed context and both native endpoint typings;
its eta refutation proves that it cannot be assumed for this candidate.

## Affected recursors and the reusable fragment

`IndexedPropRecT E r` means that r admits a structured witness whose family
is declared into Prop and whose index telescope is nonempty.  Eq.rec at 65
is affected.  True.rec and And.rec have zero indices; the latter has two
parameters and two fields.  Nat's family is not declared into Prop.  The
three complete pin environments have no affected reference, so ApproxTK
equals ApproxT on EVERY expression there, for every native context.

`KFreeT` closes the allowed references under transparent bodies and recursor
schemas.  Thus a definition, or a recursor schema, that reaches an affected
reference is also outside the reusable base.  It is not claimed that every
other recursor in every larger environment is globally unchanged.  Recursive
Nat schemas are handled by a closed set of references, not infinite unfolding.

## Model and relation consumer inventory

The following is the inventory of model inputs to the landed Fund/FundStrong,
FundCases and LRSCoreS route.  “Transport” below is an equivalence of the stated
obligations.  It does not supply an unproved old obligation.

| Consumer or model lemma | Status and exact interface |
| --- | --- |
| CptT, CTyS, sortCode, demandT; LRSCoreS/typedPERS and relation PER lemmas | Reused unchanged. LRSCoreS has no model argument. |
| ApproxT.bot | `ApproxTK.bot`, unconditionally. |
| bvar intro/inversion | `approxTK_bvar_iff`, `approxTK_bvar_inv`, unconditionally. |
| sort intro/inversion | `approxTK_sort_code`, `approxTK_sort_inv`, unconditionally. |
| Pi intro/inversion and pi bottom empty probe | `ApproxTK.pi`, `approxTK_pi_inv`, `approxTK_pi_bot_nil`; the body uses assumption A :: Γ. |
| lam intro/inversion | `ApproxTK.lam`, `approxTK_lam_inv`; same explicit native binder context. |
| ordinary app/appSpine introduction | `ApproxTK.app`, `ApproxTK.appSpine`, unconditionally. |
| old app_inv / old AppCpt reconstruction | Old app_inv is false at eqGap; use `approxTK_app_inv` with the saturated alternative. Old prefix-retention reconstruction is separately refuted in Obstruction. |
| letE inversion | `approxTK_letE_inv`, unconditionally. |
| delta/literal constructors | `ApproxTK.delta` / `ApproxTK.lit`; delta body uses native [] and EnvT.bot. |
| lift0_intro / lift0_elim; old frozen-context pi/lam statements | Transport on the K-free fragment only; not claimed globally for Eq. |
| CtxModelTLaws and CtxModelTLaws' | Actual inhabitants on Nat/True/And; kernel-refuted at eqGap for the frozen Eq carrier. |
| ElT / type membership | `ElTK`, `elTK_bot`, `elTK_forget`, `elTK_iff_elT_of_kFree`. |
| environment monotonicity | `approxTK_mono_env`; native context is held fixed. |
| RelSubstAtT / RelSubstIdT | Transport needs K-free lookupValue expressions only. |
| FundTyAt / FundConvAt | Transport additionally needs the source term / both source endpoints K-free. |
| TyValidAt / CtxValidAt | Transport needs the relevant type expressions and context values K-free. |
| EnvTypedAtT | Transport needs K-free lookupType expressions. |
| RelSubstTypedAtT | Transport needs both lookupValue and lookupType agreement; eqGap identity has an actual inhabitant. |
| TypingAt | Transport needs both endpoints and result type K-free. No global Eq typing supplier is asserted. |
| ModelConvSoundAt | Transport on K-free endpoints; the landed closed typed beta counterexample is therefore inherited even there. The Eq prefix gives a separate failure outside that fragment. |
| HybridSeed | Transport needs the source term and its type K-free. |
| ModelBetaExpandT | Kernel-refuted already on a K-free malformed-type example; no raw beta law is consumed. |
| ArgTypedAt / ModelBetaExpandTyped | Proper-context counterparts are `ArgTypedTK` / `ModelBetaExpandTypedTK`; the former is inhabited at the actual Eq prefix, the latter is refuted with typed inputs. |
| TypingLemmaEnvT | Refuted for ApproxTK in every environment. More generally, agreement at the K-free cexTerm and cexType already refutes this exact old input. |
| FundCases | Global carrier-agreement transport is proved; the original record is kernel-refuted at Nat using the landed symmTyping counterexample. |
| FundamentalSAtT / IHBelow | Global carrier-agreement transport is proved. It applies to Nat/True/And but supplies no old Fundamental instance. No global Eq instance or Fundamental refutation is claimed. |
| hardwired TypingLemmaT, CtxEnvT/ctxEnvT | Not renamed by a generic CtxModelT theorem. No global TK instance is claimed. |
| old recursorProp inversion and recCall_major_indep | Not inherited across affected references. The new neutral Eq inversion exposes the actual index guard; the K-free fragment retains the old result. |
| raw IotaSoundT / BackTransportT / semEqT_kStar_of_iotaSoundT | Not consumed. Saturated computation requires explicit RHS/source observations; typed native K-forward is a named, refuted port for this candidate. |

FundCases has exactly the following 21 ports: app, const, letE, lit, conv,
trans, zeta, zetaLocal, delta, iota, litConv, appConv, lamConv, piConv,
letEConv, sorts, consts, eta, irr, tyConv and symmTyping.  The transport
theorem covers the whole landed record when every expression agrees.
No case proof or strong-induction assembler is copied or rebuilt here.

## Exact restatement forced by the inherited obstruction

With the old CptT and CTyS fixed, exact reuse at cexTerm and cexType and the
old global TypingLemmaEnvT cannot all hold.  Thus a K-only repair cannot
provide the complete old model-input package while preserving that fragment.
A further repair must change at least one of those precisely named interfaces:
the observations retained on that K-free fragment, compact typing, or the
global typing obligation.  The old TypingLemmaEnvT is not left as an assumed
port whose satisfiability a future lane could supply.

Independently, unrestricted native K completeness would have to remove or
replace IndexAgreementDI, since the existing typed eta control refutes it.
Native computation closure through function variables would also have to
replace the bottom-only proper-prefix behavior.  These are measured failures
of this candidate, not axioms used to certify its controls.

## Nondegeneracy

`eq_typed_compact_controlTK` gives the closed Eq-family proposition its
actual non-bottom spine, typed at `.prop`, in the admitted Eq environment.
`nat_typed_compact_controlTK` gives zero its constructor spine, typed at
the Nat family spine, using natEnvUWfT.  `eqGap_typed_compact_controlTK`
gives the repaired K call `.prop`, typed at `.sort`, in the actual nonempty
eqGap context.  The beta counterexample's joint argument premise uses the
non-bottom type code `.pi .bot []`; bottom-only behavior of the argument is
proved rather than imposed as a global degeneration assumption.

The typed identity substitution package at eqGap is also supplied.  It does
not claim CtxValidAt or IHBelow, and it is not substituted for the non-bottom
typed compact witnesses above.

All imported CK2 declarations are dependencies, never local copies.
`closure_claim = 0`; the PR remains draft.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKReportAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKControlAudit
open Rcic.Declarative.NativeValleys.TypedModelKPositiveAudit
open Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit
open Rcic.Declarative.NativeValleys.TypedModelKFailureAudit
open Rcic.Declarative.NativeValleys.TypedModelKTypedBetaAudit
open Rcic.Declarative.NativeValleys.TypedModelKInheritedAudit

/-- The positive and negative measurements hold simultaneously for this
same model.  This is the bounded result, not a global closure theorem. -/
theorem approxTK_checked_boundary (n : Nat) :
    (∀ ρ c, ApproxTK eqEnvT n apartCtx ρ apartRec c → c = .bot) ∧
    (∀ ρ, ApproxTK eqEnvT n eqGapCtx ρ eqGapRedex .prop) ∧
    (∀ ρ, ApproxTK eqEnvT n binderEqCtx ρ binderIndexRedex .prop) ∧
    (∀ ρ, ApproxTK deltaEqEnv n deltaHeadEqCtx ρ (deltaRedex (.const 66 [])) .prop) ∧
    (∀ ρ, ApproxTK deltaEqEnv n deltaUnderBinderEqCtx ρ
      (deltaRedex deltaBinderIndex) .prop) ∧
    (¬ TypedNativeKForwardTK eqEnvT n) ∧
    (¬ CtxModelTLaws (ctxModelT_approxTK eqEnvT n eqGapCtx)) ∧
    (¬ ModelBetaExpandTypedTK eqEnvT n) ∧
    (∀ Γ, CtxModelTLaws' (ctxModelT_approxTK natEnvU n Γ)) ∧
    (∀ E Γ, ¬ TypingLemmaEnvT (ctxModelT_approxTK E n Γ) n) ∧
    (∀ R Γ, ¬ FundCases (ctxModelT_approxTK natEnvU n Γ) R n) :=
  ⟨fun _ _ h => approxTK_apartRec_bot h,
    approxTK_eqGap_prop n, approxTK_binder_prop n, approxTK_delta_prop n,
    approxTK_delta_under_binder_prop n, not_typedNativeKForwardTK_eqEnv n,
    not_ctxModelTLaws_approxTK_eqGap n, not_modelBetaExpandTypedTK_eqEnv n,
    ctxModelTLaws'_approxTK_natEnvU n,
    fun E Γ => not_typingLemmaEnvT_approxTK E n Γ,
    fun R Γ => not_fundCases_approxTK_natEnvU R n Γ⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_REPORT_ROOTS
#print axioms approxTK_checked_boundary
-- END RCIC_NATIVE_TYPED_MODEL_K_REPORT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKReportAudit
