import rcic.RcicNativeReadbackCK2Inputs
import rcic.RcicNativeReadbackCK2Conv
import rcic.RcicNativeReadbackCK2
import rcic.RcicNativeReadbackCK2Index

set_option maxRecDepth 8192

/-!
# A typed model obstruction to the guarded CK2 readback

The two Eq indices are closed propositions: the existing `idPiProp`, and
`Eq Prop idPiProp idPiProp`.  The latter has a rigid family head.  Both
indices are typed at `Prop`; their inequality is never treated as native
nonconvertibility.

Instead, a hypothetical global `FundamentalSAtT` supplies its own
separation argument.  Its unified spine clause reads the last argument
from the explicit family conversion required by CK2.  Its Pi clause
then asks the rigid Eq family to read as a Pi, contradicting the given
readback laws.  The same hypothetical supplier is therefore unable to
justify a native K head at the typed Eq recursor below, although the
unchanged model assigns that recursor the compact `.prop`.

This file uses individual instances of the original quantified
Fundamental motives.  It neither rebuilds their constructor induction
nor assumes a global identity or model-realization package.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit

variable {R : Readback} {n : Nat}

/-- The Eq family with the fixed closed Pi proposition as its left index. -/
def apartEqAt (x : Expr Nat) : Expr Nat :=
  foldApps (.const 63 []) [.sort .zero, idPiProp, x]

/-- A closed family-headed proposition used as the distinct right index. -/
def apartRight : Expr Nat := apartEqAt idPiProp

/-- One neutral proof between the two proposition indices. -/
def apartCtx : LCtx := [.assumption (apartEqAt apartRight)]

/-- The constant `Sort 1` motive, over the two Eq binders. -/
def apartMot : Expr Nat :=
  .lam (.sort .zero) (.lam (apartEqAt (.bvar 0)) (.sort (.succ .zero)))

/-- The typed neutral-major recursor whose model ignores the apart indices. -/
def apartRec : Expr Nat :=
  recCall (.const 65 [.succ (.succ .zero)])
    [.sort .zero, idPiProp, apartMot, .sort .zero, apartRight] (.bvar 0)

/-- The existing Pi proposition has type `Prop`, using the existing level law. -/
def apartLeft_ty (n : Nat) (Γ : LCtx) :
    HasTyT eqEnvT n Γ idPiProp (.sort .zero) :=
  .conv Γ idPiProp _ _ _
    (PiModelTermDFundAudit.hasTyT_idPiProp_at eqEnvT n Γ)
    (.sorts Γ _ .zero (eqN_imax_zero_right _))

private def apartEqAt_ty {Γ : LCtx} {x : Expr Nat}
    (hx : HasTyT eqEnvT n Γ x (.sort .zero)) :
    HasTyT eqEnvT n Γ (apartEqAt x) (.sort .zero) :=
  .app _ _ _ _ _
    (eqFamilyPartialTy (fun _ _ h => h) (.sort Γ .zero) (apartLeft_ty n Γ)) hx

/-- The counterexample context is well formed in the actual admitted Eq environment. -/
def apartCtx_wf (n : Nat) : CtxWfT eqEnvT n apartCtx :=
  .assumption [] (apartEqAt apartRight) .zero .nil
    (apartEqAt_ty (apartEqAt_ty (apartLeft_ty n [])))

private def apartMotInnerTy (n : Nat) (Γ : LCtx) :
    HasTyT eqEnvT n (.assumption (.sort .zero) :: Γ)
      (.lam (apartEqAt (.bvar 0)) (.sort (.succ .zero)))
      (.pi (apartEqAt (.bvar 0)) (.sort (.succ (.succ .zero)))) :=
  .lam _ _ _ _ _ (apartEqAt_ty (.bvar _ 0 _ rfl)) (.sort _ _)

private def apartMotTy (n : Nat) (Γ : LCtx) :
    HasTyT eqEnvT n Γ apartMot
      (.pi (.sort .zero) (.pi (apartEqAt (.bvar 0)) (.sort (.succ (.succ .zero))))) :=
  .lam _ _ _ _ _ (.sort _ _) (apartMotInnerTy n Γ)

private def apartMotAppConv {Γ : LCtx} {x p : Expr Nat}
    (hx : HasTyT eqEnvT n Γ x (.sort .zero))
    (hp : HasTyT eqEnvT n Γ p (apartEqAt x)) :
    ConvT eqEnvT n Γ (.app (.app apartMot x) p)
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
  have hout : ConvT eqEnvT n Γ (.app apartMot x)
      (.lam (apartEqAt x) (.sort (.succ .zero)))
      (.pi (apartEqAt x) (.sort (.succ (.succ .zero)))) :=
    .beta _ _ _ _ _ _ (.sort _ _) (apartMotInnerTy n Γ) hx
  exact .trans _ _ _ _ _ (.app _ _ _ _ _ _ _ hout (.refl _ _ _ hp))
    (.beta _ _ _ _ _ _ (apartEqAt_ty hx) (.sort _ _) hp)

/-- An actual native typing of the recursor; no conversion between the
two indices is used or needed to type the neutral major. -/
theorem apartRec_typed (n : Nat) :
    Nonempty (HasTyT eqEnvT n apartCtx apartRec (.sort (.succ .zero))) := by
  have hleft := apartLeft_ty n apartCtx
  have hright := apartEqAt_ty hleft
  have hrefl := eqReflApplyTy (fun _ _ h => h) (.sort apartCtx .zero) hleft
  have hmin : HasTyT eqEnvT n apartCtx (.sort .zero)
      (.app (.app apartMot idPiProp) (foldApps (.const 64 []) [.sort .zero, idPiProp])) :=
    .conv _ _ _ _ _ (.sort _ _) (.symm _ _ _ _ (apartMotAppConv hleft hrefl))
  have hmajor : HasTyT eqEnvT n apartCtx (.bvar 0) (apartEqAt apartRight) :=
    .bvar _ 0 _ rfl
  have hrec : HasTyT eqEnvT n apartCtx apartRec
      (.app (.app apartMot apartRight) (.bvar 0)) :=
    .app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _
      (.app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _
        (.const _ 65 [.succ (.succ .zero)] eqRecT rfl rfl rfl)
        (.sort _ _)) hleft) (apartMotTy n apartCtx)) hmin) hright) hmajor
  exact ⟨.conv _ _ _ _ _ hrec (apartMotAppConv hright hmajor)⟩

/-- The required identity package is constructed at this nonempty,
let-free context only; it is not asserted as a universal model field. -/
theorem apartCtx_identity (R : Readback) (n : Nat) :
    RelSubstIdT (ctxModelT_approxT eqEnvT) R n apartCtx EnvT.bot := by
  have hT := typedSubstT_id (envClosed_of_envWfT pinEqGroupWfT) (apartCtx_wf n)
  refine ⟨hT, hT, ?_, ?_, ?_⟩
  · intro i A hA
    exact ⟨by simpa only [substT_id] using
      (ConvT.refl apartCtx (.bvar i) A (.bvar apartCtx i A hA))⟩
  · intro i A _ c hc
    have hc' : c = .bot := hc.elim id id
    subst c
    exact ⟨lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _,
      lrSCoreS_bot _ _ _ _, lrSCoreS_bot _ _ _ _⟩
  · intro i v A hv _
    cases i <;> simp [apartCtx, lookupValue] at hv

/-- The context environment requested by the original adapter is exactly
the bottom variable environment at this let-free context. -/
theorem apartCtx_ctxEnv_eq_bot : ctxEnvT eqEnvT apartCtx = EnvT.bot := by
  funext i c
  cases i <;> rfl

/-- The local identity instance also has the exact canonical-environment
form consumed by the original adapter's `identity` field. -/
theorem apartCtx_identity_canonical (R : Readback) (n : Nat) :
    RelSubstIdT (ctxModelT_approxT eqEnvT) R n apartCtx (ctxEnvT eqEnvT apartCtx) := by
  rw [apartCtx_ctxEnv_eq_bot]
  exact apartCtx_identity R n

/-- Both environment-typing guards hold, using the existing bottom
environment theorem; the strengthened substitution guard excludes no
part of this counterexample. -/
theorem apartCtx_typed_identity (R : Readback) (n : Nat) :
    RelSubstTypedAtT (ctxModelT_approxT eqEnvT) R n apartCtx EnvT.bot EnvT.bot
      SubstT.id SubstT.id apartCtx :=
  ⟨apartCtx_identity R n, envTypedAtT_bot apartCtx, envTypedAtT_bot apartCtx⟩

/-- The non-bottom model observation is independent of the readback. -/
theorem apartRec_model (ρ : EnvT) : ApproxT eqEnvT ρ apartRec .prop :=
  eqRec_model_minor_backward (approxT_sort_code eqEnvT ρ .zero)

/-- The observed compact is non-bottom and is semantically typed at the
actual code of the recursor's native type `Sort 1`. -/
theorem apartRec_typed_model_seed (ρ : EnvT) :
    ApproxT eqEnvT ρ apartRec .prop ∧
    ApproxT eqEnvT ρ (.sort (.succ .zero)) .sort ∧
    CTyS eqEnvT .prop .sort ∧ (CptT.prop ≠ .bot) :=
  ⟨apartRec_model ρ, approxT_sort_code eqEnvT ρ (.succ .zero),
    by rw [CTyS]; exact Or.inr TyCodeCT.prop, fun h => CptT.noConfusion h⟩

/-- The typed model-law guard holds jointly for every compact of the
recursor, not only for the selected non-bottom observation. -/
theorem apartRec_argTyped (ρ : EnvT) :
    ArgTypedAt eqEnvT ρ apartRec (.sort (.succ .zero)) := by
  refine ⟨.sort, approxT_sort_code eqEnvT ρ (.succ .zero), ?_⟩
  intro c hc
  have hs := approxT_sort_inv (eqRec_model_minor_forward hc)
  have hs' : c = .bot ∨ c = .prop := by simpa only [sortCode_zero] using hs
  rcases hs' with rfl | rfl
  · exact ctyS_bot _
  · rw [CTyS]
    exact Or.inr TyCodeCT.prop

/-- The exact rigid-spine observation used to expose the last Eq argument. -/
theorem apartRight_model (ρ : EnvT) :
    ApproxT eqEnvT ρ apartRight (.spine 63 [.bot, .bot, .bot]) := by
  have hn : ¬ PropCtorT eqEnvT 63 := by
    rintro ⟨m, _, _, hm, hc, _⟩
    have he : m = eqFamT := Option.some.inj hm.symm
    subst m
    cases hc
  exact .appSpine (.appSpine (.appSpine
    (.const ρ 63 [] (rigidConst_of_inductiveM pinEqGroupWfT
      (m := eqFamT) rfl rfl) hn)
    (.bot _ _)) (.bot _ _)) (.bot _ _)

/-- Both observations used in the conditional native separation proof
are also typed at the actual code of their native type `Sort 0`. -/
theorem apart_separating_compacts_typed :
    CTyS eqEnvT (.pi .bot []) .prop ∧
    CTyS eqEnvT (.spine 63 [.bot, .bot, .bot]) .prop := by
  constructor
  · rw [CTyS]
    exact Or.inr (IsPropCT.pi TyCodeCT.bot
      (fun _ hs => (List.not_mem_nil _ hs).elim))
  · rw [CTyS]
    exact Or.inr (IsPropCT.spine (m := eqFamT) rfl rfl)

/-- Under the hypothetical Fundamental supplier, a Pi proposition cannot
be convertible to this rigid family proposition.  The separation comes
from that supplier's own Pi clause and the readback laws. -/
theorem not_apart_index_conv_of_fundamental
    (hL : ReadbackLaws eqEnvT R)
    (hF : FundamentalSAtT (ctxModelT_approxT eqEnvT) R n) :
    ¬ Nonempty (ConvT eqEnvT n apartCtx idPiProp apartRight (.sort .zero)) := by
  rintro ⟨hc⟩
  have hrel := fundConvAt_ctx_of_id (apartCtx_wf n) (apartCtx_identity R n)
    (hF.2 (apartCtx_wf n) hc) (.pi .bot [])
    (Or.inl (approxT_pi_bot_nil eqEnvT EnvT.bot (.sort .zero) (.bvar 0)))
  obtain ⟨A, B, A', B', _, hread, _⟩ := lrSCoreS_pi_probe_codom hrel
  have he := redR_famApp_eq hL pinEqGroupWfT
    (r := 63) (m := eqFamT) rfl rfl hread
  exact TypedModelAudit.foldApps_const_ne_pi
    [.sort .zero, idPiProp, idPiProp] A' B' he.symm

/-- Fundamental's unified spine clause reads off the native last-argument
conversion.  No native family-injectivity theorem is assumed. -/
theorem not_apart_family_conv_of_fundamental
    (hL : ReadbackLaws eqEnvT R)
    (hF : FundamentalSAtT (ctxModelT_approxT eqEnvT) R n) :
    ¬ Nonempty (ConvT eqEnvT n apartCtx apartRight
      (apartEqAt apartRight) (.sort .zero)) := by
  rintro ⟨hc⟩
  have hrel := fundConvAt_ctx_of_id (apartCtx_wf n) (apartCtx_identity R n)
    (hF.2 (apartCtx_wf n) hc) (.spine 63 [.bot, .bot, .bot])
    (Or.inl (apartRight_model EnvT.bot))
  obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, _, _, _, _, _, hca, _⟩ :=
    (lrSCoreS_spine_iff _ _ _ _ _ _).mp hrel
  have hm' : m = eqFamT := Option.some.inj hm.symm
  subst m
  have e₁ := redR_famApp_eq hL pinEqGroupWfT
    (r := 63) (m := eqFamT) rfl rfl h1
  have e₂ := redR_famApp_eq hL pinEqGroupWfT
    (r := 63) (m := eqFamT) rfl rfl h2
  obtain ⟨hc₁, hxs₁⟩ := foldApps_const_inj e₁
  obtain ⟨hc₂, hxs₂⟩ := foldApps_const_inj e₂
  have hls₁ := (Expr.const.inj hc₁).2
  have hls₂ := (Expr.const.inj hc₂).2
  subst ls₁; subst ls₂; subst xs₁; subst xs₂
  change ConvArgsT eqEnvT n apartCtx eqFamT.mtype
    [.sort .zero, idPiProp, idPiProp]
    [.sort .zero, idPiProp, apartRight] at hca
  cases hca with
  | cons _ _ _ _ _ _ _ hs₀ =>
      cases hs₀ with
      | cons _ _ _ _ _ _ _ hs₁ =>
          cases hs₁ with
          | cons _ _ _ _ _ _ hidx _ =>
              exact not_apart_index_conv_of_fundamental hL hF hidx

/-- Every candidate K witness at the source is excluded by the
hypothetical supplier.  Canonical-witness uniqueness comes from the new
composition of the existing Eq witness-environment lemmas. -/
theorem not_apart_native_head_of_fundamental
    (hL : ReadbackLaws eqEnvT R)
    (hF : FundamentalSAtT (ctxModelT_approxT eqEnvT) R n)
    (e : Expr Nat) : ¬ KNativeHead eqEnvT n apartCtx apartRec e := by
  intro h
  generalize he : apartRec = a at h
  cases h with
  | intro hK hnc hi hc =>
      simp only [apartRec, recCall_eq_app] at he
      have hh := (Expr.app.inj he).1
      obtain ⟨hconst, hp⟩ := foldApps_const_inj hh
      have hr := (Expr.const.inj hconst).1
      obtain ⟨hcomputed, hmajor⟩ := eqKCanon_families hr.symm hp.symm hK
      obtain ⟨hi⟩ := hi
      rw [hcomputed, hmajor] at hi
      exact not_apart_family_conv_of_fundamental hL hF ⟨hi⟩

/-- The model and native-gate parts of the countermodel compose with
the candidate's structural normality lemma.  No negative native typing
or conversion statement is an external premise. -/
theorem not_fundamental_of_apart_head_normality
    (hL : ReadbackLaws eqEnvT R)
    (hN : (∀ e, ¬ KNativeHead eqEnvT n apartCtx apartRec e) →
      NormalR R apartCtx apartRec) :
    ¬ FundamentalSAtT (ctxModelT_approxT eqEnvT) R n := by
  intro hF
  obtain ⟨ht⟩ := apartRec_typed n
  exact not_fundamentalSAtT_of_normal_prop_compact (apartCtx_wf n) ht
    (apartCtx_identity R n) (apartRec_model EnvT.bot)
    (hN (not_apart_native_head_of_fundamental hL hF))
    (fun _ he => Expr.noConfusion he) hF

/-- The full unchanged Fundamental input is uninhabited for candidate
(a), in the actual admitted Eq environment, at every level bound.  Its
own observations exclude its K gate and then contradict its typing
diagonal.  There is no external native nonconvertibility premise. -/
theorem not_fundamentalSAtT_whStepCK2_eqEnv (n : Nat) :
    ¬ FundamentalSAtT (ctxModelT_approxT eqEnvT) (WhStepCK2 eqEnvT n) n := by
  apply not_fundamental_of_apart_head_normality (readbackLaws_whStepCK2 eqEnvT n)
  intro hn
  exact normalR_kRec_of_no_native pinEqGroupWfT
    (w := eqConvW (fun _ _ h => h) (.sort .zero) idPiProp apartRight apartMot (.sort .zero))
    (Or.inl ⟨rfl, rfl, rfl⟩) not_isCtorSpine_bvar hn

/-- Any native head at this source has the fixed minor as its target.
This uniqueness statement does not assert that a native gate exists. -/
theorem kNativeHead_apartRec_target {e : Expr Nat}
    (h : KNativeHead eqEnvT n apartCtx apartRec e) : e = .sort .zero := by
  generalize he : apartRec = s at h
  cases h with
  | intro hK hnc hi hc =>
      simp only [apartRec, recCall_eq_app] at he
      obtain ⟨hconst, hp⟩ := foldApps_const_inj (Expr.app.inj he).1
      have hr := (Expr.const.inj hconst).1
      have hls := (Expr.const.inj hconst).2
      exact iotaRhsOf_kcanon_eq hK
        (w₂ := eqConvW (fun _ _ h => h) (.sort .zero) idPiProp apartRight apartMot (.sort .zero))
        (Or.inl ⟨rfl, rfl, rfl⟩) hr.symm hls.symm hp.symm

/-- Source classification in the complete candidate core: all possible
steps have the one model-compatible target, without assuming existence. -/
theorem whStepCK2_apartRec_target {e : Expr Nat}
    (h : WhStepCK2 eqEnvT n apartCtx apartRec e) : e = .sort .zero := by
  generalize he : apartRec = s at h
  cases h with
  | ctx h =>
      exact (whStepCtx_recCall_nonCtorMajor_aux pinEqGroupWfT (he.symm ▸ h)
        (w := eqConvW (fun _ _ h => h) (.sort .zero) idPiProp apartRight apartMot (.sort .zero))
        rfl not_isCtorSpine_bvar).elim
  | native h => exact kNativeHead_apartRec_target (he.symm ▸ h)
  | recMajor hm hr hl hnK hnP h =>
      have hh := (recCall_const_inj he).1
      exact (hnK ⟨eqGapW, hh, ⟨rfl, rfl, rfl⟩⟩).elim
  | appHead h =>
      simp only [apartRec, recCall_eq_app] at he
      have hh := (Expr.app.inj he).1
      rw [← hh] at h
      exact (normalR_recPrefixCK2 pinEqGroupWfT (r := 65) (m := eqRecT) rfl rfl
        apartCtx [.succ (.succ .zero)]
        [.sort .zero, idPiProp, apartMot, .sort .zero, apartRight] (by decide) _ h).elim

/-- The complete set of possible reduct shapes is sufficient to audit
the local realization guard, independently of Fundamental. -/
theorem redR_whStepCK2_apartRec_cases {e : Expr Nat}
    (h : RedR (WhStepCK2 eqEnvT n) apartCtx apartRec e) :
    e = apartRec ∨ e = .sort .zero := by
  cases h with
  | refl => exact Or.inl rfl
  | step hs hr =>
      rw [whStepCK2_apartRec_target hs] at hr
      exact Or.inr (redR_sort_eq (readbackLaws_whStepCK2 eqEnvT n) hr)

/-- The actual pointwise realization guard of the original adapter
holds at this source.  It sends an existing readback observation into
the model and does not supply Fundamental's opposite implication. -/
theorem apartRec_probeRealizedCK2 (n : Nat) :
    ProbeRealizedAtT (WhStepCK2 eqEnvT n) eqEnvT n apartCtx apartRec := by
  constructor
  · intro u hr
    rcases redR_whStepCK2_apartRec_cases hr with he | he
    · exact (show False from Expr.noConfusion he).elim
    · have hu := Expr.sort.inj he
      subst u
      exact apartRec_model _
  · intro A B hr _
    rcases redR_whStepCK2_apartRec_cases hr with he | he
    · exact (show False from Expr.noConfusion he).elim
    · exact (show False from Expr.noConfusion he).elim

/-- Candidate (b) stops at the rigid actual index.  This normality
proof uses only syntax and the existing family-normality law. -/
theorem apartRec_normalIndex :
    NormalR (WhStepIndexCK2 eqEnvT) apartCtx apartRec := by
  have hne : apartRight ≠ idPiProp :=
    TypedModelAudit.foldApps_const_ne_pi
      [.sort .zero, idPiProp, idPiProp] (.sort .zero) (.bvar 0)
  have hn : NormalR (WhStepCK eqEnvT) apartCtx apartRight := by
    intro e h
    exact (readbackLaws_whStepCK eqEnvT).famApp_normal pinEqGroupWfT apartCtx
      (r := 63) (m := eqFamT) rfl rfl [] [.sort .zero, idPiProp, idPiProp] e h
  exact normalR_whStepIndexCK2_eqIndex hne hn

/-- The typing motive already fails locally for candidate (b), at the
same actual typed, non-bottom model observation used for candidate (a). -/
theorem not_fundTyAt_whStepIndexCK2_apartRec (n : Nat) :
    ¬ FundTyAt (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT) n
      apartCtx apartRec (.sort (.succ .zero)) :=
  not_fundTyAt_of_normal_prop_compact (apartCtx_wf n)
    (apartCtx_identity (WhStepIndexCK2 eqEnvT) n) (apartRec_model EnvT.bot)
    apartRec_normalIndex (fun _ he => Expr.noConfusion he)

/-- The same model fixture rules out candidate (b)'s full global input
independently of its beta, binder, eta, and delta conversion controls. -/
theorem not_fundamentalSAtT_whStepIndexCK2_eqEnv (n : Nat) :
    ¬ FundamentalSAtT (ctxModelT_approxT eqEnvT) (WhStepIndexCK2 eqEnvT) n := by
  intro hF
  obtain ⟨ht⟩ := apartRec_typed n
  exact not_fundTyAt_whStepIndexCK2_apartRec n (hF.1 (apartCtx_wf n) ht)

/-- Candidate (b) also satisfies the local realization guard: this
normal source has no sort or Pi readback observation.  Its model still
has the non-bottom compact proved above, so this pointwise guard does
not supply the missing Fundamental direction. -/
theorem apartRec_probeRealizedIndex (n : Nat) :
    ProbeRealizedAtT (WhStepIndexCK2 eqEnvT) eqEnvT n apartCtx apartRec := by
  constructor
  · intro u hr
    exact (show False from Expr.noConfusion (redR_of_normal apartRec_normalIndex hr)).elim
  · intro A B hr _
    exact (show False from Expr.noConfusion (redR_of_normal apartRec_normalIndex hr)).elim

-- BEGIN RCIC_NATIVE_READBACK_CK2_MODEL_OBSTRUCTION_ROOTS
#print axioms apartEqAt
#print axioms apartRight
#print axioms apartCtx
#print axioms apartMot
#print axioms apartRec
#print axioms apartLeft_ty
#print axioms apartCtx_wf
#print axioms apartRec_typed
#print axioms apartCtx_identity
#print axioms apartCtx_ctxEnv_eq_bot
#print axioms apartCtx_identity_canonical
#print axioms apartCtx_typed_identity
#print axioms apartRec_model
#print axioms apartRec_typed_model_seed
#print axioms apartRec_argTyped
#print axioms apartRight_model
#print axioms apart_separating_compacts_typed
#print axioms not_apart_index_conv_of_fundamental
#print axioms not_apart_family_conv_of_fundamental
#print axioms not_apart_native_head_of_fundamental
#print axioms not_fundamental_of_apart_head_normality
#print axioms not_fundamentalSAtT_whStepCK2_eqEnv
#print axioms kNativeHead_apartRec_target
#print axioms whStepCK2_apartRec_target
#print axioms redR_whStepCK2_apartRec_cases
#print axioms apartRec_probeRealizedCK2
#print axioms apartRec_normalIndex
#print axioms not_fundTyAt_whStepIndexCK2_apartRec
#print axioms not_fundamentalSAtT_whStepIndexCK2_eqEnv
#print axioms apartRec_probeRealizedIndex
-- END RCIC_NATIVE_READBACK_CK2_MODEL_OBSTRUCTION_ROOTS

end Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit
