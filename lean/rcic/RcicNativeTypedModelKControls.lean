import rcic.RcicNativeTypedModelK
import rcic.RcicNativeTypedModelKObstruction

/-!
# Kernel controls for the saturated K model

Prefix-only-bottom is a statement about the complete new grammar, including
the whole-fragment import, ordinary applications, delta, structured iota and
native K.  It is the check that prevents an empty-demand function compact
from bypassing the saturated native gate.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKControlAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeModelBoundaryAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKGuardAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelKObstructionAudit

variable {n : Nat} {Γ : LCtx} {ρ : EnvT}

private theorem eqWitness_preLength (w : IotaWitness eqEnvT) (hr : w.recRef = 65) :
    w.preMajor.length = 5 := by
  have hm : w.recMember = eqRecT := by
    have h := w.hrec
    rw [hr] at h
    exact (Option.some.inj h).symm
  have hn := w.hnmin
  rw [hm] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 6 at hn
  have hp := w.hpre
  omega

/-- No unsaturated Eq recursor has a non-bottom compact, at any context or environment. -/
theorem approxTK_eqRec_prefix_bot {e : Expr Nat} {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ e c) :
    ∀ {ls : List Level} {xs : List (Expr Nat)},
      appsSpine e = (.const 65 ls, xs) → xs.length < 6 → c = .bot := by
  induction h with
  | bot => intro _ _ _ _; rfl
  | free hf _ =>
      intro ls xs he _
      obtain ⟨S, hS, hs⟩ := hf
      exact (hS.noIndexed 65 (hs 65 (occursConst_true_of_head he)) indexedPropRecT_eqRec).elim
  | pi _ _ _ _ _ => intro ls xs he _; cases (Prod.mk.inj he).1
  | lam _ _ _ _ _ _ => intro ls xs he _; cases (Prod.mk.inj he).1
  | @app Γ ρ f a g s hf hs ha ihf iha =>
      intro ls xs he hlen
      have hh : (appsSpine f).1 = .const 65 ls := (Prod.mk.inj he).1
      have hl : (appsSpine f).2.length < 6 := by
        have h := congrArg (fun p => p.2.length) he
        simp only [appsSpine, List.length_append, List.length_singleton] at h
        omega
      exact CptT.noConfusion (ihf (Prod.ext hh rfl) hl)
  | @appSpine Γ ρ f a r args u hf ha ihf iha =>
      intro ls xs he hlen
      have hh : (appsSpine f).1 = .const 65 ls := (Prod.mk.inj he).1
      have hl : (appsSpine f).2.length < 6 := by
        have h := congrArg (fun p => p.2.length) he
        simp only [appsSpine, List.length_append, List.length_singleton] at h
        omega
      exact CptT.noConfusion (ihf (Prod.ext hh rfl) hl)
  | @delta Γ ρ r ls m b c hd h ih =>
      intro ls' xs he _
      have hr : r = 65 := (Expr.const.inj (Prod.mk.inj he).1).1
      subst r
      obtain ⟨hm, _, hnrec, _⟩ := hd
      have hem : m = eqRecT := (Option.some.inj hm).symm
      subst m
      exact (hnrec rfl).elim
  | letE _ _ => intro ls xs he _; cases (Prod.mk.inj he).1
  | lit _ _ => intro ls xs he _; cases (Prod.mk.inj he).1
  | iota w hs hr ih =>
      intro ls xs he hlen
      have hh := congrArg Prod.fst he
      simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const] at hh
      have hw : w.recRef = 65 := (Expr.const.inj hh).1
      have hp := (eqRec_model_schema w hw).2.1
      have hl := congrArg (fun p => p.2.length) he
      simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const,
        List.length_append, List.length_singleton, hp] at hl
      exfalso
      omega
  | recursorPropK w x hk hn hi hc hs hr ih =>
      intro ls xs he hlen
      have hh := congrArg Prod.fst he
      simp only [recCall, appsSpine_foldApps_const] at hh
      have hw : w.recRef = 65 := (Expr.const.inj hh).1
      have hp := eqWitness_preLength w hw
      have hl := congrArg (fun p => p.2.length) he
      simp only [recCall, appsSpine_foldApps_const,
        List.length_append, List.length_singleton, hp] at hl
      exfalso
      omega

theorem approxTK_eqRec_fold_prefix_bot {ls : List Level} {xs : List (Expr Nat)}
    (hlen : xs.length < 6) {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ (foldApps (.const 65 ls) xs) c) : c = .bot :=
  approxTK_eqRec_prefix_bot h (appsSpine_foldApps_const _ _ _) hlen

theorem approxTK_eqRec_const_bot (ls : List Level) {c : CptT}
    (h : ApproxTK eqEnvT n Γ ρ (.const 65 ls) c) : c = .bot :=
  approxTK_eqRec_prefix_bot h rfl (by decide : ([] : List (Expr Nat)).length < 6)

/-- At a neutral saturated Eq call every non-bottom observation carries
the actual native guard.  A witness for another index list cannot be used. -/
theorem approxTK_eqRec_bvar_inv {ls : List Level} {pre : List (Expr Nat)}
    {i : Nat} {c : CptT} (hpre : pre.length = 5)
    (h : ApproxTK eqEnvT n Γ ρ (recCall (.const 65 ls) pre (.bvar i)) c) :
    c = .bot ∨ ∃ w : IotaWitness eqEnvT,
      w.recRef = 65 ∧ w.preMajor = pre ∧ KCanonW w (.bvar i) ∧
        KIndexGuardAt eqEnvT n Γ w := by
  generalize he : recCall (.const 65 ls) pre (.bvar i) = e at h
  cases h with
  | bot => exact Or.inl rfl
  | free hf _ =>
      rw [← he] at hf
      exact (not_kFreeT_eqRec_spine _ _ hf).elim
  | pi _ _ _ => simp only [recCall_eq_app] at he; cases he
  | lam _ _ _ _ => simp only [recCall_eq_app] at he; cases he
  | app hf hs ha =>
      simp only [recCall_eq_app] at he
      have hh := (Expr.app.inj he).1
      rw [← hh] at hf
      exact CptT.noConfusion (approxTK_eqRec_fold_prefix_bot (by omega) hf)
  | appSpine hf ha =>
      simp only [recCall_eq_app] at he
      have hh := (Expr.app.inj he).1
      rw [← hh] at hf
      exact CptT.noConfusion (approxTK_eqRec_fold_prefix_bot (by omega) hf)
  | delta _ _ => simp only [recCall_eq_app] at he; cases he
  | letE _ => simp only [recCall_eq_app] at he; cases he
  | lit _ => simp only [recCall_eq_app] at he; cases he
  | iota w hs hr =>
      simp only [iotaLhsOfS, recCall_eq_app] at he
      have hh := congrArg (fun e => (appsSpine e).1) (Expr.app.inj he).2
      simp only [appsSpine, appsSpine_foldApps_const] at hh
      cases hh
  | recursorPropK w x hk hn hi hc hs hr =>
      simp only [recCall_eq_app] at he
      obtain ⟨hh, hp⟩ := foldApps_const_inj (Expr.app.inj he).1
      have hrec := (Expr.const.inj hh).1
      have hx := (Expr.app.inj he).2
      cases hx
      exact Or.inr ⟨w, hrec.symm, hp.symm, hk, hi⟩

/-- The original apart-index countermodel has no non-bottom observation. -/
theorem approxTK_apartRec_bot {c : CptT}
    (h : ApproxTK eqEnvT n apartCtx ρ apartRec c) : c = .bot := by
  rcases approxTK_eqRec_bvar_inv (by decide) h with hb | ⟨w, hr, hp, hk, hi⟩
  · exact hb
  · exact (not_indexAgreementDI_apart hr hp hk hi.2).elim

theorem not_approxTK_apartRec_prop :
    ¬ ApproxTK eqEnvT n apartCtx ρ apartRec .prop :=
  fun h => CptT.noConfusion (approxTK_apartRec_bot h)

/-- The positive original gap uses the native and independent gates separately. -/
theorem approxTK_eqGap_prop (n : Nat) (ρ : EnvT) :
    ApproxTK eqEnvT n eqGapCtx ρ eqGapRedex .prop := by
  exact .recursorPropK eqGapW (.bvar 0) (Or.inl ⟨rfl, rfl, rfl⟩)
    not_isCtorSpine_bvar (kIndexGuardAt_eqGap n) (kCommonAt_eqGap n)
    (eqRec_model_minor_backward (approxT_sort_code eqEnvT ρ .zero))
    (approxTK_sort_code eqEnvT n eqGapCtx ρ .zero)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_CONTROL_ROOTS
#print axioms approxTK_eqRec_prefix_bot
#print axioms approxTK_eqRec_fold_prefix_bot
#print axioms approxTK_eqRec_const_bot
#print axioms approxTK_eqRec_bvar_inv
#print axioms approxTK_apartRec_bot
#print axioms not_approxTK_apartRec_prop
#print axioms approxTK_eqGap_prop
-- END RCIC_NATIVE_TYPED_MODEL_K_CONTROL_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKControlAudit
