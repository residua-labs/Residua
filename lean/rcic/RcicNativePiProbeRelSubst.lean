import rcic.RcicNativePiProbeRelBridge
import rcic.RcicNativePiProbeRelIota
import rcic.RcicNativePiProbeCongruence

/-!
# Related substitutions supply the two native let residues

`FundConvAt` changes the body at the fixed left value. `FundTyAt` changes
the substitution in the right body. The two applications of the existing
fundamental motives therefore have exactly the endpoints recorded by
`MixedSubstEdgesT`; no new fundamental constructor case is proved here.

The model inputs are local: related substitutions into the actual old let
context, and realization of the observed instantiated bodies in the source
model environments. No universal backward model transport is assumed.
The witness section checks these inputs on typed, observed instances.

All declarations are additive. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeRelSubstAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeCongruenceAudit
open Rcic.Declarative.NativeValleys.PiProbeRelBridgeAudit
open Rcic.Declarative.NativeValleys.PiProbeRelIotaAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ## The two distinct uses of the existing fundamental motives -/

/-- Body conversion is instantiated twice at the left value. The related
substitution still checks every let-bound variable's stored value. -/
theorem bodyAtValue_of_fundConvAtT
    (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {ρ : EnvT} {A value body body' B : Expr Nat}
    (hS : RelSubstAtT M R n Γ ρ ρ
      (SubstT.cons value SubstT.id) (SubstT.cons value SubstT.id)
      (.letBinding A value :: Γ))
    (hbody : FundConvAt M R n (.letBinding A value :: Γ) body body' B)
    (hleft : ModelProbeAtSubstT M R n Γ ρ (SubstT.cons value SubstT.id) body)
    (hright : ModelProbeAtSubstT M R n Γ ρ (SubstT.cons value SubstT.id) body') :
    ProbeEquivT R E n Γ (instantiate0 value body) (instantiate0 value body') := by
  have h := probeEquiv_of_fundRelationT hL hNU hW hΓ hleft hright
    (fun c hc => hbody hΓ hS c hc)
  simpa only [substT_cons_id] using h

/-- Typing of the right body is instantiated at the two related values.
This is a use of `FundTyAt`, with no new body-conversion premise. -/
theorem valueInBody_of_fundTyAtT
    (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {ρ ρ' : EnvT} {A value value' body' B : Expr Nat}
    (hS : RelSubstAtT M R n Γ ρ ρ'
      (SubstT.cons value SubstT.id) (SubstT.cons value' SubstT.id)
      (.letBinding A value :: Γ))
    (hbody' : FundTyAt M R n (.letBinding A value :: Γ) body' B)
    (hleft : ModelProbeAtSubstT M R n Γ ρ (SubstT.cons value SubstT.id) body')
    (hright : ModelProbeAtSubstT M R n Γ ρ' (SubstT.cons value' SubstT.id) body') :
    ProbeEquivT R E n Γ (instantiate0 value body') (instantiate0 value' body') := by
  have h := probeEquiv_of_fundRelationT hL hNU hW hΓ hleft hright
    (fun c hc => hbody' hΓ hS c hc)
  simpa only [substT_cons_id] using h

/-- Composition of the two localized source-model facts gives precisely
the existing mixed-substitution package. Its three realization inputs
refer to the three instantiated bodies that the package visits. -/
theorem mixedSubstEdges_of_fundAtT
    (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {ρ ρ' : EnvT} {A value value' body body' B : Expr Nat}
    (hSame : RelSubstAtT M R n Γ ρ ρ
      (SubstT.cons value SubstT.id) (SubstT.cons value SubstT.id)
      (.letBinding A value :: Γ))
    (hMixed : RelSubstAtT M R n Γ ρ ρ'
      (SubstT.cons value SubstT.id) (SubstT.cons value' SubstT.id)
      (.letBinding A value :: Γ))
    (hbody : FundConvAt M R n (.letBinding A value :: Γ) body body' B)
    (hbody' : FundTyAt M R n (.letBinding A value :: Γ) body' B)
    (hleft : ModelProbeAtSubstT M R n Γ ρ (SubstT.cons value SubstT.id) body)
    (hmiddle : ModelProbeAtSubstT M R n Γ ρ (SubstT.cons value SubstT.id) body')
    (hright : ModelProbeAtSubstT M R n Γ ρ' (SubstT.cons value' SubstT.id) body') :
    MixedSubstEdgesT R E n Γ value value' body body' :=
  ⟨bodyAtValue_of_fundConvAtT hL hNU hW hΓ hSame hbody hleft hmiddle,
    valueInBody_of_fundTyAtT hL hNU hW hΓ hMixed hbody' hmiddle hright⟩

/-- The two required motives are projected from a supplied fundamental
lemma at the actual native let premises. The right body's typing is
obtained from `convEnds` in the old let context. -/
theorem mixedSubstEdges_letE_of_fundamentalSAtT
    (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {M : CtxModelT E} (hF : FundamentalSAtT M R n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {ρ ρ' : EnvT}
    {A A' value value' body body' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hv : ConvT E n Γ value value' A)
    (hb : ConvT E n (.letBinding A value :: Γ) body body' B)
    (hSame : RelSubstAtT M R n Γ ρ ρ
      (SubstT.cons value SubstT.id) (SubstT.cons value SubstT.id)
      (.letBinding A value :: Γ))
    (hMixed : RelSubstAtT M R n Γ ρ ρ'
      (SubstT.cons value SubstT.id) (SubstT.cons value' SubstT.id)
      (.letBinding A value :: Γ))
    (hleft : ModelProbeAtSubstT M R n Γ ρ (SubstT.cons value SubstT.id) body)
    (hmiddle : ModelProbeAtSubstT M R n Γ ρ (SubstT.cons value SubstT.id) body')
    (hright : ModelProbeAtSubstT M R n Γ ρ' (SubstT.cons value' SubstT.id) body') :
    MixedSubstEdgesT R E n Γ value value' body body' := by
  have hLet : CtxWfT E n (.letBinding A value :: Γ) :=
    .letBinding Γ A u value hΓ (convEnds hW hΓ hA).1 (convEnds hW hΓ hv).1
  exact mixedSubstEdges_of_fundAtT hL hNU hW hΓ hSame hMixed
    (hF.2 hLet hb) (hF.1 hLet (convEnds hW hLet hb).2.1)
    hleft hmiddle hright

/-! ## Typed related substitutions for a closed let -/

/-- The empty source has no substituted variables or stored values. -/
theorem relSubstAtT_empty {M : CtxModelT E} (Δ : LCtx)
    (ρ ρ' : EnvT) (σ σ' : SubstT) : RelSubstAtT M R n Δ ρ ρ' σ σ' [] := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals intro i
  all_goals simp [lookupType, lookupValue]

/-- An explicit singleton-let extension. The four semantic pairings are
checked on the compacts assigned to the binder and on every compact of
its old stored value. The latter check is required by `RelSubstAtT`. -/
theorem relSubstAtT_singletonLet
    {M : CtxModelT E} (hM : CtxModelTLaws M)
    {ρ ρ' : EnvT} {S S' : CptT → Prop} {A value value' : Expr Nat}
    (hv : HasTyT E n [] value A) (hv' : HasTyT E n [] value' A)
    (hc : ConvT E n [] value value' A)
    (hrel : ∀ c, S c ∨ S' c ∨ M.Ap ρ value c ∨ M.Ap ρ' value c →
      LRSCoreS R E n [] value value' A c ∧
      LRSCoreS R E n [] value' value A c ∧
      LRSCoreS R E n [] value value A c ∧
      LRSCoreS R E n [] value' value' A c) :
    RelSubstAtT M R n [] (EnvT.cons S ρ) (EnvT.cons S' ρ')
      (SubstT.cons value SubstT.id) (SubstT.cons value' SubstT.id)
      [.letBinding A value] := by
  have hcancel (v X : Expr Nat) :
      substT (SubstT.cons v SubstT.id) (lift 0 1 X) = X := by
    rw [substT_cons_lift, substT_id]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i T ht
    cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at ht
        injection ht with ht
        subst ht
        exact ⟨by rw [hcancel]; exact hv⟩
    | succ i => simp [lookupType, List.get?_cons_succ] at ht
  · intro i v hlookup
    cases i with
    | zero =>
        simp only [lookupValue, List.get?_cons_zero] at hlookup
        injection hlookup with hlookup
        subst hlookup
        exact ⟨lift 0 1 A, rfl, ⟨by rw [hcancel, hcancel]; exact .refl _ _ _ hv⟩⟩
    | succ i => simp [lookupValue, List.get?_cons_succ] at hlookup
  · intro i T ht
    cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at ht
        injection ht with ht
        subst ht
        exact ⟨by rw [hcancel]; exact hv'⟩
    | succ i => simp [lookupType, List.get?_cons_succ] at ht
  · intro i v hlookup
    cases i with
    | zero =>
        simp only [lookupValue, List.get?_cons_zero] at hlookup
        injection hlookup with hlookup
        subst hlookup
        exact ⟨lift 0 1 A, rfl, ⟨by rw [hcancel, hcancel]; exact .symm _ _ _ _ hc⟩⟩
    | succ i => simp [lookupValue, List.get?_cons_succ] at hlookup
  · intro i T ht
    cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at ht
        injection ht with ht
        subst ht
        exact ⟨by rw [hcancel]; exact hc⟩
    | succ i => simp [lookupType, List.get?_cons_succ] at ht
  · intro i T ht c hcompact
    cases i with
    | zero =>
        simp only [lookupType, List.get?_cons_zero] at ht
        injection ht with ht
        subst ht
        simpa only [hcancel, SubstT.cons_zero] using
          hrel c (hcompact.elim Or.inl (fun h => Or.inr (Or.inl h)))
    | succ i => simp [lookupType, List.get?_cons_succ] at ht
  · intro i v T hlookup ht c hcompact
    cases i with
    | zero =>
        simp only [lookupValue, List.get?_cons_zero] at hlookup
        simp only [lookupType, List.get?_cons_zero] at ht
        injection hlookup with hlookup
        injection ht with ht
        subst hlookup
        subst ht
        have hcompact' : S c ∨ S' c ∨ M.Ap ρ value c ∨ M.Ap ρ' value c := by
          rcases hcompact with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl (hM.lift0_elim h)))
          · exact Or.inr (Or.inr (Or.inr (hM.lift0_elim h)))
        obtain ⟨_, hreverse, hleft, _⟩ := hrel c hcompact'
        simpa only [hcancel, SubstT.cons_zero] using
          And.intro hleft (And.intro hreverse (And.intro hleft hreverse))
    | succ i => simp [lookupValue, List.get?_cons_succ] at hlookup

/-! ## The selected context readback and the native let constructor -/

/-- The selected context readback computes both lets before the two
substitution edges are composed. This supplies only this constructor. -/
theorem convProbe_letE_of_mixedSubst_whStepCK
    (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A A' value value' body body' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hv : ConvT E n Γ value value' A)
    (hb : ConvT E n (.letBinding A value :: Γ) body body' B)
    (hsubst : MixedSubstEdgesT (WhStepCK E) E n Γ value value' body body') :
    ConvProbeMotiveT (WhStepCK E)
      (.letE Γ A A' value value' body body' B u hA hv hb) := by
  exact (probeEquiv_iff_of_endsT hW hΓ
    (probeEquiv_ctx_whStepCK hW (.zeta A value body))
    (probeEquiv_ctx_whStepCK hW (.zeta A' value' body'))).mpr
      (probeEquiv_subst_of_edgesT hW hΓ hsubst)

/-- The native let arm from exactly the two local fundamental motives,
the related substitutions, and the three source-model realizations. -/
theorem convProbe_letE_of_fundAt_whStepCK
    (hW : EnvWfT E) {M : CtxModelT E} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {ρ ρ' : EnvT} {A A' value value' body body' B : Expr Nat} {u : Level}
    (hA : ConvT E n Γ A A' (.sort u))
    (hv : ConvT E n Γ value value' A)
    (hb : ConvT E n (.letBinding A value :: Γ) body body' B)
    (hSame : RelSubstAtT M (WhStepCK E) n Γ ρ ρ
      (SubstT.cons value SubstT.id) (SubstT.cons value SubstT.id)
      (.letBinding A value :: Γ))
    (hMixed : RelSubstAtT M (WhStepCK E) n Γ ρ ρ'
      (SubstT.cons value SubstT.id) (SubstT.cons value' SubstT.id)
      (.letBinding A value :: Γ))
    (hbody : FundConvAt M (WhStepCK E) n (.letBinding A value :: Γ) body body' B)
    (hbody' : FundTyAt M (WhStepCK E) n (.letBinding A value :: Γ) body' B)
    (hleft : ModelProbeAtSubstT M (WhStepCK E) n Γ ρ
      (SubstT.cons value SubstT.id) body)
    (hmiddle : ModelProbeAtSubstT M (WhStepCK E) n Γ ρ
      (SubstT.cons value SubstT.id) body')
    (hright : ModelProbeAtSubstT M (WhStepCK E) n Γ ρ'
      (SubstT.cons value' SubstT.id) body') :
    ConvProbeMotiveT (WhStepCK E)
      (.letE Γ A A' value value' body body' B u hA hv hb) :=
  convProbe_letE_of_mixedSubst_whStepCK hW hΓ hA hv hb
    (mixedSubstEdges_of_fundAtT (readbackLaws_whStepCK E)
      (normalUniqueR_whStepCK hW) hW hΓ hSame hMixed hbody hbody'
      hleft hmiddle hright)

/-! ## Actual source-model witnesses with a dependent body -/

/-- A syntactically changed value, with the same typed zeta contractum. -/
def letProbeValueWrap (A value : Expr Nat) : Expr Nat :=
  .letE A value (.bvar 0)

theorem letProbe_inst_lift (value A : Expr Nat) :
    instantiate0 value (lift 0 1 A) = A := by
  rw [← substT_cons_id, substT_cons_lift, substT_id]

def letProbeValueWrapTyping {A value : Expr Nat} {u : Level}
    (hA : HasTyT E n [] A (.sort u)) (hv : HasTyT E n [] value A) :
    HasTyT E n [] (letProbeValueWrap A value) A := by
  have h := HasTyT.letE [] A u value (lift 0 1 A) (.bvar 0) hA hv
    (.bvar [.letBinding A value] 0 (lift 0 1 A) rfl)
  simpa only [letProbe_inst_lift] using h

def letProbeValueWrapZeta {A value : Expr Nat} {u : Level}
    (hA : HasTyT E n [] A (.sort u)) (hv : HasTyT E n [] value A) :
    ConvT E n [] (letProbeValueWrap A value) value A := by
  have h := ConvT.zeta [] A value (.bvar 0) (lift 0 1 A) u hA hv
    (.bvar [.letBinding A value] 0 (lift 0 1 A) rfl)
  rw [letProbe_inst_lift] at h
  exact h

/-- The source environment assigns the binder exactly the old value's
actual model compacts. It does not assign only bottom. -/
def letProbeSourceEnv (E : ResolvedEnv) (value : Expr Nat) : EnvT :=
  EnvT.cons (ApproxT E EnvT.bot value) EnvT.bot

theorem lrSCoreS_self_of_fundTyAt_empty
    {M : CtxModelT E} {value A : Expr Nat}
    (h : FundTyAt M R n [] value A) {c : CptT}
    (hc : M.Ap EnvT.bot value c) : LRSCoreS R E n [] value value A c := by
  have h' := h (.nil : CtxWfT E n [])
    (relSubstAtT_empty [] EnvT.bot EnvT.bot SubstT.id SubstT.id) c (Or.inl hc)
  simpa only [substT_id] using h'

/-- The same-value and changed-value related substitutions are both
constructed, including the stored-value field, from actual approximants
and the existing relation's readback expansion lemmas. -/
theorem letProbe_zeta_relatedSubsts
    {A value : Expr Nat} {u : Level}
    (hA : HasTyT E n [] A (.sort u)) (hv : HasTyT E n [] value A)
    (hself : ∀ c, ApproxT E EnvT.bot value c →
      LRSCoreS (WhStepCK E) E n [] value value A c) :
    RelSubstAtT (ctxModelT_approxT E) (WhStepCK E) n []
      (letProbeSourceEnv E value) (letProbeSourceEnv E value)
      (SubstT.cons value SubstT.id) (SubstT.cons value SubstT.id)
      [.letBinding A value] ∧
    RelSubstAtT (ctxModelT_approxT E) (WhStepCK E) n []
      (letProbeSourceEnv E value) (letProbeSourceEnv E value)
      (SubstT.cons value SubstT.id) (SubstT.cons (letProbeValueWrap A value) SubstT.id)
      [.letBinding A value] := by
  have hL := readbackLaws_whStepCK E
  have hs : WhStepCK E [] (letProbeValueWrap A value) value :=
    .ctx (.zeta A value (.bvar 0))
  have hvc := letProbeValueWrapZeta hA hv
  have hvt := letProbeValueWrapTyping hA hv
  constructor
  · apply relSubstAtT_singletonLet (ctxModelTLaws_approxT E) hv hv (.refl _ _ _ hv)
    intro c hc
    have hcomp : ApproxT E EnvT.bot value c := by
      rcases hc with h | h | h | h <;> exact h
    have h := hself c hcomp
    exact ⟨h, h, h, h⟩
  · apply relSubstAtT_singletonLet (ctxModelTLaws_approxT E) hv hvt (.symm _ _ _ _ hvc)
    intro c hc
    have hcomp : ApproxT E EnvT.bot value c := by
      rcases hc with h | h | h | h <;> exact h
    have h := hself c hcomp
    exact ⟨lrSCoreS_expand_right hL hs c h,
      lrSCoreS_expand hL hs c h, h,
      lrSCoreS_expand hL hs c (lrSCoreS_expand_right hL hs c h)⟩

/-- The old value's realization realizes the genuinely dependent body
`bvar 0` in the source environment, at its instantiated left endpoint. -/
theorem modelProbe_bvar_at_value
    {value : Expr Nat}
    (hreal : ModelProbeAtSubstT (ctxModelT_approxT E) R n [] EnvT.bot SubstT.id value) :
    ModelProbeAtSubstT (ctxModelT_approxT E) R n [] (letProbeSourceEnv E value)
      (SubstT.cons value SubstT.id) (.bvar 0) := by
  constructor
  · intro u hread
    exact ApproxT.bvar (hreal.sorts u (by simpa only [substT_id] using hread))
  · intro A B hread hΓA
    exact ApproxT.bvar (hreal.pis A B (by simpa only [substT_id] using hread) hΓA)

/-- The selected readback cancels the wrapper before realizing the same
source body. Only observation compacts are requested from the old value. -/
theorem modelProbe_bvar_at_zeta_value
    (hW : EnvWfT E) (A : Expr Nat) {value : Expr Nat}
    (hreal : ModelProbeAtSubstT (ctxModelT_approxT E) (WhStepCK E) n []
      EnvT.bot SubstT.id value) :
    ModelProbeAtSubstT (ctxModelT_approxT E) (WhStepCK E) n []
      (letProbeSourceEnv E value)
      (SubstT.cons (letProbeValueWrap A value) SubstT.id) (.bvar 0) := by
  have hL := readbackLaws_whStepCK E
  constructor
  · intro u hread
    have hread' := (redR_ctx_whStepCK_iff hW (.zeta A value (.bvar 0))
      (hL.sort_normal [] u)).mp hread
    exact ApproxT.bvar (hreal.sorts u (by simpa only [substT_id] using hread'))
  · intro C D hread hΓC
    have hread' := (redR_ctx_whStepCK_iff hW (.zeta A value (.bvar 0))
      (hL.pi_normal [] C D)).mp hread
    exact ApproxT.bvar (hreal.pis C D (by simpa only [substT_id] using hread') hΓC)

/-- A reusable typed instance of every local adapter input. The native
body is a variable, and the values differ by an actual zeta computation. -/
theorem mixedSubstEdges_bvar_zeta_value
    (hW : EnvWfT E) {A value : Expr Nat} {u : Level}
    (hA : HasTyT E n [] A (.sort u)) (hv : HasTyT E n [] value A)
    (hself : ∀ c, ApproxT E EnvT.bot value c →
      LRSCoreS (WhStepCK E) E n [] value value A c)
    (hreal : ModelProbeAtSubstT (ctxModelT_approxT E) (WhStepCK E) n []
      EnvT.bot SubstT.id value) :
    MixedSubstEdgesT (WhStepCK E) E n [] value (letProbeValueWrap A value)
      (.bvar 0) (.bvar 0) := by
  obtain ⟨hSame, hMixed⟩ := letProbe_zeta_relatedSubsts hA hv hself
  have hbody : FundTyAt (ctxModelT_approxT E) (WhStepCK E) n
      [.letBinding A value] (.bvar 0) (lift 0 1 A) :=
    fundT_bvar (ctxModelTLaws_approxT E) (Γ := [.letBinding A value]) 0 (lift 0 1 A) rfl
  have hleft := modelProbe_bvar_at_value hreal
  exact mixedSubstEdges_of_fundAtT (readbackLaws_whStepCK E)
    (normalUniqueR_whStepCK hW) hW .nil hSame hMixed
    (fundT_refl hbody) hbody hleft hleft (modelProbe_bvar_at_zeta_value hW A hreal)

/-- Realization at a syntactic sort uses its actual `sortCode`, including
the distinction between proposition and higher-sort compacts. -/
theorem letProbe_model_sort_id (hL : ReadbackLaws E R) (l : Level) :
    ModelProbeAtSubstT (ctxModelT_approxT E) R n [] EnvT.bot SubstT.id (.sort l) := by
  constructor
  · intro u hread
    have hu := Expr.sort.inj (redR_sort_eq hL hread)
    subst u
    exact .sort _ _
  · intro A B hread _
    exact (Expr.noConfusion (redR_sort_eq hL hread) : False).elim

theorem letProbe_model_pi_id (hL : ReadbackLaws E R) (A B : Expr Nat) :
    ModelProbeAtSubstT (ctxModelT_approxT E) R n [] EnvT.bot SubstT.id (.pi A B) := by
  constructor
  · intro u hread
    have hread' : RedR R [] (.pi A B) (.sort u) := by
      simpa only [substT_id] using hread
    exact (Expr.noConfusion (redR_pi_eq hL hread') : False).elim
  · intro _ _ _ _
    exact approxT_pi_bot_nil _ _ _ _

def letProbeNativeLetConv {A value : Expr Nat} {u : Level}
    (hA : HasTyT E n [] A (.sort u)) (hv : HasTyT E n [] value A) :
    ConvT E n [] (.letE A value (.bvar 0))
      (.letE A (letProbeValueWrap A value) (.bvar 0)) A := by
  have hc : ConvT E n [] value (letProbeValueWrap A value) A :=
    .symm _ _ _ _ (letProbeValueWrapZeta hA hv)
  have hb : ConvT E n [.letBinding A value] (.bvar 0) (.bvar 0) (lift 0 1 A) :=
    .refl _ _ _ (.bvar _ 0 _ rfl)
  have h := ConvT.letE [] A A value (letProbeValueWrap A value) (.bvar 0) (.bvar 0)
    (lift 0 1 A) u (.refl _ _ _ hA) hc hb
  simpa only [letProbe_inst_lift] using h

theorem letProbeNativeLetConv_motive
    (hW : EnvWfT E) {A value : Expr Nat} {u : Level}
    (hA : HasTyT E n [] A (.sort u)) (hv : HasTyT E n [] value A)
    (hedges : MixedSubstEdgesT (WhStepCK E) E n [] value (letProbeValueWrap A value)
      (.bvar 0) (.bvar 0)) :
    ConvProbeMotiveT (WhStepCK E) (letProbeNativeLetConv hA hv) := by
  exact convProbe_letE_of_mixedSubst_whStepCK hW .nil (.refl _ _ _ hA)
    (.symm _ _ _ _ (letProbeValueWrapZeta hA hv))
    (.refl _ _ _ (.bvar _ 0 (lift 0 1 A) rfl)) hedges

/-! Both concrete pins below use `ApproxT`, the canonical context
readback, a well-formed old let context, and a dependent variable body.
The right value is syntactically different in both pins. -/

def letProbeSortType : Expr Nat := .sort (.succ .zero)
def letProbePiValue : Expr Nat := .pi (.sort .zero) (.sort .zero)
def letProbePiType : Expr Nat := .sort (.imax (.succ .zero) (.succ .zero))

theorem letProbe_sort_mixedSubstEdges :
    MixedSubstEdgesT (WhStepCK emptyEnv) emptyEnv 0 [] (.sort .zero)
      (letProbeValueWrap letProbeSortType (.sort .zero)) (.bvar 0) (.bvar 0) := by
  apply mixedSubstEdges_bvar_zeta_value (.empty : EnvWfT emptyEnv)
    (.sort [] (.succ .zero)) (.sort [] .zero)
  · intro c hc
    exact lrSCoreS_self_of_fundTyAt_empty
      (fundT_sort (ctxModelTLaws_approxT emptyEnv) (Γ := []) .zero) hc
  · exact letProbe_model_sort_id (readbackLaws_whStepCK emptyEnv) .zero

/-- The native invariants used by the existing Pi link hold in the
chosen environment; there is no recursor declaration at which iota
substitution could fail. -/
theorem letProbe_iotaSubstT_empty : IotaSubstT emptyEnv := by
  intro lhs rhs hi _
  cases hi with
  | of w =>
      have h := w.hrec
      simp [emptyEnv] at h

/-- Composition of the existing sort and Pi fundamental links supplies
the complete value relation, at every actual compact of this Pi. -/
theorem letProbe_pi_fundTyAt :
    FundTyAt (ctxModelT_approxT emptyEnv) (WhStepCK emptyEnv) 0 []
      letProbePiValue letProbePiType := by
  intro Δ ρ ρ' σ σ' hΔ hS c hc
  have hW : EnvWfT emptyEnv := .empty
  have hcl := envClosed_of_envWfT hW
  exact fundT_pi (readbackLaws_whStepCK emptyEnv) (normalUniqueR_whStepCK hW)
    hW hcl (envMembersSubstTStable_of_envClosed hcl) letProbe_iotaSubstT_empty
    (convArgsSymmS_emptyEnv 0) (convArgsTransS_emptyEnv 0)
    (ctxModelTLaws_approxT emptyEnv) .nil (.sort [] .zero) (.sort _ .zero)
    (fundT_sort (ctxModelTLaws_approxT emptyEnv) (Γ := []) .zero)
    (fundT_sort (ctxModelTLaws_approxT emptyEnv) (Γ := [.assumption (.sort .zero)]) .zero)
    hΔ hS c hc

def letProbePiTyping : HasTyT emptyEnv 0 [] letProbePiValue letProbePiType :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort [] .zero) (.sort _ .zero)

theorem letProbe_pi_mixedSubstEdges :
    MixedSubstEdgesT (WhStepCK emptyEnv) emptyEnv 0 [] letProbePiValue
      (letProbeValueWrap letProbePiType letProbePiValue) (.bvar 0) (.bvar 0) := by
  apply mixedSubstEdges_bvar_zeta_value (.empty : EnvWfT emptyEnv)
    (.sort [] (.imax (.succ .zero) (.succ .zero))) letProbePiTyping
  · intro c hc
    exact lrSCoreS_self_of_fundTyAt_empty letProbe_pi_fundTyAt hc
  · exact letProbe_model_pi_id (readbackLaws_whStepCK emptyEnv) (.sort .zero) (.sort .zero)

/-- A non-bottom sort is actually observed, the dependent source body
has that actual compact, and the original native let motive is proved. -/
theorem letProbe_sort_typed_nonvacuity :
    Nonempty (CtxWfT emptyEnv 0 [.letBinding letProbeSortType (.sort .zero)]) ∧
    Nonempty (HasTyT emptyEnv 0 [] (.sort .zero) letProbeSortType) ∧
    Nonempty (HasTyT emptyEnv 0 [] (letProbeValueWrap letProbeSortType (.sort .zero))
      letProbeSortType) ∧
    (.sort .zero : Expr Nat) ≠ letProbeValueWrap letProbeSortType (.sort .zero) ∧
    ApproxT emptyEnv (letProbeSourceEnv emptyEnv (.sort .zero)) (.bvar 0) .prop ∧
    RedR (WhStepCK emptyEnv) [] (letProbeValueWrap letProbeSortType (.sort .zero))
      (.sort .zero) ∧
    ConvProbeMotiveT (WhStepCK emptyEnv)
      (letProbeNativeLetConv (E := emptyEnv) (n := 0) (.sort [] (.succ .zero)) (.sort [] .zero)) := by
  refine ⟨⟨.letBinding [] letProbeSortType (.succ (.succ .zero)) (.sort .zero)
    .nil (.sort [] (.succ .zero)) (.sort [] .zero)⟩,
    ⟨.sort [] .zero⟩, ⟨letProbeValueWrapTyping (.sort [] (.succ .zero)) (.sort [] .zero)⟩,
    ?_, ?_, ?_, ?_⟩
  · intro h
    cases h
  · apply ApproxT.bvar
    simpa only [sortCode_zero] using ApproxT.sort (E := emptyEnv) EnvT.bot Level.zero
  · exact .step (.ctx (.zeta _ _ _)) (.refl _)
  · exact letProbeNativeLetConv_motive (.empty : EnvWfT emptyEnv)
      (.sort [] (.succ .zero)) (.sort [] .zero) letProbe_sort_mixedSubstEdges

/-- The Pi observation arm is also non-vacuous at actual typed model
compacts, with a well-formed observed Pi domain and a changed value. -/
theorem letProbe_pi_typed_nonvacuity :
    Nonempty (CtxWfT emptyEnv 0 [.letBinding letProbePiType letProbePiValue]) ∧
    Nonempty (HasTyT emptyEnv 0 [] letProbePiValue letProbePiType) ∧
    Nonempty (HasTyT emptyEnv 0 [] (letProbeValueWrap letProbePiType letProbePiValue)
      letProbePiType) ∧
    letProbePiValue ≠ letProbeValueWrap letProbePiType letProbePiValue ∧
    Nonempty (CtxWfT emptyEnv 0 [.assumption (.sort .zero)]) ∧
    ApproxT emptyEnv (letProbeSourceEnv emptyEnv letProbePiValue) (.bvar 0) (.pi .bot []) ∧
    RedR (WhStepCK emptyEnv) [] (letProbeValueWrap letProbePiType letProbePiValue)
      (.pi (.sort .zero) (.sort .zero)) ∧
    ConvProbeMotiveT (WhStepCK emptyEnv)
      (letProbeNativeLetConv (.sort [] (.imax (.succ .zero) (.succ .zero))) letProbePiTyping) := by
  have hA : HasTyT emptyEnv 0 [] letProbePiType
      (.sort (.succ (.imax (.succ .zero) (.succ .zero)))) :=
    .sort [] (.imax (.succ .zero) (.succ .zero))
  refine ⟨⟨.letBinding [] letProbePiType _ letProbePiValue .nil hA letProbePiTyping⟩,
    ⟨letProbePiTyping⟩, ⟨letProbeValueWrapTyping hA letProbePiTyping⟩, ?_,
    ⟨.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)⟩, ?_, ?_, ?_⟩
  · intro h
    cases h
  · exact .bvar (approxT_pi_bot_nil emptyEnv EnvT.bot (.sort .zero) (.sort .zero))
  · exact .step (.ctx (.zeta _ _ _)) (.refl _)
  · exact letProbeNativeLetConv_motive (.empty : EnvWfT emptyEnv)
      hA letProbePiTyping letProbe_pi_mixedSubstEdges

-- BEGIN RCIC_PI_PROBE_REL_SUBST_ROOTS
#print axioms bodyAtValue_of_fundConvAtT
#print axioms valueInBody_of_fundTyAtT
#print axioms mixedSubstEdges_of_fundAtT
#print axioms mixedSubstEdges_letE_of_fundamentalSAtT
#print axioms relSubstAtT_empty
#print axioms relSubstAtT_singletonLet
#print axioms convProbe_letE_of_mixedSubst_whStepCK
#print axioms convProbe_letE_of_fundAt_whStepCK
#print axioms letProbeValueWrap
#print axioms letProbe_inst_lift
#print axioms letProbeValueWrapTyping
#print axioms letProbeValueWrapZeta
#print axioms letProbeSourceEnv
#print axioms lrSCoreS_self_of_fundTyAt_empty
#print axioms letProbe_zeta_relatedSubsts
#print axioms modelProbe_bvar_at_value
#print axioms modelProbe_bvar_at_zeta_value
#print axioms mixedSubstEdges_bvar_zeta_value
#print axioms letProbe_model_sort_id
#print axioms letProbe_model_pi_id
#print axioms letProbeNativeLetConv
#print axioms letProbeNativeLetConv_motive
#print axioms letProbeSortType
#print axioms letProbePiValue
#print axioms letProbePiType
#print axioms letProbe_sort_mixedSubstEdges
#print axioms letProbe_iotaSubstT_empty
#print axioms letProbe_pi_fundTyAt
#print axioms letProbePiTyping
#print axioms letProbe_pi_mixedSubstEdges
#print axioms letProbe_sort_typed_nonvacuity
#print axioms letProbe_pi_typed_nonvacuity
-- END RCIC_PI_PROBE_REL_SUBST_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeRelSubstAudit
