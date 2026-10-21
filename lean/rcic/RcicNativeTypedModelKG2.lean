import rcic.RcicNativeTypedModelCovKGuard

/-!
# RcicNativeTypedModelKG2 — finite-chain index agreement

#7761 measured the imported `KG.KIdxAgree` at six controls: it accepts the β
gap, β under a binder, head δ and neutral η, and it rejects the apart fixture
— but it also rejects δ under a binder even though the native certificate
holds (`KG.not_kIdxAgree_deltaBinder`, `not_kgDeltaEtaCompositionAt`).  The
exact gap is the composition `indexId ~(head δ)~ .const 66 ~(η)~
deltaBinderIndex`: both single agreements hold, yet the endpoint is refuted,
because `KG.KIdxAgree` lets each side take at most one δ layer before a
terminal red/η shape.

This leaf replaces the one-layer shape by **joinability through finite
chains**: `KIdxStep` is the single witnessed step system (one readback weak-
head step, one transparent head-δ unfold, one η collapse of an explicitly
typed expansion), `KIdxChain` is its reflexive-transitive closure, and
`KIdxAgree2 a b` says both sides reach one common form in finitely many
steps.  Nothing of the landed `KG.KIdxAgree`, #7757's guards or #7761's
measurements is redefined; the earlier relation lifts (`kIdxAgree2_of_kIdxAgree`).

Results, all kernel-checked:

* **(a) all six #7761 controls, including binder δ** (`kg2_six_controls`),
  the δ-under-binder entry now positive through the explicit two-step chain
  `deltaBinderIndex ~(η)~ .const 66 ~(δ)~ indexId`.
* **(b) the composition port discharged** (`kg2DeltaEtaCompositionAt`): the
  endpoint agreement holds outright, so the #7761 obstruction
  (`not_kgDeltaEtaCompositionAt`, still true for `KG.KIdxAgree`) closes for
  chains.  Both premises of the port hold (`kg2_deltaEta_premises`).
* **(c) apart stays refuted** (`not_kIdxAgree2_apart`): the apart indices are
  distinct rigid weak-head normal forms — a Π versus a rigid family
  application — and no step of the system fires at either, so every chain
  from them is empty and no common form can exist.  Chains of these steps
  preserve rigid weak-head normal forms exactly because none of them starts
  from one.
* **(d) soundness against native conversion** (`kIdxAgree2_convT`,
  `kg2_deltaBinder_convT`, `kIndexConvAt_deltaBinder_stepDerived`): if every
  step of a chain is natively realized at one typed common form, joinability
  yields the native `ConvT` between the endpoints; at the δ∘η composition the
  two step rules alone (typed η, then `deltaIndexConv`) construct the native
  certificate and hence `KIndexConvAt` at the exact #7761 witness — the
  conjunction that was refuted for `KG.KIdxAgree` is positive here
  (`kg2_six_native_conjunction`).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit
open Rcic.Declarative.NativeValleys.TypedModelKGuardAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat} {Γ : LCtx}

/-! ## §1 — the step system and its chains -/

/-- One witnessed index step: a single weak-head step of the readback, the
transparent head-δ unfold of one constant, or the η collapse of the explicit
η-expansion of a function the environment types at a Π.  Each arm mirrors the
shape of one native conversion rule (`red` for β/ι/wh reduction, `delta` for
`ConvT.delta`, `eta` for `ConvT.eta`) without irrelevance, binder
congruence or transitivity. -/
inductive KIdxStep (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Prop
  | red {a b : Expr Nat} (h : R Γ a b) : KIdxStep E R n Γ a b
  | delta {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
      (hd : DeltaConst E r m b) :
      KIdxStep E R n Γ (.const r ls) (instantiateLevels ls b)
  | eta {A B f : Expr Nat} (hf : HasTyT E n Γ f (.pi A B)) :
      KIdxStep E R n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f

/-- The reflexive-transitive closure of the step system: a finite chain of
witnessed steps from `a` to `c`. -/
inductive KIdxChain (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Prop
  | nil (a : Expr Nat) : KIdxChain E R n Γ a a
  | cons {a b c : Expr Nat} (h : KIdxStep E R n Γ a b)
      (hs : KIdxChain E R n Γ b c) : KIdxChain E R n Γ a c

/-- **Finite-chain index agreement.**  Both sides reach one common form in
finitely many witnessed steps.  This is `KG.KIdxAgree` with the one-layer
restriction removed; the landed relation lifts into this one, and every
positive control of #7761 except δ under a binder lifts with it, while δ
under a binder becomes the explicit two-step chain η-then-δ. -/
def KIdxAgree2 (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx)
    (a b : Expr Nat) : Prop :=
  ∃ c, KIdxChain E R n Γ a c ∧ KIdxChain E R n Γ b c

/-- A whole readback reduction is a chain of single steps. -/
theorem kIdxChain_of_redR {a b : Expr Nat} (h : RedR R Γ a b) :
    KIdxChain E R n Γ a b := by
  induction h with
  | refl e => exact .nil e
  | step hs _ ih => exact .cons (.red hs) ih

/-- Chains concatenate. -/
theorem kIdxChain_trans {a b c : Expr Nat} (h₁ : KIdxChain E R n Γ a b)
    (h₂ : KIdxChain E R n Γ b c) : KIdxChain E R n Γ a c := by
  induction h₁ with
  | nil a => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

/-- Chain agreement is reflexive at every term. -/
theorem kIdxAgree2_refl (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx)
    (a : Expr Nat) : KIdxAgree2 E R n Γ a a :=
  ⟨a, .nil a, .nil a⟩

/-- The landed one-layer agreement lifts into finite-chain agreement, so no
positive control of the earlier relation is lost. -/
theorem kIdxAgree2_of_kIdxAgree {a b : Expr Nat} (h : KG.KIdxAgree E R n Γ a b) :
    KIdxAgree2 E R n Γ a b := by
  induction h with
  | red h =>
      obtain ⟨N, h₁, h₂⟩ := h
      exact ⟨N, kIdxChain_of_redR h₁, kIdxChain_of_redR h₂⟩
  | deltaL hd _ ih =>
      obtain ⟨c, hc₁, hc₂⟩ := ih
      exact ⟨c, .cons (.delta hd) hc₁, hc₂⟩
  | deltaR hd _ ih =>
      obtain ⟨c, hc₁, hc₂⟩ := ih
      exact ⟨c, hc₁, .cons (.delta hd) hc₂⟩
  | etaL hf => exact ⟨_, .nil _, .cons (.eta hf) (.nil _)⟩
  | etaR hf => exact ⟨_, .cons (.eta hf) (.nil _), .nil _⟩

/-- A term at which no step of the system fires admits only the empty chain:
chains of these steps preserve rigid weak-head normal forms by never leaving
them. -/
theorem kIdxChain_stuck {a c : Expr Nat}
    (hstuck : ∀ y, ¬ KIdxStep E R n Γ a y) (h : KIdxChain E R n Γ a c) :
    c = a := by
  induction h with
  | nil a => rfl
  | cons hstep _ _ => exact (hstuck _ hstep).elim

/-! ## §2 — the six #7761 controls at finite chains -/

/-- The β gap: both sides reach the computed index, one by reflexivity, one
by the readback's own β step. -/
theorem kIdxAgree2_eqGap (R : Readback) (n : Nat) (hL : ReadbackLaws eqEnvT R) :
    KIdxAgree2 eqEnvT R n eqGapCtx (.bvar 1)
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) :=
  kIdxAgree2_of_kIdxAgree (KG.kIdxAgree_eqGap R n hL)

/-- β under a binder: the under-binder index is the η-expansion of the
computed one. -/
theorem kIdxAgree2_binder (R : Readback) (n : Nat) :
    KIdxAgree2 eqEnvT R n binderEqCtx indexId indexBinderBeta :=
  kIdxAgree2_of_kIdxAgree (KG.kIdxAgree_binder R n)

/-- δ at the index head. -/
theorem kg2_deltaHead (R : Readback) (n : Nat) (Γ : LCtx) :
    KIdxAgree2 deltaEqEnv R n Γ indexId (.const 66 []) :=
  kIdxAgree2_of_kIdxAgree (KG.kIdxAgree_deltaHead R n Γ)

/-- The η control. -/
theorem kIdxAgree2_etaIndex (R : Readback) (n : Nat) :
    KIdxAgree2 eqEnvT R n etaEqCtx (.bvar 1) etaIndex :=
  kIdxAgree2_of_kIdxAgree (KG.kIdxAgree_etaIndex R n)

/-- The checked constant agrees with its η expansion by one collapse step. -/
theorem kg2_deltaConst_eta (R : Readback) (n : Nat) (Γ : LCtx) :
    KIdxAgree2 deltaEqEnv R n Γ (.const 66 []) deltaBinderIndex :=
  ⟨.const 66 [], .nil _, .cons (.eta (deltaConstTy n Γ)) (.nil _)⟩

/-- **δ under a binder, the #7761 gap, now positive**: the actual index is
the typed η-expansion of the checked constant, and the constant δ-unfolds to
the computed index, so the two-step chain `deltaBinderIndex ~(η)~
.const 66 ~(δ)~ indexId` meets the empty chain at `indexId`. -/
theorem kIdxAgree2_deltaBinder (R : Readback) (n : Nat) (Γ : LCtx) :
    KIdxAgree2 deltaEqEnv R n Γ indexId deltaBinderIndex :=
  ⟨indexId, .nil _,
    .cons (.eta (deltaConstTy n Γ))
      (.cons (.delta (r := 66) (m := deltaEqMember) (b := indexId)
        (show DeltaConst deltaEqEnv 66 deltaEqMember indexId from
          ⟨rfl, rfl, by decide, by decide⟩))
        (.nil _))⟩

/-- The first apart index is a rigid weak-head normal form: a Π that no
readback with laws steps from, and no δ or η pattern matches. -/
theorem kIdxStep_idPiProp_false (n : Nat) (y : Expr Nat) :
    ¬ KIdxStep eqEnvT (WhStepCK2 eqEnvT n) n apartCtx idPiProp y := by
  have hL := readbackLaws_whStepCK2 eqEnvT n
  intro hs
  have hs' : KIdxStep eqEnvT (WhStepCK2 eqEnvT n) n apartCtx
      (.pi (.sort .zero) (.bvar 0)) y := hs
  cases hs' with
  | red h => exact hL.pi_normal apartCtx (.sort .zero) (.bvar 0) y h

/-- The second apart index is a rigid weak-head normal form: a saturated
application of the admitted Eq family that no readback with laws steps from,
and neither δ nor η matches an application head. -/
theorem kIdxStep_apartRight_false (n : Nat) (y : Expr Nat) :
    ¬ KIdxStep eqEnvT (WhStepCK2 eqEnvT n) n apartCtx apartRight y := by
  have hL := readbackLaws_whStepCK2 eqEnvT n
  intro hs
  have hs' : KIdxStep eqEnvT (WhStepCK2 eqEnvT n) n apartCtx
      (foldApps (.const 63 []) [.sort .zero, idPiProp, idPiProp]) y := hs
  cases hs' with
  | red h =>
      exact hL.famApp_normal pinEqGroupWfT apartCtx (r := 63) (m := eqFamT)
        rfl rfl [] [.sort .zero, idPiProp, idPiProp] y h

/-- **The apart fixture stays refuted for chains.**  Both apart indices are
distinct rigid weak-head normal forms — a Π versus a rigid family
application — and no step of the system fires at either, so both chains are
empty and the alleged common form would make the two indices equal. -/
theorem not_kIdxAgree2_apart (n : Nat) :
    ¬ KIdxAgree2 eqEnvT (WhStepCK2 eqEnvT n) n apartCtx idPiProp apartRight := by
  rintro ⟨c, hc₁, hc₂⟩
  have h₁ : c = idPiProp := kIdxChain_stuck (kIdxStep_idPiProp_false n) hc₁
  have h₂ : c = apartRight := kIdxChain_stuck (kIdxStep_apartRight_false n) hc₂
  have h : idPiProp = apartRight := h₁.symm.trans h₂
  rw [show idPiProp = Expr.pi (.sort .zero) (.bvar 0) from rfl,
    KG.apartRight_eq] at h
  simp only [foldApps] at h
  exact Expr.noConfusion h

/-- **All six #7761 controls for finite chains**, in the order apart, index
β, β under a binder, head δ, δ under a binder, and η.  Against
`KG.kg_six_agreement_controls`, only the δ-under-a-binder entry changes
sign: it is now positive. -/
theorem kg2_six_controls (n : Nat) :
    (¬ KIdxAgree2 eqEnvT (WhStepCK2 eqEnvT n) n
        apartCtx idPiProp apartRight) ∧
    KIdxAgree2 eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx (.bvar 1)
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) ∧
    KIdxAgree2 eqEnvT (WhStepCK2 eqEnvT n) n
      binderEqCtx indexId indexBinderBeta ∧
    KIdxAgree2 deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaHeadEqCtx indexId (.const 66 []) ∧
    KIdxAgree2 deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaUnderBinderEqCtx indexId deltaBinderIndex ∧
    KIdxAgree2 eqEnvT (WhStepCK2 eqEnvT n) n
      etaEqCtx (.bvar 1) etaIndex :=
  ⟨not_kIdxAgree2_apart n,
    kIdxAgree2_eqGap (WhStepCK2 eqEnvT n) n (readbackLaws_whStepCK2 eqEnvT n),
    kIdxAgree2_binder (WhStepCK2 eqEnvT n) n,
    kg2_deltaHead (WhStepCK2 deltaEqEnv n) n deltaHeadEqCtx,
    kIdxAgree2_deltaBinder (WhStepCK2 deltaEqEnv n) n deltaUnderBinderEqCtx,
    kIdxAgree2_etaIndex (WhStepCK2 eqEnvT n) n⟩

/-! ## §3 — the composition port -/

/-- The #7761 composition instance, restated for finite chains: head δ from
`indexId` to the constant, then η of that constant, closes to the endpoint
agreement. -/
def KG2DeltaEtaCompositionAt (n : Nat) : Prop :=
  KIdxAgree2 deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaUnderBinderEqCtx indexId (.const 66 []) →
  KIdxAgree2 deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaUnderBinderEqCtx (.const 66 []) deltaBinderIndex →
  KIdxAgree2 deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaUnderBinderEqCtx indexId deltaBinderIndex

/-- Both premises of the composition port hold at the δ-under-binder
fixture: the two witness steps of #7761 lift to chains. -/
theorem kg2_deltaEta_premises (n : Nat) :
    KIdxAgree2 deltaEqEnv (WhStepCK2 deltaEqEnv n) n
        deltaUnderBinderEqCtx indexId (.const 66 []) ∧
    KIdxAgree2 deltaEqEnv (WhStepCK2 deltaEqEnv n) n
      deltaUnderBinderEqCtx (.const 66 []) deltaBinderIndex :=
  ⟨kg2_deltaHead (WhStepCK2 deltaEqEnv n) n deltaUnderBinderEqCtx,
    kg2_deltaConst_eta (WhStepCK2 deltaEqEnv n) n deltaUnderBinderEqCtx⟩

/-- **The composition port is discharged.**  The #7761 obstruction refuted
the endpoint for the one-layer relation; for chains the endpoint holds
outright (`kIdxAgree2_deltaBinder`), so the port closes without consuming its
premises — the strongest possible repair at this fixture.  No general
transitivity of joinability is claimed: that would be confluence of the step
system, which is neither needed nor proved here. -/
theorem kg2DeltaEtaCompositionAt (n : Nat) : KG2DeltaEtaCompositionAt n :=
  fun _ _ => kIdxAgree2_deltaBinder (WhStepCK2 deltaEqEnv n) n
    deltaUnderBinderEqCtx

/-! ## §4 — soundness against native conversion -/

/-- If every step of a chain is natively realized at one typed common form,
the chain is one native conversion, and the endpoint keeps the typing. -/
theorem kIdxChain_convT {A : Expr Nat}
    (hS : ∀ x y, KIdxStep E R n Γ x y →
      Nonempty (ConvT E n Γ x y A) ∧ Nonempty (HasTyT E n Γ x A) ∧
        Nonempty (HasTyT E n Γ y A))
    {a c : Expr Nat} (hTa : Nonempty (HasTyT E n Γ a A))
    (h : KIdxChain E R n Γ a c) :
    Nonempty (ConvT E n Γ a c A) ∧ Nonempty (HasTyT E n Γ c A) := by
  induction h with
  | nil =>
      obtain ⟨hTa⟩ := hTa
      exact ⟨⟨.refl Γ _ A hTa⟩, ⟨hTa⟩⟩
  | cons hstep _ ih =>
      obtain ⟨⟨hxab⟩, _, ⟨hyb⟩⟩ := hS _ _ hstep
      obtain ⟨⟨hbc⟩, hyc⟩ := ih ⟨hyb⟩
      exact ⟨⟨.trans Γ _ _ _ A hxab hbc⟩, hyc⟩

/-- **Joinability is natively sound** whenever each of its steps is: two
chains to a common form compose, with one reversal, into one native
conversion between the typed endpoints. -/
theorem kIdxAgree2_convT {A : Expr Nat}
    (hS : ∀ x y, KIdxStep E R n Γ x y →
      Nonempty (ConvT E n Γ x y A) ∧ Nonempty (HasTyT E n Γ x A) ∧
        Nonempty (HasTyT E n Γ y A))
    {a b : Expr Nat} (hTa : Nonempty (HasTyT E n Γ a A))
    (hTb : Nonempty (HasTyT E n Γ b A))
    (h : KIdxAgree2 E R n Γ a b) : Nonempty (ConvT E n Γ a b A) := by
  obtain ⟨c, h₁, h₂⟩ := h
  obtain ⟨⟨hac⟩, _⟩ := kIdxChain_convT hS hTa h₁
  obtain ⟨⟨hbc⟩, _⟩ := kIdxChain_convT hS hTb h₂
  exact ⟨.trans Γ a c b A hac (.symm Γ b c A hbc)⟩

/-- The native conversion at the δ∘η composition, built from the two step
rules alone: typed η collapses the expansion to the checked constant, and
the imported `deltaIndexConv` unfolds the constant to the computed index.
No readback step is consumed, so the certificate is readback-independent. -/
theorem kg2_deltaBinder_convT (n : Nat) (Γ : LCtx) :
    Nonempty (ConvT deltaEqEnv n Γ deltaBinderIndex indexId indexFn) :=
  ⟨.trans Γ deltaBinderIndex (.const 66 []) indexId indexFn
    (.eta Γ (.const 66 []) (.sort .zero) (.sort .zero) (deltaConstTy n Γ))
    (deltaIndexConv n Γ)⟩

/-- The step-derived conversion pays the exact native `KIndexConvAt`
certificate at the #7761 δ-under-binder witness — the conjunct that was
refuted for the one-layer relation (`KG.not_kIdxAgree_deltaBinder`). -/
theorem kIndexConvAt_deltaBinder_stepDerived (n : Nat) :
    KIndexConvAt deltaEqEnv n deltaUnderBinderEqCtx
      (eqConvW deltaEqExtends indexFn indexId deltaBinderIndex
        binderIndexMot (.sort .zero)) := by
  obtain ⟨hci⟩ := kg2_deltaBinder_convT n deltaUnderBinderEqCtx
  exact (eqKGate_of_indexConv deltaEqExtends binderIndexMot (.sort .zero)
    (indexFnTy deltaEqEnv n deltaUnderBinderEqCtx)
    (indexIdTy deltaEqEnv n deltaUnderBinderEqCtx)
    (deltaBinderTy n deltaUnderBinderEqCtx)
    (.bvar deltaUnderBinderEqCtx 0 _ rfl) hci).1

/-- The six measurements after adjoining the native index certificate at
each exact legacy witness, mirroring `kg_six_native_conjunction_controls`
with the chain relation.  The δ-under-binder conjunction is now positive:
the native certificate is derived from the step rules themselves. -/
theorem kg2_six_native_conjunction (n : Nat) :
    (¬ (KIndexConvAt eqEnvT n apartCtx
          (eqConvW (fun _ _ h => h) (.sort .zero) idPiProp apartRight
            apartMot (.sort .zero)) ∧
        KIdxAgree2 eqEnvT (WhStepCK2 eqEnvT n) n
          apartCtx idPiProp apartRight)) ∧
    (KIndexConvAt eqEnvT n eqGapCtx eqGapW ∧
      KIdxAgree2 eqEnvT (WhStepCK2 eqEnvT n) n eqGapCtx (.bvar 1)
        (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1))) ∧
    (KIndexConvAt eqEnvT n binderEqCtx
        (eqConvW (fun _ _ h => h) indexFn indexId indexBinderBeta
          binderIndexMot (.sort .zero)) ∧
      KIdxAgree2 eqEnvT (WhStepCK2 eqEnvT n) n
        binderEqCtx indexId indexBinderBeta) ∧
    (KIndexConvAt deltaEqEnv n deltaHeadEqCtx
        (eqConvW deltaEqExtends indexFn indexId (.const 66 [])
          binderIndexMot (.sort .zero)) ∧
      KIdxAgree2 deltaEqEnv (WhStepCK2 deltaEqEnv n) n
        deltaHeadEqCtx indexId (.const 66 [])) ∧
    (KIndexConvAt deltaEqEnv n deltaUnderBinderEqCtx
        (eqConvW deltaEqExtends indexFn indexId deltaBinderIndex
          binderIndexMot (.sort .zero)) ∧
      KIdxAgree2 deltaEqEnv (WhStepCK2 deltaEqEnv n) n
        deltaUnderBinderEqCtx indexId deltaBinderIndex) ∧
    (KIndexConvAt eqEnvT n etaEqCtx
        (eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex
          etaIndexMot (.sort .zero)) ∧
      KIdxAgree2 eqEnvT (WhStepCK2 eqEnvT n) n
        etaEqCtx (.bvar 1) etaIndex) := by
  obtain ⟨ha, hg, hb, hd, hdb, he⟩ := kg2_six_controls n
  refine ⟨(fun h => ha h.2), ⟨(kIndexGuardAt_eqGap n).1, hg⟩,
    ⟨(kIndexGuardAt_binder n).1, hb⟩, ⟨(kIndexGuardAt_delta n).1, hd⟩,
    ⟨kIndexConvAt_deltaBinder_stepDerived n, hdb⟩, ?_⟩
  exact ⟨(eqKGate_of_indexConv (fun _ _ h => h) etaIndexMot (.sort .zero)
    (indexFnTy eqEnvT n etaEqCtx) (etaIndexParamTy n) (etaIndexTy n)
    (.bvar etaEqCtx 0 _ rfl) (etaIndexConv n)).1, he⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_KG2_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxStep
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxStep.red
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxStep.delta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxStep.eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxChain
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxChain.nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxChain.cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KIdxAgree2
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxChain_of_redR
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxChain_trans
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_refl
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_of_kIdxAgree
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxChain_stuck
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_eqGap
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_binder
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_deltaHead
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_etaIndex
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_deltaConst_eta
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_deltaBinder
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxStep_idPiProp_false
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxStep_apartRight_false
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.not_kIdxAgree2_apart
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_six_controls
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.KG2DeltaEtaCompositionAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_deltaEta_premises
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2DeltaEtaCompositionAt
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxChain_convT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIdxAgree2_convT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_deltaBinder_convT
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kIndexConvAt_deltaBinder_stepDerived
#print axioms Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2.kg2_six_native_conjunction
-- END RCIC_NATIVE_TYPED_MODEL_KG2_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKAudit.KG2
