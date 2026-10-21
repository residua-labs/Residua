import rcic.RcicNativeReadbackCK

/-!
# Native common-type K heads for the new CK2 readback

This file composes the existing projection canon and its uniqueness lemmas.
The common type is the recursor-side major family, and the canonical constructor
is `ctorMajorRec`: the unconstrained constructor-side fields of an `IotaWitness`
are not an eligibility test.  The gate is uniform in every resolved environment.

These are head rules and their compatibility facts.  Whole-core determinism,
readback laws and model compatibility are separate obligations.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- The family application in the instantiated recursor's major domain. -/
def majorFamily (w : IotaWitness E) : Expr Nat :=
  foldApps (.const w.familyRef (famLevels w))
    (w.preMajor.take w.nparams ++ redexIdx w)

/-- The same family applied to the constructor's computed result indices.
All inputs are fixed by the recursor side and the deterministic canon fields. -/
def computedFamily (w : IotaWitness E) : Expr Nat :=
  foldApps (.const w.familyRef (famLevels w))
    (w.preMajor.take w.nparams ++
      resultIdxAt w (w.preMajor.take w.nparams) w.fields)

/-- The explicit native index-alignment certificate.  Keeping this certificate
separate from common typing makes the computed-index check observable in the
native conversion relation instead of hiding it inside a typing derivation. -/
def KIndexConvAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (w : IotaWitness E) : Prop :=
  Nonempty (ConvT E n Γ (computedFamily w) (majorFamily w) (.sort .zero))

/-- Native typing puts the actual major and the recursor-side canon at one
proposition.  In particular, the canon's computed indices may agree through
native conversion rather than syntactic equality. -/
def KCommonAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (w : IotaWitness E) (x : Expr Nat) : Prop :=
  Nonempty (HasTyT E n Γ (majorFamily w) (.sort .zero)) ∧
  Nonempty (HasTyT E n Γ x (majorFamily w)) ∧
  Nonempty (HasTyT E n Γ (ctorMajorRec w) (majorFamily w))

/-- The common-type certificate supplies precisely the native irrelevance
conversion between the actual major and the deterministic canon. -/
theorem kCommonAt_irr {w : IotaWitness E} {x : Expr Nat}
    (h : KCommonAt E n Γ w x) :
    Nonempty (ConvT E n Γ x (ctorMajorRec w) (majorFamily w)) := by
  obtain ⟨⟨hP⟩, ⟨hx⟩, ⟨hc⟩⟩ := h
  exact ⟨.irr Γ (majorFamily w) x (ctorMajorRec w) hP hx hc⟩

/-- A constructor already typed at a convertible proposition satisfies the
gate by native type conversion.  This interface does not assume injectivity. -/
theorem kCommonAt_of_conv {w : IotaWitness E} {x P : Expr Nat}
    (hP : HasTyT E n Γ (majorFamily w) (.sort .zero))
    (hx : HasTyT E n Γ x (majorFamily w))
    (hc : HasTyT E n Γ (ctorMajorRec w) P)
    (hconv : ConvT E n Γ P (majorFamily w) (.sort .zero)) :
    KCommonAt E n Γ w x :=
  ⟨⟨hP⟩, ⟨hx⟩, ⟨.conv _ _ _ _ _ hc hconv⟩⟩

/-- Exactly the two existing choices of a deterministic K canon. -/
def KCanonW (w : IotaWitness E) (x : Expr Nat) : Prop :=
  KFreeW w ∨ (KFieldW w ∧ w.fields = projFields w x)

/-- The old canon uniqueness lemmas combine without inspecting any index gate. -/
theorem iotaRhsOf_kcanon_eq {w₁ w₂ : IotaWitness E} {x : Expr Nat}
    (h₁ : KCanonW w₁ x) (h₂ : KCanonW w₂ x)
    (hr : w₁.recRef = w₂.recRef) (hls : w₁.ls = w₂.ls)
    (hp : w₁.preMajor = w₂.preMajor) :
    iotaRhsOf w₁ = iotaRhsOf w₂ := by
  rcases h₁ with h₁ | ⟨h₁, hf₁⟩
  · rcases h₂ with h₂ | ⟨h₂, _⟩
    · exact iotaRhsOf_kfree_eq h₁ h₂ hr hp
    · have hlen := fields_length_eq_of_same_lhs h₂.2.1 h₁.2.1 hr.symm hp.symm
      rw [h₁.1] at hlen
      exact (h₂.1 (List.length_eq_zero.mp hlen)).elim
  · rcases h₂ with h₂ | ⟨h₂, hf₂⟩
    · have hlen := fields_length_eq_of_same_lhs h₁.2.1 h₂.2.1 hr hp
      rw [h₂.1] at hlen
      exact (h₁.1 (List.length_eq_zero.mp hlen)).elim
    · exact iotaRhsOf_kfield_eq h₁ h₂ hr hls hp hf₁ hf₂

/-- For a singleton recursor, even distinct pre-major spines have the same
field count.  The recursor member fixes their lengths, which is the only
spine information required by the existing witness-environment lemma. -/
theorem fields_length_eq_of_same_rec {w₁ w₂ : IotaWitness E}
    (hnm₁ : w₁.nMinors = 1) (hnm₂ : w₂.nMinors = 1)
    (hr : w₁.recRef = w₂.recRef) : w₁.fields.length = w₂.fields.length := by
  have hci₁ : w₁.ctorIdx = 0 := by have h := w₁.hidx; omega
  have hci₂ : w₂.ctorIdx = 0 := by have h := w₂.hidx; omega
  have hcr : w₁.ctorRef = w₂.ctorRef := by
    have h₁ := w₁.hctorIdx; have h₂ := w₂.hctorIdx
    have h₃ := w₁.hrecIdx; have h₄ := w₂.hrecIdx
    omega
  have hrm : w₁.recMember = w₂.recMember :=
    Option.some.inj (by rw [← w₁.hrec, ← w₂.hrec, hr])
  have hlen : w₁.preMajor.length = w₂.preMajor.length := by
    have h₁ := w₁.hpre; have h₂ := w₂.hpre
    have h₃ := w₁.hnmin; have h₄ := w₂.hnmin
    rw [hrm] at h₃
    omega
  obtain ⟨_, hcm, _, _, _, hnp, _, _⟩ := iotaWitness_env_of_same_refs hr hcr hlen
  have h₁ := w₁.hnpar; have h₂ := w₂.hnpar
  rw [hcm, hnp] at h₁
  omega

/-- A fieldful K witness cannot impersonate a field-free K recursor, even at
a different spine.  This is independent of native index convertibility. -/
theorem kFreeRec_not_kProjRec {r : Nat} (h : KFreeRec E r) : ¬ KProjRec E r := by
  obtain ⟨w₁, hr₁, h₁⟩ := h
  rintro ⟨w₂, hr₂, h₂⟩
  have hlen := fields_length_eq_of_same_rec h₂.2.1 h₁.2.1 (hr₂.trans hr₁.symm)
  rw [h₁.1] at hlen
  exact h₂.1 (List.length_eq_zero.mp hlen)

/-- In the admitted Eq environment, no fieldful K witness exists at Eq.rec.
Thus a distinct-index Eq normality audit has only the native common-type
gate to exclude; it has no hidden projection-K alternative. -/
theorem not_kProjRec_eqEnv : ¬ KProjRec eqEnvT 65 :=
  kFreeRec_not_kProjRec ⟨eqGapW, rfl, ⟨rfl, rfl, rfl⟩⟩

/-- The native K addition, before contextual closure. -/
inductive KNativeHead (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Prop
  | intro {w : IotaWitness E} {x : Expr Nat}
      (hK : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
      (hindex : KIndexConvAt E n Γ w)
      (hcommon : KCommonAt E n Γ w x) :
      KNativeHead E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w)

theorem KNativeHead.kStar {w : IotaWitness E} {x : Expr Nat}
    (hK : KFreeW w) (hnc : ¬ IsCtorSpine E x)
    (hi : KIndexConvAt E n Γ w)
    (hc : KCommonAt E n Γ w x) :
    KNativeHead E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) :=
  .intro (.inl hK) hnc hi hc

theorem KNativeHead.kProj {w : IotaWitness E} {x : Expr Nat}
    (hK : KFieldW w) (hnc : ¬ IsCtorSpine E x)
    (hf : w.fields = projFields w x) (hi : KIndexConvAt E n Γ w)
    (hc : KCommonAt E n Γ w x) :
    KNativeHead E n Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) :=
  .intro (.inr ⟨hK, hf⟩) hnc hi hc

/-- Native common-type K is deterministic on raw sources, with no environment
well-formedness or typing-uniqueness assumption. -/
theorem detR_kNativeHead (E : ResolvedEnv) (n : Nat) : DetR (KNativeHead E n) := by
  intro Γ a b c h₁ h₂
  cases h₁ with
  | intro hK₁ hnc₁ hi₁ hc₁ =>
      rename_i w₁ x₁
      generalize ha : recCall (.const w₁.recRef w₁.ls) w₁.preMajor x₁ = a₀ at h₂
      cases h₂ with
      | intro hK₂ hnc₂ hi₂ hc₂ =>
          simp only [recCall_eq_app] at ha
          injection ha with hf hx
          obtain ⟨hconst, hp⟩ := foldApps_const_inj hf
          injection hconst with hr hls
          subst hx
          exact iotaRhsOf_kcanon_eq hK₁ hK₂ hr hls hp

/-- A native K head and any old CK step at the same source have the same
contractum.  The proof invokes CK's exclusion lemmas and canon uniqueness;
it does not rebuild the old core's determinism argument. -/
theorem kNativeHead_ck_det (hW : EnvWfT E) {a b c : Expr Nat}
    (h₁ : KNativeHead E n Γ a b) (h₂ : WhStepCK E Γ a c) : b = c := by
  cases h₁ with
  | intro hK hnc hi hc =>
      rename_i w x
      generalize ha : recCall (.const w.recRef w.ls) w.preMajor x = a₀ at h₂
      induction h₂ with
      | ctx hs =>
          exact (whStepCtx_recCall_nonCtorMajor_aux hW (ha.symm ▸ hs) rfl hnc).elim
      | kStar hK' hnc' hidx' =>
          simp only [recCall_eq_app] at ha
          injection ha with hf hx
          obtain ⟨hconst, hp⟩ := foldApps_const_inj hf
          injection hconst with hr hls
          subst hx
          exact iotaRhsOf_kcanon_eq hK (.inl hK') hr hls hp
      | kProj hK' hnc' hf' hidx' =>
          simp only [recCall_eq_app] at ha
          injection ha with hf hx
          obtain ⟨hconst, hp⟩ := foldApps_const_inj hf
          injection hconst with hr hls
          subst hx
          exact iotaRhsOf_kcanon_eq hK (.inr ⟨hK', hf'⟩) hr hls hp
      | recMajor hm' hrec' hlen' hnK' hnP' hs' =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          obtain ⟨hconst, _⟩ := foldApps_const_inj hf
          injection hconst with hr _
          rcases hK with hK | ⟨hK, _⟩
          · exact (hnK' ⟨w, hr, hK⟩).elim
          · exact (hnP' ⟨w, hr, hK⟩).elim
      | appHead hs =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          subst hf
          exact (whStepCK_recPrefix_false_aux hW w.hrec w.hrecK hs rfl
            (by have h₁ := w.hpre; have h₂ := w.hnmin; omega)).elim

/-- The old Eq gap has an explicit native conversion from the constructor's
computed-index family to the recursor's actual-index family. -/
theorem kIndexConvAt_eqGap (n : Nat) :
    KIndexConvAt eqEnvT n eqGapCtx eqGapW := by
  have hα : HasTyT eqEnvT n eqGapCtx (.bvar 2) (.sort (.succ .zero)) :=
    .bvar eqGapCtx 2 _ rfl
  have ha : HasTyT eqEnvT n eqGapCtx (.bvar 1) (.bvar 2) :=
    .bvar eqGapCtx 1 _ rfl
  have cIdx : ConvT eqEnvT n eqGapCtx
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) (.bvar 1) (.bvar 2) :=
    .beta _ _ _ _ _ _ hα
      (.bvar (.assumption (.bvar 2) :: eqGapCtx) 0 _ rfl) ha
  refine ⟨?_⟩
  change ConvT eqEnvT n eqGapCtx
    (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1])
    (majorFamily eqGapW) (.sort .zero)
  refine .app _ _ _ _ _ _ _
    (.app _ _ _ _ _ _ _ (.app _ _ _ _ _ _ _
      (.refl _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl)) (.refl _ _ _ hα))
      (.refl _ _ _ ha)) ?_
  exact .symm _ _ _ _ cIdx

/-- The precise old Eq gap meets the new native gate, through beta conversion
of its index and native conversion of the canonical constructor's type. -/
theorem kCommonAt_eqGap (n : Nat) :
    KCommonAt eqEnvT n eqGapCtx eqGapW (.bvar 0) := by
  have hα : HasTyT eqEnvT n eqGapCtx (.bvar 2) (.sort (.succ .zero)) :=
    .bvar eqGapCtx 2 _ rfl
  have ha : HasTyT eqEnvT n eqGapCtx (.bvar 1) (.bvar 2) :=
    .bvar eqGapCtx 1 _ rfl
  have hx : HasTyT eqEnvT n eqGapCtx (.bvar 0) (majorFamily eqGapW) :=
    .bvar eqGapCtx 0 _ rfl
  have tIdx : HasTyT eqEnvT n eqGapCtx
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) (.bvar 2) :=
    .app _ _ _ _ _ (.lam _ _ _ _ _ hα
      (.bvar (.assumption (.bvar 2) :: eqGapCtx) 0 _ rfl)) ha
  have hP : HasTyT eqEnvT n eqGapCtx (majorFamily eqGapW) (.sort .zero) :=
    .app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _
      (.const _ 63 [] eqFamT rfl rfl rfl) hα) ha) tIdx
  have hc : HasTyT eqEnvT n eqGapCtx (ctorMajorRec eqGapW)
      (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1]) :=
    .app _ _ _ _ _ (.app _ _ _ _ _
      (.const _ 64 [] eqReflT rfl rfl rfl) hα) ha
  obtain ⟨cP⟩ := kIndexConvAt_eqGap n
  exact kCommonAt_of_conv hP hx hc cP

/-- The repair applies at the entire old Eq-gap redex. -/
theorem kNativeHead_eqGap (n : Nat) :
    KNativeHead eqEnvT n eqGapCtx eqGapRedex (.sort .zero) :=
  .kStar (w := eqGapW) ⟨rfl, rfl, rfl⟩ not_isCtorSpine_bvar
    (kIndexConvAt_eqGap n) (kCommonAt_eqGap n)

/-! ## Uniform typed Eq controls -/

/-- A read-only extension of the exact admitted Eq environment. -/
def ExtendsEqEnv (E : ResolvedEnv) : Prop :=
  ∀ r m, eqEnvT.members r = some m → E.members r = some m

/-- Reuse the checked Eq witness while changing only the redex data.  The
existing replacement constructor supplies all stored-type telescope proofs.
The constructor-side parameters are explicitly updated to the chosen ones. -/
def eqConvW (hE : ExtendsEqEnv E) (A a b mot minor : Expr Nat) : IotaWitness E :=
  let w := F8EtaK.replacePreMajorWitness (extWitness hE eqGapW)
    [.succ (.succ .zero)] [A, a, mot, minor, b] minor
    (eqNList_refl _) rfl rfl
  { w with ctorParams := [A, a], hctorParams := rfl }

/-- Eq's constructor telescope computes its repeated parameter as the sole
result index.  The cancellation is the existing substitution/lift law. -/
theorem eqRefl_applyTel (A a : Expr Nat) :
    applyTel [A, a] (instantiateLevels [.succ (.succ .zero)] eqReflT.mtype) =
      some (foldApps (.const 63 []) [A, a, a]) := by
  change some (foldApps (.const 63 []) [instantiate0 a (lift 0 1 A), a, a]) = _
  rw [show instantiate0 a (lift 0 1 A) = A from instantiate_lift_id 0 a A]

/-- The explicit computed family of the generic Eq witness. -/
theorem eqConvW_computedFamily (hE : ExtendsEqEnv E) (A a b mot minor : Expr Nat) :
    computedFamily (eqConvW hE A a b mot minor) =
      foldApps (.const 63 []) [A, a, a] := by
  change foldApps (.const 63 [])
    ([A, a] ++ ((appsSpine
      ((applyTel [A, a] (instantiateLevels [.succ (.succ .zero)] eqReflT.mtype)).getD
        (.sort .zero))).2.drop 2)) = _
  rw [eqRefl_applyTel]
  rfl

/-- Every canonical K witness at this Eq source has the same actual and
computed families.  This removes the arbitrary witness from a native-gate
normality audit; constructor-side parameters and universe arguments do not
enter either family. -/
theorem eqKCanon_families {w : IotaWitness eqEnvT} {x A a b mot minor : Expr Nat}
    (hr : w.recRef = 65) (hp : w.preMajor = [A, a, mot, minor, b])
    (hK : KCanonW w x) :
    computedFamily w = foldApps (.const 63 []) [A, a, a] ∧
    majorFamily w = foldApps (.const 63 []) [A, a, b] := by
  have hnm : w.nMinors = 1 := by
    rcases hK with hK | ⟨hK, _⟩
    · exact hK.2.1
    · exact hK.2.1
  have hci : w.ctorIdx = 0 := by have h := w.hidx; omega
  have hcr : w.ctorRef = eqGapW.ctorRef := by
    have h₁ := w.hrecIdx; have h₂ := w.hctorIdx
    change w.ctorRef = 64
    omega
  have hlen : w.preMajor.length = eqGapW.preMajor.length := by rw [hp]; rfl
  obtain ⟨_, hcm, hfr, _, _, hnp, _, _⟩ :=
    iotaWitness_env_of_same_refs (w1 := w) (w2 := eqGapW) hr hcr hlen
  have hfr' : w.familyRef = 63 := hfr
  have hcm' : w.ctorMember = eqReflT := hcm
  have hnp' : w.nparams = 2 := hnp
  have hfm : w.famMember = eqFamT := by
    have h := w.hfam
    rw [hfr'] at h
    exact (Option.some.inj h).symm
  have hfields : w.fields = [] := by
    apply List.length_eq_zero.mp
    have h := w.hnpar
    rw [hcm', hnp'] at h
    change 2 + w.fields.length = 2 at h
    omega
  constructor
  · unfold computedFamily famLevels resultIdxAt applyTelOr
    rw [hfr', hfm, hnp', hp, hfields, hcm']
    change foldApps (.const 63 [])
      ([A, a] ++ ((appsSpine
        ((applyTel [A, a] (instantiateLevels w.ls eqReflT.mtype)).getD
          (.sort .zero))).2.drop 2)) = _
    have hcalc := eqRefl_applyTel A a
    change applyTel [A, a] (instantiateLevels w.ls eqReflT.mtype) =
      some (foldApps (.const 63 []) [A, a, a]) at hcalc
    rw [hcalc]
    rfl
  · unfold majorFamily famLevels redexIdx
    rw [hfr', hfm, hnp', hp, hnm]
    rfl

/-- Partial native Eq application after its type and first term parameter. -/
def eqFamilyPartialTy (hE : ExtendsEqEnv E) {A a : Expr Nat}
    (hA : HasTyT E n Γ A (.sort (.succ .zero))) (ha : HasTyT E n Γ a A) :
    HasTyT E n Γ (foldApps (.const 63 []) [A, a]) (.pi A (.sort .zero)) := by
  have h₁ : HasTyT E n Γ (.app (.const 63 []) A)
      (.pi A (.pi (lift 0 1 A) (.sort .zero))) :=
    .app _ _ _ _ _ (.const _ 63 [] eqFamT (hE 63 eqFamT rfl) rfl rfl) hA
  have h₂ := HasTyT.app Γ (.app (.const 63 []) A) a A
    (.pi (lift 0 1 A) (.sort .zero)) h₁ ha
  change HasTyT E n Γ (foldApps (.const 63 []) [A, a])
    (.pi (instantiate0 a (lift 0 1 A)) (.sort .zero)) at h₂
  simpa only [instantiate0, instantiate_lift_id] using h₂

/-- Native typing of the generic recursor-side Eq canon. -/
def eqReflApplyTy (hE : ExtendsEqEnv E) {A a : Expr Nat}
    (hA : HasTyT E n Γ A (.sort (.succ .zero))) (ha : HasTyT E n Γ a A) :
    HasTyT E n Γ (foldApps (.const 64 []) [A, a])
      (foldApps (.const 63 []) [A, a, a]) := by
  have h₁ : HasTyT E n Γ (.app (.const 64 []) A)
      (.pi A (foldApps (.const 63 []) [lift 0 1 A, .bvar 0, .bvar 0])) :=
    .app _ _ _ _ _ (.const _ 64 [] eqReflT (hE 64 eqReflT rfl) rfl rfl) hA
  have h₂ := HasTyT.app Γ (.app (.const 64 []) A) a A
    (foldApps (.const 63 []) [lift 0 1 A, .bvar 0, .bvar 0]) h₁ ha
  change HasTyT E n Γ (foldApps (.const 64 []) [A, a])
    (foldApps (.const 63 []) [instantiate0 a (lift 0 1 A), a, a]) at h₂
  simpa only [instantiate0, instantiate_lift_id] using h₂

/-- Any native conversion of the actual Eq index to the computed one pays
both explicit CK2 K gates.  This includes beta, delta, binder congruence and
eta without adding any syntax-specific eligibility arm. -/
theorem eqKGate_of_indexConv (hE : ExtendsEqEnv E) (mot minor : Expr Nat)
    {A a b x : Expr Nat}
    (hA : HasTyT E n Γ A (.sort (.succ .zero)))
    (ha : HasTyT E n Γ a A) (hb : HasTyT E n Γ b A)
    (hx : HasTyT E n Γ x (foldApps (.const 63 []) [A, a, b]))
    (ci : ConvT E n Γ b a A) :
    KIndexConvAt E n Γ (eqConvW hE A a b mot minor) ∧
    KCommonAt E n Γ (eqConvW hE A a b mot minor) x := by
  have hf := eqFamilyPartialTy hE hA ha
  have hp : HasTyT E n Γ (foldApps (.const 63 []) [A, a, b]) (.sort .zero) :=
    .app _ _ _ _ _ hf hb
  have hc := eqReflApplyTy hE hA ha
  have cp : ConvT E n Γ (foldApps (.const 63 []) [A, a, a])
      (foldApps (.const 63 []) [A, a, b]) (.sort .zero) :=
    .app _ _ _ _ _ _ _ (.refl _ _ _ hf) (.symm _ _ _ _ ci)
  refine ⟨?_, ?_⟩
  · unfold KIndexConvAt
    rw [eqConvW_computedFamily]
    exact ⟨cp⟩
  · exact kCommonAt_of_conv hp hx hc cp

/-- A complete native K head control from an arbitrary typed index
conversion, uniform in the motive, minor, context and admitted extension. -/
theorem kNativeHead_eq_of_indexConv (hE : ExtendsEqEnv E) (mot minor : Expr Nat)
    {A a b x : Expr Nat}
    (hA : HasTyT E n Γ A (.sort (.succ .zero)))
    (ha : HasTyT E n Γ a A) (hb : HasTyT E n Γ b A)
    (hx : HasTyT E n Γ x (foldApps (.const 63 []) [A, a, b]))
    (ci : ConvT E n Γ b a A) (hnc : ¬ IsCtorSpine E x) :
    KNativeHead E n Γ
      (recCall (.const 65 [.succ (.succ .zero)]) [A, a, mot, minor, b] x) minor := by
  obtain ⟨hi, hc⟩ := eqKGate_of_indexConv hE mot minor hA ha hb hx ci
  exact .kStar (w := eqConvW hE A a b mot minor) ⟨rfl, rfl, rfl⟩ hnc hi hc

-- BEGIN RCIC_NATIVE_READBACK_CK2_CONV_ROOTS
#print axioms majorFamily
#print axioms computedFamily
#print axioms KIndexConvAt
#print axioms KCommonAt
#print axioms kCommonAt_irr
#print axioms kCommonAt_of_conv
#print axioms KCanonW
#print axioms iotaRhsOf_kcanon_eq
#print axioms fields_length_eq_of_same_rec
#print axioms kFreeRec_not_kProjRec
#print axioms not_kProjRec_eqEnv
#print axioms KNativeHead
#print axioms KNativeHead.intro
#print axioms KNativeHead.kStar
#print axioms KNativeHead.kProj
#print axioms detR_kNativeHead
#print axioms kNativeHead_ck_det
#print axioms kIndexConvAt_eqGap
#print axioms kCommonAt_eqGap
#print axioms kNativeHead_eqGap
#print axioms ExtendsEqEnv
#print axioms eqConvW
#print axioms eqRefl_applyTel
#print axioms eqConvW_computedFamily
#print axioms eqKCanon_families
#print axioms eqFamilyPartialTy
#print axioms eqReflApplyTy
#print axioms eqKGate_of_indexConv
#print axioms kNativeHead_eq_of_indexConv
-- END RCIC_NATIVE_READBACK_CK2_CONV_ROOTS

end Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
