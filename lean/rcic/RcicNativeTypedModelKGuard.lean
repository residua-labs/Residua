import rcic.RcicNativeReadbackCK2ModelObstruction
import rcic.RcicNativeReadbackCK2NativeControls

/-!
# A positive, bounded native-index guard for the new typed model

The native `KIndexConvAt` is imported unchanged.  The additional uniform
`SemEqDI` certificate is deliberately stronger: it supplies the independently
checked index separation that native conversion alone does not currently
supply.  The last section records the exact native-completeness obligation;
the existing neutral eta fixture refutes it.  No Fundamental premise is used.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKGuardAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- Same-valuation agreement of the two complete index families in the
independent strict model.  No occurrence of the new model appears here. -/
def IndexAgreementDI (E : ResolvedEnv) (w : IotaWitness E) : Prop :=
  ∀ ρ : EnvI, SemEqDI E ρ (computedFamily w) (majorFamily w)

/-- The original native certificate plus an explicit, stronger realization
certificate.  This is not asserted equivalent to unrestricted native conversion. -/
def KIndexGuardAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (w : IotaWitness E) : Prop :=
  KIndexConvAt E n Γ w ∧ IndexAgreementDI E w

theorem kIndexGuardAt_native {w : IotaWitness E}
    (h : KIndexGuardAt E n Γ w) : KIndexConvAt E n Γ w := h.1

/-- The guarded computation is still an instance of the unchanged native K
head; its additional realization certificate does not replace native typing. -/
theorem kNativeHead_of_guard {w : IotaWitness E} {x : Expr Nat}
    (hK : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
    (hi : KIndexGuardAt E n Γ w) (hc : KCommonAt E n Γ w x) :
    KNativeHead E n Γ
      (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) :=
  .intro hK hnc hi.1 hc

/-- Both sides use the same valuation.  Two unrelated valuations cannot be
silently substituted for this premise. -/
theorem eq_indexAgreementDI (hE : ExtendsEqEnv E)
    (A a b mot minor : Expr Nat)
    (hi : ∀ ρ : EnvI, SemEqDI E ρ b a) :
    IndexAgreementDI E (eqConvW hE A a b mot minor) := by
  intro ρ
  rw [eqConvW_computedFamily]
  change SemEqDI E ρ (foldApps (.const 63 []) [A, a, a])
    (foldApps (.const 63 []) [A, a, b])
  exact semEqDI_app
    (semEqDI_refl E ρ (foldApps (.const 63 []) [A, a]))
    (semEqDI_symm (hi ρ))

/-- Generic positive Eq control, retaining all native premises and the
separate uniform semantic agreement of its actual and computed indices. -/
theorem eqKGuard_of_indexConv (hE : ExtendsEqEnv E) (mot minor : Expr Nat)
    {A a b x : Expr Nat}
    (hA : HasTyT E n Γ A (.sort (.succ .zero)))
    (ha : HasTyT E n Γ a A) (hb : HasTyT E n Γ b A)
    (hx : HasTyT E n Γ x (foldApps (.const 63 []) [A, a, b]))
    (ci : ConvT E n Γ b a A)
    (hi : ∀ ρ : EnvI, SemEqDI E ρ b a) :
    KIndexGuardAt E n Γ (eqConvW hE A a b mot minor) ∧
    KCommonAt E n Γ (eqConvW hE A a b mot minor) x := by
  obtain ⟨hindex, hcommon⟩ := eqKGate_of_indexConv hE mot minor hA ha hb hx ci
  exact ⟨⟨hindex, eq_indexAgreementDI hE A a b mot minor hi⟩, hcommon⟩

/-- Every canonical witness at the original apart source is excluded by the
positive realization certificate.  This is independent of Fundamental and
does not claim native nonconvertibility from syntactic inequality. -/
theorem not_indexAgreementDI_apart {w : IotaWitness eqEnvT}
    {x mot minor : Expr Nat}
    (hr : w.recRef = 65)
    (hp : w.preMajor = [.sort .zero, idPiProp, mot, minor, apartRight])
    (hK : KCanonW w x) : ¬ IndexAgreementDI eqEnvT w := by
  intro h
  have hf := h EnvI.bot
  obtain ⟨hcomputed, hmajor⟩ := eqKCanon_families hr hp hK
  rw [hcomputed, hmajor] at hf
  have hrigid : RigidConst eqEnvT 63 :=
    rigidConst_of_inductiveM pinEqGroupWfT (m := eqFamT) rfl rfl
  have hi := semEqDI_famApp_slot hrigid hrigid hf (i := 2) (by decide)
  exact semEqDI_pi_famApp_disjoint hrigid
    (show SemEqDI eqEnvT EnvI.bot idPiProp apartRight from hi)

theorem not_kIndexGuardAt_apart {w : IotaWitness eqEnvT}
    {x mot minor : Expr Nat}
    (hr : w.recRef = 65)
    (hp : w.preMajor = [.sort .zero, idPiProp, mot, minor, apartRight])
    (hK : KCanonW w x) : ¬ KIndexGuardAt eqEnvT n Γ w :=
  fun h => not_indexAgreementDI_apart hr hp hK h.2

/-- The exact original beta-gap witness passes both independently specified
index checks, uniformly in its variable valuation. -/
theorem kIndexGuardAt_eqGap (n : Nat) :
    KIndexGuardAt eqEnvT n eqGapCtx eqGapW := by
  refine ⟨kIndexConvAt_eqGap n, ?_⟩
  intro ρ
  change SemEqDI eqEnvT ρ
    (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1])
    (foldApps (.const 63 []) [.bvar 2, .bvar 1,
      .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)])
  exact semEqDI_app
    (semEqDI_refl eqEnvT ρ (foldApps (.const 63 []) [.bvar 2, .bvar 1]))
    (semEqDI_symm (approxDI_beta eqEnvT ρ (.bvar 2) (.bvar 0) (.bvar 1)))

/-- The original native head is obtained from the stronger guard itself. -/
theorem guarded_kNativeHead_eqGap (n : Nat) :
    KNativeHead eqEnvT n eqGapCtx eqGapRedex (.sort .zero) :=
  kNativeHead_of_guard (w := eqGapW) (.inl ⟨rfl, rfl, rfl⟩)
    not_isCtorSpine_bvar (kIndexGuardAt_eqGap n) (kCommonAt_eqGap n)

/-- Uniform beta agreement strictly underneath the index binder. -/
theorem indexBinderBeta_agreementDI (E : ResolvedEnv) (ρ : EnvI) :
    SemEqDI E ρ indexBinderBeta indexId :=
  semEqDI_lam (.sort .zero) (.sort .zero)
    (fun us => approxDI_beta E (EnvI.cons (demand us) ρ)
      (.sort .zero) (.bvar 0) (.bvar 0))

/-- The already checked delta body is closed, so agreement holds at every
valuation, including valuations introduced underneath a binder. -/
theorem deltaIndex_agreementDI (ρ : EnvI) :
    SemEqDI deltaEqEnv ρ (.const 66 []) indexId :=
  semEqDI_delta (m := deltaEqMember) (b := indexId) (ls := [])
    (deltaConst_of_transparent rfl rfl rfl) rfl

theorem deltaBinderIndex_agreementDI (ρ : EnvI) :
    SemEqDI deltaEqEnv ρ deltaBinderIndex indexId := by
  apply semEqDI_lam (.sort .zero) (.sort .zero)
  intro us
  exact semEqDI_trans
    (semEqDI_app (deltaIndex_agreementDI (EnvI.cons (demand us) ρ))
      (semEqDI_refl deltaEqEnv _ (.bvar 0)))
    (approxDI_beta deltaEqEnv (EnvI.cons (demand us) ρ)
      (.sort .zero) (.bvar 0) (.bvar 0))

theorem kIndexGuardAt_binder (n : Nat) :
    KIndexGuardAt eqEnvT n binderEqCtx
      (eqConvW (fun _ _ h => h) indexFn indexId indexBinderBeta
        binderIndexMot (.sort .zero)) :=
  (eqKGuard_of_indexConv (fun _ _ h => h) binderIndexMot (.sort .zero)
    (indexFnTy eqEnvT n binderEqCtx) (indexIdTy eqEnvT n binderEqCtx)
    (indexBinderBetaTy eqEnvT n binderEqCtx) (.bvar binderEqCtx 0 _ rfl)
    (indexBinderBetaConv eqEnvT n binderEqCtx)
    (indexBinderBeta_agreementDI eqEnvT)).1

theorem kIndexGuardAt_delta (n : Nat) :
    KIndexGuardAt deltaEqEnv n deltaHeadEqCtx
      (eqConvW deltaEqExtends indexFn indexId (.const 66 [])
        binderIndexMot (.sort .zero)) :=
  (eqKGuard_of_indexConv deltaEqExtends binderIndexMot (.sort .zero)
    (indexFnTy deltaEqEnv n deltaHeadEqCtx) (indexIdTy deltaEqEnv n deltaHeadEqCtx)
    (deltaConstTy n deltaHeadEqCtx) (.bvar deltaHeadEqCtx 0 _ rfl)
    (deltaIndexConv n deltaHeadEqCtx) deltaIndex_agreementDI).1

theorem kIndexGuardAt_delta_under_binder (n : Nat) :
    KIndexGuardAt deltaEqEnv n deltaUnderBinderEqCtx
      (eqConvW deltaEqExtends indexFn indexId deltaBinderIndex
        binderIndexMot (.sort .zero)) :=
  (eqKGuard_of_indexConv deltaEqExtends binderIndexMot (.sort .zero)
    (indexFnTy deltaEqEnv n deltaUnderBinderEqCtx)
    (indexIdTy deltaEqEnv n deltaUnderBinderEqCtx)
    (deltaBinderTy n deltaUnderBinderEqCtx) (.bvar deltaUnderBinderEqCtx 0 _ rfl)
    (deltaBinderIndexConv n deltaUnderBinderEqCtx) deltaBinderIndex_agreementDI).1

/-- Each complete positive control retains its original native head. -/
theorem guarded_native_binder_control (n : Nat) :
    KIndexGuardAt eqEnvT n binderEqCtx
      (eqConvW (fun _ _ h => h) indexFn indexId indexBinderBeta
        binderIndexMot (.sort .zero)) ∧
    KNativeHead eqEnvT n binderEqCtx binderIndexRedex (.sort .zero) :=
  ⟨kIndexGuardAt_binder n, kNativeHead_binder n⟩

theorem guarded_native_delta_control (n : Nat) :
    KIndexGuardAt deltaEqEnv n deltaHeadEqCtx
      (eqConvW deltaEqExtends indexFn indexId (.const 66 [])
        binderIndexMot (.sort .zero)) ∧
    KNativeHead deltaEqEnv n deltaHeadEqCtx
      (deltaRedex (.const 66 [])) (.sort .zero) :=
  ⟨kIndexGuardAt_delta n, kNativeHead_delta n⟩

theorem guarded_native_delta_under_binder_control (n : Nat) :
    KIndexGuardAt deltaEqEnv n deltaUnderBinderEqCtx
      (eqConvW deltaEqExtends indexFn indexId deltaBinderIndex
        binderIndexMot (.sort .zero)) ∧
    KNativeHead deltaEqEnv n deltaUnderBinderEqCtx
      (deltaRedex deltaBinderIndex) (.sort .zero) :=
  ⟨kIndexGuardAt_delta_under_binder n, kNativeHead_delta_under_binder n⟩

/-- Quantifying over one common valuation distinguishes two different free
variables; checking only the bottom valuation would miss this distinction. -/
theorem not_uniform_agreementDI_distinct_bvars (E : ResolvedEnv)
    {i j : Nat} (hij : i ≠ j) :
    ¬ (∀ ρ : EnvI, SemEqDI E ρ (.bvar i) (.bvar j)) := by
  intro h
  let ρ : EnvI := fun k c => k = i ∧ c = .sort
  have hi : ApproxDI E ρ (.bvar i) .sort := .bvar ⟨rfl, rfl⟩
  rcases approxDI_bvar_inv ((h ρ .sort).mp hi) with hbot | hj
  · exact CptI.noConfusion hbot
  · exact hij hj.1.symm

/-- At the existing neutral eta fixture the independent model separates the
two terms.  The lambda's all-bottom step compact is absent from the variable. -/
theorem not_agreementDI_etaIndex :
    ¬ SemEqDI eqEnvT EnvI.bot (.bvar 1) etaIndex := by
  intro h
  have hη : ApproxDI eqEnvT EnvI.bot etaIndex (.lam [([], .bot)]) := by
    apply ApproxDI.lam
    intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact .bot _ _
  rcases approxDI_bvar_inv ((h (.lam [([], .bot)])).mpr hη) with hbot | hbot
  · exact CptI.noConfusion hbot
  · exact CptI.noConfusion hbot

/-- No canonical witness at the imported neutral eta source passes the
additional agreement check, although the original native K head exists. -/
theorem not_indexAgreementDI_eta {w : IotaWitness eqEnvT}
    {x mot minor : Expr Nat}
    (hr : w.recRef = 65)
    (hp : w.preMajor = [indexFn, .bvar 1, mot, minor, etaIndex])
    (hK : KCanonW w x) : ¬ IndexAgreementDI eqEnvT w := by
  intro h
  have hf := h EnvI.bot
  obtain ⟨hcomputed, hmajor⟩ := eqKCanon_families hr hp hK
  rw [hcomputed, hmajor] at hf
  have hrigid : RigidConst eqEnvT 63 :=
    rigidConst_of_inductiveM pinEqGroupWfT (m := eqFamT) rfl rfl
  exact not_agreementDI_etaIndex
    (semEqDI_famApp_slot hrigid hrigid hf (i := 2) (by decide))

theorem not_kIndexGuardAt_eta (n : Nat) :
    ¬ KIndexGuardAt eqEnvT n etaEqCtx
      (eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex
        etaIndexMot (.sort .zero)) := by
  intro h
  exact not_indexAgreementDI_eta
    (w := eqConvW (fun _ _ h => h) indexFn (.bvar 1) etaIndex
      etaIndexMot (.sort .zero)) rfl rfl
    (x := .bvar 0) (.inl ⟨rfl, rfl, rfl⟩) h.2

/-- The exact extra implication that would be needed to accept every native
K head.  Native well-formed contexts, canonical witnesses, common typing and
the existing index certificate are all retained. -/
def NativeKIndexComplete (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ (w : IotaWitness E) (x : Expr Nat),
    KCanonW w x → (¬ IsCtorSpine E x) → KCommonAt E n Γ w x →
    KIndexConvAt E n Γ w → IndexAgreementDI E w

/-- Under exactly the named completeness port, the native premise acquires
the stronger guard.  This theorem does not provide that port. -/
theorem kIndexGuardAt_of_native_complete (h : NativeKIndexComplete E n)
    (hΓ : CtxWfT E n Γ) {w : IotaWitness E} {x : Expr Nat}
    (hK : KCanonW w x) (hnc : ¬ IsCtorSpine E x)
    (hc : KCommonAt E n Γ w x) (hi : KIndexConvAt E n Γ w) :
    KIndexGuardAt E n Γ w := ⟨hi, h hΓ w x hK hnc hc hi⟩

/-- The admitted neutral eta control refutes the universal native-completeness
port.  The candidate is therefore a bounded repair, not full native K semantics. -/
theorem not_nativeKIndexComplete_eqEnv (n : Nat) :
    ¬ NativeKIndexComplete eqEnvT n := by
  intro h
  obtain ⟨hi, hc⟩ := eqKGate_of_indexConv (fun _ _ h => h)
    etaIndexMot (.sort .zero) (indexFnTy eqEnvT n etaEqCtx)
    (etaIndexParamTy n) (etaIndexTy n) (.bvar etaEqCtx 0 _ rfl) (etaIndexConv n)
  exact not_kIndexGuardAt_eta n
    (kIndexGuardAt_of_native_complete h (etaEqCtxWf n)
      (.inl ⟨rfl, rfl, rfl⟩) not_isCtorSpine_bvar hc hi)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_GUARD_ROOTS
#print axioms IndexAgreementDI
#print axioms KIndexGuardAt
#print axioms kIndexGuardAt_native
#print axioms kNativeHead_of_guard
#print axioms eq_indexAgreementDI
#print axioms eqKGuard_of_indexConv
#print axioms not_indexAgreementDI_apart
#print axioms not_kIndexGuardAt_apart
#print axioms kIndexGuardAt_eqGap
#print axioms guarded_kNativeHead_eqGap
#print axioms indexBinderBeta_agreementDI
#print axioms deltaIndex_agreementDI
#print axioms deltaBinderIndex_agreementDI
#print axioms kIndexGuardAt_binder
#print axioms kIndexGuardAt_delta
#print axioms kIndexGuardAt_delta_under_binder
#print axioms guarded_native_binder_control
#print axioms guarded_native_delta_control
#print axioms guarded_native_delta_under_binder_control
#print axioms not_uniform_agreementDI_distinct_bvars
#print axioms not_agreementDI_etaIndex
#print axioms not_indexAgreementDI_eta
#print axioms not_kIndexGuardAt_eta
#print axioms NativeKIndexComplete
#print axioms kIndexGuardAt_of_native_complete
#print axioms not_nativeKIndexComplete_eqEnv
-- END RCIC_NATIVE_TYPED_MODEL_K_GUARD_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKGuardAudit
