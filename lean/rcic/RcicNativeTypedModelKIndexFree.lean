import rcic.RcicNativeTypedModelK

/-!
# The index-free boundary and the exact model-consumer transports

True has no parameters or indices.  And has two parameters and two fields,
but no indices.  Their proposition recursors therefore remain in the reused
model fragment.  Nat is also wholly in that fragment, for the different reason
that its family is not proposition-valued.  These facts concern every structured
witness in each admitted environment, rather than one chosen recursor call.

The local transport wrappers keep the native context frozen by `CtxModelT`
distinct from the source context and the target substitution context.  Agreement
on source-context values is required exactly where `RelSubstAtT` reads them;
agreement on lookup types is required exactly where environment typing reads them.
No local fragment result is used to assert a global Fundamental supplier.

On an environment with no indexed proposition recursor, every expression is
in the fragment.  Only under that hypothesis do model equality and the complete
old context-model laws follow.  This includes cyclic recursive Nat schemas.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit
open Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
open Rcic.Declarative.NativeValleys.TypedModelKAudit

variable {E : ResolvedEnv} {n : Nat} {R : Readback} {Ξ Γ Δ : LCtx}
  {ρ ρ' : EnvT} {σ σ' : SubstT}

/-! ## Classification by admitted metadata -/

/-- Every True witness is proposition-valued and has zero indices. -/
theorem true_rec_metadata (w : IotaWitnessS trueEnvU) :
    w.recRef = 2 ∧ PropFamilyS w ∧ w.nindices = 0 := by
  have hr : w.recRef = 2 := by
    rcases trueEnvU_mem w.hrec with hm | hm | hm
    · have hc := w.hrecK
      rw [hm.2] at hc
      cases hc
    · have hc := w.hrecK
      rw [hm.2] at hc
      cases hc
    · exact hm.1
  have hp := trueEnvU_recRef_propFamily w hr
  refine ⟨hr, hp.1, ?_⟩
  have hpre := w.hpre
  have hminor := w.hidx
  have hlen := hp.2
  omega

theorem not_indexedPropRecT_trueEnvU (r : Nat) : ¬ IndexedPropRecT trueEnvU r := by
  rintro ⟨w, _, _, hni⟩
  exact hni (true_rec_metadata w).2.2

/-- Fields and indices are independent: And has two of the former and none of the latter. -/
theorem and_rec_metadata (w : IotaWitnessS andEnvU) :
    w.recRef = 2 ∧ PropFamilyS w ∧ w.nparams = 2 ∧ w.nindices = 0 ∧
      w.nMinors = 1 ∧ w.fields.length = 2 := by
  have hr : w.recRef = 2 ∧ w.recMember = andRecMemberU := by
    rcases andEnvU_mem w.hrec with hm | hm | hm
    · have hc := w.hrecK
      rw [hm.2] at hc
      cases hc
    · have hc := w.hrecK
      rw [hm.2] at hc
      cases hc
    · exact hm
  have hd := IotaWitnessS.recData_admitted andGroupAdmitted
    (fun _ _ h => h) w hr.1 hr.2
  change w.familyRef = 0 ∧ w.famMember = andFamMember ∧
    w.nparams = 2 ∧ w.nindices = 0 ∧ w.nMinors = 1 at hd
  have hctor : w.ctorMember = andIntroMember := by
    rcases andEnvU_mem w.hctor with hm | hm | hm
    · have hc := w.hctorK
      rw [hm.2] at hc
      cases hc
    · exact hm.2
    · have hc := w.hctorK
      rw [hm.2] at hc
      cases hc
  refine ⟨hr.1, ?_, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2, ?_⟩
  · change piBody w.famMember.mtype = .sort .zero
    rw [hd.2.1]
    rfl
  · have hp := w.hnpar
    rw [hd.2.2.1, hctor] at hp
    change 2 + w.fields.length = 4 at hp
    omega

theorem not_indexedPropRecT_andEnvU (r : Nat) : ¬ IndexedPropRecT andEnvU r := by
  rintro ⟨w, _, _, hni⟩
  exact hni (and_rec_metadata w).2.2.2.1

theorem kFreeT_trueEnvU (e : Expr Nat) : KFreeT trueEnvU e :=
  kFreeT_of_no_indexed not_indexedPropRecT_trueEnvU e

theorem kFreeT_andEnvU (e : Expr Nat) : KFreeT andEnvU e :=
  kFreeT_of_no_indexed not_indexedPropRecT_andEnvU e

theorem approxTK_true_iff (n : Nat) (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) (c : CptT) :
    ApproxTK trueEnvU n Γ ρ e c ↔ ApproxT trueEnvU ρ e c :=
  approxTK_iff_approxT_of_kFree (kFreeT_trueEnvU e) c

theorem approxTK_and_iff (n : Nat) (Γ : LCtx) (ρ : EnvT) (e : Expr Nat) (c : CptT) :
    ApproxTK andEnvU n Γ ρ e c ↔ ApproxT andEnvU ρ e c :=
  approxTK_iff_approxT_of_kFree (kFreeT_andEnvU e) c

/-! ## Exact source-context and source-expression restrictions -/

/-- Lifting preserves the existing constant support, including references
reached through the fragment's transparent bodies and recursor schemas. -/
theorem kFreeT_lift {e : Expr Nat} (he : KFreeT E e) (cut amount : Nat) :
    KFreeT E (lift cut amount e) :=
  kFreeT_support he (fun _ hr => by simpa only [occursConst_lift] using hr)

/-- The landed lift equivalence transports through the fragment on both
sides.  The two native contexts are explicit and may differ freely. -/
theorem approxTK_cons_lift0_iff_of_kFree {e : Expr Nat} (he : KFreeT E e)
    (Ξ Ξ' : LCtx) (S : CptT → Prop) (c : CptT) :
    ApproxTK E n Ξ (EnvT.cons S ρ) (lift 0 1 e) c ↔ ApproxTK E n Ξ' ρ e c :=
  (approxTK_iff_approxT_of_kFree (kFreeT_lift he 0 1) c).trans
    ((approxT_cons_lift0_iff E ρ S e c).trans
      (approxTK_iff_approxT_of_kFree he c).symm)

def KFreeValuesT (E : ResolvedEnv) (Γ : LCtx) : Prop :=
  ∀ (i : Nat) (v : Expr Nat), lookupValue Γ i = some v → KFreeT E v

def KFreeTypesT (E : ResolvedEnv) (Γ : LCtx) : Prop :=
  ∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A → KFreeT E A

theorem valueAgreementT_approxTK_of_kFree (hV : KFreeValuesT E Γ) :
    ValueAgreementT (ctxModelT_approxTK E n Ξ) (ctxModelT_approxT E) Γ :=
  fun i v hv => modelAgreementAtT_kFree (hV i v hv)

theorem typeAgreementT_approxTK_of_kFree (hT : KFreeTypesT E Γ) :
    TypeAgreementT (ctxModelT_approxTK E n Ξ) (ctxModelT_approxT E) Γ :=
  fun i A hA => modelAgreementAtT_kFree (hT i A hA)

theorem relSubstAtT_approxTK_iff_of_kFree_values (hV : KFreeValuesT E Γ) :
    RelSubstAtT (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ ↔
      RelSubstAtT (ctxModelT_approxT E) R n Δ ρ ρ' σ σ' Γ :=
  relSubstAtT_congr (valueAgreementT_approxTK_of_kFree hV)

theorem relSubstIdT_approxTK_iff_of_kFree_values (hV : KFreeValuesT E Γ) :
    RelSubstIdT (ctxModelT_approxTK E n Ξ) R n Γ ρ ↔
      RelSubstIdT (ctxModelT_approxT E) R n Γ ρ :=
  relSubstIdT_congr (valueAgreementT_approxTK_of_kFree hV)

theorem fundTyAt_approxTK_iff_of_kFree {e A : Expr Nat}
    (hV : KFreeValuesT E Γ) (he : KFreeT E e) :
    FundTyAt (ctxModelT_approxTK E n Ξ) R n Γ e A ↔
      FundTyAt (ctxModelT_approxT E) R n Γ e A :=
  fundTyAt_congr (valueAgreementT_approxTK_of_kFree hV) (modelAgreementAtT_kFree he)

theorem fundConvAt_approxTK_iff_of_kFree {a b A : Expr Nat}
    (hV : KFreeValuesT E Γ) (ha : KFreeT E a) (hb : KFreeT E b) :
    FundConvAt (ctxModelT_approxTK E n Ξ) R n Γ a b A ↔
      FundConvAt (ctxModelT_approxT E) R n Γ a b A :=
  fundConvAt_congr (valueAgreementT_approxTK_of_kFree hV)
    (modelAgreementAtT_kFree ha) (modelAgreementAtT_kFree hb)

theorem tyValidAt_approxTK_iff_of_kFree {A : Expr Nat}
    (hV : KFreeValuesT E Γ) (hA : KFreeT E A) :
    TyValidAt (ctxModelT_approxTK E n Ξ) R n Γ A ↔
      TyValidAt (ctxModelT_approxT E) R n Γ A :=
  tyValidAt_congr (valueAgreementT_approxTK_of_kFree hV) (modelAgreementAtT_kFree hA)

theorem ctxValidAt_approxTK_iff_of_kFree (hV : KFreeValuesT E Γ) (hT : KFreeTypesT E Γ) :
    CtxValidAt (ctxModelT_approxTK E n Ξ) R n Γ ↔
      CtxValidAt (ctxModelT_approxT E) R n Γ :=
  ctxValidAt_congr (valueAgreementT_approxTK_of_kFree hV)
    (typeAgreementT_approxTK_of_kFree hT)

theorem envTypedAtT_approxTK_iff_of_kFree_types (hT : KFreeTypesT E Γ) :
    EnvTypedAtT (ctxModelT_approxTK E n Ξ) Γ ρ ↔ EnvTypedAtT (ctxModelT_approxT E) Γ ρ :=
  envTypedAtT_congr (typeAgreementT_approxTK_of_kFree hT)

theorem relSubstTypedAtT_approxTK_iff_of_kFree
    (hV : KFreeValuesT E Γ) (hT : KFreeTypesT E Γ) :
    RelSubstTypedAtT (ctxModelT_approxTK E n Ξ) R n Δ ρ ρ' σ σ' Γ ↔
      RelSubstTypedAtT (ctxModelT_approxT E) R n Δ ρ ρ' σ σ' Γ :=
  relSubstTypedAtT_congr (valueAgreementT_approxTK_of_kFree hV)
    (typeAgreementT_approxTK_of_kFree hT)

theorem typingAt_approxTK_iff_of_kFree {a b A : Expr Nat}
    (ha : KFreeT E a) (hb : KFreeT E b) (hA : KFreeT E A) :
    TypingAt (ctxModelT_approxTK E n Ξ) ρ ρ' a b A ↔
      TypingAt (ctxModelT_approxT E) ρ ρ' a b A :=
  typingAt_congr (modelAgreementAtT_kFree ha) (modelAgreementAtT_kFree hb)
    (modelAgreementAtT_kFree hA)

theorem modelConvSoundAt_approxTK_iff_of_kFree {a b : Expr Nat}
    (ha : KFreeT E a) (hb : KFreeT E b) :
    ModelConvSoundAt (ctxModelT_approxTK E n Ξ) ρ a b ↔
      ModelConvSoundAt (ctxModelT_approxT E) ρ a b :=
  modelConvSoundAt_congr (modelAgreementAtT_kFree ha) (modelAgreementAtT_kFree hb)

theorem hybridSeed_approxTK_iff_of_kFree {a A : Expr Nat} {c : CptT}
    (ha : KFreeT E a) (hA : KFreeT E A) :
    HybridSeed (ctxModelT_approxTK E n Ξ) R n Δ ρ σ a A c ↔
      HybridSeed (ctxModelT_approxT E) R n Δ ρ σ a A c :=
  hybridSeed_congr (modelAgreementAtT_kFree ha) (modelAgreementAtT_kFree hA)

/-! ## Whole-model transports when there is no affected recursor -/

theorem modelAgreementAtT_approxTK_of_no_indexed
    (hE : ∀ r, ¬ IndexedPropRecT E r) (e : Expr Nat) :
    ModelAgreementAtT (ctxModelT_approxTK E n Ξ) (ctxModelT_approxT E) e :=
  modelAgreementAtT_kFree (kFreeT_of_no_indexed hE e)

theorem ctxModelT_approxTK_eq_approxT_of_no_indexed
    (hE : ∀ r, ¬ IndexedPropRecT E r) :
    ctxModelT_approxTK E n Ξ = ctxModelT_approxT E :=
  ctxModelT_eq_of_agreement (modelAgreementAtT_approxTK_of_no_indexed hE)

theorem ctxModelTLaws_approxTK_of_no_indexed (hE : ∀ r, ¬ IndexedPropRecT E r) :
    CtxModelTLaws (ctxModelT_approxTK E n Ξ) :=
  (ctxModelTLaws_congr (modelAgreementAtT_approxTK_of_no_indexed hE)).mpr
    (ctxModelTLaws_approxT E)

theorem ctxModelTLaws'_approxTK_of_no_indexed (hE : ∀ r, ¬ IndexedPropRecT E r) :
    CtxModelTLaws' (ctxModelT_approxTK E n Ξ) :=
  (ctxModelTLaws'_congr (modelAgreementAtT_approxTK_of_no_indexed hE)).mpr
    (ctxModelTLaws'_approxT E)

/-- This is an equivalence of obligations, not a supplier of either side. -/
theorem fundamentalSAtT_approxTK_iff_of_no_indexed (hE : ∀ r, ¬ IndexedPropRecT E r) :
    FundamentalSAtT (ctxModelT_approxTK E n Ξ) R n ↔
      FundamentalSAtT (ctxModelT_approxT E) R n :=
  fundamentalSAtT_congr (modelAgreementAtT_approxTK_of_no_indexed hE)

theorem typingLemmaEnvT_approxTK_iff_of_no_indexed (hE : ∀ r, ¬ IndexedPropRecT E r) :
    TypingLemmaEnvT (ctxModelT_approxTK E n Ξ) n ↔ TypingLemmaEnvT (ctxModelT_approxT E) n :=
  typingLemmaEnvT_congr (modelAgreementAtT_approxTK_of_no_indexed hE)

theorem fundCases_approxTK_iff_of_no_indexed (hE : ∀ r, ¬ IndexedPropRecT E r) :
    FundCases (ctxModelT_approxTK E n Ξ) R n ↔ FundCases (ctxModelT_approxT E) R n :=
  fundCases_congr (modelAgreementAtT_approxTK_of_no_indexed hE)

/-- The raw beta obligation is merely transported; no beta expansion law is assumed. -/
theorem modelBetaExpandT_approxTK_iff_of_no_indexed (hE : ∀ r, ¬ IndexedPropRecT E r) :
    ModelBetaExpandT (ctxModelT_approxTK E n Ξ) ↔ ModelBetaExpandT (ctxModelT_approxT E) :=
  modelBetaExpandT_congr (modelAgreementAtT_approxTK_of_no_indexed hE)

theorem ctxModelTLaws_approxTK_natEnvU (n : Nat) (Ξ : LCtx) :
    CtxModelTLaws (ctxModelT_approxTK natEnvU n Ξ) :=
  ctxModelTLaws_approxTK_of_no_indexed not_indexedPropRecT_natEnvU

theorem ctxModelTLaws'_approxTK_natEnvU (n : Nat) (Ξ : LCtx) :
    CtxModelTLaws' (ctxModelT_approxTK natEnvU n Ξ) :=
  ctxModelTLaws'_approxTK_of_no_indexed not_indexedPropRecT_natEnvU

theorem ctxModelTLaws_approxTK_trueEnvU (n : Nat) (Ξ : LCtx) :
    CtxModelTLaws (ctxModelT_approxTK trueEnvU n Ξ) :=
  ctxModelTLaws_approxTK_of_no_indexed not_indexedPropRecT_trueEnvU

theorem ctxModelTLaws'_approxTK_trueEnvU (n : Nat) (Ξ : LCtx) :
    CtxModelTLaws' (ctxModelT_approxTK trueEnvU n Ξ) :=
  ctxModelTLaws'_approxTK_of_no_indexed not_indexedPropRecT_trueEnvU

theorem ctxModelTLaws_approxTK_andEnvU (n : Nat) (Ξ : LCtx) :
    CtxModelTLaws (ctxModelT_approxTK andEnvU n Ξ) :=
  ctxModelTLaws_approxTK_of_no_indexed not_indexedPropRecT_andEnvU

theorem ctxModelTLaws'_approxTK_andEnvU (n : Nat) (Ξ : LCtx) :
    CtxModelTLaws' (ctxModelT_approxTK andEnvU n Ξ) :=
  ctxModelTLaws'_approxTK_of_no_indexed not_indexedPropRecT_andEnvU

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_INDEX_FREE_ROOTS
#print axioms true_rec_metadata
#print axioms not_indexedPropRecT_trueEnvU
#print axioms and_rec_metadata
#print axioms not_indexedPropRecT_andEnvU
#print axioms kFreeT_trueEnvU
#print axioms kFreeT_andEnvU
#print axioms approxTK_true_iff
#print axioms approxTK_and_iff
#print axioms kFreeT_lift
#print axioms approxTK_cons_lift0_iff_of_kFree
#print axioms KFreeValuesT
#print axioms KFreeTypesT
#print axioms valueAgreementT_approxTK_of_kFree
#print axioms typeAgreementT_approxTK_of_kFree
#print axioms relSubstAtT_approxTK_iff_of_kFree_values
#print axioms relSubstIdT_approxTK_iff_of_kFree_values
#print axioms fundTyAt_approxTK_iff_of_kFree
#print axioms fundConvAt_approxTK_iff_of_kFree
#print axioms tyValidAt_approxTK_iff_of_kFree
#print axioms ctxValidAt_approxTK_iff_of_kFree
#print axioms envTypedAtT_approxTK_iff_of_kFree_types
#print axioms relSubstTypedAtT_approxTK_iff_of_kFree
#print axioms typingAt_approxTK_iff_of_kFree
#print axioms modelConvSoundAt_approxTK_iff_of_kFree
#print axioms hybridSeed_approxTK_iff_of_kFree
#print axioms modelAgreementAtT_approxTK_of_no_indexed
#print axioms ctxModelT_approxTK_eq_approxT_of_no_indexed
#print axioms ctxModelTLaws_approxTK_of_no_indexed
#print axioms ctxModelTLaws'_approxTK_of_no_indexed
#print axioms fundamentalSAtT_approxTK_iff_of_no_indexed
#print axioms typingLemmaEnvT_approxTK_iff_of_no_indexed
#print axioms fundCases_approxTK_iff_of_no_indexed
#print axioms modelBetaExpandT_approxTK_iff_of_no_indexed
#print axioms ctxModelTLaws_approxTK_natEnvU
#print axioms ctxModelTLaws'_approxTK_natEnvU
#print axioms ctxModelTLaws_approxTK_trueEnvU
#print axioms ctxModelTLaws'_approxTK_trueEnvU
#print axioms ctxModelTLaws_approxTK_andEnvU
#print axioms ctxModelTLaws'_approxTK_andEnvU
-- END RCIC_NATIVE_TYPED_MODEL_K_INDEX_FREE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKIndexFreeAudit
