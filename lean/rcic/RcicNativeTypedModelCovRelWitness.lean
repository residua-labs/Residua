import rcic.RcicNativeTypedModelCovRelExpansion

/-!
# Native non-bottom controls for the recursive covariant relation

The polymorphic identity inhabits the genuinely recursive lambda clauses at
the same two-row compact that refutes old compact typing. The rigid successor
is a complementary escape control: its unchanged spine clause is inhabited,
including native typing and actual model realization, while covariant model
typing is impossible at every realized declared-type code.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelAudit.TypingFin
open FamModelAudit ReadbackCKAudit ReadbackCK2Audit
open TypedModelKFragmentAudit TypedModelKAudit TypedModelKFailureAudit
open TypedModelKTypedBetaAudit
open TypedModelCovKAudit TypedModelCovRelBoundaryAudit TypedModelCovPropagationAudit
open TypedModelCovRelAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- An identity row returns its demanded compact. The annotations may differ;
the left annotation supplies the native argument type required by the clause. -/
theorem lrSCoreCov_identity_row (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A A' : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (c : CptT) :
    LRSCoreCov C R n Γ (.lam A (.bvar 0)) (.lam A' (.bvar 0))
      (.pi A (lift 0 1 A)) (.lam [([c], c)]) := by
  rw [LRSCoreCov.eq_def]
  refine ⟨A, lift 0 1 A, .refl _, ⟨.assumption Γ A u hΓ hA⟩, ?_⟩
  intro s hs N N' hN hN' hc hr
  obtain rfl := List.mem_singleton.mp hs
  have hout := hr c (List.mem_singleton.mpr rfl)
  have hi : instantiate0 N (lift 0 1 A) = A := instantiate_lift_id 0 N A
  rw [hi]
  exact lrSCoreCov_expand_red_both C hL
    (redR_single (hL.beta Γ A (.bvar 0) N))
    (redR_single (hL.beta Γ A' (.bvar 0) N')) c hout

/-- Every row of the actual polymorphic identity compact is an identity row
after its first beta step. Both rows are checked, including the larger demand. -/
theorem lrSCoreCov_polyId_cpt01 (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    LRSCoreCov C R n Γ cexPolyId cexPolyId cexPolyIdTy polyIdCpt01 := by
  rw [polyIdCpt01, LRSCoreCov.eq_def]
  refine ⟨.sort (.succ .zero), .pi (.bvar 0) (.bvar 1), .refl _,
    ⟨.assumption Γ (.sort (.succ .zero)) (.succ (.succ .zero)) hΓ (.sort _ _)⟩, ?_⟩
  intro s hs N N' hN hN' hc hr
  have row (c : CptT) :
      LRSCoreCov C R n Γ (.app cexPolyId N) (.app cexPolyId N')
        (instantiate0 N (.pi (.bvar 0) (.bvar 1))) (.lam [([c], c)]) := by
    exact lrSCoreCov_expand_red_both C hL
      (redR_single (hL.beta Γ (.sort (.succ .zero)) (.lam (.bvar 0) (.bvar 0)) N))
      (redR_single (hL.beta Γ (.sort (.succ .zero)) (.lam (.bvar 0) (.bvar 0)) N'))
      (.lam [([c], c)]) (lrSCoreCov_identity_row C hL hΓ hN c)
  rcases List.mem_cons.mp hs with hs | hs
  · obtain rfl := hs
    exact row .prop
  · obtain rfl := List.mem_singleton.mp hs
    exact row polyIdWitness1

/-- The new recursive relation and the actual covariant model typing coexist
at the old polymorphic-identity obstruction, with both compacts non-bottom. -/
theorem polyId_covRel_control_approxTK (E : ResolvedEnv) (n : Nat) (ρ : EnvT) :
    Nonempty (HasTyT E n [] cexPolyId cexPolyIdTy) ∧
    EnvTypedCovAtM (ctxModelT_approxTK E n []) [] ρ ∧
    ApproxTK E n [] ρ cexPolyId polyIdCpt01 ∧
    ApproxTK E n [] ρ cexPolyIdTy polyIdTyCpt01 ∧
    CTyCov E polyIdCpt01 polyIdTyCpt01 ∧
    LRSCoreCov (covTypingCTyCov E) (WhStepCK2 E n) n []
      cexPolyId cexPolyId cexPolyIdTy polyIdCpt01 ∧
    polyIdCpt01 ≠ .bot ∧ polyIdTyCpt01 ≠ .bot ∧
    ¬ ∃ a, ApproxTK E n [] ρ cexPolyIdTy a ∧ CTyS E polyIdCpt01 a := by
  obtain ⟨ht, hρ, he, hA, hcov, hne, hneA, hnot⟩ :=
    polyId_cov_reentry_control_approxTK E n ρ
  exact ⟨ht, hρ, he, hA, hcov,
    lrSCoreCov_polyId_cpt01 (covTypingCTyCov E) (readbackLaws_whStepCK2 E n) .nil,
    hne, hneA, hnot⟩

/-- The unchanged spine leaf admits the rigid successor at its actual Pi type,
independently of which admissible compact typing supplies the recursive gates. -/
theorem lrSCoreCov_natSucc_spine (C : CovTyping natEnvU) (n : Nat) (Γ : LCtx) :
    LRSCoreCov C (WhStepCK2 natEnvU n) n Γ (.const 2 []) (.const 2 [])
      (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) := by
  rw [lrSCoreCov_spine_iff]
  have hn := normalR_ctorSpineCK2 (n := n) natEnvUWfT
    (rfl : natEnvU.members 2 = some natSuccMember) rfl Γ [] []
  refine ⟨natSuccMember, [], [], [], [], rfl, .refl _, .refl _,
    hn, hn, ?_, by decide, by decide, .nil _, ?_⟩
  · trivial
  · intro _ hind
    exact MemberClass.noConfusion hind

/-- This counterexample retains every native and model guard that could make
a proposed unconditional relation-to-model-typing escape non-vacuous. -/
theorem natSucc_covRel_nonEscape_control (n : Nat) (ρ : EnvT) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n []) ∧
    Nonempty (HasTyT natEnvU n [] (.const 2 []) (.pi (.const 0 []) (.const 0 []))) ∧
    EnvTypedCovAtM (ctxModelT_approxTK natEnvU n []) [] ρ ∧
    ApproxTK natEnvU n [] ρ (.const 2 []) (.spine 2 []) ∧
    LRSCoreCov (covTypingCTyCov natEnvU) (WhStepCK2 natEnvU n) n []
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) ∧
    (.spine 2 [] : CptT) ≠ .bot ∧
    ¬ ElTCovM (ctxModelT_approxTK natEnvU n []) ρ
      (.pi (.const 0 []) (.const 0 [])) (.spine 2 []) := by
  refine ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, ⟨hasTyT_natEnvU_succ n []⟩,
    envTypedCovAtM_nil _ ρ,
    ApproxTK.free (kFreeT_natEnvU _) (approxT_natSucc_spine ρ),
    lrSCoreCov_natSucc_spine (covTypingCTyCov natEnvU) n [],
    (fun h => CptT.noConfusion h), ?_⟩
  rintro ⟨a, ha, hc⟩
  exact not_elTCov_natSucc_spine ρ ⟨a, approxTK_forget ha, hc⟩

private theorem approxT_lam_empty_row {ρ : EnvT} {D b : Expr Nat} {c : CptT}
    (hne : c ≠ .bot) (hb : ApproxT E (EnvT.cons (demandT []) ρ) b c) :
    ApproxT E ρ (.lam D b) (.lam [([], c)]) := by
  refine .lam (.bot _ _) ?_ ⟨([], c), List.mem_singleton.mpr rfl, hne⟩ ?_
  · intro s hs u hu
    obtain rfl := List.mem_singleton.mp hs
    exact (List.not_mem_nil _ hu).elim
  · intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact hb

/-- The saturated, natively typed successor call realizes the actual positive
recursor compact from `TypingFin`, using its concrete motive and minor demands. -/
theorem approxTK_natRec_good_call (ρ : EnvT) :
    ApproxTK natEnvU 1 [] ρ (iotaLhsOf wSuccU1) (.spine 1 []) := by
  apply ApproxTK.free (kFreeT_natEnvU _)
  have hmot : ApproxT natEnvU ρ natMotive covGoodMotiveCpt :=
    approxT_lam_empty_row (fun h => CptT.noConfusion h)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)
  have hminor : ApproxT natEnvU ρ natMinorS covGoodHsCpt :=
    approxT_lam_empty_row (fun h => CptT.noConfusion h)
      (approxT_lam_empty_row (fun h => CptT.noConfusion h)
        (.const _ 1 [] rigidConst_natEnvU_zero not_propCtorT_natEnvU_zero))
  have h1 : ApproxT natEnvU ρ (.app (.const 3 [.succ .zero]) natMotive)
      (curryStepT [[], [covGoodHsCpt], ctorDemandT 2 0 [[]]] (.spine 1 [])) := by
    apply ApproxT.app (approxT_natRec_covGoodRecCpt ρ) (List.mem_singleton.mpr rfl)
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact hmot
  have h2 : ApproxT natEnvU ρ
      (.app (.app (.const 3 [.succ .zero]) natMotive) natMinorZ)
      (curryStepT [[covGoodHsCpt], ctorDemandT 2 0 [[]]] (.spine 1 [])) :=
    .app h1 (List.mem_singleton.mpr rfl) (fun _ h => (List.not_mem_nil _ h).elim)
  have h3 : ApproxT natEnvU ρ
      (.app (.app (.app (.const 3 [.succ .zero]) natMotive) natMinorZ) natMinorS)
      (curryStepT [ctorDemandT 2 0 [[]]] (.spine 1 [])) := by
    apply ApproxT.app h2 (List.mem_singleton.mpr rfl)
    intro u hu
    obtain rfl := List.mem_singleton.mp hu
    exact hminor
  apply ApproxT.app h3 (List.mem_singleton.mpr rfl)
  intro u hu
  change u ∈ [CptT.spine 2 [.bot]] at hu
  obtain rfl := List.mem_singleton.mp hu
  exact .appSpine (approxT_natSucc_spine ρ) (.bot _ _)

/-- The existing native Nat.rec successor witness takes one iota and two beta
steps to zero. No recursor normalization supplier is assumed. -/
theorem redR_natRec_good_call :
    RedR (WhStepCK2 natEnvU 1) [] (iotaLhsOf wSuccU1) (.const 1 []) := by
  apply RedR.step (WhStepCK2.ctx (WhStepCtx.iota (DerivedIotaU.ofU wSuccU1)))
  exact .step (.ctx (.appHead (.beta (.const 0 [])
    (.lam (.const 0 []) (.const 1 [])) natField)))
    (.step (.ctx (.beta (.const 0 []) (.const 1 [])
      (recCall (.const 3 [.succ .zero]) [natMotive, natMinorZ, natMinorS] natField)))
      (.refl _))

/-- A positive recursive relation observation for the actual typed Nat.rec
call. Both endpoints expand from the normal constructor zero. -/
theorem lrSCoreCov_natRec_good_call (C : CovTyping natEnvU) :
    LRSCoreCov C (WhStepCK2 natEnvU 1) 1 []
      (iotaLhsOf wSuccU1) (iotaLhsOf wSuccU1) (.const 0 []) (.spine 1 []) := by
  apply lrSCoreCov_expand_red_both C (readbackLaws_whStepCK2 natEnvU 1)
    redR_natRec_good_call redR_natRec_good_call (.spine 1 [])
  rw [lrSCoreCov_spine_iff]
  have hn := normalR_ctorSpineCK2 (n := 1) natEnvUWfT
    (rfl : natEnvU.members 1 = some natZeroMember) rfl [] [] []
  refine ⟨natZeroMember, [], [], [], [], rfl, .refl _, .refl _,
    hn, hn, ?_, by decide, by decide, .nil _, ?_⟩
  · trivial
  · intro _ hind
    exact MemberClass.noConfusion hind

/-- All the positive Nat.rec controls concern the same admitted environment,
actual source typing, fixed model context, and non-bottom result compact. -/
theorem natRec_covRel_control_approxTK (ρ : EnvT) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU 1 []) ∧
    Nonempty (HasTyT natEnvU 1 [] (iotaLhsOf wSuccU1) (.const 0 [])) ∧
    EnvTypedCovAtM (ctxModelT_approxTK natEnvU 1 []) [] ρ ∧
    ApproxTK natEnvU 1 [] ρ (iotaLhsOf wSuccU1) (.spine 1 []) ∧
    ApproxTK natEnvU 1 [] ρ (.const 0 []) (.spine 0 []) ∧
    CTyCov natEnvU (.spine 1 []) (.spine 0 []) ∧
    LRSCoreCov (covTypingCTyCov natEnvU) (WhStepCK2 natEnvU 1) 1 []
      (iotaLhsOf wSuccU1) (iotaLhsOf wSuccU1) (.const 0 []) (.spine 1 []) ∧
    (.spine 1 [] : CptT) ≠ .bot ∧ (.spine 0 [] : CptT) ≠ .bot := by
  refine ⟨⟨natEnvUWfT⟩, ⟨.nil⟩, ⟨pinIotaLhsTy⟩, envTypedCovAtM_nil _ ρ,
    approxTK_natRec_good_call ρ,
    ApproxTK.free (kFreeT_natEnvU _)
      (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat),
    ?_, lrSCoreCov_natRec_good_call (covTypingCTyCov natEnvU),
    (fun h => CptT.noConfusion h), (fun h => CptT.noConfusion h)⟩
  rw [CTyCov]
  exact Or.inr ⟨⟨1, [], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

/-- The actual Eq alias also enters the new relation at the common sort leaf.
Only this identical leaf clause is reused; no recursive relation cast is used. -/
theorem eqGapDirectAlias_lrsCoreCov_prop (C : CovTyping eqEnvT)
    (n : Nat) (A B : Expr Nat) :
    LRSCoreCov C (WhStepCK2 eqEnvT n) n eqGapCtx
      (eqGapDirectAlias A B) eqGapRedex (.sort (.succ .zero)) .prop :=
  (lrSCoreCov_prop_iff C _ _ _ _).mpr
    ((lrSCoreS_prop_iff _ _ _ _).mp (eqGapDirectAlias_lrsCoreS_prop n A B))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_WITNESS_ROOTS
#print axioms lrSCoreCov_identity_row
#print axioms lrSCoreCov_polyId_cpt01
#print axioms polyId_covRel_control_approxTK
#print axioms lrSCoreCov_natSucc_spine
#print axioms natSucc_covRel_nonEscape_control
#print axioms approxTK_natRec_good_call
#print axioms redR_natRec_good_call
#print axioms lrSCoreCov_natRec_good_call
#print axioms natRec_covRel_control_approxTK
#print axioms eqGapDirectAlias_lrsCoreCov_prop
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_WITNESS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelWitnessAudit
