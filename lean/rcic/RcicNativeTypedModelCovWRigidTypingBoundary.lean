import rcic.RcicNativeTypedModelCovWRigidTransport

/-! The landed code typing does not yet type dependent recursor results.
The W source is natively typed at Sort 1 and has a spine observation, but its declaration ends
in an application of the motive rather than a literal sort. This is a
boundary of the inherited compact typing, not a native nonconversion claim. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

open TypedModelCovTAudit TypedModelCovVAudit TypedModelCovWAudit
open TypedModelCovWIrrelAudit TypedModelCovWMatrixAudit
open TypedModelCovWNativeAudit TypedModelCovWConvAudit

theorem covWRigid_Ho_spine_not_universe (ls : List Level)
    (args : List CptWConvR) (l : Level) :
    ¬ UniverseWConv covUHoEnv (.spine 65 ls args) l := by
  intro h
  cases h with
  | spine r ls args m u l hm hu hl =>
    have he : m = covUHoRec := Option.some.inj hm.symm
    subst m
    cases hu

/-- No representative of this public spine has a strict sort code type. -/
theorem covWRigid_Ho_demand_not_sort_typed (l : Level) :
    ¬ CTySConv covUHoEnv covWRigidHoDemand (.sort (LevelCode.ofLevel l)) := by
  rintro ⟨c, a, hc, ha, ht⟩
  cases c with
  | bot => cases hc
  | sort u => cases hc
  | pi d rows => cases hc
  | lam rows => cases hc
  | spine r ls args =>
    have hr : r = 65 := (CptWConv.spine.inj hc).1
    subst r
    cases a with
    | bot => cases ha
    | sort v =>
      cases ht with
      | sortTy hu hc => exact covWRigid_Ho_spine_not_universe ls args v hu
    | pi d rows => cases ha
    | lam rows => cases ha
    | spine s ks vals => cases ha

/-- Every premise of the observation-versus-code-typing failure is inhabited.
In particular, the term and its type are natively typed in the admitted
closed environment, and the type has the requested new observation. -/
theorem covWRigid_Ho_typing_boundary_inhabited (n : Nat) :
    Nonempty (EnvWfT covUHoEnv) ∧ Nonempty (CtxWfT covUHoEnv n []) ∧
    Nonempty (HasTyT covUHoEnv n [] covWMatrixIotaSource (.sort (.succ .zero))) ∧
    Nonempty (HasTyT covUHoEnv n [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))) ∧
    CovWRigidObservation covUHoEnv n [] EnvWConvR.bot (.sort (.succ .zero))
      (.sort (LevelCode.ofLevel (.succ .zero))) ∧
    CovWRigidObservation covUHoEnv n [] EnvWConvR.bot covWMatrixIotaSource covWRigidHoDemand ∧
    covWRigidHoDemand ≠ .bot ∧
    ¬ CTySConv covUHoEnv covWRigidHoDemand (.sort (LevelCode.ofLevel (.succ .zero))) :=
  ⟨⟨covUHoEnv_wf⟩, ⟨.nil⟩, ⟨covWMatrixIotaSource_ty n []⟩,
    ⟨.sort [] (.succ .zero)⟩, covWRigid_observation_of (.sort _ _ _),
    covWRigid_observation_of (covWRigid_Ho_ctor_observed n [] EnvWConvR.bot),
    covWRigid_Ho_demand_nonbottom, covWRigid_Ho_demand_not_sort_typed _⟩

end Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit

-- BEGIN COVWRIGID GENERATED MISSING AXIOM ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_spine_not_universe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_demand_not_sort_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWRigidAudit.covWRigid_Ho_typing_boundary_inhabited
-- END COVWRIGID GENERATED MISSING AXIOM ROOTS
