import rcic.RcicNativeTypedModelCovPTyping
import rcic.RcicNativeTypedModelCovPTransport
import rcic.RcicNativeTypedModelCovZFixtures

/-!
# Eight concrete codes under positive collapse and guarded reflection

The original native, substitution, and relation certificates are retained.
Both hereditary interpretations are actually rebuilt with `CTyCovP2`; the
fixed-code compatibility facts below are proved at each displayed code.
This does not assert a new fundamental theorem for a new relation, and does
not construct a common code. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ModelObstructionAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovNormEscapeAudit
open TypedModelCovXAudit TypedModelCovXEtaAudit TypedModelCovYAudit
open TypedModelCovYEtaAudit TypedModelCovYPolyPropAudit TypedModelCovZAudit

variable {E : ResolvedEnv}

theorem covP_transport_bot (reflect : Bool) :
    CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) .bot := by
  rw [CovPCodeTransport.eq_def]
  exact ⟨fun c h => ctyCovP2_of_ctyCov2 reflect c .bot h, trivial⟩

theorem covP_transport_prop (reflect : Bool) :
    CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) .prop := by
  rw [CovPCodeTransport.eq_def]
  exact ⟨fun c h => ctyCovP2_of_ctyCov2 reflect c .prop h, trivial⟩

theorem covP_transport_sort (reflect : Bool) :
    CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) .sort := by
  rw [CovPCodeTransport.eq_def]
  exact ⟨fun c h => ctyCovP2_of_ctyCov2 reflect c .sort h, trivial⟩

theorem covP_transport_spine (reflect : Bool) (r : Nat) (us : List CptT) :
    CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) (.spine r us) := by
  rw [CovPCodeTransport.eq_def]
  exact ⟨fun c h => ctyCovP2_of_ctyCov2 reflect c (.spine r us) h, trivial⟩

theorem covP_transport_pi (reflect : Bool) (d : CptT)
    (g : List (List CptT × CptT))
    (hdom : ∀ c, CTyCovP2 reflect E c d → CTyCov2 E c d)
    (hout : ∀ row ∈ g, ∀ c, CTyCovP2 reflect E c row.2 → CTyCov2 E c row.2)
    (hd : CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) d)
    (hg : ∀ row ∈ g, CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) row.2) :
    CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) (.pi d g) := by
  rw [CovPCodeTransport.eq_def]
  exact ⟨fun c h => ctyCovP2_of_ctyCov2 reflect c (.pi d g) h, hdom, hout, hd, hg⟩

theorem covP_transport_natArrow (reflect : Bool) :
    CovPCodeTransport (CTyCov2 natEnvU) (CTyCovP2 reflect natEnvU) covYNatArrowCode := by
  apply covP_transport_pi reflect
  · intro c h
    exact ctyCovP2_spine_iff_ctyCov2.mp h
  · intro row hr c h
    obtain rfl := List.mem_singleton.mp hr
    exact ctyCovP2_spine_iff_ctyCov2.mp h
  · exact covP_transport_spine reflect 0 []
  · intro row hr
    obtain rfl := List.mem_singleton.mp hr
    exact covP_transport_spine reflect 0 []

theorem covP_transport_aliasCode (reflect : Bool) :
    CovPCodeTransport (CTyCov2 eqEnvT) (CTyCovP2 reflect eqEnvT) covYAliasPiCode := by
  apply covP_transport_pi reflect
  · intro c h
    exact ctyCovP2_prop_iff.mp h
  · intro row hr c h
    obtain rfl := List.mem_singleton.mp hr
    exact ctyCovP2_prop_iff.mp h
  · exact covP_transport_prop reflect
  · intro row hr
    obtain rfl := List.mem_singleton.mp hr
    exact covP_transport_prop reflect

theorem covP_transport_polyPropCode (reflect : Bool) :
    CovPCodeTransport (CTyCov2 eqEnvT) (CTyCovP2 reflect eqEnvT) covYPolyPropCode := by
  apply covP_transport_pi reflect
  · intro c h
    rw [ctyCovP2_bot_inv h]
    exact ctyCov2_bot _
  · intro row hr c h
    obtain rfl := List.mem_singleton.mp hr
    exact ctyCovP2_sort_iff.mp h
  · exact covP_transport_bot reflect
  · intro row hr
    obtain rfl := List.mem_singleton.mp hr
    exact covP_transport_sort reflect

/-- The landed relation payload and repaired hereditary interpretations are
named separately in this conjunction; no old environment package is relabelled. -/
def CovPJointAt (reflect : Bool) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ ρ' : EnvT) (x y A : Expr Nat) (c b : CptT) : Prop :=
  LRSCoreCovY (C2 E) (WhStepCK2 E n) n Γ x y A c b ∧
  HereditaryCovRealizationPAt (CTyCovP2 reflect E)
    (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
    (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ A c b ∧
  HereditaryCovRealizationPAt (CTyCovP2 reflect E)
    (LRSCoreCovY (C2 E) (WhStepCK2 E n) n)
    (ctxModelT_approxTK E n) (WhStepCK2 E n) n Γ ρ' A c b

theorem covP_joint_of_Y (reflect : Bool) (n : Nat) (Γ : LCtx)
    (ρ ρ' : EnvT) (x y A : Expr Nat) (c b : CptT)
    (hc : CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) b)
    (h : CovZJointCodeAt (C2 E) (ctxModelT_approxTK E n) (WhStepCK2 E n)
      n Γ ρ ρ' x y A c b) : CovPJointAt reflect E n Γ ρ ρ' x y A c b :=
  ⟨h.1,
    hereditaryCovRealizationPAt_from_Y (C2 E) (CTyCovP2 reflect E) _ _ n
      Γ ρ A c b hc h.2.1,
    hereditaryCovRealizationPAt_from_Y (C2 E) (CTyCovP2 reflect E) _ _ n
      Γ ρ' A c b hc h.2.2⟩

def CovPFixtureAt (reflect : Bool) (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (ρ : EnvT) (x y A : Expr Nat) (c b : CptT) : Prop :=
  CovZInhabitedJointAt E n Γ ρ x y A c b ∧
  CovPJointAt reflect E n Γ ρ ρ x y A c b

theorem covP_fixture_of_Y (reflect : Bool) {n : Nat} {Γ : LCtx}
    {ρ : EnvT} {x y A : Expr Nat} {c b : CptT}
    (hc : CovPCodeTransport (CTyCov2 E) (CTyCovP2 reflect E) b)
    (h : CovZInhabitedJointAt E n Γ ρ x y A c b) :
    CovPFixtureAt reflect E n Γ ρ x y A c b := by
  refine ⟨h, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, hj⟩ := h
  exact covP_joint_of_Y reflect n Γ ρ ρ x y A c b hc hj

theorem covP_fixture_natSucc_eta (reflect : Bool) (n : Nat) :
    CovPFixtureAt reflect natEnvU n [] EnvT.bot
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0)))
      (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      covXNatEtaEmptyRow covYNatArrowCode :=
  covP_fixture_of_Y reflect (covP_transport_natArrow reflect) (covZ_fixture_natSucc_eta n)

theorem covP_fixture_alias_in_pi (reflect : Bool) (n : Nat) :
    ∃ A B, CovPFixtureAt reflect eqEnvT n eqGapCtx EnvT.bot
      covNormAliasIdentity covNormAliasIdentity (covNormAliasPi A B)
      covNormAliasIdentityCpt covYAliasPiCode := by
  obtain ⟨A, B, h⟩ := covZ_fixture_alias_in_pi n
  exact ⟨A, B, covP_fixture_of_Y reflect (covP_transport_aliasCode reflect) h⟩

theorem covP_fixture_polyPropLam (reflect : Bool) (n : Nat) :
    CovPFixtureAt reflect eqEnvT n [] EnvT.bot
      covXPolyPropLam covXPolyPropLam covXPolyPropLamTy
      (.lam [([], .prop)]) covYPolyPropCode :=
  covP_fixture_of_Y reflect (covP_transport_polyPropCode reflect) (covZ_fixture_polyPropLam n)

theorem covP_fixture_alias_extension (reflect : Bool) (n : Nat) :
    ∃ A B,
      RelSubstAtCovY (C2 eqEnvT) (ctxModelT_approxTK eqEnvT n) (WhStepCK2 eqEnvT n)
        n eqGapCtx (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (EnvT.cons (demandT [CptT.pi .bot []]) EnvT.bot)
        (SubstT.cons idPiProp SubstT.id) (SubstT.cons idPiProp SubstT.id)
        (.assumption (eqGapDirectAlias A B) :: eqGapCtx) ∧
      CovPFixtureAt reflect eqEnvT n eqGapCtx EnvT.bot idPiProp idPiProp
        (eqGapDirectAlias A B) (.pi .bot []) .prop := by
  obtain ⟨A, B, hs, h⟩ := covZ_fixture_alias_extension n
  exact ⟨A, B, hs, covP_fixture_of_Y reflect (covP_transport_prop reflect) h⟩

theorem covP_fixture_nat_coverage_shape (reflect : Bool) (n : Nat) :
    (∃ d g, covYNatArrowCode = .pi d g) ∧
    CovPActionCoverage natEnvU (CTyCovP2 reflect natEnvU) (.spine 2 [])
      (.spine 0 []) [([], .spine 0 [])] ∧
    CovPFixtureAt reflect natEnvU n [] EnvT.bot
      (.const 2 []) (.const 2 []) (.pi (.const 0 []) (.const 0 []))
      (.spine 2 []) covYNatArrowCode := by
  obtain ⟨hs, hc, hj⟩ := covZ_fixture_nat_coverage_and_shape n
  refine ⟨hs, ?_, covP_fixture_of_Y reflect (covP_transport_natArrow reflect) hj⟩
  intro ds out ha hd
  rcases hc ds out ha (fun u hu => ctyCovP2_spine_iff_ctyCov2.mp (hd u hu)) with
    hb | ⟨row, hr, hsel⟩
  · exact Or.inl hb
  · exact Or.inr ⟨row, hr, hsel.1,
      ctyCovP2_of_ctyCov2 reflect out row.2 hsel.2⟩

theorem covP_fixture_eq_anchor (reflect : Bool) (n : Nat) :
    CovPFixtureAt reflect eqEnvT n eqGapCtx EnvT.bot idPiProp idPiProp
      (.sort .zero) (.pi .bot []) .prop :=
  covP_fixture_of_Y reflect (covP_transport_prop reflect) (covZ_fixture_eq_anchor n)

theorem covP_fixture_nat_anchor (reflect : Bool) (n : Nat) :
    CovPFixtureAt reflect natEnvU n [] EnvT.bot
      (.const 1 []) (.const 1 []) (.const 0 []) (.spine 1 []) (.spine 0 []) :=
  covP_fixture_of_Y reflect (covP_transport_spine reflect 0 []) (covZ_fixture_nat_anchor n)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_FIXTURES_ROOTS
#print axioms covP_transport_bot
#print axioms covP_transport_prop
#print axioms covP_transport_sort
#print axioms covP_transport_spine
#print axioms covP_transport_pi
#print axioms covP_transport_natArrow
#print axioms covP_transport_aliasCode
#print axioms covP_transport_polyPropCode
#print axioms CovPJointAt
#print axioms covP_joint_of_Y
#print axioms CovPFixtureAt
#print axioms covP_fixture_of_Y
#print axioms covP_fixture_natSucc_eta
#print axioms covP_fixture_alias_in_pi
#print axioms covP_fixture_polyPropLam
#print axioms covP_fixture_alias_extension
#print axioms covP_fixture_nat_coverage_shape
#print axioms covP_fixture_eq_anchor
#print axioms covP_fixture_nat_anchor
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_FIXTURES_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
