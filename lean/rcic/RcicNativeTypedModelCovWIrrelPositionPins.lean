import rcic.RcicNativeTypedModelCovWIrrelBoundary
import rcic.RcicNativeTypedModelCovWIrrelPositions
import rcic.RcicNativeTypedModelCovSProofAction

/-!
# Native proof-position certificates for the admitted controls

The certificates identify the actual declaration, its actual universe
vector, and the exact native telescope context.  They use native typing
derivations rather than a compact positivity test. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovPAudit TypedModelCovSAudit TypedModelCovUAudit
open TypedModelCovWAudit TypedModelCovWEtaAudit

/-- The family at reference 5 has one binder of native type `P`. -/
theorem covWIrrel_family_position (n : Nat) :
    CovWIrrelPosition covWIrrelEnv n 5 [] 0 []
      covWIrrelProp (.sort .zero) :=
  ⟨covWIrrelFamilyMember, rfl, rfl, rfl, rfl⟩

/-- `P : Sort 0` in the empty prefix context, so the family argument is
an actual declared proof position. -/
theorem covWIrrel_family_proof_position (n : Nat) :
    CovWIrrelProofPosition covWIrrelEnv n 5 [] 0 :=
  ⟨[], covWIrrelProp, .sort .zero, covWIrrel_family_position n,
    ⟨covWIrrel_prop_ty n []⟩⟩

theorem covWIrrel_family_erases (n : Nat) (u : CptT) :
    CovWIrrelSlot (CovWIrrelProofPosition covWIrrelEnv n 5 [] 0) u .bot :=
  .proof (covWIrrel_family_proof_position n) u

/-- Both native proofs have the same forced field output. -/
theorem covWIrrel_family_proofs_same_field (n : Nat) :
    CovWIrrelSlot (CovWIrrelProofPosition covWIrrelEnv n 5 [] 0)
      (.spine 4 []) .bot ∧
    CovWIrrelSlot (CovWIrrelProofPosition covWIrrelEnv n 5 [] 0)
      (.spine 8 []) .bot :=
  ⟨covWIrrel_family_erases n _, covWIrrel_family_erases n _⟩

/-- The old nonbottom proof-demand head's actual declared domain is True. -/
theorem covWIrrel_proofDemand_position (n : Nat) :
    CovWIrrelPosition covSProofFnEnv n 4 [] 0 []
      (.const 0 []) (.sort .zero) :=
  ⟨covSProofFnMember, rfl, rfl, rfl, rfl⟩

theorem covWIrrel_proofDemand_proof_position (n : Nat) :
    CovWIrrelProofPosition covSProofFnEnv n 4 [] 0 :=
  ⟨[], .const 0 [], .sort .zero, covWIrrel_proofDemand_position n,
    ⟨HasTyT.const [] 0 [] trueFamMember rfl rfl rfl⟩⟩

theorem covWIrrel_proofDemand_erases (n : Nat) (u : CptT) :
    CovWIrrelSlot (CovWIrrelProofPosition covSProofFnEnv n 4 [] 0) u .bot :=
  .proof (covWIrrel_proofDemand_proof_position n) u

/-- An already-bottom field is admitted independently of classification. -/
theorem covWIrrel_position_bot (E : ResolvedEnv) (n r : Nat)
    (ls : List Level) (i : Nat) :
    CovWIrrelSlot (CovWIrrelProofPosition E n r ls i) .bot .bot :=
  .bot

/-- The admitted Nat recursor is universe-polymorphic.  Its zero minor is
the motive applied to zero, under the preceding motive binder. -/
theorem covWIrrel_natRec_zeroMinor_position (n : Nat) (l : Level)
    (hl : levelBounded n l = true) :
    CovWIrrelPosition natEnvU n 3 [l] 1
      [.pi (.const 0 []) (.sort l)] natMzDom (.pi natMsTy natMajorTy) := by
  refine ⟨natRecMemberU, rfl, rfl, ?_, rfl⟩
  simp only [levelsBounded, hl, Bool.true_and]

def covWIrrel_natRec_zeroMinor_ty (n : Nat) (l : Level) :
    HasTyT natEnvU n
      (covWIrrelTelCtx [.pi (.const 0 []) (.sort l)])
      natMzDom (.sort l) :=
  .app _ (.bvar 0) (.const 1 []) (.const 0 []) (.sort l)
    (.bvar _ 0 _ rfl) (.const _ 1 [] natZeroMember rfl rfl rfl)

/-- The actual prefix context is natively well formed at every supplied level. -/
def covWIrrel_natRec_zeroMinor_ctx (n : Nat) (l : Level) :
    CtxWfT natEnvU n (covWIrrelTelCtx [.pi (.const 0 []) (.sort l)]) :=
  .assumption [] (.pi (.const 0 []) (.sort l))
    (.imax (.succ .zero) (.succ l)) .nil
    (.pi [] (.const 0 []) (.succ .zero) (.sort l) (.succ l)
      (.const [] 0 [] natFamMember rfl rfl rfl) (.sort _ l))

/-- Native level conversion, not a syntactic zero test, proves this position. -/
theorem covWIrrel_natRec_zeroMinor_proof_of_eqZero (n : Nat) (l : Level)
    (hl : levelBounded n l = true) (hz : eqN l .zero) :
    CovWIrrelProofPosition natEnvU n 3 [l] 1 := by
  refine ⟨[.pi (.const 0 []) (.sort l)], natMzDom, .pi natMsTy natMajorTy,
    covWIrrel_natRec_zeroMinor_position n l hl, ?_⟩
  exact ⟨.conv _ natMzDom (.sort l) (.sort .zero) (.succ l)
    (covWIrrel_natRec_zeroMinor_ty n l) (.sorts _ l .zero hz)⟩

theorem covWIrrel_natRec_zeroMinor_proof_zero (n : Nat) :
    CovWIrrelProofPosition natEnvU n 3 [.zero] 1 :=
  covWIrrel_natRec_zeroMinor_proof_of_eqZero n .zero rfl (fun _ => rfl)

/-- A nonliteral level containing an actual parameter is also classified
correctly when its native universe equality is zero. -/
theorem covWIrrel_natRec_zeroMinor_proof_imax :
    CovWIrrelProofPosition natEnvU 1 3 [.imax (.param 0) .zero] 1 :=
  covWIrrel_natRec_zeroMinor_proof_of_eqZero 1 (.imax (.param 0) .zero)
    rfl (fun _ => rfl)

/-- The positive universe test uses the admitted environment and its actual
native declaration instance as well as the well-formed prefix context. -/
theorem covWIrrel_natRec_zeroMinor_universe_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧
    Nonempty (HasTyT natEnvU n [] (.const 3 [.zero])
      (instantiateLevels [.zero] natRecMemberU.mtype)) ∧
    Nonempty (CtxWfT natEnvU n
      (covWIrrelTelCtx [.pi (.const 0 []) (.sort .zero)])) ∧
    CovWIrrelProofPosition natEnvU n 3 [.zero] 1 :=
  ⟨⟨natEnvUWfT⟩, ⟨.const [] 3 [.zero] natRecMemberU rfl rfl rfl⟩,
    ⟨covWIrrel_natRec_zeroMinor_ctx n .zero⟩,
    covWIrrel_natRec_zeroMinor_proof_zero n⟩

/-! ## Primitive non-proof certificates from explicit native sort separation

These results do not replace native sort separation with a selected positive
sort witness.  The exact required sort-separation implications remain visible
arguments.  The first two definitions only strip actual native conversion
constructors, and introduce no assumptions about typing uniqueness.
-/

/-- A constant's native typing differs from its declared type only through
the conversion constructors actually present in that typing derivation. -/
def covWIrrel_const_type_chain {E : ResolvedEnv} {n r : Nat}
    {ls : List Level} {m : CheckedMember} (hres : E.members r = some m) :
    {Γ : LCtx} → {A : Expr Nat} → HasTyT E n Γ (.const r ls) A →
      TyConvT E n Γ (instantiateLevels ls m.mtype) A
  | Γ, _, .const _ _ _ m' hres' _ _ => by
      have hm : m' = m := Option.some.inj (hres'.symm.trans hres)
      subst m'
      exact .refl Γ _
  | Γ, _, .conv _ _ A B u ht hc =>
      .trans Γ _ A B (covWIrrel_const_type_chain hres ht) (.of Γ A B u hc)

/-- A Pi typing exposes its actual formation sort before the outer native
conversion chain.  This returns the actual native subderivations. -/
def covWIrrel_pi_type_chain {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {D B : Expr Nat} :
    {A : Expr Nat} → HasTyT E n Γ (.pi D B) A →
      Σ u v : Level, HasTyT E n Γ D (.sort u) ×
        HasTyT E n (.assumption D :: Γ) B (.sort v) ×
        TyConvT E n Γ (.sort (.imax u v)) A
  | _, .pi _ _ u _ v hD hB =>
      ⟨u, v, hD, hB, .refl Γ (.sort (.imax u v))⟩
  | _, .conv _ _ A A' u ht hc => by
      obtain ⟨v, w, hD, hB, hchain⟩ := covWIrrel_pi_type_chain ht
      exact ⟨v, w, hD, hB,
        .trans Γ (.sort (.imax v w)) A A' hchain (.of Γ A A' u hc)⟩

/-- An extension retaining the native Nat declaration has no Prop typing of
Nat, conditional only on the displayed native sort-separation implication. -/
theorem covWIrrel_nat_notProp_of_sortSeparation {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (hNat : E.members 0 = some natFamMember)
    (hSort : ∀ {u v : Level},
      TyConvT E n Γ (.sort u) (.sort v) → eqN u v) :
    ¬ Nonempty (HasTyT E n Γ (.const 0 []) (.sort .zero)) := by
  rintro ⟨ht⟩
  have hc : TyConvT E n Γ (.sort (.succ .zero)) (.sort .zero) :=
    covWIrrel_const_type_chain hNat ht
  have hbad : (some 1 : Option Nat) = some 0 :=
    hSort hc (fun _ => none)
  cases hbad

/-- The native Nat arrow requires sort separation in precisely the outer
context and its one Nat-binder extension. -/
theorem covWIrrel_natArrow_notProp_of_sortSeparation {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (hNat : E.members 0 = some natFamMember)
    (hSort : ∀ {u v : Level},
      TyConvT E n Γ (.sort u) (.sort v) → eqN u v)
    (hSortBody : ∀ {u v : Level},
      TyConvT E n (.assumption (.const 0 []) :: Γ) (.sort u) (.sort v) →
        eqN u v) :
    ¬ Nonempty (HasTyT E n Γ (.pi (.const 0 []) (.const 0 [])) (.sort .zero)) := by
  rintro ⟨ht⟩
  obtain ⟨u, v, hu, hv, hchain⟩ := covWIrrel_pi_type_chain ht
  have huc : TyConvT E n Γ (.sort (.succ .zero)) (.sort u) :=
    covWIrrel_const_type_chain hNat hu
  have hvc : TyConvT E n (.assumption (.const 0 []) :: Γ)
      (.sort (.succ .zero)) (.sort v) :=
    covWIrrel_const_type_chain hNat hv
  have heu : eval (fun _ => none) u = some 1 :=
    (hSort huc (fun _ => none)).symm
  have hev : eval (fun _ => none) v = some 1 :=
    (hSortBody hvc (fun _ => none)).symm
  have hbad : (some 1 : Option Nat) = some 0 := by
    simpa [eval, heu, hev] using hSort hchain (fun _ => none)
  cases hbad

theorem covWIrrel_position_nonproof_of_notProp {E : ResolvedEnv} {n r i : Nat}
    {ls : List Level} {ds : List (Expr Nat)} {D B : Expr Nat}
    (hp : CovWIrrelPosition E n r ls i ds D B)
    (hn : ¬ Nonempty (HasTyT E n (covWIrrelTelCtx ds) D (.sort .zero))) :
    ¬ CovWIrrelProofPosition E n r ls i :=
  fun h => hn ((covWIrrel_proofPosition_iff hp).mp h)

theorem covWIrrel_natSucc_position {E : ResolvedEnv} (n : Nat)
    (hs : E.members 2 = some natSuccMember) :
    CovWIrrelPosition E n 2 [] 0 [] (.const 0 []) (.const 0 []) :=
  ⟨natSuccMember, hs, rfl, rfl, rfl⟩

/-- A directly usable local certificate for the successor's sole argument.
No global typing uniqueness premise is hidden in this statement. -/
theorem covWIrrel_natSucc_nonproof_of_sortSeparation {E : ResolvedEnv} {n : Nat}
    (hNat : E.members 0 = some natFamMember)
    (hs : E.members 2 = some natSuccMember)
    (hSort : ∀ {u v : Level},
      TyConvT E n [] (.sort u) (.sort v) → eqN u v) :
    ¬ CovWIrrelProofPosition E n 2 [] 0 :=
  covWIrrel_position_nonproof_of_notProp (covWIrrel_natSucc_position n hs)
    (covWIrrel_nat_notProp_of_sortSeparation hNat hSort)

/-- Any declared Nat-arrow domain has an explicit conditional non-proof
certificate, including such declarations in admitted Nat-environment extensions. -/
theorem covWIrrel_natArrowPosition_nonproof_of_sortSeparation
    {E : ResolvedEnv} {n r : Nat} {ls : List Level} {B : Expr Nat}
    (hp : CovWIrrelPosition E n r ls 0 []
      (.pi (.const 0 []) (.const 0 [])) B)
    (hNat : E.members 0 = some natFamMember)
    (hSort : ∀ {u v : Level},
      TyConvT E n [] (.sort u) (.sort v) → eqN u v)
    (hSortBody : ∀ {u v : Level},
      TyConvT E n [.assumption (.const 0 [])] (.sort u) (.sort v) → eqN u v) :
    ¬ CovWIrrelProofPosition E n r ls 0 :=
  covWIrrel_position_nonproof_of_notProp hp
    (covWIrrel_natArrow_notProp_of_sortSeparation hNat hSort hSortBody)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_POSITION_PINS_ROOTS
#print axioms covWIrrel_family_position
#print axioms covWIrrel_family_proof_position
#print axioms covWIrrel_family_erases
#print axioms covWIrrel_family_proofs_same_field
#print axioms covWIrrel_proofDemand_position
#print axioms covWIrrel_proofDemand_proof_position
#print axioms covWIrrel_proofDemand_erases
#print axioms covWIrrel_position_bot
#print axioms covWIrrel_natRec_zeroMinor_position
#print axioms covWIrrel_natRec_zeroMinor_ty
#print axioms covWIrrel_natRec_zeroMinor_ctx
#print axioms covWIrrel_natRec_zeroMinor_proof_of_eqZero
#print axioms covWIrrel_natRec_zeroMinor_proof_zero
#print axioms covWIrrel_natRec_zeroMinor_proof_imax
#print axioms covWIrrel_natRec_zeroMinor_universe_control
#print axioms covWIrrel_const_type_chain
#print axioms covWIrrel_pi_type_chain
#print axioms covWIrrel_nat_notProp_of_sortSeparation
#print axioms covWIrrel_natArrow_notProp_of_sortSeparation
#print axioms covWIrrel_position_nonproof_of_notProp
#print axioms covWIrrel_natSucc_position
#print axioms covWIrrel_natSucc_nonproof_of_sortSeparation
#print axioms covWIrrel_natArrowPosition_nonproof_of_sortSeparation
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_POSITION_PINS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
