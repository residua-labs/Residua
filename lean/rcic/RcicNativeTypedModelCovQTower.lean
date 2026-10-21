import rcic.RcicNativeTypedModelCovPIdentity

/-!
# Finite code descent cannot realize every native identity instance

The native argument may choose its own result code. Even that freedom is
insufficient if each empty-demand application must strictly decrease the
size of one finite compact code. Closed native types of arbitrarily large
Pi depth give the contradiction. Every type in the family is in Sort 1,
and every one has an explicit native inhabitant in every context.

The abstract descent property below mentions no proposition predicate,
row-selection order, exact leaf, or binder-body realization. An actual
hereditary interface must separately supply this property before the
boundary applies. No global fundamental theorem is asserted.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovQAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit
open TypedModelCovZMeasureAudit TypedModelCovPAudit

def covQArrowTower : Nat → Expr Nat
  | 0 => .sort .zero
  | k + 1 => .pi (.sort .zero) (covQArrowTower k)

/-- The base is a proposition used as an element of the universe Prop.
It does not assume that this proposition has a proof. -/
def covQArrowTowerWitness : Nat → Expr Nat
  | 0 => idPiProp
  | k + 1 => .lam (.sort .zero) (covQArrowTowerWitness k)

theorem covQArrowTower_lift (k cutoff amount : Nat) :
    lift cutoff amount (covQArrowTower k) = covQArrowTower k := by
  induction k generalizing cutoff with
  | zero => rfl
  | succ k ih => simp only [covQArrowTower, lift, ih]

theorem covQArrowTower_instantiate (k index : Nat) (N : Expr Nat) :
    instantiate index N (covQArrowTower k) = covQArrowTower k := by
  induction k generalizing index N with
  | zero => rfl
  | succ k ih => simp only [covQArrowTower, instantiate, ih]

theorem covQArrowTower_instantiate0 (k : Nat) (N : Expr Nat) :
    instantiate0 N (covQArrowTower k) = covQArrowTower k :=
  covQArrowTower_instantiate k 0 N

/-- One recursive native Pi derivation, with its displayed universe
conversion, constructs every type in the same universe. -/
def covQArrowTower_hasTy (E : ResolvedEnv) (n k : Nat) (Γ : LCtx) :
    HasTyT E n Γ (covQArrowTower k) (.sort (.succ .zero)) := by
  induction k generalizing Γ with
  | zero => exact .sort Γ .zero
  | succ k ih =>
      exact .conv Γ (covQArrowTower (k + 1))
        (.sort (.imax (.succ .zero) (.succ .zero)))
        (.sort (.succ .zero)) (.succ (.imax (.succ .zero) (.succ .zero)))
        (.pi Γ (.sort .zero) (.succ .zero) (covQArrowTower k) (.succ .zero)
          (.sort Γ .zero) (ih (.assumption (.sort .zero) :: Γ)))
        (.sorts Γ (.imax (.succ .zero) (.succ .zero)) (.succ .zero)
          (fun _ => rfl))

def covQArrowTowerWitness_hasTy (E : ResolvedEnv) (n k : Nat) (Γ : LCtx) :
    HasTyT E n Γ (covQArrowTowerWitness k) (covQArrowTower k) := by
  induction k generalizing Γ with
  | zero => exact hasTyT_idPiProp_ctx E n Γ
  | succ k ih =>
      exact .lam Γ (.sort .zero) (.succ .zero)
        (covQArrowTowerWitness k) (covQArrowTower k)
        (.sort Γ .zero) (ih (.assumption (.sort .zero) :: Γ))

theorem covQArrowTower_control (E : ResolvedEnv) (n k : Nat) (Γ : LCtx) :
    Nonempty (HasTyT E n Γ (covQArrowTower k) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT E n Γ (covQArrowTowerWitness k) (covQArrowTower k)) :=
  ⟨⟨covQArrowTower_hasTy E n k Γ⟩, ⟨covQArrowTowerWitness_hasTy E n k Γ⟩⟩

theorem covQ_identity_body_inst (k : Nat) :
    instantiate0 (covQArrowTower k) (.pi (.bvar 0) (.bvar 1)) =
      .pi (covQArrowTower k) (covQArrowTower k) := by
  simp [instantiate0, instantiate, covQArrowTower_lift]

/-- These are actual typed applications of the admitted identity head.
All tower instances have the same two-bottom rigid observation. -/
theorem covQ_identity_tower_application_control (n k : Nat)
    (Γ : LCtx) (ρ : EnvT) :
    Nonempty (HasTyT covZRigidIdEnv n Γ
      (.app (.app (.const 0 []) (covQArrowTower k)) (covQArrowTowerWitness k))
      (covQArrowTower k)) ∧
    ApproxTK covZRigidIdEnv n Γ ρ
      (.app (.app (.const 0 []) (covQArrowTower k)) (covQArrowTowerWitness k))
      (.spine 0 [.bot, .bot]) := by
  have ht : HasTyT covZRigidIdEnv n Γ (.app (.const 0 []) (covQArrowTower k))
      (.pi (covQArrowTower k) (covQArrowTower k)) := by
    simpa only [covQ_identity_body_inst] using
      (HasTyT.app Γ (.const 0 []) (covQArrowTower k) (.sort (.succ .zero))
        (.pi (.bvar 0) (.bvar 1)) (covZRigidIdHead_hasTy n Γ)
        (covQArrowTower_hasTy covZRigidIdEnv n k Γ))
  have hresult : HasTyT covZRigidIdEnv n Γ
      (.app (.app (.const 0 []) (covQArrowTower k)) (covQArrowTowerWitness k))
      (covQArrowTower k) := by
    simpa only [covQArrowTower_instantiate0] using
      (HasTyT.app Γ (.app (.const 0 []) (covQArrowTower k))
        (covQArrowTowerWitness k) (covQArrowTower k) (covQArrowTower k) ht
        (covQArrowTowerWitness_hasTy covZRigidIdEnv n k Γ))
  exact ⟨⟨hresult⟩,
    .appSpine (.appSpine (covZRigidIdHead_observed n Γ ρ)
      (.bot Γ ρ (covQArrowTower k))) (.bot Γ ρ (covQArrowTowerWitness k))⟩

abbrev CovQRealization := Expr Nat → CptT → CptT → Prop

/-- The result code is chosen *after* the actual native argument. It need
not be an existing row output; only its strict size decrease is required.
This is a necessary property to measure, not a supplied realization. -/
def CovQEmptyStep (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (F : CovQRealization) : Prop :=
  ∀ D B r us a, F (.pi D B) (.spine r us) a →
    ∀ N, HasTyT E n Γ N D →
      ∃ b, sizeOf b < sizeOf a ∧
        F (instantiate0 N B) (.spine r (us ++ [.bot])) b

/-- Each genuine Pi layer consumes at least one unit of the code bound.
The empty action is instantiated by an actual native argument at each
step. The statement does not assume anything about the base leaf. -/
theorem covQ_tower_code_lower_bound {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {F : CovQRealization} (hstep : CovQEmptyStep E n Γ F)
    (k r : Nat) (us : List CptT) (a : CptT)
    (h : F (covQArrowTower k) (.spine r us) a) : k ≤ sizeOf a := by
  induction k generalizing r us a with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hp : F (.pi (.sort .zero) (covQArrowTower k)) (.spine r us) a := h
      obtain ⟨b, hba, hb⟩ := hstep (.sort .zero) (covQArrowTower k) r us a hp
        idPiProp (hasTyT_idPiProp_ctx E n Γ)
      have hb' : F (covQArrowTower k) (.spine r (us ++ [.bot])) b := by
        simpa only [covQArrowTower_instantiate0] using hb
      have hk := ih r (us ++ [.bot]) b hb'
      omega

/-- No single finite code can support all native instances of the
polymorphic identity under strict empty-action code descent. The argument
may choose a fresh code at every step, so changing finite-row quantifier
order does not avoid this boundary. -/
theorem covQ_no_finite_descending_identity {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {F : CovQRealization} (hstep : CovQEmptyStep E n Γ F)
    (r : Nat) (us : List CptT) (a : CptT) :
    ¬ F cexPolyIdTy (.spine r us) a := by
  intro h
  change F (.pi (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1)))
    (.spine r us) a at h
  obtain ⟨b, hba, hb⟩ := hstep (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))
    r us a h (covQArrowTower (sizeOf a))
    (covQArrowTower_hasTy E n (sizeOf a) Γ)
  have hb' : F (.pi (covQArrowTower (sizeOf a)) (covQArrowTower (sizeOf a)))
      (.spine r (us ++ [.bot])) b := by
    simpa only [covQ_identity_body_inst] using hb
  obtain ⟨c, hcb, hc⟩ := hstep (covQArrowTower (sizeOf a))
    (covQArrowTower (sizeOf a)) r (us ++ [.bot]) b hb'
    (covQArrowTowerWitness (sizeOf a))
    (covQArrowTowerWitness_hasTy E n (sizeOf a) Γ)
  have hc' : F (covQArrowTower (sizeOf a))
      (.spine r ((us ++ [.bot]) ++ [.bot])) c := by
    simpa only [covQArrowTower_instantiate0] using hc
  have hdepth := covQ_tower_code_lower_bound hstep (sizeOf a) r
    ((us ++ [.bot]) ++ [.bot]) c hc'
  omega

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Q_TOWER_ROOTS
#print axioms covQArrowTower
#print axioms covQArrowTowerWitness
#print axioms covQArrowTower_lift
#print axioms covQArrowTower_instantiate
#print axioms covQArrowTower_instantiate0
#print axioms covQArrowTower_hasTy
#print axioms covQArrowTowerWitness_hasTy
#print axioms covQArrowTower_control
#print axioms covQ_identity_body_inst
#print axioms covQ_identity_tower_application_control
#print axioms CovQRealization
#print axioms CovQEmptyStep
#print axioms covQ_tower_code_lower_bound
#print axioms covQ_no_finite_descending_identity
-- END RCIC_NATIVE_TYPED_MODEL_COV_Q_TOWER_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovQAudit
