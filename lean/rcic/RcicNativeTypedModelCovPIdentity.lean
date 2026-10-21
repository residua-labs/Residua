import rcic.RcicNativeTypedModelCovPNeutral
import rcic.RcicNativeTypedModelCovZRigidId

/-!
# The rigid identity boundary survives positive typing and reflection

Two closed instantiations of the native polymorphic identity share the same
empty-demand compact actions. The hereditary clause requires every selected
row to work for both native instantiations. After two applications its one
result code must realize both `Sort 0` and `Pi (Sort 0) (Sort 0)`. Their exact
code shapes are incompatible. The proof uses only bottom inversion; it is
independent of the repaired proposition predicate and rigid typing gate.

All native arguments below have explicit derivations. In particular, this
proof does not demand an inhabitant of the fresh arbitrary type variable in
the outer binder-body context. No statement about cross-code transitivity
or a global common-code supplier is made. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovPAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit PiModelDeltaIotaTermAudit
open TypedModelAudit TypedModelAudit.TypingFin TypedModelKAudit ReadbackCK2Audit
open TypedModelCovXAudit TypedModelCovRelAudit TypedModelCovNormCov2Audit
open TypedModelCovYAudit TypedModelCovZMeasureAudit

def covPPropArrow : Expr Nat := .pi (.sort .zero) (.sort .zero)

def covPPropArrowId : Expr Nat := .lam (.sort .zero) (.bvar 0)

/-- The second type argument lives in the exact same native universe as
`Sort 0`; its universe equation has an explicit native conversion. -/
def covPPropArrow_hasTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ covPPropArrow (.sort (.succ .zero)) :=
  .conv Γ covPPropArrow (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.succ .zero)) (.succ (.imax (.succ .zero) (.succ .zero)))
    (.pi Γ (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
      (.sort Γ .zero) (.sort (.assumption (.sort .zero) :: Γ) .zero))
    (.sorts Γ (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun _ => rfl))

def covPPropArrowId_hasTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ covPPropArrowId covPPropArrow :=
  .lam Γ (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
    (.sort Γ .zero)
    (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)

/-- Two actual native type arguments and two actual native term arguments.
The first term is the closed proposition `forall P : Prop, P`, used as an
element of the universe Prop; no proof of that proposition is assumed. -/
theorem covP_identity_arguments_control (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Nonempty (HasTyT E n Γ (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT E n Γ covPPropArrow (.sort (.succ .zero))) ∧
    Nonempty (HasTyT E n Γ idPiProp (.sort .zero)) ∧
    Nonempty (HasTyT E n Γ covPPropArrowId covPPropArrow) :=
  ⟨⟨.sort Γ .zero⟩, ⟨covPPropArrow_hasTy E n Γ⟩,
    ⟨hasTyT_idPiProp_ctx E n Γ⟩, ⟨covPPropArrowId_hasTy E n Γ⟩⟩

variable {E : ResolvedEnv} {T : CptT → CptT → Prop} {Rel : CovPDemandRelation}

/-- Every code fails for any non-bottom rigid observation at the native
polymorphic identity type, even with completely arbitrary repaired typing
and demand relations, provided bottom still types only bottom. -/
theorem covP_not_hereditary_identity_spine
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat)
    (Γ : LCtx) (ρ : EnvT) (r : Nat) (us : List CptT) :
    ∀ a, ¬ HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
      (WhStepCK2 E n) n Γ ρ cexPolyIdTy (.spine r us) a := by
  intro a h
  change HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
    (WhStepCK2 E n) n Γ ρ
    (.pi (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))) (.spine r us) a at h
  obtain ⟨b, hb⟩ := covP_hereditary_empty_pi_step hbot n h
  have h₀ := (hb (.sort .zero) (.sort Γ .zero)).2
  have h₁ := (hb covPPropArrow (covPPropArrow_hasTy E n Γ)).2
  change HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
    (WhStepCK2 E n) n Γ ρ (.pi (.sort .zero) (.sort .zero))
    (.spine r (us ++ [.bot])) b at h₀
  change HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK E n)
    (WhStepCK2 E n) n Γ ρ (.pi covPPropArrow covPPropArrow)
    (.spine r (us ++ [.bot])) b at h₁
  obtain ⟨d, g, rfl⟩ := covP_hereditary_pi_code hbot n
    (fun he => CptT.noConfusion he) h₀
  rw [HereditaryCovRealizationPAt.eq_def] at h₀ h₁
  rcases h₀.2 with hzero | ⟨D₀, B₀, hr₀, hc₀, ha₀⟩
  · exact CptT.noConfusion hzero
  · have he₀ := redR_of_normal (normalR_piCK2 Γ (.sort .zero) (.sort .zero)) hr₀
    obtain ⟨rfl, rfl⟩ := Expr.pi.inj he₀
    rcases h₁.2 with hzero | ⟨D₁, B₁, hr₁, _, ha₁⟩
    · exact CptT.noConfusion hzero
    · have he₁ := redR_of_normal (normalR_piCK2 Γ covPPropArrow covPPropArrow) hr₁
      obtain ⟨rfl, rfl⟩ := Expr.pi.inj he₁
      have hact : CovXCompactAction E (.spine r (us ++ [.bot])) []
          (.spine r ((us ++ [.bot]) ++ [.bot])) := AppCptT.appSpine (.bot _ _)
      have hnb : (CptT.spine r ((us ++ [.bot]) ++ [.bot])) ≠ .bot :=
        fun he => CptT.noConfusion he
      rcases hc₀ [] _ hact (fun u hu => (List.not_mem_nil u hu).elim) with
        hz | ⟨row, hrow, hsel⟩
      · exact hnb hz
      · have hN₀ := hasTyT_idPiProp_ctx E n Γ
        have hN₁ := covPPropArrowId_hasTy E n Γ
        have hs := (ha₀ [] _ hact hnb row hrow hsel idPiProp idPiProp hN₀ hN₀
          ⟨.refl _ _ _ hN₀⟩ (fun u hu => (List.not_mem_nil u hu).elim)).2.2.1
        have hp := (ha₁ [] _ hact hnb row hrow hsel covPPropArrowId covPPropArrowId
          hN₁ hN₁ ⟨.refl _ _ _ hN₁⟩
          (fun u hu => (List.not_mem_nil u hu).elim)).2.2.1
        exact covP_not_hereditary_sort_pi_same_code hbot n hnb hs hp

/-- Both complete applications are natively typed and have exactly the
same compact observation after two empty-demand actions. -/
theorem covP_rigidId_two_application_control (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    Nonempty (HasTyT covZRigidIdEnv n Γ
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.sort .zero)) ∧
    Nonempty (HasTyT covZRigidIdEnv n Γ
      (.app (.app (.const 0 []) covPPropArrow) covPPropArrowId) covPPropArrow) ∧
    ApproxTK covZRigidIdEnv n Γ ρ
      (.app (.app (.const 0 []) (.sort .zero)) idPiProp) (.spine 0 [.bot, .bot]) ∧
    ApproxTK covZRigidIdEnv n Γ ρ
      (.app (.app (.const 0 []) covPPropArrow) covPPropArrowId)
      (.spine 0 [.bot, .bot]) := by
  have h₀ : HasTyT covZRigidIdEnv n Γ (.app (.const 0 []) (.sort .zero))
      (.pi (.sort .zero) (.sort .zero)) :=
    .app Γ (.const 0 []) (.sort .zero) (.sort (.succ .zero))
      (.pi (.bvar 0) (.bvar 1)) (covZRigidIdHead_hasTy n Γ) (.sort Γ .zero)
  have h₁ : HasTyT covZRigidIdEnv n Γ (.app (.const 0 []) covPPropArrow)
      (.pi covPPropArrow covPPropArrow) :=
    .app Γ (.const 0 []) covPPropArrow (.sort (.succ .zero))
      (.pi (.bvar 0) (.bvar 1)) (covZRigidIdHead_hasTy n Γ)
      (covPPropArrow_hasTy covZRigidIdEnv n Γ)
  exact ⟨⟨.app Γ _ idPiProp (.sort .zero) (.sort .zero) h₀
      (hasTyT_idPiProp_ctx covZRigidIdEnv n Γ)⟩,
    ⟨.app Γ _ covPPropArrowId covPPropArrow covPPropArrow h₁
      (covPPropArrowId_hasTy covZRigidIdEnv n Γ)⟩,
    .appSpine (.appSpine (covZRigidIdHead_observed n Γ ρ)
      (.bot Γ ρ (.sort .zero))) (.bot Γ ρ idPiProp),
    .appSpine (.appSpine (covZRigidIdHead_observed n Γ ρ)
      (.bot Γ ρ covPPropArrow)) (.bot Γ ρ covPPropArrowId)⟩

/-- The concrete declaration type has an existing lambda inhabitant over
the empty environment. The environment, context, head typing, conversion,
non-bottom observation and baseline relation are all actual inhabitants.
The new target still has no type-code witness for any repaired `T` with
bottom inversion, independently of the chosen demand relation. -/
theorem covP_rigidId_control (T : CptT → CptT → Prop) (Rel : CovPDemandRelation)
    (hbot : ∀ {u}, T u .bot → u = .bot) (n : Nat) :
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    Nonempty (ConvT covZRigidIdEnv n [] (.const 0 []) (.const 0 []) cexPolyIdTy) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n []
      (.const 0 []) (.const 0 []) cexPolyIdTy (.spine 0 []) .sort ∧
    (CptT.spine 0 []) ≠ .bot ∧
    ¬ ∃ b, HereditaryCovRealizationPAt T Rel (ctxModelT_approxTK covZRigidIdEnv n)
      (WhStepCK2 covZRigidIdEnv n) n [] EnvT.bot cexPolyIdTy (.spine 0 []) b :=
  ⟨⟨hasTyT_cexPolyId emptyEnv n⟩, ⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩,
    ⟨covZRigidIdHead_hasTy n []⟩, ⟨.refl _ _ _ (covZRigidIdHead_hasTy n [])⟩,
    covZRigidIdHead_observed n [] EnvT.bot, covZRigidIdHead_related_leaf n [],
    CptT.noConfusion,
    fun ⟨b, hb⟩ => covP_not_hereditary_identity_spine hbot n [] EnvT.bot 0 [] b hb⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_P_IDENTITY_ROOTS
#print axioms covPPropArrow
#print axioms covPPropArrowId
#print axioms covPPropArrow_hasTy
#print axioms covPPropArrowId_hasTy
#print axioms covP_identity_arguments_control
#print axioms covP_not_hereditary_identity_spine
#print axioms covP_rigidId_two_application_control
#print axioms covP_rigidId_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_P_IDENTITY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovPAudit
