import rcic.RcicNativeTypedModelCovTData
import rcic.RcicNativeTypedModelCovSOperators

/-!
# A type-valued Nat recursor with a non-spine observation

The native type below is a saturated `Nat.rec` on a local Nat assumption.
It is CK2-normal and has a constant head. Its actual model observation is
`.prop`, obtained from the semantic successor observation of that assumption.
Thus the compact shape is not the native head shape, even with all native
and finite-joint valuation premises supplied.

The extended context adds an assumption of this type. That actual native
term observes `pi bot []`, typed at the same observed `.prop` type code.
The inherited `covSRigidRel` rejects this term observation; the total unknown
relation accepts it. This is a control on that particular inherited rigid
leaf, not failure of head readback or impossibility of every provenance
interpretation. No native proposition/sort exclusivity is assumed or proved.
The parameter `n` is the native level-parameter arity. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit
open TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovQAudit TypedModelCovRAudit TypedModelCovSAudit

def covTRecMotive : Expr Nat :=
  .lam (.const 0 []) (.sort (.succ .zero))

def covTRecMinorTy : Expr Nat :=
  .pi (.const 0 [])
    (.pi (.app covTRecMotive (.bvar 0))
      (.app covTRecMotive (.app (.const 2 []) (.bvar 1))))

/-- The dependent annotation is the actual motive application. The body
returns Prop and uses neither the predecessor nor the recursive result. -/
def covTRecMinor : Expr Nat :=
  .lam (.const 0 [])
    (.lam (.app covTRecMotive (.bvar 0)) (.sort .zero))

def covTRecTypeAt (i : Nat) : Expr Nat :=
  recCall (.const 3 [.succ (.succ .zero)])
    [covTRecMotive, .sort .zero, covTRecMinor] (.bvar i)

def covTRecMinorCode : CptT := .lam [([], .lam [([], .prop)])]

def covTRecMajorCode : CptT := .spine 2 [.bot]

def covTRecCtx : LCtx := [.assumption (.const 0 [])]

def covTRecEnv : EnvT
  | 0, c => c = covTRecMajorCode
  | _ + 1, c => c = .bot

def covTRecExtCtx : LCtx :=
  [.assumption (covTRecTypeAt 0), .assumption (.const 0 [])]

def covTRecExtEnv : EnvT
  | 0, c => c = covTProbe
  | 1, c => c = covTRecMajorCode
  | _ + 2, c => c = .bot

def covTRecMotive_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ covTRecMotive
      (.pi (.const 0 []) (.sort (.succ (.succ .zero)))) :=
  .lam Γ (.const 0 []) (.succ .zero) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) (hasTyT_natEnvU_nat n Γ) (.sort _ _)

def covTRecMotive_beta (n : Nat) (Γ : LCtx) (a : Expr Nat)
    (ha : HasTyT natEnvU n Γ a (.const 0 [])) :
    ConvT natEnvU n Γ (.app covTRecMotive a) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
  .beta Γ (.const 0 []) (.sort (.succ .zero)) a
    (.sort (.succ (.succ .zero))) (.succ .zero)
    (hasTyT_natEnvU_nat n Γ) (.sort _ _) ha

def covTRecProp_hasTy (n : Nat) (Γ : LCtx) (a : Expr Nat)
    (ha : HasTyT natEnvU n Γ a (.const 0 [])) :
    HasTyT natEnvU n Γ (.sort .zero) (.app covTRecMotive a) :=
  .conv Γ (.sort .zero) (.sort (.succ .zero)) (.app covTRecMotive a)
    (.succ (.succ .zero)) (.sort Γ .zero)
    (.symm _ _ _ _ (covTRecMotive_beta n Γ a ha))

def covTRecMinor_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT natEnvU n Γ covTRecMinor covTRecMinorTy := by
  refine .lam Γ (.const 0 []) (.succ .zero) _ _
    (hasTyT_natEnvU_nat n Γ) ?_
  refine .lam _ (.app covTRecMotive (.bvar 0)) (.succ (.succ .zero)) _ _ ?_ ?_
  · exact .app _ covTRecMotive (.bvar 0) (.const 0 [])
      (.sort (.succ (.succ .zero))) (covTRecMotive_hasTy n _)
      (.bvar _ 0 _ rfl)
  · apply covTRecProp_hasTy n _ (.app (.const 2 []) (.bvar 1))
    exact .app _ (.const 2 []) (.bvar 1) (.const 0 []) (.const 0 [])
      (hasTyT_natEnvU_succ n _) (.bvar _ 1 _ rfl)

/-- Native typing is supplied for any actual Nat variable, independently
of the semantic valuation used below. -/
def covTRecTypeAt_hasTy (n : Nat) (Γ : LCtx) (i : Nat)
    (hi : HasTyT natEnvU n Γ (.bvar i) (.const 0 [])) :
    HasTyT natEnvU n Γ (covTRecTypeAt i) (.sort (.succ .zero)) := by
  have h1 : HasTyT natEnvU n Γ
      (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive)
      (.pi (.app covTRecMotive (.const 1 []))
        (.pi covTRecMinorTy
          (.pi (.const 0 []) (.app covTRecMotive (.bvar 0))))) :=
    .app Γ _ _ _ _
      (.const Γ 3 [.succ (.succ .zero)] natRecMemberU rfl rfl rfl)
      (covTRecMotive_hasTy n Γ)
  have h2 : HasTyT natEnvU n Γ
      (.app (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive) (.sort .zero))
      (.pi covTRecMinorTy (.pi (.const 0 []) (.app covTRecMotive (.bvar 0)))) :=
    .app Γ _ _ _ _ h1
      (covTRecProp_hasTy n Γ (.const 1 []) (hasTyT_natEnvU_zero n Γ))
  have h3 : HasTyT natEnvU n Γ
      (.app (.app (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive)
        (.sort .zero)) covTRecMinor)
      (.pi (.const 0 []) (.app covTRecMotive (.bvar 0))) :=
    .app Γ _ _ _ _ h2 (covTRecMinor_hasTy n Γ)
  exact .conv Γ _ (.app covTRecMotive (.bvar i)) (.sort (.succ .zero))
    (.succ (.succ .zero)) (.app Γ _ _ _ _ h3 hi)
    (covTRecMotive_beta n Γ (.bvar i) hi)

def covTRecCtx_wf (n : Nat) : CtxWfT natEnvU n covTRecCtx :=
  .assumption [] (.const 0 []) (.succ .zero) .nil (hasTyT_natEnvU_nat n [])

def covTRecExtCtx_wf (n : Nat) : CtxWfT natEnvU n covTRecExtCtx :=
  .assumption covTRecCtx (covTRecTypeAt 0) (.succ .zero) (covTRecCtx_wf n)
    (covTRecTypeAt_hasTy n covTRecCtx 0 (.bvar _ 0 _ rfl))

def covTRecExt_y_hasTy (n : Nat) :
    HasTyT natEnvU n covTRecExtCtx (.bvar 0) (covTRecTypeAt 1) :=
  .bvar _ 0 _ rfl

theorem covTRecMinor_observed (ρ : EnvT) :
    ApproxT natEnvU ρ covTRecMinor covTRecMinorCode := by
  refine .lam (.bot _ _) ?_ ?_ ?_
  · intro row hrow c hc
    obtain rfl := List.mem_singleton.mp hrow
    exact (List.not_mem_nil _ hc).elim
  · exact ⟨([], .lam [([], .prop)]), List.mem_singleton_self _, CptT.noConfusion⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    refine .lam (.bot _ _) ?_ ?_ ?_
    · intro inner hinner c hc
      obtain rfl := List.mem_singleton.mp hinner
      exact (List.not_mem_nil _ hc).elim
    · exact ⟨([], .prop), List.mem_singleton_self _, CptT.noConfusion⟩
    · intro inner hinner
      obtain rfl := List.mem_singleton.mp hinner
      exact approxT_sort_code natEnvU _ .zero

/-- The existing admitted successor schema supplies a type-valued result.
Its actual minor observes both empty-demand lambda rows used by the schema. -/
theorem covTRec_const_observed (ρ : EnvT) :
    ApproxT natEnvU ρ (.const 3 [.succ (.succ .zero)])
      (curryStepT [[], [], [covTRecMinorCode], [covTRecMajorCode]] .prop) := by
  apply ApproxT.recursor (w := covWNatSucc) [.succ (.succ .zero)]
    not_propFamilyS_covWNatSucc
    (us_pre := [[], [], [covTRecMinorCode]]) (us_fields := [[]]) rfl rfl
  change ApproxT natEnvU
    (EnvT.pushArgs (([[], [], [covTRecMinorCode]] ++ [[]]).map demandT) EnvT.bot)
    (.app (.app (.bvar 1) (.bvar 0))
      (.app (.app (.app (.app (.const 3 [.succ (.succ .zero)]) (.bvar 3))
        (.bvar 2)) (.bvar 1)) (.bvar 0))) .prop
  apply ApproxT.app (s := ([], .prop))
  · apply ApproxT.app (s := ([], .lam [([], .prop)]))
    · exact .bvar (List.mem_singleton_self _)
    · exact List.mem_singleton_self _
    · intro c hc
      exact (List.not_mem_nil _ hc).elim
  · exact List.mem_singleton_self _
  · intro c hc
    exact (List.not_mem_nil _ hc).elim

theorem covTRecTypeAt_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) (i : Nat)
    (hi : ρ i covTRecMajorCode) :
    ApproxTK natEnvU n Γ ρ (covTRecTypeAt i) .prop := by
  apply ApproxTK.free (kFreeT_natEnvU _)
  have h1 : ApproxT natEnvU ρ
      (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive)
      (curryStepT [[], [covTRecMinorCode], [covTRecMajorCode]] .prop) :=
    .app (covTRec_const_observed ρ) (List.mem_singleton_self _)
      (fun _ h => (List.not_mem_nil _ h).elim)
  have h2 : ApproxT natEnvU ρ
      (.app (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive) (.sort .zero))
      (curryStepT [[covTRecMinorCode], [covTRecMajorCode]] .prop) :=
    .app h1 (List.mem_singleton_self _)
      (fun _ h => (List.not_mem_nil _ h).elim)
  have h3 : ApproxT natEnvU ρ
      (.app (.app (.app (.const 3 [.succ (.succ .zero)]) covTRecMotive)
        (.sort .zero)) covTRecMinor)
      (curryStepT [[covTRecMajorCode]] .prop) := by
    refine .app h2 (List.mem_singleton_self _) ?_
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact covTRecMinor_observed ρ
  refine .app h3 (List.mem_singleton_self _) ?_
  intro c hc
  obtain rfl := List.mem_singleton.mp hc
  exact .bvar hi

/-- Nat has no proposition-family K canon. This uses the admitted
environment's shared witness-reference theorem, independently of a major. -/
theorem covTRec_no_native (n : Nat) (Γ : LCtx) (a b : Expr Nat) :
    ¬ KNativeHead natEnvU n Γ a b := by
  intro h
  cases h with
  | intro hK hnc hindex hcommon =>
      rename_i w x
      have hd := natEnvU_witness_refs (fun _ _ h => h)
        w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
      have hp : piBody w.famMember.mtype = .sort .zero :=
        hK.elim (fun h => h.2.2) (fun h => h.1.2.2.1)
      rw [hd.1.2] at hp
      cases hp

/-- The native head is a normal constant spine. The semantic successor
observation of its major is not a native constructor-head equation. -/
theorem covTRecTypeAt_normal (n : Nat) (Γ : LCtx) (i : Nat)
    (hi : lookupValue Γ i = none) :
    NormalR (WhStepCK2 natEnvU n) Γ (covTRecTypeAt i) := by
  intro out hs
  generalize he : covTRecTypeAt i = source at hs
  cases hs with
  | ctx h =>
      exact not_isCtorSpine_bvar
        (whStepCtx_recCall_ctor natEnvUWfT
          (rfl : natEnvU.members 3 = some natRecMemberU) rfl
          (by decide) (he.symm ▸ h))
  | native h => exact covTRec_no_native n Γ _ _ h
  | recMajor _ _ _ _ _ h =>
      have hx := (recCall_const_inj he).2.2.2
      rw [← hx] at h
      exact normalR_bvarCK2 hi _ h
  | appHead h =>
      change Expr.app
        (foldApps (.const 3 [.succ (.succ .zero)])
          [covTRecMotive, .sort .zero, covTRecMinor]) (.bvar i) = _ at he
      have hf := (Expr.app.inj he).1
      rw [← hf] at h
      exact normalR_recPrefixCK2 natEnvUWfT
        (rfl : natEnvU.members 3 = some natRecMemberU) rfl Γ
        [.succ (.succ .zero)] [covTRecMotive, .sort .zero, covTRecMinor]
        (by decide) _ h

theorem covTRecTypeAt_head (n : Nat) (Γ : LCtx) (i : Nat) :
    RedR (WhStepCK2 natEnvU n) Γ (covTRecTypeAt i)
      (foldApps (.const 3 [.succ (.succ .zero)])
        [covTRecMotive, .sort .zero, covTRecMinor, .bvar i]) :=
  .refl _

theorem covTRecTypeAt_no_sort_read (n : Nat) (Γ : LCtx) (i : Nat)
    (hi : lookupValue Γ i = none) (l : Level) :
    ¬ RedR (WhStepCK2 natEnvU n) Γ (covTRecTypeAt i) (.sort l) := by
  intro h
  exact Expr.noConfusion (redR_of_normal (covTRecTypeAt_normal n Γ i hi) h)

theorem covTRecMajorCode_typed :
    CTyS natEnvU covTRecMajorCode (.spine 0 []) := by
  rw [CTyS]
  exact Or.inr ⟨⟨2, [.bot], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

theorem covTRec_env_typed (n : Nat) :
    EnvTypedFinAtT (ctxModelT_approxTK natEnvU n covTRecCtx)
      covTRecCtx covTRecEnv := by
  intro i A hA us hus
  cases i with
  | zero =>
      have he : A = .const 0 [] := (Option.some.inj hA).symm
      subst A
      refine ⟨.spine 0 [], ?_, ?_⟩
      · exact .free (kFreeT_natEnvU _) (.const _ 0 []
          rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)
      · intro c hc
        have he : c = covTRecMajorCode := hus c hc
        subst c
        exact covTRecMajorCode_typed
  | succ i => simp [covTRecCtx, lookupType] at hA

theorem covTRec_ctx_coherent (n : Nat) :
    CtxEnvM (ctxModelT_approxTK natEnvU n covTRecCtx) covTRecCtx covTRecEnv := by
  intro i v hv
  cases i with
  | zero => cases hv
  | succ i => simp [covTRecCtx, lookupValue] at hv

theorem covTRec_ext_env_typed (n : Nat) :
    EnvTypedFinAtT (ctxModelT_approxTK natEnvU n covTRecExtCtx)
      covTRecExtCtx covTRecExtEnv := by
  intro i A hA us hus
  cases i with
  | zero =>
      have he : A = covTRecTypeAt 1 := (Option.some.inj hA).symm
      subst A
      refine ⟨.prop, covTRecTypeAt_observed n _ _ 1 rfl, ?_⟩
      intro c hc
      have he : c = covTProbe := hus c hc
      subst c
      exact covTProbe_typed natEnvU
  | succ i =>
      cases i with
      | zero =>
          have he : A = .const 0 [] := (Option.some.inj hA).symm
          subst A
          refine ⟨.spine 0 [], ?_, ?_⟩
          · exact .free (kFreeT_natEnvU _) (.const _ 0 []
              rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)
          · intro c hc
            have he : c = covTRecMajorCode := hus c hc
            subst c
            exact covTRecMajorCode_typed
      | succ i => simp [covTRecExtCtx, lookupType] at hA

theorem covTRec_ext_ctx_coherent (n : Nat) :
    CtxEnvM (ctxModelT_approxTK natEnvU n covTRecExtCtx)
      covTRecExtCtx covTRecExtEnv := by
  intro i v hv
  cases i with
  | zero => cases hv
  | succ i =>
      cases i with
      | zero => cases hv
      | succ i => simp [covTRecExtCtx, lookupValue] at hv

theorem covTRec_ext_y_observed (n : Nat) :
    ApproxTK natEnvU n covTRecExtCtx covTRecExtEnv (.bvar 0) covTProbe :=
  .free (kFreeT_bvar natEnvU 0) (.bvar rfl)

theorem covTRec_rigid_rejects :
    ¬ covSRigidRel (.bvar 0) (.bvar 0) covTProbe := by
  rintro (h | ⟨r, us, h⟩)
  · exact CptT.noConfusion h
  · exact CptT.noConfusion h

theorem covTRec_unknown_accepts :
    covSTotalRel (.bvar 0) (.bvar 0) covTProbe := trivial

/-- The inherited Prop-universe membership accepts the same actual
observation. The rejected policy above is the rigid-data leaf. -/
theorem covTRec_prop_leaf_accepts :
    covRCodeRel natEnvU .prop (.bvar 0) (.bvar 0) covTProbe :=
  ctyCovQ_of_S (covTProbe_typed natEnvU)

/-- All premises for the type-valued head/compact mismatch hold in the
single Nat-assumption context. In particular head readback is positive. -/
theorem covTRec_type_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n covTRecCtx) ∧
    EnvTypedFinAtT (ctxModelT_approxTK natEnvU n covTRecCtx) covTRecCtx covTRecEnv ∧
    CtxEnvM (ctxModelT_approxTK natEnvU n covTRecCtx) covTRecCtx covTRecEnv ∧
    Nonempty (HasTyT natEnvU n covTRecCtx (covTRecTypeAt 0) (.sort (.succ .zero))) ∧
    Nonempty (ConvT natEnvU n covTRecCtx (covTRecTypeAt 0) (covTRecTypeAt 0)
      (.sort (.succ .zero))) ∧
    ApproxTK natEnvU n covTRecCtx covTRecEnv (.bvar 0) covTRecMajorCode ∧
    ApproxTK natEnvU n covTRecCtx covTRecEnv (covTRecTypeAt 0) .prop ∧
    NormalR (WhStepCK2 natEnvU n) covTRecCtx (covTRecTypeAt 0) ∧
    (∀ l, ¬ RedR (WhStepCK2 natEnvU n) covTRecCtx (covTRecTypeAt 0) (.sort l)) := by
  have ht := covTRecTypeAt_hasTy n covTRecCtx 0 (.bvar _ 0 _ rfl)
  exact ⟨⟨natEnvUWfT⟩, ⟨covTRecCtx_wf n⟩, covTRec_env_typed n,
    covTRec_ctx_coherent n, ⟨ht⟩, ⟨.refl _ _ _ ht⟩,
    .free (kFreeT_bvar natEnvU 0) (.bvar rfl),
    covTRecTypeAt_observed n _ _ 0 rfl, covTRecTypeAt_normal n _ 0 rfl,
    covTRecTypeAt_no_sort_read n _ 0 rfl⟩

/-- The rejected compact is an actual observation of a natively typed
term in the same well-formed, finite-joint typed, let-coherent context.
This does not select a new interpretation or assume a view supplier. -/
theorem covTRec_rigid_leaf_control (n : Nat) :
    Nonempty (EnvWfT natEnvU) ∧ Nonempty (CtxWfT natEnvU n covTRecExtCtx) ∧
    EnvTypedFinAtT (ctxModelT_approxTK natEnvU n covTRecExtCtx)
      covTRecExtCtx covTRecExtEnv ∧
    CtxEnvM (ctxModelT_approxTK natEnvU n covTRecExtCtx) covTRecExtCtx covTRecExtEnv ∧
    Nonempty (HasTyT natEnvU n covTRecExtCtx (covTRecTypeAt 1) (.sort (.succ .zero))) ∧
    Nonempty (HasTyT natEnvU n covTRecExtCtx (.bvar 0) (covTRecTypeAt 1)) ∧
    Nonempty (ConvT natEnvU n covTRecExtCtx (.bvar 0) (.bvar 0) (covTRecTypeAt 1)) ∧
    ApproxTK natEnvU n covTRecExtCtx covTRecExtEnv (covTRecTypeAt 1) .prop ∧
    ApproxTK natEnvU n covTRecExtCtx covTRecExtEnv (.bvar 0) covTProbe ∧
    CTyS natEnvU covTProbe .prop ∧ covTProbe ≠ .bot ∧
    NormalR (WhStepCK2 natEnvU n) covTRecExtCtx (covTRecTypeAt 1) ∧
    ¬ covSRigidRel (.bvar 0) (.bvar 0) covTProbe ∧
    covSTotalRel (.bvar 0) (.bvar 0) covTProbe :=
  ⟨⟨natEnvUWfT⟩, ⟨covTRecExtCtx_wf n⟩, covTRec_ext_env_typed n,
    covTRec_ext_ctx_coherent n,
    ⟨covTRecTypeAt_hasTy n _ 1 (.bvar _ 1 _ rfl)⟩,
    ⟨covTRecExt_y_hasTy n⟩, ⟨.refl _ _ _ (covTRecExt_y_hasTy n)⟩,
    covTRecTypeAt_observed n _ _ 1 rfl, covTRec_ext_y_observed n,
    covTProbe_typed natEnvU, covTProbe_nonbot, covTRecTypeAt_normal n _ 1 rfl,
    covTRec_rigid_rejects, covTRec_unknown_accepts⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_T_RECURSOR_ROOTS
#print axioms covTRecMotive
#print axioms covTRecMinorTy
#print axioms covTRecMinor
#print axioms covTRecTypeAt
#print axioms covTRecMinorCode
#print axioms covTRecMajorCode
#print axioms covTRecCtx
#print axioms covTRecEnv
#print axioms covTRecExtCtx
#print axioms covTRecExtEnv
#print axioms covTRecMotive_hasTy
#print axioms covTRecMotive_beta
#print axioms covTRecProp_hasTy
#print axioms covTRecMinor_hasTy
#print axioms covTRecTypeAt_hasTy
#print axioms covTRecCtx_wf
#print axioms covTRecExtCtx_wf
#print axioms covTRecExt_y_hasTy
#print axioms covTRecMinor_observed
#print axioms covTRec_const_observed
#print axioms covTRecTypeAt_observed
#print axioms covTRec_no_native
#print axioms covTRecTypeAt_normal
#print axioms covTRecTypeAt_head
#print axioms covTRecTypeAt_no_sort_read
#print axioms covTRecMajorCode_typed
#print axioms covTRec_env_typed
#print axioms covTRec_ctx_coherent
#print axioms covTRec_ext_env_typed
#print axioms covTRec_ext_ctx_coherent
#print axioms covTRec_ext_y_observed
#print axioms covTRec_rigid_rejects
#print axioms covTRec_unknown_accepts
#print axioms covTRec_prop_leaf_accepts
#print axioms covTRec_type_control
#print axioms covTRec_rigid_leaf_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_T_RECURSOR_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit
