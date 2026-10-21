import rcic.RcicNativeTypedModelCovZRigidPoly

/-!
# The same synthesis boundary at an inhabited rigid declaration

The stored type here is the imported polymorphic identity type. Its imported
lambda inhabitant is an explicit native derivation over the empty environment.
Consequently this control does not require a new object-language assumption
of an uninhabited type. The declaration is body-free so that its observation
is the ordinary rigid spine.

At an empty-demand action, the rigid typing gate and action coverage already
conflict: the selected declaration row is a proposition code, hence can type
only bottom. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin
open ReadbackCK2Audit TypedModelKAudit TypedModelKFragmentAudit
open TypedModelCovRelAudit TypedModelCovNormCov2Audit TypedModelCovXAudit
open TypedModelCovYAudit TypedModelCovZAudit

/-- Losing the observation of the type variable makes every observation of
its identity arrow proposition-shaped. This is a direct inversion of the
landed model; it makes no appeal to normalization or a typing lemma. -/
theorem covZ_polyId_body_observed_prop {E : ResolvedEnv} {ρ : EnvT} {a : CptT}
    (hρ : ∀ c, ρ 0 c → c = .bot)
    (h : ApproxT E ρ (.pi (.bvar 0) (.bvar 1)) a) : IsPropCT E a := by
  rcases approxT_pi_inv h with rfl | ⟨d, g, rfl, hd, hg⟩
  · exact .bot
  · have hdb : d = .bot := (approxT_bvar_inv hd).elim id (hρ d)
    subst d
    apply IsPropCT.pi .bot
    intro row hr
    have hrb := approxT_bvar_inv (hg row hr).2
    have he : row.2 = .bot := hrb.elim id (hρ row.2)
    rw [he]
    exact .bot

def covZRigidIdMember : CheckedMember := ⟨.axiomM, 0, cexPolyIdTy, none⟩

def covZRigidIdEnv : ResolvedEnv := extendEnv emptyEnv 0 covZRigidIdMember

def covZRigidIdTy_hasTy (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    HasTyT E n Γ cexPolyIdTy
      (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) :=
  .pi Γ (.sort (.succ .zero)) (.succ (.succ .zero))
    (.pi (.bvar 0) (.bvar 1)) (.imax (.succ .zero) (.succ .zero))
    (.sort Γ (.succ .zero))
    (.pi (.assumption (.sort (.succ .zero)) :: Γ) (.bvar 0) (.succ .zero)
      (.bvar 1) (.succ .zero) (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl))

def covZRigidIdEnvWfT : EnvWfT covZRigidIdEnv :=
  .axiom emptyEnv 0 cexPolyIdTy
    (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))
    .empty rfl (covZRigidIdTy_hasTy emptyEnv 0 [])
    (by intro k; simp [cexPolyIdTy, lift]) rfl

def covZRigidIdHead_hasTy (n : Nat) (Γ : LCtx) :
    HasTyT covZRigidIdEnv n Γ (.const 0 []) cexPolyIdTy := by
  simpa [covZRigidIdMember, instantiateLevels_nil] using
    (HasTyT.const (E := covZRigidIdEnv) (n := n) Γ 0 [] covZRigidIdMember
      rfl rfl rfl)

theorem covZRigidIdHead_rigid : RigidConst covZRigidIdEnv 0 := by
  intro m hm
  have he : m = covZRigidIdMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covZRigidIdHead_not_propCtor : ¬ PropCtorT covZRigidIdEnv 0 := by
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  have he : m = covZRigidIdMember := Option.some.inj hm.symm
  subst m
  exact MemberClass.noConfusion hctor

theorem covZRigidIdHead_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK covZRigidIdEnv n Γ ρ (.const 0 []) (.spine 0 []) :=
  ApproxTK.free (kFreeT_rigid_const covZRigidIdHead_rigid [])
    (.const ρ 0 [] covZRigidIdHead_rigid covZRigidIdHead_not_propCtor)

/-- The rigid gate itself is inhabited, at an imported actual observation of
the declared identity type. It is its conjunction with coverage that fails. -/
theorem covZRigidId_pi_gate :
    (C2 covZRigidIdEnv).ty (.spine 0 []) polyIdTyCpt01 := by
  change CTyCov2 covZRigidIdEnv (.spine 0 []) polyIdTyCpt01
  unfold polyIdTyCpt01
  rw [CTyCov2]
  refine ⟨not_isPropCT_polyIdTyCpt01 covZRigidIdEnv,
    covZRigidIdMember, [], rfl, covZRigidIdHead_rigid, rfl,
    fun i hi => (Nat.not_lt_zero i hi).elim, cexPolyIdTy, rfl, ?_⟩
  exact approxT_cexPolyIdTy_cpt01 covZRigidIdEnv EnvT.bot

/-- The empty-demand compact action is realized by a native typed application
to Prop. Neither the function observation nor its result is bottom. -/
theorem covZRigidId_application_control (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    Nonempty (HasTyT covZRigidIdEnv n Γ (.app (.const 0 []) (.sort .zero))
      (.pi (.sort .zero) (.sort .zero))) ∧
    ApproxTK covZRigidIdEnv n Γ ρ (.app (.const 0 []) (.sort .zero))
      (.spine 0 [.bot]) :=
  ⟨⟨.app Γ (.const 0 []) (.sort .zero) (.sort (.succ .zero))
      (.pi (.bvar 0) (.bvar 1)) (covZRigidIdHead_hasTy n Γ) (.sort Γ .zero)⟩,
    .appSpine (covZRigidIdHead_observed n Γ ρ) (.bot Γ ρ (.sort .zero))⟩

/-- No choice of rows repairs the empty-demand rigid action at this
declaration: coverage and the actual rigid typing gate are incompatible. -/
theorem covZRigidId_no_pi_gate_coverage (d : CptT) (g : List (List CptT × CptT))
    (ht : (C2 covZRigidIdEnv).ty (.spine 0 []) (.pi d g)) :
    ¬ CovYActionCoverage (C2 covZRigidIdEnv) (.spine 0 []) d g := by
  intro hcov
  change CTyCov2 covZRigidIdEnv (.spine 0 []) (.pi d g) at ht
  rw [CTyCov2] at ht
  obtain ⟨_, m, ls, hm, _, hlen, _, Tres, hTres, hobs⟩ := ht
  have he : m = covZRigidIdMember := Option.some.inj hm.symm
  subst m
  have hls : ls = [] := List.length_eq_zero.mp hlen
  subst ls
  have hTres' : Tres = cexPolyIdTy := (Option.some.inj hTres).symm
  subst Tres
  change ApproxT covZRigidIdEnv EnvT.bot cexPolyIdTy (.pi d g) at hobs
  rcases approxT_pi_inv hobs with hb | ⟨d', g', he, _, hrows⟩
  · exact CptT.noConfusion hb
  · cases he
    have hact : CovXCompactAction covZRigidIdEnv (.spine 0 []) []
        (.spine 0 [.bot]) := AppCptT.appSpine (.bot _ _)
    rcases hcov [] (.spine 0 [.bot]) hact (by simp) with hb | ⟨row, hr, hsel⟩
    · exact CptT.noConfusion hb
    · have hρ : ∀ c, (EnvT.cons (demandT row.1) EnvT.bot) 0 c → c = .bot := by
        intro c hc
        rcases hsel.1 c hc with hb | hm
        · exact hb
        · exact (List.not_mem_nil c hm).elim
      have hp := covZ_polyId_body_observed_prop hρ (hrows row hr).2
      exact CptT.noConfusion ((C2 covZRigidIdEnv).prop_bot hp hsel.2)

/-- Shape alignment cannot be satisfied by any newly synthesized Pi code,
for any endpoints. The compact typing and coverage conjuncts already clash. -/
theorem not_covZRigidId_core_pi (n : Nat) (Γ : LCtx) (x y A : Expr Nat)
    (d : CptT) (g : List (List CptT × CptT)) :
    ¬ LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n Γ
      x y A (.spine 0 []) (.pi d g) := by
  intro h
  exact covZRigidId_no_pi_gate_coverage d g
    (lrSCoreCovY_typing (C2 covZRigidIdEnv) h)
    (lrSCoreCovY_pi_coverage (C2 covZRigidIdEnv) h)

/-- The frozen non-Pi fallback nevertheless relates the native head at its
actual Pi type. This supplies prior relatedness for joint-code synthesis. -/
theorem covZRigidIdHead_related_leaf (n : Nat) (Γ : LCtx) :
    LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n Γ
      (.const 0 []) (.const 0 []) cexPolyIdTy (.spine 0 []) .sort := by
  apply lrSCoreCovY_of_old_leaf (C2 covZRigidIdEnv)
    (fun _ _ h => CptT.noConfusion h)
  · change CTyCov2 covZRigidIdEnv (.spine 0 []) .sort
    rw [CTyCov2]
    exact Or.inr (.spine 0 [])
  · rw [lrSCoreCov_spine_iff]
    have hn : NormalR (WhStepCK2 covZRigidIdEnv n) Γ (.const 0 []) := by
      intro e h
      rcases whStepCK2_ctx_or_saturated h with h | h
      · exact FamModelAudit.whStepCtx_const_opaque_false
          (rfl : covZRigidIdEnv.members 0 = some covZRigidIdMember) rfl [] h
      · obtain ⟨f, x, he⟩ := saturatedRecSource_is_app h
        exact Expr.noConfusion he
    refine ⟨covZRigidIdMember, [], [], [], [], rfl, .refl _, .refl _,
      hn, hn, ?_, by decide, by decide, .nil _, ?_⟩
    · trivial
    · intro _ hind
      exact MemberClass.noConfusion hind

theorem not_covZRigidId_hereditary_any_code (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ∀ b, ¬ HereditaryCovRealizationYAt (C2 covZRigidIdEnv)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      Γ ρ cexPolyIdTy (.spine 0 []) b := by
  intro b h
  rw [HereditaryCovRealizationYAt.eq_def] at h
  cases b with
  | bot => exact CptT.noConfusion ((C2 covZRigidIdEnv).bot_inv h.1)
  | pi d g =>
      rcases h.2 with hb | ⟨D, B, _, hc, _⟩
      · exact CptT.noConfusion hb
      · exact covZRigidId_no_pi_gate_coverage d g h.1 hc
  | prop | sort | lam g | spine r us =>
      rcases h.2 with hb | ⟨A₀, hr, _, ho⟩
      · exact CptT.noConfusion hb
      · have he := redR_of_normal
          (normalR_piCK2 (E := covZRigidIdEnv) (n := n) Γ
            (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))) hr
        subst A₀
        rcases approxTK_pi_inv ho with hb | ⟨a, f, he, _⟩
        · cases hb
        · cases he

/-- The stored type has an existing native lambda inhabitant over emptyEnv,
and its body-free declaration is admitted and observed non-trivially. -/
theorem covZRigidId_control (n : Nat) :
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    (CptT.spine 0 []) ≠ .bot ∧
    ¬ ∃ b, HereditaryCovRealizationYAt (C2 covZRigidIdEnv)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot cexPolyIdTy (.spine 0 []) b :=
  ⟨⟨hasTyT_cexPolyId emptyEnv n⟩, ⟨covZRigidIdEnvWfT⟩, ⟨.nil⟩,
    ⟨covZRigidIdHead_hasTy n []⟩, covZRigidIdHead_observed n [] EnvT.bot,
    CptT.noConfusion,
    fun ⟨b, hb⟩ => not_covZRigidId_hereditary_any_code n [] EnvT.bot b hb⟩

/-- The strengthened control retains an actual native lambda inhabitant of
the declaration type, an inhabited rigid Pi gate, and the existing relation. -/
theorem covZRigidId_full_control (n : Nat) :
    Nonempty (HasTyT emptyEnv n [] cexPolyId cexPolyIdTy) ∧
    Nonempty (EnvWfT covZRigidIdEnv) ∧
    Nonempty (CtxWfT covZRigidIdEnv n []) ∧
    Nonempty (HasTyT covZRigidIdEnv n [] (.const 0 []) cexPolyIdTy) ∧
    ApproxTK covZRigidIdEnv n [] EnvT.bot (.const 0 []) (.spine 0 []) ∧
    LRSCoreCovY (C2 covZRigidIdEnv) (WhStepCK2 covZRigidIdEnv n) n []
      (.const 0 []) (.const 0 []) cexPolyIdTy (.spine 0 []) .sort ∧
    (C2 covZRigidIdEnv).ty (.spine 0 []) polyIdTyCpt01 ∧
    (CptT.spine 0 []) ≠ .bot ∧
    ¬ ∃ b, HereditaryCovRealizationYAt (C2 covZRigidIdEnv)
      (ctxModelT_approxTK covZRigidIdEnv n) (WhStepCK2 covZRigidIdEnv n) n
      [] EnvT.bot cexPolyIdTy (.spine 0 []) b := by
  obtain ⟨hbody, hW, hΓ, ht, ho, hne, hno⟩ := covZRigidId_control n
  exact ⟨hbody, hW, hΓ, ht, ho, covZRigidIdHead_related_leaf n [],
    covZRigidId_pi_gate, hne, hno⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_Z_RIGID_ID_ROOTS
#print axioms covZ_polyId_body_observed_prop
#print axioms covZRigidIdMember
#print axioms covZRigidIdEnv
#print axioms covZRigidIdTy_hasTy
#print axioms covZRigidIdEnvWfT
#print axioms covZRigidIdHead_hasTy
#print axioms covZRigidIdHead_rigid
#print axioms covZRigidIdHead_not_propCtor
#print axioms covZRigidIdHead_observed
#print axioms covZRigidId_pi_gate
#print axioms covZRigidId_application_control
#print axioms covZRigidId_no_pi_gate_coverage
#print axioms not_covZRigidId_core_pi
#print axioms covZRigidIdHead_related_leaf
#print axioms not_covZRigidId_hereditary_any_code
#print axioms covZRigidId_control
#print axioms covZRigidId_full_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_Z_RIGID_ID_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovZMeasureAudit
