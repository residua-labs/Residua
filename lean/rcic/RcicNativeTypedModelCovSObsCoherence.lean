import rcic.RcicNativeTypedModelCovSCoherence
import rcic.RcicNativeTypedModelCovSSubstitutionBoundary

/-!
# Restricted coherence of the actual observed-compact interpreter

At one fixed raw domain compact and one fixed candidate valuation, adding
outer Pi output rows strengthens the interpreter's finite intersection.
The resulting pointwise inclusion runs from the larger row list to the
smaller one. The domain and every retained child compact are unchanged.
This is a law of the actual decoder and interpreter, not a compact order,
native type-conversion theorem, or arbitrary observation-coherence theorem.

The proof preserves the strict value-row gate and both ordinary action
obligations. It also preserves the actual S-candidate forall clause. Type
row demand lists are retained in the templates, but this interpreter's row
operation uses their output constraints without demand-based selection.

The final control is independent of these Pi policies. In the actual
context `x : A, A : Sort 2`, one finite-joint typed and let-coherent
valuation observes A at both `.prop` and `.sort`, and x at `.prop`.
Environment typing uses A's `.sort` observation for x's finite demands.
The independently selected `.prop` type observation rejects x's actual
compact, while the bottom type observation accepts it. This is a bottom
versus nonbottom boundary; SubstitutionBoundary separately exhibits two
nonbottom observations of one closed native type.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit TypedModelKFragmentAudit ReadbackCK2Audit
open TypedModelCovXAudit TypedModelCovRAudit

/-- With its domain fixed, the strict arrow preserves codomain inclusion,
including the support of every stored value row. -/
theorem covSObs_arrow_codomain_mono
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {p : Bool} {Dty : Expr Nat}
    {D B B' : CovSRel} (hB : CovSRelIncl B B') :
    CovSRelIncl (covRArrow E n Γ p Dty D B)
      (covRArrow E n Γ p Dty D B') := by
  intro x y c h
  refine ⟨h.1, ?_, h.2.2.1, ?_, ?_⟩
  · cases c with
    | lam rows =>
        intro row hrow
        obtain ⟨hd, a, b, hab⟩ := h.2.1 row hrow
        exact ⟨hd, a, b, hB a b row.2 hab⟩
    | _ => trivial
  · intro ds out ha hd
    obtain ⟨a, b, hab⟩ := h.2.2.2.1 ds out ha hd
    exact ⟨a, b, hB a b out hab⟩
  · intro ds out ha N N' hN hN' hc hd
    exact hB _ _ out (h.2.2.2.2 ds out ha N N' hN hN' hc hd)

theorem covSObs_forall_body_mono
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l : Level} {p : Bool}
    {B B' : CovRForallBody}
    (hB : ∀ T S, CandidateCovS E (WhStepCK2 E n) Γ p S →
      CovSRelIncl (B T S) (B' T S)) :
    CovSRelIncl (covSForall E n Γ l p B) (covSForall E n Γ l p B') := by
  intro x y c h
  apply covSForall_intro (covSForall_shape h)
  intro ds out ha T hT S hS
  exact hB T S hS _ _ out (covSForall_apply h ha T hT S hS)

theorem covSObs_ordinary_codomain_mono
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {D B B' : CovSDataCandidate E n Γ}
    (hB : CovSRelIncl B.relation B'.relation) :
    CovSRelIncl (CovSDataCandidate.ordinary D B).relation
      (CovSDataCandidate.ordinary D B').relation := by
  intro x y c h Dty
  exact covSObs_arrow_codomain_mono hB x y c (h Dty)

theorem covSObs_allProp_body_mono
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {B B' : CovSDataCandidate E n Γ}
    (hB : CovSRelIncl B.relation B'.relation) :
    CovSRelIncl (CovSDataCandidate.allProp B).relation
      (CovSDataCandidate.allProp B').relation :=
  covSObs_forall_body_mono (p := true) (fun _ _ _ => hB)

theorem covSObs_allSort_body_mono
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {B B' : CovSDataCandidate E n Γ}
    (hB : CovSRelIncl B.relation B'.relation) :
    CovSRelIncl (CovSDataCandidate.allSort B).relation
      (CovSDataCandidate.allSort B').relation := by
  intro x y c h l
  exact covSObs_forall_body_mono (p := false) (fun _ _ _ => hB) x y c (h l)

theorem covSObs_build_rows_intro
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {rows : List (List CptT × CovSObsSyntax)}
    {F : ∀ row, row ∈ rows → CovSDataCandidate E n Γ}
    {x y : Expr Nat} {c : CptT}
    (h : ∀ row hrow, (F row hrow).relation x y c) :
    (covSBuildRows rows F).relation x y c := by
  intro r
  rcases r with ⟨r, hr⟩
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hr
  exact h row.val row.property

/-- The source and target use the same interpretation of every retained
output template. Only membership in the outer list changes. -/
theorem covSObs_build_rows_antitone
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ)
    {rows rows' : List (List CptT × CovSObsSyntax)}
    (hsub : ∀ row, row ∈ rows → row ∈ rows') :
    CovSRelIncl
      (covSBuildRows rows' (fun row _ => interpretObsTemplate E n Γ v row.2)).relation
      (covSBuildRows rows (fun row _ => interpretObsTemplate E n Γ v row.2)).relation := by
  intro x y c h
  apply covSObs_build_rows_intro
  intro row hrow
  exact covSSubstitution_rows_elim h row (hsub row hrow)

/-- The output intersection actually computed for one raw Pi row list. -/
def covSObsRows (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (rows : List (List CptT × CptT)) :
    CovSDataCandidate E n Γ :=
  covSBuildRows
    (rows.attach.map fun row => (row.val.1, templateOfObs row.val.2))
    (fun row _ => interpretObsTemplate E n Γ v row.2)

theorem covSObsRows_antitone
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ)
    {rows rows' : List (List CptT × CptT)}
    (hsub : ∀ row, row ∈ rows → row ∈ rows') :
    CovSRelIncl (covSObsRows E n Γ v rows').relation
      (covSObsRows E n Γ v rows).relation := by
  apply covSObs_build_rows_antitone
  intro r hr
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hr
  exact List.mem_map.mpr
    ⟨⟨row.val, hsub row.val row.property⟩, by simp, rfl⟩

/-- The branch discriminator is the observed domain compact. In
particular, `.prop` and `.sort` do not certify native binder origin. -/
theorem covSObsInterp_pi_eq (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (d : CptT)
    (rows : List (List CptT × CptT)) :
    covSObsInterp E n Γ v (.pi d rows) =
      match d with
      | .bot => covSTotalRel
      | .prop => (CovSDataCandidate.allProp (covSObsRows E n Γ v rows)).relation
      | .sort => (CovSDataCandidate.allSort (covSObsRows E n Γ v rows)).relation
      | _ => (CovSDataCandidate.ordinary
          (interpretObsTemplate E n Γ v (templateOfObs d))
          (covSObsRows E n Γ v rows)).relation := by
  cases d <;> simp [covSObsInterp, templateOfObs, interpretObsTemplate,
    covSObsRows, CovSDataCandidate.total]

/-- The domain is literally the same compact on both sides. This law
allows adding outer rows, without refining any domain or child compact.
No independent native observation or conversion bridge is asserted. -/
theorem covSObsInterp_pi_rows_antitone
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (d : CptT)
    {rows rows' : List (List CptT × CptT)}
    (hsub : ∀ row, row ∈ rows → row ∈ rows') :
    CovSRelIncl (covSObsInterp E n Γ v (.pi d rows'))
      (covSObsInterp E n Γ v (.pi d rows)) := by
  rw [covSObsInterp_pi_eq, covSObsInterp_pi_eq]
  have hB := covSObsRows_antitone E n Γ v hsub
  cases d with
  | bot => exact covSRelIncl_refl _
  | prop => exact covSObs_allProp_body_mono hB
  | sort => exact covSObs_allSort_body_mono hB
  | pi _ _ => exact covSObs_ordinary_codomain_mono hB
  | lam _ => exact covSObs_ordinary_codomain_mono hB
  | spine _ _ => exact covSObs_ordinary_codomain_mono hB

theorem covSObsInterp_to_bot (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (a : CptT) :
    CovSRelIncl (covSObsInterp E n Γ v a) (covSObsInterp E n Γ v .bot) := by
  rw [covSObsInterp_bot]
  exact covSRelIncl_total _

theorem covSObsInterp_bot_not_prop (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) :
    ¬ CovSRelIncl (covSObsInterp E n Γ v .bot) (covSObsInterp E n Γ v .prop) := by
  rw [covSObsInterp_bot, covSObsInterp_prop]
  exact covS_total_not_included_prop E

/-- The first stored type is the variable of the remaining context. Its
lookup at index zero is therefore the current variable at index one. -/
def covSObsMixedCtx : LCtx :=
  [.assumption (.bvar 0), .assumption (.sort (.succ (.succ .zero)))]

/-- The type variable has two admitted universe-code observations. The
term variable receives the Prop-universe compact, typed using `.sort`. -/
def covSObsMixedEnv : EnvT
  | 0, c => c = .prop
  | 1, c => c = .prop ∨ c = .sort
  | _ + 2, c => c = .bot

def covSObsMixedCtx_wf (E : ResolvedEnv) (n : Nat) : CtxWfT E n covSObsMixedCtx :=
  .assumption [.assumption (.sort (.succ (.succ .zero)))] (.bvar 0)
    (.succ (.succ .zero))
    (.assumption [] (.sort (.succ (.succ .zero))) (.succ (.succ (.succ .zero)))
      .nil (.sort [] (.succ (.succ .zero))))
    (.bvar _ 0 _ rfl)

def covSObsMixed_type_hasTy (E : ResolvedEnv) (n : Nat) :
    HasTyT E n covSObsMixedCtx (.bvar 1) (.sort (.succ (.succ .zero))) :=
  .bvar _ 1 _ rfl

def covSObsMixed_term_hasTy (E : ResolvedEnv) (n : Nat) :
    HasTyT E n covSObsMixedCtx (.bvar 0) (.bvar 1) :=
  .bvar _ 0 _ rfl

theorem covSObsMixed_env_typed (E : ResolvedEnv) (n : Nat) :
    EnvTypedFinAtT (ctxModelT_approxTK E n covSObsMixedCtx)
      covSObsMixedCtx covSObsMixedEnv := by
  intro i A hA us hus
  cases i with
  | zero =>
      have he : A = .bvar 1 := (Option.some.inj hA).symm
      subst A
      refine ⟨.sort, ?_, ?_⟩
      · exact .free (kFreeT_bvar E 1) (.bvar (Or.inr rfl))
      · intro c hc
        have he : c = .prop := hus c hc
        subst c
        exact ctyS_prop_sort E
  | succ i =>
      cases i with
      | zero =>
          have he : A = .sort (.succ (.succ .zero)) := (Option.some.inj hA).symm
          subst A
          refine ⟨.sort, ?_, ?_⟩
          · simpa only [sortCode_succ] using
              approxTK_sort_code E n covSObsMixedCtx covSObsMixedEnv
                (.succ (.succ .zero))
          · intro c hc
            have he : c = .prop ∨ c = .sort := hus c hc
            rcases he with rfl | rfl
            · exact ctyS_prop_sort E
            · exact ctyS_sort_sort E
      | succ i => simp [covSObsMixedCtx, lookupType] at hA

theorem covSObsMixed_ctx_coherent (E : ResolvedEnv) (n : Nat) :
    CtxEnvM (ctxModelT_approxTK E n covSObsMixedCtx) covSObsMixedCtx covSObsMixedEnv := by
  intro i value hv
  cases i with
  | zero => cases hv
  | succ i =>
      cases i with
      | zero => cases hv
      | succ i => simp [covSObsMixedCtx, lookupValue] at hv

theorem covSObsMixed_observations (E : ResolvedEnv) (n : Nat) :
    ApproxTK E n covSObsMixedCtx covSObsMixedEnv (.bvar 1) .bot ∧
    ApproxTK E n covSObsMixedCtx covSObsMixedEnv (.bvar 1) .prop ∧
    ApproxTK E n covSObsMixedCtx covSObsMixedEnv (.bvar 1) .sort ∧
    ApproxTK E n covSObsMixedCtx covSObsMixedEnv (.bvar 0) .prop :=
  ⟨.bot _ _ _, .free (kFreeT_bvar E 1) (.bvar (Or.inl rfl)),
    .free (kFreeT_bvar E 1) (.bvar (Or.inr rfl)),
    .free (kFreeT_bvar E 0) (.bvar rfl)⟩

/-- Both type observations concern the SAME native A, and the tested
compact is an actual observation of x : A. Every environment obligation
is supplied. This refutes uncoupled forward inclusion, without any Pi
template, row policy, or assumed compact-order edge. -/
theorem covSObsMixed_control (n : Nat) :
    Nonempty (EnvWfT emptyEnv) ∧ Nonempty (CtxWfT emptyEnv n covSObsMixedCtx) ∧
    EnvTypedFinAtT (ctxModelT_approxTK emptyEnv n covSObsMixedCtx)
      covSObsMixedCtx covSObsMixedEnv ∧
    CtxEnvM (ctxModelT_approxTK emptyEnv n covSObsMixedCtx)
      covSObsMixedCtx covSObsMixedEnv ∧
    Nonempty (HasTyT emptyEnv n covSObsMixedCtx (.bvar 1)
      (.sort (.succ (.succ .zero)))) ∧
    Nonempty (HasTyT emptyEnv n covSObsMixedCtx (.bvar 0) (.bvar 1)) ∧
    Nonempty (ConvT emptyEnv n covSObsMixedCtx (.bvar 0) (.bvar 0) (.bvar 1)) ∧
    ApproxTK emptyEnv n covSObsMixedCtx covSObsMixedEnv (.bvar 1) .bot ∧
    ApproxTK emptyEnv n covSObsMixedCtx covSObsMixedEnv (.bvar 1) .prop ∧
    ApproxTK emptyEnv n covSObsMixedCtx covSObsMixedEnv (.bvar 1) .sort ∧
    ApproxTK emptyEnv n covSObsMixedCtx covSObsMixedEnv (.bvar 0) .prop ∧
    (CptT.prop) ≠ .bot ∧
    CandidateCovS emptyEnv (WhStepCK2 emptyEnv n) covSObsMixedCtx false
      (covSObsInterp emptyEnv n covSObsMixedCtx
        (covSBaseVal emptyEnv n covSObsMixedCtx) .prop) ∧
    CovSJoint emptyEnv n covSObsMixedCtx (covSBaseVal emptyEnv n covSObsMixedCtx)
      false .bot (.bvar 0) (.bvar 0) .prop ∧
    ¬ covSObsInterp emptyEnv n covSObsMixedCtx
      (covSBaseVal emptyEnv n covSObsMixedCtx) .prop (.bvar 0) (.bvar 0) .prop := by
  obtain ⟨hb, hp, hs, hx⟩ := covSObsMixed_observations emptyEnv n
  have hreject : ¬ covSObsInterp emptyEnv n covSObsMixedCtx
      (covSBaseVal emptyEnv n covSObsMixedCtx) .prop (.bvar 0) (.bvar 0) .prop := by
    rw [covSObsInterp_prop]
    intro h
    exact covRProp_support_not_prop emptyEnv (covRSupport_intro h)
  exact ⟨⟨.empty⟩, ⟨covSObsMixedCtx_wf emptyEnv n⟩,
    covSObsMixed_env_typed emptyEnv n, covSObsMixed_ctx_coherent emptyEnv n,
    ⟨covSObsMixed_type_hasTy emptyEnv n⟩, ⟨covSObsMixed_term_hasTy emptyEnv n⟩,
    ⟨.refl _ _ _ (covSObsMixed_term_hasTy emptyEnv n)⟩,
    hb, hp, hs, hx, CptT.noConfusion,
    covSObsInterp_isCandidate emptyEnv n covSObsMixedCtx _ .prop,
    covSJoint_of_related (p := false)
      (covS_unknown_accepts_all emptyEnv n covSObsMixedCtx _ _ _ _), hreject⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_OBS_COHERENCE_ROOTS
#print axioms covSObs_arrow_codomain_mono
#print axioms covSObs_forall_body_mono
#print axioms covSObs_ordinary_codomain_mono
#print axioms covSObs_allProp_body_mono
#print axioms covSObs_allSort_body_mono
#print axioms covSObs_build_rows_intro
#print axioms covSObs_build_rows_antitone
#print axioms covSObsRows
#print axioms covSObsRows_antitone
#print axioms covSObsInterp_pi_eq
#print axioms covSObsInterp_pi_rows_antitone
#print axioms covSObsInterp_to_bot
#print axioms covSObsInterp_bot_not_prop
#print axioms covSObsMixedCtx
#print axioms covSObsMixedEnv
#print axioms covSObsMixedCtx_wf
#print axioms covSObsMixed_type_hasTy
#print axioms covSObsMixed_term_hasTy
#print axioms covSObsMixed_env_typed
#print axioms covSObsMixed_ctx_coherent
#print axioms covSObsMixed_observations
#print axioms covSObsMixed_control
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_OBS_COHERENCE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
