import rcic.RcicNativePiProbeRelAssembly
import rcic.RcicNativeTypedModelIota
import rcic.RcicEtakMovingMinorUnion

/-!
# CK2 input audit: the model's Eq computation and the full substitution boundary

The model and the typed relation here are exactly the landed `ApproxT`
and `LRSCoreS`.  No readback is selected or changed in this file.

The Eq model computes its fourth argument independently of the index and
major.  Consequently the formerly refuted local `FundConvAt` is exactly
an all-related-substitutions sort-readback obligation.  Reading the one
identity instance is only one consequence of that quantified obligation.

The final obstruction is conditional on normality of the supplied source.
It does not infer native nonconvertibility from distinct syntax, and it
does not turn local model witnesses into a global supplier.

Composition only; no Fundamental constructor induction. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeRelIotaAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit

variable {R : Readback} {n : Nat}

/-- Admission supplies a structured Eq witness; no choice operation is
needed because it is used only to prove a proposition. -/
theorem eqRec_structured_exists :
    ∃ w : IotaWitnessS eqEnvT, w.recRef = 65 := by
  obtain ⟨hi⟩ := derivedIotaT_of_iotaWitness_envWfT pinEqGroupWfT eqGapW
  obtain ⟨w, hl, _⟩ := derivedIotaT_inv hi
  have hh := congrArg (fun e => (appsSpine e).1) hl
  simp only [iotaLhsOfS, iotaLhsOf, recCall, appsSpine_foldApps_const] at hh
  exact ⟨w, (Expr.const.inj hh).1⟩

/-- The existing admitted-data and schema lemmas identify all the
structured-witness fields used by the model computation. -/
theorem eqRec_model_schema (w : IotaWitnessS eqEnvT) (hr : w.recRef = 65) :
    PropFamilyS w ∧ w.preMajor.length = 5 ∧
      w.fields = [] ∧ w.schema = .bvar 1 := by
  have hm : w.recMember = eqRecT := by
    have h := w.hrec
    rw [hr] at h
    exact (Option.some.inj h).symm
  have hd := IotaWitnessS.recData_admitted eqGroupAdm
    (fun _ _ h => h) w hr hm
  change w.familyRef = 63 ∧ w.famMember = eqFamT ∧
    w.nparams = 2 ∧ w.nindices = 1 ∧ w.nMinors = 1 at hd
  obtain ⟨_, hfm, hnp, hni, hnm⟩ := hd
  refine ⟨?_, ?_, (NativeMovingMinorUnion76.schemaData w hr).2.2.2.2.2,
    NativeMovingMinorUnion76.schema_is_bvar1 w hr⟩
  · change piBody w.famMember.mtype = .sort .zero
    rw [hfm]
    rfl
  · rw [w.hpre, hnp, hni, hnm]

private theorem demandLists_five (us : List (List CptT)) (h : us.length = 5) :
    ∃ u0 u1 u2 u3 u4, us = [u0, u1, u2, u3, u4] := by
  cases us with
  | nil => cases h
  | cons u0 us =>
    cases us with
    | nil => cases h
    | cons u1 us =>
      cases us with
      | nil => cases h
      | cons u2 us =>
        cases us with
        | nil => cases h
        | cons u3 us =>
          cases us with
          | nil => cases h
          | cons u4 us =>
            have hz : us.length = 0 := by
              simp only [List.length_cons] at h
              omega
            obtain rfl := List.eq_nil_of_length_eq_zero hz
            exact ⟨u0, u1, u2, u3, u4, rfl⟩

/-- The model's forward Eq computation ignores the native index-agreement
question.  This is a statement about `ApproxT`, not a readback step. -/
theorem eqRec_model_minor_forward {ρ : EnvT} {ls : List Level}
    {A a motive minor b major : Expr Nat} {c : CptT}
    (h : ApproxT eqEnvT ρ
      (recCall (.const 65 ls) [A, a, motive, minor, b] major) c) :
    ApproxT eqEnvT ρ minor c := by
  obtain ⟨d, hd, hfold⟩ :=
    (approxT_foldApps_iff eqEnvT ρ (.const 65 ls)
      ([A, a, motive, minor, b] ++ [major]) c).mp h
  rcases approxT_propRec_inv
      (fun hr => (hr _ (rfl : eqEnvT.members 65 = some eqRecT)).2 rfl)
      (fun m body hδ => by
        obtain ⟨hm, _, hnrec, _⟩ := hδ
        have hem : eqRecT = m := Option.some.inj hm
        exact hnrec (hem ▸ (rfl : eqRecT.mclass = .recursorM)))
      (fun w hw => (eqRec_model_schema w hw).1) hd with
      rfl | ⟨w, us, c0, hw, hlen, hschema, rfl⟩
  · rw [foldAppCptT_bot_inv hfold]
    exact .bot _ _
  · obtain ⟨hP, hpre, hfields, hschemaEq⟩ := eqRec_model_schema w hw
    obtain ⟨u0, u1, u2, u3, u4, rfl⟩ := demandLists_five us (hlen.trans hpre)
    rcases (foldAppCptT_curryStepT_iff
      (show ([u0, u1, u2, u3, u4] ++ [[]]).length =
        ([A, a, motive, minor, b] ++ [major]).length from rfl)).mp hfold with
        hbot | ⟨hargs, heq⟩
    · rw [hbot]
      exact .bot _ _
    · rw [heq]
      have hc : c0 = .bot ∨ c0 ∈ u3 := by
        have hi := approxT_bvar_inv (show ApproxT eqEnvT
          (EnvT.pushArgs ([u0, u1, u2, u3, u4].map demandT) EnvT.bot)
          (.bvar 1) c0 from by
            simpa only [hfields, List.map_nil, List.append_nil,
              hschemaEq, instantiateLevels] using hschema)
        simpa only [EnvT.pushArgs, List.map_cons, List.map_nil,
          EnvT.cons, demandT] using hi
      rcases hc with rfl | hc
      · exact .bot _ _
      · cases hargs with
        | cons _ hargs =>
          cases hargs with
          | cons _ hargs =>
            cases hargs with
            | cons _ hargs =>
              cases hargs with
              | cons hminor _ => exact hminor c0 hc

/-- The model's converse Eq computation uses one singleton demand on the
fourth argument and empty demands on every other argument. -/
theorem eqRec_model_minor_backward {ρ : EnvT} {ls : List Level}
    {A a motive minor b major : Expr Nat} {c : CptT}
    (h : ApproxT eqEnvT ρ minor c) :
    ApproxT eqEnvT ρ
      (recCall (.const 65 ls) [A, a, motive, minor, b] major) c := by
  obtain ⟨w, hw⟩ := eqRec_structured_exists
  obtain ⟨hP, hpre, hfields, hschema⟩ := eqRec_model_schema w hw
  let us : List (List CptT) := [[], [], [], [c], []]
  have hc : ApproxT eqEnvT ρ (.const 65 ls) (curryStepT (us ++ [[]]) c) := by
    rw [← hw]
    apply ApproxT.recursorProp ls hP
    · exact hpre.symm
    · rw [hfields, List.map_nil, List.append_nil, hschema]
      exact ApproxT.bvar (show c ∈ [c] from List.mem_singleton.mpr rfl)
  apply (approxT_foldApps_iff eqEnvT ρ (.const 65 ls)
    ([A, a, motive, minor, b] ++ [major]) c).mpr
  refine ⟨_, hc, (foldAppCptT_curryStepT_iff (show
    (us ++ [[]]).length = ([A, a, motive, minor, b] ++ [major]).length from rfl)).mpr
    (Or.inr ⟨?_, rfl⟩)⟩
  refine .cons (fun _ h => (List.not_mem_nil _ h).elim)
    (.cons (fun _ h => (List.not_mem_nil _ h).elim)
      (.cons (fun _ h => (List.not_mem_nil _ h).elim)
        (.cons (fun u hu => ?_)
          (.cons (fun _ h => (List.not_mem_nil _ h).elim)
            (.cons (fun _ h => (List.not_mem_nil _ h).elim) .nil)))))
  obtain rfl := List.mem_singleton.mp hu
  exact h

/-- Exact Eq semantics for the landed typed model, uniformly in the
source environment, universe list, all arguments, and the major. -/
theorem eqRec_model_minor (ρ : EnvT) (ls : List Level)
    (A a motive minor b major : Expr Nat) :
    SemEqT eqEnvT ρ
      (recCall (.const 65 ls) [A, a, motive, minor, b] major) minor :=
  fun _ => ⟨eqRec_model_minor_forward, eqRec_model_minor_backward⟩

/-- All compacts of the actual formerly-refuted endpoint are either
bottom or the actual code of Sort zero. -/
theorem eqGap_model_shape {ρ : EnvT} {c : CptT}
    (h : ApproxT eqEnvT ρ eqGapRedex c) : c = .bot ∨ c = .prop := by
  have hc := approxT_sort_inv (eqRec_model_minor_forward h)
  simpa only [sortCode_zero] using hc

/-- The missing input is quantified over the complete original related
substitution package.  In particular it is not an identity-only read. -/
def EqGapUniformReadCK2 (R : Readback) (n : Nat) : Prop :=
  ∀ {Δ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
    CtxWfT eqEnvT n Δ →
    RelSubstAtT (ctxModelT_approxT eqEnvT) R n Δ ρ ρ' σ σ' eqGapCtx →
    ∃ u, RedR R Δ (substT σ' eqGapRedex) (.sort u)

/-- An exact restatement of the full local `FundConvAt`, retaining every
substitution and every model compact.  No readback law is needed for the
equivalence itself. -/
theorem eqGapFundConvAt_iff_uniformRead :
    FundConvAt (ctxModelT_approxT eqEnvT) R n eqGapCtx
      (.sort .zero) eqGapRedex (.sort (.succ .zero)) ↔
      EqGapUniformReadCK2 R n := by
  constructor
  · intro hF Δ ρ ρ' σ σ' hΔ hS
    have h := hF hΔ hS .prop
      (Or.inl (approxT_sort_code eqEnvT ρ .zero))
    obtain ⟨_, _, u, _, hr⟩ := (lrSCoreS_prop_iff _ _ _ _).mp h
    exact ⟨u, hr⟩
  · intro hread Δ ρ ρ' σ σ' hΔ hS c hc
    have hshape : c = .bot ∨ c = .prop := by
      rcases hc with hc | hc
      · simpa only [sortCode_zero] using approxT_sort_inv hc
      · exact eqGap_model_shape hc
    rcases hshape with rfl | rfl
    · exact lrSCoreS_bot _ _ _ _
    · obtain ⟨u, hu⟩ := hread hΔ hS
      rw [lrSCoreS_prop_iff]
      exact ⟨⟨.succ .zero, .refl _⟩, .zero, u, .refl _, hu⟩

/-- The identity repair is a necessary consequence of the full local
supplier, via the already-landed nonempty Eq substitution package. -/
theorem eqGap_uniformRead_identity (h : EqGapUniformReadCK2 R n) :
    ∃ u, RedR R eqGapCtx eqGapRedex (.sort u) := by
  obtain ⟨hΓ⟩ := eqGapCtx_wf n
  have hread := h hΓ
    (relSubstIdT_eqGap_bot (ctxModelT_approxT eqEnvT) R n)
  simpa only [substT_id] using hread

/-- A normal source carrying a universe compact cannot have the full
typing motive.  Native typing, the identity substitution, and source
normality are distinct inputs; no head-separation theorem is assumed. -/
theorem not_fundTyAt_of_normal_prop_compact {Γ : LCtx} {e I : Expr Nat}
    {ρ : EnvT} (hΓ : CtxWfT eqEnvT n Γ)
    (hId : RelSubstIdT (ctxModelT_approxT eqEnvT) R n Γ ρ)
    (hmodel : ApproxT eqEnvT ρ e .prop) (hnormal : NormalR R Γ e)
    (hshape : ∀ u, e ≠ .sort u) :
    ¬ FundTyAt (ctxModelT_approxT eqEnvT) R n Γ e I := by
  intro hF
  have hrel := fundTyAt_ctx_of_id hΓ hId hF .prop hmodel
  obtain ⟨_, u, _, hr, _⟩ := (lrSCoreS_prop_iff _ _ _ _).mp hrel
  exact hshape u (redR_of_normal hnormal hr).symm

/-- The conditional boundary applies to the global supplier only after
the exact native typing of that source has been supplied. -/
theorem not_fundamentalSAtT_of_normal_prop_compact {Γ : LCtx} {e I : Expr Nat}
    {ρ : EnvT} (hΓ : CtxWfT eqEnvT n Γ) (ht : HasTyT eqEnvT n Γ e I)
    (hId : RelSubstIdT (ctxModelT_approxT eqEnvT) R n Γ ρ)
    (hmodel : ApproxT eqEnvT ρ e .prop) (hnormal : NormalR R Γ e)
    (hshape : ∀ u, e ≠ .sort u) :
    ¬ FundamentalSAtT (ctxModelT_approxT eqEnvT) R n :=
  fun hF => not_fundTyAt_of_normal_prop_compact hΓ hId hmodel hnormal hshape (hF.1 hΓ ht)

-- BEGIN RCIC_NATIVE_READBACK_CK2_INPUTS_ROOTS
#print axioms eqRec_structured_exists
#print axioms eqRec_model_schema
#print axioms eqRec_model_minor_forward
#print axioms eqRec_model_minor_backward
#print axioms eqRec_model_minor
#print axioms eqGap_model_shape
#print axioms EqGapUniformReadCK2
#print axioms eqGapFundConvAt_iff_uniformRead
#print axioms eqGap_uniformRead_identity
#print axioms not_fundTyAt_of_normal_prop_compact
#print axioms not_fundamentalSAtT_of_normal_prop_compact
-- END RCIC_NATIVE_READBACK_CK2_INPUTS_ROOTS

end Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
