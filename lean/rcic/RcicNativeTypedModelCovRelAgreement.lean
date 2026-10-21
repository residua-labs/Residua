import rcic.RcicNativeTypedModelCovRelCore

/-!
# The exact compact-level port to the landed relation

Model agreement, including K-free agreement of observations, does not change a
recursive typing gate. The compatibility predicate below specifies the gates
actually encountered in a finite compact. It imposes no model condition and no
global re-entry from covariant typing into `CTyS`.

The equivalence theorem is conditional on that explicit compact compatibility.
This is an adapter port, not a claim that all covariantly typed observations
satisfy it. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovRelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- Agreement of precisely the typing gates occurring in a finite compact.
The complete demand-list proposition is compared, not each unrelated typing
judgment in the ambient compact algebra. -/
def CovGateAgreement (C : CovTyping E) : CptT → Prop
  | .bot | .prop | .sort | .spine _ _ => True
  | .pi a f => CovGateAgreement C a ∧
      ∀ s ∈ f,
        ((∀ u ∈ s.1, C.ty u a) ↔ (∀ u ∈ s.1, CTyS E u a)) ∧
        (∀ u ∈ s.1, CovGateAgreement C u) ∧ CovGateAgreement C s.2
  | .lam f => ∀ s ∈ f,
      (∀ u ∈ s.1, CovGateAgreement C u) ∧ CovGateAgreement C s.2
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have := sizeOfT_fst_lt s
       omega)
    | (have := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have := sizeOfT_snd_lt s
       omega)

theorem covGateAgreement_bot (C : CovTyping E) : CovGateAgreement C .bot := by
  rw [CovGateAgreement.eq_def]
  trivial

theorem covGateAgreement_prop (C : CovTyping E) : CovGateAgreement C .prop := by
  rw [CovGateAgreement.eq_def]
  trivial

theorem covGateAgreement_sort (C : CovTyping E) : CovGateAgreement C .sort := by
  rw [CovGateAgreement.eq_def]
  trivial

theorem covGateAgreement_spine (C : CovTyping E) (r : Nat) (args : List CptT) :
    CovGateAgreement C (.spine r args) := by
  rw [CovGateAgreement.eq_def]
  trivial

theorem covGateAgreement_pi_nil (C : CovTyping E) {a : CptT}
    (ha : CovGateAgreement C a) : CovGateAgreement C (.pi a []) := by
  rw [CovGateAgreement.eq_def]
  exact ⟨ha, fun _ hs => (List.not_mem_nil _ hs).elim⟩

theorem covGateAgreement_pi_bot_nil (C : CovTyping E) :
    CovGateAgreement C (.pi .bot []) :=
  covGateAgreement_pi_nil C (covGateAgreement_bot C)

theorem covGateAgreement_lam (C : CovTyping E)
    {f : List (List CptT × CptT)}
    (h : ∀ s ∈ f, (∀ u ∈ s.1, CovGateAgreement C u) ∧ CovGateAgreement C s.2) :
    CovGateAgreement C (.lam f) := by
  rw [CovGateAgreement.eq_def]
  exact h

/-- A row already typed by the model's old Pi constructor makes both gate
propositions true. This proves compatibility without a re-entry rule. -/
theorem covGateAgreement_pi_of_ctyS_rows (C : CovTyping E)
    (hS : CovTypingIncludesS C) {a : CptT} {f : List (List CptT × CptT)}
    (ha : CovGateAgreement C a)
    (ht : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
    (hc : ∀ s ∈ f, (∀ u ∈ s.1, CovGateAgreement C u) ∧ CovGateAgreement C s.2) :
    CovGateAgreement C (.pi a f) := by
  rw [CovGateAgreement.eq_def]
  refine ⟨ha, ?_⟩
  intro s hs
  exact ⟨⟨fun _ => ht s hs, fun _ u hu => hS a u (ht s hs u hu)⟩, hc s hs⟩

private theorem cov_agree_polyDom (C : CovTyping E) (hS : CovTypingIncludesS C) :
    CovGateAgreement C polyIdDom1 := by
  apply covGateAgreement_pi_of_ctyS_rows C hS (covGateAgreement_sort C)
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_prop_sort E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    refine ⟨?_, covGateAgreement_sort C⟩
    intro u hu
    rcases List.mem_singleton.mp hu with rfl
    exact covGateAgreement_prop C

private theorem cov_agree_polyWitness (C : CovTyping E) :
    CovGateAgreement C polyIdWitness1 := by
  apply covGateAgreement_lam C
  intro s hs
  rcases List.mem_singleton.mp hs with rfl
  refine ⟨?_, covGateAgreement_prop C⟩
  intro u hu
  rcases List.mem_singleton.mp hu with rfl
  exact covGateAgreement_prop C

private theorem cov_agree_polyOut1 (C : CovTyping E) :
    CovGateAgreement C polyIdOut1 := by
  apply covGateAgreement_lam C
  intro s hs
  rcases List.mem_singleton.mp hs with rfl
  refine ⟨?_, cov_agree_polyWitness C⟩
  intro u hu
  rcases List.mem_singleton.mp hu with rfl
  exact cov_agree_polyWitness C

private theorem cov_agree_polyTyCod1 (C : CovTyping E) (hS : CovTypingIncludesS C) :
    CovGateAgreement C polyIdTyCod1 := by
  apply covGateAgreement_pi_of_ctyS_rows C hS (cov_agree_polyDom C hS)
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_polyIdWitness1_polyIdDom1 E
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    refine ⟨?_, cov_agree_polyDom C hS⟩
    intro u hu
    rcases List.mem_singleton.mp hu with rfl
    exact cov_agree_polyWitness C

/-- The actual two-row polymorphic-identity observation has compatible
recursive gates, although its covariant typing does not re-enter `CTyS`. -/
theorem covGateAgreement_polyIdCpt01 (C : CovTyping E) (hS : CovTypingIncludesS C) :
    CovGateAgreement C polyIdCpt01 := by
  apply covGateAgreement_lam C
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · refine ⟨?_, cov_agree_polyWitness C⟩
    intro u hu
    rcases List.mem_singleton.mp hu with rfl
    exact covGateAgreement_sort C
  · rcases List.mem_singleton.mp hs with rfl
    refine ⟨?_, cov_agree_polyOut1 C⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact covGateAgreement_sort C
    · rcases List.mem_singleton.mp hu with rfl
      exact cov_agree_polyDom C hS

/-- The realized two-row type observation is compatible as well. -/
theorem covGateAgreement_polyIdTyCpt01 (C : CovTyping E) (hS : CovTypingIncludesS C) :
    CovGateAgreement C polyIdTyCpt01 := by
  apply covGateAgreement_pi_of_ctyS_rows C hS (covGateAgreement_sort C)
  · intro s hs u hu
    rcases List.mem_cons.mp hs with rfl | hs
    · rcases List.mem_singleton.mp hu with rfl
      exact ctyS_sort_sort E
    · rcases List.mem_singleton.mp hs with rfl
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ctyS_sort_sort E
      · rcases List.mem_singleton.mp hu with rfl
        exact ctyS_polyIdDom1_sort E
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · refine ⟨?_, cov_agree_polyDom C hS⟩
      intro u hu
      rcases List.mem_singleton.mp hu with rfl
      exact covGateAgreement_sort C
    · rcases List.mem_singleton.mp hs with rfl
      refine ⟨?_, cov_agree_polyTyCod1 C hS⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact covGateAgreement_sort C
      · rcases List.mem_singleton.mp hu with rfl
        exact cov_agree_polyDom C hS

/-- Exact relation agreement at a compatible finite compact, including the
contravariant recursive demand occurrences. -/
theorem lrSCoreCov_iff_coreS (C : CovTyping E) (c : CptT)
    (hc : CovGateAgreement C c) (Γ : LCtx) (x y A : Expr Nat) :
    LRSCoreCov C R n Γ x y A c ↔ LRSCoreS R E n Γ x y A c := by
  cases c with
  | bot | prop | sort | spine r args =>
      rw [LRSCoreCov.eq_def, LRSCoreS.eq_def]
  | pi a f =>
      rw [CovGateAgreement.eq_def] at hc
      obtain ⟨ha, hg⟩ := hc
      rw [LRSCoreCov.eq_def, LRSCoreS.eq_def]
      constructor
      · rintro ⟨hi, D, F, D', F', hx, hy, hctx, hdom, hcod, ⟨w, hd⟩, rows⟩
        refine ⟨hi, D, F, D', F', hx, hy, hctx, hdom, hcod,
          ⟨w, (lrSCoreCov_iff_coreS C a ha Γ D D' (.sort w)).mp hd⟩, ?_⟩
        intro s hs hty v v' hv hv' hvv hdem
        obtain ⟨gate, demands, out⟩ := hg s hs
        obtain ⟨z, hz⟩ := rows s hs (gate.mpr hty) v v' hv hv' hvv
          (fun u hu => (lrSCoreCov_iff_coreS C u (demands u hu) Γ v v' D).mpr (hdem u hu))
        exact ⟨z, (lrSCoreCov_iff_coreS C s.2 out Γ (instantiate0 v F)
          (instantiate0 v' F') (.sort z)).mp hz⟩
      · rintro ⟨hi, D, F, D', F', hx, hy, hctx, hdom, hcod, ⟨w, hd⟩, rows⟩
        refine ⟨hi, D, F, D', F', hx, hy, hctx, hdom, hcod,
          ⟨w, (lrSCoreCov_iff_coreS C a ha Γ D D' (.sort w)).mpr hd⟩, ?_⟩
        intro s hs hty v v' hv hv' hvv hdem
        obtain ⟨gate, demands, out⟩ := hg s hs
        obtain ⟨z, hz⟩ := rows s hs (gate.mp hty) v v' hv hv' hvv
          (fun u hu => (lrSCoreCov_iff_coreS C u (demands u hu) Γ v v' D).mp (hdem u hu))
        exact ⟨z, (lrSCoreCov_iff_coreS C s.2 out Γ (instantiate0 v F)
          (instantiate0 v' F') (.sort z)).mpr hz⟩
  | lam f =>
      rw [CovGateAgreement.eq_def] at hc
      rw [LRSCoreCov.eq_def, LRSCoreS.eq_def]
      constructor
      · rintro ⟨D, F, hr, hctx, rows⟩
        refine ⟨D, F, hr, hctx, ?_⟩
        intro s hs v v' hv hv' hvv hdem
        obtain ⟨demands, out⟩ := hc s hs
        have result := rows s hs v v' hv hv' hvv
          (fun u hu => (lrSCoreCov_iff_coreS C u (demands u hu) Γ v v' D).mpr (hdem u hu))
        exact (lrSCoreCov_iff_coreS C s.2 out Γ (.app x v) (.app y v')
          (instantiate0 v F)).mp result
      · rintro ⟨D, F, hr, hctx, rows⟩
        refine ⟨D, F, hr, hctx, ?_⟩
        intro s hs v v' hv hv' hvv hdem
        obtain ⟨demands, out⟩ := hc s hs
        have result := rows s hs v v' hv hv' hvv
          (fun u hu => (lrSCoreCov_iff_coreS C u (demands u hu) Γ v v' D).mp (hdem u hu))
        exact (lrSCoreCov_iff_coreS C s.2 out Γ (.app x v) (.app y v')
          (instantiate0 v F)).mpr result
termination_by sizeOf c
decreasing_by
  all_goals try subst c
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have := sizeOfT_fst_lt s
       omega)
    | (have := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have := sizeOfT_snd_lt s
       omega)

theorem lrsCov_iff_lrss (C : CovTyping E) (c : CptT) (hc : CovGateAgreement C c)
    (Γ : LCtx) (x y A : Expr Nat) :
    LRSCov C R n Γ x y A c ↔ LRSS R E n Γ x y A c := by
  exact or_congr Iff.rfl (lrSCoreCov_iff_coreS C c hc Γ x y A)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_REL_AGREEMENT_ROOTS
#print axioms CovGateAgreement
#print axioms covGateAgreement_bot
#print axioms covGateAgreement_prop
#print axioms covGateAgreement_sort
#print axioms covGateAgreement_spine
#print axioms covGateAgreement_pi_nil
#print axioms covGateAgreement_pi_bot_nil
#print axioms covGateAgreement_lam
#print axioms covGateAgreement_pi_of_ctyS_rows
#print axioms covGateAgreement_polyIdCpt01
#print axioms covGateAgreement_polyIdTyCpt01
#print axioms lrSCoreCov_iff_coreS
#print axioms lrsCov_iff_lrss
-- END RCIC_NATIVE_TYPED_MODEL_COV_REL_AGREEMENT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovRelAudit
