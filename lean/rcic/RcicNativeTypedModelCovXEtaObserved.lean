import rcic.RcicNativeTypedModelCovXEta

/-!
# All observed successor-eta compacts

The eta left endpoint can observe lambda tables even though the right endpoint
has only bottom and its rigid spine. The table rows nevertheless have exactly
successor-shaped base outputs. Their Pi typing uses a matching finite type
table, rather than imposing the one fixed successor control code on all rows.
These are actual inversion and typing suppliers, not a universal eta case.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelCovRelAudit TypedModelCovRelWitnessAudit
open TypedModelKTransportAudit TypedModelKFragmentAudit
open TypedModelCovNormCov2Audit

/-- Every observed application of the pinned successor has a base output
of the actual successor compact shape. Saturated ApproxTK cases are covered
by the already proved forgetful map. -/
theorem covX_natSucc_app_observation {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {a : Expr Nat} {c : CptT}
    (h : ApproxTK natEnvU n Γ ρ (.app (.const 2 []) a) c) :
    c = .bot ∨ ∃ u, c = .spine 2 [u] := by
  rcases approxT_app_inv (approxTK_forget h) with hb | ⟨g, s, _, hf, _⟩ |
      ⟨r, args, u, hc, hf, _⟩
  · exact Or.inl hb
  · rcases approxT_rigid_const_inv rigidConst_natEnvU_succ hf with hb | hs
    · exact CptT.noConfusion hb
    · exact CptT.noConfusion hs
  · rcases approxT_rigid_const_inv rigidConst_natEnvU_succ hf with hb | hs
    · exact CptT.noConfusion hb
    · cases hs
      exact Or.inr ⟨u, hc⟩

/-- An eta-left observation supplies its complete finite row table, the
original annotation demand typings, a non-bottom row, and the exact shape
of every output. -/
theorem covX_natSucc_eta_observation {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {c : CptT}
    (h : ApproxTK natEnvU n Γ ρ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c) :
    c = .bot ∨ ∃ a g, c = .lam g ∧
      ApproxTK natEnvU n Γ ρ (.const 0 []) a ∧
      (∃ s ∈ g, s.2 ≠ .bot) ∧
      (∀ s ∈ g, ∀ u ∈ s.1, CTyS natEnvU u a) ∧
      ∀ s ∈ g, s.2 = .bot ∨ ∃ u, s.2 = .spine 2 [u] := by
  rcases approxTK_lam_inv h with hb | ⟨a, g, hc, hA, hne, hbody⟩
  · exact Or.inl hb
  · refine Or.inr ⟨a, g, hc, hA, hne, fun s hs => (hbody s hs).1, ?_⟩
    intro s hs
    exact covX_natSucc_app_observation (hbody s hs).2

/-- The row-aligned Nat codomain table used only to prove the compact Pi
gate for an actual eta-lambda observation. -/
def covXNatRows (g : List (List CptT × CptT)) : List (List CptT × CptT) :=
  g.map (fun s => (s.1, .spine 0 []))

/-- A nonempty aligned table is not a proposition code, since its actual
codomain rows are the admitted Nat code. -/
theorem covXNatRows_not_prop {g : List (List CptT × CptT)}
    (hne : ∃ s ∈ g, s.2 ≠ .bot) :
    ¬ IsPropCT natEnvU (.pi (.spine 0 []) (covXNatRows g)) := by
  intro hp
  cases hp with
  | pi _ hout =>
    obtain ⟨s, hs, _⟩ := hne
    exact not_isPropCT_natEnvU_nat_spine []
      (hout (s.1, .spine 0 []) (List.mem_map.mpr ⟨s, hs, rfl⟩))

/-- The original annotation's actual observations type every demanded
compact at Nat; a bottom annotation forces a bottom demand. -/
theorem covX_nat_annotation_demands {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {a u : CptT} (hA : ApproxTK natEnvU n Γ ρ (.const 0 []) a)
    (hu : CTyS natEnvU u a) : CTyS natEnvU u (.spine 0 []) := by
  rcases approxT_rigid_const_inv rigidConst_natEnvU_nat (approxTK_forget hA)
    with rfl | rfl
  · rw [ctyS_bot_inv hu]
    exact ctyS_bot _
  · exact hu

private theorem covX_nat_rows_typing {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {a : CptT} {g : List (List CptT × CptT)}
    (hA : ApproxTK natEnvU n Γ ρ (.const 0 []) a)
    (hne : ∃ s ∈ g, s.2 ≠ .bot)
    (hd : ∀ s ∈ g, ∀ u ∈ s.1, CTyS natEnvU u a)
    (hout : ∀ s ∈ g, s.2 = .bot ∨ ∃ u, s.2 = .spine 2 [u]) :
    (C2 natEnvU).ty (.lam g) (.pi (.spine 0 []) (covXNatRows g)) := by
  change CTyCov2 natEnvU (.lam g) (.pi (.spine 0 []) (covXNatRows g))
  rw [CTyCov2]
  refine ⟨covXNatRows_not_prop hne, ?_, ?_⟩
  · intro s hs u hu
    exact ctyCov2_of_ctyS (covX_nat_annotation_demands hA (hd s hs u hu))
  · intro s hs
    rcases hout s hs with hb | ⟨u, he⟩
    · exact Or.inl hb
    · refine Or.inr ⟨(s.1, .spine 0 []), List.mem_map.mpr ⟨s, hs, rfl⟩,
        fun _ hm => hm, ?_⟩
      rw [he, CTyCov2]
      exact Or.inr ⟨⟨2, [u], rfl⟩, not_isPropCT_natEnvU_nat_spine []⟩

/-- Every actual eta-left lambda compact has a genuine C2 Pi gate, using
the aligned rows. The demand typing and non-bottom row are supplied by the
same actual model observation. -/
theorem covX_natSucc_eta_pi_gate {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {c : CptT}
    (h : ApproxTK natEnvU n Γ ρ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c) :
    ∃ a g, (C2 natEnvU).ty c (.pi a g) := by
  rcases covX_natSucc_eta_observation h with rfl |
    ⟨a, g, rfl, hA, hne, hd, hout⟩
  · exact ⟨.bot, [], (C2 natEnvU).bot _⟩
  · exact ⟨.spine 0 [], covXNatRows g, covX_nat_rows_typing hA hne hd hout⟩

/-- The matched Pi code is itself observed at the actual native Nat arrow
type in every valuation; its typing witness is not merely a syntactic code. -/
theorem covX_natSucc_eta_type_observation {n : Nat} {Γ : LCtx} {ρ : EnvT}
    {c : CptT}
    (h : ApproxTK natEnvU n Γ ρ
      (.lam (.const 0 []) (.app (lift 0 1 (.const 2 [])) (.bvar 0))) c) :
    ∃ a g, ApproxTK natEnvU n Γ ρ (.pi (.const 0 []) (.const 0 [])) (.pi a g) ∧
      (C2 natEnvU).ty c (.pi a g) := by
  rcases covX_natSucc_eta_observation h with hc |
    ⟨a, g, hc, hA, hne, hd, hout⟩
  · subst c
    exact ⟨.bot, [], approxTK_pi_bot_nil natEnvU n Γ ρ _ _, (C2 natEnvU).bot _⟩
  · subst c
    refine ⟨.spine 0 [], covXNatRows g, ?_, ?_⟩
    · apply ApproxTK.pi
        (ApproxTK.free (kFreeT_natEnvU _)
          (.const ρ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat))
      · intro t ht u hu
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
        exact covX_nat_annotation_demands hA (hd s hs u hu)
      · intro t ht
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
        exact ApproxTK.free (kFreeT_natEnvU _)
          (.const _ 0 [] rigidConst_natEnvU_nat not_propCtorT_natEnvU_nat)
    · exact covX_nat_rows_typing hA hne hd hout

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_OBSERVED_ROOTS
#print axioms covX_natSucc_app_observation
#print axioms covX_natSucc_eta_observation
#print axioms covXNatRows
#print axioms covXNatRows_not_prop
#print axioms covX_nat_annotation_demands
#print axioms covX_natSucc_eta_pi_gate
#print axioms covX_natSucc_eta_type_observation
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_ETA_OBSERVED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXEtaAudit
