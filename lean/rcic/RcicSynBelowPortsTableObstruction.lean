import rcic.RcicSynSameRankDep
import rcic.RcicSynTableNoHead
import rcic.RcicSynP2Iota
import rcic.RcicSynStepFieldsDeltaIota
import rcic.RcicNativeSortRetypeAudit

/-!
# The current `tableOf` cannot simulate the admitted Nat retained-iota instance

This module composes the landed erased Church--Rosser theorem, rigid-spine
inversion, and the original S17 Nat witness.  No native inversion, uniqueness,
or Below pack is assumed.  `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Different rigid constant heads cannot be convertible in a well-formed
erased table.  Both trace inversions are the landed spine theorem. -/
theorem not_convMod_distinct_const_heads_closed {tbl : List CRule}
    (hW : TableWF tbl) {f g : Nat} (hf : NoHeadRule tbl f)
    (hg : NoHeadRule tbl g) (hne : f ≠ g)
    (ls ms : List Level) (xs ys : List ETm) :
    ¬ ConvMod (EStep tbl) LvlEq (ETm.appN (.const f ls) xs)
      (ETm.appN (.const g ms) ys) := by
  intro h
  obtain ⟨c, d, hc, hq, hd⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr)
      (confluent_eStep_wf hW) h
  obtain ⟨xs', rfl, _, _⟩ := rstar_eStep_appN_const_inv hf hc
  obtain ⟨ys', rfl, _, _⟩ := rstar_eStep_appN_const_inv hg hd
  obtain ⟨f', zs, heq, hhead, _⟩ := lvlEq_appN_inv hq
  cases hhead with
  | const _ _ => exact hne (ETm.appN_const_inj heq).1.symm

/-- The S17 rhs discards both arguments by its two original beta redexes.
This computation uses no constant rule and holds for every table. -/
theorem natSucc_rhs_beta_closed (tbl : List CRule) :
    ConvMod (EStep tbl) LvlEq ER Zε := by
  have h₁ : RStep tbl ER (.app (.lam Zε) (recε Pε Zε msε Zε)) :=
    .appL _ (.beta (.lam Zε) Zε)
  have h₂ : RStep tbl (.app (.lam Zε) (recε Pε Zε msε Zε)) Zε :=
    .beta Zε _
  exact (ConvMod.fwd (.inl h₁)).trans (ConvMod.fwd (.inl h₂))

/-- The exact admitted S17 conversion has no erased simulation in the
current delta-only `tableOf`, even allowing arbitrary conversion length. -/
theorem natSucc_not_es_tableOf_closed :
    ¬ ES (tableOf natEnvUWfT) id [] H := by
  intro h
  have h₃ : NoHeadRule (tableOf natEnvUWfT) 3 :=
    noHeadRule_tableOf_of_ne_defM natEnvUWfT
      (fm := natRecMemberU) rfl (by decide)
  have h₁ : NoHeadRule (tableOf natEnvUWfT) 1 :=
    noHeadRule_tableOf_of_ne_defM natEnvUWfT
      (fm := natZeroMember) rfl (by decide)
  have he : ConvMod (EStep (tableOf natEnvUWfT)) LvlEq EL ER := by
    simpa only [ES, s17_H_dl_eq, s17_H_dr_eq, hL_eps_el, hR_eps_er] using h
  exact not_convMod_distinct_const_heads_closed (tableWF_build natEnvUWfT)
    h₃ h₁ (by decide) [.succ .zero] [] [Pε, Zε, msε, majorε] []
      (he.trans (natSucc_rhs_beta_closed _))

/-- The general retained-iota residual itself is false on the same input;
permitting both conversion match legs does not repair the missing table rule. -/
theorem natSucc_simulation_tableOf_refuted :
    ¬ Nonempty (IotaRetainedSimulation (tableOf natEnvUWfT) hL hR id []) := by
  rintro ⟨sim⟩
  exact natSucc_not_es_tableOf_closed
    (iota_erasure_from_answers (DerivedIota.of wSuccU1) hL hR hL hR
      (.refl _) (.refl _) s17_qPL s17_qPR
      sim.matchL sim.croot sim.beta sim.matchR)

/-- The very same retained native iota input is simulated by the landed
successor-rule table.  Its certificate is reused verbatim. -/
theorem natSucc_iota_positive_control : ES natSuccTable id [] H :=
  natSucc_iota_erasure_via_answers

/-- The original S17 witness satisfies the real assumption-prefix gate. -/
theorem natSucc_assumpPref_closed : H.AssumpPref := by
  have h₁ : hL.AssumpPref :=
    NativeValleys.NativeSortRetypeAudit.enrichHasTyT_native_ap
      natEnvUWfT CtxWfT.nil hLT
  have h₂ : hR.AssumpPref :=
    NativeValleys.NativeSortRetypeAudit.enrichHasTyT_native_ap
      natEnvUWfT CtxWfT.nil hRT
  exact ⟨h₁, h₂, h₁, h₂⟩

/-- An actual scope for the S17 witness, retaining the admitted environment. -/
def natSucc_belowScope : ScopedCtx natEnvU natEnvU 1 [] :=
  ⟨natEnvUWfT, envExt_refl _, .nil⟩

/-- The counterexample is a demanded public root of the repaired grammar. -/
theorem natSucc_demand_closed : Demand (.es H natSucc_belowScope id []) :=
  .rootEs H natSucc_assumpPref_closed natSucc_belowScope id levelHom_id

/-- Consequently the user's exact current-table target is false, for any
admission-weight function.  This refutes the table-specific pack, not sortRow. -/
theorem natSucc_not_allBelowScoped_closed (Aw : Nat → Nat) :
    ¬ AllBelowScoped natEnvU Aw (tableOf natEnvUWfT) := by
  intro h
  exact natSucc_not_es_tableOf_closed
    (es_of_allBelowScoped h natSucc_belowScope levelHom_id H
      natSucc_assumpPref_closed)

/-- No supplier record can inhabit that exact admitted table. -/
theorem natSucc_not_stepSuppliers_closed (Aw : Nat → Nat) :
    ¬ StepSuppliers Aw (tableOf natEnvUWfT) natEnvU := by
  intro W
  exact natSucc_not_allBelowScoped_closed Aw
    (allBelowScoped_of_suppliers_derivedMixed Aw _ (tableWF_build natEnvUWfT) W)

/-- No universal producer can have the requested current-table contract,
even at each environment's own canonical admission weights. -/
theorem envWfT_allBelowScoped_tableOf_producer_refuted :
    ¬ (∀ {E : ResolvedEnv} (hW : EnvWfT E),
      AllBelowScoped E (enrichEnvWfT hW).admW (tableOf hW)) := by
  intro make
  exact natSucc_not_allBelowScoped_closed _ (make natEnvUWfT)

end Rcic.Syn
