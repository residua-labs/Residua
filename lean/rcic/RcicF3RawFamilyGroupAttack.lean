import rcic.RcicF3RawFamilyGroup
import rcic.RcicF3RawWGeneral

/-! Exact admitted W replay through raw-frame group composition.
This is a new proof path for an existing group-step conclusion, not a
universal StepAG producer. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.RawFamilyGroupAttack
open Rcic.Declarative PiIndex RawFamily
open PendAWBridge (fd)

theorem w_frame_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Closed P μ fd (frame P μ fd) := by
  intro vs i z hz
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
  have he : ∀ r ls, Equiv (table P μ fd (frame P μ fd) r ls)
      (table P μ fd (RawWFrame.candidate P μ) r ls) := by
    intro r ls
    unfold table
    by_cases hr : r = fd.fref
    · subst r
      rw [upd_eq, upd_eq]
      exact (RawWGeneral.role_value P μ ls).trans (RawWFrame.ofCandidate P μ ls).symm
    · rw [upd_ne _ _ _ hr, upd_ne _ _ _ hr]
      exact Equiv.rfl
  have hpC := (TelFits_tables_equiv P he _ _ _ _).mp hp
  have hxC := (TelFits_tables_equiv P he _ _ _ _).mp hx
  have hsC : if evalTotal (σOf vs) fd.resLevel = 0 then True else
      SmallAlong (mkM P (table P μ fd (RawWFrame.candidate P μ))) (σOf vs)
        (W4 (evalTotal (σOf vs) fd.resLevel)) (fd.ctors.get j).1 (push ps ρ0) xs := by
    rw [if_neg (PendAWLim.Typed.typeRead (σOf vs))] at hs ⊢
    exact (smallAlong_tables P he _ _ _ _ _).mp hs
  have hri : (fd.ctors.get j).2 = [] := List.length_eq_zero.mp
    (PendAWLim.Typed.indicesLen _ (List.get_mem _ _ j.isLt))
  simp only [hri, List.map_nil, List.append_nil] at hi
  subst i
  have hm := RawWFrame.candidate_closed P μ vs (key ps) z
    ⟨j, ps, xs, hpC, hxC, hsC, by simp only [hri, List.map_nil, List.append_nil], hz⟩
  cases ps with
  | nil => exact False.elim hpC
  | cons a ps =>
    cases ps with
    | cons b ps => exact False.elim hpC.2
    | nil =>
      have ha : a ∈ U W4 1 := mem_congr_right
        (ed_tyv (mkM P (table P μ fd (RawWFrame.candidate P μ))) (U4_dich 1)) hpC.1
      exact mem_congr_right ((RawWFrame.candidate_key P μ vs [a]).trans
        (RawWGeneral.raw_fibre P μ a ha vs).symm) hm

/-- The two component obligations used by raw group composition are produced
for the exact admitted W family, uniformly at every universe vector. -/
theorem w_package (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv)
    (μ : Nat → List Nat → PSet.{4})
    (X : RawFamilyGroup.RecStepCtx P K PendAW.fam PendAW.pNode μ) :
    RecPkgAt P μ K Efin PendAW.eAll 7 PendAW.recMem := by
  exact RawWGeneral.package P K Efin μ
    ⟨X.faith.toLegacy P (RawWGeneral.fixed P μ X.lim), X.lim,
      X.scope, X.facts, X.pfree, X.rmem, X.rbody, X.lvC⟩

theorem w_groupStep (P : Premises4) (K : Nat → Nat) :
    RoleModel.GroupStepAt role P K natEnvUWfT (by rfl)
      PendAWGroup.ctorClasses (by rfl) PendAW.membersT := by
  exact RawFamilyGroup.stepAt_node P K natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT PendAW.pNode PendAWGroup.scanHit
    (fun μ _ => ⟨RawWFrame.raw_admissible P μ, w_frame_closed P μ⟩) (w_package P K)

end Rcic.F3.PSet.RawFamilyGroupAttack
