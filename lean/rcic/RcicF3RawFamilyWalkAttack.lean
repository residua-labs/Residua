import rcic.RcicF3RawFamilyWalk
import rcic.RcicF3RawWGeneral
/-!
# Inhabited data-constructor walk replay

The general raw-frame constructor bridge is instantiated at the exact admitted
PendA W node. Every typing, field-size, frame and table premise is paid.
The infinite graph fits its original higher-order field; application produces
the same height-omega value excluded by famLim. This uses a concrete faithful
famKT table whose family entry equals the raw closed candidate. It does not
construct the universal RawFamily table. `closure_claim = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.RawFamilyWalkAttack
open Rcic.Declarative Rcic.Model.PS RawFamily

theorem node_sound (P : Premises4) (k : Nat) :
    MemberSound P (PendARoleW.table P) (fun _ => k) 6 PendAW.node := by
  let μ := PendARoleW.table P
  let K : Nat → Nat := fun _ => k
  have hs : ∀ r m, PendAW.eLeaf.members r = some m → PendAW.eAll.members r = some m := by
    intro r m hr
    exact members_extend_preserved (by rfl : PendAW.ePre.members 7 = none) r m
      (members_extend_preserved (by rfl : PendAW.eLeaf.members 6 = none) r m hr)
  have hI := ((PendARoleW.gInv P k) _ (fun _ _ => rfl) μ (PendARoleW.faithful P)).2
    PendAW.eAll (fun _ _ h => h)
  have hE : ∀ σ n, EnvSound (mkM P μ) σ K PendAW.eLeaf n := by
    intro σ n
    exact envSound_of P hs
      (fun r m h => PendARoleW.canonicalSound P k r m (hs r m h))
      (fun r m h hk => hI r m (hs r m h) hk) σ n
  refine RawFamilyWalk.constructor_at_walk P μ K PendAW.pNode ⟨1, by decide⟩
    PendAW.familyView PendAW.nodeView hs (RawWFrame.candidate P μ)
    (RawWFrame.candidate_admissible P μ) (RawWFrame.candidate_closed P μ)
    ?_ ?_ (PendARoleW.context P k).facts rfl PendAW.nodeUniverse ?_
    (PendARoleW.context P k).scope hE ?_ ?_
  · intro vs
    have h := PendARoleW.faithful P 4 PendAW.fam rfl vs
    rw [PendAWGroup.familyRole] at h
    exact h.trans (RawWFrame.ofCandidate P μ vs).symm
  · intro vs
    have h := PendARoleW.faithful P 6 PendAW.node rfl vs
    rw [PendAWGroup.nodeRole] at h
    exact h
  · intro i hi hlo hhi
    change 1 ≤ i at hlo
    change i < 1 at hhi
    exact (Nat.not_lt_of_ge hlo hhi).elim
  · intro vs _ _
    exact PendAWGroup.ctorBound PendAW.pNode K (σOf vs) ⟨1, by decide⟩
  · exact PendAWGroup.nodeBound K
theorem node_inputs (P : Premises4) :
    TelFits (mkM P (PendARoleW.table P)) fxσ [.sort (.succ .zero), PendAW.field] ρ0
      [tyv fxS, graphOf (fxDomBig P) (fxhW P)] := by
  let μ := PendARoleW.table P
  let X := El (fapps (μ 4 []) [tyv fxS])
  have hX : Equiv X (DStar P μ PendAWBridge.fd fxσ PendAWBridge.rp) :=
    (el_congr (fapps_congr (PendARoleW.familyValue P) [tyv fxS])).trans
      (PendAFamily.fibre_eq P μ)
  have hn : pempty ∉ X := by
    intro h
    exact DStar_ne P μ PendAWBridge.fd (PendAWLim.Typed.nonIR P μ)
      fxσ PendAWBridge.rp pempty (mem_congr_right hX h) Equiv.rfl
  have he : Ed (mkM P μ) (fapps (μ 4 []) [tyv fxS]) = X :=
    ed_of_dich _ (Or.inr hn)
  have hg : graphOf (fxDomBig P) (fxhW P) ∈ piSet (fxDomBig P) (fun _ => X) := by
    refine graph_mem_piSet (B := fun _ => X) (fun _ _ _ => Equiv.rfl) _ ?_
    intro i
    rw [fx_hW_beta P i]
    apply mem_congr_right hX.symm
    apply PendAFamily.finite_sub P μ
    exact mem_congr_right (PendAWBridge.unionEq P μ).symm (fxT_mem_iUnionN P _)
  refine ⟨(PendAWBridge.argsFit P μ pempty).1, ?_, trivial⟩
  change graphOf (fxDomBig P) (fxhW P) ∈ Ed (mkM P μ)
    (piVal (mkM P μ) (tyv fxS) (fun _ => fapps (μ 4 []) [tyv fxS]))
  apply mem_congr_right (ed_piVal_of_noEmpty (mkM P μ)
    (A := tyv fxS) (B := fun _ => fapps (μ 4 []) [tyv fxS])
    (fun _ _ _ => Equiv.rfl) (fun _ _ => by rw [he]; exact hn)).symm
  have hd : Equiv (fxDomBig P) (Ed (mkM P μ) (tyv fxS)) := by
    rw [fx_domBig_eq P]
    exact el_tyv.trans (ed_tyv (mkM P μ) fx_dich).symm
  exact mem_congr_right (piSet_congr hd (fun _ _ _ => by rw [he]; exact Equiv.rfl)) hg

theorem heightOmega_application (P : Premises4) (k : Nat) :
    fxZW P ∈ Ed (mkM P (PendARoleW.table P))
      (fapps (PendARoleW.table P 4 []) [tyv fxS]) ∧
    fxZW P ∉ El (fapps (famLim P (PendARoleW.table P) PendAWBridge.fd []) [tyv fxS]) := by
  let μ := PendARoleW.table P
  have hnode := (node_sound P k fxσ [] ρ0 rfl
    (fun l hl => (List.not_mem_nil l hl).elim)).1
  rw [instantiateLevels_nil] at hnode
  have hm := mem_fapps (mkM P μ) fxσ (.app (.const 4 []) (.bvar 1))
    [.sort (.succ .zero), PendAW.field] ρ0 (μ 6 [])
    [tyv fxS, graphOf (fxDomBig P) (fxhW P)] hnode (node_inputs P)
  change fapps (μ 6 []) [tyv fxS, graphOf (fxDomBig P) (fxhW P)] ∈
    Ed (mkM P μ) (fapps (μ 4 []) [tyv fxS]) at hm
  have hv := PendARoleW.faithful P 6 PendAW.node rfl []
  rw [PendAWGroup.nodeRole] at hv
  have hp := fapps_piLam (mkM P μ) fxσ
    (ctorEnd_resp (mkM P μ) fxσ PendAWBridge.fd 1 (nfOf PendAWBridge.fd 1))
    (.app (.const 4 []) (.bvar 1)) [.sort (.succ .zero), PendAW.field]
    ρ0 [tyv fxS, graphOf (fxDomBig P) (fxhW P)] (node_inputs P)
  change Equiv (fapps (piLam (mkM P μ) fxσ
    (ctorEnd (mkM P μ) fxσ PendAWBridge.fd 1 (nfOf PendAWBridge.fd 1))
    ρ0 PendAW.node.mtype) [tyv fxS, graphOf (fxDomBig P) (fxhW P)])
    (ctorEnd (mkM P μ) fxσ PendAWBridge.fd 1 (nfOf PendAWBridge.fd 1)
      (push [tyv fxS, graphOf (fxDomBig P) (fxhW P)] ρ0)) at hp
  have he : ctorEnd (mkM P μ) fxσ PendAWBridge.fd 1 (nfOf PendAWBridge.fd 1)
      (push [tyv fxS, graphOf (fxDomBig P) (fxhW P)] ρ0) = fxZW P := by
    unfold ctorEnd
    rw [PendAWBridge.fdExact, cond_neg (by decide : evalTotal fxσ (.succ .zero) ≠ 0)]
    rfl
  rw [he] at hp
  exact ⟨mem_congr_left ((fapps_congr hv _).trans hp) hm,
    (RawWFrame.heightOmega_gap P μ).2⟩
end Rcic.F3.PSet.RawFamilyWalkAttack

