import rcic.RcicF3RawWFrame
import rcic.RcicF3PendARoleW
/-!
# The full admitted W group at the raw intersection role

The raw role agrees with the W least fixed point at every fitting parameter
and universe vector of this descriptor. Its literal fixed-point and recursor
consumers yield the full group-step interface. `groupStep` still takes the
predecessor invariant through that interface; it does not construct a faithful
RawFamily table for the entire environment or prove universal StepAG.
`closure_claim = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.RawWGeneral
open Rcic.Declarative PiIndex RawFamily
open PendAWBridge (fd)

theorem field_read (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : Frame) (hC : Admissible fd C) (a : PSet.{4})
    (ha : a ∈ U W4 1) :
    Equiv (Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) fxσ (push [a] ρ0) PendAW.field))
      (piSet (Ed (mkM P μ) a) (fun _ => C [] (key [a]))) := by
  let M := mkM P (table P μ fd C)
  have hfit : TelFits (mkM P μ) (σOf []) (fd.params ++ fd.indices) ρ0 [a] := by
    refine ⟨?_, trivial⟩
    exact mem_congr_right (ed_tyv (mkM P μ) (U4_dich 1)).symm ha
  have hr : Equiv (Ed M (fapps (ofFrame P μ fd C []) [a])) (C [] (key [a])) :=
    apply_ofFrame_ed P μ fd C hC [] [a] hfit
  have hn : pempty ∉ Ed M (fapps (ofFrame P μ fd C []) [a]) := by
    intro h
    have hd := (hC [] (key [a])).2
    rw [if_neg (PendAWLim.Typed.typeRead (σOf []))] at hd
    exact hd pempty (mem_congr_right hr h) Equiv.rfl
  change Equiv (Ed M (piVal M a
    (fun _ => fapps (table P μ fd C 4 []) [a]))) _
  have ht : table P μ fd C 4 [] = ofFrame P μ fd C [] := upd_eq _ _ _ _
  rw [ht]
  refine (ed_piVal_of_noEmpty M (A := a)
    (B := fun _ => fapps (ofFrame P μ fd C []) [a])
    (fun _ _ _ => Equiv.rfl) (fun _ _ => hn)).trans ?_
  exact piSet_congr Equiv.rfl (fun _ _ _ => hr)
theorem closed_cross (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : Frame) (hC : Admissible fd C) (hc : Closed P μ fd C)
    (a : PSet.{4}) (ha : a ∈ U W4 1) (vs : List Nat) :
    Sub (PsiF P μ fd fxσ (push [a] ρ0) (C [] (key [a])))
      (C vs (key [a])) := by
  have hfit : TelFits (mkM P (table P μ fd C)) fxσ fd.params ρ0 [a] := by
    refine ⟨?_, trivial⟩
    exact mem_congr_right (ed_tyv (mkM P (table P μ fd C)) (U4_dich 1)).symm ha
  intro z hz
  obtain ⟨i, ⟨⟨j, hj⟩, xs, he, hIn⟩, hiz⟩ := mem_sep.mp
    (mem_congr_right (PsiF_fin P μ fd fxσ (push [a] ρ0) (C [] (key [a]))) hz)
  have hs : ∀ x, x ∈ Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) fxσ (push [a] ρ0) PendAW.field) →
      SmallAlong (mkM P (table P μ fd C)) fxσ (W4 1)
        [PendAW.field] (push [a] ρ0) [x] := by
    intro x _
    refine ⟨?_, trivial⟩
    exact mem_congr_left (field_read P μ C hC a ha).symm
      ((stageW4 P 1).pi (fun _ _ _ => Equiv.rfl) (ed_mem_W4_of_mem_U P (mkM P μ) (by decide) (by decide) ha)
        (fun _ _ => (hC [] (key [a])).1))
  cases j with
  | zero =>
      cases xs with
      | cons x xs => exact False.elim hIn
      | nil =>
          apply hc vs (key [a]) z
          refine ⟨⟨0, by decide⟩, [a], [], hfit,
            True.intro, True.intro, rfl, ?_⟩
          exact hiz.symm.trans he
  | succ j =>
      cases j with
      | succ j =>
          have hl : fd.ctors.length = 2 := rfl
          exact False.elim (by omega : False)
      | zero =>
          cases xs with
          | nil => exact False.elim hIn
          | cons x xs =>
              cases xs with
              | cons y ys => exact False.elim hIn.2
              | nil =>
                  have hdom : (semF P μ fd fxσ (push [a] ρ0)
                      [PendAW.field]).domBig 0 [] = Ed (mkM P μ) a := by
                    change cond P.dec (Ed (mkM P μ) a ∈ W4 1)
                      (Ed (mkM P μ) a) (singleton pempty) = _
                    exact cond_pos (ed_mem_W4_of_mem_U P (mkM P μ)
                      (by decide) (by decide) ha) _ _
                  have hIn0 := hIn.1
                  change x ∈ piSet ((semF P μ fd fxσ (push [a] ρ0)
                      [PendAW.field]).domBig 0 [])
                    ((semF P μ fd fxσ (push [a] ρ0) [PendAW.field]).fib
                      (C [] (key [a])) 0 []) at hIn0
                  rw [hdom] at hIn0
                  have hm : x ∈ piSet (Ed (mkM P μ) a) (fun _ => C [] (key [a])) :=
                    piSet_sub
                      (B₁ := (semF P μ fd fxσ (push [a] ρ0) [PendAW.field]).fib
                        (C [] (key [a])) 0 [])
                      (B₂ := fun _ => C [] (key [a]))
                      (fun _ _ h => (semF P μ fd fxσ (push [a] ρ0) [PendAW.field]).fib_resp
                        (C [] (key [a])) 0 [] h)
                      (fun _ _ _ => Equiv.rfl) (fun _ _ => mem_sep_subset) x hIn0
                  have hx := mem_congr_right (field_read P μ C hC a ha).symm hm
                  apply hc vs (key [a]) z
                  refine ⟨⟨1, by decide⟩, [a], [x], hfit,
                    ⟨hx, True.intro⟩, hs x hx, rfl, ?_⟩
                  exact hiz.symm.trans he
/-- Elementary specialization of the cross-universe constructor closure. -/
theorem closed_prefixed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : Frame) (hC : Admissible fd C) (hc : Closed P μ fd C)
    (a : PSet.{4}) (ha : a ∈ U W4 1) :
    Sub (PsiF P μ fd fxσ (push [a] ρ0) (C [] (key [a])))
      (C [] (key [a])) := closed_cross P μ C hC hc a ha []

theorem raw_fibre (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (a : PSet.{4}) (ha : a ∈ U W4 1) (vs : List Nat) :
    Equiv (frame P μ fd vs (key [a])) (DStar P μ fd (σOf vs) (push [a] ρ0)) := by
  apply ext; intro z
  constructor
  · intro hz
    have hm := frame_least P μ fd (RawWFrame.candidate P μ)
      (RawWFrame.candidate_admissible P μ) (RawWFrame.candidate_closed P μ)
      vs (key [a]) z hz
    exact mem_congr_right (RawWFrame.candidate_key P μ vs [a]) hm
  · intro hz
    have he := DStar_levels P μ fd 0 (PendAWLim.Typed.nonIR P μ)
      PendAWLim.Typed.bounded (σ := σOf vs) (σ' := fxσ)
      (fun i hi => (Nat.not_lt_zero i hi).elim) (push [a] ρ0)
    have hz0 := mem_congr_right he hz
    have hall : InAll P μ fd vs (key [a]) z := by
      intro C hC hc
      have hleast := DStar_least P μ fd (PendAWLim.Typed.nonIR P μ)
        fxσ (push [a] ρ0) (PendAWLim.Typed.typeRead fxσ)
        (closed_prefixed P μ C hC hc a ha)
      exact closed_cross P μ C hC hc a ha vs z
        (PsiF_mono P μ fd fxσ (push [a] ρ0) hleast z
          ((DStar_lfp P μ fd fxσ (push [a] ρ0) (PendAWLim.Typed.typeRead fxσ)
            (PendAWLim.Typed.nonIR P μ fxσ (push [a] ρ0))).1.2.1 z hz0))
    have hw := (stageW4 P 1).trans
      (DStar_mem P μ fd (PendAWLim.Typed.nonIR P μ) (σOf vs) (push [a] ρ0)) hz
    obtain ⟨i, hi⟩ := hw
    unfold frame
    rw [if_neg (PendAWLim.Typed.typeRead (σOf vs))]
    exact mem_sep.mpr ⟨i, (inAll_resp P μ fd vs (key [a]) hi.symm).mp hall, hi⟩
theorem role_value (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat) :
    Equiv (role P μ fd vs) (famKT P μ fd vs) := by
  refine Equiv.trans ?_ (RawWFrame.ofCandidate P μ vs)
  change Equiv (ofFrame P μ fd (frame P μ fd) vs)
    (ofFrame P μ fd (RawWFrame.candidate P μ) vs)
  refine piLam_congr_fits (mkM P μ) (σOf vs) (.sort fd.resLevel)
    (fun _ _ h => Expr.noConfusion h) (fd.params ++ fd.indices) ρ0 ?_
  intro xs hx
  have hl : fd.params.length + fd.indices.length = xs.length := by
    rw [hx.length, List.length_append]
  change Equiv (tyv (frame P μ fd vs (key
    (lastVals (fd.params.length + fd.indices.length) (push xs ρ0)))))
    (tyv (RawWFrame.candidate P μ vs (key
      (lastVals (fd.params.length + fd.indices.length) (push xs ρ0)))))
  rw [hl, lastVals_push]
  cases xs with
  | nil => exact False.elim hx
  | cons a xs =>
      cases xs with
      | cons b xs => exact False.elim hx.2
      | nil =>
          have ha : a ∈ U W4 1 := mem_congr_right
            (ed_tyv (mkM P μ) (U4_dich 1)) hx.1
          exact tyv_congr ((raw_fibre P μ a ha vs).trans
            (RawWFrame.candidate_key P μ vs [a]).symm)
theorem fixed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (hF : ∀ vs, Equiv (μ PendAW.recA.family.ref vs)
      (role P μ (famDataOf PendAW.recA) vs)) (vs : List Nat) :
    Equiv (role P μ (famDataOf PendAW.recA) vs)
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf PendAW.recA)) := by
  exact (role_value P μ vs).trans
    (PendARoleW.fixed P μ (fun ls => (hF ls).trans (role_value P μ ls)) vs)
theorem package (P : Premises4) (K : Nat → Nat) (Efin : ResolvedEnv)
    (μ : Nat → List Nat → PSet.{4})
    (X : RoleModel.RecStepCtx role P K PendAW.fam PendAW.pNode μ) :
    RecPkgAt P μ K Efin PendAW.eAll 7 PendAW.recMem := by
  intro hsub
  refine ⟨?_, RoleModel.iota_type_of_witness_row P X.faith hsub X.rmem
    PendARoleW.witnessRow PendAWLim.Typed.typeRead X.lvC⟩
  have hcl := (X.facts _ _ X.rmem).1
  have hlvl := (X.facts _ _ X.rmem).2.1
  intro σ ls ρ hlen _
  refine ⟨?_, fun b hb => by rw [X.rbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ PendAW.recMem.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (X.faith.recur _).symm ?_
  exact recVal_mem_rec_KTA P μ PendAW.recA PendARoleW.groupA (ls.map (evalTotal σ))
    (PendAWLim.Typed.nonIR P μ) PendAWLim.Typed.fresh
    (fun vs => (X.lim vs).trans (role_value P μ vs))
    (groupFaith_ctorAt P X.faith _) (PendAWLim.Typed.typeRead _)
theorem groupStep (P : Premises4) (K : Nat → Nat) :
    RoleModel.GroupStepAt role P K natEnvUWfT (by rfl)
      PendAWGroup.ctorClasses (by rfl) PendAW.membersT := by
  exact RoleModel.stepAt_node role P K natEnvUWfT rfl
    PendAWGroup.ctorClasses rfl PendAW.membersT PendAW.pNode PendAWGroup.scanHit
    (fixed P) (package P K)
theorem groupStep_nonrefutable (P : Premises4) (K : Nat → Nat) :
    ¬ (RoleModel.GroupStepAt role P K natEnvUWfT (by rfl)
      PendAWGroup.ctorClasses (by rfl) PendAW.membersT → (Premises4 → False)) := by
  intro h
  exact h (groupStep P K) P
end Rcic.F3.PSet.RawWGeneral
