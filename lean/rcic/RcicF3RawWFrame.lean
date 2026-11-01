import rcic.RcicF3RawFamilyCtor
import rcic.RcicF3PendAFamily
/-!
# The raw intersection role at the exact PendA W fixture

The small closed candidate ranges over every extensional parameter key.
At the literal admitted descriptor `PendAWBridge.fd`, its abstraction is
`famKT`. At the infinite parameter that refutes the finite-stage role, the
raw intersection is exactly the guarded W least fixed point. Hence its
literal decoded role fibre is constructor-closed and contains `fxZW`.

All smallness and closure inputs are produced in this module. The model
premise `Premises4` remains explicit. No universal group step, syntax
extraction or general recursion theorem is asserted. `closure_claim = 0`.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Rcic.F3.PSet.RawWFrame
open Rcic.Declarative PiIndex RawFamily
open PendAWBridge (fd)

def candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : Frame := fun vs i =>
  sep (fun z => ∃ xs : List PSet.{4}, key xs = i ∧
    z ∈ DStar P μ fd (σOf vs) (push xs ρ0)) (W4 1)

theorem candidate_key (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (vs : List Nat) (xs : List PSet.{4}) :
    Equiv (candidate P μ vs (key xs)) (DStar P μ fd (σOf vs) (push xs ρ0)) := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨j, ⟨ys, hy, hm⟩, hz⟩ := mem_sep.mp hz
    have he := DStar_env P μ fd (PendAWLim.Typed.nonIR P μ) (σOf vs)
      (push_congr ((key_eq_iff ys xs).mp hy) (ρ := ρ0) (ρ' := ρ0) (fun _ => Equiv.rfl))
    exact mem_congr_right he (mem_congr_left hz hm)
  · intro hz
    have hw := (stageW4 P 1).trans
      (DStar_mem P μ fd (PendAWLim.Typed.nonIR P μ) (σOf vs) (push xs ρ0)) hz
    obtain ⟨j, hj⟩ := hw
    exact mem_sep.mpr ⟨j, ⟨xs, rfl, mem_congr_left hj.symm hz⟩, hj⟩
theorem candidate_admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Admissible fd (candidate P μ) := by
  intro vs i
  refine Quotient.inductionOn i ?_
  intro xs
  have he := candidate_key P μ vs xs
  refine ⟨mem_congr_left he.symm
    (DStar_mem P μ fd (PendAWLim.Typed.nonIR P μ) (σOf vs) (push xs ρ0)), ?_⟩
  change ∀ z, z ∈ candidate P μ vs (key xs) → ¬Equiv z pempty
  intro z hz
  exact DStar_ne P μ fd (PendAWLim.Typed.nonIR P μ) (σOf vs) (push xs ρ0) z
    (mem_congr_right he hz)
theorem resultTuple (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) {z : PSet.{4}}
    (hz : z ∈ DStar P μ fd σ ρ) :
    Equiv (resTupF P μ fd σ ρ z) (ordPair pempty (tup [])) := by
  have hp := (DStar_lfp P μ fd σ ρ (PendAWLim.Typed.typeRead σ)
    (PendAWLim.Typed.nonIR P μ σ ρ)).1.2.1 z hz
  obtain ⟨i, ⟨j, c, xs, hcj, hid, hIn⟩, hiz⟩ := mem_sep.mp hp
  have hl : xs.length = c.1.length :=
    (Sem.InPhi.length _ (kindsOf fd.fref c.1) xs 0 [] hIn).trans (List.length_map _ _)
  have he := resTupF_dataVal P μ fd σ ρ hcj hl (hiz.symm.trans hid)
  have hc0 : c.2 = [] := List.length_eq_zero.mp
    (PendAWLim.Typed.indicesLen c (List.getElem?_mem hcj))
  simpa only [hc0, List.map_nil] using he
theorem fibreFull (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    Equiv (fibAt P μ fd (DStar P μ fd) σ ρ []) (DStar P μ fd σ ρ) := by
  apply ext; intro z
  constructor
  · exact mem_sep_subset
  · intro hz
    obtain ⟨i, hi⟩ := hz
    exact mem_sep.mpr ⟨i, resultTuple P μ σ ρ ⟨i, Equiv.rfl⟩, hi⟩
theorem ofCandidate (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (vs : List Nat) :
    Equiv (ofFrame P μ fd (candidate P μ) vs) (famKT P μ fd vs) := by
  unfold famKT
  rw [if_neg (PendAWLim.Typed.typeRead (σOf vs))]
  change Equiv (piLam (mkM P μ) (σOf vs) _ ρ0 (famType fd))
    (piLam (mkM P μ) (σOf vs) _ ρ0 (famType fd))
  refine piLam_congr_fits (mkM P μ) (σOf vs) (.sort fd.resLevel)
    (fun _ _ h => Expr.noConfusion h) (fd.params ++ fd.indices) ρ0 ?_
  intro xs hx
  have hl : fd.params.length + fd.indices.length = xs.length := by
    rw [hx.length, List.length_append]
  change Equiv (tyv (candidate P μ vs (key
    (lastVals (fd.params.length + fd.indices.length) (push xs ρ0)))))
    (tyv (fibAt P μ fd (DStar P μ fd) (σOf vs)
      (shiftρ fd.indices.length (push xs ρ0)) (lastVals fd.indices.length (push xs ρ0))))
  rw [hl, lastVals_push]
  change Equiv (tyv (candidate P μ vs (key xs)))
    (tyv (fibAt P μ fd (DStar P μ fd) (σOf vs) (push xs ρ0) []))
  exact tyv_congr ((candidate_key P μ vs xs).trans (fibreFull P μ (σOf vs) (push xs ρ0)).symm)
theorem candidate_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Closed P μ fd (candidate P μ) := by
  intro vs i z hz
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hz
  have he : ∀ r ls, Equiv (table P μ fd (candidate P μ) r ls) (tabKT P μ fd r ls) := by
    intro r ls
    change Equiv (upd μ fd.fref (ofFrame P μ fd (candidate P μ)) r ls)
      (upd μ fd.fref (famKT P μ fd) r ls)
    by_cases hr : r = fd.fref
    · subst r; rw [upd_eq, upd_eq]; exact ofCandidate P μ ls
    · rw [upd_ne _ _ _ hr, upd_ne _ _ _ hr]; exact Equiv.rfl
  have hp' := (TelFits_tables_equiv P he (σOf vs) fd.params ρ0 ps).mp hp
  have hx' := (TelFits_tables_equiv P he (σOf vs) (fd.ctors.get j).1 (push ps ρ0) xs).mp hx
  have hk := PendAWLim.Typed.typeRead (σOf vs)
  rw [if_neg hk] at hs hz
  have hs' := (smallAlong_tables P he (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel))
    (fd.ctors.get j).1 (push ps ρ0) xs).mp hs
  have hc0 : (fd.ctors.get j).2 = [] := List.length_eq_zero.mp
    (PendAWLim.Typed.indicesLen _ (List.get_mem _ _ j.isLt))
  simp only [hc0, List.map_nil, List.append_nil] at hi
  subst i
  have hm : z ∈ TypeFib (mkM P (tabKT P μ fd)) W4
      (evalTotal (σOf vs) fd.resLevel) (σOf vs) fd.ctors (push ps ρ0) [] := by
    apply mem_TypeFib.mpr
    refine ⟨j.val, xs, fd.ctors.get j, ?_, ?_, hz, hs'⟩
    · exact List.getElem?_eq_getElem j.isLt
    · refine ⟨fd.ctors.get j, List.getElem?_eq_getElem j.isLt, hx', ?_⟩
      rw [hc0]; exact LEq.refl []
  have hpf : TelFits (mkM P (tabKT P μ fd)) (σOf vs) (fd.params ++ fd.indices) ρ0 ps := by
    simpa only [PendAWBridge.fdExact, List.append_nil] using hp'
  have ha := fapps_piLam (mkM P (tabKT P μ fd)) (σOf vs)
    (famEnd_resp (mkM P (tabKT P μ fd)) W4 (σOf vs) fd)
    (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 ps hpf
  change Equiv (fapps (famVal (mkM P (tabKT P μ fd)) W4 (σOf vs) fd) ps)
    (famEnd (mkM P (tabKT P μ fd)) W4 (σOf vs) fd (push ps ρ0)) at ha
  have hv := (fapps_congr (PendAFamily.fixed P μ vs) ps).symm.trans ha
  unfold famEnd at hv
  rw [cond_neg hk] at hv
  have hread : Equiv (fapps (ofFrame P μ fd (candidate P μ) vs) ps)
    (tyv (candidate P μ vs (key ps))) := apply_ofFrame P μ fd (candidate P μ) vs ps
      (by
        have hp0 := (TelFits_agreeOn P
          (agreeOn_upd_off μ fd.fref (ofFrame P μ fd (candidate P μ))) (σOf vs)
          fd.params (by
            intro e he
            have heq : e = .sort (.succ .zero) := List.mem_singleton.mp he
            subst e
            intro r hr
            cases hr) ρ0 ps).mp hp
        simpa only [PendAWBridge.fdExact, List.append_nil] using hp0)
  have hty := hread.symm.trans ((fapps_congr (ofCandidate P μ vs) ps).trans hv)
  have hed := ed_congr (mkM P μ) hty
  have hC := ed_tyv (mkM P μ) (admissible_dich (candidate_admissible P μ) vs (key ps))
  have hT := ed_tyv (mkM P μ) (TypeFib_dich (mkM P (tabKT P μ fd)) W4
    (evalTotal (σOf vs) fd.resLevel) (σOf vs) fd.ctors (push ps ρ0) [])
  exact mem_congr_right ((hC.symm.trans hed).trans hT).symm hm
theorem raw_admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Admissible fd (frame P μ fd) := by
  exact frame_admissible P μ fd ⟨candidate P μ, candidate_admissible P μ, candidate_closed P μ⟩
theorem field_read (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : Frame) (hC : Admissible fd C) :
    Equiv (Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) fxσ PendAWBridge.rp PendAW.field))
      (piSet (fxDomBig P) (fun _ => C [] (key [tyv fxS]))) := by
  let M := mkM P (table P μ fd C)
  have hr : Equiv (Ed M (fapps (ofFrame P μ fd C []) [tyv fxS])) (C [] (key [tyv fxS])) :=
    apply_ofFrame_ed P μ fd C hC [] [tyv fxS] (PendAWBridge.argsFit P μ pempty)
  have hn : pempty ∉ Ed M (fapps (ofFrame P μ fd C []) [tyv fxS]) := by
    intro h
    have hd := (hC [] (key [tyv fxS])).2
    rw [if_neg (PendAWLim.Typed.typeRead (σOf []))] at hd
    exact hd pempty (mem_congr_right hr h) Equiv.rfl
  change Equiv (Ed M (piVal M (tyv fxS)
    (fun _ => fapps (table P μ fd C 4 []) [tyv fxS]))) _
  have ht : table P μ fd C 4 [] = ofFrame P μ fd C [] := upd_eq _ _ _ _
  rw [ht]
  refine (ed_piVal_of_noEmpty M (A := tyv fxS)
    (B := fun _ => fapps (ofFrame P μ fd C []) [tyv fxS]) (fun _ _ _ => Equiv.rfl) (fun _ _ => hn)).trans ?_
  have hd : Equiv (Ed M (tyv fxS)) (fxDomBig P) := by
    rw [fx_domBig_eq P]
    exact (ed_tyv M fx_dich).trans el_tyv.symm
  exact piSet_congr hd (fun _ _ _ => hr)
theorem closed_prefixed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : Frame) (hC : Admissible fd C) (hc : Closed P μ fd C) :
    Sub (PsiF P μ fd fxσ PendAWBridge.rp (C [] (key [tyv fxS])))
      (C [] (key [tyv fxS])) := by
  intro z hz
  obtain ⟨i, ⟨⟨j, hj⟩, xs, he, hIn⟩, hiz⟩ := mem_sep.mp
    (mem_congr_right (PsiF_fin P μ fd fxσ PendAWBridge.rp (C [] (key [tyv fxS]))) hz)
  have hs : ∀ x, x ∈ Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) fxσ PendAWBridge.rp PendAW.field) →
      SmallAlong (mkM P (table P μ fd C)) fxσ (W4 1)
        [PendAW.field] PendAWBridge.rp [x] := by
    intro x _
    refine ⟨?_, trivial⟩
    exact mem_congr_left (field_read P μ C hC).symm
      ((stageW4 P 1).pi (fun _ _ _ => Equiv.rfl) (fx_domBig_mem_W4 P)
        (fun _ _ => (hC [] (key [tyv fxS])).1))
  cases j with
  | zero =>
      cases xs with
      | cons x xs => exact False.elim hIn
      | nil =>
          apply hc [] (key [tyv fxS]) z
          refine ⟨⟨0, by decide⟩, [tyv fxS], [], PendAWBridge.argsFit P _ pempty,
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
                  have hm : x ∈ piSet (fxDomBig P) (fun _ => C [] (key [tyv fxS])) :=
                    piSet_sub
                      (B₁ := (semF P μ fd fxσ PendAWBridge.rp [PendAW.field]).fib
                        (C [] (key [tyv fxS])) 0 [])
                      (B₂ := fun _ => C [] (key [tyv fxS]))
                      (fun _ _ h => (semF P μ fd fxσ PendAWBridge.rp [PendAW.field]).fib_resp
                        (C [] (key [tyv fxS])) 0 [] h)
                      (fun _ _ _ => Equiv.rfl) (fun _ _ => mem_sep_subset) x hIn.1
                  have hx := mem_congr_right (field_read P μ C hC).symm hm
                  apply hc [] (key [tyv fxS]) z
                  refine ⟨⟨1, by decide⟩, [tyv fxS], [x], PendAWBridge.argsFit P _ pempty,
                    ⟨hx, True.intro⟩, hs x hx, rfl, ?_⟩
                  exact hiz.symm.trans he
theorem raw_fibre (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (frame P μ fd [] (key [tyv fxS])) (DStar P μ fd fxσ PendAWBridge.rp) := by
  apply ext; intro z
  constructor
  · intro hz
    have hm := frame_least P μ fd (candidate P μ) (candidate_admissible P μ)
      (candidate_closed P μ) [] (key [tyv fxS]) z hz
    exact mem_congr_right (candidate_key P μ [] [tyv fxS]) hm
  · intro hz
    have hall : InAll P μ fd [] (key [tyv fxS]) z := by
      intro C hC hc
      exact DStar_least P μ fd (PendAWLim.Typed.nonIR P μ) fxσ PendAWBridge.rp
        (PendAWLim.Typed.typeRead fxσ) (closed_prefixed P μ C hC hc) z hz
    have hw := (stageW4 P 1).trans
      (DStar_mem P μ fd (PendAWLim.Typed.nonIR P μ) fxσ PendAWBridge.rp) hz
    obtain ⟨i, hi⟩ := hw
    unfold frame
    rw [if_neg (PendAWLim.Typed.typeRead (σOf []))]
    exact mem_sep.mpr ⟨i, (inAll_resp P μ fd [] (key [tyv fxS]) hi.symm).mp hall, hi⟩
theorem role_fibre (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Equiv (Ed (mkM P μ) (fapps (role P μ fd []) [tyv fxS]))
      (DStar P μ fd fxσ PendAWBridge.rp) := by
  exact (apply_ofFrame_ed P μ fd (frame P μ fd) (raw_admissible P μ) [] [tyv fxS]
    (PendAWBridge.argsFit P μ pempty)).trans (raw_fibre P μ)
theorem heightOmega_gap (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    fxZW P ∈ Ed (mkM P μ) (fapps (role P μ fd []) [tyv fxS]) ∧
      fxZW P ∉ El (fapps (famLim P μ fd []) [tyv fxS]) := by
  constructor
  · exact mem_congr_right (role_fibre P μ).symm
      (mem_congr_right (PendAFamily.fibre_eq P μ) (PendAFamily.heightOmega P μ))
  · intro hz
    exact (PendAWBridge.heightOmega P μ).2
      (mem_congr_right (PendAWLim.Typed.famFiberEq P μ) hz)
theorem role_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    Sub (PsiF P μ fd fxσ PendAWBridge.rp
      (Ed (mkM P μ) (fapps (role P μ fd []) [tyv fxS])))
      (Ed (mkM P μ) (fapps (role P μ fd []) [tyv fxS])) := by
  intro z hz
  apply mem_congr_right (role_fibre P μ).symm
  exact (DStar_lfp P μ fd fxσ PendAWBridge.rp (PendAWLim.Typed.typeRead fxσ)
    (PendAWLim.Typed.nonIR P μ fxσ PendAWBridge.rp)).1.1 z
      (PsiF_mono P μ fd fxσ PendAWBridge.rp
        (fun x hx => mem_congr_right (role_fibre P μ) hx) z hz)
theorem repair_nonrefutable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ¬ ((Sub (PsiF P μ fd fxσ PendAWBridge.rp
      (Ed (mkM P μ) (fapps (role P μ fd []) [tyv fxS])))
      (Ed (mkM P μ) (fapps (role P μ fd []) [tyv fxS])) ∧
      fxZW P ∈ Ed (mkM P μ) (fapps (role P μ fd []) [tyv fxS])) →
        (Premises4 → False)) := by
  intro h
  exact h ⟨role_closed P μ, (heightOmega_gap P μ).1⟩ P
theorem wrong_tag_refused (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (j : Nat) (hj : 2 ≤ j) (xs : List PSet.{4}) :
    dataVal j xs ∉ Ed (mkM P μ) (fapps (role P μ fd []) [tyv fxS]) := by
  intro hz
  have hm := (DStar_lfp P μ fd fxσ PendAWBridge.rp (PendAWLim.Typed.typeRead fxσ)
    (PendAWLim.Typed.nonIR P μ fxσ PendAWBridge.rp)).1.2.1 _
      (mem_congr_right (role_fibre P μ) hz)
  obtain ⟨i, ⟨⟨k, hk⟩, ys, he, _⟩, hiz⟩ := mem_sep.mp
    (mem_congr_right (PsiF_fin P μ fd fxσ PendAWBridge.rp
      (DStar P μ fd fxσ PendAWBridge.rp)) hm)
  have hjk : j = k := ord_inj ((tagOf_dataVal j xs).symm.trans
    ((tagOf_congr (hiz.symm.trans he)).trans (tagOf_dataVal k ys)))
  have hl : fd.ctors.length = 2 := rfl
  omega
end Rcic.F3.PSet.RawWFrame
