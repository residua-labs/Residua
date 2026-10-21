import rcic.RcicNativeTypedModelCovUProjection
import rcic.RcicNativeTypedModelCovURealized
import rcic.RcicNativeTypedModelW6Iota
import rcic.RcicNativeTypedModelCovVAligned

/-!
# Forward observation transport for actual constructor projections

This module concerns only the non-index-revealed projection fields.  The
reverse direction is refuted by `covU_proj_ctor_observation_boundary`.
The forward argument uses the actual recursor schema and beta contraction;
native readback equality alone is not used as a model transport premise.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovVAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open PiModelDeltaIotaAudit FamModelKAudit FamModelLRSAudit
open TypedModelAudit TypedModelAudit.TypingFin
open TypedModelKAudit ReadbackCKAudit TypedModelCovUAudit
open TypedModelW6IotaAudit

/-- One beta contraction needs no converse expansion principle. -/
theorem covV_approxT_beta_forward {E : ResolvedEnv} {ρ : EnvT}
    {D body arg : Expr Nat} {c : CptT}
    (h : ApproxT E ρ (.app (.lam D body) arg) c) :
    ApproxT E ρ (instantiate0 arg body) c := by
  rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩ |
      ⟨r, args, u, rfl, hf, _⟩
  · exact .bot _ _
  · rcases approxT_lam_inv hf with hb | ⟨a, g', he, _, _, hg⟩
    · exact (CptT.noConfusion hb)
    · cases he
      exact (modelSubstFactorT_approxT E).subst0_intro ha (hg s hs).2
  · rcases approxT_lam_inv hf with hb | ⟨a, g', he, _⟩
    · exact CptT.noConfusion hb
    · exact CptT.noConfusion he

private theorem covV_approxT_foldApps_head {E : ResolvedEnv} {ρ : EnvT}
    {f f' : Expr Nat} {xs : List (Expr Nat)} {c : CptT}
    (hf : ∀ d, ApproxT E ρ f d → ApproxT E ρ f' d)
    (h : ApproxT E ρ (foldApps f xs) c) :
    ApproxT E ρ (foldApps f' xs) c := by
  obtain ⟨d, hd, happ⟩ := (approxT_foldApps_iff _ _ _ _ _).mp h
  exact (approxT_foldApps_iff _ _ _ _ _).mpr ⟨d, hf d hd, happ⟩

private theorem covV_approxT_lamTel_lift {E : ResolvedEnv} {ρ : EnvT} :
    ∀ (fs ds : List (Expr Nat)) (hlen : ds.length = fs.length)
      (e : Expr Nat) {c : CptT},
      ApproxT E ρ (foldApps (lamTel ds (lift 0 ds.length e)) fs) c →
      ApproxT E ρ e c
  | [], ds, hlen, e, c, h => by
      cases ds with
      | nil => simpa only [lamTel, foldApps, List.length_nil, lift_zero_idx] using h
      | cons _ _ =>
          simp only [List.length_cons, List.length_nil] at hlen
          have hf : False := by omega
          exact hf.elim
  | f :: fs, ds, hlen, e, c, h => by
      cases ds with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen
          have hf : False := by omega
          exact hf.elim
      | cons d ds =>
          have hlen' : ds.length = fs.length := Nat.succ.inj hlen
          have hh := covV_approxT_foldApps_head
            (fun _ hh => covV_approxT_beta_forward hh) h
          obtain ⟨ds', hdl, hb⟩ :=
            instantiate_lamTel_body 0 f ds (lift 0 (ds.length + 1) e)
          change ApproxT E ρ
            (foldApps (instantiate 0 f (lamTel ds (lift 0 (ds.length + 1) e))) fs) c at hh
          rw [hb, Nat.zero_add,
            instantiate_lift_cancel (ds.length + 1) 0 ds.length (lift 0 ds.length f)
              (Nat.zero_le _) (by omega) e,
            show ds.length + 1 - 1 = ds'.length by omega] at hh
          exact covV_approxT_lamTel_lift fs ds' (hdl.trans hlen') e hh

/-- An observed telescope selector yields the selected actual argument. -/
theorem covV_approxT_lamTel_bvar {E : ResolvedEnv} {ρ : EnvT} (dflt : Expr Nat) :
    ∀ (fs ds : List (Expr Nat)) (hlen : ds.length = fs.length)
      (j : Nat) (hj : j < ds.length) {c : CptT},
      ApproxT E ρ (foldApps (lamTel ds (.bvar j)) fs) c →
      ApproxT E ρ (fs.getD (fs.length - 1 - j) dflt) c
  | [], ds, hlen, j, hj, c, h => by
      cases ds with
      | nil => simp at hj
      | cons _ _ =>
          simp only [List.length_cons, List.length_nil] at hlen
          have hf : False := by omega
          exact hf.elim
  | f :: fs, ds, hlen, j, hj, c, h => by
      cases ds with
      | nil => simp at hj
      | cons d ds =>
          have hlen' : ds.length = fs.length := Nat.succ.inj hlen
          have hj' : j < ds.length + 1 := hj
          have hh := covV_approxT_foldApps_head
            (fun _ hh => covV_approxT_beta_forward hh) h
          obtain ⟨ds', hdl, hb⟩ := instantiate_lamTel_body 0 f ds (.bvar j)
          change ApproxT E ρ
            (foldApps (instantiate 0 f (lamTel ds (.bvar j))) fs) c at hh
          rw [hb, Nat.zero_add] at hh
          rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj') with rfl | hlt
          · have hfire : instantiate ds.length (lift 0 ds.length f) (.bvar ds.length) =
                lift 0 ds.length f := by
              simp only [instantiate]
              rw [if_pos trivial]
            rw [hfire, ← hdl] at hh
            have hidx : (f :: fs).length - 1 - ds'.length = 0 := by
              simp only [List.length_cons]
              have := hdl.trans hlen'
              omega
            rw [← hdl, hidx]
            exact covV_approxT_lamTel_lift fs ds' (hdl.trans hlen') f hh
          · have hfire : instantiate ds.length (lift 0 ds.length f) (.bvar j) = .bvar j := by
              simp only [instantiate]
              rw [if_neg (by omega : ¬ (j = ds.length)),
                if_neg (by omega : ¬ (ds.length < j))]
            rw [hfire] at hh
            have hidx : (f :: fs).length - 1 - j = (fs.length - 1 - j) + 1 := by
              simp only [List.length_cons]
              omega
            rw [hidx]
            exact covV_approxT_lamTel_bvar dflt fs ds' (hdl.trans hlen') j
              (by rw [hdl]; exact hlt) hh

/-- Admission aligns the legacy native redex with every structured witness
at the same recursor.  No native arguments are selected by this lemma. -/
theorem covV_iotaS_legacy_data {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) (s : IotaWitnessS E) (hr : s.recRef = w.recRef) :
    s.famMember = w.famMember ∧ s.nMinors = w.nMinors ∧
      s.preMajor.length = w.preMajor.length := by
  have hm : s.recMember = w.recMember := by
    have hh := s.hrec
    rw [hr, w.hrec] at hh
    exact (Option.some.inj hh).symm
  let cell : RecursorCellHF E w.recRef w.recMember :=
    envWfT_cellHF hW w.hrec w.hrecK
  have hd := IotaWitness.recData_admitted cell.cell.cell.adm
    cell.cell.cell.sub w rfl rfl
  have hs := IotaWitnessS.recData_admitted cell.cell.cell.adm
    cell.cell.cell.sub s hr hm
  refine ⟨hs.2.1.trans hd.2.1.symm,
    hs.2.2.2.2.trans hd.2.2.2.2.symm, ?_⟩
  have hsn := s.hnmin
  have hwn := w.hnmin
  rw [hm] at hsn
  have hsp := s.hpre
  have hwp := w.hpre
  omega

/-- The old model's Prop-singleton major independence, with its declaration
premises supplied from native admission. -/
theorem covV_approxT_prop_major_indep {E : ResolvedEnv} (hW : EnvWfT E)
    (w : IotaWitness E) (hP : piBody w.famMember.mtype = .sort .zero)
    (ρ : EnvT) (x y : Expr Nat) (c : CptT) :
    ApproxT E ρ (recCall (.const w.recRef w.ls) w.preMajor x) c ↔
      ApproxT E ρ (recCall (.const w.recRef w.ls) w.preMajor y) c := by
  apply approxT_recCall_major_indep
  · intro hh
    exact (hh _ w.hrec).2 w.hrecK
  · intro m b hd
    obtain ⟨hm, _, hnrec, _⟩ := hd
    have he : w.recMember = m := Option.some.inj (w.hrec.symm.trans hm)
    exact hnrec (he ▸ w.hrecK)
  · intro s hr
    obtain ⟨hfm, _, hpre⟩ := covV_iotaS_legacy_data hW w s hr
    refine ⟨?_, hpre⟩
    unfold PropFamilyS
    rw [hfm]
    exact hP

/-- Compose the landed ordinary-iota forward theorem with the native
legacy-to-structured witness bridge. -/
theorem covV_approxT_iota_legacy_prop_forward {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitness E)
    (hP : piBody w.famMember.mtype = .sort .zero) (hn1 : w.nMinors = 1)
    {ρ : EnvT} {c : CptT} (h : ApproxT E ρ (iotaLhsOf w) c) :
    ApproxT E ρ (iotaRhsOf w) c := by
  obtain ⟨hd⟩ := derivedIotaT_of_iotaWitness_envWfT hW w
  obtain ⟨s, hlhs, hrhs⟩ := derivedIotaT_inv hd
  have hr : s.recRef = w.recRef := by
    have hh := congrArg (fun e : Expr Nat => (appsSpine e).1) hlhs
    simp only [iotaLhsOfS, iotaLhsOf, recCall, appsSpine_foldApps_const] at hh
    exact Expr.const.inj hh |>.1
  obtain ⟨hfm, hnm, _⟩ := covV_iotaS_legacy_data hW w s hr
  have hPs : PropFamilyS s := by
    unfold PropFamilyS
    rw [hfm]
    exact hP
  rw [← hrhs]
  apply approxT_iotaS_fwd_prop s hPs (hnm.trans hn1) ρ
  rwa [hlhs]

/-- The admitted single-branch Prop schema can be instantiated at the
actual fields, after its major-independent source observation is given. -/
theorem covV_approxT_iota_prop_anyMajor {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitness E)
    (hP : piBody w.famMember.mtype = .sort .zero) (hn1 : w.nMinors = 1)
    (x : Expr Nat) {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ (recCall (.const w.recRef w.ls) w.preMajor x) c) :
    ApproxT E ρ (iotaRhsOf w) c :=
  covV_approxT_iota_legacy_prop_forward hW w hP hn1
    ((covV_approxT_prop_major_indep hW w hP ρ x (ctorMajor w) c).mp h)

/-- Forward projection observation, proved by the admitted schema and the
actual telescope selector.  The source major is arbitrary because the old
Prop rule supplies empty field demands.  The intended native instance is
`x = ctorMajor w`; no model converse is claimed. -/
theorem covV_approxT_projField_anyMajor {E : ResolvedEnv} (hW : EnvWfT E)
    {w : IotaWitness E} (hK : KFieldW w) {i : Nat}
    (hi : i < w.fields.length) (hnr : revealedPos? w i = none)
    (x : Expr Nat) {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ ((projFields w x).getD i (.sort .zero)) c) :
    ApproxT E ρ (w.fields.getD i (.sort .zero)) c := by
  obtain ⟨_, hnm1, hProp, hpk⟩ := hK
  have hflen : w.fields.length = fieldCount w := by
    have hp := w.hnpar
    show w.fields.length = piCount w.ctorMember.mtype - w.nparams
    omega
  have hilen : i < fieldCount w := hflen ▸ hi
  have hpos : 0 < fieldCount w := by omega
  let params := w.preMajor.take w.nparams
  let idxs := w.preMajor.drop (w.nparams + 1 + w.nMinors)
  have hpdef : params = w.preMajor.take w.nparams := rfl
  have hdef : idxs = w.preMajor.drop (w.nparams + 1 + w.nMinors) := rfl
  have hplen : params.length = w.nparams := by
    have hp := w.hpre
    rw [hpdef, List.length_take]
    omega
  have hxlen : idxs.length = w.nindices := by
    have hp := w.hpre
    rw [hdef, List.length_drop]
    omega
  -- entry `i` of the projection list is its canon field — not index-revealed, so a projection
  have hcf : canonField w i params idxs
        (projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
        x =
      projOne w i params idxs
        (projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
        x := by
    unfold canonField
    rw [hnr]
  have helt : (projFields w x).getD i (.sort .zero) =
      projOne w i params idxs
        (projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
        x := by
    show (projAll w (fieldCount w) _ _ _).getD i _ = _
    rw [List.getD_eq_getElem?_getD,
      projAll_getElem? (fieldCount w) i hilen _ _ _]
    exact hcf
  -- the stored constructor type does not mention the motive level
  have hlb : exprLevelsBounded w.famMember.arity w.ctorMember.mtype = true := by
    rw [← envWfT_ctorArity hW w]
    exact (envWfT_levels hW w.ctorRef w.ctorMember w.hctor).1
  have hlv : instantiateLevels (projLevels w) w.ctorMember.mtype =
      instantiateLevels w.ls w.ctorMember.mtype := by
    rw [instantiateLevels_take w.famMember.arity (projLevels w) w.ctorMember.mtype hlb,
      instantiateLevels_take w.famMember.arity w.ls w.ctorMember.mtype hlb]
    show instantiateLevels ((w.ls.set w.famMember.arity .zero).take w.famMember.arity)
        w.ctorMember.mtype = instantiateLevels (w.ls.take w.famMember.arity) w.ctorMember.mtype
    rw [Ann.take_set_of_le w.ls w.famMember.arity w.famMember.arity (Nat.le_refl _) _]
  have hci : w.ctorIdx = 0 := by have := w.hidx; omega
  -- the ι witness of the projection redex: same recursor at `projLevels`, same major
  let motᵢ := lamTel
    (peelDomsOr w.nindices
      (applyTelOr params (instantiateLevels (famLevels w) w.famMember.mtype)) ++
      [foldApps (.const w.familyRef (famLevels w))
        (params.map (lift 0 w.nindices) ++ (List.range w.nindices).reverse.map Expr.bvar)])
    (piDomOr (applyTel (params.map (lift 0 (w.nindices + 1)) ++
      projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
      (instantiateLevels w.ls w.ctorMember.mtype)))
  let mnᵢ := lamTel
    (peelDomsOr (fieldCount w + recCountOf w.kinds)
      (minorTel motᵢ w.nparams (foldApps (.const w.ctorRef (famLevels w)) params) w.kinds
        (applyTelOr params (instantiateLevels w.ls w.ctorMember.mtype))))
    (.bvar (fieldCount w + recCountOf w.kinds - 1 - minorPosOf w.kinds i))
  let wᵢ : IotaWitness E :=
    { w with
      ls := projLevels w
      preMajor := params ++ [motᵢ, mnᵢ] ++ idxs
      minor := mnᵢ
      hlsLen := by
        show (w.ls.set w.famMember.arity .zero).length = w.recMember.arity
        rw [List.length_set]; exact w.hlsLen
      hpre := by
        simp only [List.length_append, List.length_cons, List.length_nil, hplen, hxlen]
        omega
      hminor := by
        rw [hci]
        rw [List.getElem?_append_left
          (by simp only [List.length_append, List.length_cons, List.length_nil, hplen]; omega)]
        rw [List.getElem?_append_right (by omega), hplen,
          show w.nparams + 1 + 0 - w.nparams = 1 by omega]
        rfl
      hctorAfter := by
        rw [List.take_append_of_le_length
          (by simp only [List.length_append, List.length_cons, List.length_nil, hplen]; omega),
          List.take_left' hplen, hlv]
        exact w.hctorAfter }
  -- `projOne` unfolds to exactly this redex
  have hpo : projOne w i params idxs
        (projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
        x =
      recCall (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        x := rfl
  -- ι's contractum is `mnᵢ` applied to `rhsArgs`: the fields interleaved with one recursive
  -- call after each `directRec` field (`nb = fieldCount + recCountOf` arguments)
  have hrhs : iotaRhsOf wᵢ = foldApps mnᵢ
      (rhsArgs (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        w.nparams w.nMinors w.fields w.kinds w.ctorAfterParams) := rfl
  -- the minor is `λ (minorTel binders). bvar (nb-1-minorPosOf i)`; its binder count is `nb`
  have hAT : applyTelOr params (instantiateLevels w.ls w.ctorMember.mtype) =
      w.ctorAfterParams := by
    show (applyTel params (instantiateLevels w.ls w.ctorMember.mtype)).getD _ = _
    rw [hpdef, w.hctorAfter]
    rfl
  have hkl : w.kinds.length = fieldCount w := by
    have h1 := w.hlen
    rw [hflen] at h1
    exact h1
  obtain ⟨ds, _, hpl, hdl⟩ := peelPis_of_isPiTel
      (w.kinds.length + recCountOf w.kinds)
      (minorTel motᵢ w.nparams (foldApps (.const w.ctorRef (famLevels w)) params) w.kinds
        (applyTelOr params (instantiateLevels w.ls w.ctorMember.mtype)))
      (isPiTel_minorTel w.nparams motᵢ
        (foldApps (.const w.ctorRef (famLevels w)) params) w.kinds _
        (by rw [hAT]; exact w.hctorTel))
  rw [hkl] at hpl hdl
  have hmn : mnᵢ = lamTel ds
      (.bvar (fieldCount w + recCountOf w.kinds - 1 - minorPosOf w.kinds i)) := by
    show lamTel (peelDomsOr _ _) _ = _
    unfold peelDomsOr
    rw [hpl]
  rw [helt, hpo] at h
  have hh : ApproxT E ρ (iotaRhsOf wᵢ) c :=
    covV_approxT_iota_prop_anyMajor hW wᵢ hProp hnm1 x h
  rw [hrhs] at hh
  conv at hh => arg 3; arg 1; rw [hmn]
  have harglen : (rhsArgs (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        w.nparams w.nMinors w.fields w.kinds w.ctorAfterParams).length =
      fieldCount w + recCountOf w.kinds := by
    rw [rhsArgs_length _ _ _ _ w.fields w.kinds w.ctorAfterParams w.hlen w.hctorTel, hflen]
  have hpm : minorPosOf w.kinds i < w.kinds.length + recCountOf w.kinds :=
    minorPosOf_lt w.kinds i (by rw [hkl]; exact hilen)
  have hout := covV_approxT_lamTel_bvar (E := E) (ρ := ρ) (.sort .zero)
      (rhsArgs (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        w.nparams w.nMinors w.fields w.kinds w.ctorAfterParams)
      ds (hdl.trans harglen.symm)
      (fieldCount w + recCountOf w.kinds - 1 - minorPosOf w.kinds i) (by omega) hh
  have hix : (rhsArgs (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        w.nparams w.nMinors w.fields w.kinds w.ctorAfterParams).length - 1 -
        (fieldCount w + recCountOf w.kinds - 1 - minorPosOf w.kinds i) =
      minorPosOf w.kinds i := by
    rw [harglen]
    have hpm' := hpm
    rw [hkl] at hpm'
    omega
  rw [hix] at hout
  rw [rhsArgs_getD_minorPos _ _ _ _ _ w.fields w.kinds w.ctorAfterParams i
    w.hlen w.hctorTel hi] at hout
  exact hout

/-- Non-revealed projections in the old Prop rule have only bottom
observations.  The proof may instantiate the same declaration schema at a
uniformly bottom-observed field term; the native projection expression does
not depend on the witness's actual field list. -/
theorem covV_approxT_projField_bot {E : ResolvedEnv} (hW : EnvWfT E)
    {w : IotaWitness E} (hK : KFieldW w) {i : Nat}
    (hi : i < w.fields.length) (hnr : revealedPos? w i = none)
    (x : Expr Nat) {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ ((projFields w x).getD i (.sort .zero)) c) : c = .bot := by
  let w₀ : IotaWitness E :=
    { w with
      fields := List.replicate w.fields.length polyIdProof
      hlen := by simpa only [List.length_replicate] using w.hlen
      hnpar := by simpa only [List.length_replicate] using w.hnpar
      hpeel := by simpa only [List.length_replicate] using w.hpeel }
  have hK₀ : KFieldW w₀ := by
    refine ⟨?_, hK.2.1, hK.2.2.1, hK.2.2.2⟩
    intro he
    have hl := congrArg List.length he
    change (List.replicate w.fields.length polyIdProof).length = [].length at hl
    simp only [List.length_replicate, List.length_nil] at hl
    exact hK.1 (List.length_eq_zero.mp hl)
  have hi₀ : i < w₀.fields.length := by
    simpa only [w₀, List.length_replicate] using hi
  have hnr₀ : revealedPos? w₀ i = none := hnr
  have hAll : ∀ (k : Nat) (ps ix : List (Expr Nat)) (z : Expr Nat),
      projAll w₀ k ps ix z = projAll w k ps ix z := by
    intro k
    induction k with
    | zero => intro ps ix z; rfl
    | succ k ih =>
        intro ps ix z
        simp only [projAll, ih] <;> rfl
  have he : projFields w₀ x = projFields w x :=
    hAll (fieldCount w) (w.preMajor.take w.nparams)
      (w.preMajor.drop (w.nparams + 1 + w.nMinors)) x
  have hh : ApproxT E ρ ((projFields w₀ x).getD i (.sort .zero)) c := by
    rwa [he]
  have hout := covV_approxT_projField_anyMajor hW hK₀ hi₀ hnr₀ x hh
  have hget : w₀.fields.getD i (.sort .zero) = polyIdProof := by
    change (List.replicate w.fields.length polyIdProof).getD i (.sort .zero) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]
    rfl
  rw [hget] at hout
  exact approxT_polyIdProof_bot E ρ hout

/-- Required observation direction in the old guarded model. -/
theorem covV_approxTK_proj_ctor {E : ResolvedEnv} (hW : EnvWfT E)
    {w : IotaWitness E} (hK : KFieldW w) {i : Nat}
    (hi : i < w.fields.length) (hnr : revealedPos? w i = none)
    {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTK E n Γ ρ
      ((projFields w (ctorMajor w)).getD i (.sort .zero)) c) :
    ApproxTK E n Γ ρ (w.fields.getD i (.sort .zero)) c := by
  have hc := covV_approxT_projField_bot hW hK hi hnr (ctorMajor w)
    (approxTK_forget h)
  subst c
  exact .bot _ _ _

/-- Required observation direction in the aligned source model. -/
theorem covV_approxTN_proj_ctor {E : ResolvedEnv} (hW : EnvWfT E)
    {w : IotaWitness E} (hK : KFieldW w) {i : Nat}
    (hi : i < w.fields.length) (hnr : revealedPos? w i = none)
    {ρ : EnvT} {c : CptT}
    (h : ApproxTN E ρ ((projFields w (ctorMajor w)).getD i (.sort .zero)) c) :
    ApproxTN E ρ (w.fields.getD i (.sort .zero)) c := by
  have hc := covV_approxT_projField_bot hW hK hi hnr (ctorMajor w)
    (approxTN_forget h)
  subst c
  exact .bot _ _

/-- Required observation direction in the aligned guarded model, at exactly
the same compact.  This is general over the admitted environment, native
redex, valuation, context, and arity. -/
theorem covV_approxTKN_proj_ctor {E : ResolvedEnv} (hW : EnvWfT E)
    {w : IotaWitness E} (hK : KFieldW w) {i : Nat}
    (hi : i < w.fields.length) (hnr : revealedPos? w i = none)
    {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKN E n Γ ρ
      ((projFields w (ctorMajor w)).getD i (.sort .zero)) c) :
    ApproxTKN E n Γ ρ (w.fields.getD i (.sort .zero)) c := by
  have hc := covV_approxT_projField_bot hW hK hi hnr (ctorMajor w)
    (approxTN_forget (approxTKN_forgetN h))
  subst c
  exact .bot _ _ _

/-- The actual field target agrees with the landed native projection
readback, and the aligned observation is transported to that same target. -/
theorem covV_proj_ctor_native_and_observed {E : ResolvedEnv} (hW : EnvWfT E)
    {w : IotaWitness E} (hK : KFieldW w) {i : Nat}
    (hi : i < w.fields.length) (hnr : revealedPos? w i = none)
    {n : Nat} {Γ : LCtx} {ρ : EnvT} {c : CptT}
    (h : ApproxTKN E n Γ ρ
      ((projFields w (ctorMajor w)).getD i (.sort .zero)) c) :
    RedR (WhStepCK E) Γ
      ((projFields w (ctorMajor w)).getD i (.sort .zero))
      (w.fields.getD i (.sort .zero)) ∧
    ApproxTKN E n Γ ρ (w.fields.getD i (.sort .zero)) c :=
  ⟨redR_projField_ctorMajor hW hK hi hnr,
    covV_approxTKN_proj_ctor hW hK hi hnr h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_V_PROJECTION_ROOTS
#print axioms covV_approxT_beta_forward
#print axioms covV_approxT_lamTel_bvar
#print axioms covV_iotaS_legacy_data
#print axioms covV_approxT_prop_major_indep
#print axioms covV_approxT_iota_legacy_prop_forward
#print axioms covV_approxT_iota_prop_anyMajor
#print axioms covV_approxT_projField_anyMajor
#print axioms covV_approxT_projField_bot
#print axioms covV_approxTK_proj_ctor
#print axioms covV_approxTN_proj_ctor
#print axioms covV_approxTKN_proj_ctor
#print axioms covV_proj_ctor_native_and_observed
-- END RCIC_NATIVE_TYPED_MODEL_COV_V_PROJECTION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovVAudit
