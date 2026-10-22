import rcic.RcicSynSRDeltaClosed

/-!
# `RcicSynSRDeltaClosedField` — row 5 `es_delta` full field at `Aw := admW`, generic table

cc 23:35Z landed-file repair: `RcicSynSRDeltaClosed` landed on main via
#7829 @829c0359e9 (batch 259), so the §2 delta appended there by
31a8a2f1e5 is moved here VERBATIM — same declarations, same proofs, no
content change. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §2 the generic-`tbl` restatement — proof branch, full field, tableOfK transfer

cc 17:15Z: (1) the proof branch (`levelIsZero (σ hb.reg.1) = true`) closes
by the same StepIH mechanism — its two ports are `Goal .cl dl canonL`
(`cl_deltaCanonL_before`) and `Goal .pb hb hb.reg.2`
(`pb_deltaReg_before`: `hb`'s reg derivation is a strict sub-measure via
`TyP.wt_reg_le`, so `dmStep_pair_below` gives `Before` at the canonical
display); `hR`/`hpb`-by-issues inside `delta_proof_caseStep_of_ports`
stay `delta_issued_cl`. (2) The tableOfK transfer is a restatement over
any `(tblI : List CRule) (I : TableOfICompat S.env tblI)` — the memberCoh
discharge is table-generic (`Goal tblI`, `Before` is table-free);
instantiating `I := tableOfICompat_tableOfK hW` (glm-sr4-tablek
`e7da62df44`, unlanded, not reachable from this branch) yields the
`es_delta` cell at `tableOfK hW` verbatim. -/

/-- `Before` the δ node: `.pb hb hb.reg.2` — `hb` is a strict subderivation
    and `hb.reg.2`'s weight is dominated by `hb`'s (`TyP.wt_reg_le`). -/
theorem pb_deltaReg_before (Aw : Nat → Nat) {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) :
    Before Aw
      (.pb hb hb.reg.2 S σ (S.can σ))
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) := by
  have hdm : DMStep
      (hb.atoms Aw ++ hb.reg.2.atoms Aw)
      ((CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).atoms Aw) := by
    have hat : (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).atoms Aw =
        [(CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt Aw] := by
      simp only [CvP.atoms]
    rw [hat, ← List.append_nil (hb.atoms Aw ++ hb.reg.2.atoms Aw)]
    refine dmStep_of_below fun y hy => ?_
    rcases List.mem_append.mp hy with hy | hy
    · exact atoms_lt_of_wt_lt Aw hb (by simp only [CvP.wt]; omega) y hy
    · exact atoms_lt_of_wt_lt Aw hb.reg.2
        (Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw hb) (by simp only [CvP.wt]; omega))
        y hy
  exact before_of_same_prefix Aw rfl
    (lexDM_combMeas_mono Aw _ (Prod.Lex.left _ _ hdm))

/-- The kept branch at a generic `TableOfICompat` table: identical body to
    `es_delta_kept_memberCoh_tableOfI` with `I` for the compat instance —
    `hL`/`hB` are `ih` answers, `hag` is `AgreeOn`-refl at `admW`. -/
theorem es_delta_kept_admW_tableI {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    {tblI : List CRule} (I : TableOfICompat S.env tblI)
    (hu : levelIsZero (σ hb.reg.1) = false) :
    CaseStep (enrichEnvWfT S.env).admW tblI
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) := by
  intro hq ih
  have hap : hb.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref := hq.ap
  have hL : Goal tblI
      (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ)) :=
    (ih _ (Demand.rootCl dl (deltaCanonL hres hlen hwf hb) hap.2.1
        (assumpPref_reg hap.1) S σ hq.hom)
      (cl_deltaCanonL_before (enrichEnvWfT S.env).admW hres hbody htr hlen
        hwf hb dl dr S σ)).2
  have hB : Goal tblI
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ (S.can σ)) :=
    (ih _ (Demand.rootCl _ hb
        (assumpPref_deltaBodyInst S.env hres hbody hlen hwf Γ
          (deltaAdmDb_assumpPref (enrichEnvWfT S.env) hres hbody htr
            (srDelta_defAdm_assumpPref S.env hres hbody htr)))
        hap.1 S σ hq.hom)
      (cl_deltaDbΓ_before (enrichEnvWfT S.env).admW hres hbody htr hlen hwf
        hb dl dr S σ (fun _ _ _ ↦ rfl))).2
  exact delta_kept_caseStep_tableI hres hbody htr hlen hwf hb dl dr S σ I hu
    (fun _ _ _ ↦ rfl) (srDelta_defAdm_assumpPref S.env hres hbody htr)
    hL hB hq ih

/-- The proof branch (`levelIsZero (σ hb.reg.1) = true`) at a generic table:
    `hL : Goal .cl dl canonL` and `hpb : Goal .pb hb hb.reg.2` are `ih`
    answers — no occurrence-path premise needed, `Demand.rootPb` +
    `pb_deltaReg_before` supply the bit query at the canonical display. -/
theorem es_delta_proof_admW_tableI {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    {tblI : List CRule}
    (hu : levelIsZero (σ hb.reg.1) = true) :
    CaseStep (enrichEnvWfT S.env).admW tblI
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) := by
  intro hq ih
  have hap : hb.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref := hq.ap
  have hL : Goal tblI
      (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ)) :=
    (ih _ (Demand.rootCl dl (deltaCanonL hres hlen hwf hb) hap.2.1
        (assumpPref_reg hap.1) S σ hq.hom)
      (cl_deltaCanonL_before (enrichEnvWfT S.env).admW hres hbody htr hlen
        hwf hb dl dr S σ)).2
  have hpb : Goal tblI (.pb hb hb.reg.2 S σ (S.can σ)) :=
    (ih _ (Demand.rootPb hb hb.reg.2 hap.1 (assumpPref_reg hap.1)
        S σ hq.hom)
      (pb_deltaReg_before (enrichEnvWfT S.env).admW hres hbody htr hlen hwf
        hb dl dr S σ)).2
  exact delta_proof_caseStep_of_ports (enrichEnvWfT S.env).admW tblI
    hres hbody htr hlen hwf hb dl dr S σ (S.can σ) hu hL hpb hq ih

/-- **THE FULL `es_delta` FIELD at `Aw := admW`**, generic
    `TableOfICompat` table — no wall premise, no branch guard premise:
    the `CaseStep` itself dispatches on `levelIsZero (σ hb.reg.1)`.
    At `I := tableOfICompat_tableOfK hW` (glm-sr4-tablek `e7da62df44`,
    unlanded) this is the `es_delta` cell at `tableOfK hW`. -/
theorem es_delta_admW_tableI {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    {tblI : List CRule} (I : TableOfICompat S.env tblI) :
    CaseStep (enrichEnvWfT S.env).admW tblI
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) := by
  intro hq ih
  cases hu : levelIsZero (σ hb.reg.1) with
  | false =>
      exact es_delta_kept_admW_tableI hres hbody htr hlen hwf hb dl dr S σ
        I hu hq ih
  | true =>
      exact es_delta_proof_admW_tableI hres hbody htr hlen hwf hb dl dr S σ
        hu hq ih

/-- The full `es_delta` field at `tableOfI S.env`, `Aw := admW`. -/
theorem es_delta_admW_tableOfI {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) :
    CaseStep (enrichEnvWfT S.env).admW (tableOfI S.env)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) :=
  es_delta_admW_tableI hres hbody htr hlen hwf hb dl dr S σ
    (tableOfICompat_tableOfI S.env)

/-- The `tableOfI hW` pin of the full field at `admW`. -/
noncomputable def es_delta_admW_tableOfI_pin {E : ResolvedEnv}
    (hW : EnvWfT E) {Eₐ : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hext : EnvExt E Eₐ) (hctx : CtxWfT E n Γ) (σ : Level → Level) :
    CaseStep (enrichEnvWfT hW).admW (tableOfI hW)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        ⟨hW, hext, hctx⟩ σ
        ((⟨hW, hext, hctx⟩ : ScopedCtx Eₐ E n Γ).can σ)) :=
  es_delta_admW_tableOfI hres hbody htr hlen hwf hb dl dr
    ⟨hW, hext, hctx⟩ σ

/-- NON-VACUITY: the full field end-to-end on the fixture — premises =
    field data only, no branch guard. -/
theorem srDeltaEs_admW_closed_fixture :
    CaseStep srDeltaAdmW (tableOfI srDeltaFixtureEnvWfT)
      (.es (CvP.delta srDeltaFixtureEnv 0 [] 7 [] srDeltaFixtureMember
        (.sort .zero) srDeltaHres srDeltaHbody srDeltaHtr srDeltaHlen
        srDeltaHwf srDeltaHb srDeltaDl srDeltaHb)
        srDeltaScope id (srDeltaScope.can id)) :=
  es_delta_admW_tableOfI srDeltaHres srDeltaHbody srDeltaHtr srDeltaHlen
    srDeltaHwf srDeltaHb srDeltaDl srDeltaHb srDeltaScope id

#print axioms Rcic.Syn.es_delta_kept_admW_tableOfI
#print axioms Rcic.Syn.es_delta_kept_admW_tableOfI_pin
#print axioms Rcic.Syn.srDeltaEsKept_admW_closed_fixture
#print axioms Rcic.Syn.pb_deltaReg_before
#print axioms Rcic.Syn.es_delta_kept_admW_tableI
#print axioms Rcic.Syn.es_delta_proof_admW_tableI
#print axioms Rcic.Syn.es_delta_admW_tableI
#print axioms Rcic.Syn.es_delta_admW_tableOfI
#print axioms Rcic.Syn.es_delta_admW_tableOfI_pin
#print axioms Rcic.Syn.srDeltaEs_admW_closed_fixture


end Rcic.Syn
