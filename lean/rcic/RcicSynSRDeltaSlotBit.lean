import rcic.RcicSynStepSkeleton
import rcic.RcicSynAdm
import rcic.RcicSynDeltaBeta
import rcic.RcicSynMSAP

/-!
# `RcicSynSRDeltaSlotBit` — `DeltaSlotBitWall` discharged via `StepIH` at `admW`

cc 17:15Z (glm-sr1, row 2): issue the member-admission comparison through
`StepIH` at `admW`, as glm-sr3 did for the `.cl` legs of `es_delta`
(`RcicSynSRDeltaMemberCoh`, branch `glm/sr3-convb`, #7829 — **dependency
stated, not imported**: that head has not landed on `main`; the small
rank fact sr3 names `typeAdm_atoms_lt` is inlined below, same proof).

`DeltaSlotBitWall` asks `eqN u (instLevel ls₀ u₀)` between an in-context
typing `TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)` (below the
node — at the kept-δ site it is `dl.reg.2`) and the member's admitted
sort typing (`memberSortP_of_envWfT`, EnvWfT-prefix). The comparison is
exactly a `.bitCoh` query — `BitCoh σ D₁ D₂ = levelIsZero (σ u) =
levelIsZero (σ v)` — public/demandable where `.slot` is not
(`slot_not_demanded`).

* `bitCoh_memberSort_delta_before`: the `.bitCoh` pair is `Before` the
  kept-δ node. `dl.reg.2`'s atoms sit below `dl.wt` (`wt_reg_le` +
  `atoms_lt_of_wt_lt`), hence below the node's own atom. The member-side
  derivation is `instMemberSortP`'s `linst`/`wkClosed`-over-`ewk` tower
  — `wk`/`linst`/`ewk` add no atoms, so its atoms are `typeAdm.hT`'s,
  each `< Aw r` under the `AgreeOn` receipt (`a.lt` at `admW`,
  `wt_congr`/`agreeOn_mono` transport, `hag` closes), and `Aw r` is
  dominated by `dl`'s `.const`-subject weight (`admW_lt_of_const`).
* `slotBit_memberSort_goal`: inside the kept-δ `CaseStep`, the
  `BitCoh` goal is an `ih` answer — `Demand.rootBitCoh` needs only
  `AssumpPref` (`assumpPref_reg` on `dl`, `assumpPref_instMemberSortP`
  on `memberSortP_of_envWfT_ap`), and `Before` is the lemma above.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- **Before the kept-δ node:** `.bitCoh dl.reg.2 (instMemberSortP …).2`.
    The in-context leg is bounded through `dl.reg.2.wt ≤ dl.wt < wt δ`;
    the member leg's atoms are `typeAdm.hT`'s (`linst`/`wk`/`ewk` add
    none), each `< Aw r` under `hag`, and `Aw r < dl.wt` via the
    `.const r` subject (`admW_lt_of_const`). Mirrors sr3's
    `cl_deltaDbΓ_before`; the `typeAdm_atoms_lt` step is inlined. -/
theorem bitCoh_memberSort_delta_before (Aw : Nat → Nat) {Eₐ E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW) :
    Before Aw
      (.bitCoh dl.reg.2
        (instMemberSortP (envClosed_of_envWfT S.env)
          (memberSortP_of_envWfT S.env) Γ hres hlen hwf).2
        S σ (S.can σ))
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) := by
  have hdm : DMStep
      (dl.reg.2.atoms Aw ++
        (instMemberSortP (envClosed_of_envWfT S.env)
          (memberSortP_of_envWfT S.env) Γ hres hlen hwf).2.atoms Aw)
      ((CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).atoms Aw) := by
    have hat : (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).atoms Aw =
        [(CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt Aw] := by
      simp only [CvP.atoms]
    rw [hat, ← List.append_nil (dl.reg.2.atoms Aw ++ _)]
    refine dmStep_of_below fun y hy => ?_
    rcases List.mem_append.mp hy with hy | hy
    · have hw : dl.reg.2.wt Aw <
          (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt Aw :=
        Nat.lt_of_le_of_lt (TyP.wt_reg_le Aw dl) (by simp only [CvP.wt]; omega)
      exact atoms_lt_of_wt_lt Aw dl.reg.2 hw y hy
    · have hatoms : (instMemberSortP (envClosed_of_envWfT S.env)
          (memberSortP_of_envWfT S.env) Γ hres hlen hwf).2.atoms Aw =
          ((enrichEnvWfT S.env).typeAdm hres).hT.atoms Aw := by
        dsimp only [instMemberSortP]
        rw [atoms_wkClosed]
        rfl
      rw [hatoms] at hy
      have hle := TyP.atoms_le Aw ((enrichEnvWfT S.env).typeAdm hres).hT y hy
      rw [TyP.wt_congr ((enrichEnvWfT S.env).typeAdm hres).hT
        (agreeOn_mono ((enrichEnvWfT S.env).typeAdm hres).ext hag)] at hle
      have hylt : y < (enrichEnvWfT S.env).admW r :=
        Nat.lt_of_le_of_lt hle ((enrichEnvWfT S.env).typeAdm hres).lt
      have hAw : Aw r < dl.wt Aw := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
      have hdlw : dl.wt Aw <
          (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt Aw := by
        simp only [CvP.wt]; omega
      have hagr : Aw r = (enrichEnvWfT S.env).admW r := hag r m hres
      omega
  exact before_of_same_prefix Aw rfl
    (lexDM_combMeas_mono Aw _ (Prod.Lex.left _ _ hdm))

/-- **The `DeltaSlotBitWall` discharge:** inside the kept-δ `CaseStep`,
    the bit equation `levelIsZero (σ dl.reg.1) = levelIsZero (σ
    (instLevel ls u₀))` — `Goal` of the `.bitCoh` query pairing `dl`'s
    regularity leg with the member's admitted sort typing — is an `ih`
    answer at `admW` (`Demand.rootBitCoh` +
    `bitCoh_memberSort_delta_before`). -/
theorem slotBit_memberSort_goal (Aw : Nat → Nat) {tbl : List CRule}
    {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hAP : dl.AssumpPref) (hσ : LevelHom σ)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW)
    (ih : StepIH Aw tbl
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ))) :
    Goal tbl
      (.bitCoh dl.reg.2
        (instMemberSortP (envClosed_of_envWfT S.env)
          (memberSortP_of_envWfT S.env) Γ hres hlen hwf).2
        S σ (S.can σ)) :=
  (ih _
    (Demand.rootBitCoh dl.reg.2 _
      (assumpPref_reg hAP)
      (assumpPref_instMemberSortP (envClosed_of_envWfT S.env)
        (memberSortP_of_envWfT S.env) (memberSortP_of_envWfT_ap S.env)
        Γ hres hlen hwf)
      S σ hσ)
    (bitCoh_memberSort_delta_before Aw hres hbody htr hlen hwf hb dl dr S σ
      hag)).2

end Rcic.Syn

#print axioms Rcic.Syn.bitCoh_memberSort_delta_before
#print axioms Rcic.Syn.slotBit_memberSort_goal
