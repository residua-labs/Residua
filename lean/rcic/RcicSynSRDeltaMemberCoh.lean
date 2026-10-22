import rcic.RcicSynSRDelta
import rcic.RcicSynStepSkeleton
import rcic.RcicSynDeltaKeptES
import rcic.RcicSynStepFieldsDeltaIota
import rcic.RcicSynDeltaBeta
import rcic.RcicSynAdm

/-!
# `RcicSynSRDeltaMemberCoh` — the member-admission link, discharged inside `es_delta`'s `CaseStep`

cc 14:55Z item: the common link between two lanes — a uniqueness obligation
comparing (a) a typing below the current derivation node with (b) an admitted
typing of an environment member from an `EnvWfT` prefix. The measured answer:

* **No env-prefix induction is needed — and none is well-formed.** `EnvWfP.typeAdm` /
  `EnvWfP.defAdm` already place the admitted typing **at the target env `E`**:
  each stores `hv : TyP E₀ · [] · ·` in the admitted prefix `E₀` *plus*
  `ext : EnvExt E₀ E`, and every consumer (`deltaAdmDb`, `instMemberSortP`)
  transports prefix→extension by `TyP.ewk`. The reverse direction —
  strengthening a given `E`-typing back into `E₀` — is never used; the
  `EnvWfT` induction cc asked about is already compiled into `admW`
  (`a.lt : hv.wt admW < admW r`, the member's own slot paying for its
  admission derivation, `RcicSynAdm` §1).
* **`memberSortCoh` is therefore a rank fact, not an env fact:**
  `defAdm_atoms_lt`/`typeAdm_atoms_lt` — under the `AgreeOn` receipt every
  atom of the admitted leg is `< Aw r`, hence `< D.wt` for any `.const r`-
  subject typing (`admW_lt_of_const`) and below the δ node. So `.cl`/`.bitCoh`
  queries pairing the admission leg with a node leg are `Before`-below the
  issuing node; `StepIH` answers *every* `Demand`+`Before` query
  (`Demand.rootCl`/`rootBitCoh` at the canonical display `S.can σ`), whether
  or not an `Issues` edge exists. The leg was never an un-formable boundary.
* **Discharge:** `es_delta_kept_memberCoh_tableOfI` proves the kept-δ
  `CaseStep` at `tableOfI S.env` from `hag` (+ field data `hu`) alone: the
  `hL`/`hB` `Goal .cl` fields of `esDeltaKeptWall` are `ih` answers.
  The wall's `.cl`-content collapses; its real residual is `hag` alone
  (inhabited at `Aw := admW`, refuted at `Aw := 0` — §5 of `RcicSynSRDelta`).
  `esDeltaKeptWall` is landed and not edited; this is the additive layer.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 cast/adapter lemmas -/

/-- `AssumpPref` transports across the level-arity cast. -/
theorem castArityZero_assumpPref {E : ResolvedEnv} {a : Nat} {Γ : LCtx}
    {b T : Expr Nat} (ha : a = 0) {D : TyP E 0 Γ b T} (hD : D.AssumpPref) :
    (castArityZero ha D).AssumpPref := by
  cases ha
  exact hD

/-- The arity cast adds no atoms. -/
theorem castArityZero_atoms (Aw : Nat → Nat) {E : ResolvedEnv} {a : Nat}
    {Γ : LCtx} {b T : Expr Nat} (ha : a = 0) (D : TyP E 0 Γ b T) :
    (castArityZero ha D).atoms Aw = D.atoms Aw := by
  cases ha; rfl

/-- The admitted body adapter `deltaAdmDb` (`castArityZero` of the prefix
    `ewk`) is `AssumpPref` from the `defAdm` leg's own `AssumpPref`. -/
theorem deltaAdmDb_assumpPref {E : ResolvedEnv} (hE : EnvWfP E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true)
    (hap : (hE.defAdm hres hbody htr).hv.AssumpPref) :
    (deltaAdmDb hE hres hbody htr).AssumpPref := by
  have hewk : (TyP.ewk (hE.defAdm hres hbody htr).E₀ E 0 [] b m.mtype
      (hE.defAdm hres hbody htr).ext (hE.defAdm hres hbody htr).hv).AssumpPref :=
    hap
  exact castArityZero_assumpPref (hE.defAdm hres hbody htr).arity hewk

/-- `dbΓ`'s atoms are the selected admission's atoms: `deltaBodyInst`'s
    `linst`/`wkClosed` wrappers and `deltaAdmDb`'s `ewk`/cast all flatten. -/
theorem deltaDbΓ_atoms_adm (Aw : Nat → Nat) {E : ResolvedEnv}
    (hE : EnvWfT E) {n : Nat} (Γ : LCtx) {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) :
    (deltaDbΓ hE Γ hres hbody hlen hwf
      (deltaAdmDb (enrichEnvWfT hE) hres hbody htr)).atoms Aw =
      ((enrichEnvWfT hE).defAdm hres hbody htr).hv.atoms Aw := by
  rw [deltaDbΓ_atoms]
  show (castArityZero ((enrichEnvWfT hE).defAdm hres hbody htr).arity
    (TyP.ewk ((enrichEnvWfT hE).defAdm hres hbody htr).E₀ E 0 [] b m.mtype
      ((enrichEnvWfT hE).defAdm hres hbody htr).ext
      ((enrichEnvWfT hE).defAdm hres hbody htr).hv)).atoms Aw = _
  rw [castArityZero_atoms]
  rfl

/-! ## §2 the member-admission ranking lemmas (`memberSortCoh`'s measure content) -/

/-- Every atom of a member's admitted **body** derivation is below `Aw r` at
    the record's `Aw` (under the `AgreeOn` receipt): `defAdm.lt` bounds it at
    `admW`, `wt_congr` transports the bound, `hag` closes at `r`. -/
theorem defAdm_atoms_lt {E : ResolvedEnv} {Aw admW : Nat → Nat} {r : Nat}
    {m : CheckedMember} {b : Expr Nat} (a : DefAdm E admW r m b)
    (hag : AgreeOn E Aw admW) (hres : E.members r = some m) :
    ∀ y ∈ a.hv.atoms Aw, y < Aw r := by
  intro y hy
  have hle := TyP.atoms_le Aw a.hv y hy
  rw [TyP.wt_congr a.hv (agreeOn_mono a.ext hag)] at hle
  rw [hag r m hres]
  exact Nat.lt_of_le_of_lt hle a.lt

/-- Same for a member's admitted **stored type** derivation — the
    `memberSortCoh`/`DeltaSlotBitWall` side: a `.bitCoh`/`slot` leg pairing a
    member typing with an in-context typing is dominated by `Aw r`. -/
theorem typeAdm_atoms_lt {E : ResolvedEnv} {Aw admW : Nat → Nat} {r : Nat}
    {m : CheckedMember} (a : TypeAdm E admW r m)
    (hag : AgreeOn E Aw admW) (hres : E.members r = some m) :
    ∀ y ∈ a.hT.atoms Aw, y < Aw r := by
  intro y hy
  have hle := TyP.atoms_le Aw a.hT y hy
  rw [TyP.wt_congr a.hT (agreeOn_mono a.ext hag)] at hle
  rw [hag r m hres]
  exact Nat.lt_of_le_of_lt hle a.lt

/-! ## §3 the two `.cl` queries are `Before` the δ node -/

/-- `Before` the kept-δ node: `.cl dl canonL`. `dl`'s atoms are bounded by its
    own weight, `canonL`'s single atom by `deltaCanonL_wt_lt`; both drop the
    node's one atom via `dmStep_of_below`. -/
theorem cl_deltaCanonL_before (Aw : Nat → Nat) {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) :
    Before Aw
      (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ))
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) := by
  have hdm : DMStep
      (dl.atoms Aw ++ (deltaCanonL hres hlen hwf hb).atoms Aw)
      ((CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).atoms Aw) := by
    have hat : (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).atoms Aw =
        [(CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt Aw] := by
      simp only [CvP.atoms]
    rw [hat, ← List.append_nil
      (dl.atoms Aw ++ (deltaCanonL hres hlen hwf hb).atoms Aw)]
    refine dmStep_of_below fun y hy => ?_
    rcases List.mem_append.mp hy with hy | hy
    · exact atoms_lt_of_wt_lt Aw dl (by simp only [CvP.wt]; omega) y hy
    · exact atoms_lt_of_wt_lt Aw (deltaCanonL hres hlen hwf hb)
        (deltaCanonL_wt_lt Aw hres hbody htr hlen hwf hb dl dr) y hy
  exact before_of_same_prefix Aw rfl
    (lexDM_combMeas_mono Aw _ (Prod.Lex.left _ _ hdm))

/-- `Before` the kept-δ node: `.cl dbΓ hb`. The admitted body's atoms are
    dominated by `Aw r` (`defAdm_atoms_lt` under `hag`), which `dl`'s
    `.const`-subject weight dominates; `hb`'s atoms are bounded by `hb.wt`. -/
theorem cl_deltaDbΓ_before (Aw : Nat → Nat) {Eₐ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW) :
    Before Aw
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
          (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ (S.can σ))
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) := by
  have hdm : DMStep
      ((deltaDbΓ S.env Γ hres hbody hlen hwf
          (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)).atoms Aw ++
        hb.atoms Aw)
      ((CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).atoms Aw) := by
    have hat : (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).atoms Aw =
        [(CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt Aw] := by
      simp only [CvP.atoms]
    rw [hat, ← List.append_nil (_ ++ hb.atoms Aw)]
    refine dmStep_of_below fun y hy => ?_
    rcases List.mem_append.mp hy with hy | hy
    · rw [deltaDbΓ_atoms_adm Aw S.env Γ hres hbody htr hlen hwf] at hy
      have hmem := defAdm_atoms_lt
        ((enrichEnvWfT S.env).defAdm hres hbody htr) hag hres y hy
      have hAw : Aw r < dl.wt Aw := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
      have hdlw : dl.wt Aw <
          (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt Aw := by
        simp only [CvP.wt]; omega
      omega
    · exact atoms_lt_of_wt_lt Aw hb (by simp only [CvP.wt]; omega) y hy
  exact before_of_same_prefix Aw rfl
    (lexDM_combMeas_mono Aw _ (Prod.Lex.left _ _ hdm))

/-! ## §4 the CaseStep with the `.cl` legs as `ih` answers -/

/-- **The `memberSortCoh` discharge for row 5:** `es_delta` kept at
    `tableOfI S.env` needs only `hag` (the `Aw`-receipt) and field data —
    `hL : Goal (.cl dl canonL)` and `hB : Goal (.cl dbΓ hb)` are `ih` answers:
    `Demand.rootCl` inhabits them at the canonical display `S.can σ`
    (`AssumpPref` of `canonL` from `assumpPref_reg`, of `dbΓ` from
    `deltaAdmDb_assumpPref` + `assumpPref_deltaBodyInst`), and
    `cl_deltaCanonL_before`/`cl_deltaDbΓ_before` give `Before`. The
    `EnvWfT`-prefix side of the member typing is fully absorbed by `defAdm`'s
    `ewk`-lineage + `admW` slot — no `hasTyT_constsIn` strengthening. -/
theorem es_delta_kept_memberCoh_tableOfI (Aw : Nat → Nat) {Eₐ E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember}
    {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hag : AgreeOn E Aw (enrichEnvWfT S.env).admW) :
    CaseStep Aw (tableOfI S.env)
      (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr)
        S σ (S.can σ)) := by
  intro hq ih
  have hap : hb.AssumpPref ∧ dl.AssumpPref ∧ dr.AssumpPref := hq.ap
  have hL : Goal (tableOfI S.env)
      (.cl dl (deltaCanonL hres hlen hwf hb) S σ (S.can σ)) :=
    (ih _ (Demand.rootCl dl (deltaCanonL hres hlen hwf hb) hap.2.1
        (assumpPref_reg hap.1) S σ hq.hom)
      (cl_deltaCanonL_before Aw hres hbody htr hlen hwf hb dl dr S σ)).2
  have hB : Goal (tableOfI S.env)
      (.cl (deltaDbΓ S.env Γ hres hbody hlen hwf
        (deltaAdmDb (enrichEnvWfT S.env) hres hbody htr)) hb S σ (S.can σ)) :=
    (ih _ (Demand.rootCl _ hb
        (assumpPref_deltaBodyInst S.env hres hbody hlen hwf Γ
          (deltaAdmDb_assumpPref (enrichEnvWfT S.env) hres hbody htr
            (srDelta_defAdm_assumpPref S.env hres hbody htr)))
        hap.1 S σ hq.hom)
      (cl_deltaDbΓ_before Aw hres hbody htr hlen hwf hb dl dr S σ hag)).2
  exact delta_kept_caseStep_tableI hres hbody htr hlen hwf hb dl dr S σ
    (tableOfICompat_tableOfI S.env) hu hag
    (srDelta_defAdm_assumpPref S.env hres hbody htr) hL hB hq ih

end Rcic.Syn

#print axioms Rcic.Syn.castArityZero_assumpPref
#print axioms Rcic.Syn.castArityZero_atoms
#print axioms Rcic.Syn.deltaAdmDb_assumpPref
#print axioms Rcic.Syn.deltaDbΓ_atoms_adm
#print axioms Rcic.Syn.defAdm_atoms_lt
#print axioms Rcic.Syn.typeAdm_atoms_lt
#print axioms Rcic.Syn.cl_deltaCanonL_before
#print axioms Rcic.Syn.cl_deltaDbΓ_before
#print axioms Rcic.Syn.es_delta_kept_memberCoh_tableOfI
