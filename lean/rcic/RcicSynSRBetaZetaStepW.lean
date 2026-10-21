import rcic.RcicSynSRBetaZetaStepWCore
import rcic.RcicSynSRBetaZetaStepWNoInline

/-!
# `StepSuppliersW` and the closer on `epsW`

`StepSuppliers` with every field restated at `CaseStepW` (the `GoalW` of the
query), and `step_of_suppliersW` — the closer composed from this branch's
`esW_*` transport layer (`esW_wk_keep/not_keep`, `esW_esub_drop/keep`,
`esW_linst`, `esW_ewk`, `esW_cctx`) and the §2 composer mirrors, reusing the
landed `Issues` rows and rank edges verbatim (they are eps-free). `solve_of_stepW`
lifts it to every demanded query; `AllBelowScopedW` is the pack mirror.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the supplier record at `GoalW` -/

/-- `StepSuppliers` with CL/ES (and the EUT/PBit goals of the same tags)
    replaced by their `epsW` versions. Field shapes are the landed ones;
    only the concluding `CaseStep`→`CaseStepW` changes. -/
structure StepSuppliersW (Aw : Nat → Nat) (tbl : List CRule) (Eₐ : ResolvedEnv) : Prop where
  es_consts : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true) (hls : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr) S σ ρ)
  es_beta : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)
  es_zeta : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ)
  es_zetaLocal : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) S σ ρ)
  es_delta : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ)
  es_iota_retained : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    levelIsZero (σ hlhs.reg.1) = false →
    CaseStepW Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)
  es_lit : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ)
  es_app : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
  es_lam : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ)
  es_pi : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.pi E n Γ A A' B B' u v hA hB dl dr) S σ ρ)
  es_letE : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) S σ ρ)
  es_eta : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.eta E n Γ f A B hf dl dr) S σ ρ)
  es_fsub : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ)
  /-- The **out-of-range cutoff corner** of the `wk`-keep step — the only
      residue of the old closer's missing `epsW` analogue. For every in-range
      cutoff (`c ≤ Γ.length`), `wkInnerDisp_eq_removeAt_of_demand`
      (`RcicSynSRBetaZetaStepWNoInline`) proves `wkInnerDisp ρ c =
      removeAt ρ c` on the demand cone (`AssumpPref` pins the prefix, routed
      `.inline` entries sit at `.letBinding` positions), so the closer reads
      the child off the `Issues.wk_es` edge via `esW_wk_keep`. This field
      owes exactly the out-of-range corner: there the `wk`-inserted decl
      lands inside the prefix and the display may carry padding keeps, where
      the re-frame genuinely has no landed IH edge. -/
  es_wk_keep_reframe : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) (d : LocalDecl) (c : Nat)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hk : ρ[c]? = some .keep) (hc : Γ.length < c)
    (hne : wkInnerDisp ρ c ≠ removeAt ρ c),
    CaseStepW Aw tbl (.es (CvP.wk E n Γ a b T d c h) S σ ρ)
  cl_case : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.cl D₁ D₂ S σ ρ)
  eut_case : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.eut D₁ D₂ S σ ρ)
  pb_case : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {s : Level} (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.pb D DT S σ ρ)
  mixed_case : ∀ {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp),
    CaseStepW Aw tbl (.mixed D₁ D₂ S σ ρ)
  delta_obs : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (_hδ : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (pos : ObsPos),
    CaseStepW Aw tbl (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) pos S σ [])

/-! ## §2 the `.es` case at `GoalW` -/

/-- `es_goal_of_suppliers` at `GoalW`: transports read off the `esW_*`
    mirrors of this branch, structural cases off the §2 composer mirrors,
    rule nodes off `W`; every IH call keeps the landed `Issues` row and rank
    edge verbatim. -/
theorem es_goalW_of_suppliers {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliersW Aw tbl Eₐ)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat}
    (h : CvP E n Γ a b T) (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es h S σ ρ)) (ih : StepIHW Aw tbl (.es h S σ ρ)) :
    GoalW tbl (.es h S σ ρ) := by
  have hσ : LevelHom σ := hq.hom
  show ESW tbl σ ρ h
  cases h with
  | refl E n Γ a A ht dl dr =>
      refine esW_refl ht dl dr ?_
      exact ih_localW Aw tbl hq ih (.cl dl dr S σ ρ) Issues.refl_cl rfl
        (lexDM_combMeas_mono Aw _ (lex_of_dm (below_refl Aw ht dl dr)))
  | symm E n Γ a b A h dl dr =>
      have steps := below_symm Aw h dl dr
      refine esW_symm h dl dr ?_ ?_ ?_
      · exact ih_localW Aw tbl hq ih (.es h S σ ρ) Issues.symm_es rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.1))
      · exact ih_localW Aw tbl hq ih (.cl dl h.dr S σ ρ) Issues.symm_clL rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.1))
      · exact ih_localW Aw tbl hq ih (.cl h.dl dr S σ ρ) Issues.symm_clR rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2))
  | trans E n Γ a b c A h1 h2 dl dr =>
      have steps := below_trans Aw h1 h2 dl dr
      refine esW_trans h1 h2 dl dr ?_ ?_ ?_ ?_ ?_
      · exact ih_localW Aw tbl hq ih (.es h1 S σ ρ) Issues.trans_es1 rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.1))
      · exact ih_localW Aw tbl hq ih (.es h2 S σ ρ) Issues.trans_es2 rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.1))
      · exact ih_localW Aw tbl hq ih (.cl dl h1.dl S σ ρ) Issues.trans_clL rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2.1))
      · exact ih_localW Aw tbl hq ih (.cl h1.dr h2.dl S σ ρ) Issues.trans_clM rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2.2.1))
      · exact ih_localW Aw tbl hq ih (.cl h2.dr dr S σ ρ) Issues.trans_clR rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2.2.2))
  | beta E n Γ A body arg B u hA hbody harg dl dr =>
      exact W.es_beta hA hbody harg dl dr S σ ρ hq ih
  | zeta E n Γ A value body B u hA hv hb dl dr =>
      exact W.es_zeta hA hv hb dl dr S σ ρ hq ih
  | zetaLocal E n Γ i A v hval hty hv dl dr =>
      exact W.es_zetaLocal hval hty hv dl dr S σ ρ hq ih
  | delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr =>
      exact W.es_delta hres hbody htr hlen hwf hb dl dr S σ ρ hq ih
  | iota E n Γ lhs rhs T w hlhs hrhs dl dr =>
      cases hu : levelIsZero (σ hlhs.reg.1) with
      | true =>
          have pL : PBitW σ ρ dl hlhs.reg.2 :=
            ih_localW Aw tbl hq ih (.pb dl hlhs.reg.2 S σ ρ) Issues.iota_pbL rfl
              (lexDM_combMeas_mono Aw _ (iota_qL_below Aw w hlhs hrhs dl dr))
          have pR : PBitW σ ρ dr hlhs.reg.2 :=
            ih_localW Aw tbl hq ih (.pb dr hlhs.reg.2 S σ ρ) Issues.iota_pbR rfl
              (lexDM_combMeas_mono Aw _ (iota_qR_below Aw w hlhs hrhs dl dr))
          exact esW_iota_proof_of_pbitWs tbl σ ρ w hlhs hrhs dl dr hu pL pR
      | false => exact W.es_iota_retained w hlhs hrhs dl dr S σ ρ hu hq ih
  | lit E n Γ t exp T hlit hexp dl dr =>
      exact W.es_lit hlit hexp dl dr S σ ρ hq ih
  | app E n Γ f g a b A B h1 h2 dl dr =>
      exact W.es_app h1 h2 dl dr S σ ρ hq ih
  | lam E n Γ A A' b b' B u hA hb dl dr =>
      exact W.es_lam hA hb dl dr S σ ρ hq ih
  | pi E n Γ A A' B B' u v hA hB dl dr =>
      exact W.es_pi hA hB dl dr S σ ρ hq ih
  | letE E n Γ A A' v v' b b' B u hA hv hb dl dr =>
      exact W.es_letE hA hv hb dl dr S σ ρ hq ih
  | sorts E n Γ l₁ l₂ hl dl dr =>
      have hnode : (CvP.sorts E n Γ l₁ l₂ hl dl dr).isTransport = false := rfl
      have hpos := TyP.wt_pos Aw dl
      have hwl : dl.wt Aw < (CvP.sorts E n Γ l₁ l₂ hl dl dr).wt Aw := by
        simp only [CvP.wt]; omega
      have hwr : dr.wt Aw < (CvP.sorts E n Γ l₁ l₂ hl dl dr).wt Aw := by
        simp only [CvP.wt]; omega
      have hw1 : (sortNode E n Γ l₁).wt Aw < (CvP.sorts E n Γ l₁ l₂ hl dl dr).wt Aw := by
        simp only [sortNode, TyP.wt, CvP.wt]; omega
      have hw2 : (sortNode E n Γ l₂).wt Aw < (CvP.sorts E n Γ l₁ l₂ hl dl dr).wt Aw := by
        simp only [sortNode, TyP.wt, CvP.wt]; omega
      have c1 : CLW tbl σ ρ dl (sortNode E n Γ l₁) :=
        ih_localW Aw tbl hq ih (.cl dl (sortNode E n Γ l₁) S σ ρ) Issues.sorts_clL rfl
          (lexDM_combMeas_mono Aw _
            (lex_of_dm (dmStep_pair_below Aw (CvP.sorts E n Γ l₁ l₂ hl dl dr) hnode
              dl (sortNode E n Γ l₁) hwl hw1)))
      have c2 : CLW tbl σ ρ dr (sortNode E n Γ l₂) :=
        ih_localW Aw tbl hq ih (.cl dr (sortNode E n Γ l₂) S σ ρ) Issues.sorts_clR rfl
          (lexDM_combMeas_mono Aw _
            (lex_of_dm (dmStep_pair_below Aw (CvP.sorts E n Γ l₁ l₂ hl dl dr) hnode
              dr (sortNode E n Γ l₂) hwr hw2)))
      have c1' : ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ) (.sort (σ l₁)) := c1
      have c2' : ConvMod (EStep tbl) LvlEq (dr.epsW σ ρ) (.sort (σ l₂)) := c2
      show ConvMod (EStep tbl) LvlEq (dl.epsW σ ρ) (dr.epsW σ ρ)
      exact c1'.trans ((ConvMod.eqv (LvlEq.sort (hσ.eqN_map hl))).trans
        (ConvMod.symm' LvlEq.symm' c2'))
  | consts E n Γ r ls ls' m hres hlen hwf hwf' hls dl dr =>
      exact W.es_consts hres hlen hwf hwf' hls dl dr S σ ρ hq ih
  | eta E n Γ f A B hf dl dr =>
      exact W.es_eta hf dl dr S σ ρ hq ih
  | irr E n Γ P p q' hP hp hqq dl dr =>
      have steps := below_irr Aw hP hp hqq dl dr
      have pL : PBitW σ ρ dl hP :=
        ih_localW Aw tbl hq ih (.pb dl hP S σ ρ) Issues.irr_pbL rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.1))
      have pR : PBitW σ ρ dr hP :=
        ih_localW Aw tbl hq ih (.pb dr hP S σ ρ) Issues.irr_pbR rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.1))
      exact esW_irr_star hP hp hqq dl dr (pL.mpr hσ.zero_bit) (pR.mpr hσ.zero_bit)
  | tyConv E n Γ a b A A' u h hA dl dr =>
      have steps := below_tyConv Aw h hA dl dr
      refine esW_tyConv h hA dl dr ?_ ?_ ?_
      · exact ih_localW Aw tbl hq ih (.es h S σ ρ) Issues.tyConv_es rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.1))
      · exact ih_localW Aw tbl hq ih (.cl dl h.dl S σ ρ) Issues.tyConv_clL rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.1))
      · exact ih_localW Aw tbl hq ih (.cl h.dr dr S σ ρ) Issues.tyConv_clR rfl
          (lexDM_combMeas_mono Aw _ (lex_of_dm steps.2.2))
  | wk E n Γ a b T d c h =>
      have hbody : ESW tbl σ (removeAt ρ c) h :=
        ih_localW Aw tbl hq ih (.es h S σ (removeAt ρ c)) Issues.wk_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_wk Aw h d c))
      cases hρc : ρ[c]? with
      | none => exact esW_wk_not_keep h (Or.inl hρc) hbody
      | some dsp =>
          cases dsp with
          | keep =>
              by_cases hde : wkInnerDisp ρ c = removeAt ρ c
              · exact esW_wk_keep hTbl.closed h hρc (by rw [hde]; exact hbody)
              · exact W.es_wk_keep_reframe h d c S σ ρ hρc
                  (by
                    by_cases hc : c ≤ Γ.length
                    · exact absurd (wkInnerDisp_eq_removeAt_of_demand h hq hc) hde
                    · omega)
                  hde hq ih
          | drop =>
              exact esW_wk_not_keep h (Or.inr (Or.inl hρc)) hbody
          | inline v =>
              exact esW_wk_not_keep h (Or.inr (Or.inr ⟨v, hρc⟩)) hbody
  | esub E n Γ a b T t v j u h hget hv hvT =>
      have hbody : ESW tbl σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ) h :=
        ih_localW Aw tbl hq ih
          (.es h S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ))
          Issues.esub_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_esub Aw h hget hv hvT))
      cases hu : levelIsZero (σ u) with
      | true =>
          rw [hu, binderDisp_drop] at hbody
          exact esW_esub_drop h hget hv hvT hu hbody
      | false =>
          rw [hu, binderDisp_keep] at hbody
          exact esW_esub_keep hTbl.closed h hget hv hvT hu hbody
  | linst E a' n Γ a b T ls hls hlen h =>
      exact esW_linst h
        (ih_localW Aw tbl hq ih (.es h S (fun l => σ (instLevel ls l)) ρ) Issues.linst_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_linst Aw hls hlen h)))
  | ewk E₀' E n Γ a b T hext h =>
      exact esW_ewk h
        (ih_localW Aw tbl hq ih (.es h S σ ρ) Issues.ewk_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_ewk Aw hext h)))
  | cctx E n Γ a b T A A' u h hA =>
      exact esW_cctx h hA
        (ih_localW Aw tbl hq ih (.es h S σ ρ) Issues.cctx_es rfl
          (lexDM_combMeas_mono Aw _ (lexDM_cvMeas_cctx Aw h hA)))
  | fsub E n Γ A B Sx a b u hB hA hab dl dr =>
      exact W.es_fsub hB hA hab dl dr S σ ρ hq ih

/-! ## §3 the closer at `GoalW` -/

/-- `head_goal_bound` at `GoalW` (the `.bitCoh` sub-answers are `BitCoh`,
    unchanged at `GoalW`). -/
theorem head_goal_boundW {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {u uL uR : Level}
    (c : CvP E n Γ A A' (.sort u)) (dL : TyP E n Γ A (.sort uL)) (dR : TyP E n Γ A' (.sort uR))
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.head c uL uR dL dR S σ ρ)) (ih : StepIHW Aw tbl (.head c uL uR dL dR S σ ρ)) :
    levelIsZero (σ uL) = levelIsZero (σ uR) := by
  have l1 : levelIsZero (σ uL) = levelIsZero (σ u) :=
    ih_localW Aw tbl hq ih (.bitCoh dL c.dl S σ ρ) Issues.head_legL rfl
      (lexDM_combMeas_mono Aw _ (Prod.Lex.left _ _ (head_legL_dm Aw c dL dR)))
  have l2 : levelIsZero (σ u) = levelIsZero (σ uR) :=
    ih_localW Aw tbl hq ih (.bitCoh c.dr dR S σ ρ) Issues.head_legR rfl
      (lexDM_combMeas_mono Aw _ (Prod.Lex.left _ _ (head_legR_dm Aw c dL dR)))
  exact l1.trans l2

/-- `cts_goal_of_ports` at `GoalW`. -/
theorem cts_goalW_of_ports {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {X Y : Expr Nat} {w s : Level} (Aw : Nat → Nat) (tbl : List CRule) (hTbl : TableWF tbl)
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (ρ : List Disp)
    (hq : Demand (.cts h DX S ρ)) (ih : StepIHW Aw tbl (.cts h DX S ρ)) : CTS h DX := by
  have heut : EUTW tbl id ρ h.dl DX :=
    ih_localW Aw tbl hq ih (.eut h.dl DX S id ρ) Issues.cts_eut_dlX rfl
      (lexDM_combMeas_mono Aw _ (lexDM_cts_pair Aw h DX))
  have hL : CLW tbl id ρ h.dl.reg.2 (sortNode E n Γ w) := by
    have hd : DMStep (h.dl.reg.2.atoms Aw ++ (sortNode E n Γ w).atoms Aw) (h.atoms Aw) := by
      refine dmStep_cvp_dl_reg Aw h ?_
      intro y hy
      simp only [sortNode, TyP.atoms, List.mem_singleton] at hy
      subst y
      exact Nat.le_refl 1
    exact ih_localW Aw tbl hq ih (.cl h.dl.reg.2 (sortNode E n Γ w) S id ρ) Issues.cts_cl_regL rfl
      (lexDM_combMeas_mono Aw _ (lex_of_dm (dmStep_drop_right hd (DX.atoms Aw))))
  have hR : CLW tbl id ρ DX.reg.2 (sortNode E n Γ s) := by
    cases hs : DX.isSortOrPiHead with
    | true => exact clW_reg_sort_of_isSortOrPiHead tbl DX hs id ρ
    | false =>
        have hrow : Issues (.cts h DX S ρ) (.cl DX.reg.2 (sortNode E n Γ s) S id ρ) :=
          Issues.cts_cl_regX hs
        exact ih_localW Aw tbl hq ih _ hrow rfl
          (lexDM_combMeas_mono Aw _
            (lex_of_dm (dmStep_drop_left (dmStep_reg_sort_pair Aw DX hs) (h.atoms Aw))))
  exact cts_of_eutW_clW hTbl h DX ρ heut hL hR

/-- `bitCoh_goal_of_ports` at `GoalW`. -/
theorem bitCoh_goalW_of_ports {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {T : Expr Nat} {u v : Level} (Aw : Nat → Nat) (tbl : List CRule) (hTbl : TableWF tbl)
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.bitCoh D₁ D₂ S σ ρ)) (ih : StepIHW Aw tbl (.bitCoh D₁ D₂ S σ ρ))
    (heut : EUTW tbl σ ρ D₁ D₂) : BitCoh σ D₁ D₂ := by
  have hL : CLW tbl σ ρ D₁.reg.2 (sortNode E n Γ u) := by
    cases hs : D₁.isSortOrPiHead with
    | true => exact clW_reg_sort_of_isSortOrPiHead tbl D₁ hs σ ρ
    | false =>
        have hrow : Issues (.bitCoh D₁ D₂ S σ ρ) (.cl D₁.reg.2 (sortNode E n Γ u) S σ ρ) :=
          Issues.bitCoh_cl_regL hs
        exact ih_localW Aw tbl hq ih _ hrow rfl
          (lexDM_combMeas_mono Aw _ (lexDM_reg_sort_of_pair_left Aw D₁ hs D₂))
  have hR : CLW tbl σ ρ D₂.reg.2 (sortNode E n Γ v) := by
    cases hs : D₂.isSortOrPiHead with
    | true => exact clW_reg_sort_of_isSortOrPiHead tbl D₂ hs σ ρ
    | false =>
        have hrow : Issues (.bitCoh D₁ D₂ S σ ρ) (.cl D₂.reg.2 (sortNode E n Γ v) S σ ρ) :=
          Issues.bitCoh_cl_regR hs
        exact ih_localW Aw tbl hq ih _ hrow rfl
          (lexDM_combMeas_mono Aw _ (lexDM_reg_sort_of_pair_right Aw D₁ D₂ hs))
  exact bitCoh_of_eutW_clW hTbl D₁ D₂ σ ρ heut hL hR

/-- `head_goal_of_ih` at `GoalW` (the dispatch on the issuing row is eps-free). -/
theorem head_goalW_of_ih {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat} {u : Level} {A A' : Expr Nat}
    {uL uR : Level}
    (c : CvP E n Γ a b (.sort u)) (dL : TyP E n Γ A (.sort uL)) (dR : TyP E n Γ A' (.sort uR))
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.head c uL uR dL dR S σ ρ)) (ih : StepIHW Aw tbl (.head c uL uR dL dR S σ ρ)) :
    GoalW tbl (.head c uL uR dL dR S σ ρ) := by
  cases hq with
  | issued issuer _ hiss e =>
    cases e with
    | tyConv_head =>
        exact head_goal_boundW Aw tbl _ _ _ _ _ _ (.issued _ _ hiss Issues.tyConv_head) ih
    | occ_head hocc hapD hapc =>
        exact head_goal_boundW Aw tbl _ _ _ _ _ _
          (.issued _ _ hiss (Issues.occ_head hocc hapD hapc)) ih

/-- `observation_goal_of_demand` at `GoalW` (the `ObsGoal` is unchanged). -/
theorem observation_goalW_of_demand {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (W : StepSuppliersW Aw tbl Eₐ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} (D : TyP E n Γ e T)
    (θ φ ψ : Level → Level) (pos : ObsPos)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp) (hq : Demand (.observation D θ φ ψ pos S σ ρ))
    (ih : StepIHW Aw tbl (.observation D θ φ ψ pos S σ ρ)) :
    GoalW tbl (.observation D θ φ ψ pos S σ ρ) := by
  have hq' := hq
  cases hq with
  | issued issuer _ hiss e =>
    cases e with
    | delta_obs_out hk hap => exact W.delta_obs hiss _ hq' ih
    | delta_obs_gate hk hap => exact W.delta_obs hiss _ hq' ih

/-- **`StepW` from the suppliers.** The closer on `epsW`: transports and
    structural cases from this branch's mirrors, rule nodes from `W`, the
    eps-free tags from the landed (reused) dispatch. -/
theorem step_of_suppliersW {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliersW Aw tbl Eₐ) : StepW Aw tbl Eₐ := by
  intro q hq ih
  refine ⟨⟨trivialView Aw q⟩, ?_⟩
  cases q with
  | es h S σ ρ => exact es_goalW_of_suppliers Aw tbl hTbl W h S σ ρ hq ih
  | cl D₁ D₂ S σ ρ => exact W.cl_case D₁ D₂ S σ ρ hq ih
  | eut D₁ D₂ S σ ρ => exact W.eut_case D₁ D₂ S σ ρ hq ih
  | cts h DX S ρ => exact cts_goalW_of_ports Aw tbl hTbl h DX S ρ hq ih
  | pb D DT S σ ρ => exact W.pb_case D DT S σ ρ hq ih
  | bitCoh D₁ D₂ S σ ρ =>
      have heut : EUTW tbl σ ρ D₁ D₂ :=
        W.eut_case D₁ D₂ S σ ρ (.issued _ _ hq Issues.bitCoh_eut)
          (fun q' hd hb => ih q' hd hb)
      exact bitCoh_goalW_of_ports Aw tbl hTbl D₁ D₂ S σ ρ hq ih heut
  | mixed D₁ D₂ S σ ρ => exact W.mixed_case D₁ D₂ S σ ρ hq ih
  | head c uL uR dL dR S σ ρ => exact head_goalW_of_ih Aw tbl c dL dR S σ ρ hq ih
  | slot u uD hres dSlot ls S σ ρ => exact (slot_not_demanded hq).elim
  | observation D θ φ ψ pos S σ ρ =>
      exact observation_goalW_of_demand Aw tbl W D θ φ ψ pos S σ ρ hq ih
  | obsPair D₁ D₂ S θ ρ => exact (obsPair_not_demanded hq).elim

/-! ## §4 the fixpoint wrapper and the pack at `GoalW` -/

/-- `solve_of_step` at `AnswerW` (the recursion is on the eps-free rank). -/
theorem solve_of_stepW {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : StepW Aw tbl Eₐ) : ∀ q : P2Query Eₐ, Demand q → AnswerW Aw tbl q := by
  have allAt : ∀ k : Key, ∀ q : P2Query Eₐ, q.rank Aw = k → Demand q → AnswerW Aw tbl q :=
    keyLT_wf.fix (fun k ih q hkey hq =>
      step q hq (fun q' hq' hlt =>
        ih (q'.rank Aw) (by unfold Before at hlt; rwa [hkey] at hlt) q' rfl hq'))
  intro q hq
  exact allAt (q.rank Aw) q rfl hq

/-- The six strict-below obligations of `BelowScoped` at the `epsW` goals. -/
structure BelowScopedW (Eₐ : ResolvedEnv) (Aw : Nat → Nat) (tbl : List CRule)
    (bound : List Nat × Nat) : Prop where
  es : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T), h.AssumpPref →
    ∀ (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (cvMeas Aw h) bound → ESW tbl σ (S.can σ) h
  cl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂), D₁.AssumpPref → D₂.AssumpPref →
    ∀ (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (tyPairMeas Aw D₁ D₂) bound → CLW tbl σ (S.can σ) D₁ D₂
  eut : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂), D₁.AssumpPref → D₂.AssumpPref →
    ∀ (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (tyPairMeas Aw D₁ D₂) bound → EUTW tbl σ (S.can σ) D₁ D₂
  cts : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s)),
    h.AssumpPref → DX.AssumpPref → ScopedCtx Eₐ E n Γ →
    LexDM (cvTyMeas Aw h DX) bound → CTS h DX
  pb : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)), D.AssumpPref → DT.AssumpPref →
    ∀ (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (tyPairMeas Aw D DT) bound → PBitW σ (S.can σ) D DT
  bitCoh : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v)),
    D₁.AssumpPref → D₂.AssumpPref →
    ∀ (_S : ScopedCtx Eₐ E n Γ) (σ : Level → Level), LevelHom σ →
    LexDM (tyPairMeas Aw D₁ D₂) bound → BitCoh σ D₁ D₂

/-- `AllBelowScoped` at the `epsW` goals. -/
def AllBelowScopedW (Eₐ : ResolvedEnv) (Aw : Nat → Nat) (tbl : List CRule) : Prop :=
  ∀ bound : List Nat × Nat, BelowScopedW Eₐ Aw tbl bound

/-- `allBelowScoped_of_step` at `GoalW`. -/
theorem allBelowScopedW_of_step {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (step : StepW Aw tbl Eₐ) : AllBelowScopedW Eₐ Aw tbl := fun _bound =>
  { es := fun h hAP S σ hσ _hlt =>
        (solve_of_stepW Aw tbl step (.es h S σ (S.can σ)) (.rootEs h hAP S σ hσ)).2
    cl := fun D₁ D₂ h₁ h₂ S σ hσ _hlt =>
        (solve_of_stepW Aw tbl step (.cl D₁ D₂ S σ (S.can σ)) (.rootCl D₁ D₂ h₁ h₂ S σ hσ)).2
    eut := fun D₁ D₂ h₁ h₂ S σ hσ _hlt =>
        (solve_of_stepW Aw tbl step (.eut D₁ D₂ S σ (S.can σ)) (.rootEut D₁ D₂ h₁ h₂ S σ hσ)).2
    cts := fun h DX hAP hDX S _hlt =>
        (solve_of_stepW Aw tbl step (.cts h DX S (S.can id)) (.rootCts h DX hAP hDX S)).2
    pb := fun D DT hD hDT S σ hσ _hlt =>
        (solve_of_stepW Aw tbl step (.pb D DT S σ (S.can σ)) (.rootPb D DT hD hDT S σ hσ)).2
    bitCoh := fun D₁ D₂ h₁ h₂ S σ hσ _hlt =>
        (solve_of_stepW Aw tbl step (.bitCoh D₁ D₂ S σ (S.can σ))
          (.rootBitCoh D₁ D₂ h₁ h₂ S σ hσ)).2 }

/-- The S15 §6 chain from the suppliers, at `GoalW`. -/
theorem allBelowScopedW_of_suppliers {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    (hTbl : TableWF tbl) (W : StepSuppliersW Aw tbl Eₐ) : AllBelowScopedW Eₐ Aw tbl :=
  allBelowScopedW_of_step Aw tbl (step_of_suppliersW Aw tbl hTbl W)

end Rcic.Syn

#print axioms Rcic.Syn.StepSuppliersW
#print axioms Rcic.Syn.es_goalW_of_suppliers
#print axioms Rcic.Syn.step_of_suppliersW
#print axioms Rcic.Syn.solve_of_stepW
#print axioms Rcic.Syn.allBelowScopedW_of_step
#print axioms Rcic.Syn.allBelowScopedW_of_suppliers
