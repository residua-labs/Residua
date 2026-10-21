import rcic.RcicSynAppWalk
import rcic.RcicSynES
import rcic.RcicSynStarLift

/-!
# Syntactic sortRow, build step 3al — the stored η λ, erased through the reading

`research/rcic/semantic/S3_ES_ARMS.md` §37. `meetEta` (§30) reads a typing
`dl` of `λA. (lift 0 1 f) (bvar 0)` as a typing `a.hf` of the weakened
function and a typing `a.ha` of the variable, both under `dl.wt`. The walks
`epsWalkLam` (§26) and `epsWalkApp` (§36) say what `dl` erases to against
that reading. `etaVerdict` composes them:

- `clause bit`: `dl` erases to `lamErasure bit (appClause (a.hf.eps …)
  (a.ha.eps …))` at the binder disposition `binderDisp bit`;
- `star`: `dl` erases to `★`;
- `raw` / `none`: a walk did not claim the erasure, or a reader returned `.no`.

On `clause`, `es_eta`'s left coherence is read off the stored `dl`. The
function piece is `CL` of `a.hf` against `wkAtZero dr`: both sit under the
η node (`a.ltF`, `CvP.wt_dl_lt`; `wk` adds no atom, `CvP.wt_dr_lt`), so
`cl_under_atoms` supplies it from `Below`. `wkAtZero dr` erases to `dr`'s
erasure on `drop` and to its lift on `keep` (`eta_fun_drop` /
`eta_fun_keep`). The variable piece is `bvarEps` of `a.ha`: on `drop` both
`star` and `rel` are `★` (`resolve_drop_zero`); on `keep`, `rel` is `bvar 0`.

- `drop`: `dl` erases to the function's erasure, and `ES` is `CL`
  (`es_eta_of_below_drop`). No η step.
- `keep`, variable `bvar 0`: if the function piece `X` is not `★`, the η
  redex steps (`es_eta`), whatever `dr` erases to: `CL` gives
  `X ↔* (dr.eps).lift 0 1`, and `λ. F↑ 0 → F` holds at `F = ★` too. If
  `X = ★`, `dl` erases to `★`, `CL` gives `★ ↔* (dr.eps)↑`, and
  `convMod_star_of_lift` (§39, any `TableWF` table) gives `★ ↔* dr.eps`.

Not proved. `keep` with a proof variable (`a.ha` erases to `★` under a
relevant binder), the `star`, `raw` and `none` verdicts, and an `other`
variable head. Those are bit coherences (`PBit` / `CTS`) or
spines the readers do not push.

`Below` as stated is unsatisfiable at every rule node heavier than `2`
(`RcicSynBelowRho`, S3 §38), so the two `es_eta_of_below_*` theorems are
vacuous until its quantifiers carry a premise that `ρ` respects the
context. The rewrite content (`es_eta_meet_*`, `etaVerdict`) does not
read `Below`. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the composed verdict -/

inductive EtaVerdict {Ei : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP Ei n Γ e T) (σ : Level → Level) (ρ : List Disp) :
    {Aw : Nat → Nat} → {src : Nat} → {E : ResolvedEnv} → {A f : Expr Nat} →
    EtaMeet Aw src E n Γ A f → Type where
  | clause {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A f : Expr Nat}
      {a : AppGot Aw src E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)}
      (bit : Bool)
      (h : D.eps σ ρ = lamErasure bit (appClauseOf a σ (binderDisp bit :: ρ))) :
      EtaVerdict D σ ρ (.yes a)
  | star {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A f : Expr Nat}
      {a : AppGot Aw src E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)}
      (h : D.eps σ ρ = .star) : EtaVerdict D σ ρ (.yes a)
  | raw {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A f : Expr Nat}
      {a : AppGot Aw src E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0)} :
      EtaVerdict D σ ρ (.yes a)
  | none {Aw : Nat → Nat} {src : Nat} {E : ResolvedEnv} {A f : Expr Nat} :
      EtaVerdict D σ ρ (EtaMeet.no : EtaMeet Aw src E n Γ A f)

theorem lamErasure_star (bit : Bool) : lamErasure bit .star = .star := by
  cases bit <;> rfl

/-- `epsWalkLam` on the stored λ, then `epsWalkApp` on the body it returns. -/
noncomputable def etaVerdict {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (Aw : Nat → Nat)
    {n : Nat} {Γ : LCtx} {e T A f : Expr Nat} (D : TyP Ei n Γ e T)
    (he : e = .lam A (.app (lift 0 1 f) (.bvar 0)))
    (σ : Level → Level) (ρ : List Disp) :
    EtaVerdict D σ ρ (meetEta hext Aw D he) := by
  unfold meetEta
  have hL := epsWalkLam hext Aw σ D he ρ
  cases hri : readLam hext Aw D he with
  | no =>
      exact .none
  | yes g =>
      rw [hri] at hL
      have hA := epsWalkApp (envExt_refl E) Aw (D.wt Aw) σ g.hbody rfl g.lt
        (binderDisp (levelIsZero (σ g.u)) :: ρ)
      dsimp only
      cases hra : readApp (envExt_refl E) Aw (D.wt Aw) g.hbody rfl g.lt with
      | no =>
          exact .none
      | yes a =>
          rw [hra] at hA
          cases hL with
          | raw =>
              exact .raw
          | star h =>
              exact .star h
          | clause h =>
              cases hA with
              | raw =>
                  exact .raw
              | star h' =>
                  refine .star ?_
                  rw [h]
                  unfold lamClauseOf
                  rw [h', lamErasure_star]
              | clause h' =>
                  refine .clause (levelIsZero (σ g.u)) ?_
                  rw [h]
                  unfold lamClauseOf
                  rw [h']

/-! ## §2 the variable piece -/

theorem eta_var_drop_rel {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat}
    {D : TyP E n Γ (.bvar 0) T} {σ : Level → Level} {ρ : List Disp}
    (h : D.eps σ (.drop :: ρ) = resolve (.drop :: ρ) 0) :
    D.eps σ (.drop :: ρ) = .star :=
  h.trans (resolve_drop_zero ρ)

theorem eta_var_keep_rel {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat}
    {D : TyP E n Γ (.bvar 0) T} {σ : Level → Level} {ρ : List Disp}
    (h : D.eps σ (.keep :: ρ) = resolve (.keep :: ρ) 0) :
    D.eps σ (.keep :: ρ) = .bvar 0 :=
  h.trans (resolve_keep_zero ρ)

/-! ## §3 `ES` of η, from the erasure of the stored λ -/

theorem es_eta_meet_drop {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {σ : Level → Level} {ρ : List Disp} {X : ETm}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hL : dl.eps σ ρ = X) (hX : ConvMod (EStep tbl) LvlEq X (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) := by
  simpa [ES, CvP.dl, CvP.dr, hL] using hX

theorem es_eta_meet_keep {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {σ : Level → Level} {ρ : List Disp} {X : ETm}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hL : dl.eps σ ρ = lamClause (appClause X (.bvar 0)))
    (hX : ConvMod (EStep tbl) LvlEq X ((dr.eps σ ρ).lift 0 1))
    (hXs : X ≠ .star) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) := by
  have hb : (ETm.bvar 0) ≠ .star := by
    intro hc
    cases hc
  have hab : ETm.app X (.bvar 0) ≠ .star := by
    intro hc
    cases hc
  rw [appClause_app hXs hb, lamClause_of_ne hab] at hL
  refine es_eta h dl dr (F := dr.eps σ ρ) ?_ (.refl _)
  rw [hL]
  exact convMod_lam (convMod_app hX (.refl _))

theorem es_eta_meet_keep_star {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {σ : Level → Level} {ρ : List Disp} {X : ETm}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hL : dl.eps σ ρ = lamClause (appClause X (.bvar 0)))
    (hXs : X = .star) (hFs : dr.eps σ ρ = .star) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) := by
  subst hXs
  have hL' : dl.eps σ ρ = .star := hL
  simp only [ES, CvP.dl, CvP.dr, hL', hFs]
  exact .refl _

/-- The function piece erases to `★`. `dl` is then `★`, and `★ ↔* dr.eps`. -/
theorem es_eta_meet_keep_starX {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hL : dl.eps σ ρ = lamClause (appClause .star (.bvar 0)))
    (hS : ConvMod (EStep tbl) LvlEq .star (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) := by
  have hL' : dl.eps σ ρ = .star := hL
  simpa [ES, CvP.dl, CvP.dr, hL'] using hS

/-! ## §4 the function piece, from `Below` -/

theorem atoms_wkAtZero (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A : Expr Nat} (D : TyP E n Γ e T) :
    (wkAtZero (A := A) D).atoms Aw = D.atoms Aw := by
  unfold wkAtZero
  rw [atoms_tyCastCtx]
  rfl

/-- `CL` of the extracted function against the weakened right endpoint. Both
    sit under the η node. -/
theorem eta_fun_cl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (Bl : Below Aw tbl (cvMeas Aw (CvP.eta E n Γ f A B h dl dr)))
    (a : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0))
    (σ : Level → Level) (ρ' : List Disp)
    (hρ' : DispFor σ E n (.assumption A :: Γ) ρ') :
    CL tbl σ ρ' a.hf (wkAtZero (A := A) dr) := by
  have hdl : dl.wt Aw < (CvP.eta E n Γ f A B h dl dr).wt Aw :=
    CvP.wt_dl_lt Aw (CvP.eta E n Γ f A B h dl dr)
  have hdr : dr.wt Aw < (CvP.eta E n Γ f A B h dl dr).wt Aw :=
    CvP.wt_dr_lt Aw (CvP.eta E n Γ f A B h dl dr)
  refine cl_under_atoms Aw tbl (CvP.eta E n Γ f A B h dl dr) rfl Bl a.hf
    (wkAtZero (A := A) dr) σ ρ' hρ' (fun y hy => Nat.lt_trans (a.ltF y hy) hdl) ?_
  intro y hy
  rw [atoms_wkAtZero] at hy
  exact atoms_lt_of_wt_lt Aw dr hdr y hy

/-- Proof domain. `dl` erases to the extracted function, and that is `CL` to
    `dr`. `DispFor` for `.drop :: ρ` is discharged by `dispFor_assumption_drop`. -/
theorem es_eta_of_below_drop (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat} {u : Level}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (Bl : Below Aw tbl (cvMeas Aw (CvP.eta E n Γ f A B h dl dr)))
    (a : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = true)
    (hW : dl.eps σ ρ = lamErasure true (appClauseOf a σ (.drop :: ρ)))
    (hvar : a.ha.eps σ (.drop :: ρ) = .star) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) := by
  have hcl := eta_fun_cl Aw tbl h dl dr Bl a σ (.drop :: ρ)
    (dispFor_assumption_drop hρ hA hu)
  unfold CL at hcl
  rw [eta_fun_drop] at hcl
  refine es_eta_meet_drop h dl dr ?_ hcl
  rw [hW]
  unfold appClauseOf
  rw [hvar, appClause_right_star]
  rfl

/-- Relevant domain, variable `bvar 0`. A `★` function piece is
    `convMod_star_of_lift` of the `CL`. `DispFor` for `.keep :: ρ` is
    discharged by `dispFor_assumption_keep`. -/
theorem es_eta_of_below_keep (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat} {u : Level}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hA : TyP E n Γ A (.sort u))
    (Bl : Below Aw tbl (cvMeas Aw (CvP.eta E n Γ f A B h dl dr)))
    (a : AppGot Aw (dl.wt Aw) E n (.assumption A :: Γ) (lift 0 1 f) (.bvar 0))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ u) = false)
    (hW : dl.eps σ ρ = lamErasure false (appClauseOf a σ (.keep :: ρ)))
    (hvar : a.ha.eps σ (.keep :: ρ) = .bvar 0)
    (hTW : TableWF tbl) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) := by
  have hcl := eta_fun_cl Aw tbl h dl dr Bl a σ (.keep :: ρ)
    (dispFor_assumption_keep hρ hA hu)
  unfold CL at hcl
  rw [eta_fun_keep] at hcl
  have hL : dl.eps σ ρ = lamClause (appClause (a.hf.eps σ (.keep :: ρ)) (.bvar 0)) := by
    rw [hW]
    unfold appClauseOf
    rw [hvar]
    rfl
  by_cases hX : a.hf.eps σ (.keep :: ρ) = .star
  · rw [hX] at hL hcl
    exact es_eta_meet_keep_starX h dl dr hL (convMod_star_of_lift hTW hcl)
  · exact es_eta_meet_keep h dl dr hL hcl hX

end Rcic.Syn

#print axioms Rcic.Syn.lamErasure_star
#print axioms Rcic.Syn.etaVerdict
#print axioms Rcic.Syn.eta_var_drop_rel
#print axioms Rcic.Syn.eta_var_keep_rel
#print axioms Rcic.Syn.es_eta_meet_drop
#print axioms Rcic.Syn.es_eta_meet_keep
#print axioms Rcic.Syn.es_eta_meet_keep_star
#print axioms Rcic.Syn.es_eta_meet_keep_starX
#print axioms Rcic.Syn.atoms_wkAtZero
#print axioms Rcic.Syn.eta_fun_cl
#print axioms Rcic.Syn.es_eta_of_below_drop
#print axioms Rcic.Syn.es_eta_of_below_keep
