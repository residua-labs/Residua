import rcic.RcicSynStepSkeleton
import rcic.RcicSynSRBetaZetaBeta

/-!
# Row 2 — the additive β-body issuance row (`IssuesCTB`)

cc 11:30Z item (1), glm-sr1. `BetaBodyClWall` is already refuted on-cone
(`beta_body_cl_refuted`, `RcicSynSRBetaZetaBeta` — the `wkZetaCtx`
double-lift wedge). The remaining question the census asked is whether the
β-body `.cl` at the binder-raised display is a genuine IH edge at all.
`Issues` itself is sealed; `IssuesCTB` is its composition-only sibling
carrying exactly that row, and both edge conditions are DECIDED here:

* `beta_body_cl_before` — the strict `Before` rank edge: `g.hbody`'s atoms
  sit under `dl.wt` (`RedexGot.ltB`), `hbody`'s under the node's own `wt`;
  `dmStep_under_rule` + `lex_of_dm` + `lexDM_combMeas_mono` +
  `before_of_same_prefix`. DECREASES.
* `issuesCTB_routed` — the raised display `binderDisp :: ρ` is routed by
  one `RoutedDisp.assumption` on the node's own `hA`. ROUTED.
* `issuesCTB_hom` — same `σ`. HOLDS.
* `issuesCTB_ap` — `.cl`-AP under the named premise `IssuesCT.bodyAP`:
  `hbody`'s half is `beta.AssumpPref`'s structural projection; the
  read-side `g.hbody.AssumpPref` is the one residue the `readLam`/
  `readRedex` traversal still owes — restated as `RedexBodyAPWall`.

Verdict: the issuance edge itself is REAL (rank↓, routed, hom); the wall
fails because the PROP it would supply is false on-cone
(`beta_body_cl_refuted`) — the edge and the port are independent failures
of `es_beta`'s ports, not an IH-edge absence. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Additive issuance family — the β-body `.cl` at the raised display.
    `Issues` is sealed; this sibling carries exactly the row census
    row-2's wall needed as an IH edge. The read's `g.hbody` against the
    node's own `hbody`, one binder up at the binder's display — the
    `lam_esB`/`pi_esB` shape at the `beta` rule node. -/
inductive IssuesCTB {Eₐ : ResolvedEnv} : P2Query Eₐ → P2Query Eₐ → Prop where
  | beta_body_cl {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A body arg B : Expr Nat} {u : Level}
      {hA : TyP E n Γ A (.sort u)}
      {hbody : TyP E n (.assumption A :: Γ) body B}
      {harg : TyP E n Γ arg A}
      {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
      {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
      {Aw : Nat → Nat}
      {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
      {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
      (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
      (hr : readRedex (envExt_refl E) Aw dl rfl = .yes g) :
      IssuesCTB
        (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ)
        (.cl g.hbody hbody S σ (binderDisp (levelIsZero (σ u)) :: ρ))

/-- `Hom` is preserved verbatim — same `σ`. -/
theorem issuesCTB_hom {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ}
    (h : q.Hom) (e : IssuesCTB q q') : q'.Hom := by
  cases e
  exact h

/-- The raised display is routed by one `RoutedDisp.assumption` on the
    node's own binder typing. -/
theorem issuesCTB_routed {Eₐ : ResolvedEnv} {q q' : P2Query Eₐ}
    (h : q.Routed) (e : IssuesCTB q q') : q'.Routed := by
  cases e with
  | @beta_body_cl E n Γ A body arg B u hA hbody harg dl dr Aw E₀ n₀ Γ₀ S σ ρ g hr =>
      exact .assumption h hA

/-- `.cl`-AP of the issued β-body query, per-ctor: `hbody`'s half is
    `CvP.beta`'s `AssumpPref` projection; `g.hbody`'s half is the named
    `RedexBodyAPWall` residue below — taken here as an explicit
    hypothesis so the statement shows exactly what the read owes. -/
theorem beta_body_cl_ap {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {harg : TyP E n Γ arg A}
    {dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B)}
    {dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)}
    {Aw : Nat → Nat} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
    {σ : Level → Level} {ρ : List Disp}
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (hq : (P2Query.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr)
      S σ ρ).AP)
    (hg : g.hbody.AssumpPref) :
    (P2Query.cl g.hbody hbody S σ (binderDisp (levelIsZero (σ u)) :: ρ)).AP :=
  ⟨hg, hq.2.1⟩

/-- The strict rank decrease: same frame (the `.cl` keeps the parent's
    `S`), `DMStep` on the local key — every atom of
    `g.hbody.atoms ++ hbody.atoms` sits under the beta node's own `wt`
    atom (`g.ltB` bounds `g.hbody` by `dl.wt`; `atoms_lt_of_wt_lt` bounds
    `hbody` by its own weight; both are strict summands of `beta.wt`). -/
theorem beta_body_cl_before {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level} (Aw : Nat → Nat)
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (g : RedexGot Aw (dl.wt Aw) E n Γ A body arg)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    Before Aw
      (.cl g.hbody hbody S σ (binderDisp (levelIsZero (σ u)) :: ρ))
      (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) := by
  refine before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _ ?_)
  exact lex_of_dm (dmStep_under_rule Aw
    (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) rfl
    (fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · exact Nat.lt_trans (g.ltB y hy) (by simp only [CvP.wt]; omega)
      · exact atoms_lt_of_wt_lt Aw hbody (by simp only [CvP.wt]; omega) y hy))

/-- The ONE remaining demand-side invariant, restated as a named wall:
    the body a successful `readRedex` returns carries `AssumpPref`
    whenever the input does. Every wrapper the read composes has a landed
    AP lemma (`assumpPref_tyCast`, `assumpPref_pushBodyEsub`,
    `assumpPref_wkAtZero`, `assumpPref_instEnd`; `ewk`/`linst`/`conv` are
    transparent) — the `readLam`/`readRedex` mutual traversal that
    composes them is the open proof. Independent of the wall's refutation:
    `beta_body_cl_refuted` kills the PROP; this wall asks only whether a
    demanded `.cl` here would still be on-cone. -/
def RedexBodyAPWall : Prop :=
  ∀ {Aw : Nat → Nat} {Ei E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A body arg : Expr Nat}
    (hext : EnvExt Ei E) (D : TyP Ei n Γ e T)
    (he : e = .app (.lam A body) arg)
    (g : RedexGot Aw (D.wt Aw) E n Γ A body arg),
    readRedex hext Aw D he = .yes g →
    D.AssumpPref → g.hbody.AssumpPref

end Rcic.Syn

#print axioms Rcic.Syn.issuesCTB_hom
#print axioms Rcic.Syn.issuesCTB_routed
#print axioms Rcic.Syn.beta_body_cl_ap
#print axioms Rcic.Syn.beta_body_cl_before
#print axioms Rcic.Syn.RedexBodyAPWall
