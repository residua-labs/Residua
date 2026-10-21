/-
`RcicSynStepFields3` — `StepSuppliers.es_beta` / `es_lam` (STEP_SUPPLIERS fields
 3 of 17, batch 145 / #7430).

Each theorem has the field's **exact** binder telescope (copied from
`RcicSynStepSkeleton.StepSuppliers`) plus one extra argument — a residual-port
structure — returning the field's `CaseStep`.  The residuals are the ports the
current `Issues` grammar cannot express; every one is documented at its field.
Nothing here edits the skeleton or `RcicSynP2Shared`.

## What is genuinely issued

- `es_lam` calls `lam_esB` through `ih_issue`: the body `ES` one binder up at
  `binderDisp (levelIsZero (σ u)) :: ρ`, ranked by `rule_sub_before`.  (`lam_esA`'s
  domain `ES` is unused — the λ clause erases the domain; only its bit `u`
  matters, which arrives through the bit ports.)
- `es_beta` calls `occ_pb` through `ih_issue`: `PB[harg, hA]` at payload paths
  `(0, [2])` / `(0, [0])` (`CvP.dchildren` order `[hA, hbody, harg, dl, dr]`),
  ranked by `dmStep_pair_below` + `lex_of_dm` + `lexDM_combMeas_mono` +
  `before_of_same_prefix`.

## The residual ports (exact remaining hypotheses)

For `es_beta` (`BetaPorts`), per `BELOWC_FAILED_READERS_AND_LET_BODY.md` §3.1:

- `got`/`eps`: `Pβ := appSource dl` decoded to a `RedexGot` with
  `dl.eps σ ρ = redexClauseOf g σ ρ`.  `readRedex dl = .yes` supplies this;
  the `p-auth` `RcicSynDomainSource` decoders (`appSource`/`lamDomain`) that
  cover `readRedex dl = .no` spines (`lsub`/`cctx` heads, substitution-born
  redexes) are **not landed**, so non-clause verdicts remain open.
- `domBit`: `BIT[Hg.H, hA]` composed with the reader compatibility
  `(lamDomain (appSource dl).hf).u = g.u` — `RedexGot` carries no domain
  proof `Hg.H`, so the `occ_bitCoh` call needs the (unlanded) domain source;
  for wrapped `dl` the domain child is also not a `subAt` occurrence.
- `argTag`/`bodyTag`: `Tag[…]` star-status ports — `Issues` has **no** tag row
  (S20 `TagCoh` is `PB`-derived), and the needed `PB` sort proofs are
  synthesized (`reg.2`), never `subAt` occurrences.
- `argCl`: `CL[g.harg, harg]` — issuable only when `g.harg` sits at a `subAt`
  path, which fails under `esub`/`linst`/`wk` transport frames.
- `bodyCl`: `CL[g.hbody, hbody]` at `binderDisp … :: ρ` in
  `.assumption A :: Γ` — `occ_cl` is **same-site-`Γ`, same-`ρ`**, so no row
  can ever issue this query.
- `reductCl`: `CL[instEnd hbody harg hA, dr]` — `instEnd` is a synthesized
  canonical node, never a `subAt` occurrence.

For `es_lam` (`LamPorts`), per §3.4: `epsL`/`epsR` (`readLam` clause decodes),
`bitL`/`bitR` (`BIT[HL.H, hA.dl]`/`BIT[HR.H, hA.dr]` — needs `lamDomain`),
`bodyL` (`CL[gL.hbody, hb.dl]` at `d :: ρ`), `bodyR`
(`CL[cctx hb.dr hA, gR.hbody]` at `d :: ρ`), `tagL`/`tagR`/`bodyTag`
(`Tag[…]` star-status).  All `d :: ρ` body ports are unissuable for the same
`occ_cl` same-site reason.

`closure_claim` is unchanged; this module proves the two fields *under* the
stated residual ports — the exact gap to full closure.
-/
import rcic.RcicSynStepSkeleton
import rcic.RcicSynES
import rcic.RcicSynRedex
import rcic.RcicSynRead
import rcic.RcicSynInstEnd
import rcic.RcicSynBelow
import rcic.RcicSynClauseAlg
import rcic.RcicSynErase

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `es_beta` -/

/-- The `es_beta` ports the issued-row grammar cannot currently supply; see the
    module docstring for the per-field accounting against §3.1. -/
structure BetaPorts (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (σ : Level → Level) (ρ : List Disp) : Type where
  /-- `Pβ := appSource dl`, `Hg := lamDomain Pβ.hf`: the redex source reading. -/
  got : RedexGot Aw (dl.wt Aw) E n Γ A body arg
  /-- `dl` erases to the read's redex clause. -/
  eps : dl.eps σ ρ = redexClauseOf got σ ρ
  /-- `BIT[Hg.H, hA]` ∘ reader compatibility `Hg.u = got.u`. -/
  domBit : levelIsZero (σ got.u) = levelIsZero (σ u)
  /-- `Tag[g.harg, harg]` at the site display. -/
  argTag : (got.harg.eps σ ρ = .star) ↔ (harg.eps σ ρ = .star)
  /-- `CL[g.harg, harg]` at the site display. -/
  argCl : CL tbl σ ρ got.harg harg
  /-- `Tag[g.hbody, hbody]` at the body display. -/
  bodyTag : (got.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)
  /-- `CL[g.hbody, hbody]` at the body display. -/
  bodyCl : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) got.hbody hbody
  /-- `CL[instEnd hbody harg hA, dr]` at the site display. -/
  reductCl : CL tbl σ ρ (instEnd hbody harg hA) dr

/-- `es_beta` under the residual ports.  Uses the one genuinely issuable port —
    `occ_pb` for `PB[harg, hA]` — plus the landed `es_beta_drop`/`es_beta_rel`
    finishers. -/
theorem es_beta (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : BetaPorts Aw tbl hA hbody harg dl dr σ ρ) :
    CaseStep Aw tbl (.es (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) S σ ρ) := by
  intro hq ih
  obtain ⟨g, hW, hbit, htagA, hclA, htagB, hclB, hclR⟩ := ports
  -- `PB[harg, hA]` through `occ_pb` at `dchildren` paths `[2]`/`[0]`.
  obtain ⟨hapA, -, haparg, -, -⟩ := hq.ap
  have hpb : PBit σ ρ harg hA :=
    ih_issue Aw tbl hq ih (.pb harg hA S σ ρ)
      (Issues.occ_pb (k₁ := 0) (p₁ := [2]) (k₂ := 0) (p₂ := [0]) rfl rfl haparg hapA)
      (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
        (lex_of_dm (dmStep_pair_below Aw
          (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) rfl harg hA
          (by simp only [CvP.wt]; omega) (by simp only [CvP.wt]; omega)))))
  unfold CL at hclA hclB hclR
  cases hu : levelIsZero (σ u) with
  | true =>
      have hgu : levelIsZero (σ g.u) = true := hbit.trans hu
      have hga : g.harg.eps σ ρ = .star := htagA.mpr (hpb.mpr hu)
      have hdl : dl.eps σ ρ = g.hbody.eps σ (.drop :: ρ) := by
        rw [hW]; unfold redexClauseOf
        rw [hgu, binderDisp_drop]
        simp only [redexClause, lamErasure, hga, appClause_right_star]
      have hclB' : ConvMod (EStep tbl) LvlEq (g.hbody.eps σ (.drop :: ρ))
          (hbody.eps σ (.drop :: ρ)) := by
        rwa [hu, binderDisp_drop] at hclB
      have hclR' : ConvMod (EStep tbl) LvlEq (hbody.eps σ (.drop :: ρ)) (dr.eps σ ρ) := by
        rwa [instEnd_eps_drop hbody harg hA hu] at hclR
      exact es_beta_drop hA hbody harg dl dr (hdl ▸ hclB') hclR'
  | false =>
      have hgu : levelIsZero (σ g.u) = false := hbit.trans hu
      have hargN : harg.eps σ ρ ≠ .star := fun h => by
        have htru := hpb.mp h; rw [hu] at htru; exact Bool.noConfusion htru
      have hgaN : g.harg.eps σ ρ ≠ .star := fun h => hargN (htagA.mp h)
      rw [hu, binderDisp_keep] at htagB hclB
      by_cases hbb : hbody.eps σ (.keep :: ρ) = .star
      · have hgb : g.hbody.eps σ (.keep :: ρ) = .star := htagB.mpr hbb
        have hdl : dl.eps σ ρ = .star := by
          rw [hW]; unfold redexClauseOf
          rw [hgu, binderDisp_keep]
          simp only [redexClause, lamErasure, hgb, lamClause, appClause]
        have hclR' : ConvMod (EStep tbl) LvlEq .star (dr.eps σ ρ) := by
          rw [instEnd_eps_keep hbody harg hA hu, hbb] at hclR; exact hclR
        show ES tbl σ ρ _
        simp only [ES, CvP.dl, CvP.dr, hdl]
        exact hclR'
      · have hgbN : g.hbody.eps σ (.keep :: ρ) ≠ .star := fun h => hbb (htagB.mp h)
        have happ : appClause (.lam (g.hbody.eps σ (.keep :: ρ))) (g.harg.eps σ ρ) =
            .app (.lam (g.hbody.eps σ (.keep :: ρ))) (g.harg.eps σ ρ) :=
          appClause_app (fun h => ETm.noConfusion h) hgaN
        have hdl : dl.eps σ ρ =
            .app (.lam (g.hbody.eps σ (.keep :: ρ))) (g.harg.eps σ ρ) := by
          rw [hW]; unfold redexClauseOf
          rw [hgu, binderDisp_keep]
          simp only [redexClause, lamErasure, lamClause_of_ne hgbN, happ]
        have hclR' : ConvMod (EStep tbl) LvlEq
            (ETm.inst 0 (harg.eps σ ρ) (hbody.eps σ (.keep :: ρ))) (dr.eps σ ρ) := by
          rwa [instEnd_eps_keep hbody harg hA hu] at hclR
        exact es_beta_rel hA hbody harg dl dr
          (hdl ▸ (convMod_app (convMod_lam hclB) hclA)) hclR'

/-! ## §2 `es_lam` -/

/-- The `es_lam` ports the issued-row grammar cannot currently supply; see the
    module docstring for the per-field accounting against §3.4. -/
structure LamPorts (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (σ : Level → Level) (ρ : List Disp) : Type where
  /-- `HL := lamDomain dl rfl`: the left endpoint's λ reading. -/
  gotL : LamGot Aw (dl.wt Aw) E n Γ A b
  /-- `dl` erases to the read's λ clause. -/
  epsL : dl.eps σ ρ = lamClauseOf gotL σ ρ
  /-- `HR := lamDomain dr rfl`: the right endpoint's λ reading. -/
  gotR : LamGot Aw (dr.wt Aw) E n Γ A' b'
  /-- `dr` erases to the read's λ clause. -/
  epsR : dr.eps σ ρ = lamClauseOf gotR σ ρ
  /-- `BIT[HL.H, hA.dl]`. -/
  bitL : levelIsZero (σ gotL.u) = levelIsZero (σ u)
  /-- `BIT[HR.H, hA.dr]` — the regularity side, not `piDomSrc dr.reg.2`. -/
  bitR : levelIsZero (σ gotR.u) = levelIsZero (σ u)
  /-- `CL[gL.hbody, hb.dl]` at the binder display. -/
  bodyL : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ) gotL.hbody hb.dl
  /-- `CL[cctx hb.dr hA, gR.hbody]` at the binder display. -/
  bodyR : CL tbl σ (binderDisp (levelIsZero (σ u)) :: ρ)
    (TyP.cctx E n Γ b' B A A' u hb.dr hA) gotR.hbody
  /-- `Tag[gL.hbody, hb.dl]`. -/
  tagL : (gotL.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)
  /-- `Tag[hb.dr, gR.hbody]` (through `eps_cctx`). -/
  tagR : (hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (gotR.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)
  /-- `Tag[hb.dl, hb.dr]` — the body's own pair tag. -/
  bodyTag : (hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star) ↔
    (hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star)

/-- `es_lam` under the residual ports.  Uses `lam_esB` (issued, `rule_sub_before`)
    plus the landed `es_lam_drop`/`es_lam_keep`/`es_lam_star` finishers. -/
theorem es_lam (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : LamPorts Aw tbl hA hb dl dr σ ρ) :
    CaseStep Aw tbl (.es (CvP.lam E n Γ A A' b b' B u hA hb dl dr) S σ ρ) := by
  intro hq ih
  obtain ⟨gL, epsL, gR, epsR, bitL, bitR, bodyL, bodyR, tagL, tagR, tagB⟩ := ports
  -- `lam_esB`: the body `ES` one binder up — issued, `Before` by `rule_sub_before`.
  have hBod : ConvMod (EStep tbl) LvlEq
      (hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ))
      (hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ)) :=
    ih_issue Aw tbl hq ih
      (.es hb S σ (binderDisp (levelIsZero (σ u)) :: ρ)) Issues.lam_esB
      (rule_sub_before Aw (CvP.lam E n Γ A A' b b' B u hA hb dl dr) rfl hb
        (by simp only [CvP.wt]; omega) S σ ρ _)
  unfold CL at bodyL bodyR
  simp only [eps_cctx] at bodyR
  unfold lamClauseOf at epsL epsR
  rw [bitL] at epsL
  rw [bitR] at epsR
  by_cases hs : hb.dl.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star
  · -- both λ bodies are `★`: both erasures are `★`.
    have hgL : gL.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star :=
      tagL.mpr hs
    have hdr' : hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star :=
      tagB.mp hs
    have hgR : gR.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star :=
      tagR.mp hdr'
    have hdlS : dl.eps σ ρ = .star := by
      rw [epsL]
      cases hu : levelIsZero (σ u) with
      | true => rw [hu] at hgL; simpa only [lamErasure] using hgL
      | false => rw [hu] at hgL; simp only [lamErasure, hgL, lamClause]
    have hdrS : dr.eps σ ρ = .star := by
      rw [epsR]
      cases hu : levelIsZero (σ u) with
      | true => rw [hu] at hgR; simpa only [lamErasure] using hgR
      | false => rw [hu] at hgR; simp only [lamErasure, hgR, lamClause]
    exact es_lam_star hA hb dl dr hdlS hdrS
  · have hgLN : gL.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) ≠ .star :=
      fun h => hs (tagL.mp h)
    have hdrN : hb.dr.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) ≠ .star :=
      fun h => hs (tagB.mpr h)
    have hgRN : gR.hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) ≠ .star :=
      fun h => hdrN (tagR.mpr h)
    cases hu : levelIsZero (σ u) with
    | true =>
        rw [hu] at bodyL bodyR hgLN hgRN hBod
        have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
            (hb.dl.eps σ (.drop :: ρ)) := by
          rw [epsL, hu]; exact bodyL
        have hR : ConvMod (EStep tbl) LvlEq (hb.dr.eps σ (.drop :: ρ))
            (dr.eps σ ρ) := by
          rw [epsR, hu]; exact bodyR
        exact es_lam_drop hA hb dl dr hBod hL hR
    | false =>
        rw [hu] at bodyL bodyR hgLN hgRN hBod
        have hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
            (.lam (hb.dl.eps σ (.keep :: ρ))) := by
          rw [epsL, hu]
          show ConvMod _ _ (lamClause (gL.hbody.eps σ (binderDisp false :: ρ))) _
          rw [lamClause_of_ne hgLN]
          exact convMod_lam bodyL
        have hR : ConvMod (EStep tbl) LvlEq (.lam (hb.dr.eps σ (.keep :: ρ)))
            (dr.eps σ ρ) := by
          rw [epsR, hu]
          show ConvMod _ _ _ (lamClause (gR.hbody.eps σ (binderDisp false :: ρ)))
          rw [lamClause_of_ne hgRN]
          exact convMod_lam bodyR
        exact es_lam_keep hA hb dl dr hBod hL hR

end Rcic.Syn

#print axioms Rcic.Syn.BetaPorts
#print axioms Rcic.Syn.es_beta
#print axioms Rcic.Syn.LamPorts
#print axioms Rcic.Syn.es_lam
