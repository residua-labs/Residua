import rcic.RcicSynE
import rcic.RcicSynTableBuildI
import rcic.RcicSynCR
import rcic.RcicSynStarLift
import rcic.RcicSynSortRow
import rcic.RcicSynBelow
import rcic.RcicSynTableOfIFull

/-!
# `ConvModStarIffW` (row 2's named (c) residual) is refuted at EVERY table

glm-sr2's census (#7811, `RcicSynSRLitPiCLW.lean`) names the row-2 tag-wall
residual

    ConvModStarIffW tbl := ∀ a b, ConvMod (EStep tbl) LvlEq a b →
      (a = .star ↔ b = .star)

and cc's 04:15Z brief asks for it at the `TableClosed` tables, or an
inhabited instance at `tableOfI`. It is FALSE for every `tbl`, with no
table content involved: η alone refutes it. `EtaStep.eta .star` relates
`.lam (.app (.star.lift 0 1) (.bvar 0))` — not `.star` — to `.star`
(η-expansion of ★), so the iff fails on one `ConvMod.fwd` step:

* `convModStarIff_eta` — the refuting pair, as an inhabited conversion at
  every table (`ConvMod (EStep tbl) LvlEq (.lam …) .star`).
* `convModStarIffW_refuted` — the negated statement, every `tbl`.
* `convModStarIffW_refuted_tableOfI` — the instance at `tableOfI hW`, per
  the brief.

The star lemmas that ARE on the tree (`not_convMod_star_const`,
`eStep_pi_normal`, …) are per-normal-form non-convertibility facts; the
iff-shaped residual cannot be repaired by them. Any usable restatement has
to abandon "iff across conversion" (e.g. restrict one side to η-long
normal forms) — recorded here, not decided. `closure_claim = 0`.

# §2/§3 (cc 05:45Z brief) — CR at `tableOfI` + the ON-CONE measurement

The §1 refutation is OFF-CONE: `starEtaLHS = .lam (.app .star (.bvar 0))`
is the erasure of no typed subject (the `eps` `app` clause collapses any
application whose head erases to `★`, and the `lam` clause collapses any
abstraction whose body erases to `★`; so `.app ★ _` and `.lam ★` never
occur as `eps` images). The on-cone questions:

* EStep at `tableOfI` IS confluent — not new work: the tree already has
  both halves (`confluent_eStep_wf` under `TableWF`, batch 35, and
  `tableWF_tableOfI_full` from #7771). `confluent_eStep_tableOfI` below
  is the composite. Π-injectivity at `tableOfI`
  (`convE_pi_inv_tableOfI`, glm-sr3's app-app cell) follows the same way.
* The direction a tag consumer actually needs is ★-REACHABILITY, and it
  holds for EVERY term (no cone restriction needed):
  `convE_star_rstar_of_wf` / `convE_star_rstar_tableOfI`. The step from
  `a →* ★` to `a = ★` is exactly `EpsStarNormal` (§3), the erasure-side
  tag-coherence residue: on `ETm`, a non-`★` term can only move TOWARDS
  `★` through three entry shapes — (i) β at `.app (.lam ★) N`,
  (ii) η at `.lam (.app ★ (.bvar 0))` (i.e. `starEtaLHS` itself), and
  (iii) δ at a table rule whose closed rhs reaches `★`. The `eps` clauses
  kill (i)/(ii) as IMAGES; (iii) is tag coherence of the table's
  right-hand sides — `EpsStarNormal` names the whole gap extensionally.
  Row 2's tag wall is thereby REDUCED (not discharged) to the body-CL
  wall + `EpsStarNormal` (`tag_iff_of_cl_epsStarNormal`).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The η-expansion of `★`: the left endpoint of the refuting pair. -/
def starEtaLHS : ETm := .lam (.app (ETm.lift 0 1 .star) (.bvar 0))

theorem starEtaLHS_eq : starEtaLHS = .lam (.app (.star : ETm) (.bvar 0)) := rfl

theorem starEtaLHS_ne_star : starEtaLHS ≠ .star := by
  intro h
  exact ETm.noConfusion h

/-- The refuting conversion, inhabitable at every table: one forward η
    step from the η-expansion of `★` to `★` itself. -/
theorem convModStarIff_eta (tbl : List CRule) :
    ConvMod (EStep tbl) LvlEq starEtaLHS .star :=
  ConvMod.fwd (Or.inr (EtaStep.eta .star))

/-- **`ConvModStarIffW` is refuted at every table** — the iff fails on the
    η-expansion of `★`: the left endpoint is a `lam` (never `.star`), the
    right endpoint IS `.star`. -/
theorem convModStarIffW_refuted (tbl : List CRule) :
    ¬ (∀ (a b : ETm), ConvMod (EStep tbl) LvlEq a b → (a = .star ↔ b = .star)) := by
  intro hiff
  have h := hiff starEtaLHS .star (convModStarIff_eta tbl)
  exact starEtaLHS_ne_star (h.mpr rfl)

/-- The brief's instance: the residual is false at `tableOfI hW` for every
    well-formed environment — no `TableClosed`/`tableOfI` content can save
    it. -/
theorem convModStarIffW_refuted_tableOfI {E : ResolvedEnv} (hW : EnvWfT E) :
    ¬ (∀ (a b : ETm), ConvMod (EStep (tableOfI hW)) LvlEq a b → (a = .star ↔ b = .star)) :=
  convModStarIffW_refuted _

/-! ## §2 CR of `EStep` at `tableOfI`, assembled; ★-reachability -/

/-- `≈` relates `★` only to itself, on the right (dual of the landed
    `lvlEq_star_left`). -/
theorem lvlEq_star_right {x : ETm} (h : LvlEq x .star) : x = .star :=
  lvlEq_star_left (LvlEq.symm' h)

/-- CHURCH–ROSSELL FOR `EStep` AT `tableOfI` — the composite of the two
    landed halves (`confluent_eStep_wf`, RcicSynCR batch 35, and
    `tableWF_tableOfI_full`, #7771). No new confluence content; the value
    is the named instance every erased-calculus consumer at `tableOfI`
    (star-iff, Π-injectivity, family rigidity) can now cite directly. -/
theorem confluent_eStep_tableOfI {E : ResolvedEnv} (hW : EnvWfT E) :
    Confluent (EStep (tableOfI hW)) :=
  confluent_eStep_wf (tableWF_tableOfI_full hW)

/-- Π-INJECTIVITY AT `tableOfI` (`convE_pi_inv_wf` at `tableWF_tableOfI_full`)
    — glm-sr3's app-app cell need, as a citable instance. -/
theorem convE_pi_inv_tableOfI {E : ResolvedEnv} (hW : EnvWfT E) {A B A' B' : ETm}
    (h : ConvMod (EStep (tableOfI hW)) LvlEq (.pi A B) (.pi A' B')) :
    ConvMod (EStep (tableOfI hW)) LvlEq A A' ∧
      ConvMod (EStep (tableOfI hW)) LvlEq B B' :=
  convE_pi_inv_wf (tableWF_tableOfI_full hW) h

/-- ★-REACHABILITY, the direction every tag consumer needs: at any
    `TableWF` table, whatever converts to `★` REACHES `★` by `EStep*`.
    Holds for every term — the typed-subject restriction is not needed at
    this layer (CR + ★-normality + `≈`-splitting carry it alone). -/
theorem convE_star_rstar_of_wf {tbl : List CRule} (hW : TableWF tbl) {a : ETm}
    (h : ConvMod (EStep tbl) LvlEq a .star) : RStar (EStep tbl) a .star := by
  obtain ⟨x, y, hx, hq, hy⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) h
  have hy' := rstar_of_normal (eStep_star_normal tbl) hy
  subst hy'
  have hx' := lvlEq_star_right hq
  subst hx'
  exact hx

/-- ★-reachability at `tableOfI hW`. -/
theorem convE_star_rstar_tableOfI {E : ResolvedEnv} (hW : EnvWfT E) {a : ETm}
    (h : ConvMod (EStep (tableOfI hW)) LvlEq a .star) :
    RStar (EStep (tableOfI hW)) a .star :=
  convE_star_rstar_of_wf (tableWF_tableOfI_full hW) h

/-! ## §3 the on-cone delimitation: the tag iff, REDUCED -/

/-- THE CONSUMED DIRECTION, exactly: given the CL between two typings of
    one term, `★` on either side reaches `★` on the other. This is what
    row 2's step-2 (the `BetaBodyTagWall` consumer) actually needs first. -/
theorem cl_star_reaches {tbl : List CRule} (hW : TableWF tbl)
    {σ : Level → Level} {ρ : List Disp} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (hcl : CL tbl σ ρ D₁ D₂) (h₁ : D₁.eps σ ρ = .star) :
    RStar (EStep tbl) (D₂.eps σ ρ) .star :=
  convE_star_rstar_of_wf hW
    (ConvMod.symm' LvlEq.symm' (show ConvMod (EStep tbl) LvlEq .star (D₂.eps σ ρ) from h₁ ▸ hcl))

/-- THE NAMED RESIDUE (erasure-side tag coherence): an `eps` image that
    reaches `★` by `EStep*` already IS `★`. On raw `ETm` this is false
    (the three ★-entry shapes: β at `.app (.lam ★) N`, η at `starEtaLHS`,
    δ at a rule rhs reaching `★`); the `eps` clauses exclude the first two
    as images, the third is tag coherence of the table's right-hand sides. -/
def EpsStarNormal (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (σ : Level → Level) (ρ : List Disp),
    RStar (EStep tbl) (D.eps σ ρ) .star → D.eps σ ρ = .star

/-- The tag iff across a CL, from `EpsStarNormal`: row 2's
    `BetaBodyTagWall` (at `g.hbody`/`hbody`, display
    `binderDisp .. :: ρ`) is an instance — REDUCED to the body-CL wall
    (`BetaBodyClWall`, the CL between the two endpoints) plus
    `EpsStarNormal`. Two named open residues, no third ingredient. -/
theorem tag_iff_of_cl_epsStarNormal {tbl : List CRule} (hW : TableWF tbl)
    (hN : EpsStarNormal tbl)
    {σ : Level → Level} {ρ : List Disp} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T₁ T₂ : Expr Nat} {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (hcl : CL tbl σ ρ D₁ D₂) :
    (D₁.eps σ ρ = .star ↔ D₂.eps σ ρ = .star) := by
  constructor
  · intro h₁
    exact hN D₂ σ ρ (cl_star_reaches hW hcl h₁)
  · intro h₂
    exact hN D₁ σ ρ
      (cl_star_reaches hW (ConvMod.symm' LvlEq.symm' hcl) h₂)

end Rcic.Syn

#print axioms Rcic.Syn.convModStarIff_eta
#print axioms Rcic.Syn.convModStarIffW_refuted
#print axioms Rcic.Syn.convModStarIffW_refuted_tableOfI
#print axioms Rcic.Syn.lvlEq_star_right
#print axioms Rcic.Syn.confluent_eStep_tableOfI
#print axioms Rcic.Syn.convE_pi_inv_tableOfI
#print axioms Rcic.Syn.convE_star_rstar_of_wf
#print axioms Rcic.Syn.convE_star_rstar_tableOfI
#print axioms Rcic.Syn.cl_star_reaches
#print axioms Rcic.Syn.EpsStarNormal
#print axioms Rcic.Syn.tag_iff_of_cl_epsStarNormal
