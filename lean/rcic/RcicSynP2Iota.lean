import rcic.RcicSynNatSuccIota

/-!
# S16 §4.3/§4.5 — `iota_erasure_from_answers`, generic ι composition

`research/rcic/sortrow/S16_BVAR_CCTX_IOTA_STEPS.md` §4.3 (the four fixed
outer requests of the retained-result ι branch) and §4.5 (the final
simulation inside the current case).

* §4.3: `qCLL = CL[dl, hlhs]`, `qCLR = CL[hrhs, dr]`,
  `qPL = PB[hlhs, tL]`, `qPR = PB[hrhs, tL]` with `tL = hlhs.reg.2`.
* §4.5: `hlhs.eps ↔ the real matched lhs → the real CRoot rhs →β*
  the same finite template instance ↔ hrhs.eps`, connected to the two CL
  answers.

`iota_erasure_from_answers` takes the four answers, the real match, a
`CRoot` step and a finite `RStar (RStep tbl)` β witness **as
hypotheses** — never `ES H` itself, and never a same-rank
"the whole spine is right" supplier (§4.5's prohibition). The PB
answers travel as answer data per §4.3; the composition itself consumes
the CLs (the PBs feed §4.4's slot consumers — they do not decide whether
the major is erased).

First user: the S17 Nat-successor instance (`RcicSynNatSuccIota`),
re-derived through the generic composition.

`closure_claim = 0`; T7 declaration correspondence stays the open wall.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- A finite `RStep` chain lifts to `ConvMod (EStep tbl) LvlEq`: each
    step is injected by `.inl`. The §4.5 `→β*` leg's transport type. -/
theorem convMod_of_rstar_estep {tbl : List CRule} {a b : ETm}
    (h : RStar (RStep tbl) a b) : ConvMod (EStep tbl) LvlEq a b := by
  induction h with
  | refl a => exact .refl a
  | step h1 _ ih => exact .trans (.fwd (.inl h1)) ih

/-- S16 §4.3+§4.5: the retained-result `ES` of `CvP.iota`, composed from
    the four fixed outer answers, the real match legs, the real `CRoot`
    step and a finite `→β*` witness. The chain is
    `dl.eps ≡ hlhs.eps ≡ el →cr erhs →β* er ≡ hrhs.eps ≡ dr.eps`. -/
theorem iota_erasure_from_answers {tbl : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    {σ : Level → Level} {ρ : List Disp} {el erhs er : ETm}
    (h : DerivedIota E lhs rhs)
    (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (qCLL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hlhs.eps σ ρ))
    (qCLR : ConvMod (EStep tbl) LvlEq (hrhs.eps σ ρ) (dr.eps σ ρ))
    (qPL : PBit σ ρ hlhs hlhs.reg.2)
    (qPR : PBit σ ρ hrhs hlhs.reg.2)
    (hmatchL : ConvMod (EStep tbl) LvlEq (hlhs.eps σ ρ) el)
    (hcroot : CRoot tbl el erhs)
    (hbeta : RStar (RStep tbl) erhs er)
    (hmatchR : ConvMod (EStep tbl) LvlEq er (hrhs.eps σ ρ)) :
    ES tbl σ ρ (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) := by
  have hchain : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ) :=
    qCLL.trans (hmatchL.trans
      ((ConvMod.fwd (.inl (.cr hcroot))).trans
        ((convMod_of_rstar_estep hbeta).trans (hmatchR.trans qCLR))))
  simpa [ES, CvP.dl, CvP.dr] using hchain

/-! ## first user: the S17 Nat-successor instance -/

/-- PIN: `H`'s stored endpoints are literally `hL`/`hR` — the four
    original occurrences, not rebuilt typings. -/
theorem s17_H_dl_eq : H.dl = hL := rfl

theorem s17_H_dr_eq : H.dr = hR := rfl

/-- §4.5's left match leg for `wSuccU1`: `hL.eps id []` is kernel-`EL`. -/
theorem s17_matchL :
    ConvMod (EStep natSuccTable) LvlEq (hL.eps id []) EL :=
  .refl _

/-- §4.5's right match leg: `ER` is kernel-`hR.eps id []`. -/
theorem s17_matchR :
    ConvMod (EStep natSuccTable) LvlEq ER (hR.eps id []) :=
  .refl _

/-- §4.5's finite β witness — the four real `s17Step`s as an `RStar`. -/
def s17_beta_witness :
    RStar (RStep natSuccTable)
      (ETm.appN (natSuccRule.rhs [.succ .zero] []) [Pε, Zε, msε, Zε]) ER :=
  .step s17Step1 (.step s17Step2 (.step s17Step3 (.step s17Step4 (.refl ER))))

/-- PIN: `hL`'s register level is `succ zero` — `N`'s own sort. -/
theorem s17_hL_reg1 : hL.reg.1 = .succ .zero := rfl

/-- §4.3 `PB[hlhs, tL]`: `hL.eps` is the non-star `EL` and the register
    level `succ zero` is not zero — both iff-sides decide `false`. -/
theorem s17_qPL : PBit id [] hL hL.reg.2 :=
  iff_of_false (by rw [hL_eps_el]; decide) (by rw [s17_hL_reg1]; decide)

/-- §4.3 `PB[hrhs, tL]` — same `tL = hlhs.reg.2`, per the spec's
    `qPR = PB[hrhs, hlhs.reg.2]`. -/
theorem s17_qPR : PBit id [] hR hL.reg.2 :=
  iff_of_false (by rw [hR_eps_er]; decide) (by rw [s17_hL_reg1]; decide)

/-- First user of the generic composition: `ES natSuccTable id [] H`
    through §4.3's four answers plus the §4.5 match/CRoot/β* chain. The
    two CL answers are `.refl` because `H`'s stored endpoints are the
    four original occurrences; the same conclusion was reached directly
    by `natSucc_iota_erasure`. -/
theorem natSucc_iota_erasure_via_answers : ES natSuccTable id [] H :=
  iota_erasure_from_answers (DerivedIota.of wSuccU1) hL hR hL hR
    (.refl _) (.refl _) s17_qPL s17_qPR
    s17_matchL natSucc_croot s17_beta_witness s17_matchR

end Rcic.Syn

#print axioms Rcic.Syn.convMod_of_rstar_estep
#print axioms Rcic.Syn.iota_erasure_from_answers
#print axioms Rcic.Syn.s17_H_dl_eq
#print axioms Rcic.Syn.s17_H_dr_eq
#print axioms Rcic.Syn.s17_matchL
#print axioms Rcic.Syn.s17_matchR
#print axioms Rcic.Syn.s17_beta_witness
#print axioms Rcic.Syn.s17_hL_reg1
#print axioms Rcic.Syn.s17_qPL
#print axioms Rcic.Syn.s17_qPR
#print axioms Rcic.Syn.natSucc_iota_erasure_via_answers
