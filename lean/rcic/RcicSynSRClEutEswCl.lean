import rcic.RcicSynSRClEutEswEut
import rcic.RcicSynSRClEutClCase
import rcic.RcicErasedMajorMode
import rcic.RcicSynSortPBit

/-!
# RcicSynSRClEutEswCl — row 14 (`cl_case`) under `epsW`: the eqN-bit wall

cc 2026-10-20 20:00Z brief, lane glm-sr3. Row 14's measured wall splits in
two, and epsW moves only one half:

* The `constCl` eqN-bit wall is ERASURE-FREE: `ClConstPorts.hbit` is
  `ls₁ ≠ ls₂ → levelIsZero (σ u₁) = levelIsZero (σ u₂)` — no `eps`
  anywhere. Its gated restatement (`clConstP_esw`, below) is therefore the
  SAME Prop as #7800's `clConstP_lhom_tableOfI`; `clConstPorts_esw_of_eqN`
  re-proves the eqN-transport (the σ-distinguisher is gone at `LevelHom σ`)
  and `clConstP_esw_ident_sat` re-pins the identical-instance tooth. epsW
  changes NOTHING on this wall — a gated refutation remains sort-level
  non-uniqueness content, i.e. the row itself.
* The eps-BEARING cells restate at `epsW`. The load-bearing one (row 15's
  twin) is the lam cell: `ClLamPortsW` (`bodyClW : CLW`, `shapeW` at
  `epsW`), wall `cl_lam_wallW`, ident-satisfied. The `piCl`/`appCl`/
  `letCl`/`clOther` cells are retained unmeasured under epsW (their
  landed `eps` shapes stand; `cl_residualTag_caseStep` is still row 14's
  missing lemma).

Verdict: row 14's gated CLW field is OPEN at exactly these walls.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins

variable {E : ResolvedEnv} {Eₐ : ResolvedEnv}

/-- `hbit` at the gate is `eqN`-transported, table-independent: the
    σ-distinguisher (#7781's `sr3σ`) is GONE at `LevelHom σ`. Identical to
    #7800's `clConstPorts_of_eqN_lhom` — re-proved here because the epsW
    branch does not carry #7800's modules; the Prop is erasure-free. -/
theorem clConstPorts_esw_of_eqN (tbl : List CRule)
    {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    {σ : Level → Level} {ρ : List Disp} (hσ : LevelHom σ) (h : eqN u₁ u₂)
    (hT₁ : TyP E' n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E' n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂)) :
    ClConstPorts tbl σ ρ hT₁ hT₂ :=
  ⟨fun _ => levelIsZero_eqN_congr (hσ.eqN_map h)⟩

/-- Row 14's gated constCl wall under epsW — ONE named Prop. `hbit`
    mentions no erasure, so this is literally #7800's
    `clConstP_lhom_tableOfI` restated on the epsW branch: the residual
    content is sort-level uniqueness (`eqN u₁ u₂` for two typings of the
    same member type), nothing more. -/
def clConstP_esw (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hT₁ : TyP E' n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E' n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    {σ : Level → Level} {ρ : List Disp}, LevelHom σ →
    ClConstPorts (tableOfI hW) σ ρ hT₁ hT₂

/-- Tooth: the gated wall's conclusion is inhabited at an identical closed
    instance (`sr3hT₁` on both sides, `σ := id`, `ρ := []`). -/
theorem clConstP_esw_ident_sat (hW : EnvWfT emptyEnv) :
    ClConstPorts (tableOfI hW) id [] sr3hT₁ sr3hT₁ :=
  ⟨fun _ => rfl⟩

/-- `ClLamPorts` restated at the display-aware erasure: the common-body
    coherence at `CLW`, the ★-shape split computed by `epsW`. -/
structure ClLamPortsW (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body : Expr Nat}
    {B₁ B₂ : Expr Nat} (u₁ : Level)
    (hb₁ : TyP E n (.assumption A :: Γ) body B₁)
    (hb₂ : TyP E n (.assumption A :: Γ) body B₂) : Prop where
  bodyClW : CLW tbl σ (binderDisp (levelIsZero (σ u₁)) :: ρ) hb₁ hb₂
  shapeW : (hb₁.epsW σ (.keep :: ρ) = .star ∧ hb₂.epsW σ (.keep :: ρ) = .star) ∨
      (hb₁.epsW σ (.keep :: ρ) ≠ .star ∧ hb₂.epsW σ (.keep :: ρ) ≠ .star)

/-- Row 14's epsW-bearing lam-lam wall, ONE named Prop: the common-body
    `ClLamPortsW` at `tableOfI hW`, gated at the `LevelHom σ` every
    demanded `.cl` cell carries. -/
def cl_lam_wallW (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body B₁ B₂ : Expr Nat}
    {u₁ : Level}
    (hb₁ : TyP E' n (.assumption A :: Γ) body B₁)
    (hb₂ : TyP E' n (.assumption A :: Γ) body B₂)
    {σ : Level → Level} {ρ : List Disp}, LevelHom σ →
    ClLamPortsW (tableOfI hW) σ ρ u₁ hb₁ hb₂

/-- Tooth: the W-wall's conclusion is inhabited at an identical cell
    instance — `bodyClW` reflexive; the `epsW` shape split taken on the
    right (the fixture body `hs0s` erases to `.sort 0`, never `★`). -/
theorem cl_lam_wallW_ident_sat (hW : EnvWfT E) :
    ClLamPortsW (tableOfI hW) id [] two hs0s hs0s :=
  ⟨ConvMod.refl _,
    Or.inr (And.intro (fun h => nomatch h) (fun h => nomatch h))⟩

#print axioms clConstPorts_esw_of_eqN
#print axioms clConstP_esw
#print axioms clConstP_esw_ident_sat
#print axioms ClLamPortsW
#print axioms cl_lam_wallW
#print axioms cl_lam_wallW_ident_sat

end Rcic.Syn
