import rcic.RcicSynSREqnAnswer

/-!
# RcicSynSREqnAlias — row 14: outside the `{sort, pi}` fragment, measured

cc 2026-10-21 05:45Z brief, lane glm/sr4-eqn (#7809). Ask: measure what lies
outside the fragment (member types not in `SortPiFrag`) with a concrete
admitted member. Fixture, this module: `sr4AliasMem`, an arity-1 axiom
member whose type is the UNIVERSE ALIAS `.const 0 [.param 0]` over the
standing fixture's `sr3Mem` (`Type_(param 0)`-member) — admitted at
`sr4AliasEnv` (index 1), level-polymorphic, and OUTSIDE the fragment
(`sr4AliasT₁_not_frag`: a `TyP.const` node is neither sort nor pi).

Measurement:

* **The boundary is not the const constructor.** The cell's universes at
  the alias member are pinned THROUGH the const node's own inner `hT`
  field — a sort leaf at the aliased universe — so the eqN-chain of the
  fragment extends one layer: at `ls₁ := [1]`, `ls₂ := [max 1 1]` the
  universes are `1` and `max 1 1`, eqN by the landed `eqN_one_max`, and
  the row-14 const cell at the CONCRETE admitted member is DISCHARGED
  (`cl_const_caseStep_alias`) — no port, no edge, no global lemma.
* **Where the chain stops** (measurement, not a fixture): the pairing
  consumes constructor premises that relate universes to parameters
  (sort's `eqN k (succ l)`, pi's `imax` arms, const's instantiated inner
  `hT`). A sort-typing justified by `TyP.conv` has its universe pinned by
  the CONVERSION (`c : A ≡ .sort u`), not by any constructor premise —
  there the chain has nothing to walk, and the supply-side pinning is
  exactly the standing `cl_common_sort` residue (the CvP eqN-discipline
  measurement of `RcicSynSREqnClW`). So the fragment boundary of the
  ANSWER route is: conv-justified universes, not const layers.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Declarative.Ann (eqN_one_max)
open DispForPathPins (one)

/-! ## §1 the concrete admitted member, outside the fragment -/

/-- The universe-alias member: `alias α := const 0 [α]` over the standing
    fixture's `sr3Mem` (`Type_(param 0)`-member, arity 1). Level-polymorphic,
    admitted at index 1. -/
def sr4AliasMem : CheckedMember :=
  { mclass := .axiomM, arity := 1, mtype := .const 0 [.param 0], body := none }

def sr4AliasEnv : ResolvedEnv := extendEnv sr4Env 1 sr4AliasMem

theorem sr4AliasEnv_members1 : sr4AliasEnv.members 1 = some sr4AliasMem := rfl

theorem sr4AliasEnv_members0 : sr4AliasEnv.members 0 = some sr3Mem := rfl

/-- The alias member's sort-typings at the two instantiations: a `TyP.const`
    node whose inner `hT` is the aliased universe's sort leaf — OUTSIDE the
    `{sort, pi}` fragment (pinned below), yet eqN-chained through it. -/
def sr4AliasT₁ : TyP sr4AliasEnv 2 []
    (instantiateLevels [one] sr4AliasMem.mtype) (Expr.sort one) :=
  TyP.const sr4AliasEnv 2 [] 0 [one] [one] sr3Mem (.succ one)
    sr4AliasEnv_members0 rfl rfl (eqNList_refl _)
    (TyP.sort sr4AliasEnv 2 [] one (.succ one) (eqN_refl _))

def sr4AliasT₂ : TyP sr4AliasEnv 2 []
    (instantiateLevels [.max one one] sr4AliasMem.mtype)
    (Expr.sort (.max one one)) :=
  TyP.const sr4AliasEnv 2 [] 0 [.max one one] [.max one one] sr3Mem
    (.succ (.max one one)) sr4AliasEnv_members0 rfl rfl (eqNList_refl _)
    (TyP.sort sr4AliasEnv 2 [] (.max one one) (.succ (.max one one)) (eqN_refl _))

/-- The fixture is OUTSIDE the fragment: a `TyP.const` node is neither of
    the fragment's two constructors. -/
theorem sr4AliasT₁_not_frag : ¬ SortPiFrag sr4AliasT₁ := by
  intro h
  cases h

/-! ## §2 the cell at the concrete member: DISCHARGED -/

/-- The row-14 const/const cell at the concrete admitted NON-fragment
    member, DISCHARGED: the universes `one` / `max one one` are pinned
    through the alias's own inner sort leaves, eqN by the landed
    `eqN_one_max`, and the bit lands at every #7800 `LevelHom` — the same
    mechanism as `cl_const_caseStep_sortPiFree`, one const layer further
    out. No port, no issuance edge, no global lemma. -/
theorem cl_const_caseStep_alias (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {σ : Level → Level}
    (hσ : LevelHom σ) (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (ρ : List Disp) :
    CaseStep Aw tbl (.cl
      (TyP.const sr4AliasEnv 2 [] 1 [one] [one] sr4AliasMem one
        sr4AliasEnv_members1 rfl rfl (eqNList_refl _) sr4AliasT₁)
      (TyP.const sr4AliasEnv 2 [] 1 [one] [.max one one] sr4AliasMem (.max one one)
        sr4AliasEnv_members1 rfl rfl sr3_eqNList sr4AliasT₂)
      S σ ρ) := by
  intro _ _
  have hlen : [one].length = sr4AliasMem.arity := rfl
  exact cl_const_nodes tbl σ ρ sr4AliasEnv_members1 hlen rfl (eqNList_refl _)
    sr4AliasT₁ sr4AliasEnv_members1 hlen rfl sr3_eqNList sr4AliasT₂
    (levelIsZero_eqN_congr (hσ.eqN_map eqN_one_max))

#print axioms Rcic.Syn.sr4AliasMem
#print axioms Rcic.Syn.sr4AliasEnv
#print axioms Rcic.Syn.sr4AliasEnv_members1
#print axioms Rcic.Syn.sr4AliasEnv_members0
#print axioms Rcic.Syn.sr4AliasT₁
#print axioms Rcic.Syn.sr4AliasT₂
#print axioms Rcic.Syn.sr4AliasT₁_not_frag
#print axioms Rcic.Syn.cl_const_caseStep_alias

end Rcic.Syn
