import rcic.RcicSynSRClEutEswCl
import rcic.RcicParRedCore
import rcic.RcicLevelCalc
import rcic.RcicTypedRowsSupplyPins

/-!
# RcicSynSREqnClW — row 14 (`cl_case`) at the hom-gated eqN-bit wall

cc 2026-10-20 22:50Z brief, lane glm/sr4-eqn. The wall: `ClConstPorts.hbit`
owes `ls₁ ≠ ls₂ → levelIsZero (σ u₁) = levelIsZero (σ u₂)`. It mentions no
`eps`, so it is a pure level fact about the constants' universe arguments
at the CL query.

What the query knows about `u₁ u₂` (measured, this module):

* the const/const cell's own data pins both instantiation lists to one raw
  list (`hls₁ : eqNList ls ls₁`, `hls₂ : eqNList ls ls₂`);
  `eqNList_of_gates` composes them;
* the typings pin each `uᵢ` to the member type's universe at that
  instantiation — ONE `v` for both (`cl_common_sort`), which forces
  `eqN u₁ u₂` (`eqN_of_common_sort`, via `instLevel_eqNList`).

The gated `hbit` stated with exactly that knowledge is PROVED
(`cl_hbit_hom_of_common_sort`, via `levelIsZero_eqN_congr` ∘
`LevelHom.eqN_map` — #7800's `clConstPorts_esw_of_eqN` route, i.e. sr2's
`levelIsZero_congr_hom` composition), it supplies the full ports record
(`clConstPorts_of_common_sort`), and the hom-gated cell wall
`cl_case_wall_hom` REDUCES to the knowledge
(`cl_case_wall_hom_of_knowledge`).

Exact residue: `cl_common_sort` itself — TyP-layer sort-typing pinning
(two sort-typings of one member type at eqNList-related instantiations
share one universe `v`). Named, not claimed. The T-layer analogue
(`DT012T_type_uniqueness_of_typedRowsWf`) needs `TypedRowsWf`/`CtxWfT` and
does not reach the TyP demand. No on-cone refutation is constructible:
`cl_hbit_sr3_hom` kills the standing fixture at every `LevelHom σ` (its
`u₁ u₂` are eqN — only the non-hom `sr3σ` separated them), and every `CvP`
route between sort-typed endpoints is eqN-disciplined (`sorts` is
eqN-guarded; the computational rules track values with endpoint typings at
the conversion's own type; the transports are level-structural; `irr`
would need a sort-zero typing). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Declarative.Ann (eqN_one_max)
open DispForPathPins (one two)

variable {E : ResolvedEnv}

/-- The const/const cell's own data pins both instantiation lists to the
    raw list `ls`; composed, the two refined lists are `eqNList`-related. -/
theorem eqNList_of_gates {ls ls₁ ls₂ : List Level}
    (hls₁ : eqNList ls ls₁) (hls₂ : eqNList ls ls₂) : eqNList ls₁ ls₂ :=
  eqNList_trans (eqNList_symm hls₁) hls₂

/-- The common-sort knowledge forces the universe arguments `eqN`-equal:
    both `uᵢ` land on `instLevel lsᵢ v` for one `v`, and `instLevel_eqNList`
    moves between the two instantiations. -/
theorem eqN_of_common_sort {ls₁ ls₂ : List Level} {u₁ u₂ : Level}
    (h : eqNList ls₁ ls₂)
    (hv : ∃ v, eqN u₁ (instLevel ls₁ v) ∧ eqN u₂ (instLevel ls₂ v)) :
    eqN u₁ u₂ := by
  obtain ⟨v, h1, h2⟩ := hv
  exact eqN_trans h1 (eqN_trans (instLevel_eqNList h v) (eqN_symm h2))

/-- The gated `hbit` stated with exactly the query's knowledge (the
    common-sort pinning + the `eqNList` gates), PROVED at every
    `LevelHom σ`: the erasure bits agree. Same composition as #7800's
    `clConstPorts_esw_of_eqN` (the eqN-knowledge twin; sr2's
    `levelIsZero_congr_hom` route). -/
theorem cl_hbit_hom_of_common_sort {σ : Level → Level} (hσ : LevelHom σ)
    {ls₁ ls₂ : List Level} {u₁ u₂ : Level} (h : eqNList ls₁ ls₂)
    (hv : ∃ v, eqN u₁ (instLevel ls₁ v) ∧ eqN u₂ (instLevel ls₂ v)) :
    levelIsZero (σ u₁) = levelIsZero (σ u₂) :=
  levelIsZero_eqN_congr (hσ.eqN_map (eqN_of_common_sort h hv))

/-- The knowledge supplies the full ports record at every table. -/
theorem clConstPorts_of_common_sort (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ls₁ ls₂ : List Level}
    {m : CheckedMember} {u₁ u₂ : Level} {σ : Level → Level} {ρ : List Disp}
    (hσ : LevelHom σ) (h : eqNList ls₁ ls₂)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    (hv : ∃ v, eqN u₁ (instLevel ls₁ v) ∧ eqN u₂ (instLevel ls₂ v)) :
    ClConstPorts tbl σ ρ hT₁ hT₂ :=
  ⟨fun _ => cl_hbit_hom_of_common_sort hσ h hv⟩

/-- Row 14's exact residue, ONE named Prop (not claimed): two sort-typings
    of one member type at `eqNList`-related instantiations pin their
    universe arguments to a single `v`. The const cell's own data
    (`hres`/`hlen`/`hwf`/`hls`) contributes only `eqNList ls₁ ls₂`; the
    pinning itself is TyP-layer sort-typing determinacy at instantiated
    subjects — the T-layer analogue (`DT012T_type_uniqueness_of_typedRowsWf`)
    needs `TypedRowsWf`/`CtxWfT` and does not reach this demand. -/
def cl_common_sort : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ls₁ ls₂ : List Level}
    {m : CheckedMember} {u₁ u₂ : Level}
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    (h : eqNList ls₁ ls₂),
    ∃ v, eqN u₁ (instLevel ls₁ v) ∧ eqN u₂ (instLevel ls₂ v)

/-- Row 14's hom-gated cell wall, ONE named Prop: `cl_case_wall`'s data
    (member receipts + `levelsBounded` + the `eqNList` gates) with the
    demand's `LevelHom σ`, at `tableOfI hW`. -/
def cl_case_wall_hom (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E'.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E' n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hres₂ : E'.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E' n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    {σ : Level → Level} {ρ : List Disp}, LevelHom σ →
    ClConstPorts (tableOfI hW) σ ρ hT₁ hT₂

/-- The hom-gated cell wall is CLOSED relative to the knowledge: the gated
    `hbit` is proved, so exactly `cl_common_sort` remains. -/
theorem cl_case_wall_hom_of_knowledge (hW : EnvWfT E)
    (hK : cl_common_sort) : cl_case_wall_hom hW := by
  intro E' n Γ r ls ls₁ ls₂ m u₁ u₂ hres₁ hlen₁ hwf₁ hls₁ hT₁
    hres₂ hlen₂ hwf₂ hls₂ hT₂ σ ρ hσ
  have hls : eqNList ls₁ ls₂ := eqNList_of_gates hls₁ hls₂
  exact clConstPorts_of_common_sort _ hσ hls hT₁ hT₂ (hK hT₁ hT₂ hls)

/-- The fixture's lists are `eqNList`-related (pointwise eqN) even though
    syntactically distinct (`sr3hne`); `eqN_one_max` is landed. -/
theorem sr3_eqNList : eqNList [one] [.max one one] :=
  ⟨eqN_one_max, True.intro⟩

/-- Tooth: the standing fixture does not separate at any `LevelHom σ` —
    both universe arguments are succ-headed after the hom's structural
    maps, so only the non-hom `sr3σ` ever refuted the raw premise. -/
theorem cl_hbit_sr3_hom {σ : Level → Level} (hσ : LevelHom σ) :
    levelIsZero (σ two) = levelIsZero (σ (.succ (.max one one))) := by
  have h2 : two = .succ one := rfl
  rw [h2, hσ.map_succ, hσ.map_succ, hσ.map_max]
  rfl

/-- `succ (max 1 1) =ₙ 2`, the fixture's second universe pin. -/
theorem eqN_succ_max_one_one : eqN (.succ (.max one one)) two := by
  intro ρ
  rfl

/-- Tooth: the knowledge is inhabited at the standing fixture — `v := two`
    pins both sides (both instantiations are param-free at `v`, so
    `instLevel` is the identity; `succ (max 1 1) =ₙ 2`). -/
theorem cl_common_sort_sr3_fixture :
    ∃ v, eqN two (instLevel [one] v) ∧
      eqN (.succ (.max one one)) (instLevel [.max one one] v) := by
  refine ⟨two, eqN_refl _, ?_⟩
  have hId : instLevel [.max one one] two = two := rfl
  rw [hId]
  exact eqN_succ_max_one_one

#print axioms eqNList_of_gates
#print axioms eqN_of_common_sort
#print axioms cl_hbit_hom_of_common_sort
#print axioms clConstPorts_of_common_sort
#print axioms cl_common_sort
#print axioms cl_case_wall_hom
#print axioms cl_case_wall_hom_of_knowledge
#print axioms sr3_eqNList
#print axioms cl_hbit_sr3_hom
#print axioms cl_common_sort_sr3_fixture
#print axioms eqN_succ_max_one_one

end Rcic.Syn
