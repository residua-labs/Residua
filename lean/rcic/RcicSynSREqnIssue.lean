import rcic.RcicSynSREqnClW
import rcic.RcicSynStepCore4

/-!
# RcicSynSREqnIssue — row 14 const cell: the issuance measurement (cc 23:55Z)

cc 2026-10-20 23:55Z brief, lane glm/sr4-eqn. Question: is `cl_common_sort`
a CL/EUT fact about two typings of ONE (smaller) subject that the `cl_case`
const cell must ISSUE as an existing query kind with rank decreasing? If no
such subject pair exists: say exactly why. Answer, measured here:

**No such subject pair exists, for two independent reasons.**

1. **Kind shape.** Every existing two-derivation kind binds ONE subject
   (`.cl`/`.eut`/`.pb`/`.bitCoh`/`.mixed`: the constructor's two typings
   share `e`/`T`), or ONE conversion (`.es`/`.cts`/`.head`: the sort-typings
   sit at the conversion's endpoints). The const cell's two universes `u₁ u₂`
   are carried by `hT₁ : TyP _ _ _ (instantiateLevels ls₁ m.mtype) (.sort u₁)`
   and `hT₂ : TyP _ _ _ (instantiateLevels ls₂ m.mtype) (.sort u₂)` — two
   INDEPENDENT typings of two distinct stuck subjects (the instantiation
   lists differ). Side-0's payload mentions only `ls, ls₁`; side-1's only
   `ls, ls₂`; no `occ_*` pair row types across the sides unless the subjects
   coincide — which for stuck `instantiateLevels` at `ls₁ ≠ ls₂` is exactly
   `ls₁ = ls₂`, the already-closed ident branch, or a defeq-coinciding
   member type (closed below: `cl_const_caseStep_sortOne`). No `CvP` rule
   converts one instantiation into the other (`consts` converts the CONST
   terms `.const r ls ≡ .const r ls'` at the LEFT instantiation's member
   type; `sorts` only sort-headed instantiations; there is no
   instantiation-invariance congruence for `CvP`), so no conversion-parametrized
   kind can be built from the cell's data either.
2. **Rank.** The one constructible bridge at a sort-headed member — the
   `sorts` conversion between the two instantiated member levels, built from
   `eqN`-congruence — is NEW material: presenting it as a `.cts` root against
   the cell's own typing has no rank decrease. Kernel pin:
   `cl_cts_sorts_not_before_minimal` — at the minimal fixture (`sr3Mem`,
   `ls₁ := [1]`, `ls₂ := [max 1 1]`, `Aw := fun _ => 0`) the conversion's
   atom (weight 3) has no owner above it in the const pair's atoms `[2, 2]`
   (the `pin_bridge_endpoint_rejected` domination shape), so `LexDM` fails
   and the presentation is not `Before` the cell's query at that frame.

**Positive fragment (the principle demonstrated):** when the member type
coincides at both instantiations up to defeq — e.g. `m.mtype = .sort one`,
param-free, so `instantiateLevels lsᵢ (.sort one) ≡ .sort one` for every
`lsᵢ` — the two sort-typings ARE two typings of ONE subject, the existing
`occ_bitCoh` edge fires from the cell exactly as in the ident branch, and
the const cell is CLOSED with no port and no global lemma
(`cl_const_caseStep_sortOne`). This is the shared principle in action: the
type-uniqueness bit comes from the closer's own IH at an issued query.

**Verdict.** The residual content (`cl_common_sort`) is a two-derivation
lockstep fact about independent typings — not one issued query, and not a
global lemma (the T-layer analogue is circular per `RcicA2SortSupport`).
Row 14 stays OPEN at it; no on-cone refutation exists (standing:
`cl_hbit_sr3_hom` + the eqN-discipline measurement in `RcicSynSREqnClW`).
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open Rcic.Declarative.Ann (eqN_one_max)
open DispForPathPins (one two)

/-! ## §1 the defeq-coinciding fragment: the const cell issues `bitCoh` -/

/-- Inhabitant of the fragment's member shape: an arity-0 axiom member whose
    type is the param-free sort `.sort one` — every instantiation of it is
    itself (`instantiateLevels ls (.sort one) ≡ .sort one` for any `ls`). -/
def sr4SortMem : CheckedMember :=
  { mclass := .axiomM, arity := 0, mtype := .sort one, body := none }

theorem sr4SortMem_mtype : sr4SortMem.mtype = .sort one := rfl

/-- The row-14 const/const cell at a member type that coincides at both
    instantiations up to defeq (`m.mtype = .sort one`, param-free): CLOSED
    from the closer's own IH, no port, no global lemma, `ls₁ = ls₂` NOT
    assumed. Both instantiated subjects reduce to `.sort one`, so `hT₁ hT₂`
    are two sort-typings of ONE subject and the `occ_bitCoh` edge fires at
    `(0,[0])×(1,[0])` with strict weight drop — the ident branch's mechanism
    (`cl_const_const_caseStep_of_port`), now at `ls₁ ≠ ls₂` too. This is the
    shared principle: the eqN-bit comes from an issued query kind. -/
theorem cl_const_caseStep_sortOne (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {r : Nat}
    {ls ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hm : m.mtype = .sort one)
    (hres₁ : E.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hres₂ : E.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.cl (TyP.const E n Γ r ls ls₁ m u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S σ ρ) := by
  obtain ⟨_mcl, _ma, mm, _mb⟩ := m
  subst hm
  intro hq ih
  have hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂) :=
    ih_local Aw tbl hq ih (.bitCoh hT₁ hT₂ S σ ρ)
      (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := [0]) rfl rfl
        hq.ap.1 hq.ap.2) rfl
      (lexDM_combMeas_mono Aw _
        (lexDM_wt_lt_pair Aw hT₁ hT₂ _ _ rfl rfl
          (by simp only [TyP.wt]; omega) (by simp only [TyP.wt]; omega)))
  exact cl_const_nodes tbl σ ρ hres₁ hlen₁ hwf₁ hls₁ hT₁
    hres₂ hlen₂ hwf₂ hls₂ hT₂ hbit

/-! ## §2 the rank obstruction: a constructed `cts` bridge is not `Before` -/

/-- Every element of the smaller side of a `DMStep` has an owner at or above
    it in the larger side (shared `Z` elements own themselves; replaced `Y`
    elements sit below a removed `X` element). -/
theorem dmStep_owner_le {M' M : List Nat} (h : DMStep M' M) :
    ∀ v ∈ M', ∃ w ∈ M, v ≤ w := by
  obtain ⟨X, Y, Z, -, hM, hM', hdom⟩ := h
  intro v hv
  have hv' : v ∈ Y ++ Z := hM'.subset hv
  rcases List.mem_append.mp hv' with hy | hz
  · obtain ⟨x, hx, hlt⟩ := hdom v hy
    exact ⟨x, hM.symm.subset (List.mem_append_left Z hx), Nat.le_of_lt hlt⟩
  · exact ⟨v, hM.symm.subset (List.mem_append_right X hz), Nat.le_refl v⟩

/-- The env carrying `sr3Mem` (the arity-1 param-headed sort member of the
    standing fixture): its const typings need a member receipt. -/
def sr4Env : ResolvedEnv := extendEnv emptyEnv 0 sr3Mem

theorem sr4Env_members : sr4Env.members 0 = some sr3Mem := rfl

/-- The minimal fixture's left sort-typing, at the member-carrying env:
    `sr3Mem.mtype` at `ls₁ := [1]` is `.sort 1 : .sort 2` (a `TyP.sort`
    leaf, weight 1). -/
def sr4hT₁ : TyP sr4Env 2 [] (instantiateLevels [one] sr3Mem.mtype) (.sort two) :=
  TyP.sort sr4Env 2 [] one two (eqN_refl _)

/-- The right sort-typing: `.sort (max 1 1) : .sort (succ (max 1 1))`. -/
def sr4hT₂ : TyP sr4Env 2 [] (instantiateLevels [.max one one] sr3Mem.mtype)
    (.sort (.succ (.max one one))) :=
  TyP.sort sr4Env 2 [] (.max one one) (.succ (.max one one)) (eqN_refl _)

/-- The constructible bridge: the `sorts` conversion between the two
    instantiated member levels (`eqN 1 (max 1 1)`), dl/dr the two canonical
    `TyP.sort` leaves. Weight 3 at `Aw := fun _ => 0`; its atom is NEW
    material — not under any atom of the const pair. -/
def sr4SortsConv :
    CvP sr4Env 2 [] (.sort one) (.sort (.max one one)) (.sort two) :=
  CvP.sorts sr4Env 2 [] one (.max one one) eqN_one_max
    (TyP.sort sr4Env 2 [] one two (eqN_refl _))
    (TyP.sort sr4Env 2 [] (.max one one) two (eqN_symm eqN_succ_max_one_one))

/-- The minimal const pair: `TyP.const` nodes over the fixture's typings,
    raw list `[1]`, refined `[1]` / `[max 1 1]`, `Aw := fun _ => 0` weights
    `2` and `2`. -/
def sr4D₁ : TyP sr4Env 2 [] (.const 0 [one]) (instantiateLevels [one] sr3Mem.mtype) :=
  TyP.const sr4Env 2 [] 0 [one] [one] sr3Mem two sr4Env_members rfl rfl
    (eqNList_refl _) sr4hT₁

def sr4D₂ :
    TyP sr4Env 2 [] (.const 0 [one]) (instantiateLevels [.max one one] sr3Mem.mtype) :=
  TyP.const sr4Env 2 [] 0 [one] [.max one one] sr3Mem (.succ (.max one one))
    sr4Env_members rfl rfl sr3_eqNList sr4hT₂

/-- **The rank pin.** Presenting the constructed `sorts` bridge as a `.cts`
    query (conversion + the cell's own left typing, `cvTyMeas`) against the
    const pair (`tyPairMeas`) is NOT a rank decrease: the conversion's new
    atom `3` has no owner at or above it in `[2, 2]`, and the total weights
    are equal. So `LexDM` fails and (same frame, `before_of_same_prefix`)
    the presentation is not `Before` the cell's query — the `cts` route has
    no IH edge here. The `pin_bridge_endpoint_rejected` domination shape. -/
theorem cl_cts_sorts_not_before_minimal :
    ¬ LexDM (cvTyMeas (fun _ : Nat => 0) sr4SortsConv sr4hT₁)
            (tyPairMeas (fun _ : Nat => 0) sr4D₁ sr4D₂) := by
  have hC : cvTyMeas (fun _ : Nat => 0) sr4SortsConv sr4hT₁ = ([3, 1], 4) := rfl
  have hL : tyPairMeas (fun _ : Nat => 0) sr4D₁ sr4D₂ = ([2, 2], 4) := rfl
  rw [hC, hL]
  intro h
  cases h with
  | left _ _ hdm =>
      obtain ⟨w, hw, hle⟩ := dmStep_owner_le hdm 3 (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega

#print axioms sr4SortMem
#print axioms sr4SortMem_mtype
#print axioms cl_const_caseStep_sortOne
#print axioms dmStep_owner_le
#print axioms sr4Env
#print axioms sr4Env_members
#print axioms sr4hT₁
#print axioms sr4hT₂
#print axioms sr4SortsConv
#print axioms sr4D₁
#print axioms sr4D₂
#print axioms cl_cts_sorts_not_before_minimal

end Rcic.Syn
