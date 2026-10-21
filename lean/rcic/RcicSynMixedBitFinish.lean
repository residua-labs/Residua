import rcic.RcicSynZetaMeasureRefute
import rcic.RcicSynBelow
import rcic.RcicSynCR

/-!
# Syntactic sortRow, S17 A6 — `mixedBit_finish` and the transported / historical re-read controls

`research/rcic/sortrow/S17_MIXED_BIT_STEP.md` §3, §5 and
`research/rcic/sortrow/S17_HISTORICAL_REREAD.md` (PR #7389). Pure
additive pins over main's existing machinery — no new measure, no new
derivation form, `closure_claim = 0`.

## §3 — the MixedBit finish

`mixedBit_finish` consumes the two completed regularity normalizations
`hI : τI ↔* sort ℓI`, `hH : τH ↔* sort ℓH` and the current pair's real
MixedEUT result `hE : τI ↔* τH`, and concludes
`levelIsZero ℓI = levelIsZero ℓH` by main's erased-sort separation
`eqN_of_convE_sort_wf` — never the native `SortUnique`. **`hE` is a
hypothesis: it is computed inside the current MixedEUT case and is never
produced here, and never asked back from the current MixedBit.**

## §5 — the transported positive control

On main's `pbitWallHeavySort emptyEnv 0` (a `.conv` typing
`sort 0 : sort 1`, atoms `[6]`, weight `6`, real children the base sort
typing `1` and the original `refl` conversion `4`):

- `s17H` = `wkAtZero` of the direct `sort 0 : sort 1` into
  `pbitCtx = [.assumption (sort 0)]` — atoms `[1]`, weight `2`;
- `s17D` = the original `bvar 0` request carrying `s17H` — atoms `[3]`;
- `s17DT` = the direct `sort 0 : sort 1` (`pbitSort`) — atoms `[1]`.

`transported_focus_input` pins the kernel atoms; `provider_move_exact`
pins the moved edge `[6,3,1] → [6,1]` (the original bvar request enters
the query — it says nothing about the query's answer);
`mixed_left_conv_live_atoms` pins the legal live split `[1,4,1]` after
expanding the left `.conv`; `mixed_regularities_exact` pins both
regularity erasures to `.sort 1`; `mixedBit_transport_control` runs
`mixedBit_finish` on the fixture's real computed values.
**Never rewritten as the old homogeneous `[6,6,1]` query.**

## Re-read controls

`historical_path_still_valid` — the historical path still resolves the
original `I` to its real `.conv` children (provenance, not a live
input); `historical_reread_atoms` — re-reading the historical `I` yields
weight `6`; `not_historical_reread_edge` — no `DMStep [1,4,1] → [6,1]`
(the consumed 6 cannot be paid back: the new `6` is not kept, and no
larger deleted atom pays for it); `accepted_pathA_step` /
`accepted_pathA_cl` — the legal `[1,4,1] → [1,1,1,1]` descent for
`CL c.dr s12`, two real weight-1 typings counted as two `1`s, never
de-duplicated even though definitionally equal here.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `mixedBit_finish` (S17_MIXED_BIT_STEP §3) -/

/-- The finite MixedBit composition: both ends' completed regularity
    normalizations plus the current pair's MixedEUT result. `hE` is only
    a hypothesis — it is never produced here. -/
theorem mixedBit_finish {tbl : List CRule} (hW : TableWF tbl) {τI τH : ETm} {ℓI ℓH : Level}
    (hI : ConvMod (EStep tbl) LvlEq τI (.sort ℓI))
    (hE : ConvMod (EStep tbl) LvlEq τI τH)
    (hH : ConvMod (EStep tbl) LvlEq τH (.sort ℓH)) :
    levelIsZero ℓI = levelIsZero ℓH :=
  levelIsZero_congr
    (eqN_of_convE_sort_wf hW ((ConvMod.symm' LvlEq.symm' hI).trans (hE.trans hH)))

/-! ## §2 The transported fixture (S17 §5) -/

/-- `I`: main's heavy provider — a `.conv` typing `sort 0 : sort 1`
    (weight `6`, atoms `[6]`). -/
def s17I : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  pbitWallHeavySort emptyEnv 0

/-- `H`: the original hA the current bvar carries — `wkAtZero` of the
    direct `sort 0 : sort 1` into `pbitCtx` (atoms `[1]`, weight `2`). -/
def s17H : TyP emptyEnv 0 pbitCtx (.sort .zero) (.sort (.succ .zero)) :=
  wkAtZero (A := .sort .zero) (TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _))

/-- `D`: the original bvar request — `bvar 0` in `pbitCtx`, whose entry
    typing is `s17H` (atoms `[3]`). -/
def s17D : TyP emptyEnv 0 pbitCtx (.bvar 0) (.sort .zero) :=
  TyP.bvar emptyEnv 0 pbitCtx 0 (.sort .zero) (.succ .zero) pbit_lookup s17H

/-- `DT`: the direct `sort 0 : sort 1` in `pbitCtx` (atoms `[1]`). -/
def s17DT : TyP emptyEnv 0 pbitCtx (.sort .zero) (.sort (.succ .zero)) :=
  pbitSort emptyEnv 0

/-- Kernel atoms of the transported input: `I ↦ [6]`, `D ↦ [3]`,
    `DT ↦ [1]`, and `H ↦ [1]` at weight `2`. -/
theorem transported_focus_input (Aw : Nat → Nat) :
    s17I.atoms Aw = [6] ∧ s17D.atoms Aw = [3] ∧ s17DT.atoms Aw = [1] ∧
      s17H.atoms Aw = [1] ∧ s17H.wt Aw = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The provider move: the original bvar request `D` (atom `3`) retires
    out of the caller `[6,3,1]`, leaving the moved qAlign `[6,1]`. The
    edge proves only that the request may enter this `q` — it says
    nothing about `q`'s answer. -/
theorem provider_move_exact : DMStep [6, 1] [6, 3, 1] :=
  ⟨[3], [], [6, 1], by decide, List.Perm.swap 3 6 [1], List.Perm.refl _,
    fun y hy => absurd hy (List.not_mem_nil y)⟩

/-- Children atoms of a `.conv` node (its typing child ++ its conversion
    child); `[]` at any other root. -/
def TyP.convChildrenAtoms (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} : TyP E n Γ e T → List Nat
  | .conv _ _ _ _ _ _ _ h hc => h.atoms Aw ++ hc.atoms Aw
  | _ => []

/-- Expanding the left `.conv` gives the legal live split
    `[base, c, H] = [1, 4, 1]` — never the homogeneous `[6,6,1]`. -/
theorem mixed_left_conv_live_atoms (Aw : Nat → Nat) :
    s17I.convChildrenAtoms Aw ++ s17H.atoms Aw = [1, 4, 1] := rfl

/-- Both regularity erasures compute to the real `sort 1` erasure
    `.sort (.succ .zero)`, and both regularity levels are the real
    `sort 2` level `.succ (.succ .zero)`. -/
theorem mixed_regularities_exact :
    s17I.reg.1 = .succ (.succ .zero) ∧ s17H.reg.1 = .succ (.succ .zero) ∧
      (s17I.reg.2).eps id [] = .sort (.succ .zero) ∧
        (s17H.reg.2).eps id [] = .sort (.succ .zero) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `mixedBit_finish` run on the fixture's own computed values: the
    transported regularity erasures are definitionally `.sort 1`, so the
    two normalizations and the MixedEUT leg are all reflexive modulo
    `LvlEq`. -/
theorem mixedBit_transport_control {tbl : List CRule} (hW : TableWF tbl) :
    levelIsZero (.succ .zero) = levelIsZero (.succ .zero) :=
  mixedBit_finish hW
    (τI := (s17I.reg.2).eps id []) (τH := (s17H.reg.2).eps id [])
    (.refl _) (.refl _) (.refl _)

/-! ## §3 The historical re-read controls (S17_HISTORICAL_REREAD §1–3) -/

/-- The historical path still resolves the original `I` to its real
    `.conv` children — provenance for identity and audit, not a live
    input slot. -/
theorem historical_path_still_valid :
    ∃ (h : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)))
      (hc : CvP emptyEnv 0 [] (.sort (.succ .zero)) (.sort (.succ .zero))
        (.sort (.succ (.succ .zero)))),
      s17I = TyP.conv emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) (.sort (.succ .zero))
        (.succ (.succ .zero)) h hc :=
  ⟨_, _, rfl⟩

/-- Re-reading the historical `I` yields its original weight-`6` atom —
    a legal old object seen through a stale path. -/
theorem historical_reread_atoms (Aw : Nat → Nat) : s17I.atoms Aw = [6] := rfl

/-- The rejected path: rebuilding `MixedEUT I H` from the historical `I`
    asks for the callee `[6,1]` out of the live `[1,4,1]` — no DMStep.
    The new `6` is not kept (it is not in `[1,4,1]`, so it cannot hide
    in `Z`), and no element of `[1,4,1]` bounds it, so it cannot be paid
    for by a deleted `X`. -/
theorem not_historical_reread_edge : ¬ DMStep [6, 1] [1, 4, 1] := by
  rintro ⟨X, Y, Z, hX, hM, hM', hdom⟩
  have h6 : 6 ∈ Y ++ Z := (hM'.mem_iff).mp (by simp)
  rcases List.mem_append.mp h6 with h6Y | h6Z
  · rcases hdom 6 h6Y with ⟨x, hxX, hlt⟩
    have hx : x ∈ [1, 4, 1] := (hM.mem_iff).mpr (List.mem_append.mpr (.inl hxX))
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · have h6141 : 6 ∈ [1, 4, 1] := (hM.mem_iff).mpr (List.mem_append.mpr (.inr h6Z))
    simp at h6141

/-- The conversion child `c` inside `s17I` — the original `CvP.refl`
    whose endpoints are `sort 1 : sort 2` (weight `4`, atoms `[4]`). -/
abbrev s17c : CvP emptyEnv 0 [] (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  CvP.refl emptyEnv 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
    (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- The separately built canonical `s12 : sort 1 : sort 2` — a second,
    distinct weight-`1` typing for the same query. -/
def s17s12 : TyP emptyEnv 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- Accepted path A: `CL c.dr s12` deletes the original `4` and adds two
    real weight-`1` typings — `[1,4,1] → [1,1,1,1]`, strict descent. The
    two `1`s are `c.dr` and `s12`, counted separately even though they
    are definitionally equal in this fixture. -/
theorem accepted_pathA_step : DMStep [1, 1, 1, 1] [1, 4, 1] :=
  ⟨[4], [1, 1], [1, 1], by decide, List.Perm.swap 4 1 [1], List.Perm.refl _,
    fun y hy => ⟨4, .head _, by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
      omega⟩⟩

/-- The path-A request itself: `CL c.dr s12` holds by reflexivity — both
    are `sort 1 : sort 2` typings with erasure `.sort 1`. Also pins that
    `c.dr` and `s12` each carry one real weight-`1` atom. -/
theorem accepted_pathA_cl (Aw : Nat → Nat) (tbl : List CRule) :
    CL tbl id [] s17c.dr s17s12 ∧ s17c.dr.atoms Aw = [1] ∧ s17s12.atoms Aw = [1] :=
  ⟨.refl _, rfl, rfl⟩

end Rcic.Syn

#print axioms Rcic.Syn.mixedBit_finish
#print axioms Rcic.Syn.transported_focus_input
#print axioms Rcic.Syn.provider_move_exact
#print axioms Rcic.Syn.mixed_left_conv_live_atoms
#print axioms Rcic.Syn.mixed_regularities_exact
#print axioms Rcic.Syn.mixedBit_transport_control
#print axioms Rcic.Syn.historical_path_still_valid
#print axioms Rcic.Syn.historical_reread_atoms
#print axioms Rcic.Syn.not_historical_reread_edge
#print axioms Rcic.Syn.accepted_pathA_step
#print axioms Rcic.Syn.accepted_pathA_cl
