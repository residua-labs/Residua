/-
RcicLinstBitFlip — S13 (W-ERASURE-LSUB-INLINE-SCOPE audit,
`research/rcic/sortrow/S13_ERASURE_TRANSPORT_AUDIT.md`) §5 ruling 5:
"linst flipping `levelIsZero`: the right contract must allow the flip."
Credit: ChatGPT S13.

Fixture (universe arity 1, empty environment):

  Γu = [p : P, P : sort (param 0)]     newest-first
  D  : TyP emptyEnv 1 Γu (.bvar 0) (.bvar 1)   — the direct bvar typing of p
  σ = id, ρu = [keep, keep]            ⇒  D.eps id ρu = bvar 0
  L  = TyP.linst [zero] D
     : TyP emptyEnv 0 Γ0 (.bvar 0) (.bvar 1),
       Γ0 = [p : P, P : sort 0], ρ0 = [drop, keep]
       ⇒  L.eps id ρ0 = star

The pin seals the three kernel-computed erasures (reported, never assumed), the
RIGHT contract `ε(linst D) id ρ0 = ε D (instLevel [zero]) ρ0` — the landed
`eps_linst` at σ = id, where every gate is re-read under the composite map —
and the refusal of the WRONG contract `ε(linst D) = ETm.instLevels (ε D)`:
the left side is `star`, the right side stays `bvar 0` (the erased bvar carries
no level to map); rigid heads differ, and `LvlEq` cannot bridge them either.
No `TyP.eps` clause and no existing statement is touched.
-/

import rcic.RcicSynErase
import rcic.RcicConvPlus
import rcic.RcicSynLevel
import rcic.RcicLevelZero
import rcic.RcicTypedLevels

namespace Rcic.Syn

open Rcic.Declarative

/-! ## fixture -/

/-- `Γu = [p : P, P : sort (param 0)]` at universe arity 1, newest-first.
    p's stored type is `bvar 0` (P in the remaining context); `lookupType`
    lifts it to `bvar 1` at the use site. -/
def linstFlipΓu : LCtx := [.assumption (.bvar 0), .assumption (.sort (.param 0))]

/-- `Γ0 = [p : P, P : sort 0]` — the instantiated context. -/
def linstFlipΓ0 : LCtx := [.assumption (.bvar 0), .assumption (.sort .zero)]

/-- `ρu`: both binders relevant while P's sort is the parametric `(param 0)`. -/
def linstFlipρu : List Disp := [.keep, .keep]

/-- `ρ0`: after `[zero]`-instantiation P is a Prop (`sort 0`), so p is a
    proof slot (`drop`); P's own binder stays `keep`. -/
def linstFlipρ0 : List Disp := [.drop, .keep]

/-- `P`'s sort typing: `sort (param 0) : sort (succ (param 0))`, `eqN` slack
    taken reflexively. -/
def linstFlipPSort :
    TyP emptyEnv 1 linstFlipΓu (.sort (.param 0)) (.sort (.succ (.param 0))) :=
  TyP.sort emptyEnv 1 linstFlipΓu (.param 0) (.succ (.param 0)) (fun _ => rfl)

/-- `P` (source `bvar 1`) typed at `sort (param 0)`:
    `lookupType Γu 1 = lift 0 2 (sort (param 0)) = sort (param 0)`. -/
def linstFlipPTy : TyP emptyEnv 1 linstFlipΓu (.bvar 1) (.sort (.param 0)) :=
  TyP.bvar emptyEnv 1 linstFlipΓu 1 (.sort (.param 0)) (.succ (.param 0)) rfl
    linstFlipPSort

/-- `D` — the direct bvar typing of `p`: `bvar 0 : bvar 1` in `Γu`
    (`lookupType Γu 0 = lift 0 1 (bvar 0) = bvar 1`). -/
def linstFlipD : TyP emptyEnv 1 linstFlipΓu (.bvar 0) (.bvar 1) :=
  TyP.bvar emptyEnv 1 linstFlipΓu 0 (.bvar 1) (.param 0) rfl linstFlipPTy

/-- `L := linst [zero] D`: `TyP emptyEnv 0 Γ0 (.bvar 0) (.bvar 1)` — the
    result context `instLvlsCtx [.zero] Γu` is the definitionally `Γ0`. -/
def linstFlipL : TyP emptyEnv 0 linstFlipΓ0 (.bvar 0) (.bvar 1) :=
  TyP.linst emptyEnv 1 0 linstFlipΓu (.bvar 0) (.bvar 1) [.zero] rfl rfl
    linstFlipD

/-! ## kernel values (reported) -/

/-- The instantiated context is literally `Γ0`. -/
theorem linst_bitflip_instCtx :
    instLvlsCtx [.zero] linstFlipΓu = linstFlipΓ0 := rfl

/-- Source ε: `D.eps id ρu = bvar 0`. Under `σ = id` the bit is
    `levelIsZero (param 0) = false`, so `bvar 0` resolves through
    `[keep, keep]` to `bvar 0`. -/
theorem linst_bitflip_src_eps : linstFlipD.eps id linstFlipρu = .bvar 0 :=
  eps_bvar_rel rfl

/-- Target ε: `L.eps id ρ0 = star`. The composite map sends the gate's
    `(param 0)` to `zero`, `levelIsZero zero = true`, and the bvar erases
    to `★` — this is the flip ruling 5 names. -/
theorem linst_bitflip_tgt_eps : linstFlipL.eps id linstFlipρ0 = .star := by
  unfold linstFlipL
  rw [eps_linst]
  exact eps_bvar_proof rfl

/-- The source derivation's ε recomputed under the composite map at `ρ0`:
    `D.eps (instLevel [zero]) ρ0 = star` — the same `★`. -/
theorem linst_bitflip_src_eps_recomputed :
    linstFlipD.eps (instLevel [.zero]) linstFlipρ0 = .star :=
  eps_bvar_proof rfl

/-! ## the two contracts -/

/-- RIGHT contract (§5.5): `ε(linst D) id ρ0 = ε D (instLevel [zero]) ρ0`.
    The landed `eps_linst` at `σ = id`; it requires no bit invariance and no
    new eps branch. -/
theorem linst_bitflip_right_contract :
    linstFlipL.eps id linstFlipρ0 =
      linstFlipD.eps (instLevel [.zero]) linstFlipρ0 := by
  unfold linstFlipL
  exact eps_linst id linstFlipρ0

/-- WRONG contract (§5.5) refused: `ε(linst D) id ρ0` is `star`, while
    mapping levels inside the already-erased `ε D id ρu` leaves `bvar 0`
    — the erased bvar carries no level. `star ≠ bvar 0`: rigid heads differ. -/
theorem linst_bitflip_wrong_contract_fails :
    linstFlipL.eps id linstFlipρ0 ≠
      ETm.instLevels [.zero] (linstFlipD.eps id linstFlipρu) := by
  rw [linst_bitflip_tgt_eps, linst_bitflip_src_eps]
  decide

/-- The two erased values are not even `LvlEq` — no `star`/`bvar` clause. -/
theorem linst_bitflip_star_not_lvlEq : ¬ LvlEq .star (.bvar 0) := by
  intro h; cases h

/-! ## kernel-value reports -/

#guard decide (linstFlipD.eps id linstFlipρu = .bvar 0)
#guard decide (linstFlipL.eps id linstFlipρ0 = .star)
#guard decide (linstFlipD.eps (instLevel [.zero]) linstFlipρ0 = .star)
#guard decide (ETm.instLevels [.zero] (linstFlipD.eps id linstFlipρu) = .bvar 0)
#guard decide (instLvlsCtx [.zero] linstFlipΓu = linstFlipΓ0)

end Rcic.Syn

#print axioms Rcic.Syn.linst_bitflip_instCtx
#print axioms Rcic.Syn.linst_bitflip_src_eps
#print axioms Rcic.Syn.linst_bitflip_tgt_eps
#print axioms Rcic.Syn.linst_bitflip_src_eps_recomputed
#print axioms Rcic.Syn.linst_bitflip_right_contract
#print axioms Rcic.Syn.linst_bitflip_wrong_contract_fails
#print axioms Rcic.Syn.linst_bitflip_star_not_lvlEq
