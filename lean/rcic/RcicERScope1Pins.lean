import rcic.RcicERScope1
import rcic.RcicSynLetInline
import rcic.RcicSynSpineComb

/-!
# S15 — the out-of-range-`wk` positive control (S15_OUT_OF_RANGE_WK_PIN; #7369)

`wkOut` inserts `.assumption S0` at cutoff `2` into the *empty* context `[]`.
This is legal `AssumpPref` input: `AssumptionPrefix [] 2` holds vacuously
(`[].take 2 = []`), and `AssumptionPrefix` never carries `c ≤ Γ.length` — the
`wk` node's premise is public, not `AssumpCut`. It is exactly the arm where
`DisplayFits` and `DispShape` differ: the target display `[.keep]` *fits*
`[]` structurally (`DisplayFits [] [.keep]` via `nil`) while the strict
`DispShape [] [.keep]` fails. The erasure before and after repair is equal:
`wkSource` at `removeAt ρ 2 = [.keep]`, `wkOut` at `ρ` (whose `ρ[2]? = none`
branch leaves `inner` alone), and `wkDirect` at `ρ` all give `.sort .zero`.

Kernel-pinned exact values — if any differ, the fixture is wrong; do not
adjust the fixture, report the difference.
-/

namespace Rcic.Syn.S15Pins
open Rcic.Declarative

/-! ## §1 the fixture, verbatim from S15 §1 -/

abbrev S0 : Expr Nat := .sort .zero
abbrev S1 : Expr Nat := .sort (.succ .zero)

def wkSource : TyP emptyEnv 0 [] S0 S1 :=
  .sort _ _ _ _ _ (eqN_refl _)

def wkOut : TyP emptyEnv 0 [.assumption S0] S0 S1 :=
  .wk emptyEnv 0 [] S0 S1 (.assumption S0) 2 wkSource

def wkDirect : TyP emptyEnv 0 [.assumption S0] S0 S1 :=
  .sort _ _ _ _ _ (eqN_refl _)

/-! ## §2 context arithmetic — the out-of-range insert lands at the end -/

theorem insertAt_oob : insertAt (.assumption S0) 2 [] = [.assumption S0] := rfl

theorem lift_oob_S0 : lift 2 1 S0 = S0 := rfl

theorem lift_oob_S1 : lift 2 1 S1 = S1 := rfl

def target_ctxWf : CtxWfT emptyEnv 0 [.assumption S0] :=
  .assumption [] S0 (.succ .zero) .nil (.sort [] .zero)

/-! ## §3 the legality controls -/

/-- Public premise: `AssumptionPrefix` at an out-of-range cutoff is vacuous
    (`[].take 2 = []`). This is what `wk`'s `AssumpPref` field actually asks. -/
theorem apEmpty_two : AssumptionPrefix [] 2 := by
  intro d hd
  simp at hd

/-- The *private* `AssumpCut` gate is false at `2` — the fixture deliberately
    does not satisfy it, and `AssumptionPrefix` is never replaced by it. -/
theorem not_assumpCut_empty_two : ¬ AssumpCut [] 2 := fun h => by cases h

theorem wkSource_ap : wkSource.AssumpPref := trivial

theorem wkOut_ap : wkOut.AssumpPref := ⟨apEmpty_two, trivial⟩

/-! ## §4 display arithmetic on `ρ = [.keep]` -/

/-- The target display carried by `wkOut`'s single inserted `.keep`. -/
abbrev ρ₀ : List Disp := [.keep]

theorem rho_lookup_oob : ρ₀[2]? = none := rfl

theorem rho_removeAt : removeAt ρ₀ 2 = [.keep] := rfl

theorem rho_countKeep : countKeep (ρ₀.take 2) = 1 := rfl

/-! ## §5 erasure equality — output identical before/after repair -/

theorem eps_source : wkSource.eps id (removeAt ρ₀ 2) = .sort .zero := rfl

theorem eps_out : wkOut.eps id ρ₀ = .sort .zero := rfl

theorem eps_direct : wkDirect.eps id ρ₀ = .sort .zero := rfl

theorem eps_out_eq_source : wkOut.eps id ρ₀ = wkSource.eps id (removeAt ρ₀ 2) := rfl

theorem eps_out_eq_direct : wkOut.eps id ρ₀ = wkDirect.eps id ρ₀ := rfl

/-! ## §6 atoms and weight — the wrapper costs `+1` and nothing else (arbitrary `Aw`) -/

theorem atoms_source (Aw : Nat → Nat) : wkSource.atoms Aw = [1] := rfl

theorem atoms_out (Aw : Nat → Nat) : wkOut.atoms Aw = [1] := rfl

theorem wt_source (Aw : Nat → Nat) : wkSource.wt Aw = 1 := rfl

theorem wt_out (Aw : Nat → Nat) : wkOut.wt Aw = 2 := rfl

/-! ## §7 the SCOPE-1 distinction pinned -/

/-- `DisplayFits` accepts the fit the strict shape rejects. -/
theorem fits_nil_keep : DisplayFits [] ρ₀ := .nil _

theorem not_dispShape_nil_keep : ¬ DispShape [] ρ₀ := fun h => by cases h

/-- `DisplayFits` also accepts the *target* side the way `wk` actually sees it:
    `insertAt (.assumption S0) 2 []` against `ρ₀` is a real `DisplayFits`. -/
theorem fits_target : DisplayFits (insertAt (.assumption S0) 2 []) ρ₀ :=
  .assumptionKeep (.nil _)

/-- The `wk` support step instantiated on the pin: the source context `[]`
    fits `removeAt ρ₀ 2 = ρ₀`. -/
theorem fits_wk_pin : DisplayFits [] (removeAt ρ₀ 2) :=
  displayFits_wk fits_target

end Rcic.Syn.S15Pins

#print axioms Rcic.Syn.S15Pins.eps_out_eq_source
