import rcic.RcicSynTableOfIFull
import rcic.RcicSynStepPortsClEut
import rcic.RcicSynDispForPathPins

/-!
# RcicSynSRClEutClCase — sortRow row 14 (`cl_case`) at `tableOfI hW`

Deliverable (lane glm-sr3): the row is REFUTED at its raw `constCl` supply —
a kernel-checked refutation of the missing lemma `clConstP_tableOfI` (the
`es_cl_field` `constCl` premise at `tbl := tableOfI hW`), with every input of
the refuted instance a closed inhabited term, plus the exact restated wall
`cl_case_wall` as ONE named Prop.

## Why the raw supply is false

`ClConstPorts`'s `hbit` field owes `levelIsZero (σ u₁) = levelIsZero (σ u₂)`
whenever `ls₁ ≠ ls₂`, for the ARBITRARY `σ` the raw premise quantifies (the
demand side never restricts it: `P2Query.Hom` is `Level → Level` with no
homomorphism content). A member `sr3Mem` with `mtype := .sort (.param 0)`
instantiated at `ls₁ := [1]` vs `ls₂ := [max 1 1]` gives sort-typings at
`u₁ := 2` and `u₂ := succ (max 1 1)` — equal under every valuation, but
syntactically distinct, so the closed match-based `sr3σ` maps one to `0`
(bit `true`) and the other to `1` (bit `false`). `hbit`'s consequent is
`true = false` at `tableOfI hW` — no `TableWF` input needed at all. The raw
`constCl` premise is uninhabited at `tableOfI hW`: `es_cl_field` cannot be
supplied there, so row 14's `ClField` cannot come from this closer.

## The restated wall

`cl_case_wall` restricts `constCl` to the `.cl` const/const cell's own data
(member receipts + `levelsBounded` + `eqNList` gates — the shape
`cl_const_const_caseStep_closed` consumes); it is inhabited at identical
instances (`cl_case_wall_ident_sat`). It is RETAINED, not claimed: note that
the same distinguishing-σ concern runs through `eqNList`-equal-but-distinct
level lists, so the wall's truth is an open measurement (both directions
recorded in the census doc), not a settled fact. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins (one two)

variable {E : ResolvedEnv}

/-- The distinguishing level map: `2 ↦ 0`, everything else `1` (closed,
    no homomorphism content — the point of the refutation). -/
def sr3σ : Level → Level :=
  fun l => match l with
    | .succ (.succ .zero) => .zero
    | _ => .succ .zero

/-- The arity-1 param-headed member fixture (any `CheckedMember` value is a
    legal input to the raw port — no env-membership receipt there). -/
def sr3Mem : CheckedMember :=
  { mclass := .axiomM, arity := 1, mtype := .sort (.param 0), body := none }

/-- `sr3Mem.mtype` at `ls₁ := [1]` erases to `.sort 1`, typed at `u₁ := 2`
    (closed TyP term). -/
def sr3hT₁ : TyP emptyEnv 0 [] (instantiateLevels [one] sr3Mem.mtype)
    (.sort two) :=
  TyP.sort emptyEnv 0 [] one two (eqN_refl _)

/-- `sr3Mem.mtype` at `ls₂ := [max 1 1]` erases to `.sort (max 1 1)`, typed
    at `u₂ := succ (max 1 1)` (closed TyP term). -/
def sr3hT₂ : TyP emptyEnv 0 [] (instantiateLevels [.max one one] sr3Mem.mtype)
    (.sort (.succ (.max one one))) :=
  TyP.sort emptyEnv 0 [] (.max one one) (.succ (.max one one)) (eqN_refl _)

theorem sr3hne : [one] ≠ [.max one one] :=
  fun h => List.noConfusion h (fun he _ => Level.noConfusion he)

/-- The refuted instance: `sr3hT₁`/`sr3hT₂`/`sr3σ`/`[]` closed — every input
    inhabited; `hbit`'s consequent is definitionally `true = false`. -/
theorem clConstPorts_tableOfI_empty_refuted (hW : EnvWfT emptyEnv) :
    ¬ ClConstPorts (tableOfI hW) sr3σ [] sr3hT₁ sr3hT₂ := by
  intro ports
  have h : (true : Bool) = false := ports.hbit sr3hne
  exact Bool.noConfusion h

/-- The row-14 missing lemma, exact: the `es_cl_field` `constCl` premise
    shape at `tbl := tableOfI hW`. -/
def clConstP_tableOfI (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {ls₁ ls₂ : List Level}
    {m : CheckedMember} {u₁ u₂ : Level}
    (hT₁ : TyP E' n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hT₂ : TyP E' n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    {σ : Level → Level} {ρ : List Disp},
    ClConstPorts (tableOfI hW) σ ρ hT₁ hT₂

/-- **Row 14 verdict: the missing lemma `clConstP_tableOfI` is FALSE** (at
    the inhabited `emptyEnv` witness; all inputs closed terms). -/
theorem clConstP_tableOfI_empty_refuted : ¬ clConstP_tableOfI EnvWfT.empty :=
  fun h => clConstPorts_tableOfI_empty_refuted EnvWfT.empty (h sr3hT₁ sr3hT₂)

/-- Row 14's exact restated wall, ONE Prop: `constCl` restricted to the
    `.cl` const/const cell's own data — member receipts, `levelsBounded`,
    and the `eqNList` gates the closer `cl_const_const_caseStep_of_port`
    binds. Retained (not claimed, not refuted); inhabited at identical
    instances (`cl_case_wall_ident_sat`). -/
def cl_case_wall (hW : EnvWfT E) : Prop :=
  ∀ {E' : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hres₁ : E'.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E' n Γ (instantiateLevels ls₁ m.mtype) (.sort u₁))
    (hres₂ : E'.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E' n Γ (instantiateLevels ls₂ m.mtype) (.sort u₂))
    {σ : Level → Level} {ρ : List Disp},
    ClConstPorts (tableOfI hW) σ ρ hT₁ hT₂

/-- The restated wall is not vacuously false: at an identical cell instance
    (`ls₁ = ls₂`) `hbit`'s antecedent is false, so the ports record is
    inhabited. -/
theorem cl_case_wall_ident_sat (hW : EnvWfT E) :
    ClConstPorts (tableOfI hW) sr3σ [] sr3hT₁ sr3hT₁ :=
  ⟨fun h => (h rfl).elim⟩

#print axioms clConstPorts_tableOfI_empty_refuted
#print axioms clConstP_tableOfI_empty_refuted
#print axioms cl_case_wall_ident_sat

end Rcic.Syn
