import rcic.RcicSynSRBetaZetaStarEntry

/-!
# `DeltaRhsStarWall` — the on-cone counterexample, and the exact
uniqueness instance it hides (glm-sr1, row 2; cc 12:50Z item 1)

Applying `~/.residua-lean/briefs/sortrow-uniq-as-ih.md` to
`DeltaRhsStarWall` (`RcicSynSRBetaZetaStarEntry`).

## The uniqueness instance, named

A δ-entry `.const r ls' → (deltaRule r D_b).rhs ls' []` needs the bit of
the `TyP.const` node's own sort to agree with the rhs `★`-read. `D_b`'s
rhs reads the member's admitted sort; the const node carries its own
regularity `hT`. The instance is `.eut`-shaped at subject
`instantiateLevels ls₀ m.mtype`:

* `hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)` — a field
  of the `TyP.const` node, hence a STRICT subderivation of the step
  node (below);
* `instMemberSortP`-side: `TyP E n Γ (instantiateLevels ls₀ m.mtype)
  (.sort (instLevel ls₀ u₀))`, `u₀` the member's `typeAdm` sort — built
  from the `EnvWfT` prefix (`memberSortP_of_envWfT`), NOT below the
  node (its `wt` is `admW`-bounded via `TypeAdm.lt`, not a
  subderivation).

Conclusion needed: `eqN u (instLevel ls₀ u₀)` — equivalently the
`.slot`-goal `levelIsZero (σ u) = levelIsZero (σ (instLevel ls₀ u₀))`
(`.slot`'s exact shape, but `slot_not_demanded` keeps its demand empty).
So per the brief this is the **EnvWfT-prefix branch**: one side is the
environment member's admitted typing; the member's admission WAS
checked — `instMemberSortP` is the landed prefix result — and the
missing link is `eut` between a below-derivation and a prefix-derived
one, not issuable as an IH query today.

## `DeltaRhsStarWall` is FALSE — the fixture

`srPropEnv`/`srPropDefEnv`: an axiom at the Prop type `∀ P : Prop, P`
(sort `.imax 1 0`, `levelIsZero = true`), then a definition whose body
is the axiom's const. `srPropDef_rhs_star`: the enriched body
derivation's eps is `★` at EVERY level — `rhs ls [] = ★` — while every
honest `TyP.const` image of member 1 is already `★` (its sort field is
the same admitted sort). `DeltaRhsStarWall`'s `rhs ≠ ★` is therefore
refuted on-cone: the wall demanded too much. `DeltaStarEntryWall`
survives only through the bit-agreement above; `DeltaSlotBitWall` names
the surviving residue.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the Prop-sort fixture env -/

/-- `∀ P : Prop, P` — a Prop at `.imax 1 0`. -/
def srPropTy : Expr Nat := .pi (.sort .zero) (.bvar 0)

/-- The Prop-typed axiom member (arity 0). -/
def srPropMember : CheckedMember := ⟨.axiomM, 0, srPropTy, none⟩

/-- One-member env: `q : ∀ P : Prop, P`. -/
def srPropEnv : ResolvedEnv := extendEnv emptyEnv 0 srPropMember

/-- The definition member whose body is `const q []`. -/
def srPropDefMember : CheckedMember := ⟨.definitionM, 0, srPropTy, some (.const 0 [])⟩

/-- Two-member env: the axiom, then `p := q`. -/
def srPropDefEnv : ResolvedEnv := extendEnv srPropEnv 1 srPropDefMember

/-- `srPropTy : .sort (.imax 1 0)` in any environment (no members used). -/
def srPropTy_ty (E : ResolvedEnv) :
    HasTyT E 0 [] srPropTy (.sort (.imax (.succ .zero) .zero)) :=
  HasTyT.pi [] (.sort .zero) (.succ .zero) (.bvar 0) .zero
    (HasTyT.sort [] .zero)
    (HasTyT.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl)

/-- The def body `const 0 []` typed at the axiom's `mtype`. -/
def srPropBodyTy : HasTyT srPropEnv 0 [] (.const 0 []) srPropTy :=
  HasTyT.const [] 0 [] srPropMember rfl rfl rfl

/-- `srPropEnv` well-formed. -/
def srPropEnvWf : EnvWfT srPropEnv :=
  EnvWfT.axiom emptyEnv 0 srPropTy (.imax (.succ .zero) .zero) .empty rfl
    (srPropTy_ty emptyEnv) (fun _ => rfl) rfl

/-- `srPropDefEnv` well-formed. -/
def srPropDefEnvWf : EnvWfT srPropDefEnv :=
  EnvWfT.definition srPropEnv 1 srPropTy (.const 0 [])
    (.imax (.succ .zero) .zero) srPropEnvWf rfl (srPropTy_ty srPropEnv)
    srPropBodyTy (fun _ => rfl) (fun _ => rfl) rfl rfl

/-! ## §2 the counterexample -/

/-- KEY COMPUTATION: the δ rule for a Prop-sorted definition erases its
    closed rhs to `★` — the enriched body is a `TyP.const` whose sort
    field is `q`'s admitted sort `.imax 1 0`, `levelIsZero`-true at every
    `instLevel`. -/
theorem srPropDef_rhs_star (ls : List Level) :
    (deltaRule 1 (defBodyAt srPropEnvWf srPropBodyTy)).rhs ls [] = .star := rfl

/-- `DeltaRhsStarWall` is refuted on-cone: a `tableOf` δ rule whose
    closed rhs IS `★` exists at `srPropDefEnvWf` (every `ls`; `[]` shown).
    The honest const images of member 1 are `★` anyway — the wall's
    `rhs ≠ ★` asked for more than `DeltaStarEntryWall` needs. -/
theorem deltaRhsStarWall_refuted : ¬ DeltaRhsStarWall srPropDefEnvWf := by
  intro h
  have hmem : deltaRule 1 (defBodyAt srPropEnvWf srPropBodyTy) ∈
      tableOf srPropDefEnvWf := by
    dsimp only [srPropDefEnvWf]
    rw [tableOf_definition]
    exact List.Mem.head _
  exact h _ hmem [] (srPropDef_rhs_star [])

/-! ## §3 the surviving residue, named -/

/-- The remaining wall for the δ-entry clause at `tableOf hEnv`: a fired
    `.const r ls'` whose rhs is `★` forces every eps-reachable const image
    of `r` at those levels to carry a `levelIsZero`-true sort field —
    `levelIsZero (σ u_c) = levelIsZero (instLevel (ls_c.map σ) u₀)` —
    `u_c` the `TyP.const` node's own regularity sort (below), `u₀` the
    member's `typeAdm` sort (`instMemberSortP`, EnvWfT-prefix). The link
    `eqN u_c (instLevel ls₀ u₀)` is the `.eut`/`.slot` instance named in
    the module doc. -/
def DeltaSlotBitWall {E : ResolvedEnv} (hEnv : EnvWfT E) : Prop :=
  ∀ (r : Nat) (m : CheckedMember) (ls₀ : List Level) (u : Level)
    (n : Nat) (Γ : LCtx)
    (hres : E.members r = some m) (_hlen : ls₀.length = m.arity),
    TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u) →
    eqN u (instLevel ls₀ (memberSortP_of_envWfT hEnv r m hres).1)

end Rcic.Syn

#print axioms Rcic.Syn.srPropDef_rhs_star
#print axioms Rcic.Syn.deltaRhsStarWall_refuted
#print axioms Rcic.Syn.DeltaSlotBitWall
