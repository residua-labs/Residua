import rcic.RcicSynStepFieldsDeltaIota
import rcic.RcicSynObsLevels

/-!
# sortRow row 18 (`delta_obs`) — the `deltaObsRoute_of_internal_pos` wall — `closure_claim = 0`

glm-sr4 lane (rows 16 `pb_case`, 18 `delta_obs`; `TABLEOFI_SUPPLIER_CENSUS.md` row 18).

The landed closer `delta_obs_caseStep_of_ports` reduces the
`StepSuppliers.delta_obs` field to one retained premise per position:
`DeltaObsPorts S hres hbody htr ls pos` — for every level the selected
admission's observer lists actually record at `pos`, a `DeltaObsRoute` (the
σ-independent S7 §3 producers: `bounded`, `eqNRep`, `succGate`, `uniformType`,
`uniformProp`). The census's missing lemma `deltaObsRoute_of_internal_pos` is
exactly that premise for the positions no producer row currently enumerates;
its exact restatement as ONE named Prop is `sr4DeltaObsWall` below (closer
telescope verbatim, `hlen` included, no bundled hypotheses).

The wall is RETAINED (not claimed, not refuted): the blanket
`levelBounded`-everywhere contract is already refuted in-tree
(`tooth_levelBounded_everywhere_refuted`, the `Dvstar` pin — a `.sorts` conv
smuggles `param 0` into an arity-0 body's λ-domain gate `u★`), so `bounded`
alone cannot enumerate, and the internal-position enumeration for an arbitrary
selected admission is the row's open content.

Kernel-side teeth here:

* `sr4DeltaObsPorts_dvstar` — the missing lemma VERIFIED at the tree's real
  admission-body pin `Dvstar` (`lam s₀ (bvar 0) : pi s₀ s₀` at `u★`): every
  position of its actual observer lists carries a route — `u★` is a successor,
  so `succGate` covers it at the gate position 0; the `bvar` gate `.succ zero`
  at position 1 likewise; the out side is empty. This is the internal-position
  discharge for the one concrete admission the tree computes.
* `sr4Route_imaxParam_out` — a param-smuggled NON-succ observation is still
  routable: `eqNRep .zero` (the `.imax` arm's second argument decides), so the
  wall's failure mode is neither the smuggled succs nor the smuggled imax-zeros.
* `sr4DeltaObsField_of_wall` — the closer link: the wall yields the exact
  `delta_obs` conclusion (consumer composition via the landed closer, not a
  supply).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## The wall, restated as ONE named Prop -/

/-- Row 18's exact retained wall: the closer's `DeltaObsPorts` premise for
    every position `pos`, over the landed closer's own binder telescope (the
    closer's `hlen : ls.length = m.arity` lives in its telescope, not in the
    ports' shape, and is therefore not repeated here). This is the census's
    missing lemma `deltaObsRoute_of_internal_pos` verbatim (one Prop, no tag
    decoration, nothing bundled). -/
def sr4DeltaObsWall : Prop :=
  ∀ {E : ResolvedEnv} {Eₐ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {ls : List Level}
    (S : ScopedCtx Eₐ E n₀ Γ₀),
    ∀ pos : ObsPos, DeltaObsPorts S hres hbody htr ls pos

/-! ## The teeth -/

/-- The missing lemma, VERIFIED at the tree's real admission-body pin: every
    position of `Dvstar`'s actual observer lists carries a route. The out side
    is empty (`outLevels_Dvstar`); the gates are exactly `u★` (position 0) and
    `.succ .zero` (position 1), both successors, both covered by `succGate`. -/
theorem sr4DeltaObsPorts_dvstar (ls : List Level) :
    ∀ (k : Nat) (l : Level), (Dvstar.gateLevels id)[k]? = some l →
      Nonempty (DeltaObsRoute ls (.gate k) l) := by
  intro k l hk
  have hgl : Dvstar.gateLevels id = [deltaStarU, .succ .zero] := gateLevels_Dvstar
  rw [hgl] at hk
  cases k with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact ⟨DeltaObsRoute.succGate _⟩
  | succ k =>
      cases k with
      | zero =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hk
          subst hk
          exact ⟨DeltaObsRoute.succGate .zero⟩
      | succ k' =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_succ,
            List.getElem?_nil] at hk
          exact Option.noConfusion hk

/-- The out side of the same pin is vacuous (no output levels on the eps path
    of `Dvstar`). -/
theorem sr4DeltaObsPorts_dvstar_out (ls : List Level) :
    ∀ (k : Nat) (l : Level), (Dvstar.outLevels id)[k]? = some l →
      Nonempty (DeltaObsRoute ls (.out k) l) := by
  intro k l hk
  have hol : Dvstar.outLevels id = [] := outLevels_Dvstar
  rw [hol] at hk
  exact Option.noConfusion hk

/-- A param-smuggled NON-succ observation is still routable:
    `.imax (param 0) .zero` is `eqN .zero` (the decider's `.imax` arm ignores
    its first argument, and `eval` agrees), so the `eqNRep` row covers it at
    the bounded representative `.zero`. -/
theorem sr4Route_imaxParam_out (ls : List Level) (pos : ObsPos) :
    Nonempty (DeltaObsRoute ls pos (.imax (.param 0) .zero)) :=
  ⟨DeltaObsRoute.eqNRep .zero (fun _ => rfl) rfl⟩

/-! ## The closer link (consumer composition — not a supply) -/

/-- The wall yields the exact `delta_obs` conclusion: `delta_obs_caseStep_of_ports`
    consumes the wall's port package. This is the consumer-side implication only;
    the wall itself (`sr4DeltaObsWall`) is the row's retained premise. -/
theorem sr4DeltaObsField_of_wall
    {Eₐ : ResolvedEnv} {Aw : Nat → Nat} {tbl : List CRule}
    (wall : sr4DeltaObsWall)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype)}
    {dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)}
    {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (hδ : Demand (.es (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) S σ ρ))
    (pos : ObsPos) :
    CaseStep Aw tbl (.observation ((enrichEnvWfT S.env).defAdm hres hbody htr).hv id
      (instLevel (ls.map σ)) (fun l => σ (instLevel ls l)) pos S σ []) :=
  delta_obs_caseStep_of_ports Aw tbl hδ pos (wall S pos)

#print axioms Rcic.Syn.sr4DeltaObsWall
#print axioms Rcic.Syn.sr4DeltaObsPorts_dvstar
#print axioms Rcic.Syn.sr4DeltaObsPorts_dvstar_out
#print axioms Rcic.Syn.sr4Route_imaxParam_out
#print axioms Rcic.Syn.sr4DeltaObsField_of_wall

end Rcic.Syn
