import rcic.RcicF3StepWEqW
import rcic.RcicDTMetaTyped
import rcic.RcicF3Iota
import rcic.RcicIndGroupNonIRScope

/-!
# RcicF3StepWObstr — the exact W-class obstruction of `stepW` at the `Eq`-prefix fixture

`RcicF3StepWEqW` builds the canonical out-of-scope W-class group (`eqWNode`: `np = 0`,
`mk` at `np_c = 1`, `UniformType` result level, gap entry `.sort .zero`).  This module
closes the loop around `RcicFamAppStepWLok`'s exact boundary (`stepW_boundary_iff`):

1. **Row 1 transports DOWN** (`SortRowField.of_ext`): `SortRowField eqWEnv n →
   SortRowField eqEnvT n` — rows at the W-group env imply rows at the PREFIX.  So
   producing rows at `eqWEnv` is STRICTLY STRONGER than RK-01's open row at the `Eq`
   fixture (`RcicTypedRowsWf`'s frontier): the W-class residue does not float free of
   RK-01, it SITS ON TOP of it (`sortRowField_eqEnvT_of_eqW`).

2. **`stepW` discharges from rows at the group env alone** (`eqW_stepW_of_sortRow`):
   route W2 (`stepW_of_noAppLit_sortRow`) at the node — `SortRowField eqWEnv 0`
   suffices, zero `PiRowField`.

3. **Exactness at the fixture** (`eqW_stepW_iff`): by the boundary iff plus
   `¬ UniformProp` (`eqW_not_uniformProp`), `stepW` at `eqWNode` is LOGICALLY
   EQUIVALENT to the gap row `WalkAgree (GapSortLeAt 0 eqWEnv) eqWMembersT`.
   At THIS fixture the arm then CLOSES UNCONDITIONALLY (`eqW_stepW`): the only gap
   position has view level `.succ .zero` EQUAL to `eqWFamView1.resultLevel`, so no
   row is needed — the residue is a SUPPLY gap (no producer reaches `eqWEnv`), not
   a `stepW` counterexample at this node; the boundary arm is genuinely open only
   at W-class groups whose gap view level is not already `resultLevel`.

4. **No landed supplier reaches the fixture** (`eqW_not_inScope`,
   `eqW_not_scopeCheck`): the `Eq` prefix group is NOT in the copy's scope — the
   J-recursor's stored arity pins `elim = anySort` (`harity : 1 =
   policyRecursorArity 0 .anySort`) while the `Prop`-profile clause demands
   `propOnly` (`not_groupInScopeT_eq`, the first formal `GroupInScopeT` refutation on
   `main`: `Eq` is a `Prop` family with one non-unit non-struct constructor — its
   index `b : α` makes `UnitGroupT`/`StructGroupT` both fail — so clause 2 fires).
   `ScopeCheck` falls with it (`inScope_of_scopeCheck`).

**The named residue `[rcic-f3-stepw-wclass-rows]`** (`StepWEqWRowsAtGroupEnv`, §5):
rows AT the out-of-scope group env `eqWEnv` — a SUPPLY gap, not an open `stepW`
obligation at this node (`stepW` itself closes UNCONDITIONALLY, `eqW_stepW`).  No
landed producer reaches the env (`InScope`/`ScopeCheck`/`RevEnv` all absent), and
the only reduction available (§1) points DOWN at RK-01's own open row.  Row 2
(`PiRowField`) does not transport down at all: its conclusion is `Nonempty (TyConvT
E' ...)` — a derivation WITNESS at the extension, which may read the group's own
members (`66`/`67`) — so `PiRowField eqWEnv → PiRowField eqEnvT` is not even
well-founded as a reduction target.  Twin non-reach (famapp's finding: `Eq`'s J-cell
gated by `a ≡ b`) is cited, not re-proved.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative

open Rcic.F3.PSet (RecNode WalkRec WalkAgree AgreeAt piCount_policyPi piCount_foldApps
  piResult_policyPi)
open Rcic.Syn.FamApp.StepW (SortRowField GapSortLeAt stepW_of_noAppLit_sortRow
  stepW_boundary_iff)

/-! ## §1 transport down the prefix -/

/-- local contexts transport along member extensionality (the `CtxWfT` leg the rows read). -/
def ctxWfTExt {E E' : ResolvedEnv} {n : Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx} → CtxWfT E n Γ → CtxWfT E' n Γ
  | _, .nil => .nil
  | _, .assumption Γ A u hΓ hA => .assumption Γ A u (ctxWfTExt hext hΓ) (hasTyTExt hext hA)
  | _, .letBinding Γ A u v hΓ hA hv =>
      .letBinding Γ A u v (ctxWfTExt hext hΓ) (hasTyTExt hext hA) (hasTyTExt hext hv)

/-- **Row 1 transports DOWN an inclusion**: rows at the extension give rows at the base —
    a chain at `eqWEnv` that avoids the new members is a chain at `eqEnvT`. -/
theorem SortRowField.of_ext {E E' : ResolvedEnv} {n : Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (h : SortRowField E' n) : SortRowField E n := by
  intro Γ hΓ u v hc
  exact h (ctxWfTExt hext hΓ) (tyConvTExt hext hc)

/-- **row 1 at the fixture reduces to RK-01's open row at the `Eq` prefix**: producing
    `SortRowField eqWEnv` is strictly stronger than producing `SortRowField eqEnvT`. -/
theorem sortRowField_eqEnvT_of_eqW {n : Nat} (h : SortRowField eqWEnv n) :
    SortRowField eqEnvT n :=
  SortRowField.of_ext eqW_hext h

/-! ## §2 `stepW` discharges from rows at the group env (route W2, zero `PiRowField`) -/

theorem eqW_stepW_of_sortRow (hSort : SortRowField eqWEnv 0) :
    WalkAgree (AgreeAt 0) eqWMembersT :=
  stepW_of_noAppLit_sortRow (E := eqEnvT) (f := 66) (fm := eqWV) (rr := 68) (rm := eqWRec)
    eqPrefixWfT rfl
    (fun c hc => by simp only [List.mem_singleton] at hc; subst hc; rfl)
    rfl
    (show GroupMembersT (extendEnv eqEnvT 66 eqWV) eqEnvT
      ((66, eqWV) :: [(67, eqWMk)] ++ [(68, eqWRec)]) eqWEnv from eqWMembersT)
    eqWNode eqWWalkRec hSort eqW_gapNoAppLit

/-! ## §3 exactness: at the fixture, `stepW` IS the gap row -/

/-- at `eqWNode` the boundary's `UniformProp` arm is excluded and its `UniformType` arm
    holds, so `stepW` is LOGICALLY EQUIVALENT to the gap row, the arm's exact shape.
    At THIS fixture the arm then CLOSES (see `eqW_stepW` below): the only gap position
    has view level `.succ .zero` EQUAL to `eqWFamView1.resultLevel`, so it is
    refl-dischargeable — `stepW` holds with NO row. -/
theorem eqW_stepW_iff :
    WalkAgree (AgreeAt 0) eqWMembersT ↔
      WalkAgree (GapSortLeAt 0 eqWEnv) eqWMembersT := by
  have hiff := stepW_boundary_iff (E := eqEnvT) (f := 66) (fm := eqWV) (rr := 68) (rm := eqWRec)
    eqPrefixWfT rfl
    (fun c hc => by simp only [List.mem_singleton] at hc; subst hc; rfl)
    rfl
    (show GroupMembersT (extendEnv eqEnvT 66 eqWV) eqEnvT
      ((66, eqWV) :: [(67, eqWMk)] ++ [(68, eqWRec)]) eqWEnv from eqWMembersT)
    eqWNode eqWWalkRec
  constructor
  · intro hS
    rcases hiff.mp hS with hP | ⟨_hT, hG⟩
    · exact absurd hP eqW_not_uniformProp
    · exact hG
  · intro hG
    exact hiff.mpr (Or.inr ⟨eqW_uniformType, hG⟩)

/-- **`stepW` at the fixture holds UNCONDITIONALLY** (no row, no `PiRowField`): the
    walk is `family / constructor / recursor / nil`, and the constructor's only gap
    position (`k = 0`, `.sort .zero`) has view level `fun _ => .succ .zero` which EQUALS
    `eqWFamView1.resultLevel = .succ .zero`, so the arm is closed by `leN_refl`.  The
    rows residue below is a SUPPLY gap — nothing produces the rows at `eqWEnv`, and
    producing them would entail RK-01's row — but `stepW` at THIS node does not wait
    on them. -/
theorem eqW_stepW : WalkAgree (AgreeAt 0) eqWMembersT :=
  ⟨trivial, (fun _ _ _ _ => Or.inr (leN_refl _)), trivial, trivial⟩

/-! ## §4 the `Eq` prefix group is NOT in the copy's scope -/

section EqNotInScope

/-- a constructor's field telescope is a Π-tower with exactly one binder per field. -/
theorem piCount_ctorFieldsT (f : Nat) (ls : List Level) :
    (pl : List (Expr Nat)) → (σ : SubstT) → (fields : List FieldT) → (res : List (Expr Nat)) →
    piCount (ctorFieldsT f ls pl σ fields res) = fields.length := by
  intro pl σ fields res
  induction fields generalizing pl σ with
  | nil =>
      show piCount (foldApps (Expr.const f ls) (pl ++ res.map (substT σ))) = 0
      exact piCount_foldApps (Expr.const f ls) (fun _ _ h => nomatch h)
        (pl ++ res.map (substT σ))
  | cons fld fs ih =>
      cases fld with
      | plain D _ => exact congrArg (fun k => k + 1) (ih _ _)
      | drec _ => exact congrArg (fun k => k + 1) (ih _ _)
      | drecD _ _ => exact congrArg (fun k => k + 1) (ih _ _)

/-- **the `Eq` group is not in the copy's scope** — the first formal `GroupInScopeT`
    refutation on `main`.  The J-recursor's stored arity pins `elim = anySort`;
    the `Prop`-profile clause (clause 2 of `GroupProfileT`) demands `propOnly`: `Eq` is
    a `Prop` family (`fv.sort = .zero`) with one constructor whose index `b : α` fails
    `UnitGroupT` and `StructGroupT` (both need `fv.indices = []`, but the family
    telescope has `3 = params + indices` binders while the constructor's mirrors —
    length-coupled to `fv.params` by `MirrorsConvT` — number at most the constructor's
    `2` Π-binders). -/
theorem not_groupInScopeT_eq :
    ¬ Nonempty (GroupInScopeT emptyEnv 63 eqFamT [(64, eqReflT)] 65 eqRecT) := by
  rintro ⟨g⟩
  -- the constructor list: exactly one, its member `eqReflT` (layout + entry equations)
  have h1 : g.cs.map GroupCtorT.entry = [(64, eqReflT)] := by
    calc g.cs.map GroupCtorT.entry
        = ((g.cs.map GroupCtorT.entry).reverse).reverse :=
          (List.reverse_reverse _).symm
      _ = [(64, eqReflT)].reverse := by rw [g.hctors]
      _ = [(64, eqReflT)] := rfl
  obtain ⟨c, hcs⟩ : ∃ c, g.cs = [c] := by
    have h0 : (List.map GroupCtorT.entry g.cs).length = 1 := by
      rw [h1]; rfl
    simp only [List.length_map, List.length_cons, List.length_nil] at h0
    exact List.length_eq_one.mp h0
  rw [hcs] at h1
  have hce : GroupCtorT.entry c = (64, eqReflT) := by
    simpa using h1
  have hcme : c.member = eqReflT := (Prod.mk.inj hce).2
  have hcsne : g.cs ≠ [] := by rw [hcs]; simp
  -- the family: `UniformProp`, telescope of exactly 3 binders
  have hpc : piCount (policyPi (List.map Prod.fst (g.fv.params ++ g.fv.indices))
      (Expr.sort g.fv.sort)) = 3 := by
    rw [← g.fv.stored]; rfl
  rw [piCount_policyPi] at hpc
  have hz : piCount (Expr.sort g.fv.sort) = 0 := rfl
  have hpc2 : (List.map Prod.fst (g.fv.params ++ g.fv.indices)).length = 3 := by omega
  have hml : (List.map Prod.fst (g.fv.params ++ g.fv.indices)).length
      = (g.fv.params ++ g.fv.indices).length := List.length_map _ _
  have hla : (g.fv.params ++ g.fv.indices).length
      = g.fv.params.length + g.fv.indices.length := List.length_append _ _
  have htel : g.fv.params.length + g.fv.indices.length = 3 := by omega
  have hsort : g.fv.sort = Level.zero := by
    have hr : piResult (policyPi (List.map Prod.fst (g.fv.params ++ g.fv.indices))
        (Expr.sort g.fv.sort)) = piResult eqFamT.mtype := by rw [g.fv.stored]
    rw [piResult_policyPi] at hr
    have h2 : piResult eqFamT.mtype = Expr.sort Level.zero := rfl
    rw [h2] at hr
    have hs : Expr.sort g.fv.sort = Expr.sort Level.zero := hr
    exact Expr.sort.inj hs
  have hUP : UniformProp g.fv.sort := hsort ▸ uniformProp_zero
  -- the constructor: at most 2 mirrors, so at most 2 family parameters
  have h2 : piCount eqReflT.mtype = 2 := rfl
  have hcvs : eqReflT.mtype =
      ctorTypeT 63 (canonLevels eqFamT.arity) c.view.mirrors c.view.fields c.view.res :=
    (congrArg (fun m : CheckedMember => m.mtype) hcme).symm.trans c.view.stored
  rw [hcvs] at h2
  unfold ctorTypeT at h2
  rw [piCount_policyPi, piCount_ctorFieldsT] at h2
  simp only [List.length_map] at h2
  -- h2 : c.view.mirrors.length + c.view.fields.length = 2
  have hmir : c.view.mirrors.length = g.fv.params.length :=
    mirrorsConvT_length c.view.mirrorsConv
  have hplen : g.fv.params.length ≤ 2 := by omega
  -- so the family has an index: neither unit nor struct
  have hidxNe : g.fv.indices ≠ [] := by
    intro hni
    rw [hni, List.length_nil] at htel
    omega
  have hNU : ¬ UnitGroupT g.cs := by
    rintro ⟨_, hidxnil, _⟩
    exact hidxNe hidxnil
  have hNS : ¬ StructGroupT g.cs := by
    rintro ⟨_, hidxnil, _⟩
    exact hidxNe hidxnil
  -- the recursor's stored arity pins `elim = anySort`
  have hany : g.grec.elim = EliminationPolicy.anySort := by
    cases hel : g.grec.elim with
    | anySort => rfl
    | propOnly =>
        have har := g.grec.harity
        rw [hel, g.hrm] at har
        have hone : (1 : Nat) = 0 := har
        omega
  -- clause 2 fires: `propOnly`, contradicting `anySort`
  have hpo := g.hprof.2 hUP hcsne hNU hNS
  rw [hpo] at hany
  exact EliminationPolicy.noConfusion hany

/-- the W-fixture's env is outside the copy's scope — through its prefix. -/
theorem eqW_not_inScope : ¬ eqWEnvWfT.InScope := by
  intro hIS
  have h1 : eqPrefixWfT.InScope := hIS.1
  exact not_groupInScopeT_eq h1.2

/-- the W-fixture's env is outside the scope test's reach (`ScopeCheck → InScope`). -/
theorem eqW_not_scopeCheck : ¬ eqWEnvWfT.ScopeCheck :=
  fun h => eqW_not_inScope (eqWEnvWfT.inScope_of_scopeCheck h)

end EqNotInScope

/-! ## §5 the named residue -/

/-- **The named residue `[rcic-f3-stepw-wclass-rows]`**: rows AT the out-of-scope group
    env.  Everything else at the fixture is closed — INCLUDING `stepW` itself
    (`eqW_stepW`: the gap arm closes by `leN_refl` at this node, no row needed):

    * `stepW` at the fixture ⇔ the gap row (`eqW_stepW_iff`), and the gap row CLOSES
      here (`eqW_stepW`); rows still suffice in general (`eqW_stepW_of_sortRow`,
      route W2, zero `PiRowField`) at groups where the arm is not refl-closed;
    * row 1 at `eqWEnv` ⇒ row 1 at `eqEnvT` (`sortRowField_eqEnvT_of_eqW`) — RK-01's own
      open row; row 2 does NOT transport down (its conclusion is a derivation WITNESS at
      the extension, free to read members `66`/`67`);
    * no landed producer reaches `eqWEnv` (`eqW_not_inScope`, `eqW_not_scopeCheck`;
      `RevEnv` is the revealed-singleton class — `eqWEnv` is a fresh group env over
      `Eq`, not a `RevEnv` record), and twin non-reach for `Eq`'s J-cell (`a ≡ b` gating)
      is famapp's documented finding, cited not re-proved.

    The residue is exact on the SUPPLY side: no landed producer reaches `eqWEnv`,
    and producing these rows is strictly stronger than RK-01's frontier.
    Nothing here claims `stepW` fails at `eqWNode` — it holds (`eqW_stepW`). -/
def StepWEqWRowsAtGroupEnv : Prop :=
  ∀ n, SortRowField eqWEnv n ∧ PiRowField eqWEnv n

/-- the residue suffices for `stepW` at the fixture (its row-1 half, via route W2). -/
theorem stepW_of_stepWEqWRows (h : StepWEqWRowsAtGroupEnv) :
    WalkAgree (AgreeAt 0) eqWMembersT :=
  eqW_stepW_of_sortRow (h 0).1

/-- the residue is strictly stronger than RK-01's row 1 at the `Eq` prefix. -/
theorem sortRowField_eqEnvT_of_stepWEqWRows (h : StepWEqWRowsAtGroupEnv) (n : Nat) :
    SortRowField eqEnvT n :=
  sortRowField_eqEnvT_of_eqW (h n).1

end Rcic.Declarative

#print axioms Rcic.Declarative.eqW_stepW_of_sortRow
#print axioms Rcic.Declarative.eqW_stepW_iff
#print axioms Rcic.Declarative.eqW_stepW
#print axioms Rcic.Declarative.not_groupInScopeT_eq
#print axioms Rcic.Declarative.eqW_not_inScope
#print axioms Rcic.Declarative.stepW_of_stepWEqWRows
