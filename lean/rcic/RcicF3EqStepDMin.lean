import rcic.RcicF3Assembly
import rcic.RcicF3DFixture
import rcic.RcicF3StepWMin

/-!
# F3 stepD — boundary refutation and the minimal group-granular face

`closure_claim = 0`.

The item (cc, 20261027T031742Z): discharge `PartitionSteps.stepD` (class D,
node granularity) — the critical path of the R-CIC soundness tier. What this
module establishes, from what is on this base (`#8051`'s
`fable/rcic-f3-coverage` @ `bfc7ffb8`), is the boundary shape:

## §1 The node-granular field is refuted, not open

At the δ fixture (`RcicF3DFixture`, from `RcicTypedDeltaRecPins`: `Id` at 0,
`F : Sort 1` at 1, `mk : Id F → F` at 2, `F.rec` at 3), the node `mk` is a
genuine `PendD` node (`dr_pendD`: the field `Id F` has admission shape
`recursive 0` and is not a `DirectClause` — its head is the definition `Id`,
not the family), not a `PendA` node (`dr_not_pendA`), and cannot satisfy
`NodeFieldRow.1` (`dr_not_recFieldsDirect`, via the landed
`clauses_of_recFieldsDirect`). Hence:

* `not_partitionSteps` : `¬ PartitionSteps P K` for every `P`, `K` — so the
  antecedent of the landed `tierF3Uncond_of_partition` is **empty**;
* `not_partitionStepsABD` : the same refutation empties the
  `PartitionStepsABD` antecedent of the landed stepW wrapper
  (`StepWMin.tierF3Uncond_of_hyp`, #8222) — its `stepD` field is the same
  node-granular one. **Cross-lane finding for devin-fcd / the fcd lane.**

This upgrades the assembly's own marginal note ("a genuine PendD node cannot
satisfy `NodeFieldRow.1`") to theorems with the vacuity corollary.

## §2 The minimal face: `PartitionStepsABW` + `StepDHyp` + `DDispatch`

* `PartitionStepsABW` — `PartitionSteps` with the `stepD` field removed (the
  complementary projection to `StepWMin.PartitionStepsABD`, which drops
  `stepW` instead). Fields verbatim; the A/B1/W debts are other lanes'
  named antecedents, untouched.
* `StepDHyp P K` — the D-arm of the fold's group step, at the granularity the
  tier's own `GInvSteps.stepGrp` consumes and the accepted interface named
  (group-granular): owed only at a group that *has* a `PendD` node and no
  `PendA` node, in the D model's own class conditions (`GroupClassD`,
  `WalkClass`). What it asks for is exactly the `gInv_groupD` step translated
  from the D model's `GInvD`-at-`envCtxD` invariant to the fold's
  `GInv`-at-`envCtx` invariant — see §4.
* `DDispatch` — the per-environment dispatchability guard: every group is
  either `PendD`-free (route G — the landed fold, with the A-debt's node rows
  as its named hypotheses) or a genuine D group in the D model's class shape
  (the `StepDHyp` arm). Groups in neither arm are named in §4.
* `nodeStepRow_of_abw` — the generic dispatcher minus the D arm: at a
  `¬ PendD` node, nothing D-flavored is owed.
* `walkG_of_abwDD`, `gInvSteps_of_abw_hyp`, `tierF3Concl_of_abw_hyp`,
  `tierF3UncondDD_of_abw_hyp`, `tierF3UncondDD_of_ab_hyp` — the rebuilt assembly:
  singles class-independent via the landed `gInv_singleW`; D-free groups via
  the landed `gInv_group_of`; D groups via `StepDHyp` (now taking the group's
  own `BoundG`/`BoundDG`, as the accepted `gInv_groupD` interface does). The
  tier conclusion then follows by the landed tail (`readsOKAlong_envCtxW` →
  `faithfulR_envμR` → `envSound_of` → `empty_of_falseRec`).
* `TierF3UncondDD` — the tier statement with the dispatchability guard
  `DDispatch hW` **inside** the per-environment quantifier. The guard is the
  honest §4 residue and is refutable as a universal (any axiom-free §4
  environment), so it must not be hoisted into a global hypothesis — the
  earlier hoisted form was a vacuous premise (audit #8234, defect 4).
* `PartitionStepsAB` + `tierF3UncondDD_of_ab_hyp` — the A/B-only face of the
  partition steps (the `stepD` field of `StepWMin.PartitionStepsABD`, which
  §1 refutes, is never taken as an antecedent), composed with the landed
  `StepWMin.StepWHyp` for the W rows.

## §3 Non-refutability and non-vacuity (the #8225 discipline)

* `falseEnvU_classGD`, `tierF3Concl_falseEnvU` — the conditional tier has a
  non-vacuous instance independent of `StepDHyp`: at the admitted empty-type
  environment the conclusion holds unconditionally via the landed
  `consistent4_GD` (`ClassGD` there by this module, bounds landed).
* `not_pendA_of_groupClassD`, `ddispatch_of_classGD`, `drEnvWfT_ddispatch`,
  `drEnvWfT_dArm_nonempty` — `StepDHyp` is *owed, not vacuous*: every
  `ClassGD` environment is D-dispatchable, and the δ fixture's group is a
  genuine D group (a real `PendD` node, no `PendA`), so the open arm of the
  wrapper is inhabited at a tree fixture.
* Attempted refutation of `StepDHyp P K` at the δ fixture: no counter-model.
  The `GInvD`-twin of the step is *proved* on this base (`gInv_groupD` at
  `ClassGD` groups); what is missing is only the boundary conversion between
  the two invariants (`envCtx` vs `envCtxD`) at the group env — closed on the
  routec umbrella (`7088984faf`/`1b0b519e20`, verified at `GInvD`-level by
  this lane's `RcicF3EqDMix`, PR #8044) and not on this base. At the fixture
  the definition `Id` is transparent, so the raw and normalized tables agree
  denotationally (`RcicF3EqDBridge.normField_eq_self_of_clause` on the
  umbrella base); no model distinguishes `StepDHyp` from its proved twin.
  Reported, not proved — the exact missing pieces are named in §4.

## §4 The exact obstruction (measured, not prose)

For a `DDispatch`-failing environment the wrapper does not apply; each way to
fail is a named residue:

1. **A∧D group** (a `PendA` node in a group with a `PendD` node): the landed
   dispatch routes `PendA` nodes to `stepA`, so the corner is the A lane's
   debt by convention, at group granularity when that lane lands. Not D's.
2. **D group outside `GroupClassD`** (e.g. a `Prop` family whose δ-hidden
   field is revealed in the result indices, or a family-mentioning field
   under `Prop` large elimination): outside the D model itself
   (`consistent4_GD` does not apply either) — a genuine open corner, the
   D-analog of `PendC`.
3. **The boundary conversion** inside `StepDHyp` itself: `GInv`-at-`envCtx`
   ⇄ `GInvD`-at-`envCtxD` at the mixed group env. The middle
   (`gInv_groupD`) is landed; the seed/read-back conversions are the
   umbrella's role-parametric steps (`gInv_group_ofAtCtx`,
   `readsOKAlong_envCtxDW`), not on this base.

Axioms of every sealed declaration: ⊆ {`propext`, `Quot.sound`}. All case
splits run on `Premises4.dec` (a premise field — no `Classical.choice`).
-/

namespace Rcic.F3.StepDMin

open Rcic.Declarative Rcic.F3 Rcic.F3.PSet

/-! ## §1 The node-granular field is refuted at the δ fixture -/

/-- `mk`'s field is not a direct clause, at any levels/parameters/depth: it
mentions the family (so not family-free) and its head is the definition
`Id` (`0`), not the family (`1`) — a canonical family application is
`foldApps`-headed by the family constant. -/
private theorem dr_not_direct (lsF : List Level) (np nq d : Nat) :
    ¬ DirectClause 1 lsF np nq d drField := by
  intro hcl
  rcases hcl with hfree | ⟨idx, hEq, _, _⟩
  · exact absurd hfree (by decide)
  · exact absurd (foldApps_const_head
      (hEq.symm.trans rfl : foldApps (.const 1 lsF) (policyParameterLocals np d ++ idx)
        = foldApps (.const 0 []) [.const 1 []])) (by decide)

/-- No function-recursive shape at the fixture's node: the one field's
admission shape is `recursive 0`. -/
theorem dr_not_pendA (node : DrNode) : ¬ PendA node := by
  rintro ⟨i, k, m, h⟩
  rw [dr_shapes node i] at h
  cases k with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      injection h with h'
      exact Nat.noConfusion h'
  | succ k =>
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at h
      exact Option.noConfusion h

/-- The fixture's node is a genuine D node: the field `Id F` has admission
shape `recursive 0` and is not the canonical family application. -/
theorem dr_pendD (node : DrNode) : PendD node := by
  have hlen : node.a.constructors.length = 1 :=
    node_ctors_length (ctors := [(2, drMkMember)]) node rfl
  refine ⟨⟨0, by omega⟩, 0, drField, ?_, ?_, ?_⟩
  · rw [(dr_view node ⟨0, by omega⟩).2.2]; simp
  · rw [dr_shapes node ⟨0, by omega⟩]; simp
  · exact dr_not_direct _ _ _ _

/-- Row `.1` fails at the fixture's node: `mk`'s field mentions the family
without being a canonical family application. -/
theorem dr_not_recFieldsDirect (node : DrNode) :
    ¬ ∀ i, RecFieldsDirect 1 (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length
      (node.a.constructorViews i).fields 0 := by
  intro h
  have hlen : node.a.constructors.length = 1 :=
    node_ctors_length (ctors := [(2, drMkMember)]) node rfl
  have i0 : Fin node.a.constructors.length := ⟨0, by omega⟩
  have hcl := clauses_of_recFieldsDirect _ _ (h i0) 0 drField (by
    rw [(dr_view node i0).2.2]; simp)
  exact dr_not_direct _ _ _ _ hcl

/-- The whole node row fails at the fixture's node — the row's `.1` conjunct
is `∀ i, RecFieldsDirect`, refuted by `dr_not_recFieldsDirect`. -/
theorem dr_not_nodeFieldRow (P : Premises4) (K : Nat → Nat) (node : DrNode) :
    ¬ NodeFieldRow P K (f := 1) (fm := drFamMember) (rr := 3) (rm := drRecMember)
      (ctors := [(2, drMkMember)]) drBaseWfT rfl
      (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT node :=
  fun h => dr_not_recFieldsDirect node h.1

/-- **The node-granular `stepD` field is refuted.** `mk` is a `PendD` node,
not a `PendA` node, and its node row fails — so no `PartitionSteps P K`
exists, for any premises or bound. The antecedent of the landed
`tierF3Uncond_of_partition` is empty. -/
theorem not_partitionSteps (P : Premises4) (K : Nat → Nat) : ¬ PartitionSteps P K := by
  intro steps
  obtain ⟨node, _⟩ := group_nodeD (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)]) (rr := 3)
    (rm := drRecMember) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT
  exact dr_not_nodeFieldRow P K node
    (steps.stepD (f := 1) (fm := drFamMember) (rr := 3) (rm := drRecMember)
      (ctors := [(2, drMkMember)]) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl
      drMembersT node (dr_pendD node) (dr_not_pendA node))

/-- **Cross-lane finding**: the landed stepW wrapper's `PartitionStepsABD`
antecedent is empty too — its `stepD` field is the same node-granular one, so
`StepWMin.tierF3Uncond_of_hyp` (#8222) is vacuous as stated. -/
theorem not_partitionStepsABD (P : Premises4) (K : Nat → Nat) :
    ¬ StepWMin.PartitionStepsABD P K := by
  intro abd
  obtain ⟨node, _⟩ := group_nodeD (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)]) (rr := 3)
    (rm := drRecMember) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT
  exact dr_not_nodeFieldRow P K node
    (abd.stepD (f := 1) (fm := drFamMember) (rr := 3) (rm := drRecMember)
      (ctors := [(2, drMkMember)]) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl
      drMembersT node (dr_pendD node) (dr_not_pendA node))

/-! ## §2 The minimal face -/

/-- **The tier's non-D antecedents**: `PartitionSteps` with the `stepD` field
removed — the complementary projection to `StepWMin.PartitionStepsABD` (which
drops `stepW` instead). Field types verbatim from the assembly; the A/B1/W
debts stay the named antecedents of their own lanes. -/
structure PartitionStepsABW (P : Premises4) (K : Nat → Nat) : Prop where
  /-- **A**: function-recursive fields (`recursive (m+1)`); the KT lane. -/
  stepA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendA node →
      NodeFieldRow P K hE hfam hctors hrec hmem node
  /-- **B1**: `Prop` family, `anySort` elim, a field revealed in result
  indices (including `PendC ∧ PendB` nodes); the B lane. -/
  stepB1 : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendB node → ¬ PendA node → ¬ PendD node →
      NodeFieldRow P K hE hfam hctors hrec hmem node
  /-- **W**: the `AgreeAt` row for a node whose constructor walk splits off a
  different parameter count (`PendW`); the GW lane. -/
  stepW : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendW hmem node →
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem

/-- The landed `PartitionSteps` projects onto the D-free face. -/
theorem partitionStepsABW_of_steps {P : Premises4} {K : Nat → Nat} (steps : PartitionSteps P K) :
    PartitionStepsABW P K where
  stepA := steps.stepA
  stepB1 := steps.stepB1
  stepW := steps.stepW

/-- **The minimal D-hypothesis of the soundness tier**, at the granularity the
tier's own fold consumes and the accepted interface named: the D-arm of the
group step, owed only at a group that has a genuine `PendD` node and no
`PendA` node, in the D model's own class conditions, at the group's own
`BoundG`/`BoundDG` level bounds — the exact bound inputs the proved D-group
step `gInv_groupD` takes. The `GInvD`-twin of this step is proved on this
base (`gInv_groupD` at `ClassGD` groups); what is open is exactly the
boundary conversion between the fold's `GInv`-at-`envCtx` invariant and the
D model's `GInvD`-at-`envCtxD` invariant at the mixed group env (§4 of the
module docstring). -/
def StepDHyp (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hNA : ∀ node : RecNode E E' f rr rm, ¬ PendA node)
    (hEx : ∃ node : RecNode E E' f rr rm, PendD node),
    GroupClassD E E' f rr rm →
    (∀ node : RecNode E E' f rr rm, WalkClass node.a.family.parameters.length hmem) →
    BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    GInv P K hE →
    GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-- **D-dispatchability**: every group of the environment is either
`PendD`-free (route G — the landed fold, with the A-debt's node rows as its
named hypotheses) or a genuine D group in the D model's class shape (the
`StepDHyp` arm). The two ways to fail are the named residues of §4: an A∧D
group, and a `PendD` group outside `GroupClassD`. The axiom arm mirrors the
`Covered` recursion shape (axioms are excluded from the fold by the coverage
predicate, not by this one). -/
def DDispatch : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => DDispatch hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => DDispatch hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => DDispatch hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => DDispatch hE
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem =>
      DDispatch hE ∧
      ((∀ node : RecNode E E' f rr rm, ¬ PendD node) ∨
        ((∃ node : RecNode E E' f rr rm, PendD node) ∧
          (∀ node : RecNode E E' f rr rm, ¬ PendA node) ∧
          GroupClassD E E' f rr rm ∧
          (∀ node : RecNode E E' f rr rm,
            WalkClass node.a.family.parameters.length hmem)))

/-- The generic dispatcher minus the D arm: at a `¬ PendD` node, nothing
D-flavored is owed. (Mirror of the assembly's `nodeStepRow`; the `PendD`
case is gone because the caller routes D groups through `StepDHyp`
wholesale.) -/
theorem nodeStepRow_of_abw (P : Premises4) (K : Nat → Nat) (abw : PartitionStepsABW P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hD : ¬ PendD node) :
    NodeStepRow P K hE hfam hctors hrec hmem node := by
  have hAg : WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
    cases P.dec (WalkClass node.a.family.parameters.length hmem) with
    | isTrue hw => exact walkAgree_of_walkClass node hmem hw
    | isFalse hw => exact abw.stepW hE hfam hctors hrec hmem node hw
  cases P.dec (PendA node) with
  | isTrue hA =>
      have hr := abw.stepA hE hfam hctors hrec hmem node hA
      exact ⟨hr.1, hAg, hr.2⟩
  | isFalse hA =>
    cases P.dec (PendB node) with
    | isTrue hB =>
        have hr := abw.stepB1 hE hfam hctors hrec hmem node hB hA hD
        exact ⟨hr.1, hAg, hr.2⟩
    | isFalse hB =>
        have hG := groupClassAt_of_notADB P node hA hD hB
        exact ⟨hG.1, hAg, fun hBB μ X => recPkg_classG P K node hG.2 (hBB.2.2.2 node) X⟩

/-- The covered-environment walk under the split: D-free groups by the node
rows, D groups by `WalkClass` (via `walkAgree_of_walkClass`). -/
theorem walkG_of_abwDD (P : Premises4) (K : Nat → Nat) (abw : PartitionStepsABW P K) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → Covered hW → DDispatch hW → WalkG hW
  | _, .empty, _, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _ => hC
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hDD =>
      walkG_of_abwDD P K abw hE hC hDD
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC, hDD => walkG_of_abwDD P K abw hE hC hDD
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC, hDD => walkG_of_abwDD P K abw hE hC hDD
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC, hDD =>
      ⟨walkG_of_abwDD P K abw hE hC.1 hDD.1, walkRec_of_group hmem, fun node =>
        match hDD.2 with
        | Or.inl hND =>
            (nodeStepRow_of_abw P K abw hE hfam hctors hrec hmem node (hND node)).2.1
        | Or.inr ⟨_, _, _, hWC⟩ => walkAgree_of_walkClass node hmem (hWC node)⟩

/-- The step interface under the split, at the coverage-with-`DDispatch`
class and the `BoundG ∧ BoundDG` bound pair (both bounds are the tier's own
antecedents; the D-group arm of `StepDHyp` needs the group's `BoundDG` too):
singles class-independent (`gInv_singleW`); D-free groups by the landed
`gInv_group_of` over the D-free node rows; D groups by `StepDHyp`. -/
theorem gInvSteps_of_abw_hyp (P : Premises4) (K : Nat → Nat) (abw : PartitionStepsABW P K)
    (hyp : StepDHyp P K) :
    GInvSteps P K (fun {E : ResolvedEnv} (hW : EnvWfT E) => Covered hW ∧ DDispatch hW)
      (fun {E : ResolvedEnv} (hW : EnvWfT E) => BoundG K hW ∧ BoundDG K hW) where
  stepDef := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.1.2
      (walkG_of_abwDD P K abw hE hC.1 hC.2) IH⟩
  stepThm := fun _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp hB.1.2
      (walkG_of_abwDD P K abw hE hC.1 hC.2) IH⟩
  stepOpq := fun _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.1.2
      (walkG_of_abwDD P K abw hE hC.1 hC.2) IH⟩
  stepGrp := fun _ _ _ _ _ _ _ hE hfam hctors hrec hmem hC hB =>
    ⟨⟨hC.1.1, hC.2.1⟩, ⟨hB.1.1, hB.2.1⟩, fun IH =>
      match hC.2.2 with
      | Or.inl hND =>
          gInv_group_of P K hE hfam hctors hrec hmem
            (fun node i => (nodeStepRow_of_abw P K abw hE hfam hctors hrec hmem node (hND node)).1 i)
            (walkRec_of_group hmem)
            (fun node => (nodeStepRow_of_abw P K abw hE hfam hctors hrec hmem node (hND node)).2.1)
            hB.1.2.1 hB.1.2.2.1
            (fun node μ X =>
              (nodeStepRow_of_abw P K abw hE hfam hctors hrec hmem node (hND node)).2.2 hB.1 μ X)
            IH
      | Or.inr ⟨hEx, hNA, hGC, hWC⟩ => hyp hE hfam hctors hrec hmem hNA hEx hGC hWC hB.1 hB.2 IH⟩

/-- **The guarded tier conclusion**: with the D-free face of the partition
steps, the minimal D-hypothesis, and D-dispatchability, the tier's per-env
conclusion holds — the landed tail (`readsOKAlong_envCtxW` →
`faithfulR_envμR` → `envSound_of` → `empty_of_falseRec`) over the rebuilt
step instance, at the tier's own `BoundG`/`BoundDG` antecedents. -/
theorem tierF3Concl_of_abw_hyp (P : Premises4) (K : Nat → Nat) (abw : PartitionStepsABW P K)
    (hyp : StepDHyp P K) {E : ResolvedEnv} (hW : EnvWfT E) (hDD : DDispatch hW)
    (hB : BoundG K hW) (hBDG : BoundDG K hW) (hAx : AxiomFreeEnv' E)
    (h1 : E.members 1 = some falseRecMemberU) (n : Nat) (e : Expr Nat)
    (D : HasTyT E n [] e (.const 0 [])) (hLOK : LevelsBelow 4 K D) : False := by
  have hC : Covered hW ∧ DDispatch hW := ⟨EnvWfT_axiomFree_covered P hW hAx, hDD⟩
  have hI : GInv P K hW := gInv_of_steps P K _ _ (gInvSteps_of_abw_hyp P K abw hyp)
    (fun _ _ _ _ _ _ _ _ _ hCx => hCx.1) hW hC ⟨hB, hBDG⟩
  have hRA := readsOKAlong_envCtxW hW (walkG_of_abwDD P K abw hW hC.1 hDD)
    (envCtx hW) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtx hW) hW hRA).1
  have hIv := hI (envCtx hW) (fun _ _ => rfl) _ hF
  have hES := envSound_of P (Efin := E) (fun _ _ h => h) hIv.1
    (fun r m hm hk => hIv.2 E (fun _ _ h => h) r m hm hk) (fun _ => 0) n
  exact empty_of_falseRec P (hIv.1 1 _ h1) (sound_ty (P.good _ rfl) hES D hLOK ρ0 trivial)

/-- **The D-dispatchable tier**: `Rcic.Apex.TierF3Uncond` with the
dispatchability guard `DDispatch hW` moved **inside** the per-environment
quantifier. The guard is the honest §4 residue — it fails at named corners
(an A∧D group; a `PendD` group outside `GroupClassD`), so hoisting it to a
universal `∀ E hW, AxiomFreeEnv' E → DDispatch hW` would make the premise
refutable and the theorem vacuous (audit defect). The landed apex types
(`TierF3Uncond` etc.) carry no dispatchability slot; closing §4 turns this
into them by dropping the `DDispatch` conjunct. -/
def TierF3UncondDD : Prop :=
  Premises4 → ∀ (K : Nat → Nat) (E : ResolvedEnv) (hW : EnvWfT E),
    DDispatch hW → BoundG K hW → BoundDG K hW → AxiomFreeEnv' E →
    E.members 0 = some falseFamMember → E.members 1 = some falseRecMemberU →
    ∀ (n : Nat) (e : Expr Nat) (D : HasTyT E n [] e (.const 0 [])), LevelsBelow 4 K D → False

/-- **The D-dispatchable tier from the D-free face**: with `PartitionStepsABW`
and `StepDHyp` alone — no universal dispatchability premise, no `stepD`
antecedent. Compare the landed `tierF3Uncond_of_partition`, whose antecedent
is empty (§1). -/
theorem tierF3UncondDD_of_abw_hyp (abw : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsABW P K)
    (hyp : ∀ (P : Premises4) (K : Nat → Nat), StepDHyp P K) : TierF3UncondDD := by
  intro P K E hW hDD hB hBDG hAx _h0 h1 n e D hLOK
  exact tierF3Concl_of_abw_hyp P K (abw P K) (hyp P K) hW hDD hB hBDG hAx h1 n e D hLOK

/-- **The A/B-only face of the partition steps** (`stepA` + `stepB1`, field
types verbatim): the largest face of the landed `PartitionSteps` that §1 does
NOT refute — the node-granular `stepD` field (refuted at the δ fixture) is
never an antecedent here. -/
structure PartitionStepsAB (P : Premises4) (K : Nat → Nat) : Prop where
  /-- **A**: function-recursive fields (`recursive (m+1)`); the KT lane. -/
  stepA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendA node →
      NodeFieldRow P K hE hfam hctors hrec hmem node
  /-- **B1**: `Prop` family, `anySort` elim, a field revealed in result
  indices (including `PendC ∧ PendB` nodes); the B lane. -/
  stepB1 : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendB node → ¬ PendA node → ¬ PendD node →
      NodeFieldRow P K hE hfam hctors hrec hmem node

/-- The D-free face projects onto the A/B-only face. -/
theorem partitionStepsAB_of_abw {P : Premises4} {K : Nat → Nat} (abw : PartitionStepsABW P K) :
    PartitionStepsAB P K where
  stepA := abw.stepA
  stepB1 := abw.stepB1

/-- The landed stepW wrapper's face projects onto the A/B-only face — WITHOUT
the refuted `stepD` field. -/
theorem partitionStepsAB_of_abd {P : Premises4} {K : Nat → Nat} (abd : StepWMin.PartitionStepsABD P K) :
    PartitionStepsAB P K where
  stepA := abd.stepA
  stepB1 := abd.stepB1

/-- The same tier through the A/B face + the landed `StepWMin.StepWHyp` for
the W rows: the composition of the two wrappers takes only the UNrefuted
fields of `PartitionStepsABD` — its `stepD` is never consumed. (The
node-granular `stepA` itself is the A lane's own debt; per the stepW lane's
fixture (#8231) it is refutable at `wEnv`, so this face — like every face
carrying a node-granular `stepA` — is provisional on the A lane's
group-granular restatement; see #8237.) -/
theorem tierF3UncondDD_of_ab_hyp (ab : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsAB P K)
    (hW : StepWMin.StepWHyp) (hyp : ∀ (P : Premises4) (K : Nat → Nat), StepDHyp P K) :
    TierF3UncondDD :=
  tierF3UncondDD_of_abw_hyp
    (fun P K => ⟨(ab P K).stepA, (ab P K).stepB1,
      fun hE hfam hctors hrec hmem node hPend =>
        StepWMin.stepW_of_hyp P hW hE hfam hctors hrec hmem node hPend⟩)
    hyp

/-- The conditional tier in the D-dispatchable form (the DD analog of the
landed `tierF3_of_tierF3Uncond`: the injectivity antecedent is dead code). -/
def TierF3DD : Prop := Rcic.Apex.FamAppConvInjAll → TierF3UncondDD

theorem tierF3DD_of_abw_hyp (abw : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsABW P K)
    (hyp : ∀ (P : Premises4) (K : Nat → Nat), StepDHyp P K) : TierF3DD :=
  fun _ => tierF3UncondDD_of_abw_hyp abw hyp

/-- The kernel tier in the D-dispatchable form (F1 is landed and closed). -/
def KernelSoundnessTierDD : Prop := Rcic.Apex.TierF1 ∧ TierF3DD

theorem kernelSoundnessTierDD_of_abw_hyp (abw : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsABW P K)
    (hyp : ∀ (P : Premises4) (K : Nat → Nat), StepDHyp P K) : KernelSoundnessTierDD :=
  ⟨Rcic.Apex.tierF1, tierF3DD_of_abw_hyp abw hyp⟩

/-! ## §3 Non-refutability and non-vacuity -/

/-- No function-recursive shape at a `GroupClassD` group's nodes: a `PendA`
witness would put a `recursive (m+1)` shape in the analysis, against
`GroupClassD`'s `NoFunRec` clause. -/
theorem not_pendA_of_groupClassD {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (hGC : GroupClassD E E' f rr rm) (node : RecNode E E' f rr rm) : ¬ PendA node := by
  rintro ⟨i, k, m, h⟩
  have hmem' : (.recursive (m + 1) : FieldShape) ∈ node.h14.shapesAt i := by
    obtain ⟨hk, heq⟩ := (List.getElem?_eq_some_iff).mp h
    rw [← heq]; exact List.getElem_mem hk
  rcases (hGC node).1 i (.recursive (m + 1)) hmem' with h' | h'
  · exact FieldShape.noConfusion h'
  · injection h' with h''
    exact Nat.noConfusion h''

/-- Every `ClassGD` environment is D-dispatchable: a `PendD`-free group takes
the G arm; a group with a `PendD` node takes the D arm, with `¬ PendA` from
`GroupClassD`'s no-function-recursive clause and the class data from
`ClassGD` itself. So the guarded wrapper of §2 applies at every pure-D
environment. -/
theorem ddispatch_of_classGD (P : Premises4) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → ClassGD hW → DDispatch hW
  | _, .empty, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC => False.elim hC
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC => ddispatch_of_classGD P hE hC
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC => ddispatch_of_classGD P hE hC
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC => ddispatch_of_classGD P hE hC
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC =>
      ⟨ddispatch_of_classGD P hE hC.1, by
        cases P.dec (∃ node : RecNode E E' f rr rm, PendD node) with
        | isFalse hND => exact Or.inl fun node hD => hND ⟨node, hD⟩
        | isTrue hEx =>
            refine Or.inr ⟨hEx, fun node => not_pendA_of_groupClassD hC.2.1 node, hC.2.1, hC.2.2⟩⟩

/-- The admitted empty-type environment is in `ClassGD` — the tier-shaped
class at pure-D environments (bounds are the landed `falseEnvU_classG.2` /
`falseEnvUWfT_boundDG`). -/
theorem falseEnvU_classGD : ClassGD falseEnvUWfT := by
  refine ⟨trivial, fun node => ⟨?_, ?_, ?_⟩, fun _ => ⟨trivial, rfl, trivial⟩⟩
  · have h0 : node.a.constructors.length = 0 := node_ctors_length (ctors := []) node rfl
    exact fun i => absurd i.isLt (by omega)
  · have h0 : node.a.constructors.length = 0 := node_ctors_length (ctors := []) node rfl
    exact fun _ _ i => absurd i.isLt (by omega)
  · have h0 : node.a.constructors.length = 0 := node_ctors_length (ctors := []) node rfl
    exact fun i => absurd i.isLt (by omega)

/-- **Non-vacuity of the conditional tier, independent of `StepDHyp`**: at the
admitted empty-type environment the tier's conclusion holds unconditionally
via the landed `consistent4_GD` (class here, bounds landed). -/
theorem tierF3Concl_falseEnvU (P : Premises4) (K : Nat → Nat) (n : Nat) (e : Expr Nat)
    (h : HasTyT falseEnvU n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K h) : False :=
  consistent4_GD P K falseEnvUWfT falseEnvU_classGD (falseEnvU_classG.2 K)
    (falseEnvUWfT_boundDG K) rfl n e h hl

/-- The δ fixture is D-dispatchable — the guarded wrapper's D arm applies
there (via `ddispatch_of_classGD`). -/
theorem drEnvWfT_ddispatch (P : Premises4) : DDispatch drEnvWfT :=
  ddispatch_of_classGD P drEnvWfT drEnvWfT_classGD.1

/-- **`StepDHyp` is owed, not vacuous**: the δ fixture's group is a genuine
D-dispatch (D-dispatchable, with a real `PendD` node and no `PendA` node), so
the open arm of the wrapper is inhabited at a tree fixture. -/
theorem drEnvWfT_dArm_nonempty (P : Premises4) :
    DDispatch drEnvWfT ∧ ∃ node : DrNode, PendD node ∧ ¬ PendA node := by
  obtain ⟨node, _⟩ := group_nodeD (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)])
    (rr := 3) (rm := drRecMember) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl
    drMembersT
  exact ⟨ddispatch_of_classGD P drEnvWfT drEnvWfT_classGD.1, node, dr_pendD node, dr_not_pendA node⟩

end Rcic.F3.StepDMin
