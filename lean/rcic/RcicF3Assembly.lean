import rcic.RcicF3Cover
import rcic.RcicRiskTier

/-!
# F3 assembly: per-class step hypotheses over the coverage partition

`RcicF3Cover.rcicConsistentEmpty_of_covered` is generic over the step interface
`GInvSteps`. This module instantiates it at the coverage predicate `Covered`:
the step hypotheses are stated **per named class** of the coverage partition, in
the shape the class lanes discharge them — for every group node in the class,
the `gInv_group_of` node row (`NodeStepRow`: the fields-direct row, the
`AgreeAt` level bound along the walk, and the recursor package).

Named antecedents (nothing is silently assumed; `closure_claim = 0`):

- `PartitionSteps.stepA`   — class A (function-recursive fields; the KT lane).
- `PartitionSteps.stepB1`  — class B1 (`Prop` family, `anySort` elim, index
  reveal); conditional on the B1 bounded-rows discharge (RK-01/`SortUniq`
  territory).
- `PartitionSteps.stepD`   — class D (noncanonical `recursive 0` fields, the
  δ/β-reach lane; the merged `gInv_groupD`/`consistent4_GD` territory, named
  pending the ctx bridge + per-group class dispatch — see `PartitionSteps`.
- `PartitionSteps.stepW`   — class W nodes (`PendW`: the constructor walk's own
  parameter split differs from the recursor's family view); the GW lane's
  per-node rows.

`walkRec` is **retired, not named**: `RecursorEliminationAdmitted` now carries
`recursorMclass : m.mclass = .recursorM` (RcicInductivePolicy:241), so
`WalkRec hmem` follows from the membership derivation alone by
`walkRec_of_group` (RcicF3Layout:251) — the tag–mclass agreement
`IndGroupAdmitted.recursor` formerly left open is pinned at the admission
record, and the anomaly `WalkRec` detects is unrepresentable.

The level bound needs **no premise**: the conclusion is `TierF3`'s bounded
form, where `BoundG K hW`, `BoundDG K hW` and `LevelsBelow 4 K D`
(= `LOKt (fun _ => 0) 4 K D`) are caller antecedents. No step consumes sort
height above 4; `sound_conv_W4_any_K` (#8084, §5) makes `K`-overshoot benign at
height 4, so the caller's `K` flows through unchanged. `hBound` is gone.

The proved class G is instantiated inline: `nodeStepRow` decides the two
orthogonal axes per node — field class (`groupClassAt_of_notADB` when not
A/D/B; `recPkg_classG`'s `propEmpty_of_lim` branch discharges `PendC`, and
`PendC ∧ PendB` routes to `stepB1`) and walk agreement
(`walkAgree_of_walkClass`/`stepW`). Single members are class-independent:
`gInv_singleW` at `walkG_of_covered`.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The per-node obligations of `gInv_group_of`: the fields-direct row, the
`AgreeAt` level bound along the constructor walk, and the recursor package at
the group's `BoundG` row. Each class lane discharges this for its covered
nodes. -/
def NodeStepRow (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) : Prop :=
  (∀ i, RecFieldsDirect f (policyFamilyLevels node.a.family) node.a.family.parameters.length
      node.a.family.indices.length (node.a.constructorViews i).fields 0) ∧
  WalkAgree (AgreeAt node.a.family.parameters.length) hmem ∧
  (BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    ∀ (μ : Nat → List Nat → PSet.{4}), RecStepCtx P K fm node μ → RecPkg P μ K E' rr rm)

/-- The field half of `NodeStepRow`: the direct-fields row and the recursor
package. The walk agreement is supplied separately — `WalkClass` at proved
nodes, `stepW` at `PendW` nodes — so the field lanes do not promise the W
residue. -/
def NodeFieldRow (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) : Prop :=
  (∀ i, RecFieldsDirect f (policyFamilyLevels node.a.family) node.a.family.parameters.length
      node.a.family.indices.length (node.a.constructorViews i).fields 0) ∧
  (BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
    ∀ (μ : Nat → List Nat → PSet.{4}), RecStepCtx P K fm node μ → RecPkg P μ K E' rr rm)

/-- The per-class step hypotheses over the coverage partition. Each pending
class is a named antecedent in the shape its lane discharges. `walkRec` is
discharged, not named: `walkRec_of_group` derives `WalkRec hmem` from the
membership derivation alone, the admission record's `recursorMclass` field
having made the tag–mclass agreement provable at every cons.

Honesty notes (verified against the landed code; cc's 0615Z + 0630Z items):

- **Field class × walk agreement are orthogonal axes.** `nodeStepRow` decides
  them independently (`P.dec`): `PendA`/`PendD`/`PendB` route to the named
  field lanes; otherwise `groupClassAt_of_notADB` gives `GroupClassAt` and
  `recPkg_classG` supplies the package. `WalkClass` gives `WalkAgree` by
  `walkAgree_of_walkClass`; `PendW` is exactly `stepW`.
- **C is discharged, not named.** A `PendC` node that is not A/D/B-shaped is
  `GroupClassAt` — a family-mentioning field is `recursive 0` canonical, so
  `RecFieldsDirect` holds and `¬ PendB` gives index-freeness — and
  `recPkg_classG` discharges the package through its internal
  `propEmpty_of_lim` branch at `UniformProp`/`anySort` (`RcicF3MainG:830`). A
  node that is `PendC ∧ PendB` is index-revealed: it routes to `stepB1`, the
  B lane.
- **D is on main but stays named — glm's group-granular interface
  accepted** (their `1620Z` boundary message, verified against
  `RcicF3DMain:264`). `consistent4_GD` is `TierF3`-shaped at *env*
  granularity over `ClassGD` + `BoundG` + `BoundDG`, and `gInv_groupD`
  installs the family at its *normalized* data (`envCtxD`, `nodeFam`).
  Node granularity is wrong for D, not just the row type: routec's
  `gInv_group_ofAt` requires `∀ node i, RecFieldsDirect` for *every*
  node before `RecStepCtx`, so a group containing a PendD node never
  enters the generic group step at all — no per-node row is reachable.
  The accepted `stepD` target — **discharged verbatim on routec's
  umbrella @ `7088984faf`** (verified on FETCH_HEAD, `0320Z` glm):
  `gInv_groupD` (`RcicF3DMain:264` there) is retyped to exactly this
  signature, `GroupClassD` has lost its no-reveal clause (so `PendD ∧
  PendB` nodes are covered there), and the envCtxD role-parametric steps
  exist (`gInv_group_ofAtD`, `gInv_singleWD`, `GInvCtx`/`GInvAtCtx`;
  `RcicF3EqDMix`'s `gInvD_mix`/`consistent4_GDmix` at #8044 `4138287aed`):

  ```
  stepD : (∃ node, PendD node) → (∀ node, ¬ PendA node) →
    GroupClassD E E' f rr rm → (∀ node, WalkClass np hmem) →
    BoundG K (group …) → BoundDG K (group …) →
    GInvD P K hE → GInvD P K (group …)
  ```

  None of it is on `main`: this base's `gInv_groupD` still takes the
  env-granular `ClassGD` domain, `envCtxD_eq_envCtx_of_classG` /
  `gInv_group_ofAtD` / `gInv_singleWD` do not exist here, and `stepGrp`'s
  fold carries `GInv`/`envCtx` — so the group-granular field cannot be
  consumed (no `GInvD → GInv` boundary conversion) nor discharged (old
  `gInv_groupD` domain). Until the umbrella lands the field keeps the
  node-granular form below — unrealizable at true `recursive 0`
  noncanonical fields (`not_recFieldsDirect_of_noncanonical`, glm) —
  recording exactly the residue glm's interface replaces. **Named
  residue on this base:** `GroupClassD` keeps the no-reveal clause, so
  `PendD ∧ PendB` nodes stay uncovered; on the umbrella the clause is
  gone and that residue is closed. **Post-migration fit** (cc `0515Z`,
  verified on `1b0b519e20`): `readsOKAlong_envCtxDW` (`DRoles:351`)
  takes `WalkG hW` directly — `walkG_of_covered`'s output feeds
  `consistent4_GDmix` with no `ClassGD` anywhere; its group case reads
  the `WalkRec` conjunct via `group_layout_of_walkRec`, exactly what
  `walkRec_of_group` + the `recursorMclass` pin now supply.
- The named `stepW` is exactly the W lane's per-node obligation. The
  staged W-lane modules (`RcicF3WalkW`/`RcicF3CoverW`/`RcicF3PendWx`, with
  the env-level `ClassGW`/`consistent4_GW`/`gInv_groupW`) were removed from
  this branch (cc 10-26 11:10Z): they were `ClassGW`-flavored duplicates of
  the `WalkG`-flavored decls landed in `RcicF3MainG`/`RcicF3Layout`/
  `RcicF3FieldSmall`, and `RcicFamAppStepWLok` (main) rebuilt the `stepW`
  dischargers on those directly. The intended (#8084) reduction —
  `walkClassW_of_overshoot_rows`/`_of_scopeCheck`/`_of_inScope`/`_of_sortUnique`
  giving `WalkClassW` from `WalkRec hmem` plus the kernel rows
  `∀ N K, SortRowFieldLok σ N K E' arity` and
  `∀ N K, PiRowFieldOvershoot σ N K E' arity` (or `SortUnique`/`InScope`/
  `ScopeCheck` at the group env). Those rows are the RK-01 residue —
  `EnvWfT.ScopeCheck` is not free: its `isDrecD = false` conjunct fails
  for groups with direct-recursive fields, and `typedRowsWf`/`sortRow`/
  `piRow` producers route through `InScope`/`ScopeCheck`. #8048's
  `RcicFamAppRevB1Height4` supplies the famApp-side bounded rows
  (`TwinConvAt4OvershootK`/`RevSortLe`), not the sort/pi rows.
- `walkRec` is **discharged**: `GroupMembersT.cons` carries
  `hadm : IndGroupAdmitted E r m`, and `IndGroupAdmitted.recursor`'s
  payload `RecursorEliminationAdmitted` (RcicInductivePolicy:220) now
  pins the class tag — `recursorMclass : m.mclass = .recursorM`
  alongside `recursorArity`/`recursorType` — so every `.recursor`-tagged
  admission is *built* on a `recursorM` member and `walkRec_of_group`
  derives `WalkRec hmem` by per-cons induction on `hmem` alone. The
  placement choice (cc's 0100Z item): the record field touched 69
  builders in 40 files (mechanical `recursorMclass := rfl` appends, each
  loudly failing if untrue — plus a real `rm.mclass` check in the
  executable `buildRecAdmitted?`) versus ~80 sites for an
  `IndGroupAdmitted.recursor` argument (which would additionally have
  touched every `.recursor` match arm and distorted `∀ a`
  quantifications over the record).
  `walkRec_of_walkClass` remains for contexts already holding a
  `WalkClass` node.
- `NodeStepRow` presumes the `gInv_group_of` row, whose first component is
  `∀ i, RecFieldsDirect`. A genuine class-A node (a `recursive (m+1)` field)
  cannot satisfy it, and likewise class D. Those lanes' steps are therefore
  expected at group granularity (their own `gInv_groupX`-shaped theorems);
  when they land, `stepA`/`stepD` may be restated at that granularity — the
  node-row form here records what the generic dispatcher needs per node. -/
structure PartitionSteps (P : Premises4) (K : Nat → Nat) : Prop where
  /-- **A**: function-recursive fields (`recursive (m+1)`); the KT lane. -/
  stepA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendA node →
      NodeFieldRow P K hE hfam hctors hrec hmem node
  /-- **B1**: `Prop` family, `anySort` elim, a field revealed in result
  indices (including `PendC ∧ PendB` nodes); the B lane. The domain is the
  *pure*-B nodes the dispatcher actually sends: `¬ PendA`/`¬ PendD` are
  passed through because a `PendA ∧ PendB` node (`Acc.intro`: a revealed
  field plus a function-recursive one) routes to `stepA`, a `PendD ∧ PendB`
  node routes to `stepD`, and at either `NodeFieldRow.1`'s `∀ i,
  RecFieldsDirect` would fail — the B lane's row is provable only when
  every field is family-free or revealed-canonical. The first conjunct is
  discharged by the exported `recFieldsDirect_of_notAD` (RcicF3Cover).

  Rebase-time migration (cc/routec-sound @ `d570b060a7`, verified):
  `GroupClass` drops the `posOf=none` no-reveal clause — under `PropTel`
  every reconstructed index is `∅` regardless of revelation
  (`RcicF3PropIota`). When it reaches this base: `GroupClassAt` reduces to
  `∀ i, RecFieldsDirect` = `recFieldsDirect_of_notAD`,
  `groupClassAt_of_notADB`'s `hB` becomes unnecessary
  (`groupClassAt_of_notAD`), the `PendB` dispatch arm is removed, and
  `stepB1` retires entirely — `¬PendA ∧ ¬PendD` nodes are proved-class
  regardless of `PendB`, the same collapse `stepC` took.

  glm-f3eq status (checked `glm/rcic-f3-eq-model` @ `8721b35d60`):
  `stepB1_of_recFieldsDirect` **landed** at `7d83dc9652`, premise-free —
  `⟨hrf, fun hB μ X => recPkg_classG P K node (hB.2.2.2 node) X⟩`,
  discharging `NodeFieldRow` from `RecFieldsDirect` alone (the exported
  `recFieldsDirect_of_notAD` supplies the input). It typechecks only on
  the `d570b060a7` widened-`GroupClass` base (`recPkg_classG` there takes
  no `hpf`); on this base it is exactly the migration recipe above —
  `stepB1` retires when `d570b060a7` reaches `main` (194 unlanded
  lane commits — not mergeable into this PR without pulling cc's whole
  lane). Their older `recPkg_rev`/`gInv_group_rev` path was conditional
  on `RevIdxAgreeG`; this one is not.

  glm's measured merge dry-run (their `1530Z`, kept local): onto `d570`
  this branch breaks at `RcicF3Cover:199` (`groupClass_iff_at`'s
  `Iff.rfl`), `RcicF3Cover:359` (`hC.2.1 node` shape), and `nodeStepRow`'s
  `recPkg_classG … hG.2 …` old-arity call; dupdecls to resolve:
  `group_layout_of_walkRec` (Layout↔WalkW), `occursConst_false_of_contains`
  (Cover↔WhnfSyn), `readsOKAlong_envCtxW` (MainG↔WalkW),
  `walkAgree_of_walkClass` (Layout↔WalkW). Their suggested wiring if
  `stepB1` is kept rather than retired:
  `stepB1_of_recFieldsDirect P K hE hfam hctors hrec hmem node
    (recFieldsDirect_of_notAD P node hA hD)`. -/
  stepB1 : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendB node → ¬ PendA node → ¬ PendD node →
      NodeFieldRow P K hE hfam hctors hrec hmem node
  /-- **D**: noncanonical `recursive 0` fields (reached through δ/β). The
  dispatched domain is `PendD ∧ ¬ PendA` (a `PendA ∧ PendD` node routes to
  `stepA`); `¬ PendA` is passed through for the same `RecFieldsDirect`
  reason as `stepB1`. **Interim form**: glm's accepted group-granular
  `stepD` (see the `PartitionSteps` doc bullet) replaces this field once
  the `envCtxD`/`GInvD` dispatcher migration lands — a genuine PendD
  node cannot satisfy `NodeFieldRow.1`. -/
  stepD : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendD node → ¬ PendA node →
      NodeFieldRow P K hE hfam hctors hrec hmem node
  /-- **W**: the `AgreeAt` level-agreement row for a node whose constructor
  walk splits off a different parameter count (`PendW`). This is exactly the
  GW lane's `∀ node, WalkAgree (AgreeAt np) hmem` obligation at a
  `¬ WalkClass` node; the fields-direct and package components come from the
  node's field-class (proved machinery when it is `GroupClassAt`). On #8084
  this reduces to `SortUniqueLok` + `BothViewsBoundedAt`. -/
  stepW : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendW hmem node →
      WalkAgree (AgreeAt node.a.family.parameters.length) hmem

/-- Per-node dispatch over the two orthogonal axes: the **field class**
(`PendA`/`PendD`/`PendB` → the named lanes; otherwise `GroupClassAt` by
`groupClassAt_of_notADB`, with `recPkg_classG` — whose `propEmpty_of_lim`
branch discharges `PendC` — for the package) and the **walk agreement**
(`WalkClass` → `walkAgree_of_walkClass`; `PendW` → `stepW`). The axes are
re-decided by `P.dec`, so `NodeCovered`'s Prop is not needed — every node gets
a row. -/
theorem nodeStepRow (P : Premises4) (K : Nat → Nat) (steps : PartitionSteps P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) :
    NodeStepRow P K hE hfam hctors hrec hmem node := by
  have hAg : WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
    cases P.dec (WalkClass node.a.family.parameters.length hmem) with
    | isTrue hw => exact walkAgree_of_walkClass node hmem hw
    | isFalse hw => exact steps.stepW hE hfam hctors hrec hmem node hw
  cases P.dec (PendA node) with
  | isTrue hA =>
      have hr := steps.stepA hE hfam hctors hrec hmem node hA
      exact ⟨hr.1, hAg, hr.2⟩
  | isFalse hA =>
  cases P.dec (PendD node) with
  | isTrue hD =>
      have hr := steps.stepD hE hfam hctors hrec hmem node hD hA
      exact ⟨hr.1, hAg, hr.2⟩
  | isFalse hD =>
  cases P.dec (PendB node) with
  | isTrue hB =>
      have hr := steps.stepB1 hE hfam hctors hrec hmem node hB hA hD
      exact ⟨hr.1, hAg, hr.2⟩
  | isFalse hB =>
      have hG := groupClassAt_of_notADB P node hA hD hB
      exact ⟨hG.1, hAg, fun hBB μ X => recPkg_classG P K node hG.2 (hBB.2.2.2 node) X⟩

/-- The covered-environment walk: `WalkG` from the partition steps. Every
group's `WalkRec` is derived by `walkRec_of_group` from the admission pin;
every node's `AgreeAt` row is its class's step row. -/
theorem walkG_of_covered (P : Premises4) (K : Nat → Nat) (steps : PartitionSteps P K) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → Covered hW → WalkG hW
  | _, .empty, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC => hC
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC => walkG_of_covered P K steps hE hC
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC => walkG_of_covered P K steps hE hC
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC => walkG_of_covered P K steps hE hC
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC =>
      ⟨walkG_of_covered P K steps hE hC.1, walkRec_of_group hmem,
        fun node => (nodeStepRow P K steps hE hfam hctors hrec hmem node).2.1⟩

/-- The `Covered` instance of the step interface. Singles are
class-independent (`gInv_singleW` at `walkG_of_covered`); the group step
dispatches each node to its class's row and calls `gInv_group_of`. -/
theorem steps_covered (P : Premises4) (K : Nat → Nat) (steps : PartitionSteps P K) :
    GInvSteps P K (fun {E} (hW : EnvWfT E) => Covered hW)
      (fun {E} (hW : EnvWfT E) => BoundG K hW) where
  stepDef := fun E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, hB.1, fun IH => gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.2
      (walkG_of_covered P K steps hE hC) IH⟩
  stepThm := fun E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, hB.1, fun IH => gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp hB.2
      (walkG_of_covered P K steps hE hC) IH⟩
  stepOpq := fun E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, hB.1, fun IH => gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.2
      (walkG_of_covered P K steps hE hC) IH⟩
  stepGrp := fun E f fm ctors rr rm E' hE hfam hctors hrec hmem hC hB =>
    ⟨hC.1, hB.1, fun IH =>
      gInv_group_of P K hE hfam hctors hrec hmem
        (fun node i => (nodeStepRow P K steps hE hfam hctors hrec hmem node).1 i)
        (walkRec_of_group hmem)
        (fun node => (nodeStepRow P K steps hE hfam hctors hrec hmem node).2.1)
        hB.2.1 hB.2.2.1
        (fun node μ X => (nodeStepRow P K steps hE hfam hctors hrec hmem node).2.2 hB μ X)
        IH⟩

/-- **Assembly over the coverage partition — the bounded `TierF3` form.**
Per-class step hypotheses (the proved class G and C inline; A, B1, D, W and the
PendWx `WalkRec` residue as the named fields of `PartitionSteps`) give the
height-4 bounded consistency for every axiom-free admitted environment. The
unbounded `RcicConsistentEmpty` conclusion is superseded: `BoundG K hW`,
`BoundDG K hW` (the tier's declared bound for class D) and
`LevelsBelow 4 K D` are the tier's own antecedents, so `hBound` is gone — no
premise needs sort height above 4. The model's final step is discharged
generically: `walkG_of_covered` supplies the reads-ok row, then
`faithfulR_envμR`/`envSound_of`/`empty_of_falseRec` as in the class-G
instance.

Target: `Rcic.Apex.TierF3Uncond` — `FamAppConvInjAll` is bound by nothing in
the landed or assembly proof graph (here it was `_hF`), so it drops out of
the statement entirely. The exact remaining named premises are the
`PartitionSteps` fields: `stepA` (class A), `stepD` (class D — glm's
accepted group-granular interface, gated on the `RcicF3EqDBridge`
`envCtxD`/`GInvD` migration + fable-f3d's `gInv_groupD` retype; the
`GroupClassD` no-reveal clause leaves `PendD ∧ PendB` uncovered),
`stepB1` (B1 — discharge-ready via glm's premise-free
`stepB1_of_recFieldsDirect`; retires entirely once the `d570b060a7`
`GroupClass` reaches this base), and `stepW` (PendW `WalkAgree` — RK-01
kernel rows `SortRowFieldLok`/`PiRowFieldOvershoot` at `E'`).
`walkRec` is gone from the list: `walkRec_of_group` derives it from
`hmem` now that `RecursorEliminationAdmitted.recursorMclass` pins the
tag–mclass agreement at the admission record. -/
theorem tierF3Uncond_of_partition (steps : ∀ (P : Premises4) (K : Nat → Nat), PartitionSteps P K) :
    Rcic.Apex.TierF3Uncond := by
  intro P K E hW hB _hBDG hAx _h0 h1 n e D hLOK
  have hC : Covered hW := EnvWfT_axiomFree_covered P hW hAx
  have hI : GInv P K hW := gInv_of_steps P K _ _ (steps_covered P K (steps P K))
    (fun _ _ _ _ _ _ _ _ _ hCx => hCx) hW hC hB
  have hRA := readsOKAlong_envCtxW hW (walkG_of_covered P K (steps P K) hW hC)
    (envCtx hW) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtx hW) hW hRA).1
  have hIv := hI (envCtx hW) (fun _ _ => rfl) _ hF
  have hES := envSound_of P (Efin := E) (fun _ _ h => h) hIv.1
    (fun r m hm hk => hIv.2 E (fun _ _ h => h) r m hm hk) (fun _ => 0) n
  exact empty_of_falseRec P (hIv.1 1 _ h1) (sound_ty (P.good _ rfl) hES D hLOK ρ0 trivial)

/-- The conditional tier follows: `FamAppConvInjAll` is never consumed. -/
theorem tierF3_of_partition (steps : ∀ (P : Premises4) (K : Nat → Nat), PartitionSteps P K) :
    Rcic.Apex.TierF3 :=
  Rcic.Apex.tierF3_of_tierF3Uncond (tierF3Uncond_of_partition steps)

/-- The full unconditional kernel tier: F1 closed plus F3 modulo the same
named `PartitionSteps` rows. -/
theorem kernelSoundnessTierUncond_of_partition
    (steps : ∀ (P : Premises4) (K : Nat → Nat), PartitionSteps P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  ⟨Rcic.Apex.tierF1, tierF3Uncond_of_partition steps⟩

end PSet

end Rcic.F3

#print axioms Rcic.F3.PSet.NodeStepRow
#print axioms Rcic.F3.PSet.nodeStepRow
#print axioms Rcic.F3.PSet.walkG_of_covered
#print axioms Rcic.F3.PSet.steps_covered
#print axioms Rcic.F3.PSet.tierF3Uncond_of_partition
#print axioms Rcic.F3.PSet.tierF3_of_partition
#print axioms Rcic.F3.PSet.kernelSoundnessTierUncond_of_partition
