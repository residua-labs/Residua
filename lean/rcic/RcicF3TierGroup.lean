import rcic.RcicF3StepB1
import rcic.RcicF3EqStepDMin
import rcic.RcicF3NatFixture
import rcic.RcicTypedFunRecPins

/-!
# F3 tier assembly at GROUP granularity — the inhabitable partition record

`closure_claim = 0`.

## Why a new record

swe-audit-m3's premise inventory (#8231, `research/rcic/TIER_PREMISES.md`) and
glm-f3eq's #8234 measured that the node-granular records `PartitionSteps`
(`RcicF3Assembly`), `PartitionStepsABD` (`RcicF3StepWMin`, #8222) and
`PartitionStepsAD` (`RcicF3StepB1`, #8233) are **uninhabitable**: their
`stepA`/`stepD` fields owe `NodeFieldRow.1` (`∀ i, RecFieldsDirect`) at `PendA`/
`PendD` nodes, and those shapes are *defined* by the failure of exactly that row
(refuted at `wEnv` and at `drEnv`). Every wrapper over them is vacuous —
including #8233's `tierF3Uncond_of_AD_hyp`, which this module supersedes.

## The restated record (§1–§3)

The landed class results deliver at **group** granularity — the generic fold
`gInv_of_steps` consumes a group step `GInv hE → GInv group`, and the landed D
model (`gInv_groupD`) is a group step. So the A and D antecedents are restated
there:

* `GroupStepAt P K <group>` — the fold's group step at one group: given the
  walk agreement of every node (supplied by the W face, independently of the
  field class), `BoundG` and `BoundDG` of the group (both tier antecedents),
  `GInv hE → GInv group`. Purely semantic: no syntactic row is owed.
* `StepAG P K` — `GroupStepAt` at every group with a `PendA` node.
* `StepDG P K` — `GroupStepAt` at every group with a `PendD` node and no `PendA`
  node. **No class guard**: unlike glm's `StepDHyp` (#8234: `GroupClassD ∧
  WalkClass`, with the `DDispatch` side condition), every `PendD` group is in
  the domain — nothing is narrowed; glm's corners (D outside `GroupClassD`, D
  with `PendW`) are inside `StepDG` as owed debt (`stepDG_of_stepDHyp` is the
  comparison on glm's subdomain).
* `StepWField` — the node-granular W row (`PartitionSteps.stepW`'s type); its
  suppliers are `StepWMin.stepW_of_hyp` (#8222, `StepWHyp`) and #8235's
  `stepW_of_checked` (`StepWChecked`), either plugs in verbatim.
* `PartitionStepsG P K := {stepA : StepAG, stepD : StepDG, stepW : StepWField}`.

**`stepB1` is not a field: it is proved.** Every group with neither a `PendA`
nor a `PendD` node takes the landed `gInv_group_of` with #8233's
`nodeFieldRow_of_notAD` rows (`recPkg_classB`, the package without the
no-reveal clause) — `gInv_group_noAD` / `groupStepAt_of_noAD`, unconditional.
That covers class G, C and B1 at once.

## The tier (§3)

`tierF3Uncond_of_partitionStepsG`, `tierF3Uncond_of_AD_W` (W from `StepWHyp`),
`kernelSoundnessTierUncond_of_AD_W` — the landed tail (`readsOKAlong_envCtxW`
→ `faithfulR_envμR` → `envSound_of` → `empty_of_falseRec`, factored as
`false_of_walkG_gInv`).

## Never narrower than the old face (§4)

`partitionStepsG_of_partitionSteps`: the old record implies the new one (its
node rows assemble to the group step by the landed `nodeStepRow` +
`gInv_group_of`). The restatement only weakens the antecedent.

## Inhabitability, and m3's probes re-run (§5–§6)

* The A/D-free part is **inhabited outright**: `gInv_of_noAD` /
  `consistent4_noAD` give the model invariant / height-4 consistency at every
  A/D-free environment with walk agreement — strictly beyond `ClassG` (B1/C
  groups included) — and `tierConcl_falseEnvU_noAD` runs it end-to-end at the
  admitted empty-type environment with no premise.
* **D at the δ fixture** (`drEnv`, where m3 refuted node-granular `stepD`): the
  guard of `StepDG` holds (`drGroup_dArm`), every input of `GroupStepAt` is
  supplied there (`drAgree`, `drEnvWfT_classGD`, `gInv_drBase`), so the field
  *is exactly* the model invariant there: `stepDAt_drEnv_iff : GroupStepAt …
  drEnv ↔ GInv P K drEnvWfT`. Its normalized-role twin is **proved**
  (`gInvD_drEnv`, landed `gInvD`). The m3 mechanism (a syntactic row failing) has
  nothing to bite on; a refutation of the new field at `drEnv` would have to be
  a refutation of `GInv P K drEnvWfT` itself. The exact remaining content at the
  fixture is the role bridge `DrRoleBridge P K := GInvD P K drEnvWfT → GInv P K
  drEnvWfT` (`stepDAt_drEnv_of_bridge`).
* **A at the function-recursive fixture** (`wEnv`, where m3 refuted
  node-granular `stepA`): the guard holds (`wGroup_aArm`, m3's probe lemmas
  ported, `w_*`), and the field reduces to the model invariant there given the
  walk/bound data (`gInv_wEnv_of_stepAAt`, with the base invariant
  `gInv_natEnvU` proved); `stepAAt_of_gInv` is the converse. Again no syntactic
  row is owed.
* W: unchanged node-granular field — m3: inhabited at `eqWNode`'s open arm
  (`eqW_stepW`), in-scope at `pwEnvWfT` (`stepW_pwEnv`); not refuted.

## The exact open debts on this face

`StepAG` (class A group step — the KT lane's `RecGroupA`/`recVal_mem_rec_KT`
deliver the recursor's membership at the KT table, not yet the group step at
the fold's `envCtx` roles), `StepDG` (class D group step — `gInv_groupD`
delivers it at `envCtxD` for `ClassGD` envs; open: the `envCtx`/`envCtxD`
bridge and the non-`ClassGD` D groups), and the W field. Nothing else.

Axioms of every sealed declaration ⊆ {`propext`, `Quot.sound`}; all case splits
on `Premises4.dec`.
-/

set_option autoImplicit false

namespace Rcic.F3.TierGroup

open Rcic.Declarative Rcic.F3 Rcic.F3.PSet

/-! ## §1 the group-granular step -/

/-- **The fold's group step at one group**: with the walk agreement of every
node, the group's `BoundG` and `BoundDG`, the model invariant passes from the
base to the group. -/
def GroupStepAt (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') : Prop :=
  (∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem) →
  BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
  GInv P K hE → GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-- **A, group-granular**: the group step at every group with a function-recursive
node. -/
def StepAG (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    (∃ node : RecNode E E' f rr rm, PendA node) → GroupStepAt P K hE hfam hctors hrec hmem

/-- **D, group-granular**: the group step at every group with a noncanonical
`recursive 0` node and no function-recursive node. No class guard. -/
def StepDG (P : Premises4) (K : Nat → Nat) : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
    (∀ node : RecNode E E' f rr rm, ¬ PendA node) → (∃ node : RecNode E E' f rr rm, PendD node) →
    GroupStepAt P K hE hfam hctors hrec hmem

/-- **W**: the node-granular `AgreeAt` row at `PendW` nodes — exactly the type of
`PartitionSteps.stepW`. -/
def StepWField : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm), PendW hmem node →
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem

/-- **The restated partition record**: A and D at group granularity, W at node
granularity. B1 (with G and C) is not a field — `gInv_group_noAD` proves it. -/
structure PartitionStepsG (P : Premises4) (K : Nat → Nat) : Prop where
  /-- **A**: groups with a function-recursive (`recursive (m+1)`) node. -/
  stepA : StepAG P K
  /-- **D**: groups with a noncanonical `recursive 0` node and no `PendA` node. -/
  stepD : StepDG P K
  /-- **W**: the `AgreeAt` row at `PendW` nodes. -/
  stepW : StepWField

/-! ## §2 the dispatch -/

/-- Every node's walk agreement from the W field: `WalkClass` by the landed
`walkAgree_of_walkClass`, `PendW` by the field. -/
theorem walkAgree_of_stepW (P : Premises4) (hW : StepWField)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
  cases P.dec (WalkClass node.a.family.parameters.length hmem) with
  | isTrue hw => exact walkAgree_of_walkClass node hmem hw
  | isFalse hw => exact hW hE hfam hctors hrec hmem node hw

/-- **The A/D-free group step, proved** (G, C and B1 at once): every node's row is
#8233's `nodeFieldRow_of_notAD` (`recPkg_classB` for the package), and the
landed `gInv_group_of` assembles them. -/
theorem gInv_group_noAD (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hNA : ∀ node : RecNode E E' f rr rm, ¬ PendA node)
    (hND : ∀ node : RecNode E E' f rr rm, ¬ PendD node)
    (hAg : ∀ node : RecNode E E' f rr rm, WalkAgree (AgreeAt node.a.family.parameters.length) hmem)
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (IH : GInv P K hE) :
    GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) :=
  gInv_group_of P K hE hfam hctors hrec hmem
    (fun node => (StepB1.nodeFieldRow_of_notAD P K hE hfam hctors hrec hmem node (hNA node) (hND node)).1)
    (walkRec_of_group hmem) hAg hB.2.1 hB.2.2.1
    (fun node μ X =>
      (StepB1.nodeFieldRow_of_notAD P K hE hfam hctors hrec hmem node (hNA node) (hND node)).2 hB μ X)
    IH

/-- `gInv_group_noAD` in the `GroupStepAt` shape. -/
theorem groupStepAt_of_noAD (P : Premises4) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hNA : ∀ node : RecNode E E' f rr rm, ¬ PendA node)
    (hND : ∀ node : RecNode E E' f rr rm, ¬ PendD node) :
    GroupStepAt P K hE hfam hctors hrec hmem :=
  fun hAg hB _ IH => gInv_group_noAD P K hE hfam hctors hrec hmem hNA hND hAg hB IH

/-- **Group dispatch** over the three-way partition of groups (decided by
`Premises4.dec`): a `PendA` node → `StepAG`; else a `PendD` node → `StepDG`; else
the proved `groupStepAt_of_noAD`. Every group is covered; none is excluded. -/
theorem groupStepAt_of_AD (P : Premises4) (K : Nat → Nat) (hA : StepAG P K) (hD : StepDG P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    GroupStepAt P K hE hfam hctors hrec hmem := by
  cases P.dec (∃ node : RecNode E E' f rr rm, PendA node) with
  | isTrue hxA => exact hA hE hfam hctors hrec hmem hxA
  | isFalse hxA =>
    cases P.dec (∃ node : RecNode E E' f rr rm, PendD node) with
    | isTrue hxD => exact hD hE hfam hctors hrec hmem (fun node h => hxA ⟨node, h⟩) hxD
    | isFalse hxD =>
        exact groupStepAt_of_noAD P K hE hfam hctors hrec hmem (fun node h => hxA ⟨node, h⟩)
          (fun node h => hxD ⟨node, h⟩)

/-- The covered-environment walk from the W field alone (field class plays no
role in walk agreement). -/
theorem walkG_of_stepW (P : Premises4) (hW : StepWField) :
    {E : ResolvedEnv} → (hE : EnvWfT E) → Covered hE → WalkG hE
  | _, .empty, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC => hC
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC => walkG_of_stepW P hW hE hC
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC => walkG_of_stepW P hW hE hC
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC => walkG_of_stepW P hW hE hC
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC =>
      ⟨walkG_of_stepW P hW hE hC.1, walkRec_of_group hmem,
        walkAgree_of_stepW P hW hE hfam hctors hrec hmem⟩

/-! ## §3 the fold and the tier -/

/-- The step interface of the generic fold at the coverage class, with the bound
`BoundG ∧ BoundDG` (both tier antecedents). -/
theorem gInvSteps_of_partitionStepsG (P : Premises4) (K : Nat → Nat) (S : PartitionStepsG P K) :
    GInvSteps P K (fun {E : ResolvedEnv} (hW : EnvWfT E) => Covered hW)
      (fun {E : ResolvedEnv} (hW : EnvWfT E) => BoundG K hW ∧ BoundDG K hW) where
  stepDef := fun E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.1.2
      (walkG_of_stepW P S.stepW hE hC) IH⟩
  stepThm := fun E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp
      hB.1.2 (walkG_of_stepW P S.stepW hE hC) IH⟩
  stepOpq := fun E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, ⟨hB.1.1, hB.2⟩, fun IH => gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv
      hB.1.2 (walkG_of_stepW P S.stepW hE hC) IH⟩
  stepGrp := fun E f fm ctors rr rm E' hE hfam hctors hrec hmem hC hB =>
    ⟨hC.1, ⟨hB.1.1, hB.2.1⟩, fun IH =>
      groupStepAt_of_AD P K S.stepA S.stepD hE hfam hctors hrec hmem
        (walkAgree_of_stepW P S.stepW hE hfam hctors hrec hmem) hB.1 hB.2 IH⟩

/-- The model invariant at every covered environment within the bounds. -/
theorem gInv_of_partitionStepsG (P : Premises4) (K : Nat → Nat) (S : PartitionStepsG P K)
    {E : ResolvedEnv} (hW : EnvWfT E) (hC : Covered hW) (hB : BoundG K hW) (hD : BoundDG K hW) :
    GInv P K hW :=
  gInv_of_steps P K _ _ (gInvSteps_of_partitionStepsG P K S) (fun _ _ _ _ _ _ _ _ _ hCx => hCx) hW hC ⟨hB, hD⟩

/-- The landed tail, factored: the walk and the model invariant give height-4
consistency at an environment whose member 1 is the empty type's recursor. -/
theorem false_of_walkG_gInv (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E)
    (hWk : WalkG hW) (hI : GInv P K hW) (h1 : E.members 1 = some falseRecMemberU) (n : Nat)
    (e : Expr Nat) (D : HasTyT E n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K D) : False := by
  have hRA := readsOKAlong_envCtxW hW hWk (envCtx hW) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtx hW) hW hRA).1
  have hIv := hI (envCtx hW) (fun _ _ => rfl) _ hF
  have hES := envSound_of P (Efin := E) (fun _ _ h => h) hIv.1
    (fun r m hm hk => hIv.2 E (fun _ _ h => h) r m hm hk) (fun _ => 0) n
  exact empty_of_falseRec P (hIv.1 1 _ h1) (sound_ty (P.good _ rfl) hES D hl ρ0 trivial)

/-- **The tier from the group-granular record.** -/
theorem tierF3Uncond_of_partitionStepsG
    (steps : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsG P K) :
    Rcic.Apex.TierF3Uncond := by
  intro P K E hW hB hBDG hAx _h0 h1 n e D hLOK
  have hC : Covered hW := EnvWfT_axiomFree_covered P hW hAx
  exact false_of_walkG_gInv P K hW (walkG_of_stepW P (steps P K).stepW hW hC)
    (gInv_of_partitionStepsG P K (steps P K) hW hC hB hBDG) h1 n e D hLOK

/-- The record from the A and D group steps and glm's `StepWHyp` (#8222): the W
field is built by `StepWMin.stepW_of_hyp`. -/
theorem partitionStepsG_of_hyp (P : Premises4) (K : Nat → Nat) (h : StepWMin.StepWHyp)
    (hA : StepAG P K) (hD : StepDG P K) : PartitionStepsG P K where
  stepA := hA
  stepD := hD
  stepW := fun hE hfam hctors hrec hmem node hPend =>
    StepWMin.stepW_of_hyp P h hE hfam hctors hrec hmem node hPend

/-- **The tier, conditional on exactly the A and D group steps and `StepWHyp`.** -/
theorem tierF3Uncond_of_AD_W (h : StepWMin.StepWHyp)
    (hA : ∀ (P : Premises4) (K : Nat → Nat), StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), StepDG P K) :
    Rcic.Apex.TierF3Uncond :=
  tierF3Uncond_of_partitionStepsG fun P K => partitionStepsG_of_hyp P K h (hA P K) (hD P K)

/-- The conditional tier follows (`FamAppConvInjAll` is never consumed). -/
theorem tierF3_of_AD_W (h : StepWMin.StepWHyp)
    (hA : ∀ (P : Premises4) (K : Nat → Nat), StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), StepDG P K) :
    Rcic.Apex.TierF3 :=
  Rcic.Apex.tierF3_of_tierF3Uncond (tierF3Uncond_of_AD_W h hA hD)

/-- The full kernel tier (F1 closed; F3 modulo the A/D group steps and `StepWHyp`). -/
theorem kernelSoundnessTierUncond_of_AD_W (h : StepWMin.StepWHyp)
    (hA : ∀ (P : Premises4) (K : Nat → Nat), StepAG P K)
    (hD : ∀ (P : Premises4) (K : Nat → Nat), StepDG P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  ⟨Rcic.Apex.tierF1, tierF3Uncond_of_AD_W h hA hD⟩

/-! ## §4 never narrower than the old face; comparison with glm's `StepDHyp` -/

/-- The old node rows assemble to the group step at every group (landed
`nodeStepRow` + `gInv_group_of`). -/
theorem groupStepAt_of_partitionSteps {P : Premises4} {K : Nat → Nat} (steps : PartitionSteps P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    GroupStepAt P K hE hfam hctors hrec hmem :=
  fun _ hB _ IH =>
    gInv_group_of P K hE hfam hctors hrec hmem
      (fun node i => (nodeStepRow P K steps hE hfam hctors hrec hmem node).1 i)
      (walkRec_of_group hmem)
      (fun node => (nodeStepRow P K steps hE hfam hctors hrec hmem node).2.1)
      hB.2.1 hB.2.2.1
      (fun node μ X => (nodeStepRow P K steps hE hfam hctors hrec hmem node).2.2 hB μ X)
      IH

/-- **The restatement only weakens the antecedent**: the old record implies the
new one. -/
theorem partitionStepsG_of_partitionSteps {P : Premises4} {K : Nat → Nat}
    (steps : PartitionSteps P K) : PartitionStepsG P K where
  stepA := fun hE hfam hctors hrec hmem _ => groupStepAt_of_partitionSteps steps hE hfam hctors hrec hmem
  stepD := fun hE hfam hctors hrec hmem _ _ => groupStepAt_of_partitionSteps steps hE hfam hctors hrec hmem
  stepW := steps.stepW

/-- glm's `StepDHyp` (#8234) gives `StepDG`'s group step on glm's subdomain
(`GroupClassD ∧ WalkClass`); outside it `StepDG` is owed and `StepDHyp` is
silent — the corners `DDispatch` excludes are inside `StepDG`. -/
theorem stepDG_of_stepDHyp {P : Premises4} {K : Nat → Nat} (h : StepDMin.StepDHyp P K)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hNA : ∀ node : RecNode E E' f rr rm, ¬ PendA node) (hxD : ∃ node : RecNode E E' f rr rm, PendD node)
    (hGC : GroupClassD E E' f rr rm)
    (hWC : ∀ node : RecNode E E' f rr rm, WalkClass node.a.family.parameters.length hmem) :
    GroupStepAt P K hE hfam hctors hrec hmem :=
  fun _ hB hBDG IH => h hE hfam hctors hrec hmem hNA hxD hGC hWC hB hBDG IH

/-- Any group at which the model invariant holds satisfies the group step: the
field's content is semantic only. -/
theorem stepAt_of_gInv {P : Premises4} {K : Nat → Nat}
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (h : GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)) :
    GroupStepAt P K hE hfam hctors hrec hmem :=
  fun _ _ _ _ => h

/-! ## §5 the A/D-free part is inhabited outright -/

/-- Environments every group of which has no `PendA` and no `PendD` node (axioms
excluded, as in `Covered`). Strictly larger than `ClassG`'s field condition:
`PendB`/`PendC` groups are in. -/
def NoAD : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ _ _ _ _ _ => False
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => NoAD hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => NoAD hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => NoAD hE
  | _, .group E f _ _ rr rm E' hE _ _ _ _ =>
      NoAD hE ∧ ∀ node : RecNode E E' f rr rm, ¬ PendA node ∧ ¬ PendD node

/-- **The model invariant at every A/D-free environment** with walk agreement and
`BoundG` — no named premise. -/
theorem gInv_of_noAD (P : Premises4) (K : Nat → Nat) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → NoAD hW → WalkG hW → BoundG K hW → GInv P K hW
  | _, .empty, _, _, _ => fun _ _ _ _ =>
      ⟨fun _ _ h => (Option.noConfusion h), fun _ _ _ _ h => (Option.noConfusion h)⟩
  | _, .axiom _ _ _ _ _ _ _ _ _, hN, _, _ => hN.elim
  | _, .definition _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv, hN, hWk, hB =>
      gInv_singleW P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.2 hWk
        (gInv_of_noAD P K hE hN hWk hB.1)
  | _, .thm _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp, hN, hWk, hB =>
      gInv_singleW P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp hB.2 hWk
        (gInv_of_noAD P K hE hN hWk hB.1)
  | _, .opaque _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv, hN, hWk, hB =>
      gInv_singleW P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.2 hWk
        (gInv_of_noAD P K hE hN hWk hB.1)
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem, hN, hWk, hB =>
      gInv_group_noAD P K hE hfam hctors hrec hmem (fun node => (hN.2 node).1) (fun node => (hN.2 node).2)
        hWk.2.2 hB (gInv_of_noAD P K hE hN.1 hWk.1 hB.1)

/-- **Height-4 consistency at every A/D-free environment** with walk agreement. -/
theorem consistent4_noAD (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E)
    (hN : NoAD hW) (hWk : WalkG hW) (hB : BoundG K hW) (h1 : E.members 1 = some falseRecMemberU)
    (n : Nat) (e : Expr Nat) (D : HasTyT E n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K D) : False :=
  false_of_walkG_gInv P K hW hWk (gInv_of_noAD P K hW hN hWk hB) h1 n e D hl

/-- The admitted empty-type environment is A/D-free (its group has no
constructor). -/
theorem falseEnvU_noAD : NoAD falseEnvUWfT := by
  refine ⟨trivial, fun node => ⟨?_, ?_⟩⟩
  · rintro ⟨i, _, _, _⟩
    have h0 : node.a.constructors.length = 0 := node_ctors_length (ctors := []) node rfl
    exact absurd i.isLt (by omega)
  · rintro ⟨i, _, _, _, _, _⟩
    have h0 : node.a.constructors.length = 0 := node_ctors_length (ctors := []) node rfl
    exact absurd i.isLt (by omega)

/-- **The restated face runs end-to-end at a tier environment with no premise**:
the admitted empty-type environment, via `consistent4_noAD`. -/
theorem tierConcl_falseEnvU_noAD (P : Premises4) (K : Nat → Nat) (n : Nat) (e : Expr Nat)
    (D : HasTyT falseEnvU n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K D) : False :=
  consistent4_noAD P K falseEnvUWfT falseEnvU_noAD (walkG_of_classG falseEnvUWfT falseEnvU_classG.1)
    (falseEnvU_classG.2 K) rfl n e D hl

/-! ## §6 m3's probes re-run against the new face -/

/-! ### D at the δ fixture `drEnv` -/

/-- The δ fixture's group is in `StepDG`'s domain: no `PendA` node, a `PendD`
node (glm's `dr_not_pendA`/`dr_pendD`). -/
theorem drGroup_dArm : (∀ node : DrNode, ¬ PendA node) ∧ ∃ node : DrNode, PendD node := by
  obtain ⟨node, _⟩ := group_nodeD (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)])
    (rr := 3) (rm := drRecMember) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl
    drMembersT
  exact ⟨StepDMin.dr_not_pendA, node, StepDMin.dr_pendD node⟩

/-- The base of the δ fixture (`Id` alone) carries the model invariant at every
bound. -/
theorem gInv_drBase (P : Premises4) (K : Nat → Nat) : GInv P K drBaseWfT :=
  gInv P K drBaseWfT trivial (drEnvWfT_classGD.2 K).1.1

/-- Every node of the δ fixture has walk agreement (`WalkClass`, from `ClassGD`). -/
theorem drAgree : ∀ node : DrNode, WalkAgree (AgreeAt node.a.family.parameters.length) drMembersT :=
  fun node => walkAgree_of_walkClass node drMembersT (drEnvWfT_classGD.1.2.2 node)

/-- **`StepDG` at the δ fixture is exactly the model invariant there**: every
input of the group step is supplied at `drEnv`, so the field owes `GInv P K
drEnvWfT` and nothing syntactic. -/
theorem stepDAt_drEnv_iff (P : Premises4) (K : Nat → Nat) :
    GroupStepAt P K (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)]) (rr := 3)
      (rm := drRecMember) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT ↔
    GInv P K drEnvWfT :=
  ⟨fun h => h drAgree (drEnvWfT_classGD.2 K).1 (drEnvWfT_classGD.2 K).2 (gInv_drBase P K),
    fun h _ _ _ _ => h⟩

/-- The normalized-role twin at the δ fixture is **proved** (landed `gInvD`). -/
theorem gInvD_drEnv (P : Premises4) (K : Nat → Nat) : GInvD P K drEnvWfT :=
  gInvD P K drEnvWfT drEnvWfT_classGD.1 (drEnvWfT_classGD.2 K).1 (drEnvWfT_classGD.2 K).2

/-- **The exact remaining content of `StepDG` at the δ fixture**: the role bridge
from the normalized family (`envCtxD`) to the raw one (`envCtx`) at `drEnv`. -/
def DrRoleBridge (P : Premises4) (K : Nat → Nat) : Prop := GInvD P K drEnvWfT → GInv P K drEnvWfT

/-- The role bridge discharges the D group step at the δ fixture. -/
theorem stepDAt_drEnv_of_bridge (P : Premises4) (K : Nat → Nat) (h : DrRoleBridge P K) :
    GroupStepAt P K (f := 1) (fm := drFamMember) (ctors := [(2, drMkMember)]) (rr := 3)
      (rm := drRecMember) drBaseWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT :=
  (stepDAt_drEnv_iff P K).2 (h (gInvD_drEnv P K))

/-! ### A at the function-recursive fixture `wEnv` (m3's probe lemmas, ported) -/

/-- `fieldShapesFuel` reads only the members: `W`'s field shapes are
`[.nonrecursive, .recursive 1]` in every environment containing `Nat` at 0 and
`W` at 4 (swe-audit-m3's probe). -/
theorem w_fieldShapes_generic {E : ResolvedEnv}
    (h0 : E.members 0 = some natFamMember) (h4 : E.members 4 = some wFamMember) :
    fieldShapesFuel E 8 4 0 0 0 0 [wFieldA, wFieldF] =
      some [.nonrecursive, .recursive 1] := by
  simp [fieldShapesFuel, fieldAnalyze, piTelescopeFuel, whnfFuel, appsSpine,
    transparentBody, h0, h4, natFamMember, wFamMember, wFieldA, wFieldF,
    transparent, instantiateLevels, instantiate0, instantiate, foldApps,
    domainsContainFuel, properFamilyFuel, exactParamLocals, indicesCleanFuel,
    familyIdx, containsFamilyFuel]

/-- `W`'s family view: no parameters, no indices, level 1. -/
theorem w_family (node : RecNode natEnvU wEnv 4 6 wRecMember) :
    node.a.family.parameters = [] ∧ node.a.family.indices = [] ∧
      node.a.family.resultLevel = .succ .zero := by
  have hfam : node.a.family.member = wFamMember :=
    Option.some.inj ((node_fam_member node).symm.trans rfl)
  have hst := node.a.family.storedType
  rw [hfam] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [] _ _ _ (expr_not_pi_of_sort _)
    (expr_not_pi_of_sort _) hst
  have h3 := List.append_eq_nil.mp h1.symm
  injection h2 with h4
  exact ⟨h3.1, h3.2, h4.symm⟩

/-- `W`'s one constructor `sup` has fields `[wFieldA, wFieldF]`. -/
theorem w_fields (node : RecNode natEnvU wEnv 4 6 wRecMember)
    (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [] ∧
      (node.a.constructorViews i).resultIndices = [] ∧
      (node.a.constructorViews i).fields = [wFieldA, wFieldF] := by
  obtain ⟨hP, hI, _⟩ := w_family node
  have hp : (node.a.constructorViews i).parameters = [] := by
    have := (node.a.constructorViews i).parameterCount
    rw [hP] at this
    exact List.eq_nil_of_length_eq_zero this
  have hr : (node.a.constructorViews i).resultIndices = [] := by
    have := (node.a.constructorViews i).indexCount
    rw [hI] at this
    exact List.eq_nil_of_length_eq_zero this
  refine ⟨hp, hr, ?_⟩
  have hst := (node.a.constructorViews i).storedType
  rw [hp, List.nil_append] at hst
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals 0
      (node.a.constructorViews i).fields.length ++ (node.a.constructorViews i).resultIndices)
  have hctor : node.a.constructors[i.val] = wSupMember := by
    have hlen : node.a.constructors.length = 1 :=
      node_ctors_length (ctors := [(5, wSupMember)]) node rfl
    obtain ⟨k, hk⟩ := i
    have h := node_ctor_member node ⟨k, hk⟩
    have hi : k < 1 := hlen ▸ hk
    match k, hk, hi, h with
    | 0, _, _, h => exact Option.some.inj (h.symm.trans rfl)
  have hm : (node.a.constructors[i.val]).mtype =
      policyPi [wFieldA, wFieldF] (.const 4 []) := by
    rw [hctor]; rfl
  exact (policyPi_split_eq [wFieldA, wFieldF] _ (.const 4 []) _
    (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hst)).1.symm

/-- `W`'s shapes at every descriptor: `[.nonrecursive, .recursive 1]`. -/
theorem w_shapes (node : RecNode natEnvU wEnv 4 6 wRecMember)
    (i : Fin node.a.constructors.length) :
    node.h14.shapesAt i = [.nonrecursive, .recursive 1] := by
  have hA := node.h14.analyzed i
  have h0 : node.E0.members 0 = some natFamMember := node.base 0 natFamMember rfl
  have hfam : node.a.family.member = wFamMember :=
    Option.some.inj ((node_fam_member node).symm.trans rfl)
  have h4 : node.E0.members 4 = some wFamMember := by
    have h := node.a.family.present
    rw [node.fam, hfam] at h
    exact h
  have hf : (node.a.constructorViews i).fields = [wFieldA, wFieldF] :=
    (w_fields node i).2.2
  have hp : node.a.family.parameters = [] := (w_family node).1
  have hq : node.a.family.indices = [] := (w_family node).2.1
  have har : node.a.family.member.arity = 0 := by rw [hfam]; rfl
  rw [node.fam, har, hp, hq, hf] at hA
  exact fieldShapesFuel_unique hA (w_fieldShapes_generic h0 h4)

/-- Every node of `W`'s group is `PendA` (field 1 is `recursive 1`). -/
theorem w_pendA (node : RecNode natEnvU wEnv 4 6 wRecMember) : PendA node := by
  have i0 : Fin node.a.constructors.length := ⟨0,
    node_ctors_length (ctors := [(5, wSupMember)]) node rfl ▸ Nat.zero_lt_one⟩
  exact ⟨i0, 1, 0, by rw [w_shapes node i0]; rfl⟩

/-- `W`'s group is in `StepAG`'s domain. -/
theorem wGroup_aArm : ∃ node : RecNode natEnvU wEnv 4 6 wRecMember, PendA node := by
  obtain ⟨node, _⟩ := group_node (f := 4) (fm := wFamMember) (ctors := [(5, wSupMember)])
    (rr := 6) (rm := wRecMember) natEnvUWfT rfl
    (fun c hc => by simp at hc; subst hc; rfl) rfl wMembersT
  exact ⟨node, w_pendA node⟩

/-- The base of `W`'s fixture (the `Nat` core) carries the model invariant at
every bound. -/
theorem gInv_natEnvU (P : Premises4) (K : Nat → Nat) : GInv P K natEnvUWfT :=
  gInv P K natEnvUWfT natEnvUWfT_classG.1 (natEnvUWfT_classG.2 K)

/-- **`StepAG` at `W`'s group owes the model invariant there and nothing
syntactic**: given the walk/bound inputs at `wEnv`, the field yields `GInv P K
wEnvWfT` (the converse is `stepAt_of_gInv`). -/
theorem gInv_wEnv_of_stepAAt (P : Premises4) (K : Nat → Nat)
    (h : GroupStepAt P K (f := 4) (fm := wFamMember) (ctors := [(5, wSupMember)]) (rr := 6)
      (rm := wRecMember) natEnvUWfT rfl (fun c hc => by simp at hc; subst hc; rfl) rfl wMembersT)
    (hAg : ∀ node : RecNode natEnvU wEnv 4 6 wRecMember,
      WalkAgree (AgreeAt node.a.family.parameters.length) wMembersT)
    (hB : BoundG K wEnvWfT) (hD : BoundDG K wEnvWfT) : GInv P K wEnvWfT :=
  h hAg hB hD (gInv_natEnvU P K)

end Rcic.F3.TierGroup
