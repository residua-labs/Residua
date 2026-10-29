import rcic.RcicF3Assembly
import rcic.RcicFamAppStepWLok
import rcic.RcicF3WalkSeal

/-!
# F3 stepW: the minimal tier hypothesis, its non-refutability, and the exact obstruction

`PartitionSteps.stepW` (`RcicF3Assembly`) is the only W-class antecedent of the
soundness tier (`tierF3Uncond_of_partition`). This module delivers the tier's
W-debt in its exact and minimal form (`StepWHyp`), proves the conditional tier
needs **nothing more** on the W axis, proves the debt **non-refutable at the
landed supply** (in-scope groups and the canonical `PendW` fixture `pwEnvWfT`),
and pins the exact obstruction: the debt is a **local same-term sort-uniqueness**
instance (`Rcic.Declarative.F8A2Support.SortUnique`), strictly below the RK-01
kernel rows. `closure_claim = 0`; no theory is narrowed (expressiveness first:
`StepWHyp` is a named antecedent, not a restriction on environments).

## §1 The minimal hypothesis

`stepW_boundary_iff` (`RcicFamAppStepWLok`) splits the `stepW` obligation into
the `UniformProp` arm (discharged unconditionally by `stepW_of_uniformProp`,
zero rows) and the `UniformType` arm, open only outside the scope supply.
`StepWHyp` is `PartitionSteps.stepW` guarded down to exactly that open arm:
owed **only** at `PendW ∧ UniformType ∧ ¬ InScope` nodes. The three dischargers
that make the guards honest are all landed:

- `UniformProp` → `stepW_of_uniformProp` (route W1, zero rows);
- `InScope` → `stepW_of_inScope` (route W4; subsumes `ScopeCheck` by
  `inScope_of_scopeCheck`, i.e. `typedRowsWf_of_scopeCheck` supply);
- the residual arm → `StepWHyp` itself.

`stepW_of_hyp` reassembles the full `stepW` field from `StepWHyp` (the case
split runs on `Premises4.dec`, so no `Classical.choice` enters);
`hyp_of_steps` is the converse, so the two forms of the tier's antecedent are
interchangeable and `StepWHyp` is the weaker-stated one. The tier wrappers take
exactly the non-W antecedents: `PartitionStepsABD` (`PartitionSteps` minus the
`stepW` field) plus `StepWHyp`; `partitionSteps_of_hyp` *constructs* the full
`PartitionSteps` — the `stepW` field is never an input. So
`tierF3Uncond_of_hyp` / `kernelSoundnessTierUncond_of_hyp` compose with the
landed assembly verbatim: **the tier consumer needs nothing more on the W
axis than `StepWHyp`** — in particular it never needs the RK-01 kernel rows
(`SortRowField` / `PiRowField` at `E'`) except as sufficient conditions for
`StepWHyp` (route W3 `stepW_of_sortRow_piRow`; route W2
`stepW_of_noAppLit_sortRow` needs row 1 alone at `NoAppLit` gap entries).

**Decoupling from RK-01.** `StepWHyp` is *implied by* the rows and never implies
them: it is the one-directional level agreement at gap positions only, and at
the one on-tree out-of-scope W-class fixture it is already TRUE unconditionally
(#8215, `eqW_stepW`: the only gap position's view level *equals* the family's
result level; the rows at that env would still entail RK-01's open `Eq`-prefix
row by `sortRowField_eqEnvT_of_eqW`). So a tier conditional on `StepWHyp` is
not a tier conditional on RK-01 — the debt left is exactly the residual
boundary arm (W-class groups whose gap view level is not already the result
level).

## §2 Non-refutability (the conditional tier is not vacuous)

`stepW_pwEnv`: at the canonical `PendW` fixture — the admitted group
`pwEnvWfT` (`V : Prop → Type`, `mk` parametric `np_c = 1`, recursor indexed
`np = 0`; `PendW` at every node by `pwEnvWfT_pendW`) — the `StepWHyp`
conclusion `WalkAgree (AgreeAt …)` **holds** (the group is in scope:
`pwEnvWfT_inScope`, so route W4 fires). Together with route W1 (`UniformProp`
families owe nothing) and the in-scope supply (`stepW_of_inScope` at every
`InScope` group), the hypothesis is discharged at every environment class
where a producer exists; no fixture or theorem on the tree refutes it (the
`witness_not_agreeAt` of `RcicLevelEqnArm` is an SCM-leaf predicate, not this
`AgreeAt`). Beyond this module's base, the out-of-scope instance is #8215's
`eqW_stepW` (`UniformType ∧ PendW ∧ ¬ InScope`, discharged with no row).

## §3 The exact obstruction: local same-term sort-uniqueness

`stepW_of_sortUnique`: `SortUnique E' arity` (same-term sort uniqueness at the
group environment — two sortings `T : Sort u`, `T : Sort v` of one term in one
well-formed context have `eqN u v`; `Rcic.Declarative.F8A2Support`) discharges
`stepW` outright. By `walk_entry_double_typed` the two views of a `PendW` gap
entry are exactly two such sortings of the **same** expression in the **same**
context, so the debt can fail only where local type uniqueness fails — the
unannotated same-term type uniqueness problem (Siles–Herbelin LICS 2010,
Lemma III.6 "Type Exchange"; in Lean's own metatheory the `IsDefEq.uniq`
conjecture, Lean4Lean arXiv 2403.14064 — see the retype-wall analysis,
`research/rcic/sortrow/NATIVE_VALLEYS_STATUS.md` §9). The rows imply
`SortUnique` (`sortUniqueAt_of_sortRow_piRow`), so a refutation of `StepWHyp`
refutes `SortRowField ∧ PiRowField` at that environment (route W3's
contrapositive) — the tier's W-debt sits **strictly below** the RK-01 rows and
exactly at one level-agreement instance of the known-open uniqueness problem.
No counter-model exists on the tree; producing one is producing a two-typing
disagreement at an admitted environment, i.e. refuting the rows there too.
-/

set_option autoImplicit false

namespace Rcic.F3.StepWMin

open Rcic.Declarative
open Rcic.F3
open Rcic.F3.PSet
open Rcic.Syn.FamApp.StepW
open Rcic.Model.PS (hasTyT_denRefs groupMembersT_preserve groupMembersT_installed)

/-! ## §1 The minimal hypothesis -/

/-- Every admitted recursor node's family result level is `UniformProp` or
`UniformType` (the elimination-selection dichotomy; `MixedUniverse` result
levels admit no selected elimination). -/
theorem uniformProp_or_uniformType {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) :
    UniformProp node.a.family.resultLevel ∨ UniformType node.a.family.resultLevel := by
  cases hpol : node.a.policy with
  | anySort =>
      rcases (EliminationSelection.anySort_iff _ _ _).mp (hpol ▸ node.a.selected) with hT | ⟨hP, _⟩
      · exact Or.inr hT
      · exact Or.inl hP
  | propOnly =>
      exact Or.inl ((EliminationSelection.propOnly_iff _ _ _).mp (hpol ▸ node.a.selected)).1

/-- **The minimal W-hypothesis of the soundness tier.** `PartitionSteps.stepW`
guarded down to the boundary theorem's open arm: owed only at `PendW` nodes of
`UniformType` families outside the in-scope supply. The `UniformProp` arm is
`stepW_of_uniformProp`, the in-scope arm is `stepW_of_inScope`; nothing else is
assumed. -/
def StepWHyp : Prop :=
  ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm),
    PendW hmem node → UniformType node.a.family.resultLevel →
    ¬ (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope →
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem

/-- `StepWHyp` reassembles the full `stepW` field: the `UniformProp` arm by
route W1, the in-scope arm by route W4, the residual arm by the hypothesis.
The case split runs on `Premises4.dec` (no `Classical.choice`). -/
theorem stepW_of_hyp (P : Premises4) (h : StepWHyp)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hPend : PendW hmem node) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
  cases P.dec ((EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem).InScope) with
  | isTrue hIS =>
      exact stepW_of_inScope hE hfam hctors hrec hmem node (walkRec_of_group hmem) hIS
  | isFalse hIS =>
      rcases uniformProp_or_uniformType node with hP | hT
      · exact stepW_of_uniformProp hE hfam hctors hrec hmem node (walkRec_of_group hmem) hP
      · exact h hE hfam hctors hrec hmem node hPend hT hIS

/-- Converse: the landed `stepW` field already gives `StepWHyp` — the two
forms of the tier's W-antecedent are interchangeable, and `StepWHyp` is the
weaker-stated one (owed only on the open arm). -/
theorem hyp_of_steps {P : Premises4} {K : Nat → Nat} (steps : PartitionSteps P K) : StepWHyp :=
  fun hE hfam hctors hrec hmem node hPend _ _ => steps.stepW hE hfam hctors hrec hmem node hPend

/-- **The tier's non-W antecedents**: `PartitionSteps` with the `stepW` field
removed. A caller holding the A/B1/D rows and `StepWHyp` owes nothing else —
this is the exact input face of `tierF3Uncond_of_hyp`, so the wrappers do not
sneak the full `stepW` back in through a `PartitionSteps` argument. -/
structure PartitionStepsABD (P : Premises4) (K : Nat → Nat) : Prop where
  /-- **A**: function-recursive fields (`recursive (m+1)`); the KT lane. -/
  stepA : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendA node →
      NodeFieldRow P K hE hfam hctors hrec hmem node
  /-- **B1**: `Prop` family, `anySort` elim, a field revealed in result indices
  (including `PendC ∧ PendB` nodes); the B lane. -/
  stepB1 : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendB node → ¬ PendA node → ¬ PendD node →
      NodeFieldRow P K hE hfam hctors hrec hmem node
  /-- **D**: noncanonical `recursive 0` fields (reached through δ/β). -/
  stepD : ∀ {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
      {ctors : List (Nat × CheckedMember)}
      (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
      (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
      (node : RecNode E E' f rr rm), PendD node → ¬ PendA node →
      NodeFieldRow P K hE hfam hctors hrec hmem node

/-- The A/B1/D projection of a full `PartitionSteps` — the bridge for a caller
who already holds the landed steps record. -/
theorem partitionStepsABD_of_steps {P : Premises4} {K : Nat → Nat}
    (steps : PartitionSteps P K) : PartitionStepsABD P K where
  stepA := steps.stepA
  stepB1 := steps.stepB1
  stepD := steps.stepD

/-- **The full steps record is constructed, not taken**: from the non-W fields
plus `StepWHyp`, with the `stepW` field *built* by `stepW_of_hyp`. A caller
holding `PartitionStepsABD` and `StepWHyp` never proves `stepW` itself. -/
theorem partitionSteps_of_hyp (P : Premises4) (K : Nat → Nat) (h : StepWHyp)
    (abd : PartitionStepsABD P K) : PartitionSteps P K where
  stepA := abd.stepA
  stepB1 := abd.stepB1
  stepD := abd.stepD
  stepW := fun hE hfam hctors hrec hmem node hPend =>
    stepW_of_hyp P h hE hfam hctors hrec hmem node hPend

/-- **The conditional tier under the minimal W-hypothesis**: the height-4
consistency tier holds under `StepWHyp` and the A/B1/D rows — the input face
is `PartitionStepsABD`, so nothing on the W axis beyond `StepWHyp` is owed. -/
theorem tierF3Uncond_of_hyp (h : StepWHyp)
    (abd : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsABD P K) :
    Rcic.Apex.TierF3Uncond :=
  tierF3Uncond_of_partition (fun P K => partitionSteps_of_hyp P K h (abd P K))

/-- The full unconditional kernel tier (F1 closed, F3 modulo the same named
rows) under the same minimal W-hypothesis and the same A/B1/D input face. -/
theorem kernelSoundnessTierUncond_of_hyp (h : StepWHyp)
    (abd : ∀ (P : Premises4) (K : Nat → Nat), PartitionStepsABD P K) :
    Rcic.Apex.KernelSoundnessTierUncond :=
  ⟨Rcic.Apex.tierF1, tierF3Uncond_of_hyp h abd⟩

/-! ## §2 Non-refutability: the canonical `PendW` fixture -/

/-- The canonical `PendW` group `pwEnvWfT` (`V : Prop → Type`, `mk` parametric,
recursor indexed) is in scope: `GroupInScopeT emptyEnv 0 pwV [(1, pwMk)] 2 pwRec`
is inhabited unconditionally (the `wCanon` kernel-checked certificate, applied
by defeq of the stored members). -/
theorem pwEnvWfT_inScope :
    (EnvWfT.group emptyEnv 0 pwV [(1, pwMk)] 2 pwRec pwEnv .empty rfl
      (fun c hc => by simp at hc; subst hc; rfl) rfl pwMembersT).InScope :=
  wCanon_inScope_of_group rfl (fun c hc => by simp at hc; subst hc; rfl) rfl pwMembersT

/-- **The `StepWHyp` conclusion holds at the canonical `PendW` fixture**: every
recursor node of `pwEnvWfT` (at each of which `PendW` holds, by
`pwEnvWfT_pendW`) satisfies `WalkAgree (AgreeAt …)` — route W4 through
`pwEnvWfT_inScope`. The conditional tier is not vacuous. -/
theorem stepW_pwEnv : ∀ node : RecNode emptyEnv pwEnv 0 2 pwRec,
    WalkAgree (AgreeAt node.a.family.parameters.length) pwMembersT := by
  intro node
  exact stepW_of_inScope (E := emptyEnv) (E' := pwEnv) (f := 0) (rr := 2) (fm := pwV) (rm := pwRec)
    (ctors := [(1, pwMk)]) .empty rfl (fun c hc => by simp at hc; subst hc; rfl) rfl pwMembersT node
    (walkRec_of_group pwMembersT) pwEnvWfT_inScope

/-! ## §3 The exact obstruction: local same-term sort-uniqueness -/

/-- `GapSortLeAt` from same-term sort uniqueness at `E'` (the
`gapSortLeAt_of_sortRow_piRow` leaf with the rows+DT-012 replaced by
`SortUnique`). Private: the public face is `stepW_of_sortUnique`. -/
private theorem gapSortLeAt_of_sortUnique {np : Nat} {E' Ew : ResolvedEnv}
    (hW' : EnvWfT E') {famO : PolicyFamilyView Ew} {m : CheckedMember}
    {cv : PolicyConstructorView Ew famO m}
    (htyped : CtorTypedT cv) (hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m')
    (hU : F8A2Support.SortUnique E' famO.member.arity) :
    GapSortLeAt np E' Ew famO m cv := by
  intro k hk _ _ uR hdR hbdR
  have htelE' : TelTypedT E' famO.member.arity (cv.parameters ++ cv.fields) cv.domainsTyped.levels :=
    fun idx => let ⟨d⟩ := htyped.1 idx; ⟨hasTyTExt hEw d⟩
  obtain ⟨hΓ⟩ := ctxWfT_of_telTypedT htelE' k (Nat.le_of_lt hk)
  obtain ⟨hdO⟩ := htelE' ⟨k, hk⟩
  have heq := hU hW' hΓ hdO hdR
  rcases hbdR with hP | hle
  · exact Or.inl hP
  · exact Or.inr (leN_of_eqN_leN heq hle)

/-- **Same-term sort uniqueness discharges `stepW`** (`SortUnique E' arity` —
two sortings of one term in one well-formed context have `eqN` levels). The
rows imply it (`sortUniqueAt_of_sortRow_piRow`), so this sits strictly below
the RK-01 rows: the tier's W-debt is exactly one level-agreement instance of
the unannotated same-term type-uniqueness problem. -/
theorem stepW_of_sortUnique {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hWR : WalkRec hmem)
    (hU : F8A2Support.SortUnique E' node.a.family.member.arity) :
    WalkAgree (AgreeAt node.a.family.parameters.length) hmem := by
  rw [walkAgree_agreeAt_iff_gapSortLeAt hE hfam hctors hrec hmem hWR node]
  have hW' : EnvWfT E' := .group E f fm ctors rr rm E' hE hfam hctors hrec hmem
  have go : ∀ {S Ew E'' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
      (hw : GroupMembersT S Ew ms E''),
      (∀ c, c ∈ ms → c ∈ (f, fm) :: ctors ++ [(rr, rm)]) →
      (∀ r' m', E''.members r' = some m' → E'.members r' = some m') →
      WalkAgree (GapSortLeAt node.a.family.parameters.length E') hw := by
    intro S Ew E'' ms hw
    induction hw with
    | nil _ => intros; trivial
    | cons E₀ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ htyped hrest ih =>
        intro hms hsub
        have hin := hms (r, m) (List.mem_cons_self _ _)
        have hsubR : ∀ r' m', (extendEnv E₀ r m).members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
        have hEw : ∀ r' m', E₀.members r' = some m' → E'.members r' = some m' :=
          fun r' m' h => hsubR r' m' (members_extend_preserved hfresh r' m' h)
        refine ⟨?_, ih (fun c hc => hms c (List.mem_cons_of_mem _ hc)) hsub⟩
        cases hadm with
        | family _ _ _ _ _ => trivial
        | recursor _ _ _ _ _ _ _ => trivial
        | constructor famO view _ _ _ _ _ =>
            obtain ⟨_, _, _, _, _, harO⟩ :=
              walk_ctor_views_syn_eq hE hfam hctors hrec hmem hWR node famO view hin hEw
            exact gapSortLeAt_of_sortUnique hW' htyped.2 hEw (harO ▸ hU)
  exact go hmem (fun _ h => h) (fun _ _ h => h)

end Rcic.F3.StepWMin

#print axioms Rcic.F3.StepWMin.uniformProp_or_uniformType
#print axioms Rcic.F3.StepWMin.StepWHyp
#print axioms Rcic.F3.StepWMin.stepW_of_hyp
#print axioms Rcic.F3.StepWMin.hyp_of_steps
#print axioms Rcic.F3.StepWMin.partitionSteps_of_hyp
#print axioms Rcic.F3.StepWMin.partitionStepsABD_of_steps
#print axioms Rcic.F3.StepWMin.tierF3Uncond_of_hyp
#print axioms Rcic.F3.StepWMin.kernelSoundnessTierUncond_of_hyp
#print axioms Rcic.F3.StepWMin.pwEnvWfT_inScope
#print axioms Rcic.F3.StepWMin.stepW_pwEnv
#print axioms Rcic.F3.StepWMin.stepW_of_sortUnique
