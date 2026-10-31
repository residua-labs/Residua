import rcic.RcicAnnEnvWf
import rcic.RcicAnnLREnvG
import rcic.RcicAnnLRRowsG
/-!
# M2-e (8) — the environment judgment in the polymorphic model, and the semantic
environment discharged down to the families, constructors and recursors

`EnvWfA I E`: main's `EnvWf` (`RcicEnv`) on the copy, every member typed under
ITS OWN universe arity in the environment built so far — members with a body at
arity `0` (00 §20.6 MONOMORPHIC DELTA), level-closed. A family enters with ALL its
constructors as ONE step (`group`, M2-f (4a), 05 §1/§16): the family's checks in the
base (HeaderScope), each constructor's in the base plus the family (ConstructorScope),
and the views of `RcicAnnGroup` — the stored types built from them, `nparamsA` the
family view's parameter count, the family-free parts typed in the base. A recursor
enters WITH its group (`groupRec`, M2-f (5a), 05 §1/§3/§13): the constructors at
`f + 1, …, f + k` in candidate order, the recursor at `f + 1 + k`, its stored type the
type built from the views (`RcicAnnRecView`) and typed in the base, the family and the
constructors (DerivationScope). The free-standing recursor step of M2-e (8), which admitted
a recursor-class member with any closed type, is withdrawn: a recursor is derived (05 §13),
and the concrete ι reads its group's layout. `EnvClosedA` and `EnvLevelsA` are theorems
over the judgment.

The induction of M2-e (4) (`envSemAt_of_envWfAg`) discharges the semantic clause
for every member but the families, the constructors and the recursors: the arity-`0`
members (their derivations read at the ambient arity through `hasTyA_instLevels` at
`[]`). A polymorphic RIGID member's clause holds by REFLECTION at every pair of `=ₙ`
level lists (`envSemClauseA_rigidPolyg`): the type's validity at each instantiation
from the fundamental theorem on the instantiated derivation, the right constant
typed at the left's instantiated type through `conv` along LEVEL IRRELEVANCE
(`convA_levelIrr_wf` at the empty context, weakened into the target), the spines
stuck by `IotaRecHeadA`. `EnvWfA` admits no such member (axioms, definitions,
theorems and opaque constants enter at arity `0`; the polymorphic members are the
families, constructors and recursors), so the induction does not use it.

Families and constructors were discharged the same way until M2-f (3b): a family
application was a stuck-typed neutral, a constructor an extended one. Since (3b) a
family application has the relation's `fam` clause and a constructor application is
that clause's constructor disjunct, so neither is a neutral and reflection does not
reach them; their clause is `EnvSemIndAg`, a hypothesis. Since M2-f (4a) they enter
as one group step; M2-f (4b)/(4c) build their clause there by telescope introduction
(`telIntroAg`): the induction carries constructor closure (`CtorClosedA`, the census) and
takes the family's clause AT ITS STEP from the base's clauses (`EnvSemFamStepAg`, proved in
`RcicAnnFamSem`) and the constructors' at theirs, with the family's in hand (`EnvSemCtorStepAg`,
proved in `RcicAnnCtorSem`); `EnvSemIndAg` gives both. What remains is `EnvSemRecAg`,
the recursors' clause (M2-f (5) / M3's content); over an environment without
families, constructors or recursors (`NoFamA`, `NoRecA`) the two Type-level rows
hold with no semantic hypothesis at all.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the environment judgment -/

section WfProps
variable {I : IotaIfaceA}

end WfProps

/-- the semantic clause for the RECURSORS only: their content (M2-f / M3), the one
    hypothesis the discharge below leaves standing. -/
def EnvSemRecAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .recursorM → EnvSemClauseAg E I n ρ₀ r m

/-- the semantic clause for the FAMILIES AND CONSTRUCTORS (M2-f (3b)): a family
    application has the `fam` clause, so a family is no longer a stuck-typed neutral,
    and a constructor is no longer an extended neutral (its applications are the
    clause's constructor disjunct); their self-relatedness is M2-f (4)'s content
    (`telIntroAg`), a hypothesis until then. -/
def EnvSemIndAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → (m.mclass = .inductiveM ∨ m.mclass = .constructorM) →
    EnvSemClauseAg E I n ρ₀ r m

theorem envSemIndA_of_noFamg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (h : NoFamA E) : EnvSemIndAg E I n ρ₀ :=
  fun r m hres hind => hind.elim (fun h' => absurd h' (h r m hres).1) (fun h' => absurd h' (h r m hres).2)

theorem envSemRecA_of_noRecg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (h : NoRecA E) : EnvSemRecAg E I n ρ₀ :=
  fun r m hres hrec => absurd hrec (h r m hres)

/-! ## (2) the clause at a polymorphic rigid member -/

section Poly
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the clause at a polymorphic RIGID member (no body, not a recursor): by
    reflection at every pair of `=ₙ` level lists, from the type's validity at each
    instantiation and the level-irrelevance conversion between two instantiations. -/
theorem envSemClauseA_rigidPolyg (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hK : PropKeyA E I n) {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m) (hnobody : m.bodyA = none)
    (hnr : m.mclass ≠ .recursorM) (hni : m.mclass ≠ .inductiveM) (hnc : m.mclass ≠ .constructorM)
    {u : Level}
    (hT : ∀ ls : List Level, ls.length = m.arity → levelsBounded n ls = true →
      ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
        LRRelAg E I n ρ₀ k Δ (.sort (instLevel ls u)) (instantiateLevelsA ls m.mtypeA)
          (instantiateLevelsA ls m.mtypeA))
    (hc : ∀ ls ls' : List Level, ls.length = m.arity → ls'.length = m.arity →
      levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
      Nonempty (ConvA E I n [] (instantiateLevelsA ls m.mtypeA) (instantiateLevelsA ls' m.mtypeA)
        (.sort (instLevel ls u)))) :
    EnvSemClauseAg E I n ρ₀ r m := by
  intro ls ls' hlen hwf hwf' heq
  have hlen' : ls'.length = m.arity := (eqNList_length ls ls' heq).symm.trans hlen
  obtain ⟨k₁, h₁⟩ := hT ls hlen hwf
  obtain ⟨k₂, h₂⟩ := hT ls' hlen' hwf'
  refine ⟨max k₁ k₂, fun k hk Δ hΔ => ?_⟩
  obtain ⟨_, hval, _, hty, _, _⟩ := LRRelA_sort_elimg (h₁ k (le_max_of_le₁ hk) Δ hΔ)
  obtain ⟨_, _, _, hty', _, _⟩ := LRRelA_sort_elimg (h₂ k (le_max_of_le₂ hk) Δ hΔ)
  have hcl : ∀ (ms : List Level) (j : Nat),
      liftA j 1 (instantiateLevelsA ms m.mtypeA) = instantiateLevelsA ms m.mtypeA :=
    fun ms => liftA_instantiateLevelsA_closed (hE r m hres).1 ms
  have htc : Nonempty (HasTyA E I n Δ (.const r ls) (instantiateLevelsA ls m.mtypeA)) :=
    hty.elim fun t => ⟨.const Δ r ls m _ hres hlen hwf t⟩
  have hcΔ : Nonempty (ConvA E I n Δ (instantiateLevelsA ls' m.mtypeA) (instantiateLevelsA ls m.mtypeA)
      (.sort (instLevel ls u))) :=
    (hc ls ls' hlen hlen' hwf hwf' heq).elim fun c =>
      ⟨convA_closedWeakenA hE hI (hcl ls') (hcl ls) (fun _ => rfl) Δ (.symm _ _ _ _ c)⟩
  have htc' : Nonempty (HasTyA E I n Δ (.const r ls') (instantiateLevelsA ls m.mtypeA)) :=
    hty'.elim fun t' => hty.elim fun t => hcΔ.elim fun c =>
      ⟨.conv Δ _ _ _ (instLevel ls' u) (instLevel ls u) (.const Δ r ls' m _ hres hlen' hwf' t') t'
        (eqNA_symm (instLevel_eqNList heq u)) t c⟩
  exact LRRelA_reflectg hE hI hK hΔ hval (neutKA_const hR hres (Or.inr hnobody) hnr hni hnc Δ ls)
    (neutKA_const hR hres (Or.inr hnobody) hnr hni hnc Δ ls') htc htc'
    (htc'.elim fun t' => ⟨.consts Δ r ls ls' m hres hlen hwf hwf' heq t'⟩)

end Poly

/-! ## (2b) the census (moved from `RcicAnnFamClause`, M2-f (4b))

A family's constructors are exactly its group's. Every constructor of a well-formed environment
has its family in the environment (`ctorFamInA_of_envWfA`: a group constructor's family is the
group's, `CtorViewA.famRef`). The discharge runs on prefixes `E₀` of the final `E`; a prefix is
CONSTRUCTOR-CLOSED in `E` when every constructor of `E` whose family is in the prefix is itself in
the prefix (`CtorClosedA`). The final environment is closed in itself (`ctorClosedA_refl`), and
closure descends through every step: a step that adds no constructor (`ctorClosedA_extend_pred`),
and a group, whose new constructors have the group's family, fresh below it
(`ctorClosedA_group_pred`). At a group step, a constructor of `E` whose family is the group's is
one of the group's constructors (`groupCensusA`). -/

section Census
variable {I : IotaIfaceA}

end Census

/-! ## (2c) the clauses the discharge consumes -/

section Steps
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the clause at a group's FAMILY, at its step (M2-f (4b)): from the base's clauses, the group
    constructor-closed in `E`. `RcicAnnFamSem` proves it under the small-index profile. -/
def EnvSemFamStepAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ (E₀ : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) (u : Level), EnvWfA I E₀ →
    fm.mclass = .inductiveM → fm.bodyA = none → (∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) →
    HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u) →
    ∀ (fv : FamViewA fm) (cs : List (GroupCtorA I E₀ f fm fv)),
      GroupFreshA E₀ f fm (cs.map GroupCtorA.entry) →
      PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E →
      CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E →
      EnvSemAtg E I n ρ₀ (domA E₀) → EnvSemClauseAg E I n ρ₀ f fm

/-- the clause at the CONSTRUCTORS (M2-f (4c)'s content). -/
def EnvSemCtorAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .constructorM → EnvSemClauseAg E I n ρ₀ r m

theorem envSemFamStepA_of_indg (hInd : EnvSemIndAg E I n ρ₀) : EnvSemFamStepAg E I n ρ₀ :=
  fun _ _ _ _ _ hcls _ _ _ _ _ hfresh hpre _ _ =>
    hInd _ _ (hpre _ _ (members_groupEnvA_family hfresh)) (Or.inl hcls)

theorem envSemCtorA_of_indg (hInd : EnvSemIndAg E I n ρ₀) : EnvSemCtorAg E I n ρ₀ :=
  fun r m hres hc => hInd r m hres (Or.inr hc)

/-- the clause at a group's CONSTRUCTORS, at its step (M2-f (4c)): from the base's clauses and the
    family's, the group constructor-closed in `E`. `RcicAnnCtorSem` proves it. -/
def EnvSemCtorStepAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ (E₀ : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) (u : Level), EnvWfA I E₀ →
    fm.mclass = .inductiveM → fm.bodyA = none → (∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) →
    HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u) →
    ∀ (fv : FamViewA fm) (cs : List (GroupCtorA I E₀ f fm fv)),
      GroupFreshA E₀ f fm (cs.map GroupCtorA.entry) →
      PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E →
      CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E →
      EnvSemAtg E I n ρ₀ (domA (extendEnvA E₀ f fm)) →
      ∀ gc ∈ cs, EnvSemClauseAg E I n ρ₀ gc.ref gc.member

theorem envSemCtorStepA_of_ctorg (hCtor : EnvSemCtorAg E I n ρ₀) : EnvSemCtorStepAg E I n ρ₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ hfresh hpre _ _ gc hgc =>
    hCtor gc.ref gc.member (hpre _ _ (members_groupEnvA_ctor hfresh hgc)) gc.hcls

/-- the clause at a group's RECURSOR, at its step (M2-f (5)): from the clauses of the base, the
    family and the constructors, the group constructor-closed in `E`. `RcicAnnRecSem` proves it
    under the profile (M2-f (5b)). -/
def EnvSemRecStepAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ (E₀ : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) (u : Level), EnvWfA I E₀ →
    fm.mclass = .inductiveM → fm.bodyA = none → (∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) →
    HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u) →
    ∀ (fv : FamViewA fm) (cs : List (GroupCtorA I E₀ f fm fv)),
      GroupFreshA E₀ f fm (cs.map GroupCtorA.entry) →
      cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length →
      ∀ (rec : GroupRecA I E₀ f fm fv cs),
      (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)).members (f + 1 + cs.length) = none →
      PrefixA (groupRecEnvA cs rec) E →
      CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E →
      EnvSemAtg E I n ρ₀ (domA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))) →
      EnvSemClauseAg E I n ρ₀ (f + 1 + cs.length) rec.member

theorem envSemRecStepA_of_recg (hRec : EnvSemRecAg E I n ρ₀) : EnvSemRecStepAg E I n ρ₀ :=
  fun _ _ _ _ _ _ _ _ _ _ cs _ _ rec _ hpre _ _ =>
    hRec _ rec.member (hpre _ _ (members_groupRecEnvA cs rec)) rec.hcls

end Steps

/-! ## (3) the induction on the environment -/

section Discharge
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a group's members at the group's step: the family from `EnvSemFamStepAg`, the constructors
    from `EnvSemCtorStepAg` with the family's clause in hand, the base from the induction. -/
theorem envSemAt_groupAg (hFam : EnvSemFamStepAg E I n ρ₀) (hCtor : EnvSemCtorStepAg E I n ρ₀)
    {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {u : Level} (hW : EnvWfA I E₀)
    (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
    (hclT : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (fv : FamViewA fm) (cs : List (GroupCtorA I E₀ f fm fv))
    (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hpre : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    (hclo : CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    (ih : EnvSemAtg E I n ρ₀ (domA E₀)) :
    EnvSemAtg E I n ρ₀ (domA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))) := by
  have hfamC := hFam E₀ f fm u hW hcls hnobody hclT hT fv cs hfresh hpre hclo ih
  have ihF : EnvSemAtg E I n ρ₀ (domA (extendEnvA E₀ f fm)) := fun r m hD hres => by
    by_cases hr : r = f
    · subst hr
      rw [hpre r fm (members_groupEnvA_family hfresh)] at hres
      cases hres
      exact hfamC
    · obtain ⟨m₁, hm₁⟩ := hD
      rw [members_extendEnvA_ne E₀ f fm hr] at hm₁
      exact ih r m ⟨m₁, hm₁⟩ hres
  intro r' m' hD hres'
  obtain ⟨m₀, hm₀⟩ := hD
  have hm₀E : E.members r' = some m₀ := hpre r' m₀ hm₀
  have hmm : m₀ = m' := Option.some.inj (hm₀E.symm.trans hres')
  subst hmm
  rcases members_groupEnvA _ r' m₀ hm₀ with ⟨rfl, rfl⟩ | hc | hb
  · exact hfamC
  · obtain ⟨c, hcmem, hce⟩ := List.mem_map.mp hc
    have hm : c.member = m₀ := congrArg Prod.snd hce
    have hr : c.ref = r' := congrArg Prod.fst hce
    subst hm
    subst hr
    exact hCtor E₀ f fm u hW hcls hnobody hclT hT fv cs hfresh hpre hclo ihF c hcmem
  · exact ih r' m₀ ⟨m₀, hb⟩ hm₀E

/-- `EnvSemAg` on the members of a well-formed prefix `E₀` of `E`, constructor-closed in `E`, in
    `E`: by induction on `E₀`'s construction, closure descending with it; arity-`0` members by
    reflection or δ-expansion (M2-e (4)); a group's family from `EnvSemFamStepAg` at its step,
    where only the base's clauses are in hand (M2-f (4b), `RcicAnnFamSem`), its constructors from
    `EnvSemCtorAg` (M2-f (4c)); recursors from `EnvSemRecAg`. -/
theorem envSemAt_of_envWfAg (hE : EnvClosedA E) (hEL : EnvLevelsA E) (hI : IotaLiftA I)
    (hIS : IotaSubstA I) (hIL : IotaLevelsA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hK : PropKeyA E I n)
    (hFam : EnvSemFamStepAg E I n ρ₀) (hCtor : EnvSemCtorStepAg E I n ρ₀) (hRec : EnvSemRecStepAg E I n ρ₀) :
    {E₀ : ResolvedEnvA} → EnvWfA I E₀ → PrefixA E₀ E → CtorClosedA E₀ E → EnvSemAtg E I n ρ₀ (domA E₀)
  | _, .empty, _, _ => fun _ _ hD _ => hD.elim fun _ hm => Option.noConfusion hm
  | _, .axiomM (arity := arity) E₀ r A u hW hfresh hA _ _, hpre, hclo => by
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_extend E₀ r _ hfresh) hpre
      have ih := envSemAt_of_envWfAg hE hEL hI hIS hIL hEN hNC hR hρ hK hFam hCtor hRec hW hpre₀
        (ctorClosedA_extend_pred (fun h => MemberClass.noConfusion h) hclo)
      have harms := fundArmsA_atg hE hI hIS hEN hNC hR hρ hK ih
      intro r' m' hD hres'
      by_cases hr : r' = r
      · rw [hr] at hres' ⊢
        have hm : E.members r = some ⟨.axiomM, arity, A, none, 0, none⟩ :=
          hpre r _ (members_extendEnvA_self E₀ r _)
        rw [hm] at hres'
        cases hres'
        apply envSemClauseA_rigidPolyg hE hI hR hK hm rfl
          (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
          (fun h => MemberClass.noConfusion h)
        · intro ls hlen hwf
          exact fundArmA_nilg (fundHasTyPrefixAg hpre₀ harms.1 harms.2
            (hasTyA_instLevels (envWfA_levels hW) hIL hwf hlen hA))
        · intro ls ls' hlen hlen' hwf hwf' heq
          obtain ⟨hc⟩ := convA_levelIrr_wf (envWfA_closed hW) hI
            (iotaRecHeadTypedA_prefix hpre₀ hR) (envWfA_levels hW) hIL
            hwf hwf' hlen hlen' heq CtxWfA.nil hA
          exact ⟨convEnvA hpre₀ hc⟩
      · obtain ⟨m₀, hm₀⟩ := hD
        rw [members_extendEnvA_ne E₀ r _ hr] at hm₀
        exact ih r' m' ⟨m₀, hm₀⟩ hres'
  | _, .definitionM E₀ r A v u hW hfresh hA hv _ _ _ _, hpre, hclo => by
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_extend E₀ r _ hfresh) hpre
      have ih := envSemAt_of_envWfAg hE hEL hI hIS hIL hEN hNC hR hρ hK hFam hCtor hRec hW hpre₀
        (ctorClosedA_extend_pred (fun h => MemberClass.noConfusion h) hclo)
      have harms := fundArmsA_atg hE hI hIS hEN hNC hR hρ hK ih
      intro r' m' hD hres'
      by_cases hr : r' = r
      · rw [hr] at hres' ⊢
        have hm : E.members r = some ⟨.definitionM, 0, A, some v, 0, none⟩ :=
          hpre r _ (members_extendEnvA_self E₀ r _)
        rw [hm] at hres'
        cases hres'
        obtain ⟨k₁, hT⟩ := fundArmA_nilg (fundHasTyPrefixAg hpre₀ harms.1 harms.2
          (hasTyA_arity0 (envWfA_levels hW) hIL hA))
        obtain ⟨k₂, hV⟩ := fundArmA_nilg (fundHasTyPrefixAg hpre₀ harms.1 harms.2
          (hasTyA_arity0 (envWfA_levels hW) hIL hv))
        exact envSemClauseA_defg hE hI hm (k₀ := max k₁ k₂)
          (fun k hk Δ hΔ => hT k (Nat.le_trans (Nat.le_max_left _ _) hk) Δ hΔ)
          (fun k hk Δ hΔ => hV k (Nat.le_trans (Nat.le_max_right _ _) hk) Δ hΔ)
      · obtain ⟨m₀, hm₀⟩ := hD
        rw [members_extendEnvA_ne E₀ r _ hr] at hm₀
        exact ih r' m' ⟨m₀, hm₀⟩ hres'
  | _, .theoremM E₀ r A p hW hfresh hA _ _ _ _ _, hpre, hclo => by
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_extend E₀ r _ hfresh) hpre
      have ih := envSemAt_of_envWfAg hE hEL hI hIS hIL hEN hNC hR hρ hK hFam hCtor hRec hW hpre₀
        (ctorClosedA_extend_pred (fun h => MemberClass.noConfusion h) hclo)
      have harms := fundArmsA_atg hE hI hIS hEN hNC hR hρ hK ih
      intro r' m' hD hres'
      by_cases hr : r' = r
      · rw [hr] at hres' ⊢
        have hm : E.members r = some ⟨.theoremM, 0, A, some p, 0, none⟩ :=
          hpre r _ (members_extendEnvA_self E₀ r _)
        rw [hm] at hres'
        cases hres'
        obtain ⟨k₀, hT⟩ := fundArmA_nilg (fundHasTyPrefixAg hpre₀ harms.1 harms.2
          (hasTyA_arity0 (envWfA_levels hW) hIL hA))
        exact envSemClauseA_rigidg hE hI hR hK hm rfl (Or.inl rfl)
          (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
          (fun h => MemberClass.noConfusion h) hT
      · obtain ⟨m₀, hm₀⟩ := hD
        rw [members_extendEnvA_ne E₀ r _ hr] at hm₀
        exact ih r' m' ⟨m₀, hm₀⟩ hres'
  | _, .opaqueM E₀ r A v u hW hfresh hA _ _ _ _ _, hpre, hclo => by
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_extend E₀ r _ hfresh) hpre
      have ih := envSemAt_of_envWfAg hE hEL hI hIS hIL hEN hNC hR hρ hK hFam hCtor hRec hW hpre₀
        (ctorClosedA_extend_pred (fun h => MemberClass.noConfusion h) hclo)
      have harms := fundArmsA_atg hE hI hIS hEN hNC hR hρ hK ih
      intro r' m' hD hres'
      by_cases hr : r' = r
      · rw [hr] at hres' ⊢
        have hm : E.members r = some ⟨.opaqueM, 0, A, some v, 0, none⟩ :=
          hpre r _ (members_extendEnvA_self E₀ r _)
        rw [hm] at hres'
        cases hres'
        obtain ⟨k₀, hT⟩ := fundArmA_nilg (fundHasTyPrefixAg hpre₀ harms.1 harms.2
          (hasTyA_arity0 (envWfA_levels hW) hIL hA))
        exact envSemClauseA_rigidg hE hI hR hK hm rfl (Or.inl rfl)
          (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
          (fun h => MemberClass.noConfusion h) hT
      · obtain ⟨m₀, hm₀⟩ := hD
        rw [members_extendEnvA_ne E₀ r _ hr] at hm₀
        exact ih r' m' ⟨m₀, hm₀⟩ hres'
  | _, .group E₀ f fm u hW hcls hnobody hclT hT _ fv cs hfresh, hpre, hclo => by
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpre
      have ih := envSemAt_of_envWfAg hE hEL hI hIS hIL hEN hNC hR hρ hK hFam hCtor hRec hW hpre₀
        (ctorClosedA_group_pred hcls hfresh hclo)
      exact envSemAt_groupAg hFam hCtor hW hcls hnobody hclT hT fv cs hfresh hpre hclo ih
  | _, .groupRec E₀ f fm u hW hcls hnobody hclT hT _ fv cs hfresh hlay rec hrf, hpre, hclo => by
      have hpreG : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E :=
        prefixA_trans (prefixA_extend _ _ _ hrf) hpre
      have hcloG := ctorClosedA_groupRec_pred hclo
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpreG
      have ih := envSemAt_of_envWfAg hE hEL hI hIS hIL hEN hNC hR hρ hK hFam hCtor hRec hW hpre₀
        (ctorClosedA_group_pred hcls hfresh hcloG)
      have ihG := envSemAt_groupAg hFam hCtor hW hcls hnobody hclT hT fv cs hfresh hpreG hcloG ih
      intro r' m' hD hres'
      by_cases hr : r' = f + 1 + cs.length
      · subst hr
        rw [hpre _ _ (members_groupRecEnvA cs rec)] at hres'
        cases hres'
        exact hRec E₀ f fm u hW hcls hnobody hclT hT fv cs hfresh hlay rec hrf hpre hcloG ihG
      · obtain ⟨m₀, hm₀⟩ := hD
        unfold groupRecEnvA at hm₀
        rw [members_extendEnvA_ne _ _ _ hr] at hm₀
        exact ihG r' m' ⟨m₀, hm₀⟩ hres'

/-- THE SEMANTIC ENVIRONMENT, discharged down to the families, constructors and
    recursors: a well-formed environment satisfies `EnvSemAg` given the clause at
    its families and constructors (`EnvSemIndAg`, M2-f (4)'s content) and at its
    recursors (`EnvSemRecAg`). -/
theorem envSemA_of_envWfAg (hW : EnvWfA I E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hK : PropKeyA E I n)
    (hInd : EnvSemIndAg E I n ρ₀) (hRec : EnvSemRecAg E I n ρ₀) : EnvSemAg E I n ρ₀ :=
  fun r m hres =>
    envSemAt_of_envWfAg (envWfA_closed hW) (envWfA_levels hW) hI hIS hIL
      (envWfA_normCtorType hW) (envWfA_normClosed hW) hR hρ hK
      (envSemFamStepA_of_indg hInd) (envSemCtorStepA_of_ctorg (envSemCtorA_of_indg hInd))
      (envSemRecStepA_of_recg hRec) hW (prefixA_refl E)
      (ctorClosedA_refl E)
      r m ⟨m, hres⟩ hres

end Discharge

#print axioms envSemClauseA_rigidPolyg
#print axioms envSemFamStepA_of_indg
#print axioms envSemCtorStepA_of_ctorg
#print axioms envSemRecStepA_of_recg
#print axioms envSemAt_groupAg
#print axioms envSemAt_of_envWfAg
#print axioms envSemA_of_envWfAg

end Rcic.Declarative.Ann
