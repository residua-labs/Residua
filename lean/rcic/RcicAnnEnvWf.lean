import rcic.RcicAnnRecView

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

The induction of M2-e (4) (`envSemAt_of_envWfA`) discharges the semantic clause
for every member but the families, the constructors and the recursors: the arity-`0`
members (their derivations read at the ambient arity through `hasTyA_instLevels` at
`[]`). A polymorphic RIGID member's clause holds by REFLECTION at every pair of `=ₙ`
level lists (`envSemClauseA_rigidPoly`): the type's validity at each instantiation
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
reach them; their clause is `EnvSemIndA`, a hypothesis. Since M2-f (4a) they enter
as one group step; M2-f (4b)/(4c) build their clause there by telescope introduction
(`telIntroA`): the induction carries constructor closure (`CtorClosedA`, the census) and
takes the family's clause AT ITS STEP from the base's clauses (`EnvSemFamStepA`, proved in
`RcicAnnFamSem`) and the constructors' at theirs, with the family's in hand (`EnvSemCtorStepA`,
proved in `RcicAnnCtorSem`); `EnvSemIndA` gives both. What remains is `EnvSemRecA`,
the recursors' clause (M2-f (5) / M3's content); over an environment without
families, constructors or recursors (`NoFamA`, `NoRecA`) the two Type-level rows
hold with no semantic hypothesis at all.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the environment judgment -/

/-- environment well-formedness on the copy, in the polymorphic model: every
    member typed under its own universe arity in the environment built so far; a
    family with its constructors as one `group` step (their views in the base),
    or with its derived recursor too (`groupRec`, M2-f (5a)). -/
inductive EnvWfA (I : IotaIfaceA) : ResolvedEnvA → Type
  | empty : EnvWfA I emptyEnvA
  | axiomM {arity : Nat} (E : ResolvedEnvA) (r : Nat) (A : ExprA) (u : Level)
      (hE : EnvWfA I E) (hfresh : E.members r = none)
      (hA : HasTyA E I arity [] A (.sort u))
      (hcl : ∀ k, liftA k 1 A = A) (hlvl : exprLevelsBoundedA arity A = true) :
      EnvWfA I (extendEnvA E r ⟨.axiomM, arity, A, none, 0, none⟩)
  | definitionM (E : ResolvedEnvA) (r : Nat) (A v : ExprA) (u : Level)
      (hE : EnvWfA I E) (hfresh : E.members r = none)
      (hA : HasTyA E I 0 [] A (.sort u)) (hv : HasTyA E I 0 [] v A)
      (hclA : ∀ k, liftA k 1 A = A) (hclv : ∀ k, liftA k 1 v = v)
      (hlvlA : exprLevelsBoundedA 0 A = true) (hlvlv : exprLevelsBoundedA 0 v = true) :
      EnvWfA I (extendEnvA E r ⟨.definitionM, 0, A, some v, 0, none⟩)
  | theoremM (E : ResolvedEnvA) (r : Nat) (A p : ExprA)
      (hE : EnvWfA I E) (hfresh : E.members r = none)
      (hA : HasTyA E I 0 [] A (.sort .zero)) (hp : HasTyA E I 0 [] p A)
      (hclA : ∀ k, liftA k 1 A = A) (hclp : ∀ k, liftA k 1 p = p)
      (hlvlA : exprLevelsBoundedA 0 A = true) (hlvlp : exprLevelsBoundedA 0 p = true) :
      EnvWfA I (extendEnvA E r ⟨.theoremM, 0, A, some p, 0, none⟩)
  | opaqueM (E : ResolvedEnvA) (r : Nat) (A v : ExprA) (u : Level)
      (hE : EnvWfA I E) (hfresh : E.members r = none)
      (hA : HasTyA E I 0 [] A (.sort u)) (hv : HasTyA E I 0 [] v A)
      (hclA : ∀ k, liftA k 1 A = A) (hclv : ∀ k, liftA k 1 v = v)
      (hlvlA : exprLevelsBoundedA 0 A = true) (hlvlv : exprLevelsBoundedA 0 v = true) :
      EnvWfA I (extendEnvA E r ⟨.opaqueM, 0, A, some v, 0, none⟩)
  | group (E : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) (u : Level)
      (hE : EnvWfA I E) (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
      (hclT : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA)
      (hT : HasTyA E I fm.arity [] fm.mtypeA (.sort u))
      (hlvl : exprLevelsBoundedA fm.arity fm.mtypeA = true)
      (fv : FamViewA fm) (cs : List (GroupCtorA I E f fm fv))
      (hfresh : GroupFreshA E f fm (cs.map GroupCtorA.entry)) :
      EnvWfA I (groupEnvA E f fm (cs.map GroupCtorA.entry))
  /-- M2-f (5a): a group WITH its derived recursor (05 §1, §3, §13): the group's premises, the
      constructors at `f + 1, …, f + k` in candidate order (05 §3 member order, which the concrete
      ι reads: `iotaGroupA`), and the recursor at `f + 1 + k` with its view (`GroupRecA`: the
      stored type built from the views, typed in the DerivationScope). -/
  | groupRec (E : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) (u : Level)
      (hE : EnvWfA I E) (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
      (hclT : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA)
      (hT : HasTyA E I fm.arity [] fm.mtypeA (.sort u))
      (hlvl : exprLevelsBoundedA fm.arity fm.mtypeA = true)
      (fv : FamViewA fm) (cs : List (GroupCtorA I E f fm fv))
      (hfresh : GroupFreshA E f fm (cs.map GroupCtorA.entry))
      (hlayout : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length)
      (rec : GroupRecA I E f fm fv cs)
      (hrfresh : (groupEnvA E f fm (cs.map GroupCtorA.entry)).members (f + 1 + cs.length) = none) :
      EnvWfA I (groupRecEnvA cs rec)

section WfProps
variable {I : IotaIfaceA}

/-- `EnvClosedA` is a theorem over `EnvWfA` (main's F-04 on the copy). -/
theorem envWfA_closed : {E : ResolvedEnvA} → EnvWfA I E → EnvClosedA E
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiomM E r A _ hE _ _ hcl _ => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨hcl, fun _ hb => Option.noConfusion hb⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_closed hE r' m' hm'
  | _, .definitionM E r A v _ hE _ _ _ hclA hclv _ _ => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨hclA, fun _ hb => by cases hb; exact hclv⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_closed hE r' m' hm'
  | _, .theoremM E r A p hE _ _ _ hclA hclp _ _ => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨hclA, fun _ hb => by cases hb; exact hclp⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_closed hE r' m' hm'
  | _, .opaqueM E r A v _ hE _ _ _ hclA hclv _ _ => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨hclA, fun _ hb => by cases hb; exact hclv⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_closed hE r' m' hm'
  | _, .group _ _ _ _ hE _ hnobody hclT _ _ _ cs _ => fun r' m' hm' => by
      rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
      · exact ⟨hclT, fun _ hb => by rw [hnobody] at hb; exact Option.noConfusion hb⟩
      · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
        have hm : c.member = m' := congrArg Prod.snd hce
        subst hm
        exact ⟨c.hclT, fun _ hb => by rw [c.hnobody] at hb; exact Option.noConfusion hb⟩
      · exact envWfA_closed hE r' m' hb
  | _, .groupRec _ f _ _ hE _ hnobody hclT _ _ _ cs _ _ rec _ => fun r' m' hm' => by
      unfold groupRecEnvA at hm'
      by_cases hr : r' = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨rec.hclT, fun _ hb => by rw [rec.hnobody] at hb; exact Option.noConfusion hb⟩
      · rw [members_extendEnvA_ne _ _ _ hr] at hm'
        rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
        · exact ⟨hclT, fun _ hb => by rw [hnobody] at hb; exact Option.noConfusion hb⟩
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
          have hm : c.member = m' := congrArg Prod.snd hce
          subst hm
          exact ⟨c.hclT, fun _ hb => by rw [c.hnobody] at hb; exact Option.noConfusion hb⟩
        · exact envWfA_closed hE r' m' hb

/-- `EnvNormClosedA` is a theorem over `EnvWfA` (R-NoDeltaRec-3a): a constructor member's `normA`
    is closed. Under `noDelta` it is the stored type itself; `GroupCtorA.hnorm` is what the proof
    reads. -/
theorem envWfA_normClosed : {E : ResolvedEnvA} → EnvWfA I E → EnvNormClosedA E
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiomM E r A _ hE _ _ _ _ => fun r' m' hm' hmc T hT k => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normClosed hE r' m' hm' hmc T hT k
  | _, .definitionM E r A v _ hE _ _ _ _ _ _ _ => fun r' m' hm' hmc T hT k => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normClosed hE r' m' hm' hmc T hT k
  | _, .theoremM E r A p hE _ _ _ _ _ _ _ => fun r' m' hm' hmc T hT k => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normClosed hE r' m' hm' hmc T hT k
  | _, .opaqueM E r A v _ hE _ _ _ _ _ _ _ => fun r' m' hm' hmc T hT k => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normClosed hE r' m' hm' hmc T hT k
  | _, .group _ _ _ _ hE hcls _ _ _ _ _ cs _ => fun r' m' hm' hmc T hT k => by
      rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
      · rw [hcls] at hmc
        exact MemberClass.noConfusion hmc
      · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
        have hm : c.member = m' := congrArg Prod.snd hce
        subst hm
        obtain rfl := Option.some.inj (hT.symm.trans c.hnorm)
        exact c.hclN k
      · exact envWfA_normClosed hE r' m' hb hmc T hT k
  | _, .groupRec _ f _ _ hE hcls _ _ _ _ _ cs _ _ rec _ => fun r' m' hm' hmc T hT k => by
      unfold groupRecEnvA at hm'
      by_cases hr : r' = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        rw [rec.hcls] at hmc
        exact MemberClass.noConfusion hmc
      · rw [members_extendEnvA_ne _ _ _ hr] at hm'
        rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
        · rw [hcls] at hmc
          exact MemberClass.noConfusion hmc
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
          have hm : c.member = m' := congrArg Prod.snd hce
          subst hm
          obtain rfl := Option.some.inj (hT.symm.trans c.hnorm)
          exact c.hclN k
        · exact envWfA_normClosed hE r' m' hb hmc T hT k

/-- `EnvNormLevelsA` is a theorem over `EnvWfA` (R-NoDeltaRec-3b): a constructor member's `normA`
    is level-bounded at its arity, as `envWfA_normClosed` is for closedness. -/
theorem envWfA_normLevels : {E : ResolvedEnvA} → EnvWfA I E → EnvNormLevelsA E
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiomM E r A _ hE _ _ _ _ => fun r' m' hm' hmc T hT => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normLevels hE r' m' hm' hmc T hT
  | _, .definitionM E r A v _ hE _ _ _ _ _ _ _ => fun r' m' hm' hmc T hT => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normLevels hE r' m' hm' hmc T hT
  | _, .theoremM E r A p hE _ _ _ _ _ _ _ => fun r' m' hm' hmc T hT => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normLevels hE r' m' hm' hmc T hT
  | _, .opaqueM E r A v _ hE _ _ _ _ _ _ _ => fun r' m' hm' hmc T hT => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normLevels hE r' m' hm' hmc T hT
  | _, .group _ _ _ _ hE hcls _ _ _ _ _ cs _ => fun r' m' hm' hmc T hT => by
      rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
      · rw [hcls] at hmc
        exact MemberClass.noConfusion hmc
      · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
        have hm : c.member = m' := congrArg Prod.snd hce
        subst hm
        obtain rfl := Option.some.inj (hT.symm.trans c.hnorm)
        exact c.hlvlN
      · exact envWfA_normLevels hE r' m' hb hmc T hT
  | _, .groupRec _ f _ _ hE hcls _ _ _ _ _ cs _ _ rec _ => fun r' m' hm' hmc T hT => by
      unfold groupRecEnvA at hm'
      by_cases hr : r' = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        rw [rec.hcls] at hmc
        exact MemberClass.noConfusion hmc
      · rw [members_extendEnvA_ne _ _ _ hr] at hm'
        rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
        · rw [hcls] at hmc
          exact MemberClass.noConfusion hmc
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
          have hm : c.member = m' := congrArg Prod.snd hce
          subst hm
          obtain rfl := Option.some.inj (hT.symm.trans c.hnorm)
          exact c.hlvlN
        · exact envWfA_normLevels hE r' m' hb hmc T hT

/-- `EnvNormCtorTypeA` is a theorem over `EnvWfA` (R-NoDeltaRec-4d-iii): a constructor member's
    `normA` is the view-built `ctorTypeA` — `GroupCtorA.hnorm` is what the proof reads. -/
theorem envWfA_normCtorType : {E : ResolvedEnvA} → EnvWfA I E → EnvNormCtorTypeA E
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiomM E r A _ hE _ _ _ _ => fun r' m' hm' hmc T hT => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normCtorType hE r' m' hm' hmc T hT
  | _, .definitionM E r A v _ hE _ _ _ _ _ _ _ => fun r' m' hm' hmc T hT => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normCtorType hE r' m' hm' hmc T hT
  | _, .theoremM E r A p hE _ _ _ _ _ _ _ => fun r' m' hm' hmc T hT => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normCtorType hE r' m' hm' hmc T hT
  | _, .opaqueM E r A v _ hE _ _ _ _ _ _ _ => fun r' m' hm' hmc T hT => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hT
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_normCtorType hE r' m' hm' hmc T hT
  | _, .group _ f _ _ hE hcls _ _ _ _ fv cs _ => fun r' m' hm' hmc T hT => by
      rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
      · rw [hcls] at hmc
        exact MemberClass.noConfusion hmc
      · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
        have hm : c.member = m' := congrArg Prod.snd hce
        subst hm
        obtain rfl := Option.some.inj (hT.symm.trans c.hnorm)
        obtain ⟨ls', hls'⟩ := spineHeadRefA_some
          (spineHeadRefA_piBodyA_ctorTypeA f _ _ _ _ _)
        exact ⟨f, ls', hls'⟩
      · exact envWfA_normCtorType hE r' m' hb hmc T hT
  | _, .groupRec _ f _ _ hE hcls _ _ _ _ fv cs _ _ rec _ => fun r' m' hm' hmc T hT => by
      unfold groupRecEnvA at hm'
      by_cases hr : r' = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        rw [rec.hcls] at hmc
        exact MemberClass.noConfusion hmc
      · rw [members_extendEnvA_ne _ _ _ hr] at hm'
        rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
        · rw [hcls] at hmc
          exact MemberClass.noConfusion hmc
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
          have hm : c.member = m' := congrArg Prod.snd hce
          subst hm
          obtain rfl := Option.some.inj (hT.symm.trans c.hnorm)
          obtain ⟨ls', hls'⟩ := spineHeadRefA_some
            (spineHeadRefA_piBodyA_ctorTypeA f _ _ _ _ _)
          exact ⟨f, ls', hls'⟩
        · exact envWfA_normCtorType hE r' m' hb hmc T hT

/-- `EnvLevelsA` is a theorem over `EnvWfA`: every member level-bounded by its arity. -/
theorem envWfA_levels : {E : ResolvedEnvA} → EnvWfA I E → EnvLevelsA E
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiomM E r A _ hE _ _ _ hlvl => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨hlvl, fun _ hb => Option.noConfusion hb⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_levels hE r' m' hm'
  | _, .definitionM E r A v _ hE _ _ _ _ _ hlvlA hlvlv => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨hlvlA, fun _ hb => by cases hb; exact hlvlv⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_levels hE r' m' hm'
  | _, .theoremM E r A p hE _ _ _ _ _ hlvlA hlvlp => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨hlvlA, fun _ hb => by cases hb; exact hlvlp⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_levels hE r' m' hm'
  | _, .opaqueM E r A v _ hE _ _ _ _ _ hlvlA hlvlv => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨hlvlA, fun _ hb => by cases hb; exact hlvlv⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_levels hE r' m' hm'
  | _, .group _ _ _ _ hE _ hnobody _ _ hlvl _ cs _ => fun r' m' hm' => by
      rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
      · exact ⟨hlvl, fun _ hb => by rw [hnobody] at hb; exact Option.noConfusion hb⟩
      · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
        have hm : c.member = m' := congrArg Prod.snd hce
        subst hm
        exact ⟨c.hlvl, fun _ hb => by rw [c.hnobody] at hb; exact Option.noConfusion hb⟩
      · exact envWfA_levels hE r' m' hb
  | _, .groupRec _ f _ _ hE _ hnobody _ _ hlvl _ cs _ _ rec _ => fun r' m' hm' => by
      unfold groupRecEnvA at hm'
      by_cases hr : r' = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨rec.hlvl, fun _ hb => by rw [rec.hnobody] at hb; exact Option.noConfusion hb⟩
      · rw [members_extendEnvA_ne _ _ _ hr] at hm'
        rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
        · exact ⟨hlvl, fun _ hb => by rw [hnobody] at hb; exact Option.noConfusion hb⟩
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
          have hm : c.member = m' := congrArg Prod.snd hce
          subst hm
          exact ⟨c.hlvl, fun _ hb => by rw [c.hnobody] at hb; exact Option.noConfusion hb⟩
        · exact envWfA_levels hE r' m' hb

end WfProps

/-- the semantic clause for the RECURSORS only: their content (M2-f / M3), the one
    hypothesis the discharge below leaves standing. -/
def EnvSemRecA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .recursorM → EnvSemClauseA E I n ρ₀ r m

/-- the semantic clause for the FAMILIES AND CONSTRUCTORS (M2-f (3b)): a family
    application has the `fam` clause, so a family is no longer a stuck-typed neutral,
    and a constructor is no longer an extended neutral (its applications are the
    clause's constructor disjunct); their self-relatedness is M2-f (4)'s content
    (`telIntroA`), a hypothesis until then. -/
def EnvSemIndA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → (m.mclass = .inductiveM ∨ m.mclass = .constructorM) →
    EnvSemClauseA E I n ρ₀ r m

/-- an environment without recursors. -/
def NoRecA (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m → m.mclass ≠ .recursorM

/-- an environment without families and without constructors. -/
def NoFamA (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m → m.mclass ≠ .inductiveM ∧ m.mclass ≠ .constructorM

/-- R-PropElimOnly (M2-f (0) Decision (2)): every recursor of a Prop-profile family with a
    constructor eliminates into `Prop` only — its motive's codomain sort is `zero` syntactically. A
    premise of the recursors' clause, NEVER a conjunct of `EnvWfA` (it is a policy, not the judgment).
    The recursor's family and motive are read off its type: the family from the last binder's domain
    (the major's), the motive from the binder after the family's parameters (05 §11). A recursor right
    after its family (`r = f + 1`, 05 §3's layout of a group without constructors, `False`) is exempt
    (O1-a): there ι never fires and the major arm is off, so the clause relates its applications by
    reflection at any motive universe. So is the recursor of a unit group (`unitGroupA`, O1-b-1): there
    the head step reads no major (K-unit), and the clause relates its applications through the minor. -/
def PropElimOnlyA (E : ResolvedEnvA) : Prop :=
  ∀ (r : Nat) (rm : CheckedMemberA) (D : ExprA) (f : Nat) (ls : List Level) (fm : CheckedMemberA)
    (u₀ : Level), E.members r = some rm → rm.mclass = .recursorM →
    (piDomsA rm.mtypeA).getLast? = some D → (appsSpineA D).1 = .const f ls →
    E.members f = some fm → fm.mclass = .inductiveM → piBodyA fm.mtypeA = .sort u₀ → UniformProp u₀ →
    r ≠ f + 1 → unitGroupA r rm = false →
    ∀ M, (piDomsA rm.mtypeA)[fm.nparamsA]? = some M → piBodyA M = .sort .zero

/-- W-1 (c): `PropElimOnlyA` with the recursor of a STRUCT group exempt as well (`structGroupA`): there
    the head step reads no major either (the struct arm), and the clause relates its applications
    through the minor applied to the major's projections. -/
def PropElimStructA (E : ResolvedEnvA) : Prop :=
  ∀ (r : Nat) (rm : CheckedMemberA) (D : ExprA) (f : Nat) (ls : List Level) (fm : CheckedMemberA)
    (u₀ : Level), E.members r = some rm → rm.mclass = .recursorM →
    (piDomsA rm.mtypeA).getLast? = some D → (appsSpineA D).1 = .const f ls →
    E.members f = some fm → fm.mclass = .inductiveM → piBodyA fm.mtypeA = .sort u₀ → UniformProp u₀ →
    r ≠ f + 1 → unitGroupA r rm = false → structGroupA r rm = false →
    ∀ M, (piDomsA rm.mtypeA)[fm.nparamsA]? = some M → piBodyA M = .sort .zero

/-- the struct exemption only weakens the profile. -/
theorem propElimStructA_of_propElimOnlyA {E : ResolvedEnvA} (h : PropElimOnlyA E) : PropElimStructA E :=
  fun r rm D f ls fm u₀ hr hc hD hf hm hi hs hu hne hun _ M hM =>
    h r rm D f ls fm u₀ hr hc hD hf hm hi hs hu hne hun M hM

/-- every family is parameter-free: the scope of M2-f (5)'s recursors' clause. M2-f (6c) lifted it
    (the `fam` clause carries the parameter coherence, M2-f (6)); no theorem on the copy assumes it. -/
def NoParamsA (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .inductiveM → m.nparamsA = 0

theorem envSemIndA_of_noFam {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (h : NoFamA E) : EnvSemIndA E I n ρ₀ :=
  fun r m hres hind => hind.elim (fun h' => absurd h' (h r m hres).1) (fun h' => absurd h' (h r m hres).2)

theorem envSemRecA_of_noRec {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (h : NoRecA E) : EnvSemRecA E I n ρ₀ :=
  fun r m hres hrec => absurd hrec (h r m hres)

/-! ## (2) the clause at a polymorphic rigid member -/

section Poly
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- an arity-`0` derivation read at the ambient arity: instantiation at `[]`. -/
def hasTyA_arity0 {E₀ : ResolvedEnvA} (hEL : EnvLevelsA E₀) (hIL : IotaLevelsA I) {e A : ExprA}
    (h : HasTyA E₀ I 0 [] e A) : HasTyA E₀ I n [] e A := by
  have := hasTyA_instLevels hEL hIL (ls := []) (n := n) rfl rfl h
  rw [instantiateLevelsA_nil, instantiateLevelsA_nil] at this
  exact this

/-- the clause at a polymorphic RIGID member (no body, not a recursor): by
    reflection at every pair of `=ₙ` level lists, from the type's validity at each
    instantiation and the level-irrelevance conversion between two instantiations. -/
theorem envSemClauseA_rigidPoly (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m) (hnobody : m.bodyA = none)
    (hnr : m.mclass ≠ .recursorM) (hni : m.mclass ≠ .inductiveM) (hnc : m.mclass ≠ .constructorM)
    {u : Level}
    (hT : ∀ ls : List Level, ls.length = m.arity → levelsBounded n ls = true →
      ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
        LRRelA E I n ρ₀ k Δ (.sort (instLevel ls u)) (instantiateLevelsA ls m.mtypeA)
          (instantiateLevelsA ls m.mtypeA))
    (hc : ∀ ls ls' : List Level, ls.length = m.arity → ls'.length = m.arity →
      levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
      Nonempty (ConvA E I n [] (instantiateLevelsA ls m.mtypeA) (instantiateLevelsA ls' m.mtypeA)
        (.sort (instLevel ls u)))) :
    EnvSemClauseA E I n ρ₀ r m := by
  intro ls ls' hlen hwf hwf' heq
  have hlen' : ls'.length = m.arity := (eqNList_length ls ls' heq).symm.trans hlen
  obtain ⟨k₁, h₁⟩ := hT ls hlen hwf
  obtain ⟨k₂, h₂⟩ := hT ls' hlen' hwf'
  refine ⟨max k₁ k₂, fun k hk Δ hΔ => ?_⟩
  obtain ⟨_, hval, _, hty, _, _⟩ := LRRelA_sort_elim (h₁ k (le_max_of_le₁ hk) Δ hΔ)
  obtain ⟨_, _, _, hty', _, _⟩ := LRRelA_sort_elim (h₂ k (le_max_of_le₂ hk) Δ hΔ)
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
  exact LRRelA_reflect hE hI hval (neutKA_const hR hres (Or.inr hnobody) hnr hni hnc Δ ls)
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

/-- every constructor's family is a member. -/
def CtorFamInA (E : ResolvedEnvA) : Prop :=
  ∀ c cm f, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
    domA E f

/-- `E₀` is constructor-closed in `E`: a constructor of `E` whose family is in `E₀` is in `E₀`. -/
def CtorClosedA (E₀ E : ResolvedEnvA) : Prop :=
  ∀ c cm f, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
    domA E₀ f → E₀.members c = some cm

theorem ctorClosedA_refl (E : ResolvedEnvA) : CtorClosedA E E :=
  fun _ _ _ h _ _ _ => h

theorem domA_extendEnvA {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} {r' : Nat}
    (h : domA E r') : domA (extendEnvA E r m) r' := by
  by_cases hr : r' = r
  · subst hr; exact ⟨m, members_extendEnvA_self E r' m⟩
  · obtain ⟨m', hm'⟩ := h
    exact ⟨m', by rw [members_extendEnvA_ne E r m hr]; exact hm'⟩

theorem domA_groupEnvA {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {r' : Nat}
    (h : domA E r') : (cs : List (Nat × CheckedMemberA)) → domA (groupEnvA E f fm cs) r'
  | [] => domA_extendEnvA h
  | _ :: cs => domA_extendEnvA (domA_groupEnvA h cs)

theorem domA_groupEnvA_family {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} :
    (cs : List (Nat × CheckedMemberA)) → domA (groupEnvA E f fm cs) f
  | [] => ⟨fm, members_extendEnvA_self E f fm⟩
  | _ :: cs => domA_extendEnvA (domA_groupEnvA_family cs)

/-- a step that adds no constructor keeps every constructor's family a member. -/
theorem ctorFamInA_extend {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA} (h : CtorFamInA E)
    (hm : m.mclass ≠ .constructorM) : CtorFamInA (extendEnvA E r m) := by
  intro c cm f hc hk hf
  by_cases hr : c = r
  · subst hr; rw [members_extendEnvA_self] at hc; cases hc; exact absurd hk hm
  · rw [members_extendEnvA_ne E r m hr] at hc; exact domA_extendEnvA (h c cm f hc hk hf)

/-- a group's environment keeps every constructor's family a member: a group constructor's family
    is the group's. -/
theorem ctorFamInA_groupA {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (ih : CtorFamInA E₀) (hcls : fm.mclass = .inductiveM) (cs : List (GroupCtorA I E₀ f fm fv)) :
    CtorFamInA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) := fun c cm f' hc hk hf => by
  rcases members_groupEnvA _ c cm hc with ⟨_, rfl⟩ | hin | hb
  · rw [hcls] at hk; cases hk
  · obtain ⟨gc, _, hge⟩ := List.mem_map.mp hin
    have hm : gc.member = cm := congrArg Prod.snd hge
    subst hm
    rw [gc.view.famRef] at hf
    cases hf
    exact domA_groupEnvA_family _
  · exact domA_groupEnvA (ih c cm f' hb hk hf) _

theorem ctorFamInA_of_envWfA : {E : ResolvedEnvA} → EnvWfA I E → CtorFamInA E
  | _, .empty => fun _ _ _ h => Option.noConfusion h
  | _, .axiomM _ _ _ _ hE _ _ _ _ =>
      ctorFamInA_extend (ctorFamInA_of_envWfA hE) (fun h => MemberClass.noConfusion h)
  | _, .definitionM _ _ _ _ _ hE _ _ _ _ _ _ _ =>
      ctorFamInA_extend (ctorFamInA_of_envWfA hE) (fun h => MemberClass.noConfusion h)
  | _, .theoremM _ _ _ _ hE _ _ _ _ _ _ _ =>
      ctorFamInA_extend (ctorFamInA_of_envWfA hE) (fun h => MemberClass.noConfusion h)
  | _, .opaqueM _ _ _ _ _ hE _ _ _ _ _ _ _ =>
      ctorFamInA_extend (ctorFamInA_of_envWfA hE) (fun h => MemberClass.noConfusion h)
  | _, .group _ _ _ _ hE hcls _ _ _ _ _ cs _ => ctorFamInA_groupA (ctorFamInA_of_envWfA hE) hcls cs
  | _, .groupRec _ _ _ _ hE hcls _ _ _ _ _ cs _ _ rec _ =>
      ctorFamInA_extend (ctorFamInA_groupA (ctorFamInA_of_envWfA hE) hcls cs)
        (fun h => by rw [rec.hcls] at h; cases h)

/-- closure descends through a step that adds no constructor. -/
theorem ctorClosedA_extend_pred {E₀ E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (hm : m.mclass ≠ .constructorM) (h : CtorClosedA (extendEnvA E₀ r m) E) : CtorClosedA E₀ E := by
  intro c cm f hc hk hf hd
  have h1 := h c cm f hc hk hf (domA_extendEnvA hd)
  by_cases hr : c = r
  · subst hr; rw [members_extendEnvA_self] at h1; cases h1; exact absurd hk hm
  · rw [members_extendEnvA_ne E₀ r m hr] at h1; exact h1

/-- closure descends through a group: its new constructors have its family, fresh below. -/
theorem ctorClosedA_group_pred {E₀ E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)} (hcls : fm.mclass = .inductiveM)
    (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (h : CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E) : CtorClosedA E₀ E := by
  intro c cm f' hc hk hf hd
  have h1 := h c cm f' hc hk hf (domA_groupEnvA hd _)
  rcases members_groupEnvA _ c cm h1 with ⟨_, rfl⟩ | hin | hb
  · rw [hcls] at hk; cases hk
  · obtain ⟨gc, _, hge⟩ := List.mem_map.mp hin
    have hm : gc.member = cm := congrArg Prod.snd hge
    subst hm
    rw [gc.view.famRef] at hf
    cases hf
    obtain ⟨m', hm'⟩ := hd
    rw [hfresh.base] at hm'
    cases hm'
  · exact hb

/-- closure descends through a group with its recursor (the recursor is not a constructor). -/
theorem ctorClosedA_groupRec_pred {E₀ E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)} {rec : GroupRecA I E₀ f fm fv cs}
    (h : CtorClosedA (groupRecEnvA cs rec) E) :
    CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E :=
  ctorClosedA_extend_pred (fun h' => by rw [rec.hcls] at h'; cases h') h

/-- THE CENSUS: at a group step, constructor-closed in `E`, a constructor of `E` whose family is
    the group's is one of the group's constructors. -/
theorem groupCensusA {E₀ E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    {cs : List (GroupCtorA I E₀ f fm fv)} (hcls : fm.mclass = .inductiveM)
    (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry)) (hin₀ : CtorFamInA E₀)
    (h : CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    {c : Nat} {cm : CheckedMemberA} (hc : E.members c = some cm) (hk : cm.mclass = .constructorM)
    (hf : memberFamRefA cm = some f) : ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm := by
  have h1 := h c cm f hc hk hf (domA_groupEnvA_family _)
  rcases members_groupEnvA _ c cm h1 with ⟨_, rfl⟩ | hin | hb
  · rw [hcls] at hk; cases hk
  · obtain ⟨gc, hgc, hge⟩ := List.mem_map.mp hin
    exact ⟨gc, hgc, congrArg Prod.fst hge, congrArg Prod.snd hge⟩
  · obtain ⟨m', hm'⟩ := hin₀ c cm f hb hk hf
    rw [hfresh.base] at hm'
    cases hm'


/-- a group's family is a member of the group's environment. -/
theorem members_groupEnvA_family {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} :
    {cs : List (Nat × CheckedMemberA)} → GroupFreshA E f fm cs → (groupEnvA E f fm cs).members f = some fm
  | [], _ => members_extendEnvA_self E f fm
  | c :: _, h => by
      have ih := members_groupEnvA_family h.1
      have hne : f ≠ c.1 := fun he => by
        have h2 := h.2
        rw [← he, ih] at h2
        cases h2
      show (extendEnvA (groupEnvA E f fm _) c.1 c.2).members f = some fm
      rw [members_extendEnvA_ne _ c.1 c.2 hne]
      exact ih

end Census

/-! ## (2c) the clauses the discharge consumes -/

section Steps
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the clause at a group's FAMILY, at its step (M2-f (4b)): from the base's clauses, the group
    constructor-closed in `E`. `RcicAnnFamSem` proves it under the small-index profile. -/
def EnvSemFamStepA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ (E₀ : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) (u : Level), EnvWfA I E₀ →
    fm.mclass = .inductiveM → fm.bodyA = none → (∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) →
    HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u) →
    ∀ (fv : FamViewA fm) (cs : List (GroupCtorA I E₀ f fm fv)),
      GroupFreshA E₀ f fm (cs.map GroupCtorA.entry) →
      PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E →
      CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E →
      EnvSemAt E I n ρ₀ (domA E₀) → EnvSemClauseA E I n ρ₀ f fm

/-- the clause at the CONSTRUCTORS (M2-f (4c)'s content). -/
def EnvSemCtorA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .constructorM → EnvSemClauseA E I n ρ₀ r m

theorem envSemFamStepA_of_ind (hInd : EnvSemIndA E I n ρ₀) : EnvSemFamStepA E I n ρ₀ :=
  fun _ _ _ _ _ hcls _ _ _ _ _ hfresh hpre _ _ =>
    hInd _ _ (hpre _ _ (members_groupEnvA_family hfresh)) (Or.inl hcls)

theorem envSemCtorA_of_ind (hInd : EnvSemIndA E I n ρ₀) : EnvSemCtorA E I n ρ₀ :=
  fun r m hres hc => hInd r m hres (Or.inr hc)

/-- the clause at a group's CONSTRUCTORS, at its step (M2-f (4c)): from the base's clauses and the
    family's, the group constructor-closed in `E`. `RcicAnnCtorSem` proves it. -/
def EnvSemCtorStepA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ (E₀ : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) (u : Level), EnvWfA I E₀ →
    fm.mclass = .inductiveM → fm.bodyA = none → (∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) →
    HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u) →
    ∀ (fv : FamViewA fm) (cs : List (GroupCtorA I E₀ f fm fv)),
      GroupFreshA E₀ f fm (cs.map GroupCtorA.entry) →
      PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E →
      CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E →
      EnvSemAt E I n ρ₀ (domA (extendEnvA E₀ f fm)) →
      ∀ gc ∈ cs, EnvSemClauseA E I n ρ₀ gc.ref gc.member

/-- a group's constructor is a member of the group's environment. -/
theorem members_groupEnvA_ctor {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} :
    {cs : List (GroupCtorA I E₀ f fm fv)} → GroupFreshA E₀ f fm (cs.map GroupCtorA.entry) →
    ∀ {gc : GroupCtorA I E₀ f fm fv}, gc ∈ cs →
      (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)).members gc.ref = some gc.member
  | [], _, _, h => nomatch h
  | c :: cs, hf, gc, h => by
      show (extendEnvA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) c.ref c.member).members gc.ref =
        some gc.member
      rcases List.mem_cons.mp h with rfl | hin
      · exact members_extendEnvA_self _ _ _
      · have ih := members_groupEnvA_ctor hf.1 hin
        have hne : gc.ref ≠ c.ref := fun he => by
          have h2 := hf.2
          rw [show (GroupCtorA.entry c).1 = c.ref from rfl, ← he, ih] at h2
          cases h2
        rw [members_extendEnvA_ne _ _ _ hne]
        exact ih

/-- the family's own environment is a prefix of the group's. -/
theorem prefixA_extend_groupEnvA {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} :
    {cs : List (Nat × CheckedMemberA)} → GroupFreshA E₀ f fm cs →
    PrefixA (extendEnvA E₀ f fm) (groupEnvA E₀ f fm cs)
  | [], _ => prefixA_refl _
  | c :: _, h => prefixA_trans (prefixA_extend_groupEnvA h.1) (prefixA_extend _ c.1 c.2 h.2)

theorem envSemCtorStepA_of_ctor (hCtor : EnvSemCtorA E I n ρ₀) : EnvSemCtorStepA E I n ρ₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ hfresh hpre _ _ gc hgc =>
    hCtor gc.ref gc.member (hpre _ _ (members_groupEnvA_ctor hfresh hgc)) gc.hcls

/-- the clause at a group's RECURSOR, at its step (M2-f (5)): from the clauses of the base, the
    family and the constructors, the group constructor-closed in `E`. `RcicAnnRecSem` proves it
    under the profile (M2-f (5b)). -/
def EnvSemRecStepA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
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
      EnvSemAt E I n ρ₀ (domA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))) →
      EnvSemClauseA E I n ρ₀ (f + 1 + cs.length) rec.member

/-- a group's recursor is a member of the group's environment with its recursor. -/
theorem members_groupRecEnvA {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (cs : List (GroupCtorA I E₀ f fm fv)) (rec : GroupRecA I E₀ f fm fv cs) :
    (groupRecEnvA cs rec).members (f + 1 + cs.length) = some rec.member :=
  members_extendEnvA_self _ _ _

theorem envSemRecStepA_of_rec (hRec : EnvSemRecA E I n ρ₀) : EnvSemRecStepA E I n ρ₀ :=
  fun _ _ _ _ _ _ _ _ _ _ cs _ _ rec _ hpre _ _ =>
    hRec _ rec.member (hpre _ _ (members_groupRecEnvA cs rec)) rec.hcls

end Steps

/-! ## (3) the induction on the environment -/

section Discharge
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a group's members at the group's step: the family from `EnvSemFamStepA`, the constructors
    from `EnvSemCtorStepA` with the family's clause in hand, the base from the induction. -/
theorem envSemAt_groupA (hFam : EnvSemFamStepA E I n ρ₀) (hCtor : EnvSemCtorStepA E I n ρ₀)
    {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {u : Level} (hW : EnvWfA I E₀)
    (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
    (hclT : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (fv : FamViewA fm) (cs : List (GroupCtorA I E₀ f fm fv))
    (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hpre : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    (hclo : CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    (ih : EnvSemAt E I n ρ₀ (domA E₀)) :
    EnvSemAt E I n ρ₀ (domA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))) := by
  have hfamC := hFam E₀ f fm u hW hcls hnobody hclT hT fv cs hfresh hpre hclo ih
  have ihF : EnvSemAt E I n ρ₀ (domA (extendEnvA E₀ f fm)) := fun r m hD hres => by
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

/-- `EnvSemA` on the members of a well-formed prefix `E₀` of `E`, constructor-closed in `E`, in
    `E`: by induction on `E₀`'s construction, closure descending with it; arity-`0` members by
    reflection or δ-expansion (M2-e (4)); a group's family from `EnvSemFamStepA` at its step,
    where only the base's clauses are in hand (M2-f (4b), `RcicAnnFamSem`), its constructors from
    `EnvSemCtorA` (M2-f (4c)); recursors from `EnvSemRecA`. -/
theorem envSemAt_of_envWfA (hE : EnvClosedA E) (hEL : EnvLevelsA E) (hI : IotaLiftA I)
    (hIS : IotaSubstA I) (hIL : IotaLevelsA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀)
    (hFam : EnvSemFamStepA E I n ρ₀) (hCtor : EnvSemCtorStepA E I n ρ₀) (hRec : EnvSemRecStepA E I n ρ₀) :
    {E₀ : ResolvedEnvA} → EnvWfA I E₀ → PrefixA E₀ E → CtorClosedA E₀ E → EnvSemAt E I n ρ₀ (domA E₀)
  | _, .empty, _, _ => fun _ _ hD _ => hD.elim fun _ hm => Option.noConfusion hm
  | _, .axiomM (arity := arity) E₀ r A u hW hfresh hA _ _, hpre, hclo => by
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_extend E₀ r _ hfresh) hpre
      have ih := envSemAt_of_envWfA hE hEL hI hIS hIL hEN hNC hR hρ hFam hCtor hRec hW hpre₀
        (ctorClosedA_extend_pred (fun h => MemberClass.noConfusion h) hclo)
      have harms := fundArmsA_at hE hI hIS hEN hNC hR hρ ih
      intro r' m' hD hres'
      by_cases hr : r' = r
      · rw [hr] at hres' ⊢
        have hm : E.members r = some ⟨.axiomM, arity, A, none, 0, none⟩ :=
          hpre r _ (members_extendEnvA_self E₀ r _)
        rw [hm] at hres'
        cases hres'
        apply envSemClauseA_rigidPoly hE hI hR hm rfl
          (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
          (fun h => MemberClass.noConfusion h)
        · intro ls hlen hwf
          exact fundArmA_nil (fundHasTyPrefixA hpre₀ harms.1 harms.2
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
      have ih := envSemAt_of_envWfA hE hEL hI hIS hIL hEN hNC hR hρ hFam hCtor hRec hW hpre₀
        (ctorClosedA_extend_pred (fun h => MemberClass.noConfusion h) hclo)
      have harms := fundArmsA_at hE hI hIS hEN hNC hR hρ ih
      intro r' m' hD hres'
      by_cases hr : r' = r
      · rw [hr] at hres' ⊢
        have hm : E.members r = some ⟨.definitionM, 0, A, some v, 0, none⟩ :=
          hpre r _ (members_extendEnvA_self E₀ r _)
        rw [hm] at hres'
        cases hres'
        obtain ⟨k₁, hT⟩ := fundArmA_nil (fundHasTyPrefixA hpre₀ harms.1 harms.2
          (hasTyA_arity0 (envWfA_levels hW) hIL hA))
        obtain ⟨k₂, hV⟩ := fundArmA_nil (fundHasTyPrefixA hpre₀ harms.1 harms.2
          (hasTyA_arity0 (envWfA_levels hW) hIL hv))
        exact envSemClauseA_def hE hI hm (k₀ := max k₁ k₂)
          (fun k hk Δ hΔ => hT k (Nat.le_trans (Nat.le_max_left _ _) hk) Δ hΔ)
          (fun k hk Δ hΔ => hV k (Nat.le_trans (Nat.le_max_right _ _) hk) Δ hΔ)
      · obtain ⟨m₀, hm₀⟩ := hD
        rw [members_extendEnvA_ne E₀ r _ hr] at hm₀
        exact ih r' m' ⟨m₀, hm₀⟩ hres'
  | _, .theoremM E₀ r A p hW hfresh hA _ _ _ _ _, hpre, hclo => by
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_extend E₀ r _ hfresh) hpre
      have ih := envSemAt_of_envWfA hE hEL hI hIS hIL hEN hNC hR hρ hFam hCtor hRec hW hpre₀
        (ctorClosedA_extend_pred (fun h => MemberClass.noConfusion h) hclo)
      have harms := fundArmsA_at hE hI hIS hEN hNC hR hρ ih
      intro r' m' hD hres'
      by_cases hr : r' = r
      · rw [hr] at hres' ⊢
        have hm : E.members r = some ⟨.theoremM, 0, A, some p, 0, none⟩ :=
          hpre r _ (members_extendEnvA_self E₀ r _)
        rw [hm] at hres'
        cases hres'
        obtain ⟨k₀, hT⟩ := fundArmA_nil (fundHasTyPrefixA hpre₀ harms.1 harms.2
          (hasTyA_arity0 (envWfA_levels hW) hIL hA))
        exact envSemClauseA_rigid hE hI hR hm rfl (Or.inl rfl)
          (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
          (fun h => MemberClass.noConfusion h) hT
      · obtain ⟨m₀, hm₀⟩ := hD
        rw [members_extendEnvA_ne E₀ r _ hr] at hm₀
        exact ih r' m' ⟨m₀, hm₀⟩ hres'
  | _, .opaqueM E₀ r A v u hW hfresh hA _ _ _ _ _, hpre, hclo => by
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_extend E₀ r _ hfresh) hpre
      have ih := envSemAt_of_envWfA hE hEL hI hIS hIL hEN hNC hR hρ hFam hCtor hRec hW hpre₀
        (ctorClosedA_extend_pred (fun h => MemberClass.noConfusion h) hclo)
      have harms := fundArmsA_at hE hI hIS hEN hNC hR hρ ih
      intro r' m' hD hres'
      by_cases hr : r' = r
      · rw [hr] at hres' ⊢
        have hm : E.members r = some ⟨.opaqueM, 0, A, some v, 0, none⟩ :=
          hpre r _ (members_extendEnvA_self E₀ r _)
        rw [hm] at hres'
        cases hres'
        obtain ⟨k₀, hT⟩ := fundArmA_nil (fundHasTyPrefixA hpre₀ harms.1 harms.2
          (hasTyA_arity0 (envWfA_levels hW) hIL hA))
        exact envSemClauseA_rigid hE hI hR hm rfl (Or.inl rfl)
          (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
          (fun h => MemberClass.noConfusion h) hT
      · obtain ⟨m₀, hm₀⟩ := hD
        rw [members_extendEnvA_ne E₀ r _ hr] at hm₀
        exact ih r' m' ⟨m₀, hm₀⟩ hres'
  | _, .group E₀ f fm u hW hcls hnobody hclT hT _ fv cs hfresh, hpre, hclo => by
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpre
      have ih := envSemAt_of_envWfA hE hEL hI hIS hIL hEN hNC hR hρ hFam hCtor hRec hW hpre₀
        (ctorClosedA_group_pred hcls hfresh hclo)
      exact envSemAt_groupA hFam hCtor hW hcls hnobody hclT hT fv cs hfresh hpre hclo ih
  | _, .groupRec E₀ f fm u hW hcls hnobody hclT hT _ fv cs hfresh hlay rec hrf, hpre, hclo => by
      have hpreG : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E :=
        prefixA_trans (prefixA_extend _ _ _ hrf) hpre
      have hcloG := ctorClosedA_groupRec_pred hclo
      have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpreG
      have ih := envSemAt_of_envWfA hE hEL hI hIS hIL hEN hNC hR hρ hFam hCtor hRec hW hpre₀
        (ctorClosedA_group_pred hcls hfresh hcloG)
      have ihG := envSemAt_groupA hFam hCtor hW hcls hnobody hclT hT fv cs hfresh hpreG hcloG ih
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
    recursors: a well-formed environment satisfies `EnvSemA` given the clause at
    its families and constructors (`EnvSemIndA`, M2-f (4)'s content) and at its
    recursors (`EnvSemRecA`). -/
theorem envSemA_of_envWfA (hW : EnvWfA I E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hInd : EnvSemIndA E I n ρ₀)
    (hRec : EnvSemRecA E I n ρ₀) : EnvSemA E I n ρ₀ :=
  fun r m hres =>
    envSemAt_of_envWfA (envWfA_closed hW) (envWfA_levels hW) hI hIS hIL
      (envWfA_normCtorType hW) (envWfA_normClosed hW) hR hρ
      (envSemFamStepA_of_ind hInd) (envSemCtorStepA_of_ctor (envSemCtorA_of_ind hInd))
      (envSemRecStepA_of_rec hRec) hW (prefixA_refl E)
      (ctorClosedA_refl E)
      r m ⟨m, hres⟩ hres

/-! ## (4) the rows over well-formed environments -/

theorem sortConvCharA_wf (hW : EnvWfA I E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hInd : EnvSemIndA E I n ρ₀)
    (hRec : EnvSemRecA E I n ρ₀) {Γ : LCtxA} {l₁ l₂ u : Level} (hΓ : CtxWfA E I n Γ)
    (h : ConvA E I n Γ (.sort l₁) (.sort l₂) (.sort u)) : eqN l₁ l₂ :=
  sortConvCharA (envWfA_closed hW) hI hIS (envWfA_normCtorType hW) (envWfA_normClosed hW) hR
    (envSemA_of_envWfA hW hI hIS hIL hR hρ hInd hRec) hρ hΓ h

theorem piConvInjA_wf (hW : EnvWfA I E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hInd : EnvSemIndA E I n ρ₀)
    (hRec : EnvSemRecA E I n ρ₀)
    {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level} {D' : ExprA} {u' : Level}
    {C' : ExprA} {v' w : Level} (hΓ : CtxWfA E I n Γ)
    (h : ConvA E I n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) :
    eqN u u' ∧ eqN v v' ∧ Nonempty (TyConvA E I n Γ D D') ∧
    Nonempty (TyConvA E I n (.assumption D :: Γ) C C') :=
  piConvInjA (envWfA_closed hW) hI hIS (envWfA_normCtorType hW) (envWfA_normClosed hW) hR
    (envSemA_of_envWfA hW hI hIS hIL hR hρ hInd hRec) hρ hΓ h

/-- WITHOUT FAMILIES, CONSTRUCTORS OR RECURSORS (axioms, definitions, theorems,
    opaque constants; no ι): the two Type-level rows with NO semantic hypothesis at
    all. Families and constructors left this row at M2-f (3b) (`NoFamA`); M2-f (4)
    returns them. -/
theorem sortConvCharA_noRec (hW : EnvWfA noIotaA E) (hNo : NoRecA E) (hNoF : NoFamA E)
    {Γ : LCtxA} {l₁ l₂ u : Level} (hΓ : CtxWfA E noIotaA n Γ)
    (h : ConvA E noIotaA n Γ (.sort l₁) (.sort l₂) (.sort u)) : eqN l₁ l₂ :=
  sortConvCharA_wf (ρ₀ := fun _ => 1) hW noIotaA_lift noIotaA_subst noIotaA_levels
    (noIotaA_recHead E) posValA_one (envSemIndA_of_noFam hNoF) (envSemRecA_of_noRec hNo) hΓ h

theorem piConvInjA_noRec (hW : EnvWfA noIotaA E) (hNo : NoRecA E) (hNoF : NoFamA E)
    {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level} {D' : ExprA} {u' : Level}
    {C' : ExprA} {v' w : Level} (hΓ : CtxWfA E noIotaA n Γ)
    (h : ConvA E noIotaA n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) :
    eqN u u' ∧ eqN v v' ∧ Nonempty (TyConvA E noIotaA n Γ D D') ∧
    Nonempty (TyConvA E noIotaA n (.assumption D :: Γ) C C') :=
  piConvInjA_wf (ρ₀ := fun _ => 1) hW noIotaA_lift noIotaA_subst noIotaA_levels
    (noIotaA_recHead E) posValA_one (envSemIndA_of_noFam hNoF) (envSemRecA_of_noRec hNo) hΓ h

end Discharge

#print axioms envWfA_closed
#print axioms envWfA_normClosed
#print axioms envWfA_levels
#print axioms envSemClauseA_rigidPoly
#print axioms ctorFamInA_of_envWfA
#print axioms ctorClosedA_extend_pred
#print axioms ctorClosedA_group_pred
#print axioms groupCensusA
#print axioms members_groupEnvA_family
#print axioms envSemFamStepA_of_ind
#print axioms members_groupEnvA_ctor
#print axioms prefixA_extend_groupEnvA
#print axioms envSemCtorStepA_of_ctor
#print axioms ctorFamInA_groupA
#print axioms ctorClosedA_groupRec_pred
#print axioms members_groupRecEnvA
#print axioms envSemRecStepA_of_rec
#print axioms envSemAt_groupA
#print axioms envSemAt_of_envWfA
#print axioms envSemA_of_envWfA
#print axioms sortConvCharA_wf
#print axioms piConvInjA_wf
#print axioms sortConvCharA_noRec
#print axioms piConvInjA_noRec
#print axioms propElimStructA_of_propElimOnlyA

end Rcic.Declarative.Ann
