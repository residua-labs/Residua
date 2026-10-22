import rcic.RcicAnnFrecPin

/-!
# R-NoFunRec class (a), second row: THE ACC-SHAPED FUNCTION-RECURSIVE PIN

`pinFrecEnvA` (RcicAnnFrecPin) is the W row: one `frec` field `Sort 0 → T` — a single inner
binder, tail the family unapplied (`shape = recursive 1`). This module is the Acc row of the
same class: `AccP : Sort 0 → Sort 1` is an INDEXED family and `intro`'s recursive field is
guarded by a hypothesis — `Π (y : Sort 0), R y x → AccP y`, two inner binders with the second
DEPENDING on the first (`Bs` nonempty, `shape = recursive 2`), the tail applied to the bound
element. The relation `R` is an opaque `axiomM` member at `9`, so `innerClean`/`rigid` hold
by member class, not by parameter bookkeeping.

The pin mirrors `RcicAnnFrecPin`: members, the views, `EnvWfA` via `axiomM` + `groupRec`,
`EnvSemA`, the firing, and the `EnvNoFunA`/`AnnEnvA` teeth.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- the ambient relation `R : Sort 0 → Sort 0 → Sort 0`, opaque (axiomM), at `9`. -/
def pinPropAccRelTyA : ExprA :=
  .pi (.sort .zero) (.succ .zero) (.pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero))
    (.imax (.succ .zero) (.succ .zero))

def pinPropAccRelA : CheckedMemberA := ⟨.axiomM, 0, pinPropAccRelTyA, none, 0, none⟩

def pinPropAccRelEnvA : ResolvedEnvA := extendEnvA emptyEnvA 9 pinPropAccRelA

theorem pinPropAccRelEnv_rel : pinPropAccRelEnvA.members 9 = some pinPropAccRelA := rfl

/-- `AccP : Π (_ : Sort 0), Sort 0`, one index, no parameters — Prop-valued. -/
def pinPropAccFamA : CheckedMemberA :=
  ⟨.inductiveM, 0, .pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero),
    none, 0, none⟩

/-- `intro`'s hypothesis domain `R y x`, in the inner-binder context `[y] ++ [x]`
    (y = bvar 0, x = bvar 1). -/
def pinPropAccGuardA : ExprA := .app (.app (.const 9 []) (.bvar 0)) (.bvar 1)

/-- `intro`'s function-recursive field: `Π (y : Sort 0), R y x → AccP y` — `Bs` carries the
    guard (a domain DEPENDING on the first inner binder), `idx` the tail's index `y`
    (in the tail's context `[guard, y] ++ [x]`, so `y = bvar 1`). -/
def pinPropAccFieldA : FieldA :=
  .frec (.sort .zero) (.succ .zero) [(pinPropAccGuardA, .zero)] [.bvar 1]

/-- `intro : Π (x : Sort 0), (Π (y : Sort 0), R y x → AccP y) → AccP x` at `11`, over the
    family at `10` — `x` is a plain field and the result's index, the recursive field is
    guarded by `R y x` and recurses at `y`. -/
def pinPropAccIntroA : CheckedMemberA :=
  ⟨.constructorM, 0,
    ctorTypeA 10 (canonLevelsA 0) .zero []
      [.plain (.sort .zero) (.succ .zero), pinPropAccFieldA] [.bvar 0],
    none, 0,
    some (ctorTypeA 10 (canonLevelsA 0) .zero []
      [.plain (.sort .zero) (.succ .zero), pinPropAccFieldA] [.bvar 0])⟩


/-- `R`'s type is closed — the `axiomM` step's side condition. -/
theorem pinPropAccRelTy_closed (k : Nat) : liftA k 1 pinPropAccRelTyA = pinPropAccRelTyA := rfl

/-- `R`'s type, derivable in any context — at the `imax` sort its pi-chain produces. -/
def pinPropAccRelTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n Γ pinPropAccRelTyA
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .pi Γ _ _ _ _ (.sort Γ .zero) (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))

/-- `R` at `9`, in any context. -/
def pinPropAccRelConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 9 = some pinPropAccRelA) :
    HasTyA E I n Γ (.const 9 []) pinPropAccRelTyA :=
  .const Γ 9 [] pinPropAccRelA _ h rfl rfl pinPropAccRelTyTy

/-- the family env: `R` at `9`, then `AccP` at `10`. -/
def pinPropAccFamEnvA : ResolvedEnvA := extendEnvA pinPropAccRelEnvA 10 pinPropAccFamA

theorem pinPropAccFamEnv_rel : pinPropAccFamEnvA.members 9 = some pinPropAccRelA := rfl
theorem pinPropAccFamEnv_fam : pinPropAccFamEnvA.members 10 = some pinPropAccFamA := rfl

/-- `AccP`'s type `Π (_ : Sort 0), Sort 0`, derivable in any context. -/
def pinPropAccFamTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n Γ pinPropAccFamA.mtypeA
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ _ _ _ _ (.sort Γ .zero) (.sort _ .zero)

/-- `AccP` at `10`, in any context. -/
def pinPropAccFamConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 10 = some pinPropAccFamA) :
    HasTyA E I n Γ (.const 10 []) pinPropAccFamA.mtypeA :=
  .const Γ 10 [] pinPropAccFamA _ h rfl rfl pinPropAccFamTyTy

/-- `AccP`'s family view: no parameters, one `Sort 0` index, sort `0` (Prop). -/
def pinPropAccFamViewA : FamViewA pinPropAccFamA where
  params := []
  indices := [(.sort .zero, .succ .zero)]
  sort := .zero
  stored := rfl
  nparams := rfl
  profile := .inl (fun _ => rfl)



/-- the guard `R y x` at `Sort 0`, in the concrete context `[y, x] ++ Γ` (`y` at `bvar 0`,
    `x` at `bvar 1`). The derivation is a plain `.app`-chain term so the contexts stay
    explicit. -/
def pinPropAccGuardTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h9 : E.members 9 = some pinPropAccRelA) :
    HasTyA E I n
      (.assumption (.sort .zero) :: .assumption (.sort .zero) :: Γ)
      pinPropAccGuardA (.sort .zero) :=
  .app _ _ (.bvar 1) (.sort .zero) (.sort .zero)
    (.succ .zero) (.succ .zero) (.succ .zero)
    (.sort _ .zero) (.sort _ .zero)
    (.app _ (.const 9 []) (.bvar 0) (.sort .zero)
      (.pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero))
      (.succ .zero) (.imax (.succ .zero) (.succ .zero))
      (.imax (.succ .zero) (.succ .zero))
      (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))
      (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))
      (pinPropAccRelConstTy h9)
      (.bvar _ 0 _ _ rfl (.sort _ .zero)))
    (.bvar _ 1 _ _ rfl (.sort _ .zero))


/-- `intro`'s stored type, typed in the family's extension scope (`pinPropAccFamEnvA`): the guarded
    recursion `Π (x : Sort 0), (Π (y : Sort 0), R y x → AccP y) → AccP x`. Every annotation is the
    level `ctorTypeA`/`piTelA` themselves record — the codomain's sort, the `imax` chain on nested
    binders; with `AccP` Prop-valued every tail contributes `zero`, so `imax _ 0` collapses. -/
def pinPropAccIntroTy {I : IotaIfaceA} :
    HasTyA pinPropAccFamEnvA I 0 [] pinPropAccIntroA.mtypeA
      (.sort (.imax (.succ .zero)
        (.imax (.imax (.succ .zero) (.imax .zero .zero)) .zero))) :=
  .pi [] _ _ _ _ (.sort [] .zero)
    (.pi _ _ _ _ _
      (.pi _ _ _ _ _ (.sort _ .zero)
        (.pi _ _ _ _ _ (pinPropAccGuardTy pinPropAccRelEnv_rel)
          (.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort .zero)
            (.succ .zero) (.succ .zero) (.succ .zero)
            (.sort _ .zero) (.sort _ .zero)
            (pinPropAccFamConstTy pinPropAccFamEnv_fam)
            (.bvar _ 1 _ _ rfl (.sort _ .zero)))))
      (.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort .zero)
        (.succ .zero) (.succ .zero) (.succ .zero)
        (.sort _ .zero) (.sort _ .zero)
        (pinPropAccFamConstTy pinPropAccFamEnv_fam)
        (.bvar _ 1 _ _ rfl (.sort _ .zero))))

/-- `intro`'s view: a plain `x : Sort 0` field, then the function-recursive field guarded by
    `R y x` recursing at `y`; the result is the family at `x`. -/
def pinPropAccIntroViewA (I : IotaIfaceA) :
    CtorViewA pinPropAccRelEnvA I 10 pinPropAccFamA pinPropAccFamViewA pinPropAccIntroA where
  mirrors := []
  fields := [.plain (.sort .zero) (.succ .zero), pinPropAccFieldA]
  res := [.bvar 0]
  stored := rfl
  mirrorsConv := .nil []
  typed :=
    .plain [] 0 _ _ _ _ (.sort [] .zero)
      (.frec _ 1 _ _ _ _ _ _
        (.plain _ 1 _ _ _ _ (.sort _ .zero)
          (.plain _ 2 _ _ _ _ (pinPropAccGuardTy pinPropAccRelEnv_rel)
            (.nil _ 3 _
              (.cons _ _ _ _ _ _
                (.bvar _ 1 _ _ rfl (.sort _ .zero))
                (.nil _)))))
        (.nil _ 1 _
          (.cons _ _ _ _ _ _
            (.bvar _ 0 _ _ rfl (.sort _ .zero))
            (.nil _))))
  univ := fun _ _ _ => Or.inl (fun _ => rfl)
  univI := fun _ _ _ _ _ _ _ => Or.inl (fun _ => rfl)
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => by
    rcases List.mem_cons.mp h with h | h <;> cases h <;> trivial)
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinPropAccIntroTy⟩⟩


/-- `intro`'s stored type is scope-closed — every `bvar` sits under its binder. -/
theorem pinPropAccIntro_mtype_boundOk : boundOkB 0 pinPropAccIntroA.mtypeA = true := by decide

theorem pinPropAccIntro_mtype_closed (k : Nat) :
    liftA k 1 pinPropAccIntroA.mtypeA = pinPropAccIntroA.mtypeA :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ pinPropAccIntro_mtype_boundOk)

/-- `intro`'s stored type is level-bounded at arity `0`. -/
theorem pinPropAccIntro_mtype_levels : exprLevelsBoundedA 0 pinPropAccIntroA.mtypeA = true := by decide

/-- `intro` at `11`, the group's single constructor. -/
def pinPropAccIntroGroupA (I : IotaIfaceA) :
    GroupCtorA I pinPropAccRelEnvA 10 pinPropAccFamA pinPropAccFamViewA where
  ref := 11
  member := pinPropAccIntroA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := pinPropAccIntro_mtype_closed
  u := .imax (.succ .zero) (.imax (.imax (.succ .zero) (.imax .zero .zero)) .zero)
  hT := pinPropAccIntroTy
  hlvl := pinPropAccIntro_mtype_levels
  view := pinPropAccIntroViewA I
  hnorm := rfl
  hclN := pinPropAccIntro_mtype_closed
  hlvlN := pinPropAccIntro_mtype_levels

def pinPropAccCs (I : IotaIfaceA) : List (GroupCtorA I pinPropAccRelEnvA 10 pinPropAccFamA pinPropAccFamViewA) :=
  [pinPropAccIntroGroupA I]

def pinPropAccGroupEnvA : ResolvedEnvA := extendEnvA pinPropAccFamEnvA 11 pinPropAccIntroA

theorem pinPropAccGroupEnv_eq (I : IotaIfaceA) :
    groupEnvA pinPropAccRelEnvA 10 pinPropAccFamA ((pinPropAccCs I).map GroupCtorA.entry) =
      pinPropAccGroupEnvA := rfl

theorem pinPropAccGroup_fresh (I : IotaIfaceA) :
    GroupFreshA pinPropAccRelEnvA 10 pinPropAccFamA ((pinPropAccCs I).map GroupCtorA.entry) := ⟨rfl, rfl⟩

theorem pinPropAccGroup_layout (I : IotaIfaceA) :
    (pinPropAccCs I).reverse.map GroupCtorA.ref = List.range' (10 + 1) (pinPropAccCs I).length := rfl

/-- the base env's census: only member is the axiom `R` at `9`. -/
theorem pinPropAccRel_mem {r : Nat} {m : CheckedMemberA}
    (hm : pinPropAccRelEnvA.members r = some m) : r = 9 ∧ m = pinPropAccRelA := by
  by_cases h9 : r = 9
  · subst h9
    have h : pinPropAccRelEnvA.members 9 = some pinPropAccRelA := rfl
    rw [h] at hm; cases hm
    exact ⟨rfl, rfl⟩
  · have hnone : pinPropAccRelEnvA.members r = none := by
      rw [pinPropAccRelEnvA, members_extendEnvA_ne emptyEnvA 9 pinPropAccRelA h9]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

theorem pinPropAccRel_closed : EnvClosedA pinPropAccRelEnvA := by
  intro r m hm
  obtain ⟨rfl, rfl⟩ := pinPropAccRel_mem hm
  exact ⟨pinPropAccRelTy_closed, fun _ hb => Option.noConfusion hb⟩

theorem pinPropAccRel_levels : EnvLevelsA pinPropAccRelEnvA := by
  intro r m hm
  obtain ⟨rfl, rfl⟩ := pinPropAccRel_mem hm
  exact ⟨rfl, fun _ hb => Option.noConfusion hb⟩

theorem pinPropAccRel_normClosed : EnvNormClosedA pinPropAccRelEnvA := by
  intro r m hm hc
  obtain ⟨rfl, rfl⟩ := pinPropAccRel_mem hm
  exact MemberClass.noConfusion hc

theorem pinPropAccRel_normLevels : EnvNormLevelsA pinPropAccRelEnvA := by
  intro r m hm hc
  obtain ⟨rfl, rfl⟩ := pinPropAccRel_mem hm
  exact MemberClass.noConfusion hc

theorem pinPropAccRel_normCtor : EnvNormCtorTypeA pinPropAccRelEnvA := by
  intro r m hm hc
  obtain ⟨rfl, rfl⟩ := pinPropAccRel_mem hm
  exact MemberClass.noConfusion hc

/-- the group env's census: residents are `9`, `10`, `11`. -/
theorem pinPropAccGroup_mem {r : Nat} {m : CheckedMemberA}
    (hm : pinPropAccGroupEnvA.members r = some m) :
    (r = 9 ∧ m = pinPropAccRelA) ∨ (r = 10 ∧ m = pinPropAccFamA) ∨ (r = 11 ∧ m = pinPropAccIntroA) := by
  by_cases h11 : r = 11
  · subst h11
    have h : pinPropAccGroupEnvA.members 11 = some pinPropAccIntroA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  by_cases h10 : r = 10
  · subst h10
    have h : pinPropAccGroupEnvA.members 10 = some pinPropAccFamA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  by_cases h9 : r = 9
  · subst h9
    have h : pinPropAccGroupEnvA.members 9 = some pinPropAccRelA := rfl
    rw [h] at hm; cases hm
    exact Or.inl ⟨rfl, rfl⟩
  · have hnone : pinPropAccGroupEnvA.members r = none := by
      rw [pinPropAccGroupEnvA, members_extendEnvA_ne _ 11 _ h11, pinPropAccFamEnvA,
        members_extendEnvA_ne _ 10 _ h10, pinPropAccRelEnvA,
        members_extendEnvA_ne emptyEnvA 9 _ h9]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

theorem pinPropAccGroup_closed : EnvClosedA pinPropAccGroupEnvA := by
  intro r m hm
  rcases pinPropAccGroup_mem hm with h | h | h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨pinPropAccRelTy_closed, fun _ hb => Option.noConfusion hb⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun k => liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide)),
      fun _ hb => Option.noConfusion hb⟩

theorem pinPropAccGroup_normClosed : EnvNormClosedA pinPropAccGroupEnvA := by
  intro r m hm hc
  rcases pinPropAccGroup_mem hm with h | h | h
  · obtain ⟨rfl, rfl⟩ := h; exact MemberClass.noConfusion hc
  · obtain ⟨rfl, rfl⟩ := h; exact MemberClass.noConfusion hc
  · obtain ⟨rfl, rfl⟩ := h
    intro T hT
    cases hT
    exact fun k => liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide))

theorem pinPropAccGroup_levels : EnvLevelsA pinPropAccGroupEnvA := by
  intro r m hm
  rcases pinPropAccGroup_mem hm with h | h | h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ hb => Option.noConfusion hb⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ hb => Option.noConfusion hb⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨by decide, fun _ hb => Option.noConfusion hb⟩

theorem pinPropAccGroup_normLevels : EnvNormLevelsA pinPropAccGroupEnvA := by
  intro r m hm hc
  rcases pinPropAccGroup_mem hm with h | h | h
  · obtain ⟨rfl, rfl⟩ := h; exact MemberClass.noConfusion hc
  · obtain ⟨rfl, rfl⟩ := h; exact MemberClass.noConfusion hc
  · obtain ⟨rfl, rfl⟩ := h
    intro T hT
    cases hT
    decide

/-- the recursor's member: the `AnySort` recursor built from the views. -/
def pinPropAccRecMemberA : CheckedMemberA :=
  ⟨.recursorM, 1, groupRecTypeA pinPropAccFamViewA (pinPropAccCs noIotaA) .anySort, none, 0, none⟩

/-- `pinPropAccEnvA`: `R` at `9`, the family `AccP` at `10`, `intro` at `11`, the recursor at `12`. -/
def pinPropAccEnvA : ResolvedEnvA := extendEnvA pinPropAccGroupEnvA 12 pinPropAccRecMemberA

theorem pinPropAccRec_fresh (I : IotaIfaceA) :
    (groupEnvA pinPropAccRelEnvA 10 pinPropAccFamA ((pinPropAccCs I).map GroupCtorA.entry)).members
      (10 + 1 + (pinPropAccCs I).length) = none := rfl

/-- the axiom member's `EnvWfA` step: `R`'s type is closed, level-bounded, and typed in the
    empty base. -/
def pinPropAccRelWfA (I : IotaIfaceA) : EnvWfA I pinPropAccRelEnvA :=
  .axiomM emptyEnvA 9 pinPropAccRelTyA _ .empty rfl pinPropAccRelTyTy pinPropAccRelTy_closed rfl

/-- the group step: `AccP` with `intro`, over the axiom base. -/
def pinPropAccGroupWfA (I : IotaIfaceA) : EnvWfA I pinPropAccGroupEnvA :=
  .group pinPropAccRelEnvA 10 pinPropAccFamA (.imax (.succ .zero) (.succ .zero))
    (pinPropAccRelWfA I) rfl rfl (fun _ => rfl) pinPropAccFamTyTy rfl pinPropAccFamViewA (pinPropAccCs I)
    (pinPropAccGroup_fresh I)

/-- the recursor's type, typed in the DerivationScope at the group env's interface. The axiom
    member's semantic clause is reflection (`envSemClauseA_rigid`), discharged over the empty
    induction hypothesis. -/
theorem pinPropAccRel_sem {I : IotaIfaceA} (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hR : IotaRecHeadA pinPropAccRelEnvA I) :
    EnvSemA pinPropAccRelEnvA I 0 (fun _ => 1) := by
  intro r m hres
  obtain ⟨rfl, rfl⟩ := pinPropAccRel_mem hres
  have ih : EnvSemAt pinPropAccRelEnvA I 0 (fun _ => 1) (domA emptyEnvA) :=
    fun _ _ hD _ => hD.elim fun _ h => Option.noConfusion h
  obtain ⟨hT, hC⟩ := fundArmsA_at pinPropAccRel_closed hI hIS pinPropAccRel_normCtor
    pinPropAccRel_normClosed hR posValA_one ih
  obtain ⟨k₀, hT'⟩ := fundArmA_nil (fundHasTyPrefixA (fun _ _ h => Option.noConfusion h) hT hC
    (hasTyA_arity0 (fun _ _ h => Option.noConfusion h) hIL (pinPropAccRelTyTy (E := emptyEnvA))))
  exact envSemClauseA_rigid pinPropAccRel_closed hI hR pinPropAccRelEnv_rel rfl (Or.inl rfl)
    (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
    (fun h => MemberClass.noConfusion h) hT'

theorem pinPropAccRecTyAt0 :
    ∃ w : Level, Nonempty (HasTyA pinPropAccGroupEnvA (iotaIfaceA pinPropAccGroupEnvA) (0 + 1) []
      (groupRecTypeA pinPropAccFamViewA (pinPropAccCs (iotaIfaceA pinPropAccGroupEnvA)) .anySort)
        (.sort w)) :=
  groupRecTypeA_hasTy_der (cs := pinPropAccCs (iotaIfaceA pinPropAccGroupEnvA)) (elim := .anySort)
    pinPropAccFamTyTy (pinPropAccGroup_fresh _) pinPropAccRel_closed pinPropAccGroup_closed
    pinPropAccRel_normCtor pinPropAccRel_normClosed
    (iotaFnA_lift pinPropAccGroup_closed pinPropAccGroup_normClosed)
    (iotaFnA_subst pinPropAccGroup_closed pinPropAccGroup_normClosed)
    (recHead_of_groupEnvA (fm := pinPropAccFamA) (es := [(11, pinPropAccIntroA)]) rfl
      (fun _ he => by cases List.mem_singleton.mp he; rfl) (iotaFnA_recHead _))
    (iotaFnA_recHead _)
    (pinPropAccRel_sem
      (iotaFnA_lift pinPropAccGroup_closed pinPropAccGroup_normClosed)
      (iotaFnA_subst pinPropAccGroup_closed pinPropAccGroup_normClosed)
      (iotaFnA_levels pinPropAccGroup_levels pinPropAccGroup_normLevels)
      (recHead_of_groupEnvA (fm := pinPropAccFamA) (es := [(11, pinPropAccIntroA)]) rfl
        (fun _ he => by cases List.mem_singleton.mp he; rfl) (iotaFnA_recHead _)))
    posValA_one

theorem pinPropAccGroupAgree :
    IfaceAgreeA pinPropAccGroupEnvA (iotaIfaceA pinPropAccGroupEnvA) (iotaIfaceA pinPropAccEnvA) :=
  ifaceAgreeA_prefix (pinPropAccGroupWfA (iotaIfaceA pinPropAccGroupEnvA))
    (prefixA_extend pinPropAccGroupEnvA 12 pinPropAccRecMemberA rfl)

theorem pinPropAccRecBuilt_closed (k : Nat) :
    liftA k 1 pinPropAccRecMemberA.mtypeA = pinPropAccRecMemberA.mtypeA :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide))

/-- the derived recursor at a typing of its built type (`pinPropAccRecTyAt0` supplies one). -/
def pinPropAccRecA (w : Level)
    (hT0 : HasTyA pinPropAccGroupEnvA (iotaIfaceA pinPropAccGroupEnvA) (0 + 1) []
      (groupRecTypeA pinPropAccFamViewA (pinPropAccCs (iotaIfaceA pinPropAccGroupEnvA)) .anySort)
      (.sort w)) :
    GroupRecA (iotaIfaceA pinPropAccEnvA) pinPropAccRelEnvA 10 pinPropAccFamA pinPropAccFamViewA
      (pinPropAccCs (iotaIfaceA pinPropAccEnvA)) where
  member := pinPropAccRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := pinPropAccRecBuilt_closed
  u := w
  hT := by
    rw [pinPropAccGroupEnv_eq]
    exact hasTyIfaceA pinPropAccGroupAgree hT0
  hlvl := by decide

/-- `R`, `AccP`, `intro` and the derived recursor, admitted by `EnvWfA.groupRec` at the concrete
    ι. -/
def pinPropAccWfA (w : Level)
    (hT0 : HasTyA pinPropAccGroupEnvA (iotaIfaceA pinPropAccGroupEnvA) (0 + 1) []
      (groupRecTypeA pinPropAccFamViewA (pinPropAccCs (iotaIfaceA pinPropAccGroupEnvA)) .anySort)
      (.sort w)) :
    EnvWfA (iotaIfaceA pinPropAccEnvA) pinPropAccEnvA :=
  .groupRec pinPropAccRelEnvA 10 pinPropAccFamA (.imax (.succ .zero) (.succ .zero))
    (pinPropAccRelWfA (iotaIfaceA pinPropAccEnvA)) rfl rfl (fun _ => rfl) pinPropAccFamTyTy rfl
    pinPropAccFamViewA (pinPropAccCs (iotaIfaceA pinPropAccEnvA)) (pinPropAccGroup_fresh _)
    (pinPropAccGroup_layout _) (pinPropAccRecA w hT0) (pinPropAccRec_fresh _)

/-- every resident of `pinPropAccEnvA` is one of `9`–`12`. -/
theorem pinPropAcc_mem {r : Nat} {m : CheckedMemberA} (hm : pinPropAccEnvA.members r = some m) :
    (r = 9 ∧ m = pinPropAccRelA) ∨ (r = 10 ∧ m = pinPropAccFamA) ∨
      (r = 11 ∧ m = pinPropAccIntroA) ∨ (r = 12 ∧ m = pinPropAccRecMemberA) := by
  by_cases h12 : r = 12
  · subst h12
    have h : pinPropAccEnvA.members 12 = some pinPropAccRecMemberA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  by_cases h11 : r = 11
  · subst h11
    have h : pinPropAccEnvA.members 11 = some pinPropAccIntroA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  by_cases h10 : r = 10
  · subst h10
    have h : pinPropAccEnvA.members 10 = some pinPropAccFamA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  by_cases h9 : r = 9
  · subst h9
    have h : pinPropAccEnvA.members 9 = some pinPropAccRelA := rfl
    rw [h] at hm; cases hm
    exact Or.inl ⟨rfl, rfl⟩
  · have hnone : pinPropAccEnvA.members r = none := by
      rw [pinPropAccEnvA, members_extendEnvA_ne _ 12 _ h12, pinPropAccGroupEnvA,
        members_extendEnvA_ne _ 11 _ h11, pinPropAccFamEnvA,
        members_extendEnvA_ne _ 10 _ h10, pinPropAccRelEnvA,
        members_extendEnvA_ne emptyEnvA 9 _ h9]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

theorem pinPropAcc_inductive {r : Nat} {m : CheckedMemberA} (hm : pinPropAccEnvA.members r = some m)
    (hc : m.mclass = .inductiveM) : r = 10 ∧ m = pinPropAccFamA := by
  rcases pinPropAcc_mem hm with h | h | h | h
  · rcases h with ⟨_, rfl⟩; simp [pinPropAccRelA] at hc
  · exact h
  · rcases h with ⟨_, rfl⟩; simp [pinPropAccIntroA] at hc
  · rcases h with ⟨_, rfl⟩; simp [pinPropAccRecMemberA] at hc

/-- the small-index profile: `AccP`'s result sort is `Prop`, so the profile is vacuous — the
    `0 < y` antecedent is never met (`eval ρ .zero = 0`). -/
theorem pinPropAcc_small : SmallIndexProfileA pinPropAccEnvA := by
  intro r m u₀ hm hc hbody v hv ρ x y hx hy hlt
  obtain ⟨_, rfl⟩ := pinPropAcc_inductive hm hc
  have hPi : piBodyA pinPropAccFamA.mtypeA = .sort .zero := rfl
  rw [hPi] at hbody
  cases hbody
  have hy0 : y = 0 := (Option.some.inj hy).symm
  subst hy0
  exact absurd hlt (Nat.lt_irrefl 0)

/-- THE CLASS-(c) TOOTH: `PropElimOnlyA` FAILS — `AccP` is Prop-profiled (`UniformProp .zero`),
    the recursor sits at `12 ≠ 11` in a non-unit non-struct group, and its `.anySort` motive
    ends at `.param 0`, not `.sort .zero`. The policy that gates `envSemA_of_envWfA_rec` is
    genuinely violated: the recursor LARGE-eliminates, so the `EnvSemA` reflection route does
    not apply to this environment. -/
theorem pinPropAcc_not_propElim : ¬ PropElimOnlyA pinPropAccEnvA := fun h => by
  have hcontra := h 12 pinPropAccRecMemberA _ 10 _ pinPropAccFamA .zero rfl rfl rfl rfl rfl rfl
    rfl (fun _ => rfl) (by decide) (by decide) _ rfl
  exact absurd hcontra (by decide)

/-- `intro`'s second field is function-recursive with TWO inner binders — `y` and the `R y x`
    hypothesis — so its shape is `recursive 2`. -/
theorem pinPropAcc_intro_shapes :
    ctorShapesA 10 pinPropAccFamA.nparamsA pinPropAccIntroA.mtypeA =
      some [.nonrecursive, .recursive 2] := rfl

/-- THE TOOTH: the environment is outside `EnvNoFunA` — `intro`'s `recursive 2` field is
    function-recursive, so the erasure and the bridge refuse the environment. -/
theorem pinPropAcc_not_noFunA : ¬ EnvNoFunA pinPropAccEnvA := fun h =>
  h 11 pinPropAccIntroA 10 pinPropAccFamA [.nonrecursive, .recursive 2] rfl rfl rfl rfl
    pinPropAcc_intro_shapes _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) 1 rfl

theorem pinPropAcc_not_annEnvA : ¬ AnnEnvA pinPropAccEnvA := fun C => pinPropAcc_not_noFunA C.noFun

#print axioms pinPropAccIntroTy
#print axioms pinPropAccIntroViewA
#print axioms pinPropAccIntroGroupA
#print axioms pinPropAccRel_sem
#print axioms pinPropAccRecTyAt0
#print axioms pinPropAccWfA
#print axioms pinPropAcc_not_noFunA
#print axioms pinPropAcc_intro_shapes


/-- the copy's ι fires at `intro`, so the refusal is not vacuous: with spine
    `rec M m i (intro X G)` (motive, the one minor, the one index, major) the contraction
    reduces. -/
theorem pinPropAcc_iota_fires :
    (iotaFnA pinPropAccEnvA
      (.app (.app (.app (.app (.const 12 [.zero]) (.sort .zero)) (.sort (.succ .zero)))
        (.sort .zero)) (.app (.app (.const 11 []) (.sort .zero)) (.sort .zero)))).isSome = true := by
  decide

/-- the ι layer does not gate on the motive's universe: the same contraction fires at level
    instantiation `[.succ .zero]` (the AnySort instance). -/
theorem pinPropAcc_iota_fires_anySort :
    (iotaFnA pinPropAccEnvA
      (.app (.app (.app (.app (.const 12 [.succ .zero]) (.sort .zero)) (.sort (.succ .zero)))
        (.sort .zero)) (.app (.app (.const 11 []) (.sort .zero)) (.sort .zero)))).isSome = true := by
  decide

/-- the class-(c) boundary is REAL, not vacuous: `PropElimOnlyA` fails (the `.anySort` recursor
    large-eliminates — its motive ends at `.param 0`) while the copy's ι still contracts at
    motive universe `1`. The `EnvSemA` route is blocked at exactly the policy the class-(a)/(b)
    rows discharged; the union-correspondence row (`iotaErasesTUA_frecR`) does not need it. -/
theorem pinPropAcc_propElim_fails_iota_fires :
    ¬ PropElimOnlyA pinPropAccEnvA ∧
    (iotaFnA pinPropAccEnvA
      (.app (.app (.app (.app (.const 12 [.succ .zero]) (.sort .zero)) (.sort (.succ .zero)))
        (.sort .zero)) (.app (.app (.const 11 []) (.sort .zero)) (.sort .zero)))).isSome = true :=
  ⟨pinPropAcc_not_propElim, pinPropAcc_iota_fires_anySort⟩

#print axioms pinPropAcc_not_propElim
#print axioms pinPropAcc_iota_fires_anySort
#print axioms pinPropAcc_propElim_fails_iota_fires
#print axioms pinPropAcc_iota_fires
#print axioms pinPropAcc_not_annEnvA

end Rcic.Declarative.Ann
