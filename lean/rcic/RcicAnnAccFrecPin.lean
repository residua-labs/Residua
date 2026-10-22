import rcic.RcicAnnFrecPin

/-!
# R-NoFunRec class (a), second row: THE ACC-SHAPED FUNCTION-RECURSIVE PIN

`pinFrecEnvA` (RcicAnnFrecPin) is the W row: one `frec` field `Sort 0 → T` — a single inner
binder, tail the family unapplied (`shape = recursive 1`). This module is the Acc row of the
same class: `AccT : Sort 0 → Sort 1` is an INDEXED family and `intro`'s recursive field is
guarded by a hypothesis — `Π (y : Sort 0), R y x → AccT y`, two inner binders with the second
DEPENDING on the first (`Bs` nonempty, `shape = recursive 2`), the tail applied to the bound
element. The relation `R` is an opaque `axiomM` member at `9`, so `innerClean`/`rigid` hold
by member class, not by parameter bookkeeping.

The pin mirrors `RcicAnnFrecPin`: members, the views, `EnvWfA` via `axiomM` + `groupRec`,
`EnvSemA`, the firing, and the `EnvNoFunA`/`AnnEnvA` teeth.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- the ambient relation `R : Sort 0 → Sort 0 → Sort 0`, opaque (axiomM), at `9`. -/
def pinAccRelTyA : ExprA :=
  .pi (.sort .zero) (.succ .zero) (.pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero))
    (.imax (.succ .zero) (.succ .zero))

def pinAccRelA : CheckedMemberA := ⟨.axiomM, 0, pinAccRelTyA, none, 0, none⟩

def pinAccRelEnvA : ResolvedEnvA := extendEnvA emptyEnvA 9 pinAccRelA

theorem pinAccRelEnv_rel : pinAccRelEnvA.members 9 = some pinAccRelA := rfl

/-- `AccT : Π (_ : Sort 0), Sort 1`, one index, no parameters. -/
def pinAccFamA : CheckedMemberA :=
  ⟨.inductiveM, 0, .pi (.sort .zero) (.succ .zero) (.sort (.succ .zero)) (.succ (.succ .zero)),
    none, 0, none⟩

/-- `intro`'s hypothesis domain `R y x`, in the inner-binder context `[y] ++ [x]`
    (y = bvar 0, x = bvar 1). -/
def pinAccGuardA : ExprA := .app (.app (.const 9 []) (.bvar 0)) (.bvar 1)

/-- `intro`'s function-recursive field: `Π (y : Sort 0), R y x → AccT y` — `Bs` carries the
    guard (a domain DEPENDING on the first inner binder), `idx` the tail's index `y`
    (in the tail's context `[guard, y] ++ [x]`, so `y = bvar 1`). -/
def pinAccFieldA : FieldA :=
  .frec (.sort .zero) (.succ .zero) [(pinAccGuardA, .zero)] [.bvar 1]

/-- `intro : Π (x : Sort 0), (Π (y : Sort 0), R y x → AccT y) → AccT x` at `11`, over the
    family at `10` — `x` is a plain field and the result's index, the recursive field is
    guarded by `R y x` and recurses at `y`. -/
def pinAccIntroA : CheckedMemberA :=
  ⟨.constructorM, 0,
    ctorTypeA 10 (canonLevelsA 0) (.succ .zero) []
      [.plain (.sort .zero) (.succ .zero), pinAccFieldA] [.bvar 0],
    none, 0,
    some (ctorTypeA 10 (canonLevelsA 0) (.succ .zero) []
      [.plain (.sort .zero) (.succ .zero), pinAccFieldA] [.bvar 0])⟩


/-- `R`'s type is closed — the `axiomM` step's side condition. -/
theorem pinAccRelTy_closed (k : Nat) : liftA k 1 pinAccRelTyA = pinAccRelTyA := rfl

/-- `R`'s type, derivable in any context — at the `imax` sort its pi-chain produces. -/
def pinAccRelTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n Γ pinAccRelTyA
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .pi Γ _ _ _ _ (.sort Γ .zero) (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))

/-- `R` at `9`, in any context. -/
def pinAccRelConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 9 = some pinAccRelA) :
    HasTyA E I n Γ (.const 9 []) pinAccRelTyA :=
  .const Γ 9 [] pinAccRelA _ h rfl rfl pinAccRelTyTy

/-- the family env: `R` at `9`, then `AccT` at `10`. -/
def pinAccFamEnvA : ResolvedEnvA := extendEnvA pinAccRelEnvA 10 pinAccFamA

theorem pinAccFamEnv_rel : pinAccFamEnvA.members 9 = some pinAccRelA := rfl
theorem pinAccFamEnv_fam : pinAccFamEnvA.members 10 = some pinAccFamA := rfl

/-- `AccT`'s type `Π (_ : Sort 0), Sort 1`, derivable in any context. -/
def pinAccFamTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n Γ pinAccFamA.mtypeA
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
  .pi Γ _ _ _ _ (.sort Γ .zero) (.sort _ (.succ .zero))

/-- `AccT` at `10`, in any context. -/
def pinAccFamConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 10 = some pinAccFamA) :
    HasTyA E I n Γ (.const 10 []) pinAccFamA.mtypeA :=
  .const Γ 10 [] pinAccFamA _ h rfl rfl pinAccFamTyTy

/-- `AccT`'s family view: no parameters, one `Sort 0` index, sort `1`. -/
def pinAccFamViewA : FamViewA pinAccFamA where
  params := []
  indices := [(.sort .zero, .succ .zero)]
  sort := .succ .zero
  stored := rfl
  nparams := rfl
  profile := .inr (fun _ => Nat.succ_pos 0)



/-- the guard `R y x` at `Sort 0`, in the concrete context `[y, x] ++ Γ` (`y` at `bvar 0`,
    `x` at `bvar 1`). The derivation is a plain `.app`-chain term so the contexts stay
    explicit. -/
def pinAccGuardTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h9 : E.members 9 = some pinAccRelA) :
    HasTyA E I n
      (.assumption (.sort .zero) :: .assumption (.sort .zero) :: Γ)
      pinAccGuardA (.sort .zero) :=
  .app _ _ (.bvar 1) (.sort .zero) (.sort .zero)
    (.succ .zero) (.succ .zero) (.succ .zero)
    (.sort _ .zero) (.sort _ .zero)
    (.app _ (.const 9 []) (.bvar 0) (.sort .zero)
      (.pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero))
      (.succ .zero) (.imax (.succ .zero) (.succ .zero))
      (.imax (.succ .zero) (.succ .zero))
      (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))
      (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))
      (pinAccRelConstTy h9)
      (.bvar _ 0 _ _ rfl (.sort _ .zero)))
    (.bvar _ 1 _ _ rfl (.sort _ .zero))


/-- `intro`'s stored type, typed in the family's extension scope (`pinAccFamEnvA`): the guarded
    recursion `Π (x : Sort 0), (Π (y : Sort 0), R y x → AccT y) → AccT x`. Every annotation is the
    level `ctorTypeA`/`piTelA` themselves record — the codomain's sort, which is the `imax` chain on
    nested binders. -/
def pinAccIntroTy {I : IotaIfaceA} :
    HasTyA pinAccFamEnvA I 0 [] pinAccIntroA.mtypeA
      (.sort (.imax (.succ .zero)
        (.imax (.imax (.succ .zero) (.imax .zero (.succ .zero))) (.succ .zero)))) :=
  .pi [] _ _ _ _ (.sort [] .zero)
    (.pi _ _ _ _ _
      (.pi _ _ _ _ _ (.sort _ .zero)
        (.pi _ _ _ _ _ (pinAccGuardTy pinAccRelEnv_rel)
          (.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort (.succ .zero))
            (.succ .zero) (.succ (.succ .zero)) (.succ (.succ .zero))
            (.sort _ (.succ .zero)) (.sort _ (.succ .zero))
            (pinAccFamConstTy pinAccFamEnv_fam)
            (.bvar _ 1 _ _ rfl (.sort _ .zero)))))
      (.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort (.succ .zero))
        (.succ .zero) (.succ (.succ .zero)) (.succ (.succ .zero))
        (.sort _ (.succ .zero)) (.sort _ (.succ .zero))
        (pinAccFamConstTy pinAccFamEnv_fam)
        (.bvar _ 1 _ _ rfl (.sort _ .zero))))

/-- `intro`'s view: a plain `x : Sort 0` field, then the function-recursive field guarded by
    `R y x` recursing at `y`; the result is the family at `x`. -/
def pinAccIntroViewA (I : IotaIfaceA) :
    CtorViewA pinAccRelEnvA I 10 pinAccFamA pinAccFamViewA pinAccIntroA where
  mirrors := []
  fields := [.plain (.sort .zero) (.succ .zero), pinAccFieldA]
  res := [.bvar 0]
  stored := rfl
  mirrorsConv := .nil []
  typed :=
    .plain [] 0 _ _ _ _ (.sort [] .zero)
      (.frec _ 1 _ _ _ _ _ _
        (.plain _ 1 _ _ _ _ (.sort _ .zero)
          (.plain _ 2 _ _ _ _ (pinAccGuardTy pinAccRelEnv_rel)
            (.nil _ 3 _
              (.cons _ _ _ _ _ _
                (.bvar _ 1 _ _ rfl (.sort _ .zero))
                (.nil _)))))
        (.nil _ 1 _
          (.cons _ _ _ _ _ _
            (.bvar _ 0 _ _ rfl (.sort _ .zero))
            (.nil _))))
  univ := fun D u h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact Or.inr ⟨fun _ => Nat.succ_pos 0,
        fun ρ x y hx hy => by cases hx.symm.trans hy; exact Nat.le_refl _⟩
    · cases List.mem_singleton.mp h
  univI := fun B uB Bs idx h d hd => by
    rcases List.mem_cons.mp h with h | h
    · cases h
    · cases List.mem_singleton.mp h
      rcases List.mem_cons.mp hd with h | h
      · cases h
        exact Or.inr ⟨fun _ => Nat.succ_pos 0,
          fun ρ x y hx hy => by cases hx.symm.trans hy; exact Nat.le_refl _⟩
      · cases List.mem_singleton.mp h
        refine Or.inr ⟨fun _ => Nat.succ_pos 0, fun ρ x y hx hy => ?_⟩
        have hx0 : x = 0 := (Option.some.inj hx).symm
        subst hx0
        exact Nat.zero_le y
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => by
    rcases List.mem_cons.mp h with h | h <;> cases h <;> trivial)
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinAccIntroTy⟩⟩


/-- `intro`'s stored type is scope-closed — every `bvar` sits under its binder. -/
theorem pinAccIntro_mtype_boundOk : boundOkB 0 pinAccIntroA.mtypeA = true := by decide

theorem pinAccIntro_mtype_closed (k : Nat) :
    liftA k 1 pinAccIntroA.mtypeA = pinAccIntroA.mtypeA :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ pinAccIntro_mtype_boundOk)

/-- `intro`'s stored type is level-bounded at arity `0`. -/
theorem pinAccIntro_mtype_levels : exprLevelsBoundedA 0 pinAccIntroA.mtypeA = true := by decide

/-- `intro` at `11`, the group's single constructor. -/
def pinAccIntroGroupA (I : IotaIfaceA) :
    GroupCtorA I pinAccRelEnvA 10 pinAccFamA pinAccFamViewA where
  ref := 11
  member := pinAccIntroA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := pinAccIntro_mtype_closed
  u := .imax (.succ .zero) (.imax (.imax (.succ .zero) (.imax .zero (.succ .zero))) (.succ .zero))
  hT := pinAccIntroTy
  hlvl := pinAccIntro_mtype_levels
  view := pinAccIntroViewA I
  hnorm := rfl
  hclN := pinAccIntro_mtype_closed
  hlvlN := pinAccIntro_mtype_levels

def pinAccCs (I : IotaIfaceA) : List (GroupCtorA I pinAccRelEnvA 10 pinAccFamA pinAccFamViewA) :=
  [pinAccIntroGroupA I]

def pinAccGroupEnvA : ResolvedEnvA := extendEnvA pinAccFamEnvA 11 pinAccIntroA

theorem pinAccGroupEnv_eq (I : IotaIfaceA) :
    groupEnvA pinAccRelEnvA 10 pinAccFamA ((pinAccCs I).map GroupCtorA.entry) =
      pinAccGroupEnvA := rfl

theorem pinAccGroup_fresh (I : IotaIfaceA) :
    GroupFreshA pinAccRelEnvA 10 pinAccFamA ((pinAccCs I).map GroupCtorA.entry) := ⟨rfl, rfl⟩

theorem pinAccGroup_layout (I : IotaIfaceA) :
    (pinAccCs I).reverse.map GroupCtorA.ref = List.range' (10 + 1) (pinAccCs I).length := rfl

/-- the base env's census: only member is the axiom `R` at `9`. -/
theorem pinAccRel_mem {r : Nat} {m : CheckedMemberA}
    (hm : pinAccRelEnvA.members r = some m) : r = 9 ∧ m = pinAccRelA := by
  by_cases h9 : r = 9
  · subst h9
    have h : pinAccRelEnvA.members 9 = some pinAccRelA := rfl
    rw [h] at hm; cases hm
    exact ⟨rfl, rfl⟩
  · have hnone : pinAccRelEnvA.members r = none := by
      rw [pinAccRelEnvA, members_extendEnvA_ne emptyEnvA 9 pinAccRelA h9]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

theorem pinAccRel_closed : EnvClosedA pinAccRelEnvA := by
  intro r m hm
  obtain ⟨rfl, rfl⟩ := pinAccRel_mem hm
  exact ⟨pinAccRelTy_closed, fun _ hb => Option.noConfusion hb⟩

theorem pinAccRel_levels : EnvLevelsA pinAccRelEnvA := by
  intro r m hm
  obtain ⟨rfl, rfl⟩ := pinAccRel_mem hm
  exact ⟨rfl, fun _ hb => Option.noConfusion hb⟩

theorem pinAccRel_normClosed : EnvNormClosedA pinAccRelEnvA := by
  intro r m hm hc
  obtain ⟨rfl, rfl⟩ := pinAccRel_mem hm
  exact MemberClass.noConfusion hc

theorem pinAccRel_normLevels : EnvNormLevelsA pinAccRelEnvA := by
  intro r m hm hc
  obtain ⟨rfl, rfl⟩ := pinAccRel_mem hm
  exact MemberClass.noConfusion hc

theorem pinAccRel_normCtor : EnvNormCtorTypeA pinAccRelEnvA := by
  intro r m hm hc
  obtain ⟨rfl, rfl⟩ := pinAccRel_mem hm
  exact MemberClass.noConfusion hc

/-- the group env's census: residents are `9`, `10`, `11`. -/
theorem pinAccGroup_mem {r : Nat} {m : CheckedMemberA}
    (hm : pinAccGroupEnvA.members r = some m) :
    (r = 9 ∧ m = pinAccRelA) ∨ (r = 10 ∧ m = pinAccFamA) ∨ (r = 11 ∧ m = pinAccIntroA) := by
  by_cases h11 : r = 11
  · subst h11
    have h : pinAccGroupEnvA.members 11 = some pinAccIntroA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  by_cases h10 : r = 10
  · subst h10
    have h : pinAccGroupEnvA.members 10 = some pinAccFamA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  by_cases h9 : r = 9
  · subst h9
    have h : pinAccGroupEnvA.members 9 = some pinAccRelA := rfl
    rw [h] at hm; cases hm
    exact Or.inl ⟨rfl, rfl⟩
  · have hnone : pinAccGroupEnvA.members r = none := by
      rw [pinAccGroupEnvA, members_extendEnvA_ne _ 11 _ h11, pinAccFamEnvA,
        members_extendEnvA_ne _ 10 _ h10, pinAccRelEnvA,
        members_extendEnvA_ne emptyEnvA 9 _ h9]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

theorem pinAccGroup_closed : EnvClosedA pinAccGroupEnvA := by
  intro r m hm
  rcases pinAccGroup_mem hm with h | h | h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨pinAccRelTy_closed, fun _ hb => Option.noConfusion hb⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun k => liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide)),
      fun _ hb => Option.noConfusion hb⟩

theorem pinAccGroup_normClosed : EnvNormClosedA pinAccGroupEnvA := by
  intro r m hm hc
  rcases pinAccGroup_mem hm with h | h | h
  · obtain ⟨rfl, rfl⟩ := h; exact MemberClass.noConfusion hc
  · obtain ⟨rfl, rfl⟩ := h; exact MemberClass.noConfusion hc
  · obtain ⟨rfl, rfl⟩ := h
    intro T hT
    cases hT
    exact fun k => liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide))

theorem pinAccGroup_levels : EnvLevelsA pinAccGroupEnvA := by
  intro r m hm
  rcases pinAccGroup_mem hm with h | h | h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ hb => Option.noConfusion hb⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ hb => Option.noConfusion hb⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨by decide, fun _ hb => Option.noConfusion hb⟩

theorem pinAccGroup_normLevels : EnvNormLevelsA pinAccGroupEnvA := by
  intro r m hm hc
  rcases pinAccGroup_mem hm with h | h | h
  · obtain ⟨rfl, rfl⟩ := h; exact MemberClass.noConfusion hc
  · obtain ⟨rfl, rfl⟩ := h; exact MemberClass.noConfusion hc
  · obtain ⟨rfl, rfl⟩ := h
    intro T hT
    cases hT
    decide

/-- the recursor's member: the `AnySort` recursor built from the views. -/
def pinAccRecMemberA : CheckedMemberA :=
  ⟨.recursorM, 1, groupRecTypeA pinAccFamViewA (pinAccCs noIotaA) .anySort, none, 0, none⟩

/-- `pinAccEnvA`: `R` at `9`, the family `AccT` at `10`, `intro` at `11`, the recursor at `12`. -/
def pinAccEnvA : ResolvedEnvA := extendEnvA pinAccGroupEnvA 12 pinAccRecMemberA

theorem pinAccRec_fresh (I : IotaIfaceA) :
    (groupEnvA pinAccRelEnvA 10 pinAccFamA ((pinAccCs I).map GroupCtorA.entry)).members
      (10 + 1 + (pinAccCs I).length) = none := rfl

/-- the axiom member's `EnvWfA` step: `R`'s type is closed, level-bounded, and typed in the
    empty base. -/
def pinAccRelWfA (I : IotaIfaceA) : EnvWfA I pinAccRelEnvA :=
  .axiomM emptyEnvA 9 pinAccRelTyA _ .empty rfl pinAccRelTyTy pinAccRelTy_closed rfl

/-- the group step: `AccT` with `intro`, over the axiom base. -/
def pinAccGroupWfA (I : IotaIfaceA) : EnvWfA I pinAccGroupEnvA :=
  .group pinAccRelEnvA 10 pinAccFamA (.imax (.succ .zero) (.succ (.succ .zero)))
    (pinAccRelWfA I) rfl rfl (fun _ => rfl) pinAccFamTyTy rfl pinAccFamViewA (pinAccCs I)
    (pinAccGroup_fresh I)

/-- the recursor's type, typed in the DerivationScope at the group env's interface. The axiom
    member's semantic clause is reflection (`envSemClauseA_rigid`), discharged over the empty
    induction hypothesis. -/
theorem pinAccRel_sem {I : IotaIfaceA} (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hR : IotaRecHeadA pinAccRelEnvA I) :
    EnvSemA pinAccRelEnvA I 0 (fun _ => 1) := by
  intro r m hres
  obtain ⟨rfl, rfl⟩ := pinAccRel_mem hres
  have ih : EnvSemAt pinAccRelEnvA I 0 (fun _ => 1) (domA emptyEnvA) :=
    fun _ _ hD _ => hD.elim fun _ h => Option.noConfusion h
  obtain ⟨hT, hC⟩ := fundArmsA_at pinAccRel_closed hI hIS pinAccRel_normCtor
    pinAccRel_normClosed hR posValA_one ih
  obtain ⟨k₀, hT'⟩ := fundArmA_nil (fundHasTyPrefixA (fun _ _ h => Option.noConfusion h) hT hC
    (hasTyA_arity0 (fun _ _ h => Option.noConfusion h) hIL (pinAccRelTyTy (E := emptyEnvA))))
  exact envSemClauseA_rigid pinAccRel_closed hI hR pinAccRelEnv_rel rfl (Or.inl rfl)
    (fun h => MemberClass.noConfusion h) (fun h => MemberClass.noConfusion h)
    (fun h => MemberClass.noConfusion h) hT'

theorem pinAccRecTyAt0 :
    ∃ w : Level, Nonempty (HasTyA pinAccGroupEnvA (iotaIfaceA pinAccGroupEnvA) (0 + 1) []
      (groupRecTypeA pinAccFamViewA (pinAccCs (iotaIfaceA pinAccGroupEnvA)) .anySort)
        (.sort w)) :=
  groupRecTypeA_hasTy_der (cs := pinAccCs (iotaIfaceA pinAccGroupEnvA)) (elim := .anySort)
    pinAccFamTyTy (pinAccGroup_fresh _) pinAccRel_closed pinAccGroup_closed
    pinAccRel_normCtor pinAccRel_normClosed
    (iotaFnA_lift pinAccGroup_closed pinAccGroup_normClosed)
    (iotaFnA_subst pinAccGroup_closed pinAccGroup_normClosed)
    (recHead_of_groupEnvA (fm := pinAccFamA) (es := [(11, pinAccIntroA)]) rfl
      (fun _ he => by cases List.mem_singleton.mp he; rfl) (iotaFnA_recHead _))
    (iotaFnA_recHead _)
    (pinAccRel_sem
      (iotaFnA_lift pinAccGroup_closed pinAccGroup_normClosed)
      (iotaFnA_subst pinAccGroup_closed pinAccGroup_normClosed)
      (iotaFnA_levels pinAccGroup_levels pinAccGroup_normLevels)
      (recHead_of_groupEnvA (fm := pinAccFamA) (es := [(11, pinAccIntroA)]) rfl
        (fun _ he => by cases List.mem_singleton.mp he; rfl) (iotaFnA_recHead _)))
    posValA_one

theorem pinAccGroupAgree :
    IfaceAgreeA pinAccGroupEnvA (iotaIfaceA pinAccGroupEnvA) (iotaIfaceA pinAccEnvA) :=
  ifaceAgreeA_prefix (pinAccGroupWfA (iotaIfaceA pinAccGroupEnvA))
    (prefixA_extend pinAccGroupEnvA 12 pinAccRecMemberA rfl)

theorem pinAccRecBuilt_closed (k : Nat) :
    liftA k 1 pinAccRecMemberA.mtypeA = pinAccRecMemberA.mtypeA :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide))

/-- the derived recursor at a typing of its built type (`pinAccRecTyAt0` supplies one). -/
def pinAccRecA (w : Level)
    (hT0 : HasTyA pinAccGroupEnvA (iotaIfaceA pinAccGroupEnvA) (0 + 1) []
      (groupRecTypeA pinAccFamViewA (pinAccCs (iotaIfaceA pinAccGroupEnvA)) .anySort)
      (.sort w)) :
    GroupRecA (iotaIfaceA pinAccEnvA) pinAccRelEnvA 10 pinAccFamA pinAccFamViewA
      (pinAccCs (iotaIfaceA pinAccEnvA)) where
  member := pinAccRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := pinAccRecBuilt_closed
  u := w
  hT := by
    rw [pinAccGroupEnv_eq]
    exact hasTyIfaceA pinAccGroupAgree hT0
  hlvl := by decide

/-- `R`, `AccT`, `intro` and the derived recursor, admitted by `EnvWfA.groupRec` at the concrete
    ι. -/
def pinAccWfA (w : Level)
    (hT0 : HasTyA pinAccGroupEnvA (iotaIfaceA pinAccGroupEnvA) (0 + 1) []
      (groupRecTypeA pinAccFamViewA (pinAccCs (iotaIfaceA pinAccGroupEnvA)) .anySort)
      (.sort w)) :
    EnvWfA (iotaIfaceA pinAccEnvA) pinAccEnvA :=
  .groupRec pinAccRelEnvA 10 pinAccFamA (.imax (.succ .zero) (.succ (.succ .zero)))
    (pinAccRelWfA (iotaIfaceA pinAccEnvA)) rfl rfl (fun _ => rfl) pinAccFamTyTy rfl
    pinAccFamViewA (pinAccCs (iotaIfaceA pinAccEnvA)) (pinAccGroup_fresh _)
    (pinAccGroup_layout _) (pinAccRecA w hT0) (pinAccRec_fresh _)

/-- every resident of `pinAccEnvA` is one of `9`–`12`. -/
theorem pinAcc_mem {r : Nat} {m : CheckedMemberA} (hm : pinAccEnvA.members r = some m) :
    (r = 9 ∧ m = pinAccRelA) ∨ (r = 10 ∧ m = pinAccFamA) ∨
      (r = 11 ∧ m = pinAccIntroA) ∨ (r = 12 ∧ m = pinAccRecMemberA) := by
  by_cases h12 : r = 12
  · subst h12
    have h : pinAccEnvA.members 12 = some pinAccRecMemberA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  by_cases h11 : r = 11
  · subst h11
    have h : pinAccEnvA.members 11 = some pinAccIntroA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  by_cases h10 : r = 10
  · subst h10
    have h : pinAccEnvA.members 10 = some pinAccFamA := rfl
    rw [h] at hm; cases hm
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  by_cases h9 : r = 9
  · subst h9
    have h : pinAccEnvA.members 9 = some pinAccRelA := rfl
    rw [h] at hm; cases hm
    exact Or.inl ⟨rfl, rfl⟩
  · have hnone : pinAccEnvA.members r = none := by
      rw [pinAccEnvA, members_extendEnvA_ne _ 12 _ h12, pinAccGroupEnvA,
        members_extendEnvA_ne _ 11 _ h11, pinAccFamEnvA,
        members_extendEnvA_ne _ 10 _ h10, pinAccRelEnvA,
        members_extendEnvA_ne emptyEnvA 9 _ h9]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

theorem pinAcc_inductive {r : Nat} {m : CheckedMemberA} (hm : pinAccEnvA.members r = some m)
    (hc : m.mclass = .inductiveM) : r = 10 ∧ m = pinAccFamA := by
  rcases pinAcc_mem hm with h | h | h | h
  · rcases h with ⟨_, rfl⟩; simp [pinAccRelA] at hc
  · exact h
  · rcases h with ⟨_, rfl⟩; simp [pinAccIntroA] at hc
  · rcases h with ⟨_, rfl⟩; simp [pinAccRecMemberA] at hc

/-- the small-index profile: `AccT`'s one index domain is `Sort 0`, whose level `1` is the
    family's sort — the index is not large. -/
theorem pinAcc_small : SmallIndexProfileA pinAccEnvA := by
  intro r m u₀ hm hc hbody v hv ρ x y hx hy _
  obtain ⟨_, rfl⟩ := pinAcc_inductive hm hc
  have hPi : piBodyA pinAccFamA.mtypeA = .sort (.succ .zero) := rfl
  rw [hPi] at hbody
  cases hbody
  simp [pinAccFamA, piDomLevelsA, List.drop] at hv
  subst hv
  have hx1 : x = 1 := (Option.some.inj hx).symm
  subst hx1
  have hy1 : y = 1 := (Option.some.inj hy).symm
  subst hy1
  exact Nat.le_refl 1

theorem pinAcc_propElim : PropElimOnlyA pinAccEnvA := by
  intro _ _ _ _ _ fm u₀ _ _ _ _ hfm hind hbody hup _ _ _ _
  obtain ⟨_, rfl⟩ := pinAcc_inductive hfm hind
  simp [pinAccFamA, piBodyA] at hbody
  subst hbody
  have h1 : evalTotal (fun _ => 0) (.succ .zero) = 1 := rfl
  have h0 := hup (fun _ => 0)
  rw [h1] at h0
  exact Nat.noConfusion h0

/-- THE PIN: the Acc-shaped function-recursive `Type` family is admitted, and `EnvSemA` follows
    from the general theorem at every universe arity. -/
theorem envSemA_pinAcc (n : Nat) :
    EnvSemA pinAccEnvA (iotaIfaceA pinAccEnvA) n (fun _ => 1) := by
  obtain ⟨w, ⟨hT0⟩⟩ := pinAccRecTyAt0
  exact envSemA_of_envWfA_rec (E := pinAccEnvA) (n := n) (ρ₀ := fun _ => 1)
    (pinAccWfA w hT0) posValA_one pinAcc_small pinAcc_propElim

/-- `intro`'s second field is function-recursive with TWO inner binders — `y` and the `R y x`
    hypothesis — so its shape is `recursive 2`. -/
theorem pinAcc_intro_shapes :
    ctorShapesA 10 pinAccFamA.nparamsA pinAccIntroA.mtypeA =
      some [.nonrecursive, .recursive 2] := rfl

/-- THE TOOTH: the environment is outside `EnvNoFunA` — `intro`'s `recursive 2` field is
    function-recursive, so the erasure and the bridge refuse the environment. -/
theorem pinAcc_not_noFunA : ¬ EnvNoFunA pinAccEnvA := fun h =>
  h 11 pinAccIntroA 10 pinAccFamA [.nonrecursive, .recursive 2] rfl rfl rfl rfl
    pinAcc_intro_shapes _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) 1 rfl

theorem pinAcc_not_annEnvA : ¬ AnnEnvA pinAccEnvA := fun C => pinAcc_not_noFunA C.noFun

#print axioms pinAccIntroTy
#print axioms pinAccIntroViewA
#print axioms pinAccIntroGroupA
#print axioms pinAccRel_sem
#print axioms pinAccRecTyAt0
#print axioms pinAccWfA
#print axioms envSemA_pinAcc
#print axioms pinAcc_not_noFunA
#print axioms pinAcc_intro_shapes


/-- the copy's ι fires at `intro`, so the refusal is not vacuous: with spine
    `rec M m i (intro X G)` (motive, the one minor, the one index, major) the contraction
    reduces. -/
theorem pinAcc_iota_fires :
    (iotaFnA pinAccEnvA
      (.app (.app (.app (.app (.const 12 [.zero]) (.sort .zero)) (.sort (.succ .zero)))
        (.sort .zero)) (.app (.app (.const 11 []) (.sort .zero)) (.sort .zero)))).isSome = true := by
  decide

/-- the ι layer does not gate on the motive's universe: the same contraction fires at level
    instantiation `[.succ .zero]` (the AnySort instance). -/
theorem pinAcc_iota_fires_anySort :
    (iotaFnA pinAccEnvA
      (.app (.app (.app (.app (.const 12 [.succ .zero]) (.sort .zero)) (.sort (.succ .zero)))
        (.sort .zero)) (.app (.app (.const 11 []) (.sort .zero)) (.sort .zero)))).isSome = true := by
  decide

/-- `PropElimOnlyA` reports, does not gate: `pinAccEnvA` satisfies it VACUOUSLY — `AccT`'s sort
    `Sort 1` is not Prop-profiled — while the `.anySort` recursor at `12` is admitted and ι
    contracts at motive universe `1`. -/
theorem pinAcc_propElim_not_gate :
    PropElimOnlyA pinAccEnvA ∧
    (iotaFnA pinAccEnvA
      (.app (.app (.app (.app (.const 12 [.succ .zero]) (.sort .zero)) (.sort (.succ .zero)))
        (.sort .zero)) (.app (.app (.const 11 []) (.sort .zero)) (.sort .zero)))).isSome = true :=
  ⟨pinAcc_propElim, pinAcc_iota_fires_anySort⟩

#print axioms pinAcc_iota_fires_anySort
#print axioms pinAcc_propElim_not_gate
#print axioms pinAcc_iota_fires
#print axioms pinAcc_not_annEnvA

end Rcic.Declarative.Ann
