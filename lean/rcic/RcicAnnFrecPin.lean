import rcic.RcicAnnEnvBridgeGroup
import rcic.RcicAnnRecPins
import rcic.RcicAnnViewTy

/-!
# R-NoFunRec-1 step 1 (1c-ε3): THE FUNCTION-RECURSIVE PIN AND ITS TOOTH

A view carries no restriction on its fields. The legacy tree has no function-recursive field, so the
erasure and the bridge read that from the environment (`EnvNoFunA`, carried by `AnnEnvA`). This module
shows the scope extension is real, with the γ tree `T`, one constructor `node : (Sort 0 → T) → T`:

* the pin: `T`, `node` and the derived `AnySort` recursor are admitted by `EnvWfA.groupRec` at the
  concrete ι, and `EnvSemA` follows from the general theorem (`envSemA_pinFrec`);
* the tooth: `node`'s stored type has the shape `recursive 1`, a function-recursive field, so the
  environment is not `EnvNoFunA` and not an `AnnEnvA` (`pinFrec_not_annEnvA`): the erasure and the bridge
  refuse it.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- `node`'s one field: `Sort 0 → T`, a function-recursive field with one inner binder. -/
def pinFrecFieldA : FieldA := .frec (.sort .zero) (.succ .zero) [] []

/-- `node : (Sort 0 → T) → T` at `11`, over the family at `10` (`pinNatFamA`: `T : Sort 1`). -/
def pinFrecNodeA : CheckedMemberA :=
  ⟨.constructorM, 0, ctorTypeA 10 (canonLevelsA 0) (.succ .zero) [] [pinFrecFieldA] [], none, 0,
    some (ctorTypeA 10 (canonLevelsA 0) (.succ .zero) [] [pinFrecFieldA] [])⟩

def pinFrecNodeTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 10 = some pinNatFamA) :
    HasTyA E I n Γ pinFrecNodeA.mtypeA (.sort (.imax (.imax (.succ .zero) (.succ .zero)) (.succ .zero))) :=
  .pi Γ _ _ _ _ (.pi Γ _ _ _ _ (.sort Γ .zero) (pinNatConstTy (Γ := .assumption (.sort .zero) :: Γ) h))
    (pinNatConstTy (Γ := .assumption _ :: Γ) h)

def pinFrecNodeViewA (I : IotaIfaceA) :
    CtorViewA emptyEnvA I 10 pinNatFamA pinNatFamViewA pinFrecNodeA where
  mirrors := []
  fields := [pinFrecFieldA]
  res := []
  stored := rfl
  mirrorsConv := .nil []
  typed := .frec [] 0 (.sort .zero) (.succ .zero) [] [] [] []
    (.plain [] 0 (.sort .zero) (.succ .zero) [] [] (.sort [] .zero) (.nil _ _ [] (.nil _)))
    (.nil [] 0 [] (.nil _))
  univ := fun _ _ h => by cases List.mem_singleton.mp h
  univI := fun B uB Bs idx h d hd => by
    cases List.mem_singleton.mp h
    cases List.mem_singleton.mp hd
    exact Or.inr ⟨fun _ => Nat.succ_pos 0, fun ρ x y hx hy => by
      cases hx.symm.trans hy
      exact Nat.le_refl _⟩
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => by cases List.mem_singleton.mp h; trivial)
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinFrecNodeTy pinNatFamEnv_fam⟩⟩

def pinFrecNodeGroupA (I : IotaIfaceA) : GroupCtorA I emptyEnvA 10 pinNatFamA pinNatFamViewA where
  ref := 11
  member := pinFrecNodeA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => rfl
  u := .imax (.imax (.succ .zero) (.succ .zero)) (.succ .zero)
  hT := pinFrecNodeTy pinNatFamEnv_fam
  hlvl := rfl
  view := pinFrecNodeViewA I
  hnorm := rfl
  hclN := fun _ => rfl
  hlvlN := rfl

def pinFrecCs (I : IotaIfaceA) : List (GroupCtorA I emptyEnvA 10 pinNatFamA pinNatFamViewA) :=
  [pinFrecNodeGroupA I]

def pinFrecGroupEnvA : ResolvedEnvA := extendEnvA pinNatFamEnvA 11 pinFrecNodeA

theorem pinFrecGroupEnv_eq (I : IotaIfaceA) :
    groupEnvA emptyEnvA 10 pinNatFamA ((pinFrecCs I).map GroupCtorA.entry) = pinFrecGroupEnvA := rfl

theorem pinFrecGroup_fresh (I : IotaIfaceA) :
    GroupFreshA emptyEnvA 10 pinNatFamA ((pinFrecCs I).map GroupCtorA.entry) := ⟨rfl, rfl⟩

theorem pinFrecGroup_layout (I : IotaIfaceA) :
    (pinFrecCs I).reverse.map GroupCtorA.ref = List.range' (10 + 1) (pinFrecCs I).length := rfl

theorem pinFrecGroup_closed : EnvClosedA pinFrecGroupEnvA := by
  intro r m hm
  by_cases h11 : r = 11
  · subst h11
    have h : pinFrecGroupEnvA.members 11 = some pinFrecNodeA := rfl
    rw [h] at hm
    cases hm
    exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  by_cases h10 : r = 10
  · subst h10
    have h : pinFrecGroupEnvA.members 10 = some pinNatFamA := rfl
    rw [h] at hm
    cases hm
    exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  · have hnone : pinFrecGroupEnvA.members r = none := by
      rw [pinFrecGroupEnvA, members_extendEnvA_ne _ 11 pinFrecNodeA h11, pinNatFamEnvA,
        members_extendEnvA_ne emptyEnvA 10 pinNatFamA h10]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

/-- `EnvNormClosedA`/`EnvNormLevelsA` at the pin group (R-NoDeltaRec-3b): the family's `normA` is
    `none`; the node's is its stored type (`ctorMemberA`'s shape, no δ-reached field), closed and
    level-bounded by evaluation. -/
theorem pinFrecGroup_normClosed : EnvNormClosedA pinFrecGroupEnvA := by
  intro r m hm _ _ hT _
  by_cases h11 : r = 11
  · subst h11
    have h : pinFrecGroupEnvA.members 11 = some pinFrecNodeA := rfl
    rw [h] at hm
    cases hm
    cases hT
    rfl
  by_cases h10 : r = 10
  · subst h10
    have h : pinFrecGroupEnvA.members 10 = some pinNatFamA := rfl
    rw [h] at hm
    cases hm
    exact Option.noConfusion hT
  · have hnone : pinFrecGroupEnvA.members r = none := by
      rw [pinFrecGroupEnvA, members_extendEnvA_ne _ 11 pinFrecNodeA h11, pinNatFamEnvA,
        members_extendEnvA_ne emptyEnvA 10 pinNatFamA h10]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

theorem pinFrecGroup_normLevels : EnvNormLevelsA pinFrecGroupEnvA := by
  intro r m hm _ _ hT
  by_cases h11 : r = 11
  · subst h11
    have h : pinFrecGroupEnvA.members 11 = some pinFrecNodeA := rfl
    rw [h] at hm
    cases hm
    cases hT
    rfl
  by_cases h10 : r = 10
  · subst h10
    have h : pinFrecGroupEnvA.members 10 = some pinNatFamA := rfl
    rw [h] at hm
    cases hm
    exact Option.noConfusion hT
  · have hnone : pinFrecGroupEnvA.members r = none := by
      rw [pinFrecGroupEnvA, members_extendEnvA_ne _ 11 pinFrecNodeA h11, pinNatFamEnvA,
        members_extendEnvA_ne emptyEnvA 10 pinNatFamA h10]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

/-- the recursor's member: the `AnySort` recursor built from the views. -/
def pinFrecRecMemberA : CheckedMemberA :=
  ⟨.recursorM, 1, groupRecTypeA pinNatFamViewA (pinFrecCs noIotaA) .anySort, none, 0, none⟩

def pinFrecEnvA : ResolvedEnvA := extendEnvA pinFrecGroupEnvA 12 pinFrecRecMemberA

theorem pinFrecRec_fresh (I : IotaIfaceA) :
    (groupEnvA emptyEnvA 10 pinNatFamA ((pinFrecCs I).map GroupCtorA.entry)).members
      (10 + 1 + (pinFrecCs I).length) = none := rfl

def pinFrecGroupWfA (I : IotaIfaceA) : EnvWfA I pinFrecGroupEnvA :=
  .group emptyEnvA 10 pinNatFamA (.succ (.succ .zero)) .empty rfl rfl (fun _ => rfl)
    (.sort [] (.succ .zero)) rfl pinNatFamViewA (pinFrecCs I) (pinFrecGroup_fresh I)

/-- the recursor's type, typed in the DerivationScope at the interface of the group alone (the general
    typing of a built recursor type, whose minor reads the function-recursive field's hypothesis). -/
theorem pinFrecRecTyAt0 :
    ∃ w : Level, Nonempty (HasTyA pinFrecGroupEnvA (iotaIfaceA pinFrecGroupEnvA) (0 + 1) []
      (groupRecTypeA pinNatFamViewA (pinFrecCs (iotaIfaceA pinFrecGroupEnvA)) .anySort) (.sort w)) :=
  groupRecTypeA_hasTy_der (cs := pinFrecCs (iotaIfaceA pinFrecGroupEnvA)) (elim := .anySort)
    (.sort [] (.succ .zero)) (pinFrecGroup_fresh _) emptyEnvA_closed pinFrecGroup_closed
    (fun _ _ h => Option.noConfusion h) (fun _ _ h => Option.noConfusion h)
    (iotaFnA_lift pinFrecGroup_closed pinFrecGroup_normClosed)
    (iotaFnA_subst pinFrecGroup_closed pinFrecGroup_normClosed)
    (recHead_of_groupEnvA (fm := pinNatFamA) (es := [(11, pinFrecNodeA)]) rfl
      (fun _ he => by cases List.mem_singleton.mp he; rfl) (iotaFnA_recHead _))
    (iotaFnA_recHead _) (emptyEnvA_sem _ 0 (fun _ => 1)) posValA_one

theorem pinFrecGroupAgree :
    IfaceAgreeA pinFrecGroupEnvA (iotaIfaceA pinFrecGroupEnvA) (iotaIfaceA pinFrecEnvA) :=
  ifaceAgreeA_prefix (pinFrecGroupWfA (iotaIfaceA pinFrecGroupEnvA))
    (prefixA_extend pinFrecGroupEnvA 12 pinFrecRecMemberA rfl)

theorem pinFrecRecBuilt_closed (k : Nat) :
    liftA k 1 pinFrecRecMemberA.mtypeA = pinFrecRecMemberA.mtypeA :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide))

/-- the derived recursor at a typing of its built type (`pinFrecRecTyAt0` supplies one). -/
def pinFrecRecA (w : Level)
    (hT0 : HasTyA pinFrecGroupEnvA (iotaIfaceA pinFrecGroupEnvA) (0 + 1) []
      (groupRecTypeA pinNatFamViewA (pinFrecCs (iotaIfaceA pinFrecGroupEnvA)) .anySort) (.sort w)) :
    GroupRecA (iotaIfaceA pinFrecEnvA) emptyEnvA 10 pinNatFamA pinNatFamViewA
      (pinFrecCs (iotaIfaceA pinFrecEnvA)) where
  member := pinFrecRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := pinFrecRecBuilt_closed
  u := w
  hT := by
    rw [pinFrecGroupEnv_eq]
    exact hasTyIfaceA pinFrecGroupAgree hT0
  hlvl := by decide

/-- `T`, `node` and the derived recursor, admitted by `EnvWfA.groupRec` at the concrete ι. -/
def pinFrecWfA (w : Level)
    (hT0 : HasTyA pinFrecGroupEnvA (iotaIfaceA pinFrecGroupEnvA) (0 + 1) []
      (groupRecTypeA pinNatFamViewA (pinFrecCs (iotaIfaceA pinFrecGroupEnvA)) .anySort) (.sort w)) :
    EnvWfA (iotaIfaceA pinFrecEnvA) pinFrecEnvA :=
  .groupRec emptyEnvA 10 pinNatFamA (.succ (.succ .zero)) .empty rfl rfl (fun _ => rfl)
    (.sort [] (.succ .zero)) rfl pinNatFamViewA (pinFrecCs (iotaIfaceA pinFrecEnvA))
    (pinFrecGroup_fresh _) (pinFrecGroup_layout _) (pinFrecRecA w hT0) (pinFrecRec_fresh _)

/-- every resident of `pinFrecEnvA` is one of `10`–`12`. -/
theorem pinFrec_mem {r : Nat} {m : CheckedMemberA} (hm : pinFrecEnvA.members r = some m) :
    (r = 10 ∧ m = pinNatFamA) ∨ (r = 11 ∧ m = pinFrecNodeA) ∨ (r = 12 ∧ m = pinFrecRecMemberA) := by
  by_cases h12 : r = 12
  · subst h12
    have h : pinFrecEnvA.members 12 = some pinFrecRecMemberA := rfl
    rw [h] at hm
    cases hm
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  by_cases h11 : r = 11
  · subst h11
    have h : pinFrecEnvA.members 11 = some pinFrecNodeA := rfl
    rw [h] at hm
    cases hm
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  by_cases h10 : r = 10
  · subst h10
    have h : pinFrecEnvA.members 10 = some pinNatFamA := rfl
    rw [h] at hm
    cases hm
    exact Or.inl ⟨rfl, rfl⟩
  · have hnone : pinFrecEnvA.members r = none := by
      rw [pinFrecEnvA, members_extendEnvA_ne _ 12 _ h12, pinFrecGroupEnvA,
        members_extendEnvA_ne _ 11 _ h11, pinNatFamEnvA, members_extendEnvA_ne emptyEnvA 10 _ h10]
      rfl
    rw [hnone] at hm
    exact Option.noConfusion hm

theorem pinFrec_inductive {r : Nat} {m : CheckedMemberA} (hm : pinFrecEnvA.members r = some m)
    (hc : m.mclass = .inductiveM) : r = 10 ∧ m = pinNatFamA := by
  rcases pinFrec_mem hm with h | h | h
  · exact h
  · rcases h with ⟨_, rfl⟩
    simp [pinFrecNodeA] at hc
  · rcases h with ⟨_, rfl⟩
    simp [pinFrecRecMemberA] at hc

theorem pinFrec_small : SmallIndexProfileA pinFrecEnvA := by
  intro r m u₀ hm hc _ v hv _ _ _ _ _ _
  obtain ⟨_, rfl⟩ := pinFrec_inductive hm hc
  simp [pinNatFamA, piDomLevelsA, List.drop] at hv

theorem pinFrec_propElim : PropElimOnlyA pinFrecEnvA := by
  intro _ _ _ _ _ fm u₀ _ _ _ _ hfm hind hbody hup _ _ _ _
  obtain ⟨_, rfl⟩ := pinFrec_inductive hfm hind
  simp [pinNatFamA, piBodyA] at hbody
  subst hbody
  have h1 : evalTotal (fun _ => 0) (.succ .zero) = 1 := rfl
  have h0 := hup (fun _ => 0)
  rw [h1] at h0
  exact Nat.noConfusion h0

/-- THE PIN: the function-recursive `Type` family is admitted, and `EnvSemA` follows from the general
    theorem at every universe arity. -/
theorem envSemA_pinFrec (n : Nat) :
    EnvSemA pinFrecEnvA (iotaIfaceA pinFrecEnvA) n (fun _ => 1) := by
  obtain ⟨w, ⟨hT0⟩⟩ := pinFrecRecTyAt0
  exact envSemA_of_envWfA_rec (E := pinFrecEnvA) (n := n) (ρ₀ := fun _ => 1)
    (pinFrecWfA w hT0) posValA_one pinFrec_small pinFrec_propElim

/-- `node`'s one field is function-recursive: its stored type reads the shape `recursive 1`. -/
theorem pinFrec_node_shapes :
    ctorShapesA 10 pinNatFamA.nparamsA pinFrecNodeA.mtypeA = some [.recursive 1] := rfl

/-- THE TOOTH: the environment is outside the erasure's and the bridge's scope. The restriction the
    erasure and the bridge read (`EnvNoFunA`) fails at `node`, so `AnnEnvA` refuses the environment. -/
theorem pinFrec_not_noFunA : ¬ EnvNoFunA pinFrecEnvA := fun h =>
  h 11 pinFrecNodeA 10 pinNatFamA [.recursive 1] rfl rfl rfl rfl pinFrec_node_shapes _
    (List.mem_singleton_self _) 0 rfl

theorem pinFrec_not_annEnvA : ¬ AnnEnvA pinFrecEnvA := fun C => pinFrec_not_noFunA C.noFun

/-- the copy's ι fires at `node`, so the refusal is not vacuous: `rec P m (node g)` reduces. -/
theorem pinFrec_iota_fires :
    (iotaFnA pinFrecEnvA
      (.app (.app (.app (.const 12 [.zero]) (.sort .zero)) (.sort (.succ .zero)))
        (.app (.const 11 []) (.sort .zero)))).isSome = true := by
  decide

/-- the ι layer does not gate on the motive's universe: the same contraction fires at level
    instantiation `[.succ .zero]` (the AnySort instance, `u = 1`) — `iotaFnA` reads `s.ls` only
    into `instantiateLevelsA` on the schema (`RcicAnnIota.lean:133`), never against a sort bound.
    The iotaXch-sort check of the S2 papers, pinned. -/
theorem pinFrec_iota_fires_anySort :
    (iotaFnA pinFrecEnvA
      (.app (.app (.app (.const 12 [.succ .zero]) (.sort .zero)) (.sort (.succ .zero)))
        (.app (.const 11 []) (.sort .zero)))).isSome = true := by
  decide

/-- `PropElimOnlyA` reports, does not gate (cc's S2 check): `pinFrecEnvA` satisfies it
    VACUOUSLY — its only family `T : Sort 1` is not Prop-profiled, so `pinFrec_propElim`'s
    conditional never fires — while the `.anySort` recursor at `12` is admitted
    (`pinFrecRecMemberA`) and ι contracts at motive universe `1`
    (`pinFrec_iota_fires_anySort`). The classification and the AnySort elimination coexist. -/
theorem pinFrec_propElim_not_gate :
    PropElimOnlyA pinFrecEnvA ∧
    (iotaFnA pinFrecEnvA
      (.app (.app (.app (.const 12 [.succ .zero]) (.sort .zero)) (.sort (.succ .zero)))
        (.app (.const 11 []) (.sort .zero)))).isSome = true :=
  ⟨pinFrec_propElim, pinFrec_iota_fires_anySort⟩

#print axioms pinFrec_iota_fires_anySort
#print axioms pinFrec_propElim_not_gate
#print axioms pinFrecNodeViewA
#print axioms pinFrecWfA
#print axioms envSemA_pinFrec
#print axioms pinFrec_not_noFunA
#print axioms pinFrec_not_annEnvA
#print axioms pinFrec_iota_fires

end Rcic.Declarative.Ann
