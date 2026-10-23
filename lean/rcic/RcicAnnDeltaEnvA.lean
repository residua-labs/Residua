import rcic.RcicAnnDeltaPinD
import rcic.RcicAnnIotaWf
import rcic.RcicAnnViewTy

/-!
# R-NoDeltaRec class (b): the ANNOTATED `drEnv` twin — `drEnvA` admitted by `EnvWfA`

`RcicAnnDeltaPin`/`RcicAnnDeltaPinD` built the `.drecD` field and the member `drCtorMemberAD`
(`mk : Id F → F` with `normA = Π (x : F), F`); `RcicAnnIotaCorrD` discharged the erased-side union
certificate `envCorrAnnDU_drEnv` and left the ann-side composition gated on `NormCorrD`.
What was missing is the environment the certificate composes over: an annotated copy of `drEnv`
(`Id : Sort 1 → Sort 1 := λ A. A` at `0`, `F` at `1`, `mk` at `2`, `F.rec` at `3`) whose erasure is
`drEnv` and whose admission `EnvWfA` carries the `.drecD` evidence `CtorViewA.drecD_typed` — the
`HasTyA`/`ConvA` mirror of `drCtorViewTD`'s typed-side `drecD_typed`.

* `drFieldDomTyA`: `Id F` types at `Sort 1` in the family's extension (the `HasTyA` of
  `drCtorViewTD`'s `drFieldTyTD`).
* `drFieldDomConvA`: `Id F ≡ F` by δ at `Id` then β (`drConvTD` on the copy). The `.drecD` evidence
  and `normConv`/`normTyped` follow; `drCtorViewAD`/`drCtorA`/`drRecA` assemble the group, and
  `drEnvWfA` admits `drEnvA` by `EnvWfA.groupRec`.
* The teeth stay named: `dr_not_envNormEraseA` (the stored/normed types genuinely diverge,
  `drCtorMemberA_diverge` — `iotaErasesTUA_of_envWfA`'s `hn` route is out), `drNoFunA`
  (no `.recursive (_+1)` shape — the frec gate untouched).

`closure_claim` stays 0.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the members and the environment -/

/-- `Id : Sort 1 → Sort 1 := λ A. A` at `0`, annotated: the binder sort `Sort 1` types at
    `Sort 2`, so the annotations are `succ (succ zero)`. -/
def drIdMemberA : CheckedMemberA :=
  ⟨.definitionM, 0,
    .pi (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero)),
    some (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)), 0, none⟩

/-- `F : Sort 1` at `1`. -/
def drFamMemberA : CheckedMemberA := famMemberA 0 [] [] (.succ .zero)

/-- the `.drecD` field's surface domain `Id F`, annotated. -/
def drFieldDomA : ExprA := .app (.const 0 []) (.const 1 [])

def drIdEnvA : ResolvedEnvA := extendEnvA emptyEnvA 0 drIdMemberA
def drFamEnvA : ResolvedEnvA := extendEnvA drIdEnvA 1 drFamMemberA
/-- the group's environment: `drIdEnvA` extended by the family and `mk`. -/
def drGroupEnvA : ResolvedEnvA := extendEnvA drFamEnvA 2 drCtorMemberAD

/-- the family view: no parameters, no indices, `Sort 1`, `UniformType`. -/
def drFamViewA : FamViewA drFamMemberA where
  params := []
  indices := []
  sort := .succ .zero
  stored := rfl
  nparams := rfl
  profile := Or.inr fun ν => Nat.succ_pos _

theorem drIdMemberA_erase : eraseMember drIdMemberA = drIdMember := rfl

theorem drFamMemberA_erase : eraseMember drFamMemberA = drFamMember := rfl

/-- `mk`'s member erases to `main`'s stored one — `normA` is dropped by `eraseMember`,
    the stored type's own erasure is `drFieldA_builds`. -/
theorem drCtorMemberAD_erase : eraseMember drCtorMemberAD = drMkMember := by
  rw [show eraseMember drCtorMemberAD =
      ⟨.constructorM, 0, erase (ctorTypeA 1 [] (.succ .zero) [] [drFieldA] []), none⟩ from rfl,
    drFieldA_builds]
  rfl

theorem drIdEnvA_members (r : Nat) :
    drIdEnvA.members r = if r = 0 then some drIdMemberA else none := rfl

theorem drFamEnvA_members (r : Nat) :
    drFamEnvA.members r =
      if r = 1 then some drFamMemberA else if r = 0 then some drIdMemberA else none := rfl

theorem drGroupEnvA_members (r : Nat) :
    drGroupEnvA.members r =
      if r = 2 then some drCtorMemberAD else if r = 1 then some drFamMemberA
      else if r = 0 then some drIdMemberA else none := rfl

/-! ## (2) the field evidence: `Id F` typed and converted in the family's extension -/

/-- `λ A. A` at its type, in the family's extension — `drIdBodyTyTD` on the copy. -/
def drIdBodyTyA (I : IotaIfaceA) : HasTyA drFamEnvA I 0 []
    (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0))
    (.pi (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero))) :=
  .lam [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0) (.sort (.succ .zero))
    (.succ (.succ .zero)) (.sort [] (.succ .zero)) (.sort _ _)
    (.bvar [.assumption (.sort (.succ .zero))] 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (.sort _ _))

/-- `Id`'s type, in any context — `Sort 1 → Sort 1` at `Sort (imax 2 2)`. -/
def drIdTyA (I : IotaIfaceA) : HasTyA drFamEnvA I 0 []
    (.pi (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero)))
    (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
  .pi [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero))
    (.sort [] (.succ .zero)) (.sort _ _)

/-- `F` at `Sort 1` in any context over `drFamEnvA`. -/
def drFamConstTyA (I : IotaIfaceA) (Γ : LCtxA) :
    HasTyA drFamEnvA I 0 Γ (.const 1 []) (.sort (.succ .zero)) :=
  .const Γ 1 [] drFamMemberA _ rfl rfl rfl (.sort _ _)

/-- `Id F : Sort 1` in the family's extension scope — the `drecD_typed` typing
    (`drFieldTyTD` on the copy). -/
def drFieldDomTyA (I : IotaIfaceA) :
    HasTyA drFamEnvA I 0 [] drFieldDomA (.sort (.succ .zero)) :=
  .app [] (.const 0 []) (.const 1 []) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)) (.succ (.succ .zero)) (.succ (.succ .zero))
    (.sort _ _) (.sort _ _)
    (.const [] 0 [] drIdMemberA _ rfl rfl rfl (drIdTyA I)) (drFamConstTyA I [])

/-- `Id F ≡ (λ A. A) F`: δ at the head, under application — `drConvTD_delta` on the copy. -/
def drFieldDomConvA_delta (I : IotaIfaceA) : ConvA drFamEnvA I 0 [] drFieldDomA
    (.app (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.const 1 []))
    (.sort (.succ .zero)) :=
  .app [] (.const 0 [])
    (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.const 1 []) (.const 1 [])
    (.sort (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero)) (.succ (.succ .zero))
    (.delta [] 0 [] drIdMemberA _ rfl rfl rfl rfl rfl (drIdBodyTyA I))
    (.refl _ _ _ (drFamConstTyA I []))
    (.sort _ _)
    (.app [] (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.const 1 [])
      (.sort (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero)) (.succ (.succ .zero))
      (.succ (.succ .zero)) (.sort _ _) (.sort _ _) (drIdBodyTyA I) (drFamConstTyA I []))

/-- `(λ A. A) F ≡ F`: β — `drConvTD_beta` on the copy. -/
def drFieldDomConvA_beta (I : IotaIfaceA) : ConvA drFamEnvA I 0 []
    (.app (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.const 1 []))
    (.const 1 []) (.sort (.succ .zero)) :=
  .beta [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0) (.const 1 [])
    (.sort (.succ .zero)) (.sort _ _)
    (.bvar [.assumption (.sort (.succ .zero))] 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
      (.sort _ _))
    (drFamConstTyA I []) (drFamConstTyA I [])

/-- `Id F ≡ F` in the family's extension — the `.drecD` conversion
    (`drConvTD` on the copy). -/
def drFieldDomConvA (I : IotaIfaceA) :
    ConvA drFamEnvA I 0 [] drFieldDomA (.const 1 []) (.sort (.succ .zero)) :=
  .trans _ _ _ _ _ (drFieldDomConvA_delta I) (drFieldDomConvA_beta I)

/-- the `.drecD` evidence at `[drFieldA]`: the surface domain `Id F` types at the family's sort
    and converts to the family application `F` — `drCtorViewTD_drecD` on the copy. -/
def drCtorViewAD_drecD (I : IotaIfaceA) :
    DrecDTypedA drIdEnvA I 1 drFamMemberA drFamViewA [drFieldA] := by
  intro fsPre D idx fsRest h
  cases fsPre with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨hf, -⟩ := h
      rw [show drFieldA = .drecD drFieldDomA [] from rfl] at hf
      obtain ⟨hD, hidx⟩ := FieldA.drecD.inj hf
      subst hD; subst hidx
      exact ⟨⟨drFieldDomTyA I⟩, ⟨drFieldDomConvA I⟩, fun x hx => nomatch hx⟩
  | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact absurd (List.append_eq_nil.mp h.2.symm).2 (List.cons_ne_nil _ _)

/-- the stored/normed conversion: `Π (x : Id F), F ≡ Π (x : F), F` — the `.drecD` domain's
    conversion lifted through the constructor telescope's one binder. -/
def drCtorNormConvA (I : IotaIfaceA) : TyConvA drFamEnvA I 0 []
    (ctorTypeA 1 [] (.succ .zero) [] [drFieldA] [])
    (ctorTypeA 1 [] (.succ .zero) [] [drFieldA.norm] []) :=
  .of _ _ _ (.imax (.succ .zero) (.succ .zero)) (.imax (.succ .zero) (.succ .zero))
    (.imax (.succ .zero) (.succ .zero))
    (.pi [] drFieldDomA (.succ .zero) (.const 1 []) (.succ .zero)
      (drFieldDomTyA I) (drFamConstTyA I _))
    (eqNA_refl _)
    (.pi [] (.const 1 []) (.succ .zero) (.const 1 []) (.succ .zero)
      (drFamConstTyA I []) (drFamConstTyA I _))
    (eqNA_refl _)
    (.pi [] drFieldDomA (.const 1 []) (.const 1 []) (.const 1 [])
      (.succ .zero) (.succ .zero) (.succ .zero) (.succ .zero)
      (eqNA_refl _) (eqNA_refl _)
      (drFieldDomConvA I)
      (.refl _ _ _ (drFamConstTyA I _))
      (.pi [] (.const 1 []) (.succ .zero) (.const 1 []) (.succ .zero)
        (drFamConstTyA I []) (drFamConstTyA I _)))

/-- `mk`'s constructor view on the copy: `.drecD`-labeled field, its evidence, the normed
    conversion and typing — the `CtorViewA` mirror of `drCtorViewTD`. -/
def drCtorViewAD (I : IotaIfaceA) :
    CtorViewA drIdEnvA I 1 drFamMemberA drFamViewA drCtorMemberAD where
  mirrors := []
  fields := [drFieldA]
  res := []
  stored := rfl
  mirrorsConv := .nil _
  typed := .drecD [] 0 drFieldDomA [] [] [] (.nil _) (.nil _ 0 _ (.nil _))
  univ := fun D u h => by
    have he : FieldA.plain D u = .drecD drFieldDomA [] := List.mem_singleton.mp h
    exact FieldA.noConfusion he
  univI := fun B uB Bs idx h => by
    have he : FieldA.frec B uB Bs idx = .drecD drFieldDomA [] := List.mem_singleton.mp h
    exact FieldA.noConfusion he
  drecD_typed := drCtorViewAD_drecD I
  normConv := ⟨drCtorNormConvA I⟩
  normTyped := ⟨_, ⟨.pi [] (.const 1 []) (.succ .zero) (.const 1 []) (.succ .zero)
    (drFamConstTyA I []) (drFamConstTyA I _)⟩⟩

/-- `mk`'s stored type `Π (x : Id F), F` typed at `Sort (imax 1 1)` in the family's extension —
    `drMkTyT` on the copy. -/
def drMkTyA (I : IotaIfaceA) : HasTyA drFamEnvA I 0 [] drCtorMemberAD.mtypeA
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] drFieldDomA (.succ .zero) (.const 1 []) (.succ .zero)
    (drFieldDomTyA I) (drFamConstTyA I _)

/-- `mk` as a group constructor of `drIdEnvA`. -/
def drCtorA (I : IotaIfaceA) : GroupCtorA I drIdEnvA 1 drFamMemberA drFamViewA where
  ref := 2
  member := drCtorMemberAD
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => rfl
  u := .imax (.succ .zero) (.succ .zero)
  hT := drMkTyA I
  hlvl := by decide
  view := drCtorViewAD I
  hnorm := rfl
  hclN := fun _ => rfl
  hlvlN := by
    show exprLevelsBoundedA 0 (ctorTypeA 1 [] (.succ .zero) [] [.drec []] []) = true
    decide

/-- the group's constructor list. -/
def drCs (I : IotaIfaceA) : List (GroupCtorA I drIdEnvA 1 drFamMemberA drFamViewA) := [drCtorA I]

/-- `F.rec`'s member: the `.anySort` recursor built from the views. -/
def drRecMemberA : CheckedMemberA :=
  ⟨.recursorM, 1, groupRecTypeA drFamViewA (drCs noIotaA) .anySort, none, 0, none⟩

/-- `drEnv`'s annotated twin: `Id`, `F`, `mk`, `F.rec`. -/
def drEnvA : ResolvedEnvA := extendEnvA drGroupEnvA 3 drRecMemberA

/-! ## (3) admission -/

/-- `Id` as a definition member of `drIdEnvA`. -/
def drIdWfA (I : IotaIfaceA) : EnvWfA I drIdEnvA :=
  .definitionM emptyEnvA 0 _ _ _ .empty rfl
    (.pi [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort [] (.succ .zero)) (.sort _ _))
    (.lam [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0) (.sort (.succ .zero))
      (.succ (.succ .zero)) (.sort [] (.succ .zero)) (.sort _ _)
      (.bvar [.assumption (.sort (.succ .zero))] 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
        (.sort _ _)))
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- `F`, `mk` as a group over `drIdEnvA` — the `EnvWfA.group` step, no recursor yet. -/
def drGroupWfA (I : IotaIfaceA) : EnvWfA I drGroupEnvA :=
  .group drIdEnvA 1 drFamMemberA (.succ (.succ .zero)) (drIdWfA I) rfl rfl (fun _ => rfl)
    (.sort [] (.succ .zero)) rfl drFamViewA (drCs I) ⟨rfl, rfl⟩

/-- `drIdEnvA` has no family or constructor member. -/
theorem drIdEnvA_noFam : NoFamA drIdEnvA := fun r m hres => by
  by_cases h0 : r = 0
  · subst h0; rw [drIdEnvA_members] at hres; cases hres
    exact ⟨by decide, by decide⟩
  · have hmem : drIdEnvA.members r = none := by rw [drIdEnvA_members]; exact if_neg h0
    rw [hmem] at hres; exact Option.noConfusion hres

/-- `drIdEnvA` has no recursor member. -/
theorem drIdEnvA_noRec : NoRecA drIdEnvA := fun r m hres => by
  by_cases h0 : r = 0
  · subst h0; rw [drIdEnvA_members] at hres; cases hres
    decide
  · have hmem : drIdEnvA.members r = none := by rw [drIdEnvA_members]; exact if_neg h0
    rw [hmem] at hres; exact Option.noConfusion hres

/-- `drGroupEnvA`'s recursor head read factors through `drIdEnvA`'s — the group's members are
    a family and a constructor. -/
def drGroupRecHead : IotaRecHeadA drIdEnvA (iotaIfaceA drGroupEnvA) :=
  recHead_of_groupEnvA (fm := drFamMemberA) rfl (es := [(2, drCtorMemberAD)])
    (fun _ he => by cases List.mem_singleton.mp he; rfl) (iotaFnA_recHead drGroupEnvA)

/-- `F.rec`'s built type is typed in the group's scope — `groupRecTypeA_hasTy_der` at the
    group's own ι. -/
theorem drRecTyAt0 :
    ∃ w : Level, Nonempty (HasTyA drGroupEnvA (iotaIfaceA drGroupEnvA) (0 + 1) []
      (groupRecTypeA drFamViewA (drCs (iotaIfaceA drGroupEnvA)) .anySort) (.sort w)) :=
  groupRecTypeA_hasTy_der (cs := drCs (iotaIfaceA drGroupEnvA)) (elim := .anySort)
    (.sort [] (.succ .zero)) ⟨rfl, rfl⟩
    (envWfA_closed (drIdWfA (iotaIfaceA drGroupEnvA)))
    (envWfA_closed (drGroupWfA (iotaIfaceA drGroupEnvA)))
    (envWfA_normCtorType (drIdWfA (iotaIfaceA drGroupEnvA)))
    (envWfA_normClosed (drIdWfA (iotaIfaceA drGroupEnvA)))
    (iotaFnA_lift (envWfA_closed (drGroupWfA (iotaIfaceA drGroupEnvA)))
      (envWfA_normClosed (drGroupWfA (iotaIfaceA drGroupEnvA))))
    (iotaFnA_subst (envWfA_closed (drGroupWfA (iotaIfaceA drGroupEnvA)))
      (envWfA_normClosed (drGroupWfA (iotaIfaceA drGroupEnvA))))
    drGroupRecHead
    (iotaFnA_recHead (groupEnvA drIdEnvA 1 drFamMemberA [(2, drCtorMemberAD)]))
    (envSemA_of_envWfA (drIdWfA (iotaIfaceA drGroupEnvA))
      (iotaFnA_lift (envWfA_closed (drGroupWfA (iotaIfaceA drGroupEnvA)))
        (envWfA_normClosed (drGroupWfA (iotaIfaceA drGroupEnvA))))
      (iotaFnA_subst (envWfA_closed (drGroupWfA (iotaIfaceA drGroupEnvA)))
        (envWfA_normClosed (drGroupWfA (iotaIfaceA drGroupEnvA))))
      (iotaFnA_levels (envWfA_levels (drGroupWfA (iotaIfaceA drGroupEnvA)))
        (envWfA_normLevels (drGroupWfA (iotaIfaceA drGroupEnvA))))
      drGroupRecHead posValA_one
      (envSemIndA_of_noFam drIdEnvA_noFam) (envSemRecA_of_noRec drIdEnvA_noRec))
    posValA_one

/-- the group env's ι agrees with `drEnvA`'s on the shared prefix. -/
theorem drGroupAgree :
    IfaceAgreeA drGroupEnvA (iotaIfaceA drGroupEnvA) (iotaIfaceA drEnvA) :=
  ifaceAgreeA_prefix (drGroupWfA (iotaIfaceA drGroupEnvA))
    (prefixA_extend drGroupEnvA 3 drRecMemberA rfl)

/-- the group's built environment, as `groupEnvA` computes it. -/
theorem drGroupEnv_eq (I : IotaIfaceA) :
    groupEnvA drIdEnvA 1 drFamMemberA ((drCs I).map GroupCtorA.entry) = drGroupEnvA := rfl

/-- `F.rec`'s type is closed: the built recursor type has no free bvar. -/
theorem drRecBuilt_closed (k : Nat) : liftA k 1 drRecMemberA.mtypeA = drRecMemberA.mtypeA :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ (by decide))

/-- `F.rec` as the group's recursor (`GroupRecA`), at a typing of its built type. -/
def drRecA (w : Level)
    (hT0 : HasTyA drGroupEnvA (iotaIfaceA drGroupEnvA) (0 + 1) []
      (groupRecTypeA drFamViewA (drCs (iotaIfaceA drGroupEnvA)) .anySort) (.sort w)) :
    GroupRecA (iotaIfaceA drEnvA) drIdEnvA 1 drFamMemberA drFamViewA
      (drCs (iotaIfaceA drEnvA)) where
  member := drRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := drRecBuilt_closed
  u := w
  hT := by
    rw [drGroupEnv_eq]
    exact hasTyIfaceA drGroupAgree hT0
  hlvl := by decide

/-- `drEnvA` is admitted: `Id`, then `F`, `mk` and `F.rec` as one `groupRec` step — at a typing
    of `F.rec`'s built type (`drRecTyAt0` supplies one; the existential is `Prop`-sorted, so
    consumers destructure it inside their `Prop` goals). -/
def drEnvWfA (w : Level)
    (hT0 : HasTyA drGroupEnvA (iotaIfaceA drGroupEnvA) (0 + 1) []
      (groupRecTypeA drFamViewA (drCs (iotaIfaceA drGroupEnvA)) .anySort) (.sort w)) :
    EnvWfA (iotaIfaceA drEnvA) drEnvA :=
  .groupRec drIdEnvA 1 drFamMemberA (.succ (.succ .zero)) (drIdWfA _) rfl rfl (fun _ => rfl)
    (.sort [] (.succ .zero)) rfl drFamViewA (drCs (iotaIfaceA drEnvA)) ⟨rfl, rfl⟩ rfl
    (drRecA w hT0) rfl

/-! ## (4) erasure and teeth -/

/-- `F.rec`'s member erases to `main`'s stored one: the built recursor type erases to the typed
    build, which decides equal to `drRecTy` — `drRecTD.stored` on the copy side. -/
theorem drRecMemberA_erase : eraseMember drRecMemberA = drRecMember := by
  rw [show eraseMember drRecMemberA =
      ⟨.recursorM, 1, erase (groupRecTypeA drFamViewA (drCs noIotaA) .anySort), none⟩ from rfl]
  unfold groupRecTypeA
  rw [erase_recTypeA _ _ _ _ _ _ _ (fun cd hcd x hx => by
    cases List.mem_singleton.mp hcd
    cases List.mem_singleton.mp hx
    trivial)]
  show (⟨.recursorM, 1,
      recTypeT 1 [] [] [] (RecElimA.anySort.motiveLevel 0)
        [(2, [.drecD drField []], [])], none⟩ : CheckedMember) = drRecMember
  congr

theorem drEnvA_members (r : Nat) :
    (eraseEnv drEnvA).members r = drEnv.members r := by
  rcases r with _ | _ | _ | _ | r'
  · rfl
  · rfl
  · rw [show (eraseEnv drEnvA).members 2 = some (eraseMember drCtorMemberAD) from rfl,
      drCtorMemberAD_erase]
    rfl
  · rw [show (eraseEnv drEnvA).members 3 = some (eraseMember drRecMemberA) from rfl,
      drRecMemberA_erase]
    rfl
  · rfl

/-- the twin's erasure is `drEnv`. -/
theorem drEnvA_erase : eraseEnv drEnvA = drEnv :=
  congrArg ResolvedEnv.mk (funext drEnvA_members)

/-- `drEnvA`'s members are `0`–`3`. -/
theorem drEnvA_mem {r : Nat} {m : CheckedMemberA} (hm : drEnvA.members r = some m) :
    (r = 0 ∧ m = drIdMemberA) ∨ (r = 1 ∧ m = drFamMemberA) ∨
    (r = 2 ∧ m = drCtorMemberAD) ∨ (r = 3 ∧ m = drRecMemberA) := by
  rcases r with _ | _ | _ | _ | r'
  · left; rw [show drEnvA.members 0 = some drIdMemberA from rfl] at hm; cases hm; exact ⟨rfl, rfl⟩
  · right; left
    rw [show drEnvA.members 1 = some drFamMemberA from rfl] at hm; cases hm; exact ⟨rfl, rfl⟩
  · right; right; left
    rw [show drEnvA.members 2 = some drCtorMemberAD from rfl] at hm; cases hm; exact ⟨rfl, rfl⟩
  · right; right; right
    rw [show drEnvA.members 3 = some drRecMemberA from rfl] at hm; cases hm; exact ⟨rfl, rfl⟩
  · rw [show drEnvA.members (r' + 4) = none from rfl] at hm
    exact Option.noConfusion hm

/-- THE TOOTH, environment-level: `drCtorMemberAD_not_envNormEraseA` at `drEnvA` — a `.drecD`
    member's `normA` genuinely rewrites the erased domains. -/
theorem dr_not_envNormEraseA : ¬ EnvNormEraseA drEnvA := fun hn =>
  drCtorMemberA_diverge (hn 2 drCtorMemberAD rfl rfl _ drCtorMemberA_normA.1).symm

/-- the frec gate is untouched: no member reads a `.recursive (_+1)` shape. -/
theorem drNoFunA : EnvNoFunA drEnvA := by
  intro c cm f fm shapes hcm hcls hfam hm hshapes s hs j hs'
  rcases drEnvA_mem hcm with ⟨rfl, mc⟩ | ⟨rfl, mc⟩ | ⟨rfl, mc⟩ | ⟨rfl, mc⟩
  all_goals subst mc
  · exact absurd hcls (by decide)
  · exact absurd hcls (by decide)
  · have hf : f = 1 := by
      have h2 : memberFamRefA drCtorMemberAD = some 1 := rfl
      rw [h2] at hfam
      exact (Option.some.inj hfam).symm
    subst hf
    rw [show drEnvA.members 1 = some drFamMemberA from rfl] at hm
    cases hm
    have hs0 : some shapes = some [.recursive 0] := by
      rw [← hshapes]
      exact drCtorMemberAD_shapes
    cases Option.some.inj hs0
    cases List.mem_singleton.mp hs
    have h0 := FieldShape.recursive.inj hs'
    omega
  · exact absurd hcls (by decide)

#print axioms drEnvWfA
#print axioms drEnvA_erase
#print axioms drCtorViewAD
#print axioms drFieldDomConvA
#print axioms dr_not_envNormEraseA
#print axioms drNoFunA

end Rcic.Declarative.Ann
