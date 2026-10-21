import rcic.RcicAnnDeltaPin
import rcic.RcicAnnIotaCorrN
import rcic.RcicTypedGroupD
import rcic.RcicAnnRowsSupplyD

/-!
# R-NoDeltaRec-5 — the pin: the re-keyed reads and the gate-free scope on the `.drecD` fixture

The fixture is `RcicAnnDeltaPin`'s member, `ctorMemberA 0 1 (.succ .zero) [] [drFieldA] []` —
`mk : Id F → F` with the δ-reached field, whose stored `Π (x : Id F), F` and normalized
`Π (x : F), F` erase differently (`drCtorMemberA_diverge`).

* The re-keyed erased reads (`memberNormTyA`, `ctorShapesA`/`ctorKindsA` off `normA.getD`,
  `peelPis`/`analyzeFields`/`fieldShapesE` on the erased normal form) all answer as admission
  did — `recursive 0`/`directRec` — where the stored type gave none (`drCtorShapesA_none`,
  `drCtorKindsA_none`).
* `EnvNormEraseA` provably fails on any environment containing the member
  (`drCtorMemberAD_not_envNormEraseA`): the gate the re-key removes.
* On the typed side, `drEnv`'s group inhabits `GroupInScopeTD` with the `.drecD`-labeled
  field view (`drCtorViewTD.fields = [.drecD drField []]`), so `drEnvWfT.InScopeD` holds —
  the scope `hsnd` refused (`dr_skel_bridge_refused`), now carried by `DrecDTypedT`
  evidence: `Id F` typed at `Sort 1` (`drFieldTyTD`) and converted to `F` (`drConvTD`, δ
  at `Id` then β).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the re-keyed reads on the fixture member -/

/-- the fixture member, named: `mk` of the δ-reached group as `ctorMemberA` builds it —
    stored `Π (x : Id F), F`, normed `Π (x : F), F` (`drCtorMemberA_normA`). -/
def drCtorMemberAD : CheckedMemberA := ctorMemberA 0 1 (.succ .zero) [] [drFieldA] []

/-- the normalized member type is `Π (x : F), F` — the erased readers' new key. -/
theorem drCtorMemberAD_normTy :
    memberNormTyA drCtorMemberAD = ctorTypeA 1 [] (.succ .zero) [] [.drec []] [] := rfl

/-- the shape reader on the NORMALIZED type: `recursive 0`, admission's verdict
    (`drFieldAnalyze_pin`), where the stored type gave none (`drCtorShapesA_none`). -/
theorem drCtorMemberAD_shapes :
    ctorShapesA 1 0 (memberNormTyA drCtorMemberAD) = some [.recursive 0] := by decide

/-- the kind reader on the NORMALIZED type: `directRec`, where the stored type gave none
    (`drCtorKindsA_none`). -/
theorem drCtorMemberAD_kinds :
    ctorKindsA 1 0 (memberNormTyA drCtorMemberAD) = some [.directRec] := by decide

/-- the normalized type's Π-readings: one domain, `F`, body `F`. -/
theorem drCtorMemberAD_normTy_pi :
    piCountA (memberNormTyA drCtorMemberAD) = 1 ∧
    piDomsA (memberNormTyA drCtorMemberAD) = [.const 1 []] ∧
    piBodyA (memberNormTyA drCtorMemberAD) = .const 1 [] := ⟨rfl, rfl, rfl⟩

/-- the erased normal form is `Π (x : F), F` on `main`'s syntax. -/
theorem drCtorMemberAD_normTy_erase :
    erase (memberNormTyA drCtorMemberAD) = .pi (.const 1 []) (.const 1 []) := rfl

/-- `peelPis` on the erased normal form: `([F], F)` — the erased-domain read the stored
    type refused (`dr_storedReading`). -/
theorem drCtorMemberAD_erase_peelPis :
    peelPis (piCountA (memberNormTyA drCtorMemberAD)) (erase (memberNormTyA drCtorMemberAD)) =
      some ([.const 1 []], .const 1 []) := rfl

/-- `main`'s field analysis on the erased normal form's domains: `directRec`, where the
    stored `Id F` gave `none` (`drMk_noKind`). -/
theorem drCtorMemberAD_analyzeFields :
    analyzeFields 1 [.const 1 []] = some [.directRec] := by decide

/-- the erased field-shapes reader on the same domains: `recursive 0`. -/
theorem drCtorMemberAD_fieldShapesE :
    fieldShapesE 1 [.const 1 []] = some [.recursive 0] := by decide

/-- THE GATE, witnessed failing: an environment holding the member is not `EnvNormEraseA` —
    its `normA` is `some` of the normed type, whose erasure differs from the stored type's
    (`drCtorMemberA_diverge`). This is what `hsnd` was protecting: the legacy route needed
    the invariant everywhere; the D-route does not. -/
theorem drCtorMemberAD_not_envNormEraseA :
    ¬ EnvNormEraseA (extendEnvA emptyEnvA 0 drCtorMemberAD) := fun hn =>
  drCtorMemberA_diverge
    (hn 0 drCtorMemberAD (members_extendEnvA_self emptyEnvA 0 drCtorMemberAD) rfl _
      drCtorMemberA_normA.1).symm

end Rcic.Declarative.Ann

/-! ## (2) the group in the gate-free scope -/

namespace Rcic.Declarative

/-- `Id F` at `Sort 1` in the family's extension scope — `drFieldTyT` at `drFamEnv`. -/
def drFieldTyTD : HasTyT drFamEnv 0 [] drField (.sort (.succ .zero)) := drFieldTyT rfl rfl

/-- `λ A. A` — `Id`'s body — at `Sort 1 → Sort 1` in `drFamEnv`. -/
def drIdBodyTyTD : HasTyT drFamEnv 0 []
    (.lam (.sort (.succ .zero)) (.bvar 0)) (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .lam _ _ _ _ _ (.sort _ _) (.bvar _ 0 _ rfl)

/-- `Id F ≡ (λ A. A) F`: δ at the head, under application. -/
def drConvTD_delta : ConvT drFamEnv 0 [] drField
    (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.const 1 [])) (.sort (.succ .zero)) :=
  .app _ _ _ _ _ (.sort (.succ .zero)) (.sort (.succ .zero))
    (.delta _ 0 [] drIdMember _ rfl rfl rfl rfl rfl drIdBodyTyTD)
    (.refl _ _ _ (.const _ 1 [] drFamMember rfl rfl rfl))

/-- `(λ A. A) F ≡ F`: β. -/
def drConvTD_beta : ConvT drFamEnv 0 []
    (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.const 1 [])) (.const 1 [])
    (.sort (.succ .zero)) :=
  .beta _ (.sort (.succ .zero)) (.bvar 0) (.const 1 []) (.sort (.succ .zero))
    (.succ (.succ .zero)) (.sort _ _) (.bvar _ 0 _ rfl) (.const _ 1 [] drFamMember rfl rfl rfl)

/-- `Id F ≡ F` at the typed judgment — the `DrecDTypedT` conversion. -/
def drConvTD : ConvT drFamEnv 0 [] drField (.const 1 []) (.sort (.succ .zero)) :=
  .trans _ drField _ (.const 1 []) (.sort (.succ .zero)) drConvTD_delta drConvTD_beta

/-- the δ-reached field's typed evidence at `[.drecD drField []]` IN THE BASE `drBase`
    (`drMk_drecDTyped` is its sibling at `drMkEnv`): the surface domain types at the
    family's sort and `TyConvT`-converts to the family application there — the two facts
    `drFieldA_typed_reads` names on the copy side, on `main`. -/
def drCtorViewTD_drecD :
    DrecDTypedT drBase 1 drFamMember drFamViewT [.drecD drField []] := by
  intro fsPre D idx fsRest h
  cases fsPre with
  | nil =>
      simp only [List.nil_append, List.cons.injEq, FieldT.drecD.injEq, List.nil_eq] at h
      obtain ⟨⟨hD, hidx⟩, -⟩ := h
      subst hD; subst hidx
      exact ⟨⟨drFieldTyTD⟩, ⟨.of _ _ _ _ drConvTD⟩, fun x hx => nomatch hx⟩
  | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact absurd (List.append_eq_nil.mp h.2.symm).2 (List.cons_ne_nil _ _)

/-- `mk`'s constructor view — the field AS WRITTEN, `.drecD` labeled. -/
def drCtorViewTD : CtorViewT drBase 1 drFamMember drFamViewT drMkMember where
  mirrors := []
  fields := [.drecD drField []]
  res := []
  stored := rfl
  mirrorsConv := .nil _
  typed := .drecD _ 0 drField [] [] [] (.nil _) (.nil _ 0 [] (.nil _))
  univ := fun D u h => by nomatch h
  drecD_typed := drCtorViewTD_drecD

/-- `mk` as a group constructor. -/
def drCtorTD : GroupCtorT drBase 1 drFamMember drFamViewT where
  ref := 2
  member := drMkMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := .imax (.succ .zero) (.succ .zero)
  hT := drMkTyT
  hlvl := by decide
  view := drCtorViewTD

/-- `F.rec` as the group's recursor: `groupRecTypeT` rebuilds `drRecTy`, `drRecTyT` types
    it. -/
def drRecTD : GroupRecT drBase 1 drFamMember drFamViewT [drCtorTD] where
  member := drRecMember
  hcls := rfl
  hnobody := rfl
  elim := .anySort
  harity := rfl
  stored := by decide
  hclT := fun _ => rfl
  u := drRecSortU
  hT := drRecTyT
  hlvl := by decide

/-- THE SCOPE INSTANCE: the dr group as `GroupInScopeTD` — the scope without `hsnd`,
    inhabited with the `.drecD`-labeled view. -/
def drGroupInScopeTD : GroupInScopeTD drBase 1 drFamMember [(2, drMkMember)] 3 drRecMember
    where
  fv := drFamViewT
  htel := .nil _
  cs := [drCtorTD]
  hctors := rfl
  hlayout := rfl
  grec := drRecTD
  hrr := rfl
  hrm := rfl
  hprof := ⟨fun v hv => absurd hv (List.not_mem_nil _),
    fun h _ _ _ => absurd (h (fun _ => 0)) (by decide)⟩
  hpb := fun d hd => absurd hd (List.not_mem_nil _)

/-- the view's field is `.drecD`-labeled — `hsnd` would refuse THIS presentation
    (`dr_skel_bridge_refused`). -/
theorem drCtorTD_field_isDrecD : ∃ d ∈ drCtorViewTD.fields, d.isDrecD = true :=
  ⟨.drecD drField [], List.mem_cons_self _ _, rfl⟩

/-- `hsnd` fails on the group's constructor list — the gate's refusal, pinned at the same
    view `GroupInScopeTD` accepts. -/
theorem drCtorTD_hsnd_fails :
    ¬ (∀ c ∈ [drCtorTD], ∀ d ∈ c.view.fields, d.isDrecD = false) := fun h =>
  absurd (h drCtorTD (List.mem_cons_self _ _) _ (List.mem_cons_self _ _)) (by decide)

/-- `drEnvWfT.InScopeD`: the `.drecD` group's typed environment is in the D-scope —
    the widened `InScope` the route consumes. -/
theorem drEnvWfT_inScopeD : drEnvWfT.InScopeD := ⟨trivial, ⟨drGroupInScopeTD⟩⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.Ann.drCtorMemberAD
#print axioms Rcic.Declarative.Ann.drCtorMemberAD_shapes
#print axioms Rcic.Declarative.Ann.drCtorMemberAD_kinds
#print axioms Rcic.Declarative.Ann.drCtorMemberAD_normTy_pi
#print axioms Rcic.Declarative.Ann.drCtorMemberAD_erase_peelPis
#print axioms Rcic.Declarative.Ann.drCtorMemberAD_analyzeFields
#print axioms Rcic.Declarative.Ann.drCtorMemberAD_fieldShapesE
#print axioms Rcic.Declarative.Ann.drCtorMemberAD_not_envNormEraseA
#print axioms Rcic.Declarative.drFieldTyTD
#print axioms Rcic.Declarative.drIdBodyTyTD
#print axioms Rcic.Declarative.drConvTD_delta
#print axioms Rcic.Declarative.drConvTD_beta
#print axioms Rcic.Declarative.drConvTD
#print axioms Rcic.Declarative.drCtorViewTD_drecD
#print axioms Rcic.Declarative.drCtorViewTD
#print axioms Rcic.Declarative.drCtorTD
#print axioms Rcic.Declarative.drRecTD
#print axioms Rcic.Declarative.drGroupInScopeTD
#print axioms Rcic.Declarative.drCtorTD_hsnd_fails
#print axioms Rcic.Declarative.drEnvWfT_inScopeD
