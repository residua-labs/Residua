import rcic.RcicAnnTel
import rcic.RcicAnnEnvBridgeGroup
import rcic.RcicTypedDeltaRecPins

/-!
# R-NoDeltaRec-0: THE δ-REACHED FIELD, ON BOTH SIDES OF THE DIVERGENCE

The group of `RcicTypedDeltaRecPins`: `Id : Sort 1 → Sort 1 := λ A, A` at `0`, a family `F : Sort 1` at `1`,
`mk : Id F → F` at `2`. Its one field is directly recursive after δ.

* Admission reads it (`drFieldAnalyze_pin`, from `dr_fieldAnalyze`): `.permitted (.recursive 0) []`, and
  `fieldShapesFuel` gives `[.recursive 0]`.
* The copy's reader does not (`drCtorShapesA_none`): `ctorShapesA` reads the erased stored domain without
  δ, so the constructor has no shape list and the copy's ι is stuck there (`iotaReductA` binds
  it first).
* The constructor's built type erases to `main`'s stored one (`drCtorTypeA_erase`), so the copy twin is the
  bridge's image of the group.

`drCtorShapesA_none` is the tooth: it flips when the δ-aware reader lands (R-NoDeltaRec-0's sequence, step 5).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- the copy's twin of `mk`'s stored type: `Π (x : Id F), F`. -/
def drCtorTypeA : ExprA :=
  .pi (.app (.const 0 []) (.const 1 [])) (.succ .zero) (.const 1 []) (.succ .zero)

theorem drCtorTypeA_erase : erase drCtorTypeA = drMkMember.mtype := rfl

/-- admission, at `RcicTypedDeltaRecPins`' bound: directly recursive after δ. -/
theorem drFieldAnalyze_pin :
    fieldAnalyze drFamEnv 8 1 0 0 0 0 drField = .permitted (.recursive 0) [] ∧
    fieldShapesFuel drFamEnv 8 1 0 0 0 0 [drField] = some [.recursive 0] :=
  ⟨dr_fieldAnalyze, rfl⟩

/-- THE TOOTH: the copy's shape reader gives the constructor no shapes. It flips when the δ-aware reader
    lands. -/
theorem drCtorShapesA_none : ctorShapesA 1 0 drCtorTypeA = none := by decide

theorem drCtorKindsA_none : ctorKindsA 1 0 drCtorTypeA = none := by decide

/-- the divergence in one statement: admission has shapes, the copy's reader has none, on the same type. -/
theorem drShapes_diverge :
    (∃ shapes, fieldShapesFuel drFamEnv 8 1 0 0 0 0 [drField] = some shapes) ∧
    ctorShapesA 1 0 drCtorTypeA = none :=
  ⟨⟨_, drFieldAnalyze_pin.2⟩, drCtorShapesA_none⟩

/-- R-NoDeltaRec-1: the δ-reached field of the group, as a view field: the surface domain `Id F`, no
    index. -/
def drFieldA : FieldA := .drecD (.app (.const 0 []) (.const 1 [])) []

/-- the built constructor type erases to `main`'s stored one: the surface domain is reproduced. -/
theorem drFieldA_builds :
    erase (ctorTypeA 1 [] (.succ .zero) [] [drFieldA] []) = drMkMember.mtype := rfl

theorem drFieldA_shape : drFieldA.shape = .recursive 0 := rfl

/-- THE TOOTH of the carried restriction: a view with this field is refused by `noDelta` and by
    `TreeField`; it is not function-recursive. -/
theorem drFieldA_not_noDelta :
    ¬ drFieldA.NoDelta ∧ ¬ drFieldA.TreeField ∧ drFieldA.NoFun := ⟨fun h => h, fun h => h, trivial⟩

/-- R-NoDeltaRec-2: a view carrying this field must type `Id F` in the family's scope at the family's sort
    and convert it to the family application there. The statement reads the two facts off at the empty
    prefix. -/
theorem drFieldA_typed_reads {E : ResolvedEnvA} {I : IotaIfaceA} {fm : CheckedMemberA} {fv : FamViewA fm}
    (h : DrecDTypedA E I 1 fm fv [drFieldA]) :
    Nonempty (HasTyA (extendEnvA E 1 fm) I fm.arity (telCtxA fv.params) (.app (.const 0 []) (.const 1 []))
      (.sort fv.sort)) ∧
    Nonempty (ConvA (extendEnvA E 1 fm) I fm.arity (telCtxA fv.params) (.app (.const 0 []) (.const 1 []))
      (foldAppsA (.const 1 (canonLevelsA fm.arity))
        ((paramLocalsA fv.params.length).map (liftA 0 0) ++ [])) (.sort fv.sort)) :=
  ⟨(h [] (.app (.const 0 []) (.const 1 [])) [] [] rfl).1,
    (h [] (.app (.const 0 []) (.const 1 [])) [] [] rfl).2.1⟩

/-- R-NoDeltaRec-3a: the field's normal form is the direct recursion at its indices. -/
theorem drFieldA_norm : drFieldA.norm = .drec [] := rfl

/-- the normed constructor type — `Π (x : F), F` — is what `ctorMemberA.normA` carries, and the
    copy's shape reader reads `recursive 0` on it, admission's verdict (`drFieldAnalyze_pin`),
    where the stored `Id F` gave none (`drCtorShapesA_none`). -/
theorem drCtorTypeA_norm_shapes :
    ctorShapesA 1 0 (ctorTypeA 1 [] (.succ .zero) [] [drFieldA.norm] []) = some [.recursive 0] := by
  decide

/-- R-NoDeltaRec-3c, the member-level pin: a `ctorMemberA`-built member carries BOTH types — the
    stored `Π (x : Id F), F` in `mtypeA` and the normed `Π (x : F), F` in `normA`. The erasure sees
    only the stored one (`eraseMember` drops `normA`); `hnorm`'s conditional goes through the
    SOME-direction this member actually satisfies. -/
theorem drCtorMemberA_normA :
    (ctorMemberA 0 1 (.succ .zero) [] [drFieldA] []).normA =
      some (ctorTypeA 1 [] (.succ .zero) [] [drFieldA.norm] []) ∧
    (ctorMemberA 0 1 (.succ .zero) [] [drFieldA] []).mtypeA =
      ctorTypeA 1 [] (.succ .zero) [] [drFieldA] [] := ⟨rfl, rfl⟩

/-- the member's two types diverge exactly at the δ-reached domain: erased, the stored type keeps
    `Id F` while the normed one reads `F`. -/
theorem drCtorMemberA_diverge :
    erase (ctorTypeA 1 [] (.succ .zero) [] [drFieldA] []) ≠
      erase (ctorTypeA 1 [] (.succ .zero) [] [drFieldA.norm] []) := by
  decide

#print axioms drCtorTypeA_erase
#print axioms drFieldAnalyze_pin
#print axioms drCtorShapesA_none
#print axioms drCtorKindsA_none
#print axioms drShapes_diverge
#print axioms drFieldA_builds
#print axioms drFieldA_shape
#print axioms drFieldA_not_noDelta
#print axioms drFieldA_typed_reads
#print axioms drFieldA_norm
#print axioms drCtorTypeA_norm_shapes
#print axioms drCtorMemberA_normA
#print axioms drCtorMemberA_diverge
#print axioms drecDTypedA_idxBounded

end Rcic.Declarative.Ann
