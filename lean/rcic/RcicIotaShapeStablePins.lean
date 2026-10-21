import rcic.RcicIotaShapeStable
import rcic.RcicTypedDeltaRecPins

namespace Rcic.Declarative

/-- The δ-reached field `Id F` is closed under transparent unfolding in `drEnv`. -/
theorem drField_constsMemberFuel : constsMemberFuel drEnv 9 drField = true := by
  simp [constsMemberFuel, drField, drEnv, drMkEnv, drFamEnv, drBase, extendEnv,
    drIdMember, drFamMember, transparent, instantiateLevels]

/-- Admission's classification of the δ-reached `mk` field is stable in every
extension of `drEnv`. -/
theorem drFieldAnalyze_ext_stable (E' : ResolvedEnv)
    (hext : ∀ r m, drEnv.members r = some m → E'.members r = some m) :
    fieldAnalyze E' 8 1 0 0 0 0 drField =
      fieldAnalyze drEnv 8 1 0 0 0 0 drField :=
  fieldAnalyze_ext hext drField_constsMemberFuel

/-- Negative control: the field head is not a member of the checked environment. -/
def missingHeadField : Expr Nat := .const 99 []

theorem missingHeadField_constsMemberFuel_false :
    constsMemberFuel emptyEnv 8 missingHeadField = false := by
  simp [missingHeadField, constsMemberFuel, emptyEnv]

end Rcic.Declarative
