/-
L-K1 inhabitants (#6075). The admission judgment is `IndGroupAdmitted`
in `RcicIndGroupJudgment`. This file does not restate it. `EnvWf`
imports the judgment module, not this one: this one imports
`RcicFixtures`.
-/
import rcic.RcicIndGroupJudgment
import rcic.RcicFixtures

namespace Rcic.Declarative

/-! ## Decider checks against `RcicFixtures.natRecType`

Zero minor is `P zero`. Succ minor is `Π n : N, Π ih : P n, P (succ n)`,
the domain stored under the motive and the zero minor. -/

example :
    minorFromTelescope emptyEnv 2 0 (.bvar 0) (.const 1 []) [] (.const 0 []) =
      some (.app (.bvar 0) (.const 1 [])) := rfl

example :
    minorFromTelescope emptyEnv 2 0 (.bvar 1) (.const 2 []) [.recursive 0]
      (.pi (.const 0 []) (.const 0 [])) =
      some (.pi (.const 0 [])
        (.pi (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (.app (.const 2 []) (.bvar 1))))) := rfl

example :
    fieldAnalyze emptyEnv 8 0 0 0 0 0 (.const 0 []) =
      .permitted (.recursive 0) [] := rfl

example :
    fieldAnalyze emptyEnv 8 0 0 0 0 0 (.pi (.const 0 []) (.sort .zero)) =
      .refused .negativeOccurrence := rfl

example :
    fieldAnalyze emptyEnv 8 0 0 0 0 0 (.sort .zero) =
      .permitted .nonrecursive [] := rfl

example :
    exactParamLocals [.bvar 1] 1 = true := rfl

example :
    funIHType emptyEnv 3 0 (.pi (.sort .zero) (.const 0 [])) (.bvar 0) 1 =
      some (.pi (.sort .zero)
        (.app (.bvar 2) (.app (.bvar 1) (.bvar 0)))) := rfl

example :
    fieldAnalyze emptyEnv 12 0 0 0 0 0 (.pi (.sort .zero) (.const 0 [])) =
      .permitted (.recursive 1) [] := rfl

/-- Succ iota schema: `s n (N.rec P z s n)`, with `P,z,s,n` at bvars 3,2,1,0. -/
example :
    iotaOpenRhs emptyEnv 2 (.const 3 []) (.bvar 1)
      [.bvar 3, .bvar 2, .bvar 1] 0 2
      [.recursive 0] [.bvar 0]
      (.pi (.const 0 []) (.const 0 [])) =
      some (.app (.app (.bvar 1) (.bvar 0))
        (foldApps (.const 3 []) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])) := rfl

/-- Zero iota schema: no fields, rhs is the zero minor. -/
example :
    iotaOpenRhs emptyEnv 2 (.const 3 []) (.bvar 1)
      [.bvar 2, .bvar 1, .bvar 0] 0 2
      [] [] (.const 0 []) =
      some (.bvar 1) := rfl

/-! ## Nat inhabits §12 and §14

The inhabitant is the fixture `natEnvU` (`natRecMemberU`): motive
`Sort (param 0)`, recursor arity 1. That is 05 §11 AnySort.
`natRecMember` stores a fixed `Sort 1` motive at arity 0. 05 §11 does
not derive that signature, so this section does not claim it. The
member is left as the tree stores it. -/

def natGroupFamily : PolicyFamilyView natEnvPrefix where
  ref := 0
  member := natFamMember
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def natGroupZero : PolicyConstructorView natEnvPrefix natGroupFamily natZeroMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := .empty _ _
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

def natSuccFieldTy :
    HasTy natEnvPrefix 0 [] (.const 0 []) (.sort (.succ .zero)) :=
  HasTy.const [] 0 [] natFamMember rfl rfl (fun _ h => nomatch h)

def natGroupSucc : PolicyConstructorView natEnvPrefix natGroupFamily natSuccMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const 0 []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlen : ([] ++ [(Expr.const 0 [] : Expr Nat)]).length = 1 := rfl
      have hlt : j.val < 1 := by simpa [hlen] using j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simpa [hj, policyPrefixContext] using natSuccFieldTy
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

theorem natZeroUniverse : FieldUniverseAdmitted natGroupZero :=
  fun j => j.elim0

theorem natSuccUniverse : FieldUniverseAdmitted natGroupSucc := by
  intro j
  have hlen : natGroupSucc.fields.length = 1 := rfl
  have hlt : j.val < 1 := by simpa [hlen] using j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem natZeroFields : CtorFieldsPermitted natGroupZero :=
  fun j => j.elim0

theorem natSuccFields : CtorFieldsPermitted natGroupSucc := by
  intro j
  have hlen : natGroupSucc.fields.length = 1 := rfl
  have hlt : j.val < 1 := by simpa [hlen] using j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact ⟨.recursive 0, 4, [], rfl⟩

theorem natPrefixMem (c : Nat) :
    natEnvPrefix.members c =
      if c = 2 then some natSuccMember
      else if c = 1 then some natZeroMember
      else if c = 0 then some natFamMember
      else none := by
  simp [natEnvPrefix, extendEnv, emptyEnv]

theorem natNoRecursor : NoRecursorFor natEnvPrefix 0 := by
  intro rr rm hmem hk _hrf
  rw [natPrefixMem] at hmem
  by_cases h2 : rr = 2
  · simp [h2] at hmem
    cases hmem
    simp [natSuccMember] at hk
  · by_cases h1 : rr = 1
    · simp [h2, h1] at hmem
      cases hmem
      simp [natZeroMember] at hk
    · by_cases h0 : rr = 0
      · simp [h2, h1, h0] at hmem
        cases hmem
        simp [natFamMember] at hk
      · simp [h2, h1, h0] at hmem

theorem natCensus : CtorCensus natEnvPrefix 0 3 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, _⟩
    rw [natPrefixMem] at hc
    by_cases h2 : c = 2
    · rw [if_pos h2] at hc
      cases hc
      exact ⟨by omega, by omega⟩
    · by_cases h1 : c = 1
      · rw [if_neg h2, if_pos h1] at hc
        cases hc
        exact ⟨by omega, by omega⟩
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hc
          cases hc
          rw [natFamMember] at hk
          cases hk
        · rw [if_neg h2, if_neg h1, if_neg h0] at hc
          cases hc
  · intro h
    have hc : c = 1 ∨ c = 2 := by omega
    rcases hc with rfl | rfl
    · exact ⟨natZeroMember, by rw [natPrefixMem]; rfl, rfl, rfl⟩
    · exact ⟨natSuccMember, by rw [natPrefixMem]; rfl, rfl, rfl⟩

def natMinors : List (Expr Nat) :=
  [ .app (.bvar 0) (.const 1 [])
  , .pi (.const 0 [])
      (.pi (.app (.bvar 2) (.bvar 0))
        (.app (.bvar 3) (.app (.const 2 []) (.bvar 1)))) ]

def natGroupAdmitted : RecursorEliminationAdmitted natEnvPrefix 3 natRecMemberU where
  family := natGroupFamily
  constructors := [natZeroMember, natSuccMember]
  constructorViews
    | ⟨0, _⟩ => natGroupZero
    | ⟨1, _⟩ => natGroupSucc
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := natMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem natMinorMatch : MinorPremisesMatch natGroupAdmitted := by
  intro i
  have hlen : natGroupAdmitted.constructors.length = 2 := rfl
  have hlt : i.val < 2 := by simpa [hlen] using i.isLt
  have hc : i.val = 0 ∨ i.val = 1 := by omega
  rcases hc with hv | hv
  · have hi : i = ⟨0, by decide⟩ := Fin.ext hv
    rw [hi]
    exact ⟨[], 0, rfl, rfl⟩
  · have hi : i = ⟨1, by decide⟩ := Fin.ext hv
    rw [hi]
    exact ⟨[.recursive 0], 4, rfl, rfl⟩

def natP : Expr Nat := .pi (.const 0 []) (.sort (.param 0))
def natMz : Expr Nat := .app (.bvar 0) (.const 1 [])
def natMs : Expr Nat :=
  .pi (.const 0 [])
    (.pi (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const 2 []) (.bvar 1))))
def natN : Expr Nat := .const 0 []

def natZeroCtx : LCtx :=
  [.assumption natMs, .assumption natMz, .assumption natP]

def natSuccCtx : LCtx :=
  [.assumption natN, .assumption natMs, .assumption natMz, .assumption natP]

def natE3 : ResolvedEnv := extendEnv natEnvPrefix 3 natRecMemberU

def natRecHead : Expr Nat := .const 3 [.param 0]

def natRecApplied : Expr Nat :=
  foldApps natRecHead [.bvar 3, .bvar 2, .bvar 1, .bvar 0]

def natSuccRhs : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) natRecApplied

def natSuccLhs : Expr Nat :=
  .app (.bvar 3) (.app (.const 2 []) (.bvar 0))

def natZeroLhs : Expr Nat := .app (.bvar 2) (.const 1 [])

private def natApp {f a A B : Expr Nat} {Γ : LCtx}
    (hf : HasTy natE3 1 Γ f (.pi A B))
    (ha : HasTy natE3 1 Γ a A) :
    HasTy natE3 1 Γ (.app f a) (instantiate0 a B) :=
  HasTy.app Γ f a A B hf ha

def natRecConstTy :
    HasTy natE3 1 natSuccCtx natRecHead natRecTypeU :=
  HasTy.const natSuccCtx 3 [.param 0] natRecMemberU rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

def natSuccBvar (i : Nat) (A : Expr Nat)
    (h : lookupType natSuccCtx i = some A) :
    HasTy natE3 1 natSuccCtx (.bvar i) A :=
  HasTy.bvar _ i A h

def natCodP : Expr Nat :=
  .pi natMz (.pi natMs (.pi natN (.app (.bvar 3) (.bvar 0))))

def natMzAt : Expr Nat := .app (.bvar 3) (.const 1 [])

def natCodZ : Expr Nat :=
  .pi (.pi natN
        (.pi (.app (.bvar 5) (.bvar 0))
          (.app (.bvar 6) (.app (.const 2 []) (.bvar 1)))))
    (.pi natN (.app (.bvar 6) (.bvar 0)))

def natMsAt : Expr Nat :=
  .pi natN
    (.pi (.app (.bvar 4) (.bvar 0))
      (.app (.bvar 5) (.app (.const 2 []) (.bvar 1))))

def natCodS : Expr Nat := .pi natN (.app (.bvar 5) (.bvar 0))

def natCodN : Expr Nat := .app (.bvar 4) (.bvar 0)

def natPn : Expr Nat := .app (.bvar 3) (.bvar 0)

def natSnDom : Expr Nat := natPn

def natSnCod : Expr Nat :=
  .app (.bvar 4) (.app (.const 2 []) (.bvar 1))

def natSuccIotaTy : HasTy natE3 1 natSuccCtx natSuccRhs natSuccLhs := by
  have hP : HasTy natE3 1 natSuccCtx (.bvar 3) natP :=
    HasTy.bvar _ 3 natP rfl
  have hZ : HasTy natE3 1 natSuccCtx (.bvar 2) natMzAt :=
    HasTy.bvar _ 2 natMzAt rfl
  have hS : HasTy natE3 1 natSuccCtx (.bvar 1) natMsAt :=
    HasTy.bvar _ 1 natMsAt rfl
  have hN : HasTy natE3 1 natSuccCtx (.bvar 0) natN :=
    HasTy.bvar _ 0 natN rfl
  have h0 : HasTy natE3 1 natSuccCtx natRecHead (.pi natP natCodP) :=
    natRecConstTy
  have h1 := natApp h0 hP
  have h1' : HasTy natE3 1 natSuccCtx (.app natRecHead (.bvar 3)) (.pi natMzAt natCodZ) :=
    h1
  have h2 := natApp h1' hZ
  have h2' : HasTy natE3 1 natSuccCtx
      (.app (.app natRecHead (.bvar 3)) (.bvar 2)) (.pi natMsAt natCodS) :=
    h2
  have h3 := natApp h2' hS
  have h3' : HasTy natE3 1 natSuccCtx
      (.app (.app (.app natRecHead (.bvar 3)) (.bvar 2)) (.bvar 1))
      (.pi natN natCodN) :=
    h3
  have h4 := natApp h3' hN
  have h4' : HasTy natE3 1 natSuccCtx natRecApplied natPn := h4
  have hSn := natApp hS hN
  have hSn' : HasTy natE3 1 natSuccCtx (.app (.bvar 1) (.bvar 0))
      (.pi natSnDom natSnCod) :=
    hSn
  have h5 := natApp hSn' h4'
  have h5' : HasTy natE3 1 natSuccCtx natSuccRhs natSuccLhs := h5
  exact h5'

def natZeroIotaTy : HasTy natE3 1 natZeroCtx (.bvar 1) natZeroLhs :=
  HasTy.bvar natZeroCtx 1 natZeroLhs rfl

def natShapes : Fin natGroupAdmitted.constructors.length → List FieldShape
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => [.recursive 0]

def natIotaZero : IotaEquationTyped natGroupAdmitted ⟨0, by decide⟩ 4 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact natZeroIotaTy

def natIotaSucc : IotaEquationTyped natGroupAdmitted ⟨1, by decide⟩ 4 [.recursive 0] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact natSuccIotaTy

def natIotaClause : IotaDescriptorClause natEnvPrefix natGroupAdmitted where
  signatureOnly := rfl
  shapesAt := natShapes
  fuelAt := fun _ => 4
  analyzed := by
    intro i
    have hlen : natGroupAdmitted.constructors.length = 2 := rfl
    have hlt : i.val < 2 := by simpa [hlen] using i.isLt
    have hc : i.val = 0 ∨ i.val = 1 := by omega
    rcases hc with hv | hv
    · have hi : i = ⟨0, by decide⟩ := Fin.ext hv
      rw [hi]
      rfl
    · have hi : i = ⟨1, by decide⟩ := Fin.ext hv
      rw [hi]
      rfl
  typed := fun i =>
    if h0 : i.val = 0 then by
      have hi : i = ⟨0, by decide⟩ := Fin.ext h0
      simpa [hi, natShapes] using natIotaZero
    else if h1 : i.val = 1 then by
      have hi : i = ⟨1, by decide⟩ := Fin.ext h1
      simpa [hi, natShapes] using natIotaSucc
    else by
      have hlen : natGroupAdmitted.constructors.length = 2 := rfl
      have hlt : i.val < 2 := by simpa [hlen] using i.isLt
      omega

def natGroupRecursor : IndGroupAdmitted natEnvPrefix 3 natRecMemberU :=
  .recursor natGroupAdmitted rfl natCensus
    (by
      intro i
      have hlen : natGroupAdmitted.constructors.length = 2 := rfl
      have hlt : i.val < 2 := by simpa [hlen] using i.isLt
      have hc : i.val = 0 ∨ i.val = 1 := by omega
      rcases hc with hv | hv
      · have hi : i = ⟨0, by decide⟩ := Fin.ext hv
        rw [hi]
        exact natZeroUniverse
      · have hi : i = ⟨1, by decide⟩ := Fin.ext hv
        rw [hi]
        exact natSuccUniverse)
    (by
      intro i
      have hlen : natGroupAdmitted.constructors.length = 2 := rfl
      have hlt : i.val < 2 := by simpa [hlen] using i.isLt
      have hc : i.val = 0 ∨ i.val = 1 := by omega
      rcases hc with hv | hv
      · have hi : i = ⟨0, by decide⟩ := Fin.ext hv
        rw [hi]
        exact natZeroFields
      · have hi : i = ⟨1, by decide⟩ := Fin.ext hv
        rw [hi]
        exact natSuccFields)
    natMinorMatch natIotaClause

end Rcic.Declarative
