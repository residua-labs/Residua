/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `Pos` support block
(`posMembersAt 0`, `RcicG2Objects`) — one `EnvWfT.group` step from the
empty environment.

`Pos` is the Nat fixture with a second successor: its family is
`natFamMember`, `one` is `natZeroMember`, and `bit0`/`bit1` are both
`natSuccMember`, member for member. So the family, `one` and `bit0`
admissions ARE the Nat fixture's (`natFamAdmitted`, `natZeroAdmitted`,
`natSuccAdmitted`, `RcicIndGroupFixtureWf`); `bit1` reuses its views. The
recursor is `.anySort` by `uniformType`, its stored `posRecTy 0` the
policy recursor type by `rfl`; `bit0`/`bit1` each carry one recursive
field, so their ι equations apply the minor to the field and the
recursive call (the `natSuccIotaTy` shape).
-/
import rcic.RcicG2AdmitBool

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative
open Rcic.Scm.SrcG (sortTyAtC)

/-! ## (1) the members and the prefix chain -/

def posRecMember : CheckedMember := ⟨.recursorM, 1, posRecTy 0, none⟩

theorem posMembersAt_zero :
    posMembersAt 0 =
      [(0, natFamMember), (1, natZeroMember), (2, natSuccMember), (3, natSuccMember),
        (4, posRecMember)] := rfl

/-- family, `one`, `bit0`, `bit1`. -/
def posPrefix : ResolvedEnv := extendEnv natEnvPrefix 3 natSuccMember
def posEnv : ResolvedEnv := extendEnv posPrefix 4 posRecMember

theorem posBlockEnv_eq : blockEnv emptyEnv (posMembersAt 0) = posEnv := rfl

theorem natEnvPrefix_mem (c : Nat) :
    natEnvPrefix.members c =
      if c = 2 then some natSuccMember
      else if c = 1 then some natZeroMember
      else if c = 0 then some natFamMember
      else none := rfl

theorem posPrefix_mem (c : Nat) :
    posPrefix.members c =
      if c = 3 then some natSuccMember
      else if c = 2 then some natSuccMember
      else if c = 1 then some natZeroMember
      else if c = 0 then some natFamMember
      else none := rfl

/-! ## (2) `bit1`'s admission -/

theorem bit1Before : CtorBeforeRecursors natEnvPrefix natSuccMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [natEnvPrefix_mem] at hm
  by_cases h2 : rr = 2
  · rw [if_pos h2] at hm
    cases hm
    cases hk
  · by_cases h1 : rr = 1
    · rw [if_neg h2, if_pos h1] at hm
      cases hm
      cases hk
    · by_cases h0 : rr = 0
      · rw [if_neg h2, if_neg h1, if_pos h0] at hm
        cases hm
        cases hk
      · rw [if_neg h2, if_neg h1, if_neg h0] at hm
        cases hm

theorem bit1Contig : CtorContiguous natEnvPrefix 3 natSuccMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 1 ∨ c = 2 := by omega
    rcases hc with rfl | rfl
    · exact ⟨natZeroMember, rfl, rfl, rfl⟩
    · exact ⟨natSuccMember, rfl, rfl, rfl⟩
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [natEnvPrefix_mem] at hm
    by_cases h2 : c = 2
    · subst h2
      exact ⟨by decide, by decide⟩
    · by_cases h1 : c = 1
      · subst h1
        exact ⟨by decide, by decide⟩
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hm
          cases hm
          cases hc
        · rw [if_neg h2, if_neg h1, if_neg h0] at hm
          cases hm

/-- a `natSuccMember`-shaped constructor's one field is `Pos` itself:
    recursive, `Sort 1`. -/
theorem succUniverse (E : ResolvedEnv) (h : E.members 0 = some natFamMember) :
    FieldUniverseAdmitted (natSuccView E h)
  | ⟨0, _⟩ => Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem bit1Fields : CtorFieldsPermitted (natSuccView natEnvPrefix rfl)
  | ⟨0, _⟩ => ⟨.recursive 0, 4, [], rfl⟩

theorem posSuccFields : CtorFieldsPermitted (natSuccView posPrefix rfl)
  | ⟨0, _⟩ => ⟨.recursive 0, 4, [], rfl⟩

def bit1Admitted : IndGroupAdmitted natEnvPrefix 3 natSuccMember :=
  .constructor (natFamView natEnvPrefix rfl) (natSuccView natEnvPrefix rfl)
    rfl bit1Before bit1Contig (succUniverse _ rfl) bit1Fields

/-! ## (3) the recursor admission -/

theorem posCensus : CtorCensus posPrefix 0 4 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, _⟩
    rw [posPrefix_mem] at hc
    by_cases h3 : c = 3
    · exact ⟨by omega, by omega⟩
    · by_cases h2 : c = 2
      · exact ⟨by omega, by omega⟩
      · by_cases h1 : c = 1
        · exact ⟨by omega, by omega⟩
        · by_cases h0 : c = 0
          · rw [if_neg h3, if_neg h2, if_neg h1, if_pos h0] at hc
            cases hc
            cases hk
          · rw [if_neg h3, if_neg h2, if_neg h1, if_neg h0] at hc
            cases hc
  · intro h
    have hc : c = 1 ∨ c = 2 ∨ c = 3 := by omega
    rcases hc with rfl | rfl | rfl
    · exact ⟨natZeroMember, rfl, rfl, rfl⟩
    · exact ⟨natSuccMember, rfl, rfl, rfl⟩
    · exact ⟨natSuccMember, rfl, rfl, rfl⟩

/-- `P one`; `Π p, P p → P (bit0 p)`; `Π p, P p → P (bit1 p)` — each under
    the motive and the earlier minors. -/
def posMinors : List (Expr Nat) :=
  [ .app (.bvar 0) (.const 1 []),
    .pi (.const 0 []) (.pi (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const 2 []) (.bvar 1)))),
    .pi (.const 0 []) (.pi (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4) (.app (.const 3 []) (.bvar 1)))) ]

def posGroupAdm : RecursorEliminationAdmitted posPrefix 4 posRecMember where
  family := natFamView posPrefix rfl
  constructors := [natZeroMember, natSuccMember, natSuccMember]
  constructorViews
    | ⟨0, _⟩ => natZeroView posPrefix rfl
    | ⟨1, _⟩ => natSuccView posPrefix rfl
    | ⟨2, _⟩ => natSuccView posPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  recursorRef := rfl
  minorTypes := posMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem posMinorMatch : MinorPremisesMatch posGroupAdm
  | ⟨0, _⟩ => ⟨[], 0, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[.recursive 0], 4, rfl, rfl⟩
  | ⟨2, _⟩ => ⟨[.recursive 0], 4, rfl, rfl⟩

/-! ## (4) the ι equations -/

def posMotTy : Expr Nat := .pi (.const 0 []) (.sort (.param 0))

/-- `[m1', m0, m1, P]` — `one`'s equation context (no field). -/
def posCtx0 : LCtx :=
  [.assumption (posMinors[2]'(by decide)), .assumption (posMinors[1]'(by decide)),
    .assumption (posMinors[0]'(by decide)), .assumption posMotTy]

/-- `[p, m1', m0, m1, P]` — `bit0`'s and `bit1`'s (one field `p : Pos`). -/
def posCtx1 : LCtx := .assumption (.const 0 []) :: posCtx0

/-- `Pos.rec P m1 m0 m1' p` in `posCtx1`. -/
def posRecApplied : Expr Nat :=
  foldApps (.const 4 [.param 0]) [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0]

def posRecHeadTy : HasTy posEnv 1 posCtx1 (.const 4 [.param 0]) (posRecTy 0) :=
  HasTy.const posCtx1 4 [.param 0] posRecMember rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

def posRecAppliedTy : HasTy posEnv 1 posCtx1 posRecApplied (.app (.bvar 4) (.bvar 0)) :=
  HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _
        (HasTy.app _ _ _ _ _
          (HasTy.app _ _ _ _ _ posRecHeadTy (HasTy.bvar _ 4 _ rfl))
          (HasTy.bvar _ 3 _ rfl))
        (HasTy.bvar _ 2 _ rfl))
      (HasTy.bvar _ 1 _ rfl))
    (HasTy.bvar _ 0 _ rfl)

/-- `rec P m1 m0 m1' one ⇝ m1`. -/
def posOneIotaTy : HasTy posEnv 1 posCtx0 (.bvar 2) (.app (.bvar 3) (.const 1 [])) :=
  HasTy.bvar _ 2 _ rfl

/-- `rec P m1 m0 m1' (bit0 p) ⇝ m0 p (rec P m1 m0 m1' p)`. -/
def posBit0IotaTy :
    HasTy posEnv 1 posCtx1 (.app (.app (.bvar 2) (.bvar 0)) posRecApplied)
      (.app (.bvar 4) (.app (.const 2 []) (.bvar 0))) :=
  HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ (HasTy.bvar posCtx1 2 _ rfl) (HasTy.bvar posCtx1 0 _ rfl))
    posRecAppliedTy

/-- `rec P m1 m0 m1' (bit1 p) ⇝ m1' p (rec P m1 m0 m1' p)`. -/
def posBit1IotaTy :
    HasTy posEnv 1 posCtx1 (.app (.app (.bvar 1) (.bvar 0)) posRecApplied)
      (.app (.bvar 4) (.app (.const 3 []) (.bvar 0))) :=
  HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ (HasTy.bvar posCtx1 1 _ rfl) (HasTy.bvar posCtx1 0 _ rfl))
    posRecAppliedTy

def posIotaOne : IotaEquationTyped posGroupAdm ⟨0, by decide⟩ 4 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact posOneIotaTy

def posIotaBit0 : IotaEquationTyped posGroupAdm ⟨1, by decide⟩ 4 [.recursive 0] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact posBit0IotaTy

def posIotaBit1 : IotaEquationTyped posGroupAdm ⟨2, by decide⟩ 4 [.recursive 0] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact posBit1IotaTy

def posShapes : Fin posGroupAdm.constructors.length → List FieldShape
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => [.recursive 0]
  | ⟨2, _⟩ => [.recursive 0]

def posIotaClause : IotaDescriptorClause posPrefix posGroupAdm where
  signatureOnly := rfl
  shapesAt := posShapes
  fuelAt := fun _ => 4
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  typed
    | ⟨0, _⟩ => posIotaOne
    | ⟨1, _⟩ => posIotaBit0
    | ⟨2, _⟩ => posIotaBit1

def posRecAdmitted : IndGroupAdmitted posPrefix 4 posRecMember :=
  .recursor posGroupAdm rfl posCensus
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => succUniverse _ rfl
         | ⟨2, _⟩ => succUniverse _ rfl)
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => posSuccFields | ⟨2, _⟩ => posSuccFields)
    posMinorMatch posIotaClause

/-! ## (5) checker leaves, the chain, and the group step -/

kernel_rfl_theorem posSortB0 :
    (sortTyAtC emptyEnv 0 96 [] natFamMember.mtype).isSome = true

kernel_rfl_theorem posSortB1 :
    (sortTyAtC natFamOnly 0 96 [] natZeroMember.mtype).isSome = true

kernel_rfl_theorem posSortB2 :
    (sortTyAtC natFamZero 0 96 [] natSuccMember.mtype).isSome = true

kernel_rfl_theorem posSortB3 :
    (sortTyAtC natEnvPrefix 0 96 [] natSuccMember.mtype).isSome = true

kernel_rfl_theorem posSortB4 :
    (sortTyAtC posPrefix 1 96 [] posRecMember.mtype).isSome = true

kernel_rfl_theorem posAccB0 :
    memberAcceptB natFamOnly emptyEnv 96 natFamAdmitted
      ((sortTyAtC emptyEnv 0 96 [] natFamMember.mtype).get posSortB0).1 = true

kernel_rfl_theorem posAccB1 :
    memberAcceptB natFamOnly natFamOnly 96 natZeroAdmitted
      ((sortTyAtC natFamOnly 0 96 [] natZeroMember.mtype).get posSortB1).1 = true

kernel_rfl_theorem posAccB2 :
    memberAcceptB natFamOnly natFamZero 96 natSuccAdmitted
      ((sortTyAtC natFamZero 0 96 [] natSuccMember.mtype).get posSortB2).1 = true

kernel_rfl_theorem posAccB3 :
    memberAcceptB natFamOnly natEnvPrefix 96 bit1Admitted
      ((sortTyAtC natEnvPrefix 0 96 [] natSuccMember.mtype).get posSortB3).1 = true

kernel_rfl_theorem posAccB4 :
    memberAcceptB natFamOnly posPrefix 96 posRecAdmitted
      ((sortTyAtC posPrefix 1 96 [] posRecMember.mtype).get posSortB4).1 = true

def posGroupChain :
    GroupAcceptChain natFamOnly 96 emptyEnv
      [(0, natFamMember), (1, natZeroMember), (2, natSuccMember), (3, natSuccMember),
        (4, posRecMember)] posEnv :=
  .cons emptyEnv 0 natFamMember _ _ natFamAdmitted posSortB0 posAccB0
    (.cons natFamOnly 1 natZeroMember _ _ natZeroAdmitted posSortB1 posAccB1
      (.cons natFamZero 2 natSuccMember _ _ natSuccAdmitted posSortB2 posAccB2
        (.cons natEnvPrefix 3 natSuccMember _ _ bit1Admitted posSortB3 posAccB3
          (.cons posPrefix 4 posRecMember _ _ posRecAdmitted posSortB4 posAccB4
            (.nil posEnv)))))

kernel_rfl_theorem posClassB :
    groupClassB natFamMember [(1, natZeroMember), (2, natSuccMember), (3, natSuccMember)]
      posRecMember = true

/-- `Pos`'s block admits: one `EnvWfT.group` step from the empty env. -/
def posBlockWfT : EnvWfT (blockEnv emptyEnv (posMembersAt 0)) :=
  EG010T_group_accepted .empty 96 posClassB posGroupChain

end Rcic.G2
