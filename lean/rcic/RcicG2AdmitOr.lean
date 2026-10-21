/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `Or` support block
(`orMembersAt 0`, `RcicG2Objects`) — one `EnvWfT.group` step from the
empty environment.

`Or`'s family member is `andFamMember` (`Prop → Prop → Prop`), so the
family view and family admission are `And`'s (`RcicTypedGroupPins`).
`inl`/`inr` each take the two parameters and one proof field. Two
constructors in `Prop` select `EliminationSelection.multipleProp`, so the
policy is `.propOnly`: recursor arity 0 and a `Sort 0` motive. The stored
`orRecTy 0` is the policy recursor type by `rfl`. Typed content and the
`hT` slots are paid by checker leaves (`GroupAcceptChain`, as
`RcicG2AdmitBool`).
-/
import rcic.RcicG2AdmitBool

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative
open Rcic.Scm.SrcG (sortTyAtC)

/-! ## (1) the members and the prefix chain -/

def orInlMember : CheckedMember := ⟨.constructorM, 0, orInlTy 0, none⟩
def orInrMember : CheckedMember := ⟨.constructorM, 0, orInrTy 0, none⟩
def orRecMember : CheckedMember := ⟨.recursorM, 0, orRecTy 0, none⟩

theorem orMembersAt_zero :
    orMembersAt 0 =
      [(0, andFamMember), (1, orInlMember), (2, orInrMember), (3, orRecMember)] := rfl

/-- family, `inl`. -/
def orInlEnv : ResolvedEnv := extendEnv andFamOnly 1 orInlMember
/-- family, `inl`, `inr`. -/
def orPrefix : ResolvedEnv := extendEnv orInlEnv 2 orInrMember
def orEnv : ResolvedEnv := extendEnv orPrefix 3 orRecMember

theorem orBlockEnv_eq : blockEnv emptyEnv (orMembersAt 0) = orEnv := rfl

theorem orInlEnv_mem (c : Nat) :
    orInlEnv.members c =
      if c = 1 then some orInlMember
      else if c = 0 then some andFamMember
      else none := rfl

theorem orPrefix_mem (c : Nat) :
    orPrefix.members c =
      if c = 2 then some orInrMember
      else if c = 1 then some orInlMember
      else if c = 0 then some andFamMember
      else none := rfl

/-! ## (2) the constructor views and admissions -/

/-- `inl`'s view: parameters `A B : Prop`, one field `A`, no result index. -/
def orInlView (E : ResolvedEnv) (h : E.members 0 = some andFamMember) :
    PolicyConstructorView E (andFamilyView E h) orInlMember where
  hasClass := rfl
  arity := rfl
  parameters := [.sort .zero, .sort .zero]
  fields := [.bvar 1]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j =>
      match j with
      | ⟨0, _⟩ => .succ .zero
      | ⟨1, _⟩ => .succ .zero
      | ⟨2, _⟩ => .zero
    bounded := fun j =>
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
    hasType := fun j =>
      match j with
      | ⟨0, _⟩ => HasTy.sort _ .zero
      | ⟨1, _⟩ => HasTy.sort _ .zero
      | ⟨2, _⟩ => HasTy.bvar _ 1 (.sort .zero) rfl }
  parameterMirrors := fun i =>
    match i with
    | ⟨0, _⟩ => Conv.refl _ _
    | ⟨1, _⟩ => Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

/-- `inr`'s view: parameters `A B : Prop`, one field `B`, no result index. -/
def orInrView (E : ResolvedEnv) (h : E.members 0 = some andFamMember) :
    PolicyConstructorView E (andFamilyView E h) orInrMember where
  hasClass := rfl
  arity := rfl
  parameters := [.sort .zero, .sort .zero]
  fields := [.bvar 0]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j =>
      match j with
      | ⟨0, _⟩ => .succ .zero
      | ⟨1, _⟩ => .succ .zero
      | ⟨2, _⟩ => .zero
    bounded := fun j =>
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
    hasType := fun j =>
      match j with
      | ⟨0, _⟩ => HasTy.sort _ .zero
      | ⟨1, _⟩ => HasTy.sort _ .zero
      | ⟨2, _⟩ => HasTy.bvar _ 0 (.sort .zero) rfl }
  parameterMirrors := fun i =>
    match i with
    | ⟨0, _⟩ => Conv.refl _ _
    | ⟨1, _⟩ => Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

theorem orInlFields (E : ResolvedEnv) (h : E.members 0 = some andFamMember) :
    CtorFieldsPermitted (orInlView E h)
  | ⟨0, _⟩ => ⟨.nonrecursive, 8, [], rfl⟩

theorem orInrFields (E : ResolvedEnv) (h : E.members 0 = some andFamMember) :
    CtorFieldsPermitted (orInrView E h)
  | ⟨0, _⟩ => ⟨.nonrecursive, 8, [], rfl⟩

def orInlAdmitted : IndGroupAdmitted andFamOnly 1 orInlMember :=
  .constructor (andFamilyView andFamOnly rfl) (orInlView andFamOnly rfl)
    rfl (ctorBefore_famOnly rfl rfl) (ctorContig_famOnly rfl rfl)
    (fun _ => Or.inl falseSort_prop) (orInlFields _ rfl)

theorem orInrBefore : CtorBeforeRecursors orInlEnv orInrMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [orInlEnv_mem] at hm
  by_cases h1 : rr = 1
  · rw [if_pos h1] at hm
    cases hm
    cases hk
  · by_cases h0 : rr = 0
    · rw [if_neg h1, if_pos h0] at hm
      cases hm
      cases hk
    · rw [if_neg h1, if_neg h0] at hm
      cases hm

theorem orInrContig : CtorContiguous orInlEnv 2 orInrMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 1 := by omega
    subst hc
    exact ⟨orInlMember, rfl, rfl, rfl⟩
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [orInlEnv_mem] at hm
    by_cases h1 : c = 1
    · subst h1
      exact ⟨by decide, by decide⟩
    · by_cases h0 : c = 0
      · rw [if_neg h1, if_pos h0] at hm
        cases hm
        cases hc
      · rw [if_neg h1, if_neg h0] at hm
        cases hm

def orInrAdmitted : IndGroupAdmitted orInlEnv 2 orInrMember :=
  .constructor (andFamilyView orInlEnv rfl) (orInrView orInlEnv rfl)
    rfl orInrBefore orInrContig (fun _ => Or.inl falseSort_prop) (orInrFields _ rfl)

/-! ## (3) the recursor admission -/

theorem orCensus : CtorCensus orPrefix 0 3 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, _⟩
    rw [orPrefix_mem] at hc
    by_cases h2 : c = 2
    · rw [if_pos h2] at hc
      exact ⟨by omega, by omega⟩
    · by_cases h1 : c = 1
      · rw [if_neg h2, if_pos h1] at hc
        exact ⟨by omega, by omega⟩
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hc
          cases hc
          cases hk
        · rw [if_neg h2, if_neg h1, if_neg h0] at hc
          cases hc
  · intro h
    have hc : c = 1 ∨ c = 2 := by omega
    rcases hc with rfl | rfl
    · exact ⟨orInlMember, rfl, rfl, rfl⟩
    · exact ⟨orInrMember, rfl, rfl, rfl⟩

/-- `Π (a : A), P (inl A B a)` under `[P, B, A]`; `Π (b : B), P (inr A B b)`
    under `[ml, P, B, A]`. -/
def orMinors : List (Expr Nat) :=
  [ .pi (.bvar 2) (.app (.bvar 1) (appsp 1 [.bvar 3, .bvar 2, .bvar 0])),
    .pi (.bvar 2) (.app (.bvar 2) (appsp 2 [.bvar 4, .bvar 3, .bvar 0])) ]

def orGroupAdm : RecursorEliminationAdmitted orPrefix 3 orRecMember where
  family := andFamilyView orPrefix rfl
  constructors := [orInlMember, orInrMember]
  constructorViews
    | ⟨0, _⟩ => orInlView orPrefix rfl
    | ⟨1, _⟩ => orInrView orPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := orMinors
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp falseSort_prop (by decide)
  recursorArity := rfl
  recursorType := rfl

theorem orMinorMatch : MinorPremisesMatch orGroupAdm
  | ⟨0, _⟩ => ⟨[.nonrecursive], 8, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[.nonrecursive], 8, rfl, rfl⟩

/-- the ι contexts: `[a, mr, ml, P, B, A]` and `[b, mr, ml, P, B, A]`. -/
def orIotaCtx (fieldTy : Expr Nat) : LCtx :=
  [.assumption fieldTy, .assumption (orMinors[1]'(by decide)),
    .assumption (orMinors[0]'(by decide)),
    .assumption (.pi (orApp 0 (.bvar 1) (.bvar 0)) (.sort .zero)),
    .assumption (.sort .zero), .assumption (.sort .zero)]

def orInlIotaTy :
    HasTy orEnv 0 (orIotaCtx (.bvar 4)) (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (appsp 1 [.bvar 5, .bvar 4, .bvar 0])) :=
  HasTy.app _ (.bvar 2) (.bvar 0) (.bvar 5)
    (.app (.bvar 4) (appsp 1 [.bvar 6, .bvar 5, .bvar 0]))
    (HasTy.bvar _ 2 _ rfl) (HasTy.bvar _ 0 _ rfl)

def orInrIotaTy :
    HasTy orEnv 0 (orIotaCtx (.bvar 3)) (.app (.bvar 1) (.bvar 0))
      (.app (.bvar 3) (appsp 2 [.bvar 5, .bvar 4, .bvar 0])) :=
  HasTy.app _ (.bvar 1) (.bvar 0) (.bvar 4)
    (.app (.bvar 4) (appsp 2 [.bvar 6, .bvar 5, .bvar 0]))
    (HasTy.bvar _ 1 _ rfl) (HasTy.bvar _ 0 _ rfl)

/-- `rec A B P ml mr (inl A B a) ⇝ ml a`. -/
def orIotaInl : IotaEquationTyped orGroupAdm ⟨0, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact orInlIotaTy

/-- `rec A B P ml mr (inr A B b) ⇝ mr b`. -/
def orIotaInr : IotaEquationTyped orGroupAdm ⟨1, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact orInrIotaTy

def orIotaClause : IotaDescriptorClause orPrefix orGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => orIotaInl
    | ⟨1, _⟩ => orIotaInr

def orRecAdmitted : IndGroupAdmitted orPrefix 3 orRecMember :=
  .recursor orGroupAdm rfl orCensus
    (fun | ⟨0, _⟩ => fun _ => Or.inl falseSort_prop | ⟨1, _⟩ => fun _ => Or.inl falseSort_prop)
    (fun | ⟨0, _⟩ => orInlFields _ rfl | ⟨1, _⟩ => orInrFields _ rfl)
    orMinorMatch orIotaClause

/-! ## (4) checker leaves, the chain, and the group step -/

kernel_rfl_theorem orSortB0 :
    (sortTyAtC emptyEnv 0 96 [] andFamMember.mtype).isSome = true

kernel_rfl_theorem orSortB1 :
    (sortTyAtC andFamOnly 0 96 [] orInlMember.mtype).isSome = true

kernel_rfl_theorem orSortB2 :
    (sortTyAtC orInlEnv 0 96 [] orInrMember.mtype).isSome = true

kernel_rfl_theorem orSortB3 :
    (sortTyAtC orPrefix 0 96 [] orRecMember.mtype).isSome = true

kernel_rfl_theorem orAccB0 :
    memberAcceptB andFamOnly emptyEnv 96 andFamAdmitted
      ((sortTyAtC emptyEnv 0 96 [] andFamMember.mtype).get orSortB0).1 = true

kernel_rfl_theorem orAccB1 :
    memberAcceptB andFamOnly andFamOnly 96 orInlAdmitted
      ((sortTyAtC andFamOnly 0 96 [] orInlMember.mtype).get orSortB1).1 = true

kernel_rfl_theorem orAccB2 :
    memberAcceptB andFamOnly orInlEnv 96 orInrAdmitted
      ((sortTyAtC orInlEnv 0 96 [] orInrMember.mtype).get orSortB2).1 = true

kernel_rfl_theorem orAccB3 :
    memberAcceptB andFamOnly orPrefix 96 orRecAdmitted
      ((sortTyAtC orPrefix 0 96 [] orRecMember.mtype).get orSortB3).1 = true

def orGroupChain :
    GroupAcceptChain andFamOnly 96 emptyEnv
      [(0, andFamMember), (1, orInlMember), (2, orInrMember), (3, orRecMember)] orEnv :=
  .cons emptyEnv 0 andFamMember _ _ andFamAdmitted orSortB0 orAccB0
    (.cons andFamOnly 1 orInlMember _ _ orInlAdmitted orSortB1 orAccB1
      (.cons orInlEnv 2 orInrMember _ _ orInrAdmitted orSortB2 orAccB2
        (.cons orPrefix 3 orRecMember _ _ orRecAdmitted orSortB3 orAccB3
          (.nil orEnv))))

kernel_rfl_theorem orClassB :
    groupClassB andFamMember [(1, orInlMember), (2, orInrMember)] orRecMember = true

/-- `Or`'s block admits: one `EnvWfT.group` step from the empty env. -/
def orBlockWfT : EnvWfT (blockEnv emptyEnv (orMembersAt 0)) :=
  EG010T_group_accepted .empty 96 orClassB orGroupChain

end Rcic.G2
