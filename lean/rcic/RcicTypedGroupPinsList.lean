import rcic.RcicTypedGroupPins
import rcic.RcicIndGroupExclusions

/-!
# M3-e-4 — `List.{u}` as a second group of the typed environment judgment, in the copy's scope

`RcicTypedGroupPins` admits Nat, `True` and `False`: groups with no parameter. This file admits L-K1's
universe-polymorphic `List.{u} : Sort u → Sort (succ u)` (`PosList`'s raised family and L-K1's fixture
constructors and AnySort recursor at `8`–`11`) as a SECOND `EnvWfT` group, after Nat's (`natEnvUWfT`):

(1) the environments, each group member's scope: the family over Nat (HeaderScope), `nil` with the
    family alone and `cons` after it (ConstructorScope is the family alone, M3-e-3), the recursor with
    both (DerivationScope);
(2) L-K1's views and checks at those scopes, written once over any environment holding the family (the
    `PosList` views at `listPrefix` are this file's at one environment);
(3) the stored types typed in the typed judgment, and the views' typed content;
(4) the group step: `listEnvUWfT : EnvWfT listEnvUT`, Nat then List;
(5) the copy's structured views. The constructor and recursor types BUILT from them are L-K1's stored
    types, by `rfl`: the builders (`RcicTypedGroup`) and L-K1's derivation were written separately, and a
    parameter, its mirror, a plain field, a directly recursive field and the AnySort motive's level are
    where they could have disagreed;
(6) the group in the copy's scope (`listEnvUWfT_inScope`), and the bridge at the two-group environment,
    conditional on arc D's two typings like the bridge (`listEnvU_annotated`).
-/

namespace Rcic.Declarative

open PosList

/-! ## (1) the environments -/

/-- the family over Nat: `nil`'s and `cons`'s ConstructorScope. -/
def listFamOnlyU : ResolvedEnv := extendEnv natEnvU 8 raisedFam
/-- the group built before `cons`. -/
def listFamNilU : ResolvedEnv := extendEnv listFamOnlyU 9 listUNilMember
/-- the family and both constructors: the recursor's DerivationScope. -/
def listPrefixU : ResolvedEnv := extendEnv listFamNilU 10 listUConsMember
/-- Nat, then List with its recursor. -/
def listEnvUT : ResolvedEnv := extendEnv listPrefixU 11 listURecMember

theorem listPrefixU_mem (c : Nat) :
    listPrefixU.members c =
      if c = 10 then some listUConsMember
      else if c = 9 then some listUNilMember
      else if c = 8 then some raisedFam
      else if c = 3 then some natRecMemberU
      else natEnvPrefix.members c := rfl

theorem listFamNilU_mem (c : Nat) :
    listFamNilU.members c =
      if c = 9 then some listUNilMember
      else if c = 8 then some raisedFam
      else if c = 3 then some natRecMemberU
      else natEnvPrefix.members c := rfl

theorem listFamOnlyU_mem (c : Nat) :
    listFamOnlyU.members c =
      if c = 8 then some raisedFam
      else if c = 3 then some natRecMemberU
      else natEnvPrefix.members c := rfl

/-! ## (2) L-K1's views and checks at each member's scope -/

section Views
variable (E : ResolvedEnv) (h8 : E.members 8 = some raisedFam)

/-- `PosList.family` at any environment holding the family. -/
def listFamViewE : PolicyFamilyView E where
  ref := 8
  member := raisedFam
  present := h8
  hasClass := rfl
  parameters := [paramSort]
  indices := []
  resultLevel := .succ (.param 0)
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.param 0)
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp only [hj, policyPrefixContext]
      exact HasTy.sort (n := 1) [] (.param 0)
  }

/-- `PosList.nilView` at any environment holding the family. -/
def listNilViewE : PolicyConstructorView E (listFamViewE E h8) listUNilMember where
  hasClass := rfl
  arity := rfl
  parameters := [paramSort]
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.param 0)
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp only [hj, policyPrefixContext]
      exact HasTy.sort (n := 1) [] (.param 0)
  }
  parameterMirrors := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    simp only [hi, policyPrefixContext]
    exact Conv.refl _ _
  noFamilyInIndices := fun _ h => nomatch h

/-- the family constant, `List.{u} : Sort u → Sort (succ u)`, wherever it is present. -/
def listFamTyE (Γ : LCtx) : HasTy E 1 Γ (.const 8 [.param 0]) raisedType :=
  HasTy.const (n := 1) Γ 8 [.param 0] raisedFam h8 rfl (by
    intro l hl
    have hl' : l = .param 0 := by
      simp only [List.mem_singleton] at hl
      exact hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

/-- `PosList.consView` at any environment holding the family. -/
def listConsViewE : PolicyConstructorView E (listFamViewE E h8) listUConsMember where
  hasClass := rfl
  arity := rfl
  parameters := [paramSort]
  fields := [hdField, tlField]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j =>
      match j with
      | ⟨0, _⟩ => .succ (.param 0)
      | ⟨1, _⟩ => .param 0
      | ⟨2, _⟩ => .succ (.param 0)
    bounded := fun j => by
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
    hasType := fun j => by
      match j with
      | ⟨0, _⟩ =>
          simp only [policyPrefixContext]
          exact HasTy.sort (n := 1) [] (.param 0)
      | ⟨1, _⟩ =>
          simp only [policyPrefixContext]
          exact HasTy.bvar (n := 1) consCtx0 0 (.sort (.param 0)) rfl
      | ⟨2, _⟩ =>
          simp only [policyPrefixContext]
          exact HasTy.app (n := 1) consCtx1 (.const 8 [.param 0]) (.bvar 1)
            paramSort (.sort (.succ (.param 0))) (listFamTyE E h8 consCtx1)
            (HasTy.bvar (n := 1) consCtx1 1 paramSort rfl)
  }
  parameterMirrors := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    simp only [hi, policyPrefixContext]
    exact Conv.refl _ _
  noFamilyInIndices := fun _ h => nomatch h

end Views

/-- no member of `natEnvPrefix` belongs to family `8`, and its constructors are Nat's. -/
theorem natPrefix_notList (c : Nat) (cm : CheckedMember) (hc : natEnvPrefix.members c = some cm)
    (hk : cm.mclass = .constructorM) : memberFamRef cm ≠ some 8 := by
  rw [natPrefixMem] at hc
  by_cases h2 : c = 2
  · rw [if_pos h2] at hc
    cases hc
    rw [natSuccFamily]
    decide
  · by_cases h1 : c = 1
    · rw [if_neg h2, if_pos h1] at hc
      cases hc
      rw [natZeroFamily]
      decide
    · by_cases h0 : c = 0
      · rw [if_neg h2, if_neg h1, if_pos h0] at hc
        cases hc
        cases hk
      · rw [if_neg h2, if_neg h1, if_neg h0] at hc
        cases hc

/-- Nat's members are no recursor of family `8`: Nat's own is the one at `3`. -/
theorem natU_noListRecursor (c : Nat) (rm : CheckedMember)
    (hc : (if c = 3 then some natRecMemberU else natEnvPrefix.members c) = some rm)
    (hk : rm.mclass = .recursorM) : memberFamRef rm ≠ some 8 := by
  by_cases h3 : c = 3
  · rw [if_pos h3] at hc
    cases hc
    decide
  · rw [if_neg h3, natPrefixMem] at hc
    by_cases h2 : c = 2
    · rw [if_pos h2] at hc
      cases hc
      cases hk
    · by_cases h1 : c = 1
      · rw [if_neg h2, if_pos h1] at hc
        cases hc
        cases hk
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hc
          cases hc
          cases hk
        · rw [if_neg h2, if_neg h1, if_neg h0] at hc
          cases hc

theorem listNilBeforeU : CtorBeforeRecursors listFamOnlyU listUNilMember := by
  refine ⟨8, nilFamily, ?_⟩
  intro rr rm hm hk
  rw [listFamOnlyU_mem] at hm
  by_cases h8 : rr = 8
  · rw [if_pos h8] at hm
    cases hm
    cases hk
  · rw [if_neg h8] at hm
    exact natU_noListRecursor rr rm hm hk

theorem listConsBeforeU : CtorBeforeRecursors listFamNilU listUConsMember := by
  refine ⟨8, consFamily, ?_⟩
  intro rr rm hm hk
  rw [listFamNilU_mem] at hm
  by_cases h9 : rr = 9
  · rw [if_pos h9] at hm
    cases hm
    cases hk
  · rw [if_neg h9] at hm
    by_cases h8 : rr = 8
    · rw [if_pos h8] at hm
      cases hm
      cases hk
    · rw [if_neg h8] at hm
      exact natU_noListRecursor rr rm hm hk

theorem listNilContigU : CtorContiguous listFamOnlyU 9 listUNilMember := by
  refine ⟨8, nilFamily, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd (Nat.lt_of_lt_of_le hl (Nat.le_of_lt_succ hr)) (Nat.lt_irrefl 8)
  · intro c ⟨cm, hm, hk, hf⟩
    rw [listFamOnlyU_mem] at hm
    by_cases h8 : c = 8
    · rw [if_pos h8] at hm
      cases hm
      cases hk
    · rw [if_neg h8] at hm
      by_cases h3 : c = 3
      · rw [if_pos h3] at hm
        cases hm
        cases hk
      · rw [if_neg h3] at hm
        exact absurd hf (natPrefix_notList c cm hm hk)

theorem listConsContigU : CtorContiguous listFamNilU 10 listUConsMember := by
  refine ⟨8, consFamily, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 9 := by omega
    subst hc
    exact ⟨listUNilMember, rfl, rfl, nilFamily⟩
  · intro c ⟨cm, hm, hk, hf⟩
    rw [listFamNilU_mem] at hm
    by_cases h9 : c = 9
    · exact ⟨by omega, by omega⟩
    · rw [if_neg h9] at hm
      by_cases h8 : c = 8
      · rw [if_pos h8] at hm
        cases hm
        cases hk
      · rw [if_neg h8] at hm
        by_cases h3 : c = 3
        · rw [if_pos h3] at hm
          cases hm
          cases hk
        · rw [if_neg h3] at hm
          exact absurd hf (natPrefix_notList c cm hm hk)

theorem listConsUniverseU (E : ResolvedEnv) (h8 : E.members 8 = some raisedFam) :
    FieldUniverseAdmitted (listConsViewE E h8) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr ⟨uniformType_succ_param 0, leN_param_succ 0⟩
  | ⟨1, _⟩ => exact Or.inr ⟨uniformType_succ_param 0, leN_refl _⟩

theorem listConsFieldsU : CtorFieldsPermitted (listConsViewE listFamNilU rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 8, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.recursive 0, 8, [], rfl⟩

def listFamAdmittedU : IndGroupAdmitted natEnvU 8 raisedFam :=
  .family rfl (listFamViewE listFamOnlyU rfl) rfl rfl (Or.inr (uniformType_succ_param 0))

def listNilAdmittedU : IndGroupAdmitted listFamOnlyU 9 listUNilMember :=
  .constructor (listFamViewE listFamOnlyU rfl) (listNilViewE listFamOnlyU rfl)
    rfl listNilBeforeU listNilContigU (fun j => j.elim0) (fun j => j.elim0)

def listConsAdmittedU : IndGroupAdmitted listFamNilU 10 listUConsMember :=
  .constructor (listFamViewE listFamNilU rfl) (listConsViewE listFamNilU rfl)
    rfl listConsBeforeU listConsContigU (listConsUniverseU _ rfl) listConsFieldsU

/-- L-K1's recursor admission, `PosList.group` at the Nat-rooted prefix. -/
def listGroupU : RecursorEliminationAdmitted listPrefixU 11 listURecMember where
  family := listFamViewE listPrefixU rfl
  constructors := [listUNilMember, listUConsMember]
  constructorViews
    | ⟨0, _⟩ => listNilViewE listPrefixU rfl
    | ⟨1, _⟩ => listConsViewE listPrefixU rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [minorNil, minorCons]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType (uniformType_succ_param 0)
  recursorArity := rfl
  recursorType := rfl

theorem listCensusU : CtorCensus listPrefixU 8 11 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, hf⟩
    rw [listPrefixU_mem] at hc
    by_cases h10 : c = 10
    · exact ⟨by omega, by omega⟩
    · by_cases h9 : c = 9
      · exact ⟨by omega, by omega⟩
      · rw [if_neg h10, if_neg h9] at hc
        by_cases h8 : c = 8
        · rw [if_pos h8] at hc
          cases hc
          cases hk
        · rw [if_neg h8] at hc
          by_cases h3 : c = 3
          · rw [if_pos h3] at hc
            cases hc
            cases hk
          · rw [if_neg h3] at hc
            exact absurd hf (natPrefix_notList c cm hc hk)
  · intro h
    have hc : c = 9 ∨ c = 10 := by omega
    rcases hc with rfl | rfl
    · exact ⟨listUNilMember, rfl, rfl, nilFamily⟩
    · exact ⟨listUConsMember, rfl, rfl, consFamily⟩

theorem listMinorMatchU : MinorPremisesMatch listGroupU := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[], 0, rfl, rfl⟩
  | ⟨1, _⟩ => exact ⟨[.nonrecursive, .recursive 0], 8, rfl, rfl⟩

/-- the ι equations at `nil` and `cons`, typed with the recursor present (`PosList`'s, here). -/
private def happU {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTy listEnvUT 2 Γ f (.pi A B)) (ha : HasTy listEnvUT 2 Γ a A) :
    HasTy listEnvUT 2 Γ (.app f a) (instantiate0 a B) :=
  HasTy.app (n := 2) Γ f a A B hf ha

def listNilIotaTyU : HasTy listEnvUT 2 nilCtx (.bvar 1) nilLhs :=
  HasTy.bvar (n := 2) nilCtx 1 nilLhs rfl

def listConsIotaTyU : HasTy listEnvUT 2 consCtx consRhs consLhs := by
  have hmc : HasTy listEnvUT 2 consCtx (.bvar 2) (lift 0 3 domMc) :=
    HasTy.bvar (n := 2) consCtx 2 _ rfl
  have hhd : HasTy listEnvUT 2 consCtx (.bvar 1) (lift 0 2 domHd) :=
    HasTy.bvar (n := 2) consCtx 1 _ rfl
  have htl : HasTy listEnvUT 2 consCtx (.bvar 0) (lift 0 1 domTl) :=
    HasTy.bvar (n := 2) consCtx 0 _ rfl
  have h1 := happU hmc hhd
  have h2 := happU h1 htl
  have hA : HasTy listEnvUT 2 consCtx (.bvar 5) (lift 0 6 domA) :=
    HasTy.bvar (n := 2) consCtx 5 _ rfl
  have hP : HasTy listEnvUT 2 consCtx (.bvar 4) (lift 0 5 domP) :=
    HasTy.bvar (n := 2) consCtx 4 _ rfl
  have hMn : HasTy listEnvUT 2 consCtx (.bvar 3) (lift 0 4 domMn) :=
    HasTy.bvar (n := 2) consCtx 3 _ rfl
  have hMc : HasTy listEnvUT 2 consCtx (.bvar 2) (lift 0 3 domMc) :=
    HasTy.bvar (n := 2) consCtx 2 _ rfl
  have hRec0 : HasTy listEnvUT 2 consCtx recHead
      (instantiateLevels [.param 0, .param 1] listURecType) :=
    HasTy.const (n := 2) consCtx 11 [.param 0, .param 1] listURecMember
      rfl rfl (by
        intro l hl
        simp only [List.mem_cons, List.mem_singleton] at hl
        rcases hl with rfl | hl
        · exact ⟨0, Or.inl rfl⟩
        · rcases hl with rfl | hl
          · exact ⟨0, Or.inl rfl⟩
          · cases hl)
  have hRec1 := happU hRec0 hA
  have hRec2 := happU hRec1 hP
  have hRec3 := happU hRec2 hMn
  have hRec4 := happU hRec3 hMc
  have hRec5 := happU hRec4 htl
  have h3 := happU h2 hRec5
  exact h3

def listNilIotaU : IotaEquationTyped listGroupU ⟨0, by decide⟩ 8 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact listNilIotaTyU

def listConsIotaU : IotaEquationTyped listGroupU ⟨1, by decide⟩ 8 [.nonrecursive, .recursive 0] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact listConsIotaTyU

def listIotaClauseU : IotaDescriptorClause listPrefixU listGroupU where
  signatureOnly := rfl
  shapesAt := shapes
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => listNilIotaU
    | ⟨1, _⟩ => listConsIotaU

def listRecAdmittedU : IndGroupAdmitted listPrefixU 11 listURecMember :=
  .recursor listGroupU rfl listCensusU
    (fun i =>
      match i with
      | ⟨0, _⟩ => fun j => j.elim0
      | ⟨1, _⟩ => listConsUniverseU _ rfl)
    (fun i =>
      match i with
      | ⟨0, _⟩ => fun j => j.elim0
      | ⟨1, _⟩ => fun j =>
          match j with
          | ⟨0, _⟩ => ⟨.nonrecursive, 8, [], rfl⟩
          | ⟨1, _⟩ => ⟨.recursive 0, 8, [], rfl⟩)
    listMinorMatchU listIotaClauseU

def listURecIdxU : RecursorGroupIdxAdmitted listPrefixU 11 listURecMember :=
  .ofAdmitted rfl

/-! ## (3) the stored types in the typed judgment, and the views' typed content -/

/-- `List.{u}` in the typed judgment, wherever the family is present. -/
def listConstTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h8 : E.members 8 = some raisedFam)
    (hn : levelsBounded n [.param 0] = true) :
    HasTyT E n Γ (.const 8 [.param 0]) (.pi (.sort (.param 0)) (.sort (.succ (.param 0)))) :=
  .const Γ 8 [.param 0] raisedFam h8 rfl hn

/-- `List a : Sort (succ u)` for `a : Sort u`. -/
def listOfTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h8 : E.members 8 = some raisedFam)
    (hn : levelsBounded n [.param 0] = true) {a : Expr Nat} (ha : HasTyT E n Γ a (.sort (.param 0))) :
    HasTyT E n Γ (.app (.const 8 [.param 0]) a) (.sort (.succ (.param 0))) :=
  .app Γ _ a (.sort (.param 0)) (.sort (.succ (.param 0))) (listConstTyT h8 hn) ha

/-- the family's stored type, `Π (A : Sort u), Sort (succ u)`, over Nat. -/
def listFamTyT : HasTyT natEnvU 1 [] raisedType (.sort (.imax (.succ (.param 0)) (.succ (.succ (.param 0))))) :=
  .pi [] _ _ _ _ (.sort [] (.param 0)) (.sort _ (.succ (.param 0)))

abbrev listNilSortU : Level := .imax (.succ (.param 0)) (.succ (.param 0))

/-- `nil`'s stored type, `Π (A : Sort u), List A`, wherever the family is present. -/
def listNilTyT {E : ResolvedEnv} (h8 : E.members 8 = some raisedFam) :
    HasTyT E 1 [] listUNilType (.sort listNilSortU) :=
  .pi [] _ _ _ _ (.sort [] (.param 0)) (listOfTyT (n := 1) h8 rfl (.bvar _ 0 _ rfl))

abbrev listConsSortU : Level :=
  .imax (.succ (.param 0)) (.imax (.param 0) (.imax (.succ (.param 0)) (.succ (.param 0))))

/-- `cons`'s stored type, `Π (A : Sort u) (hd : A) (tl : List A), List A`, wherever the family is
    present: with the family alone (ConstructorScope) and after `nil`. -/
def listConsTyT {E : ResolvedEnv} (h8 : E.members 8 = some raisedFam) :
    HasTyT E 1 [] listUConsType (.sort listConsSortU) :=
  .pi [] _ _ _ _ (.sort [] (.param 0))
    (.pi _ _ _ _ _ (.bvar _ 0 _ rfl)
      (.pi _ _ _ _ _ (listOfTyT (n := 1) h8 rfl (.bvar _ 1 _ rfl)) (listOfTyT (n := 1) h8 rfl (.bvar _ 2 _ rfl))))

/-- the motive's type in the context of `A`: `List A → Sort v`, `A` at `bvar i` of its context. -/
abbrev listMotTy (i : Nat) : Expr Nat := .pi (.app (.const 8 [.param 0]) (.bvar i)) (.sort (.param 1))

/-- the recursor's stored type typed in the DerivationScope at two level parameters. -/
def listRecTypeTyT : Σ u, HasTyT listPrefixU 2 [] listURecType (.sort u) :=
  ⟨_, .pi [] _ _ _ _ (.sort [] (.param 0))
    (.pi _ _ _ _ _ (.pi _ _ _ _ _ (listOfTyT (n := 2) rfl rfl (.bvar _ 0 _ rfl)) (.sort _ (.param 1)))
      (.pi _ _ _ _ _
        (.app _ (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1))
          (.app (.const 8 [.param 0]) (.bvar 1)) (.sort (.param 1))
          (.bvar _ 0 (listMotTy 1) rfl)
          (.app _ (.const 9 [.param 0]) (.bvar 1) (.sort (.param 0)) (.app (.const 8 [.param 0]) (.bvar 0))
            (.const _ 9 [.param 0] listUNilMember rfl rfl rfl) (.bvar _ 1 _ rfl)))
        (.pi _ _ _ _ _
          (.pi _ _ _ _ _ (.bvar _ 2 _ rfl)
            (.pi _ _ _ _ _ (listOfTyT (n := 2) rfl rfl (.bvar _ 3 _ rfl))
              (.pi _ _ _ _ _
                (.app _ (.bvar 3) (.bvar 0) (.app (.const 8 [.param 0]) (.bvar 4)) (.sort (.param 1))
                  (.bvar _ 3 (listMotTy 4) rfl) (.bvar _ 0 _ rfl))
                (.app _ (.bvar 4)
                  (.app (.app (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2)) (.bvar 1))
                  (.app (.const 8 [.param 0]) (.bvar 5)) (.sort (.param 1))
                  (.bvar _ 4 (listMotTy 5) rfl)
                  (.app _ (.app (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2)) (.bvar 1)
                    (.app (.const 8 [.param 0]) (.bvar 5)) (.app (.const 8 [.param 0]) (.bvar 6))
                    (.app _ (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2) (.bvar 5)
                      (.pi (.app (.const 8 [.param 0]) (.bvar 6)) (.app (.const 8 [.param 0]) (.bvar 7)))
                      (.app _ (.const 10 [.param 0]) (.bvar 5) (.sort (.param 0))
                        (.pi (.bvar 0) (.pi (.app (.const 8 [.param 0]) (.bvar 1))
                          (.app (.const 8 [.param 0]) (.bvar 2))))
                        (.const _ 10 [.param 0] listUConsMember rfl rfl rfl) (.bvar _ 5 _ rfl))
                      (.bvar _ 2 _ rfl))
                    (.bvar _ 1 _ rfl))))))
          (.pi _ _ _ _ _ (listOfTyT (n := 2) rfl rfl (.bvar _ 3 _ rfl))
            (.app _ (.bvar 3) (.bvar 0) (.app (.const 8 [.param 0]) (.bvar 4)) (.sort (.param 1))
              (.bvar _ 3 (listMotTy 4) rfl) (.bvar _ 0 _ rfl))))))⟩

/-- the family's parameter telescope typed at its recorded sort, wherever the family is present. -/
theorem listFamTypedE (E : ResolvedEnv) (h8 : E.members 8 = some raisedFam) :
    FamilyTypedT (listFamViewE E h8) := fun i =>
  match i with
  | ⟨0, _⟩ => ⟨.sort [] (.param 0)⟩

theorem listNilTypedE (E : ResolvedEnv) (h8 : E.members 8 = some raisedFam) :
    CtorTypedT (listNilViewE E h8) :=
  ⟨fun i => match i with | ⟨0, _⟩ => ⟨.sort [] (.param 0)⟩,
   fun i => match i with | ⟨0, _⟩ => ⟨.refl _ _⟩⟩

theorem listConsTypedE (E : ResolvedEnv) (h8 : E.members 8 = some raisedFam) :
    CtorTypedT (listConsViewE E h8) :=
  ⟨fun i => match i with
    | ⟨0, _⟩ => ⟨.sort [] (.param 0)⟩
    | ⟨1, _⟩ => ⟨.bvar _ 0 _ rfl⟩
    | ⟨2, _⟩ => ⟨listOfTyT (n := 1) h8 rfl (.bvar _ 1 _ rfl)⟩,
   fun i => match i with | ⟨0, _⟩ => ⟨.refl _ _⟩⟩

theorem listFamTypedU : IndGroupTypedT listFamAdmittedU := listFamTypedE _ rfl

theorem listNilTypedU : IndGroupTypedT listNilAdmittedU := ⟨listFamTypedE _ rfl, listNilTypedE _ rfl⟩

theorem listConsTypedU : IndGroupTypedT listConsAdmittedU := ⟨listFamTypedE _ rfl, listConsTypedE _ rfl⟩

theorem listRecTypedU : IndGroupTypedT listRecAdmittedU :=
  ⟨listFamTypedE _ rfl, fun i => match i with
    | ⟨0, _⟩ => listNilTypedE _ rfl
    | ⟨1, _⟩ => listConsTypedE _ rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (synCheck _ _) rfl
    | ⟨1, _⟩ => iotaEquationTypedT_of_check (synCheck _ _) rfl⟩

/-! ## (4) the group step: Nat, then List -/

/-- L-K1's checks, member by member, each member's stored type typed in the group built so far, the
    constructors' also with the family alone (ConstructorScope), and the views' typed content. -/
def listMembersU :
    GroupMembersT listFamOnlyU natEnvU
      [(8, raisedFam), (9, listUNilMember), (10, listUConsMember), (11, listURecMember)] listEnvUT :=
  .cons _ 8 raisedFam _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    listFamAdmittedU PUnit.unit _ listFamTyT (fun h => absurd h (by decide))
    listFamTypedU
    (.cons _ 9 listUNilMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      listNilAdmittedU PUnit.unit _ (listNilTyT rfl) (fun _ => ⟨listNilTyT rfl⟩)
      listNilTypedU
      (.cons _ 10 listUConsMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        listConsAdmittedU PUnit.unit _ (listConsTyT rfl)
        (fun _ => ⟨listConsTyT rfl⟩) listConsTypedU
        (.cons _ 11 listURecMember _ _ rfl rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl
          rfl listRecAdmittedU (.ofCheck _ _ (by with_unfolding_all rfl)) _ listRecTypeTyT.2 (fun h => absurd h (by decide))
          listRecTypedU (.nil _))))

/-- Nat's group, then List's: TWO group steps of the typed environment judgment. -/
def listEnvUWfT : EnvWfT listEnvUT :=
  .group natEnvU 8 raisedFam [(9, listUNilMember), (10, listUConsMember)] 11 listURecMember listEnvUT
    natEnvUWfT rfl (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl listMembersU

/-! ## (5) the copy's structured views -/

/-- `List.{u} : Π (A : Sort u), Sort (succ u)`: one parameter, no index, a `Type` family. -/
def listFamViewT : FamViewT raisedFam where
  params := [(.sort (.param 0), .succ (.param 0))]
  indices := []
  sort := .succ (.param 0)
  stored := rfl
  profile := Or.inr (uniformType_succ_param 0)

/-- `nil : Π A, List A`: the mirror `A`, no field. Its stored type is the one built, by `rfl`. -/
def listNilCtorT : GroupCtorT natEnvU 8 raisedFam listFamViewT where
  ref := 9
  member := listUNilMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := listNilSortU
  hT := listNilTyT rfl
  hlvl := rfl
  view :=
    { mirrors := [(.sort (.param 0), .succ (.param 0))]
      fields := []
      res := []
      stored := rfl
      mirrorsConv := .cons [] _ _ _ _ [] [] (.refl [] _) (eqN_refl _) (.nil _)
      typed := .nil _ 0 [] (.nil _)
      univ := fun _ _ h => (List.not_mem_nil _ h).elim
      drecD_typed := drecDTypedT_of_absent (by decide) }

/-- `cons : Π A (hd : A) (tl : List A), List A`: the mirror `A`, a plain field at `u`, a directly
    recursive field. Its stored type is the one built, by `rfl`. -/
def listConsCtorT : GroupCtorT natEnvU 8 raisedFam listFamViewT where
  ref := 10
  member := listUConsMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := listConsSortU
  hT := listConsTyT rfl
  hlvl := rfl
  view :=
    { mirrors := [(.sort (.param 0), .succ (.param 0))]
      fields := [.plain (.bvar 0) (.param 0), .drec []]
      res := []
      stored := rfl
      mirrorsConv := .cons [] _ _ _ _ [] [] (.refl [] _) (eqN_refl _) (.nil _)
      typed := .plain _ 0 (.bvar 0) (.param 0) _ [] (.bvar _ 0 _ rfl)
        (.drec _ 1 [] [] [] (.nil _) (.nil _ 1 [] (.nil _)))
      univ := fun D u h => by
        simp only [List.mem_cons, List.mem_singleton, FieldT.plain.injEq, List.not_mem_nil, or_false]
          at h
        rcases h with ⟨rfl, rfl⟩ | h
        · exact Or.inr ⟨uniformType_succ_param 0, leN_param_succ 0⟩
        · cases h
      drecD_typed := drecDTypedT_of_absent (by decide) }

/-- the constructors, the group list's head added last. -/
def listCsT : List (GroupCtorT natEnvU 8 raisedFam listFamViewT) := [listConsCtorT, listNilCtorT]

/-- THE PREDICTION, which could have failed: the copy's builders (`RcicTypedGroup`) and L-K1's
    derivation (`RcicFixtures`, `PosList`) give the same types at a parameterized, universe-polymorphic
    family — the constructors' (a mirror, a plain field, a directly recursive field) and the AnySort
    recursor's (a minor with an induction hypothesis, the motive at `param 1`). -/
theorem listBuilt_eq_stored :
    listUNilMember.mtype = ctorTypeT 8 (canonLevels 1) listFamViewT.params [] [] ∧
    listUConsMember.mtype =
      ctorTypeT 8 (canonLevels 1) listFamViewT.params [.plain (.bvar 0) (.param 0), .drec []] [] ∧
    listURecMember.mtype = groupRecTypeT listCsT .anySort :=
  ⟨rfl, rfl, rfl⟩

/-- TOOTH: the recursor equation reads the field kinds. With `tl` a plain field the built recursor type
    has no induction hypothesis, and it is not L-K1's. (No view has that kind: a plain domain is typed
    without the family.) -/
theorem listRec_kindSensitive :
    listURecMember.mtype ≠ recTypeT 8 (canonLevels 1) listFamViewT.params [] (.param 1)
      [(9, [], []), (10, [.plain (.bvar 0) (.param 0),
        .plain (.app (.const 8 [.param 0]) (.bvar 1)) (.succ (.param 0))], [])] := by
  decide

/-- the recursor: AnySort, its stored type the one built from the views, by `rfl`. -/
def listRecT : GroupRecT natEnvU 8 raisedFam listFamViewT listCsT where
  member := listURecMember
  hcls := rfl
  hnobody := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := fun _ => rfl
  u := listRecTypeTyT.1
  hT := listRecTypeTyT.2
  hlvl := rfl

/-! ## (6) the group in the copy's scope, and the bridge -/

/-- the structured views give the group's members, and the group meets both profiles: no index, a
    `Type` family. -/
def listInScopeT :
    GroupInScopeT natEnvU 8 raisedFam [(9, listUNilMember), (10, listUConsMember)] 11 listURecMember where
  fv := listFamViewT
  htel := .cons [] _ _ [] (.sort [] (.param 0)) (.nil _)
  cs := listCsT
  hctors := rfl
  hlayout := rfl
  grec := listRecT
  hrr := rfl
  hrm := rfl
  hprof := ⟨fun v hv => (List.not_mem_nil v hv).elim, fun h _ => absurd (h fun _ => 0) (by decide)⟩
  hpb := by decide
  hsnd := by decide

theorem listEnvUWfT_inScope : listEnvUWfT.InScope := ⟨natEnvUWfT_inScope, ⟨listInScopeT⟩⟩

theorem pin_envWfT_listU : Nonempty (EnvWfT listEnvUT) := ⟨listEnvUWfT⟩

/-! ## (6) the certificate discharge: every witness over a `listEnvUT`
    sub-environment adapts — the Nat group dispatches to `natEnvU`'s
    certificates, the `List.{u}` group discharges `nil` (empty walk, the
    `bvar 1` minor slot) and `cons` (`.plain` then `.directRec`). -/

open Ann in
/-- member inversion for `listEnvUT`: Nat's group at `0–3`, `List.{u}`'s at
    `8`–`11`. -/
theorem listEnvUT_mem {c : Nat} {m : CheckedMember}
    (h : listEnvUT.members c = some m) :
    (c = 0 ∧ m = natFamMember) ∨ (c = 1 ∧ m = natZeroMember) ∨
      (c = 2 ∧ m = natSuccMember) ∨ (c = 3 ∧ m = natRecMemberU) ∨
      (c = 8 ∧ m = PosList.raisedFam) ∨ (c = 9 ∧ m = listUNilMember) ∨
      (c = 10 ∧ m = listUConsMember) ∨ (c = 11 ∧ m = listURecMember) := by
  have hmem : listEnvUT.members c =
      (if c = 11 then some listURecMember
       else if c = 10 then some listUConsMember
       else if c = 9 then some listUNilMember
       else if c = 8 then some PosList.raisedFam
       else natEnvU.members c) := rfl
  rw [hmem] at h
  by_cases h11 : c = 11
  · rw [if_pos h11] at h; cases h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h11, rfl⟩))))))
  · rw [if_neg h11] at h
    by_cases h10 : c = 10
    · rw [if_pos h10] at h; cases h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h10, rfl⟩))))))
    · rw [if_neg h10] at h
      by_cases h9 : c = 9
      · rw [if_pos h9] at h; cases h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h9, rfl⟩)))))
      · rw [if_neg h9] at h
        by_cases h8 : c = 8
        · rw [if_pos h8] at h; cases h
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h8, rfl⟩))))
        · rw [if_neg h8] at h
          have hnat : natEnvU.members c =
              (if c = 3 then some natRecMemberU
               else if c = 2 then some natSuccMember
               else if c = 1 then some natZeroMember
               else if c = 0 then some natFamMember else none) := rfl
          rw [hnat] at h
          by_cases h3 : c = 3
          · rw [if_pos h3] at h; cases h
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩)))
          · rw [if_neg h3] at h
            by_cases h2 : c = 2
            · rw [if_pos h2] at h; cases h
              exact Or.inr (Or.inr (Or.inl ⟨h2, rfl⟩))
            · rw [if_neg h2] at h
              by_cases h1 : c = 1
              · rw [if_pos h1] at h; cases h
                exact Or.inr (Or.inl ⟨h1, rfl⟩)
              · rw [if_neg h1] at h
                by_cases h0 : c = 0
                · rw [if_pos h0] at h; cases h; exact Or.inl ⟨h0, rfl⟩
                · rw [if_neg h0] at h; exact Option.noConfusion h

open Ann in
/-- the family's const at `8` is rigid wherever the family is present. -/
theorem listEnvU_const8_closed {E₀ : ResolvedEnv}
    (hmem8 : E₀.members 8 = some PosList.raisedFam) :
    (∀ ls, transparentBody E₀ 8 ls = none) ∧
      noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 1)) = true ∧
      noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 2)) = true ∧
      noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 3)) = true ∧
      noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 4)) = true ∧
      noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 5)) = true ∧
      noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 0)) = true := by
  have ht8 : ∀ ls, transparentBody E₀ 8 ls = none := by
    intro ls
    unfold transparentBody
    rw [hmem8]
    rfl
  refine ⟨ht8, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [noTransparentB]
      rw [ht8]
      rfl

open Ann in
/-- `constsMemberFuel` discharges on the List family const. -/
theorem listEnvU_constsMember {E₀ : ResolvedEnv}
    (hmem8 : E₀.members 8 = some PosList.raisedFam) {fuel : Nat} :
    constsMemberFuel E₀ (fuel + 1) (.const 8 [.param 0]) = true := by
  cases fuel with
  | zero => unfold constsMemberFuel; rw [hmem8]; rfl
  | succ f => unfold constsMemberFuel; rw [hmem8]; rfl

open Ann in
/-- The two-group dispatch: any witness's references over a sub-environment of
    `listEnvUT` belong to the Nat group or to the `List.{u}` group — the
    member classes filter the member inversion and the group arithmetic
    (`ctorRef = famRef + 1 + ctorIdx`, `recRef = famRef + 1 + nMinors`,
    `ctorIdx < nMinors`, the recursor's telescope count) closes the
    cross-group combinations. -/
theorem listEnvU_refs {E₀ : ResolvedEnv} (hsub : EnvSub E₀ listEnvUT)
    {recRef ctorRef familyRef : Nat} {recMember ctorMember famMember : CheckedMember}
    {nparams nindices nMinors ctorIdx : Nat}
    (hfam : E₀.members familyRef = some famMember)
    (hfamK : famMember.mclass = .inductiveM)
    (hctor : E₀.members ctorRef = some ctorMember)
    (hctorK : ctorMember.mclass = .constructorM)
    (hrec : E₀.members recRef = some recMember)
    (hrecK : recMember.mclass = .recursorM)
    (hctorIdx : ctorRef = familyRef + 1 + ctorIdx)
    (hrecIdx : recRef = familyRef + 1 + nMinors)
    (hidx : ctorIdx < nMinors)
    (hnmin : nparams + 1 + nMinors + nindices + 1 = piCount recMember.mtype) :
    (familyRef = 0 ∧ famMember = natFamMember ∧ recRef = 3 ∧
      recMember = natRecMemberU ∧
      ((ctorRef = 1 ∧ ctorMember = natZeroMember ∧ ctorIdx = 0) ∨
        (ctorRef = 2 ∧ ctorMember = natSuccMember ∧ ctorIdx = 1))) ∨
    (familyRef = 8 ∧ famMember = PosList.raisedFam ∧ recRef = 11 ∧
      recMember = listURecMember ∧
      ((ctorRef = 9 ∧ ctorMember = listUNilMember ∧ ctorIdx = 0) ∨
        (ctorRef = 10 ∧ ctorMember = listUConsMember ∧ ctorIdx = 1))) := by
  -- pin the family: inductiveM → {natFam at 0, raisedFam at 8}
  rcases listEnvUT_mem (hsub _ _ hfam) with
      ⟨hfr, hfm⟩|⟨hfr, hfm⟩|⟨hfr, hfm⟩|⟨hfr, hfm⟩|⟨hfr, hfm⟩|⟨hfr, hfm⟩|
      ⟨hfr, hfm⟩|⟨hfr, hfm⟩
  case _ => -- c = 0, natFamMember
    subst hfm; subst hfr
    -- pin the recursor: recursorM → {natRec at 3, listURec at 11}
    rcases listEnvUT_mem (hsub _ _ hrec) with
        ⟨hrr, hrm⟩|⟨hrr, hrm⟩|⟨hrr, hrm⟩|⟨hrr, hrm⟩|⟨hrr, hrm⟩|⟨hrr, hrm⟩|
        ⟨hrr, hrm⟩|⟨hrr, hrm⟩
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => -- rec = 3, natRecMemberU: nMinors = 2
      subst hrm; subst hrr
      have hnM : nMinors = 2 := by omega
      subst hnM
      -- pin the constructor: constructorM → {natZero 1, natSucc 2,
      -- listUNil 9, listUCons 10}; the arithmetic kills 9, 10
      rcases listEnvUT_mem (hsub _ _ hctor) with
          ⟨hcr, hcm⟩|⟨hcr, hcm⟩|⟨hcr, hcm⟩|⟨hcr, hcm⟩|⟨hcr, hcm⟩|
          ⟨hcr, hcm⟩|⟨hcr, hcm⟩|⟨hcr, hcm⟩
      case _ => exact absurd (hcm ▸ hctorK) (by decide)
      case _ => -- ctor = 1, natZero
        subst hcm; subst hcr
        exact Or.inl ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, by omega⟩⟩
      case _ => -- ctor = 2, natSucc
        subst hcm; subst hcr
        exact Or.inl ⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, by omega⟩⟩
      case _ => exact absurd (hcm ▸ hctorK) (by decide)
      case _ => exact absurd (hcm ▸ hctorK) (by decide)
      case _ => -- ctor = 9: 9 = 1 + ctorIdx, ctorIdx < 2 — impossible
        subst hcr; exact False.elim (by omega)
      case _ => -- ctor = 10: same
        subst hcr; exact False.elim (by omega)
      case _ => exact absurd (hcm ▸ hctorK) (by decide)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => -- rec = 11, listURecMember: nMinors = 10, killed by hnmin
      subst hrm; subst hrr
      have h5 : piCount listURecMember.mtype = 5 := rfl
      rw [h5] at hnmin
      exact False.elim (by omega)
  case _ => exact absurd (hfm ▸ hfamK) (by decide)
  case _ => exact absurd (hfm ▸ hfamK) (by decide)
  case _ => exact absurd (hfm ▸ hfamK) (by decide)
  case _ => -- c = 8, raisedFam
    subst hfm; subst hfr
    rcases listEnvUT_mem (hsub _ _ hrec) with
        ⟨hrr, hrm⟩|⟨hrr, hrm⟩|⟨hrr, hrm⟩|⟨hrr, hrm⟩|⟨hrr, hrm⟩|⟨hrr, hrm⟩|
        ⟨hrr, hrm⟩|⟨hrr, hrm⟩
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => -- rec = 3: 3 = 9 + nMinors impossible
      subst hrr; exact False.elim (by omega)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => exact absurd (hrm ▸ hrecK) (by decide)
    case _ => -- rec = 11: nMinors = 2
      subst hrm; subst hrr
      have hnM : nMinors = 2 := by omega
      subst hnM
      rcases listEnvUT_mem (hsub _ _ hctor) with
          ⟨hcr, hcm⟩|⟨hcr, hcm⟩|⟨hcr, hcm⟩|⟨hcr, hcm⟩|⟨hcr, hcm⟩|
          ⟨hcr, hcm⟩|⟨hcr, hcm⟩|⟨hcr, hcm⟩
      case _ => exact absurd (hcm ▸ hctorK) (by decide)
      case _ => -- ctor = 1: 1 = 9 + ctorIdx impossible
        subst hcr; exact False.elim (by omega)
      case _ => -- ctor = 2: same
        subst hcr; exact False.elim (by omega)
      case _ => exact absurd (hcm ▸ hctorK) (by decide)
      case _ => exact absurd (hcm ▸ hctorK) (by decide)
      case _ => -- ctor = 9, listUNil
        subst hcm; subst hcr
        exact Or.inr ⟨rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, by omega⟩⟩
      case _ => -- ctor = 10, listUCons
        subst hcm; subst hcr
        exact Or.inr ⟨rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, by omega⟩⟩
      case _ => exact absurd (hcm ▸ hctorK) (by decide)
  case _ => exact absurd (hfm ▸ hfamK) (by decide)
  case _ => exact absurd (hfm ▸ hfamK) (by decide)
  case _ => exact absurd (hfm ▸ hfamK) (by decide)

open Ann in
open Ann in
/-- The `(nparams, nindices)` split for a `List.{u}`-group witness:
    `hnidx` bounds the sum by the family's arity `1`; `hrecBody`'s
    single-argument body `motive major` forces `nindices = 0`, so
    `nparams = 1`.  Stated on the raw components so `IotaWitness` and
    `IotaWitnessS` share it. -/
theorem listU_npni {nparams nindices nMinors : Nat} {famMember : CheckedMember}
    {recBody : Expr Nat}
    (hnidx : nparams + nindices = piCount famMember.mtype)
    (hfamM : famMember = PosList.raisedFam) (_hnM : nMinors = 2)
    (hrecBody : recBody = foldApps (.bvar (nMinors + nindices + 1))
        ((List.range nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++
          [Expr.bvar 0]))
    (hrecBodyVal : recBody = .app (.bvar 3) (.bvar 0)) :
    nparams = 1 ∧ nindices = 0 := by
  have hni : nindices = 0 := by
    have h := hrecBody
    rw [hrecBodyVal] at h
    have hsp := congrArg appsSpine h
    rw [appsSpine_foldApps] at hsp
    -- (bvar 3, [bvar 0]) = (bvar _, idxs ++ [bvar 0])
    have hargs := congrArg Prod.snd hsp
    have hlen := congrArg List.length hargs
    simp only [appsSpine, List.length_append, List.length_map,
      List.length_reverse, List.length_range, List.length_cons,
      List.length_nil] at hargs hlen
    omega
  refine ⟨?_, hni⟩
  rw [hfamM] at hnidx
  have h1 : piCount PosList.raisedFam.mtype = 1 := rfl
  rw [h1, hni] at hnidx
  omega

open Ann in
/-- erase-side per-witness adaptation for a witness whose references are the
    `List.{u}` group's — the `natEraseCert_of_refs` proof transplanted to one
    parameter: `nil` is the zero-shape (empty field walk, minor `bvar 1` —
    the nil-minor slot at `ctorIdx = 0` of `preMajor`); `cons` is the
    succ-shape at `ctorIdx = 1` — a `.plain` head field then a `.directRec`
    tail, whose recursive call carries the recursor prefix `[A, P, mn, mc]`
    with no family-index arguments (`nindices = 0`). -/
theorem listEraseCert_of_refs {E₀ : ResolvedEnv} (w : IotaWitness E₀)
    (hmem8 : E₀.members 8 = some PosList.raisedFam)
    (hfamR : w.familyRef = 8) (hfamM : w.famMember = PosList.raisedFam)
    (hctorD : (w.ctorRef = 9 ∧ w.ctorMember = listUNilMember) ∨
      (w.ctorRef = 10 ∧ w.ctorMember = listUConsMember))
    (hrecR : w.recRef = 11) (hrecM : w.recMember = listURecMember) :
    ∃ fuel, iotaWitnessSB w fuel = true := by
  have hnM : w.nMinors = 2 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hnpni : w.nparams + w.nindices = 1 := by
    have h := w.hnidx; rw [hfamM] at h
    have h1 : piCount PosList.raisedFam.mtype = 1 := rfl
    rw [h1] at h; exact h
  have hbody : w.recBody = .app (.bvar 3) (.bvar 0) := by
    have h := w.hpeelRec; rw [hrecM, hnM] at h
    rw [show w.nparams + 1 + 2 + w.nindices + 1 = 5 from by omega] at h
    have hc : peelPis 5 listURecMember.mtype =
        some (_, .app (.bvar 3) (.bvar 0)) := rfl
    rw [hc] at h
    exact (Prod.mk.inj (Option.some.inj h)).2.symm
  have hni : w.nindices = 0 := by
    have h := w.hrecBody
    rw [hbody] at h
    have hsp := congrArg appsSpine h
    rw [appsSpine_foldApps] at hsp
    have hargs := congrArg Prod.snd hsp
    have hlen := congrArg List.length hargs
    simp only [appsSpine, List.length_append, List.length_map,
      List.length_reverse, List.length_range, List.length_cons,
      List.length_nil] at hargs hlen
    omega
  have hnp : w.nparams = 1 := by omega
  have htr8 : ∀ ls, transparentBody E₀ 8 ls = none := by
    intro ls; unfold transparentBody; rw [hmem8]; rfl
  have hnt8b1 : noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 1)) =
      true := by
    show ((transparentBody E₀ 8 [.param 0]).isNone &&
      noTransparentB E₀ (.bvar 1)) = true
    rw [htr8]; rfl
  have hnt8b5 : noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 5)) =
      true := by
    show ((transparentBody E₀ 8 [.param 0]).isNone &&
      noTransparentB E₀ (.bvar 5)) = true
    rw [htr8]; rfl
  have hst8b1 : headStableB (piTailOf (.app (.const 8 [.param 0]) (.bvar 1))) =
      true := rfl
  have hst8b5 : headStableB (piTailOf (.app (.const 8 [.param 0]) (.bvar 5))) =
      true := rfl
  have hpmLen : w.preMajor.length = 4 := by
    have h := w.hpre; rw [hnp, hnM, hni] at h; exact h
  obtain ⟨a, b, c, d, hpm⟩ : ∃ a b c d, w.preMajor = [a, b, c, d] := by
    generalize hpm0 : w.preMajor = pm
    rw [hpm0] at hpmLen
    rcases pm with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, pm'⟩⟩⟩⟩
    · simp at hpmLen
    · simp only [List.length_cons, List.length_nil] at hpmLen; exact False.elim (by omega)
    · simp only [List.length_cons, List.length_nil] at hpmLen; exact False.elim (by omega)
    · simp only [List.length_cons, List.length_nil] at hpmLen; exact False.elim (by omega)
    · rcases pm' with _ | ⟨e, pm''⟩
      · exact ⟨a, b, c, d, rfl⟩
      · simp only [List.length_cons] at hpmLen; exact False.elim (by omega)
  obtain ⟨l0, l1, hls⟩ : ∃ l0 l1, w.ls = [l0, l1] := by
    have h := w.hlsLen; rw [hrecM] at h
    have h2 : listURecMember.arity = 2 := rfl
    rw [h2] at h
    generalize hlg : w.ls = lsg
    rw [hlg] at h
    rcases lsg with _ | ⟨l0, _ | ⟨l1, _ | ⟨l', ls'⟩⟩⟩
    · simp at h
    · simp only [List.length_cons, List.length_nil] at h; exact False.elim (by omega)
    · exact ⟨l0, l1, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  rcases hctorD with ⟨hctorR, hctorM⟩ | ⟨hctorR, hctorM⟩
  · -- ======================= nil =======================
    have hctorIdx : w.ctorIdx = 0 := by
      have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
    have hfields : w.fields = [] := by
      have h := w.hnpar; rw [hnp, hctorM] at h
      have h1 : piCount listUNilMember.mtype = 1 := rfl
      rw [h1] at h
      exact List.length_eq_zero.mp (by omega)
    have hcd : w.ctorDoms = [.sort (.param 0)] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_nil, Nat.add_zero] at h
      have hc : peelPis 1 listUNilMember.mtype =
          some ([.sort (.param 0)],
            .app (.const 8 [.param 0]) (.bvar 0)) := rfl
      rw [hc] at h
      injection h with hp; injection hp with h1 h2; exact h1.symm
    have hcr : w.ctorResult = .app (.const 8 [.param 0]) (.bvar 0) := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_nil, Nat.add_zero] at h
      have hc : peelPis 1 listUNilMember.mtype =
          some ([.sort (.param 0)],
            .app (.const 8 [.param 0]) (.bvar 0)) := rfl
      rw [hc] at h
      injection h with hp; injection hp with h1 h2; exact h2.symm
    have hkinds : w.kinds = [] := by
      have h := w.hkinds; rw [hfamR, hcd, hnp] at h
      have ha : analyzeFields 8 (List.drop 1 [.sort (.param 0)]) =
          some [] := rfl
      rw [ha] at h
      injection h with h'; exact h'.symm
    refine ⟨8, ?_⟩
    show iotaWitnessSB w 8 = true
    unfold iotaWitnessSB
    rw [hfamR, hfamM, hnp, hni, hnM, hfields, hcd, hcr]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · -- directFragCheck on the empty post-parameter domain list
        rfl
      · -- iotaWitnessStableB: no field domains, no fields, tel = `List A`
        show iotaWitnessStableB E₀ 8
            (List.drop 1 [.sort (.param 0)])
            (fieldBvars (List.length ([] : List (Expr Nat))))
            (lift 0 (0 + 1 + 2 + 0) (ctorFieldTelRaw 1 [.sort (.param 0)]
              (.app (.const 8 [.param 0]) (.bvar 0)))) = true
        have htl : lift 0 (0 + 1 + 2 + 0) (ctorFieldTelRaw 1
            ([.sort (.param 0)] : List (Expr Nat))
            (.app (.const 8 [.param 0]) (.bvar 0))) =
            .app (.const 8 [.param 0]) (.bvar 3) := rfl
        rw [htl]
        show ((List.all (List.drop 1 [.sort (.param 0)])
              (constsMemberFuel E₀ 9) &&
            List.all (fieldBvars (List.length ([] : List (Expr Nat))))
              (constsMemberFuel E₀ 9)) &&
            constsMemberFuel E₀ 9
              (.app (.const 8 [.param 0]) (.bvar 3))) = true
        simp only [List.drop_one, List.all_nil, List.all_cons, constsMemberFuel,
          hmem8]
        rfl
    · have hschema : iotaSchemaS w 8 = some (.bvar 1) := by
        show iotaOpenRhs E₀ 8
            (.const w.recRef (canonRecLevels w.recMember.arity))
            (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
            (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
            w.nparams w.nMinors (w.kinds.map shapeOfKind)
            (fieldBvars w.fields.length)
            (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
              (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
          some (.bvar 1)
        rw [hrecR, hrecM, hnp, hni, hnM, hctorIdx, hfields, hcd, hcr, hkinds]
        rfl
      rw [hschema]
      rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rfl
      · rw [decide_eq_true_eq]
        rw [hpm, show ([a, b, c, d] ++ ([] : List (Expr Nat))) =
            [a, b, c, d] from rfl, hls]
        rw [show instantiateLevels [l0, l1] (.bvar 1) = (.bvar 1 : Expr Nat)
            from rfl]
        have hmin : instPrefix [a, b, c, d] (.bvar 1) = w.minor := by
          apply instPrefix_bvar_lt
          · rw [show List.length [a, b, c, d] = (4 : Nat) from rfl]; decide
          · have h := w.hminor; rw [hpm, hnp, hctorIdx] at h; exact h
        rw [hmin]
        unfold iotaRhsOf
        rw [hrecR, hls, hnp, hnM, hfields, hkinds, hpm]
        rfl
  · -- ======================= cons =======================
    have hctorIdx : w.ctorIdx = 1 := by
      have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
    obtain ⟨f0, f1, hfields⟩ : ∃ f0 f1, w.fields = [f0, f1] := by
      have h := w.hnpar; rw [hnp, hctorM] at h
      have h3 : piCount listUConsMember.mtype = 3 := rfl
      rw [h3] at h
      generalize hfg : w.fields = fg
      rw [hfg] at h
      rcases fg with _ | ⟨f0, _ | ⟨f1, _ | ⟨f', fs'⟩⟩⟩
      · simp at h
      · simp only [List.length_cons, List.length_nil] at h; exact False.elim (by omega)
      · exact ⟨f0, f1, rfl⟩
      · simp only [List.length_cons] at h; exact False.elim (by omega)
    have hcd : w.ctorDoms = [.sort (.param 0), .bvar 0,
        .app (.const 8 [.param 0]) (.bvar 1)] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_cons, List.length_nil] at h
      have hc : peelPis (1 + 2) listUConsMember.mtype =
          some ([.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)],
            .app (.const 8 [.param 0]) (.bvar 2)) := rfl
      rw [hc] at h
      injection h with hp; injection hp with h1 h2; exact h1.symm
    have hcr : w.ctorResult = .app (.const 8 [.param 0]) (.bvar 2) := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_cons, List.length_nil] at h
      have hc : peelPis (1 + 2) listUConsMember.mtype =
          some ([.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)],
            .app (.const 8 [.param 0]) (.bvar 2)) := rfl
      rw [hc] at h
      injection h with hp; injection hp with h1 h2; exact h2.symm
    have hkinds : w.kinds = [.plain, .directRec] := by
      have h := w.hkinds; rw [hfamR, hcd, hnp] at h
      have ha : analyzeFields 8 (List.drop 1 ([.sort (.param 0), .bvar 0,
          .app (.const 8 [.param 0]) (.bvar 1)] : List (Expr Nat))) =
          some [.plain, .directRec] := rfl
      rw [ha] at h
      injection h with h'; exact h'.symm
    have hctorAfter : w.ctorAfterParams =
        .pi a (.pi (.app (.const 8 [l0]) (lift 0 1 a))
          (.app (.const 8 [l0]) (lift 0 1 (lift 0 1 a)))) := by
      have h := w.hctorAfter
      rw [hnp, hpm, hls, hctorM] at h
      have hc : applyTel (List.take 1 [a, b, c, d])
          (instantiateLevels [l0, l1] listUConsMember.mtype) =
          some (.pi a (.pi (.app (.const 8 [l0]) (lift 0 1 a))
            (.app (.const 8 [l0]) (lift 0 1 (lift 0 1 a))))) := rfl
      rw [hc] at h
      injection h with h'; exact h'.symm
    have hpmTk : w.preMajor.take 1 = [a] := by rw [hpm]; rfl
    have hlen6 : (w.preMajor ++ w.fields).length = 6 := by
      rw [List.length_append, hpmLen, hfields]; rfl
    refine ⟨8, ?_⟩
    show iotaWitnessSB w 8 = true
    unfold iotaWitnessSB
    rw [hfamR, hfamM, hnp, hni, hnM, hfields, hcd, hcr]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · -- directFragCheck on [.bvar 0, List.{u} A]
        rw [show List.drop 1 ([.sort (.param 0), .bvar 0,
            .app (.const 8 [.param 0]) (.bvar 1)] : List (Expr Nat)) =
            [.bvar 0, .app (.const 8 [.param 0]) (.bvar 1)] from rfl]
        show (directFragOne E₀ 8 8 PosList.raisedFam.arity 1 0 1
              (.bvar 0) &&
            (directFragOne E₀ 8 8 PosList.raisedFam.arity 1 0 2
              (.app (.const 8 [.param 0]) (.bvar 1)) &&
            directFragCheck E₀ 8 8 PosList.raisedFam.arity 1 0 3 [])) = true
        have hd0 : directFragOne E₀ 8 8 PosList.raisedFam.arity 1 0 1
            (.bvar 0) = true := rfl
        have hd1 : directFragOne E₀ 8 8 PosList.raisedFam.arity 1 0 2
            (.app (.const 8 [.param 0]) (.bvar 1)) = true := by
          unfold directFragOne
          rw [hnt8b1]
          rfl
        rw [hd0, hd1]; rfl
      · -- iotaWitnessStableB
        show iotaWitnessStableB E₀ 8
            (List.drop 1 [.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)])
            (fieldBvars (List.length [f0, f1]))
            (lift 0 ([f0, f1].length + 1 + 2 + 0) (ctorFieldTelRaw 1 [.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)]
              (.app (.const 8 [.param 0]) (.bvar 2)))) = true
        have htl : lift 0 ([f0, f1].length + 1 + 2 + 0) (ctorFieldTelRaw 1
            ([.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)] : List (Expr Nat))
            (.app (.const 8 [.param 0]) (.bvar 2))) =
            .pi (.bvar 5) (.pi (.app (.const 8 [.param 0]) (.bvar 6))
              (.app (.const 8 [.param 0]) (.bvar 7))) := rfl
        rw [htl]
        rw [show fieldBvars (List.length [f0, f1]) =
            [.bvar 1, .bvar 0] from rfl]
        show ((List.all ([.bvar 0, .app (.const 8 [.param 0]) (.bvar 1)] :
                List (Expr Nat)) (constsMemberFuel E₀ 9) &&
              List.all ([.bvar 1, .bvar 0] : List (Expr Nat))
                (constsMemberFuel E₀ 9)) &&
              constsMemberFuel E₀ 9
                (.pi (.bvar 5) (.pi (.app (.const 8 [.param 0]) (.bvar 6))
                  (.app (.const 8 [.param 0]) (.bvar 7))))) = true
        simp only [List.all_cons, List.all_nil, constsMemberFuel, hmem8]
        rfl
    · have hschema : iotaSchemaS w 8 =
          some (foldApps (.bvar 2)
            [.bvar 1, .bvar 0,
              foldApps (.const 11 [.param 0, .param 1])
                [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]]) := by
        show iotaOpenRhs E₀ 8
            (.const w.recRef (canonRecLevels w.recMember.arity))
            (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
            (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
            w.nparams w.nMinors (w.kinds.map shapeOfKind)
            (fieldBvars w.fields.length)
            (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
              (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
          some (foldApps (.bvar 2)
            [.bvar 1, .bvar 0,
              foldApps (.const 11 [.param 0, .param 1])
                [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]])
        rw [hrecR, hrecM, hnp, hni, hnM, hctorIdx, hfields, hcd, hcr, hkinds]
        unfold iotaOpenRhs
        rw [show List.length [f0, f1] = (2 : Nat) from rfl]
        rw [show List.map shapeOfKind [.plain, .directRec] =
            [.nonrecursive, .recursive 0] from rfl]
        rw [show fieldBvars 2 = [.bvar 1, .bvar 0] from rfl]
        have hlt : lift 0 (2 + 1 + 2 + 0) (ctorFieldTelRaw 1
            ([.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)] : List (Expr Nat))
            (.app (.const 8 [.param 0]) (.bvar 2))) =
            .pi (.bvar 5) (.pi (.app (.const 8 [.param 0]) (.bvar 6))
              (.app (.const 8 [.param 0]) (.bvar 7))) := rfl
        rw [hlt]
        simp only [iotaArgs]
        rw [show instantiate 0 (.bvar 1)
            (.app (.const 8 [.param 0]) (.bvar 6)) =
            .app (.const 8 [.param 0]) (.bvar 5) from rfl]
        have hpt : piTelescopeFuel E₀ 8
            (.app (.const 8 [.param 0]) (.bvar 5)) =
            some ([], .app (.const 8 [.param 0]) (.bvar 5)) :=
          piTelescopeFuel_of_tailStable _ hnt8b5 hst8b5 (by decide)
        rw [hpt]
        rfl
      rw [hschema]
      rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rfl
      · rw [decide_eq_true_eq]
        have hL : w.preMajor ++ [f0, f1] = [a, b, c, d, f0, f1] := by
          rw [hpm]; rfl
        rw [hL, hls]
        have hIL : instantiateLevels [l0, l1]
            (foldApps (.bvar 2)
              [.bvar 1, .bvar 0,
                foldApps (.const 11 [.param 0, .param 1])
                  [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]]) =
            foldApps (.bvar 2)
              [.bvar 1, .bvar 0,
                foldApps (.const 11 [l0, l1])
                  [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]] := rfl
        rw [hIL, instPrefix_foldApps]
        have hminI : instPrefix [a, b, c, d, f0, f1] (.bvar 2) = w.minor := by
          apply instPrefix_bvar_lt
          · rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl]
            decide
          · have h := w.hminor; rw [hpm, hnp, hctorIdx] at h; exact h
        rw [hminI]
        simp only [List.map_cons, List.map_nil]
        have hf1I : instPrefix [a, b, c, d, f0, f1] (.bvar 1) = f0 := by
          apply instPrefix_bvar_lt
          · rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl]
            decide
          · rfl
        rw [hf1I]
        have hf0I : instPrefix [a, b, c, d, f0, f1] (.bvar 0) = f1 := by
          apply instPrefix_bvar_lt
          · rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl]
            decide
          · rfl
        rw [hf0I]
        rw [instPrefix_foldApps, instPrefix_const]
        simp only [List.map_cons, List.map_nil]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 5) = a from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 4) = b from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 3) = c from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 2) = d from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 0) = f1 from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        unfold iotaRhsOf
        rw [hrecR, hls, hnp, hnM, hfields, hkinds, hpm]
        have hrcf : recCallField (.const 11 [l0, l1]) [a, b, c, d] 1 2 f1
            (.app (.const 8 [l0])
              (instantiate 0 f0 (lift 0 1 a))) =
            foldApps (.const 11 [l0, l1]) [a, b, c, d, f1] := by
          show foldApps (.const 11 [l0, l1])
              (recPrefix [a, b, c, d] 1 2 ++
                familyIdx 1 (.app (.const 8 [l0]) (instantiate 0 f0
                  (lift 0 1 a))) ++ [f1]) = _
          rw [show recPrefix [a, b, c, d] 1 2 = [a, b, c, d] from rfl]
          rw [show familyIdx 1 (.app (.const 8 [l0])
              (instantiate 0 f0 (lift 0 1 a))) = [] from rfl]
          rfl
        have hrhs : rhsArgs (.const 11 [l0, l1]) [a, b, c, d] 1 2 [f0, f1]
            [.plain, .directRec] w.ctorAfterParams =
            [f0, f1, foldApps (.const 11 [l0, l1]) [a, b, c, d, f1]] := by
          rw [hctorAfter]
          show [f0, f1, recCallField (.const 11 [l0, l1]) [a, b, c, d] 1 2 f1
              (.app (.const 8 [l0]) (instantiate 0 f0 (lift 0 1 a)))] = _
          rw [hrcf]
        rw [hrhs]

open Ann in
/-- ann-side per-witness check for a witness whose references are the
    `List.{u}` group's — `natAnnCert_of_refs` transplanted to one parameter:
    `nil` is the empty shape-walk, `cons` is `[.nonrecursive, .recursive 0]`. -/
theorem listAnnCert_of_refs {E₀ : ResolvedEnv} (w : IotaWitnessS E₀)
    (hmem8 : E₀.members 8 = some PosList.raisedFam)
    (hfamR : w.familyRef = 8) (hfamM : w.famMember = PosList.raisedFam)
    (hctorD : (w.ctorRef = 9 ∧ w.ctorMember = listUNilMember) ∨
      (w.ctorRef = 10 ∧ w.ctorMember = listUConsMember))
    (hrecR : w.recRef = 11) (hrecM : w.recMember = listURecMember) :
    iotaWitnessSAnnB E₀ w = true := by
  have hnM : w.nMinors = 2 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hnpni : w.nparams + w.nindices = 1 := by
    have h := w.hnidx; rw [hfamM] at h
    have h1 : piCount PosList.raisedFam.mtype = 1 := rfl
    rw [h1] at h; exact h
  have hbody : w.recBody = .app (.bvar 3) (.bvar 0) := by
    have h := w.hpeelRec; rw [hrecM, hnM] at h
    rw [show w.nparams + 1 + 2 + w.nindices + 1 = 5 from by omega] at h
    have hc : peelPis 5 listURecMember.mtype =
        some (_, .app (.bvar 3) (.bvar 0)) := rfl
    rw [hc] at h
    exact (Prod.mk.inj (Option.some.inj h)).2.symm
  have hni : w.nindices = 0 := by
    have h := w.hrecBody
    rw [hbody] at h
    have hsp := congrArg appsSpine h
    rw [appsSpine_foldApps] at hsp
    have hargs := congrArg Prod.snd hsp
    have hlen := congrArg List.length hargs
    simp only [appsSpine, List.length_append, List.length_map,
      List.length_reverse, List.length_range, List.length_cons,
      List.length_nil] at hargs hlen
    omega
  have hnp : w.nparams = 1 := by omega
  have htr8 : ∀ ls, transparentBody E₀ 8 ls = none := by
    intro ls; unfold transparentBody; rw [hmem8]; rfl
  have hnt8b1 : noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 1)) =
      true := by
    show ((transparentBody E₀ 8 [.param 0]).isNone &&
      noTransparentB E₀ (.bvar 1)) = true
    rw [htr8]; rfl
  have hst8b1 : headStableB (piTailOf (.app (.const 8 [.param 0]) (.bvar 1))) =
      true := rfl
  have hnt8b5 : noTransparentB E₀ (.app (.const 8 [.param 0]) (.bvar 5)) =
      true := by
    show ((transparentBody E₀ 8 [.param 0]).isNone &&
      noTransparentB E₀ (.bvar 5)) = true
    rw [htr8]; rfl
  have hst8b5 : headStableB (piTailOf (.app (.const 8 [.param 0]) (.bvar 5))) =
      true := rfl
  have hpmLen : w.preMajor.length = 4 := by
    have h := w.hpre; rw [hnp, hnM, hni] at h; exact h
  obtain ⟨a, b, c, d, hpm⟩ : ∃ a b c d, w.preMajor = [a, b, c, d] := by
    generalize hpm0 : w.preMajor = pm
    rw [hpm0] at hpmLen
    rcases pm with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, pm'⟩⟩⟩⟩
    · simp at hpmLen
    · simp only [List.length_cons, List.length_nil] at hpmLen; exact False.elim (by omega)
    · simp only [List.length_cons, List.length_nil] at hpmLen; exact False.elim (by omega)
    · simp only [List.length_cons, List.length_nil] at hpmLen; exact False.elim (by omega)
    · rcases pm' with _ | ⟨e, pm''⟩
      · exact ⟨a, b, c, d, rfl⟩
      · simp only [List.length_cons] at hpmLen; exact False.elim (by omega)
  obtain ⟨l0, l1, hls⟩ : ∃ l0 l1, w.ls = [l0, l1] := by
    have h := w.hlsLen; rw [hrecM] at h
    have h2 : listURecMember.arity = 2 := rfl
    rw [h2] at h
    generalize hlg : w.ls = lsg
    rw [hlg] at h
    rcases lsg with _ | ⟨l0, _ | ⟨l1, _ | ⟨l', ls'⟩⟩⟩
    · simp at h
    · simp only [List.length_cons, List.length_nil] at h; exact False.elim (by omega)
    · exact ⟨l0, l1, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hpmTk : w.preMajor.take 1 = [a] := by rw [hpm]; rfl
  rcases hctorD with ⟨hctorR, hctorM⟩ | ⟨hctorR, hctorM⟩
  · -- ======================= nil =======================
    have hctorIdx : w.ctorIdx = 0 := by
      have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
    have hfields : w.fields = [] := by
      have h := w.hnpar; rw [hnp, hctorM] at h
      have h1 : piCount listUNilMember.mtype = 1 := rfl
      rw [h1] at h
      exact List.length_eq_zero.mp (by omega)
    have hcd : w.ctorDoms = [.sort (.param 0)] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_nil, Nat.add_zero] at h
      have hc : peelPis 1 listUNilMember.mtype =
          some ([.sort (.param 0)],
            .app (.const 8 [.param 0]) (.bvar 0)) := rfl
      rw [hc] at h
      injection h with hp; injection hp with h1 h2; exact h1.symm
    have hcr : w.ctorResult = .app (.const 8 [.param 0]) (.bvar 0) := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_nil, Nat.add_zero] at h
      have hc : peelPis 1 listUNilMember.mtype =
          some ([.sort (.param 0)],
            .app (.const 8 [.param 0]) (.bvar 0)) := rfl
      rw [hc] at h
      injection h with hp; injection hp with h1 h2; exact h2.symm
    have hsh : w.shapes = [] := by
      have h := w.hshapes
      rw [hfamR, hfamM, hnp, hni, hcd,
        show List.drop 1 ([.sort (.param 0)] : List (Expr Nat)) =
          ([] : List (Expr Nat)) from rfl] at h
      exact (Option.some.inj h).symm
    have hsc : w.schema = .bvar 1 := by
      have h := w.hschema
      rw [hrecR, hrecM, hnp, hnM, hni, hctorIdx, hfields, hcd, hcr, hsh] at h
      have hconc : iotaOpenRhs E₀ 8 (.const 11 [.param 0, .param 1])
          (.bvar 1) (preMajorBvars 1 2 0 0) 1 2 []
          (fieldBvars 0) (lift 0 (0 + 1 + 2 + 0) (ctorFieldTelRaw 1
            [.sort (.param 0)]
            (.app (.const 8 [.param 0]) (.bvar 0)))) =
          some (.bvar 1) := rfl
      exact iotaOpenRhs_agree E₀ h hconc
    show iotaWitnessSAnnB E₀ w = true
    unfold iotaWitnessSAnnB
    rw [hfamR, hfamM, hnp, hni, hctorIdx, hcd,
      show List.drop 1 ([.sort (.param 0)] : List (Expr Nat)) =
        ([] : List (Expr Nat)) from rfl]
    rw [Bool.and_eq_true]; refine ⟨rfl, ?_⟩
    have happ : applyTel (w.preMajor.take 1)
        (instantiateLevels (w.ls.take w.ctorMember.arity)
          w.ctorMember.mtype) =
        some (.app (.const 8 [l0]) a) := by
      rw [hctorM, hpmTk, hls]; rfl
    rw [happ]
    simp only
    rw [hfields, hsh]
    rw [show fieldsTelS ([] : List (Expr Nat)) ([] : List FieldShape)
        (.app (.const 8 [l0]) a) = true from rfl, Bool.true_and]
    obtain ⟨minor, hmin⟩ : ∃ m, w.preMajor[1 + 1 + 0]? = some m :=
      ⟨w.preMajor[2]'(by rw [hpmLen]; decide), List.getElem?_eq_getElem _⟩
    rw [hmin]
    simp only
    rw [decide_eq_true_eq]
    unfold iotaRhsOfS
    rw [hpm, hfields]
    rw [show ([a, b, c, d] ++ ([] : List (Expr Nat))) =
        [a, b, c, d] from rfl]
    rw [hls, hsc]
    rw [show instantiateLevels [l0, l1] (.bvar 1) = (.bvar 1 : Expr Nat)
        from rfl]
    have hminI : instPrefix [a, b, c, d] (.bvar 1) = minor := by
      apply instPrefix_bvar_lt
      · rw [show List.length [a, b, c, d] = (4 : Nat) from rfl]; decide
      · rw [hpm] at hmin; exact hmin
    rw [hminI]
    rfl
  · -- ======================= cons =======================
    have hctorIdx : w.ctorIdx = 1 := by
      have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
    obtain ⟨f0, f1, hfields⟩ : ∃ f0 f1, w.fields = [f0, f1] := by
      have h := w.hnpar; rw [hnp, hctorM] at h
      have h3 : piCount listUConsMember.mtype = 3 := rfl
      rw [h3] at h
      generalize hfg : w.fields = fg
      rw [hfg] at h
      rcases fg with _ | ⟨f0, _ | ⟨f1, _ | ⟨f', fs'⟩⟩⟩
      · simp at h
      · simp only [List.length_cons, List.length_nil] at h; exact False.elim (by omega)
      · exact ⟨f0, f1, rfl⟩
      · simp only [List.length_cons] at h; exact False.elim (by omega)
    have hcd : w.ctorDoms = [.sort (.param 0), .bvar 0,
        .app (.const 8 [.param 0]) (.bvar 1)] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_cons, List.length_nil] at h
      have hc : peelPis (1 + 2) listUConsMember.mtype =
          some ([.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)],
            .app (.const 8 [.param 0]) (.bvar 2)) := rfl
      rw [hc] at h
      injection h with hp; injection hp with h1 h2; exact h1.symm
    have hcr : w.ctorResult = .app (.const 8 [.param 0]) (.bvar 2) := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_cons, List.length_nil] at h
      have hc : peelPis (1 + 2) listUConsMember.mtype =
          some ([.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)],
            .app (.const 8 [.param 0]) (.bvar 2)) := rfl
      rw [hc] at h
      injection h with hp; injection hp with h1 h2; exact h2.symm
    have hdrop : List.drop 1 ([.sort (.param 0), .bvar 0,
        .app (.const 8 [.param 0]) (.bvar 1)] : List (Expr Nat)) =
        [.bvar 0, .app (.const 8 [.param 0]) (.bvar 1)] := rfl
    have hd0 : directFragOne E₀ 8 8 PosList.raisedFam.arity 1 0 1
        (.bvar 0) = true := rfl
    have hd1 : directFragOne E₀ 8 8 PosList.raisedFam.arity 1 0 2
        (.app (.const 8 [.param 0]) (.bvar 1)) = true := by
      unfold directFragOne
      rw [hnt8b1, hst8b1]
      rfl
    have hsh : w.shapes = [.nonrecursive, .recursive 0] := by
      have h := w.hshapes
      rw [hfamR, hfamM, hnp, hni, hcd, hdrop] at h
      have hconc : fieldShapesFuel E₀ 8 8 PosList.raisedFam.arity 1 0 1
          [.bvar 0, .app (.const 8 [.param 0]) (.bvar 1)] =
          some [.nonrecursive, .recursive 0] := by
        have hfr : ∀ j (hj : j < ([.bvar 0,
            .app (.const 8 [.param 0]) (.bvar 1)] : List (Expr Nat)).length),
            DirectFieldFrag E₀ 8 8 PosList.raisedFam.arity 1 0 (1 + j)
            [.bvar 0, .app (.const 8 [.param 0]) (.bvar 1)][j] := by
          intro j hj
          simp only [List.length_cons, List.length_nil] at hj
          match j, hj with
          | 0, _ => exact directFragOfCheck hd0
          | 1, _ => exact directFragOfCheck hd1
          | n + 2, h2 => exact absurd h2 (by omega)
        rw [fieldShapesFuel_eq_analyzeFields_of_directFrag _ hfr]
        rfl
      exact fieldShapesFuel_agree E₀ h hconc
    have hsc : w.schema = foldApps (.bvar 2)
        [.bvar 1, .bvar 0,
          foldApps (.const 11 [.param 0, .param 1])
            [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]] := by
      have h := w.hschema
      rw [hrecR, hrecM, hnp, hnM, hni, hctorIdx, hfields, hcd, hcr, hsh] at h
      have hconc : iotaOpenRhs E₀ 8 (.const 11 [.param 0, .param 1])
          (.bvar 2) (preMajorBvars 1 2 0 2) 1 2 [.nonrecursive, .recursive 0]
          (fieldBvars 2) (lift 0 (2 + 1 + 2 + 0) (ctorFieldTelRaw 1
            [.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)]
            (.app (.const 8 [.param 0]) (.bvar 2)))) =
          some (foldApps (.bvar 2)
            [.bvar 1, .bvar 0,
              foldApps (.const 11 [.param 0, .param 1])
                [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]]) := by
        unfold iotaOpenRhs
        rw [show fieldBvars 2 = [.bvar 1, .bvar 0] from rfl]
        have hlt : lift 0 (2 + 1 + 2 + 0) (ctorFieldTelRaw 1
            ([.sort (.param 0), .bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)] : List (Expr Nat))
            (.app (.const 8 [.param 0]) (.bvar 2))) =
            .pi (.bvar 5) (.pi (.app (.const 8 [.param 0]) (.bvar 6))
              (.app (.const 8 [.param 0]) (.bvar 7))) := rfl
        rw [hlt]
        simp only [iotaArgs]
        rw [show instantiate 0 (.bvar 1)
            (.app (.const 8 [.param 0]) (.bvar 6)) =
            .app (.const 8 [.param 0]) (.bvar 5) from rfl]
        have hpt : piTelescopeFuel E₀ 8
            (.app (.const 8 [.param 0]) (.bvar 5)) =
            some ([], .app (.const 8 [.param 0]) (.bvar 5)) :=
          piTelescopeFuel_of_tailStable _ hnt8b5 hst8b5 (by decide)
        rw [hpt]
        rfl
      exact iotaOpenRhs_agree E₀ h hconc
    have hlen6 : (w.preMajor ++ w.fields).length = 6 := by
      rw [List.length_append, hpmLen, hfields]; rfl
    show iotaWitnessSAnnB E₀ w = true
    unfold iotaWitnessSAnnB
    rw [hfamR, hfamM, hnp, hni, hctorIdx, hcd, hdrop]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · -- directFragCheck at `domsFuelBound` of the two post-parameter domains
      show (directFragOne E₀ (domsFuelBound [.bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)])
            8 PosList.raisedFam.arity 1 0 1 (.bvar 0) &&
          (directFragOne E₀ (domsFuelBound [.bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)])
            8 PosList.raisedFam.arity 1 0 2
            (.app (.const 8 [.param 0]) (.bvar 1)) &&
          directFragCheck E₀ (domsFuelBound [.bvar 0,
              .app (.const 8 [.param 0]) (.bvar 1)])
            8 PosList.raisedFam.arity 1 0 3 [])) = true
      have hdF0 : directFragOne E₀ (domsFuelBound [.bvar 0,
          .app (.const 8 [.param 0]) (.bvar 1)])
          8 PosList.raisedFam.arity 1 0 1 (.bvar 0) = true := rfl
      have hdF1 : directFragOne E₀ (domsFuelBound [.bvar 0,
          .app (.const 8 [.param 0]) (.bvar 1)])
          8 PosList.raisedFam.arity 1 0 2
          (.app (.const 8 [.param 0]) (.bvar 1)) = true := by
        unfold directFragOne
        rw [hnt8b1, hst8b1]
        rfl
      rw [hdF0, hdF1]; rfl
    · have happ : applyTel (w.preMajor.take 1)
          (instantiateLevels (w.ls.take w.ctorMember.arity)
            w.ctorMember.mtype) =
          some (.pi a (.pi (.app (.const 8 [l0]) (lift 0 1 a))
            (.app (.const 8 [l0]) (lift 0 1 (lift 0 1 a))))) := by
        rw [hctorM, hpmTk, hls]; rfl
      rw [happ]
      simp only
      rw [hfields, hsh]
      rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rfl
      · obtain ⟨minor, hmin⟩ : ∃ m, w.preMajor[1 + 1 + 1]? = some m :=
          ⟨w.preMajor[3]'(by rw [hpmLen]; decide), List.getElem?_eq_getElem _⟩
        rw [hmin]
        simp only
        rw [decide_eq_true_eq]
        unfold iotaRhsOfS
        rw [hpm, hfields]
        rw [show ([a, b, c, d] ++ [f0, f1] : List (Expr Nat)) =
            [a, b, c, d, f0, f1] from rfl]
        rw [hls, hsc]
        have hIL : instantiateLevels [l0, l1]
            (foldApps (.bvar 2)
              [.bvar 1, .bvar 0,
                foldApps (.const 11 [.param 0, .param 1])
                  [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]]) =
            foldApps (.bvar 2)
              [.bvar 1, .bvar 0,
                foldApps (.const 11 [l0, l1])
                  [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]] := rfl
        rw [hIL, instPrefix_foldApps]
        have hminI : instPrefix [a, b, c, d, f0, f1] (.bvar 2) = minor := by
          apply instPrefix_bvar_lt
          · rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl]
            decide
          · rw [hpm] at hmin; exact hmin
        rw [hminI]
        simp only [List.map_cons, List.map_nil]
        have hf1I : instPrefix [a, b, c, d, f0, f1] (.bvar 1) = f0 := by
          apply instPrefix_bvar_lt
          · rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl]
            decide
          · rfl
        rw [hf1I]
        have hf0I : instPrefix [a, b, c, d, f0, f1] (.bvar 0) = f1 := by
          apply instPrefix_bvar_lt
          · rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl]
            decide
          · rfl
        rw [hf0I]
        rw [instPrefix_foldApps, instPrefix_const]
        simp only [List.map_cons, List.map_nil]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 5) = a from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 4) = b from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 3) = c from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 2) = d from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        rw [show instPrefix [a, b, c, d, f0, f1] (.bvar 0) = f1 from
          instPrefix_bvar_lt
            (by rw [show List.length [a, b, c, d, f0, f1] = (6 : Nat) from rfl];
                decide) rfl]
        rw [hrecR, hnM]
        have hrcf : recCallField (.const 11 [l0, l1]) [a, b, c, d] 1 2 f1
            (.app (.const 8 [l0])
              (instantiate 0 f0 (lift 0 1 a))) =
            foldApps (.const 11 [l0, l1]) [a, b, c, d, f1] := by
          show foldApps (.const 11 [l0, l1])
              (recPrefix [a, b, c, d] 1 2 ++
                familyIdx 1 (.app (.const 8 [l0]) (instantiate 0 f0
                  (lift 0 1 a))) ++ [f1]) = _
          rw [show recPrefix [a, b, c, d] 1 2 = [a, b, c, d] from rfl]
          rw [show familyIdx 1 (.app (.const 8 [l0])
              (instantiate 0 f0 (lift 0 1 a))) = [] from rfl]
          rfl
        have hrhs : rhsArgsS (.const 11 [l0, l1]) [a, b, c, d] 1 2 [f0, f1]
            [.nonrecursive, .recursive 0]
            (.pi a (.pi (.app (.const 8 [l0]) (lift 0 1 a))
              (.app (.const 8 [l0]) (lift 0 1 (lift 0 1 a))))) =
            [f0, f1, foldApps (.const 11 [l0, l1]) [a, b, c, d, f1]] := by
          show [f0, f1, recCallField (.const 11 [l0, l1]) [a, b, c, d] 1 2 f1
              (.app (.const 8 [l0]) (instantiate 0 f0 (lift 0 1 a)))] = _
          rw [hrcf]
        rw [hrhs]

open Ann in
/-- erase-side: every `IotaWitness` over a sub-env of `listEnvUT` adapts —
    Nat-group witnesses via `natEraseCert_of_refs`, List-group witnesses via
    `listEraseCert_of_refs`. -/
theorem corrEraseCert_sub_listEnvUT {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ listEnvUT) : EnvCorrEraseCert E₀ := by
  intro w
  rcases listEnvU_refs hsub w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
      w.hctorIdx w.hrecIdx w.hidx w.hnmin with
    ⟨hfamR, hfamM, hrecR, hrecM, hctorD⟩ | ⟨hfamR, hfamM, hrecR, hrecM, hctorD⟩
  · exact natEraseCert_of_refs w hfamR hfamM
      (hctorD.elim (fun ⟨a, b, _⟩ => Or.inl ⟨a, b⟩)
        (fun ⟨a, b, _⟩ => Or.inr ⟨a, b⟩))
      hrecR hrecM
  · have hmem8 : E₀.members 8 = some PosList.raisedFam := by
      have h := w.hfam; rwa [hfamR, hfamM] at h
    exact listEraseCert_of_refs w hmem8 hfamR hfamM
      (hctorD.elim (fun ⟨a, b, _⟩ => Or.inl ⟨a, b⟩)
        (fun ⟨a, b, _⟩ => Or.inr ⟨a, b⟩))
      hrecR hrecM

open Ann in
/-- ann-side: every `IotaWitnessS` over a sub-env of `listEnvUT` passes
    `iotaWitnessSAnnB`. -/
theorem corrAnnCert_sub_listEnvUT {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ listEnvUT) : EnvCorrAnnCert E₀ := by
  intro w
  rcases listEnvU_refs hsub w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
      w.hctorIdx w.hrecIdx w.hidx w.hnmin with
    ⟨hfamR, hfamM, hrecR, hrecM, hctorD⟩ | ⟨hfamR, hfamM, hrecR, hrecM, hctorD⟩
  · exact natAnnCert_of_refs w hfamR hfamM
      (hctorD.elim (fun ⟨a, b, _⟩ => Or.inl ⟨a, b⟩)
        (fun ⟨a, b, _⟩ => Or.inr ⟨a, b⟩))
      hrecR hrecM
  · have hmem8 : E₀.members 8 = some PosList.raisedFam := by
      have h := w.hfam; rwa [hfamR, hfamM] at h
    exact listAnnCert_of_refs w hmem8 hfamR hfamM
      (hctorD.elim (fun ⟨a, b, _⟩ => Or.inl ⟨a, b⟩)
        (fun ⟨a, b, _⟩ => Or.inr ⟨a, b⟩))
      hrecR hrecM

open Ann in
/-- `listEnvUT` discharges: both certificates at every sub-environment. -/
theorem corrCertsBelow_listEnvUT : CorrCertsBelow listEnvUT :=
  fun _E₀ hsub =>
    ⟨corrEraseCert_sub_listEnvUT hsub, corrAnnCert_sub_listEnvUT hsub⟩

open Ann in
/-- the environment bridge applies at Nat-then-List: conditional on arc D's two typings, like the
    bridge. -/
theorem listEnvU_annotated (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) :
    ∃ EA : ResolvedEnvA, eraseEnv EA = listEnvUT ∧ AnnEnvA EA :=
  (annEnvA_of_envWfT_inScope hT1 hT2 listEnvUWfT listEnvUWfT_inScope).imp fun _ h => ⟨h.1, h.2.1⟩


end Rcic.Declarative

#print axioms Rcic.Declarative.listFamAdmittedU
#print axioms Rcic.Declarative.listNilAdmittedU
#print axioms Rcic.Declarative.listConsAdmittedU
#print axioms Rcic.Declarative.listRecAdmittedU
#print axioms Rcic.Declarative.listEnvUWfT
#print axioms Rcic.Declarative.pin_envWfT_listU
#print axioms Rcic.Declarative.listBuilt_eq_stored
#print axioms Rcic.Declarative.listRec_kindSensitive
#print axioms Rcic.Declarative.listEnvUWfT_inScope
#print axioms Rcic.Declarative.listEnvU_annotated
