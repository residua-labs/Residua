import rcic.RcicTypedGroupPinsList

/-!
# M3-e-5 — `Vec` as a group of the typed environment judgment: the index path

Nat, `True`, `False` and `List` have no index. This file admits `Vec : Sort 1 → N → Sort 1` (L-K1's
fixture family and constructors at `4`–`6`, indexed by Nat's `N`) with the AnySort recursor 05 §11
derives (`vecRecTypeU`, the motive at `param 0`), as a second `EnvWfT` group after Nat's:

(1) the environments, each member's scope;
(2) L-K1's views and checks. The recursor's admission checks its stored type against L-K1's own
    derivation (`recursorType := rfl`), and its ι equations are stated at the constructors' result
    indices (M3-e-5's correction of `iotaLhsType`): `vnil`'s reduct is the minor itself, typed by the
    variable rule, and `vcons`'s carries the induction hypothesis at the field's index;
(3) the stored types in the typed judgment, the views' typed content;
(4) the group step `vecEnvUWfT`;
(5) the copy's structured views with an index, a result index per constructor and a recursive field at
    an index. The constructor and recursor types BUILT from them are the stored ones, by `rfl`, so the
    copy's builders and L-K1's derivation agree on `vecRecTypeU`;
(6) the group in the copy's scope (the small-index profile at a real index) and the bridge, conditional
    on arc D's two typings;
(7) the corrected ι statement on both judgments: `vcons`'s reduct has its corrected type in the TYPED
    judgment with no conversion step (`vecConsIotaTyT`); the old statement differs from it at an indexed
    family (`vecIota_indexSensitive`); `main` accepted the old one only because untyped conversion is
    total (`vecConsOldLhs_mainAccepts`).
-/

namespace Rcic.Declarative

/-! ## (1) the environments -/

/-- `Vec.rec` with the AnySort motive 05 §11 derives: the motive at `param 0`, arity 1. -/
def vecRecTypeU : Expr Nat :=
  .pi (.sort (.succ .zero))
   (.pi (.pi (.const 0 []) (.pi (.app (.app (.const 4 []) (.bvar 1)) (.bvar 0)) (.sort (.param 0))))
    (.pi (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1)))
     (.pi (.pi (.const 0 [])
            (.pi (.bvar 3)
              (.pi (.app (.app (.const 4 []) (.bvar 4)) (.bvar 1))
                (.pi (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))
                  (.app (.app (.bvar 5) (.app (.const 2 []) (.bvar 3)))
                    (.app (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3)) (.bvar 2)) (.bvar 1)))))))
      (.pi (.const 0 [])
       (.pi (.app (.app (.const 4 []) (.bvar 4)) (.bvar 0))
        (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0)))))))

def vecRecMemberU : CheckedMember := ⟨.recursorM, 1, vecRecTypeU, none⟩

/-- the family over Nat: `vnil`'s and `vcons`'s ConstructorScope. -/
def vecFamOnlyU : ResolvedEnv := extendEnv natEnvU 4 vecFamMember
def vecFamNilU : ResolvedEnv := extendEnv vecFamOnlyU 5 vecNilMember
def vecPrefixU : ResolvedEnv := extendEnv vecFamNilU 6 vecConsMember
def vecEnvUT : ResolvedEnv := extendEnv vecPrefixU 7 vecRecMemberU

theorem vecPrefixU_mem (c : Nat) :
    vecPrefixU.members c =
      if c = 6 then some vecConsMember
      else if c = 5 then some vecNilMember
      else if c = 4 then some vecFamMember
      else if c = 3 then some natRecMemberU
      else natEnvPrefix.members c := rfl

theorem vecFamNilU_mem (c : Nat) :
    vecFamNilU.members c =
      if c = 5 then some vecNilMember
      else if c = 4 then some vecFamMember
      else if c = 3 then some natRecMemberU
      else natEnvPrefix.members c := rfl

theorem vecFamOnlyU_mem (c : Nat) :
    vecFamOnlyU.members c =
      if c = 4 then some vecFamMember
      else if c = 3 then some natRecMemberU
      else natEnvPrefix.members c := rfl

/-! ## (2) L-K1's views and checks at each member's scope -/

/-- `N : Sort 1` in the untyped judgment, wherever Nat's family is present. -/
def vecNTy (E : ResolvedEnv) (h0 : E.members 0 = some natFamMember) (Γ : LCtx) :
    HasTy E 0 Γ (.const 0 []) (.sort (.succ .zero)) :=
  HasTy.const (n := 0) Γ 0 [] natFamMember h0 rfl (fun _ h => nomatch h)

/-- `Vec : Sort 1 → N → Sort 1`, wherever the family is present. -/
def vecFamTyU (E : ResolvedEnv) (h4 : E.members 4 = some vecFamMember) (Γ : LCtx) :
    HasTy E 0 Γ (.const 4 []) vecFamType :=
  HasTy.const (n := 0) Γ 4 [] vecFamMember h4 rfl (fun _ h => nomatch h)

/-- the family view: one parameter `A : Sort 1`, one index `N`, result `Sort 1`. -/
def vecFamViewE (E : ResolvedEnv) (h4 : E.members 4 = some vecFamMember)
    (h0 : E.members 0 = some natFamMember) : PolicyFamilyView E where
  ref := 4
  member := vecFamMember
  present := h4
  hasClass := rfl
  parameters := [.sort (.succ .zero)]
  indices := [.const 0 []]
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j => match j with
      | ⟨0, _⟩ => .succ (.succ .zero)
      | ⟨1, _⟩ => .succ .zero
    bounded := fun j => match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    hasType := fun j => match j with
      | ⟨0, _⟩ => HasTy.sort (n := 0) [] (.succ .zero)
      | ⟨1, _⟩ => vecNTy E h0 _
  }

/-- `vnil : Π A, Vec A zero`: no field, the result index `zero`. -/
def vecNilViewE (E : ResolvedEnv) (h4 : E.members 4 = some vecFamMember)
    (h0 : E.members 0 = some natFamMember) :
    PolicyConstructorView E (vecFamViewE E h4 h0) vecNilMember where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ .zero)]
  fields := []
  resultIndices := [.const 1 []]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.succ .zero)
    bounded := fun _ => rfl
    hasType := fun j => match j with
      | ⟨0, _⟩ => HasTy.sort (n := 0) [] (.succ .zero)
  }
  parameterMirrors := fun i => match i with
    | ⟨0, _⟩ => Conv.refl _ _
  noFamilyInIndices := fun e he => by
    simp only [List.mem_singleton] at he
    subst he
    rfl

/-- `vcons : Π A (n : N) (hd : A) (tl : Vec A n), Vec A (succ n)`. -/
def vecConsViewE (E : ResolvedEnv) (h4 : E.members 4 = some vecFamMember)
    (h0 : E.members 0 = some natFamMember) :
    PolicyConstructorView E (vecFamViewE E h4 h0) vecConsMember where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ .zero)]
  fields := [.const 0 [], .bvar 1, .app (.app (.const 4 []) (.bvar 2)) (.bvar 1)]
  resultIndices := [.app (.const 2 []) (.bvar 2)]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j => match j with
      | ⟨0, _⟩ => .succ (.succ .zero)
      | ⟨1, _⟩ => .succ .zero
      | ⟨2, _⟩ => .succ .zero
      | ⟨3, _⟩ => .succ .zero
    bounded := fun j => match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
    hasType := fun j => match j with
      | ⟨0, _⟩ => HasTy.sort (n := 0) [] (.succ .zero)
      | ⟨1, _⟩ => vecNTy E h0 _
      | ⟨2, _⟩ => HasTy.bvar (n := 0) _ 1 (.sort (.succ .zero)) rfl
      | ⟨3, _⟩ =>
          HasTy.app (n := 0) _ (.app (.const 4 []) (.bvar 2)) (.bvar 1) (.const 0 []) (.sort (.succ .zero))
            (HasTy.app (n := 0) _ (.const 4 []) (.bvar 2) (.sort (.succ .zero))
              (.pi (.const 0 []) (.sort (.succ .zero))) (vecFamTyU E h4 _)
              (HasTy.bvar (n := 0) _ 2 (.sort (.succ .zero)) rfl))
            (HasTy.bvar (n := 0) _ 1 (.const 0 []) rfl)
  }
  parameterMirrors := fun i => match i with
    | ⟨0, _⟩ => Conv.refl _ _
  noFamilyInIndices := fun e he => by
    simp only [List.mem_singleton] at he
    subst he
    rfl

/-- Nat's members are no constructors of family `4`. -/
theorem natPrefix_notVec (c : Nat) (cm : CheckedMember) (hc : natEnvPrefix.members c = some cm)
    (hk : cm.mclass = .constructorM) : memberFamRef cm ≠ some 4 := by
  rw [natPrefixMem] at hc
  by_cases h2 : c = 2
  · rw [if_pos h2] at hc
    cases hc
    rw [PosList.natSuccFamily]
    decide
  · by_cases h1 : c = 1
    · rw [if_neg h2, if_pos h1] at hc
      cases hc
      rw [PosList.natZeroFamily]
      decide
    · by_cases h0 : c = 0
      · rw [if_neg h2, if_neg h1, if_pos h0] at hc
        cases hc
        cases hk
      · rw [if_neg h2, if_neg h1, if_neg h0] at hc
        cases hc

/-- Nat's members are no recursor of family `4`. -/
theorem natU_noVecRecursor (c : Nat) (rm : CheckedMember)
    (hc : (if c = 3 then some natRecMemberU else natEnvPrefix.members c) = some rm)
    (hk : rm.mclass = .recursorM) : memberFamRef rm ≠ some 4 := by
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

theorem vecNilFamily : memberFamRef vecNilMember = some 4 := rfl
theorem vecConsFamily : memberFamRef vecConsMember = some 4 := rfl

theorem vecNilBeforeU : CtorBeforeRecursors vecFamOnlyU vecNilMember := by
  refine ⟨4, vecNilFamily, ?_⟩
  intro rr rm hm hk
  rw [vecFamOnlyU_mem] at hm
  by_cases h4 : rr = 4
  · rw [if_pos h4] at hm
    cases hm
    cases hk
  · rw [if_neg h4] at hm
    exact natU_noVecRecursor rr rm hm hk

theorem vecConsBeforeU : CtorBeforeRecursors vecFamNilU vecConsMember := by
  refine ⟨4, vecConsFamily, ?_⟩
  intro rr rm hm hk
  rw [vecFamNilU_mem] at hm
  by_cases h5 : rr = 5
  · rw [if_pos h5] at hm
    cases hm
    cases hk
  · rw [if_neg h5] at hm
    by_cases h4 : rr = 4
    · rw [if_pos h4] at hm
      cases hm
      cases hk
    · rw [if_neg h4] at hm
      exact natU_noVecRecursor rr rm hm hk

theorem vecNilContigU : CtorContiguous vecFamOnlyU 5 vecNilMember := by
  refine ⟨4, vecNilFamily, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd (Nat.lt_of_lt_of_le hl (Nat.le_of_lt_succ hr)) (Nat.lt_irrefl 4)
  · intro c ⟨cm, hm, hk, hf⟩
    rw [vecFamOnlyU_mem] at hm
    by_cases h4 : c = 4
    · rw [if_pos h4] at hm
      cases hm
      cases hk
    · rw [if_neg h4] at hm
      by_cases h3 : c = 3
      · rw [if_pos h3] at hm
        cases hm
        cases hk
      · rw [if_neg h3] at hm
        exact absurd hf (natPrefix_notVec c cm hm hk)

theorem vecConsContigU : CtorContiguous vecFamNilU 6 vecConsMember := by
  refine ⟨4, vecConsFamily, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 5 := by omega
    subst hc
    exact ⟨vecNilMember, rfl, rfl, vecNilFamily⟩
  · intro c ⟨cm, hm, hk, hf⟩
    rw [vecFamNilU_mem] at hm
    by_cases h5 : c = 5
    · exact ⟨by omega, by omega⟩
    · rw [if_neg h5] at hm
      by_cases h4 : c = 4
      · rw [if_pos h4] at hm
        cases hm
        cases hk
      · rw [if_neg h4] at hm
        by_cases h3 : c = 3
        · rw [if_pos h3] at hm
          cases hm
          cases hk
        · rw [if_neg h3] at hm
          exact absurd hf (natPrefix_notVec c cm hm hk)

theorem vecConsUniverseU (E : ResolvedEnv) (h4 : E.members 4 = some vecFamMember)
    (h0 : E.members 0 = some natFamMember) : FieldUniverseAdmitted (vecConsViewE E h4 h0) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
  | ⟨1, _⟩ => exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
  | ⟨2, _⟩ => exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem vecConsFieldsU : CtorFieldsPermitted (vecConsViewE vecFamNilU rfl rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 8, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.nonrecursive, 8, [], rfl⟩
  | ⟨2, _⟩ => exact ⟨.recursive 0, 8, [.bvar 1], rfl⟩

theorem vecConsFieldsP : CtorFieldsPermitted (vecConsViewE vecPrefixU rfl rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 8, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.nonrecursive, 8, [], rfl⟩
  | ⟨2, _⟩ => exact ⟨.recursive 0, 8, [.bvar 1], rfl⟩

def vecFamAdmittedU : IndGroupAdmitted natEnvU 4 vecFamMember :=
  .family rfl (vecFamViewE vecFamOnlyU rfl rfl) rfl rfl (Or.inr uniformType_succ_zero)

def vecNilAdmittedU : IndGroupAdmitted vecFamOnlyU 5 vecNilMember :=
  .constructor (vecFamViewE vecFamOnlyU rfl rfl) (vecNilViewE vecFamOnlyU rfl rfl)
    rfl vecNilBeforeU vecNilContigU (fun j => j.elim0) (fun j => j.elim0)

def vecConsAdmittedU : IndGroupAdmitted vecFamNilU 6 vecConsMember :=
  .constructor (vecFamViewE vecFamNilU rfl rfl) (vecConsViewE vecFamNilU rfl rfl)
    rfl vecConsBeforeU vecConsContigU (vecConsUniverseU _ rfl rfl) vecConsFieldsU

/-- the nil minor, `P zero (vnil A)`, under `A` and the motive. -/
def vecMinorNil : Expr Nat := .app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))

/-- the cons minor, `Π n hd tl (ih : P n tl), P (succ n) (vcons A n hd tl)`, under `A`, the motive and
    the nil minor. -/
def vecMinorCons : Expr Nat :=
  .pi (.const 0 [])
    (.pi (.bvar 3)
      (.pi (.app (.app (.const 4 []) (.bvar 4)) (.bvar 1))
        (.pi (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))
          (.app (.app (.bvar 5) (.app (.const 2 []) (.bvar 3)))
            (.app (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3)) (.bvar 2)) (.bvar 1))))))

/-- L-K1's recursor admission: AnySort, its stored type L-K1's own derivation (`recursorType := rfl`). -/
def vecGroupU : RecursorEliminationAdmitted vecPrefixU 7 vecRecMemberU where
  family := vecFamViewE vecPrefixU rfl rfl
  constructors := [vecNilMember, vecConsMember]
  constructorViews
    | ⟨0, _⟩ => vecNilViewE vecPrefixU rfl rfl
    | ⟨1, _⟩ => vecConsViewE vecPrefixU rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [vecMinorNil, vecMinorCons]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem vecCensusU : CtorCensus vecPrefixU 4 7 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, hf⟩
    rw [vecPrefixU_mem] at hc
    by_cases h6 : c = 6
    · exact ⟨by omega, by omega⟩
    · by_cases h5 : c = 5
      · exact ⟨by omega, by omega⟩
      · rw [if_neg h6, if_neg h5] at hc
        by_cases h4 : c = 4
        · rw [if_pos h4] at hc
          cases hc
          cases hk
        · rw [if_neg h4] at hc
          by_cases h3 : c = 3
          · rw [if_pos h3] at hc
            cases hc
            cases hk
          · rw [if_neg h3] at hc
            exact absurd hf (natPrefix_notVec c cm hc hk)
  · intro h
    have hc : c = 5 ∨ c = 6 := by omega
    rcases hc with rfl | rfl
    · exact ⟨vecNilMember, rfl, rfl, vecNilFamily⟩
    · exact ⟨vecConsMember, rfl, rfl, vecConsFamily⟩

theorem vecMinorMatchU : MinorPremisesMatch vecGroupU := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[], 0, rfl, rfl⟩
  | ⟨1, _⟩ => exact ⟨[.nonrecursive, .nonrecursive, .recursive 0], 8, rfl, rfl⟩

/-! The ι equations. The equation context is the recursor telescope with the major replaced by the
constructor's fields: `[i, mc, mn, P, A]` at `vnil`, `[tl, hd, n, i, mc, mn, P, A]` at `vcons`
(innermost first). The index binder `i` is in scope and unused: under the corrected clause the
reducts are stated at the result indices `zero` and `succ n`, which is the type they have. -/

def vecDomA : Expr Nat := .sort (.succ .zero)
def vecDomP : Expr Nat :=
  .pi (.const 0 []) (.pi (.app (.app (.const 4 []) (.bvar 1)) (.bvar 0)) (.sort (.param 0)))
def vecDomI : Expr Nat := .const 0 []
def vecDomN : Expr Nat := .const 0 []
def vecDomHd : Expr Nat := .bvar 5
def vecDomTl : Expr Nat := .app (.app (.const 4 []) (.bvar 6)) (.bvar 1)

def vecNilCtx : LCtx :=
  [.assumption vecDomI, .assumption vecMinorCons, .assumption vecMinorNil, .assumption vecDomP,
    .assumption vecDomA]

def vecConsCtx : LCtx :=
  [.assumption vecDomTl, .assumption vecDomHd, .assumption vecDomN, .assumption vecDomI,
    .assumption vecMinorCons, .assumption vecMinorNil, .assumption vecDomP, .assumption vecDomA]

/-- `P zero (vnil A)`: the motive at `vnil`'s result index. -/
def vecNilLhs : Expr Nat := .app (.app (.bvar 3) (.const 1 [])) (.app (.const 5 []) (.bvar 4))

/-- `P (succ n) (vcons A n hd tl)`: the motive at `vcons`'s result index. -/
def vecConsLhs : Expr Nat :=
  .app (.app (.bvar 6) (.app (.const 2 []) (.bvar 2)))
    (foldApps (.const 6 []) [.bvar 7, .bvar 2, .bvar 1, .bvar 0])

def vecRecHead : Expr Nat := .const 7 [.param 0]

/-- `Vec.rec A P mn mc n tl`: the recursive call at the field's index `n`. -/
def vecRecApp : Expr Nat :=
  foldApps vecRecHead [.bvar 7, .bvar 6, .bvar 5, .bvar 4, .bvar 2, .bvar 0]

def vecConsRhs : Expr Nat := foldApps (.bvar 4) [.bvar 2, .bvar 1, .bvar 0, vecRecApp]

private def happV {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTy vecEnvUT 1 Γ f (.pi A B)) (ha : HasTy vecEnvUT 1 Γ a A) :
    HasTy vecEnvUT 1 Γ (.app f a) (instantiate0 a B) :=
  HasTy.app (n := 1) Γ f a A B hf ha

def vecNilIotaTyU : HasTy vecEnvUT 1 vecNilCtx (.bvar 2) vecNilLhs :=
  HasTy.bvar (n := 1) vecNilCtx 2 vecNilLhs rfl

def vecConsIotaTyU : HasTy vecEnvUT 1 vecConsCtx vecConsRhs vecConsLhs := by
  have htl : HasTy vecEnvUT 1 vecConsCtx (.bvar 0) (lift 0 1 vecDomTl) :=
    HasTy.bvar (n := 1) vecConsCtx 0 _ rfl
  have hhd : HasTy vecEnvUT 1 vecConsCtx (.bvar 1) (lift 0 2 vecDomHd) :=
    HasTy.bvar (n := 1) vecConsCtx 1 _ rfl
  have hn : HasTy vecEnvUT 1 vecConsCtx (.bvar 2) (lift 0 3 vecDomN) :=
    HasTy.bvar (n := 1) vecConsCtx 2 _ rfl
  have hMc : HasTy vecEnvUT 1 vecConsCtx (.bvar 4) (lift 0 5 vecMinorCons) :=
    HasTy.bvar (n := 1) vecConsCtx 4 _ rfl
  have hMn : HasTy vecEnvUT 1 vecConsCtx (.bvar 5) (lift 0 6 vecMinorNil) :=
    HasTy.bvar (n := 1) vecConsCtx 5 _ rfl
  have hP : HasTy vecEnvUT 1 vecConsCtx (.bvar 6) (lift 0 7 vecDomP) :=
    HasTy.bvar (n := 1) vecConsCtx 6 _ rfl
  have hA : HasTy vecEnvUT 1 vecConsCtx (.bvar 7) (lift 0 8 vecDomA) :=
    HasTy.bvar (n := 1) vecConsCtx 7 _ rfl
  have h1 := happV hMc hn
  have h2 := happV h1 hhd
  have h3 := happV h2 htl
  have hRec0 : HasTy vecEnvUT 1 vecConsCtx vecRecHead
      (instantiateLevels [.param 0] vecRecTypeU) :=
    HasTy.const (n := 1) vecConsCtx 7 [.param 0] vecRecMemberU
      rfl rfl (by
        intro l hl
        simp only [List.mem_singleton] at hl
        subst hl
        exact ⟨0, Or.inl rfl⟩)
  have hRec1 := happV hRec0 hA
  have hRec2 := happV hRec1 hP
  have hRec3 := happV hRec2 hMn
  have hRec4 := happV hRec3 hMc
  have hRec5 := happV hRec4 hn
  have hRec6 := happV hRec5 htl
  have h4 := happV h3 hRec6
  exact h4

def vecNilIotaU : IotaEquationTyped vecGroupU ⟨0, by decide⟩ 8 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact vecNilIotaTyU

def vecConsIotaU : IotaEquationTyped vecGroupU ⟨1, by decide⟩ 8
    [.nonrecursive, .nonrecursive, .recursive 0] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact vecConsIotaTyU

def vecShapes : Fin vecGroupU.constructors.length → List FieldShape
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => [.nonrecursive, .nonrecursive, .recursive 0]

def vecIotaClauseU : IotaDescriptorClause vecPrefixU vecGroupU where
  signatureOnly := rfl
  shapesAt := vecShapes
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => vecNilIotaU
    | ⟨1, _⟩ => vecConsIotaU

def vecRecAdmittedU : IndGroupAdmitted vecPrefixU 7 vecRecMemberU :=
  .recursor vecGroupU rfl vecCensusU
    (fun i =>
      match i with
      | ⟨0, _⟩ => fun j => j.elim0
      | ⟨1, _⟩ => vecConsUniverseU _ rfl rfl)
    (fun i =>
      match i with
      | ⟨0, _⟩ => fun j => j.elim0
      | ⟨1, _⟩ => vecConsFieldsP)
    vecMinorMatchU vecIotaClauseU

def vecRecIdxU : RecursorGroupIdxAdmitted vecPrefixU 7 vecRecMemberU :=
  .ofAdmitted rfl

/-! ## (3) the stored types in the typed judgment, and the views' typed content -/

/-- `Vec : Sort 1 → N → Sort 1` in the typed judgment, wherever the family is present. -/
def vecConstTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h4 : E.members 4 = some vecFamMember) :
    HasTyT E n Γ (.const 4 []) (.pi (.sort (.succ .zero)) (.pi (.const 0 []) (.sort (.succ .zero)))) :=
  .const Γ 4 [] vecFamMember h4 rfl rfl

/-- `Vec a i : Sort 1` for `a : Sort 1` and `i : N`. -/
def vecOfTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h4 : E.members 4 = some vecFamMember)
    {a i : Expr Nat} (ha : HasTyT E n Γ a (.sort (.succ .zero))) (hi : HasTyT E n Γ i (.const 0 [])) :
    HasTyT E n Γ (.app (.app (.const 4 []) a) i) (.sort (.succ .zero)) :=
  .app Γ _ i (.const 0 []) (.sort (.succ .zero))
    (.app Γ (.const 4 []) a (.sort (.succ .zero)) (.pi (.const 0 []) (.sort (.succ .zero)))
      (vecConstTyT h4) ha) hi

/-- the family's stored type, `Π (A : Sort 1) (n : N), Sort 1`, over Nat. -/
def vecFamTyT : Σ u, HasTyT natEnvU 0 [] vecFamType (.sort u) :=
  ⟨_, .pi [] _ _ _ _ (.sort [] (.succ .zero)) (.pi _ _ _ _ _ (natConstTyT rfl) (.sort _ (.succ .zero)))⟩

abbrev vecNilSortU : Level := .imax (.succ (.succ .zero)) (.succ .zero)

/-- `vnil`'s stored type, `Π A, Vec A zero`, wherever the family and `zero` are present. -/
def vecNilTyT {E : ResolvedEnv} (h4 : E.members 4 = some vecFamMember)
    (h1 : E.members 1 = some natZeroMember) : HasTyT E 0 [] vecNilType (.sort vecNilSortU) :=
  .pi [] _ _ _ _ (.sort [] (.succ .zero))
    (vecOfTyT h4 (.bvar _ 0 _ rfl) (.const _ 1 [] natZeroMember h1 rfl rfl))

abbrev vecConsSortU : Level :=
  .imax (.succ (.succ .zero)) (.imax (.succ .zero) (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))))

/-- `vcons`'s stored type, `Π A (n : N) (hd : A) (tl : Vec A n), Vec A (succ n)`, wherever the family,
    Nat and `succ` are present: with the family alone (ConstructorScope) and after `vnil`. -/
def vecConsTyT {E : ResolvedEnv} (h4 : E.members 4 = some vecFamMember)
    (h0 : E.members 0 = some natFamMember) (h2 : E.members 2 = some natSuccMember) :
    HasTyT E 0 [] vecConsType (.sort vecConsSortU) :=
  .pi [] _ _ _ _ (.sort [] (.succ .zero))
    (.pi _ _ _ _ _ (natConstTyT h0)
      (.pi _ _ _ _ _ (.bvar _ 1 _ rfl)
        (.pi _ _ _ _ _ (vecOfTyT h4 (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl))
          (vecOfTyT h4 (.bvar _ 3 _ rfl)
            (.app _ (.const 2 []) (.bvar 2) (.const 0 []) (.const 0 [])
              (.const _ 2 [] natSuccMember h2 rfl rfl) (.bvar _ 2 _ rfl))))))

/-- the motive's type, `Π (n : N), Vec A n → Sort u`, with `A` at `bvar j` under the index binder. -/
abbrev vecMotTy (j : Nat) : Expr Nat :=
  .pi (.const 0 []) (.pi (.app (.app (.const 4 []) (.bvar j)) (.bvar 0)) (.sort (.param 0)))

/-- `Vec.rec`'s stored type typed in the DerivationScope at one level parameter. -/
def vecRecTypeTyT : Σ u, HasTyT vecPrefixU 1 [] vecRecTypeU (.sort u) :=
  ⟨_, .pi [] _ _ _ _ (.sort [] (.succ .zero))
    (.pi _ _ _ _ _
      (.pi _ _ _ _ _ (natConstTyT rfl)
        (.pi _ _ _ _ _ (vecOfTyT rfl (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl)) (.sort _ (.param 0))))
      (.pi _ _ _ _ _
        (.app _ (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))
          (.app (.app (.const 4 []) (.bvar 1)) (.const 1 [])) (.sort (.param 0))
          (.app _ (.bvar 0) (.const 1 []) (.const 0 [])
            (.pi (.app (.app (.const 4 []) (.bvar 2)) (.bvar 0)) (.sort (.param 0)))
            (.bvar _ 0 (vecMotTy 2) rfl) (.const _ 1 [] natZeroMember rfl rfl rfl))
          (.app _ (.const 5 []) (.bvar 1) (.sort (.succ .zero))
            (.app (.app (.const 4 []) (.bvar 0)) (.const 1 []))
            (.const _ 5 [] vecNilMember rfl rfl rfl) (.bvar _ 1 _ rfl)))
        (.pi _ _ _ _ _
          (.pi _ _ _ _ _ (natConstTyT rfl)
            (.pi _ _ _ _ _ (.bvar _ 3 _ rfl)
              (.pi _ _ _ _ _ (vecOfTyT rfl (.bvar _ 4 _ rfl) (.bvar _ 1 _ rfl))
                (.pi _ _ _ _ _
                  (.app _ (.app (.bvar 4) (.bvar 2)) (.bvar 0)
                    (.app (.app (.const 4 []) (.bvar 5)) (.bvar 2)) (.sort (.param 0))
                    (.app _ (.bvar 4) (.bvar 2) (.const 0 [])
                      (.pi (.app (.app (.const 4 []) (.bvar 6)) (.bvar 0)) (.sort (.param 0)))
                      (.bvar _ 4 (vecMotTy 6) rfl) (.bvar _ 2 _ rfl))
                    (.bvar _ 0 _ rfl))
                  (.app _ (.app (.bvar 5) (.app (.const 2 []) (.bvar 3)))
                    (.app (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3)) (.bvar 2)) (.bvar 1))
                    (.app (.app (.const 4 []) (.bvar 6)) (.app (.const 2 []) (.bvar 3)))
                    (.sort (.param 0))
                    (.app _ (.bvar 5) (.app (.const 2 []) (.bvar 3)) (.const 0 [])
                      (.pi (.app (.app (.const 4 []) (.bvar 7)) (.bvar 0)) (.sort (.param 0)))
                      (.bvar _ 5 (vecMotTy 7) rfl)
                      (.app _ (.const 2 []) (.bvar 3) (.const 0 []) (.const 0 [])
                        (.const _ 2 [] natSuccMember rfl rfl rfl) (.bvar _ 3 _ rfl)))
                    (.app _ (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3)) (.bvar 2)) (.bvar 1)
                      (.app (.app (.const 4 []) (.bvar 6)) (.bvar 3))
                      (.app (.app (.const 4 []) (.bvar 7)) (.app (.const 2 []) (.bvar 4)))
                      (.app _ (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3)) (.bvar 2) (.bvar 6)
                        (.pi (.app (.app (.const 4 []) (.bvar 7)) (.bvar 4))
                          (.app (.app (.const 4 []) (.bvar 8)) (.app (.const 2 []) (.bvar 5))))
                        (.app _ (.app (.const 6 []) (.bvar 6)) (.bvar 3) (.const 0 [])
                          (.pi (.bvar 7) (.pi (.app (.app (.const 4 []) (.bvar 8)) (.bvar 1))
                            (.app (.app (.const 4 []) (.bvar 9)) (.app (.const 2 []) (.bvar 2)))))
                          (.app _ (.const 6 []) (.bvar 6) (.sort (.succ .zero))
                            (.pi (.const 0 []) (.pi (.bvar 1) (.pi (.app (.app (.const 4 []) (.bvar 2)) (.bvar 1))
                              (.app (.app (.const 4 []) (.bvar 3)) (.app (.const 2 []) (.bvar 2))))))
                            (.const _ 6 [] vecConsMember rfl rfl rfl) (.bvar _ 6 _ rfl))
                          (.bvar _ 3 _ rfl))
                        (.bvar _ 2 _ rfl))
                      (.bvar _ 1 _ rfl)))))))
          (.pi _ _ _ _ _ (natConstTyT rfl)
            (.pi _ _ _ _ _ (vecOfTyT rfl (.bvar _ 4 _ rfl) (.bvar _ 0 _ rfl))
              (.app _ (.app (.bvar 4) (.bvar 1)) (.bvar 0)
                (.app (.app (.const 4 []) (.bvar 5)) (.bvar 1)) (.sort (.param 0))
                (.app _ (.bvar 4) (.bvar 1) (.const 0 [])
                  (.pi (.app (.app (.const 4 []) (.bvar 6)) (.bvar 0)) (.sort (.param 0)))
                  (.bvar _ 4 (vecMotTy 6) rfl) (.bvar _ 1 _ rfl))
                (.bvar _ 0 _ rfl)))))))⟩

/-- the family's parameter and index typed at their recorded sorts, wherever Nat and the family are
    present. -/
theorem vecFamTypedE (E : ResolvedEnv) (h4 : E.members 4 = some vecFamMember)
    (h0 : E.members 0 = some natFamMember) : FamilyTypedT (vecFamViewE E h4 h0) := fun i =>
  match i with
  | ⟨0, _⟩ => ⟨.sort [] (.succ .zero)⟩
  | ⟨1, _⟩ => ⟨natConstTyT h0⟩

theorem vecNilTypedE (E : ResolvedEnv) (h4 : E.members 4 = some vecFamMember)
    (h0 : E.members 0 = some natFamMember) : CtorTypedT (vecNilViewE E h4 h0) :=
  ⟨fun i => match i with | ⟨0, _⟩ => ⟨.sort [] (.succ .zero)⟩,
   fun i => match i with | ⟨0, _⟩ => ⟨.refl _ _⟩⟩

theorem vecConsTypedE (E : ResolvedEnv) (h4 : E.members 4 = some vecFamMember)
    (h0 : E.members 0 = some natFamMember) : CtorTypedT (vecConsViewE E h4 h0) :=
  ⟨fun i => match i with
    | ⟨0, _⟩ => ⟨.sort [] (.succ .zero)⟩
    | ⟨1, _⟩ => ⟨natConstTyT h0⟩
    | ⟨2, _⟩ => ⟨.bvar _ 1 _ rfl⟩
    | ⟨3, _⟩ => ⟨vecOfTyT h4 (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl)⟩,
   fun i => match i with | ⟨0, _⟩ => ⟨.refl _ _⟩⟩

theorem vecFamTypedU : IndGroupTypedT vecFamAdmittedU := vecFamTypedE _ rfl rfl

theorem vecNilTypedU : IndGroupTypedT vecNilAdmittedU := ⟨vecFamTypedE _ rfl rfl, vecNilTypedE _ rfl rfl⟩

theorem vecConsTypedU : IndGroupTypedT vecConsAdmittedU :=
  ⟨vecFamTypedE _ rfl rfl, vecConsTypedE _ rfl rfl⟩

theorem vecRecTypedU : IndGroupTypedT vecRecAdmittedU :=
  ⟨vecFamTypedE _ rfl rfl, fun i => match i with
    | ⟨0, _⟩ => vecNilTypedE _ rfl rfl
    | ⟨1, _⟩ => vecConsTypedE _ rfl rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (synCheck _ _) rfl
    | ⟨1, _⟩ => iotaEquationTypedT_of_check (synCheck _ _) rfl⟩

/-! ## (4) the group step: Nat, then Vec -/

/-- L-K1's checks, member by member, each member's stored type typed in the group built so far, the
    constructors' also with the family alone (ConstructorScope: Nat's group and `Vec`), and the views'
    typed content. -/
def vecMembersU :
    GroupMembersT vecFamOnlyU natEnvU
      [(4, vecFamMember), (5, vecNilMember), (6, vecConsMember), (7, vecRecMemberU)] vecEnvUT :=
  .cons _ 4 vecFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    vecFamAdmittedU PUnit.unit _ vecFamTyT.2 (fun h => absurd h (by decide))
    vecFamTypedU
    (.cons _ 5 vecNilMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      vecNilAdmittedU PUnit.unit _ (vecNilTyT rfl rfl) (fun _ => ⟨vecNilTyT rfl rfl⟩)
      vecNilTypedU
      (.cons _ 6 vecConsMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        vecConsAdmittedU PUnit.unit _ (vecConsTyT rfl rfl rfl)
        (fun _ => ⟨vecConsTyT rfl rfl rfl⟩) vecConsTypedU
        (.cons _ 7 vecRecMemberU _ _ rfl rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl
          rfl vecRecAdmittedU (.ofCheck _ _ (by with_unfolding_all rfl)) _ vecRecTypeTyT.2 (fun h => absurd h (by decide))
          vecRecTypedU (.nil _))))

/-- Nat's group, then Vec's: TWO group steps of the typed environment judgment, the second over the
    first (Vec's index is Nat). -/
def vecEnvUWfT : EnvWfT vecEnvUT :=
  .group natEnvU 4 vecFamMember [(5, vecNilMember), (6, vecConsMember)] 7 vecRecMemberU vecEnvUT
    natEnvUWfT rfl (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl vecMembersU

/-! ## (5) the copy's structured views -/

/-- `Vec : Π (A : Sort 1) (n : N), Sort 1`: one parameter, one index, a `Type` family. -/
def vecFamViewT : FamViewT vecFamMember where
  params := [(.sort (.succ .zero), .succ (.succ .zero))]
  indices := [(.const 0 [], .succ .zero)]
  sort := .succ .zero
  stored := rfl
  profile := Or.inr uniformType_succ_zero

/-- `vnil : Π A, Vec A zero`: the mirror `A`, no field, the result index `zero`. Its stored type is the
    one built, by `rfl`. -/
def vecNilCtorT : GroupCtorT natEnvU 4 vecFamMember vecFamViewT where
  ref := 5
  member := vecNilMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := vecNilSortU
  hT := vecNilTyT rfl rfl
  hlvl := rfl
  view :=
    { mirrors := [(.sort (.succ .zero), .succ (.succ .zero))]
      fields := []
      res := [.const 1 []]
      stored := rfl
      mirrorsConv := .cons [] _ _ _ _ [] [] (.refl [] _) (eqN_refl _) (.nil _)
      typed := .nil _ 0 _
        (.cons (.const 0 []) (.sort (.succ .zero)) (.const 1 []) []
          (.const _ 1 [] natZeroMember rfl rfl rfl) (.nil _))
      univ := fun _ _ h => (List.not_mem_nil _ h).elim
      drecD_typed := drecDTypedT_of_absent (by decide) }

/-- `vcons : Π A (n : N) (hd : A) (tl : Vec A n), Vec A (succ n)`: the mirror `A`, two plain fields, a
    directly recursive field AT AN INDEX (`n`), the result index `succ n`. Its stored type is the one
    built, by `rfl`. -/
def vecConsCtorT : GroupCtorT natEnvU 4 vecFamMember vecFamViewT where
  ref := 6
  member := vecConsMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := vecConsSortU
  hT := vecConsTyT rfl rfl rfl
  hlvl := rfl
  view :=
    { mirrors := [(.sort (.succ .zero), .succ (.succ .zero))]
      fields := [.plain (.const 0 []) (.succ .zero), .plain (.bvar 1) (.succ .zero), .drec [.bvar 1]]
      res := [.app (.const 2 []) (.bvar 1)]
      stored := rfl
      mirrorsConv := .cons [] _ _ _ _ [] [] (.refl [] _) (eqN_refl _) (.nil _)
      typed := .plain _ 0 (.const 0 []) (.succ .zero) _ _ (natConstTyT rfl)
        (.plain _ 1 (.bvar 1) (.succ .zero) _ _ (.bvar _ 1 _ rfl)
          (.drec _ 2 [.bvar 1] [] _
            (.cons (.const 0 []) (.sort (.succ .zero)) (.bvar 1) [] (.bvar _ 1 _ rfl) (.nil _))
            (.nil _ 2 _
              (.cons (.const 0 []) (.sort (.succ .zero)) (.app (.const 2 []) (.bvar 1)) []
                (.app _ (.const 2 []) (.bvar 1) (.const 0 []) (.const 0 [])
                  (.const _ 2 [] natSuccMember rfl rfl rfl) (.bvar _ 1 _ rfl))
                (.nil _)))))
      univ := fun D u h => by
        rcases List.mem_cons.mp h with h | h
        · cases h
          exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
        · rcases List.mem_cons.mp h with h | h
          · cases h
            exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
          · rcases List.mem_cons.mp h with h | h
            · cases h
            · exact absurd h (List.not_mem_nil _)
      drecD_typed := drecDTypedT_of_absent (by decide) }

/-- the constructors, the group list's head added last. -/
def vecCsT : List (GroupCtorT natEnvU 4 vecFamMember vecFamViewT) := [vecConsCtorT, vecNilCtorT]

/-- THE PREDICTION, which could have failed: the copy's builders (`RcicTypedGroup`) and L-K1's
    derivation give the same types at an INDEXED family — the constructors' (a result index per
    constructor, a recursive field at an index) and the AnySort recursor's (the motive over the index
    and the major, the induction hypothesis at the field's index). -/
theorem vecBuilt_eq_stored :
    vecNilMember.mtype = ctorTypeT 4 (canonLevels 0) vecFamViewT.params [] [.const 1 []] ∧
    vecConsMember.mtype =
      ctorTypeT 4 (canonLevels 0) vecFamViewT.params
        [.plain (.const 0 []) (.succ .zero), .plain (.bvar 1) (.succ .zero), .drec [.bvar 1]]
        [.app (.const 2 []) (.bvar 1)] ∧
    vecRecMemberU.mtype = groupRecTypeT vecCsT .anySort :=
  ⟨rfl, rfl, rfl⟩

/-- the recursor: AnySort, its stored type the one built from the views, by `rfl`. -/
def vecRecT : GroupRecT natEnvU 4 vecFamMember vecFamViewT vecCsT where
  member := vecRecMemberU
  hcls := rfl
  hnobody := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := fun _ => rfl
  u := vecRecTypeTyT.1
  hT := vecRecTypeTyT.2
  hlvl := rfl

/-! ## (6) the group in the copy's scope, and the bridge -/

/-- the structured views give the group's members, and the group meets both profiles: its index `N`
    lives at `Sort 1`, no larger than the family's sort (the small-index profile at a real index), and
    it is a `Type` family. -/
def vecInScopeT :
    GroupInScopeT natEnvU 4 vecFamMember [(5, vecNilMember), (6, vecConsMember)] 7 vecRecMemberU where
  fv := vecFamViewT
  htel := .cons [] _ _ _ (.sort [] (.succ .zero)) (.cons _ _ _ [] (natConstTyT rfl) (.nil _))
  cs := vecCsT
  hctors := rfl
  hlayout := rfl
  grec := vecRecT
  hrr := rfl
  hrm := rfl
  hprof := ⟨fun v hv ρ x y hx hy _ => by
      have hv' := List.mem_singleton.mp hv
      subst hv'
      have h1 : (1 : Nat) = x := Option.some.inj hx
      have h2 : (1 : Nat) = y := Option.some.inj hy
      subst h1
      subst h2
      exact Nat.le_refl 1,
    fun h _ => absurd (h fun _ => 0) (by decide)⟩
  hpb := by decide
  hsnd := by decide

theorem vecEnvUWfT_inScope : vecEnvUWfT.InScope := ⟨natEnvUWfT_inScope, ⟨vecInScopeT⟩⟩

theorem pin_envWfT_vecU : Nonempty (EnvWfT vecEnvUT) := ⟨vecEnvUWfT⟩

open Ann in
/-- the environment bridge applies at Nat-then-Vec: conditional on arc D's two typings, like the
    bridge.  Phase-2B: no `CorrCertsBelow` premise — `main`'s `annEnvA_of_envWfT_inScope`
    discharges `AnnEnvA` from `EnvWfT` + `InScope` alone; the certificate is not what the
    bridge consumes.  The premise survives instead on the TYPED-ι-route siblings
    (`Ann.hasTyT_iota_srT`, `iotaPreserveTT`), where it is the sound gate —
    and at `vecEnvUT` it is REFUTED (`not_corrCertsBelow_vecEnvUT` below, via the
    `vecOnlyEnvU` deficient sub-env), so the typed ι route — unlike the legacy one — is
    genuinely unavailable at this environment even though the environment itself is
    well-formed and in scope. -/
theorem vecEnvU_annotated (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) :
    ∃ EA : ResolvedEnvA, eraseEnv EA = vecEnvUT ∧ AnnEnvA EA :=
  (annEnvA_of_envWfT_inScope hT1 hT2 vecEnvUWfT vecEnvUWfT_inScope).imp fun _ h => ⟨h.1, h.2.1⟩

/-! ## (7) the corrected ι statement, on both judgments -/

private def happVT {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT vecEnvUT 1 Γ f (.pi A B)) (ha : HasTyT vecEnvUT 1 Γ a A) :
    HasTyT vecEnvUT 1 Γ (.app f a) (instantiate0 a B) :=
  .app Γ f a A B hf ha

/-- `vcons`'s reduct has the corrected type in the TYPED judgment, with no conversion step: the
    statement L-K1's clause now makes is one the typed root can discharge. -/
def vecConsIotaTyT : HasTyT vecEnvUT 1 vecConsCtx vecConsRhs vecConsLhs := by
  have htl : HasTyT vecEnvUT 1 vecConsCtx (.bvar 0) (lift 0 1 vecDomTl) := .bvar vecConsCtx 0 _ rfl
  have hhd : HasTyT vecEnvUT 1 vecConsCtx (.bvar 1) (lift 0 2 vecDomHd) := .bvar vecConsCtx 1 _ rfl
  have hn : HasTyT vecEnvUT 1 vecConsCtx (.bvar 2) (lift 0 3 vecDomN) := .bvar vecConsCtx 2 _ rfl
  have hMc : HasTyT vecEnvUT 1 vecConsCtx (.bvar 4) (lift 0 5 vecMinorCons) := .bvar vecConsCtx 4 _ rfl
  have hMn : HasTyT vecEnvUT 1 vecConsCtx (.bvar 5) (lift 0 6 vecMinorNil) := .bvar vecConsCtx 5 _ rfl
  have hP : HasTyT vecEnvUT 1 vecConsCtx (.bvar 6) (lift 0 7 vecDomP) := .bvar vecConsCtx 6 _ rfl
  have hA : HasTyT vecEnvUT 1 vecConsCtx (.bvar 7) (lift 0 8 vecDomA) := .bvar vecConsCtx 7 _ rfl
  have hRec0 : HasTyT vecEnvUT 1 vecConsCtx vecRecHead (instantiateLevels [.param 0] vecRecTypeU) :=
    .const vecConsCtx 7 [.param 0] vecRecMemberU rfl rfl rfl
  exact happVT (happVT (happVT (happVT hMc hn) hhd) htl)
    (happVT (happVT (happVT (happVT (happVT (happVT hRec0 hA) hP) hMn) hMc) hn) htl)

/-- `vnil`'s reduct, the minor, has the corrected type in the typed judgment too. -/
def vecNilIotaTyT : HasTyT vecEnvUT 1 vecNilCtx (.bvar 2) vecNilLhs := .bvar vecNilCtx 2 vecNilLhs rfl

/-- the statement before M3-e-5 at `vcons`: the motive at the index binder `i` (`bvar 3`), not at the
    result index `succ n`. -/
def vecConsOldLhs : Expr Nat :=
  .app (.app (.bvar 6) (.bvar 3)) (foldApps (.const 6 []) [.bvar 7, .bvar 2, .bvar 1, .bvar 0])

/-- TOOTH: at an indexed family the correction is not vacuous. The old statement and the corrected one
    are different terms (they coincide without indices, which is why the Nat, `True` and List pins
    could not see the defect). -/
theorem vecIota_indexSensitive : vecConsOldLhs ≠ vecConsLhs := by decide

/-- why `main` accepted the old statement: untyped conversion is total (R-ConvCollapse), so the
    reduct retypes to the old statement, as it retypes to anything. That acceptance carried no
    information about the clause. -/
def vecConsOldLhs_mainAccepts : HasTy vecEnvUT 1 vecConsCtx vecConsRhs vecConsOldLhs :=
  UntypedConvCollapse.retypeAny vecConsIotaTyU _

/-! ## (8) the deficient sub-environment: the certificate is not derivable

`vecEnvUT` is a well-scoped environment (`vecEnvUWfT`, `vecEnvUWfT_inScope`), and yet
`CorrCertsBelow vecEnvUT` is FALSE.  The scoped certificate quantifies over ALL
sub-environments (`EnvSub`, no well-formedness gate), and `vecOnlyEnvU` below is one where
the `vnil` ι-witness exists but `constsMemberFuel` fails: the witness's stored result
`Vec A zero` names `.const 1` (`zero`), and `vecOnlyEnvU` omits member `1`.

This is the Phase-1 measurement for the OPTION-(A) repair: the deficient prefix is a real
sub-env of the ambient well-formed env, so `hC : CorrCertsBelow vecEnvUT` is not merely
underivable — it is REFUTABLE.  `corrCertsBelow_of_envWfT` is FALSE at the exact pin
environment (`corrCertsBelow_of_envWfT_isFalse`), and `vecOnlyEnvU` itself is not `EnvWfT`
(its family's stored type names `.const 0`, `N`, also absent — `hasTyT_constsIn` refutes
the `GroupMembersT` typing premise), so the deficiency is not a scoping gap the
environment judgment could seal: the certificate's sub-env quantifier bites exactly where
`EnvWfT` cannot look. -/

/-- `{4 : Vec, 5 : vnil, 7 : Vec.rec}` — the Vec group's recursor spine with neither its
    Nat prefix (`0`–`3`) nor `vcons` (`6`).  Every member is `vecEnvUT`'s, so this is an
    `EnvSub` of it. -/
def vecOnlyEnvU : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv emptyEnv 4 vecFamMember) 5 vecNilMember) 7 vecRecMemberU

theorem vecOnlyEnvU_mem (c : Nat) :
    vecOnlyEnvU.members c =
      if c = 7 then some vecRecMemberU
      else if c = 5 then some vecNilMember
      else if c = 4 then some vecFamMember
      else none := rfl

theorem envSub_vecOnlyU_vecEnvUT : Ann.EnvSub vecOnlyEnvU vecEnvUT := by
  intro r m h
  rw [vecOnlyEnvU_mem] at h
  by_cases h7 : r = 7
  · subst h7
    rw [if_pos rfl] at h
    cases h
    rfl
  · rw [if_neg h7] at h
    by_cases h5 : r = 5
    · subst h5
      rw [if_pos rfl] at h
      cases h
      rfl
    · rw [if_neg h5] at h
      by_cases h4 : r = 4
      · subst h4
        rw [if_pos rfl] at h
        cases h
        rfl
      · rw [if_neg h4] at h
        cases h

/-- `Vec.rec A P mn mc i (vnil A)` is an `IotaWitness` of `vecOnlyEnvU`: the three refs the
    witness needs — family `4`, ctor `5`, recursor `7` — all resolve there. -/
def wVnilOnlyU : IotaWitness vecOnlyEnvU where
  recRef := 7
  ctorRef := 5
  ls := [.param 0]
  lsC := []
  recMember := vecRecMemberU
  ctorMember := vecNilMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [vecParam, vecMotiveArg, vecMinorN, vecMinorC, vecMajorIdx]
  fields := []
  ctorParams := [vecParam]
  kinds := []
  minor := vecMinorN
  hlen := rfl
  familyRef := 4
  famMember := vecFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 1
  nMinors := 2
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort (.succ .zero)]
  ctorResult := .app (.app (.const 4 []) (.bvar 0)) (.const 1 [])
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms :=
    [ .sort (.succ .zero)
    , .pi (.const 0 [])
        (.pi (.app (.app (.const 4 []) (.bvar 1)) (.bvar 0)) (.sort (.param 0)))
    , .app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))
    , .pi (.const 0 [])
        (.pi (.bvar 3)
          (.pi (.app (.app (.const 4 []) (.bvar 4)) (.bvar 1))
            (.pi (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))
              (.app (.app (.bvar 5) (.app (.const 2 []) (.bvar 3)))
                (.app (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3))
                  (.bvar 2)) (.bvar 1))))))
    , .const 0 []
    , .app (.app (.const 4 []) (.bvar 4)) (.bvar 0) ]
  recBody := .app (.app (.bvar 4) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .app (.app (.const 4 []) vecParam) (.const 1 [])
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- the stability conjunct fails: `vnil`'s raw field telescope is its result `Vec A zero`,
    which names `.const 1` — `vecOnlyEnvU` has no member `1`, so `constsMemberFuel` is
    `false` at EVERY fuel (the failure is an omitted member, not fuel exhaustion). -/
theorem iotaWitnessStableB_wVnilOnlyU (fuel : Nat) :
    iotaWitnessStableB vecOnlyEnvU fuel
      (wVnilOnlyU.ctorDoms.drop wVnilOnlyU.nparams)
      (fieldBvars wVnilOnlyU.fields.length)
      (lift 0 (wVnilOnlyU.fields.length + 1 + wVnilOnlyU.nMinors + wVnilOnlyU.nindices)
        (ctorFieldTelRaw wVnilOnlyU.nparams wVnilOnlyU.ctorDoms
          wVnilOnlyU.ctorResult)) = false := by
  cases fuel with
  | zero =>
      simp [iotaWitnessStableB, wVnilOnlyU, List.drop, fieldBvars, List.range,
        List.reverse, List.map, ctorFieldTelRaw, List.foldr, lift, List.all,
        constsMemberFuel, vecOnlyEnvU, extendEnv, emptyEnv, transparent, vecFamMember,
        vecRecMemberU, vecNilMember]
  | succ n =>
      simp [iotaWitnessStableB, wVnilOnlyU, List.drop, fieldBvars, List.range,
        List.reverse, List.map, ctorFieldTelRaw, List.foldr, lift, List.all,
        constsMemberFuel, vecOnlyEnvU, extendEnv, emptyEnv, transparent, vecFamMember,
        vecRecMemberU, vecNilMember]

/-- the recognizer fails on `wVnilOnlyU` at every fuel: the stability conjunct above is the
    second `&&`-factor, so the whole check is `false`. -/
theorem iotaWitnessSB_wVnilOnlyU (fuel : Nat) :
    iotaWitnessSB wVnilOnlyU fuel = false := by
  simp only [iotaWitnessSB, iotaWitnessStableB_wVnilOnlyU, Bool.and_false,
    Bool.false_and]

/-- `vecOnlyEnvU` has an ι-witness whose adaptation fails at every fuel: the erasure
    certificate is uninhabited there. -/
theorem not_envCorrEraseCert_vecOnlyEnvU :
    ¬ Ann.EnvCorrEraseCert vecOnlyEnvU := by
  intro hC
  obtain ⟨fuel, hfuel⟩ := hC wVnilOnlyU
  rw [iotaWitnessSB_wVnilOnlyU] at hfuel
  exact absurd hfuel (by decide)

/-- THE MEASUREMENT: `CorrCertsBelow vecEnvUT` is FALSE.  The certificate's sub-env
    quantifier reaches `vecOnlyEnvU`, where `vnil`'s witness exists but its stored result
    names the omitted `zero`. -/
theorem not_corrCertsBelow_vecEnvUT : ¬ Ann.CorrCertsBelow vecEnvUT := by
  intro hC
  exact not_envCorrEraseCert_vecOnlyEnvU
    (hC vecOnlyEnvU envSub_vecOnlyU_vecEnvUT).1

/-- the Phase-2A theorem is refuted at the exact pin environment: `vecEnvUT` IS
    `EnvWfT + InScope` (`vecEnvUWfT`, `vecEnvUWfT_inScope`) and its certificate is FALSE —
    `CorrCertsBelow` cannot be derived from well-formedness and scope. -/
theorem corrCertsBelow_of_envWfT_isFalse :
    ¬ (∀ {E : ResolvedEnv} (hW : EnvWfT E), hW.InScope → Ann.CorrCertsBelow E) := by
  intro h
  exact not_corrCertsBelow_vecEnvUT (h vecEnvUWfT vecEnvUWfT_inScope)

/-! ### cc #6293's `vecOnlyEnvU` experiment — the legacy reduct at the redex type

cc's ruling on `EnvCorrEraseCert`: at `vecOnlyEnvU`, build or refute the typing
of the legacy `DerivedIota` reduct (the `iotaRhsOf` minor-application form) AT
THE REDEX TYPE; if refuted, the plain kernel types ι only via
`DerivedIotaU.ofUS`. Both directions pin, and the answer is REFUTED — though
instructively split:

* `pin_iotaRhs_wVnilOnlyU_typed` — the reduct alone DOES type: `fields = []`
  collapses `iotaRhsOf wVnilOnlyU` to the bare minor `.const 5 []` (`vnil`
  unapplied), and member `5` is present. So the reduct is not untypeable in
  itself — it types at its own stored type `vecNilType`.
* `pin_not_hasTyT_iotaLhs_wVnilOnlyU` — the redex can NEVER be typed at
  `vecOnlyEnvU`: its application spine names `.const 6` (`vcons`), `.const 2`
  (`succ`), `.const 1` (`zero`), `.const 0` (`N`), all absent — `hasTyT_constsIn`
  refutes every `HasTyT (iotaLhsOf wVnilOnlyU) S`.

So "the reduct typed AT THE REDEX TYPE" is refuted vacuously: there is no
redex typing for the reduct to match. Per the ruling, the plain kernel's ι-SR
is stated over `DerivedIotaU`-style typed roots — `.ofUS`, the schema route —
with the legacy minor-app form covered only where the redex itself is typable
and the witness adapts (`∃ fuel, iotaWitnessSB w fuel = true`). -/

/-- the reduct types at its own stored type (BUILD side): `iotaRhsOf
    wVnilOnlyU` reduces to `.const 5 []` since `vnil` has no fields. -/
def pin_iotaRhs_wVnilOnlyU_typed {n : Nat} :
    HasTyT vecOnlyEnvU n [] (iotaRhsOf wVnilOnlyU) vecNilType := by
  exact .const _ _ _ vecNilMember rfl rfl rfl

/-- the redex cannot be typed at `vecOnlyEnvU` (REFUTE side): `iotaLhsOf`
    expands to a `foldApps` spine whose fourth argument is `.const 6` —
    `vcons` — absent from the environment; `hasTyT_constsIn` forbids it. -/
theorem pin_not_hasTyT_iotaLhs_wVnilOnlyU {n : Nat} {Γ : LCtx} {S : Expr Nat}
    (h : HasTyT vecOnlyEnvU n Γ (iotaLhsOf wVnilOnlyU) S) : False := by
  have hc := hasTyT_constsIn h
  obtain ⟨m, hm⟩ := hc.1.1.2
  have h6 : vecOnlyEnvU.members 6 = none := rfl
  rw [h6] at hm
  exact Option.noConfusion hm

/-- the ι-SR output shape for this witness is vacuous at `vecOnlyEnvU`: the
    premise `HasTyT lhs S` is uninstantiable, so there is no `B` with the
    reduct typed at a `S`-convertible type. The plain kernel's ι-typing at
    deficient sub-envs therefore exists only via `DerivedIotaU.ofUS`. -/
theorem pin_iota_reduct_at_redex_type_refuted {n : Nat} {Γ : LCtx}
    {S B : Expr Nat}
    (hl : HasTyT vecOnlyEnvU n Γ (iotaLhsOf wVnilOnlyU) S)
    (_hr : HasTyT vecOnlyEnvU n Γ (iotaRhsOf wVnilOnlyU) B ×'
      TyConvT vecOnlyEnvU n Γ S B) : False :=
  pin_not_hasTyT_iotaLhs_wVnilOnlyU hl

/-- `ConstsIn` is monotone under the member-inclusion of an extension. -/
theorem constsIn_mono {E E' : ResolvedEnv}
    (hsub : ∀ r m, E.members r = some m → E'.members r = some m) :
    ∀ {e : Expr Nat}, ConstsIn E e → ConstsIn E' e
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .lit 0, h => let ⟨m, hm⟩ := h; ⟨m, hsub 1 m hm⟩
  | .lit (_ + 1), h =>
      let ⟨⟨m1, h1⟩, m2, h2⟩ := h
      ⟨⟨m1, hsub 1 m1 h1⟩, m2, hsub 2 m2 h2⟩
  | .const r _, ⟨m, hm⟩ => ⟨m, hsub r m hm⟩
  | .app _ _, ⟨hf, ha⟩ => ⟨constsIn_mono hsub hf, constsIn_mono hsub ha⟩
  | .lam _ _, ⟨hA, hb⟩ => ⟨constsIn_mono hsub hA, constsIn_mono hsub hb⟩
  | .pi _ _, ⟨hA, hb⟩ => ⟨constsIn_mono hsub hA, constsIn_mono hsub hb⟩
  | .letE _ _ _, ⟨hA, hv, hb⟩ =>
      ⟨constsIn_mono hsub hA, constsIn_mono hsub hv, constsIn_mono hsub hb⟩

/-- a fresh extension keeps the base's members. -/
theorem extendEnv_envSub {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hfresh : E.members r = none) :
    ∀ r' m', E.members r' = some m' → (extendEnv E r m).members r' = some m' := by
  intro r' m' hm'
  show (if r' = r then some m else E.members r') = some m'
  rw [if_neg (show r' ≠ r from fun he => by
    subst he; rw [hm'] at hfresh; cases hfresh)]
  exact hm'

/-- a member chain only grows the environment: the base's members are the result's. -/
theorem groupMembersT_mono {S E l E'}
    (h : GroupMembersT S E l E') :
    ∀ r m, E.members r = some m → E'.members r = some m := by
  induction h with
  | nil E => intro r m hm; exact hm
  | cons E r m rest E' hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
      intro r' m' hm'
      apply ih
      exact extendEnv_envSub hfresh r' m' hm'

/-- a member of the chain-built env was either added by the chain or inherited from the
    base. -/
theorem groupMembersT_mem_cases {S E l E'}
    (h : GroupMembersT S E l E') :
    ∀ {r' m'}, E'.members r' = some m' →
      (r', m') ∈ l ∨ E.members r' = some m' := by
  induction h with
  | nil E =>
      intro r' m' hm'
      exact Or.inr hm'
  | cons E r m rest E' hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
      intro r' m' hm'
      rcases ih hm' with hmem | hE''
      · exact Or.inl (List.mem_cons_of_mem _ hmem)
      · by_cases hr : r' = r
        · subst hr
          have hself : (extendEnv E r' m).members r' = some m := if_pos rfl
          rw [hself] at hE''
          have hme : m = m' := Option.some.inj hE''
          subst hme
          exact Or.inl (List.mem_cons_self _ _)
        · right
          have hxx : (extendEnv E r m).members r' = E.members r' := by
            show (if r' = r then some m else E.members r') = E.members r'
            rw [if_neg hr]
          rw [← hxx]
          exact hE''

/-- each member the chain adds has its stored type's constants inside the final env: the
    cons types the member in the env built so far (`hT`), which is a sub-env of the
    result. -/
theorem groupMembersT_constsIn_of_mem {S E l E'}
    (h : GroupMembersT S E l E') :
    ∀ {r m}, (r, m) ∈ l → ConstsIn E' m.mtype := by
  induction h with
  | nil E =>
      intro r m hmem
      cases hmem
  | cons E r m rest E' hfresh _ _ _ _ _ _ _ _ u hT _ _ hrest ih =>
      intro r' m' hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        exact constsIn_mono
          (fun r'' m'' hm' =>
            groupMembersT_mono hrest r'' m'' (extendEnv_envSub hfresh r'' m'' hm'))
          (hasTyT_constsIn hT)
      · exact ih htail

/-- every member of an `EnvWfT` environment has its stored type's constants inside the
    environment: the member was typed when it was admitted (`hT`/`hA`), and the env only
    grows after. -/
theorem envWfT_constsIn {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ r m, E.members r = some m → ConstsIn E m.mtype := by
  induction hW
  · -- empty
    intro r m hm
    cases hm
  · -- axiom
    rename_i E r A u hE hfresh hA hcl hlvl ih
    intro r' m' hm'
    show ConstsIn (extendEnv E r ⟨.axiomM, 0, A, none⟩) m'.mtype
    by_cases hr : r' = r
    · subst r'
      have hm : (extendEnv E r ⟨.axiomM, 0, A, none⟩).members r =
          some ⟨.axiomM, 0, A, none⟩ := if_pos rfl
      rw [hm] at hm'
      cases hm'
      exact constsIn_mono (extendEnv_envSub hfresh) (hasTyT_constsIn hA)
    · have hE' : E.members r' = some m' := by
        have h : (extendEnv E r ⟨.axiomM, 0, A, none⟩).members r' =
            E.members r' := by
          show (if r' = r then some ⟨.axiomM, 0, A, none⟩ else E.members r') =
            E.members r'
          rw [if_neg hr]
        rw [← h]; exact hm'
      exact constsIn_mono (extendEnv_envSub hfresh) (ih r' m' hE')
  · -- definition
    rename_i E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv ih
    intro r' m' hm'
    show ConstsIn (extendEnv E r ⟨.definitionM, 0, A, some v⟩) m'.mtype
    by_cases hr : r' = r
    · subst r'
      have hm : (extendEnv E r ⟨.definitionM, 0, A, some v⟩).members r =
          some ⟨.definitionM, 0, A, some v⟩ := if_pos rfl
      rw [hm] at hm'
      cases hm'
      exact constsIn_mono (extendEnv_envSub hfresh) (hasTyT_constsIn hA)
    · have hE' : E.members r' = some m' := by
        have h : (extendEnv E r ⟨.definitionM, 0, A, some v⟩).members r' =
            E.members r' := by
          show (if r' = r then some ⟨.definitionM, 0, A, some v⟩ else
              E.members r') = E.members r'
          rw [if_neg hr]
        rw [← h]; exact hm'
      exact constsIn_mono (extendEnv_envSub hfresh) (ih r' m' hE')
  · -- thm
    rename_i E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp ih
    intro r' m' hm'
    show ConstsIn (extendEnv E r ⟨.theoremM, 0, A, some p⟩) m'.mtype
    by_cases hr : r' = r
    · subst r'
      have hm : (extendEnv E r ⟨.theoremM, 0, A, some p⟩).members r =
          some ⟨.theoremM, 0, A, some p⟩ := if_pos rfl
      rw [hm] at hm'
      cases hm'
      exact constsIn_mono (extendEnv_envSub hfresh) (hasTyT_constsIn hA)
    · have hE' : E.members r' = some m' := by
        have h : (extendEnv E r ⟨.theoremM, 0, A, some p⟩).members r' =
            E.members r' := by
          show (if r' = r then some ⟨.theoremM, 0, A, some p⟩ else
              E.members r') = E.members r'
          rw [if_neg hr]
        rw [← h]; exact hm'
      exact constsIn_mono (extendEnv_envSub hfresh) (ih r' m' hE')
  · -- opaque
    rename_i E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv ih
    intro r' m' hm'
    show ConstsIn (extendEnv E r ⟨.opaqueM, 0, A, some v⟩) m'.mtype
    by_cases hr : r' = r
    · subst r'
      have hm : (extendEnv E r ⟨.opaqueM, 0, A, some v⟩).members r =
          some ⟨.opaqueM, 0, A, some v⟩ := if_pos rfl
      rw [hm] at hm'
      cases hm'
      exact constsIn_mono (extendEnv_envSub hfresh) (hasTyT_constsIn hA)
    · have hE' : E.members r' = some m' := by
        have h : (extendEnv E r ⟨.opaqueM, 0, A, some v⟩).members r' =
            E.members r' := by
          show (if r' = r then some ⟨.opaqueM, 0, A, some v⟩ else
              E.members r') = E.members r'
          rw [if_neg hr]
        rw [← h]; exact hm'
      exact constsIn_mono (extendEnv_envSub hfresh) (ih r' m' hE')
  · -- group
    rename_i E f fm ctors rr rm E' hE hfam hctors hrec hmem ih
    intro r' m' hm'
    rcases groupMembersT_mem_cases hmem hm' with hchain | hE'
    · exact groupMembersT_constsIn_of_mem hmem hchain
    · exact constsIn_mono (groupMembersT_mono hmem) (ih r' m' hE')

/-- `vecOnlyEnvU` is NOT well-formed either: its only `.inductiveM` member is `vecFamMember`
    at `4`, whose stored `Vec : Sort 1 → N → Sort 1` names `.const 0` (`N`) — absent from
    every sub-env of `vecOnlyEnvU`.  The deficiency is exactly what `EnvWfT`'s member-scope
    check refuses, which is why it cannot be reached from `vecEnvUWfT`: the certificate
    quantifier and the environment judgment look at different environments. -/
theorem not_envWfT_vecOnlyEnvU (hW : EnvWfT vecOnlyEnvU) : False := by
  have hc := envWfT_constsIn hW 4 vecFamMember rfl
  obtain ⟨m, hm⟩ := hc.2.1
  cases hm

end Rcic.Declarative

#print axioms Rcic.Declarative.vecFamAdmittedU
#print axioms Rcic.Declarative.vecNilAdmittedU
#print axioms Rcic.Declarative.vecConsAdmittedU
#print axioms Rcic.Declarative.vecRecAdmittedU
#print axioms Rcic.Declarative.vecEnvUWfT
#print axioms Rcic.Declarative.pin_envWfT_vecU
#print axioms Rcic.Declarative.vecBuilt_eq_stored
#print axioms Rcic.Declarative.vecEnvUWfT_inScope
#print axioms Rcic.Declarative.vecEnvU_annotated
#print axioms Rcic.Declarative.vecConsIotaTyT
#print axioms Rcic.Declarative.vecNilIotaTyT
#print axioms Rcic.Declarative.vecIota_indexSensitive
#print axioms Rcic.Declarative.wVnilOnlyU
#print axioms Rcic.Declarative.iotaWitnessSB_wVnilOnlyU
#print axioms Rcic.Declarative.not_envCorrEraseCert_vecOnlyEnvU
#print axioms Rcic.Declarative.not_corrCertsBelow_vecEnvUT
#print axioms Rcic.Declarative.corrCertsBelow_of_envWfT_isFalse
#print axioms Rcic.Declarative.envWfT_constsIn
#print axioms Rcic.Declarative.not_envWfT_vecOnlyEnvU
#print axioms Rcic.Declarative.vecConsOldLhs_mainAccepts
