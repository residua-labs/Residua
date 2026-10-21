/-
L-K1 segment 2. Nat and List prefixes admitted one member at a time.

The full-prefix views in `RcicIndGroupAdmitted` are not these steps:
`PolicyFamilyView` is indexed by the environment the member is added to.
`natRecMember` / `listRecMember` store a fixed `Sort 1` motive at arity 0.
05 §11 does not derive that signature, so this file stops at the
constructor prefix.
-/
import rcic.RcicFixtures

namespace Rcic.Declarative

private theorem slot_irrefl {k c : Nat} (hl : k < c) (hr : c < k + 1) : False :=
  Nat.lt_irrefl k (Nat.lt_of_lt_of_le hl (Nat.le_of_lt_succ hr))

/-! ## Nat prefix -/

def natFamOnly : ResolvedEnv := extendEnv emptyEnv 0 natFamMember

def natFamZero : ResolvedEnv := extendEnv natFamOnly 1 natZeroMember

theorem natFamOnly_members (c : Nat) :
    natFamOnly.members c = if c = 0 then some natFamMember else none := rfl

theorem natFamZero_members (c : Nat) :
    natFamZero.members c =
      if c = 1 then some natZeroMember
      else if c = 0 then some natFamMember
      else none := rfl

def natFamView (E : ResolvedEnv) (h : E.members 0 = some natFamMember) :
    PolicyFamilyView E where
  ref := 0
  member := natFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def natZeroView (E : ResolvedEnv) (h : E.members 0 = some natFamMember) :
    PolicyConstructorView E (natFamView E h) natZeroMember where
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
  noFamilyInIndices := fun _ hx => nomatch hx

private def natSuccFieldTy (E : ResolvedEnv) (h : E.members 0 = some natFamMember) :
    HasTy E 0 [] (.const 0 []) (.sort (.succ .zero)) :=
  HasTy.const [] 0 [] natFamMember h rfl (fun _ hx => nomatch hx)

def natSuccView (E : ResolvedEnv) (h : E.members 0 = some natFamMember) :
    PolicyConstructorView E (natFamView E h) natSuccMember where
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
      have hlen : ([] ++ [(.const 0 [] : Expr Nat)]).length = 1 := rfl
      have hlt : j.val < 1 := by simpa [hlen] using j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simpa [hj, policyPrefixContext] using natSuccFieldTy E h
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

theorem natZeroBefore : CtorBeforeRecursors natFamOnly natZeroMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [natFamOnly_members] at hm
  by_cases h0 : rr = 0
  · rw [if_pos h0] at hm
    cases hm
    unfold natFamMember at hk
    cases hk
  · rw [if_neg h0] at hm
    cases hm

theorem natZeroContig : CtorContiguous natFamOnly 1 natZeroMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact False.elim (slot_irrefl hl hr)
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [natFamOnly_members] at hm
    by_cases h0 : c = 0
    · rw [if_pos h0] at hm
      cases hm
      unfold natFamMember at hc
      cases hc
    · rw [if_neg h0] at hm
      cases hm

theorem natSuccBefore : CtorBeforeRecursors natFamZero natSuccMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [natFamZero_members] at hm
  by_cases h1 : rr = 1
  · rw [if_pos h1] at hm
    cases hm
    unfold natZeroMember at hk
    cases hk
  · by_cases h0 : rr = 0
    · rw [if_neg h1, if_pos h0] at hm
      cases hm
      unfold natFamMember at hk
      cases hk
    · rw [if_neg h1, if_neg h0] at hm
      cases hm

theorem natSuccContig : CtorContiguous natFamZero 2 natSuccMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 1 := by omega
    subst hc
    exact ⟨natZeroMember, by rw [natFamZero_members]; rfl, rfl, rfl⟩
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [natFamZero_members] at hm
    by_cases h1 : c = 1
    · subst h1
      exact ⟨by decide, by decide⟩
    · by_cases h0 : c = 0
      · rw [if_neg h1, if_pos h0] at hm
        cases hm
        unfold natFamMember at hc
        cases hc
      · rw [if_neg h1, if_neg h0] at hm
        cases hm

private theorem natZeroUniverse (E : ResolvedEnv) (h : E.members 0 = some natFamMember) :
    FieldUniverseAdmitted (natZeroView E h) :=
  fun j => j.elim0

private theorem natSuccUniverse (E : ResolvedEnv) (h : E.members 0 = some natFamMember) :
    FieldUniverseAdmitted (natSuccView E h) := by
  intro j
  have hlen : (natSuccView E h).fields.length = 1 := rfl
  have hlt : j.val < 1 := by simpa [hlen] using j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

private theorem natZeroFields (E : ResolvedEnv) (h : E.members 0 = some natFamMember) :
    CtorFieldsPermitted (natZeroView E h) :=
  fun j => j.elim0

private theorem natSuccFields : CtorFieldsPermitted (natSuccView natFamZero rfl) := by
  intro j
  have hlen : (natSuccView natFamZero rfl).fields.length = 1 := rfl
  have hlt : j.val < 1 := by simpa [hlen] using j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact ⟨.recursive 0, 4, [], rfl⟩

def natFamAdmitted : IndGroupAdmitted emptyEnv 0 natFamMember :=
  .family rfl (natFamView natFamOnly rfl) rfl rfl (Or.inr uniformType_succ_zero)

def natZeroAdmitted : IndGroupAdmitted natFamOnly 1 natZeroMember :=
  .constructor (natFamView natFamOnly rfl) (natZeroView natFamOnly rfl)
    rfl natZeroBefore natZeroContig (natZeroUniverse _ rfl) (natZeroFields _ rfl)

def natSuccAdmitted : IndGroupAdmitted natFamZero 2 natSuccMember :=
  .constructor (natFamView natFamZero rfl) (natSuccView natFamZero rfl)
    rfl natSuccBefore natSuccContig (natSuccUniverse _ rfl) natSuccFields

def natEnvWfPrefixAt (n : Nat) : EnvWf natEnvPrefix n :=
  .indMember _ 2 natSuccMember
    (.indMember _ 1 natZeroMember
      (.indMember _ 0 natFamMember (.empty n) rfl (Or.inl rfl) rfl
        (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
        (fun h => absurd h (by decide)) natFamAdmitted)
      rfl (Or.inr (Or.inl rfl)) rfl (fun _ => rfl)
      (fun h => absurd h (by decide)) rfl rfl rfl
      (fun h => absurd h (by decide)) natZeroAdmitted)
    rfl (Or.inr (Or.inl rfl)) rfl (fun _ => rfl)
    (fun h => absurd h (by decide)) rfl rfl rfl
    (fun h => absurd h (by decide)) natSuccAdmitted

def natEnvWfPrefix : EnvWf natEnvPrefix 1 := natEnvWfPrefixAt 1

theorem pin_envWf_natPrefix : Nonempty (EnvWf natEnvPrefix 1) :=
  ⟨natEnvWfPrefix⟩

/-! ## List prefix (`nparams = 1`, no indices) -/

def listParamDom : Expr Nat := .sort (.succ .zero)
def listHdField : Expr Nat := .bvar 0
def listTlField : Expr Nat := .app (.const 0 []) (.bvar 1)
def listConsDoms : List (Expr Nat) := [listParamDom, listHdField, listTlField]

def listFamOnly : ResolvedEnv := extendEnv emptyEnv 0 listFamMember

def listFamNil : ResolvedEnv := extendEnv listFamOnly 1 listNilMember

theorem listFamOnly_members (c : Nat) :
    listFamOnly.members c = if c = 0 then some listFamMember else none := rfl

theorem listFamNil_members (c : Nat) :
    listFamNil.members c =
      if c = 1 then some listNilMember
      else if c = 0 then some listFamMember
      else none := rfl

def listFamDomains (E : ResolvedEnv) :
    PolicyTelescopeTyping E 0 [listParamDom] where
  levels := fun _ => .succ (.succ .zero)
  bounded := fun _ => rfl
  hasType := fun j => by
    have hlt := j.isLt
    simp only [List.length_singleton] at hlt
    have hv : j.val = 0 := by omega
    have hj : j = ⟨0, Nat.lt_succ_self 0⟩ := Fin.ext hv
    simpa [hj, policyPrefixContext] using
      (HasTy.sort [] (.succ .zero) : HasTy E 0 [] (.sort (.succ .zero)) _)

def listFamView (E : ResolvedEnv) (h : E.members 0 = some listFamMember) :
    PolicyFamilyView E where
  ref := 0
  member := listFamMember
  present := h
  hasClass := rfl
  parameters := [listParamDom]
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := listFamDomains E

def listNilView (E : ResolvedEnv) (h : E.members 0 = some listFamMember) :
    PolicyConstructorView E (listFamView E h) listNilMember where
  hasClass := rfl
  arity := rfl
  parameters := [listParamDom]
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := listFamDomains E
  parameterMirrors := fun i => by
    have hlt := i.isLt
    simp only [List.length_singleton] at hlt
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self 0⟩ := Fin.ext hv
    simp [hi, policyPrefixContext, listParamDom]
    exact Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

def listHdCtx : LCtx := [.assumption listParamDom]

def listTlCtx : LCtx :=
  [.assumption listHdField, .assumption listParamDom]

def listConsTlTy (E : ResolvedEnv) (h : E.members 0 = some listFamMember) :
    HasTy E 0 listTlCtx listTlField (.sort (.succ .zero)) :=
  HasTy.app listTlCtx (.const 0 []) (.bvar 1)
    (.sort (.succ .zero)) (.sort (.succ .zero))
    (HasTy.const listTlCtx 0 [] listFamMember h rfl (fun _ hx => nomatch hx))
    (HasTy.bvar listTlCtx 1 (.sort (.succ .zero)) rfl)

def listConsDomains (E : ResolvedEnv) (h : E.members 0 = some listFamMember) :
    PolicyTelescopeTyping E 0 listConsDoms where
  levels := fun j => if j.val = 0 then .succ (.succ .zero) else .succ .zero
  bounded := fun j => by
    by_cases h0 : j.val = 0
    · simp [h0]; rfl
    · simp [h0]; rfl
  hasType := fun j =>
    if h0 : j.val = 0 then by
      have hj : j = ⟨0, by simpa [h0] using j.isLt⟩ := Fin.ext h0
      simp [hj, policyPrefixContext, listConsDoms]
      exact HasTy.sort [] (.succ .zero)
    else if h1 : j.val = 1 then by
      have hj : j = ⟨1, by simpa [h1] using j.isLt⟩ := Fin.ext h1
      simp [hj, policyPrefixContext, listConsDoms, listParamDom, listHdCtx]
      exact HasTy.bvar listHdCtx 0 (.sort (.succ .zero)) rfl
    else by
      have hlt := j.isLt
      simp only [listConsDoms, List.length_cons, List.length_nil] at hlt
      have h2 : j.val = 2 := by omega
      have hj : j = ⟨2, by simpa [h2] using j.isLt⟩ := Fin.ext h2
      simp [hj, policyPrefixContext, listConsDoms, listParamDom, listHdField, listTlCtx]
      exact listConsTlTy E h

def listConsView (E : ResolvedEnv) (h : E.members 0 = some listFamMember) :
    PolicyConstructorView E (listFamView E h) listConsMember where
  hasClass := rfl
  arity := rfl
  parameters := [listParamDom]
  fields := [listHdField, listTlField]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := listConsDomains E h
  parameterMirrors := fun i => by
    have hlt := i.isLt
    simp only [List.length_singleton] at hlt
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self 0⟩ := Fin.ext hv
    simp [hi, policyPrefixContext, listParamDom]
    exact Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

theorem listNilBefore : CtorBeforeRecursors listFamOnly listNilMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [listFamOnly_members] at hm
  by_cases h0 : rr = 0
  · rw [if_pos h0] at hm
    cases hm
    unfold listFamMember at hk
    cases hk
  · rw [if_neg h0] at hm
    cases hm

theorem listNilContig : CtorContiguous listFamOnly 1 listNilMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact False.elim (slot_irrefl hl hr)
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [listFamOnly_members] at hm
    by_cases h0 : c = 0
    · rw [if_pos h0] at hm
      cases hm
      unfold listFamMember at hc
      cases hc
    · rw [if_neg h0] at hm
      cases hm

theorem listConsBefore : CtorBeforeRecursors listFamNil listConsMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [listFamNil_members] at hm
  by_cases h1 : rr = 1
  · rw [if_pos h1] at hm
    cases hm
    unfold listNilMember at hk
    cases hk
  · by_cases h0 : rr = 0
    · rw [if_neg h1, if_pos h0] at hm
      cases hm
      unfold listFamMember at hk
      cases hk
    · rw [if_neg h1, if_neg h0] at hm
      cases hm

theorem listConsContig : CtorContiguous listFamNil 2 listConsMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 1 := by omega
    subst hc
    exact ⟨listNilMember, by rw [listFamNil_members]; rfl, rfl, rfl⟩
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [listFamNil_members] at hm
    by_cases h1 : c = 1
    · subst h1
      exact ⟨by decide, by decide⟩
    · by_cases h0 : c = 0
      · rw [if_neg h1, if_pos h0] at hm
        cases hm
        unfold listFamMember at hc
        cases hc
      · rw [if_neg h1, if_neg h0] at hm
        cases hm

theorem listNilUniverse (E : ResolvedEnv) (h : E.members 0 = some listFamMember) :
    FieldUniverseAdmitted (listNilView E h) :=
  fun j => j.elim0

theorem listConsUniverse : FieldUniverseAdmitted (listConsView listFamNil rfl) := by
  intro j
  have hlen : (listConsView listFamNil rfl).fields.length = 2 := rfl
  have hlt : j.val < 2 := by simpa [hlen] using j.isLt
  have hc : j.val = 0 ∨ j.val = 1 := by omega
  rcases hc with h0 | h1
  · have hj : j = ⟨0, by decide⟩ := Fin.ext h0
    rw [hj]
    exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
  · have hj : j = ⟨1, by decide⟩ := Fin.ext h1
    rw [hj]
    exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem listHdAnalyzed :
    fieldAnalyze listFamNil 8 0 0 1 0 1 listHdField =
      .permitted .nonrecursive [] := rfl

theorem listTlAnalyzed :
    fieldAnalyze listFamNil 8 0 0 1 0 2 listTlField =
      .permitted (.recursive 0) [] := rfl

theorem listNilFields (E : ResolvedEnv) (h : E.members 0 = some listFamMember) :
    CtorFieldsPermitted (listNilView E h) :=
  fun j => j.elim0

theorem listConsFields : CtorFieldsPermitted (listConsView listFamNil rfl) := by
  intro j
  have hlen : (listConsView listFamNil rfl).fields.length = 2 := rfl
  have hlt : j.val < 2 := by simpa [hlen] using j.isLt
  have hc : j.val = 0 ∨ j.val = 1 := by omega
  rcases hc with h0 | h1
  · have hj : j = ⟨0, by decide⟩ := Fin.ext h0
    rw [hj]
    exact ⟨.nonrecursive, 8, [], listHdAnalyzed⟩
  · have hj : j = ⟨1, by decide⟩ := Fin.ext h1
    rw [hj]
    exact ⟨.recursive 0, 8, [], listTlAnalyzed⟩

def listFamAdmitted : IndGroupAdmitted emptyEnv 0 listFamMember :=
  .family rfl (listFamView listFamOnly rfl) rfl rfl (Or.inr uniformType_succ_zero)

def listNilAdmitted : IndGroupAdmitted listFamOnly 1 listNilMember :=
  .constructor (listFamView listFamOnly rfl) (listNilView listFamOnly rfl)
    rfl listNilBefore listNilContig (listNilUniverse _ rfl) (listNilFields _ rfl)

def listConsAdmitted : IndGroupAdmitted listFamNil 2 listConsMember :=
  .constructor (listFamView listFamNil rfl) (listConsView listFamNil rfl)
    rfl listConsBefore listConsContig listConsUniverse listConsFields

def listEnvWfPrefixAt (n : Nat) : EnvWf listEnvPrefix n :=
  .indMember _ 2 listConsMember
    (.indMember _ 1 listNilMember
      (.indMember _ 0 listFamMember (.empty n) rfl (Or.inl rfl) rfl
        (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
        (fun h => absurd h (by decide)) listFamAdmitted)
      rfl (Or.inr (Or.inl rfl)) rfl (fun _ => rfl)
      (fun h => absurd h (by decide)) rfl rfl rfl
      (fun h => absurd h (by decide)) listNilAdmitted)
    rfl (Or.inr (Or.inl rfl)) rfl (fun _ => rfl)
    (fun h => absurd h (by decide)) rfl rfl rfl
    (fun h => absurd h (by decide)) listConsAdmitted

def listEnvWfPrefix : EnvWf listEnvPrefix 1 := listEnvWfPrefixAt 1

theorem pin_envWf_listPrefix : Nonempty (EnvWf listEnvPrefix 1) :=
  ⟨listEnvWfPrefix⟩

end Rcic.Declarative
