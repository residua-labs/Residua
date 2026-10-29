import rcic.RcicF3KTWMinorA
import rcic.RcicF3MainG
import rcic.RcicTypedGroupPinsVec

/-!
# StepAG bounded cells: literal refutations and an exact group check

The unrestricted bare-node parameter and index premises shared by the Type and
Prop apices are false. `badNode` inhabits the original domain and violates both.
The exact finite check below is equivalent to the existing stored family type
check. On typed groups, the literal cells follow from landed `TypeFacts`;
`RecGroupAShape` retains the other five fields without asserting their producers.
No StepAG apex or R-CIC closure is claimed; `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.StepAGBounded

open Rcic.Declarative Rcic.F3 Rcic.F3.PSet

/-- Exactly the remaining fields of `RecGroupA`, with no boundedness premise. -/
structure RecGroupAShape {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : Prop where
  famFree : ∀ e, e ∈ a.family.parameters ++ a.family.indices →
    occursConst a.family.ref e = false
  fields : ∀ i : Fin a.constructors.length, FieldsClassA a.family.ref
    a.family.member.arity a.family.parameters.length a.family.indices.length
    (a.constructorViews i).fields 0
  riFree : ∀ (i : Fin a.constructors.length) (e : Expr Nat),
    e ∈ (a.constructorViews i).resultIndices → occursConst a.family.ref e = false
  opq : ∀ ls, transparentBody E a.family.ref ls = none
  shapes : ∀ i : Fin a.constructors.length, ∃ fuel,
    derivedMinor a i fuel (shapesOf a.family.ref (a.constructorViews i).fields) =
      a.minorTypes[i.val]?

/-- Complete the original group record using facts already supplied by a typed group. -/
theorem recGroupA_of_facts {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (hTF : TypeFacts E') (G : RecGroupAShape node.a) :
    RecGroupA node.a := by
  exact ⟨famBounded_node node hTF, G.famFree, G.fields, G.riFree, G.opq, G.shapes⟩

/-- The two literal cells, independently of the other bounded fields. -/
def DomainBounds {E : ResolvedEnv} (v : PolicyFamilyView E) : Prop :=
  ExprsBounded v.member.arity v.parameters ∧ ExprsBounded v.member.arity v.indices

/-- Exact finite check: no syntactic surrogate for either cell. -/
def domainBoundsB {E : ResolvedEnv} (v : PolicyFamilyView E) : Bool :=
  v.parameters.all (exprLevelsBounded v.member.arity) &&
    v.indices.all (exprLevelsBounded v.member.arity)

/-- Check correctness in both directions. -/
theorem domainBoundsB_iff {E : ResolvedEnv} (v : PolicyFamilyView E) :
    domainBoundsB v = true ↔ DomainBounds v := by
  simp [domainBoundsB, DomainBounds, ExprsBounded, List.all_eq_true]

/-- The exact boundary is the existing stored family type check. -/
theorem domainBounds_iff_storedType {E : ResolvedEnv} (v : PolicyFamilyView E) :
    DomainBounds v ↔ exprLevelsBounded v.member.arity v.member.mtype = true := by
  rw [v.storedType]
  constructor
  · intro h
    have hD : ExprsBounded v.member.arity (v.parameters ++ v.indices) := by
      intro e he
      exact (List.mem_append.mp he).elim (h.1 e) (h.2 e)
    have aux : ∀ ds : List (Expr Nat), ExprsBounded v.member.arity ds →
        exprLevelsBounded v.member.arity (policyPi ds (.sort v.resultLevel)) = true := by
      intro ds
      induction ds with
      | nil => intro _; exact v.resultBounded
      | cons A ds ih =>
        intro hb
        show (exprLevelsBounded v.member.arity A &&
          exprLevelsBounded v.member.arity (policyPi ds (.sort v.resultLevel))) = true
        rw [Bool.and_eq_true]
        exact ⟨hb A (List.mem_cons_self _ _),
          ih (fun e he => hb e (List.mem_cons_of_mem _ he))⟩
    exact aux _ hD
  · intro hb
    exact ExprsBounded_append (levelsBounded_policyPi _ _ _ hb).1

/-- Names the first failing literal conjunct. -/
inductive BoundsRefusal where
  | params
  | indices
  deriving DecidableEq

/-- Refuse by conjunct name, checking parameters before indices. -/
def boundsRefusalOf {E : ResolvedEnv} (v : PolicyFamilyView E) : Option BoundsRefusal :=
  if v.parameters.all (exprLevelsBounded v.member.arity) then
    if v.indices.all (exprLevelsBounded v.member.arity) then none else some .indices
  else some .params

/-- Success is exactly the two cells, without a completeness assumption. -/
theorem boundsRefusalOf_none_iff {E : ResolvedEnv} (v : PolicyFamilyView E) :
    boundsRefusalOf v = none ↔ DomainBounds v := by
  rw [← domainBoundsB_iff]
  unfold boundsRefusalOf domainBoundsB
  cases v.parameters.all (exprLevelsBounded v.member.arity) <;>
    cases v.indices.all (exprLevelsBounded v.member.arity) <;> decide

/-- Every named refusal is a real failure of the requested pair. -/
theorem boundsRefusalOf_sound {E : ResolvedEnv} (v : PolicyFamilyView E)
    {r : BoundsRefusal} (hr : boundsRefusalOf v = some r) : ¬ DomainBounds v := by
  intro h
  have hn := boundsRefusalOf_none_iff v |>.mpr h
  rw [hr] at hn
  cases hn

/-! A bare-node counterexample: the unused let is typed at a bounded sort,
but its annotation and value mention universe parameter 0 at family arity 0.
Both domain lists are nonempty. This cannot be admitted by GroupMembersT. -/

def badDomain : Expr Nat :=
  .letE (.sort (.succ (.param 0))) (.sort (.param 0)) (.sort .zero)

def badDomainTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    HasTy E n Γ badDomain (.sort (.succ .zero)) :=
  .letE Γ _ _ _ _ (.sort Γ _) (.sort Γ _) (.sort _ .zero)

def badDomainTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    HasTyT E n Γ badDomain (.sort (.succ .zero)) :=
  .letE Γ _ _ _ _ _ (.sort Γ _) (.sort Γ _) (.sort _ .zero)

def badFamilyMember : CheckedMember :=
  ⟨.inductiveM, 0, .pi badDomain (.pi badDomain (.sort .zero)), none⟩

def badPrefix : ResolvedEnv := extendEnv emptyEnv 0 badFamilyMember

def badFamilyView : PolicyFamilyView badPrefix where
  ref := 0
  member := badFamilyMember
  present := rfl
  hasClass := rfl
  parameters := [badDomain]
  indices := [badDomain]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun i => match i with
      | ⟨0, _⟩ => badDomainTy
      | ⟨1, _⟩ => badDomainTy }

theorem badFamilyTyped : FamilyTypedT badFamilyView := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨badDomainTyT⟩
  | ⟨1, _⟩ => exact ⟨badDomainTyT⟩

def badRecMember : CheckedMember :=
  ⟨.recursorM, 1, policyRecursorType badFamilyView [] .anySort, none⟩

def badAdmission : RecursorEliminationAdmitted badPrefix 1 badRecMember where
  family := badFamilyView
  constructors := []
  constructorViews := fun i => i.elim0
  constructorsPresent := fun i => i.elim0
  recursorRef := rfl
  minorTypes := []
  minorCount := rfl
  policy := .anySort
  selected := .emptyProp (fun _ => rfl) rfl
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

def badFamilyAppTyT {Γ : LCtx} {x y : Expr Nat}
    (hx : HasTyT badPrefix 1 Γ x badDomain) (hy : HasTyT badPrefix 1 Γ y badDomain) :
    HasTyT badPrefix 1 Γ (.app (.app (.const 0 []) x) y) (.sort .zero) :=
  .app Γ _ y badDomain (.sort .zero)
    (.app Γ _ x badDomain (.pi badDomain (.sort .zero))
      (.const Γ 0 [] badFamilyMember rfl rfl rfl) hx) hy

/-- The full recursor signature is typed even at this bare node. -/
def badRecTypeTyT : Σ u, HasTyT badPrefix 1 [] badRecMember.mtype (.sort u) := by
  refine ⟨_, .pi [] _ _ _ _ badDomainTyT
    (.pi _ _ _ _ _
      (.pi _ _ _ _ _ badDomainTyT
        (.pi _ _ _ _ _ (badFamilyAppTyT (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl))
          (.sort _ (.param 0))))
      (.pi _ _ _ _ _ badDomainTyT
        (.pi _ _ _ _ _ (badFamilyAppTyT (.bvar _ 2 _ rfl) (.bvar _ 0 _ rfl))
          (.app _ (.app (.bvar 2) (.bvar 1)) (.bvar 0)
            (.app (.app (.const 0 []) (.bvar 3)) (.bvar 1)) (.sort (.param 0))
            (.app _ (.bvar 2) (.bvar 1) badDomain
              (.pi (.app (.app (.const 0 []) (.bvar 4)) (.bvar 0)) (.sort (.param 0)))
              (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl))
            (.bvar _ 0 _ rfl)))))⟩

theorem badCensus : CtorCensus badPrefix 0 1 := by
  refine ⟨Nat.le_refl 1, fun c => ⟨?_, ?_⟩⟩
  · rintro ⟨cm, hc, hk, _⟩
    by_cases h0 : c = 0
    · subst c
      have hm : badFamilyMember = cm := Option.some.inj hc
      rw [← hm] at hk
      cases hk
    · simp [badPrefix, extendEnv, emptyEnv, h0] at hc
  · intro h
    have hn : ¬ (0 < c ∧ c < 1) := by omega
    exact False.elim (hn h)

def badIotaClause : IotaDescriptorClause badPrefix badAdmission where
  signatureOnly := rfl
  shapesAt := fun i => i.elim0
  fuelAt := fun i => i.elim0
  analyzed := fun i => i.elim0
  typed := fun i => i.elim0

def badEnv : ResolvedEnv := extendEnv badPrefix 1 badRecMember

/-- All fields of the original bare-node domain are inhabited. -/
def badNode : RecNode emptyEnv badEnv 0 1 badRecMember where
  E0 := badPrefix
  a := badAdmission
  h14 := badIotaClause
  fam := rfl
  fresh := rfl
  sub := fun _ _ h => h
  base := fun _ _ h => by cases h
  h04 := badCensus
  h07 := fun i => i.elim0
  h12 := fun i => i.elim0
  famTyped := badFamilyTyped
  ctorsTyped := fun i => i.elim0
  u := badRecTypeTyT.1
  hT := badRecTypeTyT.2

/-- The literal parameter cell in each original apex's unrestricted hgrp is false. -/
theorem bare_params_refuted
    (h : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm),
      ExprsBounded node.a.family.member.arity (famDataOf node.a).params) : False := by
  have hb := h badNode badDomain (List.mem_singleton_self _)
  change false = true at hb
  cases hb

/-- The literal index cell in each original apex's unrestricted hgrp is false. -/
theorem bare_indices_refuted
    (h : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm),
      ExprsBounded node.a.family.member.arity (famDataOf node.a).indices) : False := by
  have hb := h badNode badDomain (List.mem_singleton_self _)
  change false = true at hb
  cases hb

/-- The counterexample is rejected by the existing group admission check. -/
theorem badFamily_storedType_refuses :
    exprLevelsBounded badFamilyMember.arity badFamilyMember.mtype = false := rfl

/-- A named refusal on fully inhabited bare-node data. -/
theorem badNode_refusal : boundsRefusalOf badNode.a.family = some .params := rfl

/-- The original unrestricted `hgrp` premise is itself refuted. -/
theorem bare_recGroupA_refuted
    (h : ∀ {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
      (node : RecNode E E' f rr rm), RecGroupA node.a) : False := by
  exact bare_params_refuted (fun node => (h node).bounded.params)

/-- The literal pair follows on the existing typed-group domain. -/
theorem literal_cells_of_groupMembersT {S E E' : ResolvedEnv}
    {ms : List (Nat × CheckedMember)} {f rr : Nat} {rm : CheckedMember}
    (hE : EnvWfT E) (hmem : GroupMembersT S E ms E')
    (node : RecNode E E' f rr rm) :
    ExprsBounded node.a.family.member.arity (famDataOf node.a).params ∧
      ExprsBounded node.a.family.member.arity (famDataOf node.a).indices := by
  have hb := famBounded_node node
    (typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE))
  exact ⟨hb.params, hb.indices⟩

/-- A parameter refusal identifies precisely a failed parameter cell. -/
theorem boundsRefusalOf_params_iff {E : ResolvedEnv} (v : PolicyFamilyView E) :
    boundsRefusalOf v = some .params ↔
      ¬ ExprsBounded v.member.arity v.parameters := by
  have hp : v.parameters.all (exprLevelsBounded v.member.arity) = true ↔
      ExprsBounded v.member.arity v.parameters := by
    simp [ExprsBounded, List.all_eq_true]
  rw [← hp]
  unfold boundsRefusalOf
  cases v.parameters.all (exprLevelsBounded v.member.arity) <;>
    cases v.indices.all (exprLevelsBounded v.member.arity) <;> decide

/-- An index refusal identifies a failed index cell after the parameter cell passed. -/
theorem boundsRefusalOf_indices_iff {E : ResolvedEnv} (v : PolicyFamilyView E) :
    boundsRefusalOf v = some .indices ↔
      ExprsBounded v.member.arity v.parameters ∧
        ¬ ExprsBounded v.member.arity v.indices := by
  have hp : v.parameters.all (exprLevelsBounded v.member.arity) = true ↔
      ExprsBounded v.member.arity v.parameters := by
    simp [ExprsBounded, List.all_eq_true]
  have hi : v.indices.all (exprLevelsBounded v.member.arity) = true ↔
      ExprsBounded v.member.arity v.indices := by
    simp [ExprsBounded, List.all_eq_true]
  rw [← hp, ← hi]
  unfold boundsRefusalOf
  cases v.parameters.all (exprLevelsBounded v.member.arity) <;>
    cases v.indices.all (exprLevelsBounded v.member.arity) <;> decide

/-- The admitted Vec fixture passes with both domain lists nonempty. -/
theorem vec_bounds_nonvacuous :
    domainBoundsB vecGroupU.family = true ∧
      vecGroupU.family.parameters ≠ [] ∧
      vecGroupU.family.indices ≠ [] ∧ Nonempty (EnvWfT vecEnvUT) := by
  exact ⟨rfl, by decide, by decide, ⟨vecEnvUWfT⟩⟩

/-- Existing environment admission rejects the counterexample's stored type. -/
theorem badEnv_not_wfT (h : EnvWfT badEnv) : False := by
  have hb := ((typeFacts_of_envWfT h) 0 badFamilyMember rfl).2.1
  change false = true at hb
  cases hb

/-- All five non-bounded group fields hold at the counterexample. -/
def badNode_shape : RecGroupAShape badNode.a := by
  refine ⟨?_, fun i => i.elim0, fun i => i.elim0, fun _ => rfl, fun i => i.elim0⟩
  intro e he
  change e ∈ [badDomain] ++ [badDomain] at he
  have he' : e = badDomain := by simpa using he
  subst e
  rfl

end Rcic.F3.StepAGBounded
