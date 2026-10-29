/-
05 §§5,6,10,11: declaration evidence for inductive elimination policy.

This module deliberately depends only on the declarative judgments and
the exact universe classifier.  In particular it does not import EnvWf:
EnvWf must REQUIRE this certificate when admitting a recursor, including
recursors whose IotaTyping supplier was constructed without a Bool.

The input boundary is the checked canonical STORED telescope already
used by EnvWf.isArity / IotaWitness.  Candidate normalization into this
view remains a separate obligation.  Parameter mirrors may be related
by Conv; the bare-local test on the canonical result indices is exact
syntax, not conversion.  Positivity and derivation of the minor types
remain the responsibilities of their existing admission evidence.
-/
/-
TREE ADAPTATION (main 45df7eccc6, #6075): this file is the #6071 predicate
at 2c28cb8d13, unchanged except `TyConv` → `Conv`. Face's `TyConv` is not
on main. Main's `Conv` is the untyped conversion judgment and has the
index shape face's `TyConv` used (context, left, right). Reported, not
re-chosen.
-/
import rcic.RcicUniverseClass

namespace Rcic.Declarative

/-- A corpus row is either a spec verdict of this judgment or a carrier
code that 05 does not use as a refusal class. Fuel exhaustion,
`unknown_form`, and out-of-slice / propagated residues are the latter. -/
inductive CorpusPinKind : Type
  | specAccept
  | specRefuse
  | notSpecRefusal
  deriving DecidableEq

/-- Left-to-right telescope domains, with their original de Bruijn scope. -/
def policyPi : List (Expr Nat) → Expr Nat → Expr Nat
  | [], body => body
  | A :: rest, body => .pi A (policyPi rest body)

/-- The context BEFORE domain i.  Stored domains need no extra lift here. -/
def policyPrefixContext (domains : List (Expr Nat)) (i : Nat) : LCtx :=
  ((domains.take i).reverse).map LocalDecl.assumption

/-- Typing of every telescope domain in its actual earlier-domain context.
Keeping all the domain typings prevents a proof-field check from relying
on an arbitrary, unchecked local context.  The selected sort levels are
the universe results of admission's field-type inference. -/
structure PolicyTelescopeTyping (E : ResolvedEnv) (n : Nat)
    (domains : List (Expr Nat)) : Type where
  levels : Fin domains.length → Level
  bounded : ∀ i, levelBounded n (levels i) = true
  hasType : ∀ i, HasTy E n (policyPrefixContext domains i.val)
    domains[i.val] (.sort (levels i))

def PolicyTelescopeTyping.empty (E : ResolvedEnv) (n : Nat) :
    PolicyTelescopeTyping E n [] where
  levels := fun i => Fin.elim0 i
  bounded := fun i => Fin.elim0 i
  hasType := fun i => Fin.elim0 i

/-- One supplied checked family view. Its parameter split is shared by
all constructor views and by the complete recursor signature, rather
than chosen separately for the singleton test. Binding this view to an
external candidate and its designated nparams remains a separate task. -/
structure PolicyFamilyView (E : ResolvedEnv) : Type where
  ref : Nat
  member : CheckedMember
  present : E.members ref = some member
  hasClass : member.mclass = .inductiveM
  parameters : List (Expr Nat)
  indices : List (Expr Nat)
  resultLevel : Level
  resultBounded : levelBounded member.arity resultLevel = true
  storedType : member.mtype =
    policyPi (parameters ++ indices) (.sort resultLevel)
  domainsTyped : PolicyTelescopeTyping E member.arity (parameters ++ indices)

/-- Exact canonical universe vector of a family, including the empty vector. -/
def policyFamilyLevels {E : ResolvedEnv} (family : PolicyFamilyView E) : List Level :=
  (List.range family.member.arity).map Level.param

/-- Parameters in a constructor's final context, after all stored fields. -/
def policyParameterLocals (nparams nfields : Nat) : List (Expr Nat) :=
  (List.range nparams).reverse.map (fun i => .bvar (i + nfields))

/-- Every local of a telescope, in declaration order. -/
def policyLocals (count : Nat) : List (Expr Nat) :=
  (List.range count).reverse.map Expr.bvar

/-- A constructor view is tied to its complete stored type, not an
untrusted list of field flags.  Its result contains exactly the family
parameters followed by the declared number of indices. -/
structure PolicyConstructorView (E : ResolvedEnv)
    (family : PolicyFamilyView E) (member : CheckedMember) : Type where
  hasClass : member.mclass = .constructorM
  arity : member.arity = family.member.arity
  parameters : List (Expr Nat)
  fields : List (Expr Nat)
  resultIndices : List (Expr Nat)
  parameterCount : parameters.length = family.parameters.length
  indexCount : resultIndices.length = family.indices.length
  storedType : member.mtype = policyPi (parameters ++ fields)
    (foldApps (.const family.ref (policyFamilyLevels family))
      (policyParameterLocals parameters.length fields.length ++ resultIndices))
  domainsTyped : PolicyTelescopeTyping E family.member.arity (parameters ++ fields)
  parameterMirrors : ∀ i : Fin parameters.length,
    Conv E family.member.arity (policyPrefixContext parameters i.val)
      parameters[i.val]
      (family.parameters[i.val]'(by rw [← parameterCount]; exact i.isLt))
  noFamilyInIndices : ∀ e ∈ resultIndices, occursConst family.ref e = false

namespace PolicyConstructorView

def fieldIndex {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member)
    (j : Fin c.fields.length) : Fin (c.parameters ++ c.fields).length :=
  ⟨c.parameters.length + j.val, by simp only [List.length_append]; omega⟩

def fieldLevel {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member)
    (j : Fin c.fields.length) : Level :=
  c.domainsTyped.levels (c.fieldIndex j)

/-- Only nonparameter fields are tested.  Revealed means exactly a bare
field local among RESULT INDICES; an occurrence under an application,
or only in the parameter segment, does not satisfy this predicate. -/
def FieldSafe {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member)
    (j : Fin c.fields.length) : Prop :=
  UniformProp (c.fieldLevel j) ∨
    Expr.bvar (c.fields.length - 1 - j.val) ∈ c.resultIndices

def AllFieldsSafe {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member) : Prop :=
  ∀ j, c.FieldSafe j

/-- The proof-field arm gives an actual typing judgment at Prop in the
recursor's admission prefix.  It does not use the new recursor. -/
def proofField_hasType {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member)
    (j : Fin c.fields.length) (h : UniformProp (c.fieldLevel j)) :
    HasTy E family.member.arity
      (policyPrefixContext (c.parameters ++ c.fields) (c.parameters.length + j.val))
      c.fields[j.val] (.sort .zero) := by
  have ht := c.domainsTyped.hasType (c.fieldIndex j)
  have hget : (c.parameters ++ c.fields)[(c.fieldIndex j).val] = c.fields[j.val] := by
    simp only [fieldIndex]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left]
  rw [hget] at ht
  -- main `HasTy.conv` is `(Γ e A B) (h : HasTy e A) (hc : Conv A B)`.
  -- Face passed the conversion proof in a different slot.
  exact HasTy.conv _ _ _ _ ht
    (Conv.sorts _ (c.fieldLevel j) .zero (uniformProp_eqN_zero h))

end PolicyConstructorView

inductive EliminationPolicy : Type
  | anySort
  | propOnly
  deriving DecidableEq

/-- §10's exact decision relation.  Mixed universes have no constructor.
For a singleton, PropOnly requires an actual failure of the stated
all-fields test, not merely the absence of an AnySort certificate. -/
inductive EliminationSelection (resultLevel : Level) (constructorCount : Nat)
    (allFieldsSafe : Prop) : EliminationPolicy → Prop
  | uniformType (h : UniformType resultLevel) :
      EliminationSelection resultLevel constructorCount allFieldsSafe .anySort
  | emptyProp (h : UniformProp resultLevel) (hk : constructorCount = 0) :
      EliminationSelection resultLevel constructorCount allFieldsSafe .anySort
  | singletonProp (h : UniformProp resultLevel) (hk : constructorCount = 1)
      (hsafe : allFieldsSafe) :
      EliminationSelection resultLevel constructorCount allFieldsSafe .anySort
  | multipleProp (h : UniformProp resultLevel) (hk : 1 < constructorCount) :
      EliminationSelection resultLevel constructorCount allFieldsSafe .propOnly
  | hiddenDataProp (h : UniformProp resultLevel) (hk : constructorCount = 1)
      (hunsafe : ¬ allFieldsSafe) :
      EliminationSelection resultLevel constructorCount allFieldsSafe .propOnly

def policyMotiveLevel (baseArity : Nat) : EliminationPolicy → Level
  | .anySort => .param baseArity
  | .propOnly => .zero

def policyRecursorArity (baseArity : Nat) : EliminationPolicy → Nat
  | .anySort => baseArity + 1
  | .propOnly => baseArity

/-- The entire motive domain, under the original parameter context. -/
def policyMotiveType {E : ResolvedEnv} (family : PolicyFamilyView E)
    (policy : EliminationPolicy) : Expr Nat :=
  policyPi family.indices
    (.pi (foldApps (.const family.ref (policyFamilyLevels family))
      (policyLocals (family.parameters.length + family.indices.length)))
      (.sort (policyMotiveLevel family.member.arity policy)))

/-- Complete canonical signature, including the shifted index domains.
At index j the previous j indices are kept fixed while parameters move
past the motive and all minors.  Minor contents are checked by the
separate recursor/iota derivation evidence. -/
def policyRecursorType {E : ResolvedEnv} (family : PolicyFamilyView E)
    (minorTypes : List (Expr Nat)) (policy : EliminationPolicy) : Expr Nat :=
  let k := minorTypes.length
  let q := family.indices.length
  let major := foldApps (.const family.ref (policyFamilyLevels family))
    (policyParameterLocals family.parameters.length (k + 1 + q) ++ policyLocals q)
  let result := foldApps (.bvar (k + q + 1))
    ((List.range q).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])
  policyPi family.parameters
    (.pi (policyMotiveType family policy)
      (policyPi minorTypes
        (policyPi (family.indices.mapIdx (fun j T => lift j (k + 1) T))
          (.pi major result))))

/-- Mandatory declaration evidence, to be required by EnvWf.indMember
whenever m is a recursor.  E is the checked prefix BEFORE adding r.
Neither a custom IotaTyping supplier nor the old admission Bool can
bypass the policy: they do not construct this record automatically. -/
structure RecursorEliminationAdmitted (E : ResolvedEnv) (r : Nat)
    (m : CheckedMember) : Type where
  family : PolicyFamilyView E
  constructors : List CheckedMember
  constructorViews : ∀ i : Fin constructors.length,
    PolicyConstructorView E family constructors[i.val]
  constructorsPresent : ∀ i : Fin constructors.length,
    E.members (family.ref + 1 + i.val) = some constructors[i.val]
  recursorRef : r = family.ref + 1 + constructors.length
  minorTypes : List (Expr Nat)
  minorCount : minorTypes.length = constructors.length
  policy : EliminationPolicy
  selected : EliminationSelection family.resultLevel constructors.length
    (∀ i, (constructorViews i).AllFieldsSafe) policy
  recursorArity : m.arity = policyRecursorArity family.member.arity policy
  recursorType : m.mtype = policyRecursorType family minorTypes policy
  /-- Admission integrity: the member an eliminator admission is built for is
  classed `.recursorM`. Pins the tag–mclass agreement `WalkRec` checks per
  group cons — an anomalous `.recursor` admission on a differently-classed
  member is unrepresentable, so `WalkRec hmem` becomes derivable from `hmem`
  alone. -/
  recursorMclass : m.mclass = .recursorM

namespace EliminationSelection

/-- Every in-profile family has a policy once the finite singleton test
is decided.  This includes empty Prop and both singleton alternatives. -/
theorem exists_of_classified {u : Level} {k : Nat} {safe : Prop}
    [Decidable safe] (h : UniformProp u ∨ UniformType u) :
    ∃ p, EliminationSelection u k safe p := by
  rcases h with hp | ht
  · cases k with
    | zero => exact ⟨.anySort, .emptyProp hp rfl⟩
    | succ k =>
        cases k with
        | zero =>
            by_cases hs : safe
            · exact ⟨.anySort, .singletonProp hp rfl hs⟩
            · exact ⟨.propOnly, .hiddenDataProp hp rfl hs⟩
        | succ k =>
            exact ⟨.propOnly, .multipleProp hp (by omega)⟩
  · exact ⟨.anySort, .uniformType ht⟩

theorem anySort_iff (u : Level) (k : Nat) (safe : Prop) :
    EliminationSelection u k safe .anySort ↔
      UniformType u ∨ (UniformProp u ∧ (k = 0 ∨ (k = 1 ∧ safe))) := by
  constructor
  · intro h
    cases h with
    | uniformType hu => exact Or.inl hu
    | emptyProp hu hk => exact Or.inr ⟨hu, Or.inl hk⟩
    | singletonProp hu hk hs => exact Or.inr ⟨hu, Or.inr ⟨hk, hs⟩⟩
  · intro h
    rcases h with ht | ⟨hp, hk | ⟨hk, hs⟩⟩
    · exact .uniformType ht
    · exact .emptyProp hp hk
    · exact .singletonProp hp hk hs

theorem propOnly_iff (u : Level) (k : Nat) (safe : Prop) :
    EliminationSelection u k safe .propOnly ↔
      UniformProp u ∧ (1 < k ∨ (k = 1 ∧ ¬ safe)) := by
  constructor
  · intro h
    cases h with
    | multipleProp hp hk => exact ⟨hp, Or.inl hk⟩
    | hiddenDataProp hp hk hs => exact ⟨hp, Or.inr ⟨hk, hs⟩⟩
  · rintro ⟨hp, hk | ⟨hk, hs⟩⟩
    · exact .multipleProp hp hk
    · exact .hiddenDataProp hp hk hs

private theorem prop_type_disjoint {u : Level}
    (hp : UniformProp u) (ht : UniformType u) : False := by
  have hzero := hp (fun _ => 0)
  have hpositive := ht (fun _ => 0)
  omega

theorem not_both {u : Level} {k : Nat} {safe : Prop}
    (ha : EliminationSelection u k safe .anySort)
    (hp : EliminationSelection u k safe .propOnly) : False := by
  obtain ⟨hprop, hmany | ⟨hone, hunsafe⟩⟩ := (propOnly_iff u k safe).mp hp
  · rcases (anySort_iff u k safe).mp ha with htype | ⟨_, hzero | ⟨hone, _⟩⟩
    · exact prop_type_disjoint hprop htype
    · omega
    · omega
  · rcases (anySort_iff u k safe).mp ha with htype | ⟨_, hzero | ⟨_, hsafe⟩⟩
    · exact prop_type_disjoint hprop htype
    · omega
    · exact hunsafe hsafe

theorem deterministic {u : Level} {k : Nat} {safe : Prop}
    {p q : EliminationPolicy} (hp : EliminationSelection u k safe p)
    (hq : EliminationSelection u k safe q) : p = q := by
  cases p <;> cases q
  · rfl
  · exact False.elim (not_both hp hq)
  · exact False.elim (not_both hq hp)
  · rfl

theorem uniformProp_many {u : Level} {k : Nat} {safe : Prop}
    {policy : EliminationPolicy} (h : EliminationSelection u k safe policy)
    (hu : UniformProp u) (hk : 1 < k) : policy = .propOnly :=
  deterministic h (.multipleProp hu hk)

theorem not_mixed {u : Level} {k : Nat} {safe : Prop}
    {policy : EliminationPolicy} (h : EliminationSelection u k safe policy) :
    ¬ MixedUniverse u := by
  intro hm
  cases h with
  | uniformType ht => exact hm.2 ht
  | emptyProp hp _ => exact hm.1 hp
  | singletonProp hp _ _ => exact hm.1 hp
  | multipleProp hp _ => exact hm.1 hp
  | hiddenDataProp hp _ _ => exact hm.1 hp

end EliminationSelection

namespace RecursorEliminationAdmitted

/-- A readout for consumers: a multi-constructor Prop group is bound to
the PropOnly signature, including both motive universe and arity. -/
theorem uniformProp_many {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (hprop : UniformProp a.family.resultLevel) (hmany : 1 < a.constructors.length) :
    a.policy = .propOnly ∧ m.arity = a.family.member.arity ∧
      m.mtype = policyRecursorType a.family a.minorTypes .propOnly := by
  have hp := EliminationSelection.uniformProp_many a.selected hprop hmany
  refine ⟨hp, ?_, ?_⟩
  · simpa only [hp, policyRecursorArity] using a.recursorArity
  · simpa only [hp] using a.recursorType

/-- Generic rejection of the previously admitted two-proof-constructor
large eliminator.  No conversion-injectivity statement is assumed. -/
theorem no_uniformProp_many_anySort_arity {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (hprop : UniformProp a.family.resultLevel) (hmany : 1 < a.constructors.length)
    (hlarge : m.arity = a.family.member.arity + 1) : False := by
  have hsmall := (a.uniformProp_many hprop hmany).2.1
  omega

theorem result_not_mixed {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : ¬ MixedUniverse a.family.resultLevel :=
  EliminationSelection.not_mixed a.selected

end RecursorEliminationAdmitted

/-! ## 05 §10. Two Prop constructors are not an AnySort elimination.
The PropOnly selection is the refusal of that large elimination.
Outside the 103 carrier rows. The proof applies `multipleProp`, so
deleting that constructor fails this pin. -/

def elRefuse_kind : CorpusPinKind := .specRefuse
theorem elRefuse_pin :
    elRefuse_kind = .specRefuse ∧
      ¬ EliminationSelection .zero 2 True .anySort ∧
      EliminationSelection .zero 2 True .propOnly := by
  have hp : UniformProp .zero := by intro _; rfl
  refine ⟨rfl, ?_, .multipleProp hp (by decide)⟩
  intro h
  rcases (EliminationSelection.anySort_iff .zero 2 True).mp h with ht | ⟨_, hk⟩
  · have := ht (fun _ => 0)
    simp [evalTotal] at this
  · rcases hk with hk | ⟨hk, _⟩ <;> omega

end Rcic.Declarative
