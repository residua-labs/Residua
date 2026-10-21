import rcic.RcicTypedScopeCheck

/-!
# Typed scope: evidence supplied by admission and the remaining transports

This module extracts the actual premises of `GroupMembersT`; it does not call a
checker. In particular, constructor admission already supplies whole-type typing
in ConstructorScope, not merely typing in the prefix containing earlier
constructors. The recorded telescope levels are bounded by
`PolicyTelescopeTyping.bounded`.

The restriction theorem below is about syntactic constant support. It is not a
restriction theorem for `HasTyT`, `ConvT`, or `TyConvT`: conversion may use terms
and member lookups absent from the displayed endpoints.

The final section names smaller, explicit obligations for an admission-to-scope
construction. They are definitions of propositions and syntax records, not
supplies of those propositions. In particular, this module does not assert
`groupInScopeT_of_envWfT_group`. The measured source gap, even with hypotheses
excluding function-recursive and delta-reached fields and supplying the
resulting group's `GroupProfileT`, is the absence of a producer for the
full-to-plain local factorization and the native transports below. This is not
a refutation of the proposed implication from those hypotheses, nor a proof
that such a producer is impossible. This module does not eliminate the
checker-residue case of the separate scope audit.

No landed declaration is changed. `closure_claim = 0`.
-/

namespace Rcic.Declarative

/-! ## Actual member-admission evidence -/

/-- The premises of an actual `GroupMembersT.cons`, without its remaining tail.
`S` is the admission's ConstructorScope and `E` is this member's actual prefix.
This record adds no check and changes no sort index. -/
structure ScopeMemberAdmissionT (S E : ResolvedEnv) (r : Nat)
    (m : CheckedMember) : Type where
  fresh : E.members r = none
  noBody : m.body = none
  closedType : ∀ k, lift k 1 m.mtype = m.mtype
  arityShape : m.mclass = .inductiveM → isArity m.mtype = true
  levelsBounded : exprLevelsBounded m.arity m.mtype = true
  canonical : exprFamCanonical E m.mtype = true
  arityCoherent : groupArityCoherent E m = true
  admitted : IndGroupAdmitted E r m
  indicesAdmitted : IdxAdmittedT admitted
  universeLevel : Level
  typeTyped : HasTyT E m.arity [] m.mtype (.sort universeLevel)
  constructorScopeTyped : m.mclass = .constructorM →
    Nonempty (HasTyT S m.arity [] m.mtype (.sort universeLevel))
  viewsTyped : IndGroupTypedT admitted

/-- A head receipt is data because the input derivation is data. No existential
or `Nonempty` proof is eliminated to obtain it. -/
def groupMembersT_headAdmission {S E E' : ResolvedEnv} {r : Nat}
    {m : CheckedMember} {rest : List (Nat × CheckedMember)}
    (h : GroupMembersT S E ((r, m) :: rest) E') :
    ScopeMemberAdmissionT S E r m := by
  cases h with
  | cons _ _ _ _ _ hfresh hnobody hclT harity hlvlB hcanon harities
      hadm hidxAdmT u hT hTc htyped _ =>
      exact {
        fresh := hfresh
        noBody := hnobody
        closedType := hclT
        arityShape := harity
        levelsBounded := hlvlB
        canonical := hcanon
        arityCoherent := harities
        admitted := hadm
        indicesAdmitted := hidxAdmT
        universeLevel := u
        typeTyped := hT
        constructorScopeTyped := hTc
        viewsTyped := htyped }

/-- List membership gives existence of a receipt at the actual admission
prefix. The conclusion stays in `Prop`, so extracting a receipt from it never
requires choice. -/
theorem groupMembersT_admission_at {S E E' : ResolvedEnv}
    {entries : List (Nat × CheckedMember)}
    (h : GroupMembersT S E entries E') :
    ∀ r m, (r, m) ∈ entries →
      ∃ P, Nonempty (ScopeMemberAdmissionT S P r m) := by
  induction h with
  | nil E =>
      intro r m hm
      cases hm
  | cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon harities
      hadm hidxAdmT u hT hTc htyped hrest ih =>
      intro q qm hq
      rcases List.mem_cons.mp hq with hhead | htail
      · have hr : q = r := congrArg Prod.fst hhead
        have hm : qm = m := congrArg Prod.snd hhead
        cases hr
        cases hm
        exact ⟨E, ⟨{
          fresh := hfresh
          noBody := hnobody
          closedType := hclT
          arityShape := harity
          levelsBounded := hlvlB
          canonical := hcanon
          arityCoherent := harities
          admitted := hadm
          indicesAdmitted := hidxAdmT
          universeLevel := u
          typeTyped := hT
          constructorScopeTyped := hTc
          viewsTyped := htyped }⟩⟩
      · exact ih q qm htail

/-- ConstructorScope typing is an admission supply (`hTc`), not an environment
strengthening theorem reconstructed from `hT`. It preserves the sort recorded
by that same member-admission step. -/
theorem groupMembersT_constructor_scope_typing {S E E' : ResolvedEnv}
    {entries : List (Nat × CheckedMember)} {r : Nat} {m : CheckedMember}
    (h : GroupMembersT S E entries E') (hm : (r, m) ∈ entries)
    (hc : m.mclass = .constructorM) :
    ∃ u, Nonempty (HasTyT S m.arity [] m.mtype (.sort u)) := by
  obtain ⟨P, ⟨a⟩⟩ := groupMembersT_admission_at h r m hm
  exact ⟨a.universeLevel, a.constructorScopeTyped hc⟩

/-- Every syntactically named constant of a constructor's stored type lies in
its ConstructorScope. This conclusion concerns the term, not the hidden
intermediates of a conversion derivation. -/
theorem groupMembersT_constructor_constsIn {S E E' : ResolvedEnv}
    {entries : List (Nat × CheckedMember)} {r : Nat} {m : CheckedMember}
    (h : GroupMembersT S E entries E') (hm : (r, m) ∈ entries)
    (hc : m.mclass = .constructorM) : ConstsIn S m.mtype := by
  obtain ⟨u, ⟨hT⟩⟩ := groupMembersT_constructor_scope_typing h hm hc
  exact hasTyT_constsIn hT

/-- Specialization to the exact premises of `EnvWfT.group`: the constructor's
whole stored type is typed in the base with only its family added. -/
theorem envWfT_group_constructor_scope_typing {E E' : ResolvedEnv}
    {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    {r : Nat} {m : CheckedMember} (hm : (r, m) ∈ ctors) :
    ∃ u, Nonempty (HasTyT (extendEnv E f fm) m.arity []
      m.mtype (.sort u)) := by
  exact groupMembersT_constructor_scope_typing (r := r) (m := m) hmem (by simp [hm])
    (hctors (r, m) hm)

/-! ## Recorded levels and native view typings -/

/-- Admission supplies both this exact native sort index and its boundedness.
The boundedness is a field of the view, not a consequence of whole-type
boundedness or inversion of a native pi typing. -/
theorem familyTypedT_recorded_domain {E : ResolvedEnv}
    (v : PolicyFamilyView E) (ht : FamilyTypedT v)
    (i : Fin (v.parameters ++ v.indices).length) :
    levelBounded v.member.arity (v.domainsTyped.levels i) = true ∧
      Nonempty (HasTyT E v.member.arity
        (policyPrefixContext (v.parameters ++ v.indices) i.val)
        (v.parameters ++ v.indices)[i.val] (.sort (v.domainsTyped.levels i))) :=
  ⟨v.domainsTyped.bounded i, ht i⟩

/-- The constructor's recorded field level, its bound, and its native typing
are available in the actual full prefix context of that view. This does not
yet remove recursive-field locals or change the environment. -/
theorem ctorTypedT_recorded_field {E : ResolvedEnv}
    {family : PolicyFamilyView E} {member : CheckedMember}
    (c : PolicyConstructorView E family member) (ht : CtorTypedT c)
    (j : Fin c.fields.length) :
    levelBounded family.member.arity (c.fieldLevel j) = true ∧
      Nonempty (HasTyT E family.member.arity
        (policyPrefixContext (c.parameters ++ c.fields)
          (c.parameters.length + j.val))
        c.fields[j.val] (.sort (c.fieldLevel j))) := by
  have h := ht.1 (c.fieldIndex j)
  have hget : (c.parameters ++ c.fields)[(c.fieldIndex j).val] = c.fields[j.val] := by
    simp only [PolicyConstructorView.fieldIndex]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left]
  rw [hget] at h
  exact ⟨c.domainsTyped.bounded (c.fieldIndex j), h⟩

/-! ## A support restriction that does follow -/

/-- Removing an extension at an excluded reference preserves syntactic
constant support. This is deliberately weaker than native typing restriction.
Neither freshness nor bodylessness is needed for this support-only fact. -/
theorem constsIn_drop_extension {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} (e : Expr Nat) :
    ConstsIn (extendEnv E f fm) e → occursConst f e = false → ConstsIn E e := by
  induction e with
  | bvar i => intro _ _; trivial
  | sort u => intro _ _; trivial
  | const r ls =>
      intro hs hn
      have hne : r ≠ f := by
        simpa only [occursConst, decide_eq_false_iff_not] using hn
      obtain ⟨m, hm⟩ := hs
      rw [members_extend_ne E f fm r hne] at hm
      exact ⟨m, hm⟩
  | app a b iha ihb =>
      intro hs hn
      have hn' := Bool.or_eq_false_iff.mp hn
      exact ⟨iha hs.1 hn'.1, ihb hs.2 hn'.2⟩
  | lam a b iha ihb =>
      intro hs hn
      have hn' := Bool.or_eq_false_iff.mp hn
      exact ⟨iha hs.1 hn'.1, ihb hs.2 hn'.2⟩
  | pi a b iha ihb =>
      intro hs hn
      have hn' := Bool.or_eq_false_iff.mp hn
      exact ⟨iha hs.1 hn'.1, ihb hs.2 hn'.2⟩
  | letE a v b iha ihv ihb =>
      intro hs hn
      have hn' := Bool.or_eq_false_iff.mp hn
      have hav := Bool.or_eq_false_iff.mp hn'.1
      exact ⟨iha hs.1 hav.1, ihv hs.2.1 hav.2, ihb hs.2.2 hn'.2⟩
  | lit t =>
      intro hs hn
      cases t with
      | zero =>
          have hf : f ≠ 1 := by
            simpa only [occursConst, litOccurs, decide_eq_false_iff_not] using hn
          obtain ⟨m, hm⟩ := hs
          rw [members_extend_ne E f fm 1 (Ne.symm hf)] at hm
          exact ⟨m, hm⟩
      | succ t =>
          have hf : f ≠ 1 ∧ f ≠ 2 := by
            simpa only [occursConst, litOccurs, Bool.or_eq_false_iff,
              decide_eq_false_iff_not] using hn
          obtain ⟨⟨m1, hm1⟩, ⟨m2, hm2⟩⟩ := hs
          rw [members_extend_ne E f fm 1 (Ne.symm hf.1)] at hm1
          rw [members_extend_ne E f fm 2 (Ne.symm hf.2)] at hm2
          exact ⟨⟨m1, hm1⟩, ⟨m2, hm2⟩⟩

/-- Constant support of a stored pi telescope supplies support of each of its
raw domains, independently of any native pi-inversion theorem. -/
theorem constsIn_policyPi_domain {E : ResolvedEnv} (ds : List (Expr Nat))
    (T : Expr Nat) :
    ConstsIn E (policyPi ds T) → ∀ D ∈ ds, ConstsIn E D := by
  induction ds with
  | nil =>
      intro _ D hD
      cases hD
  | cons A ds ih =>
      intro h D hD
      rcases List.mem_cons.mp hD with hD | hD
      · cases hD
        exact h.1
      · exact ih h.2 D hD

/-- Applying the supplied ConstructorScope whole-type derivation to an actual
constructor view gives support of every raw field domain in that same scope. -/
theorem constructor_scope_raw_field_constsIn {S A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember} {u : Level}
    (c : PolicyConstructorView A family member)
    (hT : HasTyT S member.arity [] member.mtype (.sort u))
    {D : Expr Nat} (hD : D ∈ c.fields) : ConstsIn S D := by
  have hs := hasTyT_constsIn hT
  rw [c.storedType] at hs
  exact constsIn_policyPi_domain (c.parameters ++ c.fields) _ hs D
    (List.mem_append.mpr (Or.inr hD))

/-- A family-free raw field of an actual constructor names only base members.
The conclusion remains syntactic support, with the original full-context
field expression unchanged. Native environment transport and deletion of
recursive locals are still not supplied by this theorem. -/
theorem constructor_scope_family_free_field_constsIn {E A : ResolvedEnv}
    {f : Nat} {fm : CheckedMember} {family : PolicyFamilyView A}
    {member : CheckedMember} {u : Level}
    (c : PolicyConstructorView A family member)
    (hT : HasTyT (extendEnv E f fm) member.arity [] member.mtype (.sort u))
    {D : Expr Nat} (hD : D ∈ c.fields) (hfree : occursConst f D = false) :
    ConstsIn E D :=
  constsIn_drop_extension D (constructor_scope_raw_field_constsIn c hT hD) hfree

/-- Constant support alone says nothing about deleting local variables. This
small syntax example is not asserted to be an admitted-group counterexample. -/
theorem constsIn_does_not_supply_plain_factorization (E : ResolvedEnv) :
    ConstsIn E (.bvar 0) ∧ unshift? [true] 0 (.bvar 0) = none :=
  ⟨True.intro, rfl⟩

/-! ## Named remaining obligations, not admission supplies

Whole-type inversion of `hTc` can obtain some domain sort indices in
ConstructorScope. It does not identify them with `domainsTyped.levels`.
Keeping those recorded indices, as below, is one precise transport route; an
alternative construction must also prove the bounds and level comparisons of
its replacement labels.
-/

/-- Remaining fixed-level transport for the actual family view from its
self-extended environment to HeaderScope. The original `FamilyTypedT v` lives
in `extendEnv E f fm`; the target here lives in `E`. -/
def FamilyHeaderRetypingRemaining (E : ResolvedEnv) (f : Nat)
    (fm : CheckedMember) (v : PolicyFamilyView (extendEnv E f fm)) : Prop :=
  TelTypedT E v.member.arity (v.parameters ++ v.indices) v.domainsTyped.levels

/-- Remaining fixed-level transport of the constructor view's full telescope
from its actual admission prefix `A` into ConstructorScope `S`. Admission's
`hTc` already supplies the whole stored type there; this asks only for the
stronger, recorded-domain-index preservation that whole-type inversion does
not itself establish. -/
def ConstructorRecordedRetypingRemaining (S : ResolvedEnv) {A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    (c : PolicyConstructorView A family member) : Prop :=
  TelTypedT S family.member.arity (c.parameters ++ c.fields) c.domainsTyped.levels

/-- A purely syntactic full-to-plain factorization for one actual constructor
view. In particular, result indices must factor through the substitution that
reinserts the omitted recursive binders. No native typing, profile, layout,
recursor, or family-free transport is hidden in this record. -/
structure CtorPlainFactorT {A : ResolvedEnv} {family : PolicyFamilyView A}
    {member : CheckedMember} (c : PolicyConstructorView A family member) : Type where
  mirrors : List (Expr Nat × Level)
  fields : List FieldT
  resultIndices : List (Expr Nat)
  parameters_eq : c.parameters = mirrors.map Prod.fst
  fields_eq : c.fields = ctorDomsT family.ref (policyFamilyLevels family)
    (policyLocals mirrors.length) SubstT.id fields
  result_eq : c.resultIndices =
    resultIndices.map (substT (ctorEndSubstT SubstT.id fields))

/-- A consumer of the factorization, using the landed builder agreement. It
does not produce the factorization or any native typing. -/
theorem CtorPlainFactorT.storedType {A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member} (q : CtorPlainFactorT c) :
    member.mtype = ctorTypeT family.ref (policyFamilyLevels family)
      q.mirrors q.fields q.resultIndices :=
  (ctorFieldTelescope_eq c rfl rfl q.parameters_eq q.fields_eq q.result_eq).2

/-- Remaining base-environment mirror conversions, including the selected
sort-label equalities. At a fixed environment, the existing
`hasTyT_mirrorsToParams` changes mirror assumptions to family parameters at the
same context length. That theorem does not remove fresh member extensions or
recursive-field locals, and does not itself supply this base-environment
`MirrorsConvT` evidence. -/
def ConstructorMirrorRetypingRemaining (E : ResolvedEnv) {A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member} (fv : FamViewT family.member)
    (q : CtorPlainFactorT c) : Prop :=
  Nonempty (MirrorsConvT E family.member.arity [] q.mirrors fv.params)

/-- Remaining native evidence after the syntax has been factored: each plain
field, each recursive field's indices, and the result indices must be typed
in the base and the plain prefix. `FieldsTyT` keeps the exact sort written on
each plain field. Establishing its relationship to the original recorded
field levels is an additional label-alignment obligation below. -/
def ConstructorPlainRetypingRemaining (E : ResolvedEnv) {A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member} (fv : FamViewT family.member)
    (q : CtorPlainFactorT c) : Prop :=
  Nonempty (FieldsTyT E family.member.arity (fun k => lift 0 k fv.idxTel)
    (telCtxT fv.params) 0 q.fields q.resultIndices)

/-- If the fixed-recorded-level route is used, this is the exact alignment
needed for each plain field's label. It cannot be inferred from equality of
the erased constructor telescopes, which discard binder levels. -/
def ConstructorPlainLabelsRemaining {A : ResolvedEnv}
    {family : PolicyFamilyView A} {member : CheckedMember}
    {c : PolicyConstructorView A family member} (q : CtorPlainFactorT c) : Prop :=
  ∀ (j : Fin c.fields.length) (D : Expr Nat) (u : Level),
    q.fields[j.val]? = some (.plain D u) → u = c.fieldLevel j

/-!
The other landed agreements have the same supply/consumer boundary:
`derivedMinor_eq` requires the already reconstructed constructor telescope
and a no-`drecD` witness; `policyRecursorType_eq` requires the already supplied
minor list. Neither theorem creates any of the native transports above.

To complete an admission-to-scope proof one must also align the selected
family/constructor views and build the existing layout, universe-comparison,
profile, and no-`drecD` fields. The actual recorded family levels already have
their bounds, as `familyTypedT_recorded_domain` shows. No theorem here promotes
the definitions in this section to assumptions of `EnvWfT` or supplies them
from a failed checker query.
-/

#print axioms groupMembersT_headAdmission
#print axioms groupMembersT_admission_at
#print axioms groupMembersT_constructor_scope_typing
#print axioms groupMembersT_constructor_constsIn
#print axioms envWfT_group_constructor_scope_typing
#print axioms familyTypedT_recorded_domain
#print axioms ctorTypedT_recorded_field
#print axioms constsIn_drop_extension
#print axioms constsIn_policyPi_domain
#print axioms constructor_scope_raw_field_constsIn
#print axioms constructor_scope_family_free_field_constsIn
#print axioms constsIn_does_not_supply_plain_factorization
#print axioms CtorPlainFactorT.storedType

end Rcic.Declarative
