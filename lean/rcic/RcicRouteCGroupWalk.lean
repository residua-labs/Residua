import rcic.RcicRouteCGroupScope

namespace Rcic.Declarative

/-! # Route C walk extraction: the group's own `GroupMembersT` supplies its
    views — admission case dispatch and the member receipts, as data. The
    native transports stay named obligations. -/

/-- the member-admission receipt at a chosen entry index, as data. -/
noncomputable def groupMembersT_memberAt {S E E' : ResolvedEnv}
    {entries : List (Nat × CheckedMember)}
    (h : GroupMembersT S E entries E') :
    ∀ (k : Nat) (r : Nat) (m : CheckedMember), entries[k]? = some (r, m) →
      Σ' (P : ResolvedEnv), ScopeMemberAdmissionT S P r m := by
  induction h with
  | nil E =>
      intro k r m hk
      cases hk
  | cons E r m rest E' hfresh hnobody hclT harity hlvlB hcanon harities
      hadm hidxAdmT u hT hTc htyped hrest ih =>
      intro k q qm hk
      cases k with
      | zero =>
          rw [List.getElem?_cons_zero] at hk
          obtain ⟨h2a, h2b⟩ :=
            Prod.ext_iff.mp (Option.some.inj hk)
          subst h2a
          subst h2b
          exact ⟨E, {
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
            viewsTyped := htyped }⟩
      | succ k =>
          rw [List.getElem?_cons_succ] at hk
          exact ih k q qm hk

/-- a telescope's `isArity` is its body's. -/
theorem isArity_policyPi : (ds : List (Expr Nat)) →
    ∀ T : Expr Nat, isArity (policyPi ds T) = isArity T
  | [], _ => rfl
  | _ :: ds, T => isArity_policyPi ds _

/-- an application spine is no arity. -/
theorem isArity_foldApps_cons : ∀ (f x : Expr Nat) (xs : List (Expr Nat)),
    isArity (foldApps f (x :: xs)) = false
  | _, _, [] => rfl
  | f, x, _ :: ys => isArity_foldApps_cons (.app f x) _ ys

/-- `foldApps` over a nonempty appended tail is no arity. -/
theorem isArity_foldApps_snoc (xs : List (Expr Nat)) (a f : Expr Nat) :
    isArity (foldApps f (xs ++ [a])) = false := by
  cases xs with
  | nil => rfl
  | cons x xs => exact isArity_foldApps_cons f x (xs ++ [a])

/-- the policy recursor signature is no arity — a `.recursor` admission is
    inconsistent with an `.inductiveM` member's `isArity` clause. -/
theorem isArity_policyRecursorType {E : ResolvedEnv}
    (family : PolicyFamilyView E) (minorTypes : List (Expr Nat))
    (policy : EliminationPolicy) :
    isArity (policyRecursorType family minorTypes policy) = false := by
  simp only [policyRecursorType]
  rw [isArity_policyPi]
  show isArity (policyPi minorTypes
      (policyPi (family.indices.mapIdx fun j T => lift j (minorTypes.length + 1) T)
        (.pi _ _))) = false
  rw [isArity_policyPi, isArity_policyPi]
  exact isArity_foldApps_snoc _ _ _

/-- a `.recursor` admission cannot sit on an `.inductiveM` member: the
    member's `isArity` clause fails on the recursor signature. -/
theorem familyNotRecursorCase {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    (harity : isArity fm.mtype = true)
    (a : RecursorEliminationAdmitted E f fm) : False := by
  rw [a.recursorType, isArity_policyRecursorType] at harity
  cases harity

/-- the family member's admission is necessarily `.family`. -/
def familyAdmittedView {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    (hfam : fm.mclass = .inductiveM) (harity : isArity fm.mtype = true)
    (adm : IndGroupAdmitted E f fm) :
    Σ' (v : PolicyFamilyView (extendEnv E f fm)),
      v.ref = f ∧ v.member = fm ∧
        (UniformProp v.resultLevel ∨ UniformType v.resultLevel) := by
  cases adm with
  | family _ view href hm hProfile =>
      exact ⟨view, href, hm, hProfile⟩
  | constructor _ view _ _ _ _ _ =>
      exact absurd (hfam.symm.trans view.hasClass)
        (fun h => MemberClass.noConfusion h)
  | recursor a _ _ _ _ _ _ =>
      exact (familyNotRecursorCase harity a).elim

/-- the recursor member's admission is necessarily `.recursor`: the other
    cases pin `.inductiveM`/`.constructorM` classes on it. Returns the
    `MinorPremisesMatch` clause too — it is the `derivedMinor_eq` wiring
    input for the stored-type equality. -/
def recursorAdmittedView {E : ResolvedEnv} {rr : Nat} {rm : CheckedMember}
    (hcls : rm.mclass = .recursorM) (adm : IndGroupAdmitted E rr rm) :
    Σ' (a : RecursorEliminationAdmitted E rr rm), MinorPremisesMatch a := by
  cases adm with
  | family _ view _ hm _ =>
      have hic : rm.mclass = .inductiveM := hm ▸ view.hasClass
      exact absurd (hic.symm.trans hcls) (fun h => MemberClass.noConfusion h)
  | constructor _ view _ _ _ _ _ =>
      exact absurd (view.hasClass.symm.trans hcls)
        (fun h => MemberClass.noConfusion h)
  | recursor a _ _ _ _ h12 _ => exact ⟨a, h12⟩

/-- NAMED OBLIGATION (class-case): a `RecursorEliminationAdmitted` never
    describes a `.constructorM` member. The class tag is not recoverable from
    the record's own fields — it is an invariant of how `IndGroupAdmitted`
    was produced, the same shape as the `*Remaining` transports. -/
def RecursorAdmissionClass : Prop :=
  ∀ {E : ResolvedEnv} {r : Nat} {m : CheckedMember},
    RecursorEliminationAdmitted E r m → m.mclass ≠ .constructorM

/-- a constructor member's admission projects to its
    `PolicyConstructorView` — `.family` contradicts the class tag and
    `.recursor` is the named class obligation. -/
def ctorAdmittedView {E : ResolvedEnv} {r : Nat} {cm : CheckedMember}
    (hrc : RecursorAdmissionClass) (hcm : cm.mclass = .constructorM)
    (adm : IndGroupAdmitted E r cm) :
    Σ' (family : PolicyFamilyView E) (view : PolicyConstructorView E family cm),
      FieldUniverseAdmitted view ∧ CtorFieldsPermitted view := by
  cases adm with
  | family _ view _ hm _ =>
      have hic : cm.mclass = .inductiveM := hm ▸ view.hasClass
      exact absurd (hic.symm.trans hcm) (fun h => MemberClass.noConfusion h)
  | constructor family view _ _ _ h07 h08 =>
      exact ⟨family, view, h07, h08⟩
  | recursor a _ _ _ _ _ _ =>
      exact absurd hcm (hrc a)

/-- what the walk supplies about one constructor: the admission's own
    view and member receipts. `P` is the ctor's actual admission prefix. -/
structure CtorAdmissionBundle (S : ResolvedEnv) (P : ResolvedEnv) (r : Nat)
    (cm : CheckedMember) : Type where
  family : PolicyFamilyView P
  cview : PolicyConstructorView P family cm
  univ : FieldUniverseAdmitted cview
  permitted : CtorFieldsPermitted cview
  nobody : cm.body = none
  clT : ∀ k, lift k 1 cm.mtype = cm.mtype
  lvl : exprLevelsBounded cm.arity cm.mtype = true
  u : Level
  typeTyped : HasTyT P cm.arity [] cm.mtype (.sort u)
  scopeTyped : Nonempty (HasTyT S cm.arity [] cm.mtype (.sort u))

/-- the walk yields each ctor's admission bundle. -/
noncomputable def envWfT_group_ctorBundle {S E E' : ResolvedEnv}
    {entries : List (Nat × CheckedMember)}
    (h : GroupMembersT S E entries E') (hrc : RecursorAdmissionClass)
    (k : Nat) {r : Nat} {cm : CheckedMember}
    (hk : entries[k]? = some (r, cm))
    (hcm : cm.mclass = .constructorM) :
    Σ' (P : ResolvedEnv), CtorAdmissionBundle S P r cm := by
  obtain ⟨P, s⟩ := groupMembersT_memberAt h k r cm hk
  obtain ⟨family, view, h07, h08⟩ := ctorAdmittedView hrc hcm s.admitted
  exact ⟨P, {
    family := family
    cview := view
    univ := h07
    permitted := h08
    nobody := s.noBody
    clT := s.closedType
    lvl := s.levelsBounded
    u := s.universeLevel
    typeTyped := s.typeTyped
    scopeTyped := s.constructorScopeTyped hcm }⟩

/-- the walk yields the family's self-extended policy view. -/
noncomputable def envWfT_group_familyView {S E E' : ResolvedEnv}
    {entries : List (Nat × CheckedMember)}
    (h : GroupMembersT S E entries E')
    {f : Nat} {fm : CheckedMember} (hm : entries[0]? = some (f, fm))
    (hfam : fm.mclass = .inductiveM) :
    Σ' (P : ResolvedEnv) (v : PolicyFamilyView (extendEnv P f fm)),
      v.ref = f ∧ v.member = fm ∧
        (UniformProp v.resultLevel ∨ UniformType v.resultLevel) := by
  obtain ⟨P, s⟩ := groupMembersT_memberAt h 0 f fm hm
  obtain ⟨v, href, hmv, hprof⟩ :=
    familyAdmittedView hfam (s.arityShape hfam) s.admitted
  exact ⟨P, v, href, hmv, hprof⟩

/-- what the walk supplies about the recursor member. -/
structure RecAdmissionBundle (P : ResolvedEnv) (rr : Nat)
    (rm : CheckedMember) : Type where
  a : RecursorEliminationAdmitted P rr rm
  minorMatch : MinorPremisesMatch a
  nobody : rm.body = none
  clT : ∀ k, lift k 1 rm.mtype = rm.mtype
  lvl : exprLevelsBounded rm.arity rm.mtype = true
  u : Level
  typeTyped : HasTyT P rm.arity [] rm.mtype (.sort u)

/-- a cons'd head entry's `getElem?`. -/
theorem head_getElem (a : Nat × CheckedMember)
    (rest : List (Nat × CheckedMember)) : (a :: rest)[0]? = some a :=
  List.getElem?_cons_zero

/-- the appended tail entry's `getElem?`. -/
theorem tailLast_getElem (b : Nat × CheckedMember) :
    ∀ (ctors : List (Nat × CheckedMember)),
      (ctors ++ [b])[ctors.length]? = some b
  | [] => rfl
  | x :: xs => by
      rw [List.cons_append, List.length_cons, List.getElem?_cons_succ]
      exact tailLast_getElem b xs

/-- the group's last entry is the recursor member. -/
theorem lastEntry_getElem (a b : Nat × CheckedMember)
    (ctors : List (Nat × CheckedMember)) :
    (a :: ctors ++ [b])[ctors.length + 1]? = some b := by
  rw [List.cons_append, List.getElem?_cons_succ]
  exact tailLast_getElem b ctors

/-- the walk yields the recursor member's admission and receipts. -/
noncomputable def envWfT_group_recBundle {S E E' : ResolvedEnv}
    {entries : List (Nat × CheckedMember)}
    (h : GroupMembersT S E entries E')
    (k : Nat) {rr : Nat} {rm : CheckedMember}
    (hk : entries[k]? = some (rr, rm))
    (hcls : rm.mclass = .recursorM) :
    Σ' (P : ResolvedEnv), RecAdmissionBundle P rr rm := by
  obtain ⟨P, s⟩ := groupMembersT_memberAt h k rr rm hk
  obtain ⟨a, h12⟩ := recursorAdmittedView hcls s.admitted
  exact ⟨P, a, h12, s.noBody, s.closedType, s.levelsBounded,
    s.universeLevel, s.typeTyped⟩

/-- the recursor's stored type from its admission bundle: `a.recursorType`
    composed through `policyRecursorType_eq`. The admitted-minor-list-to-
    views'-minor-list equality `hminor` is the named residual — per-i it is
    `MinorPremisesMatch` (carried in `b.minorMatch`) composed with
    `derivedMinor_eq` at each `ctorFieldTelescope_eq` factorization. -/
theorem recStored_of_bundle {E P : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {cs : List (GroupCtorT E f fm fv)} {rr : Nat}
    {rm : CheckedMember}
    (b : RecAdmissionBundle P rr rm)
    (href : b.a.family.ref = f)
    (hm : b.a.family.member = fm)
    (hls : policyFamilyLevels b.a.family = canonLevels fm.arity)
    (hpar : b.a.family.parameters = fv.params.map Prod.fst)
    (hidx : b.a.family.indices = fv.indices.map Prod.fst)
    (hminor : b.a.minorTypes =
      minorDomsT f (canonLevels fm.arity) fv.params.length 0
        (cs.reverse.map GroupCtorT.minorData)) :
    rm.mtype = groupRecTypeT cs b.a.policy := by
  rw [b.a.recursorType, hminor,
    policyRecursorType_eq b.a.family b.a.policy
      (cs.reverse.map GroupCtorT.minorData) href hls hpar hidx]
  subst hm
  rfl

/-- a ctor input assembled from the admission bundle plus the remaining
    transports, which stay hypotheses: the family link (`hfm`/`href`/`hsort`
    — eqN level-uniqueness territory), the factorization run and labels, the
    mirror and plain retypings, and the ConstructorScope typing. -/
def ctorScopeInput_of_bundle {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {P : ResolvedEnv} {r : Nat} {cm : CheckedMember}
    (b : CtorAdmissionBundle (extendEnv E f fm) P r cm)
    (hfm : b.family.member = fm) (href : b.family.ref = f)
    (hsort : b.family.resultLevel = fv.sort)
    (factor : CtorPlainFactorT b.cview)
    (labels : ConstructorPlainLabelsRemaining factor)
    (mirrorsConv : MirrorsConvT E fm.arity [] factor.mirrors fv.params)
    (fieldsTy : FieldsTyT E fm.arity (fun k => lift 0 k fv.idxTel)
      (telCtxT fv.params) 0 factor.fields factor.resultIndices)
    (noDrecD : ∀ d ∈ factor.fields, d.isDrecD = false)
    (hT : HasTyT (extendEnv E f fm) cm.arity [] cm.mtype (.sort b.u)) :
    CtorScopeInputT E f fm fv cm where
  A := P
  family := b.family
  cview := b.cview
  hfm := hfm
  href := href
  hsort := hsort
  factor := factor
  labels := labels
  mirrorsConv := mirrorsConv
  fieldsTy := fieldsTy
  univ := b.univ
  noDrecD := noDrecD
  nobody := b.nobody
  clT := b.clT
  u := b.u
  hT := hT
  lvl := b.lvl

/-- the per-constructor remaining transports — everything the admission
    bundle does not already carry, stated at the extracted bundle. -/
structure CtorScopeTransports (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (fv : FamViewT fm) {P : ResolvedEnv} {r : Nat} {cm : CheckedMember}
    (b : CtorAdmissionBundle (extendEnv E f fm) P r cm) : Type where
  hfm : b.family.member = fm
  href : b.family.ref = f
  hsort : b.family.resultLevel = fv.sort
  factor : CtorPlainFactorT b.cview
  labels : ConstructorPlainLabelsRemaining factor
  mirrorsConv : MirrorsConvT E fm.arity [] factor.mirrors fv.params
  fieldsTy : FieldsTyT E fm.arity (fun k => lift 0 k fv.idxTel)
    (telCtxT fv.params) 0 factor.fields factor.resultIndices
  noDrecD : ∀ d ∈ factor.fields, d.isDrecD = false
  hT : HasTyT (extendEnv E f fm) cm.arity [] cm.mtype (.sort b.u)

/-- `CtorScopeInputT` from the bundle + transports. -/
def ctorScopeInput_of_transports {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {fv : FamViewT fm} {P : ResolvedEnv} {r : Nat}
    {cm : CheckedMember}
    (b : CtorAdmissionBundle (extendEnv E f fm) P r cm)
    (t : CtorScopeTransports E f fm fv b) :
    CtorScopeInputT E f fm fv cm :=
  ctorScopeInput_of_bundle b t.hfm t.href t.hsort t.factor t.labels
    t.mirrorsConv t.fieldsTy t.noDrecD t.hT

/-- the ctor entries' `getElem?` inside the group's entry list. -/
theorem ctorEntry_getElem_of (a b : Nat × CheckedMember)
    {ctors : List (Nat × CheckedMember)} {k : Nat} {x : Nat × CheckedMember}
    (hk : ctors[k]? = some x) :
    (a :: ctors ++ [b])[k + 1]? = some x := by
  rw [List.cons_append, List.getElem?_cons_succ]
  have hlt : k < ctors.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [List.getElem?_append_left hlt]
  exact hk

/-- the recursor's remaining transports at the extracted bundle. -/
structure RecScopeTransports (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (fv : FamViewT fm) (cs : List (GroupCtorT E f fm fv))
    {P : ResolvedEnv} {rr : Nat} {rm : CheckedMember}
    (b : RecAdmissionBundle P rr rm) : Type where
  href : b.a.family.ref = f
  hm : b.a.family.member = fm
  hls : policyFamilyLevels b.a.family = canonLevels fm.arity
  hpar : b.a.family.parameters = fv.params.map Prod.fst
  hidx : b.a.family.indices = fv.indices.map Prod.fst
  hminor : b.a.minorTypes =
    minorDomsT f (canonLevels fm.arity) fv.params.length 0
      (cs.reverse.map GroupCtorT.minorData)
  hT : HasTyT (groupEnvT E f fm (cs.map GroupCtorT.entry)) rm.arity []
    rm.mtype (.sort b.u)

/-- `RecScopeInputT` from the bundle + transports: `elim`/`arity`/`stored`
    are discharged from the admission; `hT`/`lvl` stay transported. -/
def recScopeInput_of_bundle {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {fv : FamViewT fm} {cs : List (GroupCtorT E f fm fv)} {P : ResolvedEnv}
    {rr : Nat} {rm : CheckedMember}
    (b : RecAdmissionBundle P rr rm)
    (t : RecScopeTransports E f fm fv cs b) :
    RecScopeInputT E f fm fv cs rm where
  nobody := b.nobody
  clT := b.clT
  elim := b.a.policy
  arity := t.hm ▸ b.a.recursorArity
  stored := recStored_of_bundle b t.href t.hm t.hls t.hpar t.hidx t.hminor
  u := b.u
  hT := t.hT
  lvl := b.lvl

/-- per-ctor `CtorScopeInputT` from the walk: the ctor's `ctors`-index, its
    class, and the transports at its extracted bundle. -/
noncomputable def envWfT_group_ctorScopeInput {E E' : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {fv : FamViewT fm}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hrc : RecursorAdmissionClass)
    (k : Nat) {r : Nat} {cm : CheckedMember}
    (hk : ctors[k]? = some (r, cm))
    (hcm : cm.mclass = .constructorM)
    (t : CtorScopeTransports E f fm fv
      (envWfT_group_ctorBundle hmem hrc (k + 1)
        (ctorEntry_getElem_of _ _ hk) hcm).2) :
    CtorScopeInputT E f fm fv cm :=
  ctorScopeInput_of_transports
    (envWfT_group_ctorBundle hmem hrc (k + 1)
      (ctorEntry_getElem_of _ _ hk) hcm).2 t

/-- the recursor's `RecScopeInputT` from the walk + transports. -/
noncomputable def envWfT_group_recScopeInput {E E' : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {fv : FamViewT fm}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    (cs : List (GroupCtorT E f fm fv))
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hcls : rm.mclass = .recursorM)
    (t : RecScopeTransports E f fm fv cs
      (envWfT_group_recBundle hmem (ctors.length + 1)
        (lastEntry_getElem _ _ _) hcls).2) :
    RecScopeInputT E f fm fv cs rm :=
  recScopeInput_of_bundle
    (envWfT_group_recBundle hmem (ctors.length + 1)
      (lastEntry_getElem _ _ _) hcls).2 t

/-- the remaining group evidence, quantified over the extracted family
    view: `htel`, per-ctor transports, the recursor's record, and the
    layout/profile clauses, all at `fv = famViewT_of v hm hp`. -/
structure GroupScopeEvidence (E : ResolvedEnv) {A : ResolvedEnv}
    (v : PolicyFamilyView A) {fm : CheckedMember} (hm : v.member = fm)
    (hp : UniformProp v.resultLevel ∨ UniformType v.resultLevel)
    (f : Nat) (ctors : List (Nat × CheckedMember)) (rr : Nat)
    (rm : CheckedMember) : Type where
  htel : TelTyT E fm.arity []
    ((famViewT_of v hm hp).params ++ (famViewT_of v hm hp).indices)
  input : (x : Nat × CheckedMember) → x ∈ ctors →
    CtorScopeInputT E f fm (famViewT_of v hm hp) x.2
  hrefs : ctors.map Prod.fst = List.range' (f + 1) ctors.length
  rinput : RecScopeInputT E f fm (famViewT_of v hm hp)
    (ctorList_of (famViewT_of v hm hp) ctors input) rm
  hcls : rm.mclass = .recursorM
  hrr : rr = f + 1 + ctors.length
  hprof : GroupProfileT (groupRecT_of hcls rinput)

/-- THE TARGET, `EnvWfT.group` side: the group's structured scope from its
    `GroupMembersT` evidence plus the remaining transports. `hmem` supplies
    the family's view (for `fv`); `hrc` is the named class-case obligation;
    `ev` is every other remaining obligation at that view. -/
theorem groupInScopeT_of_envWfT_group {E E' : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)} {rr : Nat}
    {rm : CheckedMember}
    (hfam : fm.mclass = .inductiveM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hrc : RecursorAdmissionClass)
    (ev : ∀ {P : ResolvedEnv}
        (v : PolicyFamilyView (extendEnv P f fm)) (href : v.ref = f)
        (hm : v.member = fm)
        (hp : UniformProp v.resultLevel ∨ UniformType v.resultLevel),
      GroupScopeEvidence E v hm hp f ctors rr rm) :
    Nonempty (GroupInScopeT E f fm ctors rr rm) := by
  obtain ⟨P, v, href, hm, hp⟩ :=
    envWfT_group_familyView hmem (head_getElem _ _) hfam
  have e := ev v href hm hp
  exact groupInScopeT_of (famViewT_of v hm hp) e.htel e.input e.hrefs
    e.rinput e.hcls e.hrr (famViewT_levelBounded v hm hp) e.hprof

/-- `EnvWfT.InScope` from a per-group scope producer. -/
theorem envWfT_inScope_of_groups {E : ResolvedEnv} (hW : EnvWfT E)
    (hgs : ∀ {E' : ResolvedEnv} {f : Nat} {fm : CheckedMember}
        {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
        {E'' : ResolvedEnv},
        GroupMembersT (extendEnv E' f fm) E'
          ((f, fm) :: ctors ++ [(rr, rm)]) E'' →
        Nonempty (GroupInScopeT E' f fm ctors rr rm)) :
    hW.InScope := by
  induction hW with
  | empty => exact True.intro
  | «axiom» _ _ _ _ _ _ _ _ _ ih => exact ih
  | definition _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | thm _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | «opaque» _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | group E f fm ctors rr rm _ hE hfam hctors hrec hmem ih =>
      exact ⟨ih, hgs hmem⟩

end Rcic.Declarative
