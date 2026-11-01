import rcic.RcicTypedGroupPins
import rcic.RcicF3IndexedFieldBounds

/-!
# A singleton indexed Prop fixture with a revealed ordinary field

The group at refs 0/1/2 is

    Wrap  : Prop → Prop
    intro : (P : Prop) → Wrap P
    rec   : (M : (P : Prop) → Wrap P → Sort u) →
            ((P : Prop) → M P (intro P)) → (P : Prop) → (h : Wrap P) → M P h

The constructor's Sort0 field is ordinary data of type Sort1 and is
revealed by the exact result index bvar0. Large elimination follows from
the existing singletonProp admission rule. This is a new synthetic
fixture, not an imported Lean environment or an Acc fixture.

Admission is built from actual member views, ordinary and typed iota
derivations, and GroupMembersT. The separate indexed bound is proved for
every RecNode of this admission, using stored-syntax rigidity. No admission,
check result, field comparator, or metadata uniqueness is assumed.
The exact declaration inventory includes private and generated declarations.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000


namespace Rcic.Declarative.IndexedWrapFixture

open Rcic.Declarative
open Rcic.F3.PSet

noncomputable abbrev famApp (p : Expr Nat) : Expr Nat := .app (.const 0 []) p
noncomputable abbrev introApp (p : Expr Nat) : Expr Nat := .app (.const 1 []) p

noncomputable def famMember : CheckedMember :=
  ⟨.inductiveM, 0, .pi (.sort .zero) (.sort .zero), none⟩

noncomputable def introMember : CheckedMember :=
  ⟨.constructorM, 0, .pi (.sort .zero) (famApp (.bvar 0)), none⟩

noncomputable def famOnly : ResolvedEnv := extendEnv emptyEnv 0 famMember
noncomputable def groupPrefix : ResolvedEnv := extendEnv famOnly 1 introMember

noncomputable def familyView (E : ResolvedEnv) (h : E.members 0 = some famMember) :
    PolicyFamilyView E where
  ref := 0
  member := famMember
  present := h
  hasClass := rfl
  parameters := []
  indices := [.sort .zero]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hj : j = ⟨0, by decide⟩ := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
      subst j
      exact HasTy.sort (n := 0) [] .zero
  }

noncomputable def introView (E : ResolvedEnv) (h : E.members 0 = some famMember) :
    PolicyConstructorView E (familyView E h) introMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.sort .zero]
  resultIndices := [.bvar 0]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hj : j = ⟨0, by decide⟩ := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
      subst j
      exact HasTy.sort (n := 0) [] .zero
  }
  parameterMirrors := fun j => j.elim0
  noFamilyInIndices := fun e he => by
    cases List.mem_singleton.mp he
    rfl

theorem intro_safe {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    (introView E h).AllFieldsSafe := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr (List.mem_singleton.mpr rfl)

theorem intro_fields {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    CtorFieldsPermitted (introView E h) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 8, [], rfl⟩

noncomputable def famAdmitted : IndGroupAdmitted emptyEnv 0 famMember :=
  .family rfl (familyView famOnly rfl) rfl rfl (Or.inl (fun _ => rfl))

noncomputable def introAdmitted : IndGroupAdmitted famOnly 1 introMember :=
  .constructor (familyView famOnly rfl) (introView famOnly rfl) rfl
    (ctorBefore_famOnly rfl rfl) (ctorContig_famOnly rfl rfl)
    (fun _ => Or.inl (fun _ => rfl)) (intro_fields rfl)

noncomputable abbrev motiveTy : Expr Nat :=
  .pi (.sort .zero) (.pi (famApp (.bvar 0)) (.sort (.param 0)))

noncomputable abbrev minorTy : Expr Nat :=
  .pi (.sort .zero)
    (.app (.app (.bvar 1) (.bvar 0)) (introApp (.bvar 0)))

noncomputable def recType : Expr Nat :=
  .pi motiveTy (.pi minorTy
    (.pi (.sort .zero) (.pi (famApp (.bvar 0))
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))

noncomputable def recMember : CheckedMember := ⟨.recursorM, 1, recType, none⟩
noncomputable def env : ResolvedEnv := extendEnv groupPrefix 2 recMember

noncomputable def groupAdmitted : RecursorEliminationAdmitted groupPrefix 2 recMember where
  family := familyView groupPrefix rfl
  constructors := [introMember]
  constructorViews := fun j => by
    have hj : j = ⟨0, by decide⟩ := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
    subst j
    exact introView groupPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [minorTy]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp (fun _ => rfl) rfl
    (fun i => match i with | ⟨0, _⟩ => intro_safe rfl)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem census : CtorCensus groupPrefix 0 2 := census_famOne rfl rfl rfl

theorem minor_match : MinorPremisesMatch groupAdmitted := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.nonrecursive], 8, rfl, rfl⟩

noncomputable abbrev iotaCtx : LCtx :=
  [.assumption (.sort .zero), .assumption (.sort .zero),
    .assumption minorTy, .assumption motiveTy]

noncomputable abbrev iotaBody : Expr Nat := .app (.bvar 2) (.bvar 0)
noncomputable abbrev iotaTarget : Expr Nat :=
  .app (.app (.bvar 3) (.bvar 0)) (introApp (.bvar 0))

theorem equation_shape :
    equationDoms groupAdmitted ⟨0, by decide⟩ =
      some [motiveTy, minorTy, .sort .zero, .sort .zero] ∧
    iotaSchemaAt groupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive] = some iotaBody ∧
    iotaEquationType groupAdmitted ⟨0, by decide⟩ = iotaTarget :=
  ⟨rfl, rfl, rfl⟩

noncomputable def iotaBodyTy : HasTy env 1 iotaCtx iotaBody iotaTarget :=
  .app iotaCtx (.bvar 2) (.bvar 0) (.sort .zero)
    (.app (.app (.bvar 4) (.bvar 0)) (introApp (.bvar 0)))
    (.bvar iotaCtx 2 _ rfl) (.bvar iotaCtx 0 _ rfl)

noncomputable def iotaLegacy : IotaEquationTyped groupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive] := by
  unfold IotaEquationTyped
  rw [equation_shape.1, equation_shape.2.1]
  exact iotaBodyTy

noncomputable def iotaClause : IotaDescriptorClause groupPrefix groupAdmitted where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed := fun j => by
    have hj : j = ⟨0, by decide⟩ := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
    subst j
    exact iotaLegacy

noncomputable def recAdmitted : IndGroupAdmitted groupPrefix 2 recMember :=
  .recursor groupAdmitted rfl census
    (fun i => match i with | ⟨0, _⟩ => fun _ => Or.inl (fun _ => rfl))
    (fun i => match i with | ⟨0, _⟩ => intro_fields rfl)
    minor_match iotaClause

noncomputable def famAppTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h : E.members 0 = some famMember) (p : Expr Nat)
    (hp : HasTyT E n Γ p (.sort .zero)) :
    HasTyT E n Γ (famApp p) (.sort .zero) :=
  .app Γ (.const 0 []) p (.sort .zero) (.sort .zero)
    (.const Γ 0 [] famMember h rfl rfl) hp

noncomputable def introAppTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h : E.members 1 = some introMember) (p : Expr Nat)
    (hp : HasTyT E n Γ p (.sort .zero)) :
    HasTyT E n Γ (introApp p) (famApp p) :=
  .app Γ (.const 1 []) p (.sort .zero) (famApp (.bvar 0))
    (.const Γ 1 [] introMember h rfl rfl) hp

noncomputable def motiveAppTyT {E : ResolvedEnv} {Γ : LCtx} (i : Nat) (p t : Expr Nat)
    (hm : lookupType Γ i = some motiveTy)
    (hp : HasTyT E 1 Γ p (.sort .zero))
    (ht : HasTyT E 1 Γ t (famApp p)) :
    HasTyT E 1 Γ (.app (.app (.bvar i) p) t) (.sort (.param 0)) :=
  .app Γ (.app (.bvar i) p) t (famApp p) (.sort (.param 0))
    (.app Γ (.bvar i) p (.sort .zero)
      (.pi (famApp (.bvar 0)) (.sort (.param 0))) (.bvar Γ i _ hm) hp) ht

noncomputable abbrev motiveSort : Level := .imax (.succ .zero) (.imax .zero (.succ (.param 0)))
noncomputable abbrev minorSort : Level := .imax (.succ .zero) (.param 0)
noncomputable abbrev recSort : Level :=
  .imax motiveSort (.imax minorSort (.imax (.succ .zero) (.imax .zero (.param 0))))

noncomputable def famTyT : HasTyT emptyEnv 0 [] famMember.mtype
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] _ _ _ _ (.sort [] .zero) (.sort _ .zero)

noncomputable def introTyT {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    HasTyT E 0 [] introMember.mtype (.sort (.imax (.succ .zero) .zero)) :=
  .pi [] _ _ _ _ (.sort [] .zero) (famAppTyT h (.bvar 0) (.bvar _ 0 _ rfl))

noncomputable def motiveTyT {Γ : LCtx} : HasTyT groupPrefix 1 Γ motiveTy (.sort motiveSort) :=
  .pi _ _ _ _ _ (.sort _ .zero)
    (.pi _ _ _ _ _ (famAppTyT rfl (.bvar 0) (.bvar _ 0 _ rfl))
      (.sort _ (.param 0)))

noncomputable def minorTyT : HasTyT groupPrefix 1 [.assumption motiveTy] minorTy (.sort minorSort) :=
  .pi _ _ _ _ _ (.sort _ .zero)
    (motiveAppTyT 1 (.bvar 0) (introApp (.bvar 0)) rfl (.bvar _ 0 _ rfl)
      (introAppTyT rfl (.bvar 0) (.bvar _ 0 _ rfl)))

noncomputable def recTyT : HasTyT groupPrefix 1 [] recType (.sort recSort) :=
  .pi _ _ _ _ _ motiveTyT
    (.pi _ _ _ _ _ minorTyT
      (.pi _ _ _ _ _ (.sort _ .zero)
        (.pi _ _ _ _ _ (famAppTyT rfl (.bvar 0) (.bvar _ 0 _ rfl))
          (motiveAppTyT 3 (.bvar 1) (.bvar 0) rfl
            (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl)))))

noncomputable def iotaBodyTyT : HasTyT env 1 iotaCtx iotaBody iotaTarget :=
  .app iotaCtx (.bvar 2) (.bvar 0) (.sort .zero)
    (.app (.app (.bvar 4) (.bvar 0)) (introApp (.bvar 0)))
    (.bvar iotaCtx 2 _ rfl) (.bvar iotaCtx 0 _ rfl)

theorem familyTyped {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    FamilyTypedT (familyView E h) :=
  fun j => match j with | ⟨0, _⟩ => ⟨.sort [] .zero⟩

theorem constructorTyped {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    CtorTypedT (introView E h) :=
  ⟨fun j => match j with | ⟨0, _⟩ => ⟨.sort [] .zero⟩, fun j => j.elim0⟩

theorem famTyped : IndGroupTypedT famAdmitted := familyTyped rfl
theorem introTyped : IndGroupTypedT introAdmitted := ⟨familyTyped rfl, constructorTyped rfl⟩

theorem iotaTyped : IotaEquationTypedT groupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive] := by
  unfold IotaEquationTypedT
  rw [equation_shape.1, equation_shape.2.1]
  exact ⟨iotaBodyTyT⟩

theorem recTyped : IndGroupTypedT recAdmitted :=
  ⟨familyTyped rfl,
    fun j => match j with | ⟨0, _⟩ => constructorTyped rfl,
    fun j => match j with | ⟨0, _⟩ => iotaTyped⟩

noncomputable def membersT : GroupMembersT famOnly emptyEnv
    [(0, famMember), (1, introMember), (2, recMember)] env :=
  .cons _ 0 famMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    famAdmitted PUnit.unit _ famTyT (fun h => nomatch h) famTyped
    (.cons _ 1 introMember _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
      introAdmitted PUnit.unit _ (introTyT rfl) (fun _ => ⟨introTyT rfl⟩) introTyped
      (.cons _ 2 recMember _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
        recAdmitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ recTyT
        (fun h => nomatch h) recTyped (.nil _)))

noncomputable def envWfT : EnvWfT env :=
  .group emptyEnv 0 famMember [(1, introMember)] 2 recMember env .empty rfl
    (fun c hc => by cases List.mem_singleton.mp hc; rfl) rfl membersT

/-- The original ordinary row and the exact revealed field, at every full
valuation. This does not use an all-fields Prop typing. -/
theorem rows (K σ : Nat → Nat) :
    IndexedFieldBounds.Rows famOnly 0 σ K [] [.sort .zero] [.bvar 0] := by
  constructor
  · intro j
    match j with
    | ⟨0, _⟩ => exact ⟨.succ .zero, HasTyT.sort [] .zero, by change 1 ≤ 4; decide⟩
  · intro j hnot
    match j with
    | ⟨0, _⟩ => exact (hnot (List.mem_singleton.mpr rfl)).elim

noncomputable abbrev Node := RecNode emptyEnv env 0 2 recMember

noncomputable def node : Node where
  E0 := groupPrefix
  a := groupAdmitted
  h14 := iotaClause
  fam := rfl
  fresh := rfl
  sub := fun _ _ h => h
  base := fun _ _ h => nomatch h
  h04 := census
  h07 := fun i => match i with | ⟨0, _⟩ => fun _ => Or.inl (fun _ => rfl)
  h12 := minor_match
  famTyped := recTyped.1
  ctorsTyped := recTyped.2.1
  u := recSort
  hT := recTyT

theorem family_member (nd : Node) : nd.a.family.member = famMember :=
  Option.some.inj ((node_fam_member nd).symm.trans rfl)

/-- The stored family type permits a parameter/index split in isolation.
The recursor's first domain excludes the parameter split here. -/
theorem family_info (nd : Node) :
    nd.a.family.parameters = [] ∧ nd.a.family.indices = [.sort .zero] ∧
    nd.a.family.resultLevel = .zero := by
  have hs := nd.a.family.storedType
  rw [family_member nd] at hs
  obtain ⟨hds, hsort⟩ := policyPi_split_eq [.sort .zero] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hs
  have hlevel : nd.a.family.resultLevel = .zero := by
    injection hsort with hl
    exact hl.symm
  have hp : nd.a.family.parameters = [] := by
    cases hps : nd.a.family.parameters with
    | nil => rfl
    | cons A As =>
      have hds' : [Expr.sort .zero] = A :: (As ++ nd.a.family.indices) := by
        simpa only [hps, List.cons_append] using hds
      have hA : (.sort .zero : Expr Nat) = A := (List.cons.inj hds').1
      have hr := nd.a.recursorType
      unfold policyRecursorType at hr
      rw [hps, ← hA] at hr
      change Expr.pi motiveTy _ = Expr.pi (.sort .zero) _ at hr
      have hm : motiveTy = .sort .zero := by injection hr
      exact Expr.noConfusion hm
  have hi : nd.a.family.indices = [.sort .zero] := by
    rw [hp, List.nil_append] at hds
    exact hds.symm
  exact ⟨hp, hi, hlevel⟩

theorem constructor_info (nd : Node) (i : Fin nd.a.constructors.length) :
    nd.a.constructors[i.val] = introMember ∧ i.val = 0 := by
  have hlen : nd.a.constructors.length = 1 :=
    node_ctors_length (ctors := [(1, introMember)]) nd rfl
  have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ
    (by simpa only [hlen] using i.isLt))
  have hm := node_ctor_member nd i
  exact ⟨Option.some.inj (hm.symm.trans (by rw [hi]; rfl)), hi⟩

/-- Every possible node view has the literal revealed ordinary field;
this is derived from the full stored type, not from the chosen view alone. -/
theorem constructor_view (nd : Node) (i : Fin nd.a.constructors.length) :
    (nd.a.constructorViews i).parameters = [] ∧
    (nd.a.constructorViews i).fields = [.sort .zero] ∧
    (nd.a.constructorViews i).resultIndices = [.bvar 0] := by
  have hpl : (nd.a.constructorViews i).parameters.length = 0 := by
    rw [(nd.a.constructorViews i).parameterCount, (family_info nd).1]
    rfl
  have hp := List.eq_nil_of_length_eq_zero hpl
  have hs := (nd.a.constructorViews i).storedType
  rw [hp, List.nil_append] at hs
  have hm : (nd.a.constructors[i.val]).mtype =
      policyPi [.sort .zero] (famApp (.bvar 0)) := by
    rw [(constructor_info nd i).1]
    rfl
  have hne := foldApps_ne_pi (.const nd.a.family.ref (policyFamilyLevels nd.a.family))
    (fun _ _ h => Expr.noConfusion h)
    (policyParameterLocals 0 (nd.a.constructorViews i).fields.length ++
      (nd.a.constructorViews i).resultIndices)
  obtain ⟨hfields, hresult⟩ := policyPi_split_eq _ _ _ _
    (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hs)
  have hlevels : policyFamilyLevels nd.a.family = [] := by
    unfold policyFamilyLevels
    rw [family_member nd]
    rfl
  rw [nd.fam, hlevels] at hresult
  have hresult' : famApp (.bvar 0) =
      foldApps (.const 0 []) (nd.a.constructorViews i).resultIndices := hresult
  have hspine := congrArg appsSpine hresult'
  rw [appsSpine_foldApps] at hspine
  have his : [Expr.bvar 0] = (nd.a.constructorViews i).resultIndices :=
    congrArg Prod.snd hspine
  exact ⟨hp, hfields.symm, his.symm⟩

theorem constructor_bound (nd : Node) (K σ : Nat → Nat)
    (i : Fin nd.a.constructors.length) :
    ∃ (u : Level) (d : HasTyT famOnly nd.a.family.member.arity []
      (nd.a.constructors[i.val]).mtype (.sort u)), LOKt σ 4 K d := by
  rw [family_member nd, (constructor_info nd i).1]
  refine ⟨_, introTyT rfl, ?_⟩
  change 1 ≤ 4 ∧ 0 ≤ 4 ∧ 1 ≤ 4 ∧ (LevelsOK σ (K 0) [] ∧ True)
  exact ⟨by decide, by decide, by decide, (fun _ h => nomatch h), True.intro⟩

theorem walk_bound (K : Nat → Nat) : WalkB2 K membersT := by
  refine ⟨True.intro, ?_, True.intro, True.intro⟩
  intro vs _ _ j
  match j with
  | ⟨0, _⟩ => exact ⟨HasTyT.sort [] .zero, by change 1 ≤ 4; decide⟩

theorem rows_at_node (nd : Node) (K σ : Nat → Nat)
    (i : Fin nd.a.constructors.length) :
    IndexedFieldBounds.Rows famOnly nd.a.family.member.arity σ K
      nd.a.family.parameters (nd.a.constructorViews i).fields
      (nd.a.constructorViews i).resultIndices := by
  rw [family_member nd, (family_info nd).1,
    (constructor_view nd i).2.1, (constructor_view nd i).2.2]
  exact rows K σ

/-- Every node, every constructor instance, and every full syntax
valuation are covered; the motive universe is not truncated. -/
theorem indexed_bound (K : Nat → Nat) : IndexedFieldBounds.BoundGIndexed K envWfT :=
  ⟨True.intro, fun nd i vs _ _ => constructor_bound nd K (σOf vs) i,
    walk_bound K, fun nd _ _ i vs _ => rows_at_node nd K (σOf vs) i⟩

noncomputable def Witness : Prop :=
  Nonempty (EnvWfT env) ∧
  (∀ K : Nat → Nat, IndexedFieldBounds.BoundGIndexed K envWfT) ∧
  groupAdmitted.family.parameters = [] ∧
  groupAdmitted.family.indices = [.sort .zero] ∧
  (groupAdmitted.constructorViews ⟨0, by decide⟩).fields = [.sort .zero] ∧
  (groupAdmitted.constructorViews ⟨0, by decide⟩).resultIndices = [.bvar 0] ∧
  groupAdmitted.policy = .anySort

theorem component_witness : Witness :=
  ⟨⟨envWfT⟩, indexed_bound, rfl, rfl, rfl, rfl, rfl⟩

/-- Admission and bound pieces compose at the same explicit Premises4.
This neither supplies Premises4 unconditionally nor claims semantic iota. -/
theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness → (Premises4 → False)) := fun h => h component_witness P

end Rcic.Declarative.IndexedWrapFixture

#print axioms Rcic.Declarative.IndexedWrapFixture.envWfT
#print axioms Rcic.Declarative.IndexedWrapFixture.iotaTyped
#print axioms Rcic.Declarative.IndexedWrapFixture.rows
#print axioms Rcic.Declarative.IndexedWrapFixture.family_info
#print axioms Rcic.Declarative.IndexedWrapFixture.constructor_view
#print axioms Rcic.Declarative.IndexedWrapFixture.indexed_bound
#print axioms Rcic.Declarative.IndexedWrapFixture.component_witness
#print axioms Rcic.Declarative.IndexedWrapFixture.component_nonrefutable
