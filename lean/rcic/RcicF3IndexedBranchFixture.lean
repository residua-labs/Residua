import rcic.RcicTypedGroupPins
import rcic.RcicTypedConv
import rcic.RcicF3IndexedFieldBounds
import rcic.RcicF3IndexedBranchDomain
import rcic.RcicF3PointwiseRole

/-!
# A singleton Prop group with an indexed depth-three recursive field

The synthetic group at refs 0/1/2 is

    Branch (p : Prop) (x : Prop) : Prop
    intro (p x : Prop)
      (g : (y : Prop) → (y → (∀ Q : Prop, Q)) → x → Branch p y) : Branch p x

The parameter and recursive result index are retained separately. The
constructor's x field is revealed by result index bvar1; g is a proof and
is admitted as recursive 3. The actual recursor retains the extra motive
universe and its executable minor/schema contains all three IH binders.

Admission is constructed from stored types, direct view typings, the
derived minor and iota schema, typed iota, and GroupMembersT. The complete
indexed bound quantifies over every possible RecNode of this group.
The separate semantic domain witness makes the selected root child tuple
inhabited; this file does not yet claim a candidate-root Eval producer
instance, modern iota, an imported environment, or a W/D check pass.

The complete declaration inventory is checked by RcicF3AIndexedPropSeal.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000


namespace Rcic.Declarative.IndexedBranchFixture

open Rcic.Declarative
open Rcic.F3 Rcic.F3.PSet

noncomputable abbrev bot : Expr Nat := IndexedBranchDomain.bot
noncomputable abbrev neg (y : Expr Nat) : Expr Nat := .pi y bot
noncomputable abbrev famApp (p x : Expr Nat) : Expr Nat :=
  foldApps (.const 0 []) [p, x]
noncomputable abbrev introApp (p x g : Expr Nat) : Expr Nat :=
  foldApps (.const 1 []) [p, x, g]

/-- The original field is under [x,p]. -/
noncomputable def field : Expr Nat :=
  .pi (.sort .zero)
    (.pi (neg (.bvar 0))
      (.pi (.bvar 2) (famApp (.bvar 4) (.bvar 2))))

noncomputable def famMember : CheckedMember :=
  ⟨.inductiveM, 0,
    .pi (.sort .zero) (.pi (.sort .zero) (.sort .zero)), none⟩

noncomputable def introMember : CheckedMember :=
  ⟨.constructorM, 0,
    .pi (.sort .zero) (.pi (.sort .zero)
      (.pi field (famApp (.bvar 2) (.bvar 1)))), none⟩

noncomputable def famOnly : ResolvedEnv := extendEnv emptyEnv 0 famMember
noncomputable def groupPrefix : ResolvedEnv := extendEnv famOnly 1 introMember

noncomputable abbrev botSort : Level := .imax (.succ .zero) .zero
noncomputable abbrev negSort : Level := .imax .zero botSort
noncomputable abbrev fieldSort : Level :=
  .imax (.succ .zero) (.imax negSort (.imax .zero .zero))
noncomputable abbrev introSort : Level :=
  .imax (.succ .zero) (.imax (.succ .zero) (.imax fieldSort .zero))

noncomputable def botTy {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTy E n Γ bot (.sort botSort) :=
  .pi Γ (.sort .zero) (.succ .zero) (.bvar 0) .zero
    (.sort Γ .zero) (.bvar _ 0 _ rfl)

noncomputable def botTyT {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTyT E n Γ bot (.sort botSort) :=
  .pi Γ (.sort .zero) (.succ .zero) (.bvar 0) .zero
    (.sort Γ .zero) (.bvar _ 0 _ rfl)

noncomputable def negTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (y : Expr Nat) (hy : HasTy E n Γ y (.sort .zero)) :
    HasTy E n Γ (neg y) (.sort negSort) :=
  .pi Γ y .zero bot botSort hy (botTy _)

noncomputable def negTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (y : Expr Nat) (hy : HasTyT E n Γ y (.sort .zero)) :
    HasTyT E n Γ (neg y) (.sort negSort) :=
  .pi Γ y .zero bot botSort hy (botTyT _)

noncomputable def famAppTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h : E.members 0 = some famMember) (p x : Expr Nat)
    (hp : HasTy E n Γ p (.sort .zero))
    (hx : HasTy E n Γ x (.sort .zero)) :
    HasTy E n Γ (famApp p x) (.sort .zero) :=
  .app Γ _ x (.sort .zero) (.sort .zero)
    (.app Γ (.const 0 []) p (.sort .zero)
      (.pi (.sort .zero) (.sort .zero))
      (.const Γ 0 [] famMember h rfl (fun _ h => nomatch h)) hp) hx

noncomputable def famAppTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h : E.members 0 = some famMember) (p x : Expr Nat)
    (hp : HasTyT E n Γ p (.sort .zero))
    (hx : HasTyT E n Γ x (.sort .zero)) :
    HasTyT E n Γ (famApp p x) (.sort .zero) :=
  .app Γ _ x (.sort .zero) (.sort .zero)
    (.app Γ (.const 0 []) p (.sort .zero)
      (.pi (.sort .zero) (.sort .zero))
      (.const Γ 0 [] famMember h rfl rfl) hp) hx

noncomputable def fieldTy {E : ResolvedEnv} {n : Nat}
    (h : E.members 0 = some famMember) :
    HasTy E n [.assumption (.sort .zero), .assumption (.sort .zero)]
      field (.sort fieldSort) :=
  .pi _ _ _ _ _ (.sort _ .zero)
    (.pi _ _ _ _ _ (negTy (.bvar 0) (.bvar _ 0 _ rfl))
      (.pi _ _ _ _ _ (.bvar _ 2 _ rfl)
        (famAppTy h (.bvar 4) (.bvar 2)
          (.bvar _ 4 _ rfl) (.bvar _ 2 _ rfl))))

noncomputable def fieldTyT {E : ResolvedEnv} {n : Nat}
    (h : E.members 0 = some famMember) :
    HasTyT E n [.assumption (.sort .zero), .assumption (.sort .zero)]
      field (.sort fieldSort) :=
  .pi _ _ _ _ _ (.sort _ .zero)
    (.pi _ _ _ _ _ (negTyT (.bvar 0) (.bvar _ 0 _ rfl))
      (.pi _ _ _ _ _ (.bvar _ 2 _ rfl)
        (famAppTyT h (.bvar 4) (.bvar 2)
          (.bvar _ 4 _ rfl) (.bvar _ 2 _ rfl))))

noncomputable def familyView (E : ResolvedEnv) (h : E.members 0 = some famMember) :
    PolicyFamilyView E where
  ref := 0
  member := famMember
  present := h
  hasClass := rfl
  parameters := [.sort .zero]
  indices := [.sort .zero]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      by_cases h0 : j.val = 0
      · have hj : j = ⟨0, by decide⟩ := Fin.ext h0
        subst j
        exact HasTy.sort [] .zero
      · have hlt : j.val < 2 := j.isLt
        have hj : j = ⟨1, by decide⟩ := by
          apply Fin.ext
          change j.val = 1
          omega
        subst j
        exact HasTy.sort _ .zero
  }

noncomputable def introView (E : ResolvedEnv) (h : E.members 0 = some famMember) :
    PolicyConstructorView E (familyView E h) introMember where
  hasClass := rfl
  arity := rfl
  parameters := [.sort .zero]
  fields := [.sort .zero, field]
  resultIndices := [.bvar 1]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j => if j.val = 2 then fieldSort else .succ .zero
    bounded := fun j => by
      change levelBounded 0 (if j.val = 2 then fieldSort else .succ .zero) = true
      split <;> rfl
    hasType := fun j => by
      by_cases h0 : j.val = 0
      · have hj : j = ⟨0, by decide⟩ := Fin.ext h0
        subst j
        exact HasTy.sort [] .zero
      · by_cases h1 : j.val = 1
        · have hj : j = ⟨1, by decide⟩ := Fin.ext h1
          subst j
          exact HasTy.sort _ .zero
        · have hlt : j.val < 3 := j.isLt
          have hj : j = ⟨2, by decide⟩ := by
            apply Fin.ext
            change j.val = 2
            omega
          subst j
          exact fieldTy h
  }
  parameterMirrors := fun j => by
    have hj : j = ⟨0, by decide⟩ := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
    subst j
    exact Conv.refl [] (.sort .zero)
  noFamilyInIndices := fun e he => by
    cases List.mem_singleton.mp he
    rfl

theorem field_prop : UniformProp fieldSort := fun _ => rfl

theorem intro_safe {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    (introView E h).AllFieldsSafe := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr (List.mem_singleton.mpr rfl)
  | ⟨1, _⟩ => exact Or.inl field_prop

theorem intro_fields {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    CtorFieldsPermitted (introView E h) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 32, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.recursive 3, 8, [.bvar 2], by
      change fieldAnalyze E 8 0 0 1 1 2 field = .permitted (.recursive 3) [.bvar 2]
      simp [fieldAnalyze, field, famApp, foldApps, bot, IndexedBranchDomain.bot, neg,
        piTelescopeFuel, whnfFuel, appsSpine, domainsContainFuel,
        containsFamilyFuel, properFamilyFuel, exactParamLocals,
        indicesCleanFuel, familyIdx, transparentBody, h, famMember, transparent]⟩

noncomputable def famAdmitted : IndGroupAdmitted emptyEnv 0 famMember :=
  .family rfl (familyView famOnly rfl) rfl rfl (Or.inl (fun _ => rfl))

noncomputable def introAdmitted : IndGroupAdmitted famOnly 1 introMember :=
  .constructor (familyView famOnly rfl) (introView famOnly rfl) rfl
    (ctorBefore_famOnly rfl rfl) (ctorContig_famOnly rfl rfl)
    (fun _ => Or.inl (fun _ => rfl)) (intro_fields rfl)

/-- Under the single original parameter p. -/
noncomputable abbrev motiveTy : Expr Nat :=
  .pi (.sort .zero)
    (.pi (famApp (.bvar 1) (.bvar 0)) (.sort (.param 0)))

/-- The executable IH is under [g,x,M,p]. -/
noncomputable abbrev ihTy : Expr Nat :=
  .pi (.sort .zero)
    (.pi (neg (.bvar 0))
      (.pi (.bvar 3)
        (.app (.app (.bvar 5) (.bvar 2))
          (foldApps (.bvar 3) [.bvar 2, .bvar 1, .bvar 0]))))

/-- Under [M,p], with x then g then the actual three-binder IH. -/
noncomputable abbrev minorTy : Expr Nat :=
  .pi (.sort .zero)
    (.pi (Rcic.Declarative.lift 1 1 field)
      (.pi ihTy
        (.app (.app (.bvar 3) (.bvar 2))
          (introApp (.bvar 4) (.bvar 2) (.bvar 1)))))

/-- The semantic helper's domains are the actual executable reader's
domains after inserting the motive and the recursive field value. -/
theorem depth3_reads :
    piTelescopeFuel groupPrefix 32 (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 1 1 field)) =
      some (IndexedBranchDomain.domains,
        foldApps (.const 0 []) IndexedBranchDomain.arguments) ∧
    funIHType groupPrefix 32 1 (Rcic.Declarative.lift 1 1 field) (.bvar 1) 3 = some ihTy :=
  ⟨rfl, rfl⟩

noncomputable def recType : Expr Nat :=
  .pi (.sort .zero)
    (.pi motiveTy (.pi minorTy
      (.pi (.sort .zero)
        (.pi (famApp (.bvar 3) (.bvar 0))
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))

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
  | ⟨0, _⟩ => exact ⟨[.nonrecursive, .recursive 3], 32, rfl, rfl⟩

noncomputable abbrev iotaCtx : LCtx :=
  [.assumption (Rcic.Declarative.lift 1 3 field), .assumption (.sort .zero),
    .assumption (.sort .zero), .assumption minorTy,
    .assumption motiveTy, .assumption (.sort .zero)]

/-- At [h,n,y,g,x,suppliedIndex,minor,M,p], retain all recursive arguments. -/
noncomputable abbrev iotaCall : Expr Nat :=
  .lam (.sort .zero)
    (.lam (neg (.bvar 0))
      (.lam (.bvar 3)
        (foldApps (.const 2 [.param 0])
          [.bvar 8, .bvar 7, .bvar 6, .bvar 2,
            foldApps (.bvar 3) [.bvar 2, .bvar 1, .bvar 0]])))

noncomputable abbrev iotaBody : Expr Nat :=
  foldApps (.bvar 3) [.bvar 1, .bvar 0, iotaCall]
noncomputable abbrev iotaTarget : Expr Nat :=
  .app (.app (.bvar 4) (.bvar 1))
    (introApp (.bvar 5) (.bvar 1) (.bvar 0))

theorem equation_shape :
    equationDoms groupAdmitted ⟨0, by decide⟩ =
      some [.sort .zero, motiveTy, minorTy, .sort .zero,
        .sort .zero, Rcic.Declarative.lift 1 3 field] ∧
    iotaSchemaAt groupAdmitted ⟨0, by decide⟩ 32
      [.nonrecursive, .recursive 3] = some iotaBody ∧
    iotaEquationType groupAdmitted ⟨0, by decide⟩ = iotaTarget :=
  ⟨rfl, rfl, rfl⟩

noncomputable def recHead {Γ : LCtx} :
    HasTy env 1 Γ (.const 2 [.param 0]) recType := by
  refine HasTy.const Γ 2 [.param 0] recMember rfl rfl ?_
  intro l hl
  have hl' : l = .param 0 := by simpa using hl
  subst hl'
  exact ⟨0, Or.inl rfl⟩

/-- Direct untyped admission derivation; no conversion collapse is used. -/
noncomputable def iotaBodyTy : HasTy env 1 iotaCtx iotaBody iotaTarget := by
  let Γy := LocalDecl.assumption (.sort .zero) :: iotaCtx
  let Γn := LocalDecl.assumption (neg (.bvar 0)) :: Γy
  let Γh := LocalDecl.assumption (.bvar 3) :: Γn
  have hm : HasTy env 1 iotaCtx (.bvar 3) (Rcic.Declarative.lift 0 4 minorTy) :=
    .bvar _ 3 _ rfl
  have hx : HasTy env 1 iotaCtx (.bvar 1) (.sort .zero) := .bvar _ 1 _ rfl
  have hg : HasTy env 1 iotaCtx (.bvar 0) (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 1 3 field)) :=
    .bvar _ 0 _ rfl
  have hy : HasTy env 1 Γy (.bvar 0) (.sort .zero) := .bvar _ 0 _ rfl
  have hneg : HasTy env 1 Γy (neg (.bvar 0)) (.sort negSort) := negTy _ hy
  have hxt : HasTy env 1 Γn (.bvar 3) (.sort .zero) := .bvar _ 3 _ rfl
  have hp' : HasTy env 1 Γh (.bvar 8) (.sort .zero) := .bvar _ 8 _ rfl
  have hM' : HasTy env 1 Γh (.bvar 7) (Rcic.Declarative.lift 0 8 motiveTy) := .bvar _ 7 _ rfl
  have hm' : HasTy env 1 Γh (.bvar 6) (Rcic.Declarative.lift 0 7 minorTy) := .bvar _ 6 _ rfl
  have hy' : HasTy env 1 Γh (.bvar 2) (.sort .zero) := .bvar _ 2 _ rfl
  have hg' : HasTy env 1 Γh (.bvar 3) (Rcic.Declarative.lift 0 4 (Rcic.Declarative.lift 1 3 field)) :=
    .bvar _ 3 _ rfl
  have hn' : HasTy env 1 Γh (.bvar 1) (neg (.bvar 2)) := .bvar _ 1 _ rfl
  have hx' : HasTy env 1 Γh (.bvar 0) (.bvar 4) := .bvar _ 0 _ rfl
  exact HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ hm hx) hg)
    (HasTy.lam _ (.sort .zero) (.succ .zero) _ _ (.sort _ .zero)
      (HasTy.lam _ (neg (.bvar 0)) negSort _ _ hneg
        (HasTy.lam _ (.bvar 3) .zero _ _ hxt
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _
              (HasTy.app _ _ _ _ _
                (HasTy.app _ _ _ _ _
                  (HasTy.app _ _ _ _ _ recHead hp') hM') hm') hy')
            (HasTy.app _ _ _ _ _
              (HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ hg' hy') hn') hx')))))

noncomputable def iotaLegacy : IotaEquationTyped groupAdmitted ⟨0, by decide⟩ 32
    [.nonrecursive, .recursive 3] := by
  unfold IotaEquationTyped
  rw [equation_shape.1, equation_shape.2.1]
  exact iotaBodyTy

noncomputable def iotaClause : IotaDescriptorClause groupPrefix groupAdmitted where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive, .recursive 3]
  fuelAt := fun _ => 32
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

noncomputable abbrev motiveSort : Level :=
  .imax (.succ .zero) (.imax .zero (.succ (.param 0)))
noncomputable abbrev ihSort : Level :=
  .imax (.succ .zero) (.imax negSort (.imax .zero (.param 0)))
noncomputable abbrev minorSort : Level :=
  .imax (.succ .zero) (.imax fieldSort (.imax ihSort (.param 0)))
noncomputable abbrev recSort : Level :=
  .imax (.succ .zero)
    (.imax motiveSort (.imax minorSort
      (.imax (.succ .zero) (.imax .zero (.param 0)))))

noncomputable def famTyT : HasTyT emptyEnv 0 [] famMember.mtype
    (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .pi [] _ _ _ _ (.sort [] .zero)
    (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))

noncomputable def introTyT {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    HasTyT E 0 [] introMember.mtype (.sort introSort) :=
  .pi [] _ _ _ _ (.sort [] .zero)
    (.pi _ _ _ _ _ (.sort _ .zero)
      (.pi _ _ _ _ _ (fieldTyT h)
        (famAppTyT h (.bvar 2) (.bvar 1)
          (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl))))

/-- The checked answer contains a typed derivation, not an asserted type. -/
noncomputable def recTyT : HasTyT groupPrefix 1 [] recType (.sort recSort) :=
  (tyAtC groupPrefix 1 64 [] recType (.sort recSort)).get (by
    have h : (tyAtC groupPrefix 1 64 [] recType (.sort recSort)).isSome = true := rfl
    exact h)

noncomputable def iotaBodyTyT : HasTyT env 1 iotaCtx iotaBody iotaTarget :=
  (tyAtC env 1 64 iotaCtx iotaBody iotaTarget).get (by
    have h : (tyAtC env 1 64 iotaCtx iotaBody iotaTarget).isSome = true := rfl
    exact h)

theorem familyTyped {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    FamilyTypedT (familyView E h) :=
  fun j => match j with
    | ⟨0, _⟩ => ⟨HasTyT.sort [] .zero⟩
    | ⟨1, _⟩ => ⟨HasTyT.sort _ .zero⟩

theorem constructorTyped {E : ResolvedEnv} (h : E.members 0 = some famMember) :
    CtorTypedT (introView E h) :=
  ⟨fun j => match j with
    | ⟨0, _⟩ => ⟨HasTyT.sort [] .zero⟩
    | ⟨1, _⟩ => ⟨HasTyT.sort _ .zero⟩
    | ⟨2, _⟩ => ⟨fieldTyT h⟩,
    fun j => match j with | ⟨0, _⟩ => ⟨TyConvT.refl [] (.sort .zero)⟩⟩

theorem famTyped : IndGroupTypedT famAdmitted := familyTyped rfl
theorem introTyped : IndGroupTypedT introAdmitted :=
  ⟨familyTyped rfl, constructorTyped rfl⟩

theorem iotaTyped : IotaEquationTypedT groupAdmitted ⟨0, by decide⟩ 32
    [.nonrecursive, .recursive 3] := by
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

/-- Every level and constant instance in the direct proof is bounded,
at every full valuation, including the extra motive coordinate. -/
theorem field_lokt (K σ : Nat → Nat) :
    LOKt σ 4 K (fieldTyT (n := 0) (E := famOnly) rfl) := by
  simp [fieldTyT, negTyT, botTyT, famAppTyT, LOKt, LevelsOK,
    fieldSort, negSort, botSort, evalTotal]

theorem intro_lokt (K σ : Nat → Nat) :
    LOKt σ 4 K (introTyT (E := famOnly) rfl) := by
  simp [introTyT, fieldTyT, negTyT, botTyT, famAppTyT, LOKt, LevelsOK,
    introSort, fieldSort, negSort, botSort, evalTotal]

/-- The revealed x row is ordinary data, while the unrevealed g row has
its actual uniformly-Prop typing in the full dependent groupPrefix. -/
theorem rows (K σ : Nat → Nat) :
    IndexedFieldBounds.Rows famOnly 0 σ K [.sort .zero]
      [.sort .zero, field] [.bvar 1] := by
  constructor
  · intro j
    match j with
    | ⟨0, _⟩ => exact ⟨.succ .zero, HasTyT.sort _ .zero,
        by change 1 ≤ 4; decide⟩
    | ⟨1, _⟩ => exact ⟨fieldSort, fieldTyT rfl, field_lokt K σ⟩
  · intro j hnot
    match j with
    | ⟨0, _⟩ => exact (hnot (List.mem_singleton.mpr rfl)).elim
    | ⟨1, _⟩ => exact ⟨fieldSort, rfl, fieldTyT rfl, field_lokt K σ⟩

theorem walk_bound (K : Nat → Nat) : WalkB2 K membersT := by
  refine ⟨True.intro, ?_, True.intro, True.intro⟩
  intro vs _ _ j
  match j with
  | ⟨0, _⟩ => exact ⟨HasTyT.sort [] .zero, by change 1 ≤ 4; decide⟩
  | ⟨1, _⟩ => exact ⟨HasTyT.sort _ .zero, by change 1 ≤ 4; decide⟩
  | ⟨2, _⟩ => exact ⟨fieldTyT rfl, field_lokt K (σOf vs)⟩

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

/-- The complete recursor fixes exactly one family parameter. -/
theorem family_info (nd : Node) :
    nd.a.family.parameters = [.sort .zero] ∧
    nd.a.family.indices = [.sort .zero] ∧
    nd.a.family.resultLevel = .zero := by
  have hs := nd.a.family.storedType
  rw [family_member nd] at hs
  obtain ⟨hds, hsort⟩ := policyPi_split_eq
    [.sort .zero, .sort .zero] _ _ _
    (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hs
  have hlevel : nd.a.family.resultLevel = .zero := by
    injection hsort with hl
    exact hl.symm
  have hp : nd.a.family.parameters = [.sort .zero] := by
    cases hps : nd.a.family.parameters with
    | nil =>
      have hi : nd.a.family.indices = [.sort .zero, .sort .zero] := by
        simpa only [hps, List.nil_append] using hds.symm
      have hr := nd.a.recursorType
      unfold policyRecursorType at hr
      rw [hps] at hr
      change Expr.pi (.sort .zero) _ =
        Expr.pi (policyMotiveType nd.a.family nd.a.policy) _ at hr
      have hm : (.sort .zero : Expr Nat) =
          policyMotiveType nd.a.family nd.a.policy := by
        injection hr
      unfold policyMotiveType at hm
      rw [hi] at hm
      change Expr.sort .zero = Expr.pi (.sort .zero) _ at hm
      exact Expr.noConfusion hm
    | cons A As =>
      have hds' : [Expr.sort .zero, Expr.sort .zero] =
          A :: (As ++ nd.a.family.indices) := by
        simpa only [hps, List.cons_append] using hds
      have hA : (.sort .zero : Expr Nat) = A := (List.cons.inj hds').1
      have htail : [Expr.sort .zero] = As ++ nd.a.family.indices :=
        (List.cons.inj hds').2
      cases As with
      | nil => simpa only [← hA] using hps
      | cons B Bs =>
        have htail' : [Expr.sort .zero] =
            B :: (Bs ++ nd.a.family.indices) := htail
        have hB : (.sort .zero : Expr Nat) = B :=
          (List.cons.inj htail').1
        have hr := nd.a.recursorType
        unfold policyRecursorType at hr
        rw [hps, ← hA, ← hB] at hr
        change Expr.pi (.sort .zero) (Expr.pi motiveTy _) =
          Expr.pi (.sort .zero) (Expr.pi (.sort .zero) _) at hr
        have hm : motiveTy = .sort .zero := by
          injection hr with _ hb
          injection hb
        exact Expr.noConfusion hm
  have hi : nd.a.family.indices = [.sort .zero] := by
    rw [hp] at hds
    change Expr.sort .zero :: [Expr.sort .zero] =
      Expr.sort .zero :: nd.a.family.indices at hds
    exact (List.cons.inj hds).2.symm
  exact ⟨hp, hi, hlevel⟩

theorem constructor_info (nd : Node) (i : Fin nd.a.constructors.length) :
    nd.a.constructors[i.val] = introMember ∧ i.val = 0 := by
  have hlen : nd.a.constructors.length = 1 :=
    node_ctors_length (ctors := [(1, introMember)]) nd rfl
  have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ
    (by simpa only [hlen] using i.isLt))
  have hm := node_ctor_member nd i
  exact ⟨Option.some.inj (hm.symm.trans (by rw [hi]; rfl)), hi⟩

/-- The full constructor type fixes both domains and the actual result index. -/
theorem constructor_view (nd : Node) (i : Fin nd.a.constructors.length) :
    (nd.a.constructorViews i).parameters = [.sort .zero] ∧
    (nd.a.constructorViews i).fields = [.sort .zero, field] ∧
    (nd.a.constructorViews i).resultIndices = [.bvar 1] := by
  have hpl : (nd.a.constructorViews i).parameters.length = 1 := by
    rw [(nd.a.constructorViews i).parameterCount, (family_info nd).1]
    rfl
  have hs := (nd.a.constructorViews i).storedType
  have hm : (nd.a.constructors[i.val]).mtype =
      policyPi ([.sort .zero] ++ [.sort .zero, field])
        (foldApps (.const 0 []) [.bvar 2, .bvar 1]) := by
    rw [(constructor_info nd i).1]
    rfl
  have hne := foldApps_ne_pi
    (.const nd.a.family.ref (policyFamilyLevels nd.a.family))
    (fun _ _ h => Expr.noConfusion h)
    (policyParameterLocals (nd.a.constructorViews i).parameters.length
      (nd.a.constructorViews i).fields.length ++
      (nd.a.constructorViews i).resultIndices)
  obtain ⟨hds, hresult⟩ := policyPi_split_eq _ _ _ _
    (fun _ _ h => Expr.noConfusion h) hne (hm.symm.trans hs)
  obtain ⟨hp, hf⟩ := List.append_inj hds (by rw [hpl]; rfl)
  have hlevels : policyFamilyLevels nd.a.family = [] := by
    unfold policyFamilyLevels
    rw [family_member nd]
    rfl
  rw [nd.fam, hlevels, hp.symm, hf.symm] at hresult
  change foldApps (.const 0 []) [.bvar 2, .bvar 1] =
    foldApps (.const 0 []) ([.bvar 2] ++
      (nd.a.constructorViews i).resultIndices) at hresult
  have hspine := congrArg appsSpine hresult
  have his : [Expr.bvar 2, Expr.bvar 1] =
      [Expr.bvar 2] ++ (nd.a.constructorViews i).resultIndices := by
    simpa only [appsSpine_foldApps, appsSpine, List.nil_append]
      using congrArg Prod.snd hspine
  change Expr.bvar 2 :: [Expr.bvar 1] =
    Expr.bvar 2 :: (nd.a.constructorViews i).resultIndices at his
  exact ⟨hp.symm, hf.symm, (List.cons.inj his).2.symm⟩

theorem constructor_bound (nd : Node) (K σ : Nat → Nat)
    (i : Fin nd.a.constructors.length) :
    ∃ (u : Level) (d : HasTyT famOnly nd.a.family.member.arity []
      (nd.a.constructors[i.val]).mtype (.sort u)), LOKt σ 4 K d := by
  rw [family_member nd, (constructor_info nd i).1]
  exact ⟨_, introTyT rfl, intro_lokt K σ⟩

theorem rows_at_node (nd : Node) (K σ : Nat → Nat)
    (i : Fin nd.a.constructors.length) :
    IndexedFieldBounds.Rows famOnly nd.a.family.member.arity σ K
      nd.a.family.parameters (nd.a.constructorViews i).fields
      (nd.a.constructorViews i).resultIndices := by
  rw [family_member nd, (family_info nd).1,
    (constructor_view nd i).2.1, (constructor_view nd i).2.2]
  exact rows K σ

/-- All possible nodes, constructor instances, and full valuations are covered. -/
theorem indexed_bound (K : Nat → Nat) :
    IndexedFieldBounds.BoundGIndexed K envWfT :=
  ⟨True.intro, fun nd i vs _ _ => constructor_bound nd K (σOf vs) i,
    walk_bound K, fun nd _ _ i vs _ => rows_at_node nd K (σOf vs) i⟩

/-- The original semantic domains are exactly those of the stored field. -/
theorem original_field : field =
    policyPi IndexedBranchDomain.originalDomains
      (foldApps (.const 0 []) IndexedBranchDomain.originalArguments) := rfl

noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PointwiseRole.table P envWfT

/-- Faithfulness is produced by the actual installer, independently of
successor soundness or an assumed evaluation package. -/
theorem table_faithful (P : Premises4) :
    EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities env)) P
      (table P) (NormRole.envCtx envWfT) (EvalRole.envPlan envWfT) env :=
  (PointwiseRole.table_spec P envWfT).2.1

theorem parameter_at_table (P : Premises4) :
    TelFits (mkM P (table P)) (σOf [1]) groupAdmitted.family.parameters ρ0
      [PropEvalSafeIndex.falseCode] :=
  ⟨IndexedBranchDomain.false_mem_sort P (table P) (σOf [1]) ρ0, True.intro⟩

theorem root_index_at_table (P : Premises4) :
    TelFits (mkM P (table P)) (σOf [1]) groupAdmitted.family.indices
      (push [PropEvalSafeIndex.falseCode] ρ0) [PropEvalSafeIndex.trueCode] :=
  ⟨IndexedBranchDomain.true_mem_sort P (table P) (σOf [1]) _, True.intro⟩

theorem leaf_index_at_table (P : Premises4) :
    TelFits (mkM P (table P)) (σOf [1]) groupAdmitted.family.indices
      (push [PropEvalSafeIndex.falseCode] ρ0) [PropEvalSafeIndex.falseCode] :=
  ⟨IndexedBranchDomain.false_mem_sort P (table P) (σOf [1]) _, True.intro⟩

/-- This fitting tuple belongs to the exact normalized child domains read
from the stored depth-three field, at the actual installed table and the
complete motive-level vector. No type is yet asserted for motive or g. -/
theorem selected_child_at_table (P : Premises4) (motive g : PSet.{4}) :
    TelFits (mkM P (table P)) (σOf [1]) IndexedBranchDomain.domains
      (IndexedBranchDomain.assignment PropEvalSafeIndex.falseCode
        PropEvalSafeIndex.trueCode motive g)
      [PropEvalSafeIndex.falseCode, pempty, pempty] :=
  IndexedBranchDomain.selected_fits P (table P) (σOf [1])
    PropEvalSafeIndex.falseCode motive g

/-- The finite leaf has no fitting children in that same table. -/
theorem leaf_at_table (P : Premises4) (motive g : PSet.{4})
    (zs : List PSet.{4}) :
    ¬ TelFits (mkM P (table P)) (σOf [1]) IndexedBranchDomain.domains
      (IndexedBranchDomain.assignment PropEvalSafeIndex.falseCode
        PropEvalSafeIndex.falseCode motive g) zs :=
  IndexedBranchDomain.leaf_no_children P (table P) (σOf [1])
    PropEvalSafeIndex.falseCode motive g zs

noncomputable def SyntaxWitness : Prop :=
  Nonempty (EnvWfT env) ∧
  (∀ K : Nat → Nat, IndexedFieldBounds.BoundGIndexed K envWfT) ∧
  groupAdmitted.family.parameters = [.sort .zero] ∧
  groupAdmitted.family.indices = [.sort .zero] ∧
  (groupAdmitted.constructorViews ⟨0, by decide⟩).fields = [.sort .zero, field] ∧
  (groupAdmitted.constructorViews ⟨0, by decide⟩).resultIndices = [.bvar 1] ∧
  groupAdmitted.policy = .anySort ∧
  iotaClause.shapesAt ⟨0, by decide⟩ = [.nonrecursive, .recursive 3] ∧
  field = policyPi IndexedBranchDomain.originalDomains
    (foldApps (.const 0 []) IndexedBranchDomain.originalArguments) ∧
  piTelescopeFuel groupPrefix 32 (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 1 1 field)) =
    some (IndexedBranchDomain.domains,
      foldApps (.const 0 []) IndexedBranchDomain.arguments) ∧
  funIHType groupPrefix 32 1 (Rcic.Declarative.lift 1 1 field) (.bvar 1) 3 = some ihTy

theorem syntax_witness : SyntaxWitness :=
  ⟨⟨envWfT⟩, indexed_bound, rfl, rfl, rfl, rfl, rfl, rfl,
    original_field, depth3_reads.1, depth3_reads.2⟩

theorem syntax_nonrefutable (P : Premises4) :
    ¬ (SyntaxWitness → (Premises4 → False)) :=
  fun h => h syntax_witness P

/-- Admission, the all-node bound, executable field/IH reads and the
nonempty actual child domain compose with the same Premises4. The IH's
semantic membership and candidate/evaluation producer instance are not
conjuncts of this source checkpoint and are not claimed by it. -/
noncomputable def Witness (P : Premises4) : Prop :=
  SyntaxWitness ∧ IndexedBranchDomain.FullWitness P ∧
  EvalRole.Faithful (PointwiseRole.familyValue (PointwiseRole.arities env)) P
    (table P) (NormRole.envCtx envWfT) (EvalRole.envPlan envWfT) env ∧
  TelFits (mkM P (table P)) (σOf [1]) groupAdmitted.family.parameters ρ0
    [PropEvalSafeIndex.falseCode] ∧
  TelFits (mkM P (table P)) (σOf [1]) groupAdmitted.family.indices
    (push [PropEvalSafeIndex.falseCode] ρ0) [PropEvalSafeIndex.trueCode] ∧
  TelFits (mkM P (table P)) (σOf [1]) groupAdmitted.family.indices
    (push [PropEvalSafeIndex.falseCode] ρ0) [PropEvalSafeIndex.falseCode] ∧
  ∀ motive g : PSet.{4},
    TelFits (mkM P (table P)) (σOf [1]) IndexedBranchDomain.domains
      (IndexedBranchDomain.assignment PropEvalSafeIndex.falseCode
        PropEvalSafeIndex.trueCode motive g)
      [PropEvalSafeIndex.falseCode, pempty, pempty]

theorem component_witness (P : Premises4) : Witness P :=
  ⟨syntax_witness, IndexedBranchDomain.full_witness P,
    table_faithful P, parameter_at_table P, root_index_at_table P,
    leaf_index_at_table P, selected_child_at_table P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.Declarative.IndexedBranchFixture

#print axioms Rcic.Declarative.IndexedBranchFixture.envWfT
#print axioms Rcic.Declarative.IndexedBranchFixture.iotaTyped
#print axioms Rcic.Declarative.IndexedBranchFixture.depth3_reads
#print axioms Rcic.Declarative.IndexedBranchFixture.rows
#print axioms Rcic.Declarative.IndexedBranchFixture.family_info
#print axioms Rcic.Declarative.IndexedBranchFixture.constructor_view
#print axioms Rcic.Declarative.IndexedBranchFixture.indexed_bound
#print axioms Rcic.Declarative.IndexedBranchFixture.table_faithful
#print axioms Rcic.Declarative.IndexedBranchFixture.selected_child_at_table
#print axioms Rcic.Declarative.IndexedBranchFixture.syntax_nonrefutable
#print axioms Rcic.Declarative.IndexedBranchFixture.component_witness
#print axioms Rcic.Declarative.IndexedBranchFixture.component_nonrefutable
