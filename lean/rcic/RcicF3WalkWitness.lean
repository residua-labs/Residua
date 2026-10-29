import rcic.RcicTypedGroupPins

/-!
# F3 coverage: PendW witness — the constructor's view and the recursor's view of one family disagree

`V : Prop → Type`, `mk : Π (p : Prop), V p`. The family and the constructor are admitted with the
PARAMETRIC split (`p` a parameter); the recursor is admitted with the INDEXED split (`p` an index,
revealed by `mk`'s field). The three splits decompose the same stored types.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative

/-- `V : Prop → Type`. -/
def pwV : CheckedMember := ⟨.inductiveM, 0, .pi (.sort .zero) (.sort (.succ .zero)), none⟩

/-- `mk : Π (p : Prop), V p`. -/
def pwMk : CheckedMember := ⟨.constructorM, 0, .pi (.sort .zero) (.app (.const 0 []) (.bvar 0)), none⟩

def pwFamOnly : ResolvedEnv := extendEnv emptyEnv 0 pwV
def pwPrefix : ResolvedEnv := extendEnv pwFamOnly 1 pwMk

/-- the parametric view of the family: `p` is a parameter. -/
def pwFamView1 (E : ResolvedEnv) (h : E.members 0 = some pwV) : PolicyFamilyView E where
  ref := 0
  member := pwV
  present := h
  hasClass := rfl
  parameters := [.sort .zero]
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort _ .zero }

/-- the indexed view of the family: `p` is an index. -/
def pwFamView2 (E : ResolvedEnv) (h : E.members 0 = some pwV) : PolicyFamilyView E where
  ref := 0
  member := pwV
  present := h
  hasClass := rfl
  parameters := []
  indices := [.sort .zero]
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort _ .zero }

/-- `mk` under the parametric view: one parameter, no field. -/
def pwMkView1 (E : ResolvedEnv) (h : E.members 0 = some pwV) :
    PolicyConstructorView E (pwFamView1 E h) pwMk where
  hasClass := rfl
  arity := rfl
  parameters := [.sort .zero]
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort _ .zero }
  parameterMirrors := fun i => match i with | ⟨0, _⟩ => Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

/-- `mk` under the indexed view: no parameter, one field, revealed as the result index. -/
def pwMkView2 (E : ResolvedEnv) (h : E.members 0 = some pwV) :
    PolicyConstructorView E (pwFamView2 E h) pwMk where
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
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort _ .zero }
  parameterMirrors := fun i => Fin.elim0 i
  noFamilyInIndices := fun e he => by
    simp only [List.mem_singleton] at he; subst he; rfl


def pwFamAdmitted : IndGroupAdmitted emptyEnv 0 pwV :=
  .family rfl (pwFamView1 pwFamOnly rfl) rfl rfl (Or.inr uniformType_succ_zero)

def pwMkAdmitted : IndGroupAdmitted pwFamOnly 1 pwMk :=
  .constructor (pwFamView1 pwFamOnly rfl) (pwMkView1 pwFamOnly rfl)
    rfl (ctorBefore_famOnly rfl rfl) (ctorContig_famOnly rfl rfl) (fun j => Fin.elim0 j)
    (fun j => Fin.elim0 j)

abbrev pwMotTy : Expr Nat := .pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort (.param 0)))

abbrev pwMinor : Expr Nat :=
  .pi (.sort .zero) (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 1 []) (.bvar 0)))

def pwRecType : Expr Nat :=
  .pi pwMotTy (.pi pwMinor (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0))
    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))

def pwRec : CheckedMember := ⟨.recursorM, 1, pwRecType, none⟩

def pwEnv : ResolvedEnv := extendEnv pwPrefix 2 pwRec

def pwGroupAdmitted : RecursorEliminationAdmitted pwPrefix 2 pwRec where
  family := pwFamView2 pwPrefix rfl
  constructors := [pwMk]
  constructorViews
    | ⟨0, _⟩ => pwMkView2 pwPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [pwMinor]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl


theorem pwMinorMatch : MinorPremisesMatch pwGroupAdmitted := by
  intro i
  have hlt : i.val < 1 := i.isLt
  have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp hlt)
  rw [hi]
  exact ⟨[.nonrecursive], 8, rfl, rfl⟩

def pwIotaIntro : IotaEquationTyped pwGroupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields, pwGroupAdmitted, pwMkView2, pwFamView2, pwRec,
    pwRecType, peelPis, piCount, lift, policyPi, iotaArgs, policyParameterLocals, foldApps]
  exact HasTy.app _ (.bvar 2) (.bvar 0) (.sort .zero)
    (.app (.app (.bvar 4) (.bvar 0)) (.app (.const 1 []) (.bvar 0)))
    (HasTy.bvar _ 2 _ rfl) (HasTy.bvar _ 0 _ rfl)


def pwShapes : Fin pwGroupAdmitted.constructors.length → List FieldShape
  | ⟨0, _⟩ => [.nonrecursive]

def pwIotaClause : IotaDescriptorClause pwPrefix pwGroupAdmitted where
  signatureOnly := rfl
  shapesAt := pwShapes
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => pwIotaIntro

def pwRecAdmitted : IndGroupAdmitted pwPrefix 2 pwRec :=
  .recursor pwGroupAdmitted rfl (census_famOne rfl rfl rfl)
    (fun i => match i with | ⟨0, _⟩ => fun _ => Or.inr ⟨uniformType_succ_zero, leN_refl _⟩)
    (fun i => match i with
      | ⟨0, _⟩ => fun j => match j with | ⟨0, _⟩ => ⟨.nonrecursive, 8, [], rfl⟩)
    pwMinorMatch pwIotaClause

/-- `V p : Type` for `p : Prop`. -/
def pwVAppTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h : E.members 0 = some pwV) {x : Expr Nat}
    (hx : HasTyT E n Γ x (.sort .zero)) : HasTyT E n Γ (.app (.const 0 []) x) (.sort (.succ .zero)) :=
  .app Γ _ x (.sort .zero) (.sort (.succ .zero)) (.const Γ 0 [] pwV h rfl rfl) hx

def pwFamTyT : HasTyT emptyEnv 0 [] pwV.mtype (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
  .pi [] _ _ _ _ (.sort [] .zero) (.sort _ (.succ .zero))

def pwMkTyT {E : ResolvedEnv} (h : E.members 0 = some pwV) :
    HasTyT E 0 [] pwMk.mtype (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] _ _ _ _ (.sort [] .zero) (pwVAppTyT h (.bvar _ 0 _ rfl))


theorem pwFamTyped1 (E : ResolvedEnv) (h : E.members 0 = some pwV) : FamilyTypedT (pwFamView1 E h) :=
  fun i => match i with | ⟨0, _⟩ => ⟨.sort [] .zero⟩

theorem pwFamTyped2 (E : ResolvedEnv) (h : E.members 0 = some pwV) : FamilyTypedT (pwFamView2 E h) :=
  fun i => match i with | ⟨0, _⟩ => ⟨.sort [] .zero⟩

theorem pwMkTyped1 (E : ResolvedEnv) (h : E.members 0 = some pwV) : CtorTypedT (pwMkView1 E h) :=
  ⟨fun i => match i with | ⟨0, _⟩ => ⟨.sort [] .zero⟩,
   fun i => match i with | ⟨0, _⟩ => ⟨.refl _ _⟩⟩

theorem pwMkTyped2 (E : ResolvedEnv) (h : E.members 0 = some pwV) : CtorTypedT (pwMkView2 E h) :=
  ⟨fun i => match i with | ⟨0, _⟩ => ⟨.sort [] .zero⟩, fun i => Fin.elim0 i⟩

theorem pwFamIsTyped : IndGroupTypedT pwFamAdmitted := pwFamTyped1 _ rfl

theorem pwMkIsTyped : IndGroupTypedT pwMkAdmitted := ⟨pwFamTyped1 _ rfl, pwMkTyped1 _ rfl⟩

theorem pwRecIsTyped : IndGroupTypedT pwRecAdmitted :=
  ⟨pwFamTyped2 _ rfl, fun i => match i with | ⟨0, _⟩ => pwMkTyped2 _ rfl,
   fun i => match i with | ⟨0, _⟩ => iotaEquationTypedT_of_check (synCheck _ _) rfl⟩


def pwMkAppTyT {Γ : LCtx} {x : Expr Nat} (hx : HasTyT pwPrefix 1 Γ x (.sort .zero)) :
    HasTyT pwPrefix 1 Γ (.app (.const 1 []) x) (.app (.const 0 []) x) :=
  .app Γ _ x (.sort .zero) (.app (.const 0 []) (.bvar 0)) (.const Γ 1 [] pwMk rfl rfl rfl) hx

def pwMotTyT : HasTyT pwPrefix 1 [] pwMotTy
    (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ (.param 0))))) :=
  .pi [] _ _ _ _ (.sort [] .zero) (.pi _ _ _ _ _ (pwVAppTyT rfl (.bvar _ 0 _ rfl)) (.sort _ (.param 0)))

abbrev pwRecCtx : LCtx :=
  [.assumption (.app (.const 0 []) (.bvar 0)), .assumption (.sort .zero), .assumption pwMinor,
    .assumption pwMotTy]

def pwRecTypeTyT : Σ u, HasTyT pwPrefix 1 [] pwRecType (.sort u) :=
  ⟨_, .pi [] _ _ _ _ pwMotTyT
    (.pi _ _ _ _ _
      (.pi _ _ _ _ _ (.sort _ .zero)
        (.app _ (.app (.bvar 1) (.bvar 0)) (.app (.const 1 []) (.bvar 0)) (.app (.const 0 []) (.bvar 0))
          (.sort (.param 0))
          (.app _ (.bvar 1) (.bvar 0) (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort (.param 0)))
            (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl))
          (pwMkAppTyT (.bvar _ 0 _ rfl))))
      (.pi _ _ _ _ _ (.sort _ .zero)
        (.pi _ _ _ _ _ (pwVAppTyT rfl (.bvar _ 0 _ rfl))
          (.app _ (.app (.bvar 3) (.bvar 1)) (.bvar 0) (.app (.const 0 []) (.bvar 1)) (.sort (.param 0))
            (.app _ (.bvar 3) (.bvar 1) (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort (.param 0)))
              (.bvar pwRecCtx 3 _ rfl) (.bvar pwRecCtx 1 _ rfl))
            (.bvar pwRecCtx 0 _ rfl)))))⟩


def pwMembersT :
    GroupMembersT (extendEnv emptyEnv 0 pwV) emptyEnv [(0, pwV), (1, pwMk), (2, pwRec)] pwEnv :=
  .cons _ 0 pwV _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    pwFamAdmitted PUnit.unit _ pwFamTyT (fun h => absurd h (by decide))
    pwFamIsTyped
    (.cons _ 1 pwMk _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      pwMkAdmitted PUnit.unit _ (pwMkTyT rfl) (fun _ => ⟨pwMkTyT rfl⟩)
      pwMkIsTyped
      (.cons _ 2 pwRec _ _ rfl rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl rfl
        pwRecAdmitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ pwRecTypeTyT.2 (fun h => absurd h (by decide))
        pwRecIsTyped (.nil _)))

/-- The witness: an admitted environment, one group, whose constructor and recursor views of
    the family split `Prop → Type` at different places. -/
def pwEnvWfT : EnvWfT pwEnv :=
  .group emptyEnv 0 pwV [(1, pwMk)] 2 pwRec pwEnv .empty rfl
    (fun c hc => by simp at hc; subst hc; rfl) rfl pwMembersT

end Rcic.Declarative
#print axioms Rcic.Declarative.pwEnvWfT
