import rcic.RcicAnnAccCorrPin

/-!
# accpi — a PROP-valued Acc environment, admitted by `EnvWfT`

`pinAccEnvA` / `paEnvT` (`RcicAnnAccFrecPin`, `RcicAnnAccCorrPin`) is the TYPE-valued Acc row:
`AccT : Sort 0 → Sort 1`. Its majors are not proofs, so `irr` never identifies two of them and the
Abel–Coquand question (irr on the major + ι, unfolding the recursor indefinitely) does not arise
there. This module is the Prop-valued row of the same shape, over the same axiom `R` at `9`:

    AccP  : Π (x : Sort 0), Sort 0                                         (at 10)
    intro : Π (x : Sort 0), (Π (y : Sort 0), R y x → AccP y) → AccP x      (at 11)
    rec   : Π (M : Π x, AccP x → Sort u) (F : minor) (x : Sort 0) (t : AccP x), M x t   (at 12)

The constructor and recursor members are `paIntroT` / `paRecT` VERBATIM (their stored types do not
mention the family's sort); only the family member `accPFamT` differs (`Sort 0` result). The
recursor is admitted `AnySort` by the `singletonProp` branch of 05 §10: one constructor, field `x`
revealed as the bare result index, field `g` a proof (`Sort (imax 1 (imax 0 0)) =ₙ Sort 0`).

`closure_claim = 0`: a fixture, no row claim.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## §1 members and environments -/

/-- the Prop-valued family: `AccP : Π (x : Sort 0), Sort 0`. -/
def accPFamT : CheckedMember := ⟨.inductiveM, 0, .pi (.sort .zero) (.sort .zero), none⟩

/-- `R` (`paRelEnvT`) + `AccP` at `10`. -/
abbrev accPFamEnvT : ResolvedEnv := extendEnv paRelEnvT 10 accPFamT
/-- + `intro` at `11` (the `paIntroT` member, verbatim). -/
abbrev accPSupEnvT : ResolvedEnv := extendEnv accPFamEnvT 11 paIntroT
/-- + `rec` at `12` (the `paRecT` member, verbatim). -/
abbrev accPEnvT : ResolvedEnv := extendEnv accPSupEnvT 12 paRecT

/-- `AccP y` at `Sort 0`, so the field domain `Π (y:S0), R y x → AccP y` is a proof type:
    `Sort (imax 1 (imax 0 0))` (untyped judgment). -/
def accPFieldDomTy {E : ResolvedEnv} {n : Nat}
    (h9 : E.members 9 = some paRelT) (h10 : E.members 10 = some accPFamT) :
    HasTy E n [.assumption (.sort .zero)] paFieldDom
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  HasTy.pi _ (.sort .zero) (.succ .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1))
      (.app (.const 10 []) (.bvar 1)))
    (.imax .zero .zero)
    (HasTy.sort _ .zero)
    (HasTy.pi _ (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1)) .zero
      (.app (.const 10 []) (.bvar 1)) .zero
      (HasTy.app _ (.app (.const 9 []) (.bvar 0)) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTy.app _ (.const 9 []) (.bvar 0) (.sort .zero) (.pi (.sort .zero) (.sort .zero))
          (paRelConstTy h9)
          (HasTy.bvar _ 0 (.sort .zero) rfl))
        (HasTy.bvar _ 1 (.sort .zero) rfl))
      (HasTy.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTy.const _ 10 [] accPFamT h10 rfl (fun _ hx => nomatch hx))
        (HasTy.bvar _ 1 (.sort .zero) rfl)))

/-- the field domain in the typed judgment. -/
def accPFieldDomTyT {E : ResolvedEnv} {n : Nat}
    (h9 : E.members 9 = some paRelT) (h10 : E.members 10 = some accPFamT) :
    HasTyT E n [.assumption (.sort .zero)] paFieldDom
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  HasTyT.pi _ (.sort .zero) (.succ .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1))
      (.app (.const 10 []) (.bvar 1)))
    (.imax .zero .zero)
    (HasTyT.sort _ .zero)
    (HasTyT.pi _ (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1)) .zero
      (.app (.const 10 []) (.bvar 1)) .zero
      (HasTyT.app _ (.app (.const 9 []) (.bvar 0)) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTyT.app _ (.const 9 []) (.bvar 0) (.sort .zero) (.pi (.sort .zero) (.sort .zero))
          (HasTyT.const _ 9 [] paRelT h9 rfl rfl)
          (HasTyT.bvar _ 0 (.sort .zero) rfl))
        (HasTyT.bvar _ 1 (.sort .zero) rfl))
      (HasTyT.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTyT.const _ 10 [] accPFamT h10 rfl rfl)
        (HasTyT.bvar _ 1 (.sort .zero) rfl)))

/-! ## §2 views -/

/-- the family's view: no params, one index `Sort 0`, result `Sort 0`. -/
def accPFamViewT (E : ResolvedEnv) (h : E.members 10 = some accPFamT) :
    PolicyFamilyView E where
  ref := 10
  member := accPFamT
  present := h
  hasClass := rfl
  parameters := []
  indices := [.sort .zero]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j => match j with | ⟨0, _⟩ => .succ .zero
    bounded := fun j => match j with | ⟨0, _⟩ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort (n := 0) [] .zero
  }

/-- `intro`'s view: fields `[x : S0, g : Π y, R y x → AccP y]`, result index `x`. -/
def accPIntroViewT (E : ResolvedEnv) (h9 : E.members 9 = some paRelT)
    (h10 : E.members 10 = some accPFamT) :
    PolicyConstructorView E (accPFamViewT E h10) paIntroT where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.sort .zero, paFieldDom]
  resultIndices := [.bvar 1]
  parameterCount := rfl
  indexCount := rfl
  storedType := by with_unfolding_all rfl
  domainsTyped := {
    levels := fun j => match j with
      | ⟨0, _⟩ => .succ .zero
      | ⟨1, _⟩ => .imax (.succ .zero) (.imax .zero .zero)
    bounded := fun j => match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    hasType := fun j => match j with
      | ⟨0, _⟩ => HasTy.sort (n := 0) [] .zero
      | ⟨1, _⟩ => accPFieldDomTy h9 h10
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun e he => by
    simp only [List.mem_singleton] at he
    subst he
    rfl

/-- a Prop family admits every field universe (05 §7, the `UniformProp` arm). -/
theorem accPIntroUniv {E : ResolvedEnv} {h9 : E.members 9 = some paRelT}
    {h10 : E.members 10 = some accPFamT} :
    FieldUniverseAdmitted (accPIntroViewT E h9 h10) :=
  fun _ => Or.inl (fun _ => rfl)

/-- both fields are SAFE (05 §10): `x` is the bare result index, `g`'s level is `0` at every
    valuation. This is what grants the Prop family large elimination. -/
theorem accPIntroSafe {E : ResolvedEnv} {h9 : E.members 9 = some paRelT}
    {h10 : E.members 10 = some accPFamT} :
    (accPIntroViewT E h9 h10).AllFieldsSafe := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr (List.mem_singleton.mpr rfl)
  | ⟨1, _⟩ => exact Or.inl (fun _ => rfl)

theorem accPBefore : CtorBeforeRecursors accPFamEnvT paIntroT := by
  refine ⟨10, rfl, ?_⟩
  intro rr rm hm hc
  by_cases h10 : rr = 10
  · subst h10
    rw [show accPFamEnvT.members 10 = some accPFamT from rfl] at hm
    cases hm
    exact absurd hc (by decide)
  · rw [members_extendEnv_ne _ _ _ h10] at hm
    by_cases h9 : rr = 9
    · subst h9
      rw [show paRelEnvT.members 9 = some paRelT from rfl] at hm
      cases hm
      exact absurd hc (by decide)
    · rw [members_extendEnv_ne _ _ _ h9] at hm
      exact Option.noConfusion hm

theorem accPContig : CtorContiguous accPFamEnvT 11 paIntroT := by
  refine ⟨10, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd (And.intro hl hr) (by omega)
  · intro c ⟨cm, hm, hc, _⟩
    by_cases h10 : c = 10
    · subst h10
      rw [show accPFamEnvT.members 10 = some accPFamT from rfl] at hm
      cases hm
      exact absurd hc (by decide)
    · rw [members_extendEnv_ne _ _ _ h10] at hm
      by_cases h9 : c = 9
      · subst h9
        rw [show paRelEnvT.members 9 = some paRelT from rfl] at hm
        cases hm
        exact absurd hc (by decide)
      · rw [members_extendEnv_ne _ _ _ h9] at hm
        exact Option.noConfusion hm

theorem accPIntroFieldsFam : CtorFieldsPermitted (accPIntroViewT accPFamEnvT rfl rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 24, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.recursive 2, 24, [.bvar 1], rfl⟩

theorem accPIntroFieldsSup : CtorFieldsPermitted (accPIntroViewT accPSupEnvT rfl rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 24, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.recursive 2, 24, [.bvar 1], rfl⟩

/-! ## §3 admission -/

def accPFamAdmitted : IndGroupAdmitted paRelEnvT 10 accPFamT :=
  .family rfl (accPFamViewT accPFamEnvT rfl) rfl rfl (Or.inl (fun _ => rfl))

def accPIntroAdmitted : IndGroupAdmitted accPFamEnvT 11 paIntroT :=
  .constructor (accPFamViewT accPFamEnvT rfl) (accPIntroViewT accPFamEnvT rfl rfl) rfl
    accPBefore accPContig accPIntroUniv accPIntroFieldsFam

/-- the recursor admission: AnySort by `singletonProp` — a Prop family with ONE constructor
    whose fields are all safe. The large-eliminating Prop recursor of the Acc class. -/
def accPGroupAdm : RecursorEliminationAdmitted accPSupEnvT 12 paRecT where
  family := accPFamViewT accPSupEnvT rfl
  constructors := [paIntroT]
  constructorViews
    | ⟨0, _⟩ => accPIntroViewT accPSupEnvT rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [paMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp (fun _ => rfl) rfl
    (fun i => match i with | ⟨0, _⟩ => accPIntroSafe)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem accPCensus : CtorCensus accPSupEnvT 10 12 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hm, hc, hfam⟩
    by_cases h11 : c = 11
    · subst h11
      rw [show accPSupEnvT.members 11 = some paIntroT from rfl] at hm
      cases hm
      exact ⟨by omega, by omega⟩
    · rw [members_extendEnv_ne _ _ _ h11] at hm
      by_cases h10 : c = 10
      · subst h10
        rw [show accPFamEnvT.members 10 = some accPFamT from rfl] at hm
        cases hm
        exact absurd hc (by decide)
      · rw [members_extendEnv_ne _ _ _ h10] at hm
        by_cases h9 : c = 9
        · subst h9
          rw [show paRelEnvT.members 9 = some paRelT from rfl] at hm
          cases hm
          exact absurd hc (by decide)
        · rw [members_extendEnv_ne _ _ _ h9] at hm
          exact Option.noConfusion hm
  · intro ⟨hl, hr⟩
    have hc : c = 11 := by omega
    subst hc
    exact ⟨paIntroT, rfl, rfl, rfl⟩

theorem accPMinor_derived :
    derivedMinor accPGroupAdm ⟨0, by decide⟩ 24 [.nonrecursive, .recursive 2] =
      some paMinorTy := rfl

theorem accPMinorMatch : MinorPremisesMatch accPGroupAdm := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.nonrecursive, .recursive 2], 24, rfl, rfl⟩

theorem accPSchema_derived :
    iotaSchemaAt accPGroupAdm ⟨0, by decide⟩ 24 [.nonrecursive, .recursive 2] =
      some paSchema := rfl

theorem accPEquation_shape :
    equationDoms accPGroupAdm ⟨0, by decide⟩ =
        some [paMotTy, paMinorTy, .sort .zero, .sort .zero, paFieldDom] ∧
      iotaEquationType accPGroupAdm ⟨0, by decide⟩ = paEqTy := ⟨rfl, rfl⟩

/-- the ι schema `minor x g (λ y h, rec M minor y (g y h)) : M x (intro x g)` in the untyped
    judgment at `accPEnvT` — the same derivation as `paIotaTy`, at the Prop family. -/
def accPIotaTy : HasTy accPEnvT 1 paIotaCtx paSchema paEqTy := by
  have hMn : HasTy accPEnvT 1 paIotaCtx (.bvar 3) (lift 0 4 paMinorTy) :=
    HasTy.bvar _ 3 _ rfl
  have hX : HasTy accPEnvT 1 paIotaCtx (.bvar 1) (.sort .zero) :=
    HasTy.bvar _ 1 _ rfl
  have hG : HasTy accPEnvT 1 paIotaCtx (.bvar 0) (lift 0 1 paFieldDom) :=
    HasTy.bvar _ 0 _ rfl
  have hY0 : HasTy accPEnvT 1 (.assumption (.sort .zero) :: paIotaCtx)
      (.bvar 0) (.sort .zero) := HasTy.bvar _ 0 _ rfl
  have hX1 : HasTy accPEnvT 1 (.assumption (.sort .zero) :: paIotaCtx)
      (.bvar 2) (.sort .zero) := HasTy.bvar _ 2 _ rfl
  have hRyx : HasTy accPEnvT 1 (.assumption (.sort .zero) :: paIotaCtx)
      paRyxX (.sort .zero) :=
    HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _ (paRelConstTy rfl) hY0) hX1
  have hRec : HasTy accPEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx)
      (.const 12 [.param 0]) (instantiateLevels [.param 0] paRecT.mtype) :=
    paRecHead rfl
  have hM'' : HasTy accPEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 6) (lift 0 7 paMotTy) :=
    HasTy.bvar _ 6 _ rfl
  have hMn'' : HasTy accPEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 5) (lift 0 6 paMinorTy) :=
    HasTy.bvar _ 5 _ rfl
  have hY'' : HasTy accPEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 1) (.sort .zero) :=
    HasTy.bvar _ 1 _ rfl
  have hG'' : HasTy accPEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 2) (lift 0 3 paFieldDom) :=
    HasTy.bvar _ 2 _ rfl
  have hH'' : HasTy accPEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 0) (lift 0 1 paRyxX) :=
    HasTy.bvar _ 0 _ rfl
  exact HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ hMn hX) hG)
    (HasTy.lam _ (.sort .zero) (.succ .zero) _ _ (HasTy.sort _ .zero)
      (HasTy.lam _ paRyxX .zero _ _ hRyx
        (HasTy.app _ _ _ _ _
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _
              (HasTy.app _ _ _ _ _ hRec hM'')
              hMn'')
            hY'')
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _ hG'' hY'')
            hH''))))

def accPIotaLegacy : IotaEquationTyped accPGroupAdm ⟨0, by decide⟩ 24
    [.nonrecursive, .recursive 2] := by
  unfold IotaEquationTyped
  rw [accPEquation_shape.1, accPSchema_derived]
  exact accPIotaTy

def accPIotaClause : IotaDescriptorClause accPSupEnvT accPGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive, .recursive 2]
  fuelAt := fun _ => 24
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => accPIotaLegacy

def accPRecAdmitted : IndGroupAdmitted accPSupEnvT 12 paRecT :=
  .recursor accPGroupAdm rfl accPCensus
    (fun i => match i with | ⟨0, _⟩ => accPIntroUniv)
    (fun i => match i with | ⟨0, _⟩ => accPIntroFieldsSup)
    accPMinorMatch accPIotaClause

/-! ## §4 typed content and `EnvWfT` -/

def accPFamTyT : HasTyT paRelEnvT 0 [] (.pi (.sort .zero) (.sort .zero))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] _ _ _ _ (HasTyT.sort _ .zero) (HasTyT.sort _ .zero)

/-- `intro`'s stored type's sort: `x` at `1`, the field domain at `imax 1 (imax 0 0)`, the
    family target at `0`. -/
def accPIntroSortU : Level :=
  .imax (.succ .zero) (.imax (.imax (.succ .zero) (.imax .zero .zero)) .zero)

def accPIntroTyT : HasTyT accPFamEnvT 0 []
    (.pi (.sort .zero) (.pi paFieldDom (.app (.const 10 []) (.bvar 1))))
    (.sort accPIntroSortU) :=
  .pi [] _ _ _ _ (HasTyT.sort _ .zero)
    (.pi _ _ _ _ _ (accPFieldDomTyT rfl rfl)
      (HasTyT.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTyT.const _ 10 [] accPFamT rfl rfl rfl) (HasTyT.bvar _ 1 _ rfl)))

/-- the recursor's stored type's sort (the `inferT` answer, checked). -/
def accPRecSortU : Level :=
  .imax (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))
    (.imax
      (.imax (.succ .zero)
        (.imax (.imax (.succ .zero) (.imax .zero .zero))
          (.imax (.imax (.succ .zero) (.imax .zero (.param 0))) (.param 0))))
      (.imax (.succ .zero) (.imax .zero (.param 0))))

theorem accPRecTy_direct :
    inferT accPSupEnvT 1 [] paRecT.mtype = some (.sort accPRecSortU) := rfl


def accPRecTyT : HasTyT accPSupEnvT 1 [] paRecT.mtype (.sort accPRecSortU) :=
  (tyAtC accPSupEnvT 1 32 [] paRecT.mtype (.sort accPRecSortU)).get (by
    have h : (tyAtC accPSupEnvT 1 32 [] paRecT.mtype (.sort accPRecSortU)).isSome = true := rfl
    exact h)

theorem accPFamTypedT : IndGroupTypedT accPFamAdmitted := fun i =>
  match i with | ⟨0, _⟩ => ⟨HasTyT.sort _ .zero⟩

theorem accPIntroTypedE {E : ResolvedEnv} (h9 : E.members 9 = some paRelT)
    (h10 : E.members 10 = some accPFamT) :
    CtorTypedT (accPIntroViewT E h9 h10) :=
  ⟨fun j => by
      match j with
      | ⟨0, _⟩ => exact ⟨HasTyT.sort _ .zero⟩
      | ⟨1, _⟩ => exact ⟨accPFieldDomTyT h9 h10⟩,
    fun i => i.elim0⟩

theorem accPIntroTyped : IndGroupTypedT accPIntroAdmitted :=
  ⟨accPFamTypedT, accPIntroTypedE rfl rfl⟩

theorem accPRecTyped : IndGroupTypedT accPRecAdmitted :=
  ⟨(fun i => match i with | ⟨0, _⟩ => ⟨HasTyT.sort _ .zero⟩),
   fun i => match i with | ⟨0, _⟩ => accPIntroTypedE rfl rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 32 Γ e T) rfl⟩

def accPMembersT :
    GroupMembersT accPFamEnvT paRelEnvT [(10, accPFamT), (11, paIntroT), (12, paRecT)]
      accPEnvT :=
  .cons _ 10 accPFamT _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    accPFamAdmitted PUnit.unit _ accPFamTyT (fun h => absurd h (by decide))
    accPFamTypedT
    (.cons _ 11 paIntroT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide))
      rfl rfl rfl
      accPIntroAdmitted PUnit.unit _ accPIntroTyT (fun _ => ⟨accPIntroTyT⟩) accPIntroTyped
      (.cons _ 12 paRecT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide))
        rfl rfl rfl
        accPRecAdmitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ accPRecTyT
        (fun h => absurd h (by decide)) accPRecTyped (.nil _)))

/-- **the Prop-valued Acc environment is admitted**: the axiom `R`, then `AccP`, `intro`,
    the large-eliminating recursor, as one group step. -/
def accPEnvWfT : EnvWfT accPEnvT :=
  .group paRelEnvT 10 accPFamT [(11, paIntroT)] 12 paRecT accPEnvT paRelWfT
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl accPMembersT

/-- PIN: the family really is a Prop family (`Sort 0` result), and the recursor really is
    large-eliminating (arity `1`: the motive universe `param 0` is free). -/
theorem accPEnv_shape :
    accPEnvT.members 10 = some ⟨.inductiveM, 0, .pi (.sort .zero) (.sort .zero), none⟩ ∧
      accPEnvT.members 12 = some paRecT ∧ paRecT.arity = 1 ∧
      accPGroupAdm.policy = .anySort := ⟨rfl, rfl, rfl, rfl⟩

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.accPFamT
#print axioms Rcic.Declarative.Ann.accPFieldDomTy
#print axioms Rcic.Declarative.Ann.accPFieldDomTyT
#print axioms Rcic.Declarative.Ann.accPFamViewT
#print axioms Rcic.Declarative.Ann.accPIntroViewT
#print axioms Rcic.Declarative.Ann.accPIntroUniv
#print axioms Rcic.Declarative.Ann.accPIntroSafe
#print axioms Rcic.Declarative.Ann.accPBefore
#print axioms Rcic.Declarative.Ann.accPContig
#print axioms Rcic.Declarative.Ann.accPIntroFieldsFam
#print axioms Rcic.Declarative.Ann.accPIntroFieldsSup
#print axioms Rcic.Declarative.Ann.accPFamAdmitted
#print axioms Rcic.Declarative.Ann.accPIntroAdmitted
#print axioms Rcic.Declarative.Ann.accPGroupAdm
#print axioms Rcic.Declarative.Ann.accPCensus
#print axioms Rcic.Declarative.Ann.accPMinor_derived
#print axioms Rcic.Declarative.Ann.accPMinorMatch
#print axioms Rcic.Declarative.Ann.accPSchema_derived
#print axioms Rcic.Declarative.Ann.accPEquation_shape
#print axioms Rcic.Declarative.Ann.accPIotaTy
#print axioms Rcic.Declarative.Ann.accPIotaLegacy
#print axioms Rcic.Declarative.Ann.accPIotaClause
#print axioms Rcic.Declarative.Ann.accPRecAdmitted
#print axioms Rcic.Declarative.Ann.accPFamTyT
#print axioms Rcic.Declarative.Ann.accPIntroSortU
#print axioms Rcic.Declarative.Ann.accPIntroTyT
#print axioms Rcic.Declarative.Ann.accPRecSortU
#print axioms Rcic.Declarative.Ann.accPRecTy_direct
#print axioms Rcic.Declarative.Ann.accPRecTyT
#print axioms Rcic.Declarative.Ann.accPFamTypedT
#print axioms Rcic.Declarative.Ann.accPIntroTypedE
#print axioms Rcic.Declarative.Ann.accPIntroTyped
#print axioms Rcic.Declarative.Ann.accPRecTyped
#print axioms Rcic.Declarative.Ann.accPMembersT
#print axioms Rcic.Declarative.Ann.accPEnvWfT
#print axioms Rcic.Declarative.Ann.accPEnv_shape
