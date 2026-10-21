import rcic.RcicNativeTypedModelCovUCycle
import rcic.RcicTypedFunRecPins

/-!
# An admitted higher-order recursive proposition singleton

`W : Prop`, `sup : (Prop → W) → W`, and its large eliminator are
added over the admitted Loop group. A closed object-language axiom
`t : Loop` supplies the actual native cyclic-type parameter.
All declarations are new. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovTAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelKAudit TypedModelKFragmentAudit
open ReadbackCKAudit ReadbackCK2Audit FamModelLRSAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covUHoFam : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def covUHoField : Expr Nat := .pi (.sort .zero) (.const 63 [])
def covUHoCtor : CheckedMember :=
  ⟨.constructorM, 0, .pi covUHoField (.const 63 []), none⟩
def covUHoMotTy : Expr Nat := .pi (.const 63 []) (.sort (.param 0))
def covUHoMinTy : Expr Nat :=
  .pi covUHoField
    (.pi (.pi (.sort .zero) (.app (.bvar 2) (.app (.bvar 1) (.bvar 0))))
      (.app (.bvar 2) (.app (.const 64 []) (.bvar 1))))
def covUHoRecTy : Expr Nat :=
  .pi covUHoMotTy (.pi covUHoMinTy (.pi (.const 63 []) (.app (.bvar 2) (.bvar 0))))
def covUHoRec : CheckedMember := ⟨.recursorM, 1, covUHoRecTy, none⟩
def covUHoFamEnv : ResolvedEnv := extendEnv pinLoopEnvT 63 covUHoFam
def covUHoCtorEnv : ResolvedEnv := extendEnv covUHoFamEnv 64 covUHoCtor
def covUHoGroupEnv : ResolvedEnv := extendEnv covUHoCtorEnv 65 covUHoRec
def covUHoParameter : CheckedMember := ⟨.axiomM, 0, .const 60 [], none⟩
def covUHoEnv : ResolvedEnv := extendEnv covUHoGroupEnv 66 covUHoParameter

private theorem covUHoFamEnv_members (r : Nat) :
    covUHoFamEnv.members r =
      if r = 63 then some covUHoFam else if r = 62 then some pinLoopRecT
      else if r = 61 then some pinLoopMkT else if r = 60 then some pinLoopFamT
      else none := rfl

private theorem covUHoCtorEnv_members (r : Nat) :
    covUHoCtorEnv.members r =
      if r = 64 then some covUHoCtor else if r = 63 then some covUHoFam
      else if r = 62 then some pinLoopRecT else if r = 61 then some pinLoopMkT
      else if r = 60 then some pinLoopFamT else none := rfl

theorem covUHoEnv_members (r : Nat) :
    covUHoEnv.members r =
      if r = 66 then some covUHoParameter else if r = 65 then some covUHoRec
      else if r = 64 then some covUHoCtor else if r = 63 then some covUHoFam
      else if r = 62 then some pinLoopRecT else if r = 61 then some pinLoopMkT
      else if r = 60 then some pinLoopFamT else none := rfl

private def covUHoFamView (E : ResolvedEnv) (h : E.members 63 = some covUHoFam) :
    PolicyFamilyView E where
  ref := 63
  member := covUHoFam
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

private def covUHoFieldTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h : E.members 63 = some covUHoFam) :
    HasTy E n Γ covUHoField (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ _ _ _ _ (.sort _ _)
    (.const _ _ _ covUHoFam h rfl (fun _ hx => nomatch hx))

private def covUHoCtorView (E : ResolvedEnv) (h : E.members 63 = some covUHoFam) :
    PolicyConstructorView E (covUHoFamView E h) covUHoCtor where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [covUHoField]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .imax (.succ .zero) .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hj : j = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
      subst j
      exact covUHoFieldTy h }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

private theorem covUHoCtor_universe (E : ResolvedEnv)
    (h : E.members 63 = some covUHoFam) :
    FieldUniverseAdmitted (covUHoCtorView E h) := fun _ => .inl (fun _ => rfl)

private theorem covUHoCtor_safe (E : ResolvedEnv)
    (h : E.members 63 = some covUHoFam) :
    (covUHoCtorView E h).AllFieldsSafe := fun _ => .inl (fun _ => rfl)

private theorem covUHoCtor_fields (E : ResolvedEnv)
    (h : E.members 63 = some covUHoFam)
    (ha : fieldAnalyze E 8 63 0 0 0 0 covUHoField = .permitted (.recursive 1) []) :
    CtorFieldsPermitted (covUHoCtorView E h) := by
  intro j
  have hj : j = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  exact ⟨.recursive 1, 8, [], ha⟩

private theorem covUHo_before : CtorBeforeRecursors covUHoFamEnv covUHoCtor := by
  refine ⟨63, rfl, ?_⟩
  intro rr rm hm hk hn
  rw [covUHoFamEnv_members] at hm
  split at hm
  · cases hm; cases hk
  · split at hm
    · cases hm; cases hn
    · split at hm
      · cases hm; cases hk
      · split at hm
        · cases hm; cases hk
        · cases hm

private theorem covUHo_contiguous : CtorContiguous covUHoFamEnv 64 covUHoCtor := by
  refine ⟨63, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hf : False := by omega
    exact hf.elim
  · rintro c ⟨cm, hm, hk, hf⟩
    rw [covUHoFamEnv_members] at hm
    split at hm
    · cases hm; cases hk
    · split at hm
      · cases hm; cases hk
      · split at hm
        · cases hm; cases hf
        · split at hm
          · cases hm; cases hk
          · cases hm

private theorem covUHo_census : CtorCensus covUHoCtorEnv 63 65 := by
  refine ⟨by decide, ?_⟩
  intro c
  constructor
  · rintro ⟨cm, hm, hk, hf⟩
    rw [covUHoCtorEnv_members] at hm
    split at hm
    · rename_i hc
      exact ⟨by omega, by omega⟩
    · split at hm
      · cases hm; cases hk
      · split at hm
        · cases hm; cases hk
        · split at hm
          · cases hm; cases hf
          · split at hm
            · cases hm; cases hk
            · cases hm
  · intro hc
    have he : c = 64 := by omega
    subst c
    exact ⟨covUHoCtor, rfl, rfl, rfl⟩

private def covUHoFam_admitted : IndGroupAdmitted pinLoopEnvT 63 covUHoFam :=
  .family rfl (covUHoFamView covUHoFamEnv rfl) rfl rfl (.inl (fun _ => rfl))
private def covUHoCtor_admitted : IndGroupAdmitted covUHoFamEnv 64 covUHoCtor :=
  .constructor (covUHoFamView covUHoFamEnv rfl) (covUHoCtorView covUHoFamEnv rfl)
    rfl covUHo_before covUHo_contiguous (covUHoCtor_universe _ rfl)
    (covUHoCtor_fields _ rfl rfl)

private def covUHoPolicy : RecursorEliminationAdmitted covUHoCtorEnv 65 covUHoRec where
  family := covUHoFamView covUHoCtorEnv rfl
  constructors := [covUHoCtor]
  constructorViews | ⟨0, _⟩ => covUHoCtorView covUHoCtorEnv rfl
  constructorsPresent | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [covUHoMinTy]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp (fun _ => rfl) rfl
    (fun i => by have hi : i = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
                 subst i
                 exact covUHoCtor_safe _ rfl)
  recursorArity := rfl
  recursorType := rfl

private def covUHoSchema : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0))
    (.lam (.sort .zero)
      (.app (.app (.app (.const 65 [.param 0]) (.bvar 3)) (.bvar 2))
        (.app (.bvar 1) (.bvar 0))))
private def covUHoEquationTy : Expr Nat :=
  .app (.bvar 2) (.app (.const 64 []) (.bvar 0))
private def covUHoEquationCtx : LCtx :=
  [.assumption covUHoField, .assumption covUHoMinTy, .assumption covUHoMotTy]

private def covUHoEquationLegacy :
    HasTy covUHoGroupEnv 1 covUHoEquationCtx covUHoSchema covUHoEquationTy := by
  have hm : HasTy covUHoGroupEnv 1 covUHoEquationCtx (.bvar 1)
      (lift 0 2 covUHoMinTy) := .bvar _ 1 _ rfl
  have hf : HasTy covUHoGroupEnv 1 covUHoEquationCtx (.bvar 0) covUHoField :=
    .bvar _ 0 _ rfl
  have hrec : HasTy covUHoGroupEnv 1
      (.assumption (.sort .zero) :: covUHoEquationCtx)
      (.const 65 [.param 0]) covUHoRecTy :=
    .const _ _ _ covUHoRec rfl rfl (by
      intro l hl
      have he : l = .param 0 := by simpa using hl
      subst l
      exact ⟨0, .inl rfl⟩)
  have hmot : HasTy covUHoGroupEnv 1
      (.assumption (.sort .zero) :: covUHoEquationCtx) (.bvar 3) covUHoMotTy :=
    .bvar _ 3 _ rfl
  have hmin : HasTy covUHoGroupEnv 1
      (.assumption (.sort .zero) :: covUHoEquationCtx) (.bvar 2)
      (lift 0 3 covUHoMinTy) := .bvar _ 2 _ rfl
  have hfun : HasTy covUHoGroupEnv 1
      (.assumption (.sort .zero) :: covUHoEquationCtx) (.bvar 1) covUHoField :=
    .bvar _ 1 _ rfl
  have harg : HasTy covUHoGroupEnv 1
      (.assumption (.sort .zero) :: covUHoEquationCtx) (.bvar 0) (.sort .zero) :=
    .bvar _ 0 _ rfl
  exact .app _ _ _ _ _ (.app _ _ _ _ _ hm hf)
    (.lam _ _ _ _ _ (.sort _ _)
      (.app _ _ _ _ _
        (.app _ _ _ _ _ (.app _ _ _ _ _ hrec hmot) hmin)
        (.app _ _ _ _ _ hfun harg)))

private def covUHoDescriptor : IotaDescriptorClause covUHoCtorEnv covUHoPolicy where
  signatureOnly := rfl
  shapesAt := fun _ => [.recursive 1]
  fuelAt := fun _ => 8
  analyzed | ⟨0, _⟩ => rfl
  typed | ⟨0, _⟩ => covUHoEquationLegacy

private theorem covUHo_minor_match : MinorPremisesMatch covUHoPolicy := by
  intro i
  have hi : i = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
  subst i
  exact ⟨[.recursive 1], 8, rfl, rfl⟩

private def covUHoRec_admitted : IndGroupAdmitted covUHoCtorEnv 65 covUHoRec :=
  .recursor covUHoPolicy rfl covUHo_census
    (fun i => by have hi : i = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
                 subst i
                 exact covUHoCtor_universe _ rfl)
    (fun i => by have hi : i = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
                 subst i
                 exact covUHoCtor_fields _ rfl rfl)
    covUHo_minor_match covUHoDescriptor

private def covUHoCtorTyT : HasTyT covUHoFamEnv 0 [] covUHoCtor.mtype
    (.sort (.imax (.imax (.succ .zero) .zero) .zero)) :=
  .pi _ _ _ _ _
    (.pi _ _ _ _ _ (.sort _ _) (.const _ _ _ covUHoFam rfl rfl rfl))
    (.const _ _ _ covUHoFam rfl rfl rfl)

private def covUHoRecSort : Level :=
  .imax (.imax .zero (.succ (.param 0)))
    (.imax (.imax (.imax (.succ .zero) .zero)
      (.imax (.imax (.succ .zero) (.param 0)) (.param 0))) (.imax .zero (.param 0)))

private def covUHoRecTyT : HasTyT covUHoCtorEnv 1 [] covUHoRecTy (.sort covUHoRecSort) :=
  (tyAtC covUHoCtorEnv 1 12 [] covUHoRecTy (.sort covUHoRecSort)).get (by rfl)

private theorem covUHoCtorTyped (E : ResolvedEnv) (h : E.members 63 = some covUHoFam) :
    CtorTypedT (covUHoCtorView E h) := by
  constructor
  · intro j
    have hj : j = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
    subst j
    exact ⟨.pi _ _ _ _ _ (.sort _ _) (.const _ _ _ covUHoFam h rfl rfl)⟩
  · intro i
    exact i.elim0

private theorem covUHoFamTyped : IndGroupTypedT covUHoFam_admitted := fun i => i.elim0
private theorem covUHoCtorGroupTyped : IndGroupTypedT covUHoCtor_admitted :=
  ⟨fun i => i.elim0, covUHoCtorTyped _ rfl⟩
private theorem covUHoRecTyped : IndGroupTypedT covUHoRec_admitted :=
  ⟨fun i => i.elim0,
    (fun i => by have hi : i = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
                 subst i
                 exact covUHoCtorTyped _ rfl),
    (fun i => by have hi : i = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
                 subst i
                 exact iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 12 Γ e T) rfl)⟩

private def covUHoMembers :
    GroupMembersT covUHoFamEnv pinLoopEnvT
      [(63, covUHoFam), (64, covUHoCtor), (65, covUHoRec)] covUHoGroupEnv :=
  .cons _ 63 covUHoFam _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    covUHoFam_admitted PUnit.unit _ (.sort [] .zero) (fun h => nomatch h)
    covUHoFamTyped
    (.cons _ 64 covUHoCtor _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
      covUHoCtor_admitted PUnit.unit _ covUHoCtorTyT (fun _ => ⟨covUHoCtorTyT⟩)
      covUHoCtorGroupTyped
      (.cons _ 65 covUHoRec _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
        covUHoRec_admitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ covUHoRecTyT
        (fun h => nomatch h) covUHoRecTyped (.nil _)))

def covUHoGroup_wf : EnvWfT covUHoGroupEnv :=
  .group pinLoopEnvT 63 covUHoFam [(64, covUHoCtor)] 65 covUHoRec covUHoGroupEnv
    pinLoopGroupRecWfT rfl (fun c hc => by simp at hc; subst c; rfl) rfl covUHoMembers

def covUHoEnv_wf : EnvWfT covUHoEnv :=
  .axiom covUHoGroupEnv 66 (.const 60 []) .zero covUHoGroup_wf rfl
    (.const [] 60 [] pinLoopFamT rfl rfl rfl) (fun _ => rfl) rfl

end Rcic.Declarative.NativeValleys.TypedModelCovTAudit

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_U_SOUNDNESS_ENV_ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoFam
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoField
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoCtor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMotTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoMinTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoRecTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoRec
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoFamEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoCtorEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoGroupEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoParameter
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoEnv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoEnv_members
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoGroup_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovTAudit.covUHoEnv_wf
-- END RCIC_NATIVE_TYPED_MODEL_COV_U_SOUNDNESS_ENV_ROOTS
