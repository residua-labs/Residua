import rcic.RcicNativeTypedModelCovVProjection
import rcic.RcicNativeTypedModelCovVHeadActions
import rcic.RcicNativeTypedModelCovWRealized
import rcic.RcicTypedFunRecPins

/-!
# The revealed-index observation boundary

The canonical field of a revealed constructor argument is the corresponding
index expression.  A native typing derivation relates this index to the
actual field by conversion.  The direct proof-identity application below
shows why that conversion does not transport a nonbottom observation to the
actual field, even when every native premise is inhabited.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKAudit TypedModelKFragmentAudit TypedModelKGuardAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovUAudit TypedModelCovVAudit
open TypedModelAudit.TypingFin

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Revealed entries really are selected index arguments. -/
theorem covW_revealed_projField {E : ResolvedEnv} (w : IotaWitness E)
    {i j : Nat} (hi : i < w.fields.length)
    (hr : revealedPos? w i = some j) (x : Expr Nat) :
    (projFields w x).getD i (.sort .zero) =
      (redexIdx w).getD j (.sort .zero) := by
  have hlen : w.fields.length = fieldCount w := by
    have hp := w.hnpar
    show w.fields.length = piCount w.ctorMember.mtype - w.nparams
    omega
  unfold projFields
  rw [List.getD_eq_getElem?_getD,
    projAll_getElem? (fieldCount w) i (hlen ▸ hi)]
  change canonField w i _ _ _ x = _
  unfold canonField
  rw [hr]
  rfl

/-- The new singleton is indexed by the existing proposition `P`. -/
def covWRevFam : CheckedMember :=
  ⟨.inductiveM, 0, .pi covUProjP (.sort .zero), none⟩
def covWRevCtor : CheckedMember :=
  ⟨.constructorM, 0, .pi covUProjP (.app (.const 5 []) (.bvar 0)), none⟩
def covWRevMotTy : Expr Nat :=
  .pi covUProjP (.pi (.app (.const 5 []) (.bvar 0)) (.sort (.param 0)))
def covWRevMinTy : Expr Nat :=
  .pi covUProjP
    (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 6 []) (.bvar 0)))
def covWRevRecTy : Expr Nat :=
  .pi covWRevMotTy (.pi covWRevMinTy
    (.pi covUProjP (.pi (.app (.const 5 []) (.bvar 0))
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))
def covWRevRec : CheckedMember := ⟨.recursorM, 1, covWRevRecTy, none⟩
def covWRevFamEnv : ResolvedEnv := extendEnv covUProjEnv 5 covWRevFam
def covWRevCtorEnv : ResolvedEnv := extendEnv covWRevFamEnv 6 covWRevCtor
def covWRevEnv : ResolvedEnv := extendEnv covWRevCtorEnv 7 covWRevRec

/-- The actual field is a typed beta expansion of the selected index. -/
def covWRevField : Expr Nat := .app (.lam covUProjP (.bvar 0)) covUProjProof
def covWRevMajor : Expr Nat := .app (.const 6 []) covWRevField
def covWRevFamily (q : Expr Nat) : Expr Nat := .app (.const 5 []) q
def covWRevMotive : Expr Nat :=
  .lam covUProjP (.lam (covWRevFamily (.bvar 0)) covUProjP)
def covWRevMinor : Expr Nat := .lam covUProjP covUProjProof

private theorem covWRevFamEnv_members (r : Nat) :
    covWRevFamEnv.members r =
      if r = 5 then some covWRevFam else if r = 4 then some covUProjProofMember
      else if r = 3 then some covUProjPMember else if r = 2 then some andRecMemberU
      else if r = 1 then some andIntroMember else if r = 0 then some andFamMember
      else none := rfl

private theorem covWRevCtorEnv_members (r : Nat) :
    covWRevCtorEnv.members r =
      if r = 6 then some covWRevCtor else if r = 5 then some covWRevFam
      else if r = 4 then some covUProjProofMember else if r = 3 then some covUProjPMember
      else if r = 2 then some andRecMemberU else if r = 1 then some andIntroMember
      else if r = 0 then some andFamMember else none := rfl

private def covWRevFamView (E : ResolvedEnv)
    (hP : E.members 3 = some covUProjPMember)
    (h : E.members 5 = some covWRevFam) : PolicyFamilyView E where
  ref := 5
  member := covWRevFam
  present := h
  hasClass := rfl
  parameters := []
  indices := [covUProjP]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hj : j = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
      subst j
      exact .const _ _ _ covUProjPMember hP rfl (fun _ hx => nomatch hx) }

private def covWRevCtorView (E : ResolvedEnv)
    (hP : E.members 3 = some covUProjPMember)
    (h : E.members 5 = some covWRevFam) :
    PolicyConstructorView E (covWRevFamView E hP h) covWRevCtor where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [covUProjP]
  resultIndices := [.bvar 0]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hj : j = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
      subst j
      exact .const _ _ _ covUProjPMember hP rfl (fun _ hx => nomatch hx) }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := by
    intro e he
    have heq : e = .bvar 0 := by simpa using he
    subst e
    rfl

private theorem covWRevCtor_universe (E : ResolvedEnv)
    (hP : E.members 3 = some covUProjPMember)
    (h : E.members 5 = some covWRevFam) :
    FieldUniverseAdmitted (covWRevCtorView E hP h) := fun _ => .inl (fun _ => rfl)

private theorem covWRevCtor_safe (E : ResolvedEnv)
    (hP : E.members 3 = some covUProjPMember)
    (h : E.members 5 = some covWRevFam) :
    (covWRevCtorView E hP h).AllFieldsSafe := fun _ => .inl (fun _ => rfl)

private theorem covWRevCtor_fields (E : ResolvedEnv)
    (hP : E.members 3 = some covUProjPMember)
    (h : E.members 5 = some covWRevFam)
    (ha : fieldAnalyze E 8 5 0 0 1 0 covUProjP = .permitted .nonrecursive []) :
    CtorFieldsPermitted (covWRevCtorView E hP h) := by
  intro j
  have hj : j = ⟨0, by change 0 < 1; decide⟩ :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  exact ⟨.nonrecursive, 8, [], ha⟩

private theorem covWRev_before : CtorBeforeRecursors covWRevFamEnv covWRevCtor := by
  refine ⟨5, rfl, ?_⟩
  intro rr rm hm hk hn
  rw [covWRevFamEnv_members] at hm
  split at hm
  · cases hm; cases hk
  · split at hm
    · cases hm; cases hk
    · split at hm
      · cases hm; cases hk
      · split at hm
        · cases hm; cases hn
        · split at hm
          · cases hm; cases hk
          · split at hm
            · cases hm; cases hk
            · cases hm

private theorem covWRev_contiguous : CtorContiguous covWRevFamEnv 6 covWRevCtor := by
  refine ⟨5, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hf : False := by omega
    exact hf.elim
  · rintro c ⟨cm, hm, hk, hf⟩
    rw [covWRevFamEnv_members] at hm
    split at hm
    · cases hm; cases hk
    · split at hm
      · cases hm; cases hk
      · split at hm
        · cases hm; cases hk
        · split at hm
          · cases hm; cases hk
          · split at hm
            · cases hm; cases hf
            · split at hm
              · cases hm; cases hk
              · cases hm

private theorem covWRev_census : CtorCensus covWRevCtorEnv 5 7 := by
  refine ⟨by decide, ?_⟩
  intro c
  constructor
  · rintro ⟨cm, hm, hk, hf⟩
    rw [covWRevCtorEnv_members] at hm
    split at hm
    · rename_i hc
      exact ⟨by omega, by omega⟩
    · split at hm
      · cases hm; cases hk
      · split at hm
        · cases hm; cases hk
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
    have he : c = 6 := by omega
    subst c
    exact ⟨covWRevCtor, rfl, rfl, rfl⟩

private def covWRevFam_admitted : IndGroupAdmitted covUProjEnv 5 covWRevFam :=
  .family rfl (covWRevFamView covWRevFamEnv rfl rfl) rfl rfl (.inl (fun _ => rfl))
private def covWRevCtor_admitted : IndGroupAdmitted covWRevFamEnv 6 covWRevCtor :=
  .constructor (covWRevFamView covWRevFamEnv rfl rfl)
    (covWRevCtorView covWRevFamEnv rfl rfl)
    rfl covWRev_before covWRev_contiguous (covWRevCtor_universe _ rfl rfl)
    (covWRevCtor_fields _ rfl rfl rfl)

private def covWRevPolicy : RecursorEliminationAdmitted covWRevCtorEnv 7 covWRevRec where
  family := covWRevFamView covWRevCtorEnv rfl rfl
  constructors := [covWRevCtor]
  constructorViews | ⟨0, _⟩ => covWRevCtorView covWRevCtorEnv rfl rfl
  constructorsPresent | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [covWRevMinTy]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp (fun _ => rfl) rfl
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact covWRevCtor_safe _ rfl rfl)
  recursorArity := rfl
  recursorType := rfl

private def covWRevDescriptor : IotaDescriptorClause covWRevCtorEnv covWRevPolicy where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive]
  fuelAt := fun _ => 8
  analyzed | ⟨0, _⟩ => rfl
  typed := fun i => by
    have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
      Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
    subst i
    let Γ : LCtx := [.assumption covUProjP, .assumption covUProjP,
      .assumption covWRevMinTy, .assumption covWRevMotTy]
    have hm : HasTy covWRevEnv 1 Γ (.bvar 2) (lift 0 3 covWRevMinTy) :=
      .bvar Γ 2 _ rfl
    have hq : HasTy covWRevEnv 1 Γ (.bvar 0) covUProjP := .bvar Γ 0 _ rfl
    exact .app _ _ _ _ _ hm hq

private theorem covWRev_minor_match : MinorPremisesMatch covWRevPolicy := by
  intro i
  have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
  subst i
  exact ⟨[.nonrecursive], 8, rfl, rfl⟩

private def covWRevRec_admitted : IndGroupAdmitted covWRevCtorEnv 7 covWRevRec :=
  .recursor covWRevPolicy rfl covWRev_census
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact covWRevCtor_universe _ rfl rfl)
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact covWRevCtor_fields _ rfl rfl rfl)
    covWRev_minor_match covWRevDescriptor

private def covWRevFamTyT : HasTyT covUProjEnv 0 [] covWRevFam.mtype
    (.sort (.imax .zero (.succ .zero))) :=
  .pi _ _ _ _ _ (covUProjP_ty 0 []) (.sort _ _)

private def covWRevCtorTyT : HasTyT covWRevFamEnv 0 [] covWRevCtor.mtype
    (.sort (.imax .zero .zero)) :=
  .pi _ _ _ _ _ (.const _ 3 [] covUProjPMember rfl rfl rfl)
    (.app _ _ _ _ _ (.const _ 5 [] covWRevFam rfl rfl rfl) (.bvar _ 0 _ rfl))

private def covWRevRecSort : Level :=
  .imax (.imax .zero (.imax .zero (.succ (.param 0))))
    (.imax (.imax .zero (.param 0)) (.imax .zero (.imax .zero (.param 0))))

private def covWRevRecTyT : HasTyT covWRevCtorEnv 1 [] covWRevRecTy
    (.sort covWRevRecSort) :=
  (tyAtC covWRevCtorEnv 1 12 [] covWRevRecTy (.sort covWRevRecSort)).get (by rfl)

private theorem covWRevCtorTyped (E : ResolvedEnv)
    (hP : E.members 3 = some covUProjPMember)
    (h : E.members 5 = some covWRevFam) :
    CtorTypedT (covWRevCtorView E hP h) := by
  constructor
  · intro j
    have hj : j = ⟨0, by change 0 < 1; decide⟩ :=
      Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
    subst j
    exact ⟨.const _ 3 [] covUProjPMember hP rfl rfl⟩
  · intro j
    exact j.elim0

private theorem covWRevFamGroupTyped : IndGroupTypedT covWRevFam_admitted := by
  intro i
  have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
  subst i
  exact ⟨.const _ 3 [] covUProjPMember rfl rfl rfl⟩
private theorem covWRevCtorGroupTyped : IndGroupTypedT covWRevCtor_admitted :=
  ⟨(by
    intro i
    have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
      Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
    subst i
    exact ⟨.const _ 3 [] covUProjPMember rfl rfl rfl⟩),
    covWRevCtorTyped _ rfl rfl⟩
private theorem covWRevRecTyped : IndGroupTypedT covWRevRec_admitted :=
  ⟨(by
    intro i
    have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
      Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
    subst i
    exact ⟨.const _ 3 [] covUProjPMember rfl rfl rfl⟩),
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact covWRevCtorTyped _ rfl rfl),
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 12 Γ e T) rfl)⟩

private def covWRevMembers :
    GroupMembersT covWRevFamEnv covUProjEnv
      [(5, covWRevFam), (6, covWRevCtor), (7, covWRevRec)] covWRevEnv :=
  .cons _ 5 covWRevFam _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    covWRevFam_admitted PUnit.unit _ covWRevFamTyT (fun h => nomatch h)
    covWRevFamGroupTyped
    (.cons _ 6 covWRevCtor _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
      covWRevCtor_admitted PUnit.unit _ covWRevCtorTyT (fun _ => ⟨covWRevCtorTyT⟩)
      covWRevCtorGroupTyped
      (.cons _ 7 covWRevRec _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
        covWRevRec_admitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ covWRevRecTyT
        (fun h => nomatch h) covWRevRecTyped (.nil _)))

/-- The indexed singleton is admitted by the existing native group rules. -/
def covWRevEnv_wf : EnvWfT covWRevEnv :=
  .group covUProjEnv 5 covWRevFam [(6, covWRevCtor)] 7 covWRevRec covWRevEnv
    covUProjEnvWfT rfl (fun c hc => by simp at hc; subst c; rfl) rfl covWRevMembers

/-- An actual constructor redex whose index and field are beta-convertible. -/
def covWRevW : IotaWitness covWRevEnv where
  recRef := 7
  ctorRef := 6
  ls := [.zero]
  lsC := []
  recMember := covWRevRec
  ctorMember := covWRevCtor
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [covWRevMotive, covWRevMinor, covUProjProof]
  fields := [covWRevField]
  ctorParams := []
  kinds := [.plain]
  minor := covWRevMinor
  hlen := rfl
  familyRef := 5
  famMember := covWRevFam
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [covUProjP]
  ctorResult := .app (.const 5 []) (.bvar 0)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [covWRevMotTy, covWRevMinTy, covUProjP,
    .app (.const 5 []) (.bvar 0)]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := covWRevCtor.mtype
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

def covWRevP_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWRevEnv n Γ covUProjP (.sort .zero) :=
  .const Γ 3 [] covUProjPMember rfl rfl rfl

def covWRevIndex_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWRevEnv n Γ covUProjProof covUProjP :=
  .const Γ 4 [] covUProjProofMember rfl rfl rfl

def covWRevField_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWRevEnv n Γ covWRevField covUProjP :=
  .app _ _ _ _ _
    (.lam _ _ _ _ _ (covWRevP_ty n Γ) (.bvar _ 0 _ rfl))
    (covWRevIndex_ty n Γ)

/-- Native conversion is supplied explicitly, independently of observation. -/
def covWRev_field_index_conv (n : Nat) (Γ : LCtx) :
    ConvT covWRevEnv n Γ covWRevField covUProjProof covUProjP :=
  .beta _ _ _ _ _ _ (covWRevP_ty n Γ) (.bvar _ 0 _ rfl)
    (covWRevIndex_ty n Γ)

def covWRevFamily_ty (n : Nat) (Γ : LCtx) {q : Expr Nat}
    (hq : HasTyT covWRevEnv n Γ q covUProjP) :
    HasTyT covWRevEnv n Γ (covWRevFamily q) (.sort .zero) :=
  .app _ _ _ _ _ (.const Γ 5 [] covWRevFam rfl rfl rfl) hq

def covWRevMajor_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWRevEnv n Γ covWRevMajor (covWRevFamily covWRevField) :=
  .app _ _ _ _ _ (.const Γ 6 [] covWRevCtor rfl rfl rfl) (covWRevField_ty n Γ)

def covWRev_family_conv (n : Nat) (Γ : LCtx) :
    ConvT covWRevEnv n Γ (covWRevFamily covWRevField)
      (covWRevFamily covUProjProof) (.sort .zero) :=
  .app _ _ _ _ _ _ _ (.refl _ _ _ (.const Γ 5 [] covWRevFam rfl rfl rfl))
    (covWRev_field_index_conv n Γ)

def covWRevMajor_at_index (n : Nat) (Γ : LCtx) :
    HasTyT covWRevEnv n Γ covWRevMajor (covWRevFamily covUProjProof) :=
  .conv _ _ _ _ _ (covWRevMajor_ty n Γ) (covWRev_family_conv n Γ)

def covWRevMotive_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWRevEnv n Γ covWRevMotive
      (.pi covUProjP (.pi (covWRevFamily (.bvar 0)) (.sort .zero))) :=
  .lam _ _ _ _ _ (covWRevP_ty n Γ)
    (.lam _ _ _ _ _ (covWRevFamily_ty n _ (.bvar _ 0 _ rfl)) (covWRevP_ty n _))

private def covWRev_result_conv (n : Nat) (Γ : LCtx) {q h : Expr Nat}
    (hq : HasTyT covWRevEnv n Γ q covUProjP)
    (hh : HasTyT covWRevEnv n Γ h (covWRevFamily q)) :
    ConvT covWRevEnv n Γ (.app (.app covWRevMotive q) h)
      covUProjP (.sort .zero) := by
  have hβ : ConvT covWRevEnv n Γ (.app covWRevMotive q)
      (.lam (covWRevFamily q) covUProjP)
      (.pi (covWRevFamily q) (.sort .zero)) :=
    .beta _ _ _ _ _ _ (covWRevP_ty n Γ)
      (.lam _ _ _ _ _ (covWRevFamily_ty n _ (.bvar _ 0 _ rfl)) (covWRevP_ty n _)) hq
  exact .trans _ _ _ _ _
    (.app _ _ _ _ _ _ _ hβ (.refl _ _ _ hh))
    (.beta _ _ _ _ _ _ (covWRevFamily_ty n Γ hq) (covWRevP_ty n _) hh)

def covWRevMinor_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWRevEnv n Γ covWRevMinor
      (.pi covUProjP (.app (.app covWRevMotive (.bvar 0))
        (.app (.const 6 []) (.bvar 0)))) := by
  have hc : ConvT covWRevEnv n Γ
      (.pi covUProjP (.app (.app covWRevMotive (.bvar 0))
        (.app (.const 6 []) (.bvar 0))))
      (.pi covUProjP covUProjP) (.sort (.imax .zero .zero)) :=
    .pi _ _ _ _ _ _ _ (.refl _ _ _ (covWRevP_ty n Γ))
      (covWRev_result_conv n _ (.bvar _ 0 _ rfl)
        (.app _ _ _ _ _ (.const _ 6 [] covWRevCtor rfl rfl rfl) (.bvar _ 0 _ rfl)))
  exact .conv _ _ _ _ _
    (.lam _ _ _ _ _ (covWRevP_ty n Γ) (covWRevIndex_ty n _))
    (.symm _ _ _ _ hc)

/-- The complete saturated constructor call has the actual native result type. -/
def covWRevCall_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWRevEnv n Γ (iotaLhsOf covWRevW) covUProjP := by
  have hcall : HasTyT covWRevEnv n Γ (iotaLhsOf covWRevW)
      (.app (.app covWRevMotive covUProjProof) covWRevMajor) :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _ (.const Γ 7 [.zero] covWRevRec rfl rfl rfl)
            (covWRevMotive_ty n Γ))
          (covWRevMinor_ty n Γ))
        (covWRevIndex_ty n Γ))
      (covWRevMajor_at_index n Γ)
  exact .conv _ _ _ _ _ hcall
    (covWRev_result_conv n Γ (covWRevIndex_ty n Γ) (covWRevMajor_at_index n Γ))

/-- Both the native and independent strict-model index certificates hold. -/
theorem covWRev_index_guard (n : Nat) (Γ : LCtx) :
    KIndexGuardAt covWRevEnv n Γ covWRevW := by
  refine ⟨⟨covWRev_family_conv n Γ⟩, ?_⟩
  intro ρ
  change SemEqDI covWRevEnv ρ (covWRevFamily covWRevField)
    (covWRevFamily covUProjProof)
  exact semEqDI_app (semEqDI_refl covWRevEnv ρ (.const 5 []))
    (approxDI_beta covWRevEnv ρ covUProjP (.bvar 0) covUProjProof)

theorem covWRev_common (n : Nat) (Γ : LCtx) :
    KCommonAt covWRevEnv n Γ covWRevW covWRevMajor :=
  ⟨⟨covWRevFamily_ty n Γ (covWRevIndex_ty n Γ)⟩,
    ⟨covWRevMajor_at_index n Γ⟩, ⟨covWRevMajor_at_index n Γ⟩⟩

/-- The revealed entry selects `p`; the actual field is its proof beta expansion. -/
theorem covWRev_is_revealed :
    KFieldW covWRevW ∧ revealedPos? covWRevW 0 = some 0 ∧
    (projFields covWRevW (ctorMajor covWRevW)).getD 0 (.sort .zero) = covUProjProof ∧
    covWRevW.fields.getD 0 (.sort .zero) = covWRevField :=
  ⟨⟨by decide, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

private theorem covWRev_P_rigid : RigidConst covWRevEnv 3 := by
  intro m hm
  have he : m = covUProjPMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

private theorem covWRev_p_rigid : RigidConst covWRevEnv 4 := by
  intro m hm
  have he : m = covUProjProofMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

private theorem covWRev_p_not_propCtor : ¬ PropCtorT covWRevEnv 4 := by
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  have he : m = covUProjProofMember := Option.some.inj hm.symm
  subst m
  exact MemberClass.noConfusion hctor

private theorem covWRev_P_positive {ρ : EnvT} {c : CptT}
    (h : ApproxT covWRevEnv ρ covUProjP c) : IsPropCT covWRevEnv c := by
  rcases approxT_rigid_const_inv covWRev_P_rigid h with rfl | rfl
  · exact .bot
  · exact .spine (m := covUProjPMember) rfl rfl

/-- This uses only lambda, variable and proposition-domain typing inversion. -/
theorem covWRev_identity_bot {ρ : EnvT} {c : CptT}
    (h : ApproxT covWRevEnv ρ (.lam covUProjP (.bvar 0)) c) : c = .bot := by
  rcases approxT_lam_inv h with hbot | ⟨a, g, rfl, ha, hne, hg⟩
  · exact hbot
  · obtain ⟨s, hs, hnb⟩ := hne
    rcases approxT_bvar_inv (hg s hs).2 with hb | hb
    · exact (hnb hb).elim
    · exact (hnb (ctyS_prop_bot (covWRev_P_positive ha) ((hg s hs).1 _ hb))).elim

/-- Every observation of the actual field is bottom. No recursor occurs in it. -/
theorem covWRev_field_bot {ρ : EnvT} {c : CptT}
    (h : ApproxT covWRevEnv ρ covWRevField c) : c = .bot :=
  covUProj_app_bot_of_function_bot (fun _ => covWRev_identity_bot) h

/-- The selected index has its rigid nonbottom observation in the aligned model. -/
theorem covWRev_index_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKW covWRevEnv n Γ ρ covUProjProof (.spine 4 []) :=
  .free (kFreeT_rigid_const covWRev_p_rigid [])
    (.const ρ 4 [] covWRev_p_rigid covWRev_p_not_propCtor)

/-- The same compact is absent from the actual field. -/
theorem covWRev_field_not_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ¬ ApproxTKW covWRevEnv n Γ ρ covWRevField (.spine 4 []) := by
  intro h
  exact CptT.noConfusion
    (covWRev_field_bot (approxTN_forget (approxTKN_forgetN (approxTKW_forget h))))

/-- The distinguishing proof compact is not a typed demand at the actual
observed proposition code. This bounds the counterexample's scope. -/
theorem covWRev_not_typed_demand (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTKW covWRevEnv n Γ ρ covUProjP (.spine 3 []) ∧
    IsPropCT covWRevEnv (.spine 3 []) ∧
    ¬ CTyS covWRevEnv (.spine 4 []) (.spine 3 []) := by
  have hnp : ¬ PropCtorT covWRevEnv 3 := by
    rintro ⟨m, fam, fm, hm, hctor, _⟩
    have he : m = covUProjPMember := Option.some.inj hm.symm
    subst m
    exact MemberClass.noConfusion hctor
  have hp : IsPropCT covWRevEnv (.spine 3 []) :=
    .spine (m := covUProjPMember) rfl rfl
  refine ⟨.free (kFreeT_rigid_const covWRev_P_rigid [])
    (.const ρ 3 [] covWRev_P_rigid hnp), hp, ?_⟩
  intro ht
  exact CptT.noConfusion (ctyS_prop_bot hp ht)

/-- The actual field has a normal reduct: it beta-reduces to the selected
index itself. The failure is observation transport across that expansion. -/
theorem covWRev_field_normal_readback (n : Nat) (Γ : LCtx) :
    RedR (WhStepCK2 covWRevEnv n) Γ covWRevField covUProjProof ∧
    NormalR (WhStepCK2 covWRevEnv n) Γ covUProjProof :=
  ⟨redR_single (.ctx (.beta covUProjP (.bvar 0) covUProjProof)),
    covV_body_free_spine_normal (m := covUProjProofMember)
      (rfl : covWRevEnv.members 4 = some covUProjProofMember) rfl (by decide) [] []⟩

/-- The desired implication fails at a closed, admitted, fully typed native
constructor call.  Both native and DI index alignment are supplied; the
failure is already in the direct proof-identity lambda/application rules. -/
theorem covW_revealed_field_boundary (n : Nat) :
    Nonempty (EnvWfT covWRevEnv) ∧ Nonempty (CtxWfT covWRevEnv n []) ∧
    CovWRealized covWRevEnv n 1 [] EnvT.bot SubstT.id ∧
    EnvTypedFinAtT (⟨ApproxTKW covWRevEnv n []⟩ : CtxModelT covWRevEnv) [] EnvT.bot ∧
    CtxEnvM (⟨ApproxTKW covWRevEnv n []⟩ : CtxModelT covWRevEnv) [] EnvT.bot ∧
    KFieldW covWRevW ∧ 0 < covWRevW.fields.length ∧
    revealedPos? covWRevW 0 = some 0 ∧
    Nonempty (HasTyT covWRevEnv n [] covUProjP (.sort .zero)) ∧
    Nonempty (HasTyT covWRevEnv n [] covUProjProof covUProjP) ∧
    Nonempty (HasTyT covWRevEnv n [] covWRevField covUProjP) ∧
    Nonempty (ConvT covWRevEnv n [] covWRevField covUProjProof covUProjP) ∧
    Nonempty (HasTyT covWRevEnv n [] covWRevMajor (covWRevFamily covUProjProof)) ∧
    Nonempty (HasTyT covWRevEnv n [] (iotaLhsOf covWRevW) covUProjP) ∧
    KIndexGuardAt covWRevEnv n [] covWRevW ∧
    KCommonAt covWRevEnv n [] covWRevW (ctorMajor covWRevW) ∧
    ApproxTKW covWRevEnv n [] EnvT.bot
      ((projFields covWRevW (ctorMajor covWRevW)).getD 0 (.sort .zero)) (.spine 4 []) ∧
    ¬ ApproxTKW covWRevEnv n [] EnvT.bot
      (covWRevW.fields.getD 0 (.sort .zero)) (.spine 4 []) := by
  exact ⟨⟨covWRevEnv_wf⟩, ⟨.nil⟩, covW_realized_nil covWRevEnv n 1,
    envTypedFinAtT_nil _ _, (fun _ _ hv => Option.noConfusion hv),
    covWRev_is_revealed.1, by decide, covWRev_is_revealed.2.1,
    ⟨covWRevP_ty n []⟩, ⟨covWRevIndex_ty n []⟩, ⟨covWRevField_ty n []⟩,
    ⟨covWRev_field_index_conv n []⟩, ⟨covWRevMajor_at_index n []⟩,
    ⟨covWRevCall_ty n []⟩, covWRev_index_guard n [], covWRev_common n [],
    covWRev_index_observed n [] EnvT.bot, covWRev_field_not_observed n [] EnvT.bot⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_REVEALED_ROOTS
#print axioms covW_revealed_projField
#print axioms covWRevFam
#print axioms covWRevCtor
#print axioms covWRevMotTy
#print axioms covWRevMinTy
#print axioms covWRevRecTy
#print axioms covWRevRec
#print axioms covWRevFamEnv
#print axioms covWRevCtorEnv
#print axioms covWRevEnv
#print axioms covWRevField
#print axioms covWRevMajor
#print axioms covWRevFamily
#print axioms covWRevMotive
#print axioms covWRevMinor
#print axioms covWRevEnv_wf
#print axioms covWRevW
#print axioms covWRevP_ty
#print axioms covWRevIndex_ty
#print axioms covWRevField_ty
#print axioms covWRev_field_index_conv
#print axioms covWRevFamily_ty
#print axioms covWRevMajor_ty
#print axioms covWRev_family_conv
#print axioms covWRevMajor_at_index
#print axioms covWRevMotive_ty
#print axioms covWRevMinor_ty
#print axioms covWRevCall_ty
#print axioms covWRev_index_guard
#print axioms covWRev_common
#print axioms covWRev_is_revealed
#print axioms covWRev_identity_bot
#print axioms covWRev_field_bot
#print axioms covWRev_index_observed
#print axioms covWRev_field_not_observed
#print axioms covWRev_not_typed_demand
#print axioms covWRev_field_normal_readback
#print axioms covW_revealed_field_boundary
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_REVEALED_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWAudit
