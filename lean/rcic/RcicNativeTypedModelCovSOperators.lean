import rcic.RcicNativeTypedModelCovSCandidate
import rcic.RcicNativeTypedModelCovRForall

/-!
# Candidate operators by composition with the R operators

Positive S candidates are exactly the total relation. The input adapter
below makes this change explicit while reusing the false-tag R forall
operator. Its elimination rule quantifies over the actual S candidate
class. Ordinary arrows retain the strict stored-row rule; absent a native
domain view, the diagnostic operator checks every native domain rather
than fabricating one. This is closure, not native adequacy.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit ReadbackCK2Audit
open TypedModelCovXAudit TypedModelCovRAudit

def covSInput (positive : Bool) (S : CovSRel) : CovSRel :=
  if positive then covSTotalRel else S

theorem covSInput_isCandidate {E : ResolvedEnv} {R : Readback} {Γ : LCtx}
    (p : Bool) {S : CovSRel} (hS : CandidateCov E R Γ false S) :
    CandidateCovS E R Γ p (covSInput p S) := by
  cases p with
  | false => exact candidateCovS_of_R_false hS
  | true => exact covSTotal_isCandidate E R Γ true

def covSForall (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level)
    (p : Bool) (Body : CovRForallBody) : CovSRel :=
  covRForall E n Γ l false false (fun T S => Body T (covSInput p S))

theorem covSForall_isCandidate {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {l : Level} {p : Bool} {Body : CovRForallBody}
    (hBody : ∀ T S, CandidateCovS E (WhStepCK2 E n) Γ p S →
      CandidateCovS E (WhStepCK2 E n) Γ false (Body T S)) :
    CandidateCovS E (WhStepCK2 E n) Γ false (covSForall E n Γ l p Body) :=
  candidateCovS_of_R_false (covRForall_isCandidate
    (fun T S hS => candidateCovR_of_S_false
      (hBody T (covSInput p S) (covSInput_isCandidate p hS))))

theorem covSForall_shape {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {l : Level} {p : Bool} {Body : CovRForallBody}
    {x y : Expr Nat} {c : CptT}
    (h : covSForall E n Γ l p Body x y c) : CovRFunctionShape c := h.1

theorem covSForall_intro {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {l : Level} {p : Bool} {Body : CovRForallBody}
    {x y : Expr Nat} {c : CptT} (hs : CovRFunctionShape c)
    (h : ∀ ds out, CovXCompactAction E c ds out →
      ∀ T, HasTyT E n Γ T (.sort l) →
      ∀ S, CandidateCovS E (WhStepCK2 E n) Γ p S →
        Body T S (.app x T) (.app y T) out) :
    covSForall E n Γ l p Body x y c := by
  refine ⟨hs, ?_, ?_⟩
  · intro he
    cases he
  · intro ds out ha T hT S hS
    exact h ds out ha T hT (covSInput p S) (covSInput_isCandidate p hS)

theorem covSForall_apply {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {l : Level} {p : Bool} {Body : CovRForallBody}
    {x y : Expr Nat} {c out : CptT} {ds : List CptT}
    (h : covSForall E n Γ l p Body x y c)
    (ha : CovXCompactAction E c ds out)
    (T : Expr Nat) (hT : HasTyT E n Γ T (.sort l))
    (S : CovSRel) (hS : CandidateCovS E (WhStepCK2 E n) Γ p S) :
    Body T S (.app x T) (.app y T) out := by
  cases p with
  | false =>
      exact covRForall_apply h ha T hT S (candidateCovR_of_S_false hS)
  | true =>
      have he := hS.positive_eq_total
      subst S
      exact covRForall_apply h ha T hT covSTotalRel
        (candidateCovR_of_S_false (covSTotal_isCandidate E _ Γ false))

structure CovSDataCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx) where
  relation : CovSRel
  laws : CandidateCovS E (WhStepCK2 E n) Γ false relation

def CovSDataCandidate.total (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovSDataCandidate E n Γ :=
  ⟨covSTotalRel, covSTotal_isCandidate E _ Γ false⟩

def CovSDataCandidate.prop (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovSDataCandidate E n Γ :=
  ⟨covRCodeRel E .prop, candidateCovS_of_R_false (covRProp_isCandidate E _ Γ)⟩

def CovSDataCandidate.sort (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovSDataCandidate E n Γ :=
  ⟨covRCodeRel E .sort, candidateCovS_of_R_false (covRSort_isCandidate E _ Γ)⟩

/-- Closed rigid data leaf. A positive native type uses the separate total
positive wrapper; this erased-head leaf does not infer native Prop typing. -/
def covSRigidRel : CovSRel :=
  fun _ _ c => c = .bot ∨ ∃ r us, c = .spine r us

theorem covSRigid_isCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CandidateCovS E (WhStepCK2 E n) Γ false covSRigidRel := by
  apply candidateCovS_of_R_false
  apply covRCandidate_compact
  · exact Or.inl rfl
  · intro _ r us _
    exact Or.inr ⟨r, us, rfl⟩
  · intro he
    cases he

def CovSDataCandidate.rigid (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CovSDataCandidate E n Γ := ⟨covSRigidRel, covSRigid_isCandidate E n Γ⟩

def CovSDataCandidate.rows {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (rows : List (List CptT × CovSDataCandidate E n Γ)) : CovSDataCandidate E n Γ :=
  ⟨covSMeet (fun r : {r // r ∈ rows} => r.val.2.relation),
    covSMeet_isCandidate (fun r => r.val.2.laws)⟩

def CovSDataCandidate.ordinary {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (D B : CovSDataCandidate E n Γ) : CovSDataCandidate E n Γ :=
  ⟨covSMeet (fun Dty : Expr Nat => covRArrow E n Γ false Dty D.relation B.relation),
    covSMeet_isCandidate (fun _ => candidateCovS_of_R_false
      (covRArrow_isCandidate (candidateCovR_of_S_false D.laws)
        (candidateCovR_of_S_false B.laws)))⟩

def CovSDataCandidate.allProp {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (B : CovSDataCandidate E n Γ) : CovSDataCandidate E n Γ :=
  ⟨covSForall E n Γ .zero true (fun _ _ => B.relation),
    covSForall_isCandidate (fun _ _ _ => B.laws)⟩

/-- `.sort` has erased its nonzero level. The raw template conservatively
tests all compatible levels; the Origin boundary forbids recovering one. -/
def CovSDataCandidate.allSort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (B : CovSDataCandidate E n Γ) : CovSDataCandidate E n Γ :=
  ⟨covSMeet (fun l : {l // sortCode l = .sort} =>
      covSForall E n Γ l.val false (fun _ _ => B.relation)),
    covSMeet_isCandidate (fun _ => covSForall_isCandidate (fun _ _ _ => B.laws))⟩

theorem covS_nonzero_level_inhabited :
    Nonempty {l : Level // sortCode l = .sort} :=
  ⟨⟨.succ .zero, rfl⟩⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_OPERATORS_ROOTS
#print axioms covSInput
#print axioms covSInput_isCandidate
#print axioms covSForall
#print axioms covSForall_isCandidate
#print axioms covSForall_shape
#print axioms covSForall_intro
#print axioms covSForall_apply
#print axioms CovSDataCandidate
#print axioms CovSDataCandidate.total
#print axioms CovSDataCandidate.prop
#print axioms CovSDataCandidate.sort
#print axioms covSRigidRel
#print axioms covSRigid_isCandidate
#print axioms CovSDataCandidate.rigid
#print axioms CovSDataCandidate.rows
#print axioms CovSDataCandidate.ordinary
#print axioms CovSDataCandidate.allProp
#print axioms CovSDataCandidate.allSort
#print axioms covS_nonzero_level_inhabited
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_OPERATORS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
