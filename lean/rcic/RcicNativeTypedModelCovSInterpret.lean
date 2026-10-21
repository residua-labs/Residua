import rcic.RcicNativeTypedModelCovSTemplate
import rcic.RcicNativeTypedModelCovSOperators

/-!
# Candidate interpretation of erased observed templates

Every finite template has a supplied candidate. At an observed `.prop` or
`.sort` domain shape the interpretation uses the actual candidate quantifier.
The raw shape does not certify a native sort binder. Observed Pi rows
provide finitely many output constraints, intersected without selecting a
row after a native type argument. Their erased callbacks cannot reconstruct
an opaque bound-variable occurrence: the Origin and Substitution modules
measure precisely that failure. This is a diagnostic total interpretation,
not a general native observation theorem. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit ReadbackCK2Audit
open TypedModelCovRAudit

def covSBuildRows {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (rows : List (List CptT × CovSObsSyntax))
    (F : ∀ row, row ∈ rows → CovSDataCandidate E n Γ) : CovSDataCandidate E n Γ :=
  CovSDataCandidate.rows (rows.attach.map fun row => (row.val.1, F row.val row.property))

theorem covS_template_pair_snd_lt (row : List CptT × CovSObsSyntax) :
    sizeOf row.2 < sizeOf row := by
  cases row
  simp only [Prod.mk.sizeOf_spec]
  omega

def interpretObsTemplate (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (t : CovSObsSyntax) :
    CovSDataCandidate E n Γ :=
  match t with
  | .unknown => .total E n Γ
  | .prop => .prop E n Γ
  | .sort => .sort E n Γ
  | .rigid _ _ => .rigid E n Γ
  | .var i => v i
  | .ordinary D rows =>
      .ordinary (interpretObsTemplate E n Γ v D)
        (covSBuildRows rows (fun row _ => interpretObsTemplate E n Γ v row.2))
  | .allProp rows =>
      .allProp (covSBuildRows rows (fun row _ => interpretObsTemplate E n Γ v row.2))
  | .allSort rows =>
      .allSort (covSBuildRows rows (fun row _ => interpretObsTemplate E n Γ v row.2))
  | .unknownPi _ => .total E n Γ
  | .unsupportedLambda _ => .total E n Γ
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have h₁ := List.sizeOf_lt_of_mem (show row ∈ rows from ‹_›)
      have h₂ := covS_template_pair_snd_lt row
      omega

def covSBaseVal (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Nat → CovSDataCandidate E n Γ := fun _ => .total E n Γ

def covSObsInterp (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (a : CptT) : CovSRel :=
  (interpretObsTemplate E n Γ v (templateOfObs a)).relation

theorem covSObsInterp_isCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (a : CptT) :
    CandidateCovS E (WhStepCK2 E n) Γ false (covSObsInterp E n Γ v a) :=
  (interpretObsTemplate E n Γ v (templateOfObs a)).laws

/-- An externally supplied positivity flag selects total proof equivalence.
Native positivity must be supplied separately; raw compacts do not supply
its native typing, and this function is not a positivity detector. -/
def covSNativeInterp (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (positive : Bool) (a : CptT) : CovSRel :=
  if positive then covSTotalRel else covSObsInterp E n Γ v a

theorem covSNativeInterp_isCandidate (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (p : Bool) (a : CptT) :
    CandidateCovS E (WhStepCK2 E n) Γ p (covSNativeInterp E n Γ v p a) := by
  cases p with
  | false => exact covSObsInterp_isCandidate E n Γ v a
  | true => exact covSTotal_isCandidate E _ Γ true

theorem covSObsInterp_bot (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) :
    covSObsInterp E n Γ v .bot = covSTotalRel := by
  unfold covSObsInterp
  rw [templateOfObs_bot, interpretObsTemplate]
  rfl

theorem covSObsInterp_prop (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) :
    covSObsInterp E n Γ v .prop = covRCodeRel E .prop := by
  unfold covSObsInterp
  rw [templateOfObs_prop, interpretObsTemplate]
  rfl

theorem covSObsInterp_sort (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) :
    covSObsInterp E n Γ v .sort = covRCodeRel E .sort := by
  unfold covSObsInterp
  rw [templateOfObs_sort, interpretObsTemplate]
  rfl

theorem covSObsInterp_unknownPi (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) :
    covSObsInterp E n Γ v (.pi .bot []) = covSTotalRel := by
  unfold covSObsInterp
  rw [templateOfObs_empty_pi, interpretObsTemplate]
  rfl

/-- Unknown information accepts every term and compact without requesting
native readback, a normal form, typing of the term, or a value computation. -/
theorem covS_unknown_accepts_all (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (x y : Expr Nat) (c : CptT) :
    covSObsInterp E n Γ v .bot x y c := by
  rw [covSObsInterp_bot]
  trivial

def CovSJoint (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (v : Nat → CovSDataCandidate E n Γ) (p : Bool) (a : CptT)
    (x y : Expr Nat) (c : CptT) : Prop :=
  covSNativeInterp E n Γ v p a x y c ∧
  covSNativeInterp E n Γ v p a x x c ∧
  covSNativeInterp E n Γ v p a y y c

theorem covSJoint_of_related {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v : Nat → CovSDataCandidate E n Γ} {p : Bool} {a c : CptT}
    {x y : Expr Nat} (h : covSNativeInterp E n Γ v p a x y c) :
    CovSJoint E n Γ v p a x y c := by
  have hc := covSNativeInterp_isCandidate E n Γ v p a
  exact ⟨h, hc.self_left h, hc.self_right h⟩

theorem covSJoint_trans {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v : Nat → CovSDataCandidate E n Γ} {p : Bool} {a c : CptT}
    {x y z : Expr Nat} (hxy : CovSJoint E n Γ v p a x y c)
    (hyz : CovSJoint E n Γ v p a y z c) : CovSJoint E n Γ v p a x z c :=
  covSJoint_of_related ((covSNativeInterp_isCandidate E n Γ v p a).trans hxy.1 hyz.1)

/-- Equal decoded templates give equal interpretations. The equality is
an explicit premise; native type conversion does not yet supply it. -/
theorem covSObsInterp_congr_template {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v : Nat → CovSDataCandidate E n Γ} {a b : CptT}
    (h : templateOfObs a = templateOfObs b) :
    covSObsInterp E n Γ v a = covSObsInterp E n Γ v b := by
  unfold covSObsInterp
  rw [h]

theorem covSJoint_reindex_template {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v : Nat → CovSDataCandidate E n Γ} {p : Bool} {a b c : CptT}
    {x y : Expr Nat} (h : templateOfObs a = templateOfObs b) :
    CovSJoint E n Γ v p a x y c ↔ CovSJoint E n Γ v p b x y c := by
  simp only [CovSJoint, covSNativeInterp, covSObsInterp_congr_template h]

theorem covSJoint_symm {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v : Nat → CovSDataCandidate E n Γ} {p : Bool} {a c : CptT}
    {x y : Expr Nat} (h : CovSJoint E n Γ v p a x y c) :
    CovSJoint E n Γ v p a y x c :=
  ⟨(covSNativeInterp_isCandidate E n Γ v p a).symm h.1, h.2.2, h.2.1⟩

/-- A same-template transitivity consumer, with no finite code to join.
It does not identify independently chosen native type observations. -/
theorem covSJoint_trans_templates {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v : Nat → CovSDataCandidate E n Γ} {p : Bool} {a b c : CptT}
    {x y z : Expr Nat} (h : templateOfObs a = templateOfObs b)
    (hxy : CovSJoint E n Γ v p a x y c)
    (hyz : CovSJoint E n Γ v p b y z c) :
    CovSJoint E n Γ v p a x z c :=
  covSJoint_trans hxy ((covSJoint_reindex_template h).mpr hyz)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_INTERPRET_ROOTS
#print axioms covSBuildRows
#print axioms covS_template_pair_snd_lt
#print axioms interpretObsTemplate
#print axioms covSBaseVal
#print axioms covSObsInterp
#print axioms covSObsInterp_isCandidate
#print axioms covSNativeInterp
#print axioms covSNativeInterp_isCandidate
#print axioms covSObsInterp_bot
#print axioms covSObsInterp_prop
#print axioms covSObsInterp_sort
#print axioms covSObsInterp_unknownPi
#print axioms covS_unknown_accepts_all
#print axioms CovSJoint
#print axioms covSJoint_of_related
#print axioms covSJoint_trans
#print axioms covSObsInterp_congr_template
#print axioms covSJoint_reindex_template
#print axioms covSJoint_symm
#print axioms covSJoint_trans_templates
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_INTERPRET_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
