import rcic.RcicNativeTypedModelCovWIrrelNativeEtaBody
import rcic.RcicNativeTypedModelCovWIrrelRepair

/-!
# Complete observation shape of the admitted proof family

The finite invariant follows graph application as well as native eta.
At the bare family a graph can occur, but every row output is bottom or
the unique proof-erased family application. At an application already
typed in Sort 0 no lambda observation remains. The native eta-step
certificate below is supplied separately by admitted native typing.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKFragmentAudit TypedModelCovUAudit TypedModelCovWAudit
open TypedModelCovWEtaAudit TypedModelCovSAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def CovWIrrelFamilyResult (c : CptWIrrel) : Prop :=
  c = .bot ∨ c = covWIrrelCoarse

def CovWIrrelFamilyShape : Bool → CptWIrrel → Prop
  | false, c => c = .bot ∨ c = .spine 5 [] [] ∨
      ∃ rows, c = .lam rows ∧ ∀ s ∈ rows, CovWIrrelFamilyResult s.2
  | true, c => CovWIrrelFamilyResult c

inductive CovWIrrelFamilySource (n : Nat) (Γ : LCtx) : Bool → Expr Nat → Prop
  | head : CovWIrrelFamilySource n Γ false covWIrrelFamily
  | applied {x : Expr Nat}
      (ht : Nonempty (HasTyT covWIrrelEnv n Γ
        (.app covWIrrelFamily x) (.sort .zero))) :
      CovWIrrelFamilySource n Γ true (.app covWIrrelFamily x)

private theorem source_headConst {n : Nat} {Γ : LCtx} {b : Bool} {e : Expr Nat}
    (hs : CovWIrrelFamilySource n Γ b e) : headConst e = some 5 := by
  cases hs <;> rfl

private theorem headConst_fold_full (e : Expr Nat) (xs : List (Expr Nat)) :
    headConst (foldApps e xs) = headConst e := by
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih => exact ih (.app e x)

private theorem raw_family_head_shape {n : Nat} {ρ : EnvWIrrel}
    {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTWIrrel covWIrrelEnv n ρ e c)
    (he : CovWIrrelHeadTerm 5 [] 0 e) :
    c = .bot ∨ c = .spine 5 [] [] := by
  cases h with
  | bot => exact Or.inl rfl
  | bvar => cases he
  | sort => cases he
  | pi => cases he
  | lam => cases he
  | app => cases he
  | const => cases he; exact Or.inr rfl
  | delta hd _ =>
      cases he
      exact (not_rigidConst_of_deltaConst hd covWIrrel_family_rigid).elim
  | recursor ls hp hpre hf h =>
      have heq : (‹IotaWitnessS covWIrrelEnv›).recRef = 5 :=
        Option.some.inj he.headConst
      have hr : RigidConst covWIrrelEnv (‹IotaWitnessS covWIrrelEnv›).recRef := by
        rw [heq]
        exact covWIrrel_family_rigid
      exact ((hr _ ‹IotaWitnessS covWIrrelEnv›.hrec).2
        ‹IotaWitnessS covWIrrelEnv›.hrecK).elim
  | appSpine => cases he
  | letE => cases he
  | lit => cases he

theorem covWIrrel_raw_family_applied_shape {n : Nat} {ρ : EnvWIrrel}
    {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTWIrrel covWIrrelEnv n ρ e c)
    (he : CovWIrrelHeadTerm 5 [] 1 e) : CovWIrrelFamilyResult c := by
  cases h with
  | bot => exact Or.inl rfl
  | bvar => cases he
  | sort => cases he
  | pi => cases he
  | lam => cases he
  | app hf hs ha =>
      cases he with
      | app hh =>
          rcases raw_family_head_shape hf hh with h | h <;> cases h
  | const => cases he
  | delta => cases he
  | recursor => cases he
  | appSpine hf ha hp =>
      cases he with
      | app hh =>
          rcases raw_family_head_shape hf hh with h | h
          · cases h
          · cases h
            have hu := hp (covWIrrel_family_proof_position n)
            rw [hu]
            exact Or.inr rfl
  | letE => cases he
  | lit => cases he

/-- The exact native fact needed when eta observes the bare family. Its
conclusion includes the well-formed extended context and the actual body
typing, so no arbitrary-context separation is used. -/
def CovWIrrelFamilyEtaStep (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {D B : Expr Nat}, CtxWfT covWIrrelEnv n Γ →
    HasTyT covWIrrelEnv n Γ covWIrrelFamily (.pi D B) →
    Nonempty (CtxWfT covWIrrelEnv n (.assumption D :: Γ) ×
      HasTyT covWIrrelEnv n (.assumption D :: Γ)
        (.app covWIrrelFamily (.bvar 0)) (.sort .zero))

theorem covWIrrel_family_shape_of_native {n : Nat}
    (hScope : covWIrrelEnv_wf.InScope) (hstep : CovWIrrelFamilyEtaStep n)
    {Γ : LCtx} {ρ : EnvWIrrel} {e : Expr Nat} {c : CptWIrrel}
    (h : ApproxTKWIrrel covWIrrelEnv n Γ ρ e c) :
    ∀ {b : Bool}, CtxWfT covWIrrelEnv n Γ →
      CovWIrrelFamilySource n Γ b e → CovWIrrelFamilyShape b c := by
  induction h with
  | bot =>
      intro b hΓ hs
      cases b <;> exact Or.inl rfl
  | free _ h =>
      intro b hΓ hs
      cases hs with
      | head =>
          rcases raw_family_head_shape h .head with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
      | applied _ => exact covWIrrel_raw_family_applied_shape h (.app .head)
  | pi => intro b hΓ hs; cases hs
  | lam => intro b hΓ hs; cases hs
  | app hf hs ha ihf iha =>
      intro b hΓ he
      cases he with
      | applied _ =>
          have hh := ihf hΓ CovWIrrelFamilySource.head
          rcases hh with h | h | ⟨rows, h, hrows⟩
          · cases h
          · cases h
          · cases h
            exact hrows _ hs
  | appSpine hf ha hp ihf iha =>
      intro b hΓ he
      cases he with
      | applied _ =>
          have hh := ihf hΓ CovWIrrelFamilySource.head
          rcases hh with h | h | ⟨rows, h, hrows⟩
          · cases h
          · cases h
            have hu := hp (covWIrrel_family_proof_position n)
            rw [hu]
            exact Or.inr rfl
          · cases h
  | delta hd _ _ =>
      intro b hΓ he
      cases he
      exact (not_rigidConst_of_deltaConst hd covWIrrel_family_rigid).elim
  | letE => intro b hΓ hs; cases hs
  | lit => intro b hΓ hs; cases hs
  | iota w _ _ _ =>
      intro b hΓ hs
      have heq := source_headConst hs
      rw [iotaLhsOfS, recCall, headConst_fold_full] at heq
      have heq : w.recRef = 5 := Option.some.inj heq
      have hr : RigidConst covWIrrelEnv w.recRef := by
        rw [heq]
        exact covWIrrel_family_rigid
      exact ((hr _ w.hrec).2 w.hrecK).elim
  | recursorPropK w x _ _ _ _ _ _ _ =>
      intro b hΓ hs
      have heq := source_headConst hs
      rw [recCall, headConst_fold_full] at heq
      have heq : w.recRef = 5 := Option.some.inj heq
      have hr : RigidConst covWIrrelEnv w.recRef := by
        rw [heq]
        exact covWIrrel_family_rigid
      exact ((hr _ w.hrec).2 w.hrecK).elim
  | eta he hD ht hn hb ihD ihb =>
      intro b hΓ hs
      cases hs with
      | head =>
          obtain ⟨⟨hΓ', hbody⟩⟩ := hstep hΓ he
          refine Or.inr (Or.inr ⟨_, rfl, ?_⟩)
          intro s hs
          exact ihb s hs hΓ' (.applied ⟨hbody⟩)
      | applied hsort =>
          obtain ⟨hsort⟩ := hsort
          exact (covWIrrel_native_not_sort_and_pi covWIrrelEnv_wf
            hScope hΓ hsort he).elim

theorem covWIrrel_family_applied_all_shape_of_native {n : Nat}
    (hScope : covWIrrelEnv_wf.InScope) (hstep : CovWIrrelFamilyEtaStep n)
    {Γ : LCtx} (hΓ : CtxWfT covWIrrelEnv n Γ) {ρ : EnvWIrrel}
    {x : Expr Nat} {c : CptWIrrel}
    (ht : HasTyT covWIrrelEnv n Γ (.app covWIrrelFamily x) (.sort .zero))
    (h : ApproxTKWIrrel covWIrrelEnv n Γ ρ (.app covWIrrelFamily x) c) :
    c = .bot ∨ c = covWIrrelCoarse :=
  covWIrrel_family_shape_of_native hScope hstep h hΓ (.applied ⟨ht⟩)

theorem covWIrrel_family_all_observations_equal_of_native (n : Nat)
    (hScope : covWIrrelEnv_wf.InScope) (hstep : CovWIrrelFamilyEtaStep n)
    (Γ : LCtx) (hΓ : CtxWfT covWIrrelEnv n Γ) (ρ : EnvWIrrel)
    (c : CptWIrrel) :
    ApproxTKWIrrel covWIrrelEnv n Γ ρ covWIrrelLeft c ↔
      ApproxTKWIrrel covWIrrelEnv n Γ ρ covWIrrelRight c := by
  constructor <;> intro h
  · rcases covWIrrel_family_applied_all_shape_of_native hScope hstep hΓ
        (covWIrrel_left_ty n Γ) h with rfl | rfl
    · exact .bot _ _ _
    · exact covWIrrel_right_new n Γ ρ
  · rcases covWIrrel_family_applied_all_shape_of_native hScope hstep hΓ
        (covWIrrel_right_ty n Γ) h with rfl | rfl
    · exact .bot _ _ _
    · exact covWIrrel_left_new n Γ ρ

theorem covWIrrel_family_all_public_observations_equal_of_native (n : Nat)
    (hScope : covWIrrelEnv_wf.InScope) (hstep : CovWIrrelFamilyEtaStep n)
    (Γ : LCtx) (hΓ : CtxWfT covWIrrelEnv n Γ) (ρ : EnvWIrrel)
    (c : CptT) :
    CovWIrrelObservation covWIrrelEnv n Γ ρ covWIrrelLeft c ↔
      CovWIrrelObservation covWIrrelEnv n Γ ρ covWIrrelRight c := by
  constructor <;> rintro ⟨d, hd, h⟩
  · exact ⟨d, hd,
      (covWIrrel_family_all_observations_equal_of_native n hScope hstep Γ hΓ ρ d).mp h⟩
  · exact ⟨d, hd,
      (covWIrrel_family_all_observations_equal_of_native n hScope hstep Γ hΓ ρ d).mpr h⟩

/-- The native certificate is actually inhabited in the admitted fixture. -/
theorem covWIrrel_family_eta_step (n : Nat) : CovWIrrelFamilyEtaStep n := by
  intro Γ D B hΓ hF
  obtain ⟨⟨hΓ'⟩, ⟨hbody⟩⟩ := covWIrrel_family_eta_body hΓ hF
  exact ⟨⟨hΓ', hbody⟩⟩

/-- Every observation of a well-typed application of this family is one
of its two exact compacts. There is no semantic typing restriction on c. -/
theorem covWIrrel_family_applied_all_shape {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT covWIrrelEnv n Γ) {ρ : EnvWIrrel}
    {x : Expr Nat} {c : CptWIrrel}
    (ht : HasTyT covWIrrelEnv n Γ (.app covWIrrelFamily x) (.sort .zero))
    (h : ApproxTKWIrrel covWIrrelEnv n Γ ρ (.app covWIrrelFamily x) c) :
    c = .bot ∨ c = covWIrrelCoarse :=
  covWIrrel_family_applied_all_shape_of_native covWIrrelEnv_inScope
    (covWIrrel_family_eta_step n) hΓ ht h

/-- The supplied proof pair shares every decorated observation, including
all finite graph and eta alternatives, in each well-formed context. -/
theorem covWIrrel_family_all_observations_equal (n : Nat)
    (Γ : LCtx) (hΓ : CtxWfT covWIrrelEnv n Γ) (ρ : EnvWIrrel)
    (c : CptWIrrel) :
    ApproxTKWIrrel covWIrrelEnv n Γ ρ covWIrrelLeft c ↔
      ApproxTKWIrrel covWIrrelEnv n Γ ρ covWIrrelRight c :=
  covWIrrel_family_all_observations_equal_of_native n covWIrrelEnv_inScope
    (covWIrrel_family_eta_step n) Γ hΓ ρ c

/-- The same equality is stated at the public, recursively erased compact. -/
theorem covWIrrel_family_all_public_observations_equal (n : Nat)
    (Γ : LCtx) (hΓ : CtxWfT covWIrrelEnv n Γ) (ρ : EnvWIrrel)
    (c : CptT) :
    CovWIrrelObservation covWIrrelEnv n Γ ρ covWIrrelLeft c ↔
      CovWIrrelObservation covWIrrelEnv n Γ ρ covWIrrelRight c :=
  covWIrrel_family_all_public_observations_equal_of_native n covWIrrelEnv_inScope
    (covWIrrel_family_eta_step n) Γ hΓ ρ c

theorem covWIrrel_family_closed_observations_equal (n : Nat) (c : CptWIrrel) :
    ApproxTKWIrrel covWIrrelEnv n [] EnvWIrrel.bot covWIrrelLeft c ↔
      ApproxTKWIrrel covWIrrelEnv n [] EnvWIrrel.bot covWIrrelRight c :=
  covWIrrel_family_all_observations_equal n [] .nil EnvWIrrel.bot c

theorem covWIrrel_family_closed_public_observations_equal (n : Nat) (c : CptT) :
    CovWIrrelObservation covWIrrelEnv n [] EnvWIrrel.bot covWIrrelLeft c ↔
      CovWIrrelObservation covWIrrelEnv n [] EnvWIrrel.bot covWIrrelRight c :=
  covWIrrel_family_all_public_observations_equal n [] .nil EnvWIrrel.bot c

/-- Raw equality needs no native context because raw has no eta rule. -/
theorem covWIrrel_raw_family_all_observations_equal (n : Nat)
    (ρ : EnvWIrrel) (c : CptWIrrel) :
    ApproxTWIrrel covWIrrelEnv n ρ covWIrrelLeft c ↔
      ApproxTWIrrel covWIrrelEnv n ρ covWIrrelRight c := by
  have hcoarse (x : Expr Nat) :
      ApproxTWIrrel covWIrrelEnv n ρ (.app covWIrrelFamily x) covWIrrelCoarse :=
    covWIrrel_raw_appSpine_bot
      (.const ρ 5 [] covWIrrel_family_rigid covWIrrel_family_not_propCtor)
  constructor <;> intro h
  · rcases covWIrrel_raw_family_applied_shape h (.app .head) with rfl | rfl
    · exact .bot _ _
    · exact hcoarse covWIrrelQ
  · rcases covWIrrel_raw_family_applied_shape h (.app .head) with rfl | rfl
    · exact .bot _ _
    · exact hcoarse covWIrrelP

theorem covWIrrel_raw_family_all_public_observations_equal (n : Nat)
    (ρ : EnvWIrrel) (c : CptT) :
    CovWIrrelRawObservation covWIrrelEnv n ρ covWIrrelLeft c ↔
      CovWIrrelRawObservation covWIrrelEnv n ρ covWIrrelRight c := by
  constructor <;> rintro ⟨d, hd, h⟩
  · exact ⟨d, hd, (covWIrrel_raw_family_all_observations_equal n ρ d).mp h⟩
  · exact ⟨d, hd, (covWIrrel_raw_family_all_observations_equal n ρ d).mpr h⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FULL_PROOF_EQUALITY_ROOTS
#print axioms CovWIrrelFamilyResult
#print axioms CovWIrrelFamilyShape
#print axioms CovWIrrelFamilySource
#print axioms covWIrrel_raw_family_applied_shape
#print axioms CovWIrrelFamilyEtaStep
#print axioms covWIrrel_family_shape_of_native
#print axioms covWIrrel_family_applied_all_shape_of_native
#print axioms covWIrrel_family_all_observations_equal_of_native
#print axioms covWIrrel_family_all_public_observations_equal_of_native
#print axioms covWIrrel_family_eta_step
#print axioms covWIrrel_family_applied_all_shape
#print axioms covWIrrel_family_all_observations_equal
#print axioms covWIrrel_family_all_public_observations_equal
#print axioms covWIrrel_family_closed_observations_equal
#print axioms covWIrrel_family_closed_public_observations_equal
#print axioms covWIrrel_raw_family_all_observations_equal
#print axioms covWIrrel_raw_family_all_public_observations_equal
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_FULL_PROOF_EQUALITY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
