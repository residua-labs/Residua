/-
RCIC machine accept table (00 §20.13, segment 12, Annex 22 UNIT A4).

LEAF: one import `rcic.RcicMachine`. Namespace and `open` mirror
`RcicMachine.lean`. Diamond-free. Seal delta +10 (eleven-name
`syntaxEqual`-mismatch alternative declined; F4 default).
`soundness_claim` stays 0 — this is the Lean, not the flip.
-/
import rcic.RcicMachine

namespace Rcic.Machine
open Rcic.Declarative

/-- 00 §19.8 S-1 (ii), the tier-1 sentence as a cell table: what an
    ACCEPTED payload carries, arm by arm. Derivation cells delegate
    to the sealed RM rows; `PUnit` cells are the three payloads
    that carry no derivation: `levelEqual`-confirmed, refuted by
    `RM011_landed_not_eqN` (the arm accepts `param 0` against
    `param 1` under one dummy valuation); `convAt`-mismatch,
    refuted by `RM017_mismatch_is_not_nonconvertibility` (a
    mismatch is not nonconvertibility); and `syntaxEqual`-mismatch,
    which has NO refutation sealed at its own task — the same
    reading is refuted one task over, and the arm's ④ record is
    the SHAPE statement `RM_syntaxEqual_whole_ast`.
    `PEmpty` cells are (task, payload) pairs no
    arm of `kernelStepRaw` returns (`convType` never accepts,
    `RM017_convType_never_accepted`; `levelEqual` REFUSES on
    inequality). NOT a new soundness fact: this section's
    O-4 framing. -/
def AcceptedPayloadSound (amb : Ambient) :
    RawTask → AcceptedPayload → Type
  | .infer e, .inferredType T =>
      HasTy amb.env amb.univs amb.ctx e T
  | .check e A, .checked =>
      HasTy amb.env amb.univs amb.ctx e A
  | .whnfAt A e, .inferredWhnf A' w =>
      (A' = A) ×' MachineRed amb.env amb.univs amb.ctx e w
               ×' (machineWhnfDone amb.env w = true)
  | .convAt _ l r, .conversionConfirmed =>
      Conv amb.env amb.univs amb.ctx l r
  | .convAt _ _ _, .conversionMismatch => PUnit
  | .lookupLocal i, .inferredType A =>
      HasTy amb.env amb.univs amb.ctx (.bvar i) A
  | .lookupDeclaration r ls, .inferredType T =>
      HasTy amb.env amb.univs amb.ctx (.const r ls) T
  | .syntaxEqual a b, .conversionConfirmed =>
      Conv amb.env amb.univs amb.ctx a b
  | .syntaxEqual _ _, .conversionMismatch => PUnit
  | .levelEqual _ _, .conversionConfirmed => PUnit
  | _, _ => PEmpty

/-- THE TIER-1 STATEMENT (00 §19.8 S-1 (ii)), premise-free: every
    acceptance `kernelStepRaw` returns inhabits its cell. -/
def kernelStepRaw_accepted_sound (s : RawState) (p : AcceptedPayload)
    (hacc : kernelStepRaw s = .result (.accepted p)) :
    AcceptedPayloadSound s.ambient s.task p := by
  obtain ⟨amb, t, b⟩ := s
  cases b with
  | zero =>
    simp only [kernelStepRaw] at hacc
    injection hacc with h
    exact RunResult.noConfusion h
  | succ b' =>
    cases t with
    | infer e =>
      cases p with
      | inferredType T =>
        exact RM015_infer_sound ⟨amb, .infer e, b' + 1⟩ e T rfl hacc
      | _ =>
        simp only [kernelStepRaw] at hacc
        (try split at hacc) <;> (try split at hacc) <;>
          (injection hacc with h) <;>
            first
            | exact RunResult.noConfusion h
            | exact nomatch h
            | (injection h with h2; first | exact AcceptedPayload.noConfusion h2 | exact nomatch h2)
    | check e A =>
      cases p with
      | checked =>
        exact RM016_check_sound ⟨amb, .check e A, b' + 1⟩ e A rfl hacc
      | _ =>
        simp only [kernelStepRaw] at hacc
        (try split at hacc) <;> (try split at hacc) <;>
          (injection hacc with h) <;>
            first
            | exact RunResult.noConfusion h
            | exact nomatch h
            | (injection h with h2; first | exact AcceptedPayload.noConfusion h2 | exact nomatch h2)
    | whnfAt A e =>
      cases p with
      | inferredWhnf A' w =>
        have hEcho : A' = A := by
          simp only [kernelStepRaw] at hacc
          split at hacc
          · injection hacc with h
            injection h with h
            injection h with hEq _
            exact hEq.symm
          · injection hacc with h
            exact RunResult.noConfusion h
        subst hEcho
        exact ⟨rfl,
          RM014_whnf_reduces ⟨amb, .whnfAt A' e, b' + 1⟩ A' e w rfl hacc,
          RM014_whnf_head_normal ⟨amb, .whnfAt A' e, b' + 1⟩ A' e w rfl hacc⟩
      | _ =>
        simp only [kernelStepRaw] at hacc
        (try split at hacc) <;> (try split at hacc) <;>
          (injection hacc with h) <;>
            first
            | exact RunResult.noConfusion h
            | exact nomatch h
            | (injection h with h2; first | exact AcceptedPayload.noConfusion h2 | exact nomatch h2)
    | convType _ _ =>
      cases p <;>
        (simp only [kernelStepRaw] at hacc
         (try split at hacc) <;> (try split at hacc) <;>
           (injection hacc with h) <;>
             first
             | exact RunResult.noConfusion h
             | exact nomatch h
             | (injection h with h2; first | exact AcceptedPayload.noConfusion h2 | exact nomatch h2))
    | convAt A l r =>
      cases p with
      | conversionConfirmed =>
        exact RM017_conversion_confirmed ⟨amb, .convAt A l r, b' + 1⟩ A l r rfl hacc
      | conversionMismatch => exact PUnit.unit
      | _ =>
        simp only [kernelStepRaw] at hacc
        (try split at hacc) <;> (try split at hacc) <;>
          (injection hacc with h) <;>
            first
            | exact RunResult.noConfusion h
            | exact nomatch h
            | (injection h with h2; first | exact AcceptedPayload.noConfusion h2 | exact nomatch h2)
    | syntaxEqual a b =>
      cases p with
      | conversionConfirmed =>
        simp only [kernelStepRaw] at hacc
        split at hacc
        · subst_vars
          exact Conv.refl amb.ctx _
        · injection hacc with h
          injection h with h
          exact AcceptedPayload.noConfusion h
      | conversionMismatch => exact PUnit.unit
      | _ =>
        simp only [kernelStepRaw] at hacc
        (try split at hacc) <;> (try split at hacc) <;>
          (injection hacc with h) <;>
            first
            | exact RunResult.noConfusion h
            | exact nomatch h
            | (injection h with h2; first | exact AcceptedPayload.noConfusion h2 | exact nomatch h2)
    | levelEqual _ _ =>
      cases p with
      | conversionConfirmed => exact PUnit.unit
      | _ =>
        simp only [kernelStepRaw] at hacc
        (try split at hacc) <;> (try split at hacc) <;>
          (injection hacc with h) <;>
            first
            | exact RunResult.noConfusion h
            | exact nomatch h
            | (injection h with h2; first | exact AcceptedPayload.noConfusion h2 | exact nomatch h2)
    | lookupLocal i =>
      cases p with
      | inferredType A =>
        exact RM012_lookupLocal_hasTy ⟨amb, .lookupLocal i, b' + 1⟩ i A rfl hacc
      | _ =>
        simp only [kernelStepRaw] at hacc
        (try split at hacc) <;> (try split at hacc) <;>
          (injection hacc with h) <;>
            first
            | exact RunResult.noConfusion h
            | exact nomatch h
            | (injection h with h2; first | exact AcceptedPayload.noConfusion h2 | exact nomatch h2)
    | lookupDeclaration r ls =>
      cases p with
      | inferredType T =>
        exact RM013_lookupDeclaration_hasTy ⟨amb, .lookupDeclaration r ls, b' + 1⟩ r ls T rfl hacc
      | _ =>
        simp only [kernelStepRaw] at hacc
        (try split at hacc) <;> (try split at hacc) <;>
          (injection hacc with h) <;>
            first
            | exact RunResult.noConfusion h
            | exact nomatch h
            | (injection h with h2; first | exact AcceptedPayload.noConfusion h2 | exact nomatch h2)

/-- Run level, in the shape of `RM016_run_check_sound`: `runRaw`'s
    `.step` case is refuted by `kernelStepRaw_never_step`. -/
def runRaw_accepted_sound (k : Nat) (s : RawState) (p : AcceptedPayload)
    (hacc : runRaw (k + 1) s = .accepted p) :
    AcceptedPayloadSound s.ambient s.task p := by
  simp only [runRaw] at hacc
  cases hkr : kernelStepRaw s with
  | step s' => exact absurd hkr (kernelStepRaw_never_step s s')
  | result res =>
    rw [hkr] at hacc
    exact kernelStepRaw_accepted_sound s p
      (hkr.trans (congrArg StepOutcome.result hacc))

/-! M-005 witnesses (00 §21.4 (c); sealed; kernel reduction only).
    Budget 8 throughout (F8): no witness reaches `convCert`'s fuel-0
    arm. -/

theorem accept_witness_check (amb : Ambient) :
    kernelStepRaw ⟨amb, .check (.sort .zero) (.sort (.succ .zero)), 8⟩
      = .result (.accepted .checked) := rfl

theorem accept_witness_infer (amb : Ambient) :
    kernelStepRaw ⟨amb, .infer (.sort .zero), 8⟩
      = .result (.accepted (.inferredType (.sort (.succ .zero)))) := rfl

theorem accept_witness_whnf (amb : Ambient) :
    kernelStepRaw ⟨amb, .whnfAt (.sort (.succ .zero))
        (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero)), 8⟩
      = .result (.accepted
          (.inferredWhnf (.sort (.succ .zero)) (.sort .zero))) := rfl

theorem accept_witness_conv (amb : Ambient) :
    kernelStepRaw ⟨amb, .convAt (.sort (.succ .zero))
        (.sort .zero) (.sort .zero), 8⟩
      = .result (.accepted .conversionConfirmed) := rfl

theorem accept_witness_syntaxEqual (amb : Ambient) :
    kernelStepRaw ⟨amb, .syntaxEqual (.sort .zero) (.sort .zero), 8⟩
      = .result (.accepted .conversionConfirmed) := rfl

theorem accept_witness_lookupLocal (E : ResolvedEnv) (n : Nat) :
    kernelStepRaw ⟨⟨E, n, [.assumption (.sort .zero)]⟩, .lookupLocal 0, 8⟩
      = .result (.accepted (.inferredType (.sort .zero))) := rfl

theorem accept_witness_lookupDeclaration (n : Nat) (Γ : LCtx) :
    kernelStepRaw ⟨⟨extendEnv emptyEnv 0
        ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩, n, Γ⟩,
      .lookupDeclaration 0 [], 8⟩
      = .result (.accepted (.inferredType (.sort (.succ .zero)))) := rfl

end Rcic.Machine
