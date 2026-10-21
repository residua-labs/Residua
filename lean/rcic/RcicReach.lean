/-
Annex 22 UNIT E-R — `03` §9 `validateReachableState`, quoted.
Pinned to `apps/rcic-reachability/` (`rcic_reachability`).
22.E.10 amendment 4: this unit lands `KernelState` (the type
`validateReachableState` returns). E-D does not.

TRANSCRIPTION TABLE (`03_REFERENCE_MACHINE.md` on this unit's base
`d35d660bb`, lines re-taken):
  03:253 validateReachableState : ExactKernelRequest →
        RawKernelState → ReachabilityEvidence →
        Result KernelState IntegrityResidue — `validateReachableState`
  03:263-264 exact prefix replay / AIR transition receipt
        — evidence kind ∈ {0, 1}
  03:267 empty continuation + return-accepted cannot resume
        without reachability from the exact request —
        `reachStateResumable` (task 8, empty frames) +
        request decode (C3, composed) + evidence adequacy
No clause of the §9 validator block is dropped. Decoder is composed
(`decodeWireState`), not copied.

closure_claim stays 0.
-/
import rcic.RcicWireDecode

namespace Rcic.Reach
open Rcic.StateWf
open Rcic.WireDecode

inductive ReachResult : Type
  | ok (ks : KernelState)
  | refuse (code : String)

def residueUnknownEvidence : String := "[rcic_reach_unknown_evidence]"
def residueNotResumable : String := "[rcic_reach_not_resumable]"
def residueWrongRequest : String := "[rcic_reach_wrong_request]"
def residueEvidenceMismatch : String := "[rcic_reach_evidence_mismatch]"
def residueUnknownForm : String := "[rcic_reach_unknown_form]"

/-- C4 `rcic.reach_evidence_ok`. -/
def reachEvidenceOk (k : Nat) : Bool := k == 0 || k == 1

/-- C4 `rcic.reach_state_resumable`: task 8, empty continuation.
H-8: the C1 tag is `taskTag` of the carried `RawTask`. -/
def reachStateResumable (st : RawKernelState) : Bool :=
  taskTag st.control.task == 8 && st.continuationFrames.isEmpty

def inhabit? (st : RawKernelState) : Option KernelState :=
  if h : stateWellFormed 0 st = none then some ⟨st, h⟩ else none

/-- Reducible core (theorems pin this). Request/evidence already decoded. -/
def validateCore (form : Nat) (st : RawKernelState) (evKind : Nat)
    (req : DecodeResult) (ev : DecodeResult) (evLen : Nat) : ReachResult :=
  if form != 0 then .refuse residueUnknownForm
  else if !reachEvidenceOk evKind then .refuse residueUnknownEvidence
  else if !reachStateResumable st then .refuse residueNotResumable
  else
    match req with
    | .refuse _ => .refuse residueWrongRequest
    | .ok dst =>
      if dst.control.task != st.control.task then .refuse residueWrongRequest
      else if evKind == 0 then
        match ev with
        | .refuse _ => .refuse residueEvidenceMismatch
        | .ok edst =>
          if edst.control.task != st.control.task then .refuse residueEvidenceMismatch
          else match inhabit? st with
            | none => .refuse residueNotResumable
            | some ks => .ok ks
      else
        if evLen == 0 then .refuse residueEvidenceMismatch
        else match inhabit? st with
          | none => .refuse residueNotResumable
          | some ks => .ok ks

/-- 03:253. Composes E-D's `decodeWireState` (not copied). -/
def validateReachableState (form : Nat) (request : String)
    (st : RawKernelState) (evKind : Nat) (evBytes : String) : ReachResult :=
  validateCore form st evKind
    (decodeWireState 0 request)
    (decodeWireState 0 evBytes)
    evBytes.length

/-! ### Sealed facts -/

theorem task8_empty_wf :
    stateWellFormed 0 (mk 8 []) = none := rfl

theorem witness_unknown_form :
    validateCore 1 (mk 8 []) 1 (.ok (mk 8 [])) (.ok (mk 8 [])) 4
      = .refuse residueUnknownForm := rfl

theorem witness_unknown_evidence :
    validateCore 0 (mk 8 []) 9 (.ok (mk 8 [])) (.ok (mk 8 [])) 0
      = .refuse residueUnknownEvidence := rfl

theorem witness_not_resumable :
    validateCore 0 (mk 2 [1]) 1 (.ok (mk 8 [])) (.ok (mk 8 [])) 4
      = .refuse residueNotResumable := rfl

theorem witness_wrong_request :
    validateCore 0 (mk 8 []) 1 (.ok (mk 2 [])) (.ok (mk 8 [])) 4
      = .refuse residueWrongRequest := rfl

theorem witness_replay_mismatch :
    validateCore 0 (mk 8 []) 0 (.ok (mk 8 [])) (.ok (mk 2 [])) 3
      = .refuse residueEvidenceMismatch := rfl

theorem witness_empty_receipt :
    validateCore 0 (mk 8 []) 1 (.ok (mk 8 [])) (.ok (mk 8 [])) 0
      = .refuse residueEvidenceMismatch := rfl

/-- KernelState is inhabited at the resumable shape (the mint E-D forbids). -/
theorem witness_replay_accept :
    inhabit? (mk 8 []) = some ⟨mk 8 [], task8_empty_wf⟩ := rfl

end Rcic.Reach
