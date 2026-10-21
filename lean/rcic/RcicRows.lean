/-
Annex 23 unit H-4 — the RM-020 / RM-021 row propositions, sealed.

`00` §19.7 E-RM020Judge measured conjunct (a) of §21.4 against the
tree: sixteen sealed names, all closed literal instances, and NO sealed
statement states either row's proposition over the landed types. This
file is the closer: the two propositions, quoted from `03` §15 and
stated over the LANDED decoder and validator (`RcicWireDecode.lean`,
`RcicReach.lean`, `RcicStateWf.lean` — CALLED, not reimplemented,
23.H.0 (5)), quantified over the inputs, never at literals.

STATEMENTS QUOTED BEFORE THE LEAN (23.H.0 (3)):

  03 §15 :386 — "RM-020 raw wire decode does not mint well-formed
  state". 03 §9 :246-250 carries the content: "decodeWireState :
  Bytes → Result RawKernelState StateDecodeIntegrity" and "Wire
  decode validates canonical tags, payload shapes, typed references,
  integer bounds, frame tag syntax, and exact re-encoding. It does
  **not** mint `KernelState`."

  03 §15 :387 — "RM-021 reachable-state validation sound". 03 §9
  :253-258 carries the signature "validateReachableState :
  ExactKernelRequest → RawKernelState → ReachabilityEvidence →
  Result KernelState IntegrityResidue" and :267 the resumption
  sentence: "A raw state with `return accepted` and an empty
  continuation cannot be resumed unless it is reachable from the exact
  request under the exact profiles and environment."

WHAT THE ROWS SAY OVER THE LANDED TYPES, and nothing more. RM-020: the
no-mint content is the BOUNDARY between what decode's acceptance
settles and what E-W's `stateWellFormed` settles — decode refuses
unknown tasks and unknown frame tags but passes a chain whose io kinds
MISMATCH (`| _ => .ok` in `decodeParts`), so a decode acceptance is
worth exactly "well-formed, or refused by `stateWellFormed` as a
mismatch"; the second disjunct is inhabited (`witness_rm020_mismatch_
refused`, the literals the sealed `decode_mismatch_is_raw` /
`decode_mismatch_not_wf` already pin), which is the bite — the row is
not "decode accepts only well-formed". RM-021: the soundness
direction — whenever the validator mints a `KernelState`, the minted
value is the very state it was handed (no state transformation hides
in the mint) and that state really is well-formed (`inhabit?`
re-checks `stateWellFormed`); the refusal guards are visible in
`validateCore` and witnessed by the sealed `witness_*` refusals, and
the row asserts NOTHING about refused inputs (`witness_rm021_refusal_
control` is the vacuity control).

THE FOUR `03` §9 TYPES are not transcribed: `03` §9 names them in two
signatures and gives structure for none (the one content sentence —
"Permitted reachability evidence: exact prefix replay / AIR transition
receipt" — is transcribed by E-R's `reachEvidenceOk` as kinds 0/1).
The landed substitutes are recorded as bracketed deviation lines in
`00` §19.3's A3 cell, appended by this patch (E-RM020Judge (b)'s type
clause; the two Codex P1s it lists are answered by that record and in
the PR body, not by silence).

M-005: per row, one non-trivial instance and one refusal instance,
each at literals a Pins row already transcribes (`pin_wd_row00`,
`decode_mismatch_*`; `pin_rs_row00`, `pin_rs_row04`). The instances
pin COMPUTED equations (hypothesis inhabited, conclusion landing), not
Or-side choices — `Or` is a Prop and proof irrelevance makes any
disjunct-choice pin vacuous.

Premises: none of the open §19.2 rows. closure_claim stays 0.
-/
import rcic.RcicReach

namespace Rcic.Rows
open Rcic.StateWf
open Rcic.WireDecode
open Rcic.Reach

/-- H-4 helper (unsealed; flattening equation): `stateWellFormed 0
(mk task frames)` read as a function of the chain status alone. The
`if form != 0` arm is gone at form 0 and the projections reduce, so
this is `rfl`. -/
theorem stateWellFormed_mk (task : Nat) (frames : List Nat) :
    stateWellFormed 0 (mk task frames) =
      match frameChainOk (taskIo (taskTag (taskOfTag task))) frames with
      | .mismatch => some StateWf.residueMismatch
      | .unknownFrame => some StateWf.residueUnknownFrame
      | .ok _ =>
        if (taskIo (taskTag (taskOfTag task))).isNone then
          some StateWf.residueUnknownTask
        else none := rfl

/-- 03 §15 :386, quantified over the decoder's inputs and the decoded
state at the landed bytes entry. See the file header for the quoted
text and the boundary reading. -/
theorem RM020_decode_not_mint_wf (form : Nat) (bytes : String)
    (st : RawKernelState) (h : decodeWireState form bytes = .ok st) :
    stateWellFormed 0 st = none ∨
      stateWellFormed 0 st = some StateWf.residueMismatch := by
  unfold decodeWireState decodeParts at h
  dsimp only at h
  split at h
  · exact DecodeResult.noConfusion h
  · split at h
    · exact DecodeResult.noConfusion h
    · split at h
      · exact DecodeResult.noConfusion h
      · split at h
        · exact DecodeResult.noConfusion h
        · rename_i tkn htask
          split at h
          · rename_i hrt
            split at h
            · exact DecodeResult.noConfusion h
            · rename_i hchain
              injection h with hst
              subst hst
              rw [stateWellFormed_mk, hrt, htask]
              split
              · exact Or.inr rfl
              · rename_i hgo
                exact absurd hgo hchain
              · exact Or.inl rfl
          · exact DecodeResult.noConfusion h

/-- 03 §15 :387, quantified over the validator's inputs and the
minted `KernelState` at the landed bytes entry. See the file header
for the quoted text and the soundness reading. -/
theorem RM021_validation_sound (form : Nat) (request : String)
    (st : RawKernelState) (evKind : Nat) (evBytes : String)
    (ks : KernelState)
    (h : validateReachableState form request st evKind evBytes
          = .ok ks) :
    ks.val = st ∧ stateWellFormed 0 st = none := by
  have hgen : ∀ k : KernelState, inhabit? st = some k →
      k.val = st ∧ stateWellFormed 0 st = none := by
    intro k hk
    unfold inhabit? at hk
    split at hk
    · rename_i hwf
      cases hk
      exact ⟨rfl, hwf⟩
    · exact Option.noConfusion hk
  unfold validateReachableState validateCore at h
  split at h
  · exact ReachResult.noConfusion h
  · split at h
    · exact ReachResult.noConfusion h
    · split at h
      · exact ReachResult.noConfusion h
      · split at h
        · -- req refused
          exact ReachResult.noConfusion h
        · -- req = .ok dst
          split at h
          · exact ReachResult.noConfusion h
          · split at h
            · -- evKind == 0: replay evidence
              split at h
              · -- ev refused
                exact ReachResult.noConfusion h
              · -- ev = .ok edst
                split at h
                · exact ReachResult.noConfusion h
                · split at h
                  · exact ReachResult.noConfusion h
                  · injection h with hks
                    subst hks
                    exact hgen _ (by assumption)
            · -- evKind != 0: receipt evidence
              split at h
              · exact ReachResult.noConfusion h
              · split at h
                · exact ReachResult.noConfusion h
                · injection h with hks
                  subst hks
                  exact hgen _ (by assumption)

/-! ### M-005 instances -/

/-- M-005 non-trivial instance of `RM020_decode_not_mint_wf` (LEFT
disjunct): the corpus row `pin_wd_row00` ("accept: t:2|f:1",
`RcicWireDecodePins.lean`) inhabits the row's hypothesis and the
conclusion lands in the first disjunct. Pinned at `decodeParts`, the
reducible core the theorems reduce to; the byte split is pinned by the
Pins' `#eval`, not kernel-reducible. -/
theorem witness_rm020_accept_wf :
    decodeParts 0 [['t', ':', '2'], ['f', ':', '1']]
        = .ok (mk 2 [1]) ∧
      stateWellFormed 0 (mk 2 [1]) = none := ⟨rfl, rfl⟩

/-- M-005 refusal instance of `RM020_decode_not_mint_wf` (RIGHT
disjunct): the mismatch chain the sealed `decode_mismatch_is_raw` /
`decode_mismatch_not_wf` pin at the same literals — decode ACCEPTS
and E-W REFUSES. The row's second disjunct is inhabited, so the row
is not "decode accepts only well-formed". -/
theorem witness_rm020_mismatch_refused :
    decodeParts 0 [['t', ':', '2'], ['f', ':', '8'], ['f', ':', '1']]
        = .ok (mk 2 [8, 1]) ∧
      stateWellFormed 0 (mk 2 [8, 1]) = some StateWf.residueMismatch :=
  ⟨rfl, rfl⟩

/-- M-005 non-trivial instance of `RM021_validation_sound`: the
corpus row `pin_rs_row00` ("replay-evidence ACCEPT: request t:8,
replay bytes t:8", `RcicReachPins.lean`) inhabits the row's hypothesis
at the core the theorems reduce to, and the minted `KernelState` is
genuine — same state, well-formed. -/
theorem witness_rm021_accept_genuine :
    validateCore 0 (mk 8 []) 0 (.ok (mk 8 [])) (.ok (mk 8 [])) 3
        = .ok ⟨mk 8 [], task8_empty_wf⟩ ∧
      (⟨mk 8 [], task8_empty_wf⟩ : KernelState).val = mk 8 [] ∧
      stateWellFormed 0 (mk 8 []) = none :=
  ⟨rfl, rfl, rfl⟩

/-- M-005 refusal instance of `RM021_validation_sound` (vacuity
control): the corpus row `pin_rs_row04` ("non-resumable refusal:
frames nonempty") — the validator REFUSES, so the row's hypothesis is
FALSE here and the row asserts nothing about refused inputs. Same
literals as the sealed `witness_not_resumable`; this name is the
row's own control. -/
theorem witness_rm021_refusal_control :
    ∀ ks : KernelState,
      validateCore 0 (mk 2 [1]) 1 (.ok (mk 8 [])) (.ok (mk 8 [])) 4
        ≠ .ok ks := by
  intro ks h
  have hr : validateCore 0 (mk 2 [1]) 1 (.ok (mk 8 []))
          (.ok (mk 8 [])) 4 = .refuse residueNotResumable := rfl
  rw [hr] at h
  exact ReachResult.noConfusion h

end Rcic.Rows
