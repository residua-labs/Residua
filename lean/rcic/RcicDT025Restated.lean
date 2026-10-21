/-

# `RcicDT025Restated` — the restated DT-025 as ONE census-facing theorem

Annex 26.18 (#6293, restatement accepted): DT-025 as originally stated —
"the declarative system is normalizing" plus a normalization-based A-6 Hop —
is **false as stated**; the true content is the package below.

* **Refutation 1 (legacy).** `Normalizing` is false at every well-formed
  environment (`NormalizingFalse.normalizing_false`) — the collapse fixture.

* **Refutation 2 (typed, Loop).** At `eraseEnv pinLoopEnvA`, the cyclic
  conversion `X ≡ X → X : sort 0` (`convT_pinLoop`) types the Abel–Coquand ω
  `Ω_X = (λx:X. x x)(λx:X. x x)` (`omegaT_pinLoop_typed`), and every
  `ParRedStar` reduct of `Ω_X` keeps a `ParRed` step
  (`NormalizingFalsePinLoop.normalizingT_false_pinLoop`) — the `OmXT`
  invariant. So no `ParRedStar` reduct of `Ω_X` is `ParRed`-normal.

* **The positive residue.** `hopFacesA_of_envWf` — the A-6 Hop faces
  (`HopFacesA`, the `δ`-face supply plugged into `hstuck_of_faces`' `hdelta`
  slot) on its exact true cone: the `AnnEnvA` environments, conditional on
  the two remaining named premises `PropStuckChainsA` (the `.prop`-stuck
  nodes — the propElim boundary, false at Loop and therefore a premise on
  its own true cone, not a theorem) and `PiHeadStepTypedA` (typed head
  steps at a `Type`-level `Π`; its `major` arm is discharged, the named
  `kunit`/`kstruct` residual is the W-ATR-3 irr/η equation).

* **Checker soundness without normalization.** `RM016T_check_sound` /
  `RM016T_run_check_sound` — the typed machine's acceptance carries the
  derivation in its payload, read off into `HasTyT`. The checker is
  fuel-bounded and *refuses* on exhaustion; soundness never invokes
  normalization, only the payload derivation. The `HasTyT` conclusions are
  `Type`-valued, so the Prop-level shadow of each row wraps them in
  `Nonempty`.

No `sorry`. `closure_claim` stays 0.
-/

import rcic.RcicNormalizingFalse
import rcic.RcicNormalizingFalsePinLoop
import rcic.RcicAnnLRChainG
import rcic.RcicTypedMachineAccept

namespace Rcic

open Declarative Declarative.Ann Machine

/-- **DT-025, restated** (Annex 26.18): the conjunction a census anchors
    to — false as originally stated; the two refutations, Hop on its exact
    cone, and checker soundness without normalization. -/
theorem DT025_restated :
    (∀ {E : ResolvedEnv} {n : Nat}, EnvWf E n → Normalizing E n → False)
    ∧ (∀ {n : Nat},
        Nonempty (HasTyT (eraseEnv pinLoopEnvA) n loopΓ omegaXT loopXT)
        ∧ ∀ {N : Expr Nat},
            ParRedStar (eraseEnv pinLoopEnvA) n loopΓ omegaXT N →
              Nonempty (Σ' M : Expr Nat,
                ParRed (eraseEnv pinLoopEnvA) n loopΓ N M))
    ∧ (∀ {E : ResolvedEnvA} {n : Nat}, AnnEnvA E →
        PropStuckChainsA E (iotaIfaceA E) n →
        PiHeadStepTypedA E (iotaIfaceA E) n →
        HopFacesA E (iotaIfaceA E) n)
    ∧ (∀ (s : TypedState) (e A : Expr Nat)
        (_htask : s.task = .checkT2 A e)
        (_hacc : Σ' d, typedStep s = .accepted (.checked e A d)),
        Nonempty (HasTyT s.ambient.env s.ambient.univs s.ambient.ctx e A))
    ∧ (∀ (k : Nat) (s : TypedState) (e A : Expr Nat)
        (_htask : s.task = .checkT2 A e)
        (_hacc : Σ' d, typedRun (k + 1) s = .accepted (.checked e A d)),
        Nonempty (HasTyT s.ambient.env s.ambient.univs s.ambient.ctx e A)) :=
  ⟨fun hE => NormalizingFalse.normalizing_false hE,
   fun {_} => ⟨⟨omegaT_pinLoop_typed⟩,
     fun h => NormalizingFalsePinLoop.normalizingT_false_pinLoop h⟩,
   fun C => hopFacesA_of_envWf C,
   fun _ _ _ ht hd => ⟨RM016T_check_sound _ _ _ ht hd⟩,
   fun _ _ _ _ ht hd => ⟨RM016T_run_check_sound _ _ _ _ ht hd⟩⟩

end Rcic

#print axioms Rcic.DT025_restated
