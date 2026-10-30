import rcic.RcicF3TierGroup

/-!
# The production target for the PendA group step

`StepAG_PendA` is a transparent name for the landed `TierGroup.StepAG`.
This module specifies the target; it does not supply its proof.

In particular the domain is the whole typed group, with an existential
`PendA` node. There is no condition on raw field syntax, family numbers,
normal forms, the number of Pi binders, or a checker's acceptance.

The inputs of `GroupStepAt` remain walk agreement, both group bounds, and
the base `GInv`. The output is the existing `GInv`, hence uses the existing
`envCtx` family interpretation. Replacing that interpretation is a change
to the target, not an implementation of this abbreviation.

See `research/rcic/STEPAG_PENDA.md` for the measured inventory, the known
finite-stage obstruction, and the remaining construction.

`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.TierGroup

open Rcic.F3.PSet

/-- Named production obligation on all PendA groups. This is a statement
alias, deliberately definitionally equal to `StepAG`, with no producer. -/
abbrev StepAG_PendA (P : Premises4) (K : Nat → Nat) : Prop := StepAG P K

-- Statement-fidelity checks; these are definitional checks, not new results.
example (P : Premises4) (K : Nat → Nat) : StepAG_PendA P K = StepAG P K := rfl
example (P : Premises4) (K : Nat → Nat) (h : StepAG_PendA P K) : StepAG P K := h
example (P : Premises4) (K : Nat → Nat) (h : StepAG P K) : StepAG_PendA P K := h

end Rcic.F3.TierGroup
