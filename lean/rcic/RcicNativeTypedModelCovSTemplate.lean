import rcic.RcicNativeTypedModelCovSCandidate

/-!
# Finite templates of the information actually present in CptT

The decoder recurses only into the domain and output type compacts of a Pi.
Demand compacts and rigid arguments are retained without recursive calls.
It neither reads a native type nor computes a native readback.

The source carrier has no bound-variable constructor and erases nonzero
universe levels. These losses are explicit: `var` is available to an
origin-carrying extension but is never fabricated by this decoder;
`allSort` records an erased nonzero level; `unknownPi` records an unobserved
domain. The separate Origin module refutes reconstructing the missing data
from raw compacts, with actual native/model premises. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovSAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open TypedModelAudit TypedModelAudit.TypingFin

inductive CovSObsSyntax where
  | unknown
  | prop
  | sort
  | rigid (head : Nat) (args : List CptT)
  | var (index : Nat)
  | ordinary (domain : CovSObsSyntax)
      (rows : List (List CptT × CovSObsSyntax))
  | allProp (rows : List (List CptT × CovSObsSyntax))
  | allSort (rows : List (List CptT × CovSObsSyntax))
  | unknownPi (rows : List (List CptT × CovSObsSyntax))
  | unsupportedLambda (rows : List (List CptT × CptT))

theorem covS_pi_domain_size_lt (a : CptT) (rows : List (List CptT × CptT)) :
    sizeOf a < sizeOf (CptT.pi a rows) := by
  simp only [CptT.pi.sizeOf_spec]
  omega

theorem covS_pi_output_size_lt (a : CptT) (rows : List (List CptT × CptT))
    (row : List CptT × CptT) (hrow : row ∈ rows) :
    sizeOf row.2 < sizeOf (CptT.pi a rows) := by
  have h₁ := List.sizeOf_lt_of_mem hrow
  have h₂ := sizeOfT_snd_lt row
  simp only [CptT.pi.sizeOf_spec]
  omega

/-- A total computable decoder of observed shape, with missing provenance
represented explicitly. No recursive call takes a value/application result. -/
def templateOfObs (a : CptT) : CovSObsSyntax :=
  match a with
  | .bot => .unknown
  | .prop => .prop
  | .sort => .sort
  | .spine r us => .rigid r us
  | .lam rows => .unsupportedLambda rows
  | .pi d rows =>
      let outputs := rows.attach.map fun row =>
        (row.val.1, templateOfObs row.val.2)
      match hd : d with
      | .bot => .unknownPi outputs
      | .prop => .allProp outputs
      | .sort => .allSort outputs
      | _ => .ordinary (templateOfObs d) outputs
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  · have h₁ := List.sizeOf_lt_of_mem row.property
    have h₂ := sizeOfT_snd_lt row.val
    omega
  · subst_vars
    omega

theorem templateOfObs_bot : templateOfObs .bot = .unknown := by
  rw [templateOfObs]

theorem templateOfObs_prop : templateOfObs .prop = .prop := by
  rw [templateOfObs]

theorem templateOfObs_sort : templateOfObs .sort = .sort := by
  rw [templateOfObs]

theorem templateOfObs_spine (r : Nat) (us : List CptT) :
    templateOfObs (.spine r us) = .rigid r us := by
  rw [templateOfObs]

theorem templateOfObs_lam (rows : List (List CptT × CptT)) :
    templateOfObs (.lam rows) = .unsupportedLambda rows := by
  rw [templateOfObs]

theorem templateOfObs_empty_pi :
    templateOfObs (.pi .bot []) = .unknownPi [] := by
  rw [templateOfObs]
  rfl

theorem templateOfObs_ne_var (a : CptT) (i : Nat) :
    templateOfObs a ≠ .var i := by
  cases a with
  | bot => rw [templateOfObs]; exact CovSObsSyntax.noConfusion
  | prop => rw [templateOfObs]; exact CovSObsSyntax.noConfusion
  | sort => rw [templateOfObs]; exact CovSObsSyntax.noConfusion
  | spine r us => rw [templateOfObs]; exact CovSObsSyntax.noConfusion
  | lam rows => rw [templateOfObs]; exact CovSObsSyntax.noConfusion
  | pi a rows =>
      cases a <;> rw [templateOfObs] <;> (intro h; cases h)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_S_TEMPLATE_ROOTS
#print axioms CovSObsSyntax
#print axioms covS_pi_domain_size_lt
#print axioms covS_pi_output_size_lt
#print axioms templateOfObs
#print axioms templateOfObs_bot
#print axioms templateOfObs_prop
#print axioms templateOfObs_sort
#print axioms templateOfObs_spine
#print axioms templateOfObs_lam
#print axioms templateOfObs_empty_pi
#print axioms templateOfObs_ne_var
-- END RCIC_NATIVE_TYPED_MODEL_COV_S_TEMPLATE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovSAudit
