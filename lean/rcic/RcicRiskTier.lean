import rcic.RcicCertKernel
import rcic.RcicTypedMachineAccept
import rcic.RcicF3Defs
import rcic.RcicInvertFamily
import rcic.RcicF3BoundDefs
import rcic.RcicF3DBoundDefs

/-!
# The additive kernel soundness tier (statement layer)

`KernelSoundnessTier := TierF1 ∧ TierF3`, beside `NativeRCICClosed`
(nothing in `RcicApex` is edited or referenced). A report predicate, not a
closure claim: it implies nothing about `NativeRCICClosed` in either direction.

* `TierF1`: acceptance by the Lean machine carries a derivation (infer, check,
  check-run, cert whnf, cert conv, cert tyConv). No `EnvWfT`/`InScope`/
  `ScopeCheck` premise in any of the six.
* `TierF3 B`: height-4 consistency of the empty family, a hypothesis
  `FamAppConvInjAll` (a defined proposition) and `Premises4` as data.

`TierF2` (emitter correspondence) is not defined here: its binding of emitted
modules to Lean definitions is not stated on main. Package:
`docs/rcic/TIER_QUORUM_PACKAGE.md`. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Apex

open Rcic.Declarative Rcic.Machine Rcic.F3

/-- F1. Six acceptance-soundness statements (the landed `Type`-valued
statements, truncated by `Nonempty`). -/
def TierF1 : Prop :=
  Nonempty (type_of% @RM015T_infer_sound) ∧ Nonempty (type_of% @RM016T_check_sound) ∧
  Nonempty (type_of% @RM016T_run_check_sound) ∧
  Nonempty (type_of% @RM014T'_whnf_conv) ∧ Nonempty (type_of% @RM017T'_conv) ∧
  Nonempty (type_of% @RM017T'_tyConv)

/-- The family-application injectivity condition, defined from
`RcicInvertFamily.FamAppConvInj` at every well-formed environment. This is the
unrestricted form (an upper bound on the class-B1 condition: restricting it to
B1 families needs a landed B1 predicate, which does not exist yet). -/
def FamAppConvInjAll : Prop :=
  ∀ (E : ResolvedEnv) (n : Nat), EnvWfT E → Nonempty (FamAppConvInj E n)

/-- F3 at height 4, under `FamAppConvInjAll` and `Premises4`, with the environment bounds
`BoundG K hW` and `BoundDG K hW` as antecedents (the weakest set the class D theorem needs). `ClassG` is deliberately not an antecedent: class coverage is the
proof obligation, not part of the claim. -/
def TierF3 : Prop :=
  FamAppConvInjAll → PSet.Premises4 → ∀ (K : Nat → Nat) (E : ResolvedEnv) (hW : EnvWfT E),
    PSet.BoundG K hW → PSet.BoundDG K hW → PSet.AxiomFreeEnv' E → E.members 0 = some falseFamMember →
    E.members 1 = some falseRecMemberU →
    ∀ (n : Nat) (e : Expr Nat) (D : HasTyT E n [] e (.const 0 [])), PSet.LevelsBelow 4 K D → False

/-- The Lean machine is sound and the height-4 theory is consistent, relative
to `FamAppConvInjAll` and `Premises4`. -/
def KernelSoundnessTier : Prop := TierF1 ∧ TierF3

theorem tierF1 : TierF1 :=
  ⟨⟨@RM015T_infer_sound⟩, ⟨@RM016T_check_sound⟩, ⟨@RM016T_run_check_sound⟩,
   ⟨@RM014T'_whnf_conv⟩, ⟨@RM017T'_conv⟩, ⟨@RM017T'_tyConv⟩⟩

theorem tierF3_of_consistentEmpty (h : PSet.RcicConsistentEmpty) : TierF3 :=
  fun _ _ _ E hW _ _ hA h0 h1 n e D _ => h E hW hA h0 h1 n e D

/-- F1 is closed; the tier reduces to F3. -/
theorem kernelSoundnessTier_of_consistentEmpty (h : PSet.RcicConsistentEmpty) :
    KernelSoundnessTier :=
  ⟨tierF1, tierF3_of_consistentEmpty h⟩

end Rcic.Apex
