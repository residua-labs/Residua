import rcic.RcicNativePiProbeComputation

/-!
# The native constant-level constructor at the two type probes

`EnvWfT` already makes every stored body level-free. Thus both level
instances of a constant with a body unfold to literally the same body.
A bare constant without a body has no sort/Pi observation, even with the
additional K rules. These facts discharge the entire `ConvT.consts` arm;
there is no new level-observation or model-soundness premise.

`closure_claim = 0`. Additive composition over landed declarations.
-/

namespace Rcic.Declarative.NativeValleys.PiProbeConstantsAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.PiProbeAlgebraAudit
open Rcic.Declarative.NativeValleys.PiProbeComputationAudit

variable {E : ResolvedEnv} {n : Nat}

/-- The extra K rules have no bare-constant source. -/
theorem whStepK_const_opaque_false {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hb : m.body = none) (ls : List Level)
    {N : Expr Nat} (hs : WhStepK E n Γ (.const r ls) N) : False := by
  apply whStepCtx_const_opaque_false hm hb ls
  apply whStepK_to_ctx_of_notConstApplication hs
  intro r' ls' pre x heq
  exact Expr.noConfusion heq

theorem normalR_const_opaque {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hb : m.body = none) (ls : List Level) :
    NormalR (WhStepK E n) Γ (.const r ls) :=
  fun _ hs => whStepK_const_opaque_false hm hb ls hs

theorem redR_const_opaque_eq {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hb : m.body = none) {ls : List Level}
    {N : Expr Nat} (hread : RedR (WhStepK E n) Γ (.const r ls) N) :
    N = .const r ls :=
  redR_of_normal (normalR_const_opaque hm hb ls) hread

/-- Both endpoints lack the two type heads; no typing or equality of the
level lists is needed for this particular branch. -/
theorem probeEquiv_consts_opaque {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hb : m.body = none) (ls ls' : List Level) :
    ProbeEquivT (WhStepK E n) E n Γ (.const r ls) (.const r ls') := by
  apply probeEquiv_of_no_probesT
  · intro u h
    exact Expr.noConfusion (redR_const_opaque_eq hm hb h)
  · intro A B h
    exact Expr.noConfusion (redR_const_opaque_eq hm hb h)
  · intro u h
    exact Expr.noConfusion (redR_const_opaque_eq hm hb h)
  · intro A B h
    exact Expr.noConfusion (redR_const_opaque_eq hm hb h)

/-- This is an existing environment invariant composed with the existing
level-instantiation equations, not an added assumption on stored bodies. -/
theorem instantiateLevels_stored_body (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} {body : Expr Nat} (hm : E.members r = some m)
    (hb : m.body = some body) (ls : List Level) :
    instantiateLevels ls body = body := by
  rw [instantiateLevels_take 0 ls body (envWfT_body_lvl0 hW r m body hm hb),
    List.take_zero, instantiateLevels_nil]

/-- Both delta paths have the same endpoint, so every specified normal
readback is preserved. This includes K steps later in the common body. -/
theorem redR_consts_body_iff (hW : EnvWfT E) {Γ : LCtx} {r : Nat}
    {m : CheckedMember} {body : Expr Nat} (hm : E.members r = some m)
    (hb : m.body = some body) (ls ls' : List Level) {X : Expr Nat}
    (hX : NormalR (WhStepK E n) Γ X) :
    RedR (WhStepK E n) Γ (.const r ls) X ↔
      RedR (WhStepK E n) Γ (.const r ls') X := by
  rw [redR_delta_iff hW hm hb hX, redR_delta_iff hW hm hb hX,
    instantiateLevels_stored_body hW hm hb ls,
    instantiateLevels_stored_body hW hm hb ls']

theorem probeEquiv_consts_body (hW : EnvWfT E) {Γ : LCtx} {r : Nat}
    {m : CheckedMember} {body : Expr Nat} (hm : E.members r = some m)
    (hb : m.body = some body) (ls ls' : List Level) :
    ProbeEquivT (WhStepK E n) E n Γ (.const r ls) (.const r ls') :=
  probeEquiv_of_readback_iffT (readbackLaws_whStepK E n)
    (fun _ hX => redR_consts_body_iff hW hm hb ls ls' hX)

/-- All admitted bare constants preserve these two observations between
level instances. The native `consts` side conditions are sufficient but
unnecessary for this restricted head-only observation. -/
theorem probeEquiv_consts (hW : EnvWfT E) {Γ : LCtx} {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) (ls ls' : List Level) :
    ProbeEquivT (WhStepK E n) E n Γ (.const r ls) (.const r ls') := by
  cases hb : m.body with
  | none => exact probeEquiv_consts_opaque hm hb ls ls'
  | some body => exact probeEquiv_consts_body hW hm hb ls ls'

theorem convProbe_consts (hW : EnvWfT E) {Γ : LCtx} {r : Nat}
    {ls ls' : List Level} {m : CheckedMember} (hm : E.members r = some m)
    (hlen : ls.length = m.arity) (hls : levelsBounded n ls = true)
    (hls' : levelsBounded n ls' = true) (heq : eqNList ls ls') :
    ConvProbeMotiveT (WhStepK E n) (.consts Γ r ls ls' m hm hlen hls hls' heq) :=
  probeEquiv_consts hW hm ls ls'

/-- A typed native constant-level instance whose sort observation is
actually present: the landed transparent `const 0 := Sort 0` pin. -/
def constsSortConversion :
    ConvT defSortEnv 0 [] (.const 0 []) (.const 0 []) (.sort (.succ .zero)) :=
  .consts [] 0 [] [] ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩
    rfl rfl rfl rfl (eqNList_refl [])

theorem constsSort_nonvacuity :
    Nonempty (EnvWfT defSortEnv) ∧
    Nonempty (HasTyT defSortEnv 0 [] (.const 0 []) (.sort (.succ .zero))) ∧
    RedR (WhStepK defSortEnv 0) [] (.const 0 []) (.sort .zero) ∧
    ConvProbeMotiveT (WhStepK defSortEnv 0) constsSortConversion := by
  refine ⟨⟨defSortEnvWfT⟩, ⟨.const [] 0 []
    ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ rfl rfl rfl⟩,
    .step (.ctx (.delta (m := ⟨.definitionM, 0, .sort (.succ .zero),
      some (.sort .zero)⟩) rfl rfl)) (.refl _), ?_⟩
  exact probeEquiv_consts defSortEnvWfT
    (r := 0) (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩)
    rfl [] []

-- BEGIN RCIC_PI_PROBE_CONSTANTS_ROOTS
#print axioms whStepK_const_opaque_false
#print axioms normalR_const_opaque
#print axioms redR_const_opaque_eq
#print axioms probeEquiv_consts_opaque
#print axioms instantiateLevels_stored_body
#print axioms redR_consts_body_iff
#print axioms probeEquiv_consts_body
#print axioms probeEquiv_consts
#print axioms convProbe_consts
#print axioms constsSortConversion
#print axioms constsSort_nonvacuity
-- END RCIC_PI_PROBE_CONSTANTS_ROOTS

end Rcic.Declarative.NativeValleys.PiProbeConstantsAudit
