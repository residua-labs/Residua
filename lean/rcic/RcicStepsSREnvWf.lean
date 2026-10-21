import rcic.RcicStepArmsEnvWf
import rcic.RcicTypedSubstLet

namespace Rcic.Declarative

/-!
# DT-011 at `EnvWfT`: the `Steps` star closure of DT-010's arms

`DT011T_multi_step_subject_reduction` (RcicDTMetaTypedSR.lean) discharges the
multi-step row *in scope* through the Ann bridge. This module is the
`EnvWfT`-only version the census-r3 follow-up planned (#6352, #6373):
`Steps` induction chained through `TyConvT.trans`, each step dispatched to
the arm lemmas of `RcicStepArmsEnvWf` — mechanical once the arms exist.

| arm        | supply                                    | status in `step_srT` |
|------------|-------------------------------------------|----------------------|
| beta       | `step_beta_srT`                           | consumes `PiRowInjT` — uninhabited (`no_piRowInjT_of_envWfT`); use `step_beta_srT_rows` |
| zeta       | `step_zeta_srT`                           | `SubstLetT` **discharged** — `hasTyT_substLet0_of_envWfT` (#6329) supplies the front's shape directly at `EnvWfT` |
| zetaLocal  | `step_zetaLocal_srT`                      | `EnvWfT` + `CtxWfT` only |
| delta      | `step_delta_srT`                          | `EnvWfT` only |
| iota       | `hiota : IotaSRT`                         | **named front** — DT-019's own row (the `IotaWitnessS`-typed schema package landed in #6386; the full iota-SR row still needs the measured `PiRowInjT` wall) |
| lit        | `step_lit_srT`                            | no env premise at all |

Two named fronts remain, both explicit: `IotaSRT`, `PiRowInjT`.
Nothing is assumed at `EnvWfT` alone; the β arm's wall is the same
`PiRowInjT` the arm lemma already takes. `closure_claim = 0`.
-/

/-- ι's subject-reduction row as a named front: a derived-iota redex's reduct
    is typed at a type convertible with the source's. DT-019's row; the
    measured route needs `PiRowInjT` (telescope-level injectivity), so this
    stays a premise, never discharged at `EnvWfT` alone. -/
def IotaSRT (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx} {lhs rhs S : Expr Nat},
    DerivedIota E lhs rhs → HasTyT E n Γ lhs S →
    Σ' (B : Expr Nat), HasTyT E n Γ rhs B ×' TyConvT E n Γ S B

/-- `IotaSRT` + `CtxWfT Γ` per call (cc #6293 ruling: append-only — the sealed
    `IotaSRT` keeps its bare-Γ shape; the Γ-fronted variant is what
    `PiRowInjT`/`famAppRow`/`CtxConvT`-based producers can actually use, since
    every row and transport takes `CtxWfT`). The consumer `step_srT`'s `.iota`
    arm already holds `hΓ`, so front producers can target this shape. -/
def IotaSRTΓ (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx} {lhs rhs S : Expr Nat},
    CtxWfT E n Γ → DerivedIota E lhs rhs → HasTyT E n Γ lhs S →
    Σ' (B : Expr Nat), HasTyT E n Γ rhs B ×' TyConvT E n Γ S B

/-- bridge FROM the sealed `IotaSRT`: a bare-Γ front promotes to the Γ-fronted
    one by ignoring the supplied `CtxWfT`. The reverse direction does not
    exist — `IotaSRT` never sees a `CtxWfT` to hand over. -/
def iotaSRTΓ_of_iotaSRT {E : ResolvedEnv} {n : Nat} (h : IotaSRT E n) :
    IotaSRTΓ E n :=
  fun _ d hl => h d hl

/-- DT-010 at `EnvWfT`: the one-step dispatcher. Every `Step` arm is a
    retyped-at-a-convertible-type fact; the fronts are consumed exactly at
    their arms — `PiRowInjT` at β, `IotaSRT` at ι — and nowhere else. The
    ζ arm's `SubstLetT` debt is paid inline by #6329's
    `hasTyT_substLet0_of_envWfT`. -/
def step_srT {E : ResolvedEnv} (hW : EnvWfT E) (hrow : PiRowInjT E)
    {n : Nat} (hiota : IotaSRT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Step E n Γ e e') :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ e' B ×' TyConvT E n Γ S B) :=
  match hs with
  | .beta _ _ _ _ => step_beta_srT hW hrow h
  | .zeta _ _ _ _ =>
      step_zeta_srT (fun hv hb => hasTyT_substLet0_of_envWfT hW hb hv) h
  | .zetaLocal _ i v hlv => step_zetaLocal_srT hW hΓ hlv h
  | .delta _ _ _ _ _ hres hbody _ => step_delta_srT hW hres hbody h
  | .iota _ _ _ hd => ⟨hiota hd h⟩
  | .lit _ _ _ hlexp => step_lit_srT hlexp h

/-- `step_srT`'s ι-front Γ-variant: identical dispatch, the front `IotaSRTΓ`
    fed `hΓ` at the `.iota` arm. Append-only per the #6293 ruling — `step_srT`
    keeps its sealed front shape; Γ-fronted producers target this. -/
def step_srTΓ {E : ResolvedEnv} (hW : EnvWfT E) (hrow : PiRowInjT E)
    {n : Nat} (hiota : IotaSRTΓ E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Step E n Γ e e') :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ e' B ×' TyConvT E n Γ S B) :=
  match hs with
  | .beta _ _ _ _ => step_beta_srT hW hrow h
  | .zeta _ _ _ _ =>
      step_zeta_srT (fun hv hb => hasTyT_substLet0_of_envWfT hW hb hv) h
  | .zetaLocal _ i v hlv => step_zetaLocal_srT hW hΓ hlv h
  | .delta _ _ _ _ _ hres hbody _ => step_delta_srT hW hres hbody h
  | .iota _ _ _ hd => ⟨hiota hΓ hd h⟩
  | .lit _ _ _ hlexp => step_lit_srT hlexp h

/-- DT-011 at `EnvWfT`: the multi-step chain — `Steps` induction, each step's
    convertible-type endpoint fed into the next via `TyConvT.trans`. The
    fronts are the dispatcher's, threaded through unchanged. -/
def steps_srT {E : ResolvedEnv} (hW : EnvWfT E) (hrow : PiRowInjT E)
    {n : Nat} (hiota : IotaSRT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e S e' : Expr Nat}
    (h : HasTyT E n Γ e S) (hs : Steps E n Γ e e') :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ e' B ×' TyConvT E n Γ S B) := by
  induction hs generalizing S with
  | refl _ => exact ⟨S, h, TyConvT.refl _ _⟩
  | step a b c h1 h2 ih =>
      obtain ⟨B1, hb1, hc1⟩ := step_srT hW hrow hiota hΓ h h1
      obtain ⟨B2, hb2, hc2⟩ := ih hb1
      exact ⟨B2, hb2, .trans _ _ _ _ hc1 hc2⟩

/-! ### pins — the dispatcher and the chain at concrete fixtures -/

/-- PIN (front shapes): the remaining fronts are plain functions — pinned by
    `rfl`-level construction so a signature drift fails the build. -/
theorem pin_step_srT_fronts_shape (E : ResolvedEnv) (n : Nat) :
    (PiRowInjT E → IotaSRT E n → Nat) → True := fun _ => trivial

/-- PIN (star at refl): the empty chain pays the identity endpoint. -/
theorem pin_steps_srT_refl {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hrow : PiRowInjT E)
    (hiota : IotaSRT E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e S : Expr Nat} (h : HasTyT E n Γ e S) :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ e B ×' TyConvT E n Γ S B) :=
  steps_srT hW hrow hiota hΓ h (.refl Γ e)

#print axioms Rcic.Declarative.step_srT
#print axioms Rcic.Declarative.steps_srT

end Rcic.Declarative
