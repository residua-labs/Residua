import rcic.RcicTypedConv
import rcic.ScmSrcGroupsAdm
import rcic.ScmSrcGroupsKernelRfl

/-!
# The conversion checker's ι arm, pinned on the K3c corpus at slot 159

`RcicTypedConv`'s conversion has, beyond the three arms of `RcicTypedConvArmPins`, one shared
selector (`iotaBetaStep?`) whose two steppers only turn a refusal into a derivation when the
syntactic `headStep?` cannot produce the step:

* ARM (4), IOTA (`iotaStepWith?`, the shared selector's first arm): a
  recursor-on-constructor redex on either compared side. `iotaReductCert` (the legacy
  recognizer — post-#6196 `ConvT.iota` carries `DerivedIota`) finds the `IotaWitness`;
  `ConvT.iota` emits the step with a real `DerivedIota` (`DerivedIota.of w`); both sides are
  typed by `checkWith` at `conv`, and the step is placed at the redex's own inferred type —
  `tyConv?`'s middle (`iotaMid?`) then moves it to the sort `toSort?` reads off that type, and
  `convAt?` moves it to the asked-for type `T`.
* The conversion-aware β stepper (`betaStepWith?`, the shared selector's second arm, with
  `liftSpineWith`): `headStep?`'s β case where the λ's domain, body, or spine arguments only
  CONVERT to their expected types — `checkT`/`synCheck` refuse them as written, so `whnfTy` leaves
  a λ-headed application unstepped. The same helpers type their parts with `checkWith`/`tyAtWith`
  at `conv`.
* `piCongr?`'s domain read and `domChain`'s codomain read likewise go through `checkWith` + `toSort?`
  rather than `checkT`, so a domain or codomain that only converts to a sort still yields the
  `ConvT.pi` step.

THE MEASURED CASE (`srcNthB*`): `srcEnvG`'s slot 159, `mNthBNilVa`, the three-argument `recNthB`
theorem over byte lists. Its body is three λs over a seven-argument `recNthB` application
(`srcNthBCore`). The check the K3c `EnvWfT` entry needs — `HasTyT (envPre 159) 0 []` of the body at
the stated `mtype` — is what the earlier checker refused at every fuel: on the way in, the checker's
argument comparisons meet `recBL`'s motive applied to `blCons x t`, a λ-headed application whose
β-reduct is another λ-headed application, four steps deep, that then exposes the `recBL (blCons x t)`
ι-redex itself — and that ι-reduct is again a minor-case λ application needing three more
conversion-aware β steps (its recursive-call argument does not `synCheck` at the minor's domain; it
only converts). The `HasTyT` derivation itself is closed below by hand (`srcNthBTyT`, :the manual
assembly), and `srcNthB_conv_admits` pins the closing `tyConv?` the compiled `tyAtC` needs.

KERNEL-SHAPE HONESTY. The whole-body `tyAtC` evaluation exceeds the kernel's whnf recursion bound
(`(kernel) deep recursion detected`), so the admission is pinned at the units that DO fit, and the
`HasTyT` derivation is assembled from the kernel-checked pieces by the `HasTyT` constructors
themselves — as far as the bound allows:

* `srcNthB_head_admits` — `const recNthB` at its seven-Π signature, fuel 96;
* `srcNthB_arg0/1_admits`, `srcNthB_arg3..6_admits` — six of the seven spine arguments, each `tyAtC`
  at its instantiated domain;
* `srcNthB_arg2_checks` — argument 2 checks, fuel 96 (`checkC`'s `Σ T, HasTyT` is extracted);
* `srcNthB_dom0/1/2_ty` — the three λ-domains at their sorts;
* `srcNthBA_admits` — the `mtype` itself at `Sort 0`, the other half of the `EnvWfT` entry;
* `srcNthB_conv_admits` — the closing conversion `tyAtC` performs last: the body's inferred Π
  (`srcNthBPi`, the three λ-domains over `instPrefix args cod`) against the stored `mtype`;
* `srcNthB_refuses` — CONTROL: that same inferred Π against `Sort 0` is refused, so the admission
  is the conversion's doing, not a collapse of the checker.

THE RESIDUAL, CLOSED. Argument 2 is the only argument whose INFERRED type (`inferC arg2`, a six-Π
motive-application type, pinned literally as `T2lit` by `srcNthBT2eq`) is not literally its
instantiated domain `srcNthBDom 2` — the innermost codomain differs and `tyAtC arg2 dom2`
requires `tyConv?` on the pair, which walks six `piCongr` levels into the `recBL (blCons x t)`
ι/β chain. That `tyConv?` EVALUATION still exceeds the kernel whnf bound at every granularity
probed — the whole conv, each π half, the innermost leaf pair (`tyConv?`/`appConvWith`/
`iotaStepWith?`/`betaStepWith?`), and inside `tyAtC arg2`/`checkC (preApp3)` — so
`HasTyT arg2 dom2` cannot be extracted by running the search. It is instead built by hand at the
declarative level in the manual-assembly segment below: `srcNthBcB` chains the seven-step
conversion (four `ConvT.beta`/`.app` lifts to the `recBL` redex, `srcNthBcIota`, three more
βs) at `ctxL 6`; `srcNthBcT2` carries it under the six shared Π binders to `srcNthBDom 2`;
`srcNthBDarg2dom` transports `srcNthBDarg2S.2` along it; `srcNthBP3…srcNthBP6` finish the
`recNthB` spine, `srcNthBCoreTy` types the core, the three `.lam`s rebuild the body at
`srcNthBPi`, and `srcNthBTyT` closes the entry through `srcNthBClose`. The residual was a
kernel recursion bound on EXTRACTING the conversion derivation, never a checker refusal —
and `srcNthBTyT` discharges it.

The assembled derivations: `srcNthBDhead`, `srcNthBDarg*` are the checker's answers at the pinned
units; `srcNthBP1`/`srcNthBP2` are the first two `.app` steps of the spine assembly;
`srcNthBATyT` is the `mtype : Sort 0` half of the entry; `srcNthBClose` is the pinned closing
conversion as a `TyConvT` derivation.
-/

namespace Rcic.Declarative
open Rcic.Scm.SrcG
set_option maxRecDepth 1000000

/-- the slot-159 theorem body: `mNthBNilVa`'s stored body, three λs over the `recNthB` spine. -/
def srcNthBBody : Expr Nat := mNthBNilVa.body.getD (.sort .zero)

/-- strip `k` leading λs of a term: their domains (outermost first) and the remaining body. -/
def srcNthBStrip : Nat → Expr Nat → List (Expr Nat) × Expr Nat
  | 0, e => ([], e)
  | k + 1, .lam A b => let (ds, c) := srcNthBStrip k b; (A :: ds, c)
  | _ + 1, e => ([], e)

/-- a context of assumptions for a list of domains, newest binder first. -/
def srcNthBΓOf (ds : List (Expr Nat)) : LCtx := ds.reverse.map LocalDecl.assumption

/-- the three λ-domains of the slot-159 body (outermost first). -/
def srcNthBLamDoms : List (Expr Nat) := (srcNthBStrip 3 srcNthBBody).1

/-- the body's core: the seven-argument `recNthB` application under the three λs. -/
def srcNthBCore : Expr Nat := (srcNthBStrip 3 srcNthBBody).2

/-- the context under the three λs (newest first). -/
def srcNthBΓ : LCtx := srcNthBΓOf srcNthBLamDoms

/-- the context under the first `k` λs. -/
def srcNthBΓk (k : Nat) : LCtx := srcNthBΓOf (srcNthBLamDoms.take k)

/-- the application spine's arguments: the seven `recNthB` arguments in order. -/
def srcNthBArgs : List (Expr Nat) := (appsSpine srcNthBCore).2

/-- the application spine's head: `const recNthB`. -/
def srcNthBHead : Expr Nat := (appsSpine srcNthBCore).1

/-- `head` applied to the first `k` spine arguments. -/
def srcNthBPre (k : Nat) : Expr Nat := foldApps srcNthBHead (srcNthBArgs.take k)

/-- the `recNthB` signature's seven Π-domains (outermost first). -/
def srcNthBRDoms : List (Expr Nat) := ((peelPis 7 recNthB.mtype).map Prod.fst).getD []

/-- the `recNthB` signature's codomain after the seven Πs. -/
def srcNthBCod : Expr Nat := ((peelPis 7 recNthB.mtype).map Prod.snd).getD (.sort .zero)

/-- the `i`-th domain instantiated by the first `i` arguments. -/
def srcNthBDom (i : Nat) : Expr Nat :=
  instPrefix (srcNthBArgs.take i) (srcNthBRDoms.getD i (.sort .zero))

/-- the `i`-th spine argument. -/
def srcNthBArg (i : Nat) : Expr Nat := srcNthBArgs.getD i (.sort .zero)

/-- the codomain instantiated by all seven arguments — the core's type, witnessed by the
    manual derivation `srcNthBCoreTy` (`HasTyT … srcNthBCore srcNthBTCod`) below. -/
def srcNthBTCod : Expr Nat := instPrefix srcNthBArgs srcNthBCod

/-- the type the checker infers for `srcNthBPre k`: the first `k` arguments instantiated into the
    remaining Π tail — pinned at `k = 0` (`srcNthBDhead`), `k = 1` (`srcNthBP1`), `k = 2`
    (`srcNthBP2`), and `k = 7` (`srcNthBCoreTy` at `srcNthBTCod`). -/
def srcNthBTy (k : Nat) : Expr Nat :=
  instPrefix (srcNthBArgs.take k) (List.foldr Expr.pi srcNthBCod (srcNthBRDoms.drop k))

/-- the body's inferred type: the three λ-domains over `srcNthBTCod` — the type `tyAtC`'s closing
    `conv` compares against `mNthBNilVa.mtype`. -/
def srcNthBPi : Expr Nat :=
  .pi (srcNthBLamDoms.getD 0 (.sort .zero))
    (.pi (srcNthBLamDoms.getD 1 (.sort .zero))
      (.pi (srcNthBLamDoms.getD 2 (.sort .zero)) srcNthBTCod))

/-- the three λ-domains, named. -/
def srcNthBD0 : Expr Nat := srcNthBLamDoms.getD 0 (.sort .zero)
def srcNthBD1 : Expr Nat := srcNthBLamDoms.getD 1 (.sort .zero)
def srcNthBD2 : Expr Nat := srcNthBLamDoms.getD 2 (.sort .zero)

-- The kernel-evaluated pins and the manual `HasTyT` assembly below re-run the checker —
-- `tyAtC`/`checkC`/`tyConv?`/`iotaReductCert` on slot-159 terms at fuel 96 — at kernel
-- check time (and the `by`-proofs at elaboration): the declarations whose evaluation needs
-- the lifted bound. The prelude above (plain `Expr Nat`/`List` helpers) stays at default.
section
set_option maxHeartbeats 64000000

-- KERNEL PIN 1: the spine head `const recNthB` at its seven-Π signature, fuel 96.
kernel_rfl_theorem srcNthB_head_admits :
    (tyAtC (envPre 159) 0 96 srcNthBΓ srcNthBHead (srcNthBTy 0)).isSome = true

-- KERNEL PIN 2–3: the first two spine arguments check at their instantiated domains, fuel 96.
kernel_rfl_theorem srcNthB_arg0_admits :
    (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 0) (srcNthBDom 0)).isSome = true

kernel_rfl_theorem srcNthB_arg1_admits :
    (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 1) (srcNthBDom 1)).isSome = true

-- KERNEL PIN 4: argument 2 CHECKS, fuel 96 — `checkC`'s `Σ T, HasTyT` is extracted below. Its
-- inferred type is not literally `srcNthBDom 2` — the domain conversion is the kernel-bound
-- residual documented in the header, so it is pinned here as `checkC`, not `tyAtC`.
kernel_rfl_theorem srcNthB_arg2_checks :
    (checkC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 2)).isSome = true

-- KERNEL PIN 5–8: each remaining spine argument checks at its instantiated domain, fuel 96.
kernel_rfl_theorem srcNthB_arg3_admits :
    (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 3) (srcNthBDom 3)).isSome = true

kernel_rfl_theorem srcNthB_arg4_admits :
    (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 4) (srcNthBDom 4)).isSome = true

kernel_rfl_theorem srcNthB_arg5_admits :
    (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 5) (srcNthBDom 5)).isSome = true

kernel_rfl_theorem srcNthB_arg6_admits :
    (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 6) (srcNthBDom 6)).isSome = true

-- KERNEL PIN 6–8: the three λ-domains are types at their sorts — the outer two at `Sort 1` (they
--    are Π domains over the index structure), the innermost at `Sort 0`. 
kernel_rfl_theorem srcNthB_dom0_ty :
    (tyAtC (envPre 159) 0 96 (srcNthBΓk 0) srcNthBD0 (.sort (.succ .zero))).isSome = true

kernel_rfl_theorem srcNthB_dom1_ty :
    (tyAtC (envPre 159) 0 96 (srcNthBΓk 1) srcNthBD1 (.sort (.succ .zero))).isSome = true

kernel_rfl_theorem srcNthB_dom2_ty :
    (tyAtC (envPre 159) 0 96 (srcNthBΓk 2) srcNthBD2 (.sort .zero)).isSome = true

-- KERNEL PIN 9: the other half of the `EnvWfT` entry — the stated `mtype` is itself a `Sort 0`
--    type in `envPre 159` at `n = 0`, fuel 96. 
kernel_rfl_theorem srcNthBA_admits :
    (tyAtC (envPre 159) 0 96 ([] : LCtx) mNthBNilVa.mtype (.sort .zero)).isSome = true

-- KERNEL PIN 10: the closing conversion — the body's inferred Π converts to the stored `mtype`,
--    fuel 96. This is the `conv` `tyAtC` performs after `checkWith` infers `srcNthBPi`. 
kernel_rfl_theorem srcNthB_conv_admits :
    (tyConv? (envPre 159) 0 96 ([] : LCtx) srcNthBPi mNthBNilVa.mtype).isSome = true

-- KERNEL PIN 11, CONTROL: the body's inferred Π does NOT convert to `Sort 0` — a Π type against a
--    proposition sort is refused at fuel 96, so the slot-159 admission is the conversion path's
--    doing, not a collapse of the checker. 
kernel_rfl_theorem srcNthB_refuses :
    (tyConv? (envPre 159) 0 96 ([] : LCtx) srcNthBPi (.sort .zero)).isSome = false

/-- the checker's answers at the pinned head and arguments. -/
def srcNthBDhead : HasTyT (envPre 159) 0 srcNthBΓ srcNthBHead (srcNthBTy 0) :=
  (tyAtC (envPre 159) 0 96 srcNthBΓ srcNthBHead (srcNthBTy 0)).get srcNthB_head_admits

def srcNthBDarg0 : HasTyT (envPre 159) 0 srcNthBΓ (srcNthBArg 0) (srcNthBDom 0) :=
  (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 0) (srcNthBDom 0)).get srcNthB_arg0_admits

def srcNthBDarg1 : HasTyT (envPre 159) 0 srcNthBΓ (srcNthBArg 1) (srcNthBDom 1) :=
  (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 1) (srcNthBDom 1)).get srcNthB_arg1_admits

/-- argument 2's typing, at the checker's OWN inferred type (`Σ T, HasTyT` — its inferred type is
    not literally `srcNthBDom 2`; the domain conversion is the kernel-bound residual in the
    header). -/
def srcNthBDarg2S : Σ T, HasTyT (envPre 159) 0 srcNthBΓ (srcNthBArg 2) T :=
  (checkC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 2)).get srcNthB_arg2_checks

/-- the spine assembly, as far as the kernel bound allows: the typing rule's own `.app` steps —
    each `.app`'s expected domain is the checker-inferred Π's domain, and each argument's
    derivation is a pinned `tyAtC` answer. `srcNthBP2` types `const recNthB · arg0 · arg1` at the
    `instantiate0`-computed type; the next `.app` needs `HasTyT arg2 dom2`, which requires the
    domain conversion (the residual). -/
def srcNthBP1 : Σ T, HasTyT (envPre 159) 0 srcNthBΓ (srcNthBPre 1) T :=
  ⟨_, .app _ _ _ _ _ srcNthBDhead srcNthBDarg0⟩

def srcNthBP2 : Σ T, HasTyT (envPre 159) 0 srcNthBΓ (srcNthBPre 2) T :=
  ⟨_, .app _ _ _ _ _ srcNthBP1.2 srcNthBDarg1⟩

/-- the checker's answers at the pinned arguments. -/
def srcNthBDarg3 : HasTyT (envPre 159) 0 srcNthBΓ (srcNthBArg 3) (srcNthBDom 3) :=
  (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 3) (srcNthBDom 3)).get srcNthB_arg3_admits

def srcNthBDarg4 : HasTyT (envPre 159) 0 srcNthBΓ (srcNthBArg 4) (srcNthBDom 4) :=
  (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 4) (srcNthBDom 4)).get srcNthB_arg4_admits

def srcNthBDarg5 : HasTyT (envPre 159) 0 srcNthBΓ (srcNthBArg 5) (srcNthBDom 5) :=
  (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 5) (srcNthBDom 5)).get srcNthB_arg5_admits

def srcNthBDarg6 : HasTyT (envPre 159) 0 srcNthBΓ (srcNthBArg 6) (srcNthBDom 6) :=
  (tyAtC (envPre 159) 0 96 srcNthBΓ (srcNthBArg 6) (srcNthBDom 6)).get srcNthB_arg6_admits

/-- the checker's answers at the pinned λ-domains. -/
def srcNthBDomTy0 : HasTyT (envPre 159) 0 (srcNthBΓk 0) srcNthBD0 (.sort (.succ .zero)) :=
  (tyAtC (envPre 159) 0 96 (srcNthBΓk 0) srcNthBD0 (.sort (.succ .zero))).get srcNthB_dom0_ty

def srcNthBDomTy1 : HasTyT (envPre 159) 0 (srcNthBΓk 1) srcNthBD1 (.sort (.succ .zero)) :=
  (tyAtC (envPre 159) 0 96 (srcNthBΓk 1) srcNthBD1 (.sort (.succ .zero))).get srcNthB_dom1_ty

def srcNthBDomTy2 : HasTyT (envPre 159) 0 (srcNthBΓk 2) srcNthBD2 (.sort .zero) :=
  (tyAtC (envPre 159) 0 96 (srcNthBΓk 2) srcNthBD2 (.sort .zero)).get srcNthB_dom2_ty

/-- the pinned closing conversion, as a `TyConvT` derivation. -/
def srcNthBClose : TyConvT (envPre 159) 0 ([] : LCtx) srcNthBPi mNthBNilVa.mtype :=
  (tyConv? (envPre 159) 0 96 ([] : LCtx) srcNthBPi mNthBNilVa.mtype).get srcNthB_conv_admits

/-- the other half of the entry: the stated `mtype` is a `Sort 0` type. -/
def srcNthBATyT : HasTyT (envPre 159) 0 [] mNthBNilVa.mtype (.sort .zero) :=
  (tyAtC (envPre 159) 0 96 ([] : LCtx) mNthBNilVa.mtype (.sort .zero)).get srcNthBA_admits



/-! ## the manual `HasTyT` assembly for slot 159

`checkC`'s `Σ T, HasTyT` for argument 2 is kernel-infeasible to transport to `srcNthBDom 2`
directly (the inferred type's codomain hides the `recBL (blCons x t)` redex behind four
motive-lambda βs). This segment builds that conversion BY HAND at the declarative level:

* `srcNthBT2eq` pins the checker's extracted inferred type to a literal six-Π tower.
* `srcNthBcIota` is the typed ι step `DerivedIota.of wREX.1 + ConvT.iota` for
  `recBL motive mn mc (blCons x t) ~ mc x t (recBL · t)`, the witness extracted from the
  `iotaReductCert` certificate pin `srcNthBCertREX`.
* `srcNthBcB` chains four `ConvT.beta`/`ConvT.app` steps (the motive-lambda spine unfolding
  `arg0`'s application to the `recBL` redex), the ι step, and three more βs (the minor
  constructor's application) down to `T2`'s codomain `leafL`.
* `srcNthBcT2` is the six-`ConvT.pi` tower carrying that codomain conversion under the six
  shared binders, giving `ConvT T2lit (srcNthBDom 2)`; `srcNthBDarg2dom` transports
  `srcNthBDarg2S.2` along it.
* the seven `.app` steps `srcNthBP3…srcNthBCoreTy` finish the `recNthB` spine, the three
  `.lam`s rebuild the body at `srcNthBPi`, and `srcNthBTyT` closes through `srcNthBClose`.

No checker code is touched; every step is a `ConvT`/`HasTyT` term.
-/

-- ===== generic const typings (context-parameterized) =====

/-- Sort 0. -/
def S0e : Expr Nat := .sort .zero
/-- Sort 1. -/
def S1e : Expr Nat := .sort (.succ .zero)

def tyC4 (Γ : LCtx) : HasTyT (envPre 159) 0 Γ (.const 4 []) S1e :=
  .const Γ 4 [] mBytes rfl rfl rfl

def tyC34 (Γ : LCtx) : HasTyT (envPre 159) 0 Γ (.const 34 []) S1e :=
  .const Γ 34 [] mBL rfl rfl rfl

def tyC0 (Γ : LCtx) : HasTyT (envPre 159) 0 Γ (.const 0 []) S1e :=
  .const Γ 0 [] mN rfl rfl rfl

def tyS0 (Γ : LCtx) : HasTyT (envPre 159) 0 Γ S0e S1e :=
  .sort Γ .zero

def tyBlNil (Γ : LCtx) : HasTyT (envPre 159) 0 Γ (.const 35 []) (.const 34 []) :=
  .const Γ 35 [] mBlNil rfl rfl rfl

def tySucc (Γ : LCtx) : HasTyT (envPre 159) 0 Γ (.const 2 []) (.pi (.const 0 []) (.const 0 [])) :=
  .const Γ 2 [] mSucc rfl rfl rfl

def tyBlCons (Γ : LCtx) :
    HasTyT (envPre 159) 0 Γ (.const 36 []) (.pi (.const 4 []) (.pi (.const 34 []) (.const 34 []))) :=
  .const Γ 36 [] mBlCons rfl rfl rfl

def tyNthB (Γ : LCtx) :
    HasTyT (envPre 159) 0 Γ (.const 88 [])
      (.pi (.const 34 []) (.pi (.const 0 []) (.pi (.const 4 []) S0e))) :=
  .const Γ 88 [] mNthB rfl rfl rfl

def tyValueAt (Γ : LCtx) :
    HasTyT (envPre 159) 0 Γ (.const 133 []) (.pi (.const 106 []) (.pi (.const 4 []) S0e)) :=
  .const Γ 133 [] mValueAt rfl rfl rfl

def tyMkBound (Γ : LCtx) :
    HasTyT (envPre 159) 0 Γ (.const 107 [])
      (.pi (.const 8 []) (.pi (.const 4 [])
        (.pi (.app (.app (.const 96 []) (.bvar 1)) (.bvar 0)) (.const 106 [])))) :=
  .const Γ 107 [] mMkBound rfl rfl rfl

def tyBoolRef (Γ : LCtx) : HasTyT (envPre 159) 0 Γ (.const 110 []) (.const 8 []) :=
  .const Γ 110 [] mBoolRef rfl rfl rfl

def tyBytesB (Γ : LCtx) : HasTyT (envPre 159) 0 Γ (.const 12 []) (.const 4 []) :=
  .const Γ 12 [] mBytesB rfl rfl rfl

def tyCctBoolPf (Γ : LCtx) :
    HasTyT (envPre 159) 0 Γ (.const 114 [])
      (.app (.app (.const 96 []) (.const 110 [])) (.const 12 [])) :=
  .const Γ 114 [] mCctBoolPf rfl rfl rfl

def tyResrcNthBcBL (Γ : LCtx) :
    HasTyT (envPre 159) 0 Γ (.const 37 [.succ .zero])
      (instantiateLevels [.succ .zero] recBL.mtype) :=
  .const Γ 37 [.succ .zero] recBL rfl rfl rfl

-- ===== application builders =====

/-- `blCons x t : BL` from typed parts. -/
def blConsApp (Γ : LCtx) {x t : Expr Nat}
    (hx : HasTyT (envPre 159) 0 Γ x (.const 4 []))
    (ht : HasTyT (envPre 159) 0 Γ t (.const 34 [])) :
    HasTyT (envPre 159) 0 Γ (.app (.app (.const 36 []) x) t) (.const 34 []) :=
  .app Γ _ _ _ _ (.app Γ _ _ _ _ (tyBlCons Γ) hx) ht

/-- `succ n : N`. -/
def succApp (Γ : LCtx) {n : Expr Nat}
    (hn : HasTyT (envPre 159) 0 Γ n (.const 0 [])) :
    HasTyT (envPre 159) 0 Γ (.app (.const 2 []) n) (.const 0 []) :=
  .app Γ _ _ _ _ (tySucc Γ) hn

/-- `NthB l n bs : Prop` (well, `Sort 0`). -/
def nthBApp (Γ : LCtx) {l n bs : Expr Nat}
    (hl : HasTyT (envPre 159) 0 Γ l (.const 34 []))
    (hn : HasTyT (envPre 159) 0 Γ n (.const 0 []))
    (hbs : HasTyT (envPre 159) 0 Γ bs (.const 4 [])) :
    HasTyT (envPre 159) 0 Γ (.app (.app (.app (.const 88 []) l) n) bs) S0e :=
  .app Γ _ _ _ _ (.app Γ _ _ _ _ (.app Γ _ _ _ _ (tyNthB Γ) hl) hn) hbs

-- ===== recBL motive / minors =====

/-- the closed BL→Prop motive: `λ C34. S0`. -/
def motive159 : Expr Nat := .lam (.const 34 []) S0e

def tyMotive159 (Γ : LCtx) :
    HasTyT (envPre 159) 0 Γ motive159 (.pi (.const 34 []) S1e) :=
  .lam Γ _ _ _ _ (tyC34 Γ) (tyS0 _)

/-- the `C107 C110 C12 C114` bound: at `C106`. -/
def bound159 : Expr Nat :=
  .app (.app (.app (.const 107 []) (.const 110 [])) (.const 12 [])) (.const 114 [])

def tyBound159 (Γ : LCtx) : HasTyT (envPre 159) 0 Γ bound159 (.const 106 []) :=
  .app Γ _ _ _ _
    (.app Γ _ _ _ _
      (.app Γ _ _ _ _ (tyMkBound Γ) (tyBoolRef Γ))
      (tyBytesB Γ))
    (tyCctBoolPf Γ)

/-- `valueAt bound bs : Prop`. -/
def valueAtApp (Γ : LCtx) {bs : Expr Nat}
    (hbs : HasTyT (envPre 159) 0 Γ bs (.const 4 [])) :
    HasTyT (envPre 159) 0 Γ (.app (.app (.const 133 []) bound159) bs) S0e :=
  .app Γ _ _ _ _ (.app Γ _ _ _ _ (tyValueAt Γ) (tyBound159 Γ)) hbs

-- ===== the minor-domain conversions =====

/-- the minor-nil expected domain: `motive159 · blNil`. -/
def domMn159 : Expr Nat := .app motive159 (.const 35 [])

/-- conversion `S0 ~ (λC34.S0)·C35` at `S1` — one β, symmetric direction. -/
def mnConv159 (Γ : LCtx) : ConvT (envPre 159) 0 Γ S0e domMn159 S1e :=
  .symm Γ _ _ _ (.beta Γ (.const 34 []) S0e (.const 35 []) S1e (.succ .zero)
    (tyC34 Γ) (tyS0 _) (tyBlNil Γ))

/-- the cons-minor's stored lam type. -/
def mcLamTy159 : Expr Nat :=
  .pi (.const 4 []) (.pi (.const 34 []) (.pi S0e S0e))

/-- the cons-minor's expected domain in the `recBL` spine:
    `Π x t. Π (ih : motive·t). motive·(blCons x t)`. -/
def domMc159 : Expr Nat :=
  .pi (.const 4 []) (.pi (.const 34 [])
    (.pi (.app motive159 (.bvar 0)) (.app motive159 (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))))

/-- `imax`-of-sorts tag for a three-level conversion tower of `Sort 1` leafs. -/
def lv111 : Level := .imax (.succ .zero) (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))

/-- `ΠC4.ΠC34.ΠS0.S0 ~ domMc159` at `Sort 1`: a π tower whose two leafs are
    β-expanded motive applications (the `ih` domain and the codomain). -/
def mcConv159 (Γ : LCtx) :
    ConvT (envPre 159) 0 Γ mcLamTy159 domMc159 (.sort lv111) := by
  refine ConvT.pi Γ (.const 4 []) (.const 4 [])
      (.pi (.const 34 []) (.pi S0e S0e))
      (.pi (.const 34 []) (.pi (.app motive159 (.bvar 0))
        (.app motive159 (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))))
      (.succ .zero) (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))
      (ConvT.refl _ _ _ (tyC4 Γ)) ?_
  refine ConvT.pi _ (.const 34 []) (.const 34 [])
      (.pi S0e S0e)
      (.pi (.app motive159 (.bvar 0)) (.app motive159 (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1))))
      (.succ .zero) (.imax (.succ .zero) (.succ .zero))
      (ConvT.refl _ _ _ (tyC34 _)) ?_
  refine ConvT.pi _ S0e (.app motive159 (.bvar 0)) S0e
      (.app motive159 (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
      (.succ .zero) (.succ .zero) ?_ ?_
  · exact ConvT.symm _ _ _ _
      (.beta _ (.const 34 []) S0e (.bvar 0) S1e (.succ .zero)
        (tyC34 _) (tyS0 _) (.bvar _ 0 _ rfl))
  · exact ConvT.symm _ _ _ _
      (.beta _ (.const 34 []) S0e (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)) S1e (.succ .zero)
        (tyC34 _) (tyS0 _)
        (blConsApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl)))

-- ===== the recBL spine typing, parameterized =====

/-- `recBL motive159 mn mc major`. -/
def recBLAppOf (major mn mc : Expr Nat) : Expr Nat :=
  .app (.app (.app (.app (.const 37 [.succ .zero]) motive159) mn) mc) major

/-- `recBL motive159 mn mc major : S0` from the three typed pieces. -/
def recBLSpineTy (Γ : LCtx) (major mn mc : Expr Nat)
    (hmajor : HasTyT (envPre 159) 0 Γ major (.const 34 []))
    (hmn : HasTyT (envPre 159) 0 Γ mn S0e)
    (hmc : HasTyT (envPre 159) 0 Γ mc mcLamTy159) :
    HasTyT (envPre 159) 0 Γ (recBLAppOf major mn mc) S0e := by
  have h1 := HasTyT.app Γ _ _ _ _ (tyResrcNthBcBL Γ) (tyMotive159 Γ)
  have h2 := HasTyT.app Γ _ _ _ _ h1
    (HasTyT.conv Γ mn S0e domMn159 _ hmn (mnConv159 Γ))
  have h3 := HasTyT.app Γ _ _ _ _ h2
    (HasTyT.conv Γ mc mcLamTy159 domMc159 _ hmc (mcConv159 Γ))
  have h4 := HasTyT.app Γ _ _ _ _ h3 hmajor
  exact HasTyT.conv Γ _ (.app motive159 major) S0e (.succ .zero) h4
    (.beta Γ (.const 34 []) S0e major S1e (.succ .zero) (tyC34 Γ) (tyS0 _) hmajor)

-- ===== the slot-159 contexts and terms (literal) =====

/-- T2's fifth and sixth domains and codomain, literally (from the
    `checkC`-extracted type; `srcNthBT2eq` pins the identity). -/
def nthB05 : Expr Nat :=
  .app (.app (.app (.const 88 []) (.bvar 2)) (.bvar 1)) (.bvar 0)
def arg0e : Expr Nat := srcNthBArg 0
def mApp6 : Expr Nat :=
  .app (.app (.app (.app arg0e (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)
def leafL : Expr Nat :=
  .app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 5)) (.bvar 4)))
    (.app (.const 2 []) (.bvar 3))) (.bvar 2)

/-- arg2's inferred type, as a literal. -/
def T2lit : Expr Nat :=
  .pi (.const 4 []) (.pi (.const 34 []) (.pi (.const 0 []) (.pi (.const 4 [])
    (.pi nthB05 (.pi mApp6 leafL)))))

/-- its six domains. -/
def T2domsLit : List (Expr Nat) :=
  [.const 4 [], .const 34 [], .const 0 [], .const 4 [], nthB05, mApp6]

/-- the context under `k` of arg2's six binders — literal. -/
def ctxL (k : Nat) : LCtx := (T2domsLit.take k).reverse.map LocalDecl.assumption ++ srcNthBΓ

-- the checker's extracted inferred type IS `T2lit`.
kernel_rfl_theorem srcNthBT2eq : srcNthBDarg2S.1 = T2lit

/-- `arg0`'s spine arguments at `ctxL 6`. -/
def arg0a1 : Expr Nat := .app (.app (.const 36 []) (.bvar 5)) (.bvar 4)
def arg0a2 : Expr Nat := .app (.const 2 []) (.bvar 3)
def arg0a3 : Expr Nat := .bvar 2
def arg0a4 : Expr Nat :=
  .app (.app (.app (.app (.app (.const 90 []) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1)

def lamD : Expr Nat → Expr Nat | .lam A _ => A | e => e
def lamB : Expr Nat → Expr Nat | .lam _ b => b | e => e

/-- the four-stage β chain of the `arg0`-application. -/
def M1e : Expr Nat := instantiate0 arg0a1 (lamB arg0e)
def M2e : Expr Nat := instantiate0 arg0a2 (lamB M1e)
def M3e : Expr Nat := instantiate0 arg0a3 (lamB M2e)
def REXe : Expr Nat := instantiate0 arg0a4 (lamB M3e)

/-- the RED side: `mc' x t rcall` and its three β reducts. -/
def mcE : Expr Nat := .lam (.const 4 []) (.lam (.const 34 []) (.lam S0e
  (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
    (.app (.const 2 []) (.bvar 6))) (.bvar 5))))

def rcallE : Expr Nat := .app (.app (.app (.app (.const 37 [.succ .zero]) motive159)
  (.app (.app (.const 133 []) bound159) (.bvar 2))) mcE) (.bvar 4)

def REDe : Expr Nat := .app (.app (.app mcE (.bvar 5)) (.bvar 4)) rcallE
def R1e : Expr Nat := instantiate0 (.bvar 5) (lamB mcE)
def R2e : Expr Nat := instantiate0 (.bvar 4) (lamB R1e)
def leafE : Expr Nat := instantiate0 rcallE (lamB R2e)

-- ===== the ι witness pin =====

kernel_rfl_theorem srcNthBCertREX : (iotaReductCert (envPre 159) REXe).isSome = true

def srcNthBwREX : Σ' w : IotaWitness (envPre 159), iotaLhsOf w = REXe :=
  (iotaReductCert (envPre 159) REXe).get srcNthBCertREX

kernel_rfl_theorem srcNthBREDeq : iotaRhsOf srcNthBwREX.1 = REDe

-- ===== bvar typings at ctxL 6 =====

def bv6_5 : HasTyT (envPre 159) 0 (ctxL 6) (.bvar 5) (.const 4 []) := .bvar _ 5 _ rfl
def bv6_4 : HasTyT (envPre 159) 0 (ctxL 6) (.bvar 4) (.const 34 []) := .bvar _ 4 _ rfl
def bv6_3 : HasTyT (envPre 159) 0 (ctxL 6) (.bvar 3) (.const 0 []) := .bvar _ 3 _ rfl
def bv6_2 : HasTyT (envPre 159) 0 (ctxL 6) (.bvar 2) (.const 4 []) := .bvar _ 2 _ rfl
def bv6_1 : HasTyT (envPre 159) 0 (ctxL 6) (.bvar 1)
    (.app (.app (.app (.const 88 []) (.bvar 4)) (.bvar 3)) (.bvar 2)) := .bvar _ 1 _ rfl

-- ===== leaf typings at ctxL 6 =====

def hArg0a1 : HasTyT (envPre 159) 0 (ctxL 6) arg0a1 (.const 34 []) :=
  blConsApp _ bv6_5 bv6_4

def hArg0a2 : HasTyT (envPre 159) 0 (ctxL 6) arg0a2 (.const 0 []) :=
  succApp _ bv6_3

def tyNthBNext (Γ : LCtx) :
    HasTyT (envPre 159) 0 Γ (.const 90 [])
      (.pi (.const 4 []) (.pi (.const 34 []) (.pi (.const 0 []) (.pi (.const 4 [])
        (.pi (.app (.app (.app (.const 88 []) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 4)) (.bvar 3)))
            (.app (.const 2 []) (.bvar 2))) (.bvar 1))))))) :=
  .const Γ 90 [] mNthBNext rfl rfl rfl

def hLeaf : HasTyT (envPre 159) 0 (ctxL 6) leafL S0e :=
  nthBApp _ hArg0a1 hArg0a2 bv6_2

def hArg0a4 : HasTyT (envPre 159) 0 (ctxL 6) arg0a4 leafL :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _ (tyNthBNext _) bv6_5) bv6_4) bv6_3) bv6_2) bv6_1

/-- `mn` = `valueAt bound bs : Prop` at `ctxL 6` (REX's mn argument). -/
def mnE : Expr Nat := .app (.app (.const 133 []) bound159) (.bvar 2)

def hMn6 : HasTyT (envPre 159) 0 (ctxL 6) mnE S0e :=
  valueAtApp _ bv6_2

/-- `mc'`'s body `NthB (blCons x' t') (succ n) bs` at `[S0,C34,C4]++ctxL 6`. -/
def hNBody6 : HasTyT (envPre 159) 0
    (LocalDecl.assumption S0e :: LocalDecl.assumption (.const 34 []) ::
      LocalDecl.assumption (.const 4 []) :: ctxL 6)
    (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
      (.app (.const 2 []) (.bvar 6))) (.bvar 5)) S0e :=
  nthBApp _ (blConsApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl))
    (succApp _ (.bvar _ 6 _ rfl)) (.bvar _ 5 _ rfl)

def hMcE : HasTyT (envPre 159) 0 (ctxL 6) mcE mcLamTy159 :=
  .lam _ (.const 4 _) _ _ _ (tyC4 _)
    (.lam _ (.const 34 _) _ _ _ (tyC34 _)
      (.lam _ S0e _ _ _ (tyS0 _) hNBody6))

def hLhs : HasTyT (envPre 159) 0 (ctxL 6) REXe S0e :=
  recBLSpineTy _ arg0a1 mnE mcE hArg0a1 hMn6 hMcE

def hRcall : HasTyT (envPre 159) 0 (ctxL 6) rcallE S0e :=
  recBLSpineTy _ (.bvar 4) mnE mcE bv6_4 hMn6 hMcE

def hRhs : HasTyT (envPre 159) 0 (ctxL 6) REDe S0e :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _ hMcE bv6_5) bv6_4) hRcall

def srcNthBcIota : ConvT (envPre 159) 0 (ctxL 6) REXe REDe S0e :=
  srcNthBwREX.2 ▸ (srcNthBREDeq ▸ .iota _ _ _ _ (DerivedIota.of srcNthBwREX.1)
    (srcNthBwREX.2.symm ▸ hLhs) (srcNthBREDeq.symm ▸ hRhs))

-- ===== the hbody derivations for the seven β steps =====

def NthB0 : Expr Nat := .app (.app (.app (.const 88 []) (.bvar 2)) (.bvar 1)) (.bvar 0)
def NthB1 : Expr Nat :=
  .app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 7)) (.bvar 6)))
    (.bvar 1)) (.bvar 0)
def NthB2 : Expr Nat :=
  .app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 6)) (.bvar 5)))
    (.app (.const 2 []) (.bvar 4))) (.bvar 0)

def mn0e : Expr Nat := .app (.app (.const 133 []) bound159) (.bvar 1)
def mn3e : Expr Nat := .app (.app (.const 133 []) bound159) (.bvar 3)

def mc0e : Expr Nat := .lam (.const 4 []) (.lam (.const 34 []) (.lam S0e
  (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
    (.bvar 5)) (.bvar 4))))
def mc2e : Expr Nat := .lam (.const 4 []) (.lam (.const 34 []) (.lam S0e
  (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
    (.app (.const 2 []) (.bvar 8))) (.bvar 4))))
def mc3e : Expr Nat := .lam (.const 4 []) (.lam (.const 34 []) (.lam S0e
  (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
    (.app (.const 2 []) (.bvar 7))) (.bvar 6))))

-- recbl contexts, newest-first
def ctxR0 : LCtx := LocalDecl.assumption NthB0 :: LocalDecl.assumption (.const 4 []) ::
  LocalDecl.assumption (.const 0 []) :: LocalDecl.assumption (.const 34 []) :: ctxL 6
def ctxR1 : LCtx := LocalDecl.assumption NthB1 :: LocalDecl.assumption (.const 4 []) ::
  LocalDecl.assumption (.const 0 []) :: ctxL 6
def ctxR2 : LCtx := LocalDecl.assumption NthB2 :: LocalDecl.assumption (.const 4 []) :: ctxL 6
def ctxR3 : LCtx := LocalDecl.assumption leafL :: ctxL 6

-- the mc typings at each level — body `NthB (blCons x' t') n' bs'`-variants
def hNBody0 : HasTyT (envPre 159) 0
    (LocalDecl.assumption S0e :: LocalDecl.assumption (.const 34 []) ::
      LocalDecl.assumption (.const 4 []) :: ctxR0)
    (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
      (.bvar 5)) (.bvar 4)) S0e :=
  nthBApp _ (blConsApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl))
    (.bvar _ 5 _ rfl) (.bvar _ 4 _ rfl)

def hMc0 : HasTyT (envPre 159) 0 ctxR0 mc0e mcLamTy159 :=
  .lam _ (.const 4 _) _ _ _ (tyC4 _)
    (.lam _ (.const 34 _) _ _ _ (tyC34 _)
      (.lam _ S0e _ _ _ (tyS0 _) hNBody0))

def hRecbl0 : HasTyT (envPre 159) 0 ctxR0
    (recBLAppOf (.bvar 3) mn0e mc0e) S0e :=
  recBLSpineTy _ (.bvar 3) mn0e mc0e (.bvar _ 3 _ rfl)
    (valueAtApp _ (.bvar _ 1 _ rfl)) hMc0

def hNthB0at : HasTyT (envPre 159) 0
    (LocalDecl.assumption (.const 4 []) :: LocalDecl.assumption (.const 0 []) ::
      LocalDecl.assumption (.const 34 []) :: ctxL 6) NthB0 S0e :=
  nthBApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl)

def hbody0 : HasTyT (envPre 159) 0 (LocalDecl.assumption (.const 34 []) :: ctxL 6)
    (lamB arg0e) (.pi (.const 0 []) (.pi (.const 4 []) (.pi NthB0 S0e))) :=
  .lam _ (.const 0 _) _ _ _ (tyC0 _)
    (.lam _ (.const 4 _) _ _ _ (tyC4 _)
      (.lam _ NthB0 _ _ _ hNthB0at hRecbl0))

-- hbody1 : `λC4.λNthB1.recbl₁` at `[C0]++ctxL6`

def hNBody1 : HasTyT (envPre 159) 0
    (LocalDecl.assumption S0e :: LocalDecl.assumption (.const 34 []) ::
      LocalDecl.assumption (.const 4 []) :: ctxR1)
    (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
      (.bvar 5)) (.bvar 4)) S0e :=
  nthBApp _ (blConsApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl))
    (.bvar _ 5 _ rfl) (.bvar _ 4 _ rfl)

def hMc1 : HasTyT (envPre 159) 0 ctxR1 mc0e mcLamTy159 :=
  .lam _ (.const 4 _) _ _ _ (tyC4 _)
    (.lam _ (.const 34 _) _ _ _ (tyC34 _)
      (.lam _ S0e _ _ _ (tyS0 _) hNBody1))

def hRecbl1 : HasTyT (envPre 159) 0 ctxR1
    (recBLAppOf (.app (.app (.const 36 []) (.bvar 8)) (.bvar 7)) mn0e mc0e) S0e :=
  recBLSpineTy _ (.app (.app (.const 36 []) (.bvar 8)) (.bvar 7)) mn0e mc0e
    (blConsApp _ (.bvar _ 8 _ rfl) (.bvar _ 7 _ rfl))
    (valueAtApp _ (.bvar _ 1 _ rfl)) hMc1

def hbody1 : HasTyT (envPre 159) 0 (LocalDecl.assumption (.const 0 []) :: ctxL 6)
    (lamB M1e) (.pi (.const 4 []) (.pi NthB1 S0e)) :=
  .lam _ (.const 4 _) _ _ _ (tyC4 _)
    (.lam _ NthB1 _ _ _
      (nthBApp _ (blConsApp _ (.bvar _ 7 _ rfl) (.bvar _ 6 _ rfl))
        (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl))
      hRecbl1)

-- hbody2 : `λNthB2.recbl₂` at `[C4]++ctxL6`

def hNBody2 : HasTyT (envPre 159) 0
    (LocalDecl.assumption S0e :: LocalDecl.assumption (.const 34 []) ::
      LocalDecl.assumption (.const 4 []) :: ctxR2)
    (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
      (.app (.const 2 []) (.bvar 8))) (.bvar 4)) S0e :=
  nthBApp _ (blConsApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl))
    (succApp _ (.bvar _ 8 _ rfl)) (.bvar _ 4 _ rfl)

def hMc2 : HasTyT (envPre 159) 0 ctxR2 mc2e mcLamTy159 :=
  .lam _ (.const 4 _) _ _ _ (tyC4 _)
    (.lam _ (.const 34 _) _ _ _ (tyC34 _)
      (.lam _ S0e _ _ _ (tyS0 _) hNBody2))

def hRecbl2 : HasTyT (envPre 159) 0 ctxR2
    (recBLAppOf (.app (.app (.const 36 []) (.bvar 7)) (.bvar 6)) mn0e mc2e) S0e :=
  recBLSpineTy _ (.app (.app (.const 36 []) (.bvar 7)) (.bvar 6)) mn0e mc2e
    (blConsApp _ (.bvar _ 7 _ rfl) (.bvar _ 6 _ rfl))
    (valueAtApp _ (.bvar _ 1 _ rfl)) hMc2

def hbody2 : HasTyT (envPre 159) 0 (LocalDecl.assumption (.const 4 []) :: ctxL 6)
    (lamB M2e) (.pi NthB2 S0e) :=
  .lam _ NthB2 _ _ _
    (nthBApp _ (blConsApp _ (.bvar _ 6 _ rfl) (.bvar _ 5 _ rfl))
      (succApp _ (.bvar _ 4 _ rfl)) (.bvar _ 0 _ rfl))
    hRecbl2

-- hbody3 : `recbl₃` at `[NthB3]++ctxL6` (not a lam)

def hNBody3 : HasTyT (envPre 159) 0
    (LocalDecl.assumption S0e :: LocalDecl.assumption (.const 34 []) ::
      LocalDecl.assumption (.const 4 []) :: ctxR3)
    (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
      (.app (.const 2 []) (.bvar 7))) (.bvar 6)) S0e :=
  nthBApp _ (blConsApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl))
    (succApp _ (.bvar _ 7 _ rfl)) (.bvar _ 6 _ rfl)

def hMc3 : HasTyT (envPre 159) 0 ctxR3 mc3e mcLamTy159 :=
  .lam _ (.const 4 _) _ _ _ (tyC4 _)
    (.lam _ (.const 34 _) _ _ _ (tyC34 _)
      (.lam _ S0e _ _ _ (tyS0 _) hNBody3))

def hbody3 : HasTyT (envPre 159) 0 (LocalDecl.assumption leafL :: ctxL 6)
    (lamB M3e) S0e :=
  recBLSpineTy _ (.app (.app (.const 36 []) (.bvar 6)) (.bvar 5)) mn3e mc3e
    (blConsApp _ (.bvar _ 6 _ rfl) (.bvar _ 5 _ rfl))
    (valueAtApp _ (.bvar _ 3 _ rfl)) hMc3

-- hbody5/6/7 : the RED-side β bodies

def hbody5 : HasTyT (envPre 159) 0 (LocalDecl.assumption (.const 4 []) :: ctxL 6)
    (lamB mcE) (.pi (.const 34 []) (.pi S0e S0e)) :=
  .lam _ (.const 34 _) _ _ _ (tyC34 _)
    (.lam _ S0e _ _ _ (tyS0 _) hNBody6)

def hbody6 : HasTyT (envPre 159) 0 (LocalDecl.assumption (.const 34 []) :: ctxL 6)
    (lamB R1e) (.pi S0e S0e) :=
  .lam _ S0e _ _ _ (tyS0 _)
    (nthBApp _ (blConsApp _ (.bvar _ 7 _ rfl) (.bvar _ 1 _ rfl))
      (succApp _ (.bvar _ 5 _ rfl)) (.bvar _ 4 _ rfl))

def hbody7 : HasTyT (envPre 159) 0 (LocalDecl.assumption S0e :: ctxL 6)
    (lamB R2e) S0e :=
  nthBApp _ (blConsApp _ (.bvar _ 6 _ rfl) (.bvar _ 5 _ rfl))
    (succApp _ (.bvar _ 4 _ rfl)) (.bvar _ 3 _ rfl)

-- ===== the seven-step conversion chain at ctxL 6 =====

def cβ1 := ConvT.beta _ (.const 34 []) (lamB arg0e) arg0a1 _ _ (tyC34 _) hbody0 hArg0a1
def cβ1a := ConvT.app _ _ _ _ _ _ _ cβ1 (ConvT.refl _ _ _ hArg0a2)
def cβ1b := ConvT.app _ _ _ _ _ _ _ cβ1a (ConvT.refl _ _ _ bv6_2)
def cβ1c := ConvT.app _ _ _ _ _ _ _ cβ1b (ConvT.refl _ _ _ hArg0a4)

def cβ2 := ConvT.beta _ (.const 0 []) (lamB M1e) arg0a2 _ _ (tyC0 _) hbody1 hArg0a2
def cβ2a := ConvT.app _ _ _ _ _ _ _ cβ2 (ConvT.refl _ _ _ bv6_2)
def cβ2b := ConvT.app _ _ _ _ _ _ _ cβ2a (ConvT.refl _ _ _ hArg0a4)

def cβ3 := ConvT.beta _ (.const 4 []) (lamB M2e) arg0a3 _ _ (tyC4 _) hbody2 bv6_2
def cβ3a := ConvT.app _ _ _ _ _ _ _ cβ3 (ConvT.refl _ _ _ hArg0a4)

def cβ4 := ConvT.beta _ _ (lamB M3e) arg0a4 _ _ hLeaf hbody3 hArg0a4

def cβ5 := ConvT.beta _ (.const 4 []) (lamB mcE) (.bvar 5) _ _ (tyC4 _) hbody5 bv6_5
def cβ5a := ConvT.app _ _ _ _ _ _ _ cβ5 (ConvT.refl _ _ _ bv6_4)
def cβ5b := ConvT.app _ _ _ _ _ _ _ cβ5a (ConvT.refl _ _ _ hRcall)

def cβ6 := ConvT.beta _ (.const 34 []) (lamB R1e) (.bvar 4) _ _ (tyC34 _) hbody6 bv6_4
def cβ6a := ConvT.app _ _ _ _ _ _ _ cβ6 (ConvT.refl _ _ _ hRcall)

def cβ7 := ConvT.beta _ S0e (lamB R2e) rcallE _ _ (tyS0 _) hbody7 hRcall

/-- the full `dom2`-codomain → `T2`-codomain chain, reversed to `leafL → RHS`. -/
def srcNthBcB : ConvT (envPre 159) 0 (ctxL 6)
    (.app (.app (.app (.app arg0e arg0a1) arg0a2) arg0a3) arg0a4) leafL S0e :=
  .trans _ _ _ _ _ cβ1c (.trans _ _ _ _ _ cβ2b (.trans _ _ _ _ _ cβ3a
    (.trans _ _ _ _ _ cβ4 (.trans _ _ _ _ _ srcNthBcIota
      (.trans _ _ _ _ _ cβ5b (.trans _ _ _ _ _ cβ6a cβ7))))))

-- ===== the π tower over the six shared domains =====

def hNthB05at4 : HasTyT (envPre 159) 0 (ctxL 4) nthB05 S0e :=
  nthBApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl)

-- arg0's typing at ctxL 5 (identical lam-tower, one binder shallower)
def hNthB0at5 : HasTyT (envPre 159) 0
    (LocalDecl.assumption (.const 4 []) :: LocalDecl.assumption (.const 0 []) ::
      LocalDecl.assumption (.const 34 []) :: ctxL 5) NthB0 S0e :=
  nthBApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl)

def ctxR5 : LCtx := LocalDecl.assumption NthB0 :: LocalDecl.assumption (.const 4 []) ::
  LocalDecl.assumption (.const 0 []) :: LocalDecl.assumption (.const 34 []) :: ctxL 5

def hNBody5 : HasTyT (envPre 159) 0
    (LocalDecl.assumption S0e :: LocalDecl.assumption (.const 34 []) ::
      LocalDecl.assumption (.const 4 []) :: ctxR5)
    (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1)))
      (.bvar 5)) (.bvar 4)) S0e :=
  nthBApp _ (blConsApp _ (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl))
    (.bvar _ 5 _ rfl) (.bvar _ 4 _ rfl)

def hMc0at5 : HasTyT (envPre 159) 0 ctxR5 mc0e mcLamTy159 :=
  .lam _ (.const 4 _) _ _ _ (tyC4 _)
    (.lam _ (.const 34 _) _ _ _ (tyC34 _)
      (.lam _ S0e _ _ _ (tyS0 _) hNBody5))

def hRecblM : HasTyT (envPre 159) 0 ctxR5
    (recBLAppOf (.bvar 3) mn0e mc0e) S0e :=
  recBLSpineTy _ (.bvar 3) mn0e mc0e (.bvar _ 3 _ rfl)
    (valueAtApp _ (.bvar _ 1 _ rfl)) hMc0at5

def tyM'' : HasTyT (envPre 159) 0 (ctxL 5) arg0e
    (.pi (.const 34 []) (.pi (.const 0 []) (.pi (.const 4 []) (.pi NthB0 S0e)))) :=
  .lam _ (.const 34 _) _ _ _ (tyC34 _)
    (.lam _ (.const 0 _) _ _ _ (tyC0 _)
      (.lam _ (.const 4 _) _ _ _ (tyC4 _)
        (.lam _ NthB0 _ _ _ hNthB0at5 hRecblM)))

def hM''app : HasTyT (envPre 159) 0 (ctxL 5) mApp6 S0e :=
  .app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _
    (.app _ _ _ _ _ tyM'' (.bvar _ 3 _ rfl)) (.bvar _ 2 _ rfl))
    (.bvar _ 1 _ rfl)) (.bvar _ 0 _ rfl)

def lvT2 : Level :=
  .imax (.succ .zero) (.imax (.succ .zero) (.imax (.succ .zero)
    (.imax (.succ .zero) (.imax .zero (.imax .zero .zero)))))

-- the six-deep π tower: `T2lit ~ srcNthBDom 2`
def srcNthBcT2 : ConvT (envPre 159) 0 srcNthBΓ T2lit (srcNthBDom 2) (.sort lvT2) := by
  refine ConvT.pi _ (.const 4 []) (.const 4 []) _ _ (.succ .zero) _
    (ConvT.refl _ _ _ (tyC4 _)) ?_
  refine ConvT.pi _ (.const 34 []) (.const 34 []) _ _ (.succ .zero) _
    (ConvT.refl _ _ _ (tyC34 _)) ?_
  refine ConvT.pi _ (.const 0 []) (.const 0 []) _ _ (.succ .zero) _
    (ConvT.refl _ _ _ (tyC0 _)) ?_
  refine ConvT.pi _ (.const 4 []) (.const 4 []) _ _ (.succ .zero) _
    (ConvT.refl _ _ _ (tyC4 _)) ?_
  refine ConvT.pi _ nthB05 nthB05 _ _ (.zero) _
    (ConvT.refl _ _ _ hNthB05at4) ?_
  refine ConvT.pi _ mApp6 mApp6 _ _ (.zero) _
    (ConvT.refl _ _ _ hM''app) ?_
  exact ConvT.symm _ _ _ _ srcNthBcB

-- ===== arg2 transported to its expected domain =====

def srcNthBDarg2lit : HasTyT (envPre 159) 0 srcNthBΓ (srcNthBArg 2) T2lit :=
  srcNthBT2eq ▸ srcNthBDarg2S.2

def srcNthBDarg2dom : HasTyT (envPre 159) 0 srcNthBΓ (srcNthBArg 2) (srcNthBDom 2) :=
  .conv _ _ _ _ _ srcNthBDarg2lit srcNthBcT2

-- ===== the seven-application spine and the closing conv =====

def srcNthBP3 := HasTyT.app _ _ _ _ _ srcNthBP2.2 srcNthBDarg2dom

def srcNthBP4 := HasTyT.app _ _ _ _ _ srcNthBP3 srcNthBDarg3

def srcNthBP5 := HasTyT.app _ _ _ _ _ srcNthBP4 srcNthBDarg4

def srcNthBP6 := HasTyT.app _ _ _ _ _ srcNthBP5 srcNthBDarg5

def srcNthBCoreTy : HasTyT (envPre 159) 0 srcNthBΓ srcNthBCore srcNthBTCod :=
  .app _ _ _ _ _ srcNthBP6 srcNthBDarg6

def hLam2 : HasTyT (envPre 159) 0 (srcNthBΓk 2) (.lam srcNthBD2 srcNthBCore)
    (.pi srcNthBD2 srcNthBTCod) :=
  .lam _ _ _ _ _ srcNthBDomTy2 srcNthBCoreTy

def hLam1 : HasTyT (envPre 159) 0 (srcNthBΓk 1) (.lam srcNthBD1 (.lam srcNthBD2 srcNthBCore))
    (.pi srcNthBD1 (.pi srcNthBD2 srcNthBTCod)) :=
  .lam _ _ _ _ _ srcNthBDomTy1 hLam2

def hLam0 : HasTyT (envPre 159) 0 [] srcNthBBody srcNthBPi :=
  .lam _ _ _ _ _ srcNthBDomTy0 hLam1

def srcNthBTyT : HasTyT (envPre 159) 0 [] srcNthBBody mNthBNilVa.mtype :=
  hasTyT_of_tyConv hLam0 srcNthBClose

end



#print axioms srcNthBTyT

#print axioms srcNthB_head_admits
#print axioms srcNthB_arg0_admits
#print axioms srcNthB_arg1_admits
#print axioms srcNthB_arg2_checks
#print axioms srcNthB_arg3_admits
#print axioms srcNthB_arg4_admits
#print axioms srcNthB_arg5_admits
#print axioms srcNthB_arg6_admits
#print axioms srcNthB_dom0_ty
#print axioms srcNthB_dom1_ty
#print axioms srcNthB_dom2_ty
#print axioms srcNthBA_admits
#print axioms srcNthB_conv_admits
#print axioms srcNthB_refuses
#print axioms srcNthBDhead
#print axioms srcNthBDarg2S
#print axioms srcNthBP2
#print axioms srcNthBClose
#print axioms srcNthBATyT

end Rcic.Declarative
