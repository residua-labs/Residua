import rcic.RcicParRedT
import rcic.RcicParRedCore
import rcic.RcicParRedIota
import rcic.RcicPinLoopEraseWf
import rcic.RcicTypedFunRecPins
import rcic.RcicTypedGroupPinsVec
import rcic.RcicTypedIdxAdmitted
import rcic.RcicTypedConv
import rcic.RcicDTMetaTypedSR
import rcic.ScmSrcGroupsKernelRfl

set_option maxRecDepth 8192

/-!
# `RcicParRedTPins` — the S1 pre-landing pins (#6454)

Three pins plus the erased-shape census of `ParRedT` (`RcicParRedT.lean`).

## The arm census

`parRedT_forget?` erases a typed step to its `ParRed`-star image. The 13
ordinary `ParRedT` arms land on the erased `ParRed`'s arm-shapes
one-for-one:

| `ParRedT` arm | erased counterpart | landing |
|---|---|---|
| `refl` | `ParRed.refl` | `some` |
| `sortEq` | `ParRed.sortEq` | `some` |
| `consts` | `ParRed.consts` | `some` |
| `bvarZeta` | `ParRed.bvarZeta` | `some`, at `hv`'s image |
| `delta` | `ParRed.delta` | `some` (`hlen`/`hwf`/index typings drop) |
| `app` | `ParRed.app` | `some`, at `hf`/`ha`'s images |
| `beta` | `ParRed.beta` | `some` — the domain is unstepped on both sides (`ParRed.refl A`) |
| `zeta` | `ParRed.zeta` | `some`, `ParRed.refl A` at the annotation |
| `iotaSpine .ofU` | `ParRed.iotaSpine` | `some` — the two-step TML star (arg step, then the witness's burn) |
| `lit` | `ParRed.lit` | `some` (`hexp` drops) |
| `conv` | (index invisible erased) | `some`, the sub-step's image |
| `lam`/`pi`/`letE` | `ParRed.lam`/`pi`/`letE` | `none` — the domain premise is `ConvT` (F-ParRedT-2); its erased image is `Conv`, which the erased arm cannot consume. The CONCLUSION pairs are verbatim the erased arms'. |
| `iotaStarK` | — | `none` (the K-gate is typed) |
| `peq` | — | `none` (`PEq` is conv-level) |
| `iotaSpine .ofUS` | — | `none` (`IotaWitnessS` names redexes legacy ι cannot reach) |
| `eta` | — | `none` (the erased `ParRed` has no η — `Conv.eta` is conv-level, F-ParRedT-8) |

No `sorry`, no new axiom.
-/

namespace Rcic.Declarative

/-- A star of length ≤ 1 as its single step, when it is one. -/
def parRedStar_one? {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat} :
    ParRedStar E n Γ a b → Option (ParRed E n Γ a b)
  | .refl _ a => .some (.refl _ a)
  | .tail h (.refl _ _) => .some h
  | .tail _ (.tail _ _) => .none

/-- Forget the typing carried by a `ParRedT` step — the executable census
    of the 13 ordinary arms (see the header table). -/
def parRedT_forget? {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    ParRedT PEq E n Γ a b T → Option (ParRedStar E n Γ a b)
  | .refl Γ a _ _ => .some (.refl Γ a)
  | .sortEq Γ l₁ l₂ _ h _ _ => .some (parRedStar_one (.sortEq Γ l₁ l₂ h))
  | .consts Γ r ls ls' _ h _ _ => .some (parRedStar_one (.consts Γ r ls ls' h))
  | .bvarZeta Γ i A v v' _ h hv _ _ =>
      (parRedT_forget? hv).bind parRedStar_one? |>.map fun s =>
        .tail (.bvarZeta Γ i A v v' h s) (.refl Γ _)
  | .delta Γ r ls m b _ hres hbody htr _ _ _ _ =>
      .some (parRedStar_one (.delta Γ r ls m b hres hbody htr))
  | .app Γ _ f' _ a' _ _ _ _ _ hf _ _ _ ha _ =>
      match parRedT_forget? hf >>= parRedStar_one?,
            parRedT_forget? ha >>= parRedStar_one? with
      | some hf', some ha' =>
          .some (parRedStar_one (.app Γ _ f' _ a' hf' ha'))
      | _, _ => .none
  | .beta Γ A _ body' arg arg' _ _ _ _ _ _ _ hb ha _ =>
      match parRedT_forget? hb >>= parRedStar_one?,
            parRedT_forget? ha >>= parRedStar_one? with
      | some hb', some ha' =>
          .some (parRedStar_one
            (.beta Γ A A _ body' arg arg' (.refl Γ A) hb' ha'))
      | _, _ => .none
  | .lam .. => .none
  | .pi .. => .none
  | .letE .. => .none
  | .zeta Γ A _ value' _ body' _ _ _ _ hv _ _ hb _ =>
      match parRedT_forget? hv >>= parRedStar_one?,
            parRedT_forget? hb >>= parRedStar_one? with
      | some hv', some hb' =>
          .some (parRedStar_one
            (.zeta Γ A A _ value' _ body' (.refl Γ A) hv' hb'))
      | _, _ => .none
  | .iotaSpine Γ _ _ _ _ hstep hI _ _ =>
      match hI with
      | .ofU w =>
          (parRedT_forget? hstep).map fun s =>
            parRedStar_trans s
              (.tail
                (.iotaSpine Γ w w.ls w.lsC (eqNList_refl _) (eqNList_refl _)
                  w.preMajor w.preMajor (w.ctorParams ++ w.fields)
                  (w.ctorParams ++ w.fields)
                  (parRedArgs_refl _) (parRedArgs_refl _) rfl rfl rfl)
                (.refl Γ _))
      | .ofUS _ => .none
  | .lit Γ t _ _ => .some (parRedStar_one (.lit Γ t))
  | .eta .. => .none
  | .iotaStarK .. => .none
  | .iotaStarKEta .. => .none
  | .peq .. => .none
  | .conv _ _ _ _ _ h _ => parRedT_forget? h

/-! ## (2) ι★K at Loop — the singleton-Prop step

`pinLoopEnvT` (60 `Loop : Prop`, 61 `mk : Loop → Loop`, 62 the AnySort
recursor) is a singleton-Prop family: `iotaStarK`'s typed gate lands with
the synthesized `mk`-spine witness `wLoopK`, the major the bound variable
`x`, and the union premise `DerivedIotaU.ofU wLoopK`. The step is
`rec M m x ⇒ m x (rec M m x)` at `T = M x` — the Loop clique's
contraction as a `ParRedT` arm. -/

/-- the Loop `IotaWitness` of the synthesized `mk x` redex —
    `recCall (const 62 [param 0]) [M, m] (mk x)`. Every field is
    mechanical: the env chain is `extendEnv`-literal, the peels/tel
    checks kernel-compute, `Tm = .const 60 []`. -/
def wLoopK : IotaWitness pinLoopEnvT where
  recRef := 62
  ctorRef := 61
  ls := [.param 0]
  lsC := []
  recMember := pinLoopRecT
  ctorMember := pinLoopMkT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 2, .bvar 1]
  fields := [.bvar 0]
  ctorParams := []
  kinds := [.directRec]
  minor := .bvar 1
  hlen := rfl
  familyRef := 60
  famMember := pinLoopFamT
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.const 60 []]
  ctorResult := .const 60 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [loopMotT, loopMinorT, .const 60 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .pi (.const 60 []) (.const 60 [])
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- the synthesized lhs `rec M m (mk x)`. -/
def wLoopLhs : Expr Nat := iotaLhsOf wLoopK

/-- the synthesized rhs `m x (rec M m x)`. -/
def wLoopRhs : Expr Nat := iotaRhsOf wLoopK

private def loopAppT {f a A B : Expr Nat} {Γ : LCtx}
    (hf : HasTyT pinLoopEnvT 1 Γ f (.pi A B))
    (ha : HasTyT pinLoopEnvT 1 Γ a A) :
    HasTyT pinLoopEnvT 1 Γ (.app f a) (instantiate0 a B) :=
  .app Γ f a A B hf ha

/-- `x : Loop` in the equation context. -/
def loopVarTyT : HasTyT pinLoopEnvT 1 pinLoopCtx (.bvar 0) (.const 60 []) :=
  .bvar _ 0 _ rfl

/-- `mk x : Loop` — the ctor-spine major. -/
def loopMkTyT :
    HasTyT pinLoopEnvT 1 pinLoopCtx
      (.app (.const 61 []) (.bvar 0)) (.const 60 []) :=
  .app pinLoopCtx (.const 61 []) (.bvar 0) (.const 60 []) (.const 60 [])
    (.const _ 61 [] pinLoopMkT rfl rfl rfl) loopVarTyT

/-- `Loop : Sort 0` — the `irr` evidence for the `mk x ≈ x` index
    conversion (`hTm0` and the `hc` below). -/
def loopFamTyT : HasTyT pinLoopEnvT 1 pinLoopCtx (.const 60 []) (.sort .zero) :=
  .const _ 60 [] pinLoopFamT rfl rfl rfl

/-- `M (mk x) ≈ M x` at `Sort (param 0)` — the index conversion the
    synthesized-ι endpoint typings ride on. -/
def loopIndexConv :
    ConvT pinLoopEnvT 1 pinLoopCtx
      (.app (.bvar 2) (.app (.const 61 []) (.bvar 0))) loopMx
      (.sort (.param 0)) :=
  .app pinLoopCtx (.bvar 2) (.bvar 2) (.app (.const 61 []) (.bvar 0))
    (.bvar 0) (.const 60 []) (.sort (.param 0))
    (.refl _ _ _ (.bvar _ 2 _ rfl))
    (.irr _ _ _ _ loopFamTyT loopMkTyT loopVarTyT)

/-- `rec M m x : M x` — the step's source, typed. -/
def loopLhsTyT : HasTyT pinLoopEnvT 1 pinLoopCtx
    (foldApps pinLoopRecHead [.bvar 2, .bvar 1, .bvar 0]) loopMx := by
  have hM : HasTyT pinLoopEnvT 1 pinLoopCtx (.bvar 2) loopMotT :=
    .bvar _ 2 _ rfl
  have hm : HasTyT pinLoopEnvT 1 pinLoopCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have h0 : HasTyT pinLoopEnvT 1 pinLoopCtx pinLoopRecHead
      (.pi loopMotT loopCodP) :=
    .const _ 62 [.param 0] pinLoopRecT rfl rfl rfl
  have h1' : HasTyT pinLoopEnvT 1 pinLoopCtx (.app pinLoopRecHead (.bvar 2))
      (.pi loopMinorAt loopCodM) :=
    loopAppT h0 hM
  have h2' : HasTyT pinLoopEnvT 1 pinLoopCtx
      (.app (.app pinLoopRecHead (.bvar 2)) (.bvar 1)) loopCodT :=
    loopAppT h1' hm
  exact loopAppT h2' loopVarTyT

/-- `m x (rec M m x) : M x` — the step's reduct, typed (`irr`-converted
    to the shared index `M x`). -/
def loopRhsTyT : HasTyT pinLoopEnvT 1 pinLoopCtx wLoopRhs loopMx := by
  have hm : HasTyT pinLoopEnvT 1 pinLoopCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have h4' : HasTyT pinLoopEnvT 1 pinLoopCtx (.app (.bvar 1) (.bvar 0))
      loopMxTy :=
    loopAppT hm loopVarTyT
  have h5 : HasTyT pinLoopEnvT 1 pinLoopCtx wLoopRhs
      (.app (.bvar 2) (.app (.const 61 []) (.bvar 0))) :=
    loopAppT h4' loopLhsTyT
  exact .conv _ _ _ _ _ h5 loopIndexConv

/-- `rec M m (mk x) : M x` — the synthesized redex, typed (`hlι`). -/
def loopLhsITyT : HasTyT pinLoopEnvT 1 pinLoopCtx wLoopLhs loopMx := by
  have hM : HasTyT pinLoopEnvT 1 pinLoopCtx (.bvar 2) loopMotT :=
    .bvar _ 2 _ rfl
  have hm : HasTyT pinLoopEnvT 1 pinLoopCtx (.bvar 1) loopMinorAt :=
    .bvar _ 1 _ rfl
  have h0 : HasTyT pinLoopEnvT 1 pinLoopCtx pinLoopRecHead
      (.pi loopMotT loopCodP) :=
    .const _ 62 [.param 0] pinLoopRecT rfl rfl rfl
  have h1' : HasTyT pinLoopEnvT 1 pinLoopCtx (.app pinLoopRecHead (.bvar 2))
      (.pi loopMinorAt loopCodM) :=
    loopAppT h0 hM
  have h2' : HasTyT pinLoopEnvT 1 pinLoopCtx
      (.app (.app pinLoopRecHead (.bvar 2)) (.bvar 1)) loopCodT :=
    loopAppT h1' hm
  have h3 : HasTyT pinLoopEnvT 1 pinLoopCtx wLoopLhs
      (.app (.bvar 2) (.app (.const 61 []) (.bvar 0))) :=
    loopAppT h2' loopMkTyT
  exact .conv _ _ _ _ _ h3 loopIndexConv

/-- PIN 1 — an `iotaStarK` step at Loop: `rec M m x ⇒ m x (rec M m x)`
    at `M x`. The typed K-gate lands (`hmajor`/`hmk` at `Tm = Loop`,
    `hsel` the singleton-Prop selection, `hι` the union's `.ofU` at the
    synthesized spine). -/
def pinParRedT_iotaStarK_loop
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type} :
    ParRedT PEq pinLoopEnvT 1 pinLoopCtx
      (recCall pinLoopRecHead [.bvar 2, .bvar 1] (.bvar 0))
      wLoopRhs loopMx :=
  .iotaStarK pinLoopCtx wLoopK (.bvar 0) (.const 60 []) _ loopMx .zero True
    rfl
    (.singletonProp (fun _ => rfl) rfl True.intro)
    ⟨[], rfl⟩ loopVarTyT loopMkTyT loopFamTyT (.ofU wLoopK)
    loopLhsITyT loopLhsTyT loopRhsTyT

/-! ## (3) gate refusal — index mismatch

At the indexed family `Vec` (`vecEnvUT`: family `4`, `vnil` `5`,
`vcons` `6`, recursor `7` over `natEnvU`), the `iotaStarK` gate's
`hmajor : HasTyT Γ major Tm` premise can't be discharged when the
major's stored index differs from the ctor's result index: `bvar`
inversion (`hasTyTInv_bvar`) leaves the conversion debt
`TyConvT (Vec Nat 0) (Vec Nat 1)` — the index gap the gate refuses. -/

/-- `Vec Nat 0` — the major's stored index. -/
def pinVecIdxNat0 : Expr Nat :=
  .app (.app (.const 4 []) (.const 0 [])) (.const 1 [])

/-- `Vec Nat 1` — the ctor-result's index. -/
def pinVecIdxNat1 : Expr Nat :=
  .app (.app (.const 4 []) (.const 0 [])) (.app (.const 2 []) (.const 1 []))

/-- the major's context: `x : Vec Nat 0`. -/
def pinVecMajCtx : LCtx := [.assumption pinVecIdxNat0]

/-- PIN 2 — the index debt: a `bvar` major stored at `Vec Nat 0` typed at
    `Vec Nat 1` pays `TyConvT (Vec Nat 0) (Vec Nat 1)`. The K-gate's
    `hmajor` premise reduces to exactly this conversion — its failure is
    the refusal. -/
def pin_iotaStarK_gate_indexDebt {n : Nat}
    (h : HasTyT vecEnvUT n pinVecMajCtx (.bvar 0) pinVecIdxNat1) :
    TyConvT vecEnvUT n pinVecMajCtx pinVecIdxNat0 pinVecIdxNat1 := by
  obtain ⟨A', hlk, hcv⟩ := hasTyTInv_bvar h rfl
  have hA' : A' = pinVecIdxNat0 := (Option.some.inj hlk).symm
  subst hA'
  exact hcv

/-- the contrapositive: where the index conversion fails, the gate's
    major premise cannot be inhabited — the recursor stays neutral.
    (`→ False`: `TyConvT`/`HasTyT` are `Type`-valued.) -/
theorem pin_iotaStarK_gate_indexRefusal {n : Nat}
    (hno : TyConvT vecEnvUT n pinVecMajCtx pinVecIdxNat0 pinVecIdxNat1 → False) :
    HasTyT vecEnvUT n pinVecMajCtx (.bvar 0) pinVecIdxNat1 → False :=
  fun h => hno (pin_iotaStarK_gate_indexDebt h)

/-! ## (4) `.ofUS` at W — the frec ι step

`wEnv` (`W` at 4, `sup` at 5, `Wrec` at 6 over `natEnvU`) has a
function-recursive field `f : Π (_ : Nat), W` — no legacy `IotaWitness`
exists for its iota (`wIotaWitness_nokind`). The typed route is
`IotaWitnessS`, produced by the recursor's `RecursorGroupIdxAdmittedT`
coverage (`ofCheck`), landed in `ParRedT` through `DerivedIotaU.ofUS`.
The step is the frec contraction `Wrec M m (sup a f) ⇒ m a f (fun b =>
Wrec M m (f b))` at `M (sup a f)`. -/

/-- the typed recursor/index obligation at `wEnv` — `covered` carries the
    canonical `IotaWitnessS`. -/
def wIdxAdmT : RecursorGroupIdxAdmittedT wGroupAdmitted wIotaClause :=
  .ofCheck _ _ (by with_unfolding_all rfl)

/-- the canonical `IotaWitnessS` for `sup`. -/
def wSupWS : IotaWitnessS wEnv := (wIdxAdmT.covered ⟨0, by decide⟩).1

-- the redex is `Wrec M m (sup a f)` in `[f, a, m, M]`.
kernel_rfl_theorem wSupWS_lhs :
    iotaLhsOfS wSupWS =
      .app (.app (.app (.const 6 [.param 0]) (.bvar 3)) (.bvar 2))
        (.app (.app (.const 5 []) (.bvar 1)) (.bvar 0))

-- the reduct is the admission schema `m a f (fun b => Wrec M m (f b))`.
kernel_rfl_theorem wSupWS_rhs : iotaRhsOfS wSupWS = wSchema

-- the redex, typed at the equation's type (`tyAtC` — the equation's
-- pieces are direct, `wRecTy_direct`).
kernel_rfl_theorem wSupWS_lhs_check :
    (tyAtC wEnv 1 8 wIotaCtx (iotaLhsOfS wSupWS) wEqTy).isSome = true

def wSupWS_lhsTyT : HasTyT wEnv 1 wIotaCtx (iotaLhsOfS wSupWS) wEqTy :=
  (tyAtC wEnv 1 8 wIotaCtx (iotaLhsOfS wSupWS) wEqTy).get wSupWS_lhs_check

-- the reduct, typed — the same check admission's clause ran
-- (`iotaEquationTypedT_of_check` at fuel 8 over this ctx/type).
kernel_rfl_theorem wSupWS_rhs_check :
    (tyAtC wEnv 1 8 wIotaCtx wSchema wEqTy).isSome = true

def wSupWS_rhsTyT : HasTyT wEnv 1 wIotaCtx (iotaRhsOfS wSupWS) wEqTy :=
  wSupWS_rhs ▸ (tyAtC wEnv 1 8 wIotaCtx wSchema wEqTy).get wSupWS_rhs_check

/-- PIN 3 — the `.ofUS` frec step at W: `Wrec M m (sup a f) ⇒
    m a f (fun b => Wrec M m (f b))` at `M (sup a f)`, through
    `iotaSpine` at the trivial arg step. -/
def pinParRedT_iotaSpine_ofUS_W
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type} :
    ParRedT PEq wEnv 1 wIotaCtx (iotaLhsOfS wSupWS) (iotaRhsOfS wSupWS)
      wEqTy :=
  .iotaSpine wIotaCtx _ _ _ _
    (.refl _ _ _ wSupWS_lhsTyT) (.ofUS wSupWS)
    wSupWS_lhsTyT wSupWS_rhsTyT

/-! ## (5) η at `natEnvPrefix` — the step, the domain refusal, the β/η pair

`natEnvPrefix` (`0` = `N : Sort 1`, `1` = `zero`, `2` = `succ : N → N`)
is the η fixture: `lift 0 1 (.const 2 [])` reduces to `succ` itself
(consts carry no bvars), so the η source `λn. succ n` is
`.lam (.const 0 []) (.app (.const 2 []) (.bvar 0))` and every
`instantiate0`/`lift` along the pair's paths is definitional. -/

/-- `succ` — the η function. -/
def pinEtaF : Expr Nat := .const 2 []

/-- `N` — the η annotation AND `succ`'s Π-domain (the `ConvT.eta`
    trick: alignment syntactic by construction). -/
def pinEtaA : Expr Nat := .const 0 []

/-- `λn. succ n` — the η source (`lift 0 1 f = f` on consts). -/
def pinEtaSrc : Expr Nat :=
  .lam pinEtaA (.app (lift 0 1 pinEtaF) (.bvar 0))

/-- `N → N` — the η step's index. -/
def pinEtaTy : Expr Nat := .pi pinEtaA (.const 0 [])

/-- `succ : N → N`. -/
def pinEtaFTyT {n : Nat} : HasTyT natEnvPrefix n [] pinEtaF pinEtaTy :=
  .const [] 2 [] natSuccMember rfl rfl rfl

/-- `zero : N` — the application's argument. -/
def pinEtaZeroTyT {n : Nat} :
    HasTyT natEnvPrefix n [] (.const 1 []) pinEtaA :=
  .const [] 1 [] natZeroMember rfl rfl rfl

/-- `succ n : N` under `n : N` — the expansion body's typing. -/
def pinEtaBodyTyT {n : Nat} : HasTyT natEnvPrefix n [.assumption pinEtaA]
    (.app (lift 0 1 pinEtaF) (.bvar 0)) pinEtaA :=
  .app _ (lift 0 1 pinEtaF) (.bvar 0) pinEtaA pinEtaA
    (.const _ 2 [] natSuccMember rfl rfl rfl)
    (.bvar _ 0 _ rfl)

/-- `λn. succ n : N → N` — the left endpoint's typing (`hl`). -/
def pinEtaSrcTyT {n : Nat} :
    HasTyT natEnvPrefix n [] pinEtaSrc pinEtaTy :=
  .lam [] pinEtaA (.succ .zero) _ pinEtaA
    (.const _ 0 [] natFamMember rfl rfl rfl) pinEtaBodyTyT

/-- PIN 4 — an η step at `natEnvPrefix`:
    `λn. succ n ⇒ succ` at `N → N`. `hf` is the Tait–Martin–Löf
    refl step on `succ`; `hl` the left endpoint's typing. -/
def pinParRedT_eta_succ
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type} {n : Nat} :
    ParRedT PEq natEnvPrefix n [] pinEtaSrc pinEtaF pinEtaTy :=
  .eta [] pinEtaF pinEtaF pinEtaA (.const 0 [])
    (.refl _ _ _ pinEtaFTyT) pinEtaSrcTyT

/-- `Sort 1` — the mismatched η annotation (vs `succ`'s real domain
    `N`): the η arm's `hf` demands `succ : Π (Sort 1) B`, whose left
    typing pays `Π N N ≡ Π (Sort 1) B`. -/
def pinEtaMisDom : Expr Nat := .sort (.succ .zero)

/-- PIN 5 — the domain-alignment debt: `succ` typed at a Π whose
    domain is `Sort 1` leaves exactly `TyConvT (Π N N) (Π (Sort 1) B)`
    (`hasTyTInv_const` on `succ`'s stored `N → N`). The η arm's
    annotation IS the function's Π-domain by construction — a
    mismatched annotation is the index-mismatch position of the η
    gate. -/
def pinParRedT_eta_domainDebt {n : Nat} {B : Expr Nat}
    (h : HasTyT natEnvPrefix n [] pinEtaF (.pi pinEtaMisDom B)) :
    TyConvT natEnvPrefix n [] pinEtaTy (.pi pinEtaMisDom B) := by
  obtain ⟨m, hres, _, _, hcv⟩ := hasTyTInv_const h rfl
  injection hres with hm
  subst hm
  exact hcv

/-- the contrapositive: where the domain conversion fails, the η
    gate's function-typing premise cannot be inhabited — the η step
    is unformed at a mismatched annotation. (`→ False`: `TyConvT`/
    `HasTyT` are `Type`-valued.) -/
theorem pinParRedT_eta_domainRefusal {n : Nat} {B : Expr Nat}
    (hno : TyConvT natEnvPrefix n [] pinEtaTy (.pi pinEtaMisDom B) → False) :
    HasTyT natEnvPrefix n [] pinEtaF (.pi pinEtaMisDom B) → False :=
  fun h => hno (pinParRedT_eta_domainDebt h)

/-- `(λn. succ n) zero` — the β/η pair's source. -/
def pinEtaAppSrc : Expr Nat := .app pinEtaSrc (.const 1 [])

/-- `succ zero` — the pair's join target. -/
def pinEtaAppRed : Expr Nat := .app pinEtaF (.const 1 [])

/-- `succ zero : N` — the join target's typing. -/
def pinEtaAppRedTyT {n : Nat} :
    HasTyT natEnvPrefix n [] pinEtaAppRed pinEtaA :=
  .app [] pinEtaF (.const 1 []) pinEtaA pinEtaA pinEtaFTyT pinEtaZeroTyT

/-- PIN 6a — the β route: `(λn. succ n) zero` burns to `succ zero`
    (`instantiate0 zero (app succ x)` reduces definitionally), body
    and argument stepping by refl. -/
def pinParRedT_betaEta_beta
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type} {n : Nat} :
    ParRedT PEq natEnvPrefix n [] pinEtaAppSrc pinEtaAppRed pinEtaA :=
  .beta [] pinEtaA _ _ (.const 1 []) (.const 1 []) pinEtaA
    (.succ .zero) (.succ .zero) (.succ .zero)
    (.const [] 0 [] natFamMember rfl rfl rfl)
    (.const _ 0 [] natFamMember rfl rfl rfl)
    (.const [] 0 [] natFamMember rfl rfl rfl)
    (.refl _ _ _ pinEtaBodyTyT) (.refl _ _ _ pinEtaZeroTyT)
    pinEtaAppRedTyT

/-- PIN 6b — the app(η) route: the function η-contracts inside the
    application spine — the same endpoints as `pinParRedT_betaEta_beta`
    by a different arm. -/
def pinParRedT_betaEta_eta
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type} {n : Nat} :
    ParRedT PEq natEnvPrefix n [] pinEtaAppSrc pinEtaAppRed pinEtaA :=
  .app [] pinEtaSrc pinEtaF (.const 1 []) (.const 1 [])
    pinEtaA pinEtaA pinEtaTy (.succ .zero) (.succ .zero)
    (.eta [] pinEtaF pinEtaF pinEtaA (.const 0 [])
      (.refl _ _ _ pinEtaFTyT) pinEtaSrcTyT)
    (.refl _ _)
    (.const _ 0 [] natFamMember rfl rfl rfl)
    (.const [] 0 [] natFamMember rfl rfl rfl)
    (.refl _ _ _ pinEtaZeroTyT)
    pinEtaAppRedTyT

/-- PIN 6 — the β/η critical pair at `(λn. succ n) zero`: two
    one-step derivations of the same endpoints by different arms —
    the join is literal at `succ zero`. -/
def pinParRedT_betaEta_join
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type} {n : Nat} :
    Σ' c : Expr Nat,
      ParRedT PEq natEnvPrefix n [] pinEtaAppSrc c pinEtaA ×'
      ParRedT PEq natEnvPrefix n [] pinEtaAppSrc c pinEtaA :=
  ⟨_, pinParRedT_betaEta_beta, pinParRedT_betaEta_eta⟩

#print axioms Rcic.Declarative.pinParRedT_eta_succ
#print axioms Rcic.Declarative.pinParRedT_eta_domainDebt
#print axioms Rcic.Declarative.pinParRedT_eta_domainRefusal
#print axioms Rcic.Declarative.pinParRedT_betaEta_join

#print axioms Rcic.Declarative.parRedT_forget?
#print axioms Rcic.Declarative.pinParRedT_iotaStarK_loop
#print axioms Rcic.Declarative.pin_iotaStarK_gate_indexDebt
#print axioms Rcic.Declarative.pin_iotaStarK_gate_indexRefusal
#print axioms Rcic.Declarative.pinParRedT_iotaSpine_ofUS_W

end Rcic.Declarative
