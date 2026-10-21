/- rcic: DT-025/A-6 — the Loop refutation at the TYPED judgment.

cc's 12:3xZ ruling on #6293: before any plain Hop restatement, measure the
Loop refutation. The legacy `Normalizing` row is already refuted
(`normalizing_false`, `RcicNormalizingFalse.lean:254`) via the unchecked
proof-irrelevance collapse. Here the same non-normalization is exhibited
INSIDE the typed judgment over the erased Loop environment, using only
the cyclic conversion `X ≡ X → X : sort 0` (`pinLoopConv`, re-derived
here directly in `ConvT`):

* `loopXT`/`loopArrowT` — the erased `rec.{1} M m t` and its self-arrow.
* `pinLoopWitness` — a concrete `IotaWitness` for the Loop ι-step
  `F (mk t) →ι m t (F t)` at `eraseEnv pinLoopEnvA` (the `pinNatZeroWitness`
  recipe; every field discharges by `rfl`/`decide`).
* `convT_pinLoop` — `ConvT` data for `X ≡ X → X : sort 0` at `Γ₀`, the
  `pinLoopConv` derivation on the plain side (irr at `t ≡ mk t`, ι via
  the witness, β twice, congruence at the major).
* `omegaT_pinLoop_typed` — `Ω_X = (λx:X. x x)(λx:X. x x)` typed at `X`
  in `Γ₀ = [t : Loop]`: `x`'s type `lift 0 1 X` converts to its own
  arrow by `convTWeaken` on `convT_pinLoop` — Abel–Coquand's typed
  ω, concretely in the tree.
* `normalizingT_false_pinLoop` — every `ParRedStar` reduct of `Ω_X`
  keeps a `ParRed` step: the `OmXT` invariant (binary `app`-trees whose
  λ-leaves are `x x`-bodied) survives reduction and is never head-normal.
  Reuses `RcicNormalizingFalse`'s `OmTree` pattern (`headSym`,
  `recCall_ne_of_headSym`, `parRed_app`/`parRed_lam`/`parRed_bvar`).

No `sorry`. `closure_claim` stays 0. -/

import rcic.RcicPinLoopEraseWf
import rcic.RcicTypedWeaken
import rcic.RcicTypedEnvEntry
import rcic.RcicNormalizingFalse
import rcic.RcicAnnRecPins

namespace Rcic.Declarative

open Ann

/-! ## (1) the erased Loop terms -/

/-- `Loop` itself. -/
def loopTyT : Expr Nat := .const 60 []
/-- the motive `λ (_ : Loop). Prop`. -/
def loopMotTT : Expr Nat := .lam loopTyT (.sort .zero)
/-- the minor's body under `l` and `ih`: `ih → ih`. -/
def loopBodyTT : Expr Nat := .pi (.bvar 0) (.bvar 1)
/-- the ih-λ `λ (ih : M l). ih → ih`. -/
def loopIhLamTT : Expr Nat := .lam (.app loopMotTT (.bvar 0)) loopBodyTT
/-- the minor `λ (l : Loop) (ih : M l). ih → ih`. -/
def loopMinTT : Expr Nat := .lam loopTyT loopIhLamTT
/-- `rec.{1} (λ _. Prop) (λ l ih. ih → ih)`. -/
def loopFT : Expr Nat := .app (.app (.const 62 [.succ .zero]) loopMotTT) loopMinTT
/-- `X = rec M m t` at the variable `0`. -/
def loopXT : Expr Nat := .app loopFT (.bvar 0)
/-- the self-arrow `X → X`. -/
def loopArrowT : Expr Nat := .pi loopXT (.app loopFT (.bvar 1))
/-- the Loop context `t : Loop`. -/
def loopΓ : LCtx := [.assumption loopTyT]
/-- `Ω_X = (λx:X. x x)(λx:X. x x)`. -/
def omegaXT : Expr Nat := .app (.lam loopXT (.app (.bvar 0) (.bvar 0)))
  (.lam loopXT (.app (.bvar 0) (.bvar 0)))

/-- the erased terms are the `erase`-images, definitionally. -/
theorem loopXT_eq : erase pinLoopA = loopXT := rfl
theorem loopArrowT_eq : erase pinLoopArrow = loopArrowT := rfl
theorem loopΓ_eq : eraseCtx [.assumption (.const 60 [])] = loopΓ := rfl

/-! ## (2) the ι witness for `F (mk t) →ι m t (F t)` -/

/-- main's ι witness for `rec.{1} M m (mk t) ⇝ m t (rec M m t)` in the
erased Loop group — the `pinNatZeroWitness` recipe: `preMajor` is
`[motive, minor]`, `fields` is the single direct-recursive field `t`,
`kinds = [.directRec]`. Every layout premise discharges by computation. -/
def pinLoopWitness : IotaWitness (eraseEnv pinLoopEnvA) where
  recRef := 62
  ctorRef := 61
  ls := [.succ .zero]
  lsC := []
  recMember := eraseMember pinLoopRecMemberA
  ctorMember := eraseMember pinLoopMkA
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [loopMotTT, loopMinTT]
  fields := [.bvar 0]
  ctorParams := []
  kinds := [.directRec]
  minor := loopMinTT
  hlen := rfl
  familyRef := 60
  famMember := eraseMember pinLoopFamA
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
  ctorDoms := [loopTyT]
  ctorResult := loopTyT
  hpeel := rfl
  hfamApp := by decide
  hkinds := by decide
  recDoms := [loopMotT, loopMinorT, loopTyT]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by decide
  hctorClosed := by decide
  hlsLen := rfl
  ctorAfterParams := .pi loopTyT loopTyT
  hctorAfter := rfl
  hctorTel := by decide
  hfamTel := by decide
  hresTel := by decide

/-- the witness's left-hand side is `F (mk t)`, definitionally. -/
theorem pinLoopWitness_lhs : iotaLhsOf pinLoopWitness =
    .app loopFT (.app (.const 61 []) (.bvar 0)) := rfl
/-- the witness's right-hand side is `m t (F t)`, definitionally. -/
theorem pinLoopWitness_rhs : iotaRhsOf pinLoopWitness =
    .app (.app loopMinTT (.bvar 0)) loopXT := rfl

/-! ## (3) member typings and the `M · ≡ sort 0` β conversions -/

section PinLoopConv
variable {n : Nat}

theorem loopT_mem60 :
    (eraseEnv pinLoopEnvA).members 60 = some (eraseMember pinLoopFamA) := rfl
theorem loopT_mem61 :
    (eraseEnv pinLoopEnvA).members 61 = some (eraseMember pinLoopMkA) := rfl
theorem loopT_mem62 :
    (eraseEnv pinLoopEnvA).members 62 = some pinLoopRecT := rfl

/-- `Loop : Prop` at the erased environment. -/
def loopTyT_ty {Γ : LCtx} : HasTyT (eraseEnv pinLoopEnvA) n Γ loopTyT (.sort .zero) :=
  .const Γ 60 [] (eraseMember pinLoopFamA) loopT_mem60 rfl rfl

/-- `mk : Loop → Loop`. -/
def loopMkT_ty {Γ : LCtx} : HasTyT (eraseEnv pinLoopEnvA) n Γ (.const 61 [])
    (.pi loopTyT loopTyT) :=
  .const Γ 61 [] (eraseMember pinLoopMkA) loopT_mem61 rfl rfl

/-- `t : Loop` in `Γ₀`. -/
def loopVarT_ty : HasTyT (eraseEnv pinLoopEnvA) n loopΓ (.bvar 0) loopTyT :=
  .bvar _ 0 loopTyT rfl

/-- `M l ≡ sort 0`, the motive's β, at any context where the argument's
`Loop`-typing is supplied. -/
def convT_loopMot_beta {Γ : LCtx} {a : Expr Nat}
    (ha : HasTyT (eraseEnv pinLoopEnvA) n Γ a loopTyT) :
    ConvT (eraseEnv pinLoopEnvA) n Γ (.app loopMotTT a) (.sort .zero)
      (.sort (.succ .zero)) :=
  .beta Γ loopTyT (.sort .zero) a (.sort (.succ .zero)) .zero
    loopTyT_ty (.sort _ .zero) ha

/-- `M : Loop → sort 1`. -/
def loopMotT_ty {Γ : LCtx} : HasTyT (eraseEnv pinLoopEnvA) n Γ loopMotTT
    (.pi loopTyT (.sort (.succ .zero))) :=
  .lam Γ loopTyT .zero (.sort .zero) (.sort (.succ .zero)) loopTyT_ty (.sort _ .zero)

/-- `imax 0 0 ≡ 0`, for the `pi`-rule's `sort (imax 0 0)` conclusion. -/
theorem eqN_imax00 : eqN (.imax .zero .zero) .zero := fun _ => rfl
theorem eqN_succ_imax00 : eqN (.succ (.imax .zero .zero)) (.succ .zero) := fun _ => rfl

/-- `sort (imax 0 0) ≡ sort 0` at `sort 1`, via `sorts` + `tyConv`. -/
def convT_sortImax00 {Γ : LCtx} :
    ConvT (eraseEnv pinLoopEnvA) n Γ (.sort (.imax .zero .zero)) (.sort .zero)
      (.sort (.succ .zero)) :=
  .tyConv _ _ _ _ _ _ (.sorts _ _ _ eqN_imax00) (.sorts _ _ _ eqN_succ_imax00)

/-- `ih → ih` (`pinLoopBody`) types at `M (mk l)` in the generic
`[ih : M l, l : Loop] ++ Γ` context — the conv side is `sort (imax 0 0)
≡ M (mk l)` through `sort 0`. -/
def loopBodyTT_ty {Γ : LCtx} :
    HasTyT (eraseEnv pinLoopEnvA) n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      loopBodyTT (.app loopMotTT (.app (.const 61 []) (.bvar 1))) :=
  have hx1 : HasTyT (eraseEnv pinLoopEnvA) n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      (.bvar 1) loopTyT :=
    .bvar _ 1 loopTyT rfl
  have hc1 : ConvT (eraseEnv pinLoopEnvA) n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      (.app loopMotTT (.bvar 1))
      (.sort .zero) (.sort (.succ .zero)) :=
    convT_loopMot_beta hx1
  have hdom : HasTyT (eraseEnv pinLoopEnvA) n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      (.bvar 0) (.sort .zero) :=
    .conv _ _ _ _ (.succ .zero)
      (.bvar _ 0 (.app loopMotTT (.bvar 1)) rfl) hc1
  have hx2 : HasTyT (eraseEnv pinLoopEnvA) n
      (.assumption (.bvar 0) :: .assumption (.app loopMotTT (.bvar 0)) ::
        .assumption loopTyT :: Γ)
      (.bvar 2) loopTyT :=
    .bvar _ 2 loopTyT rfl
  have hc2 : ConvT (eraseEnv pinLoopEnvA) n
      (.assumption (.bvar 0) :: .assumption (.app loopMotTT (.bvar 0)) ::
        .assumption loopTyT :: Γ)
      (.app loopMotTT (.bvar 2))
      (.sort .zero) (.sort (.succ .zero)) :=
    convT_loopMot_beta hx2
  have hcod : HasTyT (eraseEnv pinLoopEnvA) n
      (.assumption (.bvar 0) :: .assumption (.app loopMotTT (.bvar 0)) ::
        .assumption loopTyT :: Γ)
      (.bvar 1) (.sort .zero) :=
    .conv _ _ _ _ (.succ .zero)
      (.bvar _ 1 (.app loopMotTT (.bvar 2)) rfl) hc2
  have hpi : HasTyT (eraseEnv pinLoopEnvA) n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      loopBodyTT
      (.sort (.imax .zero .zero)) :=
    .pi _ (.bvar 0) .zero (.bvar 1) .zero hdom hcod
  have hmk : HasTyT (eraseEnv pinLoopEnvA) n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      (.app (.const 61 []) (.bvar 1))
      loopTyT :=
    .app _ _ _ _ _ loopMkT_ty hx1
  have hmkβ : ConvT (eraseEnv pinLoopEnvA) n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      (.app loopMotTT (.app (.const 61 []) (.bvar 1))) (.sort .zero)
      (.sort (.succ .zero)) :=
    convT_loopMot_beta hmk
  have hconv : ConvT (eraseEnv pinLoopEnvA) n
      (.assumption (.app loopMotTT (.bvar 0)) :: .assumption loopTyT :: Γ)
      (.sort (.imax .zero .zero))
      (.app loopMotTT (.app (.const 61 []) (.bvar 1))) (.sort (.succ .zero)) :=
    .trans _ _ _ _ _ convT_sortImax00 (.symm _ _ _ _ hmkβ)
  .conv _ _ _ _ (.succ .zero) hpi hconv

/-- `λ (ih : M l). ih → ih` types at `Π (ih : M l), M (mk l)` in
`[l : Loop] ++ Γ`. -/
def loopIhLamTT_ty {Γ : LCtx} :
    HasTyT (eraseEnv pinLoopEnvA) n (.assumption loopTyT :: Γ) loopIhLamTT
      (.pi (.app loopMotTT (.bvar 0))
        (.app loopMotTT (.app (.const 61 []) (.bvar 1)))) :=
  .lam _ _ (.succ .zero) _ _
    (.app _ _ _ _ _ loopMotT_ty (.bvar _ 0 loopTyT rfl))
    loopBodyTT_ty

/-- the minor `m` types at `Π (l : Loop), Π (ih : M l), M (mk l)`. -/
def loopMinTT_ty {Γ : LCtx} :
    HasTyT (eraseEnv pinLoopEnvA) n Γ loopMinTT
      (.pi loopTyT (.pi (.app loopMotTT (.bvar 0))
        (.app loopMotTT (.app (.const 61 []) (.bvar 1))))) :=
  .lam Γ loopTyT .zero loopIhLamTT _ loopTyT_ty loopIhLamTT_ty

/-- `F = rec.{1} M m` types at `Π (t : Loop), M t`. -/
def loopFT_ty {Γ : LCtx} :
    HasTyT (eraseEnv pinLoopEnvA) n Γ loopFT
      (.pi loopTyT (.app loopMotTT (.bvar 0))) :=
  have h62 : HasTyT (eraseEnv pinLoopEnvA) n Γ (.const 62 [.succ .zero])
      (instantiateLevels [.succ .zero] pinLoopRecT.mtype) :=
    .const Γ 62 [.succ .zero] pinLoopRecT loopT_mem62 rfl rfl
  .app _ _ _ _ _ (.app _ _ _ _ _ h62 loopMotT_ty) loopMinTT_ty

/-! ## (4) the cyclic conversion, `ConvT` data -/

/-- `t ≡ mk t : Loop`, proof irrelevance at `Loop`. -/
def convT_loopIrr :
    ConvT (eraseEnv pinLoopEnvA) n loopΓ (.bvar 0) (.app (.const 61 []) (.bvar 0))
      loopTyT :=
  .irr _ loopTyT _ _ loopTyT_ty loopVarT_ty
    (.app _ _ _ _ _ loopMkT_ty loopVarT_ty)

/-- `X ≡ F (mk t) : M t` — congruence at the recursor major. -/
def convT_loopMajor :
    ConvT (eraseEnv pinLoopEnvA) n loopΓ loopXT
      (.app loopFT (.app (.const 61 []) (.bvar 0))) (.app loopMotTT (.bvar 0)) :=
  .app _ loopFT loopFT (.bvar 0) (.app (.const 61 []) (.bvar 0)) loopTyT
    (.app loopMotTT (.bvar 0)) (.refl _ _ _ loopFT_ty) convT_loopIrr

/-- `F (mk t) ≡ m t (F t) : M (mk t)` — the ι step, via `pinLoopWitness`. -/
def convT_loopIota :
    ConvT (eraseEnv pinLoopEnvA) n loopΓ (.app loopFT (.app (.const 61 []) (.bvar 0)))
      (.app (.app loopMinTT (.bvar 0)) loopXT)
      (.app loopMotTT (.app (.const 61 []) (.bvar 0))) :=
  .iota _ _ _ _ (.of pinLoopWitness)
    (.app _ _ _ _ _ loopFT_ty (.app _ _ _ _ _ loopMkT_ty loopVarT_ty))
    (.app _ _ _ _ _
      (.app _ _ _ _ _ loopMinTT_ty loopVarT_ty)
      (.app _ _ _ _ _ loopFT_ty loopVarT_ty))

/-- `m t ≡ λ (ih : M t). ih → ih : Π (ih : M t), M (mk t)` — β at the field. -/
def convT_loopMinorBeta :
    ConvT (eraseEnv pinLoopEnvA) n loopΓ (.app loopMinTT (.bvar 0)) loopIhLamTT
      (.pi (.app loopMotTT (.bvar 0))
        (.app loopMotTT (.app (.const 61 []) (.bvar 1)))) :=
  .beta _ loopTyT loopIhLamTT (.bvar 0) _ .zero loopTyT_ty loopIhLamTT_ty
    loopVarT_ty

/-- `m t (F t) ≡ (λ ih. ih → ih) (F t) : M (mk t)`. -/
def convT_loopMinorApp :
    ConvT (eraseEnv pinLoopEnvA) n loopΓ (.app (.app loopMinTT (.bvar 0)) loopXT)
      (.app loopIhLamTT loopXT) (.app loopMotTT (.app (.const 61 []) (.bvar 0))) :=
  .app _ _ _ loopXT loopXT (.app loopMotTT (.bvar 0))
    (.app loopMotTT (.app (.const 61 []) (.bvar 1))) convT_loopMinorBeta
    (.refl _ _ _ (.app _ _ _ _ _ loopFT_ty loopVarT_ty))

/-- `(λ ih. ih → ih) (F t) ≡ X → X : M (mk t)` — β at the recursive call. -/
def convT_loopReductBeta :
    ConvT (eraseEnv pinLoopEnvA) n loopΓ (.app loopIhLamTT loopXT) loopArrowT
      (.app loopMotTT (.app (.const 61 []) (.bvar 0))) :=
  .beta _ (.app loopMotTT (.bvar 0)) loopBodyTT loopXT
    (.app loopMotTT (.app (.const 61 []) (.bvar 1))) (.succ .zero)
    (.app _ _ _ _ _ loopMotT_ty loopVarT_ty)
    (loopBodyTT_ty (Γ := []))
    (.app _ _ _ _ _ loopFT_ty loopVarT_ty)

/-- THE DERIVATION at the typed root: `X ≡ X → X : sort 0` in `Γ₀` —
`pinLoopConv`'s erased shape, `ConvT` data (the `Nonempty` wrap of
`pinLoopConv_erased` is avoided by re-deriving it on the plain side). -/
def convT_pinLoop :
    ConvT (eraseEnv pinLoopEnvA) n loopΓ loopXT loopArrowT (.sort .zero) :=
  have hK : HasTyT (eraseEnv pinLoopEnvA) n loopΓ (.app (.const 61 []) (.bvar 0))
      loopTyT :=
    .app _ _ _ _ _ loopMkT_ty loopVarT_ty
  have hMt : ConvT (eraseEnv pinLoopEnvA) n loopΓ (.app loopMotTT (.bvar 0))
      (.sort .zero) (.sort (.succ .zero)) :=
    convT_loopMot_beta loopVarT_ty
  have hMkt : ConvT (eraseEnv pinLoopEnvA) n loopΓ
      (.app loopMotTT (.app (.const 61 []) (.bvar 0))) (.sort .zero)
      (.sort (.succ .zero)) :=
    convT_loopMot_beta hK
  have c2' : ConvT (eraseEnv pinLoopEnvA) n loopΓ loopXT
      (.app loopFT (.app (.const 61 []) (.bvar 0))) (.sort .zero) :=
    .tyConv _ _ _ _ _ _ convT_loopMajor hMt
  have c34' : ConvT (eraseEnv pinLoopEnvA) n loopΓ
      (.app loopFT (.app (.const 61 []) (.bvar 0))) loopArrowT (.sort .zero) :=
    .tyConv _ _ _ _ _ _
      (.trans _ _ _ _ _ convT_loopIota
        (.trans _ _ _ _ _ convT_loopMinorApp convT_loopReductBeta)) hMkt
  .trans _ _ _ _ _ c2' c34'

/-- the conversion weakened under `x : X` — `x`'s type is its own arrow. -/
def convT_pinLoop_wk :
    ConvT (eraseEnv pinLoopEnvA) n (.assumption loopXT :: loopΓ)
      (.app loopFT (.bvar 1))
      (.pi (.app loopFT (.bvar 1)) (.app loopFT (.bvar 2))) (.sort .zero) :=
  convTWeaken (.assumption loopXT) (envClosed_of_envWfT pinLoopEraseWfT)
    (c := 0) convT_pinLoop

/-! ## (5) `Ω_X` typed at `X` -/

/-- `x : lift 0 1 X`, i.e. `x : F t` at `[x : X, t : Loop]`. -/
def omegaVarT_ty :
    HasTyT (eraseEnv pinLoopEnvA) n (.assumption loopXT :: loopΓ) (.bvar 0)
      (.app loopFT (.bvar 1)) :=
  .bvar _ 0 (.app loopFT (.bvar 1)) rfl

/-- `x x : F t` — `x`'s type converts to its own arrow. -/
def omegaBodyT_ty :
    HasTyT (eraseEnv pinLoopEnvA) n (.assumption loopXT :: loopΓ)
      (.app (.bvar 0) (.bvar 0)) (.app loopFT (.bvar 1)) :=
  .app _ _ _ _ _
    (.conv _ _ _ _ .zero omegaVarT_ty convT_pinLoop_wk) omegaVarT_ty

/-- `λx:X. x x : X → X` at `Γ₀`. -/
def omegaLamT_ty :
    HasTyT (eraseEnv pinLoopEnvA) n loopΓ (.lam loopXT (.app (.bvar 0) (.bvar 0)))
      loopArrowT :=
  .lam _ _ .zero _ _
    (.conv _ _ _ _ (.succ .zero)
      (.app _ _ _ _ _ loopFT_ty loopVarT_ty)
      (convT_loopMot_beta loopVarT_ty))
    omegaBodyT_ty

/-- `λx:X. x x : X` — the arrow folds back. -/
def omegaLamT_tyX :
    HasTyT (eraseEnv pinLoopEnvA) n loopΓ (.lam loopXT (.app (.bvar 0) (.bvar 0)))
      loopXT :=
  .conv _ _ _ _ .zero omegaLamT_ty (.symm _ _ _ _ convT_pinLoop)

/-- THE TYPED ω: `Ω_X : X` at the erased Loop environment. -/
def omegaT_pinLoop_typed {n : Nat} :
    HasTyT (eraseEnv pinLoopEnvA) n loopΓ omegaXT loopXT :=
  .app _ _ _ _ _ omegaLamT_ty omegaLamT_tyX

end PinLoopConv

/-! ## (6) the `OmXT` invariant — no `ParRedStar` reduct of `Ω_X` is
`ParRed`-normal -/

namespace NormalizingFalsePinLoop

open NormalizingFalse (headSym recCall_ne_of_headSym)

/-- the ω-body `x x`. -/
def omxBody : Expr Nat := .app (.bvar 0) (.bvar 0)

/-- Reachable-Ω invariant: binary `app`-trees whose leaves are
`x x`-bodied λs (any domain — the domain may reduce). Every
`ParRedStar`-reachable term from `Ω_X` is a nonempty such tree. -/
inductive OmXT : Expr Nat → Prop
  | lam {A : Expr Nat} : OmXT (.lam A omxBody)
  | node {F X : Expr Nat} : OmXT F → OmXT X → OmXT (.app F X)

theorem omXT_lam_inv {A b : Expr Nat} (h : OmXT (.lam A b)) : b = omxBody := by
  cases h; rfl

theorem omXT_headSym {t : Expr Nat} (h : OmXT t) : headSym t = false := by
  induction h with
  | lam => rfl
  | node _ _ ihF _ => exact ihF

/-- let-free contexts stay let-free under `.assumption` extension. -/
theorem noLet_cons {Γ : LCtx} {A' : Expr Nat}
    (hz : ∀ i A v, Γ.get? i ≠ some (.letBinding A v)) :
    ∀ i A v, (.assumption A' :: Γ).get? i ≠ some (.letBinding A v) := by
  intro i A v
  cases i with
  | zero => exact fun h => LocalDecl.noConfusion (Option.some.inj h)
  | succ i => exact hz i A v

/-- in a let-free context a `bvar` is a `ParRed`-normal form. -/
theorem parRed_bvar_nf {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat}
    {t : Expr Nat}
    (hz : ∀ i A v, Γ.get? i ≠ some (.letBinding A v))
    (h : ParRed E n Γ (.bvar i) t) : t = .bvar i := by
  rcases parRed_bvar h rfl with heq | ⟨A, v, v', hget, _, _⟩
  · exact heq
  · exact absurd hget (hz i A v)

/-- `x x` in a let-free context reduces only to itself. -/
theorem parRed_omxBody {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hz : ∀ i A v, Γ.get? i ≠ some (.letBinding A v))
    {t : Expr Nat} (h : ParRed E n Γ omxBody t) : t = omxBody := by
  rcases parRed_app h rfl with ⟨f', x', heq, hf, hx⟩ | inr
  · subst heq
    obtain rfl := parRed_bvar_nf hz hf
    obtain rfl := parRed_bvar_nf hz hx
    rfl
  · rcases inr with ⟨A, body, A', body', x', hf_eq, _, _, _, _⟩ | iota
    · exact Expr.noConfusion hf_eq
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hEqL, _⟩ := iota
      exact (recCall_ne_of_headSym (t := omxBody) rfl hEqL).elim

/-- one `ParRed` step preserves the invariant. -/
theorem omXT_step {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hz : ∀ i A v, Γ.get? i ≠ some (.letBinding A v))
    {N N' : Expr Nat} (h : ParRed E n Γ N N') (hN : OmXT N) : OmXT N' := by
  induction hN generalizing N' with
  | lam =>
      obtain ⟨A', b', heq, _, hb⟩ := parRed_lam h rfl
      subst heq
      have hb' := parRed_omxBody (noLet_cons hz) hb
      subst hb'
      exact .lam
  | node hF hX ihF ihX =>
      rcases parRed_app h rfl with ⟨f', x', heq, hf, hx⟩ | inr
      · subst heq
        exact .node (ihF hf) (ihX hx)
      · rcases inr with ⟨A, body, A', body', x', hf_eq, _, hb, hx, he⟩ | iota
        · have hbe : body = omxBody := omXT_lam_inv (hf_eq ▸ hF)
          subst hf_eq hbe
          have hb' := parRed_omxBody (noLet_cons hz) hb
          subst hb' he
          have harg := ihX hx
          exact .node harg harg
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hEqL, _⟩ := iota
          exact (recCall_ne_of_headSym
            (omXT_headSym (.node hF hX)) hEqL).elim

/-- a `ParRed`-reachable `app` stays `app`-headed and keeps the
invariant (the `omTree_step_app` shape). -/
theorem omXT_step_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hz : ∀ i A v, Γ.get? i ≠ some (.letBinding A v))
    {F X N' : Expr Nat}
    (h : ParRed E n Γ (.app F X) N') (hN : OmXT (.app F X)) :
    ∃ F' X', N' = .app F' X' ∧ OmXT F' ∧ OmXT X' := by
  cases hN with
  | node hF hX =>
      rcases parRed_app h rfl with ⟨f', x', heq, hf, hx⟩ | inr
      · subst heq
        exact ⟨_, _, rfl, omXT_step hz hf hF, omXT_step hz hx hX⟩
      · rcases inr with ⟨A, body, A', body', x', hf_eq, _, hb, hx, he⟩ | iota
        · have hbe : body = omxBody := omXT_lam_inv (hf_eq ▸ hF)
          subst hf_eq hbe
          have hb' := parRed_omxBody (noLet_cons hz) hb
          subst hb'
          have harg := omXT_step hz hx hX
          exact ⟨_, _, show N' = .app x' x' from he, harg, harg⟩
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hEqL, _⟩ := iota
          exact (recCall_ne_of_headSym
            (omXT_headSym (.node hF hX)) hEqL).elim

/-- the invariant transported forward along `ParRedStar`. -/
theorem omXT_star {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hz : ∀ i A v, Γ.get? i ≠ some (.letBinding A v))
    {a b : Expr Nat} (h : ParRedStar E n Γ a b) :
    OmXT a → (∃ F X, a = .app F X) →
    OmXT b ∧ ∃ F X, b = .app F X := by
  induction h with
  | refl => intro ha haa; exact ⟨ha, haa⟩
  | tail hstep _ ih =>
      intro ha haa
      obtain ⟨F, X, heq⟩ := haa
      subst heq
      obtain ⟨F', X', hN', hF', hX'⟩ := omXT_step_app hz hstep ha
      subst hN'
      exact ih (.node hF' hX') ⟨_, _, rfl⟩

/-- every nonempty `OmXT` tree has a `ParRed` step: inside a node by
induction, at a λ-leaf head by β. -/
theorem omXT_stepBad {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {F X : Expr Nat} (hF : OmXT F) (hX : OmXT X) :
    Nonempty (Σ' (N' : Expr Nat), ParRed E n Γ (.app F X) N') := by
  induction hF generalizing X with
  | lam =>
      exact ⟨⟨.app X X,
        .beta _ _ _ _ _ _ _ (.refl _ _) (.refl _ _) (.refl _ X)⟩⟩
  | node hF1 hF2 ih1 _ =>
      obtain ⟨w⟩ := ih1 hF2
      exact ⟨⟨.app w.1 X, .app _ _ _ _ _ w.2 (.refl _ X)⟩⟩

/-- `Ω_X`'s starting tree. -/
theorem omXT_omega : OmXT omegaXT := .node .lam .lam

/-- the Loop context has no `letBinding` slots. -/
theorem loopΓ_noLet : ∀ i A v, (loopΓ).get? i ≠ some (.letBinding A v) := by
  intro i A v
  cases i with
  | zero => exact fun h => LocalDecl.noConfusion (Option.some.inj h)
  | succ i => exact fun h => Option.noConfusion h

/-- THE REFUTATION at the typed judgment: no `ParRedStar` reduct of
`Ω_X` over `eraseEnv pinLoopEnvA` in `Γ₀` is `ParRed`-normal — the
invariant survives every step and every nonempty tree has a step. -/
theorem normalizingT_false_pinLoop {n : Nat} {N : Expr Nat}
    (h : ParRedStar (eraseEnv pinLoopEnvA) n loopΓ omegaXT N) :
    Nonempty (Σ' (M : Expr Nat), ParRed (eraseEnv pinLoopEnvA) n loopΓ N M) := by
  obtain ⟨hOm, F, X, hNX⟩ := omXT_star loopΓ_noLet h omXT_omega ⟨_, _, rfl⟩
  subst hNX
  cases hOm with
  | node hF hX => exact omXT_stepBad hF hX

end NormalizingFalsePinLoop

#print axioms pinLoopWitness
#print axioms convT_pinLoop
#print axioms omegaT_pinLoop_typed
#print axioms NormalizingFalsePinLoop.normalizingT_false_pinLoop

end Rcic.Declarative
