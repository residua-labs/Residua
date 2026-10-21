import rcic.RcicDeclarative

/-!
# ds-refute (item a) — Abel–Coquand impredicative self-application is well-typed in RCIC

The refutation search (`research/rcic/refute/S0_PIROW_SEARCH.md` §3e) concludes that at an
**admitted** environment the only genuinely new ingredient of the Abel–Coquand
normalization-failure construction (arXiv:1911.08174, LMCS 16(2):14 2020) — beyond the
already-pinned `Eq` K-ι cast of `RcicPinEqIotaStarK` (`pinEq_convK`, `pinEq_gateNotMet`) —
is the *impredicative self-application*

      ⊥ = Π (A : Prop). A        ⊤ = ⊥ → ⊥        δ : ⊤,   δ z = z ⊤ z .

This module pins exactly that: `δ : ⊤` is derivable in the **empty** environment, using
only `sort`/`pi`/`lam`/`app`/`bvar` and the `eqN` sort bridge (no environment member, no
recursor, no `irr`).  It is the load-bearing term that turns the (already-pinned) equal-Prop
cast `cast ⊤ ⊤ e δ ≡ δ` into the self-loop `Ω h ⟶ Ω h`.

This is **not** a Π-injectivity counterexample — the types involved (`⊥`, `⊤`) are
impredicative Πs whose domain is `Prop = sort 0`, and the cast transports *proofs* between
Props at the same sort.  It pins the "Abel–Coquand refutes normalization" half of the
ruling, and documents (in the composition note below) that no domain swap is produced.
`closure_claim` stays 0.
-/

namespace Rcic.Declarative

namespace AbelCoquand

/-- `⊥ = Π (A : Prop). A` — impredicative absurdity (a Prop up to `eqN`). -/
def bot : Expr Nat := .pi (.sort .zero) (.bvar 0)

/-- `⊤ = ⊥ → ⊥`. -/
def top : Expr Nat := .pi bot bot

/-- `δ : ⊤`, `δ z = z ⊤ z` — the impredicative self-application. -/
def delta : Expr Nat := .lam bot (.app (.app (.bvar 0) top) (.bvar 0))

/-- the sort of `⊥`: `imax (succ 0) 0`. -/
abbrev uBot : Level := .imax (.succ .zero) .zero

/-- the sort of `⊤`. -/
abbrev uTop : Level := .imax uBot uBot

/-- `imax (succ 0) 0 =ₙ 0` — impredicativity of the empty Π (domain `Prop`). -/
theorem eqN_uBot_zero : eqN uBot .zero := by
  intro ρ
  rfl

/-- `imax uBot uBot =ₙ 0`. -/
theorem eqN_uTop_zero : eqN uTop .zero := by
  intro ρ
  rfl

/-- `⊥ : sort uBot` in any context. -/
def botHasTyAt (n : Nat) (Γ : LCtx) : HasTyT emptyEnv n Γ bot (.sort uBot) :=
  HasTyT.pi Γ (.sort .zero) (.succ .zero) (.bvar 0) .zero
    (HasTyT.sort Γ .zero)
    (HasTyT.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)

/-- `⊥ : sort 0` (Prop) in any context — via the `eqN` sort bridge. -/
def botIsPropAt (n : Nat) (Γ : LCtx) : HasTyT emptyEnv n Γ bot (.sort .zero) :=
  HasTyT.conv Γ bot (.sort uBot) (.sort .zero) (.succ uBot)
    (botHasTyAt n Γ)
    (ConvT.sorts Γ uBot .zero eqN_uBot_zero)

/-- `⊤ : sort uTop` in any context. -/
def topHasTyAt (n : Nat) (Γ : LCtx) : HasTyT emptyEnv n Γ top (.sort uTop) :=
  HasTyT.pi Γ bot uBot bot uBot (botHasTyAt n Γ) (botHasTyAt n (.assumption bot :: Γ))

/-- `⊤ : sort 0` (Prop) in any context. -/
def topIsPropAt (n : Nat) (Γ : LCtx) : HasTyT emptyEnv n Γ top (.sort .zero) :=
  HasTyT.conv Γ top (.sort uTop) (.sort .zero) (.succ uTop)
    (topHasTyAt n Γ)
    (ConvT.sorts Γ uTop .zero eqN_uTop_zero)

/-- In `[z : ⊥]`, `z : ⊥` (`= z : Π A : Prop. A`). -/
def zTy (n : Nat) : HasTyT emptyEnv n (.assumption bot :: []) (.bvar 0) bot :=
  HasTyT.bvar (.assumption bot :: []) 0 bot rfl

/-- In `[z : ⊥]`, `z ⊤ : ⊤` — applying `z : Π A : Prop. A` to the Prop `⊤`. -/
def zTopTy (n : Nat) :
    HasTyT emptyEnv n (.assumption bot :: []) (.app (.bvar 0) top) top :=
  HasTyT.app (.assumption bot :: []) (.bvar 0) top (.sort .zero) (.bvar 0)
    (zTy n) (topIsPropAt n (.assumption bot :: []))

/-- In `[z : ⊥]`, `(z ⊤) z : ⊥` — applying `z ⊤ : ⊥ → ⊥` to `z : ⊥`. -/
def deltaBodyTy (n : Nat) :
    HasTyT emptyEnv n (.assumption bot :: [])
      (.app (.app (.bvar 0) top) (.bvar 0)) bot :=
  HasTyT.app (.assumption bot :: []) (.app (.bvar 0) top) (.bvar 0) bot bot
    (zTopTy n) (zTy n)

/-- **`δ : ⊤`** — the impredicative self-application is well-typed in the empty
    environment (no members, no recursor, no `irr`).  The load-bearing new ingredient of
    the Abel–Coquand construction. -/
def deltaHasTy (n : Nat) : HasTyT emptyEnv n [] delta top :=
  HasTyT.lam [] bot uBot (.app (.app (.bvar 0) top) (.bvar 0)) bot
    (botHasTyAt n []) (deltaBodyTy n)

/-!
### Composition note (not mechanized here): the self-loop, and why no domain swap

Under the "lie" context `Γ = [h : Π A B : Prop. A = B]`, the cast
`cast := Eq.rec (sort 0) ⊤ (λ b p. b)` (admitted at `eqEnvT`, `RcicPinEqEraseWf`) reduces
at equal Props by `irr`+`app`+`ι` — the already-pinned `pinEq_convK`
(`RcicPinEqIotaStarK.lean:478`).  Chaining that cast reduction with `δ` above gives the
Abel–Coquand self-loop

      Ω h = δ (ω h) ⟶ ω h ⊤ (ω h) = cast ⊤ ⊤ (h ⊤ ⊤) δ (ω h) ⟶ δ (ω h) = Ω h,

i.e. non-normalization is real in RCIC at an admitted environment.  But every type in the
loop is an impredicative Π with domain `Prop = sort 0`, and the cast reduces only when its
two Prop *endpoints* are definitionally equal (`⊤ = ⊤`) — so no `ConvT (Π A B) (Π A' B')
(sort u)` with a *changed* domain is produced.  Non-normalization is term-level and
compatible with Π-injectivity.  See `research/rcic/refute/S0_PIROW_SEARCH.md` §3e.
-/

end AbelCoquand

#check AbelCoquand.deltaHasTy
#check AbelCoquand.botIsPropAt
#check AbelCoquand.topIsPropAt
#check AbelCoquand.eqN_uBot_zero
#check AbelCoquand.eqN_uTop_zero

end Rcic.Declarative
