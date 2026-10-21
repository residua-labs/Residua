import rcic.RcicPinEqIotaStarK

/-! `RcicPinEqStuckTy` — the check-#9 type-level K-stuck pin
(cc ruling on #6293, 03:40Z; r1b).

The "fire case" of T3″'s K-neutral disjunct concerns
`T := Eq.rec.{1} α a (λ _ _. Sort 0) (Π P. P) b q`, typed at `Sort 0`
under `q : Eq α a b` with `b` a distinct bvar — the type-level image of
the standalone `RcicTmEqNoGo` obstruction.

Two results:

* `eqKFire_ty : HasTyT eqEnvT 0 eqNeutCtx eqKTy (.sort .zero)` — `T` is
  well-typed. The motive `λ _ _. Sort 0` is the constant motive, the
  minor `Π (P : Sort 0). P` is impredicative, and the codomain
  `M b q` collapses to `Sort 0` by two β steps (`eqKConvMain`).

* `eqKFire_headed` — every `ParRedStar` reduct of `T` stays
  `const 65`-headed: `parRed_recSpine_opaque` keeps the opaque spine,
  and pointwise argument reduction can never mint a `const`-headed
  major (`eqKSafe_args` — bvar/lam/pi are shape-stable at a no-let
  context). So the major `b` never becomes `refl`-headed, no ι★K step
  ever fires, and the case is reachable ONLY through conversion
  evidence — precisely the direction `RcicTmEqNoGo` denies.

`closure_claim` stays 0. -/

namespace Rcic

open Rcic.Declarative

/-! ## the fixture -/

/-- the constant-`Sort 0` motive `λ (x : α) (_ : Eq α a x). Sort 0` at
`eqNeutCtx = [q : Eq α a b, b, m, M, a, α]` scope (α@5, a@4). -/
def eqKMot : Expr Nat :=
  .lam (.bvar 5)
    (.lam (foldApps (.const 63 []) [.bvar 6, .bvar 5, .bvar 0])
      (.sort .zero))

/-- the impredicative minor `Π (P : Sort 0). P`. -/
def eqKMin : Expr Nat := .pi (.sort .zero) (.bvar 0)

/-- the spine `[α, a, M, m, b, q]` of `T`. -/
def eqKSpine : List (Expr Nat) :=
  [.bvar 5, .bvar 4, eqKMot, eqKMin, .bvar 1, .bvar 0]

/-- `T := Eq.rec.{1} α a (λ _ _. Sort 0) (Π P. P) b q`. -/
def eqKTy : Expr Nat := foldApps (.const 65 [.succ .zero]) eqKSpine

/-- `Eq α a a` at `eqNeutCtx`. -/
def eqKEqAA : Expr Nat := foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 4]

/-- `Eq α a b` at `eqNeutCtx` — `q`'s stored type verbatim
(`lift 0 1 eqNeutPTy`). -/
def eqKEqAB : Expr Nat := foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 1]

/-- `refl α a` at `eqNeutCtx`. -/
def eqKReflApp : Expr Nat := foldApps (.const 64 []) [.bvar 5, .bvar 4]

/-! ## context leaves -/

def eqKTyα : HasTyT eqEnvT 0 eqNeutCtx (.bvar 5) (.sort (.succ .zero)) :=
  HasTyT.bvar _ 5 _ rfl

def eqKTya : HasTyT eqEnvT 0 eqNeutCtx (.bvar 4) (.bvar 5) :=
  HasTyT.bvar _ 4 _ rfl

def eqKTyb : HasTyT eqEnvT 0 eqNeutCtx (.bvar 1) (.bvar 5) :=
  HasTyT.bvar _ 1 _ rfl

/-- `q : Eq α a b` by context lookup. -/
def eqKTyq : HasTyT eqEnvT 0 eqNeutCtx (.bvar 0) eqKEqAB :=
  HasTyT.bvar _ 0 _ rfl

/-! ## motive/minor/family typings -/

/-- `[x : α] :: eqNeutCtx`. -/
private def eqKCtxX : LCtx := .assumption (.bvar 5) :: eqNeutCtx

private def eqKTyXα : HasTyT eqEnvT 0 eqKCtxX (.bvar 6) (.sort (.succ .zero)) :=
  HasTyT.bvar _ 6 _ rfl

private def eqKTyXa : HasTyT eqEnvT 0 eqKCtxX (.bvar 5) (.bvar 6) :=
  HasTyT.bvar _ 5 _ rfl

private def eqKTyXx : HasTyT eqEnvT 0 eqKCtxX (.bvar 0) (.bvar 6) :=
  HasTyT.bvar _ 0 _ rfl

/-- `Eq α a x : Sort 0` under `[x : α]`. -/
private def eqKTyEqX : HasTyT eqEnvT 0 eqKCtxX
    (foldApps (.const 63 []) [.bvar 6, .bvar 5, .bvar 0]) (.sort .zero) :=
  HasTyT.app _ _ _ _ _
    (HasTyT.app _ _ _ _ _
      (HasTyT.app _ _ _ _ _
        (HasTyT.const _ 63 [] eqFamT rfl rfl rfl) eqKTyXα)
      eqKTyXa)
    eqKTyXx

/-- `λ (_ : Eq α a x). Sort 0 : Eq α a x → Sort 1` under `[x : α]`. -/
private def eqKTyInnerLam : HasTyT eqEnvT 0 eqKCtxX
    (.lam (foldApps (.const 63 []) [.bvar 6, .bvar 5, .bvar 0]) (.sort .zero))
    (.pi (foldApps (.const 63 []) [.bvar 6, .bvar 5, .bvar 0]) (.sort (.succ .zero))) :=
  HasTyT.lam _ _ _ _ _ eqKTyEqX (HasTyT.sort _ _)

/-- the motive `λ (x : α) (_ : Eq α a x). Sort 0` :
    `Π (x : α), Eq α a x → Sort 1`. -/
def eqKMotTy : HasTyT eqEnvT 0 eqNeutCtx eqKMot
    (.pi (.bvar 5)
      (.pi (foldApps (.const 63 []) [.bvar 6, .bvar 5, .bvar 0])
        (.sort (.succ .zero)))) :=
  HasTyT.lam _ _ _ _ _ eqKTyα eqKTyInnerLam

/-- `[P : Sort 0] :: eqNeutCtx`. -/
private def eqKCtxP : LCtx := .assumption (.sort .zero) :: eqNeutCtx

private def eqKTyP : HasTyT eqEnvT 0 eqKCtxP (.bvar 0) (.sort .zero) :=
  HasTyT.bvar _ 0 _ rfl

/-- `Π (P : Sort 0). P : Sort (imax 1 0)`. -/
def eqKMinTy : HasTyT eqEnvT 0 eqNeutCtx eqKMin
    (.sort (.imax (.succ .zero) .zero)) :=
  HasTyT.pi _ _ _ _ _ (HasTyT.sort _ _) eqKTyP

/-- `refl α a : Eq α a a`. -/
def eqKReflTy : HasTyT eqEnvT 0 eqNeutCtx eqKReflApp eqKEqAA :=
  HasTyT.app _ _ _ _ _
    (HasTyT.app _ _ _ _ _
      (HasTyT.const _ 64 [] eqReflT rfl rfl rfl) eqKTyα)
    eqKTya

/-- `Eq α a a : Sort 0`. -/
def eqKEqAATy : HasTyT eqEnvT 0 eqNeutCtx eqKEqAA (.sort .zero) :=
  HasTyT.app _ _ _ _ _
    (HasTyT.app _ _ _ _ _
      (HasTyT.app _ _ _ _ _
        (HasTyT.const _ 63 [] eqFamT rfl rfl rfl) eqKTyα)
      eqKTya)
    eqKTya

/-- `Eq α a b : Sort 0`. -/
def eqKEqABTy : HasTyT eqEnvT 0 eqNeutCtx eqKEqAB (.sort .zero) :=
  HasTyT.app _ _ _ _ _
    (HasTyT.app _ _ _ _ _
      (HasTyT.app _ _ _ _ _
        (HasTyT.const _ 63 [] eqFamT rfl rfl rfl) eqKTyα)
      eqKTya)
    eqKTyb

/-! ## the β-chain `M x e ≡ Sort 0` -/

private def eqN_imax10 : eqN (.imax (.succ .zero) .zero) .zero := fun _ => rfl

private def eqN_succImax10 : eqN (.succ (.imax (.succ .zero) .zero)) (.succ .zero) :=
  fun _ => rfl

/-- `Sort (imax 1 0) ≡ Sort 0` at `Sort 1`. -/
private def eqKConvImax : ConvT eqEnvT 0 eqNeutCtx
    (.sort (.imax (.succ .zero) .zero)) (.sort .zero) (.sort (.succ .zero)) :=
  ConvT.tyConv _ _ _ _ _ _
    (ConvT.sorts _ _ _ eqN_imax10)
    (ConvT.sorts _ _ _ eqN_succImax10)

/-- outer β at `b`: `(λx. λ_. Sort 0) b ≡ λ (_ : Eq α a b). Sort 0`. -/
private def eqKBetaB : ConvT eqEnvT 0 eqNeutCtx (.app eqKMot (.bvar 1))
    (.lam eqKEqAB (.sort .zero)) (.pi eqKEqAB (.sort (.succ .zero))) :=
  ConvT.beta _ _ _ _ _ _ eqKTyα eqKTyInnerLam eqKTyb

/-- outer β at `a`. -/
private def eqKBetaA : ConvT eqEnvT 0 eqNeutCtx (.app eqKMot (.bvar 4))
    (.lam eqKEqAA (.sort .zero)) (.pi eqKEqAA (.sort (.succ .zero))) :=
  ConvT.beta _ _ _ _ _ _ eqKTyα eqKTyInnerLam eqKTya

/-- inner β at `q`: `(λ (_ : Eq α a b). Sort 0) q ≡ Sort 0`. -/
private def eqKBetaBq : ConvT eqEnvT 0 eqNeutCtx
    (.app (.lam eqKEqAB (.sort .zero)) (.bvar 0)) (.sort .zero)
    (.sort (.succ .zero)) :=
  ConvT.beta _ _ _ _ _ _ eqKEqABTy (HasTyT.sort _ _) eqKTyq

/-- inner β at `refl α a`. -/
private def eqKBetaAr : ConvT eqEnvT 0 eqNeutCtx
    (.app (.lam eqKEqAA (.sort .zero)) eqKReflApp) (.sort .zero)
    (.sort (.succ .zero)) :=
  ConvT.beta _ _ _ _ _ _ eqKEqAATy (HasTyT.sort _ _) eqKReflTy

/-- `M b q ≡ Sort 0` — the codomain collapse. -/
def eqKConvMain : ConvT eqEnvT 0 eqNeutCtx
    (.app (.app eqKMot (.bvar 1)) (.bvar 0)) (.sort .zero)
    (.sort (.succ .zero)) :=
  ConvT.trans _ _ _ _ _
    (ConvT.app _ _ _ _ _ _ _ eqKBetaB (ConvT.refl _ _ _ eqKTyq))
    eqKBetaBq

/-- `M a (refl α a) ≡ Sort 0`. -/
def eqKConvMinor : ConvT eqEnvT 0 eqNeutCtx
    (.app (.app eqKMot (.bvar 4)) eqKReflApp) (.sort .zero)
    (.sort (.succ .zero)) :=
  ConvT.trans _ _ _ _ _
    (ConvT.app _ _ _ _ _ _ _ eqKBetaA (ConvT.refl _ _ _ eqKReflTy))
    eqKBetaAr

/-- the minor `Π P. P` typed at its expected domain
`M a (refl α a)` via `imax 1 0 ≡ 0` + the collapsed motive. -/
def eqKMinConv : HasTyT eqEnvT 0 eqNeutCtx eqKMin
    (.app (.app eqKMot (.bvar 4)) eqKReflApp) :=
  HasTyT.conv _ _ _ _ _ eqKMinTy
    (ConvT.trans _ _ _ _ _ eqKConvImax (ConvT.symm _ _ _ _ eqKConvMinor))

/-! ## `T`'s typing and the head pin -/

private def eqKRec0 : HasTyT eqEnvT 0 eqNeutCtx (.const 65 [.succ .zero])
    (instantiateLevels [.succ .zero] eqRecT.mtype) :=
  HasTyT.const _ 65 [.succ .zero] eqRecT rfl rfl rfl

private def eqKRec1 := HasTyT.app _ _ _ _ _ eqKRec0 eqKTyα
private def eqKRec2 := HasTyT.app _ _ _ _ _ eqKRec1 eqKTya
private def eqKRec3 := HasTyT.app _ _ _ _ _ eqKRec2 eqKMotTy
private def eqKRec4 := HasTyT.app _ _ _ _ _ eqKRec3 eqKMinConv
private def eqKRec5 := HasTyT.app _ _ _ _ _ eqKRec4 eqKTyb
private def eqKRec6 := HasTyT.app _ _ _ _ _ eqKRec5 eqKTyq

/-- `HasTyT eqEnvT 0 eqNeutCtx T (sort 0)`: the K-stuck type IS a type. -/
def eqKFire_ty : HasTyT eqEnvT 0 eqNeutCtx eqKTy (.sort .zero) :=
  HasTyT.conv _ _ _ _ _ eqKRec6 eqKConvMain

/-- arguments that can never mint a `const`-headed spine: a bvar at a
no-let context, or any `lam`/`pi` — none of them is `foldApps (const ..)`. -/
inductive EqKSafe : Expr Nat → Prop where
  | bvar (i : Nat) : EqKSafe (.bvar i)
  | lam (A b : Expr Nat) : EqKSafe (.lam A b)
  | pi (A B : Expr Nat) : EqKSafe (.pi A B)

def eqKSafe_hnf {x : Expr Nat} (h : EqKSafe x) (r : Nat) (ls : List Level)
    (ys : List (Expr Nat)) : foldApps (.const r ls) ys ≠ x := by
  cases h with
  | bvar i => exact EqPin.foldApps_const_ne_bvar ys
  | lam A b => exact foldApps_const_ne_lam ys
  | pi A B =>
      exact (EqPin.foldApps_const_ne_of_spine (e := .pi A B) rfl
        (fun _ _ he => Expr.noConfusion he)).symm

/-- `EqKSafe` survives one `ParRed` step (bvars are normal at `eqNeutCtx`,
`lam`/`pi` keep their head — `cases` cannot eliminate the `iotaSpine`
arm's rigid `foldApps`-const source, so the arm-local inversions
`parRed_lam`/`parRed_pi` are used instead). -/
theorem eqKSafe_parRed {e t : Expr Nat} (h : ParRed eqEnvT n eqNeutCtx e t)
    (hs : EqKSafe e) : EqKSafe t := by
  cases hs with
  | bvar i =>
      have ht := EqPin.parRed_bvar_normal (eqNeutCtx_noLet i) h rfl
      rw [ht]; exact .bvar i
  | lam A b =>
      obtain ⟨A', b', ht, -, -⟩ := parRed_lam h rfl
      subst ht; exact .lam _ _
  | pi A B =>
      obtain ⟨A', B', ht, -, -⟩ := parRed_pi h rfl
      subst ht; exact .pi _ _

/-- pointwise: `EqKSafe` survives `ParRedArgs` (equation-style — the
mutual eliminator cannot be driven by `induction`). -/
theorem eqKSafe_args {xs ys : List (Expr Nat)}
    (hs : ∀ x ∈ xs, EqKSafe x) :
    ParRedArgs eqEnvT n eqNeutCtx xs ys → ∀ y ∈ ys, EqKSafe y
  | .nil _ => fun y hy => nomatch hy
  | .cons h t => fun y hy => by
      cases hy with
      | head => exact eqKSafe_parRed h (hs _ (List.mem_cons_self _ _))
      | tail _ hm =>
          exact eqKSafe_args (fun x hx => hs x (List.mem_cons_of_mem _ hx))
            t y hm

/-- `eqKSpine`'s arguments are all `EqKSafe`. -/
theorem eqKSpine_safe : ∀ x ∈ eqKSpine, EqKSafe x := by
  intro x hx
  simp only [eqKSpine, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .bvar 5
  · exact .bvar 4
  · exact .lam _ _
  · exact .pi _ _
  · exact .bvar 1
  · exact .bvar 0

/-- a `const 65`-headed spine with `EqKSafe` arguments stays
`const 65`-headed with `EqKSafe` arguments, under `ParRedStar`. -/
theorem eqKStar_headed {n : Nat} {a c : Expr Nat}
    (hR : ParRedStar eqEnvT n eqNeutCtx a c) {ls : List Level}
    {xs : List (Expr Nat)} (ha : a = foldApps (.const 65 ls) xs)
    (hsafe : ∀ x ∈ xs, EqKSafe x) :
    ∃ (ls' : List Level) (xs' : List (Expr Nat)),
      c = foldApps (.const 65 ls') xs' ∧ ∀ x ∈ xs', EqKSafe x := by
  revert ha hsafe
  induction hR generalizing ls xs with
  | refl => intro ha hsafe; exact ⟨_, _, ha, hsafe⟩
  | tail h s ih =>
      intro ha hsafe
      obtain ⟨ls', xs', hb, hargs⟩ :=
        EqPin.parRed_recSpine_opaque (E := eqEnvT) eqRecT rfl rfl h xs ha
          (fun x hx => eqKSafe_hnf (hsafe x hx))
      exact ih hb (eqKSafe_args hsafe hargs)

/-- THE PIN: every `ParRedStar` reduct of `T` is `const 65`-headed —
the K-major `b` never reaches `refl`-head, so no ι★K step ever fires. -/
theorem eqKFire_headed {n : Nat} {c : Expr Nat}
    (hR : ParRedStar eqEnvT n eqNeutCtx eqKTy c) :
    ∃ (ls' : List Level) (xs' : List (Expr Nat)),
      c = foldApps (.const 65 ls') xs' :=
  let ⟨ls', xs', hc, _⟩ := eqKStar_headed hR rfl eqKSpine_safe
  ⟨ls', xs', hc⟩

#print axioms eqKFire_ty
#print axioms eqKFire_headed

end Rcic
