import rcic.RcicF8OM1
import rcic.RcicF8XValley
import rcic.RcicAbelCoquandPin

/-!
# `RcicF8UProcX` — additive U whose app arm takes an explicit partial X

cc ruling on #7167 (2026-10-15): U's app arm waits for X (B4b). This module
is the additive sibling, the same shape as the partial suppliers already
landed for J/D/U. `XProcP` is `XProc` returning `Option` — the shape of
`xValley`, not a total X. `UProcX` sends every non-`app` subject through
the landed `UProcP.ofTotal`. The `app` arm calls the X supplier on a Π
chain built by the landed intro-spine `introU` (the function is on that
spine in the sealed fixture). A function off that spine is a refusal
(`none`): the mutual closure that would supply X from piRow's own
recursion under the lex measure is packaging item 8 and is not in this
file. `introU` is not edited. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat}

/-- Partial X: a Π-chain in, component chains out, or a refusal.
`XProc` is the total sibling (`RcicF8OM23`); this is the `Option` shape
`xValley` already returns. -/
abbrev XProcP (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {A B A' B' : Expr Nat},
    EvTc R Γ (.pi A B) (.pi A' B') →
    Option (EvTc R Γ A A' × EvTc R (.assumption A :: Γ) B B')

/-! The app-child witnesses in `RcicF8EvInv` are private. These two are the
same `List.Mem` facts, so `certOfChild` can see the function and the
argument from a literal `HasTyT.app`. -/

def appChildFst {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A) :
    Child (.ty hf) (.ty (.app Γ f a A B hf ha)) := by
  show (Jd.ty hf : Jd E n) ∈ ([Jd.ty hf, Jd.ty ha] : List (Jd E n))
  exact .head _

def appChildSnd {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A) :
    Child (.ty ha) (.ty (.app Γ f a A B hf ha)) := by
  show (Jd.ty ha : Jd E n) ∈ ([Jd.ty hf, Jd.ty ha] : List (Jd E n))
  exact .tail _ (.head _)

/-- `lift 0 0` is not `rfl` (`lift_zero_idx`). Instantiating the lifted
replacement is still `instantiate0`. -/
theorem instLift0 (arg B : Expr Nat) :
    instantiate 0 (lift 0 0 arg) B = instantiate0 arg B :=
  congrArg (fun e => instantiate 0 e B) (lift_zero_idx 0 arg)

theorem hget0 {Γ : LCtx} (A : Expr Nat) :
    ((.assumption A :: Γ)[0]?) = some (.assumption A) :=
  List.getElem?_cons_zero

/-- The argument typing, moved across `lift 0 0` so `EvTc.subst0` can
read it. Context `substRemove v 0 (A :: Γ)` is `Γ` by `rfl`. -/
def argAtLift {R : List (Jd E n)} {Γ : LCtx} {arg A : Expr Nat}
    (ha : HasTyT E n Γ arg A) (hsub : ∃ r ∈ R, SubEq (.ty ha) r) :
    EvTy R Γ (lift 0 0 arg) (lift 0 0 A) :=
  EvTy.cast rfl (lift_zero_idx 0 arg).symm (lift_zero_idx 0 A).symm
    (.lit ha hsub)

/-- Codomain component of X, instantiated at the argument: the two
result types of a literal application. -/
def appFinish {R : List (Jd E n)} {Γ : LCtx} {arg Adom B B' : Expr Nat}
    (cod : EvTc R (.assumption Adom :: Γ) B B')
    (ha : HasTyT E n Γ arg Adom) (hsub : ∃ r ∈ R, SubEq (.ty ha) r) :
    EvTc R Γ (instantiate0 arg B) (instantiate0 arg B') :=
  EvTc.cast rfl (instLift0 arg B) (instLift0 arg B')
    (EvTc.subst0 (j := 0) (v := arg) (t := Adom) cod (hget0 Adom)
      (argAtLift ha hsub))

/-- Π chain for a literal application whose function is on the intro
spine. Off that spine this is `none` — not a recursive U, and not the
packaging closure. -/
def suppliedChain (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {R : List (Jd E n)} {Γ : LCtx} {f arg Adom Bcod Adom' Bcod' : Expr Nat}
    (hf : HasTyT E n Γ f (.pi Adom Bcod)) (ha : HasTyT E n Γ arg Adom)
    (hsl : ∃ r ∈ R, SubEq (.ty (.app Γ f arg Adom Bcod hf ha)) r)
    (hf' : HasTyT E n Γ f (.pi Adom' Bcod')) (ha' : HasTyT E n Γ arg Adom')
    (hsr : ∃ r ∈ R, SubEq (.ty (.app Γ f arg Adom' Bcod' hf' ha')) r) :
    Option (EvTc R Γ (.pi Adom Bcod) (.pi Adom' Bcod')) :=
  if hs : introTypeSpine f = true then
    some (introU hcl hinst hf (certOfChild (appChildFst hf ha) hsl) hs
      (.lit hf' (certOfChild (appChildFst hf' ha') hsr)) rfl)
  else
    none

/-- One literal application, matched on a single `EvTy`. A simultaneous
match refines the shared subject to `.app` and then cannot split `wk`,
whose subject is `lift`, not a constructor. -/
structure LitApp (R : List (Jd E n)) (Γ : LCtx) (a A : Expr Nat) where
  f : Expr Nat
  arg : Expr Nat
  Adom : Expr Nat
  Bcod : Expr Nat
  hf : HasTyT E n Γ f (.pi Adom Bcod)
  ha : HasTyT E n Γ arg Adom
  hsub : ∃ r ∈ R, SubEq (.ty (.app Γ f arg Adom Bcod hf ha)) r
  subj : a = .app f arg
  tyEq : A = instantiate0 arg Bcod

def litApp? {R : List (Jd E n)} {Γ : LCtx} {a A : Expr Nat}
    (D : EvTy R Γ a A) : Option (LitApp R Γ a A) :=
  match D with
  | .lit (.app _ f arg Adom Bcod hf ha) hsub =>
      some ⟨f, arg, Adom, Bcod, hf, ha, hsub, rfl, rfl⟩
  | _ => none

/-- Move a literal-app certificate onto equal function and argument
expressions. `f` and `arg` are the binders `subst` needs; projections
are not. -/
theorem transportLitSub {R : List (Jd E n)} {Γ : LCtx}
    {f arg f' arg' Adom' Bcod' : Expr Nat}
    (hfEq : f = f') (harg : arg = arg')
    (hf0 : HasTyT E n Γ f' (.pi Adom' Bcod'))
    (ha0 : HasTyT E n Γ arg' Adom')
    (hsub : ∃ r ∈ R, SubEq (.ty (.app Γ f' arg' Adom' Bcod' hf0 ha0)) r) :
    ∃ r ∈ R, SubEq (.ty (.app Γ f arg Adom' Bcod'
        (Eq.rec (motive := fun x _ => HasTyT E n Γ x (.pi Adom' Bcod')) hf0 hfEq.symm)
        (Eq.rec (motive := fun x _ => HasTyT E n Γ x Adom') ha0 harg.symm))) r := by
  subst hfEq
  subst harg
  exact hsub

/-- App arm. Both inputs must be literal applications of the same
function and argument; the chain is `suppliedChain`; the answer is X's
codomain component instantiated at the argument. Any other provenance
shape is a refusal. -/
def uAppX (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : ∀ R : List (Jd E n), XProcP R) {R : List (Jd E n)}
    {Γ : LCtx} {a A B : Expr Nat} (l : EvTy R Γ a A) (r : EvTy R Γ a B) :
    Option (EvTc R Γ A B) :=
  match litApp? l, litApp? r with
  | some al, some ar =>
      if hfEq : al.f = ar.f then
        if harg : al.arg = ar.arg then
          let hf' : HasTyT E n Γ al.f (.pi ar.Adom ar.Bcod) :=
            Eq.rec (motive := fun x _ => HasTyT E n Γ x (.pi ar.Adom ar.Bcod))
              ar.hf hfEq.symm
          let ha' : HasTyT E n Γ al.arg ar.Adom :=
            Eq.rec (motive := fun x _ => HasTyT E n Γ x ar.Adom) ar.ha harg.symm
          (suppliedChain hcl hinst al.hf al.ha al.hsub hf' ha'
              (transportLitSub hfEq harg ar.hf ar.ha ar.hsub)).bind fun c =>
            (X R c).map fun o =>
              EvTc.cast rfl al.tyEq.symm
                ((congrArg (fun x => instantiate0 x ar.Bcod) harg).trans ar.tyEq.symm)
                (appFinish o.2 al.ha (certOfChild (appChildSnd al.hf al.ha) al.hsub))
        else
          none
      else
        none
  | _, _ => none

/-- Additive U. The app subject calls `X`. Every other subject reuses
the landed total-to-partial bridge on the supplied `U`. -/
def UProcX (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : ∀ R : List (Jd E n), XProcP R)
    (U : ∀ R : List (Jd E n), UProc R) : ∀ R : List (Jd E n), UProcP R :=
  fun R {Γ a A B} l r =>
    match a with
    | .app _ _ => uAppX hcl hinst X l r
    | .bvar _ => UProcP.ofTotal U R l r
    | .sort _ => UProcP.ofTotal U R l r
    | .const _ _ => UProcP.ofTotal U R l r
    | .lam _ _ => UProcP.ofTotal U R l r
    | .pi _ _ => UProcP.ofTotal U R l r
    | .letE _ _ _ => UProcP.ofTotal U R l r
    | .lit _ => UProcP.ofTotal U R l r

/-- The landed partial leaf contract, on this processor. Not a proof
that every `X` and `U` satisfy it — the fixture below is one answer,
and the mutant is an answer the contract rejects. -/
def UContractX (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : ∀ R : List (Jd E n), XProcP R)
    (U : ∀ R : List (Jd E n), UProc R) : Prop :=
  UContractP (UProcX hcl hinst X U)

/-! ### Fixture: Abel–Coquand `z ⊤ : ⊤`, and a heavier rogue chain -/

namespace UProcXPins

open Rcic.Declarative.AbelCoquand

def pinCl : EnvClosed emptyEnv := fun _ _ h => Option.noConfusion h

def pinSS : EnvMembersSubstStable emptyEnv := fun _ _ h => Option.noConfusion h

/-- Real partial X: when the two Πs have equal domains and equal
codomains (decidable on `Expr`), the component chains are reflexivity.
Otherwise it refuses. It does not inspect the chain's proof. The app
arm still has to call it; the fixture's Π is `⊥ ≡ ⊥`, so it answers. -/
def pinX : ∀ R : List (Jd emptyEnv 0), XProcP R :=
  fun _ {Γ A B A' B'} _ =>
    if hA : A = A' then
      if hB : B = B' then
        some (EvTc.cast rfl rfl hA (EvTc.refl Γ A),
          EvTc.cast rfl rfl hB (EvTc.refl (.assumption A :: Γ) B))
      else
        none
    else
      none

def abelΓ : LCtx := .assumption bot :: []

/-- Strictly heavier than `zTopTy`. `refl` has size 1; each `trans`
adds 2, so `bigRefl k` has size `1 + 2k`. -/
def bigRefl : Nat → TyConvT emptyEnv 0 abelΓ top top
  | 0 => .refl _ _
  | k + 1 => .trans _ _ _ _ (bigRefl k) (.refl _ _)

def rogue : TyConvT emptyEnv 0 abelΓ top top := bigRefl 32

def pinRoot : Jd emptyEnv 0 := .ty (zTopTy 0)

def pinR : List (Jd emptyEnv 0) := [pinRoot, .tc rogue]

def pinSubTy : ∃ r ∈ pinR, SubEq pinRoot r :=
  ⟨pinRoot, List.Mem.head _, .inl rfl⟩

def pinL : EvTy pinR abelΓ (.app (.bvar 0) top) top :=
  .lit (zTopTy 0) pinSubTy

def pinRight : EvTy pinR abelΓ (.app (.bvar 0) top) top :=
  .lit (zTopTy 0) pinSubTy

/-- The Π chain the app arm builds for this fixture. Both function
typings are `zTy` (`bvar` is on the intro spine), so this is `introU`,
not the `U` parameter. -/
def pinChain : Option (EvTc pinR abelΓ bot bot) :=
  suppliedChain pinCl pinSS (zTy 0) (topIsPropAt 0 abelΓ) pinSubTy
    (zTy 0) (topIsPropAt 0 abelΓ) pinSubTy

def pinFinish (o : EvTc pinR (.assumption (.sort .zero) :: abelΓ) (.bvar 0) (.bvar 0)) :
    EvTc pinR abelΓ top top :=
  appFinish o (topIsPropAt 0 abelΓ)
    (certOfChild (appChildSnd (zTy 0) (topIsPropAt 0 abelΓ)) pinSubTy)

theorem pin_app_is_uApp (U : ∀ R : List (Jd emptyEnv 0), UProc R) :
    UProcX pinCl pinSS pinX U pinR pinL pinRight =
      uAppX pinCl pinSS pinX pinL pinRight := rfl

theorem pin_app_ignores_U :
    ∀ U₁ U₂ : ∀ R : List (Jd emptyEnv 0), UProc R,
      UProcX pinCl pinSS pinX U₁ pinR pinL pinRight =
        UProcX pinCl pinSS pinX U₂ pinR pinL pinRight :=
  fun _ _ => rfl

/-- The app arm applies `pinX` to `pinChain` and instantiates the
codomain component. `U` is not in the term. -/
theorem pin_app_calls_X (U : ∀ R : List (Jd emptyEnv 0), UProc R) :
    UProcX pinCl pinSS pinX U pinR pinL pinRight =
      pinChain.bind fun c => (pinX pinR c).map fun o => pinFinish o.2 := rfl

theorem pin_app_isSome (U : ∀ R : List (Jd emptyEnv 0), UProc R) :
    (UProcX pinCl pinSS pinX U pinR pinL pinRight).isSome = true := rfl

/-- A non-app subject reuses the landed bridge. `z : ⊥` is a `bvar`. -/
def bvarR : List (Jd emptyEnv 0) := [.ty (zTy 0)]

def bvarSub : ∃ r ∈ bvarR, SubEq (.ty (zTy 0)) r :=
  ⟨.ty (zTy 0), List.Mem.head _, .inl rfl⟩

def bvarL : EvTy bvarR abelΓ (.bvar 0) bot := .lit (zTy 0) bvarSub

def bvarRight : EvTy bvarR abelΓ (.bvar 0) bot := .lit (zTy 0) bvarSub

theorem pin_bvar_reuses_U (U : ∀ R : List (Jd emptyEnv 0), UProc R) :
    UProcX pinCl pinSS pinX U bvarR bvarL bvarRight =
      UProcP.ofTotal U bvarR bvarL bvarRight := rfl

theorem rogue_heavier :
    (Jd.ty (zTopTy 0)).wt < (Jd.tc rogue).wt := by
  decide

theorem not_subeq_rogue : ¬ SubEq (.tc rogue) (.ty (zTopTy 0)) := by
  intro h
  exact Nat.lt_irrefl _
    (Nat.lt_of_le_of_lt (subEq_wt_le h) rogue_heavier)

def rogueSub : ∃ r ∈ pinR, SubEq (.tc rogue) r :=
  ⟨.tc rogue, List.Mem.tail _ (List.Mem.head _), .inl rfl⟩

def mutantTc : EvTc pinR abelΓ top top := .lit rogue rogueSub

/-- Same app-result shape as the real arm, with the X supplier unused. -/
def uProcXMutantApp (_X : ∀ R : List (Jd emptyEnv 0), XProcP R) :
    Option (EvTc pinR abelΓ top top) :=
  some mutantTc

theorem pin_mutant_ignores :
    ∀ X Y : ∀ R : List (Jd emptyEnv 0), XProcP R,
      uProcXMutantApp X = uProcXMutantApp Y :=
  fun _ _ => rfl

theorem pin_mutant_answer : uProcXMutantApp pinX = some mutantTc := rfl

theorem pin_mutant_leaves : mutantTc.leaves = [.tc rogue] := rfl

theorem pin_input_leaves :
    pinL.leaves ++ pinRight.leaves = [.ty (zTopTy 0), .ty (zTopTy 0)] := rfl

theorem pin_mutant_not_below_inputs :
    ¬ ∃ ℓ' ∈ pinL.leaves ++ pinRight.leaves, SubEq (.tc rogue) ℓ' := by
  intro ⟨ℓ', hm, hs⟩
  rw [pin_input_leaves] at hm
  cases hm with
  | head => exact not_subeq_rogue hs
  | tail _ hm2 =>
    cases hm2 with
    | head => exact not_subeq_rogue hs
    | tail _ hm3 => cases hm3

/-- The mutant returns an answer, and that answer fails the leaf
obligation `UContractP` demands of every `some`. -/
theorem pin_mutant_accepts_rejected :
    ∃ u, uProcXMutantApp pinX = some u ∧
      ¬ (∀ ℓ ∈ u.leaves, ∃ ℓ' ∈ pinL.leaves ++ pinRight.leaves, SubEq ℓ ℓ') := by
  refine ⟨mutantTc, rfl, ?_⟩
  intro hok
  have hℓ : .tc rogue ∈ mutantTc.leaves := by
    rw [pin_mutant_leaves]
    exact List.Mem.head _
  exact pin_mutant_not_below_inputs (by
    obtain ⟨ℓ', hℓ', hs⟩ := hok (.tc rogue) hℓ
    exact ⟨ℓ', hℓ', hs⟩)

end UProcXPins

end Rcic.Declarative.F8Measure
