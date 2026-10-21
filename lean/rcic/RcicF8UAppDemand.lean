import rcic.RcicF8UProcX

/-!
# `RcicF8UAppDemand` — the actual U-app prefix before X answers

ChatGPT's J-line design, `S0_UX_REENTRY_DEMAND.md` §1–3: observe the
existing `uAppX` prefix through the result of the original `suppliedChain`.
The observations retain the literal inputs, their source certificates,
the function/argument equations, and the exact casts used by `uAppX`.
Neither the observation nor its construction has an X parameter. The
correspondence theorem relates it to the existing execution; no U
implementation or chain supplier is replaced here.

An applicable X entry still needs independent context/Via and admission
evidence. This is W-UX-REENTRY-CONTEXT/ADMISSION, and is not obtained merely
from the two input typings. The `appFinish` substitution is a later,
separate reentry obligation. `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
  {Γ : LCtx} {a A B : Expr Nat}

/-- An observed execution prefix of the existing literal-app arm. The
`chain_eq` field fixes the result of the actual `suppliedChain`, rather
than an arbitrary conversion with the same endpoints. -/
structure UAppAwaitX (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (l : EvTy R Γ a A) (r : EvTy R Γ a B) where
  left : LitApp R Γ a A
  right : LitApp R Γ a B
  left_eq : litApp? l = some left
  right_eq : litApp? r = some right
  function_eq : left.f = right.f
  argument_eq : left.arg = right.arg
  chain : EvTc R Γ (.pi left.Adom left.Bcod) (.pi right.Adom right.Bcod)
  chain_eq :
    suppliedChain hcl hinst left.hf left.ha left.hsub
      (Eq.rec (motive := fun x _ => HasTyT E n Γ x (.pi right.Adom right.Bcod))
        right.hf function_eq.symm)
      (Eq.rec (motive := fun x _ => HasTyT E n Γ x right.Adom)
        right.ha argument_eq.symm)
      (transportLitSub function_eq argument_eq right.hf right.ha right.hsub) = some chain

/-- The unchanged continuation after the actual X call succeeds. -/
def UAppAwaitX.finish {hcl : EnvClosed E} {hinst : EnvMembersSubstStable E}
    {l : EvTy R Γ a A} {r : EvTy R Γ a B} (p : UAppAwaitX hcl hinst l r)
    (o : EvTc R Γ p.left.Adom p.right.Adom ×
      EvTc R (.assumption p.left.Adom :: Γ) p.left.Bcod p.right.Bcod) : EvTc R Γ A B :=
  EvTc.cast rfl p.left.tyEq.symm
    ((congrArg (fun x => instantiate0 x p.right.Bcod) p.argument_eq).trans p.right.tyEq.symm)
    (appFinish o.2 p.left.ha (certOfChild (appChildSnd p.left.hf p.left.ha) p.left.hsub))

/-- Observe precisely the prefix ending inside `suppliedChain.bind`,
immediately before `X R c`. In particular this does not run X. -/
def uAppPre (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (l : EvTy R Γ a A) (r : EvTy R Γ a B) : Option (UAppAwaitX hcl hinst l r) :=
  if hl : (litApp? l).isSome = true then
    if hr : (litApp? r).isSome = true then
      let al := (litApp? l).get hl
      let ar := (litApp? r).get hr
      if hfEq : al.f = ar.f then
        if harg : al.arg = ar.arg then
          let hf' : HasTyT E n Γ al.f (.pi ar.Adom ar.Bcod) :=
            Eq.rec (motive := fun x _ => HasTyT E n Γ x (.pi ar.Adom ar.Bcod))
              ar.hf hfEq.symm
          let ha' : HasTyT E n Γ al.arg ar.Adom :=
            Eq.rec (motive := fun x _ => HasTyT E n Γ x ar.Adom) ar.ha harg.symm
          let result := suppliedChain hcl hinst al.hf al.ha al.hsub hf' ha'
            (transportLitSub hfEq harg ar.hf ar.ha ar.hsub)
          if hc : result.isSome = true then
            some ⟨al, ar, (Option.some_get hl).symm, (Option.some_get hr).symm,
              hfEq, harg, result.get hc, (Option.some_get hc).symm⟩
          else none
        else none
      else none
    else none
  else none

/-- The observer is a decomposition of the existing arm, including its
exact supplied chain and its original continuation. -/
theorem uAppX_eq_uAppPre (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : ∀ R : List (Jd E n), XProcP R) (l : EvTy R Γ a A) (r : EvTy R Γ a B) :
    uAppX hcl hinst X l r =
      match uAppPre hcl hinst l r with
      | none => none
      | some p => (X R p.chain).map p.finish := by
  by_cases hl : (litApp? l).isSome = true
  · by_cases hr : (litApp? r).isSome = true
    · simp only [uAppPre, dif_pos hl, dif_pos hr]
      conv =>
        lhs
        unfold uAppX
        rw [(Option.some_get hl).symm, (Option.some_get hr).symm]
      try dsimp only
      by_cases hf : ((litApp? l).get hl).f = ((litApp? r).get hr).f
      · simp only [dif_pos hf]
        by_cases ha : ((litApp? l).get hl).arg = ((litApp? r).get hr).arg
        · simp only [dif_pos ha]
          let result := suppliedChain hcl hinst ((litApp? l).get hl).hf
            ((litApp? l).get hl).ha ((litApp? l).get hl).hsub
            (Eq.rec (motive := fun x _ => HasTyT E n Γ x
              (.pi ((litApp? r).get hr).Adom ((litApp? r).get hr).Bcod))
              ((litApp? r).get hr).hf hf.symm)
            (Eq.rec (motive := fun x _ => HasTyT E n Γ x ((litApp? r).get hr).Adom)
              ((litApp? r).get hr).ha ha.symm)
            (transportLitSub hf ha ((litApp? r).get hr).hf
              ((litApp? r).get hr).ha ((litApp? r).get hr).hsub)
          by_cases hc : result.isSome = true
          · simp only [dif_pos hc]
            have hs := (Option.some_get hc).symm
            dsimp only [result] at hs
            conv =>
              lhs
              rw [hs]
            rfl
          · simp only [dif_neg hc]
            have hn : result = none := by
              cases h : result <;> simp_all
            dsimp only [result] at hn
            conv =>
              lhs
              rw [hn]
            rfl
        · simp only [dif_neg ha]
      · simp only [dif_neg hf]
    · have hn : litApp? r = none := by
        cases h : litApp? r <;> simp_all
      simp [uAppX, uAppPre, hn, hr]
  · have hn : litApp? l = none := by
      cases h : litApp? l <;> simp_all
    simp [uAppX, uAppPre, hn, hl]

/-- An actual observed literal app fixes the original wrapper's app
dispatch. This says nothing about recursively reached U invocations. -/
theorem UProcX_eq_uAppX_of_await (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E)
    (X : ∀ R : List (Jd E n), XProcP R) (U : ∀ R : List (Jd E n), UProc R)
    {l : EvTy R Γ a A} {r : EvTy R Γ a B} (p : UAppAwaitX hcl hinst l r) :
    UProcX hcl hinst X U R l r = uAppX hcl hinst X l r := by
  have hs := p.left.subj
  cases a <;> simp_all [UProcX]

/-- The observed pre-answer prefix corresponds to the original UProcX
wrapper, retaining its exact supplied chain and continuation. -/
theorem UProcX_eq_uAppPre_of_await (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E)
    (X : ∀ R : List (Jd E n), XProcP R) (U : ∀ R : List (Jd E n), UProc R)
    {l : EvTy R Γ a A} {r : EvTy R Γ a B} (p : UAppAwaitX hcl hinst l r)
    (hp : uAppPre hcl hinst l r = some p) :
    UProcX hcl hinst X U R l r = (X R p.chain).map p.finish := by
  rw [UProcX_eq_uAppX_of_await hcl hinst X U p, uAppX_eq_uAppPre, hp]

/-- The same observed prefix is applicable to every X callback. No
successful X/U output is a premise of this fact. -/
theorem uAppAwaitX_independent_of_X (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {l : EvTy R Γ a A} {r : EvTy R Γ a B} (p : UAppAwaitX hcl hinst l r)
    (hp : uAppPre hcl hinst l r = some p)
    (X Y : ∀ R : List (Jd E n), XProcP R) :
    uAppX hcl hinst X l r = (X R p.chain).map p.finish ∧
      uAppX hcl hinst Y l r = (Y R p.chain).map p.finish := by
  constructor <;> rw [uAppX_eq_uAppPre, hp]

/-- Refusal preserves the same actual pre-answer observation. This
asserts no execution after the refusing X call. -/
theorem uAppAwaitX_persists_when_X_refuses (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {l : EvTy R Γ a A} {r : EvTy R Γ a B}
    (p : UAppAwaitX hcl hinst l r) (hp : uAppPre hcl hinst l r = some p)
    (X : ∀ R : List (Jd E n), XProcP R) (hX : X R p.chain = none) :
    uAppPre hcl hinst l r = some p ∧ uAppX hcl hinst X l r = none := by
  refine ⟨hp, ?_⟩
  rw [uAppX_eq_uAppPre, hp]
  dsimp only
  rw [hX]
  rfl

end Rcic.Declarative.F8Measure
