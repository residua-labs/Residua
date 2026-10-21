/-
RCIC ParRed, piece 1 of 7: core judgments.

`ParRed` / `ParRedArgs` / `ParRedCtx` (the three mutual inductives),
`ParRedStar`, and the structural apparatus every other piece needs:
level equality (`eqN*`), `foldApps` head lemmas, `step_parRed`,
`parRed_to_conv` / `parRedStar_to_conv`, the ctx-lookup and
lookup-monotonicity families, `drop_let`, the v1 weight system, and
`parRed_weaken`.  `dummyAssump` / `liftDecl_dummy` are lifted here
from their original position in the complete-development narrative:
their first consumer is `assumpPad` in `RcicParRedSubst`, which must
not depend on the sort-wall material.

Split out of the former single `rcic.RcicParRed`; statements and
proofs are verbatim.  `rcic.RcicParRed` remains as the aggregator
that imports all seven pieces.
-/
import rcic.RcicDeclarative
import rcic.RcicSubstCalc
import rcic.RcicCtxMorph
import rcic.RcicIota
import rcic.RcicEnv
import rcic.RcicDerivationRec
import rcic.RcicInvertFamily
import rcic.RcicWeaken

namespace Rcic.Declarative

theorem eqN_refl (l : Level) : eqN l l := fun _ => rfl

theorem eqN_symm {a b : Level} (h : eqN a b) : eqN b a :=
  fun ρ => (h ρ).symm

theorem eqN_trans {a b c : Level} (h1 : eqN a b) (h2 : eqN b c) : eqN a c :=
  fun ρ => (h1 ρ).trans (h2 ρ)

theorem foldApps_snoc_ne_sort {l : Level} (f x : Expr Nat)
    (ys : List (Expr Nat)) :
    foldApps f (ys ++ [x]) ≠ .sort l := by
  induction ys generalizing f with
  | nil =>
      intro h
      cases h
  | cons y ys ih =>
      intro h
      exact ih (.app f y) h

theorem foldApps_snoc_ne_bvar {i : Nat} (f x : Expr Nat)
    (ys : List (Expr Nat)) :
    foldApps f (ys ++ [x]) ≠ .bvar i := by
  induction ys generalizing f with
  | nil =>
      intro h
      cases h
  | cons y ys ih =>
      intro h
      exact ih (.app f y) h

theorem foldApps_snoc_ne_lit {t : Nat} (f x : Expr Nat)
    (ys : List (Expr Nat)) :
    foldApps f (ys ++ [x]) ≠ .lit t := by
  induction ys generalizing f with
  | nil =>
      intro h
      cases h
  | cons y ys ih =>
      intro h
      exact ih (.app f y) h

theorem foldApps_snoc_ne_pi {A B : Expr Nat} (f x : Expr Nat)
    (ys : List (Expr Nat)) :
    foldApps f (ys ++ [x]) ≠ .pi A B := by
  induction ys generalizing f with
  | nil =>
      intro h
      cases h
  | cons y ys ih =>
      intro h
      exact ih (.app f y) h

/-- Length of a ctor-app spine is preserved by `List.map` (lift / inst
of `iotaSpine.hfieldsLen`). -/
theorem map_ctorSpine_length {α β : Type _} (f : α → β)
    {fields' ctorParams fields : List α}
    (h : fields'.length = (ctorParams ++ fields).length) :
    (fields'.map f).length =
      (ctorParams.map f ++ fields.map f).length := by
  rw [← List.map_append]
  simp only [List.length_map]
  exact h

/-- A sort is a normal form of the one-step relation. -/
def step_sort_false {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    Step E n Γ a e → {u : Level} → a = .sort u → False
  | _, _, _, .beta _ _ _ _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _, _, heq => nomatch heq
  | _, _, _, .zetaLocal _ _ _ _, _, heq => nomatch heq
  | _, _, _, .delta _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .iota _ _ _ hι, _u, heq =>
      match hι with
      | .of w =>
          foldApps_snoc_ne_sort (.const w.recRef w.ls) (ctorMajor w)
            w.preMajor heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

/-- A pi is a head-normal form of the one-step relation. -/
def step_pi_false {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    Step E n Γ a e → {A B : Expr Nat} → a = .pi A B → False
  | _, _, _, .beta _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .zetaLocal _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .delta _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .iota _ _ _ hι, _A, _B, heq =>
      match hι with
      | .of w =>
          foldApps_snoc_ne_pi (.const w.recRef w.ls) (ctorMajor w)
            w.preMajor heq
  | _, _, _, .lit _ _ _ _, _, _, heq => nomatch heq

mutual
/-- Parallel reduction of the recorded fragment (eta / irr postponed).
Lit is in the fragment: 08 pin natExpand.

iotaSpine is Tait–Martin-Löf form: argument premises are one-step
`ParRedArgs` (burned, not starred), conclusion is the combustion
`iotaRhsOf w2` (no continuing `hr`). `w2` witnesses the *reduced*
spine. Level drift on the two heads is `eqNList`. Lengths sit on
the constructor so inversion reads them (same method as `hfamSpine`). -/
inductive ParRed (E : ResolvedEnv) (n : Nat) : LCtx → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (e : Expr Nat) : ParRed E n Γ e e
  | sortEq (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
      ParRed E n Γ (.sort l₁) (.sort l₂)
  | consts (Γ : LCtx) (r : Nat) (ls ls' : List Level) (h : eqNList ls ls') :
      ParRed E n Γ (.const r ls) (.const r ls')
  | bvarZeta (Γ : LCtx) (i : Nat) (A v v' : Expr Nat)
      (h : Γ.get? i = some (.letBinding A v))
      (hv : ParRed E n (Γ.drop (i + 1)) v v') :
      ParRed E n Γ (.bvar i) (lift 0 (i + 1) v')
  /-- 02 §9 delta, level-instantiated (00 §20.6 RULE CHANGES). The
  conclusion index moved from the stored `b` to `instantiateLevels ls b`;
  NO field was added (F-0.1), so every `nomatch`/size/refutation arm
  that matches `.delta ..` survives unchanged. Under `EnvWf` this
  arm is monomorphic (`envWf_body_arity_zero` + `hlen` force `ls = []`),
  which is what keeps the level-substitution metatheorem out of this
  segment. -/
  | delta (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
      (b : Expr Nat)
      (hres : E.members r = some m) (hbody : m.body = some b)
      (htr : transparent m.mclass = true) :
      ParRed E n Γ (.const r ls) (instantiateLevels ls b)
  | app (Γ : LCtx) (f f' a a' : Expr Nat)
      (hf : ParRed E n Γ f f') (ha : ParRed E n Γ a a') :
      ParRed E n Γ (.app f a) (.app f' a')
  | beta (Γ : LCtx) (A A' body body' arg arg' : Expr Nat)
      (hA : ParRed E n Γ A A')
      (hb : ParRed E n (LocalDecl.assumption A :: Γ) body body')
      (ha : ParRed E n Γ arg arg') :
      ParRed E n Γ (.app (.lam A body) arg) (instantiate0 arg' body')
  | lam (Γ : LCtx) (A A' b b' : Expr Nat)
      (hA : ParRed E n Γ A A')
      (hb : ParRed E n (LocalDecl.assumption A :: Γ) b b') :
      ParRed E n Γ (.lam A b) (.lam A' b')
  | pi (Γ : LCtx) (A A' b b' : Expr Nat)
      (hA : ParRed E n Γ A A')
      (hb : ParRed E n (LocalDecl.assumption A :: Γ) b b') :
      ParRed E n Γ (.pi A b) (.pi A' b')
  | letE (Γ : LCtx) (A A' v v' b b' : Expr Nat)
      (hA : ParRed E n Γ A A') (hv : ParRed E n Γ v v')
      (hb : ParRed E n (LocalDecl.letBinding A v :: Γ) b b') :
      ParRed E n Γ (.letE A v b) (.letE A' v' b')
  | zeta (Γ : LCtx) (A A' v v' b b' : Expr Nat)
      (hA : ParRed E n Γ A A') (hv : ParRed E n Γ v v')
      (hb : ParRed E n (LocalDecl.letBinding A v :: Γ) b b') :
      ParRed E n Γ (.letE A v b) (instantiate0 v' b')
  /-- TML parallel iota: args take one parallel step, then the
  reduced spine burns. `w2` is the witness of the reduced lhs.
  Source is the unreduced recursor application; target is
  `iotaRhsOf w2` (combustion, no trailing `hr`). `.iota` is the
  derived refl-args special case. -/
  | iotaSpine (Γ : LCtx) (w2 : IotaWitness E)
      (lsR lsC : List Level)
      (hlsR : eqNList w2.ls lsR) (hlsC : eqNList w2.lsC lsC)
      (pre pre' fields fields' : List (Expr Nat))
      (hf : ParRedArgs E n Γ pre pre')
      (ha : ParRedArgs E n Γ fields fields')
      (hpreLen : pre'.length = w2.preMajor.length)
      (hfieldsLen : fields'.length =
          (w2.ctorParams ++ w2.fields).length)
      (hlhs : iotaLhsOf w2 =
          recCall (.const w2.recRef w2.ls) pre'
            (foldApps (.const w2.ctorRef w2.lsC) fields')) :
      ParRed E n Γ
        (recCall (.const w2.recRef lsR) pre
          (foldApps (.const w2.ctorRef lsC) fields))
        (iotaRhsOf w2)
  /-- 08 pin: a literal parallel-reduces to its constructor-level
  expansion. Meets F-05b; `step_parRed` no longer postpones lit. -/
  | lit (Γ : LCtx) (t : Nat) :
      ParRed E n Γ (.lit t) (natExpand t)

/-- Pointwise one-step ParRed of an argument list. Mutual with
`ParRed` so `iotaSpine` can carry it as a constructor premise.
Parameters are `(E n)` (same as `ParRed`); `Γ` is an index. -/
inductive ParRedArgs (E : ResolvedEnv) (n : Nat) :
    LCtx → List (Expr Nat) → List (Expr Nat) → Type
  | nil (Γ : LCtx) : ParRedArgs E n Γ [] []
  | cons {Γ : LCtx} {x y : Expr Nat} {xs ys : List (Expr Nat)}
      (h : ParRed E n Γ x y) (t : ParRedArgs E n Γ xs ys) :
      ParRedArgs E n Γ (x :: xs) (y :: ys)

/-- Pointwise parallel reduction of a local context. Let values
reduce in their tail context (one step). -/
inductive ParRedCtx (E : ResolvedEnv) (n : Nat) : LCtx → LCtx → Type
  | nil : ParRedCtx E n [] []
  | assumption {Γ Γ' : LCtx} {A A' : Expr Nat}
      (hA : ParRed E n Γ A A') (hΓ : ParRedCtx E n Γ Γ') :
      ParRedCtx E n (.assumption A :: Γ) (.assumption A' :: Γ')
  | letBinding {Γ Γ' : LCtx} {A A' v v' : Expr Nat}
      (hA : ParRed E n Γ A A')
      (hv : ParRed E n Γ v v')
      (hΓ : ParRedCtx E n Γ Γ') :
      ParRedCtx E n (.letBinding A v :: Γ) (.letBinding A' v' :: Γ')
end

/-- Multi-step parallel reduction. Not mutual with `ParRed`: iotaSpine
premises are one-step `ParRedArgs`, so a star field is not required. -/
inductive ParRedStar (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (e : Expr Nat) : ParRedStar E n Γ e e
  | tail {Γ : LCtx} {a b c : Expr Nat}
      (h : ParRed E n Γ a b) (hs : ParRedStar E n Γ b c) :
      ParRedStar E n Γ a c

/-- L4b (00 §20.6 RISKS R-1). Level drift is absorbed by ONE parallel
step: if `ls =ₙ ls'` pointwise then `instantiateLevels ls T` parallel-
reduces to `instantiateLevels ls' T` for every `T`.

This is the ParRed sibling of `convInstantiateLevels` (RcicLevelCalc)
and is what makes `parRed_diamond`'s `consts × delta` join close after
00 §20.6's rule change: today both sides land on the same stored `b`
and one leg is `refl`; after the change they land on
`instantiateLevels ls₁ b` and `instantiateLevels ls₂ b`, and this
lemma is the missing leg at `eqNList ls₁ ls₂`.

Structural recursion on `T`, with `Γ` generalized inside the recursion.
Binder arms use the LEFT side for the context extension — exactly the
context the recursive call already sits in — so no context-conversion
lemma is needed. Uses only `.refl / .sortEq / .consts / .app / .lam /
.pi / .letE`: no `.delta`, no `.iotaSpine`, no `.beta`/`.zeta`, hence
no `EnvWf`, no `CtxWf`, no confluence — outside the F-05b ring. -/
def parRedInstantiateLevels {E : ResolvedEnv} {n : Nat} :
    (T : Expr Nat) → {ls ls' : List Level} → eqNList ls ls' →
    (Γ : LCtx) → ParRed E n Γ (instantiateLevels ls T) (instantiateLevels ls' T)
  | .bvar i, _, _, _, Γ => ParRed.refl Γ (.bvar i)
  | .sort l, ls, ls', h, Γ =>
      ParRed.sortEq Γ (instLevel ls l) (instLevel ls' l) (instLevel_eqNList h l)
  | .const r ms, ls, ls', h, Γ =>
      ParRed.consts Γ r (ms.map (instLevel ls)) (ms.map (instLevel ls'))
        (instLevel_eqNList_map h ms)
  | .app f x, _, _, h, Γ =>
      ParRed.app Γ _ _ _ _ (parRedInstantiateLevels f h Γ)
        (parRedInstantiateLevels x h Γ)
  | .lam A b, ls, _, h, Γ =>
      ParRed.lam Γ _ _ _ _ (parRedInstantiateLevels A h Γ)
        (parRedInstantiateLevels b h (LocalDecl.assumption (instantiateLevels ls A) :: Γ))
  | .pi A B, ls, _, h, Γ =>
      ParRed.pi Γ _ _ _ _ (parRedInstantiateLevels A h Γ)
        (parRedInstantiateLevels B h (LocalDecl.assumption (instantiateLevels ls A) :: Γ))
  | .letE A v b, ls, _, h, Γ =>
      ParRed.letE Γ _ _ _ _ _ _ (parRedInstantiateLevels A h Γ)
        (parRedInstantiateLevels v h Γ)
        (parRedInstantiateLevels b h
          (LocalDecl.letBinding (instantiateLevels ls A) (instantiateLevels ls v) :: Γ))
  | .lit t, _, _, _, Γ => ParRed.refl Γ (.lit t)

/-- Star form of L4b: one `parRedInstantiateLevels` step, then stop. -/
def parRedStarInstantiateLevels {E : ResolvedEnv} {n : Nat}
    (T : Expr Nat) {ls ls' : List Level} (h : eqNList ls ls') (Γ : LCtx) :
    ParRedStar E n Γ (instantiateLevels ls T) (instantiateLevels ls' T) :=
  .tail (parRedInstantiateLevels T h Γ) (.refl _ _)

/-- A sort parallel-reduces only to a sort, at an =ₙ level. -/
def parRed_sort {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    ParRed E n Γ a e → {u : Level} → a = .sort u →
    Σ' (v : Level), (e = .sort v) ×' eqN u v
  | _, _, _, .refl _ a, u, heq => by
      subst heq
      exact ⟨u, rfl, eqN_refl u⟩
  | _, _, _, .sortEq _ l₁ l₂ h, u, heq => by
      injection heq with hu
      subst hu
      exact ⟨l₂, rfl, h⟩
  | _, _, _, .consts _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .delta .., _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, u, heq =>
      (foldApps_snoc_ne_sort (.const w.recRef lsR)
        (foldApps (.const w.ctorRef lsC) fields) pre heq).elim
  | _, _, _, .lit _ _, _, heq => nomatch heq

/-- A pi parallel-reduces only to a pi (congruence). -/
def parRed_pi {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a e : Expr Nat} →
    ParRed E n Γ a e → {A B : Expr Nat} → a = .pi A B →
    Σ' (A' B' : Expr Nat),
      (e = .pi A' B') ×'
      ParRed E n Γ A A' ×'
      ParRed E n (LocalDecl.assumption A :: Γ) B B'
  | _, _, _, .refl _ a, A, B, heq => by
      subst heq
      exact ⟨A, B, rfl, .refl _ _, .refl _ _⟩
  | _, _, _, .sortEq _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .consts _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .bvarZeta _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .beta _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .pi _ A₀ A₁ B₀ B₁ hA hB, A, B, heq => by
      injection heq with hAeq hBeq
      subst hAeq
      subst hBeq
      exact ⟨A₁, B₁, rfl, hA, hB⟩
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .zeta _ _ _ _ _ _ _ _ _ _, _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ w lsR lsC _ _ pre _ fields _ _ _ _ _ _, A, B, heq =>
      (foldApps_snoc_ne_pi (.const w.recRef lsR)
        (foldApps (.const w.ctorRef lsC) fields) pre heq).elim
  | _, _, _, .lit _ _, _, _, heq => nomatch heq

/-- One-step of the fragment is a parallel reduction. Lit is in the
fragment (`natExpand`); the sum stays for matcher stability. -/
def step_parRed {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} →
    Step E n Γ a b →
    (Σ' (t : Nat) (exp : Expr Nat),
      (a = .lit t) ×' LiteralExpansion t exp) ⊕'
    ParRed E n Γ a b
  | _, _, _, .beta Γ A body arg =>
      .inr (.beta Γ A A body body arg arg (.refl _ _) (.refl _ _) (.refl _ _))
  | _, _, _, .zeta Γ A value body =>
      .inr (.zeta Γ A A value value body body
        (.refl _ _) (.refl _ _) (.refl _ _))
  | _, _, _, .zetaLocal Γ i v h =>
      match hg : Γ.get? i with
      | some (.letBinding A v0) =>
          have hv : v = lift 0 (i + 1) v0 := by
            simp only [lookupValue, hg] at h
            exact Option.some.inj h.symm
          .inr (hv ▸ .bvarZeta Γ i A v0 v0 hg (.refl _ _))
      | some (.assumption _) => by
          simp only [lookupValue, hg] at h; cases h
      | none => by
          simp only [lookupValue, hg] at h; cases h
  | _, _, _, .delta Γ r ls m b hres hbody htr =>
      .inr (.delta Γ r ls m b hres hbody htr)
  | _, _, _, .iota Γ lhs rhs hι =>
      match hι with
      | .of w =>
          let rec argsRefl : (xs : List (Expr Nat)) →
              ParRedArgs E n Γ xs xs
            | [] => ParRedArgs.nil Γ
            | _ :: xs => .cons (.refl _ _) (argsRefl xs)
          .inr (Eq.mpr
            (congrArg (fun e => ParRed E n Γ e (iotaRhsOf w))
              (by simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall]))
            (.iotaSpine Γ w w.ls w.lsC
              (by
                induction w.ls with
                | nil => exact True.intro
                | cons _ _ ih => exact ⟨eqN_refl _, ih⟩)
              (by
                induction w.lsC with
                | nil => exact True.intro
                | cons _ _ ih => exact ⟨eqN_refl _, ih⟩)
              w.preMajor w.preMajor
              (w.ctorParams ++ w.fields)
              (w.ctorParams ++ w.fields)
              (argsRefl _) (argsRefl _)
              rfl rfl (by simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall])))
  | _, _, _, .lit Γ t exp h =>
      match h with
      | .of _ => .inr (.lit Γ t)

/-- Read a let-value in the tail, then lift the conversion into `Γ`. -/
def conv_of_bvarZeta_value {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    {Γ : LCtx} → {i : Nat} → {A v v' : Expr Nat} →
    (h : Γ.get? i = some (.letBinding A v)) →
    Conv E n (Γ.drop (i + 1)) v v' →
    Conv E n Γ (lift 0 (i + 1) v) (lift 0 (i + 1) v')
  | [], _, _, _, _, h, _ => nomatch h
  | .assumption _ :: _, 0, _, _, _, h, _ => by
      simp only [List.get?_cons_zero] at h; exact nomatch h
  | .letBinding A0 v0 :: rest, 0, A, v, v', h, hc => by
      simp only [List.get?_cons_zero] at h
      injection h with heq
      injection heq with _hA hv
      subst hv
      have hw := convWeaken (.letBinding A0 v0) hE (c := 0) hc
      simp only [insertAt_zero] at hw
      exact hw
  | d :: rest, i + 1, A, v, v', h, hc => by
      simp only [List.get?_cons_succ, List.drop] at h hc
      have ih := conv_of_bvarZeta_value hE h hc
      have hw := convWeaken d hE (c := 0) ih
      simp only [insertAt_zero] at hw
      have htgt :
          lift 0 1 (lift 0 (i + 1) v) = lift 0 (i + 1 + 1) v :=
        lift_lift_merge 1 (i + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _) v
      have htgt' :
          lift 0 1 (lift 0 (i + 1) v') = lift 0 (i + 1 + 1) v' :=
        lift_lift_merge 1 (i + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _) v'
      rw [htgt, htgt'] at hw
      exact hw

/-- Lift a conversion across a prefix of binders. -/
def convWeaken_lctx {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    (Δ : LCtx) → {Γ : LCtx} → {a b : Expr Nat} →
    Conv E n Γ a b →
    Conv E n (Δ ++ Γ) (lift 0 Δ.length a) (lift 0 Δ.length b)
  | [], _, _, _, h => by
      simp only [List.nil_append, List.length_nil, lift_zero]
      exact h
  | d :: Δ, Γ, a, b, h => by
      have ih := convWeaken_lctx hE Δ h
      have hw := convWeaken d hE (c := 0) ih
      simp only [List.cons_append, List.length_cons]
      have ha : lift 0 1 (lift 0 Δ.length a) = lift 0 (Δ.length + 1) a :=
        lift_lift_merge 1 Δ.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) a
      have hb : lift 0 1 (lift 0 Δ.length b) = lift 0 (Δ.length + 1) b :=
        lift_lift_merge 1 Δ.length 0 0 (Nat.le_refl 0) (Nat.zero_le _) b
      rw [← ha, ← hb]
      exact hw

theorem eqNList_symm_early : {ls ls' : List Level} → eqNList ls ls' → eqNList ls' ls
  | [], [], _ => True.intro
  | _l :: _ls, _l' :: _ls', h => ⟨eqN_symm h.1, eqNList_symm_early h.2⟩
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

def parRedArgs_refl_early {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (xs : List (Expr Nat)) → ParRedArgs E n Γ xs xs
  | [] => ParRedArgs.nil Γ
  | _ :: xs => .cons (.refl _ _) (parRedArgs_refl_early xs)

/-- Head-congruence of `foldApps`. Lives outside the `parRed_to_conv`
mutual so iotaSpine level-drift does not create a non-structural
call into that mutual. -/
def conv_foldApps_head {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f f' : Expr Nat} (hf : Conv E n Γ f f') :
    (xs : List (Expr Nat)) →
    Conv E n Γ (foldApps f xs) (foldApps f' xs)
  | [] => hf
  | x :: xs =>
      conv_foldApps_head (.app Γ f f' x x hf (.refl Γ x)) xs

mutual
def parRed_to_conv {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    {Γ : LCtx} → {a b : Expr Nat} →
    ParRed E n Γ a b → Conv E n Γ a b
  | _, _, _, .refl Γ e => .refl Γ e
  | _, _, _, .sortEq Γ l₁ l₂ h => .sorts Γ l₁ l₂ h
  | _, _, _, .consts Γ r ls ls' h => .consts Γ r ls ls' h
  | _, _, _, .bvarZeta Γ i A v v' h hv =>
      have hlk : lookupValue Γ i = some (lift 0 (i + 1) v) := by
        simp only [lookupValue, h]
      .trans _ _ _ _
        (.step _ _ _ (.zetaLocal Γ i (lift 0 (i + 1) v) hlk))
        (conv_of_bvarZeta_value hE h (parRed_to_conv hE hv))
  | _, _, _, .delta Γ r ls m b hres hbody htr =>
      .step _ _ _ (.delta Γ r ls m b hres hbody htr)
  | _, _, _, .app Γ f f' a a' hf ha =>
      .app Γ f f' a a' (parRed_to_conv hE hf) (parRed_to_conv hE ha)
  | _, _, _, .beta Γ A A' body body' arg arg' hA hb ha =>
      .trans _ _ _ _
        (.app _ _ _ _ _
          (.lam _ _ _ _ _ (parRed_to_conv hE hA) (parRed_to_conv hE hb))
          (parRed_to_conv hE ha))
        (.step _ _ _ (.beta _ A' body' arg'))
  | _, _, _, .lam Γ A A' b b' hA hb =>
      .lam Γ A A' b b' (parRed_to_conv hE hA) (parRed_to_conv hE hb)
  | _, _, _, .pi Γ A A' b b' hA hb =>
      .pi Γ A A' b b' (parRed_to_conv hE hA) (parRed_to_conv hE hb)
  | _, _, _, .letE Γ A A' v v' b b' hA hv hb =>
      .letE Γ A A' v v' b b'
        (parRed_to_conv hE hA) (parRed_to_conv hE hv) (parRed_to_conv hE hb)
  | _, _, _, .zeta Γ A A' v v' b b' hA hv hb =>
      .trans _ _ _ _
        (.letE _ _ _ _ _ _ _
          (parRed_to_conv hE hA) (parRed_to_conv hE hv) (parRed_to_conv hE hb))
        (.step _ _ _ (.zeta _ A' v' b'))
  | _, _, _, .lit Γ t =>
      .step _ _ _ (.lit Γ t (natExpand t) (.of t))
  | _, _, _, .iotaSpine Γ w2 lsR lsC _hlsR _hlsC pre pre' fields fields'
        hf ha _hpreLen _hfieldsLen hlhs => by
      have hmaj : Conv E n Γ
          (foldApps (.const w2.ctorRef lsC) fields)
          (foldApps (.const w2.ctorRef lsC) fields') :=
        parRedArgs_foldApps_to_conv hE ha (.refl _ _)
      have hpre : Conv E n Γ
          (foldApps (.const w2.recRef lsR) pre)
          (foldApps (.const w2.recRef lsR) pre') :=
        parRedArgs_foldApps_to_conv hE hf (.refl _ _)
      have hcongr : Conv E n Γ
          (recCall (.const w2.recRef lsR) pre
            (foldApps (.const w2.ctorRef lsC) fields))
          (recCall (.const w2.recRef lsR) pre'
            (foldApps (.const w2.ctorRef lsC) fields')) := by
        simp only [recCall]
        rw [foldApps_snoc, foldApps_snoc]
        exact .app _ _ _ _ _ hpre hmaj
      have hlevels : Conv E n Γ
          (recCall (.const w2.recRef lsR) pre'
            (foldApps (.const w2.ctorRef lsC) fields'))
          (iotaLhsOf w2) := by
        have h1 : Conv E n Γ
            (recCall (.const w2.recRef lsR) pre'
              (foldApps (.const w2.ctorRef lsC) fields'))
            (recCall (.const w2.recRef w2.ls) pre'
              (foldApps (.const w2.ctorRef w2.lsC) fields')) := by
          simp only [recCall]
          rw [foldApps_snoc, foldApps_snoc]
          exact .app _ _ _ _ _
            (conv_foldApps_head
              (.consts Γ w2.recRef lsR w2.ls (eqNList_symm_early _hlsR))
              pre')
            (conv_foldApps_head
              (.consts Γ w2.ctorRef lsC w2.lsC (eqNList_symm_early _hlsC))
              fields')
        exact hlhs ▸ h1
      exact .trans _ _ _ _ hcongr
        (.trans _ _ _ _ hlevels
          (.step _ _ _ (.iota Γ (iotaLhsOf w2) (iotaRhsOf w2) (.of w2))))

def parRedArgs_foldApps_to_conv {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {Γ : LCtx}
    {f f' : Expr Nat} {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys) (hf : Conv E n Γ f f') :
    Conv E n Γ (foldApps f xs) (foldApps f' ys) :=
  match h with
  | ParRedArgs.nil _ => hf
  | ParRedArgs.cons (xs := xs) (ys := ys) hx t =>
      parRedArgs_foldApps_to_conv hE (xs := xs) (ys := ys) t
        (.app _ _ _ _ _ hf (parRed_to_conv hE hx))

def parRedStar_to_conv {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n) :
    {Γ : LCtx} → {a b : Expr Nat} →
    ParRedStar E n Γ a b → Conv E n Γ a b
  | _, _, _, .refl Γ e => .refl Γ e
  | _, _, _, .tail h hs =>
      .trans _ _ _ _ (parRed_to_conv hE h) (parRedStar_to_conv hE hs)
end

theorem eqNList_refl : (ls : List Level) → eqNList ls ls
  | [] => True.intro
  | l :: ls => ⟨eqN_refl l, eqNList_refl ls⟩

theorem eqNList_of_eq {ls ls' : List Level} (h : ls = ls') :
    eqNList ls ls' :=
  h ▸ eqNList_refl ls

theorem eqNList_symm : {ls ls' : List Level} → eqNList ls ls' → eqNList ls' ls
  | [], [], _ => True.intro
  | _l :: _ls, _l' :: _ls', h => ⟨eqN_symm h.1, eqNList_symm h.2⟩
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

theorem eqNList_trans : {ls1 ls2 ls3 : List Level} →
    eqNList ls1 ls2 → eqNList ls2 ls3 → eqNList ls1 ls3
  | [], [], [], _, _ => True.intro
  | _l1 :: _t1, _l2 :: _t2, _l3 :: _t3, h12, h23 =>
      ⟨eqN_trans h12.1 h23.1, eqNList_trans h12.2 h23.2⟩
  | [], [], _ :: _, _, h23 => False.elim h23
  | [], _ :: _, _, h12, _ => False.elim h12
  | _ :: _, [], _, h12, _ => False.elim h12
  | _ :: _, _ :: _, [], _, h23 => False.elim h23

/-- Corollary of `parRed_sort`: a sort parallel-reduces only at =ₙ. -/
theorem parRed_sort_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {u v : Level} (h : ParRed E n Γ (.sort u) (.sort v)) : eqN u v :=
  let ⟨_w, hsort, heqn⟩ := parRed_sort h rfl
  match hsort with
  | Eq.refl _ => heqn

/-- Π-injectivity of ParRed (fragment analogue of PiConvInj). -/
def parRed_pi_inj {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B A' B' : Expr Nat}
    (h : ParRed E n Γ (.pi A B) (.pi A' B')) :
    ParRed E n Γ A A' ×' ParRed E n (LocalDecl.assumption A :: Γ) B B' :=
  let ⟨_A1, _B1, heq, hA, hB⟩ := parRed_pi h rfl
  match heq with
  | Eq.refl _ => ⟨hA, hB⟩

theorem foldApps_app_ne_lam (f a : Expr Nat) :
    (xs : List (Expr Nat)) → {A b : Expr Nat} →
    foldApps (.app f a) xs ≠ .lam A b
  | [], _, _, h => nomatch h
  | x :: xs, _A, _b, h => foldApps_app_ne_lam (.app f a) x xs h

theorem foldApps_const_ne_lam {r : Nat} {ls : List Level} :
    (xs : List (Expr Nat)) → {A b : Expr Nat} →
    foldApps (.const r ls) xs ≠ .lam A b
  | [], _, _, h => nomatch h
  | x :: xs, _A, _b, h => foldApps_app_ne_lam (.const r ls) x xs h

/-- Pointwise reflexivity of argument spines. -/
def parRedArgs_refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (xs : List (Expr Nat)) → ParRedArgs E n Γ xs xs
  | [] => ParRedArgs.nil Γ
  | _ :: xs => .cons (.refl _ _) (parRedArgs_refl xs)

/-- Context reflexivity. Ordinary diamond is both sides of this. -/
def parRedCtx_refl {E : ResolvedEnv} {n : Nat} :
    (Γ : LCtx) → ParRedCtx E n Γ Γ
  | [] => .nil
  | .assumption A :: Γ =>
      .assumption (.refl _ A) (parRedCtx_refl Γ)
  | .letBinding A v :: Γ =>
      .letBinding (.refl _ A) (.refl _ v) (parRedCtx_refl Γ)

/-- Tails of a context reduction are still a context reduction. -/
def parRedCtx_drop {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} → (k : Nat) →
    ParRedCtx E n Γ Γ' →
    ParRedCtx E n (Γ.drop k) (Γ'.drop k)
  | _, _, 0, h => by simp only [List.drop]; exact h
  | _, _, _k + 1, .nil => .nil
  | _, _, k + 1, .assumption _ hΓ => parRedCtx_drop k hΓ
  | _, _, k + 1, .letBinding _ _ hΓ => parRedCtx_drop k hΓ

/-- Read a let at `i` through a context reduction: the stored value
takes its one step in the tail, and the tails remain related. -/
def parRedCtx_get?_let {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} → {i : Nat} → {A v : Expr Nat} →
    ParRedCtx E n Γ Γ' →
    Γ.get? i = some (.letBinding A v) →
    Σ' (A' v' : Expr Nat),
      (Γ'.get? i = some (.letBinding A' v')) ×'
      ParRed E n (Γ.drop (i + 1)) v v' ×'
      ParRedCtx E n (Γ.drop (i + 1)) (Γ'.drop (i + 1))
  | _, _, _, _, _, .nil, h => nomatch h
  | _, _, 0, _, _, .assumption _ _, h => nomatch h
  | _, _, i + 1, A, v, .assumption _ hΓ, h => by
      simp only [List.get?_cons_succ, List.drop] at h ⊢
      exact parRedCtx_get?_let (i := i) hΓ h
  | _, _, 0, A, v, .letBinding (A := A0) (v := v0) (A' := A') (v' := v')
        _hA hv hΓ, h =>
      let hveq : v0 = v := by
        have := Option.some.inj h
        injection this
      ⟨A', v', rfl, hveq ▸ hv, hΓ⟩
  | _, _, i + 1, A, v, .letBinding _ _ hΓ, h => by
      simp only [List.get?_cons_succ, List.drop] at h ⊢
      exact parRedCtx_get?_let (i := i) hΓ h

/-- Derived iota: TML iotaSpine with refl args. Sandwich: Step.iota. -/
def parRed_iota {E : ResolvedEnv} {n : Nat} (Γ : LCtx)
    (w : IotaWitness E) :
    ParRed E n Γ (iotaLhsOf w) (iotaRhsOf w) :=
  have hlsR : eqNList w.ls w.ls := by
    induction w.ls with
    | nil => exact True.intro
    | cons _ _ ih => exact ⟨eqN_refl _, ih⟩
  have hlsC : eqNList w.lsC w.lsC := by
    induction w.lsC with
    | nil => exact True.intro
    | cons _ _ ih => exact ⟨eqN_refl _, ih⟩
  have hlhs : iotaLhsOf w =
      recCall (.const w.recRef w.ls) w.preMajor
        (foldApps (.const w.ctorRef w.lsC)
          (w.ctorParams ++ w.fields)) := by
    simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall]
  Eq.mpr (congrArg (fun e => ParRed E n Γ e (iotaRhsOf w))
      (by simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall]))
    (.iotaSpine Γ w w.ls w.lsC hlsR hlsC
      w.preMajor w.preMajor
      (w.ctorParams ++ w.fields)
      (w.ctorParams ++ w.fields)
      (parRedArgs_refl _) (parRedArgs_refl _)
      rfl rfl (by simp only [iotaLhsOf, ctorMajor, ctorSpine, recCall]))

theorem lookupValue_of_get?_let {Γ : LCtx} {i : Nat}
    {A v : Expr Nat}
    (h : Γ.get? i = some (.letBinding A v)) :
    lookupValue Γ i = some (lift 0 (i + 1) v) := by
  simp only [lookupValue, h]

/-- Inverse: a successful `lookupValue` is a let-binding at `i`. -/
def get?_of_lookupValue {Γ : LCtx} {i : Nat} {val : Expr Nat}
    (h : lookupValue Γ i = some val) :
    Σ' (A stored : Expr Nat),
      (Γ.get? i = some (.letBinding A stored)) ×'
      (val = lift 0 (i + 1) stored) := by
  match hg : Γ.get? i with
  | none =>
      simp only [lookupValue, hg] at h; exact nomatch h
  | some (.assumption _) =>
      simp only [lookupValue, hg] at h; exact nomatch h
  | some (.letBinding A stored) =>
      refine ⟨A, stored, rfl, ?_⟩
      simp only [lookupValue, hg] at h
      exact (Option.some.inj h).symm

theorem lift_zero_amount_inj (k : Nat) {e1 e2 : Expr Nat} :
    lift 0 k e1 = lift 0 k e2 → e1 = e2 := by
  induction k generalizing e1 e2 with
  | zero =>
      intro h
      simpa [lift_zero] using h
  | succ k ih =>
      intro h
      have h1 : lift 0 1 (lift 0 k e1) = lift 0 (k + 1) e1 :=
        lift_lift_merge 1 k 0 0 (Nat.le_refl 0) (Nat.zero_le k) e1
      have h2 : lift 0 1 (lift 0 k e2) = lift 0 (k + 1) e2 :=
        lift_lift_merge 1 k 0 0 (Nat.le_refl 0) (Nat.zero_le k) e2
      have hmid : lift 0 k e1 = lift 0 k e2 :=
        lift_inj 0 (lift 0 k e1) (lift 0 k e2)
          (h1.trans (h.trans h2.symm))
      exact ih hmid

theorem get?_drop (Γ : LCtx) (k j : Nat) :
    (Γ.drop k).get? j = Γ.get? (j + k) := by
  induction Γ generalizing k j with
  | nil =>
      cases k <;> simp only [List.drop, List.get?]
  | cons d rest ih =>
      cases k with
      | zero => simp only [List.drop, Nat.add_zero]
      | succ k =>
          simp only [List.drop, List.get?_cons_succ, Nat.add_succ,
            Nat.succ_add]
          exact ih k j

/-- Tail lookupValue at `j` is determined by parent lookupValue at `j+k`
(same stored value; lift amount is the local index). -/
theorem lookupValue_drop_cong_at {Γ Γ' : LCtx} (k j : Nat)
    (h : lookupValue Γ (j + k) = lookupValue Γ' (j + k)) :
    lookupValue (Γ.drop k) j = lookupValue (Γ'.drop k) j := by
  simp only [lookupValue, get?_drop]
  simp only [lookupValue] at h
  match hg : Γ.get? (j + k), hg' : Γ'.get? (j + k) with
  | none, none => rfl
  | none, some (.assumption _) => rfl
  | none, some (.letBinding _ _) =>
      simp only [hg, hg'] at h; exact nomatch h
  | some (.assumption _), none => rfl
  | some (.assumption _), some (.assumption _) => rfl
  | some (.assumption _), some (.letBinding _ _) =>
      simp only [hg, hg'] at h; exact nomatch h
  | some (.letBinding _ _), none =>
      simp only [hg, hg'] at h; exact nomatch h
  | some (.letBinding _ _), some (.assumption _) =>
      simp only [hg, hg'] at h; exact nomatch h
  | some (.letBinding _ v), some (.letBinding _ v') =>
      have hvlift : lift 0 (j + k + 1) v = lift 0 (j + k + 1) v' := by
        simp only [hg, hg'] at h
        exact Option.some.inj h
      have hv : v = v' := lift_zero_amount_inj (j + k + 1) hvlift
      simp only [hv]

/-- lookupValue-equal contexts store the same unlifted let-value. -/
def get?_let_of_lookupValue_eq {Γ Γ' : LCtx} {i : Nat}
    {A v : Expr Nat}
    (h : Γ.get? i = some (.letBinding A v))
    (hΓ : lookupValue Γ i = lookupValue Γ' i) :
    Σ' (A' : Expr Nat), Γ'.get? i = some (.letBinding A' v) :=
  have hlk : lookupValue Γ i = some (lift 0 (i + 1) v) :=
    lookupValue_of_get?_let h
  have hlk' : lookupValue Γ' i = some (lift 0 (i + 1) v) :=
    hΓ.symm.trans hlk
  have ⟨A', v', hg, hv⟩ :
      Σ' (A' v' : Expr Nat),
        (Γ'.get? i = some (.letBinding A' v')) ×' (v' = v) :=
    match hg : Γ'.get? i with
    | none =>
        False.elim (by simp only [lookupValue, hg] at hlk'; exact nomatch hlk')
    | some (.assumption _) =>
        False.elim (by simp only [lookupValue, hg] at hlk'; exact nomatch hlk')
    | some (.letBinding A' v') =>
        have hvlift : lift 0 (i + 1) v' = lift 0 (i + 1) v :=
          Option.some.inj (by
            simp only [lookupValue, hg] at hlk'
            exact hlk')
        ⟨A', v', rfl, lift_zero_amount_inj (i + 1) hvlift⟩
  ⟨A', hv ▸ hg⟩

mutual
/-- ParRed is insensitive to assumption-types (only lookupValue matters). -/
def parRed_ctx_lookup {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} → {a b : Expr Nat} →
    (∀ i, lookupValue Γ i = lookupValue Γ' i) →
    ParRed E n Γ a b → ParRed E n Γ' a b
  | Γ, Γ', _, _, hΓ, .refl _ e => .refl _ _
  | Γ, Γ', _, _, hΓ, .sortEq _ l₁ l₂ h => .sortEq _ l₁ l₂ h
  | Γ, Γ', _, _, hΓ, .consts _ r ls ls' h => .consts _ r ls ls' h
  | Γ, Γ', _, _, hΓ, .bvarZeta _ i A v v' hlk hv =>
      let ⟨A', hlk'⟩ := get?_let_of_lookupValue_eq hlk (hΓ i)
      .bvarZeta _ i A' v v' hlk'
        (parRed_ctx_lookup (fun j =>
            lookupValue_drop_cong_at (i + 1) j (hΓ (j + (i + 1)))) hv)
  | Γ, Γ', _, _, hΓ, .delta _ r ls m b hres hbody htr =>
      .delta _ r ls m b hres hbody htr
  | Γ, Γ', _, _, hΓ, .app _ f f' x x' hf ha =>
      .app _ f f' x x' (parRed_ctx_lookup hΓ hf) (parRed_ctx_lookup hΓ ha)
  | Γ, Γ', _, _, hΓ, .beta _ A A' body body' arg arg' hA hb ha =>
      .beta _ A A' body body' arg arg'
        (parRed_ctx_lookup hΓ hA)
        (parRed_ctx_lookup (fun i => by
            cases i with
            | zero => rfl
            | succ i =>
                simp only [lookupValue_cons_succ, hΓ]) hb)
        (parRed_ctx_lookup hΓ ha)
  | Γ, Γ', _, _, hΓ, .lam _ A A' b b' hA hb =>
      .lam _ A A' b b'
        (parRed_ctx_lookup hΓ hA)
        (parRed_ctx_lookup (fun i => by
            cases i with
            | zero => rfl
            | succ i =>
                simp only [lookupValue_cons_succ, hΓ]) hb)
  | Γ, Γ', _, _, hΓ, .pi _ A A' b b' hA hb =>
      .pi _ A A' b b'
        (parRed_ctx_lookup hΓ hA)
        (parRed_ctx_lookup (fun i => by
            cases i with
            | zero => rfl
            | succ i =>
                simp only [lookupValue_cons_succ, hΓ]) hb)
  | Γ, Γ', _, _, hΓ, .letE _ A A' v v' b b' hA hv hb =>
      .letE _ A A' v v' b b'
        (parRed_ctx_lookup hΓ hA)
        (parRed_ctx_lookup hΓ hv)
        (parRed_ctx_lookup (fun i => by
            cases i with
            | zero => rfl
            | succ i =>
                simp only [lookupValue_cons_succ, hΓ]) hb)
  | Γ, Γ', _, _, hΓ, .zeta _ A A' v v' b b' hA hv hb =>
      .zeta _ A A' v v' b b'
        (parRed_ctx_lookup hΓ hA)
        (parRed_ctx_lookup hΓ hv)
        (parRed_ctx_lookup (fun i => by
            cases i with
            | zero => rfl
            | succ i =>
                simp only [lookupValue_cons_succ, hΓ]) hb)
  | Γ, Γ', _, _, hΓ, .iotaSpine _ w2 lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha hpreLen hfieldsLen hlhs =>
      .iotaSpine _ w2 lsR lsC hlsR hlsC pre pre' fields fields'
        (parRedArgs_ctx_lookup hf hΓ) (parRedArgs_ctx_lookup ha hΓ)
        hpreLen hfieldsLen hlhs
  | Γ, Γ', _, _, hΓ, .lit _ t => .lit _ t

def parRedArgs_ctx_lookup {E : ResolvedEnv} {n : Nat}
    {Γ Γ' : LCtx} {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys)
    (hΓ : ∀ i, lookupValue Γ i = lookupValue Γ' i) :
    ParRedArgs E n Γ' xs ys :=
  match h with
  | ParRedArgs.nil _ => ParRedArgs.nil Γ'
  | ParRedArgs.cons hx t =>
      .cons (parRed_ctx_lookup hΓ hx) (parRedArgs_ctx_lookup (h := t) hΓ)

def parRedStar_ctx_lookup {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} → {a b : Expr Nat} →
    (∀ i, lookupValue Γ i = lookupValue Γ' i) →
    ParRedStar E n Γ a b → ParRedStar E n Γ' a b
  | _Γ, _Γ', _, _, _hΓ, .refl _ e => .refl _ _
  | _Γ, _Γ', _, _, hΓ, .tail h hs =>
      .tail (parRed_ctx_lookup hΓ h) (parRedStar_ctx_lookup hΓ hs)
end

theorem lookupValue_assumption_irrel (A A' : Expr Nat) (Γ : LCtx) (i : Nat) :
    lookupValue (.assumption A :: Γ) i = lookupValue (.assumption A' :: Γ) i := by
  cases i with
  | zero => rfl
  | succ i => simp only [lookupValue_cons_succ]

def parRed_replace_assump {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' : Expr Nat} {a b : Expr Nat} :
    ParRed E n (.assumption A :: Γ) a b →
    ParRed E n (.assumption A' :: Γ) a b :=
  parRed_ctx_lookup (lookupValue_assumption_irrel A A' Γ)

mutual
/-- Adding let-values (none → some) preserves existing ParRed:
a derivation only consults lookups that already succeeded. -/
def parRed_lookup_mono {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} →
    (∀ i v, lookupValue Γ i = some v → lookupValue Γ' i = some v) →
    {a b : Expr Nat} →
    ParRed E n Γ a b → ParRed E n Γ' a b
  | Γ, Γ', hΓ, _, _, .refl _ e => .refl _ _
  | Γ, Γ', hΓ, _, _, .sortEq _ l₁ l₂ h => .sortEq _ l₁ l₂ h
  | Γ, Γ', hΓ, _, _, .consts _ r ls ls' h => .consts _ r ls ls' h
  | Γ, Γ', hΓ, _, _, .bvarZeta _ i A v v' hlk hv =>
      let hlk0 := lookupValue_of_get?_let hlk
      let hlkΓ' := hΓ i (lift 0 (i + 1) v) hlk0
      let ⟨A', hlk'⟩ := get?_let_of_lookupValue_eq hlk
        (hlk0.trans hlkΓ'.symm)
      .bvarZeta _ i A' v v' hlk'
        (parRed_lookup_mono (fun j w hw => by
            simp only [lookupValue, get?_drop] at hw ⊢
            match hg : Γ.get? (j + (i + 1)) with
            | none =>
                simp only [hg] at hw; exact nomatch hw
            | some (.assumption _) =>
                simp only [hg] at hw; exact nomatch hw
            | some (.letBinding A0 v0) =>
                simp only [hg] at hw
                have hlk : lookupValue Γ (j + (i + 1)) =
                    some (lift 0 (j + (i + 1) + 1) v0) := by
                  simp only [lookupValue, hg]
                have hlk' := hΓ (j + (i + 1)) _ hlk
                simp only [lookupValue] at hlk'
                match hg' : Γ'.get? (j + (i + 1)) with
                | some (.letBinding _ v0') =>
                    have hvlift :
                        lift 0 (j + (i + 1) + 1) v0' =
                          lift 0 (j + (i + 1) + 1) v0 := by
                      simp only [hg'] at hlk'
                      exact Option.some.inj hlk'
                    have hv0 : v0' = v0 :=
                      lift_zero_amount_inj _ hvlift
                    simp only [hg', hv0]
                    exact hw
                | none =>
                    simp only [hg'] at hlk'; exact nomatch hlk'
                | some (.assumption _) =>
                    simp only [hg'] at hlk'; exact nomatch hlk') hv)
  | Γ, Γ', hΓ, _, _, .delta _ r ls m b hres hbody htr =>
      .delta _ r ls m b hres hbody htr
  | Γ, Γ', hΓ, _, _, .app _ f f' x x' hf ha =>
      .app _ f f' x x' (parRed_lookup_mono hΓ hf) (parRed_lookup_mono hΓ ha)
  | Γ, Γ', hΓ, _, _, .beta _ A A' body body' arg arg' hA hb ha =>
      .beta _ A A' body body' arg arg'
        (parRed_lookup_mono hΓ hA)
        (parRed_lookup_mono (fun i v hv => by
            cases i with
            | zero => exact hv
            | succ i =>
                simp only [lookupValue_cons_succ] at hv ⊢
                cases hrest : lookupValue Γ i with
                | none =>
                    simp only [hrest, Option.map_none'] at hv
                    exact nomatch hv
                | some v0 =>
                    simp only [hrest, Option.map_some'] at hv
                    injection hv with hv0
                    subst hv0
                    have := hΓ i v0 hrest
                    simp only [this, Option.map_some']) hb)
        (parRed_lookup_mono hΓ ha)
  | Γ, Γ', hΓ, _, _, .lam _ A A' b b' hA hb =>
      .lam _ A A' b b'
        (parRed_lookup_mono hΓ hA)
        (parRed_lookup_mono (fun i v hv => by
            cases i with
            | zero => exact hv
            | succ i =>
                simp only [lookupValue_cons_succ] at hv ⊢
                cases hrest : lookupValue Γ i with
                | none =>
                    simp only [hrest, Option.map_none'] at hv
                    exact nomatch hv
                | some v0 =>
                    simp only [hrest, Option.map_some'] at hv
                    injection hv with hv0
                    subst hv0
                    have := hΓ i v0 hrest
                    simp only [this, Option.map_some']) hb)
  | Γ, Γ', hΓ, _, _, .pi _ A A' b b' hA hb =>
      .pi _ A A' b b'
        (parRed_lookup_mono hΓ hA)
        (parRed_lookup_mono (fun i v hv => by
            cases i with
            | zero => exact hv
            | succ i =>
                simp only [lookupValue_cons_succ] at hv ⊢
                cases hrest : lookupValue Γ i with
                | none =>
                    simp only [hrest, Option.map_none'] at hv
                    exact nomatch hv
                | some v0 =>
                    simp only [hrest, Option.map_some'] at hv
                    injection hv with hv0
                    subst hv0
                    have := hΓ i v0 hrest
                    simp only [this, Option.map_some']) hb)
  | Γ, Γ', hΓ, _, _, .letE _ A A' v v' b b' hA hv hb =>
      .letE _ A A' v v' b b'
        (parRed_lookup_mono hΓ hA)
        (parRed_lookup_mono hΓ hv)
        (parRed_lookup_mono (fun i w hw => by
            cases i with
            | zero => exact hw
            | succ i =>
                simp only [lookupValue_cons_succ] at hw ⊢
                cases hrest : lookupValue Γ i with
                | none =>
                    simp only [hrest, Option.map_none'] at hw
                    exact nomatch hw
                | some v0 =>
                    simp only [hrest, Option.map_some'] at hw
                    injection hw with hv0
                    subst hv0
                    have := hΓ i v0 hrest
                    simp only [this, Option.map_some']) hb)
  | Γ, Γ', hΓ, _, _, .zeta _ A A' v v' b b' hA hv hb =>
      .zeta _ A A' v v' b b'
        (parRed_lookup_mono hΓ hA)
        (parRed_lookup_mono hΓ hv)
        (parRed_lookup_mono (fun i w hw => by
            cases i with
            | zero => exact hw
            | succ i =>
                simp only [lookupValue_cons_succ] at hw ⊢
                cases hrest : lookupValue Γ i with
                | none =>
                    simp only [hrest, Option.map_none'] at hw
                    exact nomatch hw
                | some v0 =>
                    simp only [hrest, Option.map_some'] at hw
                    injection hw with hv0
                    subst hv0
                    have := hΓ i v0 hrest
                    simp only [this, Option.map_some']) hb)
  | Γ, Γ', hΓ, _, _, .iotaSpine _ w2 lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha hpreLen hfieldsLen hlhs =>
      .iotaSpine _ w2 lsR lsC hlsR hlsC pre pre' fields fields'
        (parRedArgs_lookup_mono hf hΓ) (parRedArgs_lookup_mono ha hΓ)
        hpreLen hfieldsLen hlhs
  | Γ, Γ', hΓ, _, _, .lit _ t => .lit _ t

def parRedArgs_lookup_mono {E : ResolvedEnv} {n : Nat}
    {Γ Γ' : LCtx} {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys)
    (hΓ : ∀ i v, lookupValue Γ i = some v → lookupValue Γ' i = some v) :
    ParRedArgs E n Γ' xs ys :=
  match h with
  | ParRedArgs.nil _ => ParRedArgs.nil Γ'
  | ParRedArgs.cons hx t =>
      .cons (parRed_lookup_mono hΓ hx) (parRedArgs_lookup_mono (h := t) hΓ)

def parRedStar_lookup_mono {E : ResolvedEnv} {n : Nat} :
    {Γ Γ' : LCtx} →
    (∀ i v, lookupValue Γ i = some v → lookupValue Γ' i = some v) →
    {a b : Expr Nat} →
    ParRedStar E n Γ a b → ParRedStar E n Γ' a b
  | _, _, _, _, _, .refl _ e => .refl _ _
  | _, _, hΓ, _, _, .tail h hs =>
      .tail (parRed_lookup_mono hΓ h) (parRedStar_lookup_mono hΓ hs)
end

theorem lookupValue_assump_subset_let (A A' v : Expr Nat) (Γ : LCtx)
    (i : Nat) (w : Expr Nat)
    (h : lookupValue (.assumption A :: Γ) i = some w) :
    lookupValue (.letBinding A' v :: Γ) i = some w := by
  cases i with
  | zero =>
      simp only [lookupValue, List.get?_cons_zero] at h
      exact nomatch h
  | succ i =>
      rw [lookupValue_cons_succ] at h ⊢
      exact h

def parRed_assump_to_let {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v : Expr Nat} {a b : Expr Nat} :
    ParRed E n (.assumption A :: Γ) a b →
    ParRed E n (.letBinding A' v :: Γ) a b :=
  parRed_lookup_mono (lookupValue_assump_subset_let A A' v Γ)

theorem lookupValue_let_assump_ne (A A' v : Expr Nat) (Γ : LCtx)
    {i : Nat} (h : i ≠ 0) :
    lookupValue (.letBinding A v :: Γ) i =
      lookupValue (.assumption A' :: Γ) i := by
  cases i with
  | zero => exact (h rfl).elim
  | succ i =>
      rw [lookupValue_cons_succ, lookupValue_cons_succ]

theorem lookupValue_assump_cons_shift {A A' : Expr Nat} {Γ Γ' : LCtx}
    {k : Nat} (hΓ : ∀ i, i ≠ k → lookupValue Γ i = lookupValue Γ' i)
    (i : Nat) (hi : i ≠ k + 1) :
    lookupValue (.assumption A :: Γ) i =
      lookupValue (.assumption A' :: Γ') i := by
  cases i with
  | zero =>
      simp only [lookupValue, List.get?_cons_zero]
  | succ i' =>
      rw [lookupValue_cons_succ, lookupValue_cons_succ,
        hΓ i' (fun heq => hi (congrArg Nat.succ heq))]

theorem lookupValue_let_cons_shift {A v : Expr Nat} {Γ Γ' : LCtx}
    {k : Nat} (hΓ : ∀ i, i ≠ k → lookupValue Γ i = lookupValue Γ' i)
    (i : Nat) (hi : i ≠ k + 1) :
    lookupValue (.letBinding A v :: Γ) i =
      lookupValue (.letBinding A v :: Γ') i := by
  cases i with
  | zero =>
      simp only [lookupValue, List.get?_cons_zero]
  | succ i' =>
      rw [lookupValue_cons_succ, lookupValue_cons_succ,
        hΓ i' (fun heq => hi (congrArg Nat.succ heq))]

mutual
/-- Inverse of parRed_assump_to_let when the dropped let is unused
(bvarZeta at k returns none). -/
def parRed_drop_let {E : ResolvedEnv} {n : Nat} (k : Nat) {Γ Γ' : LCtx}
    (hΓ : ∀ i, i ≠ k → lookupValue Γ i = lookupValue Γ' i) :
    {a b : Expr Nat} →
    ParRed E n Γ a b →
    Option (ParRed E n Γ' a b)
  | _, _, .refl _ e => some (.refl _ e)
  | _, _, .sortEq _ l₁ l₂ h => some (.sortEq _ l₁ l₂ h)
  | _, _, .consts _ r ls ls' h => some (.consts _ r ls ls' h)
  | _, _, .lit _ t => some (.lit _ t)
  | _, _, .bvarZeta _ i A v v' hlk hv =>
      if hik : i = k then none
      else
        let ⟨A', hlk'⟩ := get?_let_of_lookupValue_eq hlk (hΓ i hik)
        if hki : k < i + 1 then
          some (.bvarZeta _ i A' v v' hlk'
            (parRed_ctx_lookup (fun j =>
                lookupValue_drop_cong_at (i + 1) j
                  (hΓ (j + (i + 1)) (by omega))) hv))
        else
          match parRed_drop_let (k - (i + 1)) (fun j hj =>
              lookupValue_drop_cong_at (i + 1) j
                (hΓ (j + (i + 1)) (by omega))) hv with
          | none => none
          | some hv' => some (.bvarZeta _ i A' v v' hlk' hv')
  | _, _, .delta _ r ls m b hres hbody htr =>
      some (.delta _ r ls m b hres hbody htr)
  | _, _, .app _ f f' a a' hf ha =>
      match parRed_drop_let k hΓ hf, parRed_drop_let k hΓ ha with
      | some hf', some ha' => some (.app _ f f' a a' hf' ha')
      | _, _ => none
  | _, _, .lam _ A A' b b' hA hb =>
      match parRed_drop_let k hΓ hA,
          parRed_drop_let (k + 1)
            (lookupValue_assump_cons_shift (A := A) (A' := A) hΓ) hb with
      | some hA', some hb' => some (.lam _ A A' b b' hA' hb')
      | _, _ => none
  | _, _, .pi _ A A' B B' hA hB =>
      match parRed_drop_let k hΓ hA,
          parRed_drop_let (k + 1)
            (lookupValue_assump_cons_shift (A := A) (A' := A) hΓ) hB with
      | some hA', some hB' => some (.pi _ A A' B B' hA' hB')
      | _, _ => none
  | _, _, .letE _ A A' v v' b b' hA hv hb =>
      match parRed_drop_let k hΓ hA, parRed_drop_let k hΓ hv,
          parRed_drop_let (k + 1)
            (lookupValue_let_cons_shift (A := A) (v := v) hΓ) hb with
      | some hA', some hv', some hb' =>
          some (.letE _ A A' v v' b b' hA' hv' hb')
      | _, _, _ => none
  | _, _, .zeta _ A A' v v' b b' hA hv hb =>
      match parRed_drop_let k hΓ hA, parRed_drop_let k hΓ hv,
          parRed_drop_let (k + 1)
            (lookupValue_let_cons_shift (A := A) (v := v) hΓ) hb with
      | some hA', some hv', some hb' =>
          some (.zeta _ A A' v v' b b' hA' hv' hb')
      | _, _, _ => none
  | _, _, .beta _ A A' body body' arg arg' hA hb ha =>
      match parRed_drop_let k hΓ hA,
          parRed_drop_let (k + 1)
            (lookupValue_assump_cons_shift (A := A) (A' := A) hΓ) hb,
          parRed_drop_let k hΓ ha with
      | some hA', some hb', some ha' =>
          some (.beta _ A A' body body' arg arg' hA' hb' ha')
      | _, _, _ => none
  | _, _, .iotaSpine _ w2 lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha hpreLen hfieldsLen hlhs =>
      match parRedArgs_drop_let k hf hΓ, parRedArgs_drop_let k ha hΓ with
      | some hf', some ha' =>
          some (.iotaSpine _ w2 lsR lsC hlsR hlsC pre pre' fields fields'
            hf' ha' hpreLen hfieldsLen hlhs)
      | _, _ => none

def parRedArgs_drop_let {E : ResolvedEnv} {n : Nat} (k : Nat)
    {Γ Γ' : LCtx} {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys)
    (hΓ : ∀ i, i ≠ k → lookupValue Γ i = lookupValue Γ' i) :
    Option (ParRedArgs E n Γ' xs ys) :=
  match h with
  | ParRedArgs.nil _ => some (ParRedArgs.nil Γ')
  | ParRedArgs.cons hx t =>
      match parRed_drop_let k hΓ hx, parRedArgs_drop_let k (h := t) hΓ with
      | some hx', some t' => some (.cons hx' t')
      | _, _ => none

def parRedStar_drop_let {E : ResolvedEnv} {n : Nat} (k : Nat)
    {Γ Γ' : LCtx} (hΓ : ∀ i, i ≠ k → lookupValue Γ i = lookupValue Γ' i) :
    {a b : Expr Nat} →
    ParRedStar E n Γ a b →
    Option (ParRedStar E n Γ' a b)
  | _, _, .refl _ e => some (.refl _ e)
  | _, _, .tail h hs =>
      match parRed_drop_let k hΓ h, parRedStar_drop_let k hΓ hs with
      | some h', some hs' => some (.tail h' hs')
      | _, _ => none
end

mutual
/-- Constructor count of a ParRed derivation. drop_let preserves it;
TRIANGLE well-founded rec uses it so drop_let results are smaller
than the enclosing letE/zeta. -/
def parRedWeight {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → ParRed E n Γ a b → Nat
  | _, _, _, .refl .. => 1
  | _, _, _, .sortEq .. => 1
  | _, _, _, .consts .. => 1
  | _, _, _, .lit .. => 1
  | _, _, _, .bvarZeta _ _ _ _ _ _ hv => parRedWeight hv + 1
  | _, _, _, .delta .. => 1
  | _, _, _, .app _ _ _ _ _ hf ha => parRedWeight hf + parRedWeight ha + 1
  | _, _, _, .lam _ _ _ _ _ hA hb => parRedWeight hA + parRedWeight hb + 1
  | _, _, _, .pi _ _ _ _ _ hA hB => parRedWeight hA + parRedWeight hB + 1
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb =>
      parRedWeight hA + parRedWeight hv + parRedWeight hb + 1
  | _, _, _, .zeta _ _ _ _ _ _ _ hA hv hb =>
      parRedWeight hA + parRedWeight hv + parRedWeight hb + 1
  | _, _, _, .beta _ _ _ _ _ _ _ hA hb ha =>
      parRedWeight hA + parRedWeight hb + parRedWeight ha + 1
  | _, _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ hf ha _ _ _ =>
      parRedArgsWeight hf + parRedArgsWeight ha + 1

def parRedArgsWeight {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} (h : ParRedArgs E n Γ xs ys) : Nat :=
  match h with
  | ParRedArgs.nil _ => 1
  | ParRedArgs.cons hx t => parRedWeight hx + parRedArgsWeight (h := t) + 1

def parRedStarWeight {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → ParRedStar E n Γ a b → Nat
  | _, _, _, .refl .. => 1
  | _, _, _, .tail h hs => parRedWeight h + parRedStarWeight hs + 1
end

theorem get?_some_lt {α : Type _} {xs : List α} {i : Nat} {x : α}
    (h : xs.get? i = some x) : i < xs.length := by
  induction xs generalizing i with
  | nil =>
      simp only [List.get?] at h; exact nomatch h
  | cons _ rest ih =>
      cases i with
      | zero => simp only [List.length_cons]; omega
      | succ i =>
          simp only [List.get?_cons_succ] at h
          simp only [List.length_cons]
          exact Nat.succ_lt_succ (ih h)

/-- Inserting at `c` leaves a later let (`c ≤ i`) at `i+1`, unlifted. -/
theorem insertAt_get?_ge (d : LocalDecl) :
    {c i : Nat} → {Γ : LCtx} →
    c ≤ i → (insertAt d c Γ).get? (i + 1) = Γ.get? i
  | 0, i, Γ, _ => by
      simp only [insertAt_zero, List.get?_cons_succ]
  | c + 1, i, [], _ => by
      change (d :: []).get? (i + 1) = none
      cases i with
      | zero => rfl
      | succ _ => rfl
  | c + 1, 0, _ :: _, h => by exfalso; omega
  | c + 1, i + 1, x :: Γ, h => by
      simp only [insertAt_succ_cons, List.get?_cons_succ]
      exact insertAt_get?_ge d (by omega : c ≤ i)

/-- Inserting at `c` after a let at `i < c` liftDecl's that let. -/
theorem insertAt_get?_lt (d : LocalDecl) :
    {c i : Nat} → {Γ : LCtx} → {x : LocalDecl} →
    i < c → Γ.get? i = some x →
    (insertAt d c Γ).get? i = some (liftDecl (c - i - 1) x)
  | 0, i, Γ, x, h, _ => (Nat.not_lt_zero i h).elim
  | c + 1, 0, [], x, _, hg => by
      simp only [List.get?] at hg; exact nomatch hg
  | c + 1, 0, y :: Γ, x, _, hg => by
      simp only [List.get?_cons_zero] at hg
      injection hg with hy; subst hy
      simp only [insertAt_succ_cons, List.get?_cons_zero, liftDecl]
      simp only [Nat.sub_zero, Nat.add_sub_cancel]
  | c + 1, i + 1, [], x, _, hg => by
      simp only [List.get?] at hg; exact nomatch hg
  | c + 1, i + 1, y :: Γ, x, h, hg => by
      simp only [List.get?_cons_succ] at hg
      simp only [insertAt_succ_cons, List.get?_cons_succ]
      have ih := insertAt_get?_lt d (by omega : i < c) hg
      have : c + 1 - (i + 1) - 1 = c - i - 1 := by omega
      rw [this]
      exact ih

/-- Tail after a later let is the original tail (insert sits in the prefix). -/
theorem insertAt_drop_ge (d : LocalDecl) :
    {c i : Nat} → {Γ : LCtx} →
    c ≤ i → (insertAt d c Γ).drop (i + 2) = Γ.drop (i + 1)
  | 0, i, Γ, _ => by
      simp only [insertAt_zero, List.drop]
  | c + 1, 0, _, h => by exfalso; omega
  | c + 1, i + 1, [], h => by
      simp only [insertAt, List.drop]
  | c + 1, i + 1, x :: Γ, h => by
      simp only [insertAt_succ_cons, List.drop]
      exact insertAt_drop_ge d (by omega : c ≤ i)

/-- Tail after an earlier let: the insert lands in the tail. -/
theorem insertAt_drop_lt (d : LocalDecl) :
    {c i : Nat} → {Γ : LCtx} →
    i < c → i < Γ.length →
    (insertAt d c Γ).drop (i + 1) =
      insertAt d (c - i - 1) (Γ.drop (i + 1))
  | 0, i, Γ, h, _ => (Nat.not_lt_zero i h).elim
  | c + 1, 0, [], _, hlen => by
      simp only [List.length] at hlen; exact nomatch hlen
  | c + 1, 0, x :: Γ, _, _ => by
      simp only [insertAt_succ_cons, List.drop, Nat.sub_zero,
        Nat.add_sub_cancel]
  | c + 1, i + 1, [], _, hlen => by
      simp only [List.length] at hlen
      exfalso
      omega
  | c + 1, i + 1, x :: Γ, h, hlen => by
      simp only [insertAt_succ_cons, List.drop]
      have : c + 1 - (i + 1) - 1 = c - i - 1 := by omega
      rw [this]
      exact insertAt_drop_lt d (by omega : i < c)
        (by simp only [List.length_cons] at hlen; omega)

mutual
/-- Weakening of ParRed. Lit is closed (natExpand_lift). -/
def parRed_weaken (d : LocalDecl) {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) :
    {c : Nat} → {Γ : LCtx} → {a b : Expr Nat} →
    ParRed E n Γ a b →
    ParRed E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b)
  | c, _, _, _, .refl _ e => .refl _ _
  | c, _, _, _, .sortEq _ l₁ l₂ h => by
      simp only [lift]
      exact .sortEq _ l₁ l₂ h
  | c, _, _, _, .consts _ r ls ls' h => by
      simp only [lift]
      exact .consts _ r ls ls' h
  | c, Γ, _, _, .bvarZeta _ i A v v' hlk hv => by
      by_cases hic : i < c
      · -- Insert sits in the tail; recurse on `hv` at `c-(i+1)`.
        simp only [lift, if_neg (Nat.not_le_of_gt hic)]
        have hlen := get?_some_lt hlk
        have hg := insertAt_get?_lt d (Γ := Γ) hic hlk
        have hdrop := insertAt_drop_lt d (Γ := Γ) hic hlen
        have hv' :=
          parRed_weaken d hE (c := c - i - 1) hv
        rw [← hdrop] at hv'
        have htgt :
            lift 0 (i + 1) (lift (c - i - 1) 1 v') =
              lift (i + 1 + (c - i - 1)) 1 (lift 0 (i + 1) v') :=
          lift_lift_permute (i + 1) 1 (c - i - 1) 0 (Nat.zero_le _) v'
        have hsum : i + 1 + (c - i - 1) = c := by omega
        rw [hsum] at htgt
        simp only [liftDecl] at hg
        exact htgt ▸
          .bvarZeta (insertAt d c Γ) i
            (lift (c - i - 1) 1 A) (lift (c - i - 1) 1 v)
            (lift (c - i - 1) 1 v') hg hv'
      · -- Insert sits in the prefix; reuse `hv`, shift the index.
        have hge : c ≤ i := Nat.le_of_not_lt hic
        simp only [lift, if_pos hge]
        have hg := insertAt_get?_ge d (Γ := Γ) hge
        rw [hlk] at hg
        have hdrop := insertAt_drop_ge d (Γ := Γ) hge
        have htgt : lift 0 (i + 2) v' =
            lift c 1 (lift 0 (i + 1) v') :=
          (lift_lift_merge 1 (i + 1) 0 c (Nat.zero_le c)
            (by omega : c ≤ i + 1) v').symm
        exact htgt ▸
          .bvarZeta (insertAt d c Γ) (i + 1) A v v' hg
            (hdrop ▸ hv)
  | c, _, _, _, .delta Γ r ls m body hres hbody htr => by
      simp only [lift]
      have hcl := (envWf_closed_inst hE r m hres).2 body hbody ls c
      rw [hcl]
      exact .delta _ r ls m body hres hbody htr
  | c, _, _, _, .app _ f f' x x' hf ha => by
      simp only [lift]
      exact .app _ _ _ _ _
        (parRed_weaken d hE (c := c) hf) (parRed_weaken d hE (c := c) ha)
  | c, _, _, _, .beta Γ A A' body body' arg arg' hA hb ha => by
      have h := lift_instantiate_low 1 c 0 arg' (by omega) body'
      simp only [lift, instantiate0]
      rw [h]
      exact .beta _ _ _ _ _ _ _
        (parRed_weaken d hE (c := c) hA)
        (parRed_weaken d hE (c := c + 1) hb)
        (parRed_weaken d hE (c := c) ha)
  | c, _, _, _, .lam Γ A A' b b' hA hb => by
      simp only [lift]
      have hb' := parRed_weaken d hE (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .lam _ _ _ _ _
        (parRed_weaken d hE (c := c) hA) hb'
  | c, _, _, _, .pi Γ A A' b b' hA hb => by
      simp only [lift]
      have hb' := parRed_weaken d hE (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .pi _ _ _ _ _
        (parRed_weaken d hE (c := c) hA) hb'
  | c, _, _, _, .letE Γ A A' v v' b b' hA hv hb => by
      simp only [lift]
      have hb' := parRed_weaken d hE (c := c + 1) hb
      simp only [insertAt_succ_cons, liftDecl] at hb'
      exact .letE _ _ _ _ _ _ _
        (parRed_weaken d hE (c := c) hA)
        (parRed_weaken d hE (c := c) hv) hb'
  | c, _, _, _, .zeta Γ A A' v v' b b' hA hv hb => by
      have h := lift_instantiate_low 1 c 0 v' (by omega) b'
      simp only [lift, instantiate0]
      rw [h]
      exact .zeta _ _ _ _ _ _ _
        (parRed_weaken d hE (c := c) hA)
        (parRed_weaken d hE (c := c) hv)
        (parRed_weaken d hE (c := c + 1) hb)
  | c, _, _, _, .iotaSpine Γ w2 lsR lsC hlsR hlsC pre pre' fields fields'
        hf ha hpreLen hfieldsLen hlhs => by
      have hf' := parRedArgs_weaken d hE (c := c) hf
      have ha' := parRedArgs_weaken d hE (c := c) ha
      have hsrc :
          lift c 1 (recCall (.const w2.recRef lsR) pre
            (foldApps (.const w2.ctorRef lsC) fields)) =
          recCall (.const (liftWitness c w2).recRef lsR)
            (pre.map (lift c 1))
            (foldApps (.const (liftWitness c w2).ctorRef lsC)
              (fields.map (lift c 1))) := by
        rw [recCall_lift, lift, foldApps_lift, lift]
        rfl
      rw [hsrc]
      have hpreLen' : (pre'.map (lift c 1)).length =
          (liftWitness c w2).preMajor.length := by
        simp only [liftWitness, List.length_map]; exact hpreLen
      have hfieldsLen' : (fields'.map (lift c 1)).length =
          ((liftWitness c w2).ctorParams ++
            (liftWitness c w2).fields).length := by
        simp only [liftWitness]
        exact map_ctorSpine_length (lift c 1) hfieldsLen
      have hlhs' : iotaLhsOf (liftWitness c w2) =
          recCall (.const (liftWitness c w2).recRef (liftWitness c w2).ls)
            (pre'.map (lift c 1))
            (foldApps (.const (liftWitness c w2).ctorRef (liftWitness c w2).lsC)
              (fields'.map (lift c 1))) := by
        have := congrArg (lift c 1) hlhs
        rw [← iotaLhsOf_lift, recCall_lift, lift, foldApps_lift, lift] at this
        exact this
      rw [← iotaRhsOf_lift c w2]
      exact .iotaSpine _ (liftWitness c w2) lsR lsC hlsR hlsC
        (pre.map (lift c 1)) (pre'.map (lift c 1))
        (fields.map (lift c 1)) (fields'.map (lift c 1))
        hf' ha' hpreLen' hfieldsLen' hlhs'
  | c, _, _, _, .lit Γ t => by
      simp only [lift, natExpand_lift]
      exact .lit _ t

def parRedArgs_weaken (d : LocalDecl) {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {c : Nat} {Γ : LCtx} {xs ys : List (Expr Nat)}
    (h : ParRedArgs E n Γ xs ys) :
    ParRedArgs E n (insertAt d c Γ)
      (xs.map (lift c 1)) (ys.map (lift c 1)) :=
  match h with
  | ParRedArgs.nil Γ => ParRedArgs.nil _
  | ParRedArgs.cons hx t =>
      .cons (parRed_weaken d hE (c := c) hx) (parRedArgs_weaken d hE (h := t))

def parRedStar_weaken (d : LocalDecl) {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) {c : Nat} {Γ : LCtx} {a b : Expr Nat} :
    ParRedStar E n Γ a b →
    ParRedStar E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b)
  | .refl _ e => .refl _ _
  | .tail h hs =>
      .tail (parRed_weaken d hE (c := c) h) (parRedStar_weaken d hE hs)
end

mutual
theorem parRedWeight_pos {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → (h : ParRed E n Γ a b) → 1 ≤ parRedWeight h
  | _, _, _, .refl .. => Nat.le_refl 1
  | _, _, _, .sortEq .. => Nat.le_refl 1
  | _, _, _, .consts .. => Nat.le_refl 1
  | _, _, _, .lit .. => Nat.le_refl 1
  | _, _, _, .bvarZeta _ _ _ _ _ _ hv => by
      have := parRedWeight_pos hv; simp only [parRedWeight]; omega
  | _, _, _, .delta .. => Nat.le_refl 1
  | _, _, _, .app _ _ _ _ _ hf ha => by
      have h1 := parRedWeight_pos hf; have h2 := parRedWeight_pos ha
      simp only [parRedWeight]; omega
  | _, _, _, .lam _ _ _ _ _ hA hb => by
      have h1 := parRedWeight_pos hA; have h2 := parRedWeight_pos hb
      simp only [parRedWeight]; omega
  | _, _, _, .pi _ _ _ _ _ hA hB => by
      have h1 := parRedWeight_pos hA; have h2 := parRedWeight_pos hB
      simp only [parRedWeight]; omega
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb => by
      have h1 := parRedWeight_pos hA; have h2 := parRedWeight_pos hv
      have h3 := parRedWeight_pos hb; simp only [parRedWeight]; omega
  | _, _, _, .zeta _ _ _ _ _ _ _ hA hv hb => by
      have h1 := parRedWeight_pos hA; have h2 := parRedWeight_pos hv
      have h3 := parRedWeight_pos hb; simp only [parRedWeight]; omega
  | _, _, _, .beta _ _ _ _ _ _ _ hA hb ha => by
      have h1 := parRedWeight_pos hA; have h2 := parRedWeight_pos hb
      have h3 := parRedWeight_pos ha; simp only [parRedWeight]; omega
  | _, _, _, .iotaSpine _ _ _ _ _ _ _ _ _ _ hf ha _ _ _ => by
      have h1 := parRedArgsWeight_pos hf; have h2 := parRedArgsWeight_pos ha
      simp only [parRedWeight]; omega

theorem parRedArgsWeight_pos {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {xs ys : List (Expr Nat)} (h : ParRedArgs E n Γ xs ys) :
    1 ≤ parRedArgsWeight h :=
  match h with
  | ParRedArgs.nil _ => Nat.le_refl 1
  | ParRedArgs.cons hx t => by
      have h1 := parRedWeight_pos hx; have h2 := parRedArgsWeight_pos (h := t)
      simp only [parRedArgsWeight]; omega

theorem parRedStarWeight_pos {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {a b : Expr Nat} → (h : ParRedStar E n Γ a b) →
    1 ≤ parRedStarWeight h
  | _, _, _, .refl .. => by
      simp only [parRedStarWeight]
      exact Nat.le_refl 1
  | _, _, _, .tail h hs => by
      have h1 := parRedWeight_pos h; have h2 := parRedStarWeight_pos hs
      simp only [parRedStarWeight]; omega
end

/-- Dummy assumption at the instantiation index. `lookupValue` is
always `none`, so `devel` is insensitive to the stored type. -/
def dummyAssump : LocalDecl := .assumption (.sort .zero)

theorem liftDecl_dummy (k : Nat) : liftDecl k dummyAssump = dummyAssump := rfl

end Rcic.Declarative
