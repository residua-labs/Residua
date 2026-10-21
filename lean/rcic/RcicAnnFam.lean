import rcic.RcicAnnTyRed
import rcic.RcicAnnTel

/-!
# M2-f (3) — the `fam` clause's ingredients on the copy

L-RING C3–C7's structural relation at an inductive family (`research/rcic/
lring-20261003/RcicLR.lean` :245–:500) transplanted onto `ExprA`, BELOW the
relation (`RcicAnnLR` reads these in its `fam` clause), with the changes M2-f (0)
decided: NO Prop disjunct in `FamPhiA` (a Prop-sorted family application is
`IsPropTy` and goes to the prop clause, R-PropOutOfTower), NO universe index (the
copy's `TyKA` carries none), typed TERM reduction `TyHRedStarA` (chains of
`TyHRedA` at the carrier, each step typed — `StepAtA`'s shape) in place of
L-RING's `TyHRedStar`, and the telescope algebra of `RcicAnnTel`.

* `LfpWA Φ ρ A a b` — the least fixed point of an operator on WORLD- and
  CARRIER-INDEXED relations, impredicatively: membership at world `ρ` and carrier
  `A`. The carrier index lets a recursive field of a different index (`Vec α n`
  inside `Vec α (n+1)`) be related at ITS type; the world index lets a position be
  related at another world (R-NoFunRec-1 step 1 (1a)). `LfpWA.fold` / `.unfold` /
  `.ind` for monotone operators.
* `ArgsRelA R X` — two argument lists related along a constructor telescope
  instantiated with the LEFT arguments: a `plain` binder's pair by `R` at its
  position and prefix, a `directRec` binder's pair by the fixed-point variable
  `X` at the binder's domain. `ArgsRelPA R` — the plain walk (the family's own
  telescope: parameters and indices).
* `FamCohA` — index coherence of a constructor form with its carrier, on BOTH
  sides (so that the PER lemmas of the fixed point reuse it as it stands).
* `FamPhiA` — the one-step operator at a carrier that IS a family application:
  conversion at the carrier, and either both sides reduce to the same
  constructor at `=ₙ` levels with `ArgsRelA`-related arguments and `FamCohA`, or
  both reduce to stuck terms (`StuckTmA`: weak-head normal, not constructor-headed).
  `FamPhiWA` — the operator over worlds: at world `ρ`, `FamPhiA` at the context
  weakened to `ρ` with the clause's data at `ρ`.
* `CtorHeadA`, `StuckTmA`, `memberFamRefA`, `WkOk₀A` (the worlds the clause's
  Kripke data range over: the identity, or a well-formed extension).

The clause itself (`EqKA.fam` / `TyKA.fam`) and the re-proofs are `RcicAnnLR`'s
and its consumers' (M2-f (3)); nothing here touches the relation.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) the shape of a family application -/

theorem foldAppsA_const_head (r : Nat) (ls : List Level) (xs : List ExprA) :
    appsSpineA (foldAppsA (.const r ls) xs) = (.const r ls, xs) := by
  rw [appsSpineA_foldAppsA]; rfl

theorem foldAppsA_const_ne_sort (r : Nat) (ls : List Level) (xs : List ExprA) (l : Level) :
    foldAppsA (.const r ls) xs ≠ .sort l := fun h => by
  have := congrArg (fun e => (appsSpineA e).1) h
  simp only [foldAppsA_const_head, appsSpineA] at this
  exact ExprA.noConfusion this

theorem foldAppsA_const_ne_pi (r : Nat) (ls : List Level) (xs : List ExprA) (D : ExprA) (u : Level)
    (C : ExprA) (v : Level) : foldAppsA (.const r ls) xs ≠ .pi D u C v := fun h => by
  have := congrArg (fun e => (appsSpineA e).1) h
  simp only [foldAppsA_const_head, appsSpineA] at this
  exact ExprA.noConfusion this

theorem foldAppsA_const_inj {r r' : Nat} {ls ls' : List Level} {xs xs' : List ExprA}
    (h : foldAppsA (.const r ls) xs = foldAppsA (.const r' ls') xs') :
    r = r' ∧ ls = ls' ∧ xs = xs' := by
  have := congrArg appsSpineA h
  rw [foldAppsA_const_head, foldAppsA_const_head] at this
  injection this with h1 h2
  injection h1 with h11 h12
  exact ⟨h11, h12, h2⟩

/-! ## (1) heads, stuck terms, worlds -/

/-- the head is a constructor member of `E`. -/
def CtorHeadA (E : ResolvedEnvA) (N : ExprA) : Prop :=
  ∃ (c : Nat) (ls : List Level) (m : CheckedMemberA),
    (appsSpineA N).1 = .const c ls ∧ E.members c = some m ∧ m.mclass = .constructorM

/-- a stuck TERM at an inductive type: weak-head normal and not constructor-headed
    (L-RING's `StuckTm`). -/
def StuckTmA (E : ResolvedEnvA) (I : IotaIfaceA) (Γ : LCtxA) (N : ExprA) : Prop :=
  hStepFnA E I.fn Γ N = none ∧ ¬ CtorHeadA E N

/-- the family a constructor belongs to: the head constant of its result type
    (main's `memberFamRef`). -/
def memberFamRefA (cm : CheckedMemberA) : Option Nat := spineHeadRefA (piBodyA cm.mtypeA)

/-- the worlds the clause's Kripke data range over: the identity, or a well-formed
    extension (L-RING's `WkOk₀`). -/
def WkOk₀A (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ : WkSpecA) (Γ : LCtxA) : Prop :=
  ρ = [] ∨ WkOkA E I n ρ Γ

theorem wkOk₀A_nil (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) : WkOk₀A E I n [] Γ :=
  Or.inl rfl

theorem wkOk₀A_of {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ : WkSpecA} {Γ : LCtxA}
    (h : WkOkA E I n ρ Γ) : WkOk₀A E I n ρ Γ := Or.inr h

/-! ## (2) typed term reduction, many steps -/

/-- a typed chain of head steps on TERMS at the type `A`: each step is `TyHRedA`
    at `A`, the source typed at `A` (`StepAtA`'s shape, `RcicAnnLRExp`). -/
inductive TmChainA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (A : ExprA) :
    ExprA → ExprA → Type
  | refl (a : ExprA) (h : HasTyA E I n Γ a A) : TmChainA E I n Γ A a a
  | cons (a a' N : ExprA) (ha : HasTyA E I n Γ a A) (hs : TyHRedA E I n Γ a a' A)
      (t : TmChainA E I n Γ A a' N) : TmChainA E I n Γ A a N

/-- `a` weak-head reduces, typed step by step at `A`, to `N`. -/
def TyHRedStarA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (a N A : ExprA) : Prop :=
  Nonempty (TmChainA E I n Γ A a N)

section Chain
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {A : ExprA}

theorem tmChainA_hasTy_head : {a N : ExprA} → TmChainA E I n Γ A a N → Nonempty (HasTyA E I n Γ a A)
  | _, _, .refl _ h => ⟨h⟩
  | _, _, .cons _ _ _ ha _ _ => ⟨ha⟩

theorem tmChainA_hasTy_end : {a N : ExprA} → TmChainA E I n Γ A a N → Nonempty (HasTyA E I n Γ N A)
  | _, _, .refl _ h => ⟨h⟩
  | _, _, .cons _ _ _ _ _ t => tmChainA_hasTy_end t

/-- a chain is a conversion at `A`: each step's conversion, composed. -/
def tmChainA_conv : {a N : ExprA} → TmChainA E I n Γ A a N → ConvA E I n Γ a N A
  | _, _, .refl a h => .refl Γ a A h
  | _, _, .cons a a' N _ hs t => .trans Γ a a' N A (tyHRedA_conv hs) (tmChainA_conv t)

def tmChainA_trans : {a b N : ExprA} → TmChainA E I n Γ A a b → TmChainA E I n Γ A b N →
    TmChainA E I n Γ A a N
  | _, _, _, .refl _ _, t₂ => t₂
  | _, _, _, .cons a a' b ha hs t₁, t₂ => .cons a a' _ ha hs (tmChainA_trans t₁ t₂)

theorem tyHRedStarA_refl {a : ExprA} (h : HasTyA E I n Γ a A) : TyHRedStarA E I n Γ a a A :=
  ⟨.refl a h⟩

theorem tyHRedStarA_trans {a b N : ExprA} (h₁ : TyHRedStarA E I n Γ a b A)
    (h₂ : TyHRedStarA E I n Γ b N A) : TyHRedStarA E I n Γ a N A :=
  h₁.elim fun t₁ => h₂.elim fun t₂ => ⟨tmChainA_trans t₁ t₂⟩

theorem tyHRedStarA_conv {a N : ExprA} (h : TyHRedStarA E I n Γ a N A) :
    Nonempty (ConvA E I n Γ a N A) :=
  h.elim fun t => ⟨tmChainA_conv t⟩

theorem tyHRedStarA_hasTy_end {a N : ExprA} (h : TyHRedStarA E I n Γ a N A) :
    Nonempty (HasTyA E I n Γ N A) :=
  h.elim fun t => tmChainA_hasTy_end t

theorem tyHRedStarA_hasTy_head {a N : ExprA} (h : TyHRedStarA E I n Γ a N A) :
    Nonempty (HasTyA E I n Γ a A) :=
  h.elim fun t => tmChainA_hasTy_head t

/-- HEAD EXPANSION of a term chain: prepend a typed step at the carrier. -/
theorem tyHRedStarA_cons {a a' N : ExprA} (ha : HasTyA E I n Γ a A) (hs : TyHRedA E I n Γ a a' A)
    (h : TyHRedStarA E I n Γ a' N A) : TyHRedStarA E I n Γ a N A :=
  h.elim fun t => ⟨.cons a a' N ha hs t⟩

/-- ERASURE: a term chain ending at a normal form is a `whnfA` computation. -/
theorem tmChainA_redTo : {a N : ExprA} → TmChainA E I n Γ A a N →
    hStepFnA E I.fn Γ N = none → RedTo E I Γ a N
  | _, _, .refl a _, hN => ⟨0, whnfA_of_normal E I.fn Γ 0 a hN⟩
  | _, _, .cons _ _ _ _ hs t, hN => by
      obtain ⟨fuel, hf⟩ := tmChainA_redTo t hN
      exact ⟨fuel + 1, by simp only [whnfA, tyHRedA_hStep hs]; exact hf⟩

/-- DETERMINISM: two term chains from `a` to normal forms end at the same term
    (`RedTo_det` through erasure, as `whTyA_det` for types). -/
theorem tyHRedStarA_det {a N N' : ExprA} (h : TyHRedStarA E I n Γ a N A)
    (h' : TyHRedStarA E I n Γ a N' A) (hN : hStepFnA E I.fn Γ N = none)
    (hN' : hStepFnA E I.fn Γ N' = none) : N = N' :=
  h.elim fun t => h'.elim fun t' => RedTo_det (tmChainA_redTo t hN) (tmChainA_redTo t' hN')

end Chain

/-- a constructor application is constructor-headed. -/
theorem ctorHeadA_foldAppsA {E : ResolvedEnvA} {c : Nat} {cm : CheckedMemberA} (hcm : E.members c = some cm)
    (hk : cm.mclass = .constructorM) (ls : List Level) (args : List ExprA) :
    CtorHeadA E (foldAppsA (.const c ls) args) :=
  ⟨c, ls, cm, by rw [appsSpineA_foldAppsA]; rfl, hcm, hk⟩

/-- a stuck term is not a constructor application. -/
theorem stuckTmA_not_ctor {E : ResolvedEnvA} {I : IotaIfaceA} {Γ : LCtxA} {c : Nat} {cm : CheckedMemberA}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) {ls : List Level} {args : List ExprA}
    (h : StuckTmA E I Γ (foldAppsA (.const c ls) args)) : False :=
  h.2 (ctorHeadA_foldAppsA hcm hk ls args)

/-! ## (3) the least fixed point on world-indexed carrier relations

R-NoFunRec-1 step 1 (1a): the fixed point ranges over WORLDS (`WkSpecA`). A clause reads its data
at every weakening of its context, and a function-recursive field relates at every weakening too,
so the relation it reads is the fixed point at another world: ONE fixed point over
`WkSpecA → CRelA` serves every position (R-NoFunRec-1 step 1-0). -/

/-- carrier-indexed relations, and operators on them (at one world). -/
abbrev CRelA : Type := ExprA → ExprA → ExprA → Prop
abbrev COpA : Type := CRelA → CRelA

/-- monotonicity of an operator at one world. -/
def MonoA (Φ : COpA) : Prop :=
  ∀ (X Y : CRelA), (∀ A a b, X A a b → Y A a b) → ∀ A a b, Φ X A a b → Φ Y A a b

/-- world-indexed carrier relations, and operators on them. -/
abbrev WRelA : Type := WkSpecA → CRelA
abbrev WOpA : Type := WRelA → WRelA

/-- the least fixed point, impredicatively: `LfpWA Φ ρ A a b` is membership at world `ρ` and
    carrier `A`. -/
def LfpWA (Φ : WOpA) (ρ : WkSpecA) (A a b : ExprA) : Prop :=
  ∀ X : WRelA, (∀ ρ A a b, Φ X ρ A a b → X ρ A a b) → X ρ A a b

/-- monotonicity of a world-indexed operator. -/
def MonoWA (Φ : WOpA) : Prop :=
  ∀ (X Y : WRelA), (∀ ρ A a b, X ρ A a b → Y ρ A a b) → ∀ ρ A a b, Φ X ρ A a b → Φ Y ρ A a b

namespace LfpWA
variable {Φ : WOpA}

theorem ind {X : WRelA} (hX : ∀ ρ A a b, Φ X ρ A a b → X ρ A a b) {ρ : WkSpecA} {A a b : ExprA}
    (h : LfpWA Φ ρ A a b) : X ρ A a b := h X hX

theorem fold (hm : MonoWA Φ) {ρ : WkSpecA} {A a b : ExprA} (h : Φ (LfpWA Φ) ρ A a b) :
    LfpWA Φ ρ A a b :=
  fun X hX => hX ρ A a b (hm _ _ (fun _ _ _ _ hab => hab X hX) ρ A a b h)

theorem unfold (hm : MonoWA Φ) {ρ : WkSpecA} {A a b : ExprA} (h : LfpWA Φ ρ A a b) :
    Φ (LfpWA Φ) ρ A a b :=
  h (fun ρ A a b => Φ (LfpWA Φ) ρ A a b)
    (fun ρ A a b hΦ => hm _ _ (fun _ _ _ _ hab => fold hm hab) ρ A a b hΦ)

end LfpWA

/-! ## (4) the argument walks -/

/-- the plain walk: two argument lists related pointwise along a telescope
    instantiated with the LEFT arguments (the family's own telescope has no
    recursive binder, so this is its whole relatedness; L-RING's `ArgsRelP`). -/
inductive ArgsRelPA (R : Nat → List ExprA → ExprA → ExprA → Prop) :
    Nat → List ExprA → ExprA → List ExprA → List ExprA → Prop
  | nil (i : Nat) (prev : List ExprA) (T : ExprA) : ArgsRelPA R i prev T [] []
  | cons (i : Nat) (prev : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level)
      (f f' : ExprA) (fs fs' : List ExprA) (h : R i prev f f')
      (hs : ArgsRelPA R (i + 1) (prev ++ [f]) (instantiate0A f B) fs fs') :
      ArgsRelPA R i prev (.pi A u B v) (f :: fs) (f' :: fs')

theorem argsRelPA_length {R : Nat → List ExprA → ExprA → ExprA → Prop} {i : Nat}
    {prev : List ExprA} {T : ExprA} {fs fs' : List ExprA} (h : ArgsRelPA R i prev T fs fs') :
    fs.length = fs'.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ _ _ ih => simp [ih]

/-- THE FUNCTION-RECURSIVE POSITION (R-NoFunRec-1 step 1 (1b)): at a binder of domain `A` with `j + 1`
    inner binders, position `i` and prefix `prev`, two functions are related when, at every extension
    `ρ'` in `OK`, inner arguments related along `A` weakened there (by `RI i prev ρ'`, all `j + 1` of them)
    are taken by the weakened functions to a pair of `XF ρ'` at the codomain reached — a Kripke Π into
    `XF`. -/
def FunRelA (RI : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop)
    (XF : WkSpecA → CRelA) (OK : WkSpecA → Prop) :
    Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop :=
  fun i prev A j f f' => ∀ (ρ' : WkSpecA), OK ρ' → ∀ (ys ys' : List ExprA) (C : ExprA),
    ArgsRelPA (RI i prev ρ') 0 [] (wkExprA ρ' A) ys ys' → ys.length = j + 1 →
    applyTelA ys (wkExprA ρ' A) = some C →
    XF ρ' C (foldAppsA (wkExprA ρ' f) ys) (foldAppsA (wkExprA ρ' f') ys')

theorem funRelA_mono {RI : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {XF YF : WkSpecA → CRelA} {OK : WkSpecA → Prop}
    (h : ∀ ρ', OK ρ' → ∀ C a b, XF ρ' C a b → YF ρ' C a b) :
    ∀ i prev A j f f', FunRelA RI XF OK i prev A j f f' → FunRelA RI YF OK i prev A j f f' :=
  fun _ _ _ _ _ _ hF ρ' hρ ys ys' C hw hl hC => h ρ' hρ _ _ _ (hF ρ' hρ ys ys' C hw hl hC)

/-- the pair relation a binder of shape `kd` demands: a non-recursive binder's by the
    position relation `R`; a directly recursive one's (`recursive 0`) by the fixed-point
    variable `X` at the binder's domain; a function-recursive one's (`recursive (j+1)`) by
    `F` at the binder's position, prefix and domain (the fam clause's `F` is a `FunRelA`). -/
def kindRelA (R : Nat → List ExprA → ExprA → ExprA → Prop) (X : CRelA)
    (F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop) (i : Nat)
    (prev : List ExprA) (A : ExprA) : FieldShape → ExprA → ExprA → Prop
  | .nonrecursive, f, f' => R i prev f f'
  | .recursive 0, f, f' => X A f f'
  | .recursive (j + 1), f, f' => F i prev A j f f'

/-- two argument lists related along a constructor telescope, instantiated with
    the LEFT arguments (L-RING's `ArgsRel`): a binder of each shape by its `kindRelA`. -/
inductive ArgsRelA (R : Nat → List ExprA → ExprA → ExprA → Prop) (X : CRelA)
    (F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop) :
    Nat → List ExprA → ExprA → List FieldShape → List ExprA → List ExprA → Prop
  | nil (i : Nat) (prev : List ExprA) (T : ExprA) : ArgsRelA R X F i prev T [] [] []
  | plain (i : Nat) (prev : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level)
      (f f' : ExprA) (ks : List FieldShape) (fs fs' : List ExprA) (h : R i prev f f')
      (hs : ArgsRelA R X F (i + 1) (prev ++ [f]) (instantiate0A f B) ks fs fs') :
      ArgsRelA R X F i prev (.pi A u B v) (FieldShape.nonrecursive :: ks) (f :: fs) (f' :: fs')
  | directRec (i : Nat) (prev : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level)
      (f f' : ExprA) (ks : List FieldShape) (fs fs' : List ExprA) (h : X A f f')
      (hs : ArgsRelA R X F (i + 1) (prev ++ [f]) (instantiate0A f B) ks fs fs') :
      ArgsRelA R X F i prev (.pi A u B v) ((FieldShape.recursive 0) :: ks) (f :: fs) (f' :: fs')
  | funRec (i : Nat) (prev : List ExprA) (A : ExprA) (u : Level) (B : ExprA) (v : Level)
      (f f' : ExprA) (j : Nat) (ks : List FieldShape) (fs fs' : List ExprA) (h : F i prev A j f f')
      (hs : ArgsRelA R X F (i + 1) (prev ++ [f]) (instantiate0A f B) ks fs fs') :
      ArgsRelA R X F i prev (.pi A u B v) ((FieldShape.recursive (j + 1)) :: ks) (f :: fs) (f' :: fs')

theorem argsRelA_mono {R : Nat → List ExprA → ExprA → ExprA → Prop} {X Y : CRelA}
    {F G : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    (hXY : ∀ A a b, X A a b → Y A a b) (hFG : ∀ i prev A j f f', F i prev A j f f' → G i prev A j f f')
    {i : Nat} {prev : List ExprA} {T : ExprA}
    {ks : List FieldShape} {fs fs' : List ExprA} (h : ArgsRelA R X F i prev T ks fs fs') :
    ArgsRelA R Y G i prev T ks fs fs' := by
  induction h with
  | nil i prev T => exact .nil i prev T
  | plain i prev A u B v f f' ks fs fs' h _ ih => exact .plain i prev A u B v f f' ks fs fs' h ih
  | directRec i prev A u B v f f' ks fs fs' h _ ih =>
      exact .directRec i prev A u B v f f' ks fs fs' (hXY A f f' h) ih
  | funRec i prev A u B v f f' j ks fs fs' h _ ih =>
      exact .funRec i prev A u B v f f' j ks fs fs' (hFG i prev A j f f' h) ih

theorem argsRelA_length {R : Nat → List ExprA → ExprA → ExprA → Prop} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    {i : Nat} {prev : List ExprA} {T : ExprA} {ks : List FieldShape} {fs fs' : List ExprA}
    (h : ArgsRelA R X F i prev T ks fs fs') : fs.length = ks.length ∧ fs'.length = ks.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | plain _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ⟨by simp [ih.1], by simp [ih.2]⟩
  | directRec _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ⟨by simp [ih.1], by simp [ih.2]⟩
  | funRec _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-- extend a plain walk by one binder at its end. -/
theorem argsRelPA_snoc {R : Nat → List ExprA → ExprA → ExprA → Prop} :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {pre pre' : List ExprA}
      (_ : ArgsRelPA R i prev T pre pre') {A : ExprA} {u : Level} {B : ExprA} {v : Level} {f f' : ExprA}
      (_ : applyTelA pre T = some (.pi A u B v))
      (_ : R (i + pre.length) (prev ++ pre) f f'),
      ArgsRelPA R i prev T (pre ++ [f]) (pre' ++ [f']) := by
  intro i prev T pre pre' h
  induction h with
  | nil i prev T =>
      intro A u B v f f' hT hrel
      simp only [applyTelA] at hT
      injection hT with hT
      subst hT
      exact .cons i prev A u B v f f' [] [] (by simpa using hrel) (.nil _ _ _)
  | cons i prev A₀ u₀ B₀ v₀ g g' gs gs' hg _ ih =>
      intro A u B v f f' hT hrel
      simp only [applyTelA] at hT
      have hrel' : R (i + 1 + gs.length) (prev ++ [g] ++ gs) f f' := by
        simp only [List.length_cons, List.append_assoc, List.singleton_append] at hrel ⊢
        have e : i + 1 + gs.length = i + (gs.length + 1) := by omega
        rw [e]; exact hrel
      exact .cons i prev A₀ u₀ B₀ v₀ g g' (gs ++ [f]) (gs' ++ [f']) hg (ih hT hrel')

/-- the telescope after one more argument. -/
theorem applyTelA_snoc (pre : List ExprA) (T : ExprA) {A : ExprA} {u : Level} {B : ExprA}
    {v : Level} {f : ExprA} (h : applyTelA pre T = some (.pi A u B v)) :
    applyTelA (pre ++ [f]) T = some (instantiate0A f B) := by
  induction pre generalizing T with
  | nil =>
      simp only [applyTelA] at h
      cases h
      rfl
  | cons g pre ih =>
      cases T with
      | pi A₀ u₀ B₀ v₀ => exact ih (instantiate0A g B₀) h
      | bvar _ => exact Option.noConfusion h
      | sort _ => exact Option.noConfusion h
      | const _ _ => exact Option.noConfusion h
      | app _ _ => exact Option.noConfusion h
      | lam _ _ _ => exact Option.noConfusion h
      | letE _ _ _ => exact Option.noConfusion h
      | lit _ => exact Option.noConfusion h

/-- a telescope applied to a concatenation: the first list, then the second. -/
theorem applyTelA_append : (xs ys : List ExprA) → (T : ExprA) →
    applyTelA (xs ++ ys) T = (applyTelA xs T).bind (applyTelA ys)
  | [], _, _ => rfl
  | x :: xs, ys, .pi _ _ B _ => applyTelA_append xs ys (instantiate0A x B)
  | _ :: _, _, .bvar _ => rfl
  | _ :: _, _, .sort _ => rfl
  | _ :: _, _, .const _ _ => rfl
  | _ :: _, _, .app _ _ => rfl
  | _ :: _, _, .lam _ _ _ => rfl
  | _ :: _, _, .letE _ _ _ => rfl
  | _ :: _, _, .lit _ => rfl

/-- success on a concatenation: success on the first list, then on the second. -/
theorem applyTelA_append_some {xs ys : List ExprA} {T R : ExprA}
    (h : applyTelA (xs ++ ys) T = some R) : ∃ T', applyTelA xs T = some T' ∧ applyTelA ys T' = some R := by
  rw [applyTelA_append] at h
  cases h0 : applyTelA xs T with
  | none => rw [h0] at h; cases h
  | some T' => rw [h0] at h; exact ⟨T', rfl, h⟩

/-- a plain walk transfers between two position relations that agree on every
    doubly-related prefix (walks from the start `(i₀, prev₀, T₀)`; M2-f (4a): the
    family telescope is walked from the carrier's parameters). -/
theorem argsRelPA_transfer {R₁ R₂ : Nat → List ExprA → ExprA → ExprA → Prop} {i₀ : Nat}
    {prev₀ : List ExprA} {T₀ : ExprA}
    (hU : ∀ (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      ArgsRelPA R₁ i₀ prev₀ T₀ pre pre' → ArgsRelPA R₂ i₀ prev₀ T₀ pre pre' →
      applyTelA pre T₀ = some (.pi D uD C vC) →
      R₁ (i₀ + pre.length) (prev₀ ++ pre) = R₂ (i₀ + pre.length) (prev₀ ++ pre)) :
    ∀ {i : Nat} {prev pre pre' : List ExprA} {T : ExprA} {xs xs' : List ExprA},
      ArgsRelPA R₁ i prev T xs xs' → i = i₀ + pre.length → prev = prev₀ ++ pre →
      applyTelA pre T₀ = some T →
      ArgsRelPA R₁ i₀ prev₀ T₀ pre pre' → ArgsRelPA R₂ i₀ prev₀ T₀ pre pre' →
      ArgsRelPA R₂ i prev T xs xs' := by
  intro i prev pre pre' T xs xs' h
  induction h generalizing pre pre' with
  | nil i prev T => intro _ _ _ _ _; exact .nil i prev T
  | cons i prev A u B v f f' fs fs' hf _ ih =>
      intro hi hprev hT hp1 hp2
      subst hi; subst hprev
      have heq := hU pre pre' A u B v hp1 hp2 hT
      have hf' : R₂ (i₀ + pre.length) (prev₀ ++ pre) f f' := by rw [← heq]; exact hf
      have hp1' := argsRelPA_snoc hp1 (f := f) (f' := f') hT hf
      have hp2' := argsRelPA_snoc hp2 (f := f) (f' := f') hT hf'
      exact .cons (i₀ + pre.length) (prev₀ ++ pre) A u B v f f' fs fs' hf'
        (ih (pre := pre ++ [f]) (pre' := pre' ++ [f']) (by simp; omega) (by simp)
          (applyTelA_snoc pre T₀ hT) hp1' hp2')

/-- a binder's pair relation one walk step later: the position shifted past the step's argument. -/
theorem kindRelA_shift {R : Nat → List ExprA → ExprA → ExprA → Prop} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    {i : Nat} {prev : List ExprA} {g : ExprA} {ks : List FieldShape} {gs : List ExprA}
    {A : ExprA} {kd : FieldShape} {f f' : ExprA}
    (hrel : kindRelA R X F (i + (ks.length + 1)) (prev ++ (g :: gs)) A kd f f') :
    kindRelA R X F (i + 1 + ks.length) (prev ++ [g] ++ gs) A kd f f' := by
  have e1 : i + 1 + ks.length = i + (ks.length + 1) := by omega
  have e2 : prev ++ [g] ++ gs = prev ++ (g :: gs) := by simp
  rw [e1, e2]; exact hrel

/-- extend a prefix walk by one binder at its end. -/
theorem argsRelA_snoc {R : Nat → List ExprA → ExprA → ExprA → Prop} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {ksPre : List FieldShape} {pre pre' : List ExprA}
      (_ : ArgsRelA R X F i prev T ksPre pre pre') {A : ExprA} {u : Level} {B : ExprA} {v : Level}
      {f f' : ExprA} (kd : FieldShape) (_ : applyTelA pre T = some (.pi A u B v))
      (_ : kindRelA R X F (i + ksPre.length) (prev ++ pre) A kd f f'),
      ArgsRelA R X F i prev T (ksPre ++ [kd]) (pre ++ [f]) (pre' ++ [f']) := by
  intro i prev T ksPre pre pre' h
  induction h with
  | nil i prev T =>
      intro A u B v f f' kd hT hrel
      simp only [applyTelA] at hT
      cases hT
      cases kd using FieldShape.cases3 with
      | plain =>
          simp only [kindRelA, List.length_nil, Nat.add_zero, List.append_nil] at hrel
          exact .plain i prev A u B v f f' [] [] [] hrel (.nil _ _ _)
      | directRec => exact .directRec i prev A u B v f f' [] [] [] hrel (.nil _ _ _)
      | funRec j =>
          simp only [kindRelA, List.length_nil, Nat.add_zero, List.append_nil] at hrel
          exact .funRec i prev A u B v f f' j [] [] [] hrel (.nil _ _ _)
  | plain i prev A₀ u₀ B₀ v₀ g g' ks gs gs' hg _ ih =>
      intro A u B v f f' kd hT hrel
      have hT' : applyTelA gs (instantiate0A g B₀) = some (.pi A u B v) := hT
      exact .plain i prev A₀ u₀ B₀ v₀ g g' (ks ++ [kd]) (gs ++ [f]) (gs' ++ [f']) hg
        (ih kd hT' (kindRelA_shift hrel))
  | directRec i prev A₀ u₀ B₀ v₀ g g' ks gs gs' hg _ ih =>
      intro A u B v f f' kd hT hrel
      have hT' : applyTelA gs (instantiate0A g B₀) = some (.pi A u B v) := hT
      exact .directRec i prev A₀ u₀ B₀ v₀ g g' (ks ++ [kd]) (gs ++ [f]) (gs' ++ [f']) hg
        (ih kd hT' (kindRelA_shift hrel))
  | funRec i prev A₀ u₀ B₀ v₀ g g' j₀ ks gs gs' hg _ ih =>
      intro A u B v f f' kd hT hrel
      have hT' : applyTelA gs (instantiate0A g B₀) = some (.pi A u B v) := hT
      exact .funRec i prev A₀ u₀ B₀ v₀ g g' j₀ (ks ++ [kd]) (gs ++ [f]) (gs' ++ [f']) hg
        (ih kd hT' (kindRelA_shift hrel))

theorem map_wkExprA_nil (ps : List ExprA) : ps.map (wkExprA []) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons, ih]; rfl

/-- two worlds in a row on a list: the composed world. -/
theorem map_wkExprA_comp (σ ρ : WkSpecA) (ps : List ExprA) :
    (ps.map (wkExprA σ)).map (wkExprA ρ) = ps.map (wkExprA (WkSpecA.comp σ ρ)) := by
  rw [List.map_map]
  congr 1
  funext e
  exact (wkExprA_comp σ ρ e).symm

/-- three worlds in a row: the composition is associative. -/
theorem WkSpecA.comp_assoc : (σ ρ ρ' : WkSpecA) →
    WkSpecA.comp (WkSpecA.comp σ ρ) ρ' = WkSpecA.comp σ (WkSpecA.comp ρ ρ')
  | [], _, _ => rfl
  | (d, c) :: σ, ρ, ρ' => congrArg (fun τ => (d, c) :: τ) (WkSpecA.comp_assoc σ ρ ρ')

/-- a clause world, then a well-formed extension of it: a clause world (R-NoFunRec-1 step 1 (1b)). -/
theorem wkOk₀A_comp_ext {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {ρ ρ' : WkSpecA}
    (hρ : WkOk₀A E I n ρ Γ) (hρ' : WkOkA E I n ρ' (wkCtxA ρ Γ)) : WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ := by
  rcases hρ with rfl | hρ
  · exact Or.inr hρ'
  · exact Or.inr (wkOkA_comp hρ hρ')

/-! ## (4b) `=ₙ` on level lists (moved from `RcicAnnFamPer`, M2-f (3c)) -/

theorem eqNListA_refl : (ls : List Level) → eqNList ls ls
  | [] => True.intro
  | _ :: ls => ⟨fun _ => rfl, eqNListA_refl ls⟩

theorem eqNListA_symm : {ls ls' : List Level} → eqNList ls ls' → eqNList ls' ls
  | [], [], _ => True.intro
  | _ :: _, _ :: _, h => ⟨eqNA_symm h.1, eqNListA_symm h.2⟩
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

theorem eqNListA_trans : {ls₁ ls₂ ls₃ : List Level} → eqNList ls₁ ls₂ → eqNList ls₂ ls₃ →
    eqNList ls₁ ls₃
  | [], [], [], _, _ => True.intro
  | _ :: _, _ :: _, _ :: _, h₁, h₂ => ⟨eqNA_trans h₁.1 h₂.1, eqNListA_trans h₁.2 h₂.2⟩
  | [], [], _ :: _, _, h => False.elim h
  | [], _ :: _, _, h, _ => False.elim h
  | _ :: _, [], _, h, _ => False.elim h
  | _ :: _, _ :: _, [], _, h => False.elim h

theorem eqNListA_length : {ls ls' : List Level} → eqNList ls ls' → ls.length = ls'.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg Nat.succ (eqNListA_length h.2)
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

/-! ## (4c) the bounded tie (M2-f (3d))

`=ₙ` does not bound parameters (M2-f (4b)-1: `[imax (param 0) zero] =ₙ [zero]`), and a type
instantiated at an unbounded list is untypeable at the arity. The clause's data instantiate types
at the RIGHT list of each tie, so those ties are `eqNListB`: `=ₙ` with the right list bounded. -/

/-- `=ₙ`, with the right list bounded at the arity. -/
def eqNListB (n : Nat) (ls ls' : List Level) : Prop := eqNList ls ls' ∧ levelsBounded n ls' = true

theorem eqNListB_trans {n : Nat} {l₁ l₂ l₃ : List Level} (h₁ : eqNListB n l₁ l₂)
    (h₂ : eqNListB n l₂ l₃) : eqNListB n l₁ l₃ :=
  ⟨eqNListA_trans h₁.1 h₂.1, h₂.2⟩

theorem eqNListB_refl {n : Nat} {ls : List Level} (hb : levelsBounded n ls = true) :
    eqNListB n ls ls :=
  ⟨eqNListA_refl ls, hb⟩

theorem eqNListB_symm {n : Nat} {ls ls' : List Level} (h : eqNListB n ls ls')
    (hb : levelsBounded n ls = true) : eqNListB n ls' ls :=
  ⟨eqNListA_symm h.1, hb⟩

/-- `=ₙ`, with BOTH lists bounded: the step's carrier tie. The carrier's own list feeds the
    index relation (`RsF`), the constructor's the field relation (`Rs`). -/
def eqNListBB (n : Nat) (ls ls' : List Level) : Prop := eqNListB n ls ls' ∧ levelsBounded n ls = true

/-- every constant's level list bounded at the arity (moved from `RcicAnnFamClause`, M2-f (3d)). -/
def ConstsBoundedA (n : Nat) : ExprA → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const _ ls => levelsBounded n ls = true
  | .app f x => ConstsBoundedA n f ∧ ConstsBoundedA n x
  | .lam a _ b => ConstsBoundedA n a ∧ ConstsBoundedA n b
  | .pi a _ b _ => ConstsBoundedA n a ∧ ConstsBoundedA n b
  | .letE a w b => ConstsBoundedA n a ∧ ConstsBoundedA n w ∧ ConstsBoundedA n b
  | .lit _ => True

section Bounded
variable {E : ResolvedEnvA} {I : IotaIfaceA}

/-- a typed term's constants are bounded at the arity (the `const` rule's `hwf`). -/
theorem hasTyA_constsBounded {n : Nat} :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E I n Γ e A → ConstsBoundedA n e
  | _, _, _, .sort _ _ => trivial
  | _, _, _, .bvar _ _ _ _ _ _ => trivial
  | _, _, _, .const _ _ _ _ _ _ _ hwf _ => hwf
  | _, _, _, .pi _ _ _ _ _ hA hB => ⟨hasTyA_constsBounded hA, hasTyA_constsBounded hB⟩
  | _, _, _, .lam _ _ _ _ _ _ hA _ hbody => ⟨hasTyA_constsBounded hA, hasTyA_constsBounded hbody⟩
  | _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf ha => ⟨hasTyA_constsBounded hf, hasTyA_constsBounded ha⟩
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv _ hb =>
      ⟨hasTyA_constsBounded hA, hasTyA_constsBounded hv, hasTyA_constsBounded hb⟩
  | _, _, _, .lit _ _ _ _ => trivial
  | _, _, _, .conv _ _ _ _ _ _ h _ _ _ _ => hasTyA_constsBounded h

/-- a spine's constants include its head's. -/
theorem constsBoundedA_foldAppsA {n : Nat} : (xs : List ExprA) → {f : ExprA} →
    ConstsBoundedA n (foldAppsA f xs) → ConstsBoundedA n f
  | [], _, h => h
  | x :: xs, f, h => (constsBoundedA_foldAppsA xs (f := .app f x) h).1

/-- the head constant of a TYPED family or constructor application is bounded. -/
theorem hasTyA_foldAppsA_const_bounded {n : Nat} {Γ : LCtxA} {r : Nat} {ls : List Level}
    {xs : List ExprA} {A : ExprA} (h : HasTyA E I n Γ (foldAppsA (.const r ls) xs) A) :
    levelsBounded n ls = true :=
  constsBoundedA_foldAppsA xs (hasTyA_constsBounded h)

/-- a type that reduces to a family application: the application's levels are bounded. -/
theorem whTyA_famApp_bounded {n : Nat} {Γ : LCtxA} {A : ExprA} {r : Nat} {ls : List Level}
    {xs : List ExprA} (h : WhTyA E I n Γ A (foldAppsA (.const r ls) xs)) : levelsBounded n ls = true := by
  obtain ⟨_, ⟨hT⟩⟩ := whTyA_hasTy_end h
  exact hasTyA_foldAppsA_const_bounded hT

end Bounded

/-! ## (4b) parameter conversions (M2-f (6))

Two argument lists along a telescope, pointwise convertible at the domains the LEFT prefix reaches
(`ConvArgsA`, the copy's `ConvArgs`); and the same with, at every step, the left domain convertible
with the one the right prefix reaches (`ParConvA`). The clause carries parameter pairs this way, as
conversions, because relating them at the clause's height is the over-demand M2-f (3c) removed. Symmetry,
transitivity and the rebase of a pointwise list are structural: the domain conversions retype each
step. -/

/-- arguments pointwise convertible along a telescope: each pair at the domain the LEFT prefix
    reaches. -/
inductive ConvArgsA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    ExprA → List ExprA → List ExprA → Prop
  | nil (T : ExprA) : ConvArgsA E I n Γ T [] []
  | cons (A : ExprA) (u : Level) (B : ExprA) (v : Level) (f f' : ExprA) (fs fs' : List ExprA)
      (h : Nonempty (ConvA E I n Γ f f' A)) (hs : ConvArgsA E I n Γ (instantiate0A f B) fs fs') :
      ConvArgsA E I n Γ (.pi A u B v) (f :: fs) (f' :: fs')

/-- two argument lists along two telescopes: each pair convertible at the LEFT domain, and the left
    domain convertible with the right one. -/
inductive ParConvA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    ExprA → ExprA → List ExprA → List ExprA → Prop
  | nil (T T' : ExprA) : ParConvA E I n Γ T T' [] []
  | cons (A : ExprA) (u : Level) (B : ExprA) (v : Level) (A' : ExprA) (u' : Level) (B' : ExprA)
      (v' : Level) (f f' : ExprA) (fs fs' : List ExprA)
      (h : Nonempty (ConvA E I n Γ f f' A)) (hd : Nonempty (TyConvA E I n Γ A A'))
      (hs : ParConvA E I n Γ (instantiate0A f B) (instantiate0A f' B') fs fs') :
      ParConvA E I n Γ (.pi A u B v) (.pi A' u' B' v') (f :: fs) (f' :: fs')

section ParConv
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

theorem convArgsA_length {T : ExprA} {fs fs' : List ExprA}
    (h : ConvArgsA E I n Γ T fs fs') : fs.length = fs'.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ih => simp only [List.length_cons, ih]

theorem parConvA_length {T T' : ExprA} {fs fs' : List ExprA}
    (h : ParConvA E I n Γ T T' fs fs') : fs.length = fs'.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => simp only [List.length_cons, ih]

/-- a two-sided list is pointwise convertible at its left telescope. -/
theorem parConvA_convArgsA {T T' : ExprA} {fs fs' : List ExprA}
    (h : ParConvA E I n Γ T T' fs fs') : ConvArgsA E I n Γ T fs fs' := by
  induction h with
  | nil T _ => exact .nil T
  | cons A u B v _ _ _ _ f f' _ _ hc _ _ ih => exact .cons A u B v f f' _ _ hc ih

/-- a list pointwise convertible with ITSELF along a telescope (its typing) is two-sided with the
    same domains. -/
theorem parConvA_refl {T : ExprA} {fs : List ExprA} :
    ConvArgsA E I n Γ T fs fs → ParConvA E I n Γ T T fs fs
  | .nil T => .nil T T
  | .cons A u B v f _ fs _ hc hs => .cons A u B v A u B v f f fs fs hc ⟨.refl Γ A⟩ (parConvA_refl hs)

theorem parConvA_symm {T T' : ExprA} {fs fs' : List ExprA} :
    ParConvA E I n Γ T T' fs fs' → ParConvA E I n Γ T' T fs' fs
  | .nil T T' => .nil T' T
  | .cons A u B v A' u' B' v' f f' fs fs' hc hd hs =>
      .cons A' u' B' v' A u B v f' f fs' fs
        (hc.elim fun c => hd.elim fun d => ⟨convA_of_tyConvA (.symm _ _ _ _ c) d⟩)
        (hd.elim fun d => ⟨d.symm⟩) (parConvA_symm hs)

theorem parConvA_trans {T T' T'' : ExprA} {fs fs' fs'' : List ExprA} :
    ParConvA E I n Γ T T' fs fs' → ParConvA E I n Γ T' T'' fs' fs'' → ParConvA E I n Γ T T'' fs fs''
  | .nil T _, .nil _ T'' => .nil T T''
  | .cons A u B v A' u' B' v' f f' fs fs' hc hd hs,
    .cons _ _ _ _ A'' u'' B'' v'' _ f'' _ fs'' hc' hd' hs' =>
      .cons A u B v A'' u'' B'' v'' f f'' fs fs''
        (hc.elim fun c => hc'.elim fun c' => hd.elim fun d =>
          ⟨.trans _ _ _ _ _ c (convA_of_tyConvA c' d.symm)⟩)
        (hd.elim fun d => hd'.elim fun d' => ⟨.trans _ _ _ _ d d'⟩) (parConvA_trans hs hs')

/-- THE REBASE: a list pointwise convertible from `xs`, moved to a second list `zs` two-sided with
    `xs`, is pointwise convertible from `zs` at the second telescope. -/
theorem convArgsA_rebase {T T' : ExprA} {xs zs ys : List ExprA} :
    ParConvA E I n Γ T T' xs zs → ConvArgsA E I n Γ T xs ys → ConvArgsA E I n Γ T' zs ys
  | .nil _ T', .nil _ => .nil T'
  | .cons A u B v A' u' B' v' x z xs zs hxz hd hs, .cons _ _ _ _ _ y _ ys hxy hrest =>
      .cons A' u' B' v' z y zs ys
        (hxz.elim fun c => hxy.elim fun c' => hd.elim fun d =>
          ⟨convA_of_tyConvA (.trans _ _ _ _ _ (.symm _ _ _ _ c) c') d⟩)
        (convArgsA_rebase hs hrest)

theorem parConvA_append : ∀ {T T' : ExprA} {xs xs' ys ys' : List ExprA} {U U' : ExprA},
    ParConvA E I n Γ T T' xs xs' → applyTelA xs T = some U → applyTelA xs' T' = some U' →
    ParConvA E I n Γ U U' ys ys' → ParConvA E I n Γ T T' (xs ++ ys) (xs' ++ ys')
  | _, _, _, _, _, _, _, _, .nil _ _, hU, hU', hy => by
      injection hU with hU
      injection hU' with hU'
      subst hU
      subst hU'
      exact hy
  | _, _, _, _, _, _, _, _, .cons A u B v A' u' B' v' f f' _ _ hc hd hs, hU, hU', hy =>
      .cons A u B v A' u' B' v' f f' _ _ hc hd (parConvA_append hs hU hU' hy)

/-- a pointwise conversion reaches an instance of its telescope. -/
theorem convArgsA_applyTel : ∀ {T : ExprA} {xs xs' : List ExprA},
    ConvArgsA E I n Γ T xs xs' → ∃ U, applyTelA xs T = some U
  | _, _, _, .nil T => ⟨T, rfl⟩
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ hs => by
      obtain ⟨U, hU⟩ := convArgsA_applyTel hs
      exact ⟨U, hU⟩

theorem convArgsA_append : ∀ {T : ExprA} {xs xs' ys ys' : List ExprA} {U : ExprA},
    ConvArgsA E I n Γ T xs xs' → applyTelA xs T = some U → ConvArgsA E I n Γ U ys ys' →
    ConvArgsA E I n Γ T (xs ++ ys) (xs' ++ ys')
  | _, _, _, _, _, _, .nil _, hU, hy => by
      injection hU with hU
      subst hU
      exact hy
  | _, _, _, _, _, _, .cons A u B v f f' _ _ hc hs, hU, hy =>
      .cons A u B v f f' _ _ hc (convArgsA_append hs hU hy)

end ParConv

/-! ## (5) index coherence and the operator

M2-f (3c): a family application's walks start AFTER its own parameters (L-RING D2).
The constructor fields are walked along the constructor telescope instantiated at
the CARRIER's parameters, the indices along the family telescope instantiated
likewise, and the level lists are tied to the carrier's (`=ₙ`): no parameter domain
and no other universe instance is ever asked for at the clause's height (M2-f (3c)-0
measured both over-demands on the clause of M2-f (3b); `RcicAnnFamHeight` pins the
repaired clause's acceptance and the large-index boundary that remains). The family's
parameter count is `m.nparamsA`. -/

/-- the carrier's parameters: the first `nparamsA` arguments of its spine. -/
def carrierParamsA (m : CheckedMemberA) (A : ExprA) : List ExprA :=
  (appsSpineA A).2.take m.nparamsA

/-- the carrier's level list: its head constant's. -/
def carrierLevelsA (A : ExprA) : List Level :=
  match (appsSpineA A).1 with
  | .const _ ls => ls
  | _ => []

theorem carrierParamsA_foldAppsA (m : CheckedMemberA) (r : Nat) (ls : List Level)
    (xs : List ExprA) : carrierParamsA m (foldAppsA (.const r ls) xs) = xs.take m.nparamsA := by
  simp only [carrierParamsA, foldAppsA_const_head]

theorem carrierLevelsA_foldAppsA (r : Nat) (ls : List Level) (xs : List ExprA) :
    carrierLevelsA (foldAppsA (.const r ls) xs) = ls := by
  simp only [carrierLevelsA, foldAppsA_const_head]

/-- a recursive binder's pair: the fixed-point variable at the binder's domain, which
    stays in the carrier's FIBER (the same parameters, `=ₙ` levels) — for an admitted
    constructor that is the 05 §8 shape (exact parameters, canonical levels); for any
    other member of `E` it only makes the fixed point smaller. -/
def famRecRelA (m : CheckedMemberA) (ps : List ExprA) (ls : List Level) (X : CRelA) : CRelA :=
  fun C f f' => carrierParamsA m C = ps ∧ eqNList (carrierLevelsA C) ls ∧ X C f f'

theorem famRecRelA_mono {m : CheckedMemberA} {ps : List ExprA} {ls : List Level} {X Y : CRelA}
    (hXY : ∀ A a b, X A a b → Y A a b) : ∀ A a b, famRecRelA m ps ls X A a b →
      famRecRelA m ps ls Y A a b :=
  fun A a b h => ⟨h.1, h.2.1, hXY A a b h.2.2⟩

/-- THE DECLARED PAIR of a function-recursive position (R-NoFunRec-1 step 1 (1c-ε2d-L2)): the two fields
    typed and convertible at the position's declared domain `d`. It mentions no fixed-point variable. -/
abbrev DeclPairA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (d f f' : ExprA) : Prop :=
  Nonempty (HasTyA E I n Γ f d) ∧ Nonempty (HasTyA E I n Γ f' d) ∧ Nonempty (ConvA E I n Γ f f' d)

/-- the fam clause's function-recursive positions at one world (context `Γ`, R-NoFunRec-1 step 1 (1b)):
    `FunRelA` over the well-formed extensions of `Γ`, the fixed point at an extension (`XF ρ'`) read in
    the carrier's fiber weakened there. (1c-ε2d-L2): the function-recursive position carries the pair's
    typing and conversion at its declared domain, as the plain and directly recursive positions do. -/
abbrev famFunRelA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (m : CheckedMemberA)
    (RI : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop)
    (ps : List ExprA) (ls : List Level) (XF : WkSpecA → CRelA) :
    Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop :=
  fun i prev A j f f' =>
    FunRelA RI (fun ρ' => famRecRelA m (ps.map (wkExprA ρ')) ls (XF ρ')) (fun ρ' => WkOkA E I n ρ' Γ)
      i prev A j f f' ∧ DeclPairA E I n Γ A f f'

theorem famFunRelA_mono {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {m : CheckedMemberA}
    {RI : Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {ps ps₂ : List ExprA} {ls ls₂ : List Level} {XF XF₂ : WkSpecA → CRelA}
    (h : ∀ ρ', WkOkA E I n ρ' Γ → ∀ C a b, famRecRelA m (ps.map (wkExprA ρ')) ls (XF ρ') C a b →
      famRecRelA m (ps₂.map (wkExprA ρ')) ls₂ (XF₂ ρ') C a b) :
    ∀ i prev A j f f', famFunRelA E I n Γ m RI ps ls XF i prev A j f f' →
      famFunRelA E I n Γ m RI ps₂ ls₂ XF₂ i prev A j f f' :=
  fun _ _ _ _ _ _ hF => ⟨funRelA_mono h _ _ _ _ _ _ hF.1, hF.2⟩

/-- index coherence of a constructor form with its carrier, on BOTH sides: the
    carrier is `I lsA (ps ++ is)` (`ps` its `nparamsA` parameters); the constructor's
    declared result after the LEFT fields (along its telescope at the carrier's
    parameters) is `I lsR (ps ++ isR)` and after the RIGHT fields `I lsR' (ps ++ isR')`
    — the carrier's parameters exactly (05 §6, rule 3) — the levels agree `=ₙ` with
    the carrier's and both result index lists are RELATED to the carrier's along the
    family telescope from the carrier's parameters (`ArgsRelPA` with the clause's
    `RsF`). -/
def FamCohA (r : Nat) (mF : CheckedMemberA)
    (RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop) (A : ExprA)
    (args : List ExprA) (T : ExprA) (args' : List ExprA) (T' : ExprA) : Prop :=
  ∃ (lsA lsR lsR' : List Level) (xsA isR isR' : List ExprA) (TF R R' : ExprA),
    appsSpineA A = (.const r lsA, xsA) ∧
    applyTelA (xsA.take mF.nparamsA) (instantiateLevelsA lsA mF.mtypeA) = some TF ∧
    applyTelA args T = some R ∧ appsSpineA R = (.const r lsR, xsA.take mF.nparamsA ++ isR) ∧
    eqNList lsA lsR ∧
    ArgsRelPA (RsF lsA) mF.nparamsA (xsA.take mF.nparamsA) TF (xsA.drop mF.nparamsA) isR ∧
    applyTelA args' T' = some R' ∧ appsSpineA R' = (.const r lsR', xsA.take mF.nparamsA ++ isR') ∧
    eqNList lsA lsR' ∧
    ArgsRelPA (RsF lsA) mF.nparamsA (xsA.take mF.nparamsA) TF (xsA.drop mF.nparamsA) isR'

/-- the one-step operator of the structural relation at a carrier that IS a family
    application `I ls (ps ++ is)`: conversion at the carrier, and either both sides
    reduce (typed, at the carrier) to the same constructor at levels `=ₙ` the
    carrier's, with fields `ArgsRelA`-related along the constructor telescope at the
    CARRIER's parameters (the reducts' own parameter arguments are not walked; their
    typing at the carrier is what relates them), coherent indices, the shapes through
    erasure (`ctorShapesA r nparamsA`, the fields; R-NoFunRec-1 step 1 (1b)), both constructor forms weak-head
    normal (M2-f (3b)) — or both reduce to stuck terms. NO Prop disjunct (M2-f (0)).
    The carrier's and both constructors' level lists are bounded at the arity (M2-f (3d)):
    the index relation is read at the carrier's, the field relation at the constructor's.
    THE PARAMETER COHERENCE (P2, M2-f (6)): each form's own parameters are convertible with the
    carrier's, pointwise along the family's telescope at the form's levels. It moves across related
    carriers with the clause's parameter conversions; its reader is the recursors' clause (M2-f (6c)). -/
def FamPhiA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat)
    (m : CheckedMemberA)
    (Rs : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsI : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop)
    (X : CRelA) (XF : WkSpecA → CRelA) (A a b : ExprA) : Prop :=
  Nonempty (ConvA E I n Γ a b A) ∧
  ((∃ (c : Nat) (cm : CheckedMemberA) (lsC lsC' : List Level) (kinds : List FieldShape)
      (ps₁ ps₂ fs fs' : List ExprA) (T T' : ExprA),
      E.members c = some cm ∧ cm.mclass = .constructorM ∧ memberFamRefA cm = some r ∧
      eqNListBB n (carrierLevelsA A) lsC ∧ eqNListB n lsC lsC' ∧
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds ∧
      applyTelA (carrierParamsA m A) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T ∧
      applyTelA (carrierParamsA m A) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' ∧
      FamCohA r m RsF A fs T fs' T' ∧
      ps₁.length = m.nparamsA ∧ ps₂.length = m.nparamsA ∧
      TyHRedStarA E I n Γ a (foldAppsA (.const c lsC) (ps₁ ++ fs)) A ∧
      TyHRedStarA E I n Γ b (foldAppsA (.const c lsC') (ps₂ ++ fs')) A ∧
      hStepFnA E I.fn Γ (foldAppsA (.const c lsC) (ps₁ ++ fs)) = none ∧
      hStepFnA E I.fn Γ (foldAppsA (.const c lsC') (ps₂ ++ fs')) = none ∧
      ArgsRelA (Rs c lsC) (famRecRelA m (carrierParamsA m A) (carrierLevelsA A) X)
        (famFunRelA E I n Γ m (RsI c lsC) (carrierParamsA m A) (carrierLevelsA A) XF)
        m.nparamsA (carrierParamsA m A) T kinds fs fs' ∧
      ConvArgsA E I n Γ (instantiateLevelsA lsC m.mtypeA) (carrierParamsA m A) ps₁ ∧
      ConvArgsA E I n Γ (instantiateLevelsA lsC' m.mtypeA) (carrierParamsA m A) ps₂) ∨
   (∃ N N' : ExprA,
      TyHRedStarA E I n Γ a N A ∧ TyHRedStarA E I n Γ b N' A ∧
      StuckTmA E I Γ N ∧ StuckTmA E I Γ N'))

/-- monotonicity of the one-step operator in the fixed point at its world and at the extensions
    (which the function-recursive positions read only at well-formed extensions). -/
theorem famPhiA_mono {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} {Rs : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {X Y : CRelA} {XF YF : WkSpecA → CRelA} (hXY : ∀ A a b, X A a b → Y A a b)
    (hXF : ∀ ρ', WkOkA E I n ρ' Γ → ∀ A a b, XF ρ' A a b → YF ρ' A a b) {A a b : ExprA}
    (h : FamPhiA E I n Γ r m Rs RsF RsI X XF A a b) : FamPhiA E I n Γ r m Rs RsF RsI Y YF A a b := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h4', h5, hT, hT',
      h6, hp₁, hp₂, h7, h8, hn, hn', h9⟩ | hst
  · exact Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h4', h5, hT, hT',
      h6, hp₁, hp₂, h7, h8, hn, hn', argsRelA_mono (famRecRelA_mono hXY)
        (famFunRelA_mono (fun ρ' hρ' => famRecRelA_mono (hXF ρ' hρ'))) h9.1, h9.2⟩
  · exact Or.inr hst

/-- monotonicity at the operator's FIBER relations: a map of the recursive positions'
    wrapped relations (the carrier's parameters and levels in hand), at its world and at the
    well-formed extensions, lifts to the step. -/
theorem famPhiA_fib_mono {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} {Rs : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {X Y : CRelA} {XF YF : WkSpecA → CRelA} {A a b : ExprA}
    (hXY : ∀ D f f', famRecRelA m (carrierParamsA m A) (carrierLevelsA A) X D f f' →
      famRecRelA m (carrierParamsA m A) (carrierLevelsA A) Y D f f')
    (hXF : ∀ ρ', WkOkA E I n ρ' Γ → ∀ D f f',
      famRecRelA m ((carrierParamsA m A).map (wkExprA ρ')) (carrierLevelsA A) (XF ρ') D f f' →
      famRecRelA m ((carrierParamsA m A).map (wkExprA ρ')) (carrierLevelsA A) (YF ρ') D f f')
    (h : FamPhiA E I n Γ r m Rs RsF RsI X XF A a b) : FamPhiA E I n Γ r m Rs RsF RsI Y YF A a b := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h4', h5, hT, hT',
      h6, hp₁, hp₂, h7, h8, hn, hn', h9⟩ | hst
  · exact Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h4', h5, hT, hT',
      h6, hp₁, hp₂, h7, h8, hn, hn', argsRelA_mono hXY (famFunRelA_mono hXF) h9.1, h9.2⟩
  · exact Or.inr hst

/-- the type of the clause's inner relations: at a world, constructor, levels, field position and
    field prefix, the relation at an inner position after an inner prefix (R-NoFunRec-1 step 1 (1b)). -/
abbrev InnerRelsA : Type :=
  WkSpecA → Nat → List Level → Nat → List ExprA → Nat → List ExprA → ExprA → ExprA → Prop

/-- the inner relations a walk at world `ρ` reads for constructor `c` at levels `lsC`: at an extension
    `ρ'`, the clause's at the composed world `ρ ∘ ρ'`, the field prefix weakened there. -/
abbrev innerRelsA (RsI : InnerRelsA) (ρ : WkSpecA) (c : Nat) (lsC : List Level) :
    Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop :=
  fun i prev ρ' => RsI (WkSpecA.comp ρ ρ') c lsC i (prev.map (wkExprA ρ'))

/-- THE OPERATOR OVER WORLDS (R-NoFunRec-1 step 1 (1a), (1b)): at world `ρ`, the one-step operator at
    the clause's context weakened to `ρ`, with the clause's data at `ρ`; its directly recursive
    positions read the fixed point at `ρ`, its function-recursive ones at `ρ ∘ ρ'`, with the inner
    relations there. -/
def FamPhiWA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (r : Nat)
    (m : CheckedMemberA)
    (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsI : InnerRelsA) (X : WRelA) (ρ : WkSpecA) : CRelA :=
  FamPhiA E I n (wkCtxA ρ Γ) r m (Rs ρ) (RsF ρ) (fun c lsC => innerRelsA RsI ρ c lsC) (X ρ)
    (fun ρ' => X (WkSpecA.comp ρ ρ'))

theorem famPhiWA_mono {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI : InnerRelsA} :
    MonoWA (FamPhiWA E I n Γ r m Rs RsF RsI) :=
  fun _ _ hXY ρ _ _ _ h => famPhiA_mono (hXY ρ) (fun ρ' _ => hXY (WkSpecA.comp ρ ρ')) h

/-- the fixed point lies in conversion at the carrier: `ConvA` is the first conjunct
    of every step. -/
theorem lfpWA_famPhiWA_conv {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI : InnerRelsA}
    {ρ : WkSpecA} {A a b : ExprA} (h : LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A a b) :
    Nonempty (ConvA E I n (wkCtxA ρ Γ) a b A) :=
  (LfpWA.unfold famPhiWA_mono h).1

/-- a constructor walk at the conjunction of two fixed points transfers between
    the two position relations when they agree on every doubly-related prefix; the
    walk starts at `(i₀, prev₀, tel)` (the carrier's parameters, M2-f (3c)) and the
    recursive positions read a pointwise conjunction of two fiber relations. At a
    function-recursive position (R-NoFunRec-1 step 1 (1b)) the source's relation `Fs` gives the
    target's `Ft` and each side's own (`F₁`, `F₂`), on doubly-related prefixes (`hUI`). -/
theorem argsRelA_transfer {Rs₁ Rs₂ : Nat → List ExprA → ExprA → ExprA → Prop}
    {X₁ X₂ : CRelA} {F₁ F₂ Fs Ft : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    (i₀ : Nat) (prev₀ : List ExprA) (tel : ExprA) (kinds : List FieldShape)
    (hU : ∀ (ksPre ks : List FieldShape) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA)
        (vC : Level), kinds = ksPre ++ FieldShape.nonrecursive :: ks →
        ArgsRelA Rs₁ X₁ F₁ i₀ prev₀ tel ksPre pre pre' →
        ArgsRelA Rs₂ X₂ F₂ i₀ prev₀ tel ksPre pre pre' →
        applyTelA pre tel = some (.pi D uD C vC) →
        Rs₁ (i₀ + ksPre.length) (prev₀ ++ pre) = Rs₂ (i₀ + ksPre.length) (prev₀ ++ pre))
    (hUI : ∀ (ksPre ks : List FieldShape) (j : Nat) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
        (C : ExprA) (vC : Level) (f f' : ExprA), kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        ArgsRelA Rs₁ X₁ F₁ i₀ prev₀ tel ksPre pre pre' →
        ArgsRelA Rs₂ X₂ F₂ i₀ prev₀ tel ksPre pre pre' →
        applyTelA pre tel = some (.pi D uD C vC) →
        Fs (i₀ + ksPre.length) (prev₀ ++ pre) D j f f' →
        Ft (i₀ + ksPre.length) (prev₀ ++ pre) D j f f' ∧ F₁ (i₀ + ksPre.length) (prev₀ ++ pre) D j f f' ∧
          F₂ (i₀ + ksPre.length) (prev₀ ++ pre) D j f f') :
    ∀ {i : Nat} {prev : List ExprA} {T : ExprA} {ks : List FieldShape} {fs fs' : List ExprA},
      ArgsRelA Rs₁ (fun C a b => X₁ C a b ∧ X₂ C a b) Fs i prev T ks fs fs' →
      ∀ (ksPre : List FieldShape) (pre pre' : List ExprA),
        kinds = ksPre ++ ks → i = i₀ + ksPre.length → prev = prev₀ ++ pre → applyTelA pre tel = some T →
        ArgsRelA Rs₁ X₁ F₁ i₀ prev₀ tel ksPre pre pre' →
        ArgsRelA Rs₂ X₂ F₂ i₀ prev₀ tel ksPre pre pre' →
        ArgsRelA Rs₂ (fun C a b => X₁ C a b ∧ X₂ C a b) Ft i prev T ks fs fs' := by
  intro i prev T ks fs fs' h
  induction h with
  | nil i prev T =>
      intro ksPre pre pre' _ _ _ _ _ _
      exact .nil i prev T
  | plain i prev A₀ u₀ B₀ v₀ f f' ks fs fs' hR _ ih =>
      intro ksPre pre pre' hk hi hprev hT hp1 hp2
      subst hprev; subst hi
      have heq := hU ksPre ks pre pre' A₀ u₀ B₀ v₀ hk hp1 hp2 hT
      have hR' : Rs₂ (i₀ + ksPre.length) (prev₀ ++ pre) f f' := by rw [← heq]; exact hR
      have hp1' := argsRelA_snoc hp1 (f := f) (f' := f') FieldShape.nonrecursive hT
        (by simp only [kindRelA]; exact hR)
      have hp2' := argsRelA_snoc hp2 (f := f) (f' := f') FieldShape.nonrecursive hT
        (by simp only [kindRelA]; exact hR')
      refine .plain (i₀ + ksPre.length) (prev₀ ++ pre) A₀ u₀ B₀ v₀ f f' ks fs fs' hR'
        (ih (ksPre ++ [FieldShape.nonrecursive]) (pre ++ [f]) (pre' ++ [f']) ?_ ?_ ?_
          (applyTelA_snoc pre tel hT) hp1' hp2')
      · rw [hk, List.append_assoc]; rfl
      · simp; omega
      · simp
  | directRec i prev A₀ u₀ B₀ v₀ f f' ks fs fs' hY _ ih =>
      intro ksPre pre pre' hk hi hprev hT hp1 hp2
      subst hprev; subst hi
      have hp1' := argsRelA_snoc hp1 (f := f) (f' := f') (FieldShape.recursive 0) hT hY.1
      have hp2' := argsRelA_snoc hp2 (f := f) (f' := f') (FieldShape.recursive 0) hT hY.2
      refine .directRec (i₀ + ksPre.length) (prev₀ ++ pre) A₀ u₀ B₀ v₀ f f' ks fs fs' hY
        (ih (ksPre ++ [(FieldShape.recursive 0)]) (pre ++ [f]) (pre' ++ [f']) ?_ ?_ ?_
          (applyTelA_snoc pre tel hT) hp1' hp2')
      · rw [hk, List.append_assoc]; rfl
      · simp; omega
      · simp
  | funRec i prev A₀ u₀ B₀ v₀ f f' j ks fs fs' hF _ ih =>
      intro ksPre pre pre' hk hi hprev hT hp1 hp2
      subst hprev; subst hi
      obtain ⟨hFt, hF₁, hF₂⟩ := hUI ksPre ks j pre pre' A₀ u₀ B₀ v₀ f f' hk hp1 hp2 hT hF
      have hp1' := argsRelA_snoc hp1 (f := f) (f' := f') (FieldShape.recursive (j + 1)) hT
        (by simp only [kindRelA]; exact hF₁)
      have hp2' := argsRelA_snoc hp2 (f := f) (f' := f') (FieldShape.recursive (j + 1)) hT
        (by simp only [kindRelA]; exact hF₂)
      refine .funRec (i₀ + ksPre.length) (prev₀ ++ pre) A₀ u₀ B₀ v₀ f f' j ks fs fs' hFt
        (ih (ksPre ++ [FieldShape.recursive (j + 1)]) (pre ++ [f]) (pre' ++ [f']) ?_ ?_ ?_
          (applyTelA_snoc pre tel hT) hp1' hp2')
      · rw [hk, List.append_assoc]; rfl
      · simp; omega
      · simp

/-- one inclusion between two fixed points ON A FIBER at every world (the carriers with parameters
    `ps` weakened to the world and levels `=ₙ ls₀`, which recursive positions never leave): from
    agreement of the plain-field, index and inner relations on doubly-related prefixes there, at every
    world of the clause. -/
theorem lfpWA_le_of {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} {Rs₁ Rs₂ : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF₁ RsF₂ : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI₁ RsI₂ : InnerRelsA} {ps : List ExprA} {ls₀ : List Level}
    (hU : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA) (lsC lsA : List Level)
        (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
        (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs₁ ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI₁ ρ c lsC) (ps.map (wkExprA ρ)) lsA
            (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        ArgsRelA (Rs₂ ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI₂ ρ c lsC) (ps.map (wkExprA ρ)) lsA
            (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        Rs₁ ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) =
          Rs₂ ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre))
    (hUF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA) (pre pre' : List ExprA)
        (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls₀ lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
        ArgsRelPA (RsF₁ ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
        ArgsRelPA (RsF₂ ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
        applyTelA pre TF = some (.pi D uD C vC) →
        RsF₁ ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre) =
          RsF₂ ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre))
    (hUI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA) (lsC lsA : List Level)
        (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA) (pre pre' : List ExprA) (D : ExprA)
        (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs₁ ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI₁ ρ c lsC) (ps.map (wkExprA ρ)) lsA
            (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        ArgsRelA (Rs₂ ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI₂ ρ c lsC) (ps.map (wkExprA ρ)) lsA
            (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) →
        ∀ (ys ys' : List ExprA) (B : ExprA) (uB : Level) (C' : ExprA) (vB : Level),
        ArgsRelPA (innerRelsA RsI₁ ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) ys ys' →
        ArgsRelPA (innerRelsA RsI₂ ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) ys ys' →
        applyTelA ys (wkExprA ρ' D) = some (.pi B uB C' vB) →
        innerRelsA RsI₁ ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' (0 + ys.length)
            ([] ++ ys) =
          innerRelsA RsI₂ ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' (0 + ys.length)
            ([] ++ ys))
    {ρ : WkSpecA} {A a b : ExprA} (hρ : WkOk₀A E I n ρ Γ)
    (hAp : carrierParamsA m A = ps.map (wkExprA ρ)) (hAl : eqNList ls₀ (carrierLevelsA A))
    (h : LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) ρ A a b) :
    LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) ρ A a b := by
  have hY := h (fun ρ C a b => WkOk₀A E I n ρ Γ → carrierParamsA m C = ps.map (wkExprA ρ) →
      eqNList ls₀ (carrierLevelsA C) →
      LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) ρ C a b ∧ LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) ρ C a b)
    (fun ρ C a b hs hρ hCp hCl => by
      -- the induction hypothesis at the fiber's recursive positions, at the world
      have hX : ∀ D x y, famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C) (fun C a b =>
            WkOk₀A E I n ρ Γ → carrierParamsA m C = ps.map (wkExprA ρ) →
            eqNList ls₀ (carrierLevelsA C) →
            LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) ρ C a b ∧
              LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) ρ C a b) D x y →
          famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C)
            (LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) ρ) D x y ∧
          famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C)
            (LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) ρ) D x y :=
        fun D x y hd => by
          have hlD : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hCl (eqNListA_symm hd.2.1)
          have hh := hd.2.2 hρ hd.1 hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, ⟨hd.1, hd.2.1, hh.2⟩⟩
      -- and at the world's well-formed extensions
      have hXF : ∀ ρ', WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ D x y,
          famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C) (fun C a b =>
            WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ → carrierParamsA m C = ps.map (wkExprA (WkSpecA.comp ρ ρ')) →
            eqNList ls₀ (carrierLevelsA C) →
            LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) (WkSpecA.comp ρ ρ') C a b ∧
              LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) (WkSpecA.comp ρ ρ') C a b) D x y →
          famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
            (LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) (WkSpecA.comp ρ ρ')) D x y ∧
          famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
            (LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) (WkSpecA.comp ρ ρ')) D x y :=
        fun ρ' hρ' D x y hd => by
          have hlD : eqNList ls₀ (carrierLevelsA D) := eqNListA_trans hCl (eqNListA_symm hd.2.1)
          have hh := hd.2.2 (wkOk₀A_comp_ext hρ hρ') (hd.1.trans (map_wkExprA_comp ρ ρ' ps)) hlD
          exact ⟨⟨hd.1, hd.2.1, hh.1⟩, ⟨hd.1, hd.2.1, hh.2⟩⟩
      obtain ⟨hc, hs⟩ := hs
      refine ⟨LfpWA.fold famPhiWA_mono ⟨hc, ?_⟩, LfpWA.fold famPhiWA_mono ⟨hc, ?_⟩⟩
      · rcases hs with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hls,
            hkinds, hT, hT', hcoh, hp₁, hp₂, ha, hb, hna, hnb, hargs⟩ | hst
        · refine Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hls,
            hkinds, hT, hT', hcoh, hp₁, hp₂, ha, hb, hna, hnb, ?_, hargs.2⟩
          rw [hCp] at hargs ⊢
          exact argsRelA_mono (fun D x y hd => (hX D x y hd).1)
            (famFunRelA_mono (fun ρ' hρ' D x y hd => (hXF ρ' hρ' D x y hd).1)) hargs.1
        · exact Or.inr hst
      · rcases hs with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hls,
            hkinds, hT, hT', hcoh, hp₁, hp₂, ha, hb, hna, hnb, hargs⟩ | hst
        · obtain ⟨lsA, lsR, lsR', xsA, isR, isR', TF, Rres, Rres', hspA, hTF, hta, hspR, hlsA, hw,
            hta', hspR', hlsA', hw'⟩ := hcoh
          have hlsAC : carrierLevelsA C = lsA := by simp only [carrierLevelsA, hspA]
          have hpsC : xsA.take m.nparamsA = ps.map (wkExprA ρ) := by
            rw [← hCp]; simp only [carrierParamsA, hspA]
          have hl₀A : eqNList ls₀ lsA := hlsAC ▸ hCl
          have hl₀AB : eqNListB n ls₀ lsA := ⟨hl₀A, hlsAC ▸ hlC.2⟩
          rw [hpsC] at hTF hspR hw hspR' hw'
          refine Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hls,
            hkinds, hT, hT', ⟨lsA, lsR, lsR', xsA, isR, isR', TF, Rres, Rres', hspA, ?_, hta, ?_, hlsA,
              ?_, hta', ?_, hlsA', ?_⟩, hp₁, hp₂, ha, hb, hna, hnb, ?_, ?_⟩
          · rw [hpsC]; exact hTF
          · rw [hpsC]; exact hspR
          · rw [hpsC]
            exact argsRelPA_transfer (hUF ρ hρ lsA TF · · · · · · hl₀AB hTF) hw (pre := []) (pre' := [])
              (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)
          · rw [hpsC]; exact hspR'
          · rw [hpsC]
            exact argsRelPA_transfer (hUF ρ hρ lsA TF · · · · · · hl₀AB hTF) hw' (pre := []) (pre' := [])
              (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)
          · rw [hCp] at hargs hT ⊢
            have hl₀C : eqNList ls₀ (carrierLevelsA C) := hlsAC ▸ hl₀A
            have hY₂ := argsRelA_transfer (X₁ := famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C)
                (LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) ρ))
              (X₂ := famRecRelA m (ps.map (wkExprA ρ)) (carrierLevelsA C)
                (LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) ρ))
              (F₁ := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI₁ ρ c lsC) (ps.map (wkExprA ρ))
                (carrierLevelsA C) (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) (WkSpecA.comp ρ ρ')))
              (F₂ := famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI₂ ρ c lsC) (ps.map (wkExprA ρ))
                (carrierLevelsA C) (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) (WkSpecA.comp ρ ρ')))
              (Fs := fun i prev A j f f' =>
                FunRelA (innerRelsA RsI₁ ρ c lsC) (fun ρ' D x y =>
                  famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
                    (LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) (WkSpecA.comp ρ ρ')) D x y ∧
                  famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
                    (LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) (WkSpecA.comp ρ ρ')) D x y)
                  (fun ρ' => WkOkA E I n ρ' (wkCtxA ρ Γ)) i prev A j f f' ∧
                DeclPairA E I n (wkCtxA ρ Γ) A f f')
              (Ft := fun i prev A j f f' =>
                FunRelA (innerRelsA RsI₂ ρ c lsC) (fun ρ' D x y =>
                  famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
                    (LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) (WkSpecA.comp ρ ρ')) D x y ∧
                  famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
                    (LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) (WkSpecA.comp ρ ρ')) D x y)
                  (fun ρ' => WkOkA E I n ρ' (wkCtxA ρ Γ)) i prev A j f f' ∧
                DeclPairA E I n (wkCtxA ρ Γ) A f f')
              m.nparamsA (ps.map (wkExprA ρ)) T kinds
              (fun ksPre ks pre pre' D uD C' vC hsp h1 h2 hT₀ =>
                hU ρ hρ c cm lsC (carrierLevelsA C) kinds ksPre ks T pre pre' D uD C' vC hcm hk hfam hkinds
                  hsp hl₀C hlC.1 hT h1 h2 hT₀)
              (fun ksPre ks j pre pre' D uD C' vC f f' hsp h1 h2 hT₀ hFs => by
                have hFt : FunRelA (innerRelsA RsI₂ ρ c lsC) (fun ρ' D x y =>
                    famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
                      (LfpWA (FamPhiWA E I n Γ r m Rs₁ RsF₁ RsI₁) (WkSpecA.comp ρ ρ')) D x y ∧
                    famRecRelA m ((ps.map (wkExprA ρ)).map (wkExprA ρ')) (carrierLevelsA C)
                      (LfpWA (FamPhiWA E I n Γ r m Rs₂ RsF₂ RsI₂) (WkSpecA.comp ρ ρ')) D x y)
                    (fun ρ' => WkOkA E I n ρ' (wkCtxA ρ Γ)) (m.nparamsA + ksPre.length)
                    (ps.map (wkExprA ρ) ++ pre) D j f f' ∧
                    DeclPairA E I n (wkCtxA ρ Γ) D f f' := by
                  refine ⟨fun ρ' hρ' ys ys' Cc hys hlen hCc => ?_, hFs.2⟩
                  refine hFs.1 ρ' hρ' ys ys' Cc ?_ hlen hCc
                  exact argsRelPA_transfer
                    (fun zs zs' B uB C'' vB hz₂ hz₁ hTz =>
                      (hUI ρ hρ c cm lsC (carrierLevelsA C) kinds ksPre ks j T pre pre' D uD C' vC hcm hk hfam
                        hkinds hsp hl₀C hlC.1 hT h1 h2 hT₀ ρ' hρ' zs zs' B uB C'' vB hz₁ hz₂ hTz).symm)
                    hys (pre := []) (pre' := []) (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)
                exact ⟨hFt, ⟨funRelA_mono (fun _ _ _ _ _ hd => hd.1) _ _ _ _ _ _ hFs.1, hFs.2⟩,
                  ⟨funRelA_mono (fun _ _ _ _ _ hd => hd.2) _ _ _ _ _ _ hFt.1, hFt.2⟩⟩)
              (argsRelA_mono (fun D x y hd => hX D x y hd)
                (fun i prev A j f f' hF =>
                  ⟨funRelA_mono (fun ρ' hρ' D x y hd => hXF ρ' hρ' D x y hd) i prev A j f f' hF.1, hF.2⟩)
                hargs.1)
              [] [] [] (by simp) (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)
            exact argsRelA_mono (fun D x y hd => hd.2)
              (fun i prev A j f f' hF =>
                ⟨funRelA_mono (fun _ _ _ _ _ hd => hd.2) i prev A j f f' hF.1, hF.2⟩) hY₂
          · exact hargs.2
        · exact Or.inr hst)
  exact (hY hρ hAp hAl).2

/-- the fixed point's pairs are typed at the carrier: every disjunct of a step
    reduces both sides, typed, at the carrier. -/
theorem lfpWA_famPhiWA_hasTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI : InnerRelsA}
    {ρ : WkSpecA} {A a b : ExprA} (h : LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ A a b) :
    Nonempty (HasTyA E I n (wkCtxA ρ Γ) a A) ∧ Nonempty (HasTyA E I n (wkCtxA ρ Γ) b A) := by
  rcases (LfpWA.unfold famPhiWA_mono h).2 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ha, hb, _, _, _⟩ |
      ⟨_, _, ha, hb, _, _⟩
  · exact ⟨tyHRedStarA_hasTy_head ha, tyHRedStarA_hasTy_head hb⟩
  · exact ⟨tyHRedStarA_hasTy_head ha, tyHRedStarA_hasTy_head hb⟩

#print axioms LfpWA.fold
#print axioms LfpWA.unfold
#print axioms argsRelA_mono
#print axioms WkSpecA.comp_assoc
#print axioms argsRelPA_snoc
#print axioms famPhiA_mono
#print axioms famPhiA_fib_mono
#print axioms famPhiWA_mono
#print axioms lfpWA_famPhiWA_conv
#print axioms argsRelA_transfer
#print axioms lfpWA_le_of
#print axioms lfpWA_famPhiWA_hasTy
#print axioms hasTyA_foldAppsA_const_bounded
#print axioms whTyA_famApp_bounded
#print axioms tyHRedStarA_det
#print axioms foldAppsA_const_inj
#print axioms parConvA_refl
#print axioms parConvA_symm
#print axioms parConvA_trans
#print axioms convArgsA_rebase
#print axioms parConvA_append
#print axioms convArgsA_applyTel
#print axioms convArgsA_append

end Rcic.Declarative.Ann
