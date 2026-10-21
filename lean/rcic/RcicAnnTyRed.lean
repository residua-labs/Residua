import rcic.RcicAnnWeaken

/-!
# M1-d (iv) a — typed head reduction on the copy, and type conversion

The relation (`RcicAnnLR`, amended by M1-d (iv)) reads its shapes off TYPED
weak-head reduction and stores DECLARATIVE conversion as its base datum —
L-RING C4's design (`RcicLRRed.lean:448`, `RcicLR.lean:74` on the face),
transcribed onto the annotated copy. Three objects:

* `TyConvA Γ A B` — type conversion: coherently typed conversions at a sort
  (`of`, with exactly `ConvA.tyConv`'s coherence premises), closed under
  `refl`/`trans`. Transitive BY CONSTRUCTION across sorts, so the relation's
  type-equality data compose without any uniqueness of sorts (the face's
  `TyConv`, `RcicDeclarative.lean:1356`).
* `TyHRedA Γ a b A` — ONE typed head step: the reduction rules of `ConvA`
  (β, ζ, ζ-local, δ, ι through the interface, lit) with exactly their
  premises, a step in the head of an application, and a `conv` arm. Every
  step IS a `ConvA` (`tyHRedA_conv`), types its reduct (`tyHRedA_hasTy_right`),
  and IS an `hStepFnA` step (`tyHRedA_hStep`): so chains erase to `whnfA` and
  normal forms are unique — the kill criterion's determinism survives the move
  to typed reduction.
* `WhTyChainA Γ A N` — a chain of typed head steps, EACH STEP AT ITS OWN SORT
  and every element typed at the sort of the step it heads; `WhTyA Γ A N` its
  Prop. A chain is a `TyConvA` (`whTyChainA_tyConv`), erases to `RedTo` when
  it ends at a normal form (`whTyChainA_redTo`, whence `whTyA_det`), and a step
  can be prepended at whatever sort it comes with (`whTyA_cons`) — a chain at
  ONE fixed sort could not be, without uniqueness of sorts.

Why typed reduction here (M1-d (iv) record): with a declarative base, escape
must convert a type to its normal form, and an UNTYPED step gives no
`ConvA` without the premises of its rule — which for β would have to come from
inversion of the redex's typing, i.e. from `PiConvInj`. The typed step carries
them; the fundamental theorem supplies them from the arm it is in.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) `eqN` is an equivalence, congruent at `succ` -/

theorem eqNA_refl (l : Level) : eqN l l := fun _ => rfl
theorem eqNA_symm {l l' : Level} (h : eqN l l') : eqN l' l := fun ρ => (h ρ).symm
theorem eqNA_trans {l₁ l₂ l₃ : Level} (h₁ : eqN l₁ l₂) (h₂ : eqN l₂ l₃) : eqN l₁ l₃ :=
  fun ρ => (h₁ ρ).trans (h₂ ρ)
theorem eqNA_succ {l l' : Level} (h : eqN l l') : eqN (.succ l) (.succ l') := by
  intro ρ
  simp only [eval, h ρ]

/-! ## (1) type conversion -/

/-- coherently typed conversion of types at a sort, closed under `refl`/`trans`:
    the relation's type-equality datum. -/
inductive TyConvA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) : LCtxA → ExprA → ExprA → Type
  | refl (Γ : LCtxA) (A : ExprA) : TyConvA E I n Γ A A
  | of (Γ : LCtxA) (A B : ExprA) (l l' u : Level)
      (hAl : HasTyA E I n Γ A (.sort l)) (hlu : eqN l u)
      (hBl : HasTyA E I n Γ B (.sort l')) (hl'u : eqN l' u)
      (h : ConvA E I n Γ A B (.sort u)) : TyConvA E I n Γ A B
  | trans (Γ : LCtxA) (A B C : ExprA)
      (h1 : TyConvA E I n Γ A B) (h2 : TyConvA E I n Γ B C) : TyConvA E I n Γ A C

section TyConv
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def TyConvA.symm : {Γ : LCtxA} → {A B : ExprA} → TyConvA E I n Γ A B → TyConvA E I n Γ B A
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .of Γ A B l l' u hAl hlu hBl hl'u h =>
      .of Γ B A l' l u hBl hl'u hAl hlu (.symm Γ A B _ h)
  | _, _, _, .trans Γ A B C h1 h2 => .trans Γ C B A h2.symm h1.symm

/-- a conversion at `A` is a conversion at any type `A` converts to
    (`ConvA.tyConv`, with the coherence premises `of` carries). -/
def convA_of_tyConvA {Γ : LCtxA} {a b A : ExprA} (h : ConvA E I n Γ a b A) :
    {B : ExprA} → TyConvA E I n Γ A B → ConvA E I n Γ a b B
  | _, .refl _ _ => h
  | _, .of _ _ B l l' u hAl hlu hBl hl'u hc => .tyConv Γ a b A B l l' u h hAl hlu hBl hl'u hc
  | _, .trans _ _ _ _ h1 h2 => convA_of_tyConvA (convA_of_tyConvA h h1) h2

/-- sorts at `=ₙ` levels are type-convertible. -/
def tyConvA_sorts (Γ : LCtxA) {l l' : Level} (h : eqN l l') :
    TyConvA E I n Γ (.sort l) (.sort l') :=
  .of Γ _ _ (.succ l) (.succ l') (.succ l) (.sort Γ l) (eqNA_refl _) (.sort Γ l')
    (eqNA_succ (eqNA_symm h)) (.sorts Γ l l' h)

/-- a typing at `A` is a typing at any type `A` converts to (`HasTyA.conv`,
    the conversion re-sorted to `B`'s own sort through `ConvA.tyConv`). -/
def hasTyA_of_tyConvA {Γ : LCtxA} {e A : ExprA} (he : HasTyA E I n Γ e A) :
    {B : ExprA} → TyConvA E I n Γ A B → HasTyA E I n Γ e B
  | _, .refl _ _ => he
  | _, .of _ _ B l l' u hAl hlu hBl hl'u hc =>
      .conv Γ e A B l l' he hAl (eqNA_trans hlu (eqNA_symm hl'u)) hBl
        (.tyConv Γ A B (.sort u) (.sort l') (.succ u) (.succ l') (.succ u) hc
          (.sort Γ u) (eqNA_refl _) (.sort Γ l') (eqNA_succ hl'u)
          (.sorts Γ u l' (eqNA_symm hl'u)))
  | _, .trans _ _ _ _ h1 h2 => hasTyA_of_tyConvA (hasTyA_of_tyConvA he h1) h2

/-- the LEFT endpoint of a `TyConvA` is sort-typed once the right is: `refl` collapses the
    endpoints, `of` carries the left typing, `trans` recurses through the middle
    (R-NoDeltaRec-4d-iii — the `normConv`/`normTyped` transport). -/
def tyConvA_typed_left : {Γ : LCtxA} → {A B : ExprA} → TyConvA E I n Γ A B →
    {w : Level} → HasTyA E I n Γ B (.sort w) →
    ∃ l, Nonempty (HasTyA E I n Γ A (.sort l))
  | _, _, _, .refl _ _, _, hB => ⟨_, ⟨hB⟩⟩
  | _, _, _, .of _ _ _ l _ _ hAl _ _ _ _, _, _ => ⟨_, ⟨hAl⟩⟩
  | _, _, _, .trans _ _ _ _ h1 h2, _, hB =>
      let ⟨_, ⟨hM⟩⟩ := tyConvA_typed_left h2 hB
      tyConvA_typed_left h1 hM

/-- a typing at `sort l` is a typing at any `=ₙ` sort. -/
def hasTyA_retype_sort {Γ : LCtxA} {e : ExprA} {l l' : Level}
    (he : HasTyA E I n Γ e (.sort l)) (h : eqN l l') : HasTyA E I n Γ e (.sort l') :=
  hasTyA_of_tyConvA he (tyConvA_sorts Γ h)

end TyConv

/-! ## (2) one typed head step -/

/-- ONE typed weak-head step: `ConvA`'s reduction rules with exactly their
    premises, a step in the head of an application, and conversion of the
    type. Every arm is an `hStepFnA` step (`tyHRedA_hStep`). -/
inductive TyHRedA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → ExprA → ExprA → ExprA → Type
  | beta (Γ : LCtxA) (A : ExprA) (u : Level) (body arg B : ExprA)
      (hA : HasTyA E I n Γ A (.sort u))
      (hbody : HasTyA E I n (.assumption A :: Γ) body B)
      (harg : HasTyA E I n Γ arg A)
      (hred : HasTyA E I n Γ (instantiate0A arg body) (instantiate0A arg B)) :
      TyHRedA E I n Γ (.app (.lam A u body) arg) (instantiate0A arg body) (instantiate0A arg B)
  | zeta (Γ : LCtxA) (A value body B : ExprA) (u : Level)
      (hA : HasTyA E I n Γ A (.sort u))
      (hv : HasTyA E I n Γ value A)
      (hb : HasTyA E I n (.letBinding A value :: Γ) body B)
      (hred : HasTyA E I n Γ (instantiate0A value body) (instantiate0A value B)) :
      TyHRedA E I n Γ (.letE A value body) (instantiate0A value body) (instantiate0A value B)
  | zetaLocal (Γ : LCtxA) (i : Nat) (A v : ExprA)
      (hval : lookupValueA Γ i = some v)
      (hty : lookupTypeA Γ i = some A)
      (hv : HasTyA E I n Γ v A) :
      TyHRedA E I n Γ (.bvar i) v A
  | delta (Γ : LCtxA) (r : Nat) (ls : List Level) (m : CheckedMemberA) (b : ExprA)
      (hres : E.members r = some m) (hbody : m.bodyA = some b)
      (htr : transparent m.mclass = true)
      (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hb : HasTyA E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)) :
      TyHRedA E I n Γ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)
  | iota (Γ : LCtxA) (lhs rhs T : ExprA)
      (h : I.rel E Γ lhs rhs)
      (hlhs : HasTyA E I n Γ lhs T)
      (hrhs : HasTyA E I n Γ rhs T) :
      TyHRedA E I n Γ lhs rhs T
  | lit (Γ : LCtxA) (t : Nat) (T : ExprA)
      (hexp : HasTyA E I n Γ (natExpandA t) T) :
      TyHRedA E I n Γ (.lit t) (natExpandA t) T
  /-- a step in the head of an application, the head's type converting to a pi;
      `hB`/`hTy` are `HasTyA.app`'s own premises (they type the reduct). -/
  | app (Γ : LCtxA) (f f' a A B T₀ : ExprA) (u v w : Level)
      (h : TyHRedA E I n Γ f f' T₀)
      (hc : TyConvA E I n Γ T₀ (.pi A u B v))
      (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
      (hTy : HasTyA E I n Γ (instantiate0A a B) (.sort w))
      (ha : HasTyA E I n Γ a A) :
      TyHRedA E I n Γ (.app f a) (.app f' a) (instantiate0A a B)
  | conv (Γ : LCtxA) (a b A A' : ExprA)
      (h : TyHRedA E I n Γ a b A) (hc : TyConvA E I n Γ A A') :
      TyHRedA E I n Γ a b A'
  /-- R-MajorStep (M2-f (1)): a step in the MAJOR of a recursor spine at its major,
      when the head does not step, the group is neither a unit group nor a struct group, and ι
      refuses (`hrec`, `hu`, `hs`, `hf`, `hi`: the arm's guards, so the step IS the function's,
      `tyHRedA_hStep`). The reduct's typing
      at the LEFT's type is carried (`hrt`), as every typed rule carries its
      reduct's typing: deriving it needs the codomain's conversion under the
      step, which the relation supplies semantically (M2-f (5)). -/
  | major (Γ : LCtxA) (f a a' A B T₀ : ExprA) (u v : Level)
      (hrec : recAtMajorA E f = true) (hu : unitMinorA E f = none) (hs : structHeadA E f = false)
      (hf : hStepFnA E I.fn Γ f = none) (hi : I.fn (.app f a) = none)
      (h : TyHRedA E I n Γ a a' T₀)
      (hc : TyConvA E I n Γ T₀ A)
      (hfTy : HasTyA E I n Γ f (.pi A u B v))
      (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
      (hrt : HasTyA E I n Γ (.app f a') (instantiate0A a B)) :
      TyHRedA E I n Γ (.app f a) (.app f a') (instantiate0A a B)
  /-- O1-b-1 (K-unit): at a recursor spine of a UNIT GROUP at its major, when the head does not step
      and ι refuses (`hrec`, `hu`, `hf`, `hi`: the arm's guards, so the step IS the function's), the
      step is to the minor, whatever the major. Its conversion (`hcv`: `irr` puts the major at the
      constructor, ι fires there, README O1-b-0) and the reduct's typing at the left's type (`hrt`)
      are carried, for the relation to supply. -/
  | kunit (Γ : LCtxA) (f a mn T : ExprA)
      (hrec : recAtMajorA E f = true) (hu : unitMinorA E f = some mn)
      (hf : hStepFnA E I.fn Γ f = none) (hi : I.fn (.app f a) = none)
      (hcv : ConvA E I n Γ (.app f a) mn T)
      (hrt : HasTyA E I n Γ mn T) :
      TyHRedA E I n Γ (.app f a) mn T
  /-- W-1 (a) (K-struct without recursion): at a recursor spine of a STRUCT GROUP at its major, when the
      head does not step (`hrec`, `hs`, `hf`: the struct step's guards, so the step IS the function's;
      W-1 (e): the struct step comes before ι, so ι is not consulted), the step is to the minor applied
      to the major's projections (`structArmA`), whatever the major. Its conversion (`hcv`: `irr` puts
      the major at the constructor applied to its projections, and struct ι fires there, README W-1-0,
      W-1 (e)-0) and the reduct's typing at the left's type (`hrt`) are carried, for the relation to
      supply. -/
  | kstruct (Γ : LCtxA) (f a e T : ExprA)
      (hrec : recAtMajorA E f = true) (hs : structArmA E f a = some e)
      (hf : hStepFnA E I.fn Γ f = none)
      (hcv : ConvA E I n Γ (.app f a) e T)
      (hrt : HasTyA E I n Γ e T) :
      TyHRedA E I n Γ (.app f a) e T

/-- a live major arm has a constant head, so no λ. -/
theorem not_lam_of_recAtMajorA {E : ResolvedEnvA} {f : ExprA} (h : recAtMajorA E f = true) :
    ∀ A u b, f ≠ .lam A u b := fun A u b e => by
  rw [e, recAtMajorA_not_lam] at h
  exact Bool.noConfusion h

section Step
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- a typed step types its reduct (every rule of `ConvA` carries that typing). -/
def tyHRedA_hasTy_right : {Γ : LCtxA} → {a b A : ExprA} →
    TyHRedA E I n Γ a b A → HasTyA E I n Γ b A
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ hred => hred
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ hred => hred
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => hv
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => hb
  | _, _, _, _, .iota _ _ _ _ _ _ hrhs => hrhs
  | _, _, _, _, .lit _ _ _ hexp => hexp
  | _, _, _, _, .app Γ _ f' a A B _ u v w h hc hB hTy ha =>
      .app Γ f' a A B u v w hB hTy (hasTyA_of_tyConvA (tyHRedA_hasTy_right h) hc) ha
  | _, _, _, _, .conv _ _ _ _ _ h hc => hasTyA_of_tyConvA (tyHRedA_hasTy_right h) hc
  | _, _, _, _, .major _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrt => hrt
  | _, _, _, _, .kunit _ _ _ _ _ _ _ _ _ _ hrt => hrt
  | _, _, _, _, .kstruct _ _ _ _ _ _ _ _ _ hrt => hrt

/-- a typed step IS a conversion. -/
def tyHRedA_conv : {Γ : LCtxA} → {a b A : ExprA} →
    TyHRedA E I n Γ a b A → ConvA E I n Γ a b A
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred => .beta Γ A u body arg B hA hbody harg hred
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred => .zeta Γ A value body B u hA hv hb hred
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv => .zetaLocal Γ i A v hval hty hv
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      .delta Γ r ls m b hres hbody htr hlen hwf hb
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs => .iota Γ lhs rhs T h hlhs hrhs
  | _, _, _, _, .lit Γ t T hexp => .lit Γ t T hexp
  | _, _, _, _, .app Γ f f' a A B _ u v w h hc hB hTy ha =>
      .app Γ f f' a a A B u v (convA_of_tyConvA (tyHRedA_conv h) hc) (.refl Γ a A ha) hB
        (.app Γ f' a A B u v w hB hTy (hasTyA_of_tyConvA (tyHRedA_hasTy_right h) hc) ha)
  | _, _, _, _, .conv _ _ _ _ _ h hc => convA_of_tyConvA (tyHRedA_conv h) hc
  | _, _, _, _, .major Γ f a a' A B _ u v _ _ _ _ _ h hc hfTy hB hrt =>
      .app Γ f f a a' A B u v (.refl Γ f _ hfTy) (convA_of_tyConvA (tyHRedA_conv h) hc) hB hrt
  | _, _, _, _, .kunit _ _ _ _ _ _ _ _ _ hcv _ => hcv
  | _, _, _, _, .kstruct _ _ _ _ _ _ _ _ hcv _ => hcv

/-- a stepping term is not a λ (a λ is normal). -/
theorem tyHRedA_not_lam {Γ : LCtxA} {a b A : ExprA} (h : TyHRedA E I n Γ a b A) :
    ∀ D u body, a ≠ .lam D u body := by
  induction h with
  | beta => intro _ _ _ he; exact ExprA.noConfusion he
  | zeta => intro _ _ _ he; exact ExprA.noConfusion he
  | zetaLocal => intro _ _ _ he; exact ExprA.noConfusion he
  | delta => intro _ _ _ he; exact ExprA.noConfusion he
  | iota lhs _ _ h _ _ =>
      intro D u body he
      subst he
      have := h.exec
      simp [hStepFnA] at this
  | lit => intro _ _ _ he; exact ExprA.noConfusion he
  | app => intro _ _ _ he; exact ExprA.noConfusion he
  | conv _ _ _ _ _ _ ih => exact ih
  | major => intro _ _ _ he; exact ExprA.noConfusion he
  | kunit => intro _ _ _ he; exact ExprA.noConfusion he
  | kstruct => intro _ _ _ he; exact ExprA.noConfusion he

/-- SOUNDNESS: a typed step is the head step the function takes. -/
theorem tyHRedA_hStep {Γ : LCtxA} {a b A : ExprA} (h : TyHRedA E I n Γ a b A) :
    hStepFnA E I.fn Γ a = some b := by
  induction h with
  | beta => rfl
  | zeta => rfl
  | zetaLocal _ _ _ hval _ _ => exact hval
  | delta _ _ _ _ hres hbody htr _ _ _ => simp [hStepFnA, hres, htr, hbody]
  | iota _ _ _ h _ _ => exact h.exec
  | lit => rfl
  | app f _ a _ _ _ _ _ _ h _ _ _ _ ih =>
      simp only [hStepFnA_app_nonlam E I.fn _ a (tyHRedA_not_lam h), ih]
  | conv _ _ _ _ _ _ ih => exact ih
  | major f a _ _ _ _ _ _ hrec hu hs hf hi _ _ _ _ _ ih =>
      rw [hStepFnA_app_atMajor E I.fn _ (not_lam_of_recAtMajorA hrec) hf hi hrec hu hs, ih]
      rfl
  | kunit f a mn _ hrec hu hf hi _ _ =>
      exact hStepFnA_app_unit E I.fn _ (not_lam_of_recAtMajorA hrec) hf hi hrec hu
  | kstruct f a e _ hrec hs hf _ _ =>
      exact hStepFnA_app_struct E I.fn _ (not_lam_of_recAtMajorA hrec) hf hrec hs

end Step

/-! ## (3) chains, every step at its own sort -/

/-- a chain of typed head steps, EACH STEP AT ITS OWN SORT, every element typed
    at the sort of the step it heads: so a step can be prepended at whatever
    sort it comes with (head expansion), with no uniqueness of sorts. -/
inductive WhTyChainA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → ExprA → ExprA → Type
  | refl (Γ : LCtxA) (A : ExprA) (u : Level) (h : HasTyA E I n Γ A (.sort u)) :
      WhTyChainA E I n Γ A A
  | cons (Γ : LCtxA) (A A' N : ExprA) (u : Level)
      (hA : HasTyA E I n Γ A (.sort u))
      (hs : TyHRedA E I n Γ A A' (.sort u))
      (t : WhTyChainA E I n Γ A' N) : WhTyChainA E I n Γ A N

/-- `A` weak-head reduces, typed step by step, to `N`. -/
def WhTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (A N : ExprA) : Prop :=
  Nonempty (WhTyChainA E I n Γ A N)

section Chain
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

theorem whTyChainA_hasTy_head {Γ : LCtxA} {A N : ExprA} :
    WhTyChainA E I n Γ A N → ∃ u, Nonempty (HasTyA E I n Γ A (.sort u))
  | .refl _ _ u h => ⟨u, ⟨h⟩⟩
  | .cons _ _ _ _ u hA _ _ => ⟨u, ⟨hA⟩⟩

theorem whTyChainA_hasTy_end {Γ : LCtxA} : {A N : ExprA} →
    WhTyChainA E I n Γ A N → ∃ u, Nonempty (HasTyA E I n Γ N (.sort u))
  | _, _, .refl _ _ u h => ⟨u, ⟨h⟩⟩
  | _, _, .cons _ _ _ _ _ _ _ t => whTyChainA_hasTy_end t

/-- a chain is a type conversion: each step at its own sort, composed. -/
def whTyChainA_tyConv {Γ : LCtxA} : {A N : ExprA} →
    WhTyChainA E I n Γ A N → TyConvA E I n Γ A N
  | _, _, .refl _ A _ _ => .refl Γ A
  | _, _, .cons _ A A' N u hA hs t =>
      .trans Γ A A' N
        (.of Γ A A' u u u hA (eqNA_refl u) (tyHRedA_hasTy_right hs) (eqNA_refl u) (tyHRedA_conv hs))
        (whTyChainA_tyConv t)

/-- ERASURE: a chain ending at a normal form is a `whnfA` computation. -/
theorem whTyChainA_redTo {Γ : LCtxA} : {A N : ExprA} →
    WhTyChainA E I n Γ A N → hStepFnA E I.fn Γ N = none → RedTo E I Γ A N
  | _, _, .refl _ A _ _, hN => ⟨0, whnfA_of_normal E I.fn Γ 0 A hN⟩
  | _, _, .cons _ _ _ _ _ _ hs t, hN => by
      obtain ⟨fuel, hf⟩ := whTyChainA_redTo t hN
      exact ⟨fuel + 1, by simp only [whnfA, tyHRedA_hStep hs]; exact hf⟩

theorem whTyA_redTo {Γ : LCtxA} {A N : ExprA} (h : WhTyA E I n Γ A N)
    (hN : hStepFnA E I.fn Γ N = none) : RedTo E I Γ A N :=
  h.elim fun t => whTyChainA_redTo t hN

/-- DETERMINISM: two chains from `A` to normal forms end at the same term —
    the kill criterion's `RedTo_det`, through erasure. -/
theorem whTyA_det {Γ : LCtxA} {A N N' : ExprA}
    (h : WhTyA E I n Γ A N) (h' : WhTyA E I n Γ A N')
    (hN : hStepFnA E I.fn Γ N = none) (hN' : hStepFnA E I.fn Γ N' = none) : N = N' :=
  RedTo_det (whTyA_redTo h hN) (whTyA_redTo h' hN')

theorem whTyA_of_hasTy {Γ : LCtxA} {A : ExprA} {u : Level} (h : HasTyA E I n Γ A (.sort u)) :
    WhTyA E I n Γ A A := ⟨.refl Γ A u h⟩

theorem whTyA_hasTy_head {Γ : LCtxA} {A N : ExprA} (h : WhTyA E I n Γ A N) :
    ∃ u, Nonempty (HasTyA E I n Γ A (.sort u)) := h.elim fun t => whTyChainA_hasTy_head t

theorem whTyA_hasTy_end {Γ : LCtxA} {A N : ExprA} (h : WhTyA E I n Γ A N) :
    ∃ u, Nonempty (HasTyA E I n Γ N (.sort u)) := h.elim fun t => whTyChainA_hasTy_end t

theorem whTyA_tyConv {Γ : LCtxA} {A N : ExprA} (h : WhTyA E I n Γ A N) :
    Nonempty (TyConvA E I n Γ A N) := h.elim fun t => ⟨whTyChainA_tyConv t⟩

/-- HEAD EXPANSION: prepend a typed step, at whatever sort it comes with. -/
theorem whTyA_cons {Γ : LCtxA} {A A' N : ExprA} {u : Level} (hA : HasTyA E I n Γ A (.sort u))
    (hs : TyHRedA E I n Γ A A' (.sort u)) (h : WhTyA E I n Γ A' N) : WhTyA E I n Γ A N :=
  h.elim fun t => ⟨.cons Γ A A' N u hA hs t⟩

end Chain

/-! ## (4) shapes are normal -/

theorem hStepFnA_sort (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (l : Level) :
    hStepFnA E iota Γ (.sort l) = none := rfl
theorem hStepFnA_pi (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (D : ExprA) (u : Level)
    (C : ExprA) (v : Level) : hStepFnA E iota Γ (.pi D u C v) = none := rfl
theorem hStepFnA_lam (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (A : ExprA) (u : Level)
    (b : ExprA) : hStepFnA E iota Γ (.lam A u b) = none := rfl

#print axioms hasTyA_of_tyConvA
#print axioms convA_of_tyConvA
#print axioms tyHRedA_conv
#print axioms tyHRedA_hasTy_right
#print axioms tyHRedA_hStep
#print axioms whTyChainA_redTo
#print axioms whTyA_det
#print axioms whTyChainA_tyConv
#print axioms whTyA_cons

end Rcic.Declarative.Ann
