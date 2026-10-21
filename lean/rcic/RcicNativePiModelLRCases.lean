import rcic.RcicNativePiModelLR
import rcic.RcicCtxConvT

/-!
# RcicNativePiModelLRCases — structural cases of the fundamental lemma

The congruence/index cases of `FundamentalLRI` (#7628), as lemmas about the logical
relation, together with one design correction.

**Correction (additive).**  #7628's `LRTypeI` has a `spine` clause relating ARBITRARY
weak-head reducts by a native conversion.  That clause is too weak for transitivity: two
reducts of the middle type need not be comparable by conversion without a typed weak-head
bridge, whose β case needs Π-injectivity itself (the classical circle).  `LRTypeIN` (this
module) requires the spine reducts to be weak-head NORMAL, and lets the Π clause carry the
well-formedness of the extended context (the paper's grey presuppositions).  With that,
`WhDet` — determinism of `WhStep` — gives uniqueness of weak-head normal forms
(`whRed_normal_unique`), and the relation is closed under weak-head expansion, symmetric,
transitive, and transportable along context conversions, with NO typed bridge.
`WhDet`'s content: ι determinism (`IotaDetU`, landed legacy arm), no δ-body on recursor
heads, and prefix-arity of ι witnesses; it is a named `Prop`.

**Cases compiled** (each is the clause the fundamental lemma uses for that constructor):
`lrTypeIN_expand` (every weak-head computation case — β via `approxI_beta`, ζ via
`approxI_zeta`, δ, ι, lit — reduces to the relation on the contractum), `lrTypeIN_pi_congr`,
`lrTypeIN_sort_congr` (`sorts`), `lrTypeIN_spine_congr` (`consts`, with normal spines),
`lrTypeIN_symm`, `lrTypeIN_trans`, `lrTypeIN_ctx`/`lrTypeIN_assump_dom` (context
transport, the `lam`/`pi` binder cases), and `tyConv` is the index-freeness of the relation.
Read-off and consumers as in #7628: `lrTypeIN_pi_components`, `FundamentalLRIN`,
`piRow_of_fundamentalLRIN`.

**Not congruence cases.**  `refl` at a Π compact IS adequacy: `ApproxI ⊥ A (pi a f)` must
force `A` to weak-head reduce to a Π-type — `AdequacyPiI`, named; and `app` congruence needs
the TERM-level relation (`LRTermI`, named with its Π clause shape).  Both are exact
statements for the next round.  The `irr` interface for `devin/below-irr` is spelled out
in the PR body.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ### weak-head reduction: transitivity, normality, determinism -/

theorem whRed_trans {a b c : Expr Nat} (h₁ : WhRed E a b) (h₂ : WhRed E b c) : WhRed E a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-- Weak-head normal. -/
def WhNormal (E : ResolvedEnv) (X : Expr Nat) : Prop := ∀ Y, ¬ WhStep E X Y

theorem whNormal_pi (A B : Expr Nat) : WhNormal E (.pi A B) := fun _ h => whStep_pi_false h
theorem whNormal_sort (l : Level) : WhNormal E (.sort l) := fun _ h => whStep_sort_false h

/-- Determinism of weak-head steps (named: ι determinism, no δ-body on recursor heads,
    prefix-arity of ι witnesses). -/
def WhDet (E : ResolvedEnv) : Prop := ∀ {a b c : Expr Nat}, WhStep E a b → WhStep E a c → b = c

/-- Under determinism, weak-head normal forms are unique. -/
theorem whRed_normal_unique (hdet : WhDet E) {a X : Expr Nat} (h : WhRed E a X) (hX : WhNormal E X) :
    ∀ {Y : Expr Nat}, WhRed E a Y → WhNormal E Y → X = Y := by
  induction h with
  | refl =>
      intro Y hY _
      cases hY with
      | refl => rfl
      | step h _ => exact (hX _ h).elim
  | step h _ ih =>
      intro Y hY hYn
      cases hY with
      | refl => exact (hYn _ h).elim
      | step h' hs' =>
          have := hdet h h'
          subst this
          exact ih hX hs' hYn

/-! ### the corrected relation -/

/-- The compact-indexed logical relation with native readback, normal spine reducts and the
    Π clause's context presupposition. -/
inductive LRTypeIN (E : ResolvedEnv) (n : Nat) : LCtx → Expr Nat → Expr Nat → CptI → Prop
  | bot (Γ : LCtx) (A A' : Expr Nat) : LRTypeIN E n Γ A A' .bot
  | sort {Γ : LCtx} {A A' : Expr Nat} {u u' : Level}
      (h : WhRed E A (.sort u)) (h' : WhRed E A' (.sort u')) : LRTypeIN E n Γ A A' .sort
  | pi {Γ : LCtx} {A A' A₁ B₁ A₂ B₂ : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (h : WhRed E A (.pi A₁ B₁)) (h' : WhRed E A' (.pi A₂ B₂))
      (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
      (hdom : TyConvT E n Γ A₁ A₂) (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
      (ra : LRTypeIN E n Γ A₁ A₂ a)
      (rf : ∀ s ∈ f, LRTypeIN E n (.assumption A₁ :: Γ) B₁ B₂ s.2) :
      LRTypeIN E n Γ A A' (.pi a f)
  | spine {Γ : LCtx} {A A' X X' : Expr Nat} {r : Nat} {args : List CptI}
      (h : WhRed E A X) (h' : WhRed E A' X') (hX : WhNormal E X) (hX' : WhNormal E X')
      (hc : TyConvT E n Γ X X') : LRTypeIN E n Γ A A' (.spine r args)

/-! ### structural cases -/

/-- Closure under weak-head expansion on both sides: the β, ζ, δ, ι and `lit` cases. -/
theorem lrTypeIN_expand {Γ : LCtx} {A A' X X' : Expr Nat} {c : CptI}
    (hX : WhRed E A X) (hX' : WhRed E A' X') (h : LRTypeIN E n Γ X X' c) :
    LRTypeIN E n Γ A A' c := by
  cases h with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort (whRed_trans hX h) (whRed_trans hX' h')
  | pi h h' hΓ₁ hdom hcod ra rf =>
      exact .pi (whRed_trans hX h) (whRed_trans hX' h') hΓ₁ hdom hcod ra rf
  | spine h h' hn hn' hc => exact .spine (whRed_trans hX h) (whRed_trans hX' h') hn hn' hc

/-- The `pi` congruence case. -/
theorem lrTypeIN_pi_congr {Γ : LCtx} {A₁ B₁ A₂ B₂ : Expr Nat} {a : CptI}
    {f : List (List CptI × CptI)} (hΓ₁ : CtxWfT E n (.assumption A₁ :: Γ))
    (hdom : TyConvT E n Γ A₁ A₂) (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
    (ra : LRTypeIN E n Γ A₁ A₂ a) (rf : ∀ s ∈ f, LRTypeIN E n (.assumption A₁ :: Γ) B₁ B₂ s.2) :
    LRTypeIN E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.pi a f) :=
  .pi (.refl _) (.refl _) hΓ₁ hdom hcod ra rf

/-- The `sorts` case. -/
theorem lrTypeIN_sort_congr (Γ : LCtx) (u v : Level) : LRTypeIN E n Γ (.sort u) (.sort v) .sort :=
  .sort (.refl _) (.refl _)

/-- The `consts` case (and any pair of convertible weak-head normal spines). -/
theorem lrTypeIN_spine_congr {Γ : LCtx} {X X' : Expr Nat} (r : Nat) (args : List CptI)
    (hX : WhNormal E X) (hX' : WhNormal E X') (hc : TyConvT E n Γ X X') :
    LRTypeIN E n Γ X X' (.spine r args) :=
  .spine (.refl _) (.refl _) hX hX' hc

/-- A `TyConvT` chain types its right endpoint at some sort when the left one is typed. -/
def tyConvT_endTyped (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {X Y : Expr Nat} → TyConvT E n Γ X Y → {u : Level} → HasTyT E n Γ X (.sort u) →
    Σ' v, HasTyT E n Γ Y (.sort v)
  | _, _, .refl _ _, u, h => ⟨u, h⟩
  | _, _, .of _ _ _ v hc, _, _ => ⟨v, (convEnds hW hΓ hc).2.1⟩
  | _, _, .trans _ _ _ _ c₁ c₂, _, h =>
      let ⟨_, h₁⟩ := tyConvT_endTyped hW hΓ c₁ h
      tyConvT_endTyped hW hΓ c₂ h₁

/-- Context transport along a context conversion (the binder cases). -/
theorem lrTypeIN_ctx (hcl : EnvClosed E) (hW : EnvWfT E) {Γ Γ' : LCtx}
    (hctx : CtxConvT E n Γ Γ') (hΓ' : CtxWfT E n Γ') {A A' : Expr Nat} {c : CptI}
    (h : LRTypeIN E n Γ A A' c) : LRTypeIN E n Γ' A A' c := by
  induction h generalizing Γ' with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort h h'
  | @pi Γ A A' A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      cases hΓ₁ with
      | assumption _ _ u hΓ hA₁ =>
          have hA₁' : HasTyT E n Γ' A₁ (.sort u) := hasTyT_ctx hcl hctx hA₁
          have hΓ₁' : CtxWfT E n (.assumption A₁ :: Γ') := .assumption Γ' A₁ u hΓ' hA₁'
          exact .pi h h' hΓ₁' (tyConvT_ctx hcl hctx hdom)
            (tyConvT_ctx hcl (.same (.assumption A₁) hctx) hcod)
            (iha hctx hΓ')
            (fun s hs => ihf s hs (.same (.assumption A₁) hctx) hΓ₁')
  | spine h h' hn hn' hc => exact .spine h h' hn hn' (tyConvT_ctx hcl hctx hc)

/-- Transport along a domain chain at the head assumption. -/
theorem lrTypeIN_assump_dom (hcl : EnvClosed E) (hW : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A₁ A₂ : Expr Nat} → TyConvT E n Γ A₁ A₂ → {u : Level} → HasTyT E n Γ A₁ (.sort u) →
    ∀ {B B' : Expr Nat} {c : CptI},
      LRTypeIN E n (.assumption A₂ :: Γ) B B' c → LRTypeIN E n (.assumption A₁ :: Γ) B B' c
  | _, _, .refl _ _, _, _, _, _, _, h => h
  | _, _, .of _ A₁ A₂ v hc, _, hA₁, _, _, _, h =>
      let ends := convEnds hW hΓ hc
      lrTypeIN_ctx hcl hW
        (.assumption (ctxConvT_refl Γ) ends.2.1 ends.1 (.symm _ _ _ _ hc))
        (.assumption Γ A₁ _ hΓ hA₁) h
  | _, _, .trans _ A₁ M A₂ c₁ c₂, _, hA₁, _, _, _, h =>
      let ⟨_, hM⟩ := tyConvT_endTyped hW hΓ c₁ hA₁
      lrTypeIN_assump_dom hcl hW hΓ c₁ hA₁ (lrTypeIN_assump_dom hcl hW hΓ c₂ hM h)

/-- Symmetry. -/
theorem lrTypeIN_symm (hcl : EnvClosed E) (hW : EnvWfT E) {Γ : LCtx} {A A' : Expr Nat}
    {c : CptI} (h : LRTypeIN E n Γ A A' c) : LRTypeIN E n Γ A' A c := by
  induction h with
  | bot => exact .bot _ _ _
  | sort h h' => exact .sort h' h
  | @pi Γ A A' A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      cases hΓ₁ with
      | assumption _ _ u hΓ hA₁ =>
          obtain ⟨v, hA₂⟩ := tyConvT_endTyped hW hΓ hdom hA₁
          have hΓ₂ : CtxWfT E n (.assumption A₂ :: Γ) := .assumption Γ A₂ v hΓ hA₂
          exact .pi h' h hΓ₂ hdom.symmT (tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT) iha
            (fun s hs => lrTypeIN_assump_dom hcl hW hΓ hdom.symmT hA₂ (ihf s hs))
  | spine h h' hn hn' hc => exact .spine h' h hn' hn hc.symmT

/-- Transitivity, under determinism of weak-head steps. -/
theorem lrTypeIN_trans (hcl : EnvClosed E) (hW : EnvWfT E) (hdet : WhDet E) {Γ : LCtx}
    {A B : Expr Nat} {c : CptI} (h₁ : LRTypeIN E n Γ A B c) :
    ∀ {C : Expr Nat}, LRTypeIN E n Γ B C c → LRTypeIN E n Γ A C c := by
  induction h₁ with
  | bot => intro C _; exact .bot _ _ _
  | sort h _ =>
      intro C h₂
      cases h₂ with
      | sort _ hC => exact .sort h hC
  | @pi Γ A B A₁ B₁ A₂ B₂ a f h h' hΓ₁ hdom hcod _ _ iha ihf =>
      intro C h₂
      cases h₂ with
      | pi hB hC hΓ₂ hdom' hcod' ra' rf' =>
          have e := whRed_normal_unique hdet h' (whNormal_pi _ _) hB (whNormal_pi _ _)
          injection e with eA eB
          subst eA; subst eB
          cases hΓ₁ with
          | assumption _ _ u hΓ hA₁ =>
              exact .pi h hC (.assumption Γ A₁ u hΓ hA₁) (.trans _ _ _ _ hdom hdom')
                (.trans _ _ _ _ hcod (tyConvT_assump_dom hW hΓ hdom hcod'))
                (iha ra')
                (fun s hs => ihf s hs (lrTypeIN_assump_dom hcl hW hΓ hdom hA₁ (rf' s hs)))
  | spine h h' hn hn' hc =>
      intro C h₂
      cases h₂ with
      | spine hB hC hY hY' hc' =>
          have e := whRed_normal_unique hdet h' hn' hB hY
          subst e
          exact .spine h hC hn hY' (.trans _ _ _ _ hc hc')

/-! ### read-off and consumers -/

/-- Reading the clause at `pi bot []` for two syntactic Π-types. -/
theorem lrTypeIN_pi_components {Γ : LCtx} {A₁ B₁ A₂ B₂ : Expr Nat}
    (h : LRTypeIN E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.pi .bot [])) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  cases h with
  | pi h h' _ hdom hcod _ _ =>
      have e₁ := whRed_pi_eq h
      have e₂ := whRed_pi_eq h'
      injection e₁ with eA₁ eB₁
      injection e₂ with eA₂ eB₂
      subst eA₁; subst eB₁; subst eA₂; subst eB₂
      exact ⟨⟨hdom⟩, ⟨hcod⟩⟩

/-- The fundamental lemma for the corrected relation (the exact remaining theorem). -/
def FundamentalLRIN (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat}, TyConvT E n Γ A A' →
    ∀ c, ApproxI EnvI.bot A c → LRTypeIN E n Γ A A' c

/-- Π-injectivity (`piRow` shape) from the fundamental lemma. -/
theorem piRow_of_fundamentalLRIN (F : FundamentalLRIN E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  fun {_} hΓ {A B _ _} hc => lrTypeIN_pi_components (F hΓ hc _ (approxI_pi_bot_nil EnvI.bot A B))

/-! ### the two statements that are not congruence cases -/

/-- Adequacy at Π (the `refl` case at a Π compact): a type approximated by a Π compact
    weak-head reduces to a Π-type whose components are approximated by the compact's. -/
def AdequacyPiI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {u : Level}, HasTyT E n Γ A (.sort u) →
    ∀ {a : CptI} {f : List (List CptI × CptI)}, ApproxI EnvI.bot A (.pi a f) →
      ∃ A₁ B₁, WhRed E A (.pi A₁ B₁) ∧ ApproxI EnvI.bot A₁ a ∧
        ∀ s ∈ f, ApproxI (EnvI.cons (demand s.1) EnvI.bot) B₁ s.2

set_option linter.unusedVariables false in
/-- The term-level relation's Π clause shape (the `app` congruence case needs it): two terms
    related at a Π code map related arguments to related results.  Stated as the interface
    the type-level relation consumes; its definition is the next round. -/
def LRTermPiShape (E : ResolvedEnv) (n : Nat)
    (LRTerm : LCtx → Expr Nat → Expr Nat → Expr Nat → CptI → Prop) : Prop :=
  ∀ {Γ : LCtx} {F F' A B : Expr Nat} {s : List CptI × CptI} {g : List (List CptI × CptI)},
    LRTerm Γ F F' (.pi A B) (.lam g) → s ∈ g →
    ∀ {a a' : Expr Nat}, (∀ u ∈ s.1, LRTerm Γ a a' A u) →
      LRTerm Γ (.app F a) (.app F' a') (instantiate0 a B) s.2

#print axioms whRed_trans
#print axioms WhNormal
#print axioms whNormal_pi
#print axioms whNormal_sort
#print axioms WhDet
#print axioms whRed_normal_unique
#print axioms LRTypeIN
#print axioms lrTypeIN_expand
#print axioms lrTypeIN_pi_congr
#print axioms lrTypeIN_sort_congr
#print axioms lrTypeIN_spine_congr
#print axioms tyConvT_endTyped
#print axioms lrTypeIN_ctx
#print axioms lrTypeIN_assump_dom
#print axioms lrTypeIN_symm
#print axioms lrTypeIN_trans
#print axioms lrTypeIN_pi_components
#print axioms FundamentalLRIN
#print axioms piRow_of_fundamentalLRIN
#print axioms AdequacyPiI
#print axioms LRTermPiShape

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
