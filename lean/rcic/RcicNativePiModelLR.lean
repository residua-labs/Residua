import rcic.RcicNativePiModelIdeal
import rcic.RcicNativeValleyIota

/-!
# RcicNativePiModelLR — the compact-indexed logical relation with native readback

The read-back layer of the semantic route to Π-injectivity, over the ideal-based model of
`RcicNativePiModelIdeal`.  Following Carneiro et al. (arXiv 2607.13662, §2.6–2.8): a
relation `Γ ⊨ A ≡ A′ type |ₐ` between two types indexed by a compact `a`, whose Π-clause
says both sides weak-head reduce to Π-types whose components are OBJECT conversions
(`TyConvT`), related recursively along the compact; the fundamental lemma gives the
relation at every compact approximating `⟦A⟧_⊥`, and `pi bot [] ∈ ⟦Π A B⟧_⊥` closes.

* `WhStep`/`WhRed`: weak-head reduction on the raw syntax — β, ζ, δ, ι (union evidence),
  literal expansion, and head congruence `app f a ↝ app f′ a`.  The head congruence is
  essential: #7619's `admitted_no_rootPiObservationTransfer` shows root-only contraction
  (`HeadStepT`) cannot carry Π observations across computation inside the function spine.
  Π-types and sorts are weak-head normal (`whRed_pi_eq`, `whRed_sort_eq`).
* `LRTypeI E n Γ A A′ c`: the relation; `bot` degenerate; `sort`; `pi` with the component
  conversions and the recursive relations at the domain compact and at every codomain
  code; `spine` for constant-headed normal forms.
* `lrTypeI_pi_components`: at `pi bot []` for two syntactic Π-types the clause yields the
  component conversions (Π's do not reduce).
* `FundamentalLRI E n` — the fundamental lemma: `TyConvT Γ A A′ → ∀ c, ApproxI ⊥ A c →
  LRTypeI Γ A A′ c` (the exact remaining theorem; its β case is `approxI_beta`, its
  computational cases L2's soundness, its `irr` case the strict-Prop collapse);
  `fundamentalPiLRI_of_fundamentalLRI` and `piRow_of_fundamentalLRI` read Π-injectivity off
  it.  Unlike #7613's `FundamentalPi` (definitionally `PiInj`), `FundamentalLRI` is a
  statement about the model: its consumer `piRow_of_fundamentalLRI` is a proof, not an
  identity.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

variable {E : ResolvedEnv}

/-- The degenerate environment: every variable denotes `⊥` only. -/
def EnvI.bot : EnvI := fun _ c => c = .bot

/-! ### weak-head reduction -/

/-- Weak-head steps on the raw syntax. -/
inductive WhStep (E : ResolvedEnv) : Expr Nat → Expr Nat → Prop
  | beta (A b a : Expr Nat) : WhStep E (.app (.lam A b) a) (instantiate0 a b)
  | zeta (A v b : Expr Nat) : WhStep E (.letE A v b) (instantiate0 v b)
  | delta {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
      (hres : E.members r = some m) (hbody : m.body = some b) :
      WhStep E (.const r ls) (instantiateLevels ls b)
  | iota {lhs rhs : Expr Nat} (h : DerivedIotaU E lhs rhs) : WhStep E lhs rhs
  | lit (t : Nat) : WhStep E (.lit t) (natExpand t)
  | appHead {f f' a : Expr Nat} (h : WhStep E f f') : WhStep E (.app f a) (.app f' a)

/-- Weak-head reduction, reflexive-transitive. -/
inductive WhRed (E : ResolvedEnv) : Expr Nat → Expr Nat → Prop
  | refl (e : Expr Nat) : WhRed E e e
  | step {a b c : Expr Nat} (h : WhStep E a b) (hs : WhRed E b c) : WhRed E a c

/-- Π-types are weak-head normal. -/
theorem whStep_pi_false {A B e : Expr Nat} (h : WhStep E (.pi A B) e) : False := by
  cases h with
  | iota hι =>
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hι
      exact foldApps_snoc_ne_pi (.const r ls) major pre (by simpa [recCall] using hl.symm)

/-- Sorts are weak-head normal. -/
theorem whStep_sort_false {l : Level} {e : Expr Nat} (h : WhStep E (.sort l) e) : False := by
  cases h with
  | iota hι =>
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hι
      exact foldApps_snoc_ne_sort (.const r ls) major pre (by simpa [recCall] using hl.symm)

/-- Weak-head reduction from a Π is trivial. -/
theorem whRed_pi_eq {A B e : Expr Nat} (h : WhRed E (.pi A B) e) : e = .pi A B := by
  cases h with
  | refl => rfl
  | step h _ => exact (whStep_pi_false h).elim

/-- Weak-head reduction from a sort is trivial. -/
theorem whRed_sort_eq {l : Level} {e : Expr Nat} (h : WhRed E (.sort l) e) : e = .sort l := by
  cases h with
  | refl => rfl
  | step h _ => exact (whStep_sort_false h).elim

/-! ### the logical relation -/

/-- The compact-indexed logical relation on types with native readback. -/
inductive LRTypeI (E : ResolvedEnv) (n : Nat) : LCtx → Expr Nat → Expr Nat → CptI → Prop
  | bot (Γ : LCtx) (A A' : Expr Nat) : LRTypeI E n Γ A A' .bot
  | sort {Γ : LCtx} {A A' : Expr Nat} {u u' : Level}
      (h : WhRed E A (.sort u)) (h' : WhRed E A' (.sort u')) : LRTypeI E n Γ A A' .sort
  | pi {Γ : LCtx} {A A' A₁ B₁ A₂ B₂ : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (h : WhRed E A (.pi A₁ B₁)) (h' : WhRed E A' (.pi A₂ B₂))
      (hdom : TyConvT E n Γ A₁ A₂) (hcod : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂)
      (ra : LRTypeI E n Γ A₁ A₂ a)
      (rf : ∀ s ∈ f, LRTypeI E n (.assumption A₁ :: Γ) B₁ B₂ s.2) :
      LRTypeI E n Γ A A' (.pi a f)
  | spine {Γ : LCtx} {A A' X X' : Expr Nat} {r : Nat} {args : List CptI}
      (h : WhRed E A X) (h' : WhRed E A' X') (hc : TyConvT E n Γ X X') :
      LRTypeI E n Γ A A' (.spine r args)

/-- Reading the clause at `pi bot []` for two syntactic Π-types: the component conversions. -/
theorem lrTypeI_pi_components {n : Nat} {Γ : LCtx} {A₁ B₁ A₂ B₂ : Expr Nat}
    (h : LRTypeI E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.pi .bot [])) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  cases h with
  | pi h h' hdom hcod _ _ =>
      have e₁ := whRed_pi_eq h
      have e₂ := whRed_pi_eq h'
      injection e₁ with eA₁ eB₁
      injection e₂ with eA₂ eB₂
      subst eA₁; subst eB₁; subst eA₂; subst eB₂
      exact ⟨⟨hdom⟩, ⟨hcod⟩⟩

/-- `pi bot []` approximates every Π-type at the degenerate environment. -/
theorem approxI_pi_bot_nil (ρ : EnvI) (A B : Expr Nat) : ApproxI ρ (.pi A B) (.pi .bot []) :=
  .pi (.bot ρ A) (fun _ hs => (List.not_mem_nil _ hs).elim)

/-- The fundamental lemma (the exact remaining theorem): two convertible types are related
    at every compact approximating the first at the degenerate environment. -/
def FundamentalLRI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat}, TyConvT E n Γ A A' →
    ∀ c, ApproxI EnvI.bot A c → LRTypeI E n Γ A A' c

/-- Its instance at `pi bot []` for two convertible Π-types. -/
def FundamentalPiLRI (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ B₁ A₂ B₂ : Expr Nat},
    TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) →
    LRTypeI E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.pi .bot [])

theorem fundamentalPiLRI_of_fundamentalLRI {n : Nat} (F : FundamentalLRI E n) :
    FundamentalPiLRI E n :=
  fun {_} hΓ {A₁ B₁ _ _} hc => F hΓ hc _ (approxI_pi_bot_nil EnvI.bot A₁ B₁)

/-- Π-injectivity (the `Prop`-valued `TypedRowsWf.piRow` shape) from the fundamental lemma's
    instance. -/
theorem piRow_of_fundamentalPiLRI {n : Nat} (F : FundamentalPiLRI E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  fun {_} hΓ {_ _ _ _} hc => lrTypeI_pi_components (F hΓ hc)

/-- Π-injectivity from the fundamental lemma. -/
theorem piRow_of_fundamentalLRI {n : Nat} (F : FundamentalLRI E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
      TyConvT E n Γ (.pi A B) (.pi A' B') →
      Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  piRow_of_fundamentalPiLRI (fundamentalPiLRI_of_fundamentalLRI F)

#print axioms EnvI.bot
#print axioms WhStep
#print axioms WhRed
#print axioms whStep_pi_false
#print axioms whStep_sort_false
#print axioms whRed_pi_eq
#print axioms whRed_sort_eq
#print axioms LRTypeI
#print axioms lrTypeI_pi_components
#print axioms approxI_pi_bot_nil
#print axioms FundamentalLRI
#print axioms FundamentalPiLRI
#print axioms fundamentalPiLRI_of_fundamentalLRI
#print axioms piRow_of_fundamentalPiLRI
#print axioms piRow_of_fundamentalLRI

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
