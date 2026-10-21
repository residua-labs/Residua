import rcic.RcicParRedT
import rcic.RcicCtxConvT
import rcic.RcicDT0709EnvWf

/-!
# The `ParRedT.pi` critical pair joins at its common source

The domain and codomain premises of `ParRedT.pi` are full `ConvT`
derivations. Consequently this arm is reversible: use `ConvT.symm`,
then transport the reversed codomain conversion to the new domain's
context with `CtxConvT`.

This closes the direct `pi` / `pi` critical pair without `J`, `D`,
`PEqT`, uniqueness, or Pi injectivity. The common reduct is literally
the common source. The version `_at` also permits separate universe
witnesses and the outer `ParRedT.conv` chains leading to a common index.

Scope: these are lemmas for two uses of the `pi` constructor (possibly
followed by index conversions). They do not invert an arbitrary step
out of a Pi expression, and they do not prove Pi injectivity of `ConvT`.
The EnvWfT-fronted data definitions use the three-part endpoint package
directly. The `Nonempty` theorems wrap that data; no choice axiom is
needed. These constructions assert no bound on derivation size.

A concrete nontrivial cycle also rules out rankings that strictly
decrease on every nonidentity `ParRedT` step. This is not an obstruction
to a measure on a metatheoretic proof's recursive calls.
-/

namespace Rcic.Declarative

section PiDiamond

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
variable {A A' B B' : Expr Nat} {u v : Level}

/-- Reverse a `pi` arm once the right component typings have been
supplied. The codomain evidence initially lives under the left domain,
just as in `ParRedT.pi`; `CtxConvT` moves it under the right domain. -/
def parRedT_pi_reverse_of_endpoints
    (hcl : EnvClosed E)
    (hA : HasTyT E n Γ A (.sort u))
    (hA' : HasTyT E n Γ A' (.sort u))
    (hc : ConvT E n Γ A A' (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hB' : HasTyT E n (.assumption A :: Γ) B' (.sort v))
    (hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    ParRedT PEq E n Γ (.pi A' B') (.pi A B) (.sort (.imax u v)) :=
  let hctx : CtxConvT E n (.assumption A :: Γ) (.assumption A' :: Γ) :=
    .assumption (ctxConvT_refl Γ) hA hA' hc
  .pi Γ A' A B' B u v
    hA'
    (.symm Γ A A' (.sort u) hc)
    (hasTyT_ctx hcl hctx hB')
    (convT_ctx hcl hctx
      (.symm (.assumption A :: Γ) B B' (.sort v) hcB))
    (.pi Γ A u B v hA hB)

/-- Construct a reversed `pi` arm as data. Both endpoint supplies are
discharged by `EnvWfT`, so there is no elimination from `Nonempty` and
no additional hypothesis beyond the well-formed environment/context. -/
def parRedT_pi_reverse_data
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (hc : ConvT E n Γ A A' (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    ParRedT PEq E n Γ (.pi A' B') (.pi A B) (.sort (.imax u v)) :=
  let hA' := (endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) hΓ hc).2.1
  let hB' := (endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) (.assumption Γ A u hΓ hA) hcB).2.1
  parRedT_pi_reverse_of_endpoints
    (envClosed_of_envWfT hW) hA hA' hc hB hB' hcB

/-- Under `EnvWfT` and a well-formed context, every direct `pi` arm can
be reversed in one step. The original arm's carried result typing is
not needed: endpoint determination supplies the component typings. -/
theorem parRedT_pi_reverse
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    (hA : HasTyT E n Γ A (.sort u))
    (hc : ConvT E n Γ A A' (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hcB : ConvT E n (.assumption A :: Γ) B B' (.sort v)) :
    Nonempty (ParRedT PEq E n Γ (.pi A' B') (.pi A B) (.sort (.imax u v))) :=
  ⟨parRedT_pi_reverse_data hW hΓ hA hc hB hcB⟩

/-- Construct both steps back to the common source as data. Each branch
uses its own universe witnesses and conversion to the common index;
the construction requires no comparison of those witnesses. -/
def parRedT_pi_pi_common_source_data_at
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A₁ A₂ B₁ B₂ T : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : HasTyT E n Γ A (.sort u₁))
    (hc₁ : ConvT E n Γ A A₁ (.sort u₁))
    (hB₁ : HasTyT E n (.assumption A :: Γ) B (.sort v₁))
    (hcB₁ : ConvT E n (.assumption A :: Γ) B B₁ (.sort v₁))
    (hidx₁ : TyConvT E n Γ (.sort (.imax u₁ v₁)) T)
    (hA₂ : HasTyT E n Γ A (.sort u₂))
    (hc₂ : ConvT E n Γ A A₂ (.sort u₂))
    (hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v₂))
    (hcB₂ : ConvT E n (.assumption A :: Γ) B B₂ (.sort v₂))
    (hidx₂ : TyConvT E n Γ (.sort (.imax u₂ v₂)) T) :
    ParRedT PEq E n Γ (.pi A₁ B₁) (.pi A B) T ×
    ParRedT PEq E n Γ (.pi A₂ B₂) (.pi A B) T :=
  let hr₁ := parRedT_pi_reverse_data (PEq := PEq) hW hΓ hA₁ hc₁ hB₁ hcB₁
  let hr₂ := parRedT_pi_reverse_data (PEq := PEq) hW hΓ hA₂ hc₂ hB₂ hcB₂
  ⟨.conv Γ _ _ _ T hr₁ hidx₁, .conv Γ _ _ _ T hr₂ hidx₂⟩

/-- Two direct `pi` arms, with possibly different universe witnesses
and index-conversion chains, join at their literal common source.
Both outgoing steps have the specified common index `T`. -/
theorem parRedT_pi_pi_common_source_at
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A₁ A₂ B₁ B₂ T : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : HasTyT E n Γ A (.sort u₁))
    (hc₁ : ConvT E n Γ A A₁ (.sort u₁))
    (hB₁ : HasTyT E n (.assumption A :: Γ) B (.sort v₁))
    (hcB₁ : ConvT E n (.assumption A :: Γ) B B₁ (.sort v₁))
    (hidx₁ : TyConvT E n Γ (.sort (.imax u₁ v₁)) T)
    (hA₂ : HasTyT E n Γ A (.sort u₂))
    (hc₂ : ConvT E n Γ A A₂ (.sort u₂))
    (hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v₂))
    (hcB₂ : ConvT E n (.assumption A :: Γ) B B₂ (.sort v₂))
    (hidx₂ : TyConvT E n Γ (.sort (.imax u₂ v₂)) T) :
    Nonempty
      (ParRedT PEq E n Γ (.pi A₁ B₁) (.pi A B) T ×
       ParRedT PEq E n Γ (.pi A₂ B₂) (.pi A B) T) :=
  ⟨parRedT_pi_pi_common_source_data_at
    hW hΓ hA₁ hc₁ hB₁ hcB₁ hidx₁ hA₂ hc₂ hB₂ hcB₂ hidx₂⟩

/-- Star-form diamond for the direct `pi` / `pi` critical pair, also
covering its outer index-conversion chains. The joins coincide exactly;
no hypothesis about the abstract `PEq` parameter is used. -/
theorem parRedT_pi_pi_diamond_at
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A₁ A₂ B₁ B₂ T : Expr Nat} {u₁ v₁ u₂ v₂ : Level}
    (hA₁ : HasTyT E n Γ A (.sort u₁))
    (hc₁ : ConvT E n Γ A A₁ (.sort u₁))
    (hB₁ : HasTyT E n (.assumption A :: Γ) B (.sort v₁))
    (hcB₁ : ConvT E n (.assumption A :: Γ) B B₁ (.sort v₁))
    (hidx₁ : TyConvT E n Γ (.sort (.imax u₁ v₁)) T)
    (hA₂ : HasTyT E n Γ A (.sort u₂))
    (hc₂ : ConvT E n Γ A A₂ (.sort u₂))
    (hB₂ : HasTyT E n (.assumption A :: Γ) B (.sort v₂))
    (hcB₂ : ConvT E n (.assumption A :: Γ) B B₂ (.sort v₂))
    (hidx₂ : TyConvT E n Γ (.sort (.imax u₂ v₂)) T) :
    ∃ d : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ (.pi A₁ B₁) d T) ∧
      Nonempty (ParRedTStar PEq E n Γ (.pi A₂ B₂) d T) := by
  obtain ⟨⟨hr₁, hr₂⟩⟩ := parRedT_pi_pi_common_source_at
    (PEq := PEq) hW hΓ hA₁ hc₁ hB₁ hcB₁ hidx₁ hA₂ hc₂ hB₂ hcB₂ hidx₂
  have hs : HasTyT E n Γ (.pi A B) T :=
    hasTyT_of_tyConvT (.pi Γ A u₁ B v₁ hA₁ hB₁) hidx₁
  exact ⟨.pi A B,
    ⟨.tail hr₁ (.refl Γ (.pi A B) T hs)⟩,
    ⟨.tail hr₂ (.refl Γ (.pi A B) T hs)⟩⟩

/-- The direct `pi` / `pi` diamond at the constructor's own index. -/
theorem parRedT_pi_pi_diamond
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {A₁ A₂ B₁ B₂ : Expr Nat}
    (hA : HasTyT E n Γ A (.sort u))
    (hc₁ : ConvT E n Γ A A₁ (.sort u))
    (hc₂ : ConvT E n Γ A A₂ (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v))
    (hcB₁ : ConvT E n (.assumption A :: Γ) B B₁ (.sort v))
    (hcB₂ : ConvT E n (.assumption A :: Γ) B B₂ (.sort v)) :
    ∃ d : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ (.pi A₁ B₁) d (.sort (.imax u v))) ∧
      Nonempty (ParRedTStar PEq E n Γ (.pi A₂ B₂) d (.sort (.imax u v))) :=
  parRedT_pi_pi_diamond_at hW hΓ
    hA hc₁ hB hcB₁ (.refl Γ (.sort (.imax u v)))
    hA hc₂ hB hcB₂ (.refl Γ (.sort (.imax u v)))

end PiDiamond

/-- The source of the concrete nontrivial cycle: `forall P : Prop, P`. -/
def parRedTPiCycleSource : Expr Nat := .pi (.sort .zero) (.bvar 0)

/-- A different domain level expression and a beta-expanded codomain. -/
def parRedTPiCycleTarget : Expr Nat :=
  .pi (.sort (.max .zero .zero))
    (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0))

/-- The common type index, retained in the Pi constructor's exact form. -/
def parRedTPiCycleType : Expr Nat := .sort (.imax (.succ .zero) .zero)

/-- Non-vacuity: a nontrivial two-way cycle in the empty environment.
The domain has a nonliteral `eqN` change and the dependent codomain has
been beta-expanded. `PEq` is empty, so neither direction can use a
proof-irrelevance leaf. The bound codomain variable makes the context
transport substantive. -/
theorem pin_parRedT_pi_sort_beta_cycle :
    parRedTPiCycleSource ≠ parRedTPiCycleTarget ∧
    Nonempty
      (ParRedT (fun _ _ _ _ => Empty) emptyEnv 0 []
         parRedTPiCycleSource parRedTPiCycleTarget parRedTPiCycleType ×
       ParRedT (fun _ _ _ _ => Empty) emptyEnv 0 []
         parRedTPiCycleTarget parRedTPiCycleSource parRedTPiCycleType) := by
  constructor
  · intro h
    unfold parRedTPiCycleSource parRedTPiCycleTarget at h
    cases h
  have hA : HasTyT emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
    .sort [] .zero
  have hc : ConvT emptyEnv 0 [] (.sort .zero)
      (.sort (.max .zero .zero)) (.sort (.succ .zero)) :=
    .sorts [] .zero (.max .zero .zero) (fun _ => rfl)
  have hB : HasTyT emptyEnv 0 [.assumption (.sort .zero)]
      (.bvar 0) (.sort .zero) := .bvar _ 0 _ rfl
  have hbeta : ConvT emptyEnv 0 [.assumption (.sort .zero)]
      (.app (.lam (.sort .zero) (.bvar 0)) (.bvar 0))
      (.bvar 0) (.sort .zero) :=
    .beta _ (.sort .zero) (.bvar 0) (.bvar 0) (.sort .zero) (.succ .zero)
      (.sort _ .zero) (.bvar _ 0 _ rfl) hB
  have hcB := ConvT.symm _ _ _ _ hbeta
  obtain ⟨hrt⟩ :=
    (DT009T_endpoints_envWfT EnvWfT.empty CtxWfT.nil
      (ConvT.pi _ _ _ _ _ _ _ hc hcB)).2
  obtain ⟨hr⟩ := parRedT_pi_reverse (PEq := fun _ _ _ _ => Empty)
    EnvWfT.empty CtxWfT.nil hA hc hB hcB
  exact ⟨⟨ParRedT.pi _ _ _ _ _ _ _ hA hc hB hcB hrt, hr⟩⟩

/-- The reverse direction of the concrete cycle, as a standalone pin. -/
theorem pin_parRedT_pi_reverse_sort_beta :
    Nonempty (ParRedT (fun _ _ _ _ => Empty) emptyEnv 0 []
      parRedTPiCycleTarget parRedTPiCycleSource parRedTPiCycleType) := by
  obtain ⟨⟨_, hr⟩⟩ := pin_parRedT_pi_sort_beta_cycle.2
  exact ⟨hr⟩

universe uRank

/-- No ranking into an asymmetric relation decreases on every
nonidentity step of this `ParRedT` instance. This excludes a ranking
of the reduction relation itself; it makes no claim about measures on
the recursive calls of a metatheoretic proof. -/
theorem no_parRedT_asymmetric_rank {α : Sort uRank} {r : α → α → Prop}
    (hasymm : ∀ {x y : α}, r x y → r y x → False) :
    ¬ ∃ rank : Expr Nat → α,
      ∀ {a b T : Expr Nat},
        ParRedT (fun _ _ _ _ => Empty) emptyEnv 0 [] a b T →
        a ≠ b → r (rank b) (rank a) := by
  rintro ⟨rank, hstrict⟩
  obtain ⟨hne, hcycle⟩ := pin_parRedT_pi_sort_beta_cycle
  obtain ⟨⟨hf, hr⟩⟩ := hcycle
  exact hasymm (hstrict hf hne) (hstrict hr (fun h => hne h.symm))

/-- In particular, no natural-number ranking strictly decreases on
every nonidentity `ParRedT` step, even with empty `PEq` and environment. -/
theorem no_parRedT_strict_nat_rank :
    ¬ ∃ rank : Expr Nat → Nat,
      ∀ {a b T : Expr Nat},
        ParRedT (fun _ _ _ _ => Empty) emptyEnv 0 [] a b T →
        a ≠ b → rank b < rank a :=
  no_parRedT_asymmetric_rank (α := Nat) (r := fun a b => a < b)
    (fun h₁ h₂ => Nat.lt_asymm h₁ h₂)

#print axioms parRedT_pi_reverse_of_endpoints
#print axioms parRedT_pi_reverse_data
#print axioms parRedT_pi_reverse
#print axioms parRedT_pi_pi_common_source_data_at
#print axioms parRedT_pi_pi_common_source_at
#print axioms parRedT_pi_pi_diamond_at
#print axioms parRedT_pi_pi_diamond
#print axioms pin_parRedT_pi_sort_beta_cycle
#print axioms pin_parRedT_pi_reverse_sort_beta
#print axioms no_parRedT_asymmetric_rank
#print axioms no_parRedT_strict_nat_rank

end Rcic.Declarative
