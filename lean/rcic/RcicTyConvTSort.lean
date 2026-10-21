import rcic.RcicTypedConv

/-!
# `RcicTyConvTSort` — the plain sort-chain collapse kit

The plain twin of `Ann.convT_of_tyConvT_sort` (`RcicAnnRowsSupply`): with
the LEFT end typed at a sort, a `TyConvT` chain to any right end
collapses to ONE `ConvT` at that sort. This is the adapter
`TypedRowsWf.sortRow`'s discharge consumes — DeepSeek flagged
`sortRowT`'s `irr` exclusion as needing exactly it: collapsing the
chain produces the genuine `ConvT` at a sort the char lemmas read,
with no `irr` arm manufactured anywhere in the collapse (every step
re-sorts through `convT_of_tyConv` at the uniqueness chain — an `irr`
step in a sort chain would need its `P` to be a `sort _` typed at
`sort .zero`, which the collapse never constructs).

The Ann route annotates and re-sorts each step through `annTyA`
coherence (annotation type uniqueness) behind `InScope`. The plain
route replaces both ingredients with named leaves, the same
`parRedT_to_convT` discipline (none assumed — each points at the
semantic route that discharges it):

* `hEnd` — the sort-indexed endpoint typing: the left end of a
  `ConvT` at a sort is typed at that sort. The `hasTyT_sort_of_convT`
  shape; discharged by `convA_hasTy_left` + erasure through the
  semantic-prefix bridge (`RcicAnnRowsSupply`'s adapter is the
  producer today, `InScope`-gated).
* `hUniq` — type uniqueness: `a : A` and `a : B` give `TyConvT A B`.
  Needed only in the `of` arm, to re-sort a step `ConvT a b (sort v)`
  to the chain's premise sort `u`: uniqueness at `a` gives
  `TyConvT (sort u) (sort v)`, and `convT_of_tyConv` retypes `h`
  along its symmetric. `DT012T_type_uniqueness` is the producer today
  (`InScope`-gated).

* `refl`: `ConvT.refl` at the premise typing — a refl chain invents
  no typing of its own.
* `of`: `h : ConvT a b (sort v)`; `hEnd` types `a` at `sort v`,
  `hUniq` gives `TyConvT (sort u) (sort v)`, `convT_of_tyConv` lands
  `ConvT a b (sort u)` directly — no `sortConvChar`/`eqN` read is
  needed anywhere (the chain re-types the conversion, it does not
  assert level equality).
* `trans`: the first half collapses at `sort u`; its right end's
  typing at the same sort is `hEnd` applied to the `symm`'d
  conversion; the second half collapses against it.

No `sorry`, no new axiom, no `InScope`, no `AnnEnvA`.
-/

namespace Rcic.Declarative

/-- the `of` arm, named: a conversion at `sort v` re-sorts to any sort
    the left end is also typed at — uniqueness at the endpoint supplies
    the `TyConvT` between the sorts, `convT_of_tyConv` retypes. -/
def convT_sort_retype {E : ResolvedEnv} {n : Nat}
    (hUniq : ∀ {Γ' : LCtx} {a A B : Expr Nat}, CtxWfT E n Γ' →
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ a (.sort u)) (h : ConvT E n Γ a b (.sort v))
    (hav : HasTyT E n Γ a (.sort v)) :
    ConvT E n Γ a b (.sort u) :=
  convT_of_tyConv h (hUniq hΓ hA hav).symmT

/-- THE PLAIN CHAIN ADAPTER: with the left end typed at a sort, a
    `TyConvT` chain to any right end collapses to one `ConvT` at that
    sort — `Ann.convT_of_tyConvT_sort`'s plain twin, no annotation
    roundtrip. The two hypotheses are the honest leaves: endpoint
    typing at sort indices (`convA_hasTy_left` + erasure in scope) and
    type uniqueness (`DT012T` in scope). -/
def convT_of_tyConvT_sort {E : ResolvedEnv} {n : Nat}
    (hEnd : ∀ {Γ' : LCtx} {a b : Expr Nat} {v : Level},
      CtxWfT E n Γ' → ConvT E n Γ' a b (.sort v) →
      Nonempty (HasTyT E n Γ' a (.sort v)))
    (hUniq : ∀ {Γ' : LCtx} {a A B : Expr Nat}, CtxWfT E n Γ' →
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ a (.sort u)) (h : TyConvT E n Γ a b) :
    Nonempty (ConvT E n Γ a b (.sort u)) := by
  induction h with
  | refl => exact ⟨.refl _ _ _ hA⟩
  | of _ _ v h =>
      obtain ⟨hav⟩ := hEnd hΓ h
      exact ⟨convT_sort_retype hUniq hΓ hA h hav⟩
  | trans _ _ _ _ _ ih1 ih2 =>
      obtain ⟨c1⟩ := ih1 hA
      obtain ⟨hmid⟩ := hEnd hΓ c1.symm
      obtain ⟨c2⟩ := ih2 hmid
      exact ⟨.trans _ _ _ _ _ c1 c2⟩

/-- the sort-endpoint specialization `sortRow` consumes: a `TyConvT`
    chain between two sorts collapses to a `ConvT` between them at
    SOME sort (`succ u`, witnessed by the premise's own sort-typing —
    `HasTyT.sort` needs no environment premise). The char lemma
    (`sortConvCharT`-family) then reads `eqN u v` off the endpoints. -/
theorem tyConvT_sort_collapse {E : ResolvedEnv} {n : Nat}
    (hEnd : ∀ {Γ' : LCtx} {a b : Expr Nat} {v : Level},
      CtxWfT E n Γ' → ConvT E n Γ' a b (.sort v) →
      Nonempty (HasTyT E n Γ' a (.sort v)))
    (hUniq : ∀ {Γ' : LCtx} {a A B : Expr Nat}, CtxWfT E n Γ' →
      HasTyT E n Γ' a A → HasTyT E n Γ' a B → TyConvT E n Γ' A B)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level}
    (h : TyConvT E n Γ (.sort u) (.sort v)) :
    ∃ w : Level, Nonempty (ConvT E n Γ (.sort u) (.sort v) (.sort w)) :=
  ⟨_, convT_of_tyConvT_sort hEnd hUniq hΓ (.sort _ _) h⟩

end Rcic.Declarative
