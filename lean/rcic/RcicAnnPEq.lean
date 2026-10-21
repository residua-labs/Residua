import rcic.RcicAnnDecl

/-!
# S3 / Seg-B — `PEq`: equality of `ExprA` modulo proof positions

For #6293 (cc rulings 08:44Z, loose-leaf precision, and the Seg-B split:
this file is the definition + the free core kit; `k3c` owns F-ι★-7
(`ctx_red`) and F-ι★-9 (`lift`/`instantiate`/`subst`); irrpost owns F-ι★-8
(the measure) and F-ι★-2/F-ι★-11 (`sort_eqN`, typing-respects-erasure)).

`a ≈P b` = "equal after replacing each proof by ★": the constructor clauses
walk the shared skeleton (level annotations related by `eqN`, binder cases
extending the context by the LEFT declaration), and the `proof` leaf is
**cc's loose leaf**: two proofs with NO common proposition — `p : P`,
`q : Q`, `P Q : sort 0` — so the relation is an equivalence without
uniqueness-of-types. The common-P obligation lives in the P-component
(`peq_convA`) as calls into uniqueness at smaller derivations, not here.

Consequences of the loose leaf, recorded here because they shape the kit:

- **`refl` is unconditional** (proved below): every clause is
  self-composing.
- **`symm` is NOT free**: the `lam`/`pi`/`letE` clauses put the body at the
  left declaration's context (`A :: Γ`); symmetry needs the body read at
  `A' :: Γ`, i.e. `ctx`-transport of `PEq` across `A ≈P A'` — F-ι★-7 (k3c).
  The `proof` leaf itself is symmetric.
- **`trans` is free (leaf,leaf)**: two proof-leaves compose to a leaf on
  the endpoints — that is exactly why the leaf is loose. `(structural,
  structural)` trans additionally needs `ctx`-transport at binder clauses
  (same dependency). Mixed cases (`p ≈P q` a leaf, `q ≈P r` structural)
  need `r` to be a proof — `r`'s type is `≈P`-equal to `q`'s by
  typing-respects-erasure (F-ι★-2) and then Prop-sorted by `sort_eqN`
  (F-ι★-11) — so in the TYPED domain trans holds, but the lemma is
  conditional on the mutual, not a kit-freebie.
- **The leaf never fires on types**: a proof has a `sort 0`-sorted TYPE;
  a type has a `sort`-typed type. So on type-level `PEq` is purely
  structural — this is what makes `sort_eqN` and the Π-rigidity
  corollaries (X, `sortRow`) available off a `PEq` middle.

The `proof` leaf carries its `HasTyA` evidence: those premises are
sub-derivations of whatever derivation-bundle holds the `PEq`, which is
what the S3 measure's cited-premises discipline consumes.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- `a ≈P b`: equal after replacing each proof-position subterm by ★.
    Skeleton clauses per constructor, `eqN` on level annotations, binders
    extend by the LEFT declaration; the `proof` leaf relates any two proofs
    of any two propositions. -/
inductive PEq (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → ExprA → ExprA → Prop where
  | bvar (Γ : LCtxA) (i : Nat) :
      PEq E I n Γ (.bvar i) (.bvar i)
  | sort (Γ : LCtxA) (l l' : Level) (h : eqN l l') :
      PEq E I n Γ (.sort l) (.sort l')
  | const (Γ : LCtxA) (r : Nat) (ls ls' : List Level) (h : eqNList ls ls') :
      PEq E I n Γ (.const r ls) (.const r ls')
  | app (Γ : LCtxA) (f f' a a' : ExprA)
      (hf : PEq E I n Γ f f') (ha : PEq E I n Γ a a') :
      PEq E I n Γ (.app f a) (.app f' a')
  | lam (Γ : LCtxA) (A A' b b' : ExprA) (u u' : Level)
      (hu : eqN u u') (hA : PEq E I n Γ A A')
      (hb : PEq E I n (.assumption A :: Γ) b b') :
      PEq E I n Γ (.lam A u b) (.lam A' u' b')
  | pi (Γ : LCtxA) (A A' B B' : ExprA) (u u' v v' : Level)
      (hu : eqN u u') (hv : eqN v v') (hA : PEq E I n Γ A A')
      (hB : PEq E I n (.assumption A :: Γ) B B') :
      PEq E I n Γ (.pi A u B v) (.pi A' u' B' v')
  | letE (Γ : LCtxA) (A A' v v' b b' : ExprA)
      (hA : PEq E I n Γ A A') (hv : PEq E I n Γ v v')
      (hb : PEq E I n (.letBinding A v :: Γ) b b') :
      PEq E I n Γ (.letE A v b) (.letE A' v' b')
  | lit (Γ : LCtxA) (t : Nat) :
      PEq E I n Γ (.lit t) (.lit t)
  /-- cc's loose leaf: two proofs, no common proposition. The `irr` arm of
      `ConvA` discharges to this at the root with zero `ParRedA` steps; in
      the P-component (`peq_convA`) the leaf is lifted by `irr` at the
      evidence `P` after reconciling `P ≡ Tₗ ≡ Tᵣ ≡ Q` — two uniqueness
      calls + one recursive call on the index `≈P`, all on bundle
      sub-derivations. -/
  | proof (Γ : LCtxA) (p q P Q : ExprA)
      (hP : HasTyA E I n Γ P (.sort .zero))
      (hQ : HasTyA E I n Γ Q (.sort .zero))
      (hp : HasTyA E I n Γ p P)
      (hq : HasTyA E I n Γ q Q) :
      PEq E I n Γ p q

/-- `eqN` is reflexive. (Mirrored privately here rather than imported from
    `RcicParRedCore`: the PEq kit must not pull the untyped relation.) -/
private theorem peq_eqN_refl (l : Level) : eqN l l := fun _ => rfl

private theorem peq_eqNList_refl : (ls : List Level) → eqNList ls ls
  | [] => True.intro
  | l :: ls => ⟨peq_eqN_refl l, peq_eqNList_refl ls⟩

/-- `≈P` is reflexive — unconditional: every clause is self-composing and
    the level relations are reflexive. -/
theorem PEq.refl {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} : (a : ExprA) → PEq E I n Γ a a
  | .bvar i => .bvar Γ i
  | .sort l => .sort Γ l l (peq_eqN_refl l)
  | .const r ls => .const Γ r ls ls (peq_eqNList_refl ls)
  | .app f a => .app Γ f f a a (PEq.refl f) (PEq.refl a)
  | .lam A u b =>
      .lam Γ A A b b u u (peq_eqN_refl u) (PEq.refl A) (PEq.refl b)
  | .pi A u B v =>
      .pi Γ A A B B u u v v (peq_eqN_refl u) (peq_eqN_refl v)
        (PEq.refl A) (PEq.refl B)
  | .letE A v b =>
      .letE Γ A A v v b b (PEq.refl A) (PEq.refl v) (PEq.refl b)
  | .lit t => .lit Γ t

end Rcic.Declarative.Ann
