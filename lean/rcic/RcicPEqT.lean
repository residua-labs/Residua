import rcic.RcicDeclarative

/-!
# S3 / plain side — `PEqT`: raw comparison modulo proof positions

For #6293 (cc ruling: the ATR mutual moves to the PLAIN typed side over
`EnvWfT`). This is the plain twin of `Rcic.Declarative.Ann.PEq`
(`RcicAnnPEq.lean`) — same loose-leaf design, on erased expressions with
`HasTyT` leaf evidence. Pushed early as the Seg-B dependency; `k3c`
stacks ctx-transport (`CtxConvT`) work on it.

The notation `a ≈P b` denotes the raw constructor relation below.
Its structural clauses walk a shared skeleton (levels related by `eqN`,
binder cases extending the context by the LEFT declaration). The loose
`proof` leaf relates `p : P` and `q : Q` with `P Q : sort 0`, without
requiring a common proposition. Structural clauses carry no typing
premises for their whole endpoints.

The raw relation is reflexive but NOT transitive: `RcicPEqTProofFront`
constructs closed p, q, r in emptyEnv with p ≈P q and q ≈P r but no
p ≈P r. Raw application congruence can put a heterogeneous proof into
an incompatible argument position, producing an untypable endpoint.
Any equivalence claim must name a restricted interface and prove its
laws; no such claim follows here. The typed-endpoint case remains a
separate obligation, not a consequence of excluding this counterexample.

Consequences of the loose leaf, recorded because they shape the kit:

- **`refl` is unconditional** (proved below): every clause is
  self-composing.
- **`symm` is NOT free**: the `lam`/`pi`/`letE` clauses put the body at
  the left declaration's context (`A :: Γ`); symmetry needs the body
  read at `A' :: Γ`, i.e. ctx-transport of `PEqT` across `A ≈P A'` —
  k3c's `CtxConvT` work. The `proof` leaf itself is symmetric.
- **`trans` is free only for (leaf,leaf)**. The existing general
  conditional consumers do not establish raw transitivity: their
  universal binder and proof-transport fronts are refuted in
  `RcicPEqTCtxFrontRefutation` and `RcicPEqTProofFront`. Even adding
  source-proposition typing alone does not repair the proof fronts.
- **Excluding the proof leaf at type endpoints is a typed obligation**.
  It does not follow just from the constructor list. The sort and
  Pi-rigidity arguments must carry and use their actual typing inputs.

The `proof` leaf carries its `HasTyT` evidence: those premises are
sub-derivations of whatever derivation-bundle holds the `PEqT`, which
is what the S3 measure's cited-premises discipline consumes.
-/

namespace Rcic.Declarative

/-- `a ≈P b`: raw structural comparison with loose proof leaves.
    Skeleton clauses per constructor, `eqN` on levels, binders extend by
    the LEFT declaration; the `proof` leaf relates any two proofs of any
    two propositions. `Type`-valued (unlike the Ann `PEq`, which sits in
    `Prop`): the `proof` leaf's `HasTyT` premises are data — they are the
    cited leaves the S3 measure counts. The raw relation is not
    transitive; see `RcicPEqTProofFront`. -/
inductive PEqT (E : ResolvedEnv) (n : Nat) :
    LCtx → Expr Nat → Expr Nat → Type where
  | bvar (Γ : LCtx) (i : Nat) :
      PEqT E n Γ (.bvar i) (.bvar i)
  | sort (Γ : LCtx) (l l' : Level) (h : eqN l l') :
      PEqT E n Γ (.sort l) (.sort l')
  | const (Γ : LCtx) (r : Nat) (ls ls' : List Level) (h : eqNList ls ls') :
      PEqT E n Γ (.const r ls) (.const r ls')
  | app (Γ : LCtx) (f f' a a' : Expr Nat)
      (hf : PEqT E n Γ f f') (ha : PEqT E n Γ a a') :
      PEqT E n Γ (.app f a) (.app f' a')
  | lam (Γ : LCtx) (A A' b b' : Expr Nat)
      (hA : PEqT E n Γ A A')
      (hb : PEqT E n (.assumption A :: Γ) b b') :
      PEqT E n Γ (.lam A b) (.lam A' b')
  | pi (Γ : LCtx) (A A' B B' : Expr Nat)
      (hA : PEqT E n Γ A A')
      (hB : PEqT E n (.assumption A :: Γ) B B') :
      PEqT E n Γ (.pi A B) (.pi A' B')
  | letE (Γ : LCtx) (A A' v v' b b' : Expr Nat)
      (hA : PEqT E n Γ A A') (hv : PEqT E n Γ v v')
      (hb : PEqT E n (.letBinding A v :: Γ) b b') :
      PEqT E n Γ (.letE A v b) (.letE A' v' b')
  | lit (Γ : LCtx) (t : Nat) :
      PEqT E n Γ (.lit t) (.lit t)
  /-- cc's loose leaf: two proofs, no common proposition. The `irr` arm
      of `ConvT` discharges to this at the root with zero steps; in the
      P-component the leaf is lifted by `irr` at the evidence `P` after
      reconciling `P ≡ Tₗ ≡ Tᵣ ≡ Q` — two uniqueness calls + one
      recursive call on the index `≈P`, all on bundle sub-derivations. -/
  | proof (Γ : LCtx) (p q P Q : Expr Nat)
      (hP : HasTyT E n Γ P (.sort .zero))
      (hQ : HasTyT E n Γ Q (.sort .zero))
      (hp : HasTyT E n Γ p P)
      (hq : HasTyT E n Γ q Q) :
      PEqT E n Γ p q

/-- `eqN` is reflexive. (Mirrored privately rather than imported: the
    PEqT kit must not pull the untyped relation.) -/
private theorem peqT_eqN_refl (l : Level) : eqN l l := fun _ => rfl

private theorem peqT_eqNList_refl : (ls : List Level) → eqNList ls ls
  | [] => True.intro
  | l :: ls => ⟨peqT_eqN_refl l, peqT_eqNList_refl ls⟩

/-- `≈P` is reflexive — unconditional: every clause is self-composing
    and the level relations are reflexive. -/
def PEqT.refl {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (a : Expr Nat) → PEqT E n Γ a a
  | .bvar i => .bvar Γ i
  | .sort l => .sort Γ l l (peqT_eqN_refl l)
  | .const r ls => .const Γ r ls ls (peqT_eqNList_refl ls)
  | .app f a => .app Γ f f a a (PEqT.refl f) (PEqT.refl a)
  | .lam A b => .lam Γ A A b b (PEqT.refl A) (PEqT.refl b)
  | .pi A B => .pi Γ A A B B (PEqT.refl A) (PEqT.refl B)
  | .letE A v b =>
      .letE Γ A A v v b b (PEqT.refl A) (PEqT.refl v) (PEqT.refl b)
  | .lit t => .lit Γ t

/-! ## leaf projections

The four typing premises of a `proof` leaf, re-exported as named
projections and packaged into the per-side existentials the
P-component consumes (`p` is a proof of SOME Prop; `q` likewise). -/

/-- left proposition typing of a proof leaf. -/
def PEqT.proof.propL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {p P q Q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (_hp : HasTyT E n Γ p P)
    (_hQ : HasTyT E n Γ Q (.sort .zero)) (_hq : HasTyT E n Γ q Q) :
    HasTyT E n Γ P (.sort .zero) := hP

/-- left proof typing of a proof leaf. -/
def PEqT.proof.proofL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {p P q Q : Expr Nat}
    (_hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P)
    (_hQ : HasTyT E n Γ Q (.sort .zero)) (_hq : HasTyT E n Γ q Q) :
    HasTyT E n Γ p P := hp

/-- right proposition typing of a proof leaf. -/
def PEqT.proof.propR {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {p P q Q : Expr Nat}
    (_hP : HasTyT E n Γ P (.sort .zero)) (_hp : HasTyT E n Γ p P)
    (hQ : HasTyT E n Γ Q (.sort .zero)) (_hq : HasTyT E n Γ q Q) :
    HasTyT E n Γ Q (.sort .zero) := hQ

/-- right proof typing of a proof leaf. -/
def PEqT.proof.proofR {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {p P q Q : Expr Nat}
    (_hP : HasTyT E n Γ P (.sort .zero)) (_hp : HasTyT E n Γ p P)
    (_hQ : HasTyT E n Γ Q (.sort .zero)) (hq : HasTyT E n Γ q Q) :
    HasTyT E n Γ q Q := hq

/-- the left endpoint packaged: `p` is a proof of SOME proposition. -/
def PEqT.proof.leftPrf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {p P q Q : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P)
    (_hQ : HasTyT E n Γ Q (.sort .zero)) (_hq : HasTyT E n Γ q Q) :
    Σ' P, HasTyT E n Γ P (.sort .zero) ×' HasTyT E n Γ p P := ⟨P, hP, hp⟩

/-- the right endpoint packaged: `q` is a proof of SOME proposition. -/
def PEqT.proof.rightPrf {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {p P q Q : Expr Nat}
    (_hP : HasTyT E n Γ P (.sort .zero)) (_hp : HasTyT E n Γ p P)
    (hQ : HasTyT E n Γ Q (.sort .zero)) (hq : HasTyT E n Γ q Q) :
    Σ' Q, HasTyT E n Γ Q (.sort .zero) ×' HasTyT E n Γ q Q := ⟨Q, hQ, hq⟩

end Rcic.Declarative
