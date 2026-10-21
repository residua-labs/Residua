import rcic.RcicPEqTSubst

/-!
# `PEqT` conditional `symm` / `trans` — Seg-B kit, explicit `CtxConvT` premises

For #6293 (plain ruling): the conditional half of the `PEqT` kit —
symmetry and transitivity — where the `PEqT` binder clauses extend the
context by the LEFT declaration (`RcicPEqT.lean` header: "`symm` is NOT
free … the `lam`/`pi`/`letE` clauses put the body at the left
declaration's context"). The `proof` leaf is symmetric and leaf×leaf
transitive unconditionally; the structural binder cases are conditional
on context transport, stated here as EXPLICIT `CtxConvT`-supplying
premises so the missing piece is visible at the type, not hidden in a
`Prop` wrapper or assumed from the S3 mutual.

## Status of the raw universal contracts

The functions below remain valid conditional consumers. Their raw
universal suppliers cannot be supplied: `RcicPEqTCtxFrontRefutation`
refutes hdom and hlet in both directions for every E and n, and
`RcicPEqTProofFront` refutes hproofL and hproofR already in emptyEnv.
The latter file also gives a closed counterexample to raw PEqT
transitivity. Adding only Q : sort 0 to the proof fronts is insufficient.
A restricted interface must carry its actual typing/context inputs and
prove its laws separately; no typed-endpoint equivalence is claimed here.

## The legacy premise contract (per declaration, exact directions)

`PEqT.symm hcl hdom hlet` consumes:

- `hdom : ∀ {Δ A A'}, PEqT E n Δ A A' →
    CtxConvT E n (.assumption A :: Δ) (.assumption A' :: Δ)` —
  the `lam`/`pi` domain step, LEFT→RIGHT: after `symm` the body is read
  at the right declaration's context, so the derivation at `A :: Δ`
  transports across a conversion to `A' :: Δ`. Discharging this needs
  `A, A' : sort u` at a COMMON `u` plus `ConvT Δ A A' (sort u)` in the
  target — endpoint-domain sort equality (the F-ι★-11 surface).
- `hlet : ∀ {Δ A A' v v'}, PEqT E n Δ A A' → PEqT E n Δ v v' →
    CtxConvT E n (.letBinding A v :: Δ) (.letBinding A' v' :: Δ)` —
  the `letE` step, LEFT→RIGHT. `CtxConvT.letBinding` additionally
  requires `ConvT Δ v v' A` on the bound values and `v' : A'` — the
  same sort-equality obligation PLUS value conversion.

`PEqT.trans hcl hdom hlet hproofL hproofR` consumes:

- `hdom` — the SAME shape REVERSED: `CtxConvT (A' :: Δ) (A :: Δ)`,
  pulling the second derivation's body back into the FIRST binder's
  context (the result `lam`/`pi` extends by the left endpoint's
  declaration). Sort equality is again the discharge obligation.
- `hlet` — reversed likewise (`(.letBinding A' v' :: Δ)` →
  `(.letBinding A v :: Δ)`).
- `hproofR : ∀ {Δ x y Q}, PEqT E n Δ x y → HasTyT E n Δ x Q →
    Σ' P, HasTyT E n Δ P (.sort .zero) ×' HasTyT E n Δ y P` —
  proof-hood propagates LEFT→RIGHT across `≈P` (used when the LEFT
  derivation is a proof leaf and the right is structural).
- `hproofL : ∀ {Δ x y Q}, PEqT E n Δ x y → HasTyT E n Δ y Q →
    Σ' P, HasTyT E n Δ P (.sort .zero) ×' HasTyT E n Δ x P` —
  proof-hood propagates RIGHT→LEFT (used when the RIGHT derivation is
  a proof leaf and the left is structural).

  These signatures do not require Q : sort 0. A reflexive sort input
  therefore already refutes them. Even with that premise added, raw
  app congruence can produce an untypable endpoint from a proof input;
  see the stronger guarded-front refutations in `RcicPEqTProofFront`.

`PEqT.trans_ps` / `PEqT.trans_sp` are the standalone `trans_pp`
generalizations (proof leaf × arbitrary `≈P`, in each direction);
`trans_ps` consumes `hproofR`, `trans_sp` consumes `hproofL` — no
`CtxConvT` needed.

`eqN`/`eqNList` symm/trans are mirrored privately (the public lemmas
live in `RcicParRedCore`, outside this kit's dependency cone — the
`RcicPEqT.lean` `peqT_eqN_refl` precedent).
-/

namespace Rcic.Declarative

/-! ## (0) private `eqN`/`eqNList` symm/trans mirrors -/

private theorem peqT_eqN_symm {a b : Level} (h : eqN a b) : eqN b a :=
  fun ρ => (h ρ).symm

private theorem peqT_eqN_trans {a b c : Level} (h₁ : eqN a b) (h₂ : eqN b c) :
    eqN a c :=
  fun ρ => (h₁ ρ).trans (h₂ ρ)

/-- `eqNList` is `False` at mismatched lengths — the two asymmetric arms
    eliminate it. -/
private theorem peqT_eqNList_symm :
    {ls ls' : List Level} → eqNList ls ls' → eqNList ls' ls
  | [], [], _ => True.intro
  | _ :: _, _ :: _, h => ⟨peqT_eqN_symm h.1, peqT_eqNList_symm h.2⟩
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

/-- `eqNList` is `False` at mismatched lengths — the four asymmetric
    arms eliminate whichever hypothesis exposes the mismatch. -/
private theorem peqT_eqNList_trans :
    {l₁ l₂ l₃ : List Level} → eqNList l₁ l₂ → eqNList l₂ l₃ →
    eqNList l₁ l₃
  | [], [], [], _, _ => True.intro
  | _ :: _, _ :: _, _ :: _, h₁, h₂ =>
      ⟨peqT_eqN_trans h₁.1 h₂.1, peqT_eqNList_trans h₁.2 h₂.2⟩
  | [], _ :: _, _, h₁, _ => False.elim h₁
  | _, _ :: _, [], _, h₂ => False.elim h₂
  | _ :: _, [], _, h₁, _ => False.elim h₁
  | _, [], _ :: _, _, h₂ => False.elim h₂

/-! ## (1) conditional symmetry -/

/-- `≈P` is symmetric, CONDITIONAL on context transport for the binder
    cases. `hdom` is consumed at `lam`/`pi` (assumption-decl extension,
    LEFT→RIGHT), `hlet` at `letE` (letBinding-decl extension,
    LEFT→RIGHT); both discharge to `CtxConvT`'s raw `HasTyT`/`ConvT`
    fields, i.e. endpoint-domain sort equality (F-ι★-11) plus, for
    `letE`, value conversion `ConvT v v' A`. The `proof` leaf swaps for
    free. -/
def PEqT.symm (hcl : EnvClosed E)
    (hdom : ∀ {Δ : LCtx} {A A' : Expr Nat}, PEqT E n Δ A A' →
      CtxConvT E n (.assumption A :: Δ) (.assumption A' :: Δ))
    (hlet : ∀ {Δ : LCtx} {A A' v v' : Expr Nat},
      PEqT E n Δ A A' → PEqT E n Δ v v' →
      CtxConvT E n (.letBinding A v :: Δ) (.letBinding A' v' :: Δ)) :
    {Γ : LCtx} → {a b : Expr Nat} → PEqT E n Γ a b → PEqT E n Γ b a
  | _, _, _, .bvar _ i => PEqT.bvar _ i
  | _, _, _, .sort _ _ _ h => PEqT.sort _ _ _ (peqT_eqN_symm h)
  | _, _, _, .const _ _ _ _ h => PEqT.const _ _ _ _ (peqT_eqNList_symm h)
  | _, _, _, .lit _ t => PEqT.lit _ t
  | _, _, _, .app _ _ _ _ _ hf ha =>
      PEqT.app _ _ _ _ _ (PEqT.symm hcl hdom hlet hf)
        (PEqT.symm hcl hdom hlet ha)
  | _, _, _, .lam _ _ _ _ _ hA hb =>
      PEqT.lam _ _ _ _ _ (PEqT.symm hcl hdom hlet hA)
        (PEqT.ctx_conv hcl (hdom hA) (PEqT.symm hcl hdom hlet hb))
  | _, _, _, .pi _ _ _ _ _ hA hB =>
      PEqT.pi _ _ _ _ _ (PEqT.symm hcl hdom hlet hA)
        (PEqT.ctx_conv hcl (hdom hA) (PEqT.symm hcl hdom hlet hB))
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb =>
      PEqT.letE _ _ _ _ _ _ _ (PEqT.symm hcl hdom hlet hA)
        (PEqT.symm hcl hdom hlet hv)
        (PEqT.ctx_conv hcl (hlet hA hv) (PEqT.symm hcl hdom hlet hb))
  | _, _, _, .proof _ _ _ _ _ hP hQ hp hq =>
      PEqT.proof _ _ _ _ _ hQ hP hq hp

/-! ## (2) `trans_pp` generalizations — the mixed leaf×structural steps -/

/-- `trans_pp` generalized right: a proof leaf on the left, an arbitrary
    `≈P` on the right. Conditional on `hproofR` (proof-respects
    LEFT→RIGHT): the right endpoint's proof-hood isn't readable off
    `≈P`. -/
def PEqT.trans_ps {Γ : LCtx} {p q r P Q : Expr Nat}
    (hproofR : ∀ {Δ : LCtx} {x y Q₀ : Expr Nat}, PEqT E n Δ x y →
      HasTyT E n Δ x Q₀ →
      Σ' P', HasTyT E n Δ P' (.sort .zero) ×' HasTyT E n Δ y P')
    (hP : HasTyT E n Γ P (.sort .zero)) (hp : HasTyT E n Γ p P)
    (hq : HasTyT E n Γ q Q) (h₂ : PEqT E n Γ q r) :
    PEqT E n Γ p r :=
  let ⟨_, hR, hr⟩ := hproofR h₂ hq
  PEqT.proof _ _ _ _ _ hP hR hp hr

/-- `trans_pp` generalized left: an arbitrary `≈P` on the left, a proof
    leaf on the right. Conditional on `hproofL` (proof-respects
    RIGHT→LEFT), applied to the left derivation and the leaf's `q`
    typing. -/
def PEqT.trans_sp {Γ : LCtx} {p q r Q R : Expr Nat}
    (hproofL : ∀ {Δ : LCtx} {x y Q₀ : Expr Nat}, PEqT E n Δ x y →
      HasTyT E n Δ y Q₀ →
      Σ' P', HasTyT E n Δ P' (.sort .zero) ×' HasTyT E n Δ x P')
    (h₁ : PEqT E n Γ p q) (hq : HasTyT E n Γ q Q)
    (hR : HasTyT E n Γ R (.sort .zero)) (hr : HasTyT E n Γ r R) :
    PEqT E n Γ p r :=
  let ⟨_, hP, hp⟩ := hproofL h₁ hq
  PEqT.proof _ _ _ _ _ hP hR hp hr

/-! ## (3) conditional transitivity -/

/-- `≈P` is transitive, CONDITIONAL on reversed-direction context
    transport for the binder cases plus proof-respects in both
    directions for the mixed leaf×structural cases. `hdom`/`hlet` run
    RIGHT→LEFT: the second derivation's body is read at the middle
    endpoint's declaration, so it transports back into the first
    declaration's context (the result's binder extends by the LEFT
    endpoint's declaration). `hproofR` discharges the right structural
    endpoint's proof-hood (`trans_ps` step), `hproofL` the left's
    (`trans_sp` step) — typing-respects at `sort 0`. Leaf×leaf is
    `trans_pp` and is unconditional. -/
def PEqT.trans (hcl : EnvClosed E)
    (hdom : ∀ {Δ : LCtx} {A A' : Expr Nat}, PEqT E n Δ A A' →
      CtxConvT E n (.assumption A' :: Δ) (.assumption A :: Δ))
    (hlet : ∀ {Δ : LCtx} {A A' v v' : Expr Nat},
      PEqT E n Δ A A' → PEqT E n Δ v v' →
      CtxConvT E n (.letBinding A' v' :: Δ) (.letBinding A v :: Δ))
    (hproofL : ∀ {Δ : LCtx} {x y Q : Expr Nat}, PEqT E n Δ x y →
      HasTyT E n Δ y Q →
      Σ' P, HasTyT E n Δ P (.sort .zero) ×' HasTyT E n Δ x P)
    (hproofR : ∀ {Δ : LCtx} {x y Q : Expr Nat}, PEqT E n Δ x y →
      HasTyT E n Δ x Q →
      Σ' P, HasTyT E n Δ P (.sort .zero) ×' HasTyT E n Δ y P) :
    {Γ : LCtx} → {a b c : Expr Nat} →
    PEqT E n Γ a b → PEqT E n Γ b c → PEqT E n Γ a c
  | _, _, _, _, .proof _ _ _ _ _ hP hQ hp hq,
      .proof _ _ _ _ _ hQ' hR hq' hr =>
      PEqT.trans_pp hP hQ hQ' hR hp hq hq' hr
  | _, _, _, _, .proof _ _ _ _ _ hP _ hp hq, h₂ =>
      PEqT.trans_ps hproofR hP hp hq h₂
  | _, _, _, _, h₁, .proof _ _ _ _ _ _ hR hq hr =>
      PEqT.trans_sp hproofL h₁ hq hR hr
  | _, _, _, _, .bvar _ i, .bvar _ _ => PEqT.bvar _ i
  | _, _, _, _, .sort _ _ _ h₁, .sort _ _ _ h₂ =>
      .sort _ _ _ (peqT_eqN_trans h₁ h₂)
  | _, _, _, _, .const _ _ _ _ h₁, .const _ _ _ _ h₂ =>
      .const _ _ _ _ (peqT_eqNList_trans h₁ h₂)
  | _, _, _, _, .lit _ t, .lit _ _ => PEqT.lit _ t
  | _, _, _, _, .app _ _ _ _ _ hf ha, .app _ _ _ _ _ hf' ha' =>
      PEqT.app _ _ _ _ _ (PEqT.trans hcl hdom hlet hproofL hproofR hf hf')
        (PEqT.trans hcl hdom hlet hproofL hproofR ha ha')
  | _, _, _, _, .lam _ _ _ _ _ hA₁ hb₁, .lam _ _ _ _ _ hA₂ hb₂ =>
      PEqT.lam _ _ _ _ _ (PEqT.trans hcl hdom hlet hproofL hproofR hA₁ hA₂)
        (PEqT.trans hcl hdom hlet hproofL hproofR hb₁
          (PEqT.ctx_conv hcl (hdom hA₁) hb₂))
  | _, _, _, _, .pi _ _ _ _ _ hA₁ hB₁, .pi _ _ _ _ _ hA₂ hB₂ =>
      PEqT.pi _ _ _ _ _ (PEqT.trans hcl hdom hlet hproofL hproofR hA₁ hA₂)
        (PEqT.trans hcl hdom hlet hproofL hproofR hB₁
          (PEqT.ctx_conv hcl (hdom hA₁) hB₂))
  | _, _, _, _, .letE _ _ _ _ _ _ _ hA₁ hv₁ hb₁,
      .letE _ _ _ _ _ _ _ hA₂ hv₂ hb₂ =>
      PEqT.letE _ _ _ _ _ _ _ (PEqT.trans hcl hdom hlet hproofL hproofR hA₁ hA₂)
        (PEqT.trans hcl hdom hlet hproofL hproofR hv₁ hv₂)
        (PEqT.trans hcl hdom hlet hproofL hproofR hb₁
          (PEqT.ctx_conv hcl (hlet hA₁ hv₁) hb₂))

/-! ## (4) pins -/

/-- consumption pin: `symm` at `lam` — the body derivation moves from
    the left declaration's context to the right's via `hdom`
    (LEFT→RIGHT `CtxConvT`, the sort-equality surface). -/
def pin_PEqT_symm_lam (hcl : EnvClosed E)
    (hdom : ∀ {Δ : LCtx} {A A' : Expr Nat}, PEqT E n Δ A A' →
      CtxConvT E n (.assumption A :: Δ) (.assumption A' :: Δ))
    (hlet : ∀ {Δ : LCtx} {A A' v v' : Expr Nat},
      PEqT E n Δ A A' → PEqT E n Δ v v' →
      CtxConvT E n (.letBinding A v :: Δ) (.letBinding A' v' :: Δ))
    {Γ : LCtx} {A A' b b' : Expr Nat}
    (hA : PEqT E n Γ A A') (hb : PEqT E n (.assumption A :: Γ) b b') :
    PEqT E n Γ (.lam A' b') (.lam A b) :=
  PEqT.symm hcl hdom hlet (.lam _ _ _ _ _ hA hb)

/-- consumption pin: `trans` at `letE` — the second body derivation is
    pulled back across `hlet` (RIGHT→LEFT `CtxConvT` on letBinding
    declarations — the F-ι★-11 sort-equality + value-conv surface). -/
def pin_PEqT_trans_letE (hcl : EnvClosed E)
    (hdom : ∀ {Δ : LCtx} {A A' : Expr Nat}, PEqT E n Δ A A' →
      CtxConvT E n (.assumption A' :: Δ) (.assumption A :: Δ))
    (hlet : ∀ {Δ : LCtx} {A A' v v' : Expr Nat},
      PEqT E n Δ A A' → PEqT E n Δ v v' →
      CtxConvT E n (.letBinding A' v' :: Δ) (.letBinding A v :: Δ))
    (hproofL : ∀ {Δ : LCtx} {x y Q : Expr Nat}, PEqT E n Δ x y →
      HasTyT E n Δ y Q →
      Σ' P, HasTyT E n Δ P (.sort .zero) ×' HasTyT E n Δ x P)
    (hproofR : ∀ {Δ : LCtx} {x y Q : Expr Nat}, PEqT E n Δ x y →
      HasTyT E n Δ x Q →
      Σ' P, HasTyT E n Δ P (.sort .zero) ×' HasTyT E n Δ y P)
    {Γ : LCtx} {A A' A'' v v' v'' b b' b'' : Expr Nat}
    (h₁ : PEqT E n Γ (.letE A v b) (.letE A' v' b'))
    (h₂ : PEqT E n Γ (.letE A' v' b') (.letE A'' v'' b'')) :
    PEqT E n Γ (.letE A v b) (.letE A'' v'' b'') :=
  PEqT.trans hcl hdom hlet hproofL hproofR h₁ h₂

/-- consumption pin: `trans_sp` — the mixed `≈P` × proof-leaf step uses
    only `hproofL` (no `CtxConvT`). -/
def pin_PEqT_trans_sp {Γ : LCtx} {p q r Q R : Expr Nat}
    (hproofL : ∀ {Δ : LCtx} {x y Q₀ : Expr Nat}, PEqT E n Δ x y →
      HasTyT E n Δ y Q₀ →
      Σ' P', HasTyT E n Δ P' (.sort .zero) ×' HasTyT E n Δ x P')
    (h₁ : PEqT E n Γ p q) (hq : HasTyT E n Γ q Q)
    (hR : HasTyT E n Γ R (.sort .zero)) (hr : HasTyT E n Γ r R) :
    PEqT E n Γ p r :=
  PEqT.trans_sp hproofL h₁ hq hR hr

#print axioms PEqT.symm
#print axioms PEqT.trans
#print axioms PEqT.trans_ps
#print axioms PEqT.trans_sp
#print axioms pin_PEqT_symm_lam
#print axioms pin_PEqT_trans_letE
#print axioms pin_PEqT_trans_sp
