import Lean
import rcic.RcicF8OM1
import rcic.RcicOriginSubstPins

/-!
B3b — total lazy inversion on provenance (O-M1a part b).

B3a (`RcicF8EvInv`) inverts `EvTy` only at `litRooted` roots: a literal
`lit` derivation, possibly under `rety`. This module extends inversion to
EVERY root, so later U/P processors never have to materialize a lazily
transported typing (S2 §2's laziness contract, cc's B3b on the #6855
stack).

For each of the eight term shapes `X` the total inversion `EvTy.invXT`
takes `(D : EvTy R Γ e T) (heq : e = <shape>)` — no `litRooted` — and
returns B3a's record at the same indices:

- `lit`/`rety` roots delegate to B3a / recurse.
- `wk d c D₀` (one inserted declaration, `e = lift c 1 e₀`): head-invert
  `lift` in `heq`, invert `D₀` recursively, wrap every typing piece in
  `EvTy.wk` and every chain in `EvTc.wk` (the #6855 amendment), casting
  with `lift_instantiate_low`/`natExpand_lift`/`lift_instantiateLevels`
  where the stored shape (`instantiate0`, `natExpand`, member types) must
  commute past the lift. `bvar` splits on the cutoff (a lifted `bvar i`
  reads `i+1` or `i` in `lookupType_insertAt_ge/lt`).
- `esub j u D₀ hget hv hvT` (`e = instantiate j (lift 0 j v) e₀`):
  - `e₀` carries the shape: invert `D₀`, wrap pieces in `EvTy.esub` and
    chains in `EvTc.subst0` (`instantiate_instantiate` for `instantiate0`,
    `natExpand_instantiate`, member-type instantiate-stability for
    `const`).
  - `e₀ = bvar j`: the target IS `lift 0 j v` — invert `hv` directly and
    append `substBvarChain`, the `EvTc.subst0` of `D₀`'s own
    bvar-inversion chain (relating `lift 0 j t` to `instantiate j w A₀`
    via the P5 cancel `instantiate_lift_cancel`).
  - `e₀ = bvar i, i ≠ j`: only `invBvarT` survives (shifted lookups via
    `lookupType_substRemove_lt/gt`); other heads contradict `heq`.

Every `invXT` is defined via a bundled private `invXT'` returning the
record AND its leaf bound in one pass; `invXT` is `.1` and
`invXT_leaves` is `.2`. `_agree` gives record equality with B3a at
literal roots (the strict clause is therefore B3a's unchanged).

`invConstT` carries `(hcl : EnvClosed E) (hinst : EnvMembersSubstStable
E)` — the same member-type closedness premises `hasTyTWeaken` /
`hasTyT_substS` read; all other shapes need none.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn
open Rcic.Declarative.F8OriginSubst.Pins

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### head-inversion lemmas for `lift`

`lift` preserves every non-`bvar` head; at `bvar` the index moves by the
cutoff, which the arms split on themselves. -/

private def liftShape_bvar {c : Nat} {e : Expr Nat} {i : Nat}
    (h : lift c 1 e = .bvar i) : Σ' i₀, e = .bvar i₀ := by
  cases e with
  | bvar i₀ => exact ⟨i₀, rfl⟩
  | sort l => simp only [lift] at h; exact nomatch h
  | const r ls => simp only [lift] at h; exact nomatch h
  | app f a => simp only [lift] at h; exact nomatch h
  | lam A b => simp only [lift] at h; exact nomatch h
  | pi A B => simp only [lift] at h; exact nomatch h
  | letE A v b => simp only [lift] at h; exact nomatch h
  | lit t => simp only [lift] at h; exact nomatch h

private def liftShape_sort {c : Nat} {e : Expr Nat} {l : Level}
    (h : lift c 1 e = .sort l) : e = .sort l := by
  cases e with
  | sort l' => simp only [lift] at h; exact h
  | bvar i₀ => simp only [lift] at h; split at h <;> exact nomatch h
  | const r ls => simp only [lift] at h; exact nomatch h
  | app f a => simp only [lift] at h; exact nomatch h
  | lam A b => simp only [lift] at h; exact nomatch h
  | pi A B => simp only [lift] at h; exact nomatch h
  | letE A v b => simp only [lift] at h; exact nomatch h
  | lit t => simp only [lift] at h; exact nomatch h

private def liftShape_const {c : Nat} {e : Expr Nat} {r : Nat}
    {ls : List Level}
    (h : lift c 1 e = .const r ls) : e = .const r ls := by
  cases e with
  | const r' ls' => simp only [lift] at h; exact h
  | sort l => simp only [lift] at h; exact nomatch h
  | bvar i₀ => simp only [lift] at h; split at h <;> exact nomatch h
  | app f a => simp only [lift] at h; exact nomatch h
  | lam A b => simp only [lift] at h; exact nomatch h
  | pi A B => simp only [lift] at h; exact nomatch h
  | letE A v b => simp only [lift] at h; exact nomatch h
  | lit t => simp only [lift] at h; exact nomatch h

private def liftShape_app {c : Nat} {e f a : Expr Nat}
    (h : lift c 1 e = .app f a) :
    Σ' f₀ a₀ : Expr Nat, e = .app f₀ a₀ ∧ lift c 1 f₀ = f
      ∧ lift c 1 a₀ = a := by
  cases e with
  | app f₀ a₀ =>
      simp only [lift] at h; injection h with hf ha
      exact ⟨f₀, a₀, rfl, hf, ha⟩
  | sort l => simp only [lift] at h; exact nomatch h
  | const r ls => simp only [lift] at h; exact nomatch h
  | bvar i₀ => simp only [lift] at h; split at h <;> exact nomatch h
  | lam A b => simp only [lift] at h; exact nomatch h
  | pi A B => simp only [lift] at h; exact nomatch h
  | letE A v b => simp only [lift] at h; exact nomatch h
  | lit t => simp only [lift] at h; exact nomatch h

private def liftShape_lam {c : Nat} {e A b : Expr Nat}
    (h : lift c 1 e = .lam A b) :
    Σ' A₀ b₀ : Expr Nat, e = .lam A₀ b₀ ∧ lift c 1 A₀ = A
      ∧ lift (c + 1) 1 b₀ = b := by
  cases e with
  | lam A₀ b₀ =>
      simp only [lift] at h; injection h with hA hb
      exact ⟨A₀, b₀, rfl, hA, hb⟩
  | sort l => simp only [lift] at h; exact nomatch h
  | const r ls => simp only [lift] at h; exact nomatch h
  | app f a => simp only [lift] at h; exact nomatch h
  | bvar i₀ => simp only [lift] at h; split at h <;> exact nomatch h
  | pi A B => simp only [lift] at h; exact nomatch h
  | letE A v b => simp only [lift] at h; exact nomatch h
  | lit t => simp only [lift] at h; exact nomatch h

private def liftShape_pi {c : Nat} {e A B : Expr Nat}
    (h : lift c 1 e = .pi A B) :
    Σ' A₀ B₀ : Expr Nat, e = .pi A₀ B₀ ∧ lift c 1 A₀ = A
      ∧ lift (c + 1) 1 B₀ = B := by
  cases e with
  | pi A₀ B₀ =>
      simp only [lift] at h; injection h with hA hB
      exact ⟨A₀, B₀, rfl, hA, hB⟩
  | sort l => simp only [lift] at h; exact nomatch h
  | const r ls => simp only [lift] at h; exact nomatch h
  | app f a => simp only [lift] at h; exact nomatch h
  | lam A b => simp only [lift] at h; exact nomatch h
  | bvar i₀ => simp only [lift] at h; split at h <;> exact nomatch h
  | letE A v b => simp only [lift] at h; exact nomatch h
  | lit t => simp only [lift] at h; exact nomatch h

private def liftShape_letE {c : Nat} {e A v b : Expr Nat}
    (h : lift c 1 e = .letE A v b) :
    Σ' A₀ v₀ b₀ : Expr Nat, e = .letE A₀ v₀ b₀ ∧ lift c 1 A₀ = A
      ∧ lift c 1 v₀ = v ∧ lift (c + 1) 1 b₀ = b := by
  cases e with
  | letE A₀ v₀ b₀ =>
      simp only [lift] at h; injection h with hA hv hb
      exact ⟨A₀, v₀, b₀, rfl, hA, hv, hb⟩
  | sort l => simp only [lift] at h; exact nomatch h
  | const r ls => simp only [lift] at h; exact nomatch h
  | app f a => simp only [lift] at h; exact nomatch h
  | lam A' b' => simp only [lift] at h; exact nomatch h
  | pi A' B' => simp only [lift] at h; exact nomatch h
  | bvar i₀ => simp only [lift] at h; split at h <;> exact nomatch h
  | lit t => simp only [lift] at h; exact nomatch h

private def liftShape_lit {c : Nat} {e : Expr Nat} {t : Nat}
    (h : lift c 1 e = .lit t) : e = .lit t := by
  cases e with
  | lit t' => simp only [lift] at h; exact h
  | sort l => simp only [lift] at h; exact nomatch h
  | const r ls => simp only [lift] at h; exact nomatch h
  | app f a => simp only [lift] at h; exact nomatch h
  | lam A b => simp only [lift] at h; exact nomatch h
  | pi A B => simp only [lift] at h; exact nomatch h
  | letE A v b => simp only [lift] at h; exact nomatch h
  | bvar i₀ => simp only [lift] at h; split at h <;> exact nomatch h

/-! ### head-inversion lemmas for `instantiate`

`instantiate j w` preserves non-`bvar` heads; at the substituted variable
`bvar j` the result is `w` itself (the `PSum.inr` branch — inversion then
reads `hv`); at other `bvar`s it stays a `bvar`, contradicting non-`bvar`
targets. -/

private def instShape_bvar {j : Nat} {w e : Expr Nat} {i : Nat}
    (h : instantiate j w e = .bvar i) : Σ' i₀, e = .bvar i₀ := by
  cases e with
  | bvar i₀ => exact ⟨i₀, rfl⟩
  | sort l => simp only [instantiate] at h; exact nomatch h
  | const r ls => simp only [instantiate] at h; exact nomatch h
  | app f a => simp only [instantiate] at h; exact nomatch h
  | lam A b => simp only [instantiate] at h; exact nomatch h
  | pi A B => simp only [instantiate] at h; exact nomatch h
  | letE A v b => simp only [instantiate] at h; exact nomatch h
  | lit t => simp only [instantiate] at h; exact nomatch h

private def instShape_sort {j : Nat} {w e : Expr Nat} {l : Level}
    (h : instantiate j w e = .sort l) :
    PSum (e = .sort l) (e = .bvar j ∧ w = .sort l) := by
  cases e with
  | sort l' => simp only [instantiate] at h; exact .inl h
  | bvar i₀ =>
      simp only [instantiate] at h
      split at h
      · rename_i hij; subst hij; exact .inr ⟨rfl, h⟩
      · rename_i hij; split at h <;> exact nomatch h
  | const r ls => simp only [instantiate] at h; exact nomatch h
  | app f a => simp only [instantiate] at h; exact nomatch h
  | lam A b => simp only [instantiate] at h; exact nomatch h
  | pi A B => simp only [instantiate] at h; exact nomatch h
  | letE A v b => simp only [instantiate] at h; exact nomatch h
  | lit t => simp only [instantiate] at h; exact nomatch h

private def instShape_const {j : Nat} {w e : Expr Nat} {r : Nat}
    {ls : List Level}
    (h : instantiate j w e = .const r ls) :
    PSum (e = .const r ls) (e = .bvar j ∧ w = .const r ls) := by
  cases e with
  | const r' ls' => simp only [instantiate] at h; exact .inl h
  | sort l => simp only [instantiate] at h; exact nomatch h
  | bvar i₀ =>
      simp only [instantiate] at h
      split at h
      · rename_i hij; subst hij; exact .inr ⟨rfl, h⟩
      · rename_i hij; split at h <;> exact nomatch h
  | app f a => simp only [instantiate] at h; exact nomatch h
  | lam A b => simp only [instantiate] at h; exact nomatch h
  | pi A B => simp only [instantiate] at h; exact nomatch h
  | letE A v b => simp only [instantiate] at h; exact nomatch h
  | lit t => simp only [instantiate] at h; exact nomatch h

private def instShape_app {j : Nat} {w e f a : Expr Nat}
    (h : instantiate j w e = .app f a) :
    PSum (Σ' f₀ a₀ : Expr Nat, e = .app f₀ a₀
        ∧ instantiate j w f₀ = f ∧ instantiate j w a₀ = a)
      (e = .bvar j ∧ w = .app f a) := by
  cases e with
  | app f₀ a₀ =>
      simp only [instantiate] at h; injection h with hf ha
      exact .inl ⟨f₀, a₀, rfl, hf, ha⟩
  | sort l => simp only [instantiate] at h; exact nomatch h
  | const r ls => simp only [instantiate] at h; exact nomatch h
  | bvar i₀ =>
      simp only [instantiate] at h
      split at h
      · rename_i hij; subst hij; exact .inr ⟨rfl, h⟩
      · rename_i hij; split at h <;> exact nomatch h
  | lam A b => simp only [instantiate] at h; exact nomatch h
  | pi A B => simp only [instantiate] at h; exact nomatch h
  | letE A v b => simp only [instantiate] at h; exact nomatch h
  | lit t => simp only [instantiate] at h; exact nomatch h

private def instShape_lam {j : Nat} {w e A b : Expr Nat}
    (h : instantiate j w e = .lam A b) :
    PSum (Σ' A₀ b₀ : Expr Nat, e = .lam A₀ b₀ ∧ instantiate j w A₀ = A
        ∧ instantiate (j + 1) (lift 0 1 w) b₀ = b)
      (e = .bvar j ∧ w = .lam A b) := by
  cases e with
  | lam A₀ b₀ =>
      simp only [instantiate] at h; injection h with hA hb
      exact .inl ⟨A₀, b₀, rfl, hA, hb⟩
  | sort l => simp only [instantiate] at h; exact nomatch h
  | const r ls => simp only [instantiate] at h; exact nomatch h
  | app f a => simp only [instantiate] at h; exact nomatch h
  | bvar i₀ =>
      simp only [instantiate] at h
      split at h
      · rename_i hij; subst hij; exact .inr ⟨rfl, h⟩
      · rename_i hij; split at h <;> exact nomatch h
  | pi A B => simp only [instantiate] at h; exact nomatch h
  | letE A v b => simp only [instantiate] at h; exact nomatch h
  | lit t => simp only [instantiate] at h; exact nomatch h

def instShape_pi {j : Nat} {w e A B : Expr Nat}
    (h : instantiate j w e = .pi A B) :
    PSum (Σ' A₀ B₀ : Expr Nat, e = .pi A₀ B₀ ∧ instantiate j w A₀ = A
        ∧ instantiate (j + 1) (lift 0 1 w) B₀ = B)
      (e = .bvar j ∧ w = .pi A B) := by
  cases e with
  | pi A₀ B₀ =>
      simp only [instantiate] at h; injection h with hA hB
      exact .inl ⟨A₀, B₀, rfl, hA, hB⟩
  | sort l => simp only [instantiate] at h; exact nomatch h
  | const r ls => simp only [instantiate] at h; exact nomatch h
  | app f a => simp only [instantiate] at h; exact nomatch h
  | lam A' b => simp only [instantiate] at h; exact nomatch h
  | bvar i₀ =>
      simp only [instantiate] at h
      split at h
      · rename_i hij; subst hij; exact .inr ⟨rfl, h⟩
      · rename_i hij; split at h <;> exact nomatch h
  | letE A' v b => simp only [instantiate] at h; exact nomatch h
  | lit t => simp only [instantiate] at h; exact nomatch h

private def instShape_letE {j : Nat} {w e A v b : Expr Nat}
    (h : instantiate j w e = .letE A v b) :
    PSum (Σ' A₀ v₀ b₀ : Expr Nat, e = .letE A₀ v₀ b₀
        ∧ instantiate j w A₀ = A ∧ instantiate j w v₀ = v
        ∧ instantiate (j + 1) (lift 0 1 w) b₀ = b)
      (e = .bvar j ∧ w = .letE A v b) := by
  cases e with
  | letE A₀ v₀ b₀ =>
      simp only [instantiate] at h; injection h with hA hv hb
      exact .inl ⟨A₀, v₀, b₀, rfl, hA, hv, hb⟩
  | sort l => simp only [instantiate] at h; exact nomatch h
  | const r ls => simp only [instantiate] at h; exact nomatch h
  | app f a => simp only [instantiate] at h; exact nomatch h
  | lam A' b' => simp only [instantiate] at h; exact nomatch h
  | pi A' B' => simp only [instantiate] at h; exact nomatch h
  | bvar i₀ =>
      simp only [instantiate] at h
      split at h
      · rename_i hij; subst hij; exact .inr ⟨rfl, h⟩
      · rename_i hij; split at h <;> exact nomatch h
  | lit t => simp only [instantiate] at h; exact nomatch h

private def instShape_lit {j : Nat} {w e : Expr Nat} {t : Nat}
    (h : instantiate j w e = .lit t) :
    PSum (e = .lit t) (e = .bvar j ∧ w = .lit t) := by
  cases e with
  | lit t' => simp only [instantiate] at h; exact .inl h
  | sort l => simp only [instantiate] at h; exact nomatch h
  | const r ls => simp only [instantiate] at h; exact nomatch h
  | app f a => simp only [instantiate] at h; exact nomatch h
  | lam A b => simp only [instantiate] at h; exact nomatch h
  | pi A B => simp only [instantiate] at h; exact nomatch h
  | letE A v b => simp only [instantiate] at h; exact nomatch h
  | bvar i₀ =>
      simp only [instantiate] at h
      split at h
      · rename_i hij; subst hij; exact .inr ⟨rfl, h⟩
      · rename_i hij; split at h <;> exact nomatch h

/-! ### transport helpers -/

/-- the residual `subst0` chain used when the substituted variable was the
    inverted term: `lift 0 j t` (the stored type, transported) reduces by
    the P5 cancel to `instantiate j (lift 0 j v) (lift 0 (j+1) t)`, which
    `D₀`'s bvar-inversion chain `r₀.hc : Γ₀ ⊢ r₀.A → A₀` substitutes. -/
private def substBvarChain {Γ₀ : LCtx} {j : Nat} {A₀ t v : Expr Nat}
    (r₀ : EvInvBvar R Γ₀ j A₀) (hget : Γ₀[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t)) :
    EvTc R (substRemove v j Γ₀) (lift 0 j t)
      (instantiate j (lift 0 j v) A₀) :=
  EvTc.cast rfl
    (show instantiate j (lift 0 j v) r₀.A = lift 0 j t from by
      rw [show r₀.A = lift 0 (j + 1) t from
        Option.some.inj (r₀.hlk.symm.trans (lookupType_get_assumption hget))]
      exact instantiate_lift_cancel (j + 1) 0 j (lift 0 j v)
        (Nat.zero_le j) (by omega) t)
    rfl (EvTc.subst0 j r₀.hc hget hv)

private theorem substBvarChain_leaves {Γ₀ : LCtx} {j : Nat}
    {A₀ t v : Expr Nat}
    (r₀ : EvInvBvar R Γ₀ j A₀) (hget : Γ₀[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t)) :
    (substBvarChain r₀ hget hv).leaves = r₀.hc.leaves ++ hv.leaves := by
  simp only [substBvarChain, EvTc.cast_leaves, EvTc.leaves]

/-- the let twin of `substBvarChain` (`lookupType_get_letBinding`). -/
private def substBvarChainLet {Γ₀ : LCtx} {j : Nat} {A₀ t w : Expr Nat}
    (r₀ : EvInvBvar R Γ₀ j A₀) (hget : Γ₀[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ₀) (lift 0 j w) (lift 0 j t)) :
    EvTc R (substRemove w j Γ₀) (lift 0 j t)
      (instantiate j (lift 0 j w) A₀) :=
  EvTc.cast rfl
    (show instantiate j (lift 0 j w) r₀.A = lift 0 j t from by
      rw [show r₀.A = lift 0 (j + 1) t from
        Option.some.inj (r₀.hlk.symm.trans (lookupType_get_letBinding hget))]
      exact instantiate_lift_cancel (j + 1) 0 j (lift 0 j w)
        (Nat.zero_le j) (by omega) t)
    rfl (EvTc.substLet j r₀.hc hget hv)

private theorem substBvarChainLet_leaves {Γ₀ : LCtx} {j : Nat}
    {A₀ t w : Expr Nat}
    (r₀ : EvInvBvar R Γ₀ j A₀) (hget : Γ₀[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ₀) (lift 0 j w) (lift 0 j t)) :
    (substBvarChainLet r₀ hget hv).leaves = r₀.hc.leaves ++ hv.leaves := by
  simp only [substBvarChainLet, EvTc.cast_leaves, EvTc.leaves]

/-- the esub replacement's typing one binder deeper: `wk` inserts the
    substituted declaration head (`instDecl j v d`) at position 0 of the
    removed context, and `lift_lift_merge` folds
    `lift 0 1 (lift 0 j x) = lift 0 (j+1) x`. -/
private def esubBinderArg {Γ₀ : LCtx} {j : Nat} {d : LocalDecl}
    {v x y : Expr Nat}
    (h : EvTy R (substRemove v j Γ₀) (lift 0 j x) (lift 0 j y)) :
    EvTy R (substRemove v (j + 1) (d :: Γ₀)) (lift 0 (j + 1) x)
      (lift 0 (j + 1) y) :=
  EvTy.cast rfl
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) x)
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) y)
    (EvTy.wk (instDecl j v d) 0 h)

/-- the same transport ending at a sort (for `hvT`). -/
private def esubBinderSort {Γ₀ : LCtx} {j : Nat} {d : LocalDecl}
    {v x : Expr Nat} {u : Level}
    (h : EvTy R (substRemove v j Γ₀) (lift 0 j x) (.sort u)) :
    EvTy R (substRemove v (j + 1) (d :: Γ₀)) (lift 0 (j + 1) x) (.sort u) :=
  EvTy.cast rfl
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) x)
    rfl
    (EvTy.wk (instDecl j v d) 0 h)

/-- `EvTy.esub` at `j+1` produces the replacement `lift 0 (j+1) v`, while
    `instantiate`'s binder arm writes `lift 0 1 (lift 0 j v)` — P2 merge
    identifies them. -/
private def esubFieldCast {Γ : LCtx} {j : Nat} {v e A : Expr Nat}
    (D : EvTy R Γ (instantiate (j + 1) (lift 0 (j + 1) v) e)
      (instantiate (j + 1) (lift 0 (j + 1) v) A)) :
    EvTy R Γ (instantiate (j + 1) (lift 0 1 (lift 0 j v)) e)
      (instantiate (j + 1) (lift 0 1 (lift 0 j v)) A) :=
  EvTy.cast rfl
    (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
    (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v]) D

private theorem esubFieldCast_leaves {Γ : LCtx} {j : Nat} {v e A : Expr Nat}
    (D : EvTy R Γ (instantiate (j + 1) (lift 0 (j + 1) v) e)
      (instantiate (j + 1) (lift 0 (j + 1) v) A)) :
    (esubFieldCast D).leaves = D.leaves := EvTy.cast_leaves _ _ _ _

private theorem esubBinderArg_leaves {Γ₀ : LCtx} {j : Nat} {d : LocalDecl}
    {v x y : Expr Nat}
    (h : EvTy R (substRemove v j Γ₀) (lift 0 j x) (lift 0 j y)) :
    (esubBinderArg (d := d) h).leaves = h.leaves := by
  simp only [esubBinderArg, EvTy.cast_leaves, EvTy.leaves]

private theorem esubBinderSort_leaves {Γ₀ : LCtx} {j : Nat} {d : LocalDecl}
    {v x : Expr Nat} {u : Level}
    (h : EvTy R (substRemove v j Γ₀) (lift 0 j x) (.sort u)) :
    (esubBinderSort (d := d) h).leaves = h.leaves := by
  simp only [esubBinderSort, EvTy.cast_leaves, EvTy.leaves]

/-! ### `bvar` -/

/-- bundled `bvar`-inversion: record plus its leaf bound, in one pass. -/
private def EvTy.invBvarT' {i : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    e = .bvar i →
    Σ' r : EvInvBvar R Γ i T, ∀ ℓ ∈ r.leaves,
      ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, heq =>
      ⟨(EvTy.lit d hsub).invBvar rfl heq,
        fun ℓ hℓ => EvTy.invBvar_leaves (EvTy.lit d hsub) rfl heq ℓ hℓ⟩
  | _, _, _, .rety D₀ c, heq =>
      let s := D₀.invBvarT' heq
      ⟨⟨s.1.A, s.1.hlk, .trans s.1.hc c⟩, fun ℓ hℓ => by
        simp only [EvInvBvar.leaves, EvTc.leaves, List.mem_append] at hℓ
        rcases hℓ with hm | hm
        · exact (s.2 ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
            ⟨ℓ', List.mem_append.mpr (.inl h'), hs⟩
        · exact ⟨ℓ, List.mem_append.mpr (.inr hm), .inl rfl⟩⟩
  | _, _, _, .var i₀ A hlk, heq => by
      injection heq with hi
      subst hi
      exact ⟨⟨A, hlk, .refl _ _⟩, fun ℓ hℓ => by
        simp only [EvInvBvar.leaves, EvTc.leaves] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, _, .sort _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .wk d c D₀, heq => by
      obtain ⟨i₀, h₁⟩ := liftShape_bvar heq
      obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁
      rw [h₁] at heq
      simp only [lift] at heq
      split at heq
      · rename_i hic
        injection heq with hi; subst hi
        refine ⟨⟨lift c 1 r₀.A, lookupType_insertAt_ge d hic r₀.hlk,
          EvTc.wk d c r₀.hc⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvBvar.leaves, EvTc.leaves] at hℓ
        exact (h₀ ℓ hℓ).elim fun ℓ' ⟨h', hs⟩ => ⟨ℓ', h', hs⟩
      · rename_i hic
        injection heq with hi; subst hi
        refine ⟨⟨lift c 1 r₀.A,
          lookupType_insertAt_lt d (Nat.lt_of_not_le hic) r₀.hlk,
          EvTc.wk d c r₀.hc⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvBvar.leaves, EvTc.leaves] at hℓ
        exact (h₀ ℓ hℓ).elim fun ℓ' ⟨h', hs⟩ => ⟨ℓ', h', hs⟩
  | _, _, _, .esub j u D₀ hget hv hvT, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain ⟨i₀, h₁⟩ := instShape_bvar heq
      rw [h₁] at heq
      simp only [instantiate] at heq
      split at heq
      · rename_i hij
        have h₁j : e₀ = .bvar j := h₁.trans (congrArg Expr.bvar hij)
        obtain ⟨rhv, hvh⟩ := hv.invBvarT' heq
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.A, rhv.hlk,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvBvar.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append] at hℓ
        rcases hℓ with hm | hm | hm
        · exact (hvh ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
            ⟨ℓ', List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr h'))), hs⟩
        · exact (h₀ ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
            ⟨ℓ', List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inl h'))), hs⟩
        · exact ⟨ℓ, List.mem_append.mpr (.inl
            (List.mem_append.mpr (.inr hm))), .inl rfl⟩
      · rename_i hij
        split at heq
        · rename_i hlt
          injection heq with hi; subst hi
          obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁
          refine ⟨⟨instantiate j (lift 0 j v) r₀.A,
            lookupType_substRemove_gt hlt r₀.hlk,
            EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
          intro ℓ hℓ
          simp only [EvInvBvar.leaves, EvTc.leaves, List.mem_append] at hℓ
          rcases hℓ with hm | hm
          · exact (h₀ ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
              ⟨ℓ', List.mem_append.mpr (.inl
                (List.mem_append.mpr (.inl h'))), hs⟩
          · exact ⟨ℓ, List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr hm))), .inl rfl⟩
        · rename_i hlt
          injection heq with hi; subst hi
          obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁
          refine ⟨⟨instantiate j (lift 0 j v) r₀.A,
            lookupType_substRemove_lt
              (Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) hij) r₀.hlk,
            EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
          intro ℓ hℓ
          simp only [EvInvBvar.leaves, EvTc.leaves, List.mem_append] at hℓ
          rcases hℓ with hm | hm
          · exact (h₀ ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
              ⟨ℓ', List.mem_append.mpr (.inl
                (List.mem_append.mpr (.inl h'))), hs⟩
          · exact ⟨ℓ, List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr hm))), .inl rfl⟩
  | _, _, _, .subst0 j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain ⟨i₀, h₁⟩ := instShape_bvar heq
      rw [h₁] at heq
      simp only [instantiate] at heq
      split at heq
      · rename_i hij
        have h₁j : e₀ = .bvar j := h₁.trans (congrArg Expr.bvar hij)
        obtain ⟨rhv, hvh⟩ := hv.invBvarT' heq
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.A, rhv.hlk,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvBvar.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append] at hℓ
        rcases hℓ with hm | hm | hm
        · exact (hvh ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
            ⟨ℓ', List.mem_append.mpr (.inr h'), hs⟩
        · exact (h₀ ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
            ⟨ℓ', List.mem_append.mpr (.inl h'), hs⟩
        · exact ⟨ℓ, List.mem_append.mpr (.inr hm), .inl rfl⟩
      · rename_i hij
        split at heq
        · rename_i hlt
          injection heq with hi; subst hi
          obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁
          refine ⟨⟨instantiate j (lift 0 j v) r₀.A,
            lookupType_substRemove_gt hlt r₀.hlk,
            EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
          intro ℓ hℓ
          simp only [EvInvBvar.leaves, EvTc.leaves, List.mem_append] at hℓ
          rcases hℓ with hm | hm
          · exact (h₀ ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
              ⟨ℓ', List.mem_append.mpr (.inl h'), hs⟩
          · exact ⟨ℓ, List.mem_append.mpr (.inr hm), .inl rfl⟩
        · rename_i hlt
          injection heq with hi; subst hi
          obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁
          refine ⟨⟨instantiate j (lift 0 j v) r₀.A,
            lookupType_substRemove_lt
              (Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) hij) r₀.hlk,
            EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
          intro ℓ hℓ
          simp only [EvInvBvar.leaves, EvTc.leaves, List.mem_append] at hℓ
          rcases hℓ with hm | hm
          · exact (h₀ ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
              ⟨ℓ', List.mem_append.mpr (.inl h'), hs⟩
          · exact ⟨ℓ, List.mem_append.mpr (.inr hm), .inl rfl⟩
  | _, _, _, .substLet j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain ⟨i₀, h₁⟩ := instShape_bvar heq
      rw [h₁] at heq
      simp only [instantiate] at heq
      split at heq
      · rename_i hij
        have h₁j : e₀ = .bvar j := h₁.trans (congrArg Expr.bvar hij)
        obtain ⟨rhv, hvh⟩ := hv.invBvarT' heq
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.A, rhv.hlk,
          .trans rhv.hc (substBvarChainLet r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvBvar.leaves, EvTc.leaves, substBvarChainLet_leaves,
          List.mem_append] at hℓ
        rcases hℓ with hm | hm | hm
        · exact (hvh ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
            ⟨ℓ', List.mem_append.mpr (.inr h'), hs⟩
        · exact (h₀ ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
            ⟨ℓ', List.mem_append.mpr (.inl h'), hs⟩
        · exact ⟨ℓ, List.mem_append.mpr (.inr hm), .inl rfl⟩
      · rename_i hij
        split at heq
        · rename_i hlt
          injection heq with hi; subst hi
          obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁
          refine ⟨⟨instantiate j (lift 0 j v) r₀.A,
            lookupType_substRemove_gt hlt r₀.hlk,
            EvTc.substLet j r₀.hc hget hv⟩, ?_⟩
          intro ℓ hℓ
          simp only [EvInvBvar.leaves, EvTc.leaves, List.mem_append] at hℓ
          rcases hℓ with hm | hm
          · exact (h₀ ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
              ⟨ℓ', List.mem_append.mpr (.inl h'), hs⟩
          · exact ⟨ℓ, List.mem_append.mpr (.inr hm), .inl rfl⟩
        · rename_i hlt
          injection heq with hi; subst hi
          obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁
          refine ⟨⟨instantiate j (lift 0 j v) r₀.A,
            lookupType_substRemove_lt
              (Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) hij) r₀.hlk,
            EvTc.substLet j r₀.hc hget hv⟩, ?_⟩
          intro ℓ hℓ
          simp only [EvInvBvar.leaves, EvTc.leaves, List.mem_append] at hℓ
          rcases hℓ with hm | hm
          · exact (h₀ ℓ hm).elim fun ℓ' ⟨h', hs⟩ =>
              ⟨ℓ', List.mem_append.mpr (.inl h'), hs⟩
          · exact ⟨ℓ, List.mem_append.mpr (.inr hm), .inl rfl⟩
  termination_by _ _ _ D _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- `bvar`-inversion on provenance — total over all roots. -/
def EvTy.invBvarT {i : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .bvar i) : EvInvBvar R Γ i T :=
  (D.invBvarT' heq).1

/-- every leaf of a `bvar`-inversion sits at-or-below an input leaf. -/
theorem EvTy.invBvarT_leaves {i : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .bvar i) :
    ∀ ℓ ∈ (D.invBvarT heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ' :=
  (D.invBvarT' heq).2

/-- `invBvarT` agrees with B3a's `invBvar` at lit-rooted inputs (record
    equality — the strict clause is thereby B3a's own). -/
theorem EvTy.invBvarT_agree {i : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .bvar i) →
    D.invBvarT heq = D.invBvar hD heq
  | _, _, _, .lit d hsub, _, heq => by
      simp only [EvTy.invBvarT, EvTy.invBvarT', EvTy.invBvar]
  | _, _, _, .rety D₀ c, hD, heq => by
      rename_i Γ₀ e₀ T' A₀
      have ih := D₀.invBvarT_agree hD heq
      simp only [EvTy.invBvarT] at ih
      simp only [EvTy.invBvarT, EvTy.invBvarT', EvTy.invBvar]
      exact congrArg
        (fun r : EvInvBvar R Γ₀ i A₀ =>
          (⟨r.A, r.hlk, .trans r.hc c⟩ : EvInvBvar R Γ₀ i T')) ih
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-! ### append-membership sinks

`rety`/`wk`/`esub` leaves nest left (`(a ++ b) ++ c`); these shims keep the
bundled bounds readable. -/

private theorem mem2_l {α : Type} {a : α} {l r : List α} (h : a ∈ l) :
    a ∈ l ++ r := List.mem_append.mpr (.inl h)

private theorem mem2_r {α : Type} {a : α} {l r : List α} (h : a ∈ r) :
    a ∈ l ++ r := List.mem_append.mpr (.inr h)

private theorem mem3_l {α : Type} {a : α} {l₁ l₂ l₃ : List α}
    (h : a ∈ l₁) : a ∈ l₁ ++ l₂ ++ l₃ :=
  List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h)))

private theorem mem3_m {α : Type} {a : α} {l₁ l₂ l₃ : List α}
    (h : a ∈ l₂) : a ∈ l₁ ++ l₂ ++ l₃ :=
  List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))

private theorem mem3_r {α : Type} {a : α} {l₁ l₂ l₃ : List α}
    (h : a ∈ l₃) : a ∈ l₁ ++ l₂ ++ l₃ :=
  List.mem_append.mpr (.inr h)

/-- a leaf of an `esub` node's output comes from the child, the
    replacement's typing, or the replacement-type's sort typing — the
    three summands of `esub`'s own leaves. -/
private theorem esub_sink {Γ₀ : LCtx} {j : Nat} {u : Level}
    {e₀ A₀ t v : Expr Nat} {D₀ : EvTy R Γ₀ e₀ A₀}
    {hget : Γ₀[j]? = some (.assumption t)}
    {hv : EvTy R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t)}
    {hvT : EvTy R (substRemove v j Γ₀) (lift 0 j t) (.sort u)}
    {ℓ : Jd E n}
    (h : (∃ ℓ' ∈ D₀.leaves, SubEq ℓ ℓ') ∨
         (∃ ℓ' ∈ hv.leaves, SubEq ℓ ℓ') ∨
         (∃ ℓ' ∈ hvT.leaves, SubEq ℓ ℓ')) :
    ∃ ℓ' ∈ (EvTy.esub j u D₀ hget hv hvT).leaves, SubEq ℓ ℓ' := by
  rcases h with ⟨ℓ', h', hs⟩ | ⟨ℓ', h', hs⟩ | ⟨ℓ', h', hs⟩
  · exact ⟨ℓ', mem3_l h', hs⟩
  · exact ⟨ℓ', mem3_m h', hs⟩
  · exact ⟨ℓ', mem3_r h', hs⟩

/-- `subst0` sink (the `hvT`-free twin of `esub_sink`). -/
private theorem subst0_sink {Γ₀ : LCtx} {j : Nat}
    {e₀ A₀ t v : Expr Nat} {D₀ : EvTy R Γ₀ e₀ A₀}
    {hget : Γ₀[j]? = some (.assumption t)}
    {hv : EvTy R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t)}
    {ℓ : Jd E n}
    (h : (∃ ℓ' ∈ D₀.leaves, SubEq ℓ ℓ') ∨
         (∃ ℓ' ∈ hv.leaves, SubEq ℓ ℓ')) :
    ∃ ℓ' ∈ (EvTy.subst0 j D₀ hget hv).leaves, SubEq ℓ ℓ' := by
  rcases h with ⟨ℓ', h', hs⟩ | ⟨ℓ', h', hs⟩
  · exact ⟨ℓ', mem2_l h', hs⟩
  · exact ⟨ℓ', mem2_r h', hs⟩

/-- `substLet` sink (the let twin of `subst0_sink`). -/
private theorem substLet_sink {Γ₀ : LCtx} {j : Nat}
    {e₀ A₀ t w : Expr Nat} {D₀ : EvTy R Γ₀ e₀ A₀}
    {hget : Γ₀[j]? = some (.letBinding t w)}
    {hv : EvTy R (substRemove w j Γ₀) (lift 0 j w) (lift 0 j t)}
    {ℓ : Jd E n}
    (h : (∃ ℓ' ∈ D₀.leaves, SubEq ℓ ℓ') ∨
         (∃ ℓ' ∈ hv.leaves, SubEq ℓ ℓ')) :
    ∃ ℓ' ∈ (EvTy.substLet j D₀ hget hv).leaves, SubEq ℓ ℓ' := by
  rcases h with ⟨ℓ', h', hs⟩ | ⟨ℓ', h', hs⟩
  · exact ⟨ℓ', mem2_l h', hs⟩
  · exact ⟨ℓ', mem2_r h', hs⟩

/-- `rety` sink: child leaves or the retyping chain's leaves. -/
private theorem rety_sink {Γ : LCtx} {e T T' : Expr Nat}
    {D₀ : EvTy R Γ e T} {c : EvTc R Γ T T'} {ℓ : Jd E n}
    (h : (∃ ℓ' ∈ D₀.leaves, SubEq ℓ ℓ') ∨ ℓ ∈ c.leaves) :
    ∃ ℓ' ∈ (EvTy.rety D₀ c).leaves, SubEq ℓ ℓ' := by
  rcases h with ⟨ℓ', h', hs⟩ | h'
  · exact ⟨ℓ', mem2_l h', hs⟩
  · exact ⟨ℓ, mem2_r h', .inl rfl⟩

/-! ### `app` -/

private def EvTy.invAppT' {f a : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    e = .app f a →
    Σ' r : EvInvApp R Γ f a T, ∀ ℓ ∈ r.leaves,
      ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, heq =>
      ⟨(EvTy.lit d hsub).invApp rfl heq,
        fun ℓ hℓ => EvTy.invApp_leaves (EvTy.lit d hsub) rfl heq ℓ hℓ⟩
  | _, _, _, .rety D₀ c, heq =>
      let s := D₀.invAppT' heq
      ⟨⟨s.1.A, s.1.B, s.1.hf, s.1.ha, .trans s.1.hc c⟩, fun ℓ hℓ => by
        simp only [EvInvApp.leaves, EvTc.leaves, List.mem_append,
          or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm
        · exact rety_sink (.inl (s.2 ℓ (mem2_l (mem2_l hm))))
        · exact rety_sink (.inl (s.2 ℓ (mem2_l (mem2_r hm))))
        · exact rety_sink (.inl (s.2 ℓ (mem2_r hm)))
        · exact rety_sink (.inr hm)⟩
  | _, _, _, .var _ _ _, heq => nomatch heq
  | _, _, _, .sort _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .wk d c D₀, heq => by
      obtain ⟨f₀, a₀, h₁, rfl, rfl⟩ := liftShape_app heq
      obtain ⟨r₀, h₀⟩ := D₀.invAppT' h₁
      refine ⟨⟨lift c 1 r₀.A, lift (c + 1) 1 r₀.B,
        EvTy.wk d c r₀.hf, EvTy.wk d c r₀.ha,
        EvTc.cast rfl
          (lift_instantiate_low 1 c 0 a₀ (Nat.zero_le c) r₀.B) rfl
          (EvTc.wk d c r₀.hc)⟩, ?_⟩
      intro ℓ hℓ
      simp only [EvInvApp.leaves, EvTy.leaves, EvTc.leaves,
        EvTc.cast_leaves, List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm | hm
      · exact h₀ ℓ (mem2_l (mem2_l hm))
      · exact h₀ ℓ (mem2_l (mem2_r hm))
      · exact h₀ ℓ (mem2_r hm)
  | _, _, _, .esub j u D₀ hget hv hvT, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨f₀, a₀, h₁, hf, ha⟩ | ⟨h₁j, hw⟩) := instShape_app heq
      · subst hf; subst ha
        obtain ⟨r₀, h₀⟩ := D₀.invAppT' h₁
        refine ⟨⟨instantiate j (lift 0 j v) r₀.A,
          instantiate (j + 1) (lift 0 1 (lift 0 j v)) r₀.B,
          EvTy.esub j u r₀.hf hget hv hvT,
          EvTy.esub j u r₀.ha hget hv hvT,
          EvTc.cast rfl
            (instantiate_instantiate 0 j a₀ (lift 0 j v)
              (Nat.zero_le j) r₀.B)
            rfl (EvTc.subst0 j r₀.hc hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvApp.leaves, EvTy.leaves, EvTc.leaves,
          EvTc.cast_leaves, List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm | hm | hm
        · exact esub_sink (.inl (h₀ ℓ (mem2_l (mem2_l hm))))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
      · obtain ⟨rhv, hvh⟩ := hv.invAppT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.A, rhv.B, rhv.hf, rhv.ha,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvApp.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_l (mem2_l hm)))))
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_l (mem2_r hm)))))
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_r hm))))
        · exact esub_sink (.inl (h₀ ℓ hm))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
  | _, _, _, .subst0 j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨f₀, a₀, h₁, hf, ha⟩ | ⟨h₁j, hw⟩) := instShape_app heq
      · subst hf; subst ha
        obtain ⟨r₀, h₀⟩ := D₀.invAppT' h₁
        refine ⟨⟨instantiate j (lift 0 j v) r₀.A,
          instantiate (j + 1) (lift 0 1 (lift 0 j v)) r₀.B,
          EvTy.subst0 j r₀.hf hget hv,
          EvTy.subst0 j r₀.ha hget hv,
          EvTc.cast rfl
            (instantiate_instantiate 0 j a₀ (lift 0 j v)
              (Nat.zero_le j) r₀.B)
            rfl (EvTc.subst0 j r₀.hc hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvApp.leaves, EvTy.leaves, EvTc.leaves,
          EvTc.cast_leaves, List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l (mem2_l hm))))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invAppT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.A, rhv.B, rhv.hf, rhv.ha,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvApp.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact subst0_sink (.inr (hvh ℓ (mem2_l (mem2_l hm))))
        · exact subst0_sink (.inr (hvh ℓ (mem2_l (mem2_r hm))))
        · exact subst0_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact subst0_sink (.inl (h₀ ℓ hm))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  | _, _, _, .substLet j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨f₀, a₀, h₁, hf, ha⟩ | ⟨h₁j, hw⟩) := instShape_app heq
      · subst hf; subst ha
        obtain ⟨r₀, h₀⟩ := D₀.invAppT' h₁
        refine ⟨⟨instantiate j (lift 0 j v) r₀.A,
          instantiate (j + 1) (lift 0 1 (lift 0 j v)) r₀.B,
          EvTy.substLet j r₀.hf hget hv,
          EvTy.substLet j r₀.ha hget hv,
          EvTc.cast rfl
            (instantiate_instantiate 0 j a₀ (lift 0 j v)
              (Nat.zero_le j) r₀.B)
            rfl (EvTc.substLet j r₀.hc hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvApp.leaves, EvTy.leaves, EvTc.leaves,
          EvTc.cast_leaves, List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l (mem2_l hm))))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invAppT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.A, rhv.B, rhv.hf, rhv.ha,
          .trans rhv.hc (substBvarChainLet r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvApp.leaves, EvTc.leaves, substBvarChainLet_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact substLet_sink (.inr (hvh ℓ (mem2_l (mem2_l hm))))
        · exact substLet_sink (.inr (hvh ℓ (mem2_l (mem2_r hm))))
        · exact substLet_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact substLet_sink (.inl (h₀ ℓ hm))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  termination_by _ _ _ D _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- `app`-inversion on provenance — total over all roots. -/
def EvTy.invAppT {f a : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .app f a) : EvInvApp R Γ f a T :=
  (D.invAppT' heq).1

theorem EvTy.invAppT_leaves {f a : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .app f a) :
    ∀ ℓ ∈ (D.invAppT heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ' :=
  (D.invAppT' heq).2

theorem EvTy.invAppT_agree {f a : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .app f a) →
    D.invAppT heq = D.invApp hD heq
  | _, _, _, .lit d hsub, _, heq => by
      simp only [EvTy.invAppT, EvTy.invAppT', EvTy.invApp]
  | _, _, _, .rety D₀ c, hD, heq => by
      rename_i Γ₀ e₀ T' A₀
      have ih := D₀.invAppT_agree hD heq
      simp only [EvTy.invAppT] at ih
      simp only [EvTy.invAppT, EvTy.invAppT', EvTy.invApp]
      exact congrArg
        (fun r : EvInvApp R Γ₀ f a A₀ =>
          (⟨r.A, r.B, r.hf, r.ha, .trans r.hc c⟩ :
            EvInvApp R Γ₀ f a T')) ih
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD


/-! ### `lam` -/

private def EvTy.invLamT' {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    e = .lam A body →
    Σ' r : EvInvLam R Γ A body T, ∀ ℓ ∈ r.leaves,
      ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, heq =>
      ⟨(EvTy.lit d hsub).invLam rfl heq,
        fun ℓ hℓ => EvTy.invLam_leaves (EvTy.lit d hsub) rfl heq ℓ hℓ⟩
  | _, _, _, .rety D₀ c, heq =>
      let s := D₀.invLamT' heq
      ⟨⟨s.1.u, s.1.B, s.1.hA, s.1.hb, .trans s.1.hc c⟩, fun ℓ hℓ => by
        simp only [EvInvLam.leaves, EvTc.leaves, List.mem_append,
          or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm
        · exact rety_sink (.inl (s.2 ℓ (mem2_l (mem2_l hm))))
        · exact rety_sink (.inl (s.2 ℓ (mem2_l (mem2_r hm))))
        · exact rety_sink (.inl (s.2 ℓ (mem2_r hm)))
        · exact rety_sink (.inr hm)⟩
  | _, _, _, .var _ _ _, heq => nomatch heq
  | _, _, _, .sort _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .wk d c D₀, heq => by
      obtain ⟨A₀, b₀, h₁, hA, hb⟩ := liftShape_lam heq
      subst hA; subst hb
      obtain ⟨r₀, h₀⟩ := D₀.invLamT' h₁
      refine ⟨⟨r₀.u, lift (c + 1) 1 r₀.B,
        EvTy.wk d c r₀.hA, EvTy.wk d (c + 1) r₀.hb,
        EvTc.wk d c r₀.hc⟩, ?_⟩
      intro ℓ hℓ
      simp only [EvInvLam.leaves, EvTy.leaves, EvTc.leaves,
        List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm | hm
      · exact h₀ ℓ (mem2_l (mem2_l hm))
      · exact h₀ ℓ (mem2_l (mem2_r hm))
      · exact h₀ ℓ (mem2_r hm)
  | _, _, _, .esub j u D₀ hget hv hvT, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨A₀', b₀, h₁, hA, hb⟩ | ⟨h₁j, hw⟩) := instShape_lam heq
      · subst hA; subst hb
        obtain ⟨r₀, h₀⟩ := D₀.invLamT' h₁
        refine ⟨⟨r₀.u, instantiate (j + 1) (lift 0 1 (lift 0 j v)) r₀.B,
          EvTy.esub j u r₀.hA hget hv hvT,
          esubFieldCast (EvTy.esub (j + 1) u r₀.hb (by simpa using hget)
            (esubBinderArg (d := .assumption A₀') hv)
            (esubBinderSort (d := .assumption A₀') hvT)),
          EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLam.leaves, EvTy.leaves, EvTc.leaves,
          esubFieldCast_leaves, esubBinderArg_leaves, esubBinderSort_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm | hm | hm
        · exact esub_sink (.inl (h₀ ℓ (mem2_l (mem2_l hm))))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
      · obtain ⟨rhv, hvh⟩ := hv.invLamT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.u, rhv.B, rhv.hA, rhv.hb,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLam.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_l (mem2_l hm)))))
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_l (mem2_r hm)))))
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_r hm))))
        · exact esub_sink (.inl (h₀ ℓ hm))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
  | _, _, _, .subst0 j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨A₀', b₀, h₁, hA, hb⟩ | ⟨h₁j, hw⟩) := instShape_lam heq
      · subst hA; subst hb
        obtain ⟨r₀, h₀⟩ := D₀.invLamT' h₁
        refine ⟨⟨r₀.u, instantiate (j + 1) (lift 0 1 (lift 0 j v)) r₀.B,
          EvTy.subst0 j r₀.hA hget hv,
          esubFieldCast (EvTy.subst0 (j + 1) r₀.hb (by simpa using hget)
            (esubBinderArg (d := .assumption A₀') hv)),
          EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLam.leaves, EvTy.leaves, EvTc.leaves,
          esubFieldCast_leaves, esubBinderArg_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l (mem2_l hm))))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invLamT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.u, rhv.B, rhv.hA, rhv.hb,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLam.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact subst0_sink (.inr (hvh ℓ (mem2_l (mem2_l hm))))
        · exact subst0_sink (.inr (hvh ℓ (mem2_l (mem2_r hm))))
        · exact subst0_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact subst0_sink (.inl (h₀ ℓ hm))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  | _, _, _, .substLet j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨A₀', b₀, h₁, hA, hb⟩ | ⟨h₁j, hw⟩) := instShape_lam heq
      · subst hA; subst hb
        obtain ⟨r₀, h₀⟩ := D₀.invLamT' h₁
        refine ⟨⟨r₀.u, instantiate (j + 1) (lift 0 1 (lift 0 j v)) r₀.B,
          EvTy.substLet j r₀.hA hget hv,
          esubFieldCast (EvTy.substLet (j + 1) r₀.hb (by simpa using hget)
            (esubBinderArg (d := .assumption A₀') hv)),
          EvTc.substLet j r₀.hc hget hv⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLam.leaves, EvTy.leaves, EvTc.leaves,
          esubFieldCast_leaves, esubBinderArg_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l (mem2_l hm))))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invLamT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.u, rhv.B, rhv.hA, rhv.hb,
          .trans rhv.hc (substBvarChainLet r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLam.leaves, EvTc.leaves, substBvarChainLet_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact substLet_sink (.inr (hvh ℓ (mem2_l (mem2_l hm))))
        · exact substLet_sink (.inr (hvh ℓ (mem2_l (mem2_r hm))))
        · exact substLet_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact substLet_sink (.inl (h₀ ℓ hm))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  termination_by _ _ _ D _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- `lam`-inversion on provenance — total over all roots. -/
def EvTy.invLamT {A body : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .lam A body) : EvInvLam R Γ A body T :=
  (D.invLamT' heq).1

theorem EvTy.invLamT_leaves {A body : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .lam A body) :
    ∀ ℓ ∈ (D.invLamT heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ' :=
  (D.invLamT' heq).2

theorem EvTy.invLamT_agree {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .lam A body) →
    D.invLamT heq = D.invLam hD heq
  | _, _, _, .lit d hsub, _, heq => by
      simp only [EvTy.invLamT, EvTy.invLamT', EvTy.invLam]
  | _, _, _, .rety D₀ c, hD, heq => by
      rename_i Γ₀ e₀ T' A₀
      have ih := D₀.invLamT_agree hD heq
      simp only [EvTy.invLamT] at ih
      simp only [EvTy.invLamT, EvTy.invLamT', EvTy.invLam]
      exact congrArg
        (fun r : EvInvLam R Γ₀ A body A₀ =>
          (⟨r.u, r.B, r.hA, r.hb, .trans r.hc c⟩ :
            EvInvLam R Γ₀ A body T')) ih
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-! ### `pi` -/

private def EvTy.invPiT' {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    e = .pi A B →
    Σ' r : EvInvPi R Γ A B T, ∀ ℓ ∈ r.leaves,
      ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, heq =>
      ⟨(EvTy.lit d hsub).invPi rfl heq,
        fun ℓ hℓ => EvTy.invPi_leaves (EvTy.lit d hsub) rfl heq ℓ hℓ⟩
  | _, _, _, .rety D₀ c, heq =>
      let s := D₀.invPiT' heq
      ⟨⟨s.1.u, s.1.v, s.1.hA, s.1.hB, .trans s.1.hc c⟩, fun ℓ hℓ => by
        simp only [EvInvPi.leaves, EvTc.leaves, List.mem_append,
          or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm
        · exact rety_sink (.inl (s.2 ℓ (mem2_l (mem2_l hm))))
        · exact rety_sink (.inl (s.2 ℓ (mem2_l (mem2_r hm))))
        · exact rety_sink (.inl (s.2 ℓ (mem2_r hm)))
        · exact rety_sink (.inr hm)⟩
  | _, _, _, .var _ _ _, heq => nomatch heq
  | _, _, _, .sort _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .wk d c D₀, heq => by
      obtain ⟨A₀, B₀, h₁, hA, hB⟩ := liftShape_pi heq
      subst hA; subst hB
      obtain ⟨r₀, h₀⟩ := D₀.invPiT' h₁
      refine ⟨⟨r₀.u, r₀.v,
        EvTy.wk d c r₀.hA, EvTy.wk d (c + 1) r₀.hB,
        EvTc.wk d c r₀.hc⟩, ?_⟩
      intro ℓ hℓ
      simp only [EvInvPi.leaves, EvTy.leaves, EvTc.leaves,
        List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm | hm
      · exact h₀ ℓ (mem2_l (mem2_l hm))
      · exact h₀ ℓ (mem2_l (mem2_r hm))
      · exact h₀ ℓ (mem2_r hm)
  | _, _, _, .esub j u D₀ hget hv hvT, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨A₀', B₀, h₁, hA, hB⟩ | ⟨h₁j, hw⟩) := instShape_pi heq
      · subst hA; subst hB
        obtain ⟨r₀, h₀⟩ := D₀.invPiT' h₁
        refine ⟨⟨r₀.u, r₀.v,
          EvTy.esub j u r₀.hA hget hv hvT,
          esubFieldCast (EvTy.esub (j + 1) u r₀.hB (by simpa using hget)
            (esubBinderArg (d := .assumption A₀') hv)
            (esubBinderSort (d := .assumption A₀') hvT)),
          EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvPi.leaves, EvTy.leaves, EvTc.leaves,
          esubFieldCast_leaves, esubBinderArg_leaves, esubBinderSort_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm | hm | hm
        · exact esub_sink (.inl (h₀ ℓ (mem2_l (mem2_l hm))))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
      · obtain ⟨rhv, hvh⟩ := hv.invPiT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.u, rhv.v, rhv.hA, rhv.hB,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvPi.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_l (mem2_l hm)))))
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_l (mem2_r hm)))))
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_r hm))))
        · exact esub_sink (.inl (h₀ ℓ hm))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
  | _, _, _, .subst0 j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨A₀', B₀, h₁, hA, hB⟩ | ⟨h₁j, hw⟩) := instShape_pi heq
      · subst hA; subst hB
        obtain ⟨r₀, h₀⟩ := D₀.invPiT' h₁
        refine ⟨⟨r₀.u, r₀.v,
          EvTy.subst0 j r₀.hA hget hv,
          esubFieldCast (EvTy.subst0 (j + 1) r₀.hB (by simpa using hget)
            (esubBinderArg (d := .assumption A₀') hv)),
          EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvPi.leaves, EvTy.leaves, EvTc.leaves,
          esubFieldCast_leaves, esubBinderArg_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l (mem2_l hm))))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invPiT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.u, rhv.v, rhv.hA, rhv.hB,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvPi.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact subst0_sink (.inr (hvh ℓ (mem2_l (mem2_l hm))))
        · exact subst0_sink (.inr (hvh ℓ (mem2_l (mem2_r hm))))
        · exact subst0_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact subst0_sink (.inl (h₀ ℓ hm))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  | _, _, _, .substLet j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨A₀', B₀, h₁, hA, hB⟩ | ⟨h₁j, hw⟩) := instShape_pi heq
      · subst hA; subst hB
        obtain ⟨r₀, h₀⟩ := D₀.invPiT' h₁
        refine ⟨⟨r₀.u, r₀.v,
          EvTy.substLet j r₀.hA hget hv,
          esubFieldCast (EvTy.substLet (j + 1) r₀.hB (by simpa using hget)
            (esubBinderArg (d := .assumption A₀') hv)),
          EvTc.substLet j r₀.hc hget hv⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvPi.leaves, EvTy.leaves, EvTc.leaves,
          esubFieldCast_leaves, esubBinderArg_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l (mem2_l hm))))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invPiT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.u, rhv.v, rhv.hA, rhv.hB,
          .trans rhv.hc (substBvarChainLet r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvPi.leaves, EvTc.leaves, substBvarChainLet_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact substLet_sink (.inr (hvh ℓ (mem2_l (mem2_l hm))))
        · exact substLet_sink (.inr (hvh ℓ (mem2_l (mem2_r hm))))
        · exact substLet_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact substLet_sink (.inl (h₀ ℓ hm))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  termination_by _ _ _ D _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- `pi`-inversion on provenance — total over all roots. -/
def EvTy.invPiT {A B : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .pi A B) : EvInvPi R Γ A B T :=
  (D.invPiT' heq).1

theorem EvTy.invPiT_leaves {A B : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .pi A B) :
    ∀ ℓ ∈ (D.invPiT heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ' :=
  (D.invPiT' heq).2

theorem EvTy.invPiT_agree {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .pi A B) →
    D.invPiT heq = D.invPi hD heq
  | _, _, _, .lit d hsub, _, heq => by
      simp only [EvTy.invPiT, EvTy.invPiT', EvTy.invPi]
  | _, _, _, .rety D₀ c, hD, heq => by
      rename_i Γ₀ e₀ T' A₀
      have ih := D₀.invPiT_agree hD heq
      simp only [EvTy.invPiT] at ih
      simp only [EvTy.invPiT, EvTy.invPiT', EvTy.invPi]
      exact congrArg
        (fun r : EvInvPi R Γ₀ A B A₀ =>
          (⟨r.u, r.v, r.hA, r.hB, .trans r.hc c⟩ :
            EvInvPi R Γ₀ A B T')) ih
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-! ### `letE` -/

private def EvTy.invLetET' {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    e = .letE A value body →
    Σ' r : EvInvLetE R Γ A value body T, ∀ ℓ ∈ r.leaves,
      ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, heq =>
      ⟨(EvTy.lit d hsub).invLetE rfl heq,
        fun ℓ hℓ => EvTy.invLetE_leaves (EvTy.lit d hsub) rfl heq ℓ hℓ⟩
  | _, _, _, .rety D₀ c, heq =>
      let s := D₀.invLetET' heq
      ⟨⟨s.1.u, s.1.B, s.1.hA, s.1.hv, s.1.hb, .trans s.1.hc c⟩,
        fun ℓ hℓ => by
        simp only [EvInvLetE.leaves, EvTc.leaves, List.mem_append,
          or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact rety_sink (.inl (s.2 ℓ (mem2_l (mem2_l (mem2_l hm)))))
        · exact rety_sink (.inl (s.2 ℓ (mem2_l (mem2_l (mem2_r hm)))))
        · exact rety_sink (.inl (s.2 ℓ (mem2_l (mem2_r hm))))
        · exact rety_sink (.inl (s.2 ℓ (mem2_r hm)))
        · exact rety_sink (.inr hm)⟩
  | _, _, _, .var _ _ _, heq => nomatch heq
  | _, _, _, .sort _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .wk d c D₀, heq => by
      obtain ⟨A₀, v₀, b₀, h₁, hA, hv0, hb⟩ := liftShape_letE heq
      subst hA; subst hv0; subst hb
      obtain ⟨r₀, h₀⟩ := D₀.invLetET' h₁
      refine ⟨⟨r₀.u, lift (c + 1) 1 r₀.B,
        EvTy.wk d c r₀.hA, EvTy.wk d c r₀.hv, EvTy.wk d (c + 1) r₀.hb,
        EvTc.cast rfl
          (lift_instantiate_low 1 c 0 v₀ (Nat.zero_le c) r₀.B) rfl
          (EvTc.wk d c r₀.hc)⟩, ?_⟩
      intro ℓ hℓ
      simp only [EvInvLetE.leaves, EvTy.leaves, EvTc.leaves,
        EvTc.cast_leaves, List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm | hm | hm
      · exact h₀ ℓ (mem2_l (mem2_l (mem2_l hm)))
      · exact h₀ ℓ (mem2_l (mem2_l (mem2_r hm)))
      · exact h₀ ℓ (mem2_l (mem2_r hm))
      · exact h₀ ℓ (mem2_r hm)
  | _, _, _, .esub j u D₀ hget hv hvT, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨A₀', v₀, b₀, h₁, hA, hv0, hb⟩ | ⟨h₁j, hw⟩) :=
        instShape_letE heq
      · subst hA; subst hv0; subst hb
        obtain ⟨r₀, h₀⟩ := D₀.invLetET' h₁
        refine ⟨⟨r₀.u, instantiate (j + 1) (lift 0 1 (lift 0 j v)) r₀.B,
          EvTy.esub j u r₀.hA hget hv hvT,
          EvTy.esub j u r₀.hv hget hv hvT,
          esubFieldCast (EvTy.esub (j + 1) u r₀.hb (by simpa using hget)
            (esubBinderArg (d := .letBinding A₀' v₀) hv)
            (esubBinderSort (d := .letBinding A₀' v₀) hvT)),
          EvTc.cast rfl
            (instantiate_instantiate 0 j v₀ (lift 0 j v)
              (Nat.zero_le j) r₀.B)
            rfl (EvTc.subst0 j r₀.hc hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLetE.leaves, EvTy.leaves, EvTc.leaves,
          EvTc.cast_leaves, esubFieldCast_leaves, esubBinderArg_leaves,
          esubBinderSort_leaves, List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
        · exact esub_sink (.inl (h₀ ℓ (mem2_l (mem2_l (mem2_l hm)))))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_l (mem2_l (mem2_r hm)))))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
      · obtain ⟨rhv, hvh⟩ := hv.invLetET' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.u, rhv.B, rhv.hA, rhv.hv, rhv.hb,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLetE.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm
        · exact esub_sink (.inr (.inl
            (hvh ℓ (mem2_l (mem2_l (mem2_l hm))))))
        · exact esub_sink (.inr (.inl
            (hvh ℓ (mem2_l (mem2_l (mem2_r hm))))))
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_l (mem2_r hm)))))
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_r hm))))
        · exact esub_sink (.inl (h₀ ℓ hm))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
  | _, _, _, .subst0 j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨A₀', v₀, b₀, h₁, hA, hv0, hb⟩ | ⟨h₁j, hw⟩) :=
        instShape_letE heq
      · subst hA; subst hv0; subst hb
        obtain ⟨r₀, h₀⟩ := D₀.invLetET' h₁
        refine ⟨⟨r₀.u, instantiate (j + 1) (lift 0 1 (lift 0 j v)) r₀.B,
          EvTy.subst0 j r₀.hA hget hv,
          EvTy.subst0 j r₀.hv hget hv,
          esubFieldCast (EvTy.subst0 (j + 1) r₀.hb (by simpa using hget)
            (esubBinderArg (d := .letBinding A₀' v₀) hv)),
          EvTc.cast rfl
            (instantiate_instantiate 0 j v₀ (lift 0 j v)
              (Nat.zero_le j) r₀.B)
            rfl (EvTc.subst0 j r₀.hc hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLetE.leaves, EvTy.leaves, EvTc.leaves,
          EvTc.cast_leaves, esubFieldCast_leaves, esubBinderArg_leaves,
           List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm | hm | hm
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l (mem2_l (mem2_l hm)))))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l (mem2_l (mem2_r hm)))))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invLetET' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.u, rhv.B, rhv.hA, rhv.hv, rhv.hb,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLetE.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm
        · exact subst0_sink (.inr
            (hvh ℓ (mem2_l (mem2_l (mem2_l hm)))))
        · exact subst0_sink (.inr
            (hvh ℓ (mem2_l (mem2_l (mem2_r hm)))))
        · exact subst0_sink (.inr (hvh ℓ (mem2_l (mem2_r hm))))
        · exact subst0_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact subst0_sink (.inl (h₀ ℓ hm))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  | _, _, _, .substLet j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (⟨A₀', v₀, b₀, h₁, hA, hv0, hb⟩ | ⟨h₁j, hw⟩) :=
        instShape_letE heq
      · subst hA; subst hv0; subst hb
        obtain ⟨r₀, h₀⟩ := D₀.invLetET' h₁
        refine ⟨⟨r₀.u, instantiate (j + 1) (lift 0 1 (lift 0 j v)) r₀.B,
          EvTy.substLet j r₀.hA hget hv,
          EvTy.substLet j r₀.hv hget hv,
          esubFieldCast (EvTy.substLet (j + 1) r₀.hb (by simpa using hget)
            (esubBinderArg (d := .letBinding A₀' v₀) hv)),
          EvTc.cast rfl
            (instantiate_instantiate 0 j v₀ (lift 0 j v)
              (Nat.zero_le j) r₀.B)
            rfl (EvTc.substLet j r₀.hc hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLetE.leaves, EvTy.leaves, EvTc.leaves,
          EvTc.cast_leaves, esubFieldCast_leaves, esubBinderArg_leaves,
           List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm | hm | hm
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l (mem2_l (mem2_l hm)))))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l (mem2_l (mem2_r hm)))))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l (mem2_r hm))))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invLetET' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.u, rhv.B, rhv.hA, rhv.hv, rhv.hb,
          .trans rhv.hc (substBvarChainLet r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLetE.leaves, EvTc.leaves, substBvarChainLet_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm | hm
        · exact substLet_sink (.inr
            (hvh ℓ (mem2_l (mem2_l (mem2_l hm)))))
        · exact substLet_sink (.inr
            (hvh ℓ (mem2_l (mem2_l (mem2_r hm)))))
        · exact substLet_sink (.inr (hvh ℓ (mem2_l (mem2_r hm))))
        · exact substLet_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact substLet_sink (.inl (h₀ ℓ hm))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  termination_by _ _ _ D _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- `letE`-inversion on provenance — total over all roots. -/
def EvTy.invLetET {A value body : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .letE A value body) :
    EvInvLetE R Γ A value body T :=
  (D.invLetET' heq).1

theorem EvTy.invLetET_leaves {A value body : Expr Nat} {Γ : LCtx}
    {e T : Expr Nat} (D : EvTy R Γ e T) (heq : e = .letE A value body) :
    ∀ ℓ ∈ (D.invLetET heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ' :=
  (D.invLetET' heq).2

theorem EvTy.invLetET_agree {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .letE A value body) →
    D.invLetET heq = D.invLetE hD heq
  | _, _, _, .lit d hsub, _, heq => by
      simp only [EvTy.invLetET, EvTy.invLetET', EvTy.invLetE]
  | _, _, _, .rety D₀ c, hD, heq => by
      rename_i Γ₀ e₀ T' A₀
      have ih := D₀.invLetET_agree hD heq
      simp only [EvTy.invLetET] at ih
      simp only [EvTy.invLetET, EvTy.invLetET', EvTy.invLetE]
      exact congrArg
        (fun r : EvInvLetE R Γ₀ A value body A₀ =>
          (⟨r.u, r.B, r.hA, r.hv, r.hb, .trans r.hc c⟩ :
            EvInvLetE R Γ₀ A value body T')) ih
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD


/-! ### `const` -/

private def EvTy.invConstT' (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    e = .const r ls →
    Σ' rr : EvInvConst E n R Γ r ls T, ∀ ℓ ∈ rr.leaves,
      ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, heq =>
      ⟨(EvTy.lit d hsub).invConst rfl heq,
        fun ℓ hℓ => EvTy.invConst_leaves (EvTy.lit d hsub) rfl heq ℓ hℓ⟩
  | _, _, _, .rety D₀ c, heq =>
      let s := D₀.invConstT' hcl hinst heq
      ⟨⟨s.1.m, s.1.hres, s.1.hlen, s.1.hwf, .trans s.1.hc c⟩,
        fun ℓ hℓ => by
        simp only [EvInvConst.leaves, EvTc.leaves, List.mem_append] at hℓ
        rcases hℓ with hm | hm
        · exact rety_sink (.inl (s.2 ℓ hm))
        · exact rety_sink (.inr hm)⟩
  | _, _, _, .var _ _ _, heq => nomatch heq
  | _, _, _, .sort _, heq => nomatch heq
  | _, _, _, .const r₀ ls₀ m hres hlen hwf, heq => by
      injection heq with hr hls
      subst hr; subst hls
      exact ⟨⟨m, hres, hlen, hwf, .refl _ _⟩, fun ℓ hℓ => by
        simp only [EvInvConst.leaves, EvTc.leaves] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, _, .wk d c D₀, heq => by
      obtain h₁ := liftShape_const heq
      obtain ⟨r₀, h₀⟩ := D₀.invConstT' hcl hinst h₁
      refine ⟨⟨r₀.m, r₀.hres, r₀.hlen, r₀.hwf,
        EvTc.cast rfl
          ((lift_instantiateLevels ls 1 r₀.m.mtype c).trans
            (congrArg (instantiateLevels ls) ((hcl r r₀.m r₀.hres).1 c)))
          rfl (EvTc.wk d c r₀.hc)⟩, ?_⟩
      intro ℓ hℓ
      simp only [EvInvConst.leaves, EvTc.leaves, EvTc.cast_leaves] at hℓ
      exact h₀ ℓ hℓ
  | _, _, _, .esub j u D₀ hget hv hvT, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (h₁ | ⟨h₁j, hw⟩) := instShape_const heq
      · obtain ⟨r₀, h₀⟩ := D₀.invConstT' hcl hinst h₁
        refine ⟨⟨r₀.m, r₀.hres, r₀.hlen, r₀.hwf,
          EvTc.cast rfl
            ((hinst r r₀.m r₀.hres).1 ls (lift 0 j v) j) rfl
            (EvTc.subst0 j r₀.hc hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvConst.leaves, EvTc.leaves, EvTc.cast_leaves,
          List.mem_append] at hℓ
        rcases hℓ with hm | hm
        · exact esub_sink (.inl (h₀ ℓ hm))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
      · obtain ⟨rhv, hvh⟩ := hv.invConstT' hcl hinst hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.m, rhv.hres, rhv.hlen, rhv.hwf,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvConst.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm
        · exact esub_sink (.inr (.inl (hvh ℓ hm)))
        · exact esub_sink (.inl (h₀ ℓ hm))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
  | _, _, _, .subst0 j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (h₁ | ⟨h₁j, hw⟩) := instShape_const heq
      · obtain ⟨r₀, h₀⟩ := D₀.invConstT' hcl hinst h₁
        refine ⟨⟨r₀.m, r₀.hres, r₀.hlen, r₀.hwf,
          EvTc.cast rfl
            ((hinst r r₀.m r₀.hres).1 ls (lift 0 j v) j) rfl
            (EvTc.subst0 j r₀.hc hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvConst.leaves, EvTc.leaves, EvTc.cast_leaves,
          List.mem_append] at hℓ
        rcases hℓ with hm | hm
        · exact subst0_sink (.inl (h₀ ℓ hm))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invConstT' hcl hinst hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.m, rhv.hres, rhv.hlen, rhv.hwf,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvConst.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm
        · exact subst0_sink (.inr (hvh ℓ hm))
        · exact subst0_sink (.inl (h₀ ℓ hm))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  | _, _, _, .substLet j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (h₁ | ⟨h₁j, hw⟩) := instShape_const heq
      · obtain ⟨r₀, h₀⟩ := D₀.invConstT' hcl hinst h₁
        refine ⟨⟨r₀.m, r₀.hres, r₀.hlen, r₀.hwf,
          EvTc.cast rfl
            ((hinst r r₀.m r₀.hres).1 ls (lift 0 j v) j) rfl
            (EvTc.substLet j r₀.hc hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvConst.leaves, EvTc.leaves, EvTc.cast_leaves,
          List.mem_append] at hℓ
        rcases hℓ with hm | hm
        · exact substLet_sink (.inl (h₀ ℓ hm))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invConstT' hcl hinst hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.m, rhv.hres, rhv.hlen, rhv.hwf,
          .trans rhv.hc (substBvarChainLet r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvConst.leaves, EvTc.leaves, substBvarChainLet_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm
        · exact substLet_sink (.inr (hvh ℓ hm))
        · exact substLet_sink (.inl (h₀ ℓ hm))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  termination_by _ _ _ D _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- `const`-inversion on provenance — total over all roots. The
    member-transport casts need the same `EnvClosed`/`EnvMembersSubstStable`
    structure `hasTyTWeaken`/`hasTyT_substS` read. -/
def EvTy.invConstT (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {r : Nat} {ls : List Level} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .const r ls) :
    EvInvConst E n R Γ r ls T :=
  (D.invConstT' hcl hinst heq).1

theorem EvTy.invConstT_leaves (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {r : Nat} {ls : List Level}
    {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .const r ls) :
    ∀ ℓ ∈ (D.invConstT hcl hinst heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ' :=
  (D.invConstT' hcl hinst heq).2

theorem EvTy.invConstT_agree (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .const r ls) →
    D.invConstT hcl hinst heq = D.invConst hD heq
  | _, _, _, .lit d hsub, _, heq => by
      simp only [EvTy.invConstT, EvTy.invConstT', EvTy.invConst]
  | _, _, _, .rety D₀ c, hD, heq => by
      rename_i Γ₀ e₀ T' A₀
      have ih := D₀.invConstT_agree hcl hinst hD heq
      simp only [EvTy.invConstT] at ih
      simp only [EvTy.invConstT, EvTy.invConstT', EvTy.invConst]
      exact congrArg
        (fun rr : EvInvConst E n R Γ₀ r ls A₀ =>
          (⟨rr.m, rr.hres, rr.hlen, rr.hwf, .trans rr.hc c⟩ :
            EvInvConst E n R Γ₀ r ls T')) ih
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-! ### `lit` -/

private def EvTy.invLitT' {t : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    e = .lit t →
    Σ' r : EvInvLit R Γ t T, ∀ ℓ ∈ r.leaves,
      ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, heq =>
      ⟨(EvTy.lit d hsub).invLit rfl heq,
        fun ℓ hℓ => EvTy.invLit_leaves (EvTy.lit d hsub) rfl heq ℓ hℓ⟩
  | _, _, _, .rety D₀ c, heq =>
      let s := D₀.invLitT' heq
      ⟨⟨s.1.T', s.1.hnat, .trans s.1.hc c⟩, fun ℓ hℓ => by
        simp only [EvInvLit.leaves, EvTc.leaves, List.mem_append,
          or_assoc] at hℓ
        rcases hℓ with hm | hm | hm
        · exact rety_sink (.inl (s.2 ℓ (mem2_l hm)))
        · exact rety_sink (.inl (s.2 ℓ (mem2_r hm)))
        · exact rety_sink (.inr hm)⟩
  | _, _, _, .var _ _ _, heq => nomatch heq
  | _, _, _, .sort _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .wk d c D₀, heq => by
      obtain h₁ := liftShape_lit heq
      obtain ⟨r₀, h₀⟩ := D₀.invLitT' h₁
      refine ⟨⟨lift c 1 r₀.T',
        EvTy.cast rfl (natExpand_lift c 1 t) rfl
          (EvTy.wk d c r₀.hnat),
        EvTc.wk d c r₀.hc⟩, ?_⟩
      intro ℓ hℓ
      simp only [EvInvLit.leaves, EvTy.leaves, EvTc.leaves,
        EvTy.cast_leaves, List.mem_append] at hℓ
      rcases hℓ with hm | hm
      · exact h₀ ℓ (mem2_l hm)
      · exact h₀ ℓ (mem2_r hm)
  | _, _, _, .esub j u D₀ hget hv hvT, heq => by
      rename_i Γ₀ e₀ A₀ t' v
      obtain (h₁ | ⟨h₁j, hw⟩) := instShape_lit heq
      · obtain ⟨r₀, h₀⟩ := D₀.invLitT' h₁
        refine ⟨⟨instantiate j (lift 0 j v) r₀.T',
          EvTy.cast rfl (natExpand_instantiate j (lift 0 j v) t) rfl
            (EvTy.esub j u r₀.hnat hget hv hvT),
          EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLit.leaves, EvTy.leaves, EvTc.leaves,
          EvTy.cast_leaves, List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm | hm
        · exact esub_sink (.inl (h₀ ℓ (mem2_l hm)))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inr (.inr ⟨ℓ, hm, .inl rfl⟩))
        · exact esub_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
      · obtain ⟨rhv, hvh⟩ := hv.invLitT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.T', rhv.hnat,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLit.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_l hm))))
        · exact esub_sink (.inr (.inl (hvh ℓ (mem2_r hm))))
        · exact esub_sink (.inl (h₀ ℓ hm))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
  | _, _, _, .subst0 j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t' v
      obtain (h₁ | ⟨h₁j, hw⟩) := instShape_lit heq
      · obtain ⟨r₀, h₀⟩ := D₀.invLitT' h₁
        refine ⟨⟨instantiate j (lift 0 j v) r₀.T',
          EvTy.cast rfl (natExpand_instantiate j (lift 0 j v) t) rfl
            (EvTy.subst0 j r₀.hnat hget hv),
          EvTc.subst0 j r₀.hc hget hv⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLit.leaves, EvTy.leaves, EvTc.leaves,
          EvTy.cast_leaves, List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm
        · exact subst0_sink (.inl (h₀ ℓ (mem2_l hm)))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact subst0_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invLitT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.T', rhv.hnat,
          .trans rhv.hc (substBvarChain r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLit.leaves, EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm
        · exact subst0_sink (.inr (hvh ℓ (mem2_l hm)))
        · exact subst0_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact subst0_sink (.inl (h₀ ℓ hm))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  | _, _, _, .substLet j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t' v
      obtain (h₁ | ⟨h₁j, hw⟩) := instShape_lit heq
      · obtain ⟨r₀, h₀⟩ := D₀.invLitT' h₁
        refine ⟨⟨instantiate j (lift 0 j v) r₀.T',
          EvTy.cast rfl (natExpand_instantiate j (lift 0 j v) t) rfl
            (EvTy.substLet j r₀.hnat hget hv),
          EvTc.substLet j r₀.hc hget hv⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLit.leaves, EvTy.leaves, EvTc.leaves,
          EvTy.cast_leaves, List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm
        · exact substLet_sink (.inl (h₀ ℓ (mem2_l hm)))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
        · exact substLet_sink (.inl (h₀ ℓ (mem2_r hm)))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invLitT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨⟨rhv.T', rhv.hnat,
          .trans rhv.hc (substBvarChainLet r₀ hget hv)⟩, ?_⟩
        intro ℓ hℓ
        simp only [EvInvLit.leaves, EvTc.leaves, substBvarChainLet_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm | hm
        · exact substLet_sink (.inr (hvh ℓ (mem2_l hm)))
        · exact substLet_sink (.inr (hvh ℓ (mem2_r hm)))
        · exact substLet_sink (.inl (h₀ ℓ hm))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  termination_by _ _ _ D _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- `lit`-inversion on provenance — total over all roots. -/
def EvTy.invLitT {t : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .lit t) : EvInvLit R Γ t T :=
  (D.invLitT' heq).1

theorem EvTy.invLitT_leaves {t : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .lit t) :
    ∀ ℓ ∈ (D.invLitT heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ' :=
  (D.invLitT' heq).2

theorem EvTy.invLitT_agree {t : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .lit t) →
    D.invLitT heq = D.invLit hD heq
  | _, _, _, .lit d hsub, _, heq => by
      simp only [EvTy.invLitT, EvTy.invLitT', EvTy.invLit]
  | _, _, _, .rety D₀ c, hD, heq => by
      rename_i Γ₀ e₀ T' A₀
      have ih := D₀.invLitT_agree hD heq
      simp only [EvTy.invLitT] at ih
      simp only [EvTy.invLitT, EvTy.invLitT', EvTy.invLit]
      exact congrArg
        (fun r : EvInvLit R Γ₀ t A₀ =>
          (⟨r.T', r.hnat, .trans r.hc c⟩ : EvInvLit R Γ₀ t T')) ih
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-! ### `sort` -/

private def EvTy.invSortTT' {l : Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    e = .sort l →
    Σ' c₀ : EvTc R Γ (.sort (.succ l)) T, ∀ ℓ ∈ c₀.leaves,
      ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, heq =>
      ⟨(EvTy.lit d hsub).invSortT rfl heq,
        fun ℓ hℓ => EvTy.invSortT_leaves (EvTy.lit d hsub) rfl heq ℓ hℓ⟩
  | _, _, _, .rety D₀ c, heq =>
      let s := D₀.invSortTT' heq
      ⟨.trans s.1 c, fun ℓ hℓ => by
        simp only [EvTc.leaves, List.mem_append] at hℓ
        rcases hℓ with hm | hm
        · exact rety_sink (.inl (s.2 ℓ hm))
        · exact rety_sink (.inr hm)⟩
  | _, _, _, .var _ _ _, heq => nomatch heq
  | _, _, _, .sort l₀, heq => by
      injection heq with hl
      subst hl
      exact ⟨.refl _ _, fun ℓ hℓ => by
        simp only [EvTc.leaves] at hℓ
        exact absurd hℓ (List.not_mem_nil _)⟩
  | _, _, _, .const _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .wk d c D₀, heq => by
      obtain h₁ := liftShape_sort heq
      obtain ⟨r₀, h₀⟩ := D₀.invSortTT' h₁
      refine ⟨EvTc.wk d c r₀, ?_⟩
      intro ℓ hℓ
      simp only [EvTc.leaves] at hℓ
      exact h₀ ℓ hℓ
  | _, _, _, .esub j u D₀ hget hv hvT, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (h₁ | ⟨h₁j, hw⟩) := instShape_sort heq
      · obtain ⟨r₀, h₀⟩ := D₀.invSortTT' h₁
        refine ⟨EvTc.subst0 j r₀ hget hv, ?_⟩
        intro ℓ hℓ
        simp only [EvTc.leaves, List.mem_append] at hℓ
        rcases hℓ with hm | hm
        · exact esub_sink (.inl (h₀ ℓ hm))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
      · obtain ⟨rhv, hvh⟩ := hv.invSortTT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨.trans rhv (substBvarChain r₀ hget hv), ?_⟩
        intro ℓ hℓ
        simp only [EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm
        · exact esub_sink (.inr (.inl (hvh ℓ hm)))
        · exact esub_sink (.inl (h₀ ℓ hm))
        · exact esub_sink (.inr (.inl ⟨ℓ, hm, .inl rfl⟩))
  | _, _, _, .subst0 j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (h₁ | ⟨h₁j, hw⟩) := instShape_sort heq
      · obtain ⟨r₀, h₀⟩ := D₀.invSortTT' h₁
        refine ⟨EvTc.subst0 j r₀ hget hv, ?_⟩
        intro ℓ hℓ
        simp only [EvTc.leaves, List.mem_append] at hℓ
        rcases hℓ with hm | hm
        · exact subst0_sink (.inl (h₀ ℓ hm))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invSortTT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨.trans rhv (substBvarChain r₀ hget hv), ?_⟩
        intro ℓ hℓ
        simp only [EvTc.leaves, substBvarChain_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm
        · exact subst0_sink (.inr (hvh ℓ hm))
        · exact subst0_sink (.inl (h₀ ℓ hm))
        · exact subst0_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  | _, _, _, .substLet j D₀ hget hv, heq => by
      rename_i Γ₀ e₀ A₀ t v
      obtain (h₁ | ⟨h₁j, hw⟩) := instShape_sort heq
      · obtain ⟨r₀, h₀⟩ := D₀.invSortTT' h₁
        refine ⟨EvTc.substLet j r₀ hget hv, ?_⟩
        intro ℓ hℓ
        simp only [EvTc.leaves, List.mem_append] at hℓ
        rcases hℓ with hm | hm
        · exact substLet_sink (.inl (h₀ ℓ hm))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
      · obtain ⟨rhv, hvh⟩ := hv.invSortTT' hw
        obtain ⟨r₀, h₀⟩ := D₀.invBvarT' h₁j
        refine ⟨.trans rhv (substBvarChainLet r₀ hget hv), ?_⟩
        intro ℓ hℓ
        simp only [EvTc.leaves, substBvarChainLet_leaves,
          List.mem_append, or_assoc] at hℓ
        rcases hℓ with hm | hm | hm
        · exact substLet_sink (.inr (hvh ℓ hm))
        · exact substLet_sink (.inl (h₀ ℓ hm))
        · exact substLet_sink (.inr ⟨ℓ, hm, .inl rfl⟩)
  termination_by _ _ _ D _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- `sort`-inversion on provenance — total over all roots: a chain. -/
def EvTy.invSortTT {l : Level} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .sort l) : EvTc R Γ (.sort (.succ l)) T :=
  (D.invSortTT' heq).1

theorem EvTy.invSortTT_leaves {l : Level} {Γ : LCtx} {e T : Expr Nat}
    (D : EvTy R Γ e T) (heq : e = .sort l) :
    ∀ ℓ ∈ (D.invSortTT heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ' :=
  (D.invSortTT' heq).2

theorem EvTy.invSortTT_agree {l : Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .sort l) →
    D.invSortTT heq = D.invSortT hD heq
  | _, _, _, .lit d hsub, _, heq => by
      simp only [EvTy.invSortTT, EvTy.invSortTT', EvTy.invSortT]
  | _, _, _, .rety D₀ c, hD, heq => by
      have ih := D₀.invSortTT_agree hD heq
      simp only [EvTy.invSortTT] at ih
      simp only [EvTy.invSortTT, EvTy.invSortTT', EvTy.invSortT]
      exact congrArg (fun x => EvTc.trans x c) ih
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD


/-! ### non-vacuity pins (`emptyEnv`, `n = 0`) -/

private def pinCl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
private def pinSS : EnvMembersSubstStable emptyEnv :=
  envWfT_subst_inst EnvWfT.empty

/-- `bvar 0` in one `sort 1` assumption; also the esub `D₀` of pins 2/3. -/
private def pinB0_1 : HasTyT emptyEnv 0 [.assumption (.sort (.succ .zero))]
    (.bvar 0) (.sort (.succ .zero)) := .bvar _ 0 _ rfl

/-- `lam (sort 1) (bvar 0) : pi (sort 1) (sort 1)`. -/
private def pinLamS1 : HasTyT emptyEnv 0 []
    (.lam (.sort (.succ .zero)) (.bvar 0))
    (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .lam [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)
    (.sort (.succ .zero)) (.sort [] (.succ .zero)) pinB0_1

/-- `(lam (sort 1) (bvar 0)) (bvar 0) : sort 1` in one `sort 1`
    assumption — the `app` literal for the `wk` pin. -/
private def pinAppD : HasTyT emptyEnv 0 [.assumption (.sort (.succ .zero))]
    (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.bvar 0))
    (.sort (.succ .zero)) :=
  .app _ _ _ _ _
    (hasTyTWeaken (.assumption (.sort (.succ .zero))) pinCl (c := 0)
      pinLamS1) pinB0_1

/-- the `wk`-root pin: the app typing weakened by one `sort 0`
    assumption. -/
private def pinR1 : List (Jd emptyEnv 0) := [.ty pinAppD]
private def pinAppWk : EvTy pinR1
    [.assumption (.sort .zero), .assumption (.sort (.succ .zero))]
    (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.bvar 1))
    (.sort (.succ .zero)) :=
  .wk (.assumption (.sort .zero)) 0
    (.lit pinAppD ⟨.ty pinAppD, .head _, .inl rfl⟩)

/-- `invAppT` through a `wk` root. -/
def pin_invAppT_wk : EvInvApp pinR1
    [.assumption (.sort .zero), .assumption (.sort (.succ .zero))]
    (.lam (.sort (.succ .zero)) (.bvar 0)) (.bvar 1)
    (.sort (.succ .zero)) :=
  pinAppWk.invAppT rfl

/-- its `_leaves`: every inverted leaf is at-or-below the wk'd leaf. -/
theorem pin_invAppT_wk_leaves :
    ∀ ℓ ∈ (pinAppWk.invAppT rfl).leaves,
      ∃ ℓ' ∈ pinAppWk.leaves, SubEq ℓ ℓ' :=
  pinAppWk.invAppT_leaves rfl

/-- the esub case-(i) pin: substituting `sort 0` for the `sort 1`
    assumption under a `wk`-rooted `lam` typing — `e₀` is the `lam`
    (not the substituted variable), so the head survives `instantiate`. -/
private def pinS0 : HasTyT emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort [] .zero
private def pinS1 : HasTyT emptyEnv 0 [] (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) := .sort [] (.succ .zero)

private def pinR2 : List (Jd emptyEnv 0) := [.ty pinLamS1, .ty pinS0, .ty pinS1]

private def pinEsubLam : EvTy pinR2 []
    (.lam (.sort (.succ .zero)) (.bvar 0))
    (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .esub (v := .sort .zero) 0 (.succ (.succ .zero))
    (.wk (.assumption (.sort (.succ .zero))) 0
      (.lit pinLamS1 ⟨.ty pinLamS1, .head _, .inl rfl⟩)) rfl
    (.lit pinS0 ⟨.ty pinS0, .tail _ (.head _), .inl rfl⟩)
    (.lit pinS1 ⟨.ty pinS1, .tail _ (.tail _ (.head _)), .inl rfl⟩)

/-- `invLamT` through an `esub` root, case (i). -/
def pin_invLamT_esub : EvInvLam pinR2 [] (.sort (.succ .zero)) (.bvar 0)
    (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  pinEsubLam.invLamT rfl

theorem pin_invLamT_esub_leaves :
    ∀ ℓ ∈ (pinEsubLam.invLamT rfl).leaves,
      ∃ ℓ' ∈ pinEsubLam.leaves, SubEq ℓ ℓ' :=
  pinEsubLam.invLamT_leaves rfl

/-- the esub case-(ii) pin: `D₀` types `bvar 0` itself, so the inverted
    term IS the replacement `w` — the application
    `(lam (sort 1) (bvar 0)) (sort 0)`. Inversion reads `hv`. -/
private def pinAppV : HasTyT emptyEnv 0 []
    (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
    (.sort (.succ .zero)) :=
  .app _ _ _ _ _ pinLamS1 pinS0

private def pinR3 : List (Jd emptyEnv 0) := [.ty pinB0_1, .ty pinAppV, .ty pinS1]

private def pinEsubApp : EvTy pinR3 []
    (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
    (.sort (.succ .zero)) :=
  .esub (v := .app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
    0 (.succ (.succ .zero))
    (.lit pinB0_1 ⟨.ty pinB0_1, .head _, .inl rfl⟩) rfl
    (.lit pinAppV ⟨.ty pinAppV, .tail _ (.head _), .inl rfl⟩)
    (.lit pinS1 ⟨.ty pinS1, .tail _ (.tail _ (.head _)), .inl rfl⟩)

/-- `invAppT` through an `esub` root, case (ii): the residual chain is
    `hv`'s inversion chain `trans` the substituted bvar chain. -/
def pin_invAppT_esub_ii : EvInvApp pinR3 []
    (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)
    (.sort (.succ .zero)) :=
  pinEsubApp.invAppT rfl

theorem pin_invAppT_esub_ii_leaves :
    ∀ ℓ ∈ (pinEsubApp.invAppT rfl).leaves,
      ∃ ℓ' ∈ pinEsubApp.leaves, SubEq ℓ ℓ' :=
  pinEsubApp.invAppT_leaves rfl

#print axioms instShape_pi
#print axioms EvTy.invAppT
#print axioms EvTy.invLamT
#print axioms EvTy.invPiT
#print axioms EvTy.invLetET
#print axioms EvTy.invBvarT
#print axioms EvTy.invConstT
#print axioms EvTy.invLitT
#print axioms EvTy.invSortTT
#print axioms EvTy.invAppT_leaves
#print axioms EvTy.invLamT_leaves
#print axioms EvTy.invPiT_leaves
#print axioms EvTy.invLetET_leaves
#print axioms EvTy.invBvarT_leaves
#print axioms EvTy.invConstT_leaves
#print axioms EvTy.invLitT_leaves
#print axioms EvTy.invSortTT_leaves
#print axioms EvTy.invAppT_agree
#print axioms EvTy.invLamT_agree
#print axioms EvTy.invPiT_agree
#print axioms EvTy.invLetET_agree
#print axioms EvTy.invBvarT_agree
#print axioms EvTy.invConstT_agree
#print axioms EvTy.invLitT_agree
#print axioms EvTy.invSortTT_agree
#print axioms pin_invAppT_wk
#print axioms pin_invAppT_wk_leaves
#print axioms pin_invLamT_esub
#print axioms pin_invLamT_esub_leaves
#print axioms pin_invAppT_esub_ii
#print axioms pin_invAppT_esub_ii_leaves

end Rcic.Declarative.F8Measure
