import rcic.RcicSynSRLitPiAlign
import rcic.RcicERScope1

/-!
# `RcicSynSRLitPiInv` — the four `TyP`-level inversions as named boundaries

cc 12:50Z item (2): the four `TyP`-level inversions under `wk` / `esub` /
`linst` / `ewk`, then the five `ZetaSlot` arms and `EpsEpsWPairW` from them.

**Measurement first.** Each transport arm of `zetaSlotAlignEW_of_residuals`
is, definitionally, `ZetaSlotAlignEW` at the *de-transported* display —
`RoutedDisp`'s `wk`/`esub`/`linst`/`ewk` constructors route `removeAt ρ c` /
`insertDisp b j ρ` / `ρ` / `ρ` back at the base context or source env.
§2 pins this down kernel-side: `arm = align ∘ de-transport`. So the arms are
the fixed point, not separate content — the inversion's job is to feed the
*produced* derivation's `eps`, which the `RoutedDisp`-induction's own `ih`
cannot reach (the de-transported routing is not a spine subterm).

The inversions themselves (§1) are stated exactly as the transport arms
consume them: a transported `TyP` (subject a `lift`/`instantiate`/
`instantiateLevels`-image, or env an extension point) descends to a
derivation at the base. Each is a genuine boundary, not a lemma pending
tactics: `conv`/`cctx` nodes embed `CvP` evidence whose endpoints are NOT
transported — a `TyP` inversion needs the `CvP` un-transport twin, and the
`bvar`/`const`/`lit` regularity fields keep the sort-shape only under a
tracked motive the `conv` arm cannot supply (the (B)-cluster wall, same
family as `ZetaSlotEwkArmW`/`EpsWPrefixNormW`).

§1: the four named Props + the one real reduction they immediately give
(`ZetaSlotHeadUnwkW` is `TyPInvWkW` at `c = 0`). §2: the four arms as
`ZetaSlotAlignEW`-projections. §3: on-cone instances — Demand-reachable
(`canon`-routed), `LevelHom id`, all premises inhabited.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the four inversion Props -/

/-- `wk`-inversion: a `lift c 1`-image typed at the inserted context descends
    to a `Γ`-derivation (of some type — the consumed use only needs the
    existential). `ZetaSlotHeadUnwkW` is the `c = 0` face. -/
def TyPInvWkW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (d : LocalDecl) (c : Nat)
    {e T : Expr Nat},
    TyP E n (insertAt d c Γ) (lift c 1 e) T →
    ∃ (T' : Expr Nat), Nonempty (TyP E n Γ e T')

/-- `esub`-inversion: an `instantiate j (lift 0 j v)`-image typed at the
    `substRemove` context ascends to a `Γ`-derivation (`TyP.esub`'s premise
    slot). The replacement typings `hvS`/`hvT` are the node's own certificate
    fields — the arm carries them, so the inversion does too. -/
def TyPInvEsubW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t v : Expr Nat} {j : Nat}
    {u : Level} (_hget : Γ[j]? = some (.assumption t))
    (_hvS : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (_hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    {e T : Expr Nat},
    TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) e) T →
    ∃ (T' : Expr Nat), Nonempty (TyP E n Γ e T')

/-- `linst`-inversion: an `instantiateLevels ls`-image at the instantiated
    context descends to arity `a'` (`TyP.linst`'s premise arity). -/
def TyPInvLinstW : Prop :=
  ∀ {E : ResolvedEnv} {n a' : Nat} {Γ : LCtx} (ls : List Level)
    (_hls : levelsBounded n ls = true) (_hlen : ls.length = a')
    {e T : Expr Nat},
    TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls e) T →
    ∃ (T' : Expr Nat), Nonempty (TyP E a' Γ e T')

/-- `ewk`-inversion (environment strengthening): a derivation at the
    extended env descends to the source. The genuinely-false direction
    off-cone (`const`/`iota` resolve members the prefix may lack); on-cone
    the subject's consts are the source-typed subject's own — the
    `hasTyT_strengthen`-shaped gate lives inside any attempted proof. -/
def TyPInvEwkW : Prop :=
  ∀ {E₀ E : ResolvedEnv} (_hext : EnvExt E₀ E) {n : Nat} {Γ : LCtx}
    {e T : Expr Nat},
    TyP E n Γ e T → ∃ (T' : Expr Nat), Nonempty (TyP E₀ n Γ e T')

/-- The head-slot unwinding is the `c = 0` face of `TyPInvWkW`
    (`insertAt _ 0` and `lift 0 1` unfold definitionally). -/
theorem zetaSlotHeadUnwkW_of_invWk (h : TyPInvWkW) : ZetaSlotHeadUnwkW := by
  intro E n Γ d e T D
  exact h d 0 D

/-! ## §2 each transport arm IS the alignment at its de-transported display

These four projections are the exact fixed-point content: nothing is lost
between `ZetaSlotAlignEW` and the named arms. -/

/-- `wk` arm = alignment at `removeAt ρ' c` (routed by `RoutedDisp.wk`). -/
theorem zetaSlotWkArmW_of_align (a : ZetaSlotAlignEW) : ZetaSlotWkArmW := by
  intro E n Γ σ ρ' d c hρ' i v A hval hty T hv
  exact a hval hty hv (.wk d c hρ')

/-- `esub` arm = alignment at `insertDisp (binderDisp _) j ρ'`
    (routed by `RoutedDisp.esub`). -/
theorem zetaSlotEsubArmW_of_align (a : ZetaSlotAlignEW) : ZetaSlotEsubArmW := by
  intro E n Γ σ ρ' t vₛ j u hget hvS hvT hρ' i v A hval hty T hv
  exact a hval hty hv (.esub hget hvS hvT hρ')

/-- `linst` arm = alignment at `ρ` under the composite level map
    (routed by `RoutedDisp.linst`). -/
theorem zetaSlotLinstArmW_of_align (a : ZetaSlotAlignEW) : ZetaSlotLinstArmW := by
  intro E n a' Γ σ ρ ls hls hlen hρ i v A hval hty T hv
  exact a hval hty hv (.linst ls hls hlen hρ)

/-- `ewk` arm = alignment at `ρ` at the source env
    (routed by `RoutedDisp.ewk`). -/
theorem zetaSlotEwkArmW_of_align (a : ZetaSlotAlignEW) : ZetaSlotEwkArmW := by
  intro E₀ E n Γ σ ρ hext hρ i v A hval hty T hv
  exact a hval hty hv (.ewk hext hρ)

/-! ## §3 on-cone instances of the four inversions

Each pin: `E = emptyEnv`, `σ`-free (these Props have no `σ`), the premise
derivation inhabited by `TyP.sort`, the conclusion's existential met by the
same sort rule at the descended context. Demand-reachability: the contexts
are `canon`-routable (`CtxP.assumption`/`letBinding`/`nil`). -/

/-- `TyPInvWkW` on-cone: `Γ = []`, `d = .assumption (.sort .zero)`, `c = 0`,
    `e = .sort .zero` — `insertAt _ 0 [] = [d]`, `lift 0 1` on a sort is
    `rfl`-invariant. -/
theorem tyPInvWkW_onCone :
    ∃ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (d : LocalDecl) (c : Nat)
      (e T : Expr Nat) (_ : TyP E n (insertAt d c Γ) (lift c 1 e) T),
      ∃ (T' : Expr Nat), Nonempty (TyP E n Γ e T') :=
  ⟨emptyEnv, 0, [], .assumption (.sort .zero), 0, .sort .zero,
    .sort (.succ .zero),
    TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    ⟨TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)⟩⟩

/-- `TyPInvEsubW` on-cone: `Γ = [.assumption (.sort 1)]`, `j = 0`, `v = t =
    .sort` chain — `substRemove _ 0` clears the head, `instantiate 0 _ (sort)`
    is `rfl`-invariant, both replacement typings are `TyP.sort`. -/
theorem tyPInvEsubW_onCone :
    ∃ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (t v : Expr Nat) (j : Nat)
      (u : Level) (_ : Γ[j]? = some (.assumption t))
      (_ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (_ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
      (e T : Expr Nat)
      (_ : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) e) T),
      ∃ (T' : Expr Nat), Nonempty (TyP E n Γ e T') :=
  ⟨emptyEnv, 0, [.assumption (.sort (.succ .zero))], .sort (.succ .zero),
    .sort .zero, 0, .succ (.succ .zero), rfl,
    TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _),
    TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _),
    .sort .zero, .sort (.succ .zero),
    TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    ⟨TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _)⟩⟩

/-- `TyPInvLinstW` on-cone: `ls = []` (`levelsBounded`/`length` by `rfl`),
    `instLvlsCtx []` and `instantiateLevels []` are `rfl`-identities. -/
theorem tyPInvLinstW_onCone :
    ∃ (E : ResolvedEnv) (n a' : Nat) (Γ : LCtx) (ls : List Level)
      (_ : levelsBounded n ls = true) (_ : ls.length = a')
      (e T : Expr Nat)
      (_ : TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls e) T),
      ∃ (T' : Expr Nat), Nonempty (TyP E a' Γ e T') :=
  ⟨emptyEnv, 0, 0, [.assumption (.sort .zero)], [], rfl, rfl,
    .sort .zero, .sort (.succ .zero),
    TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    ⟨TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _)⟩⟩

/-- `TyPInvEwkW` on-cone: the diagonal `E₀ = E = emptyEnv`
    (`envExt_refl`). -/
theorem tyPInvEwkW_onCone :
    ∃ (E₀ E : ResolvedEnv) (_ : EnvExt E₀ E) (n : Nat) (Γ : LCtx)
      (e T : Expr Nat) (_ : TyP E n Γ e T),
      ∃ (T' : Expr Nat), Nonempty (TyP E₀ n Γ e T') :=
  ⟨emptyEnv, emptyEnv, envExt_refl emptyEnv, 0,
    [.assumption (.sort .zero)], .sort .zero, .sort (.succ .zero),
    TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    ⟨TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _)⟩⟩

/-! ## §4 the unguarded inversions are refuted — the guards are the boundary

`TyPInvWkW`, `TyPInvLinstW`, `TyPInvEwkW` as stated in §1 are **false** —
each admits a small counterexample whose premises are all inhabited
(`emptyEnv`-anchored or a one-member `extendEnv`; nothing exotic). The
guarded restatements below are the consumable boundaries. `TyPInvEsubW`
survives: `hget` forces `j < Γ.length`, and every out-of-bounds branch is
killed by `substRemove` length arithmetic — it stays unguarded.

The three counterexample shapes:

- `wk`: `insertAt d c []` clamps to `[d]` for every `c ≥ 1`, and
  `lift c 1 (.bvar i)` leaves `bvar i` for `i < c` — so `bvar 0` acquires
  a typing at `[d]` that cannot descend to `[]`.
- `linst`: arity `a'` descends from `n`; a `.param k` with `a' ≤ k < n`
  is legal at the premise arity and illegal at the conclusion.
- `ewk`: the extension may add a member the prefix lacks; `const r`
  resolves only at `E`. -/

/-- `bvar i` is untypeable once `i` is out of bounds — induction on the
    derivation in `TyP.termFree_lt`'s shape. Nested patterns on the subject
    (never `cases e'`/`cases he`, which would revert `D` and break the
    `sizeOf` link to the scrutinee). Every transport arm either preserves the
    bound arithmetically (`wk`/`linst`/`cctx`/`ewk`/`conv`), or — for
    `esub`/`lsub` — splits on the `instantiate` cutoff: the `i' = j` branch
    fires the `hv` induction hypothesis (the replacement's own typing is out
    of bounds), `i' > j` descends to `i'+1`, and `i' < j` is vacuous. -/
theorem tyP_bvar_oob {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {i : Nat} : (D : TyP E n Γ e T) → e = .bvar i → Γ.length ≤ i → False
  | .sort .., he, _ => by simp only [reduceCtorEq] at he
  | .bvar _ _ _ i' _ _ hlook _, he, hlen => by
      have hii := (Expr.bvar.injEq ..).mp he
      have hlt := lookupType_lt_length hlook
      omega
  | .const .., he, _ => by simp only [reduceCtorEq] at he
  | .pi .., he, _ => by simp only [reduceCtorEq] at he
  | .lam .., he, _ => by simp only [reduceCtorEq] at he
  | .app .., he, _ => by simp only [reduceCtorEq] at he
  | .letE .., he, _ => by simp only [reduceCtorEq] at he
  | .lit .., he, _ => by simp only [reduceCtorEq] at he
  | .conv _ _ _ _ _ _ _ h _, he, hlen => tyP_bvar_oob h he hlen
  | .wk _ _ _ (.bvar i') _ d c D, he, hlen => by
      rw [insertAt_length] at hlen
      simp only [lift] at he
      split at he <;> have hii := (Expr.bvar.injEq ..).mp he <;>
        exact tyP_bvar_oob D rfl (by omega)
  | .wk _ _ _ (.sort ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.const ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.pi ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.lam ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.app ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.letE ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.lit ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .esub _ _ Γ' (.bvar i') _ _ v j _ D hget hv _, he, hlen => by
      obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hget
      have hlen' : Γ'.length - 1 ≤ i := substRemove_length_lt hj ▸ hlen
      simp only [instantiate] at he
      split at he
      · exact tyP_bvar_oob hv he hlen
      · split at he <;> have hii := (Expr.bvar.injEq ..).mp he <;>
          first | exact tyP_bvar_oob D rfl (by omega) | omega
  | .esub _ _ _ (.sort ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.const ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.pi ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.lam ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.app ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.letE ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.lit ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ Γ' (.bvar i') _ _ v j _ D hget hv _, he, hlen => by
      obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hget
      have hlen' : Γ'.length - 1 ≤ i := substRemove_length_lt hj ▸ hlen
      simp only [instantiate] at he
      split at he
      · exact tyP_bvar_oob hv he hlen
      · split at he <;> have hii := (Expr.bvar.injEq ..).mp he <;>
          first | exact tyP_bvar_oob D rfl (by omega) | omega
  | .lsub _ _ _ (.sort ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.const ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.pi ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.lam ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.app ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.letE ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.lit ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .linst _ _ _ Γ' (.bvar i') _ ls _ _ D, he, hlen => by
      simp only [instantiateLevels] at he
      have hii := (Expr.bvar.injEq ..).mp he
      rw [← hii] at hlen
      simp only [instLvlsCtx, List.length_map] at hlen
      exact tyP_bvar_oob D rfl hlen
  | .linst _ _ _ _ (.sort ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.const ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.pi ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.lam ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.app ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.letE ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.lit ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .ewk _ _ _ _ _ _ _ D, he, hlen => tyP_bvar_oob D he hlen
  | .cctx _ _ _ _ _ _ _ _ D _, he, hlen => tyP_bvar_oob D he hlen
  termination_by D _ _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- The unguarded `wk`-inversion is refuted, on-cone: `Γ = []`, `c = 5`,
    `d = .assumption (.sort .zero)`, `e = .bvar 0`. `insertAt _ 5 [] = [d]`
    and `lift 5 1 (.bvar 0) = .bvar 0` definitionally, so
    `TyP.bvar` inhabits the premise while `bvar 0` is untypeable in `[]`
    (`tyP_bvar_oob`). -/
theorem tyPInvWkW_unguarded_unsat :
    ¬ (∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (d : LocalDecl) (c : Nat)
        {e T : Expr Nat},
        TyP E n (insertAt d c Γ) (lift c 1 e) T →
        ∃ (T' : Expr Nat), Nonempty (TyP E n Γ e T')) := by
  intro h
  obtain ⟨T', ⟨D'⟩⟩ :=
    h (Γ := []) (e := .bvar 0) (T := .sort .zero)
      (.assumption (.sort .zero)) 5
      (TyP.bvar emptyEnv 0 [.assumption (.sort .zero)] 0 (.sort .zero)
        (.succ .zero) rfl
        (TyP.sort emptyEnv 0 _ .zero (.succ .zero) (eqN_refl _)))
  exact tyP_bvar_oob D' rfl (Nat.zero_le _)

/-- `const r` forces `E.members r` inhabited — induction on the derivation
    (same `TyP.termFree_lt` shape, nested subject patterns — no in-body
    `cases` on `D`-dependent variables). Transports preserve the ref
    (`lift`/`instantiate` ignore const levels, `instantiateLevels` preserves
    `r`, `ewk` resolves through `EnvExt`). -/
theorem tyP_const_resolves {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {r : Nat} {ls : List Level} :
    (D : TyP E n Γ e T) → e = .const r ls → ∃ m : CheckedMember, E.members r = some m
  | .sort .., he => by simp only [reduceCtorEq] at he
  | .bvar .., he => by simp only [reduceCtorEq] at he
  | .const _ _ _ _ _ _ m _ hres _ _ _ _, he => by
      obtain ⟨hr, -⟩ := (Expr.const.injEq ..).mp he
      rw [← hr]
      exact ⟨m, hres⟩
  | .pi .., he => by simp only [reduceCtorEq] at he
  | .lam .., he => by simp only [reduceCtorEq] at he
  | .app .., he => by simp only [reduceCtorEq] at he
  | .letE .., he => by simp only [reduceCtorEq] at he
  | .lit .., he => by simp only [reduceCtorEq] at he
  | .conv _ _ _ _ _ _ _ h _, he => tyP_const_resolves h he
  | .wk _ _ _ (.bvar _) _ _ _ D, he => by
      simp only [lift] at he
      split at he <;> simp only [reduceCtorEq] at he
  | .wk _ _ _ (.const r' ms') _ _ _ D, he => by
      simp only [lift] at he
      obtain ⟨hr, -⟩ := (Expr.const.injEq ..).mp he
      rw [← hr]; exact tyP_const_resolves D rfl
  | .wk _ _ _ (.sort ..) _ _ _ _, he => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.pi ..) _ _ _ _, he => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.lam ..) _ _ _ _, he => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.app ..) _ _ _ _, he => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.letE ..) _ _ _ _, he => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.lit ..) _ _ _ _, he => by simp only [lift, reduceCtorEq] at he
  | .esub _ _ _ (.bvar _) _ _ v j _ D _ hv _, he => by
      simp only [instantiate] at he
      split at he
      · exact tyP_const_resolves hv he
      · split at he <;> simp only [reduceCtorEq] at he
  | .esub _ _ _ (.const r' ms') _ _ _ _ _ D _ _ _, he => by
      simp only [instantiate] at he
      obtain ⟨hr, -⟩ := (Expr.const.injEq ..).mp he
      rw [← hr]; exact tyP_const_resolves D rfl
  | .esub _ _ _ (.sort ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.pi ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.lam ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.app ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.letE ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.lit ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.bvar _) _ _ v j _ D _ hv _, he => by
      simp only [instantiate] at he
      split at he
      · exact tyP_const_resolves hv he
      · split at he <;> simp only [reduceCtorEq] at he
  | .lsub _ _ _ (.const r' ms') _ _ _ _ _ D _ _ _, he => by
      simp only [instantiate] at he
      obtain ⟨hr, -⟩ := (Expr.const.injEq ..).mp he
      rw [← hr]; exact tyP_const_resolves D rfl
  | .lsub _ _ _ (.sort ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.pi ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.lam ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.app ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.letE ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.lit ..) .., he => by simp only [instantiate, reduceCtorEq] at he
  | .linst _ _ _ _ (.bvar _) _ _ _ _ _, he => by
      simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.const r' ms') _ _ _ _ D, he => by
      simp only [instantiateLevels] at he
      obtain ⟨hr, -⟩ := (Expr.const.injEq ..).mp he
      rw [← hr]; exact tyP_const_resolves D rfl
  | .linst _ _ _ _ (.sort ..) .., he => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.pi ..) .., he => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.lam ..) .., he => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.app ..) .., he => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.letE ..) .., he => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.lit ..) .., he => by simp only [instantiateLevels, reduceCtorEq] at he
  | .ewk _ _ _ _ _ _ hext D, he => by
      obtain ⟨m, hm⟩ := tyP_const_resolves D he
      exact ⟨m, hext r m hm⟩
  | .cctx _ _ _ _ _ _ _ _ D _, he => tyP_const_resolves D he
  termination_by D _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- The unguarded `ewk`-inversion is refuted: take `E₀ = emptyEnv`,
    `E = extendEnv emptyEnv 0 ⟨.axiomM, 0, .sort .zero, none⟩`,
    `e = .const 0 []` — resolution succeeds at `E` and cannot descend. -/
theorem tyPInvEwkW_unguarded_unsat :
    ¬ (∀ {E₀ E : ResolvedEnv} (_hext : EnvExt E₀ E) {n : Nat} {Γ : LCtx}
        {e T : Expr Nat}, TyP E n Γ e T →
        ∃ (T' : Expr Nat), Nonempty (TyP E₀ n Γ e T')) := by
  intro h
  obtain ⟨T', ⟨D'⟩⟩ :=
    h (envExt_extendEnv (E := emptyEnv) (r := 0)
        ⟨.axiomM, 0, .sort .zero, none⟩ rfl)
      (TyP.const (extendEnv emptyEnv 0 ⟨.axiomM, 0, .sort .zero, none⟩)
        0 [] 0 [] [] ⟨.axiomM, 0, .sort .zero, none⟩ (.succ .zero)
        rfl rfl rfl (eqNList_refl [])
        (TyP.sort _ 0 [] .zero (.succ .zero) (eqN_refl _)))
  obtain ⟨m, hm⟩ := tyP_const_resolves D' rfl
  exact Option.noConfusion hm

/-- `levelBounded` on a level parameter is exactly the bound. -/
theorem levelBounded_param {k i : Nat} (h : levelBounded k (.param i) = true) :
    i < k := by
  simp only [levelBounded, decide_eq_true_eq] at h; exact h

/-- `levelsBounded` distributes over membership. -/
theorem levelsBounded_mem {k : Nat} {ls : List Level}
    (h : levelsBounded k ls = true) :
    ∀ {l : Level}, l ∈ ls → levelBounded k l = true := by
  induction ls with
  | nil => intro l hm; cases hm
  | cons l₀ t ih =>
      simp only [levelsBounded, Bool.and_eq_true] at h
      intro l hm
      rcases List.mem_cons.mp hm with rfl | hl
      · exact h.1
      · exact ih h.2 hl

/-- A `const r` subject's level parameters are bounded by the derivation's
    arity — induction (same `TyP.termFree_lt` shape, nested subject
    patterns); the `linst` arm discharges through `levelsBounded` of the
    instantiation list (the out-of-range `getD` branch is vacuous). -/
theorem tyP_const_param_lt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {r : Nat} {ls : List Level} {k : Nat} :
    (D : TyP E n Γ e T) → e = .const r ls → .param k ∈ ls → k < n
  | .sort .., he, _ => by simp only [reduceCtorEq] at he
  | .bvar .., he, _ => by simp only [reduceCtorEq] at he
  | .const _ _ _ _ ls' _ _ _ _ _ hwf _ _, he, hmem => by
      obtain ⟨-, hml⟩ := (Expr.const.injEq ..).mp he
      rw [← hml] at hmem
      exact levelBounded_param (levelsBounded_mem hwf hmem)
  | .pi .., he, _ => by simp only [reduceCtorEq] at he
  | .lam .., he, _ => by simp only [reduceCtorEq] at he
  | .app .., he, _ => by simp only [reduceCtorEq] at he
  | .letE .., he, _ => by simp only [reduceCtorEq] at he
  | .lit .., he, _ => by simp only [reduceCtorEq] at he
  | .conv _ _ _ _ _ _ _ h _, he, hmem => tyP_const_param_lt h he hmem
  | .wk _ _ _ (.bvar _) _ _ _ D, he, hmem => by
      simp only [lift] at he
      split at he <;> simp only [reduceCtorEq] at he
  | .wk _ _ _ (.const r' ms') _ _ _ D, he, hmem => by
      simp only [lift] at he
      obtain ⟨-, hml⟩ := (Expr.const.injEq ..).mp he
      rw [← hml] at hmem; exact tyP_const_param_lt D rfl hmem
  | .wk _ _ _ (.sort ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.pi ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.lam ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.app ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.letE ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .wk _ _ _ (.lit ..) _ _ _ _, he, _ => by simp only [lift, reduceCtorEq] at he
  | .esub _ _ _ (.bvar _) _ _ v j _ D _ hv _, he, hmem => by
      simp only [instantiate] at he
      split at he
      · exact tyP_const_param_lt hv he hmem
      · split at he <;> simp only [reduceCtorEq] at he
  | .esub _ _ _ (.const r' ms') _ _ _ _ _ D _ _ _, he, hmem => by
      simp only [instantiate] at he
      obtain ⟨-, hml⟩ := (Expr.const.injEq ..).mp he
      rw [← hml] at hmem; exact tyP_const_param_lt D rfl hmem
  | .esub _ _ _ (.sort ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.pi ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.lam ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.app ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.letE ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .esub _ _ _ (.lit ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.bvar _) _ _ v j _ D _ hv _, he, hmem => by
      simp only [instantiate] at he
      split at he
      · exact tyP_const_param_lt hv he hmem
      · split at he <;> simp only [reduceCtorEq] at he
  | .lsub _ _ _ (.const r' ms') _ _ _ _ _ D _ _ _, he, hmem => by
      simp only [instantiate] at he
      obtain ⟨-, hml⟩ := (Expr.const.injEq ..).mp he
      rw [← hml] at hmem; exact tyP_const_param_lt D rfl hmem
  | .lsub _ _ _ (.sort ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.pi ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.lam ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.app ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.letE ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .lsub _ _ _ (.lit ..) .., he, _ => by simp only [instantiate, reduceCtorEq] at he
  | .linst _ a' _ Γ' (.bvar _) _ _ _ _ _, he, hmem => by
      simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ a' _ Γ' (.const r' ms) _ ls' hls hlen0 D, he, hmem => by
      simp only [instantiateLevels] at he
      obtain ⟨-, hml⟩ := (Expr.const.injEq ..).mp he
      rw [← hml] at hmem
      rcases List.mem_map.mp hmem with ⟨m', hm'm, hmeq⟩
      cases m' with
      | param k' =>
          simp only [instLevel, lvlSubst, levelParamSubst] at hmeq
          cases hget : ls'[k']? with
          | some l' =>
              try rw [hget] at hmeq
              have hlk : l' = .param k := hmeq
              exact levelBounded_param
                (hlk ▸ levelsBounded_mem hls (List.getElem?_mem hget))
          | none =>
              have hklt : k' < a' := tyP_const_param_lt D rfl hm'm
              have hkge : a' ≤ k' := hlen0 ▸ List.getElem?_eq_none_iff.mp hget
              omega
      | zero => simp only [instLevel, lvlSubst, reduceCtorEq] at hmeq
      | succ l => simp only [instLevel, lvlSubst, reduceCtorEq] at hmeq
      | max a b => simp only [instLevel, lvlSubst, reduceCtorEq] at hmeq
      | imax a b => simp only [instLevel, lvlSubst, reduceCtorEq] at hmeq
  | .linst _ _ _ _ (.sort ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.pi ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.lam ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.app ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.letE ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .linst _ _ _ _ (.lit ..) .., he, _ => by simp only [instantiateLevels, reduceCtorEq] at he
  | .ewk _ _ _ _ _ _ _ D, he, hmem => tyP_const_param_lt D he hmem
  | .cctx _ _ _ _ _ _ _ _ D _, he, hmem => tyP_const_param_lt D he hmem
  termination_by D _ _ => sizeOf D
  decreasing_by all_goals (simp; omega)

/-- The unguarded `linst`-inversion is refuted: `ls = []`, `n = 1`, `a' = 0`,
    `e = .const 0 [.param 0]` — `.param 0` is legal at arity `1`, illegal at
    arity `0` (`tyP_const_param_lt`). -/
theorem tyPInvLinstW_unguarded_unsat :
    ¬ (∀ {E : ResolvedEnv} {n a' : Nat} {Γ : LCtx} (ls : List Level)
        (_hls : levelsBounded n ls = true) (_hlen : ls.length = a')
        {e T : Expr Nat},
        TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls e) T →
        ∃ (T' : Expr Nat), Nonempty (TyP E a' Γ e T')) := by
  intro h
  obtain ⟨T', ⟨D'⟩⟩ :=
    h (n := 1) (a' := 0) (Γ := []) (e := .const 0 [.param 0])
      (T := .sort .zero) [] rfl rfl
      (TyP.const (extendEnv emptyEnv 0 ⟨.axiomM, 1, .sort .zero, none⟩)
        1 [] 0 [.param 0] [.param 0]
        ⟨.axiomM, 1, .sort .zero, none⟩ (.succ .zero)
        rfl rfl rfl (eqNList_refl _)
        (TyP.sort _ 1 [] .zero (.succ .zero) (eqN_refl _)))
  exact absurd (tyP_const_param_lt D' rfl (by simp)) (Nat.lt_irrefl _)

/-! ## §5 the guarded restatements — the consumable boundaries -/

/-- `wk`-inversion, guarded: in-range insertion only (`insertAt`'s
    over-length clamp makes the unguarded form refutable — §4). -/
def TyPInvWkGW : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (d : LocalDecl) (c : Nat)
    (_hc : c ≤ Γ.length) {e T : Expr Nat},
    TyP E n (insertAt d c Γ) (lift c 1 e) T →
    ∃ (T' : Expr Nat), Nonempty (TyP E n Γ e T')

/-- `linst`-inversion, guarded: the descended subject's level parameters
    must fit the target arity (`tyP_const_param_lt` shows a subject-typed
    proof supplies them; the guard states the consumed shape directly). -/
def TyPInvLinstGW : Prop :=
  ∀ {E : ResolvedEnv} {n a' : Nat} {Γ : LCtx} (ls : List Level)
    (_hls : levelsBounded n ls = true) (_hlen : ls.length = a')
    {e T : Expr Nat}, exprLevelsBounded a' e = true →
    TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls e) T →
    ∃ (T' : Expr Nat), Nonempty (TyP E a' Γ e T')

/-- `ewk`-inversion, guarded: `hasTyT_strengthen`-shaped — the subject and
    context's constants stay below `k`, and the extension agrees with the
    source below `k` (`envExt_extendEnv` fills holes, which the unguarded
    form cannot survive — §4). -/
def TyPInvEwkGW : Prop :=
  ∀ {E₀ E : ResolvedEnv} (_hext : EnvExt E₀ E) {k n : Nat} {Γ : LCtx}
    {e T : Expr Nat},
    EnvAgreeBelow E₀ E k → Rcic.Scm.SrcG.constsBelow k e = true →
    ctxConstsBelow k Γ = true →
    TyP E n Γ e T → ∃ (T' : Expr Nat), Nonempty (TyP E₀ n Γ e T')

/-- The head-slot unwinding from the guarded `wk`-inversion
    (`0 ≤ Γ.length` discharges the guard). -/
theorem zetaSlotHeadUnwkW_of_invWkG (h : TyPInvWkGW) : ZetaSlotHeadUnwkW := by
  intro E n Γ d e T D
  exact h d 0 (Nat.zero_le _) D

/-- `TyPInvWkGW` on-cone — same pin as §3 plus the `0 ≤ 0` guard. -/
theorem tyPInvWkGW_onCone :
    ∃ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (d : LocalDecl) (c : Nat)
      (_ : c ≤ Γ.length) (e T : Expr Nat)
      (_ : TyP E n (insertAt d c Γ) (lift c 1 e) T),
      ∃ (T' : Expr Nat), Nonempty (TyP E n Γ e T') :=
  ⟨emptyEnv, 0, [], .assumption (.sort .zero), 0, Nat.zero_le _,
    .sort .zero, .sort (.succ .zero),
    TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    ⟨TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)⟩⟩

/-- `TyPInvLinstGW` on-cone — `ls = []`, `e = .sort .zero`:
    `exprLevelsBounded` on a sort is `rfl`-true. -/
theorem tyPInvLinstGW_onCone :
    ∃ (E : ResolvedEnv) (n a' : Nat) (Γ : LCtx) (ls : List Level)
      (_ : levelsBounded n ls = true) (_ : ls.length = a')
      (e T : Expr Nat) (_ : exprLevelsBounded a' e = true)
      (_ : TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls e) T),
      ∃ (T' : Expr Nat), Nonempty (TyP E a' Γ e T') :=
  ⟨emptyEnv, 0, 0, [.assumption (.sort .zero)], [], rfl, rfl,
    .sort .zero, .sort (.succ .zero), rfl,
    TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    ⟨TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _)⟩⟩

/-- `TyPInvEwkGW` on-cone — diagonal `envExt_refl`, `k = 0`:
    no constants below `0` to check. -/
theorem tyPInvEwkGW_onCone :
    ∃ (E₀ E : ResolvedEnv) (_ : EnvExt E₀ E) (k n : Nat) (Γ : LCtx)
      (e T : Expr Nat) (_ : EnvAgreeBelow E₀ E k)
      (_ : Rcic.Scm.SrcG.constsBelow k e = true) (_ : ctxConstsBelow k Γ = true)
      (_ : TyP E n Γ e T),
      ∃ (T' : Expr Nat), Nonempty (TyP E₀ n Γ e T') :=
  ⟨emptyEnv, emptyEnv, envExt_refl emptyEnv, 0, 0,
    [.assumption (.sort .zero)], .sort .zero, .sort (.succ .zero),
    EnvAgreeBelow.refl _ _, rfl, rfl,
    TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _),
    .sort (.succ .zero),
    ⟨TyP.sort emptyEnv 0 [_] .zero (.succ .zero) (eqN_refl _)⟩⟩

#print axioms Rcic.Syn.TyPInvWkW
#print axioms Rcic.Syn.TyPInvEsubW
#print axioms Rcic.Syn.TyPInvLinstW
#print axioms Rcic.Syn.TyPInvEwkW
#print axioms Rcic.Syn.zetaSlotHeadUnwkW_of_invWk
#print axioms Rcic.Syn.zetaSlotWkArmW_of_align
#print axioms Rcic.Syn.zetaSlotEsubArmW_of_align
#print axioms Rcic.Syn.zetaSlotLinstArmW_of_align
#print axioms Rcic.Syn.zetaSlotEwkArmW_of_align
#print axioms Rcic.Syn.tyPInvWkW_onCone
#print axioms Rcic.Syn.tyPInvEsubW_onCone
#print axioms Rcic.Syn.tyPInvLinstW_onCone
#print axioms Rcic.Syn.tyPInvEwkW_onCone
#print axioms Rcic.Syn.tyP_bvar_oob
#print axioms Rcic.Syn.tyPInvWkW_unguarded_unsat
#print axioms Rcic.Syn.tyP_const_resolves
#print axioms Rcic.Syn.tyPInvEwkW_unguarded_unsat
#print axioms Rcic.Syn.levelBounded_param
#print axioms Rcic.Syn.levelsBounded_mem
#print axioms Rcic.Syn.tyP_const_param_lt
#print axioms Rcic.Syn.tyPInvLinstW_unguarded_unsat
#print axioms Rcic.Syn.TyPInvWkGW
#print axioms Rcic.Syn.TyPInvLinstGW
#print axioms Rcic.Syn.TyPInvEwkGW
#print axioms Rcic.Syn.zetaSlotHeadUnwkW_of_invWkG
#print axioms Rcic.Syn.tyPInvWkGW_onCone
#print axioms Rcic.Syn.tyPInvLinstGW_onCone
#print axioms Rcic.Syn.tyPInvEwkGW_onCone
