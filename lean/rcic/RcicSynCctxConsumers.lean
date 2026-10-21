import rcic.RcicSynRegStep

/-!
# Syntactic sortRow, build step S6-§4 — the two general-`cctx` consumers

`research/rcic/sortrow/S6_MIXED_TRANSPORT_STEPS.md` §4. The original right node is
`TyP.cctx E n Γ₀ e T A A' u D c` with `D : TyP E n (.assumption A :: Γ₀) e T`,
`c : CvP E n Γ₀ A A' (.sort u)`, and the target context decomposition
`Ct = .assumption C₀ J`, `J : TyP E n Γ₀ A' (.sort uJ)`. The producer issues two
independent bounded subqueries, both paid by the original `c` — never by copying
it (`closure_claim = 0`, no `isTransport = false` premise anywhere):

* **the gate call** (`bitCoh_cctx_gate`): `BitCoh σ J c.dr` in the real tail
  context Γ₀, giving `levelIsZero (σ uJ) = levelIsZero (σ u)`. Multiset edge
  `dmStep_cctx_gate`: `K ++ at(J) ++ at(D) ++ at(c)` → the `tyPairMeas J c.dr`
  pair, using `dmStep_cvp_dr` on `c` and dropping `D`.
* **the source-body call**: build `Cs = .assumption C₀ c.dl`
  (`cctxSourceCtx`), align the target binder disposition
  `binderDisp (levelIsZero (σ uJ))` with the source binder's by the gate's bit
  equation (`dispFor_cctx_source`), then recurse into `D`. Multiset edge
  `dmStep_cctx_body`: `K ++ at(c)` → `K ++ at(c.dl)` via `dmStep_cvp_dl`; the
  pair-call leg `lexDM_cctx_body_pair` keeps `at(D) ++ at(X)` inside `K` and
  pays by `c`'s original atoms.

`K` is a generic kept-occurrence list — `CtxP` carries no atom list, so `at(C₀)`
and any other still-live original fields are absorbed into it. Both edges
*consume* the owner theorems `dmStep_cvp_dl`/`dmStep_cvp_dr`, which cover all 24
`CvP` constructors; nothing is re-proved.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the source context and its aligned disposition -/

/-- `Cs = .assumption C₀ c.dl`: the source-side `CtxP` of the body call — the
    original tail `C₀` with the binder typed by `c`'s left endpoint. -/
def cctxSourceCtx {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A A' : Expr Nat} {u : Level}
    (C₀ : CtxP E n Γ₀) (c : CvP E n Γ₀ A A' (.sort u)) :
    CtxP E n (.assumption A :: Γ₀) :=
  .assumption _ _ _ _ _ C₀ c.dl

/-- The target binder's disposition `binderDisp (levelIsZero (σ uJ))` realized at
    the source context: `dispFor_binderDisp` on `c.dl` gives it at `σ u`, and the
    gate's bit equation `levelIsZero (σ uJ) = levelIsZero (σ u)` aligns them. -/
theorem dispFor_cctx_source {σ : Level → Level} {ρ : List Disp}
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A A' : Expr Nat} {u uJ : Level}
    (hρ : DispFor σ E n Γ₀ ρ) (c : CvP E n Γ₀ A A' (.sort u))
    (hbit : levelIsZero (σ uJ) = levelIsZero (σ u)) :
    DispFor σ E n (.assumption A :: Γ₀) (binderDisp (levelIsZero (σ uJ)) :: ρ) := by
  rw [hbit]
  exact dispFor_binderDisp hρ c.dl

/-! ## §2 consumer 1 — the gate call `BitCoh σ J c.dr` -/

/-- The gate edge: `at(J) ++ at(c.dr)` is a `DMStep` below the caller's
    `K ++ at(J) ++ at(D) ++ at(c)` — `dmStep_cvp_dr` on `c`, `D` dropped, `J` and
    the kept table `K` preserved. -/
theorem dmStep_cctx_gate (Aw : Nat → Nat) (K : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T A A' : Expr Nat} {u uJ : Level}
    (J : TyP E n Γ₀ A' (.sort uJ)) (D : TyP E n (.assumption A :: Γ₀) e T)
    (c : CvP E n Γ₀ A A' (.sort u)) :
    DMStep (J.atoms Aw ++ c.dr.atoms Aw)
      (K ++ J.atoms Aw ++ D.atoms Aw ++ c.atoms Aw) :=
  dmStep_perm_right (by
      rw [← List.append_assoc, ← List.append_assoc])
    (dmStep_drop_left
      (dmStep_append_left (dmStep_drop_left (dmStep_cvp_dr Aw c) (D.atoms Aw))
        (J.atoms Aw))
      K)

/-- The gate call at `tyPairMeas`: `LexDM (tyPairMeas Aw J c.dr) bound` for the
    caller bound `(K ++ at(J) ++ at(D) ++ at(c), w)`. -/
theorem lexDM_cctx_gate (Aw : Nat → Nat) (K : List Nat) (w : Nat)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T A A' : Expr Nat} {u uJ : Level}
    (J : TyP E n Γ₀ A' (.sort uJ)) (D : TyP E n (.assumption A :: Γ₀) e T)
    (c : CvP E n Γ₀ A A' (.sort u)) :
    LexDM (tyPairMeas Aw J c.dr) (K ++ J.atoms Aw ++ D.atoms Aw ++ c.atoms Aw, w) :=
  lex_of_dm (dmStep_cctx_gate Aw K J D c)

/-- Consumer 1: `B.bitCoh J c.dr` — the binder sort-bits agree under `σ`. -/
theorem bitCoh_cctx_gate (Aw : Nat → Nat) (tbl : List CRule) (K : List Nat) (w : Nat)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T A A' : Expr Nat} {u uJ : Level}
    {σ : Level → Level} {ρ : List Disp}
    (J : TyP E n Γ₀ A' (.sort uJ)) (D : TyP E n (.assumption A :: Γ₀) e T)
    (c : CvP E n Γ₀ A A' (.sort u))
    (hρ : DispFor σ E n Γ₀ ρ)
    (B : Below Aw tbl (K ++ J.atoms Aw ++ D.atoms Aw ++ c.atoms Aw, w)) :
    levelIsZero (σ uJ) = levelIsZero (σ u) :=
  B.bitCoh J c.dr σ ρ hρ (lexDM_cctx_gate Aw K w J D c)

/-! ## §3 consumer 2 — the source-body call -/

/-- The body edge: `K ++ at(c.dl)` is a `DMStep` below `K ++ at(c)` —
    `dmStep_cvp_dl` on `c`, the kept table `K` preserved on both sides. -/
theorem dmStep_cctx_body (Aw : Nat → Nat) (K : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A A' : Expr Nat} {u : Level}
    (c : CvP E n Γ₀ A A' (.sort u)) :
    DMStep (K ++ c.dl.atoms Aw) (K ++ c.atoms Aw) :=
  dmStep_append_left (dmStep_cvp_dl Aw c) K

/-- The body edge at `LexDM`: the callee's kept table `(K ++ at(c.dl), w')` is
    below the caller's `(K ++ at(c), w)` at any second coordinate. -/
theorem lexDM_cctx_body (Aw : Nat → Nat) (K : List Nat) (w w' : Nat)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A A' : Expr Nat} {u : Level}
    (c : CvP E n Γ₀ A A' (.sort u)) :
    LexDM (K ++ c.dl.atoms Aw, w') (K ++ c.atoms Aw, w) :=
  lex_of_dm (dmStep_cctx_body Aw K c)

/-- The body leg as a `Below` pair call on `(D, X)`: the caller bound lists
    `at(D)`, `at(X)` and `at(c)` after the kept prefix `K`; the callee's own pair
    `at(D) ++ at(X)` is dominated by the `K ++ at(c)` part it replaces — `c`'s
    atoms are never copied onto both sides. -/
theorem lexDM_cctx_body_pair (Aw : Nat → Nat) (K : List Nat) (w : Nat)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A A' : Expr Nat} {u : Level}
    {e T : Expr Nat} {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e' T' : Expr Nat}
    (D : TyP E n (.assumption A :: Γ₀) e T) (X : TyP E' n' Γ' e' T')
    (c : CvP E n Γ₀ A A' (.sort u)) :
    LexDM (tyPairMeas Aw D X)
      (K ++ (D.atoms Aw ++ X.atoms Aw) ++ c.atoms Aw, w) := by
  have hne : K ++ c.atoms Aw ≠ [] :=
    fun hnil => CvP.atoms_ne_nil Aw c (List.append_eq_nil.mp hnil).2
  have hdrop : DMStep (D.atoms Aw ++ X.atoms Aw)
      ((K ++ c.atoms Aw) ++ (D.atoms Aw ++ X.atoms Aw)) :=
    dmStep_drop hne
  have hp : ((K ++ c.atoms Aw) ++ (D.atoms Aw ++ X.atoms Aw)).Perm
      (K ++ (D.atoms Aw ++ X.atoms Aw) ++ c.atoms Aw) := by
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left K List.perm_append_comm
  exact lex_of_dm (dmStep_perm_right hp hdrop)

/-- The two §4.2 subqueries of a `TyP.cctx D c` node at `Ct = .assumption C₀ J`,
    packaged: the gate's bit equation and the source-context disposition for the
    body recursion into `D`. -/
structure CctxConsumers (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T A A' : Expr Nat} {u uJ : Level}
    (_C₀ : CtxP E n Γ₀) (J : TyP E n Γ₀ A' (.sort uJ))
    (D : TyP E n (.assumption A :: Γ₀) e T) (c : CvP E n Γ₀ A A' (.sort u)) :
    Prop where
  /-- the gate answer: `levelIsZero (σ uJ) = levelIsZero (σ u)`. -/
  gate_bit : levelIsZero (σ uJ) = levelIsZero (σ u)
  /-- the source context's disposition, aligned to the target binder bit. -/
  source_disp : DispFor σ E n (.assumption A :: Γ₀)
    (binderDisp (levelIsZero (σ uJ)) :: ρ)

/-- Consumer bundle: from `Below` at the caller bound `K ++ at(J) ++ at(D) ++
    at(c)` produce both subquery answers — `B.bitCoh` for the gate, and the
    aligned source `DispFor` for the body. -/
theorem cctx_consumers (Aw : Nat → Nat) (tbl : List CRule) (K : List Nat) (w : Nat)
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {e T A A' : Expr Nat} {u uJ : Level}
    {σ : Level → Level} {ρ : List Disp}
    (C₀ : CtxP E n Γ₀) (J : TyP E n Γ₀ A' (.sort uJ))
    (D : TyP E n (.assumption A :: Γ₀) e T) (c : CvP E n Γ₀ A A' (.sort u))
    (hρ : DispFor σ E n Γ₀ ρ)
    (B : Below Aw tbl (K ++ J.atoms Aw ++ D.atoms Aw ++ c.atoms Aw, w)) :
    CctxConsumers σ ρ C₀ J D c :=
  ⟨bitCoh_cctx_gate Aw tbl K w J D c hρ B,
    dispFor_cctx_source hρ c (bitCoh_cctx_gate Aw tbl K w J D c hρ B)⟩

end Rcic.Syn
