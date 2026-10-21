import rcic.RcicSynLetRight

/-!
# Wall 2 (changed-declaration letRight), step 7 — prepayment

`research/rcic/sortrow/BELOWC_SEMANTIC_WALLS.md` Part III, "Prepayment".

While the let node's atom `N = wt C` is live, the port family is built: `letValueES`,
`letValuePBLeft`, `letValuePBRight`, the per-site `replacementPB`, the per-bvar
`slotBaseBit` / `chainJunctionBit` / `chainEndBit` / `replacementBaseBit`, and
`rightSurfaceMixedCL`. The family is finite — it follows the original tree and its encountered
stacks (`bodyRequestAtoms` walks the tree once, no successful-read filter) — and every new atom
is an atom of a suboccurrence of the original let fields: the value conversion and its
endpoints, the domain's left endpoint, the body's right endpoint and its sub-typings
(providers at bvar sites, replacement formations at `esub` / `lsub` sites, bridges at `cctx`
sites), and the right endpoint `dr` with the recipe's components. Hence every atom is `< N`
and `K ++ [N] >DM K ++ S` (`letBridge_prepaid`). The native weights of `U`, `H'`, `D'` are
never claimed below `N`: the bounded operand is the explicit recipe.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the body's request atoms -/

/-- The atoms the body's answers read, one pass over the original tree: the provider `hA` at
    every `bvar` (slot base / junctions / end / replacement base), the replacement formation
    `hv`, `hvT` at every `esub` / `lsub` (replacement `PB`, and the recursion into `hv`), and
    the bridge `hA` at every `cctx` (junction endpoints). -/
def bodyRequestAtoms (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP E n Γ e T → List Nat
  | _, _, _, _, _, .sort .. => []
  | _, _, _, _, _, .bvar _ _ _ _ _ _ _ hA => hA.atoms Aw
  | _, _, _, _, _, .const .. => []
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => bodyRequestAtoms Aw hA ++ bodyRequestAtoms Aw hB
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hbody _ => bodyRequestAtoms Aw hbody
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _ => bodyRequestAtoms Aw hf ++ bodyRequestAtoms Aw ha
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ hv hb _ => bodyRequestAtoms Aw hv ++ bodyRequestAtoms Aw hb
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => bodyRequestAtoms Aw hexp
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _ => bodyRequestAtoms Aw h
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => bodyRequestAtoms Aw D
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv hvT =>
      hv.atoms Aw ++ hvT.atoms Aw ++ bodyRequestAtoms Aw hv ++ bodyRequestAtoms Aw D
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv hvT =>
      hv.atoms Aw ++ hvT.atoms Aw ++ bodyRequestAtoms Aw hv ++ bodyRequestAtoms Aw D
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => bodyRequestAtoms Aw D
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => bodyRequestAtoms Aw D
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA => bodyRequestAtoms Aw D ++ hA.atoms Aw

/-- Every request atom of the body is at most the body's weight: each is an atom of a
    sub-typing, and weights are monotone along the tree. -/
theorem bodyRequestAtoms_le (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → (D : TyP E n Γ e T) → ∀ y ∈ bodyRequestAtoms Aw D, y ≤ D.wt Aw
  | _, _, _, _, _, .sort .., _, hy => by simp [bodyRequestAtoms] at hy
  | _, _, _, _, _, .bvar _ _ _ _ _ _ _ hA, y, hy => by
      simp only [bodyRequestAtoms] at hy
      have := TyP.atoms_le Aw hA y hy
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .const .., _, hy => by simp [bodyRequestAtoms] at hy
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, y, hy => by
      simp only [bodyRequestAtoms, List.mem_append] at hy
      simp only [TyP.wt]
      rcases hy with hy | hy
      · have := bodyRequestAtoms_le Aw hA y hy; omega
      · have := bodyRequestAtoms_le Aw hB y hy; omega
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hbody _, y, hy => by
      simp only [bodyRequestAtoms] at hy
      have := bodyRequestAtoms_le Aw hbody y hy
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _, y, hy => by
      simp only [bodyRequestAtoms, List.mem_append] at hy
      simp only [TyP.wt]
      rcases hy with hy | hy
      · have := bodyRequestAtoms_le Aw hf y hy; omega
      · have := bodyRequestAtoms_le Aw ha y hy; omega
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ hv hb _, y, hy => by
      simp only [bodyRequestAtoms, List.mem_append] at hy
      simp only [TyP.wt]
      rcases hy with hy | hy
      · have := bodyRequestAtoms_le Aw hv y hy; omega
      · have := bodyRequestAtoms_le Aw hb y hy; omega
  | _, _, _, _, _, .lit _ _ _ _ _ hexp, y, hy => by
      simp only [bodyRequestAtoms] at hy
      have := bodyRequestAtoms_le Aw hexp y hy
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, y, hy => by
      simp only [bodyRequestAtoms] at hy
      have := bodyRequestAtoms_le Aw h y hy
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D, y, hy => by
      simp only [bodyRequestAtoms] at hy
      have := bodyRequestAtoms_le Aw D y hy
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv hvT, y, hy => by
      simp only [bodyRequestAtoms, List.mem_append] at hy
      simp only [TyP.wt]
      rcases hy with ((hy | hy) | hy) | hy
      · have := TyP.atoms_le Aw hv y hy; omega
      · have := TyP.atoms_le Aw hvT y hy; omega
      · have := bodyRequestAtoms_le Aw hv y hy; omega
      · have := bodyRequestAtoms_le Aw D y hy; omega
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv hvT, y, hy => by
      simp only [bodyRequestAtoms, List.mem_append] at hy
      simp only [TyP.wt]
      rcases hy with ((hy | hy) | hy) | hy
      · have := TyP.atoms_le Aw hv y hy; omega
      · have := TyP.atoms_le Aw hvT y hy; omega
      · have := bodyRequestAtoms_le Aw hv y hy; omega
      · have := bodyRequestAtoms_le Aw D y hy; omega
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D, y, hy => by
      simp only [bodyRequestAtoms] at hy
      have := bodyRequestAtoms_le Aw D y hy
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, y, hy => by
      simp only [bodyRequestAtoms] at hy
      have := bodyRequestAtoms_le Aw D y hy
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA, y, hy => by
      simp only [bodyRequestAtoms, List.mem_append] at hy
      simp only [TyP.wt]
      rcases hy with hy | hy
      · have := bodyRequestAtoms_le Aw D y hy; omega
      · have := CvP.atoms_le Aw hA y hy; omega

/-! ## §2 the port family of the let node -/

/-- The atoms of the whole port family: the value answers (`hv`'s atoms and its endpoints
    against `hA.dl`), the body's requests, and the right-surface MixedCL's operands (`dr` and
    the recipe's components `hA.dr`, `hv.dr`, `hb.dr`). -/
def letBridgeRequestAtoms (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)) : List Nat :=
  hv.atoms Aw ++ hv.dl.atoms Aw ++ hA.dl.atoms Aw ++ hv.dr.atoms Aw ++
    bodyRequestAtoms Aw hb.dr ++
    dr.atoms Aw ++ hA.dr.atoms Aw ++ hv.dr.atoms Aw ++ hb.dr.atoms Aw

/-- Every atom of the family is a suboccurrence of the original let fields, hence `< N`. -/
theorem letBridgeRequestAtoms_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)) :
    ∀ y ∈ letBridgeRequestAtoms Aw hA hv hb dr,
      y < (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr).wt Aw := by
  intro y hy
  simp only [letBridgeRequestAtoms, List.mem_append] at hy
  simp only [CvP.wt]
  have h1 := CvP.wt_dl_lt Aw hv
  have h2 := CvP.wt_dr_lt Aw hv
  have h3 := CvP.wt_dl_lt Aw hA
  have h4 := CvP.wt_dr_lt Aw hA
  have h5 := CvP.wt_dr_lt Aw hb
  rcases hy with (((((((hy | hy) | hy) | hy) | hy) | hy) | hy) | hy) | hy
  · have := CvP.atoms_le Aw hv y hy; omega
  · have := TyP.atoms_le Aw hv.dl y hy; omega
  · have := TyP.atoms_le Aw hA.dl y hy; omega
  · have := TyP.atoms_le Aw hv.dr y hy; omega
  · have := bodyRequestAtoms_le Aw hb.dr y hy; omega
  · have := TyP.atoms_le Aw dr y hy; omega
  · have := TyP.atoms_le Aw hA.dr y hy; omega
  · have := TyP.atoms_le Aw hv.dr y hy; omega
  · have := TyP.atoms_le Aw hb.dr y hy; omega

/-- `K ++ [N] >DM K ++ S` when every atom of `S` is below `N`. -/
theorem dmStep_append_below {N : Nat} {S K : List Nat} (h : ∀ y ∈ S, y < N) :
    DMStep (K ++ S) (K ++ [N]) :=
  ⟨[N], S, K, List.cons_ne_nil _ _, List.perm_append_comm,
    List.perm_append_comm, fun y hy => ⟨N, List.mem_cons_self _ _, h y hy⟩⟩

/-- The DM edge of the planned port family: `K ++ S_q < K ++ [N]`, for every retained ledger
    `K` (no bound on `K`, no sum-of-atoms claim). -/
theorem letBridge_prepaid (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)) (K : List Nat) :
    DMStep (K ++ letBridgeRequestAtoms Aw hA hv hb dr)
      (K ++ [(CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr).wt Aw]) :=
  dmStep_append_below (letBridgeRequestAtoms_lt Aw hA hv hb dl dr)

end Rcic.Syn

#print axioms Rcic.Syn.bodyRequestAtoms_le
#print axioms Rcic.Syn.letBridgeRequestAtoms_lt
#print axioms Rcic.Syn.dmStep_append_below
#print axioms Rcic.Syn.letBridge_prepaid
