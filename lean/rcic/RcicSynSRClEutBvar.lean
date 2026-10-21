import rcic.RcicSynSRClEutTransport
import rcic.RcicSynBvarEpsEsub

/-!
# `RcicSynSRClEutBvar` — the `esub`-collapsed-bvar arm, classified

cc 12:50Z item (`sortrow-uniq-as-ih`), `thsaLhom_lit_wall`:

**The exact instance.** The arm pairs a fixed endpoint
`X : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) (.bvar j)) T₁`
with the node's value derivation
`hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)` —
subjects equal only PROPOSITIONALLY (`instantiate_bvar_eq`); the
conversion-preserves-sort residual is `ConvMod (X.eps σ ρ) (hv₂.eps σ ρ)`
(`goal_cl_esub_bvar_keep` below pins it at the formable `.cl X esub`).

**Below the node? YES — kernel-checked.** `hv₂` is a strict subderivation:
its atom list is a strict dropped sub-multiset of the node's
(`lexDM_tyPair_esub_bvarR`/`_bvarL`; `hvT₂`/`D₂`'s atoms come out, `hv₂`'s
stay). The derivation-order half of the IH test passes.

**Issueable as an IH query? NO — kernel-checked unformable.** Every
`P2Query` constructor (`.cl`/`.eut`/`.bitCoh`/`.mixed`/`obsPair`) indexes
the pair by ONE syntactic subject `e`. `instantiate j (lift 0 j v)
(.bvar j)` does not reduce to `lift 0 j v` for VARIABLE `j` (`Nat.decEq j j`
is stuck), and `Eq.mpr`-casting through `instantiate_bvar_eq` wraps the
derivation in a stuck `Eq.rec`, which `TyP.atoms`/`TyP.eps`/`localKey`/
`AssumpPref` cannot traverse — no rank statement on a casted query is even
statable. `.es`/`.cts`/`.pb` carry different goals. So the instance is the
**inhabited on-cone boundary**: the residual `bvarCollapseCL` is real
semantic content with no query expression — `thsaLhom_lit_wall`'s named
residual keeps it. The drop arm (`levelIsZero (σ u) = true`) collapses the
node's erasure to `★` (`cl_esub_bvar_drop_eps`), the refutation shape.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the "below the node" half — strict subderivation, kernel-checked -/

/-- Right side: the payload and the kind source drop; the fixed endpoint and
    the value typing keep their places — `(p++s)++(x++v)` reorders to
    `x++(p++v++s)`. -/
theorem perm_cl_esub_bvarR (p v s x : List Nat) :
    ((p ++ s) ++ (x ++ v)).Perm (x ++ (p ++ v ++ s)) := by
  refine List.perm_append_comm.trans ?_
  rw [show (x ++ v) ++ (p ++ s) = x ++ v ++ p ++ s by
        simp only [List.append_assoc],
      show x ++ (p ++ v ++ s) = x ++ p ++ v ++ s by
        simp only [List.append_assoc],
      show x ++ v ++ p ++ s = x ++ ((v ++ p) ++ s) by
        simp only [List.append_assoc],
      show x ++ p ++ v ++ s = x ++ ((p ++ v) ++ s) by
        simp only [List.append_assoc]]
  exact List.Perm.append_left x (List.Perm.append_right s List.perm_append_comm)

/-- Left side: the payload and the kind source drop; the value typing and
    the fixed endpoint keep their places — `(p++s)++(v++x)` reorders to
    `(p++v++s)++x`. -/
theorem perm_cl_esub_bvarL (p v s x : List Nat) :
    ((p ++ s) ++ (v ++ x)).Perm ((p ++ v ++ s) ++ x) := by
  have h1 : (p ++ s ++ v ++ x).Perm (p ++ v ++ s ++ x) := by
    rw [show p ++ s ++ v ++ x = p ++ ((s ++ v) ++ x) by
          simp only [List.append_assoc],
        show p ++ v ++ s ++ x = p ++ ((v ++ s) ++ x) by
          simp only [List.append_assoc]]
    exact List.Perm.append_left p
      (List.Perm.append_right x List.perm_append_comm)
  rw [show (p ++ s) ++ (v ++ x) = p ++ s ++ v ++ x by
        simp only [List.append_assoc],
      show (p ++ v ++ s) ++ x = p ++ v ++ s ++ x by
        simp only [List.append_assoc]]
  exact h1

/-- The value derivation `hv₂` IS a strict subderivation of the
    `esub`-collapsed-bvar node, in the closer's own measure: the pair
    `(X, hv₂)` sits strictly below `(X, esub-node)` (`D₂`'s and `hvT₂`'s
    atoms come out of the multiset, `hv₂`'s stay). The "below" half of the
    IH test — what fails is expressibility, not depth. -/
theorem lexDM_tyPair_esub_bvarR (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (X : TyP E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.bvar j)) T₁)
    (D₂ : TyP E n Γ (.bvar j) A₂)
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    LexDM (tyPairMeas Aw X hv₂)
      (tyPairMeas Aw X
        (TyP.esub E n Γ (.bvar j) A₂ t v j u D₂ hget hv₂ hvT₂)) := by
  have hX : (D₂.atoms Aw ++ hvT₂.atoms Aw) ≠ [] :=
    fun h => TyP.atoms_ne_nil Aw D₂ (List.append_eq_nil.mp h).1
  simp only [tyPairMeas, TyP.atoms]
  exact Prod.Lex.left _ _
    (dmStep_perm_right
      (perm_cl_esub_bvarR (D₂.atoms Aw) (hv₂.atoms Aw) (hvT₂.atoms Aw)
        (X.atoms Aw))
      (dmStep_drop hX))

/-- Left-side mirror: `(hv₁, X)` sits strictly below `(esub-node, X)`. -/
theorem lexDM_tyPair_esub_bvarL (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₁ T₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (D₁ : TyP E n Γ (.bvar j) A₁)
    (hv₁ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₁ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (X : TyP E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.bvar j)) T₂) :
    LexDM (tyPairMeas Aw hv₁ X)
      (tyPairMeas Aw
        (TyP.esub E n Γ (.bvar j) A₁ t v j u D₁ hget hv₁ hvT₁) X) := by
  have hX : (D₁.atoms Aw ++ hvT₁.atoms Aw) ≠ [] :=
    fun h => TyP.atoms_ne_nil Aw D₁ (List.append_eq_nil.mp h).1
  simp only [tyPairMeas, TyP.atoms]
  exact Prod.Lex.left _ _
    (dmStep_perm_right
      (perm_cl_esub_bvarL (D₁.atoms Aw) (hv₁.atoms Aw) (hvT₁.atoms Aw)
        (X.atoms Aw))
      (dmStep_drop hX))

/-! ## §2 the exact residual, kernel-checked at the formable `.cl X esub` -/

/-- The keep arm's goal reduction: `P2Query.cl X esub` DOES form (both
    endpoints carry the stuck subject `instantiate j (lift 0 j v)
    (.bvar j)`), and its goal collapses to `ConvMod (X.eps σ ρ)
    (hv₂.eps σ ρ)` — the conversion-preserves-sort instance. The next step
    — issuing that pair as `.cl X hv₂` — is the unformable one: `hv₂`'s
    subject `lift 0 j v` is propositionally (`instantiate_bvar_eq`) but not
    syntactically the stuck `e`, and no `P2Query` constructor takes an
    equality witness. -/
theorem goal_cl_esub_bvar_keep {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {T₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (X : TyP E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.bvar j)) T₁)
    (D₂ : TyP E n Γ (.bvar j) A₂)
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = false) (hlen : j ≤ ρ.length)
    (hhole : D₂.eps σ (insertDisp .keep j ρ) =
      resolve (insertDisp .keep j ρ) j) :
    Goal tbl (P2Query.cl X
        (TyP.esub E n Γ (.bvar j) A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
      = ConvMod (EStep tbl) LvlEq (X.eps σ ρ) (hv₂.eps σ ρ) := by
  simp only [goal_cl_residual_unfold,
    eps_esub_hole_keep hu hlen hhole]

/-- The drop arm's goal reduction: same pair, `levelIsZero (σ u) = true` —
    the node erases to `★`, so the residual is `ConvMod (X.eps σ ρ) .star`.
    At the wall's endpoint (`X` erasing to `.const 1 []` under `LevelHom`)
    that is `not_convMod_star_const`-refutable — the boundary's refutation
    shape, inhabited iff the arm's `hvT` places `t` at a Prop sort. -/
theorem goal_cl_esub_bvar_drop {tbl : List CRule}
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {T₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    (X : TyP E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.bvar j)) T₁)
    (D₂ : TyP E n Γ (.bvar j) A₂)
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hu : levelIsZero (σ u) = true) (hlen : j ≤ ρ.length)
    (hhole : D₂.eps σ (insertDisp .drop j ρ) =
      resolve (insertDisp .drop j ρ) j) :
    Goal tbl (P2Query.cl X
        (TyP.esub E n Γ (.bvar j) A₂ t v j u D₂ hget hv₂ hvT₂) S σ ρ)
      = ConvMod (EStep tbl) LvlEq (X.eps σ ρ) .star := by
  simp only [goal_cl_residual_unfold,
    eps_esub_hole_drop hu hlen hhole]

/-! ## §3 the boundary, named -/

/-- **The named residual** of the `esub`-collapsed-bvar arm: the
    conversion-preserves-sort obligation `ConvMod (X.eps σ ρ) (hv₂.eps σ ρ)`
    between the fixed endpoint (subject `instantiate j (lift 0 j v)
    (.bvar j)`) and the value derivation (subject `lift 0 j v`). It is what
    `.cl X esub`'s keep arm reduces to, it is NOT expressible as any
    `P2Query` (subjects equal only by `instantiate_bvar_eq`, and
    `Eq.mpr`-casts break `atoms`/`eps`/`localKey`), so it is not an IH query
    — it is the inhabited on-cone boundary inside `thsaLhom_lit_wall`. -/
def bvarCollapseCL (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {T₁ A₂ t v : Expr Nat} {j : Nat} {u : Level}
    {_hget : Γ[j]? = some (.assumption t)}
    (X : TyP E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) (.bvar j)) T₁)
    (_D₂ : TyP E n Γ (.bvar j) A₂)
    (hv₂ : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (_hvT₂ : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (σ : Level → Level) (ρ : List Disp) : Prop :=
  ConvMod (EStep tbl) LvlEq (X.eps σ ρ) (hv₂.eps σ ρ)

/-- The drop arm's star collapse — the boundary's refutation shape. -/
theorem cl_esub_bvar_drop_eps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A t v : Expr Nat} {j : Nat} {u : Level}
    {hget : Γ[j]? = some (.assumption t)}
    {D : TyP E n Γ (.bvar j) A}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hu : levelIsZero (σ u) = true) (hlen : j ≤ ρ.length)
    (hhole : D.eps σ (insertDisp .drop j ρ) =
      resolve (insertDisp .drop j ρ) j) :
    (TyP.esub E n Γ (.bvar j) A t v j u D hget hv hvT).eps σ ρ = .star :=
  eps_esub_hole_drop hu hlen hhole

#print axioms Rcic.Syn.perm_cl_esub_bvarR
#print axioms Rcic.Syn.perm_cl_esub_bvarL
#print axioms Rcic.Syn.lexDM_tyPair_esub_bvarR
#print axioms Rcic.Syn.lexDM_tyPair_esub_bvarL
#print axioms Rcic.Syn.goal_cl_esub_bvar_keep
#print axioms Rcic.Syn.goal_cl_esub_bvar_drop
#print axioms Rcic.Syn.bvarCollapseCL
#print axioms Rcic.Syn.cl_esub_bvar_drop_eps
