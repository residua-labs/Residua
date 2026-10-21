import rcic.RcicSynSREqnIssue

/-!
# RcicSynSREqnTransport — row 14: the level-renaming transport, its fragment, its refuted gate

cc 2026-10-21 00:40Z brief, lane glm/sr4-eqn (#7809). Prescription: make the
const cell's two typings ONE subject by transporting `hT₂ : TyP E n Γ
(instantiateLevels ls₂ m.mtype) (.sort u₂)` to `hT₂'` at the `ls₁`-
instantiation with `eqN u₂' u₂` (structural, by induction on the derivation,
weight not larger), then fire `occ_bitCoh` on `hT₁ hT₂'` — the sortOne
mechanism at `ls₁ ≠ ls₂`. Measured, this module:

* **PROVED — the `{sort, pi}` fragment** (`SortPiFrag`,
  `tyP_sortPiFrag_transport`): for derivations built from `TyP.sort` and
  `TyP.pi` only, the transport holds gate-free at every `eqNList ls₁ ls₂`,
  context-parametric (an `ls₂`-instantiated pre-image `Δ` above an untouched
  base transports to the `ls₁`-image), universe `eqN`-related, weight not
  larger. Covers the level-polymorphic universe-tree member types
  (`.sort (.param i)`, `.pi … (.sort (.param j))` — the common `Type`-valued
  member shapes), where the two subjects differ only in the substituted
  parameters.
* **PROVED — the cell FROM the issuance wall** (`cl_const_caseStep_sortPi`):
  given the missing `Issues` edge as a hypothesis and `SortPiFrag hT₂`, the
  row-14 const/const cell closes from the closer's own IH — the transport
  makes `hT₂'` a second sort-typing of `hT₁`'s subject with weight
  `≤ hT₂.wt` (strictly below the cell's node), the edge issues
  `bitCoh hT₁ hT₂'` at `(0,[0])×(1,[0])`, and the bit lands on the cell's
  own `u₂` by `levelIsZero_eqN_congr (hσ.eqN_map …)` — the #7800 `LevelHom`
  gate, the shape `step_of_suppliers` consumes via `Demand.hom`. No port, no
  `ls₁ = ls₂` assumption, no global uniqueness lemma.
* **MEASURED — the wall is the ISSUANCE, not the transport**
  (`cl_const_bitCoh_issuance`, named, not claimed): every landed `Issues`
  row whose child is a `bitCoh` builds its operands from the parent's own
  tree (`occ_bitCoh`'s operands must be `subAt` observations of the issuer;
  `pb_bvar_bitCoh` uses the pb node's own fields). A transported operand — a
  NEW derivation at the transported subject — is not observable at any path
  of the cell's query, so `occ_bitCoh` cannot fire it, even though the rank
  side is fine (weights strictly below). `cl_const_caseStep_sortOne` is the
  degenerate instance where the transported operand IS the observed one
  (the subjects already coincide, so the `rfl` observations hold).
* **REFUTED — the gate the `const`-extension needs**
  (`cl_const_levels_gate_refuted`): extending the fragment with `TyP.const`
  requires `levelsBounded n raw'` for the rebuilt raw list at the
  `ls₁`-instantiation, and that congruence (`eqNList ls ls'` +
  `levelsBounded n ls` ⇒ `levelsBounded n ls'`) is FALSE: `eqN .zero (.imax
  (.param 1) .zero)` holds (imax's zero-arm collapse; `fun ρ => rfl`) while
  `levelsBounded 1` separates them. `TyP.const`'s `hwf` premise is syntactic;
  the eqN slack admits unbounded variants. Not a rank failure — a premise-side
  wall (the brief's escape clause, one lane over).
* **Named walls** (not claimed): `cl_const_bitCoh_issuance` (the missing
  issuance edge — THE wall of this route); `cl_const_transport_supply` (the
  full same-context transport — beyond the fragment it needs the refuted
  gate for const nodes' raw lists, a context re-instantiation transport for
  const nodes under binders, and a mutual `CvP` transport for `conv`-wrapped
  derivations); `cl_const_levels_gate` (the refuted congruence itself).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the fragment predicate -/

/-- Derivations in the `{sort, pi}` fragment: `TyP.sort` leaves and `TyP.pi`
    nodes whose children are again in the fragment. No binder lookup, no const
    node, no conversion, no transport — the subject's parameters reach every
    sub-derivation and nothing else moves. -/
inductive SortPiFrag :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → Prop
  | sort (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l k : Level)
      (h : eqN k (Level.succ l)) :
      SortPiFrag (TyP.sort E n Γ l k h)
  | pi (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level)
      (B : Expr Nat) (v : Level)
      (hA : TyP E n Γ A (Expr.sort u))
      (hB : TyP E n (LocalDecl.assumption A :: Γ) B (Expr.sort v))
      (dA : SortPiFrag hA) (dB : SortPiFrag hB) :
      SortPiFrag (TyP.pi E n Γ A u B v hA hB)

/-! ## §2 the transport (gate-free at the fragment) -/

/-- The level-renaming transport at the `{sort, pi}` fragment: from `eqNList
    ls₁ ls₂` and a sort-typing of the `ls₂`-instantiation of `T`, at a context
    that is an `ls₂`-instantiated pre-image `Δ` above an untouched base, a
    sort-typing of the `ls₁`-instantiation exists at the `ls₁`-image context,
    with universe `eqN`-related to the original and weight not larger.
    Induction on the derivation: every case rebuilds the same constructor
    (`sort`: the leaf's level moves by `instLevel_eqNList`; `pi`: both
    children transport, the pushed assumption is the transported piece). -/
theorem tyP_sortPiFrag_transport (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {ls₁ ls₂ : List Level} (hls : eqNList ls₁ ls₂) :
    ∀ {C : LCtx} {e A : Expr Nat} (D : TyP E n C e A), SortPiFrag D →
    ∀ (T : Expr Nat) (Δ Γbase : LCtx) (v : Level),
      C = instLvlsCtx ls₂ Δ ++ Γbase → e = instantiateLevels ls₂ T →
      A = Expr.sort v →
    ∃ (v' : Level) (D' : TyP E n (instLvlsCtx ls₁ Δ ++ Γbase)
        (instantiateLevels ls₁ T) (Expr.sort v')),
      eqN v' v ∧ D'.wt Aw ≤ D.wt Aw := by
  intro C e A D hF
  induction hF with
  | sort Γ₀ l k hk =>
      intro T Δ Γbase v hC he hAeq
      injection hAeq with hk'
      subst hk'
      cases T with
      | sort w =>
          simp only [instantiateLevels] at he
          injection he with hl
          subst hl
          refine ⟨k, TyP.sort E n (instLvlsCtx ls₁ Δ ++ Γbase) (instLevel ls₁ w) k
            (eqN_trans hk (eqN_congr_succ (eqN_symm (instLevel_eqNList hls w)))),
            eqN_refl k, ?_⟩
          simp only [TyP.wt]
          omega
      | bvar i => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | const r ms => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | app f x => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | lam a b => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | letE a b c => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | lit t => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | pi a b => simp only [instantiateLevels] at he; exact Expr.noConfusion he
  | pi Γ₀ A u B w hA hB dA dB ihA ihB =>
      intro T Δ Γbase v hC he hAeq
      injection hAeq with hv
      subst hv
      cases T with
      | pi A₀ B₀ =>
          simp only [instantiateLevels] at he
          injection he with hlA hlB
          obtain ⟨u', hA', hu, hwA⟩ := ihA A₀ Δ Γbase u hC hlA rfl
          have hCB : LocalDecl.assumption A :: Γ₀ =
              instLvlsCtx ls₂ (LocalDecl.assumption A₀ :: Δ) ++ Γbase := by
            subst hlA; subst hC; rfl
          obtain ⟨w', hB', hw, hwB⟩ :=
            ihB B₀ (LocalDecl.assumption A₀ :: Δ) Γbase w hCB hlB rfl
          refine ⟨Level.imax u' w',
            TyP.pi E n (instLvlsCtx ls₁ Δ ++ Γbase) (instantiateLevels ls₁ A₀) u'
              (instantiateLevels ls₁ B₀) w' hA' hB',
            eqN_congr_imax hu hw, ?_⟩
          simp only [TyP.wt]
          omega
      | bvar i => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | sort l => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | const r ms => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | app f x => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | lam a b => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | letE a b c => simp only [instantiateLevels] at he; exact Expr.noConfusion he
      | lit t => simp only [instantiateLevels] at he; exact Expr.noConfusion he

/-! ## §3 the row-14 const cell at the fragment -/

/-! ## §3 the issuance wall and the conditional cell -/

/-- THE wall of the transport route, ONE named Prop (not claimed): a `cl`
    pair issues `bitCoh` on the first node's own sort-typing plus ANY second
    sort-typing of that same subject. Measured against the landed `Issues`
    rows: every constructor whose child is a `bitCoh` builds its operands
    from the parent's own tree — `occ_bitCoh` requires both operands to be
    `subAt` observations of the issuer, `pb_bvar_bitCoh` uses the pb node's
    own fields — so a TRANSPORTED operand (new derivation, same subject) is
    not issuable, even though its weight is strictly below the cell's nodes
    (the rank side is fine). This is the exact edge `cl_const_caseStep_sortPi`
    below consumes; `cl_const_caseStep_sortOne` is the degenerate instance
    where the transported operand IS the observed one (subjects already
    coincide, so `occ_bitCoh` fires with `rfl`). -/
def cl_const_bitCoh_issuance : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat} {u w : Level}
    (N₁ : TyP E n Γ e T₁) (N₂ : TyP E n Γ e T₂)
    (D₁ : TyP E n Γ T₁ (Expr.sort u)) (D₂' : TyP E n Γ T₁ (Expr.sort w))
    {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (S : ScopedCtx Eₐ E₀ n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp),
    Issues (.cl N₁ N₂ S σ ρ) (.bitCoh D₁ D₂' S σ ρ)

/-- The row-14 const/const cell DISCHARGED FROM THE WALL: given the issuance
    edge (as a hypothesis — the wall above) and the `{sort, pi}` fragment on
    the right typing, the cell closes from the closer's own IH — the
    transport makes `hT₂'` a second sort-typing of `hT₁`'s subject with
    weight `≤ hT₂.wt` (strictly below the cell's node), the (hypothetical)
    edge issues `bitCoh hT₁ hT₂'`, and the bit lands on the cell's own `u₂`
    through the eqN slack at every #7800 `LevelHom`. So the issuance wall is
    EXACTLY the remaining gap of this route at the fragment; no port, no
    `ls₁ = ls₂`, no uniqueness lemma. -/
theorem cl_const_caseStep_sortPi (Aw : Nat → Nat) (tbl : List CRule)
    (edge : cl_const_bitCoh_issuance)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {r : Nat}
    {ls ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    {σ : Level → Level} (hσ : LevelHom σ)
    (hres₁ : E.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (Expr.sort u₁))
    (hres₂ : E.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (Expr.sort u₂))
    (hF : SortPiFrag hT₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (ρ : List Disp) :
    CaseStep Aw tbl
      (.cl (TyP.const E n Γ r ls ls₁ m u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S σ ρ) := by
  obtain ⟨u₂', D₂', hu₂, hwle⟩ :=
    tyP_sortPiFrag_transport Aw (eqNList_of_gates hls₁ hls₂) hT₂ hF m.mtype [] Γ u₂
      rfl rfl rfl
  intro hq ih
  have hbit₂ : levelIsZero (σ u₁) = levelIsZero (σ u₂') :=
    ih_local Aw tbl hq ih
      (.bitCoh hT₁ D₂' S σ ρ)
      (edge (TyP.const E n Γ r ls ls₁ m u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) hT₁ D₂' S σ ρ)
      rfl
      (lexDM_combMeas_mono Aw _
        (lexDM_wt_lt_pair Aw hT₁ D₂' _ _ rfl rfl
          (by simp only [TyP.wt]; omega)
          (by simp only [TyP.wt]; omega)))
  have hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂) := by
    rw [hbit₂, levelIsZero_eqN_congr (hσ.eqN_map hu₂)]
  exact cl_const_nodes tbl σ ρ hres₁ hlen₁ hwf₁ hls₁ hT₁
    hres₂ hlen₂ hwf₂ hls₂ hT₂ hbit

/-! ## §4 the refuted gate and the named walls -/

/-- The imax zero-arm collapse: `.imax (.param 1) .zero` is semantically
    `.zero` (imax's second arm evaluating to zero collapses the whole
    expression regardless of the first arm) while carrying an unbound
    parameter. This is the eqN slack that breaks boundedness congruence. -/
theorem eqN_zero_imax_param_zero :
    eqN Level.zero (Level.imax (Level.param 1) Level.zero) :=
  fun _ => rfl

/-- The boundedness congruence the `const`-extension of the transport needs
    (the rebuilt `TyP.const` node's `hwf` premise at the `ls₁`-instantiated
    raw list): REFUTED at `n := 1`. -/
def cl_const_levels_gate : Prop :=
  ∀ {n : Nat} {ls ls' : List Level}, eqNList ls ls' → levelsBounded n ls = true →
    levelsBounded n ls' = true

/-- Kernel-checked refutation, all premises inhabited: the lists are
    `eqNList`-related pointwise (`eqN_zero_imax_param_zero`) and the left one
    is bounded, but the right one is not — `decide` closes it. So the
    transport's const case cannot discharge `hwf` from the eqN gates; the
    fragment boundary is a premise-side wall, not a rank failure. -/
theorem cl_const_levels_gate_refuted : ¬ cl_const_levels_gate := by
  intro h
  have h1 : levelsBounded 1 [Level.imax (Level.param 1) Level.zero] = true :=
    h (ls := [Level.zero]) (ls' := [Level.imax (Level.param 1) Level.zero])
      ⟨eqN_zero_imax_param_zero, True.intro⟩ rfl
  exact absurd h1 (by decide)

/-- Row 14's exact residue under this route beyond the issuance wall, ONE
    named Prop (not claimed): the full same-context level-renaming transport.
    Beyond the `{sort, pi}` fragment it needs, per constructor: the refuted
    boundedness gate (`cl_const_levels_gate`) for `TyP.const`'s raw list; a
    context re-instantiation transport for const nodes under binders (the
    inner `hT` at `instLvlsCtx ls₂ Δ ++ Γ` must move to the `ls₁`-image
    context); and a mutual `CvP` transport for `conv`-wrapped derivations. -/
def cl_const_transport_supply : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ls₁ ls₂ : List Level}
    {T : Expr Nat} {v : Level}, eqNList ls₁ ls₂ →
    (D : TyP E n Γ (instantiateLevels ls₂ T) (Expr.sort v)) →
    ∃ (v' : Level) (D' : TyP E n Γ (instantiateLevels ls₁ T) (Expr.sort v')),
      eqN v' v
end Rcic.Syn

#print axioms Rcic.Syn.SortPiFrag
#print axioms Rcic.Syn.tyP_sortPiFrag_transport
#print axioms Rcic.Syn.cl_const_bitCoh_issuance
#print axioms Rcic.Syn.cl_const_caseStep_sortPi
#print axioms Rcic.Syn.eqN_zero_imax_param_zero
#print axioms Rcic.Syn.cl_const_levels_gate
#print axioms Rcic.Syn.cl_const_levels_gate_refuted
#print axioms Rcic.Syn.cl_const_transport_supply
