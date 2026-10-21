import rcic.RcicSynSREqnTransport

/-!
# RcicSynSREqnAnswer — row 14: ANSWER transport at the fragment; the cell without the edge

cc 2026-10-21 05:45Z brief, lane glm/sr4-eqn (#7809). Prescription: move the
ANSWER, not the QUERY — issue on the parent's own observable derivations,
then carry the bit along the gate-free transport. Measured, this module:

* **ANSWER invariance** (`bit_answer_transport_inv`): the BitCoh answer
  (`levelIsZero (σ u) = levelIsZero (σ v)`) is invariant under the fragment
  transport at every #7800 `LevelHom` — eqN-related universes give equal
  bits. So the unissuable transported query would answer exactly what the
  cell needs; the wall `cl_const_bitCoh_issuance` never carried new content
  at the fragment.
* **THE DISCHARGE** (`sortPiFrag_pair`, `cl_const_caseStep_sortPiFree`):
  at the `{sort, pi}` fragment the answer is not merely transport-invariant,
  it is **cell-derivable** — the two fragment typings pair by mutual
  induction: ONE pattern-level `v` pins both universes
  (`cl_common_sort_sortPiFrag` — the named residue `cl_common_sort` PROVED
  at the fragment), because every constructor premise from universe to
  parameters is eqN-disciplined (`TyP.sort`'s `eqN k (succ l)`, `TyP.pi`'s
  `imax` arms, `instLevel_eqNList` at the leaves). The row-14 const/const
  cell then closes with NO issuance edge, NO transport theorem, NO
  sub-query: `cl_const_caseStep_sortPiFree`. `cl_const_bitCoh_issuance` is
  not needed at the fragment — the wall retreats to non-fragment typings.
* **Boundary**: the pairing consumes exactly the sort/pi constructors' own
  premises. What lies outside is measured in `RcicSynSREqnAlias` with a
  concrete admitted member: const-of-universe layers still chain (a
  one-layer extension, kernel-pinned there), conv-justified universes do
  not.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the ANSWER is transport-invariant at every hom -/

/-- The BitCoh ANSWER is invariant under the fragment transport: at every
    `LevelHom σ`, eqN-related universes (`v'` transported to `v`) give equal
    bits, in both directions. So the query the issuance wall refuses would
    answer exactly what the cell consumes — the wall carries no answer-side
    content at the fragment. -/
theorem bit_answer_transport_inv {σ : Level → Level} (hσ : LevelHom σ)
    {u v v' : Level} (hv : eqN v' v) :
    levelIsZero (σ u) = levelIsZero (σ v') ↔
      levelIsZero (σ u) = levelIsZero (σ v) := by
  have h := levelIsZero_eqN_congr (hσ.eqN_map hv)
  exact ⟨fun hb => hb.trans h, fun hb => hb.trans h.symm⟩

/-! ## §2 the pairing: one pattern-level `v` pins both fragment universes -/

/-- Mutual pairing of two fragment typings of ONE member-type pattern at
    `eqNList`-related instantiations: a single pattern-level `v` pins both
    universes through the constructors' own eqN-disciplined premises. The
    sort leaf: both `h : eqN k (succ l)` premises chain through
    `instLevel_eqNList` at the leaf's level pattern. -/
theorem sortPiFrag_pair {E : ResolvedEnv} {n : Nat} {ls₁ ls₂ : List Level}
    (hls : eqNList ls₁ ls₂) :
    ∀ {Γ₂ : LCtx} {e A₂ : Expr Nat}
      {D₂ : TyP E n Γ₂ e A₂} (F₂ : SortPiFrag D₂),
      ∀ {Γ₁ : LCtx} {T : Expr Nat} (hT : e = instantiateLevels ls₂ T)
        {u₂ : Level} (hA₂ : A₂ = Expr.sort u₂)
        {A₁ : Expr Nat} {D₁ : TyP E n Γ₁ (instantiateLevels ls₁ T) A₁}
        {u₁ : Level} (hA₁ : A₁ = Expr.sort u₁) (F₁ : SortPiFrag D₁),
      ∃ v, eqN u₁ (instLevel ls₁ v) ∧ eqN u₂ (instLevel ls₂ v) := by
  intro Γ₂ e A₂ D₂ F₂
  induction F₂ with
  | sort Γ₀ l k hk =>
      intro Γ₁ T hT u₂ hA₂ A₁ D₁ u₁ hA₁ F₁
      injection hA₂ with hku
      subst hku
      cases T with
      | sort w =>
          simp only [instantiateLevels] at hT
          injection hT with hl
          subst hl
          cases F₁ with
          | sort Γ₁' l₁ k₁ hk₁ =>
              injection hA₁ with hku₁
              subst hku₁
              refine ⟨.succ w, ?_, ?_⟩
              · rw [instLevel_succ]; exact hk₁
              · rw [instLevel_succ]; exact hk
      | bvar i | const r ms | app f x | lam a b | letE a b c | lit t |
          pi a b =>
          simp only [instantiateLevels] at hT; exact Expr.noConfusion hT
  | pi Γ₀ A u B w hA hB dA dB ihA ihB =>
      intro Γ₁ T hT u₂ hA₂ A₁ D₁ u₁ hA₁ F₁
      injection hA₂ with hku
      subst hku
      cases T with
      | pi A₀ B₀ =>
          simp only [instantiateLevels] at hT
          injection hT with hlA hlB
          subst hlA
          subst hlB
          cases F₁ with
          | pi Γ₁' A₁ u₁' B₁ v₁ hA₁ hB₁ dA₁ dB₁ =>
              obtain ⟨vA, hA₁p, hA₂p⟩ := ihA (T := A₀) rfl rfl rfl dA₁
              obtain ⟨vB, hB₁p, hB₂p⟩ := ihB (T := B₀) rfl rfl rfl dB₁
              injection hA₁ with hku₁
              subst hku₁
              refine ⟨.imax vA vB, ?_, ?_⟩
              · rw [instLevel_imax]; exact eqN_congr_imax hA₁p hB₁p
              · rw [instLevel_imax]; exact eqN_congr_imax hA₂p hB₂p
      | bvar i | const r ms | app f x | lam a b | letE a b c | lit t |
          sort l =>
          simp only [instantiateLevels] at hT; exact Expr.noConfusion hT

/-! ## §3 the knowledge at the fragment, and the cell with no edge -/

/-- The named residue `cl_common_sort` PROVED at the `{sort, pi}` fragment:
    two fragment sort-typings of one member type at `eqNList`-related
    instantiations share one pattern-level `v`. -/
theorem cl_common_sort_sortPiFrag {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (Expr.sort u₁))
    (F₁ : SortPiFrag hT₁)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (Expr.sort u₂))
    (F₂ : SortPiFrag hT₂) (hls : eqNList ls₁ ls₂) :
    ∃ v, eqN u₁ (instLevel ls₁ v) ∧ eqN u₂ (instLevel ls₂ v) :=
  sortPiFrag_pair hls F₂ rfl rfl rfl F₁

/-- The row-14 eqN-bit at the fragment needs NO sub-query: it is carried by
    the cell's own constructor fields (the pairing above), at every #7800
    `LevelHom`. -/
theorem cl_bit_free_sortPiFrag {σ : Level → Level} (hσ : LevelHom σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ls₁ ls₂ : List Level}
    {m : CheckedMember} {u₁ u₂ : Level}
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (Expr.sort u₁))
    (F₁ : SortPiFrag hT₁)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (Expr.sort u₂))
    (F₂ : SortPiFrag hT₂) (hls : eqNList ls₁ ls₂) :
    levelIsZero (σ u₁) = levelIsZero (σ u₂) :=
  cl_hbit_hom_of_common_sort hσ hls
    (cl_common_sort_sortPiFrag hT₁ F₁ hT₂ F₂ hls)

/-- The fragment supplies the full ports record (the `hbit` row and every
    other row) at every table. -/
theorem clConstPorts_of_sortPiFrag (tbl : List CRule) {σ : Level → Level}
    (hσ : LevelHom σ) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level} {ρ : List Disp}
    (hls : eqNList ls₁ ls₂)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (Expr.sort u₁))
    (F₁ : SortPiFrag hT₁)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (Expr.sort u₂))
    (F₂ : SortPiFrag hT₂) :
    ClConstPorts tbl σ ρ hT₁ hT₂ :=
  clConstPorts_of_common_sort tbl hσ hls hT₁ hT₂
    (cl_common_sort_sortPiFrag hT₁ F₁ hT₂ F₂ hls)

/-- The row-14 const/const cell at the `{sort, pi}` fragment DISCHARGED with
    NO issuance edge, NO transport, NO sub-query (`ih` unused): the pairing
    pins the universes, the bit lands through the eqN slack at every #7800
    `LevelHom`, `cl_const_nodes` closes. The issuance wall
    `cl_const_bitCoh_issuance` is not needed here — at the fragment the
    ANSWER route terminates in the cell's own data. -/
theorem cl_const_caseStep_sortPiFree (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx} {r : Nat}
    {ls ls₁ ls₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    {σ : Level → Level} (hσ : LevelHom σ)
    (hres₁ : E.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hls₁ : eqNList ls ls₁)
    (hT₁ : TyP E n Γ (instantiateLevels ls₁ m.mtype) (Expr.sort u₁))
    (F₁ : SortPiFrag hT₁)
    (hres₂ : E.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hls₂ : eqNList ls ls₂)
    (hT₂ : TyP E n Γ (instantiateLevels ls₂ m.mtype) (Expr.sort u₂))
    (F₂ : SortPiFrag hT₂)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (ρ : List Disp) :
    CaseStep Aw tbl
      (.cl (TyP.const E n Γ r ls ls₁ m u₁ hres₁ hlen₁ hwf₁ hls₁ hT₁)
        (TyP.const E n Γ r ls ls₂ m u₂ hres₂ hlen₂ hwf₂ hls₂ hT₂) S σ ρ) := by
  intro _ _
  exact cl_const_nodes tbl σ ρ hres₁ hlen₁ hwf₁ hls₁ hT₁
    hres₂ hlen₂ hwf₂ hls₂ hT₂
    (cl_bit_free_sortPiFrag hσ hT₁ F₁ hT₂ F₂ (eqNList_of_gates hls₁ hls₂))

#print axioms Rcic.Syn.bit_answer_transport_inv
#print axioms Rcic.Syn.sortPiFrag_pair
#print axioms Rcic.Syn.cl_common_sort_sortPiFrag
#print axioms Rcic.Syn.cl_bit_free_sortPiFrag
#print axioms Rcic.Syn.clConstPorts_of_sortPiFrag
#print axioms Rcic.Syn.cl_const_caseStep_sortPiFree

end Rcic.Syn
