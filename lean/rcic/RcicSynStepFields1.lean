import rcic.RcicSynStepSkeleton

/-!
# `StepSuppliers` field work, part 1: `es_fsub`, `es_zeta`, `es_lit`

Spec: `research/rcic/sortrow/BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §3.1–3.3.
Each field's exact statement (the `CaseStep` shape copied verbatim from
`RcicSynStepSkeleton.StepSuppliers`) is attempted as a standalone theorem
against the IH/issued rows the field statement gives plus landed lemmas.

**Result: none of the three fields is provable as stated.** Each needs `CL`
ports against freshly built canonical surfaces that the demand grammar never
issues:

| field | the issued rows supply | the missing §3 ports |
|---|---|---|
| `es_fsub` | `ES[hab]` (`fsub_es`) | `CL[dl, instEnd hB hab.dl hA]`, `CL[instEnd hB hab.dr hA, dr]`; the keep branch also needs `TableClosed tbl`, not among the field's inputs |
| `es_zeta` | `PB[hv, hA]` (`zeta_pb`) | `CL[dl, TyP.letE … dl.reg.1 hA hv hb dl.reg.2]` (surface), `CL[letSub hb hv hA, dr]` (reduct) |
| `es_lit` | `CL[hexp, dr]` (`lit_cl`) | `CL[dl, TyP.lit … hlit hexp]` (surface) |

Why the ports are unreachable under `StepIH`: a `.cl D₁ D₂ S σ ρ` child of the
`.es` node is demanded only via `rootCl` (which pins `ρ = S.can σ`; the field's
`ρ` is arbitrary) or via an `Issues` edge. The only `.cl`-emitting rows for
these nodes are the named per-case rows (`lit_cl`; none at all for `zeta` and
`fsub`) and the generic `occ_cl`, which requires **both** operands at
`DNode.subAt` payload positions. `instEnd`, `letSub`, and the canonical
`TyP.letE`/`TyP.lit` surfaces are freshly built judgments — never at such a
position (`RcicSynP2Shared` §G: "a freshly built judgment is never at such a
position"). The `Below`-consuming assemblers (`es_of_below_fsub`,
`es_of_below_zeta` via `zeta_dl`/`zeta_dr`, `es_of_below_lit`) cannot be fed:
`Below` quantifies over arbitrary strictly-smaller objects in arbitrary
contexts, while `StepIH` answers only demanded queries.

What this module proves, per field:

1. the issued port the IH actually supplies (`*_issued_*`);
2. the field's exact `CaseStep` statement as a conditional closure given
   precisely the missing ports (`*_caseStep_of_*`) — the exact failing case;
3. a kernel-checked occurrence control: every `.cl` child the node issues is
   the named row or an occurrence pair (`*_issued_cl_*`).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-- Ctor tag of a `CvP`, nonzero exactly on the three step-field ctors.
    `cases` on an `Issues` edge whose parent is a concrete `.es` node cannot
    eliminate the other `.es` rows: index unification reaches e.g.
    `letE A value body = instantiate0 value body`, which is neither solvable
    nor refutable (`instantiate0` is stuck on variables).  `congrArg` of a
    ctor-tag projection on the parent equation reduces to a numeral equality
    and refutes every foreign row directly — a projection, not evidence. -/
def cvpCtorTag {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    CvP E n Γ a b T → Nat
  | .lit .. => 1
  | .zeta .. => 2
  | .fsub .. => 3
  | _ => 0

/-- `cvpCtorTag` lifted to the `.es` parent of an `Issues` edge. -/
def esParentTag : P2Query Eₐ → Nat
  | .es c _ _ _ => cvpCtorTag c
  | _ => 0

/-! ## §1 `es_lit` — the issued `CL[hexp, dr]` and the missing `CL[dl, surface]` -/

/-- The `lit_cl` row issues `CL[hexp, dr]` (spec §3.3 `lit.expansionCL`); the IH
    answers it at a strictly smaller local key (`below_lit`'s pair leg). -/
theorem lit_issued_expansion_cl
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ)) :
    CL tbl σ ρ hexp dr :=
  ih_local Aw tbl hq ih (.cl hexp dr S σ ρ) Issues.lit_cl rfl
    (lexDM_combMeas_mono Aw _ (lex_of_dm (below_lit Aw hlit hexp dl dr).2.2.2))

/-- `es_lit`'s exact `CaseStep` statement, closed under exactly the one port the
    grammar does not issue: `CL[dl, surface]` for a `.lit t`-surface whose
    erasure is `hexp`'s (spec §3.3 `lit.surfaceCL`).  `es_lit`'s midpoint is
    `hexp.eps σ ρ`; `hmid` is exactly the surface's erasure condition — for the
    canonical `TyP.lit … hexp` it holds by `rfl` (the `.lit` arm of `TyP.eps`). -/
theorem lit_caseStep_of_surface_cl
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (Dlit : TyP E n Γ (.lit t) T)
    (hL : CL tbl σ ρ dl Dlit) (hmid : Dlit.eps σ ρ = hexp.eps σ ρ) :
    CaseStep Aw tbl (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ) :=
  fun hq ih => by
    refine es_lit hlit hexp dl dr ?_ ?_
    · have hL' : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (Dlit.eps σ ρ) := hL
      exact hmid ▸ hL'
    · exact lit_issued_expansion_cl Aw tbl hlit hexp dl dr S σ ρ hq ih

/-- Every `.cl` child the `lit` node issues is either an `occ_cl` occurrence
    pair (both operands at payload `subAt` positions) or the `lit_cl` port —
    no row emits `CL[dl, surface]` for a freshly built `.lit t` surface.  The
    parent is generalized before `cases` (the concrete dependent index blocks
    dependent elimination); foreign rows are then refuted by `esParentTag`. -/
theorem lit_issued_cl_variants
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat} {e T₁ T₂ : Expr Nat}
    (hlit : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (iss : Issues (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ)
      (.cl D₁ D₂ S σ ρ)) :
    (∃ k p, P2Query.subAt
        (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ) k p = some (.ty D₁)) ∧
    (∃ k p, P2Query.subAt
        (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ) k p = some (.ty D₂)) ∨
    ∃ (E' : ResolvedEnv) (n' : Nat) (Γ' : LCtx) (t' : Nat) (exp' T' : Expr Nat)
      (hlit' : LiteralExpansion t' exp') (hexp' : TyP E' n' Γ' exp' T')
      (dl' : TyP E' n' Γ' (.lit t') T') (dr' : TyP E' n' Γ' exp' T')
      (E₀' : ResolvedEnv) (n₀' : Nat) (Γ₀' : LCtx) (S' : ScopedCtx Eₐ E₀' n₀' Γ₀')
      (σ' : Level → Level) (ρ' : List Disp),
      (.es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ : P2Query Eₐ) =
        .es (CvP.lit E' n' Γ' t' exp' T' hlit' hexp' dl' dr') S' σ' ρ' ∧
      HEq D₁ hexp' ∧ HEq D₂ dr' := by
  have aux : ∀ q : P2Query Eₐ, Issues q (.cl D₁ D₂ S σ ρ) →
      q = .es (CvP.lit E n Γ t exp T hlit hexp dl dr) S σ ρ →
      (∃ k p, q.subAt k p = some (.ty D₁)) ∧ (∃ k p, q.subAt k p = some (.ty D₂)) ∨
      ∃ (E' : ResolvedEnv) (n' : Nat) (Γ' : LCtx) (t' : Nat) (exp' T' : Expr Nat)
        (hlit' : LiteralExpansion t' exp') (hexp' : TyP E' n' Γ' exp' T')
        (dl' : TyP E' n' Γ' (.lit t') T') (dr' : TyP E' n' Γ' exp' T')
        (E₀' : ResolvedEnv) (n₀' : Nat) (Γ₀' : LCtx) (S' : ScopedCtx Eₐ E₀' n₀' Γ₀')
        (σ' : Level → Level) (ρ' : List Disp),
        q = .es (CvP.lit E' n' Γ' t' exp' T' hlit' hexp' dl' dr') S' σ' ρ' ∧
        HEq D₁ hexp' ∧ HEq D₂ dr' := by
    intro q iss hq
    cases iss with
    | occ_cl h₁ h₂ _ _ => exact Or.inl ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩
    | lit_cl =>
        exact Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          rfl, HEq.rfl, HEq.rfl⟩
    | _ => exact absurd (congrArg esParentTag hq) (by simp [esParentTag, cvpCtorTag])
  exact aux _ iss rfl

/-! ## §2 `es_zeta` — the issued `PB[hv, hA]` and the two missing `CL`s -/

/-- The `zeta_pb` row issues `PB[hv, hA]` (the stored value's proof bit at the
    node's own `hA`); the IH answers it at a strictly smaller local key. -/
theorem zeta_issued_value_pb
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ)) :
    PBit σ ρ hv hA := by
  have hnode : (CvP.zeta E n Γ A value body B u hA hv hb dl dr).isTransport = false := rfl
  have hwv : hv.wt Aw < (CvP.zeta E n Γ A value body B u hA hv hb dl dr).wt Aw := by
    simp only [CvP.wt]; omega
  have hwA : hA.wt Aw < (CvP.zeta E n Γ A value body B u hA hv hb dl dr).wt Aw := by
    simp only [CvP.wt]; omega
  exact ih_local Aw tbl hq ih (.pb hv hA S σ ρ) Issues.zeta_pb rfl
    (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw
        (CvP.zeta E n Γ A value body B u hA hv hb dl dr) hnode hv hA hwv hwA)))

/-- `es_zeta`'s exact `CaseStep` statement, closed under exactly the two §3.2
    ports: `CL[dl, surface]` (`surface := TyP.letE … dl.reg.1 hA hv hb dl.reg.2`,
    `eps_let_clause`) and `CL[reduct, dr]` (`reduct := letSub hb hv hA`,
    `letSub_eps`). Both surfaces are freshly built, so no `occ_cl` reaches them. -/
theorem zeta_caseStep_of_port_cls
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hL : CL tbl σ ρ dl (TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2))
    (hR : CL tbl σ ρ (letSub hb hv hA) dr) :
    CaseStep Aw tbl (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ) :=
  fun _ _ => by
    refine es_zeta (mid := (letSub hb hv hA).eps σ ρ) hA hv hb dl dr ?_ ?_
    · have hL' : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
        ((TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2).eps σ ρ) := hL
      exact ((eps_let_clause hA hv hb dl.reg.2 σ ρ).trans
        (letSub_eps hb hv hA σ ρ).symm) ▸ hL'
    · have hR' : ConvMod (EStep tbl) LvlEq
        ((letSub hb hv hA).eps σ ρ) (dr.eps σ ρ) := hR
      exact hR'

/-- Every `.cl` child the `zeta` node issues is an `occ_cl` occurrence pair —
    there is no named `zeta_cl` row.  The §3.2 surfaces (`TyP.letE …`,
    `letSub`) are never at `subAt` payload positions, so `StepIH` cannot
    supply either `CL`.  The parent is generalized before `cases`; foreign
    rows are refuted by `esParentTag`. -/
theorem zeta_issued_cl_is_occurrence
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level} {e T₁ T₂ : Expr Nat}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (iss : Issues (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ)
      (.cl D₁ D₂ S σ ρ)) :
    (∃ k p, P2Query.subAt
      (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ) k p = some (.ty D₁)) ∧
    (∃ k p, P2Query.subAt
      (.es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ) k p = some (.ty D₂)) := by
  have aux : ∀ q : P2Query Eₐ, Issues q (.cl D₁ D₂ S σ ρ) →
      q = .es (CvP.zeta E n Γ A value body B u hA hv hb dl dr) S σ ρ →
      (∃ k p, q.subAt k p = some (.ty D₁)) ∧
        (∃ k p, q.subAt k p = some (.ty D₂)) := by
    intro q iss hq
    cases iss with
    | occ_cl h₁ h₂ _ _ => exact ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩
    | _ => exact absurd (congrArg esParentTag hq) (by simp [esParentTag, cvpCtorTag])
  exact aux _ iss rfl

/-! ## §3 `es_fsub` — the issued `ES[hab]` and the two missing `CL`s + `TableClosed` -/

/-- The `fsub_es` row issues `ES[hab]` (spec §3.1 `fsub.replacementES`); the IH
    answers it at a strictly smaller local key (`below_fsub`'s `hab` leg). -/
theorem fsub_issued_replacement_es
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hq : Demand (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ))
    (ih : StepIH Aw tbl (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ)) :
    ES tbl σ ρ hab :=
  ih_local Aw tbl hq ih (.es hab S σ ρ) Issues.fsub_es rfl
    (lexDM_combMeas_mono Aw _ (lex_of_dm (below_fsub Aw hB hA hab dl dr).2.2.1))

/-- `es_fsub`'s exact `CaseStep` statement, closed under exactly the §3.1 ports:
    `CL[dl, instEnd hB hab.dl hA]` (`fsub.leftCL`), `CL[instEnd hB hab.dr hA, dr]`
    (`fsub.rightCL`) and the keep branch's `TableClosed tbl` — none of which the
    field's inputs supply. `ES[hab]` comes from the issued `fsub_es` row. -/
theorem fsub_caseStep_of_ports
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hcl : TableClosed tbl)
    (hL : CL tbl σ ρ dl (instEnd hB hab.dl hA))
    (hR : CL tbl σ ρ (instEnd hB hab.dr hA) dr) :
    CaseStep Aw tbl (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ) :=
  fun hq ih => by
    match hzu : levelIsZero (σ u) with
    | true =>
        have hLe := instEnd_eps_drop hB hab.dl hA (σ := σ) (ρ := ρ) hzu
        have hRe := instEnd_eps_drop hB hab.dr hA (σ := σ) (ρ := ρ) hzu
        refine es_fsub_drop hB hA hab dl dr ?_ ?_
        · simpa only [CL, hLe] using hL
        · simpa only [CL, hRe] using hR
    | false =>
        have hLe := instEnd_eps_keep hB hab.dl hA (σ := σ) (ρ := ρ) hzu
        have hRe := instEnd_eps_keep hB hab.dr hA (σ := σ) (ρ := ρ) hzu
        refine es_fsub_keep (ea := hab.dl.eps σ ρ) (eb := hab.dr.eps σ ρ)
          hcl hB hA hab dl dr ?_ ?_ ?_
        · simpa only [CL, hLe] using hL
        · simpa only [CL, hRe] using hR
        · exact ih_local Aw tbl hq ih (.es hab S σ ρ) Issues.fsub_es rfl
            (lexDM_combMeas_mono Aw _
              (lex_of_dm (below_fsub Aw hB hA hab dl dr).2.2.1))

/-- Every `.cl` child the `fsub` node issues is an `occ_cl` occurrence pair —
    there is no named `fsub_cl` row.  `instEnd` is a freshly built judgment,
    never at a `subAt` payload position.  The parent is generalized before
    `cases`; foreign rows are refuted by `esParentTag`. -/
theorem fsub_issued_cl_is_occurrence
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B Sx a b : Expr Nat} {u : Level} {e T₁ T₂ : Expr Nat}
    (hB : TyP E n (.assumption A :: Γ) B Sx) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a Sx))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a Sx))
    {D₁ : TyP E n Γ e T₁} {D₂ : TyP E n Γ e T₂}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (iss : Issues (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ)
      (.cl D₁ D₂ S σ ρ)) :
    (∃ k p, P2Query.subAt
      (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ) k p = some (.ty D₁)) ∧
    (∃ k p, P2Query.subAt
      (.es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ) k p = some (.ty D₂)) := by
  have aux : ∀ q : P2Query Eₐ, Issues q (.cl D₁ D₂ S σ ρ) →
      q = .es (CvP.fsub E n Γ A B Sx a b u hB hA hab dl dr) S σ ρ →
      (∃ k p, q.subAt k p = some (.ty D₁)) ∧
        (∃ k p, q.subAt k p = some (.ty D₂)) := by
    intro q iss hq
    cases iss with
    | occ_cl h₁ h₂ _ _ => exact ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩
    | _ => exact absurd (congrArg esParentTag hq) (by simp [esParentTag, cvpCtorTag])
  exact aux _ iss rfl

end Rcic.Syn

#print axioms Rcic.Syn.cvpCtorTag
#print axioms Rcic.Syn.esParentTag
#print axioms Rcic.Syn.lit_issued_expansion_cl
#print axioms Rcic.Syn.lit_caseStep_of_surface_cl
#print axioms Rcic.Syn.lit_issued_cl_variants
#print axioms Rcic.Syn.zeta_issued_value_pb
#print axioms Rcic.Syn.zeta_caseStep_of_port_cls
#print axioms Rcic.Syn.zeta_issued_cl_is_occurrence
#print axioms Rcic.Syn.fsub_issued_replacement_es
#print axioms Rcic.Syn.fsub_caseStep_of_ports
#print axioms Rcic.Syn.fsub_issued_cl_is_occurrence
