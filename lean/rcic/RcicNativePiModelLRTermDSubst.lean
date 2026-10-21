import rcic.RcicNativePiModelLRTermD
import rcic.RcicNativePiModelLRTermSubst
import rcic.RcicTypedSubst
import rcic.RcicTypedEnvEntry
import rcic.RcicSubstCalc

/-!
# RcicNativePiModelLRTermDSubst — related-substitution stability of `LRTermD`

The #7652 port onto the repaired relation `LRTermD` (#7646, this lane).
A related substituent is read as its full approximation set, `approxSubst`
(grok's `RcicNativePiModelLRTermSubst`): index `j` denotes `denI (EnvI.drop ρ j) r`.

Where #7652 stops because `LRTermS` has no spine reading at a Π
(`lrTermS_spine_at_pi_false`), the repaired relation does — `lrTermD_const_pi_diag`.
This module records the difference and the exact remaining boundary:

* `liftD_sort_inv`, `instantiateD_sort_inv` — a sort can only be produced by
  instantiating a sort, or the substituted variable when the substituent is a
  sort.  `isPropTyI_subst` transports `IsPropTyI` across a *typed* substitution:
  the substitute-typing (`hasTyT_subst_of_envWfT`, the `EnvWfT`-fronted
  general-`j` wrapper over `hasTyT_substS`) gives the sort-0 typing, and
  `hns : r ≠ .sort l` rules out the one degenerate edge — a proposition-typed
  variable replaced by a literal universe.  That edge is the named boundary;
  ruling it out without `hns` needs sort uniqueness (`sort l : sort 0`), a named
  remaining front.
* `whStepD_instantiate`/`whRedD_instantiate` — weak-head computation commutes
  with instantiation (ported from #7652, whose versions are `private`; δ uses
  `EnvClosed`, ι stays the input `hι` — agy-pimodel #7649's semantics).
* `lrTermDCore_sort_subst` / `fundamentalTermDIS` — the `.bot`/`.sort`/variable
  stability on `LRTermD`, same shape as #7652's `FundamentalTermIS`.
* `fundamentalTermDIS_typed` — the same triple where the `.sort` conjunct takes
  the full `LRTermD` input: the proposition case is discharged by
  `isPropTyI_subst` (needs the substitution's typing hypotheses).
* `lrTermD_const_diag_subst` — a constant's diagonal reading is stable under a
  typed substitution (`instantiate` is the identity on constants); on `LRTermS`
  this element had no reading at a Π at all.
* `lrTermD_spine_at_pi_nonvacuous` — the direct refusal of #7652's obstruction
  on the repaired relation: an opaque constant inhabits `spine r []` at `.pi A B`.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

variable {E : ResolvedEnv} {n : Nat}

/-- Lifting preserves every head constructor; a sort in the image is a sort in
    the source. -/
theorem liftD_sort_inv {k d : Nat} {e : Expr Nat} {l : Level}
    (h : lift k d e = .sort l) : e = .sort l := by
  cases e <;> simp only [lift] at h
  case bvar i => split at h <;> exact nomatch h
  case sort l' => exact h
  all_goals exact nomatch h

/-- Instantiation produces a sort only from a sort, or from the substituted
    variable when the replacement is a sort. -/
theorem instantiateD_sort_inv {j : Nat} {s e : Expr Nat} {l : Level}
    (h : instantiate j s e = .sort l) :
    e = .sort l ∨ (e = .bvar j ∧ s = .sort l) := by
  cases e <;> simp only [instantiate] at h
  case bvar i =>
    by_cases h0 : i = j
    · rw [if_pos h0] at h
      exact Or.inr ⟨congrArg Expr.bvar h0, h⟩
    · rw [if_neg h0] at h
      by_cases h1 : j < i
      · rw [if_pos h1] at h; exact nomatch h
      · rw [if_neg h1] at h; exact nomatch h
  case sort l' => exact Or.inl h
  all_goals exact nomatch h

/-- The `EnvWfT`-fronted general-`j` assumption substitution — one line over the
    structure core `hasTyT_substS`, mirroring `hasTyT_substLet_of_envWfT`. -/
def hasTyT_subst_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTyT E n Γ e A → Γ[j]? = some (.assumption t) →
    HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t) →
    HasTyT E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A) :=
  hasTyT_substS (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) v t

/-- Proposition-ness is stable under a typed substitution, provided the
    substituent is not a literal universe (`hns`; otherwise a proposition-typed
    variable could become a sort, and the `IsPropTyI` second conjunct would need
    sort uniqueness to discharge `sort l : sort 0`). -/
theorem isPropTyI_subst (hW : EnvWfT E) {Γ' : LCtx} {j : Nat} {r T₀ A : Expr Nat}
    (hj : Γ'[j]? = some (.assumption T₀))
    (hr : HasTyT E n (substRemove r j Γ') (lift 0 j r) (lift 0 j T₀))
    (hns : ∀ l, r ≠ .sort l) (h : IsPropTyI E n Γ' A) :
    IsPropTyI E n (substRemove r j Γ') (instantiate j (lift 0 j r) A) := by
  obtain ⟨⟨hA⟩, hnsA⟩ := h
  refine ⟨⟨hasTyT_subst_of_envWfT hW r T₀ hA hj hr⟩, ?_⟩
  intro l hl
  rcases instantiateD_sort_inv hl with heq | ⟨_, hs⟩
  · exact hnsA l heq
  · exact hns l (liftD_sort_inv hs)

/-! ### weak-head computation commutes with instantiation (port of #7652's
    `private` helpers, public names so the repaired relation can use them) -/

private theorem instantiateD_instantiate0 (j : Nat) (s a B : Expr Nat) :
    instantiate j s (instantiate0 a B) =
      instantiate0 (instantiate j s a) (instantiate (j + 1) (lift 0 1 s) B) := by
  calc
    instantiate j s (instantiate0 a B)
        = substT (SubstT.single j s) (instantiate0 a B) := by rw [instantiate_eq_substT]
    _ = instantiate0 (substT (SubstT.single j s) a) (substT (SubstT.single j s).up B) :=
        substT_instantiate0 (SubstT.single j s) a B
    _ = instantiate0 (instantiate j s a) (substT (SubstT.single (j + 1) (lift 0 1 s)) B) := by
        rw [← instantiate_eq_substT]
        exact congrArg (fun t => instantiate0 (instantiate j s a) t)
          (substT_ext (SubstT.single_up j s) B)
    _ = instantiate0 (instantiate j s a) (instantiate (j + 1) (lift 0 1 s) B) := by
        rw [← instantiate_eq_substT]

theorem whStepD_instantiate
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {a b : Expr Nat} (h : WhStep E a b) :
    ∀ (j : Nat) (s : Expr Nat), WhStep E (instantiate j s a) (instantiate j s b) := by
  induction h with
  | beta A body arg =>
      intro j s
      rw [show instantiate j s (.app (.lam A body) arg) =
          .app (.lam (instantiate j s A) (instantiate (j + 1) (lift 0 1 s) body))
            (instantiate j s arg) from rfl,
        instantiateD_instantiate0 j s arg body]
      exact WhStep.beta _ _ _
  | zeta A value body =>
      intro j s
      rw [show instantiate j s (.letE A value body) =
          .letE (instantiate j s A) (instantiate j s value)
            (instantiate (j + 1) (lift 0 1 s) body) from rfl,
        instantiateD_instantiate0 j s value body]
      exact WhStep.zeta _ _ _
  | @delta rmem ls m b hres hbody =>
      intro j s
      have hbod : ∀ k, lift k 1 b = b := (hcl rmem m hres).2 b hbody
      have hfix : instantiate j s (instantiateLevels ls b) = instantiateLevels ls b := by
        rw [instantiate_eq_substT]
        exact substT_closed (lift_instantiateLevels_closedT hbod ls) _
      rw [show instantiate j s (.const rmem ls) = .const rmem ls from rfl, hfix]
      exact WhStep.delta hres hbody
  | iota h =>
      intro j s
      exact hι h j s
  | lit t =>
      intro j s
      have hfix : instantiate j s (natExpand t) = natExpand t := natExpand_instantiate j s t
      rw [show instantiate j s (.lit t) = .lit t from rfl, hfix]
      exact WhStep.lit t
  | appHead _ ih =>
      intro j s
      exact WhStep.appHead (ih j s)

theorem whRedD_instantiate
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {a b : Expr Nat} (h : WhRed E a b) (j : Nat) (s : Expr Nat) :
    WhRed E (instantiate j s a) (instantiate j s b) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (whStepD_instantiate hι hcl h j s) ih

theorem whRedD_instantiate_sort
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {a : Expr Nat} {l : Level} (h : WhRed E a (.sort l))
    (j : Nat) (s : Expr Nat) :
    WhRed E (instantiate j s a) (.sort l) :=
  whRedD_instantiate hι hcl h j s

/-- `.sort`-element stability, core reading (the #7652 `.sort` clause verbatim
    on the repaired relation). -/
theorem lrTermDCore_sort_subst
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {j : Nat} {r r' : Expr Nat} {Γ₁ Γ₂ : LCtx}
    {M M' A : Expr Nat}
    (h : LRTermDCore E n Γ₁ M M' A .sort) :
    LRTermDCore E n Γ₂ (instantiate j (lift 0 j r) M)
      (instantiate j (lift 0 j r') M') (instantiate j (lift 0 j r) A) .sort := by
  rw [LRTermDCore.eq_def] at h ⊢
  obtain ⟨⟨l, hA⟩, hLR⟩ := h
  cases hLR with
  | sort hM hM' =>
      exact ⟨⟨l, whRedD_instantiate_sort hι hcl hA j (lift 0 j r)⟩,
        .sort (whRedD_instantiate_sort hι hcl hM j (lift 0 j r))
          (whRedD_instantiate_sort hι hcl hM' j (lift 0 j r'))⟩

/-- Related-substitution stability of `LRTermD` — the #7652 `FundamentalTermIS`
    shape on the repaired relation: `.bot` for every term, `.sort` at the core
    reading, and the substituted variable at every compact of the substituent's
    full approximation set. -/
theorem fundamentalTermDIS
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {ρ : EnvI} {j : Nat} {r r' T : Expr Nat} {Γ : LCtx}
    (hrel : ∀ c, ApproxI (EnvI.drop ρ j) r c →
      LRTermD E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermD E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M M' A : Expr Nat},
        LRTermDCore E n Γ M M' A .sort →
        LRTermD E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxI ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermD E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) := by
  refine ⟨?bot, ?sort, ?var⟩
  case bot =>
    intro _ _ _
    exact lrTermD_bot _ _ _ _
  case sort =>
    intro M M' A h
    exact Or.inr (lrTermDCore_sort_subst hι hcl h)
  case var =>
    intro c hmem
    have hlook : ApproxI (EnvI.insert ρ j (denI (EnvI.drop ρ j) r)) (.bvar j) c :=
      (approxSubst ρ j r (.bvar j) c).mp hmem
    have hL : instantiate j (lift 0 j r) (.bvar j) = lift 0 j r := by
      rw [instantiate, if_pos (rfl : j = j)]
    have hR : instantiate j (lift 0 j r') (.bvar j) = lift 0 j r' := by
      rw [instantiate, if_pos (rfl : j = j)]
    rw [hL, hR]
    rcases approxI_bvar_inv hlook with hbot | hmem
    · subst hbot
      exact lrTermD_bot _ _ _ _
    · rw [EnvI.insert_self] at hmem
      exact hrel c hmem

/-- The typed form: the `.sort` conjunct takes the full `LRTermD` input.  The
    proposition case is discharged by `isPropTyI_subst`; the degenerate edge —
    the substituent being a literal universe — is the hypothesis `hns`. -/
theorem fundamentalTermDIS_typed (hW : EnvWfT E)
    (hι : ∀ {lhs rhs : Expr Nat}, DerivedIotaU E lhs rhs → ∀ (j : Nat) (s : Expr Nat),
      WhStep E (instantiate j s lhs) (instantiate j s rhs))
    (hcl : EnvClosed E) {ρ : EnvI} {j : Nat} {r r' T T₀ : Expr Nat} {Γ Γ' : LCtx}
    (hj : Γ'[j]? = some (.assumption T₀))
    (hr : HasTyT E n Γ (lift 0 j r) (lift 0 j T₀))
    (hΓ : Γ = substRemove r j Γ')
    (hns : ∀ l, r ≠ .sort l)
    (hrel : ∀ c, ApproxI (EnvI.drop ρ j) r c →
      LRTermD E n Γ (lift 0 j r) (lift 0 j r') T c) :
    (∀ {M M' A : Expr Nat},
        LRTermD E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .bot) ∧
    (∀ {M M' A : Expr Nat},
        LRTermD E n Γ' M M' A .sort →
        LRTermD E n Γ (instantiate j (lift 0 j r) M)
          (instantiate j (lift 0 j r') M')
          (instantiate j (lift 0 j r) A) .sort) ∧
    (∀ c, ApproxI ρ (instantiate j (lift 0 j r) (.bvar j)) c →
        LRTermD E n Γ (instantiate j (lift 0 j r) (.bvar j))
          (instantiate j (lift 0 j r') (.bvar j)) T c) := by
  subst Γ
  refine ⟨?bot, ?sort, ?var⟩
  case bot =>
    exact (fundamentalTermDIS hι hcl hrel).1
  case sort =>
    intro M M' A h
    rcases h with hP | hC
    · exact Or.inl (isPropTyI_subst hW hj hr hns hP)
    · exact Or.inr (lrTermDCore_sort_subst hι hcl hC)
  case var =>
    exact (fundamentalTermDIS hι hcl hrel).2.2

/-- A constant's diagonal reading is stable under a typed substitution:
    `instantiate` is the identity on constants, and the typing side moves by
    `hasTyT_subst_of_envWfT`.  At a Π type this element had no reading at all on
    `LRTermS` — the repair makes the diagonal persist. -/
theorem lrTermD_const_diag_subst (hW : EnvWfT E) {Γ' : LCtx} {j : Nat}
    {r₁ : Nat} {ls : List Level} {m : CheckedMember} {r T₀ A : Expr Nat}
    (hmem : E.members r₁ = some m) (hbody : m.body = none)
    (hM : HasTyT E n Γ' (.const r₁ ls) A)
    (hj : Γ'[j]? = some (.assumption T₀))
    (hr : HasTyT E n (substRemove r j Γ') (lift 0 j r) (lift 0 j T₀)) :
    LRTermD E n (substRemove r j Γ') (.const r₁ ls) (.const r₁ ls)
      (instantiate j (lift 0 j r) A) (.spine r₁ []) := by
  refine Or.inr ?_
  rw [LRTermDCore.eq_def]
  refine Or.inr ⟨ls, ls, [], [], .refl _, .refl _, whNormal_const_of_opaque hmem hbody,
    whNormal_const_of_opaque hmem hbody,
    ⟨.refl _ _ _ (hasTyT_subst_of_envWfT hW r T₀ hM hj hr)⟩, [],
    Nat.le_refl 0, Nat.le_refl 0, rfl, fun i => absurd i.isLt (Nat.not_lt_zero _)⟩

/-- The #7652 obstruction does not apply to the repaired relation: an opaque
    constant inhabits its own spine compact at a Π type. -/
theorem lrTermD_spine_at_pi_nonvacuous {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {A B : Expr Nat}
    (hmem : E.members r = some m) (hbody : m.body = none)
    (hM : HasTyT E n Γ (.const r ls) (.pi A B)) :
    ∃ M : Expr Nat, LRTermD E n Γ M M (.pi A B) (.spine r []) :=
  ⟨_, lrTermD_const_pi_diag hmem hbody hM⟩

#print axioms liftD_sort_inv
#print axioms instantiateD_sort_inv
#print axioms hasTyT_subst_of_envWfT
#print axioms isPropTyI_subst
#print axioms whStepD_instantiate
#print axioms whRedD_instantiate
#print axioms whRedD_instantiate_sort
#print axioms lrTermDCore_sort_subst
#print axioms fundamentalTermDIS
#print axioms fundamentalTermDIS_typed
#print axioms lrTermD_const_diag_subst
#print axioms lrTermD_spine_at_pi_nonvacuous

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
