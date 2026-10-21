import rcic.RcicSynSRBetaZetaStarIff

/-!
# The `★`-entry grammar — `EpsStarNormal` decomposed (glm-sr1, row 2)

`EpsStarNormal tbl` (landed in `RcicSynSRBetaZetaStarIff`) asks that an
`eps` image reaching `★` by `EStep*` already be `★`. This module names the
*entry* into `★`: the last step of any `EStep*`-path to `★` is one of
exactly four shapes —

* **β-entry** `.app (.lam M) N → inst 0 N M = ★`;
* **η-entry** `starEtaLHS → ★`;
* **δ-bare entry** `const ρ.head ls → ρ.rhs ls [] = ★` (nullary rule);
* **δ-ctor entry** `.app (const ρ.head ls) (const d ls') → ρ.rhs ls ls' = ★`
  (nullary args, nullary major spine).

`eStep_star_root` proves the grammar; `rstar_star_last` extracts the last
step of a path to `★`; and `epsStarNormal_iff_noEntry` restates
`EpsStarNormal` as the reachability wall `StarEntryWall`: **no `eps` image
reaches an entry shape**. The three entry families are named separately
(`BetaStarEntryWall`, `EtaStarEntryWall`, `DeltaStarEntryWall`) so the
β/η exclusion-by-eps-clauses (mid-`★`/PB-totality side) and the δ
table-RHS tag coherence can be discharged independently — no third
ingredient is hidden inside.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `appN` never returns `★` with nonempty spine -/

/-- `appN f xs = ★` iff the spine is empty and the head is `★`. -/
theorem appN_eq_star {f : ETm} {xs : List ETm} (h : ETm.appN f xs = .star) :
    xs = [] ∧ f = .star := by
  induction xs generalizing f with
  | nil => exact ⟨rfl, h⟩
  | cons x xs ih =>
      have h' := (ih h).2
      cases h'

/-- `CRoot` inversion with free indices — destructing against a literal
    `.star` target fails to unify the computed `appN` rhs, so the shape
    lemma is stated with `a`/`b` abstract. -/
theorem croot_inv {tbl : List CRule} {a b : ETm} (h : CRoot tbl a b) :
    (∃ ρ ∈ tbl, ρ.major = none ∧ ∃ (ls : List Level) (args : List ETm),
        a = ETm.appN (.const ρ.head ls) args ∧ args.length = ρ.nargs ls ∧
        b = ETm.appN (ρ.rhs ls []) args) ∨
    (∃ ρ ∈ tbl, ∃ (d : Nat) (m : List Level → Nat) (ls ls' : List Level)
        (args bs : List ETm),
        ρ.major = some (d, m) ∧
        a = ETm.appN (.const ρ.head ls) (args ++ [ETm.appN (.const d ls') bs]) ∧
        args.length = ρ.nargs ls ∧ bs.length = m ls' ∧
        b = ETm.appN (ρ.rhs ls ls') (args ++ bs)) := by
  cases h with
  | @bare ρ hρ hm ls args hn =>
      exact .inl ⟨ρ, hρ, hm, ls, args, rfl, hn, rfl⟩
  | @ctor ρ hρ d m hm ls ls' args bs hn hb =>
      exact .inr ⟨ρ, hρ, d, m, ls, ls', args, bs, hm, rfl, hn, hb, rfl⟩

/-- The `args` of a `★`-returning `CRoot` fire is empty — bare. -/
theorem croot_star_args_nil {tbl : List CRule} {ρ : CRule} (_hρ : ρ ∈ tbl)
    (_hm : ρ.major = none) {ls : List Level} {args : List ETm}
    (hn : args.length = ρ.nargs ls)
    (hres : ETm.appN (ρ.rhs ls []) args = .star) :
    args = [] ∧ ρ.nargs ls = 0 ∧ ρ.rhs ls [] = .star := by
  obtain ⟨hx, hf⟩ := appN_eq_star hres
  rw [hx] at hn
  exact ⟨hx, hn.symm, hf⟩

/-- The `args ++ bs` of a `★`-returning ctor fire is empty. -/
theorem croot_star_ctor_nil {tbl : List CRule} {ρ : CRule} (_hρ : ρ ∈ tbl)
    {d : Nat} {m : List Level → Nat} (_hm : ρ.major = some (d, m))
    {ls ls' : List Level} {args bs : List ETm}
    (hn : args.length = ρ.nargs ls) (hb : bs.length = m ls')
    (hres : ETm.appN (ρ.rhs ls ls') (args ++ bs) = .star) :
    args = [] ∧ bs = [] ∧ ρ.nargs ls = 0 ∧ m ls' = 0 ∧ ρ.rhs ls ls' = .star := by
  obtain ⟨hx, hf⟩ := appN_eq_star hres
  obtain ⟨ha, hbs⟩ := List.append_eq_nil.mp hx
  rw [ha] at hn
  rw [hbs] at hb
  exact ⟨ha, hbs, hn.symm, hb.symm, hf⟩

/-! ## §2 the entry shapes -/

/-- A `★`-producing δ-entry: a nullary `CRoot` fire whose rhs IS `★`. -/
def DeltaStarEntry (tbl : List CRule) (x : ETm) : Prop :=
  (∃ ρ ∈ tbl, ρ.major = none ∧ ∃ ls : List Level,
      ρ.nargs ls = 0 ∧ x = .const ρ.head ls ∧ ρ.rhs ls [] = .star) ∨
  (∃ ρ ∈ tbl, ∃ (d : Nat) (m : List Level → Nat) (ls ls' : List Level),
      ρ.major = some (d, m) ∧ ρ.nargs ls = 0 ∧ m ls' = 0 ∧
      x = .app (.const ρ.head ls) (.const d ls') ∧ ρ.rhs ls ls' = .star)

/-- The full `★`-entry grammar: β-to-`★`, `starEtaLHS`, or a nullary δ
    fire returning `★`. -/
def StarEntryShape (tbl : List CRule) (x : ETm) : Prop :=
  (∃ M N : ETm, x = .app (.lam M) N ∧ ETm.inst 0 N M = .star) ∨
  x = starEtaLHS ∨
  DeltaStarEntry tbl x

/-- ONE STEP INTO `★` — the entry grammar. Any `EStep tbl x .star` has `x`
    in one of the four entry shapes. -/
theorem eStep_star_root {tbl : List CRule} {x : ETm} (h : EStep tbl x .star) :
    StarEntryShape tbl x := by
  generalize hs : ETm.star = s at h
  rcases h with h | h
  · cases h with
    | beta M N => exact .inl ⟨M, N, rfl, hs.symm⟩
    | cr hc =>
        rcases croot_inv hc with ⟨ρ, hρ, hm, ls, args, hxa, hn, hxb⟩ |
            ⟨ρ, hρ, d, m, ls, ls', args, bs, hm, hxa, hn, hb, hxb⟩
        · obtain ⟨ha, hn0, hr⟩ := croot_star_args_nil hρ hm hn (hs.trans hxb).symm
          rw [ha] at hxa
          exact .inr (.inr (.inl ⟨ρ, hρ, hm, ls, hn0, hxa, hr⟩))
        · obtain ⟨ha, hbs, hn0, hb0, hr⟩ := croot_star_ctor_nil hρ hm hn hb (hs.trans hxb).symm
          rw [ha, hbs] at hxa
          exact .inr (.inr (.inr ⟨ρ, hρ, d, m, ls, ls', hm, hn0, hb0, hxa, hr⟩))
    | appL => cases hs
    | appR => cases hs
    | lam => cases hs
    | piL => cases hs
    | piR => cases hs
  · cases h with
    | eta F =>
        rw [← hs]
        exact .inr (.inl rfl)
    | appL => cases hs
    | appR => cases hs
    | lam => cases hs
    | piL => cases hs
    | piR => cases hs

/-! ## §3 the last-step decomposition -/

/-- A path to `★` is either trivial (`a = ★`) or passes through a final
    `★`-entry: `a →* x` with `x → ★`. -/
theorem rstar_star_last {tbl : List CRule} {a : ETm}
    (h : RStar (EStep tbl) a .star) :
    a = .star ∨ ∃ x, RStar (EStep tbl) a x ∧ EStep tbl x .star := by
  generalize hb : ETm.star = b at h
  induction h with
  | refl =>
      rw [← hb]
      exact .inl rfl
  | step hstep _ ih =>
      rw [← hb] at ih ⊢
      rcases ih rfl with rfl | ⟨x, hr, hx⟩
      · exact .inr ⟨_, .refl _, hstep⟩
      · exact .inr ⟨x, .step hstep hr, hx⟩

/-- `a →* ★` decomposes to `a = ★` or `a` reaching a `★`-entry shape. -/
theorem rstar_star_entry {tbl : List CRule} {a : ETm}
    (h : RStar (EStep tbl) a .star) :
    a = .star ∨ ∃ x, RStar (EStep tbl) a x ∧ StarEntryShape tbl x := by
  rcases rstar_star_last h with rfl | ⟨x, hr, hx⟩
  · exact .inl rfl
  · exact .inr ⟨x, hr, eStep_star_root hx⟩

/-! ## §4 the named entry walls and the restatement -/

/-- No `eps` image reduces to a β-to-`★` redex `.app (.lam M) N` with
    `inst 0 N M = ★`. -/
def BetaStarEntryWall (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (σ : Level → Level) (ρ : List Disp) (M N : ETm),
    RStar (EStep tbl) (D.eps σ ρ) (.app (.lam M) N) → ETm.inst 0 N M ≠ .star

/-- No `eps` image reduces to `starEtaLHS`. -/
def EtaStarEntryWall (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (σ : Level → Level) (ρ : List Disp),
    ¬ RStar (EStep tbl) (D.eps σ ρ) starEtaLHS

/-- No `eps` image reduces to a `★`-returning δ entry. -/
def DeltaStarEntryWall (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (σ : Level → Level) (ρ : List Disp) (x : ETm),
    DeltaStarEntry tbl x → ¬ RStar (EStep tbl) (D.eps σ ρ) x

/-- The joint reachability wall: no `eps` image reaches any `★`-entry
    shape. -/
def StarEntryWall (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (σ : Level → Level) (ρ : List Disp) (x : ETm),
    StarEntryShape tbl x → ¬ RStar (EStep tbl) (D.eps σ ρ) x

/-- Entry shapes are never `★` itself. -/
theorem starEntryShape_ne_star {tbl : List CRule} {x : ETm}
    (h : StarEntryShape tbl x) : x ≠ .star := by
  rcases h with ⟨M, N, hx, -⟩ | hx | ⟨ρ, hρ, hm, ls, -, hx, -⟩ |
    ⟨ρ, hρ, d, m, ls, ls', -, -, -, hx, -⟩ <;>
    · rw [hx]; exact fun h => ETm.noConfusion h

/-- The one-step fire of an entry shape: `x → ★`. -/
theorem eStep_star_of_entry {tbl : List CRule} {x : ETm}
    (h : StarEntryShape tbl x) : EStep tbl x .star := by
  rcases h with ⟨M, N, rfl, hi⟩ | rfl | hδ
  · exact .inl (hi ▸ RStep.beta M N)
  · exact .inr (EtaStep.eta .star)
  · rcases hδ with ⟨ρ, hρ, hm, ls, hn, rfl, hr⟩ |
      ⟨ρ, hρ, d, m, ls, ls', hm, hn, hb, rfl, hr⟩
    · exact .inl (RStep.cr (hr ▸ CRoot.bare hρ hm ls [] hn.symm))
    · show EStep tbl
          (ETm.appN (.const ρ.head ls) (([] : List ETm) ++ [ETm.appN (.const d ls') []]))
          .star
      exact .inl (RStep.cr (hr ▸ CRoot.ctor hρ hm ls ls' [] [] hn.symm hb.symm))

/-- `EpsStarNormal` IS the entry wall — both directions are the
    last-step decomposition plus the entry grammar. -/
theorem epsStarNormal_iff_noEntry (tbl : List CRule) :
    EpsStarNormal tbl ↔ StarEntryWall tbl := by
  constructor
  · intro hN E n Γ e T D σ ρ x hx hr
    have hstar := hN D σ ρ (hr.trans' (.step (eStep_star_of_entry hx) (.refl _)))
    rw [hstar] at hr
    exact starEntryShape_ne_star hx (rstar_of_normal (eStep_star_normal tbl) hr)
  · intro hW E n Γ e T D σ ρ hr
    rcases rstar_star_entry hr with heq | ⟨x, hr', hx⟩
    · exact heq
    · exact absurd hr' (hW D σ ρ x hx)

/-! ## §5 `DeltaStarEntry` at `tableOfI` — only δ-rule bodies -/

/-- Source split of `tableOfI`: every rule is a `tableOf` δ rule or an
    `iotaRulesOf` emission. -/
theorem tableOfI_source {E : ResolvedEnv} (hEnv : EnvWfT E) {ρ : CRule}
    (h : ρ ∈ tableOfI hEnv) :
    ρ ∈ tableOf hEnv ∨
      ∃ (f : Nat) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
        (rr : Nat) (rm : CheckedMember), ρ ∈ iotaRulesOf f fm ctors rr rm := by
  induction hEnv with
  | empty => cases h
  | «axiom» _ _ _ _ hE _ _ _ _ ih =>
      rw [tableOfI_axiom] at h
      rcases ih h with ht | hi
      · rw [tableOf_axiom]; exact .inl ht
      · exact .inr hi
  | definition _ _ _ _ _ hE _ _ _ _ _ _ _ ih =>
      rw [tableOfI_definition] at h
      rcases List.mem_cons.mp h with rfl | h'
      · rw [tableOf_definition]; exact .inl (List.Mem.head _)
      · rcases ih h' with ht | hi
        · rw [tableOf_definition]; exact .inl (List.Mem.tail _ ht)
        · exact .inr hi
  | thm _ _ _ _ hE _ _ _ _ _ _ _ ih =>
      rw [tableOfI_thm] at h
      rcases ih h with ht | hi
      · rw [tableOf_thm]; exact .inl ht
      · exact .inr hi
  | «opaque» _ _ _ _ _ hE _ _ _ _ _ _ _ ih =>
      rw [tableOfI_opaque] at h
      rcases ih h with ht | hi
      · rw [tableOf_opaque]; exact .inl ht
      · exact .inr hi
  | group _ f fm ctors rr rm _ hE _ _ _ _ ih =>
      rw [tableOfI_group] at h
      rcases List.mem_append.mp h with hi | h'
      · exact .inr ⟨f, fm, ctors, rr, rm, hi⟩
      · rcases ih h' with ht | hi'
        · rw [tableOf_group]; exact .inl ht
        · exact .inr hi'

/-- `DeltaStarEntry` at `tableOfI` is exactly the `tableOf` δ rules: the
    iota half is excluded twice over (`major = some` kills the bare shape;
    `nargs = _ + 1 + _ + _` kills the ctor shape). The remaining wall is
    the named δ-RHS coherence: a `tableOf` rule whose closed rhs IS `★`
    — `deltaRule r D_b` with `D_b.eps (instLevel ls) [] = ★`. -/
theorem deltaStarEntry_tableOfI {E : ResolvedEnv} (hEnv : EnvWfT E) {x : ETm}
    (h : DeltaStarEntry (tableOfI hEnv) x) :
    ∃ ρ, ρ ∈ tableOf hEnv ∧ ρ.major = none ∧ ∃ ls : List Level,
      ρ.nargs ls = 0 ∧ x = .const ρ.head ls ∧ ρ.rhs ls [] = .star := by
  rcases h with ⟨ρ, hρ, hm, ls, hn, hx, hr⟩ | ⟨ρ, hρ, d, m, ls, ls', hm, hn, hb, hx, hr⟩
  · rcases tableOfI_source hEnv hρ with ht | ⟨f, fm, ctors, rr, rm, hi⟩
    · exact ⟨ρ, ht, hm, ls, hn, hx, hr⟩
    · obtain ⟨i, _hi, hspec⟩ := mem_iotaRulesOf hi
      obtain ⟨-, -, k, hmaj⟩ := iotaRuleOfCtor_spec hspec
      rw [hm] at hmaj
      exact Option.noConfusion hmaj
  · rcases tableOfI_source hEnv hρ with ht | ⟨f, fm, ctors, rr, rm, hi⟩
    · have hnone := major_none_tableOf hEnv ρ ht
      rw [hnone] at hm
      exact Option.noConfusion hm
    · obtain ⟨i, _hi, hspec⟩ := mem_iotaRulesOf hi
      obtain ⟨-, hnargs, -, -⟩ := iotaRuleOfCtor_spec hspec
      rw [hnargs] at hn
      have hpos : 0 < piCount fm.mtype - iotaNindices rm + 1 + ctors.length +
          iotaNindices rm :=
        Nat.lt_of_lt_of_le (Nat.succ_pos _)
          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      exact absurd hn (Nat.ne_of_gt hpos)

/-- The δ-RHS residue at `tableOf`, sharpened: no `tableOf` rule erases a
    closed body to `★`. Unfolded at a `.definition` node this is
    `(defBodyAt hE hv).eps (instLevel ls) [] ≠ .star` — closing it needs the
    body's `★`-read to agree with the head-const's admitted sort bit, i.e.
    `TyP`-level sort uniqueness for `instantiateLevels ls m.mtype` — the
    `DT012T`/`InScope` family, a forbidden sortRow input. No on-cone instance
    exists either: a real `const` typing carries a sort `eqN`-linked to the
    body's regularity sort, so its bit can't be split from the rhs bit. -/
def DeltaRhsStarWall {E : ResolvedEnv} (hEnv : EnvWfT E) : Prop :=
  ∀ ρ ∈ tableOf hEnv, ∀ ls : List Level, ρ.rhs ls [] ≠ .star

/-- `DeltaRhsStarWall` discharges the δ-entry wall at `tableOfI`: the entry's
    `rhs = ★` conjunct is its only surviving clause after
    `deltaStarEntry_tableOfI`. -/
theorem deltaStarEntryWall_tableOfI {E : ResolvedEnv} (hEnv : EnvWfT E)
    (h : DeltaRhsStarWall hEnv) : DeltaStarEntryWall (tableOfI hEnv) := by
  intro _ _ _ _ _ D σ ρ x hx _
  rcases deltaStarEntry_tableOfI hEnv hx with ⟨ρ', hρ', -, ls, -, -, hr⟩
  exact h ρ' hρ' ls hr

end Rcic.Syn
