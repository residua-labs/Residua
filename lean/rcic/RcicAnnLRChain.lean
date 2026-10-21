import rcic.RcicAnnSortUniq
import rcic.RcicAnnFamHeight
import rcic.RcicAnnLRNeut

/-!
# DT-025 / A-6 S1-a — chain extraction from the copy's term relation

R-A6-S1 (PR #6229, `issuecomment-6099264394`): the copy route, NOT
relation-change-first. A related pair at a NON-Prop type carries a head chain
to a normal form, clause by clause of `TyKA`, with NO edit to `TyKA`, `LRRelA`,
`LRTyA`, `FamPhiA` or any sealed statement — this module only ADDS:

* the OWED `WhTyA → TyHRedStarA` bridge (`whTyA_tyHRedStarA`): a type-at-its-own-sort
  chain (`WhTyChainA`, each step at the sort it comes with) is a term chain at ONE
  sort (`TmChainA`, every step at it), given the head's typing at that sort. The
  definitional gap between the two chain notions is exactly the per-step sort: closed
  by sort uniqueness (`sortUniqA`, the copy's six environment hypotheses + `CtxWfA`),
  since each step's head typing and the carried sort typing are two typings of the
  same term at two sorts. This is the bridge the sortT route owed; it was measured
  absent (grep `TyHRedStarA` producers: only `tyHRedStarA_refl`/`_cons`/`_wk`/
  `_retype`/`_trans` pre-exist) and is built here beside the relation.
* the extraction lemma `lrRelA_chain`, by case analysis over the `TyKA` derivation:
  - **fam**: the chains are fields of `FamPhiA`'s two disjuncts (the constructor
    disjunct's reducts with their `hStepFnA = none`, the stuck disjunct's stuck
    reducts — `StuckTmA` carries normality as its first conjunct), read off one
    `LfpWA.unfold` and retyped from the carrier to the type along the clause's
    `WhTyA` (`tyHRedStarA_retype`).
  - **sortT**: `∃ R, LT … Γ a R` is a lower `TyKA` for `a`; `tyKA_whnf` (pre-exist,
    `RcicAnnSortUniq`) reads its `hA` field as a whnf chain to a normal form, and the
    clause's own `HasTyA a (.sort l)` feeds the bridge; the result retypes to `A`.
  - **sortP**: `PropValidA` IS a whnf chain to a triple-like normal form
    (`TripleLikeA` carries `hStepFnA = none` as its first conjunct) — DERIVED, not
    excluded: the elements of a `Prop`-level sort are propositions-as-TYPES, and a
    type's chain is carried. The bridge applies at the clause's sort typing.
  - **prop**: EXCLUDED by the syntax-keyed premise `hkey` — the clause keys
    `IsPropTy` at its normal form, so the premise is stated at normal forms
    (`¬ IsPropTy N ∨ StuckA N`): at a neutral Prop the stuck disjunct keeps the pair
    INSIDE the lemma (the named hypothesis carries the chain regardless of the key —
    the stuck-at-Prop overlap `TyKA_unique` already measures: prop and stuck share
    the same relation there), while at a non-stuck Prop (`ω`) the pair is outside,
    by design: a proof need not have a normal form (`AlgEq.irr` is exactly that).
    NOTE `¬ IsPropTy A` at the UNREDUCED type would need whnf-invariance of
    `inferSortA`, which does not exist (measured: `RcicAnnInfer` disclaims soundness
    in either direction); keying at the normal form is the honest form.
  - **stuck**: NOT derivable (the clause carries typings + `ConvA` only); the pair's
    chains enter as the NAMED hypothesis `hstuck`, keyed on the type's whnf being
    stuck — S1-b's consumption point: its arms at stuck types discharge exactly this.
  - **pi**: WALLED in S1-a — see the report; excluded by the classification premise
    `hnopi` (a non-Prop π whnf is the one shape the lemma does not cover).

The walls at the pi clause (the escape route is otherwise assembled from
pre-exist pieces: `wkOkA_push`/`wkCtxA_push`/`wkExprA_push`, `LRRelA_bvar`,
`hStepFnA_liftA` as an equality for the base case, `tyHRedStarA_wk`,
`hStepFnA_wk_none`):

1. the recursion at the codomain instance `T := instantiate0A x (wkExprA (WkSpecA.ub ρ) C)`
   needs `¬ IsPropTy N ∨ StuckA N` at `T`'s normal forms. `T` is typed at `.sort v`
   with `isZero v = false` (from the clause's `hnp` via `isPropTy_pi_iff`), but
   excluding the prop clause at `T`'s whnf needs the INFERRED sort to agree with the
   declared sort for well-typed types — synthesis soundness, measured absent
   (`RcicAnnInfer`'s header disclaims it; `inferSortA_det` is fuel-determinism only).
2. the same recursion needs `hstuck` at the codomain — chains for the APPLICATION
   pair at a stuck codomain instance — which the outer named hypothesis (keyed at
   `Γ, A`) does not supply.
3. converting the application's chain into the function's ("`wk f`'s chain is a
   prefix") is blocked at a `TyHRedA.iota`-arm step whose head steps: the arm carries
   `I.rel` (the ι's graph + the step function's value) but NO typed head step, and
   `IotaRecHeadA` does not exclude ι answering the head-step value on a full-arity
   recursor spine whose head steps via its own major arm. Closing this needs
   `hStepFnA F = some f' → TyHRedA F f'`-completeness (typed-step completeness),
   measured absent.

Per the segment's stop rules these are REPORTED, not built in: the lemma carries
`hnopi` so that a π-whnf type is outside its scope until the walls fall.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the owed bridge: a type-at-its-own-sort chain is a term chain at one sort -/

section Bridge
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- each step of a `WhTyChainA` comes at its own sort `u`; the head of each step is
typed at `.sort u`. Given the chain's head typed at ONE fixed sort `l`, every step
retypes to `.sort l`: sort uniqueness identifies `u` with `l` (two typings of the same
term), `tyConvA_sorts` converts the step, `TyHRedA.conv` retypes it. -/
def whTyChainA_tmChainA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) :
    {a N : ExprA} → WhTyChainA E I n Γ a N →
      ∀ {l : Level}, HasTyA E I n Γ a (.sort l) → TmChainA E I n Γ (.sort l) a N
  | _, _, .refl _ _ _ _, _, hl => .refl _ hl
  | _, _, .cons _ _ _ _ u hA hs t, l, hl =>
      have equ : eqN u l := sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ hA hl
      .cons _ _ _ (hasTyA_retype_sort hA equ)
        (TyHRedA.conv _ _ _ _ _ hs (tyConvA_sorts Γ equ))
        (whTyChainA_tmChainA hE hI hIS hEN hNC hR hS hρ hΓ t
          (hasTyA_retype_sort (tyHRedA_hasTy_right hs) equ))

/-- THE BRIDGE: a type's whnf chain, with the term typed at the sort, is a TERM chain
    at that sort. `WhTyA` is type-at-its-sort (each step at its own), `TyHRedStarA`
    is term-at-type (all steps at one); the distance is closed by sort uniqueness —
    the sort-typing the sortT/sortP clauses already carry. -/
theorem whTyA_tyHRedStarA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {a N : ExprA} {l : Level}
    (h : WhTyA E I n Γ a N) (hl : Nonempty (HasTyA E I n Γ a (.sort l))) :
    TyHRedStarA E I n Γ a N (.sort l) := by
  refine h.elim fun t => hl.elim fun hl' => ?_
  exact ⟨whTyChainA_tmChainA hE hI hIS hEN hNC hR hS hρ hΓ t hl'⟩

/-- the extraction routes' common shape: a whnf chain to a normal form, the term
    typed at a sort the type also reaches, is a chain AT THE TYPE ending normal. -/
theorem whnfChainA_at (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {A a N : ExprA} {l : Level}
    (hN : WhTyA E I n Γ a N) (hn : hStepFnA E I.fn Γ N = none)
    (hl : Nonempty (HasTyA E I n Γ a (.sort l))) (hA : WhTyA E I n Γ A (.sort l)) :
    TyHRedStarA E I n Γ a N A ∧ hStepFnA E I.fn Γ N = none :=
  ⟨tyHRedStarA_retype (tyConvA_symm_ne (whTyA_tyConv hA))
      (whTyA_tyHRedStarA hE hI hIS hEN hNC hR hS hρ hΓ hN hl), hn⟩

end Bridge

/-! ## (2) the chain-extraction lemma -/

/-- **S1-a**: a pair related at a type whose normal form is neither a proposition nor
    a non-Prop π has head chains to normal forms at that type — the stuck clause's
    chains supplied by name, every other clause's derived from the derivation. The
    premises:

* `hstuck` — the NAMED hypothesis (S1-b's consumption point): at a stuck normal form
  of the type, the pair carries the chains. Keyed on the TYPE's whnf, not on the
  derivation, so it also covers the prop clause's neutral-Prop face (see `hkey`).
* `hkey` — the non-Prop premise, keyed at normal forms exactly where the clauses key
  it (`IsPropTy` reads the whnf): a normal form of the type is either not a
  proposition, or stuck (and then `hstuck` carries the chains regardless of the key).
* `hnopi` — the walled case: the type does not whnf to a non-Prop π (the escape route's
  three walls are reported in the module header; until they fall, a π-whnf type is
  outside this lemma's scope).

`prop` is excluded by `hkey` at its own `A'`; `sortP` is NOT excluded — its elements
are propositions-as-types, and `PropValidA` IS the chain datum. -/
theorem lrRelA_chain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I)
    (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {k : Nat} {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {A a b : ExprA}
    (hstuck : ∀ {N : ExprA}, WhTyA E I n Γ A N → StuckA E I Γ N →
      ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none)
    (hkey : ∀ {N : ExprA}, WhTyA E I n Γ A N → hStepFnA E I.fn Γ N = none →
      ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N)
    (hnopi : ∀ {D : ExprA} {u v : Level} {C : ExprA}, WhTyA E I n Γ A (.pi D u C v) →
      isZero v = true)
    (hrel : LRRelA E I n ρ₀ k Γ A a b) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none := by
  obtain ⟨R, hR, hab⟩ := hrel
  rw [LRTyA_eq] at hR
  cases hR with
  | prop hA hn hP =>
      rcases hkey hA hn with hnp' | hst
      · exact absurd hP hnp'
      · exact hstuck hA hst
  | sortT hA hz hk =>
      rename_i l
      obtain ⟨_, ⟨Ra, hRa⟩, ⟨Rb, hRb⟩, hta, htb, _⟩ := hab
      have hTa' : LRTyA E I n ρ₀ (ht ρ₀ l) Γ a Ra := hRa
      have hTb' : LRTyA E I n ρ₀ (ht ρ₀ l) Γ b Rb := hRb
      rw [LRTyA_eq] at hTa' hTb'
      obtain ⟨Na, whNa, hnNa⟩ := tyKA_whnf hTa'
      obtain ⟨Nb, whNb, hnNb⟩ := tyKA_whnf hTb'
      obtain ⟨cha, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ whNa hnNa hta hA
      obtain ⟨chb, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ whNb hnNb htb hA
      exact ⟨Na, cha, hnNa, Nb, chb, hnNb⟩
  | sortP hA hz =>
      obtain ⟨⟨Na, whNa, hTa⟩, ⟨Nb, whNb, hTb⟩, hta, htb, _, _⟩ := hab
      obtain ⟨cha, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ whNa hTa.1 hta hA
      obtain ⟨chb, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ whNb hTb.1 htb hA
      exact ⟨Na, cha, hTa.1, Nb, chb, hTb.1⟩
  | pi hA hnp hDty hCty RD hD RC hC hCeq =>
      rename_i D C u v
      exact absurd ((isPropTy_pi_iff E I Γ D u C v).mpr (hnopi hA)) hnp
  | fam hA hn hnp hm hind hsh hps hu hz Rs RsF RsI hFld hFldF hFldeq hFldRec hFldFeq
      hxsD hFldI hFldIeq hFldIRec hFldIdom =>
      rename_i r ls ps is m u u₀
      have hcA : Nonempty (TyConvA E I n Γ
          (foldAppsA (.const r ls) (ps ++ is)) A) :=
        tyConvA_symm_ne (whTyA_tyConv hA)
      rcases (LfpWA.unfold famPhiWA_mono hab).2 with
        ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h4', h5,
          hT1, hT1', hFC, hp₁, hp₂, hTa, hTb, hnNa, hnNb, hArgs, hCv₁, hCv₂⟩ |
        ⟨N, N', hNa, hNb, hSa, hSb⟩
      · exact ⟨_, tyHRedStarA_retype hcA hTa, hnNa, _, tyHRedStarA_retype hcA hTb, hnNb⟩
      · exact ⟨_, tyHRedStarA_retype hcA hNa, hSa.1, _, tyHRedStarA_retype hcA hNb, hSb.1⟩
  | stuck hA hN => exact hstuck hA hN

/-- W2 DISCHARGED at a well-formed environment (R-NoDeltaRec-4d-iii, PR #6263): `lrRelA_chain`'s
    premise list minus `hEN`/`hNC`, which `envWfA_normCtorType`/`envWfA_normClosed` supply from
    any `EnvWfA` of the environment. -/
theorem lrRelA_chain_wf {E : ResolvedEnvA} {I J : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hW : EnvWfA J E) (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I)
    (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {k : Nat} {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {A a b : ExprA}
    (hstuck : ∀ {N : ExprA}, WhTyA E I n Γ A N → StuckA E I Γ N →
      ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none)
    (hkey : ∀ {N : ExprA}, WhTyA E I n Γ A N → hStepFnA E I.fn Γ N = none →
      ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N)
    (hnopi : ∀ {D : ExprA} {u v : Level} {C : ExprA}, WhTyA E I n Γ A (.pi D u C v) →
      isZero v = true)
    (hrel : LRRelA E I n ρ₀ k Γ A a b) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none :=
  lrRelA_chain hE hI hIS (envWfA_normCtorType hW) (envWfA_normClosed hW) hR hS hρ hΓ hstuck hkey
    hnopi hrel

/-! ## (3) the S1-a teeth -/

section Pins

/-! ### the fam extraction pin

At the stack's own lightest family fixture (`pinFamFEnvA 1` — `F : Π (A : Sort 1),
Sort 1` with its binder a parameter, `RcicAnnFamHeight`), the copy's six
environment hypotheses are ALL discharged (`EnvSemA` through the profile theorem:
the family is small-index — it has no index binders — constructor-less, and the
environment is recursor-less), and a concrete pair at the FAM CLAUSE — the fresh
variable `x : F (Sort 0)` related to itself by reflection — has its chains
extracted BY THE LEMMA. The extraction runs the stuck disjunct of `FamPhiA`
(reflection folded it there): the witness on both sides is `x` itself with the
empty chain. The π-clause pin this fixture would also carry is the segment's
REPORTED WALL (module header, wall 3) and is not pinned. -/

/-- the fixture's family is small-index: its one binder is a parameter, so it has
    no index binders to bound. -/
theorem pinFamF1_small : SmallIndexProfileA (pinFamFEnvA 1) := by
  intro r m u₀ hm hind hsh v hv ρ x y hx hy hy0
  have hm' : m = pinFamFA 1 := by
    by_cases hr : r = 0
    · subst hr; cases hm; rfl
    · simp [pinFamFEnvA, extendEnvA, emptyEnvA, hr] at hm
  subst hm'
  simp only [pinFamFA, piDomLevelsA, List.drop, List.length_cons, List.drop_nil,
    List.not_mem_nil] at hv

/-- `EnvSemA` at the fixture: the profile theorem, the constructor and recursor
    clauses vacuous (the family's only member is the inductive itself). -/
theorem pinFamF1_sem (n : Nat) : EnvSemA (pinFamFEnvA 1) noIotaA n (fun _ => 1) :=
  envSemA_of_envWfA_profile (pinFamFEnvWfA 1 pinFamF1ViewA) noIotaA_lift noIotaA_subst
    noIotaA_levels (noIotaA_recHead _) posValA_one pinFamF1_small
    (fun r m hm hcm => by rw [pinFamF_ind hm] at hcm; exact MemberClass.noConfusion hcm)
    (envSemRecA_of_noRec (fun r m hm hrec => by
      rw [pinFamF_ind hm] at hrec; exact MemberClass.noConfusion hrec))

/-- THE FAM PIN: `x : F (Sort 0)` is related to itself at the family application
    (the fam clause, by reflection), and the lemma extracts the pair's head chains —
    through `hstuck` VACUOUS (a family application's normal form is shape-headed, so
    the type is not stuck) and `hkey`/`hnopi` discharged by the fixture's own
    normal-form and key lemmas. -/
theorem pinFamF1_chain (k : Nat) :
    ∃ Na, TyHRedStarA (pinFamFEnvA 1) noIotaA 0 [.assumption pinFamFAppA] (.bvar 0) Na
        pinFamFAppA ∧
      hStepFnA (pinFamFEnvA 1) noIotaA.fn [.assumption pinFamFAppA] Na = none ∧
      ∃ Nb, TyHRedStarA (pinFamFEnvA 1) noIotaA 0 [.assumption pinFamFAppA] (.bvar 0) Nb
        pinFamFAppA ∧
      hStepFnA (pinFamFEnvA 1) noIotaA.fn [.assumption pinFamFAppA] Nb = none := by
  have hE : EnvClosedA (pinFamFEnvA 1) := pinFamF_closed 1
  have hI : IotaLiftA noIotaA := noIotaA_lift
  have hIS : IotaSubstA noIotaA := noIotaA_subst
  have hR : IotaRecHeadA (pinFamFEnvA 1) noIotaA := noIotaA_recHead _
  have hEN : EnvNormCtorTypeA (pinFamFEnvA 1) := fun _ _ hm hcm _ _ => by
    rw [pinFamF_ind hm] at hcm; exact MemberClass.noConfusion hcm
  have hNC : EnvNormClosedA (pinFamFEnvA 1) := fun _ _ hm hcm _ _ _ => by
    rw [pinFamF_ind hm] at hcm; exact MemberClass.noConfusion hcm
  have hS : EnvSemA (pinFamFEnvA 1) noIotaA 0 (fun _ => 1) := pinFamF1_sem 0
  have hρ : PosValA (fun _ => 1) := posValA_one
  have ht : HasTyA (pinFamFEnvA 1) noIotaA 0 [.assumption pinFamFAppA] (.bvar 0)
      pinFamFAppA :=
    .bvar _ 0 _ (.succ .zero) rfl (pinFamFAppTy (pinFamF_members 1) 0 _)
  have hΓ : CtxWfA (pinFamFEnvA 1) noIotaA 0 [.assumption pinFamFAppA] :=
    .assumption .nil (pinFamFAppTy (pinFamF_members 1) 0 _)
  obtain ⟨R, hRk⟩ := pinFamF1_tyKA (k := k)
    (LE := fun j _ => LREqA (pinFamFEnvA 1) noIotaA 0 (fun _ => 1) j)
    (LT := fun j _ => LRTyA (pinFamFEnvA 1) noIotaA 0 (fun _ => 1) j) 0 (fun _ => 1) _
  have hrel : LRRelA (pinFamFEnvA 1) noIotaA 0 (fun _ => 1) k [.assumption pinFamFAppA]
      pinFamFAppA (.bvar 0) (.bvar 0) :=
    LRRelA_reflect hE hI ⟨R, by rw [LRTyA_eq]; exact hRk⟩
      (neutKA_bvar hE hI (iotaConstHeadA_of_recHead hR) rfl)
      (neutKA_bvar hE hI (iotaConstHeadA_of_recHead hR) rfl) ⟨ht⟩ ⟨ht⟩ ⟨.refl _ _ _ ht⟩
  exact lrRelA_chain hE hI hIS hEN hNC hR hS hρ hΓ
    (hstuck := fun {N} hN hSt => by
      have e := whTyA_det (whTyA_of_hasTy
          (pinFamFAppTy (pinFamF_members 1) 0 [.assumption pinFamFAppA])) hN
        (pinFamFApp_nf (pinFamF_members 1) _) hSt.1
      subst e
      exact (stuckA_not_fam hSt
        (by simp [appsSpineA] : (appsSpineA pinFamFAppA).1 = .const 0 ([] : List Level))
        (pinFamF_members 1) rfl).elim)
    (hkey := fun {N} hN hn => by
      have e := whTyA_det (whTyA_of_hasTy
          (pinFamFAppTy (pinFamF_members 1) 0 [.assumption pinFamFAppA])) hN
        (pinFamFApp_nf (pinFamF_members 1) _) hn
      subst e
      exact Or.inl (pinFamFApp_notProp (pinFamF_members 1) _))
    (hnopi := fun {D u v C} hN => by
      have e := whTyA_det (whTyA_of_hasTy
          (pinFamFAppTy (pinFamF_members 1) 0 [.assumption pinFamFAppA])) hN
        (pinFamFApp_nf (pinFamF_members 1) _) (hStepFnA_pi _ _ _ _ _ _ _)
      exact absurd e (foldAppsA_const_ne_pi 0 [] [.sort .zero] D u C v))
    hrel

/-! ### the negative Prop note

`ω := ∀ (Z : Sort 0), Z` is a proposition by the key (`isPropTy_pi_iff` reads its
codomain annotation `0` — `omegaA_isPropTy`) whose normal form is π-headed, so NOT
stuck (`stuckA_not_pi`). Instantiating the lemma's `hkey` premise at `N := ω`
(its own normal form: `whTyA_of_hasTy` of its typing, `hStepFnA_pi` its normality)
BOTH disjuncts are false: a pair at `ω` is OUTSIDE the lemma, by design — a proof
need not have a normal form, which is exactly `AlgEq.irr`'s licence and the reason
the prop clause carries no chain datum. -/

example : ¬ (¬ IsPropTy emptyEnvA noIotaA [] omegaA ∨ StuckA emptyEnvA noIotaA [] omegaA) := by
  intro h
  rcases h with h | h
  · exact h omegaA_isPropTy
  · exact stuckA_not_pi h

/-! ### the stuck-at-Prop overlap

A NEUTRAL Prop — `α := x₀ : Sort 0` — satisfies BOTH `IsPropTy` (the key reads the
context's own `Sort 0`) AND `StuckA` (variable-headed, no value): the two keys are
co-satisfiable, and `TyKA_unique` already measures that the prop and stuck clauses
share the same relation there. The lemma keeps such a pair INSIDE its scope: `hkey`
holds via the RIGHT disjunct and `hstuck` carries the chain regardless of the key —
pinned here by exhibiting both facts at `α`. -/

example : IsPropTy emptyEnvA noIotaA [.assumption (.sort .zero)] (.bvar 0) ∧
    StuckA emptyEnvA noIotaA [.assumption (.sort .zero)] (.bvar 0) :=
  ⟨⟨1, .zero, rfl, rfl⟩, ⟨rfl, by simp [appsSpineA, isShapeHeadA]⟩⟩

end Pins

/-! ## (4) DT-025 / A-6 S1-c — the π escape (ruling R-A6-S1c, PR #6246's cc verdict)

The three walls, read against the tree after S1-a landed. What is BUILT here and what
is a MEASURED residue is recorded per wall, in the closed residue vocabulary:

* **Wall 3 (typed-step completeness), the dischargeable core.** At a STEP-CLEAN
  environment — no member carries a body (the δ arm's `m.bodyA = some b` guard dead),
  the interface answers nothing (the ι arm dead), no member is a recursor (the
  struct / unit-minor / major arms' `recAtMajorA` guard dead) — every step the head
  function takes at a NON-PROP π IS a typed step (`hStepFnA_typedPi`): β by inversion
  and `hasTyA_inst0'`, ζ by `hasTyA_inst0Let`, ζ-local by `substTyA_id`'s value field
  and `convA_hasTy_right`, a head step by induction and `TyHRedA.app`, lit by
  `hasTyA_lit_gen`. The FIVE ARMS THAT DO NOT CLOSE AT THE SIX are reported below
  (module header, "the five arms"); they are carried by the named premise `hpiStep`
  of `lrRelA_chain_env`, and `hStepFnA_typedPi` discharges that premise at every
  step-clean environment — `lrRelA_chain_env_stepClean` is the instantiation.
* **Wall 1 (codomain prop-exclusion), the declared-sort route.** From the π clause's
  `hCty : HasTyA … C (.sort v)` and the Π's non-Prop-ness (`isZero v = false` via
  `isPropTy_pi_iff`), the key at the codomain's whnf `N` follows for every face but
  one (`hkey_of_sortTy`): `N` sort-headed by `not_isPropTy_sort`; `N` π-headed by
  `isPropTy_pi_iff` + `sortUniqA` (the π's own `.sort (imax u' v')` typing against the
  declared one, `isZero_imax`, `isZero_eqN`); `N` stuck-headed by the right disjunct.
  The MEASURED ABSENT face (two searches: the `IsPropTy` lemma census —
  `not_isPropTy_sort` / `isPropTy_pi_iff` / `not_isPropTy_of_inferSortA` is all the
  tree carries, `RcicAnnAlg`/`RcicAnnLR`; the `sortUniqA` route census — the canonical
  const typing kills the 0-ARY Sort-0 family but a general family spine's canonical
  sort is telescope content, and `inferSortA` walking the same telescope is synthesis
  soundness, which `RcicAnnInfer`'s header disclaims in either direction) is the
  FAMILY-APPLICATION face: `¬ IsPropTy` at a normal `foldAppsA (.const r ls) xs` with
  `r` inductive of `E`. It is carried by the named premise `hfamkey`.
* **Wall 2 (re-keying `hstuck`), environment-wide — and a genuine open obligation.**
  `lrRelA_chain_env` states `hstuck` for every context and type, keyed on the
  stuck clause's own pair data (both typings at the stuck normal form and their
  conversion — exactly what the clause's relation and S1-b's `fundA` arms carry;
  the ruling's `∀ Γ A a b` sketch elides this triple, and without it the premise
  would demand chains for untyped pairs, which is false). This re-keys at the
  codomain for free — the π arm's recursion instantiates it at the pushed context
  unchanged. The price is real and is recorded here rather than hidden: the
  universal quantification makes `hstuck` CIRCULAR for W-APP's consumption —
  W-APP's discharge needs `f`'s head chain at its π type, and the only producer
  of that chain is this theorem, which demands `hstuck` at every type including
  the one being proved. S1-d must restructure it (bound `hstuck` in the rec
  motive, or quantify it over the types reached inside `A`'s `TyKA` derivation);
  until then W-APP cannot consume `lrRelA_chain_env` as stated.

The π escape itself (`lrRelA_chain_env`'s π arm + `piHeadPrefix`): the fresh variable
enters at the pushed world by `LRRelA_bvar` and `LRRelA.at` at the domain's own
`TyKA`; the application premise gives the pair `(wk f x, wk g x)` inside the
codomain instance's relation; the induction hypothesis — with `hkey` at the codomain
DISCHARGED from the declared sort (wall 1) and `hstuck` re-keyed (wall 2) — gives
the application pair's chains; `piHeadPrefix` converts them into the function's by
induction on the chain: a normal application has a normal head (`hstuck`-arm-free
inversion), and a head step is an `hStepFnA_app_head` step whose typed counterpart
is exactly `hpiStep` (wall 3). `hnopi` is GONE — not narrowed: the π clause is
handled by recursion, and the two residues (`hfamkey`, `hpiStep`) are named on the
lemma, not hidden in a syntactic exclusion.

Why the sealed `lrRelA_chain` keeps its own proof: its keyed `hstuck` premise (at
one `Γ, A`, for the lemma's own pair) does not imply the environment-wide triple —
so the original is NOT re-derivable from the variant (the derivation direction the
merge-case instructions sketch would need keyed ⊢ environment-wide, which is false:
the keyed premise says nothing about the codomain's context). Every sealed statement
above is unchanged; the variant is additive.

**The five arms that do not close at the six hypotheses** (each is a premise the
relation or the rows supply — `TyHRedA`'s own docstrings name them "carried, for
the relation to supply"; they land under `AnnEnvA` in `RcicAnnIotaSR`/`RcicAnnAnnotate`):

* δ — `TyHRedA.delta`'s `hb : HasTyA … (instantiateLevelsA ls b) (instantiateLevelsA
  ls m.mtypeA)`: the member body's typing, `EnvWfA` content (`envWfA_memberBody`,
  `hasTyA_memberBody_inst`), not derivable from `EnvSemA` (which relates the constant
  to itself at its type, not the body).
* ι — `TyHRedA.iota`'s `hrhs`: the reduct's typing, ι subject reduction
  (`IotaSRA`/`convA_iota_of_fn`, `RcicAnnIotaSR:1000,1019`), proved on the tree only
  under `AnnEnvA` at the CONCRETE ι.
* struct / unit-minor — `TyHRedA.kstruct`/`kunit`'s `hcv : ConvA … T`: the struct/unit
  conversion, the same rows' content.
* major — `TyHRedA.major`'s `hrt`: the reduct's typing at the codomain instance
  under the major's step, "which the relation supplies semantically (M2-f (5))".

At a step-clean environment all five guards are dead and `hStepFnA_typedPi` needs
none of them — `lrRelA_chain_env_stepClean` (below) is that instantiation. -/

section S1c

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-! ### wall 3, the small print: arm inversion and the lift equality -/

/-- a normal application has a normal head (the head-step arm fires first) —
    `hStepFnA_foldApps_none` at the singleton spine. -/
theorem hStepFnA_app_none_head (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f x : ExprA}
    (h : hStepFnA E iota Γ (.app f x) = none) : hStepFnA E iota Γ f = none :=
  ((hStepFnA_foldApps_none E iota Γ f [x] h).resolve_left (by simp)).1

/-! ### wall 3's dischargeable core: step-completeness at a non-Prop π -/

/-- step-completeness at a step-clean environment: on the six hypotheses, every step
    the head function takes at a non-Prop π is a typed step. The five arms that need
    more than the six (δ's body typing, ι's reduct typing, the struct/unit
    conversions, the major's codomain-under-step typing) are dead here by the three
    profile conditions, and are carried by `lrRelA_chain_env`'s `hpiStep` in general. -/
theorem hStepFnA_typedPi (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ)
    (hnobody : ∀ r m, E.members r = some m → m.bodyA = none)
    (hiotaNone : ∀ e, I.fn e = none)
    (hnorec : ∀ r m, E.members r = some m → m.mclass ≠ .recursorM) :
    ∀ (F : ExprA) {f' D u C v : _}, isZero v = false →
      HasTyA E I n Γ F (.pi D u C v) → hStepFnA E I.fn Γ F = some f' →
      Nonempty (TyHRedA E I n Γ F f' (.pi D u C v)) := by
  intro F
  induction F with
  | app f x ihf ihx =>
      intro f' D u C v hz hF hstep
      rcases lamA_or_not f with ⟨A₀, u₀, body, rfl⟩ | hnl
      · -- β
        have hc : hStepFnA E I.fn Γ (.app (.lam A₀ u₀ body) x) = some (instantiate0A x body) :=
          hStepFnA_app_lam E I.fn Γ A₀ u₀ body x
        rw [hstep] at hc
        have hf'e : f' = instantiate0A x body := Option.some.inj hc
        obtain ⟨A₁, u₁, B₁, v₁, _w₁, ⟨hf⟩, ⟨hx⟩, ⟨hB₁⟩, _, ⟨t₁⟩⟩ := hasTyA_app_gen hF
        obtain ⟨B₂, v₂, ⟨hA₀⟩, ⟨hB₂⟩, ⟨hbody₂⟩, ⟨tl₂⟩⟩ := hasTyA_lam_gen hf
        -- the app-typing's codomain sort is Type-level (the redex's type is):
        have hz₁ : isZero v₁ = false :=
          codom_typeLevel hE hI hIS hEN hNC hR hS hρ hΓ hB₁ hx ⟨t₁⟩ (Or.inr ⟨D, u, C, v, hz, ⟨.refl Γ _⟩⟩)
        -- so the lam's own codomain annotation is too (a Prop π converts to no Type-level π):
        have hz₂ : isZero v₂ = false := by
          cases hzv : isZero v₂ with
          | false => rfl
          | true =>
              exact (tyConvA_prop_typi_false hE hI hIS hEN hNC hR hS hρ hΓ (.pi Γ A₀ u₀ B₂ v₂ hA₀ hB₂)
                (by rw [isZero_imax]; exact hzv) hz₁ tl₂).elim
        obtain ⟨⟨tdom⟩, hcod⟩ := tyConvA_pi_inj hE hI hIS hEN hNC hR hS hρ hΓ hz₂ tl₂
        have hx₀ : HasTyA E I n Γ x A₀ := hasTyA_of_tyConvA hx tdom.symm
        have hbeta : TyHRedA E I n Γ (.app (.lam A₀ u₀ body) x) (instantiate0A x body)
            (instantiate0A x B₂) :=
          .beta Γ A₀ u₀ body x B₂ hA₀ hbody₂ hx₀
            (hasTyA_inst0' hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hbody₂ hx₀)
        obtain ⟨tcB⟩ := hcod x hx₀
        have hconv : TyConvA E I n Γ (instantiate0A x B₂) (.pi D u C v) :=
          .trans _ _ _ _ tcB t₁
        subst hf'e
        exact ⟨TyHRedA.conv Γ _ _ _ _ hbeta hconv⟩
      · -- a head step, or the dead arms
        have hrecf : recAtMajorA E f = false := by
          cases hrec : recAtMajorA E f with
          | false => rfl
          | true =>
              obtain ⟨r, ls, m, _, hm, hcm, _⟩ := recAtMajorA_true hrec
              exact absurd hcm (hnorec r m hm)
        have hsp : structPosA E f = false := structPosA_of_not_rec hrecf
        have hii : I.fn (ExprA.app f x) = none := hiotaNone _
        rw [hStepFnA_app_nonlam E I.fn Γ x hnl] at hstep
        cases hff : hStepFnA E I.fn Γ f with
        | none =>
            rw [hff] at hstep
            dsimp only at hstep
            rw [if_neg (by rw [hsp]; exact Bool.false_ne_true)] at hstep
            rw [hii] at hstep
            dsimp only at hstep
            rw [if_neg (by rw [hrecf]; exact Bool.false_ne_true)] at hstep
            exact Option.noConfusion hstep
        | some g =>
            rw [hff] at hstep
            dsimp only at hstep
            have hf'e : f' = .app g x := (Option.some.inj hstep).symm
            obtain ⟨A₁, u₁, B₁, v₁, _w₁, ⟨hf⟩, ⟨hx⟩, ⟨hB₁⟩, ⟨hTy₁⟩, ⟨t₁⟩⟩ := hasTyA_app_gen hF
            have hz₁ : isZero v₁ = false :=
              codom_typeLevel hE hI hIS hEN hNC hR hS hρ hΓ hB₁ hx ⟨t₁⟩ (Or.inr ⟨D, u, C, v, hz, ⟨.refl Γ _⟩⟩)
            obtain ⟨hstepF⟩ := ihf (f' := g) hz₁ hf hff
            have happ : TyHRedA E I n Γ (.app f x) (.app g x) (instantiate0A x B₁) :=
              .app Γ f g x A₁ B₁ (.pi A₁ u₁ B₁ v₁) u₁ v₁ _ hstepF (.refl Γ _)
                hB₁ hTy₁ hx
            subst hf'e
            exact ⟨TyHRedA.conv Γ _ _ _ _ happ t₁⟩
  | lam A u b =>
      intro f' D u' C v' _ hF hstep
      rw [hStepFnA_lam E I.fn Γ A u b] at hstep
      exact Option.noConfusion hstep
  | pi A u B v =>
      intro f' D u' C v' _ hF hstep
      rw [hStepFnA_pi E I.fn Γ A u B v] at hstep
      exact Option.noConfusion hstep
  | sort l =>
      intro f' D u' C v' _ hF hstep
      rw [hStepFnA_sort E I.fn Γ l] at hstep
      exact Option.noConfusion hstep
  | bvar i =>
      intro f' D u C v _ hF hstep
      obtain ⟨A₁, hlook, ⟨t₁⟩⟩ := hasTyA_bvar_gen hF
      have hval : lookupValueA Γ i = some f' := hstep
      have hvv : HasTyA E I n Γ f' A₁ := by
        have hcv := (substTyA_id hE hI hΓ).val i A₁ f' hlook hval
        rw [SubstA.id_apply, substA_id, substA_id] at hcv
        exact convA_hasTy_right hE hI hR hIS hΓ hcv
      exact ⟨TyHRedA.conv Γ _ _ _ _ (.zetaLocal Γ i A₁ f' hval hlook hvv) t₁⟩
  | const r ls =>
      intro f' D u C v _ hF hstep
      simp only [hStepFnA] at hstep
      cases hm : E.members r with
      | none => rw [hm] at hstep; exact Option.noConfusion hstep
      | some m =>
          rw [hm] at hstep
          dsimp only at hstep
          by_cases htr : transparent m.mclass = true
          · rw [if_pos htr] at hstep
            cases hb : m.bodyA with
            | none =>
                rw [hb] at hstep
                simp only [Option.map_none'] at hstep
                exact Option.noConfusion hstep
            | some b => rw [hnobody r m hm] at hb; exact Option.noConfusion hb
          · rw [if_neg htr] at hstep; exact Option.noConfusion hstep
  | letE A val body =>
      intro f' D u C v _ hF hstep
      obtain ⟨u₀, _w₀, B₁, ⟨hA⟩, ⟨hval⟩, _, ⟨hbody⟩, ⟨t₁⟩⟩ := hasTyA_letE_gen hF
      have hc : hStepFnA E I.fn Γ (.letE A val body) = some (instantiate0A val body) := rfl
      rw [hstep] at hc
      have hf'e : f' = instantiate0A val body := Option.some.inj hc
      subst hf'e
      exact ⟨TyHRedA.conv Γ _ _ _ _
        (.zeta Γ A val body B₁ u₀ hA hval hbody
          (hasTyA_inst0Let hE hI (iotaRecHeadTypedA_of hR) hIS hΓ hbody hval)) t₁⟩
  | lit t =>
      intro f' D u C v _ hF hstep
      have hc : hStepFnA E I.fn Γ (.lit t) = some (natExpandA t) := rfl
      rw [hstep] at hc
      have hf'e : f' = natExpandA t := Option.some.inj hc
      subst hf'e
      exact ⟨.lit Γ t (.pi D u C v) (hasTyA_lit_gen hF)⟩


/-! ### wall 1: the declared-sort route to the codomain's key -/

/-- a sort-typing travels down a type's whnf chain (subject reduction at each sort,
    which is large). -/
theorem whTyChainA_sort_end (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) :
    {X N : ExprA} → WhTyChainA E I n Γ X N → ∀ {v : Level},
      Nonempty (HasTyA E I n Γ X (.sort v)) → Nonempty (HasTyA E I n Γ N (.sort v))
  | _, _, .refl _ _ _ _, _, h => h
  | _, _, .cons _ _ _ _ _ _ hs t, v, h =>
      h.elim fun hh =>
        whTyChainA_sort_end hE hI hIS hEN hNC hR hS hρ hΓ t
          (tyHRedA_sr_large hE hI hIS hEN hNC hR hS hρ hΓ hs hh (Or.inl ⟨v, ⟨.refl Γ _⟩⟩))

/-- neither a sort nor a π is typed AT a π (their canonical types are sorts, and no
    sort converts to a π), so a sort- or π-headed spine has no arguments. -/
theorem hasTyA_headSpine_nil (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) (h : ExprA)
    (hh : ∀ T, HasTyA E I n Γ h T → ∀ A u B v, T ≠ .pi A u B v) :
    (xs : List ExprA) → ∀ T, HasTyA E I n Γ (foldAppsA h xs) T → xs = [] := by
  refine snocInduction (P := fun xs => ∀ T, HasTyA E I n Γ (foldAppsA h xs) T → xs = [])
    (fun _ _ => rfl) ?_
  intro ys x ih T hT
  rw [foldAppsA_append] at hT
  simp only [foldAppsA] at hT
  obtain ⟨_, _, _, _, _, ⟨hf⟩, _, _, _, _⟩ := hasTyA_app_gen hT
  have hys := ih _ hf
  subst hys
  exact absurd rfl (hh _ hf _ _ _ _)

/-- a sort is never typed at a π. -/
theorem hasTyA_sort_notPi (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {l : Level} :
    ∀ T, HasTyA E I n Γ (.sort l) T → ∀ A u B v, T ≠ .pi A u B v := by
  intro T h A u B v e
  subst e
  exact (tyConvA_pi_sort_false hE hI hIS hEN hNC hR hS hρ hΓ (hasTyA_sort_gen h).symm).elim

/-- a π is never typed at a π either. -/
theorem hasTyA_pi_notPi (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) {D : ExprA} {u : Level} {C : ExprA} {v : Level} :
    ∀ T, HasTyA E I n Γ (.pi D u C v) T → ∀ A u' B v', T ≠ .pi A u' B v' := by
  intro T h A u' B v' e
  subst e
  exact (tyConvA_pi_sort_false hE hI hIS hEN hNC hR hS hρ hΓ (hasTyA_pi_sort h).symm).elim

/-- WALL 1's route: from a declared non-Prop sort at the type, to the whnf key — the
    sort face by `not_isPropTy_sort`, the π face by `isPropTy_pi_iff` + `sortUniqA` (the
    π's own `.sort (imax u' v')` typing against the declared one, through `isZero_imax`
    and `isZero_eqN`), the stuck face by the right disjunct. The family-application
    face is the measured absence (module header): it is `hfamkey` below, a premise of
    `lrRelA_chain_env`, keyed exactly at the declared-sort route. -/
theorem hkey_of_sortTy (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ)
    (hfamkey : ∀ {Γ' : LCtxA} {X' N' : ExprA} {v' : Level} {r : Nat} {ls : List Level}
      {xs : List ExprA} {m : CheckedMemberA}, CtxWfA E I n Γ' →
      HasTyA E I n Γ' X' (.sort v') → isZero v' = false → WhTyA E I n Γ' X' N' →
      hStepFnA E I.fn Γ' N' = none → N' = foldAppsA (.const r ls) xs →
      E.members r = some m → m.mclass = .inductiveM → ¬ IsPropTy E I Γ' N')
    {X : ExprA} {v : Level} (hX : HasTyA E I n Γ X (.sort v)) (hz : isZero v = false)
    {N : ExprA} (hN : WhTyA E I n Γ X N) (hn : hStepFnA E I.fn Γ N = none) :
    ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N := by
  obtain ⟨c⟩ := hN
  have hNv : Nonempty (HasTyA E I n Γ N (.sort v)) :=
    whTyChainA_sort_end hE hI hIS hEN hNC hR hS hρ hΓ c ⟨hX⟩
  have hsp := foldAppsA_appsSpineA N
  have hna := appsSpineA_fst_not_app N
  rw [← hsp] at hn hNv ⊢
  generalize (appsSpineA N).1 = H at hn hNv hna hsp
  generalize (appsSpineA N).2 = xs at hn hNv hsp
  obtain ⟨hNv⟩ := hNv
  have hshape := hStepFnA_foldApps_none E I.fn Γ H xs hn
  cases H with
  | bvar i =>
      refine Or.inr ⟨hn, ?_⟩
      rw [appsSpineA_foldAppsA]
      show ¬ isShapeHeadA E (.bvar i)
      exact fun h => h
  | const r ls =>
      cases hmem : E.members r with
      | none =>
          refine Or.inr ⟨hn, ?_⟩
          rw [appsSpineA_foldAppsA]
          show ¬ isShapeHeadA E (.const r ls)
          simp [isShapeHeadA, hmem]
      | some m =>
          by_cases hind : m.mclass = .inductiveM
          · exact Or.inl (hfamkey hΓ hX hz (hsp.symm ▸ ⟨c⟩) hn rfl hmem hind)
          · refine Or.inr ⟨hn, ?_⟩
            rw [appsSpineA_foldAppsA]
            exact not_isShapeHeadA_const hmem hind
  | sort l =>
      have hnil := hasTyA_headSpine_nil hE hI hIS hR hS hρ hΓ _
        (hasTyA_sort_notPi hE hI hIS hEN hNC hR hS hρ hΓ) xs _ hNv
      subst hnil
      exact Or.inl (not_isPropTy_sort E I Γ l)
  | pi D u C v' =>
      have hnil := hasTyA_headSpine_nil hE hI hIS hR hS hρ hΓ _
        (hasTyA_pi_notPi hE hI hIS hEN hNC hR hS hρ hΓ) xs _ hNv
      subst hnil
      obtain ⟨hA', hB'⟩ := hasTyA_pi_parts hNv
      have hcanon := sortUniqA hE hI hIS hEN hNC hR hS hρ hΓ hNv (.pi Γ D u C v' hA' hB')
      have hze := isZero_eqN hcanon
      rw [isZero_imax] at hze
      have hzv' : isZero v' = false := hze ▸ hz
      refine Or.inl fun hP => ?_
      have hzt := (isPropTy_pi_iff E I Γ D u C v').mp hP
      rw [hzv'] at hzt
      exact Bool.noConfusion hzt
  | lam A u b =>
      rcases hshape with e | ⟨_, hnl⟩
      · subst e
        simp only [foldAppsA] at hNv
        obtain ⟨_, _, _, _, _, ⟨t⟩⟩ := hasTyA_lam_gen hNv
        exact (tyConvA_pi_sort_false hE hI hIS hEN hNC hR hS hρ hΓ t).elim
      · exact absurd rfl (hnl A u b)
  | letE A val body =>
      rcases hshape with e | ⟨hhn, _⟩
      · subst e
        simp [foldAppsA, hStepFnA] at hn
      · simp [hStepFnA] at hhn
  | lit t =>
      rcases hshape with e | ⟨hhn, _⟩
      · subst e
        simp [foldAppsA, hStepFnA] at hn
      · simp [hStepFnA] at hhn
  | app f x => exact absurd rfl (hna f x)

/-! ### the π escape's two combinators -/

/-- determinism at the application: while the head function still steps, every
    step `app F x` takes is `app`-congruent (`hStepFnA_app_head`), so a typed chain
    out of the application begins with the function's own `whnfA` run. The end
    hypothesis (the chain's normality) is what carries the tail the chain takes
    after `F` goes normal; here only the function's run is read. -/
theorem piHeadPrefix {Γ : LCtxA} {T : ExprA} :
    ∀ {a Na : ExprA}, TmChainA E I n Γ T a Na → ∀ {F x : ExprA},
      a = .app F x → hStepFnA E I.fn Γ Na = none → ∃ Nf, RedTo E I Γ F Nf := by
  intro a Na c
  induction c with
  | refl e he =>
      intro F x heq hn
      subst heq
      exact ⟨F, 0, whnfA_of_normal E I.fn Γ 0 F (hStepFnA_app_none_head E I.fn Γ hn)⟩
  | cons e a' N he hs t ih =>
      intro F x heq hn
      subst heq
      have hstep : hStepFnA E I.fn Γ (.app F x) = some a' := tyHRedA_hStep hs
      cases hF : hStepFnA E I.fn Γ F with
      | none => exact ⟨F, 0, whnfA_of_normal E I.fn Γ 0 F hF⟩
      | some g =>
          have hg : hStepFnA E I.fn Γ (.app F x) = some (.app g x) :=
            hStepFnA_app_head E I.fn Γ x hF
          rw [hg] at hstep
          cases hstep
          obtain ⟨Nf, fuel, hf⟩ := ih rfl hn
          exact ⟨Nf, fuel + 1, by simp only [whnfA]; rw [hF]; exact hf⟩

/-- iterate wall 3's typed head step along a `whnfA` run: every step a π-typed
    term takes is a `TyHRedA` at the π (`hpiStep` supplies each step, subject
    reduction's `tyHRedA_hasTy_right` retypes the reduct), so the computation is
    a typed chain at the π. -/
theorem whnfA_typedPi {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    (hpiStep : ∀ {e e' : ExprA}, HasTyA E I n Γ e (.pi D u C v) →
      hStepFnA E I.fn Γ e = some e' → Nonempty (TyHRedA E I n Γ e e' (.pi D u C v))) :
    (fuel : Nat) → {e w : ExprA} → HasTyA E I n Γ e (.pi D u C v) →
      whnfA E I.fn Γ fuel e = some w →
      Nonempty (TmChainA E I n Γ (.pi D u C v) e w)
  | 0, e, w, he, hw => by
      simp only [whnfA] at hw
      split at hw
      · cases hw
        exact ⟨.refl _ he⟩
      · cases hw
  | fuel + 1, e, w, he, hw => by
      simp only [whnfA] at hw
      split at hw
      · next e' hs =>
          obtain ⟨hs'⟩ := hpiStep he hs
          obtain ⟨t⟩ := whnfA_typedPi hpiStep fuel (tyHRedA_hasTy_right hs') hw
          exact ⟨.cons _ _ _ he hs' t⟩
      · next _ =>
          cases hw
          exact ⟨.refl _ he⟩

/-- the fam clause's chains: the fixed point's two disjuncts already carry them
    at the carrier; the clause's whnf conversion retypes them at the type. Factored
    out so the clause's implicit spine data stay inferable from `hA`/`hab`. -/
theorem fam_chain_pair {Γ : LCtxA} {A : ExprA} {r : Nat} {ls : List Level}
    {ps is : List ExprA} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {a b : ExprA}
    (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
    (hab : LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) []
      (foldAppsA (.const r ls) (ps ++ is)) a b) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none := by
  have hcA : Nonempty (TyConvA E I n Γ (foldAppsA (.const r ls) (ps ++ is)) A) :=
    tyConvA_symm_ne (whTyA_tyConv hA)
  rcases (LfpWA.unfold famPhiWA_mono hab).2 with
    ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h4', h5,
      hT1, hT1', hFC, hp₁, hp₂, hTa, hTb, hnNa, hnNb, hArgs, hCv₁, hCv₂⟩ |
    ⟨N, N', hNa, hNb, hSa, hSb⟩
  · exact ⟨_, tyHRedStarA_retype hcA hTa, hnNa, _, tyHRedStarA_retype hcA hTb, hnNb⟩
  · exact ⟨_, tyHRedStarA_retype hcA hNa, hSa.1, _, tyHRedStarA_retype hcA hNb, hSb.1⟩

/-! ### `lrRelA_chain_env`: `hstuck` environment-wide, `hnopi` gone -/

/-- **S1-c**: `lrRelA_chain` at a context-independent `hstuck` (wall 2), with the
    π arm closed by the escape — `hnopi` is gone. The rec's motive carries the
    context well-formedness (`Nonempty`, so `WkOkA` supplies it) and the key, so
    the codomain's induction hypothesis re-keys them at `D :: Γ`:

    * `hstuck` — the S1-b datum, now stated for every context / type / pair /
      normal form: at a stuck normal form of the type, the related pair carries
      the chains. Re-keyed at the codomain's context inside the π arm.
    * `hkey` — the clause-keyed premise, unchanged in shape: at the type's
      normal form, either not a proposition or stuck. At the codomain it is
      rebuilt by `hkey_of_sortTy` from the π clause's own `hCty` and the
      codomain's non-Prop-ness (wall 1's route).
    * `hfamkey` — wall 1's measured residual: the family-application face of the
      codomain's key, keyed at the declared sort like `hkey_of_sortTy` takes it.
    * `hpiStep` — wall 3's residual: step-completeness at a non-Prop π in a
      general environment (`hStepFnA_typedPi` discharges it under the three
      step-clean profile conditions).

    The π arm pushes the fresh variable through `LRRelA_bvar`, reads
    `RC`'s Kripke application at `bvar 0`, extracts the application's chain by
    `ihC` at the re-keyed motive, takes the function's `whnfA` run as the
    chain's head prefix (`piHeadPrefix`, determinism + `hStepFnA_app_head`),
    un-weakens it (`redTo_wk_rev`), and retypes the result at the type
    (`tyHRedStarA_retype` along the whnf conversion).

    KNOWN LIMITATION (`hstuck`'s circularity, cc AMEND on #6261): the
    environment-wide `hstuck` is demanded at every type, so W-APP cannot
    discharge it — the chain it would need to justify `hstuck` at `f`'s π
    type is produced only by this theorem. S1-d must restructure `hstuck`
    (bounded in the rec motive, or quantified over the types reached inside
    `A`'s `TyKA` derivation); until then W-APP cannot consume this theorem
    as stated. -/
theorem lrRelA_chain_env {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I)
    (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {k : Nat} {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {A a b : ExprA}
    (hstuck : ∀ {Γ' : LCtxA} {A' a' b' N' : ExprA}, CtxWfA E I n Γ' →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' →
      Nonempty (HasTyA E I n Γ' a' N') → Nonempty (HasTyA E I n Γ' b' N') →
      Nonempty (ConvA E I n Γ' a' b' N') →
      ∃ Na, TyHRedStarA E I n Γ' a' Na A' ∧ hStepFnA E I.fn Γ' Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ' b' Nb A' ∧ hStepFnA E I.fn Γ' Nb = none)
    (hkey : ∀ {N : ExprA}, WhTyA E I n Γ A N → hStepFnA E I.fn Γ N = none →
      ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N)
    (hfamkey : ∀ {Γ' : LCtxA} {X' N' : ExprA} {v' : Level} {r : Nat} {ls : List Level}
      {xs : List ExprA} {m : CheckedMemberA}, CtxWfA E I n Γ' →
      HasTyA E I n Γ' X' (.sort v') → isZero v' = false → WhTyA E I n Γ' X' N' →
      hStepFnA E I.fn Γ' N' = none → N' = foldAppsA (.const r ls) xs →
      E.members r = some m → m.mclass = .inductiveM → ¬ IsPropTy E I Γ' N')
    (hpiStep : ∀ {Γ' : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
      {e e' : ExprA}, CtxWfA E I n Γ' → isZero v = false →
      HasTyA E I n Γ' e (.pi D u C v) → hStepFnA E I.fn Γ' e = some e' →
      Nonempty (TyHRedA E I n Γ' e e' (.pi D u C v)))
    (hrel : LRRelA E I n ρ₀ k Γ A a b) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none := by
  obtain ⟨R, hRK, hab⟩ := hrel
  rw [LRTyA_eq] at hRK
  refine TyKA.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ' T' RT' _ =>
      Nonempty (CtxWfA E I n Γ') →
      (∀ {N' : ExprA}, WhTyA E I n Γ' T' N' → hStepFnA E I.fn Γ' N' = none →
        ¬ IsPropTy E I Γ' N' ∨ StuckA E I Γ' N') →
      ∀ a' b' : ExprA, RT' a' b' →
        ∃ Na, TyHRedStarA E I n Γ' a' Na T' ∧ hStepFnA E I.fn Γ' Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ' b' Nb T' ∧ hStepFnA E I.fn Γ' Nb = none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hRK ⟨hΓ⟩ hkey a b hab
  · exact fun _ _ _ _ _ => True.intro
  · exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  · exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  · exact fun _ _ _ _ _ => True.intro
  · exact fun hA hn hP hΓx hk a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      rcases hk hA hn with hnp' | hst
      · exact absurd hP hnp'
      · exact hstuck hΓ' hA hst hab.1 hab.2.1 hab.2.2
  · exact fun hA hz hk hΓx hkey' a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      rename_i l
      obtain ⟨_, ⟨Ra, hRa⟩, ⟨Rb, hRb⟩, hta, htb, _⟩ := hab
      have hTa' : LRTyA E I n ρ₀ (ht ρ₀ l) _ a' Ra := hRa
      have hTb' : LRTyA E I n ρ₀ (ht ρ₀ l) _ b' Rb := hRb
      rw [LRTyA_eq] at hTa' hTb'
      obtain ⟨Na, whNa, hnNa⟩ := tyKA_whnf hTa'
      obtain ⟨Nb, whNb, hnNb⟩ := tyKA_whnf hTb'
      obtain ⟨cha, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNa hnNa hta hA
      obtain ⟨chb, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNb hnNb htb hA
      exact ⟨Na, cha, hnNa, Nb, chb, hnNb⟩
  · exact fun hA hz hΓx hkey' a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      obtain ⟨⟨Na, whNa, hTa⟩, ⟨Nb, whNb, hTb⟩, hta, htb, _, _⟩ := hab
      obtain ⟨cha, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNa hTa.1 hta hA
      obtain ⟨chb, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNb hTb.1 htb hA
      exact ⟨Na, cha, hTa.1, Nb, chb, hTb.1⟩
  · exact fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq hΓx hkey' f g hab => by
      rename_i Γ A D C u v
      obtain ⟨hΓ'⟩ := hΓx
      have hzv : isZero v = false := by
        cases hz : isZero v with
        | false => rfl
        | true => exact absurd ((isPropTy_pi_iff E I Γ D u C v).mpr hz) hnp
      have hΓD : Nonempty (CtxWfA E I n (.assumption D :: Γ)) :=
        hDty.elim fun t => ⟨.assumption hΓ' t⟩
      have hρ₀ : WkOkA E I n [(.assumption D, 0)] Γ :=
        ⟨⟨Nat.zero_le _, trivial⟩, hΓD⟩
      have hT'eq : instantiate0A (.bvar 0)
          (wkExprA (WkSpecA.ub [(.assumption D, 0)]) C) = C :=
        instantiate0A_bvar0_liftA C
      have hCty' : Nonempty (HasTyA E I n (wkCtxA [(.assumption D, 0)] Γ)
          (instantiate0A (.bvar 0) (wkExprA (WkSpecA.ub [(.assumption D, 0)]) C))
          (.sort v)) := by
        show Nonempty (HasTyA E I n (.assumption D :: Γ) _ (.sort v))
        rw [hT'eq]
        exact hCty
      have hkeyC : ∀ {N' : ExprA}, WhTyA E I n (wkCtxA [(.assumption D, 0)] Γ)
          (instantiate0A (.bvar 0) (wkExprA (WkSpecA.ub [(.assumption D, 0)]) C)) N' →
          hStepFnA E I.fn (wkCtxA [(.assumption D, 0)] Γ) N' = none →
          ¬ IsPropTy E I (wkCtxA [(.assumption D, 0)] Γ) N' ∨
            StuckA E I (wkCtxA [(.assumption D, 0)] Γ) N' :=
        fun hN' hn' => hCty'.elim fun hCt => hΓD.elim fun hΓD' =>
          hkey_of_sortTy hE hI hIS hEN hNC hR hS hρ hΓD' hfamkey hCt hzv hN' hn'
      have hxv : lookupValueA (wkCtxA [(.assumption D, 0)] Γ) 0 = none :=
        lookupValueA_cons_zero_assumption D Γ
      have hDx : ∃ R', LRTyA E I n ρ₀ k (wkCtxA [(.assumption D, 0)] Γ)
          (wkExprA [(.assumption D, 0)] D) R' :=
        ⟨RD [(.assumption D, 0)], by rw [LRTyA_eq]; exact hD _ hρ₀⟩
      have htx : Nonempty (HasTyA E I n (wkCtxA [(.assumption D, 0)] Γ) (.bvar 0)
          (wkExprA [(.assumption D, 0)] D)) := by
        show Nonempty (HasTyA E I n (.assumption D :: Γ) (.bvar 0) (liftA 0 1 D))
        exact (hasTyA_wk_ne hE hI [(.assumption D, 0)] ⟨Nat.zero_le _, trivial⟩ hDty).elim
          fun t => ⟨.bvar _ 0 _ _ (lookupTypeA_cons_zero_assumption D Γ) t⟩
      have hxrel : LRRelA E I n ρ₀ k (wkCtxA [(.assumption D, 0)] Γ)
          (wkExprA [(.assumption D, 0)] D) (.bvar 0) (.bvar 0) :=
        LRRelA_bvar hE hI (iotaConstHeadA_of_recHead hR) hxv hDx htx
      have hRD : RD [(.assumption D, 0)] (.bvar 0) (.bvar 0) :=
        LRRelA.at hxrel (by rw [LRTyA_eq]; exact hD _ hρ₀)
      have happR : RC [(.assumption D, 0)] (.bvar 0)
          (.app (wkExprA [(.assumption D, 0)] f) (.bvar 0))
          (.app (wkExprA [(.assumption D, 0)] g) (.bvar 0)) :=
        hab.1 _ hρ₀ _ _ hRD
      obtain ⟨Na, cha, hnNa, Nb, chb, hnNb⟩ :=
        ihC _ hρ₀ (.bvar 0) (.bvar 0) hRD hΓD hkeyC _ _ happR
      obtain ⟨hf⟩ := hab.2.1
      obtain ⟨hg⟩ := hab.2.2.1
      obtain ⟨tcha⟩ := cha
      obtain ⟨Nf, hfred⟩ := piHeadPrefix tcha rfl hnNa
      obtain ⟨Nf', _, hfred'⟩ := redTo_wk_rev hE hI Γ [(.assumption D, 0)]
        ⟨Nat.zero_le _, trivial⟩ hfred
      obtain ⟨fuelf, hwf⟩ := hfred'
      have hnf' : hStepFnA E I.fn Γ Nf' = none :=
        whnfA_normal E I.fn Γ fuelf f Nf' hwf
      obtain ⟨chf⟩ := whnfA_typedPi (fun {e e'} he hstep => hpiStep hΓ' hzv he hstep)
        fuelf hf hwf
      obtain ⟨tchb⟩ := chb
      obtain ⟨Ng, hgred⟩ := piHeadPrefix tchb rfl hnNb
      obtain ⟨Ng', _, hgred'⟩ := redTo_wk_rev hE hI Γ [(.assumption D, 0)]
        ⟨Nat.zero_le _, trivial⟩ hgred
      obtain ⟨fuelg, hwg⟩ := hgred'
      have hng' : hStepFnA E I.fn Γ Ng' = none :=
        whnfA_normal E I.fn Γ fuelg g Ng' hwg
      obtain ⟨chg⟩ := whnfA_typedPi (fun {e e'} he hstep => hpiStep hΓ' hzv he hstep)
        fuelg hg hwg
      exact ⟨Nf', tyHRedStarA_retype (tyConvA_symm_ne (whTyA_tyConv hA)) ⟨chf⟩, hnf',
        Ng', tyHRedStarA_retype (tyConvA_symm_ne (whTyA_tyConv hA)) ⟨chg⟩, hng'⟩
  · intro Γ' A' r ls ps is m u u₀ hA
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΓx hkey' a' b' hab
    exact fam_chain_pair hA hab
  · exact fun hA hN hΓx hkey' a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      exact hstuck hΓ' hA hN hab.1 hab.2.1 hab.2.2

/-- the step-clean instantiation (cc AMEND on #6261): `hpiStep` discharged by
    `hStepFnA_typedPi` at the three step-clean profile conditions — every
    member body opaque, the iota function everywhere `none`, no recursor
    members. The remaining premises (`hstuck`, `hkey`, `hfamkey`) are the
    open obligations S1-d inherits, with `hstuck`'s circularity noted on
    `lrRelA_chain_env`. -/
theorem lrRelA_chain_env_stepClean {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I)
    (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {k : Nat} {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    (hnobody : ∀ r m, E.members r = some m → m.bodyA = none)
    (hiotaNone : ∀ e, I.fn e = none)
    (hnorec : ∀ r m, E.members r = some m → m.mclass ≠ .recursorM)
    {A a b : ExprA}
    (hstuck : ∀ {Γ' : LCtxA} {A' a' b' N' : ExprA}, CtxWfA E I n Γ' →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' →
      Nonempty (HasTyA E I n Γ' a' N') → Nonempty (HasTyA E I n Γ' b' N') →
      Nonempty (ConvA E I n Γ' a' b' N') →
      ∃ Na, TyHRedStarA E I n Γ' a' Na A' ∧ hStepFnA E I.fn Γ' Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ' b' Nb A' ∧ hStepFnA E I.fn Γ' Nb = none)
    (hkey : ∀ {N : ExprA}, WhTyA E I n Γ A N → hStepFnA E I.fn Γ N = none →
      ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N)
    (hfamkey : ∀ {Γ' : LCtxA} {X' N' : ExprA} {v' : Level} {r : Nat} {ls : List Level}
      {xs : List ExprA} {m : CheckedMemberA}, CtxWfA E I n Γ' →
      HasTyA E I n Γ' X' (.sort v') → isZero v' = false → WhTyA E I n Γ' X' N' →
      hStepFnA E I.fn Γ' N' = none → N' = foldAppsA (.const r ls) xs →
      E.members r = some m → m.mclass = .inductiveM → ¬ IsPropTy E I Γ' N')
    (hrel : LRRelA E I n ρ₀ k Γ A a b) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none :=
  lrRelA_chain_env hE hI hIS hEN hNC hR hS hρ hΓ hstuck hkey hfamkey
    (fun hΓ' hz he hstep =>
      hStepFnA_typedPi hE hI hIS hEN hNC hR hS hρ hΓ' hnobody hiotaNone hnorec _ hz he hstep)
    hrel

#print axioms piHeadPrefix
#print axioms whnfA_typedPi
#print axioms lrRelA_chain_env
#print axioms lrRelA_chain_wf
#print axioms lrRelA_chain_env_stepClean
#print axioms whTyChainA_sort_end
#print axioms hkey_of_sortTy
#print axioms hasTyA_headSpine_nil
#print axioms hasTyA_sort_notPi
#print axioms hasTyA_pi_notPi
#print axioms fam_chain_pair
#print axioms hStepFnA_app_none_head
#print axioms hStepFnA_typedPi

#print axioms whTyChainA_tmChainA
#print axioms whTyA_tyHRedStarA
#print axioms whnfChainA_at
#print axioms lrRelA_chain
#print axioms pinFamF1_small
#print axioms pinFamF1_sem
#print axioms pinFamF1_chain

end S1c

/-!
## S1-d — `hstuck` in bounded form, and the walls

**Item 1 — the bound.** `TyInKA d Γ' A' R'` reads "a `TyKA` node at
`(Γ', A', R')` is reached inside `d`". `tyKA_chain_sub` restates
`lrRelA_chain_env`'s extraction with `hstuck` quantified over
`TyInKA d` — the types reached inside `A`'s own `TyKA` derivation —
rather than environment-wide over every `WhTyA`/`StuckA` pair. The
circular demand is gone: at a `pi` node the extraction's only live
recursive call is `ihC`, so the rec motive carries a `sub`-transformer
`TyInKA d' ⊆ TyInKA d`, and the `hstuck` premise is invoked only at
nodes `sub` can actually reach — the root (reflexively) and Π-codomain
instances (`piCod`), which is exactly what `TyInKA` covers. The domain
children (`hD`), the `EqKA` children (`hCeq`) and the family fields are
NOT members: `lrRelA_chain_env`'s proof never routes `sub` through them
(its `ihD`/`ihCeq`/family IHs are unapplied), so no `hstuck` instance is
ever constructed there. Widening `TyInKA`'s coverage is additive — a
future arm threading `sub` through `hD`, `hCeq` or family fields adds the
corresponding constructor and weakens the premise accordingly.

For W-APP's consumption: `f`'s chain at `π` comes from
`tyKA_chain_sub d_f`, whose `hstuck` is demanded only at `TyInKA d_f` —
`d_f`'s own reached nodes — not at the Π type the wall is proving (that
Π is `d_f`'s *root*, a non-stuck node, so `hstuck` is never invoked at
it). The env-wide reading demanded `hstuck` at every type including the
very Π type under construction; the bounded reading demands it only
inside `d_f`.

**The walls.** Each wall is a chain *step*: the shape-specific
`TyHRedA` constructor followed by a component chain that `hstuck` (or
the relation) must supply. The derivable fragments:

- **W-VAR** (`tyHRedStarA_bvar_zetaLocal`): `lookupValueA Γ i = some v`
  gives `.bvar i →[zetaLocal] v`; `bvar i`'s chain is that step plus
  `v`'s chain. The residual obligation is `v`'s chain — arbitrary typed,
  it is the stuck-clause datum at `A`, exactly what the `hstuck` premise
  is for.
- **W-DELTA** (`tyHRedStarA_const_delta`): a transparent member gives
  `.const r ls →[delta] instantiateLevelsA ls b`; the constant's chain
  is that step plus the body instance's chain — the residual is the
  body's chain (`EnvSemA` relates the constant to itself, not the body;
  the body's typing is `EnvWfA` content, S1-b's wall).
- **W-APP** (`tyHRedStarA_app_head`): a head chain `f →* Nf` at `T₀`
  lifts through `TyHRedA.app` to `.app f a →* .app Nf a` at the codomain
  instance; `hStepFnA_app_none` closes the tail when `Nf` is a non-λ
  non-recursor neutral (ι refusing). `f`'s chain is the part
  `tyKA_chain_sub` produces at `d_f`; the `Nf = .lam` tail (`body[a]`'s
  chain) is the residual stuck datum.
-/

section S1d

/-- `TyInKA d Γ' A' R'`: a `TyKA` node at `(Γ', A', R')` reached inside
    `d` through the positions the extraction threads `sub` through —
    reflexively at the root, and through `TyKA.pi`'s codomain child
    (`piCod`; the π arm's `ihC` recursion). -/
inductive TyInKA {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} :
    ∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop},
    TyKA E I n ρ₀ k LE LT Γ A R → LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop
  | refl {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
      (d : TyKA E I n ρ₀ k LE LT Γ A R) : TyInKA d Γ A R
  | piCod {Γ : LCtxA} {A D C : ExprA} {u v : Level}
      {RD : WkSpecA → ExprA → ExprA → Prop}
      {RC : WkSpecA → ExprA → ExprA → ExprA → Prop}
      {hA : WhTyA E I n Γ A (.pi D u C v)}
      {hnp : ¬ IsPropTy E I Γ (.pi D u C v)}
      {hDty : Nonempty (HasTyA E I n Γ D (.sort u))}
      {hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v))}
      {hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ)}
      (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
      {hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))}
      {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop}
      {ρ : WkSpecA} {hok : WkOkA E I n ρ Γ} {a a' : ExprA} {hr : RD ρ a a'} :
      TyInKA (hC ρ hok a a' hr) Γ' A' R' →
      TyInKA (TyKA.pi hA hnp hDty hCty RD hD RC hC hCeq) Γ' A' R'

/-- **S1-d Item 1 — `hstuck`, bounded.** `lrRelA_chain_env` restated with
    `hstuck` quantified over `TyInKA d` — the types reached inside the
    derivation being eliminated, transported up to the root `d` by the
    `sub` transformer the motive carries — instead of environment-wide.
    The extraction's shape is unchanged; each arm gains the transformer
    as a leading argument and the π arm threads it into `ihC` through
    `piCod`. `hkey`/`hfamkey`/`hpiStep` are unchanged. -/
theorem tyKA_chain_sub {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I)
    (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {k : Nat}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (d : TyKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j) Γ A R)
    (hstuck : ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop} {a' b' N' : ExprA},
      TyInKA d Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' → R' a' b' →
      ∃ Na, TyHRedStarA E I n Γ' a' Na A' ∧ hStepFnA E I.fn Γ' Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ' b' Nb A' ∧ hStepFnA E I.fn Γ' Nb = none)
    (hkey : ∀ {N : ExprA}, WhTyA E I n Γ A N → hStepFnA E I.fn Γ N = none →
      ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N)
    (hfamkey : ∀ {Γ' : LCtxA} {X' N' : ExprA} {v' : Level} {r : Nat} {ls : List Level}
      {xs : List ExprA} {m : CheckedMemberA}, CtxWfA E I n Γ' →
      HasTyA E I n Γ' X' (.sort v') → isZero v' = false → WhTyA E I n Γ' X' N' →
      hStepFnA E I.fn Γ' N' = none → N' = foldAppsA (.const r ls) xs →
      E.members r = some m → m.mclass = .inductiveM → ¬ IsPropTy E I Γ' N')
    (hpiStep : ∀ {Γ' : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
      {e e' : ExprA}, CtxWfA E I n Γ' → isZero v = false →
      HasTyA E I n Γ' e (.pi D u C v) → hStepFnA E I.fn Γ' e = some e' →
      Nonempty (TyHRedA E I n Γ' e e' (.pi D u C v)))
    (hΓ : CtxWfA E I n Γ) {a b : ExprA} (hab : R a b) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none := by
  refine TyKA.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ' T' RT' d' =>
      (∀ {Γ'' : LCtxA} {A'' : ExprA} {R'' : ExprA → ExprA → Prop},
        TyInKA d' Γ'' A'' R'' → TyInKA d Γ'' A'' R'') →
      Nonempty (CtxWfA E I n Γ') →
      (∀ {N' : ExprA}, WhTyA E I n Γ' T' N' → hStepFnA E I.fn Γ' N' = none →
        ¬ IsPropTy E I Γ' N' ∨ StuckA E I Γ' N') →
      ∀ a' b' : ExprA, RT' a' b' →
        ∃ Na, TyHRedStarA E I n Γ' a' Na T' ∧ hStepFnA E I.fn Γ' Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ' b' Nb T' ∧ hStepFnA E I.fn Γ' Nb = none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ d (fun h => h) ⟨hΓ⟩ hkey a b hab
  · exact fun _ _ _ _ _ => True.intro
  · exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  · exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro
  · exact fun _ _ _ _ _ => True.intro
  · exact fun hA hn hP hsub hΓx hk a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      rcases hk hA hn with hnp' | hst
      · exact absurd hP hnp'
      · exact hstuck (hsub (TyInKA.refl _)) ⟨hΓ'⟩ hA hst hab
  · exact fun hA hz hk hsub hΓx hkey' a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      rename_i l
      obtain ⟨_, ⟨Ra, hRa⟩, ⟨Rb, hRb⟩, hta, htb, _⟩ := hab
      have hTa' : LRTyA E I n ρ₀ (ht ρ₀ l) _ a' Ra := hRa
      have hTb' : LRTyA E I n ρ₀ (ht ρ₀ l) _ b' Rb := hRb
      rw [LRTyA_eq] at hTa' hTb'
      obtain ⟨Na, whNa, hnNa⟩ := tyKA_whnf hTa'
      obtain ⟨Nb, whNb, hnNb⟩ := tyKA_whnf hTb'
      obtain ⟨cha, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNa hnNa hta hA
      obtain ⟨chb, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNb hnNb htb hA
      exact ⟨Na, cha, hnNa, Nb, chb, hnNb⟩
  · exact fun hA hz hsub hΓx hkey' a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      obtain ⟨⟨Na, whNa, hTa⟩, ⟨Nb, whNb, hTb⟩, hta, htb, _, _⟩ := hab
      obtain ⟨cha, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNa hTa.1 hta hA
      obtain ⟨chb, _⟩ := whnfChainA_at hE hI hIS hEN hNC hR hS hρ hΓ' whNb hTb.1 htb hA
      exact ⟨Na, cha, hTa.1, Nb, chb, hTb.1⟩
  · exact fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq hsub hΓx hkey' f g hab => by
      rename_i Γ A D C u v
      obtain ⟨hΓ'⟩ := hΓx
      have hzv : isZero v = false := by
        cases hz : isZero v with
        | false => rfl
        | true => exact absurd ((isPropTy_pi_iff E I Γ D u C v).mpr hz) hnp
      have hΓD : Nonempty (CtxWfA E I n (.assumption D :: Γ)) :=
        hDty.elim fun t => ⟨.assumption hΓ' t⟩
      have hρ₀ : WkOkA E I n [(.assumption D, 0)] Γ :=
        ⟨⟨Nat.zero_le _, trivial⟩, hΓD⟩
      have hT'eq : instantiate0A (.bvar 0)
          (wkExprA (WkSpecA.ub [(.assumption D, 0)]) C) = C :=
        instantiate0A_bvar0_liftA C
      have hCty' : Nonempty (HasTyA E I n (wkCtxA [(.assumption D, 0)] Γ)
          (instantiate0A (.bvar 0) (wkExprA (WkSpecA.ub [(.assumption D, 0)]) C))
          (.sort v)) := by
        show Nonempty (HasTyA E I n (.assumption D :: Γ) _ (.sort v))
        rw [hT'eq]
        exact hCty
      have hkeyC : ∀ {N' : ExprA}, WhTyA E I n (wkCtxA [(.assumption D, 0)] Γ)
          (instantiate0A (.bvar 0) (wkExprA (WkSpecA.ub [(.assumption D, 0)]) C)) N' →
          hStepFnA E I.fn (wkCtxA [(.assumption D, 0)] Γ) N' = none →
          ¬ IsPropTy E I (wkCtxA [(.assumption D, 0)] Γ) N' ∨
            StuckA E I (wkCtxA [(.assumption D, 0)] Γ) N' :=
        fun hN' hn' => hCty'.elim fun hCt => hΓD.elim fun hΓD' =>
          hkey_of_sortTy hE hI hIS hEN hNC hR hS hρ hΓD' hfamkey hCt hzv hN' hn'
      have hxv : lookupValueA (wkCtxA [(.assumption D, 0)] Γ) 0 = none :=
        lookupValueA_cons_zero_assumption D Γ
      have hDx : ∃ R', LRTyA E I n ρ₀ k (wkCtxA [(.assumption D, 0)] Γ)
          (wkExprA [(.assumption D, 0)] D) R' :=
        ⟨RD [(.assumption D, 0)], by rw [LRTyA_eq]; exact hD _ hρ₀⟩
      have htx : Nonempty (HasTyA E I n (wkCtxA [(.assumption D, 0)] Γ) (.bvar 0)
          (wkExprA [(.assumption D, 0)] D)) := by
        show Nonempty (HasTyA E I n (.assumption D :: Γ) (.bvar 0) (liftA 0 1 D))
        exact (hasTyA_wk_ne hE hI [(.assumption D, 0)] ⟨Nat.zero_le _, trivial⟩ hDty).elim
          fun t => ⟨.bvar _ 0 _ _ (lookupTypeA_cons_zero_assumption D Γ) t⟩
      have hxrel : LRRelA E I n ρ₀ k (wkCtxA [(.assumption D, 0)] Γ)
          (wkExprA [(.assumption D, 0)] D) (.bvar 0) (.bvar 0) :=
        LRRelA_bvar hE hI (iotaConstHeadA_of_recHead hR) hxv hDx htx
      have hRD : RD [(.assumption D, 0)] (.bvar 0) (.bvar 0) :=
        LRRelA.at hxrel (by rw [LRTyA_eq]; exact hD _ hρ₀)
      have happR : RC [(.assumption D, 0)] (.bvar 0)
          (.app (wkExprA [(.assumption D, 0)] f) (.bvar 0))
          (.app (wkExprA [(.assumption D, 0)] g) (.bvar 0)) :=
        hab.1 _ hρ₀ _ _ hRD
      obtain ⟨Na, cha, hnNa, Nb, chb, hnNb⟩ :=
        ihC _ hρ₀ (.bvar 0) (.bvar 0) hRD
          (fun {Γ'' : LCtxA} {A'' : ExprA} {R'' : ExprA → ExprA → Prop}
              (h : TyInKA (hC _ hρ₀ (.bvar 0) (.bvar 0) hRD) Γ'' A'' R'') =>
            hsub (@TyInKA.piCod E I n ρ₀ k _ _ Γ A D C u v RD RC hA hnp hDty hCty hD
              hC hCeq Γ'' A'' R'' _ hρ₀ (.bvar 0) (.bvar 0) hRD h)) hΓD hkeyC _ _ happR
      obtain ⟨hf⟩ := hab.2.1
      obtain ⟨hg⟩ := hab.2.2.1
      obtain ⟨tcha⟩ := cha
      obtain ⟨Nf, hfred⟩ := piHeadPrefix tcha rfl hnNa
      obtain ⟨Nf', _, hfred'⟩ := redTo_wk_rev hE hI Γ [(.assumption D, 0)]
        ⟨Nat.zero_le _, trivial⟩ hfred
      obtain ⟨fuelf, hwf⟩ := hfred'
      have hnf' : hStepFnA E I.fn Γ Nf' = none :=
        whnfA_normal E I.fn Γ fuelf f Nf' hwf
      obtain ⟨chf⟩ := whnfA_typedPi (fun {e e'} he hstep => hpiStep hΓ' hzv he hstep)
        fuelf hf hwf
      obtain ⟨tchb⟩ := chb
      obtain ⟨Ng, hgred⟩ := piHeadPrefix tchb rfl hnNb
      obtain ⟨Ng', _, hgred'⟩ := redTo_wk_rev hE hI Γ [(.assumption D, 0)]
        ⟨Nat.zero_le _, trivial⟩ hgred
      obtain ⟨fuelg, hwg⟩ := hgred'
      have hng' : hStepFnA E I.fn Γ Ng' = none :=
        whnfA_normal E I.fn Γ fuelg g Ng' hwg
      obtain ⟨chg⟩ := whnfA_typedPi (fun {e e'} he hstep => hpiStep hΓ' hzv he hstep)
        fuelg hg hwg
      exact ⟨Nf', tyHRedStarA_retype (tyConvA_symm_ne (whTyA_tyConv hA)) ⟨chf⟩, hnf',
        Ng', tyHRedStarA_retype (tyConvA_symm_ne (whTyA_tyConv hA)) ⟨chg⟩, hng'⟩
  · intro Γ' A' r ls ps is m u u₀ hA
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsub hΓx hkey' a' b' hab
    exact fam_chain_pair hA hab
  · exact fun hA hN hsub hΓx hkey' a' b' hab => by
      obtain ⟨hΓ'⟩ := hΓx
      exact hstuck (hsub (TyInKA.refl _)) ⟨hΓ'⟩ hA hN hab

/-- the `LRRelA` form of `tyKA_chain_sub`: the root derivation is `hrel`'s
    `LRTyA`, and `hstuck` is bounded by its `TyInKA`. -/
theorem lrRelA_chain_env_sub {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I)
    (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {k : Nat} {Γ : LCtxA} (hΓ : CtxWfA E I n Γ)
    {A a b : ExprA} (hrel : LRRelA E I n ρ₀ k Γ A a b)
    (hstuck : ∀ {R' : ExprA → ExprA → Prop} (d : TyKA E I n ρ₀ k
        (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j) Γ A R'),
      ∀ {Γ' : LCtxA} {A' : ExprA} {R'' : ExprA → ExprA → Prop} {a' b' N' : ExprA},
        TyInKA d Γ' A' R'' → Nonempty (CtxWfA E I n Γ') →
        WhTyA E I n Γ' A' N' → StuckA E I Γ' N' → R'' a' b' →
        ∃ Na, TyHRedStarA E I n Γ' a' Na A' ∧ hStepFnA E I.fn Γ' Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ' b' Nb A' ∧ hStepFnA E I.fn Γ' Nb = none)
    (hkey : ∀ {N : ExprA}, WhTyA E I n Γ A N → hStepFnA E I.fn Γ N = none →
      ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N)
    (hfamkey : ∀ {Γ' : LCtxA} {X' N' : ExprA} {v' : Level} {r : Nat} {ls : List Level}
      {xs : List ExprA} {m : CheckedMemberA}, CtxWfA E I n Γ' →
      HasTyA E I n Γ' X' (.sort v') → isZero v' = false → WhTyA E I n Γ' X' N' →
      hStepFnA E I.fn Γ' N' = none → N' = foldAppsA (.const r ls) xs →
      E.members r = some m → m.mclass = .inductiveM → ¬ IsPropTy E I Γ' N')
    (hpiStep : ∀ {Γ' : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
      {e e' : ExprA}, CtxWfA E I n Γ' → isZero v = false →
      HasTyA E I n Γ' e (.pi D u C v) → hStepFnA E I.fn Γ' e = some e' →
      Nonempty (TyHRedA E I n Γ' e e' (.pi D u C v))) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none := by
  obtain ⟨R, hRK, hab⟩ := hrel
  rw [LRTyA_eq] at hRK
  exact tyKA_chain_sub hE hI hIS hEN hNC hR hS hρ hRK (hstuck hRK) hkey hfamkey hpiStep hΓ hab

/-- **W-VAR** — the let-position variable's chain is one `zetaLocal` step
    to the stored value plus the value's own chain (the residual leaf
    obligation `hstuck` supplies). -/
theorem tyHRedStarA_bvar_zetaLocal {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {i : Nat} {A v N : ExprA}
    (hval : lookupValueA Γ i = some v) (hty : lookupTypeA Γ i = some A)
    (hv : HasTyA E I n Γ v A) (hbv : HasTyA E I n Γ (.bvar i) A)
    (hchain : TyHRedStarA E I n Γ v N A) :
    TyHRedStarA E I n Γ (.bvar i) N A :=
  tyHRedStarA_cons hbv (.zetaLocal Γ i A v hval hty hv) hchain

/-- **W-DELTA** — a transparent constant's chain is one `delta` step to
    the instantiated member body plus the body's own chain (the residual
    leaf obligation). -/
theorem tyHRedStarA_const_delta {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {r : Nat} {ls : List Level} {m : CheckedMemberA} {b N : ExprA}
    (hres : E.members r = some m) (hbody : m.bodyA = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyA E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA))
    (hc : HasTyA E I n Γ (.const r ls) (instantiateLevelsA ls m.mtypeA))
    (hchain : TyHRedStarA E I n Γ (instantiateLevelsA ls b) N
      (instantiateLevelsA ls m.mtypeA)) :
    TyHRedStarA E I n Γ (.const r ls) N (instantiateLevelsA ls m.mtypeA) :=
  tyHRedStarA_cons hc (.delta Γ r ls m b hres hbody htr hlen hwf hb) hchain

/-- **W-APP, the chain part** — a head chain `f →* Nf` at `T₀` lifts
    through `TyHRedA.app` to `.app f a →* .app Nf a` at the codomain
    instance `instantiate0A a B`; `f`'s chain is `tyKA_chain_sub d_f`'s
    output (its `hstuck` bounded to `TyInKA d_f`, consumable without
    circularity), and the `app Nf a` tail is `hStepFnA_app_none`'s
    guards — the `Nf = .lam` residual is the stuck datum. -/
def tmChainA_appHead {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {T₀ A B : ExprA} {u v w : Level} {a : ExprA}
    (hc : TyConvA E I n Γ T₀ (.pi A u B v))
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyA E I n Γ (instantiate0A a B) (.sort w))
    (ha : HasTyA E I n Γ a A) {f Nf : ExprA} :
    TmChainA E I n Γ T₀ f Nf →
    TmChainA E I n Γ (instantiate0A a B) (.app f a) (.app Nf a)
  | .refl _ h => .refl _ (.app Γ _ a A B u v w hB hTy (hasTyA_of_tyConvA h hc) ha)
  | .cons _ _ _ ha' hs t => .cons _ _ _ (.app Γ _ a A B u v w hB hTy
      (hasTyA_of_tyConvA ha' hc) ha)
      (.app Γ _ _ a A B _ u v w hs hc hB hTy ha) (tmChainA_appHead hc hB hTy ha t)

/-- `tmChainA_appHead` at the `TyHRedStarA` level. -/
theorem tyHRedStarA_app_head {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {T₀ A B f Nf : ExprA} {u v w : Level} {a : ExprA}
    (hc : TyConvA E I n Γ T₀ (.pi A u B v))
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyA E I n Γ (instantiate0A a B) (.sort w))
    (ha : HasTyA E I n Γ a A)
    (h : TyHRedStarA E I n Γ f Nf T₀) :
    TyHRedStarA E I n Γ (.app f a) (.app Nf a) (instantiate0A a B) :=
  h.elim fun t => ⟨tmChainA_appHead hc hB hTy ha t⟩

/-- **W-VAR, wall-shaped** — the let-variable's two chains reduce to the
    value's chain-endpoint (the residual datum; the `∃` shape matches
    `RcicAnnLRStuckFund`'s W-VAR goal exactly, with the endpoint shared). -/
theorem wallVar_chain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {i : Nat} {A v : ExprA}
    (hval : lookupValueA Γ i = some v) (hty : lookupTypeA Γ i = some A)
    (hv : HasTyA E I n Γ v A) (hbv : HasTyA E I n Γ (.bvar i) A)
    (hvchain : ∃ Nb, TyHRedStarA E I n Γ v Nb A ∧ hStepFnA E I.fn Γ Nb = none) :
    ∃ Na, TyHRedStarA E I n Γ (.bvar i) Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ v Nb A ∧ hStepFnA E I.fn Γ Nb = none :=
  let ⟨Nb, chv, hnv⟩ := hvchain
  ⟨Nb, tyHRedStarA_bvar_zetaLocal hval hty hv hbv chv, hnv, Nb, chv, hnv⟩

/-- **W-DELTA, wall-shaped** — the transparent constant's two chains
    reduce to the body instance's chain-endpoint. -/
theorem wallDelta_chain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {r : Nat} {ls : List Level} {m : CheckedMemberA} {b : ExprA}
    (hres : E.members r = some m) (hbody : m.bodyA = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : HasTyA E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA))
    (hc : HasTyA E I n Γ (.const r ls) (instantiateLevelsA ls m.mtypeA))
    (hbchain : ∃ Nb, TyHRedStarA E I n Γ (instantiateLevelsA ls b) Nb
        (instantiateLevelsA ls m.mtypeA) ∧ hStepFnA E I.fn Γ Nb = none) :
    ∃ Na, TyHRedStarA E I n Γ (.const r ls) Na (instantiateLevelsA ls m.mtypeA) ∧
      hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ (instantiateLevelsA ls b) Nb
        (instantiateLevelsA ls m.mtypeA) ∧ hStepFnA E I.fn Γ Nb = none :=
  let ⟨Nb, chb, hnb⟩ := hbchain
  ⟨Nb, tyHRedStarA_const_delta hres hbody htr hlen hwf hb hc chb, hnb, Nb, chb, hnb⟩

/-- **W-APP, wall-shaped** — the application's chain reduces to `f`'s
    head chain (the part `tyKA_chain_sub d_f` produces with `hstuck`
    bounded to `TyInKA d_f`, consumable without circularity) plus the
    `app Nf a` tail's normality — discharged by `hStepFnA_app_none`
    when `Nf` is a non-λ neutral at which neither ι nor the major arm
    fires (`structPosA`/`recAtMajorA`/`iota` refusing). The `Nf = .lam`
    endpoint is NOT in this lemma's scope: `hStepFnA_app_lam` makes
    `htail` unsatisfiable there (β fires); `wallApp_lam_chain` is the
    λ endpoint's own lemma. -/
theorem wallApp_chain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {T₀ A B f Nf : ExprA} {u v w : Level} {a : ExprA}
    (hc : TyConvA E I n Γ T₀ (.pi A u B v))
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyA E I n Γ (instantiate0A a B) (.sort w))
    (ha : HasTyA E I n Γ a A)
    (hf : TyHRedStarA E I n Γ f Nf T₀)
    (htail : hStepFnA E I.fn Γ (.app Nf a) = none) :
    ∃ Na, TyHRedStarA E I n Γ (.app f a) Na (instantiate0A a B) ∧
      hStepFnA E I.fn Γ Na = none :=
  ⟨_, tyHRedStarA_app_head hc hB hTy ha hf, htail⟩

end S1d

/-!
## S1-e — the λ endpoint, and `hstuck` composed from the walls

The `Nf = .lam` endpoint of W-APP: `hStepFnA_app_lam` fires β, so
`wallApp_chain`'s `htail` can never hold there — the λ endpoint's
chain continues through `body[a]` instead (`wallApp_lam_chain`).
-/

section S1e

/-- **W-APP at the λ endpoint** — `f` head-reduces to `.lam A u body`;
    the application's chain is the head lift, one `TyHRedA.beta` step
    to `instantiate0A a body`, then `body[a]`'s own chain (the named
    residual `hchain`). The λ's domain is `hc`'s π domain literally,
    so no π-injectivity is consumed; a convertible-domain λ is out of
    scope (the endpoint's shape is the premise's). -/
theorem wallApp_lam_chain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {T₀ A B body f : ExprA} {u v w : Level} {a : ExprA}
    (hc : TyConvA E I n Γ T₀ (.pi A u B v))
    (hA : HasTyA E I n Γ A (.sort u))
    (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
    (hTy : HasTyA E I n Γ (instantiate0A a B) (.sort w))
    (ha : HasTyA E I n Γ a A)
    (hbody : HasTyA E I n (.assumption A :: Γ) body B)
    (hred : HasTyA E I n Γ (instantiate0A a body) (instantiate0A a B))
    (hf : TyHRedStarA E I n Γ f (.lam A u body) T₀)
    (hchain : ∃ Nc, TyHRedStarA E I n Γ (instantiate0A a body) Nc
        (instantiate0A a B) ∧ hStepFnA E I.fn Γ Nc = none) :
    ∃ Na, TyHRedStarA E I n Γ (.app f a) Na (instantiate0A a B) ∧
      hStepFnA E I.fn Γ Na = none :=
  let ⟨Nc, chc, hnc⟩ := hchain
  let happ := tyHRedStarA_app_head hc hB hTy ha hf
  let hlamTy : HasTyA E I n Γ (.lam A u body) (.pi A u B v) :=
    .lam Γ A u body B v hA hB hbody
  let happTy : HasTyA E I n Γ (.app (.lam A u body) a) (instantiate0A a B) :=
    .app Γ (.lam A u body) a A B u v w hB hTy hlamTy ha
  let hstep : TyHRedA E I n Γ (.app (.lam A u body) a) (instantiate0A a body)
      (instantiate0A a B) :=
    .beta Γ A u body a B hA hbody ha hred
  let starβ : TyHRedStarA E I n Γ (.app (.lam A u body) a) (instantiate0A a body)
      (instantiate0A a B) :=
    tyHRedStarA_cons happTy hstep (tyHRedStarA_refl hred)
  ⟨Nc, tyHRedStarA_trans happ (tyHRedStarA_trans starβ chc), hnc⟩

/-- **S1-e step 3** — `TyInKA` membership carries the reached derivation:
    `refl` is the node itself, `piCod` recurses into the codomain child. -/
theorem tyInKA_extract {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k} {Γ' : LCtxA} {A' : ExprA}
    {R' : ExprA → ExprA → Prop} {Γ : LCtxA} {A : ExprA}
    {R : ExprA → ExprA → Prop} {d : TyKA E I n ρ₀ k LE LT Γ A R}
    (h : TyInKA d Γ' A' R') : Nonempty (TyKA E I n ρ₀ k LE LT Γ' A' R') := by
  induction h with
  | refl d => exact ⟨d⟩
  | piCod =>
    rename_i hsub ih
    exact ih

/-- a reached node at a whnf-stuck type carries the `stuck` clause's
    relation: `TyInKA` extracts the derivation, `TyKA_unique` identifies
    its relation with `TyKA.stuck`'s — the related pair's typings at `N'`
    and their conversion unpack below. -/
theorem tyInKA_stuck_rel {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    {d : TyKA E I n ρ₀ k LE LT Γ A R} {Γ' : LCtxA} {A' : ExprA}
    {R' : ExprA → ExprA → Prop} {N' : ExprA}
    (hin : TyInKA d Γ' A' R') (hA : WhTyA E I n Γ' A' N') (hN : StuckA E I Γ' N') :
    R' = (fun a b => Nonempty (HasTyA E I n Γ' a N') ∧
      Nonempty (HasTyA E I n Γ' b N') ∧ Nonempty (ConvA E I n Γ' a b N')) :=
  (tyInKA_extract hin).elim fun d' => TyKA_unique d' (.stuck hA hN)

/-- `hasTyA_const_gen` plus the member's arity and level bounds — the
    `TyHRedA.delta` step's data from the constant's typing alone. -/
theorem hasTyA_const_full {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    {Γ : LCtxA} → {r : Nat} → {ls : List Level} → {T : ExprA} →
    HasTyA E I n Γ (.const r ls) T →
    ∃ m, E.members r = some m ∧ ls.length = m.arity ∧ levelsBounded n ls = true ∧
      Nonempty (TyConvA E I n Γ (instantiateLevelsA ls m.mtypeA) T)
  | _, _, _, _, .const Γ _ _ m _ hres hlen hwf _ =>
      ⟨m, hres, hlen, hwf, ⟨.refl Γ _⟩⟩
  | _, _, _, _, .conv _ _ _ _ _ _ h hAl hlu hB hc => by
      obtain ⟨m, hm, hl, hw, ⟨t⟩⟩ := hasTyA_const_full h
      exact ⟨m, hm, hl, hw, ⟨tyConvA_snoc_conv t hAl hlu hB hc⟩⟩

/-- **the exhaustive face split, proved** — every `ExprA` constructor is
    either one of the five step shapes `hStepFnA` knows (`.bvar` under a
    let-binding, `.const` under a transparent member, `.app`, `.letE`,
    `.lit`) or head-normal outright (`.sort`/`.lam`/`.pi`, and the
    non-firing `.bvar`/`.const`/`.app` sub-cases). This replaces the
    `hdec` premise: the composer needs no classifier supplied, since the
    split is syntax. -/
theorem hStepFnA_cases (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (e : ExprA) :
    (∃ i, e = .bvar i) ∨ (∃ r ls, e = .const r ls) ∨
    (∃ f a, e = .app f a) ∨ (∃ A v body, e = .letE A v body) ∨
    (∃ t, e = .lit t) ∨ hStepFnA E iota Γ e = none := by
  cases e with
  | bvar i => exact .inl ⟨i, rfl⟩
  | sort _ => exact .inr (.inr (.inr (.inr (.inr rfl))))
  | const r ls => exact .inr (.inl ⟨r, ls, rfl⟩)
  | app f a => exact .inr (.inr (.inl ⟨f, a, rfl⟩))
  | lam _ _ _ => exact .inr (.inr (.inr (.inr (.inr rfl))))
  | pi _ _ _ _ => exact .inr (.inr (.inr (.inr (.inr rfl))))
  | letE A v body => exact .inr (.inr (.inr (.inl ⟨A, v, body, rfl⟩)))
  | lit t => exact .inr (.inr (.inr (.inr (.inl ⟨t, rfl⟩))))

/-- **W-LET** — a let's chain is ζ into the instantiated body, then the
    body's own chain: `letE A v b ⇝ b[v]` (`TyHRedA.zeta`) needs the
    let's four typings; the residual is the body-instance's chain at
    `B[v]`, retyped to the let's type downstream by `letE_gen`'s
    conversion. -/
theorem wallLet_chain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {A v body B : ExprA} {u : Level}
    (hA : HasTyA E I n Γ A (.sort u))
    (hv : HasTyA E I n Γ v A)
    (hb : HasTyA E I n (.letBinding A v :: Γ) body B)
    (hred : HasTyA E I n Γ (instantiate0A v body) (instantiate0A v B))
    (hlet : HasTyA E I n Γ (.letE A v body) (instantiate0A v B))
    (hc : ∃ Nl, TyHRedStarA E I n Γ (instantiate0A v body) Nl (instantiate0A v B) ∧
      hStepFnA E I.fn Γ Nl = none) :
    ∃ Nl, TyHRedStarA E I n Γ (.letE A v body) Nl (instantiate0A v B) ∧
      hStepFnA E I.fn Γ Nl = none := by
  obtain ⟨Nl, chl, hnl⟩ := hc
  exact ⟨Nl, tyHRedStarA_cons hlet (.zeta Γ A v body B u hA hv hb hred) chl, hnl⟩

/-- **W-LIT** — a literal's chain is the expansion step
    (`TyHRedA.lit`, `natExpandA`), then the expansion's own chain at the
    literal's type. -/
theorem wallLit_chain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {t : Nat} {T : ExprA}
    (hexp : HasTyA E I n Γ (natExpandA t) T)
    (hc : ∃ Nl, TyHRedStarA E I n Γ (natExpandA t) Nl T ∧
      hStepFnA E I.fn Γ Nl = none) :
    ∃ Nl, TyHRedStarA E I n Γ (.lit t) Nl T ∧
      hStepFnA E I.fn Γ Nl = none := by
  obtain ⟨Nl, chl, hnl⟩ := hc
  exact ⟨Nl, tyHRedStarA_cons (.lit Γ t T hexp) (.lit Γ t T hexp) chl, hnl⟩

/-- **the walls, composed per term** — a term `e` typed at a type `N'`
    carries a head-normalizing chain. The case split is `hStepFnA_cases`
    (proved — every constructor is a step face or normal); the named
    residuals are `hvar` (the value's chain, W-VAR), `hdelta` (the body
    instance's typing and chain, W-DELTA), `happ` (the head's chain,
    W-APP), `htail` (the application's endpoint: normal, or a
    domain-matching λ with its β-continuation), `hlet` (the
    body-instance's chain, W-LET), `hlit` (the expansion's chain,
    W-LIT). Non-firing `.bvar`/`.const` sub-cases (unbound variable,
    opaque or bodiless member) are normal endpoints outright. The ζ
    step's instantiation typing `hred` is derived here from
    `hasTyA_substA` at the let-binding substitution — derivable, so not
    a residual. -/
theorem stuckTermChain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ))
    {N' e : ExprA} (ht : Nonempty (HasTyA E I n Γ e N'))
    (hvar : ∀ {i : Nat} {v Aᵢ : ExprA}, e = .bvar i →
        lookupValueA Γ i = some v → lookupTypeA Γ i = some Aᵢ →
        Nonempty (TyConvA E I n Γ Aᵢ N') →
        ∃ Nv, TyHRedStarA E I n Γ v Nv Aᵢ ∧ hStepFnA E I.fn Γ Nv = none)
    (hdelta : ∀ {r : Nat} {ls : List Level} {m : CheckedMemberA} {b : ExprA},
        e = .const r ls → E.members r = some m → m.bodyA = some b →
        transparent m.mclass = true → ls.length = m.arity →
        levelsBounded n ls = true →
        Nonempty (TyConvA E I n Γ (instantiateLevelsA ls m.mtypeA) N') →
        Nonempty (HasTyA E I n Γ (instantiateLevelsA ls b)
          (instantiateLevelsA ls m.mtypeA)) ∧
        ∃ Nb, TyHRedStarA E I n Γ (instantiateLevelsA ls b) Nb
          (instantiateLevelsA ls m.mtypeA) ∧ hStepFnA E I.fn Γ Nb = none)
    (happ : ∀ {f a A B : ExprA} {u v : Level}, e = .app f a →
        Nonempty (HasTyA E I n Γ f (.pi A u B v)) →
        ∃ Nf, TyHRedStarA E I n Γ f Nf (.pi A u B v) ∧
          hStepFnA E I.fn Γ Nf = none)
    (htail : ∀ {f a A B Nf : ExprA} {u v w : Level}, e = .app f a →
        TyHRedStarA E I n Γ f Nf (.pi A u B v) → hStepFnA E I.fn Γ Nf = none →
        Nonempty (HasTyA E I n Γ a A) →
        Nonempty (HasTyA E I n (.assumption A :: Γ) B (.sort v)) →
        Nonempty (HasTyA E I n Γ (instantiate0A a B) (.sort w)) →
        (hStepFnA E I.fn Γ (.app Nf a) = none) ∨
        ∃ body, Nf = .lam A u body ∧ Nonempty (HasTyA E I n Γ A (.sort u)) ∧
          Nonempty (HasTyA E I n (.assumption A :: Γ) body B) ∧
          Nonempty (HasTyA E I n Γ (instantiate0A a body) (instantiate0A a B)) ∧
          ∃ Nc, TyHRedStarA E I n Γ (instantiate0A a body) Nc (instantiate0A a B) ∧
            hStepFnA E I.fn Γ Nc = none)
    (hlet : ∀ {A v body B : ExprA} {u w : Level}, e = .letE A v body →
        Nonempty (HasTyA E I n Γ A (.sort u)) →
        Nonempty (HasTyA E I n Γ v A) →
        Nonempty (HasTyA E I n Γ (instantiate0A v B) (.sort w)) →
        Nonempty (HasTyA E I n (.letBinding A v :: Γ) body B) →
        Nonempty (TyConvA E I n Γ (instantiate0A v B) N') →
        ∃ Nl, TyHRedStarA E I n Γ (instantiate0A v body) Nl (instantiate0A v B) ∧
          hStepFnA E I.fn Γ Nl = none)
    (hlit : ∀ {t : Nat}, e = .lit t →
        Nonempty (HasTyA E I n Γ (natExpandA t) N') →
        ∃ Nl, TyHRedStarA E I n Γ (natExpandA t) Nl N' ∧
          hStepFnA E I.fn Γ Nl = none) :
    ∃ Ne, TyHRedStarA E I n Γ e Ne N' ∧ hStepFnA E I.fn Γ Ne = none := by
  obtain ⟨ht'⟩ := ht
  rcases hStepFnA_cases E I.fn Γ e with hbv | hcn | hap | hlt | hli | hnorm
  · obtain ⟨i, rfl⟩ := hbv
    obtain ⟨Aᵢ, hty, cN⟩ := hasTyA_bvar_gen ht'
    cases hval : lookupValueA Γ i with
    | none => exact ⟨.bvar i, tyHRedStarA_refl ht', by simpa [hStepFnA] using hval⟩
    | some v =>
      obtain ⟨Nv, chv, hnv⟩ := hvar rfl hval hty cN
      obtain ⟨hv⟩ := tyHRedStarA_hasTy_head chv
      obtain ⟨t⟩ := tyConvA_symm_ne cN
      obtain ⟨Na, cha, hna, -⟩ := wallVar_chain hval hty hv
        (hasTyA_of_tyConvA ht' t) ⟨Nv, chv, hnv⟩
      exact ⟨Na, tyHRedStarA_retype cN cha, hna⟩
  · obtain ⟨r, ls, rfl⟩ := hcn
    obtain ⟨m, hres, hlen, hwf, cN⟩ := hasTyA_const_full ht'
    cases htr : transparent m.mclass with
    | false =>
      exact ⟨.const r ls, tyHRedStarA_refl ht', by simp [hStepFnA, hres, htr]⟩
    | true =>
      cases hb : m.bodyA with
      | none =>
        exact ⟨.const r ls, tyHRedStarA_refl ht', by simp [hStepFnA, hres, htr, hb]⟩
      | some b =>
        obtain ⟨hbt, Nb, chb, hnb⟩ := hdelta rfl hres hb htr hlen hwf cN
        obtain ⟨hb'⟩ := hbt
        obtain ⟨t⟩ := tyConvA_symm_ne cN
        obtain ⟨Na, cha, hna, -⟩ := wallDelta_chain hres hb htr hlen hwf hb'
          (hasTyA_of_tyConvA ht' t) ⟨Nb, chb, hnb⟩
        exact ⟨Na, tyHRedStarA_retype cN cha, hna⟩
  · obtain ⟨f, a, rfl⟩ := hap
    obtain ⟨A, u, B, v, w, hf, ha, hB, hTy, cT⟩ := hasTyA_app_gen ht'
    obtain ⟨Nf, chf, hnf⟩ := happ rfl hf
    rcases htail rfl chf hnf ha hB hTy with hnone | ⟨body, hlam, hA, hbody, hred, Nc, chc, hnc⟩
    · obtain ⟨hf'⟩ := hf; obtain ⟨ha'⟩ := ha; obtain ⟨hB'⟩ := hB; obtain ⟨hTy'⟩ := hTy
      exact ⟨.app Nf a,
        tyHRedStarA_retype cT (tyHRedStarA_app_head (.refl _ _) hB' hTy' ha' chf), hnone⟩
    · subst hlam
      obtain ⟨hf'⟩ := hf; obtain ⟨ha'⟩ := ha; obtain ⟨hB'⟩ := hB; obtain ⟨hTy'⟩ := hTy
      obtain ⟨hA'⟩ := hA; obtain ⟨hbody'⟩ := hbody; obtain ⟨hred'⟩ := hred
      obtain ⟨Na, cha, hna⟩ := wallApp_lam_chain (.refl _ _) hA' hB' hTy' ha' hbody' hred' chf
        ⟨Nc, chc, hnc⟩
      exact ⟨Na, tyHRedStarA_retype cT cha, hna⟩
  · obtain ⟨A, v, body, rfl⟩ := hlt
    obtain ⟨u, w, B, hA, hv, hTy, hb, cN⟩ := hasTyA_letE_gen ht'
    obtain ⟨Nl, chl, hnl⟩ := hlet rfl hA hv hTy hb cN
    obtain ⟨hΓ'⟩ := hΓ
    obtain ⟨hA'⟩ := hA; obtain ⟨hv'⟩ := hv; obtain ⟨hTy'⟩ := hTy; obtain ⟨hb'⟩ := hb
    have hs := hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS
      (substTyA_cons_id_let hE hI hΓ' hv') hb'
    rw [substA_cons_id_instantiate0, substA_cons_id_instantiate0] at hs
    obtain ⟨Na, cha, hna⟩ := wallLet_chain hA' hv' hb' hs
      (.letE Γ A u w v B body hA' hv' hTy' hb') ⟨Nl, chl, hnl⟩
    exact ⟨Na, tyHRedStarA_retype cN cha, hna⟩
  · obtain ⟨t, rfl⟩ := hli
    obtain ⟨Nl, chl, hnl⟩ := hlit rfl ⟨hasTyA_lit_gen ht'⟩
    obtain ⟨Na, cha, hna⟩ := wallLit_chain (hasTyA_lit_gen ht') ⟨Nl, chl, hnl⟩
    exact ⟨Na, cha, hna⟩
  · exact ⟨e, tyHRedStarA_refl ht', hnorm⟩

/-- **S1-e — `hstuck` from the faces.** At a `TyInKA`-reached node whose
    type whnf's to a stuck `N'`, the reached derivation is a `TyKA.stuck`
    (`tyInKA_stuck_rel`), so `R' a' b'` unpacks to the typings of `a'`/`b'`
    at `N'`; `stuckTermChain` chains each, retyped `N' → A'`. The split is
    proved (`hStepFnA_cases` — no classifier premise); the named residuals
    (`hvar`, `hdelta`, `happ`, `htail`, `hlet`, `hlit`) are quantified
    over the reached nodes so a caller can use node data — W-APP's `happ`
    is `tyKA_chain_sub` at `f`'s own derivation (`happ_of_tyKA_sub`). -/
theorem hstuck_of_faces {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {k : Nat} {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (d : TyKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j) Γ A R)
    (hvar : ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop} {N' Aᵢ v e : ExprA}
      {i : Nat}, TyInKA d Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' →
      e = .bvar i → lookupValueA Γ' i = some v → lookupTypeA Γ' i = some Aᵢ →
      Nonempty (TyConvA E I n Γ' Aᵢ N') →
      ∃ Nv, TyHRedStarA E I n Γ' v Nv Aᵢ ∧ hStepFnA E I.fn Γ' Nv = none)
    (hdelta : ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop} {N' b e : ExprA}
      {r : Nat} {ls : List Level} {m : CheckedMemberA},
      TyInKA d Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' →
      e = .const r ls → E.members r = some m → m.bodyA = some b →
      transparent m.mclass = true → ls.length = m.arity →
      levelsBounded n ls = true →
      Nonempty (TyConvA E I n Γ' (instantiateLevelsA ls m.mtypeA) N') →
      Nonempty (HasTyA E I n Γ' (instantiateLevelsA ls b)
        (instantiateLevelsA ls m.mtypeA)) ∧
      ∃ Nb, TyHRedStarA E I n Γ' (instantiateLevelsA ls b) Nb
        (instantiateLevelsA ls m.mtypeA) ∧ hStepFnA E I.fn Γ' Nb = none)
    (happ : ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop} {N' f a A B e : ExprA}
      {u v : Level}, TyInKA d Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' →
      e = .app f a → Nonempty (HasTyA E I n Γ' f (.pi A u B v)) →
      ∃ Nf, TyHRedStarA E I n Γ' f Nf (.pi A u B v) ∧
        hStepFnA E I.fn Γ' Nf = none)
    (htail : ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop} {N' f a A B Nf e : ExprA}
      {u v w : Level}, TyInKA d Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' →
      e = .app f a →
      TyHRedStarA E I n Γ' f Nf (.pi A u B v) → hStepFnA E I.fn Γ' Nf = none →
      Nonempty (HasTyA E I n Γ' a A) →
      Nonempty (HasTyA E I n (.assumption A :: Γ') B (.sort v)) →
      Nonempty (HasTyA E I n Γ' (instantiate0A a B) (.sort w)) →
      (hStepFnA E I.fn Γ' (.app Nf a) = none) ∨
      ∃ body, Nf = .lam A u body ∧ Nonempty (HasTyA E I n Γ' A (.sort u)) ∧
        Nonempty (HasTyA E I n (.assumption A :: Γ') body B) ∧
        Nonempty (HasTyA E I n Γ' (instantiate0A a body) (instantiate0A a B)) ∧
        ∃ Nc, TyHRedStarA E I n Γ' (instantiate0A a body) Nc (instantiate0A a B) ∧
          hStepFnA E I.fn Γ' Nc = none)
    (hlet : ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop}
      {N' A₂ v body B e : ExprA} {u w : Level},
      TyInKA d Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' →
      e = .letE A₂ v body →
      Nonempty (HasTyA E I n Γ' A₂ (.sort u)) →
      Nonempty (HasTyA E I n Γ' v A₂) →
      Nonempty (HasTyA E I n Γ' (instantiate0A v B) (.sort w)) →
      Nonempty (HasTyA E I n (.letBinding A₂ v :: Γ') body B) →
      Nonempty (TyConvA E I n Γ' (instantiate0A v B) N') →
      ∃ Nl, TyHRedStarA E I n Γ' (instantiate0A v body) Nl (instantiate0A v B) ∧
        hStepFnA E I.fn Γ' Nl = none)
    (hlit : ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop}
      {N' e : ExprA} {t : Nat},
      TyInKA d Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' →
      e = .lit t → Nonempty (HasTyA E I n Γ' (natExpandA t) N') →
      ∃ Nl, TyHRedStarA E I n Γ' (natExpandA t) Nl N' ∧
        hStepFnA E I.fn Γ' Nl = none) :
    ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop} {a' b' N' : ExprA},
      TyInKA d Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' → R' a' b' →
      ∃ Na, TyHRedStarA E I n Γ' a' Na A' ∧ hStepFnA E I.fn Γ' Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ' b' Nb A' ∧ hStepFnA E I.fn Γ' Nb = none := by
  intro Γ' A' R' a' b' N' hin hΓ hA hN hab
  have e := tyInKA_stuck_rel hin hA hN
  rw [e] at hab
  obtain ⟨hta, htb, -⟩ := hab
  have cNA : Nonempty (TyConvA E I n Γ' N' A') := tyConvA_symm_ne (whTyA_tyConv hA)
  obtain ⟨Na, cha, hna⟩ := stuckTermChain hE hI hR hIS hΓ hta
    (fun he hvl hty cN => hvar hin hΓ hA hN he hvl hty cN)
    (fun he hm hb₂ htr hl hw cN => hdelta hin hΓ hA hN he hm hb₂ htr hl hw cN)
    (fun he hf => happ hin hΓ hA hN he hf)
    (fun he chf hnf ha hB hTy => htail hin hΓ hA hN he chf hnf ha hB hTy)
    (fun he hA₂ hv hTy hb cN => hlet hin hΓ hA hN he hA₂ hv hTy hb cN)
    (fun he hexp => hlit hin hΓ hA hN he hexp)
  obtain ⟨Nb, chb, hnb⟩ := stuckTermChain hE hI hR hIS hΓ htb
    (fun he hvl hty cN => hvar hin hΓ hA hN he hvl hty cN)
    (fun he hm hb₂ htr hl hw cN => hdelta hin hΓ hA hN he hm hb₂ htr hl hw cN)
    (fun he hf => happ hin hΓ hA hN he hf)
    (fun he chf hnf ha hB hTy => htail hin hΓ hA hN he chf hnf ha hB hTy)
    (fun he hA₂ hv hTy hb cN => hlet hin hΓ hA hN he hA₂ hv hTy hb cN)
    (fun he hexp => hlit hin hΓ hA hN he hexp)
  exact ⟨Na, tyHRedStarA_retype cNA cha, hna, Nb, tyHRedStarA_retype cNA chb, hnb⟩

/-- **W-APP's `happ` is `tyKA_chain_sub` at `f`'s derivation** — the
    face is discharged by the extraction theorem itself, applied at the
    function's own `TyKA` node (`d_f`, from the relation at `f`'s type):
    its `hstuck` is bounded to `TyInKA d_f`, the premise the bounded
    form was built for. `hstuck_f`/`hkey_f`/`hfamkey_f`/`hpiStep_f` are
    `d_f`'s own residuals — named, not produced here. -/
theorem happ_of_tyKA_sub {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hR : IotaRecHeadA E I)
    (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀) {k : Nat}
    {Γ : LCtxA} {A B f g : ExprA} {u v : Level} {Rf : ExprA → ExprA → Prop}
    (d_f : TyKA E I n ρ₀ k (fun j _ => LREqA E I n ρ₀ j) (fun j _ => LRTyA E I n ρ₀ j)
      Γ (.pi A u B v) Rf)
    (hstuck_f : ∀ {Γ' : LCtxA} {A' : ExprA} {R' : ExprA → ExprA → Prop} {a' b' N' : ExprA},
      TyInKA d_f Γ' A' R' → Nonempty (CtxWfA E I n Γ') →
      WhTyA E I n Γ' A' N' → StuckA E I Γ' N' → R' a' b' →
      ∃ Na, TyHRedStarA E I n Γ' a' Na A' ∧ hStepFnA E I.fn Γ' Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ' b' Nb A' ∧ hStepFnA E I.fn Γ' Nb = none)
    (hkey_f : ∀ {N : ExprA}, WhTyA E I n Γ (.pi A u B v) N →
      hStepFnA E I.fn Γ N = none → ¬ IsPropTy E I Γ N ∨ StuckA E I Γ N)
    (hfamkey_f : ∀ {Γ' : LCtxA} {X' N' : ExprA} {v' : Level} {r : Nat} {ls : List Level}
      {xs : List ExprA} {m : CheckedMemberA}, CtxWfA E I n Γ' →
      HasTyA E I n Γ' X' (.sort v') → isZero v' = false → WhTyA E I n Γ' X' N' →
      hStepFnA E I.fn Γ' N' = none → N' = foldAppsA (.const r ls) xs →
      E.members r = some m → m.mclass = .inductiveM → ¬ IsPropTy E I Γ' N')
    (hpiStep_f : ∀ {Γ' : LCtxA} {D : ExprA} {u' : Level} {C : ExprA} {v' : Level}
      {e e' : ExprA}, CtxWfA E I n Γ' → isZero v' = false →
      HasTyA E I n Γ' e (.pi D u' C v') → hStepFnA E I.fn Γ' e = some e' →
      Nonempty (TyHRedA E I n Γ' e e' (.pi D u' C v')))
    (hΓ : CtxWfA E I n Γ) {g' : ExprA} (hfrel : Rf f g') :
    ∃ Nf, TyHRedStarA E I n Γ f Nf (.pi A u B v) ∧ hStepFnA E I.fn Γ Nf = none := by
  obtain ⟨Nf, chf, hnf, _⟩ := tyKA_chain_sub hE hI hIS hEN hNC hR hS hρ d_f hstuck_f
    hkey_f hfamkey_f hpiStep_f hΓ hfrel
  exact ⟨Nf, chf, hnf⟩

end S1e

#print axioms tyKA_chain_sub
#print axioms lrRelA_chain_env_sub
#print axioms tmChainA_appHead
#print axioms tyHRedStarA_app_head
#print axioms tyHRedStarA_bvar_zetaLocal
#print axioms tyHRedStarA_const_delta
#print axioms wallVar_chain
#print axioms wallDelta_chain
#print axioms wallApp_chain
#print axioms wallApp_lam_chain
#print axioms tyInKA_extract
#print axioms tyInKA_stuck_rel
#print axioms hasTyA_const_full
#print axioms hStepFnA_cases
#print axioms wallLet_chain
#print axioms wallLit_chain
#print axioms stuckTermChain
#print axioms hstuck_of_faces
#print axioms happ_of_tyKA_sub

end Rcic.Declarative.Ann
