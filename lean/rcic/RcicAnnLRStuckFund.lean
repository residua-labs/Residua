import rcic.RcicAnnLRRows
import rcic.RcicAnnFamHeight
import rcic.RcicAnnFamSem

/-!
# DT-025 / A-6 S1-b — the stuck clause's chains: measured at `fundA`'s arms

R-A6-S1's S1-b (PR #6229, `issuecomment-6099264394`): MEASURE whether
`fundA`'s arms that land a term at a stuck type (var / app / const-δ /
rec-ι / conv) can supply head chains; only if EVERY arm can does the stuck
clause gain the datum; any arm that cannot is REPORTED as a wall, not
patched. This module is the measurement record plus the derivable
discharges, stated STANDALONE (no import of S1-a's unmerged
`RcicAnnLRChain.lean`; S1-a's PR #6246 was OPEN, not merged, when this was
built — the integration with either `hstuck` keying is a one-line
consumption of the conclusions below, which match S1-a's `hstuck` body
verbatim).

## (A) the arm inventory, measured

`fundA` (`RcicAnnLRFundBind.lean:1761`) assembles `FundHasTyArmsA`
(9 arms, `RcicAnnLRFund.lean:533-542`) and `FundConvArmsA` (19 arms,
`RcicAnnLRFund.lean:544-563`) through `fundHasTyOfArmsA` /
`fundConvOfArmsA` (`RcicAnnLRFund.lean:574/:597`). An arm LANDS AT A STUCK
TYPE when its conclusion's TYPE can whnf to a `StuckA` term (variable,
non-family constant, or their spines — `RcicAnnWk.lean:93`):

* PROVABLY non-stuck-landing (a stuck type is not a shape, and these types
  ARE shapes): `HasTyArmSortA` (`.sort`, `RcicAnnLRFund.lean:362`),
  `HasTyArmPiA` (`.pi`, `:375`), `HasTyArmLamA` (type `.pi`, `:380`),
  `ConvArmSortsA` (`.sort`, `:503`), `ConvArmEtaA` (`.pi`, `:513`), the
  `ConvArmPiA`/`ConvArmLamA` congruences (`.sort`/`.pi`, `:486`/`:479`) —
  by `stuckA_not_sort`/`stuckA_not_pi` (`RcicAnnWk.lean:96/:99`).
* Stuck-landing, per the ruling's five candidates:
  - var — `HasTyArmBvarA` (`RcicAnnLRFund.lean:365`), its type from the
    context;
  - app — `HasTyArmAppA` (`:387`), type `instantiate0A a B`;
  - const-δ — `HasTyArmConstA` (`:369`, type `instantiateLevelsA ls
    m.mtypeA`) and `ConvArmDeltaA` (`:446`);
  - rec-ι — `ConvArmIotaA` (`:454`) and `ConvArmStructIotaA` (`:460`);
  - conv — `HasTyArmConvA` (`:408`), type `B` arbitrary.
* Stuck-landing BEYOND the ruling's lists (measured; see the stop-rule
  reports): `HasTyArmLetEA` (`:395`, type `instantiate0A value B` — absent
  from both the candidate list and the non-stuck list), `HasTyArmLitA`
  (`:404`, type `T` arbitrary — the ruling's non-stuck list names `lit`,
  but a literal is typed at the type of its expansion, which is arbitrary),
  and on the conversion side the mirror/congruence arms that inherit their
  components' arbitrary types (`beta`/`zeta`/`zetaLocal`/`lit`/`app`/`letE`
  congruences, `consts`, `irr`, `tyConv`, `refl`/`symm`/`trans`).

## (B) the measurement, per stuck-landing candidate

What a stuck chain asks (`hstuck`'s body): for the arm's two terms, a
`TyHRedStarA` chain at the arm's type ending at an `hStepFnA = none`
endpoint. What the arms' existing content supplies: typings, conversions,
the semantic environment's clauses (`EnvSemA` relates each member const to
its `=ₙ`-level variants — `RcicAnnLRFund.lean:122`), and the arm IHs
(`FundArmA`, i.e. relations at substituted types). NONE of that is
reduction data — the one measurement that changes the picture is
`NeutKA` (`RcicAnnLRNeut.lean:40`): a term already known head-normal under
every world and spine IS its own chain endpoint (`neutKA_whnf`).

* **var** — `hStepFnA (.bvar i) = lookupValueA Γ i`
  (`RcicAnnStep.lean:705`). At a value-free position the discharge is
  DERIVABLE (sealed: `hasTyArmBvarA_stuck_chain`). At a let position the
  chain is the `zetaLocal` step to the value followed by the VALUE's chain
  — an arbitrary term's normalization, not in the arm's content: WALL
  (goal W-VAR below). Note the arm itself never splits these cases
  (`hasTyArmBvarA_holds`, `RcicAnnLRFund.lean:672`, routes through
  `ValidSubstA`, not reflection).
* **const** — `hStepFnA (.const r ls)` fires δ exactly for a transparent
  member with a body (`RcicAnnStep.lean:706-709`). At a rigid member
  (`transparent m.mclass = false` — every class but `definitionM`,
  `RcicDeclarative.lean:196`) the discharge is DERIVABLE (sealed:
  `hasTyArmConstA_stuck_chain`). At a transparent member the chain is the
  δ step (derivable: the arm carries its premises) followed by the BODY
  instance's chain — arbitrary term: WALL (goal W-DELTA; the same wall is
  `ConvArmDeltaA`'s, whose right-hand term IS the body instance).
* **app** — WALL (goal W-APP). The chain for `.app f a` needs `f`'s head
  chain (each `TyHRedA.app` step consumes one) or `f`'s neutrality; the
  arm's IH for `f` is a `FundArmA` at a π type, whose clause is Kripke
  functional data, not reduction data, and `f`'s shape is not in the
  premises.
* **rec-ι** — WALL (goal W-IOTA). `ConvArmIotaA` carries `I.rel` and both
  typings, so the LEFT term's first step is derivable (`TyHRedA.iota`);
  but the pair needs the RIGHT term's chain, and the ι interface
  constrains where ι FIRES (`IotaRecHeadA`, `RcicAnnDecl.lean:104`) — not
  what it RETURNS. `ConvArmStructIotaA` is the same wall one `kstruct`
  step earlier (goal W-STRUCTIOTA).
* **conv** — WALL (goal W-CONV). `e` is an arbitrary typed term; its chain
  is exactly the normalization datum. The same wall covers every
  mirror/congruence arm above, each reducing to its components' chains.

Because not every candidate can, the stuck clause does NOT gain the datum
env-wide, and the capstone `fund_stuck_chain : FundHasTyA … → <env-wide
hstuck>` does NOT fall out (fund-reachable pairs at stuck types include
non-neutral terms — e.g. every `HasTyArmConvA` landing). What DOES fall
out, sealed here as the capstone's derivable fragment:
`lrRelA_neut_stuck_chain` — every related pair of extended neutrals at a
stuck type carries the chains, which is the standard construction's
"reducible at a neutral type" restricted to the neutral class, and is
what `fund_self` reaches at every stuck type whose elements the fund
route supplies as neutrals.

## (C) the walls, goals in full (reported, not patched)

W-VAR (the var arm at a let position; `value`'s chain is the missing
datum; everything else is derivable from the letBinding's own data):

    ∀ {E I n ρ₀ Γ} (six env hypotheses) {i A u v},
      lookupValueA Γ i = some v → lookupTypeA Γ i = some A →
      HasTyA E I n Γ v A →
      ∀ {N}, WhTyA E I n Γ A N → StuckA E I Γ N →
        ∃ Na, TyHRedStarA E I n Γ (.bvar i) Na A ∧ hStepFnA E I.fn Γ Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ v Nb A ∧ hStepFnA E I.fn Γ Nb = none

W-CONST/W-DELTA (the transparent const; the body instance's chain):

    ∀ {E I n Γ r ls m u b}, E.members r = some m → m.bodyA = some b →
      transparent m.mclass = true → ls.length = m.arity → levelsBounded n ls = true →
      HasTyA E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort u) →
      HasTyA E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA) →
      ∀ {N}, WhTyA E I n Γ (instantiateLevelsA ls m.mtypeA) N → StuckA E I Γ N →
        ∃ Na, TyHRedStarA E I n Γ (.const r ls) Na (instantiateLevelsA ls m.mtypeA) ∧
          hStepFnA E I.fn Γ Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ (instantiateLevelsA ls b) Nb
            (instantiateLevelsA ls m.mtypeA) ∧ hStepFnA E I.fn Γ Nb = none

W-APP (the app arm; `f`'s head chain or neutrality is the missing datum):

    ∀ {E I n ρ₀ Γ f a A B u v w} (six env hypotheses),
      HasTyA E I n (.assumption A :: Γ) B (.sort v) →
      HasTyA E I n Γ (instantiate0A a B) (.sort w) →
      HasTyA E I n Γ f (.pi A u B v) → HasTyA E I n Γ a A →
      ∀ {N}, WhTyA E I n Γ (instantiate0A a B) N → StuckA E I Γ N →
        ∃ Na, TyHRedStarA E I n Γ (.app f a) Na (instantiate0A a B) ∧
          hStepFnA E I.fn Γ Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ (.app f a) Nb (instantiate0A a B) ∧
            hStepFnA E I.fn Γ Nb = none

W-IOTA / W-STRUCTIOTA (the recursor pair; the ι value's chain):

    ∀ {E I n Γ lhs rhs T}, I.rel E Γ lhs rhs →
      HasTyA E I n Γ lhs T → HasTyA E I n Γ rhs T →
      ∀ {N}, WhTyA E I n Γ T N → StuckA E I Γ N →
        ∃ Na, TyHRedStarA E I n Γ lhs Na T ∧ hStepFnA E I.fn Γ Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ rhs Nb T ∧ hStepFnA E I.fn Γ Nb = none

  (`ConvArmStructIotaA`: the same with `lhs := .app f a`, one `kstruct`
  step derivable first, the wall unchanged at `e`/`rhs`.)

W-CONV (the conv arm; `e` arbitrary — the normalization datum itself):

    ∀ {E I n ρ₀ Γ e A B l u} (six env hypotheses),
      HasTyA E I n Γ e A → HasTyA E I n Γ A (.sort l) → eqN l u →
      HasTyA E I n Γ B (.sort u) → ConvA E I n Γ A B (.sort u) →
      ∀ {N}, WhTyA E I n Γ B N → StuckA E I Γ N →
        ∃ Na, TyHRedStarA E I n Γ e Na B ∧ hStepFnA E I.fn Γ Na = none ∧
          ∃ Nb, TyHRedStarA E I n Γ e Nb B ∧ hStepFnA E I.fn Γ Nb = none

Stop-rule reports (non-stuck-list arms that MEASURE stuck-landing;
reported before any treatment, per the ruling's clause-scope stop rule —
NOT built here): `HasTyArmLitA` (`RcicAnnLRFund.lean:404`) — its type is
the arbitrary `T` of the literal's expansion; its chain is one `lit` step
(derivable) followed by `natExpandA t`'s chain, which needs the expansion
spine's ι-behaviour, not in the arm's content. `HasTyArmLetEA`
(`RcicAnnLRFund.lean:395`) — type `instantiate0A value B`; one `zeta`
step (derivable) followed by the body instance's chain, not in the
arm's content.

Why the walls are SEMANTIC, not proof-engineering: `loopIotaA`
(`RcicAnnDecl.lean:126`) types its own reducts and `loopIotaA_no_whnf`
kills every normal form where it fires; the six environment hypotheses
exclude it only through `IotaRecHeadA E I`. The stuck-chain datum at a
non-neutral term therefore lives in normalization content the copy's
relation does not carry — the ruling's own reading ("the neutral-type
clause demands reduction to a neutral") is what `TyKA.stuck` lacks.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section StuckChain
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- the reflexive discharge, shared by every arm whose term is already
    head-normal at its own type: the pair is its own two chains. -/
theorem hStuckChainA_self {Γ : LCtxA} {A a : ExprA} (ht : HasTyA E I n Γ a A)
    (hn : hStepFnA E I.fn Γ a = none) :
    ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
      ∃ Nb, TyHRedStarA E I n Γ a Nb A ∧ hStepFnA E I.fn Γ Nb = none :=
  ⟨_, tyHRedStarA_refl ht, hn, _, tyHRedStarA_refl ht, hn⟩

/-- **the var arm's discharge** (value-free positions): a typed variable
    without a value carries the stuck clause's chains — its own reflexive
    chains, the variable being its own `hStepFnA = none` endpoint. This is
    the hstuck body for the arm's pair, at the arm's own type; the let
    position is the wall W-VAR (module header). -/
theorem hasTyArmBvarA_stuck_chain {Γ : LCtxA} {A : ExprA} {u : Level} {i : Nat}
    (h : lookupTypeA Γ i = some A) (hA : HasTyA E I n Γ A (.sort u))
    (hv : lookupValueA Γ i = none) :
    ∀ {N : ExprA}, WhTyA E I n Γ A N → StuckA E I Γ N →
      ∃ Na, TyHRedStarA E I n Γ (.bvar i) Na A ∧ hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ (.bvar i) Nb A ∧ hStepFnA E I.fn Γ Nb = none := by
  intro _ _ _
  exact hStuckChainA_self (.bvar Γ i A u h hA) (by
    show lookupValueA Γ i = none; exact hv)

/-- **the const arm's discharge** (rigid members): a constant of a rigid
    member class (every class but `definitionM`) carries the stuck clause's
    chains — `hStepFnA` refuses δ at a rigid member, so the constant is its
    own normal endpoint. The transparent member is the wall W-CONST
    (module header). -/
theorem hasTyArmConstA_stuck_chain {Γ : LCtxA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {u : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hT : HasTyA E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort u))
    (hrig : transparent m.mclass = false) :
    ∀ {N : ExprA}, WhTyA E I n Γ (instantiateLevelsA ls m.mtypeA) N → StuckA E I Γ N →
      ∃ Na, TyHRedStarA E I n Γ (.const r ls) Na (instantiateLevelsA ls m.mtypeA) ∧
        hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ (.const r ls) Nb (instantiateLevelsA ls m.mtypeA) ∧
          hStepFnA E I.fn Γ Nb = none := by
  intro _ _ _
  refine hStuckChainA_self (.const Γ r ls m u hres hlen hwf hT) ?_
  simp [hStepFnA, hres, hrig]

end StuckChain

/-- **the capstone's derivable fragment**: a related pair of extended
    neutrals at a stuck type carries the stuck clause's chains — S1-a's
    `hstuck` body for the pair, read off the relation's own typings and
    the neutrals' own normality. This is the standard construction's
    "reducible at a neutral type" on the class the relation can see; the
    non-neutral landings are the module header's walls. -/
theorem lrRelA_neut_stuck_chain {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {ρ₀ : Nat → Nat} {k : Nat} {Γ : LCtxA} {A a b : ExprA}
    (hrel : LRRelA E I n ρ₀ k Γ A a b) (hna : NeutKA E I Γ a) (hnb : NeutKA E I Γ b) :
    ∀ {N : ExprA}, WhTyA E I n Γ A N → StuckA E I Γ N →
      ∃ Na, TyHRedStarA E I n Γ a Na A ∧ hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ b Nb A ∧ hStepFnA E I.fn Γ Nb = none := by
  intro _ _ _
  obtain ⟨hta, htb⟩ := LRRelA_hasTy hrel
  exact hta.elim fun ta => htb.elim fun tb =>
    ⟨_, tyHRedStarA_refl ta, neutKA_whnf hna, _, tyHRedStarA_refl tb, neutKA_whnf hnb⟩

/-! ## the consumption pin

At the stack's own lightest family fixture (`pinFamFEnvA 1`, `noIotaA`;
`RcicAnnFamHeight`), the copy's six environment hypotheses are ALL
discharged (`EnvSemA` through the profile theorem), and a NEUTRAL VARIABLE
AT A STUCK TYPE — `x₀ : y₁` in `Γ = [y : Sort 0, x : y]`, the type `y` a
variable with no value — is related to itself BY THE FUND ROUTE
(`fund_self` at the fixture) and gets its chains through the capstone
fragment above. The fixture's sem support mirrors S1-a's unmerged
`pinFamF1_small`/`pinFamF1_sem` (PR #6246, OPEN when this was built);
drop these two in favour of S1-a's at integration. -/

/-- the fixture's family is small-index (mirrors S1-a's unmerged pin). -/
theorem pinFamF1_small_s1b : SmallIndexProfileA (pinFamFEnvA 1) := by
  intro r m u₀ hm hind hsh v hv ρ x y hx hy hy0
  have hm' : m = pinFamFA 1 := by
    by_cases hr : r = 0
    · subst hr; cases hm; rfl
    · simp [pinFamFEnvA, extendEnvA, emptyEnvA, hr] at hm
  subst hm'
  simp only [pinFamFA, piDomLevelsA, List.drop, List.length_cons, List.drop_nil,
    List.not_mem_nil] at hv

/-- `EnvSemA` at the fixture (mirrors S1-a's unmerged pin). -/
theorem pinFamF1_sem_s1b (n : Nat) : EnvSemA (pinFamFEnvA 1) noIotaA n (fun _ => 1) :=
  envSemA_of_envWfA_profile (pinFamFEnvWfA 1 pinFamF1ViewA) noIotaA_lift noIotaA_subst
    noIotaA_levels (noIotaA_recHead _) posValA_one pinFamF1_small_s1b
    (fun r m hm hcm => by rw [pinFamF_ind hm] at hcm; exact MemberClass.noConfusion hcm)
    (envSemRecA_of_noRec (fun r m hm hrec => by
      rw [pinFamF_ind hm] at hrec; exact MemberClass.noConfusion hrec))

/-- `Γ = [y : Sort 0, x : y]`: the pin's context — `y` (index 1) a variable
    type at `Sort 0`, `x` (index 0) a variable AT that stuck type. -/
def pinStuckCtxA : LCtxA := [.assumption (.bvar 0), .assumption (.sort .zero)]

/-- **THE STUCK PIN**: at the fixture, the neutral variable `x` is related to
    itself at the STUCK type `y` by the fund route (`fund_self`'s conclusion,
    the stuck clause of `TyKA` behind it), and the pair carries the stuck
    chains — extracted by the capstone fragment from the relation's typings
    and `x`'s own neutrality. -/
theorem pinFamF1_var_stuck :
    ∃ Na, TyHRedStarA (pinFamFEnvA 1) noIotaA 0 pinStuckCtxA (.bvar 0) Na (.bvar 1) ∧
      hStepFnA (pinFamFEnvA 1) noIotaA.fn pinStuckCtxA Na = none ∧
      ∃ Nb, TyHRedStarA (pinFamFEnvA 1) noIotaA 0 pinStuckCtxA (.bvar 0) Nb (.bvar 1) ∧
      hStepFnA (pinFamFEnvA 1) noIotaA.fn pinStuckCtxA Nb = none := by
  have hE : EnvClosedA (pinFamFEnvA 1) := pinFamF_closed 1
  have hI : IotaLiftA noIotaA := noIotaA_lift
  have hIS : IotaSubstA noIotaA := noIotaA_subst
  have hR : IotaRecHeadA (pinFamFEnvA 1) noIotaA := noIotaA_recHead _
  have hEN : EnvNormCtorTypeA (pinFamFEnvA 1) := fun _ _ hm hcm _ _ => by
    rw [pinFamF_ind hm] at hcm; exact MemberClass.noConfusion hcm
  have hNC : EnvNormClosedA (pinFamFEnvA 1) := fun _ _ hm hcm _ _ _ => by
    rw [pinFamF_ind hm] at hcm; exact MemberClass.noConfusion hcm
  have hS : EnvSemA (pinFamFEnvA 1) noIotaA 0 (fun _ => 1) := pinFamF1_sem_s1b 0
  have hρ : PosValA (fun _ => 1) := posValA_one
  have hΓ₁ : CtxWfA (pinFamFEnvA 1) noIotaA 0 [.assumption (.sort .zero)] :=
    .assumption .nil (.sort ([] : LCtxA) .zero)
  have hy₁ : HasTyA (pinFamFEnvA 1) noIotaA 0 [.assumption (.sort .zero)] (.bvar 0)
      (.sort .zero) :=
    .bvar _ 0 (.sort .zero) (.succ .zero) (by simp [lookupTypeA, liftA]) (.sort _ .zero)
  have hΓ₂ : CtxWfA (pinFamFEnvA 1) noIotaA 0 pinStuckCtxA := .assumption hΓ₁ hy₁
  have hy : HasTyA (pinFamFEnvA 1) noIotaA 0 pinStuckCtxA (.bvar 1) (.sort .zero) :=
    .bvar _ 1 (.sort .zero) (.succ .zero) (by simp [pinStuckCtxA, lookupTypeA, liftA])
      (.sort _ .zero)
  have hx : HasTyA (pinFamFEnvA 1) noIotaA 0 pinStuckCtxA (.bvar 0) (.bvar 1) :=
    .bvar _ 0 (.bvar 1) .zero (by simp [pinStuckCtxA, lookupTypeA, liftA]) hy
  have hvx : lookupValueA pinStuckCtxA 0 = none := by simp [pinStuckCtxA, lookupValueA]
  obtain ⟨k₀, hrel⟩ := fund_self hE hI hIS hEN hNC hR hS hρ hΓ₂ hx
  exact lrRelA_neut_stuck_chain (hrel k₀ (Nat.le_refl _))
    (neutKA_bvar hE hI (iotaConstHeadA_of_recHead hR) hvx)
    (neutKA_bvar hE hI (iotaConstHeadA_of_recHead hR) hvx)
    (whTyA_of_hasTy hy)
    ⟨by simp [pinStuckCtxA, hStepFnA, lookupValueA],
      by simp [appsSpineA, isShapeHeadA]⟩

#print axioms hStuckChainA_self
#print axioms hasTyArmBvarA_stuck_chain
#print axioms hasTyArmConstA_stuck_chain
#print axioms lrRelA_neut_stuck_chain
#print axioms pinFamF1_small_s1b
#print axioms pinFamF1_sem_s1b
#print axioms pinFamF1_var_stuck

end Rcic.Declarative.Ann
