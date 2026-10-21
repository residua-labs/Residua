import rcic.RcicDTMetaTypedSR
import rcic.RcicTypedGroupPinsVec
import rcic.ScmSrcGroupsEnvWfT

/-!
# DT-022 on the typed root: no general recursion introduction (tymig segment B)

02 §11 (`docs/rcic/02_DECLARATIVE_THEORY.md:336`): "Ordinary singleton declarations cannot
self-reference. Recursive computation enters only through admitted inductive recursors."
GM-THEORY-005 (`docs/rcic/GLOBAL_MUTANT_REGISTRY.md:40`): "Ordinary definition can self-reference."
Before this module the row had no carrier, only the blocker comment at `RcicDeclarative.lean:2720`.

The content is a well-founded δ-dependency. `DeltaDep E r' r` says that `r`'s stored body names `r'`
(`occursConst`, `RcicDeclarative.lean:363`, reused). On every `EnvWfT` environment this relation is
`WellFounded` (`DT022T_no_general_recursion`). So no body names itself, and no chain of bodies closes
into a cycle of any length. Unfolding bodies cannot introduce recursion; recursion enters only
through ι.

The measure is the admission rank (`EnvWfT.rank`): a member admitted at step `k` of the derivation
has rank `k`. The key lemma `envWfT_bodyConsts_before` holds because a singleton's body is typed in
the PRE-extension environment (`EnvWfT.definition` / `.thm` / `.opaque`, with `hfresh`). A typed term
names only members of its environment (`hasTyT_constsIn`), so every constant a body names was admitted
strictly earlier. Group cells add no body (`hnobody` on each `GroupMembersT` cell).

Teeth (GM-THEORY-005):
* `tooth_GM_THEORY_005_selfDef`: `def d := d` (any ref, type, level list) is a member of NO `EnvWfT`
  environment.
* `tooth_GM_THEORY_005_twoCycle`: neither is `d1 := d2, d2 := d1`.
* `tooth_GM_THEORY_005_rule`: the mutant ADMISSION RULE types the value in the self-extended
  environment, and at `natEnvU` (ref 4) its premise is inhabited. The real rule's premise, the value
  typed in the base, is refuted at the same data. The weakening the mutant names is exactly the
  one the rule's scope excludes.

Pins at `srcEnvG` (168 slots: 29 definitions, 23 theorems): `pin_DT022T_srcEnvG` (the relation is
well-founded there, through `envWfT_srcEnvG`) and `pin_DT022T_srcChain`, the real three-step δ-chain
`124 → 123 → 121 → 12` (`boundListBool → cctLbPf → bcLB → bytesB`), ranked strictly downward by the
theorem.

Second instrument, independent of `EnvWfT` and of the rank: `srcBodiesBelowSlot` evaluates over the
slot table (`kernel_rfl_theorem`) that every constant of every stored body is below its member's
slot. From that computation alone `pin_DT022T_srcEnvG_byEval` derives the same `WellFounded`, with
the slot index as the measure.

`closure_claim` 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Declarative

/-! ## (1) the relation -/

/-- δ-dependency: the stored body of member `r` names member `r'` (at any level list). -/
def DeltaDep (E : ResolvedEnv) (r' r : Nat) : Prop :=
  ∃ (m : CheckedMember) (b : Expr Nat), E.members r = some m ∧ m.body = some b ∧
    occursConst r' b = true

/-- a constant occurring in a term whose constants are all members is a member. -/
theorem member_of_occursConst {E : ResolvedEnv} {r : Nat} :
    (e : Expr Nat) → ConstsIn E e → occursConst r e = true → ∃ m, E.members r = some m
  | .bvar _, _, h => by simp [occursConst] at h
  | .sort _, _, h => by simp [occursConst] at h
  | .const r' _, hc, h => by
      simp only [occursConst, decide_eq_true_eq] at h
      subst h
      exact hc
  | .app f x, hc, h => by
      simp only [occursConst, Bool.or_eq_true] at h
      rcases h with h | h
      · exact member_of_occursConst f hc.1 h
      · exact member_of_occursConst x hc.2 h
  | .lam a b, hc, h => by
      simp only [occursConst, Bool.or_eq_true] at h
      rcases h with h | h
      · exact member_of_occursConst a hc.1 h
      · exact member_of_occursConst b hc.2 h
  | .pi a b, hc, h => by
      simp only [occursConst, Bool.or_eq_true] at h
      rcases h with h | h
      · exact member_of_occursConst a hc.1 h
      · exact member_of_occursConst b hc.2 h
  | .letE a v b, hc, h => by
      simp only [occursConst, Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact member_of_occursConst a hc.1 h
      · exact member_of_occursConst v hc.2.1 h
      · exact member_of_occursConst b hc.2.2 h
  | .lit t, hc, h => by
      cases t with
      | zero =>
          simp only [occursConst, litOccurs, decide_eq_true_eq] at h
          subst h
          exact hc
      | succ n =>
          simp only [occursConst, litOccurs, Bool.or_eq_true, decide_eq_true_eq] at h
          rcases h with h | h
          · subst h
            exact hc.1
          · subst h
            exact hc.2

/-- a group cell adds no body: every member a `GroupMembersT` chain adds carries `body = none`. -/
theorem groupMembersT_body_none {S E l E'} (h : GroupMembersT S E l E') :
    ∀ {r m}, (r, m) ∈ l → m.body = none := by
  induction h with
  | nil E =>
      intro r m hmem
      cases hmem
  | cons E r m rest E' hfresh hnobody _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
      intro r' m' hmem
      rcases List.mem_cons.mp hmem with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact hnobody
      · exact ih h

/-! ## (2) the admission rank -/

/-- the number of admission steps in an `EnvWfT` derivation. -/
def EnvWfT.depth : {E : ResolvedEnv} → EnvWfT E → Nat
  | _, .empty => 0
  | _, .axiom _ _ _ _ hE _ _ _ _ => hE.depth + 1
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.depth + 1
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => hE.depth + 1
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.depth + 1
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _ => hE.depth + 1

/-- one admission step's rank: members of the base keep their rank, every member the step adds
    gets the step's position `d + 1`. -/
def stepRank (E : ResolvedEnv) (rk : Nat → Nat) (d : Nat) : Nat → Nat :=
  fun r => if (E.members r).isSome then rk r else d + 1

/-- the admission rank of a member: the position of the step that admitted it. -/
def EnvWfT.rank : {E : ResolvedEnv} → EnvWfT E → Nat → Nat
  | _, .empty => fun _ => 0
  | _, .axiom E _ _ _ hE _ _ _ _ => stepRank E hE.rank hE.depth
  | _, .definition E _ _ _ _ hE _ _ _ _ _ _ _ => stepRank E hE.rank hE.depth
  | _, .thm E _ _ _ hE _ _ _ _ _ _ _ => stepRank E hE.rank hE.depth
  | _, .opaque E _ _ _ _ hE _ _ _ _ _ _ _ => stepRank E hE.rank hE.depth
  | _, .group E _ _ _ _ _ _ hE _ _ _ _ => stepRank E hE.rank hE.depth

theorem stepRank_of_mem {E : ResolvedEnv} {rk : Nat → Nat} {d r : Nat} {m : CheckedMember}
    (h : E.members r = some m) : stepRank E rk d r = rk r := by
  simp [stepRank, h]

theorem stepRank_of_fresh {E : ResolvedEnv} {rk : Nat → Nat} {d r : Nat}
    (h : E.members r = none) : stepRank E rk d r = d + 1 := by
  simp [stepRank, h]

theorem stepRank_le {E : ResolvedEnv} {rk : Nat → Nat} {d : Nat} (hrk : ∀ r, rk r ≤ d) (r : Nat) :
    stepRank E rk d r ≤ d + 1 := by
  unfold stepRank
  split
  · exact Nat.le_succ_of_le (hrk r)
  · exact Nat.le_refl _

/-- every rank is at most the derivation's depth. -/
theorem EnvWfT.rank_le_depth : {E : ResolvedEnv} → (hW : EnvWfT E) → ∀ r, hW.rank r ≤ hW.depth
  | _, .empty => fun _ => Nat.le_refl 0
  | _, .axiom _ _ _ _ hE _ _ _ _ => stepRank_le hE.rank_le_depth
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => stepRank_le hE.rank_le_depth
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => stepRank_le hE.rank_le_depth
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => stepRank_le hE.rank_le_depth
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _ => stepRank_le hE.rank_le_depth

/-! ## (3) bodies name only earlier members -/

/-- the inherited case: a member of the base keeps its rank, and so does every constant its body
    names (that body was typed in the base: `envWfT_bodyTypedRaw` + `hasTyT_constsIn`). -/
theorem stepRank_lt_of_base {E : ResolvedEnv} (hE : EnvWfT E)
    (ih : ∀ r m b r', E.members r = some m → m.body = some b → occursConst r' b = true →
      hE.rank r' < hE.rank r)
    {r : Nat} {m : CheckedMember} {b : Expr Nat} {r' : Nat}
    (hm : E.members r = some m) (hb : m.body = some b) (ho : occursConst r' b = true) :
    stepRank E hE.rank hE.depth r' < stepRank E hE.rank hE.depth r := by
  obtain ⟨m', hm'⟩ :=
    member_of_occursConst b (hasTyT_constsIn (envWfT_bodyTypedRaw hE r m b hm hb).1) ho
  rw [stepRank_of_mem hm', stepRank_of_mem hm]
  exact ih r m b r' hm hb ho

/-- the new-singleton case: the body was typed in the base, so every constant it names is a base
    member, ranked at most the base's depth; the new member is ranked one past it. -/
theorem stepRank_lt_of_new {E : ResolvedEnv} (hE : EnvWfT E) {r₀ : Nat}
    (hfresh : E.members r₀ = none) {v A : Expr Nat} (hv : HasTyT E 0 [] v A) {r' : Nat}
    (ho : occursConst r' v = true) :
    stepRank E hE.rank hE.depth r' < stepRank E hE.rank hE.depth r₀ := by
  obtain ⟨m', hm'⟩ := member_of_occursConst v (hasTyT_constsIn hv) ho
  rw [stepRank_of_mem hm', stepRank_of_fresh hfresh]
  exact Nat.lt_succ_of_le (hE.rank_le_depth r')

/-- B1: in an `EnvWfT` environment every constant a stored body names was admitted strictly before
    the body's member. -/
theorem envWfT_bodyConsts_before {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ (r : Nat) (m : CheckedMember) (b : Expr Nat) (r' : Nat), E.members r = some m →
      m.body = some b → occursConst r' b = true → hW.rank r' < hW.rank r := by
  induction hW with
  | empty =>
      intro r m b r' hm _ _
      simp [emptyEnv] at hm
  | «axiom» E r₀ A u hE hfresh _ _ _ ih =>
      intro r m b r' hm hb ho
      show stepRank E hE.rank hE.depth r' < stepRank E hE.rank hE.depth r
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hb
      · simp only [extendEnv, if_neg hr] at hm
        exact stepRank_lt_of_base hE ih hm hb ho
  | definition E r₀ A v u hE hfresh _ hv _ _ _ _ ih =>
      intro r m b r' hm hb ho
      show stepRank E hE.rank hE.depth r' < stepRank E hE.rank hE.depth r
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hb
        exact stepRank_lt_of_new hE hfresh hv ho
      · simp only [extendEnv, if_neg hr] at hm
        exact stepRank_lt_of_base hE ih hm hb ho
  | thm E r₀ A p hE hfresh _ hp _ _ _ _ ih =>
      intro r m b r' hm hb ho
      show stepRank E hE.rank hE.depth r' < stepRank E hE.rank hE.depth r
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hb
        exact stepRank_lt_of_new hE hfresh hp ho
      · simp only [extendEnv, if_neg hr] at hm
        exact stepRank_lt_of_base hE ih hm hb ho
  | «opaque» E r₀ A v u hE hfresh _ hv _ _ _ _ ih =>
      intro r m b r' hm hb ho
      show stepRank E hE.rank hE.depth r' < stepRank E hE.rank hE.depth r
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        cases hb
        exact stepRank_lt_of_new hE hfresh hv ho
      · simp only [extendEnv, if_neg hr] at hm
        exact stepRank_lt_of_base hE ih hm hb ho
  | group E f fm ctors rr rm E' hE _ _ _ hmem ih =>
      intro r m b r' hm hb ho
      show stepRank E hE.rank hE.depth r' < stepRank E hE.rank hE.depth r
      rcases groupMembersT_mem_cases hmem hm with hin | hmE
      · rw [groupMembersT_body_none hmem hin] at hb
        cases hb
      · exact stepRank_lt_of_base hE ih hmE hb ho

/-! ## (4) the row -/

/-- DT-022 typed: on every `EnvWfT` environment the δ-dependency relation is well-founded. No
    stored body names its own member, and no chain of bodies closes into a cycle of any length.
    The measure is the admission rank. -/
theorem DT022T_no_general_recursion {E : ResolvedEnv} (hW : EnvWfT E) :
    WellFounded (DeltaDep E) :=
  Subrelation.wf
    (fun {r' r} (h : DeltaDep E r' r) => by
      obtain ⟨m, b, hm, hb, ho⟩ := h
      exact envWfT_bodyConsts_before hW r m b r' hm hb ho)
    (measure hW.rank).wf

/-- no stored body names its own member. -/
theorem DT022T_no_self_reference {E : ResolvedEnv} (hW : EnvWfT E) {r : Nat}
    {m : CheckedMember} {b : Expr Nat} (hm : E.members r = some m) (hb : m.body = some b) :
    occursConst r b = false := by
  cases h : occursConst r b
  · rfl
  · exact absurd (envWfT_bodyConsts_before hW r m b r hm hb h) (Nat.lt_irrefl _)

/-- no two stored bodies name each other's members. -/
theorem DT022T_no_two_cycle {E : ResolvedEnv} (hW : EnvWfT E) {r₁ r₂ : Nat}
    (h₁ : DeltaDep E r₂ r₁) (h₂ : DeltaDep E r₁ r₂) : False := by
  obtain ⟨m₁, b₁, hm₁, hb₁, ho₁⟩ := h₁
  obtain ⟨m₂, b₂, hm₂, hb₂, ho₂⟩ := h₂
  exact Nat.lt_asymm (envWfT_bodyConsts_before hW r₁ m₁ b₁ r₂ hm₁ hb₁ ho₁)
    (envWfT_bodyConsts_before hW r₂ m₂ b₂ r₁ hm₂ hb₂ ho₂)

/-! ## (5) teeth: GM-THEORY-005 -/

/-- TOOTH (GM-THEORY-005, 1-cycle): `def d := d`, at any ref, type and level list, is a member of no
    `EnvWfT` environment. -/
theorem tooth_GM_THEORY_005_selfDef {E : ResolvedEnv} {r : Nat} {A : Expr Nat}
    {ls : List Level}
    (hm : E.members r = some ⟨.definitionM, 0, A, some (.const r ls)⟩) (hW : EnvWfT E) : False := by
  have h := DT022T_no_self_reference hW hm rfl
  simp [occursConst] at h

/-- TOOTH (GM-THEORY-005, 2-cycle): `d₁ := d₂`, `d₂ := d₁` are members of no `EnvWfT` environment. -/
theorem tooth_GM_THEORY_005_twoCycle {E : ResolvedEnv} {r₁ r₂ : Nat} {A₁ A₂ : Expr Nat}
    {ls₁ ls₂ : List Level}
    (hm₁ : E.members r₁ = some ⟨.definitionM, 0, A₁, some (.const r₂ ls₁)⟩)
    (hm₂ : E.members r₂ = some ⟨.definitionM, 0, A₂, some (.const r₁ ls₂)⟩)
    (hW : EnvWfT E) : False :=
  DT022T_no_two_cycle hW ⟨_, _, hm₁, rfl, by simp [occursConst]⟩
    ⟨_, _, hm₂, rfl, by simp [occursConst]⟩

/-- the self-referential definition the GM-THEORY-005 mutant would admit at `natEnvU`'s fresh ref 4:
    `d : Nat := d`. -/
def selfDefMember : CheckedMember := ⟨.definitionM, 0, .const 0 [], some (.const 4 [])⟩

/-- TOOTH (GM-THEORY-005, the rule): the mutant admission rule types the value in the SELF-EXTENDED
    environment, and its premise is inhabited at `natEnvU` (the const rule types `d` by its own
    membership). The real rule's premise, the same value typed in the base, is refuted there:
    ref 4 is fresh in `natEnvU` and a typed term names only members. -/
theorem tooth_GM_THEORY_005_rule :
    Nonempty (HasTyT (extendEnv natEnvU 4 selfDefMember) 0 [] (.const 4 [])
      (instantiateLevels [] (.const 0 []))) ∧
    ¬ Nonempty (HasTyT natEnvU 0 [] (.const 4 []) (.const 0 [])) := by
  refine ⟨⟨HasTyT.const [] 4 [] selfDefMember rfl rfl rfl⟩, ?_⟩
  rintro ⟨h⟩
  obtain ⟨m, hm⟩ := hasTyT_constsIn h
  rw [pinDefEnvU_fresh] at hm
  cases hm

end Rcic.Declarative

namespace Rcic.Scm.SrcG

open Rcic.Declarative

/-! ## (6) pins at `srcEnvG` -/

/-- PIN (DT-022T): the δ-dependency relation is well-founded on the 168-slot K3c environment, through
    the unconditional `envWfT_srcEnvG`. -/
theorem pin_DT022T_srcEnvG : WellFounded (DeltaDep srcEnvG) :=
  DT022T_no_general_recursion envWfT_srcEnvG

-- the four members of the real δ-chain `124 → 123 → 121 → 12` (kernel-checked lookups).
kernel_rfl_theorem srcEnvG_slot124 : srcEnvG.members 124 = some mBoundListBool
kernel_rfl_theorem srcEnvG_slot123 : srcEnvG.members 123 = some mCctLbPf
kernel_rfl_theorem srcEnvG_slot121 : srcEnvG.members 121 = some mBcLB
-- the chain's three links: each body names the next member (kernel-checked evaluations).
kernel_rfl_theorem srcOcc_124_123 : (mBoundListBool.body.map (occursConst 123)) = some true
kernel_rfl_theorem srcOcc_123_121 : (mCctLbPf.body.map (occursConst 121)) = some true
kernel_rfl_theorem srcOcc_121_12 : (mBcLB.body.map (occursConst 12)) = some true

theorem deltaDep_of_lookup {E : ResolvedEnv} {r r' : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (ho : m.body.map (occursConst r') = some true) :
    DeltaDep E r' r := by
  cases hb : m.body with
  | none => rw [hb] at ho; cases ho
  | some b =>
      rw [hb] at ho
      exact ⟨m, b, hm, hb, Option.some.inj ho⟩

/-- PIN (DT-022T, a real chain): `boundListBool → cctLbPf → bcLB → bytesB` are three δ-dependencies
    of `srcEnvG`, and the theorem ranks them strictly downward. -/
theorem pin_DT022T_srcChain :
    DeltaDep srcEnvG 123 124 ∧ DeltaDep srcEnvG 121 123 ∧ DeltaDep srcEnvG 12 121 ∧
    envWfT_srcEnvG.rank 12 < envWfT_srcEnvG.rank 121 ∧
    envWfT_srcEnvG.rank 121 < envWfT_srcEnvG.rank 123 ∧
    envWfT_srcEnvG.rank 123 < envWfT_srcEnvG.rank 124 := by
  have d1 := deltaDep_of_lookup srcEnvG_slot124 srcOcc_124_123
  have d2 := deltaDep_of_lookup srcEnvG_slot123 srcOcc_123_121
  have d3 := deltaDep_of_lookup srcEnvG_slot121 srcOcc_121_12
  refine ⟨d1, d2, d3, ?_, ?_, ?_⟩
  · obtain ⟨m, b, hm, hb, ho⟩ := d3
    exact envWfT_bodyConsts_before envWfT_srcEnvG _ m b _ hm hb ho
  · obtain ⟨m, b, hm, hb, ho⟩ := d2
    exact envWfT_bodyConsts_before envWfT_srcEnvG _ m b _ hm hb ho
  · obtain ⟨m, b, hm, hb, ho⟩ := d1
    exact envWfT_bodyConsts_before envWfT_srcEnvG _ m b _ hm hb ho

/-! ## (7) second instrument: slot order, by evaluation, without `EnvWfT` -/

/-- every constant of `e` has a ref below `k`. -/
def constsBelow (k : Nat) : Expr Nat → Bool
  | .bvar _ => true
  | .sort _ => true
  | .const r _ => decide (r < k)
  | .app f x => constsBelow k f && constsBelow k x
  | .lam a b => constsBelow k a && constsBelow k b
  | .pi a b => constsBelow k a && constsBelow k b
  | .letE a v b => constsBelow k a && constsBelow k v && constsBelow k b
  | .lit t =>
      match t with
      | 0 => decide (1 < k)
      | _ + 1 => decide (1 < k) && decide (2 < k)

theorem lt_of_constsBelow {k r : Nat} :
    (e : Expr Nat) → constsBelow k e = true → occursConst r e = true → r < k
  | .bvar _, _, h => by simp [occursConst] at h
  | .sort _, _, h => by simp [occursConst] at h
  | .const r' _, hc, h => by
      simp only [constsBelow, decide_eq_true_eq] at hc
      simp only [occursConst, decide_eq_true_eq] at h
      subst h
      exact hc
  | .app f x, hc, h => by
      simp only [constsBelow, Bool.and_eq_true] at hc
      simp only [occursConst, Bool.or_eq_true] at h
      rcases h with h | h
      · exact lt_of_constsBelow f hc.1 h
      · exact lt_of_constsBelow x hc.2 h
  | .lam a b, hc, h => by
      simp only [constsBelow, Bool.and_eq_true] at hc
      simp only [occursConst, Bool.or_eq_true] at h
      rcases h with h | h
      · exact lt_of_constsBelow a hc.1 h
      · exact lt_of_constsBelow b hc.2 h
  | .pi a b, hc, h => by
      simp only [constsBelow, Bool.and_eq_true] at hc
      simp only [occursConst, Bool.or_eq_true] at h
      rcases h with h | h
      · exact lt_of_constsBelow a hc.1 h
      · exact lt_of_constsBelow b hc.2 h
  | .letE a v b, hc, h => by
      simp only [constsBelow, Bool.and_eq_true] at hc
      simp only [occursConst, Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact lt_of_constsBelow a hc.1.1 h
      · exact lt_of_constsBelow v hc.1.2 h
      · exact lt_of_constsBelow b hc.2 h
  | .lit t, hc, h => by
      cases t with
      | zero =>
          simp only [constsBelow, decide_eq_true_eq] at hc
          simp only [occursConst, litOccurs, decide_eq_true_eq] at h
          subst h
          exact hc
      | succ n =>
          simp only [constsBelow, Bool.and_eq_true, decide_eq_true_eq] at hc
          simp only [occursConst, litOccurs, Bool.or_eq_true, decide_eq_true_eq] at h
          rcases h with h | h
          · subst h
            exact hc.1
          · subst h
            exact hc.2

/-- every stored body of a slot table names only refs below its own slot. -/
def bodiesBelowSlot (tbl : List (Nat × CheckedMember)) : Bool :=
  tbl.all fun p =>
    match p.2.body with
    | some b => constsBelow p.1 b
    | none => true

-- the evaluation over `srcEnvG`'s 168-slot table (kernel-checked).
kernel_rfl_theorem srcBodiesBelowSlot : bodiesBelowSlot srcMembersG = true

/-- a member of a fold of `extendEnv` over a slot table is a row of the table or a member of the
    starting environment (the last write wins, and it is a row). Stated for any step function that
    IS `extendEnv` pointwise, so a caller's own fold lambda is matched first-order. -/
theorem foldl_extendEnv_mem (f : ResolvedEnv → Nat × CheckedMember → ResolvedEnv)
    (hf : ∀ E p, f E p = extendEnv E p.1 p.2) :
    ∀ (tbl : List (Nat × CheckedMember)) (acc : ResolvedEnv) {c : Nat} {m : CheckedMember},
      (tbl.foldl f acc).members c = some m → (c, m) ∈ tbl ∨ acc.members c = some m
  | [], _, _, _, h => Or.inr h
  | (r₀, m₀) :: tl, acc, c, m, h => by
      rw [List.foldl_cons] at h
      rcases foldl_extendEnv_mem f hf tl _ h with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · rw [hf] at h'
        by_cases hc : c = r₀
        · subst hc
          have hm : m₀ = m := by
            simp only [extendEnv, if_pos rfl] at h'
            exact Option.some.inj h'
          subst hm
          exact Or.inl (List.mem_cons_self _ _)
        · simp only [extendEnv, if_neg hc] at h'
          exact Or.inr h'

/-- every member of `srcEnvG` is a row of its slot table. -/
theorem srcEnvG_mem_table {r : Nat} {m : CheckedMember} (hm : srcEnvG.members r = some m) :
    (r, m) ∈ srcMembersG := by
  rw [← srcEnvG_eq] at hm
  rcases foldl_extendEnv_mem _ (fun _ ⟨_, _⟩ => rfl) srcMembersG emptyEnv hm with h | h
  · exact h
  · simp [emptyEnv] at h

/-- by evaluation alone: every δ-dependency of `srcEnvG` points to a lower slot. -/
theorem srcEnvG_deltaDep_lt {r' r : Nat} (h : DeltaDep srcEnvG r' r) : r' < r := by
  obtain ⟨m, b, hm, hb, ho⟩ := h
  have hrow := srcEnvG_mem_table hm
  have hall := List.all_eq_true.mp srcBodiesBelowSlot (r, m) hrow
  simp only [hb] at hall
  exact lt_of_constsBelow b hall ho

/-- SECOND INSTRUMENT: the same well-foundedness at `srcEnvG`, from the slot-order evaluation and the
    slot index as measure. No `EnvWfT`, no rank. -/
theorem pin_DT022T_srcEnvG_byEval : WellFounded (DeltaDep srcEnvG) :=
  Subrelation.wf (fun {_ _} h => srcEnvG_deltaDep_lt h) (measure id).wf

end Rcic.Scm.SrcG

#print axioms Rcic.Declarative.member_of_occursConst
#print axioms Rcic.Declarative.groupMembersT_body_none
#print axioms Rcic.Declarative.EnvWfT.depth
#print axioms Rcic.Declarative.EnvWfT.rank
#print axioms Rcic.Declarative.EnvWfT.rank_le_depth
#print axioms Rcic.Declarative.stepRank_lt_of_base
#print axioms Rcic.Declarative.stepRank_lt_of_new
#print axioms Rcic.Declarative.envWfT_bodyConsts_before
#print axioms Rcic.Declarative.DT022T_no_general_recursion
#print axioms Rcic.Declarative.DT022T_no_self_reference
#print axioms Rcic.Declarative.DT022T_no_two_cycle
#print axioms Rcic.Declarative.tooth_GM_THEORY_005_selfDef
#print axioms Rcic.Declarative.tooth_GM_THEORY_005_twoCycle
#print axioms Rcic.Declarative.tooth_GM_THEORY_005_rule
#print axioms Rcic.Scm.SrcG.pin_DT022T_srcEnvG
#print axioms Rcic.Scm.SrcG.pin_DT022T_srcChain
#print axioms Rcic.Scm.SrcG.srcBodiesBelowSlot
#print axioms Rcic.Scm.SrcG.foldl_extendEnv_mem
#print axioms Rcic.Scm.SrcG.srcEnvG_mem_table
#print axioms Rcic.Scm.SrcG.srcEnvG_deltaDep_lt
#print axioms Rcic.Scm.SrcG.pin_DT022T_srcEnvG_byEval
#print axioms Rcic.Declarative.stepRank_of_mem
#print axioms Rcic.Declarative.stepRank_of_fresh
#print axioms Rcic.Declarative.stepRank_le
#print axioms Rcic.Scm.SrcG.srcEnvG_slot124
#print axioms Rcic.Scm.SrcG.srcEnvG_slot123
#print axioms Rcic.Scm.SrcG.srcEnvG_slot121
#print axioms Rcic.Scm.SrcG.srcOcc_124_123
#print axioms Rcic.Scm.SrcG.srcOcc_123_121
#print axioms Rcic.Scm.SrcG.srcOcc_121_12
#print axioms Rcic.Scm.SrcG.deltaDep_of_lookup
#print axioms Rcic.Scm.SrcG.lt_of_constsBelow
