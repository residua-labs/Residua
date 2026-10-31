import rcic.RcicDTMetaTypedNoRec
import rcic.RcicTypedGroup
import rcic.RcicAnnEnvBridgeGroup

/-! # RcicTypedStrengthen — S1 of [rcic_cres_wall_strengthening]

Predicates and agreement layer under the eventual `HasTyT` environment-
strengthening theorem (spec `00:18675-18676`; plan #6394). Nothing here
transports a derivation yet; the segment fixes the vocabulary S2's mutual
induction needs:

- §1 `constsBelow` is invariant under `lift` and `instantiateLevels`, and
  `instantiate` is clean in both directions (clean pieces instantiate clean;
  a clean instantiation has a clean body);
- §2 `declConstsBelow`/`ctxConstsBelow`: every stored type and let-value of a
  local context below the cut, with `lookupType`/`lookupValue` hits landing
  clean (a lookup hit is a lifted stored entry, and the bound is
  lift-invariant);
- §3 `EnvAgreeBelow E' E k`: the two environments carry identical members
  below the cut, closed under `extendEnv`/`groupEnvT` on entries at or past
  `k`; `GroupInScopeT.hlayout` discharges the group-side bound;
- §4 the `hasTyT_constsIn` / `envWfT_bodyTypedRaw` bridges the `.const` and
  `.delta` arms consume, plus `instantiateLevels` consts-preservation.

- §5 S2's arm-by-arm audit made executable: the TEN arms endpoint
  cleanliness leaves open (six hidden-intermediate, two member-supplied,
  two expansion), each a named premise;
- §5b S3's discharges: `RankCoherentBelow` + `envWfT_body_constsBelow`
  (δ, off `envWfT_bodyConsts_before`) and `derivedIota_of_agreeBelow`
  (ι, the `DerivedIota` replay under agreement);
- §6 the mutual `hasTyT_strengthen`/`convT_strengthen`/`tyConvT_strengthen`
  skeleton — every other arm closes inside the induction, δ/ι included:
  `StrengthenArms` now bundles the eight remaining debts.

- §7 S4's `cleanDeriv`: recursive `cleanHasTyT`/`cleanConvT`/`cleanTyConvT`
  predicates carry cleanliness of every sub-derivation conclusion, so the
  six hidden-intermediate arms close inside `hasTyT_strengthenC` /
  `convT_strengthenC` / `tyConvT_strengthenC` under `EnvAgreeBelow` alone —
  no `StrengthenArms`, no `RankCoherentBelow`.
- §7b member types name only earlier-or-equal members
  (`envWfT_typeConsts_le`, the type-side of `envWfT_bodyConsts_before`),
  crossed to refs by `RankCoherentBelow` in `envWfT_mtype_constsBelow`.
- §7c `cleanHasTyT_of_checkConstT`/`_of_checkLitT`/`_of_checkT`/
  `_of_synCheck`: the syntactic checker's derivations are `cleanDeriv`s
  when the subject and context are clean and the environment's member
  types are.
- §8 S5's group corollary `hasTyT_strengthen_group`: a `checkT` derivation
  in a group-grown environment replays in the base — agreement off the
  `GroupMembersT` chain (`groupMembersT_agreeBelow`), rank coherence
  propagated through the step (`rankCoherentBelow_of_group`, vacuous at a
  group allocated above its base via `rankCoherentBelow_of_forall_lt`), and
  `vecEnvU_strengthen_pin` exercising it at the Vec group.

The hidden-intermediate route (`cleanDeriv`, `ConvT.trans` downstream of
W-ATR-1) is S4 per the approved plan — no `sorry` in any committed
segment. -/

namespace Rcic.Declarative

open Rcic.Scm.SrcG (constsBelow lt_of_constsBelow)

/-! ## §1 `constsBelow` under `lift`, `instantiate`, `instantiateLevels` -/

/-- `lift` never enters a `.const` node: the constant bound is lift-invariant. -/
theorem constsBelow_lift {k : Nat} :
    (e : Expr Nat) → ∀ c a, constsBelow k (lift c a e) = constsBelow k e := by
  intro e
  induction e with
  | bvar j =>
      intro c a
      unfold lift
      by_cases h : c ≤ j
      · rw [if_pos h]; rfl
      · rw [if_neg h]
  | sort _ => intro c a; rfl
  | const _ _ => intro c a; rfl
  | lit _ => intro c a; rfl
  | app f x ihf ihx =>
      intro c a
      simp only [lift, constsBelow, ihf, ihx]
  | lam A b ihA ihb =>
      intro c a
      simp only [lift, constsBelow, ihA, ihb]
  | pi A B ihA ihB =>
      intro c a
      simp only [lift, constsBelow, ihA, ihB]
  | letE A v b ihA ihv ihb =>
      intro c a
      simp only [lift, constsBelow, ihA, ihv, ihb]

/-- forward direction: clean pieces stay clean under instantiation (the
    replacement's constants are the only constants an instantiation adds). -/
theorem constsBelow_instantiate {k : Nat} :
    (e : Expr Nat) → ∀ i v, constsBelow k e = true → constsBelow k v = true →
      constsBelow k (instantiate i v e) = true := by
  intro e
  induction e with
  | bvar j =>
      intro i v _ hv
      unfold instantiate
      by_cases hij : j = i
      · rw [if_pos hij]
        exact hv
      · rw [if_neg hij]
        by_cases hij2 : i < j
        · rw [if_pos hij2]; rfl
        · rw [if_neg hij2]; rfl
  | sort _ => intro i v _ _; rfl
  | const _ _ => intro i v he _; exact he
  | lit _ => intro i v he _; exact he
  | app f x ihf ihx =>
      intro i v he hv
      simp only [instantiate, constsBelow, Bool.and_eq_true] at he ⊢
      exact ⟨ihf i v he.1 hv, ihx i v he.2 hv⟩
  | lam A b ihA ihb =>
      intro i v he hv
      simp only [instantiate, constsBelow, Bool.and_eq_true] at he ⊢
      refine ⟨ihA i v he.1 hv, ihb (i+1) (lift 0 1 v) he.2 ?_⟩
      rw [constsBelow_lift]
      exact hv
  | pi A B ihA ihB =>
      intro i v he hv
      simp only [instantiate, constsBelow, Bool.and_eq_true] at he ⊢
      refine ⟨ihA i v he.1 hv, ihB (i+1) (lift 0 1 v) he.2 ?_⟩
      rw [constsBelow_lift]
      exact hv
  | letE A w b ihA ihw ihb =>
      intro i v he hv
      simp only [instantiate, constsBelow, Bool.and_eq_true] at he
      have hbv : constsBelow k (lift 0 1 v) = true := by rw [constsBelow_lift]; exact hv
      show (constsBelow k (instantiate i v A) && constsBelow k (instantiate i v w) &&
        constsBelow k (instantiate (i+1) (lift 0 1 v) b)) = true
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨ihA i v he.1.1 hv, ihw i v he.1.2 hv⟩,
        ihb (i+1) (lift 0 1 v) he.2 hbv⟩

/-- the converse: a clean instantiation has a clean body — every constant of
    `e` survives instantiation, so `e`'s bound follows the result's. -/
theorem constsBelow_of_instantiate {k : Nat} :
    (e : Expr Nat) → ∀ i v, constsBelow k (instantiate i v e) = true →
      constsBelow k e = true := by
  intro e
  induction e with
  | bvar _ => intro i v _; rfl
  | sort _ => intro i v _; rfl
  | const _ _ => intro i v h; exact h
  | lit _ => intro i v h; exact h
  | app f x ihf ihx =>
      intro i v h
      simp only [instantiate, constsBelow, Bool.and_eq_true] at h ⊢
      exact ⟨ihf i v h.1, ihx i v h.2⟩
  | lam A b ihA ihb =>
      intro i v h
      simp only [instantiate, constsBelow, Bool.and_eq_true] at h ⊢
      exact ⟨ihA i v h.1, ihb (i+1) (lift 0 1 v) h.2⟩
  | pi A B ihA ihB =>
      intro i v h
      simp only [instantiate, constsBelow, Bool.and_eq_true] at h ⊢
      exact ⟨ihA i v h.1, ihB (i+1) (lift 0 1 v) h.2⟩
  | letE A w b ihA ihw ihb =>
      intro i v h
      simp only [instantiate, constsBelow, Bool.and_eq_true] at h ⊢
      exact ⟨⟨ihA i v h.1.1, ihw i v h.1.2⟩, ihb (i+1) (lift 0 1 v) h.2⟩

/-- `instantiateLevels` keeps every `.const` reference: only the level list
    changes, so the bound is preserved. -/
theorem constsBelow_instantiateLevels {k : Nat} (ls : List Level) :
    (e : Expr Nat) → constsBelow k (instantiateLevels ls e) = constsBelow k e := by
  intro e
  induction e with
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app f x ihf ihx => simp only [instantiateLevels, constsBelow, ihf, ihx]
  | lam A b ihA ihb => simp only [instantiateLevels, constsBelow, ihA, ihb]
  | pi A B ihA ihB => simp only [instantiateLevels, constsBelow, ihA, ihB]
  | letE A v b ihA ihv ihb =>
      simp only [instantiateLevels, constsBelow, ihA, ihv, ihb]

/-- occurrence is likewise `instantiateLevels`-invariant. -/
theorem occursConst_instantiateLevels {r : Nat} (ls : List Level) :
    (e : Expr Nat) → occursConst r (instantiateLevels ls e) = occursConst r e := by
  intro e
  induction e with
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app f x ihf ihx => simp only [instantiateLevels, occursConst, ihf, ihx]
  | lam A b ihA ihb => simp only [instantiateLevels, occursConst, ihA, ihb]
  | pi A B ihA ihB => simp only [instantiateLevels, occursConst, ihA, ihB]
  | letE A v b ihA ihv ihb =>
      simp only [instantiateLevels, occursConst, ihA, ihv, ihb]

/-- `ConstsIn` is `instantiateLevels`-invariant: only the level lists move. -/
theorem ConstsIn_instantiateLevels {E : ResolvedEnv} (ls : List Level) :
    (e : Expr Nat) → ConstsIn E e → ConstsIn E (instantiateLevels ls e) := by
  intro e
  induction e with
  | bvar _ => intro h; exact h
  | sort _ => intro h; exact h
  | const _ _ => intro h; exact h
  | lit _ => intro h; exact h
  | app f x ihf ihx => intro h; exact ⟨ihf h.1, ihx h.2⟩
  | lam A b ihA ihb => intro h; exact ⟨ihA h.1, ihb h.2⟩
  | pi A B ihA ihB => intro h; exact ⟨ihA h.1, ihB h.2⟩
  | letE A v b ihA ihv ihb => intro h; exact ⟨ihA h.1, ihv h.2.1, ihb h.2.2⟩

/-! ## §2 context cleanliness -/

/-- one local declaration's stored expressions, all below the cut. -/
def declConstsBelow (k : Nat) : LocalDecl → Bool
  | .assumption A => constsBelow k A
  | .letBinding A v => constsBelow k A && constsBelow k v

/-- every stored type and let-value of `Γ` has its constants below `k`. -/
def ctxConstsBelow (k : Nat) : LCtx → Bool
  | [] => true
  | d :: Γ => declConstsBelow k d && ctxConstsBelow k Γ

/-- the `i`-th entry of a clean context is clean. -/
theorem ctxConstsBelow_get {k : Nat} {Γ : LCtx} {i : Nat} {d : LocalDecl}
    (hc : ctxConstsBelow k Γ = true) (h : Γ.get? i = some d) :
    declConstsBelow k d = true := by
  induction Γ generalizing i with
  | nil => simp at h
  | cons d0 Γ ih =>
      cases i with
      | zero =>
          simp only [ctxConstsBelow, Bool.and_eq_true] at hc
          simp only [List.get?_cons_zero] at h
          cases h
          exact hc.1
      | succ i =>
          simp only [ctxConstsBelow, Bool.and_eq_true] at hc
          exact ih hc.2 h

theorem ctxConstsBelow_of_cons {k : Nat} {Γ : LCtx} {d : LocalDecl}
    (h : ctxConstsBelow k (d :: Γ) = true) : ctxConstsBelow k Γ = true := by
  simp only [ctxConstsBelow, Bool.and_eq_true] at h
  exact h.2

theorem ctxConstsBelow_cons_of {k : Nat} {Γ : LCtx} {d : LocalDecl}
    (hd : declConstsBelow k d = true) (hΓ : ctxConstsBelow k Γ = true) :
    ctxConstsBelow k (d :: Γ) = true := by
  simp only [ctxConstsBelow, Bool.and_eq_true]
  exact ⟨hd, hΓ⟩

/-- what `lookupType` returns at an `.assumption` hit. -/
theorem lookupType_of_get?_assumption {Γ : LCtx} {i : Nat} {a : Expr Nat}
    (h : Γ.get? i = some (.assumption a)) :
    lookupType Γ i = some (lift 0 (i+1) a) := by
  simp only [lookupType, h]

/-- what `lookupType` returns at a `.letBinding` hit. -/
theorem lookupType_of_get?_letBinding {Γ : LCtx} {i : Nat} {a v : Expr Nat}
    (h : Γ.get? i = some (.letBinding a v)) :
    lookupType Γ i = some (lift 0 (i+1) a) := by
  simp only [lookupType, h]

/-- what `lookupValue` returns at a `.letBinding` hit. -/
theorem lookupValue_of_get?_letBinding {Γ : LCtx} {i : Nat} {a v : Expr Nat}
    (h : Γ.get? i = some (.letBinding a v)) :
    lookupValue Γ i = some (lift 0 (i+1) v) := by
  simp only [lookupValue, h]

/-- a `lookupType` hit in a clean context is clean: the hit is a stored entry
    lifted, and the bound is lift-invariant. -/
theorem ctxConstsBelow_lookupType {k : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (hc : ctxConstsBelow k Γ = true) (h : lookupType Γ i = some A) :
    constsBelow k A = true := by
  cases hgd : Γ.get? i with
  | none =>
      unfold lookupType at h
      rw [hgd] at h
      exact Option.noConfusion h
  | some d =>
      have hcl := ctxConstsBelow_get hc hgd
      cases d with
      | assumption a =>
          rw [lookupType_of_get?_assumption hgd] at h
          simp only [Option.some.injEq] at h
          subst h
          rw [constsBelow_lift]
          exact hcl
      | letBinding a v =>
          rw [lookupType_of_get?_letBinding hgd] at h
          simp only [Option.some.injEq] at h
          subst h
          rw [constsBelow_lift]
          simp only [declConstsBelow, Bool.and_eq_true] at hcl
          exact hcl.1

/-- a `lookupValue` hit in a clean context is clean. -/
theorem ctxConstsBelow_lookupValue {k : Nat} {Γ : LCtx} {i : Nat} {v : Expr Nat}
    (hc : ctxConstsBelow k Γ = true) (h : lookupValue Γ i = some v) :
    constsBelow k v = true := by
  cases hgd : Γ.get? i with
  | none =>
      unfold lookupValue at h
      rw [hgd] at h
      exact Option.noConfusion h
  | some d =>
      have hcl := ctxConstsBelow_get hc hgd
      cases d with
      | assumption a =>
          unfold lookupValue at h
          rw [hgd] at h
          exact Option.noConfusion h
      | letBinding a w =>
          rw [lookupValue_of_get?_letBinding hgd] at h
          simp only [Option.some.injEq] at h
          subst h
          rw [constsBelow_lift]
          simp only [declConstsBelow, Bool.and_eq_true] at hcl
          exact hcl.2

/-! ## §3 environment agreement below a cut -/

/-- `E'` and `E` carry identical members below `k`: early constants resolve
    identically in the two environments. -/
def EnvAgreeBelow (E' E : ResolvedEnv) (k : Nat) : Prop :=
  ∀ r, r < k → E'.members r = E.members r

theorem EnvAgreeBelow.refl (E : ResolvedEnv) (k : Nat) : EnvAgreeBelow E E k :=
  fun _ _ => rfl

theorem EnvAgreeBelow.symm {E' E : ResolvedEnv} {k : Nat} (h : EnvAgreeBelow E' E k) :
    EnvAgreeBelow E E' k :=
  fun r hr => (h r hr).symm

theorem EnvAgreeBelow.trans {E₁ E₂ E₃ : ResolvedEnv} {k : Nat}
    (h₁₂ : EnvAgreeBelow E₁ E₂ k) (h₂₃ : EnvAgreeBelow E₂ E₃ k) :
    EnvAgreeBelow E₁ E₃ k :=
  fun r hr => (h₁₂ r hr).trans (h₂₃ r hr)

theorem EnvAgreeBelow.mono {E' E : ResolvedEnv} {k k' : Nat} (h : EnvAgreeBelow E' E k)
    (hk : k' ≤ k) : EnvAgreeBelow E' E k' :=
  fun r hr => h r (Nat.lt_of_lt_of_le hr hk)

/-- agreement survives extending both sides with the same member at or past
    the cut. -/
theorem EnvAgreeBelow.extendEnv {E' E : ResolvedEnv} {k : Nat} (h : EnvAgreeBelow E' E k)
    {r : Nat} {m : CheckedMember} (hr : k ≤ r) :
    EnvAgreeBelow (Rcic.Declarative.extendEnv E' r m) (Rcic.Declarative.extendEnv E r m) k := by
  intro r' hr'
  have hne : r' ≠ r := Nat.ne_of_lt (Nat.lt_of_lt_of_le hr' hr)
  have e1 : (Rcic.Declarative.extendEnv E' r m).members r' = E'.members r' := if_neg hne
  have e2 : (Rcic.Declarative.extendEnv E r m).members r' = E.members r' := if_neg hne
  rw [e1, e2]
  exact h r' hr'

/-- agreement survives extending the left side alone: the new member sits at
    or past the cut, so lookups below `k` pass through to `E'`. -/
theorem EnvAgreeBelow.extendEnv_left {E' E : ResolvedEnv} {k : Nat} (h : EnvAgreeBelow E' E k)
    {r : Nat} {m : CheckedMember} (hr : k ≤ r) :
    EnvAgreeBelow (Rcic.Declarative.extendEnv E' r m) E k := by
  intro r' hr'
  have hne : r' ≠ r := Nat.ne_of_lt (Nat.lt_of_lt_of_le hr' hr)
  have e1 : (Rcic.Declarative.extendEnv E' r m).members r' = E'.members r' := if_neg hne
  rw [e1]
  exact h r' hr'

/-- agreement survives a group extended on both sides: the family sits at `f`
    and every constructor's reference is strictly above it, so nothing below
    `k ≤ f` is disturbed. The constructor bound `∀ c ∈ cs, f < c.1` is a named
    premise — the census/`GroupInScopeT.hlayout` discharges it at real groups
    (`GroupInScopeT.ctorRef_gt` below). -/
theorem EnvAgreeBelow.groupEnvT {E' E : ResolvedEnv} {k : Nat} (h : EnvAgreeBelow E' E k)
    {f : Nat} {fm : CheckedMember} (hf : k ≤ f) :
    ∀ (cs : List (Nat × CheckedMember)), (∀ c ∈ cs, f < c.1) →
      EnvAgreeBelow (Rcic.Declarative.groupEnvT E' f fm cs)
        (Rcic.Declarative.groupEnvT E f fm cs) k
  | [], _ => h.extendEnv hf
  | c :: cs, hcs =>
      (EnvAgreeBelow.groupEnvT h hf cs
        (fun c' hc' => hcs c' (List.mem_cons.mpr (Or.inr hc')))).extendEnv
        (Nat.le_trans hf (Nat.le_of_lt (hcs c (List.mem_cons.mpr (Or.inl rfl)))))

/-- the same-side corollary: a group grown on `E` agrees with `E` below `f`. -/
theorem EnvAgreeBelow.groupEnvT_self {E : ResolvedEnv} {k f : Nat} {fm : CheckedMember}
    (hf : k ≤ f) :
    ∀ (cs : List (Nat × CheckedMember)), (∀ c ∈ cs, f < c.1) →
      EnvAgreeBelow (Rcic.Declarative.groupEnvT E f fm cs) E k
  | [], _ => EnvAgreeBelow.extendEnv_left (EnvAgreeBelow.refl E k) hf
  | c :: cs, hcs =>
      EnvAgreeBelow.extendEnv_left
        (EnvAgreeBelow.groupEnvT_self hf cs
          (fun c' hc' => hcs c' (List.mem_cons.mpr (Or.inr hc'))))
        (Nat.le_trans hf (Nat.le_of_lt (hcs c (List.mem_cons.mpr (Or.inl rfl)))))

/-- `GroupInScopeT.hlayout` pins the constructor references to
    `range' (f+1) len`: every constructor ref is strictly above the family's.
    This is what discharges `EnvAgreeBelow.groupEnvT`'s premise at a scoped
    group. -/
theorem GroupInScopeT.ctorRef_gt {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    (h : GroupInScopeT E f fm ctors rr rm) {c : Nat × CheckedMember}
    (hc : c ∈ ctors) : f < c.1 := by
  have hmem : c ∈ h.cs.map GroupCtorT.entry :=
    List.mem_reverse.mp (h.hctors.symm ▸ hc)
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmem
  have hR : x.ref ∈ List.range' (f+1) h.cs.length := by
    rw [← h.hlayout]
    exact List.mem_map.mpr ⟨x, List.mem_reverse.mpr hx, rfl⟩
  obtain ⟨i, _hi, hxi⟩ := List.mem_range'.mp hR
  have hc1 : c.1 = x.ref := by
    subst hxe
    rfl
  omega

/-! ## §4 the typed bridges -/

/-- a constant occurring in a `constsBelow k` term typed in `E` is below `k`
    and a member of `E` — the conjunction the `.const` and `.delta` arms
    consume. -/
theorem member_of_occursConst_below {E : ResolvedEnv} {k n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (h : HasTyT E n Γ e A) (hc : constsBelow k e = true) {r : Nat}
    (ho : occursConst r e = true) :
    r < k ∧ ∃ m, E.members r = some m :=
  ⟨lt_of_constsBelow e hc ho, member_of_occursConst e (hasTyT_constsIn h) ho⟩

/-- under agreement below `k`, an occurring constant of a clean term resolves
    identically in the two environments. -/
theorem EnvAgreeBelow.resolve {E' E : ResolvedEnv} {k : Nat} (hag : EnvAgreeBelow E' E k)
    {e : Expr Nat} (hc : constsBelow k e = true) {r : Nat} (ho : occursConst r e = true) :
    E'.members r = E.members r :=
  hag r (lt_of_constsBelow e hc ho)

/-- the δ supply: a member's stored body names only members — its typing lives
    in `E` by `envWfT_bodyTypedRaw`. -/
theorem envWfT_body_constsIn {E : ResolvedEnv} (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some b) :
    ConstsIn E b :=
  hasTyT_constsIn (envWfT_bodyTypedRaw hW r m b hm hb).1

/-- the δ-unfold `instantiateLevels ls b` names the same members as `b`. -/
theorem envWfT_body_constsIn_levels {E : ResolvedEnv} (hW : EnvWfT E)
    {r : Nat} {m : CheckedMember} {b : Expr Nat}
    (hm : E.members r = some m) (hb : m.body = some b) (ls : List Level) :
    ConstsIn E (instantiateLevels ls b) :=
  ConstsIn_instantiateLevels ls b (envWfT_body_constsIn hW hm hb)

#print axioms Rcic.Declarative.constsBelow_lift
#print axioms Rcic.Declarative.constsBelow_instantiate
#print axioms Rcic.Declarative.constsBelow_of_instantiate
#print axioms Rcic.Declarative.constsBelow_instantiateLevels
#print axioms Rcic.Declarative.occursConst_instantiateLevels
#print axioms Rcic.Declarative.ConstsIn_instantiateLevels
#print axioms Rcic.Declarative.ctxConstsBelow_get
#print axioms Rcic.Declarative.ctxConstsBelow_of_cons
#print axioms Rcic.Declarative.ctxConstsBelow_cons_of
#print axioms Rcic.Declarative.lookupType_of_get?_assumption
#print axioms Rcic.Declarative.lookupType_of_get?_letBinding
#print axioms Rcic.Declarative.lookupValue_of_get?_letBinding
#print axioms Rcic.Declarative.ctxConstsBelow_lookupType
#print axioms Rcic.Declarative.ctxConstsBelow_lookupValue
#print axioms Rcic.Declarative.EnvAgreeBelow.refl
#print axioms Rcic.Declarative.EnvAgreeBelow.symm
#print axioms Rcic.Declarative.EnvAgreeBelow.trans
#print axioms Rcic.Declarative.EnvAgreeBelow.mono
#print axioms Rcic.Declarative.EnvAgreeBelow.extendEnv
#print axioms Rcic.Declarative.EnvAgreeBelow.extendEnv_left
#print axioms Rcic.Declarative.EnvAgreeBelow.groupEnvT
#print axioms Rcic.Declarative.EnvAgreeBelow.groupEnvT_self
#print axioms Rcic.Declarative.GroupInScopeT.ctorRef_gt
#print axioms Rcic.Declarative.member_of_occursConst_below
#print axioms Rcic.Declarative.EnvAgreeBelow.resolve
#print axioms Rcic.Declarative.envWfT_body_constsIn
#print axioms Rcic.Declarative.envWfT_body_constsIn_levels

/-! ## §5 S2 — the mutual strengthening skeleton's open arms, as named premises

The S2 theorem transports `HasTyT`/`ConvT`/`TyConvT` derivations from `E'` to
`E` under `EnvAgreeBelow E' E k` when the subject, type, and context name no
constant at or past `k`. The arm-by-arm audit (this section is the audit made
executable — the plan's `(htrans : TransStrengthenArm k E E')` rule, #6394)
finds TEN arms that endpoint cleanliness does not determine, not the plan's
estimated four; each is an explicit named premise below, house style
(`ConvTEtaLeftT`/`DT009T_endpointsS`: debts carry exactly the gap the rule
leaves, never a silent assumption):

HIDDEN INTERMEDIATE — the rule's middle term/type is unconstrained by the
conclusion's endpoints, so the induction hypotheses cannot be applied (this is
the wall `RcicTypedScopeCheck.lean:38-44` names; `S4`'s `cleanDeriv` route is
the intended discharge, and `trans` specifically waits on W-ATR-1 per the
approved plan):

* `HasTyT.app`   — the function's domain `A` is not a subterm of `.app f a`
  nor of `instantiate0 a B` (only `B` is recovered, via
  `constsBelow_of_instantiate`);
* `HasTyT.conv`  — the converted-from type `A`;
* `ConvT.app`    — the same hidden domain in the congruence rule;
* `ConvT.tyConv` — the converted-at type `A`;
* `ConvT.trans`  — the middle term `b`;
* `TyConvT.trans`— the middle type `B`;

MEMBER-SUPPLIED — facts the derivation reads from the environment rather than
from the judgment's own fields. S3 closed both inside the induction (§5b):
`ConvT.delta`'s body bound comes from `envWfT_body_constsBelow`
(`envWfT_bodyConsts_before`'s rank bound crossed to a ref bound by the
`RankCoherentBelow` premise), and `ConvT.iota`'s witness replays by
`derivedIota_of_agreeBelow` off `constsBelow k lhs`. Their sub-derivations
(`hb`, `hlhs`, `hrhs`) are structural subterms, so the recursive calls are
legal and no arm-shaped premise is needed — a standalone discharge would
instead force a self-referential arms bundle:

* `ConvT.delta` — `constsBelow k (instantiateLevels ls b)` for the member body;
* `ConvT.iota`  — `DerivedIota E lhs rhs` replay under agreement;

EXPANSION — the literal's expansion is not a subterm of `.lit t`:

* `HasTyT.lit` — `constsBelow k (natExpand t)`;
* `ConvT.lit`  — `constsBelow k exp` for `LiteralExpansion t exp`.

Every other arm closes inside the mutual induction: `sort`, `bvar`, `const`
(the ref resolves identically below `k`), `pi`, `lam`, `letE`, `refl`, `symm`,
`beta`, `zeta`, `zetaLocal` (the stored value's cleanliness comes from the
right endpoint; `ctxConstsBelow_lookupValue`/`lookupType` is the alternative
supply), the `lam`/`pi`/`letE` congruences, `sorts`, `consts`, `eta`, `irr`,
`TyConvT.refl`/`of`. -/

/-- DEBT (app, typed): the `app` rule's hidden domain. Only the endpoint
    cleanliness the site can supply is carried; `B` is recoverable through
    `constsBelow_of_instantiate` but `A` is not. -/
def HasTyTAppStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {f a A B : Expr Nat},
    HasTyT E' n Γ f (.pi A B) → HasTyT E' n Γ a A →
    constsBelow k f = true → constsBelow k a = true →
    constsBelow k (instantiate0 a B) = true →
    ctxConstsBelow k Γ = true →
    Nonempty (HasTyT E n Γ (.app f a) (instantiate0 a B))

/-- DEBT (lit, typed): the `natExpand t` expansion's constants are not
    bounded by `constsBelow k (.lit t)`. -/
def HasTyTLitStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {t : Nat} {T : Expr Nat},
    HasTyT E' n Γ (natExpand t) T →
    constsBelow k T = true → ctxConstsBelow k Γ = true →
    Nonempty (HasTyT E n Γ (.lit t) T)

/-- DEBT (conv, typed): the converted-from type `A` is a hidden
    intermediate. -/
def HasTyTConvStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {e A B : Expr Nat} {u : Level},
    HasTyT E' n Γ e A → ConvT E' n Γ A B (.sort u) →
    constsBelow k e = true → constsBelow k B = true →
    ctxConstsBelow k Γ = true →
    Nonempty (HasTyT E n Γ e B)

/-- DEBT (trans): the middle term `b` is unconstrained by endpoint
    cleanliness — the wall `RcicTypedScopeCheck.lean:38-44` names. -/
def ConvTTransStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {a b c A : Expr Nat},
    ConvT E' n Γ a b A → ConvT E' n Γ b c A →
    constsBelow k a = true → constsBelow k c = true →
    constsBelow k A = true → ctxConstsBelow k Γ = true →
    Nonempty (ConvT E n Γ a c A)

/-- DEBT (delta), discharged by S3: the unfolded member body's bound. The
    site resolves the member below `k` (`E.members r = some m` carried
    resolved); what it cannot supply is `constsBelow k (instantiateLevels
    ls b)` — supplied inside the induction by `envWfT_body_constsBelow`
    (§5b, `envWfT_bodyConsts_before` + `RankCoherentBelow`). -/
def ConvTDeltaStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat},
    E'.members r = some m → E.members r = some m → m.body = some b →
    transparent m.mclass = true → ls.length = m.arity →
    levelsBounded n ls = true →
    HasTyT E' n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype) →
    constsBelow k (instantiateLevels ls m.mtype) = true →
    ctxConstsBelow k Γ = true →
    Nonempty (ConvT E n Γ (.const r ls) (instantiateLevels ls b)
      (instantiateLevels ls m.mtype))

/-- DEBT (iota), discharged by S3: the `DerivedIota` witness replays in
    `E` inside the induction by `derivedIota_of_agreeBelow` (§5b) — the
    witness's three member references land below `k` off `constsBelow k
    lhs`, so agreeing lookups rebuild it. -/
def ConvTIotaStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {lhs rhs T : Expr Nat},
    DerivedIota E' lhs rhs →
    HasTyT E' n Γ lhs T → HasTyT E' n Γ rhs T →
    constsBelow k lhs = true → constsBelow k rhs = true →
    constsBelow k T = true → ctxConstsBelow k Γ = true →
    Nonempty (ConvT E n Γ lhs rhs T)

/-- DEBT (lit, conversion): the expansion `exp` is hidden. -/
def ConvTLitStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {t : Nat} {exp T : Expr Nat},
    LiteralExpansion t exp → HasTyT E' n Γ exp T →
    constsBelow k T = true → ctxConstsBelow k Γ = true →
    Nonempty (ConvT E n Γ (.lit t) exp T)

/-- DEBT (app congruence): the shared π-domain `A` is hidden. -/
def ConvTAppStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {f g a b A B : Expr Nat},
    ConvT E' n Γ f g (.pi A B) → ConvT E' n Γ a b A →
    constsBelow k f = true → constsBelow k g = true →
    constsBelow k a = true → constsBelow k b = true →
    constsBelow k (instantiate0 a B) = true →
    ctxConstsBelow k Γ = true →
    Nonempty (ConvT E n Γ (.app f a) (.app g b) (instantiate0 a B))

/-- DEBT (tyConv): the converted-at type `A` is hidden. -/
def ConvTTyConvStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {a b A A' : Expr Nat} {u : Level},
    ConvT E' n Γ a b A → ConvT E' n Γ A A' (.sort u) →
    constsBelow k a = true → constsBelow k b = true →
    constsBelow k A' = true → ctxConstsBelow k Γ = true →
    Nonempty (ConvT E n Γ a b A')

/-- DEBT (tyConv trans): the middle type `B` is hidden. -/
def TyConvTTransStrengthenArm (E' E : ResolvedEnv) (n k : Nat) : Prop :=
  ∀ {Γ : LCtx} {A B C : Expr Nat},
    TyConvT E' n Γ A B → TyConvT E' n Γ B C →
    constsBelow k A = true → constsBelow k C = true →
    ctxConstsBelow k Γ = true →
    Nonempty (TyConvT E n Γ A C)

/-- the open arms, bundled: each field is the one premise its arm needs.
    S3 discharged the two member-supplied arms inside the induction —
    `ConvT.delta` via `RankCoherentBelow` + `envWfT_bodyConsts_before`,
    `ConvT.iota` via `derivedIota_of_agreeBelow` (§5b) — leaving the six
    hidden-intermediate and two expansion debts for S4 (`cleanDeriv`;
    `ConvT.trans` may wait on W-ATR-1). The discharged arm types
    (`ConvTDeltaStrengthenArm`, `ConvTIotaStrengthenArm`) stay defined:
    they record the gap's shape, and their names are sealed. -/
structure StrengthenArms (E' E : ResolvedEnv) (n k : Nat) : Prop where
  app : HasTyTAppStrengthenArm E' E n k
  lit : HasTyTLitStrengthenArm E' E n k
  conv : HasTyTConvStrengthenArm E' E n k
  ctrans : ConvTTransStrengthenArm E' E n k
  clit : ConvTLitStrengthenArm E' E n k
  capp : ConvTAppStrengthenArm E' E n k
  ctyconv : ConvTTyConvStrengthenArm E' E n k
  ttrans : TyConvTTransStrengthenArm E' E n k

/-! ## §5b S3: the δ and ι discharges -/

/-- bound below `k` when every occurring constant is — the converse of
    `lt_of_constsBelow`. -/
theorem constsBelow_of_forall {k : Nat} :
    (e : Expr Nat) → (∀ r, occursConst r e = true → r < k) →
      constsBelow k e = true
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const r _, h =>
      decide_eq_true (h r (by simp only [occursConst, decide_eq_true_eq]))
  | .lit t, h => by
      cases t with
      | zero =>
          simp only [constsBelow, decide_eq_true_eq]
          exact h 1 rfl
      | succ _ =>
          simp only [constsBelow, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨h 1 rfl, h 2 rfl⟩
  | .app f x, h => by
      simp only [constsBelow, Bool.and_eq_true]
      refine ⟨constsBelow_of_forall f ?_, constsBelow_of_forall x ?_⟩
      · intro r hr
        exact h r (by simp only [occursConst, Bool.or_eq_true]; exact Or.inl hr)
      · intro r hr
        exact h r (by simp only [occursConst, Bool.or_eq_true]; exact Or.inr hr)
  | .lam a b, h => by
      simp only [constsBelow, Bool.and_eq_true]
      refine ⟨constsBelow_of_forall a ?_, constsBelow_of_forall b ?_⟩
      · intro r hr
        exact h r (by simp only [occursConst, Bool.or_eq_true]; exact Or.inl hr)
      · intro r hr
        exact h r (by simp only [occursConst, Bool.or_eq_true]; exact Or.inr hr)
  | .pi a b, h => by
      simp only [constsBelow, Bool.and_eq_true]
      refine ⟨constsBelow_of_forall a ?_, constsBelow_of_forall b ?_⟩
      · intro r hr
        exact h r (by simp only [occursConst, Bool.or_eq_true]; exact Or.inl hr)
      · intro r hr
        exact h r (by simp only [occursConst, Bool.or_eq_true]; exact Or.inr hr)
  | .letE a v b, h => by
      simp only [constsBelow, Bool.and_eq_true]
      refine ⟨⟨constsBelow_of_forall a ?_, constsBelow_of_forall v ?_⟩,
        constsBelow_of_forall b ?_⟩
      · intro r hr
        exact h r (by
          simp only [occursConst, Bool.or_eq_true]; exact Or.inl (Or.inl hr))
      · intro r hr
        exact h r (by
          simp only [occursConst, Bool.or_eq_true]
          exact Or.inl (Or.inr hr))
      · intro r hr
        exact h r (by
          simp only [occursConst, Bool.or_eq_true]
          exact Or.inr hr)

/-- the `k`-cut is rank-coherent in `E'`: every member at or above `k` was
    admitted strictly after every member below `k`. `groupEnvT`-grown
    tails satisfy it when the base's members sit below the family's ref —
    the group step ranks every member it adds at the step's depth, above
    all earlier admissions. Without it nothing orders refs by admission:
    `EnvWfT` admits at any fresh ref, so `envWfT_bodyConsts_before`'s
    rank bound crosses to a ref bound only here. -/
def RankCoherentBelow {E' : ResolvedEnv} (hW : EnvWfT E') (k : Nat) : Prop :=
  ∀ r' r : Nat, (∃ m', E'.members r' = some m') → k ≤ r' →
    (∃ m, E'.members r = some m) → r < k → hW.rank r < hW.rank r'

/-- S3-δ: a member's stored body names only below-`k` constants under rank
    coherence — `envWfT_bodyConsts_before` ranks each of them strictly
    before `r`, and `r < k` forbids a ≥ `k` constant ranking that low. -/
theorem envWfT_body_constsBelow {E' : ResolvedEnv} (hW : EnvWfT E') {k : Nat}
    (hcoh : RankCoherentBelow hW k) {r : Nat} {m : CheckedMember}
    {b : Expr Nat}
    (hm : E'.members r = some m) (hr : r < k) (hb : m.body = some b) :
    constsBelow k b = true := by
  apply constsBelow_of_forall
  intro r' ho
  rcases Nat.lt_or_ge r' k with hlt | hge
  · exact hlt
  · obtain ⟨m', hm'⟩ :=
      member_of_occursConst b (envWfT_body_constsIn hW hm hb) ho
    have hrr := envWfT_bodyConsts_before hW r m b r' hm hb ho
    exact absurd (hcoh r' r ⟨m', hm'⟩ hge ⟨m, hm⟩ hr) (Nat.lt_asymm hrr)

/-- the fold's head constants occur in the folded application. -/
theorem occursConst_foldApps_head {r : Nat} (f : Expr Nat) :
    (xs : List (Expr Nat)) → occursConst r f = true →
      occursConst r (foldApps f xs) = true
  | [], h => h
  | x :: xs, h =>
      occursConst_foldApps_head (.app f x) xs (by
        simp only [occursConst, Bool.or_eq_true]; exact Or.inl h)

/-- a member argument's constants occur in the fold. -/
theorem occursConst_foldApps_of_mem {r : Nat} {x f : Expr Nat}
    {xs : List (Expr Nat)} (hx : x ∈ xs) (h : occursConst r x = true) :
    occursConst r (foldApps f xs) = true := by
  induction xs generalizing f with
  | nil => cases hx
  | cons y ys ih =>
      simp only [foldApps]
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact occursConst_foldApps_head _ _ (by
          simp only [occursConst, Bool.or_eq_true]; exact Or.inr h)
      · exact ih hmem

/-- the recursor head's reference occurs in an ι left-hand side. -/
theorem occursConst_iotaLhs_recRef {E : ResolvedEnv} (w : IotaWitness E) :
    occursConst w.recRef (iotaLhsOf w) = true := by
  show occursConst w.recRef
    (foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w])) = true
  exact occursConst_foldApps_head _ _ (by
    simp only [occursConst, decide_eq_true_eq])

/-- the major's constructor head occurs in an ι left-hand side. -/
theorem occursConst_iotaLhs_ctorRef {E : ResolvedEnv} (w : IotaWitness E) :
    occursConst w.ctorRef (iotaLhsOf w) = true := by
  show occursConst w.ctorRef
    (foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w])) = true
  apply occursConst_foldApps_of_mem (x := ctorMajor w)
  · exact List.mem_append_right _ (List.mem_singleton_self _)
  · show occursConst w.ctorRef
      (foldApps (.const w.ctorRef w.lsC) (ctorSpine w)) = true
    exact occursConst_foldApps_head _ _ (by
      simp only [occursConst, decide_eq_true_eq])

/-- S3-ι: a `DerivedIota` whose lhs is clean replays in the agreeing
    environment. The witness reads exactly three member lookups (family,
    constructor, recursor); `recRef` and `ctorRef` occur in the lhs, and
    `familyRef < ctorRef` by `hctorIdx`, so all three land below `k` and
    resolve identically. Every other field is data, so the replayed
    witness's `iotaLhsOf`/`iotaRhsOf` are literally the same. -/
def derivedIota_of_agreeBelow {E' E : ResolvedEnv} {k : Nat}
    (hagree : EnvAgreeBelow E' E k) {lhs rhs : Expr Nat}
    (h : DerivedIota E' lhs rhs) (hl : constsBelow k lhs = true) :
    DerivedIota E lhs rhs := by
  cases h with
  | of w =>
      have hre : w.recRef < k :=
        lt_of_constsBelow _ hl (occursConst_iotaLhs_recRef w)
      have hct : w.ctorRef < k :=
        lt_of_constsBelow _ hl (occursConst_iotaLhs_ctorRef w)
      have hfa : w.familyRef < k := by have h := w.hctorIdx; omega
      exact .of { w with
        hrec := hagree w.recRef hre ▸ w.hrec,
        hctor := hagree w.ctorRef hct ▸ w.hctor,
        hfam := hagree w.familyRef hfa ▸ w.hfam }

/-! ## §6 the mutual skeleton -/

mutual

/-- S3: `HasTyT` strengthens along `EnvAgreeBelow E' E k` — a derivation of
    a clean judgment replays in the smaller environment, every `.const`
    lookup landing below `k` and resolving identically. The remaining arms
    endpoint cleanliness leaves open are `arms`' named fields (§5); `hW` is
    the plan-stated premise and `hcoh` the S3 rank-coherence premise —
    `convT_strengthen`'s `delta` arm reads both (the body bound crosses
    from rank to ref there), while `iota` replays the `DerivedIota`
    witness under `hagree` alone. -/
def hasTyT_strengthen {E E' : ResolvedEnv} (hW : EnvWfT E') {n k : Nat}
    (hagree : EnvAgreeBelow E' E k) (hcoh : RankCoherentBelow hW k)
    (arms : StrengthenArms E' E n k) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E' n Γ e A →
    constsBelow k e = true → constsBelow k A = true →
    ctxConstsBelow k Γ = true → Nonempty (HasTyT E n Γ e A)
  | _, _, _, .sort _ _, _, _, _ => ⟨.sort _ _⟩
  | _, _, _, .bvar _ _ _ h, _, _, _ => ⟨.bvar _ _ _ h⟩
  | _, _, _, .const _ r _ m hres hlen hwf, he, _, _ => by
      have hr : r < k := by
        simp only [constsBelow, decide_eq_true_eq] at he; exact he
      exact ⟨.const _ r _ m (hagree r hr ▸ hres) hlen hwf⟩
  | _, _, _, .pi _ A u B v hA hB, he, _, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he
      refine (hasTyT_strengthen hW hagree hcoh arms hA he.1 rfl hΓ).elim fun hA' => ?_
      refine (hasTyT_strengthen hW hagree hcoh arms hB he.2 rfl
        (ctxConstsBelow_cons_of he.1 hΓ)).elim fun hB' => ?_
      exact ⟨.pi _ A u B v hA' hB'⟩
  | _, _, _, .lam _ A _ body B hA hbody, he, hT, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he hT
      refine (hasTyT_strengthen hW hagree hcoh arms hA he.1 rfl hΓ).elim fun hA' => ?_
      refine (hasTyT_strengthen hW hagree hcoh arms hbody he.2 hT.2
        (ctxConstsBelow_cons_of he.1 hΓ)).elim fun hbody' => ?_
      exact ⟨.lam _ A _ body B hA' hbody'⟩
  | _, _, _, .app _ _ _ _ _ hf ha, he, hT, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he
      exact arms.app hf ha he.1 he.2 hT hΓ
  | _, _, _, .letE _ A _ value B body hA hv hb, he, hT, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he
      have hBc : constsBelow k B = true :=
        constsBelow_of_instantiate _ 0 _ hT
      refine (hasTyT_strengthen hW hagree hcoh arms hA he.1.1 rfl hΓ).elim fun hA' => ?_
      refine (hasTyT_strengthen hW hagree hcoh arms hv he.1.2 he.1.1 hΓ).elim
        fun hv' => ?_
      have hd : declConstsBelow k (.letBinding A value) = true := by
        simp only [declConstsBelow, Bool.and_eq_true]; exact ⟨he.1.1, he.1.2⟩
      refine (hasTyT_strengthen hW hagree hcoh arms hb he.2 hBc
        (ctxConstsBelow_cons_of hd hΓ)).elim fun hb' => ?_
      exact ⟨.letE _ A _ value B body hA' hv' hb'⟩
  | _, _, _, .lit _ _ _ hexp, _, hT, hΓ => arms.lit hexp hT hΓ
  | _, _, _, .conv _ _ _ _ _ h hc, he, hT, hΓ =>
      arms.conv h hc he hT hΓ

/-- `ConvT` at a fixed type strengthens along the same agreement. -/
def convT_strengthen {E E' : ResolvedEnv} (hW : EnvWfT E') {n k : Nat}
    (hagree : EnvAgreeBelow E' E k) (hcoh : RankCoherentBelow hW k)
    (arms : StrengthenArms E' E n k) :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvT E' n Γ a b T →
    constsBelow k a = true → constsBelow k b = true →
    constsBelow k T = true → ctxConstsBelow k Γ = true →
    Nonempty (ConvT E n Γ a b T)
  | _, _, _, _, .refl _ _ _ h, he, _, hT, hΓ =>
      (hasTyT_strengthen hW hagree hcoh arms h he hT hΓ).elim fun h' =>
        ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .symm _ _ _ _ h, he_l, he_r, hT, hΓ =>
      (convT_strengthen hW hagree hcoh arms h he_r he_l hT hΓ).elim fun h' =>
        ⟨.symm _ _ _ _ h'⟩
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, he_l, he_r, hT, hΓ =>
      arms.ctrans h1 h2 he_l he_r hT hΓ
  | _, _, _, _, .beta _ A body arg B u hA hbody harg, he_l, _, hT, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he_l
      have hBc : constsBelow k B = true :=
        constsBelow_of_instantiate _ 0 _ hT
      refine (hasTyT_strengthen hW hagree hcoh arms hA he_l.1.1 rfl hΓ).elim
        fun hA' => ?_
      refine (hasTyT_strengthen hW hagree hcoh arms hbody he_l.1.2 hBc
        (ctxConstsBelow_cons_of he_l.1.1 hΓ)).elim fun hbody' => ?_
      refine (hasTyT_strengthen hW hagree hcoh arms harg he_l.2 he_l.1.1 hΓ).elim
        fun harg' => ?_
      exact ⟨.beta _ A body arg B u hA' hbody' harg'⟩
  | _, _, _, _, .zeta _ A value body B u hA hv hb, he_l, _, hT, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he_l
      have hBc : constsBelow k B = true :=
        constsBelow_of_instantiate _ 0 _ hT
      refine (hasTyT_strengthen hW hagree hcoh arms hA he_l.1.1 rfl hΓ).elim
        fun hA' => ?_
      refine (hasTyT_strengthen hW hagree hcoh arms hv he_l.1.2 he_l.1.1 hΓ).elim
        fun hv' => ?_
      have hd : declConstsBelow k (.letBinding A value) = true := by
        simp only [declConstsBelow, Bool.and_eq_true]
        exact ⟨he_l.1.1, he_l.1.2⟩
      refine (hasTyT_strengthen hW hagree hcoh arms hb he_l.2 hBc
        (ctxConstsBelow_cons_of hd hΓ)).elim fun hb' => ?_
      exact ⟨.zeta _ A value body B u hA' hv' hb'⟩
  | _, _, _, _, .zetaLocal _ _ _ _ hval hty hv, _, he_r, hT, hΓ =>
      (hasTyT_strengthen hW hagree hcoh arms hv he_r hT hΓ).elim fun hv' =>
        ⟨.zetaLocal _ _ _ _ hval hty hv'⟩
  | _, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb, he_l, _, hT, hΓ => by
      have hr : r < k := by
        simp only [constsBelow, decide_eq_true_eq] at he_l; exact he_l
      have hbc : constsBelow k (instantiateLevels ls b) = true := by
        rw [constsBelow_instantiateLevels]
        exact envWfT_body_constsBelow hW hcoh hres hr hbody
      refine (hasTyT_strengthen hW hagree hcoh arms hb hbc hT hΓ).elim
        fun hbody' => ?_
      exact ⟨.delta _ r ls m b (hagree r hr ▸ hres) hbody htr hlen hwf hbody'⟩
  | _, _, _, _, .iota _ _ _ _ h hlhs hrhs, he_l, he_r, hT, hΓ =>
      (hasTyT_strengthen hW hagree hcoh arms hlhs he_l hT hΓ).elim fun hl' =>
      (hasTyT_strengthen hW hagree hcoh arms hrhs he_r hT hΓ).elim fun hr' =>
        ⟨.iota _ _ _ _ (derivedIota_of_agreeBelow hagree h he_l) hl' hr'⟩
  | _, _, _, _, .lit _ _ _ _ h hexp, _, _, hT, hΓ =>
      arms.clit h hexp hT hΓ
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, he_l, he_r, hT, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he_l he_r
      exact arms.capp h1 h2 he_l.1 he_r.1 he_l.2 he_r.2 hT hΓ
  | _, _, _, _, .lam _ A A' b b' B u hA hb, he_l, he_r, hT, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he_l he_r hT
      refine (convT_strengthen hW hagree hcoh arms hA he_l.1 he_r.1 rfl hΓ).elim
        fun hA' => ?_
      refine (convT_strengthen hW hagree hcoh arms hb he_l.2 he_r.2 hT.2
        (ctxConstsBelow_cons_of he_l.1 hΓ)).elim fun hb' => ?_
      exact ⟨.lam _ A A' b b' B u hA' hb'⟩
  | _, _, _, _, .pi _ A A' B B' u v hA hB, he_l, he_r, _, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he_l he_r
      refine (convT_strengthen hW hagree hcoh arms hA he_l.1 he_r.1 rfl hΓ).elim
        fun hA' => ?_
      refine (convT_strengthen hW hagree hcoh arms hB he_l.2 he_r.2 rfl
        (ctxConstsBelow_cons_of he_l.1 hΓ)).elim fun hB' => ?_
      exact ⟨.pi _ A A' B B' u v hA' hB'⟩
  | _, _, _, _, .letE _ A A' v v' b b' B u hA hv hb, he_l, he_r, hT, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he_l he_r
      have hBc : constsBelow k B = true :=
        constsBelow_of_instantiate _ 0 _ hT
      refine (convT_strengthen hW hagree hcoh arms hA he_l.1.1 he_r.1.1 rfl hΓ).elim
        fun hA' => ?_
      refine (convT_strengthen hW hagree hcoh arms hv he_l.1.2 he_r.1.2 he_l.1.1
        hΓ).elim fun hv' => ?_
      have hd : declConstsBelow k (.letBinding A v) = true := by
        simp only [declConstsBelow, Bool.and_eq_true]
        exact ⟨he_l.1.1, he_l.1.2⟩
      refine (convT_strengthen hW hagree hcoh arms hb he_l.2 he_r.2 hBc
        (ctxConstsBelow_cons_of hd hΓ)).elim fun hb' => ?_
      exact ⟨.letE _ A A' v v' b b' B u hA' hv' hb'⟩
  | _, _, _, _, .sorts _ _ _ h, _, _, _, _ => ⟨.sorts _ _ _ h⟩
  | _, _, _, _, .consts _ r _ _ m hres hlen hwf hwf' h, he_l, _, _, _ => by
      have hr : r < k := by
        simp only [constsBelow, decide_eq_true_eq] at he_l; exact he_l
      exact ⟨.consts _ r _ _ m (hagree r hr ▸ hres) hlen hwf hwf' h⟩
  | _, _, _, _, .eta _ f A B h, he_l, _, hT, hΓ => by
      simp only [constsBelow, Bool.and_eq_true] at he_l
      have hf : constsBelow k f = true := by
        have hf0 := he_l.2.1
        rwa [constsBelow_lift] at hf0
      refine (hasTyT_strengthen hW hagree hcoh arms h hf hT hΓ).elim fun h' => ?_
      exact ⟨.eta _ f A B h'⟩
  | _, _, _, _, .irr _ _ _ _ hP hp hq, he_l, he_r, hT, hΓ => by
      refine (hasTyT_strengthen hW hagree hcoh arms hP hT rfl hΓ).elim fun hP' => ?_
      refine (hasTyT_strengthen hW hagree hcoh arms hp he_l hT hΓ).elim fun hp' => ?_
      refine (hasTyT_strengthen hW hagree hcoh arms hq he_r hT hΓ).elim fun hq' => ?_
      exact ⟨.irr _ _ _ _ hP' hp' hq'⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, he_l, he_r, hT, hΓ =>
      arms.ctyconv h hA he_l he_r hT hΓ

/-- `TyConvT` chains strengthen leg by leg along the same agreement. -/
def tyConvT_strengthen {E E' : ResolvedEnv} (hW : EnvWfT E') {n k : Nat}
    (hagree : EnvAgreeBelow E' E k) (hcoh : RankCoherentBelow hW k)
    (arms : StrengthenArms E' E n k) :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT E' n Γ A B →
    constsBelow k A = true → constsBelow k B = true →
    ctxConstsBelow k Γ = true → Nonempty (TyConvT E n Γ A B)
  | _, _, _, .refl _ _, _, _, _ => ⟨.refl _ _⟩
  | _, _, _, .of _ _ _ u h, he_a, he_b, hΓ =>
      (convT_strengthen hW hagree hcoh arms h he_a he_b rfl hΓ).elim fun h' =>
        ⟨.of _ _ _ u h'⟩
  | _, _, _, .trans _ _ _ _ h1 h2, he_a, he_b, hΓ =>
      arms.ttrans h1 h2 he_a he_b hΓ

end

/-! ## §7 S4: the `cleanDeriv`-conditioned theorem

`cleanHasTyT`/`cleanConvT`/`cleanTyConvT` mark every node of a derivation
with `constsBelow k` on its own conclusion, recursively through the
sub-derivations. Where endpoint cleanliness left the §5 arms open,
node-wise cleanliness closes all of them inside the induction: a rule's
hidden intermediates are always some sub-derivation's conclusion, whose
cleanliness the recursive hypothesis now carries. So the conditioned trio
needs only `hagree` — `delta`'s body bound is `hb`'s own node conclusion
(no `RankCoherentBelow` here), `iota` replays the `DerivedIota` witness off
`constsBelow k lhs` as in §5b, and the §5 arms have no premise left to ask
for. The unconditioned route still waits on W-ATR-1 (#6293): what is
conditioned is that the derivation's own nodes name nothing at or past `k`
— `checkT`'s output satisfies it (§7c) but arbitrary derivations need
not. -/

mutual

/-- S4's `cleanDeriv`, `HasTyT`: every node's own conclusion — subject and
    type — names no constant at or past `k`, recursively through the
    sub-derivations. The node's exprs appear as `constsBelow` conjuncts so
    a hidden intermediate (the `A` of `app`/`conv`) is always recovered
    from the node that introduces it. -/
def cleanHasTyT {E : ResolvedEnv} {n : Nat} (k : Nat) :
    {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → Prop
  | _, _, _, .sort _ _ => True
  | _, _, _, .bvar _ _ A _ => constsBelow k A = true
  | _, _, _, .const _ r ls m _ _ _ =>
      constsBelow k (.const r ls) = true ∧
        constsBelow k (instantiateLevels ls m.mtype) = true
  | _, _, _, .pi _ A _ B _ hA hB =>
      constsBelow k (.pi A B) = true ∧ cleanHasTyT k hA ∧ cleanHasTyT k hB
  | _, _, _, .lam _ A _ body B hA hbody =>
      constsBelow k (.lam A body) = true ∧ constsBelow k (.pi A B) = true ∧
        cleanHasTyT k hA ∧ cleanHasTyT k hbody
  | _, _, _, .app _ f a _ B hf ha =>
      constsBelow k (.app f a) = true ∧
        constsBelow k (instantiate0 a B) = true ∧
        cleanHasTyT k hf ∧ cleanHasTyT k ha
  | _, _, _, .letE _ A _ value B body hA hv hb =>
      constsBelow k (.letE A value body) = true ∧
        constsBelow k (instantiate0 value B) = true ∧
        cleanHasTyT k hA ∧ cleanHasTyT k hv ∧ cleanHasTyT k hb
  | _, _, _, .lit _ t T hexp =>
      constsBelow k (.lit t) = true ∧ constsBelow k T = true ∧ cleanHasTyT k hexp
  | _, _, _, .conv _ e _ B _ h hc =>
      constsBelow k e = true ∧ constsBelow k B = true ∧
        cleanHasTyT k h ∧ cleanConvT k hc

/-- `cleanDeriv`, `ConvT`: the three conclusion exprs clean at every
    node. -/
def cleanConvT {E : ResolvedEnv} {n : Nat} (k : Nat) :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Prop
  | _, _, _, _, .refl _ a A h =>
      constsBelow k a = true ∧ constsBelow k A = true ∧ cleanHasTyT k h
  | _, _, _, _, .symm _ a b A h =>
      constsBelow k b = true ∧ constsBelow k a = true ∧
        constsBelow k A = true ∧ cleanConvT k h
  | _, _, _, _, .trans _ a _ c A h1 h2 =>
      constsBelow k a = true ∧ constsBelow k c = true ∧
        constsBelow k A = true ∧ cleanConvT k h1 ∧ cleanConvT k h2
  | _, _, _, _, .beta _ A body arg B _ hA hbody harg =>
      constsBelow k (.app (.lam A body) arg) = true ∧
        constsBelow k (instantiate0 arg body) = true ∧
        constsBelow k (instantiate0 arg B) = true ∧
        cleanHasTyT k hA ∧ cleanHasTyT k hbody ∧ cleanHasTyT k harg
  | _, _, _, _, .zeta _ A value body B _ hA hv hb =>
      constsBelow k (.letE A value body) = true ∧
        constsBelow k (instantiate0 value body) = true ∧
        constsBelow k (instantiate0 value B) = true ∧
        cleanHasTyT k hA ∧ cleanHasTyT k hv ∧ cleanHasTyT k hb
  | _, _, _, _, .zetaLocal _ _ A v _ _ hv =>
      constsBelow k v = true ∧ constsBelow k A = true ∧ cleanHasTyT k hv
  | _, _, _, _, .delta _ r ls m b _ _ _ _ _ hb =>
      constsBelow k (.const r ls) = true ∧
        constsBelow k (instantiateLevels ls b) = true ∧
        constsBelow k (instantiateLevels ls m.mtype) = true ∧
        cleanHasTyT k hb
  | _, _, _, _, .iota _ lhs rhs T _ hlhs hrhs =>
      constsBelow k lhs = true ∧ constsBelow k rhs = true ∧
        constsBelow k T = true ∧ cleanHasTyT k hlhs ∧ cleanHasTyT k hrhs
  | _, _, _, _, .lit _ _ exp T _ hexp =>
      constsBelow k exp = true ∧ constsBelow k T = true ∧
        cleanHasTyT k hexp
  | _, _, _, _, .app _ f g a b _ B h1 h2 =>
      constsBelow k (.app f a) = true ∧ constsBelow k (.app g b) = true ∧
        constsBelow k (instantiate0 a B) = true ∧
        cleanConvT k h1 ∧ cleanConvT k h2
  | _, _, _, _, .lam _ A A' b b' B _ hA hb =>
      constsBelow k (.lam A b) = true ∧ constsBelow k (.lam A' b') = true ∧
        constsBelow k (.pi A B) = true ∧ cleanConvT k hA ∧ cleanConvT k hb
  | _, _, _, _, .pi _ A A' B B' _ _ hA hB =>
      constsBelow k (.pi A B) = true ∧ constsBelow k (.pi A' B') = true ∧
        cleanConvT k hA ∧ cleanConvT k hB
  | _, _, _, _, .letE _ A A' v v' b b' B _ hA hv hb =>
      constsBelow k (.letE A v b) = true ∧
        constsBelow k (.letE A' v' b') = true ∧
        constsBelow k (instantiate0 v B) = true ∧
        cleanConvT k hA ∧ cleanConvT k hv ∧ cleanConvT k hb
  | _, _, _, _, .sorts _ _ _ _ => True
  | _, _, _, _, .consts _ r ls _ m _ _ _ _ _ =>
      constsBelow k (.const r ls) = true ∧
        constsBelow k (instantiateLevels ls m.mtype) = true
  | _, _, _, _, .eta _ f A B h =>
      constsBelow k (.lam A (.app (lift 0 1 f) (.bvar 0))) = true ∧
        constsBelow k f = true ∧ constsBelow k (.pi A B) = true ∧
        cleanHasTyT k h
  | _, _, _, _, .irr _ P p q hP hp hq =>
      constsBelow k p = true ∧ constsBelow k q = true ∧
        constsBelow k P = true ∧
        cleanHasTyT k hP ∧ cleanHasTyT k hp ∧ cleanHasTyT k hq
  | _, _, _, _, .tyConv _ a b _ A' _ h hA =>
      constsBelow k a = true ∧ constsBelow k b = true ∧
        constsBelow k A' = true ∧ cleanConvT k h ∧ cleanConvT k hA

/-- `cleanDeriv`, `TyConvT`: both endpoint types clean at every node. -/
def cleanTyConvT {E : ResolvedEnv} {n : Nat} (k : Nat) :
    {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B → Prop
  | _, _, _, .refl _ A => constsBelow k A = true
  | _, _, _, .of _ A B _ h =>
      constsBelow k A = true ∧ constsBelow k B = true ∧ cleanConvT k h
  | _, _, _, .trans _ A _ C h1 h2 =>
      constsBelow k A = true ∧ constsBelow k C = true ∧
        cleanTyConvT k h1 ∧ cleanTyConvT k h2

end

/-- `natExpand t`'s spine bottoms out at `const 1`: a bound on the
    expansion forces `1 < k`. -/
theorem natExpand_constsBelow_one {k : Nat} :
    (t : Nat) → constsBelow k (natExpand t) = true → 1 < k
  | 0, h => by
      simpa only [natExpand, litZero, constsBelow, decide_eq_true_eq] using h
  | t + 1, h => by
      simp only [natExpand, litSucc, constsBelow, Bool.and_eq_true] at h
      exact natExpand_constsBelow_one t h.2

/-- `.lit t` and `natExpand t` name the same constants ({1}, or {1,2} for
    `t ≥ 1`): a bound on the expansion is a bound on the literal. -/
theorem constsBelow_lit_of_natExpand {k : Nat} :
    (t : Nat) → constsBelow k (natExpand t) = true → constsBelow k (.lit t) = true
  | 0, h => h
  | t + 1, h => by
      simp only [natExpand, litSucc, constsBelow, Bool.and_eq_true,
        decide_eq_true_eq] at h
      simp only [constsBelow, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨natExpand_constsBelow_one t h.2, h.1⟩

/-- a clean `HasTyT` node's own conclusion is clean. -/
theorem cleanHasTyT_node {E : ResolvedEnv} {n k : Nat} {Γ : LCtx}
    {e A : Expr Nat} {h : HasTyT E n Γ e A} (hc : cleanHasTyT k h) :
    constsBelow k e = true ∧ constsBelow k A = true :=
  match h, hc with
  | .sort _ _, _ => ⟨rfl, rfl⟩
  | .bvar _ _ _ _, hc => ⟨rfl, hc⟩
  | .const _ _ _ _ _ _ _, hc => hc
  | .pi _ _ _ _ _ _ _, hc => ⟨hc.1, rfl⟩
  | .lam _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1⟩
  | .app _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1⟩
  | .letE _ _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1⟩
  | .lit _ _ _ _, hc => ⟨hc.1, hc.2.1⟩
  | .conv _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1⟩

/-- a clean `ConvT` node's own conclusion is clean. -/
theorem cleanConvT_node {E : ResolvedEnv} {n k : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {h : ConvT E n Γ a b T} (hc : cleanConvT k h) :
    constsBelow k a = true ∧ constsBelow k b = true ∧
      constsBelow k T = true :=
  match h, hc with
  | .refl _ _ _ _, hc => ⟨hc.1, hc.1, hc.2.1⟩
  | .symm _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .trans _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .beta _ _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .zeta _ _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .zetaLocal _ _ _ _ _ _ _, hc => ⟨rfl, hc.1, hc.2.1⟩
  | .delta _ _ _ _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .iota _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .lit _ _ _ _ hLE _, hc => by
      cases hLE
      exact ⟨constsBelow_lit_of_natExpand _ hc.1, hc.1, hc.2.1⟩
  | .app _ _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .lam _ _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .pi _ _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, rfl⟩
  | .letE _ _ _ _ _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .sorts _ _ _ _, _ => ⟨rfl, rfl, rfl⟩
  | .consts _ _ _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.1, hc.2⟩
  | .eta _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .irr _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩
  | .tyConv _ _ _ _ _ _ _ _, hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩

/-- a clean `TyConvT` node's own conclusion is clean. -/
theorem cleanTyConvT_node {E : ResolvedEnv} {n k : Nat} {Γ : LCtx}
    {A B : Expr Nat} {h : TyConvT E n Γ A B} (hc : cleanTyConvT k h) :
    constsBelow k A = true ∧ constsBelow k B = true := by
  cases h <;> simp only [cleanTyConvT] at hc
  · exact ⟨hc, hc⟩
  · exact ⟨hc.1, hc.2.1⟩
  · exact ⟨hc.1, hc.2.1⟩

mutual

/-- S4: `HasTyT` strengthens along `EnvAgreeBelow E' E k` on clean
    derivations — every node's own conclusion supplies the constant bound
    its parent rule needs, so all §5 debts close inside the induction and
    the only premises left are agreement (`hagree`) and context
    cleanliness. `delta`'s body bound rides inside `hb`'s clean (no
    `RankCoherentBelow` needed here); `iota` replays the `DerivedIota`
    witness off `constsBelow k lhs` as in §5b. -/
def hasTyT_strengthenC {E E' : ResolvedEnv} {n k : Nat}
    (hagree : EnvAgreeBelow E' E k) :
    {Γ : LCtx} → {e A : Expr Nat} → (h : HasTyT E' n Γ e A) →
    cleanHasTyT k h → ctxConstsBelow k Γ = true →
    Nonempty (HasTyT E n Γ e A)
  | _, _, _, .sort _ _, _, _ => ⟨.sort _ _⟩
  | _, _, _, .bvar _ _ _ h, _, _ => ⟨.bvar _ _ _ h⟩
  | _, _, _, .const _ r ls m hres hlen hwf, hc, _ => by
      have hr : r < k := by
        obtain ⟨hl, _⟩ := hc
        simp only [constsBelow, decide_eq_true_eq] at hl; exact hl
      exact ⟨.const _ r ls m (hagree r hr ▸ hres) hlen hwf⟩
  | _, _, _, .pi _ A u B v hA hB, hc, hΓ => by
      obtain ⟨he, hcA, hcB⟩ := hc
      simp only [constsBelow, Bool.and_eq_true] at he
      refine (hasTyT_strengthenC hagree hA hcA hΓ).elim fun hA' => ?_
      refine (hasTyT_strengthenC hagree hB hcB
        (ctxConstsBelow_cons_of he.1 hΓ)).elim fun hB' => ?_
      exact ⟨.pi _ A u B v hA' hB'⟩
  | _, _, _, .lam _ A u body B hA hbody, hc, hΓ => by
      obtain ⟨he, _, hcA, hcb⟩ := hc
      simp only [constsBelow, Bool.and_eq_true] at he
      refine (hasTyT_strengthenC hagree hA hcA hΓ).elim fun hA' => ?_
      refine (hasTyT_strengthenC hagree hbody hcb
        (ctxConstsBelow_cons_of he.1 hΓ)).elim fun hbody' => ?_
      exact ⟨.lam _ A u body B hA' hbody'⟩
  | _, _, _, .app _ f a A B hf ha, hc, hΓ => by
      obtain ⟨_, _, hcf, hca⟩ := hc
      refine (hasTyT_strengthenC hagree hf hcf hΓ).elim fun hf' => ?_
      refine (hasTyT_strengthenC hagree ha hca hΓ).elim fun ha' => ?_
      exact ⟨.app _ f a A B hf' ha'⟩
  | _, _, _, .letE _ A u value B body hA hv hb, hc, hΓ => by
      obtain ⟨he, _, hcA, hcv, hcb⟩ := hc
      simp only [constsBelow, Bool.and_eq_true] at he
      refine (hasTyT_strengthenC hagree hA hcA hΓ).elim fun hA' => ?_
      refine (hasTyT_strengthenC hagree hv hcv hΓ).elim fun hv' => ?_
      have hd : declConstsBelow k (.letBinding A value) = true := by
        simp only [declConstsBelow, Bool.and_eq_true]
        exact ⟨he.1.1, he.1.2⟩
      refine (hasTyT_strengthenC hagree hb hcb
        (ctxConstsBelow_cons_of hd hΓ)).elim fun hb' => ?_
      exact ⟨.letE _ A u value B body hA' hv' hb'⟩
  | _, _, _, .lit _ t _ hexp, hc, hΓ => by
      obtain ⟨_, _, hce⟩ := hc
      refine (hasTyT_strengthenC hagree hexp hce hΓ).elim fun hexp' => ?_
      exact ⟨.lit _ t _ hexp'⟩
  | _, _, _, .conv _ e A B u h hc2, hc, hΓ => by
      obtain ⟨_, _, hch, hcc⟩ := hc
      refine (hasTyT_strengthenC hagree h hch hΓ).elim fun h' => ?_
      refine (convT_strengthenC hagree hc2 hcc hΓ).elim fun hc' => ?_
      exact ⟨.conv _ e A B u h' hc'⟩

/-- `ConvT` at a fixed type strengthens along the same agreement on clean
    derivations. -/
def convT_strengthenC {E E' : ResolvedEnv} {n k : Nat}
    (hagree : EnvAgreeBelow E' E k) :
    {Γ : LCtx} → {a b T : Expr Nat} → (h : ConvT E' n Γ a b T) →
    cleanConvT k h → ctxConstsBelow k Γ = true →
    Nonempty (ConvT E n Γ a b T)
  | _, _, _, _, .refl _ _ _ h, hc, hΓ => by
      obtain ⟨_, _, hch⟩ := hc
      exact (hasTyT_strengthenC hagree h hch hΓ).elim fun h' =>
        ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .symm _ _ _ _ h, hc, hΓ => by
      obtain ⟨_, _, _, hch⟩ := hc
      exact (convT_strengthenC hagree h hch hΓ).elim fun h' =>
        ⟨.symm _ _ _ _ h'⟩
  | _, _, _, _, .trans _ a b c A h1 h2, hc, hΓ => by
      obtain ⟨_, _, _, hc1, hc2⟩ := hc
      refine (convT_strengthenC hagree h1 hc1 hΓ).elim fun h1' => ?_
      refine (convT_strengthenC hagree h2 hc2 hΓ).elim fun h2' => ?_
      exact ⟨.trans _ a b c A h1' h2'⟩
  | _, _, _, _, .beta _ A body arg B u hA hbody harg, hc, hΓ => by
      obtain ⟨he_l, _, _, hcA, hcb, hcarg⟩ := hc
      simp only [constsBelow, Bool.and_eq_true] at he_l
      refine (hasTyT_strengthenC hagree hA hcA hΓ).elim fun hA' => ?_
      refine (hasTyT_strengthenC hagree hbody hcb
        (ctxConstsBelow_cons_of he_l.1.1 hΓ)).elim fun hbody' => ?_
      refine (hasTyT_strengthenC hagree harg hcarg hΓ).elim fun harg' => ?_
      exact ⟨.beta _ A body arg B u hA' hbody' harg'⟩
  | _, _, _, _, .zeta _ A value body B u hA hv hb, hc, hΓ => by
      obtain ⟨he_l, _, _, hcA, hcv, hcb⟩ := hc
      simp only [constsBelow, Bool.and_eq_true] at he_l
      refine (hasTyT_strengthenC hagree hA hcA hΓ).elim fun hA' => ?_
      refine (hasTyT_strengthenC hagree hv hcv hΓ).elim fun hv' => ?_
      have hd : declConstsBelow k (.letBinding A value) = true := by
        simp only [declConstsBelow, Bool.and_eq_true]
        exact ⟨he_l.1.1, he_l.1.2⟩
      refine (hasTyT_strengthenC hagree hb hcb
        (ctxConstsBelow_cons_of hd hΓ)).elim fun hb' => ?_
      exact ⟨.zeta _ A value body B u hA' hv' hb'⟩
  | _, _, _, _, .zetaLocal _ _ _ _ hval hty hv, hc, hΓ => by
      obtain ⟨_, _, hcv⟩ := hc
      exact (hasTyT_strengthenC hagree hv hcv hΓ).elim fun hv' =>
        ⟨.zetaLocal _ _ _ _ hval hty hv'⟩
  | _, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb, hc, hΓ => by
      obtain ⟨he_l, _, _, hcb⟩ := hc
      have hr : r < k := by
        simp only [constsBelow, decide_eq_true_eq] at he_l; exact he_l
      refine (hasTyT_strengthenC hagree hb hcb hΓ).elim fun hbody' => ?_
      exact ⟨.delta _ r ls m b (hagree r hr ▸ hres) hbody htr hlen hwf hbody'⟩
  | _, _, _, _, .iota _ _ _ _ h hlhs hrhs, hc, hΓ => by
      obtain ⟨he_l, _, _, hcl, hcr⟩ := hc
      refine (hasTyT_strengthenC hagree hlhs hcl hΓ).elim fun hl' => ?_
      refine (hasTyT_strengthenC hagree hrhs hcr hΓ).elim fun hr' => ?_
      exact ⟨.iota _ _ _ _
        (derivedIota_of_agreeBelow hagree h he_l) hl' hr'⟩
  | _, _, _, _, .lit _ t exp T h hexp, hc, hΓ => by
      obtain ⟨_, _, hce⟩ := hc
      exact (hasTyT_strengthenC hagree hexp hce hΓ).elim fun hexp' =>
        ⟨.lit _ t exp T h hexp'⟩
  | _, _, _, _, .app _ f g a b A B h1 h2, hc, hΓ => by
      obtain ⟨_, _, _, hc1, hc2⟩ := hc
      refine (convT_strengthenC hagree h1 hc1 hΓ).elim fun h1' => ?_
      refine (convT_strengthenC hagree h2 hc2 hΓ).elim fun h2' => ?_
      exact ⟨.app _ f g a b A B h1' h2'⟩
  | _, _, _, _, .lam _ A A' b b' B u hA hb, hc, hΓ => by
      obtain ⟨he_l, _, _, hcA, hcb⟩ := hc
      simp only [constsBelow, Bool.and_eq_true] at he_l
      refine (convT_strengthenC hagree hA hcA hΓ).elim fun hA' => ?_
      refine (convT_strengthenC hagree hb hcb
        (ctxConstsBelow_cons_of he_l.1 hΓ)).elim fun hb' => ?_
      exact ⟨.lam _ A A' b b' B u hA' hb'⟩
  | _, _, _, _, .pi _ A A' B B' u v hA hB, hc, hΓ => by
      obtain ⟨he_l, _, hcA, hcB⟩ := hc
      simp only [constsBelow, Bool.and_eq_true] at he_l
      refine (convT_strengthenC hagree hA hcA hΓ).elim fun hA' => ?_
      refine (convT_strengthenC hagree hB hcB
        (ctxConstsBelow_cons_of he_l.1 hΓ)).elim fun hB' => ?_
      exact ⟨.pi _ A A' B B' u v hA' hB'⟩
  | _, _, _, _, .letE _ A A' v v' b b' B u hA hv hb, hc, hΓ => by
      obtain ⟨he_l, _, _, hcA, hcv, hcb⟩ := hc
      simp only [constsBelow, Bool.and_eq_true] at he_l
      refine (convT_strengthenC hagree hA hcA hΓ).elim fun hA' => ?_
      refine (convT_strengthenC hagree hv hcv hΓ).elim fun hv' => ?_
      have hd : declConstsBelow k (.letBinding A v) = true := by
        simp only [declConstsBelow, Bool.and_eq_true]
        exact ⟨he_l.1.1, he_l.1.2⟩
      refine (convT_strengthenC hagree hb hcb
        (ctxConstsBelow_cons_of hd hΓ)).elim fun hb' => ?_
      exact ⟨.letE _ A A' v v' b b' B u hA' hv' hb'⟩
  | _, _, _, _, .sorts _ _ _ h, _, _ => ⟨.sorts _ _ _ h⟩
  | _, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h, hc, _ => by
      obtain ⟨he_l, _⟩ := hc
      have hr : r < k := by
        simp only [constsBelow, decide_eq_true_eq] at he_l; exact he_l
      exact ⟨.consts _ r ls ls' m (hagree r hr ▸ hres) hlen hwf hwf' h⟩
  | _, _, _, _, .eta _ f A B h, hc, hΓ => by
      obtain ⟨_, _, _, hch⟩ := hc
      exact (hasTyT_strengthenC hagree h hch hΓ).elim fun h' =>
        ⟨.eta _ f A B h'⟩
  | _, _, _, _, .irr _ P p q hP hp hq, hc, hΓ => by
      obtain ⟨_, _, _, hcP, hcp, hcq⟩ := hc
      refine (hasTyT_strengthenC hagree hP hcP hΓ).elim fun hP' => ?_
      refine (hasTyT_strengthenC hagree hp hcp hΓ).elim fun hp' => ?_
      refine (hasTyT_strengthenC hagree hq hcq hΓ).elim fun hq' => ?_
      exact ⟨.irr _ P p q hP' hp' hq'⟩
  | _, _, _, _, .tyConv _ a b A A' u h hA, hc, hΓ => by
      obtain ⟨_, _, _, hch, hcA⟩ := hc
      refine (convT_strengthenC hagree h hch hΓ).elim fun h' => ?_
      refine (convT_strengthenC hagree hA hcA hΓ).elim fun hA' => ?_
      exact ⟨.tyConv _ a b A A' u h' hA'⟩

/-- `TyConvT` chains strengthen leg by leg along the same agreement on
    clean derivations. -/
def tyConvT_strengthenC {E E' : ResolvedEnv} {n k : Nat}
    (hagree : EnvAgreeBelow E' E k) :
    {Γ : LCtx} → {A B : Expr Nat} → (h : TyConvT E' n Γ A B) →
    cleanTyConvT k h → ctxConstsBelow k Γ = true →
    Nonempty (TyConvT E n Γ A B)
  | _, _, _, .refl _ _, _, _ => ⟨.refl _ _⟩
  | _, _, _, .of _ _ _ u h, hc, hΓ => by
      simp only [cleanTyConvT] at hc
      obtain ⟨_, _, hch⟩ := hc
      exact (convT_strengthenC hagree h hch hΓ).elim fun h' =>
        ⟨.of _ _ _ u h'⟩
  | _, _, _, .trans _ A B C h1 h2, hc, hΓ => by
      simp only [cleanTyConvT] at hc
      obtain ⟨_, _, hc1, hc2⟩ := hc
      refine (tyConvT_strengthenC hagree h1 hc1 hΓ).elim fun h1' => ?_
      refine (tyConvT_strengthenC hagree h2 hc2 hΓ).elim fun h2' => ?_
      exact ⟨.trans _ A B C h1' h2'⟩

end

/-! ## §7b member types name only earlier-or-equal members

`envWfT_typeConsts_le` is the type-side of `envWfT_bodyConsts_before`: a
member's stored type was typed before admission, so its constants rank at
or below the member's own — `≤`, not `<`, because the whole group ranks at
the one step and a constructor's stored type may name the family (05 §4's
ConstructorScope). Crossed to refs by `RankCoherentBelow`, it supplies the
member-type cleanliness `checkT`'s `.const` nodes need for `cleanDeriv`. -/

/-- each member a group chain adds is fresh in the chain's base env. -/
theorem groupMembersT_fresh_of_mem {S E l E'}
    (h : GroupMembersT S E l E') :
    ∀ {r m}, (r, m) ∈ l → E.members r = none := by
  induction h with
  | nil E => intro r m hm; cases hm
  | cons E r₀ m₀ rest E' hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
      intro r m hm
      rcases List.mem_cons.mp hm with hhead | htail
      · cases hhead; exact hfresh
      · have h' := ih htail
        have h'' : (if r = r₀ then some m₀ else E.members r) = none := h'
        by_cases hr : r = r₀
        · rw [if_pos hr] at h''
          exact Option.noConfusion h''
        · rw [if_neg hr] at h''
          exact h''

/-- the inherited case for types: a base member's type constants keep their
    base ranks — `envWfT_constsIn` makes them base members, and the step
    preserves base ranks. -/
theorem stepRank_le_of_base {E : ResolvedEnv} (hE : EnvWfT E)
    (ih : ∀ r m r', E.members r = some m → occursConst r' m.mtype = true →
      hE.rank r' ≤ hE.rank r)
    {r : Nat} {m : CheckedMember} {r' : Nat}
    (hm : E.members r = some m) (ho : occursConst r' m.mtype = true) :
    stepRank E hE.rank hE.depth r' ≤ stepRank E hE.rank hE.depth r := by
  obtain ⟨m', hm'⟩ :=
    member_of_occursConst m.mtype (envWfT_constsIn hE r m hm) ho
  rw [stepRank_of_mem hm', stepRank_of_mem hm]
  exact ih r m r' hm ho

/-- the new-singleton case for types: the stored type was typed in the
    base, so its constants are base members, ranked at most the base's
    depth; the new member is ranked one past it. -/
theorem stepRank_le_of_new {E : ResolvedEnv} (hE : EnvWfT E) {r₀ : Nat}
    (hfresh : E.members r₀ = none) {arity : Nat} {A : Expr Nat} {u : Level}
    (hA : HasTyT E arity [] A (.sort u)) {r' : Nat}
    (ho : occursConst r' A = true) :
    stepRank E hE.rank hE.depth r' ≤ stepRank E hE.rank hE.depth r₀ := by
  obtain ⟨m', hm'⟩ := member_of_occursConst A (hasTyT_constsIn hA) ho
  rw [stepRank_of_mem hm', stepRank_of_fresh hfresh]
  exact Nat.le_succ_of_le (hE.rank_le_depth r')

/-- S4's type-side rank bound: every constant a stored member type names
    ranks at or below the member's own. -/
theorem envWfT_typeConsts_le {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ (r : Nat) (m : CheckedMember) (r' : Nat), E.members r = some m →
      occursConst r' m.mtype = true → hW.rank r' ≤ hW.rank r := by
  induction hW with
  | empty => intro r m r' hm _; simp [emptyEnv] at hm
  | «axiom» E r₀ A u hE hfresh hA _ _ ih =>
      intro r m r' hm ho
      show stepRank E hE.rank hE.depth r' ≤ stepRank E hE.rank hE.depth r
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact stepRank_le_of_new hE hfresh hA ho
      · simp only [extendEnv, if_neg hr] at hm
        exact stepRank_le_of_base hE ih hm ho
  | definition E r₀ A v u hE hfresh hA _ _ _ _ _ ih =>
      intro r m r' hm ho
      show stepRank E hE.rank hE.depth r' ≤ stepRank E hE.rank hE.depth r
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact stepRank_le_of_new hE hfresh hA ho
      · simp only [extendEnv, if_neg hr] at hm
        exact stepRank_le_of_base hE ih hm ho
  | thm E r₀ A p hE hfresh hA _ _ _ _ _ ih =>
      intro r m r' hm ho
      show stepRank E hE.rank hE.depth r' ≤ stepRank E hE.rank hE.depth r
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact stepRank_le_of_new hE hfresh hA ho
      · simp only [extendEnv, if_neg hr] at hm
        exact stepRank_le_of_base hE ih hm ho
  | «opaque» E r₀ A v u hE hfresh hA _ _ _ _ _ ih =>
      intro r m r' hm ho
      show stepRank E hE.rank hE.depth r' ≤ stepRank E hE.rank hE.depth r
      by_cases hr : r = r₀
      · subst hr
        simp only [extendEnv, if_pos rfl] at hm
        cases hm
        exact stepRank_le_of_new hE hfresh hA ho
      · simp only [extendEnv, if_neg hr] at hm
        exact stepRank_le_of_base hE ih hm ho
  | group E f fm ctors rr rm E' hE _ _ _ hmem ih =>
      intro r m r' hm ho
      show stepRank E hE.rank hE.depth r' ≤ stepRank E hE.rank hE.depth r
      rcases groupMembersT_mem_cases hmem hm with hin | hmE
      · rw [stepRank_of_fresh (groupMembersT_fresh_of_mem hmem hin)]
        exact stepRank_le hE.rank_le_depth r'
      · exact stepRank_le_of_base hE ih hmE ho

/-- S4-const: a below-`k` member's stored type is below `k` under rank
    coherence — `envWfT_typeConsts_le` bounds its constants' ranks by the
    member's own, and coherence lifts any ≥ `k` constant above that. -/
theorem envWfT_mtype_constsBelow {E' : ResolvedEnv} (hW : EnvWfT E')
    {k : Nat} (hcoh : RankCoherentBelow hW k) {r : Nat} {m : CheckedMember}
    (hm : E'.members r = some m) (hr : r < k) :
    constsBelow k m.mtype = true := by
  apply constsBelow_of_forall
  intro r' ho
  rcases Nat.lt_or_ge r' k with hlt | hge
  · exact hlt
  · obtain ⟨m', hm'⟩ :=
      member_of_occursConst m.mtype (envWfT_constsIn hW r m hm) ho
    have hrr := envWfT_typeConsts_le hW r m r' hm ho
    exact absurd (hcoh r' r ⟨m', hm'⟩ hge ⟨m, hm⟩ hr) (Nat.not_lt_of_le hrr)

/-! ## §7c `checkT` produces clean derivations

The syntactic checker's derivations are `cleanDeriv`s when the subject and
context are clean and the environment's member types are — `checkConstT`'s
`.const` nodes carry `instantiateLevels ls m.mtype`, clean by
`envWfT_mtype_constsBelow` (the member resolves below `k` off the subject),
and `checkLitT`'s numeral spine names the hardcoded refs `1`/`2`, clean
under `2 < k`. -/

/-- a `checkConstT` hit is node-clean at `k`: the ref resolves below `k`,
    and the member's stored type is below `k` by
    `envWfT_mtype_constsBelow` (`instantiateLevels` preserves the bound). -/
theorem cleanHasTyT_of_checkConstT {E : ResolvedEnv} (hW : EnvWfT E)
    {n k : Nat} (hcoh : RankCoherentBelow hW k) {Γ : LCtx} {r : Nat}
    {ls : List Level} (hr : r < k) {p : Σ T, HasTyT E n Γ (.const r ls) T}
    (hck : checkConstT E n Γ r ls = some p) :
    cleanHasTyT k p.2 := by
  unfold checkConstT at hck
  split at hck
  · rename_i m hm
    split at hck
    · rename_i hlen
      split at hck
      · rename_i hwf
        cases hck
        exact ⟨decide_eq_true hr, by
          rw [constsBelow_instantiateLevels]
          exact envWfT_mtype_constsBelow hW hcoh hm hr⟩
      · cases hck
    · cases hck
  · cases hck

/-- `checkLitT`'s derivation is node-clean at `k`: the numeral spine names
    only `1` and `2`, and every `.const` node's member type resolves below
    `k`. -/
theorem cleanHasTyT_of_checkLitT {E : ResolvedEnv} (hW : EnvWfT E)
    {n k : Nat} (hcoh : RankCoherentBelow hW k) (h1 : 1 < k) (h2 : 2 < k) :
    {Γ : LCtx} → {t : Nat} → (p : Σ T, HasTyT E n Γ (natExpand t) T) →
    checkLitT E n Γ t = some p → ctxConstsBelow k Γ = true →
    cleanHasTyT k p.2 := by
  intro Γ t
  induction t generalizing Γ with
  | zero =>
      intro p hck hΓ
      exact cleanHasTyT_of_checkConstT hW hcoh h1 hck
  | succ t ih =>
      intro p hck hΓ
      unfold checkLitT at hck
      cases hf : checkConstT E n Γ 2 [] with
      | none => rw [hf] at hck; cases hck
      | some df' =>
          obtain ⟨Tf, df⟩ := df'
          cases Tf with
          | pi A B =>
              cases ht : checkLitT E n Γ t with
              | none => rw [hf, ht] at hck; cases hck
              | some da' =>
                  obtain ⟨Ta, da⟩ := da'
                  rw [hf, ht] at hck
                  dsimp only at hck
                  by_cases heq : Ta = A
                  · rw [dif_pos heq] at hck
                    cases hck
                    subst Ta
                    have hcdf := cleanHasTyT_of_checkConstT hW hcoh h2 hf
                    have hcda := ih ⟨A, da⟩ ht hΓ
                    obtain ⟨hnat, _⟩ := cleanHasTyT_node hcda
                    obtain ⟨_, hpic⟩ := cleanHasTyT_node hcdf
                    simp only [constsBelow, Bool.and_eq_true] at hpic
                    refine ⟨?_, constsBelow_instantiate _ 0 _ hpic.2 hnat,
                      hcdf, hcda⟩
                    simp only [constsBelow, Bool.and_eq_true]
                    exact ⟨decide_eq_true h2, hnat⟩
                  · rw [dif_neg heq] at hck
                    cases hck
          | _ => rw [hf] at hck; cases hck

/-- `checkT`'s derivation is node-clean at `k`: every node it builds names
    either a subject subterm, a context hit, or a below-`k` member's stored
    type. -/
theorem cleanHasTyT_of_checkT {E : ResolvedEnv} (hW : EnvWfT E)
    {n k : Nat} (hcoh : RankCoherentBelow hW k) (h1 : 1 < k) (h2 : 2 < k) :
    {Γ : LCtx} → {e : Expr Nat} → (p : Σ T, HasTyT E n Γ e T) →
    checkT E n Γ e = some p →
    constsBelow k e = true → ctxConstsBelow k Γ = true →
    cleanHasTyT k p.2 := by
  intro Γ e
  induction e generalizing Γ with
  | sort l =>
      intro p hck _ _
      cases hck
      trivial
  | bvar i =>
      intro p hck _ hΓ
      unfold checkT at hck
      split at hck
      · rename_i A hlook
        cases hck
        exact ctxConstsBelow_lookupType hΓ hlook
      · cases hck
  | const r ls =>
      intro p hck he _
      unfold checkT at hck
      have hr : r < k := by
        simp only [constsBelow, decide_eq_true_eq] at he; exact he
      exact cleanHasTyT_of_checkConstT hW hcoh hr hck
  | app f a ihf iha =>
      intro p hck he hΓ
      have he' := he
      simp only [constsBelow, Bool.and_eq_true] at he
      unfold checkT at hck
      cases hf : checkT E n Γ f with
      | none => rw [hf] at hck; cases hck
      | some fp =>
          obtain ⟨Tf, df⟩ := fp
          cases Tf with
          | pi A B =>
              cases ha : checkT E n Γ a with
              | none => rw [hf, ha] at hck; cases hck
              | some ap =>
                  obtain ⟨Ta, da⟩ := ap
                  rw [hf, ha] at hck
                  dsimp only at hck
                  by_cases heq : Ta = A
                  · rw [dif_pos heq] at hck
                    cases hck
                    subst Ta
                    have hcdf := ihf ⟨.pi A B, df⟩ hf he.1 hΓ
                    have hcda := iha ⟨A, da⟩ ha he.2 hΓ
                    obtain ⟨_, hpi⟩ := cleanHasTyT_node hcdf
                    simp only [constsBelow, Bool.and_eq_true] at hpi
                    exact ⟨he',
                      constsBelow_instantiate _ 0 _ hpi.2 he.2, hcdf, hcda⟩
                  · rw [dif_neg heq] at hck
                    cases hck
          | _ => rw [hf] at hck; cases hck
  | lam A b ihA ihb =>
      intro p hck he hΓ
      have he' := he
      simp only [constsBelow, Bool.and_eq_true] at he
      unfold checkT at hck
      cases hA' : checkT E n Γ A with
      | none => rw [hA'] at hck; cases hck
      | some sA =>
          obtain ⟨TA, dA⟩ := sA
          cases TA with
          | sort u =>
              cases hb' : checkT E n (.assumption A :: Γ) b with
              | none => rw [hA', hb'] at hck; cases hck
              | some sb =>
                  obtain ⟨B, db⟩ := sb
                  rw [hA', hb'] at hck
                  cases hck
                  have hcdA := ihA ⟨.sort u, dA⟩ hA' he.1 hΓ
                  have hcdb := ihb ⟨B, db⟩ hb' he.2
                    (ctxConstsBelow_cons_of he.1 hΓ)
                  obtain ⟨_, hBc⟩ := cleanHasTyT_node hcdb
                  refine ⟨he', ?_, hcdA, hcdb⟩
                  simp only [constsBelow, Bool.and_eq_true]
                  exact ⟨he.1, hBc⟩
          | _ => rw [hA'] at hck; cases hck
  | pi A B ihA ihB =>
      intro p hck he hΓ
      have he' := he
      simp only [constsBelow, Bool.and_eq_true] at he
      unfold checkT at hck
      cases hA' : checkT E n Γ A with
      | none => rw [hA'] at hck; cases hck
      | some sA =>
          obtain ⟨TA, dA⟩ := sA
          cases TA with
          | sort u =>
              cases hB' : checkT E n (.assumption A :: Γ) B with
              | none => rw [hA', hB'] at hck; cases hck
              | some sB =>
                  obtain ⟨TB, dB⟩ := sB
                  cases TB with
                  | sort v =>
                      rw [hA', hB'] at hck
                      cases hck
                      exact ⟨he', ihA ⟨.sort u, dA⟩ hA' he.1 hΓ,
                        ihB ⟨.sort v, dB⟩ hB' he.2
                          (ctxConstsBelow_cons_of he.1 hΓ)⟩
                  | _ => rw [hA', hB'] at hck; cases hck
          | _ => rw [hA'] at hck; cases hck
  | letE A v b ihA ihv ihb =>
      intro p hck he hΓ
      have he' := he
      simp only [constsBelow, Bool.and_eq_true] at he
      unfold checkT at hck
      cases hA' : checkT E n Γ A with
      | none => rw [hA'] at hck; cases hck
      | some sA =>
          obtain ⟨TA, dA⟩ := sA
          cases TA with
          | sort u =>
              cases hv' : checkT E n Γ v with
              | none => rw [hA', hv'] at hck; cases hck
              | some sv =>
                  obtain ⟨Tv, dv⟩ := sv
                  cases hb' : checkT E n (.letBinding A v :: Γ) b with
                  | none => rw [hA', hv', hb'] at hck; cases hck
                  | some sb =>
                      obtain ⟨B, db⟩ := sb
                      rw [hA', hv', hb'] at hck
                      dsimp only at hck
                      by_cases heq : Tv = A
                      · rw [dif_pos heq] at hck
                        cases hck
                        subst Tv
                        have hcdA := ihA ⟨.sort u, dA⟩ hA' he.1.1 hΓ
                        have hcdv := ihv ⟨A, dv⟩ hv' he.1.2 hΓ
                        have hd : declConstsBelow k (.letBinding A v) = true := by
                          simp only [declConstsBelow, Bool.and_eq_true]
                          exact ⟨he.1.1, he.1.2⟩
                        have hcdb := ihb ⟨B, db⟩ hb' he.2
                          (ctxConstsBelow_cons_of hd hΓ)
                        obtain ⟨_, hBc⟩ := cleanHasTyT_node hcdb
                        exact ⟨he',
                          constsBelow_instantiate _ 0 _ hBc he.1.2,
                          hcdA, hcdv, hcdb⟩
                      · rw [dif_neg heq] at hck
                        cases hck
          | _ => rw [hA'] at hck; cases hck
  | lit t =>
      intro p hck he hΓ
      unfold checkT at hck
      cases hcl : checkLitT E n Γ t with
      | none => rw [hcl] at hck; cases hck
      | some p' =>
          rw [hcl] at hck
          cases hck
          have hcl' := cleanHasTyT_of_checkLitT hW hcoh h1 h2 _ hcl hΓ
          obtain ⟨_, hTc⟩ := cleanHasTyT_node hcl'
          exact ⟨he, hTc, hcl'⟩

/-- `synCheck`'s derivation is the checker's, so it is clean on the same
    hypotheses. -/
theorem cleanHasTyT_of_synCheck {E : ResolvedEnv} (hW : EnvWfT E)
    {n k : Nat} (hcoh : RankCoherentBelow hW k) (h1 : 1 < k) (h2 : 2 < k)
    {Γ : LCtx} {e T : Expr Nat} {d : HasTyT E n Γ e T}
    (hck : synCheck E n Γ e T = some d)
    (he : constsBelow k e = true) (hΓ : ctxConstsBelow k Γ = true) :
    cleanHasTyT k d := by
  unfold synCheck at hck
  cases hc : checkT E n Γ e with
  | none => rw [hc] at hck; cases hck
  | some s =>
      obtain ⟨T', d'⟩ := s
      rw [hc] at hck
      dsimp only at hck
      by_cases heq : T' = T
      · rw [dif_pos heq] at hck
        cases hck
        subst T'
        exact cleanHasTyT_of_checkT hW hcoh h1 h2 _ hc he hΓ
      · rw [dif_neg heq] at hck
        cases hck

/-! ## §8 S5 — the group corollary

A derivation the syntactic checker produced in a group-grown environment
transports to the base when the subject and context name no constant at or
past the family's ref. Three pieces feed `hasTyT_strengthenC`:

- `groupMembersT_agreeBelow`: the `GroupMembersT` chain only adds members at
  refs ≥ the cut, so `EnvAgreeBelow E' E f` — agreement is read off the
  chain itself, not a `groupEnvT` identity.
- `rankCoherentBelow_of_group`: `RankCoherentBelow` propagates through the
  group step — a member the chain adds is fresh in the base, so it ranks at
  the step's depth-plus-one above every member's base rank; a below-`k`
  member is never a chain member when every chain ref is ≥ `k` (the
  `GroupInScopeT.hlayout`/`ctorRef_gt` + `hrr` bound). The base's own
  coherence at the cut is the remaining premise: at a group allocated above
  its base's refs it is vacuous (`rankCoherentBelow_of_forall_lt`).
- `hasTyT_strengthen_group`: `checkT` makes the derivation clean
  (`cleanHasTyT_of_checkT`), the two lemmas above supply `hagree`/`hcoh`,
  and `hasTyT_strengthenC` transports the whole judgment — the inferred
  type rides along as the derivation's own conclusion.

`vecEnvU_strengthen_pin` exercises it at the Vec group: `Nat` checker-typed
in `vecEnvUT` replays in `natEnvU`. -/

/-- a `GroupMembersT` chain adding only members at refs ≥ `k` agrees with
    its base below `k`: each `cons` extends at a fresh ref the cut cannot
    see (`EnvAgreeBelow.extendEnv_left`). -/
theorem groupMembersT_agreeBelow {S E l E'} {k : Nat} :
    GroupMembersT S E l E' → (∀ c ∈ l, k ≤ c.1) → EnvAgreeBelow E' E k
  | .nil _, _ => EnvAgreeBelow.refl _ k
  | .cons _ r m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest, hbound =>
      EnvAgreeBelow.trans
        (groupMembersT_agreeBelow hrest
          (fun c hc => hbound c (List.mem_cons.mpr (Or.inr hc))))
        (EnvAgreeBelow.extendEnv_left (EnvAgreeBelow.refl _ k)
          (hbound (r, m) (List.mem_cons.mpr (Or.inl rfl))))

/-- coherence at `k` holds vacuously when every member's ref is below `k` —
    the group-allocated-above-base discipline at concrete environments. -/
theorem rankCoherentBelow_of_forall_lt {E : ResolvedEnv} (hW : EnvWfT E)
    {k : Nat} (h : ∀ r m, E.members r = some m → r < k) :
    RankCoherentBelow hW k :=
  fun r' _ ⟨m', hm'⟩ hge _ _ => absurd (h r' m' hm') (Nat.not_lt_of_ge hge)

/-- coherence propagates through a group step whose chain refs are all at
    or above the cut. A chain-added member is fresh in the base, so it
    ranks at the step (`hE.depth + 1`); a base member keeps its base rank.
    Every below-`k` member is a base member (chain refs are ≥ `k`), so the
    base's coherence at `k` is what remains — `RankCoherentBelow hE k`. -/
theorem rankCoherentBelow_of_group {E E' : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)} {rr : Nat}
    {rm : CheckedMember} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    {k : Nat} (hcoh : RankCoherentBelow hE k)
    (hrefs : ∀ c ∈ (f, fm) :: ctors ++ [(rr, rm)], k ≤ c.1) :
    RankCoherentBelow
      (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) k := by
  intro r' r ⟨m', hm'⟩ hge ⟨m, hm⟩ hlt
  show stepRank E hE.rank hE.depth r < stepRank E hE.rank hE.depth r'
  rcases groupMembersT_mem_cases hmem hm' with hmem' | hE'
  · rw [stepRank_of_fresh (groupMembersT_fresh_of_mem hmem hmem')]
    rcases groupMembersT_mem_cases hmem hm with hmem'' | hE''
    · exact absurd (hrefs (r, m) hmem'') (Nat.not_le_of_gt hlt)
    · rw [stepRank_of_mem hE'']
      exact Nat.lt_succ_of_le (hE.rank_le_depth r)
  · rw [stepRank_of_mem hE']
    rcases groupMembersT_mem_cases hmem hm with hmem'' | hE''
    · exact absurd (hrefs (r, m) hmem'') (Nat.not_le_of_gt hlt)
    · rw [stepRank_of_mem hE'']
      exact hcoh r' r ⟨m', hE'⟩ hge ⟨m, hE''⟩ hlt

/-- THE GROUP COROLLARY: a term the syntactic checker types in a
    group-grown environment, clean below the family's ref, replays in the
    base. `GroupInScopeT.hlayout` (through `ctorRef_gt`) and `hrr` pin the
    chain's refs at `f` and above, so the chain agrees with `E` below `f`
    and the group env is coherent at `f` off the base's own coherence.
    `checkT` makes the derivation clean; `hasTyT_strengthenC` then
    transports subject and inferred type together. The `1 < f`/`2 < f`
    bounds keep `checkLitT`'s hardcoded numeral refs below the cut. -/
theorem hasTyT_strengthen_group {E E' : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)} {rr : Nat}
    {rm : CheckedMember} (hE : EnvWfT E) (hcoh : RankCoherentBelow hE f)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (g : GroupInScopeT E f fm ctors rr rm)
    {n : Nat} {Γ : LCtx} {e : Expr Nat}
    (p : Σ T, HasTyT E' n Γ e T) (hck : checkT E' n Γ e = some p)
    (he : constsBelow f e = true) (hΓ : ctxConstsBelow f Γ = true)
    (h1 : 1 < f) (h2 : 2 < f) :
    Nonempty (HasTyT E n Γ e p.1) :=
  let hW' := EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem
  have hrefs : ∀ c ∈ (f, fm) :: ctors ++ [(rr, rm)], f ≤ c.1 := by
    intro c hc
    rcases List.mem_cons.mp hc with heq | htail
    · cases heq; exact Nat.le_refl f
    · rcases List.mem_append.mp htail with hct | hrr'
      · exact Nat.le_of_lt (g.ctorRef_gt hct)
      · cases List.mem_singleton.mp hrr'
        exact Nat.le_of_lt (by rw [g.hrr]; omega)
  hasTyT_strengthenC (groupMembersT_agreeBelow hmem hrefs) p.2
    (cleanHasTyT_of_checkT hW'
      (rankCoherentBelow_of_group hE hfam hctors hrec hmem hcoh hrefs)
      h1 h2 p hck he hΓ) hΓ

/-- PIN: the corollary at the Vec group. `Nat`'s family constant, typed by
    the checker in `vecEnvUT` (a group over `natEnvU` at `f = 4`), replays
    in `natEnvU` — `natEnvU`'s members sit at `0..3`, so its coherence at
    `4` is vacuous, and `vecInScopeT`'s layout pins every chain ref at `4`
    or above. -/
theorem vecEnvU_strengthen_pin :
    Nonempty (HasTyT natEnvU 0 [] (.const 0 []) (.sort (.succ .zero))) :=
  hasTyT_strengthen_group (f := 4) (fm := vecFamMember)
    (ctors := [(5, vecNilMember), (6, vecConsMember)]) (rr := 7)
    (rm := vecRecMemberU) natEnvUWfT
    (rankCoherentBelow_of_forall_lt natEnvUWfT fun r m h => by
      rcases natEnvU_mem h with ⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩ <;>
        omega)
    rfl
    (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl)
    rfl
    vecMembersU vecInScopeT _
    (Option.get_mem (o := checkT vecEnvUT 0 [] (.const 0 [])) rfl)
    rfl rfl (by decide) (by decide)

#print axioms Rcic.Declarative.groupMembersT_agreeBelow
#print axioms Rcic.Declarative.rankCoherentBelow_of_forall_lt
#print axioms Rcic.Declarative.rankCoherentBelow_of_group
#print axioms Rcic.Declarative.hasTyT_strengthen_group
#print axioms Rcic.Declarative.vecEnvU_strengthen_pin

#print axioms Rcic.Declarative.constsBelow_of_forall
#print axioms Rcic.Declarative.envWfT_body_constsBelow
#print axioms Rcic.Declarative.derivedIota_of_agreeBelow
#print axioms Rcic.Declarative.hasTyT_strengthen
#print axioms Rcic.Declarative.convT_strengthen
#print axioms Rcic.Declarative.tyConvT_strengthen
#print axioms Rcic.Declarative.cleanHasTyT
#print axioms Rcic.Declarative.cleanConvT
#print axioms Rcic.Declarative.cleanTyConvT
#print axioms Rcic.Declarative.cleanHasTyT_node
#print axioms Rcic.Declarative.cleanConvT_node
#print axioms Rcic.Declarative.cleanTyConvT_node
#print axioms Rcic.Declarative.hasTyT_strengthenC
#print axioms Rcic.Declarative.convT_strengthenC
#print axioms Rcic.Declarative.tyConvT_strengthenC
#print axioms Rcic.Declarative.groupMembersT_fresh_of_mem
#print axioms Rcic.Declarative.envWfT_typeConsts_le
#print axioms Rcic.Declarative.envWfT_mtype_constsBelow
#print axioms Rcic.Declarative.cleanHasTyT_of_checkConstT
#print axioms Rcic.Declarative.cleanHasTyT_of_checkLitT
#print axioms Rcic.Declarative.cleanHasTyT_of_checkT
#print axioms Rcic.Declarative.cleanHasTyT_of_synCheck

end Rcic.Declarative
