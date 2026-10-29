/-
RCIC 07 §3 — G1-S3: `EnvWfT` admission of the bound predicate environment.

`predEnvOf cd` (S2) is the contract's group as a `ResolvedEnv`; this module
admits it through `EnvWfT`: the `svCount + svpCount` flat `axiomM` members by
`.axiom` steps, the Nat block as ONE `.group` step at its shifted base
(`natBase cd`), and the six predicate members by `.axiom` steps.

The Nat port runs at a SYMBOLIC base `b` over a symbolic prefix env: the
`natEnvU` fixture's views/checks are rebuilt `(E, b, h)`-parameterized — every
environment read (`extendEnv`'s `if j = r`, `transparentBody`, `whnfFuel`,
`fieldAnalyze`, `constsMemberFuel`) is discharged by rewriting the `members`
scrutinee with the stage's membership lemma, then reducing the pure-data
computation.  (`Nat.decEq b (b+k)` does not reduce for symbolic `b`; every
membership proof goes through `if_pos rfl` / `if_neg (by omega)`.)

The final `EnvWfT (predEnvOf cd)` is transported along the pointwise members
equality between the admission chain and the list-lookup env (S2's per-block
lookup lemmas).  `closure_claim = 0`.
-/
import rcic.RcicPredEnvObj
import rcic.RcicTypedGroupPins

namespace Rcic.PredSig
open Rcic.Declarative Rcic.ScopeExact

/-! ## extendEnv membership helpers -/

theorem extendEnv_mem_self (E : ResolvedEnv) (r : Nat) (m : CheckedMember) :
    (extendEnv E r m).members r = some m :=
  if_pos rfl

theorem extendEnv_mem_ne (E : ResolvedEnv) {j r : Nat} (h : j ≠ r) (m : CheckedMember) :
    (extendEnv E r m).members j = E.members j :=
  if_neg h

/-! ## The axiom prefix env (SV block ++ SVP block, all `typeObjectMember`) -/

/-- The env after the first `n` flat axiom members — indices `0..n-1` all
`typeObjectMember` (the SV block, then the SVP block). -/
def axPrefixEnv (cd : ContractSigData) : Nat → ResolvedEnv
  | 0 => emptyEnv
  | n + 1 => extendEnv (axPrefixEnv cd n) n typeObjectMember

theorem axPrefixEnv_members (cd : ContractSigData) (n j : Nat) :
    (axPrefixEnv cd n).members j = if j < n then some typeObjectMember else none := by
  induction n generalizing j with
  | zero => simp [axPrefixEnv, emptyEnv]
  | succ n ih =>
      simp only [axPrefixEnv]
      by_cases hjn : j = n
      · subst hjn
        rw [extendEnv_mem_self]
        simp
      · rw [extendEnv_mem_ne _ hjn, ih]
        rcases Nat.lt_trichotomy j n with hlt | rfl | hgt
        · simp [hlt, Nat.lt_succ_of_lt hlt]
        · exact absurd rfl hjn
        · have hge : ¬ j < n := by omega
          have hge' : ¬ j < n + 1 := by omega
          simp [hge, hge']

/-- `EnvWfT` for the flat axiom prefix — `typeObjectMember` is `sort 1` at
arity 0, no body. -/
def axPrefixEnvWf (cd : ContractSigData) : ∀ n, EnvWfT (axPrefixEnv cd n)
  | 0 => .empty
  | n + 1 =>
      .axiom (axPrefixEnv cd n) n (.sort (.succ .zero)) (.succ (.succ .zero))
        (axPrefixEnvWf cd n)
        (by rw [axPrefixEnv_members]; simp)
        (.sort [] (.succ .zero)) (fun _ => rfl) rfl

/-- The prefix env the Nat group is admitted over. -/
abbrev envPre (cd : ContractSigData) : ResolvedEnv := axPrefixEnv cd (natBase cd)

theorem envPre_members (cd : ContractSigData) (j : Nat) :
    (envPre cd).members j = if j < natBase cd then some typeObjectMember else none :=
  axPrefixEnv_members cd _ j

theorem envPre_fresh (cd : ContractSigData) (j : Nat) (hj : ¬ j < natBase cd) :
    (envPre cd).members j = none := by
  rw [envPre_members]; exact if_neg hj

theorem envPre_below (cd : ContractSigData) (j : Nat) (hj : j < natBase cd) :
    (envPre cd).members j = some typeObjectMember := by
  rw [envPre_members]; exact if_pos hj

def envPreWf (cd : ContractSigData) : EnvWfT (envPre cd) := axPrefixEnvWf cd _

/-- No group-class member lives in the axiom prefix. -/
theorem envPre_noGroup {cd : ContractSigData} {c : Nat} {cm : CheckedMember}
    (h : (envPre cd).members c = some cm) :
    cm.mclass ≠ .inductiveM ∧ cm.mclass ≠ .constructorM ∧ cm.mclass ≠ .recursorM := by
  rw [envPre_members] at h
  split at h
  · rename_i hc
    have : cm = typeObjectMember := Option.some.inj h |>.symm
    subst this
    exact ⟨by decide, by decide, by decide⟩
  · cases h

/-! ## The Nat-group stage envs -/

/-- The group built so far, stage by stage.  `abbrev` so `extendEnv` rewrites
see through the names. -/
abbrev natE1 (cd : ContractSigData) : ResolvedEnv :=
  extendEnv (envPre cd) (natBase cd) natFamMember
abbrev natE2 (cd : ContractSigData) : ResolvedEnv :=
  extendEnv (natE1 cd) (natBase cd + 1) (natZeroMemberAt (natBase cd))
abbrev natE3 (cd : ContractSigData) : ResolvedEnv :=
  extendEnv (natE2 cd) (natBase cd + 2) (natSuccMemberAt (natBase cd))
abbrev natE4 (cd : ContractSigData) : ResolvedEnv :=
  extendEnv (natE3 cd) (natBase cd + 3) (natRecMemberAt (natBase cd))

theorem natE1_fam (cd : ContractSigData) :
    (natE1 cd).members (natBase cd) = some natFamMember :=
  extendEnv_mem_self _ _ _

theorem natE1_fresh1 (cd : ContractSigData) :
    (natE1 cd).members (natBase cd + 1) = none := by
  rw [extendEnv_mem_ne _ (by omega : natBase cd + 1 ≠ natBase cd)]
  exact envPre_fresh cd _ (by omega)

theorem natE2_fam (cd : ContractSigData) :
    (natE2 cd).members (natBase cd) = some natFamMember := by
  rw [extendEnv_mem_ne _ (by omega : natBase cd ≠ natBase cd + 1)]
  exact natE1_fam cd

theorem natE2_zero (cd : ContractSigData) :
    (natE2 cd).members (natBase cd + 1) = some (natZeroMemberAt (natBase cd)) :=
  extendEnv_mem_self _ _ _

theorem natE2_fresh2 (cd : ContractSigData) :
    (natE2 cd).members (natBase cd + 2) = none := by
  rw [extendEnv_mem_ne _ (by omega : natBase cd + 2 ≠ natBase cd + 1)]
  rw [extendEnv_mem_ne _ (by omega : natBase cd + 2 ≠ natBase cd)]
  exact envPre_fresh cd _ (by omega)

theorem natE3_fam (cd : ContractSigData) :
    (natE3 cd).members (natBase cd) = some natFamMember := by
  rw [extendEnv_mem_ne _ (by omega : natBase cd ≠ natBase cd + 2)]
  exact natE2_fam cd

theorem natE3_zero (cd : ContractSigData) :
    (natE3 cd).members (natBase cd + 1) = some (natZeroMemberAt (natBase cd)) := by
  rw [extendEnv_mem_ne _ (by omega : natBase cd + 1 ≠ natBase cd + 2)]
  exact natE2_zero cd

theorem natE3_succ (cd : ContractSigData) :
    (natE3 cd).members (natBase cd + 2) = some (natSuccMemberAt (natBase cd)) :=
  extendEnv_mem_self _ _ _

theorem natE3_fresh3 (cd : ContractSigData) :
    (natE3 cd).members (natBase cd + 3) = none := by
  rw [extendEnv_mem_ne _ (by omega : natBase cd + 3 ≠ natBase cd + 2)]
  rw [extendEnv_mem_ne _ (by omega : natBase cd + 3 ≠ natBase cd + 1)]
  rw [extendEnv_mem_ne _ (by omega : natBase cd + 3 ≠ natBase cd)]
  exact envPre_fresh cd _ (by omega)

theorem natE4_fam (cd : ContractSigData) :
    (natE4 cd).members (natBase cd) = some natFamMember := by
  rw [extendEnv_mem_ne _ (by omega : natBase cd ≠ natBase cd + 3)]
  exact natE3_fam cd

theorem natE4_zero (cd : ContractSigData) :
    (natE4 cd).members (natBase cd + 1) = some (natZeroMemberAt (natBase cd)) := by
  rw [extendEnv_mem_ne _ (by omega : natBase cd + 1 ≠ natBase cd + 3)]
  exact natE3_zero cd

theorem natE4_succ (cd : ContractSigData) :
    (natE4 cd).members (natBase cd + 2) = some (natSuccMemberAt (natBase cd)) := by
  rw [extendEnv_mem_ne _ (by omega : natBase cd + 2 ≠ natBase cd + 3)]
  exact natE3_succ cd

theorem natE4_rec (cd : ContractSigData) :
    (natE4 cd).members (natBase cd + 3) = some (natRecMemberAt (natBase cd)) :=
  extendEnv_mem_self _ _ _

/-! ## Stage-membership classifications -/

/-- `natE1` = envPre + the family: every member is either the family or a
prefix axiom. -/
theorem natE1_mem_class {cd : ContractSigData} {c : Nat} {cm : CheckedMember}
    (h : (natE1 cd).members c = some cm) :
    (c = natBase cd ∧ cm = natFamMember) ∨ (cm = typeObjectMember ∧ c < natBase cd) := by
  by_cases hc : c = natBase cd
  · subst hc
    rw [extendEnv_mem_self] at h
    exact Or.inl ⟨rfl, Option.some.inj h |>.symm⟩
  · right
    rw [extendEnv_mem_ne _ hc] at h
    rw [envPre_members] at h
    split at h
    · rename_i hlt
      exact ⟨Option.some.inj h |>.symm, hlt⟩
    · cases h

theorem natE2_mem_class {cd : ContractSigData} {c : Nat} {cm : CheckedMember}
    (h : (natE2 cd).members c = some cm) :
    (c = natBase cd ∧ cm = natFamMember) ∨
      (c = natBase cd + 1 ∧ cm = natZeroMemberAt (natBase cd)) ∨
      (cm = typeObjectMember ∧ c < natBase cd) := by
  by_cases hc : c = natBase cd + 1
  · subst hc
    rw [extendEnv_mem_self] at h
    exact Or.inr (Or.inl ⟨rfl, Option.some.inj h |>.symm⟩)
  · rw [extendEnv_mem_ne _ hc] at h
    rcases natE1_mem_class h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')

theorem natE3_mem_class {cd : ContractSigData} {c : Nat} {cm : CheckedMember}
    (h : (natE3 cd).members c = some cm) :
    (c = natBase cd ∧ cm = natFamMember) ∨
      (c = natBase cd + 1 ∧ cm = natZeroMemberAt (natBase cd)) ∨
      (c = natBase cd + 2 ∧ cm = natSuccMemberAt (natBase cd)) ∨
      (cm = typeObjectMember ∧ c < natBase cd) := by
  by_cases hc : c = natBase cd + 2
  · subst hc
    rw [extendEnv_mem_self] at h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, Option.some.inj h |>.symm⟩))
  · rw [extendEnv_mem_ne _ hc] at h
    rcases natE2_mem_class h with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr h'))

/-- `natE1`/`natE2`/`natE3` have no recursor-class member. -/
theorem natE1_noRec {cd : ContractSigData} {c : Nat} {cm : CheckedMember}
    (h : (natE1 cd).members c = some cm) : cm.mclass ≠ .recursorM := by
  rcases natE1_mem_class h with ⟨_, rfl⟩ | ⟨rfl, _⟩
  · intro hcc; cases hcc
  · intro hcc; cases hcc

theorem natE2_noRec {cd : ContractSigData} {c : Nat} {cm : CheckedMember}
    (h : (natE2 cd).members c = some cm) : cm.mclass ≠ .recursorM := by
  rcases natE2_mem_class h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩
  · intro hcc; cases hcc
  · intro hcc; cases hcc
  · intro hcc; cases hcc

theorem natE3_noRec {cd : ContractSigData} {c : Nat} {cm : CheckedMember}
    (h : (natE3 cd).members c = some cm) : cm.mclass ≠ .recursorM := by
  rcases natE3_mem_class h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩
  · intro hcc; cases hcc
  · intro hcc; cases hcc
  · intro hcc; cases hcc
  · intro hcc; cases hcc

/-- The only constructor of `natE2` is `zero` at `b+1`. -/
theorem natE2_ctor_of {cd : ContractSigData} {c : Nat} {cm : CheckedMember}
    (h : (natE2 cd).members c = some cm) (hc : cm.mclass = .constructorM) :
    c = natBase cd + 1 ∧ cm = natZeroMemberAt (natBase cd) := by
  rcases natE2_mem_class h with ⟨_, rfl⟩ | h' | ⟨rfl, _⟩
  · cases hc
  · exact ⟨h'.1, h'.2⟩
  · cases hc

/-- The only constructors of `natE3` are `zero`/`succ` at `b+1`/`b+2`. -/
theorem natE3_ctor_of {cd : ContractSigData} {c : Nat} {cm : CheckedMember}
    (h : (natE3 cd).members c = some cm) (hc : cm.mclass = .constructorM) :
    c = natBase cd + 1 ∨ c = natBase cd + 2 := by
  rcases natE3_mem_class h with ⟨_, rfl⟩ | ⟨h1, _⟩ | ⟨h2, _⟩ | ⟨rfl, _⟩
  · cases hc
  · exact Or.inl h1
  · exact Or.inr h2
  · cases hc

/-! ## The Nat family/constructor/recursor views at base `b` -/

/-- `natFamView` at family ref `b` (the fixture's is at `0`). -/
def natFamViewB (E : ResolvedEnv) (b : Nat) (h : E.members b = some natFamMember) :
    PolicyFamilyView E where
  ref := b
  member := natFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

/-- `natZeroView` at family ref `b`. -/
def natZeroViewB (E : ResolvedEnv) (b : Nat) (h : E.members b = some natFamMember) :
    PolicyConstructorView E (natFamViewB E b h) (natZeroMemberAt b) where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := .empty _ _
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

/-- `const b : Sort 1` in any env holding the family (the fixture's
`natSuccFieldTy`, at the shifted ref). -/
private def natConstTyB {n : Nat} (E : ResolvedEnv) {b : Nat}
    (h : E.members b = some natFamMember) (Γ : LCtx) :
    HasTy E n Γ (.const b []) (.sort (.succ .zero)) :=
  HasTy.const Γ b [] natFamMember h rfl (fun _ hx => nomatch hx)

/-- `natSuccView` at family ref `b`. -/
def natSuccViewB (E : ResolvedEnv) (b : Nat) (h : E.members b = some natFamMember) :
    PolicyConstructorView E (natFamViewB E b h) (natSuccMemberAt b) where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const b []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlen : ([] ++ [(.const b [] : Expr Nat)]).length = 1 := rfl
      have hlt : j.val < 1 := by simp [hlen]
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      rw [hj]
      exact natConstTyB E h _ }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

/-- `natZeroUniverse`: no fields. -/
private theorem natZeroUniverseB (E : ResolvedEnv) {b : Nat}
    (h : E.members b = some natFamMember) :
    FieldUniverseAdmitted (natZeroViewB E b h) :=
  fun j => j.elim0

/-- `natSuccUniverse` at base `b`. -/
private theorem natSuccUniverseB (E : ResolvedEnv) {b : Nat}
    (h : E.members b = some natFamMember) :
    FieldUniverseAdmitted (natSuccViewB E b h) := by
  intro j
  have hlen : (natSuccViewB E b h).fields.length = 1 := rfl
  have hlt : j.val < 1 := by simp [hlen]
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

/-- `natZeroFields`: no fields. -/
private theorem natZeroFieldsB (E : ResolvedEnv) {b : Nat}
    (h : E.members b = some natFamMember) :
    CtorFieldsPermitted (natZeroViewB E b h) :=
  fun j => j.elim0

/-- `natSuccFields` at base `b`: `succ`'s one field `const b []` analyzes to
`recursive` — the env lookups inside `fieldAnalyze` read the family member
through the hypothesis. -/
private theorem natSuccFieldsB (E : ResolvedEnv) {b : Nat}
    (h : E.members b = some natFamMember) :
    CtorFieldsPermitted (natSuccViewB E b h) := by
  intro j
  have hlen : (natSuccViewB E b h).fields.length = 1 := rfl
  have hlt : j.val < 1 := by simp [hlen]
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact ⟨.recursive 0, 4, [], by
    simp [fieldAnalyze, piTelescopeFuel, domainsContainFuel, properFamilyFuel,
      containsFamilyFuel, indicesCleanFuel, exactParamLocals, transparentBody,
      whnfFuel, appsSpine, familyIdx, natSuccViewB, natFamViewB, natFamMember,
      transparent, h]⟩

/-! ## Group-ordering side conditions at the stage envs -/

/-- `memberFamRef` of the shifted zero member: the telescope result is the bare
family constant. -/
theorem natZero_famRef (b : Nat) : memberFamRef (natZeroMemberAt b) = some b := rfl

theorem natSucc_famRef (b : Nat) : memberFamRef (natSuccMemberAt b) = some b := rfl

/-- The recursor's declared family is the head of its last (major) domain. -/
theorem natRec_famRef (b : Nat) : memberFamRef (natRecMemberAt b) = some b := rfl

/-- 05 §3 for `zero` at `b+1` over `natE1`: the family is `b`, and `natE1`
holds no recursor. -/
theorem natZeroBeforeB (cd : ContractSigData) :
    CtorBeforeRecursors (natE1 cd) (natZeroMemberAt (natBase cd)) :=
  ⟨natBase cd, rfl, fun _ _ hm hk _ => absurd hk (natE1_noRec hm)⟩

/-- 05 §3 for `succ` at `b+2` over `natE2`. -/
theorem natSuccBeforeB (cd : ContractSigData) :
    CtorBeforeRecursors (natE2 cd) (natSuccMemberAt (natBase cd)) :=
  ⟨natBase cd, rfl, fun _ _ hm hk _ => absurd hk (natE2_noRec hm)⟩

/-- Constructors for `b` strictly between `b` and `b+1` in `natE1`: none —
the interval is empty; and none exist in `natE1` at all. -/
theorem natZeroContigB (cd : ContractSigData) :
    CtorContiguous (natE1 cd) (natBase cd + 1) (natZeroMemberAt (natBase cd)) := by
  refine ⟨natBase cd, rfl, Nat.lt_succ_self _, ?_, ?_⟩
  · intro c h1 h2
    exact absurd h2 (by omega)
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rcases natE1_mem_class hm with ⟨_, rfl⟩ | ⟨rfl, _⟩
    · cases hc
    · cases hc

/-- In `natE2` the only ctor strictly between `b` and `b+2` is `zero` at `b+1`. -/
theorem natSuccContigB (cd : ContractSigData) :
    CtorContiguous (natE2 cd) (natBase cd + 2) (natSuccMemberAt (natBase cd)) := by
  refine ⟨natBase cd, rfl, by omega, ?_, ?_⟩
  · intro c h1 h2
    have hc : c = natBase cd + 1 := by omega
    subst hc
    exact ⟨natZeroMemberAt (natBase cd), natE2_zero cd, rfl, rfl⟩
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rcases natE2_mem_class hm with ⟨_, rfl⟩ | ⟨h1, _⟩ | ⟨rfl, _⟩
    · cases hc
    · exact ⟨by omega, by omega⟩
    · cases hc

/-- The family admission over `envPre`. -/
def natFamAdmittedB (cd : ContractSigData) :
    IndGroupAdmitted (envPre cd) (natBase cd) natFamMember :=
  .family (envPre_fresh cd _ (by omega)) (natFamViewB (natE1 cd) _ (natE1_fam cd))
    rfl rfl (Or.inr uniformType_succ_zero)

/-- `zero`'s admission over `natE1`. -/
def natZeroAdmittedB (cd : ContractSigData) :
    IndGroupAdmitted (natE1 cd) (natBase cd + 1) (natZeroMemberAt (natBase cd)) :=
  .constructor (natFamViewB (natE1 cd) _ (natE1_fam cd))
    (natZeroViewB (natE1 cd) _ (natE1_fam cd)) (natE1_fresh1 cd)
    (natZeroBeforeB cd) (natZeroContigB cd)
    (natZeroUniverseB _ _) (natZeroFieldsB _ _)

/-- `succ`'s admission over `natE2`. -/
def natSuccAdmittedB (cd : ContractSigData) :
    IndGroupAdmitted (natE2 cd) (natBase cd + 2) (natSuccMemberAt (natBase cd)) :=
  .constructor (natFamViewB (natE2 cd) _ (natE2_fam cd))
    (natSuccViewB (natE2 cd) _ (natE2_fam cd)) (natE2_fresh2 cd)
    (natSuccBeforeB cd) (natSuccContigB cd)
    (natSuccUniverseB _ _) (natSuccFieldsB _ _)

/-- 05 §3 census in `natE3`: family `b`'s constructors are exactly `b+1`, `b+2`. -/
theorem natCensusB (cd : ContractSigData) :
    CtorCensus (natE3 cd) (natBase cd) (natBase cd + 3) := by
  refine ⟨by omega, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hm, hc, _⟩
    rcases natE3_ctor_of hm hc with h1 | h2
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  · intro h
    have hc : c = natBase cd + 1 ∨ c = natBase cd + 2 := by omega
    rcases hc with rfl | rfl
    · exact ⟨natZeroMemberAt (natBase cd), natE3_zero cd, rfl, rfl⟩
    · exact ⟨natSuccMemberAt (natBase cd), natE3_succ cd, rfl, rfl⟩

/-- The minor types at the shifted base (the fixture's `natMinors`). -/
def natMinorsB (b : Nat) : List (Expr Nat) :=
  [ .app (.bvar 0) (.const (b + 1) [])
  , .pi (.const b [])
      (.pi (.app (.bvar 2) (.bvar 0))
        (.app (.bvar 3) (.app (.const (b + 2) []) (.bvar 1)))) ]

/-- The recursor's `RecursorEliminationAdmitted` evidence at `natE3`. -/
def natGroupAdmittedB (cd : ContractSigData) :
    RecursorEliminationAdmitted (natE3 cd) (natBase cd + 3)
      (natRecMemberAt (natBase cd)) where
  family := natFamViewB (natE3 cd) _ (natE3_fam cd)
  constructors := [natZeroMemberAt (natBase cd), natSuccMemberAt (natBase cd)]
  constructorViews
    | ⟨0, _⟩ => natZeroViewB (natE3 cd) _ (natE3_fam cd)
    | ⟨1, _⟩ => natSuccViewB (natE3 cd) _ (natE3_fam cd)
    | ⟨k + 2, hk⟩ => absurd hk (Nat.not_lt.mpr (Nat.le_add_left 2 k))
  constructorsPresent
    | ⟨0, _⟩ => natE3_zero cd
    | ⟨1, _⟩ => natE3_succ cd
    | ⟨k + 2, hk⟩ => absurd hk (Nat.not_lt.mpr (Nat.le_add_left 2 k))
  recursorRef := rfl
  minorTypes := natMinorsB (natBase cd)
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

/-- `MinorPremisesMatch` at the shifted base: the empty-field constructor
analyzes immediately; `succ`'s field is the symbolic-`fieldAnalyze` run of
`natSuccFieldsB`. -/
theorem natMinorMatchB (cd : ContractSigData) :
    MinorPremisesMatch (natGroupAdmittedB cd) := by
  intro i
  have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl
  have hlt : i.val < 2 := by simpa [hlen] using i.isLt
  have hc : i.val = 0 ∨ i.val = 1 := by omega
  rcases hc with hv | hv
  · have hi : i = ⟨0, by rw [hlen]; decide⟩ := Fin.ext hv
    rw [hi]
    exact ⟨[], 4, rfl, rfl⟩
  · have hi : i = ⟨1, by rw [hlen]; decide⟩ := Fin.ext hv
    rw [hi]
    refine ⟨[.recursive 0], 4, ?_, ?_⟩
    · simp only [fieldShapesFuel, natGroupAdmittedB, natSuccViewB, natFamViewB,
        natFamMember, List.length_nil]
      rw [show fieldAnalyze (natE3 cd) 4 (natBase cd) 0 0 0 (0 + 0)
            (.const (natBase cd) []) =
            .permitted (.recursive 0) [] from ?_]
      · rfl
      · simp [fieldAnalyze, piTelescopeFuel, domainsContainFuel,
          properFamilyFuel, containsFamilyFuel, indicesCleanFuel,
          exactParamLocals, transparentBody, whnfFuel, appsSpine, familyIdx,
          natFamMember, transparent, natE3_fam]
    · simp [derivedMinor, minorFromTelescope, funIHType, piTelescopeFuel,
        whnfFuel, transparentBody, appsSpine, familyIdx, ctorFieldTelescope,
        policyFamilyLevels, policyParameterLocals, policyPi, lift, foldApps,
        instPrefix, policyLocals, natGroupAdmittedB, natSuccViewB, natFamViewB,
        natFamMember, transparent, natE3_fam, natMinorsB]

/-! ## The iota equations at base `b` (the fixture's `nat*IotaTy` port) -/

section IotaB

def natPB (b : Nat) : Expr Nat := .pi (.const b []) (.sort (.param 0))
def natMzB (b : Nat) : Expr Nat := .app (.bvar 0) (.const (b + 1) [])
def natMsB (b : Nat) : Expr Nat :=
  .pi (.const b [])
    (.pi (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const (b + 2) []) (.bvar 1))))
def natNB (b : Nat) : Expr Nat := .const b []

def natZeroCtxB (b : Nat) : LCtx :=
  [.assumption (natMsB b), .assumption (natMzB b), .assumption (natPB b)]
def natSuccCtxB (b : Nat) : LCtx :=
  [.assumption (natNB b), .assumption (natMsB b), .assumption (natMzB b),
    .assumption (natPB b)]

def natRecHeadB (b : Nat) : Expr Nat := .const (b + 3) [.param 0]
def natRecAppliedB (b : Nat) : Expr Nat :=
  foldApps (natRecHeadB b) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]
def natSuccRhsB (b : Nat) : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) (natRecAppliedB b)
def natSuccLhsB (b : Nat) : Expr Nat :=
  .app (.bvar 3) (.app (.const (b + 2) []) (.bvar 0))
def natZeroLhsB (b : Nat) : Expr Nat := .app (.bvar 2) (.const (b + 1) [])

def natRecConstTyB (cd : ContractSigData) :
    HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd)) (natRecHeadB (natBase cd))
      (natRecTypeAt (natBase cd)) :=
  HasTy.const _ (natBase cd + 3) [.param 0] (natRecMemberAt (natBase cd))
    (natE4_rec cd) rfl
    (by
      intro l hl
      have hl' : l = .param 0 := by simpa using hl
      subst hl'
      exact ⟨0, Or.inl rfl⟩)

private def natAppB {cd : ContractSigData} {f a A B : Expr Nat} {Γ : LCtx}
    (hf : HasTy (natE4 cd) 1 Γ f (.pi A B)) (ha : HasTy (natE4 cd) 1 Γ a A) :
    HasTy (natE4 cd) 1 Γ (.app f a) (instantiate0 a B) :=
  HasTy.app Γ f a A B hf ha

def natCodPB (b : Nat) : Expr Nat :=
  .pi (natMzB b) (.pi (natMsB b) (.pi (natNB b) (.app (.bvar 3) (.bvar 0))))
def natMzAtB (b : Nat) : Expr Nat := .app (.bvar 3) (.const (b + 1) [])
def natCodZB (b : Nat) : Expr Nat :=
  .pi (.pi (natNB b)
        (.pi (.app (.bvar 5) (.bvar 0))
          (.app (.bvar 6) (.app (.const (b + 2) []) (.bvar 1)))))
    (.pi (natNB b) (.app (.bvar 6) (.bvar 0)))
def natMsAtB (b : Nat) : Expr Nat :=
  .pi (natNB b)
    (.pi (.app (.bvar 4) (.bvar 0))
      (.app (.bvar 5) (.app (.const (b + 2) []) (.bvar 1))))
def natCodSB (b : Nat) : Expr Nat := .pi (natNB b) (.app (.bvar 5) (.bvar 0))
def natCodNB (_b : Nat) : Expr Nat := .app (.bvar 4) (.bvar 0)
def natPnB (_b : Nat) : Expr Nat := .app (.bvar 3) (.bvar 0)
def natSnDomB (b : Nat) : Expr Nat := natPnB b
def natSnCodB (b : Nat) : Expr Nat :=
  .app (.bvar 4) (.app (.const (b + 2) []) (.bvar 1))

def natSuccIotaTyB (cd : ContractSigData) :
    HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd)) (natSuccRhsB (natBase cd))
      (natSuccLhsB (natBase cd)) := by
  have hP : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd)) (.bvar 3)
      (natPB (natBase cd)) := HasTy.bvar _ 3 _ rfl
  have hZ : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd)) (.bvar 2)
      (natMzAtB (natBase cd)) := HasTy.bvar _ 2 _ rfl
  have hS : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd)) (.bvar 1)
      (natMsAtB (natBase cd)) := HasTy.bvar _ 1 _ rfl
  have hN : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd)) (.bvar 0)
      (natNB (natBase cd)) := HasTy.bvar _ 0 _ rfl
  have h0 : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (natRecHeadB (natBase cd)) (.pi (natPB (natBase cd)) (natCodPB (natBase cd))) :=
    natRecConstTyB cd
  have h1 := natAppB h0 hP
  have h1' : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (.app (natRecHeadB (natBase cd)) (.bvar 3))
      (.pi (natMzAtB (natBase cd)) (natCodZB (natBase cd))) := h1
  have h2 := natAppB h1' hZ
  have h2' : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (.app (.app (natRecHeadB (natBase cd)) (.bvar 3)) (.bvar 2))
      (.pi (natMsAtB (natBase cd)) (natCodSB (natBase cd))) := h2
  have h3 := natAppB h2' hS
  have h3' : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (.app (.app (.app (natRecHeadB (natBase cd)) (.bvar 3)) (.bvar 2)) (.bvar 1))
      (.pi (natNB (natBase cd)) (natCodNB (natBase cd))) := h3
  have h4 := natAppB h3' hN
  have h4' : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (natRecAppliedB (natBase cd)) (natPnB (natBase cd)) := h4
  have hSn := natAppB hS hN
  have hSn' : HasTy (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (.app (.bvar 1) (.bvar 0))
      (.pi (natSnDomB (natBase cd)) (natSnCodB (natBase cd))) := hSn
  exact natAppB hSn' h4'

def natZeroIotaTyB (cd : ContractSigData) :
    HasTy (natE4 cd) 1 (natZeroCtxB (natBase cd)) (.bvar 1)
      (natZeroLhsB (natBase cd)) :=
  HasTy.bvar (natZeroCtxB (natBase cd)) 1 _ rfl

end IotaB

/-- The descriptor's field shapes at the shifted base. -/
def natShapesB : Fin (natGroupAdmittedB cd).constructors.length → List FieldShape
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => [.recursive 0]
  | ⟨k + 2, hk⟩ => absurd hk (by
      have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl
      rw [hlen] at hk; omega)

/-- `fieldShapesFuel` on `succ`'s field at `natE3` (the checked version of
`natSuccFieldsB`'s computation). -/
private theorem natE3_fieldShapes_succ (cd : ContractSigData) :
    fieldShapesFuel (natE3 cd) 4 (natBase cd) 0 0 0 0
      [.const (natBase cd) []] = some [.recursive 0] := by
  simp only [fieldShapesFuel]
  rw [show fieldAnalyze (natE3 cd) 4 (natBase cd) 0 0 0 0
        (.const (natBase cd) []) = .permitted (.recursive 0) [] from ?_]
  · rfl
  · simp [fieldAnalyze, piTelescopeFuel, domainsContainFuel, properFamilyFuel,
      containsFamilyFuel, indicesCleanFuel, exactParamLocals, transparentBody,
      whnfFuel, appsSpine, familyIdx, natFamMember, transparent, natE3_fam]

/-- The iota descriptor clause at `natE3` (admission evidence, `HasTy` lane). -/
def natIotaClauseB (cd : ContractSigData) :
    IotaDescriptorClause (natE3 cd) (natGroupAdmittedB cd) where
  signatureOnly := rfl
  shapesAt := natShapesB
  fuelAt := fun _ => 4
  analyzed := by
    intro i
    have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl
    have hlt : i.val < 2 := by simpa [hlen] using i.isLt
    have hc : i.val = 0 ∨ i.val = 1 := by omega
    rcases hc with hv | hv
    · have hi : i = ⟨0, by rw [hlen]; decide⟩ := Fin.ext hv
      rw [hi]
      rfl
    · have hi : i = ⟨1, by rw [hlen]; decide⟩ := Fin.ext hv
      rw [hi]
      exact natE3_fieldShapes_succ cd
  typed := fun i =>
    if h0 : i.val = 0 then by
      have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl
      have hi : i = ⟨0, by rw [hlen]; decide⟩ := Fin.ext h0
      subst hi
      simp only [natShapesB, IotaEquationTyped]
      rw [show equationDoms (natGroupAdmittedB cd) ⟨0, _⟩ = some _ from rfl]
      rw [show iotaSchemaAt (natGroupAdmittedB cd) ⟨0, _⟩ 4 [] =
          some (.bvar 1) from ?_]
      · exact natZeroIotaTyB cd
      · simp [iotaSchemaAt, iotaOpenRhs, iotaArgs, preMajorBvars, fieldBvars,
          ctorFieldTelescope, lift, policyPi, policyFamilyLevels,
          policyParameterLocals, policyLocals, foldApps, natGroupAdmittedB,
          natZeroViewB, natFamViewB, natFamMember, policyRecursorLevels,
          policyRecursorArity, canonRecLevels]
    else if h1 : i.val = 1 then by
      have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl
      have hi : i = ⟨1, by rw [hlen]; decide⟩ := Fin.ext h1
      subst hi
      simp only [natShapesB, IotaEquationTyped]
      rw [show equationDoms (natGroupAdmittedB cd) ⟨1, _⟩ = some _ from rfl]
      rw [show iotaSchemaAt (natGroupAdmittedB cd) ⟨1, _⟩ 4 [.recursive 0] =
          some (natSuccRhsB (natBase cd)) from ?_]
      · exact natSuccIotaTyB cd
      · simp [iotaSchemaAt, iotaOpenRhs, iotaArgs, preMajorBvars, fieldBvars,
          ctorFieldTelescope, lift, policyPi, policyFamilyLevels,
          policyParameterLocals, policyLocals, piTelescopeFuel, whnfFuel,
          transparentBody, appsSpine, recCallField, recPrefix, foldApps,
          natGroupAdmittedB, natSuccViewB, natFamViewB, natFamMember,
          transparent, policyRecursorLevels, policyRecursorArity,
          canonRecLevels, natE3_fam, natSuccRhsB, natRecAppliedB,
          natRecHeadB, List.range_succ]
    else by
      have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl
      have hlt : i.val < 2 := by simpa [hlen] using i.isLt
      exact absurd hlt (by omega)

/-- The recursor's `IndGroupAdmitted` over `natE3`. -/
def natGroupRecursorB (cd : ContractSigData) :
    IndGroupAdmitted (natE3 cd) (natBase cd + 3) (natRecMemberAt (natBase cd)) :=
  .recursor (natGroupAdmittedB cd) (natE3_fresh3 cd) (natCensusB cd)
    (by
      intro i
      have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl
      have hlt : i.val < 2 := by simpa [hlen] using i.isLt
      have hc : i.val = 0 ∨ i.val = 1 := by omega
      rcases hc with hv | hv
      · have hi : i = ⟨0, by rw [hlen]; decide⟩ := Fin.ext hv
        rw [hi]
        exact natZeroUniverseB _ _
      · have hi : i = ⟨1, by rw [hlen]; decide⟩ := Fin.ext hv
        rw [hi]
        exact natSuccUniverseB _ _)
    (by
      intro i
      have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl
      have hlt : i.val < 2 := by simpa [hlen] using i.isLt
      have hc : i.val = 0 ∨ i.val = 1 := by omega
      rcases hc with hv | hv
      · have hi : i = ⟨0, by rw [hlen]; decide⟩ := Fin.ext hv
        rw [hi]
        exact natZeroFieldsB _ _
      · have hi : i = ⟨1, by rw [hlen]; decide⟩ := Fin.ext hv
        rw [hi]
        exact natSuccFieldsB _ _)
    (natMinorMatchB cd) (natIotaClauseB cd)

/-! ## The typed lane (`HasTyT`) at base `b` -/

/-- `const b : Sort 1` in the typed judgment, any env holding the family. -/
private def natConstTyTB {n : Nat} (E : ResolvedEnv) {b : Nat}
    (h : E.members b = some natFamMember) {Γ : LCtx} :
    HasTyT E n Γ (.const b []) (.sort (.succ .zero)) :=
  HasTyT.const Γ b [] natFamMember h rfl rfl

/-- The motive's type, `N → Sort u`, at the shifted base. -/
abbrev natMotTyB (b : Nat) : Expr Nat := .pi (.const b []) (.sort (.param 0))

/-- `P a : Sort u`, for the motive `P` at `bvar i` and `a : N`, at `natE3`. -/
def natMotAppTyTB {cd : ContractSigData} {Γ : LCtx} (i : Nat) (a : Expr Nat)
    (hP : lookupType Γ i = some (natMotTyB (natBase cd)))
    (ha : HasTyT (natE3 cd) 1 Γ a (.const (natBase cd) [])) :
    HasTyT (natE3 cd) 1 Γ (.app (.bvar i) a) (.sort (.param 0)) :=
  .app Γ (.bvar i) a (.const (natBase cd) []) (.sort (.param 0))
    (.bvar Γ i _ hP) ha

/-- the successor minor's type under the motive and `mz`, at base `b`. -/
abbrev natMsTyB (b : Nat) : Expr Nat :=
  .pi (.const b []) (.pi (.app (.bvar 2) (.bvar 0))
    (.app (.bvar 3) (.app (.const (b + 2) []) (.bvar 1))))

/-- the major and the body, `Π (t : N), P t`, at base `b`. -/
abbrev natMajorTyB (b : Nat) : Expr Nat :=
  .pi (.const b []) (.app (.bvar 3) (.bvar 0))

/-- `natMsTyT` at `natE3`. -/
def natMsTyTB (cd : ContractSigData) :
    HasTyT (natE3 cd) 1
      [.assumption (.app (.bvar 0) (.const (natBase cd + 1) [])),
       .assumption (natMotTyB (natBase cd))]
      (natMsTyB (natBase cd))
      (.sort (.imax (.succ .zero) (.imax (.param 0) (.param 0)))) :=
  .pi _ _ _ _ _ (natConstTyTB _ (natE3_fam cd))
    (.pi _ _ _ _ _ (natMotAppTyTB 2 (.bvar 0) rfl (.bvar _ 0 _ rfl))
      (natMotAppTyTB 3 _ rfl
        (.app _ (.const (natBase cd + 2) []) (.bvar 1)
          (.const (natBase cd) []) (.const (natBase cd) [])
          (.const _ (natBase cd + 2) [] (natSuccMemberAt (natBase cd))
            (natE3_succ cd) rfl rfl)
          (.bvar _ 1 _ rfl))))

/-- `natMajorTyT` at `natE3`. -/
def natMajorTyTB (cd : ContractSigData) :
    HasTyT (natE3 cd) 1
      [.assumption (natMsTyB (natBase cd)),
       .assumption (.app (.bvar 0) (.const (natBase cd + 1) [])),
       .assumption (natMotTyB (natBase cd))]
      (natMajorTyB (natBase cd)) (.sort (.imax (.succ .zero) (.param 0))) :=
  .pi _ _ _ _ _ (natConstTyTB _ (natE3_fam cd))
    (natMotAppTyTB 3 (.bvar 0) rfl (.bvar _ 0 _ rfl))

/-- `natRecTypeUTyT` at `natE3` — the recursor's stored type typed in the
DerivationScope env (family + constructors, recursor still fresh). -/
def natRecTypeUTyTB (cd : ContractSigData) :
    HasTyT (natE3 cd) 1 [] (natRecTypeAt (natBase cd)) (.sort natRecSortU) :=
  .pi _ _ _ _ _
    (.pi _ _ _ _ _ (natConstTyTB _ (natE3_fam cd)) (.sort _ (.param 0)))
    (.pi _ _ _ _ _
      (natMotAppTyTB 0 (.const (natBase cd + 1) []) rfl
        (.const _ (natBase cd + 1) [] (natZeroMemberAt (natBase cd))
          (natE3_zero cd) rfl rfl))
      (.pi _ _ _ _ _ (natMsTyTB cd) (natMajorTyTB cd)))

/-! ## `IndGroupTypedT` at the shifted base -/

/-- `natSuccFieldTyped` at `natE3`. -/
theorem natSuccFieldTypedTB (E : ResolvedEnv) {b : Nat}
    (h : E.members b = some natFamMember) :
    TelTypedT E 0 ([] ++ [.const b []]) (fun _ => .succ .zero)
  | ⟨0, _⟩ => ⟨natConstTyTB E h⟩
  | ⟨k + 1, hk⟩ => absurd hk (by simp)

theorem natFamTypedB (cd : ContractSigData) :
    IndGroupTypedT (natFamAdmittedB cd) := fun i => i.elim0

theorem natZeroTypedB (cd : ContractSigData) :
    IndGroupTypedT (natZeroAdmittedB cd) :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem natSuccTypedB (cd : ContractSigData) :
    IndGroupTypedT (natSuccAdmittedB cd) :=
  ⟨fun i => i.elim0, ⟨natSuccFieldTypedTB _ (natE2_fam cd), fun i => i.elim0⟩⟩

/-- The typed iota equations at `natE4` (`HasTyT` ports of the `nat*IotaTyB`
derivations). -/
def natRecConstTyTB (cd : ContractSigData) :
    HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd)) (natRecHeadB (natBase cd))
      (natRecTypeAt (natBase cd)) :=
  HasTyT.const _ (natBase cd + 3) [.param 0] (natRecMemberAt (natBase cd))
    (natE4_rec cd) rfl rfl

private def natAppTB {cd : ContractSigData} {f a A B : Expr Nat} {Γ : LCtx}
    (hf : HasTyT (natE4 cd) 1 Γ f (.pi A B))
    (ha : HasTyT (natE4 cd) 1 Γ a A) :
    HasTyT (natE4 cd) 1 Γ (.app f a) (instantiate0 a B) :=
  HasTyT.app Γ f a A B hf ha

def natSuccIotaTyTB (cd : ContractSigData) :
    HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd)) (natSuccRhsB (natBase cd))
      (natSuccLhsB (natBase cd)) := by
  have hP : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd)) (.bvar 3)
      (natPB (natBase cd)) := HasTyT.bvar _ 3 _ rfl
  have hZ : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd)) (.bvar 2)
      (natMzAtB (natBase cd)) := HasTyT.bvar _ 2 _ rfl
  have hS : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd)) (.bvar 1)
      (natMsAtB (natBase cd)) := HasTyT.bvar _ 1 _ rfl
  have hN : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd)) (.bvar 0)
      (natNB (natBase cd)) := HasTyT.bvar _ 0 _ rfl
  have h0 : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (natRecHeadB (natBase cd)) (.pi (natPB (natBase cd)) (natCodPB (natBase cd))) :=
    natRecConstTyTB cd
  have h1 := natAppTB h0 hP
  have h1' : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (.app (natRecHeadB (natBase cd)) (.bvar 3))
      (.pi (natMzAtB (natBase cd)) (natCodZB (natBase cd))) := h1
  have h2 := natAppTB h1' hZ
  have h2' : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (.app (.app (natRecHeadB (natBase cd)) (.bvar 3)) (.bvar 2))
      (.pi (natMsAtB (natBase cd)) (natCodSB (natBase cd))) := h2
  have h3 := natAppTB h2' hS
  have h3' : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (.app (.app (.app (natRecHeadB (natBase cd)) (.bvar 3)) (.bvar 2)) (.bvar 1))
      (.pi (natNB (natBase cd)) (natCodNB (natBase cd))) := h3
  have h4 := natAppTB h3' hN
  have h4' : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (natRecAppliedB (natBase cd)) (natPnB (natBase cd)) := h4
  have hSn := natAppTB hS hN
  have hSn' : HasTyT (natE4 cd) 1 (natSuccCtxB (natBase cd))
      (.app (.bvar 1) (.bvar 0))
      (.pi (natSnDomB (natBase cd)) (natSnCodB (natBase cd))) := hSn
  exact natAppTB hSn' h4'

def natZeroIotaTyTB (cd : ContractSigData) :
    HasTyT (natE4 cd) 1 (natZeroCtxB (natBase cd)) (.bvar 1)
      (natZeroLhsB (natBase cd)) :=
  HasTyT.bvar (natZeroCtxB (natBase cd)) 1 _ rfl

theorem natRecTypedB (cd : ContractSigData) :
    IndGroupTypedT (natGroupRecursorB cd) := by
  refine ⟨fun i => i.elim0, fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ => ?_⟩
  · rcases i with _ | _ | k
    · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
    · exact ⟨natSuccFieldTypedTB _ (natE3_fam cd), fun i => i.elim0⟩
    · exact absurd hi (by have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl; omega)
  · rcases i with _ | _ | k
    · simp only [natIotaClauseB, natShapesB, IotaEquationTypedT]
      rw [show iotaSchemaAt (natGroupAdmittedB cd) ⟨0, _⟩ 4 [] =
          some (.bvar 1) from ?_]
      · exact ⟨natZeroIotaTyTB cd⟩
      · simp [iotaSchemaAt, iotaOpenRhs, iotaArgs, preMajorBvars, fieldBvars,
          ctorFieldTelescope, lift, liftFields, policyPi, policyFamilyLevels,
          policyParameterLocals, policyLocals, foldApps, natGroupAdmittedB,
          natZeroViewB, natFamViewB, natFamMember, policyRecursorLevels,
          policyRecursorArity, canonRecLevels]
    · simp only [natIotaClauseB, natShapesB, IotaEquationTypedT]
      rw [show iotaSchemaAt (natGroupAdmittedB cd) ⟨0 + 1, _⟩ 4 [.recursive 0] =
          some (natSuccRhsB (natBase cd)) from ?_]
      · exact ⟨natSuccIotaTyTB cd⟩
      · simp [iotaSchemaAt, iotaOpenRhs, iotaArgs, preMajorBvars, fieldBvars,
          ctorFieldTelescope, lift, liftFields, policyPi, policyFamilyLevels,
          policyParameterLocals, policyLocals, piTelescopeFuel, whnfFuel,
          transparentBody, appsSpine, recCallField, recPrefix, foldApps,
          natGroupAdmittedB, natSuccViewB, natFamViewB, natFamMember,
          transparent, policyRecursorLevels, policyRecursorArity,
          canonRecLevels, natE3_fam, natSuccRhsB, natRecAppliedB,
          natRecHeadB, List.range_succ]
    · exact absurd hi (by have hlen : (natGroupAdmittedB cd).constructors.length = 2 := rfl; omega)

/-! ## `GroupMembersT` and the group step -/

/-- `exprFamCanonical`/`groupArityCoherent` for the shifted members at their
stage envs — each check's `E.members` scrutinee rewrites through the stage's
membership lemma. -/
private theorem natZero_canon (cd : ContractSigData) :
    exprFamCanonical (natE1 cd) (natZeroMemberAt (natBase cd)).mtype = true := by
  simp [exprFamCanonical, constLevelsCanonical, natZeroMemberAt, natE1_fam,
    natFamMember]

private theorem natZero_arities (cd : ContractSigData) :
    groupArityCoherent (natE1 cd) (natZeroMemberAt (natBase cd)) = true := by
  simp [groupArityCoherent, memberFamRef, spineHeadRef, piResult, appsSpine,
    natZeroMemberAt, natE1_fam, natFamMember]

private theorem natSucc_canon (cd : ContractSigData) :
    exprFamCanonical (natE2 cd) (natSuccMemberAt (natBase cd)).mtype = true := by
  simp [exprFamCanonical, constLevelsCanonical, natSuccMemberAt, natE2_fam,
    natFamMember]

private theorem natSucc_arities (cd : ContractSigData) :
    groupArityCoherent (natE2 cd) (natSuccMemberAt (natBase cd)) = true := by
  simp [groupArityCoherent, memberFamRef, spineHeadRef, piResult, appsSpine,
    natSuccMemberAt, natE2_fam, natFamMember]

private theorem natRec_canon (cd : ContractSigData) :
    exprFamCanonical (natE3 cd) (natRecMemberAt (natBase cd)).mtype = true := by
  simp [exprFamCanonical, constLevelsCanonical, natRecMemberAt, natRecTypeAt,
    natE3_fam, natE3_zero, natE3_succ, natFamMember, natZeroMemberAt,
    natSuccMemberAt]

private theorem natRec_arities (cd : ContractSigData) :
    groupArityCoherent (natE3 cd) (natRecMemberAt (natBase cd)) = true := by
  simp [groupArityCoherent, memberFamRef, spineHeadRef, piResult, piLastDom,
    appsSpine, natRecMemberAt, natRecTypeAt, natE3_fam, natFamMember]

/-- `recIdxAdmittedTB` at the shifted base — the sufficient condition for
`RecursorGroupIdxAdmittedT.ofCheck`. -/
private theorem natRec_idxCheckB_A (cd : ContractSigData) :
    ((natE3 cd).members (natBase cd + 3)).isNone = true := by
  rw [natE3_fresh3]; rfl

private theorem natRec_idxCheckB_C (cd : ContractSigData) :
    exprClosedAt 0 (natRecMemberAt (natBase cd)).mtype = true := by
  simp [exprClosedAt, natRecMemberAt, natRecTypeAt, foldApps,
    natRecAppliedB, natRecHeadB]

private theorem natRec_idxCheckB_D0_1 (cd : ContractSigData) :
    exprClosedAt 0 ((natGroupAdmittedB cd).constructors[0]'(by simp [natGroupAdmittedB])).mtype
      = true := by
  simp only [exprClosedAt, natGroupAdmittedB, natZeroMemberAt]

private theorem natRec_idxCheckB_D0_2 (cd : ContractSigData) :
    iotaWitnessStableB (natE3 cd)
      ((natIotaClauseB cd).fuelAt ⟨0, by simp [natGroupAdmittedB]⟩)
      ((natGroupAdmittedB cd).constructorViews ⟨0, by simp [natGroupAdmittedB]⟩).fields
      (fieldBvars ((natGroupAdmittedB cd).constructorViews
        ⟨0, by simp [natGroupAdmittedB]⟩).fields.length)
      (lift 0 (1 + (natGroupAdmittedB cd).constructors.length +
        (natGroupAdmittedB cd).family.indices.length)
        (ctorFieldTelescope ((natGroupAdmittedB cd).constructorViews
          ⟨0, by simp [natGroupAdmittedB]⟩))) = true := by
  show iotaWitnessStableB (natE3 cd) 4 [] [] (.const (natBase cd) []) = true
  simp only [iotaWitnessStableB, List.all_nil, Bool.true_and, constsMemberFuel]
  rw [natE3_fam]
  rfl

private theorem natRec_idxCheckB_D0_3 (cd : ContractSigData) :
    iotaWitnessStableB (extendEnv (natE3 cd) (natBase cd + 3) (natRecMemberAt (natBase cd)))
      ((natIotaClauseB cd).fuelAt ⟨0, by simp [natGroupAdmittedB]⟩)
      ((natGroupAdmittedB cd).constructorViews ⟨0, by simp [natGroupAdmittedB]⟩).fields
      (fieldBvars ((natGroupAdmittedB cd).constructorViews
        ⟨0, by simp [natGroupAdmittedB]⟩).fields.length)
      (lift 0 (1 + (natGroupAdmittedB cd).constructors.length +
        (natGroupAdmittedB cd).family.indices.length)
        (ctorFieldTelescope ((natGroupAdmittedB cd).constructorViews
          ⟨0, by simp [natGroupAdmittedB]⟩))) = true := by
  show iotaWitnessStableB (natE4 cd) 4 [] [] (.const (natBase cd) []) = true
  simp only [iotaWitnessStableB, List.all_nil, Bool.true_and, constsMemberFuel]
  rw [natE4_fam]
  rfl

private theorem natRec_idxCheckB_D0_4 (cd : ContractSigData) :
    exprClosedAt ((natGroupAdmittedB cd).family.parameters.length + 1 +
        (natGroupAdmittedB cd).constructors.length +
        (natGroupAdmittedB cd).family.indices.length +
        ((natGroupAdmittedB cd).constructorViews
          ⟨0, by simp [natGroupAdmittedB]⟩).fields.length)
      (descriptorSchema (natGroupAdmittedB cd) (natIotaClauseB cd)
        ⟨0, by simp [natGroupAdmittedB]⟩) = true := by
  simp [descriptorSchema, iotaSchemaAt, iotaOpenRhs, iotaArgs,
    preMajorBvars, fieldBvars, ctorFieldTelescope, lift, policyPi,
    policyFamilyLevels, policyParameterLocals, policyLocals, foldApps,
    exprClosedAt, natGroupAdmittedB, natIotaClauseB, natShapesB,
    natZeroViewB, natFamViewB, natFamMember, natZeroMemberAt,
    policyRecursorLevels, policyRecursorArity, canonRecLevels, natE3_fam,
    List.range_succ]

private theorem natRec_idxCheckB_D0 (cd : ContractSigData) :
    recIdxCtorB (natGroupAdmittedB cd) (natIotaClauseB cd)
      ⟨0, by simp [natGroupAdmittedB]⟩ = true := by
  simp only [recIdxCtorB, Bool.and_eq_true]
  exact ⟨⟨⟨natRec_idxCheckB_D0_1 cd, natRec_idxCheckB_D0_2 cd⟩,
    natRec_idxCheckB_D0_3 cd⟩, natRec_idxCheckB_D0_4 cd⟩

private theorem natRec_idxCheckB_D1 (cd : ContractSigData) :
    recIdxCtorB (natGroupAdmittedB cd) (natIotaClauseB cd)
      ⟨1, by simp [natGroupAdmittedB]⟩ = true := by
  simp only [recIdxCtorB, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [exprClosedAt, natGroupAdmittedB, natSuccMemberAt, lift,
      natRecTypeAt, foldApps, natRecAppliedB, natRecHeadB]
    rfl
  · show iotaWitnessStableB (natE3 cd) 4 [.const (natBase cd) []] [.bvar 0]
        (.pi (.const (natBase cd) []) (.const (natBase cd) [])) = true
    simp only [iotaWitnessStableB, List.all_cons, List.all_nil, Bool.true_and,
      Bool.and_true, constsMemberFuel]
    rw [natE3_fam]
    rfl
  · show iotaWitnessStableB (natE4 cd) 4 [.const (natBase cd) []] [.bvar 0]
        (.pi (.const (natBase cd) []) (.const (natBase cd) [])) = true
    simp only [iotaWitnessStableB, List.all_cons, List.all_nil, Bool.true_and,
      Bool.and_true, constsMemberFuel]
    rw [natE4_fam]
    rfl
  · simp [descriptorSchema, iotaSchemaAt, iotaOpenRhs, iotaArgs,
      preMajorBvars, fieldBvars, ctorFieldTelescope, lift, liftFields,
      policyPi, policyFamilyLevels, policyParameterLocals, policyLocals,
      foldApps, exprClosedAt, instantiate0, instantiate, recCallField,
      recPrefix, familyIdx, natGroupAdmittedB, natIotaClauseB, natShapesB,
      natSuccViewB, natFamViewB, natFamMember, natSuccMemberAt,
      natRecMemberAt, natRecTypeAt, transparent, transparentBody, whnfFuel,
      piTelescopeFuel, appsSpine, policyRecursorLevels, policyRecursorArity,
      canonRecLevels, natE3_fam, natE3_zero, natE3_succ, natE3_fresh3,
      natSuccRhsB, natRecAppliedB, natRecHeadB, List.range_succ]

private theorem natRec_idxCheckB_D (cd : ContractSigData) :
    (List.range (natGroupAdmittedB cd).constructors.length).all (fun j =>
      if hj : j < (natGroupAdmittedB cd).constructors.length then
        recIdxCtorB (natGroupAdmittedB cd) (natIotaClauseB cd) ⟨j, hj⟩
      else false) = true := by
  show (List.range 2).all (fun j => if hj : j < 2 then
      recIdxCtorB (natGroupAdmittedB cd) (natIotaClauseB cd) ⟨j, hj⟩
      else false) = true
  simp only [show List.range 2 = [0, 1] from rfl,
    List.all_cons, List.all_nil, Bool.and_true]
  rw [dif_pos (by decide : (0:Nat) < 2), dif_pos (by decide : (1:Nat) < 2)]
  rw [Bool.and_eq_true]
  exact ⟨natRec_idxCheckB_D0 cd, natRec_idxCheckB_D1 cd⟩

private theorem natRec_idxCheckB (cd : ContractSigData) :
    recIdxAdmittedTB (natGroupAdmittedB cd) (natIotaClauseB cd) = true := by
  unfold recIdxAdmittedTB
  rw [natRec_idxCheckB_A, natRec_idxCheckB_C, natRec_idxCheckB_D]
  rfl

/-- The four-member `GroupMembersT` chain over `envPre`, ending at `natE4`. -/
def natMembersTB (cd : ContractSigData) :
    GroupMembersT (natE1 cd) (envPre cd)
      [(natBase cd, natFamMember),
       (natBase cd + 1, natZeroMemberAt (natBase cd)),
       (natBase cd + 2, natSuccMemberAt (natBase cd)),
       (natBase cd + 3, natRecMemberAt (natBase cd))] (natE4 cd) :=
  .cons _ (natBase cd) natFamMember _ _ (envPre_fresh cd _ (by omega)) rfl
    (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    (natFamAdmittedB cd) PUnit.unit _ (.sort [] (.succ .zero))
    (fun h => absurd h (by decide)) (natFamTypedB cd)
    (.cons _ (natBase cd + 1) (natZeroMemberAt (natBase cd)) _ _
      (natE1_fresh1 cd) rfl (fun _ => rfl)
      (fun h => absurd h (by simp [natZeroMemberAt])) rfl
      (natZero_canon cd) (natZero_arities cd)
      (natZeroAdmittedB cd) PUnit.unit _
      (natConstTyTB _ (natE1_fam cd))
      (fun _ => ⟨natConstTyTB _ (natE1_fam cd)⟩) (natZeroTypedB cd)
      (.cons _ (natBase cd + 2) (natSuccMemberAt (natBase cd)) _ _
        (natE2_fresh2 cd) rfl (fun _ => rfl)
        (fun h => absurd h (by simp [natSuccMemberAt])) rfl
        (natSucc_canon cd) (natSucc_arities cd)
        (natSuccAdmittedB cd) PUnit.unit _
        (.pi [] _ _ _ _ (natConstTyTB _ (natE2_fam cd))
          (natConstTyTB _ (natE2_fam cd)))
        (fun _ => ⟨.pi [] _ _ _ _ (natConstTyTB _ (natE1_fam cd))
          (natConstTyTB _ (natE1_fam cd))⟩) (natSuccTypedB cd)
        (.cons _ (natBase cd + 3) (natRecMemberAt (natBase cd)) _ _
          (natE3_fresh3 cd) rfl (fun _ => rfl)
          (fun h => absurd h (by simp [natRecMemberAt])) rfl
          (natRec_canon cd) (natRec_arities cd)
          (natGroupRecursorB cd)
          (.ofCheck (natGroupAdmittedB cd) (natIotaClauseB cd)
            (natRec_idxCheckB cd)) _
          (natRecTypeUTyTB cd)
          (fun h => absurd h (by simp [natRecMemberAt])) (natRecTypedB cd)
          (.nil _))))

/-- Nat as one `EnvWfT.group` step over the axiom prefix — the contract's
`natEnvU`-style inductive block at its canonical position. -/
def natGroupEnvWf (cd : ContractSigData) : EnvWfT (natE4 cd) :=
  .group (envPre cd) (natBase cd) natFamMember
    [(natBase cd + 1, natZeroMemberAt (natBase cd)),
     (natBase cd + 2, natSuccMemberAt (natBase cd))]
    (natBase cd + 3) (natRecMemberAt (natBase cd)) (natE4 cd)
    (envPreWf cd) rfl
    (fun c hc => by
      simp at hc
      rcases hc with rfl | rfl <;> rfl)
    rfl (natMembersTB cd)

/-! ## `listCanon` membership -/

/-- `listInsert` keeps the accumulator's members and adds the inserted key. -/
theorem mem_listInsert {x : String} (acc : List String) (r : String)
    (h : x ∈ acc ∨ x = r) : x ∈ listInsert acc r := by
  induction acc generalizing r with
  | nil =>
      simp only [listInsert]
      rcases h with h | h
      · cases h
      · subst h; exact List.mem_cons_self _ _
  | cons y ys ih =>
      simp only [listInsert]
      by_cases hyr : y = r
      · subst hyr
        rw [if_pos rfl]
        rcases h with h | rfl
        · exact h
        · exact List.mem_cons_self _ _
      · rw [if_neg hyr]
        by_cases hrlt : r < y
        · rw [if_pos hrlt]
          rcases h with h | rfl
          · exact List.mem_cons_of_mem _ h
          · exact List.mem_cons_self _ _
        · rw [if_neg hrlt]
          rcases h with h | rfl
          · rcases List.mem_cons.mp h with rfl | hys
            · exact List.mem_cons_self _ _
            · exact List.mem_cons_of_mem _ (ih _ (Or.inl hys))
          · exact List.mem_cons_of_mem _ (ih _ (Or.inr rfl))

/-- `listCanon` preserves membership. -/
theorem mem_listCanon {x : String} {xs : List String} (h : x ∈ xs) :
    x ∈ listCanon xs := by
  have hfold : ∀ (acc xs : List String), x ∈ acc ∨ x ∈ xs →
      x ∈ xs.foldl listInsert acc := by
    intro acc xs h
    induction xs generalizing acc with
    | nil =>
        rcases h with h | h
        · exact h
        · cases h
    | cons y ys ih =>
        simp only [List.foldl_cons]
        apply ih
        rcases h with h | h
        · exact Or.inl (mem_listInsert _ _ (Or.inl h))
        · rcases List.mem_cons.mp h with rfl | hys
          · exact Or.inl (mem_listInsert _ _ (Or.inr rfl))
          · exact Or.inr hys
  exact hfold [] xs (Or.inr h)

/-! ## Digest/residue index bounds -/

theorem tin_mem (cd : ContractSigData) : cd.tin ∈ cd.svDigests :=
  mem_listCanon (List.mem_cons_self _ _)

theorem tst_mem (cd : ContractSigData) : cd.tst ∈ cd.svDigests :=
  mem_listCanon (List.mem_cons_of_mem _ (List.mem_cons_self _ _))

theorem tout_mem (cd : ContractSigData) : cd.tout ∈ cd.svDigests :=
  mem_listCanon
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))

/-- `predBase` unfolds to `natBase + 4` — the Nat block's four members. -/
theorem predBase_eq (cd : ContractSigData) : predBase cd = natBase cd + 4 := rfl

theorem svIndexOf_lt_natBase (cd : ContractSigData) {d : String}
    (hd : d ∈ cd.svDigests) : svIndexOf cd d < natBase cd := by
  have hlt : (cd.svDigests).findIdx (· == d) < (cd.svDigests).length :=
    List.findIdx_lt_length_of_exists ⟨d, hd, beq_self_eq_true d⟩
  simp only [svIndexOf, natBase, svpBase, svCount, svpCount]
  omega

theorem svpIndexOf_lt_natBase (cd : ContractSigData) {r : String}
    (hr : r ∈ cd.resIds) : svpIndexOf cd r < natBase cd := by
  have hlt : (cd.resIds).findIdx (· == r) < (cd.resIds).length :=
    List.findIdx_lt_length_of_exists ⟨r, hr, beq_self_eq_true r⟩
  simp only [svpIndexOf, natBase, svpBase, svCount, svpCount]
  omega

/-- `natE4`'s members below `natBase` pass through to the axiom prefix
(every index there is `typeObjectMember`). -/
theorem natE4_low (cd : ContractSigData) {j : Nat}
    (hj : j < natBase cd) : (natE4 cd).members j = some typeObjectMember := by
  rw [extendEnv_mem_ne _ (by omega : j ≠ natBase cd + 3),
      extendEnv_mem_ne _ (by omega : j ≠ natBase cd + 2),
      extendEnv_mem_ne _ (by omega : j ≠ natBase cd + 1),
      extendEnv_mem_ne _ (by omega : j ≠ natBase cd)]
  exact envPre_below cd j hj

/-- `natE4`'s members at or past `predBase` are `none`. -/
theorem natE4_fresh_ge (cd : ContractSigData) {j : Nat}
    (hj : natBase cd + 4 ≤ j) : (natE4 cd).members j = none := by
  rw [extendEnv_mem_ne _ (by omega : j ≠ natBase cd + 3),
      extendEnv_mem_ne _ (by omega : j ≠ natBase cd + 2),
      extendEnv_mem_ne _ (by omega : j ≠ natBase cd + 1),
      extendEnv_mem_ne _ (by omega : j ≠ natBase cd)]
  exact envPre_fresh cd _ (by omega)

/-! ## The predicate-axiom chain env -/

/-- The env after the predicate members in `l` have been pushed at indices
`i, i+1, …` — `l`'s head lands at `i`, so the fold recurses inward. -/
def predChainAt (cd : ContractSigData) : Nat → List PredSlot → ResolvedEnv
  | _, [] => natE4 cd
  | i, s :: ss => extendEnv (predChainAt cd (i + 1) ss) i (predMember cd s)

/-- Members below the chain window pass through to `natE4`. -/
theorem predChainAt_below (cd : ContractSigData) (l : List PredSlot) (i j : Nat)
    (hj : j < i) :
    (predChainAt cd i l).members j = (natE4 cd).members j := by
  induction l generalizing i with
  | nil => rfl
  | cons s ss ih =>
      simp only [predChainAt]
      rw [extendEnv_mem_ne _ (by omega : j ≠ i)]
      exact ih (i + 1) (by omega)

/-- Members at or past the chain window: index `i + k` holds `l[k]`'s member
when `k < l.length`, `natE4`'s (empty) member past the end. -/
theorem predChainAt_get (cd : ContractSigData) (l : List PredSlot) (i j : Nat)
    (hpi : predBase cd ≤ i) (hij : i ≤ j) :
    (predChainAt cd i l).members j = (l[j - i]?).map (predMember cd) := by
  induction l generalizing i with
  | nil =>
      simp only [predChainAt, List.getElem?_nil, Option.map_none]
      exact natE4_fresh_ge cd (j := j) (by
        rw [predBase_eq cd] at hpi; omega)
  | cons s ss ih =>
      simp only [predChainAt]
      by_cases h0 : j = i
      · subst h0
        rw [extendEnv_mem_self]
        simp
      · rw [extendEnv_mem_ne _ h0]
        have hjs : (s :: ss)[j - i]? = ss[j - (i + 1)]? := by
          have hjs' : j - i = (j - (i + 1)) + 1 := by omega
          rw [hjs']
          exact List.getElem?_cons_succ
        rw [hjs]
        exact ih (i + 1) (by omega) (by omega)

/-- The chain env sees every SV member — their indices sit below `natBase`. -/
theorem predChainAt_sv (cd : ContractSigData) (l : List PredSlot) (i : Nat)
    (hi : predBase cd ≤ i) {d : String} (hd : d ∈ cd.svDigests) :
    (predChainAt cd i l).members (svIndexOf cd d) = some typeObjectMember := by
  have hlt := svIndexOf_lt_natBase cd hd
  rw [predChainAt_below cd l i (svIndexOf cd d) (by
    have hpb := predBase_eq cd; omega)]
  exact natE4_low cd hlt

/-- The chain env sees every SVP member whose residue id is admitted. -/
theorem predChainAt_svp (cd : ContractSigData) (l : List PredSlot) (i : Nat)
    (hi : predBase cd ≤ i) {r : String} (hr : r ∈ cd.resIds) :
    (predChainAt cd i l).members (svpIndexOf cd r) = some typeObjectMember := by
  have hlt := svpIndexOf_lt_natBase cd hr
  rw [predChainAt_below cd l i (svpIndexOf cd r) (by
    have hpb := predBase_eq cd; omega)]
  exact natE4_low cd hlt

/-- The chain env sees the Nat family. -/
theorem predChainAt_fam (cd : ContractSigData) (l : List PredSlot) (i : Nat)
    (hi : predBase cd ≤ i) :
    (predChainAt cd i l).members (natBase cd) = some natFamMember := by
  rw [predChainAt_below cd l i (natBase cd) (by
    have hpb := predBase_eq cd; omega)]
  exact natE4_fam cd

/-! ## Predicate signature typing -/

/-- `const r : Sort 1` where `E` holds an SV/SVP type-object member. -/
private def svConstTy (E : ResolvedEnv) {r : Nat}
    (h : E.members r = some typeObjectMember) {Γ : LCtx} :
    HasTyT E 0 Γ (.const r []) (.sort (.succ .zero)) :=
  HasTyT.const Γ r [] typeObjectMember h rfl rfl

/-- `Prop : Sort 1` in any context. -/
private def propTy (E : ResolvedEnv) {Γ : LCtx} :
    HasTyT E 0 Γ propExpr (.sort (.succ .zero)) :=
  .sort Γ .zero

/-- Each signature `exprOfSig cd s` types at `Sort 1` in any env carrying the
SV/SVP members it names plus the Nat family (`bound`'s codomain).  The
`residuePost` arm needs its residue admitted (`validFor`). -/
def predSlotTy (cd : ContractSigData) {E : ResolvedEnv}
    (htin : E.members (svIndexOf cd cd.tin) = some typeObjectMember)
    (htst : E.members (svIndexOf cd cd.tst) = some typeObjectMember)
    (htout : E.members (svIndexOf cd cd.tout) = some typeObjectMember)
    (hnat : E.members (natBase cd) = some natFamMember)
    (hsvp : ∀ r : String, r ∈ cd.resIds →
      E.members (svpIndexOf cd r) = some typeObjectMember)
    (s : PredSlot) (hs : s.validFor cd) :
    Σ' u, HasTyT E 0 [] (exprOfSig cd s) (.sort u) := by
  cases s with
  | pre | returnGuard | residueGuard _ =>
      exact ⟨_, .pi [] _ _ _ _ (svConstTy E htin)
        (.pi _ _ _ _ _ (svConstTy E htst) (propTy E))⟩
  | returnPost =>
      exact ⟨_, .pi [] _ _ _ _ (svConstTy E htin)
        (.pi _ _ _ _ _ (svConstTy E htst)
          (.pi _ _ _ _ _ (svConstTy E htout)
            (.pi _ _ _ _ _ (svConstTy E htst) (propTy E))))⟩
  | residuePost r =>
      exact ⟨_, .pi [] _ _ _ _ (svConstTy E htin)
        (.pi _ _ _ _ _ (svConstTy E htst)
          (.pi _ _ _ _ _ (svConstTy E (hsvp r hs)) (propTy E)))⟩
  | bound =>
      exact ⟨_, .pi [] _ _ _ _ (svConstTy E htin)
        (.pi _ _ _ _ _ (svConstTy E htst) (natConstTyTB E hnat))⟩

/-- Every slot in `predSlotsOf` is valid — its residue slots only list residues
of `cd.resIds`. -/
theorem predSlotsOf_valid (cd : ContractSigData) :
    ∀ s ∈ predSlotsOf cd, s.validFor cd := by
  intro s hs
  cases s with
  | pre | returnGuard | returnPost | bound => exact trivial
  | residueGuard r =>
      show r ∈ cd.resIds
      simpa [predSlotsOf] using hs
  | residuePost r =>
      show r ∈ cd.resIds
      simpa [predSlotsOf] using hs

/-! ## The fold -/

/-- `EnvWfT` at the chain env for a suffix `l` of valid slots starting at
`i ≥ predBase`. -/
def predChainWf (cd : ContractSigData) : ∀ (l : List PredSlot) (i : Nat),
    predBase cd ≤ i → (∀ s ∈ l, s.validFor cd) → EnvWfT (predChainAt cd i l)
  | [], _, _, _ => natGroupEnvWf cd
  | s :: ss, i, hi, hok =>
      .axiom (predChainAt cd (i + 1) ss) i (exprOfSig cd s) _
        (predChainWf cd ss (i + 1) (by omega)
          (fun s' hs' => hok s' (List.mem_cons_of_mem _ hs')))
        (by rw [predChainAt_below cd ss (i + 1) i (by omega)]
            exact natE4_fresh_ge cd (by
              have hpb := predBase_eq cd; omega))
        (predSlotTy cd
          (predChainAt_sv cd ss (i + 1) (by omega) (tin_mem cd))
          (predChainAt_sv cd ss (i + 1) (by omega) (tst_mem cd))
          (predChainAt_sv cd ss (i + 1) (by omega) (tout_mem cd))
          (predChainAt_fam cd ss (i + 1) (by omega))
          (fun r hr => predChainAt_svp cd ss (i + 1) (by omega) hr)
          s (hok s (List.mem_cons_self _ _))).2
        (fun k => by cases s <;> rfl)
        (by cases s <;> rfl)

/-! ## Transport: the chain env IS `predEnvOf` -/

/-- `natE4`'s low members agree with `prefixEntries`' lookup. -/
theorem natE4_eq_prefix (cd : ContractSigData) (j : Nat) (hj : j < predBase cd) :
    (natE4 cd).members j = (prefixEntries cd)[j]? := by
  have hnb : natBase cd = svCount cd + svpCount cd := rfl
  have hpb : predBase cd = natBase cd + 4 := rfl
  by_cases hb : j < natBase cd
  · rw [natE4_low cd hb]
    by_cases hsv : j < svCount cd
    · have hl1 : (List.replicate (svCount cd) typeObjectMember ++
          List.replicate (svpCount cd) typeObjectMember).length =
          svCount cd + svpCount cd := by
        rw [List.length_append, List.length_replicate, List.length_replicate]
      have hlt : j < (List.replicate (svCount cd) typeObjectMember ++
          List.replicate (svpCount cd) typeObjectMember).length := by
        rw [hl1]; omega
      have hlt0 : j < (List.replicate (svCount cd) typeObjectMember).length := by
        rw [List.length_replicate]; exact hsv
      simp only [prefixEntries]
      rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt0]
      rw [List.getElem?_replicate, if_pos hsv]
    · have hlt : j < (List.replicate (svCount cd) typeObjectMember ++
          List.replicate (svpCount cd) typeObjectMember).length := by
        rw [List.length_append, List.length_replicate, List.length_replicate]
        omega
      have hle : (List.replicate (svCount cd) typeObjectMember).length ≤ j := by
        rw [List.length_replicate]; omega
      have hsvp : j - svCount cd < svpCount cd := by omega
      simp only [prefixEntries]
      rw [List.getElem?_append_left hlt, List.getElem?_append_right hle]
      rw [List.length_replicate, List.getElem?_replicate, if_pos hsvp]
  · obtain ⟨k, hk4, rfl⟩ : ∃ k < 4, j = natBase cd + k :=
      ⟨j - natBase cd, by omega, by omega⟩
    have hlen : (List.replicate (svCount cd) typeObjectMember ++
        List.replicate (svpCount cd) typeObjectMember).length = natBase cd := by
      rw [List.length_append, List.length_replicate, List.length_replicate]
      omega
    have hle : (List.replicate (svCount cd) typeObjectMember ++
        List.replicate (svpCount cd) typeObjectMember).length ≤
        natBase cd + k := by omega
    simp only [prefixEntries]
    rw [List.getElem?_append_right hle, hlen, Nat.add_sub_cancel_left]
    rcases k with _ | _ | _ | _ | k
    · rw [Nat.add_zero, natE4_fam]; rfl
    · rw [natE4_zero]; rfl
    · rw [natE4_succ]; rfl
    · rw [natE4_rec]; rfl
    · exact absurd hk4 (by omega)

/-- ResolvedEnv extensionality — equal member functions give equal envs. -/
theorem envExt {E E' : ResolvedEnv} (h : ∀ i, E.members i = E'.members i) :
    E = E' := by
  obtain ⟨f⟩ := E; obtain ⟨g⟩ := E'
  have : f = g := funext h
  subst this; rfl

/-- The admission chain is `predEnvOf` pointwise. -/
theorem predChainAt_eq_predEnvOf (cd : ContractSigData) :
    predChainAt cd (predBase cd) (predSlotsOf cd) = predEnvOf cd := by
  apply envExt
  intro j
  show _ = (memberEntries cd)[j]?
  by_cases hj : j < predBase cd
  · rw [predChainAt_below cd _ (predBase cd) j hj, natE4_eq_prefix cd j hj]
    have hlt : j < (prefixEntries cd).length := by
      rw [prefixEntries_length]; exact hj
    rw [memberEntries_eq_prefix_append_slots, List.getElem?_append_left hlt]
  · rw [predChainAt_get cd _ (predBase cd) j (Nat.le_refl _) (by omega)]
    have hle : (prefixEntries cd).length ≤ j := by
      rw [prefixEntries_length]; omega
    rw [memberEntries_eq_prefix_append_slots, List.getElem?_append_right hle,
        prefixEntries_length, List.getElem?_map]

/-! ## The headline -/

/-- **S3's headline** — the bound predicate environment is well-formed:
`predEnvOf cd` admits through `EnvWfT`, with the SV/SVP members as `axiomM`
prefix steps, Nat as one `.group` step, and the six predicate members as
`axiomM` steps carrying their `HasTyT` telescopes. -/
def predEnvWfT (cd : ContractSigData) : EnvWfT (predEnvOf cd) :=
  predChainAt_eq_predEnvOf cd ▸
    predChainWf cd (predSlotsOf cd) (predBase cd) (Nat.le_refl _)
      (predSlotsOf_valid cd)

end Rcic.PredSig
