import rcic.RcicTypedCheck
import rcic.RcicAnnEnvBridgeGroup
import rcic.RcicIndGroupAdmitted
import rcic.RcicIndGroupFixtureWf
import rcic.RcicAnnViewTySem

/-!
# M3-e-2 — an inductive group in the typed environment judgment and in the copy's scope

Nat with `zero`, `succ` and its universe-polymorphic recursor (`natRecMemberU`), at L-K1's fixture
references `0 … 3`:

* is ONE `EnvWfT` group step from the empty environment (`natEnvUWfT`). The member checks are L-K1's
  own, as `natEnvWfPrefixAt` and `natEnvUWfAt` pass them to `EnvWf.indMember`: `natFamAdmitted`,
  `natZeroAdmitted`, `natSuccAdmitted`, `natGroupRecursor` and `natURecAdmitted`. Each member's stored
  type is typed in the typed judgment, and so is the typed content of L-K1's views.
* is in the copy's scope (`natEnvUWfT_inScope`). Its structured views type the family's sort in the
  base, each constructor's type with the family present (ConstructorScope), and the recursor's type
  with the constructors present, at one level parameter (DerivationScope).
  - The recursor type built from the views (`groupRecTypeT`) is L-K1's stored `natRecTypeU`, by `rfl`.
  - L-K1's fixed-motive `natRecMember` is no recursor of the views (`natRecMember_not_groupRec`).

So the environment bridge's hypotheses hold at an environment with a group, and the bridge applies to
it (`natEnvU_annotated`, conditional on arc D's two typings like the bridge itself).

O1-a (section (6)): `False` at `0`, no constructor, its universe-polymorphic recursor at `1`:
* one `EnvWfT` group step (`falseEnvUWfT`), with L-K1's own checks: the family admitted, and the
  recursor admitted AnySort by `EliminationSelection.emptyProp` (the selection L-K1's `el03_pin` makes
  for a `Prop` family without constructors). Its stored type is L-K1's policy type, by `rfl`;
* in the copy's scope under the profile's O1 (`falseEnvUWfT_inScope`). The views' recursor type is the
  same term, by `rfl`;
* outside the scope before O1-a (`false_O1_before`: "a `Prop` family's recursor is PropOnly" fails
  here).

O1-b-2 (section (7)): `True` at `0`, `intro` at `1` (no field), its universe-polymorphic recursor at `2`:
* one `EnvWfT` group step (`trueEnvUWfT`), with L-K1's own checks: the family and the constructor
  admitted, and the recursor admitted AnySort by `EliminationSelection.singletonProp` (the selection
  L-K1's `el05_pin` makes for a `Prop` family whose one constructor has no field). Its stored type is
  L-K1's policy type, by `rfl`;
* in the copy's scope under the profile's unit exemption (`trueEnvUWfT_inScope`): `True` is a unit group
  on the typed views (`trueUnitT`), and the views' recursor type is the same term, by `rfl`;
* outside the scope before O1-b-2 (`true_O1_before`: "a `Prop` family with a constructor eliminates into
  `Prop` only" fails here).

W-1 (e-3) (sections (8), (9)): two struct groups at `0 … 2`. `S` has one field, a proof of
`Π (P : Prop), P → P`. `And` has two parameters in `Prop` and two fields, each a proof:
* one `EnvWfT` group step each (`structEnvUWfT`, `andEnvUWfT`), with L-K1's own checks. The recursor is
  admitted AnySort by `EliminationSelection.singletonProp`: every field is safe, its sort zero at every
  valuation. Its stored type is L-K1's policy type, by `rfl`. `S`'s family is `True`'s member, so its
  family view and admission are `True`'s;
* in the copy's scope under the profile's struct exemption (`structEnvUWfT_inScope`,
  `andEnvUWfT_inScope`): each is a struct group on the typed views (`structStructT`, `andStructT`), and
  the views' recursor type is the same term, by `rfl`;
* outside the scope before W-1 (e-3) (`struct_O1_before`, `and_O1_before`);
* annotated with no hypothesis, through the semantic prefix (`structEnvU_annotated`,
  `andEnvU_annotated`), with row 1 consumed at each environment (`structEnv_sorts_notConv`,
  `andEnv_sorts_notConv`).

The three checks of a constructor admitted right after its family (`ctorBefore_famOnly`,
`ctorContig_famOnly`, `census_famOne`) are stated once over the family's member; `True`, `S` and `And`
use them.
-/

namespace Rcic.Declarative

/-! ## (1) the family and the constructors -/

/-- `N : Sort 1`: no parameter, no index. -/
def natFamViewT : FamViewT natFamMember where
  params := []
  indices := []
  sort := .succ .zero
  stored := rfl
  profile := Or.inr uniformType_succ_zero

/-- `N : Sort 1`, wherever the family is present. -/
def natConstTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h : E.members 0 = some natFamMember) :
    HasTyT E n Γ (.const 0 []) (.sort (.succ .zero)) :=
  .const Γ 0 [] natFamMember h rfl rfl

/-- `zero : N`: no field. -/
def natZeroCtorT : GroupCtorT emptyEnv 0 natFamMember natFamViewT where
  ref := 1
  member := natZeroMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := .succ .zero
  hT := natConstTyT rfl
  hlvl := rfl
  view :=
    { mirrors := []
      fields := []
      res := []
      stored := rfl
      mirrorsConv := .nil []
      typed := .nil [] 0 [] (.nil (.succ .zero))
      univ := fun _ _ h => (List.not_mem_nil _ h).elim
      drecD_typed := drecDTypedT_of_absent (by decide) }

/-- `succ : N → N`: one directly recursive field. -/
def natSuccCtorT : GroupCtorT emptyEnv 0 natFamMember natFamViewT where
  ref := 2
  member := natSuccMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := .imax (.succ .zero) (.succ .zero)
  hT := .pi [] _ _ _ _ (natConstTyT rfl) (natConstTyT rfl)
  hlvl := rfl
  view :=
    { mirrors := []
      fields := [.drec []]
      res := []
      stored := rfl
      mirrorsConv := .nil []
      typed := .drec [] 0 [] [] [] (.nil (.succ .zero)) (.nil [] 0 [] (.nil (.succ .zero)))
      univ := fun _ _ h => by simp at h
      drecD_typed := drecDTypedT_of_absent (by decide) }

/-- the constructors, the group list's head added last. -/
def natCsT : List (GroupCtorT emptyEnv 0 natFamMember natFamViewT) := [natSuccCtorT, natZeroCtorT]

/-! ## (2) the recursor's type, typed with the constructors present -/

/-- the motive's type, `N → Sort u`. -/
abbrev natMotTyU : Expr Nat := .pi (.const 0 []) (.sort (.param 0))

/-- `P a : Sort u`, for the motive `P` at `bvar i` and `a : N`. -/
def natMotAppTyT {Γ : LCtx} (i : Nat) (a : Expr Nat) (hP : lookupType Γ i = some natMotTyU)
    (ha : HasTyT natEnvPrefix 1 Γ a (.const 0 [])) :
    HasTyT natEnvPrefix 1 Γ (.app (.bvar i) a) (.sort (.param 0)) :=
  .app Γ (.bvar i) a (.const 0 []) (.sort (.param 0)) (.bvar Γ i _ hP) ha

/-- the zero minor's type, `P zero`, under the motive. -/
abbrev natMzDom : Expr Nat := .app (.bvar 0) (.const 1 [])
/-- the successor minor's type, `Π (n : N) (ih : P n), P (succ n)`, under the motive and `mz`. -/
abbrev natMsTy : Expr Nat :=
  .pi (.const 0 []) (.pi (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const 2 []) (.bvar 1))))
/-- the major and the body, `Π (t : N), P t`, under the motive and both minors. -/
abbrev natMajorTy : Expr Nat := .pi (.const 0 []) (.app (.bvar 3) (.bvar 0))

/-- the recursor type's sort: one `imax` per binder. -/
abbrev natRecSortU : Level :=
  .imax (.imax (.succ .zero) (.succ (.param 0)))
    (.imax (.param 0)
      (.imax (.imax (.succ .zero) (.imax (.param 0) (.param 0))) (.imax (.succ .zero) (.param 0))))

def natMsTyT :
    HasTyT natEnvPrefix 1 [.assumption natMzDom, .assumption natMotTyU] natMsTy
      (.sort (.imax (.succ .zero) (.imax (.param 0) (.param 0)))) :=
  .pi _ _ _ _ _ (natConstTyT rfl)
    (.pi _ _ _ _ _ (natMotAppTyT 2 (.bvar 0) rfl (.bvar _ 0 _ rfl))
      (natMotAppTyT 3 _ rfl
        (.app _ (.const 2 []) (.bvar 1) (.const 0 []) (.const 0 [])
          (.const _ 2 [] natSuccMember rfl rfl rfl) (.bvar _ 1 _ rfl))))

def natMajorTyT :
    HasTyT natEnvPrefix 1 [.assumption natMsTy, .assumption natMzDom, .assumption natMotTyU]
      natMajorTy (.sort (.imax (.succ .zero) (.param 0))) :=
  .pi _ _ _ _ _ (natConstTyT rfl) (natMotAppTyT 3 (.bvar 0) rfl (.bvar _ 0 _ rfl))

/-- `natRecTypeU` typed in the derivation scope at one level parameter. -/
def natRecTypeUTyT : HasTyT natEnvPrefix 1 [] natRecTypeU (.sort natRecSortU) :=
  .pi _ _ _ _ _ (.pi _ _ _ _ _ (natConstTyT rfl) (.sort _ (.param 0)))
    (.pi _ _ _ _ _ (natMotAppTyT 0 (.const 1 []) rfl (.const _ 1 [] natZeroMember rfl rfl rfl))
      (.pi _ _ _ _ _ natMsTyT natMajorTyT))

/-- the recursor: AnySort, its stored type the one built from the views. -/
def natRecT : GroupRecT emptyEnv 0 natFamMember natFamViewT natCsT where
  member := natRecMemberU
  hcls := rfl
  hnobody := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := fun _ => rfl
  u := natRecSortU
  hT := natRecTypeUTyT
  hlvl := rfl

/-! ## (3) the group step of the typed environment judgment -/

/-- the typed content of L-K1's views: their domains typed at the recorded levels. Only `succ`'s field
    is a domain. -/
theorem natSuccFieldTyped {E : ResolvedEnv} (h : E.members 0 = some natFamMember) :
    TelTypedT E 0 ([] ++ [Expr.const 0 []]) (fun _ => .succ .zero)
  | ⟨0, _⟩ => ⟨natConstTyT h⟩
  | ⟨k + 1, hk⟩ => absurd hk (by simp)

theorem natFamTyped : IndGroupTypedT natFamAdmitted := fun i => i.elim0

theorem natZeroTyped : IndGroupTypedT natZeroAdmitted :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem natSuccTyped : IndGroupTypedT natSuccAdmitted :=
  ⟨fun i => i.elim0, natSuccFieldTyped rfl, fun i => i.elim0⟩

theorem natRecTyped : IndGroupTypedT natGroupRecursor := by
  refine ⟨fun i => i.elim0, fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ => ?_⟩
  · rcases i with _ | _ | k
    · exact ⟨fun j => j.elim0, fun j => j.elim0⟩
    · exact ⟨natSuccFieldTyped rfl, fun j => j.elim0⟩
    · exact absurd hi (by simp [natGroupAdmitted])
  · rcases i with _ | _ | k
    · exact iotaEquationTypedT_of_check (synCheck _ _) rfl
    · exact iotaEquationTypedT_of_check (synCheck _ _) rfl
    · exact absurd hi (by simp [natGroupAdmitted])

/-- L-K1's checks, member by member, as `natEnvWfPrefixAt` and `natEnvUWfAt` pass them to
    `EnvWf.indMember`, each member's stored type typed in the group built so far, and the typed content
    of L-K1's views. `zero` and `succ` are also typed in ConstructorScope, Nat alone (05 §4). -/
def natMembersT :
    GroupMembersT (extendEnv emptyEnv 0 natFamMember) emptyEnv
      [(0, natFamMember), (1, natZeroMember), (2, natSuccMember), (3, natRecMemberU)] natEnvU :=
  .cons _ 0 natFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    natFamAdmitted PUnit.unit _ (.sort [] (.succ .zero)) (fun h => absurd h (by decide))
    natFamTyped
    (.cons _ 1 natZeroMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      natZeroAdmitted PUnit.unit _ (natConstTyT rfl) (fun _ => ⟨natConstTyT rfl⟩)
      natZeroTyped
      (.cons _ 2 natSuccMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        natSuccAdmitted PUnit.unit _
        (.pi [] _ _ _ _ (natConstTyT rfl) (natConstTyT rfl))
        (fun _ => ⟨.pi [] _ _ _ _ (natConstTyT rfl) (natConstTyT rfl)⟩) natSuccTyped
        (.cons _ 3 natRecMemberU _ _ rfl rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl
          rfl natGroupRecursor (.ofCheck _ _ (by with_unfolding_all rfl)) _ natRecTypeUTyT (fun h => absurd h (by decide))
          natRecTyped (.nil _))))

/-- Nat, its constructors and its recursor: ONE group step of the typed environment judgment. -/
def natEnvUWfT : EnvWfT natEnvU :=
  .group emptyEnv 0 natFamMember [(1, natZeroMember), (2, natSuccMember)] 3 natRecMemberU natEnvU .empty
    rfl (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl natMembersT

/-! ## (4) the group in the copy's scope -/

/-- the structured views give the group's members, and the group meets both profiles: no index, a
    `Type` family. -/
def natInScopeT :
    GroupInScopeT emptyEnv 0 natFamMember [(1, natZeroMember), (2, natSuccMember)] 3 natRecMemberU where
  fv := natFamViewT
  htel := .nil []
  cs := natCsT
  hctors := rfl
  hlayout := rfl
  grec := natRecT
  hrr := rfl
  hrm := rfl
  hprof := ⟨fun v hv => (List.not_mem_nil v hv).elim, fun h _ => absurd (h fun _ => 0) (by decide)⟩
  hpb := by decide
  hsnd := by decide

theorem natEnvUWfT_inScope : natEnvUWfT.InScope := ⟨trivial, ⟨natInScopeT⟩⟩

theorem pin_envWfT_natU : Nonempty (EnvWfT natEnvU) := ⟨natEnvUWfT⟩

/-- TOOTH (M3-e-3): ConstructorScope is not the group built so far. When `succ` is checked, the group
    built so far holds `zero` and types it at `Nat`; Nat's ConstructorScope does not hold it, and gives it
    no typing at any type. A stored type naming `zero` would pass `hT` there and fail `hTc`. -/
theorem natZero_ctorScope_split {n : Nat} {Γ : LCtx} :
    Nonempty (HasTyT (extendEnv (extendEnv emptyEnv 0 natFamMember) 1 natZeroMember) n Γ (.const 1 [])
      (.const 0 [])) ∧
    ∀ T, HasTyT (extendEnv emptyEnv 0 natFamMember) n Γ (.const 1 []) T → False :=
  ⟨⟨.const Γ 1 [] natZeroMember rfl rfl rfl⟩, fun _ h => by
    obtain ⟨m, hm⟩ := hasTyT_constsIn h
    simp [extendEnv, emptyEnv] at hm⟩

/-- TOOTH: L-K1's fixed-motive recursor `natRecMember` (a `Sort 1` motive at arity `0`, which 05 §11
    does not derive) is no recursor of this group. Its stored type is neither policy's built type. -/
theorem natRecMember_not_groupRec :
    ¬ ∃ rec : GroupRecT emptyEnv 0 natFamMember natFamViewT natCsT, rec.member = natRecMember := by
  rintro ⟨rec, hm⟩
  have hs := rec.stored
  rw [hm] at hs
  cases h : rec.elim <;> rw [h] at hs <;> exact absurd hs (by decide)

/-! ## (4.5) the ι-correspondence certificates at `natEnvU`

GAP-B for the Nat group: both directions of `IotaCorrTA` discharge at every
sub-environment of `natEnvU` — member inversion pins the three witness
references to the group (`0` family, `1`/`2` constructors, `3` recursor),
`Nat`'s `.const 0 []` field domain is rigid and whnf-stable (`noTransparentB`/
`headStableB`/`transparentBody`), and the schema/RHS equality computes through
`instPrefix_bvar_lt`/`instPrefix_bvarSpine` on the emitted direct-recursive
call.  Decided per-witness by `iotaWitnessSB`/`iotaWitnessSAnnB` — never
the false universal `∀ EA, IotaCorrTA EA`. -/

open Ann in
/-- member inversion for `natEnvU` (covers `natEnvPrefix` + the recursor). -/
theorem natEnvU_mem {c : Nat} {m : CheckedMember}
    (h : natEnvU.members c = some m) :
    (c = 0 ∧ m = natFamMember) ∨ (c = 1 ∧ m = natZeroMember) ∨
      (c = 2 ∧ m = natSuccMember) ∨ (c = 3 ∧ m = natRecMemberU) := by
  have hmem : natEnvU.members c =
      (if c = 3 then some natRecMemberU
       else if c = 2 then some natSuccMember
       else if c = 1 then some natZeroMember
       else if c = 0 then some natFamMember else none) := rfl
  rw [hmem] at h
  by_cases h3 : c = 3
  · rw [if_pos h3] at h; cases h
    exact Or.inr (Or.inr (Or.inr ⟨h3, rfl⟩))
  · rw [if_neg h3] at h
    by_cases h2 : c = 2
    · rw [if_pos h2] at h; cases h
      exact Or.inr (Or.inr (Or.inl ⟨h2, rfl⟩))
    · rw [if_neg h2] at h
      by_cases h1 : c = 1
      · rw [if_pos h1] at h; cases h; exact Or.inr (Or.inl ⟨h1, rfl⟩)
      · rw [if_neg h1] at h
        by_cases h0 : c = 0
        · rw [if_pos h0] at h; cases h; exact Or.inl ⟨h0, rfl⟩
        · rw [if_neg h0] at h; exact Option.noConfusion h

open Ann in
/-- The shared member-class pinning every `IotaWitness`/`IotaWitnessS` over
a `natEnvU` sub-environment satisfies: family `0`, ctor `1` or `2`,
recursor `3`. -/
theorem natEnvU_witness_refs {E₀ : ResolvedEnv} (hsub : EnvSub E₀ natEnvU)
    {recRef ctorRef familyRef : Nat} {recMember ctorMember famMember : CheckedMember}
    (hfam : E₀.members familyRef = some famMember)
    (hfamK : famMember.mclass = .inductiveM)
    (hctor : E₀.members ctorRef = some ctorMember)
    (hctorK : ctorMember.mclass = .constructorM)
    (hrec : E₀.members recRef = some recMember)
    (hrecK : recMember.mclass = .recursorM) :
    (familyRef = 0 ∧ famMember = natFamMember) ∧
    ((ctorRef = 1 ∧ ctorMember = natZeroMember) ∨
      (ctorRef = 2 ∧ ctorMember = natSuccMember)) ∧
    (recRef = 3 ∧ recMember = natRecMemberU) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases natEnvU_mem (hsub _ _ hfam) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · exact ⟨hr, hm⟩
    · rw [hm] at hfamK; exact absurd hfamK (by decide)
    · rw [hm] at hfamK; exact absurd hfamK (by decide)
    · rw [hm] at hfamK; exact absurd hfamK (by decide)
  · rcases natEnvU_mem (hsub _ _ hctor) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · rw [hm] at hctorK; exact absurd hctorK (by decide)
    · exact Or.inl ⟨hr, hm⟩
    · exact Or.inr ⟨hr, hm⟩
    · rw [hm] at hctorK; exact absurd hctorK (by decide)
  · rcases natEnvU_mem (hsub _ _ hrec) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · rw [hm] at hrecK; exact absurd hrecK (by decide)
    · rw [hm] at hrecK; exact absurd hrecK (by decide)
    · rw [hm] at hrecK; exact absurd hrecK (by decide)
    · exact ⟨hr, hm⟩

open Ann in
/-- `Nat`'s domain is rigid + head-stable in any env that has the family. -/
theorem natEnvU_const0_closed {E₀ : ResolvedEnv}
    (hmem0 : E₀.members 0 = some natFamMember) :
    noTransparentB E₀ (.const 0 []) = true ∧
      headStableB (.const 0 []) = true ∧
      transparentBody E₀ 0 [] = none := by
  have ht0 : transparentBody E₀ 0 [] = none := by
    unfold transparentBody
    rw [hmem0]
    rfl
  refine ⟨?_, rfl, ht0⟩
  show (transparentBody E₀ 0 []).isNone = true
  rw [ht0]
  rfl

open Ann in
/-- `constsMemberFuel` discharges on the Nat family const. -/
theorem natEnvU_constsMember {E₀ : ResolvedEnv}
    (hmem0 : E₀.members 0 = some natFamMember) {fuel : Nat} :
    constsMemberFuel E₀ (fuel + 1) (.const 0 []) = true := by
  cases fuel with
  | zero => unfold constsMemberFuel; rw [hmem0]; rfl
  | succ f => unfold constsMemberFuel; rw [hmem0]; rfl

open Ann in
/-- erase-side per-witness adaptation for a witness whose references are the
    Nat group's — factored out of `corrEraseCert_sub_natEnvU` so the SAME proof
    serves a Nat witness over a larger sub-environment (e.g. `listEnvUT`'s). -/
theorem natEraseCert_of_refs {E₀ : ResolvedEnv} (w : IotaWitness E₀)
    (hfamR : w.familyRef = 0) (hfamM : w.famMember = natFamMember)
    (hctorD : (w.ctorRef = 1 ∧ w.ctorMember = natZeroMember) ∨
      (w.ctorRef = 2 ∧ w.ctorMember = natSuccMember))
    (hrecR : w.recRef = 3) (hrecM : w.recMember = natRecMemberU) :
    ∃ fuel, iotaWitnessSB w fuel = true := by
  have hnM : w.nMinors = 2 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hnp0 : w.nparams + w.nindices = 0 := by
    have h := w.hnidx; rw [hfamM] at h
    have h0 : piCount natFamMember.mtype = 0 := rfl
    rw [h0] at h; omega
  have hnp : w.nparams = 0 := by omega
  have hni : w.nindices = 0 := by omega
  have hmem0 : E₀.members 0 = some natFamMember := by
    have h := w.hfam; rwa [hfamR, hfamM] at h
  have hpmLen : w.preMajor.length = 3 := by
    have h := w.hpre; rw [hnp, hnM, hni] at h; omega
  obtain ⟨l, hls⟩ : ∃ l, w.ls = [l] := by
    have h := w.hlsLen; rw [hrecM] at h
    have h1 : natRecMemberU.arity = 1 := rfl
    rw [h1] at h
    generalize hlg : w.ls = lsg
    rw [hlg] at h
    rcases lsg with _ | ⟨l, _ | ⟨l', ls⟩⟩
    · simp at h
    · exact ⟨l, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  rcases hctorD with ⟨hctorR, hctorM⟩ | ⟨hctorR, hctorM⟩
  · -- ======================= zero =======================
    have hctorIdx : w.ctorIdx = 0 := by
      have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
    have hfields : w.fields = [] := by
      have h := w.hnpar; rw [hnp, hctorM] at h
      have h0 : piCount natZeroMember.mtype = 0 := rfl
      rw [h0] at h; simp only [Nat.zero_add] at h
      exact List.length_eq_zero.mp h
    have hcd : w.ctorDoms = [] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_nil, Nat.add_zero, peelPis] at h
      injection h with hp; injection hp with h1 h2; exact h1.symm
    have hcr : w.ctorResult = .const 0 [] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_nil, Nat.add_zero, peelPis] at h
      injection h with hp; injection hp with h1 h2; exact h2.symm
    have hkinds : w.kinds = [] := by
      have h := w.hkinds; rw [hfamR, hcd, hnp] at h
      simp only [List.drop_nil, analyzeFields] at h
      injection h with h'; exact h'.symm
    have hctorAfter : w.ctorAfterParams = .const 0 [] := by
      have h := w.hctorAfter; rw [hnp, hctorM] at h
      simp only [List.take_zero, applyTel] at h
      injection h with h'; exact h'.symm
    -- the recognizer
    refine ⟨8, ?_⟩
    show iotaWitnessSB w 8 = true
    unfold iotaWitnessSB
    rw [hfamR, hfamM, hnp, hni, hnM, hfields, hcd, hcr]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rfl
      · unfold iotaWitnessStableB ctorFieldTelRaw
        simp only [List.drop_nil, List.foldr_nil, fieldBvars,
          List.range_zero, List.reverse_nil, List.map_nil, List.all_nil]
        show constsMemberFuel E₀ (8 + 1)
            (lift 0 (0 + 1 + 2 + 0) (.const 0 [])) = true
        have htl : lift 0 (0 + 1 + 2 + 0) (.const 0 [] : Expr Nat) =
            .const 0 [] := rfl
        rw [htl]
        exact natEnvU_constsMember hmem0
    · have hschema : iotaSchemaS w 8 = some (.bvar 1) := by
        show iotaOpenRhs E₀ 8
            (.const w.recRef (canonRecLevels w.recMember.arity))
            (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
            (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
            w.nparams w.nMinors (w.kinds.map shapeOfKind)
            (fieldBvars w.fields.length)
            (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
              (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
          some (.bvar 1)
        rw [hrecR, hrecM, hnp, hni, hnM, hctorIdx, hfields, hcd, hcr, hkinds]
        rfl
      rw [hschema]
      rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rfl
      · rw [decide_eq_true_eq]
        rw [hls, List.append_nil]
        rw [show instantiateLevels [l] (.bvar 1) = (.bvar 1 : Expr Nat) from rfl]
        have hmin : instPrefix w.preMajor (.bvar 1) = w.minor := by
          apply instPrefix_bvar_lt
          · rw [hpmLen]; decide
          · rw [hpmLen]
            show w.preMajor[1]? = some w.minor
            have h := w.hminor; rw [hnp, hctorIdx] at h
            exact h
        rw [hmin]
        unfold iotaRhsOf
        rw [hrecR, hls, hnp, hnM, hfields, hkinds, hctorAfter]
        rfl
  · -- ======================= succ =======================
    have hctorIdx : w.ctorIdx = 1 := by
      have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
    obtain ⟨f, hfields⟩ : ∃ f, w.fields = [f] := by
      have h := w.hnpar; rw [hnp, hctorM] at h
      have h0 : piCount natSuccMember.mtype = 1 := rfl
      rw [h0] at h; simp only [Nat.zero_add] at h
      generalize hfg : w.fields = fg
      rw [hfg] at h
      rcases fg with _ | ⟨f, _ | ⟨f', fs⟩⟩
      · simp at h
      · exact ⟨f, rfl⟩
      · simp only [List.length_cons] at h; exact False.elim (by omega)
    have hcd : w.ctorDoms = [.const 0 []] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_cons, List.length_nil, Nat.add_zero, peelPis] at h
      injection h with hp; injection hp with h1 h2; exact h1.symm
    have hcr : w.ctorResult = .const 0 [] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_cons, List.length_nil, Nat.add_zero, peelPis] at h
      injection h with hp; injection hp with h1 h2; exact h2.symm
    have hkinds : w.kinds = [.directRec] := by
      have h := w.hkinds; rw [hfamR, hcd, hnp] at h
      have ha : analyzeFields 0 ([.const 0 []].drop 0) = some [.directRec] := rfl
      rw [ha] at h
      injection h with h'; exact h'.symm
    have hctorAfter : w.ctorAfterParams =
        .pi (.const 0 []) (.const 0 []) := by
      have h := w.hctorAfter; rw [hnp, hctorM] at h
      simp only [List.take_zero, applyTel] at h
      have hIL : instantiateLevels w.ls natSuccMember.mtype =
          .pi (.const 0 []) (.const 0 []) := rfl
      rw [hIL] at h
      injection h with h'; exact h'.symm
    obtain ⟨hnt0, hst0, ht0⟩ := natEnvU_const0_closed hmem0
    have hlen4 : (w.preMajor ++ [f]).length = 4 := by
      rw [List.length_append, hpmLen]; rfl
    refine ⟨8, ?_⟩
    show iotaWitnessSB w 8 = true
    unfold iotaWitnessSB
    rw [hfamR, hfamM, hnp, hni, hnM, hfields, hcd, hcr]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · -- directFragCheck E₀ 8 0 0 0 0 0 [.const 0 []]
        show directFragCheck E₀ 8 0 natFamMember.arity 0 0 0
            (List.drop 0 [.const 0 []]) = true
        rw [List.drop_zero]
        show directFragOne E₀ 8 0 natFamMember.arity 0 0 0 (.const 0 []) &&
            directFragCheck E₀ 8 0 natFamMember.arity 0 0 (0 + 1) [] = true
        rw [Bool.and_eq_true]; refine ⟨?_, rfl⟩
        unfold directFragOne
        rw [hnt0]
        rfl
      · -- iotaWitnessStableB
        show iotaWitnessStableB E₀ 8 ([.const 0 []].drop 0) (fieldBvars [f].length)
            (lift 0 (1 + 1 + 2 + 0)
              (ctorFieldTelRaw 0 [.const 0 []] (.const 0 []))) = true
        show ((List.all [.const 0 []] (constsMemberFuel E₀ (8 + 1)) &&
            List.all [.bvar 0] (constsMemberFuel E₀ (8 + 1))) &&
            constsMemberFuel E₀ (8 + 1) (.pi (.const 0 []) (.const 0 []))) = true
        simp only [List.all_cons, List.all_nil, constsMemberFuel, hmem0]
        rfl
    · have hschema : iotaSchemaS w 8 =
          some (foldApps (.bvar 1)
            [.bvar 0,
              foldApps (.const 3 [.param 0])
                (bvarSpine 4)]) := by
        show iotaOpenRhs E₀ 8
            (.const w.recRef (canonRecLevels w.recMember.arity))
            (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
            (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
            w.nparams w.nMinors (w.kinds.map shapeOfKind)
            (fieldBvars w.fields.length)
            (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
              (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
          some (foldApps (.bvar 1)
            [.bvar 0, foldApps (.const 3 [.param 0]) (bvarSpine 4)])
        rw [hrecR, hrecM, hnp, hni, hnM, hctorIdx, hfields, hcd, hcr, hkinds]
        unfold iotaOpenRhs
        simp only [iotaArgs]
        have hlt : lift 0 ([f].length + 1 + 2 + 0) (.const 0 [] : Expr Nat) =
            .const 0 [] := rfl
        rw [hlt]
        have hpt : piTelescopeFuel E₀ 8 (.const 0 []) =
            some ([], .const 0 []) :=
          piTelescopeFuel_of_tailStable _ hnt0 hst0 (by decide)
        rw [hpt]
        rfl
      rw [hschema]
      rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rfl
      · rw [decide_eq_true_eq]
        rw [hls]
        have hIL : instantiateLevels [l]
            (foldApps (.bvar 1)
              [.bvar 0, foldApps (.const 3 [.param 0]) (bvarSpine 4)]) =
          foldApps (.bvar 1)
            [.bvar 0, foldApps (.const 3 [l]) (bvarSpine 4)] := rfl
        rw [hIL, instPrefix_foldApps]
        have hminI : instPrefix (w.preMajor ++ [f]) (.bvar 1) = w.minor := by
          have hj : 1 < (w.preMajor ++ [f]).length := by rw [hlen4]; decide
          have hget : (w.preMajor ++ [f])[(w.preMajor ++ [f]).length - 1 - 1]? =
              some w.minor := by
            rw [hlen4]
            rw [show ((4 : Nat) - 1 - 1) = 2 from rfl]
            rw [List.getElem?_append_left (by rw [hpmLen]; decide)]
            have h := w.hminor; rw [hnp, hctorIdx] at h
            exact h
          exact instPrefix_bvar_lt hj hget
        rw [hminI]
        simp only [List.map_cons, List.map_nil]
        have hfI : instPrefix (w.preMajor ++ [f]) (.bvar 0) = f := by
          have hj : 0 < (w.preMajor ++ [f]).length := by rw [hlen4]; decide
          have hget : (w.preMajor ++ [f])[(w.preMajor ++ [f]).length - 1 - 0]? =
              some f := by
            rw [hlen4]
            rw [show ((4 : Nat) - 1 - 0) = 3 from rfl]
            rw [List.getElem?_append_right (Nat.le_of_eq hpmLen)]
            rw [hpmLen, show (3 - 3 : Nat) = 0 from rfl]
            rfl
          exact instPrefix_bvar_lt hj hget
        rw [hfI]
        rw [instPrefix_foldApps, instPrefix_const]
        have hsp : (bvarSpine (w.preMajor ++ [f]).length).map
            (instPrefix (w.preMajor ++ [f])) = w.preMajor ++ [f] :=
          instPrefix_bvarSpine _
        rw [hlen4] at hsp
        rw [hsp]
        unfold iotaRhsOf
        rw [hrecR, hls, hnp, hnM, hfields, hkinds, hctorAfter]
        have hrcf : recCallField (.const 3 [l]) w.preMajor 0 2 f (.const 0 []) =
            foldApps (.const 3 [l]) (w.preMajor ++ [f]) := by
          show foldApps (.const 3 [l])
              (recPrefix w.preMajor 0 2 ++ familyIdx 0 (.const 0 []) ++ [f]) = _
          have hfidx : familyIdx 0 (.const 0 [] : Expr Nat) = [] := rfl
          rw [hfidx]
          have hpre' : recPrefix w.preMajor 0 2 = w.preMajor := by
            show w.preMajor.take (0 + 1 + 2) = w.preMajor
            rw [show (0 + 1 + 2 : Nat) = w.preMajor.length from hpmLen.symm]
            exact List.take_length _
          rw [hpre', List.append_nil]
        have hrhs : rhsArgs (.const 3 [l]) w.preMajor 0 2 [f] [.directRec]
            (.pi (.const 0 []) (.const 0 [])) =
            [f, foldApps (.const 3 [l]) (w.preMajor ++ [f])] := by
          show [f, recCallField (.const 3 [l]) w.preMajor 0 2 f (.const 0 [])] = _
          rw [hrcf]
        rw [hrhs]

open Ann in
/-- erase-side: every `IotaWitness` over a sub-env of `natEnvU` adapts. -/
theorem corrEraseCert_sub_natEnvU {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ natEnvU) : EnvCorrEraseCert E₀ := by
  intro w
  obtain ⟨⟨hfamR, hfamM⟩, hctorD, ⟨hrecR, hrecM⟩⟩ :=
    natEnvU_witness_refs hsub w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
  exact natEraseCert_of_refs w hfamR hfamM hctorD hrecR hrecM

open Ann in
/-- ann-side per-witness check for a witness whose references are the Nat
    group's — the `natEnvU` proof with the pinning supplied. -/
theorem natAnnCert_of_refs {E₀ : ResolvedEnv} (w : IotaWitnessS E₀)
    (hfamR : w.familyRef = 0) (hfamM : w.famMember = natFamMember)
    (hctorD : (w.ctorRef = 1 ∧ w.ctorMember = natZeroMember) ∨
      (w.ctorRef = 2 ∧ w.ctorMember = natSuccMember))
    (hrecR : w.recRef = 3) (hrecM : w.recMember = natRecMemberU) :
    iotaWitnessSAnnB E₀ w = true := by
  have hnM : w.nMinors = 2 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hnp0 : w.nparams + w.nindices = 0 := by
    have h := w.hnidx; rw [hfamM] at h
    have h0 : piCount natFamMember.mtype = 0 := rfl
    rw [h0] at h; omega
  have hnp : w.nparams = 0 := by omega
  have hni : w.nindices = 0 := by omega
  have hmem0 : E₀.members 0 = some natFamMember := by
    have h := w.hfam; rwa [hfamR, hfamM] at h
  have hpmLen : w.preMajor.length = 3 := by
    have h := w.hpre; rw [hnp, hnM, hni] at h; omega
  obtain ⟨l, hls⟩ : ∃ l, w.ls = [l] := by
    have h := w.hlsLen; rw [hrecM] at h
    have h1 : natRecMemberU.arity = 1 := rfl
    rw [h1] at h
    generalize hlg : w.ls = lsg
    rw [hlg] at h
    rcases lsg with _ | ⟨l, _ | ⟨l', ls⟩⟩
    · simp at h
    · exact ⟨l, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  obtain ⟨hnt0, hst0, ht0⟩ := natEnvU_const0_closed hmem0
  have hlen4 : (w.preMajor ++ w.fields).length =
      w.preMajor.length + w.fields.length := List.length_append _ _
  rcases hctorD with ⟨hctorR, hctorM⟩ | ⟨hctorR, hctorM⟩
  · -- ======================= zero =======================
    have hctorIdx : w.ctorIdx = 0 := by
      have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
    have hfields : w.fields = [] := by
      have h := w.hnpar; rw [hnp, hctorM] at h
      have h0 : piCount natZeroMember.mtype = 0 := rfl
      rw [h0] at h; simp only [Nat.zero_add] at h
      exact List.length_eq_zero.mp h
    have hcd : w.ctorDoms = [] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_nil, Nat.add_zero, peelPis] at h
      injection h with hp; injection hp with h1 h2; exact h1.symm
    have hcr : w.ctorResult = .const 0 [] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_nil, Nat.add_zero, peelPis] at h
      injection h with hp; injection hp with h1 h2; exact h2.symm
    have hsh : w.shapes = [] := by
      have h := w.hshapes
      rw [hfamR, hfamM, hnp, hni, hcd, List.drop_zero] at h
      exact (Option.some.inj h).symm
    have hsc : w.schema = .bvar 1 := by
      have h := w.hschema
      rw [hrecR, hrecM, hnp, hnM, hni, hctorIdx, hfields, hcd, hcr, hsh] at h
      have hconc : iotaOpenRhs E₀ 8 (.const 3 (canonRecLevels 1))
          (.bvar 1) (preMajorBvars 0 2 0 0) 0 2 []
          (fieldBvars 0) (lift 0 (0 + 1 + 2 + 0)
            (ctorFieldTelRaw 0 [] (.const 0 []))) = some (.bvar 1) := rfl
      exact iotaOpenRhs_agree E₀ h hconc
    show iotaWitnessSAnnB E₀ w = true
    unfold iotaWitnessSAnnB
    rw [hfamR, hfamM, hnp, hni, hctorIdx, hcd, List.drop_zero]
    rw [Bool.and_eq_true]; refine ⟨rfl, ?_⟩
    have happ : applyTel (w.preMajor.take 0)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
        some (.const 0 []) := by
      rw [hctorM]
      show applyTel (w.preMajor.take 0)
          (instantiateLevels (w.ls.take 0) natZeroMember.mtype) =
        some (.const 0 [])
      rw [List.take_zero]
      rfl
    rw [happ]
    simp only
    rw [hfields, hsh]
    rw [show fieldsTelS ([] : List (Expr Nat)) ([] : List FieldShape)
        (.const 0 []) = true from rfl, Bool.true_and]
    obtain ⟨minor, hmin⟩ : ∃ m, w.preMajor[0 + 1 + 0]? = some m :=
      ⟨w.preMajor[1]'(by rw [hpmLen]; decide), List.getElem?_eq_getElem _⟩
    rw [hmin]
    simp only
    rw [decide_eq_true_eq]
    unfold iotaRhsOfS
    rw [hls, hfields, List.append_nil, hsc]
    rw [show instantiateLevels [l] (.bvar 1) = (.bvar 1 : Expr Nat) from rfl]
    have hminI : instPrefix w.preMajor (.bvar 1) = minor := by
      have hj : 1 < w.preMajor.length := by rw [hpmLen]; decide
      have hget : w.preMajor[w.preMajor.length - 1 - 1]? = some minor := by
        rw [hpmLen]
        rw [show ((3 : Nat) - 1 - 1) = 1 from rfl]
        exact hmin
      exact instPrefix_bvar_lt hj hget
    rw [hminI, hrecR, hnM]
    rfl
  · -- ======================= succ =======================
    have hctorIdx : w.ctorIdx = 1 := by
      have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
    obtain ⟨f, hfields⟩ : ∃ f, w.fields = [f] := by
      have h := w.hnpar; rw [hnp, hctorM] at h
      have h0 : piCount natSuccMember.mtype = 1 := rfl
      rw [h0] at h; simp only [Nat.zero_add] at h
      generalize hfg : w.fields = fg
      rw [hfg] at h
      rcases fg with _ | ⟨f, _ | ⟨f', fs⟩⟩
      · simp at h
      · exact ⟨f, rfl⟩
      · simp only [List.length_cons] at h; exact False.elim (by omega)
    have hcd : w.ctorDoms = [.const 0 []] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_cons, List.length_nil, Nat.add_zero, peelPis] at h
      injection h with hp; injection hp with h1 h2; exact h1.symm
    have hcr : w.ctorResult = .const 0 [] := by
      have h := w.hpeel; rw [hnp, hfields, hctorM] at h
      simp only [List.length_cons, List.length_nil, Nat.add_zero, peelPis] at h
      injection h with hp; injection hp with h1 h2; exact h2.symm
    have hlen4 : (w.preMajor ++ [f]).length = 4 := by
      rw [List.length_append, hpmLen]; rfl
    have hdfo : directFragOne E₀ 8 0 natFamMember.arity 0 0 0
        (.const 0 []) = true := by
      unfold directFragOne
      rw [hnt0]
      rfl
    have hsh : w.shapes = [.recursive 0] := by
      have h := w.hshapes
      rw [hfamR, hfamM, hnp, hni, hcd, List.drop_zero] at h
      have hconc : fieldShapesFuel E₀ 8 0 natFamMember.arity 0 0 0
          [.const 0 []] = some [.recursive 0] := by
        have hfr : ∀ j (hj : j < ([.const 0 []] : List (Expr Nat)).length),
            DirectFieldFrag E₀ 8 0 natFamMember.arity 0 0 (0 + j)
              [.const 0 []][j] := by
          intro j hj
          have hj0 : j = 0 := by
            simp only [List.length_cons, List.length_nil] at hj; omega
          subst hj0
          exact directFragOfCheck hdfo
        rw [fieldShapesFuel_eq_analyzeFields_of_directFrag _ hfr]
        rfl
      exact fieldShapesFuel_agree E₀ h hconc
    have hsc : w.schema = foldApps (.bvar 1)
        [.bvar 0, foldApps (.const 3 [.param 0]) (bvarSpine 4)] := by
      have h := w.hschema
      rw [hrecR, hrecM, hnp, hnM, hni, hctorIdx, hfields, hcd, hcr, hsh] at h
      have hconc : iotaOpenRhs E₀ 8 (.const 3 (canonRecLevels 1))
          (.bvar 1) (preMajorBvars 0 2 0 1) 0 2 [.recursive 0]
          (fieldBvars 1) (lift 0 (1 + 1 + 2 + 0)
            (ctorFieldTelRaw 0 [.const 0 []] (.const 0 []))) =
          some (foldApps (.bvar 1)
            [.bvar 0, foldApps (.const 3 [.param 0]) (bvarSpine 4)]) := by
        unfold iotaOpenRhs
        simp only [iotaArgs]
        have hlt : lift 0 (1 + 1 + 2 + 0) (.const 0 [] : Expr Nat) =
            .const 0 [] := rfl
        rw [hlt]
        have hpt : piTelescopeFuel E₀ 8 (.const 0 []) =
            some ([], .const 0 []) :=
          piTelescopeFuel_of_tailStable _ hnt0 hst0 (by decide)
        rw [hpt]
        rfl
      exact iotaOpenRhs_agree E₀ h hconc
    show iotaWitnessSAnnB E₀ w = true
    unfold iotaWitnessSAnnB
    rw [hfamR, hfamM, hnp, hni, hctorIdx, hcd, List.drop_zero]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · show directFragOne E₀ (domsFuelBound [.const 0 []]) 0
          natFamMember.arity 0 0 0 (.const 0 [] : Expr Nat) &&
        directFragCheck E₀ (domsFuelBound [.const 0 []]) 0
          natFamMember.arity 0 0 (0 + 1) [] = true
      rw [Bool.and_eq_true]; refine ⟨?_, rfl⟩
      unfold directFragOne
      rw [hnt0]
      rfl
    · have happ : applyTel (w.preMajor.take 0)
          (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
          some (.pi (.const 0 []) (.const 0 [])) := by
        rw [hctorM]
        show applyTel (w.preMajor.take 0)
            (instantiateLevels (w.ls.take 0) natSuccMember.mtype) =
          some (.pi (.const 0 []) (.const 0 []))
        rw [List.take_zero]
        rfl
      rw [happ]
      simp only
      rw [hfields, hsh]
      rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rfl
      · obtain ⟨minor, hmin⟩ : ∃ m, w.preMajor[0 + 1 + 1]? = some m :=
          ⟨w.preMajor[2]'(by rw [hpmLen]; decide), List.getElem?_eq_getElem _⟩
        rw [hmin]
        simp only
        rw [decide_eq_true_eq]
        unfold iotaRhsOfS
        rw [hls, hfields, hsc]
        have hIL : instantiateLevels [l]
            (foldApps (.bvar 1)
              [.bvar 0, foldApps (.const 3 [.param 0]) (bvarSpine 4)]) =
          foldApps (.bvar 1)
            [.bvar 0, foldApps (.const 3 [l]) (bvarSpine 4)] := rfl
        rw [hIL, instPrefix_foldApps]
        have hminI : instPrefix (w.preMajor ++ [f]) (.bvar 1) = minor := by
          have hj : 1 < (w.preMajor ++ [f]).length := by
            rw [hlen4]; decide
          have hget : (w.preMajor ++ [f])[(w.preMajor ++ [f]).length - 1 - 1]? =
              some minor := by
            rw [hlen4]
            rw [show ((4 : Nat) - 1 - 1) = 2 from rfl]
            rw [List.getElem?_append_left (by rw [hpmLen]; decide)]
            exact hmin
          exact instPrefix_bvar_lt hj hget
        rw [hminI]
        simp only [List.map_cons, List.map_nil]
        have hfI : instPrefix (w.preMajor ++ [f]) (.bvar 0) = f := by
          have hj : 0 < (w.preMajor ++ [f]).length := by
            rw [hlen4]; decide
          have hget : (w.preMajor ++ [f])[(w.preMajor ++ [f]).length - 1 - 0]? =
              some f := by
            rw [hlen4]
            rw [show ((4 : Nat) - 1 - 0) = 3 from rfl]
            rw [List.getElem?_append_right (Nat.le_of_eq hpmLen)]
            rw [hpmLen, show (3 - 3 : Nat) = 0 from rfl]
            rfl
          exact instPrefix_bvar_lt hj hget
        rw [hfI]
        rw [instPrefix_foldApps, instPrefix_const]
        have hsp : (bvarSpine (w.preMajor ++ [f]).length).map
            (instPrefix (w.preMajor ++ [f])) = w.preMajor ++ [f] :=
          instPrefix_bvarSpine _
        rw [hlen4] at hsp
        rw [hsp]
        rw [hrecR, hnM]
        have hrcf : recCallField (.const 3 [l]) w.preMajor 0 2 f (.const 0 []) =
            foldApps (.const 3 [l]) (w.preMajor ++ [f]) := by
          show foldApps (.const 3 [l])
              (recPrefix w.preMajor 0 2 ++ familyIdx 0 (.const 0 []) ++ [f]) = _
          have hfidx : familyIdx 0 (.const 0 [] : Expr Nat) = [] := rfl
          rw [hfidx]
          have hpre' : recPrefix w.preMajor 0 2 = w.preMajor := by
            show w.preMajor.take (0 + 1 + 2) = w.preMajor
            rw [show (0 + 1 + 2 : Nat) = w.preMajor.length from hpmLen.symm]
            exact List.take_length _
          rw [hpre', List.append_nil]
        have hrhs : rhsArgsS (.const 3 [l]) w.preMajor 0 2 [f] [.recursive 0]
            (.pi (.const 0 []) (.const 0 [])) =
            [f, foldApps (.const 3 [l]) (w.preMajor ++ [f])] := by
          show [f, recCallField (.const 3 [l]) w.preMajor 0 2 f
              (.const 0 [])] = _
          rw [hrcf]
        rw [hrhs]

open Ann in
/-- ann-side: every `IotaWitnessS` over a sub-env of `natEnvU` passes
`iotaWitnessSAnnB`. -/
theorem corrAnnCert_sub_natEnvU {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ natEnvU) : EnvCorrAnnCert E₀ := by
  intro w
  obtain ⟨⟨hfamR, hfamM⟩, hctorD, ⟨hrecR, hrecM⟩⟩ :=
    natEnvU_witness_refs hsub w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
  exact natAnnCert_of_refs w hfamR hfamM hctorD hrecR hrecM

open Ann in
/-- `natEnvU` discharges: both certificates at every sub-environment. -/
theorem corrCertsBelow_natEnvU : CorrCertsBelow natEnvU :=
  fun _E₀ hsub => ⟨corrEraseCert_sub_natEnvU hsub, corrAnnCert_sub_natEnvU hsub⟩

/-! ## (5) the bridge at Nat -/

open Ann in
/-- the environment bridge applies at Nat: conditional on arc D's two typings, like the bridge. -/
theorem natEnvU_annotated (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) :
    ∃ EA : ResolvedEnvA, eraseEnv EA = natEnvU ∧ AnnEnvA EA :=
  (annEnvA_of_envWfT_inScope hT1 hT2 natEnvUWfT natEnvUWfT_inScope).imp fun _ h => ⟨h.1, h.2.1⟩

/-! ## (6) O1-a: `False`, a `Prop` family without constructors -/

/-- `Sort 0` is `Prop` at every valuation. -/
theorem falseSort_prop : UniformProp .zero := fun _ => rfl

/-- `False : Sort 0`: no parameter, no index, no constructor. -/
def falseFamMember : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩

/-- the family alone. -/
def falsePrefix : ResolvedEnv := extendEnv emptyEnv 0 falseFamMember

/-- L-K1's family view, wherever the family is present. -/
def falseFamilyView (E : ResolvedEnv) (h : E.members 0 = some falseFamMember) : PolicyFamilyView E where
  ref := 0
  member := falseFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

/-- the recursor's type, `Π (motive : False → Sort u) (t : False), motive t`, as L-K1's policy
    builds it (`falseGroupAdmitted.recursorType := rfl`). -/
def falseRecTypeU : Expr Nat :=
  .pi (.pi (.const 0 []) (.sort (.param 0))) (.pi (.const 0 []) (.app (.bvar 1) (.bvar 0)))

def falseRecMemberU : CheckedMember := ⟨.recursorM, 1, falseRecTypeU, none⟩

def falseEnvU : ResolvedEnv := extendEnv falsePrefix 1 falseRecMemberU

def falseFamAdmitted : IndGroupAdmitted emptyEnv 0 falseFamMember :=
  .family rfl (falseFamilyView falsePrefix rfl) rfl rfl (Or.inl falseSort_prop)

/-- L-K1's recursor admission: no constructor, no minor, AnySort by `EliminationSelection.emptyProp`
    (the selection L-K1's `el03_pin` makes for this shape). -/
def falseGroupAdmitted : RecursorEliminationAdmitted falsePrefix 1 falseRecMemberU where
  family := falseFamilyView falsePrefix rfl
  constructors := []
  constructorViews := fun i => i.elim0
  constructorsPresent := fun i => i.elim0
  recursorRef := rfl
  minorTypes := []
  minorCount := rfl
  policy := .anySort
  selected := .emptyProp falseSort_prop rfl
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem falseCensus : CtorCensus falsePrefix 0 1 := by
  refine ⟨by decide, fun c => ⟨?_, fun h => absurd h (by omega)⟩⟩
  rintro ⟨cm, hc, hk, _⟩
  by_cases h0 : c = 0
  · subst h0
    cases hc
    cases hk
  · simp [falsePrefix, extendEnv, emptyEnv, h0] at hc

def falseIotaClause : IotaDescriptorClause falsePrefix falseGroupAdmitted where
  signatureOnly := rfl
  shapesAt := fun i => i.elim0
  fuelAt := fun i => i.elim0
  analyzed := fun i => i.elim0
  typed := fun i => i.elim0

def falseGroupRecursor : IndGroupAdmitted falsePrefix 1 falseRecMemberU :=
  .recursor falseGroupAdmitted rfl falseCensus (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    falseIotaClause

def falseURecAdmitted : RecursorGroupIdxAdmitted falsePrefix 1 falseRecMemberU :=
  .ofAdmitted rfl

/-- `False : Sort 0`, wherever the family is present. -/
def falseConstTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h : E.members 0 = some falseFamMember) :
    HasTyT E n Γ (.const 0 []) (.sort .zero) :=
  .const Γ 0 [] falseFamMember h rfl rfl

/-- the recursor type's sort: one `imax` per binder. -/
abbrev falseRecSortU : Level :=
  .imax (.imax .zero (.succ (.param 0))) (.imax .zero (.param 0))

/-- `falseRecTypeU` typed in the derivation scope at one level parameter. -/
def falseRecTypeUTyT : HasTyT falsePrefix 1 [] falseRecTypeU (.sort falseRecSortU) :=
  .pi _ _ _ _ _ (.pi _ _ _ _ _ (falseConstTyT rfl) (.sort _ (.param 0)))
    (.pi _ _ _ _ _ (falseConstTyT rfl)
      (.app _ (.bvar 1) (.bvar 0) (.const 0 []) (.sort (.param 0)) (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl)))

theorem falseFamTyped : IndGroupTypedT falseFamAdmitted := fun i => i.elim0

theorem falseRecTyped : IndGroupTypedT falseGroupRecursor :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

def falseMembersT :
    GroupMembersT (extendEnv emptyEnv 0 falseFamMember) emptyEnv [(0, falseFamMember), (1, falseRecMemberU)]
      falseEnvU :=
  .cons _ 0 falseFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    falseFamAdmitted PUnit.unit _ (.sort [] .zero) (fun h => absurd h (by decide))
    falseFamTyped
    (.cons _ 1 falseRecMemberU _ _ rfl rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl rfl
      falseGroupRecursor (.ofCheck _ _ (by with_unfolding_all rfl)) _ falseRecTypeUTyT (fun h => absurd h (by decide))
      falseRecTyped (.nil _))

/-- `False` and its recursor: ONE group step of the typed environment judgment, with no constructor. -/
def falseEnvUWfT : EnvWfT falseEnvU :=
  .group emptyEnv 0 falseFamMember [] 1 falseRecMemberU falseEnvU .empty rfl (fun c hc => by simp at hc) rfl
    falseMembersT

/-- the structured views: `False : Sort 0`, a `Prop` family. -/
def falseFamViewT : FamViewT falseFamMember where
  params := []
  indices := []
  sort := .zero
  stored := rfl
  profile := Or.inl falseSort_prop

def falseCsT : List (GroupCtorT emptyEnv 0 falseFamMember falseFamViewT) := []

/-- the recursor: AnySort, its stored type the one built from the views. -/
def falseRecT : GroupRecT emptyEnv 0 falseFamMember falseFamViewT falseCsT where
  member := falseRecMemberU
  hcls := rfl
  hnobody := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := fun _ => rfl
  u := falseRecSortU
  hT := falseRecTypeUTyT
  hlvl := rfl

def falseInScopeT : GroupInScopeT emptyEnv 0 falseFamMember [] 1 falseRecMemberU where
  fv := falseFamViewT
  htel := .nil []
  cs := falseCsT
  hctors := rfl
  hlayout := rfl
  grec := falseRecT
  hrr := rfl
  hrm := rfl
  hprof := ⟨fun v hv => (List.not_mem_nil v hv).elim, fun _ h => absurd rfl h⟩
  hpb := by decide
  hsnd := by decide

theorem falseEnvUWfT_inScope : falseEnvUWfT.InScope := ⟨trivial, ⟨falseInScopeT⟩⟩

theorem falseEnvU_ctor_free {r : Nat} {m : CheckedMember}
    (h : falseEnvU.members r = some m) : m.mclass ≠ .constructorM := by
  have h' : (if r = 1 then some falseRecMemberU else
      if r = 0 then some falseFamMember else none) = some m := h
  split at h'
  · injection h' with e
    rw [← e]
    decide
  · split at h'
    · injection h' with e
      rw [← e]
      decide
    · exact Option.noConfusion h'

/-- Both ι-correspondence certificates hold vacuously below `falseEnvU`: every
sub-environment is constructor-free, so no `IotaWitness`/`IotaWitnessS` exists.
This is the discharge shape ctor-free environments get for free; ctor-ful
environments still owe the schema-instance lemma for the rhs-check conjunct. -/
theorem corrCertsBelow_falseEnvU : Ann.CorrCertsBelow falseEnvU := fun _E₀ hsub =>
  ⟨fun w => absurd w.hctorK (falseEnvU_ctor_free (hsub _ _ w.hctor)),
   fun w => absurd w.hctorK (falseEnvU_ctor_free (hsub _ _ w.hctor))⟩


/-- TOOTH: O1 before O1-a — every `Prop` family's recursor PropOnly — fails at `False`. -/
theorem false_O1_before : ¬ (UniformProp falseFamViewT.sort → falseRecT.elim = .propOnly) := by
  intro h
  have := h falseSort_prop
  cases this

open Ann in
theorem falseEnvU_annotated (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) :
    ∃ EA : ResolvedEnvA, eraseEnv EA = falseEnvU ∧ AnnEnvA EA :=
  (annEnvA_of_envWfT_inScope hT1 hT2 falseEnvUWfT falseEnvUWfT_inScope).imp fun _ h => ⟨h.1, h.2.1⟩

/-! ## (7) O1-b-2: `True`, a unit group -/

/-- `True : Sort 0`: no parameter, no index. -/
def trueFamMember : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
/-- `intro : True`: no field. -/
def trueIntroMember : CheckedMember := ⟨.constructorM, 0, .const 0 [], none⟩

/-- the family alone, then with its constructor. -/
def trueFamOnly : ResolvedEnv := extendEnv emptyEnv 0 trueFamMember
def truePrefix : ResolvedEnv := extendEnv trueFamOnly 1 trueIntroMember

theorem trueFamOnly_members (c : Nat) :
    trueFamOnly.members c = if c = 0 then some trueFamMember else none := rfl

theorem truePrefix_members (c : Nat) :
    truePrefix.members c =
      if c = 1 then some trueIntroMember else if c = 0 then some trueFamMember else none := rfl

/-- L-K1's family view, wherever the family is present. -/
def trueFamilyView (E : ResolvedEnv) (h : E.members 0 = some trueFamMember) : PolicyFamilyView E where
  ref := 0
  member := trueFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

/-- L-K1's constructor view of `intro`: no parameter, no field, no result index. -/
def trueIntroView (E : ResolvedEnv) (h : E.members 0 = some trueFamMember) :
    PolicyConstructorView E (trueFamilyView E h) trueIntroMember where
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

/-- a constructor of a family `fm` at `0`, admitted right after it: there is no recursor yet. -/
theorem ctorBefore_famOnly {fm : CheckedMember} (hfm : fm.mclass = .inductiveM) {m : CheckedMember}
    (hf : memberFamRef m = some 0) : CtorBeforeRecursors (extendEnv emptyEnv 0 fm) m := by
  refine ⟨0, hf, ?_⟩
  intro rr rm hm hk _
  have hmem : (extendEnv emptyEnv 0 fm).members rr = if rr = 0 then some fm else none := rfl
  rw [hmem] at hm
  by_cases h0 : rr = 0
  · rw [if_pos h0] at hm
    cases hm
    rw [hfm] at hk
    cases hk
  · rw [if_neg h0] at hm
    cases hm

/-- the same constructor at `1` is contiguous: the family alone precedes it. -/
theorem ctorContig_famOnly {fm : CheckedMember} (hfm : fm.mclass = .inductiveM) {m : CheckedMember}
    (hf : memberFamRef m = some 0) : CtorContiguous (extendEnv emptyEnv 0 fm) 1 m := by
  refine ⟨0, hf, by decide, ?_, ?_⟩
  · intro c hl hr
    exact False.elim (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hl (Nat.le_of_lt_succ hr)))
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    have hmem : (extendEnv emptyEnv 0 fm).members c = if c = 0 then some fm else none := rfl
    rw [hmem] at hm
    by_cases h0 : c = 0
    · rw [if_pos h0] at hm
      cases hm
      rw [hfm] at hc
      cases hc
    · rw [if_neg h0] at hm
      cases hm

/-- the family `fm` at `0` with one constructor `m` at `1`: the constructors are exactly those below
    the recursor at `2`. -/
theorem census_famOne {fm : CheckedMember} (hfm : fm.mclass = .inductiveM) {m : CheckedMember}
    (hk : m.mclass = .constructorM) (hf : memberFamRef m = some 0) :
    CtorCensus (extendEnv (extendEnv emptyEnv 0 fm) 1 m) 0 2 := by
  refine ⟨by decide, fun c => ?_⟩
  have hmem : (extendEnv (extendEnv emptyEnv 0 fm) 1 m).members c =
      if c = 1 then some m else if c = 0 then some fm else none := rfl
  constructor
  · rintro ⟨cm, hc, hk', _⟩
    rw [hmem] at hc
    by_cases h1 : c = 1
    · exact ⟨by omega, by omega⟩
    · by_cases h0 : c = 0
      · rw [if_neg h1, if_pos h0] at hc
        cases hc
        rw [hfm] at hk'
        cases hk'
      · rw [if_neg h1, if_neg h0] at hc
        cases hc
  · intro h
    have hc : c = 1 := by omega
    subst hc
    exact ⟨m, rfl, hk, hf⟩

theorem trueIntroBefore : CtorBeforeRecursors trueFamOnly trueIntroMember := ctorBefore_famOnly rfl rfl

theorem trueIntroContig : CtorContiguous trueFamOnly 1 trueIntroMember := ctorContig_famOnly rfl rfl

def trueFamAdmitted : IndGroupAdmitted emptyEnv 0 trueFamMember :=
  .family rfl (trueFamilyView trueFamOnly rfl) rfl rfl (Or.inl falseSort_prop)

def trueIntroAdmitted : IndGroupAdmitted trueFamOnly 1 trueIntroMember :=
  .constructor (trueFamilyView trueFamOnly rfl) (trueIntroView trueFamOnly rfl)
    rfl trueIntroBefore trueIntroContig (fun j => j.elim0) (fun j => j.elim0)

/-- the recursor's type, `Π (motive : True → Sort u) (m : motive intro) (t : True), motive t`, as
    L-K1's policy builds it (`trueGroupAdmitted.recursorType := rfl`). -/
def trueRecTypeU : Expr Nat :=
  .pi (.pi (.const 0 []) (.sort (.param 0)))
    (.pi (.app (.bvar 0) (.const 1 [])) (.pi (.const 0 []) (.app (.bvar 2) (.bvar 0))))

def trueRecMemberU : CheckedMember := ⟨.recursorM, 1, trueRecTypeU, none⟩

def trueEnvU : ResolvedEnv := extendEnv truePrefix 2 trueRecMemberU

/-- L-K1's recursor admission: one constructor without fields, one minor, AnySort by
    `EliminationSelection.singletonProp` (the selection L-K1's `el05_pin` makes for this shape). -/
def trueGroupAdmitted : RecursorEliminationAdmitted truePrefix 2 trueRecMemberU where
  family := trueFamilyView truePrefix rfl
  constructors := [trueIntroMember]
  constructorViews
    | ⟨0, _⟩ => trueIntroView truePrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [.app (.bvar 0) (.const 1 [])]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp falseSort_prop rfl (fun ⟨0, _⟩ j => j.elim0)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl


theorem trueCensus : CtorCensus truePrefix 0 2 := census_famOne rfl rfl rfl

theorem trueMinorMatch : MinorPremisesMatch trueGroupAdmitted := by
  intro i
  have hlt : i.val < 1 := i.isLt
  have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp hlt)
  rw [hi]
  exact ⟨[], 0, rfl, rfl⟩

/-- the ι equation at `intro`: `rec M m intro ⇝ m`, the minor at `bvar 0` under `M` and `m`. -/
def trueIntroCtx : LCtx := [.assumption (.app (.bvar 0) (.const 1 [])), .assumption (.pi (.const 0 []) (.sort (.param 0)))]

def trueIntroIotaTy : HasTy trueEnvU 1 trueIntroCtx (.bvar 0) (.app (.bvar 1) (.const 1 [])) :=
  HasTy.bvar trueIntroCtx 0 _ rfl

def trueIotaIntro : IotaEquationTyped trueGroupAdmitted ⟨0, by decide⟩ 0 [] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact trueIntroIotaTy

def trueShapes : Fin trueGroupAdmitted.constructors.length → List FieldShape
  | ⟨0, _⟩ => []

def trueIotaClause : IotaDescriptorClause truePrefix trueGroupAdmitted where
  signatureOnly := rfl
  shapesAt := trueShapes
  fuelAt := fun _ => 0
  analyzed := by
    intro i
    have hlt : i.val < 1 := i.isLt
    have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp hlt)
    rw [hi]
    rfl
  typed := fun i => by
    have hlt : i.val < 1 := i.isLt
    have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp hlt)
    simpa [hi, trueShapes] using trueIotaIntro

def trueGroupRecursor : IndGroupAdmitted truePrefix 2 trueRecMemberU :=
  .recursor trueGroupAdmitted rfl trueCensus
    (by
      intro i
      have hlt : i.val < 1 := i.isLt
      have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp hlt)
      rw [hi]
      exact fun j => j.elim0)
    (by
      intro i
      have hlt : i.val < 1 := i.isLt
      have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp hlt)
      rw [hi]
      exact fun j => j.elim0)
    trueMinorMatch trueIotaClause

def trueURecAdmitted : RecursorGroupIdxAdmitted truePrefix 2 trueRecMemberU :=
  .ofAdmitted rfl


/-- `True : Sort 0`, wherever the family is present. -/
def trueConstTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h : E.members 0 = some trueFamMember) :
    HasTyT E n Γ (.const 0 []) (.sort .zero) :=
  .const Γ 0 [] trueFamMember h rfl rfl

/-- the recursor type's sort: one `imax` per binder. -/
abbrev trueRecSortU : Level :=
  .imax (.imax .zero (.succ (.param 0))) (.imax (.param 0) (.imax .zero (.param 0)))

/-- `trueRecTypeU` typed in the derivation scope at one level parameter, with `intro` present. -/
def trueRecTypeUTyT : HasTyT truePrefix 1 [] trueRecTypeU (.sort trueRecSortU) :=
  .pi _ _ _ _ _ (.pi _ _ _ _ _ (trueConstTyT rfl) (.sort _ (.param 0)))
    (.pi _ _ _ _ _
      (.app _ (.bvar 0) (.const 1 []) (.const 0 []) (.sort (.param 0)) (.bvar _ 0 _ rfl)
        (.const _ 1 [] trueIntroMember rfl rfl rfl))
      (.pi _ _ _ _ _ (trueConstTyT rfl)
        (.app _ (.bvar 2) (.bvar 0) (.const 0 []) (.sort (.param 0)) (.bvar _ 2 _ rfl) (.bvar _ 0 _ rfl))))

theorem trueFamTyped : IndGroupTypedT trueFamAdmitted := fun i => i.elim0

theorem trueIntroTyped : IndGroupTypedT trueIntroAdmitted :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem trueRecTyped : IndGroupTypedT trueGroupRecursor := by
  refine ⟨fun i => i.elim0, fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ => ?_⟩
  · rcases i with _ | k
    · exact ⟨fun j => j.elim0, fun j => j.elim0⟩
    · exact absurd hi (by simp [trueGroupAdmitted])
  · rcases i with _ | k
    · exact iotaEquationTypedT_of_check (synCheck _ _) rfl
    · exact absurd hi (by simp [trueGroupAdmitted])

/-- L-K1's checks, member by member, each member's stored type typed in the group built so far;
    `intro` also in ConstructorScope, `True` alone (05 §4). -/
def trueMembersT :
    GroupMembersT (extendEnv emptyEnv 0 trueFamMember) emptyEnv
      [(0, trueFamMember), (1, trueIntroMember), (2, trueRecMemberU)] trueEnvU :=
  .cons _ 0 trueFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    trueFamAdmitted PUnit.unit _ (.sort [] .zero) (fun h => absurd h (by decide))
    trueFamTyped
    (.cons _ 1 trueIntroMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      trueIntroAdmitted PUnit.unit _ (trueConstTyT rfl) (fun _ => ⟨trueConstTyT rfl⟩)
      trueIntroTyped
      (.cons _ 2 trueRecMemberU _ _ rfl rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl rfl
        trueGroupRecursor (.ofCheck _ _ (by with_unfolding_all rfl)) _ trueRecTypeUTyT (fun h => absurd h (by decide))
        trueRecTyped (.nil _)))

/-- `True`, `intro` and the recursor: ONE group step of the typed environment judgment. -/
def trueEnvUWfT : EnvWfT trueEnvU :=
  .group emptyEnv 0 trueFamMember [(1, trueIntroMember)] 2 trueRecMemberU trueEnvU .empty rfl
    (fun c hc => by simp at hc; subst hc; rfl) rfl trueMembersT

/-- the structured views: `True : Sort 0`, a `Prop` family. -/
def trueFamViewT : FamViewT trueFamMember where
  params := []
  indices := []
  sort := .zero
  stored := rfl
  profile := Or.inl falseSort_prop

/-- `intro : True`: no field. -/
def trueIntroCtorT : GroupCtorT emptyEnv 0 trueFamMember trueFamViewT where
  ref := 1
  member := trueIntroMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := .zero
  hT := trueConstTyT rfl
  hlvl := rfl
  view :=
    { mirrors := []
      fields := []
      res := []
      stored := rfl
      mirrorsConv := .nil []
      typed := .nil [] 0 [] (.nil .zero)
      univ := fun _ _ h => (List.not_mem_nil _ h).elim
      drecD_typed := drecDTypedT_of_absent (by decide) }

def trueCsT : List (GroupCtorT emptyEnv 0 trueFamMember trueFamViewT) := [trueIntroCtorT]

/-- the recursor: AnySort, its stored type the one built from the views. -/
def trueRecT : GroupRecT emptyEnv 0 trueFamMember trueFamViewT trueCsT where
  member := trueRecMemberU
  hcls := rfl
  hnobody := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := fun _ => rfl
  u := trueRecSortU
  hT := trueRecTypeUTyT
  hlvl := rfl

/-- `True` is a unit group on the typed views. -/
theorem trueUnitT : UnitGroupT trueCsT :=
  ⟨rfl, rfl, fun c hc => by simp only [trueCsT, List.mem_singleton] at hc; subst hc; rfl⟩

def trueInScopeT : GroupInScopeT emptyEnv 0 trueFamMember [(1, trueIntroMember)] 2 trueRecMemberU where
  fv := trueFamViewT
  htel := .nil []
  cs := trueCsT
  hctors := rfl
  hlayout := rfl
  grec := trueRecT
  hrr := rfl
  hrm := rfl
  hprof := ⟨fun v hv => (List.not_mem_nil v hv).elim, fun _ _ hU => absurd trueUnitT hU⟩
  hpb := by decide
  hsnd := by decide

theorem trueEnvUWfT_inScope : trueEnvUWfT.InScope := ⟨trivial, ⟨trueInScopeT⟩⟩

/-- TOOTH: (O1) before O1-b-2 — a `Prop` family with a constructor eliminates into `Prop` only — fails
    at `True`. -/
theorem true_O1_before :
    ¬ (UniformProp trueFamViewT.sort → trueCsT ≠ [] → trueRecT.elim = .propOnly) := by
  intro h
  have := h falseSort_prop (List.cons_ne_nil _ _)
  cases this

open Ann in
/-! ### the ι-correspondence certificates at `trueEnvU`

The unit-group discharge: `intro` has no fields, so the DIRECT fragment is
empty and the whole certificate is the member inversion plus the decided
schema equality `instPrefix w.preMajor (.bvar 0) = w.minor`. -/

open Ann in
/-- member inversion for `trueEnvU`: any present member is one of the
three group members. -/
theorem trueEnvU_mem {c : Nat} {m : CheckedMember}
    (h : trueEnvU.members c = some m) :
    (c = 0 ∧ m = trueFamMember) ∨ (c = 1 ∧ m = trueIntroMember) ∨
      (c = 2 ∧ m = trueRecMemberU) := by
  have hmem : trueEnvU.members c =
      (if c = 2 then some trueRecMemberU
       else if c = 1 then some trueIntroMember
       else if c = 0 then some trueFamMember else none) := rfl
  rw [hmem] at h
  by_cases h2 : c = 2
  · rw [if_pos h2] at h; cases h; exact Or.inr (Or.inr ⟨h2, rfl⟩)
  · rw [if_neg h2] at h
    by_cases h1 : c = 1
    · rw [if_pos h1] at h; cases h; exact Or.inr (Or.inl ⟨h1, rfl⟩)
    · rw [if_neg h1] at h
      by_cases h0 : c = 0
      · rw [if_pos h0] at h; cases h; exact Or.inl ⟨h0, rfl⟩
      · rw [if_neg h0] at h; exact Option.noConfusion h

open Ann in
/-- erase-side: every `IotaWitness` over a sub-env of `trueEnvU` adapts. -/
theorem corrEraseCert_sub_trueEnvU {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ trueEnvU) : EnvCorrEraseCert E₀ := by
  intro w
  -- member enumeration: the three witness refs are pinned to the group.
  obtain ⟨hfamR, hfamM⟩ : w.familyRef = 0 ∧ w.famMember = trueFamMember := by
    rcases trueEnvU_mem (hsub _ _ w.hfam) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · exact ⟨hr, hm⟩
    · have hk := w.hfamK; rw [hm] at hk; exact absurd hk (by decide)
    · have hk := w.hfamK; rw [hm] at hk; exact absurd hk (by decide)
  obtain ⟨hctorR, hctorM⟩ : w.ctorRef = 1 ∧ w.ctorMember = trueIntroMember := by
    rcases trueEnvU_mem (hsub _ _ w.hctor) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · have hk := w.hctorK; rw [hm] at hk; exact absurd hk (by decide)
    · exact ⟨hr, hm⟩
    · have hk := w.hctorK; rw [hm] at hk; exact absurd hk (by decide)
  obtain ⟨hrecR, hrecM⟩ : w.recRef = 2 ∧ w.recMember = trueRecMemberU := by
    rcases trueEnvU_mem (hsub _ _ w.hrec) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · have hk := w.hrecK; rw [hm] at hk; exact absurd hk (by decide)
    · have hk := w.hrecK; rw [hm] at hk; exact absurd hk (by decide)
    · exact ⟨hr, hm⟩
  -- scalar pins
  have hctorIdx : w.ctorIdx = 0 := by
    have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hnp0 : w.nparams + w.nindices = 0 := by
    have h := w.hnidx; rw [hfamM] at h
    have h0 : piCount trueFamMember.mtype = 0 := rfl
    rw [h0] at h; omega
  have hnp : w.nparams = 0 := by omega
  have hni : w.nindices = 0 := by omega
  have hfields : w.fields = [] := by
    have h := w.hnpar; rw [hnp, hctorM] at h
    have h0 : piCount trueIntroMember.mtype = 0 := rfl
    rw [h0] at h; simp only [Nat.zero_add] at h
    exact List.length_eq_zero.mp h
  have hcd : w.ctorDoms = [] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    simp only [List.length_nil, Nat.add_zero, peelPis] at h
    injection h with hp; injection hp with h1 h2; exact h1.symm
  have hcr : w.ctorResult = .const 0 [] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    simp only [List.length_nil, Nat.add_zero, peelPis] at h
    injection h with hp; injection hp with h1 h2; exact h2.symm
  have hkinds : w.kinds = [] := by
    have h := w.hkinds; rw [hfamR, hcd, hnp] at h
    simp only [List.drop_nil, analyzeFields] at h
    injection h with h'; exact h'.symm
  obtain ⟨l, hls⟩ : ∃ l, w.ls = [l] := by
    have h := w.hlsLen; rw [hrecM] at h
    have h1 : trueRecMemberU.arity = 1 := rfl
    rw [h1] at h
    generalize hlg : w.ls = lsg
    rw [hlg] at h
    rcases lsg with _ | ⟨l, _ | ⟨l', ls⟩⟩
    · simp at h
    · exact ⟨l, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hctorAfter : w.ctorAfterParams = .const 0 [] := by
    have h := w.hctorAfter; rw [hnp, hctorM] at h
    simp only [List.take_zero, applyTel] at h
    injection h with h'; exact h'.symm
  have hmem0 : E₀.members 0 = some trueFamMember := by
    have h := w.hfam; rwa [hfamR, hfamM] at h
  -- the recognizer, conjunct by conjunct
  refine ⟨8, ?_⟩
  show iotaWitnessSB w 8 = true
  unfold iotaWitnessSB
  rw [hfamR, hfamM, hnp, hni, hnM, hfields, hcd, hcr]
  rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
  · rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · rfl
    · unfold iotaWitnessStableB ctorFieldTelRaw
      simp only [List.drop_nil, List.foldr_nil, fieldBvars,
        List.range_zero, List.reverse_nil, List.map_nil, List.all_nil]
      show constsMemberFuel E₀ (8 + 1) (lift 0 (0 + 1 + 1 + 0) (.const 0 [])) = true
      have htl : lift 0 (0 + 1 + 1 + 0) (.const 0 [] : Expr Nat) = .const 0 [] := rfl
      rw [htl]
      unfold constsMemberFuel
      rw [hmem0]
      rfl
  · have hschema : iotaSchemaS w 8 = some (.bvar 0) := by
      show iotaOpenRhs E₀ 8
          (.const w.recRef (canonRecLevels w.recMember.arity))
          (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors (w.kinds.map shapeOfKind)
          (fieldBvars w.fields.length)
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
        some (.bvar 0)
      rw [hrecR, hrecM, hnp, hni, hnM, hctorIdx, hfields, hcd, hcr, hkinds]
      rfl
    rw [hschema]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · rfl
    · rw [decide_eq_true_eq]
      rw [hls, List.append_nil]
      show instPrefix w.preMajor (instantiateLevels [l] (.bvar 0)) =
        iotaRhsOf w
      have hinst : instPrefix w.preMajor (.bvar 0) = w.minor := by
        apply instPrefix_bvar_lt
        · have h := w.hpre; rw [hnp, hnM, hni] at h; omega
        · have h := w.hminor; rw [hnp, hctorIdx] at h
          have hlen : w.preMajor.length = 2 := by
            have h2 := w.hpre; rw [hnp, hnM, hni] at h2; omega
          rw [hlen]; exact h
      rw [show instantiateLevels [l] (.bvar 0) = (.bvar 0 : Expr Nat) from rfl,
        hinst]
      unfold iotaRhsOf
      rw [hrecR, hls, hnp, hnM, hfields, hkinds, hctorAfter]
      rfl

open Ann in
/-- ann-side: every `IotaWitnessS` over a sub-env of `trueEnvU` passes
`iotaWitnessSAnnB`. -/
theorem corrAnnCert_sub_trueEnvU {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ trueEnvU) : EnvCorrAnnCert E₀ := by
  intro w
  obtain ⟨hfamR, hfamM⟩ : w.familyRef = 0 ∧ w.famMember = trueFamMember := by
    rcases trueEnvU_mem (hsub _ _ w.hfam) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · exact ⟨hr, hm⟩
    · have hk := w.hfamK; rw [hm] at hk; exact absurd hk (by decide)
    · have hk := w.hfamK; rw [hm] at hk; exact absurd hk (by decide)
  obtain ⟨hctorR, hctorM⟩ : w.ctorRef = 1 ∧ w.ctorMember = trueIntroMember := by
    rcases trueEnvU_mem (hsub _ _ w.hctor) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · have hk := w.hctorK; rw [hm] at hk; exact absurd hk (by decide)
    · exact ⟨hr, hm⟩
    · have hk := w.hctorK; rw [hm] at hk; exact absurd hk (by decide)
  obtain ⟨hrecR, hrecM⟩ : w.recRef = 2 ∧ w.recMember = trueRecMemberU := by
    rcases trueEnvU_mem (hsub _ _ w.hrec) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · have hk := w.hrecK; rw [hm] at hk; exact absurd hk (by decide)
    · have hk := w.hrecK; rw [hm] at hk; exact absurd hk (by decide)
    · exact ⟨hr, hm⟩
  have hctorIdx : w.ctorIdx = 0 := by
    have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hnp0 : w.nparams + w.nindices = 0 := by
    have h := w.hnidx; rw [hfamM] at h
    have h0 : piCount trueFamMember.mtype = 0 := rfl
    rw [h0] at h; omega
  have hnp : w.nparams = 0 := by omega
  have hni : w.nindices = 0 := by omega
  have hfields : w.fields = [] := by
    have h := w.hnpar; rw [hnp, hctorM] at h
    have h0 : piCount trueIntroMember.mtype = 0 := rfl
    rw [h0] at h; simp only [Nat.zero_add] at h
    exact List.length_eq_zero.mp h
  have hcd : w.ctorDoms = [] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    simp only [List.length_nil, Nat.add_zero, peelPis] at h
    injection h with hp; injection hp with h1 h2; exact h1.symm
  have hcr : w.ctorResult = .const 0 [] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    simp only [List.length_nil, Nat.add_zero, peelPis] at h
    injection h with hp; injection hp with h1 h2; exact h2.symm
  obtain ⟨l, hls⟩ : ∃ l, w.ls = [l] := by
    have h := w.hlsLen; rw [hrecM] at h
    have h1 : trueRecMemberU.arity = 1 := rfl
    rw [h1] at h
    generalize hlg : w.ls = lsg
    rw [hlg] at h
    rcases lsg with _ | ⟨l, _ | ⟨l', ls⟩⟩
    · simp at h
    · exact ⟨l, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hpmLen : w.preMajor.length = 2 := by
    have h := w.hpre; rw [hnp, hnM, hni] at h; omega
  have hsh : w.shapes = [] := by
    have h := w.hshapes
    rw [hfamR, hfamM, hnp, hni, hcd, List.drop_zero] at h
    exact (Option.some.inj h).symm
  have hsc : w.schema = .bvar 0 := by
    have h := w.hschema
    rw [hrecR, hrecM, hnp, hnM, hni, hctorIdx, hfields, hcd, hcr, hsh] at h
    have hconc : iotaOpenRhs E₀ 8 (.const 2 (canonRecLevels 1))
        (.bvar 0) (preMajorBvars 0 1 0 0) 0 1 []
        (fieldBvars 0) (lift 0 (0 + 1 + 1 + 0)
          (ctorFieldTelRaw 0 [] (.const 0 []))) = some (.bvar 0) := rfl
    exact iotaOpenRhs_agree E₀ h hconc
  show iotaWitnessSAnnB E₀ w = true
  unfold iotaWitnessSAnnB
  rw [hfamR, hfamM, hnp, hni, hctorIdx, hcd, List.drop_zero]
  rw [Bool.and_eq_true]; refine ⟨rfl, ?_⟩
  have happ : applyTel (w.preMajor.take 0)
      (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
      some (.const 0 []) := by
    rw [hctorM]
    show applyTel (w.preMajor.take 0)
        (instantiateLevels (w.ls.take 0) trueIntroMember.mtype) =
      some (.const 0 [])
    rw [List.take_zero]
    rfl
  rw [happ]
  simp only
  rw [hfields, hsh]
  rw [show fieldsTelS ([] : List (Expr Nat)) ([] : List FieldShape)
      (.const 0 []) = true from rfl, Bool.true_and]
  obtain ⟨minor, hmin⟩ : ∃ m, w.preMajor[0 + 1 + 0]? = some m :=
    ⟨w.preMajor[1]'(by rw [hpmLen]; decide), List.getElem?_eq_getElem _⟩
  rw [hmin]
  simp only
  rw [decide_eq_true_eq]
  unfold iotaRhsOfS
  rw [hls, hfields, List.append_nil, hsc]
  rw [show instantiateLevels [l] (.bvar 0) = (.bvar 0 : Expr Nat) from rfl]
  have hminI : instPrefix w.preMajor (.bvar 0) = minor := by
    have hj : 0 < w.preMajor.length := by rw [hpmLen]; decide
    have hget : w.preMajor[w.preMajor.length - 1 - 0]? = some minor := by
      rw [hpmLen]
      rw [show ((2 : Nat) - 1 - 0) = 1 from rfl]
      exact hmin
    exact instPrefix_bvar_lt hj hget
  rw [hminI, hrecR, hnM]
  rfl

open Ann in
/-- `trueEnvU` discharges: both certificates at every sub-environment. -/
theorem corrCertsBelow_trueEnvU : CorrCertsBelow trueEnvU :=
  fun _E₀ hsub => ⟨corrEraseCert_sub_trueEnvU hsub, corrAnnCert_sub_trueEnvU hsub⟩

open Ann in

/-- the environment bridge applies at `True`: conditional on arc D's two typings, like the bridge. -/
theorem trueEnvU_annotated (hT1 : CtorTyOfViewA) (hT2 : RecTyOfViewsA) :
    ∃ EA : ResolvedEnvA, eraseEnv EA = trueEnvU ∧ AnnEnvA EA :=
  (annEnvA_of_envWfT_inScope hT1 hT2 trueEnvUWfT trueEnvUWfT_inScope).imp fun _ h => ⟨h.1, h.2.1⟩

/-! ## (8) W-1 (e-3): `S`, a struct group -/

/-- `S`'s field type, `Π (P : Prop), P → P`: a closed proposition. -/
abbrev structFieldTy : Expr Nat := .pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))
/-- its sort, `imax 1 (imax 0 0)`. -/
abbrev structFieldLv : Level := .imax (.succ .zero) (.imax .zero .zero)

/-- the field's sort is zero at every valuation: the field is a proof. -/
theorem structFieldLv_prop : UniformProp structFieldLv := fun _ => rfl

/-- `mk : (Π (P : Prop), P → P) → S`. `S`'s family is `True`'s member, `Sort 0` without parameter or
    index, so its family view, admission and typing are `True`'s. -/
def structMkMember : CheckedMember := ⟨.constructorM, 0, .pi structFieldTy (.const 0 []), none⟩

/-- the family, then with its constructor. -/
def structPrefix : ResolvedEnv := extendEnv trueFamOnly 1 structMkMember

/-- the field's type in `main`'s judgment, in any context. -/
def structFieldHasTy {E : ResolvedEnv} {n : Nat} (Γ : LCtx) : HasTy E n Γ structFieldTy (.sort structFieldLv) :=
  .pi Γ (.sort .zero) (.succ .zero) (.pi (.bvar 0) (.bvar 1)) (.imax .zero .zero) (.sort Γ .zero)
    (.pi _ (.bvar 0) .zero (.bvar 1) .zero (.bvar _ 0 (.sort .zero) rfl) (.bvar _ 1 (.sort .zero) rfl))

/-- the same in the typed judgment. -/
def structFieldTyT {E : ResolvedEnv} {n : Nat} (Γ : LCtx) : HasTyT E n Γ structFieldTy (.sort structFieldLv) :=
  .pi Γ (.sort .zero) (.succ .zero) (.pi (.bvar 0) (.bvar 1)) (.imax .zero .zero) (.sort Γ .zero)
    (.pi _ (.bvar 0) .zero (.bvar 1) .zero (.bvar _ 0 (.sort .zero) rfl) (.bvar _ 1 (.sort .zero) rfl))

/-- L-K1's constructor view of `mk`: no parameter, one field, no result index. -/
def structMkView (E : ResolvedEnv) (h : E.members 0 = some trueFamMember) :
    PolicyConstructorView E (trueFamilyView E h) structMkMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [structFieldTy]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => structFieldLv
    bounded := fun _ => rfl
    hasType := fun j => by
      match j with
      | ⟨0, _⟩ =>
          simp only [policyPrefixContext]
          exact structFieldHasTy [] }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

/-- the field is non-recursive (L-K1's positivity decider, at fuel 8). -/
theorem structMkFields (E : ResolvedEnv) (h : E.members 0 = some trueFamMember) :
    CtorFieldsPermitted (structMkView E h) := fun j =>
  match j with
  | ⟨0, _⟩ => ⟨.nonrecursive, 8, [], rfl⟩

def structMkAdmitted : IndGroupAdmitted trueFamOnly 1 structMkMember :=
  .constructor (trueFamilyView trueFamOnly rfl) (structMkView trueFamOnly rfl)
    rfl (ctorBefore_famOnly rfl rfl) (ctorContig_famOnly rfl rfl) (fun _ => Or.inl falseSort_prop)
    (structMkFields _ rfl)

/-- the minor premise, `Π (x : Π P, P → P), motive (mk x)`, under the motive. -/
abbrev structMinorTy : Expr Nat := .pi structFieldTy (.app (.bvar 1) (.app (.const 1 []) (.bvar 0)))

/-- the recursor's type, `Π (motive : S → Sort u) (m : Π x, motive (mk x)) (t : S), motive t`, as
    L-K1's policy builds it (`structGroupAdmitted.recursorType := rfl`). -/
def structRecTypeU : Expr Nat :=
  .pi (.pi (.const 0 []) (.sort (.param 0)))
    (.pi structMinorTy (.pi (.const 0 []) (.app (.bvar 2) (.bvar 0))))

def structRecMemberU : CheckedMember := ⟨.recursorM, 1, structRecTypeU, none⟩

def structEnvU : ResolvedEnv := extendEnv structPrefix 2 structRecMemberU

/-- L-K1's recursor admission: one constructor whose field is a proof, AnySort by
    `EliminationSelection.singletonProp`, every field safe (its sort zero at every valuation). -/
def structGroupAdmitted : RecursorEliminationAdmitted structPrefix 2 structRecMemberU where
  family := trueFamilyView structPrefix rfl
  constructors := [structMkMember]
  constructorViews
    | ⟨0, _⟩ => structMkView structPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [structMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp falseSort_prop rfl (fun ⟨0, _⟩ j =>
    match j with
    | ⟨0, _⟩ => Or.inl structFieldLv_prop)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem structMinorMatch : MinorPremisesMatch structGroupAdmitted := by
  intro i
  have hlt : i.val < 1 := i.isLt
  have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp hlt)
  rw [hi]
  exact ⟨[.nonrecursive], 8, rfl, rfl⟩

/-- the ι equation at `mk`: `rec M m (mk x) ⇝ m x`, typed in the context `x, m, M`. -/
def structMkCtx : LCtx :=
  [.assumption structFieldTy, .assumption structMinorTy, .assumption (.pi (.const 0 []) (.sort (.param 0)))]

def structMkIotaTy :
    HasTy structEnvU 1 structMkCtx (.app (.bvar 1) (.bvar 0)) (.app (.bvar 2) (.app (.const 1 []) (.bvar 0))) :=
  HasTy.app structMkCtx (.bvar 1) (.bvar 0) structFieldTy (.app (.bvar 3) (.app (.const 1 []) (.bvar 0)))
    (HasTy.bvar structMkCtx 1 _ rfl) (HasTy.bvar structMkCtx 0 _ rfl)

def structIotaMk : IotaEquationTyped structGroupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact structMkIotaTy

def structShapes : Fin structGroupAdmitted.constructors.length → List FieldShape
  | ⟨0, _⟩ => [.nonrecursive]

def structIotaClause : IotaDescriptorClause structPrefix structGroupAdmitted where
  signatureOnly := rfl
  shapesAt := structShapes
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => structIotaMk

def structRecAdmitted : IndGroupAdmitted structPrefix 2 structRecMemberU :=
  .recursor structGroupAdmitted rfl (census_famOne rfl rfl rfl)
    (fun i => match i with | ⟨0, _⟩ => fun _ => Or.inl falseSort_prop)
    (fun i => match i with | ⟨0, _⟩ => structMkFields _ rfl)
    structMinorMatch structIotaClause

def structURecAdmitted : RecursorGroupIdxAdmitted structPrefix 2 structRecMemberU :=
  .ofAdmitted rfl

/-- `mk`'s stored type typed, wherever the family is present. -/
abbrev structMkSortU : Level := .imax structFieldLv .zero

def structMkTyT {E : ResolvedEnv} (h : E.members 0 = some trueFamMember) :
    HasTyT E 0 [] structMkMember.mtype (.sort structMkSortU) :=
  .pi [] _ _ _ _ (structFieldTyT []) (trueConstTyT h)

/-- the recursor's stored type typed in the derivation scope at one level parameter. -/
def structRecTypeUTyT : Σ u, HasTyT structPrefix 1 [] structRecTypeU (.sort u) :=
  ⟨_, .pi _ _ _ _ _ (.pi _ _ _ _ _ (trueConstTyT rfl) (.sort _ (.param 0)))
    (.pi _ _ _ _ _
      (.pi _ _ _ _ _ (structFieldTyT _)
        (.app _ (.bvar 1) (.app (.const 1 []) (.bvar 0)) (.const 0 []) (.sort (.param 0)) (.bvar _ 1 _ rfl)
          (.app _ (.const 1 []) (.bvar 0) structFieldTy (.const 0 [])
            (.const _ 1 [] structMkMember rfl rfl rfl) (.bvar _ 0 _ rfl))))
      (.pi _ _ _ _ _ (trueConstTyT rfl)
        (.app _ (.bvar 2) (.bvar 0) (.const 0 []) (.sort (.param 0)) (.bvar _ 2 _ rfl) (.bvar _ 0 _ rfl))))⟩

/-- `mk`'s field typed at its recorded sort, wherever the family is present. -/
theorem structMkTypedE (E : ResolvedEnv) (h : E.members 0 = some trueFamMember) :
    CtorTypedT (structMkView E h) :=
  ⟨fun i => match i with | ⟨0, _⟩ => ⟨structFieldTyT []⟩, fun i => i.elim0⟩

theorem structMkTyped : IndGroupTypedT structMkAdmitted := ⟨fun i => i.elim0, structMkTypedE _ rfl⟩

theorem structRecTyped : IndGroupTypedT structRecAdmitted :=
  ⟨fun i => i.elim0, fun i => match i with | ⟨0, _⟩ => structMkTypedE _ rfl,
   fun i => match i with | ⟨0, _⟩ => iotaEquationTypedT_of_check (synCheck _ _) rfl⟩

/-- L-K1's checks, member by member, each member's stored type typed in the group built so far;
    `mk` also in ConstructorScope, `S` alone (05 §4). -/
def structMembersT :
    GroupMembersT (extendEnv emptyEnv 0 trueFamMember) emptyEnv
      [(0, trueFamMember), (1, structMkMember), (2, structRecMemberU)] structEnvU :=
  .cons _ 0 trueFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    trueFamAdmitted PUnit.unit _ (.sort [] .zero) (fun h => absurd h (by decide))
    trueFamTyped
    (.cons _ 1 structMkMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      structMkAdmitted PUnit.unit _ (structMkTyT rfl) (fun _ => ⟨structMkTyT rfl⟩)
      structMkTyped
      (.cons _ 2 structRecMemberU _ _ rfl rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl rfl
        structRecAdmitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ structRecTypeUTyT.2 (fun h => absurd h (by decide))
        structRecTyped (.nil _)))

/-- `S`, `mk` and the recursor: ONE group step of the typed environment judgment. -/
def structEnvUWfT : EnvWfT structEnvU :=
  .group emptyEnv 0 trueFamMember [(1, structMkMember)] 2 structRecMemberU structEnvU .empty rfl
    (fun c hc => by simp at hc; subst hc; rfl) rfl structMembersT

/-- `mk : (Π P, P → P) → S`: one plain field, at a sort zero at every valuation. -/
def structMkCtorT : GroupCtorT emptyEnv 0 trueFamMember trueFamViewT where
  ref := 1
  member := structMkMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := structMkSortU
  hT := structMkTyT rfl
  hlvl := rfl
  view :=
    { mirrors := []
      fields := [.plain structFieldTy structFieldLv]
      res := []
      stored := rfl
      mirrorsConv := .nil []
      typed := .plain [] 0 structFieldTy structFieldLv [] [] (structFieldTyT []) (.nil _ 1 [] (.nil .zero))
      univ := fun _ _ _ => Or.inl falseSort_prop
      drecD_typed := drecDTypedT_of_absent (by decide) }

def structCsT : List (GroupCtorT emptyEnv 0 trueFamMember trueFamViewT) := [structMkCtorT]

/-- the recursor: AnySort, its stored type the one built from the views. -/
def structRecT : GroupRecT emptyEnv 0 trueFamMember trueFamViewT structCsT where
  member := structRecMemberU
  hcls := rfl
  hnobody := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := fun _ => rfl
  u := structRecTypeUTyT.1
  hT := structRecTypeUTyT.2
  hlvl := rfl

/-- `S` is a struct group on the typed views. -/
theorem structStructT : StructGroupT structCsT :=
  ⟨rfl, rfl, fun c hc => by
    simp only [structCsT, List.mem_singleton] at hc
    subst hc
    exact ⟨List.cons_ne_nil _ _, fun F hF => ⟨_, _, List.mem_singleton.mp hF, structFieldLv_prop⟩⟩⟩

def structInScopeT : GroupInScopeT emptyEnv 0 trueFamMember [(1, structMkMember)] 2 structRecMemberU where
  fv := trueFamViewT
  htel := .nil []
  cs := structCsT
  hctors := rfl
  hlayout := rfl
  grec := structRecT
  hrr := rfl
  hrm := rfl
  hprof := ⟨fun v hv => (List.not_mem_nil v hv).elim, fun _ _ _ hS => absurd structStructT hS⟩
  hpb := by decide
  hsnd := by decide

theorem structEnvUWfT_inScope : structEnvUWfT.InScope := ⟨trivial, ⟨structInScopeT⟩⟩

/-- TOOTH: (O1) as it stood before W-1 (e-3) — a `Prop` family with a constructor eliminates into
    `Prop` only, unless it is a unit group — fails at `S`. -/
theorem struct_O1_before :
    ¬ (UniformProp trueFamViewT.sort → structCsT ≠ [] → ¬ UnitGroupT structCsT →
      structRecT.elim = .propOnly) := by
  intro h
  have := h falseSort_prop (List.cons_ne_nil _ _) (fun hU => by
    have hf := hU.2.2 structMkCtorT (List.mem_singleton_self _)
    cases hf)
  cases this

open Ann in
/-! ### the ι-correspondence certificates at `structEnvU`

GAP-B for the `S` group: member inversion pins the three witness references
(family `0`, constructor `1`, recursor `2`), `structFieldTy`'s `.pi`-telescope
and `.const 0 []` result are rigid (`constsMemberFuel`/`noTransparentB`/
`headStableB`), the fields classify identically under `analyzeFields` and
`fieldShapesFuel` (all `.plain`/`.nonrecursive`), plus the schema/RHS equality
computes through `instPrefix_bvar_lt`.  Decided per-witness by
`iotaWitnessSB`/`iotaWitnessSAnnB`. -/

/-! ### shared walk lemmas: all-plain / all-nonrecursive telescopes -/

open Ann in
/-- `rhsArgs` at all-plain fields returns the fields, walking `T`'s Π-spine. -/
theorem rhsArgs_allPlain {rec : Expr Nat} {pm : List (Expr Nat)}
    {np nM : Nat} :
    ∀ (fs : List (Expr Nat)) (T : Expr Nat), isPiTel fs.length T = true →
      rhsArgs rec pm np nM fs (fs.map fun _ => .plain) T = fs := by
  intro fs; induction fs with
  | nil => intro T _; rfl
  | cons f fs ih =>
      intro T h
      rw [List.length_cons] at h
      cases T with
      | pi A B =>
          simp only [isPiTel] at h
          show f :: rhsArgs rec pm np nM fs (fs.map fun _ => .plain)
              (instantiate0 f B) = f :: fs
          rw [ih (instantiate0 f B) (isPiTel_instantiate 0 f _ _ h)]
      | bvar _ => simp only [isPiTel, Bool.false_eq_true] at h
      | sort _ => simp only [isPiTel, Bool.false_eq_true] at h
      | const _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | app _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | lam _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | letE _ _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | lit _ => simp only [isPiTel, Bool.false_eq_true] at h

open Ann in
/-- `rhsArgsS` at all-nonrecursive shapes returns the fields. -/
theorem rhsArgsS_allNonrec {rec : Expr Nat} {pm : List (Expr Nat)}
    {np nM : Nat} :
    ∀ (fs : List (Expr Nat)) (T : Expr Nat), isPiTel fs.length T = true →
      rhsArgsS rec pm np nM fs (fs.map fun _ => .nonrecursive) T = fs := by
  intro fs; induction fs with
  | nil => intro T _; rfl
  | cons f fs ih =>
      intro T h
      rw [List.length_cons] at h
      cases T with
      | pi A B =>
          simp only [isPiTel] at h
          show f :: rhsArgsS rec pm np nM fs (fs.map fun _ => .nonrecursive)
              (instantiate0 f B) = f :: fs
          rw [ih (instantiate0 f B) (isPiTel_instantiate 0 f _ _ h)]
      | bvar _ => simp only [isPiTel, Bool.false_eq_true] at h
      | sort _ => simp only [isPiTel, Bool.false_eq_true] at h
      | const _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | app _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | lam _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | letE _ _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | lit _ => simp only [isPiTel, Bool.false_eq_true] at h

open Ann in
/-- `fieldsTelS` at all-nonrecursive shapes holds on a deep-enough Π
    telescope. -/
theorem fieldsTelS_allNonrec :
    ∀ (fs : List (Expr Nat)) (T : Expr Nat), isPiTel fs.length T = true →
      fieldsTelS fs (fs.map fun _ => .nonrecursive) T = true := by
  intro fs; induction fs with
  | nil => intro T _; rfl
  | cons f fs ih =>
      intro T h
      rw [List.length_cons] at h
      cases T with
      | pi A B =>
          simp only [isPiTel] at h
          show (shapeGuardS A .nonrecursive &&
              fieldsTelS fs (fs.map fun _ => .nonrecursive)
                (instantiate0 f B)) = true
          rw [Bool.and_eq_true]
          exact ⟨rfl, ih (instantiate0 f B)
            (isPiTel_instantiate 0 f _ _ h)⟩
      | bvar _ => simp only [isPiTel, Bool.false_eq_true] at h
      | sort _ => simp only [isPiTel, Bool.false_eq_true] at h
      | const _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | app _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | lam _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | letE _ _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | lit _ => simp only [isPiTel, Bool.false_eq_true] at h

open Ann in
/-- `iotaArgs` at all-nonrecursive shapes returns the field bvars. -/
theorem iotaArgs_allNonrec {E : ResolvedEnv} {fuel : Nat} {rec : Expr Nat}
    {pm : List (Expr Nat)} {np nM : Nat} :
    ∀ (fs : List (Expr Nat)) (T : Expr Nat), isPiTel fs.length T = true →
      iotaArgs E fuel rec pm np nM (fs.map fun _ => .nonrecursive) fs T =
        some fs := by
  intro fs; induction fs with
  | nil => intro T _; rfl
  | cons f fs ih =>
      intro T h
      rw [List.length_cons] at h
      cases T with
      | pi A B =>
          simp only [isPiTel] at h
          show (iotaArgs E fuel rec pm np nM (fs.map fun _ => .nonrecursive)
              fs (instantiate0 f B)).map (fun rest => f :: rest) = some (f :: fs)
          rw [ih (instantiate0 f B) (isPiTel_instantiate 0 f _ _ h)]
          rfl
      | bvar _ => simp only [isPiTel, Bool.false_eq_true] at h
      | sort _ => simp only [isPiTel, Bool.false_eq_true] at h
      | const _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | app _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | lam _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | letE _ _ _ => simp only [isPiTel, Bool.false_eq_true] at h
      | lit _ => simp only [isPiTel, Bool.false_eq_true] at h

/-! ### `S` (`structEnvU`) -/

open Ann in
/-- member inversion for `structEnvU`: family `True` at 0, `mk` at 1, the
    recursor at 2. -/
theorem structEnvU_mem {c : Nat} {m : CheckedMember}
    (h : structEnvU.members c = some m) :
    (c = 0 ∧ m = trueFamMember) ∨ (c = 1 ∧ m = structMkMember) ∨
      (c = 2 ∧ m = structRecMemberU) := by
  have hmem : structEnvU.members c =
      (if c = 2 then some structRecMemberU
       else if c = 1 then some structMkMember
       else if c = 0 then some trueFamMember else none) := rfl
  rw [hmem] at h
  by_cases h2 : c = 2
  · rw [if_pos h2] at h; cases h
    exact Or.inr (Or.inr ⟨h2, rfl⟩)
  · rw [if_neg h2] at h
    by_cases h1 : c = 1
    · rw [if_pos h1] at h; cases h; exact Or.inr (Or.inl ⟨h1, rfl⟩)
    · rw [if_neg h1] at h
      by_cases h0 : c = 0
      · rw [if_pos h0] at h; cases h; exact Or.inl ⟨h0, rfl⟩
      · rw [if_neg h0] at h; exact Option.noConfusion h

open Ann in
/-- `constsMemberFuel` on `True`'s family const, wherever the family is
    present. -/
theorem structEnvU_constsMember {E₀ : ResolvedEnv}
    (hmem0 : E₀.members 0 = some trueFamMember) {fuel : Nat} :
    constsMemberFuel E₀ (fuel + 1) (.const 0 []) = true := by
  cases fuel with
  | zero => unfold constsMemberFuel; rw [hmem0]; rfl
  | succ f => unfold constsMemberFuel; rw [hmem0]; rfl

open Ann in
/-- erase-side: every `IotaWitness` over a sub-env of `structEnvU` adapts. -/
theorem corrEraseCert_sub_structEnvU {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ structEnvU) : EnvCorrEraseCert E₀ := by
  intro w
  obtain ⟨hfamR, hfamM⟩ : w.familyRef = 0 ∧ w.famMember = trueFamMember := by
    rcases structEnvU_mem (hsub _ _ w.hfam) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · exact ⟨hr, hm⟩
    · have hk := w.hfamK; rw [hm] at hk; exact absurd hk (by decide)
    · have hk := w.hfamK; rw [hm] at hk; exact absurd hk (by decide)
  obtain ⟨hctorR, hctorM⟩ : w.ctorRef = 1 ∧ w.ctorMember = structMkMember := by
    rcases structEnvU_mem (hsub _ _ w.hctor) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · have hk := w.hctorK; rw [hm] at hk; exact absurd hk (by decide)
    · exact ⟨hr, hm⟩
    · have hk := w.hctorK; rw [hm] at hk; exact absurd hk (by decide)
  obtain ⟨hrecR, hrecM⟩ : w.recRef = 2 ∧ w.recMember = structRecMemberU := by
    rcases structEnvU_mem (hsub _ _ w.hrec) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · have hk := w.hrecK; rw [hm] at hk; exact absurd hk (by decide)
    · have hk := w.hrecK; rw [hm] at hk; exact absurd hk (by decide)
    · exact ⟨hr, hm⟩
  have hctorIdx : w.ctorIdx = 0 := by
    have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hnp0 : w.nparams + w.nindices = 0 := by
    have h := w.hnidx; rw [hfamM] at h
    have h0 : piCount trueFamMember.mtype = 0 := rfl
    rw [h0] at h; omega
  have hnp : w.nparams = 0 := by omega
  have hni : w.nindices = 0 := by omega
  obtain ⟨f, hfields⟩ : ∃ f, w.fields = [f] := by
    have h := w.hnpar; rw [hnp, hctorM] at h
    have h0 : piCount structMkMember.mtype = 1 := rfl
    rw [h0] at h; simp only [Nat.zero_add] at h
    generalize hfg : w.fields = fg
    rw [hfg] at h
    rcases fg with _ | ⟨f, _ | ⟨f', fs⟩⟩
    · simp at h
    · exact ⟨f, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hcd : w.ctorDoms = [structFieldTy] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    have h0 : peelPis (0 + [f].length) structMkMember.mtype =
        some ([structFieldTy], .const 0 []) := rfl
    rw [h0] at h
    injection h with hp; injection hp with h1 h2; exact h1.symm
  have hcr : w.ctorResult = .const 0 [] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    have h0 : peelPis (0 + [f].length) structMkMember.mtype =
        some ([structFieldTy], .const 0 []) := rfl
    rw [h0] at h
    injection h with hp; injection hp with h1 h2; exact h2.symm
  have hkinds : w.kinds = [.plain] := by
    have h := w.hkinds; rw [hfamR, hcd, hnp] at h
    have ha : analyzeFields 0 ([structFieldTy].drop 0) = some [.plain] := rfl
    rw [ha] at h
    injection h with h'; exact h'.symm
  have hctorAfter : w.ctorAfterParams =
      .pi structFieldTy (.const 0 []) := by
    have h := w.hctorAfter; rw [hnp, hctorM] at h
    simp only [List.take_zero, applyTel] at h
    have hIL : instantiateLevels w.ls structMkMember.mtype =
        .pi structFieldTy (.const 0 []) := rfl
    rw [hIL] at h
    injection h with h'; exact h'.symm
  have hmem0 : E₀.members 0 = some trueFamMember := by
    have h := w.hfam; rwa [hfamR, hfamM] at h
  have hpmLen : w.preMajor.length = 2 := by
    have h := w.hpre; rw [hnp, hnM, hni] at h; omega
  refine ⟨16, ?_⟩
  show iotaWitnessSB w 16 = true
  unfold iotaWitnessSB
  rw [hfamR, hfamM, hnp, hni, hnM, hfields, hcd, hcr]
  rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
  · rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · show directFragCheck E₀ 16 0 trueFamMember.arity 0 0 0
          ([structFieldTy].drop 0) = true
      rw [List.drop_zero]
      show directFragOne E₀ 16 0 trueFamMember.arity 0 0 0 structFieldTy &&
          directFragCheck E₀ 16 0 trueFamMember.arity 0 0 (0 + 1) [] = true
      rw [Bool.and_eq_true]; refine ⟨?_, rfl⟩
      unfold directFragOne
      rfl
    · show iotaWitnessStableB E₀ 16 ([structFieldTy].drop 0)
          (fieldBvars [f].length)
          (lift 0 (1 + 1 + 1 + 0)
            (ctorFieldTelRaw 0 [structFieldTy] (.const 0 []))) = true
      have htl : lift 0 (1 + 1 + 1 + 0)
          (ctorFieldTelRaw 0 [structFieldTy] (.const 0 [])) =
          .pi structFieldTy (.const 0 []) := rfl
      rw [List.drop_zero, htl]
      unfold iotaWitnessStableB
      rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
        · show List.all [structFieldTy]
              (constsMemberFuel E₀ (16 + 1)) = true
          simp only [List.all_cons, List.all_nil, constsMemberFuel,
            Bool.and_true, Bool.true_and]
        · show List.all [.bvar 0] (constsMemberFuel E₀ (16 + 1)) = true
          simp only [List.all_cons, List.all_nil, constsMemberFuel,
            Bool.and_true, Bool.true_and]
      · show constsMemberFuel E₀ (16 + 1)
            (.pi structFieldTy (.const 0 [])) = true
        simp only [constsMemberFuel, hmem0, trueFamMember, transparent,
          Bool.and_true, Bool.true_and]
        rfl
  · have hschema : iotaSchemaS w 16 =
        some (.app (.bvar 1) (.bvar 0)) := by
      show iotaOpenRhs E₀ 16
          (.const w.recRef (canonRecLevels w.recMember.arity))
          (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors (w.kinds.map shapeOfKind)
          (fieldBvars w.fields.length)
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
        some (.app (.bvar 1) (.bvar 0))
      rw [hrecR, hrecM, hnp, hni, hnM, hctorIdx, hfields, hcd, hcr, hkinds]
      have htl : lift 0 ([f].length + 1 + 1 + 0)
          (ctorFieldTelRaw 0 [structFieldTy] (.const 0 [])) =
          .pi structFieldTy (.const 0 []) := rfl
      rw [htl]
      rfl
    rw [hschema]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · rfl
    · rw [decide_eq_true_eq]
      obtain ⟨l, hls⟩ : ∃ l, w.ls = [l] := by
        have h := w.hlsLen; rw [hrecM] at h
        have h1 : structRecMemberU.arity = 1 := rfl
        rw [h1] at h
        generalize hlg : w.ls = lsg
        rw [hlg] at h
        rcases lsg with _ | ⟨l, _ | ⟨l', ls⟩⟩
        · simp at h
        · exact ⟨l, rfl⟩
        · simp only [List.length_cons] at h; exact False.elim (by omega)
      rw [hls]
      have hIL : instantiateLevels [l] (.app (.bvar 1) (.bvar 0)) =
          (.app (.bvar 1) (.bvar 0) : Expr Nat) := rfl
      rw [hIL]
      show instPrefix (w.preMajor ++ [f])
          (foldApps (.bvar 1) [.bvar 0]) = iotaRhsOf w
      rw [instPrefix_foldApps]
      have hlen3 : (w.preMajor ++ [f]).length = 3 := by
        rw [List.length_append, hpmLen]; rfl
      have hminI : instPrefix (w.preMajor ++ [f]) (.bvar 1) = w.minor := by
        have hj : 1 < (w.preMajor ++ [f]).length := by rw [hlen3]; decide
        have hget : (w.preMajor ++ [f])[(w.preMajor ++ [f]).length - 1 - 1]? =
            some w.minor := by
          rw [hlen3]
          rw [show ((3 : Nat) - 1 - 1) = 1 from rfl]
          rw [List.getElem?_append_left (by rw [hpmLen]; decide)]
          have h := w.hminor; rw [hnp, hctorIdx] at h
          exact h
        exact instPrefix_bvar_lt hj hget
      rw [hminI]
      simp only [List.map_cons, List.map_nil]
      have hfI : instPrefix (w.preMajor ++ [f]) (.bvar 0) = f := by
        have hj : 0 < (w.preMajor ++ [f]).length := by rw [hlen3]; decide
        have hget : (w.preMajor ++ [f])[(w.preMajor ++ [f]).length - 1 - 0]? =
            some f := by
          rw [hlen3]
          rw [show ((3 : Nat) - 1 - 0) = 2 from rfl]
          rw [List.getElem?_append_right (Nat.le_of_eq hpmLen)]
          rw [hpmLen, show (2 - 2 : Nat) = 0 from rfl]
          rfl
        exact instPrefix_bvar_lt hj hget
      rw [hfI]
      show foldApps w.minor [f] = iotaRhsOf w
      unfold iotaRhsOf
      rw [hrecR, hls, hnp, hnM, hfields, hkinds, hctorAfter]
      rfl

open Ann in
/-- ann-side: every `IotaWitnessS` over a sub-env of `structEnvU` passes
`iotaWitnessSAnnB`. -/
theorem corrAnnCert_sub_structEnvU {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ structEnvU) : EnvCorrAnnCert E₀ := by
  intro w
  obtain ⟨hfamR, hfamM⟩ : w.familyRef = 0 ∧ w.famMember = trueFamMember := by
    rcases structEnvU_mem (hsub _ _ w.hfam) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · exact ⟨hr, hm⟩
    · have hk := w.hfamK; rw [hm] at hk; exact absurd hk (by decide)
    · have hk := w.hfamK; rw [hm] at hk; exact absurd hk (by decide)
  obtain ⟨hctorR, hctorM⟩ : w.ctorRef = 1 ∧ w.ctorMember = structMkMember := by
    rcases structEnvU_mem (hsub _ _ w.hctor) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · have hk := w.hctorK; rw [hm] at hk; exact absurd hk (by decide)
    · exact ⟨hr, hm⟩
    · have hk := w.hctorK; rw [hm] at hk; exact absurd hk (by decide)
  obtain ⟨hrecR, hrecM⟩ : w.recRef = 2 ∧ w.recMember = structRecMemberU := by
    rcases structEnvU_mem (hsub _ _ w.hrec) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · have hk := w.hrecK; rw [hm] at hk; exact absurd hk (by decide)
    · have hk := w.hrecK; rw [hm] at hk; exact absurd hk (by decide)
    · exact ⟨hr, hm⟩
  have hctorIdx : w.ctorIdx = 0 := by
    have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hnp0 : w.nparams + w.nindices = 0 := by
    have h := w.hnidx; rw [hfamM] at h
    have h0 : piCount trueFamMember.mtype = 0 := rfl
    rw [h0] at h; omega
  have hnp : w.nparams = 0 := by omega
  have hni : w.nindices = 0 := by omega
  obtain ⟨f, hfields⟩ : ∃ f, w.fields = [f] := by
    have h := w.hnpar; rw [hnp, hctorM] at h
    have h0 : piCount structMkMember.mtype = 1 := rfl
    rw [h0] at h; simp only [Nat.zero_add] at h
    generalize hfg : w.fields = fg
    rw [hfg] at h
    rcases fg with _ | ⟨f, _ | ⟨f', fs⟩⟩
    · simp at h
    · exact ⟨f, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hcd : w.ctorDoms = [structFieldTy] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    have h0 : peelPis (0 + [f].length) structMkMember.mtype =
        some ([structFieldTy], .const 0 []) := rfl
    rw [h0] at h
    injection h with hp; injection hp with h1 h2; exact h1.symm
  have hcr : w.ctorResult = .const 0 [] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    have h0 : peelPis (0 + [f].length) structMkMember.mtype =
        some ([structFieldTy], .const 0 []) := rfl
    rw [h0] at h
    injection h with hp; injection hp with h1 h2; exact h2.symm
  have hmem0 : E₀.members 0 = some trueFamMember := by
    have h := w.hfam; rwa [hfamR, hfamM] at h
  have hpmLen : w.preMajor.length = 2 := by
    have h := w.hpre; rw [hnp, hnM, hni] at h; omega
  obtain ⟨l, hls⟩ : ∃ l, w.ls = [l] := by
    have h := w.hlsLen; rw [hrecM] at h
    have h1 : structRecMemberU.arity = 1 := rfl
    rw [h1] at h
    generalize hlg : w.ls = lsg
    rw [hlg] at h
    rcases lsg with _ | ⟨l, _ | ⟨l', ls⟩⟩
    · simp at h
    · exact ⟨l, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hsh : w.shapes = [.nonrecursive] := by
    have h := w.hshapes
    rw [hfamR, hfamM, hnp, hni, hcd, List.drop_zero] at h
    have hconc : fieldShapesFuel E₀
        (domsFuelBound [structFieldTy]) 0 trueFamMember.arity 0 0 0
        [structFieldTy] = some [.nonrecursive] := by
      have hfr : ∀ j (hj : j < ([structFieldTy] : List (Expr Nat)).length),
          DirectFieldFrag E₀ (domsFuelBound [structFieldTy]) 0
            trueFamMember.arity 0 0 (0 + j) [structFieldTy][j] := by
        intro j hj
        have hj0 : j = 0 := by
          simp only [List.length_cons, List.length_nil] at hj; omega
        subst hj0
        apply directFragOfCheck
        unfold directFragOne
        rfl
      rw [fieldShapesFuel_eq_analyzeFields_of_directFrag _ hfr]
      rfl
    exact fieldShapesFuel_agree E₀ h hconc
  have hsc : w.schema = .app (.bvar 1) (.bvar 0) := by
    have h := w.hschema
    rw [hrecR, hrecM, hnp, hnM, hni, hctorIdx, hfields, hcd, hcr, hsh] at h
    have htl : lift 0 ([f].length + 1 + 1 + 0)
        (ctorFieldTelRaw 0 [structFieldTy] (.const 0 [])) =
        .pi structFieldTy (.const 0 []) := rfl
    rw [htl] at h
    have hconc : iotaOpenRhs E₀ 16 (.const 2 (canonRecLevels 1))
        (.bvar 1) (preMajorBvars 0 1 0 1) 0 1 [.nonrecursive]
        (fieldBvars 1) (.pi structFieldTy (.const 0 [])) =
        some (.app (.bvar 1) (.bvar 0)) := rfl
    exact iotaOpenRhs_agree E₀ h hconc
  show iotaWitnessSAnnB E₀ w = true
  unfold iotaWitnessSAnnB
  rw [hfamR, hfamM, hnp, hni, hctorIdx, hcd, List.drop_zero]
  rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
  · show directFragOne E₀ (domsFuelBound [structFieldTy]) 0
        trueFamMember.arity 0 0 0 structFieldTy &&
      directFragCheck E₀ (domsFuelBound [structFieldTy]) 0
        trueFamMember.arity 0 0 (0 + 1) [] = true
    rw [Bool.and_eq_true]; refine ⟨?_, rfl⟩
    unfold directFragOne
    rfl
  · have happ : applyTel (w.preMajor.take 0)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
        some (.pi structFieldTy (.const 0 [])) := by
      rw [hctorM]
      show applyTel (w.preMajor.take 0)
          (instantiateLevels (w.ls.take 0) structMkMember.mtype) =
        some (.pi structFieldTy (.const 0 []))
      rw [List.take_zero]
      rfl
    rw [happ]
    simp only
    rw [hfields, hsh]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · rfl
    · obtain ⟨minor, hmin⟩ : ∃ m, w.preMajor[0 + 1 + 0]? = some m :=
        ⟨w.preMajor[1]'(by rw [hpmLen]; decide), List.getElem?_eq_getElem _⟩
      rw [hmin]
      simp only
      rw [decide_eq_true_eq]
      unfold iotaRhsOfS
      rw [hls, hfields, hsc]
      have hIL : instantiateLevels [l] (.app (.bvar 1) (.bvar 0)) =
          (.app (.bvar 1) (.bvar 0) : Expr Nat) := rfl
      rw [hIL]
      show instPrefix (w.preMajor ++ [f])
          (foldApps (.bvar 1) [.bvar 0]) =
          foldApps minor (rhsArgsS (.const 2 [l]) w.preMajor 0 1 [f]
            [.nonrecursive] (.pi structFieldTy (.const 0 [])))
      rw [instPrefix_foldApps]
      have hlen3 : (w.preMajor ++ [f]).length = 3 := by
        rw [List.length_append, hpmLen]; rfl
      have hminI : instPrefix (w.preMajor ++ [f]) (.bvar 1) = minor := by
        have hj : 1 < (w.preMajor ++ [f]).length := by rw [hlen3]; decide
        have hget : (w.preMajor ++ [f])[(w.preMajor ++ [f]).length - 1 - 1]? =
            some minor := by
          rw [hlen3]
          rw [show ((3 : Nat) - 1 - 1) = 1 from rfl]
          rw [List.getElem?_append_left (by rw [hpmLen]; decide)]
          exact hmin
        exact instPrefix_bvar_lt hj hget
      rw [hminI]
      simp only [List.map_cons, List.map_nil]
      have hfI : instPrefix (w.preMajor ++ [f]) (.bvar 0) = f := by
        have hj : 0 < (w.preMajor ++ [f]).length := by rw [hlen3]; decide
        have hget : (w.preMajor ++ [f])[(w.preMajor ++ [f]).length - 1 - 0]? =
            some f := by
          rw [hlen3]
          rw [show ((3 : Nat) - 1 - 0) = 2 from rfl]
          rw [List.getElem?_append_right (Nat.le_of_eq hpmLen)]
          rw [hpmLen, show (2 - 2 : Nat) = 0 from rfl]
          rfl
        exact instPrefix_bvar_lt hj hget
      rw [hfI]
      have hrhs : rhsArgsS (.const 2 [l]) w.preMajor 0 1 [f]
          [.nonrecursive] (.pi structFieldTy (.const 0 [])) = [f] :=
        rhsArgsS_allNonrec [f] _ rfl
      rw [hrhs]

open Ann in
/-- `structEnvU` discharges: both certificates at every sub-environment. -/
theorem corrCertsBelow_structEnvU : CorrCertsBelow structEnvU :=
  fun _E₀ hsub =>
    ⟨corrEraseCert_sub_structEnvU hsub, corrAnnCert_sub_structEnvU hsub⟩


open Ann in
/-- the environment bridge applies at `S` with no hypothesis: through the semantic prefix
    (`annEnvA_of_envWfT_semPrefix`), which reads only that the groups are in the copy's scope. -/
theorem structEnvU_annotated : ∃ EA : ResolvedEnvA, eraseEnv EA = structEnvU ∧ AnnEnvA EA :=
  (annEnvA_of_envWfT_semPrefix structEnvUWfT structEnvUWfT_inScope).imp fun _ h => ⟨h.1, h.2.1⟩

open Ann in
/-- ROW 1 consumed at `S`'s environment, through the semantic prefix: `Sort 0` and `Sort 1` are not
    convertible there. -/
theorem structEnv_sorts_notConv {n : Nat} {T : Expr Nat}
    (h : ConvT structEnvU n [] (.sort .zero) (.sort (.succ .zero)) T) : False :=
  refutEqN_zero_succ_false (sortConvCharT_semPrefix structEnvUWfT structEnvUWfT_inScope .nil h)

/-! ## (9) W-1 (e-3): `And`, a struct group with parameters -/

/-- `And : Prop → Prop → Prop`. -/
def andFamMember : CheckedMember :=
  ⟨.inductiveM, 0, .pi (.sort .zero) (.pi (.sort .zero) (.sort .zero)), none⟩

/-- `And x y`. -/
abbrev andApp (x y : Expr Nat) : Expr Nat := .app (.app (.const 0 []) x) y

/-- `intro : Π (A B : Prop), A → B → And A B`: the parameters mirrored, two plain fields, each a proof. -/
def andIntroMember : CheckedMember :=
  ⟨.constructorM, 0, .pi (.sort .zero) (.pi (.sort .zero) (.pi (.bvar 1) (.pi (.bvar 1)
    (andApp (.bvar 3) (.bvar 2))))), none⟩

/-- the family alone, then with its constructor. -/
def andFamOnly : ResolvedEnv := extendEnv emptyEnv 0 andFamMember
def andPrefix : ResolvedEnv := extendEnv andFamOnly 1 andIntroMember

/-- L-K1's family view of `And`, wherever the family is present. -/
def andFamilyView (E : ResolvedEnv) (h : E.members 0 = some andFamMember) : PolicyFamilyView E where
  ref := 0
  member := andFamMember
  present := h
  hasClass := rfl
  parameters := [.sort .zero, .sort .zero]
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j =>
      match j with
      | ⟨0, _⟩ => HasTy.sort _ .zero
      | ⟨1, _⟩ => HasTy.sort _ .zero }

/-- L-K1's constructor view of `intro`: two parameters, two fields, no result index. -/
def andIntroView (E : ResolvedEnv) (h : E.members 0 = some andFamMember) :
    PolicyConstructorView E (andFamilyView E h) andIntroMember where
  hasClass := rfl
  arity := rfl
  parameters := [.sort .zero, .sort .zero]
  fields := [.bvar 1, .bvar 1]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j =>
      match j with
      | ⟨0, _⟩ => .succ .zero
      | ⟨1, _⟩ => .succ .zero
      | ⟨2, _⟩ => .zero
      | ⟨3, _⟩ => .zero
    bounded := fun j =>
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
    hasType := fun j =>
      match j with
      | ⟨0, _⟩ => HasTy.sort _ .zero
      | ⟨1, _⟩ => HasTy.sort _ .zero
      | ⟨2, _⟩ => HasTy.bvar _ 1 (.sort .zero) rfl
      | ⟨3, _⟩ => HasTy.bvar _ 1 (.sort .zero) rfl }
  parameterMirrors := fun i =>
    match i with
    | ⟨0, _⟩ => Conv.refl _ _
    | ⟨1, _⟩ => Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

/-- both fields are non-recursive (L-K1's positivity decider, at fuel 8). -/
theorem andIntroFields (E : ResolvedEnv) (h : E.members 0 = some andFamMember) :
    CtorFieldsPermitted (andIntroView E h) := fun j =>
  match j with
  | ⟨0, _⟩ => ⟨.nonrecursive, 8, [], rfl⟩
  | ⟨1, _⟩ => ⟨.nonrecursive, 8, [], rfl⟩

def andFamAdmitted : IndGroupAdmitted emptyEnv 0 andFamMember :=
  .family rfl (andFamilyView andFamOnly rfl) rfl rfl (Or.inl falseSort_prop)

def andIntroAdmitted : IndGroupAdmitted andFamOnly 1 andIntroMember :=
  .constructor (andFamilyView andFamOnly rfl) (andIntroView andFamOnly rfl)
    rfl (ctorBefore_famOnly rfl rfl) (ctorContig_famOnly rfl rfl) (fun _ => Or.inl falseSort_prop)
    (andIntroFields _ rfl)

/-- the motive's type, `And A B → Sort u`, under `A` and `B`. -/
abbrev andMotTy : Expr Nat := .pi (andApp (.bvar 1) (.bvar 0)) (.sort (.param 0))

/-- the minor premise, `Π (a : A) (b : B), motive (intro A B a b)`, under `A`, `B` and the motive. -/
abbrev andMinorTy : Expr Nat :=
  .pi (.bvar 2) (.pi (.bvar 2) (.app (.bvar 2)
    (.app (.app (.app (.app (.const 1 []) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))))

/-- the recursor's type, `Π (A B : Prop) (motive : And A B → Sort u)
    (m : Π a b, motive (intro A B a b)) (t : And A B), motive t`, as L-K1's policy builds it
    (`andGroupAdmitted.recursorType := rfl`). -/
def andRecTypeU : Expr Nat :=
  .pi (.sort .zero) (.pi (.sort .zero) (.pi andMotTy (.pi andMinorTy
    (.pi (andApp (.bvar 3) (.bvar 2)) (.app (.bvar 2) (.bvar 0))))))

def andRecMemberU : CheckedMember := ⟨.recursorM, 1, andRecTypeU, none⟩

def andEnvU : ResolvedEnv := extendEnv andPrefix 2 andRecMemberU

/-- L-K1's recursor admission: one constructor whose fields are proofs, AnySort by
    `EliminationSelection.singletonProp`. -/
def andGroupAdmitted : RecursorEliminationAdmitted andPrefix 2 andRecMemberU where
  family := andFamilyView andPrefix rfl
  constructors := [andIntroMember]
  constructorViews
    | ⟨0, _⟩ => andIntroView andPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [andMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp falseSort_prop rfl (fun ⟨0, _⟩ j =>
    match j with
    | ⟨0, _⟩ => Or.inl falseSort_prop
    | ⟨1, _⟩ => Or.inl falseSort_prop)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem andMinorMatch : MinorPremisesMatch andGroupAdmitted := by
  intro i
  have hlt : i.val < 1 := i.isLt
  have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp hlt)
  rw [hi]
  exact ⟨[.nonrecursive, .nonrecursive], 8, rfl, rfl⟩

/-- the ι equation at `intro`: `rec A B M m (intro A B a b) ⇝ m a b`, in the context `b, a, m, M, B, A`. -/
def andIntroCtx : LCtx :=
  [.assumption (.bvar 3), .assumption (.bvar 3), .assumption andMinorTy, .assumption andMotTy,
    .assumption (.sort .zero), .assumption (.sort .zero)]

def andIntroIotaTy :
    HasTy andEnvU 1 andIntroCtx (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      (.app (.bvar 3) (.app (.app (.app (.app (.const 1 []) (.bvar 5)) (.bvar 4)) (.bvar 1)) (.bvar 0))) :=
  HasTy.app andIntroCtx (.app (.bvar 2) (.bvar 1)) (.bvar 0) (.bvar 4)
    (.app (.bvar 4) (.app (.app (.app (.app (.const 1 []) (.bvar 6)) (.bvar 5)) (.bvar 2)) (.bvar 0)))
    (HasTy.app andIntroCtx (.bvar 2) (.bvar 1) (.bvar 5)
      (.pi (.bvar 5) (.app (.bvar 5) (.app (.app (.app (.app (.const 1 []) (.bvar 7)) (.bvar 6)) (.bvar 1))
        (.bvar 0))))
      (HasTy.bvar andIntroCtx 2 _ rfl) (HasTy.bvar andIntroCtx 1 _ rfl))
    (HasTy.bvar andIntroCtx 0 _ rfl)

def andIotaIntro : IotaEquationTyped andGroupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive, .nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  exact andIntroIotaTy

def andShapes : Fin andGroupAdmitted.constructors.length → List FieldShape
  | ⟨0, _⟩ => [.nonrecursive, .nonrecursive]

def andIotaClause : IotaDescriptorClause andPrefix andGroupAdmitted where
  signatureOnly := rfl
  shapesAt := andShapes
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => andIotaIntro

def andRecAdmitted : IndGroupAdmitted andPrefix 2 andRecMemberU :=
  .recursor andGroupAdmitted rfl (census_famOne rfl rfl rfl)
    (fun i => match i with | ⟨0, _⟩ => fun _ => Or.inl falseSort_prop)
    (fun i => match i with | ⟨0, _⟩ => andIntroFields _ rfl)
    andMinorMatch andIotaClause

def andURecAdmitted : RecursorGroupIdxAdmitted andPrefix 2 andRecMemberU :=
  .ofAdmitted rfl

/-- `And x y : Prop` for `x y : Prop`, wherever the family is present. -/
def andOfTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h : E.members 0 = some andFamMember) {x y : Expr Nat}
    (hx : HasTyT E n Γ x (.sort .zero)) (hy : HasTyT E n Γ y (.sort .zero)) :
    HasTyT E n Γ (andApp x y) (.sort .zero) :=
  .app Γ _ y (.sort .zero) (.sort .zero)
    (.app Γ _ x (.sort .zero) (.pi (.sort .zero) (.sort .zero)) (.const Γ 0 [] andFamMember h rfl rfl) hx) hy

/-- the family's stored type, `Prop → Prop → Prop`. -/
abbrev andFamSortU : Level := .imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))

def andFamTyT : HasTyT emptyEnv 0 [] andFamMember.mtype (.sort andFamSortU) :=
  .pi [] _ _ _ _ (.sort [] .zero) (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))

/-- `intro`'s stored type, wherever the family is present. -/
abbrev andIntroSortU : Level := .imax (.succ .zero) (.imax (.succ .zero) (.imax .zero (.imax .zero .zero)))

def andIntroTyT {E : ResolvedEnv} (h : E.members 0 = some andFamMember) :
    HasTyT E 0 [] andIntroMember.mtype (.sort andIntroSortU) :=
  .pi [] _ _ _ _ (.sort [] .zero)
    (.pi _ _ _ _ _ (.sort _ .zero)
      (.pi _ _ _ _ _ (.bvar _ 1 _ rfl)
        (.pi _ _ _ _ _ (.bvar _ 1 _ rfl)
          (andOfTyT h (.bvar _ 3 _ rfl) (.bvar _ 2 _ rfl)))))

/-- the minor's body context, `b, a, motive, B, A`. -/
abbrev andMinorCtx : LCtx :=
  [.assumption (.bvar 2), .assumption (.bvar 2), .assumption andMotTy, .assumption (.sort .zero),
    .assumption (.sort .zero)]

/-- `intro A B a b : And A B` in the minor's body context, one argument at a time. -/
def andIntroAppTyT :
    HasTyT andPrefix 1 andMinorCtx (.app (.app (.app (.app (.const 1 []) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))
      (andApp (.bvar 4) (.bvar 3)) :=
  .app andMinorCtx _ (.bvar 0) (.bvar 3) (andApp (.bvar 5) (.bvar 4))
    (.app andMinorCtx _ (.bvar 1) (.bvar 4) (.pi (.bvar 4) (andApp (.bvar 6) (.bvar 5)))
      (.app andMinorCtx _ (.bvar 3) (.sort .zero) (.pi (.bvar 5) (.pi (.bvar 1) (andApp (.bvar 7) (.bvar 2))))
        (.app andMinorCtx (.const 1 []) (.bvar 4) (.sort .zero)
          (.pi (.sort .zero) (.pi (.bvar 1) (.pi (.bvar 1) (andApp (.bvar 3) (.bvar 2)))))
          (.const andMinorCtx 1 [] andIntroMember rfl rfl rfl) (.bvar andMinorCtx 4 _ rfl))
        (.bvar andMinorCtx 3 _ rfl))
      (.bvar andMinorCtx 1 _ rfl))
    (.bvar andMinorCtx 0 _ rfl)

/-- the recursor's stored type typed in the derivation scope at one level parameter. -/
def andRecTypeUTyT : Σ u, HasTyT andPrefix 1 [] andRecTypeU (.sort u) :=
  ⟨_, .pi [] _ _ _ _ (.sort [] .zero)
    (.pi _ _ _ _ _ (.sort _ .zero)
      (.pi _ _ _ _ _
        (.pi _ _ _ _ _ (andOfTyT rfl (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl)) (.sort _ (.param 0)))
        (.pi _ _ _ _ _
          (.pi _ _ _ _ _ (.bvar _ 2 _ rfl)
            (.pi _ _ _ _ _ (.bvar _ 2 _ rfl)
              (.app _ (.bvar 2) (.app (.app (.app (.app (.const 1 []) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))
                (andApp (.bvar 4) (.bvar 3)) (.sort (.param 0)) (.bvar _ 2 _ rfl) andIntroAppTyT)))
          (.pi _ _ _ _ _ (andOfTyT rfl (.bvar _ 3 _ rfl) (.bvar _ 2 _ rfl))
            (.app _ (.bvar 2) (.bvar 0) (andApp (.bvar 4) (.bvar 3)) (.sort (.param 0)) (.bvar _ 2 _ rfl)
              (.bvar _ 0 _ rfl))))))⟩

/-- the family's parameters typed at their recorded sort, wherever the family is present. -/
theorem andFamTypedE (E : ResolvedEnv) (h : E.members 0 = some andFamMember) :
    FamilyTypedT (andFamilyView E h) := fun i =>
  match i with
  | ⟨0, _⟩ => ⟨.sort [] .zero⟩
  | ⟨1, _⟩ => ⟨.sort _ .zero⟩

/-- `intro`'s parameters and fields typed at their recorded sorts, and its parameters the family's. -/
theorem andIntroTypedE (E : ResolvedEnv) (h : E.members 0 = some andFamMember) :
    CtorTypedT (andIntroView E h) :=
  ⟨fun i => match i with
    | ⟨0, _⟩ => ⟨.sort [] .zero⟩
    | ⟨1, _⟩ => ⟨.sort _ .zero⟩
    | ⟨2, _⟩ => ⟨.bvar _ 1 _ rfl⟩
    | ⟨3, _⟩ => ⟨.bvar _ 1 _ rfl⟩,
   fun i => match i with
    | ⟨0, _⟩ => ⟨.refl _ _⟩
    | ⟨1, _⟩ => ⟨.refl _ _⟩⟩

theorem andFamTyped : IndGroupTypedT andFamAdmitted := andFamTypedE _ rfl

theorem andIntroTyped : IndGroupTypedT andIntroAdmitted := ⟨andFamTypedE _ rfl, andIntroTypedE _ rfl⟩

theorem andRecTyped : IndGroupTypedT andRecAdmitted :=
  ⟨andFamTypedE _ rfl, fun i => match i with | ⟨0, _⟩ => andIntroTypedE _ rfl,
   fun i => match i with | ⟨0, _⟩ => iotaEquationTypedT_of_check (synCheck _ _) rfl⟩

/-- L-K1's checks, member by member, each member's stored type typed in the group built so far;
    `intro` also in ConstructorScope, `And` alone (05 §4). -/
def andMembersT :
    GroupMembersT (extendEnv emptyEnv 0 andFamMember) emptyEnv
      [(0, andFamMember), (1, andIntroMember), (2, andRecMemberU)] andEnvU :=
  .cons _ 0 andFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    andFamAdmitted PUnit.unit _ andFamTyT (fun h => absurd h (by decide))
    andFamTyped
    (.cons _ 1 andIntroMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      andIntroAdmitted PUnit.unit _ (andIntroTyT rfl) (fun _ => ⟨andIntroTyT rfl⟩)
      andIntroTyped
      (.cons _ 2 andRecMemberU _ _ rfl rfl (fun _ => rfl) (fun hc => absurd hc (by decide)) rfl rfl rfl
        andRecAdmitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ andRecTypeUTyT.2 (fun h => absurd h (by decide))
        andRecTyped (.nil _)))

/-- `And`, `intro` and the recursor: ONE group step of the typed environment judgment. -/
def andEnvUWfT : EnvWfT andEnvU :=
  .group emptyEnv 0 andFamMember [(1, andIntroMember)] 2 andRecMemberU andEnvU .empty rfl
    (fun c hc => by simp at hc; subst hc; rfl) rfl andMembersT

/-- the structured views: `And : Prop → Prop → Prop`, a `Prop` family with two parameters. -/
def andFamViewT : FamViewT andFamMember where
  params := [(.sort .zero, .succ .zero), (.sort .zero, .succ .zero)]
  indices := []
  sort := .zero
  stored := rfl
  profile := Or.inl falseSort_prop

/-- `intro : Π A B, A → B → And A B`: the mirrors, two plain fields in `Prop`. -/
def andIntroCtorT : GroupCtorT emptyEnv 0 andFamMember andFamViewT where
  ref := 1
  member := andIntroMember
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hclT := fun _ => rfl
  u := andIntroSortU
  hT := andIntroTyT rfl
  hlvl := rfl
  view :=
    { mirrors := [(.sort .zero, .succ .zero), (.sort .zero, .succ .zero)]
      fields := [.plain (.bvar 1) .zero, .plain (.bvar 1) .zero]
      res := []
      stored := rfl
      mirrorsConv := .cons [] _ _ _ _ _ _ (.refl [] _) (eqN_refl _)
        (.cons _ _ _ _ _ [] [] (.refl _ _) (eqN_refl _) (.nil _))
      typed := .plain _ 0 (.bvar 1) .zero _ [] (.bvar _ 1 _ rfl)
        (.plain _ 1 (.bvar 1) .zero [] [] (.bvar _ 1 _ rfl) (.nil _ 2 [] (.nil .zero)))
      univ := fun _ _ _ => Or.inl falseSort_prop
      drecD_typed := drecDTypedT_of_absent (by decide) }

def andCsT : List (GroupCtorT emptyEnv 0 andFamMember andFamViewT) := [andIntroCtorT]

/-- the recursor: AnySort, its stored type the one built from the views. -/
def andRecT : GroupRecT emptyEnv 0 andFamMember andFamViewT andCsT where
  member := andRecMemberU
  hcls := rfl
  hnobody := rfl
  elim := .anySort
  harity := rfl
  stored := rfl
  hclT := fun _ => rfl
  u := andRecTypeUTyT.1
  hT := andRecTypeUTyT.2
  hlvl := rfl

/-- `And` is a struct group on the typed views. -/
theorem andStructT : StructGroupT andCsT :=
  ⟨rfl, rfl, fun c hc => by
    simp only [andCsT, List.mem_singleton] at hc
    subst hc
    refine ⟨List.cons_ne_nil _ _, fun F hF => ?_⟩
    have hF' : F ∈ [FieldT.plain (.bvar 1) .zero, .plain (.bvar 1) .zero] := hF
    rcases List.mem_cons.mp hF' with h | h
    · exact ⟨_, _, h, falseSort_prop⟩
    · exact ⟨_, _, List.mem_singleton.mp h, falseSort_prop⟩⟩

def andInScopeT : GroupInScopeT emptyEnv 0 andFamMember [(1, andIntroMember)] 2 andRecMemberU where
  fv := andFamViewT
  htel := .cons [] _ _ _ (.sort [] .zero) (.cons _ _ _ _ (.sort _ .zero) (.nil _))
  cs := andCsT
  hctors := rfl
  hlayout := rfl
  grec := andRecT
  hrr := rfl
  hrm := rfl
  hprof := ⟨fun v hv => (List.not_mem_nil v hv).elim, fun _ _ _ hS => absurd andStructT hS⟩
  hpb := by decide
  hsnd := by decide

theorem andEnvUWfT_inScope : andEnvUWfT.InScope := ⟨trivial, ⟨andInScopeT⟩⟩

/-- TOOTH: (O1) as it stood before W-1 (e-3) fails at `And`. -/
theorem and_O1_before :
    ¬ (UniformProp andFamViewT.sort → andCsT ≠ [] → ¬ UnitGroupT andCsT →
      andRecT.elim = .propOnly) := by
  intro h
  have := h falseSort_prop (List.cons_ne_nil _ _) (fun hU => by
    have hf := hU.2.2 andIntroCtorT (List.mem_singleton_self _)
    cases hf)
  cases this

open Ann in
/-! ### the ι-correspondence certificates at `andEnvU`

GAP-B for the `And` group: member inversion pins the references (`0`/`1`/`2`),
`hmajorTy` forces the `(2,0)` split — the major domain `And (bvar 3) (bvar 2)`
is inconsistent with `(0,2)` and `(1,1)` — the two `.bvar 1` fields classify
identically under both analyzers, and the schema `minor f0 f1` computes through
`instPrefix_bvar_lt`.  Decided per-witness by `iotaWitnessSB`/
`iotaWitnessSAnnB`. -/

/-! ### `And` (`andEnvU`) -/

open Ann in
/-- member inversion for `andEnvU`: `And` at 0, `intro` at 1, the recursor
    at 2. -/
theorem andEnvU_mem {c : Nat} {m : CheckedMember}
    (h : andEnvU.members c = some m) :
    (c = 0 ∧ m = andFamMember) ∨ (c = 1 ∧ m = andIntroMember) ∨
      (c = 2 ∧ m = andRecMemberU) := by
  have hmem : andEnvU.members c =
      (if c = 2 then some andRecMemberU
       else if c = 1 then some andIntroMember
       else if c = 0 then some andFamMember else none) := rfl
  rw [hmem] at h
  by_cases h2 : c = 2
  · rw [if_pos h2] at h; cases h
    exact Or.inr (Or.inr ⟨h2, rfl⟩)
  · rw [if_neg h2] at h
    by_cases h1 : c = 1
    · rw [if_pos h1] at h; cases h; exact Or.inr (Or.inl ⟨h1, rfl⟩)
    · rw [if_neg h1] at h
      by_cases h0 : c = 0
      · rw [if_pos h0] at h; cases h; exact Or.inl ⟨h0, rfl⟩
      · rw [if_neg h0] at h; exact Option.noConfusion h

open Ann in
/-- `constsMemberFuel` on `And`'s family const, wherever the family is
    present. -/
theorem andEnvU_constsMember {E₀ : ResolvedEnv}
    (hmem0 : E₀.members 0 = some andFamMember) {fuel : Nat} :
    constsMemberFuel E₀ (fuel + 1) (.const 0 []) = true := by
  cases fuel with
  | zero => unfold constsMemberFuel; rw [hmem0]; rfl
  | succ f => unfold constsMemberFuel; rw [hmem0]; rfl

open Ann in
/-- The `And` witness pins, shared by the two certificates: member references,
    the (2,0) parameter/index split forced by `hmajorTy`, the two fields,
    domains, result and minor. -/
theorem andEnvU_witness_pins {E₀ : ResolvedEnv} (hsub : EnvSub E₀ andEnvU)
    {recRef ctorRef familyRef : Nat} {recMember ctorMember famMember : CheckedMember}
    (hfam : E₀.members familyRef = some famMember)
    (hfamK : famMember.mclass = .inductiveM)
    (hctor : E₀.members ctorRef = some ctorMember)
    (hctorK : ctorMember.mclass = .constructorM)
    (hrec : E₀.members recRef = some recMember)
    (hrecK : recMember.mclass = .recursorM) :
    (familyRef = 0 ∧ famMember = andFamMember) ∧
      (ctorRef = 1 ∧ ctorMember = andIntroMember) ∧
      (recRef = 2 ∧ recMember = andRecMemberU) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases andEnvU_mem (hsub _ _ hfam) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · exact ⟨hr, hm⟩
    · rw [hm] at hfamK; exact absurd hfamK (by decide)
    · rw [hm] at hfamK; exact absurd hfamK (by decide)
  · rcases andEnvU_mem (hsub _ _ hctor) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · rw [hm] at hctorK; exact absurd hctorK (by decide)
    · exact ⟨hr, hm⟩
    · rw [hm] at hctorK; exact absurd hctorK (by decide)
  · rcases andEnvU_mem (hsub _ _ hrec) with ⟨hr, hm⟩ | ⟨hr, hm⟩ | ⟨hr, hm⟩
    · rw [hm] at hrecK; exact absurd hrecK (by decide)
    · rw [hm] at hrecK; exact absurd hrecK (by decide)
    · exact ⟨hr, hm⟩

open Ann in
/-- erase-side: every `IotaWitness` over a sub-env of `andEnvU` adapts. -/
theorem corrEraseCert_sub_andEnvU {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ andEnvU) : EnvCorrEraseCert E₀ := by
  intro w
  obtain ⟨⟨hfamR, hfamM⟩, ⟨hctorR, hctorM⟩, ⟨hrecR, hrecM⟩⟩ :=
    andEnvU_witness_pins hsub w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
  have hctorIdx : w.ctorIdx = 0 := by
    have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hsum : w.nparams + w.nindices = 2 := by
    have h := w.hnidx; rw [hfamM] at h
    have h0 : piCount andFamMember.mtype = 2 := rfl
    rw [h0] at h; exact h
  -- `hmajorTy` forces the split (2,0): the stored major domain is
  -- `And (bvar 3) (bvar 2)`, and the canonical argument list at (np,ni)
  -- is `bvar`s `np+ni+1` … `ni+2` then `ni-1` … `0` — only np=2, ni=0
  -- gives `.bvar 3`, `.bvar 2`.
  have hnp : w.nparams = 2 := by
    have hrd : w.recDoms = [.sort .zero, .sort .zero, andMotTy, andMinorTy,
        andApp (.bvar 3) (.bvar 2)] := by
      have h := w.hpeelRec; rw [hrecM, hnM] at h
      have h5 : w.nparams + 1 + 1 + w.nindices + 1 = 5 := by omega
      rw [h5] at h
      have h0 : peelPis 5 andRecMemberU.mtype =
          some ([.sort .zero, .sort .zero, andMotTy, andMinorTy,
            andApp (.bvar 3) (.bvar 2)], .app (.bvar 2) (.bvar 0)) := rfl
      rw [h0] at h
      injection h with hp; injection hp with h1 _; exact h1.symm
    have hmaj := w.hmajorTy
    rw [hfamR, hfamM, hnM, hrd] at hmaj
    have h4 : w.nparams + 1 + 1 + w.nindices = 4 := by omega
    rw [h4] at hmaj
    have hdoms : ([.sort .zero, .sort .zero, andMotTy, andMinorTy,
        andApp (.bvar 3) (.bvar 2)] : List (Expr Nat))[4]? =
        some (andApp (.bvar 3) (.bvar 2)) := rfl
    rw [hdoms] at hmaj
    rcases (show w.nparams = 0 ∨ w.nparams = 1 ∨ w.nparams = 2 by omega)
        with hnp0 | hnp1 | hnp2
    · rw [hnp0] at hmaj
      rw [show w.nindices = 2 by omega] at hmaj
      have hm := Option.some.inj hmaj
      change andApp (.bvar 3) (.bvar 2) =
          .app (.app (.const 0 []) (.bvar 1)) (.bvar 0) at hm
      injection hm with _ h2
      exact absurd (Expr.bvar.inj h2) (by decide)
    · rw [hnp1] at hmaj
      rw [show w.nindices = 1 by omega] at hmaj
      have hm := Option.some.inj hmaj
      change andApp (.bvar 3) (.bvar 2) =
          .app (.app (.const 0 []) (.bvar 3)) (.bvar 0) at hm
      injection hm with _ h2
      exact absurd (Expr.bvar.inj h2) (by decide)
    · exact hnp2
  have hni : w.nindices = 0 := by omega
  obtain ⟨f0, f1, hfields⟩ : ∃ f g, w.fields = [f, g] := by
    have h := w.hnpar; rw [hnp, hctorM] at h
    have h0 : piCount andIntroMember.mtype = 4 := rfl
    rw [h0] at h
    generalize hfg : w.fields = fg
    rw [hfg] at h
    rcases fg with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · simp at h
    · simp at h
    · exact ⟨a, b, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hcd : w.ctorDoms = [.sort .zero, .sort .zero, .bvar 1, .bvar 1] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    have h0 : peelPis (2 + [f0, f1].length) andIntroMember.mtype =
        some ([.sort .zero, .sort .zero, .bvar 1, .bvar 1],
          andApp (.bvar 3) (.bvar 2)) := rfl
    rw [h0] at h
    injection h with hp; injection hp with h1 h2; exact h1.symm
  have hcr : w.ctorResult = andApp (.bvar 3) (.bvar 2) := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    have h0 : peelPis (2 + [f0, f1].length) andIntroMember.mtype =
        some ([.sort .zero, .sort .zero, .bvar 1, .bvar 1],
          andApp (.bvar 3) (.bvar 2)) := rfl
    rw [h0] at h
    injection h with hp; injection hp with h1 h2; exact h2.symm
  have hkinds : w.kinds = [.plain, .plain] := by
    have h := w.hkinds; rw [hfamR, hcd, hnp] at h
    have ha : analyzeFields 0
        ([.sort .zero, .sort .zero, .bvar 1, .bvar 1].drop 2) =
        some [.plain, .plain] := rfl
    rw [ha] at h
    injection h with h'; exact h'.symm
  have hmem0 : E₀.members 0 = some andFamMember := by
    have h := w.hfam; rwa [hfamR, hfamM] at h
  obtain ⟨p0, p1, p2, p3, hpm⟩ : ∃ a b c d, w.preMajor = [a, b, c, d] := by
    have h := w.hpre; rw [hnp, hnM, hni] at h
    generalize hpg : w.preMajor = pg
    rw [hpg] at h
    rcases pg with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, es⟩⟩⟩⟩⟩
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · exact ⟨a, b, c, d, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hminor : w.minor = p3 := by
    have h := w.hminor; rw [hnp, hctorIdx, hpm] at h
    have h0 : ([p0, p1, p2, p3] : List (Expr Nat))[2 + 1 + 0]? =
        some p3 := rfl
    rw [h0] at h; injection h with h'; exact h'.symm
  have hpiCA : isPiTel 2 w.ctorAfterParams = true := by
    have h := w.hctorTel
    have hlen : w.kinds.length = 2 := by rw [hkinds]; rfl
    rw [hlen] at h; exact h
  obtain ⟨l, hls⟩ : ∃ l, w.ls = [l] := by
    have h := w.hlsLen; rw [hrecM] at h
    have h1 : andRecMemberU.arity = 1 := rfl
    rw [h1] at h
    generalize hlg : w.ls = lsg
    rw [hlg] at h
    rcases lsg with _ | ⟨l, _ | ⟨l', ls⟩⟩
    · simp at h
    · exact ⟨l, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  refine ⟨16, ?_⟩
  show iotaWitnessSB w 16 = true
  unfold iotaWitnessSB
  rw [hfamR, hfamM, hnp, hni, hnM, hfields, hcd, hcr]
  rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
  · rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · show directFragCheck E₀ 16 0 andFamMember.arity 2 0 2
          ([.sort .zero, .sort .zero, .bvar 1, .bvar 1].drop 2) = true
      have hdrop : ([.sort .zero, .sort .zero, .bvar 1, .bvar 1] :
          List (Expr Nat)).drop 2 = [.bvar 1, .bvar 1] := rfl
      rw [hdrop]
      rfl
    · show iotaWitnessStableB E₀ 16
          ([.sort .zero, .sort .zero, .bvar 1, .bvar 1].drop 2)
          (fieldBvars [f0, f1].length)
          (lift 0 ([f0, f1].length + 1 + 1 + 0)
            (ctorFieldTelRaw 2 [.sort .zero, .sort .zero, .bvar 1, .bvar 1]
              (andApp (.bvar 3) (.bvar 2)))) = true
      have hdrop : ([.sort .zero, .sort .zero, .bvar 1, .bvar 1] :
          List (Expr Nat)).drop 2 = [.bvar 1, .bvar 1] := rfl
      have htl : lift 0 ([f0, f1].length + 1 + 1 + 0)
          (ctorFieldTelRaw 2 [.sort .zero, .sort .zero, .bvar 1, .bvar 1]
            (andApp (.bvar 3) (.bvar 2))) =
          .pi (.bvar 5) (.pi (.bvar 5)
            (andApp (.bvar 7) (.bvar 6))) := rfl
      rw [hdrop, htl]
      unfold iotaWitnessStableB
      rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
      · rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
        · show List.all [.bvar 1, .bvar 1]
              (constsMemberFuel E₀ (16 + 1)) = true
          simp only [List.all_cons, List.all_nil, constsMemberFuel,
            Bool.and_true, Bool.true_and]
        · show List.all [.bvar 1, .bvar 0]
              (constsMemberFuel E₀ (16 + 1)) = true
          simp only [List.all_cons, List.all_nil, constsMemberFuel,
            Bool.and_true, Bool.true_and]
      · show constsMemberFuel E₀ (16 + 1)
            (.pi (.bvar 5) (.pi (.bvar 5)
              (andApp (.bvar 7) (.bvar 6)))) = true
        simp only [constsMemberFuel, hmem0, andFamMember, andApp,
          transparent, Bool.and_true, Bool.true_and]
        rfl
  · have hschema : iotaSchemaS w 16 =
        some (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) := by
      show iotaOpenRhs E₀ 16
          (.const w.recRef (canonRecLevels w.recMember.arity))
          (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors (w.kinds.map shapeOfKind)
          (fieldBvars w.fields.length)
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) =
        some (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      rw [hrecR, hrecM, hnp, hni, hnM, hctorIdx, hfields, hcd, hcr, hkinds]
      have htl : lift 0 ([f0, f1].length + 1 + 1 + 0)
          (ctorFieldTelRaw 2 [.sort .zero, .sort .zero, .bvar 1, .bvar 1]
            (andApp (.bvar 3) (.bvar 2))) =
          .pi (.bvar 5) (.pi (.bvar 5)
            (andApp (.bvar 7) (.bvar 6))) := rfl
      rw [htl]
      unfold iotaOpenRhs
      rw [show iotaArgs E₀ 16 (.const 2 (canonRecLevels andRecMemberU.arity))
          (preMajorBvars 2 1 0 [f0, f1].length) 2 1
          (List.map shapeOfKind [.plain, .plain]) (fieldBvars [f0, f1].length)
          (.pi (.bvar 5) (.pi (.bvar 5) (andApp (.bvar 7) (.bvar 6)))) =
        some [.bvar 1, .bvar 0] from
        iotaArgs_allNonrec [.bvar 1, .bvar 0]
          (.pi (.bvar 5) (.pi (.bvar 5) (andApp (.bvar 7) (.bvar 6)))) rfl]
      rfl
    rw [hschema]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · rfl
    · rw [decide_eq_true_eq]
      rw [hls]
      have hIL : instantiateLevels [l]
          (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) =
          (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0) : Expr Nat) := rfl
      rw [hIL]
      show instPrefix (w.preMajor ++ [f0, f1])
          (foldApps (.bvar 2) [.bvar 1, .bvar 0]) = iotaRhsOf w
      rw [instPrefix_foldApps]
      have hlen6 : (w.preMajor ++ [f0, f1]).length = 6 := by
        rw [List.length_append, hpm]; rfl
      have hminI : instPrefix (w.preMajor ++ [f0, f1]) (.bvar 2) =
          w.minor := by
        have hj : 2 < (w.preMajor ++ [f0, f1]).length := by
          rw [hlen6]; decide
        have hget : (w.preMajor ++ [f0, f1])[(w.preMajor ++ [f0, f1]).length - 1 - 2]? =
            some w.minor := by
          rw [hlen6, hpm, hminor]
          rfl
        exact instPrefix_bvar_lt hj hget
      rw [hminI]
      simp only [List.map_cons, List.map_nil]
      have hfI1 : instPrefix (w.preMajor ++ [f0, f1]) (.bvar 1) = f0 := by
        have hj : 1 < (w.preMajor ++ [f0, f1]).length := by
          rw [hlen6]; decide
        have hget : (w.preMajor ++ [f0, f1])[(w.preMajor ++ [f0, f1]).length - 1 - 1]? =
            some f0 := by
          rw [hlen6, hpm]
          rfl
        exact instPrefix_bvar_lt hj hget
      have hfI0 : instPrefix (w.preMajor ++ [f0, f1]) (.bvar 0) = f1 := by
        have hj : 0 < (w.preMajor ++ [f0, f1]).length := by
          rw [hlen6]; decide
        have hget : (w.preMajor ++ [f0, f1])[(w.preMajor ++ [f0, f1]).length - 1 - 0]? =
            some f1 := by
          rw [hlen6, hpm]
          rfl
        exact instPrefix_bvar_lt hj hget
      rw [hfI1, hfI0]
      show foldApps w.minor [f0, f1] = iotaRhsOf w
      unfold iotaRhsOf
      rw [hrecR, hls, hnp, hnM, hfields, hkinds]
      have hrhs : rhsArgs (.const 2 [l]) w.preMajor 2 1 [f0, f1]
          [.plain, .plain] w.ctorAfterParams = [f0, f1] :=
        rhsArgs_allPlain [f0, f1] _ hpiCA
      rw [hrhs]

open Ann in
/-- ann-side: every `IotaWitnessS` over a sub-env of `andEnvU` passes
`iotaWitnessSAnnB`. -/
theorem corrAnnCert_sub_andEnvU {E₀ : ResolvedEnv}
    (hsub : EnvSub E₀ andEnvU) : EnvCorrAnnCert E₀ := by
  intro w
  obtain ⟨⟨hfamR, hfamM⟩, ⟨hctorR, hctorM⟩, ⟨hrecR, hrecM⟩⟩ :=
    andEnvU_witness_pins hsub w.hfam w.hfamK w.hctor w.hctorK w.hrec w.hrecK
  have hctorIdx : w.ctorIdx = 0 := by
    have h := w.hctorIdx; rw [hctorR, hfamR] at h; omega
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx; rw [hrecR, hfamR] at h; omega
  have hsum : w.nparams + w.nindices = 2 := by
    have h := w.hnidx; rw [hfamM] at h
    have h0 : piCount andFamMember.mtype = 2 := rfl
    rw [h0] at h; exact h
  have hnp : w.nparams = 2 := by
    have hrd : w.recDoms = [.sort .zero, .sort .zero, andMotTy, andMinorTy,
        andApp (.bvar 3) (.bvar 2)] := by
      have h := w.hpeelRec; rw [hrecM, hnM] at h
      have h5 : w.nparams + 1 + 1 + w.nindices + 1 = 5 := by omega
      rw [h5] at h
      have h0 : peelPis 5 andRecMemberU.mtype =
          some ([.sort .zero, .sort .zero, andMotTy, andMinorTy,
            andApp (.bvar 3) (.bvar 2)], .app (.bvar 2) (.bvar 0)) := rfl
      rw [h0] at h
      injection h with hp; injection hp with h1 _; exact h1.symm
    have hmaj := w.hmajorTy
    rw [hfamR, hfamM, hnM, hrd] at hmaj
    have h4 : w.nparams + 1 + 1 + w.nindices = 4 := by omega
    rw [h4] at hmaj
    have hdoms : ([.sort .zero, .sort .zero, andMotTy, andMinorTy,
        andApp (.bvar 3) (.bvar 2)] : List (Expr Nat))[4]? =
        some (andApp (.bvar 3) (.bvar 2)) := rfl
    rw [hdoms] at hmaj
    rcases (show w.nparams = 0 ∨ w.nparams = 1 ∨ w.nparams = 2 by omega)
        with hnp0 | hnp1 | hnp2
    · rw [hnp0] at hmaj
      rw [show w.nindices = 2 by omega] at hmaj
      have hm := Option.some.inj hmaj
      change andApp (.bvar 3) (.bvar 2) =
          .app (.app (.const 0 []) (.bvar 1)) (.bvar 0) at hm
      injection hm with _ h2
      exact absurd (Expr.bvar.inj h2) (by decide)
    · rw [hnp1] at hmaj
      rw [show w.nindices = 1 by omega] at hmaj
      have hm := Option.some.inj hmaj
      change andApp (.bvar 3) (.bvar 2) =
          .app (.app (.const 0 []) (.bvar 3)) (.bvar 0) at hm
      injection hm with _ h2
      exact absurd (Expr.bvar.inj h2) (by decide)
    · exact hnp2
  have hni : w.nindices = 0 := by omega
  obtain ⟨f0, f1, hfields⟩ : ∃ f g, w.fields = [f, g] := by
    have h := w.hnpar; rw [hnp, hctorM] at h
    have h0 : piCount andIntroMember.mtype = 4 := rfl
    rw [h0] at h
    generalize hfg : w.fields = fg
    rw [hfg] at h
    rcases fg with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · simp at h
    · simp at h
    · exact ⟨a, b, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hcd : w.ctorDoms = [.sort .zero, .sort .zero, .bvar 1, .bvar 1] := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    have h0 : peelPis (2 + [f0, f1].length) andIntroMember.mtype =
        some ([.sort .zero, .sort .zero, .bvar 1, .bvar 1],
          andApp (.bvar 3) (.bvar 2)) := rfl
    rw [h0] at h
    injection h with hp; injection hp with h1 h2; exact h1.symm
  have hcr : w.ctorResult = andApp (.bvar 3) (.bvar 2) := by
    have h := w.hpeel; rw [hnp, hfields, hctorM] at h
    have h0 : peelPis (2 + [f0, f1].length) andIntroMember.mtype =
        some ([.sort .zero, .sort .zero, .bvar 1, .bvar 1],
          andApp (.bvar 3) (.bvar 2)) := rfl
    rw [h0] at h
    injection h with hp; injection hp with h1 h2; exact h2.symm
  have hmem0 : E₀.members 0 = some andFamMember := by
    have h := w.hfam; rwa [hfamR, hfamM] at h
  obtain ⟨p0, p1, p2, p3, hpm⟩ : ∃ a b c d, w.preMajor = [a, b, c, d] := by
    have h := w.hpre; rw [hnp, hnM, hni] at h
    generalize hpg : w.preMajor = pg
    rw [hpg] at h
    rcases pg with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, es⟩⟩⟩⟩⟩
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · exact ⟨a, b, c, d, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  obtain ⟨l, hls⟩ : ∃ l, w.ls = [l] := by
    have h := w.hlsLen; rw [hrecM] at h
    have h1 : andRecMemberU.arity = 1 := rfl
    rw [h1] at h
    generalize hlg : w.ls = lsg
    rw [hlg] at h
    rcases lsg with _ | ⟨l, _ | ⟨l', ls⟩⟩
    · simp at h
    · exact ⟨l, rfl⟩
    · simp only [List.length_cons] at h; exact False.elim (by omega)
  have hsh : w.shapes = [.nonrecursive, .nonrecursive] := by
    have h := w.hshapes
    rw [hfamR, hfamM, hnp, hni, hcd] at h
    have hdrop : ([.sort .zero, .sort .zero, .bvar 1, .bvar 1] :
        List (Expr Nat)).drop 2 = [.bvar 1, .bvar 1] := rfl
    rw [hdrop] at h
    have hconc : fieldShapesFuel E₀
        (domsFuelBound [.bvar 1, .bvar 1]) 0 andFamMember.arity 2 0 2
        [.bvar 1, .bvar 1] = some [.nonrecursive, .nonrecursive] := by
      have hfr : ∀ j (hj : j <
          ([.bvar 1, .bvar 1] : List (Expr Nat)).length),
          DirectFieldFrag E₀ (domsFuelBound [.bvar 1, .bvar 1]) 0
            andFamMember.arity 2 0 (2 + j)
            ([.bvar 1, .bvar 1])[j] := by
        intro j hj
        have hj' : j = 0 ∨ j = 1 := by
          simp only [List.length_cons, List.length_nil] at hj; omega
        rcases hj' with rfl | rfl <;>
          exact directFragOfCheck (by unfold directFragOne; rfl)
      rw [fieldShapesFuel_eq_analyzeFields_of_directFrag _ hfr]
      rfl
    exact fieldShapesFuel_agree E₀ h hconc
  have hsc : w.schema = .app (.app (.bvar 2) (.bvar 1)) (.bvar 0) := by
    have h := w.hschema
    rw [hrecR, hrecM, hnp, hnM, hni, hctorIdx, hfields, hcd, hcr, hsh] at h
    have htl : lift 0 ([f0, f1].length + 1 + 1 + 0)
        (ctorFieldTelRaw 2 [.sort .zero, .sort .zero, .bvar 1, .bvar 1]
          (andApp (.bvar 3) (.bvar 2))) =
        .pi (.bvar 5) (.pi (.bvar 5)
          (andApp (.bvar 7) (.bvar 6))) := rfl
    rw [htl] at h
    have hconc : iotaOpenRhs E₀ 16 (.const 2 (canonRecLevels 1))
        (.bvar 2) (preMajorBvars 2 1 0 2) 2 1
        [.nonrecursive, .nonrecursive] (fieldBvars 2)
        (.pi (.bvar 5) (.pi (.bvar 5)
          (andApp (.bvar 7) (.bvar 6)))) =
        some (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) := by
      unfold iotaOpenRhs
      rw [show iotaArgs E₀ 16 (.const 2 (canonRecLevels 1))
          (preMajorBvars 2 1 0 2) 2 1
          [.nonrecursive, .nonrecursive] (fieldBvars 2)
          (.pi (.bvar 5) (.pi (.bvar 5) (andApp (.bvar 7) (.bvar 6)))) =
        some [.bvar 1, .bvar 0] from
        iotaArgs_allNonrec [.bvar 1, .bvar 0]
          (.pi (.bvar 5) (.pi (.bvar 5) (andApp (.bvar 7) (.bvar 6)))) rfl]
      rfl
    exact iotaOpenRhs_agree E₀ h hconc
  show iotaWitnessSAnnB E₀ w = true
  unfold iotaWitnessSAnnB
  rw [hfamR, hfamM, hnp, hni, hctorIdx, hcd]
  have hdrop : ([.sort .zero, .sort .zero, .bvar 1, .bvar 1] :
      List (Expr Nat)).drop 2 = [.bvar 1, .bvar 1] := rfl
  rw [hdrop]
  rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
  · show directFragCheck E₀ (domsFuelBound [.bvar 1, .bvar 1]) 0
        andFamMember.arity 2 0 2 [.bvar 1, .bvar 1] = true
    rfl
  · have happ : applyTel (w.preMajor.take 2)
        (instantiateLevels (w.ls.take w.ctorMember.arity) w.ctorMember.mtype) =
        some (instantiate 0 p1 (instantiate 1 (lift 0 1 p0)
          (.pi (.bvar 1) (.pi (.bvar 1)
            (andApp (.bvar 3) (.bvar 2)))))) := by
      rw [hctorM, hpm]
      rfl
    rw [happ]
    simp only
    rw [hfields, hsh]
    rw [Bool.and_eq_true]; refine ⟨?_, ?_⟩
    · have hpiCA : isPiTel 2
          (instantiate 0 p1 (instantiate 1 (lift 0 1 p0)
            (.pi (.bvar 1) (.pi (.bvar 1)
              (andApp (.bvar 3) (.bvar 2)))))) = true := rfl
      exact fieldsTelS_allNonrec [f0, f1] _ hpiCA
    · obtain ⟨minor, hmin⟩ : ∃ m, w.preMajor[2 + 1 + 0]? = some m := by
        have h0 : ([p0, p1, p2, p3] : List (Expr Nat))[2 + 1 + 0]? =
            some p3 := rfl
        exact ⟨p3, by rw [hpm]; exact h0⟩
      have hminorP : minor = p3 := by
        rw [hpm] at hmin
        have h0 : ([p0, p1, p2, p3] : List (Expr Nat))[2 + 1 + 0]? =
            some p3 := rfl
        rw [h0] at hmin; injection hmin with h'; exact h'.symm
      subst hminorP
      rw [hmin]
      simp only
      rw [decide_eq_true_eq]
      unfold iotaRhsOfS
      rw [hls, hfields, hsc]
      have hIL : instantiateLevels [l]
          (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) =
          (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0) : Expr Nat) := rfl
      rw [hIL]
      show instPrefix (w.preMajor ++ [f0, f1])
          (foldApps (.bvar 2) [.bvar 1, .bvar 0]) =
          foldApps minor (rhsArgsS (.const 2 [l]) w.preMajor 2 1 [f0, f1]
            [.nonrecursive, .nonrecursive]
            (instantiate 0 p1 (instantiate 1 (lift 0 1 p0)
              (.pi (.bvar 1) (.pi (.bvar 1)
                (andApp (.bvar 3) (.bvar 2)))))))
      rw [instPrefix_foldApps]
      have hlen6 : (w.preMajor ++ [f0, f1]).length = 6 := by
        rw [List.length_append, hpm]; rfl
      have hminI : instPrefix (w.preMajor ++ [f0, f1]) (.bvar 2) = minor := by
        have hj : 2 < (w.preMajor ++ [f0, f1]).length := by
          rw [hlen6]; decide
        have hget : (w.preMajor ++ [f0, f1])[(w.preMajor ++ [f0, f1]).length - 1 - 2]? =
            some minor := by
          rw [hlen6, hpm]; rfl
        exact instPrefix_bvar_lt hj hget
      rw [hminI]
      simp only [List.map_cons, List.map_nil]
      have hfI1 : instPrefix (w.preMajor ++ [f0, f1]) (.bvar 1) = f0 := by
        have hj : 1 < (w.preMajor ++ [f0, f1]).length := by
          rw [hlen6]; decide
        have hget : (w.preMajor ++ [f0, f1])[(w.preMajor ++ [f0, f1]).length - 1 - 1]? =
            some f0 := by
          rw [hlen6, hpm]; rfl
        exact instPrefix_bvar_lt hj hget
      have hfI0 : instPrefix (w.preMajor ++ [f0, f1]) (.bvar 0) = f1 := by
        have hj : 0 < (w.preMajor ++ [f0, f1]).length := by
          rw [hlen6]; decide
        have hget : (w.preMajor ++ [f0, f1])[(w.preMajor ++ [f0, f1]).length - 1 - 0]? =
            some f1 := by
          rw [hlen6, hpm]; rfl
        exact instPrefix_bvar_lt hj hget
      rw [hfI1, hfI0]
      have hrhs : rhsArgsS (.const 2 [l]) w.preMajor 2 1 [f0, f1]
          [.nonrecursive, .nonrecursive]
          (instantiate 0 p1 (instantiate 1 (lift 0 1 p0)
            (.pi (.bvar 1) (.pi (.bvar 1)
              (andApp (.bvar 3) (.bvar 2)))))) = [f0, f1] :=
        rhsArgsS_allNonrec [f0, f1] _ rfl
      rw [hrhs]

open Ann in
/-- `andEnvU` discharges: both certificates at every sub-environment. -/
theorem corrCertsBelow_andEnvU : CorrCertsBelow andEnvU :=
  fun _E₀ hsub =>
    ⟨corrEraseCert_sub_andEnvU hsub, corrAnnCert_sub_andEnvU hsub⟩


open Ann in
/-- the environment bridge applies at `And` with no hypothesis, through the semantic prefix. -/
theorem andEnvU_annotated : ∃ EA : ResolvedEnvA, eraseEnv EA = andEnvU ∧ AnnEnvA EA :=
  (annEnvA_of_envWfT_semPrefix andEnvUWfT andEnvUWfT_inScope).imp fun _ h => ⟨h.1, h.2.1⟩

open Ann in
/-- ROW 1 consumed at `And`'s environment, through the semantic prefix. -/
theorem andEnv_sorts_notConv {n : Nat} {T : Expr Nat}
    (h : ConvT andEnvU n [] (.sort .zero) (.sort (.succ .zero)) T) : False :=
  refutEqN_zero_succ_false (sortConvCharT_semPrefix andEnvUWfT andEnvUWfT_inScope .nil h)

end Rcic.Declarative

#print axioms Rcic.Declarative.natEnvUWfT
#print axioms Rcic.Declarative.natEnvUWfT_inScope
#print axioms Rcic.Declarative.pin_envWfT_natU
#print axioms Rcic.Declarative.hasTyT_constsIn
#print axioms Rcic.Declarative.natZero_ctorScope_split
#print axioms Rcic.Declarative.natRecMember_not_groupRec
#print axioms Rcic.Declarative.natEnvU_annotated
#print axioms Rcic.Declarative.falseEnvUWfT
#print axioms Rcic.Declarative.falseEnvUWfT_inScope
#print axioms Rcic.Declarative.false_O1_before
#print axioms Rcic.Declarative.falseEnvU_annotated
#print axioms Rcic.Declarative.trueEnvUWfT
#print axioms Rcic.Declarative.trueEnvUWfT_inScope
#print axioms Rcic.Declarative.trueUnitT
#print axioms Rcic.Declarative.true_O1_before
#print axioms Rcic.Declarative.trueEnvU_annotated
#print axioms Rcic.Declarative.structEnvUWfT
#print axioms Rcic.Declarative.structEnvUWfT_inScope
#print axioms Rcic.Declarative.structStructT
#print axioms Rcic.Declarative.struct_O1_before
#print axioms Rcic.Declarative.structEnvU_annotated
#print axioms Rcic.Declarative.structEnv_sorts_notConv
#print axioms Rcic.Declarative.andEnvUWfT
#print axioms Rcic.Declarative.andEnvUWfT_inScope
#print axioms Rcic.Declarative.andStructT
#print axioms Rcic.Declarative.and_O1_before
#print axioms Rcic.Declarative.andEnvU_annotated
#print axioms Rcic.Declarative.andEnv_sorts_notConv
