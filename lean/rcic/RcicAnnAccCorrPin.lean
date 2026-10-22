import rcic.RcicIotaFunRecCorr
import rcic.RcicIotaFunRecCorrR
import rcic.RcicAnnAccFrecPin
import rcic.RcicTypedFunRecPins

/-!
# S6-4 class (a) — the Acc row: gates at the `pinAccEnvA` fixture

The step-indexed `iotaErasesTUA_frec`/`iotaCorrTUA_frec` of
`RcicIotaFunRecCorr` take a per-firing gate `FrecFiringGates`.  This module
discharges them at `pinAccEnvA` (`RcicAnnAccFrecPin`): the indexed Acc-shaped
environment whose family `AccT : Π (x : Sort 0), Sort 1` (at `10`) and
constructor `intro : Π (x:S0), (Π (y:S0), R y x → AccT y) → AccT x` (at `11`,
over the opaque `R` axiom at `9`) carry a function-recursive field — the pin
designed to sit outside `EnvNoFunA` (`pinAcc_not_noFunA`).

The firing is unique: `iotaGroupA pinAccEnvA r c` succeeds only at `r = 12`,
`c = 11` (`pinAcc_group_inv`).  On the erased side the `.frec` field reads
`.drec` (`FieldA.erase`), so `eraseMember pinAccIntroA`'s stored type is the
honest Π-domain `Π (x:S0), (Π (y:S0), R y x → AccT y) → AccT x` — the typed
field analysis still classifies it `.recursive 2` (the inner `R y x`
hypothesis binder counts).

## Contents

- `pinAcc_normErase` — `EnvNormEraseA pinAccEnvA`.
- `pinAcc_group_inv` — every `iotaGroupA` hit is the `intro`/`AccT`/`rec`
  group at `12`/`11`.
- `paEnvWfT_erase` — `EnvWfT (eraseEnv pinAccEnvA)`: the axiom `R` step, then
  the group step (`AccT` family, `intro`, the AnySort recursor), mirroring
  `RcicTypedGroupPinsVec`'s indexed-family template.
- `pinAcc_gates` — the per-firing `FrecFiringGates` at `pinAccEnvA`.
- `pinAcc_iotaErasesTUA` — `IotaErasesTUA pinAccEnvA`.

`closure_claim` stays `0`.
-/

namespace Rcic.Declarative.Ann

/-- `EnvNormEraseA` at `pinAccEnvA`: the only `.constructorM` member is
    `pinAccIntroA`, whose `normA` is stored already normalized. -/
theorem pinAcc_normErase : EnvNormEraseA pinAccEnvA := by
  intro r m hm hmc T hT
  rcases pinAcc_mem hm with ⟨hr, rfl⟩ | ⟨hr, rfl⟩ | ⟨hr, rfl⟩ | ⟨hr, rfl⟩
  · simp [pinAccRelA] at hmc
  · simp [pinAccFamA] at hmc
  · have hTe : T = ctorTypeA 10 (canonLevelsA 0) (.succ .zero) []
        [.plain (.sort .zero) (.succ .zero), pinAccFieldA] [.bvar 0] :=
      Option.some.inj hT.symm
    subst hTe; rfl
  · simp [pinAccRecMemberA] at hmc

/-- the one group `iotaGroupA` can return at `pinAccEnvA`: recursor `12`,
    constructor `11`, family `10` — `nparams = 0`, `nindices = 1`,
    `nMinors = 1`, `ctorIdx = 0`. -/
theorem pinAcc_group_hit :
    iotaGroupA pinAccEnvA 12 11 =
      some ⟨pinAccRecMemberA, pinAccIntroA, pinAccFamA, 11, 10, 0, 1, 1, 0⟩ := rfl

/-- `iotaGroupA` at `pinAccEnvA` only hits the `intro`/`AccT`/`rec` group. -/
theorem pinAcc_group_inv {r c : Nat} {g : IotaGroupA}
    (hg : iotaGroupA pinAccEnvA r c = some g) :
    r = 12 ∧ c = 11 ∧ g.recM = pinAccRecMemberA ∧ g.ctorM = pinAccIntroA ∧
      g.famM = pinAccFamA ∧ g.ctorRef = 11 ∧ g.familyRef = 10 ∧ g.nparams = 0 ∧
      g.nindices = 1 ∧ g.nMinors = 1 ∧ g.ctorIdx = 0 := by
  rcases hr' : pinAccEnvA.members r with _ | rm
  · unfold iotaGroupA at hg; rw [hr'] at hg; exact Option.noConfusion hg
  rcases hc' : pinAccEnvA.members c with _ | cm
  · unfold iotaGroupA at hg; rw [hr', hc'] at hg; exact Option.noConfusion hg
  rcases pinAcc_mem hr' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases pinAcc_mem hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- fifteen of the sixteen member pairs fail the class guards; only (12, 11) hits
  all_goals first
    | exact Option.noConfusion hg
    | (have h := Option.some.inj (pinAcc_group_hit.symm.trans hg)
       cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-! ## the erased environment's `EnvWfT`

`eraseEnv pinAccEnvA`'s members are the axiom `R` at `9` and the group's
erasures at `10`–`12`: `.frec` reads `.drec` on the erased side
(`FieldA.erase`), so `eraseMember pinAccIntroA`'s stored type is the honest
Π `Π (x : Sort 0), (Π (y : Sort 0), R y x → AccT y) → AccT x` — the indexed
Acc eliminator (`AccT` at `10`, `intro` at `11`, `rec` at `12`) over the
axiom base.  `EnvWfT` is built member-by-member, mirroring `pfEnvWfT` and the
indexed `vecEnvUWfT`. -/

/-- the erased axiom member record: `R : S0 → S0 → S0`. -/
abbrev paRelT : CheckedMember := eraseMember pinAccRelA
/-- the erased family: `AccT : Π (x : Sort 0), Sort 1`. -/
abbrev paFamT : CheckedMember := eraseMember pinAccFamA
/-- the erased constructor: `intro : Π (x:S0), (Π (y:S0), R y x → AccT y) → AccT x`. -/
abbrev paIntroT : CheckedMember := eraseMember pinAccIntroA
/-- the erased recursor. -/
abbrev paRecT : CheckedMember := eraseMember pinAccRecMemberA
/-- `R`'s env: `emptyEnv` + axiom at `9`. -/
abbrev paRelEnvT : ResolvedEnv := extendEnv emptyEnv 9 paRelT
/-- `pfRelEnvT` + `AccT` at `10`. -/
abbrev paFamEnvT : ResolvedEnv := extendEnv paRelEnvT 10 paFamT
/-- `pfFamEnvT` + `intro` at `11`. -/
abbrev paSupEnvT : ResolvedEnv := extendEnv paFamEnvT 11 paIntroT
/-- `pfSupEnvT` + `rec` at `12` — `eraseEnv pinAccEnvA`. -/
abbrev paEnvT : ResolvedEnv := extendEnv paSupEnvT 12 paRecT

/-- intro's erased field-1 domain: `Π (y:S0), R y x → AccT y`, at ctx `[x:S0]`. -/
abbrev paFieldDom : Expr Nat :=
  .pi (.sort .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1))
      (.app (.const 10 []) (.bvar 1)))

/-- the recursor's motive slot: `Π (x:S0), AccT x → Sort (param 0)`. -/
abbrev paMotTy : Expr Nat :=
  .pi (.sort .zero) (.pi (.app (.const 10 []) (.bvar 0)) (.sort (.param 0)))

/-- intro's minor: `Π (x:S0) (g : Π y, R y x → AccT y) (ih : Π y, R y x → M y (g y h)),
    M x (intro x g)` — the `derivedMinor` output for the `.recursive 2` field. -/
abbrev paMinorTy : Expr Nat :=
  .pi (.sort .zero)
    (.pi paFieldDom
      (.pi (.pi (.sort .zero)
            (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2))
              (.app (.app (.bvar 4) (.bvar 1))
                (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))))
        (.app (.app (.bvar 3) (.bvar 2))
          (.app (.app (.const 11 []) (.bvar 2)) (.bvar 1)))))

/-- the erased group's env as `extendEnv`'s: memberwise identical to
    `eraseEnv pinAccEnvA`. -/
theorem paEnvT_eq : eraseEnv pinAccEnvA = paEnvT := by
  apply congrArg ResolvedEnv.mk
  funext r
  by_cases h12 : r = 12 <;> by_cases h11 : r = 11 <;> by_cases h10 : r = 10 <;>
    by_cases h9 : r = 9 <;>
    simp [h12, h11, h10, h9, pinAccEnvA, pinAccGroupEnvA, pinAccFamEnvA,
      pinAccRelEnvA, eraseEnv, extendEnvA, paEnvT, paSupEnvT, paFamEnvT,
      paRelEnvT, extendEnv, paRelT, paFamT, paIntroT, paRecT, emptyEnvA, emptyEnv]

/-- `R`'s const typing (untyped judgment), at any env carrying the axiom member. -/
def paRelConstTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h9 : E.members 9 = some paRelT) :
    HasTy E n Γ (.const 9 []) (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero))) :=
  HasTy.const _ 9 [] paRelT h9 rfl (fun _ hx => nomatch hx)

/-- the field domain `Π (y:S0), R y x → AccT y : Sort (imax 1 (imax 0 1))`, at
    ctx `[x : S0]` (untyped judgment). -/
def paFieldDomTy {E : ResolvedEnv} {n : Nat}
    (h9 : E.members 9 = some paRelT) (h10 : E.members 10 = some paFamT) :
    HasTy E n [.assumption (.sort .zero)] paFieldDom
      (.sort (.imax (.succ .zero) (.imax .zero (.succ .zero)))) :=
  HasTy.pi _ (.sort .zero) (.succ .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1))
      (.app (.const 10 []) (.bvar 1)))
    (.imax .zero (.succ .zero))
    (HasTy.sort _ .zero)
    (HasTy.pi _ (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1)) .zero
      (.app (.const 10 []) (.bvar 1)) (.succ .zero)
      (HasTy.app _ (.app (.const 9 []) (.bvar 0)) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTy.app _ (.const 9 []) (.bvar 0) (.sort .zero) (.pi (.sort .zero) (.sort .zero))
          (paRelConstTy h9)
          (HasTy.bvar _ 0 (.sort .zero) rfl))
        (HasTy.bvar _ 1 (.sort .zero) rfl))
      (HasTy.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort (.succ .zero))
        (HasTy.const _ 10 [] paFamT h10 rfl (fun _ hx => nomatch hx))
        (HasTy.bvar _ 1 (.sort .zero) rfl)))

/-- the field domain in the typed judgment (the view's `CtorTypedT` content). -/
def paFieldDomTyT {E : ResolvedEnv} {n : Nat}
    (h9 : E.members 9 = some paRelT) (h10 : E.members 10 = some paFamT) :
    HasTyT E n [.assumption (.sort .zero)] paFieldDom
      (.sort (.imax (.succ .zero) (.imax .zero (.succ .zero)))) :=
  HasTyT.pi _ (.sort .zero) (.succ .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1))
      (.app (.const 10 []) (.bvar 1)))
    (.imax .zero (.succ .zero))
    (HasTyT.sort _ .zero)
    (HasTyT.pi _ (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1)) .zero
      (.app (.const 10 []) (.bvar 1)) (.succ .zero)
      (HasTyT.app _ (.app (.const 9 []) (.bvar 0)) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTyT.app _ (.const 9 []) (.bvar 0) (.sort .zero) (.pi (.sort .zero) (.sort .zero))
          (HasTyT.const _ 9 [] paRelT h9 rfl rfl)
          (HasTyT.bvar _ 0 (.sort .zero) rfl))
        (HasTyT.bvar _ 1 (.sort .zero) rfl))
      (HasTyT.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort (.succ .zero))
        (HasTyT.const _ 10 [] paFamT h10 rfl rfl)
        (HasTyT.bvar _ 1 (.sort .zero) rfl)))

/-- the family's view: no params, one index domain `Sort 0`, result `Sort 1`. -/
def paFamViewT (E : ResolvedEnv) (h : E.members 10 = some paFamT) : PolicyFamilyView E where
  ref := 10
  member := paFamT
  present := h
  hasClass := rfl
  parameters := []
  indices := [.sort .zero]
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j => match j with | ⟨0, _⟩ => .succ .zero
    bounded := fun j => match j with | ⟨0, _⟩ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort (n := 0) [] .zero
  }

/-- `intro`'s view: fields `[x : S0, g : Π y, R y x → AccT y]`, result index `x`. -/
def paIntroViewT (E : ResolvedEnv) (h9 : E.members 9 = some paRelT)
    (h10 : E.members 10 = some paFamT) :
    PolicyConstructorView E (paFamViewT E h10) paIntroT where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.sort .zero, paFieldDom]
  resultIndices := [.bvar 1]
  parameterCount := rfl
  indexCount := rfl
  storedType := by with_unfolding_all rfl
  domainsTyped := {
    levels := fun j => match j with
      | ⟨0, _⟩ => .succ .zero
      | ⟨1, _⟩ => .imax (.succ .zero) (.imax .zero (.succ .zero))
    bounded := fun j => match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    hasType := fun j => match j with
      | ⟨0, _⟩ => HasTy.sort (n := 0) [] .zero
      | ⟨1, _⟩ => paFieldDomTy h9 h10
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun e he => by
    simp only [List.mem_singleton] at he
    subst he
    rfl

/-- `imax 1 (imax 0 1) ≤ₙ 1`: the Acc field's `Sort (imax 1 (imax 0 1))`
    fits the `Sort 1` family. -/
theorem leN_imax_acc :
    leN (.imax (.succ .zero) (.imax .zero (.succ .zero))) (.succ .zero) := by
  intro ρ x y hx hy
  have e : eval ρ (.imax (.succ .zero) (.imax .zero (.succ .zero))) = some 1 := rfl
  have e' : eval ρ (.succ .zero) = some 1 := rfl
  rw [e] at hx
  rw [e'] at hy
  have hx1 : x = 1 := (Option.some.inj hx).symm
  have hy1 : y = 1 := (Option.some.inj hy).symm
  subst hx1
  subst hy1
  exact Nat.le_refl 1

/-- `intro`'s field universes: `x : Sort 0` at `1`, `g`'s domain at
    `imax 1 (imax 0 1)` — each bounded by the family's `Sort 1`. -/
theorem paIntroUniv {E : ResolvedEnv} {h9 : E.members 9 = some paRelT}
    {h10 : E.members 10 = some paFamT} :
    FieldUniverseAdmitted (paIntroViewT E h9 h10) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
  | ⟨1, _⟩ =>
      exact Or.inr ⟨uniformType_succ_zero, leN_imax_acc⟩

/-- `intro` sits before any `10`-recursor: `paFamEnvT` has only the axiom
    `9` and the family `10`. -/
theorem paBefore : CtorBeforeRecursors paFamEnvT paIntroT := by
  refine ⟨10, rfl, ?_⟩
  intro rr rm hm hc
  by_cases h10 : rr = 10
  · subst h10
    rw [show paFamEnvT.members 10 = some paFamT from rfl] at hm
    cases hm
    exact absurd hc (by decide)
  · rw [members_extendEnv_ne _ _ _ h10] at hm
    by_cases h9 : rr = 9
    · subst h9
      rw [show paRelEnvT.members 9 = some paRelT from rfl] at hm
      cases hm
      exact absurd hc (by decide)
    · rw [members_extendEnv_ne _ _ _ h9] at hm
      exact Option.noConfusion hm

/-- no `AccT` constructor inside `(10, 11)`, none outside it in
    `paFamEnvT`. -/
theorem paContig : CtorContiguous paFamEnvT 11 paIntroT := by
  refine ⟨10, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd (And.intro hl hr) (by omega)
  · intro c ⟨cm, hm, hc, _⟩
    by_cases h10 : c = 10
    · subst h10
      rw [show paFamEnvT.members 10 = some paFamT from rfl] at hm
      cases hm
      exact absurd hc (by decide)
    · rw [members_extendEnv_ne _ _ _ h10] at hm
      by_cases h9 : c = 9
      · subst h9
        rw [show paRelEnvT.members 9 = some paRelT from rfl] at hm
        cases hm
        exact absurd hc (by decide)
      · rw [members_extendEnv_ne _ _ _ h9] at hm
        exact Option.noConfusion hm

/-- the fields analyze `[.nonrecursive, .recursive 2]` — permitted — in
    `paFamEnvT`. -/
theorem paIntroFieldsFam : CtorFieldsPermitted (paIntroViewT paFamEnvT rfl rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 24, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.recursive 2, 24, [.bvar 1], rfl⟩

/-- the same in `paSupEnvT` (the recursor admission's own check). -/
theorem paIntroFieldsSup : CtorFieldsPermitted (paIntroViewT paSupEnvT rfl rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 24, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.recursive 2, 24, [.bvar 1], rfl⟩

/-- `AccT` is admitted in `paRelEnvT`. -/
def paFamAdmitted : IndGroupAdmitted paRelEnvT 10 paFamT :=
  .family rfl (paFamViewT paFamEnvT rfl) rfl rfl (Or.inr uniformType_succ_zero)

/-- `intro` is admitted in `paFamEnvT`. -/
def paIntroAdmitted : IndGroupAdmitted paFamEnvT 11 paIntroT :=
  .constructor (paFamViewT paFamEnvT rfl) (paIntroViewT paFamEnvT rfl rfl) rfl
    paBefore paContig paIntroUniv paIntroFieldsFam

/-- the recursor admission: family `10`, the one constructor `intro` at
    `11`, AnySort at `Sort 1` (uniform-type family). -/
def paGroupAdm : RecursorEliminationAdmitted paSupEnvT 12 paRecT where
  family := paFamViewT paSupEnvT rfl
  constructors := [paIntroT]
  constructorViews
    | ⟨0, _⟩ => paIntroViewT paSupEnvT rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [paMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

/-- the group's census: `intro` at `11` is the only `AccT`-constructor
    below `12`. -/
theorem paCensus : CtorCensus paSupEnvT 10 12 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hm, hc, hfam⟩
    by_cases h11 : c = 11
    · subst h11
      rw [show paSupEnvT.members 11 = some paIntroT from rfl] at hm
      cases hm
      exact ⟨by omega, by omega⟩
    · rw [members_extendEnv_ne _ _ _ h11] at hm
      by_cases h10 : c = 10
      · subst h10
        rw [show paFamEnvT.members 10 = some paFamT from rfl] at hm
        cases hm
        exact absurd hc (by decide)
      · rw [members_extendEnv_ne _ _ _ h10] at hm
        by_cases h9 : c = 9
        · subst h9
          rw [show paRelEnvT.members 9 = some paRelT from rfl] at hm
          cases hm
          exact absurd hc (by decide)
        · rw [members_extendEnv_ne _ _ _ h9] at hm
          exact Option.noConfusion hm
  · intro ⟨hl, hr⟩
    have hc : c = 11 := by omega
    subst hc
    exact ⟨paIntroT, rfl, rfl, rfl⟩

/-- the derived minor is `paMinorTy` at the two-shape list. -/
theorem paMinor_derived :
    derivedMinor paGroupAdm ⟨0, by decide⟩ 24 [.nonrecursive, .recursive 2] =
      some paMinorTy := rfl

theorem paMinorMatch : MinorPremisesMatch paGroupAdm := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.nonrecursive, .recursive 2], 24, rfl, rfl⟩

/-- the equation's context: `g`, `x`, the index, the minor, the motive —
    innermost first. -/
def paIotaCtx : LCtx :=
  [.assumption paFieldDom, .assumption (.sort .zero), .assumption (.sort .zero),
    .assumption paMinorTy, .assumption paMotTy]

/-- `R y x` at the `y`-extended context — the inner λ's domain. -/
abbrev paRyxX : Expr Nat := .app (.app (.const 9 []) (.bvar 0)) (.bvar 2)

/-- the λ-wrapped recursive call: `fun (y:S0) (h : R y x) =>
    rec M minor y (g y h)`. -/
def paCall : Expr Nat :=
  .lam (.sort .zero)
    (.lam paRyxX
      (.app (.app (.app (.app (.const 12 [.param 0]) (.bvar 6)) (.bvar 5))
        (.bvar 1)) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))

/-- the schema admission derives: `minor x g (λ y h, rec M minor y (g y h))`. -/
def paSchema : Expr Nat :=
  .app (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) paCall

/-- the equation's type: `M x (intro x g)`. -/
def paEqTy : Expr Nat :=
  .app (.app (.bvar 4) (.bvar 1)) (.app (.app (.const 11 []) (.bvar 1)) (.bvar 0))

theorem paSchema_derived :
    iotaSchemaAt paGroupAdm ⟨0, by decide⟩ 24 [.nonrecursive, .recursive 2] =
      some paSchema := rfl

theorem paEquation_shape :
    equationDoms paGroupAdm ⟨0, by decide⟩ =
        some [paMotTy, paMinorTy, .sort .zero, .sort .zero, paFieldDom] ∧
      iotaEquationType paGroupAdm ⟨0, by decide⟩ = paEqTy := ⟨rfl, rfl⟩

/-- the recursor's head, wherever `12` is present (untyped judgment). -/
def paRecHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h12 : E.members 12 = some paRecT) :
    HasTy E n Γ (.const 12 [.param 0]) paRecT.mtype :=
  HasTy.const _ 12 [.param 0] paRecT h12 rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

/-- the equation in the untyped judgment: `minor x g (λ y h, rec M minor
    y (g y h)) : M x (intro x g)`. -/
def paIotaTy : HasTy paEnvT 1 paIotaCtx paSchema paEqTy := by
  have hMn : HasTy paEnvT 1 paIotaCtx (.bvar 3) (lift 0 4 paMinorTy) :=
    HasTy.bvar _ 3 _ rfl
  have hX : HasTy paEnvT 1 paIotaCtx (.bvar 1) (.sort .zero) :=
    HasTy.bvar _ 1 _ rfl
  have hG : HasTy paEnvT 1 paIotaCtx (.bvar 0) (lift 0 1 paFieldDom) :=
    HasTy.bvar _ 0 _ rfl
  -- inside `λ (y : Sort 0)`: the domain `R y x` types at `Sort 0`
  have hY0 : HasTy paEnvT 1 (.assumption (.sort .zero) :: paIotaCtx)
      (.bvar 0) (.sort .zero) := HasTy.bvar _ 0 _ rfl
  have hX1 : HasTy paEnvT 1 (.assumption (.sort .zero) :: paIotaCtx)
      (.bvar 2) (.sort .zero) := HasTy.bvar _ 2 _ rfl
  have hRyx : HasTy paEnvT 1 (.assumption (.sort .zero) :: paIotaCtx)
      paRyxX (.sort .zero) :=
    HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _ (paRelConstTy rfl) hY0) hX1
  -- inside `λ (y : S0) (h : R y x)`: the recursive call
  have hRec : HasTy paEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx)
      (.const 12 [.param 0]) (instantiateLevels [.param 0] paRecT.mtype) :=
    paRecHead rfl
  have hM'' : HasTy paEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 6) (lift 0 7 paMotTy) :=
    HasTy.bvar _ 6 _ rfl
  have hMn'' : HasTy paEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 5) (lift 0 6 paMinorTy) :=
    HasTy.bvar _ 5 _ rfl
  have hY'' : HasTy paEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 1) (.sort .zero) :=
    HasTy.bvar _ 1 _ rfl
  have hG'' : HasTy paEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 2) (lift 0 3 paFieldDom) :=
    HasTy.bvar _ 2 _ rfl
  have hH'' : HasTy paEnvT 1 (.assumption paRyxX ::
        .assumption (.sort .zero) :: paIotaCtx) (.bvar 0) (lift 0 1 paRyxX) :=
    HasTy.bvar _ 0 _ rfl
  exact HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ hMn hX) hG)
    (HasTy.lam _ (.sort .zero) (.succ .zero) _ _ (HasTy.sort _ .zero)
      (HasTy.lam _ paRyxX .zero _ _ hRyx
        (HasTy.app _ _ _ _ _
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _
              (HasTy.app _ _ _ _ _ hRec hM'')
              hMn'')
            hY'')
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _ hG'' hY'')
            hH''))))

def paIotaLegacy : IotaEquationTyped paGroupAdm ⟨0, by decide⟩ 24
    [.nonrecursive, .recursive 2] := by
  unfold IotaEquationTyped
  rw [paEquation_shape.1, paSchema_derived]
  exact paIotaTy

/-- the descriptor clause: the fields read `[.nonrecursive, .recursive 2]`
    at fuel `24`, and the equation types. -/
def paIotaClause : IotaDescriptorClause paSupEnvT paGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive, .recursive 2]
  fuelAt := fun _ => 24
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => paIotaLegacy

/-- `rec` is admitted in `paSupEnvT`. -/
def paRecAdmitted : IndGroupAdmitted paSupEnvT 12 paRecT :=
  .recursor paGroupAdm rfl paCensus
    (fun i => match i with | ⟨0, _⟩ => paIntroUniv)
    (fun i => match i with | ⟨0, _⟩ => paIntroFieldsSup)
    paMinorMatch paIotaClause

/-- `R`'s stored type in the typed judgment at `emptyEnv`. -/
def paRelTyT : HasTyT emptyEnv 0 []
    (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero)))
    (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .pi [] _ _ _ _ (HasTyT.sort _ .zero)
    (.pi _ _ _ _ _ (HasTyT.sort _ .zero) (HasTyT.sort _ .zero))

/-- `AccT`'s stored type `Π (x : Sort 0), Sort 1` in the typed judgment. -/
def paFamTyT : HasTyT paRelEnvT 0 [] (.pi (.sort .zero) (.sort (.succ .zero)))
    (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
  .pi [] _ _ _ _ (HasTyT.sort _ .zero) (HasTyT.sort _ (.succ .zero))

/-- `intro`'s stored type's sort. -/
def paIntroSortU : Level :=
  .imax (.succ .zero)
    (.imax (.imax (.succ .zero) (.imax .zero (.succ .zero))) (.succ .zero))

/-- `intro`'s stored type types in `paFamEnvT` — `x` at `1`, the field
    domain at `imax 1 (imax 0 1)`, the family target at `1`. -/
def paIntroTyT : HasTyT paFamEnvT 0 []
    (.pi (.sort .zero) (.pi paFieldDom (.app (.const 10 []) (.bvar 1))))
    (.sort paIntroSortU) :=
  .pi [] _ _ _ _ (HasTyT.sort _ .zero)
    (.pi _ _ _ _ _ (paFieldDomTyT rfl rfl)
      (HasTyT.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort (.succ .zero))
        (HasTyT.const _ 10 [] paFamT rfl rfl rfl) (HasTyT.bvar _ 1 _ rfl)))

/-- the recursor's stored type's sort (the `inferT` answer, checked). -/
def paRecSortU : Level :=
  .imax (.imax (.succ .zero) (.imax (.succ .zero) (.succ (.param 0))))
    (.imax
      (.imax (.succ .zero)
        (.imax (.imax (.succ .zero) (.imax .zero (.succ .zero)))
          (.imax (.imax (.succ .zero) (.imax .zero (.param 0))) (.param 0))))
      (.imax (.succ .zero) (.imax (.succ .zero) (.param 0))))

theorem paRecTy_direct :
    inferT paSupEnvT 1 [] paRecT.mtype = some (.sort paRecSortU) := rfl

def paRecTyT : HasTyT paSupEnvT 1 [] paRecT.mtype (.sort paRecSortU) :=
  (tyAtC paSupEnvT 1 32 [] paRecT.mtype (.sort paRecSortU)).get (by
    have h : (tyAtC paSupEnvT 1 32 [] paRecT.mtype (.sort paRecSortU)).isSome = true := rfl
    exact h)

/-- the family's typed content: the one index `Sort 0` at level `1`. -/
theorem paFamTypedT : IndGroupTypedT paFamAdmitted := fun i =>
  match i with | ⟨0, _⟩ => ⟨HasTyT.sort _ .zero⟩

/-- `intro`'s typed content: each field types at its recorded level, its
    (zero) parameters mirror. -/
theorem paIntroTypedE {E : ResolvedEnv} (h9 : E.members 9 = some paRelT)
    (h10 : E.members 10 = some paFamT) :
    CtorTypedT (paIntroViewT E h9 h10) :=
  ⟨fun j => by
      match j with
      | ⟨0, _⟩ => exact ⟨HasTyT.sort _ .zero⟩
      | ⟨1, _⟩ => exact ⟨paFieldDomTyT h9 h10⟩,
    fun i => i.elim0⟩

theorem paIntroTyped : IndGroupTypedT paIntroAdmitted :=
  ⟨paFamTypedT, paIntroTypedE rfl rfl⟩

/-- the recursor's typed content, its ι equation typed by `tyAtC`. -/
theorem paRecTyped : IndGroupTypedT paRecAdmitted :=
  ⟨(fun i => match i with | ⟨0, _⟩ => ⟨HasTyT.sort _ .zero⟩),
   fun i => match i with | ⟨0, _⟩ => paIntroTypedE rfl rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 32 Γ e T) rfl⟩

/-- the axiom step: `R : Sort 0 → Sort 0 → Sort 0` at `9`. -/
def paRelWfT : EnvWfT paRelEnvT :=
  .axiom emptyEnv 9 _ _ EnvWfT.empty rfl paRelTyT (fun _ => rfl) rfl

/-- the group members, one after another. -/
def paMembersT :
    GroupMembersT paFamEnvT paRelEnvT [(10, paFamT), (11, paIntroT), (12, paRecT)]
      paEnvT :=
  .cons _ 10 paFamT _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    paFamAdmitted PUnit.unit _ paFamTyT (fun h => absurd h (by decide))
    paFamTypedT
    (.cons _ 11 paIntroT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide))
      rfl rfl rfl
      paIntroAdmitted PUnit.unit _ paIntroTyT (fun _ => ⟨paIntroTyT⟩) paIntroTyped
      (.cons _ 12 paRecT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide))
        rfl rfl rfl
        paRecAdmitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ paRecTyT
        (fun h => absurd h (by decide)) paRecTyped (.nil _)))

/-- `paEnvT` — the erased frec Acc environment — is a well-formed typed
    environment: the axiom `R`, then `AccT`, `intro`, `rec` as one group
    step. -/
def paEnvWfT : EnvWfT paEnvT :=
  .group paRelEnvT 10 paFamT [(11, paIntroT)] 12 paRecT paEnvT paRelWfT
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl paMembersT

/-- the erased side of `pinAccEnvA` is a well-formed typed environment. -/
def paEnvWfT_erase : EnvWfT (eraseEnv pinAccEnvA) := paEnvT_eq ▸ paEnvWfT


/-! ## the per-firing gates at `pinAccEnvA`

`pinAcc_group_inv` makes every `iotaGroupA` hit the `intro` group, and
`iotaReductA_some` pins the major's argument count at `2`.  The four
`FrecFiringGates` then discharge at fuel `24`: the fragment list is a
`DirectFieldFrag` on `x : Sort 0` then a `FunRecFrag` on
`Π (y:S0), R y x → AccT y`; the walk supplies hold at the free `X`/`ls`
because the field's free index `x` sits BELOW the inner telescope's
offset (`hARtel`/`hidx` are symbolic `instOff`-distribution proofs, not
the closed-term shortcuts `pinFrec` used); the stability check computes;
and the open schema is closed under `5`. -/

/-- `intro`'s erased field domains: `[Sort 0, Π (y:S0), R y x → AccT y]`. -/
theorem paIntroDomsA_erase :
    (piDomsA pinAccIntroA.mtypeA).map erase =
      [.sort .zero, paFieldDom] := rfl

/-- `intro`'s erased result is the family application `AccT x`. -/
theorem paIntroBody_erase :
    erase (piBodyA pinAccIntroA.mtypeA) = .app (.const 10 []) (.bvar 1) := rfl

/-- the fired shapes of `intro`'s NORMALIZED stored type — the read
    `iotaReductA` makes — are the nonrecursive index field then the
    function-recursive field at inner arity `2`. -/
theorem paIntroShapes_norm :
    ctorShapesA 10 0 (pinAccIntroA.normA.getD pinAccIntroA.mtypeA) =
      some [.nonrecursive, .recursive 2] := rfl

/-- `iotaReductA` success pins the major's argument count to the
    constructor's Π-count: `2`. -/
theorem pinAcc_nf {s : RecSpineA} {e' : ExprA}
    (hr : iotaReductA s
      ⟨pinAccRecMemberA, pinAccIntroA, pinAccFamA, 11, 10, 0, 1, 1, 0⟩ =
        some e') :
    (appsSpineA s.major).2.length = 2 := by
  obtain ⟨_, _, _, _, _, hlen, _⟩ := iotaReductA_some hr
  exact hlen

/-- `x : Sort 0` is a direct fragment: rigid, stable, fuel-covered, not a
    family application, no inner telescope. -/
theorem paS0Frag : FieldFrag (eraseEnv pinAccEnvA) 24 10 pinAccFamA.arity 0 1 0
    (.sort .zero) := by
  show DirectFieldFrag (eraseEnv pinAccEnvA) 24 10 pinAccFamA.arity 0 1 0
      (.sort .zero)
  exact ⟨rfl, rfl, by decide, fun h => absurd h (by decide), Or.inl rfl⟩

/-- `g : Π (y:S0), R y x → AccT y` is the function-recursive fragment at
    depth `1`: rigid (the axiom `R` and `AccT` are both opaque), stable
    tail `AccT y`, fuel `24` covers `esize 11 + piCount 2 + 3 = 16`, the
    tail is the canonical family application at `top = 2`, and the inner
    binders `y : S0`, `R y x` are family-free. -/
theorem paFieldFrag : FieldFrag (eraseEnv pinAccEnvA) 24 10 pinAccFamA.arity 0 1 1
    paFieldDom := by
  show FunRecFrag (eraseEnv pinAccEnvA) 24 10 pinAccFamA.arity 0 1 1 paFieldDom
  exact ⟨rfl, rfl, by decide, rfl, rfl⟩

/-- `paFieldDom` after the `x`-marker substitution the walk performs:
    `instantiate0 (bvar 1)` maps the free `x` (`bvar 1` at the `y`-binder)
    to the marker `bvar 2`. -/
abbrev paFieldDomM : Expr Nat :=
  .pi (.sort .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2))
      (.app (.const 10 []) (.bvar 1)))

/-- the canonical fuel read at the marker-substituted field domain. -/
theorem paFieldDomM_canon :
    piTelescopeFuel (eraseEnv pinAccEnvA) 24 paFieldDomM =
      some ((piTelE paFieldDomM).1, (piTelE paFieldDomM).2) := by
  rw [piTelE_piDomsOf paFieldDomM]
  exact piTelescopeFuel_of_tailStable paFieldDomM rfl rfl (by decide)

/-- the copy-side telescope reading at the free frame `X`/`ls`: `Φ`
    distributes over the Π-structure, the family-free inner binders stay,
    and the tail `AccT y` images at offset `2`.  Unlike `pinFrec`'s field
    this domain is NOT closed — `x` is free — so this is a genuine
    `instOff`-distribution proof, not the closed-term shortcut. -/
theorem paFieldDomM_hARtel (X : List (Expr Nat)) (ls : List Level) :
    piTelE (instPrefix X (instantiateLevels ls paFieldDomM)) =
      (telImgC 0 X ls (piTelE paFieldDomM).1,
        instOff (piTelE paFieldDomM).1.length X
          (instantiateLevels ls (piTelE paFieldDomM).2)) := by
  have hIL : instantiateLevels ls paFieldDomM = paFieldDomM := rfl
  rw [hIL]
  have htail : instOff 2 X
      (.app (.const 10 []) (.bvar 1) : Expr Nat) =
      .app (.const 10 []) (.bvar 1) := by
    rw [instOff_appC, instOff_constC, instOff_bvar_ltC X 2 1 (by decide)]
  have hstep : instPrefix X paFieldDomM =
      .pi (.sort .zero)
        (.pi (instOff 1 X
            (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2)))
          (.app (.const 10 []) (.bvar 1))) := by
    rw [← instOff_zero, instOff_piC, instOff_piC,
      instOff_closed 0 X (.sort .zero) rfl, htail]
  rw [hstep]
  show (([.sort .zero, instOff 1 X
        (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2))],
      .app (.const 10 []) (.bvar 1)) :
      List (Expr Nat) × Expr Nat) =
    ([instOff 0 X (instantiateLevels ls (.sort .zero)),
      instOff 1 X (instantiateLevels ls
        (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2)))],
     instOff 2 X
       (instantiateLevels ls (.app (.const 10 []) (.bvar 1))))
  rw [instOff_closed 0 X (instantiateLevels ls (.sort .zero)) rfl]
  rw [show instantiateLevels ls (.sort .zero : Expr Nat) = .sort .zero
      from rfl]
  rw [show instantiateLevels ls
      (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2)) =
      .app (.app (.const 9 []) (.bvar 0)) (.bvar 2) from rfl]
  rw [show instantiateLevels ls (.app (.const 10 []) (.bvar 1)) =
      .app (.const 10 []) (.bvar 1) from rfl, htail]

/-- the family-index image at the free frame: the tail's index `y` sits
    BELOW the inner telescope's offset `2`, so `instOff 2 X` leaves it —
    and the whole application — alone. -/
theorem paFieldDomM_hidx (X : List (Expr Nat)) (ls : List Level) :
    (familyIdx 0 (piTelE paFieldDomM).2).map
        (fun a => instOff (piTelE paFieldDomM).1.length X
          (instantiateLevels ls a)) =
      familyIdx 0 (instOff (piTelE paFieldDomM).1.length X
        (instantiateLevels ls (piTelE paFieldDomM).2)) := by
  show ([instOff 2 X (instantiateLevels ls (.bvar 1))] : List (Expr Nat)) =
    familyIdx 0 (instOff 2 X
      (instantiateLevels ls (.app (.const 10 []) (.bvar 1))))
  rw [show instantiateLevels ls (.bvar 1 : Expr Nat) = .bvar 1 from rfl,
    instOff_bvar_ltC X 2 1 (by decide)]
  rw [show instantiateLevels ls (.app (.const 10 []) (.bvar 1)) =
      .app (.const 10 []) (.bvar 1) from rfl,
    instOff_appC, instOff_constC, instOff_bvar_ltC X 2 1 (by decide)]
  rfl

/-- the two-field walk: `x` nonrecursive (marker `bvar 1`), `g`
    function-recursive (marker `bvar 0`, inner arity `2`). -/
theorem paSupplies (X : List (Expr Nat)) (ls : List Level) :
    WalkSuppliesC (eraseEnv pinAccEnvA) 24 X ls 0 1 [.bvar 1, .bvar 0]
      [.nonrecursive, .recursive 2]
      (.pi (.sort .zero) (.pi paFieldDom (.app (.const 10 []) (.bvar 1)))) := by
  refine WalkSuppliesC.supNonrec 1 [.bvar 0] [.recursive 2] (.sort .zero)
    (.pi paFieldDom (.app (.const 10 []) (.bvar 1))) ?_
  show WalkSuppliesC (eraseEnv pinAccEnvA) 24 X ls 0 1 [.bvar 0]
      [.recursive 2]
      (.pi paFieldDomM (.app (.const 10 []) (.bvar 2)))
  refine WalkSuppliesC.supFrec 0 [] [] paFieldDomM
    (.app (.const 10 []) (.bvar 2)) 1 paFieldDomM_canon rfl
    (paFieldDomM_hARtel X ls) (paFieldDomM_hidx X ls)
    (WalkSuppliesC.supNil [] _ rfl)

/-- `FrecFiringGates` at the unique `pinAccEnvA` firing, fuel `24`. -/
theorem pinAcc_gates {e e' : ExprA} {s : RecSpineA} {c : Nat} {g : IotaGroupA}
    (hs : recSpineA e = some s) (hc : spineHeadRefA s.major = some c)
    (hg : iotaGroupA pinAccEnvA s.recRef c = some g)
    (hr : iotaReductA s g = some e') :
    FrecFiringGates pinAccEnvA 24 s g := by
  cases s with
  | mk recRef ls pre major =>
    cases g with
    | mk recM ctorM famM ctorRef familyRef nparams nindices nMinors ctorIdx =>
      obtain ⟨hr12, hc11, hrecM, hctorM, hfamM, hcr, hf10, hnp, hni, hnM, hci⟩ :=
        pinAcc_group_inv hg
      subst hr12 hc11 hrecM hctorM hfamM hcr hf10 hnp hni hnM hci
      have hnf : (appsSpineA major).2.length = 2 := pinAcc_nf hr
      unfold FrecFiringGates
      refine ⟨?_, ?_, ?_, ?_⟩
      · change FieldFragList (eraseEnv pinAccEnvA) 24 10 pinAccFamA.arity 0 1 0
            [.sort .zero, paFieldDom]
        exact ⟨paS0Frag, paFieldFrag, trivial⟩
      · intro shapes X ls hsh
        change ctorShapesA 10 0 (pinAccIntroA.normA.getD pinAccIntroA.mtypeA) =
            some shapes at hsh
        rw [paIntroShapes_norm] at hsh; cases hsh
        change WalkSuppliesC (eraseEnv pinAccEnvA) 24 X ls 0 1
          (fieldBvars ((appsSpineA major).2.length)) [.nonrecursive, .recursive 2]
          (lift 0 ((appsSpineA major).2.length + 1 + 1 + 1)
            (ctorFieldTelRaw 0 ((piDomsA pinAccIntroA.mtypeA).map erase)
              (erase (piBodyA pinAccIntroA.mtypeA))))
        rw [hnf, paIntroDomsA_erase, paIntroBody_erase]
        show WalkSuppliesC (eraseEnv pinAccEnvA) 24 X ls 0 1 [.bvar 1, .bvar 0]
          [.nonrecursive, .recursive 2]
          (.pi (.sort .zero) (.pi paFieldDom (.app (.const 10 []) (.bvar 1))))
        exact paSupplies X ls
      · change iotaWitnessStableB (eraseEnv pinAccEnvA) 24
            ((piDomsA pinAccIntroA.mtypeA).map erase)
            (fieldBvars ((appsSpineA major).2.length))
            (lift 0 ((appsSpineA major).2.length + 1 + 1 + 1)
              (ctorFieldTelRaw 0 ((piDomsA pinAccIntroA.mtypeA).map erase)
                (erase (piBodyA pinAccIntroA.mtypeA)))) = true
        rw [hnf, paIntroDomsA_erase, paIntroBody_erase]
        change iotaWitnessStableB (eraseEnv pinAccEnvA) 24
            [.sort .zero, paFieldDom] [.bvar 1, .bvar 0]
            (.pi (.sort .zero) (.pi paFieldDom
              (.app (.const 10 []) (.bvar 1)))) = true
        have hmem9 : (eraseEnv pinAccEnvA).members 9 = some paRelT := rfl
        have hmem10 : (eraseEnv pinAccEnvA).members 10 = some paFamT := rfl
        have hS0 : constsMemberFuel (eraseEnv pinAccEnvA) (24 + 1)
            (.sort .zero : Expr Nat) = true := by
          simp only [constsMemberFuel]
        have hF : constsMemberFuel (eraseEnv pinAccEnvA) (24 + 1)
            paFieldDom = true := by
          simp only [paFieldDom, constsMemberFuel, hmem9, hmem10, transparent,
            paRelT, paFamT, eraseMember, pinAccRelA, pinAccFamA]
          rfl
        have hTel : constsMemberFuel (eraseEnv pinAccEnvA) (24 + 1)
            (.pi (.sort .zero) (.pi paFieldDom
              (.app (.const 10 []) (.bvar 1)))) = true := by
          simp only [paFieldDom, constsMemberFuel, hmem9, hmem10, transparent,
            paRelT, paFamT, eraseMember, pinAccRelA, pinAccFamA]
          rfl
        simp only [iotaWitnessStableB, List.all_cons, List.all_nil, hS0, hF,
          hTel, Bool.and_true, Bool.true_and]
        show (constsMemberFuel (eraseEnv pinAccEnvA) 25 (.bvar 1) &&
            constsMemberFuel (eraseEnv pinAccEnvA) 25 (.bvar 0)) = true
        simp only [constsMemberFuel]
        rfl
      · intro shapes schema hsh hopen
        change ctorShapesA 10 0 (pinAccIntroA.normA.getD pinAccIntroA.mtypeA) =
            some shapes at hsh
        rw [paIntroShapes_norm] at hsh; cases hsh
        change iotaOpenRhs (eraseEnv pinAccEnvA) 24
            (.const 12 (canonRecLevels pinAccRecMemberA.arity))
            (.bvar (((appsSpineA major).2.length) + 1 + (1 - 1 - 0)))
            (preMajorBvars 0 1 1 ((appsSpineA major).2.length)) 0 1
            [.nonrecursive, .recursive 2]
            (fieldBvars ((appsSpineA major).2.length))
            (lift 0 ((appsSpineA major).2.length + 1 + 1 + 1)
              (ctorFieldTelRaw 0 ((piDomsA pinAccIntroA.mtypeA).map erase)
                (erase (piBodyA pinAccIntroA.mtypeA)))) = some schema at hopen
        rw [hnf, paIntroDomsA_erase, paIntroBody_erase] at hopen
        have hcomp : iotaOpenRhs (eraseEnv pinAccEnvA) 24
            (.const 12 (canonRecLevels pinAccRecMemberA.arity))
            (.bvar (2 + 1 + (1 - 1 - 0)))
            (preMajorBvars 0 1 1 2) 0 1 [.nonrecursive, .recursive 2]
            [.bvar 1, .bvar 0]
            (.pi (.sort .zero) (.pi paFieldDom
              (.app (.const 10 []) (.bvar 1)))) = some _ := rfl
        change iotaOpenRhs (eraseEnv pinAccEnvA) 24
            (.const 12 (canonRecLevels pinAccRecMemberA.arity))
            (.bvar (2 + 1 + (1 - 1 - 0)))
            (preMajorBvars 0 1 1 2) 0 1 [.nonrecursive, .recursive 2]
            [.bvar 1, .bvar 0]
            (.pi (.sort .zero) (.pi paFieldDom
              (.app (.const 10 []) (.bvar 1)))) = some schema at hopen
        rw [hcomp] at hopen
        cases hopen
        change exprClosedAt (0 + 1 + 1 + 1 + (appsSpineA major).2.length) _ = true
        rw [hnf]
        rfl

/-- S6-4's Acc-shaped row: the union erase face at the indexed Acc
    fixture.  Every firing in `pinAccEnvA` factors through the unique
    `intro` group (`pinAcc_group_inv`), the gates hold (`pinAcc_gates`),
    and the erased side is `EnvWfT`-admitted (`paEnvWfT_erase`) — so a
    step of the copy's ι is a union derived-ι step of
    `eraseEnv pinAccEnvA`, past `EnvNoFunA`.

    As at `pinFrec`, the `ann` direction (`IotaCorrTUA`) is NOT stated:
    `EnvCorrAnnCert` reads the direct-fragment recognizer, which
    deliberately rejects frec witnesses — that remains the boundary. -/
theorem pinAcc_iotaErasesTUA : IotaErasesTUA pinAccEnvA := by
  obtain ⟨w, ⟨hT0⟩⟩ := pinAccRecTyAt0
  exact iotaErasesTUA_frecR (pinAccWfA w hT0) pinAcc_normErase paEnvWfT_erase 24
    (fun _ _ _ _ _ => pinAcc_gates)

#print axioms pinAcc_iotaErasesTUA

end Rcic.Declarative.Ann
