import rcic.RcicIotaFunRecCorr
import rcic.RcicIotaFunRecCorrR
import rcic.RcicAnnPropAccFrecPin
import rcic.RcicTypedFunRecPins

/-!
# class (c) — the Prop-valued Acc row: gates at the `pinPropAccEnvA` fixture

The step-indexed `iotaErasesTUA_frecR`/`iotaCorrTUA_frecR` of
`RcicIotaFunRecCorrR` take a per-firing gate `FrecFiringGates`.  This module
discharges them at `pinPropAccEnvA` (`RcicAnnPropAccFrecPin`): the Prop-valued,
LARGE-eliminating, indexed Acc-shaped environment whose family
`AccP : Π (x : Sort 0), Sort 0` (at `10`) and constructor
`intro : Π (x:S0), (Π (y:S0), R y x → AccP y) → AccP x` (at `11`, over the
opaque `R` axiom at `9`) carry a function-recursive field — the pin designed to
sit outside `EnvNoFunA` (`pinPropAcc_not_noFunA`) AND outside `PropElimOnlyA`
(`pinPropAcc_not_propElim`): the `.anySort` recursor selects via
`singletonProp` — the frec field's domain is Prop-leveled (`imax 1 (imax 0 0)`)
and the index field `x` is revealed in the result indices, so `AllFieldsSafe`
holds and a Prop family admits the large motive `.param 0`.

The firing is unique: `iotaGroupA pinPropAccEnvA r c` succeeds only at `r = 12`,
`c = 11` (`pinPropAcc_group_inv`).  On the erased side the `.frec` field reads
`.drec` (`FieldA.erase`), so `eraseMember pinPropAccIntroA`'s stored type is the
honest Π-domain `Π (x:S0), (Π (y:S0), R y x → AccP y) → AccP x` — the typed
field analysis still classifies it `.recursive 2` (the inner `R y x`
hypothesis binder counts).

## Contents

- `pinPropAcc_normErase` — `EnvNormEraseA pinPropAccEnvA`.
- `pinPropAcc_group_inv` — every `iotaGroupA` hit is the `intro`/`AccP`/`rec`
  group at `12`/`11`.
- `ppaEnvWfT_erase` — `EnvWfT (eraseEnv pinPropAccEnvA)`: the axiom `R` step, then
  the group step (`AccP` family, `intro`, the AnySort recursor), mirroring
  `RcicTypedGroupPinsVec`'s indexed-family template.
- `pinPropAcc_gates` — the per-firing `FrecFiringGates` at `pinPropAccEnvA`.
- `pinPropAcc_iotaErasesTUA` — `IotaErasesTUA pinPropAccEnvA`.

`closure_claim` stays `0`.
-/

namespace Rcic.Declarative.Ann

/-- `EnvNormEraseA` at `pinPropAccEnvA`: the only `.constructorM` member is
    `pinPropAccIntroA`, whose `normA` is stored already normalized. -/
theorem pinPropAcc_normErase : EnvNormEraseA pinPropAccEnvA := by
  intro r m hm hmc T hT
  rcases pinPropAcc_mem hm with ⟨hr, rfl⟩ | ⟨hr, rfl⟩ | ⟨hr, rfl⟩ | ⟨hr, rfl⟩
  · simp [pinPropAccRelA] at hmc
  · simp [pinPropAccFamA] at hmc
  · have hTe : T = ctorTypeA 10 (canonLevelsA 0) .zero []
        [.plain (.sort .zero) (.succ .zero), pinPropAccFieldA] [.bvar 0] :=
      Option.some.inj hT.symm
    subst hTe; rfl
  · simp [pinPropAccRecMemberA] at hmc

/-- the one group `iotaGroupA` can return at `pinPropAccEnvA`: recursor `12`,
    constructor `11`, family `10` — `nparams = 0`, `nindices = 1`,
    `nMinors = 1`, `ctorIdx = 0`. -/
theorem pinPropAcc_group_hit :
    iotaGroupA pinPropAccEnvA 12 11 =
      some ⟨pinPropAccRecMemberA, pinPropAccIntroA, pinPropAccFamA, 11, 10, 0, 1, 1, 0⟩ := rfl

/-- `iotaGroupA` at `pinPropAccEnvA` only hits the `intro`/`AccP`/`rec` group. -/
theorem pinPropAcc_group_inv {r c : Nat} {g : IotaGroupA}
    (hg : iotaGroupA pinPropAccEnvA r c = some g) :
    r = 12 ∧ c = 11 ∧ g.recM = pinPropAccRecMemberA ∧ g.ctorM = pinPropAccIntroA ∧
      g.famM = pinPropAccFamA ∧ g.ctorRef = 11 ∧ g.familyRef = 10 ∧ g.nparams = 0 ∧
      g.nindices = 1 ∧ g.nMinors = 1 ∧ g.ctorIdx = 0 := by
  rcases hr' : pinPropAccEnvA.members r with _ | rm
  · unfold iotaGroupA at hg; rw [hr'] at hg; exact Option.noConfusion hg
  rcases hc' : pinPropAccEnvA.members c with _ | cm
  · unfold iotaGroupA at hg; rw [hr', hc'] at hg; exact Option.noConfusion hg
  rcases pinPropAcc_mem hr' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases pinPropAcc_mem hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- fifteen of the sixteen member pairs fail the class guards; only (12, 11) hits
  all_goals first
    | exact Option.noConfusion hg
    | (have h := Option.some.inj (pinPropAcc_group_hit.symm.trans hg)
       cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-! ## the erased environment's `EnvWfT`

`eraseEnv pinPropAccEnvA`'s members are the axiom `R` at `9` and the group's
erasures at `10`–`12`: `.frec` reads `.drec` on the erased side
(`FieldA.erase`), so `eraseMember pinPropAccIntroA`'s stored type is the honest
Π `Π (x : Sort 0), (Π (y : Sort 0), R y x → AccP y) → AccP x` — the indexed
Acc eliminator (`AccP` at `10`, `intro` at `11`, `rec` at `12`) over the
axiom base.  `EnvWfT` is built member-by-member, mirroring `pfEnvWfT` and the
indexed `vecEnvUWfT`. -/

/-- the erased axiom member record: `R : S0 → S0 → S0`. -/
abbrev ppaRelT : CheckedMember := eraseMember pinPropAccRelA
/-- the erased family: `AccP : Π (x : Sort 0), Sort 0`. -/
abbrev ppaFamT : CheckedMember := eraseMember pinPropAccFamA
/-- the erased constructor: `intro : Π (x:S0), (Π (y:S0), R y x → AccP y) → AccP x`. -/
abbrev ppaIntroT : CheckedMember := eraseMember pinPropAccIntroA
/-- the erased recursor. -/
abbrev ppaRecT : CheckedMember := eraseMember pinPropAccRecMemberA
/-- `R`'s env: `emptyEnv` + axiom at `9`. -/
abbrev ppaRelEnvT : ResolvedEnv := extendEnv emptyEnv 9 ppaRelT
/-- `pfRelEnvT` + `AccP` at `10`. -/
abbrev ppaFamEnvT : ResolvedEnv := extendEnv ppaRelEnvT 10 ppaFamT
/-- `pfFamEnvT` + `intro` at `11`. -/
abbrev ppaSupEnvT : ResolvedEnv := extendEnv ppaFamEnvT 11 ppaIntroT
/-- `pfSupEnvT` + `rec` at `12` — `eraseEnv pinPropAccEnvA`. -/
abbrev ppaEnvT : ResolvedEnv := extendEnv ppaSupEnvT 12 ppaRecT

/-- intro's erased field-1 domain: `Π (y:S0), R y x → AccP y`, at ctx `[x:S0]`. -/
abbrev ppaFieldDom : Expr Nat :=
  .pi (.sort .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1))
      (.app (.const 10 []) (.bvar 1)))

/-- the recursor's motive slot: `Π (x:S0), AccP x → Sort (param 0)`. -/
abbrev ppaMotTy : Expr Nat :=
  .pi (.sort .zero) (.pi (.app (.const 10 []) (.bvar 0)) (.sort (.param 0)))

/-- intro's minor: `Π (x:S0) (g : Π y, R y x → AccP y) (ih : Π y, R y x → M y (g y h)),
    M x (intro x g)` — the `derivedMinor` output for the `.recursive 2` field. -/
abbrev ppaMinorTy : Expr Nat :=
  .pi (.sort .zero)
    (.pi ppaFieldDom
      (.pi (.pi (.sort .zero)
            (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2))
              (.app (.app (.bvar 4) (.bvar 1))
                (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))))
        (.app (.app (.bvar 3) (.bvar 2))
          (.app (.app (.const 11 []) (.bvar 2)) (.bvar 1)))))

/-- the erased group's env as `extendEnv`'s: memberwise identical to
    `eraseEnv pinPropAccEnvA`. -/
theorem ppaEnvT_eq : eraseEnv pinPropAccEnvA = ppaEnvT := by
  apply congrArg ResolvedEnv.mk
  funext r
  by_cases h12 : r = 12 <;> by_cases h11 : r = 11 <;> by_cases h10 : r = 10 <;>
    by_cases h9 : r = 9 <;>
    simp [h12, h11, h10, h9, pinPropAccEnvA, pinPropAccGroupEnvA, pinPropAccFamEnvA,
      pinPropAccRelEnvA, eraseEnv, extendEnvA, ppaEnvT, ppaSupEnvT, ppaFamEnvT,
      ppaRelEnvT, extendEnv, ppaRelT, ppaFamT, ppaIntroT, ppaRecT, emptyEnvA, emptyEnv]

/-- `R`'s const typing (untyped judgment), at any env carrying the axiom member. -/
def ppaRelConstTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h9 : E.members 9 = some ppaRelT) :
    HasTy E n Γ (.const 9 []) (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero))) :=
  HasTy.const _ 9 [] ppaRelT h9 rfl (fun _ hx => nomatch hx)

/-- the field domain `Π (y:S0), R y x → AccP y : Sort (imax 1 (imax 0 0))`, at
    ctx `[x : S0]` (untyped judgment). -/
def ppaFieldDomTy {E : ResolvedEnv} {n : Nat}
    (h9 : E.members 9 = some ppaRelT) (h10 : E.members 10 = some ppaFamT) :
    HasTy E n [.assumption (.sort .zero)] ppaFieldDom
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  HasTy.pi _ (.sort .zero) (.succ .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1))
      (.app (.const 10 []) (.bvar 1)))
    (.imax .zero .zero)
    (HasTy.sort _ .zero)
    (HasTy.pi _ (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1)) .zero
      (.app (.const 10 []) (.bvar 1)) .zero
      (HasTy.app _ (.app (.const 9 []) (.bvar 0)) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTy.app _ (.const 9 []) (.bvar 0) (.sort .zero) (.pi (.sort .zero) (.sort .zero))
          (ppaRelConstTy h9)
          (HasTy.bvar _ 0 (.sort .zero) rfl))
        (HasTy.bvar _ 1 (.sort .zero) rfl))
      (HasTy.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTy.const _ 10 [] ppaFamT h10 rfl (fun _ hx => nomatch hx))
        (HasTy.bvar _ 1 (.sort .zero) rfl)))

/-- the field domain in the typed judgment (the view's `CtorTypedT` content). -/
def ppaFieldDomTyT {E : ResolvedEnv} {n : Nat}
    (h9 : E.members 9 = some ppaRelT) (h10 : E.members 10 = some ppaFamT) :
    HasTyT E n [.assumption (.sort .zero)] ppaFieldDom
      (.sort (.imax (.succ .zero) (.imax .zero .zero))) :=
  HasTyT.pi _ (.sort .zero) (.succ .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1))
      (.app (.const 10 []) (.bvar 1)))
    (.imax .zero .zero)
    (HasTyT.sort _ .zero)
    (HasTyT.pi _ (.app (.app (.const 9 []) (.bvar 0)) (.bvar 1)) .zero
      (.app (.const 10 []) (.bvar 1)) .zero
      (HasTyT.app _ (.app (.const 9 []) (.bvar 0)) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTyT.app _ (.const 9 []) (.bvar 0) (.sort .zero) (.pi (.sort .zero) (.sort .zero))
          (HasTyT.const _ 9 [] ppaRelT h9 rfl rfl)
          (HasTyT.bvar _ 0 (.sort .zero) rfl))
        (HasTyT.bvar _ 1 (.sort .zero) rfl))
      (HasTyT.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTyT.const _ 10 [] ppaFamT h10 rfl rfl)
        (HasTyT.bvar _ 1 (.sort .zero) rfl)))

/-- the family's view: no params, one index domain `Sort 0`, result `Sort 0` (Prop). -/
def ppaFamViewT (E : ResolvedEnv) (h : E.members 10 = some ppaFamT) : PolicyFamilyView E where
  ref := 10
  member := ppaFamT
  present := h
  hasClass := rfl
  parameters := []
  indices := [.sort .zero]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j => match j with | ⟨0, _⟩ => .succ .zero
    bounded := fun j => match j with | ⟨0, _⟩ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort (n := 0) [] .zero
  }

/-- `intro`'s view: fields `[x : S0, g : Π y, R y x → AccP y]`, result index `x`. -/
def ppaIntroViewT (E : ResolvedEnv) (h9 : E.members 9 = some ppaRelT)
    (h10 : E.members 10 = some ppaFamT) :
    PolicyConstructorView E (ppaFamViewT E h10) ppaIntroT where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.sort .zero, ppaFieldDom]
  resultIndices := [.bvar 1]
  parameterCount := rfl
  indexCount := rfl
  storedType := by with_unfolding_all rfl
  domainsTyped := {
    levels := fun j => match j with
      | ⟨0, _⟩ => .succ .zero
      | ⟨1, _⟩ => .imax (.succ .zero) (.imax .zero .zero)
    bounded := fun j => match j with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    hasType := fun j => match j with
      | ⟨0, _⟩ => HasTy.sort (n := 0) [] .zero
      | ⟨1, _⟩ => ppaFieldDomTy h9 h10
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun e he => by
    simp only [List.mem_singleton] at he
    subst he
    rfl

/-- `intro`'s field universes: `AccP` is Prop-valued, so `UniformProp resultLevel`
    discharges every field — no `leN` bound needed. -/
theorem ppaIntroUniv {E : ResolvedEnv} {h9 : E.members 9 = some ppaRelT}
    {h10 : E.members 10 = some ppaFamT} :
    FieldUniverseAdmitted (ppaIntroViewT E h9 h10) := fun _ => Or.inl (fun _ => rfl)

/-- `intro` sits before any `10`-recursor: `ppaFamEnvT` has only the axiom
    `9` and the family `10`. -/
theorem ppaBefore : CtorBeforeRecursors ppaFamEnvT ppaIntroT := by
  refine ⟨10, rfl, ?_⟩
  intro rr rm hm hc
  by_cases h10 : rr = 10
  · subst h10
    rw [show ppaFamEnvT.members 10 = some ppaFamT from rfl] at hm
    cases hm
    exact absurd hc (by decide)
  · rw [members_extendEnv_ne _ _ _ h10] at hm
    by_cases h9 : rr = 9
    · subst h9
      rw [show ppaRelEnvT.members 9 = some ppaRelT from rfl] at hm
      cases hm
      exact absurd hc (by decide)
    · rw [members_extendEnv_ne _ _ _ h9] at hm
      exact Option.noConfusion hm

/-- no `AccP` constructor inside `(10, 11)`, none outside it in
    `ppaFamEnvT`. -/
theorem ppaContig : CtorContiguous ppaFamEnvT 11 ppaIntroT := by
  refine ⟨10, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd (And.intro hl hr) (by omega)
  · intro c ⟨cm, hm, hc, _⟩
    by_cases h10 : c = 10
    · subst h10
      rw [show ppaFamEnvT.members 10 = some ppaFamT from rfl] at hm
      cases hm
      exact absurd hc (by decide)
    · rw [members_extendEnv_ne _ _ _ h10] at hm
      by_cases h9 : c = 9
      · subst h9
        rw [show ppaRelEnvT.members 9 = some ppaRelT from rfl] at hm
        cases hm
        exact absurd hc (by decide)
      · rw [members_extendEnv_ne _ _ _ h9] at hm
        exact Option.noConfusion hm

/-- the fields analyze `[.nonrecursive, .recursive 2]` — permitted — in
    `ppaFamEnvT`. -/
theorem ppaIntroFieldsFam : CtorFieldsPermitted (ppaIntroViewT ppaFamEnvT rfl rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 24, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.recursive 2, 24, [.bvar 1], rfl⟩

/-- the same in `ppaSupEnvT` (the recursor admission's own check). -/
theorem ppaIntroFieldsSup : CtorFieldsPermitted (ppaIntroViewT ppaSupEnvT rfl rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 24, [], rfl⟩
  | ⟨1, _⟩ => exact ⟨.recursive 2, 24, [.bvar 1], rfl⟩

/-- `AccP` is admitted in `ppaRelEnvT` — `UniformProp`-profiled. -/
def ppaFamAdmitted : IndGroupAdmitted ppaRelEnvT 10 ppaFamT :=
  .family rfl (ppaFamViewT ppaFamEnvT rfl) rfl rfl (Or.inl (fun _ => rfl))

/-- `intro` is admitted in `ppaFamEnvT`. -/
def ppaIntroAdmitted : IndGroupAdmitted ppaFamEnvT 11 ppaIntroT :=
  .constructor (ppaFamViewT ppaFamEnvT rfl) (ppaIntroViewT ppaFamEnvT rfl rfl) rfl
    ppaBefore ppaContig ppaIntroUniv ppaIntroFieldsFam

/-- `intro`'s fields are all safe for the singleton test: `x` is revealed in the
    result indices, and the frec field's domain is Prop-leveled
    (`imax 1 (imax 0 0)` evaluates to `0`). -/
theorem ppaIntroSafe : (ppaIntroViewT ppaSupEnvT rfl rfl).AllFieldsSafe := fun j =>
  match j with
  | ⟨0, _⟩ => Or.inr (by
      show Expr.bvar 1 ∈ [Expr.bvar 1]
      exact List.mem_singleton_self _)
  | ⟨1, _⟩ => Or.inl (fun _ => rfl)
  | ⟨k+2, hk⟩ => absurd hk (by
      rw [show (ppaIntroViewT ppaSupEnvT rfl rfl).fields.length = 2 from rfl]
      omega)

/-- the recursor admission: family `10`, the one constructor `intro` at
    `11`, AnySort via `singletonProp` — `AllFieldsSafe` holds, so the Prop
    family LARGE-eliminates. -/
def ppaGroupAdm : RecursorEliminationAdmitted ppaSupEnvT 12 ppaRecT where
  family := ppaFamViewT ppaSupEnvT rfl
  constructors := [ppaIntroT]
  constructorViews
    | ⟨0, _⟩ => ppaIntroViewT ppaSupEnvT rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [ppaMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp (fun _ => rfl) rfl (fun i j =>
    match i with
    | ⟨0, _⟩ => ppaIntroSafe j
    | ⟨k+1, hk⟩ => absurd hk (by
        simp only [List.length_cons, List.length_nil]
        omega))
  recursorArity := rfl
  recursorType := rfl

/-- the group's census: `intro` at `11` is the only `AccP`-constructor
    below `12`. -/
theorem ppaCensus : CtorCensus ppaSupEnvT 10 12 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hm, hc, hfam⟩
    by_cases h11 : c = 11
    · subst h11
      rw [show ppaSupEnvT.members 11 = some ppaIntroT from rfl] at hm
      cases hm
      exact ⟨by omega, by omega⟩
    · rw [members_extendEnv_ne _ _ _ h11] at hm
      by_cases h10 : c = 10
      · subst h10
        rw [show ppaFamEnvT.members 10 = some ppaFamT from rfl] at hm
        cases hm
        exact absurd hc (by decide)
      · rw [members_extendEnv_ne _ _ _ h10] at hm
        by_cases h9 : c = 9
        · subst h9
          rw [show ppaRelEnvT.members 9 = some ppaRelT from rfl] at hm
          cases hm
          exact absurd hc (by decide)
        · rw [members_extendEnv_ne _ _ _ h9] at hm
          exact Option.noConfusion hm
  · intro ⟨hl, hr⟩
    have hc : c = 11 := by omega
    subst hc
    exact ⟨ppaIntroT, rfl, rfl, rfl⟩

/-- the derived minor is `ppaMinorTy` at the two-shape list. -/
theorem ppaMinor_derived :
    derivedMinor ppaGroupAdm ⟨0, by decide⟩ 24 [.nonrecursive, .recursive 2] =
      some ppaMinorTy := rfl

theorem ppaMinorMatch : MinorPremisesMatch ppaGroupAdm := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.nonrecursive, .recursive 2], 24, rfl, rfl⟩

/-- the equation's context: `g`, `x`, the index, the minor, the motive —
    innermost first. -/
def ppaIotaCtx : LCtx :=
  [.assumption ppaFieldDom, .assumption (.sort .zero), .assumption (.sort .zero),
    .assumption ppaMinorTy, .assumption ppaMotTy]

/-- `R y x` at the `y`-extended context — the inner λ's domain. -/
abbrev ppaRyxX : Expr Nat := .app (.app (.const 9 []) (.bvar 0)) (.bvar 2)

/-- the λ-wrapped recursive call: `fun (y:S0) (h : R y x) =>
    rec M minor y (g y h)`. -/
def ppaCall : Expr Nat :=
  .lam (.sort .zero)
    (.lam ppaRyxX
      (.app (.app (.app (.app (.const 12 [.param 0]) (.bvar 6)) (.bvar 5))
        (.bvar 1)) (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))

/-- the schema admission derives: `minor x g (λ y h, rec M minor y (g y h))`. -/
def ppaSchema : Expr Nat :=
  .app (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) ppaCall

/-- the equation's type: `M x (intro x g)`. -/
def ppaEqTy : Expr Nat :=
  .app (.app (.bvar 4) (.bvar 1)) (.app (.app (.const 11 []) (.bvar 1)) (.bvar 0))

theorem ppaSchema_derived :
    iotaSchemaAt ppaGroupAdm ⟨0, by decide⟩ 24 [.nonrecursive, .recursive 2] =
      some ppaSchema := rfl

theorem ppaEquation_shape :
    equationDoms ppaGroupAdm ⟨0, by decide⟩ =
        some [ppaMotTy, ppaMinorTy, .sort .zero, .sort .zero, ppaFieldDom] ∧
      iotaEquationType ppaGroupAdm ⟨0, by decide⟩ = ppaEqTy := ⟨rfl, rfl⟩

/-- the recursor's head, wherever `12` is present (untyped judgment). -/
def ppaRecHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h12 : E.members 12 = some ppaRecT) :
    HasTy E n Γ (.const 12 [.param 0]) ppaRecT.mtype :=
  HasTy.const _ 12 [.param 0] ppaRecT h12 rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

/-- the equation in the untyped judgment: `minor x g (λ y h, rec M minor
    y (g y h)) : M x (intro x g)`. -/
def ppaIotaTy : HasTy ppaEnvT 1 ppaIotaCtx ppaSchema ppaEqTy := by
  have hMn : HasTy ppaEnvT 1 ppaIotaCtx (.bvar 3) (lift 0 4 ppaMinorTy) :=
    HasTy.bvar _ 3 _ rfl
  have hX : HasTy ppaEnvT 1 ppaIotaCtx (.bvar 1) (.sort .zero) :=
    HasTy.bvar _ 1 _ rfl
  have hG : HasTy ppaEnvT 1 ppaIotaCtx (.bvar 0) (lift 0 1 ppaFieldDom) :=
    HasTy.bvar _ 0 _ rfl
  -- inside `λ (y : Sort 0)`: the domain `R y x` types at `Sort 0`
  have hY0 : HasTy ppaEnvT 1 (.assumption (.sort .zero) :: ppaIotaCtx)
      (.bvar 0) (.sort .zero) := HasTy.bvar _ 0 _ rfl
  have hX1 : HasTy ppaEnvT 1 (.assumption (.sort .zero) :: ppaIotaCtx)
      (.bvar 2) (.sort .zero) := HasTy.bvar _ 2 _ rfl
  have hRyx : HasTy ppaEnvT 1 (.assumption (.sort .zero) :: ppaIotaCtx)
      ppaRyxX (.sort .zero) :=
    HasTy.app _ _ _ _ _
      (HasTy.app _ _ _ _ _ (ppaRelConstTy rfl) hY0) hX1
  -- inside `λ (y : S0) (h : R y x)`: the recursive call
  have hRec : HasTy ppaEnvT 1 (.assumption ppaRyxX ::
        .assumption (.sort .zero) :: ppaIotaCtx)
      (.const 12 [.param 0]) (instantiateLevels [.param 0] ppaRecT.mtype) :=
    ppaRecHead rfl
  have hM'' : HasTy ppaEnvT 1 (.assumption ppaRyxX ::
        .assumption (.sort .zero) :: ppaIotaCtx) (.bvar 6) (lift 0 7 ppaMotTy) :=
    HasTy.bvar _ 6 _ rfl
  have hMn'' : HasTy ppaEnvT 1 (.assumption ppaRyxX ::
        .assumption (.sort .zero) :: ppaIotaCtx) (.bvar 5) (lift 0 6 ppaMinorTy) :=
    HasTy.bvar _ 5 _ rfl
  have hY'' : HasTy ppaEnvT 1 (.assumption ppaRyxX ::
        .assumption (.sort .zero) :: ppaIotaCtx) (.bvar 1) (.sort .zero) :=
    HasTy.bvar _ 1 _ rfl
  have hG'' : HasTy ppaEnvT 1 (.assumption ppaRyxX ::
        .assumption (.sort .zero) :: ppaIotaCtx) (.bvar 2) (lift 0 3 ppaFieldDom) :=
    HasTy.bvar _ 2 _ rfl
  have hH'' : HasTy ppaEnvT 1 (.assumption ppaRyxX ::
        .assumption (.sort .zero) :: ppaIotaCtx) (.bvar 0) (lift 0 1 ppaRyxX) :=
    HasTy.bvar _ 0 _ rfl
  exact HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ hMn hX) hG)
    (HasTy.lam _ (.sort .zero) (.succ .zero) _ _ (HasTy.sort _ .zero)
      (HasTy.lam _ ppaRyxX .zero _ _ hRyx
        (HasTy.app _ _ _ _ _
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _
              (HasTy.app _ _ _ _ _ hRec hM'')
              hMn'')
            hY'')
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _ hG'' hY'')
            hH''))))

def ppaIotaLegacy : IotaEquationTyped ppaGroupAdm ⟨0, by decide⟩ 24
    [.nonrecursive, .recursive 2] := by
  unfold IotaEquationTyped
  rw [ppaEquation_shape.1, ppaSchema_derived]
  exact ppaIotaTy

/-- the descriptor clause: the fields read `[.nonrecursive, .recursive 2]`
    at fuel `24`, and the equation types. -/
def ppaIotaClause : IotaDescriptorClause ppaSupEnvT ppaGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive, .recursive 2]
  fuelAt := fun _ => 24
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => ppaIotaLegacy

/-- `rec` is admitted in `ppaSupEnvT`. -/
def ppaRecAdmitted : IndGroupAdmitted ppaSupEnvT 12 ppaRecT :=
  .recursor ppaGroupAdm rfl ppaCensus
    (fun i => match i with | ⟨0, _⟩ => ppaIntroUniv)
    (fun i => match i with | ⟨0, _⟩ => ppaIntroFieldsSup)
    ppaMinorMatch ppaIotaClause

/-- `R`'s stored type in the typed judgment at `emptyEnv`. -/
def ppaRelTyT : HasTyT emptyEnv 0 []
    (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero)))
    (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .pi [] _ _ _ _ (HasTyT.sort _ .zero)
    (.pi _ _ _ _ _ (HasTyT.sort _ .zero) (HasTyT.sort _ .zero))

/-- `AccP`'s stored type `Π (x : Sort 0), Sort 0` in the typed judgment. -/
def ppaFamTyT : HasTyT ppaRelEnvT 0 [] (.pi (.sort .zero) (.sort .zero))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] _ _ _ _ (HasTyT.sort _ .zero) (HasTyT.sort _ .zero)

/-- `intro`'s stored type's sort. -/
def ppaIntroSortU : Level :=
  .imax (.succ .zero)
    (.imax (.imax (.succ .zero) (.imax .zero .zero)) .zero)

/-- `intro`'s stored type types in `ppaFamEnvT` — `x` at `1`, the field
    domain at `imax 1 (imax 0 0)`, the family target at `0`. -/
def ppaIntroTyT : HasTyT ppaFamEnvT 0 []
    (.pi (.sort .zero) (.pi ppaFieldDom (.app (.const 10 []) (.bvar 1))))
    (.sort ppaIntroSortU) :=
  .pi [] _ _ _ _ (HasTyT.sort _ .zero)
    (.pi _ _ _ _ _ (ppaFieldDomTyT rfl rfl)
      (HasTyT.app _ (.const 10 []) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTyT.const _ 10 [] ppaFamT rfl rfl rfl) (HasTyT.bvar _ 1 _ rfl)))

/-- the recursor's stored type's sort (the `inferT` answer, checked). -/
def ppaRecSortU : Level :=
  .imax (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))
    (.imax
      (.imax (.succ .zero)
        (.imax (.imax (.succ .zero) (.imax .zero .zero))
          (.imax (.imax (.succ .zero) (.imax .zero (.param 0))) (.param 0))))
      (.imax (.succ .zero) (.imax .zero (.param 0))))

theorem ppaRecTy_direct :
    inferT ppaSupEnvT 1 [] ppaRecT.mtype = some (.sort ppaRecSortU) := rfl

def ppaRecTyT : HasTyT ppaSupEnvT 1 [] ppaRecT.mtype (.sort ppaRecSortU) :=
  (tyAtC ppaSupEnvT 1 32 [] ppaRecT.mtype (.sort ppaRecSortU)).get (by
    have h : (tyAtC ppaSupEnvT 1 32 [] ppaRecT.mtype (.sort ppaRecSortU)).isSome = true := rfl
    exact h)

/-- the family's typed content: the one index `Sort 0` at level `1`. -/
theorem ppaFamTypedT : IndGroupTypedT ppaFamAdmitted := fun i =>
  match i with | ⟨0, _⟩ => ⟨HasTyT.sort _ .zero⟩

/-- `intro`'s typed content: each field types at its recorded level, its
    (zero) parameters mirror. -/
theorem ppaIntroTypedE {E : ResolvedEnv} (h9 : E.members 9 = some ppaRelT)
    (h10 : E.members 10 = some ppaFamT) :
    CtorTypedT (ppaIntroViewT E h9 h10) :=
  ⟨fun j => by
      match j with
      | ⟨0, _⟩ => exact ⟨HasTyT.sort _ .zero⟩
      | ⟨1, _⟩ => exact ⟨ppaFieldDomTyT h9 h10⟩,
    fun i => i.elim0⟩

theorem ppaIntroTyped : IndGroupTypedT ppaIntroAdmitted :=
  ⟨ppaFamTypedT, ppaIntroTypedE rfl rfl⟩

/-- the recursor's typed content, its ι equation typed by `tyAtC`. -/
theorem ppaRecTyped : IndGroupTypedT ppaRecAdmitted :=
  ⟨(fun i => match i with | ⟨0, _⟩ => ⟨HasTyT.sort _ .zero⟩),
   fun i => match i with | ⟨0, _⟩ => ppaIntroTypedE rfl rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 32 Γ e T) rfl⟩

/-- the axiom step: `R : Sort 0 → Sort 0 → Sort 0` at `9`. -/
def ppaRelWfT : EnvWfT ppaRelEnvT :=
  .axiom emptyEnv 9 _ _ EnvWfT.empty rfl ppaRelTyT (fun _ => rfl) rfl

/-- the group members, one after another. -/
def ppaMembersT :
    GroupMembersT ppaFamEnvT ppaRelEnvT [(10, ppaFamT), (11, ppaIntroT), (12, ppaRecT)]
      ppaEnvT :=
  .cons _ 10 ppaFamT _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    ppaFamAdmitted PUnit.unit _ ppaFamTyT (fun h => absurd h (by decide))
    ppaFamTypedT
    (.cons _ 11 ppaIntroT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide))
      rfl rfl rfl
      ppaIntroAdmitted PUnit.unit _ ppaIntroTyT (fun _ => ⟨ppaIntroTyT⟩) ppaIntroTyped
      (.cons _ 12 ppaRecT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide))
        rfl rfl rfl
        ppaRecAdmitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ ppaRecTyT
        (fun h => absurd h (by decide)) ppaRecTyped (.nil _)))

/-- `ppaEnvT` — the erased frec Acc environment — is a well-formed typed
    environment: the axiom `R`, then `AccP`, `intro`, `rec` as one group
    step. -/
def ppaEnvWfT : EnvWfT ppaEnvT :=
  .group ppaRelEnvT 10 ppaFamT [(11, ppaIntroT)] 12 ppaRecT ppaEnvT ppaRelWfT
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl ppaMembersT

/-- the erased side of `pinPropAccEnvA` is a well-formed typed environment. -/
def ppaEnvWfT_erase : EnvWfT (eraseEnv pinPropAccEnvA) := ppaEnvT_eq ▸ ppaEnvWfT


/-! ## the per-firing gates at `pinPropAccEnvA`

`pinPropAcc_group_inv` makes every `iotaGroupA` hit the `intro` group, and
`iotaReductA_some` pins the major's argument count at `2`.  The four
`FrecFiringGates` then discharge at fuel `24`: the fragment list is a
`DirectFieldFrag` on `x : Sort 0` then a `FunRecFrag` on
`Π (y:S0), R y x → AccP y`; the walk supplies hold at the free `X`/`ls`
because the field's free index `x` sits BELOW the inner telescope's
offset (`hARtel`/`hidx` are symbolic `instOff`-distribution proofs, not
the closed-term shortcuts `pinFrec` used); the stability check computes;
and the open schema is closed under `5`. -/

/-- `intro`'s erased field domains: `[Sort 0, Π (y:S0), R y x → AccP y]`. -/
theorem ppaIntroDomsA_erase :
    (piDomsA pinPropAccIntroA.mtypeA).map erase =
      [.sort .zero, ppaFieldDom] := rfl

/-- `intro`'s erased result is the family application `AccP x`. -/
theorem ppaIntroBody_erase :
    erase (piBodyA pinPropAccIntroA.mtypeA) = .app (.const 10 []) (.bvar 1) := rfl

/-- the fired shapes of `intro`'s NORMALIZED stored type — the read
    `iotaReductA` makes — are the nonrecursive index field then the
    function-recursive field at inner arity `2`. -/
theorem ppaIntroShapes_norm :
    ctorShapesA 10 0 (pinPropAccIntroA.normA.getD pinPropAccIntroA.mtypeA) =
      some [.nonrecursive, .recursive 2] := rfl

/-- `iotaReductA` success pins the major's argument count to the
    constructor's Π-count: `2`. -/
theorem pinPropAcc_nf {s : RecSpineA} {e' : ExprA}
    (hr : iotaReductA s
      ⟨pinPropAccRecMemberA, pinPropAccIntroA, pinPropAccFamA, 11, 10, 0, 1, 1, 0⟩ =
        some e') :
    (appsSpineA s.major).2.length = 2 := by
  obtain ⟨_, _, _, _, _, hlen, _⟩ := iotaReductA_some hr
  exact hlen

/-- `x : Sort 0` is a direct fragment: rigid, stable, fuel-covered, not a
    family application, no inner telescope. -/
theorem ppaS0Frag : FieldFrag (eraseEnv pinPropAccEnvA) 24 10 pinPropAccFamA.arity 0 1 0
    (.sort .zero) := by
  show DirectFieldFrag (eraseEnv pinPropAccEnvA) 24 10 pinPropAccFamA.arity 0 1 0
      (.sort .zero)
  exact ⟨rfl, rfl, by decide, fun h => absurd h (by decide), Or.inl rfl⟩

/-- `g : Π (y:S0), R y x → AccP y` is the function-recursive fragment at
    depth `1`: rigid (the axiom `R` and `AccP` are both opaque), stable
    tail `AccP y`, fuel `24` covers `esize 11 + piCount 2 + 3 = 16`, the
    tail is the canonical family application at `top = 2`, and the inner
    binders `y : S0`, `R y x` are family-free. -/
theorem ppaFieldFrag : FieldFrag (eraseEnv pinPropAccEnvA) 24 10 pinPropAccFamA.arity 0 1 1
    ppaFieldDom := by
  show FunRecFrag (eraseEnv pinPropAccEnvA) 24 10 pinPropAccFamA.arity 0 1 1 ppaFieldDom
  exact ⟨rfl, rfl, by decide, rfl, rfl⟩

/-- `ppaFieldDom` after the `x`-marker substitution the walk performs:
    `instantiate0 (bvar 1)` maps the free `x` (`bvar 1` at the `y`-binder)
    to the marker `bvar 2`. -/
abbrev ppaFieldDomM : Expr Nat :=
  .pi (.sort .zero)
    (.pi (.app (.app (.const 9 []) (.bvar 0)) (.bvar 2))
      (.app (.const 10 []) (.bvar 1)))

/-- the canonical fuel read at the marker-substituted field domain. -/
theorem ppaFieldDomM_canon :
    piTelescopeFuel (eraseEnv pinPropAccEnvA) 24 ppaFieldDomM =
      some ((piTelE ppaFieldDomM).1, (piTelE ppaFieldDomM).2) := by
  rw [piTelE_piDomsOf ppaFieldDomM]
  exact piTelescopeFuel_of_tailStable ppaFieldDomM rfl rfl (by decide)

/-- the copy-side telescope reading at the free frame `X`/`ls`: `Φ`
    distributes over the Π-structure, the family-free inner binders stay,
    and the tail `AccP y` images at offset `2`.  Unlike `pinFrec`'s field
    this domain is NOT closed — `x` is free — so this is a genuine
    `instOff`-distribution proof, not the closed-term shortcut. -/
theorem ppaFieldDomM_hARtel (X : List (Expr Nat)) (ls : List Level) :
    piTelE (instPrefix X (instantiateLevels ls ppaFieldDomM)) =
      (telImgC 0 X ls (piTelE ppaFieldDomM).1,
        instOff (piTelE ppaFieldDomM).1.length X
          (instantiateLevels ls (piTelE ppaFieldDomM).2)) := by
  have hIL : instantiateLevels ls ppaFieldDomM = ppaFieldDomM := rfl
  rw [hIL]
  have htail : instOff 2 X
      (.app (.const 10 []) (.bvar 1) : Expr Nat) =
      .app (.const 10 []) (.bvar 1) := by
    rw [instOff_appC, instOff_constC, instOff_bvar_ltC X 2 1 (by decide)]
  have hstep : instPrefix X ppaFieldDomM =
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
theorem ppaFieldDomM_hidx (X : List (Expr Nat)) (ls : List Level) :
    (familyIdx 0 (piTelE ppaFieldDomM).2).map
        (fun a => instOff (piTelE ppaFieldDomM).1.length X
          (instantiateLevels ls a)) =
      familyIdx 0 (instOff (piTelE ppaFieldDomM).1.length X
        (instantiateLevels ls (piTelE ppaFieldDomM).2)) := by
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
theorem ppaSupplies (X : List (Expr Nat)) (ls : List Level) :
    WalkSuppliesC (eraseEnv pinPropAccEnvA) 24 X ls 0 1 [.bvar 1, .bvar 0]
      [.nonrecursive, .recursive 2]
      (.pi (.sort .zero) (.pi ppaFieldDom (.app (.const 10 []) (.bvar 1)))) := by
  refine WalkSuppliesC.supNonrec 1 [.bvar 0] [.recursive 2] (.sort .zero)
    (.pi ppaFieldDom (.app (.const 10 []) (.bvar 1))) ?_
  show WalkSuppliesC (eraseEnv pinPropAccEnvA) 24 X ls 0 1 [.bvar 0]
      [.recursive 2]
      (.pi ppaFieldDomM (.app (.const 10 []) (.bvar 2)))
  refine WalkSuppliesC.supFrec 0 [] [] ppaFieldDomM
    (.app (.const 10 []) (.bvar 2)) 1 ppaFieldDomM_canon rfl
    (ppaFieldDomM_hARtel X ls) (ppaFieldDomM_hidx X ls)
    (WalkSuppliesC.supNil [] _ rfl)

/-- `FrecFiringGates` at the unique `pinPropAccEnvA` firing, fuel `24`. -/
theorem pinPropAcc_gates {e e' : ExprA} {s : RecSpineA} {c : Nat} {g : IotaGroupA}
    (hs : recSpineA e = some s) (hc : spineHeadRefA s.major = some c)
    (hg : iotaGroupA pinPropAccEnvA s.recRef c = some g)
    (hr : iotaReductA s g = some e') :
    FrecFiringGates pinPropAccEnvA 24 s g := by
  cases s with
  | mk recRef ls pre major =>
    cases g with
    | mk recM ctorM famM ctorRef familyRef nparams nindices nMinors ctorIdx =>
      obtain ⟨hr12, hc11, hrecM, hctorM, hfamM, hcr, hf10, hnp, hni, hnM, hci⟩ :=
        pinPropAcc_group_inv hg
      subst hr12 hc11 hrecM hctorM hfamM hcr hf10 hnp hni hnM hci
      have hnf : (appsSpineA major).2.length = 2 := pinPropAcc_nf hr
      unfold FrecFiringGates
      refine ⟨?_, ?_, ?_, ?_⟩
      · change FieldFragList (eraseEnv pinPropAccEnvA) 24 10 pinPropAccFamA.arity 0 1 0
            [.sort .zero, ppaFieldDom]
        exact ⟨ppaS0Frag, ppaFieldFrag, trivial⟩
      · intro shapes X ls hsh
        change ctorShapesA 10 0 (pinPropAccIntroA.normA.getD pinPropAccIntroA.mtypeA) =
            some shapes at hsh
        rw [ppaIntroShapes_norm] at hsh; cases hsh
        change WalkSuppliesC (eraseEnv pinPropAccEnvA) 24 X ls 0 1
          (fieldBvars ((appsSpineA major).2.length)) [.nonrecursive, .recursive 2]
          (lift 0 ((appsSpineA major).2.length + 1 + 1 + 1)
            (ctorFieldTelRaw 0 ((piDomsA pinPropAccIntroA.mtypeA).map erase)
              (erase (piBodyA pinPropAccIntroA.mtypeA))))
        rw [hnf, ppaIntroDomsA_erase, ppaIntroBody_erase]
        show WalkSuppliesC (eraseEnv pinPropAccEnvA) 24 X ls 0 1 [.bvar 1, .bvar 0]
          [.nonrecursive, .recursive 2]
          (.pi (.sort .zero) (.pi ppaFieldDom (.app (.const 10 []) (.bvar 1))))
        exact ppaSupplies X ls
      · change iotaWitnessStableB (eraseEnv pinPropAccEnvA) 24
            ((piDomsA pinPropAccIntroA.mtypeA).map erase)
            (fieldBvars ((appsSpineA major).2.length))
            (lift 0 ((appsSpineA major).2.length + 1 + 1 + 1)
              (ctorFieldTelRaw 0 ((piDomsA pinPropAccIntroA.mtypeA).map erase)
                (erase (piBodyA pinPropAccIntroA.mtypeA)))) = true
        rw [hnf, ppaIntroDomsA_erase, ppaIntroBody_erase]
        change iotaWitnessStableB (eraseEnv pinPropAccEnvA) 24
            [.sort .zero, ppaFieldDom] [.bvar 1, .bvar 0]
            (.pi (.sort .zero) (.pi ppaFieldDom
              (.app (.const 10 []) (.bvar 1)))) = true
        have hmem9 : (eraseEnv pinPropAccEnvA).members 9 = some ppaRelT := rfl
        have hmem10 : (eraseEnv pinPropAccEnvA).members 10 = some ppaFamT := rfl
        have hS0 : constsMemberFuel (eraseEnv pinPropAccEnvA) (24 + 1)
            (.sort .zero : Expr Nat) = true := by
          simp only [constsMemberFuel]
        have hF : constsMemberFuel (eraseEnv pinPropAccEnvA) (24 + 1)
            ppaFieldDom = true := by
          simp only [ppaFieldDom, constsMemberFuel, hmem9, hmem10, transparent,
            ppaRelT, ppaFamT, eraseMember, pinPropAccRelA, pinPropAccFamA]
          rfl
        have hTel : constsMemberFuel (eraseEnv pinPropAccEnvA) (24 + 1)
            (.pi (.sort .zero) (.pi ppaFieldDom
              (.app (.const 10 []) (.bvar 1)))) = true := by
          simp only [ppaFieldDom, constsMemberFuel, hmem9, hmem10, transparent,
            ppaRelT, ppaFamT, eraseMember, pinPropAccRelA, pinPropAccFamA]
          rfl
        simp only [iotaWitnessStableB, List.all_cons, List.all_nil, hS0, hF,
          hTel, Bool.and_true, Bool.true_and]
        show (constsMemberFuel (eraseEnv pinPropAccEnvA) 25 (.bvar 1) &&
            constsMemberFuel (eraseEnv pinPropAccEnvA) 25 (.bvar 0)) = true
        simp only [constsMemberFuel]
        rfl
      · intro shapes schema hsh hopen
        change ctorShapesA 10 0 (pinPropAccIntroA.normA.getD pinPropAccIntroA.mtypeA) =
            some shapes at hsh
        rw [ppaIntroShapes_norm] at hsh; cases hsh
        change iotaOpenRhs (eraseEnv pinPropAccEnvA) 24
            (.const 12 (canonRecLevels pinPropAccRecMemberA.arity))
            (.bvar (((appsSpineA major).2.length) + 1 + (1 - 1 - 0)))
            (preMajorBvars 0 1 1 ((appsSpineA major).2.length)) 0 1
            [.nonrecursive, .recursive 2]
            (fieldBvars ((appsSpineA major).2.length))
            (lift 0 ((appsSpineA major).2.length + 1 + 1 + 1)
              (ctorFieldTelRaw 0 ((piDomsA pinPropAccIntroA.mtypeA).map erase)
                (erase (piBodyA pinPropAccIntroA.mtypeA)))) = some schema at hopen
        rw [hnf, ppaIntroDomsA_erase, ppaIntroBody_erase] at hopen
        have hcomp : iotaOpenRhs (eraseEnv pinPropAccEnvA) 24
            (.const 12 (canonRecLevels pinPropAccRecMemberA.arity))
            (.bvar (2 + 1 + (1 - 1 - 0)))
            (preMajorBvars 0 1 1 2) 0 1 [.nonrecursive, .recursive 2]
            [.bvar 1, .bvar 0]
            (.pi (.sort .zero) (.pi ppaFieldDom
              (.app (.const 10 []) (.bvar 1)))) = some _ := rfl
        change iotaOpenRhs (eraseEnv pinPropAccEnvA) 24
            (.const 12 (canonRecLevels pinPropAccRecMemberA.arity))
            (.bvar (2 + 1 + (1 - 1 - 0)))
            (preMajorBvars 0 1 1 2) 0 1 [.nonrecursive, .recursive 2]
            [.bvar 1, .bvar 0]
            (.pi (.sort .zero) (.pi ppaFieldDom
              (.app (.const 10 []) (.bvar 1)))) = some schema at hopen
        rw [hcomp] at hopen
        cases hopen
        change exprClosedAt (0 + 1 + 1 + 1 + (appsSpineA major).2.length) _ = true
        rw [hnf]
        rfl

/-- S6-4's Acc-shaped row: the union erase face at the indexed Acc
    fixture.  Every firing in `pinPropAccEnvA` factors through the unique
    `intro` group (`pinPropAcc_group_inv`), the gates hold (`pinPropAcc_gates`),
    and the erased side is `EnvWfT`-admitted (`ppaEnvWfT_erase`) — so a
    step of the copy's ι is a union derived-ι step of
    `eraseEnv pinPropAccEnvA`, past `EnvNoFunA`.

    As at `pinFrec`, the `ann` direction (`IotaCorrTUA`) is NOT stated:
    `EnvCorrAnnCert` reads the direct-fragment recognizer, which
    deliberately rejects frec witnesses — that remains the boundary. -/
theorem pinPropAcc_iotaErasesTUA : IotaErasesTUA pinPropAccEnvA := by
  obtain ⟨w, ⟨hT0⟩⟩ := pinPropAccRecTyAt0
  exact iotaErasesTUA_frecR (pinPropAccWfA w hT0) pinPropAcc_normErase ppaEnvWfT_erase 24
    (fun _ _ _ _ _ => pinPropAcc_gates)

#print axioms pinPropAcc_iotaErasesTUA

end Rcic.Declarative.Ann
