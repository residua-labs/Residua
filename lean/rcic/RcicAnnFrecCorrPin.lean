import rcic.RcicIotaFunRecCorr
import rcic.RcicIotaFunRecCorrR
import rcic.RcicAnnFrecPin
import rcic.RcicTypedFunRecPins

/-!
# S6-4 — the frec union ι-correspondence at the `pinFrecEnvA` fixture

The step-indexed `iotaErasesTUA_frec`/`iotaCorrTUA_frec` of
`RcicIotaFunRecCorr` take a per-firing gate `FrecFiringGates`.  This module
discharges them at `pinFrecEnvA` (`RcicAnnFrecPin`): the copy-side environment
whose one inductive group (`T` at `10`, `node : (Sort 0 → T) → T` at `11`,
`Wrec`-analogue at `12`) carries a function-recursive field — the pin designed
to sit outside `EnvNoFunA` (`pinFrec_not_noFunA`).

The firing is unique: `iotaGroupA pinFrecEnvA r c` succeeds only at
`r = 12`, `c = 11`, at the one group `⟨pinFrecRecMemberA, pinFrecNodeA,
pinNatFamA, …⟩` (`pinFrec_group_inv`).  Every premise of
`FrecFiringGates` is then decided or pinned to `rfl` on the concrete group:
the field-fragment list (`FieldFragList`), the walk supplies
(`WalkSuppliesC`), the witness stability (`iotaWitnessStableB`), and the
schema scope (`exprClosedAt`).

## Contents

- `pinFrec_normErase` — `EnvNormEraseA pinFrecEnvA` (the one constructor's
  `normA` is already normal).
- `pinFrec_group_inv` — every `iotaGroupA pinFrecEnvA` hit is the
  `node`/`T`/`Wrec` group at `12`/`11`.
- `pinFrec_gates` — the per-firing `FrecFiringGates` at `pinFrecEnvA`.
- `pinFrec_iotaErasesTUA` — `IotaErasesTUA pinFrecEnvA` once
  `EnvWfT (eraseEnv pinFrecEnvA)` is supplied.

`closure_claim` stays `0`.
-/

namespace Rcic.Declarative.Ann

/-- `EnvNormEraseA` at `pinFrecEnvA`: the only `.constructorM` member is
    `pinFrecNodeA`, whose `normA` is stored already normalized, so the erased
    normal form is the erased stored type. -/
theorem pinFrec_normErase : EnvNormEraseA pinFrecEnvA := by
  intro r m hm hmc T hT
  rcases pinFrec_mem hm with ⟨hr, rfl⟩ | ⟨hr, rfl⟩ | ⟨hr, rfl⟩
  · simp [pinNatFamA] at hmc
  · have hTe : T = ctorTypeA 10 (canonLevelsA 0) (.succ .zero) [] [pinFrecFieldA] [] :=
      Option.some.inj hT.symm
    subst hTe; rfl
  · simp [pinFrecRecMemberA] at hmc

/-- the one group `iotaGroupA` can return at `pinFrecEnvA`: recursor `12`,
    constructor `11`, family `10` — `nparams = nindices = 0`, `nMinors = 1`,
    `ctorIdx = 0`. -/
theorem pinFrec_group_hit :
    iotaGroupA pinFrecEnvA 12 11 =
      some ⟨pinFrecRecMemberA, pinFrecNodeA, pinNatFamA, 11, 10, 0, 0, 1, 0⟩ := rfl

/-- `iotaGroupA` at `pinFrecEnvA` only hits the `node`/`T`/`Wrec` group: the
    recursor member `12` and the constructor `11`, with the family's own counts
    (`nparams = 0`, `nindices = 0`, `nMinors = 1`, `ctorIdx = 0`). -/
theorem pinFrec_group_inv {r c : Nat} {g : IotaGroupA}
    (hg : iotaGroupA pinFrecEnvA r c = some g) :
    r = 12 ∧ c = 11 ∧ g.recM = pinFrecRecMemberA ∧ g.ctorM = pinFrecNodeA ∧
      g.famM = pinNatFamA ∧ g.ctorRef = 11 ∧ g.familyRef = 10 ∧ g.nparams = 0 ∧
      g.nindices = 0 ∧ g.nMinors = 1 ∧ g.ctorIdx = 0 := by
  rcases hr' : pinFrecEnvA.members r with _ | rm
  · unfold iotaGroupA at hg; rw [hr'] at hg; exact Option.noConfusion hg
  rcases hc' : pinFrecEnvA.members c with _ | cm
  · unfold iotaGroupA at hg; rw [hr', hc'] at hg; exact Option.noConfusion hg
  rcases pinFrec_mem hr' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases pinFrec_mem hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  -- eight of the nine member pairs fail the class guards; only (12, 11) hits
  all_goals first
    | exact Option.noConfusion hg
    | (have h := Option.some.inj (pinFrec_group_hit.symm.trans hg)
       cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-! ## the erased environment's `EnvWfT`

`eraseEnv pinFrecEnvA`'s members are the frec group's erasures: `.frec` reads
`.drec` on the erased side (`FieldA.erase`), so `eraseMember pinFrecNodeA`'s
stored type is the honest Π `Π (_ : Π (_ : Sort 0), T), T` — a W-type
eliminator (`T` at `10`, `node` at `11`, `Wrec` at `12`) over `emptyEnv`.
`EnvWfT` is built member-by-member, mirroring `natEnvUWfT`/`wEnvWfT`. -/

/-- the erased family's member record. -/
abbrev pfFamT : CheckedMember := eraseMember pinNatFamA
/-- the erased constructor's member record: `node : Π (_ : Π (_ : Sort 0), T), T`. -/
abbrev pfNodeT : CheckedMember := eraseMember pinFrecNodeA
/-- the erased recursor's member record. -/
abbrev pfRecT : CheckedMember := eraseMember pinFrecRecMemberA
/-- `eraseEnv pinNatFamEnvA`: `emptyEnv` + `T` at `10`. -/
abbrev pfFamEnvT : ResolvedEnv := extendEnv emptyEnv 10 pfFamT
/-- `eraseEnv pinFrecGroupEnvA`: `pfFamEnvT` + `node` at `11`. -/
abbrev pfSupEnvT : ResolvedEnv := extendEnv pfFamEnvT 11 pfNodeT
/-- `eraseEnv pinFrecEnvA`: `pfSupEnvT` + `Wrec` at `12`. -/
abbrev pfEnvT : ResolvedEnv := extendEnv pfSupEnvT 12 pfRecT

/-- the node's one field domain: `Π (_ : Sort 0), T`. -/
abbrev pfFieldDom : Expr Nat := .pi (.sort .zero) (.const 10 [])
/-- the recursor motive slot: `Π (_ : T), Sort (param 0)`. -/
abbrev pfMotTy : Expr Nat := .pi (.const 10 []) (.sort (.param 0))
/-- the minor for `node`: `Π (f : Π (_ : Sort 0), T), Π (_ : Π (b : Sort 0),
    m (f b)), m (node f)`. -/
abbrev pfMinorTy : Expr Nat :=
  .pi pfFieldDom (.pi (.pi (.sort .zero) (.app (.bvar 2) (.app (.bvar 1) (.bvar 0))))
    (.app (.bvar 2) (.app (.const 11 []) (.bvar 1))))
/-- the erased recursor's stored type: `Π (m : T → Sort u), Π minor, Π (t : T),
    m t`. -/
abbrev pfRecTy : Expr Nat :=
  .pi pfMotTy (.pi pfMinorTy (.pi (.const 10 []) (.app (.bvar 2) (.bvar 0))))

/-- the erased group's env as `extendEnv`'s: memberwise identical to
    `eraseEnv pinFrecEnvA`. -/
theorem pfEnvT_eq : eraseEnv pinFrecEnvA = pfEnvT := by
  apply congrArg ResolvedEnv.mk
  funext r
  by_cases h12 : r = 12 <;> by_cases h11 : r = 11 <;> by_cases h10 : r = 10 <;>
    simp [h12, h11, h10, pinFrecEnvA, pinFrecGroupEnvA, pinNatFamEnvA, eraseEnv,
      extendEnvA, pfEnvT, pfSupEnvT, pfFamEnvT, extendEnv, pfFamT, pfNodeT, pfRecT,
      emptyEnvA, emptyEnv]


/-- the family's view, wherever `T` is present at `10`: `T : Sort 1`, no
    parameters, no indices. -/
def pfFamViewT (E : ResolvedEnv) (h : E.members 10 = some pfFamT) :
    PolicyFamilyView E where
  ref := 10
  member := pfFamT
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

/-- the field domain `Π (_ : Sort 0), T` at `Sort (imax 1 1)`, wherever `T`
    is present (untyped judgment — admission's telescope typing). -/
def pfFieldDomTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h10 : E.members 10 = some pfFamT) :
    HasTy E n Γ pfFieldDom (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ (.sort .zero) (.succ .zero) (.const 10 []) (.succ .zero)
    (HasTy.sort _ .zero) (HasTy.const _ 10 [] pfFamT h10 rfl (fun _ hx => nomatch hx))

/-- the same in the typed judgment (the view's `CtorTypedT` content). -/
def pfFieldDomTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h10 : E.members 10 = some pfFamT) :
    HasTyT E n Γ pfFieldDom (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ (.sort .zero) (.succ .zero) (.const 10 []) (.succ .zero)
    (HasTyT.sort _ .zero) (HasTyT.const _ 10 [] pfFamT h10 rfl rfl)

/-- `node`'s view: the one `.drec`-shaped field `Π (_ : Sort 0), T` (the
    erased image of the Ann `.frec` field), no parameters, no indices. -/
def pfNodeView (E : ResolvedEnv) (h10 : E.members 10 = some pfFamT) :
    PolicyConstructorView E (pfFamViewT E h10) pfNodeT where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [pfFieldDom]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .imax (.succ .zero) (.succ .zero)
    bounded := fun _ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => pfFieldDomTy h10
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

/-- the field's level `imax 1 1` is bounded by the family's `1`. -/
theorem pfNodeUniv {E : ResolvedEnv} {h10 : E.members 10 = some pfFamT} :
    FieldUniverseAdmitted (pfNodeView E h10) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr ⟨uniformType_succ_zero, leN_imax_succ_zero_self⟩

/-- `node` is admitted before `T`'s recursor exists: `pfFamEnvT` has no
    recursor member at all. -/
theorem pfBefore : CtorBeforeRecursors pfFamEnvT pfNodeT := by
  refine ⟨10, rfl, ?_⟩
  intro rr rm hm hc
  by_cases h10 : rr = 10
  · subst h10
    rw [show pfFamEnvT.members 10 = some pfFamT from rfl] at hm
    cases hm
    exact absurd hc (by decide)
  · rw [members_extendEnv_ne _ _ _ h10] at hm
    exact Option.noConfusion hm

/-- no constructor for `T` sits strictly inside `(10, 11)`, and none outside
    `pfFamEnvT`'s span. -/
theorem pfContig : CtorContiguous pfFamEnvT 11 pfNodeT := by
  refine ⟨10, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd (And.intro hl hr) (by omega)
  · intro c ⟨cm, hm, hc, _⟩
    by_cases h10 : c = 10
    · subst h10
      rw [show pfFamEnvT.members 10 = some pfFamT from rfl] at hm
      cases hm
      exact absurd hc (by decide)
    · rw [members_extendEnv_ne _ _ _ h10] at hm
      exact Option.noConfusion hm

/-- the field analyzes `.recursive 1` — permitted — in `pfFamEnvT`. -/
theorem pfNodeFieldsFam : CtorFieldsPermitted (pfNodeView pfFamEnvT rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.recursive 1, 8, [], rfl⟩

/-- the same in `pfSupEnvT` (the recursor admission's own check). -/
theorem pfNodeFieldsSup : CtorFieldsPermitted (pfNodeView pfSupEnvT rfl) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.recursive 1, 8, [], rfl⟩

/-- the recursor admission: family `10`, the one constructor `node` at `11`,
    AnySort at `Sort 1` (uniform-type family). -/
def pfGroupAdm : RecursorEliminationAdmitted pfSupEnvT 12 pfRecT where
  family := pfFamViewT pfSupEnvT rfl
  constructors := [pfNodeT]
  constructorViews
    | ⟨0, _⟩ => pfNodeView pfSupEnvT rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [pfMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

/-- the group's census: `node` at `11` is the only `T`-constructor below `12`. -/
theorem pfCensus : CtorCensus pfSupEnvT 10 12 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hm, hc, hfam⟩
    by_cases h11 : c = 11
    · subst h11
      rw [show pfSupEnvT.members 11 = some pfNodeT from rfl] at hm
      cases hm
      exact ⟨by omega, by omega⟩
    · rw [members_extendEnv_ne _ _ _ h11] at hm
      by_cases h10 : c = 10
      · subst h10
        rw [show pfFamEnvT.members 10 = some pfFamT from rfl] at hm
        cases hm
        exact absurd hc (by decide)
      · rw [members_extendEnv_ne _ _ _ h10] at hm
        exact Option.noConfusion hm
  · intro ⟨hl, hr⟩
    have hc : c = 11 := by omega
    subst hc
    exact ⟨pfNodeT, rfl, rfl, rfl⟩

/-- the derived minor is `pfMinorTy` at the recursive-shape list. -/
theorem pfMinor_derived :
    derivedMinor pfGroupAdm ⟨0, by decide⟩ 8 [.recursive 1] = some pfMinorTy := rfl

theorem pfMinorMatch : MinorPremisesMatch pfGroupAdm := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.recursive 1], 8, rfl, rfl⟩

/-- the equation's context: `f`, the minor, the motive. -/
def pfIotaCtx : LCtx :=
  [.assumption pfFieldDom, .assumption pfMinorTy, .assumption pfMotTy]

/-- the λ-wrapped recursive call: `fun (_ : Sort 0) => rec m minor (f ·)`. -/
def pfCall : Expr Nat :=
  .lam (.sort .zero)
    (.app (.app (.app (.const 12 [.param 0]) (.bvar 3)) (.bvar 2))
      (.app (.bvar 1) (.bvar 0)))

/-- the schema admission derives: `minor f (fun _ => rec m minor (f ·))`. -/
def pfSchema : Expr Nat := .app (.app (.bvar 1) (.bvar 0)) pfCall

/-- the equation's type: `m (node f)`. -/
def pfEqTy : Expr Nat := .app (.bvar 2) (.app (.const 11 []) (.bvar 0))

theorem pfSchema_derived :
    iotaSchemaAt pfGroupAdm ⟨0, by decide⟩ 8 [.recursive 1] = some pfSchema := rfl

theorem pfEquation_shape :
    equationDoms pfGroupAdm ⟨0, by decide⟩ = some [pfMotTy, pfMinorTy, pfFieldDom] ∧
    iotaEquationType pfGroupAdm ⟨0, by decide⟩ = pfEqTy := ⟨rfl, rfl⟩

/-- the recursor's head, wherever `12` is present (untyped judgment). -/
def pfRecHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h12 : E.members 12 = some pfRecT) :
    HasTy E n Γ (.const 12 [.param 0]) pfRecTy :=
  HasTy.const _ 12 [.param 0] pfRecT h12 rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

/-- the equation in the untyped judgment: `minor f (fun _ => rec m minor (f ·))
    : m (node f)` — direct, off the field's own telescope. -/
def pfIotaTy : HasTy pfEnvT 1 pfIotaCtx pfSchema pfEqTy := by
  have hMot : HasTy pfEnvT 1 pfIotaCtx (.bvar 2) pfMotTy := HasTy.bvar _ 2 _ rfl
  have hMs : HasTy pfEnvT 1 pfIotaCtx (.bvar 1) (lift 0 2 pfMinorTy) :=
    HasTy.bvar _ 1 _ rfl
  have hF : HasTy pfEnvT 1 pfIotaCtx (.bvar 0) pfFieldDom := HasTy.bvar _ 0 _ rfl
  have hS0 : HasTy pfEnvT 1 pfIotaCtx (.sort .zero) (.sort (.succ .zero)) :=
    HasTy.sort _ .zero
  have hMot' : HasTy pfEnvT 1 (.assumption (.sort .zero) :: pfIotaCtx) (.bvar 3) pfMotTy :=
    HasTy.bvar _ 3 _ rfl
  have hMs' : HasTy pfEnvT 1 (.assumption (.sort .zero) :: pfIotaCtx) (.bvar 2)
      (lift 0 3 pfMinorTy) := HasTy.bvar _ 2 _ rfl
  have hF' : HasTy pfEnvT 1 (.assumption (.sort .zero) :: pfIotaCtx) (.bvar 1) pfFieldDom :=
    HasTy.bvar _ 1 _ rfl
  have hB : HasTy pfEnvT 1 (.assumption (.sort .zero) :: pfIotaCtx) (.bvar 0) (.sort .zero) :=
    HasTy.bvar _ 0 _ rfl
  exact HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ hMs hF)
    (HasTy.lam _ (.sort .zero) (.succ .zero) _ _ hS0
      (HasTy.app _ _ _ _ _
        (HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ (pfRecHead rfl) hMot') hMs')
        (HasTy.app _ _ _ _ _ hF' hB)))

def pfIotaLegacy : IotaEquationTyped pfGroupAdm ⟨0, by decide⟩ 8 [.recursive 1] := by
  unfold IotaEquationTyped
  rw [pfEquation_shape.1, pfSchema_derived]
  exact pfIotaTy

/-- the descriptor clause: the field reads `.recursive 1` at fuel `8`, and the
    equation types. -/
def pfIotaClause : IotaDescriptorClause pfSupEnvT pfGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => [.recursive 1]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => pfIotaLegacy

/-- `T` is admitted in `emptyEnv`. -/
def pfFamAdmitted : IndGroupAdmitted emptyEnv 10 pfFamT :=
  .family rfl (pfFamViewT pfFamEnvT rfl) rfl rfl (Or.inr uniformType_succ_zero)

/-- `node` is admitted in `pfFamEnvT`. -/
def pfNodeAdmitted : IndGroupAdmitted pfFamEnvT 11 pfNodeT :=
  .constructor (pfFamViewT pfFamEnvT rfl) (pfNodeView pfFamEnvT rfl) rfl
    pfBefore pfContig pfNodeUniv pfNodeFieldsFam

/-- `Wrec` is admitted in `pfSupEnvT`. -/
def pfRecAdmitted : IndGroupAdmitted pfSupEnvT 12 pfRecT :=
  .recursor pfGroupAdm rfl pfCensus
    (fun i => match i with | ⟨0, _⟩ => pfNodeUniv)
    (fun i => match i with | ⟨0, _⟩ => pfNodeFieldsSup)
    pfMinorMatch pfIotaClause

/-- `node`'s stored type's sort: `imax (imax 1 1) 1`. -/
def pfNodeSortU : Level := .imax (.imax (.succ .zero) (.succ .zero)) (.succ .zero)

/-- `node`'s stored type types in `pfFamEnvT` — the field domain at
    `imax 1 1`, the family target at `1`. -/
def pfNodeTyT : HasTyT pfFamEnvT 0 [] pfNodeT.mtype (.sort pfNodeSortU) :=
  .pi [] pfFieldDom (.imax (.succ .zero) (.succ .zero)) (.const 10 []) (.succ .zero)
    (pfFieldDomTyT rfl) (HasTyT.const _ 10 [] pfFamT rfl rfl rfl)

/-- the recursor's stored type's sort (the `inferT` answer, checked). -/
def pfRecSortU : Level :=
  .imax (.imax (.succ .zero) (.succ (.param 0)))
    (.imax (.imax (.imax (.succ .zero) (.succ .zero))
             (.imax (.imax (.succ .zero) (.param 0)) (.param 0)))
      (.imax (.succ .zero) (.param 0)))

theorem pfRecTy_direct : inferT pfSupEnvT 1 [] pfRecTy = some (.sort pfRecSortU) := rfl

def pfRecTyT : HasTyT pfSupEnvT 1 [] pfRecTy (.sort pfRecSortU) :=
  (tyAtC pfSupEnvT 1 8 [] pfRecTy (.sort pfRecSortU)).get (by
    have h : (tyAtC pfSupEnvT 1 8 [] pfRecTy (.sort pfRecSortU)).isSome = true := rfl
    exact h)

/-- `node`'s typed content: its one field types, its (zero) parameters mirror. -/
theorem pfNodeTypedE {E : ResolvedEnv} (h10 : E.members 10 = some pfFamT) :
    CtorTypedT (pfNodeView E h10) :=
  ⟨fun j => by
      match j with
      | ⟨0, _⟩ => exact ⟨pfFieldDomTyT h10⟩,
    fun i => i.elim0⟩

/-- the family's typed content: no telescope. -/
theorem pfFamTypedT : IndGroupTypedT pfFamAdmitted := fun i => i.elim0

theorem pfNodeTyped : IndGroupTypedT pfNodeAdmitted :=
  ⟨fun i => i.elim0, pfNodeTypedE rfl⟩

/-- the recursor's typed content, its ι equation typed by `tyAtC`. -/
theorem pfRecTyped : IndGroupTypedT pfRecAdmitted :=
  ⟨fun i => i.elim0, fun i => match i with | ⟨0, _⟩ => pfNodeTypedE rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 8 Γ e T) rfl⟩

/-- the group members, one after another. -/
def pfMembersT :
    GroupMembersT pfFamEnvT emptyEnv [(10, pfFamT), (11, pfNodeT), (12, pfRecT)] pfEnvT :=
  .cons _ 10 pfFamT _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    pfFamAdmitted PUnit.unit _ (.sort [] (.succ .zero)) (fun h => absurd h (by decide))
    pfFamTypedT
    (.cons _ 11 pfNodeT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      pfNodeAdmitted PUnit.unit _ pfNodeTyT (fun _ => ⟨pfNodeTyT⟩) pfNodeTyped
      (.cons _ 12 pfRecT _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        pfRecAdmitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ pfRecTyT
        (fun h => absurd h (by decide)) pfRecTyped (.nil _)))

/-- `pfEnvT` — the erased frec environment — is a well-formed typed
    environment: `T`, `node`, `Wrec` as one group step over `emptyEnv`. -/
def pfEnvWfT : EnvWfT pfEnvT :=
  .group emptyEnv 10 pfFamT [(11, pfNodeT)] 12 pfRecT pfEnvT EnvWfT.empty
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl pfMembersT

/-- the erased side of `pinFrecEnvA` is a well-formed typed environment. -/
def pfEnvWfT_erase : EnvWfT (eraseEnv pinFrecEnvA) := pfEnvT_eq ▸ pfEnvWfT


/-! ## the per-firing gates at `pinFrecEnvA`

`pinFrec_group_inv` makes every `iotaGroupA` hit the `node` group, and
`iotaReductA_some` pins the major's argument count at `1`.  The four
`FrecFiringGates` then discharge: the fragment list is `pfFieldDom`'s
`FunRecFrag`, the walk supplies hold at the free `X`/`ls` because every
telescope entry is closed, the stability check computes, and the open schema
is `pfSchema`, closed under `3`. -/

/-- `node`'s erased field domains: `[Π (_ : Sort 0), T]`. -/
theorem pfNodeDomsA_erase :
    (piDomsA pinFrecNodeA.mtypeA).map erase = [pfFieldDom] := rfl

/-- `node`'s erased result is the family constant. -/
theorem pfNodeBody_erase : erase (piBodyA pinFrecNodeA.mtypeA) = .const 10 [] := rfl

/-- the fired shapes of `node`'s NORMALIZED stored type — the read
    `iotaReductA` makes — are the one function-recursive field. -/
theorem pfNodeShapes_norm :
    ctorShapesA 10 0 (pinFrecNodeA.normA.getD pinFrecNodeA.mtypeA) =
      some [.recursive 1] := rfl

/-- `iotaReductA` success pins the major's argument count to the
    constructor's Π-count: `1`. -/
theorem pinFrec_nf {s : RecSpineA} {e' : ExprA}
    (hr : iotaReductA s
      ⟨pinFrecRecMemberA, pinFrecNodeA, pinNatFamA, 11, 10, 0, 0, 1, 0⟩ =
        some e') :
    (appsSpineA s.major).2.length = 1 := by
  obtain ⟨_, _, _, _, _, hlen, _⟩ := iotaReductA_some hr
  exact hlen

/-- `pfFieldDom` is closed — `lift` is the identity on it. -/
theorem pfFieldDom_lift (c amt : Nat) : lift c amt pfFieldDom = pfFieldDom := rfl

/-- `instPrefix` is the identity on closed terms: each `instantiate` step
    finds no `bvar` at the cutoff. -/
theorem instPrefix_of_liftClosed {e : Expr Nat} (h : lift 0 1 e = e) :
    ∀ args : List (Expr Nat), instPrefix args e = e := by
  intro args
  induction args with
  | nil => rfl
  | cons a as ih =>
      show instPrefix as (instantiate as.length (lift 0 as.length a) e) = e
      rw [instantiate_of_closed e h]
      exact ih

/-- `instOff` is the identity on closed terms at any offset. -/
theorem instOff_of_liftClosed {e : Expr Nat} (h : lift 0 1 e = e) :
    ∀ (k : Nat) (args : List (Expr Nat)), instOff k args e = e := by
  intro k args
  induction args generalizing e with
  | nil => rfl
  | cons a as ih =>
      show instOff k as (instantiate (k + as.length) (lift 0 (k + as.length) a) e) = e
      rw [instantiate_of_closed e h]
      exact ih h

/-- `instantiateLevels` on `pfFieldDom`: no level parameters to move. -/
theorem instantiateLevels_pfFieldDom (ls : List Level) :
    instantiateLevels ls pfFieldDom = pfFieldDom := rfl

/-- the field fragment: `pfFieldDom` is a `FunRecFrag` at `pfEnvT` — rigid,
    stable tail, fuel `8` covers the scan, canonical family tail, family-free
    inner binders. -/
theorem pfFieldDomFrag : FieldFrag (eraseEnv pinFrecEnvA) 8 10 0 0 0 0 pfFieldDom :=
  ⟨rfl, rfl, by decide, rfl, rfl⟩

/-- `FrecFiringGates` at the unique `pinFrecEnvA` firing, fuel `8`. -/
theorem pinFrec_gates {e e' : ExprA} {s : RecSpineA} {c : Nat} {g : IotaGroupA}
    (hs : recSpineA e = some s) (hc : spineHeadRefA s.major = some c)
    (hg : iotaGroupA pinFrecEnvA s.recRef c = some g)
    (hr : iotaReductA s g = some e') :
    FrecFiringGates pinFrecEnvA 8 s g := by
  cases s with
  | mk recRef ls pre major =>
    cases g with
    | mk recM ctorM famM ctorRef familyRef nparams nindices nMinors ctorIdx =>
      obtain ⟨hr12, hc11, hrecM, hctorM, hfamM, hcr, hf10, hnp, hni, hnM, hci⟩ :=
        pinFrec_group_inv hg
      subst hr12 hc11 hrecM hctorM hfamM hcr hf10 hnp hni hnM hci
      have hnf : (appsSpineA major).2.length = 1 := pinFrec_nf hr
      unfold FrecFiringGates
      refine ⟨?_, ?_, ?_, ?_⟩
      · change FieldFragList (eraseEnv pinFrecEnvA) 8 10 pinNatFamA.arity 0 0 0
            [pfFieldDom]
        exact ⟨pfFieldDomFrag, trivial⟩
      · intro shapes X ls hsh
        change ctorShapesA 10 0 (pinFrecNodeA.normA.getD pinFrecNodeA.mtypeA) =
            some shapes at hsh
        rw [pfNodeShapes_norm] at hsh; cases hsh
        change WalkSuppliesC (eraseEnv pinFrecEnvA) 8 X ls 0 1
          (fieldBvars ((appsSpineA major).2.length)) [.recursive 1]
          (lift 0 ((appsSpineA major).2.length + 1 + 1 + 0)
            (ctorFieldTelRaw 0 ((piDomsA pinFrecNodeA.mtypeA).map erase)
              (erase (piBodyA pinFrecNodeA.mtypeA))))
        rw [hnf, pfNodeDomsA_erase, pfNodeBody_erase]
        show WalkSuppliesC (eraseEnv pinFrecEnvA) 8 X ls 0 1 [.bvar 0]
          [.recursive 1] (.pi pfFieldDom (.const 10 []))
        refine WalkSuppliesC.supFrec 0 [] [] pfFieldDom (.const 10 []) 0 rfl rfl ?_ ?_
          (WalkSuppliesC.supNil [] _ rfl)
        · rw [instantiateLevels_pfFieldDom, instPrefix_of_liftClosed rfl]
          show ([.sort .zero], .const 10 []) =
              ([instOff 0 X (.sort .zero)], instOff 1 X (.const 10 []))
          rw [instOff_of_liftClosed
              (rfl : lift 0 1 (.sort .zero : Expr Nat) = .sort .zero),
            instOff_of_liftClosed
              (rfl : lift 0 1 (.const 10 [] : Expr Nat) = .const 10 [])]
        · show (familyIdx 0 (.const 10 [])).map
              (fun a => instOff 1 X (instantiateLevels ls a)) =
            familyIdx 0 (instOff 1 X (instantiateLevels ls (.const 10 [])))
          rw [show instantiateLevels ls (.const 10 [] : Expr Nat) = .const 10 [] from rfl,
            instOff_of_liftClosed
              (rfl : lift 0 1 (.const 10 [] : Expr Nat) = .const 10 [])]
          rfl
      · change iotaWitnessStableB (eraseEnv pinFrecEnvA) 8
            ((piDomsA pinFrecNodeA.mtypeA).map erase)
            (fieldBvars ((appsSpineA major).2.length))
            (lift 0 ((appsSpineA major).2.length + 1 + 1 + 0)
              (ctorFieldTelRaw 0 ((piDomsA pinFrecNodeA.mtypeA).map erase)
                (erase (piBodyA pinFrecNodeA.mtypeA)))) = true
        rw [hnf, pfNodeDomsA_erase, pfNodeBody_erase]
        change iotaWitnessStableB (eraseEnv pinFrecEnvA) 8 [pfFieldDom] [.bvar 0]
            (.pi pfFieldDom (.const 10 [])) = true
        have hmem10 : (eraseEnv pinFrecEnvA).members 10 = some pfFamT := rfl
        have hF : constsMemberFuel (eraseEnv pinFrecEnvA) (8 + 1) pfFieldDom = true := by
          simp only [pfFieldDom, constsMemberFuel, hmem10, transparent]
          rfl
        have hTel : constsMemberFuel (eraseEnv pinFrecEnvA) (8 + 1)
            (.pi pfFieldDom (.const 10 [])) = true := by
          simp only [pfFieldDom, constsMemberFuel, hmem10, transparent]
          rfl
        have hBv : List.all (fieldBvars 1)
            (constsMemberFuel (eraseEnv pinFrecEnvA) (8 + 1)) = true := by
          show List.all [.bvar 0] (constsMemberFuel (eraseEnv pinFrecEnvA) (8 + 1)) = true
          simp only [List.all_cons, List.all_nil, constsMemberFuel]
          rfl
        simp only [iotaWitnessStableB, List.all_cons, List.all_nil, hF, hBv, hTel,
          constsMemberFuel, Bool.and_true, Bool.true_and]
      · intro shapes schema hsh hopen
        change ctorShapesA 10 0 (pinFrecNodeA.normA.getD pinFrecNodeA.mtypeA) =
            some shapes at hsh
        rw [pfNodeShapes_norm] at hsh; cases hsh
        change iotaOpenRhs (eraseEnv pinFrecEnvA) 8
            (.const 12 (canonRecLevels pinFrecRecMemberA.arity))
            (.bvar (((appsSpineA major).2.length) + 0 + (1 - 1 - 0)))
            (preMajorBvars 0 1 0 ((appsSpineA major).2.length)) 0 1 [.recursive 1]
            (fieldBvars ((appsSpineA major).2.length))
            (lift 0 ((appsSpineA major).2.length + 1 + 1 + 0)
              (ctorFieldTelRaw 0 ((piDomsA pinFrecNodeA.mtypeA).map erase)
                (erase (piBodyA pinFrecNodeA.mtypeA)))) = some schema at hopen
        rw [hnf, pfNodeDomsA_erase, pfNodeBody_erase] at hopen
        have hcomp : iotaOpenRhs (eraseEnv pinFrecEnvA) 8
            (.const 12 (canonRecLevels pinFrecRecMemberA.arity)) (.bvar (1 + 0 + (1 - 1 - 0)))
            (preMajorBvars 0 1 0 1) 0 1 [.recursive 1] [.bvar 0]
            (.pi pfFieldDom (.const 10 [])) = some pfSchema := rfl
        change iotaOpenRhs (eraseEnv pinFrecEnvA) 8
            (.const 12 (canonRecLevels pinFrecRecMemberA.arity)) (.bvar (1 + 0 + (1 - 1 - 0)))
            (preMajorBvars 0 1 0 1) 0 1 [.recursive 1] [.bvar 0]
            (.pi pfFieldDom (.const 10 [])) = some schema at hopen
        rw [hcomp] at hopen
        cases hopen
        change exprClosedAt (0 + 1 + 1 + 0 + (appsSpineA major).2.length) pfSchema = true
        rw [hnf]
        rfl

/-- S6-4 payoff: the union erase face at the concrete frec fixture.  Every firing in
    `pinFrecEnvA` factors through the unique frec group (`pinFrec_group_inv`), the gates hold
    (`pinFrec_gates`), and the erased side is `EnvWfT`-admitted (`pfEnvWfT_erase`) — so a step
    of the copy's ι is a union derived-ι step of `eraseEnv pinFrecEnvA`, past `EnvNoFunA`.

    The `ann` direction (`IotaCorrTUA`) is NOT stated here: `EnvCorrAnnCert` reads the
    direct-fragment recognizer, which deliberately rejects frec witnesses — that is the
    remaining boundary, not a gap in this theorem. -/
theorem pinFrec_iotaErasesTUA : IotaErasesTUA pinFrecEnvA := by
  obtain ⟨w, ⟨hT0⟩⟩ := pinFrecRecTyAt0
  exact iotaErasesTUA_frecR (pinFrecWfA w hT0) pinFrec_normErase pfEnvWfT_erase 8
    (fun _ _ _ _ _ => pinFrec_gates)

#print axioms pinFrec_iotaErasesTUA
