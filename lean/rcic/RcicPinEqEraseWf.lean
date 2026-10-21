import rcic.RcicEGTypedGroup
import rcic.ScmSrcGroupsKernelRfl

set_option maxRecDepth 8192

/-!
# `EnvWfT eqEnvT` — the erased `Eq` group's `.group` clause

The typed `iotaStarK` fixture (F05b, cc on #6293/#6421): `Eq` at 63, `Eq.refl` at
64, the AnySort recursor at 65. Family `Eq : Π (α : Sort 1)(a : α)(b : α), Sort 0`
— `α` and `a` are parameters, `b` the sole index. `α : Sort 1`, not `Sort 0`: at
a Prop carrier `irr` would equate `a` and `b` outright and the `b ≢ a` gate case
could not exist; at `Type 0` the distinct-bvar major is genuinely stuck.

`Eq.refl` is FIELD-FREE: the `singletonProp` selection is vacuous on fields and
the iota equation `m : M a (refl α a)` is a single context lookup — there is no
`m x (rec …)` rhs like Loop's. Route: `EG010T_group_accepted` over a
`GroupAcceptChain` at `emptyEnv`, the same route `RcicPinLoopEraseWf` uses. The
three `IndGroupAdmitted` cells are hand-built at refs 63/64/65; the recursor
carries a full `RecursorEliminationAdmitted` (`singletonProp` selection,
`minorTypes = [eqMinorT]`, `recursorType := rfl` — the stored type is the
canonical `policyRecursorType` by computation) plus `CtorCensus`,
`FieldUniverseAdmitted`, `CtorFieldsPermitted`, `MinorPremisesMatch`, and an
`IotaDescriptorClause` whose `typed` field is an honest legacy `HasTy`
derivation (a `.bvar` lookup — the field-free constructor's reduct IS the
minor variable). No `retypeAny`/collapse route is used anywhere.
-/

namespace Rcic.Declarative

open Rcic.Scm.SrcG (sortTyAtC)

/-! ## (1) the erased members and the prefix chain -/

/-- `Eq : Π (α : Sort 1)(a : α)(b : α), Sort 0` — 2 parameters, 1 index. -/
def eqFamT : CheckedMember :=
  ⟨.inductiveM, 0,
    .pi (.sort (.succ .zero)) (.pi (.bvar 0) (.pi (.bvar 1) (.sort .zero))),
    none⟩

/-- `Eq.refl : Π (α : Sort 1)(a : α), Eq α a a`. -/
def eqReflT : CheckedMember :=
  ⟨.constructorM, 0,
    .pi (.sort (.succ .zero))
      (.pi (.bvar 0)
        (foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 0])),
    none⟩

/-- motive `Π (b : α), Eq α a b → Sort (param 0)` — under `[α, a]`. -/
def eqMotT : Expr Nat :=
  .pi (.bvar 1)
    (.pi (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 0])
      (.sort (.param 0)))

/-- minor `m : M a (refl α a)` — under `[α, a, M]`. -/
def eqMinorT : Expr Nat :=
  .app (.app (.bvar 0) (.bvar 1))
    (foldApps (.const 64 []) [.bvar 2, .bvar 1])

/-- the stored recursor type: `Π (α : Sort 1)(a : α)(M : Π b, Eq α a b →
    Sort (param 0))(m : M a (refl α a))(b : α)(p : Eq α a b), M b p`. -/
def eqRecT : CheckedMember :=
  ⟨.recursorM, 1,
    .pi (.sort (.succ .zero))
      (.pi (.bvar 0)
        (.pi eqMotT
          (.pi eqMinorT
            (.pi (.bvar 3)
              (.pi (foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0])
                (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))))))),
    none⟩

def eqFamEnvT : ResolvedEnv := extendEnv emptyEnv 63 eqFamT
def eqPrefixT : ResolvedEnv := extendEnv eqFamEnvT 64 eqReflT
def eqEnvT : ResolvedEnv := extendEnv eqPrefixT 65 eqRecT

theorem eqFamEnvT_mem (c : Nat) :
    eqFamEnvT.members c =
      if c = 63 then some eqFamT else none := by
  simp [eqFamEnvT, extendEnv, emptyEnv]

theorem eqPrefixT_mem (c : Nat) :
    eqPrefixT.members c =
      if c = 64 then some eqReflT
      else if c = 63 then some eqFamT
      else none := by
  simp [eqPrefixT, eqFamEnvT, extendEnv, emptyEnv]

theorem eqEnvT_mem (c : Nat) :
    eqEnvT.members c =
      if c = 65 then some eqRecT
      else if c = 64 then some eqReflT
      else if c = 63 then some eqFamT
      else none := by
  simp [eqEnvT, eqPrefixT, eqFamEnvT, extendEnv, emptyEnv]

/-! ## (2) family view and admissions -/

def eqFamDom0TyS :
    HasTy eqFamEnvT 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  HasTy.sort [] (.succ .zero)

def eqFamDom1TyS :
    HasTy eqFamEnvT 0 [.assumption (.sort (.succ .zero))] (.bvar 0)
      (.sort (.succ .zero)) :=
  HasTy.bvar _ 0 _ rfl

def eqFamDom2TyS :
    HasTy eqFamEnvT 0 [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]
      (.bvar 1) (.sort (.succ .zero)) :=
  HasTy.bvar _ 1 _ rfl

def eqFamViewS : PolicyFamilyView eqFamEnvT where
  ref := 63
  member := eqFamT
  present := rfl
  hasClass := rfl
  parameters := [.sort (.succ .zero), .bvar 0]
  indices := [.bvar 1]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun i => match i.val with | 0 => .succ (.succ .zero) | _ => .succ .zero
    bounded := fun i => by
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨n + 3, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [Expr.bvar 1] : List (Expr Nat))).length = 3 := rfl
          omega
    hasType := fun i => by
      match i with
      | ⟨0, _⟩ => exact eqFamDom0TyS
      | ⟨1, _⟩ => exact eqFamDom1TyS
      | ⟨2, _⟩ => exact eqFamDom2TyS
      | ⟨n + 3, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [Expr.bvar 1] : List (Expr Nat))).length = 3 := rfl
          omega
  }

/-- the same family seen from the recursor's prefix (65's scope). -/
def eqFamDom0TyR :
    HasTy eqPrefixT 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  HasTy.sort [] (.succ .zero)

def eqFamDom1TyR :
    HasTy eqPrefixT 0 [.assumption (.sort (.succ .zero))] (.bvar 0)
      (.sort (.succ .zero)) :=
  HasTy.bvar _ 0 _ rfl

def eqFamDom2TyR :
    HasTy eqPrefixT 0 [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]
      (.bvar 1) (.sort (.succ .zero)) :=
  HasTy.bvar _ 1 _ rfl

def eqFamViewR : PolicyFamilyView eqPrefixT where
  ref := 63
  member := eqFamT
  present := rfl
  hasClass := rfl
  parameters := [.sort (.succ .zero), .bvar 0]
  indices := [.bvar 1]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun i => match i.val with | 0 => .succ (.succ .zero) | _ => .succ .zero
    bounded := fun i => by
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨n + 3, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [Expr.bvar 1] : List (Expr Nat))).length = 3 := rfl
          omega
    hasType := fun i => by
      match i with
      | ⟨0, _⟩ => exact eqFamDom0TyR
      | ⟨1, _⟩ => exact eqFamDom1TyR
      | ⟨2, _⟩ => exact eqFamDom2TyR
      | ⟨n + 3, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [Expr.bvar 1] : List (Expr Nat))).length = 3 := rfl
          omega
  }

/-- constructor-domain typings for `refl`'s shared `[α, a]` telescope. -/
def eqReflDom0TyS :
    HasTy eqFamEnvT 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  eqFamDom0TyS

def eqReflDom1TyS :
    HasTy eqFamEnvT 0 [.assumption (.sort (.succ .zero))] (.bvar 0)
      (.sort (.succ .zero)) :=
  eqFamDom1TyS

def eqReflViewS : PolicyConstructorView eqFamEnvT eqFamViewS eqReflT where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ .zero), .bvar 0]
  fields := []
  resultIndices := [.bvar 0]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun i => match i.val with | 0 => .succ (.succ .zero) | _ => .succ .zero
    bounded := fun i => by
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨n + 2, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [] : List (Expr Nat))).length = 2 := rfl
          omega
    hasType := fun i => by
      match i with
      | ⟨0, _⟩ => exact eqReflDom0TyS
      | ⟨1, _⟩ => exact eqReflDom1TyS
      | ⟨n + 2, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [] : List (Expr Nat))).length = 2 := rfl
          omega
  }
  parameterMirrors := fun _ => Conv.refl _ _
  noFamilyInIndices := by
    intro e he
    rcases List.mem_singleton.mp he with rfl
    rfl

def eqReflDom0TyR :
    HasTy eqPrefixT 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  eqFamDom0TyR

def eqReflDom1TyR :
    HasTy eqPrefixT 0 [.assumption (.sort (.succ .zero))] (.bvar 0)
      (.sort (.succ .zero)) :=
  eqFamDom1TyR

def eqReflViewR : PolicyConstructorView eqPrefixT eqFamViewR eqReflT where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ .zero), .bvar 0]
  fields := []
  resultIndices := [.bvar 0]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun i => match i.val with | 0 => .succ (.succ .zero) | _ => .succ .zero
    bounded := fun i => by
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨n + 2, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [] : List (Expr Nat))).length = 2 := rfl
          omega
    hasType := fun i => by
      match i with
      | ⟨0, _⟩ => exact eqReflDom0TyR
      | ⟨1, _⟩ => exact eqReflDom1TyR
      | ⟨n + 2, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [] : List (Expr Nat))).length = 2 := rfl
          omega
  }
  parameterMirrors := fun _ => Conv.refl _ _
  noFamilyInIndices := by
    intro e he
    rcases List.mem_singleton.mp he with rfl
    rfl

theorem eqNoRec : NoRecursorFor eqFamEnvT 63 := by
  intro rr rm hmem hk _hrf
  rw [eqFamEnvT_mem] at hmem
  by_cases h63 : rr = 63
  · simp [h63] at hmem
    cases hmem
    simp [eqFamT] at hk
  · simp [h63] at hmem

def eqFamAdm : IndGroupAdmitted emptyEnv 63 eqFamT :=
  .family rfl eqFamViewS rfl rfl (.inl (fun _ => rfl))

def eqReflAdm : IndGroupAdmitted eqFamEnvT 64 eqReflT :=
  .constructor eqFamViewS eqReflViewS rfl
    ⟨63, rfl, eqNoRec⟩
    ⟨63, rfl, by decide,
      (fun c h1 h2 => False.elim (by omega)),
      (fun c hc => by
        obtain ⟨cm, hcm, hk, _⟩ := hc
        rw [eqFamEnvT_mem] at hcm
        by_cases h63 : c = 63
        · simp [h63] at hcm
          cases hcm
          simp [eqFamT] at hk
        · simp [h63] at hcm)⟩
    (fun j => j.elim0)
    (fun j => j.elim0)

/-! ## (3) the recursor admission -/

def eqGroupAdm : RecursorEliminationAdmitted eqPrefixT 65 eqRecT where
  family := eqFamViewR
  constructors := [eqReflT]
  constructorViews
    | ⟨0, _⟩ => eqReflViewR
    | ⟨n + 1, h⟩ => absurd (show n + 1 < 1 from by simpa using h) (by omega)
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨n + 1, h⟩ => absurd (show n + 1 < 1 from by simpa using h) (by omega)
  recursorRef := rfl
  minorTypes := [eqMinorT]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp (fun _ => rfl) rfl
    (fun i => by
      have hlt : i.val < 1 := by simpa using i.isLt
      have hv : i.val = 0 := by omega
      have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      subst hi
      exact fun j => j.elim0)
  recursorArity := rfl
  recursorType := rfl

theorem eqCensus : CtorCensus eqPrefixT 63 65 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hcm, hk, href⟩
    rw [eqPrefixT_mem] at hcm
    by_cases h64 : c = 64
    · rw [if_pos h64] at hcm
      cases hcm
      exact ⟨by omega, by omega⟩
    · by_cases h63 : c = 63
      · rw [if_neg h64, if_pos h63] at hcm
        cases hcm
        simp [eqFamT] at hk
      · rw [if_neg h64, if_neg h63] at hcm
        cases hcm
  · intro h
    have hc : c = 64 := by omega
    subst hc
    exact ⟨eqReflT, rfl, rfl, rfl⟩

theorem eqUniverse : ∀ i : Fin eqGroupAdm.constructors.length,
    FieldUniverseAdmitted (eqGroupAdm.constructorViews i)
  | ⟨0, _⟩, j => j.elim0
  | ⟨n + 1, h⟩, _ =>
      absurd (show n + 1 < 1 from by simpa [eqGroupAdm] using h) (by omega)

theorem eqFields : ∀ i : Fin eqGroupAdm.constructors.length,
    CtorFieldsPermitted (eqGroupAdm.constructorViews i)
  | ⟨0, _⟩, j => j.elim0
  | ⟨n + 1, h⟩, _ =>
      absurd (show n + 1 < 1 from by simpa [eqGroupAdm] using h) (by omega)

theorem eqMinorMatch : MinorPremisesMatch eqGroupAdm := by
  intro i
  have hlen : eqGroupAdm.constructors.length = 1 := rfl
  have hlt : i.val < 1 := by simpa [hlen] using i.isLt
  have hv : i.val = 0 := by omega
  have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hi]
  exact ⟨[], 0, rfl, rfl⟩

/-! ## (4) the refl-iota equation, honestly

`IotaEquationTyped` asks legacy `HasTy` of the reduct at `M a (refl α a)`
in the recursor's equation context `[b, m, M, a, α]` under `eqEnvT` at
arity 1 (`signatureOnly` keeps the recursor a signature there). The
field-free constructor's reduct IS the minor variable `bvar 1`: a single
lookup, lifted `lift 0 2` past `b` and `m` itself, lands exactly on
`iotaEquationType` — the `M`-applied-to-`a`-and-`refl` form. -/

/-- the equation domains are the stored recursor telescope without the
major: `[α, a, M, m, b]` in declaration order. -/
theorem eqEqDoms : equationDoms eqGroupAdm ⟨0, by decide⟩ =
    some [.sort (.succ .zero), .bvar 0, eqMotT, eqMinorT, .bvar 3] := rfl

/-- the field-free schema is the minor variable `m` itself. -/
theorem eqEqSchema : iotaSchemaAt eqGroupAdm ⟨0, by decide⟩ 0 [] =
    some (.bvar 1) := rfl

/-- the equation context: `[b, m, M, a, α]` (innermost first) — the index
binder, the minor, the motive, then the parameters. -/
def eqEqCtx : LCtx :=
  [.assumption (.bvar 3), .assumption eqMinorT, .assumption eqMotT,
    .assumption (.bvar 0), .assumption (.sort (.succ .zero))]

/-- `M a (Eq.refl α a)` — the motive at `refl`'s result index. -/
def eqEqLhs : Expr Nat :=
  .app (.app (.bvar 2) (.bvar 3))
    (.app (.app (.const 64 []) (.bvar 4)) (.bvar 3))

/-- the field-free reduct is the minor variable `m`, a single lookup. -/
def eqEqIotaTy : HasTy eqEnvT 1 eqEqCtx (.bvar 1) eqEqLhs :=
  HasTy.bvar _ 1 _ rfl

def eqIotaTyped :
    IotaEquationTyped eqGroupAdm ⟨0, by decide⟩ 0 [] := by
  unfold IotaEquationTyped
  rw [eqEqDoms, eqEqSchema]
  exact eqEqIotaTy

def eqIotaClause : IotaDescriptorClause eqPrefixT eqGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => []
  fuelAt := fun _ => 0
  analyzed := by
    intro i
    have hlen : eqGroupAdm.constructors.length = 1 := rfl
    have hlt : i.val < 1 := by simpa [hlen] using i.isLt
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    rw [hi]
    rfl
  typed
    | ⟨0, _⟩ => eqIotaTyped
    | ⟨n + 1, h⟩ =>
        absurd (show n + 1 < 1 from by simpa [eqGroupAdm] using h) (by omega)

def eqRecAdm : IndGroupAdmitted eqPrefixT 65 eqRecT :=
  .recursor eqGroupAdm rfl eqCensus eqUniverse eqFields
    eqMinorMatch eqIotaClause

/-! ## (5) checker leaves and the chain -/

kernel_rfl_theorem eqSortB0 :
    (sortTyAtC emptyEnv 0 96 [] eqFamT.mtype).isSome = true

kernel_rfl_theorem eqSortB1 :
    (sortTyAtC eqFamEnvT 0 96 [] eqReflT.mtype).isSome = true

kernel_rfl_theorem eqSortB2 :
    (sortTyAtC eqPrefixT 1 96 [] eqRecT.mtype).isSome = true

kernel_rfl_theorem eqAccB0 :
    memberAcceptB eqFamEnvT emptyEnv 96 eqFamAdm
      ((sortTyAtC emptyEnv 0 96 [] eqFamT.mtype).get eqSortB0).1 = true

kernel_rfl_theorem eqAccB1 :
    memberAcceptB eqFamEnvT eqFamEnvT 96 eqReflAdm
      ((sortTyAtC eqFamEnvT 0 96 [] eqReflT.mtype).get eqSortB1).1 = true

kernel_rfl_theorem eqAccB2 :
    memberAcceptB eqFamEnvT eqPrefixT 96 eqRecAdm
      ((sortTyAtC eqPrefixT 1 96 [] eqRecT.mtype).get eqSortB2).1 = true

def eqGroupChain :
    GroupAcceptChain eqFamEnvT 96 emptyEnv
      [(63, eqFamT), (64, eqReflT), (65, eqRecT)] eqEnvT :=
  .cons emptyEnv 63 eqFamT _ _ eqFamAdm eqSortB0 eqAccB0
    (.cons eqFamEnvT 64 eqReflT _ _ eqReflAdm eqSortB1 eqAccB1
      (.cons eqPrefixT 65 eqRecT _ _ eqRecAdm eqSortB2 eqAccB2
        (.nil eqEnvT)))

kernel_rfl_theorem eqClassB :
    groupClassB eqFamT [(64, eqReflT)] eqRecT = true

/-- the `.group` clause at the erased refs, assembled. -/
def pinEqGroupWfT : EnvWfT eqEnvT :=
  EG010T_group_accepted .empty 96 eqClassB eqGroupChain

#print axioms pinEqGroupWfT
#print axioms eqIotaTyped

end Rcic.Declarative
