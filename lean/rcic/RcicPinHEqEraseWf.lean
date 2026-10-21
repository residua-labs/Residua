import rcic.RcicEGTypedGroup
import rcic.ScmSrcGroupsKernelRfl

set_option maxRecDepth 8192

/-!
# `EnvWfT heqEnvT` — the erased `HEq` group's `.group` clause

The `HEq` twin of `RcicPinEqEraseWf` (F05b, cc on #6421): `HEq` at 63,
`HEq.refl` at 64, the AnySort recursor at 65. Family
`HEq : Π (α : Sort 1)(a : α)(β : Sort 1)(b : β), Sort 0` — `α, a` are
parameters, `β, b` the indices. Same carrier choice as `Eq`: `α : Sort 1`
(not `Prop`), so the `b ≢ a` gate-refusal case exists without proof
irrelevance collapsing the endpoints.

`HEq.refl` is field-free: the `singletonProp` selection is vacuous on
fields and the iota equation `m : M α a (refl α a)` is a single context
lookup at position 2 — the index binders `b, β` push the minor one slot
deeper than `Eq`'s equation context. Route: `EG010T_group_accepted`
over a `GroupAcceptChain` at `emptyEnv`, identical to the `Eq` fixture.
-/

namespace Rcic.Declarative

open Rcic.Scm.SrcG (sortTyAtC)

/-! ## (1) the erased members and the prefix chain -/

/-- `HEq : Π (α : Sort 1)(a : α)(β : Sort 1)(b : β), Sort 0` —
2 parameters, 2 indices. -/
def heqFamT : CheckedMember :=
  ⟨.inductiveM, 0,
    .pi (.sort (.succ .zero)) (.pi (.bvar 0)
      (.pi (.sort (.succ .zero)) (.pi (.bvar 0) (.sort .zero)))),
    none⟩

/-- `HEq.refl : Π (α : Sort 1)(a : α), HEq α a α a`. -/
def heqReflT : CheckedMember :=
  ⟨.constructorM, 0,
    .pi (.sort (.succ .zero))
      (.pi (.bvar 0)
        (foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 1, .bvar 0])),
    none⟩

/-- motive `Π (β : Sort 1)(b : β), HEq α a β b → Sort (param 0)` —
under `[a, α]` (innermost first). -/
def heqMotT : Expr Nat :=
  .pi (.sort (.succ .zero))
    (.pi (.bvar 0)
      (.pi (foldApps (.const 63 []) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])
        (.sort (.param 0))))

/-- minor `m : M α a (HEq.refl α a)` — under `[M, a, α]` (innermost
first): `M β b p` instantiated at the constructor's result indices
`(α, a)` and proof `refl α a`. -/
def heqMinorT : Expr Nat :=
  .app (.app (.app (.bvar 0) (.bvar 2)) (.bvar 1))
    (foldApps (.const 64 []) [.bvar 2, .bvar 1])

/-- the stored recursor type:
`Π (α : Sort 1)(a : α)(M : Π β b, HEq α a β b → Sort (param 0))
   (m : M α a (HEq.refl α a))(β : Sort 1)(b : β)(p : HEq α a β b),
   M β b p`. -/
def heqRecT : CheckedMember :=
  ⟨.recursorM, 1,
    .pi (.sort (.succ .zero))
      (.pi (.bvar 0)
        (.pi heqMotT
          (.pi heqMinorT
            (.pi (.sort (.succ .zero))
              (.pi (.bvar 0)
                (.pi (foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 1,
                      .bvar 0])
                  (.app (.app (.app (.bvar 4) (.bvar 2)) (.bvar 1))
                    (.bvar 0)))))))),
    none⟩

def heqFamEnvT : ResolvedEnv := extendEnv emptyEnv 63 heqFamT
def heqPrefixT : ResolvedEnv := extendEnv heqFamEnvT 64 heqReflT
def heqEnvT : ResolvedEnv := extendEnv heqPrefixT 65 heqRecT

theorem heqFamEnvT_mem (c : Nat) :
    heqFamEnvT.members c =
      if c = 63 then some heqFamT else none := by
  simp [heqFamEnvT, extendEnv, emptyEnv]

theorem heqPrefixT_mem (c : Nat) :
    heqPrefixT.members c =
      if c = 64 then some heqReflT
      else if c = 63 then some heqFamT
      else none := by
  simp [heqPrefixT, heqFamEnvT, extendEnv, emptyEnv]

theorem heqEnvT_mem (c : Nat) :
    heqEnvT.members c =
      if c = 65 then some heqRecT
      else if c = 64 then some heqReflT
      else if c = 63 then some heqFamT
      else none := by
  simp [heqEnvT, heqPrefixT, heqFamEnvT, extendEnv, emptyEnv]

/-! ## (2) family view and admissions -/

def heqFamDom0TyS :
    HasTy heqFamEnvT 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  HasTy.sort [] (.succ .zero)

def heqFamDom1TyS :
    HasTy heqFamEnvT 0 [.assumption (.sort (.succ .zero))] (.bvar 0)
      (.sort (.succ .zero)) :=
  HasTy.bvar _ 0 _ rfl

def heqFamDom2TyS :
    HasTy heqFamEnvT 0 [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  HasTy.sort _ (.succ .zero)

def heqFamDom3TyS :
    HasTy heqFamEnvT 0
      [.assumption (.sort (.succ .zero)), .assumption (.bvar 0),
        .assumption (.sort (.succ .zero))]
      (.bvar 0) (.sort (.succ .zero)) :=
  HasTy.bvar _ 0 _ rfl

def heqFamViewS : PolicyFamilyView heqFamEnvT where
  ref := 63
  member := heqFamT
  present := rfl
  hasClass := rfl
  parameters := [.sort (.succ .zero), .bvar 0]
  indices := [.sort (.succ .zero), .bvar 0]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun i => match i.val with
      | 0 => .succ (.succ .zero)
      | 2 => .succ (.succ .zero)
      | _ => .succ .zero
    bounded := fun i => by
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
      | ⟨n + 4, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [Expr.sort (.succ .zero),
                Expr.bvar 0] : List (Expr Nat))).length = 4 := rfl
          omega
    hasType := fun i => by
      match i with
      | ⟨0, _⟩ => exact heqFamDom0TyS
      | ⟨1, _⟩ => exact heqFamDom1TyS
      | ⟨2, _⟩ => exact heqFamDom2TyS
      | ⟨3, _⟩ => exact heqFamDom3TyS
      | ⟨n + 4, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [Expr.sort (.succ .zero),
                Expr.bvar 0] : List (Expr Nat))).length = 4 := rfl
          omega
  }

/-- the same family seen from the recursor's prefix (65's scope). -/
def heqFamDom0TyR :
    HasTy heqPrefixT 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  HasTy.sort [] (.succ .zero)

def heqFamDom1TyR :
    HasTy heqPrefixT 0 [.assumption (.sort (.succ .zero))] (.bvar 0)
      (.sort (.succ .zero)) :=
  HasTy.bvar _ 0 _ rfl

def heqFamDom2TyR :
    HasTy heqPrefixT 0 [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  HasTy.sort _ (.succ .zero)

def heqFamDom3TyR :
    HasTy heqPrefixT 0
      [.assumption (.sort (.succ .zero)), .assumption (.bvar 0),
        .assumption (.sort (.succ .zero))]
      (.bvar 0) (.sort (.succ .zero)) :=
  HasTy.bvar _ 0 _ rfl

def heqFamViewR : PolicyFamilyView heqPrefixT where
  ref := 63
  member := heqFamT
  present := rfl
  hasClass := rfl
  parameters := [.sort (.succ .zero), .bvar 0]
  indices := [.sort (.succ .zero), .bvar 0]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun i => match i.val with
      | 0 => .succ (.succ .zero)
      | 2 => .succ (.succ .zero)
      | _ => .succ .zero
    bounded := fun i => by
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
      | ⟨n + 4, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [Expr.sort (.succ .zero),
                Expr.bvar 0] : List (Expr Nat))).length = 4 := rfl
          omega
    hasType := fun i => by
      match i with
      | ⟨0, _⟩ => exact heqFamDom0TyR
      | ⟨1, _⟩ => exact heqFamDom1TyR
      | ⟨2, _⟩ => exact heqFamDom2TyR
      | ⟨3, _⟩ => exact heqFamDom3TyR
      | ⟨n + 4, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [Expr.sort (.succ .zero),
                Expr.bvar 0] : List (Expr Nat))).length = 4 := rfl
          omega
  }

/-- constructor-domain typings for `refl`'s shared `[α, a]` telescope. -/
def heqReflDom0TyS :
    HasTy heqFamEnvT 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  heqFamDom0TyS

def heqReflDom1TyS :
    HasTy heqFamEnvT 0 [.assumption (.sort (.succ .zero))] (.bvar 0)
      (.sort (.succ .zero)) :=
  heqFamDom1TyS

def heqReflViewS : PolicyConstructorView heqFamEnvT heqFamViewS heqReflT where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ .zero), .bvar 0]
  fields := []
  resultIndices := [.bvar 1, .bvar 0]
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
      | ⟨0, _⟩ => exact heqReflDom0TyS
      | ⟨1, _⟩ => exact heqReflDom1TyS
      | ⟨n + 2, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [] : List (Expr Nat))).length = 2 := rfl
          omega
  }
  parameterMirrors := fun _ => Conv.refl _ _
  noFamilyInIndices := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he2
    · rfl
    · rcases List.mem_singleton.mp he2 with rfl
      rfl

def heqReflDom0TyR :
    HasTy heqPrefixT 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  heqFamDom0TyR

def heqReflDom1TyR :
    HasTy heqPrefixT 0 [.assumption (.sort (.succ .zero))] (.bvar 0)
      (.sort (.succ .zero)) :=
  heqFamDom1TyR

def heqReflViewR : PolicyConstructorView heqPrefixT heqFamViewR heqReflT where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ .zero), .bvar 0]
  fields := []
  resultIndices := [.bvar 1, .bvar 0]
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
      | ⟨0, _⟩ => exact heqReflDom0TyR
      | ⟨1, _⟩ => exact heqReflDom1TyR
      | ⟨n + 2, h⟩ =>
          have hlen :
            (([Expr.sort (.succ .zero), Expr.bvar 0] ++ [] : List (Expr Nat))).length = 2 := rfl
          omega
  }
  parameterMirrors := fun _ => Conv.refl _ _
  noFamilyInIndices := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he2
    · rfl
    · rcases List.mem_singleton.mp he2 with rfl
      rfl

theorem heqNoRec : NoRecursorFor heqFamEnvT 63 := by
  intro rr rm hmem hk _hrf
  rw [heqFamEnvT_mem] at hmem
  by_cases h63 : rr = 63
  · simp [h63] at hmem
    cases hmem
    simp [heqFamT] at hk
  · simp [h63] at hmem

def heqFamAdm : IndGroupAdmitted emptyEnv 63 heqFamT :=
  .family rfl heqFamViewS rfl rfl (.inl (fun _ => rfl))

def heqReflAdm : IndGroupAdmitted heqFamEnvT 64 heqReflT :=
  .constructor heqFamViewS heqReflViewS rfl
    ⟨63, rfl, heqNoRec⟩
    ⟨63, rfl, by decide,
      (fun c h1 h2 => False.elim (by omega)),
      (fun c hc => by
        obtain ⟨cm, hcm, hk, _⟩ := hc
        rw [heqFamEnvT_mem] at hcm
        by_cases h63 : c = 63
        · simp [h63] at hcm
          cases hcm
          simp [heqFamT] at hk
        · simp [h63] at hcm)⟩
    (fun j => j.elim0)
    (fun j => j.elim0)

/-! ## (3) the recursor admission -/

def heqGroupAdm : RecursorEliminationAdmitted heqPrefixT 65 heqRecT where
  family := heqFamViewR
  constructors := [heqReflT]
  constructorViews
    | ⟨0, _⟩ => heqReflViewR
    | ⟨n + 1, h⟩ => absurd (show n + 1 < 1 from by simpa using h) (by omega)
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨n + 1, h⟩ => absurd (show n + 1 < 1 from by simpa using h) (by omega)
  recursorRef := rfl
  minorTypes := [heqMinorT]
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

theorem heqCensus : CtorCensus heqPrefixT 63 65 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hcm, hk, href⟩
    rw [heqPrefixT_mem] at hcm
    by_cases h64 : c = 64
    · rw [if_pos h64] at hcm
      cases hcm
      exact ⟨by omega, by omega⟩
    · by_cases h63 : c = 63
      · rw [if_neg h64, if_pos h63] at hcm
        cases hcm
        simp [heqFamT] at hk
      · rw [if_neg h64, if_neg h63] at hcm
        cases hcm
  · intro h
    have hc : c = 64 := by omega
    subst hc
    exact ⟨heqReflT, rfl, rfl, rfl⟩

theorem heqUniverse : ∀ i : Fin heqGroupAdm.constructors.length,
    FieldUniverseAdmitted (heqGroupAdm.constructorViews i)
  | ⟨0, _⟩, j => j.elim0
  | ⟨n + 1, h⟩, _ =>
      absurd (show n + 1 < 1 from by simpa [heqGroupAdm] using h) (by omega)

theorem heqFields : ∀ i : Fin heqGroupAdm.constructors.length,
    CtorFieldsPermitted (heqGroupAdm.constructorViews i)
  | ⟨0, _⟩, j => j.elim0
  | ⟨n + 1, h⟩, _ =>
      absurd (show n + 1 < 1 from by simpa [heqGroupAdm] using h) (by omega)

theorem heqMinorMatch : MinorPremisesMatch heqGroupAdm := by
  intro i
  have hlen : heqGroupAdm.constructors.length = 1 := rfl
  have hlt : i.val < 1 := by simpa [hlen] using i.isLt
  have hv : i.val = 0 := by omega
  have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hi]
  exact ⟨[], 0, rfl, rfl⟩

/-! ## (4) the refl-iota equation, honestly

`IotaEquationTyped` asks legacy `HasTy` of the reduct at
`M α a (HEq.refl α a)` in the recursor's equation context
`[b, β, m, M, a, α]` under `heqEnvT` at arity 1 (`signatureOnly` keeps
the recursor a signature there). The field-free constructor's reduct IS
the minor variable `bvar 2` — the TWO index binders `b, β` push `m` one
slot deeper than `Eq`'s `bvar 1`. -/

/-- the equation domains are the stored recursor telescope without the
major: `[α, a, M, m, β, b]` in declaration order. -/
theorem heqEqDoms : equationDoms heqGroupAdm ⟨0, by decide⟩ =
    some [.sort (.succ .zero), .bvar 0, heqMotT, heqMinorT,
      .sort (.succ .zero), .bvar 0] := rfl

/-- the field-free schema is the minor variable `m` itself. -/
theorem heqEqSchema : iotaSchemaAt heqGroupAdm ⟨0, by decide⟩ 0 [] =
    some (.bvar 2) := rfl

/-- the equation context: `[b, β, m, M, a, α]` (innermost first) — the
value index `b : β`, the type index `β`, the minor, the motive, then
the parameters. -/
def heqEqCtx : LCtx :=
  [.assumption (.bvar 0), .assumption (.sort (.succ .zero)),
    .assumption heqMinorT, .assumption heqMotT,
    .assumption (.bvar 0), .assumption (.sort (.succ .zero))]

/-- `M α a (HEq.refl α a)` — the motive at `refl`'s result indices. -/
def heqEqLhs : Expr Nat :=
  .app (.app (.app (.bvar 3) (.bvar 5)) (.bvar 4))
    (foldApps (.const 64 []) [.bvar 5, .bvar 4])

/-- the field-free reduct is the minor variable `m`, a single lookup. -/
def heqEqIotaTy : HasTy heqEnvT 1 heqEqCtx (.bvar 2) heqEqLhs :=
  HasTy.bvar _ 2 _ rfl

def heqIotaTyped :
    IotaEquationTyped heqGroupAdm ⟨0, by decide⟩ 0 [] := by
  unfold IotaEquationTyped
  rw [heqEqDoms, heqEqSchema]
  exact heqEqIotaTy

def heqIotaClause : IotaDescriptorClause heqPrefixT heqGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => []
  fuelAt := fun _ => 0
  analyzed := by
    intro i
    have hlen : heqGroupAdm.constructors.length = 1 := rfl
    have hlt : i.val < 1 := by simpa [hlen] using i.isLt
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    rw [hi]
    rfl
  typed
    | ⟨0, _⟩ => heqIotaTyped
    | ⟨n + 1, h⟩ =>
        absurd (show n + 1 < 1 from by simpa [heqGroupAdm] using h) (by omega)

def heqRecAdm : IndGroupAdmitted heqPrefixT 65 heqRecT :=
  .recursor heqGroupAdm rfl heqCensus heqUniverse heqFields
    heqMinorMatch heqIotaClause

/-! ## (5) checker leaves and the chain -/

kernel_rfl_theorem heqSortB0 :
    (sortTyAtC emptyEnv 0 96 [] heqFamT.mtype).isSome = true

kernel_rfl_theorem heqSortB1 :
    (sortTyAtC heqFamEnvT 0 96 [] heqReflT.mtype).isSome = true

kernel_rfl_theorem heqSortB2 :
    (sortTyAtC heqPrefixT 1 96 [] heqRecT.mtype).isSome = true

kernel_rfl_theorem heqAccB0 :
    memberAcceptB heqFamEnvT emptyEnv 96 heqFamAdm
      ((sortTyAtC emptyEnv 0 96 [] heqFamT.mtype).get heqSortB0).1 = true

kernel_rfl_theorem heqAccB1 :
    memberAcceptB heqFamEnvT heqFamEnvT 96 heqReflAdm
      ((sortTyAtC heqFamEnvT 0 96 [] heqReflT.mtype).get heqSortB1).1 = true

kernel_rfl_theorem heqAccB2 :
    memberAcceptB heqFamEnvT heqPrefixT 96 heqRecAdm
      ((sortTyAtC heqPrefixT 1 96 [] heqRecT.mtype).get heqSortB2).1 = true

def heqGroupChain :
    GroupAcceptChain heqFamEnvT 96 emptyEnv
      [(63, heqFamT), (64, heqReflT), (65, heqRecT)] heqEnvT :=
  .cons emptyEnv 63 heqFamT _ _ heqFamAdm heqSortB0 heqAccB0
    (.cons heqFamEnvT 64 heqReflT _ _ heqReflAdm heqSortB1 heqAccB1
      (.cons heqPrefixT 65 heqRecT _ _ heqRecAdm heqSortB2 heqAccB2
        (.nil heqEnvT)))

kernel_rfl_theorem heqClassB :
    groupClassB heqFamT [(64, heqReflT)] heqRecT = true

/-- the `.group` clause at the erased refs, assembled. -/
def pinHEqGroupWfT : EnvWfT heqEnvT :=
  EG010T_group_accepted .empty 96 heqClassB heqGroupChain

#print axioms pinHEqGroupWfT
#print axioms heqIotaTyped

end Rcic.Declarative
