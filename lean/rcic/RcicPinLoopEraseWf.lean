import rcic.RcicEGTypedGroup
import rcic.RcicAnnRecPins
import rcic.ScmSrcGroupsKernelRfl

set_option maxRecDepth 8192

/-!
# `EnvWfT (eraseEnv pinLoopEnvA)` — the erased Loop group's `.group` clause

`pinLoopEnvA` (60 `Loop : Prop`, 61 `mk : Loop → Loop`, 62 the AnySort
recursor) is well-formed on the ANN side by `pinLoopGroupRecWfA`'s `.groupRec`
step. M-a's open caveat on #6293: the ERASED side's `EnvWfT (eraseEnv
pinLoopEnvA)` — which every Loop-wall argument (F-05b, `iotaErasesA`) takes as
premise — was unassembled. This file pays it.

Route: `EG010T_group_accepted` over a `GroupAcceptChain` at `emptyEnv`, the
same route `ScmSrcGroupsEnvWfT*` uses for the real source groups. The three
`IndGroupAdmitted` cells are hand-built at the erased refs 60/61/62, mirroring
the Nat template (`RcicIndGroupAdmitted`): the family and constructor are
direct; the recursor carries a full `RecursorEliminationAdmitted`
(`singletonProp` selection, `minorTypes = [erase pinLoopMinorDomAt]`,
`recursorType := rfl` — the policy skeleton is the erasure of the Ann-side
`groupRecTypeA` computation) plus `CtorCensus`, `FieldUniverseAdmitted`,
`CtorFieldsPermitted`, `MinorPremisesMatch`, and an `IotaDescriptorClause`
whose `typed` field is an honest legacy `HasTy` derivation of the mk-iota
equation `m x (rec M m x) : M (mk x)` (the `natSuccIotaTy` template — the
legacy judgment is degenerate, but the descriptor asks for it and the honest
derivation exists). No `retypeAny`/collapse route is used anywhere.
-/

namespace Rcic.Declarative

open Rcic.Scm.SrcG (sortTyAtC)

/-! ## (1) the erased members and the prefix chain -/

def pinLoopFamT : CheckedMember := Ann.eraseMember Ann.pinLoopFamA
def pinLoopMkT : CheckedMember := Ann.eraseMember Ann.pinLoopMkA
def pinLoopRecT : CheckedMember := Ann.eraseMember Ann.pinLoopRecMemberA

def pinLoopFamEnvT : ResolvedEnv := extendEnv emptyEnv 60 pinLoopFamT
def pinLoopPrefixT : ResolvedEnv := extendEnv pinLoopFamEnvT 61 pinLoopMkT
def pinLoopEnvT : ResolvedEnv := extendEnv pinLoopPrefixT 62 pinLoopRecT

theorem pinLoopFamEnvT_mem (c : Nat) :
    pinLoopFamEnvT.members c =
      if c = 60 then some pinLoopFamT else none := by
  simp [pinLoopFamEnvT, extendEnv, emptyEnv]

theorem pinLoopPrefixT_mem (c : Nat) :
    pinLoopPrefixT.members c =
      if c = 61 then some pinLoopMkT
      else if c = 60 then some pinLoopFamT
      else none := by
  simp [pinLoopPrefixT, pinLoopFamEnvT, extendEnv, emptyEnv]

theorem pinLoopEnvT_mem (c : Nat) :
    pinLoopEnvT.members c =
      if c = 62 then some pinLoopRecT
      else if c = 61 then some pinLoopMkT
      else if c = 60 then some pinLoopFamT
      else none := by
  simp [pinLoopEnvT, pinLoopPrefixT, pinLoopFamEnvT, extendEnv, emptyEnv]

/-- `eraseEnv` of the Ann fixture unfolds pointwise to the `extendEnv`
    chain: `members_eraseEnv`/`members_eraseEnv_extend` per slot. -/
theorem eraseEnv_pinLoopEnvA : Ann.eraseEnv Ann.pinLoopEnvA = pinLoopEnvT := by
  apply congrArg ResolvedEnv.mk
  funext r'
  by_cases h62 : r' = 62 <;> by_cases h61 : r' = 61 <;> by_cases h60 : r' = 60 <;>
    simp [Ann.pinLoopEnvA, Ann.pinLoopFamEnvA, Ann.eraseEnv, Ann.extendEnvA, Ann.emptyEnvA,
      pinLoopEnvT, pinLoopPrefixT, pinLoopFamEnvT, extendEnv, emptyEnv,
      h62, h61, h60, Ann.eraseMember, pinLoopRecT, pinLoopMkT, pinLoopFamT]

/-! ## (2) the erased recursor type literals -/

/-- motive `Π (_ : Loop), Sort (param 0)` — `erase (pinLoopMotTyAt (.param 0))`. -/
def loopMotT : Expr Nat := .pi (.const 60 []) (.sort (.param 0))
/-- the single minor `Π (l : Loop), Π (ih : M l), M (mk l)` — `erase
    (pinLoopMinorDomAt …)`; `derivedMinor` computes exactly this. -/
def loopMinorT : Expr Nat :=
  .pi (.const 60 [])
    (.pi (.app (.bvar 1) (.bvar 0))
      (.app (.bvar 2) (.app (.const 61 []) (.bvar 1))))

theorem pinLoopRecT_mtype :
    pinLoopRecT.mtype =
      .pi loopMotT (.pi loopMinorT (.pi (.const 60 []) (.app (.bvar 2) (.bvar 0)))) :=
  rfl

/-! ## (3) family view and admissions -/

def pinLoopFamViewS : PolicyFamilyView pinLoopFamEnvT where
  ref := 60
  member := pinLoopFamT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

/-- the same family seen from the recursor's prefix (62's scope). -/
def pinLoopFamViewR : PolicyFamilyView pinLoopPrefixT where
  ref := 60
  member := pinLoopFamT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def pinLoopFieldTyS : HasTy pinLoopFamEnvT 0 [] (.const 60 []) (.sort .zero) :=
  HasTy.const [] 60 [] pinLoopFamT rfl rfl (fun _ h => nomatch h)

def pinLoopFieldTyR : HasTy pinLoopPrefixT 0 [] (.const 60 []) (.sort .zero) :=
  HasTy.const [] 60 [] pinLoopFamT rfl rfl (fun _ h => nomatch h)

def pinLoopMkViewS : PolicyConstructorView pinLoopFamEnvT pinLoopFamViewS pinLoopMkT where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const 60 []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlen : ([] ++ [(Expr.const 60 [] : Expr Nat)]).length = 1 := rfl
      have hlt : j.val < 1 := by simpa [hlen] using j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      subst hj
      simpa [policyPrefixContext] using pinLoopFieldTyS
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

def pinLoopMkViewR : PolicyConstructorView pinLoopPrefixT pinLoopFamViewR pinLoopMkT where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const 60 []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlen : ([] ++ [(Expr.const 60 [] : Expr Nat)]).length = 1 := rfl
      have hlt : j.val < 1 := by simpa [hlen] using j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      subst hj
      simpa [policyPrefixContext] using pinLoopFieldTyR
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

theorem pinLoopNoRec : NoRecursorFor pinLoopFamEnvT 60 := by
  intro rr rm hmem hk _hrf
  rw [pinLoopFamEnvT_mem] at hmem
  by_cases h60 : rr = 60
  · simp [h60] at hmem
    cases hmem
    simp [pinLoopFamT, Ann.eraseMember, Ann.pinLoopFamA] at hk
  · simp [h60] at hmem

def pinLoopFamAdm : IndGroupAdmitted emptyEnv 60 pinLoopFamT :=
  .family rfl pinLoopFamViewS rfl rfl (.inl (fun _ => rfl))

def pinLoopMkAdm : IndGroupAdmitted pinLoopFamEnvT 61 pinLoopMkT :=
  .constructor pinLoopFamViewS pinLoopMkViewS rfl
    ⟨60, rfl, pinLoopNoRec⟩
    ⟨60, rfl, by decide,
      (fun c h1 h2 => False.elim (by omega)),
      (fun c hc => by
        obtain ⟨cm, hcm, hk, _⟩ := hc
        rw [pinLoopFamEnvT_mem] at hcm
        by_cases h60 : c = 60
        · simp [h60] at hcm
          cases hcm
          simp [pinLoopFamT, Ann.eraseMember, Ann.pinLoopFamA] at hk
        · simp [h60] at hcm)⟩
    (fun j => .inl (fun _ => rfl))
    (fun j => by
      have hlen : pinLoopMkViewS.fields.length = 1 := rfl
      have hlt : j.val < 1 := by simpa [hlen] using j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      subst hj
      exact ⟨.recursive 0, 8, [], rfl⟩)

/-! ## (4) the recursor admission -/

def pinLoopGroupAdm : RecursorEliminationAdmitted pinLoopPrefixT 62 pinLoopRecT where
  family := pinLoopFamViewR
  constructors := [pinLoopMkT]
  constructorViews
    | ⟨0, _⟩ => pinLoopMkViewR
    | ⟨n + 1, h⟩ => absurd (show n + 1 < 1 from by simpa using h) (by omega)
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨n + 1, h⟩ => absurd (show n + 1 < 1 from by simpa using h) (by omega)
  recursorRef := rfl
  minorTypes := [loopMinorT]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp (fun _ => rfl) rfl
    (fun i => by
      have hlt : i.val < 1 := by simpa using i.isLt
      have hv : i.val = 0 := by omega
      have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      subst hi
      exact fun _ => .inl (fun _ => rfl))
  recursorArity := rfl
  recursorType := rfl

theorem pinLoopCensus : CtorCensus pinLoopPrefixT 60 62 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hcm, hk, href⟩
    rw [pinLoopPrefixT_mem] at hcm
    by_cases h61 : c = 61
    · rw [if_pos h61] at hcm
      cases hcm
      exact ⟨by omega, by omega⟩
    · by_cases h60 : c = 60
      · rw [if_neg h61, if_pos h60] at hcm
        cases hcm
        simp [pinLoopFamT, Ann.eraseMember, Ann.pinLoopFamA] at hk
      · rw [if_neg h61, if_neg h60] at hcm
        cases hcm
  · intro h
    have hc : c = 61 := by omega
    subst hc
    exact ⟨pinLoopMkT, rfl, rfl, rfl⟩

theorem pinLoopUniverse : ∀ i : Fin pinLoopGroupAdm.constructors.length,
    FieldUniverseAdmitted (pinLoopGroupAdm.constructorViews i)
  | ⟨0, _⟩, j => .inl (fun _ => rfl)
  | ⟨n + 1, h⟩, _ =>
      absurd (show n + 1 < 1 from by simpa [pinLoopGroupAdm] using h) (by omega)

theorem pinLoopFields : ∀ i : Fin pinLoopGroupAdm.constructors.length,
    CtorFieldsPermitted (pinLoopGroupAdm.constructorViews i)
  | ⟨0, _⟩, j => by
      have hlen : pinLoopMkViewR.fields.length = 1 := rfl
      have hlt : j.val < 1 := by simpa [hlen] using j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      subst hj
      exact ⟨.recursive 0, 8, [], rfl⟩
  | ⟨n + 1, h⟩, _ =>
      absurd (show n + 1 < 1 from by simpa [pinLoopGroupAdm] using h) (by omega)

theorem pinLoopMinorMatch : MinorPremisesMatch pinLoopGroupAdm := by
  intro i
  have hlen : pinLoopGroupAdm.constructors.length = 1 := rfl
  have hlt : i.val < 1 := by simpa [hlen] using i.isLt
  have hv : i.val = 0 := by omega
  have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hi]
  exact ⟨[.recursive 0], 8, rfl, rfl⟩

/-! ## (5) the mk-iota equation, honestly

`IotaEquationTyped` asks legacy `HasTy` of the reduct `m x (rec M m x)` at
`M (mk x)`, in `[x : Loop, m : minor, M : motive]` under `pinLoopEnvT` at
arity 1 (`signatureOnly` keeps the recursor a signature there). Same shape as
`natSuccIotaTy`, one minor fewer. -/

def pinLoopCtx : LCtx :=
  [.assumption (.const 60 []), .assumption loopMinorT, .assumption loopMotT]

def pinLoopRecHead : Expr Nat := .const 62 [.param 0]

def pinLoopRecApplied : Expr Nat :=
  foldApps pinLoopRecHead [.bvar 2, .bvar 1, .bvar 0]

def pinLoopRhs : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) pinLoopRecApplied

def pinLoopLhs : Expr Nat :=
  .app (.bvar 2) (.app (.const 61 []) (.bvar 0))

private def loopApp {f a A B : Expr Nat} {Γ : LCtx}
    (hf : HasTy pinLoopEnvT 1 Γ f (.pi A B))
    (ha : HasTy pinLoopEnvT 1 Γ a A) :
    HasTy pinLoopEnvT 1 Γ (.app f a) (instantiate0 a B) :=
  HasTy.app Γ f a A B hf ha

/-- the minor `m`'s stored type, lifted to the equation ctx (`lift 0 2`). -/
def loopMinorAt : Expr Nat :=
  .pi (.const 60 [])
    (.pi (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4) (.app (.const 61 []) (.bvar 1))))

/-- `rec`'s stored type (instantiateLevels at `[.param 0]` is the identity). -/
def loopRecTyU : Expr Nat :=
  .pi loopMotT (.pi loopMinorT (.pi (.const 60 []) (.app (.bvar 2) (.bvar 0))))

/-- stored tail of `loopRecTyU`, under the motive binder. -/
def loopCodP : Expr Nat :=
  .pi loopMinorT (.pi (.const 60 []) (.app (.bvar 2) (.bvar 0)))

/-- after `rec M`: the major pi `Π (t : Loop), M t` with `M` at ctx height. -/
def loopCodM : Expr Nat := .pi (.const 60 []) (.app (.bvar 4) (.bvar 0))
/-- after `rec M m`: `Π (t : Loop), M t`. -/
def loopCodT : Expr Nat := .pi (.const 60 []) (.app (.bvar 3) (.bvar 0))
/-- `m x : Π (ih : M x), M (mk x)`. -/
def loopMxTy : Expr Nat :=
  .pi (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const 61 []) (.bvar 1)))
/-- `M x` — the type of `rec M m x` and the minor's IH domain. -/
def loopMx : Expr Nat := .app (.bvar 2) (.bvar 0)

def pinLoopRecConstTy :
    HasTy pinLoopEnvT 1 pinLoopCtx pinLoopRecHead loopRecTyU :=
  HasTy.const pinLoopCtx 62 [.param 0] pinLoopRecT rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

def pinLoopIotaTy : HasTy pinLoopEnvT 1 pinLoopCtx pinLoopRhs pinLoopLhs := by
  have hM : HasTy pinLoopEnvT 1 pinLoopCtx (.bvar 2) loopMotT :=
    HasTy.bvar _ 2 loopMotT rfl
  have hm : HasTy pinLoopEnvT 1 pinLoopCtx (.bvar 1) loopMinorAt :=
    HasTy.bvar _ 1 loopMinorAt rfl
  have hx : HasTy pinLoopEnvT 1 pinLoopCtx (.bvar 0) (.const 60 []) :=
    HasTy.bvar _ 0 (.const 60 []) rfl
  have h0 : HasTy pinLoopEnvT 1 pinLoopCtx pinLoopRecHead (.pi loopMotT loopCodP) :=
    pinLoopRecConstTy
  have h1 := loopApp h0 hM
  have h1' : HasTy pinLoopEnvT 1 pinLoopCtx (.app pinLoopRecHead (.bvar 2))
      (.pi loopMinorAt loopCodM) :=
    h1
  have h2 := loopApp h1' hm
  have h2' : HasTy pinLoopEnvT 1 pinLoopCtx
      (.app (.app pinLoopRecHead (.bvar 2)) (.bvar 1)) loopCodT :=
    h2
  have h3 := loopApp h2' hx
  have h3' : HasTy pinLoopEnvT 1 pinLoopCtx pinLoopRecApplied loopMx := h3
  have h4 := loopApp hm hx
  have h4' : HasTy pinLoopEnvT 1 pinLoopCtx (.app (.bvar 1) (.bvar 0)) loopMxTy :=
    h4
  have h5 := loopApp h4' h3'
  have h5' : HasTy pinLoopEnvT 1 pinLoopCtx pinLoopRhs pinLoopLhs := h5
  exact h5'

def pinLoopIotaTyped :
    IotaEquationTyped pinLoopGroupAdm ⟨0, by decide⟩ 8 [.recursive 0] :=
  pinLoopIotaTy

def pinLoopIotaClause : IotaDescriptorClause pinLoopPrefixT pinLoopGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => [.recursive 0]
  fuelAt := fun _ => 8
  analyzed := by
    intro i
    have hlen : pinLoopGroupAdm.constructors.length = 1 := rfl
    have hlt : i.val < 1 := by simpa [hlen] using i.isLt
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    rw [hi]
    rfl
  typed
    | ⟨0, _⟩ => pinLoopIotaTyped
    | ⟨n + 1, h⟩ =>
        absurd (show n + 1 < 1 from by simpa [pinLoopGroupAdm] using h) (by omega)

def pinLoopRecAdm : IndGroupAdmitted pinLoopPrefixT 62 pinLoopRecT :=
  .recursor pinLoopGroupAdm rfl pinLoopCensus pinLoopUniverse pinLoopFields
    pinLoopMinorMatch pinLoopIotaClause

/-! ## (6) checker leaves and the chain -/

kernel_rfl_theorem pinLoopSortB0 :
    (sortTyAtC emptyEnv 0 96 [] pinLoopFamT.mtype).isSome = true

kernel_rfl_theorem pinLoopSortB1 :
    (sortTyAtC pinLoopFamEnvT 0 96 [] pinLoopMkT.mtype).isSome = true

kernel_rfl_theorem pinLoopSortB2 :
    (sortTyAtC pinLoopPrefixT 1 96 [] pinLoopRecT.mtype).isSome = true

kernel_rfl_theorem pinLoopAccB0 :
    memberAcceptB pinLoopFamEnvT emptyEnv 96 pinLoopFamAdm
      ((sortTyAtC emptyEnv 0 96 [] pinLoopFamT.mtype).get pinLoopSortB0).1 = true

kernel_rfl_theorem pinLoopAccB1 :
    memberAcceptB pinLoopFamEnvT pinLoopFamEnvT 96 pinLoopMkAdm
      ((sortTyAtC pinLoopFamEnvT 0 96 [] pinLoopMkT.mtype).get pinLoopSortB1).1 = true

kernel_rfl_theorem pinLoopAccB2 :
    memberAcceptB pinLoopFamEnvT pinLoopPrefixT 96 pinLoopRecAdm
      ((sortTyAtC pinLoopPrefixT 1 96 [] pinLoopRecT.mtype).get pinLoopSortB2).1 = true

def pinLoopGroupChain :
    GroupAcceptChain pinLoopFamEnvT 96 emptyEnv
      [(60, pinLoopFamT), (61, pinLoopMkT), (62, pinLoopRecT)] pinLoopEnvT :=
  .cons emptyEnv 60 pinLoopFamT _ _ pinLoopFamAdm pinLoopSortB0 pinLoopAccB0
    (.cons pinLoopFamEnvT 61 pinLoopMkT _ _ pinLoopMkAdm pinLoopSortB1 pinLoopAccB1
      (.cons pinLoopPrefixT 62 pinLoopRecT _ _ pinLoopRecAdm pinLoopSortB2 pinLoopAccB2
        (.nil pinLoopEnvT)))

kernel_rfl_theorem pinLoopClassB :
    groupClassB pinLoopFamT [(61, pinLoopMkT)] pinLoopRecT = true

/-- the `.group` clause at the erased refs, assembled. -/
def pinLoopGroupRecWfT : EnvWfT pinLoopEnvT :=
  EG010T_group_accepted .empty 96 pinLoopClassB pinLoopGroupChain

/-- **the derivation every Loop-wall argument takes**: the Ann fixture
    `pinLoopEnvA` erases to a well-formed typed environment. -/
def pinLoopEraseWfT : EnvWfT (Ann.eraseEnv Ann.pinLoopEnvA) :=
  eraseEnv_pinLoopEnvA ▸ pinLoopGroupRecWfT

#print axioms pinLoopEraseWfT
#print axioms pinLoopGroupRecWfT
#print axioms pinLoopIotaTy

end Rcic.Declarative
