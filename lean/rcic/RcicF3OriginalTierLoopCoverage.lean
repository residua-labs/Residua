import rcic.RcicF3LoopFixture
import rcic.RcicF3StepWDApex
import rcic.RcicF3DBoundBridge

/-!
# Original-domain D-coverage counterexample

The original False group remains at refs 0/1. The existing erased Loop
signature is admitted over it at refs 60/61/62. No original statement is changed.
The target is a complete counterexample to D-check coverage on the
original bounded, axiom-free, False-prefixed tier domain, at EVERY K.
This refutes neither the original tier nor its consistency conclusion.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Rcic.Declarative.FalseLoopCoverage

open Rcic.Declarative
noncomputable section

open Rcic.Scm.SrcG (sortTyAtC)

/-! ## (1) the erased members and the prefix chain -/

noncomputable def pinLoopFamT : CheckedMember := Ann.eraseMember Ann.pinLoopFamA
noncomputable def pinLoopMkT : CheckedMember := Ann.eraseMember Ann.pinLoopMkA
noncomputable def pinLoopRecT : CheckedMember := Ann.eraseMember Ann.pinLoopRecMemberA

noncomputable def pinLoopFamEnvT : ResolvedEnv := extendEnv falseEnvU 60 pinLoopFamT
noncomputable def pinLoopPrefixT : ResolvedEnv := extendEnv pinLoopFamEnvT 61 pinLoopMkT
noncomputable def pinLoopEnvT : ResolvedEnv := extendEnv pinLoopPrefixT 62 pinLoopRecT

theorem pinLoopFamEnvT_mem (c : Nat) :
    pinLoopFamEnvT.members c =
      if c = 60 then some pinLoopFamT else falseEnvU.members c := by
  simp [pinLoopFamEnvT, extendEnv]

theorem pinLoopPrefixT_mem (c : Nat) :
    pinLoopPrefixT.members c =
      if c = 61 then some pinLoopMkT
      else if c = 60 then some pinLoopFamT
      else falseEnvU.members c := by
  simp [pinLoopPrefixT, pinLoopFamEnvT, extendEnv]

theorem pinLoopEnvT_mem (c : Nat) :
    pinLoopEnvT.members c =
      if c = 62 then some pinLoopRecT
      else if c = 61 then some pinLoopMkT
      else if c = 60 then some pinLoopFamT
      else falseEnvU.members c := by
  simp [pinLoopEnvT, pinLoopPrefixT, pinLoopFamEnvT, extendEnv]

/-! ## (2) the erased recursor type literals -/

/-- motive `Π (_ : Loop), Sort (param 0)` — `erase (pinLoopMotTyAt (.param 0))`. -/
noncomputable def loopMotT : Expr Nat := .pi (.const 60 []) (.sort (.param 0))
/-- the single minor `Π (l : Loop), Π (ih : M l), M (mk l)` — `erase
    (pinLoopMinorDomAt …)`; `derivedMinor` computes exactly this. -/
noncomputable def loopMinorT : Expr Nat :=
  .pi (.const 60 [])
    (.pi (.app (.bvar 1) (.bvar 0))
      (.app (.bvar 2) (.app (.const 61 []) (.bvar 1))))

theorem pinLoopRecT_mtype :
    pinLoopRecT.mtype =
      .pi loopMotT (.pi loopMinorT (.pi (.const 60 []) (.app (.bvar 2) (.bvar 0)))) :=
  rfl

/-! ## (3) family view and admissions -/

noncomputable def pinLoopFamViewS : PolicyFamilyView pinLoopFamEnvT where
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
noncomputable def pinLoopFamViewR : PolicyFamilyView pinLoopPrefixT where
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

noncomputable def pinLoopFieldTyS : HasTy pinLoopFamEnvT 0 [] (.const 60 []) (.sort .zero) :=
  HasTy.const [] 60 [] pinLoopFamT rfl rfl (fun _ h => nomatch h)

noncomputable def pinLoopFieldTyR : HasTy pinLoopPrefixT 0 [] (.const 60 []) (.sort .zero) :=
  HasTy.const [] 60 [] pinLoopFamT rfl rfl (fun _ h => nomatch h)

noncomputable def pinLoopMkViewS : PolicyConstructorView pinLoopFamEnvT pinLoopFamViewS pinLoopMkT where
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

noncomputable def pinLoopMkViewR : PolicyConstructorView pinLoopPrefixT pinLoopFamViewR pinLoopMkT where
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

theorem false_member_cases {r : Nat} {m : CheckedMember}
    (hm : falseEnvU.members r = some m) :
    (r = 0 ∧ m = falseFamMember) ∨ (r = 1 ∧ m = falseRecMemberU) := by
  match r, hm with
  | 0, hm => cases hm; exact Or.inl ⟨rfl, rfl⟩
  | 1, hm => cases hm; exact Or.inr ⟨rfl, rfl⟩
  | r + 2, hm =>
      rw [Rcic.F3.PSet.falseEnvU_m2 r] at hm
      cases hm

theorem false_no_constructor {r : Nat} {m : CheckedMember}
    (hm : falseEnvU.members r = some m) : m.mclass ≠ .constructorM := by
  rcases false_member_cases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide

theorem pinLoopNoRec : NoRecursorFor pinLoopFamEnvT 60 := by
  intro rr rm hmem hk hrf
  rw [pinLoopFamEnvT_mem] at hmem
  by_cases h60 : rr = 60
  · rw [if_pos h60] at hmem
    cases hmem
    cases hk
  · rw [if_neg h60] at hmem
    rcases false_member_cases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · cases hk
    · have hzero : memberFamRef falseRecMemberU = some 0 := rfl
      rw [hzero] at hrf
      cases hrf

noncomputable def pinLoopFamAdm : IndGroupAdmitted falseEnvU 60 pinLoopFamT :=
  .family rfl pinLoopFamViewS rfl rfl (.inl (fun _ => rfl))

noncomputable def pinLoopMkAdm : IndGroupAdmitted pinLoopFamEnvT 61 pinLoopMkT :=
  .constructor pinLoopFamViewS pinLoopMkViewS rfl
    ⟨60, rfl, pinLoopNoRec⟩
    ⟨60, rfl, by decide,
      (fun c h1 h2 => False.elim (by omega)),
      (fun c hc => by
        obtain ⟨cm, hcm, hk, _⟩ := hc
        rw [pinLoopFamEnvT_mem] at hcm
        by_cases h60 : c = 60
        · rw [if_pos h60] at hcm
          cases hcm
          cases hk
        · rw [if_neg h60] at hcm
          exact (false_no_constructor hcm hk).elim)⟩
    (fun j => .inl (fun _ => rfl))
    (fun j => by
      have hlt : j.val < 1 := j.isLt
      have hv : j.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      subst hj
      exact ⟨.recursive 0, 8, [], rfl⟩)

/-! ## (4) the recursor admission -/

noncomputable def pinLoopGroupAdm : RecursorEliminationAdmitted pinLoopPrefixT 62 pinLoopRecT where
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
  recursorMclass := rfl

theorem pinLoopCensus : CtorCensus pinLoopPrefixT 60 62 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hcm, hk, href⟩
    rw [pinLoopPrefixT_mem] at hcm
    by_cases h61 : c = 61
    · exact ⟨by omega, by omega⟩
    · rw [if_neg h61] at hcm
      by_cases h60 : c = 60
      · rw [if_pos h60] at hcm
        cases hcm
        cases hk
      · rw [if_neg h60] at hcm
        exact (false_no_constructor hcm hk).elim
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

noncomputable def pinLoopCtx : LCtx :=
  [.assumption (.const 60 []), .assumption loopMinorT, .assumption loopMotT]

noncomputable def pinLoopRecHead : Expr Nat := .const 62 [.param 0]

noncomputable def pinLoopRecApplied : Expr Nat :=
  foldApps pinLoopRecHead [.bvar 2, .bvar 1, .bvar 0]

noncomputable def pinLoopRhs : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) pinLoopRecApplied

noncomputable def pinLoopLhs : Expr Nat :=
  .app (.bvar 2) (.app (.const 61 []) (.bvar 0))

private noncomputable def loopApp {f a A B : Expr Nat} {Γ : LCtx}
    (hf : HasTy pinLoopEnvT 1 Γ f (.pi A B))
    (ha : HasTy pinLoopEnvT 1 Γ a A) :
    HasTy pinLoopEnvT 1 Γ (.app f a) (instantiate0 a B) :=
  HasTy.app Γ f a A B hf ha

/-- the minor `m`'s stored type, lifted to the equation ctx (`lift 0 2`). -/
noncomputable def loopMinorAt : Expr Nat :=
  .pi (.const 60 [])
    (.pi (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4) (.app (.const 61 []) (.bvar 1))))

/-- `rec`'s stored type (instantiateLevels at `[.param 0]` is the identity). -/
noncomputable def loopRecTyU : Expr Nat :=
  .pi loopMotT (.pi loopMinorT (.pi (.const 60 []) (.app (.bvar 2) (.bvar 0))))

/-- stored tail of `loopRecTyU`, under the motive binder. -/
noncomputable def loopCodP : Expr Nat :=
  .pi loopMinorT (.pi (.const 60 []) (.app (.bvar 2) (.bvar 0)))

/-- after `rec M`: the major pi `Π (t : Loop), M t` with `M` at ctx height. -/
noncomputable def loopCodM : Expr Nat := .pi (.const 60 []) (.app (.bvar 4) (.bvar 0))
/-- after `rec M m`: `Π (t : Loop), M t`. -/
noncomputable def loopCodT : Expr Nat := .pi (.const 60 []) (.app (.bvar 3) (.bvar 0))
/-- `m x : Π (ih : M x), M (mk x)`. -/
noncomputable def loopMxTy : Expr Nat :=
  .pi (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app (.const 61 []) (.bvar 1)))
/-- `M x` — the type of `rec M m x` and the minor's IH domain. -/
noncomputable def loopMx : Expr Nat := .app (.bvar 2) (.bvar 0)

noncomputable def pinLoopRecConstTy :
    HasTy pinLoopEnvT 1 pinLoopCtx pinLoopRecHead loopRecTyU :=
  HasTy.const pinLoopCtx 62 [.param 0] pinLoopRecT rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

noncomputable def pinLoopIotaTy : HasTy pinLoopEnvT 1 pinLoopCtx pinLoopRhs pinLoopLhs := by
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

noncomputable def pinLoopIotaTyped :
    IotaEquationTyped pinLoopGroupAdm ⟨0, by decide⟩ 8 [.recursive 0] :=
  pinLoopIotaTy

noncomputable def pinLoopIotaClause : IotaDescriptorClause pinLoopPrefixT pinLoopGroupAdm where
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

noncomputable def pinLoopRecAdm : IndGroupAdmitted pinLoopPrefixT 62 pinLoopRecT :=
  .recursor pinLoopGroupAdm rfl pinLoopCensus pinLoopUniverse pinLoopFields
    pinLoopMinorMatch pinLoopIotaClause

/-! ## (6) checker leaves and the chain -/

kernel_rfl_theorem pinLoopSortB0 :
    (sortTyAtC falseEnvU 0 96 [] pinLoopFamT.mtype).isSome = true

kernel_rfl_theorem pinLoopSortB1 :
    (sortTyAtC pinLoopFamEnvT 0 96 [] pinLoopMkT.mtype).isSome = true

kernel_rfl_theorem pinLoopSortB2 :
    (sortTyAtC pinLoopPrefixT 1 96 [] pinLoopRecT.mtype).isSome = true

kernel_rfl_theorem pinLoopAccB0 :
    memberAcceptB pinLoopFamEnvT falseEnvU 96 pinLoopFamAdm
      ((sortTyAtC falseEnvU 0 96 [] pinLoopFamT.mtype).get pinLoopSortB0).1 = true

kernel_rfl_theorem pinLoopAccB1 :
    memberAcceptB pinLoopFamEnvT pinLoopFamEnvT 96 pinLoopMkAdm
      ((sortTyAtC pinLoopFamEnvT 0 96 [] pinLoopMkT.mtype).get pinLoopSortB1).1 = true

kernel_rfl_theorem pinLoopAccB2 :
    memberAcceptB pinLoopFamEnvT pinLoopPrefixT 96 pinLoopRecAdm
      ((sortTyAtC pinLoopPrefixT 1 96 [] pinLoopRecT.mtype).get pinLoopSortB2).1 = true

noncomputable def pinLoopGroupChain :
    GroupAcceptChain pinLoopFamEnvT 96 falseEnvU
      [(60, pinLoopFamT), (61, pinLoopMkT), (62, pinLoopRecT)] pinLoopEnvT :=
  .cons falseEnvU 60 pinLoopFamT _ _ pinLoopFamAdm pinLoopSortB0 pinLoopAccB0
    (.cons pinLoopFamEnvT 61 pinLoopMkT _ _ pinLoopMkAdm pinLoopSortB1 pinLoopAccB1
      (.cons pinLoopPrefixT 62 pinLoopRecT _ _ pinLoopRecAdm pinLoopSortB2 pinLoopAccB2
        (.nil pinLoopEnvT)))

kernel_rfl_theorem pinLoopClassB :
    groupClassB pinLoopFamT [(61, pinLoopMkT)] pinLoopRecT = true

/-- the `.group` clause at the erased refs, assembled. -/
noncomputable def pinLoopGroupRecWfT : EnvWfT pinLoopEnvT :=
  EG010T_group_accepted falseEnvUWfT 96 pinLoopClassB pinLoopGroupChain


/-! ## Original bounds and exact coverage failure -/

open Rcic.F3.PSet
open Rcic.F3.StepDGOrder Rcic.F3.StepWCheck

/-- The recursor node of the `Loop` block. -/
abbrev LoopNode := RecNode falseEnvU pinLoopEnvT 60 62 pinLoopRecT

theorem loop_fam (node : LoopNode) : node.a.family.member = pinLoopFamT :=
  Option.some.inj ((node_fam_member node).symm.trans rfl)

/-- The family view of the `Loop` block: no parameters, no indices, level 0. -/
theorem loop_family (node : LoopNode) :
    node.a.family.parameters = [] ∧ node.a.family.indices = [] ∧ node.a.family.resultLevel = .zero := by
  have hst := node.a.family.storedType
  rw [loop_fam node] at hst
  obtain ⟨h1, h2⟩ := policyPi_split_eq [] _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) hst
  have h3 := List.append_eq_nil.mp h1.symm
  injection h2 with h4
  exact ⟨h3.1, h3.2, h4.symm⟩

theorem loop_ctor (node : LoopNode) (i : Fin node.a.constructors.length) :
    node.a.constructors[i.val] = pinLoopMkT ∧ i.val = 0 := by
  have hlen : node.a.constructors.length = 1 := node_ctors_length (ctors := [(61, pinLoopMkT)]) node rfl
  obtain ⟨k, hk⟩ := i
  have h := node_ctor_member node ⟨k, hk⟩
  have hi : k < 1 := hlen ▸ hk
  match k, hk, hi, h with
  | 0, _, _, h => exact ⟨Option.some.inj (h.symm.trans rfl), rfl⟩

/-- The constructor view of `mk`: no parameters or result indices, the one field `Loop`. -/
theorem loop_view (node : LoopNode) (i : Fin node.a.constructors.length) :
    (node.a.constructorViews i).parameters = [] ∧ (node.a.constructorViews i).resultIndices = [] ∧
      (node.a.constructorViews i).fields = [.const 60 []] := by
  obtain ⟨hP, hI, _⟩ := loop_family node
  have hp : (node.a.constructorViews i).parameters = [] := by
    have := (node.a.constructorViews i).parameterCount
    rw [hP] at this
    exact List.eq_nil_of_length_eq_zero this
  have hr : (node.a.constructorViews i).resultIndices = [] := by
    have := (node.a.constructorViews i).indexCount
    rw [hI] at this
    exact List.eq_nil_of_length_eq_zero this
  refine ⟨hp, hr, ?_⟩
  have hst := (node.a.constructorViews i).storedType
  rw [hp, List.nil_append] at hst
  have hne := foldApps_ne_pi (.const node.a.family.ref (policyFamilyLevels node.a.family))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals 0 (node.a.constructorViews i).fields.length ++
      (node.a.constructorViews i).resultIndices)
  have hm : (node.a.constructors[i.val]).mtype = policyPi [.const 60 []] (.const 60 []) := by
    rw [(loop_ctor node i).1]; rfl
  exact (policyPi_split_eq [.const 60 []] _ (.const 60 []) _ (fun _ _ h => Expr.noConfusion h) hne
    (hm.symm.trans hst)).1.symm

/-- `Loop : Prop`, wherever the family is present. -/
noncomputable def loopConstTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h : E.members 60 = some pinLoopFamT) :
    HasTyT E n Γ (.const 60 []) (.sort .zero) :=
  .const Γ 60 [] pinLoopFamT h rfl rfl

/-- One link of an admission chain as a `GroupMembersT` step, with the
leaf's facts read off by projections (so that the step reduces). -/
noncomputable def chainLink {S : ResolvedEnv} {fuel : Nat} (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
    (rest : List (Nat × CheckedMember)) (E' : ResolvedEnv) (hadm : IndGroupAdmitted E r m)
    (hsort : (sortTyAtC E m.arity fuel [] m.mtype).isSome = true)
    (hleaf : memberAcceptB S E fuel hadm ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).1 = true)
    (hrest : GroupMembersT S (extendEnv E r m) rest E') : GroupMembersT S E ((r, m) :: rest) E' :=
  let hl := (Bool.and_eq_true _ _).mp hleaf
  let h1 := (Bool.and_eq_true _ _).mp hl.1
  .cons E r m rest E' hadm.fresh (memberStructB_of h1.1).1 (memberStructB_of h1.1).2.1
    (memberStructB_of h1.1).2.2.1 (memberStructB_of h1.1).2.2.2.1 (memberStructB_of h1.1).2.2.2.2.1
    (memberStructB_of h1.1).2.2.2.2.2 hadm (memberContentB_of hadm hl.2).1
    ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).1 ((sortTyAtC E m.arity fuel [] m.mtype).get hsort).2
    (memberScopeB_of h1.2) (memberContentB_of hadm hl.2).2 hrest

/-- The `Loop` block's members, from the admission chain of `pinLoopGroupChain`. -/
noncomputable def loopMembersT : GroupMembersT pinLoopFamEnvT falseEnvU
    [(60, pinLoopFamT), (61, pinLoopMkT), (62, pinLoopRecT)] pinLoopEnvT :=
  chainLink (fuel := 96) falseEnvU 60 pinLoopFamT _ _ pinLoopFamAdm pinLoopSortB0 pinLoopAccB0
    (chainLink (fuel := 96) pinLoopFamEnvT 61 pinLoopMkT _ _ pinLoopMkAdm pinLoopSortB1 pinLoopAccB1
      (chainLink (fuel := 96) pinLoopPrefixT 62 pinLoopRecT _ _ pinLoopRecAdm pinLoopSortB2 pinLoopAccB2
        (.nil _)))

/-- The admitted `Loop` block's derivation, as its `.group` clause: the
admissions and leaves of `pinLoopGroupRecWfT`, with the group's class facts
read off `groupClassB_of`. -/
noncomputable def loopWfT : EnvWfT pinLoopEnvT :=
  .group falseEnvU 60 pinLoopFamT [(61, pinLoopMkT)] 62 pinLoopRecT pinLoopEnvT falseEnvUWfT
    (groupClassB_of pinLoopClassB).1 (groupClassB_of pinLoopClassB).2.1 (groupClassB_of pinLoopClassB).2.2
    loopMembersT

/-- The recursive proof field's typing, at level `0`. -/
theorem loop_fields_typed (K : Nat → Nat) (vs : List Nat) (Ps Fs : List (Expr Nat))
    (hP : Ps = []) (hF : Fs = [.const 60 []]) (k : Fin Fs.length) :
    ∃ l : Level, UniformProp l ∧ ∃ d : HasTyT (extendEnv falseEnvU 60 pinLoopFamT) 0
      (policyPrefixContext (Ps ++ Fs) (Ps.length + k.val)) (Fs[k]) (.sort l), LOKt (σOf vs) 4 K d := by
  subst hP; subst hF
  match k with
  | ⟨0, _⟩ => exact ⟨.zero, fun _ => rfl, loopConstTyT rfl, fun l hl => absurd hl (List.not_mem_nil _)⟩

/-- **The `Loop` block is in the class**, at every instance bound: a `Prop`
family with large elimination whose constructor's field is a recursive proof. -/
theorem loopWfT_classG : ClassG loopWfT ∧ ∀ K, BoundG K loopWfT := by
  refine ⟨⟨falseEnvU_classG.1, fun node => ⟨fun i => ?_, fun _ _ i k _ => ?_⟩, fun node => ?_⟩,
    fun K => ⟨falseEnvUWfT_boundG K, fun node i vs _ _ => ?_, ?_, fun node _ _ i vs _ k => ?_⟩⟩
  · rw [(loop_view node i).2.2, (loop_family node).1]
    refine ⟨Or.inr ⟨[], ?_, by rw [(loop_family node).2.1], fun e he => absurd he (List.not_mem_nil _)⟩, trivial⟩
    show Expr.const 60 [] = foldApps (.const 60 ((List.range node.a.family.member.arity).map Level.param)) ([] ++ [])
    rw [loop_fam node]
    rfl
  · rw [(loop_view node i).2.1]
    rfl
  · rw [(loop_family node).1]
    exact ⟨trivial, rfl, rfl, trivial⟩
  · rw [(loop_ctor node i).1]
    exact ⟨_, .pi [] _ _ _ _ (loopConstTyT rfl) (loopConstTyT rfl),
      Nat.zero_le _, Nat.zero_le _,
      fun l hl => absurd hl (List.not_mem_nil _), fun l hl => absurd hl (List.not_mem_nil _)⟩
  · refine ⟨trivial, fun vs _ _ k => ?_, trivial, trivial⟩
    obtain ⟨k, hk⟩ := k
    match k, hk with
    | 0, _ => exact ⟨loopConstTyT rfl, fun l hl => absurd hl (List.not_mem_nil _)⟩
  · rw [show node.a.family.member.arity = 0 by rw [loop_fam node]; rfl]
    exact loop_fields_typed K vs _ _ (loop_family node).1 (loop_view node i).2.2 k

/-- The induction applied to the `Loop` block: its table is a sound model of it. -/
theorem loopWfT_envSound (P : Premises4) (K : Nat → Nat) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P (envμR P (envCtx loopWfT) loopWfT)) σ K pinLoopEnvT n :=
  envSound_envμR_classG P K loopWfT loopWfT_classG.1 (loopWfT_classG.2 K) σ n


/-- The second original bound also holds at every K, without reordering K. -/
theorem boundDG (K : Nat → Nat) : BoundDG K loopWfT := by
  refine ⟨falseEnvUWfT_boundDG K, fun node i vs _ _ k => ?_⟩
  rw [show node.a.family.member.arity = 0 by rw [loop_fam node]; rfl]
  obtain ⟨l, _, d, hd⟩ := loop_fields_typed K vs _ _
    (loop_view node i).1 (loop_view node i).2.2 k
  exact ⟨l, d, hd⟩

theorem boundG (K : Nat → Nat) : BoundG K loopWfT :=
  loopWfT_classG.2 K

theorem false_present : pinLoopEnvT.members 0 = some falseFamMember := rfl
theorem falseRec_present : pinLoopEnvT.members 1 = some falseRecMemberU := rfl

theorem axiom_free : AxiomFreeEnv' pinLoopEnvT := by
  intro r m hm
  rw [pinLoopEnvT_mem] at hm
  by_cases h62 : r = 62
  · rw [if_pos h62] at hm
    cases hm
    exact fun h => MemberClass.noConfusion h
  · rw [if_neg h62] at hm
    by_cases h61 : r = 61
    · rw [if_pos h61] at hm
      cases hm
      exact fun h => MemberClass.noConfusion h
    · rw [if_neg h61] at hm
      by_cases h60 : r = 60
      · rw [if_pos h60] at hm
        cases hm
        exact fun h => MemberClass.noConfusion h
      · rw [if_neg h60] at hm
        exact falseEnvU_axiomFree r m hm

kernel_rfl_theorem false_w_check : Rcic.F3.StepWApex.envCheck falseEnvUWfT = true

theorem w_checked : EnvWChecked loopWfT := by
  refine ⟨(Rcic.F3.StepWApex.envCheck_pass_iff falseEnvUWfT).mp false_w_check, ?_⟩
  intro node _ hType _
  have h := hType (fun _ => 0)
  rw [(loop_family node).2.2] at h
  exact False.elim (Nat.lt_irrefl 0 h)

theorem w_check : Rcic.F3.StepWApex.envCheck loopWfT = true :=
  (Rcic.F3.StepWApex.envCheck_pass_iff loopWfT).mpr w_checked

/-- Every possible recursor node has the original anySort policy. -/
theorem policy_any (node : LoopNode) : node.a.policy = .anySort := by
  cases hp : node.a.policy with
  | anySort => rfl
  | propOnly =>
      have ha := node.a.recursorArity
      rw [loop_fam node, hp] at ha
      change 1 = 0 at ha
      exact False.elim (Nat.noConfusion ha)

/-- The exact selected-node side condition is false, independently of K. -/
theorem side_false (K : Nat → Nat) (node : LoopNode) :
    ¬ StepDGSide K node := by
  intro hs
  have hlen : node.a.constructors.length = 1 :=
    node_ctors_length (ctors := [(61, pinLoopMkT)]) node rfl
  let i : Fin node.a.constructors.length := ⟨0, by rw [hlen]; decide⟩
  have hp : UniformProp node.a.family.resultLevel := by
    intro σ
    rw [(loop_family node).2.2]
    rfl
  have hfield : (.const 60 [] : Expr Nat) ∈ (node.a.constructorViews i).fields := by
    rw [(loop_view node i).2.2]
    exact List.mem_singleton.mpr rfl
  have hbad := (hs.2.1 hp (policy_any node) i).1 (.const 60 []) hfield
  rw [node.fam] at hbad
  change true = false at hbad
  exact Bool.noConfusion hbad

/-- This is whole-environment refusal, not a synthetic isolated Boolean. -/
theorem d_check_false (K : Nat → Nat) :
    Rcic.F3.StepWDApex.envCheck K loopWfT = false := by
  apply Bool.of_not_eq_true
  intro hp
  have hs := ((Rcic.F3.StepWDApex.envCheck_pass_iff K loopWfT).mp hp).2
  exact side_false K _ hs

/-- Rebounding cannot pay this checker: its structural corner fails for every K'. -/
theorem no_rebound_pass (K : Nat → Nat) :
    ¬ ∃ K' : Nat → Nat, (∀ r, K r ≤ K' r) ∧
      Rcic.F3.StepWDApex.envCheck K' loopWfT = true := by
  rintro ⟨K', _, h⟩
  rw [d_check_false K'] at h
  exact Bool.noConfusion h

/-- All original environment antecedents hold simultaneously in one environment. -/
noncomputable def OriginalDomainWitness : Prop :=
  ∃ (E : ResolvedEnv) (h : EnvWfT E),
    (∀ K, BoundG K h ∧ BoundDG K h) ∧ AxiomFreeEnv' E ∧
    E.members 0 = some falseFamMember ∧ E.members 1 = some falseRecMemberU ∧
    Rcic.F3.StepWApex.envCheck h = true ∧
    ∀ K, Rcic.F3.StepWDApex.envCheck K h = false

theorem original_domain_witness : OriginalDomainWitness :=
  ⟨pinLoopEnvT, loopWfT, (fun K => ⟨boundG K, boundDG K⟩),
    axiom_free, false_present, falseRec_present, w_check, d_check_false⟩

/-- Literal negation of DCompleteOnTier's quantified body; no P is assumed. -/
theorem dCompleteOnTier_false :
    ¬ (∀ (K : Nat → Nat) (E : ResolvedEnv) (h : EnvWfT E),
      BoundG K h → BoundDG K h → AxiomFreeEnv' E →
      E.members 0 = some falseFamMember →
      E.members 1 = some falseRecMemberU →
      Rcic.F3.StepWDApex.envCheck K h = true) := by
  intro h
  have hp := h (fun _ => 0) pinLoopEnvT loopWfT (boundG _) (boundDG _)
    axiom_free false_present falseRec_present
  rw [d_check_false] at hp
  exact Bool.noConfusion hp

/-- The original tier's conclusion is already true at this refusal witness,
using the existing ClassG model. This is a coverage refutation only. -/
theorem original_conclusion (P : Premises4) (K : Nat → Nat)
    (n : Nat) (e : Expr Nat)
    (D : HasTyT pinLoopEnvT n [] e (.const 0 []))
    (hD : LevelsBelow 4 K D) : False :=
  consistent4_G P K loopWfT loopWfT_classG.1 (boundG K)
    falseRec_present n e D hD

end
end Rcic.Declarative.FalseLoopCoverage

#print axioms Rcic.Declarative.FalseLoopCoverage.loopWfT
#print axioms Rcic.Declarative.FalseLoopCoverage.boundG
#print axioms Rcic.Declarative.FalseLoopCoverage.boundDG
#print axioms Rcic.Declarative.FalseLoopCoverage.w_check
#print axioms Rcic.Declarative.FalseLoopCoverage.d_check_false
#print axioms Rcic.Declarative.FalseLoopCoverage.original_domain_witness
#print axioms Rcic.Declarative.FalseLoopCoverage.dCompleteOnTier_false
#print axioms Rcic.Declarative.FalseLoopCoverage.no_rebound_pass
#print axioms Rcic.Declarative.FalseLoopCoverage.original_conclusion
