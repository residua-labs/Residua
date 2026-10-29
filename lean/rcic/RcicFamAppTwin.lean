import rcic.RcicFamAppTwinGeneric

/-!
# fable-famapp — a CONSISTENT scoped twin of the class-B fixture, and the family row's shadow in it

`RcicClassCAxSpine`'s twin `gEnv` keeps `RI₀` constructor-less, makes `mk₀` an AXIOM and keeps the
empty family's AnySort eliminator `rec₀ : Π M X h, M X h`. It passes the scope test, but it is
inconsistent (`rec₀ (λ _ _. Π P : Sort 0, P) X (mk₀ X)` inhabits every proposition), so it has no
model, and nothing semantic can be read off the shadows it gives.

`cEnv` is a twin with the SAME translation `tr` and a model-shaped environment: `RI₀` at `0` with
TWO constructors `mk₁` at `1` and `mk₂` at `2`, both `Π X : Sort 0, RI₀ X` (`riCtor`), and the
recursor `rec₂` at `3` eliminating into `Prop` only. 05 §10 selects `.propOnly` for two constructors
(`EliminationSelection.multipleProp`), so the group is `Or`-shaped: a `Prop` family with
family-free, non-recursive constructors eliminating into `Prop`, no axiom, no definition — the
shape routec's F3 model admits (`ClassG`). The scope test passes (`cEnvWfT_scopeCheck`): the O1
profile asks `.propOnly` of a `Prop` family with constructors that is not a unit or struct group,
and `rec₂` is `.propOnly`. So the three rows of `cEnv` are landed (`cRows`), and `tr` lands
`riEnv`'s derivations in it (`cTwin : TwinTarget cEnv`, `mk ↦ mk₂`).

Consequence (`riIdxShadow_cEnv`): `RI x ≡ RI a : Sort w` in `riEnv` gives `tr x ≡ tr a : Sort 0` in
`cEnv`. Read through a model of `cEnv` this is `⟦tr x⟧ ≈ ⟦tr a⟧` — the semantic index agreement
that class B's ι soundness needs (`RcicF3EqBoundary`: the one step that needs the syntax), obtained
WITHOUT a conversion `x ≡ a` in `riEnv` and without `FamAppConvInj` there. What is not here: the
way back to `riEnv` (the lift-back wall, `RcicFamAppTwinGeneric`), and the model of `cEnv`
(routec's `F3Cc`, another branch). closure_claim = 0.
-/

namespace Rcic.Syn.FamApp

set_option maxRecDepth 8192

open Rcic.Declarative
open Rcic.Syn
open Rcic.Syn.ClassC

/-! ## §1 members -/

/-- family, `mk₁`, `mk₂` (`riCtorEnv` is family + `mk₁`). -/
def cPrefix : ResolvedEnv := extendEnv riCtorEnv 2 riCtor

theorem cPrefix_members (r : Nat) :
    cPrefix.members r =
      if r = 2 then some riCtor else if r = 1 then some riCtor
      else if r = 0 then some riFam else none := rfl

/-- the motive, `Π (X : Sort 0), RI₀ X → Sort 0`. -/
def cMotTy : Expr Nat := .pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort .zero))
/-- the first minor under `[M]`: `Π (X : Sort 0), M X (mk₁ X)`. -/
def cMin1 : Expr Nat :=
  .pi (.sort .zero) (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 1 []) (.bvar 0)))
/-- the second minor under `[m₁, M]`: `Π (X : Sort 0), M X (mk₂ X)`. -/
def cMin2 : Expr Nat :=
  .pi (.sort .zero) (.app (.app (.bvar 2) (.bvar 0)) (.app (.const 2 []) (.bvar 0)))
def cMinors : List (Expr Nat) := [cMin1, cMin2]

/-- `rec₂ : Π (M : Π X, RI₀ X → Sort 0) (m₁ : Π X, M X (mk₁ X)) (m₂ : Π X, M X (mk₂ X)) (X : Sort 0)
    (h : RI₀ X), M X h`, the policy's recursor type at `.propOnly`. -/
def cRecTy : Expr Nat :=
  .pi cMotTy (.pi cMin1 (.pi cMin2 (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0))
    (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))))))

def cRec : CheckedMember := ⟨.recursorM, 0, cRecTy, none⟩

def cEnv : ResolvedEnv := extendEnv cPrefix 3 cRec

theorem cEnv_members (r : Nat) :
    cEnv.members r =
      if r = 3 then some cRec else if r = 2 then some riCtor else if r = 1 then some riCtor
      else if r = 0 then some riFam else none := rfl

/-! ## §2 admissions -/

theorem cMkB_before : CtorBeforeRecursors riCtorEnv riCtor := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [riCtorEnv_members] at hm
  split at hm
  · cases hm; cases hk
  · split at hm
    · cases hm; cases hk
    · cases hm

theorem cMkB_contig : CtorContiguous riCtorEnv 2 riCtor := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 1 := by omega
    subst hc
    exact ⟨riCtor, rfl, rfl, rfl⟩
  · rintro c ⟨cm, hm, hk, hf⟩
    rw [riCtorEnv_members] at hm
    split at hm
    · rename_i hc
      subst hc
      exact ⟨by decide, by decide⟩
    · split at hm
      · cases hm; cases hk
      · cases hm

def cMkB_admitted : IndGroupAdmitted riCtorEnv 2 riCtor :=
  .constructor (riFamView riCtorEnv rfl) (riCtorView riCtorEnv rfl) rfl cMkB_before cMkB_contig
    (riCtor_universe _ rfl) (riCtor_fields _ rfl rfl)

theorem cCensus : CtorCensus cPrefix 0 3 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, hf⟩
    rw [cPrefix_members] at hc
    by_cases h2 : c = 2
    · subst h2
      exact ⟨by decide, by decide⟩
    · by_cases h1 : c = 1
      · subst h1
        exact ⟨by decide, by decide⟩
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hc
          cases hc
          cases hk
        · rw [if_neg h2, if_neg h1, if_neg h0] at hc
          cases hc
  · intro h
    have hc : c = 1 ∨ c = 2 := by omega
    rcases hc with rfl | rfl
    · exact ⟨riCtor, rfl, rfl, rfl⟩
    · exact ⟨riCtor, rfl, rfl, rfl⟩

/-- 05 §10 at two constructors: `.propOnly` by `multipleProp`. -/
def cGroupAdm : RecursorEliminationAdmitted cPrefix 3 cRec where
  family := riFamView cPrefix rfl
  constructors := [riCtor, riCtor]
  constructorViews
    | ⟨0, _⟩ => riCtorView cPrefix rfl
    | ⟨1, _⟩ => riCtorView cPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := cMinors
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem cPolicy_propOnly : cGroupAdm.policy = .propOnly := rfl

theorem cMinorMatch : MinorPremisesMatch cGroupAdm
  | ⟨0, _⟩ => ⟨[.nonrecursive], 8, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[.nonrecursive], 8, rfl, rfl⟩

/-- the ι context, innermost first: `[n : Sort 0 (the field), X : Sort 0 (the index), m₂, m₁, M]`. -/
def cIotaCtx : LCtx :=
  [.assumption (.sort .zero), .assumption (.sort .zero), .assumption cMin2, .assumption cMin1,
    .assumption cMotTy]

/-- `rec₂ M m₁ m₂ n (mk₁ n) ⇝ m₁ n`, in the equation context. -/
def cIota1 : IotaEquationTyped cGroupAdm ⟨0, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  have hm : HasTy cEnv 0 cIotaCtx (.bvar 3) (lift 0 4 cMin1) := .bvar cIotaCtx 3 _ rfl
  have hq : HasTy cEnv 0 cIotaCtx (.bvar 0) (.sort .zero) := .bvar cIotaCtx 0 _ rfl
  exact .app _ _ _ _ _ hm hq

/-- `rec₂ M m₁ m₂ n (mk₂ n) ⇝ m₂ n`, in the equation context. -/
def cIota2 : IotaEquationTyped cGroupAdm ⟨1, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx, iotaLhsType,
    iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields]
  have hm : HasTy cEnv 0 cIotaCtx (.bvar 2) (lift 0 3 cMin2) := .bvar cIotaCtx 2 _ rfl
  have hq : HasTy cEnv 0 cIotaCtx (.bvar 0) (.sort .zero) := .bvar cIotaCtx 0 _ rfl
  exact .app _ _ _ _ _ hm hq

def cIotaClause : IotaDescriptorClause cPrefix cGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => cIota1
    | ⟨1, _⟩ => cIota2

def cRec_admitted : IndGroupAdmitted cPrefix 3 cRec :=
  .recursor cGroupAdm rfl cCensus
    (fun | ⟨0, _⟩ => riCtor_universe _ rfl | ⟨1, _⟩ => riCtor_universe _ rfl)
    (fun | ⟨0, _⟩ => riCtor_fields _ rfl rfl | ⟨1, _⟩ => riCtor_fields _ rfl rfl)
    cMinorMatch cIotaClause

/-! ## §3 typed content and `EnvWfT` -/

/-- `mk`'s stored type typed wherever the family is present. -/
def riCtorTyTAt (E : ResolvedEnv) (h0 : E.members 0 = some riFam) :
    HasTyT E 0 [] riCtor.mtype (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ _ _ _ _ (.sort _ _)
    (.app _ _ _ _ _ (.const _ 0 [] riFam h0 rfl rfl) (.bvar _ 0 _ rfl))

theorem riFamTypedAt (E : ResolvedEnv) (h0 : E.members 0 = some riFam) :
    FamilyTypedT (riFamView E h0) := by
  intro i
  have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
  subst i
  exact ⟨.sort _ _⟩

theorem cMkB_typed : IndGroupTypedT cMkB_admitted := ⟨riFamTypedAt _ rfl, riCtorTyped _ rfl⟩

/-- the recursor's stored type, typed by the checker in DerivationScope. -/
def cRecTyT : Σ u, HasTyT cPrefix 0 [] cRecTy (.sort u) :=
  (Rcic.Scm.SrcG.sortTyAtC cPrefix 0 96 [] cRecTy).get (by rfl)

theorem cRecTyped : IndGroupTypedT cRec_admitted :=
  ⟨riFamTypedAt _ rfl,
    (fun | ⟨0, _⟩ => riCtorTyped _ rfl | ⟨1, _⟩ => riCtorTyped _ rfl),
    (fun
      | ⟨0, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 12 Γ e T) rfl
      | ⟨1, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 12 Γ e T) rfl)⟩

def cMembers :
    GroupMembersT riFamEnv emptyEnv [(0, riFam), (1, riCtor), (2, riCtor), (3, cRec)] cEnv :=
  .cons _ 0 riFam _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    riFam_admitted PUnit.unit _ riFamTyT (fun h => nomatch h) riFamGroupTyped
    (.cons _ 1 riCtor _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
      riCtor_admitted PUnit.unit _ riCtorTyT (fun _ => ⟨riCtorTyT⟩) riCtorGroupTyped
      (.cons _ 2 riCtor _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
        cMkB_admitted PUnit.unit _ (riCtorTyTAt riCtorEnv rfl) (fun _ => ⟨riCtorTyT⟩) cMkB_typed
        (.cons _ 3 cRec _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
          cRec_admitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ cRecTyT.2
          (fun h => nomatch h) cRecTyped (.nil _))))

/-- **the consistent twin is admitted by R-CIC's environment judgment.** -/
def cEnvWfT : EnvWfT cEnv :=
  .group emptyEnv 0 riFam [(1, riCtor), (2, riCtor)] 3 cRec cEnv .empty rfl
    (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> rfl) rfl cMembers

/-! ## §4 the scope test passes: the twin's rows are landed -/

theorem cEnvWfT_scopeCheck : cEnvWfT.ScopeCheck :=
  ⟨trivial, synChecker,
    (groupSkel? synChecker emptyEnv 8 0 riFam [(1, riCtor), (2, riCtor)] cRec 0).get rfl, rfl,
    by decide⟩

theorem cRows (n : Nat) : TypedRowsWf cEnv n :=
  typedRowsWf_of_scopeCheck cEnvWfT cEnvWfT_scopeCheck n

/-- `cEnv` is a target of `tr`: `mk ↦ mk₂`, the constructor at `2`. -/
def cTwin : TwinTarget cEnv where
  meta := .ofEnvWfT cEnvWfT cRows
  rows := cRows
  h0 := rfl
  m₂ := riCtor
  h2 := rfl
  h2t := rfl
  h2a := rfl

/-! ## §5 the three shadows of `riEnv` in the consistent twin -/

theorem riSortRow_cEnv {n : Nat} {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {u v : Level}
    (h : TyConvT riEnv n Γ (.sort u) (.sort v)) : eqN u v :=
  cTwin.sortShadow hΓ h

theorem riPiShadow_cEnv {n : Nat} {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {A B A' B' : Expr Nat}
    (h : TyConvT riEnv n Γ (.pi A B) (.pi A' B')) :
    Nonempty (TyConvT cEnv n (trCtx Γ) (tr A) (tr A')) ∧
      Nonempty (TyConvT cEnv n (.assumption (tr A) :: trCtx Γ) (tr B) (tr B')) :=
  cTwin.piShadow hΓ h

/-- **the family row's shadow in the consistent twin**: `RI x ≡ RI a : Sort w` in `riEnv` gives
    `tr x ≡ tr a : Sort 0` in `cEnv`. -/
theorem riIdxShadow_cEnv {n : Nat} {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {x a : Expr Nat} {w : Level}
    (h : ConvT riEnv n Γ (.app (.const 0 []) x) (.app (.const 0 []) a) (.sort w)) :
    Nonempty (ConvT cEnv n (trCtx Γ) (tr x) (tr a) (.sort .zero)) :=
  cTwin.riIdxShadow hΓ h

theorem riFamAppShadow_cEnv {n : Nat} {Γ : LCtx} (hΓ : CtxWfT riEnv n Γ) {ls ls' : List Level}
    {xs xs' : List (Expr Nat)} {w : Level}
    (h : ConvT riEnv n Γ (foldApps (.const 0 ls) xs) (foldApps (.const 0 ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT cEnv n (trCtx Γ) (instantiateLevels ls riFam.mtype) (xs.map tr) (xs'.map tr) :=
  cTwin.famAppShadowConv hΓ h

end Rcic.Syn.FamApp

#print axioms Rcic.Syn.FamApp.cEnvWfT
#print axioms Rcic.Syn.FamApp.cEnvWfT_scopeCheck
#print axioms Rcic.Syn.FamApp.cRows
#print axioms Rcic.Syn.FamApp.riIdxShadow_cEnv
#print axioms Rcic.Syn.FamApp.riFamAppShadow_cEnv
