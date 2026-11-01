import rcic.RcicF3AccFixture
import rcic.RcicTypedEnv
import rcic.RcicTypedIdxAdmitted

/-!
# F3 AGPropAny: the Acc fixture as a TYPED environment (`EnvWfT accEnv`)

Session-25 strengthener (PR #8275 follow-up): the fixture becomes a live typed
environment — `EnvWfT.group` over the three-member Acc group, the W fixture's
`wEnvWfT` twin (RcicTypedFunRecPins:573) at a `Prop` family WITH A PARAMETER and a
function-recursive field (both are firsts: W's family is a parameter-free `Type`
family).  The `EnvWfT` supply makes the fixture usable as a typed root for future
pins at the AGPropAny corner (`InScope`-style queries, typed walks, ι reads).

Delivered (all anchors ⊆ {propext, Quot.sound}, five zero-axiom):
* the ι descriptor clause `accIotaClause` — equation domains
  `[Prop, motTy, minorTy, lift 0 2 accField]` (the PARAMETER is an equation binder:
  W's parameter-free shape did not show this), the schema `ms f (fun x : P =>
  AccRrec P mot ms (f x))` with the IH wrapper's λ domain the PARAMETER TERM
  (`P`, a local — not a sort), and the equation type `mot (intro P f)`;
* the recursor/index obligation `accRecIdx` via `IdxAdmittedT.ofCheck` — the
  decidable closure check discharges at the frec corner (`with_unfolding_all rfl`),
  the W-line pattern (the canonical `IotaWitnessS` is constructed, not refuted);
* the typed rows: `accFamTyT` / `accIntroTyT` (hand derivations) and `accRecTyT`
  (conversion checker at the four-binder telescope);
* the three-member `GroupMembersT` chain and the `EnvWfT.group` step: `accEnvWfT`,
  `pin_accEnvWfT`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.AccEnv

open Rcic.Declarative
open Rcic.F3

/-! ## (1) member freshness on the way up -/

theorem accFamOnly_members (c : Nat) :
    accFamOnly.members c = if c = 0 then some accFamMember else none := rfl

theorem accPrefix_members (c : Nat) :
    accPrefix.members c =
      if c = 1 then some accIntroMember else if c = 0 then some accFamMember else none := rfl

/-! ## (2) the ι descriptor clause at the Acc group -/

/-- the equation's context: `f`, the minor, the motive, `P` (the parameter last —
`assumptionCtx` reverses the outer-first domain list). -/
def accIotaCtx : LCtx :=
  [.assumption (lift 0 2 accField), .assumption accMinorTy, .assumption accMotTy,
    .assumption (.sort .zero)]

/-- the λ-wrapped recursive call 05 §14 writes for the function-recursive field:
    `fun (x : P) => AccRrec P mot ms (f x)` — the IH's Π domain is the PARAMETER TERM
    (`P`, a local), not a sort. -/
def accCall : Expr Nat :=
  .lam (.bvar 3) (.app (.app (.app (.app (.const 2 [.param 0]) (.bvar 4)) (.bvar 3)) (.bvar 2))
    (.app (.bvar 1) (.bvar 0)))

/-- the schema admission derives: `ms f (fun x => AccRrec P mot ms (f x))`. -/
def accSchema : Expr Nat := .app (.app (.bvar 1) (.bvar 0)) accCall

/-- the equation's type: `mot (intro P f)`. -/
def accEqTy : Expr Nat := .app (.bvar 2) (.app (.app (.const 1 []) (.bvar 3)) (.bvar 0))

theorem accEquation_doms :
    equationDoms accGroupAdmitted ⟨0, by decide⟩ =
      some [.sort .zero, accMotTy, accMinorTy, lift 0 2 accField] := rfl

theorem accSchema_derived :
    iotaSchemaAt accGroupAdmitted ⟨0, by decide⟩ 8 [.recursive 1] = some accSchema := rfl

theorem accEquation_shape :
    iotaEquationType accGroupAdmitted ⟨0, by decide⟩ = accEqTy := rfl

/-- the equation in the untyped judgment, as admission's clause asks — the Acc twin of
    `wIotaTyLegacy`: every piece is DIRECT (`f x : AccR P` off the field's own telescope,
    the λ wrapper at the minor's IH domain, no conversion anywhere). -/
def accIotaTyLegacy : HasTy accEnv 1 accIotaCtx accSchema accEqTy := by
  have hMot : HasTy accEnv 1 accIotaCtx (.bvar 2) (lift 0 3 accMotTy) := HasTy.bvar _ 2 _ rfl
  have hMs : HasTy accEnv 1 accIotaCtx (.bvar 1) (lift 0 2 accMinorTy) := HasTy.bvar _ 1 _ rfl
  have hF : HasTy accEnv 1 accIotaCtx (.bvar 0) (lift 0 1 (lift 0 2 accField)) :=
    HasTy.bvar _ 0 _ rfl
  have hP : HasTy accEnv 1 accIotaCtx (.bvar 3) (.sort .zero) := HasTy.bvar _ 3 _ rfl
  -- the recursor's head, in the untyped judgment
  have hRecHead : HasTy accEnv 1 accIotaCtx (.const 2 [.param 0]) accRecTy := by
    refine HasTy.const _ 2 [.param 0] accRecMember rfl rfl ?_
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩
  -- the same rows one binder in (under `x : P`)
  have hP' : HasTy accEnv 1 (.assumption (.bvar 3) :: accIotaCtx) (.bvar 4) (.sort .zero) :=
    HasTy.bvar _ 4 _ rfl
  have hMot' : HasTy accEnv 1 (.assumption (.bvar 3) :: accIotaCtx) (.bvar 3)
      (lift 0 4 accMotTy) := HasTy.bvar _ 3 _ rfl
  have hMs' : HasTy accEnv 1 (.assumption (.bvar 3) :: accIotaCtx) (.bvar 2)
      (lift 0 3 accMinorTy) := HasTy.bvar _ 2 _ rfl
  have hF' : HasTy accEnv 1 (.assumption (.bvar 3) :: accIotaCtx) (.bvar 1)
      (lift 0 2 (lift 0 2 accField)) := HasTy.bvar _ 1 _ rfl
  have hX : HasTy accEnv 1 (.assumption (.bvar 3) :: accIotaCtx) (.bvar 0) (.bvar 4) :=
    HasTy.bvar _ 0 _ rfl
  have hRecHead' : HasTy accEnv 1 (.assumption (.bvar 3) :: accIotaCtx)
      (.const 2 [.param 0]) accRecTy := by
    refine HasTy.const _ 2 [.param 0] accRecMember rfl rfl ?_
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩
  exact HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ hMs hF)
    (HasTy.lam _ (.bvar 3) .zero _ _
      hP
      (HasTy.app _ _ _ _ _
        (HasTy.app _ _ _ _ _
          (HasTy.app _ _ _ _ _
            (HasTy.app _ _ _ _ _ hRecHead' hP')
            hMot')
          hMs')
        (HasTy.app _ _ _ _ _ hF' hX)))

def accIotaClause : IotaDescriptorClause accPrefix accGroupAdmitted where
  signatureOnly := rfl
  shapesAt := fun _ => [.recursive 1]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => by
      unfold IotaEquationTyped
      rw [accEquation_doms, accSchema_derived]
      exact accIotaTyLegacy

/-! ## (3) the group's `.recursor` admission -/

/-- the constructor census: `intro` (at 1) is the family's ONLY constructor, and the
    family sits at 0 with the recursor at 2. -/
theorem accCensus : CtorCensus accPrefix 0 2 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, hfam⟩
    rw [accPrefix_members] at hc
    by_cases h1 : c = 1
    · rw [if_pos h1] at hc
      cases hc
      exact ⟨by omega, by omega⟩
    · by_cases h0 : c = 0
      · rw [if_neg h1, if_pos h0] at hc
        cases hc
        exact absurd hk (by decide)
      · rw [if_neg h1, if_neg h0] at hc
        cases hc
  · intro h
    have hc : c = 1 := by omega
    subst hc
    exact ⟨accIntroMember, by rw [accPrefix_members]; rfl, rfl, rfl⟩

/-- the universe row at the single constructor: the field is a proof (`imax 0 0`). -/
def accUniverseRow (i : Fin accGroupAdmitted.constructors.length) :
    FieldUniverseAdmitted (accGroupAdmitted.constructorViews i) :=
  match i with
  | ⟨0, _⟩ => fun _ => Or.inl accImaxZero_prop

/-- the fields-permitted row at the single constructor. -/
def accFieldsRow (i : Fin accGroupAdmitted.constructors.length) :
    CtorFieldsPermitted (accGroupAdmitted.constructorViews i) :=
  match i with
  | ⟨0, _⟩ => accIntroFields accPrefix rfl accField_analyze

def accGroupRecursor : IndGroupAdmitted accPrefix 2 accRecMember :=
  .recursor accGroupAdmitted rfl accCensus
    (fun i => accUniverseRow i)
    (fun i => accFieldsRow i)
    accMinorMatch accIotaClause

/-! ## (4) the typed obligations -/

/-- the recursor/index obligation, via the decidable closure-and-canonical-witness check —
    the canonical `IotaWitnessS` for the function-recursive field is CONSTRUCTED by `ofCheck`
    (the W-line pattern; the check evaluates green at the frec corner, `with_unfolding_all`). -/
def accRecIdx : RecursorGroupIdxAdmittedT accGroupAdmitted accIotaClause :=
  .ofCheck accGroupAdmitted accIotaClause (by with_unfolding_all rfl)

/-- `AccR`'s stored type: `Prop → Prop` at `Sort (imax 1 1)` in the typed judgment. -/
def accFamTyT : HasTyT emptyEnv 0 [] accFamMember.mtype
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (HasTyT.sort [] .zero) (HasTyT.sort [.assumption (.sort .zero)] .zero)

/-- the field's own row, under the parameter binder: `P → AccR P` at `Sort (imax 0 0)`. -/
def accFieldTyT (E : ResolvedEnv) (h : E.members 0 = some accFamMember) :
    HasTyT E 0 [.assumption (.sort .zero)] accField (.sort (.imax .zero .zero)) :=
  .pi [.assumption (.sort .zero)] (.bvar 0) .zero (accApp (.bvar 1)) .zero
    (HasTyT.bvar _ 0 _ rfl)
    (HasTyT.app _ (.const 0 []) (.bvar 1) (.sort .zero) (.sort .zero)
      (HasTyT.const _ 0 [] accFamMember h rfl rfl)
      (HasTyT.bvar _ 1 _ rfl))

/-- `intro`'s stored type at `Sort (imax 1 (imax (imax 0 0) 0))` in the typed judgment. -/
def accIntroTyT (E : ResolvedEnv) (h : E.members 0 = some accFamMember) :
    HasTyT E 0 [] accIntroMember.mtype
      (.sort (.imax (.succ .zero) (.imax (.imax .zero .zero) .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) (.pi accField (accApp (.bvar 1)))
    (.imax (.imax .zero .zero) .zero)
    (HasTyT.sort [] .zero)
    (.pi [.assumption (.sort .zero)] accField (.imax .zero .zero) (accApp (.bvar 1)) .zero
      (accFieldTyT E h)
      (HasTyT.app _ (.const 0 []) (.bvar 1) (.sort .zero) (.sort .zero)
        (HasTyT.const _ 0 [] accFamMember h rfl rfl)
        (HasTyT.bvar _ 1 _ rfl)))

/-- the recursor's stored type's sort. -/
def accRecSortU : Level :=
  .imax (.succ .zero)
    (.imax (.imax .zero (.succ (.param 0)))
      (.imax (.imax (.imax .zero .zero) (.imax (.imax .zero (.param 0)) (.param 0)))
        (.imax .zero (.param 0))))

/-- the recursor's stored type, via the conversion checker (the `wRecTyT` pattern: no
    conversion anywhere, but the telescope is four binders deep). -/
def accRecTyT : HasTyT accPrefix 1 [] accRecTy (.sort accRecSortU) :=
  (tyAtC accPrefix 1 8 [] accRecTy (.sort accRecSortU)).get (by
    have h : (tyAtC accPrefix 1 8 [] accRecTy (.sort accRecSortU)).isSome = true := rfl
    exact h)

/-! ## (5) the members' typed content -/

/-- the family's typed content: one parameter row, `Prop : Sort 1`. -/
theorem accFamTyped : IndGroupTypedT accFamAdmitted :=
  fun j => by
    match j with
    | ⟨0, _⟩ => exact ⟨HasTyT.sort [] .zero⟩

/-- the constructor's typed content: both telescope rows plus the parameter mirror
    (the ctor's `P` is a type conversion of the family's — here the identity, by `refl`). -/
theorem accIntroTyped : IndGroupTypedT accIntroAdmitted :=
  ⟨fun j => by
      match j with
      | ⟨0, _⟩ => exact ⟨HasTyT.sort [] .zero⟩,
    fun j => by
      match j with
      | ⟨0, _⟩ => exact ⟨HasTyT.sort [] .zero⟩
      | ⟨1, _⟩ => exact ⟨accFieldTyT accFamOnly rfl⟩,
    fun i => by
      match i with
      | ⟨0, _⟩ => exact ⟨TyConvT.refl [] (.sort .zero)⟩⟩

/-- the recursor's typed content: family and constructor rows at the admission env, and the
    ι equation typed in `HasTyT` by the conversion checker (the `wRecTyped` pattern). -/
theorem accRecTyped : IndGroupTypedT accGroupRecursor :=
  ⟨fun j => by
      match j with
      | ⟨0, _⟩ => exact ⟨HasTyT.sort [] .zero⟩,
    fun i => by
      match i with
      | ⟨0, _⟩ =>
        exact ⟨fun j => by
          match j with
          | ⟨0, _⟩ => exact ⟨HasTyT.sort [] .zero⟩
          | ⟨1, _⟩ => exact ⟨accFieldTyT accPrefix rfl⟩,
        fun i => by
          match i with
          | ⟨0, _⟩ => exact ⟨TyConvT.refl [] (.sort .zero)⟩⟩,
    fun i => by
      match i with
      | ⟨0, _⟩ =>
        exact iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 8 Γ e T) rfl⟩

/-! ## (6) the group chain and the environment judgment -/

def accMembersT :
    GroupMembersT accFamOnly emptyEnv
      [(0, accFamMember), (1, accIntroMember), (2, accRecMember)] accEnv :=
  .cons _ 0 accFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    accFamAdmitted PUnit.unit _ accFamTyT (fun h => absurd h (by decide))
    accFamTyped
    (.cons _ 1 accIntroMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      accIntroAdmitted PUnit.unit _ (accIntroTyT accFamOnly rfl) (fun _ => ⟨accIntroTyT accFamOnly rfl⟩)
      accIntroTyped
      (.cons _ 2 accRecMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        accGroupRecursor accRecIdx _ accRecTyT (fun h => absurd h (by decide))
        accRecTyped (.nil _)))

/-- the typed environment judgment admits the Acc group — the W fixture's `wEnvWfT` twin at
    a parameterized `Prop` family with a function-recursive field. -/
def accEnvWfT : EnvWfT accEnv :=
  .group emptyEnv 0 accFamMember [(1, accIntroMember)] 2 accRecMember accEnv .empty
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl accMembersT

/-- the pin: the fixture is a live typed environment. -/
theorem pin_accEnvWfT : Nonempty (EnvWfT accEnv) := ⟨accEnvWfT⟩

end Rcic.F3.AccEnv

#print axioms Rcic.F3.AccEnv.accFamOnly_members
#print axioms Rcic.F3.AccEnv.accPrefix_members
#print axioms Rcic.F3.AccEnv.accEquation_doms
#print axioms Rcic.F3.AccEnv.accSchema_derived
#print axioms Rcic.F3.AccEnv.accEquation_shape
#print axioms Rcic.F3.AccEnv.accIotaTyLegacy
#print axioms Rcic.F3.AccEnv.accIotaClause
#print axioms Rcic.F3.AccEnv.accCensus
#print axioms Rcic.F3.AccEnv.accGroupRecursor
#print axioms Rcic.F3.AccEnv.accRecIdx
#print axioms Rcic.F3.AccEnv.accFamTyT
#print axioms Rcic.F3.AccEnv.accFieldTyT
#print axioms Rcic.F3.AccEnv.accIntroTyT
#print axioms Rcic.F3.AccEnv.accRecSortU
#print axioms Rcic.F3.AccEnv.accRecTyT
#print axioms Rcic.F3.AccEnv.accFamTyped
#print axioms Rcic.F3.AccEnv.accIntroTyped
#print axioms Rcic.F3.AccEnv.accRecTyped
#print axioms Rcic.F3.AccEnv.accMembersT
#print axioms Rcic.F3.AccEnv.accEnvWfT
#print axioms Rcic.F3.AccEnv.pin_accEnvWfT
