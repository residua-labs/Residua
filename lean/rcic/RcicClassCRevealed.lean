import rcic.RcicAccPiMeasure
import rcic.RcicClassCCex

/-!
# cc-classc — a class-(c) group with a revealed DATA field: `ConvT` has its K-like cell, `tableOfK`
# misses it, a bare override closes it

The fixture `RI`, over the empty environment:

    RI  : Π (X : Sort 0), Sort 0                                          (at 0)
    mk  : Π (X : Sort 0), RI X                                            (at 1)
    rec : Π (M : Π X, RI X → Sort u) (m : Π X, M X (mk X)) (X : Sort 0) (h : RI X), M X h   (at 2)

`X : Sort 0` is DATA (its domain `Sort 0` lives in `Sort 1`), revealed as the bare result index, so
05 §10 admits the recursor `AnySort` by `singletonProp`. The family is a `Prop` with a constructor,
an index and a field, so it is neither a unit nor a struct group: it is in class (c)
(`GroupProfileT`'s O1 conjunct would force `.propOnly`). It is not Acc-shaped. Its field is plain,
so `ConvT`'s ι IS there (`riW`), unlike Acc (`accP_no_derivedIota`).

* §1–§3 `riEnvWfT : EnvWfT riEnv`, `riPolicy_anySort`.
* §4 `riConvK`: the K-like cell `rec M m X h ≡ m X : M X h` at a VARIABLE major `h : RI X` is a
  `ConvT` derivation in the rows' own judgment: `irr` (`h ≡ mk X : RI X`), `app` congruence, ι at
  the constructor, and `tyConv` for the motive's proof argument. No K rule is used
  (`derivedIota_no_bvar_major`); `irr` against a constructor proof of the SAME type does it.
* §5 the erased cell. The landed `TyP.eps` drops `h` and erases the two endpoints to `rec M m X` and
  `m X`. `iotaKGate` refuses `RI` (its field is not a family application), so `tableOfK` keeps the
  constructor-major rule, which never matches an erased major. The erased redex is normal and
  `const`-headed, the contractum `bvar`-headed, so they are NOT convertible
  (`riCell_not_convE_tableOfK`). The bare override `rec ↦ λ M m X. m X` (the field read off the
  index) is `TableWF` by G1 (`riOverride_wf`), and it closes the cell in one unfold and three β
  (`riCell_convE_override`).

So class (c) beyond the K gate is not a confluence obstruction, and the cell that separates the
override from `tableOfK` is in `ConvT` itself. `closure_claim = 0`.
-/

namespace Rcic.Syn.ClassC

set_option maxRecDepth 8192

open Rcic.Declarative
open Rcic.Syn

/-! ## §1 members and environments -/

def riFam : CheckedMember := ⟨.inductiveM, 0, .pi (.sort .zero) (.sort .zero), none⟩
def riCtor : CheckedMember :=
  ⟨.constructorM, 0, .pi (.sort .zero) (.app (.const 0 []) (.bvar 0)), none⟩
/-- the motive domain `Π (X : Sort 0), RI X → Sort u`. -/
def riMotTy : Expr Nat :=
  .pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0)) (.sort (.param 0)))
/-- the minor domain `Π (X : Sort 0), M X (mk X)`, under `[M]`. -/
def riMinTy : Expr Nat :=
  .pi (.sort .zero) (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 1 []) (.bvar 0)))
def riRecTy : Expr Nat :=
  .pi riMotTy (.pi riMinTy
    (.pi (.sort .zero) (.pi (.app (.const 0 []) (.bvar 0))
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))
def riRec : CheckedMember := ⟨.recursorM, 1, riRecTy, none⟩

def riFamEnv : ResolvedEnv := extendEnv emptyEnv 0 riFam
def riCtorEnv : ResolvedEnv := extendEnv riFamEnv 1 riCtor
def riEnv : ResolvedEnv := extendEnv riCtorEnv 2 riRec

theorem riFamEnv_members (r : Nat) :
    riFamEnv.members r = if r = 0 then some riFam else none := rfl

theorem riCtorEnv_members (r : Nat) :
    riCtorEnv.members r =
      if r = 1 then some riCtor else if r = 0 then some riFam else none := rfl

/-! ## §2 views and admissions -/

def riFamView (E : ResolvedEnv) (h : E.members 0 = some riFam) : PolicyFamilyView E where
  ref := 0
  member := riFam
  present := h
  hasClass := rfl
  parameters := []
  indices := [.sort .zero]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hj : j = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
      subst j
      exact .sort _ _ }

def riCtorView (E : ResolvedEnv) (h : E.members 0 = some riFam) :
    PolicyConstructorView E (riFamView E h) riCtor where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.sort .zero]
  resultIndices := [.bvar 0]
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hj : j = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
      subst j
      exact .sort _ _ }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := by
    intro e he
    have heq : e = .bvar 0 := by simpa using he
    subst e
    rfl

theorem riCtor_universe (E : ResolvedEnv) (h : E.members 0 = some riFam) :
    FieldUniverseAdmitted (riCtorView E h) := fun _ => .inl (fun _ => rfl)

/-- the field `X` is DATA (level `1`), safe only because it is the bare result index. -/
theorem riCtor_safe (E : ResolvedEnv) (h : E.members 0 = some riFam) :
    (riCtorView E h).AllFieldsSafe := fun j => by
  have hj : j = ⟨0, by change 0 < 1; decide⟩ :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  exact .inr (List.mem_singleton_self _)

/-- and it is NOT a proof field: its level is not uniformly `0`. -/
theorem riCtor_field_not_prop (E : ResolvedEnv) (h : E.members 0 = some riFam) :
    ¬ UniformProp ((riCtorView E h).fieldLevel ⟨0, by change 0 < 1; decide⟩) := by
  intro hp
  have h1 : evalTotal (fun _ => 0) (.succ .zero) = 0 := hp (fun _ => 0)
  exact absurd h1 (by decide)

theorem riCtor_fields (E : ResolvedEnv) (h : E.members 0 = some riFam)
    (ha : fieldAnalyze E 8 0 0 0 1 0 (.sort .zero) = .permitted .nonrecursive []) :
    CtorFieldsPermitted (riCtorView E h) := by
  intro j
  have hj : j = ⟨0, by change 0 < 1; decide⟩ :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  exact ⟨.nonrecursive, 8, [], ha⟩

theorem ri_before : CtorBeforeRecursors riFamEnv riCtor := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk hn
  rw [riFamEnv_members] at hm
  split at hm
  · cases hm; cases hk
  · cases hm

theorem ri_contiguous : CtorContiguous riFamEnv 1 riCtor := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hf : False := by omega
    exact hf.elim
  · rintro c ⟨cm, hm, hk, hf⟩
    rw [riFamEnv_members] at hm
    split at hm
    · cases hm; cases hk
    · cases hm

theorem ri_census : CtorCensus riCtorEnv 0 2 := by
  refine ⟨by decide, ?_⟩
  intro c
  constructor
  · rintro ⟨cm, hm, hk, hf⟩
    rw [riCtorEnv_members] at hm
    split at hm
    · rename_i hc
      exact ⟨by omega, by omega⟩
    · split at hm
      · cases hm; cases hk
      · cases hm
  · intro hc
    have he : c = 1 := by omega
    subst c
    exact ⟨riCtor, rfl, rfl, rfl⟩

def riFam_admitted : IndGroupAdmitted emptyEnv 0 riFam :=
  .family rfl (riFamView riFamEnv rfl) rfl rfl (.inl (fun _ => rfl))
def riCtor_admitted : IndGroupAdmitted riFamEnv 1 riCtor :=
  .constructor (riFamView riFamEnv rfl) (riCtorView riFamEnv rfl)
    rfl ri_before ri_contiguous (riCtor_universe _ rfl) (riCtor_fields _ rfl rfl)

/-- 05 §10 at `RI`: one constructor, every field safe, so `AnySort`. -/
def riPolicy : RecursorEliminationAdmitted riCtorEnv 2 riRec where
  family := riFamView riCtorEnv rfl
  constructors := [riCtor]
  constructorViews | ⟨0, _⟩ => riCtorView riCtorEnv rfl
  constructorsPresent | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [riMinTy]
  minorCount := rfl
  policy := .anySort
  selected := .singletonProp (fun _ => rfl) rfl
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact riCtor_safe _ rfl)
  recursorArity := rfl
  recursorType := rfl

def riDescriptor : IotaDescriptorClause riCtorEnv riPolicy where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive]
  fuelAt := fun _ => 8
  analyzed | ⟨0, _⟩ => rfl
  typed := fun i => by
    have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
      Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
    subst i
    let Γ : LCtx := [.assumption (.sort .zero), .assumption (.sort .zero),
      .assumption riMinTy, .assumption riMotTy]
    have hm : HasTy riEnv 1 Γ (.bvar 2) (lift 0 3 riMinTy) := .bvar Γ 2 _ rfl
    have hq : HasTy riEnv 1 Γ (.bvar 0) (.sort .zero) := .bvar Γ 0 _ rfl
    exact .app _ _ _ _ _ hm hq

theorem ri_minor_match : MinorPremisesMatch riPolicy := by
  intro i
  have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
  subst i
  exact ⟨[.nonrecursive], 8, rfl, rfl⟩

def riRec_admitted : IndGroupAdmitted riCtorEnv 2 riRec :=
  .recursor riPolicy rfl ri_census
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact riCtor_universe _ rfl)
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact riCtor_fields _ rfl rfl)
    ri_minor_match riDescriptor

/-- **class (c)**: the admitted policy is `AnySort`, at a `Prop` family that has an index (so it is
    no unit or struct group) and a DATA field. -/
theorem riPolicy_anySort : riPolicy.policy = .anySort ∧ riPolicy.family.indices ≠ [] ∧
    riPolicy.family.resultLevel = .zero := ⟨rfl, by decide, rfl⟩

/-! ## §3 typed content and `EnvWfT` -/

def riFamTyT : HasTyT emptyEnv 0 [] riFam.mtype (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ _ _ _ _ (.sort _ _) (.sort _ _)

def riCtorTyT : HasTyT riFamEnv 0 [] riCtor.mtype (.sort (.imax (.succ .zero) .zero)) :=
  .pi _ _ _ _ _ (.sort _ _)
    (.app _ _ _ _ _ (.const _ 0 [] riFam rfl rfl rfl) (.bvar _ 0 _ rfl))

def riRecSort : Level :=
  .imax (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))
    (.imax (.imax (.succ .zero) (.param 0)) (.imax (.succ .zero) (.imax .zero (.param 0))))

def riRecTyT : HasTyT riCtorEnv 1 [] riRecTy (.sort riRecSort) :=
  (tyAtC riCtorEnv 1 12 [] riRecTy (.sort riRecSort)).get (by rfl)

theorem riCtorTyped (E : ResolvedEnv) (h : E.members 0 = some riFam) :
    CtorTypedT (riCtorView E h) := by
  constructor
  · intro j
    have hj : j = ⟨0, by change 0 < 1; decide⟩ :=
      Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
    subst j
    exact ⟨.sort _ _⟩
  · intro j
    exact j.elim0

theorem riFamGroupTyped : IndGroupTypedT riFam_admitted := by
  intro i
  have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
    Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
  subst i
  exact ⟨.sort _ _⟩

theorem riCtorGroupTyped : IndGroupTypedT riCtor_admitted :=
  ⟨(by
    intro i
    have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
      Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
    subst i
    exact ⟨.sort _ _⟩),
    riCtorTyped _ rfl⟩

theorem riRecTyped : IndGroupTypedT riRec_admitted :=
  ⟨(by
    intro i
    have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
      Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
    subst i
    exact ⟨.sort _ _⟩),
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact riCtorTyped _ rfl),
    (fun i => by
      have hi : i = ⟨0, by change 0 < 1; decide⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      subst i
      exact iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 12 Γ e T) rfl)⟩

def riMembers :
    GroupMembersT riFamEnv emptyEnv [(0, riFam), (1, riCtor), (2, riRec)] riEnv :=
  .cons _ 0 riFam _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    riFam_admitted PUnit.unit _ riFamTyT (fun h => nomatch h) riFamGroupTyped
    (.cons _ 1 riCtor _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
      riCtor_admitted PUnit.unit _ riCtorTyT (fun _ => ⟨riCtorTyT⟩) riCtorGroupTyped
      (.cons _ 2 riRec _ _ rfl rfl (fun _ => rfl) (fun h => nomatch h) rfl rfl rfl
        riRec_admitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ riRecTyT
        (fun h => nomatch h) riRecTyped (.nil _)))

/-- **`RI` is admitted by R-CIC's environment judgment.** -/
def riEnvWfT : EnvWfT riEnv :=
  .group emptyEnv 0 riFam [(1, riCtor)] 2 riRec riEnv .empty rfl
    (fun c hc => by simp at hc; subst c; rfl) rfl riMembers

/-! ## §4 the K-like cell is a `ConvT` derivation at a variable major

Scope `[h : RI X, X : Sort 0, m : minor, M : motive]` (innermost first): `M m X h` are `bvar 3 2 1 0`.

    rec M m X h  ≡ (irr h ≡ mk X, app)  rec M m X (mk X)  ≡ι  m X        at M X h

The ι node is typed at `M X (mk X)`. `tyConv` moves it to `M X h` with the motive's proof argument
converted by the same `irr` leaf. -/

def riCtx : LCtx :=
  [.assumption (.app (.const 0 []) (.bvar 0)), .assumption (.sort .zero), .assumption riMinTy,
    .assumption riMotTy]

def riTy (Γ : LCtx) (e T : Expr Nat) (h : (tyAtC riEnv 1 32 Γ e T).isSome = true) :
    HasTyT riEnv 1 Γ e T :=
  (tyAtC riEnv 1 32 Γ e T).get h

def riRecHead : Expr Nat := .const 2 [.param 0]
/-- `RI X`. -/
def riP : Expr Nat := .app (.const 0 []) (.bvar 1)
/-- `mk X`. -/
def riMkX : Expr Nat := .app (.const 1 []) (.bvar 1)
/-- `rec M m X`. -/
def riRecMMX : Expr Nat := foldApps riRecHead [.bvar 3, .bvar 2, .bvar 1]
/-- the redex at the variable major, `rec M m X h`. -/
def riLhs : Expr Nat := foldApps riRecHead [.bvar 3, .bvar 2, .bvar 1, .bvar 0]
/-- the redex at the constructor major, `rec M m X (mk X)`. -/
def riMid : Expr Nat := foldApps riRecHead [.bvar 3, .bvar 2, .bvar 1, riMkX]
/-- the contractum `m X`. -/
def riRhs : Expr Nat := .app (.bvar 2) (.bvar 1)
/-- `M X h`. -/
def riTyL : Expr Nat := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
/-- `M X (mk X)`. -/
def riTyR : Expr Nat := .app (.app (.bvar 3) (.bvar 1)) riMkX
/-- `M X`. -/
def riMX : Expr Nat := .app (.bvar 3) (.bvar 1)

def riCtxWf : CtxWfT riEnv 1 riCtx :=
  .assumption _ _ _
    (.assumption _ (.sort .zero) _
      (.assumption _ riMinTy _
        (.assumption [] riMotTy _ .nil
          (riTy [] riMotTy (.sort (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))) rfl))
        (riTy _ riMinTy (.sort (.imax (.succ .zero) (.param 0))) rfl))
      (HasTyT.sort _ .zero))
    (riTy _ (.app (.const 0 []) (.bvar 0)) (.sort .zero) rfl)

def riPTy : HasTyT riEnv 1 riCtx riP (.sort .zero) := riTy _ _ _ rfl
def riHTy : HasTyT riEnv 1 riCtx (.bvar 0) riP := HasTyT.bvar _ 0 _ rfl
def riMkXTy : HasTyT riEnv 1 riCtx riMkX riP := riTy _ _ _ rfl
def riRecMMXTy : HasTyT riEnv 1 riCtx riRecMMX
    (.pi riP (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))) := riTy _ _ _ rfl
def riLhsTy : HasTyT riEnv 1 riCtx riLhs riTyL := riTy _ _ _ rfl
def riMidTy : HasTyT riEnv 1 riCtx riMid riTyR := riTy _ _ _ rfl
def riRhsTy : HasTyT riEnv 1 riCtx riRhs riTyR := riTy _ _ _ rfl
def riMXTy : HasTyT riEnv 1 riCtx riMX (.pi riP (.sort (.param 0))) := riTy _ _ _ rfl

/-- the `irr` leaf `h ≡ mk X : RI X`. -/
def riIrr : ConvT riEnv 1 riCtx (.bvar 0) riMkX riP :=
  .irr _ _ _ _ riPTy riHTy riMkXTy

/-- `ConvT`'s ι witness at `RI`: the field is plain, so `analyzeFields` accepts it. -/
def riW : IotaWitness riEnv where
  recRef := 2
  ctorRef := 1
  ls := [.param 0]
  lsC := []
  recMember := riRec
  ctorMember := riCtor
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 3, .bvar 2, .bvar 1]
  fields := [.bvar 1]
  ctorParams := []
  kinds := [.plain]
  minor := .bvar 2
  hlen := rfl
  familyRef := 0
  famMember := riFam
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort .zero]
  ctorResult := .app (.const 0 []) (.bvar 0)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [riMotTy, riMinTy, .sort .zero, .app (.const 0 []) (.bvar 0)]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := riCtor.mtype
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

theorem riW_lhs : iotaLhsOf riW = riMid := rfl
theorem riW_rhs : iotaRhsOf riW = riRhs := rfl

/-- the ι node at the constructor major. -/
def riIota : ConvT riEnv 1 riCtx riMid riRhs riTyR :=
  .iota _ _ _ _ (riW_lhs ▸ riW_rhs ▸ DerivedIota.of riW) riMidTy riRhsTy

/-- `rec M m X h ≡ rec M m X (mk X) : M X h` — `irr` under `app`. -/
def riStep1 : ConvT riEnv 1 riCtx riLhs riMid riTyL :=
  .app _ riRecMMX riRecMMX (.bvar 0) riMkX riP (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))
    (.refl _ _ _ riRecMMXTy) riIrr

/-- `M X (mk X) ≡ M X h : Sort u` — the motive's proof argument, by the same leaf. -/
def riTyFix : ConvT riEnv 1 riCtx riTyR riTyL (.sort (.param 0)) :=
  .app _ riMX riMX riMkX (.bvar 0) riP (.sort (.param 0))
    (.refl _ _ _ riMXTy) (.symm _ _ _ _ riIrr)

/-- **The class-(c3) K-like cell in `ConvT`:** `rec M m X h ≡ m X : M X h` at a variable major. -/
def riConvK : ConvT riEnv 1 riCtx riLhs riRhs riTyL :=
  .trans _ _ riMid _ _ riStep1 (.tyConv _ _ _ _ _ (.param 0) riIota riTyFix)

/-! ## §5 the erased cell: `tableOfK` misses it, the bare override closes it -/

/-- the K gate refuses `RI`: its field `X` is not a family application. -/
theorem riKGate_false : iotaKGate 0 riFam riCtor riRec = false := by decide

theorem riKRuleOf_none : iotaKRuleOf 0 riFam [(1, riCtor)] 2 riRec = none := by
  simp [iotaKRuleOf, riKGate_false]

theorem tableOfK_ri : tableOfK riEnvWfT = iotaRulesKOf 0 riFam [(1, riCtor)] 2 riRec := by
  show iotaRulesKOf 0 riFam [(1, riCtor)] 2 riRec ++ tableOfK .empty = _
  rw [tableOfK_empty, List.append_nil]

/-- no rule of `tableOfK riEnvWfT` is bare. -/
theorem tableOfK_ri_no_bare : ∀ ρ ∈ tableOfK riEnvWfT, ρ.major ≠ none := by
  intro ρ hρ hm
  rw [tableOfK_ri] at hρ
  have := bare_mem_iotaRulesKOf hρ hm
  rw [riKRuleOf_none] at this
  cases this

def riScope : ScopedCtx riEnv riEnv 1 riCtx := ⟨riEnvWfT, envExt_refl _, riCtxWf⟩

noncomputable def riLhsP : TyP riEnv 1 riCtx riLhs riTyL :=
  enrichHasTyT_of_envWfT riEnvWfT riCtxWf riLhsTy
noncomputable def riMidP : TyP riEnv 1 riCtx riMid riTyR :=
  enrichHasTyT_of_envWfT riEnvWfT riCtxWf riMidTy
noncomputable def riRhsP : TyP riEnv 1 riCtx riRhs riTyR :=
  enrichHasTyT_of_envWfT riEnvWfT riCtxWf riRhsTy

/-- the erased redex `rec M m X` (`h`, a proof, dropped). -/
def riLhsE (ls : List Level) : ETm := ETm.appN (.const 2 ls) [.bvar 2, .bvar 1, .bvar 0]
/-- the erased contractum `m X`. -/
def riRhsE : ETm := .app (.bvar 1) (.bvar 0)

/-- PIN: the canonical disposition drops the proof `h` and keeps the data `X`, `m`, `M`. -/
theorem ri_can : riScope.can id = [.drop, .keep, .keep, .keep] := by
  with_unfolding_all rfl

/-- PIN: the variable-major redex and the constructor-major redex erase to the same `rec M m X`,
    the contractum to `m X`. -/
theorem ri_eps : riLhsP.eps id (riScope.can id) = riLhsE [.param 0] ∧
    riMidP.eps id (riScope.can id) = riLhsE [.param 0] ∧
    riRhsP.eps id (riScope.can id) = riRhsE := by
  refine ⟨?_, ?_, ?_⟩ <;> with_unfolding_all rfl

/-- `const h` applied to variables only. -/
inductive ConstBvars (h : Nat) : ETm → Prop
  | head (ls : List Level) : ConstBvars h (.const h ls)
  | app {t : ETm} (i : Nat) (ht : ConstBvars h t) : ConstBvars h (.app t (.bvar i))

theorem constBvars_spineHead {h : Nat} {t : ETm} (ht : ConstBvars h t) :
    ∃ ls, ETm.spineHead t = .const h ls := by
  induction ht with
  | head ls => exact ⟨ls, rfl⟩
  | app _ _ ih => exact ih

theorem constBvars_app_arg {h : Nat} {t x : ETm} (hc : ConstBvars h (.app t x)) :
    ∃ i, x = .bvar i := by
  cases hc with
  | app i _ => exact ⟨i, rfl⟩

theorem appN_const_ne_bvar {c i : Nat} {ls : List Level} (xs : List ETm) :
    ETm.appN (.const c ls) xs ≠ .bvar i := by
  intro h
  have := congrArg ETm.spineHead h
  rw [ETm.spineHead_appN] at this
  cases this

theorem rStep_bvar_false {tbl : List CRule} {i : Nat} {z : ETm} (h : RStep tbl (.bvar i) z) :
    False := by
  cases h with
  | cr hc =>
      obtain ⟨c, ls, xs, hx⟩ := cRoot_lhs hc
      exact appN_const_ne_bvar xs hx.symm

theorem cRoot_constBvars_false {tbl : List CRule} {h : Nat}
    (hnb : ∀ ρ ∈ tbl, ρ.head = h → ρ.major ≠ none) {t z : ETm}
    (hc : CRoot tbl t z) (ht : ConstBvars h t) : False := by
  cases hc with
  | bare hρ hm ls args _ =>
      obtain ⟨ls', hs⟩ := constBvars_spineHead ht
      rw [ETm.spineHead_appN] at hs
      cases hs
      exact hnb _ hρ rfl hm
  | ctor hρ hm ls ls' args bs _ _ =>
      rw [ETm.appN_snoc] at ht
      obtain ⟨i, hi⟩ := constBvars_app_arg ht
      exact appN_const_ne_bvar bs hi

theorem rStep_constBvars_false {tbl : List CRule} {h : Nat}
    (hnb : ∀ ρ ∈ tbl, ρ.head = h → ρ.major ≠ none) {t z : ETm}
    (hs : RStep tbl t z) (ht : ConstBvars h t) : False := by
  induction hs with
  | beta M N => cases ht with | app _ ht' => cases ht'
  | cr hc => exact cRoot_constBvars_false hnb hc ht
  | appL a _ ih => cases ht with | app _ ht' => exact ih ht'
  | appR f hs' => cases ht with | app _ _ => exact rStep_bvar_false hs'
  | lam _ => cases ht
  | piL _ _ => cases ht
  | piR _ _ => cases ht

theorem etaStep_constBvars_false {h : Nat} {t z : ETm} (hs : EtaStep t z)
    (ht : ConstBvars h t) : False := by
  induction hs with
  | eta F => cases ht
  | appL a _ ih => cases ht with | app _ ht' => exact ih ht'
  | appR f hs' => cases ht with | app _ _ => cases hs'
  | lam _ => cases ht
  | piL _ _ => cases ht
  | piR _ _ => cases ht

theorem riLhsE_constBvars (ls : List Level) : ConstBvars 2 (riLhsE ls) :=
  .app 0 (.app 1 (.app 2 (.head ls)))

/-- **`tableOfK` does not close the cell**: the erased redex is normal (the only rule at `2` needs a
    constructor major, which erasure dropped) and `const`-headed; every reduct of the contractum is
    `bvar 1`-headed. -/
theorem riCell_not_convE_tableOfK (ls : List Level) :
    ¬ ConvMod (EStep (tableOfK riEnvWfT)) LvlEq (riLhsE ls) riRhsE := by
  intro h
  have hW := tableWF_tableOfK riEnvWfT
  obtain ⟨c, d, hc, hq, hd⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) h
  have hnb : ∀ ρ ∈ tableOfK riEnvWfT, ρ.head = 2 → ρ.major ≠ none :=
    fun ρ hρ _ => tableOfK_ri_no_bare ρ hρ
  obtain rfl := rstar_of_normal (fun z hz => hz.elim
    (fun hr => rStep_constBvars_false hnb hr (riLhsE_constBvars ls))
    (fun he => etaStep_constBvars_false he (riLhsE_constBvars ls))) hc
  have hdh : ETm.spineHead d = .bvar 1 := rstar_spineHead_bvar hd rfl
  have := lvlEq_spineHead_bvar (lvlEq_equivalence.symm hq) hdh
  cases this

/-- the same, read on the landed erasure of the `ConvT` cell `riConvK`'s endpoints. -/
theorem riConvK_not_es_tableOfK :
    ¬ ConvMod (EStep (tableOfK riEnvWfT)) LvlEq (riLhsP.eps id (riScope.can id))
      (riRhsP.eps id (riScope.can id)) := by
  rw [ri_eps.1, ri_eps.2.2]
  exact riCell_not_convE_tableOfK _

/-- the bare override at `RI`'s recursor: `rec ↦ λ M m X. m X` — the revealed field read off the
    index. -/
def riKRule : CRule where
  head := 2
  nargs := fun _ => 0
  major := none
  rhs := fun _ _ => .lam (.lam (.lam (.app (.bvar 1) (.bvar 0))))

theorem riKRule_override : BareOverride [riKRule] where
  bare := by intro ρ hρ; simp only [List.mem_singleton] at hρ; subst hρ; rfl
  nullary := by intro ρ hρ _; simp only [List.mem_singleton] at hρ; subst hρ; rfl
  closed := by
    intro ρ hρ _ _
    simp only [List.mem_singleton] at hρ; subst hρ
    simp [riKRule, ETm.ClosedAt]
  congr :=
    { rhs := by
        intro ρ hρ _ _ _ _ _ _
        simp only [List.mem_singleton] at hρ; subst hρ
        exact LvlEq.rfl' _
      nargs := by
        intro ρ hρ _ _ _
        simp only [List.mem_singleton] at hρ; subst hρ; rfl
      marity := by
        intro ρ hρ _ _ hm
        simp only [List.mem_singleton] at hρ; subst hρ; cases hm }
  nodup := by simp

theorem riKRule_atRecursor : HeadsAtRecursors riEnv [riKRule] := by
  intro κ hκ
  simp only [List.mem_singleton] at hκ; subst hκ
  exact ⟨riRec, rfl, rfl⟩

/-- **G1 at `RI`**: the overridden table is `TableWF`. -/
theorem riOverride_wf : TableWF (overrideTableK riEnvWfT [riKRule]) :=
  tableWF_override_tableOfK riEnvWfT riKRule_override riKRule_atRecursor

theorem riKRule_mem : riKRule ∈ overrideTableK riEnvWfT [riKRule] :=
  List.mem_append_left _ (List.mem_singleton_self _)

/-- one bare unfold at the head, then three β. -/
theorem riOverride_chain (ls : List Level) :
    RStar (RStep (overrideTableK riEnvWfT [riKRule])) (riLhsE ls) riRhsE :=
  .step (rStep_appN_head (.cr (.bare riKRule_mem rfl ls [] rfl)) [.bvar 2, .bvar 1, .bvar 0])
    (.step (rStep_appN_head (.beta _ (.bvar 2)) [.bvar 1, .bvar 0])
      (.step (rStep_appN_head (.beta _ (.bvar 1)) [.bvar 0])
        (.step (.beta _ (.bvar 0)) (.refl _))))

/-- **the override closes the cell** that `ConvT` derives at a variable major. -/
theorem riConvK_es_override :
    ConvMod (EStep (overrideTableK riEnvWfT [riKRule])) LvlEq (riLhsP.eps id (riScope.can id))
      (riRhsP.eps id (riScope.can id)) := by
  rw [ri_eps.1, ri_eps.2.2]
  exact convMod_of_rstar_estep (riOverride_chain _)

/-- and erased sort separation holds there (G1). -/
theorem ri_eqN_of_convE_sort {l l' : Level}
    (h : ConvMod (EStep (overrideTableK riEnvWfT [riKRule])) LvlEq (.sort l) (.sort l')) :
    eqN l l' :=
  eqN_of_convE_sort_override riEnvWfT riKRule_override riKRule_atRecursor h

/-! ## §6 the pack premise: `AllBelowScoped … (tableOfK riEnvWfT)` is false

The enriched `riConvK` is a demanded `es` root at the admitted scope. Its erased endpoints are the
cell's, so `ES` fails under `tableOfK` and holds under the override. Hence no `tableOfK`-based
`AllBelowScoped` pack exists at `riEnv`, for any measure weight `Aw`. -/

/-- `AssumpPref` of any `EnvWfT`-fronted conversion enrichment, from the native adapters. -/
theorem enrichConvT_native_ap {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {a b T : Expr Nat} (h : ConvT E n Γ a b T) :
    (enrichConvT_of_envWfT hW hΓ h).AssumpPref :=
  assumpPref_enrichConvT (envClosed_of_envWfT hW) (envExt_refl E)
    ((NativeValleys.NativeSortRetypeAudit.nativeEnrichAPAdapters E n).member hW)
    ((NativeValleys.NativeSortRetypeAudit.nativeEnrichAPAdapters E n).letCtx hW) _ h
    (assumpPref_enrichCtxWfT (envClosed_of_envWfT hW) (envExt_refl E)
      ((NativeValleys.NativeSortRetypeAudit.nativeEnrichAPAdapters E n).member hW)
      ((NativeValleys.NativeSortRetypeAudit.nativeEnrichAPAdapters E n).letCtx hW) hΓ)

/-- the enriched K-like cell. -/
noncomputable def riH : CvP riEnv 1 riCtx riLhs riRhs riTyL :=
  enrichConvT_of_envWfT riEnvWfT riCtxWf riConvK

theorem riH_ap : riH.AssumpPref := enrichConvT_native_ap riEnvWfT riCtxWf riConvK

theorem riH_dl_eps : riH.dl.eps id (riScope.can id) = riLhsE [.param 0] := by
  with_unfolding_all rfl

theorem riH_dr_eps : riH.dr.eps id (riScope.can id) = riRhsE := by
  with_unfolding_all rfl

/-- `ES` fails at the cell under `tableOfK`. -/
theorem riH_not_es_tableOfK : ¬ ES (tableOfK riEnvWfT) id (riScope.can id) riH := by
  intro h
  unfold ES at h
  rw [riH_dl_eps, riH_dr_eps] at h
  exact riCell_not_convE_tableOfK _ h

/-- **No `tableOfK` pack at an admitted class-(c3) environment.** -/
theorem not_allBelowScoped_tableOfK_ri (Aw : Nat → Nat) :
    ¬ AllBelowScoped riEnv Aw (tableOfK riEnvWfT) := fun hBel =>
  riH_not_es_tableOfK (es_of_allBelowScoped hBel riScope levelHom_id riH riH_ap)

/-- `ES` holds at the cell under the G1 override. -/
theorem riH_es_override : ES (overrideTableK riEnvWfT [riKRule]) id (riScope.can id) riH := by
  unfold ES
  rw [riH_dl_eps, riH_dr_eps]
  exact convMod_of_rstar_estep (riOverride_chain _)

end Rcic.Syn.ClassC

#print axioms Rcic.Syn.ClassC.riPolicy_anySort
#print axioms Rcic.Syn.ClassC.riCtor_field_not_prop
#print axioms Rcic.Syn.ClassC.riEnvWfT
#print axioms Rcic.Syn.ClassC.riConvK
#print axioms Rcic.Syn.ClassC.riKGate_false
#print axioms Rcic.Syn.ClassC.ri_eps
#print axioms Rcic.Syn.ClassC.riCell_not_convE_tableOfK
#print axioms Rcic.Syn.ClassC.riConvK_not_es_tableOfK
#print axioms Rcic.Syn.ClassC.riOverride_wf
#print axioms Rcic.Syn.ClassC.riConvK_es_override
#print axioms Rcic.Syn.ClassC.ri_eqN_of_convE_sort
#print axioms Rcic.Syn.ClassC.riH_not_es_tableOfK
#print axioms Rcic.Syn.ClassC.not_allBelowScoped_tableOfK_ri
#print axioms Rcic.Syn.ClassC.riH_es_override
