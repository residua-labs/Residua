/-
RCIC 07 §3 — G2-S1: `EnvWfT` admission of the `Bool` support block
(`boolMembersAt 0`, `RcicG2Objects`) — one `EnvWfT.group` step from the
empty environment.

`Bool`'s family member is `natFamMember` (`Sort 1`, arity 0) and both
nullary constructors are `natZeroMember` (`const 0`), member for member;
so the family and `ff` admissions ARE the Nat fixture's (`natFamAdmitted`,
`natZeroAdmitted`, `RcicIndGroupFixtureWf`), and `tt` reuses its views.
The recursor admission is new: `.anySort` by `uniformType` (a `Type`
family), its stored `boolRecTy 0` the policy recursor type by `rfl` —
so the hand-written type in `RcicG2Objects` is the one 05 §11 derives.
Typed content and the `hT` slots are paid by checker leaves through the
`GroupAcceptChain` route (`RcicEGTypedGroup`, as `RcicPinEqEraseWf`).
-/
import rcic.RcicG2Admit
import rcic.RcicIndGroupFixtureWf
import rcic.RcicEGTypedGroup

set_option maxRecDepth 8192

namespace Rcic.G2
open Rcic.Declarative
open Rcic.Scm.SrcG (sortTyAtC)

/-! ## (1) the members and the prefix chain -/

def boolRecMember : CheckedMember := ⟨.recursorM, 1, boolRecTy 0, none⟩

theorem boolMembersAt_zero :
    boolMembersAt 0 =
      [(0, natFamMember), (1, natZeroMember), (2, natZeroMember), (3, boolRecMember)] := rfl

/-- family, `ff`, `tt`. -/
def boolPrefix : ResolvedEnv := extendEnv natFamZero 2 natZeroMember
def boolEnv : ResolvedEnv := extendEnv boolPrefix 3 boolRecMember

theorem boolBlockEnv_eq : blockEnv emptyEnv (boolMembersAt 0) = boolEnv := rfl

theorem boolPrefix_mem (c : Nat) :
    boolPrefix.members c =
      if c = 2 then some natZeroMember
      else if c = 1 then some natZeroMember
      else if c = 0 then some natFamMember
      else none := rfl

/-! ## (2) the family and constructor admissions -/

theorem ttBefore : CtorBeforeRecursors natFamZero natZeroMember := by
  refine ⟨0, rfl, ?_⟩
  intro rr rm hm hk _
  rw [natFamZero_members] at hm
  by_cases h1 : rr = 1
  · rw [if_pos h1] at hm
    cases hm
    cases hk
  · by_cases h0 : rr = 0
    · rw [if_neg h1, if_pos h0] at hm
      cases hm
      cases hk
    · rw [if_neg h1, if_neg h0] at hm
      cases hm

theorem ttContig : CtorContiguous natFamZero 2 natZeroMember := by
  refine ⟨0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    have hc : c = 1 := by omega
    subst hc
    exact ⟨natZeroMember, by rw [natFamZero_members]; rfl, rfl, rfl⟩
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [natFamZero_members] at hm
    by_cases h1 : c = 1
    · subst h1
      exact ⟨by decide, by decide⟩
    · by_cases h0 : c = 0
      · rw [if_neg h1, if_pos h0] at hm
        cases hm
        cases hc
      · rw [if_neg h1, if_neg h0] at hm
        cases hm

/-- `tt`, admitted after `ff`. -/
def ttAdmitted : IndGroupAdmitted natFamZero 2 natZeroMember :=
  .constructor (natFamView natFamZero rfl) (natZeroView natFamZero rfl)
    rfl ttBefore ttContig (fun j => j.elim0) (fun j => j.elim0)

theorem boolCensus : CtorCensus boolPrefix 0 3 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, _⟩
    rw [boolPrefix_mem] at hc
    by_cases h2 : c = 2
    · rw [if_pos h2] at hc
      exact ⟨by omega, by omega⟩
    · by_cases h1 : c = 1
      · rw [if_neg h2, if_pos h1] at hc
        exact ⟨by omega, by omega⟩
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hc
          cases hc
          cases hk
        · rw [if_neg h2, if_neg h1, if_neg h0] at hc
          cases hc
  · intro h
    have hc : c = 1 ∨ c = 2 := by omega
    rcases hc with rfl | rfl
    · exact ⟨natZeroMember, rfl, rfl, rfl⟩
    · exact ⟨natZeroMember, rfl, rfl, rfl⟩

/-! ## (3) the recursor admission -/

/-- `P ff` and `P tt`, under the motive and the earlier minors. -/
def boolMinors : List (Expr Nat) :=
  [ .app (.bvar 0) (.const 1 []), .app (.bvar 1) (.const 2 []) ]

def boolGroupAdm : RecursorEliminationAdmitted boolPrefix 3 boolRecMember where
  family := natFamView boolPrefix rfl
  constructors := [natZeroMember, natZeroMember]
  constructorViews
    | ⟨0, _⟩ => natZeroView boolPrefix rfl
    | ⟨1, _⟩ => natZeroView boolPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  recursorRef := rfl
  minorTypes := boolMinors
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem boolMinorMatch : MinorPremisesMatch boolGroupAdm
  | ⟨0, _⟩ => ⟨[], 0, rfl, rfl⟩
  | ⟨1, _⟩ => ⟨[], 0, rfl, rfl⟩

/-- the equation context `[mt, mf, P]` — field-free, so each reduct is its
    minor variable, a single lookup. -/
def boolEqCtx : LCtx :=
  [.assumption (.app (.bvar 1) (.const 2 [])), .assumption (.app (.bvar 0) (.const 1 [])),
    .assumption (.pi (.const 0 []) (.sort (.param 0)))]

def boolIotaFF : IotaEquationTyped boolGroupAdm ⟨0, by decide⟩ 0 [] := by
  unfold IotaEquationTyped
  exact HasTy.bvar boolEqCtx 1 _ rfl

def boolIotaTT : IotaEquationTyped boolGroupAdm ⟨1, by decide⟩ 0 [] := by
  unfold IotaEquationTyped
  exact HasTy.bvar boolEqCtx 0 _ rfl

def boolIotaClause : IotaDescriptorClause boolPrefix boolGroupAdm where
  signatureOnly := rfl
  shapesAt := fun _ => []
  fuelAt := fun _ => 0
  analyzed
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  typed
    | ⟨0, _⟩ => boolIotaFF
    | ⟨1, _⟩ => boolIotaTT

def boolRecAdmitted : IndGroupAdmitted boolPrefix 3 boolRecMember :=
  .recursor boolGroupAdm rfl boolCensus
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => fun j => j.elim0)
    (fun | ⟨0, _⟩ => fun j => j.elim0 | ⟨1, _⟩ => fun j => j.elim0)
    boolMinorMatch boolIotaClause

/-! ## (4) checker leaves, the chain, and the group step -/

kernel_rfl_theorem boolSortB0 :
    (sortTyAtC emptyEnv 0 96 [] natFamMember.mtype).isSome = true

kernel_rfl_theorem boolSortB1 :
    (sortTyAtC natFamOnly 0 96 [] natZeroMember.mtype).isSome = true

kernel_rfl_theorem boolSortB2 :
    (sortTyAtC natFamZero 0 96 [] natZeroMember.mtype).isSome = true

kernel_rfl_theorem boolSortB3 :
    (sortTyAtC boolPrefix 1 96 [] boolRecMember.mtype).isSome = true

kernel_rfl_theorem boolAccB0 :
    memberAcceptB natFamOnly emptyEnv 96 natFamAdmitted
      ((sortTyAtC emptyEnv 0 96 [] natFamMember.mtype).get boolSortB0).1 = true

kernel_rfl_theorem boolAccB1 :
    memberAcceptB natFamOnly natFamOnly 96 natZeroAdmitted
      ((sortTyAtC natFamOnly 0 96 [] natZeroMember.mtype).get boolSortB1).1 = true

kernel_rfl_theorem boolAccB2 :
    memberAcceptB natFamOnly natFamZero 96 ttAdmitted
      ((sortTyAtC natFamZero 0 96 [] natZeroMember.mtype).get boolSortB2).1 = true

kernel_rfl_theorem boolAccB3 :
    memberAcceptB natFamOnly boolPrefix 96 boolRecAdmitted
      ((sortTyAtC boolPrefix 1 96 [] boolRecMember.mtype).get boolSortB3).1 = true

def boolGroupChain :
    GroupAcceptChain natFamOnly 96 emptyEnv
      [(0, natFamMember), (1, natZeroMember), (2, natZeroMember), (3, boolRecMember)] boolEnv :=
  .cons emptyEnv 0 natFamMember _ _ natFamAdmitted boolSortB0 boolAccB0
    (.cons natFamOnly 1 natZeroMember _ _ natZeroAdmitted boolSortB1 boolAccB1
      (.cons natFamZero 2 natZeroMember _ _ ttAdmitted boolSortB2 boolAccB2
        (.cons boolPrefix 3 boolRecMember _ _ boolRecAdmitted boolSortB3 boolAccB3
          (.nil boolEnv))))

kernel_rfl_theorem boolClassB :
    groupClassB natFamMember [(1, natZeroMember), (2, natZeroMember)] boolRecMember = true

/-- `Bool`'s block admits: one `EnvWfT.group` step from the empty env. -/
def boolBlockWfT : EnvWfT (blockEnv emptyEnv (boolMembersAt 0)) :=
  EG010T_group_accepted .empty 96 boolClassB boolGroupChain

end Rcic.G2
