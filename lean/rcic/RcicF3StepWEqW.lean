import rcic.RcicPinEqEraseWf
import rcic.RcicF3Layout
import rcic.RcicFamAppStepWLok

/-!
# RcicF3StepWEqW — the canonical W-class group over the OUT-OF-SCOPE `Eq` prefix

The W-class residue of `stepW` (`RcicFamAppStepWLok` §4's exact boundary): a `PendW`
group (a constructor whose own admission view splits off MORE parameters than the
recursor's family view) whose group environment `E'` lies OUTSIDE every landed row
supplier (`InScope`, `ScopeCheck`, `RevEnv`).  Pure-W groups are in scope — the
`wCanon` V-group passes `groupCheckB` by `rfl` (`RcicFamAppStepWLok` §5) — so an
out-of-scope W-class env is out of scope through its PREFIX.  This module builds the
canonical such fixture: the `pw` W-witness (`V : Prop → Type`, `mk` admitted with the
PARAMETRIC split `np_c = 1`, the recursor with the INDEXED split `np = 0`; the shape of
`RcicF3WalkWitness` on the f3-coverage branch) rebased over `eqEnvT` — the `Eq`
fixture (`RcicPinEqEraseWf`: `Eq : Π (A : Sort 1) (a b : A), Prop`, `refl`, the
`AnySort` J recursor; `pinEqGroupWfT : EnvWfT eqEnvT`).

What the fixture carries (`closure_claim = 0`, nothing about rows is claimed here):

- `eqWEnvWfT : EnvWfT eqWEnv` — the W-group admitted over the `Eq` prefix;
- `eqWNode : RecNode eqEnvT eqWEnv 66 68 eqWRec` with `np = 0` (`eqW_np`),
  `¬ WalkClass 0 eqWMembersT` (`eqW_not_walkClass`, i.e. `PendW`: `mk`'s own view has
  `np_c = 1` parameters), `UniformType` result level (`eqW_uniformType`) and
  `¬ UniformProp` (`eqW_not_uniformProp`) — the boundary's open arm;
- `eqW_gapNoAppLit` — the gap entry is `.sort .zero`, application-free, so the
  weakest `stepW` route (`stepW_of_noAppLit_sortRow`: `SortRowField` ALONE, zero
  `PiRowField`, zero `FamAppRowField`) already applies at this node;
- `eqW_hext` — `eqEnvT`'s members are all preserved in `eqWEnv` (the transport
  premise the obstruction module consumes).
-/

set_option autoImplicit false

namespace Rcic.Declarative

open Rcic.F3.PSet

/-! ## (1) the group — the `pw` W-witness at refs `66/67/68` over `eqEnvT` -/

/-- `V : Prop → Type`. -/
def eqWV : CheckedMember := ⟨.inductiveM, 0, .pi (.sort .zero) (.sort (.succ .zero)), none⟩

/-- `mk : Π (p : Prop), V p`. -/
def eqWMk : CheckedMember :=
  ⟨.constructorM, 0, .pi (.sort .zero) (.app (.const 66 []) (.bvar 0)), none⟩

/-- the motive: `Π (p : Prop) (v : V p), Sort (param 0)`. -/
abbrev eqWMotTy : Expr Nat :=
  .pi (.sort .zero) (.pi (.app (.const 66 []) (.bvar 0)) (.sort (.param 0)))

/-- the minor: `Π (p : Prop), mot p (mk p)`. -/
abbrev eqWMinor : Expr Nat :=
  .pi (.sort .zero) (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 67 []) (.bvar 0)))

def eqWRecType : Expr Nat :=
  .pi eqWMotTy (.pi eqWMinor (.pi (.sort .zero) (.pi (.app (.const 66 []) (.bvar 0))
    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))

def eqWRec : CheckedMember := ⟨.recursorM, 1, eqWRecType, none⟩

def eqWFamOnly : ResolvedEnv := extendEnv eqEnvT 66 eqWV
def eqWPrefix : ResolvedEnv := extendEnv eqWFamOnly 67 eqWMk
def eqWEnv : ResolvedEnv := extendEnv eqWPrefix 68 eqWRec

/-- membership in the family-only extension. -/
theorem eqWFamOnly_mem (c : Nat) :
    eqWFamOnly.members c = if c = 66 then some eqWV else eqEnvT.members c := rfl

/-- membership in the constructor extension. -/
theorem eqWPrefix_mem (c : Nat) :
    eqWPrefix.members c =
      if c = 67 then some eqWMk
      else if c = 66 then some eqWV
      else eqEnvT.members c := rfl

theorem eqW_fresh66 : eqEnvT.members 66 = none := by simp [eqEnvT_mem]
theorem eqW_fresh67 : eqWFamOnly.members 67 = none := by
  simp [eqWFamOnly_mem, eqEnvT_mem]
theorem eqW_fresh68 : eqWPrefix.members 68 = none := by
  simp [eqWPrefix_mem, eqEnvT_mem, eqWFamOnly_mem]

/-! ## (2) the two views of the family and of `mk` -/

/-- the parametric view of the family: `p` is a parameter. -/
def eqWFamView1 (E : ResolvedEnv) (h : E.members 66 = some eqWV) : PolicyFamilyView E where
  ref := 66
  member := eqWV
  present := h
  hasClass := rfl
  parameters := [.sort .zero]
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort _ .zero }

/-- the indexed view of the family: `p` is an index. -/
def eqWFamView2 (E : ResolvedEnv) (h : E.members 66 = some eqWV) : PolicyFamilyView E where
  ref := 66
  member := eqWV
  present := h
  hasClass := rfl
  parameters := []
  indices := [.sort .zero]
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort _ .zero }

/-- `mk` under the parametric view: one parameter, no field. -/
def eqWMkView1 (E : ResolvedEnv) (h : E.members 66 = some eqWV) :
    PolicyConstructorView E (eqWFamView1 E h) eqWMk where
  hasClass := rfl
  arity := rfl
  parameters := [.sort .zero]
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort _ .zero }
  parameterMirrors := fun i => match i with | ⟨0, _⟩ => Conv.refl _ _
  noFamilyInIndices := fun _ hx => nomatch hx

/-- `mk` under the indexed view: no parameter, one field, revealed as the result index. -/
def eqWMkView2 (E : ResolvedEnv) (h : E.members 66 = some eqWV) :
    PolicyConstructorView E (eqWFamView2 E h) eqWMk where
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
    hasType := fun j => match j with | ⟨0, _⟩ => HasTy.sort _ .zero }
  parameterMirrors := fun i => Fin.elim0 i
  noFamilyInIndices := fun e he => by
    simp only [List.mem_singleton] at he; subst he; rfl

/-! ## (3) the three admissions and the group walk -/

def eqWFamAdmitted : IndGroupAdmitted eqEnvT 66 eqWV :=
  .family rfl (eqWFamView1 eqWFamOnly rfl) rfl rfl (Or.inr uniformType_succ_zero)

/-- `mk`'s family ref is `66` (the stored type's result head). -/
theorem eqW_mkFamRef : memberFamRef eqWMk = some 66 := rfl

/-- no recursor for `66` sits in the family-only env. -/
def eqWCtorBefore : CtorBeforeRecursors eqWFamOnly eqWMk := by
  refine ⟨66, eqW_mkFamRef, ?_⟩
  intro rr rm hm hk hfr
  rw [eqWFamOnly_mem] at hm
  by_cases h66 : rr = 66
  · rw [if_pos h66] at hm
    cases hm
    exact absurd hk (fun h => nomatch h)
  · rw [if_neg h66, eqEnvT_mem] at hm
    by_cases h65 : rr = 65
    · rw [if_pos h65] at hm; cases hm; exact absurd hfr (fun h => nomatch h)
    · rw [if_neg h65] at hm
      by_cases h64 : rr = 64
      · rw [if_pos h64] at hm; cases hm; exact absurd hk (fun h => nomatch h)
      · rw [if_neg h64] at hm
        by_cases h63 : rr = 63
        · rw [if_pos h63] at hm; cases hm; exact absurd hk (fun h => nomatch h)
        · rw [if_neg h63] at hm; cases hm

def eqWCtorContig : CtorContiguous eqWFamOnly 67 eqWMk := by
  refine ⟨66, eqW_mkFamRef, by decide, ?_, ?_⟩
  · intro c hl hr
    exact False.elim (Nat.lt_irrefl 66 (Nat.lt_of_lt_of_le hl (Nat.le_of_lt_succ hr)))
  · intro c hex
    rcases hex with ⟨cm, hm, hc, hfr⟩
    rw [eqWFamOnly_mem] at hm
    by_cases h66 : c = 66
    · rw [if_pos h66] at hm
      cases hm
      exact absurd hc (fun h => nomatch h)
    · rw [if_neg h66, eqEnvT_mem] at hm
      by_cases h65 : c = 65
      · rw [if_pos h65] at hm; cases hm; exact absurd hc (fun h => nomatch h)
      · rw [if_neg h65] at hm
        by_cases h64 : c = 64
        · rw [if_pos h64] at hm; cases hm; exact absurd hfr (fun h => nomatch h)
        · rw [if_neg h64] at hm
          by_cases h63 : c = 63
          · rw [if_pos h63] at hm; cases hm; exact absurd hc (fun h => nomatch h)
          · rw [if_neg h63] at hm; cases hm

def eqWMkAdmitted : IndGroupAdmitted eqWFamOnly 67 eqWMk :=
  .constructor (eqWFamView1 eqWFamOnly rfl) (eqWMkView1 eqWFamOnly rfl)
    rfl eqWCtorBefore eqWCtorContig (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)

def eqWGroupAdmitted : RecursorEliminationAdmitted eqWPrefix 68 eqWRec where
  family := eqWFamView2 eqWPrefix rfl
  recursorMclass := rfl
  constructors := [eqWMk]
  constructorViews
    | ⟨0, _⟩ => eqWMkView2 eqWPrefix rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [eqWMinor]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem eqWMinorMatch : MinorPremisesMatch eqWGroupAdmitted := by
  intro i
  have hlt : i.val < 1 := i.isLt
  have hi : i = ⟨0, by decide⟩ := Fin.ext (Nat.lt_one_iff.mp hlt)
  rw [hi]
  exact ⟨[.nonrecursive], 8, rfl, rfl⟩

def eqWIotaIntro : IotaEquationTyped eqWGroupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive] := by
  dsimp [IotaEquationTyped, iotaEquationType, equationDoms, iotaSchemaAt, assumptionCtx,
    iotaLhsType, iotaOpenRhs, policyRecursorLevels, policyRecursorArity, policyFamilyLevels,
    preMajorBvars, fieldBvars, ctorFieldTelescope, liftFields, eqWGroupAdmitted, eqWMkView2,
    eqWFamView2, eqWRec, eqWRecType, peelPis, piCount, lift, policyPi, iotaArgs,
    policyParameterLocals, foldApps]
  exact HasTy.app _ (.bvar 2) (.bvar 0) (.sort .zero)
    (.app (.app (.bvar 4) (.bvar 0)) (.app (.const 67 []) (.bvar 0)))
    (HasTy.bvar _ 2 _ rfl) (HasTy.bvar _ 0 _ rfl)

def eqWShapes : Fin eqWGroupAdmitted.constructors.length → List FieldShape
  | ⟨0, _⟩ => [.nonrecursive]

def eqWIotaClause : IotaDescriptorClause eqWPrefix eqWGroupAdmitted where
  signatureOnly := rfl
  shapesAt := eqWShapes
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => eqWIotaIntro

/-- the census at the recursor: the constructors of `66` below `68` are exactly `67`. -/
def eqWCensus : CtorCensus eqWPrefix 66 68 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk', hf'⟩
    rw [eqWPrefix_mem] at hc
    by_cases h67 : c = 67
    · rw [if_pos h67] at hc
      exact ⟨by omega, by omega⟩
    · rw [if_neg h67] at hc
      by_cases h66 : c = 66
      · rw [if_pos h66] at hc
        cases hc
        exact absurd hk' (fun h => nomatch h)
      · rw [if_neg h66, eqEnvT_mem] at hc
        by_cases h65 : c = 65
        · rw [if_pos h65] at hc; cases hc; exact absurd hk' (fun h => nomatch h)
        · rw [if_neg h65] at hc
          by_cases h64 : c = 64
          · rw [if_pos h64] at hc; cases hc; exact absurd hf' (fun h => nomatch h)
          · rw [if_neg h64] at hc
            by_cases h63 : c = 63
            · rw [if_pos h63] at hc; cases hc; exact absurd hk' (fun h => nomatch h)
            · rw [if_neg h63] at hc; cases hc
  · intro h
    have hc : c = 67 := by omega
    subst hc
    exact ⟨eqWMk, rfl, rfl, eqW_mkFamRef⟩

def eqWRecAdmitted : IndGroupAdmitted eqWPrefix 68 eqWRec :=
  .recursor eqWGroupAdmitted rfl eqWCensus
    (fun i => match i with | ⟨0, _⟩ => fun _ => Or.inr ⟨uniformType_succ_zero, leN_refl _⟩)
    (fun i => match i with
      | ⟨0, _⟩ => fun j => match j with | ⟨0, _⟩ => ⟨.nonrecursive, 8, [], rfl⟩)
    eqWMinorMatch eqWIotaClause

/-! ## (4) the typings the walk and the node pay -/

/-- `V p : Type` for `p : Prop`. -/
def eqWVAppTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h : E.members 66 = some eqWV)
    {x : Expr Nat} (hx : HasTyT E n Γ x (.sort .zero)) :
    HasTyT E n Γ (.app (.const 66 []) x) (.sort (.succ .zero)) :=
  .app Γ _ x (.sort .zero) (.sort (.succ .zero)) (.const Γ 66 [] eqWV h rfl rfl) hx

def eqWFamTyT : HasTyT eqEnvT 0 [] eqWV.mtype
    (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
  .pi [] _ _ _ _ (.sort [] .zero) (.sort _ (.succ .zero))

def eqWMkTyT {E : ResolvedEnv} (h : E.members 66 = some eqWV) :
    HasTyT E 0 [] eqWMk.mtype (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] _ _ _ _ (.sort [] .zero) (eqWVAppTyT h (.bvar _ 0 _ rfl))

theorem eqWFamTyped1 (E : ResolvedEnv) (h : E.members 66 = some eqWV) :
    FamilyTypedT (eqWFamView1 E h) :=
  fun i => match i with | ⟨0, _⟩ => ⟨.sort [] .zero⟩

theorem eqWFamTyped2 (E : ResolvedEnv) (h : E.members 66 = some eqWV) :
    FamilyTypedT (eqWFamView2 E h) :=
  fun i => match i with | ⟨0, _⟩ => ⟨.sort [] .zero⟩

theorem eqWMkTyped1 (E : ResolvedEnv) (h : E.members 66 = some eqWV) :
    CtorTypedT (eqWMkView1 E h) :=
  ⟨fun i => match i with | ⟨0, _⟩ => ⟨.sort [] .zero⟩,
   fun i => match i with | ⟨0, _⟩ => ⟨.refl _ _⟩⟩

theorem eqWMkTyped2 (E : ResolvedEnv) (h : E.members 66 = some eqWV) :
    CtorTypedT (eqWMkView2 E h) :=
  ⟨fun i => match i with | ⟨0, _⟩ => ⟨.sort [] .zero⟩, fun i => Fin.elim0 i⟩

theorem eqWFamIsTyped : IndGroupTypedT eqWFamAdmitted := eqWFamTyped1 _ rfl

theorem eqWMkIsTyped : IndGroupTypedT eqWMkAdmitted := ⟨eqWFamTyped1 _ rfl, eqWMkTyped1 _ rfl⟩

theorem eqWRecIsTyped : IndGroupTypedT eqWRecAdmitted :=
  ⟨eqWFamTyped2 _ rfl, fun i => match i with | ⟨0, _⟩ => eqWMkTyped2 _ rfl,
   fun i => match i with | ⟨0, _⟩ => iotaEquationTypedT_of_check (synCheck _ _) rfl⟩

def eqWMkAppTyT {Γ : LCtx} {x : Expr Nat} (hx : HasTyT eqWPrefix 1 Γ x (.sort .zero)) :
    HasTyT eqWPrefix 1 Γ (.app (.const 67 []) x) (.app (.const 66 []) x) :=
  .app Γ _ x (.sort .zero) (.app (.const 66 []) (.bvar 0)) (.const Γ 67 [] eqWMk rfl rfl rfl) hx

def eqWMotTyT : HasTyT eqWPrefix 1 [] eqWMotTy
    (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ (.param 0))))) :=
  .pi [] _ _ _ _ (.sort [] .zero)
    (.pi _ _ _ _ _ (eqWVAppTyT rfl (.bvar _ 0 _ rfl)) (.sort _ (.param 0)))

abbrev eqWRecCtx : LCtx :=
  [.assumption (.app (.const 66 []) (.bvar 0)), .assumption (.sort .zero), .assumption eqWMinor,
    .assumption eqWMotTy]

def eqWRecTypeTyT : Σ u, HasTyT eqWPrefix 1 [] eqWRecType (.sort u) :=
  ⟨_, .pi [] _ _ _ _ eqWMotTyT
    (.pi _ _ _ _ _
      (.pi _ _ _ _ _ (.sort _ .zero)
        (.app _ (.app (.bvar 1) (.bvar 0)) (.app (.const 67 []) (.bvar 0))
          (.app (.const 66 []) (.bvar 0)) (.sort (.param 0))
          (.app _ (.bvar 1) (.bvar 0) (.sort .zero)
            (.pi (.app (.const 66 []) (.bvar 0)) (.sort (.param 0)))
            (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl))
          (eqWMkAppTyT (.bvar _ 0 _ rfl))))
      (.pi _ _ _ _ _ (.sort _ .zero)
        (.pi _ _ _ _ _ (eqWVAppTyT rfl (.bvar _ 0 _ rfl))
          (.app _ (.app (.bvar 3) (.bvar 1)) (.bvar 0) (.app (.const 66 []) (.bvar 1))
            (.sort (.param 0))
            (.app _ (.bvar 3) (.bvar 1) (.sort .zero)
              (.pi (.app (.const 66 []) (.bvar 0)) (.sort (.param 0)))
              (.bvar eqWRecCtx 3 _ rfl) (.bvar eqWRecCtx 1 _ rfl))
            (.bvar eqWRecCtx 0 _ rfl)))))⟩

/-- the group walk: family, constructor, recursor, over the `Eq` prefix. -/
def eqWMembersT :
    GroupMembersT eqWFamOnly eqEnvT [(66, eqWV), (67, eqWMk), (68, eqWRec)] eqWEnv :=
  .cons _ 66 eqWV _ _ eqW_fresh66 rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    eqWFamAdmitted PUnit.unit _ eqWFamTyT (fun h => nomatch h)
    eqWFamIsTyped
    (.cons _ 67 eqWMk _ _ eqW_fresh67 rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      eqWMkAdmitted PUnit.unit _ (eqWMkTyT rfl) (fun _ => ⟨eqWMkTyT rfl⟩)
      eqWMkIsTyped
      (.cons _ 68 eqWRec _ _ eqW_fresh68 rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        eqWRecAdmitted (.ofCheck _ _ (by with_unfolding_all rfl)) _ eqWRecTypeTyT.2
        (fun h => absurd h (by decide))
        eqWRecIsTyped (.nil _)))

/-- the `Eq` prefix's own derivation, as a LITERAL `.group` application (so `EnvWfT.InScope`
    fires on it by whnf; `pinEqGroupWfT`'s `let`-chain blocks reduction). -/
def eqPrefixWfT : EnvWfT eqEnvT :=
  .group emptyEnv 63 eqFamT [(64, eqReflT)] 65 eqRecT eqEnvT .empty rfl
    (fun c hc => by simp at hc; subst hc; rfl) rfl
    (groupMembersT_of_chain eqGroupChain)

/-- The witness: an admitted W-class group environment over the out-of-scope `Eq` prefix. -/
def eqWEnvWfT : EnvWfT eqWEnv :=
  .group eqEnvT 66 eqWV [(67, eqWMk)] 68 eqWRec eqWEnv eqPrefixWfT rfl
    (fun c hc => by simp at hc; subst hc; rfl) rfl eqWMembersT

/-! ## (5) the node, `np`, `PendW`, the gap, and the boundary's open arm -/

def eqWBase : ∀ r m, eqEnvT.members r = some m → eqWPrefix.members r = some m := by
  intro r m h
  rw [eqWPrefix_mem]
  by_cases h67 : r = 67
  · subst h67
    rw [eqEnvT_mem] at h
    cases h
  · rw [if_neg h67]
    by_cases h66 : r = 66
    · subst h66
      rw [eqW_fresh66] at h
      cases h
    · rw [if_neg h66]
      exact h

def eqWPres : ∀ r m, eqWPrefix.members r = some m →
    (extendEnv eqWPrefix 68 eqWRec).members r = some m := by
  intro r m h
  have hp : (extendEnv eqWPrefix 68 eqWRec).members r =
      if r = 68 then some eqWRec else eqWPrefix.members r := rfl
  rw [hp]
  by_cases h68 : r = 68
  · rw [h68] at h
    rw [eqW_fresh68] at h
    cases h
  · rw [if_neg h68]
    exact h

def eqWSub : ∀ r m, (extendEnv eqWPrefix 68 eqWRec).members r = some m → eqWEnv.members r = some m := by
  intro r m h
  exact (show eqWEnv.members r = some m from h)

/-- the recursor node, built directly from the admission. -/
def eqWNode : RecNode eqEnvT eqWEnv 66 68 eqWRec where
  E0 := eqWPrefix
  a := eqWGroupAdmitted
  h14 := eqWIotaClause
  fam := rfl
  fresh := eqW_fresh68
  sub := eqWSub
  base := eqWBase
  h04 := eqWCensus
  h07 := fun i => match i with | ⟨0, _⟩ => fun _ => Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
  h12 := eqWMinorMatch
  famTyped := eqWFamTyped2 _ rfl
  ctorsTyped := fun i => match i with | ⟨0, _⟩ => eqWMkTyped2 _ rfl
  u := eqWRecTypeTyT.1
  hT := eqWRecTypeTyT.2

/-- the recursor's family view is the INDEXED one: `np = 0`. -/
theorem eqW_np : eqWNode.a.family.parameters.length = 0 := rfl

/-- `mk`'s own admission view is the PARAMETRIC one: `np_c = 1`. -/
theorem eqW_mkNpC : (eqWMkView1 eqWFamOnly rfl).parameters.length = 1 := rfl

/-- **`PendW` at the node**: the constructor's own view splits off one parameter where the
    recursor's family view splits off none — `¬ WalkClass 0`. -/
theorem eqW_not_walkClass : ¬ WalkClass 0 eqWMembersT :=
  fun ⟨_, hMk, _⟩ => Nat.succ_ne_zero _ hMk

def eqWWalkRec : WalkRec eqWMembersT :=
  ⟨trivial, trivial, rfl, trivial⟩

/-- the family's result level is `Type 0`: the boundary's `UniformType` arm. -/
theorem eqW_uniformType : UniformType eqWNode.a.family.resultLevel := uniformType_succ_zero

theorem eqW_not_uniformProp : ¬ UniformProp eqWNode.a.family.resultLevel :=
  not_uniformProp_succ_zero

/-- the gap entry is `.sort .zero` — application-free, so the weakest `stepW` route
    (`SortRowField` alone) applies at this node. -/
theorem eqW_gapNoAppLit :
    WalkAgree (Rcic.Syn.FamApp.StepW.GapEntriesNoAppLit 0) eqWMembersT :=
  ⟨trivial, fun k _hk _hge hlt => by
    have h0 : k = 0 := Nat.lt_one_iff.mp hlt
    subst h0
    exact .sort .zero, trivial, trivial⟩

/-- `eqEnvT`'s members survive into `eqWEnv` — the transport premise of the obstruction. -/
theorem eqW_hext : ∀ r m, eqEnvT.members r = some m → eqWEnv.members r = some m :=
  fun r m h => eqWSub r m (eqWPres r m (eqWBase r m h))

end Rcic.Declarative

#print axioms Rcic.Declarative.eqWEnvWfT
#print axioms Rcic.Declarative.eqWNode
#print axioms Rcic.Declarative.eqW_not_walkClass
