import rcic.RcicTypedConvPins
import rcic.RcicUntypedConvCollapse
import rcic.RcicIARecTyped

open Rcic.Scm.SrcG

/-!
# R-NoFunRec-1 step 0 — a recursive field reached through δ, admitted and typed

The group of R-NoFunRec-1-0, item 4: `Id : Sort 1 → Sort 1 := λ A, A` at `0`, a family `F : Sort 1` at
`1`, and `mk : Id F → F` at `2`. The field `Id F` is directly recursive after δ and β
(`dr_fieldAnalyze`). Its head as written is `Id`, and its spine names `F` (`dr_storedReading`).

* Admission reads the field as the analysis does (`dr_analyzedReading`). The derived minor is
  `Π (x : Id F), motive x → motive (mk x)` (`drMinor_derived`), and the recursor stored with it is
  admitted (`drGroupRecursor`). The ι schema is `minor x (rec motive minor x)` (`drSchema_derived`).
  Before step 0 the minor read `F` off `Id`'s spine as an index (`motive F x`), so this recursor failed
  `MinorPremisesMatch` and admission refused the group.
* The typed environment judgment admits the environment (`drEnvWfT`): `Id` as a definition, then the
  group, with the ι equation typed in `HasTyT` (`IndGroupTypedT`). The equation needs the conversion
  `Id F ≡ F` at the recursive call's major, so the syntactic checker refuses it and the conversion checker
  types it (`drIota_needs_conversion`).
* The typed check can fail where the untyped one cannot. At the schema read off the stored type,
  `minor x (rec motive minor F x)`, the conversion checker refuses the equation: the call applies the
  recursor to `F : Sort 1` where the major `F` is due (`drIota_stored_refused`). The untyped judgment types
  that schema at the equation's type (`drIota_stored_legacy`), as it types every typable term at every
  type (`retypeAny`).
* `main`'s ι has no rule at `mk`. Its field has no kind (`drMk_noKind`), so no ι witness names this
  recursor, and the recursor's index admission holds with no case (`drRecIdxAdmitted`).
* The group's δ-reached field is scope-admitted on real evidence (R-NoDeltaRec-4c): the reader
  produces the `.drecD` skeleton (`dr_reader_sees_drecD`, convChecker only — the syntactic checker
  cannot type the recursor's domains), the scope test certifies it (`dr_skel_scope_admitted`, via
  `drecDsCheckB`), and the copy-side bridge still refuses it (`dr_skel_bridge_refused`, the `hsnd`
  gate). R-NoDeltaRec-4d-iii builds the annotated side of a `.drecD` field (`annFieldsTyT`'s `drecD`
  arm, `CtorCopyA.drecD_typed`) but keeps `hsnd`: it is the `EnvNormEraseA` gate of the
  erased↔annotated ι-correspondence, which a `.drecD` member breaks (`drCtorMemberA_diverge`). So
  this group stays outside the typed in-scope path exactly as before; R-NoDeltaRec stays open debt.
-/

namespace Rcic.Declarative

/-! ## (1) the group -/

/-- `Id : Sort 1 → Sort 1 := λ A, A` at `0`, a definition of arity 0. -/
def drIdMember : CheckedMember :=
  ⟨.definitionM, 0, .pi (.sort (.succ .zero)) (.sort (.succ .zero)),
    some (.lam (.sort (.succ .zero)) (.bvar 0))⟩

/-- `F : Sort 1` at `1`. -/
def drFamMember : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩

/-- the field `Id F`. -/
def drField : Expr Nat := .app (.const 0 []) (.const 1 [])

/-- `mk : Id F → F` at `2`. -/
def drMkMember : CheckedMember := ⟨.constructorM, 0, .pi drField (.const 1 []), none⟩

def drMotiveTy : Expr Nat := .pi (.const 1 []) (.sort (.param 0))

/-- the minor, under the motive: `Π (x : Id F), motive x → motive (mk x)`. -/
def drMinorTy : Expr Nat :=
  .pi drField (.pi (.app (.bvar 1) (.bvar 0)) (.app (.bvar 2) (.app (.const 2 []) (.bvar 1))))

/-- `F.rec` at `3`, eliminating into any sort, over that minor. -/
def drRecTy : Expr Nat := .pi drMotiveTy (.pi drMinorTy (.pi (.const 1 []) (.app (.bvar 2) (.bvar 0))))

def drRecMember : CheckedMember := ⟨.recursorM, 1, drRecTy, none⟩

def drBase : ResolvedEnv := extendEnv emptyEnv 0 drIdMember
def drFamEnv : ResolvedEnv := extendEnv drBase 1 drFamMember
def drMkEnv : ResolvedEnv := extendEnv drFamEnv 2 drMkMember
def drEnv : ResolvedEnv := extendEnv drMkEnv 3 drRecMember

theorem drFamEnv_members (c : Nat) :
    drFamEnv.members c = if c = 1 then some drFamMember else if c = 0 then some drIdMember else none :=
  rfl

theorem drMkEnv_members (c : Nat) :
    drMkEnv.members c =
      if c = 2 then some drMkMember else if c = 1 then some drFamMember
      else if c = 0 then some drIdMember else none := rfl

/-! ## (2) admission reads the field as the analysis does -/

/-- the analysis: directly recursive after δ and β, no index. -/
theorem dr_fieldAnalyze : fieldAnalyze drFamEnv 8 1 0 0 0 0 drField = .permitted (.recursive 0) [] := rfl

/-- the stored type's spine names `F` as an index of a field whose family has none: the reading admission
    used before step 0. -/
theorem dr_storedReading : familyIdx 0 drField = [.const 1 []] := rfl

/-- admission's reading since step 0: the field's telescope after δ and β is the family, no binder. -/
theorem dr_analyzedReading : piTelescopeFuel drMkEnv 8 drField = some ([], .const 1 []) := rfl

def drFamView (E : ResolvedEnv) (h : E.members 1 = some drFamMember) : PolicyFamilyView E where
  ref := 1
  member := drFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

/-- the field at `Sort 1` in the untyped judgment: `Id` applied to `F`, no conversion. -/
def drFieldTy (E : ResolvedEnv) (h0 : E.members 0 = some drIdMember) (h1 : E.members 1 = some drFamMember) :
    HasTy E 0 [] drField (.sort (.succ .zero)) :=
  HasTy.app [] (.const 0 []) (.const 1 []) (.sort (.succ .zero)) (.sort (.succ .zero))
    (HasTy.const [] 0 [] drIdMember h0 rfl (fun _ hx => nomatch hx))
    (HasTy.const [] 1 [] drFamMember h1 rfl (fun _ hx => nomatch hx))

def drMkView (E : ResolvedEnv) (h0 : E.members 0 = some drIdMember) (h1 : E.members 1 = some drFamMember) :
    PolicyConstructorView E (drFamView E h1) drMkMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [drField]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlt : j.val < 1 := j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simpa [hj, policyPrefixContext] using drFieldTy E h0 h1
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

theorem drMkBefore : CtorBeforeRecursors drFamEnv drMkMember := by
  refine ⟨1, rfl, ?_⟩
  intro rr rm hm hk _
  rw [drFamEnv_members] at hm
  by_cases h1 : rr = 1
  · rw [if_pos h1] at hm
    cases hm
    exact absurd hk (by decide)
  · by_cases h0 : rr = 0
    · rw [if_neg h1, if_pos h0] at hm
      cases hm
      exact absurd hk (by decide)
    · rw [if_neg h1, if_neg h0] at hm
      cases hm

theorem drMkContig : CtorContiguous drFamEnv 2 drMkMember := by
  refine ⟨1, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd hr (by omega)
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [drFamEnv_members] at hm
    by_cases h1 : c = 1
    · rw [if_pos h1] at hm
      cases hm
      exact absurd hc (by decide)
    · by_cases h0 : c = 0
      · rw [if_neg h1, if_pos h0] at hm
        cases hm
        exact absurd hc (by decide)
      · rw [if_neg h1, if_neg h0] at hm
        cases hm

theorem drMkUniverse (E : ResolvedEnv) (h0 : E.members 0 = some drIdMember)
    (h1 : E.members 1 = some drFamMember) : FieldUniverseAdmitted (drMkView E h0 h1) := by
  intro j
  have hlt : j.val < 1 := j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem drMkFields (E : ResolvedEnv) (h0 : E.members 0 = some drIdMember)
    (h1 : E.members 1 = some drFamMember)
    (hfa : fieldAnalyze E 8 1 0 0 0 0 drField = .permitted (.recursive 0) []) :
    CtorFieldsPermitted (drMkView E h0 h1) := by
  intro j
  have hlt : j.val < 1 := j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact ⟨.recursive 0, 8, [], hfa⟩

def drFamAdmitted : IndGroupAdmitted drBase 1 drFamMember :=
  .family rfl (drFamView drFamEnv rfl) rfl rfl (Or.inr uniformType_succ_zero)

def drMkAdmitted : IndGroupAdmitted drFamEnv 2 drMkMember :=
  .constructor (drFamView drFamEnv rfl) (drMkView drFamEnv rfl rfl) rfl drMkBefore drMkContig
    (drMkUniverse _ rfl rfl) (drMkFields _ rfl rfl rfl)

def drGroupAdmitted : RecursorEliminationAdmitted drMkEnv 3 drRecMember where
  family := drFamView drMkEnv rfl
  constructors := [drMkMember]
  constructorViews
    | ⟨0, _⟩ => drMkView drMkEnv rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [drMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

theorem drCensus : CtorCensus drMkEnv 1 3 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, _⟩
    rw [drMkEnv_members] at hc
    by_cases h2 : c = 2
    · exact ⟨by omega, by omega⟩
    · by_cases h1 : c = 1
      · rw [if_neg h2, if_pos h1] at hc
        cases hc
        exact absurd hk (by decide)
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hc
          cases hc
          exact absurd hk (by decide)
        · rw [if_neg h2, if_neg h1, if_neg h0] at hc
          cases hc
  · intro h
    have hc : c = 2 := by omega
    subst hc
    exact ⟨drMkMember, rfl, rfl, rfl⟩

/-- THE DERIVED MINOR (05 §12) reads the field after δ and β: its induction hypothesis is `motive x`. -/
theorem drMinor_derived : derivedMinor drGroupAdmitted ⟨0, by decide⟩ 8 [.recursive 0] = some drMinorTy :=
  rfl

theorem drMinorMatch : MinorPremisesMatch drGroupAdmitted := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.recursive 0], 8, rfl, rfl⟩

/-- the equation's context: `x : Id F`, the minor, the motive. -/
def drIotaCtx : LCtx := [.assumption drField, .assumption drMinorTy, .assumption drMotiveTy]

/-- the schema admission derives (05 §14): `minor x (rec motive minor x)`. -/
def drSchema : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) (foldApps (.const 3 [.param 0]) [.bvar 2, .bvar 1, .bvar 0])

/-- the schema read off the stored type's spine, as before step 0: `minor x (rec motive minor F x)`. -/
def drSchemaStored : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) (foldApps (.const 3 [.param 0]) [.bvar 2, .bvar 1, .const 1 [], .bvar 0])

/-- the equation's type: `motive (mk x)`. -/
def drEqTy : Expr Nat := .app (.bvar 2) (.app (.const 2 []) (.bvar 0))

theorem drSchema_derived : iotaSchemaAt drGroupAdmitted ⟨0, by decide⟩ 8 [.recursive 0] = some drSchema :=
  rfl

theorem drEquation_shape :
    equationDoms drGroupAdmitted ⟨0, by decide⟩ = some [drMotiveTy, drMinorTy, drField] ∧
    iotaEquationType drGroupAdmitted ⟨0, by decide⟩ = drEqTy := ⟨rfl, rfl⟩

/-- `Id F` converts to `F` in the untyped judgment: δ at `Id`, then β. -/
def drConvLegacy (Γ : LCtx) : Conv drEnv 1 Γ drField (.const 1 []) :=
  .trans _ _ (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.const 1 [])) _
    (.app _ _ _ _ _ (.step _ _ _ (.delta _ 0 [] drIdMember _ rfl rfl rfl)) (.refl _ _))
    (.step _ _ _ (.beta _ _ _ _))

/-- the recursor's head, in the untyped judgment. -/
def drRecHead : HasTy drEnv 1 drIotaCtx (.const 3 [.param 0]) drRecTy :=
  HasTy.const _ 3 [.param 0] drRecMember rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

/-- the equation in the untyped judgment, as admission's clause asks: the recursive call's major converted
    from `Id F` to `F`. -/
def drIotaTyLegacy : HasTy drEnv 1 drIotaCtx drSchema drEqTy := by
  have hMot : HasTy drEnv 1 drIotaCtx (.bvar 2) drMotiveTy := HasTy.bvar _ 2 _ rfl
  have hMin : HasTy drEnv 1 drIotaCtx (.bvar 1) (lift 0 2 drMinorTy) := HasTy.bvar _ 1 _ rfl
  have hX : HasTy drEnv 1 drIotaCtx (.bvar 0) drField := HasTy.bvar _ 0 _ rfl
  have hXF : HasTy drEnv 1 drIotaCtx (.bvar 0) (.const 1 []) := HasTy.conv _ _ _ _ hX (drConvLegacy _)
  have h1 := HasTy.app _ _ _ _ _ drRecHead hMot
  have h2 := HasTy.app _ _ _ _ _ h1 hMin
  have h3 := HasTy.app _ _ _ _ _ h2 hXF
  have h4 := HasTy.app _ _ _ _ _ hMin hX
  exact HasTy.app _ _ _ _ _ h4 h3

def drIotaLegacy : IotaEquationTyped drGroupAdmitted ⟨0, by decide⟩ 8 [.recursive 0] := by
  unfold IotaEquationTyped
  rw [drEquation_shape.1, drSchema_derived]
  exact drIotaTyLegacy

def drIotaClause : IotaDescriptorClause drMkEnv drGroupAdmitted where
  signatureOnly := rfl
  shapesAt := fun _ => [.recursive 0]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => drIotaLegacy

def drGroupRecursor : IndGroupAdmitted drMkEnv 3 drRecMember :=
  .recursor drGroupAdmitted rfl drCensus
    (fun i => match i with | ⟨0, _⟩ => drMkUniverse _ rfl rfl)
    (fun i => match i with | ⟨0, _⟩ => drMkFields _ rfl rfl rfl)
    drMinorMatch drIotaClause

/-! ## (3) `main`'s ι has no rule here -/

/-- `main`'s ι reads `mk`'s field as written and gives it no kind (R-NoFunRec-0, R-NoDeltaRec). -/
theorem drMk_noKind : analyzeFields 1 [drField] = none := rfl

/-- So no ι witness names this recursor: its family is `F` at `1`, its one constructor `mk`, whose field
    has no kind. The recursor's index admission holds with no case. -/
def drRecIdxAdmitted : RecursorGroupIdxAdmitted drMkEnv 3 drRecMember where
  typing := fun {E'} hext _ w hr _ => by
    exfalso
    have hrecIdx := w.hrecIdx
    rw [hr] at hrecIdx
    have hidx := w.hidx
    have hfam := w.hfam
    have hfamK := w.hfamK
    by_cases hf0 : w.familyRef = 0
    · rw [hf0, hext 0 drIdMember rfl] at hfam
      rw [← Option.some.inj hfam] at hfamK
      exact absurd hfamK (by decide)
    · have hf1 : w.familyRef = 1 := by omega
      have hk0 : w.ctorIdx = 0 := by omega
      rw [hf1, hext 1 drFamMember rfl] at hfam
      have hfm : w.famMember = drFamMember := (Option.some.inj hfam).symm
      have hc2 : w.ctorRef = 2 := by have := w.hctorIdx; omega
      have hctor := w.hctor
      rw [hc2, hext 2 drMkMember rfl] at hctor
      have hcm : w.ctorMember = drMkMember := (Option.some.inj hctor).symm
      have hnidx := w.hnidx
      rw [hfm] at hnidx
      have hnp : w.nparams = 0 := by
        have h0 : piCount drFamMember.mtype = 0 := rfl
        omega
      have hlen1 : w.nparams + w.fields.length = 1 := by
        rw [w.hnpar, hcm]; rfl
      have hpeel := w.hpeel
      rw [hlen1, hcm] at hpeel
      have hpeel' : (some ([drField], Expr.const 1 []) : Option (List (Expr Nat) × Expr Nat)) =
          some (w.ctorDoms, w.ctorResult) := hpeel
      have hdoms : [drField] = w.ctorDoms := (Prod.mk.inj (Option.some.inj hpeel')).1
      have hkinds := w.hkinds
      rw [hf1, ← hdoms, hnp] at hkinds
      exact absurd hkinds (by rw [List.drop_zero, drMk_noKind]; exact fun h => Option.noConfusion h)

/-! ## (4) the typed environment judgment admits it -/

/-- `Id` typed: its type at `Sort (imax 2 2)`, its body at its type. -/
def drBaseWfT : EnvWfT drBase :=
  .definition emptyEnv 0 _ _ (.imax (.succ (.succ .zero)) (.succ (.succ .zero))) .empty rfl
    (.pi [] _ _ _ _ (.sort [] _) (.sort _ _))
    (.lam [] _ (.succ (.succ .zero)) (.bvar 0) _ (.sort [] _) (.bvar _ 0 _ rfl))
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- the field at `Sort 1` in the typed judgment: `Id` applied to `F`, no conversion. -/
def drFieldTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h0 : E.members 0 = some drIdMember)
    (h1 : E.members 1 = some drFamMember) : HasTyT E n Γ drField (.sort (.succ .zero)) :=
  .app Γ (.const 0 []) (.const 1 []) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.const Γ 0 [] drIdMember h0 rfl rfl) (.const Γ 1 [] drFamMember h1 rfl rfl)

def drMkTyT : HasTyT drFamEnv 0 [] drMkMember.mtype (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] drField (.succ .zero) (.const 1 []) (.succ .zero) (drFieldTyT rfl rfl)
    (.const _ 1 [] drFamMember rfl rfl rfl)

/-- the recursor type's sort, as the conversion checker reads it. -/
def drRecSortU : Level :=
  .imax (.imax (.succ .zero) (.succ (.param 0)))
    (.imax (.imax (.succ .zero) (.imax (.param 0) (.param 0))) (.imax (.succ .zero) (.param 0)))

/-- the recursor's stored type is typed only with conversion: its minor applies the motive to `x : Id F`. -/
theorem drRecTy_check :
    inferC drMkEnv 1 8 [] drRecTy = some (.sort drRecSortU) ∧ inferT drMkEnv 1 [] drRecTy = none :=
  ⟨rfl, rfl⟩

def drRecTyT : HasTyT drMkEnv 1 [] drRecTy (.sort drRecSortU) :=
  (tyAtC drMkEnv 1 8 [] drRecTy (.sort drRecSortU)).get rfl

theorem drMkTypedE (E : ResolvedEnv) (h0 : E.members 0 = some drIdMember)
    (h1 : E.members 1 = some drFamMember) : CtorTypedT (drMkView E h0 h1) :=
  ⟨fun i => match i with | ⟨0, _⟩ => ⟨drFieldTyT h0 h1⟩, fun i => i.elim0⟩

theorem drFamTyped : IndGroupTypedT drFamAdmitted := fun i => i.elim0

theorem drMkTyped : IndGroupTypedT drMkAdmitted := ⟨fun i => i.elim0, drMkTypedE _ rfl rfl⟩

/-- the recursor's typed content, with its ι equation typed in `HasTyT` by the conversion checker. -/
theorem drRecTyped : IndGroupTypedT drGroupRecursor :=
  ⟨fun i => i.elim0, fun i => match i with | ⟨0, _⟩ => drMkTypedE _ rfl rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 8 Γ e T) rfl⟩

def drMembersT :
    GroupMembersT drFamEnv drBase [(1, drFamMember), (2, drMkMember), (3, drRecMember)] drEnv :=
  .cons _ 1 drFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    drFamAdmitted PUnit.unit _ (.sort [] (.succ .zero)) (fun h => absurd h (by decide))
    drFamTyped
    (.cons _ 2 drMkMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      drMkAdmitted PUnit.unit _ drMkTyT (fun _ => ⟨drMkTyT⟩) drMkTyped
      -- R-NoFunRec-1 B2 (step 2d-2b): the legacy `drRecIdxAdmitted` above was VACUOUS — `main`'s ι
      -- has no witness naming this recursor (`drMk_noKind`). The typed obligation is real coverage:
      -- the canonical `IotaWitnessS` for the δ-reached `Id F` field, built by `ofCheck`.
      (.cons _ 3 drRecMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        drGroupRecursor (.ofCheck _ _ (by with_unfolding_all rfl)) _ drRecTyT (fun h => absurd h (by decide))
        drRecTyped (.nil _)))

/-- `Id`, then `F`, `mk` and `F.rec` as ONE group step: the typed environment judgment admits a group
    whose recursive field is reached only through δ. -/
def drEnvWfT : EnvWfT drEnv :=
  .group drBase 1 drFamMember [(2, drMkMember)] 3 drRecMember drEnv drBaseWfT
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT

theorem pin_envWfT_deltaRec : Nonempty (EnvWfT drEnv) := ⟨drEnvWfT⟩

/-! ## (5) the typed check, at the right schema and at the stored type's -/

/-- the typed equation needs the conversion `Id F ≡ F`: the syntactic checker refuses it, and the
    conversion checker types it. -/
theorem drIota_needs_conversion :
    (synCheck drEnv 1 drIotaCtx drSchema drEqTy).isSome = false ∧
    (tyAtC drEnv 1 8 drIotaCtx drSchema drEqTy).isSome = true := ⟨rfl, rfl⟩

/-- TOOTH: at the schema read off the stored type, the conversion checker refuses the equation. The
    recursive call applies the recursor to `F : Sort 1` where its major `F` is due. -/
theorem drIota_stored_refused : tyAtC drEnv 1 8 drIotaCtx drSchemaStored drEqTy = none := rfl

/-- the untyped judgment types the stored type's schema at the equation's type. Two retypings through its
    total conversion (`retypeAny`) carry it: `F : Sort 1` is retyped at `F`, the major's domain, and the
    call's type `motive F` at `Id F → motive x`, so that it takes `x`. This is why admission's clause,
    typed there, could not refuse the schema. -/
def drIota_stored_legacy : HasTy drEnv 1 drIotaCtx drSchemaStored drEqTy := by
  have hMot : HasTy drEnv 1 drIotaCtx (.bvar 2) drMotiveTy := HasTy.bvar _ 2 _ rfl
  have hMin : HasTy drEnv 1 drIotaCtx (.bvar 1) (lift 0 2 drMinorTy) := HasTy.bvar _ 1 _ rfl
  have hX : HasTy drEnv 1 drIotaCtx (.bvar 0) drField := HasTy.bvar _ 0 _ rfl
  have hF : HasTy drEnv 1 drIotaCtx (.const 1 []) (.const 1 []) :=
    UntypedConvCollapse.retypeAny (HasTy.const _ 1 [] drFamMember rfl rfl (fun _ hx => nomatch hx)) _
  have h1 := HasTy.app _ _ _ _ _ drRecHead hMot
  have h2 := HasTy.app _ _ _ _ _ h1 hMin
  have h3 := HasTy.app _ _ _ _ _ h2 hF
  have h3' := UntypedConvCollapse.retypeAny h3 (.pi drField (.app (.bvar 3) (.bvar 0)))
  have h4 := HasTy.app _ _ _ _ _ h3' hX
  have h5 := HasTy.app _ _ _ _ _ hMin hX
  exact HasTy.app _ _ _ _ _ h5 h4

/-! ## (6) outside the copy's scope -/

/-- R-NoDeltaRec-4b: the reader now SEES the δ-reached field — `mk`'s `Id F` field reads
    `.drecD (Id F) []` under the conversion checker, where the syntactic spine alone used to read
    none (and the plain fallback read nothing, `F` absent from the base). `synChecker` still reads
    no skeleton — it cannot type the recursor's domains (the same `Id F ≡ F` conversion
    `drIota_needs_conversion` shows). The produced skeleton passes the scope test
    (`drecDsCheckB`, -4c) — `dr_skel_scope_admitted` — and fails the bridge's `hsnd` —
    `dr_skel_bridge_refused`. -/
theorem dr_reader_sees_drecD :
    groupSkel? synChecker drBase 8 1 drFamMember [(2, drMkMember)] drRecMember 0 = none ∧
    (groupSkel? (convChecker 8) drBase 8 1 drFamMember [(2, drMkMember)] drRecMember 0).map
      (fun sk => sk.ctors.map CtorSkelT.fields) = some [[.drecD drField []]] := ⟨rfl, rfl⟩

/-- and the produced skeleton now PASSES the scope test (R-NoDeltaRec-4c): `drecDsCheckB`
    certifies `Id F`'s typing at the family's sort in the family scope and its conversion to the
    family application — evidence `-4d-iii` threads through `annFieldsTyT`'s `drecD` arm into
    `CtorCopyA.drecD_typed` (`hsnd` still gates the group out of the `envBridge` scope). -/
theorem dr_skel_scope_admitted :
    ∀ sk, groupSkel? (convChecker 8) drBase 8 1 drFamMember [(2, drMkMember)] drRecMember 0 = some sk →
      groupCheckB (convChecker 8) drBase 1 drFamMember [(2, drMkMember)] 3 drRecMember sk = true := by
  intro sk hsk
  obtain rfl := Option.some.inj hsk
  rfl

/-- the bridge-side gate refuses the same skeleton: `hsnd` needs no `drecD` field. R-NoDeltaRec-4d-iii
    keeps the gate (`GroupInScopeT.hsnd`, the `EnvNormEraseA` boundary), so this is still a refusal. -/
theorem dr_skel_bridge_refused :
    ∀ sk, groupSkel? (convChecker 8) drBase 8 1 drFamMember [(2, drMkMember)] drRecMember 0 = some sk →
      ¬ ∀ k ∈ sk.ctors, ∀ d ∈ k.fields, d.isDrecD = false := by
  intro sk hsk
  obtain rfl := Option.some.inj hsk
  decide

/-! ## (7) the `.drecD` cell on the IA-021 checker route

`drRecTyT` pays `GroupMembersT.cons`'s `hT` for the recursor by one whole-type checker
leaf.  The admission-derived route of #6517 (`RcicIARecTyped`) discharges the same
premise compositionally: `IA021T_recursor_typed` glues the family telescope (vacuous —
`F` has no parameters or indices), the motive, the tail, and `MinorDomainsTyped` — here
paid by `IA021T_minorDomains_of_check`'s per-minor `sortTyAtC` leaves, not hand-built.

The `.drecD` content is exactly what the leaf exercises: the stored minor
`Π (x : Id F), motive x → motive (mk x)` types in its minor context ONLY because the
conversion checker's δ-step folds `Id F` to `F` at the `motive x` domain — the
conversion `drIota_needs_conversion` isolates at the ι equation.  The conv-aware cell
(`IA019T_admitted_minor_typed_conv`, `RcicIARecIH`) is not applied: its `hW.InScope`/
`hW.ScopeCheck` debts are the copy-scope gates `hsnd`/`groupCheckB` keeps `.drecD`
groups out of (`dr_skel_bridge_refused`), and no `EnvWfT` derivation of this env
carries them.  `drMk_drecDTyped` below pays the `DrecDTypedT` evidence the cell's
`hdd` premise would consume. -/

/-- the typed family view over the `.drecD` group: `F : Sort 1`, no parameters or
    indices. -/
def drFamViewT : FamViewT drFamMember where
  params := []
  indices := []
  sort := .succ .zero
  stored := rfl
  profile := Or.inr uniformType_succ_zero

/-- the field walk's typed content: `.drecD drField []`'s index spine is empty, and so
    is the remainder. -/
def drFieldsTyT : FieldsTyT drMkEnv drFamMember.arity
    (fun k => lift 0 k drFamViewT.idxTel) (telCtxT drFamViewT.params) 0
    [.drecD drField []] [] :=
  .drecD [] 0 drField [] [] [] (.nil _) (.nil [] 0 [] (.nil _))

/- `Id F` converts to the family application `F` under the family alone — the
   `TyConvT` the `.drecD` evidence carries (`drecDsCheckB`'s `conv` leaf, paid at the
   same fuel the scope test used). -/
kernel_rfl_theorem drDrecD_conv :
    ((convChecker 96).conv (extendEnv drMkEnv 1 drFamMember) 0 [] drField
      (.const 1 [])).isSome = true

/-- `DrecDTypedT` at the `.drecD drField []` field: the surface domain `Id F` types at
    `Sort 1` in the family's scope and converts to the family application there; the
    index side is vacuous (`drField` carries no analyzed index). -/
theorem drMk_drecDTyped :
    DrecDTypedT drMkEnv 1 drFamMember drFamViewT [.drecD drField []] := by
  intro fsPre D idx fsRest h
  cases fsPre with
  | nil =>
      simp only [List.nil_append, List.cons.injEq, FieldT.drecD.injEq, List.nil_eq] at h
      obtain ⟨⟨hD, hidx⟩, -⟩ := h
      subst hD; subst hidx
      refine ⟨⟨drFieldTyT rfl rfl⟩, ?_, fun x hx => nomatch hx⟩
      exact ⟨((convChecker 96).conv _ _ _ _ _).get drDrecD_conv⟩
  | cons p ps =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact absurd (List.append_eq_nil.mp h.2.symm).2 (List.cons_ne_nil _ _)

/- the `.drecD` minor's checker leaf: the stored minor `Π (x : Id F), motive x →
   motive (mk x)` sort-typed in its minor context — its `motive x` domain types only
   through the `Id F ≡ F` conversion. -/
kernel_rfl_theorem drMinorChk0 :
    (sortTyAtC drMkEnv drRecMember.arity 96 (minorCtxT drGroupAdmitted 0)
      (drGroupAdmitted.minorTypes[0]'(by
        have : drGroupAdmitted.minorTypes.length = 1 := rfl; omega))).isSome = true

/-- the per-minor leaves packaged for `IA021T_minorDomains_of_check`. -/
def drMinorChk : ∀ i : Fin drGroupAdmitted.minorTypes.length,
    (sortTyAtC drMkEnv drRecMember.arity 96 (minorCtxT drGroupAdmitted i.val)
      (drGroupAdmitted.minorTypes[i.val])).isSome = true
  | ⟨0, _⟩ => drMinorChk0
  | ⟨k+1, h⟩ => absurd h (by
      have : drGroupAdmitted.minorTypes.length = 1 := rfl; omega)

/-- the checker-paid `MinorDomainsTyped` for the `.drecD` group: the one premise of
    `IA021T_recursor_typed` admission's typed content does not itself pay
    (`[admission_minorTypes_untyped]`), here discharged per-minor by `sortTyAtC`. -/
def drMinorDomains : MinorDomainsTyped drGroupAdmitted :=
  IA021T_minorDomains_of_check drGroupAdmitted 96 drMinorChk

/-- `drMkEnv` — the env the admission record is checked at — is closed: it is
    `drEnv`'s fresh-extension prefix. -/
theorem drMkEnvClosed : EnvClosed drMkEnv :=
  envClosed_of_extend_fresh (envClosed_of_envWfT drEnvWfT) rfl

/-- the family telescope premise at the `.drecD` cell: `F` has no parameters or
    indices, so the data premise is vacuous. -/
def drFamTel : FamilyTelTypedT (drFamView drMkEnv rfl) :=
  ⟨fun i => absurd i.isLt (by
    have h : ((drFamView drMkEnv rfl).parameters ++
      (drFamView drMkEnv rfl).indices).length = 0 := rfl
    omega)⟩

/-- PIN (IA-021T composite at the `.drecD` group): the stored recursor type typed from
    admission plus the checker-paid minor domains — the `GroupMembersT.cons` `hT`
    premise, derived rather than leaf-checked. -/
def pin_IA021T_drRec : Σ' u, HasTyT drMkEnv drRecMember.arity [] drRecTy (.sort u) :=
  IA021T_recursor_typed drGroupAdmitted drMkEnvClosed drFamTel drMinorDomains

-- SECOND INSTRUMENT: the composite's sort agrees with the whole-type leaf's
-- `drRecSortU` — the admission-derived and checker routes produce the same `u`.
kernel_rfl_theorem pin_IA021T_drRec_agree :
    pin_IA021T_drRec.1 = drRecSortU

/-- the composite's derivation slots into `GroupMembersT.cons`'s `hT` premise: the
    whole group membership rebuilt with the admission-derived typing in place of the
    hand leaf `drRecTyT`. -/
def drMembersT_ofComposite :
    GroupMembersT drFamEnv drBase [(1, drFamMember), (2, drMkMember), (3, drRecMember)]
      drEnv :=
  .cons _ 1 drFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    drFamAdmitted PUnit.unit _ (.sort [] (.succ .zero)) (fun h => absurd h (by decide))
    drFamTyped
    (.cons _ 2 drMkMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      drMkAdmitted PUnit.unit _ drMkTyT (fun _ => ⟨drMkTyT⟩) drMkTyped
      (.cons _ 3 drRecMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        drGroupRecursor (.ofCheck _ _ (by with_unfolding_all rfl)) _ pin_IA021T_drRec.2
        (fun h => absurd h (by decide)) drRecTyped (.nil _)))

/-- the full environment judgment with the composite derivation at the recursor's
    premise — the `.drecD` group's `GroupMembersT.cons` discharged without the
    whole-type leaf. -/
def drEnvWfT_ofComposite : EnvWfT drEnv :=
  .group drBase 1 drFamMember [(2, drMkMember)] 3 drRecMember drEnv drBaseWfT
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl drMembersT_ofComposite

end Rcic.Declarative

#print axioms Rcic.Declarative.drFamViewT
#print axioms Rcic.Declarative.drFieldsTyT
#print axioms Rcic.Declarative.drDrecD_conv
#print axioms Rcic.Declarative.drMk_drecDTyped
#print axioms Rcic.Declarative.drMinorChk0
#print axioms Rcic.Declarative.drMinorChk
#print axioms Rcic.Declarative.drMinorDomains
#print axioms Rcic.Declarative.drMkEnvClosed
#print axioms Rcic.Declarative.drFamTel
#print axioms Rcic.Declarative.pin_IA021T_drRec
#print axioms Rcic.Declarative.pin_IA021T_drRec_agree
#print axioms Rcic.Declarative.drMembersT_ofComposite
#print axioms Rcic.Declarative.drEnvWfT_ofComposite

#print axioms Rcic.Declarative.dr_fieldAnalyze
#print axioms Rcic.Declarative.dr_storedReading
#print axioms Rcic.Declarative.dr_analyzedReading
#print axioms Rcic.Declarative.drMinor_derived
#print axioms Rcic.Declarative.drMinorMatch
#print axioms Rcic.Declarative.drSchema_derived
#print axioms Rcic.Declarative.drGroupRecursor
#print axioms Rcic.Declarative.drMk_noKind
#print axioms Rcic.Declarative.drRecIdxAdmitted
#print axioms Rcic.Declarative.drRecTy_check
#print axioms Rcic.Declarative.drRecTyped
#print axioms Rcic.Declarative.drEnvWfT
#print axioms Rcic.Declarative.pin_envWfT_deltaRec
#print axioms Rcic.Declarative.drIota_needs_conversion
#print axioms Rcic.Declarative.drIota_stored_refused
#print axioms Rcic.Declarative.drIota_stored_legacy
#print axioms Rcic.Declarative.dr_reader_sees_drecD
#print axioms Rcic.Declarative.dr_skel_scope_admitted
#print axioms Rcic.Declarative.dr_skel_bridge_refused
