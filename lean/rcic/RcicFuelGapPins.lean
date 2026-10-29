import rcic.RcicAnnIotaCorrD
import rcic.RcicTypedDeltaRecPins

/-!
# S3 — `fgEnv`: the fuel gap (cc LAND #6611, universal-discharge measurement)

S2's D-arm admitted the `.drecD` field `Id F` at `drEnv` by normalizing the
stored telescope with `domsFuelBound` — a bound proportional to the domains'
own size (`esize + piCount + 2` each).  The witness's semantic analysis runs
at `w.fuel`, an arbitrary bound the witness carries.  The two budgets can
diverge: a δ-chain whose unfold depth exceeds its surface size leaves the
domain under-normalized inside the recognizer, while `fieldShapesFuel` /
`iotaOpenRhs` (at `w.fuel`) read it fully.  `fgEnv` is that env.

Members: `Id` at `0` (transparent, as `drEnv`'s), `D2` at `1` —
`D2 T := Id (Id T)`, a definition whose δ-unfold chain is deeper than its
size suggests — then the group `G` at `2`, `mk : Π (x : D2 G), G` at `3`,
`G.rec` at `4` (same signature shape as `drEnv`'s).

Measured:

- `fieldShapesFuel fgEnv 40 2 0 0 0 0 [D2 G] = some [.recursive 0]` — the
  canonical analysis at `w.fuel = 40` reads the field recursive.
- `domsFuelBound [D2 G] = 5`, but `whnfFuel` needs `7` on `D2 G` — the
  recognizer's normalized-telescope walk leaves the domain unnormalized:
  `telWhnfDom … = Π (x : D2 G), G`.
- `recCallField` on the unnormalized `D2 G` extracts `familyIdx 0 (D2 G)
  = [G]` — the def's spine argument — emitting `rec P m G x`; `iotaOpenRhs`
  at `w.fuel` emits `rec P m x`.  The decided schema/RHS agreement fails on
  BOTH arms (`directFragCheck`'s `noTransparentB` rejects `D2`'s transparent
  head anyway), so `iotaWitnessSAnnDB fgEnv wFg = false`.
- `EnvWfT fgEnv` holds (same admission shape as `drEnvWfT`, ported), and
  `wFg.shapes = [.recursive 0]` — no function-recursive shape, so `fgEnv`
  is outside the S6 `.frec` gate.

Hence `EnvCorrAnnDU` is **not** derivable from `EnvWfT` outside the frec
gate: the universal discharge `∀ E, EnvWfT E → EnvCorrAnnDU E` (restricted
to non-`.recursive (_+1)` shape space) is refuted by a sealed counterexample.
The failure is a FUEL BOUND, not a shape-class failure: `telWhnfDom`'s
budget is a function of the stored domain's size, while δ-depth is a
property of the environment's definition chain.  A recognizer whose
normalization budget is the witness's own `w.fuel` (or a bound proved to
cover the env's δ-depth) would be the next arm; that is a different
declaration, not this pin.

ι subject reduction still holds at `fgEnv` (`fgIotaSR_lhs`/`fgIotaSR_rhs`) —
the certificate is the failure, as at `drEnv` and `vecOnlyEnvU`.

`closure_claim` stays 0.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the environment -/

/-- `Id : Sort 1 → Sort 1 := λ A, A` at `0` — `drEnv`'s member reused. -/
def fgIdMember : CheckedMember := drIdMember

/-- `D2 : Sort 1 → Sort 1 := λ T, Id (Id T)` at `1` — the chain member:
    whnf needs ~3 steps per `Id` layer, while `domsFuelBound` sees only the
    surface application. -/
def fgD2Body : Expr Nat :=
  .lam (.sort (.succ .zero)) (.app (.const 0 []) (.app (.const 0 []) (.bvar 0)))
def fgD2Member : CheckedMember :=
  ⟨.definitionM, 0, .pi (.sort (.succ .zero)) (.sort (.succ .zero)), some fgD2Body⟩

/-- `G : Sort 1` at `2`. -/
def fgFamMember : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩

/-- the field `D2 G`. -/
def fgField : Expr Nat := .app (.const 1 []) (.const 2 [])

/-- `mk : D2 G → G` at `3`. -/
def fgMkMember : CheckedMember := ⟨.constructorM, 0, .pi fgField (.const 2 []), none⟩

/-- the motive `Π (x : G), Sort (param 0)`. -/
def fgMotiveTy : Expr Nat := .pi (.const 2 []) (.sort (.param 0))

/-- the minor `Π (x : D2 G), motive x → motive (mk x)`. -/
def fgMinorTy : Expr Nat :=
  .pi fgField (.pi (.app (.bvar 1) (.bvar 0)) (.app (.bvar 2) (.app (.const 3 []) (.bvar 1))))

/-- `G.rec` at `4`, same signature shape as `drEnv`'s `F.rec`. -/
def fgRecTy : Expr Nat :=
  .pi fgMotiveTy (.pi fgMinorTy (.pi (.const 2 []) (.app (.bvar 2) (.bvar 0))))
def fgRecMember : CheckedMember := ⟨.recursorM, 1, fgRecTy, none⟩

def fgB0 : ResolvedEnv := extendEnv emptyEnv 0 fgIdMember
def fgB1 : ResolvedEnv := extendEnv fgB0 1 fgD2Member
def fgFamEnv : ResolvedEnv := extendEnv fgB1 2 fgFamMember
def fgMkEnv : ResolvedEnv := extendEnv fgFamEnv 3 fgMkMember
def fgEnv : ResolvedEnv := extendEnv fgMkEnv 4 fgRecMember

theorem fgB1_members (c : Nat) :
    fgB1.members c = if c = 1 then some fgD2Member else if c = 0 then some fgIdMember else none :=
  rfl

theorem fgFamEnv_members (c : Nat) :
    fgFamEnv.members c = if c = 2 then some fgFamMember else
      if c = 1 then some fgD2Member else if c = 0 then some fgIdMember else none :=
  rfl

theorem fgMkEnv_members (c : Nat) :
    fgMkEnv.members c = if c = 3 then some fgMkMember else
      if c = 2 then some fgFamMember else if c = 1 then some fgD2Member
      else if c = 0 then some fgIdMember else none := rfl

/-! ## (2) the fuel gap, measured -/

/-- the recognizer's normalization budget for `[D2 G]` — domain-size bound. -/
theorem fg_domsBound : domsFuelBound [fgField] = 5 := rfl

/-- … which cannot cover the two-layer `Id` chain: `whnfFuel` exhausts at 5
    and 6, succeeding only at 7. -/
theorem fg_whnfFuel_bound_low : (whnfFuel fgB1 5 fgField).isSome = false := rfl
theorem fg_whnfFuel_bound_six : (whnfFuel fgB1 6 fgField).isSome = false := rfl
theorem fg_whnfFuel_bound_ok : (whnfFuel fgB1 7 fgField).isSome = true := rfl

/-- the canonical analysis at the witness's fuel reads `.recursive 0`. -/
theorem fg_fieldAnalyze : fieldAnalyze fgFamEnv 40 2 0 0 0 0 fgField =
    .permitted (.recursive 0) [] := rfl

/-- the stored domain's spine names `D2`'s argument `G` as an index. -/
theorem fg_storedReading : familyIdx 0 fgField = [.const 2 []] := rfl

/-- admission's reading after δ+β: the family `G`, no binder. -/
theorem fg_analyzedReading : piTelescopeFuel fgFamEnv 40 fgField =
    some ([], .const 2 []) := rfl

/-! ## (3) admission reads the field as the analysis does -/

def fgFamView (E : ResolvedEnv) (h : E.members 2 = some fgFamMember) : PolicyFamilyView E where
  ref := 2
  member := fgFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

/-- the field at `Sort 1` in the untyped judgment: `D2` applied to `G`. -/
def fgFieldTy (E : ResolvedEnv) (h1 : E.members 1 = some fgD2Member)
    (h2 : E.members 2 = some fgFamMember) : HasTy E 0 [] fgField (.sort (.succ .zero)) :=
  HasTy.app [] (.const 1 []) (.const 2 []) (.sort (.succ .zero)) (.sort (.succ .zero))
    (HasTy.const [] 1 [] fgD2Member h1 rfl (fun _ hx => nomatch hx))
    (HasTy.const [] 2 [] fgFamMember h2 rfl (fun _ hx => nomatch hx))

def fgMkView (E : ResolvedEnv) (h1 : E.members 1 = some fgD2Member)
    (h2 : E.members 2 = some fgFamMember) :
    PolicyConstructorView E (fgFamView E h2) fgMkMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [fgField]
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
      simpa [hj, policyPrefixContext] using fgFieldTy E h1 h2
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

theorem fgMkBefore : CtorBeforeRecursors fgFamEnv fgMkMember := by
  refine ⟨2, rfl, ?_⟩
  intro rr rm hm hk _
  rw [fgFamEnv_members] at hm
  by_cases h2 : rr = 2
  · rw [if_pos h2] at hm
    cases hm
    exact absurd hk (by decide)
  · by_cases h1 : rr = 1
    · rw [if_neg h2, if_pos h1] at hm
      cases hm
      exact absurd hk (by decide)
    · by_cases h0 : rr = 0
      · rw [if_neg h2, if_neg h1, if_pos h0] at hm
        cases hm
        exact absurd hk (by decide)
      · rw [if_neg h2, if_neg h1, if_neg h0] at hm
        cases hm

theorem fgMkContig : CtorContiguous fgFamEnv 3 fgMkMember := by
  refine ⟨2, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd hr (by omega)
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    rw [fgFamEnv_members] at hm
    by_cases h2 : c = 2
    · rw [if_pos h2] at hm
      cases hm
      exact absurd hc (by decide)
    · by_cases h1 : c = 1
      · rw [if_neg h2, if_pos h1] at hm
        cases hm
        exact absurd hc (by decide)
      · by_cases h0 : c = 0
        · rw [if_neg h2, if_neg h1, if_pos h0] at hm
          cases hm
          exact absurd hc (by decide)
        · rw [if_neg h2, if_neg h1, if_neg h0] at hm
          cases hm

theorem fgMkUniverse (E : ResolvedEnv) (h1 : E.members 1 = some fgD2Member)
    (h2 : E.members 2 = some fgFamMember) : FieldUniverseAdmitted (fgMkView E h1 h2) := by
  intro j
  have hlt : j.val < 1 := j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem fgMkFields (E : ResolvedEnv) (h1 : E.members 1 = some fgD2Member)
    (h2 : E.members 2 = some fgFamMember)
    (hfa : fieldAnalyze E 40 2 0 0 0 0 fgField = .permitted (.recursive 0) []) :
    CtorFieldsPermitted (fgMkView E h1 h2) := by
  intro j
  have hlt : j.val < 1 := j.isLt
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  rw [hj]
  exact ⟨.recursive 0, 40, [], hfa⟩

def fgFamAdmitted : IndGroupAdmitted fgB1 2 fgFamMember :=
  .family rfl (fgFamView fgFamEnv rfl) rfl rfl (Or.inr uniformType_succ_zero)

def fgMkAdmitted : IndGroupAdmitted fgFamEnv 3 fgMkMember :=
  .constructor (fgFamView fgFamEnv rfl) (fgMkView fgFamEnv rfl rfl) rfl fgMkBefore fgMkContig
    (fgMkUniverse _ rfl rfl) (fgMkFields _ rfl rfl rfl)

def fgGroupAdmitted : RecursorEliminationAdmitted fgMkEnv 4 fgRecMember where
  family := fgFamView fgMkEnv rfl
  constructors := [fgMkMember]
  constructorViews
    | ⟨0, _⟩ => fgMkView fgMkEnv rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [fgMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

theorem fgCensus : CtorCensus fgMkEnv 2 4 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, _⟩
    rw [fgMkEnv_members] at hc
    by_cases h3 : c = 3
    · exact ⟨by omega, by omega⟩
    · by_cases h2 : c = 2
      · rw [if_neg h3, if_pos h2] at hc
        cases hc
        exact absurd hk (by decide)
      · by_cases h1 : c = 1
        · rw [if_neg h3, if_neg h2, if_pos h1] at hc
          cases hc
          exact absurd hk (by decide)
        · by_cases h0 : c = 0
          · rw [if_neg h3, if_neg h2, if_neg h1, if_pos h0] at hc
            cases hc
            exact absurd hk (by decide)
          · rw [if_neg h3, if_neg h2, if_neg h1, if_neg h0] at hc
            cases hc
  · intro h
    have hc : c = 3 := by omega
    subst hc
    exact ⟨fgMkMember, rfl, rfl, rfl⟩

/-- the equation's context: `x : D2 G`, the minor, the motive. -/
def fgIotaCtx : LCtx := [.assumption fgField, .assumption fgMinorTy, .assumption fgMotiveTy]

/-- the equation's type: `motive (mk x)`. -/
def fgEqTy : Expr Nat := .app (.bvar 2) (.app (.const 3 []) (.bvar 0))

/-- the ι schema `minor x (G.rec P m x)`, canonical levels. -/
def fgSchema : Expr Nat :=
  .app (.app (.bvar 1) (.bvar 0)) (foldApps (.const 4 [.param 0]) [.bvar 2, .bvar 1, .bvar 0])

theorem fgMinor_derived : derivedMinor fgGroupAdmitted ⟨0, by decide⟩ 40 [.recursive 0] =
    some fgMinorTy := rfl

theorem fgMinorMatch : MinorPremisesMatch fgGroupAdmitted := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.recursive 0], 40, rfl, rfl⟩

theorem fgSchema_derived : iotaSchemaAt fgGroupAdmitted ⟨0, by decide⟩ 40 [.recursive 0] =
    some fgSchema := rfl

theorem fgEquation_shape :
    equationDoms fgGroupAdmitted ⟨0, by decide⟩ = some [fgMotiveTy, fgMinorTy, fgField] ∧
    iotaEquationType fgGroupAdmitted ⟨0, by decide⟩ = fgEqTy := ⟨rfl, rfl⟩

/-- `D2 G` converts to `G` in the untyped judgment: δ at `D2`, β, δ at `Id`,
    β, δ at `Id`, β. -/
def fgConvLegacy (Γ : LCtx) : Conv fgEnv 1 Γ fgField (.const 2 []) :=
  .trans _ _ (.app (.lam (.sort (.succ .zero)) (.app (.const 0 [])
      (.app (.const 0 []) (.bvar 0)))) (.const 2 [])) _
    (.app _ _ _ _ _ (.step _ _ _ (.delta _ 1 [] fgD2Member _ rfl rfl rfl)) (.refl _ _))
    (.trans _ _ (.app (.const 0 []) (.app (.const 0 []) (.const 2 []))) _
      (.step _ _ _ (.beta _ _ _ _))
      (.trans _ _ (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.app (.const 0 []) (.const 2 []))) _
        (.app _ _ _ _ _ (.step _ _ _ (.delta _ 0 [] fgIdMember _ rfl rfl rfl)) (.refl _ _))
        (.trans _ _ (.app (.const 0 []) (.const 2 [])) _
          (.step _ _ _ (.beta _ _ _ _))
          (.trans _ _ (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.const 2 [])) _
            (.app _ _ _ _ _ (.step _ _ _ (.delta _ 0 [] fgIdMember _ rfl rfl rfl)) (.refl _ _))
            (.step _ _ _ (.beta _ _ _ _))))))

/-- the recursor's head, in the untyped judgment. -/
def fgRecHead : HasTy fgEnv 1 fgIotaCtx (.const 4 [.param 0]) fgRecTy :=
  HasTy.const _ 4 [.param 0] fgRecMember rfl rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

/-- the equation in the untyped judgment: the recursive call's major converted
    from `D2 G` to `G`. -/
def fgIotaTyLegacy : HasTy fgEnv 1 fgIotaCtx fgSchema fgEqTy := by
  have hMot : HasTy fgEnv 1 fgIotaCtx (.bvar 2) fgMotiveTy := HasTy.bvar _ 2 _ rfl
  have hMin : HasTy fgEnv 1 fgIotaCtx (.bvar 1) (lift 0 2 fgMinorTy) := HasTy.bvar _ 1 _ rfl
  have hX : HasTy fgEnv 1 fgIotaCtx (.bvar 0) fgField := HasTy.bvar _ 0 _ rfl
  have hXF : HasTy fgEnv 1 fgIotaCtx (.bvar 0) (.const 2 []) :=
    HasTy.conv _ _ _ _ hX (fgConvLegacy _)
  have h1 := HasTy.app _ _ _ _ _ fgRecHead hMot
  have h2 := HasTy.app _ _ _ _ _ h1 hMin
  have h3 := HasTy.app _ _ _ _ _ h2 hXF
  have h4 := HasTy.app _ _ _ _ _ hMin hX
  exact HasTy.app _ _ _ _ _ h4 h3

def fgIotaLegacy : IotaEquationTyped fgGroupAdmitted ⟨0, by decide⟩ 40 [.recursive 0] := by
  unfold IotaEquationTyped
  rw [fgEquation_shape.1, fgSchema_derived]
  exact fgIotaTyLegacy

def fgIotaClause : IotaDescriptorClause fgMkEnv fgGroupAdmitted where
  signatureOnly := rfl
  shapesAt := fun _ => [.recursive 0]
  fuelAt := fun _ => 40
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => fgIotaLegacy

def fgGroupRecursor : IndGroupAdmitted fgMkEnv 4 fgRecMember :=
  .recursor fgGroupAdmitted rfl fgCensus
    (fun i => match i with | ⟨0, _⟩ => fgMkUniverse _ rfl rfl)
    (fun i => match i with | ⟨0, _⟩ => fgMkFields _ rfl rfl rfl)
    fgMinorMatch fgIotaClause

/-! ## (4) the typed environment judgment admits `fgEnv` -/

def fgB0WfT : EnvWfT fgB0 :=
  .definition emptyEnv 0 _ _ (.imax (.succ (.succ .zero)) (.succ (.succ .zero))) .empty rfl
    (.pi [] _ _ _ _ (.sort [] _) (.sort _ _))
    (.lam [] _ (.succ (.succ .zero)) (.bvar 0) _ (.sort [] _) (.bvar _ 0 _ rfl))
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- `D2`'s body `λ T, Id (Id T)` in the typed judgment. -/
def fgD2BodyTyT : HasTyT fgB0 0 [] fgD2Body (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .lam [] _ (.succ (.succ .zero)) _ _
    (.sort [] _)
    (.app _ (.const 0 []) _ _ _
      (.const _ 0 [] fgIdMember rfl rfl rfl)
      (.app _ (.const 0 []) (.bvar 0) _ _
        (.const _ 0 [] fgIdMember rfl rfl rfl) (.bvar _ 0 _ rfl)))

def fgB1WfT : EnvWfT fgB1 :=
  .definition fgB0 1 _ _ (.imax (.succ (.succ .zero)) (.succ (.succ .zero))) fgB0WfT rfl
    (.pi [] _ _ _ _ (.sort [] _) (.sort _ _))
    fgD2BodyTyT
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- the field at `Sort 1` in the typed judgment: `D2` applied to `G`. -/
def fgFieldTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h1 : E.members 1 = some fgD2Member)
    (h2 : E.members 2 = some fgFamMember) : HasTyT E n Γ fgField (.sort (.succ .zero)) :=
  .app Γ (.const 1 []) (.const 2 []) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.const Γ 1 [] fgD2Member h1 rfl rfl) (.const Γ 2 [] fgFamMember h2 rfl rfl)

def fgMkTyT : HasTyT fgFamEnv 0 [] fgMkMember.mtype (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] fgField (.succ .zero) (.const 2 []) (.succ .zero) (fgFieldTyT rfl rfl)
    (.const _ 2 [] fgFamMember rfl rfl rfl)

/-- the recursor type's sort, as the conversion checker reads it. -/
def fgRecSortU : Level :=
  .imax (.imax (.succ .zero) (.succ (.param 0)))
    (.imax (.imax (.succ .zero) (.imax (.param 0) (.param 0))) (.imax (.succ .zero) (.param 0)))

theorem fgRecTy_check :
    inferC fgMkEnv 1 16 [] fgRecTy = some (.sort fgRecSortU) ∧ inferT fgMkEnv 1 [] fgRecTy = none :=
  ⟨rfl, rfl⟩

def fgRecTyT : HasTyT fgMkEnv 1 [] fgRecTy (.sort fgRecSortU) :=
  (tyAtC fgMkEnv 1 16 [] fgRecTy (.sort fgRecSortU)).get rfl

theorem fgMkTypedE (E : ResolvedEnv) (h1 : E.members 1 = some fgD2Member)
    (h2 : E.members 2 = some fgFamMember) : CtorTypedT (fgMkView E h1 h2) :=
  ⟨fun i => match i with | ⟨0, _⟩ => ⟨fgFieldTyT h1 h2⟩, fun i => i.elim0⟩

theorem fgFamTyped : IndGroupTypedT fgFamAdmitted := fun i => i.elim0

theorem fgMkTyped : IndGroupTypedT fgMkAdmitted := ⟨fun i => i.elim0, fgMkTypedE _ rfl rfl⟩

/-- the recursor's typed content, with its ι equation typed in `HasTyT` by the conversion checker. -/
theorem fgRecTyped : IndGroupTypedT fgGroupRecursor :=
  ⟨fun i => i.elim0, fun i => match i with | ⟨0, _⟩ => fgMkTypedE _ rfl rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 16 Γ e T) rfl⟩

def fgMembersT :
    GroupMembersT fgFamEnv fgB1 [(2, fgFamMember), (3, fgMkMember), (4, fgRecMember)] fgEnv :=
  .cons _ 2 fgFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    fgFamAdmitted PUnit.unit _ (.sort [] (.succ .zero)) (fun h => absurd h (by decide))
    fgFamTyped
    (.cons _ 3 fgMkMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      fgMkAdmitted PUnit.unit _ fgMkTyT (fun _ => ⟨fgMkTyT⟩) fgMkTyped
      (.cons _ 4 fgRecMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        fgGroupRecursor (.ofCheck _ _ (by with_unfolding_all rfl)) _ fgRecTyT
        (fun h => absurd h (by decide)) fgRecTyped (.nil _)))

/-- `Id`, `D2`, then `G`, `mk` and `G.rec` as ONE group step: the typed
    environment judgment admits a group whose recursive field sits behind a
    two-layer δ-chain. -/
def fgEnvWfT : EnvWfT fgEnv :=
  .group fgB1 2 fgFamMember [(3, fgMkMember)] 4 fgRecMember fgEnv fgB1WfT
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl fgMembersT

theorem pin_envWfT_fuelGap : Nonempty (EnvWfT fgEnv) := ⟨fgEnvWfT⟩

/-! ## (5) the canonical witness and the refutation -/

/-- the canonical `IotaWitnessS` for `mk`'s `D2 G` field, at `fuel = 40` —
    deep enough for `fieldShapesFuel`/`iotaOpenRhs` to read through `D2`. -/
def wFg : IotaWitnessS fgEnv where
  recRef := 4
  ctorRef := 3
  ls := [.param 0]
  lsC := []
  recMember := fgRecMember
  ctorMember := fgMkMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := preMajorBvars 0 1 0 1
  fields := fieldBvars 1
  ctorParams := []
  familyRef := 2
  famMember := fgFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
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
  ctorDoms := [fgField]
  ctorResult := .const 2 []
  hpeel := rfl
  hfamApp := rfl
  recDoms := [fgMotiveTy, fgMinorTy, .const 2 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 40
  shapes := [.recursive 0]
  hshapes := rfl
  schema := fgSchema
  hschema := rfl
  hstable := iotaWitnessS_hstable_of_constsMemberFuel rfl rfl (by
    have hmem0 : fgEnv.members 0 = some fgIdMember := rfl
    have hmem1 : fgEnv.members 1 = some fgD2Member := rfl
    have hmem2 : fgEnv.members 2 = some fgFamMember := rfl
    show iotaWitnessStableB fgEnv 40 [fgField] (fieldBvars 1)
      (lift 0 2 (ctorFieldTelRaw 0 [fgField] (.const 2 []))) = true
    simp [iotaWitnessStableB, fgField, fieldBvars, ctorFieldTelRaw, lift,
      constsMemberFuel, hmem0, hmem1, hmem2, fgIdMember, fgD2Member, fgFamMember,
      fgD2Body, drIdMember, transparent, instantiateLevels])
  hschemaScope := rfl

/-- ι SUBJECT REDUCTION HOLDS AT `fgEnv`: redex and reduct are both typed at
    `fgEqTy` by the conversion checker — the certificate is the failure, not
    the step. -/
theorem fgIotaSR_lhs :
    Nonempty (HasTyT fgEnv 1 fgIotaCtx (iotaLhsOfS wFg) fgEqTy) :=
  ⟨tyAtC fgEnv 1 16 fgIotaCtx (iotaLhsOfS wFg) fgEqTy |>.get (by rfl)⟩

theorem fgIotaSR_rhs :
    Nonempty (HasTyT fgEnv 1 fgIotaCtx fgSchema fgEqTy) :=
  ⟨tyAtC fgEnv 1 16 fgIotaCtx fgSchema fgEqTy |>.get (by rfl)⟩

/-- THE FUEL GAP: the extended recognizer fails at the canonical witness —
    `telWhnfDom` at `domsFuelBound = 5` cannot unfold the `D2` chain (needs
    7), so `rhsArgsS` reads `D2`'s spine argument `G` as a field index and
    the decided schema/RHS agreement fails; the direct arm's `noTransparentB`
    rejects `D2` as well. -/
theorem pin_iotaWitnessSAnnDB_wFg : iotaWitnessSAnnDB fgEnv wFg = false := by
  decide

/-- `fgEnv` is `EnvWfT` and its shape space has no function-recursive shape
    (`wFg.shapes = [.recursive 0]`), yet `EnvCorrAnnDU` fails: the universal
    discharge `∀ E, EnvWfT E → EnvCorrAnnDU E` outside the frec gate is
    REFUTED.  Failure class: fuel bound — `domsFuelBound` bounds whnf by the
    stored domains' own size; a definition chain's δ-depth exceeds it. -/
theorem not_envCorrAnnDU_fgEnv : ¬ EnvCorrAnnDU fgEnv := by
  intro h
  have hw := h wFg
  rw [pin_iotaWitnessSAnnDB_wFg] at hw
  exact absurd hw (by decide)

theorem fuelGap_counterexample :
    Nonempty (EnvWfT fgEnv) ∧ wFg.shapes = [.recursive 0] ∧ ¬ EnvCorrAnnDU fgEnv :=
  ⟨⟨fgEnvWfT⟩, rfl, not_envCorrAnnDU_fgEnv⟩

end Rcic.Declarative.Ann
