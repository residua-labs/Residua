import rcic.RcicTypedConvPins
import rcic.RcicTypedGroupPins

/-!
# R-NoFunRec S1 — a function-recursive field, admitted and typed, with the legacy canaries

The W fixture group of R-NoFunRec-0: `W : Sort 1` at `4` over the Nat core (`natEnvU`, refs `0 … 3`),
with ONE constructor `sup : (a : Nat) → (f : Π (b : Nat), W) → W` at `5` and its AnySort recursor
`Wrec` at `6`. The field `f` is function-recursive with `inner = 1`: its Π telescope is one binder
over the family, the smallest shape 05 §12/§14 writes a function IH for.

* Admission reads the field as the analysis does: `fieldAnalyze` returns `.permitted (.recursive 1)`
  at `f` and `.permitted .nonrecursive` at `a` (`wFieldA_analyze`, `wFieldF_analyze`), so the shapes
  list is `[.nonrecursive, .recursive 1]` (`wShapes`). The derived minor binds the function IH
  `Π (b : Nat), motive (f b)` before the result (`wMinor_derived`), and the recursor stored with it
  is admitted (`wGroupRecursor`). The ι schema applies the minor to both fields and the λ-wrapped
  recursive call `fun b => Wrec motive msup (f b)` (`wSchema_derived`) — 05 §14's function call,
  computed by `iotaOpenRhs`, not written by hand.
* The typed environment judgment admits the group (`wEnvWfT`): `W` as ONE group step over the Nat
  core, with the ι equation typed in `HasTyT` (`IndGroupTypedT`). Unlike R-NoFunRec-1-0's δ-reached
  field, NOTHING here needs conversion: the recursor's stored type types by the syntactic checker
  (`wRecTy_direct`), because `f b : W` is read off the field's own telescope, no δ.
* `main`'s ι has no rule at `sup`. Its function-recursive field has no kind (`supField_noKind`), so
  the whole constructor's kinds list is `none` (`supFields_noKind`), and NO legacy `IotaWitness`
  names this recursor — not in `wEnv` and not in any extension of `wSupEnv`
  (`supIota_legacy_refused`). The legacy index obligation is therefore vacuous (`wRecIdxAdmitted`);
  the typed obligation is real coverage, built by `.ofCheck` (`wMembersT`'s recursor member).

`closure_claim` stays 0: this file pins the fixture, its admission and the pre-fix canaries. The
wall-break theorems (the typed `IotaWitnessS` route to `wIota_derived`, the bridge's frec erasure)
are S3+ targets, not claims.
-/

namespace Rcic.Declarative

/-! ## (1) the group -/

/-- `W : Sort 1` at `4`, over the Nat core. -/
def wFamMember : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩

/-- the plain field `a : Nat`. -/
def wFieldA : Expr Nat := .const 0 []

/-- the function-recursive field `f : Π (b : Nat), W`, `inner = 1`. -/
def wFieldF : Expr Nat := .pi (.const 0 []) (.const 4 [])

/-- `sup : (a : Nat) → (f : Π (b : Nat), W) → W` at `5`. -/
def wSupMember : CheckedMember :=
  ⟨.constructorM, 0, .pi wFieldA (.pi wFieldF (.const 4 [])), none⟩

/-- the motive: `Π (_ : W), Sort (param 0)`. -/
def wMotTy : Expr Nat := .pi (.const 4 []) (.sort (.param 0))

/-- the minor: `Π (a : Nat), Π (f : Π (b : Nat), W), Π (ih : Π (b : Nat), mot (f b)),
    mot (sup a f)` — the function IH `fun b => ih-argument` bound before the result. -/
def wMinorTy : Expr Nat :=
  .pi wFieldA (.pi wFieldF
    (.pi (.pi (.const 0 []) (.app (.bvar 3) (.app (.bvar 1) (.bvar 0))))
      (.app (.bvar 3) (.app (.app (.const 5 []) (.bvar 2)) (.bvar 1)))))

/-- `Wrec` at `6`, eliminating into any sort. -/
def wRecTy : Expr Nat :=
  .pi wMotTy (.pi wMinorTy (.pi (.const 4 []) (.app (.bvar 2) (.bvar 0))))

def wRecMember : CheckedMember := ⟨.recursorM, 1, wRecTy, none⟩

def wFamEnv : ResolvedEnv := extendEnv natEnvU 4 wFamMember
def wSupEnv : ResolvedEnv := extendEnv wFamEnv 5 wSupMember
def wEnv : ResolvedEnv := extendEnv wSupEnv 6 wRecMember

theorem wEnv_members (c : Nat) :
    wEnv.members c =
      if c = 6 then some wRecMember else if c = 5 then some wSupMember
      else if c = 4 then some wFamMember else if c = 3 then some natRecMemberU
      else if c = 2 then some natSuccMember else if c = 1 then some natZeroMember
      else if c = 0 then some natFamMember else none := rfl

theorem wFamEnv_members (c : Nat) :
    wFamEnv.members c =
      if c = 4 then some wFamMember else if c = 3 then some natRecMemberU
      else if c = 2 then some natSuccMember else if c = 1 then some natZeroMember
      else if c = 0 then some natFamMember else none := rfl

theorem wSupEnv_members (c : Nat) :
    wSupEnv.members c =
      if c = 5 then some wSupMember else if c = 4 then some wFamMember
      else if c = 3 then some natRecMemberU
      else if c = 2 then some natSuccMember else if c = 1 then some natZeroMember
      else if c = 0 then some natFamMember else none := rfl

/-! ## (2) admission reads the field as the analysis does -/

/-- the analysis: `a` is nonrecursive. -/
theorem wFieldA_analyze :
    fieldAnalyze wFamEnv 8 4 0 0 0 0 wFieldA = .permitted .nonrecursive [] := rfl

/-- the analysis: `f` is function-recursive at `inner = 1` — its Π telescope is one binder over the
    family, read as the analysis does (`piTelescopeFuel`), not off the stored spine. -/
theorem wFieldF_analyze :
    fieldAnalyze wFamEnv 8 4 0 0 0 1 wFieldF = .permitted (.recursive 1) [] := rfl

theorem wFieldF_analyze' :
    fieldAnalyze wSupEnv 8 4 0 0 0 1 wFieldF = .permitted (.recursive 1) [] := rfl

/-- the shapes list the descriptor reads off both fields. -/
theorem wShapes :
    fieldShapesFuel wSupEnv 8 4 0 0 0 0 [wFieldA, wFieldF] =
      some [.nonrecursive, .recursive 1] := rfl

/-- `W : Sort 1`, wherever the family is present (no parameter, no index). -/
def wFamView (E : ResolvedEnv) (h : E.members 4 = some wFamMember) : PolicyFamilyView E where
  ref := 4
  member := wFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

/-- `a : Nat` at `Sort 1` in the untyped judgment, wherever `Nat` is present. -/
def wFieldATy {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h0 : E.members 0 = some natFamMember) :
    HasTy E n Γ wFieldA (.sort (.succ .zero)) :=
  HasTy.const _ 0 [] natFamMember h0 rfl (fun _ hx => nomatch hx)

/-- `f : Π (b : Nat), W` at `Sort (imax 1 1)` in the untyped judgment. -/
def wFieldFTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h0 : E.members 0 = some natFamMember)
    (h4 : E.members 4 = some wFamMember) :
    HasTy E n Γ wFieldF (.sort (.imax (.succ .zero) (.succ .zero))) :=
  HasTy.pi _ (.const 0 []) (.succ .zero) (.const 4 []) (.succ .zero)
    (HasTy.const _ 0 [] natFamMember h0 rfl (fun _ hx => nomatch hx))
    (HasTy.const _ 4 [] wFamMember h4 rfl (fun _ hx => nomatch hx))

def wSupView (E : ResolvedEnv) (h0 : E.members 0 = some natFamMember)
    (h4 : E.members 4 = some wFamMember) :
    PolicyConstructorView E (wFamView E h4) wSupMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [wFieldA, wFieldF]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun j =>
      match j with
      | ⟨0, _⟩ => .succ .zero
      | ⟨1, _⟩ => .imax (.succ .zero) (.succ .zero)
    bounded := fun j => by
      match j with
      | ⟨0, _⟩ => exact rfl
      | ⟨1, _⟩ => exact rfl
    hasType := fun j => by
      match j with
      | ⟨0, _⟩ => exact wFieldATy h0
      | ⟨1, _⟩ => exact wFieldFTy h0 h4
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

/-- `imax 1 1 ≤ₙ 1`: the function-recursive field's `Sort (imax 1 1)` fits the `Sort 1` family. -/
theorem leN_imax_succ_zero_self :
    leN (.imax (.succ .zero) (.succ .zero)) (.succ .zero) := by
  intro ρ x y hx hy
  have e : eval ρ (.imax (.succ .zero) (.succ .zero)) = some 1 := rfl
  have e' : eval ρ (.succ .zero) = some 1 := rfl
  rw [e] at hx
  rw [e'] at hy
  have hx1 : x = 1 := (Option.some.inj hx).symm
  have hy1 : y = 1 := (Option.some.inj hy).symm
  subst hx1
  subst hy1
  exact Nat.le_refl 1

theorem wSupUniverse (E : ResolvedEnv) (h0 : E.members 0 = some natFamMember)
    (h4 : E.members 4 = some wFamMember) : FieldUniverseAdmitted (wSupView E h0 h4) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
  | ⟨1, _⟩ => exact Or.inr ⟨uniformType_succ_zero, leN_imax_succ_zero_self⟩

theorem wSupFields (E : ResolvedEnv) (h0 : E.members 0 = some natFamMember)
    (h4 : E.members 4 = some wFamMember)
    (hfa : fieldAnalyze E 8 4 0 0 0 0 wFieldA = .permitted .nonrecursive [])
    (hff : fieldAnalyze E 8 4 0 0 0 1 wFieldF = .permitted (.recursive 1) []) :
    CtorFieldsPermitted (wSupView E h0 h4) := by
  intro j
  match j with
  | ⟨0, _⟩ => exact ⟨.nonrecursive, 8, [], hfa⟩
  | ⟨1, _⟩ => exact ⟨.recursive 1, 8, [], hff⟩

theorem wBefore : CtorBeforeRecursors wFamEnv wSupMember := by
  refine ⟨4, rfl, ?_⟩
  intro rr rm hm hk hne
  rw [wFamEnv_members] at hm
  by_cases h4 : rr = 4
  · rw [if_pos h4] at hm
    cases hm
    exact absurd hk (by decide)
  · by_cases h3 : rr = 3
    · rw [if_neg h4, if_pos h3] at hm
      cases hm
      rw [show memberFamRef natRecMemberU = some 0 from rfl] at hne
      exact absurd hne (by decide)
    · by_cases h2 : rr = 2
      · rw [if_neg h4, if_neg h3, if_pos h2] at hm
        cases hm
        exact absurd hk (by decide)
      · by_cases h1 : rr = 1
        · rw [if_neg h4, if_neg h3, if_neg h2, if_pos h1] at hm
          cases hm
          exact absurd hk (by decide)
        · by_cases h0 : rr = 0
          · rw [if_neg h4, if_neg h3, if_neg h2, if_neg h1, if_pos h0] at hm
            cases hm
            exact absurd hk (by decide)
          · rw [if_neg h4, if_neg h3, if_neg h2, if_neg h1, if_neg h0] at hm
            cases hm

theorem wContig : CtorContiguous wFamEnv 5 wSupMember := by
  refine ⟨4, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    exact absurd hr (by omega)
  · intro c hex
    rcases hex with ⟨cm, hm, hc, hfam⟩
    rw [wFamEnv_members] at hm
    by_cases h4 : c = 4
    · rw [if_pos h4] at hm
      cases hm
      exact absurd hc (by decide)
    · by_cases h3 : c = 3
      · rw [if_neg h4, if_pos h3] at hm
        cases hm
        exact absurd hc (by decide)
      · by_cases h2 : c = 2
        · rw [if_neg h4, if_neg h3, if_pos h2] at hm
          cases hm
          exact absurd hfam (by decide)
        · by_cases h1 : c = 1
          · rw [if_neg h4, if_neg h3, if_neg h2, if_pos h1] at hm
            cases hm
            exact absurd hfam (by decide)
          · by_cases h0 : c = 0
            · rw [if_neg h4, if_neg h3, if_neg h2, if_neg h1, if_pos h0] at hm
              cases hm
              exact absurd hc (by decide)
            · rw [if_neg h4, if_neg h3, if_neg h2, if_neg h1, if_neg h0] at hm
              cases hm

theorem wCensus : CtorCensus wSupEnv 4 6 := by
  refine ⟨by decide, fun c => ?_⟩
  constructor
  · rintro ⟨cm, hc, hk, hfam⟩
    rw [wSupEnv_members] at hc
    by_cases h5 : c = 5
    · rw [if_pos h5] at hc
      cases hc
      exact ⟨by omega, by omega⟩
    · by_cases h4 : c = 4
      · rw [if_neg h5, if_pos h4] at hc
        cases hc
        exact absurd hk (by decide)
      · by_cases h3 : c = 3
        · rw [if_neg h5, if_neg h4, if_pos h3] at hc
          cases hc
          exact absurd hk (by decide)
        · by_cases h2 : c = 2
          · rw [if_neg h5, if_neg h4, if_neg h3, if_pos h2] at hc
            cases hc
            exact absurd hfam (by decide)
          · by_cases h1 : c = 1
            · rw [if_neg h5, if_neg h4, if_neg h3, if_neg h2, if_pos h1] at hc
              cases hc
              exact absurd hfam (by decide)
            · by_cases h0 : c = 0
              · rw [if_neg h5, if_neg h4, if_neg h3, if_neg h2, if_neg h1, if_pos h0] at hc
                cases hc
                exact absurd hk (by decide)
              · rw [if_neg h5, if_neg h4, if_neg h3, if_neg h2, if_neg h1, if_neg h0] at hc
                cases hc
  · intro h
    have hc : c = 5 := by omega
    subst hc
    exact ⟨wSupMember, by rw [wSupEnv_members]; rfl, rfl, rfl⟩

def wFamAdmitted : IndGroupAdmitted natEnvU 4 wFamMember :=
  .family rfl (wFamView wFamEnv rfl) rfl rfl (Or.inr uniformType_succ_zero)

def wSupAdmitted : IndGroupAdmitted wFamEnv 5 wSupMember :=
  .constructor (wFamView wFamEnv rfl) (wSupView wFamEnv rfl rfl) rfl wBefore wContig
    (wSupUniverse wFamEnv rfl rfl) (wSupFields wFamEnv rfl rfl rfl rfl)

def wGroupAdmitted : RecursorEliminationAdmitted wSupEnv 6 wRecMember where
  family := wFamView wSupEnv rfl
  constructors := [wSupMember]
  constructorViews
    | ⟨0, _⟩ => wSupView wSupEnv rfl rfl
  constructorsPresent
    | ⟨0, _⟩ => rfl
  recursorRef := rfl
  minorTypes := [wMinorTy]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl
  recursorMclass := rfl

/-! ## (2b) the derived minor and the ι schema -/

/-- THE DERIVED MINOR (05 §12) reads `f` through its Π telescope: its induction hypothesis is
    `Π (b : Nat), motive (f b)` — the function IH, `funIHType`'s output at `inner = 1`. -/
theorem wMinor_derived :
    derivedMinor wGroupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive, .recursive 1] = some wMinorTy :=
  rfl

theorem wMinorMatch : MinorPremisesMatch wGroupAdmitted := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨[.nonrecursive, .recursive 1], 8, rfl, rfl⟩

/-- the equation's context: `f`, `a`, the minor, the motive. -/
def wIotaCtx : LCtx :=
  [.assumption wFieldF, .assumption wFieldA, .assumption wMinorTy, .assumption wMotTy]

/-- the λ-wrapped recursive call 05 §14 writes for a function-recursive field:
    `fun (b : Nat) => Wrec mot msup (f b)`, `funRecArg`'s output. -/
def wCall : Expr Nat :=
  .lam (.const 0 [])
    (.app (.app (.app (.const 6 [.param 0]) (.bvar 4)) (.bvar 3)) (.app (.bvar 1) (.bvar 0)))

/-- the schema admission derives (05 §14): `msup a f (fun b => Wrec mot msup (f b))`. -/
def wSchema : Expr Nat :=
  .app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) wCall

/-- the equation's type: `mot (sup a f)`. -/
def wEqTy : Expr Nat :=
  .app (.bvar 3) (.app (.app (.const 5 []) (.bvar 1)) (.bvar 0))

theorem wSchema_derived :
    iotaSchemaAt wGroupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive, .recursive 1] = some wSchema :=
  rfl

theorem wEquation_shape :
    equationDoms wGroupAdmitted ⟨0, by decide⟩ = some [wMotTy, wMinorTy, wFieldA, wFieldF] ∧
    iotaEquationType wGroupAdmitted ⟨0, by decide⟩ = wEqTy := ⟨rfl, rfl⟩

/-- the recursor's head, in the untyped judgment, wherever `Wrec` is present. -/
def wRecHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h6 : E.members 6 = some wRecMember) :
    HasTy E n Γ (.const 6 [.param 0]) wRecTy :=
  HasTy.const _ 6 [.param 0] wRecMember h6 rfl (by
    intro l hl
    have hl' : l = .param 0 := by simpa using hl
    subst hl'
    exact ⟨0, Or.inl rfl⟩)

/-- the equation in the untyped judgment, as admission's clause asks: every piece is DIRECT —
    `f b : W` off the field's own telescope, the λ wrapper at the minor's IH domain, no conversion
    anywhere (contrast `drIotaTyLegacy`, which needs `Id F ≡ F`). -/
def wIotaTyLegacy : HasTy wEnv 1 wIotaCtx wSchema wEqTy := by
  have hMot : HasTy wEnv 1 wIotaCtx (.bvar 3) wMotTy := HasTy.bvar _ 3 _ rfl
  have hMs : HasTy wEnv 1 wIotaCtx (.bvar 2) (lift 0 3 wMinorTy) := HasTy.bvar _ 2 _ rfl
  have hA : HasTy wEnv 1 wIotaCtx (.bvar 1) wFieldA := HasTy.bvar _ 1 _ rfl
  have hF : HasTy wEnv 1 wIotaCtx (.bvar 0) wFieldF := HasTy.bvar _ 0 _ rfl
  have hNat : HasTy wEnv 1 wIotaCtx (.const 0 []) (.sort (.succ .zero)) :=
    HasTy.const _ 0 [] natFamMember rfl rfl (fun _ hx => nomatch hx)
  have hMot' : HasTy wEnv 1 (.assumption (.const 0 []) :: wIotaCtx) (.bvar 4) wMotTy :=
    HasTy.bvar _ 4 _ rfl
  have hMs' : HasTy wEnv 1 (.assumption (.const 0 []) :: wIotaCtx) (.bvar 3) (lift 0 4 wMinorTy) :=
    HasTy.bvar _ 3 _ rfl
  have hF' : HasTy wEnv 1 (.assumption (.const 0 []) :: wIotaCtx) (.bvar 1) wFieldF :=
    HasTy.bvar _ 1 _ rfl
  have hB : HasTy wEnv 1 (.assumption (.const 0 []) :: wIotaCtx) (.bvar 0) (.const 0 []) :=
    HasTy.bvar _ 0 _ rfl
  exact HasTy.app _ _ _ _ _
    (HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ hMs hA) hF)
    (HasTy.lam _ (.const 0 []) (.succ .zero) _ _ hNat
      (HasTy.app _ _ _ _ _
        (HasTy.app _ _ _ _ _ (HasTy.app _ _ _ _ _ (wRecHead rfl) hMot') hMs')
        (HasTy.app _ _ _ _ _ hF' hB)))

def wIotaLegacy : IotaEquationTyped wGroupAdmitted ⟨0, by decide⟩ 8 [.nonrecursive, .recursive 1] :=
  by
  unfold IotaEquationTyped
  rw [wEquation_shape.1, wSchema_derived]
  exact wIotaTyLegacy

def wIotaClause : IotaDescriptorClause wSupEnv wGroupAdmitted where
  signatureOnly := rfl
  shapesAt := fun _ => [.nonrecursive, .recursive 1]
  fuelAt := fun _ => 8
  analyzed
    | ⟨0, _⟩ => rfl
  typed
    | ⟨0, _⟩ => wIotaLegacy

def wGroupRecursor : IndGroupAdmitted wSupEnv 6 wRecMember :=
  .recursor wGroupAdmitted rfl wCensus
    (fun i => match i with | ⟨0, _⟩ => wSupUniverse wSupEnv rfl rfl)
    (fun i => match i with | ⟨0, _⟩ => wSupFields wSupEnv rfl rfl rfl rfl)
    wMinorMatch wIotaClause

/-! ## (3) `main`'s ι has no rule here -/

/-- CANARY (R-NoFunRec-0): `main`'s ι reads `sup`'s function-recursive field as written and gives
    it no kind — `RecKind` is only plain | directRec. -/
theorem supField_noKind : analyzeField 4 wFieldF = none := rfl

/-- …so the whole constructor's kinds list is `none`. -/
theorem supFields_noKind : analyzeFields 4 [wFieldA, wFieldF] = none := rfl

/-- the shared inversion: in ANY extension of `wSupEnv`, a legacy witness naming `Wrec` pins its
    family to `W` at `4`, its constructor to `sup` at `5`, and its fields to `[a, f]` — whose kinds
    list is `none`. `main`'s ι face derives no rule at a function-recursive constructor. -/
theorem wIotaWitness_nokind {E' : ResolvedEnv}
    (hext : ∀ r' m', wSupEnv.members r' = some m' → E'.members r' = some m')
    (w : IotaWitness E') (hr : w.recRef = 6) (hm : w.recMember = wRecMember) : False := by
  have hrecIdx := w.hrecIdx
  rw [hr] at hrecIdx
  have hidx := w.hidx
  have hctorIdx := w.hctorIdx
  have hfam := w.hfam
  have hfamK := w.hfamK
  have hnM : 1 ≤ w.nMinors := by omega
  have hfle : w.familyRef ≤ 4 := by omega
  by_cases hf4 : w.familyRef = 4
  · rw [hf4, hext 4 wFamMember rfl] at hfam
    have hfm : w.famMember = wFamMember := (Option.some.inj hfam).symm
    have hk0 : w.ctorIdx = 0 := by omega
    have hc5 : w.ctorRef = 5 := by omega
    have hctor := w.hctor
    rw [hc5, hext 5 wSupMember rfl] at hctor
    have hcm : w.ctorMember = wSupMember := (Option.some.inj hctor).symm
    have hnidx := w.hnidx
    rw [hfm] at hnidx
    have hpc0 : piCount wFamMember.mtype = 0 := rfl
    rw [hpc0] at hnidx
    have hnp : w.nparams = 0 := by omega
    have hlen2 : w.nparams + w.fields.length = 2 := by rw [w.hnpar, hcm]; rfl
    have hpeel := w.hpeel
    rw [hlen2, hcm] at hpeel
    have hpeel' : (some ([wFieldA, wFieldF], Expr.const 4 []) : Option (List (Expr Nat) × Expr Nat)) =
        some (w.ctorDoms, w.ctorResult) := hpeel
    have hdoms : [wFieldA, wFieldF] = w.ctorDoms := (Prod.mk.inj (Option.some.inj hpeel')).1
    have hkinds := w.hkinds
    rw [hf4, ← hdoms, hnp] at hkinds
    exact absurd hkinds (by rw [List.drop_zero, supFields_noKind]; exact fun h => Option.noConfusion h)
  · by_cases hf3 : w.familyRef = 3
    · rw [hf3, hext 3 natRecMemberU rfl] at hfam
      rw [← Option.some.inj hfam] at hfamK
      exact absurd hfamK (by decide)
    · by_cases hf2 : w.familyRef = 2
      · rw [hf2, hext 2 natSuccMember rfl] at hfam
        rw [← Option.some.inj hfam] at hfamK
        exact absurd hfamK (by decide)
      · by_cases hf1 : w.familyRef = 1
        · rw [hf1, hext 1 natZeroMember rfl] at hfam
          rw [← Option.some.inj hfam] at hfamK
          exact absurd hfamK (by decide)
        · have hf0 : w.familyRef = 0 := by omega
          rw [hf0, hext 0 natFamMember rfl] at hfam
          have hfm : w.famMember = natFamMember := (Option.some.inj hfam).symm
          have hnidx := w.hnidx
          rw [hfm] at hnidx
          have hpc0 : piCount natFamMember.mtype = 0 := rfl
          rw [hpc0] at hnidx
          have hnM5 : w.nMinors = 5 := by omega
          have hcnt : w.nparams + 1 + w.nMinors + w.nindices + 1 = 7 := by omega
          have hpeelRec := w.hpeelRec
          rw [hm, hcnt] at hpeelRec
          have hnone : peelPis 7 wRecMember.mtype = none := rfl
          rw [hnone] at hpeelRec
          exact Option.noConfusion hpeelRec

theorem wEnv_extends (r' : Nat) (m' : CheckedMember) (h : wSupEnv.members r' = some m') :
    wEnv.members r' = some m' := by
  by_cases h6 : r' = 6
  · rw [h6] at h
    simp [wSupEnv_members] at h
  · have hsplit : wEnv.members r' = if r' = 6 then some wRecMember else wSupEnv.members r' := rfl
    rw [hsplit, if_neg h6]
    exact h

/-- CANARY (R-NoFunRec-0): no legacy ι witness names `Wrec` at `sup` — not in `wEnv`, and not in any
    extension of `wSupEnv` (`wIotaWitness_nokind`). -/
theorem supIota_legacy_refused :
    ¬ ∃ w : IotaWitness wEnv, w.recRef = 6 ∧ w.recMember = wRecMember := by
  rintro ⟨w, hr, hm⟩
  exact wIotaWitness_nokind (fun r' m' h => wEnv_extends r' m' h) w hr hm

/-- so the legacy index obligation holds with no case: `main`'s ι has no rule at this recursor. -/
def wRecIdxAdmitted : RecursorGroupIdxAdmitted wSupEnv 6 wRecMember where
  typing := fun {_} hext _ w hw hwm => (wIotaWitness_nokind hext w hw hwm).elim

/-! ## (4) the typed environment judgment admits it -/

/-- `W : Sort 1`, wherever the family is present. -/
def wFamConstTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h4 : E.members 4 = some wFamMember) :
    HasTyT E n Γ (.const 4 []) (.sort (.succ .zero)) :=
  .const Γ 4 [] wFamMember h4 rfl rfl

/-- `f : Π (b : Nat), W` at `Sort (imax 1 1)` in the typed judgment. -/
def wFieldFTyT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (h0 : E.members 0 = some natFamMember)
    (h4 : E.members 4 = some wFamMember) :
    HasTyT E n Γ wFieldF (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ (.const 0 []) (.succ .zero) (.const 4 []) (.succ .zero)
    (natConstTyT h0) (wFamConstTyT h4)

/-- `sup`'s stored type at `Sort (imax 1 (imax (imax 1 1) 1))` in the typed judgment. -/
def wSupTyT : HasTyT wFamEnv 0 [] wSupMember.mtype
    (.sort (.imax (.succ .zero) (.imax (.imax (.succ .zero) (.succ .zero)) (.succ .zero)))) :=
  .pi [] wFieldA (.succ .zero) _ (.imax (.imax (.succ .zero) (.succ .zero)) (.succ .zero))
    (natConstTyT rfl)
    (.pi [.assumption wFieldA] wFieldF (.imax (.succ .zero) (.succ .zero)) (.const 4 [])
      (.succ .zero) (wFieldFTyT rfl rfl) (wFamConstTyT rfl))

/-- the recursor's stored type's sort. -/
def wRecSortU : Level :=
  .imax (.imax (.succ .zero) (.succ (.param 0)))
    (.imax (.imax (.succ .zero) (.imax (.imax (.succ .zero) (.succ .zero))
        (.imax (.imax (.succ .zero) (.param 0)) (.param 0))))
      (.imax (.succ .zero) (.param 0)))

/-- no conversion anywhere: the recursor's stored type types by the SYNTACTIC checker, because
    `f b : W` is read off the field's own telescope (`wFieldF`'s codomain IS the family). Contrast
    `drRecTy_check`, where the δ-reached `Id F` field forced the conversion checker. -/
theorem wRecTy_direct : inferT wSupEnv 1 [] wRecTy = some (.sort wRecSortU) := rfl

def wRecTyT : HasTyT wSupEnv 1 [] wRecTy (.sort wRecSortU) :=
  (tyAtC wSupEnv 1 8 [] wRecTy (.sort wRecSortU)).get (by
    have h : (tyAtC wSupEnv 1 8 [] wRecTy (.sort wRecSortU)).isSome = true := rfl
    exact h)

theorem wSupTypedE (E : ResolvedEnv) (h0 : E.members 0 = some natFamMember)
    (h4 : E.members 4 = some wFamMember) : CtorTypedT (wSupView E h0 h4) :=
  ⟨fun j => by
      match j with
      | ⟨0, _⟩ => exact ⟨natConstTyT h0⟩
      | ⟨1, _⟩ => exact ⟨wFieldFTyT h0 h4⟩,
    fun i => i.elim0⟩

theorem wFamTyped : IndGroupTypedT wFamAdmitted := fun i => i.elim0

theorem wSupTyped : IndGroupTypedT wSupAdmitted :=
  ⟨fun i => i.elim0, wSupTypedE wFamEnv rfl rfl⟩

/-- the recursor's typed content, with its ι equation typed in `HasTyT` by the conversion checker
    (the syntactic checker types it too — the equation's pieces are direct, `wRecTy_direct`). -/
theorem wRecTyped : IndGroupTypedT wGroupRecursor :=
  ⟨fun i => i.elim0, fun i => match i with | ⟨0, _⟩ => wSupTypedE wSupEnv rfl rfl,
   fun i => match i with
    | ⟨0, _⟩ => iotaEquationTypedT_of_check (fun Γ e T => tyAtC _ _ 8 Γ e T) rfl⟩

def wMembersT :
    GroupMembersT wFamEnv natEnvU
      [(4, wFamMember), (5, wSupMember), (6, wRecMember)] wEnv :=
  .cons _ 4 wFamMember _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) rfl rfl rfl
    wFamAdmitted PUnit.unit _ (.sort [] (.succ .zero)) (fun h => absurd h (by decide))
    wFamTyped
    (.cons _ 5 wSupMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
      wSupAdmitted PUnit.unit _ wSupTyT (fun _ => ⟨wSupTyT⟩) wSupTyped
      -- the typed obligation is real coverage: the canonical `IotaWitnessS` for the
      -- function-recursive field, built by `ofCheck` (R-NoFunRec-1 B2, step 2d-2b pattern).
      (.cons _ 6 wRecMember _ _ rfl rfl (fun _ => rfl) (fun h => absurd h (by decide)) rfl rfl rfl
        wGroupRecursor (.ofCheck _ _ (by with_unfolding_all rfl)) _ wRecTyT
        (fun h => absurd h (by decide)) wRecTyped (.nil _)))

/-- the Nat core, then `W`, `sup` and `Wrec` as ONE group step: the typed environment judgment
    admits a group whose recursive field is FUNCTION-recursive. -/
def wEnvWfT : EnvWfT wEnv :=
  .group natEnvU 4 wFamMember [(5, wSupMember)] 6 wRecMember wEnv natEnvUWfT
    rfl (fun c hc => by simp at hc; subst hc; rfl) rfl wMembersT

theorem pin_envWfT_funRec : Nonempty (EnvWfT wEnv) := ⟨wEnvWfT⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.wFieldA_analyze
#print axioms Rcic.Declarative.wFieldF_analyze
#print axioms Rcic.Declarative.wShapes
#print axioms Rcic.Declarative.wMinor_derived
#print axioms Rcic.Declarative.wMinorMatch
#print axioms Rcic.Declarative.wSchema_derived
#print axioms Rcic.Declarative.wEquation_shape
#print axioms Rcic.Declarative.wGroupRecursor
#print axioms Rcic.Declarative.supField_noKind
#print axioms Rcic.Declarative.supFields_noKind
#print axioms Rcic.Declarative.wIotaWitness_nokind
#print axioms Rcic.Declarative.supIota_legacy_refused
#print axioms Rcic.Declarative.wRecIdxAdmitted
#print axioms Rcic.Declarative.wRecTy_direct
#print axioms Rcic.Declarative.wRecTyT
#print axioms Rcic.Declarative.wSupTypedE
#print axioms Rcic.Declarative.wRecTyped
#print axioms Rcic.Declarative.wMembersT
#print axioms Rcic.Declarative.wEnvWfT
#print axioms Rcic.Declarative.pin_envWfT_funRec
