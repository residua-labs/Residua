import rcic.RcicTypedFunRecPins
import rcic.RcicDerivedIotaU
import rcic.RcicIotaShapeStable
import rcic.RcicAnnEnvBridgeGroup

/-!
# R-NoFunRec S3 — `wIota_derived` over `DerivedIotaU`/`DerivedIotaT`, and the
bridge's `.frec` erasure at the W group (per-group, append-only)

cc ruling on #6391 (design B, the union relation): the frec theorems are stated
over `DerivedIotaU` and `DerivedIotaT`, never by editing `DerivedIota` or any
sealed statement. This file is the wall-break moment of the S0 plan (§3.2
item 1): the ι rule at `sup` COMPUTES, and the reduct contains 05 §14's
function IH `fun b => Wrec mot msup (f b)` verbatim (`wCall`, S1).

- `wIotaWitnessS` — the canonical `IotaWitnessS` at `Wrec`/`sup` (the shape
  `IotaWitnessS` was built for: `fieldShapesFuel` reads `.recursive 1` at `f`,
  `iotaOpenRhs`'s schema is the open equation; stability by
  `iotaWitnessS_hstable_of_constsMemberFuel`, no new analysis).
- `wIota_derivedT` / `wIota_derived` — the landing at the SAME endpoints in the
  typed root's `DerivedIotaT` and in the union `DerivedIotaU` (option (b), S2);
  `wIotaU_elim` exercises S2's case split at this landing.
- Bridge, per-group and append-only (cc condition 3 on #6391): the sup view's
  Ann reading (`wFieldPlainA`, `wFieldFrecA`) BUILDS sup's stored type and its
  erasure is sup's stored plain type VERBATIM (`wSupTypeA_erase`) — no `NoFun`
  premise anywhere. The sealed `.frec ↦ .drec` collapse is separately measured
  (`wFrecA_erase_collapses`, `wCtorTypeT_collapse_distinct`): it LOSES the Π,
  which is the G13 evidence for the S4/S6 debt, not a claim about them.

NAMED REMAINDERS of `[rcic_cres_wall_no_fun_rec]` (recorded, never claimed):
the untyped `ParRed`/machine side does not compute frec ι (RM-side
completeness — the `.ofS` arm's `ParRed.iotaSpine` debt, `devel_iota`,
`step_to_parRed` et al.), and `RcicDTMeta`'s `IotaTyping` consumers do not
cover the S-typing. `closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-! ## (1) the canonical `IotaWitnessS` at `Wrec`/`sup` -/

/-- the shape-based ι witness at the W group: recursor `Wrec` at `6`,
    constructor `sup` at `5`, family `W` at `4`, no params or indices, one
    minor, fields `[a, f]` with kinds `[.nonrecursive, .recursive 1]`, schema
    the open equation S1 pinned (`wSchema`). -/
def wIotaWitnessS : IotaWitnessS wEnv where
  recRef := 6
  ctorRef := 5
  ls := [.param 0]
  lsC := []
  recMember := wRecMember
  ctorMember := wSupMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := preMajorBvars 0 1 0 2
  fields := fieldBvars 2
  ctorParams := []
  familyRef := 4
  famMember := wFamMember
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
  ctorDoms := [wFieldA, wFieldF]
  ctorResult := .const 4 []
  hpeel := rfl
  hfamApp := rfl
  recDoms := [wMotTy, wMinorTy, .const 4 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 8
  shapes := [.nonrecursive, .recursive 1]
  hshapes := rfl
  schema := wSchema
  hschema := rfl
  hstable := iotaWitnessS_hstable_of_constsMemberFuel rfl rfl (by
    have hmem0 : wEnv.members 0 = some natFamMember := rfl
    have hmem4 : wEnv.members 4 = some wFamMember := rfl
    have hA : constsMemberFuel wEnv (8 + 1) wFieldA = true := by
      simp only [wFieldA, constsMemberFuel, hmem0, transparent]
      rfl
    have hF : constsMemberFuel wEnv (8 + 1) wFieldF = true := by
      simp only [wFieldF, constsMemberFuel, hmem0, hmem4, transparent]
      rfl
    have hTel : constsMemberFuel wEnv (8 + 1)
        (lift 0 2 (ctorFieldTelRaw 0 [wFieldA, wFieldF] (.const 4 []))) = true := by
      simp only [wFieldA, wFieldF, ctorFieldTelRaw, lift, constsMemberFuel,
        hmem0, hmem4, transparent]
      rfl
    have hBv : List.all (fieldBvars 2) (constsMemberFuel wEnv (8 + 1)) = true := by
      show List.all [.bvar 1, .bvar 0] (constsMemberFuel wEnv (8 + 1)) = true
      simp only [List.all_cons, List.all_nil, constsMemberFuel]
      rfl
    show iotaWitnessStableB wEnv 8 [wFieldA, wFieldF] (fieldBvars 2)
      (lift 0 2 (ctorFieldTelRaw 0 [wFieldA, wFieldF] (.const 4 []))) = true
    simp only [iotaWitnessStableB, List.all_cons, List.all_nil,
      Bool.and_eq_true, hA, hF, hBv]
    exact ⟨⟨⟨trivial, trivial, trivial⟩, trivial⟩, hTel⟩)
  hschemaScope := by rfl

/-! ## (2) the endpoints, spelled -/

/-- the redex: `Wrec mot msup (sup a f)` in the canonical equation context
    `[mot, msup, a, f]` (S1's `wEquation_shape` context). -/
theorem wIota_lhs_shape :
    iotaLhsOfS wIotaWitnessS =
      recCall (.const 6 [.param 0]) [.bvar 3, .bvar 2]
        (.app (.app (.const 5 []) (.bvar 1)) (.bvar 0)) := rfl

/-- the reduct is S1's schema: `msup a f (fun b => Wrec mot msup (f b))`. -/
theorem wIota_rhs_shape : iotaRhsOfS wIotaWitnessS = wSchema := rfl

/-- the reduct spelled open: 05 §14's function IH `wCall` appears VERBATIM —
    `fun (b : Nat) => Wrec mot msup (f b)` is the last argument. -/
theorem wIota_rhs_open :
    iotaRhsOfS wIotaWitnessS =
      .app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) wCall := rfl

/-- the redex spelled open. -/
theorem wIota_lhs_open :
    iotaLhsOfS wIotaWitnessS =
      .app (.app (.app (.const 6 [.param 0]) (.bvar 3)) (.bvar 2))
        (.app (.app (.const 5 []) (.bvar 1)) (.bvar 0)) := rfl

/-! ## (3) the landings: `DerivedIotaT` and `DerivedIotaU` at the same endpoints -/

/-- the typed root's landing: `DerivedIotaT` at the W redex/reduct pair. -/
theorem wIota_derivedT :
    Nonempty (DerivedIotaT wEnv (iotaLhsOfS wIotaWitnessS) (iotaRhsOfS wIotaWitnessS)) :=
  ⟨.of wIotaWitnessS⟩

/-- the union landing (S2, option (b)): `DerivedIotaU` at the W redex/reduct
    pair, via the `.ofUS` arm — `main`'s legacy `IotaWitness` face stays closed
    (`supIota_legacy_refused`); the rule the kernel gains is the S-reading. -/
def wIotaU : DerivedIotaU wEnv (iotaLhsOfS wIotaWitnessS) (iotaRhsOfS wIotaWitnessS) :=
  derivedIotaU_ofIotaWitnessS wIotaWitnessS

/-- THE WALL-BREAK (S0 §3.2 item 1, stated per cc's ruling): the W group's ι
    computes in the union relation — no `NoFun`, no legacy witness. -/
theorem wIota_derived :
    Nonempty (DerivedIotaU wEnv (iotaLhsOfS wIotaWitnessS) (iotaRhsOfS wIotaWitnessS)) :=
  ⟨wIotaU⟩

/-- S2's elim at this landing: the case split lands `.inr` — the union route
    really is the typed-root reading here, not the legacy one. -/
theorem wIotaU_elim : derivedIotaU_elim wIotaU = .inr (.of wIotaWitnessS) := rfl

/-- spelled-endpoint form: the redex and the reduct with `wCall` verbatim. -/
theorem wIota_derived_open :
    Nonempty (DerivedIotaU wEnv
      (.app (.app (.app (.const 6 [.param 0]) (.bvar 3)) (.bvar 2))
        (.app (.app (.const 5 []) (.bvar 1)) (.bvar 0)))
      (.app (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) wCall)) := by
  rw [← wIota_lhs_open, ← wIota_rhs_open]
  exact wIota_derived

/-! ## (4) the bridge's `.frec` erasure at the W group (per-group, append-only)

cc condition 3 on #6391: a PARALLEL route, old statements untouched. The
per-group form: at the W group's own fields, with the actual W arguments —
no `NoFun` premise, no env-wide `EnvNoFunA`. -/

/-- `sup`'s first field, Ann-side: the plain `a : Nat`. -/
def wFieldPlainA : Ann.FieldA := .plain (.const 0 []) (.succ .zero)

/-- `sup`'s second field, Ann-side: `f : Π (b : Nat), W` as ONE `.frec` field
    (inner domain `Nat`, no further inner binders, no indices). -/
def wFieldFrecA : Ann.FieldA := .frec (.const 0 []) (.succ .zero) [] []

/-- the frec field's domain as the bridge's OWN builder computes it (at the
    identity substitution, no parameter locals): `Π (b : Nat), W`. -/
def wFrecDomA : Ann.ExprA × Level :=
  Ann.frecDomA 4 [] (.succ .zero) [] Ann.SubstA.id
    [(.const 0 [], (.succ .zero : Level))] []

theorem wFrecDomA_shape :
    wFrecDomA.1 = .pi (.const 0 []) (.succ .zero) (.const 4 []) (.succ .zero) := rfl

/-- the erased frec domain KEEPS the Π: it is `wFieldF` itself — the bridge's
    `.frec` arm has a real erasure at W, it was only ever stated under `NoFun`
    (G11's `(hnf _ _).elim` is vacuity, not falsehood). -/
theorem wFrecDomA_erase : Ann.erase wFrecDomA.1 = wFieldF := rfl

/-- the sup view's Ann-built type erases VERBATIM to sup's stored plain type —
    `Π (a : Nat), (Π (b : Nat), W) → W` — with a frec field present and no
    `NoFun` premise. This is the per-group `.frec` erasure (G11/G12 at W). -/
theorem wSupTypeA_erase :
    Ann.erase (Ann.ctorTypeA 4 [] (.succ .zero) [] [wFieldPlainA, wFieldFrecA] []) =
      wSupMember.mtype := rfl

/-- CANARY (G13 at W, pre-S4 evidence): the sealed `FieldA.erase` maps the frec
    field to a bare `.drec`. -/
theorem wFrecA_erase_collapses : Ann.FieldA.erase wFieldFrecA = .drec [] := rfl

/-- CANARY (G13 at W, pre-S4 evidence): the T-group built from the COLLAPSED
    fields is NOT sup's stored type — the Π over `b : Nat` (the function IH's
    domain) is gone. The `.frec ↦ .drec` route loses information at W; the
    honest erasure is `wSupTypeA_erase` above. S4 (`FieldT` frec shape) and S6
    (the ι-correspondence past `EnvNoFunA`) remain NAMED DEBT. -/
theorem wCtorTypeT_collapse_distinct :
    ctorTypeT 4 [] [] [Ann.FieldA.erase wFieldPlainA, Ann.FieldA.erase wFieldFrecA] [] ≠
      wSupMember.mtype := by decide

end Rcic.Declarative

#print axioms Rcic.Declarative.wIotaWitnessS
#print axioms Rcic.Declarative.wIota_lhs_shape
#print axioms Rcic.Declarative.wIota_rhs_shape
#print axioms Rcic.Declarative.wIota_rhs_open
#print axioms Rcic.Declarative.wIota_lhs_open
#print axioms Rcic.Declarative.wIota_derivedT
#print axioms Rcic.Declarative.wIotaU
#print axioms Rcic.Declarative.wIota_derived
#print axioms Rcic.Declarative.wIotaU_elim
#print axioms Rcic.Declarative.wIota_derived_open
#print axioms Rcic.Declarative.wFrecDomA_shape
#print axioms Rcic.Declarative.wFrecDomA_erase
#print axioms Rcic.Declarative.wSupTypeA_erase
#print axioms Rcic.Declarative.wFrecA_erase_collapses
#print axioms Rcic.Declarative.wCtorTypeT_collapse_distinct
