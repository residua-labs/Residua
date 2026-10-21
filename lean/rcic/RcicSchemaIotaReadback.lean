import rcic.RcicNativeFamModel
import rcic.RcicParRedTPins
import rcic.RcicConvChar

/-!
# Schema-ι at a typed redex, with no legacy `ConvT.iota`

`WhStepCtx.iota` fires on both arms of `DerivedIotaU`. `ConvT.iota` takes
only legacy `DerivedIota`. This module does not inhabit `SchemaIotaConv`
and does not add a `ConvT` constructor.

Negative horn, at the landed W-group. `wEnvWfT` admits `wEnv`. Both
endpoints of `wSupWS` (`Wrec M m (sup a f)` and the admission schema) are
`HasTyT` at `wEqTy`. `WhStepCtx.iota (DerivedIotaU.ofUS wSupWS)` is a
weak-head step between them. No `IotaWitness` names `Wrec`
(`supIota_legacy_refused`), so there is no `DerivedIota` at those
endpoints and `ConvT.iota` cannot be applied there. This is one
counterexample, not a claim that every schema step lacks a legacy
certificate, and not a claim that no other `ConvT` constructor relates
the endpoints.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.SchemaIotaReadback

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.FamModelAudit

/-- Project a legacy landing to its witness. The indices of `DerivedIota.of`
are the witness's own endpoints, so the equations are `rfl`. -/
private def derivedIotaWitness {E : ResolvedEnv} {lhs rhs : Expr Nat}
    (h : DerivedIota E lhs rhs) :
    Σ' w : IotaWitness E, lhs = iotaLhsOf w ∧ rhs = iotaRhsOf w :=
  match h with
  | .of w => ⟨w, And.intro rfl rfl⟩

/-- The schema redex is the three-argument const spine `Wrec M m (sup a f)`. -/
private theorem wSup_lhs_foldApps :
    foldApps (.const 6 [.param 0])
      ([.bvar 3, .bvar 2,
        .app (.app (.const 5 []) (.bvar 1)) (.bvar 0)] : List (Expr Nat)) =
    .app (.app (.app (.const 6 [.param 0]) (.bvar 3)) (.bvar 2))
      (.app (.app (.const 5 []) (.bvar 1)) (.bvar 0)) := rfl

/-- No legacy `DerivedIota` at the schema endpoints. Any such landing's
recursor head is `const 6 [.param 0]`, hence `recRef = 6`, and `wEnv.members 6`
forces `recMember = wRecMember`, which `supIota_legacy_refused` excludes. -/
private theorem schemaIota_wSup_no_derivedIota :
    DerivedIota wEnv (iotaLhsOfS wSupWS) (iotaRhsOfS wSupWS) → False := by
  intro h
  match derivedIotaWitness h with
  | ⟨w, And.intro hlhs _⟩ =>
    rw [wSupWS_lhs] at hlhs
    unfold iotaLhsOf recCall at hlhs
    obtain ⟨hconst, _⟩ := foldApps_const_inj (wSup_lhs_foldApps.trans hlhs)
    have href : w.recRef = 6 := (Expr.const.inj hconst).1.symm
    have hmem : wEnv.members 6 = some w.recMember := by
      rw [← href]
      exact w.hrec
    have htab : wEnv.members 6 = some wRecMember := by
      rw [wEnv_members]
      exact if_pos rfl
    exact supIota_legacy_refused
      ⟨w, And.intro href (Option.some.inj (hmem.symm.trans htab))⟩

/-- Admitted environment, both endpoints typed, schema-ι step present,
legacy `DerivedIota` absent. `ConvT.iota` needs that `DerivedIota`. -/
theorem schemaIota_wSup_no_legacyConv :
    Nonempty (EnvWfT wEnv) ∧
    Nonempty (HasTyT wEnv 1 wIotaCtx (iotaLhsOfS wSupWS) wEqTy) ∧
    Nonempty (HasTyT wEnv 1 wIotaCtx (iotaRhsOfS wSupWS) wEqTy) ∧
    ((WhStepCtx.iota (DerivedIotaU.ofUS wSupWS) :
        WhStepCtx wEnv wIotaCtx (iotaLhsOfS wSupWS) (iotaRhsOfS wSupWS)) =
      (WhStepCtx.iota (DerivedIotaU.ofUS wSupWS) :
        WhStepCtx wEnv wIotaCtx (iotaLhsOfS wSupWS) (iotaRhsOfS wSupWS))) ∧
    (DerivedIota wEnv (iotaLhsOfS wSupWS) (iotaRhsOfS wSupWS) → False) :=
  ⟨⟨wEnvWfT⟩, ⟨wSupWS_lhsTyT⟩, ⟨wSupWS_rhsTyT⟩, rfl, schemaIota_wSup_no_derivedIota⟩

end Rcic.Declarative.NativeValleys.SchemaIotaReadback

#print axioms Rcic.Declarative.NativeValleys.SchemaIotaReadback.schemaIota_wSup_no_legacyConv
