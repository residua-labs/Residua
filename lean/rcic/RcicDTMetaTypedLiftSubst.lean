import rcic.RcicTypedGroupPins
import rcic.RcicDTMetaTypedScope

/-!
# DT typed counterparts, segment 1 — DT-004 / DT-005 / DT-006

O2S-pattern typed counterparts (erratum E-O2SCounterparts) for the 02 §14
rows whose legacy mechanizations sit on the degenerate `HasTy`/`Conv`
judgment (`RcicUntypedConvCollapse`'s `retypeAny`/`propSelfTyped`). Each
`DTxxxT_…` is stated over the typed root (`HasTyT`/`ConvT`/`CtxWfT`/`EnvWfT`,
single-owned in `RcicDeclarative`), lands BESIDE the legacy theorem — no
legacy statement is touched — and carries a consumption pin at a real
fixture (`natEnvU` / `listEnvUT`).

- DT-004 — one declaration inserted at the head, `hasTyTWeaken` under the
  closedness the typed entry supplies (`envClosed_of_envWfT`).
- DT-005 — head (`j = 0`) substitution under an `assumption` cell, through
  the `EnvWfT`-fronted `hasTyT_subst0_of_envWfT`.
- DT-006 — the let's OWN zeta conversion's right endpoint. The
  unconditional structure-layer let substitution is `ConvTZetaRightT`
  territory (still open); on environments in the semantic-prefix bridge's
  scope, `DT009T_endpoints_inScope` supplies the endpoint, so this
  counterpart carries the O2S premise shape `EnvWfT` + `hW.InScope` +
  `CtxWfT`. The let-cell's `CtxWfT` subsumes the legacy `hv` premise (it
  literally contains the value's typing) and adds the domain's sort-typing
  plus the base context's well-formedness — all satisfiable, as the pin
  shows.

`dtTypedCensus` is this lane's census for the full 11-row migration target
(the O2S `pin_o2s_census` is sealed at 8 and untouched); right cells name
the intended counterparts, landing segment by segment.
-/

namespace Rcic.Declarative

/-- DT-004 typed: lifting preserves typing — one declaration inserted at
    the head (`insertAt d 0`), on the typed judgment, under the typed
    entry. -/
theorem DT004T_lifting_preserves_typing {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {d : LocalDecl} {e A : Expr Nat}
    (hW : EnvWfT E) (h : HasTyT E n Γ e A) :
    Nonempty (HasTyT E n (insertAt d 0 Γ) (lift 0 1 e) (lift 0 1 A)) :=
  ⟨hasTyTWeaken d (envClosed_of_envWfT hW) (c := 0) h⟩

/-- DT-005 typed: substitution preserves typing — head (`j = 0`)
    substitution under an `assumption` cell, through the `EnvWfT`-fronted
    `hasTyT_subst0_of_envWfT`. -/
theorem DT005T_substitution_preserves_typing {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (hW : EnvWfT E) {A B v e : Expr Nat}
    (hv : HasTyT E n Γ v A)
    (he : HasTyT E n (LocalDecl.assumption A :: Γ) e B) :
    Nonempty (HasTyT E n Γ (instantiate0 v e) (instantiate0 v B)) :=
  ⟨hasTyT_subst0_of_envWfT hW he hv⟩

/-- DT-006 typed: let substitution preserves typing — the let's own zeta
    conversion's RIGHT endpoint, read off `DT009T_endpoints_inScope`.
    Premise disclosure: `EnvWfT` + `hW.InScope` + the let-cell's `CtxWfT`
    (carrying the base context's well-formedness, the domain's sort-typing,
    and the value's typing — the legacy `hv`). -/
theorem DT006T_let_substitution_preserves {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} {A v B e : Expr Nat}
    (hΓ : CtxWfT E n (LocalDecl.letBinding A v :: Γ))
    (he : HasTyT E n (LocalDecl.letBinding A v :: Γ) e B) :
    Nonempty (HasTyT E n Γ (instantiate0 v e) (instantiate0 v B)) := by
  cases hΓ with
  | letBinding _ _ u _ hΓ' hA hv =>
      exact (DT009T_endpoints_inScope hW hP hΓ'
        (ConvT.zeta _ _ _ _ _ _ hA hv he)).2

/-! ## the lane census (11 rows; O2S's `pin_o2s_census` is sealed at 8) -/

/-- every 02 §14 row this lane migrates, legacy name → typed-counterpart
    name, in row order. All 11 rows land: DT-007's residue
    `[DT007T_seal_collision]` is CLOSED — `hasTyT_type_sort_exists_scope`
    is registered as `DT007T_typing_regularity` after the six helpers it
    collided on (`get?_lt_length`, the `lookup{Type,Value}_*` let
    lemmas) moved to single ownership in `RcicConvChar`, letting
    `RcicParRedSRTyped` co-import with `RcicParRedSR`. -/
def dtTypedCensus : List (String × String) :=
  [("DT003_context_regularity", "DT003T_context_regularity"),
   ("DT004_lifting_preserves_typing", "DT004T_lifting_preserves_typing"),
   ("DT005_substitution_preserves_typing",
     "DT005T_substitution_preserves_typing"),
   ("DT006_let_substitution_preserves", "DT006T_let_substitution_preserves"),
   ("DT007_typing_regularity", "DT007T_typing_regularity"),
   ("DT013_environment_weakening", "DT013T_environment_weakening"),
   ("DT014_transparent_delta_soundness",
     "DT014T_transparent_delta_soundness"),
   ("DT015_rigidity", "DT015T_rigidity"),
   ("DT016_proof_irrelevance_soundness",
     "DT016T_proof_irrelevance_soundness"),
   ("DT020_lambda_embeds_into_iota", "DT020T_lambda_embeds_into_iota"),
   ("DT023_not_everything_typable", "DT023T_not_everything_typable")]

theorem pin_dt_typed_census : dtTypedCensus.length = 11 := rfl

/-! ## consumption pins at real fixtures -/

/-- PIN (DT-004T): consumed at `natEnvU` — `Sort 0`'s own typing lifted
    under a fresh `Sort 0` assumption. -/
theorem pin_DT004T_natU {n : Nat} :
    Nonempty (HasTyT natEnvU n [LocalDecl.assumption (.sort .zero)]
      (lift 0 1 (.sort .zero)) (lift 0 1 (.sort (.succ .zero)))) :=
  DT004T_lifting_preserves_typing natEnvUWfT (pinSortT natEnvU n)

/-- PIN (DT-005T): consumed at `natEnvU` — `Sort 0` substituted for the head
    `Sort 1` assumption inside `bvar 0`'s typing. -/
theorem pin_DT005T_natU {n : Nat} :
    Nonempty (HasTyT natEnvU n []
      (instantiate0 (.sort .zero) (.bvar 0))
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  DT005T_substitution_preserves_typing natEnvUWfT (HasTyT.sort [] .zero)
    (HasTyT.bvar [LocalDecl.assumption (.sort (.succ .zero))] 0
      (.sort (.succ .zero)) rfl)

/-- PIN (DT-006T): consumed at `listEnvUT` (the real two-group environment,
    in scope) — the let's value `Sort 0` substituted into `bvar 0`'s typing
    under `letBinding (Sort 1) (Sort 0)`. -/
theorem pin_DT006T_listU {n : Nat} :
    Nonempty (HasTyT listEnvUT n []
      (instantiate0 (.sort .zero) (.bvar 0))
      (instantiate0 (.sort .zero) (.sort (.succ .zero)))) :=
  DT006T_let_substitution_preserves listEnvUWfT listEnvUWfT_inScope
    (CtxWfT.letBinding [] (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort .zero) CtxWfT.nil (HasTyT.sort [] (.succ .zero))
      (HasTyT.sort [] .zero))
    (HasTyT.bvar [LocalDecl.letBinding (.sort (.succ .zero)) (.sort .zero)] 0
      (.sort (.succ .zero)) rfl)

end Rcic.Declarative

#print axioms Rcic.Declarative.DT004T_lifting_preserves_typing
#print axioms Rcic.Declarative.DT005T_substitution_preserves_typing
#print axioms Rcic.Declarative.DT006T_let_substitution_preserves
#print axioms Rcic.Declarative.pin_dt_typed_census
#print axioms Rcic.Declarative.pin_DT004T_natU
#print axioms Rcic.Declarative.pin_DT005T_natU
#print axioms Rcic.Declarative.pin_DT006T_listU
