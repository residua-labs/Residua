import rcic.RcicF8JEndpointFixture
/-! Scope controls BESIDE the canonical sealed refutations in RcicF8EvParStar.
No refutation body or shared carrier is duplicated; both historical import paths
remain usable in either order. The unconditional statements stay exactly as landed.
closure_claim=0. -/
set_option autoImplicit false
namespace Rcic.Declarative.JTileS0
open F8Measure XTileQ1
/-- Sort indices do not exclude the counterexample. -/
theorem conversion_at_sort : Nonempty (ConvT emptyEnv 0 illCtx P₁ P₂ (.sort .zero)) :=
  ⟨conv_sort0⟩

/-- The other endpoint is genuinely typed, not a jointly empty fixture. -/
theorem typed_right : Nonempty (HasTyT emptyEnv 0 illCtx P₂ (.sort .zero)) := ⟨P₂_prop⟩

def admitted_environment : EnvWfT emptyEnv := .empty

/-- The bad fixture is outside the corrected JProcWf call domain.
This is a direct context inversion, not an added premise on either refutation. -/
theorem illCtx_not_wf : ¬ Nonempty (CtxWfT emptyEnv 0 illCtx) := by
  rintro ⟨hΓ⟩
  cases hΓ with
  | assumption _ _ u _ hA =>
      obtain ⟨m, hm, _, _, _⟩ := hasTyTInv_const hA rfl
      exact Option.noConfusion hm

end Rcic.Declarative.JTileS0
