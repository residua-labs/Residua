import rcic.RcicF3PiRawFieldViews
import rcic.RcicF3PiRawRenameAttack

/-!
# Hidden fields, dependent indices, and repeated binder insertion

These are admission/reader regressions, including depth three and relabelled
families. The delta variants test the reader, not typing of the alias
environment. Complete typed W regressions are kept separately.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PiRawFieldViewsAttack
open Rcic.Declarative PiRawFieldViews PiRawRenameAttack PiRawCtorAttack

theorem hidden_views : ∀ f ∈ [1, 2, 987],
    ∀ T ∈ [original f, beta f, delta f, zeta f],
      View (PiRawParamsAttack.env f) 32 f 0 1 0 0 T (.recursive 3) := by
  intro f hf T hT
  exact of_admitted (hidden_checks f hf T hT).1

def inserted (f : Nat) : Expr Nat :=
  Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 1 3 (indexed f))

theorem repeated_insertion : ∀ f ∈ [1, 2, 987],
    View (paramEnv f) 32 f 0 1 1 6 (inserted f) (.recursive 3) := by
  intro f hf
  have htf := type_facts f
  have hcl : EnvClosed (paramEnv f) := fun r m hm =>
    ⟨(htf r m hm).1, fun b hb => ((htf r m hm).2.2 b hb).1⟩
  have hv : View (paramEnv f) 32 f 0 1 1 2 (indexed f) (.recursive 3) :=
    of_admitted (indexed_insertion f hf).1
  exact (hv.lift hcl 1 3 (by decide)).lift hcl 0 1 (by decide)

/-- Six distinct prior data values make a wrong parameter offset observable.
The dependent index is still part of the two-element family argument spine. -/
theorem indexed_readback (M : Interp.{4}) (σ : Nat → Nat) :
    ∀ f ∈ [1, 2, 987],
      ∃ ds args : List (Expr Nat), ds.length = 3 ∧ args.length = 2 ∧
        piTelescopeFuel (paramEnv f) 32 (Rcic.Declarative.lift 0 1 (inserted f)) =
          some (ds, foldApps (.const f []) args) ∧
        ∀ xs, xs.length = ds.length →
          (args.take 1).map (den M σ
            (push xs (vcons (dataVal 14 [])
              (push [dataVal 8 [], dataVal 9 [], dataVal 10 [], dataVal 11 [],
                dataVal 12 [], dataVal 13 []] (push [dataVal 7 []] ρ0))))) =
            [dataVal 7 []] := by
  intro f hf
  have htf := type_facts f
  have hcl : EnvClosed (paramEnv f) := fun r m hm =>
    ⟨(htf r m hm).1, fun b hb => ((htf r m hm).2.2 b hb).1⟩
  exact View.ih_read M σ [dataVal 7 []]
    [dataVal 8 [], dataVal 9 [], dataVal 10 [], dataVal 11 [], dataVal 12 [], dataVal 13 []]
    ρ0 (dataVal 14 []) hcl rfl (repeated_insertion f hf)

end Rcic.F3.PSet.PiRawFieldViewsAttack
