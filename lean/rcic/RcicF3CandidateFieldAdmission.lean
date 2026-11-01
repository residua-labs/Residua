import rcic.RcicF3PiCleanViews
import rcic.RcicF3PropEvalInputs

/-!
# Complete original-field certificates from the actual admission scan

The same successful fieldShapesFuel computation produces both the parameter
offset views and the family-free normalized domains and complete arguments.
The latter are packaged in the lift-stable certificate list consumed by the
interleaved Inputs producer. No normalization or evaluation premise is added.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.CandidateFieldAdmission
open Rcic.Declarative

theorem certificates_of_fields {E : ResolvedEnv} {fuel f nu np ni : Nat} :
    ∀ (Fs : List (Expr Nat)) (prior : Nat) (ss : List FieldShape),
      fieldShapesFuel E fuel f nu np ni (np + prior) Fs = some ss →
      PropEval.FieldCertificates
        (fun _ A s => PiCleanViews.Clean E fuel f nu np ni A s) prior ss Fs := by
  intro Fs
  induction Fs with
  | nil =>
      intro prior ss h
      have he : ss = [] := (Option.some.inj h).symm
      subst ss
      trivial
  | cons A Fs ih =>
      intro prior ss h
      cases ha : fieldAnalyze E fuel f nu np ni (np + prior) A with
      | unresolved => simp only [fieldShapesFuel, ha] at h; cases h
      | refused why => simp only [fieldShapesFuel, ha] at h; cases h
      | permitted s idx =>
          cases ht : fieldShapesFuel E fuel f nu np ni ((np + prior) + 1) Fs with
          | none => simp only [fieldShapesFuel, ha, ht] at h; cases h
          | some rest =>
              have he : ss = s :: rest := by
                simpa only [fieldShapesFuel, ha, ht, Option.bind_some,
                  Option.map_some', pure, Option.some.injEq] using h.symm
              subst ss
              have ht' : fieldShapesFuel E fuel f nu np ni (np + (prior + 1)) Fs =
                  some rest := by
                simpa only [Nat.add_assoc] using ht
              exact ⟨PiCleanViews.of_admitted ha, ih (prior + 1) rest ht'⟩

/-- Select the clean evidence for an original field without changing its
position, normalization fuel, family identifier or complete argument spine. -/
theorem clean_at {E : ResolvedEnv} {fuel f nu np ni : Nat} :
    ∀ (Fs : List (Expr Nat)) (ss : List FieldShape) (prior : Nat),
      PropEval.FieldCertificates
        (fun _ A s => PiCleanViews.Clean E fuel f nu np ni A s) prior ss Fs →
      ∀ k : Fin Fs.length, ∃ s, PiCleanViews.Clean E fuel f nu np ni (Fs[k]) s := by
  intro Fs
  induction Fs with
  | nil => intro ss prior h k; exact Fin.elim0 k
  | cons A Fs ih =>
      intro ss prior h k
      cases ss with
      | nil => exact h.elim
      | cons s ss =>
          rcases k with ⟨k, hk⟩
          cases k with
          | zero => exact ⟨s, h.1⟩
          | succ k => exact ih ss (prior + 1) h.2 ⟨k, by simpa using hk⟩

/-- The syntactic view and clean-domain certificates come from one literal
admission computation, rather than independent assumptions. -/
theorem of_fields {E : ResolvedEnv} {fuel f nu np ni : Nat}
    (Fs : List (Expr Nat)) (prior : Nat) (ss : List FieldShape)
    (h : fieldShapesFuel E fuel f nu np ni (np + prior) Fs = some ss) :
    PiRawFieldViews.Views E fuel f nu np ni prior ss Fs ∧
      PropEval.FieldCertificates
        (fun _ A s => PiCleanViews.Clean E fuel f nu np ni A s) prior ss Fs :=
  ⟨PiRawFieldViews.of_fields Fs prior ss h, certificates_of_fields Fs prior ss h⟩

end Rcic.F3.PSet.CandidateFieldAdmission
