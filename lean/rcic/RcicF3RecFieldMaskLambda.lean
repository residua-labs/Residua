import rcic.RcicF3RecFieldMaskRelation

/-!
# The lambda case of bounded recursive-local masking

The syntactic body mode fixes one recursive depth for every reached
argument. In the stable case, reached body equality gives abstraction
equality. In the origin case, actual beta at the original argument
transports each body Origin to an application of the original lambda.
The masked body is empty at every member of its annotation, so LamProof
makes the masked lambda empty, including the empty-domain case.

Only the annotation's original-to-masked denotation equality and the
recursive body case are inputs. They are induction conclusions, not a
new semantic premise for StepAG. No fit of the masked assignment is used.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMask
open Rcic.Declarative RawFamily RecFieldOrigin

/-- The body hypothesis is at the SAME ordinary argument in the original
and masked assignments. Its mode is fixed before that argument is given. -/
theorem lambda_case (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ : Nat → Nat) (marks : Marks) (ρ η : Nat → PSet.{4})
    (A body B : Expr Nat) (hfreeA : occursConst fd.fref A = false)
    (hA : Equiv (den (mkM P (table P μ fd C)) σ ρ A)
      (den (mkM P (table P μ fd C)) σ η A))
    (ih : ∀ a, a ∈ Ed (mkM P (table P μ fd C))
        (den (mkM P (table P μ fd C)) σ ρ A) →
      Holds P μ fd C σ (ordinary marks) (vcons a ρ) (vcons a η) body B) :
    Holds P μ fd C σ marks ρ η (.lam A body) (.pi A B) := by
  let M := mkM P μ
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  cases hm : mode (ordinary marks) body with
  | none =>
      have hb : ∀ a, a ∈ Ed MC (den MC σ ρ A) →
          Equiv (den MC σ (vcons a ρ) body) (den MC σ (vcons a η) body) := by
        intro a ha
        simpa only [Holds, hm, Value] using ih a ha
      have he : Equiv (den MC σ ρ (.lam A body)) (den MC σ η (.lam A body)) :=
        lamVal_congr_on MC hA (den_resp MC σ ρ body) hb
      simpa only [Holds, mode, hm, Option.map, Value] using he
  | some m =>
      have hb : ∀ a, a ∈ Ed MC (den MC σ ρ A) →
          Equiv (den MC σ (vcons a η) body) pempty ∧
          Origin M fd C m
            (Ed MC (den MC σ (vcons a ρ) B))
            (Ed MD (den MD σ (vcons a ρ) B))
            (den MC σ (vcons a ρ) body) := by
        intro a ha
        simpa only [Holds, hm, Value] using ih a ha
      have hp : LamProof MC (den MC σ η A)
          (fun a => den MC σ (vcons a η) body) := by
        intro a ha
        exact (hb a (mem_congr_right (ed_congr MC hA).symm ha)).1
      have hempty : Equiv (den MC σ η (.lam A body)) pempty := by
        change Equiv (cond MC.dec (LamProof MC (den MC σ η A)
          (fun a => den MC σ (vcons a η) body)) pempty _) pempty
        rw [cond_pos hp]
        exact Equiv.rfl
      have hsame : den MC σ ρ A = den MD σ ρ A :=
        PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
          (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ A hfreeA ρ
      have ho : Origin M fd C (m + 1)
          (Ed MC (den MC σ ρ (.pi A B)))
          (Ed MD (den MD σ ρ (.pi A B))) (den MC σ ρ (.lam A body)) := by
        apply Origin.pi (den MC σ ρ A)
          (fun a => den MC σ (vcons a ρ) B)
          (fun a => den MD σ (vcons a ρ) B)
          (den_resp MC σ ρ B) (den_resp MD σ ρ B) Equiv.rfl
        · change Equiv (Ed M (piVal M (den MD σ ρ A)
            (fun a => den MD σ (vcons a ρ) B)))
            (Ed M (piVal M (den MC σ ρ A)
              (fun a => den MD σ (vcons a ρ) B)))
          simpa only [hsame] using
            (Equiv.rfl : Equiv (Ed M (piVal M (den MD σ ρ A)
              (fun a => den MD σ (vcons a ρ) B)))
              (Ed M (piVal M (den MD σ ρ A)
                (fun a => den MD σ (vcons a ρ) B))))
        · intro a ha
          exact (hb a ha).2.transport Equiv.rfl Equiv.rfl
            (beta_val MC (den_resp MC σ ρ body) ha).symm
      simpa only [Holds, mode, hm, Option.map, Value] using And.intro hempty ho

end Rcic.F3.PSet.RecFieldMask
