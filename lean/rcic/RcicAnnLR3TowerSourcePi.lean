import rcic.RcicAnnLR3TowerCodeSystem
import rcic.RcicAnnLR3EnvironmentPi

/-!
# Source products and sorts are codes of the tower system

For any evaluator environment, valuation and raw environment, the actual
image of a source sort is the tower's universe code image. Under the
type-formation premises of the domain and the codomain body, the actual
image of a source product is the image of a well-formed tower product code;
its tower index is the evaluated `imax` level. The premises are a
well-formed domain code with the domain's actual image, and well-formed fibre
codes whose images agree with the body's actual images at every raw
argument. Hence the source product's type value
is a code of `TowerCodeSystem.codeSystem` at its evaluated level, with the
product relation.

The raw fibre-image function is the body's actual evaluation, so its finite
demand and bottom observation are the inherited evaluator laws
(`body_legalFiniteDemand`, `denote_bot`). These are the type-formation
parts of the `Ty_pi`/`Ty_sort` arms; the arms themselves, readback and the
member arms are not claimed. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.TowerSourcePi

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements
open TypeZeroTowerProbe TowerCodeSystem

theorem imaxLevel_some (a b : Nat) :
    InductiveCodes.imaxLevel (some a) (some b) = some (imaxN a b) := by
  cases b <;> rfl

theorem eval_imax_some (ν : Valuation) {u v : Level} {a b : Nat}
    (hu : eval ν u = some a) (hv : eval ν v = some b) :
    eval ν (.imax u v) = some (imaxN a b) := by
  rw [← InductiveCodes.imaxLevel_eval, hu, hv, imaxLevel_some]

/-- A source sort's image is the universe code's image. -/
theorem source_sort_code (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (l : Level) {k : Nat} (hl : eval ν l = some k) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.sort l)) (image (Code.univ k)) ∧
    codeSystem.Code (some (k + 1)) (EnvironmentEval.denote E F ν ρ (.sort l))
      (El (Code.univ k)) := by
  have himg : ValueEq (EnvironmentEval.denote E F ν ρ (.sort l)) (image (Code.univ k)) := by
    have h : EnvironmentEval.denote E F ν ρ (.sort l) = universeValue (eval ν l) :=
      (EnvironmentEval.annSemantics codeSystem E F).sort_image ν [] ρ l
    rw [h, hl]
    exact ValueEq.refl _
  exact ⟨himg, ⟨⟨Code.univ k, WF.univ k, himg⟩,
    fun x y => ((elU_of_wf (WF.univ k) himg) x y).symm⟩⟩

/-- The product code determined by a source product's actual images. -/
def productCode (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (B : ExprA) {a b : Nat} (cA : Code a) (cB : Value → Code b) :
    Code (imaxN a b) :=
  Code.pi cA (fun x => EnvironmentEval.denote E F ν (EnvI.cons x ρ) B) cB

theorem productCode_wf (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (B : ExprA) {a b : Nat} {cA : Code a}
    {cB : Value → Code b} (hA : WF cA) (hB : ∀ x, WF (cB x))
    (fibre : ∀ x,
      ValueEq (image (cB x)) (EnvironmentEval.denote E F ν (EnvI.cons x ρ) B)) :
    WF (productCode E F ν ρ B cA cB) :=
  WF.pi hA hB (EnvironmentEval.body_legalFiniteDemand E F ν ρ B _)
    (fun _ => EnvironmentEval.denote_bot E F ν _ B) fibre

/-- A source product's actual image is the product code's image, and it is a
code of the tower system at its evaluated level with the product relation. -/
theorem source_pi_code (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A B : ExprA) (u v : Level) {a b : Nat}
    (hu : eval ν u = some a) (hv : eval ν v = some b)
    {cA : Code a} {cB : Value → Code b} (hA : WF cA) (hB : ∀ x, WF (cB x))
    (hAimg : ValueEq (EnvironmentEval.denote E F ν ρ A) (image cA))
    (fibre : ∀ x,
      ValueEq (image (cB x)) (EnvironmentEval.denote E F ν (EnvI.cons x ρ) B)) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.pi A u B v))
        (image (productCode E F ν ρ B cA cB)) ∧
      codeSystem.Code (eval ν (.imax u v)) (EnvironmentEval.denote E F ν ρ (.pi A u B v))
        (El (productCode E F ν ρ B cA cB)) := by
  have himg : ValueEq (EnvironmentEval.denote E F ν ρ (.pi A u B v))
      (image (productCode E F ν ρ B cA cB)) := by
    have h := EnvironmentEval.denote_pi_value E F ν ρ A B u v
    rw [hu, hv, imaxLevel_some, NeutralCodes.valueEq_eq hAimg,
      NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_graph E F ν ρ A B u)] at h
    exact h
  refine ⟨himg, ?_⟩
  rw [eval_imax_some ν hu hv]
  exact ⟨⟨_, productCode_wf E F ν ρ B hA hB fibre, himg⟩, fun x y =>
    ((elU_of_wf (productCode_wf E F ν ρ B hA hB fibre) himg) x y).symm⟩

end Rcic.Declarative.Ann.LR3.TowerSourcePi
