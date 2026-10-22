import rcic.RcicAnnLR3InductiveCodes
import rcic.RcicAnnLR3FunctionCoreControls

/-!
# An inhabited source product and the legacy-universe extension boundary

The dependent-product code, its native source image, and a full-domain
reflected member are supplied. The empty admitted environment and all
children of its source formation rule are inhabited.

The negative result is limited to literal retention of old universe
carriers: such a carrier does not acquire the new product by changing the
outer Code relation. It is not a refutation of expanded universes or an
admitted source class. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.InductiveCodeControls

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements InductiveCodes

def zeroValuation : Valuation := fun _ => some 0
def productType : ExprA :=
  .pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
def productClosure : Value := denI EnvI.bot (.lam (sortTerm (some 0)) (sortTerm (some 0)))
def productValue : Value := piValue (some 1) (universeValue (some 0)) productClosure
def productPER : Relation :=
  FunctionPER NeutralPi.applyValue (NeutralCodes.UniversePER (some 0))
    (fun _ => NeutralCodes.UniversePER (some 0))

theorem closure_application (x : Value) :
    ValueEq (NeutralPi.applyValue productClosure x) (universeValue (some 0)) :=
  (FunctionEval.native_lambda_application EnvI.bot (sortTerm (some 0))
    (sortTerm (some 0)) x).trans
      (FunctionEval.sortTerm_environment (EnvI.cons x EnvI.bot) EnvI.bot (some 0))

theorem product_code : CodeI (some 1) productValue productPER := by
  apply CodeI.pi (kA := some 1) (kB := some 1)
    (A := universeValue (some 0)) (C := productClosure)
    (RA := NeutralCodes.UniversePER (some 0))
    (RB := fun _ => NeutralCodes.UniversePER (some 0))
  · exact .old (NeutralCodes.code_universe (some 0))
  · intro x y _
    exact code_value_eq (.old (NeutralCodes.code_universe (some 0)))
      (closure_application x).symm
  · exact fun _ _ _ _ _ => Iff.rfl
  · exact ValueEq.refl _
  · exact fun _ _ => Iff.rfl

theorem product_image :
    ValueEq (UnitModel.denote zeroValuation EnvI.bot productType) productValue :=
  (piValue_native EnvI.bot (some 1) (sortTerm (some 0)) (sortTerm (some 0))).symm

theorem product_source_code :
    CodeI (some 1) (UnitModel.denote zeroValuation EnvI.bot productType) productPER :=
  code_value_eq product_code product_image.symm

theorem product_reflected_member (name : Nat) :
    Member productPER (UnifiedPi.universeGraph (some 0) name) :=
  UnifiedPi.universeGraph_function_member (NeutralCodes.UniversePER (some 0)) (some 0) name

theorem product_universe_member : Member (UniverseI (some 1)) productValue :=
  code_member_universeI product_code

theorem product_not_old_universe : ¬ Member (NeutralCodes.UniversePER (some 1)) productValue := by
  intro h
  obtain ⟨R, hR⟩ := NeutralCodes.decode (NeutralCodes.code_universe (some 1)) h
  exact old_code_not_pi hR (old_code_bot (NeutralCodes.code_universe (some 0))) (ValueEq.refl _)

theorem enlarged_universe_not_legacy :
    ¬ Same (UniverseI (some 1)) (NeutralCodes.UniversePER (some 1)) := by
  intro h
  exact product_not_old_universe ((h productValue productValue).mp product_universe_member)

theorem enlarged_universe_not_code {l : Option Nat} :
    ¬ CodeI l (universeValue (some 1)) (UniverseI (some 1)) := by
  intro h
  exact enlarged_universe_not_legacy
    (code_coherent h (.old (NeutralCodes.code_universe (some 1))))

def source_admitted : EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA := .empty
def source_domain :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort [] .zero
def source_codomain :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [.assumption (.sort .zero)]
      (.sort .zero) (.sort (.succ .zero)) := .sort _ .zero
def source_product :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] productType
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero) source_domain source_codomain

def legacyModel : AnnSemantics := FunctionEval.annSemantics legacyUniverseSystem

theorem domainIH :
    PairedTyGoal legacyModel emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.sort .zero) (.sort (.succ .zero)) :=
  PairedArms.ty_sort_supplied legacyModel _ _ _ [] .zero

theorem codomainIH :
    PairedTyGoal legacyModel emptyEnvA (iotaIfaceA emptyEnvA) 0
      [.assumption (.sort .zero)] (.sort .zero) (.sort (.succ .zero)) :=
  PairedArms.ty_sort_supplied legacyModel _ _ _ [.assumption (.sort .zero)] .zero

/-- The exact source arm fails for this concrete legacy-universe model,
with actual source children, paired IHs, admission and realization. -/
theorem legacy_ty_pi_refuted :
    ¬ PairedArms.Ty_pi legacyModel emptyEnvA (iotaIfaceA emptyEnvA) 0 := by
  intro h
  have hg := h [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    source_domain source_codomain domainIH codomainIH
  obtain ⟨k, R, S, hp, hm⟩ := hg .nil zeroValuation zeroValuation EnvI.bot EnvI.bot
    (ValuationRel.refl _) (.nil _ _)
  have hc := hp.left_code
  change CodeI k (universeValue (some 1)) R at hc
  have ht := code_coherent hc (.old (NeutralCodes.code_universe (some 1)))
  change R (UnitModel.denote zeroValuation EnvI.bot productType)
    (UnitModel.denote zeroValuation EnvI.bot productType) at hm
  rw [NeutralCodes.valueEq_eq product_image] at hm
  exact product_not_old_universe ((ht _ _).mp hm)

theorem legacy_arm_premises_inhabited :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.sort .zero) (.sort (.succ .zero))) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [.assumption (.sort .zero)]
      (.sort .zero) (.sort (.succ .zero))) ∧
    PairedTyGoal legacyModel emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.sort .zero) (.sort (.succ .zero)) ∧
    PairedTyGoal legacyModel emptyEnvA (iotaIfaceA emptyEnvA) 0
      [.assumption (.sort .zero)] (.sort .zero) (.sort (.succ .zero)) ∧
    PairedRealises legacyModel zeroValuation zeroValuation [] EnvI.bot EnvI.bot ∧
    (¬ PairedArms.Ty_pi legacyModel emptyEnvA (iotaIfaceA emptyEnvA) 0) :=
  ⟨⟨source_admitted⟩, ⟨.nil⟩, ⟨source_domain⟩, ⟨source_codomain⟩,
    domainIH, codomainIH, .nil _ _, legacy_ty_pi_refuted⟩

theorem control_inhabited (name : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 [] productType
      (.sort (.imax (.succ .zero) (.succ .zero)))) ∧
    CodeI (some 1) (UnitModel.denote zeroValuation EnvI.bot productType) productPER ∧
    Laws productPER ∧ Member productPER (UnifiedPi.universeGraph (some 0) name) ∧
    Member (UniverseI (some 1)) productValue ∧
    (¬ Member (NeutralCodes.UniversePER (some 1)) productValue) :=
  ⟨⟨source_admitted⟩, ⟨.nil⟩, ⟨source_product⟩, product_source_code,
    code_laws product_code, product_reflected_member name,
    product_universe_member, product_not_old_universe⟩

end Rcic.Declarative.Ann.LR3.InductiveCodeControls
