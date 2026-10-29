import rcic.RcicAnnLR3NoneSelfUniverse
import rcic.RcicAnnLR3OptionAdmittedLevels
import rcic.RcicAnnLR3EnvironmentEval

/-!
# Original sort-arm supply for an all-Option named code algebra

The new self-decoding none algebra is combined with the existing finite
NeutralCodes algebra. Cross-index coherence is proved by exact SortMember
uniqueness. Every field of CodeSystem is constructed, including the none
universe's own code, self membership, decoder and exact elimination.

The inherited EnvironmentEval image then gives the unchanged PairedTyGoal
and Ty_sort, with their original quantification over all Option-valued
valuations. No FiniteOn premise is added. A concrete admitted parameter
sort realizes the none case, and its source images agree with the new
retained self-universe kernel. Neither full Fundamental nor a bridge into
the finite Nat-indexed RCodeSound interface is asserted. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.NoneSortSupply

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

def Code : Option Nat → Value → Relation → Prop
  | none, V, R => NoneSelfUniverse.NoneCode V R
  | some k, V, R => NeutralCodes.Code (some k) V R

def UniversePER : Option Nat → Relation
  | none => NoneSelfUniverse.UniversePER
  | some k => NeutralCodes.UniversePER (some k)

theorem code_lawful {k : Option Nat} {V : Value} {R : Relation}
    (h : Code k V R) : Laws R := by
  cases k with
  | none => exact NoneSelfUniverse.noneCode_lawful h
  | some k => exact NeutralCodes.code_lawful h

theorem code_level {k : Option Nat} {V : Value} {R : Relation}
    (h : Code k V R) : SortMember k V := by
  cases k with
  | none => exact NoneSelfUniverse.noneCode_level h
  | some k => exact NeutralCodes.code_level h

theorem code_defined {k : Option Nat} {V : Value} {R : Relation}
    (h : Code k V R) : TypeDefined V := by
  cases k with
  | none => exact NoneSelfUniverse.noneCode_defined h
  | some k => exact NeutralCodes.code_defined h

theorem code_coherent {k l : Option Nat} {V : Value} {R S : Relation}
    (h : Code k V R) (g : Code l V S) : Same R S := by
  have hkl := sortMember_unique (code_level h) (code_level g) (code_defined h)
  cases hkl
  cases k with
  | none => exact NoneSelfUniverse.noneCode_coherent h g
  | some k => exact NeutralCodes.code_coherent h g

theorem universe_code (k : Option Nat) :
    Code (k.map Nat.succ) (universeValue k) (UniversePER k) := by
  cases k with
  | none => exact NoneSelfUniverse.self_code
  | some k => exact NeutralCodes.code_universe (some k)

theorem universe_member (k : Option Nat) :
    Member (UniversePER (k.map Nat.succ)) (universeValue k) := by
  cases k with
  | none => exact NoneSelfUniverse.raw_self_member
  | some k => exact NeutralCodes.universe_member (some k)

theorem universe_elim {k l : Option Nat} {R : Relation} {x : Value}
    (h : Code l (universeValue k) R) (hx : Member R x) :
    SortMember k x ∧ TypeDefined x := by
  have hu : Member (UniversePER k) x :=
    (code_coherent h (universe_code k) x x).mp hx
  cases k with
  | none => exact NoneSelfUniverse.raw_elimination hu
  | some k => exact NeutralCodes.universe_elim (NeutralCodes.code_universe (some k)) hu

def codeSystem : CodeSystem where
  Code := Code
  universePER := UniversePER
  lawful := code_lawful
  defined := code_defined
  level := code_level
  coherent := code_coherent
  universe_code := universe_code
  universe_member := universe_member
  universe_elim := universe_elim

/-- Universe relatedness supplies actual element codes in both branches.
The self none code is included and does not need a smaller derivation. -/
def universeTransport : UniverseTransport codeSystem where
  relate := by
    intro k V W h
    cases k with
    | none =>
        obtain ⟨R, hv, hw⟩ := NoneSelfUniverse.raw_transport h
        exact ⟨R, R, hv, hw, fun _ _ => Iff.rfl⟩
    | some k =>
        obtain ⟨R, S, hv, hw, hrs⟩ := NeutralCodes.universe_transport h
        exact ⟨R, S, hv, hw, hrs⟩

theorem none_decode {V : Value} (h : Member (codeSystem.universePER none) V) :
    ∃ R : Relation, codeSystem.Code none V R :=
  NoneSelfUniverse.raw_decode h

theorem none_self_decodes :
    codeSystem.Code none (universeValue none) (codeSystem.universePER none) ∧
    Member (codeSystem.universePER none) (universeValue none) :=
  ⟨universe_code none, universe_member none⟩

def semantics (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax) : AnnSemantics :=
  EnvironmentEval.annSemantics codeSystem E F

/-- This is the original PairedTyGoal, with no valuation restriction. -/
theorem paired_sort_goal (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (l : Level) :
    PairedTyGoal (semantics E F) E I n Γ (.sort l) (.sort (.succ l)) :=
  PairedArms.paired_sort_goal (semantics E F) E I n Γ l

theorem ty_sort_supplied (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (I : IotaIfaceA) (n : Nat) : PairedArms.Ty_sort (semantics E F) E I n :=
  paired_sort_goal E F I n

/-- The actual none arm has the new none universe's own relation. -/
theorem none_sort_judgment (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (Γ : LCtxA) (ν μ : Valuation) (ρ σ : EnvI) (l : Level)
    (hν : ValuationRel ν μ) (hl : eval ν l = none) :
    PairedJudgment (semantics E F) ν μ Γ ρ σ (.sort l) (.sort l) (.sort (.succ l)) := by
  have hm : eval μ l = none := (eval_of_valuationRel hν l).symm.trans hl
  have hsl : eval ν (.succ l) = none := by simp [eval, hl]
  have hsm : eval μ (.succ l) = none := by simp [eval, hm]
  unfold PairedJudgment
  simp only [(semantics E F).sort_image, hl, hm, hsl, hsm]
  exact ⟨none, NoneSelfUniverse.UniversePER, NoneSelfUniverse.UniversePER,
    CodePair.diagonal (universe_code none), NoneSelfUniverse.raw_self_member⟩

/-- Actual source typing, exact Option level, type image and term image
for a future Option-valued source-certificate bridge. -/
theorem retained_none_sort_certificate (E : ResolvedEnvA)
    (F : EnvironmentEval.FamilySyntax) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA)
    (ν : Valuation) (ρ : EnvI) (l : Level) (hl : eval ν l = none) :
    Nonempty (HasTyA E I n Γ (.sort l) (.sort (.succ l))) ∧
    Nonempty (HasTyA E I n Γ (.sort (.succ l)) (.sort (.succ (.succ l)))) ∧
    eval ν (.succ (.succ l)) = none ∧
    ValueEq ((semantics E F).image ν Γ ρ (.sort (.succ l)))
      NoneSelfUniverse.selfUniverse.{0}.value ∧
    NoneSelfUniverse.selfUniverse.relation NoneSelfUniverse.self.{0} NoneSelfUniverse.self ∧
    ValueEq (NoneSelfUniverse.selfUniverse.erase NoneSelfUniverse.self.{0})
      ((semantics E F).image ν Γ ρ (.sort l)) := by
  have hsl : eval ν (.succ l) = none := by simp [eval, hl]
  have hssl : eval ν (.succ (.succ l)) = none := by simp [eval, hl]
  refine ⟨⟨.sort Γ l⟩, ⟨.sort Γ (.succ l)⟩, hssl, ?_,
    NoneSelfUniverse.self_member, ?_⟩
  · rw [(semantics E F).sort_image, hsl]
    exact ValueEq.refl _
  · rw [(semantics E F).sort_image, hl]
    exact ValueEq.refl _

/-- Admission, source bounds, actual source derivation and empty paired
realization all hold for the concrete partial valuation. -/
theorem admitted_none_sort (F : EnvironmentEval.FamilySyntax) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 []
      UniverseDecoderBoundary.noneSort (.sort (.succ (.param 0)))) ∧
    exprLevelsBoundedA 1 UniverseDecoderBoundary.noneSort = true ∧
    ValuationRel UniverseDecoderBoundary.noneValuation UniverseDecoderBoundary.noneValuation ∧
    PairedRealises (semantics emptyEnvA F) UniverseDecoderBoundary.noneValuation
      UniverseDecoderBoundary.noneValuation [] EnvI.bot EnvI.bot ∧
    PairedJudgment (semantics emptyEnvA F) UniverseDecoderBoundary.noneValuation
      UniverseDecoderBoundary.noneValuation [] EnvI.bot EnvI.bot
      UniverseDecoderBoundary.noneSort UniverseDecoderBoundary.noneSort
      (.sort (.succ (.param 0))) :=
  ⟨⟨.empty⟩, ⟨.nil⟩, ⟨UniverseDecoderBoundary.source_none_sort⟩, rfl,
    ValuationRel.refl _, .nil _ _,
    none_sort_judgment emptyEnvA F [] _ _ _ _ (.param 0) (ValuationRel.refl _) rfl⟩

/-- The new source attachment keeps the full original sort comparison. -/
theorem evaluated_sort_eq_iff_eqN (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (Γ : LCtxA) (ρ : EnvI) (a b : Level) :
    (∀ ν : Valuation,
      ValueEq ((semantics E F).image ν Γ ρ (.sort a))
        ((semantics E F).image ν Γ ρ (.sort b))) ↔ eqN a b := by
  constructor
  · intro h ν
    have hv := h ν
    rw [(semantics E F).sort_image, (semantics E F).sort_image] at hv
    exact sort_code_injective hv
  · intro h ν
    rw [(semantics E F).sort_image, (semantics E F).sort_image, h ν]
    exact ValueEq.refl _

end Rcic.Declarative.Ann.LR3.NoneSortSupply
