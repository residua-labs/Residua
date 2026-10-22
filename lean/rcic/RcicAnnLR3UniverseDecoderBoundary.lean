import rcic.RcicAnnLR3InductiveCodes
import rcic.RcicAnnLR3FunctionCoreControls

/-!
# The positive decoder-constructor boundary at `none`

This is a boundary for one proposed universe construction, not for the
admitted source class or for expanded universes in general. `CodeU U`
uses ordinary relation indices and fixes the proposed universe carriers
as the parameter `U`. Its universe constructor requires a smaller code
derivation for every member of the proposed universe. The decoder's
relation-valued function is explicit data; it is not selected from a
propositional existential.

The neutral, proof and native product clauses are included. No legacy
universe clause is retained. Nevertheless, if `universeValue none` is a
member of `U none`, no derivation can code that value: a universe case
would require a strictly smaller derivation of the same value. The proof
is ordinary induction on the code derivation, not a level-rank argument.

The existing universe supplies a concrete self-member, and an actual
sort in the admitted empty source environment evaluates to this `none`
case. No valuation or admitted environment is excluded. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.UniverseDecoderBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

/-- Explicit proposed universe carriers and ordinary PER indices. The
decoder function is a constructor argument, never chosen from Prop. -/
inductive CodeU (U : Option Nat → Relation) : Option Nat → Value → Relation → Prop
  | neutral {k : Option Nat} {name : Nat} {V : Value} {R : Relation}
      (value : ValueEq V (NeutralCodes.neutralTypeValue k name))
      (carrier : Same R (NeutralCodes.El (.neutralType k name))) : CodeU U k V R
  | proof {P : Prop} {V : Value} {R : Relation}
      (value : ValueEq V (NeutralCodes.proofCodeValue P))
      (carrier : Same R (NeutralCodes.El (.proof P))) : CodeU U (some 0) V R
  | pi {kA kB : Option Nat} {A C V : Value} {RA R : Relation} {RB : Value → Relation}
      (domain : CodeU U kA A RA)
      (fibres : ∀ x y, RA x y → CodeU U kB (NeutralPi.applyValue C x) (RB x))
      (coherent : FamilyCoherent RA RB)
      (value : ValueEq V (InductiveCodes.piValue (InductiveCodes.imaxLevel kA kB) A C))
      (carrier : Same R (FunctionPER NeutralPi.applyValue RA RB)) :
      CodeU U (InductiveCodes.imaxLevel kA kB) V R
  | univ {k : Option Nat} {V : Value} {R : Relation}
      (decoded : Value → Relation)
      (decode : ∀ x, Member (U k) x → CodeU U k x (decoded x))
      (value : ValueEq V (universeValue k))
      (carrier : Same R (U k)) : CodeU U (k.map Nat.succ) V R

theorem code_bot {U : Option Nat → Relation} {k : Option Nat} {V : Value} {R : Relation}
    (h : CodeU U k V R) : V .bot := by
  cases h with
  | neutral hv _ => exact (hv .bot).mpr (Or.inl rfl)
  | proof hv _ => exact (hv .bot).mpr (Or.inl rfl)
  | pi _ _ _ hv _ => exact (hv .bot).mpr (Or.inl rfl)
  | univ _ _ hv _ => exact (hv .bot).mpr (ApproxI.bot _ _)

theorem code_level {U : Option Nat → Relation} {k : Option Nat} {V : Value} {R : Relation}
    (h : CodeU U k V R) : SortMember k V := by
  cases h with
  | neutral hv _ =>
    exact sortMember_congr hv.symm (NeutralCodes.reify_level (.neutralType _ _))
  | proof hv _ => exact sortMember_congr hv.symm (NeutralCodes.reify_level (.proof _))
  | pi _ _ _ hv _ => exact sortMember_congr hv.symm (InductiveCodes.piValue_level _ _ _)
  | univ _ _ hv _ => exact sortMember_congr hv.symm (sort_member _ _)

theorem code_laws {U : Option Nat → Relation} (hU : ∀ k, Laws (U k))
    {k : Option Nat} {V : Value} {R : Relation} (h : CodeU U k V R) : Laws R := by
  induction h with
  | @neutral k name V R _ hr =>
    have hE := NeutralCodes.el_laws (.neutralType k name)
    exact ⟨fun hxy => (hr _ _).mpr (hE.symm ((hr _ _).mp hxy)),
      fun hxy hyz => (hr _ _).mpr (hE.trans ((hr _ _).mp hxy) ((hr _ _).mp hyz))⟩
  | @proof P V R _ hr =>
    have hE := NeutralCodes.el_laws (.proof P)
    exact ⟨fun hxy => (hr _ _).mpr (hE.symm ((hr _ _).mp hxy)),
      fun hxy hyz => (hr _ _).mpr (hE.trans ((hr _ _).mp hxy) ((hr _ _).mp hyz))⟩
  | pi _ _ hc _ hr ihA ihB =>
    have hF := functionPER_laws NeutralPi.applyValue ihA (fun x hx => ihB x x hx) hc
    exact ⟨fun hxy => (hr _ _).mpr (hF.symm ((hr _ _).mp hxy)),
      fun hxy hyz => (hr _ _).mpr (hF.trans ((hr _ _).mp hxy) ((hr _ _).mp hyz))⟩
  | univ _ _ _ hr _ =>
    exact ⟨fun hxy => (hr _ _).mpr ((hU _).symm ((hr _ _).mp hxy)),
      fun hxy hyz => (hr _ _).mpr ((hU _).trans ((hr _ _).mp hxy) ((hr _ _).mp hyz))⟩

/-- The recursive decoder asks for its own self-member as an earlier
derivation. Neutral, proof and product values cannot discharge that request. -/
theorem no_self_universe_value {U : Option Nat → Relation}
    (hself : Member (U none) (universeValue none))
    {k : Option Nat} {V : Value} {R : Relation} (h : CodeU U k V R) :
    ¬ ValueEq V (universeValue none) := by
  induction h with
  | neutral hv _ =>
    intro he
    exact NeutralCodes.neutralType_not_universe _ _ _ (hv.symm.trans he)
  | proof hv _ =>
    intro he
    exact NeutralCodes.proofCode_not_universe _ _ (hv.symm.trans he)
  | pi hA _ _ hv _ _ _ =>
    intro he
    exact InductiveCodes.old_code_not_pi (NeutralCodes.code_universe none)
      (code_bot hA) (he.symm.trans hv)
  | @univ k V R decoded decode hv hr ih =>
    intro he
    have hk : k = none := sort_code_injective (hv.symm.trans he)
    subst k
    exact ih (universeValue none) hself (ValueEq.refl _)

theorem no_self_universe_code {U : Option Nat → Relation}
    (hself : Member (U none) (universeValue none)) {k : Option Nat} {R : Relation} :
    ¬ CodeU U k (universeValue none) R := by
  intro h
  exact no_self_universe_value hself h (ValueEq.refl _)

theorem legacy_self_member :
    Member (NeutralCodes.UniversePER none) (universeValue none) :=
  NeutralCodes.universe_member none

theorem legacy_no_self_universe_code {k : Option Nat} {R : Relation} :
    ¬ CodeU NeutralCodes.UniversePER k (universeValue none) R :=
  no_self_universe_code legacy_self_member

/-- A numeric stage attached only to the semantic level cannot decrease
strictly when decoding every universe, since successor fixes `none`. -/
theorem no_strict_level_rank (rank : Option Nat → Nat) :
    ¬ (∀ k, rank k < rank (k.map Nat.succ)) := by
  intro h
  exact Nat.lt_irrefl (rank none) (h none)

def noneValuation : Valuation := fun _ => none
def noneSort : ExprA := .sort (.param 0)

def source_admitted : EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA := .empty

def source_none_sort :
    HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 [] noneSort
      (.sort (.succ (.param 0))) := .sort [] (.param 0)

theorem source_none_image :
    ValueEq (UnitModel.denote noneValuation EnvI.bot noneSort) (universeValue none) :=
  ValueEq.refl _

theorem source_none_type_image :
    ValueEq (UnitModel.denote noneValuation EnvI.bot (.sort (.succ (.param 0))))
      (universeValue none) := ValueEq.refl _

theorem admitted_decoder_boundary :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 1 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 1 [] noneSort
      (.sort (.succ (.param 0)))) ∧
    Member (NeutralCodes.UniversePER none) (universeValue none) ∧
    (∀ k R, ¬ CodeU NeutralCodes.UniversePER k
      (UnitModel.denote noneValuation EnvI.bot noneSort) R) := by
  refine ⟨⟨source_admitted⟩, ⟨.nil⟩, ⟨source_none_sort⟩, legacy_self_member, ?_⟩
  intro k R
  rw [NeutralCodes.valueEq_eq source_none_image]
  exact legacy_no_self_universe_code

end Rcic.Declarative.Ann.LR3.UniverseDecoderBoundary
