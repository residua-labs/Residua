import rcic.RcicAnnLR3NeutralPER
import rcic.RcicAnnLR3TypedCoverageBoundary

/-!
# The admitted empty axiom and Loop as positive neutral controls

The old concrete code system is extended by composition at its empty
family value. Its universe relations, exact levels and code coherence are
retained. The additional carrier consists of actual nonbottom neutral
constants of the inherited semantic domain; no constructor evidence is
fabricated. This supplies the complete const constructor contract for the
admitted two-member empty-axiom environment, and actual Realises witnesses
for the empty-family and Loop contexts.

This small code system is a boundary control, not a complete interpretation
of Pi, arbitrary admitted families or their recursors. Its positive
controls are not an instance of AllAdmittedFundamental. `closure_claim = 0`.
-/
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Declarative.Ann.LR3.NeutralControls
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements TypedArms TruthAxiomBoundary

def Neutral (x : Value) : Prop := ∃ r, NeutralPER.AtomNeutral r x

theorem neutral_atom (r : Nat) : Neutral (NeutralPER.neutralAtom r) :=
  ⟨r, NeutralPER.neutralAtom_is_neutral r⟩

theorem neutral_extensional : NeutralPER.ExtensionalNeutral Neutral := by
  intro x y h
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, (NeutralPER.atomNeutral_extensional r h).mp hr⟩
  · rintro ⟨r, hr⟩; exact ⟨r, (NeutralPER.atomNeutral_extensional r h).mpr hr⟩

def carrier : Relation := NeutralPER.ProofPER Neutral EmptyEvidence

theorem carrier_laws : Laws carrier := NeutralPER.proofPER_laws _ _

theorem carrier_iff (x y : Value) : carrier x y ↔ Neutral x ∧ Neutral y := by
  constructor
  · intro h
    exact ⟨(NeutralPER.member_of_false_truth_iff Neutral emptyEvidence_false x).mp ⟨h.1, h.1⟩,
      (NeutralPER.member_of_false_truth_iff Neutral emptyEvidence_false y).mp ⟨h.2, h.2⟩⟩
  · intro h; exact ⟨.inr h.1, .inr h.2⟩

theorem carrier_atom (r : Nat) : Member carrier (NeutralPER.neutralAtom r) :=
  NeutralPER.neutral_member _ _ (neutral_atom r)

/-- Extend just the old empty-family carrier; universe carriers are kept
exact. The original relation is included, not replaced or redefined. -/
def ExtendAt (V : Value) (R : Relation) (x y : Value) : Prop :=
  R x y ∨ (V = TypedConstantModel.emptyValue ∧ Neutral x ∧ Neutral y)

theorem extend_old {V : Value} {R : Relation} {x y : Value} (h : R x y) :
    ExtendAt V R x y := .inl h

theorem extend_empty : Same
    (ExtendAt TypedConstantModel.emptyValue emptyCarrier) carrier := by
  intro x y
  constructor
  · intro h
    rcases h with h | h
    · exact (emptyEvidence_false h.1).elim
    · exact (carrier_iff x y).mpr h.2
  · intro h; exact .inr ⟨rfl, (carrier_iff x y).mp h⟩

theorem extend_universe (k : Option Nat) (R : Relation) :
    Same (ExtendAt (universeValue k) R) R := by
  intro x y
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact (TypedConstantModel.emptyValue_ne_universe k h.1.symm).elim
  · exact Or.inl

theorem laws_of_same {R S : Relation} (h : Same R S) (hs : Laws S) : Laws R where
  symm := fun hxy => (h _ _).mpr (hs.symm ((h _ _).mp hxy))
  trans := fun hxy hyz => (h _ _).mpr (hs.trans ((h _ _).mp hxy) ((h _ _).mp hyz))

theorem extended_laws {k : Option Nat} {V : Value} {R : Relation}
    (hc : TypedConstantModel.Code k V R) : Laws (ExtendAt V R) := by
  rcases TypedConstantModel.code_shape hc with ⟨_, hv, hr⟩ | ⟨j, _, hv, hr⟩
  · rw [hv, hr]; exact laws_of_same extend_empty carrier_laws
  · rw [hv, hr]; exact laws_of_same (extend_universe j _) (sortPER_laws j)

/-- A new code relation over the old one; all old statements stay intact. -/
def Code (k : Option Nat) (V : Value) (R : Relation) : Prop :=
  ∃ S, TypedConstantModel.Code k V S ∧ Same R (ExtendAt V S)

theorem code_lawful {k : Option Nat} {V : Value} {R : Relation}
    (hc : Code k V R) : Laws R := by
  obtain ⟨S, hS, hs⟩ := hc
  exact laws_of_same hs (extended_laws hS)

theorem code_defined {k : Option Nat} {V : Value} {R : Relation}
    (hc : Code k V R) : TypeDefined V := by
  obtain ⟨S, hs, _⟩ := hc
  exact TypedConstantModel.code_defined hs

theorem code_level {k : Option Nat} {V : Value} {R : Relation}
    (hc : Code k V R) : SortMember k V := by
  obtain ⟨S, hs, _⟩ := hc
  exact TypedConstantModel.code_level hs

theorem code_coherent {k l : Option Nat} {V : Value} {R S : Relation}
    (h : Code k V R) (g : Code l V S) : Same R S := by
  obtain ⟨R₀, hr, hR⟩ := h
  obtain ⟨S₀, hs, hS⟩ := g
  have same := TypedConstantModel.code_coherent hr hs
  intro x y
  apply (hR x y).trans
  apply Iff.trans _ (hS x y).symm
  exact or_congr (same x y) Iff.rfl

theorem code_empty : Code (some 0) TypedConstantModel.emptyValue carrier :=
  ⟨emptyCarrier, TypedConstantModel.Code.empty, fun x y => (extend_empty x y).symm⟩

theorem code_universe (k : Option Nat) :
    Code (k.map Nat.succ) (universeValue k) (SortPER k) :=
  ⟨SortPER k, TypedConstantModel.Code.univ k, fun x y => (extend_universe k _ x y).symm⟩

theorem code_universe_elim {k l : Option Nat} {R : Relation} {x : Value}
    (hc : Code l (universeValue k) R) (hm : Member R x) :
    SortMember k x ∧ TypeDefined x := by
  obtain ⟨S, hs, he⟩ := hc
  exact TypedConstantModel.code_universe_elim hs
    ((extend_universe k S x x).mp ((he x x).mp hm))

def codeSystem : CodeSystem where
  Code := Code
  universePER := SortPER
  lawful := code_lawful
  defined := code_defined
  level := code_level
  coherent := code_coherent
  universe_code := code_universe
  universe_member := TypedConstantModel.codeSystem.universe_member
  universe_elim := code_universe_elim

/-- The two local source families have the same empty constructor closure.
Variables are their environment values and axioms are neutral constants. -/
def image (ν : Valuation) (_Γ : LCtxA) (ρ : EnvI) : ExprA → Value
  | .sort l => universeValue (eval ν l)
  | .bvar i => ρ i
  | .const r _ls =>
      if r = 80 ∨ r = 60 then TypedConstantModel.emptyValue else NeutralPER.neutralAtom r
  | e => UnitModel.denote ν ρ e

def model : AnnSemantics where
  toCodeSystem := codeSystem
  image := image
  sort_image := fun _ _ _ _ => rfl

theorem emptyType_goal (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    TyGoal model E I n Γ emptyType (.sort .zero) := by
  intro _ ν ρ _
  refine ⟨some 1, SortPER (some 0), code_universe (some 0), sort_defined _ _, ?_⟩
  exact ⟨TypedConstantModel.emptyValue_member, TypedConstantModel.emptyValue_defined,
    ValueEq.refl _⟩

theorem badTerm_goal (Γ : LCtxA) :
    TyGoal model badEnv (iotaIfaceA badEnv) 0 Γ badTerm emptyType := by
  intro _ ν ρ _
  exact ⟨some 0, carrier, code_empty, TypedConstantModel.emptyValue_defined, carrier_atom 81⟩

/-- Every member lookup in the admitted empty-axiom environment is handled.
The const arm's original premises and formation IH are retained. -/
theorem const_arm : Ty_const model badEnv (iotaIfaceA badEnv) 0 := by
  intro Γ r ls m u hres hlen _hwf _hT _ih
  by_cases h81 : r = 81
  · subst r
    have hm : badAxiom = m := Option.some.inj hres
    subst m
    have hnil : ls = [] := List.length_eq_zero.mp hlen
    subst ls
    exact badTerm_goal Γ
  · by_cases h80 : r = 80
    · subst r
      have hm : emptyFamily = m := Option.some.inj hres
      subst m
      have hnil : ls = [] := List.length_eq_zero.mp hlen
      subst ls
      exact emptyType_goal badEnv (iotaIfaceA badEnv) 0 Γ
    · have hn : badEnv.members r = none := by
        simp only [badEnv, familyEnv, extendEnvA, emptyEnvA, if_neg h81, if_neg h80]
      rw [hn] at hres
      cases hres

def genericOne : EnvI := EnvI.cons (NeutralPER.neutralAtom 1000) EnvI.bot

theorem empty_context_realises (ν : Valuation) :
    Realises model ν TypedCoverageBoundary.emptyContext genericOne :=
  .assumption (.nil EnvI.bot) code_empty (carrier_atom 1000)

theorem loop_context_realises (ν : Valuation) :
    Realises model ν TypedInductive.loopContext genericOne :=
  .assumption (.nil EnvI.bot) code_empty (carrier_atom 1000)

theorem loop_family_agrees : Same carrier
    (NeutralPER.FamilyPER Neutral TypedInductive.loopSignature ()) :=
  NeutralPER.proofPER_same
    ⟨fun h => (emptyEvidence_false h).elim,
      fun h => (TypedInductive.loopClosure_false h).elim⟩ (fun _ => Iff.rfl)

theorem loop_major_member :
    Member (NeutralPER.FamilyPER Neutral TypedInductive.loopSignature ()) (genericOne 0) :=
  (loop_family_agrees _ _).mp (carrier_atom 1000)

theorem neutral_controls_inhabited :
    Nonempty (EnvWfA (iotaIfaceA badEnv) badEnv) ∧
    Nonempty (HasTyA badEnv (iotaIfaceA badEnv) 0 [] badTerm emptyType) ∧
    Ty_const model badEnv (iotaIfaceA badEnv) 0 ∧
    TyGoal model badEnv (iotaIfaceA badEnv) 0 [] emptyType (.sort .zero) ∧
    TyGoal model badEnv (iotaIfaceA badEnv) 0 [] badTerm emptyType ∧
    Nonempty (CtxWfA familyEnv (iotaIfaceA familyEnv) 0 TypedCoverageBoundary.emptyContext) ∧
    (∀ ν, Realises model ν TypedCoverageBoundary.emptyContext genericOne) ∧
    Nonempty (EnvWfA (iotaIfaceA pinLoopEnvA) pinLoopEnvA) ∧
    Nonempty (CtxWfA pinLoopEnvA (iotaIfaceA pinLoopEnvA) 0 TypedInductive.loopContext) ∧
    (∀ ν, Realises model ν TypedInductive.loopContext genericOne) ∧
    Member (NeutralPER.FamilyPER Neutral TypedInductive.loopSignature ()) (genericOne 0) ∧
    (¬ EmptyEvidence) ∧ (¬ TypedInductive.Closure TypedInductive.loopSignature ()) :=
  ⟨⟨badEnv_admitted _⟩, ⟨badTerm_typed _⟩, const_arm,
    emptyType_goal badEnv (iotaIfaceA badEnv) 0 [], badTerm_goal [],
    ⟨TypedCoverageBoundary.emptyContext_wf⟩, empty_context_realises, ⟨pinLoop_wf⟩,
    ⟨TypedInductive.loopContext_wf⟩, loop_context_realises, loop_major_member,
    emptyEvidence_false, TypedInductive.loopClosure_false⟩

end Rcic.Declarative.Ann.LR3.NeutralControls
