import rcic.RcicAnnLR3TaggedKClosure
import rcic.RcicAnnLR3PairedStatements

/- Guarded tagged-code reading control. closure_claim = 0.
   Source parsing, minor production, neutral identity production and their image
   equations are separate obligations. The strong CodeRelated relation and its
   retained KernelIso are unchanged. -/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TaggedSaturatedTower TaggedKClosure

namespace GuardedCodeRead

universe u

inductive Read {k : Nat} (G : Prop) (minor fallback : Code.{u} k) :
    Code.{u} k → Prop where
  | yes : G → Read G minor fallback minor
  | no : (¬ G) → Read G minor fallback fallback

theorem read_of_guard {k : Nat} {G : Prop} (minor fallback : Code.{u} k)
    (hG : G) : Read G minor fallback minor :=
  .yes hG

theorem read_of_not_guard {k : Nat} {G : Prop} (minor fallback : Code.{u} k)
    (hG : ¬ G) : Read G minor fallback fallback :=
  .no hG

theorem output_eq_of_guard {k : Nat} {G : Prop}
    {minor fallback C : Code.{u} k} (hG : G)
    (hC : Read G minor fallback C) : C = minor := by
  cases hC with
  | yes _ => rfl
  | no hN => exact False.elim (hN hG)

theorem output_eq_of_not_guard {k : Nat} {G : Prop}
    {minor fallback C : Code.{u} k} (hG : ¬ G)
    (hC : Read G minor fallback C) : C = fallback := by
  cases hC with
  | yes hY => exact False.elim (hG hY)
  | no _ => rfl

theorem functional {k : Nat} {G : Prop}
    {minor fallback C D : Code.{u} k}
    (hC : Read G minor fallback C) (hD : Read G minor fallback D) : C = D := by
  cases hC with
  | yes hG => exact (output_eq_of_guard hG hD).symm
  | no hG => exact (output_eq_of_not_guard hG hD).symm

theorem exists_iff {k : Nat} (G : Prop) (minor fallback : Code.{u} k) :
    (∃ C, Read G minor fallback C) ↔ G ∨ ¬ G := by
  constructor
  · rintro ⟨C, hC⟩
    cases hC with
    | yes hG => exact Or.inl hG
    | no hG => exact Or.inr hG
  · intro h
    cases h with
    | inl hG => exact ⟨minor, .yes hG⟩
    | inr hG => exact ⟨fallback, .no hG⟩

theorem existsUnique_iff {k : Nat} (G : Prop) (minor fallback : Code.{u} k) :
    (∃ C, Read G minor fallback C ∧ ∀ D, Read G minor fallback D → D = C) ↔
      G ∨ ¬ G := by
  constructor
  · rintro ⟨C, hC, _⟩
    exact (exists_iff G minor fallback).mp ⟨C, hC⟩
  · intro h
    obtain ⟨C, hC⟩ := (exists_iff G minor fallback).mpr h
    exact ⟨C, hC, fun D hD => functional hD hC⟩

def ofDecision {k : Nat} {G : Prop} (d : Decidable G)
    (minor fallback : Code.{u} k) : Code.{u} k :=
  match d with
  | isTrue _ => minor
  | isFalse _ => fallback

theorem ofDecision_reads {k : Nat} {G : Prop} (d : Decidable G)
    (minor fallback : Code.{u} k) : Read G minor fallback (ofDecision d minor fallback) := by
  cases d with
  | isTrue hG => exact .yes hG
  | isFalse hG => exact .no hG

theorem ofDecision_eq_of_guard {k : Nat} {G : Prop} (d : Decidable G)
    (minor fallback : Code.{u} k) (hG : G) : ofDecision d minor fallback = minor :=
  output_eq_of_guard hG (ofDecision_reads d minor fallback)

theorem ofDecision_eq_of_not_guard {k : Nat} {G : Prop} (d : Decidable G)
    (minor fallback : Code.{u} k) (hG : ¬ G) : ofDecision d minor fallback = fallback :=
  output_eq_of_not_guard hG (ofDecision_reads d minor fallback)

theorem ofDecision_independent {k : Nat} {G : Prop} (d e : Decidable G)
    (minor fallback : Code.{u} k) :
    ofDecision d minor fallback = ofDecision e minor fallback :=
  functional (ofDecision_reads d minor fallback) (ofDecision_reads e minor fallback)

def kernelIso_of_guard {k : Nat} {G : Prop}
    {minor fallback C : Code.{u} k} (hG : G)
    (hC : Read G minor fallback C) : KernelIso C.kernel minor.kernel := by
  have h : C = minor := output_eq_of_guard hG hC
  subst C
  exact KernelIso.refl minor.kernel

theorem codeRelated_of_guard {k : Nat} {G : Prop}
    {minor fallback C : Code.{u} k} (hG : G)
    (hC : Read G minor fallback C) : CodeRelated C minor := by
  have h : C = minor := output_eq_of_guard hG hC
  subst C
  exact codeRelated_refl minor

theorem pairTransport_of_guard {k : Nat} {G : Prop}
    {minor fallback C : Code.{u} k} (hG : G)
    (hC : Read G minor fallback C) : PairTransport C minor :=
  pairTransport_of_kernelIso (kernelIso_of_guard hG hC)

theorem pairTransport_of_guard_reverse {k : Nat} {G : Prop}
    {minor fallback C : Code.{u} k} (hG : G)
    (hC : Read G minor fallback C) : PairTransport minor C := by
  have h : C = minor := output_eq_of_guard hG hC
  subst C
  exact pairTransport_of_kernelIso (KernelIso.refl minor.kernel)

theorem readings_codeRelated {k : Nat} {G : Prop}
    {minor fallback C D : Code.{u} k}
    (hC : Read G minor fallback C) (hD : Read G minor fallback D) : CodeRelated C D := by
  have h : C = D := functional hC hD
  subst C
  exact codeRelated_refl D

/-- Component invariance is sufficient for the branch reader to preserve the
unchanged strong code relation. It does not assume an extra K relation edge. -/
theorem related_of_components {k : Nat} {G H : Prop}
    {minor₁ fallback₁ minor₂ fallback₂ C D : Code.{u} k}
    (hG : G ↔ H) (hm : CodeRelated minor₁ minor₂)
    (hf : CodeRelated fallback₁ fallback₂)
    (hC : Read G minor₁ fallback₁ C) (hD : Read H minor₂ fallback₂ D) :
    CodeRelated C D := by
  cases hC with
  | yes h =>
      rw [output_eq_of_guard (hG.mp h) hD]
      exact hm
  | no h =>
      have hn : ¬ H := fun hh => h (hG.mpr hh)
      rw [output_eq_of_not_guard hn hD]
      exact hf

theorem guard_iff_output_tag {k : Nat} {G : Prop}
    {minor fallback C : Code.{u} k} (hTags : minor.tag ≠ fallback.tag)
    (hC : Read G minor fallback C) : G ↔ C.tag = minor.tag := by
  constructor
  · intro hG
    exact congrArg (fun X : Code.{u} k => X.tag) (output_eq_of_guard hG hC)
  · intro hTag
    cases hC with
    | yes hG => exact hG
    | no _ => exact False.elim (hTags hTag.symm)

/-- Inspect actual output data, then use the Prop derivation only inside proofs.
There is no elimination of the two-constructor Read proposition into data. -/
def guardDecisionOfRead {k : Nat} {G : Prop}
    {minor fallback C : Code.{u} k}
    (hTags : minor.tag ≠ fallback.tag) (hC : Read G minor fallback C) : Decidable G :=
  if hTag : C.tag = minor.tag then
    isTrue ((guard_iff_output_tag hTags hC).mpr hTag)
  else
    isFalse (fun hG => hTag ((guard_iff_output_tag hTags hC).mp hG))

theorem failed_neutral_names_related_iff {k : Nat} {G H : Prop}
    {minor₁ minor₂ C D : Code.{u} k} {r s : Nat}
    (hG : ¬ G) (hH : ¬ H)
    (hC : Read G minor₁ (Code.neutral.{u} k r) C)
    (hD : Read H minor₂ (Code.neutral.{u} k s) D) :
    CodeRelated C D ↔ r = s := by
  have hC' : C = Code.neutral.{u} k r := output_eq_of_not_guard hG hC
  have hD' : D = Code.neutral.{u} k s := output_eq_of_not_guard hH hD
  subst C
  subst D
  exact neutral_codeRelated_iff k r s

/-- Term environments are separate from the level valuations of ValuationRel. -/
def EnvRel (ρ σ : EnvI) : Prop := ∀ n, ValueEq (ρ n) (σ n)

theorem envRel_eq {ρ σ : EnvI} (h : EnvRel ρ σ) : ρ = σ := by
  funext n
  exact NeutralCodes.valueEq_eq (h n)

theorem envRel_refl (ρ : EnvI) : EnvRel ρ ρ := by
  intro n c
  exact Iff.rfl

abbrev GuardAt := Valuation → EnvI → Prop
abbrev CodeAt (k : Nat) := Valuation → EnvI → Code.{u} k

def At {k : Nat} (G : GuardAt) (minor fallback : CodeAt.{u} k)
    (ν : Valuation) (ρ : EnvI) (C : Code.{u} k) : Prop :=
  Read (G ν ρ) (minor ν ρ) (fallback ν ρ) C

theorem at_functional {k : Nat} {G : GuardAt} {minor fallback : CodeAt.{u} k}
    {ν : Valuation} {ρ : EnvI} {C D : Code.{u} k}
    (hC : At G minor fallback ν ρ C) (hD : At G minor fallback ν ρ D) : C = D :=
  functional hC hD

theorem at_exists_iff {k : Nat} (G : GuardAt) (minor fallback : CodeAt.{u} k)
    (ν : Valuation) (ρ : EnvI) :
    (∃ C, At G minor fallback ν ρ C) ↔ G ν ρ ∨ ¬ G ν ρ :=
  exists_iff (G ν ρ) (minor ν ρ) (fallback ν ρ)

theorem at_stable {k : Nat} (G : GuardAt) (minor fallback : CodeAt.{u} k)
    {ν μ : Valuation} {ρ σ : EnvI}
    (hν : PairedStatements.ValuationRel ν μ) (hρ : EnvRel ρ σ)
    (C : Code.{u} k) : At G minor fallback ν ρ C ↔ At G minor fallback μ σ C := by
  have hLevels : ν = μ := funext hν
  have hEnvs : ρ = σ := envRel_eq hρ
  cases hLevels
  cases hEnvs
  exact Iff.rfl

theorem related_inputs_agree {k : Nat} {G : GuardAt} {minor fallback : CodeAt.{u} k}
    {ν μ : Valuation} {ρ σ : EnvI} {C D : Code.{u} k}
    (hν : PairedStatements.ValuationRel ν μ) (hρ : EnvRel ρ σ)
    (hC : At G minor fallback ν ρ C) (hD : At G minor fallback μ σ D) : C = D :=
  at_functional ((at_stable G minor fallback hν hρ C).mp hC) hD

def atDecision {k : Nat} (G : GuardAt) (minor fallback : CodeAt.{u} k)
    (ν : Valuation) (ρ : EnvI) (d : Decidable (G ν ρ)) : Code.{u} k :=
  ofDecision d (minor ν ρ) (fallback ν ρ)

theorem atDecision_reads {k : Nat} (G : GuardAt) (minor fallback : CodeAt.{u} k)
    (ν : Valuation) (ρ : EnvI) (d : Decidable (G ν ρ)) :
    At G minor fallback ν ρ (atDecision G minor fallback ν ρ d) :=
  ofDecision_reads d (minor ν ρ) (fallback ν ρ)

theorem atDecision_stable {k : Nat} (G : GuardAt) (minor fallback : CodeAt.{u} k)
    {ν μ : Valuation} {ρ σ : EnvI}
    (hν : PairedStatements.ValuationRel ν μ) (hρ : EnvRel ρ σ)
    (d : Decidable (G ν ρ)) (e : Decidable (G μ σ)) :
    atDecision G minor fallback ν ρ d = atDecision G minor fallback μ σ e :=
  related_inputs_agree hν hρ
    (atDecision_reads G minor fallback ν ρ d)
    (atDecision_reads G minor fallback μ σ e)

end GuardedCodeRead
end Rcic.Declarative.Ann.LR3
