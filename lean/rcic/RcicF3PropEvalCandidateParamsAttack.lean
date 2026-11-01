import rcic.RcicF3PropEvalCandidateParams
import rcic.RcicF3PropEvalCandidateAttack

/-!
# Constructor-slice composition and complete-key refusal at AccR

The actual admitted constructor inhabits the guarded candidate's constructor
relation at the empty proposition parameter. Parameter slicing is applied
to that produced constructor witness. An extra index suffix passes the
parameter-prefix equality but is refused by actual candidate membership,
because evaluation retains the whole key. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidateParamsAttack
open Rcic.Declarative PiIndex RawFamilyRec RawFamily PlanPropEndAttack
open PropEvalUniqueAttack (ctx)
open PropEvalCandidateAttack (X)

/-- The witness uses actual candidate semantics; the recursive domain is empty. -/
theorem constructor (P : Premises4) :
    CtorAt P (installed P) fd (X P) [] (key [parameter]) pempty := by
  refine ⟨⟨0, by change 0 < 1; decide⟩, [parameter], [pempty], ?_, ?_, ?_, rfl, ?_⟩
  · exact PropEvalAttack.parameters_fit P (table P (installed P) fd (X P))
  · exact PropEvalAttack.original_field_fit P (table P (installed P) fd (X P))
  · trivial
  · exact Equiv.rfl

/-- Passing the prefix guard cannot erase a spurious dependent-index suffix. -/
theorem suffix_rejected (P : Premises4) (z : PSet.{4}) :
    paramKey 1 (key [parameter, datum]) = key [parameter] ∧
      z ∉ X P [] (key [parameter, datum]) := by
  refine ⟨rfl, ?_⟩
  intro hz
  obtain ⟨w, hw⟩ := PropEvalCandidate.exists_of_mem P (installed P) (ctx P)
    [] (key [parameter, datum]) z hz
    (fun u hu => by change u < 0 at hu; omega) rfl
  exact (PropEvalAttack.suffix_rejected P w).2 hw

def Witness (P : Premises4) : Prop :=
  CtorAt P (installed P) fd (X P) [] (key [parameter]) pempty ∧
  (let M := mkM P (table P (installed P) fd (X P))
   ∃ (j : Fin fd.ctors.length) (xs : List PSet.{4}),
    TelFits M (σOf []) fd.params ρ0 [parameter] ∧
    TelFits M (σOf []) (fd.ctors.get j).1 (push [parameter] ρ0) xs ∧
    key [parameter] = key ([parameter] ++ (fd.ctors.get j).2.map
      (den M (σOf []) (push xs (push [parameter] ρ0)))) ∧
    Equiv (pempty : PSet.{4}) pempty) ∧
  (paramKey 1 (key [parameter, datum]) = key [parameter] ∧
    ∀ z : PSet.{4}, z ∉ X P [] (key [parameter, datum]))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨constructor P,
    PropEvalCandidate.ctorAt_parameters P (installed P) fd (X P) []
      (key [parameter]) pempty (constructor P) [parameter] rfl rfl,
    rfl, fun z => (suffix_rejected P z).2⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalCandidateParamsAttack
