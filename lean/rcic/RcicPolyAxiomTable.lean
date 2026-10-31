import rcic.RcicF3EnvG
import rcic.RcicPolyAxiomAdmission

/-!
# Declared axiom arity survives the shared environment table fold

The value rule deliberately distinguishes arity one from arity zero. The actual
parameterized admission fixture must select the former. This is a regression
for table construction and faithfulness, not a soundness theorem.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PolyAxiomTable

open Rcic.Declarative

noncomputable def aritySensitiveValue : MemberValue := fun _ _ _ m _ =>
  if m.arity = 1 then singleton pempty else pempty

def plainCtx : Nat → Role := fun _ => .plain

theorem installed_at_declared_arity :
    envμBy aritySensitiveValue plainCtx PolyAxiomAdmission.admitted 7 [] =
      singleton pempty := rfl

theorem marker_nonempty : ¬ Equiv (singleton pempty) pempty := fun h =>
  not_mem_pempty (mem_congr_right h (mem_singleton.mpr Equiv.rfl))

theorem wrong_zero_arity_refused :
    ¬ Equiv (envμBy aritySensitiveValue plainCtx PolyAxiomAdmission.admitted 7 [])
      (aritySensitiveValue 7 (fun _ _ => pempty) .plain
        ⟨.axiomM, 0, .sort (.param 0), none⟩ []) := by
  change ¬ Equiv (singleton pempty) pempty
  exact marker_nonempty

theorem value_agrees : ValueAgrees aritySensitiveValue :=
  fun _ _ _ _ _ _ => Equiv.rfl

theorem reads_along : ReadsOKAlong plainCtx PolyAxiomAdmission.admitted := by
  refine ⟨True.intro, ?_, ?_⟩
  · intro r hr
    cases hr
  · intro b hb
    cases hb

theorem selected_faithful :
    FaithfulBy aritySensitiveValue
      (envμBy aritySensitiveValue plainCtx PolyAxiomAdmission.admitted)
      plainCtx PolyAxiomAdmission.env :=
  (faithfulBy_envμBy aritySensitiveValue value_agrees plainCtx
    PolyAxiomAdmission.admitted reads_along).1

end Rcic.F3.PSet.PolyAxiomTable
