import rcic.RcicF3PiEraseCompile
import rcic.RcicF3PiEraseAttack
/-!
# Compiler regression at the nested empty-domain counterexample

The compiled telescope accepts the actual erased proof, while the literal
nested graph product refuses it. This is an elementary application of
compile_spec and the existing checked counterexample, not a new universal
raw-syntax bridge. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiEraseCompileAttack
universe u

def domains (m : Nat) (_ : Nat → PSet.{u}) : PSet.{u} :=
  tyv (if m = 1 then PiErasureAttack.domain else pempty)

def telescope (M : Interp.{u}) : RecTel.{u, 0} PUnit.{1} 2 :=
  PiEraseCompile.compile M domains (fun _ => PUnit.unit) 2 (fun _ => pempty)

theorem nested_empty (M : Interp.{u}) :
    pempty ∈ Ed M ((telescope M).erasedType M (fun _ => PiErasureAttack.domain)) ∧
      ¬ pempty ∈ PiErasureAttack.literal.{u} := by
  have hD : ∀ m (ρ ρ' : Nat → PSet.{u}), (∀ j, Equiv (ρ j) (ρ' j)) →
      Equiv (domains m ρ) (domains m ρ') := fun _ _ _ _ => Equiv.rfl
  have hX : Dich PiErasureAttack.domain.{u} :=
    Or.inr (fun h => tyv_ne_pempty pempty (mem_singleton.mp h).symm)
  have hs := PiEraseCompile.compile_spec M domains (fun _ => PUnit.unit) hD
    (fun _ _ _ => rfl) (fun _ => PiErasureAttack.domain) (fun _ => hX)
    2 (fun _ => pempty)
  have he : Equiv ((telescope M).erasedType M (fun _ => PiErasureAttack.domain))
      (piVal M (tyv PiErasureAttack.domain) (fun _ =>
        piVal M (tyv pempty) (fun _ => tyv PiErasureAttack.domain))) := hs
  exact ⟨mem_congr_right (ed_congr M he).symm (PiErasureAttack.nested_empty_domain.{u, u} M).1,
    (PiErasureAttack.nested_empty_domain.{u, u} M).2⟩
end Rcic.F3.PSet.PiEraseCompileAttack
