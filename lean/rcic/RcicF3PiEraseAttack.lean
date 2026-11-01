import rcic.RcicF3Core
/-!
# Self-attack: literal products do not model proof erasure

Both the outer domain and the final fibre are the nonempty singleton of
`tyv pempty`. The inner domain is empty. R-CIC's `piVal` makes that inner
function proof-like, so the outer product admits `pempty`; the literal
nested graph product does not. Thus a bridge from `RecTel.denote` to
R-CIC denotation cannot silently identify these interpretations, even
with a nonproof recursive result fibre. No theory restriction is inferred.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.F3.PSet.PiErasureAttack
universe u

def atom : PSet.{u} := tyv pempty

def domain : PSet.{u} := singleton atom

def raw (M : Interp.{u}) : PSet.{u} :=
  Ed M (piVal M (tyv domain) (fun _ =>
    piVal M (tyv pempty) (fun _ => tyv domain)))

def literal : PSet.{u} := piSet domain (fun _ => piSet pempty (fun _ => domain))

theorem nested_empty_domain (M : Interp.{u}) : pempty ∈ raw M ∧ ¬pempty ∈ literal := by
  have e0 : Equiv (Ed M (tyv pempty)) pempty :=
    ed_tyv M (Or.inr not_mem_pempty)
  have hP : PiProp M (tyv pempty) (fun _ => tyv domain) := by
    intro x hx
    exact (not_mem_pempty (mem_congr_right e0 hx)).elim
  have ei := ed_piVal M (tyv pempty) (fun _ => tyv domain)
    (fun _ _ _ => Equiv.rfl)
  rw [cond_pos hP] at ei
  have hm : pempty ∈ Ed M (piVal M (tyv pempty) (fun _ => tyv domain)) :=
    mem_congr_right ei.symm (mem_tv.mpr ⟨fun x hx =>
      (not_mem_pempty (mem_congr_right e0 hx)).elim, Equiv.rfl⟩)
  have ho : PiProp M (tyv domain) (fun _ =>
      piVal M (tyv pempty) (fun _ => tyv domain)) := by
    intro _ _ y hy
    exact (mem_tv.mp (mem_congr_right ei hy)).2
  have eo := ed_piVal M (tyv domain) (fun _ =>
    piVal M (tyv pempty) (fun _ => tyv domain)) (fun _ _ _ => Equiv.rfl)
  rw [cond_pos ho] at eo
  constructor
  · exact mem_congr_right eo.symm
      (mem_tv.mpr ⟨fun _ _ => hm, Equiv.rfl⟩)
  · intro h
    obtain ⟨b, _, hb⟩ := (isFuncOnDep_of_mem_piSet
      (A := domain) (B := fun _ => piSet pempty (fun _ => domain))
      (fun _ _ _ => Equiv.rfl) h).1 atom (mem_singleton.mpr Equiv.rfl)
    exact not_mem_pempty hb
end Rcic.F3.PSet.PiErasureAttack
