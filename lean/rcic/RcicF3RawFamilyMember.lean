import rcic.RcicF3RawFamilyLevels
/-! A chosen admissible raw frame pays the family member's full stored type
at every legal instance, in its actual updated table. Small closed-frame
production remains open. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative PiIndex
theorem family_member_sound (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (K : Nat → Nat) (m : CheckedMember) (hTy : m.mtype = famType fd)
    (hcl : ∀ k, Rcic.Declarative.lift k 1 m.mtype = m.mtype)
    (hb : exprLevelsBounded m.arity m.mtype = true) (hbody : m.body = none) :
    MemberSound P (table P μ fd C) K fd.fref m := by
  intro σ ls ρ hlen _
  let M := mkM P (table P μ fd C)
  let vs := ls.map (evalTotal σ)
  refine ⟨?_, fun b hb' => by rw [hbody] at hb'; cases hb'⟩
  rw [den_inst_canon M σ ls ρ m.mtype hcl (hlen ▸ hb), hTy]
  have hm := ofFrame_mem P (table P μ fd C) fd C hC vs
  have he : Equiv (M.μ fd.fref vs) (ofFrame P (table P μ fd C) fd C vs) := by
    change Equiv (table P μ fd C fd.fref vs) _
    rw [show table P μ fd C fd.fref vs = ofFrame P μ fd C vs from upd_eq _ _ _ _]
    exact (ofFrame_updated P μ fd C hf vs).symm
  exact mem_congr_left he.symm hm
end Rcic.F3.PSet.RawFamily
