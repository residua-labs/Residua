import rcic.RcicF3PropEvalCandidate
import rcic.RcicF3RawFamilyLevels

/-!
# Raw-role family inputs for the candidate's typed IH packet

The faithful raw family equation, its bounded family syntax and admissible
frame produce the packet's family abstraction and complete-application
proof face. The abstraction is transported to the actual recursor valuation;
only the family slots must agree. Non-fitting complete applications cannot
have members, and fitting ones read the actual raw frame. No constructor
closure or evaluation totality is added as an input. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalCandidate
open Rcic.Declarative PiIndex RawFamily

/-- Standard raw-role inputs of the actual indexed packet are produced together. -/
theorem raw_family_inputs (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : PropEval.Context) (hM : C.M = mkM P μ)
    (hB : FamBounded (famDataOf C.node.a) C.node.a.family.member.arity)
    (hFamily : ∀ vs, Equiv (μ (famDataOf C.node.a).fref vs)
      (role P μ (famDataOf C.node.a) vs))
    (hRaw : Admissible (famDataOf C.node.a) (frame P μ (famDataOf C.node.a)))
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0) :
    ∃ endVal : (Nat → PSet.{4}) → PSet.{4},
      EnvResp endVal ∧
      Equiv (C.M.μ C.node.a.family.ref
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
        (piLam C.M C.σ endVal ρ0
          (policyPi (C.node.a.family.parameters ++ C.node.a.family.indices)
            (.sort C.node.a.family.resultLevel))) ∧
      ∀ ys, ys.length = C.node.a.family.parameters.length + C.node.a.family.indices.length →
        ∀ z, z ∈ Ed C.M (fapps
          (C.M.μ C.node.a.family.ref
            ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))) ys) →
          Equiv z pempty := by
  let M := mkM P μ
  let fd := famDataOf C.node.a
  let R := frame P μ fd
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  let g := endValue R vs (fd.params.length + fd.indices.length)
  have hg : EnvResp g := endValue_resp R vs _
  have hσ : ∀ u, u < C.node.a.family.member.arity → C.σ u = σOf vs u :=
    canonical_agreement C
  have h0vs : evalTotal (σOf vs) fd.resLevel = 0 :=
    (evalTotal_agree hσ fd.resLevel hB.res).symm.trans h0
  have hlevels : Equiv (piLam M C.σ g ρ0 (famType fd)) (ofFrame P μ fd R vs) := by
    exact piLam_levels M hσ hg (fun _ => Equiv.rfl) (.sort fd.resLevel)
      (fun _ => Equiv.rfl) (fd.params ++ fd.indices)
      (fun e he => by
        rcases List.mem_append.mp he with hp | hi
        · exact hB.params e hp
        · exact hB.indices e hi) ρ0
  refine ⟨g, hg, ?_, ?_⟩
  · rw [hM]
    exact (hFamily vs).trans hlevels.symm
  · intro ys hlen z hz
    rw [hM] at hz
    have hzRole : z ∈ Ed M (fapps (ofFrame P μ fd R vs) ys) :=
      mem_congr_right (ed_congr M (fapps_congr (hFamily vs) ys)) hz
    have hn : ¬ Equiv (fapps (ofFrame P μ fd R vs) ys) pempty := by
      intro he
      exact not_mem_pempty
        (mem_congr_right ((ed_congr M he).trans (ed_pempty M)) hzRole)
    have hfit : TelFits M (σOf vs) (fd.params ++ fd.indices) ρ0 ys :=
      fits_of_fapps_ne M (σOf vs) hg (.sort fd.resLevel) (fd.params ++ fd.indices)
        ρ0 ys (by simpa only [List.length_append, famDataOf] using hlen) hn
    have hzR := mem_congr_right (apply_ofFrame_ed P μ fd R hRaw vs ys hfit) hzRole
    have hface := (hRaw vs (key ys)).2
    rw [if_pos h0vs] at hface
    exact hface z hzR

end Rcic.F3.PSet.PropEvalCandidate
