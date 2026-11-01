import rcic.RcicF3PropEvalFramePacket
import rcic.RcicF3PiCleanViews
import rcic.RcicF3CandidateScope
import rcic.RcicF3PropEvalMotiveGuard

/-!
# Admitted evaluation inputs over a produced admissible base frame

The actual original fields fit both the faithful raw interpretation and the
restriction of N by the same guarded evaluation predicate. The existing
normalized views, input-spine induction and stored-minor derivation are
reused with that restriction. Recursive child existence comes from actual
candidate membership; no evaluation or IH callback is supplied here.

The base's admissibility is an explicit intermediate premise. A subsequent
public producer must instantiate it with the produced normalized frame and
pay constructor closure. No universal StepAG is asserted. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

/-- Admission, actual prefix soundness, and original field membership pay the
normalized packet inputs at every position of the interleaved spine. -/
theorem recursive_packet_of_clean_view_on_frame (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (hM : C.M = mkM P μ)
    (N : RawFamily.Frame)
    (hN : RawFamily.Admissible (famDataOf C.node.a) N)
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (K : Nat → Nat) {nRaw nCandidate : Nat}
    (hERaw : EnvSound C.M C.σ K (extendEnv C.E C.f fm) nRaw)
    (hECandidate : EnvSound
      (mkM P (RawFamily.table P μ (famDataOf C.node.a)
        (PropEvalFrame.candidate N C)))
      C.σ K (extendEnv C.E C.f fm) nCandidate)
    (hb : BodiesOK (extendEnv C.E C.f fm) C.σ K)
    (hcl : EnvClosed C.node.E0)
    (v : Level) (hU : C.M.U = U W4)
    (endVal : (Nat → PSet.{4}) → PSet.{4}) (hEnd : EnvResp endVal)
    (hps : C.parameters.length = C.node.a.family.parameters.length)
    (hF : Equiv
      (C.M.μ C.node.a.family.ref
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (piLam C.M C.σ endVal ρ0
        (policyPi (C.node.a.family.parameters ++ C.node.a.family.indices)
          (.sort C.node.a.family.resultLevel))))
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hProp : ∀ ys,
      ys.length = C.node.a.family.parameters.length + C.node.a.family.indices.length →
      ∀ z, z ∈ Ed C.M (fapps
        (C.M.μ C.node.a.family.ref
          ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))) ys) →
        Equiv z pempty)
    (hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z')
    (fuel inner prior : Nat) (A : Expr Nat)
    (hview : PiRawFieldViews.View C.node.E0 fuel C.node.a.family.ref
      C.node.a.family.member.arity C.node.a.family.parameters.length
      C.node.a.family.indices.length prior A (.recursive inner))
    (hclean : PiCleanViews.Clean C.node.E0 fuel C.node.a.family.ref
      C.node.a.family.member.arity C.node.a.family.parameters.length
      C.node.a.family.indices.length A (.recursive inner))
    (pre : List PSet.{4}) (hpre : pre.length = prior)
    (Mx : Expr Nat) (x : PSet.{4})
    (hI : InstOK (extendEnv C.E C.f fm) C.σ K A)
    (hMx : den C.M C.σ (push pre (push C.parameters ρ0)) Mx = C.motive)
    (hxRaw : x ∈ Ed C.M (den C.M C.σ (push pre (push C.parameters ρ0)) A))
    (hxCandidate : x ∈
      Ed (mkM P (RawFamily.table P μ (famDataOf C.node.a) (PropEvalFrame.candidate N C)))
        (den (mkM P (RawFamily.table P μ (famDataOf C.node.a)
          (PropEvalFrame.candidate N C))) C.σ (push pre (push C.parameters ρ0)) A)) :
    RecursivePacket C fuel inner A Mx (push pre (push C.parameters ρ0)) x := by
  let Mc := mkM P (RawFamily.table P μ (famDataOf C.node.a)
    (PropEvalFrame.candidate N C))
  let ρ := push pre (push C.parameters ρ0)
  have hv : PiRawFieldViews.View C.node.E0 fuel C.node.a.family.ref
      C.node.a.family.member.arity C.node.a.family.parameters.length
      C.node.a.family.indices.length pre.length A (.recursive inner) := by
    simpa only [hpre] using hview
  obtain ⟨ds, args, hdepth, hargc, hscan, hprefix⟩ :=
    PiRawFieldViews.View.ih_read C.M C.σ C.parameters pre ρ0 x hcl hps hv
  obtain ⟨hd, ha⟩ := (hclean.lift hcl 0 1).recursive_frees hscan
  have hscanPrefix := CandidateScope.recNode_read hmem C.node hscan
  have hIlift : InstOK (extendEnv C.E C.f fm) C.σ K
      (Rcic.Declarative.lift 0 1 A) := by
    simpa only [InstOK, constInsts_lift] using hI
  have hRawLift : den C.M C.σ (vcons x ρ) (Rcic.Declarative.lift 0 1 A) =
      den C.M C.σ ρ A := den_lift0_push C.M C.σ [x] ρ A
  have hCandidateLift : den Mc C.σ (vcons x ρ) (Rcic.Declarative.lift 0 1 A) =
      den Mc C.σ ρ A := den_lift0_push Mc C.σ [x] ρ A
  have hxRawLift : x ∈ Ed C.M
      (den C.M C.σ (vcons x ρ) (Rcic.Declarative.lift 0 1 A)) := by
    rw [hRawLift]
    exact hxRaw
  have hxCandidateLift : x ∈ Ed Mc
      (den Mc C.σ (vcons x ρ) (Rcic.Declarative.lift 0 1 A)) := by
    rw [hCandidateLift]
    exact hxCandidate
  have hnormRaw := den_piTelescope_of_mem C.M C.σ K hERaw hb fuel
    (Rcic.Declarative.lift 0 1 A) ds _ (vcons x ρ) x
    hscanPrefix hIlift hxRawLift
  have hnormCandidate := den_piTelescope_of_mem Mc C.σ K hECandidate hb fuel
    (Rcic.Declarative.lift 0 1 A) ds _ (vcons x ρ) x
    hscanPrefix hIlift hxCandidateLift
  have hguarded : ∀ i z, Eval C i z → z ∈ childCarrier C v i := by
    intro i z he
    exact he.mem_guarded_of_typed_motive v hU hmo hProp
  apply recursive_packet_on_frame P μ C hM N hN hf fuel inner A Mx ρ x
    v hU endVal hEnd hps hF hmo ds args hdepth hargc hscan hd ha
    (fun zs hzs => hprefix zs hzs.length)
    ((den_lift0_push C.M C.σ [x] ρ Mx).trans hMx)
    (fun ys hys z hz => hProp ys (hys.trans hargc) z hz)
    (mem_congr_right (ed_congr C.M hnormRaw.symm) hxRawLift)
    (mem_congr_right (ed_congr Mc hnormCandidate.symm) hxCandidateLift)
    hguarded hfunctional

/-- The finite input spine with every recursive-head callback supplied by
the actual normalized candidate field. The remaining inputs are ordinary
typing, admission, original field fitting, and the proved functionality
interface. Guarded typing is produced from the actual typed motive. There
is no premise asserting child evaluation existence. -/
theorem inputs_of_clean_views_on_frame (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (hM : C.M = mkM P μ)
    (N : RawFamily.Frame)
    (hN : RawFamily.Admissible (famDataOf C.node.a) N)
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (K : Nat → Nat) {nRaw nCandidate : Nat}
    (hERaw : EnvSound C.M C.σ K (extendEnv C.E C.f fm) nRaw)
    (hECandidate : EnvSound
      (mkM P (RawFamily.table P μ (famDataOf C.node.a)
        (PropEvalFrame.candidate N C)))
      C.σ K (extendEnv C.E C.f fm) nCandidate)
    (hb : BodiesOK (extendEnv C.E C.f fm) C.σ K)
    (hcl : EnvClosed C.node.E0)
    (v : Level) (hU : C.M.U = U W4)
    (endVal : (Nat → PSet.{4}) → PSet.{4}) (hEnd : EnvResp endVal)
    (hps : C.parameters.length = C.node.a.family.parameters.length)
    (hF : Equiv
      (C.M.μ C.node.a.family.ref
        ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (piLam C.M C.σ endVal ρ0
        (policyPi (C.node.a.family.parameters ++ C.node.a.family.indices)
          (.sort C.node.a.family.resultLevel))))
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hProp : ∀ ys,
      ys.length = C.node.a.family.parameters.length + C.node.a.family.indices.length →
      ∀ z, z ∈ Ed C.M (fapps
        (C.M.μ C.node.a.family.ref
          ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))) ys) →
        Equiv z pempty)
    (hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z')
    (fuel : Nat) :
    ∀ (ss : List FieldShape) (Fs : List (Expr Nat)) (prior : Nat),
      PiRawFieldViews.Views C.node.E0 fuel C.node.a.family.ref
        C.node.a.family.member.arity C.node.a.family.parameters.length
        C.node.a.family.indices.length prior ss Fs →
      FieldCertificates (fun _ A s => PiCleanViews.Clean C.node.E0 fuel
        C.node.a.family.ref C.node.a.family.member.arity
        C.node.a.family.parameters.length C.node.a.family.indices.length A s) prior ss Fs →
      ∀ (pre : List PSet.{4}), pre.length = prior →
      ∀ (Tend Mx acc : Expr Nat) (xs : List PSet.{4}),
      (∀ A ∈ Fs, InstOK (extendEnv C.E C.f fm) C.σ K A) →
      den C.M C.σ (push pre (push C.parameters ρ0)) Mx = C.motive →
      TelFits C.M C.σ Fs (push pre (push C.parameters ρ0)) xs →
      TelFits (mkM P (RawFamily.table P μ (famDataOf C.node.a)
        (PropEvalFrame.candidate N C))) C.σ Fs
        (push pre (push C.parameters ρ0)) xs →
      ∃ ys out, Inputs C fuel Mx acc ss (policyPi Fs Tend)
        (push pre (push C.parameters ρ0)) xs ys out := by
  apply inputs_of_certified_views C
    (mkM P (RawFamily.table P μ (famDataOf C.node.a)
      (PropEvalFrame.candidate N C)))
    (extendEnv C.E C.f fm) K fuel hcl C.parameters
    (fun _ A s => PiCleanViews.Clean C.node.E0 fuel C.node.a.family.ref
      C.node.a.family.member.arity C.node.a.family.parameters.length
      C.node.a.family.indices.length A s)
  · intro prior A s c a _ h
    exact h.lift hcl c a
  · intro prior A inner hview hclean pre hpre Mx x hI hMx hxRaw hxCandidate
    exact recursive_packet_of_clean_view_on_frame P μ C hM N hN hf fm ctors hmem K
      hERaw hECandidate hb hcl v hU endVal hEnd hps hF hmo hProp hfunctional
      fuel inner prior A hview hclean pre hpre Mx x hI hMx hxRaw hxCandidate

end Rcic.F3.PSet.PropEval
