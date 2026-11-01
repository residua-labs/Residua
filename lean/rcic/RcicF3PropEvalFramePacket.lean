import rcic.RcicF3PropEvalFrame
import rcic.RcicF3PropEvalPacket

/-!
# Actual typed IH packets from a guarded base-frame candidate

The existing bounded extractor and executable indexed IH builder are reused.
The base-frame restriction supplies each reached child's evaluation; typed
motive guarding and functionality retain their literal component inputs.
Neither base closure nor a global raw-frame inclusion is assumed here.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

/-- The actual normalized candidate field pays the only evaluation-existence
input of the packet producer. Complete keys and the extra motive slot are retained. -/
theorem recursive_packet_on_frame (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (hM : C.M = mkM P μ)
    (N : RawFamily.Frame)
    (hN : RawFamily.Admissible (famDataOf C.node.a) N)
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (fuel inner : Nat) (A Mx : Expr Nat) (ρ : Nat → PSet.{4}) (x : PSet.{4})
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
    (ds args : List (Expr Nat)) (hdepth : ds.length = inner)
    (hargc : args.length = C.node.a.family.parameters.length + C.node.a.family.indices.length)
    (hscan : piTelescopeFuel C.node.E0 fuel (Rcic.Declarative.lift 0 1 A) =
      some (ds, foldApps (.const C.node.a.family.ref
        (canonL C.node.a.family.member.arity)) args))
    (hd : ∀ e ∈ ds, occursConst (famDataOf C.node.a).fref e = false)
    (ha : ∀ e ∈ args, occursConst (famDataOf C.node.a).fref e = false)
    (hprefix : ∀ zs, TelFits C.M C.σ ds (vcons x ρ) zs →
      (args.take C.node.a.family.parameters.length).map
        (den C.M C.σ (push zs (vcons x ρ))) = C.parameters)
    (hMx : den C.M C.σ (vcons x ρ) (Rcic.Declarative.lift 0 1 Mx) = C.motive)
    (hProp : ∀ ys, ys.length = args.length → ∀ z,
      z ∈ Ed C.M (fapps
        (C.M.μ C.node.a.family.ref
          ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))) ys) → Equiv z pempty)
    (hxRaw : x ∈ Ed C.M (den C.M C.σ (vcons x ρ)
      (policyPi ds (foldApps (.const C.node.a.family.ref
        (canonL C.node.a.family.member.arity)) args))))
    (hxCandidate : x ∈
      Ed (mkM P (RawFamily.table P μ (famDataOf C.node.a) (PropEvalFrame.candidate N C)))
        (den (mkM P (RawFamily.table P μ (famDataOf C.node.a)
          (PropEvalFrame.candidate N C))) C.σ (vcons x ρ)
          (policyPi ds (foldApps (.const C.node.a.family.ref
            (canonL C.node.a.family.member.arity)) args))))
    (hguarded : ∀ i z, Eval C i z → z ∈ childCarrier C v i)
    (hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z') :
    RecursivePacket C fuel inner A Mx ρ x := by
  apply recursive_packet_of_leaf_evaluations C fuel inner A Mx ρ x v hU endVal hEnd
    hps hF hmo ds args hdepth hargc hscan hprefix hMx hProp hxRaw hguarded hfunctional
  exact PropEvalFrame.leaf_eval P μ C hM N hN hf ds args hd ha
    (by simpa only [List.length_append, famDataOf] using hargc)
    (vcons x ρ) x
    (fun zs hzs => by rw [hprefix zs hzs]; exact LEq.refl C.parameters)
    hxCandidate

end Rcic.F3.PSet.PropEval
