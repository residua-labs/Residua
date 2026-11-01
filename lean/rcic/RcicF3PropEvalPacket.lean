import rcic.RcicF3PropEvalInputs
import rcic.RcicF3PropEvalCandidate
import rcic.RcicF3PiIndexedIHBuilder
import rcic.RcicF3PropEvalGuarded
import rcic.RcicF3PropEvalIH

/-!
# Candidate child evaluations produce the executable recursive input packet

The extractor is used only at keys reached by the actual normalized field.
Every compiled telescope path is represented by a fitting argument tuple.
Candidate membership supplies existence at those tuples; the already proved
guarded typing and functionality interfaces supply the extractor's remaining
facts. The actual indexed builder then produces typed IH membership, while
its computation theorem produces the literal recursive child evaluations.
This does not assume evaluation totality on all raw fibres. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

noncomputable def childCarrier (C : Context) (v : Level) (i : Index.{4}) : PSet.{4} :=
  PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
    (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
    C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i pempty

/-- A leaf-scoped evaluation producer supplies the actual executable IH packet.
The next theorem supplies that producer from the guarded candidate itself. -/
theorem recursive_packet_of_leaf_evaluations (C : Context)
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
    (hprefix : ∀ zs, TelFits C.M C.σ ds (vcons x ρ) zs →
      (args.take C.node.a.family.parameters.length).map
        (den C.M C.σ (push zs (vcons x ρ))) = C.parameters)
    (hMx : den C.M C.σ (vcons x ρ) (Rcic.Declarative.lift 0 1 Mx) = C.motive)
    (hProp : ∀ ys, ys.length = args.length → ∀ z,
      z ∈ Ed C.M (fapps
        (C.M.μ C.node.a.family.ref
          ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))) ys) → Equiv z pempty)
    (hx : x ∈ Ed C.M (den C.M C.σ (vcons x ρ)
      (policyPi ds (foldApps (.const C.node.a.family.ref
        (canonL C.node.a.family.member.arity)) args))))
    (hguarded : ∀ i z, Eval C i z → z ∈ childCarrier C v i)
    (hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z')
    (hex : ∀ zs, TelFits C.M C.σ ds (vcons x ρ) zs →
      ∃ z, Eval C (key (args.map (den C.M C.σ (push zs (vcons x ρ))))) z) :
    RecursivePacket C fuel inner A Mx ρ x := by
  let F := C.M.μ C.node.a.family.ref
    ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))
  let t := tel C.M C.σ ds args (vcons x ρ)
  let T := childCarrier C v
  let g : Index.{4} → PSet.{4} → PSet.{4} :=
    fun i _ => PropEvalExtract.value (T i) (Eval C i)
  have hexT : ∀ zs, TelFits C.M C.σ ds (vcons x ρ) zs →
      let i := key (args.map (den C.M C.σ (push zs (vcons x ρ))))
      ∃ z, z ∈ T i ∧ Eval C i z := by
    intro zs hzs
    obtain ⟨z, hz⟩ := hex zs hzs
    exact ⟨z, hguarded _ _ hz, hz⟩
  have hfunT : ∀ zs, TelFits C.M C.σ ds (vcons x ρ) zs →
      let i := key (args.map (den C.M C.σ (push zs (vcons x ρ))))
      ∀ z z', z ∈ T i → z' ∈ T i → Eval C i z → Eval C i z' → Equiv z z' :=
    fun _ _ _ _ _ _ hz hz' => hfunctional _ _ _ hz hz'
  have hspec : ∀ zs, TelFits C.M C.σ ds (vcons x ρ) zs →
      let i := key (args.map (den C.M C.σ (push zs (vcons x ρ))))
      g i pempty ∈ T i ∧ Eval C i (g i pempty) :=
    fun zs hzs => PropEvalExtract.value_spec_of_output_congr
      (hexT zs hzs) (hfunT zs hzs) (fun _ hz _ => hz)
      (fun _ _ he h => h.output_congr he.symm)
  have hmap : ∀ p y, y ∈ proofFibre C.M F (t.result p) →
      g (t.result p) y ∈
        PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v) F
          C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0)
          (t.result p) y := by
    intro p y hy
    obtain ⟨zs, hzs, hr⟩ := PiSyntaxCompile.result_fits C.M C.σ
      (read C.M C.σ args) ds (vcons x ρ) p
    have hr' : t.result p = key (args.map (den C.M C.σ (push zs (vcons x ρ)))) := hr
    rw [hr'] at hy ⊢
    exact guarded_mem_at_proof C.M C.σ (evalTotal C.σ v) F C.motive
      C.parameters C.node.a.family.indices (push C.parameters ρ0) _ y _ hy
      (hspec zs hzs).1
  obtain ⟨ihT, hread, hih⟩ := PiRawIHAny.indexed_builder_mem C.M hU C.σ
    C.node.a.family.ref (canonL C.node.a.family.member.arity) endVal hEnd
    C.node.a.family.resultLevel v C.node.a.family.parameters C.node.a.family.indices
    C.parameters hps hF C.motive hmo C.node.E0 fuel A ds args
    (by simpa only [List.length_append] using hargc) (vcons x ρ) hprefix Mx hMx
    hscan hProp hx g hmap
  rw [hdepth] at hread
  refine ⟨ihT, t.indexedIH C.M g x, ds, args, hread, hih,
    hscan, hdepth, hargc, ?_⟩
  exact indexed_children_of_bounded C ds args (vcons x ρ) T x hexT hfunT

/-- The actual normalized candidate field pays the only evaluation-existence
input of the packet producer. Complete keys and the extra motive slot are retained. -/
theorem recursive_packet_of_candidate (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (hM : C.M = mkM P μ)
    (hRaw : RawFamily.Admissible (famDataOf C.node.a)
      (RawFamily.frame P μ (famDataOf C.node.a)))
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
      Ed (mkM P (RawFamily.table P μ (famDataOf C.node.a) (PropEvalCandidate.candidate P μ C)))
        (den (mkM P (RawFamily.table P μ (famDataOf C.node.a)
          (PropEvalCandidate.candidate P μ C))) C.σ (vcons x ρ)
          (policyPi ds (foldApps (.const C.node.a.family.ref
            (canonL C.node.a.family.member.arity)) args))))
    (hguarded : ∀ i z, Eval C i z → z ∈ childCarrier C v i)
    (hfunctional : ∀ i z z', Eval C i z → Eval C i z' → Equiv z z') :
    RecursivePacket C fuel inner A Mx ρ x := by
  apply recursive_packet_of_leaf_evaluations C fuel inner A Mx ρ x v hU endVal hEnd
    hps hF hmo ds args hdepth hargc hscan hprefix hMx hProp hxRaw hguarded hfunctional
  exact PropEvalCandidate.leaf_eval P μ C hM hRaw hf ds args hd ha
    (by simpa only [List.length_append, famDataOf] using hargc)
    (vcons x ρ) x
    (fun zs hzs => by rw [hprefix zs hzs]; exact LEq.refl C.parameters)
    hxCandidate

end Rcic.F3.PSet.PropEval
