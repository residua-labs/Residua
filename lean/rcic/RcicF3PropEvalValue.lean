import rcic.RcicF3PropEvalPacket

/-!
# The bounded value of the actual indexed Prop evaluation relation

The value is the same saturated separation/union extractor used at every
recursive IH leaf. Its inputs retain the actual RecNode, full valuation,
typed normalized fields, complete parameter/index key and motive universe.
No evaluation callback or existential witness selection defines the value.

Correctness composes explicit evaluation existence, guarded typing and
functionality. The candidate constructor producer and concrete closed frames
pay those inputs at the AccR fixture in the companion module. Universal
frame closure, production-table migration and StepAG remain separate work.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEvalValue
open Rcic.Declarative PiIndex PropEval

noncomputable def result (C : Context) (v : Level) (i : Index.{4}) : PSet.{4} :=
  PropEvalExtract.value (childCarrier C v i) (Eval C i)

/-- Every bounded evaluation has the value defined by the actual relation. -/
theorem result_equiv {C : Context} {v : Level} {i : Index.{4}} {z : PSet.{4}}
    (he : Eval C i z) (hz : z ∈ childCarrier C v i)
    (hfun : ∀ x y, Eval C i x → Eval C i y → Equiv x y) :
    Equiv (result C v i) z :=
  PropEvalExtract.value_equiv hz he (fun x y _ _ hx hy => hfun x y hx hy)

/-- Checked extraction; none of these three inputs is assumed by the definition. -/
theorem result_spec (C : Context) (v : Level) (i : Index.{4})
    (hex : ∃ z, Eval C i z)
    (hguard : ∀ z, Eval C i z → z ∈ childCarrier C v i)
    (hfun : ∀ x y, Eval C i x → Eval C i y → Equiv x y) :
    result C v i ∈ childCarrier C v i ∧ Eval C i (result C v i) := by
  obtain ⟨z, hz⟩ := hex
  exact PropEvalExtract.value_spec_of_output_congr
    ⟨z, hguard z hz, hz⟩
    (fun x y _ _ hx hy => hfun x y hx hy)
    (fun _ hx _ => hx)
    (fun _ _ hxy hx => hx.output_congr hxy.symm)

/-- A fitting dependent index tuple and actual proof major identify the guarded
bound with the requested motive type at its full universe valuation. -/
theorem result_mem_motive (C : Context) (v : Level)
    (is : List PSet.{4}) (z : PSet.{4}) (hU : C.M.U = U W4)
    (hps : C.parameters.length = C.node.a.family.parameters.length)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length +
            C.node.a.family.indices.length))) (.sort v)))))
    (his : TelFits C.M C.σ C.node.a.family.indices (push C.parameters ρ0) is)
    (hz : z ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (C.parameters ++ is)))
    (hproof : Equiv z pempty)
    (hresult : result C v (key (C.parameters ++ is)) ∈
      childCarrier C v (key (C.parameters ++ is))) :
    result C v (key (C.parameters ++ is)) ∈
      Ed C.M (fapps C.motive (is ++ [z])) := by
  let F := C.M.μ C.node.a.family.ref
    ((canonL C.node.a.family.member.arity).map (evalTotal C.σ))
  have hT := PiRawMotiveAny.motive_mem_U C.M hU C.σ
    C.node.a.family.ref (canonL C.node.a.family.member.arity)
    C.node.a.family.parameters C.node.a.family.indices C.parameters is hps
    C.motive z v hmo his hz
  have he := (PiRawMotiveAny.guarded_resp C.M C.σ (evalTotal C.σ v)
    F C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0)
    (key (C.parameters ++ is)) hproof).symm.trans
      (PiRawMotiveAny.guarded_key C.M C.σ (evalTotal C.σ v)
        F C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0)
        is z his hz hT)
  exact mem_congr_right he hresult

/-- Read transport preserves the entire evaluation relation and its bounded
carrier; it needs neither evaluation existence nor functionality. -/
theorem result_congr (C D : Context) (v w : Level) (i j : Index.{4})
    (hbound : Equiv (childCarrier C v i) (childCarrier D w j))
    (heval : ∀ z, Eval C i z ↔ Eval D j z) :
    Equiv (result C v i) (result D w j) := by
  apply PropEvalExtract.value_congr hbound
  intro x
  constructor
  · rintro ⟨z, hz, hxz⟩
    exact ⟨z, (heval z).mp hz, hxz⟩
  · rintro ⟨z, hz, hxz⟩
    exact ⟨z, (heval z).mpr hz, hxz⟩

/-- An unused complete key cannot gain a result through bounded extraction. -/
theorem result_empty (C : Context) (v : Level) (i : Index.{4})
    (hn : ∀ z, ¬ Eval C i z) : Equiv (result C v i) pempty :=
  PropEvalExtract.value_empty hn

end Rcic.F3.PSet.PropEvalValue
