import rcic.RcicF3PropEval
import rcic.RcicF3PiRawMotiveAny

/-!
# Evaluation results in the guarded motive at the actual motive universe

Parameter transport preserves the full constructor key. Index fitting,
actual constructor family membership and its proof erasure remain explicit,
scoped to the context's fixed parameter slice. The typed motive supplies
the bound at its own universe; no family-universe truncation is used.
These are local bridges, not universal constructor or evaluation producers.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

noncomputable def Context.indicesAt (C : Context)
    (j : Fin C.node.a.constructors.length) (ps xs : List PSet.{4}) : List PSet.{4} :=
  (C.node.a.constructorViews j).resultIndices.map
    (den C.M C.σ (push xs (push ps ρ0)))

noncomputable def Context.constructorAt (C : Context)
    (j : Fin C.node.a.constructors.length) (ps xs : List PSet.{4}) : PSet.{4} :=
  fapps (C.M.μ (C.node.a.family.ref + 1 + j.val)
    ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ))) (ps ++ xs)

/-- A typed actual constructor endpoint enters the full-key guarded motive. -/
theorem endpoint_mem_guarded
    (M : Interp.{4}) (hU : M.U = U W4) (σ : Nat → Nat)
    (f : Nat) (ls : List Level) (Ps Is : List (Expr Nat))
    (ps₀ : List PSet.{4}) (hps₀ : ps₀.length = Ps.length)
    (mo : PSet.{4}) (v : Level)
    (hmo : mo ∈ Ed M (den M σ (push ps₀ ρ0)
      (policyPi Is (.pi (foldApps (.const f ls)
        (policyLocals (Ps.length + Is.length))) (.sort v)))))
    (ps is : List PSet.{4}) (c z : PSet.{4}) (hps : LEq ps ps₀)
    (his : TelFits M σ Is (push ps ρ0) is)
    (hc : c ∈ Ed M (fapps (M.μ f (ls.map (evalTotal σ))) (ps ++ is)))
    (hc0 : Equiv c pempty)
    (hz : z ∈ Ed M (fapp (fapps mo is) c)) :
    z ∈ PiRawMotiveAny.guarded M σ (evalTotal σ v)
      (M.μ f (ls.map (evalTotal σ))) mo ps₀ Is (push ps₀ ρ0)
      (key (ps ++ is)) pempty := by
  let F := M.μ f (ls.map (evalTotal σ))
  have hargs : LEq (ps ++ is) (ps₀ ++ is) := LEq_append hps (LEq.refl is)
  have his₀ : TelFits M σ Is (push ps₀ ρ0) is :=
    TelFits_congr M σ Is (push_congr hps (fun _ => Equiv.rfl)) (LEq.refl is) his
  have hmajor : pempty ∈ Ed M (fapps F (ps₀ ++ is)) :=
    mem_congr_right (ed_congr M (fapps_congr_args F hargs))
      (mem_congr_left hc0 hc)
  have hT := PiRawMotiveAny.motive_mem_U M hU σ f ls Ps Is ps₀ is hps₀
    mo pempty v hmo his₀ hmajor
  have hg := PiRawMotiveAny.guarded_key M σ (evalTotal σ v) F mo ps₀ Is
    (push ps₀ ρ0) is pempty his₀ hmajor hT
  have hz₀ : z ∈ Ed M (fapps mo (is ++ [pempty])) := by
    rw [fapps_append]
    exact mem_congr_right
      (ed_congr M (fapp_congr (Equiv.refl (fapps mo is)) hc0)) hz
  have hk : key (ps ++ is) = key (ps₀ ++ is) := (key_eq_iff _ _).mpr hargs
  rw [hk]
  exact mem_congr_right hg.symm hz₀

/-- The actual evaluation decomposition supplies the root and original dependent indices. -/
theorem Eval.mem_guarded {C : Context} {i : Index.{4}} {z : PSet.{4}}
    (hEval : Eval C i z) (v : Level) (hU : C.M.U = U W4)
    (hMotive : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref (policyFamilyLevels C.node.a.family))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hIndex : ∀ (j : Fin C.node.a.constructors.length) ps xs,
      LEq ps C.parameters →
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps →
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs →
      TelFits C.M C.σ C.node.a.family.indices (push ps ρ0) (C.indicesAt j ps xs))
    (hCtor : ∀ (j : Fin C.node.a.constructors.length) ps xs,
      LEq ps C.parameters →
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps →
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs →
      C.constructorAt j ps xs ∈ Ed C.M
        (fapps (C.M.μ C.node.a.family.ref
          ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ)))
          (ps ++ C.indicesAt j ps xs)))
    (hCtor0 : ∀ (j : Fin C.node.a.constructors.length) ps xs,
      LEq ps C.parameters →
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps →
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs →
      Equiv (C.constructorAt j ps xs) pempty) :
    z ∈ PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
      (C.M.μ C.node.a.family.ref ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ)))
      C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i pempty := by
  obtain ⟨j, ps, xs, hkey, hps, hp, hx, hz⟩ := hEval.result_typed
  have hps₀ : C.parameters.length = C.node.a.family.parameters.length :=
    hps.length.symm.trans hp.length
  have hr := endpoint_mem_guarded C.M hU C.σ C.node.a.family.ref
    (policyFamilyLevels C.node.a.family) C.node.a.family.parameters C.node.a.family.indices
    C.parameters hps₀ C.motive v hMotive ps (C.indicesAt j ps xs)
    (C.constructorAt j ps xs) z hps (hIndex j ps xs hps hp hx)
    (hCtor j ps xs hps hp hx) (hCtor0 j ps xs hps hp hx) hz
  rw [hkey]
  exact hr

/-- Any representative in a proof fibre has the same guarded motive as pempty.
This is the major-argument transport required by the indexed builder. -/
theorem guarded_mem_at_proof (M : Interp.{4}) (σ : Nat → Nat) (k : Nat)
    (F mo : PSet.{4}) (ps : List PSet.{4}) (Is : List (Expr Nat)) (ρ : Nat → PSet.{4})
    (i : Index.{4}) (x z : PSet.{4})
    (hx : x ∈ proofFibre M F i)
    (hz : z ∈ PiRawMotiveAny.guarded M σ k F mo ps Is ρ i pempty) :
    z ∈ PiRawMotiveAny.guarded M σ k F mo ps Is ρ i x := by
  have he : Equiv x pempty := (mem_tv.mp hx).2
  exact mem_congr_right (PiRawMotiveAny.guarded_resp M σ k F mo ps Is ρ i he).symm hz

end Rcic.F3.PSet.PropEval
