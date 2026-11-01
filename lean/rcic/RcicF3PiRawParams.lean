import rcic.RcicF3PiRawIH
import rcic.RcicF3PiAdmission
/-! Admission-derived parameter readback for actual raw IH types.
The actual parameter/prior-binder blocks pay the prefix equation; ordinary
EnvSound/BodiesOK and actual field membership pay normalization. Universal
raw signature/input assembly remains open. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawParams
open Rcic.Declarative
universe u
/-- Elementary evaluation of canonical parameter locals through the actual
parameter, preceding-binder and recursive-field argument blocks. -/
theorem param_prefix (M : Interp.{u}) (σ : Nat → Nat)
    (ps pre xs : List PSet.{u}) (ρ : Nat → PSet.{u})
    (ix : List (Expr Nat)) :
    ((policyParameterLocals ps.length (pre.length + xs.length) ++ ix).take ps.length).map
      (den M σ (push xs (push pre (push ps ρ)))) = ps := by
  have ht := List.take_left (policyParameterLocals ps.length (pre.length + xs.length)) ix
  rw [policyParameterLocals_length] at ht
  rw [ht]
  have h := den_paramLocals M σ ps (pre ++ xs) ρ
  rw [List.length_append, push_append, push_append] at h
  exact h
/-- Admission fixes the complete parameter prefix, even with arbitrary prior
binders and arbitrary recursive Pi depth. No semantic prefix equation is assumed. -/
theorem admitted_readback (M : Interp.{u}) (σ : Nat → Nat)
    (ps pre : List PSet.{u}) (ρ : Nat → PSet.{u})
    {E : ResolvedEnv} {fuel f nu ni inner : Nat} {T : Expr Nat}
    {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu ps.length ni (ps.length + pre.length) T =
      .permitted (.recursive inner) idx) :
    ∃ ds ix, ds.length = inner ∧ ix.length = ni ∧
      piTelescopeFuel E (fuel - 1) T = some (ds,
        foldApps (.const f ((List.range nu).map Level.param))
          (policyParameterLocals ps.length (pre.length + ds.length) ++ ix)) ∧
      ∀ xs, xs.length = ds.length →
        ((policyParameterLocals ps.length (pre.length + ds.length) ++ ix).take ps.length).map
          (den M σ (push xs (push pre (push ps ρ)))) = ps := by
  obtain ⟨ds, b, hr, hl, _, _, hp⟩ := PiIndependent.recursive_scans h
  obtain ⟨ix, hb, hi, _⟩ := properFamilyFuel_shape (by omega) hp
  rw [show ds.length + (ps.length + pre.length) =
    ps.length + (pre.length + ds.length) by omega, paramLocals_top] at hb
  refine ⟨ds, ix, hl, hi, ?_, ?_⟩
  · rw [← hb]; exact hr
  · intro xs hxs
    rw [← hxs]
    exact param_prefix M σ ps pre xs ρ ix
/-- Composition with actual raw field membership and the executable IH
builder. Admission and the actual binder blocks pay parameter readback.
Ordinary environment soundness is retained for hidden-field normalization. -/
theorem admitted_builder_spec (M : Interp.{4}) (hU : M.U = U W4)
    (σ K : Nat → Nat) (f nu : Nat) (φ : PiIndex.Index.{4} → Prop)
    (Ps Is : List (Expr Nat)) (ps pre : List PSet.{4}) (hps : ps.length = Ps.length)
    (hF : Equiv (M.μ f (((List.range nu).map Level.param).map (evalTotal σ)))
      (PiValue.value M σ φ (Ps ++ Is) ρ0))
    (mo : PSet.{4})
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ((List.range nu).map Level.param))
        (policyLocals (Ps.length + Is.length))) (.sort .zero)))))
    {E : ResolvedEnv} {n : Nat} (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K)
    (fuel inner : Nat) (A Mx : Expr Nat) (idx : List (Expr Nat))
    (h : fieldAnalyze E fuel f nu Ps.length Is.length (Ps.length + pre.length)
      (Rcic.Declarative.lift 0 1 A) = .permitted (.recursive inner) idx)
    (hI : InstOK E σ K (Rcic.Declarative.lift 0 1 A))
    (hMx : den M σ (push pre (push ps ρ0)) (Rcic.Declarative.lift 0 1 Mx) = mo)
    (hx : push pre (push ps ρ0) 0 ∈ Ed M
      (den M σ (push pre (push ps ρ0)) (Rcic.Declarative.lift 0 1 A))) :
    ∃ ds args ih, ds.length = inner ∧ args.length = (Ps ++ Is).length ∧
      piTelescopeFuel E (fuel - 1) (Rcic.Declarative.lift 0 1 A) =
        some (ds, foldApps (.const f ((List.range nu).map Level.param)) args) ∧
      funIHType E (fuel - 1) Ps.length A Mx inner = some ih ∧
      Equiv ((PiIndex.tel M σ ds args (push pre (push ps ρ0))).erasedIHType M
        (PiRawMotive.guarded M σ
          (M.μ f (((List.range nu).map Level.param).map (evalTotal σ))) mo ps Is (push ps ρ0))
        (push pre (push ps ρ0) 0))
        (den M σ (push pre (push ps ρ0)) ih) := by
  have h' : fieldAnalyze E fuel f nu ps.length Is.length (ps.length + pre.length)
      (Rcic.Declarative.lift 0 1 A) = .permitted (.recursive inner) idx := by
    simpa only [hps] using h
  obtain ⟨ds, ix, hl, hi, hr, hp⟩ := admitted_readback M σ ps pre ρ0 h'
  let args := policyParameterLocals ps.length (pre.length + ds.length) ++ ix
  have ha : args.length = (Ps ++ Is).length := by
    simp only [args, List.length_append, policyParameterLocals_length, hi, hps]
  let ih := policyPi ds (foldApps (Rcic.Declarative.lift 0 ds.length
    (Rcic.Declarative.lift 0 1 Mx)) (args.drop Ps.length ++ [PiRawIH.fieldApp ds.length]))
  have hih : funIHType E (fuel - 1) Ps.length A Mx ds.length = some ih :=
    PiRawIH.funIHType_eq E (fuel - 1) Ps.length A Mx ds args f _ hr
  have hn := den_piTelescope_of_mem M σ K hE hb (fuel - 1)
    (Rcic.Declarative.lift 0 1 A) ds _ (push pre (push ps ρ0)) _ hr hI hx
  have hx' := mem_congr_right (ed_congr M hn.symm) hx
  refine ⟨ds, args, ih, hl, ha, hr, ?_, ?_⟩
  · rw [← hl]; exact hih
  · exact PiRawIH.builder_spec M hU σ f _ φ Ps Is ps hps hF mo hmo E (fuel - 1)
      A ds args ha (push pre (push ps ρ0))
      (fun xs hxs => by rw [← hps]; exact hp xs hxs.length) Mx hMx hr ih hih hx'
end Rcic.F3.PSet.PiRawParams
