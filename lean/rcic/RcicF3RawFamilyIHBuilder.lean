import rcic.RcicF3RawFamilyLevels
import rcic.RcicF3PiRawIHAny
/-! Actual IH membership from original field admission, inserted binders,
and local recursion at a fixed parameter slice. The motive may have any
admitted sort. Family boundedness pays universe agreement internally.
This does not assemble the typed minor spine or produce a small frame.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyIH
open Rcic.Declarative PiIndex RawFamily
theorem admitted_builder_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (σ K : Nat → Nat) (nu : Nat) (hB : FamBounded fd nu)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (h0 : evalTotal σ fd.resLevel ≠ 0) :
    let vs := (canonL nu).map (evalTotal σ)
    let M := mkM P (table P μ fd C)
    ∀ (v : Level) (ps pre : List PSet.{4}) (hps : ps.length = fd.params.length)
      (mo x z : PSet.{4}) (g : PSet.{4} → PSet.{4})
      (hg : ∀ a b, Equiv a b → Equiv (g a) (g b))
      (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
        (policyPi fd.indices (.pi (foldApps (.const fd.fref (canonL nu))
          (policyLocals (fd.params.length + fd.indices.length))) (.sort v)))))
      (hmap : ∀ i y, RawFamilyRec.paramKey ps.length i = key ps →
        MemT y z → y ∈ C vs i → g y ∈
          PiRawMotiveAny.guarded M σ (evalTotal σ v) (M.μ fd.fref vs)
            mo ps fd.indices (push ps ρ0) i y)
      (E : ResolvedEnv) (n : Nat) (htf : TypeFacts E)
      (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K)
      (fuel inner prior c a : Nat) (T Mx : Expr Nat) (idx : List (Expr Nat))
      (hc : c ≤ prior) (hpre : pre.length = prior + a)
      (h : fieldAnalyze E fuel fd.fref nu fd.params.length fd.indices.length
        (fd.params.length + prior) T = .permitted (.recursive inner) idx)
      (hI : InstOK E σ K (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift c a T)))
      (hMx : den M σ (vcons x (push pre (push ps ρ0)))
        (Rcic.Declarative.lift 0 1 Mx) = mo)
      (hx : x ∈ Ed M (den M σ (vcons x (push pre (push ps ρ0)))
        (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift c a T))))
      (hxz : MemT x z),
    ∃ ih, funIHType E (fuel - 1) fd.params.length
      (Rcic.Declarative.lift c a T) Mx inner = some ih ∧
      ihAtN g inner x ∈ Ed M (den M σ (vcons x (push pre (push ps ρ0))) ih) := by
  dsimp only
  intro v ps pre hps mo x z g hg hmo hmap E n htf hE hb fuel inner prior c a T Mx idx
    hc hpre h hI hMx hx hxz
  let vs := (canonL nu).map (evalTotal σ)
  let M := mkM P (table P μ fd C)
  let ρ := vcons x (push pre (push ps ρ0))
  let Q := PiRawMotiveAny.guarded M σ (evalTotal σ v) (M.μ fd.fref vs)
    mo ps fd.indices (push ps ρ0)
  have hσ : ∀ i, i < nu → σ i = σOf vs i := fun i hi => (σOf_canon σ nu i hi).symm
  have hF : Equiv (M.μ fd.fref vs)
      (piLam M σ (endValue C vs (fd.params.length + fd.indices.length)) ρ0 (famType fd)) := by
    change Equiv (table P μ fd C fd.fref vs) _
    rw [show table P μ fd C fd.fref vs = ofFrame P μ fd C vs from upd_eq _ _ _ _]
    exact (ofFrame_updated_levels P μ fd C vs σ nu hB hσ hf).symm
  have h' : fieldAnalyze E fuel fd.fref nu ps.length fd.indices.length
      (ps.length + prior) T = .permitted (.recursive inner) idx := by simpa only [hps] using h
  obtain ⟨ds, args, hl, ha, hr, hp⟩ :=
    PiRawRename.admitted_ih_read M σ ps pre ρ0 x htf hc hpre h'
  have ha' : args.length = (fd.params ++ fd.indices).length := by
    rw [ha, List.length_append, hps]
  let A := Rcic.Declarative.lift c a T
  let ih := policyPi ds (foldApps (Rcic.Declarative.lift 0 ds.length
    (Rcic.Declarative.lift 0 1 Mx))
    (args.drop fd.params.length ++ [PiRawIH.fieldApp ds.length]))
  have hih : funIHType E (fuel - 1) fd.params.length A Mx ds.length = some ih :=
    PiRawIH.funIHType_eq E (fuel - 1) fd.params.length A Mx ds args fd.fref _ hr
  have hn := den_piTelescope_of_mem M σ K hE hb (fuel - 1)
    (Rcic.Declarative.lift 0 1 A) ds _ ρ x hr hI hx
  have hx' := mem_congr_right (ed_congr M hn.symm) hx
  have hp' : ∀ p, RawFamilyRec.paramKey ps.length ((tel M σ ds args ρ).result p) = key ps :=
    PiLeafParams.result_parameters M σ ds args ρ ps (fun xs hxs => hp xs hxs.length)
  have h0' : evalTotal (σOf vs) fd.resLevel ≠ 0 := by
    rw [← evalTotal_agree hσ fd.resLevel hB.res]
    exact h0
  have hmem := ih_mem_at_parameters_at P μ fd C hC hf vs σ h0'
    (canonL nu) rfl ds args ha' ρ ps hp' Q
    (PiRawMotiveAny.guarded_dich M σ (evalTotal σ v) (M.μ fd.fref vs)
      mo ps fd.indices (push ps ρ0))
    g hg z x hmap hx' hxz
  have he := PiRawIHAny.builder_spec M rfl σ fd.fref (canonL nu)
    (endValue C vs (fd.params.length + fd.indices.length)) (endValue_resp C vs _)
    fd.resLevel v fd.params fd.indices ps hps hF mo hmo E (fuel - 1) A ds args ha' ρ
    (fun xs hxs => by rw [← hps]; exact hp xs hxs.length) Mx hMx hr ih hih hx'
  refine ⟨ih, ?_, ?_⟩
  · rw [← hl]; exact hih
  · rw [← hl]
    exact mem_congr_right (ed_congr M he) hmem
end Rcic.F3.PSet.RawFamilyIH
