import rcic.RcicF3RawFamilyMinorInputs

/-!
# Complete admitted minor input production and application

The public producer starts from the original fieldShapesFuel success. It
derives the normalized views, the initial motive/minor prefix insertion,
every interleaved IH, and childness below the actual constructor. The typed
minor then consumes the produced spine at its original dependent endpoint.
Frame existence and the ordinary environment/motive/local-map inputs remain
explicit; this is not universal StepAG.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.RawFamilyMinor
open Rcic.Declarative PiIndex RawFamily

theorem inputs_of_admitted (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (σ K : Nat → Nat) (nu : Nat) (hB : FamBounded fd nu)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (h0 : evalTotal σ fd.resLevel ≠ 0) :
    let vs := (canonL nu).map (evalTotal σ)
    let M := mkM P (table P μ fd C)
    ∀ (v : Level) (ps pre : List PSet.{4}) (hps : ps.length = fd.params.length)
      (mo : PSet.{4}) (g : PSet.{4} → PSet.{4})
      (hg : ∀ a b, Equiv a b → Equiv (g a) (g b))
      (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
        (policyPi fd.indices (.pi (foldApps (.const fd.fref (canonL nu))
          (policyLocals (fd.params.length + fd.indices.length))) (.sort v)))))
      (E : ResolvedEnv) (n : Nat) (htf : TypeFacts E)
      (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K)
      (fuel j : Nat) (ss : List FieldShape) (Fs : List (Expr Nat))
      (Tend Mx acc : Expr Nat) (xs : List PSet.{4})
      (hsh : fieldShapesFuel E fuel fd.fref nu fd.params.length fd.indices.length
        fd.params.length Fs = some ss)
      (hI : ∀ A ∈ Fs, InstOK E σ K A)
      (hx : TelFits M σ Fs (push ps ρ0) xs)
      (hMx : den M σ (push pre (push ps ρ0)) Mx = mo)
      (hmap : ∀ i y, RawFamilyRec.paramKey ps.length i = key ps →
        MemT y (dataVal j xs) → y ∈ C vs i → g y ∈
          PiRawMotiveAny.guarded M σ (evalTotal σ v) (M.μ fd.fref vs)
            mo ps fd.indices (push ps ρ0) i y),
    ∃ out, PiRawMinor.Inputs M σ E fuel fd.params.length Mx acc ss
      (Rcic.Declarative.lift 0 pre.length (policyPi Fs Tend))
      (push pre (push ps ρ0)) xs (RecPlan.args g ss xs) out := by
  dsimp only
  intro v ps pre hps mo g hg hmo E n htf hE hb fuel j ss Fs Tend Mx acc xs hsh hI hx hMx hmap
  let M := mkM P (table P μ fd C)
  have hcl : EnvClosed E := fun r m hm =>
    ⟨(htf r m hm).1, fun b hb => ((htf r m hm).2.2 b hb).1⟩
  have hv0 := PiRawFieldViews.of_fields Fs 0 ss
    (by simpa only [Nat.add_zero] using hsh)
  have hv : PiRawFieldViews.Views E fuel fd.fref nu fd.params.length fd.indices.length
      pre.length ss (liftFields pre.length Fs 0) := by
    simpa only [Nat.zero_add] using hv0.lift hcl 0 pre.length (Nat.zero_le _)
  have hfits : TelFits M σ (liftFields pre.length Fs 0) (push pre (push ps ρ0)) xs :=
    (TelFits_liftFields M σ pre (push ps ρ0) Fs [] xs).mpr hx
  obtain ⟨out, hout⟩ := inputs_of_views P μ fd C hC σ K nu hB hf h0
    v ps hps mo (dataVal j xs) g hg hmo hmap E n htf hE hb fuel
    ss (liftFields pre.length Fs 0) pre.length hv pre rfl
    (Rcic.Declarative.lift Fs.length pre.length Tend) Mx acc xs
    (instOK_liftFields Fs hI pre.length 0) hMx hfits
    (fun x hx => memT_dataVal hx)
  refine ⟨out, ?_⟩
  rw [lift_policyPi, Nat.zero_add]
  exact hout


/-- On the data-family face, a stored typed minor consumes the produced spine.
Its result uses the original constructor fields and dependent indices; inserted
motive/minor/IH binders are removed from that endpoint. -/
theorem apply_admitted (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (σ K : Nat → Nat) (nu : Nat) (hB : FamBounded fd nu)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (h0 : evalTotal σ fd.resLevel ≠ 0) :
    let vs := (canonL nu).map (evalTotal σ)
    let M := mkM P (table P μ fd C)
    ∀ (v : Level) (ps pre : List PSet.{4}) (hps : ps.length = fd.params.length)
      (mo : PSet.{4}) (g : PSet.{4} → PSet.{4})
      (hg : ∀ a b, Equiv a b → Equiv (g a) (g b))
      (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
        (policyPi fd.indices (.pi (foldApps (.const fd.fref (canonL nu))
          (policyLocals (fd.params.length + fd.indices.length))) (.sort v)))))
      (E : ResolvedEnv) (n : Nat) (htf : TypeFacts E)
      (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K)
      (fuel j : Nat) (ss : List FieldShape) (Fs : List (Expr Nat))
      (Tend Mx acc : Expr Nat) (xs : List PSet.{4})
      (hsh : fieldShapesFuel E fuel fd.fref nu fd.params.length fd.indices.length
        fd.params.length Fs = some ss)
      (hI : ∀ A ∈ Fs, InstOK E σ K A)
      (hx : TelFits M σ Fs (push ps ρ0) xs)
      (hMx : den M σ (push pre (push ps ρ0)) Mx = mo)
      (hmap : ∀ i y, RawFamilyRec.paramKey ps.length i = key ps →
        MemT y (dataVal j xs) → y ∈ C vs i → g y ∈
          PiRawMotiveAny.guarded M σ (evalTotal σ v) (M.μ fd.fref vs)
            mo ps fd.indices (push ps ρ0) i y)
      (R : Expr Nat) (F : PSet.{4})
      (hR : minorFromTelescope E fuel fd.params.length Mx acc ss
        (Rcic.Declarative.lift 0 pre.length (policyPi Fs Tend)) = some R)
      (hF : F ∈ Ed M (den M σ (push pre (push ps ρ0)) R)),
    fapps F (RecPlan.args g ss xs) ∈ Ed M
      (fapp (fapps mo ((familyIdx fd.params.length Tend).map
        (den M σ (push xs (push ps ρ0)))))
        (fapps (den M σ (push pre (push ps ρ0)) acc) xs)) := by
  dsimp only
  intro v ps pre hps mo g hg hmo E n htf hE hb fuel j ss Fs Tend Mx acc xs
    hsh hI hx hMx hmap R F hR hF
  let M := mkM P (table P μ fd C)
  obtain ⟨out, hout⟩ := inputs_of_admitted P μ fd C hC σ K nu hB hf h0
    v ps pre hps mo g hg hmo E n htf hE hb fuel j ss Fs Tend Mx acc xs
    hsh hI hx hMx hmap
  have he := PiRawMinor.apply_endpoint M σ E fuel fd.params.length hout hR hF
    (liftFields pre.length Fs 0) (Rcic.Declarative.lift Fs.length pre.length Tend)
    (by rw [lift_policyPi, Nat.zero_add])
    (by rw [liftFields_length']; exact hx.length.symm)
  rw [hMx, familyIdx_lift, List.map_map] at he
  have hden : (den M σ (push xs (push pre (push ps ρ0))) ∘
      Rcic.Declarative.lift Fs.length pre.length) = den M σ (push xs (push ps ρ0)) := by
    funext e
    rw [← hx.length]
    exact den_lift_push M σ xs pre (push ps ρ0) e
  rw [hden] at he
  exact he

end Rcic.F3.PSet.RawFamilyMinor
