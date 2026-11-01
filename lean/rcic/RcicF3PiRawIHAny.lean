import rcic.RcicF3PiRawMotiveAny
import rcic.RcicF3PiRawRename
import rcic.RcicF3RawFamilyLaws
/-! Raw recursive-field IH fidelity at the typed motive universe. Complete
parameter/index keys and original field admission are preserved. These are
components for A; no universal frame or A producer is claimed.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawIHAny
open Rcic.Declarative PiIndex PiRawIH

/-- Fitting majors from a constructed family table pay the exact raw IH leaf.
The family payload is extensionally responsive by construction; no motive
shape, recursive map, or semantic prefix wall is introduced. -/
theorem normalized_spec (M : Interp.{4}) (hU : M.U = U W4) (σ : Nat → Nat)
    (f : Nat) (ls : List Level) (g : (Nat → PSet.{4}) → PSet.{4}) (hg : EnvResp g) (w v : Level)
    (Ps Is : List (Expr Nat)) (ps : List PSet.{4}) (hps : ps.length = Ps.length)
    (hF : Equiv (M.μ f (ls.map (evalTotal σ)))
      (piLam M σ g ρ0 (policyPi (Ps ++ Is) (.sort w))))
    (mo : PSet.{4})
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ls) (policyLocals (Ps.length + Is.length)))
        (.sort v)))))
    (ds args : List (Expr Nat)) (ha : args.length = (Ps ++ Is).length)
    (ρ : Nat → PSet.{4})
    (hprefix : ∀ xs, TelFits M σ ds ρ xs →
      (args.take Ps.length).map (den M σ (push xs ρ)) = ps)
    (Mx : Expr Nat) (hMx : den M σ ρ Mx = mo)
    (hx : ρ 0 ∈ Ed M (den M σ ρ
      (policyPi ds (foldApps (.const f ls) args)))) :
    Equiv ((PiIndex.tel M σ ds args ρ).erasedIHType M
      (PiRawMotiveAny.guarded M σ (evalTotal σ v) (M.μ f (ls.map (evalTotal σ))) mo ps Is (push ps ρ0))
      (ρ 0))
      (den M σ ρ (policyPi ds (foldApps (Rcic.Declarative.lift 0 ds.length Mx)
        (args.drop Ps.length ++ [fieldApp ds.length])))) := by
  let F := M.μ f (ls.map (evalTotal σ))
  let C := PiRawMotiveAny.guarded M σ (evalTotal σ v) F mo ps Is (push ps ρ0)
  apply PiSyntaxIH.compile_spec M σ (read M σ args) C
    (PiRawMotiveAny.guarded_dich M σ (evalTotal σ v) F mo ps Is (push ps ρ0))
  apply (PiSyntaxIH.endEq_iff M σ (read M σ args) C _ ds ρ (ρ 0)).mpr
  intro xs hxs
  let js := (args.drop Ps.length).map (den M σ (push xs ρ))
  let z := fapps (ρ 0) xs
  have he : args.map (den M σ (push xs ρ)) = ps ++ js := by
    have he := congrArg (fun as => as.map (den M σ (push xs ρ)))
      (List.take_append_drop Ps.length args)
    dsimp only at he
    rw [List.map_append, hprefix xs hxs] at he
    exact he.symm
  have hz : z ∈ Ed M (fapps F (ps ++ js)) := by
    have ht := mem_fapps M σ (foldApps (.const f ls) args) ds ρ (ρ 0) xs hx hxs
    rw [den_foldApps, he] at ht
    exact ht
  have hl : (ps ++ js).length = (Ps ++ Is).length := by
    rw [← he, List.length_map, ha]
  have hne : ¬ Equiv (fapps (piLam M σ g ρ0
      (policyPi (Ps ++ Is) (.sort w))) (ps ++ js)) pempty := by
    intro heq
    exact not_mem_pempty (mem_congr_right
      ((ed_congr M ((fapps_congr hF (ps ++ js)).trans heq)).trans (ed_pempty M)) hz)
  have hfit := fits_of_fapps_ne M σ hg (.sort w) (Ps ++ Is) ρ0 (ps ++ js) hl hne
  have his := fits_tail M σ Ps Is ρ0 ps js hps hfit
  have htype := PiRawMotiveAny.motive_mem_U M hU σ f ls Ps Is ps js hps mo z v hmo his hz
  have hguard := PiRawMotiveAny.guarded_key M σ (evalTotal σ v) F mo ps Is
    (push ps ρ0) js z his hz htype
  have htag := PiTypedCompile.tyv_ed_of_mem_U M W4 (evalTotal σ v)
    (by rw [← hU]; exact htype)
  have hr : read M σ args (push xs ρ) = key (ps ++ js) := congrArg key he
  change Equiv (tyv (C (read M σ args (push xs ρ)) z)) _
  rw [hr]
  have hden : den M σ (push xs ρ)
      (foldApps (Rcic.Declarative.lift 0 ds.length Mx)
        (args.drop Ps.length ++ [fieldApp ds.length])) = fapps mo (js ++ [z]) := by
    rw [den_foldApps, ← hxs.length, den_lift0_push, hMx,
      List.map_append, List.map_cons, List.map_nil, den_fieldApp]
  rw [hden]
  exact (tyv_congr hguard).trans htag

/-- Composition with executable funIHType at arbitrary depth. -/
theorem builder_spec (M : Interp.{4}) (hU : M.U = U W4) (σ : Nat → Nat)
    (f : Nat) (ls : List Level) (g : (Nat → PSet.{4}) → PSet.{4}) (hg : EnvResp g) (w v : Level)
    (Ps Is : List (Expr Nat)) (ps : List PSet.{4}) (hps : ps.length = Ps.length)
    (hF : Equiv (M.μ f (ls.map (evalTotal σ)))
      (piLam M σ g ρ0 (policyPi (Ps ++ Is) (.sort w))))
    (mo : PSet.{4})
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ls) (policyLocals (Ps.length + Is.length)))
        (.sort v)))))
    (E : ResolvedEnv) (fuel : Nat) (A : Expr Nat)
    (ds args : List (Expr Nat)) (ha : args.length = (Ps ++ Is).length)
    (ρ : Nat → PSet.{4})
    (hprefix : ∀ xs, TelFits M σ ds ρ xs →
      (args.take Ps.length).map (den M σ (push xs ρ)) = ps)
    (Mx : Expr Nat) (hMx : den M σ ρ (Rcic.Declarative.lift 0 1 Mx) = mo)
    (hread : piTelescopeFuel E fuel (Rcic.Declarative.lift 0 1 A) =
      some (ds, foldApps (.const f ls) args))
    (ih : Expr Nat) (hih : funIHType E fuel Ps.length A Mx ds.length = some ih)
    (hx : ρ 0 ∈ Ed M (den M σ ρ
      (policyPi ds (foldApps (.const f ls) args)))) :
    Equiv ((PiIndex.tel M σ ds args ρ).erasedIHType M
      (PiRawMotiveAny.guarded M σ (evalTotal σ v) (M.μ f (ls.map (evalTotal σ))) mo ps Is (push ps ρ0))
      (ρ 0))
      (den M σ ρ ih) := by
  have he := funIHType_eq E fuel Ps.length A Mx ds args f ls hread
  have hi := Option.some.inj (he.symm.trans hih)
  rw [← hi]
  exact normalized_spec M hU σ f ls g hg w v Ps Is ps hps hF mo hmo ds args ha ρ
    hprefix (Rcic.Declarative.lift 0 1 Mx) hMx hx

/-- Original fieldAnalyze admission survives binder insertion. Readback and
fitting motive exactness are derived, and funIHType success is a conclusion. -/
theorem builder_original (M : Interp.{4}) (hU : M.U = U W4)
    (σ K : Nat → Nat) (f nu : Nat) (g : (Nat → PSet.{4}) → PSet.{4}) (hg : EnvResp g) (w v : Level)
    (Ps Is : List (Expr Nat)) (ps pre : List PSet.{4}) (hps : ps.length = Ps.length)
    (hF : Equiv (M.μ f (((List.range nu).map Level.param).map (evalTotal σ)))
      (piLam M σ g ρ0 (policyPi (Ps ++ Is) (.sort w))))
    (mo x : PSet.{4})
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ((List.range nu).map Level.param))
        (policyLocals (Ps.length + Is.length))) (.sort v)))))
    {E : ResolvedEnv} {n : Nat} (htf : TypeFacts E)
    (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K)
    (fuel inner prior c a : Nat) (T Mx : Expr Nat) (idx : List (Expr Nat))
    (hc : c ≤ prior) (hpre : pre.length = prior + a)
    (h : fieldAnalyze E fuel f nu Ps.length Is.length (Ps.length + prior) T =
      .permitted (.recursive inner) idx)
    (hI : InstOK E σ K (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift c a T)))
    (hMx : den M σ (vcons x (push pre (push ps ρ0)))
      (Rcic.Declarative.lift 0 1 Mx) = mo)
    (hx : x ∈ Ed M (den M σ (vcons x (push pre (push ps ρ0)))
      (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift c a T)))) :
    ∃ ds args ih, ds.length = inner ∧ args.length = (Ps ++ Is).length ∧
      piTelescopeFuel E (fuel - 1)
        (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift c a T)) =
        some (ds, foldApps (.const f ((List.range nu).map Level.param)) args) ∧
      funIHType E (fuel - 1) Ps.length (Rcic.Declarative.lift c a T) Mx inner = some ih ∧
      Equiv ((PiIndex.tel M σ ds args (vcons x (push pre (push ps ρ0)))).erasedIHType M
        (PiRawMotiveAny.guarded M σ (evalTotal σ v)
          (M.μ f (((List.range nu).map Level.param).map (evalTotal σ))) mo ps Is (push ps ρ0)) x)
        (den M σ (vcons x (push pre (push ps ρ0))) ih) := by
  have h' : fieldAnalyze E fuel f nu ps.length Is.length (ps.length + prior) T =
      .permitted (.recursive inner) idx := by simpa only [hps] using h
  obtain ⟨ds, args, hl, ha, hr, hp⟩ := PiRawRename.admitted_ih_read M σ ps pre ρ0 x htf hc hpre h'
  have ha' : args.length = (Ps ++ Is).length := by
    rw [ha, List.length_append, hps]
  let A := Rcic.Declarative.lift c a T
  let ρ := vcons x (push pre (push ps ρ0))
  let ih := policyPi ds (foldApps (Rcic.Declarative.lift 0 ds.length
    (Rcic.Declarative.lift 0 1 Mx)) (args.drop Ps.length ++ [PiRawIH.fieldApp ds.length]))
  have hih : funIHType E (fuel - 1) Ps.length A Mx ds.length = some ih :=
    PiRawIH.funIHType_eq E (fuel - 1) Ps.length A Mx ds args f _ hr
  have hn := den_piTelescope_of_mem M σ K hE hb (fuel - 1)
    (Rcic.Declarative.lift 0 1 A) ds _ ρ x hr hI hx
  have hx' := mem_congr_right (ed_congr M hn.symm) hx
  refine ⟨ds, args, ih, hl, ha', hr, ?_, ?_⟩
  · rw [← hl]; exact hih
  · exact builder_spec M hU σ f _ g hg w v Ps Is ps hps hF mo hmo E (fuel - 1)
      A ds args ha' ρ (fun xs hxs => by rw [← hps]; exact hp xs hxs.length)
      Mx hMx hr ih hih hx'

/-- The constructed raw family discharges responsiveness on proof and data faces.
No admissibility or closure premise is needed for this IH-fidelity adapter. -/
theorem rawFamily_spec (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : RawFamily.Frame) (vs : List Nat)
    (f : Nat) (ls : List Level) (v : Level)
    (ps : List PSet.{4}) (hps : ps.length = fd.params.length)
    (hF : Equiv ((mkM P μ).μ f (ls.map (evalTotal (σOf vs))))
      (RawFamily.ofFrame P μ fd C vs))
    (mo : PSet.{4})
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0)
      (policyPi fd.indices (.pi (foldApps (.const f ls) (policyLocals (fd.params.length + fd.indices.length)))
        (.sort v)))))
    (ds args : List (Expr Nat)) (ha : args.length = (fd.params ++ fd.indices).length)
    (ρ : Nat → PSet.{4})
    (hprefix : ∀ xs, TelFits (mkM P μ) (σOf vs) ds ρ xs →
      (args.take fd.params.length).map (den (mkM P μ) (σOf vs) (push xs ρ)) = ps)
    (Mx : Expr Nat) (hMx : den (mkM P μ) (σOf vs) ρ Mx = mo)
    (hx : ρ 0 ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ
      (policyPi ds (foldApps (.const f ls) args)))) :
    Equiv ((PiIndex.tel (mkM P μ) (σOf vs) ds args ρ).erasedIHType (mkM P μ)
      (PiRawMotiveAny.guarded (mkM P μ) (σOf vs) (evalTotal (σOf vs) v) ((mkM P μ).μ f (ls.map (evalTotal (σOf vs)))) mo ps fd.indices (push ps ρ0))
      (ρ 0))
      (den (mkM P μ) (σOf vs) ρ (policyPi ds (foldApps (Rcic.Declarative.lift 0 ds.length Mx)
        (args.drop fd.params.length ++ [fieldApp ds.length])))) := by
  exact normalized_spec (mkM P μ) rfl (σOf vs) f ls
    (RawFamily.endValue C vs (fd.params.length + fd.indices.length))
    (RawFamily.endValue_resp C vs _) fd.resLevel v fd.params fd.indices ps hps
    hF mo hmo ds args ha ρ hprefix Mx hMx hx

/-- Constructed-frame composition retains original admission and executable
success, with no new global motive or frame-closure premise. -/
theorem rawFamily_builder_original (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : RawFamily.Frame) (vs : List Nat) (K : Nat → Nat) (f nu : Nat) (v : Level)
    (ps pre : List PSet.{4}) (hps : ps.length = fd.params.length)
    (hF : Equiv ((mkM P μ).μ f (((List.range nu).map Level.param).map (evalTotal (σOf vs))))
      (RawFamily.ofFrame P μ fd C vs))
    (mo x : PSet.{4})
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0)
      (policyPi fd.indices (.pi (foldApps (.const f ((List.range nu).map Level.param))
        (policyLocals (fd.params.length + fd.indices.length))) (.sort v)))))
    {E : ResolvedEnv} {n : Nat} (htf : TypeFacts E)
    (hE : EnvSound (mkM P μ) (σOf vs) K E n) (hb : BodiesOK E (σOf vs) K)
    (fuel inner prior c a : Nat) (T Mx : Expr Nat) (idx : List (Expr Nat))
    (hc : c ≤ prior) (hpre : pre.length = prior + a)
    (h : fieldAnalyze E fuel f nu fd.params.length fd.indices.length (fd.params.length + prior) T =
      .permitted (.recursive inner) idx)
    (hI : InstOK E (σOf vs) K (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift c a T)))
    (hMx : den (mkM P μ) (σOf vs) (vcons x (push pre (push ps ρ0)))
      (Rcic.Declarative.lift 0 1 Mx) = mo)
    (hx : x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (vcons x (push pre (push ps ρ0)))
      (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift c a T)))) :
    ∃ ds args ih, ds.length = inner ∧ args.length = (fd.params ++ fd.indices).length ∧
      piTelescopeFuel E (fuel - 1)
        (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift c a T)) =
        some (ds, foldApps (.const f ((List.range nu).map Level.param)) args) ∧
      funIHType E (fuel - 1) fd.params.length (Rcic.Declarative.lift c a T) Mx inner = some ih ∧
      Equiv ((PiIndex.tel (mkM P μ) (σOf vs) ds args (vcons x (push pre (push ps ρ0)))).erasedIHType (mkM P μ)
        (PiRawMotiveAny.guarded (mkM P μ) (σOf vs) (evalTotal (σOf vs) v)
          ((mkM P μ).μ f (((List.range nu).map Level.param).map (evalTotal (σOf vs)))) mo ps fd.indices (push ps ρ0)) x)
        (den (mkM P μ) (σOf vs) (vcons x (push pre (push ps ρ0))) ih) := by
  exact builder_original (mkM P μ) rfl (σOf vs) K f nu
    (RawFamily.endValue C vs (fd.params.length + fd.indices.length))
    (RawFamily.endValue_resp C vs _) fd.resLevel v fd.params fd.indices ps pre hps
    hF mo x hmo htf hE hb fuel inner prior c a T Mx idx hc hpre h hI hMx hx

end Rcic.F3.PSet.PiRawIHAny
