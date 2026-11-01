import rcic.RcicF3PiRawParams
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawRename
open Rcic.Declarative
/-- Successful arbitrary-depth telescope readback survives insertion of binders.
This success-form reader lemma follows the existing private commutation proof in
RcicIARecIH; it exposes the result needed by the admitted raw recursor bridge. -/
theorem read_lift (E : ResolvedEnv) (hcl : EnvClosed E) :
    (fuel : Nat) → {T b : Expr Nat} → {ds : List (Expr Nat)} →
    piTelescopeFuel E fuel T = some (ds, b) → (c a : Nat) →
    piTelescopeFuel E fuel (Rcic.Declarative.lift c a T) =
      some (liftFields a ds c,
        Rcic.Declarative.lift (c + ds.length) a b) := by
  intro fuel
  induction fuel with
  | zero =>
      intro T b ds h
      simp only [piTelescopeFuel] at h
      cases h
  | succ fuel ih =>
      intro T b ds h c a
      simp only [piTelescopeFuel] at h ⊢
      rw [whnfFuel_lift E hcl c a fuel T]
      cases hw : whnfFuel E fuel T with
      | none => rw [hw] at h; cases h
      | some w =>
          rw [hw] at h
          simp only [Option.map_some']
          cases w with
          | pi A B =>
              dsimp only at h
              simp only [Rcic.Declarative.lift]
              cases hp : piTelescopeFuel E fuel B with
              | none => rw [hp] at h; cases h
              | some p =>
                  obtain ⟨doms, body⟩ := p
                  rw [hp] at h
                  have hd := (Prod.mk.inj (Option.some.inj h)).1
                  have hb := (Prod.mk.inj (Option.some.inj h)).2
                  subst ds; subst b
                  rw [ih hp (c + 1) a]
                  simp only [liftFields, List.length_cons]
                  rw [show c + 1 + doms.length = c + (doms.length + 1) by omega]
          | bvar i =>
              have hd := (Prod.mk.inj (Option.some.inj h)).1
              have hb := (Prod.mk.inj (Option.some.inj h)).2
              subst ds; subst b
              by_cases hc : c ≤ i <;>
                simp only [Rcic.Declarative.lift, hc, liftFields, List.length_nil, Nat.add_zero, ↓reduceIte]
          | sort l | const r ls | app f x | lam A B | letE A v B | lit t =>
              have hd := (Prod.mk.inj (Option.some.inj h)).1
              have hb := (Prod.mk.inj (Option.some.inj h)).2
              subst ds; subst b
              simp only [Rcic.Declarative.lift, liftFields, List.length_nil, Nat.add_zero]
/-- Original admission transports its complete parameter/index readback through
an arbitrary block inserted among preceding locals. It retains the entire
recursive telescope and the original normalization fuel. -/
theorem admitted_lift (M : Interp.{4}) (σ : Nat → Nat)
    (ps : List PSet.{4}) (ρ : Nat → PSet.{4})
    {E : ResolvedEnv} (hcl : EnvClosed E)
    {fuel f nu ni prior inner c a : Nat} {T : Expr Nat} {idx : List (Expr Nat)}
    (hc : c ≤ prior)
    (h : fieldAnalyze E fuel f nu ps.length ni (ps.length + prior) T =
      .permitted (.recursive inner) idx) :
    ∃ ds args, ds.length = inner ∧ args.length = ps.length + ni ∧
      piTelescopeFuel E (fuel - 1) (Rcic.Declarative.lift c a T) =
        some (liftFields a ds c, foldApps
          (.const f ((List.range nu).map Level.param)) args) ∧
      ∀ pre xs, pre.length = prior + a → xs.length = ds.length →
        (args.take ps.length).map
          (den M σ (push xs (push pre (push ps ρ)))) = ps := by
  obtain ⟨ds, b, hr, hl, _, _, hp⟩ := PiIndependent.recursive_scans h
  obtain ⟨ix, hb, hi, _⟩ := properFamilyFuel_shape (by omega) hp
  rw [show ds.length + (ps.length + prior) =
    ps.length + (prior + ds.length) by omega, paramLocals_top] at hb
  have ht := read_lift E hcl (fuel - 1) hr c a
  rw [hb, foldApps_lift, Rcic.Declarative.lift, List.map_append,
    policyParameterLocals_lift_le ps.length (prior + ds.length)
      (c + ds.length) a (by omega)] at ht
  let args := policyParameterLocals ps.length (prior + ds.length + a) ++
    ix.map (Rcic.Declarative.lift (c + ds.length) a)
  refine ⟨ds, args, hl, ?_, ht, ?_⟩
  · simp only [args, List.length_append, policyParameterLocals_length, List.length_map, hi]
  · intro pre xs hpre hxs
    change ((policyParameterLocals ps.length (prior + ds.length + a) ++
      ix.map (Rcic.Declarative.lift (c + ds.length) a)).take ps.length).map _ = ps
    rw [show prior + ds.length + a = pre.length + xs.length by omega]
    exact PiRawParams.param_prefix M σ ps pre xs ρ _
/-- Readback from the original admitted field, after preceding binder insertion
and the actual field binder inserted by funIHType. Ordinary environment
stored type facts supply closed bodies; no re-admission of shifted syntax or
semantic parameter equation is assumed. -/
theorem admitted_ih_read (M : Interp.{4}) (σ : Nat → Nat)
    (ps pre : List PSet.{4}) (ρ : Nat → PSet.{4}) (x : PSet.{4})
    {E : ResolvedEnv} (htf : TypeFacts E)
    {fuel f nu ni prior inner c a : Nat} {T : Expr Nat} {idx : List (Expr Nat)}
    (hc : c ≤ prior) (hpre : pre.length = prior + a)
    (h : fieldAnalyze E fuel f nu ps.length ni (ps.length + prior) T =
      .permitted (.recursive inner) idx) :
    ∃ ds args, ds.length = inner ∧ args.length = ps.length + ni ∧
      piTelescopeFuel E (fuel - 1)
        (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift c a T)) =
        some (ds, foldApps (.const f ((List.range nu).map Level.param)) args) ∧
      ∀ xs, xs.length = ds.length →
        (args.take ps.length).map
          (den M σ (push xs (vcons x (push pre (push ps ρ))))) = ps := by
  have hcl : EnvClosed E := fun r m hm =>
    ⟨(htf r m hm).1, fun b hb => ((htf r m hm).2.2 b hb).1⟩
  obtain ⟨ds, args, hl, ha, hr, hp⟩ := admitted_lift M σ ps ρ hcl hc h
  let ds' := liftFields a ds c
  have hl' : ds'.length = ds.length := liftFields_length' a ds c
  have hr' := read_lift E hcl (fuel - 1) hr 0 1
  rw [foldApps_lift, Rcic.Declarative.lift] at hr'
  simp only [Nat.zero_add] at hr'
  refine ⟨liftFields 1 ds' 0, args.map (Rcic.Declarative.lift ds'.length 1),
    ?_, ?_, hr', ?_⟩
  · rw [liftFields_length', hl']; exact hl
  · rw [List.length_map]; exact ha
  · intro xs hxs
    rw [liftFields_length'] at hxs
    rw [← List.map_take, List.map_map]
    have hf : (den M σ (push xs (vcons x (push pre (push ps ρ)))) ∘
        Rcic.Declarative.lift ds'.length 1) =
        den M σ (push xs (push pre (push ps ρ))) := by
      funext e
      change den M σ (push xs (push [x] (push pre (push ps ρ))))
        (Rcic.Declarative.lift ds'.length [x].length e) = _
      rw [← hxs]
      exact den_lift_push M σ xs [x] _ e
    rw [hf]
    exact hp pre xs hpre (hxs.trans hl')

/-- Original admission, ordinary environment facts and actual field membership
produce the executable IH type after binder insertion. The semantic prefix
and admission of the shifted field are conclusions of readback, not premises. -/
theorem builder_original (M : Interp.{4}) (hU : M.U = U W4)
    (σ K : Nat → Nat) (f nu : Nat) (φ : PiIndex.Index.{4} → Prop)
    (Ps Is : List (Expr Nat)) (ps pre : List PSet.{4}) (hps : ps.length = Ps.length)
    (hF : Equiv (M.μ f (((List.range nu).map Level.param).map (evalTotal σ)))
      (PiValue.value M σ φ (Ps ++ Is) ρ0))
    (mo x : PSet.{4})
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ((List.range nu).map Level.param))
        (policyLocals (Ps.length + Is.length))) (.sort .zero)))))
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
        (PiRawMotive.guarded M σ
          (M.μ f (((List.range nu).map Level.param).map (evalTotal σ))) mo ps Is (push ps ρ0)) x)
        (den M σ (vcons x (push pre (push ps ρ0))) ih) := by
  have h' : fieldAnalyze E fuel f nu ps.length Is.length (ps.length + prior) T =
      .permitted (.recursive inner) idx := by simpa only [hps] using h
  obtain ⟨ds, args, hl, ha, hr, hp⟩ := admitted_ih_read M σ ps pre ρ0 x htf hc hpre h'
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
  · exact PiRawIH.builder_spec M hU σ f _ φ Ps Is ps hps hF mo hmo E (fuel - 1)
      A ds args ha' ρ (fun xs hxs => by rw [← hps]; exact hp xs hxs.length)
      Mx hMx hr ih hih hx' 
end Rcic.F3.PSet.PiRawRename
