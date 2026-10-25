import rcic.RcicF3DIota

/-!
# F3 D-9: constructors of a group with δ-hidden fields

The family is installed at its normalized data's value, whose fibres are cut
out by the **normalized** field telescopes; a constructor's stored type
carries the **original** fields. `ctorVal_mem_norm` restates `ctorVal_mem`
for a data whose fields agree with the stored type's fields at every fitting
parameter environment (`TelAgree`): the fitting fields fit the normalized
telescope, so the constructor's value lies in the fibre. `ctor_member_sound_norm`
is the member-level wrapper (as `ctor_member_sound`), with the agreement
required only at the constructor's own instances. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- **The constructor's value is an element of its type**, for a data whose
fields `fs'` agree with the stored type's fields `fs` at every fitting parameter
environment (generalizing `ctorVal_mem`, where `fs' = fs`). -/
theorem ctorVal_mem_norm {M : Interp.{4}} (hU : M.U = U W4) (vs : List Nat) (fd : FamData) (j : Nat)
    (cps fs fs' ri : List (Expr Nat)) (hj : fd.ctors[j]? = some (fs', ri))
    (hnp : cps.length = fd.params.length) (hq : ri.length = fd.indices.length)
    (hfam : Equiv (M.μ fd.fref vs) (piLam M (σOf vs) (famEnd M W4 (σOf vs) fd) (fun _ => pempty) (famType fd)))
    (hagree : ∀ ps, TelFits M (σOf vs) cps ρ0 ps → TelAgree M (σOf vs) fs fs' (push ps ρ0))
    (htyp : ∀ zs, TelFits M (σOf vs) (cps ++ fs) ρ0 zs → ∃ v,
      den M (σOf vs) (push zs ρ0) (foldApps (.const fd.fref ((List.range vs.length).map Level.param))
        (policyParameterLocals cps.length fs.length ++ ri)) ∈
        Ed M (den M (σOf vs) (push zs ρ0) (.sort v)))
    (hsmall : evalTotal (σOf vs) fd.resLevel ≠ 0 → ∀ ps xs, TelFits M (σOf vs) cps ρ0 ps →
      TelFits M (σOf vs) fs (push ps ρ0) xs →
      SmallAlong M (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel)) fs (push ps ρ0) xs) :
    piLam M (σOf vs) (ctorEnd M (σOf vs) fd j fs.length) ρ0
        (policyPi (cps ++ fs) (foldApps (.const fd.fref ((List.range vs.length).map Level.param))
          (policyParameterLocals cps.length fs.length ++ ri))) ∈
      Ed M (den M (σOf vs) ρ0 (policyPi (cps ++ fs) (foldApps (.const fd.fref
        ((List.range vs.length).map Level.param)) (policyParameterLocals cps.length fs.length ++ ri)))) := by
  refine piLam_mem M _ (ctorEnd_resp M _ fd j fs.length) _ ρ0 ?_
  refine piGood_policyPi_fits M _ _ _ _ ρ0 fun zs hz => ?_
  refine piGood_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h) _ ?_
  obtain ⟨ps, xs, rfl, hps, hxs⟩ := TelFits_split cps fs ρ0 zs hz
  have hpl : ps.length = cps.length := hps.length
  have hxl : xs.length = fs.length := hxs.length
  have hag := hagree ps hps
  have hxs' : TelFits M (σOf vs) fs' (push ps ρ0) xs := (telFits_iff_of_agree M _ hag xs).mp hxs
  -- the result type's value
  have hR : Equiv (den M (σOf vs) (push (ps ++ xs) ρ0) (foldApps (.const fd.fref
      ((List.range vs.length).map Level.param)) (policyParameterLocals cps.length fs.length ++ ri)))
      (fapps (famVal M W4 (σOf vs) fd) (ps ++ ri.map (den M (σOf vs) (push xs (push ps ρ0))))) := by
    rw [den_foldApps, List.map_append, ← hpl, ← hxl, den_paramLocals]
    show Equiv (fapps (M.μ fd.fref (((List.range vs.length).map Level.param).map (evalTotal (σOf vs)))) _) _
    rw [map_param_σOf, push_append]
    exact fapps_congr hfam _
  obtain ⟨v, hv0⟩ := htyp (ps ++ xs) hz
  have hv : fapps (famVal M W4 (σOf vs) fd) (ps ++ ri.map (den M (σOf vs) (push xs (push ps ρ0)))) ∈
      Ed M (den M (σOf vs) (push (ps ++ xs) ρ0) (.sort v)) := mem_congr_left hR hv0
  refine mem_congr_right (ed_congr M hR).symm ?_
  have hne := ne_of_mem_sort hU hv
  have hisl : (ri.map (den M (σOf vs) (push xs (push ps ρ0)))).length = fd.indices.length := by
    rw [List.length_map, hq]
  have hcf : CtorFits M (σOf vs) fd.ctors (push ps ρ0) (ri.map (den M (σOf vs) (push xs (push ps ρ0))))
      j xs := ⟨(fs', ri), hj, hxs', LEq.refl _⟩
  have hsm' : evalTotal (σOf vs) fd.resLevel ≠ 0 →
      SmallAlong M (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel)) fs' (push ps ρ0) xs := fun h0 =>
    (smallAlong_iff_of_agree M _ _ hag xs hxs).mp (hsmall h0 ps xs hps hxs)
  generalize ri.map (den M (σOf vs) (push xs (push ps ρ0))) = is at hv hne hisl hcf ⊢
  have hfit : TelFits M (σOf vs) (fd.params ++ fd.indices) ρ0 (ps ++ is) :=
    fits_of_fapps_ne M (σOf vs) (famEnd_resp M W4 (σOf vs) fd) (.sort fd.resLevel)
      (fd.params ++ fd.indices) ρ0 (ps ++ is)
      (by rw [List.length_append, List.length_append, hisl, hpl, hnp]) hne
  have he := fapps_piLam M (σOf vs) (famEnd_resp M W4 (σOf vs) fd) (.sort fd.resLevel)
    (fd.params ++ fd.indices) ρ0 (ps ++ is) hfit
  refine mem_congr_right (ed_congr M he).symm ?_
  have hshift : shiftρ fd.indices.length (push (ps ++ is) ρ0) = push ps ρ0 := by
    rw [push_append, ← hisl, shiftρ_push]
  have hlast : lastVals fd.indices.length (push (ps ++ is) ρ0) = is := by
    rw [push_append, ← hisl, lastVals_push]
  show ctorEnd M (σOf vs) fd j fs.length (push (ps ++ xs) ρ0) ∈
    Ed M (famEnd M W4 (σOf vs) fd (push (ps ++ is) ρ0))
  unfold ctorEnd famEnd cond
  rw [hshift, hlast]
  cases hd : M.dec (evalTotal (σOf vs) fd.resLevel = 0) with
  | isTrue h0 =>
      refine mem_congr_right (ed_tyv M (dich_tv _)).symm ?_
      exact mem_tv.mpr ⟨⟨j, xs, hcf⟩, Equiv.rfl⟩
  | isFalse h0 =>
      refine mem_congr_right (ed_tyv M (TypeFib_dich M W4 _ _ _ _ _)).symm ?_
      have hlx : lastVals fs.length (push (ps ++ xs) ρ0) = xs := by
        rw [push_append, ← hxl, lastVals_push]
      rw [hlx]
      have ht := mem_FitSetT M W4 _ _ fs' (push ps ρ0) xs hxs' (hsm' h0)
      have hb := mem_BoundT M W4 _ (σOf vs) (push ps ρ0) 0 fd.ctors j (fs', ri) hj ht
      rw [Nat.zero_add] at hb
      obtain ⟨i, hi⟩ := hb
      exact mem_sep.mpr ⟨i, ⟨j, xs, hcf, hi⟩, hi⟩

/-- A constructor member is sound, for a data whose fields agree with the stored
type's at the constructor's instances (as `ctor_member_sound`). -/
theorem ctor_member_sound_norm (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {c : Nat}
    {cm : CheckedMember} (fd : FamData) (j : Nat) (cps fs fs' ri : List (Expr Nat))
    (hj : fd.ctors[j]? = some (fs', ri)) (hnp : cps.length = fd.params.length) (hq : ri.length = fd.indices.length)
    (hst : cm.mtype = policyPi (cps ++ fs) (foldApps (.const fd.fref ((List.range cm.arity).map Level.param))
      (policyParameterLocals cps.length fs.length ++ ri)))
    (hcl : ∀ k, Rcic.Declarative.lift k 1 cm.mtype = cm.mtype)
    (hlvl : exprLevelsBounded cm.arity cm.mtype = true) (hbody : cm.body = none)
    (hnf : nfOf fd j = fs.length)
    (hF : ∀ vs, Equiv (μ c vs)
      (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) fd j (nfOf fd j)) ρ0 cm.mtype))
    (hfam : ∀ vs, vs.length = cm.arity → Equiv (μ fd.fref vs)
      (piLam (mkM P μ) (σOf vs) (famEnd (mkM P μ) W4 (σOf vs) fd) (fun _ => pempty) (famType fd)))
    (hagree : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) → ∀ ps,
      TelFits (mkM P μ) (σOf vs) cps ρ0 ps → TelAgree (mkM P μ) (σOf vs) fs fs' (push ps ρ0))
    (htyp : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) →
      ∀ zs, TelFits (mkM P μ) (σOf vs) (cps ++ fs) ρ0 zs → ∃ v,
      den (mkM P μ) (σOf vs) (push zs ρ0) (foldApps (.const fd.fref ((List.range vs.length).map Level.param))
        (policyParameterLocals cps.length fs.length ++ ri)) ∈
        Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push zs ρ0) (.sort v)))
    (hsmall : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) →
      evalTotal (σOf vs) fd.resLevel ≠ 0 → ∀ ps xs, TelFits (mkM P μ) (σOf vs) cps ρ0 ps →
      TelFits (mkM P μ) (σOf vs) fs (push ps ρ0) xs →
      SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel)) fs (push ps ρ0) xs) :
    MemberSound P μ K c cm := by
  intro σ ls ρ hlen hl
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  have hvl : (ls.map (evalTotal σ)).length = cm.arity := by rw [List.length_map, hlen]
  have hbd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K c := by
    intro v hv
    obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hv
    exact hl l hl'
  rw [den_inst_canon (mkM P μ) σ ls ρ cm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (hF _).symm ?_
  rw [hnf, hst]
  have hst' : (List.range cm.arity).map Level.param = (List.range (ls.map (evalTotal σ)).length).map Level.param := by
    rw [hvl]
  rw [hst']
  exact ctorVal_mem_norm rfl (ls.map (evalTotal σ)) fd j cps fs fs' ri hj hnp hq (hfam _ hvl) (hagree _ hvl hbd)
    (htyp _ hvl hbd) (hsmall _ hvl hbd)

end PSet

end Rcic.F3
