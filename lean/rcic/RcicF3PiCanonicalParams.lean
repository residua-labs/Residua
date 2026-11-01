import rcic.RcicF3PiGroupSyntax
import rcic.RcicF3PiRawCtor
/-! Canonical family parameters recovered from bounded raw result typehood.
Constructor parameter mirrors may contain the family constant. The signature
uses the family's clean parameter domains, while the abstraction retains its
original stored constructor type. Ordinary soundness and body regularity are
retained; universal raw group assembly remains open. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiCanonicalParams
open Rcic.Declarative PiValueRule

/-- An actual raw tuple supplies fitting complete family arguments, without
bounded mirror conversion or raw own-parameter freeness assumptions. -/
theorem result_fits (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (φ : List Nat → PiIndex.Index.{4} → Prop)
    (famDs Ps As ix : List (Expr Nat)) (vs : List Nat)
    (har : Ps.length + ix.length = famDs.length)
    (K : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hE : EnvSound (mkM P (upd μ f (PiValue.table P μ φ famDs))) (σOf vs) K E n)
    {u : Level}
    (d : HasTyT E n [] (policyPi (Ps ++ As)
      (foldApps (.const f ((List.range vs.length).map Level.param))
        (policyParameterLocals Ps.length As.length ++ ix))) (.sort u))
    (hd : LOKt (σOf vs) 4 K d)
    (ps xs : List PSet.{4}) (hps : ps.length = Ps.length) (hxs : xs.length = As.length)
    (ht : TelFits (mkM P (upd μ f (PiValue.table P μ φ famDs)))
      (σOf vs) (Ps ++ As) ρ0 (ps ++ xs)) :
    TelFits (mkM P μ) (σOf vs) famDs ρ0
      (ps ++ ix.map (den (mkM P (upd μ f (PiValue.table P μ φ famDs)))
        (σOf vs) (push (ps ++ xs) ρ0))) := by
  let X := PiValue.table P μ φ famDs
  let M := mkM P (upd μ f X)
  let ys := ps ++ ix.map (den M (σOf vs) (push (ps ++ xs) ρ0))
  have hs := hsound_ty (P.good M rfl) hE d hd
  obtain ⟨v, hv⟩ := tel_end_type _ (Ps ++ As) d hs ρ0 (ps ++ xs) True.intro ht
  have he : den M (σOf vs) (push (ps ++ xs) ρ0)
      (foldApps (.const f ((List.range vs.length).map Level.param))
        (policyParameterLocals Ps.length As.length ++ ix)) = fapps (X vs) ys := by
    rw [den_foldApps]
    change fapps ((upd μ f X) f
      (((List.range vs.length).map Level.param).map (evalTotal (σOf vs))))
      ((policyParameterLocals Ps.length As.length ++ ix).map
        (den M (σOf vs) (push (ps ++ xs) ρ0))) = _
    rw [upd_eq, map_param_σOf, List.map_append, ← hps, ← hxs, den_paramLocals]
  have hn : ¬ Equiv (fapps (X vs) ys) pempty := by
    rw [← he]
    exact ne_of_mem_sort rfl hv
  have hy : ys.length = famDs.length := by
    simp only [ys, List.length_append, List.length_map, hps, har]
  exact fits_of_fapps_ne (mkM P μ) (σOf vs)
    (PiValue.endValue_resp (φ vs) famDs.length) (.sort .zero) famDs ρ0 ys hy hn

/-- Elementary telescope splitting at the known argument boundary. -/
theorem fits_append_exact (M : Interp.{4}) (σ : Nat → Nat)
    (Ds Ds' : List (Expr Nat)) (ρ : Nat → PSet.{4}) (xs ys : List PSet.{4})
    (hl : xs.length = Ds.length) (hf : TelFits M σ (Ds ++ Ds') ρ (xs ++ ys)) :
    TelFits M σ Ds ρ xs ∧ TelFits M σ Ds' (push xs ρ) ys := by
  obtain ⟨xs', ys', he, hx, hy⟩ := TelFits_split Ds Ds' ρ (xs ++ ys) hf
  obtain ⟨h1, h2⟩ := List.append_inj he (hl.trans hx.length.symm)
  cases h1
  cases h2
  exact ⟨hx, hy⟩

/-- Forward transport from an original raw constructor tuple to the canonical
family-parameter prefix and normalized fields. This is not a reverse iff. -/
theorem canonical_tuple (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (φ : List Nat → PiIndex.Index.{4} → Prop)
    (famPs Is Ps As ix : List (Expr Nat)) (vs : List Nat)
    (hparam : Ps.length = famPs.length) (hindex : ix.length = Is.length)
    (hfree : ∀ A ∈ famPs, occursConst f A = false)
    (K : Nat → Nat) {E : ResolvedEnv} {n fuel : Nat} {fs : List FieldSpec}
    (hE : EnvSound (mkM P (upd μ f (PiValue.table P μ φ (famPs ++ Is))))
      (σOf vs) K E n)
    (hb : BodiesOK E (σOf vs) K)
    (hR : PiHereditary.BodiesRegular
      (mkM P (upd μ f (PiValue.table P μ φ (famPs ++ Is)))) (σOf vs) K E)
    (hv : PiValueExtract.Views E fuel f vs.length (famPs ++ Is).length As fs)
    {u : Level}
    (d : HasTyT E n [] (policyPi (Ps ++ As)
      (foldApps (.const f ((List.range vs.length).map Level.param))
        (policyParameterLocals Ps.length As.length ++ ix))) (.sort u))
    (hd : LOKt (σOf vs) 4 K d) (zs : List PSet.{4})
    (ht : TelFits (mkM P (upd μ f (PiValue.table P μ φ (famPs ++ Is))))
      (σOf vs) (Ps ++ As) ρ0 zs) :
    TelFits (mkM P (upd μ f (PiValue.table P μ φ (famPs ++ Is)))) (σOf vs)
      (famPs ++ fs.map (fieldExpr f ((List.range vs.length).map Level.param))) ρ0 zs := by
  let X := PiValue.table P μ φ (famPs ++ Is)
  let M := mkM P (upd μ f X)
  obtain ⟨ps, xs, rfl, hp, hx⟩ := TelFits_split Ps As ρ0 zs ht
  have hall := result_fits P μ f φ (famPs ++ Is) Ps As ix vs
    (by simp only [List.length_append, hparam, hindex]) K hE d hd
    ps xs hp.length hx.length ht
  have hbase := (fits_append_exact (mkM P μ) (σOf vs) famPs Is ρ0 ps
    (ix.map (den M (σOf vs) (push (ps ++ xs) ρ0)))
    (hp.length.trans hparam) hall).1
  have hagree : AgreeOn μ (upd μ f X) (fun r => r ≠ f) :=
    fun r hr ls => (upd_ne μ f X hr ls).symm
  have hrefs : RefsIn (fun r => r ≠ f) famPs := by
    intro A hA r hr hrf
    cases hrf
    have h := (PiIndependent.expr_refs f A).mp hr
    rw [hfree A hA] at h
    cases h
  have hcanon := (TelFits_agreeOn P hagree (σOf vs) famPs hrefs ρ0 ps).mp hbase
  have hnorm := (PiGroupSyntax.prefix_fits_iff P (upd μ f X) (σOf vs) K
    hE hb hR hv Ps d hd ρ0 (ps ++ xs) True.intro).mpr ht
  have hfields := (fits_append_exact M (σOf vs) Ps
    (fs.map (fieldExpr f ((List.range vs.length).map Level.param))) ρ0 ps xs
    hp.length hnorm).2
  exact hcanon.append hfields

/-- The actual raw constructor abstraction inhabits its original full type.
Its own parameter syntax is unrestricted; the clean family prefix is used
only in the candidate-independent constructor signature. -/
theorem constructor_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (famPs Is : List (Expr Nat)) (cs : List Constructor) (vs : List Nat)
    (c : Fin cs.length) {E : ResolvedEnv} {n fuel : Nat}
    (Ps As ix : List (Expr Nat)) (fs : List FieldSpec)
    (hparam : Ps.length = famPs.length) (hindex : ix.length = Is.length)
    (hfree : ∀ A ∈ famPs, occursConst f A = false)
    (hv : PiValueExtract.Views E fuel f vs.length (famPs ++ Is).length As fs)
    (hc : (cs[c]).fields = famPs.map FieldSpec.plain ++ fs)
    (hr : (cs[c]).result = policyParameterLocals Ps.length As.length ++ ix)
    (hresult : ∀ a ∈ policyParameterLocals Ps.length As.length ++ ix, occursConst f a = false)
    (K : Nat → Nat)
    (hE : EnvSound (mkM P (upd μ f (PiValue.table P μ
      (predicate P μ (famPs ++ Is) cs) (famPs ++ Is)))) (σOf vs) K E n)
    (hb : BodiesOK E (σOf vs) K)
    (hR : PiHereditary.BodiesRegular (mkM P (upd μ f (PiValue.table P μ
      (predicate P μ (famPs ++ Is) cs) (famPs ++ Is)))) (σOf vs) K E)
    {u : Level}
    (d : HasTyT E n [] (policyPi (Ps ++ As)
      (foldApps (.const f ((List.range vs.length).map Level.param))
        (policyParameterLocals Ps.length As.length ++ ix))) (.sort u))
    (hd : LOKt (σOf vs) 4 K d) :
    let M := mkM P (upd μ f (PiValue.table P μ (predicate P μ (famPs ++ Is) cs) (famPs ++ Is)))
    let T := policyPi (Ps ++ As)
      (foldApps (.const f ((List.range vs.length).map Level.param))
        (policyParameterLocals Ps.length As.length ++ ix))
    piLam M (σOf vs) (fun _ => pempty) ρ0 T ∈ Ed M (den M (σOf vs) ρ0 T) := by
  dsimp only
  let φ := predicate P μ (famPs ++ Is) cs
  let X := PiValue.table P μ φ (famPs ++ Is)
  let M := mkM P (upd μ f X)
  have hclean := (PiRawCtor.prefix_views famPs hfree hv).clean
  rw [← hc] at hclean
  have hs := hsound_ty (P.good M rfl) hE d hd
  refine piLam_mem M (σOf vs) (envResp_const pempty) _ ρ0 ?_
  refine piGood_policyPi_fits M (σOf vs) (fun _ => pempty) _ (Ps ++ As) ρ0 ?_
  intro zs hz
  refine piGood_foldApps M (σOf vs) (fun _ => pempty) _
    (.const f ((List.range vs.length).map Level.param))
    (fun _ _ h => Expr.noConfusion h) (policyParameterLocals Ps.length As.length ++ ix) ?_
  have hcanon := canonical_tuple P μ f φ famPs Is Ps As ix vs hparam hindex hfree
    K hE hb hR hv d hd zs hz
  have htuple : TelFits M (σOf vs)
      ((cs[c]).fields.map (fieldExpr f ((List.range vs.length).map Level.param))) ρ0 zs := by
    rw [hc]
    simpa only [List.map_append, List.map_map, Function.comp_def, fieldExpr, List.map_id'] using hcanon
  have hp := close_tuple P μ f (famPs ++ Is) cs vs c hclean zs htuple
  rw [hr] at hp
  obtain ⟨v, hv⟩ := tel_end_type _ (Ps ++ As) d hs ρ0 zs True.intro hz
  let ys := PiIndependent.leafArgs P μ (σOf vs)
    (policyParameterLocals Ps.length As.length ++ ix) (push zs ρ0)
  have he := PiIndependent.leaf_read P μ f X (σOf vs)
    ((List.range vs.length).map Level.param) _ hresult (push zs ρ0)
  rw [map_param_σOf] at he
  have hn : ¬ Equiv (fapps (X vs) ys) pempty := by
    rw [← he]
    exact ne_of_mem_sort rfl hv
  have hy : ys.length = (famPs ++ Is).length := by
    simp only [ys, PiIndependent.leafArgs, List.length_map, List.length_append,
      policyParameterLocals_length, hparam, hindex]
  have hfit := fits_of_fapps_ne (mkM P μ) (σOf vs)
    (PiValue.endValue_resp (φ vs) (famPs ++ Is).length) (.sort .zero)
    (famPs ++ Is) ρ0 ys hy hn
  rw [he]
  exact (PiValue.apply_mem_iff (mkM P μ) (σOf vs) (φ vs)
    (famPs ++ Is) ρ0 ys hy pempty).mpr ⟨hfit, hp, Equiv.rfl⟩

end Rcic.F3.PSet.PiCanonicalParams
