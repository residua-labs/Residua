import rcic.RcicRouteCIndexFamilyFragment

/-!
# The complete carrier PER of the new family clause

The non-index proof is composed from the landed `ctorPerA_of`, using the
retained `LRTyA` and `LREqA` obligations. The index proof uses typed conversion
only. Thus the PER below is supplied for every new family certificate, including
constructor-bearing signatures, without assuming its conclusion as a premise.
The mutual type-equality tower, general fundamental theorem and rows remain open.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.RouteCIndex

open Rcic.Declarative

/-- Every carrier validated by the modified family clause is a PER. Plain and
inner constructor fields use the landed semantic PER/transport theorems; indices
use only the new declared typed-conversion calculus. -/
theorem indexFamTyA_per {E : ResolvedEnvA} {I : IotaIfaceA} {n k : Nat} {ρ₀ : Nat → Nat}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (hEN : EnvNormCtorTypeA E) (h : IndexFamTyA E I n ρ₀ k Γ A R) : PerMotA R := by
  cases h with
  | @fam r ls ps is m u u₀ hA hn hnp hm hind hsh hps hu hz Rs RsI
      hFld hFldeq hFldRec hFldFeq hxsD hFldI hFldIeq hFldIRec hFldIdom =>
    rw [LRTyA_eq] at hFld hFldI
    rw [LREqA_eq] at hFldeq hFldIeq
    have HS := lowEqSymmA_all (I := I) (n := n) (ρ₀ := ρ₀) hEN k
    have HT := lowEqTransA_all (I := I) (n := n) (ρ₀ := ρ₀) hEN k
    have hP : FiberPerWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI ps ls := by
      intro ρ hρ
      refine ⟨indexRelsA_per hsh (hFldFeq ρ hρ), ?_⟩
      have hpsρ : (ps.map (wkExprA ρ)).length = m.nparamsA := by
        rw [List.length_map]
        exact hps
      have hFld := hFld ρ hρ
      have hFldeq := hFldeq ρ hρ
      have hFldRec := hFldRec ρ hρ
      have hFldI := hFldI ρ hρ
      have hFldIeq := hFldIeq ρ hρ
      have hFldIRec := hFldIRec ρ hρ
      have hFldIdom := hFldIdom ρ hρ
      exact
        ctorPerA_of hEN hpsρ hFld
            (fun c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
              tyKA_per hEN HS HT (hFld c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10))
            (fun c cm lsA lsC lsC' kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' h1 h2 h3 h4 h5 h6 h7 h8 h9
                h10 h11 h12 h13 _ _ tD tD' =>
              eqKA_transport hEN HS HT (hFldeq c cm lsA lsC lsC' kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC'
                h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13) tD tD')
            hFldRec hFldI
            (fun c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ρ' hρ' zs zs' D₁ u₁
                C₁ v₁ hz hD₁ =>
              tyKA_per hEN HS HT (hFldI c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ρ'
                hρ' zs zs' D₁ u₁ C₁ v₁ hz hD₁))
            (fun c cm lsA lsC lsC' kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' h1 h2 h3 h4 h5 h6 h7 h8 h9
                h10 h11 h12 h13 ρ' hρ' zs zs' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' hz hD₁ hD₁' _ _ tD tD' =>
              eqKA_transport hEN HS HT (hFldIeq c cm lsA lsC lsC' kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC'
                h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 ρ' hρ' zs zs' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' hz hD₁ hD₁') tD tD')
            hFldIRec hFldIdom
    have hAp : carrierParamsA m (foldAppsA (.const r ls) (ps ++ is)) = ps.map (wkExprA []) := by
      rw [map_wkExprA_nil]
      exact carrierParamsA_famApp hps ls
    have hAl : eqNList ls (carrierLevelsA (foldAppsA (.const r ls) (ps ++ is))) := by
      rw [carrierLevelsA_foldAppsA]
      exact eqNListA_refl ls
    exact ⟨fun _ _ hab => lfpWA_symm hP hps (wkOk₀A_nil E I n Γ) hAp hAl hab,
      fun _ _ _ hab hbc => lfpWA_trans hP hps (wkOk₀A_nil E I n Γ) hAp hAl hab hbc⟩

#print axioms indexFamTyA_per

end Rcic.Declarative.Ann.RouteCIndex
