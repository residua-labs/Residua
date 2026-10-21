import rcic.RcicRouteCIndexSyntactic

/-!
# General transport for the syntactic-index operator

The typed-domain equality datum is the weakened `hFldFeq` of the new family
clause. It supplies the complete index-walk PER using rigidity of the declared
telescope. The landed carrier transport then applies to every constructor
signature, with its semantic field interpretation unchanged. No index domain
is interpreted by a logical relation at any height.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.RouteCIndex

open Rcic.Declarative

/-- The exact height-free replacement for index-domain semantic equality. -/
def IndexDomainsConvertA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA)
    (m : CheckedMemberA) (ps : List ExprA) (ls₀ : List Level) : Prop :=
  ∀ (lsF lsF' : List Level) (TF TF' : ExprA) (pre pre' : List ExprA)
    (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
    (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
    eqNListB n ls₀ lsF → eqNListB n lsF lsF' →
    applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
    applyTelA ps (instantiateLevelsA lsF' m.mtypeA) = some TF' →
    ArgsRelPA (IndexRelsA E I n Γ m [] lsF) m.nparamsA ps TF pre pre' →
    applyTelA pre TF = some (.pi D uD C vC) →
    applyTelA pre' TF' = some (.pi D' uD' C' vC') →
    Nonempty (TyConvA E I n Γ D D')

/-- General index-walk PER: only typed domain conversion and declared-telescope
rigidity are consumed. This supplies the premise of landed carrier transport. -/
theorem indexRelsA_per {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {m : CheckedMemberA} {ps : List ExprA} {ls₀ : List Level} {u₀ : Level}
    (hsh : piBodyA m.mtypeA = .sort u₀)
    (hdom : IndexDomainsConvertA E I n Γ m ps ls₀) :
    IdxPerA n (IndexRelsA E I n Γ m []) m ps ls₀ := by
  intro lsF lsF' TF TF' hl₀ hll hTF hTF'
  constructor
  · intro pre pre' D u C v hw _ hD
    obtain ⟨D', u', C', v', hD'⟩ :=
      applyTelA_pi_cross (Or.inl ⟨u₀, hsh⟩) rfl hTF hTF' (argsRelPA_length hw) hD
    have hfull : applyTelA (ps ++ pre) (instantiateLevelsA lsF m.mtypeA) = some (.pi D u C v) := by
      rw [applyTelA_append, hTF]
      exact hD
    have hfull' : applyTelA (ps ++ pre') (instantiateLevelsA lsF' m.mtypeA) = some (.pi D' u' C' v') := by
      rw [applyTelA_append, hTF']
      exact hD'
    have hd := hdom lsF lsF' TF TF' pre pre' D u C v D' u' C' v' hl₀ hll hTF hTF' hw hD hD'
    exact ⟨D', u', C', v', hD', fun f f' h =>
      declaredIndexRelA_transport hfull hfull' hd (declaredIndexRelA_symm h)⟩
  · intro p₁ p₂ p₃ D u C v h₁₂ _ _ hD
    obtain ⟨D', u', C', v', hD'⟩ :=
      applyTelA_pi_cross (Or.inl ⟨u₀, hsh⟩) rfl hTF hTF' (argsRelPA_length h₁₂) hD
    have hfull : applyTelA (ps ++ p₁) (instantiateLevelsA lsF m.mtypeA) = some (.pi D u C v) := by
      rw [applyTelA_append, hTF]
      exact hD
    have hfull' : applyTelA (ps ++ p₂) (instantiateLevelsA lsF' m.mtypeA) = some (.pi D' u' C' v') := by
      rw [applyTelA_append, hTF']
      exact hD'
    have hd := hdom lsF lsF' TF TF' p₁ p₂ D u C v D' u' C' v' hl₀ hll hTF hTF' h₁₂ hD hD'
    exact ⟨D', u', C', v', hD', fun f₁ f₂ f₃ h₁ h₂ =>
      declaredIndexRelA_trans h₁
        (declaredIndexRelA_transport hfull' hfull (tyConvA_symm_ne hd) h₂)⟩

/-- Constructor signatures are unrestricted here: the carrier moves along
typed syntactic indices, retaining the original semantic field walk literally. -/
theorem indexFamRelA_carrier {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {ρ : WkSpecA} {ps : List ExprA} {ls₀ ls ls' : List Level}
    {is is' : List ExprA} {TF TF' a b : ExprA} {u₀ : Level}
    (hsh : piBodyA m.mtypeA = .sort u₀)
    (hdom : IndexDomainsConvertA E I n (wkCtxA ρ Γ) m ps ls₀)
    (hps : ps.length = m.nparamsA) (hl₀ : eqNList ls₀ ls) (hls : eqNListB n ls ls')
    (hTF : applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF)
    (hTF' : applyTelA ps (instantiateLevelsA ls' m.mtypeA) = some TF')
    (hw : IndexWalkA E I n (wkCtxA ρ Γ) TF TF' is is')
    (hc : Nonempty (TyConvA E I n (wkCtxA ρ Γ)
      (foldAppsA (.const r ls) (ps ++ is)) (foldAppsA (.const r ls') (ps ++ is'))))
    (h : IndexFamRelA E I n Γ r m Rs RsI ρ (foldAppsA (.const r ls) (ps ++ is)) a b) :
    IndexFamRelA E I n Γ r m Rs RsI ρ (foldAppsA (.const r ls') (ps ++ is')) a b := by
  have hI : IdxPerA n (IndexRelsA E I n Γ m ρ) m ps ls₀ := indexRelsA_per hsh hdom
  have hw' : ArgsRelPA (IndexRelsA E I n Γ m ρ ls) m.nparamsA ps TF is is' :=
    convArgsA_declaredIndex (parConvA_convArgsA hw) m.nparamsA ps hTF
  exact lfpWA_carrier hI hps hl₀ hls hTF hTF' hw' hc h

-- BEGIN RCIC_ROUTE_C_INDEX_TRANSPORT_ROOTS
#print axioms IndexDomainsConvertA
#print axioms indexRelsA_per
#print axioms indexFamRelA_carrier
-- END RCIC_ROUTE_C_INDEX_TRANSPORT_ROOTS

end Rcic.Declarative.Ann.RouteCIndex
