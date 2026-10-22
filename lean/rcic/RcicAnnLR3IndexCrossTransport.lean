import rcic.RcicRouteCIndexTransport

/-!
# Canonical syntactic indices across parameter prefixes

The LR3 equality clause retains `hXFeq`: typed conversion of reached index
domains when the family's parameter prefix changes. The canonical index
relation can therefore be transported directly, without a semantic index
relation or an induction hypothesis at the index domain's height.

This module supplies the equality of canonical position relations and both
directions of whole-index-walk transport. The right telescope shapes are
reconstructed from the stored sort body and equal parameter lengths. It
also transports the complete index-domain PER datum to the new parameters.
Constructor fields and inner function fields are not changed.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative RouteCIndex

/-- The fixed-world, fixed-level content of the new family clause's
`hXFeq`. Only the left walk is required. -/
def IndexCrossDomainsA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (Γ : LCtxA) (m : CheckedMemberA) (ps ps' : List ExprA) (ls : List Level) : Prop :=
  ∀ (TF TF' : ExprA) (pre pre' : List ExprA)
    (D : ExprA) (u : Level) (C : ExprA) (v : Level)
    (D' : ExprA) (u' : Level) (C' : ExprA) (v' : Level),
    applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF →
    applyTelA ps' (instantiateLevelsA ls m.mtypeA) = some TF' →
    ArgsRelPA (IndexRelsA E I n Γ m [] ls) m.nparamsA ps TF pre pre' →
    applyTelA pre TF = some (.pi D u C v) →
    applyTelA pre TF' = some (.pi D' u' C' v') →
    Nonempty (TyConvA E I n Γ D D')

/-- Typed domain conversion gives actual equality of declared position
relations, including different full parameter/index prefixes. -/
theorem declaredIndexRelA_eq3 {E : ResolvedEnvA} {I : IotaIfaceA} {n i j : Nat}
    {Γ : LCtxA} {T T' D D' C C' : ExprA} {pre pre' : List ExprA}
    {u v u' v' : Level}
    (hT : applyTelA pre T = some (.pi D u C v))
    (hT' : applyTelA pre' T' = some (.pi D' u' C' v'))
    (hd : Nonempty (TyConvA E I n Γ D D')) :
    DeclaredIndexRelA E I n Γ T i pre =
      DeclaredIndexRelA E I n Γ T' j pre' := by
  funext a b
  apply propext
  exact ⟨declaredIndexRelA_transport hT hT' hd,
    declaredIndexRelA_transport hT' hT (tyConvA_symm_ne hd)⟩

/-- The relation equality needed by the `(F)` component of cross-fiber
transport, with the complete declared prefixes rebuilt explicitly. -/
theorem indexRelsA_cross_eq3 {E : ResolvedEnvA} {I : IotaIfaceA} {n i j : Nat}
    {Γ : LCtxA} {m : CheckedMemberA} {ls ls' : List Level}
    {ps ps' pre pre' : List ExprA} {TF TF' D D' C C' : ExprA} {u v u' v' : Level}
    (hTF : applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF)
    (hTF' : applyTelA ps' (instantiateLevelsA ls' m.mtypeA) = some TF')
    (hD : applyTelA pre TF = some (.pi D u C v))
    (hD' : applyTelA pre' TF' = some (.pi D' u' C' v'))
    (hd : Nonempty (TyConvA E I n Γ D D')) :
    IndexRelsA E I n Γ m [] ls i (ps ++ pre) =
      IndexRelsA E I n Γ m [] ls' j (ps' ++ pre') := by
  have hfull : applyTelA (ps ++ pre) (instantiateLevelsA ls m.mtypeA) =
      some (.pi D u C v) := by
    rw [applyTelA_append, hTF]
    exact hD
  have hfull' : applyTelA (ps' ++ pre') (instantiateLevelsA ls' m.mtypeA) =
      some (.pi D' u' C' v') := by
    rw [applyTelA_append, hTF']
    exact hD'
  exact declaredIndexRelA_eq3 hfull hfull' hd

/-- A complete canonical index walk crosses from `ps` to `ps'`. Every
right-hand Pi shape is supplied by the landed rigid-telescope lemma. -/
theorem indexArgs_cross_fwd3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {m : CheckedMemberA} {ls : List Level} {ps ps' : List ExprA}
    {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (hpl : ps.length = ps'.length)
    (hdom : IndexCrossDomainsA3 E I n Γ m ps ps' ls)
    {TF TF' : ExprA}
    (hTF : applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF)
    (hTF' : applyTelA ps' (instantiateLevelsA ls m.mtypeA) = some TF')
    {xs xs' : List ExprA}
    (hw : ArgsRelPA (IndexRelsA E I n Γ m [] ls) m.nparamsA ps TF xs xs') :
    ArgsRelPA (IndexRelsA E I n Γ m [] ls) m.nparamsA ps' TF' xs xs' := by
  have h := argsRelPA_cross
    (R := IndexRelsA E I n Γ m [] ls) (R' := IndexRelsA E I n Γ m [] ls)
    (i₀ := m.nparamsA) (prev₀ := ps) (prev₀' := ps') (T₀ := TF) (T₀' := TF')
    (fun pre pre' D u C v hp _ hD => by
      obtain ⟨D', u', C', v', hD'⟩ :=
        applyTelA_pi_cross (rigid_of_sortBody hsh) hpl hTF hTF' rfl hD
      have hd := hdom TF TF' pre pre' D u C v D' u' C' v' hTF hTF' hp hD hD'
      refine ⟨D', u', C', v', hD', fun f f' hr => ?_⟩
      rw [← indexRelsA_cross_eq3 (i := m.nparamsA + pre.length)
        (j := m.nparamsA + pre.length) hTF hTF' hD hD' hd]
      exact hr)
    hw [] [] TF' (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
  simpa using h

/-- The same left-domain datum gives the backward walk. The generic walk
proof constructs the needed left prefix alongside the right prefix. -/
theorem indexArgs_cross_bwd3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {m : CheckedMemberA} {ls : List Level} {ps ps' : List ExprA}
    {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (hpl : ps.length = ps'.length)
    (hdom : IndexCrossDomainsA3 E I n Γ m ps ps' ls)
    {TF TF' : ExprA}
    (hTF : applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF)
    (hTF' : applyTelA ps' (instantiateLevelsA ls m.mtypeA) = some TF')
    {xs xs' : List ExprA}
    (hw : ArgsRelPA (IndexRelsA E I n Γ m [] ls) m.nparamsA ps' TF' xs xs') :
    ArgsRelPA (IndexRelsA E I n Γ m [] ls) m.nparamsA ps TF xs xs' := by
  have h := argsRelPA_cross
    (R := IndexRelsA E I n Γ m [] ls) (R' := IndexRelsA E I n Γ m [] ls)
    (i₀ := m.nparamsA) (prev₀ := ps') (prev₀' := ps) (T₀ := TF') (T₀' := TF)
    (fun pre pre' D u C v _ hp' hD => by
      obtain ⟨D', u', C', v', hD'⟩ :=
        applyTelA_pi_cross (rigid_of_sortBody hsh) hpl.symm hTF' hTF rfl hD
      have hd := hdom TF TF' pre pre' D' u' C' v' D u C v hTF hTF' hp' hD' hD
      refine ⟨D', u', C', v', hD', fun f f' hr => ?_⟩
      rw [indexRelsA_cross_eq3 (i := m.nparamsA + pre.length)
        (j := m.nparamsA + pre.length) hTF hTF' hD' hD hd]
      exact hr)
    hw [] [] TF (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
  simpa using h

/-- Reverse the cross-domain datum itself, supplying the changed walk by
the preceding backward transport theorem. -/
theorem indexCrossDomainsA3_symm {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {m : CheckedMemberA} {ls : List Level} {ps ps' : List ExprA}
    {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (hpl : ps.length = ps'.length)
    (hdom : IndexCrossDomainsA3 E I n Γ m ps ps' ls) :
    IndexCrossDomainsA3 E I n Γ m ps' ps ls := by
  intro TF' TF pre pre' D' u' C' v' D u C v hTF' hTF hw hD' hD
  have hw' := indexArgs_cross_bwd3 hsh hpl hdom hTF hTF' hw
  exact tyConvA_symm_ne
    (hdom TF TF' pre pre' D u C v D' u' C' v' hTF hTF' hw' hD hD')

/-- The complete within-fiber index-domain datum moves to the new
parameters. At the second level list the source walk is flipped by the
already supplied index PER, then the cross-domain conversion is applied. -/
theorem indexDomainsConvertA_cross3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {m : CheckedMemberA} {ls₀ : List Level} {ps ps' : List ExprA}
    {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (hpl : ps.length = ps'.length)
    (hdom : IndexDomainsConvertA E I n Γ m ps ls₀)
    (hcross : ∀ ls, eqNListB n ls₀ ls → IndexCrossDomainsA3 E I n Γ m ps ps' ls) :
    IndexDomainsConvertA E I n Γ m ps' ls₀ := by
  intro ls ls' TB TB' pre pre' DB uB CB vB DB' uB' CB' vB'
    hl₀ hll hTB hTB' hwB hDB hDB'
  obtain ⟨TA, hTA⟩ := applyTelA_some_transfer_levels
    (rigid_of_sortBody hsh) ls ls hpl.symm hTB
  obtain ⟨TA', hTA'⟩ := applyTelA_some_transfer_levels
    (rigid_of_sortBody hsh) ls' ls' hpl.symm hTB'
  have hwA := indexArgs_cross_bwd3 hsh hpl (hcross ls hl₀) hTA hTB hwB
  obtain ⟨DA, uA, CA, vA, hDA⟩ :=
    applyTelA_pi_cross (rigid_of_sortBody hsh) hpl.symm hTB hTA rfl hDB
  obtain ⟨DA', uA', CA', vA', hDA'⟩ :=
    applyTelA_pi_cross (rigid_of_sortBody hsh) hpl.symm hTB' hTA' rfl hDB'
  have hleft := hcross ls hl₀ TA TB pre pre' DA uA CA vA DB uB CB vB
    hTA hTB hwA hDA hDB
  have hmid := hdom ls ls' TA TA' pre pre' DA uA CA vA DA' uA' CA' vA'
    hl₀ hll hTA hTA' hwA hDA hDA'
  have hwA' := (indexRelsA_per hsh hdom).flip hl₀ hll hTA hTA' hwA
  have hright := hcross ls' (eqNListB_trans hl₀ hll)
    TA' TB' pre' pre DA' uA' CA' vA' DB' uB' CB' vB'
    hTA' hTB' hwA' hDA' hDB'
  obtain ⟨cl⟩ := hleft
  obtain ⟨cm⟩ := hmid
  obtain ⟨cr⟩ := hright
  exact ⟨.trans Γ DB DA DB' cl.symm (.trans Γ DA DA' DB' cm cr)⟩

/-- A supplied PER at the new parameter prefix; it is derived from typed
domain conversion and the reconstructed walks, not an assumed PER. -/
theorem indexRelsA_per_cross3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {m : CheckedMemberA} {ls₀ : List Level} {ps ps' : List ExprA}
    {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀)
    (hpl : ps.length = ps'.length)
    (hdom : IndexDomainsConvertA E I n Γ m ps ls₀)
    (hcross : ∀ ls, eqNListB n ls₀ ls → IndexCrossDomainsA3 E I n Γ m ps ps' ls) :
    IdxPerA n (IndexRelsA E I n Γ m []) m ps' ls₀ :=
  indexRelsA_per hsh (indexDomainsConvertA_cross3 hsh hpl hdom hcross)

#print axioms IndexCrossDomainsA3
#print axioms declaredIndexRelA_eq3
#print axioms indexRelsA_cross_eq3
#print axioms indexArgs_cross_fwd3
#print axioms indexArgs_cross_bwd3
#print axioms indexCrossDomainsA3_symm
#print axioms indexDomainsConvertA_cross3
#print axioms indexRelsA_per_cross3

end Rcic.Declarative.Ann.LR3
