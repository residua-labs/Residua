import rcic.RcicRouteCLargeIndexBoundary

/-!
# Route C R2: a family fragment with syntactic indices

The index relation below asks for annotated typed conversion at the domain
exposed by the declared telescope. It has no height argument. The family
operator is the landed operator specialized at that relation: plain fields,
direct recursion and function recursion retain their semantic clauses.

`IndexFamTyA` is a separately named family-clause fragment. Its field obligations
are the landed obligations, including semantic inner domains of function fields.
Only index-domain validity is removed and index-domain equality becomes typed
conversion. This is not a replacement of the full mutual `TyKA`/`EqKA` tower.
The all-constructor transport/fund/row integration remains a separate obligation.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.RouteCIndex

open Rcic.Declarative

/-- Typed conversion at the next declared domain, after the complete prefix. -/
def DeclaredIndexRelA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (Γ : LCtxA) (T : ExprA) (_i : Nat) (pre : List ExprA) (a b : ExprA) : Prop :=
  ∃ D u C v, applyTelA pre T = some (.pi D u C v) ∧
    Nonempty (ConvA E I n Γ a b D)

theorem declaredIndexRelA_iff {E : ResolvedEnvA} {I : IotaIfaceA} {n i : Nat}
    {Γ : LCtxA} {T D C a b : ExprA} {pre : List ExprA} {u v : Level}
    (hT : applyTelA pre T = some (.pi D u C v)) :
    DeclaredIndexRelA E I n Γ T i pre a b ↔ Nonempty (ConvA E I n Γ a b D) := by
  constructor
  · rintro ⟨D', u', C', v', hT', h⟩
    cases Option.some.inj (hT.symm.trans hT')
    exact h
  · exact fun h => ⟨D, u, C, v, hT, h⟩

theorem declaredIndexRelA_symm {E : ResolvedEnvA} {I : IotaIfaceA} {n i : Nat}
    {Γ : LCtxA} {T a b : ExprA} {pre : List ExprA}
    (h : DeclaredIndexRelA E I n Γ T i pre a b) :
    DeclaredIndexRelA E I n Γ T i pre b a := by
  rcases h with ⟨D, u, C, v, hT, hc⟩
  exact ⟨D, u, C, v, hT, hc.elim fun c => ⟨.symm _ _ _ _ c⟩⟩

theorem declaredIndexRelA_trans {E : ResolvedEnvA} {I : IotaIfaceA} {n i : Nat}
    {Γ : LCtxA} {T a b c : ExprA} {pre : List ExprA}
    (h : DeclaredIndexRelA E I n Γ T i pre a b)
    (h' : DeclaredIndexRelA E I n Γ T i pre b c) :
    DeclaredIndexRelA E I n Γ T i pre a c := by
  rcases h with ⟨D, u, C, v, hT, hab⟩
  have hbc := (declaredIndexRelA_iff hT).1 h'
  exact ⟨D, u, C, v, hT, hab.elim fun ab => hbc.elim fun bc => ⟨.trans _ _ _ _ _ ab bc⟩⟩

/-- Moving an index between two declared domains uses typed conversion only. -/
theorem declaredIndexRelA_transport {E : ResolvedEnvA} {I : IotaIfaceA} {n i j : Nat}
    {Γ : LCtxA} {T T' D D' C C' a b : ExprA} {pre pre' : List ExprA} {u v u' v' : Level}
    (hT : applyTelA pre T = some (.pi D u C v))
    (hT' : applyTelA pre' T' = some (.pi D' u' C' v'))
    (hd : Nonempty (TyConvA E I n Γ D D'))
    (h : DeclaredIndexRelA E I n Γ T i pre a b) :
    DeclaredIndexRelA E I n Γ T' j pre' a b :=
  (declaredIndexRelA_iff hT').2 (convA_retype hd ((declaredIndexRelA_iff hT).1 h))

/-- A dependent two-sided index walk also records conversion of the reached
domains. This datum is essential when the preceding indices change. -/
abbrev IndexWalkA := ParConvA

theorem indexWalkA_symm {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {T T' : ExprA} {xs xs' : List ExprA}
    (h : IndexWalkA E I n Γ T T' xs xs') : IndexWalkA E I n Γ T' T xs' xs :=
  parConvA_symm h

theorem indexWalkA_trans {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {T T' T'' : ExprA} {xs xs' xs'' : List ExprA}
    (h : IndexWalkA E I n Γ T T' xs xs') (h' : IndexWalkA E I n Γ T' T'' xs' xs'') :
    IndexWalkA E I n Γ T T'' xs xs'' := parConvA_trans h h'

theorem indexWalkA_rebase {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {T T' : ExprA} {xs xs' ys : List ExprA}
    (h : IndexWalkA E I n Γ T T' xs xs') (h' : ConvArgsA E I n Γ T xs ys) :
    ConvArgsA E I n Γ T' xs' ys := convArgsA_rebase h h'

/-- The index walk used by the actual family operator entails typed conversion
at every declared domain, starting at any already instantiated prefix. -/
theorem argsRelPA_declaredIndex_conv {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {T : ExprA} {i : Nat} {pre : List ExprA} {U : ExprA} {xs ys : List ExprA}
    (h : ArgsRelPA (DeclaredIndexRelA E I n Γ T) i pre U xs ys)
    (hT : applyTelA pre T = some U) : ConvArgsA E I n Γ U xs ys := by
  revert hT
  induction h with
  | nil i pre U => intro _; exact .nil U
  | cons i pre A u B v f f' fs fs' h hs ih =>
      intro hT
      refine .cons A u B v f f' fs fs' ((declaredIndexRelA_iff hT).1 h) (ih ?_)
      rw [applyTelA_append, hT]
      rfl

/-- Conversely, declared typed conversions supply the specialized index walk. -/
theorem convArgsA_declaredIndex {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {T U : ExprA} {xs ys : List ExprA} (h : ConvArgsA E I n Γ U xs ys)
    (i : Nat) (pre : List ExprA) (hT : applyTelA pre T = some U) :
    ArgsRelPA (DeclaredIndexRelA E I n Γ T) i pre U xs ys := by
  induction h generalizing i pre with
  | nil U => exact .nil i pre U
  | cons A u B v f f' fs fs' h hs ih =>
      refine .cons i pre A u B v f f' fs fs' ((declaredIndexRelA_iff hT).2 h) (ih _ _ ?_)
      rw [applyTelA_append, hT]
      rfl

/-- A two-sided typed walk transports the operator's specialized index walk,
including the dependent domain changes. -/
theorem declaredIndexWalk_rebase {E : ResolvedEnvA} {I : IotaIfaceA} {n i j : Nat}
    {Γ : LCtxA} {T T' U U' : ExprA} {pre pre' xs zs ys : List ExprA}
    (hT : applyTelA pre T = some U) (hT' : applyTelA pre' T' = some U')
    (hp : IndexWalkA E I n Γ U U' xs zs)
    (h : ArgsRelPA (DeclaredIndexRelA E I n Γ T) i pre U xs ys) :
    ArgsRelPA (DeclaredIndexRelA E I n Γ T') j pre' U' zs ys :=
  convArgsA_declaredIndex (convArgsA_rebase hp (argsRelPA_declaredIndex_conv h hT)) j pre' hT'

/-- The declared index relation at each world and level instance. -/
def IndexRelsA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA)
    (m : CheckedMemberA) (ρ : WkSpecA) (ls : List Level) :
    Nat → List ExprA → ExprA → ExprA → Prop :=
  DeclaredIndexRelA E I n (wkCtxA ρ Γ) (instantiateLevelsA ls m.mtypeA)

/-- The landed structural family operator, changing its index relation only. -/
def IndexFamPhiWA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA)
    (r : Nat) (m : CheckedMemberA)
    (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsI : InnerRelsA) : WOpA :=
  FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI

theorem indexFamPhiWA_mono {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} : MonoWA (IndexFamPhiWA E I n Γ r m Rs RsI) := famPhiWA_mono

/-- Carrier relation with semantic constructor fields and syntactic indices. -/
def IndexFamRelA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA)
    (r : Nat) (m : CheckedMemberA)
    (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsI : InnerRelsA) : WRelA := LfpWA (IndexFamPhiWA E I n Γ r m Rs RsI)

theorem indexFamRelA_conv {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {ρ : WkSpecA} {A a b : ExprA}
    (h : IndexFamRelA E I n Γ r m Rs RsI ρ A a b) :
    Nonempty (ConvA E I n (wkCtxA ρ Γ) a b A) := lfpWA_famPhiWA_conv h

/-- The exact no-constructor hypothesis used for the inhabited large-index family. -/
def NoFamilyCtorA (E : ResolvedEnvA) (r : Nat) : Prop :=
  ∀ c cm, E.members c = some cm → cm.mclass = .constructorM →
    memberFamRefA cm = some r → False

/-- The constructor-free fixed point still requires typed head reductions to
stuck forms; plain conversion alone does not supply it. -/
theorem indexFamRelA_noCtor_iff {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {ρ : WkSpecA} {A a b : ExprA} (hno : NoFamilyCtorA E r) :
    IndexFamRelA E I n Γ r m Rs RsI ρ A a b ↔
      Nonempty (ConvA E I n (wkCtxA ρ Γ) a b A) ∧
      ∃ N N', TyHRedStarA E I n (wkCtxA ρ Γ) a N A ∧
        TyHRedStarA E I n (wkCtxA ρ Γ) b N' A ∧
        StuckTmA E I (wkCtxA ρ Γ) N ∧ StuckTmA E I (wkCtxA ρ Γ) N' := by
  constructor
  · intro h
    have hs := LfpWA.unfold indexFamPhiWA_mono h
    refine ⟨hs.1, ?_⟩
    rcases hs.2 with hc | ht
    · rcases hc with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hm, hk, hr, _⟩
      exact (hno c cm hm hk hr).elim
    · exact ht
  · intro h
    exact LfpWA.fold indexFamPhiWA_mono ⟨h.1, Or.inr h.2⟩

theorem indexFamRelA_noCtor_transport {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {ρ : WkSpecA} {A B a b : ExprA} (hno : NoFamilyCtorA E r)
    (hc : Nonempty (TyConvA E I n (wkCtxA ρ Γ) A B))
    (h : IndexFamRelA E I n Γ r m Rs RsI ρ A a b) :
    IndexFamRelA E I n Γ r m Rs RsI ρ B a b := by
  rcases (indexFamRelA_noCtor_iff hno).1 h with ⟨hab, N, N', ha, hb, hN, hN'⟩
  exact (indexFamRelA_noCtor_iff hno).2
    ⟨convA_retype hc hab, N, N', tyHRedStarA_retype hc ha, tyHRedStarA_retype hc hb, hN, hN'⟩

theorem indexFamRelA_noCtor_symm {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {ρ : WkSpecA} {A a b : ExprA} (hno : NoFamilyCtorA E r)
    (h : IndexFamRelA E I n Γ r m Rs RsI ρ A a b) :
    IndexFamRelA E I n Γ r m Rs RsI ρ A b a := by
  rcases (indexFamRelA_noCtor_iff hno).1 h with ⟨hab, N, N', ha, hb, hN, hN'⟩
  exact (indexFamRelA_noCtor_iff hno).2
    ⟨hab.elim fun c => ⟨.symm _ _ _ _ c⟩, N', N, hb, ha, hN', hN⟩

theorem indexFamRelA_noCtor_trans {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {ρ : WkSpecA} {A a b c : ExprA} (hno : NoFamilyCtorA E r)
    (h : IndexFamRelA E I n Γ r m Rs RsI ρ A a b)
    (h' : IndexFamRelA E I n Γ r m Rs RsI ρ A b c) :
    IndexFamRelA E I n Γ r m Rs RsI ρ A a c := by
  rcases (indexFamRelA_noCtor_iff hno).1 h with ⟨hab, N, N', ha, _, hN, _⟩
  rcases (indexFamRelA_noCtor_iff hno).1 h' with ⟨hbc, M, M', _, hc, _, hM'⟩
  exact (indexFamRelA_noCtor_iff hno).2
    ⟨hab.elim fun ab => hbc.elim fun bc => ⟨.trans _ _ _ _ _ ab bc⟩, N, M', ha, hc, hN, hM'⟩

-- BEGIN RCIC_ROUTE_C_INDEX_ROOTS
#print axioms DeclaredIndexRelA
#print axioms declaredIndexRelA_iff
#print axioms declaredIndexRelA_symm
#print axioms declaredIndexRelA_trans
#print axioms declaredIndexRelA_transport
#print axioms IndexWalkA
#print axioms indexWalkA_symm
#print axioms indexWalkA_trans
#print axioms indexWalkA_rebase
#print axioms argsRelPA_declaredIndex_conv
#print axioms convArgsA_declaredIndex
#print axioms declaredIndexWalk_rebase
#print axioms IndexRelsA
#print axioms IndexFamPhiWA
#print axioms indexFamPhiWA_mono
#print axioms IndexFamRelA
#print axioms indexFamRelA_conv
#print axioms NoFamilyCtorA
#print axioms indexFamRelA_noCtor_iff
#print axioms indexFamRelA_noCtor_transport
#print axioms indexFamRelA_noCtor_symm
#print axioms indexFamRelA_noCtor_trans
-- END RCIC_ROUTE_C_INDEX_ROOTS

end Rcic.Declarative.Ann.RouteCIndex
