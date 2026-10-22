import rcic.RcicRouteCIndexSyntactic

/-!
# LR3 family operator with relational reduction and syntactic indices

The term-reduction and normality predicates are explicit parameters so that the
operator can be checked independently of the contextual head implementation.
Only family indices use the fixed declared-telescope conversion relation.
Plain constructor fields, recursive fields, and inner function fields retain
the landed semantic walks and the same fixed-point positions.

The concrete LR3 core must instantiate both parameters with its own head layer.
No old reduction, old normality, old proposition key, or logical-relation call
at an index height occurs in these definitions. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- Stuck terms relative to the supplied relational normality certificate. -/
def StuckTmParamA3 (E : ResolvedEnvA) (normal : LCtxA → ExprA → Prop)
    (Γ : LCtxA) (N : ExprA) : Prop :=
  normal Γ N ∧ ¬ CtorHeadA E N

/-- The structural family operator. The head-dependent data are parameters;
the family index relation is fixed to annotated typed conversion at the
declared telescope. Constructor fields remain semantic. -/
def FamPhiParamA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (red : LCtxA → ExprA → ExprA → ExprA → Prop) (normal : LCtxA → ExprA → Prop)
    (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (Rs : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsI : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop)
    (X : CRelA) (XF : WkSpecA → CRelA) (A a b : ExprA) : Prop :=
  Nonempty (ConvA E I n Γ a b A) ∧
  ((∃ (c : Nat) (cm : CheckedMemberA) (lsC lsC' : List Level) (kinds : List FieldShape)
      (ps₁ ps₂ fs fs' : List ExprA) (T T' : ExprA),
      E.members c = some cm ∧ cm.mclass = .constructorM ∧ memberFamRefA cm = some r ∧
      eqNListBB n (carrierLevelsA A) lsC ∧ eqNListB n lsC lsC' ∧
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds ∧
      applyTelA (carrierParamsA m A) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T ∧
      applyTelA (carrierParamsA m A) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' ∧
      FamCohA r m (RouteCIndex.IndexRelsA E I n Γ m []) A fs T fs' T' ∧
      ps₁.length = m.nparamsA ∧ ps₂.length = m.nparamsA ∧
      red Γ a (foldAppsA (.const c lsC) (ps₁ ++ fs)) A ∧
      red Γ b (foldAppsA (.const c lsC') (ps₂ ++ fs')) A ∧
      normal Γ (foldAppsA (.const c lsC) (ps₁ ++ fs)) ∧
      normal Γ (foldAppsA (.const c lsC') (ps₂ ++ fs')) ∧
      ArgsRelA (Rs c lsC) (famRecRelA m (carrierParamsA m A) (carrierLevelsA A) X)
        (famFunRelA E I n Γ m (RsI c lsC) (carrierParamsA m A) (carrierLevelsA A) XF)
        m.nparamsA (carrierParamsA m A) T kinds fs fs' ∧
      ConvArgsA E I n Γ (instantiateLevelsA lsC m.mtypeA) (carrierParamsA m A) ps₁ ∧
      ConvArgsA E I n Γ (instantiateLevelsA lsC' m.mtypeA) (carrierParamsA m A) ps₂) ∨
   (∃ N N' : ExprA,
      red Γ a N A ∧ red Γ b N' A ∧
      StuckTmParamA3 E normal Γ N ∧ StuckTmParamA3 E normal Γ N'))

theorem famPhiParamA_mono3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {red : LCtxA → ExprA → ExprA → ExprA → Prop} {normal : LCtxA → ExprA → Prop}
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    {Rs : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {X Y : CRelA} {XF YF : WkSpecA → CRelA} (hXY : ∀ A a b, X A a b → Y A a b)
    (hXF : ∀ ρ', WkOkA E I n ρ' Γ → ∀ A a b, XF ρ' A a b → YF ρ' A a b) {A a b : ExprA}
    (h : FamPhiParamA3 E I n red normal Γ r m Rs RsI X XF A a b) :
    FamPhiParamA3 E I n red normal Γ r m Rs RsI Y YF A a b := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h4', h5, hT, hT',
      h6, hp₁, hp₂, h7, h8, hn, hn', h9⟩ | hst
  · exact Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h4', h5, hT, hT',
      h6, hp₁, hp₂, h7, h8, hn, hn', argsRelA_mono (famRecRelA_mono hXY)
        (famFunRelA_mono (fun ρ' hρ' => famRecRelA_mono (hXF ρ' hρ'))) h9.1, h9.2⟩
  · exact Or.inr hst

/-- The same operator over worlds. Recursive function fields read the fixed
point at the composed world, as in the landed family operator. -/
def FamPhiWParamA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (red : LCtxA → ExprA → ExprA → ExprA → Prop) (normal : LCtxA → ExprA → Prop)
    (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsI : InnerRelsA) (X : WRelA) (ρ : WkSpecA) : CRelA :=
  FamPhiParamA3 E I n red normal (wkCtxA ρ Γ) r m (Rs ρ)
    (fun c lsC => innerRelsA RsI ρ c lsC) (X ρ)
    (fun ρ' => X (WkSpecA.comp ρ ρ'))

theorem famPhiWParamA_mono3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {red : LCtxA → ExprA → ExprA → ExprA → Prop} {normal : LCtxA → ExprA → Prop}
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} : MonoWA (FamPhiWParamA3 E I n red normal Γ r m Rs RsI) :=
  fun _ _ hXY ρ _ _ _ h => famPhiParamA_mono3 (hXY ρ)
    (fun ρ' _ => hXY (WkSpecA.comp ρ ρ')) h

/-- Every member of the new-head family fixed point retains conversion at its
carrier, independently of which relational head layer supplies the chains. -/
theorem lfpWA_famPhiWParamA_conv3 {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {red : LCtxA → ExprA → ExprA → ExprA → Prop} {normal : LCtxA → ExprA → Prop}
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsI : InnerRelsA} {ρ : WkSpecA} {A a b : ExprA}
    (h : LfpWA (FamPhiWParamA3 E I n red normal Γ r m Rs RsI) ρ A a b) :
    Nonempty (ConvA E I n (wkCtxA ρ Γ) a b A) :=
  (LfpWA.unfold famPhiWParamA_mono3 h).1

#print axioms StuckTmParamA3
#print axioms FamPhiParamA3
#print axioms famPhiParamA_mono3
#print axioms FamPhiWParamA3
#print axioms famPhiWParamA_mono3
#print axioms lfpWA_famPhiWParamA_conv3

end Rcic.Declarative.Ann.LR3
