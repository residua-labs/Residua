import rcic.RcicF3BoundedBVar
import rcic.RcicF3NormPropParamFields

/-!
# Bounded parameter mirrors supply the original field prefixes

The conversion for parameter k is interpreted before that parameter is
inserted, in the original preceding-own-parameter context. This direction
is essential: a family-fitting tuple produces an own-fitting tuple by
induction, without a fitting dummy value for the current or later binders.

`Bounds` records actual typed conversion derivations and their unchanged
LOK bounds. It is not a semantic equality or fitting callback. The theorem
below shows exactly what such source evidence would buy: original BoundDG
then normalizes every hidden field at the actual dependent source prefix,
and reconstructs the original tuple from the actual cache.

This module does NOT produce Bounds from BoundG/BoundDG or from the stored
unbounded CtorTypedT mirror evidence. It adds no residual adapter and makes
no universal PropOnly claim. The unresolved syntactic producer must supply
the conversions in these preceding-own prefixes, not in a larger context
whose current parameter or later fields already need to fit.

Source-only draft; root owns native validation. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.BoundedParameterMirrorTransport
open Rcic.Declarative RawFamily PiValueRule

/-- A bounded typed chain at every original parameter prefix. The length
equation identifies only the index sets; it is not an equation of domains. -/
def Bounds (E : ResolvedEnv) (n : Nat) (σ : Nat → Nat) (N : Nat)
    (K : Nat → Nat) (own family : List (Expr Nat))
    (hlen : own.length = family.length) : Prop :=
  ∀ k : Fin own.length,
    ∃ c : TyConvT E n (policyPrefixContext own k.val)
      (own[k]) (family[k.val]'(hlen ▸ k.isLt)),
      BoundedBVar.Bounded σ N K c

/-- Equal syntax supplies the reflexive chains with no numeric side debt. -/
theorem bounds_refl (E : ResolvedEnv) (n : Nat) (σ : Nat → Nat)
    (N : Nat) (K : Nat → Nat) (ds : List (Expr Nat)) :
    Bounds E n σ N K ds ds rfl := by
  intro k
  refine ⟨.refl _ _, ?_⟩
  simpa only [BoundedBVar.Bounded] using True.intro

/-- The existing tuple induction constructs each own prefix before the
next chain is interpreted. No fit is requested for a current or later
parameter, and no syntactic context-conversion operation is performed. -/
theorem parameters_fit (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat}
    (hE : EnvSound (mkM P μ) σ K E n)
    (own family : List (Expr Nat)) (hlen : own.length = family.length)
    (hmir : Bounds E n σ 4 K own family hlen)
    (ps : List PSet.{4})
    (hps : TelFits (mkM P μ) σ family ρ0 ps) :
    TelFits (mkM P μ) σ own ρ0 ps := by
  apply EvalPlanNormal.tuple_transport (mkM P μ) (mkM P μ) σ own family
    hlen.symm ρ0 ?_ ps hps
  intro k hk pre hpre
  obtain ⟨c, hc⟩ := hmir ⟨k, hk⟩
  have hfit : Fits (mkM P μ) σ (policyPrefixContext own k)
      (push pre ρ0) := by
    simpa only [List.nil_append, List.length_nil, Nat.zero_add, push] using
      CandidateScope.fits_original_prefix P μ σ [] own ⟨k, hk⟩ [] pre
        True.intro hpre
  have he := BoundedBVar.chain_sound P μ σ K hE (push pre ρ0) hfit c hc
  intro x hx
  exact mem_congr_right (ed_congr (mkM P μ) he).symm hx

/-- Once the actual own parameters fit, the original D bound pays the
whole beta/zeta/delta telescope theorem. Candidate soundness and old body
bounds are the same produced prefix inputs used by the existing theorem. -/
theorem original_field_normalized_of_own_fit (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (node : RecNode E E' f rr rm)
    (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (hES : EnvSound (mkM P μ) σ K (extendEnv E f fm) node.a.family.member.arity)
    (vs : List Nat) (hσ : σ = σOf vs)
    (hvl : vs.length = node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (j : Fin node.a.constructors.length)
    (k : Fin (node.a.constructorViews j).fields.length)
    (ps pre : List PSet.{4})
    (hpOwn : TelFits (mkM P μ) σ (node.a.constructorViews j).parameters ρ0 ps)
    (hpre : TelFits (mkM P μ) σ ((node.a.constructorViews j).fields.take k.val)
      (push ps ρ0) pre)
    {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel node.E0 fuel ((node.a.constructorViews j).fields[k]) =
      some (ds, b)) :
    Equiv (den (mkM P μ) σ (push pre (push ps ρ0)) (policyPi ds b))
      (den (mkM P μ) σ (push pre (push ps ρ0))
        ((node.a.constructorViews j).fields[k])) := by
  obtain ⟨l, d, hd⟩ := hD.2 node j vs hvl hvs k
  have hdσ : LOKt σ 4 K d := by rw [hσ]; exact hd
  exact CandidateScope.recNode_den_piTelescope P μ σ K hE hB.1 hA hI
    hmem node hES d hdσ hw (push pre (push ps ρ0))
    (CandidateScope.fits_original_prefix P μ σ (node.a.constructorViews j).parameters
      (node.a.constructorViews j).fields k ps pre hpOwn hpre)

/-- Syntactic mirror bounds and original BoundDG compose in the exact
candidate model. No bounded typing is moved to a different local context. -/
theorem original_field_normalized_of_mirrors (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (node : RecNode E E' f rr rm)
    (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (hES : EnvSound (mkM P μ) σ K (extendEnv E f fm) node.a.family.member.arity)
    (vs : List Nat) (hσ : σ = σOf vs)
    (hvl : vs.length = node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (j : Fin node.a.constructors.length)
    (hmir : Bounds (extendEnv E f fm) node.a.family.member.arity σ 4 K
      (node.a.constructorViews j).parameters node.a.family.parameters
      (node.a.constructorViews j).parameterCount)
    (k : Fin (node.a.constructorViews j).fields.length)
    (ps pre : List PSet.{4})
    (hps : TelFits (mkM P μ) σ node.a.family.parameters ρ0 ps)
    (hpre : TelFits (mkM P μ) σ ((node.a.constructorViews j).fields.take k.val)
      (push ps ρ0) pre)
    {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel node.E0 fuel ((node.a.constructorViews j).fields[k]) =
      some (ds, b)) :
    Equiv (den (mkM P μ) σ (push pre (push ps ρ0)) (policyPi ds b))
      (den (mkM P μ) σ (push pre (push ps ρ0))
        ((node.a.constructorViews j).fields[k])) := by
  have hpOwn := parameters_fit P μ σ K hES
    (node.a.constructorViews j).parameters node.a.family.parameters
    (node.a.constructorViews j).parameterCount hmir ps hps
  exact original_field_normalized_of_own_fit P μ σ K hE hfam hctors hrec hmem
    hB hD node hA hI hES vs hσ hvl hvs j k ps pre hpOwn hpre hw

/-- The actual normalized tuple is reconstructed field by field after
the syntactically bounded mirrors produce the initial own-parameter fit.
The same complete parameter and index keys and actual values are kept. -/
theorem fields_to_raw_of_guarded (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hB : BoundG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (hBD : BoundDG K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (X D : Frame) (hX : Admissible (famDataOf p.node.a) X)
    (hD : Admissible (famDataOf p.node.a) D)
    (hA : AllSound P (table P μ (famDataOf p.node.a) D) K p.E)
    (hI : ∀ r m, p.E.members r = some m → m.mclass = .recursorM →
      IotaAt P (table P μ (famDataOf p.node.a) D) K p.E' r)
    (hES : EnvSound (mkM P (table P μ (famDataOf p.node.a) D)) σ K
      (extendEnv p.E p.f fm) p.node.a.family.member.arity)
    (vs : List Nat) (hσ : σ = σOf vs)
    (hvl : vs.length = p.node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K p.rr)
    (j : Fin p.node.a.constructors.length)
    (hmir : Bounds (extendEnv p.E p.f fm) p.node.a.family.member.arity σ 4 K
      (p.node.a.constructorViews j).parameters p.node.a.family.parameters
      (p.node.a.constructorViews j).parameterCount)
    (ps xs : List PSet.{4})
    (hps : TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      p.node.a.family.parameters ρ0 ps)
    (hsub : EvalPlanNormalSlice.GuardedSub p.node.a.family.member.arity
      p.node.a.family.parameters.length σ ps X D)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) X))
      σ (EvalPlanNormal.fields p j) (push ps ρ0) xs) :
    TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      (p.node.a.constructorViews j).fields (push ps ρ0) xs := by
  let MX := mkM P (table P μ (famDataOf p.node.a) X)
  let MD := mkM P (table P μ (famDataOf p.node.a) D)
  have hpOwn := parameters_fit P (table P μ (famDataOf p.node.a) D) σ K hES
    (p.node.a.constructorViews j).parameters p.node.a.family.parameters
    (p.node.a.constructorViews j).parameterCount hmir ps hps
  have hlen : (EvalPlanNormal.fields p j).length =
      (p.node.a.constructorViews j).fields.length :=
    (List.length_map _ _).trans (EvalPlanNormal.specs_length (p.constructors j).fields)
  apply EvalPlanNormal.tuple_transport MX MD σ (p.node.a.constructorViews j).fields
    (EvalPlanNormal.fields p j) hlen (push ps ρ0) ?_ xs hxs
  intro k hk pre hpre
  obtain ⟨prior, s, q, hprior, hq⟩ :=
    EvalPlanNormal.field_at (p.constructors j).fields k hk
  have hkG : k < (EvalPlanNormal.fields p j).length := by rw [hlen]; exact hk
  have hget : (EvalPlanNormal.fields p j)[k]'hkG =
      fieldExpr p.node.a.family.ref (canonL p.node.a.family.member.arity)
        (EvalPlanNormal.fieldSpec q) :=
    Option.some.inj ((List.getElem?_eq_getElem hkG).symm.trans hq)
  have hpreLen : pre.length = prior := by
    have hl := hpre.length
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hl
    exact hl.trans (by simpa only [Nat.zero_add] using hprior.symm)
  rw [hget]
  cases q with
  | plain hfree =>
      have he := PiIndependent.den_free P μ (famDataOf p.node.a).fref
        (ofFrame P μ (famDataOf p.node.a) X) (ofFrame P μ (famDataOf p.node.a) D)
        σ ((p.node.a.constructorViews j).fields[k]) hfree (push pre (push ps ρ0))
      intro x hx
      change x ∈ Ed MD (den MX σ (push pre (push ps ρ0))
        ((p.node.a.constructorViews j).fields[k])) at hx
      change den MX σ (push pre (push ps ρ0))
          ((p.node.a.constructorViews j).fields[k]) =
        den MD σ (push pre (push ps ρ0))
          ((p.node.a.constructorViews j).fields[k]) at he
      rw [he] at hx
      exact hx
  | recursive r =>
      intro x hx
      have hxN := EvalPlanNormalSlice.recursive_sub_of_guarded P μ (famDataOf p.node.a)
        X D hX hD σ r ps pre hps.length hpreLen hsub x hx
      have hn := original_field_normalized_of_own_fit P
        (table P μ (famDataOf p.node.a) D) σ K hE hfam hctors hrec hmem
        hB hBD p.node hA hI hES vs hσ hvl hvs j ⟨k, hk⟩ ps pre hpOwn hpre r.read
      exact mem_congr_right (ed_congr MD hn) hxN

#print axioms parameters_fit
#print axioms original_field_normalized_of_own_fit
#print axioms original_field_normalized_of_mirrors
#print axioms fields_to_raw_of_guarded

end Rcic.F3.PSet.BoundedParameterMirrorTransport
