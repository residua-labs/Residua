import rcic.RcicF3EvalPlanNormalTuple
import rcic.RcicF3DBoundDefs

/-!
# Original fields from the actual D bound and checked parameter telescopes

BoundDG types the original fields in each constructor's own parameter
context. The existing D-side condition says that this parameter telescope
is literally the family's. Thus the actual fitting parameters and ordinary
prefix supply the original context, and bounded reader normalization pays
the reverse field transport at every recursive depth and dependent index.

No semantic mirror law is assumed. The equal-parameter premise is exactly
an existing check conjunct; unchecked arbitrary mirrors remain open.
The empty-parameter instance is produced directly from admission.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormPropParamFields
open Rcic.Declarative RawFamily PiValueRule

theorem own_parameters {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (hnp : node.a.family.parameters = [])
    (j : Fin node.a.constructors.length) :
    (node.a.constructorViews j).parameters = [] :=
  List.eq_nil_of_length_eq_zero
    ((node.a.constructorViews j).parameterCount.trans (congrArg List.length hnp))

/-- Empty family parameters automatically satisfy the literal checked
parameter equality; no additional assumption is needed on this instance. -/
theorem matching_parameters_of_empty {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (hnp : node.a.family.parameters = []) :
    ∀ j : Fin node.a.constructors.length,
      (node.a.constructorViews j).parameters = node.a.family.parameters :=
  fun j => (own_parameters node hnp j).trans hnp.symm

/-- D bounds every original field instance at the recursor valuation.
This extraction is independent of any local-context fitting proof. -/
theorem original_fields_instOK (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (node : RecNode E E' f rr rm) (vs : List Nat)
    (hσ : σ = σOf vs) (hvl : vs.length = node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K rr) (j : Fin node.a.constructors.length) :
    ∀ A ∈ (node.a.constructorViews j).fields, InstOK (extendEnv E f fm) σ K A := by
  intro A hA
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hA
  obtain ⟨l, d, hd⟩ := hD.2 node j vs hvl hvs ⟨k, hk⟩
  apply instOK_of_lokt σ 4 K d
  rw [hσ]
  exact hd

/-- The actual BoundDG field derivation is used in its original context;
the existing literal parameter equality identifies that context. -/
theorem original_field_normalized (P : Premises4)
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
    (hpar : ∀ j : Fin node.a.constructors.length,
      (node.a.constructorViews j).parameters = node.a.family.parameters)
    (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (hES : EnvSound (mkM P μ) σ K (extendEnv E f fm) node.a.family.member.arity)
    (vs : List Nat) (hσ : σ = σOf vs)
    (hvl : vs.length = node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (j : Fin node.a.constructors.length)
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
  obtain ⟨l, d, hd⟩ := hD.2 node j vs hvl hvs k
  have hdσ : LOKt σ 4 K d := by rw [hσ]; exact hd
  have hpOwn : TelFits (mkM P μ) σ (node.a.constructorViews j).parameters ρ0 ps := by
    rw [hpar j]
    exact hps
  exact CandidateScope.recNode_den_piTelescope P μ σ K hE hB.1 hA hI
    hmem node hES d hdσ hw (push pre (push ps ρ0))
    (CandidateScope.fits_original_prefix P μ σ (node.a.constructorViews j).parameters
      (node.a.constructorViews j).fields k ps pre hpOwn hpre)

/-- Full original tuple reconstruction from the actual normalized tuple.
Only the reached full-key slice of the candidate is compared to the target.
Original field typing and reader normalization are produced from BoundDG. -/
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
    (hpar : ∀ j : Fin p.node.a.constructors.length,
      (p.node.a.constructorViews j).parameters = p.node.a.family.parameters)
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
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
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
      have hn := original_field_normalized P (table P μ (famDataOf p.node.a) D)
        σ K hE hfam hctors hrec hmem hB hBD p.node hpar hA hI hES
        vs hσ hvl hvs j ⟨k, hk⟩ ps pre hps hpre r.read
      exact mem_congr_right (ed_congr MD hn) hxN

end Rcic.F3.PSet.NormPropParamFields
