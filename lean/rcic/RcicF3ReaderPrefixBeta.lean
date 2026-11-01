import rcic.RcicF3PointwisePropOnlyNormalized
import rcic.RcicF3PointwiseReaderNoBetaFields
import rcic.RcicF3FamilyBetaMirror

/-!
# Cached source reconstruction using the available family/field prefix

The available local context consists of the family's parameters followed by
the original fields already reconstructed. It need not be the constructor's
own parameter context. A beta contraction whose argument is a lookup from
this available context has its annotated-domain membership directly from
Fits. No bounded constructor-parameter mirror is requested.

The syntactic reduction relation also composes the existing fresh-family
beta construction, transparent delta, zeta, application suffixes, and Pi
descent. Its target is the actual cached field, not a chosen surrogate.
This is a new produced source face. Completeness of that face for arbitrary
admitted recursive fields is not asserted. closure_claim = 0.

Source draft; native elaboration and the complete axiom audit are root-owned.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.ReaderPrefixBeta
open Rcic.Declarative RawFamily PiValueRule

/-- A source-only relation interpreted at the supplied local context.
The beta rule checks a literal lookup, not a semantic fitting callback. -/
inductive Reduces (p : EvalPlan.Plan) : LCtx → Expr Nat → Expr Nat → Prop where
  | refl (Γ : LCtx) (A : Expr Nat) : Reduces p Γ A A
  | betaLocal {Γ : LCtx} {A body : Expr Nat} {i : Nat}
      (lookup : lookupType Γ i = some A) :
      Reduces p Γ (.app (.lam A body) (.bvar i))
        (instantiate0 (.bvar i) body)
  | betaFamily (Γ : LCtx) (A : Expr Nat) :
      Reduces p Γ
        (FamilyBetaMirror.mirror (EvalPlanNormal.fd p)
          p.node.a.family.member.arity A) A
  | zeta (Γ : LCtx) (A v body : Expr Nat) :
      Reduces p Γ (.letE A v body) (instantiate0 v body)
  | delta (Γ : LCtx) (r : Nat) (ls : List Level) (body : Expr Nat)
      (lookup : transparentBody p.node.E0 r ls = some body) :
      Reduces p Γ (.const r ls) body
  | apps {Γ : LCtx} {f g : Expr Nat}
      (head : Reduces p Γ f g) (args : List (Expr Nat)) :
      Reduces p Γ (foldApps f args) (foldApps g args)
  | pi {Γ : LCtx} {A B B' : Expr Nat}
      (body : Reduces p (.assumption A :: Γ) B B') :
      Reduces p Γ (.pi A B) (.pi A B')
  | trans {Γ : LCtx} {A B C : Expr Nat}
      (left : Reduces p Γ A B) (right : Reduces p Γ B C) :
      Reduces p Γ A C

/-- Every conversion step is interpreted in an already-fitting context.
Pi descent extends that fit by its actual domain member. The whole own
parameter telescope never enters this theorem. -/
theorem Reduces.den_equiv (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (D : Frame) (hD : Admissible (famDataOf p.node.a) D)
    (hδ : DeltaNormalize.BodyEquations
      (mkM P (table P μ (famDataOf p.node.a) D)) p.node.E0 σ)
    {Γ : LCtx} {A B : Expr Nat} (h : Reduces p Γ A B) :
    ∀ (ρ : Nat → PSet.{4}),
      Fits (mkM P (table P μ (famDataOf p.node.a) D)) σ Γ ρ →
      Equiv (den (mkM P (table P μ (famDataOf p.node.a) D)) σ ρ A)
        (den (mkM P (table P μ (famDataOf p.node.a) D)) σ ρ B) := by
  let M := mkM P (table P μ (famDataOf p.node.a) D)
  induction h with
  | refl => intro ρ _hρ; exact Equiv.rfl
  | @betaLocal Γ A body i hlookup =>
      intro ρ hρ
      have harg : den M σ ρ (.bvar i) ∈ Ed M (den M σ ρ A) :=
        fits_lookupType M σ Γ ρ hρ i A hlookup
      rw [den_inst0]
      exact beta_val M
        (fun _ _ hx => den_congr M σ body
          (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl))) harg
  | betaFamily Γ A =>
      intro ρ _hρ
      simpa only [FamilyBetaMirror.mirrors] using
        FamilyBetaMirror.den_of_group P μ p fm ctors hE hmem D hD σ ρ 1 A
  | zeta Γ A v body =>
      intro ρ _hρ
      rw [den_inst0]
      exact Equiv.rfl
  | delta Γ r ls body hlookup =>
      intro ρ _hρ
      exact hδ r ls body hlookup ρ
  | @apps Γ f g hhead args ih =>
      intro ρ hρ
      rw [den_foldApps, den_foldApps]
      exact fapps_congr (ih ρ hρ) _
  | @pi Γ A B B' hbody ih =>
      intro ρ hρ
      change Equiv (piVal M (den M σ ρ A)
        (fun x => den M σ (vcons x ρ) B))
        (piVal M (den M σ ρ A) (fun x => den M σ (vcons x ρ) B'))
      apply piVal_congr_on M
        (B := fun x => den M σ (vcons x ρ) B)
        (B' := fun x => den M σ (vcons x ρ) B') Equiv.rfl
        (fun _ _ hx => den_congr M σ B
          (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl)))
        (fun _ _ hx => den_congr M σ B'
          (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl)))
      intro x hx
      exact ih (vcons x ρ) ⟨hρ, hx⟩
  | trans _ _ ihLeft ihRight =>
      intro ρ hρ
      exact (ihLeft ρ hρ).trans (ihRight ρ hρ)

/-- Existing actual no-beta head traces are included at every context. -/
theorem Reduces.of_noBetaHead (p : EvalPlan.Plan) (Γ : LCtx)
    {fuel : Nat} {e w : Expr Nat}
    (h : ReaderNoBeta.Head p.node.E0 fuel e w) : Reduces p Γ e w := by
  induction h with
  | stop fuel e hs => exact .refl Γ e
  | @zeta fuel e A v body w args hs hnext ih =>
      have he := foldApps_appsSpine e
      rw [hs] at he
      simp only at he
      have hstep : Reduces p Γ e (foldApps (instantiate0 v body) args) := by
        rw [← he]
        exact .apps (.zeta Γ A v body) args
      exact .trans hstep ih
  | @delta fuel r ls e body w args hs hb hnext ih =>
      have he := foldApps_appsSpine e
      rw [hs] at he
      simp only at he
      have hstep : Reduces p Γ e (foldApps body args) := by
        rw [← he]
        exact .apps (.delta Γ r ls body hb) args
      exact .trans hstep ih

/-- Pi descent retains the exact domains of the successful cached reader. -/
theorem Reduces.of_noBetaTelescope (p : EvalPlan.Plan) (Γ : LCtx)
    {fuel : Nat} {e b : Expr Nat} {ds : List (Expr Nat)}
    (h : ReaderNoBeta.Telescope p.node.E0 fuel e ds b) :
    Reduces p Γ e (policyPi ds b) := by
  induction h generalizing Γ with
  | leaf hhead hnot => exact of_noBetaHead p Γ hhead
  | @pi fuel e A B b ds hhead htail ih =>
      exact .trans (of_noBetaHead p Γ hhead)
        (.pi (ih (.assumption A :: Γ)))

/-- The earlier fresh-family wrapper may occur beside local beta steps. -/
theorem Reduces.of_familyMirrors (p : EvalPlan.Plan) (Γ : LCtx)
    (depth : Nat) (A : Expr Nat) :
    Reduces p Γ
      (FamilyBetaMirror.mirrors (EvalPlanNormal.fd p)
        p.node.a.family.member.arity depth A) A := by
  induction depth with
  | zero => exact .refl Γ A
  | succ depth ih => exact .trans (.betaFamily Γ _) ih

/-- A literal lookup-backed unused binder is a concrete source producer.
Its annotation may depend on all earlier parameters and fields. -/
theorem Reduces.localWrapper (p : EvalPlan.Plan) (Γ : LCtx)
    (i : Nat) (T A : Expr Nat) (hlookup : lookupType Γ i = some T) :
    Reduces p Γ
      (.app (.lam T (Rcic.Declarative.lift 0 1 A)) (.bvar i)) A := by
  have h := Reduces.betaLocal (p := p) (body := Rcic.Declarative.lift 0 1 A) hlookup
  have hinst : instantiate0 (.bvar i) (Rcic.Declarative.lift 0 1 A) = A :=
    instantiate_lift_id 0 (.bvar i) A
  rw [hinst] at h
  exact h

/-- At field k the available context contains fitting FAMILY parameters
and the ORIGINAL fields already reconstructed. No own-parameter fit is
asserted. Both expressions are the literal source/cache entries. -/
def Cached (p : EvalPlan.Plan) : Prop :=
  ∀ (j : Fin p.node.a.constructors.length) (k : Nat)
    (hk : k < (p.node.a.constructorViews j).fields.length)
    (hkn : k < (EvalPlanNormal.fields p j).length),
    Reduces p
      (policyPrefixContext
        (p.node.a.family.parameters ++ (p.node.a.constructorViews j).fields)
        (p.node.a.family.parameters.length + k))
      ((p.node.a.constructorViews j).fields[k]) ((EvalPlanNormal.fields p j)[k])

def SourcePrefixBeta {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop := Cached (EvalPlan.ofNode node)

theorem cached_of_source_eq (p : EvalPlan.Plan)
    (he : ∀ j : Fin p.node.a.constructors.length,
      EvalPlanNormal.fields p j = (p.node.a.constructorViews j).fields) : Cached p := by
  intro j k hk hkn
  have hget : (EvalPlanNormal.fields p j)[k]'hkn =
      ((p.node.a.constructorViews j).fields[k]'hk) := by
    exact Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans
      ((congrArg (fun fs => fs[k]?) (he j)).trans (List.getElem?_eq_getElem hk)))
  rw [hget]
  exact .refl _ _

/-- Every previously certified actual delta/zeta reader has this source
certificate. No condition is imposed on original parameter mirrors. -/
theorem cached_of_noBeta (p : EvalPlan.Plan) (hread : ReaderNoBeta.Cached p) : Cached p := by
  intro j k hk hkn
  obtain ⟨prior, s, q, hprior, hq, htrace⟩ :=
    ReaderNoBeta.field_at (p.constructors j).fields (hread j) k hk
  have hget : (EvalPlanNormal.fields p j)[k]'hkn =
      fieldExpr p.node.a.family.ref (canonL p.node.a.family.member.arity)
        (EvalPlanNormal.fieldSpec q) :=
    Option.some.inj ((List.getElem?_eq_getElem hkn).symm.trans hq)
  rw [hget]
  cases q with
  | plain hfree => exact .refl _ _
  | recursive r => exact Reduces.of_noBetaTelescope p _ htrace

/-- Reconstruct the actual original tuple after normalized monotonicity.
Only an already constructed prefix is used to interpret each local beta. -/
theorem fields_to_raw (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hsource : Cached p) (X D : Frame)
    (hX : Admissible (famDataOf p.node.a) X)
    (hD : Admissible (famDataOf p.node.a) D)
    (hδ : DeltaNormalize.BodyEquations
      (mkM P (table P μ (famDataOf p.node.a) D)) p.node.E0 σ)
    (hsub : FrameSub X D) (j : Fin p.node.a.constructors.length)
    (ps xs : List PSet.{4})
    (hps : TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      p.node.a.family.parameters ρ0 ps)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) X)) σ
      (EvalPlanNormal.fields p j) (push ps ρ0) xs) :
    TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      (p.node.a.constructorViews j).fields (push ps ρ0) xs := by
  let MD := mkM P (table P μ (famDataOf p.node.a) D)
  have hnorm := PointwisePropOnlyNormalizedFields.fields_mono P μ σ p
    X D hX hD hsub j (push ps ρ0) xs hxs
  have hlen : (EvalPlanNormal.fields p j).length =
      (p.node.a.constructorViews j).fields.length :=
    (List.length_map _ _).trans (EvalPlanNormal.specs_length (p.constructors j).fields)
  apply EvalPlanNormal.tuple_transport MD MD σ (p.node.a.constructorViews j).fields
    (EvalPlanNormal.fields p j) hlen (push ps ρ0) ?_ xs hnorm
  intro k hk pre hpre
  have hkn : k < (EvalPlanNormal.fields p j).length := by rw [hlen]; exact hk
  have hfit := CandidateScope.fits_original_prefix P
    (table P μ (famDataOf p.node.a) D) σ p.node.a.family.parameters
    (p.node.a.constructorViews j).fields ⟨k, hk⟩ ps pre hps hpre
  have he := Reduces.den_equiv P μ σ p fm ctors hE hmem D hD hδ
    (hsource j k hk hkn) (push pre (push ps ρ0)) hfit
  intro x hx
  exact mem_congr_right (ed_congr MD he).symm hx

/-- The public transport produces delta semantics from the original
predecessor's faithful table, as in the existing no-beta construction. -/
theorem fields_to_raw_of_pointwise (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (α : PointwiseRole.Arities) (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hsource : Cached p) (X D : Frame)
    (hX : Admissible (famDataOf p.node.a) X)
    (hD : Admissible (famDataOf p.node.a) D)
    (hsub : FrameSub X D) (j : Fin p.node.a.constructors.length)
    (ps xs : List PSet.{4})
    (hps : TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      p.node.a.family.parameters ρ0 ps)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) X)) σ
      (EvalPlanNormal.fields p j) (push ps ρ0) xs) :
    TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      (p.node.a.constructorViews j).fields (push ps ρ0) xs :=
  fields_to_raw P μ σ p fm ctors hE hmem hsource X D hX hD
    (ReaderNoBeta.bodyEquations_update_at_node P μ σ p fm ctors hE hmem
      α ctx plans hctx hFaith D) hsub j ps xs hps hxs

end Rcic.F3.PSet.ReaderPrefixBeta

#print axioms Rcic.F3.PSet.ReaderPrefixBeta.Reduces.den_equiv
#print axioms Rcic.F3.PSet.ReaderPrefixBeta.cached_of_noBeta
#print axioms Rcic.F3.PSet.ReaderPrefixBeta.fields_to_raw_of_pointwise
