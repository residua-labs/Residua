import rcic.RcicF3IndexedWrapFixture
import rcic.RcicF3PropIndexConversionGeneric
import rcic.RcicF3PropIndexConversionSemantics
import rcic.RcicF3IndexedPropPlainValue
import rcic.RcicF3IndexedPropPlainIota
import rcic.RcicF3IndexedPropRecMem
import rcic.RcicF3IndexedPropCtor

/-!
# The admitted Wrap target in the arbitrary-extension iota attack

The admitted target is the separate synthetic Wrap fixture, with one
revealed ordinary field. The containing signature adds the unadmitted
two-constructor Prop Bool gadget at refs 3..6. Its table agrees exactly
with the canonical pointwise Wrap table at refs 0..2; actual read
congruence transfers faithfulness of the admitted target.

The candidate bad redex supplies index b while its constructor contains
field a. Both indices are local proposition codes. The minor returns
its supplied index as data, at motive universe 1. Its major is typed
using the actual generic Bool conversion between Wrap a and Wrap b.

This file proves the complete IotaAt obstruction, including actual
hereditary and computation certificates. IndexedWrapBoundBoundary proves
that this fixture lies outside the unchanged original BoundG domain.
The containing signature is not asserted EnvWfT.
scope_closure_claim = 0. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000


namespace Rcic.F3.PSet.IndexedWrapIotaAttack

open Rcic.Declarative Rcic.Model.PS RawFamily
open PropEvalSafeIndex (falseCode trueCode)

noncomputable abbrev σ : Nat → Nat := σOf [1]
noncomputable abbrev bound : Nat → Nat := fun _ => 1

noncomputable def extension : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv (extendEnv IndexedWrapFixture.env
    3 PropIndexConversionAttack.boolMember)
    4 PropIndexConversionAttack.ctorMember)
    5 PropIndexConversionAttack.ctorMember)
    6 PropIndexConversionAttack.recMember

noncomputable def lookups : PropIndexConversionGeneric.Lookups extension :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem member_ref (r : Nat) (m : CheckedMember)
    (h : IndexedWrapFixture.env.members r = some m) : r = 0 ∨ r = 1 ∨ r = 2 := by
  by_cases h2 : r = 2
  · exact Or.inr (Or.inr h2)
  by_cases h1 : r = 1
  · exact Or.inr (Or.inl h1)
  by_cases h0 : r = 0
  · exact Or.inl h0
  have hn : (none : Option CheckedMember) = some m := by
    simpa only [IndexedWrapFixture.env, IndexedWrapFixture.groupPrefix,
      IndexedWrapFixture.famOnly, extendEnv, if_neg h2, if_neg h1,
      if_neg h0, emptyEnv] using h
  cases hn

theorem extends_wrap : ∀ r m, IndexedWrapFixture.env.members r = some m →
    extension.members r = some m := by
  intro r m hm
  rcases member_ref r m hm with hr | hr | hr
  · subst r; exact hm
  · subst r; exact hm
  · subst r; exact hm

noncomputable def baseTable (P : Premises4) : Nat → List Nat → PSet.{4} :=
  PointwiseRole.table P IndexedWrapFixture.envWfT

/-- The modifications are outside the admitted target's complete support. -/
noncomputable def table (P : Premises4) : Nat → List Nat → PSet.{4}
  | 3, _ => trueCode
  | 4, _ => pempty
  | 5, _ => pempty
  | 6, _ => PropIndexConversionSemantics.recValue P
  | r, vs => baseTable P r vs

noncomputable abbrev model (P : Premises4) : Interp.{4} := mkM P (table P)

theorem table_agrees (P : Premises4) :
    AgreeOn (baseTable P) (table P) (Dom IndexedWrapFixture.env) := by
  intro r hr vs
  cases hm : IndexedWrapFixture.env.members r with
  | none =>
      change (IndexedWrapFixture.env.members r).isSome at hr
      rw [hm] at hr
      cases hr
  | some m =>
      rcases member_ref r m hm with he | he | he
      · subst r; rfl
      · subst r; rfl
      · subst r; rfl

theorem faithful (P : Premises4) :
    EvalRole.Faithful
      (PointwiseRole.familyValue (PointwiseRole.arities IndexedWrapFixture.env))
      P (table P) (NormRole.envCtx IndexedWrapFixture.envWfT)
      (EvalRole.envPlan IndexedWrapFixture.envWfT) IndexedWrapFixture.env := by
  have hF := (PointwiseRole.table_spec P IndexedWrapFixture.envWfT).2.1
  have hR := (PointwiseRole.table_spec P IndexedWrapFixture.envWfT).2.2
  intro r m hm vs
  rw [← table_agrees P r (dom_of_members hm) vs]
  exact (hF r m hm vs).trans
    (EvalRole.member_agree (PointwiseRole.familyReadsCtx _ P _)
      (table_agrees P) r m (EvalRole.envPlan IndexedWrapFixture.envWfT r)
      (hR r m hm) vs)

theorem ctorClasses : ∀ c ∈ [(1, IndexedWrapFixture.introMember)],
    c.2.mclass = .constructorM := by
  intro c hc
  cases List.mem_singleton.mp hc
  rfl

noncomputable def plan : EvalPlan.Plan :=
  EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
    (f := 0) (fm := IndexedWrapFixture.famMember)
    (ctors := [(1, IndexedWrapFixture.introMember)])
    (rr := 2) (rm := IndexedWrapFixture.recMember)
    rfl ctorClasses rfl IndexedWrapFixture.membersT

theorem uniform_prop : UniformProp plan.node.a.family.resultLevel := by
  intro τ
  rw [(IndexedWrapFixture.family_info plan.node).2.2]
  rfl

theorem policy (node : IndexedWrapFixture.Node) : node.a.policy = .anySort := by
  cases h : node.a.policy with
  | anySort => rfl
  | propOnly =>
      have ha := node.a.recursorArity
      rw [IndexedWrapFixture.family_member node, h] at ha
      change 1 = 0 at ha
      exact False.elim (Nat.noConfusion ha)

theorem count : plan.node.a.constructors.length = 1 :=
  node_ctors_length (ctors := [(1, IndexedWrapFixture.introMember)]) plan.node rfl

noncomputable def ctor : Fin plan.node.a.constructors.length :=
  ⟨0, by rw [count]; decide⟩

theorem fields_free (node : IndexedWrapFixture.Node)
    (j : Fin node.a.constructors.length) (A : Expr Nat)
    (hA : A ∈ (node.a.constructorViews j).fields) :
    occursConst node.a.family.ref A = false := by
  rw [(IndexedWrapFixture.constructor_view node j).2.1] at hA
  cases List.mem_singleton.mp hA
  rfl

theorem shapes (node : IndexedWrapFixture.Node)
    (j : Fin node.a.constructors.length) :
    node.h14.shapesAt j = [.nonrecursive] := by
  have h := node.h14.analyzed j
  rw [(IndexedWrapFixture.constructor_view node j).2.1] at h
  exact fieldShapesFuel_unique h
    (show fieldShapesFuel node.E0 8 node.a.family.ref
      node.a.family.member.arity node.a.family.parameters.length
      node.a.family.indices.length (node.a.family.parameters.length + 0)
      [.sort .zero] = some [.nonrecursive] from rfl)

theorem noFun (node : IndexedWrapFixture.Node) : NoFunRec node := by
  intro j s hs
  rw [shapes node j] at hs
  exact Or.inl (List.mem_singleton.mp hs)

theorem recursor_value (P : Premises4) : ∀ vs,
    Equiv (table P 2 vs)
      (EvalPlanValue.memberValue (model P) (σOf vs) plan IndexedWrapFixture.recMember) :=
  PointwiseRoleEquations.recursor_value_of_group P
    (PointwiseRole.arities IndexedWrapFixture.env) (table P)
    (f := 0) (fm := IndexedWrapFixture.famMember)
    (ctors := [(1, IndexedWrapFixture.introMember)])
    (rr := 2) (rm := IndexedWrapFixture.recMember)
    .empty rfl ctorClasses rfl IndexedWrapFixture.membersT
    (NormRole.envCtx IndexedWrapFixture.envWfT)
    (EvalRole.envPlan IndexedWrapFixture.envWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P)

theorem family_equation (P : Premises4) : ∀ vs,
    Equiv (table P plan.node.a.family.ref vs)
      (ofFrame P (table P) (famDataOf plan.node.a)
        (frame P (table P) (EvalPlanNormal.fd (EvalPlan.ofNode plan.node))) vs) :=
  PointwisePropPrefix.family_equation_of_group P
    (PointwiseRole.arities IndexedWrapFixture.env) (table P)
    (f := 0) (fm := IndexedWrapFixture.famMember)
    (ctors := [(1, IndexedWrapFixture.introMember)])
    (rr := 2) (rm := IndexedWrapFixture.recMember)
    .empty rfl ctorClasses rfl IndexedWrapFixture.membersT
    (NormRole.envCtx IndexedWrapFixture.envWfT)
    (EvalRole.envPlan IndexedWrapFixture.envWfT)
    (fun _ _ => rfl) (faithful P) uniform_prop

theorem family_prefix_sound (P : Premises4) : ∀ τ n,
    EnvSound (model P) τ bound IndexedWrapFixture.famOnly n :=
  (PointwisePropPrefix.canonical_group_facts P bound (table P)
    (f := 0) (fm := IndexedWrapFixture.famMember)
    (ctors := [(1, IndexedWrapFixture.introMember)])
    (rr := 2) (rm := IndexedWrapFixture.recMember)
    .empty rfl ctorClasses rfl IndexedWrapFixture.membersT
    (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities IndexedWrapFixture.env)
    (PointwiseRole.arities_agree IndexedWrapFixture.env)
    (NormRole.envCtx IndexedWrapFixture.envWfT)
    (EvalRole.envPlan IndexedWrapFixture.envWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P) uniform_prop).rawEnv

theorem constructor_sound (P : Premises4) :
    MemberSound P (table P) bound 1 IndexedWrapFixture.introMember := by
  have h := IndexedPropCtor.member_sound P (table P) bound
    (f := 0) (fm := IndexedWrapFixture.famMember)
    (ctors := [(1, IndexedWrapFixture.introMember)])
    (rr := 2) (rm := IndexedWrapFixture.recMember)
    .empty rfl ctorClasses rfl IndexedWrapFixture.membersT
    (IndexedWrapFixture.indexed_bound bound) (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities IndexedWrapFixture.env)
    (PointwiseRole.arities_agree IndexedWrapFixture.env)
    (NormRole.envCtx IndexedWrapFixture.envWfT)
    (EvalRole.envPlan IndexedWrapFixture.envWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P) uniform_prop ctor
  change MemberSound P (table P) bound 1 (plan.node.a.constructors[ctor.val]) at h
  rw [(IndexedWrapFixture.constructor_info plan.node ctor).1] at h
  exact h

theorem recursor_sound (P : Premises4) :
    MemberSound P (table P) bound 2 IndexedWrapFixture.recMember :=
  IndexedPropRecMem.member_sound P (table P) bound
    (f := 0) (fm := IndexedWrapFixture.famMember)
    (ctors := [(1, IndexedWrapFixture.introMember)])
    (rr := 2) (rm := IndexedWrapFixture.recMember)
    .empty rfl ctorClasses rfl IndexedWrapFixture.membersT
    (IndexedWrapFixture.indexed_bound bound) (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities IndexedWrapFixture.env) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (NormRole.envCtx IndexedWrapFixture.envWfT)
    (EvalRole.envPlan IndexedWrapFixture.envWfT)
    (fun _ _ => rfl) (fun _ _ => rfl) (faithful P) uniform_prop (policy plan.node)

/-! ## Actual target syntax: two local index codes -/

noncomputable def context : LCtx := [.assumption (.sort .zero), .assumption (.sort .zero)]
noncomputable abbrev a : Expr Nat := .bvar 1
noncomputable abbrev b : Expr Nat := .bvar 0

noncomputable def wrapMotive : Expr Nat :=
  .lam (.sort .zero) (.lam (IndexedWrapFixture.famApp (.bvar 0)) (.sort .zero))

noncomputable def wrapMinor : Expr Nat := .lam (.sort .zero) (.bvar 0)

noncomputable def motiveBodyTyped (Γ : LCtx) : HasTyT extension 0 (.assumption (.sort .zero) :: Γ)
    (.lam (IndexedWrapFixture.famApp (.bvar 0)) (.sort .zero))
    (.pi (IndexedWrapFixture.famApp (.bvar 0)) (.sort (.succ .zero))) :=
  .lam _ _ .zero _ _
    (IndexedWrapFixture.famAppTyT rfl (.bvar 0) (.bvar _ 0 _ rfl))
    (.sort _ .zero)

noncomputable def motiveTyped (Γ : LCtx) : HasTyT extension 0 Γ wrapMotive
    (instantiateLevels [.succ .zero] IndexedWrapFixture.motiveTy) :=
  .lam Γ (.sort .zero) (.succ .zero) _ _ (.sort Γ .zero) (motiveBodyTyped Γ)

noncomputable def motiveBeta (Γ : LCtx) (p t : Expr Nat)
    (hp : HasTyT extension 0 Γ p (.sort .zero))
    (ht : HasTyT extension 0 Γ t (IndexedWrapFixture.famApp p)) :
    ConvT extension 0 Γ (.app (.app wrapMotive p) t) (.sort .zero)
      (.sort (.succ .zero)) := by
  have houter : ConvT extension 0 Γ (.app wrapMotive p)
      (.lam (IndexedWrapFixture.famApp p) (.sort .zero))
      (.pi (IndexedWrapFixture.famApp p) (.sort (.succ .zero))) :=
    .beta Γ (.sort .zero)
      (.lam (IndexedWrapFixture.famApp (.bvar 0)) (.sort .zero)) p
      (.pi (IndexedWrapFixture.famApp (.bvar 0)) (.sort (.succ .zero)))
      (.succ .zero) (.sort Γ .zero) (motiveBodyTyped Γ) hp
  have happ := ConvT.app Γ (.app wrapMotive p)
    (.lam (IndexedWrapFixture.famApp p) (.sort .zero)) t t
    (IndexedWrapFixture.famApp p) (.sort (.succ .zero)) houter (.refl Γ t _ ht)
  have hinner : ConvT extension 0 Γ
      (.app (.lam (IndexedWrapFixture.famApp p) (.sort .zero)) t)
      (.sort .zero) (.sort (.succ .zero)) :=
    .beta Γ (IndexedWrapFixture.famApp p) (.sort .zero) t
      (.sort (.succ .zero)) .zero (IndexedWrapFixture.famAppTyT rfl p hp)
      (.sort _ .zero) ht
  exact .trans Γ _ _ _ _ happ hinner

noncomputable def minorTyped (Γ : LCtx) : HasTyT extension 0 Γ wrapMinor
    (.pi (.sort .zero)
      (.app (.app wrapMotive (.bvar 0)) (IndexedWrapFixture.introApp (.bvar 0)))) :=
  .lam Γ (.sort .zero) (.succ .zero) _ _ (.sort Γ .zero)
    (.conv _ (.bvar 0) (.sort .zero) _ (.succ .zero) (.bvar _ 0 _ rfl)
      (.symm _ _ _ _ (motiveBeta _ (.bvar 0) (IndexedWrapFixture.introApp (.bvar 0))
        (.bvar _ 0 _ rfl)
        (IndexedWrapFixture.introAppTyT rfl (.bvar 0) (.bvar _ 0 _ rfl)))))

noncomputable def plainMinorTyped (Γ : LCtx) :
    HasTyT extension 0 Γ wrapMinor (.pi (.sort .zero) (.sort .zero)) :=
  .lam Γ (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
    (.sort Γ .zero) (.bvar _ 0 _ rfl)

noncomputable def aTyped : HasTyT extension 0 context a (.sort .zero) := .bvar context 1 _ rfl
noncomputable def bTyped : HasTyT extension 0 context b (.sort .zero) := .bvar context 0 _ rfl

noncomputable def aFamilyTyped : HasTyT extension 0 context
    (IndexedWrapFixture.famApp a) (.sort .zero) :=
  IndexedWrapFixture.famAppTyT rfl a aTyped

noncomputable def bFamilyTyped : HasTyT extension 0 context
    (IndexedWrapFixture.famApp b) (.sort .zero) :=
  IndexedWrapFixture.famAppTyT rfl b bTyped

noncomputable def indexConversion : ConvT extension 0 context
    (IndexedWrapFixture.famApp a) (IndexedWrapFixture.famApp b) (.sort .zero) :=
  PropIndexConversionGeneric.propositionConversion lookups context _ _ aFamilyTyped bFamilyTyped

noncomputable def majorTyped : HasTyT extension 0 context (IndexedWrapFixture.introApp a)
    (IndexedWrapFixture.famApp b) :=
  .conv context _ _ _ .zero (IndexedWrapFixture.introAppTyT rfl a aTyped) indexConversion

noncomputable def witness : IotaWitness extension where
  recRef := 2
  ctorRef := 1
  ls := [.succ .zero]
  lsC := []
  recMember := IndexedWrapFixture.recMember
  ctorMember := IndexedWrapFixture.introMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [wrapMotive, wrapMinor, b]
  fields := [a]
  ctorParams := []
  kinds := [.plain]
  minor := wrapMinor
  hlen := rfl
  familyRef := 0
  famMember := IndexedWrapFixture.famMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort .zero]
  ctorResult := IndexedWrapFixture.famApp (.bvar 0)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [IndexedWrapFixture.motiveTy, IndexedWrapFixture.minorTy,
    .sort .zero, IndexedWrapFixture.famApp (.bvar 0)]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := IndexedWrapFixture.introMember.mtype
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

noncomputable def recTyped : HasTyT extension 0 context (.const 2 [.succ .zero])
    (instantiateLevels [.succ .zero] IndexedWrapFixture.recType) :=
  .const context 2 [.succ .zero] IndexedWrapFixture.recMember rfl rfl rfl

noncomputable def partialTyped : HasTyT extension 0 context
    (.app (.app (.const 2 [.succ .zero]) wrapMotive) wrapMinor)
    (.pi (.sort .zero) (.pi (IndexedWrapFixture.famApp (.bvar 0))
      (.app (.app wrapMotive (.bvar 1)) (.bvar 0)))) :=
  .app context _ wrapMinor _ _
    (.app context _ wrapMotive _ _ recTyped (motiveTyped context)) (minorTyped context)

noncomputable def leftBeforeCast : HasTyT extension 0 context (iotaLhsOf witness)
    (.app (.app wrapMotive b) (IndexedWrapFixture.introApp a)) :=
  .app context _ (IndexedWrapFixture.introApp a) _ _
    (.app context _ b _ _ partialTyped bTyped) majorTyped

noncomputable def lhsTyped : HasTyT extension 0 context (iotaLhsOf witness) (.sort .zero) :=
  .conv context _ _ (.sort .zero) (.succ .zero) leftBeforeCast
    (motiveBeta context b (IndexedWrapFixture.introApp a) bTyped majorTyped)

noncomputable def rhsTyped : HasTyT extension 0 context (iotaRhsOf witness) (.sort .zero) :=
  .app context wrapMinor a (.sort .zero) (.sort .zero) (plainMinorTyped context) aTyped

private theorem nil_levels (r : Nat) : LevelsOK σ (bound r) [] :=
  fun l hl => (List.not_mem_nil l hl).elim

theorem motiveBody_bound (Γ : LCtx) : LOKt σ 4 bound (motiveBodyTyped Γ) :=
  ⟨⟨nil_levels 0, True.intro⟩, by change 1 ≤ 4; decide⟩

theorem motive_bound (Γ : LCtx) : LOKt σ 4 bound (motiveTyped Γ) :=
  ⟨by change 1 ≤ 4; decide, motiveBody_bound Γ⟩

theorem motiveBeta_bound (Γ : LCtx) (p t : Expr Nat)
    (hp : HasTyT extension 0 Γ p (.sort .zero))
    (ht : HasTyT extension 0 Γ t (IndexedWrapFixture.famApp p))
    (lp : LOKt σ 4 bound hp) (lt : LOKt σ 4 bound ht) :
    LOKc σ 4 bound (motiveBeta Γ p t hp ht) :=
  ⟨⟨⟨by change 1 ≤ 4; decide, motiveBody_bound Γ, lp⟩, lt⟩,
    ⟨⟨nil_levels 0, lp⟩, by change 1 ≤ 4; decide, lt⟩⟩

theorem minor_bound (Γ : LCtx) : LOKt σ 4 bound (minorTyped Γ) :=
  ⟨by change 1 ≤ 4; decide,
    ⟨True.intro, motiveBeta_bound (.assumption (.sort .zero) :: Γ) _ _
      (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)
      (IndexedWrapFixture.introAppTyT (E := extension) (n := 0)
        (Γ := .assumption (.sort .zero) :: Γ) rfl (.bvar 0)
        (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl))
      True.intro ⟨nil_levels 1, True.intro⟩⟩⟩

theorem indexConversion_bound : LOKc σ 4 bound indexConversion :=
  PropIndexConversionGeneric.propositionConversion_bound lookups σ bound context _ _
    aFamilyTyped bFamilyTyped ⟨nil_levels 0, True.intro⟩ ⟨nil_levels 0, True.intro⟩

theorem major_bound : LOKt σ 4 bound majorTyped :=
  ⟨⟨nil_levels 1, True.intro⟩, indexConversion_bound⟩

theorem rec_levels : LevelsOK σ (bound 2) [.succ .zero] := by
  intro l hl
  cases List.mem_singleton.mp hl
  exact Nat.le_refl 1

theorem partial_bound : LOKt σ 4 bound partialTyped :=
  ⟨⟨rec_levels, motive_bound context⟩, minor_bound context⟩

theorem lhs_bound : LOKt σ 4 bound lhsTyped :=
  ⟨⟨⟨partial_bound, True.intro⟩, major_bound⟩,
    motiveBeta_bound context b (IndexedWrapFixture.introApp a)
      bTyped majorTyped True.intro major_bound⟩

theorem rhs_bound : LOKt σ 4 bound rhsTyped :=
  ⟨⟨by change 1 ≤ 4; decide, True.intro⟩, True.intro⟩

/-! Further certificates below use the exact same P and the actual
faithful extension table. No admission of `extension` is introduced. -/

private theorem app_hsound (P : Premises4) {Γ : LCtx} {f x A B : Expr Nat}
    (hf : HasTyT extension 0 Γ f (.pi A B)) (hx : HasTyT extension 0 Γ x A)
    (sf : HSoundT (model P) σ hf) (sx : HSoundT (model P) σ hx) :
    HSoundT (model P) σ (.app Γ f x A B hf hx) := by
  refine ⟨?_, sf, sx⟩
  intro ρ hρ
  change fapp (den (model P) σ ρ f) (den (model P) σ ρ x) ∈
    Ed (model P) (den (model P) σ ρ (instantiate0 x B))
  rw [den_inst0]
  exact app_mem (model P) (den_resp (model P) σ ρ B) (sf.root ρ hρ) (sx.root ρ hρ)

private theorem conv_hsound (P : Premises4) {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (ht : HasTyT extension 0 Γ e A) (hc : ConvT extension 0 Γ A B (.sort u))
    (st : HSoundT (model P) σ ht) (sc : HSoundC (model P) σ hc) :
    HSoundT (model P) σ (.conv Γ e A B u ht hc) :=
  ⟨fun ρ hρ => mem_congr_right (ed_congr (model P) (sc.root ρ hρ).1)
    (st.root ρ hρ), st, sc⟩

private theorem lam_hsound (P : Premises4) {Γ : LCtx} {A body B : Expr Nat} {u : Level}
    (hA : HasTyT extension 0 Γ A (.sort u))
    (hb : HasTyT extension 0 (.assumption A :: Γ) body B)
    (sA : HSoundT (model P) σ hA) (sb : HSoundT (model P) σ hb) :
    HSoundT (model P) σ (.lam Γ A u body B hA hb) :=
  ⟨fun ρ hρ => lam_mem (model P) (den_resp (model P) σ ρ body)
    (den_resp (model P) σ ρ B)
    (fun x hx => sb.root (vcons x ρ) (fits_cons_assumption hρ hx)), sA, sb⟩

private theorem bvar_hsound (P : Premises4) (Γ : LCtx) (i : Nat) (A : Expr Nat)
    (hi : lookupType Γ i = some A) :
    HSoundT (model P) σ (HasTyT.bvar (E := extension) (n := 0) Γ i A hi) :=
  fun ρ hρ => fits_lookupType (model P) σ Γ ρ hρ i A hi

private theorem sort_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ (HasTyT.sort (E := extension) (n := 0) Γ .zero) :=
  fun _ _ => sort_mem (P.good _ rfl) (by decide : 1 ≤ 4)

private theorem refl_hsound (P : Premises4) {Γ : LCtx} {e A : Expr Nat}
    (h : HasTyT extension 0 Γ e A) (s : HSoundT (model P) σ h) :
    HSoundC (model P) σ (.refl Γ e A h) :=
  ⟨fun ρ hρ => ⟨Equiv.rfl, s.root ρ hρ⟩, s⟩

private theorem symm_hsound (P : Premises4) {Γ : LCtx} {e f A : Expr Nat}
    (h : ConvT extension 0 Γ e f A) (s : HSoundC (model P) σ h) :
    HSoundC (model P) σ (.symm Γ e f A h) :=
  ⟨fun ρ hρ => ⟨(s.root ρ hρ).1.symm,
    mem_congr_left (s.root ρ hρ).1 (s.root ρ hρ).2⟩, s⟩

private theorem trans_hsound (P : Premises4) {Γ : LCtx} {e f g A : Expr Nat}
    (h1 : ConvT extension 0 Γ e f A) (h2 : ConvT extension 0 Γ f g A)
    (s1 : HSoundC (model P) σ h1) (s2 : HSoundC (model P) σ h2) :
    HSoundC (model P) σ (.trans Γ e f g A h1 h2) :=
  ⟨fun ρ hρ => ⟨(s1.root ρ hρ).1.trans (s2.root ρ hρ).1,
    (s1.root ρ hρ).2⟩, s1, s2⟩

private theorem appConv_hsound (P : Premises4) {Γ : LCtx} {f g x y A B : Expr Nat}
    (h1 : ConvT extension 0 Γ f g (.pi A B)) (h2 : ConvT extension 0 Γ x y A)
    (s1 : HSoundC (model P) σ h1) (s2 : HSoundC (model P) σ h2) :
    HSoundC (model P) σ (.app Γ f g x y A B h1 h2) := by
  refine ⟨?_, s1, s2⟩
  intro ρ hρ
  refine ⟨fapp_congr (s1.root ρ hρ).1 (s2.root ρ hρ).1, ?_⟩
  change fapp (den (model P) σ ρ f) (den (model P) σ ρ x) ∈
    Ed (model P) (den (model P) σ ρ (instantiate0 x B))
  rw [den_inst0]
  exact app_mem (model P) (den_resp (model P) σ ρ B)
    (s1.root ρ hρ).2 (s2.root ρ hρ).2

private theorem tyConv_hsound (P : Premises4) {Γ : LCtx} {e f A A' : Expr Nat} {u : Level}
    (h : ConvT extension 0 Γ e f A) (hA : ConvT extension 0 Γ A A' (.sort u))
    (s : HSoundC (model P) σ h) (sA : HSoundC (model P) σ hA) :
    HSoundC (model P) σ (.tyConv Γ e f A A' u h hA) :=
  ⟨fun ρ hρ => ⟨(s.root ρ hρ).1,
    mem_congr_right (ed_congr (model P) (sA.root ρ hρ).1) (s.root ρ hρ).2⟩, s, sA⟩

private theorem beta_hsound (P : Premises4) {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : HasTyT extension 0 Γ A (.sort u))
    (hb : HasTyT extension 0 (.assumption A :: Γ) body B)
    (ha : HasTyT extension 0 Γ arg A)
    (sA : HSoundT (model P) σ hA) (sb : HSoundT (model P) σ hb)
    (sa : HSoundT (model P) σ ha) :
    HSoundC (model P) σ (.beta Γ A body arg B u hA hb ha) := by
  refine ⟨?_, sA, sb, sa⟩
  intro ρ hρ
  have hx := sa.root ρ hρ
  have hy := sb.root (vcons (den (model P) σ ρ arg) ρ) (fits_cons_assumption hρ hx)
  have he : Equiv (den (model P) σ ρ (.app (.lam A body) arg))
      (den (model P) σ ρ (instantiate0 arg body)) := by
    rw [den_inst0]
    exact beta_val (model P) (den_resp (model P) σ ρ body) hx
  refine ⟨he, mem_congr_left he.symm ?_⟩
  rw [den_inst0, den_inst0]
  exact hy

theorem family_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ
      (HasTyT.const (E := extension) (n := 0) Γ 0 []
        IndexedWrapFixture.famMember rfl rfl rfl) :=
  fun ρ hρ => (family_prefix_sound P σ 0).const Γ 0 []
    IndexedWrapFixture.famMember ρ rfl rfl (nil_levels 0) hρ

theorem intro_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ
      (HasTyT.const (E := extension) (n := 0) Γ 1 []
        IndexedWrapFixture.introMember rfl rfl rfl) :=
  fun ρ _ => (constructor_sound P σ [] ρ rfl (nil_levels 1)).1

theorem familyApp_hsound (P : Premises4) (Γ : LCtx) (p : Expr Nat)
    (hp : HasTyT extension 0 Γ p (.sort .zero)) (sp : HSoundT (model P) σ hp) :
    HSoundT (model P) σ (IndexedWrapFixture.famAppTyT rfl p hp) :=
  app_hsound P _ _ (family_hsound P Γ) sp

theorem introApp_hsound (P : Premises4) (Γ : LCtx) (p : Expr Nat)
    (hp : HasTyT extension 0 Γ p (.sort .zero)) (sp : HSoundT (model P) σ hp) :
    HSoundT (model P) σ (IndexedWrapFixture.introAppTyT rfl p hp) :=
  app_hsound P _ _ (intro_hsound P Γ) sp

theorem motiveBody_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ (motiveBodyTyped Γ) :=
  lam_hsound P _ _
    (familyApp_hsound P (.assumption (.sort .zero) :: Γ) (.bvar 0)
      (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)
      (bvar_hsound P (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl))
    (sort_hsound P _)

theorem motive_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ (motiveTyped Γ) :=
  lam_hsound P _ _ (sort_hsound P Γ) (motiveBody_hsound P Γ)

theorem motiveBeta_hsound (P : Premises4) (Γ : LCtx) (p t : Expr Nat)
    (hp : HasTyT extension 0 Γ p (.sort .zero))
    (ht : HasTyT extension 0 Γ t (IndexedWrapFixture.famApp p))
    (sp : HSoundT (model P) σ hp) (st : HSoundT (model P) σ ht) :
    HSoundC (model P) σ (motiveBeta Γ p t hp ht) := by
  dsimp only [motiveBeta]
  apply trans_hsound
  · apply appConv_hsound
    · exact beta_hsound P _ _ _ (sort_hsound P Γ) (motiveBody_hsound P Γ) sp
    · exact refl_hsound P ht st
  · exact beta_hsound P _ _ _ (familyApp_hsound P Γ p hp sp) (sort_hsound P _) st

theorem minor_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ (minorTyped Γ) :=
  lam_hsound P _ _ (sort_hsound P Γ)
    (conv_hsound P _ _
      (bvar_hsound P (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)
      (symm_hsound P _ (motiveBeta_hsound P (.assumption (.sort .zero) :: Γ) (.bvar 0)
        (IndexedWrapFixture.introApp (.bvar 0))
        (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)
        (IndexedWrapFixture.introAppTyT rfl (.bvar 0)
          (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl))
        (bvar_hsound P (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)
        (introApp_hsound P (.assumption (.sort .zero) :: Γ) (.bvar 0)
          (.bvar (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)
          (bvar_hsound P (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)))))

theorem plainMinor_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ (plainMinorTyped Γ) :=
  lam_hsound P _ _ (sort_hsound P Γ)
    (bvar_hsound P (.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)

/-- Inhabited Prop codes agree; this does not compare their data indices. -/
theorem inhabited_prop_codes (M : Interp.{4}) {X Y x y : PSet.{4}}
    (hX : X ∈ U W4 0) (hY : Y ∈ U W4 0)
    (hx : x ∈ Ed M X) (hy : y ∈ Ed M Y) : Equiv X Y := by
  obtain ⟨S, hS, hXS⟩ := mem_sImage_tyv.mp hX
  obtain ⟨T, hT, hYT⟩ := mem_sImage_tyv.mp hY
  have hSp := mem_propSets.mp hS
  have hTp := mem_propSets.mp hT
  have hxS := mem_congr_right ((ed_congr M hXS).trans (ed_tyv M (Or.inl hSp))) hx
  have hyT := mem_congr_right ((ed_congr M hYT).trans (ed_tyv M (Or.inl hTp))) hy
  have hST : Equiv S T := by
    apply ext
    intro z
    constructor
    · intro hz
      exact mem_congr_left ((hTp y hyT).trans (hSp z hz).symm) hyT
    · intro hz
      exact mem_congr_left ((hSp x hxS).trans (hTp z hz).symm) hxS
  exact hXS.trans ((tyv_congr hST).trans hYT.symm)

theorem a_hsound (P : Premises4) : HSoundT (model P) σ aTyped :=
  bvar_hsound P context 1 _ rfl

theorem b_hsound (P : Premises4) : HSoundT (model P) σ bTyped :=
  bvar_hsound P context 0 _ rfl

theorem family_code_eq (P : Premises4) (ρ : Nat → PSet.{4})
    (hρ : Fits (model P) σ context ρ) :
    Equiv (den (model P) σ ρ (IndexedWrapFixture.famApp a))
      (den (model P) σ ρ (IndexedWrapFixture.famApp b)) :=
  inhabited_prop_codes (model P)
    (mem_congr_right (ed_tyv (model P) (U4_dich 0))
      ((familyApp_hsound P context a aTyped (a_hsound P)).root ρ hρ))
    (mem_congr_right (ed_tyv (model P) (U4_dich 0))
      ((familyApp_hsound P context b bTyped (b_hsound P)).root ρ hρ))
    ((introApp_hsound P context a aTyped (a_hsound P)).root ρ hρ)
    ((introApp_hsound P context b bTyped (b_hsound P)).root ρ hρ)

/-! ## The gadget is hereditarily sound at these equal family-code minors -/

theorem bool_proof (P : Premises4) : pempty ∈ Ed (model P) (table P 3 []) :=
  mem_congr_right (ed_tyv (model P) (dich_tv True)).symm
    (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)

theorem bool_erased (P : Premises4) {z : PSet.{4}}
    (hz : z ∈ Ed (model P) (table P 3 [])) : Equiv z pempty :=
  (mem_tv.mp (mem_congr_right (ed_tyv (model P) (dich_tv True)) hz)).2

theorem gadget_rec_mem (P : Premises4) (ρ : Nat → PSet.{4}) :
    PropIndexConversionSemantics.recValue P ∈
      Ed (model P) (den (model P) σ ρ PropIndexConversionAttack.recType) := by
  change piLam (model P) σ (fun η => η 2) ρ PropIndexConversionAttack.recType ∈ _
  apply piLam_mem (model P) σ (fun _ _ h => h 2) PropIndexConversionAttack.recType ρ
  intro mo hmo x hx y hy z hz
  change x ∈ Ed (model P) (fapp mo z)
  change x ∈ Ed (model P) (fapp mo pempty) at hx
  exact mem_congr_right (ed_congr (model P)
    (fapp_congr Equiv.rfl (bool_erased P hz).symm)) hx

theorem gadget_bool_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ (PropIndexConversionGeneric.boolTyped (n := 0) lookups Γ) :=
  fun _ _ => (PropEvalSafeIndex.true_fits P σ).1

theorem gadget_first_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ (PropIndexConversionGeneric.firstTyped (n := 0) lookups Γ) :=
  fun _ _ => bool_proof P

theorem gadget_second_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ (PropIndexConversionGeneric.secondTyped (n := 0) lookups Γ) :=
  fun _ _ => bool_proof P

theorem gadget_motive_hsound (P : Premises4) (Γ : LCtx) :
    HSoundT (model P) σ (PropIndexConversionGeneric.motiveTyped (n := 0) lookups Γ) :=
  lam_hsound P _ _ (gadget_bool_hsound P Γ) (sort_hsound P _)

theorem gadget_betaFirst_hsound (P : Premises4) (Γ : LCtx) :
    HSoundC (model P) σ (PropIndexConversionGeneric.betaFirst (n := 0) lookups Γ) :=
  beta_hsound P _ _ _ (gadget_bool_hsound P Γ) (sort_hsound P _)
    (gadget_first_hsound P Γ)

theorem gadget_betaSecond_hsound (P : Premises4) (Γ : LCtx) :
    HSoundC (model P) σ (PropIndexConversionGeneric.betaSecond (n := 0) lookups Γ) :=
  beta_hsound P _ _ _ (gadget_bool_hsound P Γ) (sort_hsound P _)
    (gadget_second_hsound P Γ)

theorem gadget_partial_hsound (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) σ hU) (sV : HSoundT (model P) σ hV) :
    HSoundT (model P) σ (PropIndexConversionGeneric.partialTyped lookups Γ U V hU hV) := by
  dsimp only [PropIndexConversionGeneric.partialTyped]
  apply app_hsound
  · apply app_hsound
    · apply app_hsound
      · intro ρ _
        exact gadget_rec_mem P ρ
      · exact gadget_motive_hsound P Γ
    · exact conv_hsound P hU _ sU (symm_hsound P _ (gadget_betaFirst_hsound P Γ))
  · exact conv_hsound P hV _ sV (symm_hsound P _ (gadget_betaSecond_hsound P Γ))

theorem gadget_firstLhs_hsound (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) σ hU) (sV : HSoundT (model P) σ hV) :
    HSoundT (model P) σ (PropIndexConversionGeneric.firstLhsTyped lookups Γ U V hU hV) :=
  conv_hsound P _ _
    (app_hsound P _ _ (gadget_partial_hsound P Γ U V hU hV sU sV)
      (gadget_first_hsound P Γ)) (gadget_betaFirst_hsound P Γ)

theorem gadget_secondLhs_hsound (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) σ hU) (sV : HSoundT (model P) σ hV) :
    HSoundT (model P) σ (PropIndexConversionGeneric.secondLhsTyped lookups Γ U V hU hV) :=
  conv_hsound P _ _
    (app_hsound P _ _ (gadget_partial_hsound P Γ U V hU hV sU sV)
      (gadget_second_hsound P Γ)) (gadget_betaSecond_hsound P Γ)

theorem gadget_application_first (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) σ hU) (sV : HSoundT (model P) σ hV)
    (ρ : Nat → PSet.{4}) (hρ : Fits (model P) σ Γ ρ) :
    Equiv (fapps (PropIndexConversionSemantics.recValue P)
      [den (model P) σ ρ PropIndexConversionAttack.motive,
        den (model P) σ ρ U, den (model P) σ ρ V, pempty])
      (den (model P) σ ρ U) := by
  have hx : den (model P) σ ρ U ∈ Ed (model P)
      (fapp (den (model P) σ ρ PropIndexConversionAttack.motive) pempty) :=
    mem_congr_right (ed_congr (model P)
      ((gadget_betaFirst_hsound P Γ).root ρ hρ).1).symm (sU.root ρ hρ)
  have hy : den (model P) σ ρ V ∈ Ed (model P)
      (fapp (den (model P) σ ρ PropIndexConversionAttack.motive) pempty) :=
    mem_congr_right (ed_congr (model P)
      ((gadget_betaSecond_hsound P Γ).root ρ hρ).1).symm (sV.root ρ hρ)
  have hfit : TelFits (model P) σ PropIndexConversionSemantics.domains ρ0
      [den (model P) σ ρ PropIndexConversionAttack.motive,
        den (model P) σ ρ U, den (model P) σ ρ V, pempty] :=
    ⟨(gadget_motive_hsound P Γ).root ρ hρ, hx, hy, bool_proof P, True.intro⟩
  exact fapps_piLam (model P) σ (fun _ _ h => h 2)
    (.app (.bvar 3) (.bvar 0)) PropIndexConversionSemantics.domains ρ0 _ hfit

theorem gadget_conversion_hsound (P : Premises4) (Γ : LCtx) (U V : Expr Nat)
    (hU : HasTyT extension 0 Γ U (.sort .zero)) (hV : HasTyT extension 0 Γ V (.sort .zero))
    (sU : HSoundT (model P) σ hU) (sV : HSoundT (model P) σ hV)
    (hUV : ∀ ρ, Fits (model P) σ Γ ρ →
      Equiv (den (model P) σ ρ U) (den (model P) σ ρ V)) :
    HSoundC (model P) σ
      (PropIndexConversionGeneric.propositionConversion lookups Γ U V hU hV) := by
  dsimp only [PropIndexConversionGeneric.propositionConversion]
  apply trans_hsound
  · apply symm_hsound
    exact ⟨fun ρ hρ => ⟨gadget_application_first P Γ U V hU hV sU sV ρ hρ,
      (gadget_firstLhs_hsound P Γ U V hU hV sU sV).root ρ hρ⟩,
      gadget_firstLhs_hsound P Γ U V hU hV sU sV, sU⟩
  · apply trans_hsound
    · apply tyConv_hsound
      · apply appConv_hsound
        · exact refl_hsound P _ (gadget_partial_hsound P Γ U V hU hV sU sV)
        · exact ⟨fun _ _ => ⟨Equiv.rfl, bool_proof P⟩,
            gadget_bool_hsound P Γ, gadget_first_hsound P Γ, gadget_second_hsound P Γ⟩
      · exact gadget_betaFirst_hsound P Γ
    · exact ⟨fun ρ hρ =>
        ⟨(gadget_application_first P Γ U V hU hV sU sV ρ hρ).trans (hUV ρ hρ),
          (gadget_secondLhs_hsound P Γ U V hU hV sU sV).root ρ hρ⟩,
        gadget_secondLhs_hsound P Γ U V hU hV sU sV, sV⟩

/-- The family conversion used by the actual major is hereditary sound,
even though its data indices have not been identified. -/
theorem indexConversion_hsound (P : Premises4) : HSoundC (model P) σ indexConversion :=
  gadget_conversion_hsound P context _ _ aFamilyTyped bFamilyTyped
    (familyApp_hsound P context a aTyped (a_hsound P))
    (familyApp_hsound P context b bTyped (b_hsound P)) (family_code_eq P)

theorem major_hsound (P : Premises4) : HSoundT (model P) σ majorTyped :=
  conv_hsound P _ _ (introApp_hsound P context a aTyped (a_hsound P))
    (indexConversion_hsound P)

theorem rec_hsound (P : Premises4) : HSoundT (model P) σ recTyped :=
  fun ρ _ => (recursor_sound P σ [.succ .zero] ρ rfl rec_levels).1

theorem partial_hsound (P : Premises4) : HSoundT (model P) σ partialTyped :=
  app_hsound P _ _ (app_hsound P _ _ (rec_hsound P) (motive_hsound P context))
    (minor_hsound P context)

theorem lhs_hsound (P : Premises4) : HSoundT (model P) σ lhsTyped :=
  conv_hsound P _ _
    (app_hsound P _ _ (app_hsound P _ _ (partial_hsound P) (b_hsound P))
      (major_hsound P))
    (motiveBeta_hsound P context b (IndexedWrapFixture.introApp a)
      bTyped majorTyped (b_hsound P) (major_hsound P))

theorem rhs_hsound (P : Premises4) : HSoundT (model P) σ rhsTyped :=
  app_hsound P _ _ (plainMinor_hsound P context) (a_hsound P)

noncomputable def values : Nat → PSet.{4} := vcons trueCode (vcons falseCode ρ0)

theorem values_fit (P : Premises4) : Fits (model P) σ context values :=
  ⟨⟨True.intro, (PropEvalSafeIndex.false_fits P σ).1⟩,
    (PropEvalSafeIndex.true_fits P σ).1⟩

theorem left_root_mem (P : Premises4) :
    den (model P) σ values (iotaLhsOf witness) ∈
      Ed (model P) (den (model P) σ values (.sort .zero)) :=
  (lhs_hsound P).root values (values_fit P)

theorem right_root_mem (P : Premises4) :
    den (model P) σ values (iotaRhsOf witness) ∈
      Ed (model P) (den (model P) σ values (.sort .zero)) :=
  (rhs_hsound P).root values (values_fit P)

theorem right_value (P : Premises4) :
    Equiv (den (model P) σ values (iotaRhsOf witness)) falseCode :=
  beta_val (model P) (fun _ _ h => h)
    ((a_hsound P).root values (values_fit P))

theorem good_and_lhs_bound (P : Premises4) :
    ∃ (N : Nat) (Lv : Nat → PSet.{4} → Prop),
      Good (model P) N Lv ∧ LOKt σ N bound lhsTyped :=
  ⟨4, _, P.good _ rfl, lhs_bound⟩

theorem left_nonempty (P : Premises4) :
    ¬ Equiv (den (model P) σ values (iotaLhsOf witness)) pempty := by
  intro he
  have hm := mem_congr_right (ed_tyv (model P) (U4_dich 0)) (left_root_mem P)
  exact pempty_not_mem_U4 P 0 (mem_congr_left he hm)

/-- The complete original recursor telescope is recovered from this
actual nonempty application, without a postulated key comparison. -/
theorem recovered_arguments (P : Premises4) : ∃ ps mo ms is,
    IndexedPropPlainIota.Arguments (model P) plan witness σ values ctor ps mo ms is :=
  IndexedPropPlainIota.arguments_of_typed_nonempty P (table P) plan
    IndexedWrapFixture.famMember [(1, IndexedWrapFixture.introMember)]
    .empty IndexedWrapFixture.membersT (recursor_value P)
    (noFun plan.node) (fields_free plan.node) witness rfl rfl ctor rfl
    (IndexedWrapFixture.constructor_info plan.node ctor).1.symm
    σ values rhsTyped (rhs_hsound P) (values_fit P)
    (left_root_mem P) (right_root_mem P) (left_nonempty P)

private theorem supplied_index {u v w mo : PSet.{4}} {ms is : List PSet.{4}}
    (hlen : ms.length = 1) (hs : [u, v, w] = mo :: (ms ++ is)) : is = [w] := by
  cases ms with
  | nil => exact False.elim (Nat.noConfusion hlen)
  | cons x xs =>
      have hz : xs.length = 0 := Nat.succ.inj hlen
      have hx : xs = [] := List.eq_nil_of_length_eq_zero hz
      subst xs
      exact (congrArg (fun zs : List PSet.{4} => zs.tail.tail) hs).symm

/-- The endpoint computes at the supplied index b. The fitting tuple
used for this equation is [b]; the redex's constructor field remains a. -/
theorem left_value (P : Premises4) :
    Equiv (den (model P) σ values (iotaLhsOf witness)) trueCode := by
  obtain ⟨ps, mo, ms, is, hA⟩ := recovered_arguments P
  have hps : ps = [] := List.eq_nil_of_length_eq_zero (by
    rw [hA.parameters_length, (IndexedWrapFixture.family_info plan.node).1]
    rfl)
  have hms : ms.length = 1 := hA.minors_length.trans count
  have hs := hA.split
  rw [hps] at hs
  have his : is = [trueCode] := supplied_index hms hs
  have hresult : IndexedPropEval.fieldResultIndices (model P) σ ps [trueCode]
      (plan.node.a.constructorViews ctor).resultIndices = is := by
    rw [hps, his, (IndexedWrapFixture.constructor_view plan.node ctor).2.2,
      IndexedPropEval.fieldResultIndices]
    rfl
  have hxs : TelFits (model P) σ (plan.node.a.constructorViews ctor).fields
      (push ps ρ0) [trueCode] := by
    rw [hps, (IndexedWrapFixture.constructor_view plan.node ctor).2.1]
    exact ⟨(PropEvalSafeIndex.true_fits P σ).1, True.intro⟩
  have hifs : TelFits (model P) σ plan.node.a.family.indices (push ps ρ0)
      (IndexedPropEval.fieldResultIndices (model P) σ ps [trueCode]
        (plan.node.a.constructorViews ctor).resultIndices) := by
    rw [hresult]
    exact hA.indices_fit
  have hmajor : den (model P) σ values (ctorMajor witness) ∈
      Ed (model P) (fapps (table P plan.node.a.family.ref
        ((canonL plan.node.a.family.member.arity).map (evalTotal σ)))
        (ps ++ IndexedPropEval.fieldResultIndices (model P) σ ps [trueCode]
          (plan.node.a.constructorViews ctor).resultIndices)) := by
    rw [hresult]
    exact hA.major_fit
  have he := IndexedPropEval.endValue_plain_at_fields P (table P) bound plan
    IndexedWrapFixture.famMember [(1, IndexedWrapFixture.introMember)]
    .empty rfl ctorClasses rfl IndexedWrapFixture.membersT
    (IndexedWrapFixture.indexed_bound bound) (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities IndexedWrapFixture.env) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (family_equation P) [1]
    (fun u hu => by cases List.mem_singleton.mp hu; exact Nat.le_refl 1)
    (uniform_prop σ) (policy plan.node) (noFun plan.node) (fields_free plan.node)
    ps mo ms (den (model P) σ values (ctorMajor witness)) hA.minors_length
    hA.parameters_fit hA.motive_fit hA.minors_fit ctor [trueCode] hxs hifs hmajor
  rw [hresult, hA.minor_read] at he
  have hm : Equiv (fapps (den (model P) σ values wrapMinor) [trueCode]) trueCode :=
    beta_val (model P) (fun _ _ h => h)
      ((b_hsound P).root values (values_fit P))
  exact hA.lhs_endpoint.trans (he.trans hm)

/-- All literal premises of the current arbitrary-extension IotaAt are
present. Its claimed equality contradicts the two actual data values. -/
theorem not_iota_at (P : Premises4) :
    ¬ IotaAt P (table P) bound extension 2 := by
  intro hi
  have he := hi extension (fun _ _ h => h) witness rfl σ 0 context (.sort .zero)
    values lhsTyped (lhs_hsound P) (good_and_lhs_bound P) rhsTyped (rhs_hsound P)
    rec_levels (values_fit P) (left_root_mem P) (right_root_mem P)
  exact PropEvalSafeIndex.distinct_codes P
    ((right_value P).symm.trans (he.symm.trans (left_value P)))

/-- This concerns the invariant with the current arbitrary-extension
legacy IotaAt. It does not refute the previously produced PendA-only
package, whose legacy witness space is empty. -/
theorem not_gInv (P : Premises4) :
    ¬ PointwiseRole.GInv P bound IndexedWrapFixture.envWfT := by
  intro h
  have hh := h (PointwiseRole.arities IndexedWrapFixture.env)
    (PointwiseRole.arities_agree IndexedWrapFixture.env)
    (NormRole.envCtx IndexedWrapFixture.envWfT) (fun _ _ => rfl)
    (EvalRole.envPlan IndexedWrapFixture.envWfT) (fun _ _ => rfl)
    (table P) (faithful P)
  exact not_iota_at P (hh.2 extension extends_wrap 2 IndexedWrapFixture.recMember rfl rfl)

/-- Same-P composition exposes every semantic hypothesis of the attacked
redex together with its different result values and actual target admission. -/
structure Witness (P : Premises4) : Prop where
  admitted : Nonempty (EnvWfT IndexedWrapFixture.env)
  indexed_bound : IndexedFieldBounds.BoundGIndexed bound IndexedWrapFixture.envWfT
  table_faithful : EvalRole.Faithful
    (PointwiseRole.familyValue (PointwiseRole.arities IndexedWrapFixture.env))
    P (table P) (NormRole.envCtx IndexedWrapFixture.envWfT)
    (EvalRole.envPlan IndexedWrapFixture.envWfT) IndexedWrapFixture.env
  left_hereditary : HSoundT (model P) σ lhsTyped
  right_hereditary : HSoundT (model P) σ rhsTyped
  left_bounded : ∃ (N : Nat) (Lv : Nat → PSet.{4} → Prop),
    Good (model P) N Lv ∧ LOKt σ N bound lhsTyped
  recursor_bounded : LevelsOK σ (bound 2) witness.ls
  context_fits : Fits (model P) σ context values
  left_member : den (model P) σ values (iotaLhsOf witness) ∈
    Ed (model P) (den (model P) σ values (.sort .zero))
  right_member : den (model P) σ values (iotaRhsOf witness) ∈
    Ed (model P) (den (model P) σ values (.sort .zero))
  left_result : Equiv (den (model P) σ values (iotaLhsOf witness)) trueCode
  right_result : Equiv (den (model P) σ values (iotaRhsOf witness)) falseCode
  refutation : ¬ IotaAt P (table P) bound extension 2

theorem component_witness (P : Premises4) : Witness P :=
  ⟨⟨IndexedWrapFixture.envWfT⟩, IndexedWrapFixture.indexed_bound bound, faithful P,
    lhs_hsound P, rhs_hsound P, good_and_lhs_bound P, rec_levels, values_fit P,
    left_root_mem P, right_root_mem P, left_value P, right_value P, not_iota_at P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) := fun h => h (component_witness P) P

end Rcic.F3.PSet.IndexedWrapIotaAttack

#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.faithful
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.family_prefix_sound
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.constructor_sound
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.recursor_sound
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.witness
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.lhsTyped
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.lhs_bound
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.rhsTyped
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.family_code_eq
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.indexConversion_hsound
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.lhs_hsound
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.rhs_hsound
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.values_fit
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.right_value
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.left_value
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.not_iota_at
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.not_gInv
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.component_witness
#print axioms Rcic.F3.PSet.IndexedWrapIotaAttack.component_nonrefutable
