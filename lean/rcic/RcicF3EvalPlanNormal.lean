import rcic.RcicF3EvalRoleDelta
import rcic.RcicF3RawFamilyMono

/-!
# The admitted normalized operator and its all-instance forward bridge

Only ordinary constructor fields are normalized. Family parameters, index
types, result indices, constructor order, and the actual field values are
retained. The same frame therefore gives the same family table before and
after normalization.

An inhabited raw field normalizes at every universe valuation using the
produced faithful-body equations. The field tuple proof also transports
the literal SmallAlong predicate. The public group theorem supplies the
body equations internally and has no K, InstOK, normalization, frame
admissibility, or constructor-closure premise. It does not produce the
small closed normalized frame or the bounded reverse bridge.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormal
open Rcic.Declarative PiValueRule RawFamily PiIndex
universe u

/-- Preserve the actual domains and the complete normalized argument list. -/
noncomputable def fieldSpec {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape} :
    EvalPlan.Field E fuel f nu np ni prior A s → FieldSpec
  | .plain _ => .plain A
  | .recursive r => .recursive r.domains r.arguments

/-- Ordinary fields remain in their original order and de Bruijn scopes. -/
noncomputable def specs {E : ResolvedEnv} {fuel f nu np ni : Nat} :
    {prior : Nat} → {ss : List FieldShape} → {Fs : List (Expr Nat)} →
    EvalPlan.Fields E fuel f nu np ni prior ss Fs → List FieldSpec
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => fieldSpec head :: specs tail

theorem specs_clean {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs) :
    Clean f (np + ni) (specs p) := by
  induction p with
  | nil => exact True.intro
  | cons head tail ih =>
      cases head with
      | plain hf => exact ⟨hf, ih⟩
      | recursive r =>
          exact ⟨r.domains_free, r.arguments_free, r.argument_count, ih⟩

/-- Forward normalization uses the original field inhabitant. -/
theorem field_den_of_mem (M : Interp.{u}) (E : ResolvedEnv) (σ : Nat → Nat)
    (hδ : DeltaNormalize.BodyEquations M E σ)
    {fuel f nu np ni prior : Nat} {A : Expr Nat} {s : FieldShape}
    (p : EvalPlan.Field E fuel f nu np ni prior A s)
    (ρ : Nat → PSet.{u}) (x : PSet.{u})
    (hx : x ∈ Ed M (den M σ ρ A)) :
    Equiv (den M σ ρ (fieldExpr f (canonL nu) (fieldSpec p))) (den M σ ρ A) := by
  cases p with
  | plain => exact Equiv.rfl
  | recursive r =>
      exact DeltaNormalize.telescope_of_mem M E σ hδ fuel A r.domains
        (foldApps (.const f (canonL nu)) r.arguments) ρ x r.read hx

/-- Normalize the whole tuple at the same actual values. Its field-set
membership in any bounding stage is preserved in both directions. -/
theorem fields_forward (M : Interp.{u}) (E : ResolvedEnv) (σ : Nat → Nat)
    (hδ : DeltaNormalize.BodyEquations M E σ)
    {fuel f nu np ni prior : Nat} {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs) :
    ∀ (ρ : Nat → PSet.{u}) (xs : List PSet.{u}), TelFits M σ Fs ρ xs →
      TelFits M σ ((specs p).map (fieldExpr f (canonL nu))) ρ xs ∧
      ∀ W : PSet.{u}, SmallAlong M σ W Fs ρ xs ↔
        SmallAlong M σ W ((specs p).map (fieldExpr f (canonL nu))) ρ xs := by
  induction p with
  | nil prior =>
      intro ρ xs hx
      cases xs with
      | nil => exact ⟨True.intro, fun _ => Iff.rfl⟩
      | cons => exact hx.elim
  | @cons prior s A ss Fs head tail ih =>
      intro ρ xs hx
      cases xs with
      | nil => exact hx.elim
      | cons x xs =>
          have he := ed_congr M (field_den_of_mem M E σ hδ head ρ x hx.1)
          obtain ⟨hfit, hsmall⟩ := ih (vcons x ρ) xs hx.2
          refine ⟨⟨mem_congr_right he.symm hx.1, hfit⟩, ?_⟩
          intro W
          change (Ed M (den M σ ρ A) ∈ W ∧ SmallAlong M σ W Fs (vcons x ρ) xs) ↔
            (Ed M (den M σ ρ (fieldExpr f (canonL nu) (fieldSpec head))) ∈ W ∧
              SmallAlong M σ W ((specs tail).map (fieldExpr f (canonL nu))) (vcons x ρ) xs)
          exact and_congr
            ⟨fun h => mem_congr_left he.symm h, fun h => mem_congr_left he h⟩
            (hsmall W)

noncomputable def fields (p : EvalPlan.Plan) (j : Fin p.node.a.constructors.length) :
    List (Expr Nat) :=
  (specs (p.constructors j).fields).map
    (fieldExpr p.node.a.family.ref (canonL p.node.a.family.member.arity))

/-- The finite constructor list includes no parameter duplication and loses
no constructor to the logical fallback outside the finite range. -/
noncomputable def constructors (p : EvalPlan.Plan) :
    List (List (Expr Nat) × List (Expr Nat)) :=
  (List.range p.node.a.constructors.length).map (fun j =>
    if hj : j < p.node.a.constructors.length then
      (fields p ⟨j, hj⟩, (p.node.a.constructorViews ⟨j, hj⟩).resultIndices)
    else ([], []))

noncomputable def fd (p : EvalPlan.Plan) : FamData :=
  { famDataOf p.node.a with ctors := constructors p }

theorem ctors_length (p : EvalPlan.Plan) :
    (fd p).ctors.length = p.node.a.constructors.length := by
  simp only [fd, constructors, List.length_map, List.length_range]

noncomputable def index (p : EvalPlan.Plan) (j : Fin (fd p).ctors.length) :
    Fin p.node.a.constructors.length :=
  ⟨j.val, by simpa only [ctors_length] using j.isLt⟩

theorem ctor_get (p : EvalPlan.Plan) (j : Fin (fd p).ctors.length) :
    (fd p).ctors.get j =
      (fields p (index p j), (p.node.a.constructorViews (index p j)).resultIndices) := by
  change (constructors p)[j.val]'j.isLt = _
  simp only [constructors, List.getElem_map, List.getElem_range]
  have hj : j.val < p.node.a.constructors.length := (index p j).isLt
  rw [dif_pos hj]
  apply Prod.ext
  · apply congrArg (fields p)
    apply Fin.ext
    simp only [index, List.getElem_range]
  · apply congrArg (fun k : Fin p.node.a.constructors.length =>
      (p.node.a.constructorViews k).resultIndices)
    apply Fin.ext
    simp only [index, List.getElem_range]

/-- The same frame induces exactly the same family value and table. Only
the constructor predicate changes when the descriptor is normalized. -/
theorem table_eq (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (C : Frame) :
    table P μ (fd p) C = table P μ (famDataOf p.node.a) C := rfl

/-- Every raw constructor presentation enters the actual normalized
operator, including its size guard and complete dependent result key. -/
theorem ctorAt_of_bodyEquations (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (p : EvalPlan.Plan) (C : Frame)
    (hδ : ∀ σ, DeltaNormalize.BodyEquations
      (mkM P (table P μ (famDataOf p.node.a) C)) p.node.E0 σ) :
    ∀ vs i z, CtorAt P μ (famDataOf p.node.a) C vs i z →
      CtorAt P μ (fd p) C vs i z := by
  intro vs i z hc
  obtain ⟨j, ps, xs, hp, hx, hs, hi, hz⟩ := hc
  let k : Fin p.node.a.constructors.length :=
    ⟨j.val, by simpa only [famDataOf_ctors_length] using j.isLt⟩
  have hraw : (famDataOf p.node.a).ctors.get j =
      ((p.node.a.constructorViews k).fields, (p.node.a.constructorViews k).resultIndices) := by
    have h := famDataOf_ctor p.node.a k
    rw [List.getElem?_eq_getElem j.isLt] at h
    exact Option.some.inj h
  rw [hraw] at hx hs hi
  let jn : Fin (fd p).ctors.length :=
    ⟨k.val, by simpa only [ctors_length] using k.isLt⟩
  have hk : index p jn = k := Fin.ext rfl
  have hnormal := ctor_get p jn
  rw [hk] at hnormal
  have hf := fields_forward (mkM P (table P μ (famDataOf p.node.a) C))
    p.node.E0 (σOf vs) (hδ (σOf vs)) (p.constructors k).fields
    (push ps ρ0) xs hx
  unfold CtorAt
  rw [table_eq]
  refine ⟨jn, ps, xs, hp, ?_, ?_, ?_, hz⟩
  · rw [hnormal]
    exact hf.1
  · rw [hnormal]
    dsimp only [fd]
    by_cases h0 : evalTotal (σOf vs) (famDataOf p.node.a).resLevel = 0
    · rw [if_pos h0]
      exact True.intro
    · rw [if_neg h0] at hs ⊢
      exact (hf.2 (W4 (evalTotal (σOf vs) (famDataOf p.node.a).resLevel))).mp hs
  · rw [hnormal]
    exact hi

/-- Actual group admission and faithfulness produce every delta equation
used by the all-instance forward constructor bridge. No semantic callback,
numerical bound, or frame admissibility is an additional input. -/
theorem ctorAt_of_group (F : RoleModel.FamilyValue) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (ctx : Nat → Role) (plans : EvalRole.Plans)
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hctx : ∀ r, Dom p.E' r →
      ctx r = envCtx (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
        hE hfam hctors hrec hmem) r)
    (hF : EvalRole.Faithful F P μ ctx plans p.E') (C : Frame) :
    ∀ vs i z, CtorAt P μ (famDataOf p.node.a) C vs i z →
      CtorAt P μ (fd p) C vs i z := by
  apply ctorAt_of_bodyEquations P μ p C
  intro σ
  have ht : table P μ (famDataOf p.node.a) C =
      upd μ p.f (ofFrame P μ (famDataOf p.node.a) C) := by
    exact congrArg (fun r => upd μ r (ofFrame P μ (famDataOf p.node.a) C)) p.node.fam
  rw [ht]
  exact EvalRoleDelta.bodyEquations_at_node F P μ ctx plans hE hfam hctors hrec hmem
    hctx hF p.node (ofFrame P μ (famDataOf p.node.a) C) σ

end Rcic.F3.PSet.EvalPlanNormal
