import rcic.RcicF3ReaderNoBeta
import rcic.RcicF3EvalPlanNormalTuple
import rcic.RcicF3PointwiseRoleEquations

/-!
# Actual cached field transport through delta/zeta readers

The syntax certificate is attached to every recursive field in the actual
retained cache; plain fields impose no extra condition. A certified reader
keeps the literal source, fuel, domains and complete family argument list.
Guarded monotonicity and produced bidirectional normalization reconstruct
the original field tuple at the same values in an arbitrary target frame.

The public pointwise wrapper produces transparent-body equations from the
actual predecessor's faithful table and the body's original read support.
It uses neither completed-group soundness nor a mirror-fitting assumption.
The unrestricted beta-containing PropOnly case remains open.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.ReaderNoBeta
open Rcic.Declarative Rcic.Model.PS RawFamily PiValueRule

def FieldTrace {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape} :
    EvalPlan.Field E fuel f nu np ni prior A s → Prop
  | .plain _ => True
  | .recursive r => Telescope E fuel A r.domains
      (foldApps (.const f (canonL nu)) r.arguments)

def FieldsTrace {E : ResolvedEnv} {fuel f nu np ni : Nat} :
    {prior : Nat} → {ss : List FieldShape} → {Fs : List (Expr Nat)} →
    EvalPlan.Fields E fuel f nu np ni prior ss Fs → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons head tail => FieldTrace head ∧ FieldsTrace tail

/-- The certificate is read from this plan's retained constructor cache. -/
def Cached (p : EvalPlan.Plan) : Prop :=
  ∀ j : Fin p.node.a.constructors.length, FieldsTrace (p.constructors j).fields

/-- The canonical original-node face used by admission-step producers. -/
def SourceNoBeta {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Prop := Cached (EvalPlan.ofNode node)

/-- Actual cache lookup, retaining the source certificate at that position.
No reader result is selected from an existential witness. -/
theorem field_at {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs)
    (hp : FieldsTrace p) :
    ∀ k (hk : k < Fs.length),
      ∃ (prior' : Nat) (s : FieldShape)
        (q : EvalPlan.Field E fuel f nu np ni prior' (Fs[k]'hk) s),
        prior' = prior + k ∧
        ((EvalPlanNormal.specs p).map (fieldExpr f (canonL nu)))[k]? =
          some (fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec q)) ∧
        FieldTrace q := by
  revert hp
  induction p with
  | nil => intro _hp k hk; exact (Nat.not_lt_zero k hk).elim
  | @cons prior s A ss Fs head tail ih =>
      intro hp k hk
      cases k with
      | zero =>
          refine ⟨prior, s, head, rfl, ?_, hp.1⟩
          simp only [EvalPlanNormal.specs, List.map_cons, List.getElem?_cons_zero]
      | succ k =>
          obtain ⟨prior', s', q, hprior, hq, htrace⟩ :=
            ih hp.2 k (Nat.lt_of_succ_lt_succ hk)
          refine ⟨prior', s', q, hprior.trans (Nat.add_right_comm prior 1 k), ?_, htrace⟩
          simpa only [EvalPlanNormal.specs, List.map_cons, List.getElem?_cons_succ]
            using hq

/-- The entire original tuple is recovered using the candidate relation
only on the reached valuation and parameter-key slice. Parameter values
need only their literal count; no parameter telescope is reinterpreted. -/
theorem fields_to_raw_of_guarded (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (hread : Cached p)
    (X D : Frame) (hX : Admissible (famDataOf p.node.a) X)
    (hD : Admissible (famDataOf p.node.a) D)
    (hδ : DeltaNormalize.BodyEquations
      (mkM P (table P μ (famDataOf p.node.a) D)) p.node.E0 σ)
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : ps.length = p.node.a.family.parameters.length)
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
  obtain ⟨prior, s, q, hprior, hq, htrace⟩ :=
    field_at (p.constructors j).fields (hread j) k hk
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
        X D hX hD σ r ps pre hps hpreLen hsub x hx
      have ht : Telescope p.node.E0 (p.constructors j).fuel
          ((p.node.a.constructorViews j).fields[k]) r.domains
          (foldApps (.const p.node.a.family.ref
            (canonL p.node.a.family.member.arity)) r.arguments) := htrace
      have hn := ht.den MD σ hδ (push pre (push ps ρ0))
      exact mem_congr_right (ed_congr MD hn) hxN

/-- The original predecessor pays every delta equation after an arbitrary
fresh family update and the actual bodyless reader extension. -/
theorem bodyEquations_update_at_node (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (α : PointwiseRole.Arities) (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (D : Frame) :
    DeltaNormalize.BodyEquations
      (mkM P (table P μ (famDataOf p.node.a) D)) p.node.E0 σ := by
  have hfresh : p.E.members (famDataOf p.node.a).fref = none := by
    change p.E.members p.node.a.family.ref = none
    rw [p.node.fam]
    exact groupMembersT_fresh_base hmem p.f fm (List.mem_cons_self _ _)
  have hnew : ∀ r m, p.node.E0.members r = some m →
      p.E.members r = none → m.body = none := by
    intro r m hm hn
    have hm' := p.node.sub r m (members_extend_preserved p.node.fresh r m hm)
    rcases groupMembersT_cases hmem r m hm' with hold | hnew
    · rw [hn] at hold
      cases hold
    · exact groupMembersT_body_none hmem r m hnew
  have hδ := PointwiseRoleEquations.bodyEquations_of_faithful P α μ
    ctx plans hE hctx hFaith σ
  have hδD := EvalRoleDelta.bodyEquations_transfer P hE
    (agreeOn_upd hfresh μ (ofFrame P μ (famDataOf p.node.a) D)) σ hδ
  exact EvalRoleDelta.bodyEquations_extension P
    (table P μ (famDataOf p.node.a) D) p.node.base hnew σ hδD

/-- Public original-group transport. The syntax certificate is the only
extra face condition; all transparent-body semantics are produced here
from the predecessor's actual pointwise faithful table. -/
theorem fields_to_raw_of_pointwise (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (α : PointwiseRole.Arities) (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom p.E r → ctx r = NormRole.envCtx hE r)
    (hFaith : EvalRole.Faithful (PointwiseRole.familyValue α) P μ ctx plans p.E)
    (hread : Cached p)
    (X D : Frame) (hX : Admissible (famDataOf p.node.a) X)
    (hD : Admissible (famDataOf p.node.a) D)
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : ps.length = p.node.a.family.parameters.length)
    (hsub : EvalPlanNormalSlice.GuardedSub p.node.a.family.member.arity
      p.node.a.family.parameters.length σ ps X D)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) X))
      σ (EvalPlanNormal.fields p j) (push ps ρ0) xs) :
    TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      (p.node.a.constructorViews j).fields (push ps ρ0) xs :=
  fields_to_raw_of_guarded P μ σ p hread X D hX hD
    (bodyEquations_update_at_node P μ σ p fm ctors hE hmem α ctx plans hctx hFaith D)
    j ps xs hps hsub hxs

end Rcic.F3.PSet.ReaderNoBeta

#print axioms Rcic.F3.PSet.ReaderNoBeta.fields_to_raw_of_guarded
#print axioms Rcic.F3.PSet.ReaderNoBeta.bodyEquations_update_at_node
#print axioms Rcic.F3.PSet.ReaderNoBeta.fields_to_raw_of_pointwise
