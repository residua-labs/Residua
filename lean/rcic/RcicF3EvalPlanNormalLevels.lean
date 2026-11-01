import rcic.RcicF3EvalPlanNormal
import rcic.RcicF3CandidatePrefixFromGroup

/-!
# Family-level bounds of the actual normalized constructor descriptor

Head normalization preserves the original family-level scope because every
transparent body in the admitted reader is level closed. The retained
Option reads then give level bounds for every normalized field. Parameters,
index types, result levels and constructor result indices are unchanged.
This supports transport to the full recursor valuation without bounding or
discarding its extra motive slot. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormal
open Rcic.Declarative PiValueRule

theorem telescope_levels {E : ResolvedEnv}
    (hbodies : ∀ r m b, E.members r = some m → m.body = some b →
      transparent m.mclass = true → exprLevelsBounded 0 b = true)
    (k : Nat) :
    ∀ (fuel : Nat) (A : Expr Nat) (ds : List (Expr Nat)) (b : Expr Nat),
      piTelescopeFuel E fuel A = some (ds, b) →
      exprLevelsBounded k A = true →
      exprLevelsBounded k (policyPi ds b) = true := by
  intro fuel
  induction fuel with
  | zero => intro A ds b hr _; cases hr
  | succ fuel ih =>
      intro A ds b hr hA
      cases hw : whnfFuel E fuel A with
      | none =>
          simp only [piTelescopeFuel, hw] at hr
          cases hr
      | some w =>
          have hwr := whnfFuel_levelsBounded hbodies fuel A w hA hw
          cases w with
          | pi D B =>
              have hDB : exprLevelsBounded k D = true ∧
                  exprLevelsBounded k B = true := by
                simpa only [exprLevelsBounded, Bool.and_eq_true] using hwr
              cases ht : piTelescopeFuel E fuel B with
              | none =>
                  simp only [piTelescopeFuel, hw, ht] at hr
                  cases hr
              | some result =>
                  rcases result with ⟨ds', b'⟩
                  have htail := ih B ds' b' ht hDB.2
                  simp only [piTelescopeFuel, hw, ht] at hr
                  cases hr
                  simpa only [policyPi, exprLevelsBounded, Bool.and_eq_true]
                    using And.intro hDB.1 htail
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [piTelescopeFuel, hw] at hr
              cases hr
              exact hwr

theorem field_levels {E : ResolvedEnv}
    (hbodies : ∀ r m b, E.members r = some m → m.body = some b →
      transparent m.mclass = true → exprLevelsBounded 0 b = true)
    {fuel f nu np ni prior : Nat} {A : Expr Nat} {s : FieldShape}
    (p : EvalPlan.Field E fuel f nu np ni prior A s) (k : Nat)
    (hA : exprLevelsBounded k A = true) :
    exprLevelsBounded k (fieldExpr f (canonL nu) (fieldSpec p)) = true := by
  cases p with
  | plain => exact hA
  | recursive r => exact telescope_levels hbodies k fuel A _ _ r.read hA

theorem fields_levels {E : ResolvedEnv}
    (hbodies : ∀ r m b, E.members r = some m → m.body = some b →
      transparent m.mclass = true → exprLevelsBounded 0 b = true)
    {fuel f nu np ni prior : Nat} {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : EvalPlan.Fields E fuel f nu np ni prior ss Fs) (k : Nat) :
    ExprsBounded k Fs →
      ExprsBounded k ((specs p).map (fieldExpr f (canonL nu))) := by
  induction p with
  | nil => exact fun _ _ he => (List.not_mem_nil _ he).elim
  | cons head tail ih =>
      intro hFs e he
      rcases List.mem_cons.mp he with rfl | he
      · exact field_levels hbodies head k (hFs _ (List.mem_cons_self _ _))
      · exact ih (fun A hA => hFs A (List.mem_cons_of_mem _ hA)) e he

/-- The body-level premise is produced from the actual predecessor and the
group's bodyless extensions, independently of semantic soundness. -/
theorem reader_bodies_levels {E E' : ResolvedEnv} {f rr : Nat}
    {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) :
    ∀ r m b, node.E0.members r = some m → m.body = some b →
      transparent m.mclass = true → exprLevelsBounded 0 b = true := by
  intro r m b hm hb htr
  have hfinal := node.sub r m (members_extend_preserved node.fresh r m hm)
  rcases groupMembersT_cases hmem r m hfinal with hold | hnew
  · exact (EvalRoleDelta.transparent_body_data hE r m b hold hb htr).2.2.2.2
  · rw [groupMembersT_body_none hmem r m hnew] at hb
    cases hb

/-- The actual cached descriptor retains the original family-level bound.
The quantifier is syntactic and does not constrain larger universe values. -/
theorem bounded_of_group (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E') :
    FamBounded (fd p) p.node.a.family.member.arity := by
  obtain ⟨_, _, _, _, _, hraw⟩ := CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  have hbodies := reader_bodies_levels hE hmem p.node
  refine ⟨hraw.params, hraw.indices, hraw.res, ?_⟩
  intro c hc
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem hc
  let j : Fin (fd p).ctors.length := ⟨k, hk⟩
  have hcj : c = (fields p (index p j),
      (p.node.a.constructorViews (index p j)).resultIndices) := by
    rw [← he]
    exact ctor_get p j
  rw [hcj]
  have hmember := famDataOf_ctor p.node.a (index p j)
  have hbound := hraw.ctors _ (List.getElem?_mem hmember)
  exact ⟨fields_levels hbodies (p.constructors (index p j)).fields _ hbound.1,
    hbound.2⟩

end Rcic.F3.PSet.EvalPlanNormal
