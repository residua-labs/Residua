import rcic.RcicF3PiRecExtract
/-! Admission-plan recursor values. The data endpoint consumes the normalized
field plan retained by the typed admission descriptor. The Prop endpoint
retains the existing policy. This supplies operational unfolding and
extensionality, not universal recursor typing or a group producer.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecPlanValue
universe u
open Rcic.Declarative

noncomputable def endValue (M : Interp.{u}) (σ : Nat → Nat) (fd : FamData)
    (plan : List (List FieldShape)) (ρ : Nat → PSet.{u}) : PSet.{u} :=
  cond M.dec (evalTotal σ fd.resLevel = 0) (recEnd M σ fd ρ)
    (RecPlan.core M fd.fref plan (minorsOf fd.indices.length fd.ctors.length ρ) (ρ 0))

noncomputable def memberValue (M : Interp.{u}) (σ : Nat → Nat) (fd : FamData)
    (plan : List (List FieldShape)) (m : CheckedMember) : PSet.{u} :=
  piLam M σ (endValue M σ fd plan) (fun _ => pempty) m.mtype

noncomputable def nodeValue (M : Interp.{u}) (σ : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : PSet.{u} :=
  memberValue M σ (famDataOf node.a) (RecPlan.nodePlan node) rm

/-- Extensional endpoint and exact compatibility at the old raw plan. -/
theorem laws (M : Interp.{u}) (σ : Nat → Nat) (fd : FamData)
    (plan : List (List FieldShape)) :
    EnvResp (endValue M σ fd plan) ∧
      ∀ ρ, endValue M σ fd (RecPlan.rawPlan fd) ρ = recEnd M σ fd ρ := by
  constructor
  · intro ρ ρ' h
    unfold endValue
    apply cond_congr Iff.rfl (recEnd_resp M σ fd ρ ρ' h)
    exact recCore_congr M (RecPlan.descriptor fd.fref plan)
      (minorsOf_congr _ _ h) _ _ (h 0)
  · intro ρ
    unfold endValue
    rw [RecPlan.core_raw]
    unfold recEnd
    by_cases h0 : evalTotal σ fd.resLevel = 0
    · rw [cond_pos h0, cond_pos h0]
    · rw [cond_neg h0, cond_neg h0]

/-- Actual original fields unfold the repaired endpoint using admission's
normalized plan. Ordinary environment/instance facts pay field extraction. -/
theorem node_end_of_fits (M : Interp.{u}) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) {n : Nat}
    (hE : EnvSound M σ K node.E0 n) (hb : BodiesOK node.E0 σ K)
    (ht : evalTotal σ node.a.family.resultLevel ≠ 0)
    (ps : List PSet.{u}) (mo : PSet.{u}) (ms is : List PSet.{u})
    (hms : ms.length = node.a.constructors.length)
    (his : is.length = node.a.family.indices.length)
    (i : Fin node.a.constructors.length)
    (hI : ∀ A ∈ (node.a.constructorViews i).fields, InstOK node.E0 σ K A)
    (ρ : Nat → PSet.{u}) (xs : List PSet.{u})
    (hx : TelFits M σ (node.a.constructorViews i).fields ρ xs) :
    Equiv (endValue M σ (famDataOf node.a) (RecPlan.nodePlan node)
      (push (ps ++ mo :: (ms ++ (is ++ [dataVal i.val xs]))) (fun _ => pempty)))
      (fapps (ms.getD i.val pempty)
        (RecPlan.args (RecPlan.nodeCore M node ms) (node.h14.shapesAt i) xs)) := by
  unfold endValue
  have ht' : evalTotal σ (famDataOf node.a).resLevel ≠ 0 := ht
  rw [cond_neg ht']
  have his' : is.length = (famDataOf node.a).indices.length := his
  rw [minorsOf_env ps mo ms is (dataVal i.val xs) (fun _ => pempty)
    (hms.trans (famDataOf_ctors_length node.a).symm) his']
  have hz : push (ps ++ mo :: (ms ++ (is ++ [dataVal i.val xs])))
      (fun _ : Nat => (pempty : PSet.{u})) 0 = dataVal i.val xs := by
    rw [push_cons_eq]
    rfl
  rw [hz]
  change Equiv (RecPlan.core M node.a.family.ref (RecPlan.nodePlan node) ms _)
    (fapps _ _)
  rw [node.fam]
  exact RecPlan.node_data_of_fits M σ K node hE hb ms i hI ρ xs hx

end Rcic.F3.PSet.RecPlanValue
