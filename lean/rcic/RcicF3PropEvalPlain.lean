import rcic.RcicF3PropEvalTyped
import rcic.RcicF3NormDPlanBridge

/-!
# Actual plain proof spines for the indexed Prop endpoint

An all-plain input spine contains precisely its original fields. At a
singleton Prop group, the existing bounded proof-field clause therefore
identifies every actual evaluation with the selected stored minor applied
to a proof tuple of the exact original field length. The full evaluation
key and the full recursor universe vector remain unchanged.

The final theorem consumes BoundG, the sound family prefix and an actual
evaluation. It assumes neither global evaluation existence nor endpoint
equality at untyped local environments. The no-PendA field-freeness face
also produces the plain-shape hypothesis from the actual admission scan.
This is an input to the nonvacuous legacy-iota proof, not the completed
IotaAt or universal group step. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

/-- Erasing an all-plain spine removes no value or binder. -/
theorem Inputs.plain_values {C : Context} {fuel : Nat} {Mx acc T : Expr Nat}
    {ss : List FieldShape} {ρ : Nat → PSet.{4}} {xs ys : List PSet.{4}}
    {out : PSet.{4}} (h : Inputs C fuel Mx acc ss T ρ xs ys out)
    (hplain : ∀ s, s ∈ ss → s = .nonrecursive) : ys = xs := by
  induction ss generalizing fuel Mx acc T ρ xs ys out with
  | nil => cases h; rfl
  | cons s ss ih =>
      have hs := hplain s (List.mem_cons_self _ _)
      subst s
      cases h with
      | plain x hx tail =>
          exact congrArg (List.cons x)
            (ih tail (fun s hs => hplain s (List.mem_cons_of_mem _ hs)))

/-- Actual NoFunRec admission and the checked family-free fields produce
plain shapes; a zero-depth recursive shape cannot be silently kept. -/
theorem plain_shapes_of_free (C : Context)
    (hFF : FamFreeBodies C.node.E0 C.node.a.family.ref)
    (hN : NoFunRec C.node)
    (hfree : ∀ (j : Fin C.node.a.constructors.length) A,
      A ∈ (C.node.a.constructorViews j).fields →
      occursConst C.node.a.family.ref A = false) :
    ∀ (j : Fin C.node.a.constructors.length) s,
      s ∈ C.node.h14.shapesAt j → s = .nonrecursive := by
  intro j s hs
  have hS := shapesNorm_of_fieldShapesFuel hFF (C.node.a.constructorViews j).fields
    C.node.a.family.parameters.length (C.node.h14.shapesAt j)
    (C.node.h14.analyzed j) (hN j)
  rw [← NormDPlanBridge.raw_shapes hS] at hs
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hs
  simp only [RecPlan.rawShape, hfree j A hA, Bool.false_eq_true, if_false]

/-- The result is the selected actual minor on its exact proof-field tuple.
The constructor census is used only to align the evaluated and selected rows. -/
theorem Eval.plain_result (C : Context)
    (hone : C.node.a.constructors.length ≤ 1)
    (hplain : ∀ (j : Fin C.node.a.constructors.length) s,
      s ∈ C.node.h14.shapesAt j → s = .nonrecursive)
    (hprop : ∀ (j : Fin C.node.a.constructors.length) ps,
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps →
      LEq ps C.parameters →
      PropTel C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0))
    (j : Fin C.node.a.constructors.length)
    {i : Index.{4}} {z : PSet.{4}} (h : Eval C i z) :
    Equiv z (fapps (C.minors.getD j.val pempty)
      ((C.node.a.constructorViews j).fields.map (fun _ => pempty))) := by
  cases h with
  | root j' ps xs ys fuel R out z hps hp hf hs hst hd hm hi hr =>
      have hj : j' = j := Fin.ext (by have := j'.isLt; have := j.isLt; omega)
      subst j'
      rw [hi.plain_values (hplain j)] at hr
      have hx0 := propTel_fits C.M C.σ (C.node.a.constructorViews j).fields
        (push ps ρ0) xs (hprop j ps hps hp) hf
      have hlen : xs.map (fun _ => (pempty : PSet.{4})) =
          (C.node.a.constructorViews j).fields.map (fun _ => pempty) := by
        simp only [List.map_const', hf.length]
      rw [hlen] at hx0
      exact hr.trans (fapps_congr_args _ hx0)

/-- BoundG pays proof-field erasure at the actual full recursor valuation.
In particular, no family-arity length restriction drops the motive slot. -/
theorem Eval.plain_result_of_boundG (C : Context)
    (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hB : BoundG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hM : C.M = mkM P μ)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (hES : EnvSound (mkM P μ) C.σ K (extendEnv C.E C.f fm)
      C.node.a.family.member.arity)
    (vs : List Nat) (hσ : C.σ = σOf vs)
    (hvs : ∀ v, v ∈ vs → v ≤ K C.rr)
    (hplain : ∀ (j : Fin C.node.a.constructors.length) s,
      s ∈ C.node.h14.shapesAt j → s = .nonrecursive)
    (j : Fin C.node.a.constructors.length)
    {i : Index.{4}} {z : PSet.{4}} (h : Eval C i z) :
    Equiv z (fapps (C.minors.getD j.val pempty)
      ((C.node.a.constructorViews j).fields.map (fun _ => pempty))) := by
  apply h.plain_result C (selection_prop C.node.a C.σ h0 hpolicy).2 hplain
    (fun k ps hps _ => ?_) j
  rw [hM] at hps ⊢
  apply propTel_of_typings_at P μ K C.σ C.node.a.family.parameters
    (C.node.a.constructorViews k).fields hES ?_ ps hps
  intro l
  obtain ⟨v, hv, d, hd⟩ :=
    hB.2.2.2 C.node (selection_prop C.node.a C.σ h0 hpolicy).1 hpolicy k vs hvs l
  exact ⟨v, hv C.σ, d, by rw [hσ]; exact hd⟩

end Rcic.F3.PSet.PropEval
