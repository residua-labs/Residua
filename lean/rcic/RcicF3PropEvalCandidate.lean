import rcic.RcicF3PropEval
import rcic.RcicF3RawFamilyInduction
import rcic.RcicF3RawFamilyView
import rcic.RcicF3PiLeafParams

/-!
# Guarded candidate membership supplies actual recursive evaluations

The candidate retains the complete family vector and parameter/index key.
Its guard compares syntax valuations only below the family arity. At a
normalized recursive field, free domains transport the same fitting argument
list, and free terminal arguments preserve the entire key. Actual field
membership then supplies child evaluation existence through the candidate.
The closure-to-totality lemma is a composition with an explicit closure proof;
this module does not assert universal candidate closure. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PiIndependent
open Rcic.Declarative

/-- Family-free dependent domains preserve fitting under a single table update. -/
theorem telFits_free (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) :
    ∀ (ds : List (Expr Nat)), (∀ A ∈ ds, occursConst f A = false) →
      ∀ (ρ : Nat → PSet.{4}) (xs : List PSet.{4}),
        TelFits (mkM P (upd μ f X₁)) σ ds ρ xs ↔
          TelFits (mkM P (upd μ f X₂)) σ ds ρ xs := by
  intro ds
  induction ds with
  | nil =>
      intro _ ρ xs
      cases xs <;> rfl
  | cons A ds ih =>
      intro hfree ρ xs
      cases xs with
      | nil => rfl
      | cons x xs =>
          change (x ∈ Ed (mkM P (upd μ f X₁))
              (den (mkM P (upd μ f X₁)) σ ρ A) ∧ _) ↔
            (x ∈ Ed (mkM P (upd μ f X₂))
              (den (mkM P (upd μ f X₂)) σ ρ A) ∧ _)
          rw [den_free P μ f X₁ X₂ σ A (hfree A (List.mem_cons_self _ _)) ρ]
          exact and_congr Iff.rfl
            (ih (fun B hB => hfree B (List.mem_cons_of_mem _ hB)) (vcons x ρ) xs)

end Rcic.F3.PSet.PiIndependent

namespace Rcic.F3.PSet.PropEvalCandidate
open Rcic.Declarative PiIndex RawFamilyRec

def EvalPredicate (C : PropEval.Context) (vs : List Nat) (i : Index.{4})
    (_ : PSet.{4}) : Prop :=
  (∀ u, u < C.node.a.family.member.arity → C.σ u = σOf vs u) →
  paramKey C.node.a.family.parameters.length i = key C.parameters →
  ∃ z, PropEval.Eval C i z

noncomputable def candidate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : PropEval.Context) : RawFamily.Frame :=
  RawFamily.restrict (RawFamily.frame P μ (famDataOf C.node.a)) (EvalPredicate C)

theorem admissible (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : PropEval.Context)
    (hRaw : RawFamily.Admissible (famDataOf C.node.a)
      (RawFamily.frame P μ (famDataOf C.node.a))) :
    RawFamily.Admissible (famDataOf C.node.a) (candidate P μ C) :=
  RawFamily.restrict_admissible P (famDataOf C.node.a) _ hRaw (EvalPredicate C)

theorem exists_of_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : PropEval.Context) (vs : List Nat) (i : Index.{4}) (x : PSet.{4})
    (hx : x ∈ candidate P μ C vs i)
    (hσ : ∀ u, u < C.node.a.family.member.arity → C.σ u = σOf vs u)
    (hp : paramKey C.node.a.family.parameters.length i = key C.parameters) :
    ∃ z, PropEval.Eval C i z := by
  obtain ⟨j, hQ, _⟩ := mem_sep.mp hx
  exact hQ hσ hp

/-- Canonical family levels retain precisely the guarded family slots.
The motive valuation outside these slots remains arbitrary. -/
theorem canonical_agreement (C : PropEval.Context) :
    ∀ u, u < C.node.a.family.member.arity → C.σ u =
      σOf (((List.range C.node.a.family.member.arity).map Level.param).map
        (evalTotal C.σ)) u := by
  intro u hu
  symm
  have hlen : u < (((List.range C.node.a.family.member.arity).map Level.param).map
      (evalTotal C.σ)).length := by simpa only [List.length_map, List.length_range] using hu
  unfold σOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp only [Option.getD_some, List.getElem_map, List.getElem_range, evalTotal]

/-- Actual membership of the normalized candidate field produces an evaluation
at every fitting raw argument list. Both domain and full-key transport are
proved from the admission's family-free syntax facts. -/
theorem leaf_eval (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : PropEval.Context) (hM : C.M = mkM P μ)
    (hRaw : RawFamily.Admissible (famDataOf C.node.a)
      (RawFamily.frame P μ (famDataOf C.node.a)))
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (ds args : List (Expr Nat))
    (hd : ∀ e ∈ ds, occursConst (famDataOf C.node.a).fref e = false)
    (ha : ∀ e ∈ args, occursConst (famDataOf C.node.a).fref e = false)
    (hlen : args.length = ((famDataOf C.node.a).params ++ (famDataOf C.node.a).indices).length)
    (ρ : Nat → PSet.{4}) (x : PSet.{4})
    (hprefix : ∀ zs, TelFits C.M C.σ ds ρ zs →
      LEq ((args.take C.node.a.family.parameters.length).map
        (den C.M C.σ (push zs ρ))) C.parameters)
    (hx : x ∈ Ed (mkM P (RawFamily.table P μ (famDataOf C.node.a) (candidate P μ C)))
      (den (mkM P (RawFamily.table P μ (famDataOf C.node.a) (candidate P μ C))) C.σ ρ
        (policyPi ds (foldApps
          (.const (famDataOf C.node.a).fref
            ((List.range C.node.a.family.member.arity).map Level.param)) args)))) :
    ∀ zs, TelFits C.M C.σ ds ρ zs →
      ∃ z, PropEval.Eval C (key (args.map (den C.M C.σ (push zs ρ)))) z := by
  intro zs hzs
  let fd := famDataOf C.node.a
  let X := candidate P μ C
  let MX := mkM P (RawFamily.table P μ fd X)
  let vs := ((List.range C.node.a.family.member.arity).map Level.param).map (evalTotal C.σ)
  have hfit := PiIndependent.telFits_free P μ fd.fref (μ fd.fref)
    (RawFamily.ofFrame P μ fd X) C.σ ds hd ρ zs
  rw [PiIndependent.upd_self] at hfit
  have hzsX : TelFits MX C.σ ds ρ zs := hfit.mp (by simpa only [hM] using hzs)
  have hargs := PiIndependent.leafArgs_free P μ fd.fref
    (RawFamily.ofFrame P μ fd X) (μ fd.fref) C.σ args ha (push zs ρ)
  rw [PiIndependent.upd_self] at hargs
  have hargsEq : args.map (den MX C.σ (push zs ρ)) =
      args.map (den C.M C.σ (push zs ρ)) := by
    simpa only [PiIndependent.leafArgs, hM] using hargs
  have hleaf := mem_fapps MX C.σ
    (foldApps (.const fd.fref ((List.range C.node.a.family.member.arity).map Level.param)) args)
    ds ρ x zs hx hzsX
  rw [den_foldApps] at hleaf
  have hdecoded := (RawFamily.apply_updated_mem_iff P μ fd X
    (admissible P μ C hRaw) hf vs (args.map (den MX C.σ (push zs ρ)))
    ((List.length_map _ _).trans hlen) (fapps x zs)).mp hleaf
  have hmem : fapps x zs ∈ X vs (key (args.map (den C.M C.σ (push zs ρ)))) := by
    rw [← hargsEq]
    exact hdecoded.2
  apply exists_of_mem P μ C vs _ (fapps x zs) hmem (canonical_agreement C)
  change key ((args.map (den C.M C.σ (push zs ρ))).take C.node.a.family.parameters.length) = _
  rw [← List.map_take]
  exact (key_eq_iff _ _).mpr (hprefix zs hzs)

/-- Checked leastness composition. The constructor-closure proof is an explicit
argument here and must be supplied by the actual candidate constructor step. -/
theorem exists_of_closed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : PropEval.Context)
    (hRaw : RawFamily.Admissible (famDataOf C.node.a)
      (RawFamily.frame P μ (famDataOf C.node.a)))
    (hClosed : RawFamily.Closed P μ (famDataOf C.node.a) (candidate P μ C))
    (vs : List Nat) (i : Index.{4}) (x : PSet.{4})
    (hx : x ∈ RawFamily.frame P μ (famDataOf C.node.a) vs i)
    (hσ : ∀ u, u < C.node.a.family.member.arity → C.σ u = σOf vs u)
    (hp : paramKey C.node.a.family.parameters.length i = key C.parameters) :
    ∃ z, PropEval.Eval C i z :=
  exists_of_mem P μ C vs i x
    (RawFamily.frame_least P μ (famDataOf C.node.a) (candidate P μ C)
      (admissible P μ C hRaw) hClosed vs i x hx) hσ hp

end Rcic.F3.PSet.PropEvalCandidate
