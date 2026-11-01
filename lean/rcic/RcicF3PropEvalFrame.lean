import rcic.RcicF3PropEvalCandidate

/-!
# Guarded evaluation candidates over any admissible base frame

The candidate is a literal restriction of the supplied base frame by the
same complete-key, parameter-scoped evaluation predicate. Its membership
therefore supplies recursive evaluations at reached keys. No constructor
closure or evaluation totality is supplied to this adapter.

The normalized-frame producer will instantiate this base. The historical
raw-frame APIs remain unchanged. This module alone does not produce the
candidate's closure or a repaired StepAG theorem. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalFrame
open Rcic.Declarative PiIndex RawFamilyRec

noncomputable def candidate (N : RawFamily.Frame) (C : PropEval.Context) :
    RawFamily.Frame := RawFamily.restrict N (PropEvalCandidate.EvalPredicate C)

theorem admissible (P : Premises4) (C : PropEval.Context) (N : RawFamily.Frame)
    (hN : RawFamily.Admissible (famDataOf C.node.a) N) :
    RawFamily.Admissible (famDataOf C.node.a) (candidate N C) :=
  RawFamily.restrict_admissible P (famDataOf C.node.a) N hN
    (PropEvalCandidate.EvalPredicate C)

theorem exists_of_mem (C : PropEval.Context) (N : RawFamily.Frame)
    (vs : List Nat) (i : Index.{4}) (x : PSet.{4})
    (hx : x ∈ candidate N C vs i)
    (hσ : ∀ u, u < C.node.a.family.member.arity → C.σ u = σOf vs u)
    (hp : paramKey C.node.a.family.parameters.length i = key C.parameters) :
    ∃ z, PropEval.Eval C i z := by
  obtain ⟨j, hQ, _⟩ := mem_sep.mp hx
  exact hQ hσ hp

/-- Actual membership of the normalized candidate field produces an evaluation
at every fitting raw argument list. Both domain and full-key transport are
proved from the admission's family-free syntax facts. -/
theorem leaf_eval (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (C : PropEval.Context) (hM : C.M = mkM P μ)
    (N : RawFamily.Frame)
    (hN : RawFamily.Admissible (famDataOf C.node.a) N)
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
    (hx : x ∈ Ed (mkM P (RawFamily.table P μ (famDataOf C.node.a) (candidate N C)))
      (den (mkM P (RawFamily.table P μ (famDataOf C.node.a) (candidate N C))) C.σ ρ
        (policyPi ds (foldApps
          (.const (famDataOf C.node.a).fref
            ((List.range C.node.a.family.member.arity).map Level.param)) args)))) :
    ∀ zs, TelFits C.M C.σ ds ρ zs →
      ∃ z, PropEval.Eval C (key (args.map (den C.M C.σ (push zs ρ)))) z := by
  intro zs hzs
  let fd := famDataOf C.node.a
  let X := candidate N C
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
    (admissible P C N hN) hf vs (args.map (den MX C.σ (push zs ρ)))
    ((List.length_map _ _).trans hlen) (fapps x zs)).mp hleaf
  have hmem : fapps x zs ∈ X vs (key (args.map (den C.M C.σ (push zs ρ)))) := by
    rw [← hargsEq]
    exact hdecoded.2
  apply exists_of_mem C N vs _ (fapps x zs) hmem (PropEvalCandidate.canonical_agreement C)
  change key ((args.map (den C.M C.σ (push zs ρ))).take C.node.a.family.parameters.length) = _
  rw [← List.map_take]
  exact (key_eq_iff _ _).mpr (hprefix zs hzs)

end Rcic.F3.PSet.PropEvalFrame
