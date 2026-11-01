import rcic.RcicF3RawFamilyView
import rcic.RcicF3EvalPlanNormalMono

/-!
# A produced beta-hidden parameter mirror at valid family candidates

The family argument of the beta redex is typed by the supplied admissible
frame itself. Actual group metadata pays the closed family kind and its
universe support. Thus every finite nesting of this mirror evaluates to
the original domain at the full valuation, in every admissible candidate
table, without a BoundG, EnvSound, or mirror-soundness callback.

The telescope theorem preserves the original parameter values and binder
order. This is a component for this particular typed beta construction.
It does not interpret an arbitrary TyConvT mirror, establish read support
at arbitrary invalid ambient family entries, or remove dependence on
earlier recursive DATA values. No StepAG premise is changed.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.FamilyBetaMirror
open Rcic.Declarative Rcic.Model.PS RawFamily

/-- A fresh-family occurrence hidden in an unused, correctly typed beta
argument. The original domain can depend on all preceding local values. -/
def mirror (fd : FamData) (arity : Nat) (A : Expr Nat) : Expr Nat :=
  .app (.lam (famType fd) (Rcic.Declarative.lift 0 1 A))
    (.const fd.fref (canonL arity))

def mirrors (fd : FamData) (arity : Nat) : Nat → Expr Nat → Expr Nat
  | 0, A => A
  | n + 1, A => mirror fd arity (mirrors fd arity n A)

/-- Admissibility supplies the actual beta argument's membership. The
full local environment and valuation are retained, including extra slots. -/
theorem den_mirror (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (arity : Nat)
    (hclosed : ∀ k, Rcic.Declarative.lift k 1 (famType fd) = famType fd)
    (hbounded : exprLevelsBounded arity (famType fd) = true)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (A : Expr Nat) :
    Equiv (den (mkM P (table P μ fd C)) σ ρ (mirror fd arity A))
      (den (mkM P (table P μ fd C)) σ ρ A) := by
  let M := mkM P (table P μ fd C)
  let vs := (canonL arity).map (evalTotal σ)
  have hag : ∀ i, i < arity → σOf vs i = σ i := by
    intro i hi
    have hlen : i < vs.length := by
      simpa only [vs, canonL, List.length_map, List.length_range] using hi
    change vs.getD i 0 = σ i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    simp only [Option.getD_some, vs, canonL, List.getElem_map,
      List.getElem_range, evalTotal]
  have htype : den M (σOf vs) ρ0 (famType fd) = den M σ ρ (famType fd) :=
    (den_levels_agree M hag (famType fd) hbounded ρ0).trans
      (den_closed M σ (famType fd) hclosed ρ0 ρ)
  have harg : ofFrame P μ fd C vs ∈ Ed M (den M σ ρ (famType fd)) := by
    have h := ofFrame_mem P (table P μ fd C) fd C hC vs
    have he : Equiv (ofFrame P (table P μ fd C) fd C vs)
        (ofFrame P μ fd C vs) := ofFrame_updated P μ fd C hf vs
    rw [htype] at h
    exact mem_congr_left he h
  have hconst : den M σ ρ (.const fd.fref (canonL arity)) =
      ofFrame P μ fd C vs := upd_eq _ _ _ _
  change Equiv (fapp (lamVal M (den M σ ρ (famType fd))
    (fun x => den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 A)))
    (den M σ ρ (.const fd.fref (canonL arity)))) (den M σ ρ A)
  rw [hconst]
  have hβ := beta_val M
    (b := fun x => den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 A))
    (fun _ _ h => den_congr M σ _ (vcons_congr h (fun _ => Equiv.rfl))) harg
  have hlift : den M σ (vcons (ofFrame P μ fd C vs) ρ)
      (Rcic.Declarative.lift 0 1 A) = den M σ ρ A :=
    den_lift0_push M σ [ofFrame P μ fd C vs] ρ A
  change Equiv _ (den M σ (vcons (ofFrame P μ fd C vs) ρ)
    (Rcic.Declarative.lift 0 1 A)) at hβ
  rw [hlift] at hβ
  exact hβ

/-- This covers arbitrary finite hidden depth; no normalization fuel is
selected and no component of the valuation is replaced. -/
theorem den_mirrors (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (arity : Nat)
    (hclosed : ∀ k, Rcic.Declarative.lift k 1 (famType fd) = famType fd)
    (hbounded : exprLevelsBounded arity (famType fd) = true)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (n : Nat) (A : Expr Nat) :
    Equiv (den (mkM P (table P μ fd C)) σ ρ (mirrors fd arity n A))
      (den (mkM P (table P μ fd C)) σ ρ A) := by
  induction n with
  | zero => exact Equiv.rfl
  | succ n ih =>
      exact (den_mirror P μ fd C hC hf arity hclosed hbounded σ ρ
        (mirrors fd arity n A)).trans ih

/-- Original tuple membership is recovered in the SAME candidate model,
at the same values, after all nested beta mirrors have been removed. -/
theorem fits_mirrors (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hC : Admissible fd C)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (arity : Nat)
    (hclosed : ∀ k, Rcic.Declarative.lift k 1 (famType fd) = famType fd)
    (hbounded : exprLevelsBounded arity (famType fd) = true)
    (σ : Nat → Nat) (n : Nat) : ∀ (ds : List (Expr Nat))
      (ρ : Nat → PSet.{4}) (xs : List PSet.{4}),
    TelFits (mkM P (table P μ fd C)) σ (ds.map (mirrors fd arity n)) ρ xs ↔
      TelFits (mkM P (table P μ fd C)) σ ds ρ xs := by
  intro ds
  induction ds with
  | nil => intro ρ xs; cases xs <;> exact Iff.rfl
  | cons A ds ih =>
      intro ρ xs
      cases xs with
      | nil => exact Iff.rfl
      | cons x xs =>
          have he := ed_congr (mkM P (table P μ fd C))
            (den_mirrors P μ fd C hC hf arity hclosed hbounded σ ρ n A)
          change (x ∈ _ ∧ _) ↔ (x ∈ _ ∧ _)
          exact and_congr
            ⟨fun hx => mem_congr_right he hx,
              fun hx => mem_congr_right he.symm hx⟩
            (ih (vcons x ρ) xs)

/-- The complete hidden telescope is independent of the candidate family
when the underlying domains are family-free. The proof does not equate
arbitrary ambient family tables, and keeps the same parameter tuple. -/
theorem fits_candidates (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C D : Frame) (hC : Admissible fd C) (hD : Admissible fd D)
    (hf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (arity : Nat)
    (hclosed : ∀ k, Rcic.Declarative.lift k 1 (famType fd) = famType fd)
    (hbounded : exprLevelsBounded arity (famType fd) = true)
    (σ : Nat → Nat) (n : Nat) (ds : List (Expr Nat))
    (hds : ∀ e ∈ ds, occursConst fd.fref e = false)
    (ρ : Nat → PSet.{4}) (xs : List PSet.{4}) :
    TelFits (mkM P (table P μ fd C)) σ (ds.map (mirrors fd arity n)) ρ xs ↔
      TelFits (mkM P (table P μ fd D)) σ (ds.map (mirrors fd arity n)) ρ xs := by
  have hag : AgreeOn (table P μ fd C) (table P μ fd D) (fun r => r ≠ fd.fref) := by
    intro r hr vs
    change upd μ fd.fref (ofFrame P μ fd C) r vs =
      upd μ fd.fref (ofFrame P μ fd D) r vs
    rw [upd_ne μ fd.fref (ofFrame P μ fd C) hr,
      upd_ne μ fd.fref (ofFrame P μ fd D) hr]
  exact (fits_mirrors P μ fd C hC hf arity hclosed hbounded σ n ds ρ xs).trans
    ((TelFits_agreeOn P hag σ ds
      (fun e he r hr => denRefs_ne_of_occurs e (hds e he) r hr) ρ xs).trans
      (fits_mirrors P μ fd D hD hf arity hclosed hbounded σ n ds ρ xs).symm)

/-- All syntax metadata of the beta construction is supplied by the
actual admitted group; only the selected candidate's admissibility remains. -/
theorem den_of_group (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (C : Frame) (hC : Admissible (EvalPlanNormal.fd p) C)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (n : Nat) (A : Expr Nat) :
    Equiv (den (mkM P (table P μ (EvalPlanNormal.fd p) C)) σ ρ
      (mirrors (EvalPlanNormal.fd p) p.node.a.family.member.arity n A))
      (den (mkM P (table P μ (EvalPlanNormal.fd p) C)) σ ρ A) := by
  obtain ⟨hfm, hty, hf, hTF, _, _⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem p.node
  have hm : p.E'.members p.f = some fm :=
    groupMembersT_installed hmem (List.mem_cons_self _ _)
  have hc : ∀ k, Rcic.Declarative.lift k 1
      (famType (EvalPlanNormal.fd p)) = famType (EvalPlanNormal.fd p) := by
    intro k
    change Rcic.Declarative.lift k 1 (famType (famDataOf p.node.a)) =
      famType (famDataOf p.node.a)
    rw [← hty]
    exact (hTF p.f fm hm).1 k
  have hb : exprLevelsBounded p.node.a.family.member.arity
      (famType (EvalPlanNormal.fd p)) = true := by
    change exprLevelsBounded p.node.a.family.member.arity
      (famType (famDataOf p.node.a)) = true
    rw [← hty, hfm]
    exact (hTF p.f fm hm).2.1
  exact den_mirrors P μ (EvalPlanNormal.fd p) C hC hf
    p.node.a.family.member.arity hc hb σ ρ n A

end Rcic.F3.PSet.FamilyBetaMirror
