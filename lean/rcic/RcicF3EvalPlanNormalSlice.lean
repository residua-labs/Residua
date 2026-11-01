import rcic.RcicF3EvalPlanNormal
import rcic.RcicF3PiLeafParams

/-!
# Local guarded transport of actual normalized recursive fields

The induction predicate asks for target-frame membership only when the
actual family-level valuation and complete key's parameter prefix match.
A retained recursive field supplies that guard on each of its semantic
telescope paths. Its original value therefore transports to the target
field without a global inclusion of the restricted frame in that target.
No target closure or semantic normalization assumption is used here.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.EvalPlanNormalSlice
open Rcic.Declarative PiIndex RawFamily RawFamilyRec

def Predicate (nu np : Nat) (σ : Nat → Nat) (ps : List PSet.{4})
    (D : Frame) (vs : List Nat) (i : Index.{4}) (z : PSet.{4}) : Prop :=
  (∀ u, u < nu → σ u = σOf vs u) →
  paramKey np i = key ps → z ∈ D vs i

def GuardedSub (nu np : Nat) (σ : Nat → Nat) (ps : List PSet.{4})
    (C D : Frame) : Prop :=
  ∀ vs i z, z ∈ C vs i → Predicate nu np σ ps D vs i z

/-- Complete family application needs inclusion only at the key actually
being read. Nonfitting applications are empty on the source side. -/
theorem application_sub_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C D : Frame) (hC : Admissible fd C) (hD : Admissible fd D)
    (vs : List Nat) (xs : List PSet.{4})
    (hl : xs.length = (fd.params ++ fd.indices).length)
    (hsub : Sub (C vs (key xs)) (D vs (key xs))) :
    Sub (Ed (mkM P μ) (fapps (ofFrame P μ fd C vs) xs))
      (Ed (mkM P μ) (fapps (ofFrame P μ fd D vs) xs)) := by
  cases P.dec (TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 xs) with
  | isTrue hf =>
      intro z hz
      exact mem_congr_right (apply_ofFrame_ed P μ fd D hD vs xs hf).symm
        (hsub z (mem_congr_right (apply_ofFrame_ed P μ fd C hC vs xs hf) hz))
  | isFalse hf =>
      have he := fapps_fam_nofit P μ fd (σOf vs)
        (endValue_resp C vs (fd.params.length + fd.indices.length)) xs hl hf
      intro z hz
      exact (not_mem_pempty (mem_congr_right
        ((ed_congr (mkM P μ) he).trans (ed_pempty (mkM P μ))) hz)).elim

/-- The plan's literal parameter locals identify every reached full key's
prefix, even when recursive domains depend on earlier ordinary fields. -/
theorem parameter_key (M : Interp.{4}) (σ : Nat → Nat)
    {E : ResolvedEnv} {fuel f nu np ni prior inner : Nat} {A : Expr Nat}
    (r : EvalPlan.Recursive E fuel f nu np ni prior A inner)
    (ps pre : List PSet.{4}) (hps : ps.length = np) (hpre : pre.length = prior)
    (zs : List PSet.{4}) (hzs : zs.length = r.domains.length) :
    paramKey np (key (r.arguments.map
      (den M σ (push zs (push pre (push ps ρ0)))))) = key ps := by
  change key ((r.arguments.map
    (den M σ (push zs (push pre (push ps ρ0))))).take np) = key ps
  rw [← List.map_take]
  apply congrArg key
  obtain ⟨ix, ha, _⟩ := r.parameter_prefix
  rw [ha]
  simpa only [hps, hpre, hzs] using
    PiRawParams.param_prefix M σ ps pre zs ρ0 ix

/-- On an actual retained recursive field, the guard is produced at each
telescope leaf. The full argument list is kept; only its parameter prefix
is used to discharge the induction predicate's guard. -/
theorem recursive_sub_of_guarded (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C D : Frame) (hC : Admissible fd C) (hD : Admissible fd D)
    (σ : Nat → Nat)
    {E : ResolvedEnv} {fuel nu prior inner : Nat} {A : Expr Nat}
    (r : EvalPlan.Recursive E fuel fd.fref nu fd.params.length fd.indices.length
      prior A inner)
    (ps pre : List PSet.{4}) (hps : ps.length = fd.params.length)
    (hpre : pre.length = prior)
    (hsub : GuardedSub nu fd.params.length σ ps C D) :
    Sub (Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) σ (push pre (push ps ρ0))
        (policyPi r.domains (foldApps (.const fd.fref (canonL nu)) r.arguments))))
      (Ed (mkM P (table P μ fd D))
        (den (mkM P (table P μ fd D)) σ (push pre (push ps ρ0))
          (policyPi r.domains (foldApps (.const fd.fref (canonL nu)) r.arguments)))) := by
  let X := ofFrame P μ fd C
  let Y := ofFrame P μ fd D
  let M := mkM P μ
  let ρ := push pre (push ps ρ0)
  let t := PiSyntaxCompile.compile M σ (PiIndependent.leafArgs P μ σ r.arguments)
    r.domains ρ
  have hcan : ∀ u, u < nu → σ u = σOf ((canonL nu).map (evalTotal σ)) u := by
    intro u hu
    symm
    have hlen : u < ((canonL nu).map (evalTotal σ)).length := by
      simpa only [canonL, List.length_map, List.length_range] using hu
    change ((canonL nu).map (evalTotal σ)).getD u 0 = σ u
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    simp only [Option.getD_some, canonL, List.getElem_map, List.getElem_range, evalTotal]
  intro x hx
  have hxT := mem_congr_right
    (PiIndependent.recursiveField_ed P μ fd.fref X σ (canonL nu)
      r.domains r.arguments r.domains_free r.arguments_free ρ).symm hx
  rw [t.erasedType_tables P (upd μ fd.fref X) μ] at hxT
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains M σ _ r.domains ρ
  have hyT := t.erasedType_mono_on M ht
    (fun xs => Ed M (fapps (X ((canonL nu).map (evalTotal σ))) xs))
    (fun xs => Ed M (fapps (Y ((canonL nu).map (evalTotal σ))) xs))
    (fun _ => dich_ed M _) (fun _ => dich_ed M _) (fun path => ?_) x hxT
  · rw [← t.erasedType_tables P (upd μ fd.fref Y) μ] at hyT
    exact mem_congr_right
      (PiIndependent.recursiveField_ed P μ fd.fref Y σ (canonL nu)
        r.domains r.arguments r.domains_free r.arguments_free ρ) hyT
  · obtain ⟨zs, hzs, hresult⟩ := PiSyntaxCompile.result_fits M σ
      (PiIndependent.leafArgs P μ σ r.arguments) r.domains ρ path
    apply application_sub_at P μ fd C D hC hD
      ((canonL nu).map (evalTotal σ)) (t.result path)
    · rw [hresult]
      exact (List.length_map _ _).trans
        (by simpa only [List.length_append] using r.argument_count)
    · intro z hz
      have hp : paramKey fd.params.length (key (t.result path)) = key ps := by
        rw [hresult]
        exact parameter_key M σ r ps pre hps hpre zs hzs.length
      exact hsub _ _ z hz hcan hp

/-- The induction restriction itself supplies the guarded comparison. It
need not be included in the target at keys outside the guard. -/
theorem recursive_sub (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (N D : Frame) (hN : Admissible fd N) (hD : Admissible fd D)
    (σ : Nat → Nat)
    {E : ResolvedEnv} {fuel nu prior inner : Nat} {A : Expr Nat}
    (r : EvalPlan.Recursive E fuel fd.fref nu fd.params.length fd.indices.length
      prior A inner)
    (ps pre : List PSet.{4}) (hps : ps.length = fd.params.length)
    (hpre : pre.length = prior) :
    let R := restrict N (Predicate nu fd.params.length σ ps D)
    Sub (Ed (mkM P (table P μ fd R))
      (den (mkM P (table P μ fd R)) σ (push pre (push ps ρ0))
        (policyPi r.domains (foldApps (.const fd.fref (canonL nu)) r.arguments))))
      (Ed (mkM P (table P μ fd D))
        (den (mkM P (table P μ fd D)) σ (push pre (push ps ρ0))
          (policyPi r.domains (foldApps (.const fd.fref (canonL nu)) r.arguments)))) := by
  dsimp only
  apply recursive_sub_of_guarded P μ fd
    (restrict N (Predicate nu fd.params.length σ ps D)) D
    (restrict_admissible P fd N hN _) hD σ r ps pre hps hpre
  intro vs i z hz hlevel hparam
  obtain ⟨a, hq, he⟩ := mem_sep.mp hz
  exact mem_congr_left he (hq hlevel hparam)

end Rcic.F3.PSet.EvalPlanNormalSlice
