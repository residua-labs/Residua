import rcic.RcicF3PiSizedEnv
import rcic.RcicF3PiHereditaryAttack
import rcic.RcicF3PiLiveAttack
import rcic.RcicF3PiRawCtorAttack
/-! Strict small-signature regressions: real transparent definitions,
independent parameterized fields and oversized fallback refusal.
No universal group producer. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSizedAttack
open Rcic.Declarative PiHereditaryAttack PiSized

/-- Stored identity definitions pay smallness at every numeric label. -/
theorem identity_sized (P : Premises4) (K : Nat → Nat) (label : Nat) (σ : Nat → Nat) :
    BodiesSized (mkM P (envμ P (identityWfT label))) σ K (identityEnv label) := by
  obtain ⟨hB, hA, _, _⟩ := identity_conditions P K label
  have hI : ∀ r m, (identityEnv label).members r = some m →
      m.mclass = .recursorM → IotaAt P (envμ P (identityWfT label)) K (identityEnv label) r := by
    intro r m hm hk
    by_cases hr : r = label
    · subst hr
      rw [show (identityEnv r).members r = some PiSyntaxAttack.idMember from
        members_extend_eq emptyEnv r PiSyntaxAttack.idMember] at hm
      cases hm
      cases hk
    · rw [show (identityEnv label).members r = none from
        members_extend_ne emptyEnv label PiSyntaxAttack.idMember r hr] at hm
      cases hm
  exact bodiesSized_of_bound P _ K (identityWfT label) hB hA hI
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ hm hn => by rw [hm] at hn; cases hn) σ

/-- The small compiler has full raw/beta/delta/zeta fidelity on an inhabited
closed dependent product, with stored-body smallness paid internally. -/
theorem closed_small_presentations_iff (P : Premises4) (σ K : Nat → Nat)
    (label : Nat) (ρ : Nat → PSet.{4}) :
    let μ := envμ P (identityWfT label);
    let M := mkM P μ
    (∀ T ∈ [closedField, closedBeta, closedDelta label, closedZeta],
      ∀ x, x ∈ Ed M ((PiSmallCompile.widen (PiSmallCompile.compile P μ σ (PiTypedCompile.leafIndex M σ (.bvar 1))
        closedDomains ρ)).erasedType M (fun i => i.1)) ↔ x ∈ Ed M (den M σ ρ T)) ∧
      den M σ ρ closedProof ∈ Ed M (den M σ ρ closedField) := by
  let μ := envμ P (identityWfT label)
  let M := mkM P μ
  obtain ⟨hB, hA, hC, hR⟩ := identity_conditions P K label
  have hE : EnvSound M σ K (identityEnv label) 0 := envSound_of_allSound P hA hC σ 0
  have hb : BodiesOK (identityEnv label) σ K :=
    bodiesOK_of_envWfT K (identityWfT label) hB (fun _ _ h => h)
      (fun _ _ h hn => by rw [h] at hn; cases hn) σ
  have hS := identity_sized P K label σ
  have go : ∀ T, T ∈ [closedField, closedBeta, closedDelta label, closedZeta] →
      ∀ (d : HasTyT (identityEnv label) 0 [] T (.sort PiSyntaxAttack.level)),
      LOKt σ 4 K d → ∀ x,
      x ∈ Ed M ((PiSmallCompile.widen (PiSmallCompile.compile P μ σ (PiTypedCompile.leafIndex M σ (.bvar 1))
        closedDomains ρ)).erasedType M (fun i => i.1)) ↔ x ∈ Ed M (den M σ ρ T) := by
    intro T hT d hd x
    have he := compiled_field_ed P μ σ K hE hb (hR σ) hS d hd
      (closed_reads label T hT) (PiTypedCompile.leafIndex M σ (.bvar 1))
      (fun i => i.1) (fun i => i.2) (fun _ => Equiv.rfl) ρ trivial
    exact ⟨mem_congr_right he, mem_congr_right he.symm⟩
  refine ⟨?_, ?_⟩
  · intro T hT
    have ht := hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact go _ hT (closedFieldTy _) (by
        simp [closedFieldTy, LOKt, PiSyntaxAttack.level, evalTotal])
    · exact go _ hT (closedBetaTy _) (by
        simp [closedBetaTy, PiSyntaxAttack.idBodyTy, closedFieldTy, LOKt,
          PiSyntaxAttack.level, evalTotal])
    · exact go _ hT (closedDeltaTy label) (by
        simp [closedDeltaTy, closedFieldTy, LOKt, LevelsOK,
          PiSyntaxAttack.level, evalTotal])
    · exact go _ hT (closedZetaTy _) (by
        simp [closedZetaTy, closedFieldTy, LOKt, PiSyntaxAttack.level, evalTotal])
  · exact sound_ty (P.good _ rfl) hE (closedProofTy _) (by
      simp [closedProofTy, LOKt, evalTotal]) ρ trivial

/-- The untyped oversized fallback counterexample cannot meet Sized. -/
theorem oversized_not_sized (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) :
    ¬ Sized (mkM P μ) σ (policyPi [.bvar 0] (.bvar 2)) PiLiveAttack.largeAssignment := by
  intro h
  exact PiLiveAttack.large_domain_invariants.2 (Small.congr
    (ed_tyv (mkM P μ) PiLiveAttack.large_domain_invariants.1) h.2.1)

open PiRawCtorAttack
/-- Ordinary field typing under the actual parameterized-family environment. -/
def param_field_typed (f : Nat) :
    HasTyT (paramEnv f) 0 [.assumption (.sort .zero)] (paramField f)
      (.sort (.imax .zero .zero)) :=
  .pi _ _ .zero _ .zero (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl)
    (.app _ _ _ (.sort .zero) (.sort .zero)
      (.const _ f [] paramMember (members_extend_eq _ _ _) rfl rfl)
      (.bvar _ 1 (.sort .zero) rfl))
def param_beta (f : Nat) : Expr Nat :=
  .app (.lam (.sort (.imax .zero .zero)) (.bvar 0)) (paramField f)
def param_zeta (f : Nat) : Expr Nat :=
  .letE (.sort (.imax .zero .zero)) (paramField f) (.bvar 0)
def param_beta_typed (f : Nat) :
    HasTyT (paramEnv f) 0 [.assumption (.sort .zero)] (param_beta f) (.sort (.imax .zero .zero)) :=
  .app _ _ _ (.sort (.imax .zero .zero)) (.sort (.imax .zero .zero))
    (.lam _ _ _ _ _ (.sort _ (.imax .zero .zero)) (.bvar _ 0 _ rfl)) (param_field_typed f)
def param_zeta_typed (f : Nat) :
    HasTyT (paramEnv f) 0 [.assumption (.sort .zero)] (param_zeta f) (.sort (.imax .zero .zero)) :=
  .letE _ _ _ _ _ _ (.sort _ (.imax .zero .zero)) (param_field_typed f) (.bvar _ 0 _ rfl)

/-- Admission and normalized reads agree on raw and hidden presentations. -/
theorem param_presentations (f : Nat) :
    ∀ T ∈ [paramField f, param_beta f, param_zeta f],
      fieldAnalyze (paramEnv f) 8 f 0 1 0 1 T = .permitted (.recursive 1) [] ∧
      piTelescopeFuel (paramEnv f) 8 T =
        some ([.bvar 0], .app (.const f []) (.bvar 1)) := by
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl
  all_goals simp [fieldAnalyze, paramField, param_beta, param_zeta,
    piTelescopeFuel, whnfFuel, appsSpine, transparentBody, paramEnv,
    members_extend_eq, paramMember, transparent, domainsContainFuel,
    containsFamilyFuel, properFamilyFuel, exactParamLocals, indicesCleanFuel,
    familyIdx, foldApps, instantiate0, instantiate, lift]

/-- The complete admitted-field composition is inhabited under an actual
parameterized family at every numeric reference. Signature independence,
raw fidelity and actual erased membership are all exercised. -/
theorem param_admitted_exact (P : Premises4) (f : Nat) :
    let μ := PiValueRuleAttack.emptyBase;
    let X := PiValue.table P μ (paramPred P) params;
    let σ := σOf [];
    let M := mkM P (upd μ f X);
    let ρ := vcons (tyv pempty) ρ0;
    ∀ T ∈ [paramField f, param_beta f, param_zeta f],
      ∃ ds args, ds.length = 1 ∧ args.length = 1 ∧
        piTelescopeFuel (paramEnv f) 7 T = some (ds, foldApps (.const f []) args) ∧
        (∀ X₁ X₂ ρ', PiIndependent.recursiveTel P (upd μ f X₁) σ ds args ρ' =
          PiIndependent.recursiveTel P (upd μ f X₂) σ ds args ρ') ∧
        pempty ∈ Ed M ((PiSmallCompile.widen
          (PiIndependent.recursiveTel P μ σ ds args ρ)).erasedType M
          (fun xs => Ed M (fapps (X []) xs))) ∧
        Equiv (Ed M ((PiSmallCompile.widen
          (PiIndependent.recursiveTel P μ σ ds args ρ)).erasedType M
          (fun xs => Ed M (fapps (X []) xs)))) (Ed M (den M σ ρ T)) := by
  let μ := PiValueRuleAttack.emptyBase
  let X := PiValue.table P μ (paramPred P) params
  let σ := σOf []
  let M := mkM P (upd μ f X)
  let ρ := vcons (tyv pempty) ρ0
  have hB : BoundG (fun _ => 0) (EnvWfT.empty) := trivial
  have hA : AllSound P (upd μ f X) (fun _ => 0) emptyEnv := by
    intro _ _ hm; cases hm
  have hI : ∀ r m, emptyEnv.members r = some m → m.mclass = .recursorM →
      IotaAt P (upd μ f X) (fun _ => 0) emptyEnv r := by
    intro _ _ hm; cases hm
  have hfin : ∀ r m, emptyEnv.members r = some m → emptyEnv.members r = some m :=
    fun _ _ h => h
  have hsub : ∀ r m, emptyEnv.members r = some m → (paramEnv f).members r = some m := by
    intro _ _ hm; cases hm
  have hnew : ∀ r m, (paramEnv f).members r = some m → emptyEnv.members r = none →
      m.body = none := by
    intro r m hm _
    by_cases hr : r = f
    · subst r
      rw [show (paramEnv f).members f = some paramMember from members_extend_eq _ _ _] at hm
      cases hm
      rfl
    · rw [show (paramEnv f).members r = none from members_extend_ne emptyEnv f paramMember r hr] at hm
      cases hm
  have hES : EnvSound M σ (fun _ => 0) (paramEnv f) 0 := paramSound P f σ (fun _ => 0)
  have hρ : Fits M σ [.assumption (.sort .zero)] ρ :=
    ⟨trivial, tyv_pempty_mem_sort P (upd μ f X) σ ρ0 .zero⟩
  have hx : pempty ∈ Ed M (den M σ ρ (paramField f)) := (param_inhabited P f).1.2.1
  have go : ∀ T, T ∈ [paramField f, param_beta f, param_zeta f] →
      ∀ (d : HasTyT (paramEnv f) 0 [.assumption (.sort .zero)] T (.sort (.imax .zero .zero))),
      LOKt σ 4 (fun _ => 0) d →
      ∃ ds args, ds.length = 1 ∧ args.length = 1 ∧
        piTelescopeFuel (paramEnv f) 7 T = some (ds, foldApps (.const f []) args) ∧
        (∀ X₁ X₂ ρ', PiIndependent.recursiveTel P (upd μ f X₁) σ ds args ρ' =
          PiIndependent.recursiveTel P (upd μ f X₂) σ ds args ρ') ∧
        pempty ∈ Ed M ((PiSmallCompile.widen
          (PiIndependent.recursiveTel P μ σ ds args ρ)).erasedType M
          (fun xs => Ed M (fapps (X []) xs))) ∧
        Equiv (Ed M ((PiSmallCompile.widen
          (PiIndependent.recursiveTel P μ σ ds args ρ)).erasedType M
          (fun xs => Ed M (fapps (X []) xs)))) (Ed M (den M σ ρ T)) := by
    intro T hT d hd
    obtain ⟨ha, hw⟩ := param_presentations f T hT
    obtain ⟨ds, args, hl, hn, hr, hi, hs⟩ := admitted_field_exact P μ σ (fun _ => 0) f X
      .empty hB hA hI hfin hsub hnew ha (by decide) hES d hd
    have he := (hs ρ hρ).2
    have hnorm := PiHereditary.den_piTelescope_of_bound P (upd μ f X) σ (fun _ => 0)
      .empty hB hA hI hfin hsub hnew hES d hd hw ρ hρ
    have hraw : pempty ∈ Ed M (den M σ ρ T) :=
      mem_congr_right (ed_congr M hnorm) hx
    exact ⟨ds, args, hl, hn, hr, hi, mem_congr_right he.symm hraw, he⟩
  dsimp only
  intro T hT
  have ht := hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact go _ hT (param_field_typed f) (by simp [param_field_typed, LOKt, LevelsOK, evalTotal])
  · exact go _ hT (param_beta_typed f) (by
      simp [param_beta_typed, param_field_typed, LOKt, LevelsOK, evalTotal])
  · exact go _ hT (param_zeta_typed f) (by
      simp [param_zeta_typed, param_field_typed, LOKt, LevelsOK, evalTotal])
end Rcic.F3.PSet.PiSizedAttack
