import rcic.RcicF3RawFamilyIHBuilder
import rcic.RcicF3RawFamilyMember
import rcic.RcicF3RawFamilyViewAttack
/-! Actual height-omega field in the repaired frame, with a data-valued motive
at an extra universe parameter. Admission, ordinary environment soundness,
inserted binders and the local guarded map are paid at this fixture.
This does not produce universal A soundness. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyIHBuilderAttack
open Rcic.Declarative PiIndex RawFamily
open PendAWBridge (fd)
def σ : Nat → Nat := σOf [1]
def env : ResolvedEnv := extendEnv emptyEnv 4 PendAW.fam
def model (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : Interp.{4} :=
  mkM P (table P μ fd (frame P μ fd))
def target (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : PSet.{4} :=
  frame P μ fd [] (key [tyv fxS])
def major : Expr Nat := .app (.const 4 []) (.bvar 0)
def motive (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : PSet.{4} :=
  piLam (model P μ) σ (fun _ => tyv (target P μ)) (push [tyv fxS] ρ0)
    (.pi major (.sort (.param 0)))
def x (P : Premises4) : PSet.{4} := graphOf (fxDomBig P) (fxhW P)
def context (P : Premises4) (μ : Nat → List Nat → PSet.{4}) : Nat → PSet.{4} :=
  vcons (x P) (push [motive P μ] (push [tyv fxS] ρ0))
/-- Elementary extra motive level: the family has arity zero. -/
theorem extra_level : (canonL 0).map (evalTotal σ) = [] ∧ σ 0 = 1 ∧ σ 0 ≠ σOf [] 0 := by
  decide
/-- Ordinary stored type facts; no raw recursor soundness is assumed. -/
theorem type_facts : TypeFacts env := by
  apply typeFacts_extend (typeFacts_of_envWfT .empty)
  exact ⟨fun _ => rfl, rfl, fun _ h => nomatch h⟩
theorem sound (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    EnvSound (model P μ) σ (fun _ => 0) env 0 := by
  have shape : ∀ r m, env.members r = some m → r = 4 ∧ m = PendAW.fam := by
    intro r m hm
    by_cases hr : r = 4
    · subst r
      change (extendEnv emptyEnv 4 PendAW.fam).members 4 = some m at hm
      rw [members_extend_eq] at hm
      exact ⟨rfl, (Option.some.inj hm).symm⟩
    · change (extendEnv emptyEnv 4 PendAW.fam).members r = some m at hm
      rw [members_extend_ne emptyEnv 4 PendAW.fam r hr] at hm
      cases hm
  apply envSound_of_allSound P (μ := table P μ fd (frame P μ fd))
    (K := fun _ => 0) (E := env) ?_ ?_ σ 0
  · intro r m hm
    obtain ⟨hr, hm⟩ := shape r m hm
    subst r; subst m
    exact family_member_sound P μ fd (frame P μ fd) (RawWFrame.raw_admissible P μ)
      RawFamilyViewAttack.w_family_free (fun _ => 0) PendAW.fam rfl
      (fun _ => rfl) rfl rfl
  · intro r m hm
    obtain ⟨_, hm⟩ := shape r m hm
    subst m
    exact ⟨fun h => MemberClass.noConfusion h, fun h => MemberClass.noConfusion h⟩
theorem target_type (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    tyv (target P μ) ∈ U W4 1 := by
  obtain ⟨i, hi⟩ := (RawWFrame.raw_admissible P μ [] (key [tyv fxS])).1
  exact mem_sImage_tyv.mpr ⟨target P μ, mem_sep.mpr
    ⟨i, (dich_congr hi.symm).mp (admissible_dich (RawWFrame.raw_admissible P μ) [] _), hi⟩,
    Equiv.rfl⟩

theorem motive_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    motive P μ ∈ Ed (model P μ) (den (model P μ) σ (push [tyv fxS] ρ0)
      (.pi major (.sort (.param 0)))) := by
  refine piLam_mem (model P μ) σ (envResp_const _) _ _ ?_
  change PiGood (model P μ) σ (fun _ => tyv (target P μ)) _
    (policyPi [major] (.sort (.param 0)))
  apply piGood_policyPi
  intro ρ
  exact mem_congr_right (ed_tyv (model P μ) (U4_dich 1)).symm (target_type P μ)

theorem field_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    x P ∈ Ed (model P μ) (den (model P μ) σ (context P μ)
      (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 PendAW.field))) := by
  change x P ∈ Ed (model P μ) (den (model P μ) σ
    (vcons (x P) (vcons (motive P μ) (push [tyv fxS] ρ0))) _)
  rw [den_lift01, den_lift01,
    den_levels_closed (model P μ) σ fxσ PendAW.field rfl]
  exact RawFamilyViewAttack.omega_field P μ

theorem member_key (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (i : Index.{4}) (y : PSet.{4})
    (hp : RawFamilyRec.paramKey 1 i = key [tyv fxS])
    (hy : y ∈ frame P μ fd [] i) : i = key [tyv fxS] := by
  obtain ⟨j, ps, xs, hps, _, _, hi, _⟩ := RawFamilyInductionAttack.w_dense P μ [] i y hy
  have hidx : ∀ j : Fin fd.ctors.length, (fd.ctors.get j).2 = [] := by decide
  rw [hidx, List.map_nil, List.append_nil] at hi
  subst i
  have hl : ps.length = 1 := hps.length
  change key (ps.take 1) = key [tyv fxS] at hp
  rw [← hl, List.take_length] at hp
  exact hp

theorem map_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (i : Index.{4}) (y : PSet.{4})
    (hp : RawFamilyRec.paramKey 1 i = key [tyv fxS])
    (hy : y ∈ frame P μ fd [] i) :
    y ∈ PiRawMotiveAny.guarded (model P μ) σ 1 ((model P μ).μ 4 [])
      (motive P μ) [tyv fxS] [] (push [tyv fxS] ρ0) i y := by
  have hi := member_key P μ i y hp hy
  subst i
  have hz : y ∈ Ed (model P μ) (fapps ((model P μ).μ 4 []) [tyv fxS]) :=
    (apply_updated_mem_iff P μ fd (frame P μ fd) (RawWFrame.raw_admissible P μ)
      RawFamilyViewAttack.w_family_free [] [tyv fxS] rfl y).mpr
      ⟨PendAWBridge.argsFit P (table P μ fd (frame P μ fd)) pempty, hy⟩
  have hm : Equiv (fapps (motive P μ) [y]) (tyv (target P μ)) :=
    fapps_piLam (model P μ) σ (envResp_const _) (.sort (.param 0))
      [major] (push [tyv fxS] ρ0) [y] ⟨hz, True.intro⟩
  have hT : fapps (motive P μ) [y] ∈ (model P μ).U 1 :=
    mem_congr_left hm.symm (target_type P μ)
  have he := PiRawMotiveAny.guarded_key (model P μ) σ 1 ((model P μ).μ 4 [])
    (motive P μ) [tyv fxS] [] (push [tyv fxS] ρ0) [] y True.intro hz hT
  exact mem_congr_right he.symm
    (mem_congr_right ((ed_congr (model P μ) hm).trans
      (ed_tyv (model P μ) (admissible_dich (RawWFrame.raw_admissible P μ) [] _))).symm hy)

/-- Elementary executable admission, instance-bound and body checks. -/
theorem checks :
    fieldAnalyze env 16 4 0 1 0 1 PendAW.field = .permitted (.recursive 1) [] ∧
    InstOK env σ (fun _ => 0)
      (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 1 PendAW.field)) ∧
    BodiesOK env σ (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [fieldAnalyze, PendAW.field, piTelescopeFuel, whnfFuel, appsSpine,
      transparentBody, env, members_extend_eq, PendAW.fam, transparent,
      domainsContainFuel, containsFamilyFuel, properFamilyFuel, exactParamLocals,
      indicesCleanFuel, familyIdx]
  · intro r ls hr
    change (r, ls) ∈ ([] ++ ([(4, [])] ++ [])) at hr
    simp only [List.nil_append, List.append_nil] at hr
    cases List.mem_singleton.mp hr
    exact ⟨PendAW.fam, members_extend_eq _ _ _, rfl,
      fun _ h => (List.not_mem_nil _ h).elim⟩
  · intro r m b ls hm hb
    by_cases hr : r = 4
    · subst r
      change (extendEnv emptyEnv 4 PendAW.fam).members 4 = some m at hm
      rw [members_extend_eq] at hm
      cases Option.some.inj hm
      cases hb
    · change (extendEnv emptyEnv 4 PendAW.fam).members r = some m at hm
      rw [members_extend_ne emptyEnv 4 PendAW.fam r hr] at hm
      cases hm

/-- Actual infinite W field, nonempty data motive at the extra motive universe,
original field admission, two inserted binders and executable IH membership.
Premises4 is retained; this is an IH instance, not a universal A producer. -/
theorem inhabited (P : Premises4) (μ : Nat → List Nat → PSet.{4}) :
    ∃ ih, funIHType env 15 1 (Rcic.Declarative.lift 0 1 PendAW.field)
      (.bvar 0) 1 = some ih ∧
      ihAtN (fun y => y) 1 (x P) ∈ Ed (model P μ) (den (model P μ) σ (context P μ) ih) := by
  exact RawFamilyIH.admitted_builder_mem P μ fd (frame P μ fd)
    (RawWFrame.raw_admissible P μ) σ (fun _ => 0) 0 PendAWLim.Typed.bounded
    RawFamilyViewAttack.w_family_free (by decide)
    (.param 0) [tyv fxS] [motive P μ] rfl (motive P μ) (x P) (fxZW P)
    (fun y => y) (fun _ _ h => h) (motive_mem P μ)
    (fun i y hp _ hy => map_mem P μ i y hp hy) env 0 type_facts (sound P μ)
    checks.2.2 16 1 0 0 1 PendAW.field (.bvar 0) [] (Nat.le_refl 0) rfl
    checks.1 checks.2.1 rfl (field_mem P μ) (memT_dataVal (by simp [fxZW, x]))
end Rcic.F3.PSet.RawFamilyIHBuilderAttack
