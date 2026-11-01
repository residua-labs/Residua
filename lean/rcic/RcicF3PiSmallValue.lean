import rcic.RcicF3PiSmallField
import rcic.RcicF3PiIndependentField
/-! Actual small field values enter the independent small telescope after
inhabited normalization. Only forward membership is asserted here;
full type agreement and universal group closure remain separate.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallValue
universe u v
theorem fapp_small {g a : PSet.{max u v}} (hg : Small.{u,v} g) :
    Small.{u,v} (fapp g a) := by
  exact small_sUnion (small_sep (small_sUnion (small_sUnion hg)) _)
theorem domain_small (M : Interp.{max u v}) {A g : PSet.{max u v}}
    {B : PSet.{max u v} → PSet.{max u v}}
    (hB : ∀ a a', Equiv a a' → Equiv (B a) (B a'))
    (hg : Small.{u,v} g) (hf : g ∈ Ed M (piVal M A B))
    (hne : ¬ Equiv g pempty) : Small.{u,v} (Ed M A) := by
  have hf' := mem_congr_right (ed_piVal M A B hB) hf
  cases hd : M.dec (PiProp M A B) with
  | isTrue hP =>
    rw [cond_pos hP] at hf'
    exact (hne (mem_tv.mp hf').2).elim
  | isFalse hP =>
    rw [cond_neg hP] at hf'
    have hfun := isFuncOnDep_of_mem_piSet (fun _ _ h => ed_congr M (hB _ _ h)) hf'
    apply small_subset (small_sUnion (small_sUnion hg))
    intro a ha
    obtain ⟨b, _, hab⟩ := hfun.1 a ha
    exact mem_sUnion_sUnion_of_pair_left hab
theorem lamVal_ed_domain (M : Interp.{max u v}) {A A' : PSet.{max u v}}
    (b : PSet.{max u v} → PSet.{max u v})
    (hb : ∀ x x', Equiv x x' → Equiv (b x) (b x')) (hA : Equiv (Ed M A) (Ed M A')) :
    Equiv (lamVal M A b) (lamVal M A' b) := by
  exact cond_congr ⟨fun h x hx => h x (mem_congr_right hA.symm hx),
    fun h x hx => h x (mem_congr_right hA hx)⟩ Equiv.rfl
    (mkLam_congr_on hb hA (fun _ _ => Equiv.rfl))
open Rcic.Declarative
open PiSmallCompile
universe w
/-- Forward compression of actual small values; no reverse fidelity claim. -/
theorem compile_mem {I : Type w} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (R : (Nat → PSet.{4}) → I) (X : I → PSet.{4})
    (hX : ∀ i, Dich (X i)) (b : Expr Nat)
    (hL : ∀ ρ, Equiv (X (R ρ)) (Ed (mkM P μ) (den (mkM P μ) σ ρ b))) :
    ∀ ds ρ (g : PSet.{4}), Small.{3,4} g →
      g ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ (policyPi ds b)) →
      g ∈ Ed (mkM P μ) ((widen (compile P μ σ R ds ρ)).erasedType (mkM P μ) X) := by
  intro ds
  induction ds with
  | nil =>
    intro ρ g _ hg
    exact mem_congr_right ((hL ρ).symm.trans (ed_tyv (mkM P μ) (hX (R ρ))).symm) hg
  | cons A ds ih =>
    intro ρ g hg hf
    let M := mkM P μ
    let D := Ed M (den M σ ρ A)
    let S := rep P D
    let T := lift.{3,4} S
    let B := fun a => den M σ (vcons a ρ) (policyPi ds b)
    let C := fun a => tyv (classFiber T (fun q =>
      Ed M ((widen (compile P μ σ R ds
        (vcons (lift.{3,4} (PiCompile.classValue S (FBrDown.{3,4} S q))) ρ))).erasedType M X)) a)
    have hB : ∀ a a', Equiv a a' → Equiv (B a) (B a') :=
      fun _ _ h => den_congr M σ _ (vcons_congr h (fun _ => Equiv.rfl))
    have hC : ∀ a a', Equiv a a' → Equiv (C a) (C a') :=
      fun _ _ h => tyv_congr (classFiber_congr T _ h)
    change g ∈ Ed M (piVal M (tyv T) C)
    haveI := P.dec
    by_cases hSmall : Small.{3,4} D
    · have e : Equiv D T := rep_spec P D hSmall
      have hT : Dich T := (dich_congr e).mp (dich_ed M _)
      have eD : Equiv (Ed M (tyv T)) D := (ed_tyv M hT).trans e.symm
      have hmem : lamVal M (tyv T) (fun a => fapp g a) ∈ Ed M (piVal M (tyv T) C) := by
        apply lam_mem M (fun _ _ h => fapp_congr Equiv.rfl h) hC
        intro z hz
        have hzT : z ∈ T := mem_congr_right (ed_tyv M hT) hz
        obtain ⟨i, hi⟩ := hzT
        let q := Quotient.mk (FSetoid T) i
        let r := FBrDown.{3,4} S q
        let z' := lift.{3,4} (PiCompile.classValue S r)
        have hz'T : z' ∈ T := lift_mem_lift.{3,4}.mpr (PiCompile.classValue_mem S r)
        have hz'D : z' ∈ D := mem_congr_right e.symm hz'T
        have ev : Equiv z' z := (classValue_lift S q).trans
          ((PiCompile.classValue_at T i).trans hi)
        have hf' := app_mem M hB hf hz'D
        have hr := ih (vcons z' ρ) (fapp g z') (fapp_small hg) hf'
        have ef := (classFiber_congr T (fun q => Ed M
          ((widen (compile P μ σ R ds
            (vcons (lift.{3,4} (PiCompile.classValue S (FBrDown.{3,4} S q))) ρ))).erasedType M X))
          hi.symm).trans (classFiber_at T _ i)
        have ec : Equiv (Ed M (C z))
            (Ed M ((widen (compile P μ σ R ds (vcons z' ρ))).erasedType M X)) :=
          (ed_tyv M ((dich_congr ef).mpr (dich_ed M _))).trans ef
        exact mem_congr_right ec.symm (mem_congr_left (fapp_congr Equiv.rfl ev) hr)
      have elam := (lamVal_ed_domain.{3,4} M (fun a => fapp g a)
        (fun _ _ h => fapp_congr Equiv.rfl h) eD).trans (eta_val M hB hf)
      exact mem_congr_left elam hmem
    · have eg : Equiv g pempty := by
        by_cases he : Equiv g pempty
        · exact he
        · exact (hSmall (domain_small M hB hg hf he)).elim
      have eS : S = pempty := by
        unfold S rep
        rw [dif_neg hSmall]
      have eT : Equiv T pempty := by
        change Equiv (lift.{3,4} S) pempty
        rw [eS]
        exact lift_pempty_equiv
      have hT : Dich T := (dich_congr eT).mpr (Or.inl (fun _ h => (not_mem_pempty h).elim))
      have hnone : ∀ a, a ∈ Ed M (tyv T) → False :=
        fun _ ha => not_mem_pempty (mem_congr_right ((ed_tyv M hT).trans eT) ha)
      have hp : PiProp M (tyv T) C := fun a ha => (hnone a ha).elim
      have et := ed_piVal M (tyv T) C hC
      rw [cond_pos hp] at et
      exact mem_congr_right et.symm (mem_tv.mpr ⟨fun a ha => (hnone a ha).elim, eg⟩)
theorem typed_value_small (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {l : Level}
    (hE : EnvSound (mkM P μ) σ K E n) (d : HasTyT E n Γ T (.sort l))
    (hd : LOKt σ 4 K d) (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ)
    {x : PSet.{4}} (hx : x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ T)) :
    Small.{3,4} x := by
  have ht := (hsound_ty (P.good _ rfl) hE d hd).root ρ hρ
  have hu := mem_congr_right (ed_tyv (mkM P μ) (U4_dich _)) ht
  exact small_of_mem_small (ed_small P (mkM P μ) (evalTotal σ l) hu) hx
theorem normalized_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (X : List Nat → PSet.{4}) (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    (hE : EnvSound (mkM P (upd μ f X)) σ K E n) (hb : BodiesOK E σ K)
    (fuel : Nat) (T : Expr Nat) (ls : List Level) (ds args : List (Expr Nat))
    (hw : piTelescopeFuel E fuel T = some (ds, foldApps (.const f ls) args))
    (hI : InstOK E σ K T) (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false) (ρ : Nat → PSet.{4}) (x : PSet.{4})
    (hs : Small.{3,4} x)
    (hx : x ∈ Ed (mkM P (upd μ f X)) (den (mkM P (upd μ f X)) σ ρ T)) :
    let M := mkM P (upd μ f X)
    x ∈ Ed M ((widen (PiIndependent.recursiveTel P μ σ ds args ρ)).erasedType
      M (fun xs => Ed M (fapps (X (ls.map (evalTotal σ))) xs))) := by
  dsimp only
  let M := mkM P (upd μ f X)
  have hn := den_piTelescope_of_mem M σ K hE hb fuel T ds
    (foldApps (.const f ls) args) ρ x hw hI hx
  have hnmem := mem_congr_right (ed_congr M hn).symm hx
  have hm := compile_mem P (upd μ f X) σ (PiIndependent.leafArgs P μ σ args)
    (fun xs => Ed M (fapps (X (ls.map (evalTotal σ))) xs)) (fun _ => dich_ed M _)
    (foldApps (.const f ls) args) (fun ρ' => by
      rw [PiIndependent.leaf_read P μ f X σ ls args ha ρ']; exact Equiv.rfl) ds ρ x hs hnmem
  have he := PiIndependent.smallCompile_free P μ f X (μ f) σ
    (PiIndependent.leafArgs P μ σ args) ds ρ hd
  rw [PiIndependent.upd_self] at he
  rw [he] at hm
  exact hm
end Rcic.F3.PSet.PiSmallValue
