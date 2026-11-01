import rcic.RcicF3PiSmallTuple
import rcic.RcicF3PiSmallValue
import rcic.RcicF3DeltaNormalize

/-!
# Conditional recursive telescope compilation at exact small stages

The supplied field value is preserved while every branch address is moved
to the selected small universe. Smallness is required only of that value.
At an oversized domain the value must be proof-erased, so the empty fallback
is sound. The normalized-entry theorem obtains value-smallness from the
literal field-domain stage and composes the all-universe delta equations.

This is forward compression. It neither asserts reverse field fidelity nor
constructs a candidate-independent constructor shape or fixed output key.
The exact W4 wrappers use only the corresponding Premises4 choice fields.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallRecursive
open Rcic.Declarative
open PiSmallTuple (rep rep_spec)
universe u v w

noncomputable def widen {I : Type w} :
    {m : Nat} → RecTel.{u,w} I m → RecTel.{max (u+1) v,w} I m
  | _, .ret i => .ret i
  | _, .pi A B => .pi (lift.{u,max (u+1) v} A)
      (fun q => widen (B (FBrDown.{u,max (u+1) v} A q)))

theorem classValue_lift (A : PSet.{u})
    (q : FBr (lift.{u,max (u+1) v} A)) :
    Equiv (lift.{u,max (u+1) v}
      (PiCompile.classValue A (FBrDown.{u,max (u+1) v} A q)))
      (PiCompile.classValue (lift.{u,max (u+1) v} A) q) := by
  refine Quotient.inductionOn q ?_
  intro i
  rw [FBrDown_mk]
  exact (lift_equiv.{u,max (u+1) v}
    (PiCompile.classValue_at A (liftIdxDown A i))).trans
    ((liftIdxDown_eq A i).symm.trans
      (PiCompile.classValue_at (lift.{u,max (u+1) v} A) i).symm)

/-- Actual decoded arguments are passed to the remaining dependent syntax.
The arbitrary result label may retain the complete parameter/index key. -/
noncomputable def compile {I : Type w} (M : Interp.{max (u+1) v})
    (ch : Choice.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{max (u+1) v}) → I) :
    (ds : List (Expr Nat)) → (Nat → PSet.{max (u+1) v}) → RecTel.{u,w} I ds.length
  | [], ρ => .ret (R ρ)
  | A :: ds, ρ =>
      let D := rep.{u,v} M ch (Ed M (den M σ ρ A))
      .pi D (fun q => compile M ch σ R ds
        (vcons (lift.{u,max (u+1) v} (PiCompile.classValue D q)) ρ))

theorem lifted_rep_dich (M : Interp.{max (u+1) v}) (ch : Choice.{u})
    (D : PSet.{max (u+1) v}) (hD : Dich D) :
    Dich (lift.{u,max (u+1) v} (rep.{u,v} M ch D)) := by
  cases hd : M.dec (Small.{u,max (u+1) v} D) with
  | isTrue hs => exact (dich_congr (rep_spec.{u,v} M ch D hs)).mp hD
  | isFalse hs =>
      have he : rep.{u,v} M ch D = pempty := by
        unfold rep
        rw [dif_neg hs]
      rw [he]
      exact (dich_congr lift_pempty_equiv).mpr
        (Or.inl (fun _ hz => (not_mem_pempty hz).elim))

theorem compile_domains {I : Type w} (M : Interp.{max (u+1) v})
    (ch : Choice.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{max (u+1) v}) → I) :
    ∀ ds ρ, (widen.{u,v,w} (compile.{u,v,w} M ch σ R ds ρ)).DomainsDich
  | [], _ => True.intro
  | A :: ds, ρ =>
      ⟨lifted_rep_dich.{u,v} M ch (Ed M (den M σ ρ A)) (dich_ed M _),
        fun _ => compile_domains M ch σ R ds _⟩

/-- Every small path decodes to actual fitting arguments, and its label
is the unchanged reader applied to the complete extended environment. -/
theorem result_fits {I : Type w} (M : Interp.{max (u+1) v})
    (ch : Choice.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{max (u+1) v}) → I) : ∀ ds ρ p,
    ∃ xs, TelFits M σ ds ρ xs ∧
      (compile.{u,v,w} M ch σ R ds ρ).result p = R (push xs ρ) := by
  intro ds
  induction ds with
  | nil => intro ρ p; exact ⟨[], True.intro, rfl⟩
  | cons A ds ih =>
      intro ρ p
      let D := Ed M (den M σ ρ A)
      let S := rep.{u,v} M ch D
      let a := lift.{u,max (u+1) v} (PiCompile.classValue S p.1)
      have hs := PiSmallTuple.small_of_rep_mem.{u,v} M ch D p.1
      have ha : a ∈ D := mem_congr_right (rep_spec.{u,v} M ch D hs).symm
        (lift_mem_lift.{u,max (u+1) v}.mpr (PiCompile.classValue_mem S p.1))
      obtain ⟨xs, hx, he⟩ := ih (vcons a ρ) p.2
      exact ⟨a :: xs, ⟨ha, hx⟩, he⟩

/-- The actual field value enters the small telescope. This does not need
the original domains to be small at branches the value cannot inhabit. -/
theorem compile_mem {I : Type w} (M : Interp.{max (u+1) v})
    (ch : Choice.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{max (u+1) v}) → I) (X : I → PSet.{max (u+1) v})
    (hX : ∀ i, Dich (X i)) (b : Expr Nat)
    (hL : ∀ ρ, Equiv (X (R ρ)) (Ed M (den M σ ρ b))) :
    ∀ ds ρ (g : PSet.{max (u+1) v}), Small.{u,max (u+1) v} g →
      g ∈ Ed M (den M σ ρ (policyPi ds b)) →
      g ∈ Ed M ((widen.{u,v,w} (compile.{u,v,w} M ch σ R ds ρ)).erasedType M X) := by
  intro ds
  induction ds with
  | nil =>
      intro ρ g _ hg
      exact mem_congr_right
        ((hL ρ).symm.trans (ed_tyv M (hX (R ρ))).symm) hg
  | cons A ds ih =>
      intro ρ g hg hf
      let D := Ed M (den M σ ρ A)
      let S := rep.{u,v} M ch D
      let T := lift.{u,max (u+1) v} S
      let B := fun a => den M σ (vcons a ρ) (policyPi ds b)
      let C := fun a => tyv (classFiber T (fun q =>
        Ed M ((widen.{u,v,w} (compile.{u,v,w} M ch σ R ds
          (vcons (lift.{u,max (u+1) v}
            (PiCompile.classValue S (FBrDown.{u,max (u+1) v} S q))) ρ))).erasedType M X)) a)
      have hB : ∀ a a', Equiv a a' → Equiv (B a) (B a') :=
        fun _ _ h => den_congr M σ _ (vcons_congr h (fun _ => Equiv.rfl))
      have hC : ∀ a a', Equiv a a' → Equiv (C a) (C a') :=
        fun _ _ h => tyv_congr (classFiber_congr T _ h)
      change g ∈ Ed M (piVal M (tyv T) C)
      cases hd : M.dec (Small.{u,max (u+1) v} D) with
      | isTrue hSmall =>
          have e : Equiv D T := rep_spec.{u,v} M ch D hSmall
          have hT : Dich T := (dich_congr e).mp (dich_ed M _)
          have eD : Equiv (Ed M (tyv T)) D := (ed_tyv M hT).trans e.symm
          have hmem : lamVal M (tyv T) (fun a => fapp g a) ∈
              Ed M (piVal M (tyv T) C) := by
            apply lam_mem M (fun _ _ h => fapp_congr Equiv.rfl h) hC
            intro z hz
            have hzT : z ∈ T := mem_congr_right (ed_tyv M hT) hz
            obtain ⟨i, hi⟩ := hzT
            let q := Quotient.mk (FSetoid T) i
            let r := FBrDown.{u,max (u+1) v} S q
            let z' := lift.{u,max (u+1) v} (PiCompile.classValue S r)
            have hz'T : z' ∈ T :=
              lift_mem_lift.{u,max (u+1) v}.mpr (PiCompile.classValue_mem S r)
            have hz'D : z' ∈ D := mem_congr_right e.symm hz'T
            have ev : Equiv z' z := (classValue_lift.{u,v} S q).trans
              ((PiCompile.classValue_at T i).trans hi)
            have hf' := app_mem M hB hf hz'D
            have hr := ih (vcons z' ρ) (fapp g z') (PiSmallValue.fapp_small.{u,max (u+1) v} hg) hf'
            have ef := (classFiber_congr T (fun q => Ed M
              ((widen.{u,v,w} (compile.{u,v,w} M ch σ R ds
                (vcons (lift.{u,max (u+1) v}
                  (PiCompile.classValue S (FBrDown.{u,max (u+1) v} S q))) ρ))).erasedType M X))
              hi.symm).trans (classFiber_at T _ i)
            have ec : Equiv (Ed M (C z))
                (Ed M ((widen.{u,v,w} (compile.{u,v,w} M ch σ R ds (vcons z' ρ))).erasedType M X)) :=
              (ed_tyv M ((dich_congr ef).mpr (dich_ed M _))).trans ef
            exact mem_congr_right ec.symm
              (mem_congr_left (fapp_congr Equiv.rfl ev) hr)
          have elam := (PiSmallValue.lamVal_ed_domain.{u,max (u+1) v}
            M (fun a => fapp g a) (fun _ _ h => fapp_congr Equiv.rfl h) eD).trans
            (eta_val M hB hf)
          exact mem_congr_left elam hmem
      | isFalse hSmall =>
          have eg : Equiv g pempty := by
            cases he : M.dec (Equiv g pempty) with
            | isTrue h => exact h
            | isFalse h => exact (hSmall (PiSmallValue.domain_small.{u,max (u+1) v} M hB hg hf h)).elim
          have eS : S = pempty := by
            unfold S rep
            rw [dif_neg hSmall]
          have eT : Equiv T pempty := by
            change Equiv (lift.{u,max (u+1) v} S) pempty
            rw [eS]
            exact lift_pempty_equiv
          have hT : Dich T := (dich_congr eT).mpr
            (Or.inl (fun _ h => (not_mem_pempty h).elim))
          have hnone : ∀ a, a ∈ Ed M (tyv T) → False :=
            fun _ ha => not_mem_pempty
              (mem_congr_right ((ed_tyv M hT).trans eT) ha)
          have hp : PiProp M (tyv T) C := fun a ha => (hnone a ha).elim
          have et := ed_piVal M (tyv T) C hC
          rw [cond_pos hp] at et
          exact mem_congr_right et.symm
            (mem_tv.mpr ⟨fun a ha => (hnone a ha).elim, eg⟩)

/-- Compose inhabited normalization and conditional small compression.
The exact stage bounds the original field domain, as in SmallAlong. -/
theorem normalized_mem {I : Type w} (M : Interp.{max (u+1) v})
    (ch : Choice.{u}) (E : ResolvedEnv) (σ : Nat → Nat)
    (hδ : DeltaNormalize.BodyEquations M E σ)
    (R : (Nat → PSet.{max (u+1) v}) → I) (X : I → PSet.{max (u+1) v})
    (hX : ∀ i, Dich (X i)) (b : Expr Nat)
    (hL : ∀ ρ, Equiv (X (R ρ)) (Ed M (den M σ ρ b)))
    (fuel : Nat) (T : Expr Nat) (ds : List (Expr Nat))
    (ρ : Nat → PSet.{max (u+1) v}) (g : PSet.{max (u+1) v})
    (hr : piTelescopeFuel E fuel T = some (ds, b))
    (hstage : Ed M (den M σ ρ T) ∈ univIn.{u,v})
    (hg : g ∈ Ed M (den M σ ρ T)) :
    g ∈ Ed M ((widen.{u,v,w} (compile.{u,v,w} M ch σ R ds ρ)).erasedType M X) := by
  have hs := small_of_mem_small (mem_univIn.{u,v}.mp hstage) hg
  have he := DeltaNormalize.telescope_of_mem M E σ hδ fuel T ds b ρ g hr hg
  exact compile_mem.{u,v,w} M ch σ R X hX b hL ds ρ g hs
    (mem_congr_right (ed_congr M he).symm hg)

theorem normalized_mem_stage_one {I : Type w} (P : Premises4)
    (M : Interp.{4}) (E : ResolvedEnv) (σ : Nat → Nat)
    (hδ : DeltaNormalize.BodyEquations M E σ)
    (R : (Nat → PSet.{4}) → I) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (b : Expr Nat) (hL : ∀ ρ, Equiv (X (R ρ)) (Ed M (den M σ ρ b)))
    (fuel : Nat) (T : Expr Nat) (ds : List (Expr Nat)) (ρ : Nat → PSet.{4})
    (g : PSet.{4}) (hr : piTelescopeFuel E fuel T = some (ds, b))
    (hstage : Ed M (den M σ ρ T) ∈ W4 1) (hg : g ∈ Ed M (den M σ ρ T)) :
    g ∈ Ed M ((widen.{0,4,w} (compile.{0,4,w} M P.c0 σ R ds ρ)).erasedType M X) :=
  normalized_mem.{0,4,w} M P.c0 E σ hδ R X hX b hL fuel T ds ρ g hr hstage hg

theorem normalized_mem_stage_two {I : Type w} (P : Premises4)
    (M : Interp.{4}) (E : ResolvedEnv) (σ : Nat → Nat)
    (hδ : DeltaNormalize.BodyEquations M E σ)
    (R : (Nat → PSet.{4}) → I) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (b : Expr Nat) (hL : ∀ ρ, Equiv (X (R ρ)) (Ed M (den M σ ρ b)))
    (fuel : Nat) (T : Expr Nat) (ds : List (Expr Nat)) (ρ : Nat → PSet.{4})
    (g : PSet.{4}) (hr : piTelescopeFuel E fuel T = some (ds, b))
    (hstage : Ed M (den M σ ρ T) ∈ W4 2) (hg : g ∈ Ed M (den M σ ρ T)) :
    g ∈ Ed M ((widen.{1,4,w} (compile.{1,4,w} M P.c1 σ R ds ρ)).erasedType M X) :=
  normalized_mem.{1,4,w} M P.c1 E σ hδ R X hX b hL fuel T ds ρ g hr hstage hg

theorem normalized_mem_stage_three {I : Type w} (P : Premises4)
    (M : Interp.{4}) (E : ResolvedEnv) (σ : Nat → Nat)
    (hδ : DeltaNormalize.BodyEquations M E σ)
    (R : (Nat → PSet.{4}) → I) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (b : Expr Nat) (hL : ∀ ρ, Equiv (X (R ρ)) (Ed M (den M σ ρ b)))
    (fuel : Nat) (T : Expr Nat) (ds : List (Expr Nat)) (ρ : Nat → PSet.{4})
    (g : PSet.{4}) (hr : piTelescopeFuel E fuel T = some (ds, b))
    (hstage : Ed M (den M σ ρ T) ∈ W4 3) (hg : g ∈ Ed M (den M σ ρ T)) :
    g ∈ Ed M ((widen.{2,4,w} (compile.{2,4,w} M P.c2 σ R ds ρ)).erasedType M X) :=
  normalized_mem.{2,4,w} M P.c2 E σ hδ R X hX b hL fuel T ds ρ g hr hstage hg

theorem normalized_mem_stage_four_plus {I : Type w} (P : Premises4)
    (M : Interp.{4}) (E : ResolvedEnv) (σ : Nat → Nat)
    (hδ : DeltaNormalize.BodyEquations M E σ)
    (R : (Nat → PSet.{4}) → I) (X : I → PSet.{4}) (hX : ∀ i, Dich (X i))
    (b : Expr Nat) (hL : ∀ ρ, Equiv (X (R ρ)) (Ed M (den M σ ρ b)))
    (k fuel : Nat) (T : Expr Nat) (ds : List (Expr Nat)) (ρ : Nat → PSet.{4})
    (g : PSet.{4}) (hr : piTelescopeFuel E fuel T = some (ds, b))
    (hstage : Ed M (den M σ ρ T) ∈ W4 (k + 4)) (hg : g ∈ Ed M (den M σ ρ T)) :
    g ∈ Ed M ((widen.{3,4,w} (compile.{3,4,w} M P.c3 σ R ds ρ)).erasedType M X) :=
  normalized_mem.{3,4,w} M P.c3 E σ hδ R X hX b hL fuel T ds ρ g hr hstage hg

end Rcic.F3.PSet.PiSmallRecursive
