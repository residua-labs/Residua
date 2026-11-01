import rcic.RcicF3PiSmallFieldAt

/-!
# Small recursive spines with a separate domain environment

The small branch topology is compiled in one model and environment, while
the actual field value and leaf membership are read in another. The exact
domain relation compares only reached Pi domains and pushes the SAME actual
argument into both environments. Terminal labels can therefore retain the
full actual constructor prefix and complete child key.

The theorem produces forward field membership from value-smallness, source
membership, reached-domain equivalence and reached-leaf inclusion. It does
not infer domain independence from admission, require terminal-key
independence, or add a hypothesis to the public StepAG target.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallMaskSpine
open Rcic.Declarative
open PiSmallTuple (rep rep_spec)
open PiSmallRecursive (compile widen classValue_lift)
universe u v w T

/-- Erased semantic products read only the common decision procedure.
The topology and complete leaf labels are unchanged. -/
theorem erasedType_of_dec {I : Type w} (M N : Interp.{T})
    (h : M.dec = N.dec) {m : Nat} (t : RecTel.{T,w} I m)
    (X : I → PSet.{T}) : t.erasedType M X = t.erasedType N X := by
  induction t with
  | ret _ => rfl
  | pi A B ih =>
      simp only [RecTel.erasedType]
      have he : ∀ q, Ed M ((B q).erasedType M X) = Ed N ((B q).erasedType N X) := by
        intro q
        rw [ih q]
        simp only [Ed, h]
      rw [funext he]
      simp only [piVal, PiProp, Ed, h]

theorem elements_of_dec {I : Type w} (M N : Interp.{T})
    (h : M.dec = N.dec) {m : Nat} (t : RecTel.{T,w} I m)
    (X : I → PSet.{T}) :
    Ed M (t.erasedType M X) = Ed N (t.erasedType N X) := by
  rw [erasedType_of_dec M N h t X]
  simp only [Ed, h]

/-- Ordinary argument values are retained in both environments. No
comparison outside the inhabited source domain is required. -/
def Domains (M N : Interp.{T}) (σ : Nat → Nat) :
    List (Expr Nat) → (Nat → PSet.{T}) →
      (Nat → PSet.{T}) → Prop
  | [], _, _ => True
  | A :: ds, ρ, η =>
      Equiv (Ed M (den M σ ρ A)) (Ed N (den N σ η A)) ∧
      ∀ a, a ∈ Ed M (den M σ ρ A) → Domains M N σ ds (vcons a ρ) (vcons a η)

theorem domains_self (M : Interp.{T}) (σ : Nat → Nat) :
    ∀ ds ρ, Domains M M σ ds ρ ρ
  | [], _ => True.intro
  | _ :: ds, _ => ⟨Equiv.rfl, fun _ _ => domains_self M σ ds _⟩

/-- Conditional small compression with a reached-leaf inclusion. The
label reader is evaluated in the topology environment; the supplied leaf
inclusion may read all source locals and all actual inner arguments. -/
theorem compile_mem {I : Type w} (M N : Interp.{max (u+1) v})
    (ch : Choice.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{max (u+1) v}) → I)
    (X : I → PSet.{max (u+1) v}) (hX : ∀ i, Dich (X i)) (b : Expr Nat) :
    ∀ ds ρ η, Domains M N σ ds ρ η →
      (∀ xs, TelFits M σ ds ρ xs →
        Sub (Ed M (den M σ (push xs ρ) b)) (X (R (push xs η)))) →
      ∀ g : PSet.{max (u+1) v}, Small.{u,max (u+1) v} g →
        g ∈ Ed M (den M σ ρ (policyPi ds b)) →
        g ∈ Ed M ((widen.{u,v,w} (compile.{u,v,w} N ch σ R ds η)).erasedType M X) := by
  intro ds
  induction ds with
  | nil =>
      intro ρ η _ hL g _ hg
      exact mem_congr_right (ed_tyv M (hX (R η))).symm
        (hL [] True.intro g hg)
  | cons A ds ih =>
      intro ρ η hDom hL g hg hf
      let D := Ed N (den N σ η A)
      let S := rep.{u,v} N ch D
      let T := lift.{u,max (u+1) v} S
      let B := fun a => den M σ (vcons a ρ) (policyPi ds b)
      let C := fun a => tyv (classFiber T (fun q =>
        Ed M ((widen.{u,v,w} (compile.{u,v,w} N ch σ R ds
          (vcons (lift.{u,max (u+1) v}
            (PiCompile.classValue S (FBrDown.{u,max (u+1) v} S q))) η))).erasedType M X)) a)
      have hB : ∀ a a', Equiv a a' → Equiv (B a) (B a') :=
        fun _ _ h => den_congr M σ _ (vcons_congr h (fun _ => Equiv.rfl))
      have hC : ∀ a a', Equiv a a' → Equiv (C a) (C a') :=
        fun _ _ h => tyv_congr (classFiber_congr T _ h)
      change g ∈ Ed M (piVal M (tyv T) C)
      cases hd : N.dec (Small.{u,max (u+1) v} D) with
      | isTrue hSmall =>
          have e : Equiv D T := rep_spec.{u,v} N ch D hSmall
          have hT : Dich T := (dich_congr e).mp (dich_ed N _)
          have eD : Equiv (Ed M (tyv T)) (Ed M (den M σ ρ A)) :=
            (ed_tyv M hT).trans (e.symm.trans hDom.1.symm)
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
            have hz'D : z' ∈ Ed M (den M σ ρ A) :=
              mem_congr_right (e.symm.trans hDom.1.symm) hz'T
            have ev : Equiv z' z := (classValue_lift.{u,v} S q).trans
              ((PiCompile.classValue_at T i).trans hi)
            have hf' := app_mem M hB hf hz'D
            have hr := ih (vcons z' ρ) (vcons z' η) (hDom.2 z' hz'D)
              (fun xs hx => hL (z' :: xs) ⟨hz'D, hx⟩)
              (fapp g z') (PiSmallValue.fapp_small.{u,max (u+1) v} hg) hf'
            have ef := (classFiber_congr T (fun q => Ed M
              ((widen.{u,v,w} (compile.{u,v,w} N ch σ R ds
                (vcons (lift.{u,max (u+1) v}
                  (PiCompile.classValue S (FBrDown.{u,max (u+1) v} S q))) η))).erasedType M X))
              hi.symm).trans (classFiber_at T _ i)
            have ec : Equiv (Ed M (C z))
                (Ed M ((widen.{u,v,w} (compile.{u,v,w} N ch σ R ds (vcons z' η))).erasedType M X)) :=
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
            | isFalse h =>
                exact (hSmall ((PiSmallValue.domain_small.{u,max (u+1) v}
                  M hB hg hf h).congr hDom.1)).elim
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

/-- Literal SmallAlong's one-field stage gives the required value bound.
The original field and actual element are preserved. -/
theorem compile_mem_of_stage {I : Type w} (M N : Interp.{max (u+1) v})
    (ch : Choice.{u}) (σ : Nat → Nat)
    (R : (Nat → PSet.{max (u+1) v}) → I)
    (X : I → PSet.{max (u+1) v}) (hX : ∀ i, Dich (X i))
    (ds : List (Expr Nat)) (b : Expr Nat)
    (ρ η : Nat → PSet.{max (u+1) v}) (hDom : Domains M N σ ds ρ η)
    (hL : ∀ xs, TelFits M σ ds ρ xs →
      Sub (Ed M (den M σ (push xs ρ) b)) (X (R (push xs η))))
    (g : PSet.{max (u+1) v})
    (hstage : Ed M (den M σ ρ (policyPi ds b)) ∈ univIn.{u,v})
    (hg : g ∈ Ed M (den M σ ρ (policyPi ds b))) :
    g ∈ Ed M ((widen.{u,v,w} (compile.{u,v,w} N ch σ R ds η)).erasedType M X) :=
  compile_mem.{u,v,w} M N ch σ R X hX b ds ρ η hDom hL g
    (small_of_mem_small (mem_univIn.{u,v}.mp hstage) hg) hg

end Rcic.F3.PSet.PiSmallMaskSpine
