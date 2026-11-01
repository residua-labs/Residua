import rcic.RcicF3PiTypedCompile
import rcic.RcicF3StageFacts
import rcic.RcicF3KTWBig
/-!
# Small branch domains for structural typed telescopes

Hereditary typing bounds all Ed binder domains by universe 3. This uses
only the existing Premises4 choice levels. The telescope's result label
may still live in a larger universe. No normalized admission or family
fixed-point producer is asserted. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallCompile
open Rcic.Declarative

theorem ed_small (P : Premises4) (M : Interp.{4}) {x : PSet.{4}}
    (k : Nat) (hx : x ∈ U W4 k) : Small.{3,4} (Ed M x) := by
  have h := ed_mem_W4_of_mem_U P M (Nat.le_max_left k 4)
    (show 1 ≤ max k 4 from Nat.le_trans (by decide) (Nat.le_max_right k 4)) hx
  have e : W4 (max k 4) = univIn.{3,4} := by
    match max k 4, Nat.le_max_right k 4 with
    | 0, h => exact (by omega : False).elim
    | 1, h => exact (by omega : False).elim
    | 2, h => exact (by omega : False).elim
    | 3, h => exact (by omega : False).elim
    | _ + 4, _ => rfl
  exact mem_univIn.{3,4}.mp (e ▸ h)
universe v

def DomainsSmall {I : Type v} : {m : Nat} → RecTel.{4,v} I m → Prop
  | _, .ret _ => True
  | _, .pi A B => Small.{3,4} A ∧ ∀ q, DomainsSmall (B q)

theorem domainsSmall_of_hsound {I : Type v} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (R : (Nat → PSet.{4}) → I) (b : Expr Nat) :
    ∀ (ds : List (Expr Nat)) {Γ : LCtx} {l : Level}
    (d : HasTyT E n Γ (policyPi ds b) (.sort l)), HSoundT (mkM P μ) σ d →
    ∀ ρ, Fits (mkM P μ) σ Γ ρ →
      DomainsSmall (PiSyntaxCompile.compile (mkM P μ) σ R ds ρ) := by
  intro ds
  induction ds with
  | nil => intro Γ l d hs ρ hρ; trivial
  | cons A ds ih =>
    intro Γ l d hs ρ hρ
    obtain ⟨a, dA, hA⟩ := pi_dom_sound d hs
    obtain ⟨v, dB, hB⟩ := pi_body_sound d hs
    refine ⟨ed_small P (mkM P μ) (evalTotal σ a) ?_, fun q => ?_⟩
    · exact mem_congr_right (ed_tyv (mkM P μ) (U4_dich _)) (hA.root ρ hρ)
    · exact ih dB hB _ ⟨hρ, PiCompile.classValue_mem _ q⟩

/-- Embed small branch domains while retaining the large result labels. -/
def widen {I : Type v} : {m : Nat} → RecTel.{3,v} I m → RecTel.{4,v} I m
  | _, .ret i => .ret i
  | _, .pi A B => .pi (lift.{3,4} A) (fun q => widen (B (FBrDown.{3,4} A q)))

theorem classValue_lift (A : PSet.{3}) (q : FBr (lift.{3,4} A)) :
    Equiv (lift.{3,4} (PiCompile.classValue A (FBrDown.{3,4} A q)))
      (PiCompile.classValue (lift.{3,4} A) q) := by
  refine Quotient.inductionOn q ?_
  intro i
  rw [FBrDown_mk]
  exact (lift_equiv.{3,4} (PiCompile.classValue_at A (liftIdxDown A i))).trans
    ((liftIdxDown_eq A i).symm.trans (PiCompile.classValue_at (lift.{3,4} A) i).symm)

/-- Total fallback is relevant only outside the typed domain. -/
def rep (P : Premises4) (x : PSet.{4}) : PSet.{3} :=
  @dite _ (Small.{3,4} x) (P.dec _) (fun h => smallRep.{3,4} P.c3 x h) (fun _ => pempty)

theorem rep_spec (P : Premises4) (x : PSet.{4}) (hx : Small.{3,4} x) :
    Equiv x (lift.{3,4} (rep P x)) := by
  unfold rep
  rw [dif_pos hx]
  exact smallRep_spec.{3,4} P.c3 x hx

/-- Compile small branch addresses, passing their lifted values to the
actual dependent syntax. Result indices retain their original universe. -/
def compile {I : Type v} (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (R : (Nat → PSet.{4}) → I) :
    (ds : List (Expr Nat)) → (Nat → PSet.{4}) → RecTel.{3,v} I ds.length
  | [], ρ => .ret (R ρ)
  | A :: ds, ρ =>
    let D := rep P (Ed (mkM P μ) (den (mkM P μ) σ ρ A))
    .pi D (fun q => compile P μ σ R ds
      (vcons (lift.{3,4} (PiCompile.classValue D q)) ρ))

theorem compile_spec_of_hsound {I : Type v} (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (R : (Nat → PSet.{4}) → I)
    (X : I → PSet.{4}) (hX : ∀ i, Dich (X i)) (b : Expr Nat) :
    ∀ (ds : List (Expr Nat)) {Γ : LCtx} {l : Level}
    (d : HasTyT E n Γ (policyPi ds b) (.sort l)), HSoundT (mkM P μ) σ d →
    ∀ ρ, Fits (mkM P μ) σ Γ ρ → PiSyntaxCompile.EndEq (mkM P μ) σ R X b ds ρ →
      Equiv ((widen (compile P μ σ R ds ρ)).erasedType (mkM P μ) X)
        (den (mkM P μ) σ ρ (policyPi ds b)) := by
  intro ds
  induction ds with
  | nil => intro Γ l d hs ρ hρ hEnd; exact hEnd
  | cons A ds ih =>
    intro Γ l d hs ρ hρ hEnd
    let M := mkM P μ
    let D := Ed M (den M σ ρ A)
    let S := rep P D
    let T := lift.{3,4} S
    let C := fun a => tyv (classFiber T (fun q =>
      Ed M ((widen (compile P μ σ R ds
        (vcons (lift.{3,4} (PiCompile.classValue S (FBrDown.{3,4} S q))) ρ))).erasedType M X)) a)
    have hC : ∀ a b, Equiv a b → Equiv (C a) (C b) :=
      fun _ _ h => tyv_congr (classFiber_congr T _ h)
    obtain ⟨a, dA, hA⟩ := pi_dom_sound d hs
    obtain ⟨v, dB, hB⟩ := pi_body_sound d hs
    have hSmall : Small.{3,4} D := ed_small P M (evalTotal σ a)
      (mem_congr_right (ed_tyv M (U4_dich _)) (hA.root ρ hρ))
    have e : Equiv D T := rep_spec P D hSmall
    have hT : Dich T := (dich_congr e).mp (dich_ed M _)
    change Equiv (piVal M (tyv T) C)
      (piVal M (den M σ ρ A) (fun a => den M σ (vcons a ρ) (policyPi ds b)))
    refine Equiv.trans (y := piVal M (tyv D) (fun a => den M σ (vcons a ρ) (policyPi ds b))) ?_ ?_
    · apply piVal_congr_on M (B' := fun a => den M σ (vcons a ρ) (policyPi ds b))
        (tyv_congr e.symm) hC
        (fun a b h => den_congr M σ _ (vcons_congr h (fun _ => Equiv.rfl)))
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
      have ef := (classFiber_congr T (fun q => Ed M
        ((widen (compile P μ σ R ds
          (vcons (lift.{3,4} (PiCompile.classValue S (FBrDown.{3,4} S q))) ρ))).erasedType M X))
        hi.symm).trans (classFiber_at T _ i)
      exact (tyv_congr ef).trans
        (((widen (compile P μ σ R ds (vcons z' ρ))).erasedType_tagged M X hX).trans
          ((ih dB hB (vcons z' ρ) ⟨hρ, hz'D⟩ (hEnd z' hz'D)).trans
            (den_congr M σ (policyPi ds b) (vcons_congr ev (fun _ => Equiv.rfl)))))
    · exact PiEraseCompile.piVal_ed_domain M (den M σ ρ A) _
        (fun a b h => den_congr M σ _ (vcons_congr h (fun _ => Equiv.rfl)))

/-- At a fixed sound interpretation, all leaf and smallness obligations
are derived from the actual bounded derivation. -/
theorem compile_spec (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P μ) σ K E n) (ds : List (Expr Nat)) (b : Expr Nat)
    {l : Level} (d : HasTyT E n Γ (policyPi ds b) (.sort l)) (hd : LOKt σ 4 K d)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    Equiv ((widen (compile P μ σ (PiTypedCompile.leafIndex (mkM P μ) σ b) ds ρ)).erasedType
      (mkM P μ) (fun i => i.1)) (den (mkM P μ) σ ρ (policyPi ds b)) := by
  exact compile_spec_of_hsound P μ σ (PiTypedCompile.leafIndex (mkM P μ) σ b)
    (fun i => i.1) (fun i => i.2) b ds d (hsound_ty (P.good _ rfl) hE d hd) ρ hρ
    (PiTypedCompile.typed_endEq P μ σ K hE ds b d hd ρ hρ)
end Rcic.F3.PSet.PiSmallCompile
