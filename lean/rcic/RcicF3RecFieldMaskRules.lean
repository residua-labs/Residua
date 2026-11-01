import rcic.RcicF3RecFieldMaskRelation
import rcic.RcicCtxMorph

/-!
# Actual lookup, application and conversion rules for the bounded mask

Ordinary binder extension uses the exact lifted lookup types. The
application case interprets the original bounded function and argument
derivations in the two original fitted environments. A nonempty common
consumer determines the same decoded domain in both models, so an origin
argument is empty by the separator. An origin head instead preserves its
residual origin at the actual argument and complete result key.

These are induction rules, to be called by the actual typing recursion.
They neither supply a masked Fits hypothesis nor change the checked apex.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMask
open Rcic.Declarative RawFamily RecFieldOrigin

/-- Extending the original and masked assignments by equivalent ordinary
values preserves every earlier lookup type by its literal one-step lift. -/
theorem context_ordinary (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ : Nat → Nat)
    (marks : Marks) (Γ : LCtx) (ρ η : Nat → PSet.{4})
    (h : Context P μ fd C σ marks Γ ρ η)
    (decl : LocalDecl) (x y : PSet.{4}) (hxy : Equiv x y) :
    Context P μ fd C σ (ordinary marks) (decl :: Γ) (vcons x ρ) (vcons y η) := by
  intro i A hi
  cases i with
  | zero => exact hxy
  | succ i =>
      rw [lookupType_cons_succ] at hi
      cases ht : lookupType Γ i with
      | none => rw [ht] at hi; cases hi
      | some B =>
          rw [ht] at hi
          cases hi
          have hB := h i B ht
          change Value (mkM P μ) fd C (marks i)
            (Ed (mkM P (table P μ fd C))
              (den (mkM P (table P μ fd C)) σ (vcons x ρ) (Declarative.lift 0 1 B)))
            (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
              (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
                σ (vcons x ρ) (Declarative.lift 0 1 B))) (ρ i) (η i)
          simpa only [den_lift, liftρ_zero, shiftρ_one_cons] using hB

/-- A clean expected annotation turns an origin case into actual value
agreement. Only the source original environment needs a soundness call. -/
theorem clean_typed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (marks : Marks) (ρ η : Nat → PSet.{4})
    (hρ : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    {e A : Expr Nat} (hfreeA : occursConst fd.fref A = false)
    (d : HasTyT E n Γ e A) (hd : LOKt σ 4 K d)
    (h : Holds P μ fd C σ marks ρ η e A) :
    Equiv (den (mkM P (table P μ fd C)) σ ρ e)
      (den (mkM P (table P μ fd C)) σ η e) := by
  cases hm : mode marks e with
  | none => simpa only [Holds, Value, hm] using h
  | some m =>
      simp only [Holds, Value, hm] at h
      exact (RecFieldOriginCases.clean_expected P μ fd C σ K hE ρ hρ
        hfreeA d hd h.2).trans h.1.symm

/-- The actual application premises pay both memberships. Neither its
expected domain nor codomain is assumed family-free. -/
theorem application_case (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (marks : Marks) (ρ η : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    (f a A B : Expr Nat)
    (hf : occursConst fd.fref f = false) (ha : occursConst fd.fref a = false)
    (df : HasTyT E n Γ f (.pi A B)) (hdf : LOKt σ 4 K df)
    (da : HasTyT E n Γ a A) (hda : LOKt σ 4 K da)
    (rf : Holds P μ fd C σ marks ρ η f (.pi A B))
    (ra : Holds P μ fd C σ marks ρ η a A) :
    Holds P μ fd C σ marks ρ η (.app f a) (instantiate0 a B) := by
  let M := mkM P μ
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  cases hmf : mode marks f with
  | some m =>
      simp only [Holds, Value, hmf] at rf
      have ho := RecFieldOriginSyntax.typed_application P μ fd C σ K hEC hED
        ρ hρC hρD f a A B hf ha df hdf da hda m rf.2
      simp only [Holds, mode, hmf, Option.map, Value]
      exact ⟨(fapp_congr rf.1 Equiv.rfl).trans (fapp_pempty _), ho⟩
  | none =>
      have er : Equiv (den MC σ ρ f) (den MC σ η f) := by
        simpa only [Holds, Value, hmf] using rf
      simp only [Holds, mode, hmf, Option.map, Value]
      change Equiv (fapp (den MC σ ρ f) (den MC σ ρ a))
        (fapp (den MC σ η f) (den MC σ η a))
      cases hma : mode marks a with
      | none =>
          have ea : Equiv (den MC σ ρ a) (den MC σ η a) := by
            simpa only [Holds, Value, hma] using ra
          exact fapp_congr er ea
      | some m =>
          simp only [Holds, Value, hma] at ra
          cases M.dec (Equiv (den MC σ ρ f) pempty) with
          | isTrue hz =>
              exact ((fapp_congr hz Equiv.rfl).trans (fapp_pempty _)).trans
                ((fapp_congr (er.symm.trans hz) Equiv.rfl).trans (fapp_pempty _)).symm
          | isFalse hz =>
              have ef : den MC σ ρ f = den MD σ ρ f :=
                PiIndependent.den_free P μ fd.fref (ofFrame P μ fd C)
                  (ofFrame P μ fd (RawFamilyEnlarge.enlarge fd C)) σ f hf ρ
              have hg : den MC σ ρ f ∈ Ed M
                  (piVal M (den MC σ ρ A) (fun x => den MC σ (vcons x ρ) B)) :=
                sound_ty (P.good MC rfl) hEC df hdf ρ hρC
              have hg' : den MC σ ρ f ∈ Ed M
                  (piVal M (den MD σ ρ A) (fun x => den MD σ (vcons x ρ) B)) := by
                rw [ef]
                exact sound_ty (P.good MD rfl) hED df hdf ρ hρD
              have hc := mem_congr_right
                (ed_piVal M (den MC σ ρ A) (fun x => den MC σ (vcons x ρ) B)
                  (den_resp MC σ ρ B)) hg
              have hd := mem_congr_right
                (ed_piVal M (den MD σ ρ A) (fun x => den MD σ (vcons x ρ) B)
                  (den_resp MD σ ρ B)) hg'
              have hdomains : Equiv (Ed M (den MC σ ρ A)) (Ed M (den MD σ ρ A)) := by
                cases M.dec (PiProp M (den MC σ ρ A) (fun x => den MC σ (vcons x ρ) B)) with
                | isTrue hp =>
                    rw [cond_pos hp] at hc
                    exact (hz (mem_tv.mp hc).2).elim
                | isFalse hp =>
                    rw [cond_neg hp] at hc
                    cases M.dec (PiProp M (den MD σ ρ A) (fun x => den MD σ (vcons x ρ) B)) with
                    | isTrue hp' =>
                        rw [cond_pos hp'] at hd
                        exact (hz (mem_tv.mp hd).2).elim
                    | isFalse hp' =>
                        rw [cond_neg hp'] at hd
                        exact ext fun x =>
                          ⟨fun hx => piSet_dom
                            (fun y y' he => ed_congr M (den_resp MD σ ρ B y y' he))
                            (fun y y' he => ed_congr M (den_resp MC σ ρ B y y' he)) hd hc hx,
                           fun hx => piSet_dom
                            (fun y y' he => ed_congr M (den_resp MC σ ρ B y y' he))
                            (fun y y' he => ed_congr M (den_resp MD σ ρ B y y' he)) hc hd hx⟩
              have hzA := RecFieldOrigin.separator ra.2
                (sound_ty (P.good MC rfl) hEC da hda ρ hρC) hdomains
              exact fapp_congr er (hzA.trans ra.1.symm)

/-- Conversion transports exactly the two original decoded types. The
masked term and the syntactic mode are unchanged. -/
theorem conversion_case (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (marks : Marks) (ρ η : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρ)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρ)
    {e A B : Expr Nat} {u : Level}
    (d : HasTyT E n Γ e A) (c : ConvT E n Γ A B (.sort u))
    (hd : LOKt σ 4 K (.conv Γ e A B u d c))
    (h : Holds P μ fd C σ marks ρ η e A) :
    Holds P μ fd C σ marks ρ η e B := by
  cases hm : mode marks e with
  | none => simpa only [Holds, Value, hm] using h
  | some m =>
      simp only [Holds, Value, hm] at h ⊢
      exact ⟨h.1, RecFieldOriginCases.conversion_rule P
        (table P μ fd C) (table P μ fd (RawFamilyEnlarge.enlarge fd C)) σ K
        hEC hED ρ ρ hρC hρD d c hd h.2⟩

end Rcic.F3.PSet.RecFieldMask
