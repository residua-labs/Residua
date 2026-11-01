import rcic.RcicF3RecFieldMaskSupport

/-!
# Bounded masking rules with two original assignments

Each semantic soundness call uses its own actual fitting assignment.
Agreement of a clean function or argument is derived only from the
subject's actual support. The result type of an application is transported
at the equivalent original arguments, retaining its full dependency.

The lambda mode remains fixed syntactically. Ordinary binder arguments are
the same reached value in both original contexts, while a let rule may
extend them with different equivalent values. No masked Fits is used.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMaskSupport
open Rcic.Declarative RawFamily RecFieldOrigin
open RecFieldMask (Marks ordinary mode Value)

theorem clean_typed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (marks : Marks) (allowed : Allowed) (ρC ρD η : Nat → PSet.{4})
    (ha : Agree allowed ρC ρD)
    (hρ : Fits (mkM P (table P μ fd C)) σ Γ ρC)
    {e A : Expr Nat} (hf : occursConst fd.fref A = false) (hs : Supported allowed A)
    (d : HasTyT E n Γ e A) (hd : LOKt σ 4 K d)
    (h : Holds P μ fd C σ marks ρC ρD η e A) :
    Equiv (den (mkM P (table P μ fd C)) σ ρC e)
      (den (mkM P (table P μ fd C)) σ η e) := by
  cases hm : mode marks e with
  | none => simpa only [Holds, Value, hm] using h
  | some m =>
      simp only [Holds, Value, hm] at h
      have he := models_agree P μ fd C σ allowed ρC ρD ha A hf hs
      have hz := separator h.2 (sound_ty (P.good _ rfl) hE d hd ρC hρ)
        (ed_congr (mkM P μ) he)
      exact hz.trans h.1.symm

/-- Both original application memberships and agreement of the actual
supported subjects pay the origin-head rule. The target codomain is then
transported from the source argument to the target's original argument. -/
theorem origin_application (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (allowed : Allowed) (ρC ρD : Nat → PSet.{4}) (hag : Agree allowed ρC ρD)
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρC)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρD)
    (f a A B : Expr Nat)
    (hf : occursConst fd.fref f = false) (ha : occursConst fd.fref a = false)
    (hsf : Supported allowed f) (hsa : Supported allowed a)
    (df : HasTyT E n Γ f (.pi A B)) (hdf : LOKt σ 4 K df)
    (da : HasTyT E n Γ a A) (hda : LOKt σ 4 K da)
    (m : Nat)
    (ho : Origin (mkM P μ) fd C m
      (Ed (mkM P (table P μ fd C))
        (den (mkM P (table P μ fd C)) σ ρC (.pi A B)))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ ρD (.pi A B)))
      (den (mkM P (table P μ fd C)) σ ρC f)) :
    Origin (mkM P μ) fd C (m - 1)
      (Ed (mkM P (table P μ fd C))
        (den (mkM P (table P μ fd C)) σ ρC (instantiate0 a B)))
      (Ed (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
        (den (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C)))
          σ ρD (instantiate0 a B)))
      (den (mkM P (table P μ fd C)) σ ρC (.app f a)) := by
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  have ef := models_agree P μ fd C σ allowed ρC ρD hag f hf hsf
  have ea := models_agree P μ fd C σ allowed ρC ρD hag a ha hsa
  have hz := sound_ty (P.good MC rfl) hEC df hdf ρC hρC
  have hzD : den MC σ ρC f ∈ Ed MD (den MD σ ρD (.pi A B)) :=
    mem_congr_left ef.symm (sound_ty (P.good MD rfl) hED df hdf ρD hρD)
  have harg := sound_ty (P.good MC rfl) hEC da hda ρC hρC
  have h := RecFieldOrigin.application (M := mkM P μ) (fd := fd) (C := C)
    (den_resp MC σ ρC B) (den_resp MD σ ρD B) ho hz hzD harg
  change Origin (mkM P μ) fd C (m - 1)
    (Ed MC (den MC σ ρC (instantiate0 a B)))
    (Ed MD (den MD σ ρD (instantiate0 a B)))
    (fapp (den MC σ ρC f) (den MC σ ρC a))
  rw [den_inst0, den_inst0]
  exact h.transport Equiv.rfl
    (ed_congr MD (den_resp MD σ ρD B _ _ ea)) Equiv.rfl

theorem application_case (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (marks : Marks) (allowed : Allowed) (ρC ρD η : Nat → PSet.{4})
    (hag : Agree allowed ρC ρD)
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρC)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρD)
    (f a A B : Expr Nat)
    (hf : occursConst fd.fref f = false) (ha : occursConst fd.fref a = false)
    (hsf : Supported allowed f) (hsa : Supported allowed a)
    (df : HasTyT E n Γ f (.pi A B)) (hdf : LOKt σ 4 K df)
    (da : HasTyT E n Γ a A) (hda : LOKt σ 4 K da)
    (rf : Holds P μ fd C σ marks ρC ρD η f (.pi A B))
    (ra : Holds P μ fd C σ marks ρC ρD η a A) :
    Holds P μ fd C σ marks ρC ρD η (.app f a) (instantiate0 a B) := by
  let M := mkM P μ
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  cases hmf : mode marks f with
  | some m =>
      simp only [Holds, Value, hmf] at rf
      have ho := origin_application P μ fd C σ K hEC hED allowed ρC ρD hag
        hρC hρD f a A B hf ha hsf hsa df hdf da hda m rf.2
      simp only [Holds, mode, hmf, Option.map, Value]
      exact ⟨(fapp_congr rf.1 Equiv.rfl).trans (fapp_pempty _), ho⟩
  | none =>
      have er : Equiv (den MC σ ρC f) (den MC σ η f) := by
        simpa only [Holds, Value, hmf] using rf
      simp only [Holds, mode, hmf, Option.map, Value]
      change Equiv (fapp (den MC σ ρC f) (den MC σ ρC a))
        (fapp (den MC σ η f) (den MC σ η a))
      cases hma : mode marks a with
      | none =>
          have ea : Equiv (den MC σ ρC a) (den MC σ η a) := by
            simpa only [Holds, Value, hma] using ra
          exact fapp_congr er ea
      | some m =>
          simp only [Holds, Value, hma] at ra
          cases M.dec (Equiv (den MC σ ρC f) pempty) with
          | isTrue hz =>
              exact ((fapp_congr hz Equiv.rfl).trans (fapp_pempty _)).trans
                ((fapp_congr (er.symm.trans hz) Equiv.rfl).trans (fapp_pempty _)).symm
          | isFalse hz =>
              have ef := models_agree P μ fd C σ allowed ρC ρD hag f hf hsf
              have hg : den MC σ ρC f ∈ Ed M
                  (piVal M (den MC σ ρC A) (fun x => den MC σ (vcons x ρC) B)) :=
                sound_ty (P.good MC rfl) hEC df hdf ρC hρC
              have hg' : den MC σ ρC f ∈ Ed M
                  (piVal M (den MD σ ρD A) (fun x => den MD σ (vcons x ρD) B)) :=
                mem_congr_left ef.symm (sound_ty (P.good MD rfl) hED df hdf ρD hρD)
              have hc := mem_congr_right
                (ed_piVal M (den MC σ ρC A) (fun x => den MC σ (vcons x ρC) B)
                  (den_resp MC σ ρC B)) hg
              have hd := mem_congr_right
                (ed_piVal M (den MD σ ρD A) (fun x => den MD σ (vcons x ρD) B)
                  (den_resp MD σ ρD B)) hg'
              have hdomains : Equiv (Ed M (den MC σ ρC A)) (Ed M (den MD σ ρD A)) := by
                cases M.dec (PiProp M (den MC σ ρC A) (fun x => den MC σ (vcons x ρC) B)) with
                | isTrue hp =>
                    rw [cond_pos hp] at hc
                    exact (hz (mem_tv.mp hc).2).elim
                | isFalse hp =>
                    rw [cond_neg hp] at hc
                    cases M.dec (PiProp M (den MD σ ρD A) (fun x => den MD σ (vcons x ρD) B)) with
                    | isTrue hp' =>
                        rw [cond_pos hp'] at hd
                        exact (hz (mem_tv.mp hd).2).elim
                    | isFalse hp' =>
                        rw [cond_neg hp'] at hd
                        exact ext fun x =>
                          ⟨fun hx => piSet_dom
                            (fun y y' he => ed_congr M (den_resp MD σ ρD B y y' he))
                            (fun y y' he => ed_congr M (den_resp MC σ ρC B y y' he)) hd hc hx,
                           fun hx => piSet_dom
                            (fun y y' he => ed_congr M (den_resp MC σ ρC B y y' he))
                            (fun y y' he => ed_congr M (den_resp MD σ ρD B y y' he)) hc hd hx⟩
              have hzA := separator ra.2
                (sound_ty (P.good MC rfl) hEC da hda ρC hρC) hdomains
              exact fapp_congr er (hzA.trans ra.1.symm)

theorem lambda_case (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ : Nat → Nat) (marks : Marks) (allowed : Allowed)
    (ρC ρD η : Nat → PSet.{4}) (hag : Agree allowed ρC ρD)
    (A body B : Expr Nat) (hf : occursConst fd.fref A = false) (hs : Supported allowed A)
    (hA : Equiv (den (mkM P (table P μ fd C)) σ ρC A)
      (den (mkM P (table P μ fd C)) σ η A))
    (ih : ∀ a, a ∈ Ed (mkM P (table P μ fd C))
        (den (mkM P (table P μ fd C)) σ ρC A) →
      Holds P μ fd C σ (ordinary marks) (vcons a ρC) (vcons a ρD) (vcons a η) body B) :
    Holds P μ fd C σ marks ρC ρD η (.lam A body) (.pi A B) := by
  let M := mkM P μ
  let MC := mkM P (table P μ fd C)
  let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
  cases hm : mode (ordinary marks) body with
  | none =>
      have hb : ∀ a, a ∈ Ed MC (den MC σ ρC A) →
          Equiv (den MC σ (vcons a ρC) body) (den MC σ (vcons a η) body) := by
        intro a ha
        simpa only [Holds, hm, Value] using ih a ha
      have he : Equiv (den MC σ ρC (.lam A body)) (den MC σ η (.lam A body)) :=
        lamVal_congr_on MC hA (den_resp MC σ ρC body) hb
      simpa only [Holds, mode, hm, Option.map, Value] using he
  | some m =>
      have hb : ∀ a, a ∈ Ed MC (den MC σ ρC A) →
          Equiv (den MC σ (vcons a η) body) pempty ∧
          Origin M fd C m
            (Ed MC (den MC σ (vcons a ρC) B))
            (Ed MD (den MD σ (vcons a ρD) B))
            (den MC σ (vcons a ρC) body) := by
        intro a ha
        simpa only [Holds, hm, Value] using ih a ha
      have hp : LamProof MC (den MC σ η A) (fun a => den MC σ (vcons a η) body) := by
        intro a ha
        exact (hb a (mem_congr_right (ed_congr MC hA).symm ha)).1
      have hempty : Equiv (den MC σ η (.lam A body)) pempty := by
        change Equiv (cond MC.dec (LamProof MC (den MC σ η A)
          (fun a => den MC σ (vcons a η) body)) pempty _) pempty
        rw [cond_pos hp]
        exact Equiv.rfl
      have hsame := models_agree P μ fd C σ allowed ρC ρD hag A hf hs
      have ho : Origin M fd C (m + 1)
          (Ed MC (den MC σ ρC (.pi A B)))
          (Ed MD (den MD σ ρD (.pi A B))) (den MC σ ρC (.lam A body)) := by
        apply Origin.pi (den MC σ ρC A)
          (fun a => den MC σ (vcons a ρC) B)
          (fun a => den MD σ (vcons a ρD) B)
          (den_resp MC σ ρC B) (den_resp MD σ ρD B) Equiv.rfl
        · exact ed_congr M (piVal_congr M hsame.symm (den_resp MD σ ρD B))
        · intro a ha
          exact (hb a ha).2.transport Equiv.rfl Equiv.rfl
            (beta_val MC (den_resp MC σ ρC body) ha).symm
      simpa only [Holds, mode, hm, Option.map, Value] using And.intro hempty ho

theorem conversion_case (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (C : Frame)
    (σ K : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (marks : Marks) (ρC ρD η : Nat → PSet.{4})
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρC)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρD)
    {e A B : Expr Nat} {u : Level}
    (d : HasTyT E n Γ e A) (c : ConvT E n Γ A B (.sort u))
    (hd : LOKt σ 4 K (.conv Γ e A B u d c))
    (h : Holds P μ fd C σ marks ρC ρD η e A) :
    Holds P μ fd C σ marks ρC ρD η e B := by
  cases hm : mode marks e with
  | none => simpa only [Holds, Value, hm] using h
  | some m =>
      simp only [Holds, Value, hm] at h ⊢
      exact ⟨h.1, RecFieldOriginCases.conversion_rule P
        (table P μ fd C) (table P μ fd (RawFamilyEnlarge.enlarge fd C)) σ K
        hEC hED ρC ρD hρC hρD d c hd h.2⟩

end Rcic.F3.PSet.RecFieldMaskSupport
