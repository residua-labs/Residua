import rcic.RcicF3RecFieldMaskSupportRules

/-!
# Complete bounded typing induction with supported original captures

The original HasTyT derivation is interpreted in two separately fitted
assignments. Every read slot is justified by actual freeBvarRef support.
Opaque unused captures may differ without an equality or Origin premise.
The induction covers every typing constructor, including converted
applications, binders and lets, and concludes actual-to-masked equality
for a clean typed domain. Its masked assignment is never claimed to fit.

This is still a bounded theorem at its full sigma and K. Reader provenance
must supply the original domain derivation and its capture maps; no
unbounded normalization, common small frame or universal A follows here.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecFieldMaskSupport
open Rcic.Declarative RawFamily RecFieldOrigin
open RecFieldMask (Marks ordinary mode Value)

/-- The supported mode case is produced by recursion on the actual
bounded typing, rather than supplied as a term-classification callback. -/
theorem of_typing (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n) :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) → LOKt σ 4 K d →
    (marks : Marks) → (allowed : Allowed) → (ρC ρD η : Nat → PSet.{4}) →
    Agree allowed ρC ρD →
    Fits (mkM P (table P μ fd C)) σ Γ ρC →
    Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρD →
    Context P μ fd C σ marks allowed Γ ρC ρD η →
    occursConst fd.fref e = false → Supported allowed e →
    Holds P μ fd C σ marks ρC ρD η e A
  | _, _, _, .sort _ _, _, _, _, _, _, _, _, _, _, _, _, _ => Equiv.rfl
  | Γ, _, _, .bvar _ i A hi, _, marks, allowed, ρC, ρD, η, _, _, _, hctx, _, hs =>
      hctx i A (hs i (by show decide (i = i + 0) = true; exact decide_eq_true rfl)) hi
  | _, _, _, .const _ _ _ _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _ => Equiv.rfl
  | Γ, _, _, .pi _ A u B v dA dB, hd, marks, allowed, ρC, ρD, η,
      hag, hρC, hρD, hctx, hfree, hs => by
      have hf : occursConst fd.fref A = false ∧ occursConst fd.fref B = false :=
        Bool.or_eq_false_iff.mp hfree
      have hsp := hs.pi
      let MC := mkM P (table P μ fd C)
      let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
      have rA := of_typing P μ fd C σ K hEC hED dA hd.2.2.1
        marks allowed ρC ρD η hag hρC hρD hctx hf.1 hsp.1
      have eA := typed_type P μ fd C σ K hEC marks ρC ρD η hρC dA hd.2.2.1 rA
      have sameA := models_agree P μ fd C σ allowed ρC ρD hag A hf.1 hsp.1
      change Equiv (piVal MC (den MC σ ρC A) (fun x => den MC σ (vcons x ρC) B))
        (piVal MC (den MC σ η A) (fun x => den MC σ (vcons x η) B))
      apply piVal_congr_on MC eA (den_resp MC σ ρC B) (den_resp MC σ η B)
      intro x hx
      have hxD : x ∈ Ed MD (den MD σ ρD A) :=
        mem_congr_right (ed_congr (mkM P μ) sameA) hx
      have hfC : Fits MC σ (.assumption A :: Γ) (vcons x ρC) := ⟨hρC, hx⟩
      have hfD : Fits MD σ (.assumption A :: Γ) (vcons x ρD) := ⟨hρD, hxD⟩
      have hr := context_ordinary P μ fd C σ marks allowed Γ ρC ρD η hctx
        (.assumption A) x x x Equiv.rfl
      have rB := of_typing P μ fd C σ K hEC hED dB hd.2.2.2
        (ordinary marks) (allowCons True allowed) (vcons x ρC) (vcons x ρD)
        (vcons x η) (agree_cons hag (fun _ => Equiv.rfl)) hfC hfD hr hf.2 hsp.2
      exact typed_type P μ fd C σ K hEC (ordinary marks)
        (vcons x ρC) (vcons x ρD) (vcons x η) hfC dB hd.2.2.2 rB
  | Γ, _, _, .lam _ A u body B dA db, hd, marks, allowed, ρC, ρD, η,
      hag, hρC, hρD, hctx, hfree, hs => by
      have hf : occursConst fd.fref A = false ∧ occursConst fd.fref body = false :=
        Bool.or_eq_false_iff.mp hfree
      have hsp := hs.lam
      let MC := mkM P (table P μ fd C)
      let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
      have rA := of_typing P μ fd C σ K hEC hED dA hd.1
        marks allowed ρC ρD η hag hρC hρD hctx hf.1 hsp.1
      have eA := typed_type P μ fd C σ K hEC marks ρC ρD η hρC dA hd.1 rA
      have sameA := models_agree P μ fd C σ allowed ρC ρD hag A hf.1 hsp.1
      apply lambda_case P μ fd C σ marks allowed ρC ρD η hag A body B hf.1 hsp.1 eA
      intro x hx
      have hxD : x ∈ Ed MD (den MD σ ρD A) :=
        mem_congr_right (ed_congr (mkM P μ) sameA) hx
      exact of_typing P μ fd C σ K hEC hED db hd.2
        (ordinary marks) (allowCons True allowed) (vcons x ρC) (vcons x ρD)
        (vcons x η) (agree_cons hag (fun _ => Equiv.rfl)) ⟨hρC, hx⟩ ⟨hρD, hxD⟩
        (context_ordinary P μ fd C σ marks allowed Γ ρC ρD η hctx
          (.assumption A) x x x Equiv.rfl) hf.2 hsp.2
  | _, _, _, .app _ f a A B df da, hd, marks, allowed, ρC, ρD, η,
      hag, hρC, hρD, hctx, hfree, hs => by
      have hf : occursConst fd.fref f = false ∧ occursConst fd.fref a = false :=
        Bool.or_eq_false_iff.mp hfree
      have hsp := hs.app
      have rf := of_typing P μ fd C σ K hEC hED df hd.1
        marks allowed ρC ρD η hag hρC hρD hctx hf.1 hsp.1
      have ra := of_typing P μ fd C σ K hEC hED da hd.2
        marks allowed ρC ρD η hag hρC hρD hctx hf.2 hsp.2
      exact application_case P μ fd C σ K hEC hED marks allowed ρC ρD η hag
        hρC hρD f a A B hf.1 hf.2 hsp.1 hsp.2 df hd.1 da hd.2 rf ra
  | Γ, _, _, .letE _ A u value B body dA dv db, hd, marks, allowed, ρC, ρD, η,
      hag, hρC, hρD, hctx, hfree, hs => by
      have hf : (occursConst fd.fref A = false ∧ occursConst fd.fref value = false) ∧
          occursConst fd.fref body = false := by
        simpa only [occursConst, Bool.or_eq_false_iff] using hfree
      have hsp := hs.letE
      let MC := mkM P (table P μ fd C)
      let MD := mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))
      have rv := of_typing P μ fd C σ K hEC hED dv hd.2.1
        marks allowed ρC ρD η hag hρC hρD hctx hf.1.2 hsp.2.1
      have ev := clean_typed P μ fd C σ K hEC marks allowed ρC ρD η hag hρC
        hf.1.1 hsp.1 dv hd.2.1 rv
      have sameV := models_agree P μ fd C σ allowed ρC ρD hag value hf.1.2 hsp.2.1
      have hfC : Fits MC σ (.letBinding A value :: Γ)
          (vcons (den MC σ ρC value) ρC) :=
        ⟨hρC, sound_ty (P.good MC rfl) hEC dv hd.2.1 ρC hρC, Equiv.rfl⟩
      have hfD : Fits MD σ (.letBinding A value :: Γ)
          (vcons (den MD σ ρD value) ρD) :=
        ⟨hρD, sound_ty (P.good MD rfl) hED dv hd.2.1 ρD hρD, Equiv.rfl⟩
      have hr := context_ordinary P μ fd C σ marks allowed Γ ρC ρD η hctx
        (.letBinding A value) (den MC σ ρC value) (den MD σ ρD value)
        (den MC σ η value) ev
      have rb := of_typing P μ fd C σ K hEC hED db hd.2.2
        (ordinary marks) (allowCons True allowed)
        (vcons (den MC σ ρC value) ρC) (vcons (den MD σ ρD value) ρD)
        (vcons (den MC σ η value) η) (agree_cons hag (fun _ => sameV))
        hfC hfD hr hf.2 hsp.2.2
      change Value (mkM P μ) fd C (mode (ordinary marks) body)
        (Ed MC (den MC σ ρC (instantiate0 value B)))
        (Ed MD (den MD σ ρD (instantiate0 value B)))
        (den MC σ (vcons (den MC σ ρC value) ρC) body)
        (den MC σ (vcons (den MC σ η value) η) body)
      rw [den_inst0, den_inst0]
      exact rb
  | _, _, _, .lit _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _ => Equiv.rfl
  | _, _, _, .conv _ e A B u d c, hd, marks, allowed, ρC, ρD, η,
      hag, hρC, hρD, hctx, hfree, hs => by
      have r := of_typing P μ fd C σ K hEC hED d hd.1
        marks allowed ρC ρD η hag hρC hρD hctx hfree hs
      exact conversion_case P μ fd C σ K hEC hED marks ρC ρD η hρC hρD d c hd r

/-- A clean supported domain has the same denotation at its actual source
and masked assignments, despite opaque differing original captures. -/
theorem domain_eq (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hEC : EnvSound (mkM P (table P μ fd C)) σ K E n)
    (hED : EnvSound (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ K E n)
    (marks : Marks) (allowed : Allowed) (ρC ρD η : Nat → PSet.{4})
    (hag : Agree allowed ρC ρD)
    (hρC : Fits (mkM P (table P μ fd C)) σ Γ ρC)
    (hρD : Fits (mkM P (table P μ fd (RawFamilyEnlarge.enlarge fd C))) σ Γ ρD)
    (hctx : Context P μ fd C σ marks allowed Γ ρC ρD η)
    {A : Expr Nat} {u : Level} (hf : occursConst fd.fref A = false)
    (hs : Supported allowed A) (d : HasTyT E n Γ A (.sort u)) (hd : LOKt σ 4 K d) :
    Equiv (den (mkM P (table P μ fd C)) σ ρC A)
      (den (mkM P (table P μ fd C)) σ η A) :=
  typed_type P μ fd C σ K hEC marks ρC ρD η hρC d hd
    (of_typing P μ fd C σ K hEC hED d hd marks allowed ρC ρD η
      hag hρC hρD hctx hf hs)

end Rcic.F3.PSet.RecFieldMaskSupport
