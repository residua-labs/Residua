import rcic.RcicAnnLRRed
import rcic.RcicAnnLRG
/-!
# M2-b (i) — the relation respects typed reduction; escape to conversion
# (amended by M1-d (iv))

Three facts the fundamental theorem leans on, each short because the clauses are
keyed on normal forms and state their data at them: a type and its typed
weak-head normal form carry the SAME relation (`tyKA_of_whTyAg`, both ways;
likewise `eqKA_of_whTyA`); every `EqKAg` is a `TyConvA` (`eqKA_tyConvg`); and
ESCAPE — a related pair is typed and convertible at the type (`escapeAg`,
`escapeA_hasTyg`), every clause through the `ConvA`/`HasTyA` data it carries,
re-typed from the normal form to the type along the chain (`convA_of_tyConvA`,
`hasTyA_of_tyConvA`). No row, no uniqueness, no hypothesis about `ConvA`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Red
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

/-- a type and its typed normal form carry the same relation. -/
theorem tyKA_of_whTyAg {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyA E I n Γ A A₀) (hn₀ : hStepFnA E I.fn Γ A₀ = none)
    (h : TyKAg E I n ρ₀ k LE LT Γ A R) : TyKAg E I n ρ₀ k LE LT Γ A₀ R := by
  cases h with
  | prop hA hn hP =>
      have e := whTyA_det hA hA₀ hn hn₀
      subst e
      obtain ⟨_, h'⟩ := whTyA_hasTy_end hA
      exact h'.elim fun h' => .prop (whTyA_of_hasTy h') hn hP
  | sortT hA hz hk =>
      have e := whTyA_det hA hA₀ (hStepFnA_sort _ _ _ _) hn₀
      subst e
      obtain ⟨_, h'⟩ := whTyA_hasTy_end hA
      exact h'.elim fun h' => .sortT (whTyA_of_hasTy h') hz hk
  | sortP hA hz =>
      have e := whTyA_det hA hA₀ (hStepFnA_sort _ _ _ _) hn₀
      subst e
      obtain ⟨_, h'⟩ := whTyA_hasTy_end hA
      exact h'.elim fun h' => .sortP (whTyA_of_hasTy h') hz
  | pi hA hnp hDty hCty RD hD RC hC hCeq =>
      have e := whTyA_det hA hA₀ (hStepFnA_pi _ _ _ _ _ _ _) hn₀
      subst e
      obtain ⟨_, h'⟩ := whTyA_hasTy_end hA
      exact h'.elim fun h' => .pi (whTyA_of_hasTy h') hnp hDty hCty RD hD RC hC hCeq
  | fam hA hn hnp hm hind hsh hps hu hz Rs RsF RsI hFld hFldF hFldeq hFldRec hFldFeq hxsD hFldI hFldIeq hFldIRec hFldIdom =>
      have e := whTyA_det hA hA₀ hn hn₀
      subst e
      obtain ⟨_, h'⟩ := whTyA_hasTy_end hA
      exact h'.elim fun h' => .fam (whTyA_of_hasTy h') hn hnp hm hind hsh hps hu hz Rs RsF RsI hFld hFldF hFldeq hFldRec hFldFeq hxsD hFldI hFldIeq hFldIRec hFldIdom
  | stuck hA hN hnp =>
      have e := whTyA_det hA hA₀ hN.1 hn₀
      subst e
      obtain ⟨_, h'⟩ := whTyA_hasTy_end hA
      exact h'.elim fun h' => .stuck (whTyA_of_hasTy h') hN hnp

/-- DT-025/A-6 S1-g.2: a type reducing to a normal PROPOSITION is valid with the triple —
    the prop clause (in the guarded copy the triple is the prop clause's alone). -/
theorem tyKA_of_propNFg {Γ : LCtxA} {A N : ExprA} (hA : WhTyA E I n Γ A N)
    (hn : hStepFnA E I.fn Γ N = none) (hP : IsPropTy E I Γ N) :
    TyKAg E I n ρ₀ k LE LT Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N)) :=
  .prop hA hn hP

/-- a type reducing to a triple-like normal form is valid, given the normal form's side of
    the `IsPropTy` boundary: the prop clause at a proposition, the guarded stuck clause at a
    non-proposition. -/
theorem tyKA_valid_of_tripleLikeg {Γ : LCtxA} {A N : ExprA} (hA : WhTyA E I n Γ A N)
    (h : TripleLikeA E I Γ N) (hdec : IsPropTy E I Γ N ∨ ¬ IsPropTy E I Γ N) :
    ∃ R, TyKAg E I n ρ₀ k LE LT Γ A R :=
  hdec.elim (fun hP => ⟨_, .prop hA h.1 hP⟩)
    (fun hnp => h.2.elim (fun hP => absurd hP hnp) (fun hs => ⟨_, .stuck hA ⟨h.1, hs⟩ hnp⟩))

/-- and back: the relation of the normal form is the relation of the type. -/
theorem tyKA_of_whTyA'g {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyA E I n Γ A A₀) (hn₀ : hStepFnA E I.fn Γ A₀ = none)
    (h : TyKAg E I n ρ₀ k LE LT Γ A₀ R) : TyKAg E I n ρ₀ k LE LT Γ A R := by
  cases h with
  | prop hA hn hP =>
      have e := whTyA_det hA (whTyA_self hA) hn hn₀
      subst e
      exact .prop hA₀ hn hP
  | sortT hA hz hk =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_sort _ _ _ _) hn₀
      subst e
      exact .sortT hA₀ hz hk
  | sortP hA hz =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_sort _ _ _ _) hn₀
      subst e
      exact .sortP hA₀ hz
  | pi hA hnp hDty hCty RD hD RC hC hCeq =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_pi _ _ _ _ _ _ _) hn₀
      subst e
      exact .pi hA₀ hnp hDty hCty RD hD RC hC hCeq
  | fam hA hn hnp hm hind hsh hps hu hz Rs RsF RsI hFld hFldF hFldeq hFldRec hFldFeq hxsD hFldI hFldIeq hFldIRec hFldIdom =>
      have e := whTyA_det hA (whTyA_self hA) hn hn₀
      subst e
      exact .fam hA₀ hn hnp hm hind hsh hps hu hz Rs RsF RsI hFld hFldF hFldeq hFldRec hFldFeq hxsD hFldI hFldIeq hFldIRec hFldIdom
  | stuck hA hN hnp =>
      have e := whTyA_det hA (whTyA_self hA) hN.1 hn₀
      subst e
      exact .stuck hA₀ hN hnp

/-- every type equality is a type conversion (the datum every clause carries). -/
theorem eqKA_tyConvg {Γ : LCtxA} {A B : ExprA} (h : EqKAg E I n ρ₀ k LE LT Γ A B) :
    Nonempty (TyConvA E I n Γ A B) := by
  cases h with
  | sort _ _ _ _ hc => exact hc
  | pi _ _ _ _ _ _ _ _ _ _ _ _ hc => exact hc
  | fam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc => exact hc
  | stuck _ _ _ _ hc _ => exact hc

/-- the type's own typing, at the chain's sort. -/
theorem tyKA_hasTyg {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKAg E I n ρ₀ k LE LT Γ A R) : ∃ u, Nonempty (HasTyA E I n Γ A (.sort u)) := by
  cases h with
  | prop hA _ _ => exact whTyA_hasTy_head hA
  | sortT hA _ _ => exact whTyA_hasTy_head hA
  | sortP hA _ => exact whTyA_hasTy_head hA
  | pi hA _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hA
  | fam hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hA
  | stuck hA _ => exact whTyA_hasTy_head hA

/-! ## escape -/

/-- a related pair is convertible at the type. -/
theorem escapeAg {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKAg E I n ρ₀ k LE LT Γ A R) {a b : ExprA} (hr : R a b) :
    Nonempty (ConvA E I n Γ a b A) := by
  cases h with
  | prop hA _ _ =>
      obtain ⟨_, _, hc⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc => hc.elim fun c => ⟨convA_of_tyConvA c tc.symm⟩
  | sortT hA _ _ =>
      obtain ⟨_, _, _, _, _, hc⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc => hc.elim fun c => ⟨convA_of_tyConvA c tc.symm⟩
  | sortP hA _ =>
      obtain ⟨_, _, _, _, hc, _⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc => hc.elim fun c => ⟨convA_of_tyConvA c tc.symm⟩
  | pi hA _ _ _ _ _ _ _ _ =>
      obtain ⟨_, _, _, hc⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc => hc.elim fun c => ⟨convA_of_tyConvA c tc.symm⟩
  | fam hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have hc := lfpWA_famPhiWA_conv hr
      exact (whTyA_tyConv hA).elim fun tc => hc.elim fun c => ⟨convA_of_tyConvA c tc.symm⟩
  | stuck hA _ _ =>
      obtain ⟨_, _, hc, _⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc => hc.elim fun c => ⟨convA_of_tyConvA c tc.symm⟩

/-- a related pair is typed at the type. -/
theorem escapeA_hasTyg {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKAg E I n ρ₀ k LE LT Γ A R) {a b : ExprA} (hr : R a b) :
    Nonempty (HasTyA E I n Γ a A) ∧ Nonempty (HasTyA E I n Γ b A) := by
  cases h with
  | prop hA _ _ =>
      obtain ⟨ha, hb, _⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc =>
        ⟨ha.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩, hb.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩⟩
  | sortT hA _ _ =>
      obtain ⟨_, _, _, ha, hb, _⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc =>
        ⟨ha.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩, hb.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩⟩
  | sortP hA _ =>
      obtain ⟨_, _, ha, hb, _⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc =>
        ⟨ha.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩, hb.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩⟩
  | pi hA _ _ _ _ _ _ _ _ =>
      obtain ⟨_, ha, hb, _⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc =>
        ⟨ha.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩, hb.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩⟩
  | fam hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨ha, hb⟩ := lfpWA_famPhiWA_hasTy hr
      exact (whTyA_tyConv hA).elim fun tc =>
        ⟨ha.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩, hb.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩⟩
  | stuck hA _ _ =>
      obtain ⟨ha, hb, _, _⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc =>
        ⟨ha.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩, hb.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩⟩

end Red

/-- the knotted forms. -/
theorem escape_LRTyAg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAg E I n ρ₀ k Γ A R) {a b : ExprA} (hr : R a b) :
    Nonempty (ConvA E I n Γ a b A) := by
  rw [LRTyA_eqg] at h
  exact escapeAg h hr

theorem LREqA_tyConvg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A B : ExprA} (h : LREqAg E I n ρ₀ k Γ A B) :
    Nonempty (TyConvA E I n Γ A B) := by
  rw [LREqA_eqg] at h
  exact eqKA_tyConvg h

#print axioms tyKA_of_whTyAg
#print axioms tyKA_of_propNFg
#print axioms tyKA_valid_of_tripleLikeg
#print axioms tyKA_of_whTyA'g
#print axioms eqKA_tyConvg
#print axioms escapeAg
#print axioms escapeA_hasTyg
#print axioms escape_LRTyAg

end Rcic.Declarative.Ann
