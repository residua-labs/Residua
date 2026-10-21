import rcic.RcicAnnLR

/-!
# M2-b (i) — the relation respects typed reduction; escape to conversion
# (amended by M1-d (iv))

Three facts the fundamental theorem leans on, each short because the clauses are
keyed on normal forms and state their data at them: a type and its typed
weak-head normal form carry the SAME relation (`tyKA_of_whTyA`, both ways;
likewise `eqKA_of_whTyA`); every `EqKA` is a `TyConvA` (`eqKA_tyConv`); and
ESCAPE — a related pair is typed and convertible at the type (`escapeA`,
`escapeA_hasTy`), every clause through the `ConvA`/`HasTyA` data it carries,
re-typed from the normal form to the type along the chain (`convA_of_tyConvA`,
`hasTyA_of_tyConvA`). No row, no uniqueness, no hypothesis about `ConvA`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Red
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

/-- a type and its typed normal form carry the same relation. -/
theorem tyKA_of_whTyA {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyA E I n Γ A A₀) (hn₀ : hStepFnA E I.fn Γ A₀ = none)
    (h : TyKA E I n ρ₀ k LE LT Γ A R) : TyKA E I n ρ₀ k LE LT Γ A₀ R := by
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
  | stuck hA hN =>
      have e := whTyA_det hA hA₀ hN.1 hn₀
      subst e
      obtain ⟨_, h'⟩ := whTyA_hasTy_end hA
      exact h'.elim fun h' => .stuck (whTyA_of_hasTy h') hN

/-- a type reducing to a triple-like normal form is valid, with the triple: the
    prop clause or the stuck clause, whichever applies (the relations coincide). -/
theorem tyKA_of_tripleLike {Γ : LCtxA} {A N : ExprA} (hA : WhTyA E I n Γ A N)
    (h : TripleLikeA E I Γ N) :
    TyKA E I n ρ₀ k LE LT Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N)) :=
  h.2.elim (fun hP => .prop hA h.1 hP) (fun hs => .stuck hA ⟨h.1, hs⟩)

/-- a normal form reduces (typed) only to itself. -/
theorem whTyA_self {Γ : LCtxA} {A N : ExprA} (h : WhTyA E I n Γ A N) : WhTyA E I n Γ A A := by
  obtain ⟨_, h'⟩ := whTyA_hasTy_head h
  exact h'.elim fun h' => whTyA_of_hasTy h'

/-- and back: the relation of the normal form is the relation of the type. -/
theorem tyKA_of_whTyA' {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyA E I n Γ A A₀) (hn₀ : hStepFnA E I.fn Γ A₀ = none)
    (h : TyKA E I n ρ₀ k LE LT Γ A₀ R) : TyKA E I n ρ₀ k LE LT Γ A R := by
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
  | stuck hA hN =>
      have e := whTyA_det hA (whTyA_self hA) hN.1 hn₀
      subst e
      exact .stuck hA₀ hN

/-- every type equality is a type conversion (the datum every clause carries). -/
theorem eqKA_tyConv {Γ : LCtxA} {A B : ExprA} (h : EqKA E I n ρ₀ k LE LT Γ A B) :
    Nonempty (TyConvA E I n Γ A B) := by
  cases h with
  | sort _ _ _ _ hc => exact hc
  | pi _ _ _ _ _ _ _ _ _ _ _ _ hc => exact hc
  | fam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc => exact hc
  | stuck _ _ _ _ hc => exact hc

/-- the type's own typing, at the chain's sort. -/
theorem tyKA_hasTy {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKA E I n ρ₀ k LE LT Γ A R) : ∃ u, Nonempty (HasTyA E I n Γ A (.sort u)) := by
  cases h with
  | prop hA _ _ => exact whTyA_hasTy_head hA
  | sortT hA _ _ => exact whTyA_hasTy_head hA
  | sortP hA _ => exact whTyA_hasTy_head hA
  | pi hA _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hA
  | fam hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hA
  | stuck hA _ => exact whTyA_hasTy_head hA

/-! ## escape -/

/-- a related pair is convertible at the type. -/
theorem escapeA {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKA E I n ρ₀ k LE LT Γ A R) {a b : ExprA} (hr : R a b) :
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
  | stuck hA _ =>
      obtain ⟨_, _, hc⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc => hc.elim fun c => ⟨convA_of_tyConvA c tc.symm⟩

/-- a related pair is typed at the type. -/
theorem escapeA_hasTy {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKA E I n ρ₀ k LE LT Γ A R) {a b : ExprA} (hr : R a b) :
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
  | stuck hA _ =>
      obtain ⟨ha, hb, _⟩ := hr
      exact (whTyA_tyConv hA).elim fun tc =>
        ⟨ha.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩, hb.elim fun h => ⟨hasTyA_of_tyConvA h tc.symm⟩⟩

end Red

/-- the knotted forms. -/
theorem escape_LRTyA {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyA E I n ρ₀ k Γ A R) {a b : ExprA} (hr : R a b) :
    Nonempty (ConvA E I n Γ a b A) := by
  rw [LRTyA_eq] at h
  exact escapeA h hr

theorem LREqA_tyConv {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A B : ExprA} (h : LREqA E I n ρ₀ k Γ A B) :
    Nonempty (TyConvA E I n Γ A B) := by
  rw [LREqA_eq] at h
  exact eqKA_tyConv h

#print axioms tyKA_of_whTyA
#print axioms tyKA_of_whTyA'
#print axioms eqKA_tyConv
#print axioms escapeA
#print axioms escapeA_hasTy
#print axioms escape_LRTyA

end Rcic.Declarative.Ann
