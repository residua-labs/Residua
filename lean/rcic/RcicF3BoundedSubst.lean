import rcic.RcicF3BoundedWeaken
import rcic.RcicF3BoundedPiSpine

/-!
# Bounded typed substitution and an actual typed beta-domain producer

The existing structural typed substitution argument is repeated with its
LOKt/LOKc obligations retained at the original sigma, N and K. Its member
substitution-stability premise is produced from EnvClosed. Arbitrary
assumption and let-binding positions, dependent binders, iota endpoints and
all conversion constructors are included; no conversion row is supplied
externally. A let slot is substituted by its own stored value.

The public beta_telescope producer contracts an actual typed lambda body
at an argument typed at that lambda's own domain, then extracts all domains
of a literal Pi reduct. This is the aligned beta case. An arbitrary typing
of a raw beta redex may convert the lambda's Pi type before application;
decomposing that conversion is still a separate unpaid obligation. The
corresponding zeta producer uses the actual let-typing premises, and
zeta_subject_reduction replays every outer type conversion unchanged.
A general
piTelescopeFuel-to-typing bridge, including converted application heads
and bounded delta, is not asserted here. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.BoundedTransport
open Rcic.Declarative

private def TyBound (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (e A : Expr Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) : Prop :=
  ∃ d : HasTyT E n Γ e A, LOKt σ N K d

private def CvBound (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a b T : Expr Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) : Prop :=
  ∃ d : ConvT E n Γ a b T, LOKc σ N K d

/-- The selected slot is an assumption, or a let whose own stored value
is the replacement. This is a literal local-context fact. -/
def Slot (Γ : LCtx) (j : Nat) (t v : Expr Nat) : Prop :=
  Γ[j]? = some (.assumption t) ∨ Γ[j]? = some (.letBinding t v)

private theorem slot_cons {Γ : LCtx} {j : Nat} {t v : Expr Nat}
    (ins : LocalDecl) (h : Slot Γ j t v) : Slot (ins :: Γ) (j + 1) t v := by
  simpa only [Slot, List.getElem?_cons_succ] using h

private theorem slot_type {Γ : LCtx} {j : Nat} {t v : Expr Nat}
    (h : Slot Γ j t v) : lookupType Γ j = some (Rcic.Declarative.lift 0 (j + 1) t) := by
  rcases h with h | h
  · exact lookupType_get_assumption h
  · have h' : Γ.get? j = some (.letBinding t v) := by
      rw [List.get?_eq_getElem?]
      exact h
    simp only [lookupType, h']

private theorem slot_value {Γ : LCtx} {j : Nat} {t v : Expr Nat}
    (h : Γ[j]? = some (.letBinding t v)) :
    lookupValue Γ j = some (Rcic.Declarative.lift 0 (j + 1) v) := by
  have h' : Γ.get? j = some (.letBinding t v) := by
    rw [List.get?_eq_getElem?]
    exact h
  simp only [lookupValue, h']

private theorem replacement_cons {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ins : LocalDecl) {v t : Expr Nat} {j : Nat} {Γ : LCtx}
    (dv : HasTyT E n (substRemove v j Γ) (Rcic.Declarative.lift 0 j v) (Rcic.Declarative.lift 0 j t))
    (hv : LOKt σ N K dv) :
    ∃ dv' : HasTyT E n (substRemove v (j + 1) (ins :: Γ))
      (Rcic.Declarative.lift 0 (j + 1) v) (Rcic.Declarative.lift 0 (j + 1) t), LOKt σ N K dv' := by
  have h := Rcic.Declarative.Ann.Lok.hasTyT_weaken_lok (instDecl j v ins) hcl
    (σ := σ) (N := N) (K := K) (c := 0) dv hv
  rw [lift_lift_merge 1 j 0 0 (by omega) (by omega),
    lift_lift_merge 1 j 0 0 (by omega) (by omega)] at h
  exact h

mutual
/-- Substitution at an assumption or its own let value preserves the
original bounds, including every conversion node of the derivation. -/
theorem subst_any_t {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    (d : HasTyT E n Γ e A) → LOKt σ N K d →
    Slot Γ j t v →
    (dv : HasTyT E n (substRemove v j Γ) (Rcic.Declarative.lift 0 j v) (Rcic.Declarative.lift 0 j t)) →
    LOKt σ N K dv →
    ∃ d' : HasTyT E n (substRemove v j Γ)
      (instantiate j (Rcic.Declarative.lift 0 j v) e) (instantiate j (Rcic.Declarative.lift 0 j v) A),
      LOKt σ N K d'
  | _, _, _, _, .sort _ l, hd, _, _, _ => ⟨.sort _ l, hd⟩
  | j, Γ, _, _, .bvar _ i A hlook, _hd, hget, dv, hv => by
      change TyBound E n (substRemove v j Γ)
        (instantiate j (Rcic.Declarative.lift 0 j v) (.bvar i))
        (instantiate j (Rcic.Declarative.lift 0 j v) A) σ N K
      by_cases hij : i = j
      · subst hij
        rw [slot_type hget] at hlook
        injection hlook with hA
        subst hA
        simp only [instantiate, if_pos rfl]
        rw [instantiate_lift_cancel (i + 1) 0 i (Rcic.Declarative.lift 0 i v) (by omega) (by omega)]
        exact ⟨dv, hv⟩
      · by_cases hlt : i < j
        · simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          refine ⟨.bvar _ i _ (lookupType_substRemove_lt (v := v) hlt hlook), ?_⟩
          exact True.intro
        · simp only [instantiate, if_neg hij, if_pos (by omega : j < i),
            show i - 1 + 1 = i from by omega]
          refine ⟨.bvar _ (i - 1) _
            (lookupType_substRemove_gt (v := v) (show j < i from by omega) hlook), ?_⟩
          exact True.intro
  | j, _, _, _, .const _ r ls m hm hn hls, hd, _, _, _ => by
      simp only [instantiate]
      rw [(stable_of_closed hcl r m hm).1 ls (Rcic.Declarative.lift 0 j v) j]
      exact ⟨.const _ r ls m hm hn hls, hd⟩
  | j, Γ, _, _, .pi _ A u B w dA dB, hd, hget, dv, hv => by
      obtain ⟨dv', hv'⟩ := replacement_cons hcl σ N K (.assumption A) dv hv
      have hget' : Slot (.assumption A :: Γ) (j + 1) t v := slot_cons _ hget
      have hB := subst_any_t hcl σ N K v t (j := j + 1) dB hd.2.2.2 hget' dv' hv'
      have hA := subst_any_t hcl σ N K v t dA hd.2.2.1 hget dv hv
      simp only [substRemove_succ_cons, instDecl, instantiate] at hB
      simp only [instantiate] at hA
      obtain ⟨dB', hdB⟩ := hB
      obtain ⟨dA', hdA⟩ := hA
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact ⟨.pi _ _ u _ w dA' dB', hd.1, hd.2.1, hdA, hdB⟩
  | j, Γ, _, _, .lam _ A u body B dA db, hd, hget, dv, hv => by
      obtain ⟨dv', hv'⟩ := replacement_cons hcl σ N K (.assumption A) dv hv
      have hget' : Slot (.assumption A :: Γ) (j + 1) t v := slot_cons _ hget
      have hb := subst_any_t hcl σ N K v t (j := j + 1) db hd.2 hget' dv' hv'
      have hA := subst_any_t hcl σ N K v t dA hd.1 hget dv hv
      simp only [substRemove_succ_cons, instDecl] at hb
      simp only [instantiate] at hA
      obtain ⟨db', hdb⟩ := hb
      obtain ⟨dA', hdA⟩ := hA
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact ⟨.lam _ _ u _ _ dA' db', hdA, hdb⟩
  | j, _, _, _, .app _ f a A B df da, hd, hget, dv, hv => by
      have hf := subst_any_t hcl σ N K v t df hd.1 hget dv hv
      have ha := subst_any_t hcl σ N K v t da hd.2 hget dv hv
      simp only [instantiate] at hf
      obtain ⟨df', hdf⟩ := hf
      obtain ⟨da', hda⟩ := ha
      simp only [instantiate, instantiate0]
      rw [instantiate_instantiate 0 j a (Rcic.Declarative.lift 0 j v) (by omega) B]
      exact ⟨.app _ _ _ _ _ df' da', hdf, hda⟩
  | j, Γ, _, _, .letE _ A u value B body dA dw db, hd, hget, dv, hv => by
      obtain ⟨dv', hv'⟩ := replacement_cons hcl σ N K (.letBinding A value) dv hv
      have hget' : Slot (.letBinding A value :: Γ) (j + 1) t v := slot_cons _ hget
      have hb := subst_any_t hcl σ N K v t (j := j + 1) db hd.2.2 hget' dv' hv'
      have hA := subst_any_t hcl σ N K v t dA hd.1 hget dv hv
      have hw := subst_any_t hcl σ N K v t dw hd.2.1 hget dv hv
      simp only [substRemove_succ_cons, instDecl] at hb
      simp only [instantiate] at hA
      obtain ⟨db', hdb⟩ := hb
      obtain ⟨dA', hdA⟩ := hA
      obtain ⟨dw', hdw⟩ := hw
      simp only [instantiate, instantiate0]
      rw [instantiate_instantiate 0 j value (Rcic.Declarative.lift 0 j v) (by omega) B,
        lift_lift_merge (e := v) 1 j 0 0 (by omega) (by omega)]
      exact ⟨.letE _ _ u _ _ _ dA' dw' db', hdA, hdw, hdb⟩
  | j, _, _, _, .lit _ q T de, hd, hget, dv, hv => by
      have he := subst_any_t hcl σ N K v t de hd hget dv hv
      rw [natExpand_instantiate j (Rcic.Declarative.lift 0 j v) q] at he
      obtain ⟨de', hde⟩ := he
      simp only [instantiate]
      exact ⟨.lit _ _ _ de', hde⟩
  | j, _, _, _, .conv _ e A B u d q, hd, hget, dv, hv => by
      obtain ⟨d', hd'⟩ := subst_any_t hcl σ N K v t d hd.1 hget dv hv
      obtain ⟨q', hq'⟩ := subst_any_c hcl σ N K v t q hd.2 hget dv hv
      exact ⟨.conv _ _ _ _ u d' q', hd', hq'⟩
  termination_by j Γ e A d _ _ _ _ => sizeOf d
  decreasing_by all_goals (simp; omega)

/-- The conversion companion retains its original bound through the
same substitution; all typed premises are transformed by subst_t. -/
theorem subst_any_c {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (v t : Expr Nat) :
    {j : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    (d : ConvT E n Γ a b T) → LOKc σ N K d →
    Slot Γ j t v →
    (dv : HasTyT E n (substRemove v j Γ) (Rcic.Declarative.lift 0 j v) (Rcic.Declarative.lift 0 j t)) →
    LOKt σ N K dv →
    ∃ d' : ConvT E n (substRemove v j Γ)
      (instantiate j (Rcic.Declarative.lift 0 j v) a) (instantiate j (Rcic.Declarative.lift 0 j v) b)
      (instantiate j (Rcic.Declarative.lift 0 j v) T), LOKc σ N K d'
  | j, _, _, _, _, .refl _ _ _ d, hd, hget, dv, hv => by
      obtain ⟨d', hd'⟩ := subst_any_t hcl σ N K v t d hd hget dv hv
      exact ⟨.refl _ _ _ d', hd'⟩
  | j, _, _, _, _, .symm _ _ _ _ q, hq, hget, dv, hv => by
      obtain ⟨q', hq'⟩ := subst_any_c hcl σ N K v t q hq hget dv hv
      exact ⟨.symm _ _ _ _ q', hq'⟩
  | j, _, _, _, _, .trans _ _ _ _ _ q r, hd, hget, dv, hv => by
      obtain ⟨q', hq'⟩ := subst_any_c hcl σ N K v t q hd.1 hget dv hv
      obtain ⟨r', hr'⟩ := subst_any_c hcl σ N K v t r hd.2 hget dv hv
      exact ⟨.trans _ _ _ _ _ q' r', hq', hr'⟩
  | j, Γ, _, _, _, .beta _ A body arg B u dA db da, hd, hget, dv, hv => by
      obtain ⟨dv', hv'⟩ := replacement_cons hcl σ N K (.assumption A) dv hv
      have hget' : Slot (.assumption A :: Γ) (j + 1) t v := slot_cons _ hget
      have hb := subst_any_t hcl σ N K v t (j := j + 1) db hd.2.1 hget' dv' hv'
      have hA := subst_any_t hcl σ N K v t dA hd.1 hget dv hv
      have ha := subst_any_t hcl σ N K v t da hd.2.2 hget dv hv
      simp only [substRemove_succ_cons, instDecl] at hb
      simp only [instantiate] at hA ha
      obtain ⟨db', hdb⟩ := hb
      obtain ⟨dA', hdA⟩ := hA
      obtain ⟨da', hda⟩ := ha
      simp only [instantiate, instantiate0]
      rw [instantiate_instantiate 0 j arg (Rcic.Declarative.lift 0 j v) (by omega) body,
        instantiate_instantiate 0 j arg (Rcic.Declarative.lift 0 j v) (by omega) B]
      have hlv : Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 j v) = Rcic.Declarative.lift 0 (j + 1) v :=
        lift_lift_merge (e := v) 1 j 0 0 (by omega) (by omega)
      first | rw [hlv] | skip
      exact ⟨.beta _ _ _ _ _ u dA' db' da', hdA, hdb, hda⟩
  | j, Γ, _, _, _, .zeta _ A value body B u dA dw db, hd, hget, dv, hv => by
      obtain ⟨dv', hv'⟩ := replacement_cons hcl σ N K (.letBinding A value) dv hv
      have hget' : Slot (.letBinding A value :: Γ) (j + 1) t v := slot_cons _ hget
      have hb := subst_any_t hcl σ N K v t (j := j + 1) db hd.2.2 hget' dv' hv'
      have hA := subst_any_t hcl σ N K v t dA hd.1 hget dv hv
      have hw := subst_any_t hcl σ N K v t dw hd.2.1 hget dv hv
      simp only [substRemove_succ_cons, instDecl] at hb
      simp only [instantiate] at hA
      obtain ⟨db', hdb⟩ := hb
      obtain ⟨dA', hdA⟩ := hA
      obtain ⟨dw', hdw⟩ := hw
      simp only [instantiate, instantiate0]
      rw [instantiate_instantiate 0 j value (Rcic.Declarative.lift 0 j v) (by omega) body,
        instantiate_instantiate 0 j value (Rcic.Declarative.lift 0 j v) (by omega) B]
      have hlv : Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 j v) = Rcic.Declarative.lift 0 (j + 1) v :=
        lift_lift_merge (e := v) 1 j 0 0 (by omega) (by omega)
      first | rw [hlv] | skip
      exact ⟨.zeta _ _ _ _ _ u dA' dw' db', hdA, hdw, hdb⟩
  | j, Γ, _, _, _, .zetaLocal _ i A w hval hty dw, hd, hget, dv, hv => by
      change CvBound E n (substRemove v j Γ)
        (instantiate j (Rcic.Declarative.lift 0 j v) (.bvar i))
        (instantiate j (Rcic.Declarative.lift 0 j v) w)
        (instantiate j (Rcic.Declarative.lift 0 j v) A) σ N K
      by_cases hij : i = j
      · subst hij
        rcases hget with hg | hg
        · rw [lookupValue_get_assumption hg] at hval
          cases hval
        · rw [slot_type (Or.inr hg)] at hty
          injection hty with heA
          subst heA
          rw [slot_value hg] at hval
          injection hval with hew
          subst hew
          simp only [instantiate, if_pos rfl]
          rw [instantiate_lift_cancel (i + 1) 0 i (Rcic.Declarative.lift 0 i v) (by omega) (by omega),
            instantiate_lift_cancel (i + 1) 0 i (Rcic.Declarative.lift 0 i v) (by omega) (by omega)]
          exact ⟨.refl _ _ _ dv, hv⟩
      · obtain ⟨dw', hdw⟩ := subst_any_t hcl σ N K v t dw hd hget dv hv
        by_cases hlt : i < j
        · simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
          refine ⟨.zetaLocal _ i _ _ (lookupValue_substRemove_lt (v := v) hlt hval)
            (lookupType_substRemove_lt (v := v) hlt hty) dw', ?_⟩
          exact hdw
        · simp only [instantiate, if_neg hij, if_pos (by omega : j < i),
            show i - 1 + 1 = i from by omega]
          refine ⟨.zetaLocal _ (i - 1) _ _
            (lookupValue_substRemove_gt (v := v) (show j < i from by omega) hval)
            (lookupType_substRemove_gt (v := v) (show j < i from by omega) hty) dw', ?_⟩
          exact hdw
  | j, _, _, _, _, .delta _ r ls m b hm hb ht hn hls db, hd, hget, dv, hv => by
      have hB := subst_any_t hcl σ N K v t db hd.2 hget dv hv
      rw [(stable_of_closed hcl r m hm).2 b hb ls (Rcic.Declarative.lift 0 j v) j,
        (stable_of_closed hcl r m hm).1 ls (Rcic.Declarative.lift 0 j v) j] at hB
      obtain ⟨db', hdb⟩ := hB
      rw [(stable_of_closed hcl r m hm).2 b hb ls (Rcic.Declarative.lift 0 j v) j,
        (stable_of_closed hcl r m hm).1 ls (Rcic.Declarative.lift 0 j v) j]
      exact ⟨.delta _ r ls m b hm hb ht hn hls db', hd.1, hdb⟩
  | j, _, _, _, _, .iota _ lhs rhs T hi dl dr, hd, hget, dv, hv => by
      obtain ⟨dl', hdl⟩ := subst_any_t hcl σ N K v t dl hd.1 hget dv hv
      obtain ⟨dr', hdr⟩ := subst_any_t hcl σ N K v t dr hd.2 hget dv hv
      exact ⟨.iota _ _ _ _ (iotaSubst E lhs rhs hi (Rcic.Declarative.lift 0 j v) j) dl' dr', hdl, hdr⟩
  | j, _, _, _, _, .lit _ q e T he de, hd, hget, dv, hv => by
      have hE := subst_any_t hcl σ N K v t de hd hget dv hv
      cases he
      rw [natExpand_instantiate j (Rcic.Declarative.lift 0 j v) q] at hE
      obtain ⟨de', hde⟩ := hE
      simp only [instantiate]
      rw [natExpand_instantiate j (Rcic.Declarative.lift 0 j v) q]
      exact ⟨.lit _ _ _ _ (.of q) de', hde⟩
  | j, _, _, _, _, .app _ f g a b A B q r, hd, hget, dv, hv => by
      have hq := subst_any_c hcl σ N K v t q hd.1 hget dv hv
      have hr := subst_any_c hcl σ N K v t r hd.2 hget dv hv
      simp only [instantiate] at hq
      obtain ⟨q', hq'⟩ := hq
      obtain ⟨r', hr'⟩ := hr
      simp only [instantiate, instantiate0]
      rw [instantiate_instantiate 0 j a (Rcic.Declarative.lift 0 j v) (by omega) B]
      exact ⟨.app _ _ _ _ _ _ _ q' r', hq', hr'⟩
  | j, Γ, _, _, _, .lam _ A A' b b' B u q r, hd, hget, dv, hv => by
      obtain ⟨dv', hv'⟩ := replacement_cons hcl σ N K (.assumption A) dv hv
      have hget' : Slot (.assumption A :: Γ) (j + 1) t v := slot_cons _ hget
      have hr := subst_any_c hcl σ N K v t (j := j + 1) r hd.2 hget' dv' hv'
      have hq := subst_any_c hcl σ N K v t q hd.1 hget dv hv
      simp only [substRemove_succ_cons, instDecl] at hr
      simp only [instantiate] at hq
      obtain ⟨r', hr'⟩ := hr
      obtain ⟨q', hq'⟩ := hq
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact ⟨.lam _ _ _ _ _ _ u q' r', hq', hr'⟩
  | j, Γ, _, _, _, .pi _ A A' B B' u w q r, hd, hget, dv, hv => by
      obtain ⟨dv', hv'⟩ := replacement_cons hcl σ N K (.assumption A) dv hv
      have hget' : Slot (.assumption A :: Γ) (j + 1) t v := slot_cons _ hget
      have hr := subst_any_c hcl σ N K v t (j := j + 1) r hd.2.2.2 hget' dv' hv'
      have hq := subst_any_c hcl σ N K v t q hd.2.2.1 hget dv hv
      simp only [substRemove_succ_cons, instDecl, instantiate] at hr
      simp only [instantiate] at hq
      obtain ⟨r', hr'⟩ := hr
      obtain ⟨q', hq'⟩ := hq
      simp only [instantiate]
      rw [lift_lift_merge 1 j 0 0 (by omega) (by omega)]
      exact ⟨.pi _ _ _ _ _ u w q' r', hd.1, hd.2.1, hq', hr'⟩
  | j, Γ, _, _, _, .letE _ A A' w w' b b' B u q r s, hd, hget, dv, hv => by
      obtain ⟨dv', hv'⟩ := replacement_cons hcl σ N K (.letBinding A w) dv hv
      have hget' : Slot (.letBinding A w :: Γ) (j + 1) t v := slot_cons _ hget
      have hs := subst_any_c hcl σ N K v t (j := j + 1) s hd.2.2 hget' dv' hv'
      have hq := subst_any_c hcl σ N K v t q hd.1 hget dv hv
      have hr := subst_any_c hcl σ N K v t r hd.2.1 hget dv hv
      simp only [substRemove_succ_cons, instDecl] at hs
      simp only [instantiate] at hq
      obtain ⟨s', hs'⟩ := hs
      obtain ⟨q', hq'⟩ := hq
      obtain ⟨r', hr'⟩ := hr
      simp only [instantiate, instantiate0]
      rw [instantiate_instantiate 0 j w (Rcic.Declarative.lift 0 j v) (by omega) B,
        lift_lift_merge (e := v) 1 j 0 0 (by omega) (by omega)]
      exact ⟨.letE _ _ _ _ _ _ _ _ u q' r' s', hq', hr', hs'⟩
  | _, _, _, _, _, .sorts _ l l' he, hd, _, _, _ => ⟨.sorts _ l l' he, hd⟩
  | j, _, _, _, _, .consts _ r ls ls' m hm hn hls hls' he, hd, _, _, _ => by
      simp only [instantiate]
      rw [(stable_of_closed hcl r m hm).1 ls (Rcic.Declarative.lift 0 j v) j]
      exact ⟨.consts _ r ls ls' m hm hn hls hls' he, hd⟩
  | j, _, _, _, _, .eta _ f A B df, hd, hget, dv, hv => by
      have hf := subst_any_t hcl σ N K v t df hd hget dv hv
      simp only [instantiate] at hf ⊢
      have hp : instantiate (j + 1) (Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 j v)) (Rcic.Declarative.lift 0 1 f) =
          Rcic.Declarative.lift 0 1 (instantiate j (Rcic.Declarative.lift 0 j v) f) := by
        rw [lift_instantiate_high 1 0 j (Rcic.Declarative.lift 0 j v) (by omega),
          show 1 + j = j + 1 from by omega]
      rw [show (if (0 : Nat) = j + 1 then Rcic.Declarative.lift 0 1 (Rcic.Declarative.lift 0 j v)
        else if j + 1 < 0 then Expr.bvar (0 - 1) else Expr.bvar 0) = Expr.bvar 0
        from by rw [if_neg (by omega : ¬ (0 : Nat) = j + 1),
          if_neg (by omega : ¬ j + 1 < 0)], hp]
      obtain ⟨df', hdf⟩ := hf
      exact ⟨.eta _ _ _ _ df', hdf⟩
  | j, _, _, _, _, .irr _ A p q dA dp dq, hd, hget, dv, hv => by
      have hA := subst_any_t hcl σ N K v t dA hd.1 hget dv hv
      simp only [instantiate] at hA
      obtain ⟨dA', hdA⟩ := hA
      obtain ⟨dp', hdp⟩ := subst_any_t hcl σ N K v t dp hd.2.1 hget dv hv
      obtain ⟨dq', hdq⟩ := subst_any_t hcl σ N K v t dq hd.2.2 hget dv hv
      exact ⟨.irr _ _ _ _ dA' dp' dq', hdA, hdp, hdq⟩
  | j, _, _, _, _, .tyConv _ a b A A' u q r, hd, hget, dv, hv => by
      obtain ⟨q', hq'⟩ := subst_any_c hcl σ N K v t q hd.1 hget dv hv
      have hr := subst_any_c hcl σ N K v t r hd.2 hget dv hv
      simp only [instantiate] at hr
      obtain ⟨r', hr'⟩ := hr
      exact ⟨.tyConv _ _ _ _ _ u q' r', hq', hr'⟩
  termination_by j Γ a b T d _ _ _ _ => sizeOf d
  decreasing_by all_goals (simp; omega)
end

/-- The original assumption-substitution interface, with no let-slot
premise or extra semantic input. -/
theorem subst_t {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (v t : Expr Nat) {j : Nat} {Γ : LCtx} {e A : Expr Nat}
    (d : HasTyT E n Γ e A) (hd : LOKt σ N K d)
    (hget : Γ[j]? = some (.assumption t))
    (dv : HasTyT E n (substRemove v j Γ) (Rcic.Declarative.lift 0 j v) (Rcic.Declarative.lift 0 j t))
    (hv : LOKt σ N K dv) :
    ∃ d' : HasTyT E n (substRemove v j Γ)
      (instantiate j (Rcic.Declarative.lift 0 j v) e) (instantiate j (Rcic.Declarative.lift 0 j v) A),
      LOKt σ N K d' :=
  subst_any_t hcl σ N K v t d hd (Or.inl hget) dv hv

theorem subst_c {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (v t : Expr Nat) {j : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (d : ConvT E n Γ a b T) (hd : LOKc σ N K d)
    (hget : Γ[j]? = some (.assumption t))
    (dv : HasTyT E n (substRemove v j Γ) (Rcic.Declarative.lift 0 j v) (Rcic.Declarative.lift 0 j t))
    (hv : LOKt σ N K dv) :
    ∃ d' : ConvT E n (substRemove v j Γ)
      (instantiate j (Rcic.Declarative.lift 0 j v) a) (instantiate j (Rcic.Declarative.lift 0 j v) b)
      (instantiate j (Rcic.Declarative.lift 0 j v) T), LOKc σ N K d' :=
  subst_any_c hcl σ N K v t d hd (Or.inl hget) dv hv

theorem subst0_t {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A body B arg : Expr Nat}
    (db : HasTyT E n (.assumption A :: Γ) body B) (hb : LOKt σ N K db)
    (da : HasTyT E n Γ arg A) (ha : LOKt σ N K da) :
    ∃ d : HasTyT E n Γ (instantiate0 arg body) (instantiate0 arg B),
      LOKt σ N K d := by
  have harg : ∃ da' : HasTyT E n
      (substRemove arg 0 (.assumption A :: Γ)) (Rcic.Declarative.lift 0 0 arg) (Rcic.Declarative.lift 0 0 A),
      LOKt σ N K da' := by
    rw [lift_zero, lift_zero]
    exact ⟨da, ha⟩
  obtain ⟨da', ha'⟩ := harg
  have h := subst_t hcl σ N K arg A (j := 0) db hb (by simp) da' ha'
  rw [lift_zero] at h
  exact h

theorem let_subst0_t {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A body B value : Expr Nat}
    (db : HasTyT E n (.letBinding A value :: Γ) body B) (hb : LOKt σ N K db)
    (dv : HasTyT E n Γ value A) (hv : LOKt σ N K dv) :
    ∃ d : HasTyT E n Γ (instantiate0 value body) (instantiate0 value B),
      LOKt σ N K d := by
  have hvalue : ∃ dv' : HasTyT E n
      (substRemove value 0 (.letBinding A value :: Γ))
      (Rcic.Declarative.lift 0 0 value) (Rcic.Declarative.lift 0 0 A), LOKt σ N K dv' := by
    rw [lift_zero, lift_zero]
    exact ⟨dv, hv⟩
  obtain ⟨dv', hv'⟩ := hvalue
  have h := subst_any_t hcl σ N K value A (j := 0) db hb (Or.inr (by simp)) dv' hv'
  rw [lift_zero] at h
  exact h

/-- The aligned typed beta rule produces the bounded reduct and its
bounded conversion. The input domain is the lambda's actual annotation. -/
theorem beta_reduct {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A body B arg : Expr Nat} {u : Level}
    (dA : HasTyT E n Γ A (.sort u)) (hA : LOKt σ N K dA)
    (db : HasTyT E n (.assumption A :: Γ) body B) (hb : LOKt σ N K db)
    (da : HasTyT E n Γ arg A) (ha : LOKt σ N K da) :
    (∃ d : HasTyT E n Γ (instantiate0 arg body) (instantiate0 arg B),
      LOKt σ N K d) ∧
    (∃ c : ConvT E n Γ (.app (.lam A body) arg)
      (instantiate0 arg body) (instantiate0 arg B), LOKc σ N K c) :=
  ⟨subst0_t hcl σ N K db hb da ha, ⟨.beta Γ A body arg B u dA db da, hA, hb, ha⟩⟩

/-- Contract the actual bounded typed beta premises and extract every
dependent domain of its Pi reduct, retaining the complete terminal body. -/
theorem beta_telescope {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A body arg : Expr Nat} {u l : Level}
    (dA : HasTyT E n Γ A (.sort u)) (hA : LOKt σ N K dA)
    (db : HasTyT E n (.assumption A :: Γ) body (.sort l)) (hb : LOKt σ N K db)
    (da : HasTyT E n Γ arg A) (ha : LOKt σ N K da)
    (ds : List (Expr Nat)) (terminal : Expr Nat)
    (hshape : instantiate0 arg body = policyPi ds terminal) :
    BoundedPiSpine.Domains (E := E) (n := n) σ N K Γ ds ∧
      ∃ (v : Level) (dt : HasTyT E n (BoundedPiSpine.context Γ ds) terminal (.sort v)),
        LOKt σ N K dt := by
  have h := (beta_reduct hcl σ N K dA hA db hb da ha).1
  change ∃ d : HasTyT E n Γ (instantiate0 arg body) (.sort l), LOKt σ N K d at h
  rw [hshape] at h
  obtain ⟨d, hd⟩ := h
  exact BoundedPiSpine.telescope σ N K ds terminal d hd

/-- Actual typed let elimination preserves the same bound without
assuming endpoint typing or a conversion-row supplier. -/
theorem zeta_reduct {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A body B value : Expr Nat} {u : Level}
    (dA : HasTyT E n Γ A (.sort u)) (hA : LOKt σ N K dA)
    (dv : HasTyT E n Γ value A) (hv : LOKt σ N K dv)
    (db : HasTyT E n (.letBinding A value :: Γ) body B) (hb : LOKt σ N K db) :
    (∃ d : HasTyT E n Γ (instantiate0 value body) (instantiate0 value B),
      LOKt σ N K d) ∧
    (∃ c : ConvT E n Γ (.letE A value body)
      (instantiate0 value body) (instantiate0 value B), LOKc σ N K c) :=
  ⟨let_subst0_t hcl σ N K db hb dv hv,
    ⟨.zeta Γ A value body B u dA dv db, hA, hv, hb⟩⟩

theorem zeta_telescope {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A body value : Expr Nat} {u l : Level}
    (dA : HasTyT E n Γ A (.sort u)) (hA : LOKt σ N K dA)
    (dv : HasTyT E n Γ value A) (hv : LOKt σ N K dv)
    (db : HasTyT E n (.letBinding A value :: Γ) body (.sort l)) (hb : LOKt σ N K db)
    (ds : List (Expr Nat)) (terminal : Expr Nat)
    (hshape : instantiate0 value body = policyPi ds terminal) :
    BoundedPiSpine.Domains (E := E) (n := n) σ N K Γ ds ∧
      ∃ (v : Level) (dt : HasTyT E n (BoundedPiSpine.context Γ ds) terminal (.sort v)),
        LOKt σ N K dt := by
  have h := (zeta_reduct hcl σ N K dA hA dv hv db hb).1
  change ∃ d : HasTyT E n Γ (instantiate0 value body) (.sort l), LOKt σ N K d at h
  rw [hshape] at h
  obtain ⟨d, hd⟩ := h
  exact BoundedPiSpine.telescope σ N K ds terminal d hd

private theorem zeta_aux {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A value body : Expr Nat} :
    {e T : Expr Nat} → (d : HasTyT E n Γ e T) → LOKt σ N K d →
      e = .letE A value body →
      ∃ d' : HasTyT E n Γ (instantiate0 value body) T, LOKt σ N K d'
  | _, _, .letE _ A0 u value0 B body0 dA dv db, hd, he => by
      injection he with hA hvalue hbody
      subst hA
      subst hvalue
      subst hbody
      exact let_subst0_t hcl σ N K db hd.2.2 dv hd.2.1
  | _, _, .conv _ _ S T u d c, hd, he => by
      obtain ⟨d', hd'⟩ := zeta_aux hcl σ N K d hd.1 he
      exact ⟨.conv Γ (instantiate0 value body) S T u d' c, hd', hd.2⟩
  | _, _, .sort _ _, _, he => by cases he
  | _, _, .bvar _ _ _ _, _, he => by cases he
  | _, _, .const _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .pi _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lam _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .app _ _ _ _ _ _ _, _, he => by cases he
  | _, _, .lit _ _ _ _, _, he => by cases he

/-- Literal zeta reduction preserves the exact requested type even when
the let introduction is followed by arbitrary bounded type conversions.
No type-conversion decomposition or scope premise is needed for this arm. -/
theorem zeta_subject_reduction {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A value body T : Expr Nat}
    (d : HasTyT E n Γ (.letE A value body) T) (hd : LOKt σ N K d) :
    ∃ d' : HasTyT E n Γ (instantiate0 value body) T, LOKt σ N K d' :=
  zeta_aux hcl σ N K d hd rfl

/-- Every domain of a literal Pi reduct is produced from a single actual
bounded typing of its let-hidden source, including outer conversions. -/
theorem zeta_telescope_of_typing {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A value body : Expr Nat} {l : Level}
    (d : HasTyT E n Γ (.letE A value body) (.sort l)) (hd : LOKt σ N K d)
    (ds : List (Expr Nat)) (terminal : Expr Nat)
    (hshape : instantiate0 value body = policyPi ds terminal) :
    BoundedPiSpine.Domains (E := E) (n := n) σ N K Γ ds ∧
      ∃ (v : Level) (dt : HasTyT E n (BoundedPiSpine.context Γ ds) terminal (.sort v)),
        LOKt σ N K dt := by
  have h := zeta_subject_reduction hcl σ N K d hd
  rw [hshape] at h
  obtain ⟨d', hd'⟩ := h
  exact BoundedPiSpine.telescope σ N K ds terminal d' hd'

end Rcic.F3.PSet.BoundedTransport