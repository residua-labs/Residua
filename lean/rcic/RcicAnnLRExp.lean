import rcic.RcicAnnLRWk

/-!
# M2-b (ii) — the relation is closed under typed head expansion

What the fundamental theorem's reduction arms (β, ζ, δ, ι, lit, and the
`conv`/`tyConv` arms through `tyKA_of_whTyA`) consume: a type stays valid, and
two types stay equal, when a typed head step is PREPENDED (`tyKA_expand`,
`eqKA_expand_left/right`, by chain concatenation — the per-step sorts of
`WhTyChainA` are exactly what lets the new step sit at its own sort); and a
term stays related when a typed head step is prepended on either side
(`tyKA_termExpand_left/right`): at a prop or stuck type by `ConvA.trans`, at a
sort by the same at the sort's height (lower heights as hypotheses, knotted by
strong induction, L-RING C6's device), at a pi through the Kripke clause —
the application `app (wk f) a` steps in its head to `app (wk f') a`, a typed
step (`TyHRedA.app`) whose premises are the clause's own data (`hCty` for the
codomain's typing, `hC`'s validity for the instance's typing, `hD`'s escape for
the argument's typing). No ring-form premise anywhere.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) chains concatenate; typed steps weaken along a spec -/

section Chains
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def whTyChainA_trans {Γ : LCtxA} : {A B N : ExprA} →
    WhTyChainA E I n Γ A B → WhTyChainA E I n Γ B N → WhTyChainA E I n Γ A N
  | _, _, _, .refl _ _ _ _, t => t
  | _, _, _, .cons _ A A' B u hA hs s, t => .cons _ A A' _ u hA hs (whTyChainA_trans s t)

theorem whTyA_trans {Γ : LCtxA} {A B N : ExprA} (h : WhTyA E I n Γ A B) (h' : WhTyA E I n Γ B N) :
    WhTyA E I n Γ A N :=
  h.elim fun s => h'.elim fun t => ⟨whTyChainA_trans s t⟩

end Chains

/-! ## (2) types: validity and equality are closed under head expansion -/

section TyExpand
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

theorem tyKA_expand {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyA E I n Γ A A₀) (h : TyKA E I n ρ₀ k LE LT Γ A₀ R) :
    TyKA E I n ρ₀ k LE LT Γ A R := by
  cases h with
  | prop hA hn hP => exact .prop (whTyA_trans hA₀ hA) hn hP
  | sortT hA hz hk => exact .sortT (whTyA_trans hA₀ hA) hz hk
  | sortP hA hz => exact .sortP (whTyA_trans hA₀ hA) hz
  | pi hA hnp hDty hCty RD hD RC hC hCeq =>
      exact .pi (whTyA_trans hA₀ hA) hnp hDty hCty RD hD RC hC hCeq
  | fam hA hn hnp hm hind hsh hps hu hz Rs RsF RsI hFld hFldF hFldeq hFldRec hFldFeq hxsD hFldI hFldIeq
      hFldIRec hFldIdom =>
      exact .fam (whTyA_trans hA₀ hA) hn hnp hm hind hsh hps hu hz Rs RsF RsI hFld hFldF hFldeq hFldRec
        hFldFeq hxsD hFldI hFldIeq hFldIRec hFldIdom
  | stuck hA hN => exact .stuck (whTyA_trans hA₀ hA) hN

theorem eqKA_expand_left {Γ : LCtxA} {A A₀ B : ExprA}
    (hA₀ : WhTyA E I n Γ A A₀) (h : EqKA E I n ρ₀ k LE LT Γ A₀ B) :
    EqKA E I n ρ₀ k LE LT Γ A B := by
  have htc : Nonempty (TyConvA E I n Γ A A₀) := whTyA_tyConv hA₀
  cases h with
  | sort hA hB hk hl hc =>
      exact .sort (whTyA_trans hA₀ hA) hB hk hl (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ t c⟩)
  | pi hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc =>
      exact .pi (whTyA_trans hA₀ hA) hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC
        (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ t c⟩)
  | fam hA hB hnA hnB hm hind hsh hls hps hps' Rs RsF RsI hFld hFldF hFldeq hFldRec hFldFeq hXFld hXRec hXRes hXResR hXFeq hxs hc hpar
      hFldI hFldIeq hFldIRec hXFldI hXRecI hFldIdom hXFldIdom =>
      exact .fam (whTyA_trans hA₀ hA) hB hnA hnB hm hind hsh hls hps hps' Rs RsF RsI hFld hFldF hFldeq hFldRec
        hFldFeq hXFld hXRec hXRes hXResR hXFeq hxs
        (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ t c⟩) hpar hFldI hFldIeq hFldIRec hXFldI hXRecI hFldIdom hXFldIdom
  | stuck hA hB hN hN' hc =>
      exact .stuck (whTyA_trans hA₀ hA) hB hN hN' (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ t c⟩)

theorem eqKA_expand_right {Γ : LCtxA} {A B B₀ : ExprA}
    (hB₀ : WhTyA E I n Γ B B₀) (h : EqKA E I n ρ₀ k LE LT Γ A B₀) :
    EqKA E I n ρ₀ k LE LT Γ A B := by
  have htc : Nonempty (TyConvA E I n Γ B B₀) := whTyA_tyConv hB₀
  cases h with
  | sort hA hB hk hl hc =>
      exact .sort hA (whTyA_trans hB₀ hB) hk hl
        (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ c t.symm⟩)
  | pi hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc =>
      exact .pi hA (whTyA_trans hB₀ hB) hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC
        (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ c t.symm⟩)
  | fam hA hB hnA hnB hm hind hsh hls hps hps' Rs RsF RsI hFld hFldF hFldeq hFldRec hFldFeq hXFld hXRec hXRes hXResR hXFeq hxs hc hpar
      hFldI hFldIeq hFldIRec hXFldI hXRecI hFldIdom hXFldIdom =>
      exact .fam hA (whTyA_trans hB₀ hB) hnA hnB hm hind hsh hls hps hps' Rs RsF RsI hFld hFldF hFldeq hFldRec
        hFldFeq hXFld hXRec hXRes hXResR hXFeq hxs
        (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ c t.symm⟩) hpar hFldI hFldIeq hFldIRec hXFldI hXRecI hFldIdom hXFldIdom
  | stuck hA hB hN hN' hc =>
      exact .stuck hA (whTyA_trans hB₀ hB) hN hN'
        (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ c t.symm⟩)

end TyExpand

/-! ## (3) terms: the relation is closed under head expansion on either side -/

/-- a typed head step on `a` at type `A`, together with `a`'s typing: the datum
    the expansion lemmas take (`TyHRedA` types only its reduct). -/
abbrev StepAtA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (a a' A : ExprA) : Prop :=
  Nonempty (HasTyA E I n Γ a A) ∧ Nonempty (TyHRedA E I n Γ a a' A)

/-- the lower heights expand on the left and on the right. -/
abbrev LowEqExpA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (k : Nat) (LE : LowEqTA k) : Prop :=
  ∀ (j : Nat) (hj : j < k) (Γ : LCtxA) (a a' b : ExprA) (u : Level),
    StepAtA E I n Γ a a' (.sort u) → LE j hj Γ a' b → LE j hj Γ a b

abbrev LowEqExpRA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (k : Nat) (LE : LowEqTA k) : Prop :=
  ∀ (j : Nat) (hj : j < k) (Γ : LCtxA) (a b b' : ExprA) (u : Level),
    StepAtA E I n Γ b b' (.sort u) → LE j hj Γ a b' → LE j hj Γ a b

abbrev LowTyExpA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (k : Nat) (LT : LowTyTA k) : Prop :=
  ∀ (j : Nat) (hj : j < k) (Γ : LCtxA) (a a' : ExprA) (u : Level),
    StepAtA E I n Γ a a' (.sort u) → (∃ R, LT j hj Γ a' R) → ∃ R, LT j hj Γ a R

section EqTy
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

theorem eqKA_hasTy_left {Γ : LCtxA} {A B : ExprA} (h : EqKA E I n ρ₀ k LE LT Γ A B) :
    ∃ u, Nonempty (HasTyA E I n Γ A (.sort u)) := by
  cases h with
  | sort hA _ _ _ _ => exact whTyA_hasTy_head hA
  | pi hA _ _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hA
  | fam hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hA
  | stuck hA _ _ _ _ => exact whTyA_hasTy_head hA

theorem eqKA_hasTy_right {Γ : LCtxA} {A B : ExprA} (h : EqKA E I n ρ₀ k LE LT Γ A B) :
    ∃ u, Nonempty (HasTyA E I n Γ B (.sort u)) := by
  cases h with
  | sort _ hB _ _ _ => exact whTyA_hasTy_head hB
  | pi _ hB _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hB
  | fam _ hB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hB
  | stuck _ hB _ _ _ => exact whTyA_hasTy_head hB

end EqTy

section TermExpand
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

/-- a step at `A` is a step at any type `A` converts to, with the typing. -/
theorem stepAtA_tyConv {Γ : LCtxA} {a a' A A' : ExprA} (h : StepAtA E I n Γ a a' A)
    (hc : Nonempty (TyConvA E I n Γ A A')) : StepAtA E I n Γ a a' A' :=
  ⟨hc.elim fun c => h.1.elim fun t => ⟨hasTyA_of_tyConvA t c⟩,
   hc.elim fun c => h.2.elim fun s => ⟨.conv _ _ _ _ _ s c⟩⟩

theorem stepAtA_conv {Γ : LCtxA} {a a' A : ExprA} (h : StepAtA E I n Γ a a' A) :
    Nonempty (ConvA E I n Γ a a' A) := h.2.elim fun s => ⟨tyHRedA_conv s⟩

theorem stepAtA_hasTy_right {Γ : LCtxA} {a a' A : ExprA} (h : StepAtA E I n Γ a a' A) :
    Nonempty (HasTyA E I n Γ a' A) := h.2.elim fun s => ⟨tyHRedA_hasTy_right s⟩

/-- the three-fold "typed, typed, convertible" relation at a normal form expands
    on the left … -/
theorem triple_expand_left {Γ : LCtxA} {A A' a a' b : ExprA}
    (hA : WhTyA E I n Γ A A') (hs : StepAtA E I n Γ a a' A)
    (h : Nonempty (HasTyA E I n Γ a' A') ∧ Nonempty (HasTyA E I n Γ b A') ∧
      Nonempty (ConvA E I n Γ a' b A')) :
    Nonempty (HasTyA E I n Γ a A') ∧ Nonempty (HasTyA E I n Γ b A') ∧
      Nonempty (ConvA E I n Γ a b A') := by
  have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
  exact ⟨hs'.1, h.2.1, (stepAtA_conv hs').elim fun c => h.2.2.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩⟩

/-- … and on the right. -/
theorem triple_expand_right {Γ : LCtxA} {A A' a b b' : ExprA}
    (hA : WhTyA E I n Γ A A') (hs : StepAtA E I n Γ b b' A)
    (h : Nonempty (HasTyA E I n Γ a A') ∧ Nonempty (HasTyA E I n Γ b' A') ∧
      Nonempty (ConvA E I n Γ a b' A')) :
    Nonempty (HasTyA E I n Γ a A') ∧ Nonempty (HasTyA E I n Γ b A') ∧
      Nonempty (ConvA E I n Γ a b A') := by
  have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
  exact ⟨h.1, hs'.1, (stepAtA_conv hs').elim fun c => h.2.2.elim fun c' =>
    ⟨.trans _ _ _ _ _ c' (.symm _ _ _ _ c)⟩⟩

/-- the step on the function side, lifted to a step on the application side
    under a world: `app (wk f) a →h app (wk f') a` at the codomain instance. -/
theorem stepAtA_app (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A D C f f' a : ExprA}
    {u v : Level} (ρ : WkSpecA) (hρ : WkSpecA.ok ρ Γ)
    (hA : WhTyA E I n Γ A (.pi D u C v))
    (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (hTy : ∃ w, Nonempty (HasTyA E I n (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (.sort w)))
    (ha : Nonempty (HasTyA E I n (wkCtxA ρ Γ) a (wkExprA ρ D)))
    (hs : StepAtA E I n Γ f f' A) :
    StepAtA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ f) a) (.app (wkExprA ρ f') a)
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) := by
  have hpi : Nonempty (TyConvA E I n (wkCtxA ρ Γ) (wkExprA ρ A)
      (.pi (wkExprA ρ D) u (wkExprA (WkSpecA.ub ρ) C) v)) := by
    have h := whTyA_tyConv (whTyA_wk hE hI Γ ρ hρ hA)
    rw [wkExprA_pi_ub] at h
    exact h
  have hCty' := hasTyA_wk_ne_binder hE hI ρ hρ hCty
  obtain ⟨w, hTy⟩ := hTy
  refine ⟨?_, ?_⟩
  · exact hpi.elim fun c => hCty'.elim fun hB => hTy.elim fun hT => ha.elim fun ha =>
      hs.1.elim fun hf => ⟨.app _ _ _ _ _ u v w hB hT
        (hasTyA_of_tyConvA (hasTyA_wk hE hI Γ ρ hρ hf) c) ha⟩
  · exact hpi.elim fun c => hCty'.elim fun hB => hTy.elim fun hT => ha.elim fun ha =>
      hs.2.elim fun s => ⟨.app _ _ _ _ _ _ _ u v w (tyHRedA_wk hE hI Γ ρ hρ s) c hB hT ha⟩

/-- the LEFT-expansion motive: the term relation at a type takes a typed head
    step on its first argument. -/
abbrev ExpMotTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (A : ExprA)
    (R : ExprA → ExprA → Prop) : Prop :=
  ∀ a a' b : ExprA, StepAtA E I n Γ a a' A → R a' b → R a b

/-- … and the RIGHT-expansion motive. -/
abbrev ExpMotTyRA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) (A : ExprA)
    (R : ExprA → ExprA → Prop) : Prop :=
  ∀ a b b' : ExprA, StepAtA E I n Γ b b' A → R a b' → R a b

theorem expMinor_prop {Γ : LCtxA} {A A' : ExprA}
    (hA : WhTyA E I n Γ A A') (_hn : hStepFnA E I.fn Γ A' = none) (_hP : IsPropTy E I Γ A') :
    ExpMotTyA E I n Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a A') ∧ Nonempty (HasTyA E I n Γ b A') ∧
      Nonempty (ConvA E I n Γ a b A')) ∧
    ExpMotTyRA E I n Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a A') ∧ Nonempty (HasTyA E I n Γ b A') ∧
      Nonempty (ConvA E I n Γ a b A')) :=
  ⟨fun _ _ _ hs h => triple_expand_left hA hs h, fun _ _ _ hs h => triple_expand_right hA hs h⟩

theorem expMinor_stuck {Γ : LCtxA} {A N : ExprA}
    (hA : WhTyA E I n Γ A N) (_hN : StuckA E I Γ N) :
    ExpMotTyA E I n Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N)) ∧
    ExpMotTyRA E I n Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N)) :=
  ⟨fun _ _ _ hs h => triple_expand_left hA hs h, fun _ _ _ hs h => triple_expand_right hA hs h⟩

theorem propValidA_expand {Γ : LCtxA} {a a' : ExprA} {l : Level}
    (hs : StepAtA E I n Γ a a' (.sort l)) (h : PropValidA E I n Γ a') : PropValidA E I n Γ a := by
  obtain ⟨N, hN, hT⟩ := h
  exact ⟨N, hs.1.elim fun t => hs.2.elim fun s => hN.elim fun c => ⟨.cons _ _ _ _ _ t s c⟩, hT⟩

theorem expMinor_sortP {Γ : LCtxA} {A : ExprA} {l : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (_hz : isZero l = true) :
    ExpMotTyA E I n Γ A (fun a b =>
      PropValidA E I n Γ a ∧ PropValidA E I n Γ b ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA E I n Γ a b) ∧
    ExpMotTyRA E I n Γ A (fun a b =>
      PropValidA E I n Γ a ∧ PropValidA E I n Γ b ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA E I n Γ a b) := by
  refine ⟨fun a a' b hs ⟨h1, h2, h3, h4, h5, h6⟩ => ?_, fun a b b' hs ⟨h1, h2, h3, h4, h5, h6⟩ => ?_⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    exact ⟨propValidA_expand hs' h1, h2, hs'.1, h4,
      (stepAtA_conv hs').elim fun c => h5.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩,
      propEqA_expand_left hs'.1 hs'.2 h6⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    exact ⟨h1, propValidA_expand hs' h2, h3, hs'.1,
      (stepAtA_conv hs').elim fun c => h5.elim fun c' => ⟨.trans _ _ _ _ _ c' (.symm _ _ _ _ c)⟩,
      propEqA_expand_right hs'.1 hs'.2 h6⟩

theorem expMinor_sortT (HLE : LowEqExpA E I n k LE) (HLER : LowEqExpRA E I n k LE)
    (HLT : LowTyExpA E I n k LT) {Γ : LCtxA} {A : ExprA} {l : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (_hz : isZero l = false) (hk : ht ρ₀ l < k) :
    ExpMotTyA E I n Γ A (fun a b =>
      LE (ht ρ₀ l) hk Γ a b ∧
      (∃ R, LT (ht ρ₀ l) hk Γ a R) ∧
      (∃ R, LT (ht ρ₀ l) hk Γ b R) ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l))) ∧
    ExpMotTyRA E I n Γ A (fun a b =>
      LE (ht ρ₀ l) hk Γ a b ∧
      (∃ R, LT (ht ρ₀ l) hk Γ a R) ∧
      (∃ R, LT (ht ρ₀ l) hk Γ b R) ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l))) := by
  refine ⟨fun a a' b hs ⟨h1, h2, h3, h4, h5, h6⟩ => ?_, fun a b b' hs ⟨h1, h2, h3, h4, h5, h6⟩ => ?_⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    exact ⟨HLE _ _ Γ a a' b l hs' h1, HLT _ _ Γ a a' l hs' h2, h3, hs'.1, h5,
      (stepAtA_conv hs').elim fun c => h6.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    exact ⟨HLER _ _ Γ a b b' l hs' h1, h2, HLT _ _ Γ b b' l hs' h3, h4, hs'.1,
      (stepAtA_conv hs').elim fun c => h6.elim fun c' => ⟨.trans _ _ _ _ _ c' (.symm _ _ _ _ c)⟩⟩

theorem expMinor_pi (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A D C : ExprA} {u v : Level}
    (hA : WhTyA E I n Γ A (.pi D u C v))
    (_hnp : ¬ IsPropTy E I Γ (.pi D u C v))
    (_hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
    (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      TyKA E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKA E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C)))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ),
      ExpMotTyA E I n (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ) ∧
      ExpMotTyRA E I n (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      ExpMotTyA E I n (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a) ∧
      ExpMotTyRA E I n (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (_ihCeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'), True) :
    ExpMotTyA E I n Γ A (fun f g =>
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      Nonempty (HasTyA E I n Γ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Γ g (.pi D u C v)) ∧
      Nonempty (ConvA E I n Γ f g (.pi D u C v))) ∧
    ExpMotTyRA E I n Γ A (fun f g =>
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      Nonempty (HasTyA E I n Γ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Γ g (.pi D u C v)) ∧
      Nonempty (ConvA E I n Γ f g (.pi D u C v))) := by
  refine ⟨fun f f' g hs ⟨h1, h2, h3, h4⟩ => ?_, fun f g g' hs ⟨h1, h2, h3, h4⟩ => ?_⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    refine ⟨fun ρ hρ a a' hr => ?_, hs'.1, h3,
      (stepAtA_conv hs').elim fun c => h4.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩⟩
    have hTy := tyKA_hasTy (hC ρ hρ a a' hr)
    have ha := (escapeA_hasTy (hD ρ hρ) hr).1
    exact (ihC ρ hρ a a' hr).1 _ _ _ (stepAtA_app hE hI ρ hρ.1 hA hCty hTy ha hs) (h1 ρ hρ a a' hr)
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    refine ⟨fun ρ hρ a a' hr => ?_, h2, hs'.1,
      (stepAtA_conv hs').elim fun c => h4.elim fun c' => ⟨.trans _ _ _ _ _ c' (.symm _ _ _ _ c)⟩⟩
    -- the right application's argument is `a'`: the step lands at `C[a']`, and
    -- `hCeq` carries it over to `C[a]`, the type `RC ρ a` lives at
    have heq := hCeq ρ hρ a a' hr
    have ha' := (escapeA_hasTy (hD ρ hρ) hr).2
    have hstep := stepAtA_app hE hI ρ hρ.1 hA hCty (eqKA_hasTy_right heq) ha' hs
    exact (ihC ρ hρ a a' hr).2 _ _ _
      (stepAtA_tyConv hstep ((eqKA_tyConv heq).elim fun t => ⟨t.symm⟩)) (h1 ρ hρ a a' hr)

/-- the fam clause: the fixed point at its carrier takes a typed head step on either
    side; one unfolding, the step prepended to the side's typed chain, the conversion
    composed (the step retyped to the carrier along the type's own chain). -/
theorem expMinor_fam {Γ : LCtxA} {A C : ExprA} {r : Nat} {m : CheckedMemberA}
    {Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop} {RsI : InnerRelsA}
    (hA : WhTyA E I n Γ A C) :
    ExpMotTyA E I n Γ A (fun a b => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) [] C a b) ∧
    ExpMotTyRA E I n Γ A (fun a b => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) [] C a b) := by
  refine ⟨fun a a' b hs h => ?_, fun a b b' hs h => ?_⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    obtain ⟨hc, hd⟩ := LfpWA.unfold famPhiWA_mono h
    refine LfpWA.fold famPhiWA_mono
      ⟨(stepAtA_conv hs').elim fun c => hc.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩, ?_⟩
    have hpre : ∀ {N : ExprA}, TyHRedStarA E I n Γ a' N C → TyHRedStarA E I n Γ a N C :=
      fun hN => hs'.1.elim fun t => hs'.2.elim fun st => tyHRedStarA_cons t st hN
    rcases hd with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h11, ha, hb, hna, hnb, h12⟩ | ⟨N, N', ha, hb, hN, hN'⟩
    · exact Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h11, hpre ha, hb, hna, hnb, h12⟩
    · exact Or.inr ⟨N, N', hpre ha, hb, hN, hN'⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    obtain ⟨hc, hd⟩ := LfpWA.unfold famPhiWA_mono h
    refine LfpWA.fold famPhiWA_mono
      ⟨(stepAtA_conv hs').elim fun c => hc.elim fun c' => ⟨.trans _ _ _ _ _ c' (.symm _ _ _ _ c)⟩, ?_⟩
    have hpre : ∀ {N : ExprA}, TyHRedStarA E I n Γ b' N C → TyHRedStarA E I n Γ b N C :=
      fun hN => hs'.1.elim fun t => hs'.2.elim fun st => tyHRedStarA_cons t st hN
    rcases hd with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h11, ha, hb, hna, hnb, h12⟩ | ⟨N, N', ha, hb, hN, hN'⟩
    · exact Or.inl ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h11, ha, hpre hb, hna, hnb, h12⟩
    · exact Or.inr ⟨N, N', ha, hpre hb, hN, hN'⟩

/-- **the term relation is closed under typed head expansion**, on either side
    (one height, lower heights as hypotheses). -/
theorem tyKA_termExpand (hE : EnvClosedA E) (hI : IotaLiftA I)
    (HLE : LowEqExpA E I n k LE) (HLER : LowEqExpRA E I n k LE) (HLT : LowTyExpA E I n k LT) :
    {Γ : LCtxA} → {A : ExprA} → {R : ExprA → ExprA → Prop} → TyKA E I n ρ₀ k LE LT Γ A R →
      ExpMotTyA E I n Γ A R ∧ ExpMotTyRA E I n Γ A R :=
  fun {_Γ _A _R} h =>
  TyKA.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ A R _ => ExpMotTyA E I n Γ A R ∧ ExpMotTyRA E I n Γ A R)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro)
    (fun hA hn hP => expMinor_prop hA hn hP)
    (fun hA hz hk => expMinor_sortT HLE HLER HLT hA hz hk)
    (fun hA hz => expMinor_sortP hA hz)
    (fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC _ihCeq =>
      expMinor_pi hE hI hA hnp hDty hCty RD hD RC hC hCeq ihD ihC (fun _ _ _ _ _ => True.intro))
    (fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => expMinor_fam hA)
    (fun hA hN => expMinor_stuck hA hN)
    h

end TermExpand

/-! ## (4) every height: the knot -/

theorem LR_exp_allA {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) : ∀ k : Nat,
    (∀ {Γ : LCtxA} {a a' b : ExprA} {u : Level}, StepAtA E I n Γ a a' (.sort u) →
      LREqA E I n ρ₀ k Γ a' b → LREqA E I n ρ₀ k Γ a b) ∧
    (∀ {Γ : LCtxA} {a b b' : ExprA} {u : Level}, StepAtA E I n Γ b b' (.sort u) →
      LREqA E I n ρ₀ k Γ a b' → LREqA E I n ρ₀ k Γ a b) ∧
    (∀ {Γ : LCtxA} {a a' : ExprA} {u : Level}, StepAtA E I n Γ a a' (.sort u) →
      (∃ R, LRTyA E I n ρ₀ k Γ a' R) → ∃ R, LRTyA E I n ρ₀ k Γ a R) ∧
    (∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}, LRTyA E I n ρ₀ k Γ A R →
      ExpMotTyA E I n Γ A R ∧ ExpMotTyRA E I n Γ A R) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have HLE : LowEqExpA E I n k (fun j _ => LREqA E I n ρ₀ j) :=
      fun j hj Γ a a' b u hs h => (ih j hj).1 hs h
    have HLER : LowEqExpRA E I n k (fun j _ => LREqA E I n ρ₀ j) :=
      fun j hj Γ a b b' u hs h => (ih j hj).2.1 hs h
    have HLT : LowTyExpA E I n k (fun j _ => LRTyA E I n ρ₀ j) :=
      fun j hj Γ a a' u hs h => (ih j hj).2.2.1 hs h
    refine ⟨fun hs h => ?_, fun hs h => ?_, fun hs h => ?_, fun h => ?_⟩
    · rw [LREqA_eq] at h ⊢
      exact eqKA_expand_left (hs.1.elim fun t => hs.2.elim fun s => ⟨.cons _ _ _ _ _ t s (.refl _ _ _ (tyHRedA_hasTy_right s))⟩) h
    · rw [LREqA_eq] at h ⊢
      exact eqKA_expand_right (hs.1.elim fun t => hs.2.elim fun s => ⟨.cons _ _ _ _ _ t s (.refl _ _ _ (tyHRedA_hasTy_right s))⟩) h
    · obtain ⟨R, hR⟩ := h
      rw [LRTyA_eq] at hR ⊢
      exact ⟨R, tyKA_expand (hs.1.elim fun t => hs.2.elim fun s => ⟨.cons _ _ _ _ _ t s (.refl _ _ _ (tyHRedA_hasTy_right s))⟩) hR⟩
    · rw [LRTyA_eq] at h
      exact tyKA_termExpand hE hI HLE HLER HLT h

/-- the knotted forms. -/
theorem LRRelA_expand_left {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A a a' b : ExprA}
    (hs : StepAtA E I n Γ a a' A) (h : LRRelA E I n ρ₀ k Γ A a' b) : LRRelA E I n ρ₀ k Γ A a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, ((LR_exp_allA hE hI k).2.2.2 hR).1 a a' b hs hab⟩

theorem LRRelA_expand_right {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A a b b' : ExprA}
    (hs : StepAtA E I n Γ b b' A) (h : LRRelA E I n ρ₀ k Γ A a b') : LRRelA E I n ρ₀ k Γ A a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, ((LR_exp_allA hE hI k).2.2.2 hR).2 a b b' hs hab⟩

theorem LRTyA_expand {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyA E I n Γ A A₀) (h : LRTyA E I n ρ₀ k Γ A₀ R) : LRTyA E I n ρ₀ k Γ A R := by
  rw [LRTyA_eq] at h ⊢
  exact tyKA_expand hA₀ h

#print axioms whTyA_trans
#print axioms tyKA_expand
#print axioms eqKA_expand_left
#print axioms tyKA_termExpand
#print axioms LR_exp_allA
#print axioms LRRelA_expand_left
#print axioms LRRelA_expand_right

end Rcic.Declarative.Ann
