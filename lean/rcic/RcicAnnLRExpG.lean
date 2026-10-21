import rcic.RcicAnnLRExp
import rcic.RcicAnnLRWkG
/-!
# M2-b (ii) — the relation is closed under typed head expansion

What the fundamental theorem's reduction arms (β, ζ, δ, ι, lit, and the
`conv`/`tyConv` arms through `tyKA_of_whTyAg`) consume: a type stays valid, and
two types stay equal, when a typed head step is PREPENDED (`tyKA_expandg`,
`eqKA_expand_leftg/right`, by chain concatenation — the per-step sorts of
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

end Chains

/-! ## (2) types: validity and equality are closed under head expansion -/

section TyExpand
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

theorem tyKA_expandg {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyA E I n Γ A A₀) (h : TyKAg E I n ρ₀ k LE LT Γ A₀ R) :
    TyKAg E I n ρ₀ k LE LT Γ A R := by
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
  | stuck hA hN hnp => exact .stuck (whTyA_trans hA₀ hA) hN hnp

theorem eqKA_expand_leftg {Γ : LCtxA} {A A₀ B : ExprA}
    (hA₀ : WhTyA E I n Γ A A₀) (h : EqKAg E I n ρ₀ k LE LT Γ A₀ B) :
    EqKAg E I n ρ₀ k LE LT Γ A B := by
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
  | stuck hA hB hN hN' hc hPP =>
      exact .stuck (whTyA_trans hA₀ hA) hB hN hN' (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ t c⟩) hPP

theorem eqKA_expand_rightg {Γ : LCtxA} {A B B₀ : ExprA}
    (hB₀ : WhTyA E I n Γ B B₀) (h : EqKAg E I n ρ₀ k LE LT Γ A B₀) :
    EqKAg E I n ρ₀ k LE LT Γ A B := by
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
  | stuck hA hB hN hN' hc hPP =>
      exact .stuck hA (whTyA_trans hB₀ hB) hN hN'
        (htc.elim fun t => hc.elim fun c => ⟨.trans _ _ _ _ c t.symm⟩) hPP

end TyExpand

/-! ## (3) terms: the relation is closed under head expansion on either side -/

section EqTy
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

theorem eqKA_hasTy_leftg {Γ : LCtxA} {A B : ExprA} (h : EqKAg E I n ρ₀ k LE LT Γ A B) :
    ∃ u, Nonempty (HasTyA E I n Γ A (.sort u)) := by
  cases h with
  | sort hA _ _ _ _ => exact whTyA_hasTy_head hA
  | pi hA _ _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hA
  | fam hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hA
  | stuck hA _ _ _ _ => exact whTyA_hasTy_head hA

theorem eqKA_hasTy_rightg {Γ : LCtxA} {A B : ExprA} (h : EqKAg E I n ρ₀ k LE LT Γ A B) :
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

theorem expMinor_pig (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A D C : ExprA} {u v : Level}
    (hA : WhTyA E I n Γ A (.pi D u C v))
    (_hnp : ¬ IsPropTy E I Γ (.pi D u C v))
    (_hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
    (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
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
    have hTy := tyKA_hasTyg (hC ρ hρ a a' hr)
    have ha := (escapeA_hasTyg (hD ρ hρ) hr).1
    exact (ihC ρ hρ a a' hr).1 _ _ _ (stepAtA_app hE hI ρ hρ.1 hA hCty hTy ha hs) (h1 ρ hρ a a' hr)
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    refine ⟨fun ρ hρ a a' hr => ?_, h2, hs'.1,
      (stepAtA_conv hs').elim fun c => h4.elim fun c' => ⟨.trans _ _ _ _ _ c' (.symm _ _ _ _ c)⟩⟩
    -- the right application's argument is `a'`: the step lands at `C[a']`, and
    -- `hCeq` carries it over to `C[a]`, the type `RC ρ a` lives at
    have heq := hCeq ρ hρ a a' hr
    have ha' := (escapeA_hasTyg (hD ρ hρ) hr).2
    have hstep := stepAtA_app hE hI ρ hρ.1 hA hCty (eqKA_hasTy_rightg heq) ha' hs
    exact (ihC ρ hρ a a' hr).2 _ _ _
      (stepAtA_tyConv hstep ((eqKA_tyConvg heq).elim fun t => ⟨t.symm⟩)) (h1 ρ hρ a a' hr)

/-- DT-025/A-6 S1-g.2: a key-proposition expands — a typed step prepends to its chain. -/
theorem propValidKA_expand {Γ : LCtxA} {a a' : ExprA} {l : Level}
    (hs : StepAtA E I n Γ a a' (.sort l)) (h : PropValidKA E I n Γ a') : PropValidKA E I n Γ a := by
  obtain ⟨N, hN, hn, hP⟩ := h
  exact ⟨N, hs.1.elim fun t => hs.2.elim fun s => hN.elim fun c => ⟨.cons _ _ _ _ _ t s c⟩, hn, hP⟩

/-- DT-025/A-6 S1-g.2: the guarded `sortP` relation (key-propositions) expands. -/
theorem expMinor_sortPg {Γ : LCtxA} {A : ExprA} {l : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (_hz : isZero l = true) :
    ExpMotTyA E I n Γ A (fun a b =>
      PropValidKA E I n Γ a ∧ PropValidKA E I n Γ b ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA E I n Γ a b) ∧
    ExpMotTyRA E I n Γ A (fun a b =>
      PropValidKA E I n Γ a ∧ PropValidKA E I n Γ b ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA E I n Γ a b) := by
  refine ⟨fun a a' b hs ⟨h1, h2, h3, h4, h5, h6⟩ => ?_, fun a b b' hs ⟨h1, h2, h3, h4, h5, h6⟩ => ?_⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    exact ⟨propValidKA_expand hs' h1, h2, hs'.1, h4,
      (stepAtA_conv hs').elim fun c => h5.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩,
      propEqA_expand_left hs'.1 hs'.2 h6⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    exact ⟨h1, propValidKA_expand hs' h2, h3, hs'.1,
      (stepAtA_conv hs').elim fun c => h5.elim fun c' => ⟨.trans _ _ _ _ _ c' (.symm _ _ _ _ c)⟩,
      propEqA_expand_right hs'.1 hs'.2 h6⟩

/-- DT-025/A-6 S1-g.2: the guarded stuck clause's relation expands too — a typed step on the
    expanded side (retyped to `N` along the type's own whnf conversion) prepends to that
    side's chain. -/
theorem expMinor_stuckg {Γ : LCtxA} {A N : ExprA}
    (hA : WhTyA E I n Γ A N) (_hN : StuckA E I Γ N) (_hnp : ¬ IsPropTy E I Γ N) :
    ExpMotTyA E I n Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N) ∧
      ∃ Na, TyHRedStarA E I n Γ a Na N ∧ hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ b Nb N ∧ hStepFnA E I.fn Γ Nb = none) ∧
    ExpMotTyRA E I n Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N) ∧
      ∃ Na, TyHRedStarA E I n Γ a Na N ∧ hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ b Nb N ∧ hStepFnA E I.fn Γ Nb = none) := by
  refine ⟨fun a a' b hs ⟨ha, hb, hc, Na, cha, hna, Nb, chb, hnb⟩ => ?_,
    fun a b b' hs ⟨ha, hb, hc, Na, cha, hna, Nb, chb, hnb⟩ => ?_⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    obtain ⟨ha', hb', hc'⟩ := triple_expand_left hA hs ⟨ha, hb, hc⟩
    exact ⟨ha', hb', hc',
      Na, hs'.1.elim fun t => hs'.2.elim fun s => tyHRedStarA_cons t s cha, hna, Nb, chb, hnb⟩
  · have hs' := stepAtA_tyConv hs (whTyA_tyConv hA)
    obtain ⟨ha', hb', hc'⟩ := triple_expand_right hA hs ⟨ha, hb, hc⟩
    exact ⟨ha', hb', hc',
      Na, cha, hna, Nb, hs'.1.elim fun t => hs'.2.elim fun s => tyHRedStarA_cons t s chb, hnb⟩

/-- **the term relation is closed under typed head expansion**, on either side
    (one height, lower heights as hypotheses). -/
theorem tyKA_termExpandg (hE : EnvClosedA E) (hI : IotaLiftA I)
    (HLE : LowEqExpA E I n k LE) (HLER : LowEqExpRA E I n k LE) (HLT : LowTyExpA E I n k LT) :
    {Γ : LCtxA} → {A : ExprA} → {R : ExprA → ExprA → Prop} → TyKAg E I n ρ₀ k LE LT Γ A R →
      ExpMotTyA E I n Γ A R ∧ ExpMotTyRA E I n Γ A R :=
  fun {_Γ _A _R} h =>
  TyKAg.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ A R _ => ExpMotTyA E I n Γ A R ∧ ExpMotTyRA E I n Γ A R)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ => True.intro)
    (fun hA hn hP => expMinor_prop hA hn hP)
    (fun hA hz hk => expMinor_sortT HLE HLER HLT hA hz hk)
    (fun hA hz => expMinor_sortPg hA hz)
    (fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC _ihCeq =>
      expMinor_pig hE hI hA hnp hDty hCty RD hD RC hC hCeq ihD ihC (fun _ _ _ _ _ => True.intro))
    (fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => expMinor_fam hA)
    (fun hA hN hnp => expMinor_stuckg hA hN hnp)
    h

end TermExpand

/-! ## (4) every height: the knot -/

theorem LR_exp_allAg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) : ∀ k : Nat,
    (∀ {Γ : LCtxA} {a a' b : ExprA} {u : Level}, StepAtA E I n Γ a a' (.sort u) →
      LREqAg E I n ρ₀ k Γ a' b → LREqAg E I n ρ₀ k Γ a b) ∧
    (∀ {Γ : LCtxA} {a b b' : ExprA} {u : Level}, StepAtA E I n Γ b b' (.sort u) →
      LREqAg E I n ρ₀ k Γ a b' → LREqAg E I n ρ₀ k Γ a b) ∧
    (∀ {Γ : LCtxA} {a a' : ExprA} {u : Level}, StepAtA E I n Γ a a' (.sort u) →
      (∃ R, LRTyAg E I n ρ₀ k Γ a' R) → ∃ R, LRTyAg E I n ρ₀ k Γ a R) ∧
    (∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}, LRTyAg E I n ρ₀ k Γ A R →
      ExpMotTyA E I n Γ A R ∧ ExpMotTyRA E I n Γ A R) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have HLE : LowEqExpA E I n k (fun j _ => LREqAg E I n ρ₀ j) :=
      fun j hj Γ a a' b u hs h => (ih j hj).1 hs h
    have HLER : LowEqExpRA E I n k (fun j _ => LREqAg E I n ρ₀ j) :=
      fun j hj Γ a b b' u hs h => (ih j hj).2.1 hs h
    have HLT : LowTyExpA E I n k (fun j _ => LRTyAg E I n ρ₀ j) :=
      fun j hj Γ a a' u hs h => (ih j hj).2.2.1 hs h
    refine ⟨fun hs h => ?_, fun hs h => ?_, fun hs h => ?_, fun h => ?_⟩
    · rw [LREqA_eqg] at h ⊢
      exact eqKA_expand_leftg (hs.1.elim fun t => hs.2.elim fun s => ⟨.cons _ _ _ _ _ t s (.refl _ _ _ (tyHRedA_hasTy_right s))⟩) h
    · rw [LREqA_eqg] at h ⊢
      exact eqKA_expand_rightg (hs.1.elim fun t => hs.2.elim fun s => ⟨.cons _ _ _ _ _ t s (.refl _ _ _ (tyHRedA_hasTy_right s))⟩) h
    · obtain ⟨R, hR⟩ := h
      rw [LRTyA_eqg] at hR ⊢
      exact ⟨R, tyKA_expandg (hs.1.elim fun t => hs.2.elim fun s => ⟨.cons _ _ _ _ _ t s (.refl _ _ _ (tyHRedA_hasTy_right s))⟩) hR⟩
    · rw [LRTyA_eqg] at h
      exact tyKA_termExpandg hE hI HLE HLER HLT h

/-- the knotted forms. -/
theorem LRRelA_expand_leftg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A a a' b : ExprA}
    (hs : StepAtA E I n Γ a a' A) (h : LRRelAg E I n ρ₀ k Γ A a' b) : LRRelAg E I n ρ₀ k Γ A a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, ((LR_exp_allAg hE hI k).2.2.2 hR).1 a a' b hs hab⟩

theorem LRRelA_expand_rightg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A a b b' : ExprA}
    (hs : StepAtA E I n Γ b b' A) (h : LRRelAg E I n ρ₀ k Γ A a b') : LRRelAg E I n ρ₀ k Γ A a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, ((LR_exp_allAg hE hI k).2.2.2 hR).2 a b b' hs hab⟩

theorem LRTyA_expandg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyA E I n Γ A A₀) (h : LRTyAg E I n ρ₀ k Γ A₀ R) : LRTyAg E I n ρ₀ k Γ A R := by
  rw [LRTyA_eqg] at h ⊢
  exact tyKA_expandg hA₀ h

#print axioms tyKA_expandg
#print axioms eqKA_expand_leftg
#print axioms tyKA_termExpandg
#print axioms LR_exp_allAg
#print axioms LRRelA_expand_leftg
#print axioms LRRelA_expand_rightg

end Rcic.Declarative.Ann
