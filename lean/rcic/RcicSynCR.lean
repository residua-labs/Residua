import rcic.RcicSynConst

/-!
# Syntactic sortRow, build step 2b-5 — CR(E) and sort separation for E

`research/rcic/semantic/S2_ERASED_E.md` §4. β strongly commutes with the constant rules
(`strongCommute_betaStep_cStep`): the constant rules never duplicate, and a constant pattern has no
β redex at a non-variable position. With CR(β) (`RcicSynBeta`) and CR(constant rules)
(`RcicSynConst`), Hindley–Rosen gives CR(`RStep tbl`) (`confluent_rStep`). With CR(η) and the
strong commutation of `RStep` with η (`RcicSynEta`, `RcicSynCommute`), it gives CR(E)
(`confluent_eStep_wf`).

So, for every `TableWF` table, `sort l ↔*_{E∪≈} sort l'` implies `eqN l l'`
(`eqN_of_convE_sort_wf`). That is build step 2. It has no hypothesis left beyond `TableWF`, and no
termination: Loop's unfold rule makes E non-terminating, and the pin
`loop_not_convE_sort_zero_one` still separates `sort 0` from `sort 1`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 constant steps under `lift` and `inst` -/

theorem cRoot_lift {tbl : List CRule} (hcl : TableClosed tbl) {a b : ETm} (h : CRoot tbl a b)
    (c k : Nat) : CRoot tbl (a.lift c k) (b.lift c k) := by
  cases h with
  | @bare ρ hρ hm ls args hn =>
      rw [ETm.lift_appN, ETm.lift_appN, ETm.lift_closed0 (hcl _ hρ ls [])]
      exact .bare hρ hm ls _ (by rw [List.length_map, hn])
  | @ctor ρ hρ d m hm ls ls' args bs hn hb =>
      rw [ETm.lift_appN, ETm.lift_appN, ETm.lift_closed0 (hcl _ hρ ls ls'), List.map_append,
        List.map_append, List.map_singleton, ETm.lift_appN]
      exact .ctor hρ hm ls ls' _ _ (by rw [List.length_map, hn]) (by rw [List.length_map, hb])

theorem cRoot_inst {tbl : List CRule} (hcl : TableClosed tbl) {a b : ETm} (h : CRoot tbl a b)
    (j : Nat) (r : ETm) : CRoot tbl (ETm.inst j r a) (ETm.inst j r b) := by
  cases h with
  | @bare ρ hρ hm ls args hn =>
      rw [ETm.inst_appN, ETm.inst_appN, ETm.inst_closed0 (hcl _ hρ ls [])]
      exact .bare hρ hm ls _ (by rw [List.length_map, hn])
  | @ctor ρ hρ d m hm ls ls' args bs hn hb =>
      rw [ETm.inst_appN, ETm.inst_appN, ETm.inst_closed0 (hcl _ hρ ls ls'), List.map_append,
        List.map_append, List.map_singleton, ETm.inst_appN]
      exact .ctor hρ hm ls ls' _ _ (by rw [List.length_map, hn]) (by rw [List.length_map, hb])

theorem cStep_lift {tbl : List CRule} (hcl : TableClosed tbl) {a b : ETm} (h : CStep tbl a b)
    (c k : Nat) : CStep tbl (a.lift c k) (b.lift c k) := by
  induction h generalizing c with
  | cr hc => exact .cr (cRoot_lift hcl hc c k)
  | appL a _ ih => exact .appL _ (ih c)
  | appR f _ ih => exact .appR _ (ih c)
  | lam _ ih => exact .lam (ih (c + 1))
  | piL b _ ih => exact .piL _ (ih c)
  | piR a _ ih => exact .piR _ (ih (c + 1))

theorem cStep_inst {tbl : List CRule} (hcl : TableClosed tbl) {M M' : ETm} (h : CStep tbl M M')
    (j : Nat) (r : ETm) : CStep tbl (ETm.inst j r M) (ETm.inst j r M') := by
  induction h generalizing j r with
  | cr hc => exact .cr (cRoot_inst hcl hc j r)
  | appL a _ ih => exact .appL _ (ih j r)
  | appR f _ ih => exact .appR _ (ih j r)
  | lam _ ih => exact .lam (ih (j + 1) _)
  | piL b _ ih => exact .piL _ (ih j r)
  | piR a _ ih => exact .piR _ (ih (j + 1) _)

theorem cStar_app {tbl : List CRule} {f f' a a' : ETm} (hf : RStar (CStep tbl) f f')
    (ha : RStar (CStep tbl) a a') : RStar (CStep tbl) (.app f a) (.app f' a') :=
  (rstar_congr (g := fun t => ETm.app t a) (fun h => .appL _ h) hf).trans'
    (rstar_congr (g := fun t => ETm.app f' t) (fun h => .appR _ h) ha)

theorem cStar_pi {tbl : List CRule} {a a' b b' : ETm} (ha : RStar (CStep tbl) a a')
    (hb : RStar (CStep tbl) b b') : RStar (CStep tbl) (.pi a b) (.pi a' b') :=
  (rstar_congr (g := fun t => ETm.pi t b) (fun h => .piL _ h) ha).trans'
    (rstar_congr (g := fun t => ETm.pi a' t) (fun h => .piR _ h) hb)

theorem cStar_lam {tbl : List CRule} {b b' : ETm} (hb : RStar (CStep tbl) b b') :
    RStar (CStep tbl) (.lam b) (.lam b') :=
  rstar_congr (g := ETm.lam) (fun h => .lam h) hb

/-- a constant step in the replacement is C* in the instance (one step per occurrence). -/
theorem cStar_inst_repl {tbl : List CRule} (hcl : TableClosed tbl) : (M : ETm) → (j : Nat) →
    {r r' : ETm} → CStep tbl r r' → RStar (CStep tbl) (ETm.inst j r M) (ETm.inst j r' M)
  | .bvar i, j, r, r', hr => by
      simp only [ETm.inst]
      split
      · exact .single hr
      · exact .refl _
  | .star, _, _, _, _ => .refl _
  | .sort _, _, _, _, _ => .refl _
  | .const _ _, _, _, _, _ => .refl _
  | .app f a, j, _, _, hr => cStar_app (cStar_inst_repl hcl f j hr) (cStar_inst_repl hcl a j hr)
  | .lam b, j, _, _, hr => cStar_lam (cStar_inst_repl hcl b (j + 1) (cStep_lift hcl hr 0 1))
  | .pi a b, j, _, _, hr =>
      cStar_pi (cStar_inst_repl hcl a j hr) (cStar_inst_repl hcl b (j + 1) (cStep_lift hcl hr 0 1))

/-! ## §2 β inside constant patterns -/

theorem appN_const_ne_lam (r : Nat) (ls : List Level) (xs : List ETm) (M : ETm) :
    ETm.appN (.const r ls) xs ≠ .lam M := by
  intro h
  have h1 := congrArg ETm.spineHead h
  rw [ETm.spineHead_appN] at h1
  simp only [ETm.spineHead] at h1
  cases h1

theorem betaStep_app_inv {f a c : ETm} (h : BetaStep (.app f a) c) :
    (∃ M, f = .lam M) ∨ (∃ f', c = .app f' a ∧ BetaStep f f') ∨
      (∃ a', c = .app f a' ∧ BetaStep a a') := by
  generalize hs : ETm.app f a = s at h
  cases h with
  | beta M N => cases hs; exact .inl ⟨M, rfl⟩
  | appL _ h => cases hs; exact .inr (.inl ⟨_, rfl, h⟩)
  | appR _ h => cases hs; exact .inr (.inr ⟨_, rfl, h⟩)
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

theorem betaStep_appN_inv {c : ETm} : {xs : List ETm} → {f : ETm} → BetaStep (ETm.appN f xs) c →
    (∃ f', c = ETm.appN f' xs ∧ BetaStep f f') ∨
      (∃ xs', c = ETm.appN f xs' ∧ OneStep BetaStep xs xs') ∨
      (∃ ys M, ETm.appN f ys = .lam M)
  | [], _, h => .inl ⟨_, rfl, h⟩
  | x :: xs, f, h => by
      rcases betaStep_appN_inv (xs := xs) (f := .app f x) h with
        ⟨g, rfl, hg⟩ | ⟨xs', rfl, h'⟩ | ⟨ys, M, hM⟩
      · rcases betaStep_app_inv hg with ⟨M, rfl⟩ | ⟨f', rfl, hf⟩ | ⟨x', rfl, hx⟩
        · exact .inr (.inr ⟨[], M, rfl⟩)
        · exact .inl ⟨f', rfl, hf⟩
        · exact .inr (.inl ⟨x' :: xs, rfl, .head _ hx⟩)
      · exact .inr (.inl ⟨x :: xs', rfl, .tail x h'⟩)
      · exact .inr (.inr ⟨x :: ys, M, hM⟩)

theorem betaStep_const_normal (r : Nat) (ls : List Level) (t : ETm) :
    ¬ BetaStep (.const r ls) t := by
  intro h
  generalize hs : ETm.const r ls = s at h
  cases h <;> cases hs

theorem betaStep_appN_const_inv {r : Nat} {ls : List Level} {xs : List ETm} {c : ETm}
    (h : BetaStep (ETm.appN (.const r ls) xs) c) :
    ∃ xs', c = ETm.appN (.const r ls) xs' ∧ OneStep BetaStep xs xs' := by
  rcases betaStep_appN_inv h with ⟨_, _, hf⟩ | h' | ⟨ys, M, hM⟩
  · exact absurd hf (betaStep_const_normal r ls _)
  · exact h'
  · exact absurd hM (appN_const_ne_lam r ls ys M)

theorem betaStep_appN_head {f f' : ETm} (h : BetaStep f f') :
    (xs : List ETm) → BetaStep (ETm.appN f xs) (ETm.appN f' xs)
  | [] => h
  | x :: xs => betaStep_appN_head (.appL x h) xs

theorem betaStep_appN_one {xs xs' : List ETm} (h : OneStep BetaStep xs xs') :
    (f : ETm) → BetaStep (ETm.appN f xs) (ETm.appN f xs') := by
  induction h with
  | head xs h => intro f; exact betaStep_appN_head (.appR f h) xs
  | tail x _ ih => intro f; exact ih (.app f x)

/-- the root case: β inside a constant pattern variable, matched by one β step on the right-hand
    side. -/
theorem cRoot_betaStep {tbl : List CRule} {a b c : ETm} (h1 : CRoot tbl a c)
    (h2 : BetaStep a b) : ∃ d, CRoot tbl b d ∧ BetaStep c d := by
  cases h1 with
  | bare hρ hm ls args hn =>
      obtain ⟨args', rfl, h'⟩ := betaStep_appN_const_inv h2
      exact ⟨_, .bare hρ hm ls args' (by rw [h'.length_eq, hn]), betaStep_appN_one h' _⟩
  | ctor hρ hm ls ls' args bs hn hb =>
      obtain ⟨xs', rfl, h'⟩ := betaStep_appN_const_inv h2
      rcases h'.split with ⟨args', rfl, ha⟩ | ⟨ys, rfl, hy⟩
      · exact ⟨_, .ctor hρ hm ls ls' args' bs (by rw [ha.length_eq, hn]) hb,
          betaStep_appN_one (ha.append_left bs) _⟩
      · obtain ⟨maj, rfl, hmaj⟩ := hy.single_inv
        obtain ⟨bs', rfl, hbs⟩ := betaStep_appN_const_inv hmaj
        exact ⟨_, .ctor hρ hm ls ls' args bs' hn (by rw [hbs.length_eq, hb]),
          betaStep_appN_one (hbs.append_right args) _⟩

theorem cStep_lam_inv {tbl : List CRule} {M X : ETm} (h : CStep tbl (.lam M) X) :
    ∃ M', X = .lam M' ∧ CStep tbl M M' := by
  generalize hs : ETm.lam M = s at h
  cases h with
  | cr hc =>
      subst hs
      obtain ⟨c, ls, xs, hx⟩ := cRoot_lhs hc
      exact absurd hx.symm (appN_const_ne_lam c ls xs M)
  | lam h => cases hs; exact ⟨_, rfl, h⟩
  | appL => cases hs
  | appR => cases hs
  | piL => cases hs
  | piR => cases hs

/-! ## §3 the strong commutation and CR -/

theorem strongCommute_betaStep_cStep {tbl : List CRule} (hcl : TableClosed tbl) :
    StrongCommute BetaStep (CStep tbl) := by
  intro a b c h1 h2
  induction h1 generalizing c with
  | beta M N =>
      generalize hs : ETm.app (.lam M) N = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          obtain ⟨d, hbd, hcd⟩ := cRoot_betaStep hc (.beta M N)
          exact ⟨d, .single (.cr hbd), .inr hcd⟩
      | appL _ hf =>
          cases hs
          obtain ⟨M', rfl, hM⟩ := cStep_lam_inv hf
          exact ⟨_, .single (cStep_inst hcl hM 0 N), .inr (.beta _ _)⟩
      | appR _ hN =>
          cases hs
          exact ⟨_, cStar_inst_repl hcl M 0 hN, .inr (.beta _ _)⟩
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | @appL f f' x h ih =>
      generalize hs : ETm.app f x = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          obtain ⟨d, hbd, hcd⟩ := cRoot_betaStep hc (.appL x h)
          exact ⟨d, .single (.cr hbd), .inr hcd⟩
      | appL _ h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, cStar_app hbd (.refl x), rrefl_congr (fun h => BetaStep.appL x h) hcd⟩
      | appR _ h' =>
          cases hs
          exact ⟨_, .single (.appR _ h'), .inr (.appL _ h)⟩
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | @appR f x x' h ih =>
      generalize hs : ETm.app f x = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          obtain ⟨d, hbd, hcd⟩ := cRoot_betaStep hc (.appR f h)
          exact ⟨d, .single (.cr hbd), .inr hcd⟩
      | appL _ h' =>
          cases hs
          exact ⟨_, .single (.appL _ h'), .inr (.appR _ h)⟩
      | appR _ h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, cStar_app (.refl f) hbd, rrefl_congr (fun h => BetaStep.appR f h) hcd⟩
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | @lam B B' h ih =>
      generalize hs : ETm.lam B = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          obtain ⟨d, hbd, hcd⟩ := cRoot_betaStep hc (.lam h)
          exact ⟨d, .single (.cr hbd), .inr hcd⟩
      | lam h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, cStar_lam hbd, rrefl_congr (fun h => BetaStep.lam h) hcd⟩
      | appL => cases hs
      | appR => cases hs
      | piL => cases hs
      | piR => cases hs
  | @piL A A' B h ih =>
      generalize hs : ETm.pi A B = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          obtain ⟨d, hbd, hcd⟩ := cRoot_betaStep hc (.piL B h)
          exact ⟨d, .single (.cr hbd), .inr hcd⟩
      | piL _ h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, cStar_pi hbd (.refl B), rrefl_congr (fun h => BetaStep.piL B h) hcd⟩
      | piR _ h' =>
          cases hs
          exact ⟨_, .single (.piR _ h'), .inr (.piL _ h)⟩
      | appL => cases hs
      | appR => cases hs
      | lam => cases hs
  | @piR A B B' h ih =>
      generalize hs : ETm.pi A B = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          obtain ⟨d, hbd, hcd⟩ := cRoot_betaStep hc (.piR A h)
          exact ⟨d, .single (.cr hbd), .inr hcd⟩
      | piL _ h' =>
          cases hs
          exact ⟨_, .single (.piL _ h'), .inr (.piR _ h)⟩
      | piR _ h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, cStar_pi (.refl A) hbd, rrefl_congr (fun h => BetaStep.piR A h) hcd⟩
      | appL => cases hs
      | appR => cases hs
      | lam => cases hs

theorem rStep_of_betaStep {tbl : List CRule} {a b : ETm} (h : BetaStep a b) : RStep tbl a b := by
  induction h with
  | beta M N => exact .beta M N
  | appL a _ ih => exact .appL a ih
  | appR f _ ih => exact .appR f ih
  | lam _ ih => exact .lam ih
  | piL b _ ih => exact .piL b ih
  | piR a _ ih => exact .piR a ih

theorem rStep_of_cStep {tbl : List CRule} {a b : ETm} (h : CStep tbl a b) : RStep tbl a b := by
  induction h with
  | cr hc => exact .cr hc
  | appL a _ ih => exact .appL a ih
  | appR f _ ih => exact .appR f ih
  | lam _ ih => exact .lam ih
  | piL b _ ih => exact .piL b ih
  | piR a _ ih => exact .piR a ih

theorem rStep_split {tbl : List CRule} {a b : ETm} (h : RStep tbl a b) :
    BetaStep a b ∨ CStep tbl a b := by
  induction h with
  | beta M N => exact .inl (.beta M N)
  | cr hc => exact .inr (.cr hc)
  | appL a _ ih => exact ih.imp (BetaStep.appL a) (CStep.appL a)
  | appR f _ ih => exact ih.imp (BetaStep.appR f) (CStep.appR f)
  | lam _ ih => exact ih.imp BetaStep.lam CStep.lam
  | piL b _ ih => exact ih.imp (BetaStep.piL b) (CStep.piL b)
  | piR a _ ih => exact ih.imp (BetaStep.piR a) (CStep.piR a)

/-- CR(`RStep tbl`), step 2b's first obligation. -/
theorem confluent_rStep {tbl : List CRule} (hW : TableWF tbl) : Confluent (RStep tbl) := by
  have hU : Confluent (fun a b => BetaStep a b ∨ CStep tbl a b) := confluent_union confluent_betaStep (confluent_cStep hW)
    (commute_of_strong (strongCommute_betaStep_cStep hW.closed))
  have up : ∀ {a b : ETm}, RStar (RStep tbl) a b →
      RStar (fun a b => BetaStep a b ∨ CStep tbl a b) a b :=
    fun h => rstar_mono rStep_split h
  have down : ∀ {a b : ETm}, RStar (fun a b => BetaStep a b ∨ CStep tbl a b) a b →
      RStar (RStep tbl) a b :=
    fun h => rstar_mono (fun h' => h'.elim rStep_of_betaStep rStep_of_cStep) h
  intro a b c hb hc
  obtain ⟨d, h1, h2⟩ := hU (up hb) (up hc)
  exact ⟨d, down h1, down h2⟩

/-- CR(E) for every `TableWF` table. -/
theorem confluent_eStep_wf {tbl : List CRule} (hW : TableWF tbl) : Confluent (EStep tbl) :=
  confluent_eStep (confluent_rStep hW) confluent_etaStep
    (strongCommute_rStep_etaStep hW.closed hW.bare_nullary)

/-- SORT SEPARATION FOR E MODULO `≈`, build step 2: for every `TableWF` table,
    `sort l ↔*_{E∪≈} sort l'` implies `eqN l l'`. -/
theorem eqN_of_convE_sort_wf {tbl : List CRule} (hW : TableWF tbl) {l l' : Level}
    (h : ConvMod (EStep tbl) LvlEq (.sort l) (.sort l')) : eqN l l' :=
  eqN_of_convMod_sort (eStep_strongSim hW.congr) (confluent_eStep_wf hW) (eStep_sort_normal tbl) h

/-! ## §4 pins -/

/-- PIN (non-vacuity under non-termination): Loop's unfold rule makes E non-terminating
    (`rec ↦ λ M m. m (rec M m)`), and `sort 0` and `sort 1` are still not convertible modulo `≈`. -/
theorem loop_not_convE_sort_zero_one :
    ¬ ConvMod (EStep [loopRule]) LvlEq (.sort .zero) (.sort (.succ .zero)) := by
  intro h
  have he := eqN_of_convE_sort_wf loopTable_wf h
  have h0 : (some 0 : Option Nat) = some 1 := he (fun _ => none)
  injection h0 with h1
  exact Nat.noConfusion h1

/-- PIN: Loop's rule fires again on its own right-hand side (the recursion is real). -/
theorem loop_step_twice (ls : List Level) :
    RStar (EStep [loopRule]) (.const 7 ls)
      (.lam (.lam (.app (.bvar 0) (.app (.app (loopRule.rhs ls []) (.bvar 1)) (.bvar 0))))) :=
  .step (loop_step ls)
    (.single (.inl (.lam (.lam (.appR _ (.appL _ (.appL _ (.cr (.bare
      (List.mem_singleton_self _) rfl ls [] rfl)))))))))

end Rcic.Syn

#print axioms Rcic.Syn.cRoot_lift
#print axioms Rcic.Syn.cRoot_inst
#print axioms Rcic.Syn.cStep_lift
#print axioms Rcic.Syn.cStep_inst
#print axioms Rcic.Syn.cStar_app
#print axioms Rcic.Syn.cStar_pi
#print axioms Rcic.Syn.cStar_lam
#print axioms Rcic.Syn.cStar_inst_repl
#print axioms Rcic.Syn.appN_const_ne_lam
#print axioms Rcic.Syn.betaStep_app_inv
#print axioms Rcic.Syn.betaStep_appN_inv
#print axioms Rcic.Syn.betaStep_const_normal
#print axioms Rcic.Syn.betaStep_appN_const_inv
#print axioms Rcic.Syn.betaStep_appN_head
#print axioms Rcic.Syn.betaStep_appN_one
#print axioms Rcic.Syn.cRoot_betaStep
#print axioms Rcic.Syn.cStep_lam_inv
#print axioms Rcic.Syn.strongCommute_betaStep_cStep
#print axioms Rcic.Syn.rStep_of_betaStep
#print axioms Rcic.Syn.rStep_of_cStep
#print axioms Rcic.Syn.rStep_split
#print axioms Rcic.Syn.confluent_rStep
#print axioms Rcic.Syn.confluent_eStep_wf
#print axioms Rcic.Syn.eqN_of_convE_sort_wf
#print axioms Rcic.Syn.loop_not_convE_sort_zero_one
#print axioms Rcic.Syn.loop_step_twice
