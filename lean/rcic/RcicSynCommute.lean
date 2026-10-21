import rcic.RcicSynEta

/-!
# Syntactic sortRow, build step 2b-2 — β plus the constant rules strongly commute with η

`research/rcic/semantic/S2_ERASED_E.md` §4.3. `strongCommute_rStep_etaStep`: an `RStep tbl` step
and an η step out of one term close with η* on the `R` side and at most one `R` step on the η
side. Two table conditions are used, both from `TableWF`:
* `closed`: a constant step out of a lifted term is a lifted step (`rStep_lift_inv`);
* `bare_nullary`: the body of an η redex `λ. F↑ 0` is never a constant redex.

The β/η critical pair `λ. (λM)↑ 0` closes with no step at all (`inst_bvar_lift`). Constant steps
never duplicate an argument (`CRule`), so an η step inside a pattern variable is matched by one η
step on the right-hand side.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 term facts -/

theorem ETm.inst_bvar_lift : (e : ETm) → (j : Nat) → ETm.inst j (.bvar j) (e.lift (j + 1) 1) = e
  | .bvar i, j => by etm_bvar_leaves
  | .star, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app f a, j => by
      show ETm.app (ETm.inst j (.bvar j) (f.lift (j + 1) 1)) (ETm.inst j (.bvar j) (a.lift (j + 1) 1)) = _
      rw [ETm.inst_bvar_lift f j, ETm.inst_bvar_lift a j]
  | .lam b, j => by
      have hl : ETm.lift 0 1 (.bvar j) = .bvar (j + 1) := by
        simp only [ETm.lift, if_pos (Nat.zero_le j)]
      show ETm.lam (ETm.inst (j + 1) (ETm.lift 0 1 (.bvar j)) (b.lift (j + 1 + 1) 1)) = _
      rw [hl, ETm.inst_bvar_lift b (j + 1)]
  | .pi a b, j => by
      have hl : ETm.lift 0 1 (.bvar j) = .bvar (j + 1) := by
        simp only [ETm.lift, if_pos (Nat.zero_le j)]
      show ETm.pi (ETm.inst j (.bvar j) (a.lift (j + 1) 1))
        (ETm.inst (j + 1) (ETm.lift 0 1 (.bvar j)) (b.lift (j + 1 + 1) 1)) = _
      rw [hl, ETm.inst_bvar_lift a j, ETm.inst_bvar_lift b (j + 1)]

theorem appN_eq_bvar {f : ETm} {xs : List ETm} {i : Nat} (h : ETm.appN f xs = .bvar i) :
    xs = [] ∧ f = .bvar i := by
  induction xs generalizing f with
  | nil => exact ⟨rfl, h⟩
  | cons x xs ih =>
      have h' := (ih h).2
      cases h'

theorem appN_const_ne_bvar (c : Nat) (ls : List Level) (xs : List ETm) (i : Nat) :
    ETm.appN (.const c ls) xs ≠ .bvar i := by
  intro h
  have h' := (appN_eq_bvar h).2
  cases h'

theorem ETm.lift_eq_const_inv {c k : Nat} {F : ETm} {r : Nat} {ls : List Level}
    (h : F.lift c k = .const r ls) : F = .const r ls := by
  cases F with
  | bvar i => simp only [ETm.lift] at h; split at h <;> cases h
  | const r' ls' => cases h; rfl
  | star => cases h
  | sort _ => cases h
  | app _ _ => cases h
  | lam _ => cases h
  | pi _ _ => cases h

theorem ETm.lift_eq_appN_inv {c k : Nat} {g : ETm} {xs : List ETm} :
    {F : ETm} → F.lift c k = ETm.appN g xs →
    ∃ F₀ xs₀, F = ETm.appN F₀ xs₀ ∧ F₀.lift c k = g ∧ xs = xs₀.map (ETm.lift c k) := by
  induction xs generalizing g with
  | nil => intro F h; exact ⟨F, [], rfl, h, rfl⟩
  | cons x xs ih =>
      intro F h
      obtain ⟨F₁, xs₀, rfl, h₁, rfl⟩ := ih h
      obtain ⟨G, X, rfl, rfl, rfl⟩ := ETm.lift_eq_app_inv h₁
      exact ⟨G, X :: xs₀, rfl, rfl, rfl⟩

theorem map_eq_append_inv {f : ETm → ETm} : {xs ys zs : List ETm} → xs.map f = ys ++ zs →
    ∃ ys₀ zs₀, xs = ys₀ ++ zs₀ ∧ ys₀.map f = ys ∧ zs₀.map f = zs
  | xs, [], zs, h => ⟨[], xs, rfl, rfl, h⟩
  | [], _ :: _, _, h => by cases h
  | x :: xs, y :: ys, zs, h => by
      simp only [List.map_cons, List.cons_append] at h
      injection h with h₁ h₂
      obtain ⟨ys₀, zs₀, rfl, rfl, rfl⟩ := map_eq_append_inv h₂
      exact ⟨x :: ys₀, zs₀, rfl, by rw [List.map_cons, h₁], rfl⟩

theorem map_eq_singleton_inv {f : ETm → ETm} {xs : List ETm} {y : ETm} (h : xs.map f = [y]) :
    ∃ x, xs = [x] ∧ f x = y := by
  cases xs with
  | nil => cases h
  | cons x xs =>
      cases xs with
      | nil => injection h with h₁ _; exact ⟨x, rfl, h₁⟩
      | cons _ _ => injection h with _ h₂; cases h₂

/-! ## §2 η and substitution -/

theorem etaStep_inst {M M' : ETm} (h : EtaStep M M') (j : Nat) (r : ETm) :
    EtaStep (ETm.inst j r M) (ETm.inst j r M') := by
  induction h generalizing j r with
  | eta F =>
      have e : ETm.inst (j + 1) (r.lift 0 1) (F.lift 0 1) = (ETm.inst j r F).lift 0 1 := by
        rw [ETm.lift_inst_high 1 0 j r (Nat.zero_le j) F, Nat.add_comm 1 j]
      have e0 : ETm.inst (j + 1) (r.lift 0 1) (.bvar 0) = .bvar 0 := by
        simp only [ETm.inst, if_neg (show ¬ (0 = j + 1) by omega),
          if_neg (show ¬ (j + 1 < 0) by omega)]
      show EtaStep (.lam (.app (ETm.inst (j + 1) (r.lift 0 1) (F.lift 0 1))
        (ETm.inst (j + 1) (r.lift 0 1) (.bvar 0)))) (ETm.inst j r F)
      rw [e, e0]
      exact .eta _
  | appL a _ ih => exact .appL _ (ih j r)
  | appR f _ ih => exact .appR _ (ih j r)
  | lam _ ih => exact .lam (ih (j + 1) _)
  | piL b _ ih => exact .piL _ (ih j r)
  | piR a _ ih => exact .piR _ (ih (j + 1) _)

theorem rstar_congr {α : Type} {R : α → α → Prop} {g : α → α}
    (hg : ∀ {a b : α}, R a b → R (g a) (g b)) {a b : α} (h : RStar R a b) :
    RStar R (g a) (g b) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (hg h) ih

theorem etaStar_app {f f' a a' : ETm} (hf : RStar EtaStep f f') (ha : RStar EtaStep a a') :
    RStar EtaStep (.app f a) (.app f' a') :=
  (rstar_congr (g := fun t => ETm.app t a) (fun h => .appL _ h) hf).trans'
    (rstar_congr (g := fun t => ETm.app f' t) (fun h => .appR _ h) ha)

theorem etaStar_pi {a a' b b' : ETm} (ha : RStar EtaStep a a') (hb : RStar EtaStep b b') :
    RStar EtaStep (.pi a b) (.pi a' b') :=
  (rstar_congr (g := fun t => ETm.pi t b) (fun h => .piL _ h) ha).trans'
    (rstar_congr (g := fun t => ETm.pi a' t) (fun h => .piR _ h) hb)

theorem etaStar_lam {b b' : ETm} (hb : RStar EtaStep b b') : RStar EtaStep (.lam b) (.lam b') :=
  rstar_congr (g := ETm.lam) (fun h => .lam h) hb

/-- an η step in the replacement is η* in the instance (one step per occurrence). -/
theorem etaStar_inst_repl : (M : ETm) → (j : Nat) → {r r' : ETm} → EtaStep r r' →
    RStar EtaStep (ETm.inst j r M) (ETm.inst j r' M)
  | .bvar i, j, r, r', hr => by
      simp only [ETm.inst]
      split
      · exact .single hr
      · exact .refl _
  | .star, _, _, _, _ => .refl _
  | .sort _, _, _, _, _ => .refl _
  | .const _ _, _, _, _, _ => .refl _
  | .app f a, j, _, _, hr => etaStar_app (etaStar_inst_repl f j hr) (etaStar_inst_repl a j hr)
  | .lam b, j, _, _, hr => etaStar_lam (etaStar_inst_repl b (j + 1) (etaStep_lift hr 0 1))
  | .pi a b, j, _, _, hr =>
      etaStar_pi (etaStar_inst_repl a j hr) (etaStar_inst_repl b (j + 1) (etaStep_lift hr 0 1))

/-! ## §3 `RStep` reflected by `lift` -/

/-- closed right-hand sides (`TableWF.closed`). -/
def TableClosed (tbl : List CRule) : Prop := ∀ ρ ∈ tbl, ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms)

theorem cRoot_lift_inv {tbl : List CRule} (hcl : TableClosed tbl) {c k : Nat} {F G : ETm}
    (h : CRoot tbl (F.lift c k) G) : ∃ G', G = G'.lift c k ∧ CRoot tbl F G' := by
  generalize hT : F.lift c k = T at h
  cases h with
  | @bare ρ hρ hm ls args hn =>
      obtain ⟨F₀, xs₀, rfl, hF₀, rfl⟩ := ETm.lift_eq_appN_inv hT
      have := ETm.lift_eq_const_inv hF₀
      subst this
      refine ⟨ETm.appN (ρ.rhs ls []) xs₀, ?_,
        .bare hρ hm ls xs₀ (by rw [← hn, List.length_map])⟩
      rw [ETm.lift_appN, ETm.lift_closed0 (hcl _ hρ ls [])]
  | @ctor ρ hρ d m hm ls ls' args bs hn hb =>
      obtain ⟨F₀, xs₀, rfl, hF₀, hxs⟩ := ETm.lift_eq_appN_inv hT
      have := ETm.lift_eq_const_inv hF₀
      subst this
      obtain ⟨as₀, ms₀, rfl, rfl, hms⟩ := map_eq_append_inv hxs.symm
      obtain ⟨m₀, rfl, hm₀⟩ := map_eq_singleton_inv hms
      obtain ⟨M₀, bs₀, rfl, hM₀, rfl⟩ := ETm.lift_eq_appN_inv hm₀
      have := ETm.lift_eq_const_inv hM₀
      subst this
      refine ⟨ETm.appN (ρ.rhs ls ls') (as₀ ++ bs₀), ?_,
        .ctor hρ hm ls ls' as₀ bs₀ (by rw [← hn, List.length_map])
          (by rw [← hb, List.length_map])⟩
      rw [ETm.lift_appN, ETm.lift_closed0 (hcl _ hρ ls ls'), List.map_append]

theorem rStep_lift_inv {tbl : List CRule} (hcl : TableClosed tbl) {c k : Nat} {F G : ETm}
    (h : RStep tbl (F.lift c k) G) : ∃ G', G = G'.lift c k ∧ RStep tbl F G' := by
  generalize hT : F.lift c k = T at h
  induction h generalizing F c with
  | beta M N =>
      obtain ⟨F₁, N₀, rfl, h₁, rfl⟩ := ETm.lift_eq_app_inv hT
      obtain ⟨M₀, rfl, rfl⟩ := ETm.lift_eq_lam_inv h₁
      exact ⟨ETm.inst 0 N₀ M₀, (ETm.lift_inst_low k c 0 N₀ (Nat.zero_le c) M₀).symm, .beta _ _⟩
  | cr hc =>
      subst hT
      obtain ⟨G', rfl, hG⟩ := cRoot_lift_inv hcl hc
      exact ⟨G', rfl, .cr hG⟩
  | appL a _ ih =>
      obtain ⟨F₁, F₂, rfl, h₁, rfl⟩ := ETm.lift_eq_app_inv hT
      obtain ⟨G', rfl, hG⟩ := ih h₁
      exact ⟨.app G' F₂, rfl, .appL _ hG⟩
  | appR f _ ih =>
      obtain ⟨F₁, F₂, rfl, rfl, h₂⟩ := ETm.lift_eq_app_inv hT
      obtain ⟨G', rfl, hG⟩ := ih h₂
      exact ⟨.app F₁ G', rfl, .appR _ hG⟩
  | lam _ ih =>
      obtain ⟨B, rfl, hB⟩ := ETm.lift_eq_lam_inv hT
      obtain ⟨G', rfl, hG⟩ := ih hB
      exact ⟨.lam G', rfl, .lam hG⟩
  | piL b _ ih =>
      obtain ⟨A, B, rfl, hA, rfl⟩ := ETm.lift_eq_pi_inv hT
      obtain ⟨G', rfl, hG⟩ := ih hA
      exact ⟨.pi G' B, rfl, .piL _ hG⟩
  | piR a _ ih =>
      obtain ⟨A, B, rfl, rfl, hB⟩ := ETm.lift_eq_pi_inv hT
      obtain ⟨G', rfl, hG⟩ := ih hB
      exact ⟨.pi A G', rfl, .piR _ hG⟩

theorem rStep_bvar_normal (tbl : List CRule) (i : Nat) (t : ETm) : ¬ RStep tbl (.bvar i) t := by
  intro h
  generalize hs : ETm.bvar i = s at h
  cases h with
  | cr hc =>
      obtain ⟨c, ls, xs, rfl⟩ := cRoot_lhs hc
      exact appN_const_ne_bvar c ls xs i hs.symm
  | beta => cases hs
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

/-! ## §4 η inside constant patterns -/

/-- exactly one element steps. -/
inductive OneStep (R : ETm → ETm → Prop) : List ETm → List ETm → Prop
  | head {x x' : ETm} (xs : List ETm) (h : R x x') : OneStep R (x :: xs) (x' :: xs)
  | tail (x : ETm) {xs xs' : List ETm} (h : OneStep R xs xs') : OneStep R (x :: xs) (x :: xs')

theorem OneStep.length_eq {R : ETm → ETm → Prop} {xs xs' : List ETm} (h : OneStep R xs xs') :
    xs'.length = xs.length := by
  induction h with
  | head => rfl
  | tail _ _ ih => simp only [List.length_cons, ih]

theorem OneStep.append_left {R : ETm → ETm → Prop} {xs xs' : List ETm} (h : OneStep R xs xs')
    (ys : List ETm) : OneStep R (xs ++ ys) (xs' ++ ys) := by
  induction h with
  | head xs h => exact .head _ h
  | tail x _ ih => exact .tail x ih

theorem OneStep.append_right {R : ETm → ETm → Prop} {ys ys' : List ETm} (h : OneStep R ys ys') :
    (xs : List ETm) → OneStep R (xs ++ ys) (xs ++ ys')
  | [] => h
  | x :: xs => .tail x (OneStep.append_right h xs)

theorem OneStep.split {R : ETm → ETm → Prop} : {xs ys zs : List ETm} → OneStep R (xs ++ ys) zs →
    (∃ xs', zs = xs' ++ ys ∧ OneStep R xs xs') ∨ (∃ ys', zs = xs ++ ys' ∧ OneStep R ys ys')
  | [], _, _, h => .inr ⟨_, rfl, h⟩
  | x :: xs, ys, zs, h => by
      cases h with
      | head _ h => exact .inl ⟨_, rfl, .head _ h⟩
      | tail _ h =>
          rcases OneStep.split h with ⟨xs', rfl, h'⟩ | ⟨ys', rfl, h'⟩
          · exact .inl ⟨_, rfl, .tail x h'⟩
          · exact .inr ⟨_, rfl, h'⟩

theorem OneStep.single_inv {R : ETm → ETm → Prop} {x : ETm} {zs : List ETm}
    (h : OneStep R [x] zs) : ∃ x', zs = [x'] ∧ R x x' := by
  cases h with
  | head _ h => exact ⟨_, rfl, h⟩
  | tail _ h => cases h

theorem etaStep_app_inv {f a c : ETm} (h : EtaStep (.app f a) c) :
    (∃ f', c = .app f' a ∧ EtaStep f f') ∨ (∃ a', c = .app f a' ∧ EtaStep a a') := by
  generalize hs : ETm.app f a = s at h
  cases h with
  | appL _ h => cases hs; exact .inl ⟨_, rfl, h⟩
  | appR _ h => cases hs; exact .inr ⟨_, rfl, h⟩
  | eta => cases hs
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

theorem etaStep_appN_inv {c : ETm} : {xs : List ETm} → {f : ETm} → EtaStep (ETm.appN f xs) c →
    (∃ f', c = ETm.appN f' xs ∧ EtaStep f f') ∨
      (∃ xs', c = ETm.appN f xs' ∧ OneStep EtaStep xs xs')
  | [], _, h => .inl ⟨_, rfl, h⟩
  | x :: xs, f, h => by
      rcases etaStep_appN_inv (xs := xs) (f := .app f x) h with ⟨g, rfl, hg⟩ | ⟨xs', rfl, h'⟩
      · rcases etaStep_app_inv hg with ⟨f', rfl, hf⟩ | ⟨x', rfl, hx⟩
        · exact .inl ⟨f', rfl, hf⟩
        · exact .inr ⟨x' :: xs, rfl, .head _ hx⟩
      · exact .inr ⟨x :: xs', rfl, .tail x h'⟩

theorem etaStep_const_normal (r : Nat) (ls : List Level) (t : ETm) : ¬ EtaStep (.const r ls) t := by
  intro h
  generalize hs : ETm.const r ls = s at h
  cases h <;> cases hs

theorem etaStep_appN_const_inv {r : Nat} {ls : List Level} {xs : List ETm} {c : ETm}
    (h : EtaStep (ETm.appN (.const r ls) xs) c) :
    ∃ xs', c = ETm.appN (.const r ls) xs' ∧ OneStep EtaStep xs xs' := by
  rcases etaStep_appN_inv h with ⟨_, _, hf⟩ | h'
  · exact absurd hf (etaStep_const_normal r ls _)
  · exact h'

theorem etaStep_appN_head {f f' : ETm} (h : EtaStep f f') :
    (xs : List ETm) → EtaStep (ETm.appN f xs) (ETm.appN f' xs)
  | [] => h
  | x :: xs => etaStep_appN_head (.appL x h) xs

theorem etaStep_appN_one {xs xs' : List ETm} (h : OneStep EtaStep xs xs') :
    (f : ETm) → EtaStep (ETm.appN f xs) (ETm.appN f xs') := by
  induction h with
  | head xs h => intro f; exact etaStep_appN_head (.appR f h) xs
  | tail x _ ih => intro f; exact ih (.app f x)

/-- the constant-rule case of the strong commutation: η inside a pattern variable. -/
theorem cRoot_etaStep {tbl : List CRule} {a b c : ETm} (h1 : CRoot tbl a b) (h2 : EtaStep a c) :
    ∃ d, EtaStep b d ∧ CRoot tbl c d := by
  cases h1 with
  | bare hρ hm ls args hn =>
      obtain ⟨args', rfl, h'⟩ := etaStep_appN_const_inv h2
      exact ⟨_, etaStep_appN_one h' _, .bare hρ hm ls args' (by rw [h'.length_eq, hn])⟩
  | ctor hρ hm ls ls' args bs hn hb =>
      obtain ⟨xs', rfl, h'⟩ := etaStep_appN_const_inv h2
      rcases h'.split with ⟨args', rfl, ha⟩ | ⟨ys, rfl, hy⟩
      · exact ⟨_, etaStep_appN_one (ha.append_left bs) _,
          .ctor hρ hm ls ls' args' bs (by rw [ha.length_eq, hn]) hb⟩
      · obtain ⟨maj, rfl, hmaj⟩ := hy.single_inv
        obtain ⟨bs', rfl, hbs⟩ := etaStep_appN_const_inv hmaj
        exact ⟨_, etaStep_appN_one (hbs.append_right args) _,
          .ctor hρ hm ls ls' args bs' hn (by rw [hbs.length_eq, hb])⟩

/-! ## §5 the η-redex body -/

/-- major-less rules are nullary (`TableWF.bare_nullary`). -/
def TableBareNullary (tbl : List CRule) : Prop :=
  ∀ ρ ∈ tbl, ρ.major = none → ∀ ls, ρ.nargs ls = 0

theorem cRoot_not_eta_body {tbl : List CRule} (hnull : TableBareNullary tbl) {F G : ETm}
    (h : CRoot tbl (.app (F.lift 0 1) (.bvar 0)) G) : False := by
  generalize hs : ETm.app (F.lift 0 1) (.bvar 0) = s at h
  cases h with
  | bare hρ hm ls args hn =>
      rw [hnull _ hρ hm ls] at hn
      cases args with
      | nil => cases hs
      | cons _ _ => cases hn
  | ctor hρ hm ls ls' args bs hn hb =>
      rw [ETm.appN_snoc] at hs
      injection hs with _ hs₂
      exact appN_const_ne_bvar _ _ _ _ hs₂.symm

/-- an `R` step out of an η redex's body either undoes the redex (β at `(λM)↑ 0`) or is a step
    inside `F`. -/
theorem rStep_eta_body {tbl : List CRule} (hcl : TableClosed tbl) (hnull : TableBareNullary tbl)
    {F B' : ETm} (h : RStep tbl (.app (F.lift 0 1) (.bvar 0)) B') :
    ETm.lam B' = F ∨ ∃ G', B' = .app (G'.lift 0 1) (.bvar 0) ∧ RStep tbl F G' := by
  generalize hs : ETm.app (F.lift 0 1) (.bvar 0) = s at h
  cases h with
  | beta M N =>
      injection hs with h₁ h₂
      obtain ⟨M₀, rfl, rfl⟩ := ETm.lift_eq_lam_inv h₁
      subst h₂
      exact .inl (congrArg ETm.lam (ETm.inst_bvar_lift M₀ 0))
  | cr hc =>
      subst hs
      exact (cRoot_not_eta_body hnull hc).elim
  | appL _ hf =>
      injection hs with h₁ h₂
      subst h₁; subst h₂
      obtain ⟨G', rfl, hG⟩ := rStep_lift_inv hcl hf
      exact .inr ⟨G', rfl, hG⟩
  | appR _ hx =>
      injection hs with h₁ h₂
      subst h₂
      exact (rStep_bvar_normal tbl 0 _ hx).elim
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

/-! ## §6 the strong commutation -/

theorem rrefl_congr {R : ETm → ETm → Prop} {g : ETm → ETm} (hg : ∀ {a b : ETm}, R a b → R (g a) (g b))
    {a b : ETm} (h : a = b ∨ R a b) : g a = g b ∨ R (g a) (g b) :=
  h.imp (congrArg g) hg

/-- STRONG COMMUTATION, step 2b's third obligation. -/
theorem strongCommute_rStep_etaStep {tbl : List CRule} (hcl : TableClosed tbl)
    (hnull : TableBareNullary tbl) : StrongCommute (RStep tbl) EtaStep := by
  intro a b c h1 h2
  induction h1 generalizing c with
  | beta M N =>
      generalize hs : ETm.app (.lam M) N = s at h2
      cases h2 with
      | appL _ hf =>
          cases hs
          generalize hl : ETm.lam M = l at hf
          cases hf with
          | eta F =>
              cases hl
              refine ⟨_, .refl _, .inl ?_⟩
              simp only [ETm.inst, ETm.inst_lift_id, ↓reduceIte]
          | lam hM =>
              cases hl
              exact ⟨_, .single (etaStep_inst hM 0 N), .inr (.beta _ _)⟩
          | appL => cases hl
          | appR => cases hl
          | piL => cases hl
          | piR => cases hl
      | appR _ hN =>
          cases hs
          exact ⟨_, etaStar_inst_repl M 0 hN, .inr (.beta _ _)⟩
      | eta => cases hs
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | cr hc =>
      obtain ⟨d, hbd, hcd⟩ := cRoot_etaStep hc h2
      exact ⟨d, .single hbd, .inr (.cr hcd)⟩
  | appL x h ih =>
      generalize hs : ETm.app _ x = s at h2
      cases h2 with
      | appL _ h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, etaStar_app hbd (.refl x), rrefl_congr (fun h => .appL x h) hcd⟩
      | appR _ h' =>
          cases hs
          exact ⟨_, .single (.appR _ h'), .inr (.appL _ h)⟩
      | eta => cases hs
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | appR f h ih =>
      generalize hs : ETm.app f _ = s at h2
      cases h2 with
      | appL _ h' =>
          cases hs
          exact ⟨_, .single (.appL _ h'), .inr (.appR _ h)⟩
      | appR _ h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, etaStar_app (.refl f) hbd, rrefl_congr (fun h => .appR f h) hcd⟩
      | eta => cases hs
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | @lam B B' h ih =>
      generalize hs : ETm.lam B = s at h2
      cases h2 with
      | eta F =>
          cases hs
          rcases rStep_eta_body hcl hnull h with he | ⟨G', rfl, hG⟩
          · exact ⟨_, .refl _, .inl he.symm⟩
          · exact ⟨G', .single (.eta G'), .inr hG⟩
      | lam h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, etaStar_lam hbd, rrefl_congr (fun h => .lam h) hcd⟩
      | appL => cases hs
      | appR => cases hs
      | piL => cases hs
      | piR => cases hs
  | piL b h ih =>
      generalize hs : ETm.pi _ b = s at h2
      cases h2 with
      | piL _ h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, etaStar_pi hbd (.refl b), rrefl_congr (fun h => .piL b h) hcd⟩
      | piR _ h' =>
          cases hs
          exact ⟨_, .single (.piR _ h'), .inr (.piL _ h)⟩
      | eta => cases hs
      | appL => cases hs
      | appR => cases hs
      | lam => cases hs
  | piR a h ih =>
      generalize hs : ETm.pi a _ = s at h2
      cases h2 with
      | piL _ h' =>
          cases hs
          exact ⟨_, .single (.piL _ h'), .inr (.piR _ h)⟩
      | piR _ h' =>
          cases hs
          obtain ⟨d, hbd, hcd⟩ := ih h'
          exact ⟨_, etaStar_pi (.refl a) hbd, rrefl_congr (fun h => .piR a h) hcd⟩
      | eta => cases hs
      | appL => cases hs
      | appR => cases hs
      | lam => cases hs

/-- what is left of sort separation for E: CR of `RStep tbl` alone. -/
theorem eqN_of_convE_sort' {tbl : List CRule} (hT : TableCongr tbl) (hcl : TableClosed tbl)
    (hnull : TableBareNullary tbl) (hR : Confluent (RStep tbl)) {l l' : Level}
    (h : ConvMod (EStep tbl) LvlEq (.sort l) (.sort l')) : eqN l l' :=
  eqN_of_convE_sort hT hR confluent_etaStep (strongCommute_rStep_etaStep hcl hnull) h

end Rcic.Syn

#print axioms Rcic.Syn.ETm.inst_bvar_lift
#print axioms Rcic.Syn.appN_eq_bvar
#print axioms Rcic.Syn.appN_const_ne_bvar
#print axioms Rcic.Syn.ETm.lift_eq_const_inv
#print axioms Rcic.Syn.ETm.lift_eq_appN_inv
#print axioms Rcic.Syn.map_eq_append_inv
#print axioms Rcic.Syn.map_eq_singleton_inv
#print axioms Rcic.Syn.etaStep_inst
#print axioms Rcic.Syn.rstar_congr
#print axioms Rcic.Syn.etaStar_app
#print axioms Rcic.Syn.etaStar_pi
#print axioms Rcic.Syn.etaStar_lam
#print axioms Rcic.Syn.etaStar_inst_repl
#print axioms Rcic.Syn.cRoot_lift_inv
#print axioms Rcic.Syn.rStep_lift_inv
#print axioms Rcic.Syn.rStep_bvar_normal
#print axioms Rcic.Syn.OneStep.length_eq
#print axioms Rcic.Syn.OneStep.append_left
#print axioms Rcic.Syn.OneStep.append_right
#print axioms Rcic.Syn.OneStep.split
#print axioms Rcic.Syn.OneStep.single_inv
#print axioms Rcic.Syn.etaStep_app_inv
#print axioms Rcic.Syn.etaStep_appN_inv
#print axioms Rcic.Syn.etaStep_const_normal
#print axioms Rcic.Syn.etaStep_appN_const_inv
#print axioms Rcic.Syn.etaStep_appN_head
#print axioms Rcic.Syn.etaStep_appN_one
#print axioms Rcic.Syn.cRoot_etaStep
#print axioms Rcic.Syn.cRoot_not_eta_body
#print axioms Rcic.Syn.rStep_eta_body
#print axioms Rcic.Syn.rrefl_congr
#print axioms Rcic.Syn.strongCommute_rStep_etaStep
#print axioms Rcic.Syn.eqN_of_convE_sort'
