import rcic.RcicSynBeta

/-!
# Syntactic sortRow, build step 2b-4 — CR(constant rules)

`research/rcic/semantic/S2_ERASED_E.md` §3, §4.1. The constant rules of a `TableWF` table have the
diamond property up to equality (`cStep_diamond`), so they are confluent (`confluent_cStep`).

* Constant steps never duplicate (`CRule`): a step inside a pattern variable is matched by one
  step on the right-hand side (`cRoot_cStep`).
* Patterns do not overlap. A step out of a constant-headed spine is a step inside one argument,
  or a root step on a prefix (`cStep_appN_const_inv`). On a redex the only root prefix is the
  whole redex, with a unique result (`cRoot_prefix_det`, from `bare_unique` and `ctor_disjoint`).
  A major's constructor head has no rule (`rigid`).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 spines are injective at a constant head -/

namespace ETm

/-- the head of an application spine. -/
def spineHead : ETm → ETm
  | .app f _ => spineHead f
  | t => t

/-- the arguments of an application spine. -/
def spineArgs : ETm → List ETm
  | .app f a => spineArgs f ++ [a]
  | _ => []

theorem spineHead_appN (f : ETm) (xs : List ETm) : spineHead (appN f xs) = spineHead f := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

theorem spineArgs_appN (f : ETm) (xs : List ETm) : spineArgs (appN f xs) = spineArgs f ++ xs := by
  induction xs generalizing f with
  | nil => simp only [appN, List.append_nil]
  | cons x xs ih =>
      rw [appN, ih (.app f x)]
      simp only [spineArgs, List.append_assoc, List.singleton_append]

theorem appN_const_inj {r r' : Nat} {ls ls' : List Level} {xs ys : List ETm}
    (h : appN (.const r ls) xs = appN (.const r' ls') ys) : r = r' ∧ ls = ls' ∧ xs = ys := by
  have h1 := congrArg spineHead h
  have h2 := congrArg spineArgs h
  rw [spineHead_appN, spineHead_appN] at h1
  rw [spineArgs_appN, spineArgs_appN] at h2
  simp only [spineHead, spineArgs, List.nil_append] at h1 h2
  cases h1
  exact ⟨rfl, rfl, h2⟩

end ETm

/-! ## §2 the constant step -/

/-- one constant-rule step, closed under congruence. -/
inductive CStep (tbl : List CRule) : ETm → ETm → Prop
  | cr {a b : ETm} (h : CRoot tbl a b) : CStep tbl a b
  | appL {f f' : ETm} (a : ETm) (h : CStep tbl f f') : CStep tbl (.app f a) (.app f' a)
  | appR (f : ETm) {a a' : ETm} (h : CStep tbl a a') : CStep tbl (.app f a) (.app f a')
  | lam {b b' : ETm} (h : CStep tbl b b') : CStep tbl (.lam b) (.lam b')
  | piL {a a' : ETm} (b : ETm) (h : CStep tbl a a') : CStep tbl (.pi a b) (.pi a' b)
  | piR (a : ETm) {b b' : ETm} (h : CStep tbl b b') : CStep tbl (.pi a b) (.pi a b')

theorem cStep_appN_head {tbl : List CRule} {f f' : ETm} (h : CStep tbl f f') :
    (xs : List ETm) → CStep tbl (ETm.appN f xs) (ETm.appN f' xs)
  | [] => h
  | x :: xs => cStep_appN_head (.appL x h) xs

theorem cStep_appN_one {tbl : List CRule} {xs xs' : List ETm} (h : OneStep (CStep tbl) xs xs') :
    (f : ETm) → CStep tbl (ETm.appN f xs) (ETm.appN f xs') := by
  induction h with
  | head xs h => intro f; exact cStep_appN_head (.appR f h) xs
  | tail x _ ih => intro f; exact ih (.app f x)

theorem cStep_app_inv {tbl : List CRule} {f a c : ETm} (h : CStep tbl (.app f a) c) :
    CRoot tbl (.app f a) c ∨ (∃ f', c = .app f' a ∧ CStep tbl f f') ∨
      (∃ a', c = .app f a' ∧ CStep tbl a a') := by
  generalize hs : ETm.app f a = s at h
  cases h with
  | cr hc => subst hs; exact .inl hc
  | appL _ h => cases hs; exact .inr (.inl ⟨_, rfl, h⟩)
  | appR _ h => cases hs; exact .inr (.inr ⟨_, rfl, h⟩)
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

/-- a step out of a spine: in the head, in one argument, or a root step on a non-empty prefix. -/
theorem cStep_appN_inv {tbl : List CRule} {c : ETm} : {xs : List ETm} → {f : ETm} →
    CStep tbl (ETm.appN f xs) c →
    (∃ f', c = ETm.appN f' xs ∧ CStep tbl f f') ∨
      (∃ xs', c = ETm.appN f xs' ∧ OneStep (CStep tbl) xs xs') ∨
      (∃ ys zs b, xs = ys ++ zs ∧ CRoot tbl (ETm.appN f ys) b ∧ c = ETm.appN b zs)
  | [], _, h => .inl ⟨_, rfl, h⟩
  | x :: xs, f, h => by
      rcases cStep_appN_inv (xs := xs) (f := .app f x) h with
        ⟨g, rfl, hg⟩ | ⟨xs', rfl, h'⟩ | ⟨ys, zs, b, rfl, hb, rfl⟩
      · rcases cStep_app_inv hg with hc | ⟨f', rfl, hf⟩ | ⟨x', rfl, hx⟩
        · exact .inr (.inr ⟨[x], xs, g, rfl, hc, rfl⟩)
        · exact .inl ⟨f', rfl, hf⟩
        · exact .inr (.inl ⟨x' :: xs, rfl, .head _ hx⟩)
      · exact .inr (.inl ⟨x :: xs', rfl, .tail x h'⟩)
      · exact .inr (.inr ⟨x :: ys, zs, b, rfl, hb, rfl⟩)

theorem cStep_const_inv {tbl : List CRule} {r : Nat} {ls : List Level} {c : ETm}
    (h : CStep tbl (.const r ls) c) : CRoot tbl (.const r ls) c := by
  generalize hs : ETm.const r ls = s at h
  cases h with
  | cr hc => subst hs; exact hc
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

/-- a step out of a constant-headed spine: in one argument, or a root step on a prefix. -/
theorem cStep_appN_const_inv {tbl : List CRule} {r : Nat} {ls : List Level} {xs : List ETm}
    {c : ETm} (h : CStep tbl (ETm.appN (.const r ls) xs) c) :
    (∃ xs', c = ETm.appN (.const r ls) xs' ∧ OneStep (CStep tbl) xs xs') ∨
      (∃ ys zs b, xs = ys ++ zs ∧ CRoot tbl (ETm.appN (.const r ls) ys) b ∧
        c = ETm.appN b zs) := by
  rcases cStep_appN_inv h with ⟨f', rfl, hf⟩ | h' | h'
  · exact .inr ⟨[], xs, f', rfl, cStep_const_inv hf, rfl⟩
  · exact .inl h'
  · exact .inr h'

/-! ## §3 root redexes -/

/-- what a root redex at a constant-headed spine is. -/
theorem cRoot_inv {tbl : List CRule} {r : Nat} {ls : List Level} {ys : List ETm} {b : ETm}
    (h : CRoot tbl (ETm.appN (.const r ls) ys) b) :
    ∃ ρ ∈ tbl, ρ.head = r ∧
      ((ρ.major = none ∧ ys.length = ρ.nargs ls ∧ b = ETm.appN (ρ.rhs ls []) ys) ∨
       (∃ d m ls' args bs, ρ.major = some (d, m) ∧
          ys = args ++ [ETm.appN (.const d ls') bs] ∧ args.length = ρ.nargs ls ∧
          bs.length = m ls' ∧ b = ETm.appN (ρ.rhs ls ls') (args ++ bs))) := by
  generalize hT : ETm.appN (.const r ls) ys = T at h
  cases h with
  | @bare ρ hρ hm ls₀ args hn =>
      obtain ⟨rfl, rfl, rfl⟩ := ETm.appN_const_inj hT.symm
      exact ⟨ρ, hρ, rfl, .inl ⟨hm, hn, rfl⟩⟩
  | @ctor ρ hρ d m hm ls₀ ls' args bs hn hb =>
      obtain ⟨rfl, rfl, rfl⟩ := ETm.appN_const_inj hT.symm
      exact ⟨ρ, hρ, rfl, .inr ⟨d, m, ls', args, bs, hm, rfl, hn, hb, rfl⟩⟩

/-- a major's constructor head is never the head of a root redex (`rigid`). -/
theorem cRoot_not_major_head {tbl : List CRule} (hW : TableWF tbl) {ρ : CRule} (hρ : ρ ∈ tbl)
    {d : Nat} {m : List Level → Nat} (hm : ρ.major = some (d, m)) {ls' : List Level}
    {ys : List ETm} {b : ETm} (h : CRoot tbl (ETm.appN (.const d ls') ys) b) : False := by
  obtain ⟨σ, hσ, hhead, _⟩ := cRoot_inv h
  exact hW.rigid ρ hρ hm σ hσ hhead

/-- on a redex, the only root prefix is the whole redex, with the same result. -/
theorem cRoot_prefix_det {tbl : List CRule} (hW : TableWF tbl) {r : Nat} {ls : List Level}
    {xs ys zs : List ETm} {b b' : ETm} (h1 : CRoot tbl (ETm.appN (.const r ls) xs) b)
    (h2 : CRoot tbl (ETm.appN (.const r ls) ys) b') (hxs : xs = ys ++ zs) : zs = [] ∧ b' = b := by
  obtain ⟨ρ, hρ, hhρ, hρc⟩ := cRoot_inv h1
  obtain ⟨σ, hσ, hhσ, hσc⟩ := cRoot_inv h2
  have hhead : σ.head = ρ.head := hhσ.trans hhρ.symm
  rcases hρc with ⟨hmρ, hnρ, rfl⟩ | ⟨d, m, ls', args, bs, hmρ, rfl, hnρ, hbρ, rfl⟩
  · have hσρ := hW.bare_unique ρ hρ hmρ σ hσ hhead
    subst hσρ
    rcases hσc with ⟨_, hnσ, rfl⟩ | ⟨_, _, _, _, _, hmσ, _⟩
    · have hl : zs.length = 0 := by
        have := congrArg List.length hxs
        rw [List.length_append, hnρ, hnσ] at this
        omega
      have hz := List.eq_nil_of_length_eq_zero hl
      subst hz
      rw [List.append_nil] at hxs
      subst hxs
      exact ⟨rfl, rfl⟩
    · rw [hmρ] at hmσ; cases hmσ
  · rcases hσc with ⟨hmσ, _, _⟩ | ⟨e, n, ms', args₂, bs₂, hmσ, rfl, hnσ, hbσ, rfl⟩
    · have hρσ := hW.bare_unique σ hσ hmσ ρ hρ hhead.symm
      subst hρσ
      rw [hmρ] at hmσ; cases hmσ
    · obtain ⟨hnargs, hde⟩ := hW.ctor_disjoint ρ hρ σ hσ hhead.symm hmρ hmσ
      have hlen : args.length = args₂.length := by rw [hnρ, hnσ, hnargs]
      rw [List.append_assoc] at hxs
      obtain ⟨rfl, hrest⟩ := List.append_inj hxs hlen
      have hl : zs.length = 0 := by
        have := congrArg List.length hrest
        simp only [List.length_append, List.length_singleton] at this
        omega
      have hz := List.eq_nil_of_length_eq_zero hl
      subst hz
      simp only [List.singleton_append] at hrest
      injection hrest with hmaj _
      obtain ⟨rfl, rfl, rfl⟩ := ETm.appN_const_inj hmaj
      have hσρ := hde rfl
      subst hσρ
      exact ⟨rfl, rfl⟩

/-- the root case of the diamond: a step out of a redex is its contraction, or a step inside one
    pattern variable, matched by one step on the right-hand side. -/
theorem cRoot_cStep {tbl : List CRule} (hW : TableWF tbl) {a b c : ETm}
    (h1 : CRoot tbl a b) (h2 : CStep tbl a c) : c = b ∨ ∃ d, CStep tbl b d ∧ CRoot tbl c d := by
  have h1' := h1
  cases h1 with
  | @bare ρ hρ hm ls args hn =>
      rcases cStep_appN_const_inv h2 with ⟨args', rfl, h'⟩ | ⟨ys, zs, b', rfl, hb', rfl⟩
      · exact .inr ⟨_, cStep_appN_one h' _, .bare hρ hm ls args' (by rw [h'.length_eq, hn])⟩
      · obtain ⟨rfl, rfl⟩ := cRoot_prefix_det hW h1' hb' rfl
        exact .inl rfl
  | @ctor ρ hρ d m hm ls ls' args bs hn hb =>
      rcases cStep_appN_const_inv h2 with ⟨xs', rfl, h'⟩ | ⟨ys, zs, b', hxs, hb', rfl⟩
      · rcases h'.split with ⟨args', rfl, ha⟩ | ⟨ys, rfl, hy⟩
        · exact .inr ⟨_, cStep_appN_one (ha.append_left bs) _,
            .ctor hρ hm ls ls' args' bs (by rw [ha.length_eq, hn]) hb⟩
        · obtain ⟨maj, rfl, hmaj⟩ := hy.single_inv
          rcases cStep_appN_const_inv hmaj with ⟨bs', rfl, hbs⟩ | ⟨_, _, _, _, hroot, _⟩
          · exact .inr ⟨_, cStep_appN_one (hbs.append_right args) _,
              .ctor hρ hm ls ls' args bs' hn (by rw [hbs.length_eq, hb])⟩
          · exact (cRoot_not_major_head hW hρ hm hroot).elim
      · obtain ⟨rfl, rfl⟩ := cRoot_prefix_det hW h1' hb' hxs
        exact .inl rfl

/-! ## §4 the diamond and CR -/

/-- the constant rules have the diamond property up to equality. -/
theorem cStep_diamond {tbl : List CRule} (hW : TableWF tbl) {a b c : ETm}
    (h1 : CStep tbl a b) (h2 : CStep tbl a c) : b = c ∨ ∃ d, CStep tbl b d ∧ CStep tbl c d := by
  induction h1 generalizing c with
  | cr hc =>
      rcases cRoot_cStep hW hc h2 with rfl | ⟨d, hbd, hcd⟩
      · exact .inl rfl
      · exact .inr ⟨d, hbd, .cr hcd⟩
  | @appL f f' x h ih =>
      generalize hs : ETm.app f x = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          rcases cRoot_cStep hW hc (.appL x h) with rfl | ⟨d, hcd, hbd⟩
          · exact .inl rfl
          · exact .inr ⟨d, .cr hbd, hcd⟩
      | appL _ h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .appL _ hd1, .appL _ hd2⟩
      | appR _ h' =>
          cases hs
          exact .inr ⟨_, .appR _ h', .appL _ h⟩
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | @appR f x x' h ih =>
      generalize hs : ETm.app f x = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          rcases cRoot_cStep hW hc (.appR f h) with rfl | ⟨d, hcd, hbd⟩
          · exact .inl rfl
          · exact .inr ⟨d, .cr hbd, hcd⟩
      | appL _ h' =>
          cases hs
          exact .inr ⟨_, .appL _ h', .appR _ h⟩
      | appR _ h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .appR _ hd1, .appR _ hd2⟩
      | lam => cases hs
      | piL => cases hs
      | piR => cases hs
  | @lam B B' h ih =>
      generalize hs : ETm.lam B = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          rcases cRoot_cStep hW hc (.lam h) with rfl | ⟨d, hcd, hbd⟩
          · exact .inl rfl
          · exact .inr ⟨d, .cr hbd, hcd⟩
      | lam h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .lam hd1, .lam hd2⟩
      | appL => cases hs
      | appR => cases hs
      | piL => cases hs
      | piR => cases hs
  | @piL A A' B h ih =>
      generalize hs : ETm.pi A B = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          rcases cRoot_cStep hW hc (.piL B h) with rfl | ⟨d, hcd, hbd⟩
          · exact .inl rfl
          · exact .inr ⟨d, .cr hbd, hcd⟩
      | piL _ h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .piL _ hd1, .piL _ hd2⟩
      | piR _ h' =>
          cases hs
          exact .inr ⟨_, .piR _ h', .piL _ h⟩
      | appL => cases hs
      | appR => cases hs
      | lam => cases hs
  | @piR A B B' h ih =>
      generalize hs : ETm.pi A B = s at h2
      cases h2 with
      | cr hc =>
          subst hs
          rcases cRoot_cStep hW hc (.piR A h) with rfl | ⟨d, hcd, hbd⟩
          · exact .inl rfl
          · exact .inr ⟨d, .cr hbd, hcd⟩
      | piL _ h' =>
          cases hs
          exact .inr ⟨_, .piL _ h', .piR _ h⟩
      | piR _ h' =>
          cases hs
          rcases ih h' with rfl | ⟨d, hd1, hd2⟩
          · exact .inl rfl
          · exact .inr ⟨_, .piR _ hd1, .piR _ hd2⟩
      | appL => cases hs
      | appR => cases hs
      | lam => cases hs

/-- a relation with the diamond property up to equality is confluent. -/
theorem confluent_of_refl_diamond {α : Type} {T : α → α → Prop}
    (hd : ∀ {a b c : α}, T a b → T a c → b = c ∨ ∃ d, T b d ∧ T c d) : Confluent T := by
  let U : α → α → Prop := fun a b => a = b ∨ T a b
  have hU : ∀ {a b c : α}, U a b → U a c → ∃ d, U b d ∧ U c d := by
    intro a b c hb hc
    rcases hb with rfl | hb
    · exact ⟨c, hc, .inl rfl⟩
    rcases hc with rfl | hc
    · exact ⟨b, .inl rfl, .inr hb⟩
    rcases hd hb hc with rfl | ⟨d, h1, h2⟩
    · exact ⟨b, .inl rfl, .inl rfl⟩
    · exact ⟨d, .inr h1, .inr h2⟩
  have up : ∀ {a b : α}, RStar T a b → RStar U a b := fun h => rstar_mono (S := U) Or.inr h
  have down : ∀ {a b : α}, RStar U a b → RStar T a b :=
    fun h => rstar_flatten (rstar_mono (S := RStar T) rstar_of_refl h)
  intro a b c hb hc
  obtain ⟨d, h1, h2⟩ := confluent_of_diamond (T := U) hU (up hb) (up hc)
  exact ⟨d, down h1, down h2⟩

/-- CR(constant rules). -/
theorem confluent_cStep {tbl : List CRule} (hW : TableWF tbl) : Confluent (CStep tbl) :=
  confluent_of_refl_diamond (cStep_diamond hW)

end Rcic.Syn

#print axioms Rcic.Syn.ETm.spineHead_appN
#print axioms Rcic.Syn.ETm.spineArgs_appN
#print axioms Rcic.Syn.ETm.appN_const_inj
#print axioms Rcic.Syn.cStep_appN_head
#print axioms Rcic.Syn.cStep_appN_one
#print axioms Rcic.Syn.cStep_app_inv
#print axioms Rcic.Syn.cStep_appN_inv
#print axioms Rcic.Syn.cStep_const_inv
#print axioms Rcic.Syn.cStep_appN_const_inv
#print axioms Rcic.Syn.cRoot_inv
#print axioms Rcic.Syn.cRoot_not_major_head
#print axioms Rcic.Syn.cRoot_prefix_det
#print axioms Rcic.Syn.cRoot_cStep
#print axioms Rcic.Syn.cStep_diamond
#print axioms Rcic.Syn.confluent_of_refl_diamond
#print axioms Rcic.Syn.confluent_cStep
