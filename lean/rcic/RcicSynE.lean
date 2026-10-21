import rcic.RcicSynLevel

/-!
# Syntactic sortRow, build step 2a — the erased rewrite system E

`research/rcic/semantic/S2_ERASED_E.md`. E acts on erased terms `ETm` (`RcicSynLevel`). It is
the union of two relations, each closed under all congruences:
* `RStep tbl`: β, plus the constant rules of a rule table `tbl` (δ, ι, unfold);
* `EtaStep`: η.

A constant rule matches `const head ls` applied to `nargs ls` argument variables and, when it has
a major, a constructor spine `const d ls'` applied to `m ls'` variables. Its right-hand side is a
term `rhs ls ls'` applied to all the matched variables in order. Every left-linear right-hand side
over the pattern variables has this form, up to β.

Proved here, for any table whose right-hand sides are `≈`-congruent and whose arities are
`eqNList`-invariant:
* sorts are E-normal (`eStep_sort_normal`);
* `≈` strongly simulates E (`eStep_strongSim`);
* Hindley–Rosen: E is confluent once `RStep tbl` and `EtaStep` are, and they strongly commute
  (`confluent_eStep`);
* hence sort separation for E modulo `≈` from those three obligations (`eqN_of_convE_sort`).

The three obligations are build step 2b, under `TableWF` (closed right-hand sides, rigid
constructor heads, one arity per head, major-less rules nullary). The last condition is what keeps
η from overlapping a constant rule at a variable-final pattern.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 spines and closedness -/

namespace ETm

/-- `f x₁ … xₙ`. -/
def appN (f : ETm) : List ETm → ETm
  | [] => f
  | x :: xs => appN (.app f x) xs

theorem appN_append (f : ETm) (xs ys : List ETm) :
    appN f (xs ++ ys) = appN (appN f xs) ys := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

theorem appN_snoc (f : ETm) (xs : List ETm) (x : ETm) :
    appN f (xs ++ [x]) = .app (appN f xs) x := by
  rw [appN_append]; rfl

/-- every free index is below `k`. -/
def ClosedAt : Nat → ETm → Prop
  | k, .bvar i => i < k
  | _, .star => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | k, .app f a => ClosedAt k f ∧ ClosedAt k a
  | k, .lam b => ClosedAt (k + 1) b
  | k, .pi a b => ClosedAt k a ∧ ClosedAt (k + 1) b

end ETm

theorem appN_eq_sort {f : ETm} {xs : List ETm} {l : Level} (h : ETm.appN f xs = .sort l) :
    xs = [] ∧ f = .sort l := by
  induction xs generalizing f with
  | nil => exact ⟨rfl, h⟩
  | cons x xs ih =>
      have h' := (ih h).2
      cases h'

theorem appN_const_ne_sort (c : Nat) (ls : List Level) (xs : List ETm) (l : Level) :
    ETm.appN (.const c ls) xs ≠ .sort l := by
  intro h
  have h' := (appN_eq_sort h).2
  cases h'

/-! ## §2 the rules -/

/-- A constant rule of E.
* left-hand side: `const head ls` applied to `nargs ls` variables, then, when `major = some (d, m)`,
  the constructor spine `const d ls'` applied to `m ls'` variables;
* right-hand side: `rhs ls ls'` applied to all matched variables in order (`ls' = []` when there
  is no major).
The arities are functions of the level lists because erasure drops proof arguments, and which
arguments are proofs depends on the instantiation (`Box.{u}`, S0 R1). -/
structure CRule where
  head : Nat
  nargs : List Level → Nat
  major : Option (Nat × (List Level → Nat))
  rhs : List Level → List Level → ETm

/-- root steps of the constant rules. -/
inductive CRoot (tbl : List CRule) : ETm → ETm → Prop
  | bare {ρ : CRule} (hρ : ρ ∈ tbl) (hm : ρ.major = none) (ls : List Level) (args : List ETm)
      (hn : args.length = ρ.nargs ls) :
      CRoot tbl (ETm.appN (.const ρ.head ls) args) (ETm.appN (ρ.rhs ls []) args)
  | ctor {ρ : CRule} (hρ : ρ ∈ tbl) {d : Nat} {m : List Level → Nat}
      (hm : ρ.major = some (d, m)) (ls ls' : List Level) (args bs : List ETm)
      (hn : args.length = ρ.nargs ls) (hb : bs.length = m ls') :
      CRoot tbl (ETm.appN (.const ρ.head ls) (args ++ [ETm.appN (.const d ls') bs]))
        (ETm.appN (ρ.rhs ls ls') (args ++ bs))

/-- β and the constant rules, closed under congruence. -/
inductive RStep (tbl : List CRule) : ETm → ETm → Prop
  | beta (M N : ETm) : RStep tbl (.app (.lam M) N) (ETm.inst 0 N M)
  | cr {a b : ETm} (h : CRoot tbl a b) : RStep tbl a b
  | appL {f f' : ETm} (a : ETm) (h : RStep tbl f f') : RStep tbl (.app f a) (.app f' a)
  | appR (f : ETm) {a a' : ETm} (h : RStep tbl a a') : RStep tbl (.app f a) (.app f a')
  | lam {b b' : ETm} (h : RStep tbl b b') : RStep tbl (.lam b) (.lam b')
  | piL {a a' : ETm} (b : ETm) (h : RStep tbl a a') : RStep tbl (.pi a b) (.pi a' b)
  | piR (a : ETm) {b b' : ETm} (h : RStep tbl b b') : RStep tbl (.pi a b) (.pi a b')

/-- η (`λ. F↑ 0 → F`), closed under congruence. -/
inductive EtaStep : ETm → ETm → Prop
  | eta (F : ETm) : EtaStep (.lam (.app (F.lift 0 1) (.bvar 0))) F
  | appL {f f' : ETm} (a : ETm) (h : EtaStep f f') : EtaStep (.app f a) (.app f' a)
  | appR (f : ETm) {a a' : ETm} (h : EtaStep a a') : EtaStep (.app f a) (.app f a')
  | lam {b b' : ETm} (h : EtaStep b b') : EtaStep (.lam b) (.lam b')
  | piL {a a' : ETm} (b : ETm) (h : EtaStep a a') : EtaStep (.pi a b) (.pi a' b)
  | piR (a : ETm) {b b' : ETm} (h : EtaStep b b') : EtaStep (.pi a b) (.pi a b')

/-- E: one step of `RStep tbl` or of `EtaStep`. -/
def EStep (tbl : List CRule) (a b : ETm) : Prop := RStep tbl a b ∨ EtaStep a b

/-! ## §3 sorts are E-normal -/

theorem cRoot_lhs {tbl : List CRule} {a b : ETm} (h : CRoot tbl a b) :
    ∃ c ls xs, a = ETm.appN (.const c ls) xs := by
  cases h with
  | bare _ _ ls args _ => exact ⟨_, ls, args, rfl⟩
  | ctor _ _ ls _ args bs _ _ => exact ⟨_, ls, _, rfl⟩

theorem rStep_sort_normal (tbl : List CRule) (l : Level) (t : ETm) : ¬ RStep tbl (.sort l) t := by
  intro h
  generalize hs : ETm.sort l = s at h
  cases h with
  | beta => cases hs
  | cr hc =>
      obtain ⟨c, ls, xs, rfl⟩ := cRoot_lhs hc
      exact appN_const_ne_sort c ls xs l hs.symm
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

theorem etaStep_sort_normal (l : Level) (t : ETm) : ¬ EtaStep (.sort l) t := by
  intro h
  generalize hs : ETm.sort l = s at h
  cases h with
  | eta => cases hs
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

theorem eStep_sort_normal (tbl : List CRule) (l : Level) (t : ETm) : ¬ EStep tbl (.sort l) t
  | .inl h => rStep_sort_normal tbl l t h
  | .inr h => etaStep_sort_normal l t h

/-! ## §4 inversion of `≈` -/

/-- `≈` on lists, pointwise. -/
inductive LvlEqList : List ETm → List ETm → Prop
  | nil : LvlEqList [] []
  | cons {x x' : ETm} {xs xs' : List ETm} (h : LvlEq x x') (hs : LvlEqList xs xs') :
      LvlEqList (x :: xs) (x' :: xs')

theorem LvlEqList.length_eq {xs xs' : List ETm} (h : LvlEqList xs xs') :
    xs.length = xs'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem LvlEqList.append {xs xs' ys ys' : List ETm} (h1 : LvlEqList xs xs')
    (h2 : LvlEqList ys ys') : LvlEqList (xs ++ ys) (xs' ++ ys') := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem LvlEqList.split {xs ys zs : List ETm} (h : LvlEqList (xs ++ ys) zs) :
    ∃ zs1 zs2, zs = zs1 ++ zs2 ∧ LvlEqList xs zs1 ∧ LvlEqList ys zs2 := by
  induction xs generalizing zs with
  | nil => exact ⟨[], zs, rfl, .nil, h⟩
  | cons x xs ih =>
      cases h with
      | cons hx hs =>
          obtain ⟨zs1, zs2, rfl, h1, h2⟩ := ih hs
          exact ⟨_ :: zs1, zs2, rfl, .cons hx h1, h2⟩

theorem LvlEqList.single_inv {x : ETm} {zs : List ETm} (h : LvlEqList [x] zs) :
    ∃ z, zs = [z] ∧ LvlEq x z := by
  cases h with
  | cons hx hs =>
      cases hs with
      | nil => exact ⟨_, rfl, hx⟩

theorem lvlEq_appN {f f' : ETm} {xs xs' : List ETm} (hf : LvlEq f f') (hxs : LvlEqList xs xs') :
    LvlEq (ETm.appN f xs) (ETm.appN f' xs') := by
  induction hxs generalizing f f' with
  | nil => exact hf
  | cons hx _ ih => exact ih (.app hf hx)

theorem lvlEq_appN_inv {f t : ETm} {xs : List ETm} (h : LvlEq (ETm.appN f xs) t) :
    ∃ f' xs', t = ETm.appN f' xs' ∧ LvlEq f f' ∧ LvlEqList xs xs' := by
  induction xs generalizing f with
  | nil => exact ⟨t, [], rfl, h, .nil⟩
  | cons x xs ih =>
      obtain ⟨g, xs', rfl, hg, hxs⟩ := ih h
      cases hg with
      | app hf hx => exact ⟨_, _ :: xs', rfl, hf, .cons hx hxs⟩

theorem lvlEq_bvar_inv {i : Nat} {t : ETm} (h : LvlEq (.bvar i) t) : t = .bvar i := by
  cases h; rfl

/-- `≈` reflects `lift`: what is `≈` to a lifted term is itself lifted. -/
theorem lvlEq_lift_inv : (F : ETm) → (c k : Nat) → {G : ETm} → LvlEq (F.lift c k) G →
    ∃ F', G = F'.lift c k ∧ LvlEq F F'
  | .bvar i, c, k, G, h => by
      refine ⟨.bvar i, ?_, .bvar i⟩
      simp only [ETm.lift] at h ⊢
      split
      · split at h
        · exact lvlEq_bvar_inv h
        · contradiction
      · split at h
        · contradiction
        · exact lvlEq_bvar_inv h
  | .star, c, k, G, h => by
      cases h; exact ⟨.star, rfl, .star⟩
  | .sort l, c, k, G, h => by
      cases h with
      | sort hl => exact ⟨.sort _, rfl, .sort hl⟩
  | .const r ls, c, k, G, h => by
      cases h with
      | const _ hls => exact ⟨.const r _, rfl, .const r hls⟩
  | .app f a, c, k, G, h => by
      cases h with
      | app hf ha =>
          obtain ⟨f', rfl, hf'⟩ := lvlEq_lift_inv f c k hf
          obtain ⟨a', rfl, ha'⟩ := lvlEq_lift_inv a c k ha
          exact ⟨.app f' a', rfl, .app hf' ha'⟩
  | .lam b, c, k, G, h => by
      cases h with
      | lam hb =>
          obtain ⟨b', rfl, hb'⟩ := lvlEq_lift_inv b (c + 1) k hb
          exact ⟨.lam b', rfl, .lam hb'⟩
  | .pi a b, c, k, G, h => by
      cases h with
      | pi ha hb =>
          obtain ⟨a', rfl, ha'⟩ := lvlEq_lift_inv a c k ha
          obtain ⟨b', rfl, hb'⟩ := lvlEq_lift_inv b (c + 1) k hb
          exact ⟨.pi a' b', rfl, .pi ha' hb'⟩

/-! ## §5 `≈` strongly simulates E -/

/-- what the strong simulation needs of a table: `≈`-congruent right-hand sides and
    `eqNList`-invariant arities. In the RCIC instance the arities count non-proof arguments, whose
    tags are `eqN`-invariant (`levelIsZero_instLevel_congr`). -/
structure TableCongr (tbl : List CRule) : Prop where
  rhs : ∀ ρ ∈ tbl, ∀ {ls ls₂ ms ms₂ : List Level}, eqNList ls ls₂ → eqNList ms ms₂ →
    LvlEq (ρ.rhs ls ms) (ρ.rhs ls₂ ms₂)
  nargs : ∀ ρ ∈ tbl, ∀ {ls ls₂ : List Level}, eqNList ls ls₂ → ρ.nargs ls = ρ.nargs ls₂
  marity : ∀ ρ ∈ tbl, ∀ {d : Nat} {m : List Level → Nat}, ρ.major = some (d, m) →
    ∀ {ls ls₂ : List Level}, eqNList ls ls₂ → m ls = m ls₂

theorem cRoot_strongSim {tbl : List CRule} (hT : TableCongr tbl) {a a' b : ETm}
    (hq : LvlEq a a') (h : CRoot tbl a b) : ∃ b', CRoot tbl a' b' ∧ LvlEq b b' := by
  cases h with
  | bare hρ hm ls args hn =>
      obtain ⟨f', xs', rfl, hf, hxs⟩ := lvlEq_appN_inv hq
      cases hf with
      | const _ hls =>
          refine ⟨_, .bare hρ hm _ xs' ?_, lvlEq_appN (hT.rhs _ hρ hls (eqNList_refl [])) hxs⟩
          rw [← hxs.length_eq, hn, hT.nargs _ hρ hls]
  | ctor hρ hm ls ls' args bs hn hb =>
      obtain ⟨f', xs', rfl, hf, hxs⟩ := lvlEq_appN_inv hq
      cases hf with
      | const _ hls =>
          obtain ⟨as₂, ys, rfl, has, hys⟩ := hxs.split
          obtain ⟨maj, rfl, hmaj⟩ := hys.single_inv
          obtain ⟨g, bs₂, rfl, hg, hbs⟩ := lvlEq_appN_inv hmaj
          cases hg with
          | const _ hls' =>
              refine ⟨_, .ctor hρ hm _ _ as₂ bs₂ ?_ ?_,
                lvlEq_appN (hT.rhs _ hρ hls hls') (has.append hbs)⟩
              · rw [← has.length_eq, hn, hT.nargs _ hρ hls]
              · rw [← hbs.length_eq, hb, hT.marity _ hρ hm hls']

theorem rStep_strongSim {tbl : List CRule} (hT : TableCongr tbl) :
    StrongSim LvlEq (RStep tbl) := by
  intro a a' b hq hs
  revert a'
  induction hs with
  | beta M N =>
      intro a' hq
      cases hq with
      | app hf ha =>
          cases hf with
          | lam hb => exact ⟨_, .beta _ _, LvlEq.inst' hb 0 ha⟩
  | cr hc =>
      intro a' hq
      obtain ⟨b', hc', hb⟩ := cRoot_strongSim hT hq hc
      exact ⟨b', .cr hc', hb⟩
  | appL a _ ih =>
      intro a' hq
      cases hq with
      | app hf ha =>
          obtain ⟨g, hg, hq'⟩ := ih hf
          exact ⟨_, .appL _ hg, .app hq' ha⟩
  | appR f _ ih =>
      intro a' hq
      cases hq with
      | app hf ha =>
          obtain ⟨g, hg, hq'⟩ := ih ha
          exact ⟨_, .appR _ hg, .app hf hq'⟩
  | lam _ ih =>
      intro a' hq
      cases hq with
      | lam hb =>
          obtain ⟨g, hg, hq'⟩ := ih hb
          exact ⟨_, .lam hg, .lam hq'⟩
  | piL b _ ih =>
      intro a' hq
      cases hq with
      | pi ha hb =>
          obtain ⟨g, hg, hq'⟩ := ih ha
          exact ⟨_, .piL _ hg, .pi hq' hb⟩
  | piR a _ ih =>
      intro a' hq
      cases hq with
      | pi ha hb =>
          obtain ⟨g, hg, hq'⟩ := ih hb
          exact ⟨_, .piR _ hg, .pi ha hq'⟩

theorem etaStep_strongSim : StrongSim LvlEq EtaStep := by
  intro a a' b hq hs
  revert a'
  induction hs with
  | eta F =>
      intro a' hq
      cases hq with
      | lam hb =>
          cases hb with
          | app hf hx =>
              obtain ⟨F', rfl, hF⟩ := lvlEq_lift_inv F 0 1 hf
              cases hx
              exact ⟨F', .eta F', hF⟩
  | appL a _ ih =>
      intro a' hq
      cases hq with
      | app hf ha =>
          obtain ⟨g, hg, hq'⟩ := ih hf
          exact ⟨_, .appL _ hg, .app hq' ha⟩
  | appR f _ ih =>
      intro a' hq
      cases hq with
      | app hf ha =>
          obtain ⟨g, hg, hq'⟩ := ih ha
          exact ⟨_, .appR _ hg, .app hf hq'⟩
  | lam _ ih =>
      intro a' hq
      cases hq with
      | lam hb =>
          obtain ⟨g, hg, hq'⟩ := ih hb
          exact ⟨_, .lam hg, .lam hq'⟩
  | piL b _ ih =>
      intro a' hq
      cases hq with
      | pi ha hb =>
          obtain ⟨g, hg, hq'⟩ := ih ha
          exact ⟨_, .piL _ hg, .pi hq' hb⟩
  | piR a _ ih =>
      intro a' hq
      cases hq with
      | pi ha hb =>
          obtain ⟨g, hg, hq'⟩ := ih hb
          exact ⟨_, .piR _ hg, .pi ha hq'⟩

theorem eStep_strongSim {tbl : List CRule} (hT : TableCongr tbl) :
    StrongSim LvlEq (EStep tbl) := by
  intro a a' b hq hs
  cases hs with
  | inl h =>
      obtain ⟨b', h', hb⟩ := rStep_strongSim hT hq h
      exact ⟨b', .inl h', hb⟩
  | inr h =>
      obtain ⟨b', h', hb⟩ := etaStep_strongSim hq h
      exact ⟨b', .inr h', hb⟩

/-! ## §6 Hindley–Rosen, abstractly -/

section ARS

variable {α : Type}

/-- `R*` and `S*` commute. -/
def Commute (R S : α → α → Prop) : Prop :=
  ∀ {a b c : α}, RStar R a b → RStar S a c → ∃ d, RStar S b d ∧ RStar R c d

/-- one `R` step against one `S` step closes with `S*` on one side and at most one `R` step on the
    other (Hindley's condition). -/
def StrongCommute (R S : α → α → Prop) : Prop :=
  ∀ {a b c : α}, R a b → S a c → ∃ d, RStar S b d ∧ (c = d ∨ R c d)

theorem rstar_mono {R S : α → α → Prop} (hRS : ∀ {a b : α}, R a b → S a b) {a b : α}
    (h : RStar R a b) : RStar S a b := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (hRS h) ih

theorem rstar_flatten {R : α → α → Prop} {a b : α} (h : RStar (RStar R) a b) : RStar R a b := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact h.trans' ih

theorem rstar_of_refl {R : α → α → Prop} {a b : α} (h : a = b ∨ R a b) : RStar R a b := by
  cases h with
  | inl h => subst h; exact .refl _
  | inr h => exact .single h

/-- Hindley's lemma: strong commutation gives commutation. -/
theorem commute_of_strong {R S : α → α → Prop} (h : StrongCommute R S) : Commute R S := by
  have strip : ∀ {a c : α}, RStar S a c → ∀ {b : α}, R a b →
      ∃ d, RStar S b d ∧ (c = d ∨ R c d) := by
    intro a c hs
    induction hs with
    | refl a => intro b hr; exact ⟨b, .refl b, .inr hr⟩
    | step hs1 _ ih =>
        intro b hr
        obtain ⟨d1, hbd1, hd1⟩ := h hr hs1
        cases hd1 with
        | inl he =>
            subst he
            rename_i c _
            exact ⟨c, hbd1.trans' ‹RStar S _ c›, .inl rfl⟩
        | inr hr' =>
            obtain ⟨d, hd1d, hcd⟩ := ih hr'
            exact ⟨d, hbd1.trans' hd1d, hcd⟩
  intro a b c hr hs
  induction hr generalizing c with
  | refl => exact ⟨c, hs, .refl c⟩
  | step hr1 _ ih =>
      obtain ⟨e, he, hce⟩ := strip hs hr1
      obtain ⟨d, hbd, hed⟩ := ih he
      exact ⟨d, hbd, (rstar_of_refl hce).trans' hed⟩

/-- a relation with the diamond property has a confluent closure. -/
theorem confluent_of_diamond {T : α → α → Prop}
    (hd : ∀ {a b c : α}, T a b → T a c → ∃ d, T b d ∧ T c d) : Confluent T := by
  have strip : ∀ {a c : α}, RStar T a c → ∀ {b : α}, T a b → ∃ d, RStar T b d ∧ T c d := by
    intro a c hs
    induction hs with
    | refl a => intro b hb; exact ⟨b, .refl b, hb⟩
    | step hs1 _ ih =>
        intro b hb
        obtain ⟨d1, hbd1, hd1⟩ := hd hb hs1
        obtain ⟨d, hd1d, hcd⟩ := ih hd1
        exact ⟨d, .step hbd1 hd1d, hcd⟩
  intro a b c hb hc
  induction hb generalizing c with
  | refl => exact ⟨c, hc, .refl c⟩
  | step h1 _ ih =>
      obtain ⟨e, he, hce⟩ := strip hc h1
      obtain ⟨d, hbd, hed⟩ := ih he
      exact ⟨d, hbd, .step hce hed⟩

/-- HINDLEY–ROSEN: the union of two confluent, commuting relations is confluent. -/
theorem confluent_union {R S : α → α → Prop} (hR : Confluent R) (hS : Confluent S)
    (hc : Commute R S) : Confluent (fun a b => R a b ∨ S a b) := by
  let T : α → α → Prop := fun a b => RStar R a b ∨ RStar S a b
  have hT : ∀ {a b c : α}, T a b → T a c → ∃ d, T b d ∧ T c d := by
    intro a b c hb hc'
    cases hb with
    | inl hb =>
        cases hc' with
        | inl hc' => obtain ⟨d, h1, h2⟩ := hR hb hc'; exact ⟨d, .inl h1, .inl h2⟩
        | inr hc' => obtain ⟨d, h1, h2⟩ := hc hb hc'; exact ⟨d, .inr h1, .inl h2⟩
    | inr hb =>
        cases hc' with
        | inl hc' => obtain ⟨d, h1, h2⟩ := hc hc' hb; exact ⟨d, .inl h2, .inr h1⟩
        | inr hc' => obtain ⟨d, h1, h2⟩ := hS hb hc'; exact ⟨d, .inr h1, .inr h2⟩
  have up : ∀ {a b : α}, RStar (fun a b => R a b ∨ S a b) a b → RStar T a b :=
    rstar_mono (fun h => h.elim (fun h => .inl (.single h)) (fun h => .inr (.single h)))
  have down : ∀ {a b : α}, RStar T a b → RStar (fun a b => R a b ∨ S a b) a b := by
    intro a b h
    apply rstar_flatten
    exact rstar_mono (fun h => h.elim (rstar_mono .inl) (rstar_mono .inr)) h
  intro a b c hb hc'
  obtain ⟨d, h1, h2⟩ := confluent_of_diamond hT (up hb) (up hc')
  exact ⟨d, down h1, down h2⟩

end ARS

/-! ## §7 sort separation for E, from step 2b's three obligations -/

theorem confluent_eStep {tbl : List CRule} (hR : Confluent (RStep tbl))
    (hη : Confluent EtaStep) (hc : StrongCommute (RStep tbl) EtaStep) :
    Confluent (EStep tbl) :=
  confluent_union hR hη (commute_of_strong hc)

/-- SORT SEPARATION FOR E MODULO `≈`. What is left for step 2b: CR of `RStep tbl` (Takahashi),
    CR of `EtaStep`, and their strong commutation, under `TableWF`. -/
theorem eqN_of_convE_sort {tbl : List CRule} (hT : TableCongr tbl)
    (hR : Confluent (RStep tbl)) (hη : Confluent EtaStep)
    (hc : StrongCommute (RStep tbl) EtaStep) {l l' : Level}
    (h : ConvMod (EStep tbl) LvlEq (.sort l) (.sort l')) : eqN l l' :=
  eqN_of_convMod_sort (eStep_strongSim hT) (confluent_eStep hR hη hc)
    (eStep_sort_normal tbl) h

/-! ## §8 the table conditions for step 2b -/

/-- the conditions under which step 2b proves the three obligations.
* `closed`: right-hand sides have no free index, so root steps commute with `lift`/`inst`;
* `rigid`: a constructor head used in a major has no rule, so a major spine is never a redex at a
  non-variable position of the pattern;
* `bare_unique`: a head with a major-less rule has no other rule;
* `ctor_disjoint`: two major rules of one head have the same argument count and distinct
  constructor heads;
* `bare_nullary`: a major-less rule has no argument. Otherwise `λ. c x₁ … xₖ₋₁ 0` would reduce by η
  to `c x₁ … xₖ₋₁` and by the rule to `λ. rhs x₁ … xₖ₋₁ 0`, a critical pair that `StrongCommute`
  does not close. With a major, the last pattern argument is a constructor spine, never `bvar 0`. -/
structure TableWF (tbl : List CRule) : Prop where
  congr : TableCongr tbl
  closed : ∀ ρ ∈ tbl, ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms)
  rigid : ∀ ρ ∈ tbl, ∀ {d : Nat} {m : List Level → Nat}, ρ.major = some (d, m) →
    ∀ σ ∈ tbl, σ.head ≠ d
  bare_unique : ∀ ρ ∈ tbl, ρ.major = none → ∀ σ ∈ tbl, σ.head = ρ.head → σ = ρ
  ctor_disjoint : ∀ ρ ∈ tbl, ∀ σ ∈ tbl, ρ.head = σ.head →
    ∀ {d e : Nat} {m n : List Level → Nat}, ρ.major = some (d, m) → σ.major = some (e, n) →
    ρ.nargs = σ.nargs ∧ (d = e → σ = ρ)
  bare_nullary : ∀ ρ ∈ tbl, ρ.major = none → ∀ ls, ρ.nargs ls = 0

/-! ## §9 pins -/

/-- Loop's unfold rule (S0 §2.2): `rec → λ M m. m (rec M m)`, at head 7. -/
def loopRule : CRule where
  head := 7
  nargs := fun _ => 0
  major := none
  rhs := fun ls _ =>
    .lam (.lam (.app (.bvar 0) (.app (.app (.const 7 ls) (.bvar 1)) (.bvar 0))))

theorem loopTable_wf : TableWF [loopRule] where
  congr :=
    { rhs := by
        intro ρ hρ ls ls₂ ms ms₂ hls _
        simp only [List.mem_singleton] at hρ; subst hρ
        exact .lam (.lam (.app (.bvar 0) (.app (.app (.const 7 hls) (.bvar 1)) (.bvar 0))))
      nargs := by
        intro ρ hρ _ _ _
        simp only [List.mem_singleton] at hρ; subst hρ; rfl
      marity := by
        intro ρ hρ _ _ hm
        simp only [List.mem_singleton] at hρ; subst hρ; cases hm }
  closed := by
    intro ρ hρ ls ms
    simp only [List.mem_singleton] at hρ; subst hρ
    simp only [loopRule, ETm.ClosedAt]
    exact ⟨Nat.zero_lt_succ _, ⟨trivial, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩,
      Nat.zero_lt_succ _⟩
  rigid := by
    intro ρ hρ _ _ hm
    simp only [List.mem_singleton] at hρ; subst hρ; cases hm
  bare_unique := by
    intro ρ hρ _ σ hσ _
    simp only [List.mem_singleton] at hρ hσ; subst hρ; subst hσ; rfl
  ctor_disjoint := by
    intro ρ hρ _ _ _ _ _ _ _ hm
    simp only [List.mem_singleton] at hρ; subst hρ; cases hm
  bare_nullary := by
    intro ρ hρ _ ls
    simp only [List.mem_singleton] at hρ; subst hρ; rfl

/-- PIN: Loop's rule fires at every level list, so `rec.{u}` and `rec.{u'}` with `u =ₙ u'` step to
    `≈` right-hand sides (S0 §6.6's `Y`). -/
theorem loop_step (ls : List Level) :
    EStep [loopRule] (.const 7 ls) (loopRule.rhs ls []) :=
  .inl (.cr (.bare (List.mem_singleton_self _) rfl ls [] rfl))

/-- PIN: η is a step of E, not only a conversion. -/
theorem eta_step_pin (tbl : List CRule) :
    EStep tbl (.lam (.app (.const 3 []) (.bvar 0))) (.const 3 []) :=
  .inr (.eta (.const 3 []))

end Rcic.Syn

#print axioms Rcic.Syn.ETm.appN_append
#print axioms Rcic.Syn.ETm.appN_snoc
#print axioms Rcic.Syn.appN_eq_sort
#print axioms Rcic.Syn.appN_const_ne_sort
#print axioms Rcic.Syn.cRoot_lhs
#print axioms Rcic.Syn.rStep_sort_normal
#print axioms Rcic.Syn.etaStep_sort_normal
#print axioms Rcic.Syn.eStep_sort_normal
#print axioms Rcic.Syn.LvlEqList.length_eq
#print axioms Rcic.Syn.LvlEqList.append
#print axioms Rcic.Syn.LvlEqList.split
#print axioms Rcic.Syn.LvlEqList.single_inv
#print axioms Rcic.Syn.lvlEq_appN
#print axioms Rcic.Syn.lvlEq_appN_inv
#print axioms Rcic.Syn.lvlEq_bvar_inv
#print axioms Rcic.Syn.lvlEq_lift_inv
#print axioms Rcic.Syn.cRoot_strongSim
#print axioms Rcic.Syn.rStep_strongSim
#print axioms Rcic.Syn.etaStep_strongSim
#print axioms Rcic.Syn.eStep_strongSim
#print axioms Rcic.Syn.rstar_mono
#print axioms Rcic.Syn.rstar_flatten
#print axioms Rcic.Syn.rstar_of_refl
#print axioms Rcic.Syn.commute_of_strong
#print axioms Rcic.Syn.confluent_of_diamond
#print axioms Rcic.Syn.confluent_union
#print axioms Rcic.Syn.confluent_eStep
#print axioms Rcic.Syn.eqN_of_convE_sort
#print axioms Rcic.Syn.loopTable_wf
#print axioms Rcic.Syn.loop_step
#print axioms Rcic.Syn.eta_step_pin
