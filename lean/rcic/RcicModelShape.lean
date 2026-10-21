import rcic.RcicDomainShape
import rcic.RcicDeclarative

/-
RCIC semantic model, part 2 (relation layer + interpretation): the
*propositional* twin of `RcicDomainShape`'s Boolean order, and the
`LE_Interp`-style interpretation relation `Interp EI ρ m M` — "compact
`m` is a lower bound of the denotation of `M` under valuation `ρ`".

Why a Prop twin (05:15Z ruling, sortRow via model soundness):

* The sort tag is instantiated at `α := Level`, and the semantic order
  on sort codes must be `=ₙ`-robust: `ConvT` derives `.sort u ≡ .sort v`
  for `eqN u v` (e.g. `imax 0 0` vs `0`), so a *syntactic* tag order
  would make soundness false. The tag relation is therefore `eqN`
  itself: `LeT (sortT u) (sortT v) ↔ eqN u v` — both directions of
  `sortRow` land for free.
* `eqN` is semantic (`∀ρ, eval ρ u = eval ρ v`) and has no decidable
  Boolean in this codebase — the model never calls the Boolean layer:
  application is relational (`AppLe`, the covering spec of
  `DShapeFun.app` for well-formed graphs) and the order is `LEP`.
* The Boolean layer is unchanged and still governs `DShape.WF` (which
  IS computable at `Level`, since syntactic `DecidableEq Level` exists):
  graph well-formedness is a syntactic-consistency property; only the
  *order the model reads* is `eqN`-parameterised.

`Interp`'s clauses follow the authors' audited `LE_Interp` design
(lower-bound relation, monotone in `m`, no function `f.app` needed) on
RCIC's `Expr Nat`: `bot` approximates anything at every level; `bvar`/
`sort` are bounded by the valuation/code; `app` is relational
application; `lam`/`pi` bind graphs whose entries interpret the body
under a pushed valuation; `letE` substitutes semantically; `lit`
defers to `natExpand`; `const` is delegated to an environment
interpretation parameter `EI` — δ-unfolding, the index-ignoring
recursor clause `⟦rec … b q⟧ρ := p(⟦M⟧ρ ⟦b⟧ρ ⊥)(⟦m⟧ρ)`, and `lfp` for
Loop all live in a concrete `EI` supplied by the next segment, without
churning this relation. `ρ` is an index (not a parameter), since
recursive occurrences go under `push`. `closure_claim` stays 0.
-/

namespace Rcic
namespace Domain

/-! ### 1. Propositional covering order, parameterised by the tag relation -/

variable {α : Type}

namespace DShape0

/-- Prop-level order at level 0: `R` is the sort-tag relation. -/
def LEP (R : α → α → Prop) : DShape0 α → DShape0 α → Prop
  | .bot, _ => True
  | .sort a, .sort a' => R a a'
  | _, _ => False

theorem LEP.rfl {R : α → α → Prop} (hR : ∀ a, R a a) (s : DShape0 α) :
    LEP R s s := by cases s <;> first | exact trivial | exact hR _

theorem LEP.trans {R : α → α → Prop}
    (hR : ∀ a b c, R a b → R b c → R a c) {s t u : DShape0 α} :
    LEP R s t → LEP R t u → LEP R s u := by
  cases s <;> cases t <;> cases u <;> simp only [LEP]
    <;> intro h1 h2 <;> first
    | exact h1.elim
    | exact h2.elim
    | exact hR _ _ _ h1 h2
    | exact trivial

theorem LEP.bot {R : α → α → Prop} (s : DShape0 α) : LEP R .bot s := by
  cases s <;> simp [LEP]

theorem LEP.le_bot {R : α → α → Prop} {s : DShape0 α} :
    LEP R s .bot → s = .bot := by
  cases s <;> simp [LEP]

/-- Prop-level compatibility at level 0. -/
def CompatPP (C : α → α → Prop) : DShape0 α → DShape0 α → Prop
  | .bot, _ | _, .bot => True
  | .sort a, .sort a' => C a a'

theorem CompatPP.symm {C : α → α → Prop} (hC : ∀ a b, C a b → C b a)
    {s t : DShape0 α} : CompatPP C s t → CompatPP C t s := by
  cases s <;> cases t <;> simp only [CompatPP] <;> intro h <;> first
    | exact h.elim
    | exact hC _ _ h
    | exact trivial

end DShape0

namespace DShapeFun
variable {S : Type}

/-- Covering order on graphs, propositionally: every entry `(u, v)` of
`f` is dominated by an entry `(u', v')` of `g` with `R u' u` (covering
input below) and `R v v'` (covering output above). -/
def LEP (R : S → S → Prop) (f g : List (S × S)) : Prop :=
  ∀ x ∈ f, ∃ y ∈ g, R y.1 x.1 ∧ R x.2 y.2

theorem LEP.refl {R : S → S → Prop} (hR : ∀ s, R s s) (f : List (S × S)) :
    LEP R f f := fun x hx => ⟨x, hx, hR _, hR _⟩

theorem LEP.trans {R : S → S → Prop}
    (hR : ∀ a b c : S, R a b → R b c → R a c) {f g h : List (S × S)} :
    LEP R f g → LEP R g h → LEP R f h := fun hfg hgh x hx => by
  obtain ⟨y, hyg, h1, h2⟩ := hfg x hx
  obtain ⟨z, hzh, h3, h4⟩ := hgh y hyg
  exact ⟨z, hzh, hR _ _ _ h3 h1, hR _ _ _ h2 h4⟩

theorem LEP.mono {R R' : S → S → Prop} {f g : List (S × S)}
    (h : ∀ a b, R a b → R' a b) : LEP R f g → LEP R' f g :=
  fun hfg x hx => by
    obtain ⟨y, hy, h1, h2⟩ := hfg x hx
    exact ⟨y, hy, h _ _ h1, h _ _ h2⟩

/-- Graph compatibility, propositionally: every cross pair of entries
with compatible inputs has compatible outputs. -/
def CompatPP (C : S → S → Prop) (f g : List (S × S)) : Prop :=
  ∀ x ∈ f, ∀ y ∈ g, C x.1 y.1 → C x.2 y.2

theorem CompatPP.symm {C : S → S → Prop}
    (hC : ∀ a b : S, C a b → C b a) {f g : List (S × S)} :
    CompatPP C f g → CompatPP C g f :=
  fun h y hy x hx hc => hC _ _ (h x hx y hy (hC _ _ hc))

/-- The Prop covering order agrees with the Boolean one when the
relations agree pointwise. -/
theorem LEP_iff {R : S → S → Prop} {Rb : S → S → Bool}
    (h : ∀ a b, R a b ↔ Rb a b = true) {f g : List (S × S)} :
    LEP R f g ↔ ble Rb f g = true := by
  rw [ble_def]
  constructor
  · intro hL x hx
    obtain ⟨y, hy, h1, h2⟩ := hL x hx
    exact ⟨y, hy,
      (Bool.and_eq_true _ _).symm ▸ ⟨(h _ _).1 h1, (h _ _).1 h2⟩⟩
  · intro hL x hx
    obtain ⟨y, hy, hb⟩ := hL x hx
    obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ ▸ hb
    exact ⟨y, hy, (h _ _).2 h1, (h _ _).2 h2⟩

end DShapeFun

namespace DShapeS
variable {S : Type}

/-- Prop-level order at successor levels. -/
def LEP (Rα : α → α → Prop) (R : S → S → Prop) :
    DShapeS α S → DShapeS α S → Prop
  | .bot, _ => True
  | .sort a, .sort a' => Rα a a'
  | .unit, .unit => True
  | .pi a f, .pi a' f' => R a a' ∧ DShapeFun.LEP R f f'
  | .lam f, .lam f' => DShapeFun.LEP R f f'
  | .sigma a f, .sigma a' f' => R a a' ∧ DShapeFun.LEP R f f'
  | .pair a b, .pair a' b' => R a a' ∧ R b b'
  | .nat, .nat => True
  | .zero, .zero => True
  | .succ v, .succ v' => R v v'
  | .eqc A a b, .eqc A' a' b' => R A A' ∧ R a a' ∧ R b b'
  | .reflc w, .reflc w' => R w w'
  | .neut i, .neut j => i = j
  | _, _ => False

theorem LEP.rfl {Rα : α → α → Prop} {R : S → S → Prop}
    (hRα : ∀ a, Rα a a) (hR : ∀ s, R s s) (s : DShapeS α S) :
    LEP Rα R s s := by
  cases s <;> simp only [LEP] <;> first
    | exact hRα _
    | exact ⟨hR _, DShapeFun.LEP.refl hR _⟩
    | exact ⟨hR _, hR _, hR _⟩
    | exact ⟨hR _, hR _⟩
    | exact DShapeFun.LEP.refl hR _
    | exact hR _
    | exact Eq.refl _
    | exact trivial

theorem LEP.trans {Rα : α → α → Prop} {R : S → S → Prop}
    (hRα : ∀ a b c, Rα a b → Rα b c → Rα a c)
    (hR : ∀ a b c : S, R a b → R b c → R a c) {s t u : DShapeS α S} :
    LEP Rα R s t → LEP Rα R t u → LEP Rα R s u := by
  cases s <;> cases t <;> cases u <;> simp only [LEP]
    <;> intro h1 h2 <;> first
    | exact h1.elim
    | exact h2.elim
    | exact hRα _ _ _ h1 h2
    | exact ⟨hR _ _ _ h1.1 h2.1, DShapeFun.LEP.trans hR h1.2 h2.2⟩
    | exact ⟨hR _ _ _ h1.1 h2.1,
        hR _ _ _ h1.2.1 h2.2.1, hR _ _ _ h1.2.2 h2.2.2⟩
    | exact ⟨hR _ _ _ h1.1 h2.1, hR _ _ _ h1.2 h2.2⟩
    | exact DShapeFun.LEP.trans hR h1 h2
    | exact hR _ _ _ h1 h2
    | exact h1.trans h2
    | exact trivial

theorem LEP.bot {Rα : α → α → Prop} {R : S → S → Prop} (s : DShapeS α S) :
    LEP Rα R .bot s := by cases s <;> simp [LEP]

theorem LEP.le_bot {Rα : α → α → Prop} {R : S → S → Prop} {s : DShapeS α S} :
    LEP Rα R s .bot → s = .bot := by
  cases s <;> simp [LEP]

/-- Prop-level compatibility at successor levels; `C` is the
*compatibility* relation on sub-shapes (not the order). -/
def CompatPP (Cα : α → α → Prop) (C : S → S → Prop) :
    DShapeS α S → DShapeS α S → Prop
  | .bot, _ | _, .bot => True
  | .sort a, .sort a' => Cα a a'
  | .unit, .unit => True
  | .pi a f, .pi a' f' => C a a' ∧ DShapeFun.CompatPP C f f'
  | .lam f, .lam f' => DShapeFun.CompatPP C f f'
  | .sigma a f, .sigma a' f' => C a a' ∧ DShapeFun.CompatPP C f f'
  | .pair a b, .pair a' b' => C a a' ∧ C b b'
  | .nat, .nat => True
  | .zero, .zero => True
  | .succ v, .succ v' => C v v'
  | .eqc A a b, .eqc A' a' b' => C A A' ∧ C a a' ∧ C b b'
  | .reflc w, .reflc w' => C w w'
  | .neut i, .neut j => i = j
  | _, _ => False

theorem CompatPP.symm {Cα : α → α → Prop} {C : S → S → Prop}
    (hCα : ∀ a b, Cα a b → Cα b a)
    (hC : ∀ a b : S, C a b → C b a) {s t : DShapeS α S} :
    CompatPP Cα C s t → CompatPP Cα C t s := by
  cases s <;> cases t <;> simp only [CompatPP] <;> intro h <;> first
    | exact h.elim
    | exact hCα _ _ h
    | exact ⟨hC _ _ h.1, DShapeFun.CompatPP.symm hC h.2⟩
    | exact ⟨hC _ _ h.1, hC _ _ h.2.1, hC _ _ h.2.2⟩
    | exact ⟨hC _ _ h.1, hC _ _ h.2⟩
    | exact DShapeFun.CompatPP.symm hC h
    | exact hC _ _ h
    | exact h.symm
    | exact trivial

theorem CompatPP.bot_l {Cα : α → α → Prop} {C : S → S → Prop}
    (s : DShapeS α S) : CompatPP Cα C .bot s := by
  cases s <;> simp [CompatPP]

theorem CompatPP.bot_r {Cα : α → α → Prop} {C : S → S → Prop}
    (s : DShapeS α S) : CompatPP Cα C s .bot := by
  cases s <;> simp [CompatPP]

/-- The Prop order agrees with the Boolean order when the tag relation
is syntactic equality and the sub-shape relations agree pointwise. -/
theorem LEP_iff_ble {R : S → S → Prop} {RSb : S → S → Bool}
    [DecidableEq α]
    (hS : ∀ a b, R a b ↔ RSb a b = true) {s t : DShapeS α S} :
    LEP (· = ·) R s t ↔ ble RSb s t = true := by
  cases s <;> cases t
    <;> simp only [LEP, ble, decide_eq_true_iff, Bool.and_eq_true, and_assoc]
    <;> first
    | exact ⟨False.elim, fun h => nomatch h⟩
    | exact ⟨fun _ => Eq.refl _, fun _ => True.intro⟩
    | exact Iff.rfl
    | exact hS _ _
    | exact and_congr (hS _ _) (DShapeFun.LEP_iff hS)
    | exact and_congr (hS _ _) (and_congr (hS _ _) (hS _ _))
    | exact and_congr (hS _ _) (hS _ _)
    | exact DShapeFun.LEP_iff hS

end DShapeS

namespace DShape

/-- The Prop-level order on `DShape α n`, by level recursion; `Rα` is
the sort-tag relation (`eqN` in the model). -/
def LEP (Rα : α → α → Prop) : ∀ {n}, DShape α n → DShape α n → Prop
  | 0 => DShape0.LEP Rα
  | _ + 1 => DShapeS.LEP Rα (DShape.LEP Rα)

/-- Prop-level compatibility on `DShape α n`. -/
def CompatPP (Cα : α → α → Prop) : ∀ {n}, DShape α n → DShape α n → Prop
  | 0 => DShape0.CompatPP Cα
  | _ + 1 => DShapeS.CompatPP Cα (DShape.CompatPP Cα)

theorem LEP.rfl {Rα : α → α → Prop} (hR : ∀ a, Rα a a) :
    ∀ {n} (s : DShape α n), LEP Rα s s
  | 0, s => DShape0.LEP.rfl hR s
  | _ + 1, s => DShapeS.LEP.rfl hR (LEP.rfl hR) s

theorem LEP.trans {Rα : α → α → Prop}
    (hR : ∀ a b c, Rα a b → Rα b c → Rα a c) :
    ∀ {n} {s t u : DShape α n},
      LEP Rα s t → LEP Rα t u → LEP Rα s u
  | 0, _, _, _, h1, h2 => DShape0.LEP.trans hR h1 h2
  | _ + 1, _, _, _, h1, h2 =>
      DShapeS.LEP.trans (R := DShape.LEP Rα) hR
        (fun _ _ _ x y => LEP.trans hR x y) h1 h2

theorem LEP.bot {Rα : α → α → Prop} : ∀ {n} (s : DShape α n),
    LEP Rα DShape.bot s
  | 0, s => DShape0.LEP.bot s
  | _ + 1, s => DShapeS.LEP.bot s

theorem LEP.le_bot {Rα : α → α → Prop} : ∀ {n} {s t : DShape α n},
    LEP Rα s t → t = DShape.bot → s = DShape.bot
  | 0, _, _ => fun h ht => DShape0.LEP.le_bot (ht ▸ h)
  | _ + 1, _, _ => fun h ht => DShapeS.LEP.le_bot (ht ▸ h)

theorem CompatPP.symm {Cα : α → α → Prop}
    (hC : ∀ a b, Cα a b → Cα b a) :
    ∀ {n} {s t : DShape α n},
      CompatPP Cα s t → CompatPP Cα t s
  | 0, _, _, h => DShape0.CompatPP.symm hC h
  | _ + 1, _, _, h =>
      DShapeS.CompatPP.symm (C := DShape.CompatPP Cα) hC
        (fun _ _ x => CompatPP.symm hC x) h

/-- Under `DecidableEq α` with syntactic tag equality, the Prop order
is the Boolean order — the bridge between the two layers. -/
theorem LEP_iff_ble [DecidableEq α] :
    ∀ {n} {s t : DShape α n}, LEP (· = ·) s t ↔ ble s t = true
  | 0, s, t => by
      show DShape0.LEP (· = ·) s t ↔ DShape0.ble s t = true
      cases s <;> cases t <;> simp [DShape0.LEP, DShape0.ble]
  | _ + 1, s, t =>
      DShapeS.LEP_iff_ble (fun _ _ => LEP_iff_ble)

end DShape

/-- The order on `TShape`, propositionally: different levels are
incomparable; within a level it is `DShape.LEP`. -/
def TShape.LEP (Rα : α → α → Prop) [DecidableEq α]
    (s t : TShape α) : Prop :=
  ∃ h : s.1 = t.1,
    DShape.LEP Rα s.2.1 (cast (congrArg (DShape α) h.symm) t.2.1)

namespace TShape
variable [DecidableEq α]

theorem LEP.rfl {Rα : α → α → Prop} (hR : ∀ a, Rα a a)
    (s : TShape α) : LEP Rα s s :=
  ⟨Eq.refl _, DShape.LEP.rfl hR s.2.1⟩

theorem LEP.trans {Rα : α → α → Prop}
    (hR : ∀ a b c, Rα a b → Rα b c → Rα a c) {s t u : TShape α} :
    LEP Rα s t → LEP Rα t u → LEP Rα s u := by
  rcases s with ⟨ns, xs⟩; rcases t with ⟨nt, xt⟩; rcases u with ⟨nu, xu⟩
  rintro ⟨hst, h1⟩ ⟨htu, h2⟩
  have hn1 : ns = nt := hst
  have hn2 : nt = nu := htu
  subst hn1; subst hn2
  exact ⟨Eq.refl _, DShape.LEP.trans hR h1 h2⟩

theorem LEP.bot_le {Rα : α → α → Prop} (s : TShape α) :
    LEP Rα ⟨s.1, WShape.bot⟩ s := by
  rcases s with ⟨n, w⟩
  exact ⟨Eq.refl _, DShape.LEP.bot w.1⟩

/-- A shape below a bottom code is itself bottom (the cast collapses
after the level equation is substituted; the leftover proof term is
`rfl` by proof irrelevance). -/
theorem LEP.le_bot {Rα : α → α → Prop} {n : Nat} {s : TShape α}
    (h : LEP Rα s (⟨n, WShape.bot⟩ : TShape α)) :
    s = ⟨n, WShape.bot⟩ := by
  rcases s with ⟨k, w⟩
  obtain ⟨hn, hle⟩ := h
  have hkn : k = n := hn
  subst hkn
  have hw : w = WShape.bot := Subtype.ext (DShape.LEP.le_bot hle (by rfl))
  subst hw
  rfl

end TShape

/-! ### 2. The model instantiation: tags `Level`, tag relation `eqN` -/

namespace Model

open Rcic.Declarative

/-- Well-formed compact shapes over `Level` tags. -/
abbrev LSh (n : Nat) := WShape Level n

/-- The total model domain. -/
abbrev LTShape := TShape Level

/-- The model order on `TShape Level`: the sort-tag relation is `eqN`.
Sort codes are ordered exactly by semantic level equality — the
`sorts` conversion rule is sound *because* `eqN` is reflexive, and
`sortRow` reads `eqN` straight back out of the order. -/
def LeT (s t : LTShape) : Prop := TShape.LEP eqN s t

theorem LeT.refl (s : LTShape) : LeT s s :=
  TShape.LEP.rfl (fun _ _ => Eq.refl _) s

theorem LeT.trans {s t u : LTShape} : LeT s t → LeT t u → LeT s u :=
  TShape.LEP.trans (fun _ _ _ h1 h2 ρ => (h1 ρ).trans (h2 ρ))

theorem LeT.bot_le (s : LTShape) : LeT ⟨s.1, WShape.bot⟩ s :=
  TShape.LEP.bot_le s

/-- Level-`n` bottom, as a `TShape`. -/
def botT (n : Nat) : LTShape := ⟨n, WShape.bot⟩

/-- The sort code `sort u` at level 0, as a `TShape`. -/
def sortT (u : Level) : LTShape := ⟨0, ⟨.sort u, trivial⟩⟩

/-- **Universe-code disjointness, both directions:** the semantic order
between sort codes *is* `eqN`. `sortRow` is this lemma applied after
conversion-soundness. -/
theorem sortT_leT_iff {u v : Level} : LeT (sortT u) (sortT v) ↔ eqN u v := by
  exact ⟨fun h => h.2, fun h => ⟨Eq.refl _, h⟩⟩

/-- A well-formed step-function graph at level `n`, packaged as the
well-formedness of its `lam` shape. -/
abbrev WFun (n : Nat) :=
  { g : DShapeFun Level n // DShape.WF (n := n + 1) (.lam g) }

/-- The `lam` code of a well-formed graph, as a `TShape`. -/
def lamT {n : Nat} (f : WFun n) : LTShape := ⟨n + 1, ⟨.lam f.1, f.2⟩⟩

/-- The `Π` code of domain `a` and well-formed codomain graph `f`. -/
def piT {n : Nat} (a : LSh n) (f : WFun n) : LTShape :=
  ⟨n + 1, ⟨.pi a.1 f.1, ⟨a.2, f.2⟩⟩⟩

/-- Relational application — the covering spec of `DShapeFun.app` for
well-formed graphs: `m` is below `f`'s value at `a` iff some graph
entry `(x, y)` covers it — input `x` below `a`, output `y` above `m`.
(For `WF` graphs this is exactly `m ≤ f·a`; the model needs only this
relational form, so `app`'s Boolean internals never appear.) -/
def AppLe (f a m : LTShape) : Prop :=
  ∃ (n : Nat) (fg : WFun n) (x y : LSh n),
    f = lamT fg ∧ (x.1, y.1) ∈ fg.1 ∧ LeT ⟨n, x⟩ a ∧ LeT m ⟨n, y⟩

theorem AppLe.mono {f a m m' : LTShape} (h : LeT m m') :
    AppLe f a m' → AppLe f a m :=
  fun ⟨n, fg, x, y, hf, hxy, hxa, hm'⟩ =>
    ⟨n, fg, x, y, hf, hxy, hxa, LeT.trans h hm'⟩

/-- Graph-domain coverage (the relational form of the authors'
`Shape.HasDom`): every entry `(x, y)` is dominated by an entry whose
input lies in the domain `a`. -/
def HasDomP (f a : LTShape) : Prop :=
  ∀ (n : Nat) (fg : WFun n) (x y : LSh n),
    f = lamT fg → (x.1, y.1) ∈ fg.1 →
      ∃ x' y' : LSh n, (x'.1, y'.1) ∈ fg.1 ∧
        DShape.LEP eqN x'.1 x.1 ∧ DShape.LEP eqN y.1 y'.1 ∧
        LeT ⟨n, x'⟩ a

/-- Valuations: a `TShape Level` per de Bruijn index (the paper's
⊥-valued variables live here — nothing forces `ρ i` above `botT`). -/
abbrev Valuation := Nat → LTShape

/-- Under-binder extension: `bvar 0 ↦ x`, the rest shifted. -/
def Valuation.push (ρ : Valuation) (x : LTShape) : Valuation
  | 0 => x
  | i + 1 => ρ i

/-- Pointwise order on valuations. -/
def Valuation.LeP (ρ ρ' : Valuation) : Prop := ∀ i, LeT (ρ i) (ρ' i)

theorem Valuation.LeP.rfl (ρ : Valuation) : ρ.LeP ρ :=
  fun _ => LeT.refl _

theorem Valuation.LeP.push {ρ ρ' : Valuation} {x x' : LTShape}
    (hρ : ρ.LeP ρ') (hx : LeT x x') : (ρ.push x).LeP (ρ'.push x')
  | 0 => hx
  | _ + 1 => hρ _

/-- The interpretation relation: `Interp EI ρ m M` reads "compact `m`
is a lower bound of `⟦M⟧ρ`", where `EI` is the environment
interpretation — the denotation of `const r ls`, supplied by the model
of `ResolvedEnv` (next segment: `definitionM` unfolds, `recursorM` is
the index-ignoring projection `p(⟦M⟧ρ ⟦b⟧ρ ⊥)(⟦m⟧ρ)`, Loop via `lfp`).

Clauses follow the authors' `LE_Interp`: `bot` approximates anything at
every level; `bvar`/`sort` are bounded by the valuation/code; `app` is
relational application; `lam`/`pi` bind graphs whose entries interpret
the body under a pushed valuation; `letE` substitutes semantically;
`lit` defers to `natExpand`; `const` takes `EI`'s value bounded by
`m`'s target. `ρ` is an index, not a parameter, since recursive
occurrences go under `push`. -/
inductive Interp (EI : Nat → List Level → LTShape → Prop) :
    Valuation → LTShape → Expr Nat → Prop where
  | bot {ρ : Valuation} {n : Nat} {M : Expr Nat} :
      Interp EI ρ ⟨n, WShape.bot⟩ M
  | bvar {ρ : Valuation} {m : LTShape} {i : Nat} :
      LeT m (ρ i) → Interp EI ρ m (.bvar i)
  | sort {ρ : Valuation} {m : LTShape} {u : Level} :
      LeT m (sortT u) → Interp EI ρ m (.sort u)
  | app {ρ : Valuation} {m f a : LTShape} {F A : Expr Nat} :
      Interp EI ρ f F → Interp EI ρ a A → AppLe f a m →
      Interp EI ρ m (.app F A)
  | lam {ρ : Valuation} {m : LTShape} {n : Nat} {a : LSh n} {f : WFun n}
      {A F : Expr Nat} :
      Interp EI ρ ⟨n, a⟩ A →
      HasDomP (lamT f) ⟨n, a⟩ →
      (∀ x y : LSh n, (x.1, y.1) ∈ f.1 → LeT ⟨n, x⟩ ⟨n, a⟩ →
        Interp EI (ρ.push ⟨n, x⟩) ⟨n, y⟩ F) →
      LeT m (lamT f) →
      Interp EI ρ m (.lam A F)
  | pi {ρ : Valuation} {m : LTShape} {n : Nat} {a a' : LSh n} {f : WFun n}
      {A B : Expr Nat} :
      Interp EI ρ ⟨n, a⟩ A → Interp EI ρ ⟨n, a'⟩ A →
      HasDomP (lamT f) ⟨n, a'⟩ →
      (∀ x y : LSh n, (x.1, y.1) ∈ f.1 → LeT ⟨n, x⟩ ⟨n, a'⟩ →
        Interp EI (ρ.push ⟨n, x⟩) ⟨n, y⟩ B) →
      LeT m (piT a f) →
      Interp EI ρ m (.pi A B)
  | letE {ρ : Valuation} {m s : LTShape} {A v b : Expr Nat} :
      Interp EI ρ s v → Interp EI (ρ.push s) m b →
      Interp EI ρ m (.letE A v b)
  | const {ρ : Valuation} {m u : LTShape} {r : Nat} {ls : List Level} :
      EI r ls u → LeT m u → Interp EI ρ m (.const r ls)
  | lit {ρ : Valuation} {m : LTShape} {t : Nat} :
      Interp EI ρ m (natExpand t) → Interp EI ρ m (.lit t)

/-- `Interp` is downward-closed in the shape argument — the
lower-bound reading. -/
theorem Interp.mono {EI : Nat → List Level → LTShape → Prop} {ρ : Valuation}
    {M : Expr Nat} {m' : LTShape} (H : Interp EI ρ m' M) :
    ∀ {m : LTShape}, LeT m m' → Interp EI ρ m M := by
  induction H with
  | bot =>
    intro m h
    obtain rfl := TShape.LEP.le_bot h
    exact .bot
  | bvar h1 => exact fun h => .bvar (LeT.trans h h1)
  | sort h1 => exact fun h => .sort (LeT.trans h h1)
  | app hf ha h1 ihf iha =>
    exact fun h => .app (ihf (LeT.refl _)) (iha (LeT.refl _))
      (AppLe.mono h h1)
  | lam ha hdom hb hm iha ihb =>
    exact fun h => .lam (iha (LeT.refl _)) hdom
      (fun x y hxy hxa => ihb x y hxy hxa (LeT.refl _)) (LeT.trans h hm)
  | pi ha ha' hdom hb hm iha iha' ihb =>
    exact fun h => .pi (iha (LeT.refl _)) (iha' (LeT.refl _)) hdom
      (fun x y hxy hxa => ihb x y hxy hxa (LeT.refl _)) (LeT.trans h hm)
  | letE hs hb ihs ihb => exact fun h => .letE (ihs (LeT.refl _)) (ihb h)
  | const hu hm => exact fun h => .const hu (LeT.trans h hm)
  | lit h1 ih => exact fun h => .lit (ih h)

/-- `Interp` is monotone in the valuation. -/
theorem Interp.mono_l {EI : Nat → List Level → LTShape → Prop}
    {m : LTShape} {M : Expr Nat} {ρ : Valuation}
    (H : Interp EI ρ m M) :
    ∀ {ρ' : Valuation}, ρ.LeP ρ' → Interp EI ρ' m M := by
  induction H with
  | bot => exact fun _ => .bot
  | bvar h => exact fun hρ => .bvar (LeT.trans h (hρ _))
  | sort h => exact fun _ => .sort h
  | app hf ha h1 ihf iha => exact fun hρ => .app (ihf hρ) (iha hρ) h1
  | lam ha hdom hb hm iha ihb =>
    exact fun hρ => .lam (iha hρ) hdom
      (fun x y hxy hxa =>
        ihb x y hxy hxa (Valuation.LeP.push hρ (LeT.refl _)))
      hm
  | pi ha ha' hdom hb hm iha iha' ihb =>
    exact fun hρ => .pi (iha hρ) (iha' hρ) hdom
      (fun x y hxy hxa =>
        ihb x y hxy hxa (Valuation.LeP.push hρ (LeT.refl _)))
      hm
  | letE hs hb ihs ihb =>
    exact fun hρ => .letE (ihs hρ) (ihb (Valuation.LeP.push hρ (LeT.refl _)))
  | const hu hm => exact fun _ => .const hu hm
  | lit h1 ih => exact fun hρ => .lit (ih hρ)

/-- Canonical self-interpretations. -/
theorem Interp.bvar' {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {i : Nat} : Interp EI ρ (ρ i) (.bvar i) :=
  .bvar (LeT.refl _)

theorem Interp.sort' {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {u : Level} : Interp EI ρ (sortT u) (.sort u) :=
  .sort (LeT.refl _)

/-- Sort inversion: a compact below `⟦sort u⟧` is a bottom or below
the sort code. -/
theorem Interp.le_sort {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m : LTShape} {u : Level}
    (H : Interp EI ρ m (.sort u)) :
    (∃ n, m = ⟨n, WShape.bot⟩) ∨ LeT m (sortT u) := by
  cases H with
  | bot => exact .inl ⟨_, Eq.refl _⟩
  | sort h => exact .inr h

/-- Bvar inversion. -/
theorem Interp.le_bvar {EI : Nat → List Level → LTShape → Prop}
    {ρ : Valuation} {m : LTShape} {i : Nat}
    (H : Interp EI ρ m (.bvar i)) :
    (∃ n, m = ⟨n, WShape.bot⟩) ∨ LeT m (ρ i) := by
  cases H with
  | bot => exact .inl ⟨_, Eq.refl _⟩
  | bvar h => exact .inr h

/-- Semantic equality of denotations: same lower bounds. Conversion
soundness is `ConvT M N ⟹ SEq`. -/
def SEq (EI : Nat → List Level → LTShape → Prop) (ρ : Valuation)
    (M N : Expr Nat) : Prop :=
  ∀ m, Interp EI ρ m M ↔ Interp EI ρ m N

theorem SEq.refl {EI : Nat → List Level → LTShape → Prop} {ρ : Valuation}
    (M : Expr Nat) : SEq EI ρ M M := fun _ => Iff.rfl

theorem SEq.symm {EI : Nat → List Level → LTShape → Prop} {ρ : Valuation}
    {M N : Expr Nat} (h : SEq EI ρ M N) : SEq EI ρ N M :=
  fun m => (h m).symm

theorem SEq.trans {EI : Nat → List Level → LTShape → Prop} {ρ : Valuation}
    {M N P : Expr Nat} (h1 : SEq EI ρ M N) (h2 : SEq EI ρ N P) :
    SEq EI ρ M P := fun m => (h1 m).trans (h2 m)

end Model

end Domain
end Rcic

#print axioms Rcic.Domain.Model.Interp
#print axioms Rcic.Domain.Model.Interp.mono
#print axioms Rcic.Domain.Model.Interp.mono_l
#print axioms Rcic.Domain.Model.sortT_leT_iff
