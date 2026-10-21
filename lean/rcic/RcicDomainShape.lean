/-
RCIC semantic-model DOMAIN KIT, part 1 (compact elements): the
level-graded shape domain of arXiv 2607.13662 §2.1-2.2, written fresh
for RCIC — no code is ported (upstream carries no licence; ruling on
#6593). Audited design facts used: `C` = graded compact elements,
step functions = finite input/output graphs, decidable order /
compatibility / join / application, well-formedness as a subset type.

Differences from the paper's mechanisation (all recorded):

* The sort tag is parametric (`α`, `[DecidableEq α]`), not `Bool` —
  RCIC's sort row is a parametric level algebra; the kit must not bake
  in the authors' two-sort toy. The eventual instantiation is decided
  by the LR layer, not here.
* `neut (i : Nat)` is a new compact constructor — decision #1 of the
  semantic-rows ruling (non-degenerate neutrals; `RcicKGateNoGo` shows
  the Eq gate cannot live in a monotone denotation of degenerate
  neutrals). `neut i` is ordered only below `neut i` itself.
* `id` is spelled `eqc` (`Eq`-family code `eqc A a b` + `reflc w`) —
  RCIC's indexed family.

Every order/compatibility check is a `Bool` with `Decidable`
instances *built in* — the #6593 audit found the authors' only
`Classical.choice` entry point was `by_cases` falling back to
`propDecidable` for want of these instances; we never repeat that.

Architecture note: each level's operations are *structural* defs
parameterised by the lower level's relation (`DShapeS.ble R`,
`DShapeS.compat R`, `DShapeS.join jR R`), so equation lemmas are
first-order and `simp` unfolds cleanly; `DShape n` is only a
`Nat`-recursion wrapper. `closure_claim` stays 0.
-/

namespace Rcic
namespace Domain

variable {α : Type} [DecidableEq α]

/-! ### 1. Compact elements, level-graded -/

/-- Level-0 compact elements: only `⊥` and sort codes. -/
inductive DShape0 (α : Type) : Type where
  | bot : DShape0 α
  | sort : α → DShape0 α

/-- Successor-level compact elements over a lower level `S`.
`unit` is the singleton code; `neut i` is a non-degenerate neutral
atom; `pi`/`sigma`/`lam` carry finite step-function graphs;
`eqc`/`reflc` are the Eq-family code and its canonical value. -/
inductive DShapeS (α : Type) (S : Type) : Type where
  | bot : DShapeS α S
  | sort : α → DShapeS α S
  | unit : DShapeS α S
  | pi : S → List (S × S) → DShapeS α S
  | lam : List (S × S) → DShapeS α S
  | sigma : S → List (S × S) → DShapeS α S
  | pair : S → S → DShapeS α S
  | nat : DShapeS α S
  | zero : DShapeS α S
  | succ : S → DShapeS α S
  | eqc : S → S → S → DShapeS α S
  | reflc : S → DShapeS α S
  | neut : Nat → DShapeS α S

/-- `DShape α n` is the paper's `C_n`: level 0 sees `⊥` and sorts;
each successor adds the constructor towers over the previous level. -/
def DShape (α : Type) : Nat → Type
  | 0 => DShape0 α
  | n + 1 => DShapeS α (DShape α n)

/-- Step functions are finite lists of input/output pairs. -/
abbrev DShapeFun (α : Type) (n : Nat) := List (DShape α n × DShape α n)

/-- Generic `bot` at any level. -/
def DShape.bot : ∀ {n}, DShape α n
  | 0 => .bot
  | _ + 1 => .bot

/-- Generic `sort` code at any level. -/
def DShape.sort (a : α) : ∀ {n}, DShape α n
  | 0 => .sort a
  | _ + 1 => .sort a

/-! ### 2. Boolean order, compatibility, join, application -/

namespace DShapeFun
variable {S : Type}

/-- Covering order on step-function graphs: every entry `(u, v)` of
`f` is dominated by an entry `(u', v')` of `g` with `u' R u`
(`u'` below `u` — the covering entry fires wherever `(u, v)` does)
and `v R v'` (the covering output is above `v`). -/
def ble (R : S → S → Bool) (f g : List (S × S)) : Bool :=
  f.all fun (u, v) => g.any fun (u', v') => R u' u && R v v'

theorem ble_def {R : S → S → Bool} {f g : List (S × S)} :
    ble R f g ↔ ∀ x ∈ f, ∃ y ∈ g, R y.1 x.1 && R x.2 y.2 := by
  simp [ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]

/-- Graph compatibility: every cross pair of entries with compatible
inputs has compatible outputs. -/
def compat (R : S → T → Bool) (f : List (S × S)) (g : List (T × T)) : Bool :=
  f.all fun (x, y) => g.all fun (x', y') => !(R x x') || R y y'

theorem compat_def {R : S → T → Bool} {f : List (S × S)} {g : List (T × T)} :
    compat R f g ↔ ∀ x ∈ f, ∀ y ∈ g, R x.1 y.1 → R x.2 y.2 := by
  simp only [compat, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true,
    Bool.eq_false_iff]
  refine forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => ?_
  cases R _ _ <;> simp

/-- `trunc f a` keeps the entries whose input is below `a`. -/
def trunc (R : S → S → Bool) (f : List (S × S)) (a : S) : List (S × S) :=
  f.filter fun x => R x.1 a

/-- `maxBelow f` finds the entry of `f` whose input dominates every
other input of `f` (none on `[]`/no dominant entry). -/
def maxBelow (R : S → S → Bool) (f : List (S × S)) : Option (S × S) :=
  f.find? fun (x, _) => f.all fun (x', _) => R x' x

/-- Semantic application of a step function: the output of the
maximal-input entry among those whose input lies below `a`;
`bot` if the truncated graph is empty or has no dominant entry. -/
def app (R : S → S → Bool) (bot : S) (f : List (S × S)) (a : S) : S :=
  ((maxBelow R (trunc R f a)).map Prod.snd).getD bot

/-- Pairwise join on compatible inputs: for `x ∈ f`, `y ∈ g` with
compatible inputs, emit `(x.1 ⊔ y.1, (f·j) ⊔ (g·j))` where the
applications are evaluated at the joined input. -/
def join (jR : S → S → S) (R : S → S → Bool) (c : S → S → Bool) (bot : S)
    (f g : List (S × S)) : List (S × S) :=
  f.foldl (init := []) fun l x => g.foldl (init := l) fun l y =>
    if c x.1 y.1 then
      (jR x.1 y.1,
       jR (app R bot f (jR x.1 y.1)) (app R bot g (jR x.1 y.1))) :: l
    else l

end DShapeFun

namespace DShape0

/-- Boolean order at level 0. -/
def ble : DShape0 α → DShape0 α → Bool
  | .bot, _ => true
  | .sort a, .sort a' => decide (a = a')
  | _, _ => false

def ble_def {s t : DShape0 α} :
    ble s t ↔ (s = .bot ∨ ∃ a, s = .sort a ∧ t = .sort a) := by
  cases s <;> cases t <;> simp [ble, eq_comm]

/-- Compatibility at level 0: `bot` with anything; equal sorts. -/
def compat : DShape0 α → DShape0 α → Bool
  | .bot, _ | _, .bot => true
  | .sort a, .sort a' => decide (a = a')

def compat_def {s t : DShape0 α} :
    compat s t ↔ (s = .bot ∨ t = .bot ∨ ∃ a, s = .sort a ∧ t = .sort a) := by
  cases s <;> cases t <;> simp [compat, eq_comm]

/-- Join at level 0 (totalised: incompatible pairs give `bot`). -/
def join : DShape0 α → DShape0 α → DShape0 α
  | .bot, s | s, .bot => s
  | .sort a, .sort a' => if a = a' then .sort a else .bot

/-- Boolean equality at level 0. -/
def beq : DShape0 α → DShape0 α → Bool
  | .bot, .bot => true
  | .sort a, .sort a' => decide (a = a')
  | _, _ => false

theorem beq_iff {s t : DShape0 α} : beq s t ↔ s = t := by
  cases s <;> cases t <;> simp [beq]

def decEq (s t : DShape0 α) : Decidable (s = t) :=
  if h : beq s t then isTrue (beq_iff.1 h) else isFalse (mt beq_iff.2 h)

end DShape0

namespace DShapeS
variable {S : Type}

/-- Boolean order at successor levels. -/
def ble (R : S → S → Bool) : DShapeS α S → DShapeS α S → Bool
  | .bot, _ => true
  | .sort a, .sort a' => decide (a = a')
  | .unit, .unit => true
  | .pi a f, .pi a' f' => R a a' && DShapeFun.ble R f f'
  | .lam f, .lam f' => DShapeFun.ble R f f'
  | .sigma a f, .sigma a' f' => R a a' && DShapeFun.ble R f f'
  | .pair a b, .pair a' b' => R a a' && R b b'
  | .nat, .nat => true
  | .zero, .zero => true
  | .succ v, .succ v' => R v v'
  | .eqc A a b, .eqc A' a' b' => R A A' && R a a' && R b b'
  | .reflc w, .reflc w' => R w w'
  | .neut i, .neut j => decide (i = j)
  | _, _ => false

/-- Compatibility at successor levels; `cR` is the *compatibility*
relation on sub-shapes (not the order). -/
def compat (cR : S → S → Bool) : DShapeS α S → DShapeS α S → Bool
  | .bot, _ | _, .bot => true
  | .sort a, .sort a' => decide (a = a')
  | .unit, .unit => true
  | .pi a f, .pi a' f' => cR a a' && DShapeFun.compat cR f f'
  | .lam f, .lam f' => DShapeFun.compat cR f f'
  | .sigma a f, .sigma a' f' => cR a a' && DShapeFun.compat cR f f'
  | .pair a b, .pair a' b' => cR a a' && cR b b'
  | .nat, .nat => true
  | .zero, .zero => true
  | .succ v, .succ v' => cR v v'
  | .eqc A a b, .eqc A' a' b' => cR A A' && cR a a' && cR b b'
  | .reflc w, .reflc w' => cR w w'
  | .neut i, .neut j => decide (i = j)
  | _, _ => false

/-- Join at successor levels (totalised by `compat`; incompatible
heads give `bot`). -/
def join (jR : S → S → S) (R cR : S → S → Bool) (botS : S) :
    DShapeS α S → DShapeS α S → DShapeS α S
  | .bot, s | s, .bot => s
  | .sort a, .sort a' => if a = a' then .sort a else .bot
  | .unit, .unit => .unit
  | .pi a f, .pi a' f' => .pi (jR a a') (DShapeFun.join jR R cR botS f f')
  | .lam f, .lam f' => .lam (DShapeFun.join jR R cR botS f f')
  | .sigma a f, .sigma a' f' =>
    .sigma (jR a a') (DShapeFun.join jR R cR botS f f')
  | .pair a b, .pair a' b' => .pair (jR a a') (jR b b')
  | .nat, .nat => .nat
  | .zero, .zero => .zero
  | .succ v, .succ v' => .succ (jR v v')
  | .eqc A a b, .eqc A' a' b' => .eqc (jR A A') (jR a a') (jR b b')
  | .reflc w, .reflc w' => .reflc (jR w w')
  | .neut i, .neut j => if i = j then .neut i else .bot
  | _, _ => .bot

/-- Boolean equality at successor levels. -/
def beq [DecidableEq S] : DShapeS α S → DShapeS α S → Bool
  | .bot, .bot => true
  | .sort a, .sort a' => decide (a = a')
  | .unit, .unit => true
  | .pi a f, .pi a' f' => decide (a = a') && decide (f = f')
  | .lam f, .lam f' => decide (f = f')
  | .sigma a f, .sigma a' f' => decide (a = a') && decide (f = f')
  | .pair a b, .pair a' b' => decide (a = a') && decide (b = b')
  | .nat, .nat => true
  | .zero, .zero => true
  | .succ v, .succ v' => decide (v = v')
  | .eqc A a b, .eqc A' a' b' =>
    decide (A = A') && decide (a = a') && decide (b = b')
  | .reflc w, .reflc w' => decide (w = w')
  | .neut i, .neut j => decide (i = j)
  | _, _ => false

theorem beq_iff [DecidableEq S] {s t : DShapeS α S} :
    beq s t ↔ s = t := by
  cases s <;> cases t <;> simp [beq, and_assoc]

def decEq [DecidableEq S] (s t : DShapeS α S) : Decidable (s = t) :=
  if h : beq s t then isTrue (beq_iff.1 h)
  else isFalse (mt beq_iff.2 h)

end DShapeS

namespace DShape

/-- The order on `DShape α n`, by recursion on the level. -/
def ble : ∀ {n}, DShape α n → DShape α n → Bool
  | 0 => DShape0.ble
  | _ + 1 => DShapeS.ble ble

/-- Compatibility on `DShape α n`. -/
def compat : ∀ {n}, DShape α n → DShape α n → Bool
  | 0 => DShape0.compat
  | _ + 1 => DShapeS.compat compat

/-- Join on `DShape α n`. -/
def join : ∀ {n}, DShape α n → DShape α n → DShape α n
  | 0 => DShape0.join
  | _ + 1 => DShapeS.join join ble compat DShape.bot

/-- `ble` read as a proposition. -/
def LE {n} (s t : DShape α n) : Prop := ble s t

instance {n} : _root_.LE (DShape α n) := ⟨DShape.LE⟩

/-- The order is decidable by construction — `by_cases` on
`s ≤ t` never touches `Classical.propDecidable`. -/
instance {n} : DecidableRel (α := DShape α n) (· ≤ ·) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- Compatibility as a proposition. -/
def CompatP {n} (s t : DShape α n) : Prop := compat s t

instance {n} {s t : DShape α n} : Decidable (CompatP s t) :=
  inferInstanceAs (Decidable (_ = true))

/-- Structural `DecidableEq` on shapes — needed downstream for
`by_cases` on `x = .bot` (the audit's missing-instance lesson). -/
def decEq : ∀ {n} (s t : DShape α n), Decidable (s = t)
  | 0 => DShape0.decEq
  | n' + 1 =>
    letI : DecidableEq (DShape α n') := fun a b => decEq a b
    fun (s t : DShapeS α (DShape α n')) => DShapeS.decEq s t

instance {n} : DecidableEq (DShape α n) := fun s t => decEq s t

end DShape

/-! ### 3. Order and compatibility lemmas -/

namespace DShapeFun
variable {S : Type}

theorem ble_refl {R : S → S → Bool} (hR : ∀ s, R s s) :
    ∀ f : List (S × S), ble R f f := by
  simp only [ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  intro f x hx; exact ⟨x, hx, hR _, hR _⟩

theorem ble_trans {R : S → S → Bool}
    (hR : ∀ {a b c : S}, R a b → R b c → R a c)
    {f g h : List (S × S)} : ble R f g → ble R g h → ble R f h := by
  simp only [ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  intro hfg hgh x hx
  obtain ⟨y, hyg, h1, h2⟩ := hfg x hx
  obtain ⟨z, hzh, h3, h4⟩ := hgh y hyg
  exact ⟨z, hzh, hR h3 h1, hR h2 h4⟩

/-- Pointwise `R`-weakening descends through the covering order. -/
theorem ble_mono {R R' : S → S → Bool} {f g : List (S × S)}
    (h : ∀ {a b}, R a b → R' a b) : ble R f g → ble R' f g := by
  simp only [ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  intro hfg x hx; obtain ⟨y, hy, h1, h2⟩ := hfg x hx
  exact ⟨y, hy, h h1, h h2⟩

/-- Compatibility is symmetric when `R` is. -/
theorem compat_symm {R : S → S → Bool} (hR : ∀ {a b : S}, R a b → R b a)
    {f g : List (S × S)} : compat R f g → compat R g f := by
  simp only [compat_def]
  intro H x hx y hy h; exact hR (H y hy x hx (hR h))

/- Self-compatibility of a graph is *not* automatic (entries may map
compatible inputs to incompatible outputs); it is a `WF` property,
proved at the well-formed layer. -/

/-- Truncation picks up exactly the entries with input below `a`. -/
theorem mem_trunc {R : S → S → Bool} {f : List (S × S)} {a : S} {x} :
    x ∈ trunc R f a ↔ x ∈ f ∧ R x.1 a := by
  simp [trunc]

theorem mem_trunc_self {R : S → S → Bool} {f : List (S × S)} {a : S} :
    trunc R f a ⊆ f := fun _ h => (mem_trunc.1 h).1

/-- `maxBelow`'s result is an entry of the list. -/
theorem maxBelow_mem {R : S → S → Bool} {f : List (S × S)} {x : S × S} :
    maxBelow R f = some x → x ∈ f := by
  simp only [maxBelow]; intro h
  exact List.mem_of_find?_eq_some h

/-- `maxBelow`'s input dominates every input in the list. -/
theorem maxBelow_dominates {R : S → S → Bool} {f : List (S × S)} {x : S × S} :
    maxBelow R f = some x → ∀ x' ∈ f, R x'.1 x.1 := by
  intro h x' hx'
  simp only [maxBelow] at h
  have hp := (List.find?_eq_some.1 h).1
  rw [List.all_eq_true] at hp
  exact hp _ hx'

end DShapeFun

namespace DShape0

theorem ble_refl : ∀ s : DShape0 α, ble s s := by
  intro s; cases s <;> simp [ble]

theorem ble_trans {s t u : DShape0 α} : ble s t → ble t u → ble s u := by
  cases s <;> cases t <;> cases u <;> simp [ble]
  exact fun h1 h2 => h1 ▸ h2 ▸ rfl

theorem ble_le_bot {s : DShape0 α} : ble s .bot → s = .bot := by
  cases s <;> simp [ble]

theorem compat_refl : ∀ s : DShape0 α, compat s s := by
  intro s; cases s <;> simp [compat]

theorem compat_symm {s t : DShape0 α} : compat s t → compat t s := by
  cases s <;> cases t <;> simp [compat, eq_comm]

end DShape0

namespace DShapeS
variable {S : Type}

theorem ble_refl {R : S → S → Bool} (hR : ∀ s : S, R s s) :
    ∀ s : DShapeS α S, ble R s s := by
  intro s; cases s <;> simp [ble, hR, DShapeFun.ble_refl hR]

theorem ble_trans {R : S → S → Bool}
    (hR : ∀ {a b c : S}, R a b → R b c → R a c)
    {s t u : DShapeS α S} : ble R s t → ble R t u → ble R s u := by
  intro hst htu
  cases s <;> cases t <;> cases u <;>
    simp only [ble, Bool.and_eq_true, decide_eq_true_iff, reduceCtorEq]
      at hst htu ⊢
  case sort.sort.sort => exact hst ▸ htu
  case pi.pi.pi =>
    exact ⟨hR hst.1 htu.1, DShapeFun.ble_trans (@hR) hst.2 htu.2⟩
  case lam.lam.lam => exact DShapeFun.ble_trans (@hR) hst htu
  case sigma.sigma.sigma =>
    exact ⟨hR hst.1 htu.1, DShapeFun.ble_trans (@hR) hst.2 htu.2⟩
  case pair.pair.pair => exact ⟨hR hst.1 htu.1, hR hst.2 htu.2⟩
  case succ.succ.succ => exact hR hst htu
  case eqc.eqc.eqc =>
    exact ⟨⟨hR hst.1.1 htu.1.1, hR hst.1.2 htu.1.2⟩, hR hst.2 htu.2⟩
  case reflc.reflc.reflc => exact hR hst htu
  case neut.neut.neut => exact hst ▸ htu

theorem compat_symm {R : S → S → Bool} (hR : ∀ {a b : S}, R a b → R b a)
    {s t : DShapeS α S} : compat R s t → compat R t s := by
  intro hst
  cases s <;> cases t <;>
    simp only [compat, Bool.and_eq_true, decide_eq_true_iff, reduceCtorEq]
      at hst ⊢
  case sort.sort => exact eq_comm.1 hst
  case pi.pi => exact ⟨hR hst.1, DShapeFun.compat_symm (@hR) hst.2⟩
  case lam.lam => exact DShapeFun.compat_symm (@hR) hst
  case sigma.sigma => exact ⟨hR hst.1, DShapeFun.compat_symm (@hR) hst.2⟩
  case pair.pair => exact ⟨hR hst.1, hR hst.2⟩
  case succ.succ => exact hR hst
  case eqc.eqc => exact ⟨⟨hR hst.1.1, hR hst.1.2⟩, hR hst.2⟩
  case reflc.reflc => exact hR hst
  case neut.neut => exact hst.symm

theorem ble_bot {R : S → S → Bool} (s : DShapeS α S) :
    ble R .bot s := rfl

theorem ble_le_bot {R : S → S → Bool} {s : DShapeS α S} :
    ble R s .bot → s = .bot := by
  cases s <;> simp [ble]

theorem join_bot_l {jR : S → S → S} {R cR : S → S → Bool} {botS : S}
    (s : DShapeS α S) : join jR R cR botS .bot s = s := by
  cases s <;> rfl

theorem join_bot_r {jR : S → S → S} {R cR : S → S → Bool} {botS : S}
    (s : DShapeS α S) : join jR R cR botS s .bot = s := by
  cases s <;> rfl

end DShapeS

namespace DShapeFun
variable {S : Type}

/-- Specification of `app`: when the truncated graph has a
dominant-input entry `(x, y)`, `app f a = y`, that entry is in `f`,
its input is below `a`, and it dominates every input of `f` below
`a`. -/
theorem app_spec {R : S → S → Bool} {bot : S} {f : List (S × S)}
    {a x y : S}
    (h : maxBelow R (trunc R f a) = some (x, y)) :
    app R bot f a = y ∧
      (x, y) ∈ f ∧ R x a ∧
        ∀ x' ∈ f, R x'.1 a → R x'.1 x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [app, h]
  · exact mem_trunc_self (maxBelow_mem h)
  · exact (mem_trunc.1 (maxBelow_mem h)).2
  · intro x' hx' hle
    exact maxBelow_dominates h _ (mem_trunc.2 ⟨hx', hle⟩)

/-- `app` returns `bot` exactly when the truncated graph has no
dominant-input entry. -/
theorem app_eq_bot {R : S → S → Bool} {bot : S} {f : List (S × S)}
    {a : S}
    (h : maxBelow R (trunc R f a) = none) : app R bot f a = bot := by
  simp [app, h]

/-- Truncation is monotone in the bound. -/
theorem trunc_mono {R : S → S → Bool}
    (hR : ∀ {a b c : S}, R a b → R b c → R a c)
    {f : List (S × S)} {a b : S} (hab : R a b) :
    trunc R f a ⊆ trunc R f b :=
  fun _ hx => mem_trunc.2 ⟨(mem_trunc.1 hx).1, hR (mem_trunc.1 hx).2 hab⟩

end DShapeFun

/-! ### 4. Level-polymorphic order facts -/

namespace DShape

theorem ble_refl : ∀ {n} (s : DShape α n), ble s s
  | 0 => fun s => DShape0.ble_refl s
  | _ + 1 => fun s => DShapeS.ble_refl (fun x => ble_refl x) s

theorem ble_trans : ∀ {n} {s t u : DShape α n},
    ble s t → ble t u → ble s u
  | 0 => fun hst htu => DShape0.ble_trans hst htu
  | _ + 1 => fun hst htu => DShapeS.ble_trans (@ble_trans _) hst htu

theorem ble_le_bot {n} {s : DShape α n} :
    ble s DShape.bot → s = DShape.bot := by
  induction n with
  | zero => exact fun h => DShape0.ble_le_bot h
  | succ n' =>
    intro h
    have h' : DShapeS.ble (α := α) (S := DShape α n') DShape.ble s
        DShapeS.bot := h
    exact DShapeS.ble_le_bot h'

theorem ble_bot {n} (s : DShape α n) : ble DShape.bot s := by
  induction n with
  | zero => cases s <;> rfl
  | succ n' =>
    show DShapeS.ble (α := α) (S := DShape α n') DShape.ble
      DShapeS.bot s = true
    exact DShapeS.ble_bot s

@[refl] theorem LE.rfl {n} (s : DShape α n) : s ≤ s := ble_refl s

theorem LE.trans {n} {s t u : DShape α n} : s ≤ t → t ≤ u → s ≤ u :=
  ble_trans

theorem bot_le {n} (s : DShape α n) : DShape.bot ≤ s := ble_bot s

theorem le_bot {n} {s : DShape α n} : s ≤ DShape.bot → s = DShape.bot :=
  ble_le_bot

theorem compat_bot {n} (s : DShape α n) : compat DShape.bot s := by
  cases n <;> cases s <;> rfl

theorem compat_symm : ∀ {n} {s t : DShape α n}, compat s t → compat t s
  | 0 => DShape0.compat_symm
  | _ + 1 => DShapeS.compat_symm (@compat_symm _)

/-- The covering order is a preorder; antisymmetry is the setoid
`Equiv`, not structural equality. -/
def Equiv {n} (s t : DShape α n) : Prop := s ≤ t ∧ t ≤ s

theorem Equiv.refl {n} (s : DShape α n) : Equiv s s := ⟨LE.rfl _, LE.rfl _⟩
theorem Equiv.symm {n} {s t : DShape α n} (h : Equiv s t) : Equiv t s :=
  ⟨h.2, h.1⟩
theorem Equiv.trans {n} {s t u : DShape α n} (h1 : Equiv s t)
    (h2 : Equiv t u) : Equiv s u :=
  ⟨LE.trans h1.1 h2.1, LE.trans h2.2 h1.2⟩

instance {n} : Setoid (DShape α n) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

end DShape

namespace DShapeFun
variable {S : Type}

/-- Inner `foldl` membership: over a fixed `x`, iterating `gl` emits
exactly the `y ∈ gl` with compatible input. The applications `f`, `g`
stay fixed; `gl` is the iterated copy. -/
theorem mem_join_inner {jR : S → S → S} {R c : S → S → Bool} {bot : S}
    {f g : List (S × S)} {x z : S × S} :
    ∀ {gl l : List (S × S)},
      z ∈ gl.foldl (init := l) (fun l y =>
          if c x.1 y.1 then
            (jR x.1 y.1,
             jR (app R bot f (jR x.1 y.1)) (app R bot g (jR x.1 y.1))) :: l
          else l) ↔
        z ∈ l ∨ ∃ y ∈ gl, c x.1 y.1 ∧
          z = (jR x.1 y.1,
               jR (app R bot f (jR x.1 y.1)) (app R bot g (jR x.1 y.1))) := by
  intro gl
  induction gl with
  | nil => intro l; simp
  | cons y gl ih =>
    intro l
    rw [List.foldl_cons, ih]
    by_cases hc : c x.1 y.1 = true
    · rw [if_pos hc]
      constructor
      · rintro (h | ⟨y', hy', h1, h2⟩)
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inr ⟨y, List.mem_cons_self _ _, hc, rfl⟩
          · exact .inl h
        · exact .inr ⟨y', List.mem_cons_of_mem _ hy', h1, h2⟩
      · rintro (h | ⟨y', hy', h1, h2⟩)
        · exact .inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.1 hy' with rfl | hy'
          · exact .inl (List.mem_cons.2 (.inl h2))
          · exact .inr ⟨y', hy', h1, h2⟩
    · rw [if_neg hc]
      constructor
      · rintro (h | ⟨y', hy', h1, h2⟩)
        · exact .inl h
        · exact .inr ⟨y', List.mem_cons_of_mem _ hy', h1, h2⟩
      · rintro (h | ⟨y', hy', h1, h2⟩)
        · exact .inl h
        · rcases List.mem_cons.1 hy' with rfl | hy'
          · exact absurd h1 hc
          · exact .inr ⟨y', hy', h1, h2⟩

/-- `join` emits an entry exactly for each compatible input pair. -/
theorem mem_join {jR : S → S → S} {R c : S → S → Bool} {bot : S}
    {f g : List (S × S)} {z : S × S} :
    z ∈ join jR R c bot f g ↔
      ∃ x ∈ f, ∃ y ∈ g,
        c x.1 y.1 ∧
          z = (jR x.1 y.1, jR (app R bot f (jR x.1 y.1))
                            (app R bot g (jR x.1 y.1))) := by
  suffices H : ∀ {fl l : List (S × S)},
      z ∈ fl.foldl (init := l) (fun l x => g.foldl (init := l) fun l y =>
          if c x.1 y.1 then
            (jR x.1 y.1,
             jR (app R bot f (jR x.1 y.1)) (app R bot g (jR x.1 y.1))) :: l
          else l) ↔
        z ∈ l ∨ ∃ x ∈ fl, ∃ y ∈ g, c x.1 y.1 ∧
          z = (jR x.1 y.1,
               jR (app R bot f (jR x.1 y.1)) (app R bot g (jR x.1 y.1))) by
    simpa [join] using H (fl := f) (l := [])
  intro fl
  induction fl with
  | nil => intro l; simp
  | cons x fl ih =>
    intro l
    rw [List.foldl_cons, ih, mem_join_inner]
    constructor
    · rintro ((h | ⟨y, hy, h1, h2⟩) | ⟨x', hx', y, hy, h1, h2⟩)
      · exact .inl h
      · exact .inr ⟨x, List.mem_cons_self _ _, y, hy, h1, h2⟩
      · exact .inr ⟨x', List.mem_cons_of_mem _ hx', y, hy, h1, h2⟩
    · rintro (h | ⟨x', hx', y, hy, h1, h2⟩)
      · exact .inl (.inl h)
      · rcases List.mem_cons.1 hx' with rfl | hx'
        · exact .inl (.inr ⟨y, hy, h1, h2⟩)
        · exact .inr ⟨x', hx', y, hy, h1, h2⟩

end DShapeFun

/-! ### 5. Join unit laws, shape-level application -/

namespace DShape

/-- `bot` is a left unit for `join`. -/
theorem join_bot_l : ∀ {n} (s : DShape α n), join DShape.bot s = s := by
  intro n s
  cases n with
  | zero => cases s <;> rfl
  | succ n' =>
    show DShapeS.join DShape.join DShape.ble DShape.compat
        DShape.bot DShapeS.bot s = s
    exact DShapeS.join_bot_l s

/-- `bot` is a right unit for `join`. -/
theorem join_bot_r : ∀ {n} (s : DShape α n), join s DShape.bot = s := by
  intro n s
  cases n with
  | zero => cases s <;> rfl
  | succ n' =>
    show DShapeS.join DShape.join DShape.ble DShape.compat
        DShape.bot s DShapeS.bot = s
    exact DShapeS.join_bot_r s

/-- Semantic application: only `lam` applies; everything else is
`bot`. -/
def app : ∀ {n}, DShape α (n + 1) → DShape α n → DShape α n
  | 0 => fun _ _ => .bot
  | _ + 1 => fun s a =>
    match s with
    | .lam f => DShapeFun.app DShape.ble DShape.bot f a
    | _ => DShape.bot

theorem app_lam {n'} (f : DShapeFun α (n' + 1)) (a : DShape α (n' + 1)) :
    app (DShapeS.lam f : DShape α (n' + 2)) a =
      DShapeFun.app DShape.ble DShape.bot f a := rfl

theorem app_bot {n'} (a : DShape α (n' + 1)) :
    app (DShapeS.bot : DShape α (n' + 2)) a = DShape.bot := rfl

end DShape

/-! ### 6. Well-formed shapes, `WShape`, `TShape`

`WFfun` is the normal-form condition on step-function graphs: entries
are well-formed, and the graph is closed under compatible-input joins
in the sense that some entry `z` whose input is *equivalent* to the
joined input dominates the joined output. `HasBot` adds the
bottom-input entry that makes `f ≤ join f g` provable (every input of
`f` is compatible with `g`'s bottom entry). `WF` is the corresponding
predicate on shapes; `WShape` is the subset type, and `TShape` is the
total domain — a sigma over levels, as in §2.2.

The join/least-upper-bound and `app`-core lemmas for well-formed
shapes are the mutual `JoinSpec` package — the next item; this kit
delivers the predicate layer and the fully-proved primitive layer. -/

namespace DShapeFun

/-- Well-formedness of a graph over well-formed sub-shapes. `R` is
the sub-order, `cR` the sub-compatibility, `jR` the sub-join. -/
structure WF (wfs : S → Prop) (R cR : S → S → Bool) (jR : S → S → S)
    (f : List (S × S)) : Prop where
  entries : ∀ x ∈ f, wfs x.1 ∧ wfs x.2
  /-- Join-closure: compatible inputs `x.1`, `y.1` are realised by an
  entry `z` whose input is *equivalent* to their join and whose
  output dominates the joined output. -/
  closed : ∀ x ∈ f, ∀ y ∈ f, cR x.1 y.1 →
    ∃ z ∈ f, R (jR x.1 y.1) z.1 ∧ R z.1 (jR x.1 y.1) ∧
      R (jR x.2 y.2) z.2

/-- The bottom-entry condition: `f` has an entry whose input is
`bot`-equivalent. -/
def HasBot (bot : S) (bEq : S → S → Bool) (f : List (S × S)) : Prop :=
  ∃ x ∈ f, bEq x.1 bot ∧ bEq bot x.1

end DShapeFun

namespace DShapeS
variable {S : Type}

/-- Well-formedness at successor levels, parameterised by the
sub-shape predicate and relations. -/
def WF (wfs : S → Prop) (R cR : S → S → Bool) (jR : S → S → S)
    (botS : S) (bEq : S → S → Bool) : DShapeS α S → Prop
  | .bot | .sort _ | .unit | .nat | .zero | .neut _ => True
  | .pi a f | .sigma a f =>
    wfs a ∧ DShapeFun.WF wfs R cR jR f ∧ DShapeFun.HasBot botS bEq f
  | .lam f =>
    DShapeFun.WF wfs R cR jR f ∧ DShapeFun.HasBot botS bEq f
  | .pair a b => wfs a ∧ wfs b
  | .succ v | .reflc v => wfs v
  | .eqc A a b => wfs A ∧ wfs a ∧ wfs b

end DShapeS

namespace DShape0

/-- All level-0 shapes are well-formed. -/
def WF : DShape0 α → Prop := fun _ => True

omit [DecidableEq α] in
theorem wf : ∀ s : DShape0 α, WF s := fun _ => trivial

end DShape0

namespace DShape

/-- Well-formedness on `DShape α n`, by level recursion. -/
def WF : ∀ {n}, DShape α n → Prop
  | 0 => DShape0.WF
  | _ + 1 =>
    DShapeS.WF WF ble compat join DShape.bot ble

theorem wf_bot : ∀ {n}, WF (DShape.bot : DShape α n)
  | 0 => trivial
  | _ + 1 => trivial

end DShape

/-- The subset type of well-formed compact shapes at level `n`. -/
def WShape (α : Type) [DecidableEq α] (n : Nat) : Type :=
  { s : DShape α n // DShape.WF s }

namespace WShape
variable {n : Nat}

instance : _root_.LE (WShape α n) where
  le s t := s.1 ≤ t.1

instance : DecidableRel (α := WShape α n) (· ≤ ·) :=
  fun s t => inferInstanceAs (Decidable (DShape.ble s.1 t.1 = true))

/-- Compatibility on well-formed shapes. -/
def Compat (s t : WShape α n) : Prop := DShape.compat s.1 t.1

instance {s t : WShape α n} : Decidable (Compat s t) :=
  inferInstanceAs (Decidable (_ = true))

/-- Bottom of `WShape α n`. -/
def bot : WShape α n := ⟨DShape.bot, DShape.wf_bot⟩

theorem bot_le (s : WShape α n) : bot ≤ s := DShape.bot_le s.1

@[refl] theorem LE.refl (s : WShape α n) : s ≤ s := DShape.LE.rfl s.1

theorem LE.trans {s t u : WShape α n} : s ≤ t → t ≤ u → s ≤ u :=
  DShape.LE.trans

end WShape

/-- The total domain: well-formed compact shapes over all levels —
a sigma over the level index, as in §2.2. -/
def TShape (α : Type) [DecidableEq α] : Type := Σ n, WShape α n

namespace TShape

/-- The order on `TShape`: elements at different levels are
incomparable. -/
def LE (s t : TShape α) : Prop :=
  ∃ h : s.1 = t.1, s.2.1 ≤ cast (congrArg (DShape α) h.symm) t.2.1

/-- Compatibility on `TShape`. -/
def Compat (s t : TShape α) : Prop :=
  ∃ h : s.1 = t.1,
    DShape.CompatP s.2.1 (cast (congrArg (DShape α) h.symm) t.2.1)

theorem le_refl (s : TShape α) : LE s s := ⟨rfl, DShape.LE.rfl _⟩

theorem le_trans {s t u : TShape α} : LE s t → LE t u → LE s u := by
  rcases s with ⟨ns, xs⟩; rcases t with ⟨nt, xt⟩; rcases u with ⟨nu, xu⟩
  rintro ⟨hst, h1⟩ ⟨htu, h2⟩
  have est : ns = nt := hst
  have etu : nt = nu := htu
  subst est etu
  exact ⟨rfl, DShape.LE.trans h1 h2⟩

theorem compat_symm {s t : TShape α} : Compat s t → Compat t s := by
  rcases s with ⟨ns, xs⟩; rcases t with ⟨nt, xt⟩
  rintro ⟨hst, h⟩
  have est : ns = nt := hst
  subst est
  exact ⟨rfl, DShape.compat_symm h⟩

end TShape

/-! ### 7. Ideals, directed suprema, least fixed points (§2.3)

The compact shapes of `TShape` approximate the full domain; the
domain itself is the *ideal completion*: points are ideals —
nonempty, downward-closed, directed sets of compacts — represented
as predicates (`DPred`). In the ideal completion, directed suprema
are unions and the least fixed point of a continuous endomap is the
union of its iterates (Kleene). Everything here is choice-free:
witnesses are carried in the data, never extracted. -/

/-- Predicates on the total domain: sets of compact approximants. -/
abbrev DPred (α : Type) [DecidableEq α] : Type := TShape α → Prop

/-- Inclusion of predicates — the order of the ideal completion. -/
def PLe (P Q : DPred α) : Prop := ∀ x, P x → Q x

theorem PLe.refl (P : DPred α) : PLe P P := fun _ h => h

theorem PLe.trans {P Q R : DPred α} : PLe P Q → PLe Q R → PLe P R :=
  fun h1 h2 x hx => h2 x (h1 x hx)

/-- The empty predicate — the bottom of the predicate order. -/
def pBot : DPred α := fun _ => False

theorem PLe.bot (P : DPred α) : PLe pBot P := fun _ h => False.elim h

/-- Ideals of compacts: nonempty, downward-closed, directed sets
(§2.3) — points of the full domain, at the predicate level. -/
structure IsIdeal (P : DPred α) : Prop where
  /-- Ideals are inhabited. -/
  nonempty : ∃ x, P x
  /-- Downward closure under the `TShape` order. -/
  closed : ∀ {x y}, TShape.LE x y → P y → P x
  /-- Directedness: any two members have a common upper bound. -/
  directed : ∀ {x y}, P x → P y →
    ∃ z, P z ∧ TShape.LE x z ∧ TShape.LE y z

/-- All members of an ideal live at the same level: directedness
forces a common upper bound, and the `TShape` order only relates
equal levels. -/
theorem IsIdeal.level_eq {P : DPred α} (h : IsIdeal P)
    {s t : TShape α} (hs : P s) (ht : P t) : s.1 = t.1 := by
  obtain ⟨z, _, hsz, htz⟩ := h.directed hs ht
  exact hsz.1.trans htz.1.symm

/-- An ideal contains the bottom shape of its level. -/
theorem IsIdeal.mem_bot {P : DPred α} (h : IsIdeal P)
    {s : TShape α} (hs : P s) : P ⟨s.1, WShape.bot⟩ := by
  rcases s with ⟨n, w⟩
  exact h.closed (x := ⟨n, WShape.bot⟩) (y := ⟨n, w⟩)
    ⟨rfl, WShape.bot_le w⟩ hs

/-- The bottom ideal at level `n`: everything below `⊥ₙ`. -/
def idealBot (n : Nat) : DPred α := fun s => TShape.LE s ⟨n, WShape.bot⟩

theorem idealBot_isIdeal (n : Nat) : IsIdeal (idealBot (α := α) n) where
  nonempty := ⟨⟨n, WShape.bot⟩, TShape.le_refl _⟩
  closed := by
    intro x y hxy hx
    exact TShape.le_trans hxy hx
  directed := by
    intro x y hx hy
    exact ⟨⟨n, WShape.bot⟩, TShape.le_refl _, hx, hy⟩

/-- Union of a family of predicates — the candidate supremum. -/
def Union {ι : Type} (F : ι → DPred α) : DPred α := fun x => ∃ i, F i x

theorem Union.intro {ι : Type} {F : ι → DPred α} (i : ι) {x : TShape α}
    (h : F i x) : Union F x := ⟨i, h⟩

/-- Membership in a union is membership in some member — the
elimination form is the existential itself. -/
theorem Union.elim {ι : Type} {F : ι → DPred α} {x : TShape α}
    (h : Union F x) : ∃ i, F i x := h

/-- A family of predicates is directed when any two members sit
below a common third. -/
def Directed {ι : Type} (F : ι → DPred α) : Prop :=
  ∀ i j, ∃ k, PLe (F i) (F k) ∧ PLe (F j) (F k)

/-- Sups are unions: the union of a directed family of ideals is an
ideal (§2.3, the directed-supremum clause of the ideal completion). -/
theorem isIdeal_union {ι : Type} {F : ι → DPred α} (i₀ : ι)
    (hI : ∀ i, IsIdeal (F i)) (hD : Directed F) :
    IsIdeal (Union F) where
  nonempty := by
    obtain ⟨x, hx⟩ := (hI i₀).nonempty
    exact ⟨x, i₀, hx⟩
  closed := by
    intro x y hxy hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, (hI i).closed hxy hi⟩
  directed := by
    intro x y hx hy
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    obtain ⟨k, hik, hjk⟩ := hD i j
    obtain ⟨z, hz, hxz, hyz⟩ := (hI k).directed (hik _ hi) (hjk _ hj)
    exact ⟨z, ⟨k, hz⟩, hxz, hyz⟩

/-- The union is the least upper bound of the family: each member
is below it, and it is below every common upper bound. -/
theorem union_isLUB {ι : Type} (F : ι → DPred α) :
    (∀ i, PLe (F i) (Union F)) ∧
    ∀ Q : DPred α, (∀ i, PLe (F i) Q) → PLe (Union F) Q :=
  ⟨fun i _ h => ⟨i, h⟩,
   fun _ hQ _ h => Exists.elim h fun i hi => hQ i _ hi⟩

/-- Unions are monotone in the family. -/
theorem Union.mono {ι : Type} {F G : ι → DPred α}
    (h : ∀ i, PLe (F i) (G i)) : PLe (Union F) (Union G) :=
  fun _ hx => Exists.elim hx fun i hi => ⟨i, h i _ hi⟩

/-- `F` is monotone when it preserves predicate inclusion. -/
def Mono (F : DPred α → DPred α) : Prop :=
  ∀ {P Q}, PLe P Q → PLe (F P) (F Q)

/-- An ω-chain of predicates. -/
def IsChain (C : Nat → DPred α) : Prop := ∀ n, PLe (C n) (C (n + 1))

/-- Continuity: monotone, and preserving unions of ω-chains
(Scott continuity at the predicate level, §2.3). -/
structure IsCont (F : DPred α → DPred α) : Prop where
  /-- Preservation of the inclusion order. -/
  mono : Mono F
  /-- `F` commutes with chain suprema. -/
  union : ∀ C, IsChain C → PLe (F (Union C)) (Union fun n => F (C n))

/-- Iterates of `F` starting at the predicate `P`. -/
def iterFrom (F : DPred α → DPred α) (P : DPred α) : Nat → DPred α
  | 0 => P
  | n + 1 => F (iterFrom F P n)

theorem iterFrom_zero (F : DPred α → DPred α) (P : DPred α) :
    iterFrom F P 0 = P := rfl

theorem iterFrom_succ (F : DPred α → DPred α) (P : DPred α) (n : Nat) :
    iterFrom F P (n + 1) = F (iterFrom F P n) := rfl

/-- The iterates form an ω-chain once `P ⊆ F P` and `F` is
monotone. -/
theorem iterFrom_chain {F : DPred α → DPred α} (hF : Mono F) {P : DPred α}
    (hP : PLe P (F P)) : IsChain (iterFrom F P) := by
  intro n; induction n with
  | zero => exact hP
  | succ n ih => exact hF ih

/-- Iterates are monotone in the index. -/
theorem iterFrom_le_of_le {F : DPred α → DPred α} (hF : Mono F) {P : DPred α}
    (hP : PLe P (F P)) {m n : Nat} (hmn : m ≤ n) :
    PLe (iterFrom F P m) (iterFrom F P n) := by
  induction hmn with
  | refl => exact PLe.refl _
  | step hmn ih => exact PLe.trans ih (iterFrom_chain hF hP _)

/-- Every iterate is an ideal when `P` is and `F` preserves
ideals. -/
theorem isIdeal_iterFrom {F : DPred α → DPred α}
    (hFI : ∀ Q : DPred α, IsIdeal Q → IsIdeal (F Q))
    {P : DPred α} (hPI : IsIdeal P) :
    ∀ n, IsIdeal (iterFrom F P n)
  | 0 => hPI
  | n + 1 => hFI _ (isIdeal_iterFrom hFI hPI n)

/-- The least fixed point above `P`: the union of the iterates of
`F` starting at `P` (Kleene, §2.3). -/
def lfpFrom (F : DPred α → DPred α) (P : DPred α) : DPred α :=
  Union (iterFrom F P)

/-- Every iterate is below the union of iterates. -/
theorem iterFrom_le_lfpFrom (F : DPred α → DPred α) (P : DPred α)
    (n : Nat) : PLe (iterFrom F P n) (lfpFrom F P) :=
  fun _ h => ⟨n, h⟩

/-- The start point is below `lfpFrom`. -/
theorem lfpFrom_ge (F : DPred α → DPred α) (P : DPred α) :
    PLe P (lfpFrom F P) := fun _ h => ⟨0, h⟩

/-- Continuity makes the union of iterates a prefixed point:
`F (⋃ₙ Fⁿ P) ⊆ ⋃ₙ Fⁿ⁺¹ P ⊆ ⋃ₙ Fⁿ P`. -/
theorem lfpFrom_unfold {F : DPred α → DPred α} (hF : IsCont F) {P : DPred α}
    (hP : PLe P (F P)) : PLe (F (lfpFrom F P)) (lfpFrom F P) :=
  fun x hx => Exists.elim (hF.union _ (iterFrom_chain hF.mono hP) x hx)
    fun n hn => ⟨n + 1, hn⟩

/-- The union of iterates is below every prefixed point above `P`:
it is the *least* such. -/
theorem lfpFrom_least {F : DPred α → DPred α} (hF : Mono F) {P Q : DPred α}
    (hPQ : PLe P Q) (hQ : PLe (F Q) Q) : PLe (lfpFrom F P) Q := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have hiter : ∀ n, PLe (iterFrom F P n) Q := by
    intro n; induction n with
    | zero => exact hPQ
    | succ n ih => exact PLe.trans (hF ih) hQ
  exact hiter n x hn

/-- Kleene's theorem, relative form: `lfpFrom F P` is a genuine
fixed point of a continuous `F` when `P ⊆ F P`. -/
theorem lfpFrom_fixed {F : DPred α → DPred α} (hF : IsCont F) {P : DPred α}
    (hP : PLe P (F P)) :
    PLe (F (lfpFrom F P)) (lfpFrom F P) ∧
      PLe (lfpFrom F P) (F (lfpFrom F P)) :=
  ⟨lfpFrom_unfold hF hP,
   lfpFrom_least hF.mono
     (PLe.trans hP (hF.mono (lfpFrom_ge F P)))
     (hF.mono (lfpFrom_unfold hF hP))⟩

/-- The union of iterates from an ideal is an ideal — `lfpFrom` is
a domain element when `F` preserves ideals (§2.3). -/
theorem isIdeal_lfpFrom {F : DPred α → DPred α} (hF : IsCont F)
    (hFI : ∀ Q : DPred α, IsIdeal Q → IsIdeal (F Q)) {P : DPred α}
    (hPI : IsIdeal P) (hP : PLe P (F P)) :
    IsIdeal (lfpFrom F P) :=
  isIdeal_union 0 (isIdeal_iterFrom hFI hPI) fun i j =>
    (Nat.le_total i j).elim
      (fun h => ⟨j, iterFrom_le_of_le hF.mono hP h, PLe.refl _⟩)
      (fun h => ⟨i, PLe.refl _, iterFrom_le_of_le hF.mono hP h⟩)

/-- The iterates from the bottom predicate (the standard Kleene
sequence `Fⁿ ⊥`). -/
def iter (F : DPred α → DPred α) : Nat → DPred α := iterFrom F pBot

/-- The least fixed point outright: the union of the iterates of
`F` from the bottom predicate. -/
def lfp (F : DPred α → DPred α) : DPred α := lfpFrom F pBot

theorem iter_zero (F : DPred α → DPred α) : iter F 0 = pBot := rfl

theorem iter_succ (F : DPred α → DPred α) (n : Nat) :
    iter F (n + 1) = F (iter F n) := rfl

/-- The Kleene sequence is a chain when `F` is monotone. -/
theorem iter_chain {F : DPred α → DPred α} (hF : Mono F) : IsChain (iter F) :=
  iterFrom_chain (P := pBot) hF (fun _ h => False.elim h)

/-- Every iterate is below `lfp F`. -/
theorem iter_le_lfp (F : DPred α → DPred α) (n : Nat) :
    PLe (iter F n) (lfp F) := fun _ h => ⟨n, h⟩

/-- `lfp F` is below every prefixed point: it is the least. -/
theorem lfp_least {F : DPred α → DPred α} (hF : Mono F) {Q : DPred α} (hQ : PLe (F Q) Q) :
    PLe (lfp F) Q :=
  lfpFrom_least hF (PLe.bot Q) hQ

/-- Continuity makes `lfp F` a prefixed point. -/
theorem lfp_unfold {F : DPred α → DPred α} (hF : IsCont F) : PLe (F (lfp F)) (lfp F) :=
  lfpFrom_unfold (P := pBot) hF (fun _ h => False.elim h)

/-- Kleene's theorem: `lfp F` is a fixed point of a continuous
`F`. -/
theorem lfp_fixed {F : DPred α → DPred α} (hF : IsCont F) :
    PLe (F (lfp F)) (lfp F) ∧ PLe (lfp F) (F (lfp F)) :=
  lfpFrom_fixed (P := pBot) hF (fun _ h => False.elim h)

/-- The identity map is continuous. -/
theorem IsCont.id : IsCont ((fun P => P) : DPred α → DPred α) where
  mono := fun h => h
  union := fun _ _ _ h => h

/-- Constant maps are continuous (ω-chains are `Nat`-indexed, so
index `0` supplies the witness). -/
theorem IsCont.const (Q : DPred α) :
    IsCont ((fun _ => Q) : DPred α → DPred α) where
  mono := fun _ _ h => h
  union := fun _ _ _ h => ⟨0, h⟩

/-- Continuous maps compose. -/
theorem IsCont.comp {F G : DPred α → DPred α}
    (hF : IsCont F) (hG : IsCont G) :
    IsCont (fun P => F (G P)) where
  mono := fun h => hF.mono (hG.mono h)
  union C hC := by
    intro x hx
    have hC' : IsChain (fun n => G (C n)) := fun n => hG.mono (hC n)
    exact hF.union _ hC' x (hF.mono (hG.union C hC) x hx)

/-- The pointwise union of continuous maps is continuous. -/
theorem IsCont.union' {F G : DPred α → DPred α}
    (hF : IsCont F) (hG : IsCont G) :
    IsCont ((fun P x => F P x ∨ G P x) : DPred α → DPred α) where
  mono := fun h _ hx =>
    hx.elim (fun a => .inl (hF.mono h _ a)) (fun b => .inr (hG.mono h _ b))
  union C hC := by
    intro x hx
    cases hx with
    | inl hf =>
      obtain ⟨n, hn⟩ := hF.union C hC x hf
      exact ⟨n, .inl hn⟩
    | inr hg =>
      obtain ⟨n, hn⟩ := hG.union C hC x hg
      exact ⟨n, .inr hn⟩

/-- `F` applied `n` times to a variable predicate. -/
def iterAt (F : DPred α → DPred α) : Nat → DPred α → DPred α
  | 0 => fun P => P
  | n + 1 => fun P => F (iterAt F n P)

/-- Iterates of a continuous map are continuous. -/
theorem IsCont.iterAt {F : DPred α → DPred α} (hF : IsCont F) :
    ∀ n, IsCont (iterAt F n) := by
  intro n; induction n with
  | zero => exact IsCont.id
  | succ n ih => exact IsCont.comp (F := F) (G := Rcic.Domain.iterAt F n) hF ih

end Domain
end Rcic
