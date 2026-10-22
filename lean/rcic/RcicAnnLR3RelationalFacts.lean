import rcic.RcicAnnTyRed

/-!
# Fuel-free replacements used by the LR3 measurement

These are finite-trace lemmas, with all required relational contracts visible.
They do not choose, decide, or supply a new annotated head strategy. In particular,
the application-prefix lemma needs application inversion, and inverse weakening
needs reflected steps. Forward preservation alone is not reflection.
closure_claim = 0.
-/

namespace Rcic.Declarative.Ann.LR3Measurement

set_option autoImplicit false

universe u v

def Normal {α : Type u} (R : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬ R a b

def Deterministic {α : Type u} (R : α → α → Prop) : Prop :=
  ∀ {a b c}, R a b → R a c → b = c

inductive Trace {α : Type u} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Trace R a a
  | cons {a b c : α} (h : R a b) (t : Trace R b c) : Trace R a c

theorem Trace.eq_of_normal {α : Type u} {R : α → α → Prop} {a b : α}
    (t : Trace R a b) (hn : Normal R a) : a = b := by
  cases t with
  | refl => rfl
  | cons h _ => exact (hn _ h).elim

/-- Normal-form uniqueness uses finite traces and determinism, not fuel. -/
theorem Trace.normal_unique {α : Type u} {R : α → α → Prop}
    (hd : Deterministic R) {a b c : α}
    (t : Trace R a b) (s : Trace R a c)
    (hb : Normal R b) (hc : Normal R c) : b = c := by
  induction t generalizing c with
  | refl => exact s.eq_of_normal hb
  | cons h t ih =>
      cases s with
      | refl => exact (hc _ h).elim
      | cons h' s =>
          have e := hd h h'
          cases e
          exact ih s hb hc

/-- Iteration of a typed-step bridge uses induction on its supplied trace.
`P` carries endpoint typing; no normalizer or progress premise is introduced. -/
theorem Trace.typed {α : Type u} {R S : α → α → Prop} {P : α → Prop}
    (hs : ∀ {a b}, P a → R a b → P b ∧ S a b)
    {a b : α} (t : Trace R a b) (ha : P a) : P b ∧ Trace S a b := by
  induction t with
  | refl => exact ⟨ha, .refl _⟩
  | cons h t ih =>
      obtain ⟨hb, hS⟩ := hs ha h
      obtain ⟨hc, tS⟩ := ih hb
      exact ⟨hc, .cons hS tS⟩

/-- The `piHeadPrefix` replacement. Its two inversion contracts are exactly
what is needed to extract a function's normalizing prefix from an application.
The proof never asks whether an arbitrary head has a successor. -/
theorem Trace.application_prefix {α : Type u} {R : α → α → Prop}
    (app : α → α → α)
    (stepInv : ∀ {f x y}, R (app f x) y →
      Normal R f ∨ ∃ g, R f g ∧ y = app g x)
    (normalInv : ∀ {f x}, Normal R (app f x) → Normal R f)
    {a z : α} (t : Trace R a z) (hz : Normal R z) :
    ∀ {f x}, a = app f x → ∃ g, Trace R f g ∧ Normal R g := by
  induction t with
  | refl =>
      intro f x e
      subst e
      exact ⟨f, .refl f, normalInv hz⟩
  | cons h t ih =>
      intro f x e
      subst e
      rcases stepInv h with hn | ⟨g, hg, e⟩
      · exact ⟨f, .refl f, hn⟩
      · obtain ⟨g', tg, hn⟩ := ih hz e
        exact ⟨g', .cons hg tg, hn⟩

/-- Reflected steps preserve normality under a map. This is the extra contract
needed for weakening; forward preservation alone has the opposite direction. -/
theorem normal_map_of_reflection {α : Type u} {β : Type v}
    {R : α → α → Prop} {S : β → β → Prop} (f : α → β)
    (back : ∀ {a z}, S (f a) z → ∃ b, z = f b ∧ R a b)
    {a : α} (ha : Normal R a) : Normal S (f a) := by
  intro z hz
  obtain ⟨b, _, hb⟩ := back hz
  exact ha b hb

/-- A finite normalizing trace can be reflected through weakening, provided
steps reflect and source steps are preserved. No inverse is chosen globally. -/
theorem Trace.reflect_normal {α : Type u} {β : Type v}
    {R : α → α → Prop} {S : β → β → Prop} (f : α → β)
    (forward : ∀ {a b}, R a b → S (f a) (f b))
    (back : ∀ {a z}, S (f a) z → ∃ b, z = f b ∧ R a b)
    {y z : β} (t : Trace S y z) (hz : Normal S z) :
    ∀ {a}, y = f a → ∃ b, z = f b ∧ Trace R a b ∧ Normal R b := by
  induction t with
  | refl =>
      intro a e
      subst e
      exact ⟨a, rfl, .refl a, fun b hb => hz (f b) (forward hb)⟩
  | cons h t ih =>
      intro a e
      subst e
      obtain ⟨b, eb, hb⟩ := back h
      obtain ⟨c, ec, tc, hc⟩ := ih hz eb
      exact ⟨c, ec, .cons hb tc, hc⟩

#print axioms Trace.normal_unique
#print axioms Trace.typed
#print axioms Trace.application_prefix
#print axioms normal_map_of_reflection
#print axioms Trace.reflect_normal

end Rcic.Declarative.Ann.LR3Measurement
