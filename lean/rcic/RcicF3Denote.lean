import rcic.RcicF3Small
import rcic.RcicLevelDec

/-!
# F3 S2: the raw denotation of R-CIC expressions

Values live in one carrier `PSet.{T}`. The encoding (F3 plan, D1):

- every proof denotes `∅` (`pempty`);
- a type denotes a tagged pair `tyv S = ⟨{∅}, S⟩`, so no type value is `∅`;
  `El t` extracts the element set (`el_tyv`);
- `sort l` denotes `tyv (U (evalTotal σ l))`, where `U k` is the set of
  types of level `k` supplied by the universe stages;
- `pi A B` denotes the truth value `[∀ x ∈ El A, ∅ ∈ El (B x)]` when every
  fibre's elements are all `∅` (a proposition), and the dependent product of
  the fibres otherwise;
- `lam A b` denotes `∅` when the body is `∅` at every element of `El A` (a
  proof), and the graph of the body otherwise; application is graph
  application (`fapp ∅ a = ∅`, so proofs stay proofs);
- element sets are read through `Ed`, which normalizes `El t` to `∅` unless
  it is dichotomous (all elements `∅`, or none), so the two tests agree
  without regularity or unique typing.

The two tests are classical: `den` takes a decision procedure `dec` as a
parameter (a premise of the final theorem, never an axiom). Unique typing is
not used. `den_congr`: the denotation respects `≈` in the environment.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-! ## Congruence of the set combinators (ported from R1-b) -/

/-- `sImage` congruence: pointwise `≈` on elements. -/
theorem sImage_congr {h h' : PSet.{T} → PSet.{T}} {s s' : PSet.{T}}
    (hh : ∀ a a', Equiv a a' → Equiv (h a) (h' a')) (hs : Equiv s s') :
    Equiv (sImage h s) (sImage h' s') := by
  apply ext; intro x; constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hs.exists_mem_left i
    exact ⟨j, (hh _ _ hj).symm.trans hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hs.exists_mem_right i
    exact ⟨j, (hh _ _ hj).trans hi⟩

/-- `sep` congruence: predicate transports along `≈`. -/
theorem sep_congr {p p' : PSet.{T} → Prop} {s s' : PSet.{T}}
    (hp : ∀ a b, Equiv a b → (p a → p' b))
    (hp' : ∀ a b, Equiv a b → (p' a → p b))
    (hs : Equiv s s') :
    Equiv (sep p s) (sep p' s') := by
  apply ext; intro x; constructor
  · intro hx
    obtain ⟨i, hpi, hix⟩ := mem_sep.mp hx
    obtain ⟨j, hj⟩ := hs.exists_mem_left i
    exact mem_sep.mpr ⟨j, hp _ _ hj hpi, hj.symm.trans hix⟩
  · intro hx
    obtain ⟨i, hpi, hix⟩ := mem_sep.mp hx
    obtain ⟨j, hj⟩ := hs.exists_mem_right i
    exact mem_sep.mpr ⟨j, hp' _ _ hj.symm hpi, hj.trans hix⟩

/-- `fapp` congruence. -/
theorem fapp_congr {F F' a a' : PSet.{T}}
    (hF : Equiv F F') (ha : Equiv a a') :
    Equiv (fapp F a) (fapp F' a') :=
  sUnion_congr (sep_congr
    (fun _ _ hb hab =>
      mem_congr_right hF (mem_congr_left (ordPair_congr ha hb) hab))
    (fun _ _ hb hab =>
      mem_congr_right hF.symm
        (mem_congr_left (ordPair_congr ha.symm hb) hab))
    (sUnion_congr (sUnion_congr hF)))

/-- `mkLam` congruence. -/
theorem mkLam_congr {g g' : PSet.{T} → PSet.{T}} {A A' : PSet.{T}}
    (hg : ∀ a a', Equiv a a' → Equiv (g a) (g' a')) (hA : Equiv A A') :
    Equiv (mkLam g A) (mkLam g' A') :=
  sImage_congr (fun _ _ h => ordPair_congr h (hg _ _ h)) hA

/-- `isFuncOnDep` transports along `≈`. -/
theorem isFuncOnDep_equiv {A A' : PSet.{T}} {B B' : PSet.{T} → PSet.{T}} {g g' : PSet.{T}}
    (hA : Equiv A A') (hB : ∀ a a', Equiv a a' → Equiv (B a) (B' a'))
    (hg : Equiv g g')
    (h : isFuncOnDep A B g) : isFuncOnDep A' B' g' := by
  obtain ⟨hdom, hcod, huniq⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, hab⟩ := hdom a (mem_congr_right hA.symm ha)
    exact ⟨b, mem_congr_right (hB _ _ Equiv.rfl) hb,
      mem_congr_right hg hab⟩
  · intro p hp
    obtain ⟨a, ha, b, hb, hp'⟩ := hcod p (mem_congr_right hg.symm hp)
    exact ⟨a, mem_congr_right hA ha, b,
      mem_congr_right (hB _ _ Equiv.rfl) hb, hp'⟩
  · intro a b b' h1 h2
    exact huniq a b b' (mem_congr_right hg.symm h1)
      (mem_congr_right hg.symm h2)

/-- `piSet` congruence. -/
theorem piSet_congr {A A' : PSet.{T}} {B B' : PSet.{T} → PSet.{T}}
    (hA : Equiv A A') (hB : ∀ a a', Equiv a a' → Equiv (B a) (B' a')) :
    Equiv (piSet A B) (piSet A' B') :=
  sep_congr
    (fun _ _ haa' h => isFuncOnDep_equiv hA hB haa' h)
    (fun _ _ haa' h =>
      isFuncOnDep_equiv hA.symm
        (fun a a' he => (hB a' a he.symm).symm) haa' h)
    (powerset_congr (prod_congr hA
      (sUnion_congr (sImage_congr hB hA))))


/-- The tag of a type value. -/
def tyTag : PSet.{T} := singleton pempty

/-- A type value: its element set, tagged. -/
def tyv (S : PSet.{T}) : PSet.{T} := ordPair tyTag S

/-- The element set of a type value. -/
def El (t : PSet.{T}) : PSet.{T} :=
  sUnion (sep (fun z => Equiv t (ordPair tyTag z)) (sUnion t))

theorem el_tyv {S : PSet.{T}} : Equiv (El (tyv S)) S := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨t, ht, hz'⟩ := mem_sUnion.mp hz
    obtain ⟨⟨i, hi⟩, ht'⟩ := ht
    obtain ⟨_, hw⟩ := ordPair_equiv hi
    exact mem_congr_right (ht'.symm.trans hw.symm) hz'
  · intro hz
    have hS : S ∈ sUnion (tyv S) :=
      mem_sUnion.mpr ⟨pair tyTag S, mem_pair.mpr (Or.inr Equiv.rfl), mem_pair.mpr (Or.inr Equiv.rfl)⟩
    obtain ⟨i, hi⟩ := hS
    have hQ : Equiv (tyv S) (ordPair tyTag ((sUnion (tyv S)).Func i)) :=
      (ordPair_congr Equiv.rfl hi).symm
    exact mem_sUnion.mpr ⟨(sUnion (tyv S)).Func i, ⟨⟨i, hQ⟩, Equiv.refl _⟩, mem_congr_right hi.symm hz⟩

theorem el_congr {t t' : PSet.{T}} (h : Equiv t t') : Equiv (El t) (El t') := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨w, hw, hzw⟩ := mem_sUnion.mp hz
    obtain ⟨i, hp, hi⟩ := mem_sep.mp hw
    have hmem : (sUnion t).Func i ∈ sUnion t' := mem_congr_right (sUnion_congr h) ⟨i, Equiv.refl _⟩
    obtain ⟨j, hj⟩ := hmem
    refine mem_sUnion.mpr ⟨(sUnion t').Func j, mem_sep.mpr ⟨j, ?_, Equiv.refl _⟩,
      mem_congr_right (hi.symm.trans hj.symm) hzw⟩
    exact h.symm.trans (hp.trans (ordPair_congr Equiv.rfl hj.symm))
  · intro hz
    obtain ⟨w, hw, hzw⟩ := mem_sUnion.mp hz
    obtain ⟨i, hp, hi⟩ := mem_sep.mp hw
    have hmem : (sUnion t').Func i ∈ sUnion t := mem_congr_right (sUnion_congr h.symm) ⟨i, Equiv.refl _⟩
    obtain ⟨j, hj⟩ := hmem
    refine mem_sUnion.mpr ⟨(sUnion t).Func j, mem_sep.mpr ⟨j, ?_, Equiv.refl _⟩,
      mem_congr_right (hi.symm.trans hj.symm) hzw⟩
    exact h.trans (hp.trans (ordPair_congr Equiv.rfl hj.symm))

theorem tyv_congr {S S' : PSet.{T}} (h : Equiv S S') : Equiv (tyv S) (tyv S') :=
  ordPair_congr Equiv.rfl h

/-- The truth value of a proposition: `{∅}` if it holds, `∅` otherwise. -/
def tv (φ : Prop) : PSet.{T} := sep (fun _ => φ) (singleton pempty)

theorem mem_tv {φ : Prop} {z : PSet.{T}} : z ∈ tv φ ↔ φ ∧ Equiv z pempty := by
  constructor
  · intro h
    obtain ⟨i, hp, hi⟩ := mem_sep.mp h
    exact ⟨hp, hi.symm⟩
  · rintro ⟨hp, hz⟩
    exact mem_sep.mpr ⟨PUnit.unit, hp, hz.symm⟩

/-- A classical conditional, from a decision procedure. -/
def cond (dec : ∀ p : Prop, Decidable p) (c : Prop) (a b : PSet.{T}) : PSet.{T} :=
  @ite _ c (dec c) a b

theorem cond_pos {dec : ∀ p : Prop, Decidable p} {c : Prop} (h : c) (a b : PSet.{T}) :
    cond dec c a b = a := @if_pos _ (dec c) h _ a b

theorem cond_neg {dec : ∀ p : Prop, Decidable p} {c : Prop} (h : ¬ c) (a b : PSet.{T}) :
    cond dec c a b = b := @if_neg _ (dec c) h _ a b

theorem cond_congr {dec : ∀ p : Prop, Decidable p} {c c' : Prop} (hc : c ↔ c') {a a' b b' : PSet.{T}}
    (ha : Equiv a a') (hb : Equiv b b') : Equiv (cond dec c a b) (cond dec c' a' b') := by
  have e : c = c' := propext hc
  subst e
  by_cases h : c
  · rw [cond_pos h, cond_pos h]; exact ha
  · rw [cond_neg h, cond_neg h]; exact hb

/-- Push a value under a binder. -/
def vcons (x : PSet.{T}) (ρ : Nat → PSet.{T}) : Nat → PSet.{T}
  | 0 => x
  | i + 1 => ρ i

/-- The model data the denotation is parametric in: the decision
procedure, the universe stages (the set of types of each level) and the
interpretation of environment constants. -/
structure Interp where
  dec : ∀ p : Prop, Decidable p
  U : Nat → PSet.{T}
  μ : Nat → List Nat → PSet.{T}

/-- Dichotomy: all elements are `∅` (a proposition's proofs), or none is. -/
def Dich (S : PSet.{T}) : Prop := (∀ y, y ∈ S → Equiv y pempty) ∨ ¬ pempty ∈ S

/-- The element set of a type value, normalized to be dichotomous. -/
def Ed (M : Interp.{T}) (t : PSet.{T}) : PSet.{T} := cond M.dec (Dich (El t)) (El t) pempty

/-- The proposition test for a product: every element of every fibre is `∅`. -/
def PiProp (M : Interp.{T}) (A : PSet.{T}) (B : PSet.{T} → PSet.{T}) : Prop :=
  ∀ x, x ∈ Ed M A → ∀ y, y ∈ Ed M (B x) → Equiv y pempty

/-- The proof test for an abstraction: the body is `∅` at every element. -/
def LamProof (M : Interp.{T}) (A : PSet.{T}) (b : PSet.{T} → PSet.{T}) : Prop :=
  ∀ x, x ∈ Ed M A → Equiv (b x) pempty

def piVal (M : Interp.{T}) (A : PSet.{T}) (B : PSet.{T} → PSet.{T}) : PSet.{T} :=
  tyv (cond M.dec (PiProp M A B) (tv (∀ x, x ∈ Ed M A → pempty ∈ Ed M (B x)))
    (piSet (Ed M A) (fun x => Ed M (B x))))

def lamVal (M : Interp.{T}) (A : PSet.{T}) (b : PSet.{T} → PSet.{T}) : PSet.{T} :=
  cond M.dec (LamProof M A b) pempty (mkLam b (Ed M A))

/-- The denotation of a literal: `natExpand` unfolded through `μ 1` / `μ 2`. -/
def denLit (M : Interp.{T}) : Nat → PSet.{T}
  | 0 => M.μ 1 []
  | n + 1 => fapp (M.μ 2 []) (denLit M n)

/-- The denotation, at a level valuation `σ` and an environment `ρ`. -/
def den (M : Interp.{T}) (σ : Nat → Nat) : (Nat → PSet.{T}) → Expr Nat → PSet.{T}
  | ρ, .bvar i => ρ i
  | _, .sort l => tyv (M.U (evalTotal σ l))
  | _, .const r ls => M.μ r (ls.map (evalTotal σ))
  | ρ, .app f a => fapp (den M σ ρ f) (den M σ ρ a)
  | ρ, .lam A b => lamVal M (den M σ ρ A) (fun x => den M σ (vcons x ρ) b)
  | ρ, .pi A B => piVal M (den M σ ρ A) (fun x => den M σ (vcons x ρ) B)
  | ρ, .letE _ v b => den M σ (vcons (den M σ ρ v) ρ) b
  | _, .lit t => denLit M t

theorem den_natExpand (M : Interp.{T}) (σ : Nat → Nat) (ρ : Nat → PSet.{T}) :
    ∀ t, den M σ ρ (natExpand t) = denLit M t
  | 0 => rfl
  | n + 1 => by
      show fapp (den M σ ρ (.const 2 [])) (den M σ ρ (natExpand n)) = _
      rw [den_natExpand M σ ρ n]
      rfl

theorem vcons_congr {x x' : PSet.{T}} {ρ ρ' : Nat → PSet.{T}} (hx : Equiv x x')
    (hρ : ∀ i, Equiv (ρ i) (ρ' i)) : ∀ i, Equiv (vcons x ρ i) (vcons x' ρ' i)
  | 0 => hx
  | i + 1 => hρ i

theorem dich_congr {S S' : PSet.{T}} (h : Equiv S S') : Dich S ↔ Dich S' := by
  constructor
  · rintro (h1 | h1)
    · exact Or.inl fun y hy => h1 y (mem_congr_right h.symm hy)
    · exact Or.inr fun h2 => h1 (mem_congr_right h.symm h2)
  · rintro (h1 | h1)
    · exact Or.inl fun y hy => h1 y (mem_congr_right h hy)
    · exact Or.inr fun h2 => h1 (mem_congr_right h h2)

theorem ed_congr (M : Interp.{T}) {t t' : PSet.{T}} (h : Equiv t t') : Equiv (Ed M t) (Ed M t') :=
  cond_congr (dich_congr (el_congr h)) (el_congr h) Equiv.rfl

theorem piVal_congr (M : Interp.{T}) {A A' : PSet.{T}} {B B' : PSet.{T} → PSet.{T}}
    (hA : Equiv A A') (hB : ∀ x x', Equiv x x' → Equiv (B x) (B' x')) :
    Equiv (piVal M A B) (piVal M A' B') := by
  have eA := ed_congr M hA
  have eB : ∀ x x', Equiv x x' → Equiv (Ed M (B x)) (Ed M (B' x')) := fun x x' h => ed_congr M (hB x x' h)
  refine tyv_congr (cond_congr ?_ ?_ (piSet_congr eA eB))
  · constructor
    · intro h x hx y hy
      have hx' := mem_congr_right eA.symm hx
      exact h x hx' y (mem_congr_right (eB x x Equiv.rfl).symm hy)
    · intro h x hx y hy
      have hx' := mem_congr_right eA hx
      exact h x hx' y (mem_congr_right (eB x x Equiv.rfl) hy)
  · refine ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
    · obtain ⟨hφ, hz⟩ := mem_tv.mp hz
      exact mem_tv.mpr ⟨fun x hx => mem_congr_right (eB x x Equiv.rfl)
        (hφ x (mem_congr_right eA.symm hx)), hz⟩
    · obtain ⟨hφ, hz⟩ := mem_tv.mp hz
      exact mem_tv.mpr ⟨fun x hx => mem_congr_right (eB x x Equiv.rfl).symm
        (hφ x (mem_congr_right eA hx)), hz⟩

theorem lamVal_congr (M : Interp.{T}) {A A' : PSet.{T}} {b b' : PSet.{T} → PSet.{T}}
    (hA : Equiv A A') (hb : ∀ x x', Equiv x x' → Equiv (b x) (b' x')) :
    Equiv (lamVal M A b) (lamVal M A' b') := by
  have eA := ed_congr M hA
  refine cond_congr ⟨fun h x hx => ?_, fun h x hx => ?_⟩ Equiv.rfl (mkLam_congr hb eA)
  · exact (hb x x Equiv.rfl).symm.trans (h x (mem_congr_right eA.symm hx))
  · exact (hb x x Equiv.rfl).trans (h x (mem_congr_right eA hx))

/-- The denotation respects `≈` in the environment. -/
theorem den_congr (M : Interp.{T}) (σ : Nat → Nat) :
    (e : Expr Nat) → ∀ {ρ ρ' : Nat → PSet.{T}}, (∀ i, Equiv (ρ i) (ρ' i)) →
      Equiv (den M σ ρ e) (den M σ ρ' e)
  | .bvar i, _, _, h => h i
  | .sort _, _, _, _ => Equiv.rfl
  | .const _ _, _, _, _ => Equiv.rfl
  | .app f a, _, _, h => fapp_congr (den_congr M σ f h) (den_congr M σ a h)
  | .lam A b, _, _, h => lamVal_congr M (den_congr M σ A h)
      (fun _ _ hx => den_congr M σ b (vcons_congr hx h))
  | .pi A B, _, _, h => piVal_congr M (den_congr M σ A h)
      (fun _ _ hx => den_congr M σ B (vcons_congr hx h))
  | .letE _ v b, _, _, h => den_congr M σ b (vcons_congr (den_congr M σ v h) h)
  | .lit _, _, _, _ => Equiv.rfl

/-- Drop `k` leading bindings. -/
def shiftρ (k : Nat) (ρ : Nat → PSet.{T}) (i : Nat) : PSet.{T} := ρ (i + k)

/-- `ρ[j ↦ a]` with reindexing — the `instantiate` environment. -/
def insρ (j : Nat) (a : PSet.{T}) (ρ : Nat → PSet.{T}) (i : Nat) : PSet.{T} :=
  if i = j then a else if j < i then ρ (i - 1) else ρ i

/-! ### Assignment algebra -/

/-- The `lift` assignment: `lift k j e` read at `ρ` is `e` read at
`liftρ k j ρ` (positions ≥ `k` shifted by `j`). -/
def liftρ (k j : Nat) (ρ : Nat → PSet.{T}) (i : Nat) : PSet.{T} :=
  if i < k then ρ i else ρ (i + j)

/-- `liftρ 0 j` is `shiftρ j`. -/
theorem liftρ_zero (j : Nat) (ρ : Nat → PSet.{T}) :
    liftρ 0 j ρ = shiftρ j ρ :=
  funext fun i => if_neg (Nat.not_lt_zero i)

/-- `liftρ` commutes with `vcons`. -/
theorem liftρ_cons (k j : Nat) (a : PSet.{T}) (ρ : Nat → PSet.{T}) :
    liftρ (k + 1) j (vcons a ρ) = vcons a (liftρ k j ρ) := by
  funext i; cases i with
  | zero =>
    show (if 0 < k + 1 then vcons a ρ 0 else vcons a ρ (0 + j)) = _
    rw [if_pos (Nat.zero_lt_succ k)]; rfl
  | succ i =>
    show (if i + 1 < k + 1 then vcons a ρ (i + 1) else
        vcons a ρ (i + 1 + j)) = (if i < k then ρ i else ρ (i + j))
    by_cases h : i + 1 < k + 1
    · rw [if_pos h, if_pos (Nat.lt_of_succ_lt_succ h)]; rfl
    · rw [if_neg h, if_neg (fun hc => h (Nat.succ_lt_succ hc))]
      show vcons a ρ (i + 1 + j) = ρ (i + j)
      rw [Nat.add_comm (i + 1) j, Nat.add_one, Nat.add_succ,
        Nat.add_comm j i]; rfl

/-- `insρ` commutes with `vcons` (index pushed past the binder). -/
theorem insρ_succ_cons (j : Nat) (a v : PSet.{T}) (ρ : Nat → PSet.{T}) :
    insρ (j + 1) a (vcons v ρ) = vcons v (insρ j a ρ) := by
  funext i; cases i with
  | zero =>
    show (if 0 = j + 1 then a else if j + 1 < 0 then
        vcons v ρ (0 - 1) else vcons v ρ 0) = v
    rw [if_neg (Ne.symm (Nat.succ_ne_zero j)),
        if_neg (Nat.not_lt_zero _)]; rfl
  | succ i =>
    show (if i + 1 = j + 1 then a else if j + 1 < i + 1 then
        vcons v ρ (i + 1 - 1) else vcons v ρ (i + 1)) =
        (if i = j then a else if j < i then ρ (i - 1) else ρ i)
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (mt Nat.add_right_cancel hij), if_neg hij]
      by_cases hji : j < i
      · rw [if_pos (Nat.succ_lt_succ hji), if_pos hji]
        cases i with
        | zero => exact absurd hji (Nat.not_lt_zero j)
        | succ i => rfl
      · rw [if_neg (mt Nat.lt_of_succ_lt_succ hji), if_neg hji]; rfl

/-- `shiftρ` at zero is the identity. -/
theorem shiftρ_zero (ρ : Nat → PSet.{T}) : shiftρ 0 ρ = ρ := rfl

/-- `shiftρ` past a `vcons` drops the cons. -/
theorem shiftρ_succ_cons (k : Nat) (a : PSet.{T}) (ρ : Nat → PSet.{T}) :
    shiftρ (k + 1) (vcons a ρ) = shiftρ k ρ := rfl

/-! ### `den` commutation lemmas -/

/-- `evalTotal` commutes with `lvlSubst` (the total-evaluator form
of `eval_lvlSubst`). -/
theorem evalTotal_lvlSubst (σ : Nat → Nat)
    (τ : Level → Level) (l : Level) :
    evalTotal σ (lvlSubst τ l) =
      evalTotal
        (fun i => evalTotal σ (τ (.param i))) l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [lvlSubst, evalTotal, ih]
  | max a b iha ihb =>
      simp only [lvlSubst, evalTotal, iha, ihb]
  | imax a b iha ihb =>
      simp only [lvlSubst, evalTotal, iha, ihb]
  | param i => rfl

/-- Level evaluation commutes with `instLevel`. -/
theorem evalTotal_instLevel (σ : Nat → Nat) (ls : List Level)
    (l : Level) :
    evalTotal σ (instLevel ls l) =
      evalTotal
        (fun i => ((ls.map (evalTotal σ))[i]?).getD (σ i)) l := by
  show evalTotal σ
      (lvlSubst (levelParamSubst ls) l) = _
  rw [evalTotal_lvlSubst]
  congr 1
  funext i
  show evalTotal σ ((ls[i]?).getD (.param i)) =
      ((ls.map (evalTotal σ))[i]?).getD (σ i)
  rw [List.getElem?_map]
  cases h : ls[i]? with
  | none => rfl
  | some l' => rfl

/-- `vcons` then `shiftρ 1` collapses to the tail. -/
theorem shiftρ_one_cons (a : PSet.{T}) (ρ : Nat → PSet.{T}) :
    shiftρ 1 (vcons a ρ) = ρ :=
  funext fun _ => rfl

/-- `den` commutes with `lift` via `liftρ`. -/
theorem den_lift (M : Interp.{T}) (σ : Nat → Nat)
    (e : Expr Nat) :
    ∀ {ρ : Nat → PSet.{T}} {k j : Nat},
      den M σ ρ (Rcic.Declarative.lift k j e) =
        den M σ (liftρ k j ρ) e := by
  induction e with
  | bvar i =>
    intro ρ k j
    show den M σ ρ (ite (k ≤ i) (.bvar (i + j)) (.bvar i)) = _
    by_cases h : k ≤ i
    · rw [if_pos h]
      show ρ (i + j) = (if i < k then ρ i else ρ (i + j))
      rw [if_neg (Nat.not_lt_of_le h)]
    · rw [if_neg h]
      show ρ i = (if i < k then ρ i else ρ (i + j))
      rw [if_pos (Nat.lt_of_not_le h)]
  | sort l => intro _ _ _; rfl
  | const r ms => intro _ _ _; rfl
  | lit t => intro _ _ _; rfl
  | app f x ihf ihx =>
    intro _ _ _
    simp only [Rcic.Declarative.lift, den, ihf, ihx]
  | lam A b ihA ihb =>
    intro _ _ _
    simp only [Rcic.Declarative.lift, den, ihA, ihb, liftρ_cons]
  | pi A B ihA ihB =>
    intro _ _ _
    simp only [Rcic.Declarative.lift, den, ihA, ihB, liftρ_cons]
  | letE _ v b _ ihv ihb =>
    intro _ _ _
    simp only [Rcic.Declarative.lift, den, ihv, ihb, liftρ_cons]

/-- `den` commutes with `instantiate` via `insρ`. -/
theorem den_instantiate (M : Interp.{T}) (σ : Nat → Nat)
    (e : Expr Nat) :
    ∀ {ρ : Nat → PSet.{T}} {j : Nat} {rep : Expr Nat},
      den M σ ρ (instantiate j rep e) =
        den M σ (insρ j (den M σ ρ rep) ρ) e := by
  induction e with
  | bvar i =>
    intro ρ j rep
    show den M σ ρ (ite (i = j) rep
        (ite (j < i) (.bvar (i - 1)) (.bvar i))) =
        insρ j (den M σ ρ rep) ρ i
    by_cases hij : i = j
    · rw [if_pos hij]
      show den M σ ρ rep = (if i = j then den M σ ρ rep
          else if j < i then ρ (i - 1) else ρ i)
      rw [if_pos hij]
    · rw [if_neg hij]
      by_cases hji : j < i
      · rw [if_pos hji]
        show ρ (i - 1) = (if i = j then den M σ ρ rep
            else if j < i then ρ (i - 1) else ρ i)
        rw [if_neg hij, if_pos hji]
      · rw [if_neg hji]
        show ρ i = (if i = j then den M σ ρ rep
            else if j < i then ρ (i - 1) else ρ i)
        rw [if_neg hij, if_neg hji]
  | sort l => intro _ _ _; rfl
  | const r ms => intro _ _ _; rfl
  | lit t => intro _ _ _; rfl
  | app f x ihf ihx =>
    intro _ _ _
    simp only [instantiate, den, ihf, ihx]
  | lam A b ihA ihb =>
    intro ρ j rep
    have hrep : ∀ x : PSet.{T},
        den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 rep) =
          den M σ ρ rep := by
      intro x
      rw [den_lift, liftρ_zero, shiftρ_one_cons]
    simp only [instantiate, den, ihA, ihb, hrep,
      insρ_succ_cons]
  | pi A B ihA ihB =>
    intro ρ j rep
    have hrep : ∀ x : PSet.{T},
        den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 rep) =
          den M σ ρ rep := by
      intro x
      rw [den_lift, liftρ_zero, shiftρ_one_cons]
    simp only [instantiate, den, ihA, ihB, hrep,
      insρ_succ_cons]
  | letE _ v b _ ihv ihb =>
    intro ρ j rep
    have hrep : ∀ x : PSet.{T},
        den M σ (vcons x ρ) (Rcic.Declarative.lift 0 1 rep) =
          den M σ ρ rep := by
      intro x
      rw [den_lift, liftρ_zero, shiftρ_one_cons]
    simp only [instantiate, den, ihv, ihb, hrep,
      insρ_succ_cons]

/-- `den` commutes with `instantiateLevels` via `evalTotal_instLevel`. -/
theorem den_instantiateLevels (M : Interp.{T}) (σ : Nat → Nat)
    (e : Expr Nat) :
    ∀ {ρ : Nat → PSet.{T}} (ls : List Level),
      den M σ ρ (instantiateLevels ls e) =
        den M (fun i =>
          ((ls.map (evalTotal σ))[i]?).getD (σ i)) ρ e := by
  induction e with
  | bvar i => intro _ _; rfl
  | lit t => intro _ _; rfl
  | sort l =>
    intro ρ ls
    simp only [instantiateLevels, den, evalTotal_instLevel]
  | const r ms =>
    intro ρ ls
    simp only [instantiateLevels, den]
    congr 1
    induction ms with
    | nil => rfl
    | cons m ms ih =>
      simp only [List.map_cons, Function.comp, evalTotal_instLevel, ih]
  | app f x ihf ihx =>
    intro _ _
    simp only [instantiateLevels, den, ihf, ihx]
  | lam A b ihA ihb =>
    intro _ _
    simp only [instantiateLevels, den, ihA, ihb]
  | pi A B ihA ihB =>
    intro _ _
    simp only [instantiateLevels, den, ihA, ihB]
  | letE _ v b _ ihv ihb =>
    intro _ _
    simp only [instantiateLevels, den, ihv, ihb]

end PSet

end Rcic.F3
