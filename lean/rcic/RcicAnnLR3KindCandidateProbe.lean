import rcic.RcicAnnLR3CandidateCodeSystem

/-!
# Probe R8: kind-indexed candidates (Werner 1994, ch. 4) in Type 0

Type-level computation (`F A : Sort`, term-dependent fibres) needs
candidates for predicates, not only for types. This module tests the
standard recipe in our setting. Raw values play the role of Werner's untyped
pure terms.

- **Kinds are data.** `Kind` is a plain inductive (`star`, `arrT K` for a
  family over realizers, `arrK K₁ K₂` for a family over candidates), with
  decidable equality. Its domains are kept apart in `Dom K`, so a kind does
  not carry a relation.
- **Candidate spaces by structural recursion.** `CR : Kind → Type` is
  `Relation` at `star`, `Value → CR K` at `arrT K` and `CR K₁ → CR K₂` at
  `arrK K₁ K₂`. Everything lives in `Type 0` and unfolds by `rfl`
  (`cr_star`, `cr_arrT`, `cr_arrK`).
- **Invariance is part of what a candidate is.** `Inv K d` relates
  candidates. At `star` it means both are saturated and they are the same
  relation. At `arrT` it means related realizers (by the domain relation)
  go to invariant candidates. At `arrK` it means invariant arguments go to
  invariant results. `inv_laws`: `Inv K d` is a PER whenever the domain
  relations are PERs.
- **Nonemptiness without choice.** `can K` is defined by recursion on the
  kind and is invariant (`can_inv`).
- **Impredicative quantification at every kind.** `allRel K d B` intersects
  `B C` over the invariant candidates `C` of kind `K`. It is saturated when
  every `B C` is (`all_sat`); `can K` supplies the bottom observation.
- **Term-dependent fibres respect the domain** (`fibre_respect`). An
  invariant family `C : Value → Relation` gives the same relation at related
  realizers. This is CR3 for dependent fibres, and here it holds by
  construction, not as a later lemma. Leibniz transport follows
  (`leibniz_transport`): whatever realizes `∀ P : A → Prop, P x → P x`
  realizes `∀ P : A → Prop, P x → P y` when `x` and `y` are related in `A`.
- **Mutant.** Invariance is load-bearing: a family that is saturated at
  every point but not invariant (`badFamily`) gives different relations at
  two related realizers (`badFamily_not_inv`).

Not covered: the interpretation of type expressions into `CR K` over a
kind-heterogeneous candidate environment, strong elimination as a least
fixed point, and the link to evaluator images. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.KindCandidateProbe

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open CandidateTowerProbe (Sat)
open CandidateCodeSystem (botRel botRel_sat)

inductive Kind where
  | star : Kind
  | arrT : Kind → Kind
  | arrK : Kind → Kind → Kind
  deriving DecidableEq

/-- Candidate spaces, by structural recursion on the kind. -/
def CR : Kind → Type
  | .star => Relation
  | .arrT K => Value → CR K
  | .arrK K₁ K₂ => CR K₁ → CR K₂

theorem cr_star : CR .star = Relation := rfl
theorem cr_arrT (K : Kind) : CR (.arrT K) = (Value → CR K) := rfl
theorem cr_arrK (K₁ K₂ : Kind) : CR (.arrK K₁ K₂) = (CR K₁ → CR K₂) := rfl

/-- Domain relations of a kind, kept apart from the kind itself. -/
def Dom : Kind → Type
  | .star => Unit
  | .arrT K => Relation × Dom K
  | .arrK K₁ K₂ => Dom K₁ × Dom K₂

def DomWf : (K : Kind) → Dom K → Prop
  | .star, _ => True
  | .arrT K, d => Laws d.1 ∧ DomWf K d.2
  | .arrK K₁ K₂, d => DomWf K₁ d.1 ∧ DomWf K₂ d.2

/-- Invariance: the relation between candidates of one kind. -/
def Inv : (K : Kind) → Dom K → CR K → CR K → Prop
  | .star, _, R, S => Sat R ∧ Sat S ∧ Same R S
  | .arrT K, d, f, g => ∀ x y, d.1 x y → Inv K d.2 (f x) (g y)
  | .arrK K₁ K₂, d, F, G => ∀ C C', Inv K₁ d.1 C C' → Inv K₂ d.2 (F C) (G C')

theorem inv_star (R S : Relation) : Inv .star () R S = (Sat R ∧ Sat S ∧ Same R S) := rfl

/-- A partial equivalence on candidates. -/
structure PER {α : Type} (r : α → α → Prop) : Prop where
  symm : ∀ {a b}, r a b → r b a
  trans : ∀ {a b c}, r a b → r b c → r a c

theorem inv_laws : (K : Kind) → (d : Dom K) → DomWf K d → PER (Inv K d)
  | .star, _, _ =>
      ⟨fun ⟨hR, hS, h⟩ => ⟨hS, hR, fun x y => (h x y).symm⟩,
        fun ⟨hR, _, h⟩ ⟨_, hT, g⟩ => ⟨hR, hT, fun x y => (h x y).trans (g x y)⟩⟩
  | .arrT K, d, hd => by
      have ih := inv_laws K d.2 hd.2
      refine ⟨fun h x y hxy => ih.symm (h y x (hd.1.symm hxy)), fun h g x y hxy => ?_⟩
      exact ih.trans (h x y hxy) (g y y (hd.1.trans (hd.1.symm hxy) hxy))
  | .arrK K₁ K₂, d, hd => by
      have ih₁ := inv_laws K₁ d.1 hd.1
      have ih₂ := inv_laws K₂ d.2 hd.2
      refine ⟨fun h C C' hC => ih₂.symm (h C' C (ih₁.symm hC)), fun h g C C' hC => ?_⟩
      exact ih₂.trans (h C C' hC) (g C' C' (ih₁.trans (ih₁.symm hC) hC))

/-- The canonical candidate, by recursion on the kind. -/
def can : (K : Kind) → CR K
  | .star => botRel
  | .arrT K => fun _ => can K
  | .arrK _ K₂ => fun _ => can K₂

theorem can_inv : (K : Kind) → (d : Dom K) → Inv K d (can K) (can K)
  | .star, _ => ⟨botRel_sat, botRel_sat, fun _ _ => Iff.rfl⟩
  | .arrT K, d => fun _ _ _ => can_inv K d.2
  | .arrK _ K₂, d => fun _ _ _ => can_inv K₂ d.2

/-! ## Impredicative quantification at every kind -/

def allRel (K : Kind) (d : Dom K) (B : CR K → Relation) : Relation :=
  fun f g => ∀ C, Inv K d C C → B C f g

theorem all_sat (K : Kind) (d : Dom K) (B : CR K → Relation)
    (hB : ∀ C, Inv K d C C → Sat (B C)) : Sat (allRel K d B) := by
  refine ⟨⟨fun h C hC => (hB C hC).1.symm (h C hC), fun h g C hC => (hB C hC).1.trans (h C hC)
    (g C hC)⟩, fun x y h => ?_⟩
  exact (hB _ (can_inv K d)).2 x y (h _ (can_inv K d))

/-! ## Term-dependent fibres -/

/-- An invariant family gives the same relation at related realizers. -/
theorem fibre_respect {D : Relation} {C : CR (.arrT .star)} (hC : Inv (.arrT .star) (D, ()) C C)
    {x y : Value} (hxy : D x y) : Same (C x) (C y) :=
  (hC x y hxy).2.2

def arrowRel (R S : Relation) : Relation := fun f g =>
  f .bot ∧ g .bot ∧ ∀ u v, R u v → S (NeutralPi.applyValue f u) (NeutralPi.applyValue g v)

theorem arrow_sat {R S : Relation} (hR : Laws R) (hS : Sat S) : Sat (arrowRel R S) := by
  refine ⟨⟨fun ⟨hf, hg, h⟩ => ⟨hg, hf, fun u v huv => hS.1.symm (h v u (hR.symm huv))⟩,
    fun ⟨hf, _, h⟩ ⟨_, hk, g⟩ => ⟨hf, hk, fun u v huv => ?_⟩⟩, fun _ _ h => h.1⟩
  exact hS.1.trans (h u v huv) (g v v (hR.trans (hR.symm huv) huv))

/-- Leibniz transport: a realizer of `∀ P : A → Prop, P x → P x` realizes
`∀ P : A → Prop, P x → P y` when `x` and `y` are related in `A`. -/
theorem leibniz_transport {D : Relation} {x y f g : Value} (hxy : D x y)
    (h : allRel (.arrT .star) (D, ()) (fun C => arrowRel (C x) (C x)) f g) :
    allRel (.arrT .star) (D, ()) (fun C => arrowRel (C x) (C y)) f g := by
  intro C hC
  obtain ⟨hf, hg, k⟩ := h C hC
  exact ⟨hf, hg, fun u v huv => (fibre_respect hC hxy _ _).mp (k u v huv)⟩

theorem leibniz_sat {D : Relation} (hD : Laws D) {x y : Value} (hxy : D x y) :
    Sat (allRel (.arrT .star) (D, ()) (fun C => arrowRel (C x) (C y))) :=
  all_sat _ _ _ fun _ hC =>
    arrow_sat (hC x x (hD.trans hxy (hD.symm hxy))).1.1 (hC y y (hD.trans (hD.symm hxy) hxy)).1

/-! ## Mutant: invariance is load-bearing -/

/-- A family saturated at every point that reads one observation of the
realizer. -/
def badFamily : CR (.arrT .star) := fun z u v => u .bot ∧ v .bot ∧ z (.spine 0 [])

def mark : Value := fun c => c = .bot ∨ c = .spine 0 []

theorem badFamily_sat (z : Value) : Sat (badFamily z) :=
  ⟨⟨fun ⟨hu, hv, hz⟩ => ⟨hv, hu, hz⟩, fun ⟨hu, _, hz⟩ ⟨_, hw, _⟩ => ⟨hu, hw, hz⟩⟩,
    fun _ _ h => h.1⟩

/-- All premises constructed: `bottom` and `mark` are related by the
saturated relation `botRel`, `badFamily` is saturated at every point, and
its relations at the two realizers differ, so it is not invariant. -/
theorem badFamily_not_inv :
    botRel bottom mark ∧ (∀ z, Sat (badFamily z)) ∧
    ¬ Same (badFamily bottom) (badFamily mark) ∧
    ¬ Inv (.arrT .star) (botRel, ()) badFamily badFamily := by
  have hne : ¬ Same (badFamily bottom) (badFamily mark) := by
    intro h
    obtain ⟨_, _, hz⟩ := (h bottom bottom).mpr ⟨rfl, rfl, Or.inr rfl⟩
    cases hz
  refine ⟨⟨rfl, Or.inl rfl⟩, badFamily_sat, hne, fun h => hne ?_⟩
  exact fibre_respect h ⟨rfl, Or.inl rfl⟩

end Rcic.Declarative.Ann.LR3.KindCandidateProbe
