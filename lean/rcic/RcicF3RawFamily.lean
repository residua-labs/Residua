import rcic.RcicF3PiValue
import rcic.RcicF3RoleTable

/-!
# A raw, indexed intersection role

The role is defined on every stored family signature. Constructor closure
uses the literal field denotations, including all dependent products, and
all universe instances jointly. No raw shape classifier or numeric-label
exception selects the interpretation. Prop fibres are truth sets; data
fibres are bounded intersections of constructor-closed frames.

This definition does not establish that the intersection is closed or
small. Those are production obligations at admitted positive signatures;
in particular `Closed` is not an additional apex assumption. The semantic
W construction is needed to supply a small closed frame, rather than an
omega-stage continuity assertion. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamily
open Rcic.Declarative PiIndex

abbrev Frame := List Nat → Index.{4} → PSet.{4}

def endValue (C : Frame) (vs : List Nat) (q : Nat)
    (ρ : Nat → PSet.{4}) : PSet.{4} :=
  tyv (C vs (key (lastVals q ρ)))

def ofFrame (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (vs : List Nat) : PSet.{4} :=
  piLam (mkM P μ) (σOf vs) (endValue C vs (fd.params.length + fd.indices.length))
    ρ0 (famType fd)

def table (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) : Nat → List Nat → PSet.{4} :=
  upd μ fd.fref (ofFrame P μ fd C)

/-- Frames used for the intersection have correctly sized fibres and the
appropriate proof/data face. This predicate has no environment or table
argument. Its inhabitation at admitted signatures remains a theorem to prove. -/
def Admissible (fd : FamData) (C : Frame) : Prop :=
  ∀ vs i, C vs i ∈ W4 (evalTotal (σOf vs) fd.resLevel) ∧
    (if evalTotal (σOf vs) fd.resLevel = 0 then
      ∀ z, z ∈ C vs i → Equiv z pempty
    else ∀ z, z ∈ C vs i → ¬ Equiv z pempty)

/-- One literal constructor step. The complete parameter/index tuple is
retained in the quotient key; no representative of that key is chosen. -/
def CtorAt (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (vs : List Nat) (i : Index.{4}) (z : PSet.{4}) : Prop :=
  ∃ (j : Fin fd.ctors.length) (ps xs : List PSet.{4}),
    TelFits (mkM P (table P μ fd C)) (σOf vs) fd.params ρ0 ps ∧
    TelFits (mkM P (table P μ fd C)) (σOf vs) (fd.ctors.get j).1 (push ps ρ0) xs ∧
    (if evalTotal (σOf vs) fd.resLevel = 0 then True else
      SmallAlong (mkM P (table P μ fd C)) (σOf vs)
        (W4 (evalTotal (σOf vs) fd.resLevel)) (fd.ctors.get j).1 (push ps ρ0) xs) ∧
    i = key (ps ++ (fd.ctors.get j).2.map
      (den (mkM P (table P μ fd C)) (σOf vs) (push xs (push ps ρ0)))) ∧
    Equiv z (if evalTotal (σOf vs) fd.resLevel = 0 then pempty else dataVal j.val xs)

def Closed (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) : Prop :=
  ∀ vs i z, CtorAt P μ fd C vs i z → z ∈ C vs i

def InAll (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (vs : List Nat) (i : Index.{4}) (z : PSet.{4}) : Prop :=
  ∀ C : Frame, Admissible fd C → Closed P μ fd C → z ∈ C vs i

def frame (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) : Frame := fun vs i =>
  if evalTotal (σOf vs) fd.resLevel = 0 then tv (InAll P μ fd vs i pempty)
  else sep (InAll P μ fd vs i) (W4 (evalTotal (σOf vs) fd.resLevel))

/-- The proposed universal role; its StepAG producer is not asserted here. -/
def role : RoleModel.FamilyValue := fun P μ fd => ofFrame P μ fd (frame P μ fd)

end Rcic.F3.PSet.RawFamily
