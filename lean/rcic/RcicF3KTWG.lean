import rcic.RcicF3KT

/-!
# F3 S7 KT-2b-1: guarded W-signatures (indexed families as a least fixed point)

`RcicF3KTW`'s W-signature has no side conditions.  A fibre of an *indexed* family has one: a
recursive field `f : Π y : A, F (idx y)` must have, at each `y`, a child whose tuple is `idx y`; the
child's tuple is read off the child's *decoded set*, so it cannot be part of the `Type`-level
shape (that would be induction–recursion).  It is a guard on the decoded children instead.

A `GSig` adds `ok s h`, a proposition about a shape and the decoded children, invariant under
pointwise `≈`.  `ValidW` is the inductive predicate "every subtree is guarded"; the fibre is the
image of the valid trees, `gSet := mk {w // ValidW w} (decW ∘ val)`, still with a `Type u` index
type: smallness is by construction.

- `gphi_gSet_equiv`: `Φ(gSet) ≈ gSet` (no choice);
- `gSet_least`: below every `Φ`-closed `X` (explicit `Choice` premise to pick child indices);
- `gSet_equiv_lfp`: `lfp U Φ ≈ gSet` on a bounding `U ⊇ gSet` where `Φ` is a `KTOp`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u

namespace PSet

/-- A guarded W-signature over `PSet.{u}`. -/
structure GSig where
  Sh : Type u
  br : Sh → Type u
  code : (s : Sh) → (br s → PSet.{u}) → PSet.{u}
  ok : (s : Sh) → (br s → PSet.{u}) → Prop
  code_congr : ∀ s (h h' : br s → PSet.{u}), (∀ b, Equiv (h b) (h' b)) → Equiv (code s h) (code s h')
  ok_congr : ∀ s (h h' : br s → PSet.{u}), (∀ b, Equiv (h b) (h' b)) → ok s h → ok s h'

/-- Trees of the signature. -/
inductive GT (S : GSig.{u}) : Type u where
  | sup (s : S.Sh) (g : S.br s → GT S)

/-- Structural decoding. -/
def decG (S : GSig.{u}) : GT S → PSet.{u}
  | .sup s g => S.code s (fun b => decG S (g b))

/-- Every subtree is guarded. -/
inductive ValidW (S : GSig.{u}) : GT S → Prop where
  | sup (s : S.Sh) (g : S.br s → GT S) (hg : ∀ b, ValidW S (g b))
      (hok : S.ok s (fun b => decG S (g b))) : ValidW S (.sup s g)

/-- The fibre: decoded valid trees. -/
def gSet (S : GSig.{u}) : PSet.{u} := mk {w : GT S // ValidW S w} (fun w => decG S w.1)

/-- The guarded operator. -/
def gphi (S : GSig.{u}) (X : PSet.{u}) : PSet.{u} :=
  mk (Σ s : S.Sh, {i : S.br s → X.Idx // S.ok s (fun b => X.Func (i b))})
    (fun p => S.code p.1 (fun b => X.Func (p.2.1 b)))

theorem gphi_gSet_closed (S : GSig.{u}) : Sub (gphi S (gSet S)) (gSet S) := by
  intro z ⟨⟨s, i, hok⟩, hz⟩
  refine ⟨⟨.sup s (fun b => (i b).1), ValidW.sup s _ (fun b => (i b).2) ?_⟩, hz⟩
  exact hok

theorem gSet_sub_gphi (S : GSig.{u}) : Sub (gSet S) (gphi S (gSet S)) := by
  intro z ⟨⟨w, hw⟩, hz⟩
  cases hw with
  | sup s g hg hok =>
    exact ⟨⟨s, fun b => ⟨g b, hg b⟩, hok⟩, hz⟩

/-- `Φ(gSet) ≈ gSet`, with no choice. -/
theorem gphi_gSet_equiv (S : GSig.{u}) : Equiv (gphi S (gSet S)) (gSet S) :=
  ext fun z => ⟨gphi_gSet_closed S z, gSet_sub_gphi S z⟩

/-- **Induction**: `gSet` is below every `Φ`-closed set. -/
theorem gSet_least (ch : Choice.{u}) (S : GSig.{u}) {X : PSet.{u}} (hX : Sub (gphi S X) X) :
    Sub (gSet S) X := by
  have key : ∀ w : GT S, ValidW S w → decG S w ∈ X := by
    intro w hw
    induction hw with
    | sup s g hg hok ih =>
      let i : S.br s → X.Idx := fun b =>
        (ch (α := ULift.{u + 1} X.Idx) (fun j => Equiv (X.Func j.down) (decG S (g b)))
          (let ⟨j, hj⟩ := ih b; ⟨⟨j⟩, hj⟩)).1.down
      have hi : ∀ b, Equiv (X.Func (i b)) (decG S (g b)) := fun b =>
        (ch (α := ULift.{u + 1} X.Idx) (fun j => Equiv (X.Func j.down) (decG S (g b)))
          (let ⟨j, hj⟩ := ih b; ⟨⟨j⟩, hj⟩)).2
      have hok' : S.ok s (fun b => X.Func (i b)) :=
        S.ok_congr s _ _ (fun b => (hi b).symm) hok
      have hmem : S.code s (fun b => X.Func (i b)) ∈ gphi S X := ⟨⟨s, i, hok'⟩, Equiv.refl _⟩
      exact mem_congr_left (S.code_congr s _ _ hi) (hX _ hmem)
  intro z ⟨⟨w, hw⟩, hz⟩
  exact mem_congr_left hz (key w hw)

/-- **`lfp` is `gSet`**, on any bounding set containing `gSet` where `Φ` is a `KTOp`. -/
theorem gSet_equiv_lfp (ch : Choice.{u}) (S : GSig.{u}) {U : PSet.{u}} (hU : Sub (gSet S) U)
    (hΦ : KTOp U (gphi S)) : Equiv (lfp U (gphi S)) (gSet S) :=
  ext fun z => ⟨lfp_least hU (gphi_gSet_closed S) z,
    gSet_least ch S (lfp_closed hΦ) z⟩

end PSet

end Rcic.F3
