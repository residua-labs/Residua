import rcic.RcicF3KT

/-!
# F3 S7 KT-2a: the least fixed point of a W-shaped operator is a small set by construction

Route (i) of the class-A smallness decision (`F3_PLAN.md` S7; lane PROGRESS): the fibre of a
function-recursive family is the image of a Lean indexed W-type living one universe down.

A `WSig` is an abstract W-signature over `PSet.{u}`: shapes `Sh`, branching types `br s`
(`Type u`), and a decoding `code s h` of a shape applied to its children's sets. `WT` is the
W-type, `decW` its structural decoding, `wSet := mk WT decW : PSet.{u}`.

- `phi_wSet_equiv`: `Φ(wSet) ≈ wSet` (no choice);
- `wSet_least`: `wSet` is below every `Φ`-closed `X` (the induction principle; the one use of the
  explicit `Choice` premise is to pick an index for each child);
- `wSet_equiv_lfp`: for any bounding `U ⊇ wSet` on which `Φ` is a `KTOp`, `lfp U Φ ≈ wSet`.

So `lfp` is `≈` to a set with a `Type u` index type: smallness one universe down is by
construction, with no ordinals. Dependency of a later field's domain on an earlier *recursive*
field is induction–recursion and is outside this signature (lane PROGRESS).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u

namespace PSet

/-- An abstract W-signature over `PSet.{u}`. -/
structure WSig where
  Sh : Type u
  br : Sh → Type u
  code : (s : Sh) → (br s → PSet.{u}) → PSet.{u}
  code_congr : ∀ s (h h' : br s → PSet.{u}), (∀ b, Equiv (h b) (h' b)) → Equiv (code s h) (code s h')

/-- The W-type of the signature. -/
inductive WT (S : WSig.{u}) : Type u where
  | sup (s : S.Sh) (g : S.br s → WT S)

/-- The structural decoding. -/
def decW (S : WSig.{u}) : WT S → PSet.{u}
  | .sup s g => S.code s (fun b => decW S (g b))

/-- The fibre: the set of decoded trees. -/
def wSet (S : WSig.{u}) : PSet.{u} := mk (WT S) (decW S)

/-- The operator: shapes applied to children drawn from `X`. -/
def phi (S : WSig.{u}) (X : PSet.{u}) : PSet.{u} :=
  mk (Σ s : S.Sh, S.br s → X.Idx) (fun p => S.code p.1 (fun b => X.Func (p.2 b)))

theorem phi_wSet_closed (S : WSig.{u}) : Sub (phi S (wSet S)) (wSet S) := by
  intro z ⟨⟨s, i⟩, hz⟩
  exact ⟨.sup s i, hz⟩

theorem wSet_sub_phi (S : WSig.{u}) : Sub (wSet S) (phi S (wSet S)) := by
  intro z ⟨w, hw⟩
  cases w with
  | sup s g =>
    exact ⟨⟨s, g⟩, hw⟩

/-- `Φ(wSet) ≈ wSet`, with no choice. -/
theorem phi_wSet_equiv (S : WSig.{u}) : Equiv (phi S (wSet S)) (wSet S) :=
  ext fun z => ⟨phi_wSet_closed S z, wSet_sub_phi S z⟩

/-- **Induction**: `wSet` is below every `Φ`-closed set. -/
theorem wSet_least (ch : Choice.{u}) (S : WSig.{u}) {X : PSet.{u}} (hX : Sub (phi S X) X) :
    Sub (wSet S) X := by
  have key : ∀ w : WT S, decW S w ∈ X := by
    intro w
    induction w with
    | sup s g ih =>
      let i : S.br s → X.Idx := fun b =>
        (ch (α := ULift.{u + 1} X.Idx) (fun j => Equiv (X.Func j.down) (decW S (g b)))
          (let ⟨j, hj⟩ := ih b; ⟨⟨j⟩, hj⟩)).1.down
      have hi : ∀ b, Equiv (X.Func (i b)) (decW S (g b)) := fun b =>
        (ch (α := ULift.{u + 1} X.Idx) (fun j => Equiv (X.Func j.down) (decW S (g b)))
          (let ⟨j, hj⟩ := ih b; ⟨⟨j⟩, hj⟩)).2
      have hmem : S.code s (fun b => X.Func (i b)) ∈ phi S X := ⟨⟨s, i⟩, Equiv.refl _⟩
      exact mem_congr_left (S.code_congr s _ _ hi) (hX _ hmem)
  intro z ⟨w, hw⟩
  exact mem_congr_left hw (key w)

/-- **`lfp` is `wSet`**, on any bounding set containing `wSet` where `Φ` is a `KTOp`. -/
theorem wSet_equiv_lfp (ch : Choice.{u}) (S : WSig.{u}) {U : PSet.{u}} (hU : Sub (wSet S) U)
    (hΦ : KTOp U (phi S)) : Equiv (lfp U (phi S)) (wSet S) :=
  ext fun z => ⟨lfp_least hU (phi_wSet_closed S) z,
    wSet_least ch S (lfp_closed hΦ) z⟩

end PSet

end Rcic.F3
