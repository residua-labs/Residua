import rcic.RcicF8OM23

/-!
# Original-wrapper annotation request: the eta/K self-overlap O-M edge

The removed atoms are the TWO COMPLETE original D inputs H1/H2, not just
hf1/hf2 typings, the inner d1/d2, or a generated K step. Each c_i is an
actual Child of its own original conv wrapper. The caller is those two atoms
followed by untouched Z. The callee replaces them by the literal leaves of
an EvTc.trans/symm request; no materialized composite is admitted as lit.

This module adds no ParRedT/EvPar constructor, X implementation or assumption.
The X-output corollary is explicitly conditional on the landed XContract.
No global piRow, U, sort uniqueness or reconstructed endpoint is used.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.EtaKAnnot

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
variable {f b₁ b₂ A₁ B₁ A₂ B₂ T : Expr Nat}

/-- First COMPLETE original peak input. -/
def leftInput
    (d₁ : ParRedT (PEqLeafT E n) E n Γ f b₁ (.pi A₁ B₁))
    (c₁ : TyConvT E n Γ (.pi A₁ B₁) T) :
    ParRedT (PEqLeafT E n) E n Γ f b₁ T :=
  .conv Γ f b₁ (.pi A₁ B₁) T d₁ c₁

/-- Second COMPLETE original peak input. -/
def rightInput
    (d₂ : ParRedT (PEqLeafT E n) E n Γ f b₂ (.pi A₂ B₂))
    (c₂ : TyConvT E n Γ (.pi A₂ B₂) T) :
    ParRedT (PEqLeafT E n) E n Γ f b₂ T :=
  .conv Γ f b₂ (.pi A₂ B₂) T d₂ c₂

variable
    (d₁ : ParRedT (PEqLeafT E n) E n Γ f b₁ (.pi A₁ B₁))
    (d₂ : ParRedT (PEqLeafT E n) E n Γ f b₂ (.pi A₂ B₂))
    (c₁ : TyConvT E n Γ (.pi A₁ B₁) T)
    (c₂ : TyConvT E n Γ (.pi A₂ B₂) T)

/-- Replaced multiset, represented as a list: retain both occurrences even
when the two input derivations coincide. Z is not removed. -/
def removedAtoms : List (Jd E n) :=
  [.pr (leftInput d₁ c₁), .pr (rightInput d₂ c₂)]

/-- Exact caller: complete original D fork plus the untouched frame. -/
def callerAtoms (Z : List (Jd E n)) : List (Jd E n) :=
  removedAtoms d₁ d₂ c₁ c₂ ++ Z

theorem leftChain_child : Child (.tc c₁) (.pr (leftInput d₁ c₁)) :=
  .tail _ (.head _)

theorem rightChain_child : Child (.tc c₂) (.pr (rightInput d₂ c₂)) :=
  .tail _ (.head _)

/-- The actual X input. Lazy composition retains ONLY the two original
wrapper fields as leaves, not an atom for the generated trans/symm chain. -/
def annotRequest :
    EvTc (removedAtoms d₁ d₂ c₁ c₂) Γ (.pi A₁ B₁) (.pi A₂ B₂) :=
  .trans
    (.lit c₁ ⟨_, .head _, .inr (.child (leftChain_child d₁ c₁))⟩)
    (.symm (.lit c₂ ⟨_, .tail _ (.head _),
      .inr (.child (rightChain_child d₂ c₂))⟩))

theorem annotRequest_leaves :
    (annotRequest d₁ d₂ c₁ c₂).leaves = [.tc c₁, .tc c₂] := rfl

/-- Exact materialization at the original endpoints; no equality merely
of endpoints or a replacement by a convenient reflexive chain. -/
theorem annotRequest_val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    (annotRequest d₁ d₂ c₁ c₂).val hcl hinst =
      TyConvT.trans Γ (.pi A₁ B₁) T (.pi A₂ B₂) c₁ c₂.symmT := rfl

/-- Each request leaf is strictly below a REMOVED original input. -/
theorem annotRequest_strict (ℓ : Jd E n)
    (hℓ : ℓ ∈ (annotRequest d₁ d₂ c₁ c₂).leaves) :
    ∃ root ∈ removedAtoms d₁ d₂ c₁ c₂, SubOf ℓ root := by
  rw [annotRequest_leaves] at hℓ
  rcases List.mem_cons.mp hℓ with rfl | hℓ
  · exact ⟨_, .head _, .child (leftChain_child d₁ c₁)⟩
  · rcases List.mem_cons.mp hℓ with rfl | hℓ
    · exact ⟨_, .tail _ (.head _), .child (rightChain_child d₂ c₂)⟩
    · exact False.elim (List.not_mem_nil _ hℓ)

/-- Named O-M obligation discharged for the ORIGINAL wrapper pair. This
is an edge from D's original caller to X's input, not from U's output to X. -/
theorem OM_etaK_annot (Z : List (Jd E n)) :
    OM3_edge (callerAtoms d₁ d₂ c₁ c₂ Z)
      ((annotRequest d₁ d₂ c₁ c₂).leaves ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (annotRequest_strict d₁ d₂ c₁ c₂)

/-- The existing X contract retains strict original-input provenance of
BOTH returned components. It does not implement X or supply its contract. -/
theorem X_outputs_strict
    (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X) :
    let q := annotRequest d₁ d₂ c₁ c₂
    let ans := X (removedAtoms d₁ d₂ c₁ c₂) q
    ∀ ℓ ∈ ans.1.leaves ++ ans.2.leaves,
      ∃ root ∈ removedAtoms d₁ d₂ c₁ c₂, SubOf ℓ root := by
  dsimp only
  intro ℓ hℓ
  obtain ⟨ℓ', hm, hs⟩ := hX _ (annotRequest d₁ d₂ c₁ c₂) ℓ hℓ
  obtain ⟨root, hr, ht⟩ := annotRequest_strict d₁ d₂ c₁ c₂ ℓ' hm
  exact ⟨root, hr, subEq_trans_subOf hs ht⟩

/-- Returned components remain strictly below the SAME original D caller.
This is not a claim that output support is strictly below q.leaves. -/
theorem X_outputs_edge
    (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    (Z : List (Jd E n)) :
    let q := annotRequest d₁ d₂ c₁ c₂
    let ans := X (removedAtoms d₁ d₂ c₁ c₂) q
    OM3_edge (callerAtoms d₁ d₂ c₁ c₂ Z)
      ((ans.1.leaves ++ ans.2.leaves) ++ Z) :=
  om3_edge_of_strictLeaves (List.cons_ne_nil _ _)
    (X_outputs_strict d₁ d₂ c₁ c₂ X hX)

end Rcic.Declarative.F8Measure.EtaKAnnot

#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.leftInput
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.rightInput
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.removedAtoms
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.callerAtoms
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.leftChain_child
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.rightChain_child
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.annotRequest
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.annotRequest_leaves
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.annotRequest_val
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.annotRequest_strict
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.OM_etaK_annot
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.X_outputs_strict
#print axioms Rcic.Declarative.F8Measure.EtaKAnnot.X_outputs_edge
