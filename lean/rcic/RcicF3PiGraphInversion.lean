import rcic.RcicF3BoundedBVar
import rcic.RcicF3PiCompile
import rcic.RcicF3PropIota

/-!
# Reached semantic Pi inversion from an actual function

An existing function supplies all default outputs when one argument class
is changed. The explicit patched graph therefore proves reached codomain
inclusion from inclusion of whole function spaces, without selecting a
family of inhabitants or using Choice4. Empty domains require no output.

For the erased interpretation, a nonempty actual function rules out both
proof branches. A bounded conversion in the original fitted context then
gives equality of domain element sets and of every reached codomain.
This is semantic inversion at an actual function, not syntactic piRow,
typing of a normalized reduct, or soundness in a masked local context.
The recursive-local mask and its all-universe producer remain unpaid.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiGraphInversion
open Rcic.Declarative
universe u

/-- One explicit update of a quotient-indexed graph. The old function is
read everywhere except at the supplied argument's equivalence class. -/
noncomputable def patch (dec : ∀ p : Prop, Decidable p)
    (A g a y : PSet.{u}) (q : FBr A) : PSet.{u} :=
  cond dec (Equiv (PiCompile.classValue A q) a) y
    (fapp g (PiCompile.classValue A q))

private theorem patch_mem (dec : ∀ p : Prop, Decidable p)
    {A g a y : PSet.{u}} {B : PSet.{u} → PSet.{u}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hg : g ∈ piSet A B) (hy : y ∈ B a) :
    graphOf A (patch dec A g a y) ∈ piSet A B := by
  apply graph_mem_piSet hB
  intro i
  change cond dec (Equiv (PiCompile.classValue A (Quotient.mk (FSetoid A) i)) a)
    y (fapp g (PiCompile.classValue A (Quotient.mk (FSetoid A) i))) ∈ B (A.Func i)
  cases dec (Equiv (PiCompile.classValue A (Quotient.mk (FSetoid A) i)) a) with
  | isTrue he =>
      rw [cond_pos he]
      exact mem_congr_right (hB a (A.Func i)
        (he.symm.trans (PiCompile.classValue_at A i))) hy
  | isFalse he =>
      rw [cond_neg he]
      exact mem_congr_right (hB _ _ (PiCompile.classValue_at A i))
        (fapp_mem_piSet hB hg (PiCompile.classValue_mem A _))

/-- Function-space inclusion implies reached codomain inclusion. The
source function supplies a default section; no choice is made from B. -/
theorem codomain_sub (dec : ∀ p : Prop, Decidable p)
    {A A' g : PSet.{u}} {B B' : PSet.{u} → PSet.{u}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hB' : ∀ x x', Equiv x x' → Equiv (B' x) (B' x'))
    (h : Sub (piSet A B) (piSet A' B')) (hg : g ∈ piSet A B)
    (a : PSet.{u}) (ha : a ∈ A) : Sub (B a) (B' a) := by
  intro y hy
  let k := patch dec A g a y
  have hk : graphOf A k ∈ piSet A' B' := h _ (patch_mem dec hB hg hy)
  obtain ⟨i, hi⟩ := ha
  have he : Equiv (PiCompile.classValue A (Quotient.mk (FSetoid A) i)) a :=
    (PiCompile.classValue_at A i).trans hi
  have hp : ordPair a y ∈ graphOf A k := by
    refine ⟨i, ?_⟩
    change Equiv (ordPair (A.Func i)
      (cond dec (Equiv (PiCompile.classValue A (Quotient.mk (FSetoid A) i)) a)
        y (fapp g (PiCompile.classValue A (Quotient.mk (FSetoid A) i)))))
      (ordPair a y)
    rw [cond_pos he]
    exact ordPair_congr hi Equiv.rfl
  obtain ⟨a', _ha', y', hy', hp'⟩ :=
    (isFuncOnDep_of_mem_piSet hB' hk).2.1 _ hp
  have ep := ordPair_equiv hp'
  exact mem_congr_left ep.2.symm
    (mem_congr_right (hB' a' a ep.1.symm) hy')

/-- Equality of inhabited function spaces determines their domains and
all reached codomain element sets. The domain itself may be empty. -/
theorem function_spaces (dec : ∀ p : Prop, Decidable p)
    {A A' g : PSet.{u}} {B B' : PSet.{u} → PSet.{u}}
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hB' : ∀ x x', Equiv x x' → Equiv (B' x) (B' x'))
    (h : Equiv (piSet A B) (piSet A' B')) (hg : g ∈ piSet A B) :
    Equiv A A' ∧ ∀ a, a ∈ A → Equiv (B a) (B' a) := by
  have hg' := mem_congr_right h hg
  have hA : Equiv A A' := ext fun a =>
    ⟨fun ha => piSet_dom hB' hB hg' hg ha,
      fun ha => piSet_dom hB hB' hg hg' ha⟩
  refine ⟨hA, ?_⟩
  intro a ha
  exact ext fun y =>
    ⟨codomain_sub dec hB hB' (fun _ hz => mem_congr_right h hz) hg a ha y,
      codomain_sub dec hB' hB (fun _ hz => mem_congr_right h.symm hz)
        hg' a (mem_congr_right hA ha) y⟩

/-- A nonempty actual function removes the two proof branches before
function-space inversion is used. No regularity premise is added. -/
theorem elements (M : Interp.{u}) (A A' g : PSet.{u})
    (B B' : PSet.{u} → PSet.{u})
    (hB : ∀ x x', Equiv x x' → Equiv (B x) (B x'))
    (hB' : ∀ x x', Equiv x x' → Equiv (B' x) (B' x'))
    (h : Equiv (Ed M (piVal M A B)) (Ed M (piVal M A' B')))
    (hg : g ∈ Ed M (piVal M A B)) (hne : ¬ Equiv g pempty) :
    Equiv (Ed M A) (Ed M A') ∧
      ∀ a, a ∈ Ed M A → Equiv (Ed M (B a)) (Ed M (B' a)) := by
  have hg' := mem_congr_right h hg
  have hleft := ed_piVal M A B hB
  have hright := ed_piVal M A' B' hB'
  cases M.dec (PiProp M A B) with
  | isTrue hp =>
      rw [cond_pos hp] at hleft
      exact (hne (mem_tv.mp (mem_congr_right hleft hg)).2).elim
  | isFalse hp =>
      rw [cond_neg hp] at hleft
      cases M.dec (PiProp M A' B') with
      | isTrue hp' =>
          rw [cond_pos hp'] at hright
          exact (hne (mem_tv.mp (mem_congr_right hright hg')).2).elim
      | isFalse hp' =>
          rw [cond_neg hp'] at hright
          exact function_spaces M.dec
            (fun _ _ e => ed_congr M (hB _ _ e))
            (fun _ _ e => ed_congr M (hB' _ _ e))
            (hleft.symm.trans (h.trans hright)) (mem_congr_right hleft hg)

/-- Literal composition with the conversion extracted from an actual
bounded derivation. The original context and full valuation are retained. -/
theorem bounded_conversion (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvSound (mkM P μ) σ K E n)
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ)
    {A B A' B' : Expr Nat}
    (c : TyConvT E n Γ (.pi A B) (.pi A' B'))
    (hc : BoundedBVar.Bounded σ 4 K c)
    (g : PSet.{4})
    (hg : g ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ (.pi A B)))
    (hne : ¬ Equiv g pempty) :
    Equiv (Ed (mkM P μ) (den (mkM P μ) σ ρ A))
      (Ed (mkM P μ) (den (mkM P μ) σ ρ A')) ∧
      ∀ a, a ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ A) →
        Equiv (Ed (mkM P μ) (den (mkM P μ) σ (vcons a ρ) B))
          (Ed (mkM P μ) (den (mkM P μ) σ (vcons a ρ) B')) := by
  have he := BoundedBVar.chain_sound P μ σ K hE ρ hρ c hc
  exact elements (mkM P μ) (den (mkM P μ) σ ρ A)
    (den (mkM P μ) σ ρ A') g
    (fun a => den (mkM P μ) σ (vcons a ρ) B)
    (fun a => den (mkM P μ) σ (vcons a ρ) B')
    (den_resp _ _ _ B) (den_resp _ _ _ B')
    (ed_congr (mkM P μ) he) hg hne

end Rcic.F3.PSet.PiGraphInversion
