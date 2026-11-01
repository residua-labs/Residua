import rcic.RcicF3IndexedBranchFixture
import rcic.RcicF3RawFamilyLevels

/-!
# Literal Branch fields and constructors in an admissible closed frame

The stored recursive field is

    (y : Prop) → (y → bot) → x → Branch p y.

The parameter p and ordinary field x are retained. The recursive field
value is pempty, with membership constructed through the actual dependent
telescope and the complete child key [p,y].

An empty decoded index gives a leaf constructor. For a general parent,
the actual negative-proof argument makes every reached child index empty.
Closure then supplies those child fibres and hence the parent field.

These are intermediate frame lemmas. A later consumer must supply closure
from the actual candidate producer. This module does not assert an Eval,
typed IH, iota theorem, installed-table result, or whole-tier result.

The actual candidate and evaluation consumer is IndexedBranchEvalAttack.
scope_closure_claim = 0. closure_claim = 0.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000


namespace Rcic.F3.PSet.IndexedBranchFields

open Rcic.Declarative PiIndex RawFamily
open IndexedBranchDomain
  (originalAssignment originalDomains originalArguments)

noncomputable abbrev fd : FamData :=
  famDataOf IndexedBranchFixture.groupAdmitted

noncomputable def model
    (P : Premises4)
    (μ : Nat → List Nat → PSet.{4})
    (Y : Frame) : Interp.{4} :=
  mkM P (RawFamily.table P μ fd Y)

private theorem family_free :
    ∀ e ∈ fd.params ++ fd.indices,
      occursConst fd.fref e = false := by
  intro e he
  change e ∈ [(.sort .zero : Expr Nat), .sort .zero] at he
  rcases List.mem_cons.mp he with rfl | he
  · rfl
  · cases List.mem_singleton.mp he
    rfl

/-- Construct membership of the actual stored field from its reached
child fibres. The syntax valuation is independent of the arity-zero
family instance. The callback is discharged by ctor_of_closed below. -/
theorem field_mem_of_children
    (P : Premises4)
    (μ : Nat → List Nat → PSet.{4})
    (Y : Frame)
    (hY : Admissible fd Y)
    (σ : Nat → Nat)
    (p x : PSet.{4})
    (hp : p ∈ Ed (model P μ Y) (tyv (U W4 0)))
    (hchildren :
      ∀ y n h,
        TelFits (model P μ Y) σ originalDomains
          (originalAssignment p x) [y, n, h] →
        pempty ∈ Y [] (key [p, y])) :
    pempty ∈ Ed (model P μ Y)
      (den (model P μ Y) σ (originalAssignment p x)
        IndexedBranchFixture.field) := by
  let M := model P μ Y
  let t := tel M σ originalDomains originalArguments
    (originalAssignment p x)
  let F := fitFrame P μ fd Y []
  have ht : t.DomainsDich :=
    PiSyntaxCompile.compile_domains M σ
      (read M σ originalArguments) originalDomains
      (originalAssignment p x)
  have htrue :
      pempty ∈ Ed M (t.erasedType M (fun _ => tv True)) :=
    (PiPropField.member_iff M t ht (fun _ => True) pempty).mpr
      ⟨Equiv.rfl, fun _ => True.intro⟩
  have hleaf :
      ∀ zs,
        TelFits M σ originalDomains (originalAssignment p x) zs →
        pempty ∈ F
          (key (originalArguments.map
            (den M σ (push zs (originalAssignment p x))))) := by
    intro zs hzs
    cases zs with
    | nil => exact hzs.elim
    | cons y ys =>
        cases ys with
        | nil => exact hzs.2.elim
        | cons n ns =>
            cases ns with
            | nil => exact hzs.2.2.elim
            | cons h hs =>
                cases hs with
                | nil =>
                    change pempty ∈ F (key [p, y])
                    have hfit :
                        TelFits M (σOf [])
                          (fd.params ++ fd.indices) ρ0 [p, y] :=
                      ⟨hp, hzs.1, True.intro⟩
                    obtain ⟨j, hj⟩ := hchildren y n h hzs
                    exact mem_sep.mpr ⟨j, hfit, hj⟩
                | cons q qs => exact hzs.2.2.2.elim
  have hfield : pempty ∈ Ed M (t.erasedType M F) :=
    t.erasedType_mono_on M ht
      (fun _ => tv True) F
      (fun _ => dich_tv True)
      (fitFrame_dich P μ fd Y hY [])
      (fun q z hz => by
        obtain ⟨zs, hzs, he⟩ :=
          PiSyntaxCompile.result_fits M σ
            (read M σ originalArguments) originalDomains
            (originalAssignment p x) q
        have he' :
            t.result q =
              key (originalArguments.map
                (den M σ (push zs (originalAssignment p x)))) := he
        change z ∈ F (t.result q)
        rw [he']
        exact mem_congr_left (mem_tv.mp hz).2.symm (hleaf zs hzs))
      pempty htrue
  rw [IndexedBranchFixture.original_field]
  exact mem_congr_right
    (recursiveField_ed_at P μ fd Y hY family_free
      [] σ [] rfl originalDomains originalArguments rfl
      (originalAssignment p x)) hfield

/-- At an empty decoded index, the third child argument is impossible.
The constructor still retains its actual ordinary field x. -/
theorem empty_ctor
    (P : Premises4)
    (μ : Nat → List Nat → PSet.{4})
    (Y : Frame)
    (hY : Admissible fd Y)
    (p x : PSet.{4})
    (hp : p ∈ Ed (model P μ Y) (tyv (U W4 0)))
    (hx : x ∈ Ed (model P μ Y) (tyv (U W4 0)))
    (hempty : ∀ z, z ∈ Ed (model P μ Y) x → False) :
    CtorAt P μ fd Y [] (key [p, x]) pempty := by
  have hg :
      pempty ∈ Ed (model P μ Y)
        (den (model P μ Y) (σOf []) (originalAssignment p x)
          IndexedBranchFixture.field) := by
    apply field_mem_of_children P μ Y hY (σOf []) p x hp
    intro y n h hzs
    exact (hempty h hzs.2.2.1).elim
  refine ⟨⟨0, by decide⟩, [p], [x, pempty], ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hp, True.intro⟩
  · exact ⟨hx, hg, True.intro⟩
  · exact True.intro
  · rfl
  · exact Equiv.rfl

/-- The actual negative-proof argument makes every reached child a leaf.
The supplied frame closure inserts those leaves; no child-existence or
evaluation callback remains in the conclusion or public premises. -/
theorem ctor_of_closed
    (P : Premises4)
    (μ : Nat → List Nat → PSet.{4})
    (Y : Frame)
    (hY : Admissible fd Y)
    (hclosed : Closed P μ fd Y)
    (p x : PSet.{4})
    (hp : p ∈ Ed (model P μ Y) (tyv (U W4 0)))
    (hx : x ∈ Ed (model P μ Y) (tyv (U W4 0))) :
    CtorAt P μ fd Y [] (key [p, x]) pempty := by
  have hg :
      pempty ∈ Ed (model P μ Y)
        (den (model P μ Y) (σOf []) (originalAssignment p x)
          IndexedBranchFixture.field) := by
    apply field_mem_of_children P μ Y hY (σOf []) p x hp
    intro y n h hzs
    have hempty : ∀ z, z ∈ Ed (model P μ Y) y → False :=
      IndexedBranchDomain.original_child_empty P
        (RawFamily.table P μ fd Y) (σOf []) p x y n h hzs
    exact hclosed [] (key [p, y]) pempty
      (empty_ctor P μ Y hY p y hp hzs.1 hempty)
  refine ⟨⟨0, by decide⟩, [p], [x, pempty], ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hp, True.intro⟩
  · exact ⟨hx, hg, True.intro⟩
  · exact True.intro
  · rfl
  · exact Equiv.rfl

end Rcic.F3.PSet.IndexedBranchFields

#print axioms Rcic.F3.PSet.IndexedBranchFields.field_mem_of_children
#print axioms Rcic.F3.PSet.IndexedBranchFields.empty_ctor
#print axioms Rcic.F3.PSet.IndexedBranchFields.ctor_of_closed
