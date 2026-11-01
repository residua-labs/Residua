import rcic.RcicF3PiNormalize
import rcic.RcicF3PiIndependent
import rcic.RcicF3PiRecNode
/-! Actual admitted raw fields pay the normalized recursor's semantic
child guard. This concerns operational unfolding, not recursor typing or
universal group production. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.RecPlan
open Rcic.Declarative
universe u

/-- Inhabited raw recursive fields supply the semantic telescope used by
operational childness, at exactly the normalized admission depth. -/
theorem field_mem_of_admitted (M : Interp.{u}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n fuel f nu np ni depth : Nat}
    (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K)
    {T : Expr Nat} {s : FieldShape} {idx : List (Expr Nat)}
    (ha : fieldAnalyze E fuel f nu np ni depth T = .permitted s idx)
    (hI : InstOK E σ K T) (ρ : Nat → PSet.{u}) (x : PSet.{u})
    (hx : x ∈ Ed M (den M σ ρ T)) : FieldMem.{u,u+1} M s x := by
  cases s with
  | nonrecursive => trivial
  | recursive inner =>
      obtain ⟨ds, b, hr, hl, _, _, _⟩ := PiIndependent.recursive_scans ha
      obtain ⟨hd, hm⟩ := normalizedField_mem M σ K hE hb (fuel - 1) T ds b ρ x hr hI hx
      cases hl
      exact ⟨{ S : PSet.{u} // Dich S },
        PiSyntaxCompile.compile M σ (PiTypedCompile.leafIndex M σ b) ds ρ,
        (fun i => i.1), hd, hm⟩

/-- Complete dependent raw tuples supply every normalized operational
field witness; no caller supplies a telescope or childness premise. -/
theorem fields_mem_of_admitted (M : Interp.{u}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n fuel f nu np ni : Nat}
    (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K) :
    ∀ (As : List (Expr Nat)) (depth : Nat) (ss : List FieldShape),
    fieldShapesFuel E fuel f nu np ni depth As = some ss →
    (∀ A ∈ As, InstOK E σ K A) → ∀ ρ xs,
    TelFits M σ As ρ xs → FieldsMem.{u,u+1} M ss xs := by
  intro As
  induction As with
  | nil =>
      intro depth ss ha hI ρ xs hx
      simp only [fieldShapesFuel, Option.some.injEq] at ha
      subst ss
      cases xs with
      | nil => trivial
      | cons x xs => exact hx.elim
  | cons A As ih =>
      intro depth ss ha hI ρ xs hx
      cases hh : fieldAnalyze E fuel f nu np ni depth A with
      | unresolved => simp only [fieldShapesFuel, hh] at ha; cases ha
      | refused why => simp only [fieldShapesFuel, hh] at ha; cases ha
      | permitted s idx =>
          cases ht : fieldShapesFuel E fuel f nu np ni (depth + 1) As with
          | none => simp only [fieldShapesFuel, hh, ht] at ha; cases ha
          | some rest =>
              simp only [fieldShapesFuel, hh, ht] at ha
              have hs : s :: rest = ss := Option.some.inj ha
              rw [← hs]
              cases xs with
              | nil => exact hx.elim
              | cons x xs =>
                  exact ⟨field_mem_of_admitted M σ K hE hb hh
                    (hI A (List.mem_cons_self _ _)) ρ x hx.1,
                    ih (depth + 1) rest ht (fun B hB => hI B (List.mem_cons_of_mem _ hB))
                      (vcons x ρ) xs hx.2⟩

/-- Any normalized operational plan unfolds on an original admitted tuple.
This is elementary composition, with ordinary normalization premises. -/
theorem core_data_of_fits (M : Interp.{u}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n fuel f nu np ni depth : Nat}
    (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K)
    (plan : List (List FieldShape)) (ms : List PSet.{u})
    {j : Nat} {ss : List FieldShape} (hj : plan[j]? = some ss)
    (As : List (Expr Nat))
    (ha : fieldShapesFuel E fuel f nu np ni depth As = some ss)
    (hI : ∀ A ∈ As, InstOK E σ K A) (ρ : Nat → PSet.{u}) (xs : List PSet.{u})
    (hx : TelFits M σ As ρ xs) :
    Equiv (core M f plan ms (dataVal j xs))
      (fapps (ms.getD j pempty) (args (core M f plan ms) ss xs)) := by
  exact core_data_mem M f plan ms hj
    (fields_mem_of_admitted M σ K hE hb As depth ss ha hI ρ xs hx)

/-- The actual admitted node unfolds on actual original field tuples.
This pays only the operational child guard, not the motive/minor typing. -/
theorem node_data_of_fits (M : Interp.{u}) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) {n : Nat}
    (hE : EnvSound M σ K node.E0 n) (hb : BodiesOK node.E0 σ K)
    (ms : List PSet.{u}) (i : Fin node.a.constructors.length)
    (hI : ∀ A ∈ (node.a.constructorViews i).fields, InstOK node.E0 σ K A)
    (ρ : Nat → PSet.{u}) (xs : List PSet.{u})
    (hx : TelFits M σ (node.a.constructorViews i).fields ρ xs) :
    Equiv (nodeCore M node ms (dataVal i.val xs))
      (fapps (ms.getD i.val pempty)
        (args (nodeCore M node ms) (node.h14.shapesAt i) xs)) := by
  exact node_data_mem M node ms i (fields_mem_of_admitted M σ K hE hb
    (node.a.constructorViews i).fields node.a.family.parameters.length
    (node.h14.shapesAt i) (node.h14.analyzed i) hI ρ xs hx)

end Rcic.F3.PSet.RecPlan
