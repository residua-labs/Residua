import rcic.RcicF3PiPropPrefix
import rcic.RcicF3KTWPropFix
/-! Dependent proof-prefix self-attacks: actual nested recursive fields,
a later field applying a function to the earlier proof, arbitrary family
renumbering, extensional proof aliases, and refusal to erase plain data.
Reader pins are not raw typed-group witnesses. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiPropPrefixAttack
open Rcic.Declarative PiPropPrefix
universe u

def proofTy : PSet.{u} := tyv (tv True)
def datum : PSet.{u} := dataVal 7 []
def domain : PSet.{u} := singleton datum

def nested (M : Interp.{u}) : PSet.{u} :=
  piVal M (tyv domain) (fun _ => piVal M (tyv domain) (fun _ => proofTy))

def table (M : Interp.{u}) (f : Nat) : Nat → List Nat → PSet.{u} :=
  fun r _ => if r = f then proofTy else if r = f + 1 then tyv domain
    else if r = f + 2 then lamVal M (nested M) (fun _ => tyv domain) else pempty

def model (M : Interp.{u}) (f : Nat) : Interp.{u} := { M with μ := table M f }
def field (f : Nat) : Expr Nat :=
  .pi (.const (f + 1) []) (.pi (.const (f + 1) []) (.const f []))
def later (f : Nat) : Expr Nat := .app (.const (f + 2) []) (.bvar 0)
def domains (f : Nat) : List (Expr Nat) := [field f, later f]
def shapes : List FieldShape := [.recursive 2, .nonrecursive]
def alias : PSet.{u} := sep (fun _ => False) (singleton datum)

theorem alias_equiv : Equiv (alias : PSet.{u}) pempty := by
  apply ext
  intro z
  constructor
  · intro hz
    obtain ⟨_, hf, _⟩ := mem_sep.mp hz
    exact hf.elim
  · intro hz
    exact (not_mem_pempty hz).elim

/-- Elementary proof-product computation. -/
theorem nested_empty (M : Interp.{u}) (z : PSet.{u})
    (hz : z ∈ Ed M (nested M)) : Equiv z pempty := by
  have hp : PiProp M (tyv domain) (fun _ => proofTy) := by
    intro _ _ y hy
    exact (mem_tv.mp (mem_congr_right (ed_tyv M (dich_tv True)) hy)).2
  have hi := ed_piVal_of_prop M hp
  have hP : PiProp M (tyv domain) (fun _ =>
      piVal M (tyv domain) (fun _ => proofTy)) := by
    intro _ _ y hy
    exact (mem_tv.mp (mem_congr_right hi hy)).2
  exact (mem_tv.mp (mem_congr_right (ed_piVal_of_prop M hP) hz)).2

theorem nested_member (M : Interp.{u}) : pempty ∈ Ed M (nested M) := by
  have hb : pempty ∈ Ed M (proofTy : PSet.{u}) :=
    mem_congr_right (ed_tyv M (dich_tv True)).symm (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  have hp : PiProp M (tyv domain) (fun _ => proofTy) := by
    intro _ _ y hy
    exact (mem_tv.mp (mem_congr_right (ed_tyv M (dich_tv True)) hy)).2
  have hi := ed_piVal_of_prop M hp
  have hmi : pempty ∈ Ed M (piVal M (tyv domain) (fun _ => proofTy)) :=
    mem_congr_right hi.symm (mem_tv.mpr ⟨fun _ _ => hb, Equiv.rfl⟩)
  have hP : PiProp M (tyv domain) (fun _ =>
      piVal M (tyv domain) (fun _ => proofTy)) := by
    intro _ _ y hy
    exact (mem_tv.mp (mem_congr_right hi hy)).2
  exact mem_congr_right (ed_piVal_of_prop M hP).symm
    (mem_tv.mpr ⟨fun _ _ => hmi, Equiv.rfl⟩)

theorem actual_erases (M : Interp.{u}) (f : Nat) (σ : Nat → Nat) :
    Erases (model M f) σ shapes (domains f) := by
  change (∀ ρ x, x ∈ Ed (model M f) (den (model M f) σ ρ (field f)) →
    Equiv x pempty) ∧ True
  refine ⟨?_, True.intro⟩
  intro ρ x hx
  have he : den (model M f) σ ρ (field f) = nested M := by
    have h1 : f + 1 ≠ f := by omega
    simp only [field, den, model, table, List.map_nil, if_neg h1, if_pos rfl]
    rfl
  rw [he] at hx
  exact nested_empty M x hx

theorem actual_fits (M : Interp.{u}) (f : Nat) (σ : Nat → Nat)
    (ρ : Nat → PSet.{u}) :
    TelFits (model M f) σ (domains f) ρ [alias, datum] := by
  have hz : (alias : PSet.{u}) ∈ Ed M (nested M) :=
    mem_congr_left alias_equiv.symm (nested_member M)
  have hf : (alias : PSet.{u}) ∈ Ed (model M f)
      (den (model M f) σ ρ (field f)) := by
    have h1 : f + 1 ≠ f := by omega
    simpa only [field, den, model, table, List.map_nil, if_neg h1, if_pos rfl,
      nested, piVal, PiProp, Ed] using hz
  change _ ∧ _ ∧ True
  refine ⟨hf, ?_, True.intro⟩
  have he : den (model M f) σ (vcons alias ρ) (later f) =
      fapp (lamVal M (nested M) (fun _ => tyv domain)) alias := by
    have h2 : f + 2 ≠ f := by omega
    have h21 : f + 2 ≠ f + 1 := by omega
    simp only [later, den, vcons, model, table, List.map_nil,
      if_neg h2, if_neg h21, if_pos rfl, ite_true]
  rw [he]
  have hb := beta_val M (b := fun _ => (tyv domain : PSet.{u}))
    (fun _ _ _ => Equiv.rfl) hz
  have hd : Dich (domain : PSet.{u}) :=
    Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
  exact mem_congr_right (ed_congr (model M f) hb).symm
    (mem_congr_right (ed_tyv (model M f) hd).symm (mem_singleton.mpr Equiv.rfl))

/-- A real tuple: the later field applies a function to the earlier
recursive proof. Its plain data value is retained by canonicalization. -/
theorem dependent_tuple (M : Interp.{u}) (f : Nat) (σ : Nat → Nat)
    (ρ : Nat → PSet.{u}) :
    TelFits (model M f) σ (domains f) ρ [pempty, datum] ∧
      ∀ es : List (Expr Nat), LEq (es.map (den (model M f) σ (push [alias, datum] ρ)))
        (es.map (den (model M f) σ (push [pempty, datum] ρ))) := by
  have h := canonical_tuple (model M f) σ shapes (domains f) (actual_erases M f σ)
    ρ [alias, datum] (actual_fits M f σ ρ)
  exact ⟨h.2.1, h.2.2⟩

/-- Erasing a plain field as well really breaks the dependent tuple. -/
theorem plain_erasure_refused (M : Interp.{u}) (f : Nat) (σ : Nat → Nat)
    (ρ : Nat → PSet.{u}) :
    ¬ TelFits (model M f) σ (domains f) ρ [pempty, pempty] := by
  intro hx
  have he : den (model M f) σ (vcons pempty ρ) (later f) =
      fapp (lamVal M (nested M) (fun _ => tyv domain)) pempty := by
    have h2 : f + 2 ≠ f := by omega
    have h21 : f + 2 ≠ f + 1 := by omega
    simp only [later, den, vcons, model, table, List.map_nil,
      if_neg h2, if_neg h21, if_pos rfl, ite_true]
  have h0 : pempty ∈ Ed (model M f) (den (model M f) σ (vcons pempty ρ) (later f)) := hx.2.1
  rw [he] at h0
  have hb := beta_val M (b := fun _ => (tyv domain : PSet.{u}))
    (fun _ _ _ => Equiv.rfl) (nested_member M)
  have hd : Dich (domain : PSet.{u}) :=
    Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
  have hn := mem_congr_right ((ed_congr (model M f) hb).trans
    (ed_tyv (model M f) hd)) h0
  exact dataVal_ne_pempty 7 [] (mem_singleton.mp hn).symm

/- Exact admission reader pins, including both literal aliases. These do
not assert a typed inductive group for this semantic field fixture. -/
kernel_rfl_theorem scanOne : fieldShapesFuel emptyEnv 32 1 0 0 0 0 (domains 1) = some shapes
kernel_rfl_theorem scanTwo : fieldShapesFuel emptyEnv 32 2 0 0 0 0 (domains 2) = some shapes
kernel_rfl_theorem scanRelabel : fieldShapesFuel emptyEnv 32 987 0 0 0 0 (domains 987) = some shapes
end Rcic.F3.PSet.PiPropPrefixAttack
