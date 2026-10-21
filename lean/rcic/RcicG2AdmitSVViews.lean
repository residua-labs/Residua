/-
RCIC 07 §3 — G2-S1: the policy views every `SV<d>` group admission reads.

Every `SV<d>` family is `natFamMember`'s shape (`Sort 1`, arity 0, no
parameter, no index) at its own ref, and every constructor field is a
closed `const` naming a `Sort 1` family (a sibling `SV<…>`, `BNat`, or the
group's own family for a self field) — so a constructor view is fixed by
its family ref and its field refs. `svCtors` has at most two fields per
constructor in every pin shape (`i64`/`list`/`str`/`bytes`/`pair`/`sum`,
and the two-field `record` pin), hence the 0/1/2-field views.
-/
import rcic.RcicG2AdmitBNat

namespace Rcic.G2
open Rcic.Declarative

/-- A `Sort 1` family with no parameter and no index at ref `f`. -/
def sortOneFamView (E : ResolvedEnv) (f : Nat) (h : E.members f = some natFamMember) :
    PolicyFamilyView E where
  ref := f
  member := natFamMember
  present := h
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def ctor0Member (f : Nat) : CheckedMember := ⟨.constructorM, 0, .const f [], none⟩

def ctor1Member (f g : Nat) : CheckedMember :=
  ⟨.constructorM, 0, .pi (.const g []) (.const f []), none⟩

def ctor2Member (f g₁ g₂ : Nat) : CheckedMember :=
  ⟨.constructorM, 0, .pi (.const g₁ []) (.pi (.const g₂ []) (.const f [])), none⟩

/-- `const g : Sort 1` for a `Sort 1` family at `g`, in any context. -/
def sortOneConstHasTy {E : ResolvedEnv} {Γ : LCtx} {g : Nat}
    (hg : E.members g = some natFamMember) :
    HasTy E 0 Γ (.const g []) (.sort (.succ .zero)) :=
  HasTy.const Γ g [] natFamMember hg rfl (fun _ hx => nomatch hx)

def ctor0View (E : ResolvedEnv) (f : Nat) (h : E.members f = some natFamMember) :
    PolicyConstructorView E (sortOneFamView E f h) (ctor0Member f) where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := .empty _ _
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

def ctor1View (E : ResolvedEnv) (f g : Nat) (h : E.members f = some natFamMember)
    (hg : E.members g = some natFamMember) :
    PolicyConstructorView E (sortOneFamView E f h) (ctor1Member f g) where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const g []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun | ⟨0, _⟩ => sortOneConstHasTy hg }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

def ctor2View (E : ResolvedEnv) (f g₁ g₂ : Nat) (h : E.members f = some natFamMember)
    (hg₁ : E.members g₁ = some natFamMember) (hg₂ : E.members g₂ = some natFamMember) :
    PolicyConstructorView E (sortOneFamView E f h) (ctor2Member f g₁ g₂) where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const g₁ [], .const g₂ []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun
      | ⟨0, _⟩ => sortOneConstHasTy hg₁
      | ⟨1, _⟩ => sortOneConstHasTy hg₂ }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ hx => nomatch hx

/-- every field of these views lives in `Sort 1`, the family's own sort. -/
theorem ctor1Universe (E : ResolvedEnv) (f g : Nat) (h : E.members f = some natFamMember)
    (hg : E.members g = some natFamMember) :
    FieldUniverseAdmitted (ctor1View E f g h hg)
  | ⟨0, _⟩ => Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

theorem ctor2Universe (E : ResolvedEnv) (f g₁ g₂ : Nat) (h : E.members f = some natFamMember)
    (hg₁ : E.members g₁ = some natFamMember) (hg₂ : E.members g₂ = some natFamMember) :
    FieldUniverseAdmitted (ctor2View E f g₁ g₂ h hg₁ hg₂)
  | ⟨0, _⟩ => Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
  | ⟨1, _⟩ => Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

end Rcic.G2
