import rcic.RcicF3PiValueRule
/-! Adversarial normalized constructor equations: an inhabited self-loop
shape has no inductive proof; an empty-domain recursive constructor produces
an actual field tuple and family member. Labels are arbitrary naturals.
These are component fixtures, not a universal group theorem. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiValueRuleAttack
open Rcic.Declarative PiIndex PiValue PiValueRule

def emptyBase : Nat → List Nat → PSet.{4} := fun _ _ => tyv pempty

def loopCtor : Constructor := ⟨[.recursive [] []], []⟩

/-- The self-loop's shape is inhabited; refusal is not an empty-shape argument. -/
def loopShape (P : Premises4) :
    Shape P emptyBase (σOf []) [] [] loopCtor.fields ρ0 :=
  .recursive (fun _ => True.intro) (.nil _)

/-- A normalized self-loop has no inductive proof at any index. -/
theorem loop_refused (P : Premises4) (i : Index.{4}) :
    ¬ predicate P emptyBase [] [loopCtor] [] i := by
  intro h
  induction h with
  | sup s hg ih =>
    rcases s with ⟨⟨j, hj⟩, s⟩
    have hj0 : j = 0 := by
      change j < 1 at hj
      omega
    subst j
    cases s with
    | recursive guard tail => exact ih ⟨.here⟩ PUnit.unit

def emptyCtor (f : Nat) : Constructor := ⟨[.recursive [.const (f + 1) []] []], []⟩

/-- Empty normalized domains have no recursive branch address. -/
theorem empty_path_refused (P : Premises4) (f : Nat) (ρ : Nat → PSet.{4})
    (p : (PiIndex.tel (mkM P emptyBase) (σOf []) [.const (f + 1) []] [] ρ).tel.Path) :
    False := by
  have h := PiCompile.classValue_mem
    (Ed (mkM P emptyBase) (tyv (pempty : PSet.{4}))) p.1
  exact not_mem_pempty (mem_congr_right
    (ed_tyv (mkM P emptyBase) (Or.inl (fun _ h => (not_mem_pempty h).elim))) h)

/-- An empty-domain recursive constructor produces a proof without a base constructor. -/
theorem empty_produced (P : Premises4) (f : Nat) :
    predicate P emptyBase [] [emptyCtor f] [] (key []) := by
  let s : Shape P emptyBase (σOf []) [] [] (emptyCtor f).fields ρ0 :=
    .recursive (fun p => (empty_path_refused P f ρ0 p).elim) (.nil _)
  apply PiPropProducer.Valid.sup (S := signature P emptyBase (σOf []) [] [] [emptyCtor f] ρ0)
    ⟨⟨0, Nat.zero_lt_succ 0⟩, s⟩
  intro k p
  rcases k with ⟨k⟩
  cases k with
  | here => exact (empty_path_refused P f ρ0 p).elim
  | next _ k => cases k

/-- The positive fixture pays actual normalized field membership and the resulting family. -/
theorem empty_raw (P : Premises4) (f : Nat) :
    let φ := predicate P emptyBase [] [emptyCtor f]
    let M := mkM P (upd emptyBase f (table P emptyBase φ []))
    TelFits M (σOf []) [fieldExpr f [] (.recursive [.const (f + 1) []] [])] ρ0 [pempty] ∧
      pempty ∈ Ed M (den M (σOf []) ρ0 (.const f [])) := by
  dsimp only
  let φ := predicate P emptyBase [] [emptyCtor f]
  let X := table P emptyBase φ []
  let M := mkM P (upd emptyBase f X)
  have hd : ∀ e ∈ ([.const (f + 1) []] : List (Expr Nat)), occursConst f e = false := by
    intro e he
    have he' := List.mem_singleton.mp he
    subst e
    have hn : f + 1 ≠ f := by omega
    simp [occursConst, hn]
  have ha : ∀ e ∈ ([] : List (Expr Nat)), occursConst f e = false :=
    fun _ h => (List.not_mem_nil _ h).elim
  have hm := recursive_mem_iff P emptyBase f φ [] (σOf []) []
    [.const (f + 1) []] [] hd ha rfl ρ0 pempty
  refine ⟨⟨hm.mpr ⟨Equiv.rfl, fun p => (empty_path_refused P f ρ0 p).elim⟩, True.intro⟩, ?_⟩
  have he := PiIndependent.leaf_read P emptyBase f X (σOf []) [] [] ha ρ0
  change pempty ∈ Ed M (den M (σOf []) ρ0 (foldApps (.const f []) []))
  rw [he]
  exact (apply_mem_iff (mkM P emptyBase) (σOf []) (φ []) [] ρ0 [] rfl pempty).mpr
    ⟨True.intro, empty_produced P f, Equiv.rfl⟩

end Rcic.F3.PSet.PiValueRuleAttack
