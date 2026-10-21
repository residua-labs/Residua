import rcic.RcicModelOps
import rcic.RcicSortLevelBridge

/-!
# RcicSemLevel — Model A sort layer (S0 slice M0)

`research/rcic/semantic/S0_MODEL_REDESIGN.md` §2.2, ruled S1 on #6760.

Sorts denote `Ω = 𝒫{∅}` at level value `0` and `U k` at `k + 1`, for an
abstract tower carrying only U1 (`Ω ∈ U k`) and U2 (`U j ∈ U k` for
`j < k`). Separation is by `mem_irrefl`; `eqN` is recovered from equality at
every total valuation through the landed `evalTotal_eq_iff_eqN`. Π-closure of
the tower (U3–U5) is slice M1 and is not assumed here; `stdTower` shows U1/U2
are satisfiable and is not a model tower.

No `Classical`. `closure_claim = 0`.
-/

namespace Rcic.Model.Sem

open Rcic.Model Rcic.Declarative

/-- Constructive truth values `Ω = 𝒫{∅}`. -/
def Omega : PS := PS.powerset (PS.singleton PS.pempty)

/-- The part of the universe tower that sort separation needs. -/
structure SortTower where
  U : Nat → PS
  omega_mem : ∀ k, Omega ∈ U k
  mem_of_lt : ∀ {j k : Nat}, j < k → U j ∈ U k

/-- The denotation of a sort whose level evaluates to `a`. -/
def sortCodeAt (T : SortTower) : Nat → PS
  | 0 => Omega
  | k + 1 => T.U k

/-- `⟦sort l⟧σ`. -/
def sortDen (T : SortTower) (σ : Nat → Nat) (l : Level) : PS :=
  sortCodeAt T (evalTotal σ l)

theorem not_equiv_of_mem {x y : PS} (h : x ∈ y) : ¬ PS.Equiv x y :=
  fun e => PS.mem_irrefl y (PS.mem_congr_left e h)

theorem sortCodeAt_inj (T : SortTower) :
    ∀ {a b : Nat}, PS.Equiv (sortCodeAt T a) (sortCodeAt T b) → a = b
  | 0, 0, _ => rfl
  | 0, k + 1, e => absurd e (not_equiv_of_mem (T.omega_mem k))
  | k + 1, 0, e => absurd e.symm (not_equiv_of_mem (T.omega_mem k))
  | j + 1, k + 1, e => by
      rcases Nat.lt_trichotomy j k with h | h | h
      · exact absurd e (not_equiv_of_mem (T.mem_of_lt h))
      · exact congrArg (· + 1) h
      · exact absurd e.symm (not_equiv_of_mem (T.mem_of_lt h))

theorem sortCodeAt_mem_succ (T : SortTower) :
    ∀ a : Nat, sortCodeAt T a ∈ sortCodeAt T (a + 1)
  | 0 => T.omega_mem 0
  | k + 1 => T.mem_of_lt (Nat.lt_succ_self k)

/-- Sort separation at one total valuation. -/
theorem evalTotal_eq_of_sortDen (T : SortTower) {σ : Nat → Nat} {u v : Level}
    (h : PS.Equiv (sortDen T σ u) (sortDen T σ v)) :
    evalTotal σ u = evalTotal σ v :=
  sortCodeAt_inj T h

/-- Equal sort denotations at every total valuation give `eqN`. -/
theorem eqN_of_sortDen (T : SortTower) {u v : Level}
    (h : ∀ σ, PS.Equiv (sortDen T σ u) (sortDen T σ v)) : eqN u v :=
  eqN_of_evalTotal_eq fun σ => evalTotal_eq_of_sortDen T (h σ)

/-- ConvT row 14 (`sorts`): `eqN` sorts denote equally. -/
theorem sortDen_congr_eqN (T : SortTower) {u v : Level} (h : eqN u v)
    (σ : Nat → Nat) : PS.Equiv (sortDen T σ u) (sortDen T σ v) := by
  have he : evalTotal σ u = evalTotal σ v := (evalTotal_eq_iff_eqN u v).mpr h σ
  unfold sortDen
  rw [he]
  exact PS.Equiv.refl _

theorem sortDen_equiv_iff_eqN (T : SortTower) (u v : Level) :
    (∀ σ, PS.Equiv (sortDen T σ u) (sortDen T σ v)) ↔ eqN u v :=
  ⟨eqN_of_sortDen T, sortDen_congr_eqN T⟩

/-- HasTyT `sort` arm: `⟦sort l⟧ ∈ ⟦sort (succ l)⟧`. -/
theorem sortDen_mem_succ (T : SortTower) (σ : Nat → Nat) (l : Level) :
    sortDen T σ l ∈ sortDen T σ (.succ l) :=
  sortCodeAt_mem_succ T (evalTotal σ l)

/-- The sortRow corollary shape (S0 §2.5), for any relation on levels whose
related sorts the soundness theorem denotes equally at every valuation. -/
theorem eqN_of_sortSound (T : SortTower) {R : Level → Level → Prop}
    (hR : ∀ {u v}, R u v → ∀ σ, PS.Equiv (sortDen T σ u) (sortDen T σ v))
    {u v : Level} (h : R u v) : eqN u v :=
  eqN_of_sortDen T (hR h)

/-! ### U1/U2 are satisfiable -/

/-- `{Ω}`, then von Neumann successors. Not Π-closed. -/
def stdU : Nat → PS
  | 0 => PS.singleton Omega
  | k + 1 => PS.insert (stdU k) (stdU k)

theorem omega_mem_stdU : ∀ k, Omega ∈ stdU k
  | 0 => PS.mem_singleton.mpr (PS.Equiv.refl _)
  | k + 1 => PS.subset_insert _ (omega_mem_stdU k)

theorem stdU_mem_succ (k : Nat) : stdU k ∈ stdU (k + 1) :=
  PS.mem_insert.mpr (Or.inl (PS.Equiv.refl _))

theorem stdU_subset_add (j : Nat) : ∀ d, PS.Subset (stdU j) (stdU (j + d))
  | 0 => PS.Subset.refl _
  | d + 1 => PS.Subset.trans (stdU_subset_add j d) PS.subset_insert

theorem stdU_mem_of_lt {j k : Nat} (h : j < k) : stdU j ∈ stdU k := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  have hs := stdU_subset_add (j + 1) d
  rw [hd] at hs
  exact hs _ (stdU_mem_succ j)

def stdTower : SortTower := ⟨stdU, omega_mem_stdU, stdU_mem_of_lt⟩

theorem stdTower_sort_zero_ne_one :
    ¬ PS.Equiv (sortDen stdTower (fun _ => 0) .zero)
        (sortDen stdTower (fun _ => 0) (.succ .zero)) :=
  fun e => absurd (evalTotal_eq_of_sortDen stdTower e) (by decide)

end Rcic.Model.Sem
