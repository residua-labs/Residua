import rcic.RcicF3FamKTBridge

/-!
# F3: the `.fn` bridge obstruction transferred to `PsiF` — the realizability fixture

`RcicF3FamKTFnObstr` refutes fib-continuity at the guarded-W level (`GSig`,
`gphi`, `gSet`): the height-`ω` tree over a leaf-ful `.fn` signature with an
infinite function domain is valid but at no finite iterate stage.  The residue
`[rcic-f3-famkt-bridge-fn-cont]` (named in `RcicF3FamKTBridge` as
`FnContUnion`: pre-fixedness of the union of `PhiF`-iterates) stayed open as
"the transfer to a real `FamData`".  This module CLOSES that transfer:

**`fnContUnion_false`**: there is a concrete `FamData` (two constructors — a
leaf and a `.fn` node over an infinite domain), a concrete table `μ`, `σ`,
`ρp`, at which `¬ FnContUnion σ ρp` — the union of `PhiF`-iterates is NOT
pre-fixed.  The witness is the `PsiF`-level height-`ω` tree: its `.fn` field
value is a graph assigning to every domain element a finitely-staged child,
so it re-enters `PsiF` of the union, but no finite iterate contains it.

Method notes (why no axioms are needed):
- the only nonconstructive ingredient is the numeral-extraction section on
  the domain's element classes, taken from `Premises4.c0` (a *hypothesis*,
  never `Classical.choice`);
- strict staging is proved with *constant* children (the depth-extraction is
  needed only for unboundedness of the `ω`-graph, not for the staging ladder);
- `W4`-membership of the graph goes through the `Stage.image` closure, so the
  candidate set never needs to be a stage member.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet

open Rcic.Declarative

universe u v

/-! ### §0 helpers: `lift` through the finite ordinals -/

/-- Lifts of finite ordinals are the ordinals (by `mem`-transfer, with the
bound strengthened so the forward direction has every smaller instance). -/
theorem lift_ord : ∀ (n k : Nat), k ≤ n → Equiv (lift.{u, v} (ord k)) (ord k)
  | 0, k, hk => by
      have : k = 0 := Nat.le_zero.mp hk
      subst this
      apply ext; intro z
      constructor
      · intro hz
        obtain ⟨y, hy, _⟩ := mem_lift.mp hz
        exact (not_mem_pempty hy).elim
      · intro hz
        exact absurd hz not_mem_pempty
  | n + 1, k, hk => by
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · have hkn : k ≤ n := Nat.le_of_lt_succ hlt
        exact lift_ord n k hkn
      · have : k = n + 1 := Nat.le_antisymm hk hge
        subst this
        have ihn : ∀ j ≤ n, Equiv (lift.{u, v} (ord j)) (ord j) := fun j hj =>
          lift_ord n j hj
        apply ext; intro z
        constructor
        · intro hz
          obtain ⟨y, hy, hzy⟩ := mem_lift.mp hz
          obtain ⟨j, hj, hjy⟩ := ord_mem_iff.mp hy
          exact ord_mem_iff.mpr ⟨j, hj,
            hzy.trans ((lift_equiv hjy).trans (ihn j (Nat.le_of_lt_succ hj)))⟩
        · intro hz
          obtain ⟨j, hj, hjz⟩ := ord_mem_iff.mp hz
          exact mem_lift.mpr ⟨ord j, ord_mem_iff.mpr ⟨j, hj, Equiv.rfl⟩,
            hjz.trans (ihn j (Nat.le_of_lt_succ hj)).symm⟩

/-! ### §1 the realizability fixture

Two constructors: a leaf and a `.fn` node over an infinite domain.  The
domain is read from a table entry (`μ fxC [] = tyv fxS`), where `fxS` is the
lift of the set of finite ordinals — an infinite *small* set. -/

/-- The fixture's family ref (a fresh member number). -/
def fxF : Nat := 500

/-- The table entry carrying the infinite function domain. -/
def fxC : Nat := 501

/-- The positive finite ordinals, at universe `0`: infinite, pairwise
distinct, and `∅` is not among them (so `Dich` holds via the second
disjunct). -/
def fxDom0 : PSet.{0} := mk (ULift.{0} Nat) (fun n => ord (n.down + 1))

/-- The infinite domain as a small set of `PSet.{4}`. -/
def fxS : PSet.{4} := lift.{0, 4} fxDom0

/-- The fixture table: `fxC` carries the domain, everything else is inert. -/
def fxμ : Nat → List Nat → PSet.{4} := fun r _ => if r = fxC then tyv fxS else pempty

def fxσ : Nat → Nat := fun _ => 0

def fxρp : Nat → PSet.{4} := fun _ => pempty

/-- The node field: `Π y : dom, F`. -/
def fxA : Expr Nat := .pi (.const fxC []) (.const fxF [])

def fxLeaf : List (Expr Nat) × List (Expr Nat) := ([], [])

def fxNode : List (Expr Nat) × List (Expr Nat) := ([fxA], [])

def fxFd : FamData := ⟨fxF, [], [], .succ .zero, [fxLeaf, fxNode], .anySort⟩

theorem fxFd_ctors_len : fxFd.ctors.length = 2 := rfl

theorem fxFd_leaf : fxFd.ctors[0]? = some fxLeaf := rfl

theorem fxFd_node : fxFd.ctors[1]? = some fxNode := rfl

/-- The node field reads as `.fn`. -/
theorem fx_kind : kindOf fxF fxA = PKind.fn := by
  show (if occursConst fxF fxA = true then PKind.fn else PKind.plain) = PKind.fn
  rw [if_pos]
  decide

theorem fx_kinds : kindsOf fxF fxNode.1 = [PKind.fn] := by
  show [kindOf fxF fxA] = [PKind.fn]
  rw [fx_kind]

theorem fx_level : evalTotal fxσ fxFd.resLevel = 1 := rfl

/-- The stage bound of the fixture is the small universe. -/
theorem fx_bound : W4 (evalTotal fxσ fxFd.resLevel) = univIn.{0, 4} := rfl

/-- The domain's denotation. -/
theorem fx_den_dom (P : Premises4) (ρ : Nat → PSet.{4}) :
    den (mkM P fxμ) fxσ ρ (.const fxC []) = tyv fxS := rfl

/-! ### §2 the domain: an infinite small set -/

theorem ord_succ_not_pempty (n : Nat) : ¬ Equiv (ord (n + 1)) pempty := by
  intro h
  have h' : Equiv (ord (n + 1)) (ord (0 : Nat)) := h
  exact absurd (ord_inj h') (by omega)

/-- The domain is dichotomous via the second disjunct: `∅` is not among the
positive ordinals. -/
theorem fx_dich : Dich fxS := by
  right
  intro hz
  obtain ⟨y, hy, hzy⟩ := mem_lift.mp hz
  obtain ⟨a, hay⟩ := hy
  have hy' : Equiv y (ord (a.down + 1)) := hay.symm
  exact ord_succ_not_pempty a.down
    (hzy.trans ((lift_equiv hy').trans
      (lift_ord.{0, 4} (a.down + 1) (a.down + 1) (Nat.le_refl _)))).symm

theorem fx_Ed_eq (P : Premises4) : Ed (mkM P fxμ) (tyv fxS) = El (tyv fxS) :=
  ed_of_dich _ ((dich_congr el_tyv).mpr (fx_dich))

/-- The `.fn` domain read at the node field, position `0`. -/
def fxDomEF (P : Premises4) : PSet.{4} := domEF P fxμ fxσ fxρp fxNode.1 0 []

theorem fx_domEF_eq (P : Premises4) : fxDomEF P = El (tyv fxS) := by
  have h : fxDomEF P = Ed (mkM P fxμ) (tyv fxS) := rfl
  rw [h, fx_Ed_eq P]

theorem fx_domEF_mem (P : Premises4) : fxDomEF P ∈ W4 (evalTotal fxσ fxFd.resLevel) := by
  have hS : fxS ∈ univIn.{0, 4} := mem_univIn.mpr (small_lift.{0, 4} fxDom0)
  rw [fx_domEF_eq, fx_bound]
  exact mem_congr_left el_tyv.symm hS

/-- The `.fn` arm's branching domain. -/
def fxDomBig (P : Premises4) : PSet.{4} := domBigF P fxμ fxFd fxσ fxρp fxNode.1 0 []

theorem fx_domBig_eq (P : Premises4) : fxDomBig P = El (tyv fxS) := by
  have h : fxDomBig P = cond P.dec (fxDomEF P ∈ W4 (evalTotal fxσ fxFd.resLevel))
      (fxDomEF P) (singleton pempty) := rfl
  rw [h, cond_pos (fx_domEF_mem P)]
  exact fx_domEF_eq P

/-- Every element of the branching domain is a positive finite ordinal, and
conversely. -/
theorem fx_domBig_mem (P : Premises4) {z : PSet.{4}} :
    z ∈ fxDomBig P ↔ ∃ n, Equiv z (ord (n + 1)) := by
  rw [fx_domBig_eq]
  constructor
  · intro hz
    obtain ⟨y, hy, hzy⟩ := mem_lift.mp (mem_congr_right el_tyv hz)
    obtain ⟨a, hay⟩ := hy
    have hy' : Equiv y (ord (a.down + 1)) := hay.symm
    exact ⟨a.down, hzy.trans ((lift_equiv hy').trans
      (lift_ord.{0, 4} (a.down + 1) (a.down + 1) (Nat.le_refl _)))⟩
  · rintro ⟨n, hn⟩
    have hm : ord (n + 1) ∈ fxS :=
      mem_lift.mpr ⟨ord (n + 1), ⟨⟨n⟩, Equiv.refl _⟩,
        (lift_ord.{0, 4} (n + 1) (n + 1) (Nat.le_refl (n + 1))).symm⟩
    exact mem_congr_right el_tyv.symm (mem_congr_left hn.symm hm)

theorem fx_domBig_nonempty (P : Premises4) : ∃ z, z ∈ fxDomBig P :=
  ⟨ord 1, (fx_domBig_mem P).mpr ⟨0, Equiv.refl _⟩⟩

/-! ### §3 the staged trees

`fxT P n` is the depth-`n` witness tree: a leaf under a chain of constant
`graphOf`s over the infinite domain. -/
section Fixture

variable (P : Premises4)

def fxT : Premises4 → Nat → PSet.{4}
  | _, 0 => dataVal 0 []
  | P, n + 1 => dataVal 1 [graphOf (fxDomBig P) (fun _ => fxT P n)]

/-- Constant-argument graphs are literal images. -/
theorem fx_graph_const (A t : PSet.{4}) :
    graphOf A (fun _ => t) = sImage (fun a => ordPair a t) A := rfl

theorem fx_S (P : Premises4) : Stage (W4 (evalTotal fxσ fxFd.resLevel)) :=
  stageW4 P (evalTotal fxσ fxFd.resLevel)

theorem fx_fxS_mem (P : Premises4) : fxS ∈ W4 (evalTotal fxσ fxFd.resLevel) := by
  rw [fx_bound]
  exact mem_univIn.mpr (small_lift.{0, 4} fxDom0)

theorem fx_domBig_mem_W4 : fxDomBig P ∈ W4 (evalTotal fxσ fxFd.resLevel) := by
  rw [fx_domBig_eq]
  exact mem_congr_left el_tyv.symm (fx_fxS_mem P)

theorem fx_graph_const_mem (t : PSet.{4})
    (ht : t ∈ W4 (evalTotal fxσ fxFd.resLevel)) :
    graphOf (fxDomBig P) (fun _ => t) ∈ W4 (evalTotal fxσ fxFd.resLevel) := by
  have hA := fx_domBig_mem_W4 P
  rw [fx_graph_const]
  refine (fx_S P).image (fun a a' ha => ordPair_congr ha Equiv.rfl) hA ?_
  intro a ha
  exact (fx_S P).pair ((fx_S P).singleton_mem ((fx_S P).trans hA ha))
    ((fx_S P).pair ((fx_S P).trans hA ha) ht)

theorem fxT_mem_W4 (n : Nat) : fxT P n ∈ W4 (evalTotal fxσ fxFd.resLevel) := by
  induction n with
  | zero =>
      exact dataVal_mem_stage (fx_S P) 0 [] (fun x hx => absurd hx (List.not_mem_nil _))
  | succ n ih =>
      have hg := fx_graph_const_mem P (fxT P n) ih
      exact dataVal_mem_stage (fx_S P) 1 [graphOf (fxDomBig P) (fun _ => fxT P n)]
        (by
          intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; exact hg
          · exact absurd h (List.not_mem_nil _))

/-! #### the tuple reads -/

theorem fx_resTup (n : Nat) :
    Equiv (resTupF P fxμ fxFd fxσ fxρp (fxT P n)) (ordPair pempty pempty) := by
  cases n with
  | zero =>
      exact resTupF_dataVal P fxμ fxFd fxσ fxρp (hj := fxFd_leaf) (hl := rfl) (hz := Equiv.refl _)
  | succ m =>
      exact resTupF_dataVal P fxμ fxFd fxσ fxρp (hj := fxFd_node) (hl := rfl) (hz := Equiv.refl _)

theorem fx_recTup (y : PSet.{4}) :
    Equiv (recTupF P fxμ fxFd fxσ fxρp fxNode.1 0 [] y) (ordPair pempty pempty) := by
  have h1 : recTupF P fxμ fxFd fxσ fxρp fxNode.1 0 [] y
      = cond P.dec (fxDomEF P ∈ W4 (evalTotal fxσ fxFd.resLevel))
        (recTupAt P fxμ fxFd fxσ (vcons y (push [] fxρp)) (.const fxF []))
        (singleton pempty) := rfl
  have hfit : argsFitF P fxμ fxFd fxσ (vcons y (push [] fxρp)) (.const fxF []) := trivial
  have h2 : recTupAt P fxμ fxFd fxσ (vcons y (push [] fxρp)) (.const fxF [])
      = cond P.dec (argsFitF P fxμ fxFd fxσ (vcons y (push [] fxρp)) (.const fxF []))
        (ordPair pempty (tup ((familyIdx fxFd.params.length (.const fxF [])).map
          (den (mkM P fxμ) fxσ (vcons y (push [] fxρp))))))
        (singleton pempty) := rfl
  rw [h1, cond_pos (fx_domEF_mem P), h2, cond_pos hfit]
  exact Equiv.refl _

/-! #### `fapp` of a constant graph -/

theorem fapp_graph_const {A t y : PSet.{4}} (hy : y ∈ A) :
    Equiv (fapp (graphOf A (fun _ => t)) y) t := by
  obtain ⟨i0, hi0⟩ := hy
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨b, hb, hzb⟩ := mem_sUnion.mp hz
    obtain ⟨j, hjp, hjb⟩ := mem_sep.mp hb
    obtain ⟨i, hi⟩ := hjp
    have hbt : Equiv t b :=
      ((ordPair_equiv (hi :
        Equiv (ordPair (A.Func i) t)
          (ordPair y ((sUnion (sUnion (graphOf A (fun _ => t)))).Func j)))).2).trans hjb
    exact (equiv_iff_mem.mp hbt z).mpr hzb
  · intro hz
    have hmem : ordPair y t ∈ graphOf A (fun _ => t) := ⟨i0, ordPair_congr hi0 Equiv.rfl⟩
    have htp : t ∈ sep (fun b => ordPair y b ∈ graphOf A (fun _ => t))
        (sUnion (sUnion (graphOf A (fun _ => t)))) := by
      obtain ⟨ia, ha⟩ := mem_sUnion_sUnion_of_pair hmem
      exact mem_sep.mpr ⟨ia, mem_congr_left (ordPair_congr Equiv.rfl ha.symm) hmem, ha⟩
    exact mem_sUnion.mpr ⟨t, htp, hz⟩

theorem childAtV_graph_const {A t y : PSet.{4}} (hy : y ∈ A) :
    Equiv (childAtV A (graphOf A (fun _ => t)) y) t := by
  obtain ⟨i0, hi0⟩ := hy
  apply ext; intro z
  rw [childAtV_mem]
  constructor
  · rintro ⟨i, hi, hzi⟩
    exact mem_congr_right (fapp_graph_const (A := A) (t := t) ⟨i, Equiv.refl _⟩) hzi
  · intro hz
    refine ⟨i0, hi0, ?_⟩
    exact mem_congr_right (fapp_graph_const (A := A) (t := t) (y := A.Func i0)
      ⟨i0, Equiv.refl _⟩).symm hz

end Fixture

/-! ### §4 staging

`fxT P n` enters `iterPhi (n + 1)` but never `iterPhi n` — the constant
children pin the depth exactly. -/
section Staging

variable (P : Premises4)

theorem fxT_fib_mem {X y : PSet.{4}} {n : Nat} (h : fxT P n ∈ X) :
    fxT P n ∈ (semF P fxμ fxFd fxσ fxρp fxNode.1).fib X 0 [] y := by
  obtain ⟨i, hi⟩ := h
  refine mem_sep.mpr ⟨i, ?_, hi⟩
  exact (resTupF_congr P fxμ fxFd fxσ fxρp hi).trans
    ((fx_resTup P n).trans (fx_recTup P y).symm)

theorem fx_graph_mem_pi {X : PSet.{4}} {n : Nat} (h : fxT P n ∈ X) :
    graphOf (fxDomBig P) (fun _ => fxT P n) ∈
      piSet (fxDomBig P) ((semF P fxμ fxFd fxσ fxρp fxNode.1).fib X 0 []) :=
  graph_mem_piSet (fun x x' hx => (semF P fxμ fxFd fxσ fxρp fxNode.1).fib_resp X 0 [] hx)
    (fun _ => fxT P n) (fun _ => fxT_fib_mem P h)

/-- Membership in the one-step operator, at this fixture. -/
theorem fx_mem_PsiF_iff (P : Premises4) {X z : PSet.{4}} :
    z ∈ PsiF P fxμ fxFd fxσ fxρp X ↔
      z ∈ W4 (evalTotal fxσ fxFd.resLevel) ∧ ∃ (j : Fin 2) (xs : List PSet.{4}),
        Equiv z (dataVal j.val xs) ∧
        Sem.InPhi (semF P fxμ fxFd fxσ fxρp (fxFd.ctors.get j).1) X
          (kindsOf fxF (fxFd.ctors.get j).1) xs 0 [] := by
  constructor
  · intro hz
    obtain ⟨i, hj, hi⟩ := mem_sep.mp (mem_congr_right (PsiF_fin P fxμ fxFd fxσ fxρp X) hz)
    obtain ⟨j, xs, hia, hIn⟩ := hj
    exact ⟨⟨i, hi⟩, j, xs, hi.symm.trans hia, hIn⟩
  · rintro ⟨⟨i, hi⟩, j, xs, hia, hIn⟩
    exact mem_congr_right (PsiF_fin P fxμ fxFd fxσ fxρp X).symm
      (mem_sep.mpr ⟨i, ⟨j, xs, hi.trans hia, hIn⟩, hi⟩)

theorem fxT_mem_iter (P : Premises4) (n : Nat) :
    fxT P n ∈ iterPhi P fxμ fxFd (n + 1) fxσ fxρp := by
  cases n with
  | zero =>
      refine (fx_mem_PsiF_iff P).mpr ⟨fxT_mem_W4 P 0, ⟨⟨0, by omega⟩, [], ?_, trivial⟩⟩
      exact Equiv.refl _
  | succ m =>
      have ih := fxT_mem_iter P m
      have hg := fx_graph_mem_pi P (X := iterPhi P fxμ fxFd (m + 1) fxσ fxρp) (n := m) ih
      refine (fx_mem_PsiF_iff P).mpr ⟨fxT_mem_W4 P (m + 1),
        ⟨⟨1, by omega⟩, [graphOf (fxDomBig P) (fun _ => fxT P m)], ?_, ⟨hg, trivial⟩⟩⟩
      exact Equiv.refl _

theorem childAtV_congr_left {A F F' y : PSet.{4}} (h : Equiv F F') :
    Equiv (childAtV A F y) (childAtV A F' y) := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨i, hi, hzi⟩ := childAtV_mem.mp hz
    exact childAtV_mem.mpr ⟨i, hi, mem_congr_right (fapp_congr h Equiv.rfl) hzi⟩
  · intro hz
    obtain ⟨i, hi, hzi⟩ := childAtV_mem.mp hz
    exact childAtV_mem.mpr ⟨i, hi, mem_congr_right (fapp_congr h.symm Equiv.rfl) hzi⟩

theorem fxT_not_mem_iter (P : Premises4) (n : Nat) :
    fxT P n ∉ iterPhi P fxμ fxFd n fxσ fxρp := by
  induction n with
  | zero => exact fun hz => not_mem_pempty hz
  | succ m ih =>
      intro hz
      have h1 := (fx_mem_PsiF_iff P).mp
        (show fxT P (m + 1) ∈ PsiF P fxμ fxFd fxσ fxρp (iterPhi P fxμ fxFd m fxσ fxρp) from hz)
      obtain ⟨_, j, xs, hia, hIn⟩ := h1
      obtain ⟨jv, hjt⟩ := j
      have hj1 : 1 = jv := ord_inj (ordPair_equiv (ordPair_equiv hia).2).1
      subst hj1
      cases xs with
      | nil => exact hIn.elim
      | cons x' xs' =>
        cases xs' with
        | cons x'' xs'' => exact hIn.2
        | nil =>
          obtain ⟨hpi, _⟩ := hIn
          -- payload injectivity: the graph is `≈` the payload slot
          have hia' : Equiv (dataVal 1 [graphOf (fxDomBig P) (fun _ => fxT P m)])
              (dataVal 1 [x']) := hia
          have hlen : List.length [graphOf (fxDomBig P) (fun _ => fxT P m)] = List.length [x'] := rfl
          obtain ⟨_, hle⟩ := dataVal_inj hlen hia'
          obtain ⟨hgx, _⟩ := hle
          have hy : ord (1 : Nat) ∈ fxDomBig P := (fx_domBig_mem P).mpr ⟨0, Equiv.refl _⟩
          obtain ⟨hcv, _⟩ := childAtV_mem_fib (semF P fxμ fxFd fxσ fxρp fxNode.1)
            (X := iterPhi P fxμ fxFd m fxσ fxρp) (k := 0) (pre := [])
            (domB := fxDomBig P) hpi (y := ord (1 : Nat)) hy
          have hc : Equiv (childAtV (fxDomBig P) x' (ord (1 : Nat))) (fxT P m) :=
            (childAtV_congr_left hgx.symm).trans (childAtV_graph_const hy)
          exact ih (mem_congr_left hc hcv)

end Staging

/-! ### §5 the unbounded witness

The graph over the infinite domain whose child at the class of `ord (N+1)`
is pinned to the depth-`N+1` tree — so no finite iterate can contain it. -/
section Witness

variable (P : Premises4)

theorem fx_domBig_num {a : PSet.{4}} (ha : a ∈ fxDomBig P) :
    ∃ n : ULift.{1} Nat, Equiv a (ord (n.down + 1)) := by
  obtain ⟨n, hn⟩ := (fx_domBig_mem P).mp ha
  exact ⟨⟨n⟩, hn⟩

/-- The numeral of a domain element, read off by choice. -/
def fxNumOf (P : Premises4) (a : PSet.{4}) (ha : a ∈ fxDomBig P) : ULift.{1} Nat :=
  P.c0 (fun n : ULift.{1} Nat => Equiv a (ord (n.down + 1))) (fx_domBig_num P ha)

/-- The choice-property of `fxNumOf`, factored out. -/
theorem fxNumOf_prop (P : Premises4) (a : PSet.{4}) (ha : a ∈ fxDomBig P) :
    Equiv a (ord ((fxNumOf P a ha).down + 1)) :=
  (P.c0 (fun n : ULift.{1} Nat => Equiv a (ord (n.down + 1))) (fx_domBig_num P ha)).property

theorem fx_numOf_pinned (P : Premises4) {a : PSet.{4}} (ha : a ∈ fxDomBig P) {n : Nat}
    (hn : Equiv a (ord (n + 1))) : (fxNumOf P a ha).down = n :=
  Nat.succ_inj'.mp (ord_inj ((fxNumOf_prop P a ha).symm.trans hn))

theorem fx_numOf_congr (P : Premises4) {a b : PSet.{4}} (ha : a ∈ fxDomBig P)
    (hb : b ∈ fxDomBig P) (hab : Equiv a b) : fxNumOf P a ha = fxNumOf P b hb := by
  have hmm : (fxNumOf P a ha).down + 1 = (fxNumOf P b hb).down + 1 :=
    ord_inj ((fxNumOf_prop P a ha).symm.trans (hab.trans (fxNumOf_prop P b hb)))
  exact congrArg ULift.up (Nat.succ_inj'.mp hmm)

/-- Totalized numeral, read off by choice: on the domain it is pinned to the
true numeral, off the domain it is pinned to `0`. -/
def fxNumOfTPred (P : Premises4) (a : PSet.{4}) (n : ULift.{1} Nat) : Prop :=
  (a ∈ fxDomBig P → Equiv a (ord (n.down + 1))) ∧ (a ∉ fxDomBig P → n = ⟨0⟩)

theorem fxNumOfT_ex (P : Premises4) (a : PSet.{4}) : ∃ n, fxNumOfTPred P a n :=
  match P.dec (a ∈ fxDomBig P) with
  | isTrue hd => ⟨fxNumOf P a hd, ⟨fun _ => fxNumOf_prop P a hd, fun hmem => absurd hd hmem⟩⟩
  | isFalse hd => ⟨⟨0⟩, ⟨fun hmem => absurd hmem hd, fun _ => rfl⟩⟩

def fxNumOfT (P : Premises4) (a : PSet.{4}) : ULift.{1} Nat :=
  P.c0 (fxNumOfTPred P a) (fxNumOfT_ex P a)

theorem fxNumOfT_prop (P : Premises4) (a : PSet.{4}) : fxNumOfTPred P a (fxNumOfT P a) :=
  (P.c0 (fxNumOfTPred P a) (fxNumOfT_ex P a)).property

theorem fx_numOfT_pinned (P : Premises4) {a : PSet.{4}} (ha : a ∈ fxDomBig P) :
    (fxNumOfT P a).down = (fxNumOf P a ha).down :=
  Nat.succ_inj'.mp (ord_inj
    (((fxNumOfT_prop P a).1 ha).symm.trans (fxNumOf_prop P a ha)))

theorem fx_numOfT_congr (P : Premises4) {a b : PSet.{4}} (hab : Equiv a b) :
    fxNumOfT P a = fxNumOfT P b := by
  cases hA : P.dec (a ∈ fxDomBig P) with
  | isTrue ha =>
      have hb : b ∈ fxDomBig P := mem_congr_left hab ha
      have hmm : (fxNumOfT P a).down + 1 = (fxNumOfT P b).down + 1 :=
        ord_inj (((fxNumOfT_prop P a).1 ha).symm.trans
          (hab.trans ((fxNumOfT_prop P b).1 hb)))
      exact congrArg ULift.up (Nat.succ_inj'.mp hmm)
  | isFalse ha =>
      have hb' : b ∉ fxDomBig P := fun hb => ha (mem_congr_left hab.symm hb)
      have hz1 : fxNumOfT P a = ⟨0⟩ := (fxNumOfT_prop P a).2 ha
      have hz2 : fxNumOfT P b = ⟨0⟩ := (fxNumOfT_prop P b).2 hb'
      rw [hz1, hz2]

/-- The unbounded assignment: class `q` ↦ the staged tree at `q`'s numeral. -/
def fxhW (P : Premises4) : FBr (fxDomBig P) → PSet.{4} :=
  Quotient.lift
    (fun i => fxT P (fxNumOf P ((fxDomBig P).Func i) ⟨i, Equiv.refl _⟩).down)
    (fun a b hab => by
      have hc := fx_numOf_congr P (a := (fxDomBig P).Func a) (b := (fxDomBig P).Func b)
        ⟨a, Equiv.refl _⟩ ⟨b, Equiv.refl _⟩ hab
      exact congrArg (fun n : ULift.{1} Nat => fxT P n.down) hc)

theorem fx_hW_beta (i : (fxDomBig P).Idx) :
    fxhW P (Quotient.mk (FSetoid (fxDomBig P)) i)
      = fxT P (fxNumOfT P ((fxDomBig P).Func i)).down := by
  show fxT P (fxNumOf P ((fxDomBig P).Func i) ⟨i, Equiv.refl _⟩).down
      = fxT P (fxNumOfT P ((fxDomBig P).Func i)).down
  rw [fx_numOfT_pinned P ⟨i, Equiv.refl _⟩]

/-- The image-section presentation of the witness graph. -/
def fxSec (P : Premises4) (a : PSet.{4}) : PSet.{4} :=
  ordPair a (fxT P (fxNumOfT P a).down)

theorem fx_xW_eq_sImage :
    Equiv (graphOf (fxDomBig P) (fxhW P)) (sImage (fxSec P) (fxDomBig P)) := by
  have hf : (fun i : (fxDomBig P).Idx =>
        ordPair ((fxDomBig P).Func i) (fxhW P (Quotient.mk (FSetoid (fxDomBig P)) i)))
      = (fun i : (fxDomBig P).Idx => fxSec P ((fxDomBig P).Func i)) := by
    funext i
    rw [fx_hW_beta P i]
    rfl
  show Equiv (mk _ (fun i : (fxDomBig P).Idx => ordPair ((fxDomBig P).Func i)
      (fxhW P (Quotient.mk (FSetoid (fxDomBig P)) i))))
    (mk _ (fun i : (fxDomBig P).Idx => fxSec P ((fxDomBig P).Func i)))
  rw [hf]
  exact Equiv.refl _

theorem fx_xW_mem : graphOf (fxDomBig P) (fxhW P) ∈ W4 (evalTotal fxσ fxFd.resLevel) := by
  have hA := fx_domBig_mem_W4 P
  refine mem_congr_left (fx_xW_eq_sImage P).symm ((fx_S P).image ?_ hA ?_)
  · intro a a' ha
    refine ordPair_congr ha ?_
    rw [fx_numOfT_congr P ha]
    exact Equiv.refl _
  · intro a ha
    exact (fx_S P).pair ((fx_S P).singleton_mem ((fx_S P).trans hA ha))
      ((fx_S P).pair ((fx_S P).trans hA ha) (fxT_mem_W4 P _))

/-! #### `fapp` of a general graph -/

theorem fapp_graphOf {A : PSet.{4}} (h : FBr A → PSet.{4}) (i : A.Idx) :
    Equiv (fapp (graphOf A h) (A.Func i)) (h (Quotient.mk (FSetoid A) i)) := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨b, hb, hzb⟩ := mem_sUnion.mp hz
    obtain ⟨j, hjp, hjb⟩ := mem_sep.mp hb
    obtain ⟨k, hk⟩ := hjp
    obtain ⟨h1, h2⟩ := ordPair_equiv hk
    have hq : Quotient.mk (FSetoid A) k = Quotient.mk (FSetoid A) i := Quotient.sound h1
    rw [hq] at h2
    exact mem_congr_right (hjb.symm.trans h2.symm) hzb
  · intro hz
    have hmem : ordPair (A.Func i) (h (Quotient.mk (FSetoid A) i)) ∈ graphOf A h :=
      ⟨i, Equiv.refl _⟩
    have htp : h (Quotient.mk (FSetoid A) i) ∈
        sep (fun b => ordPair (A.Func i) b ∈ graphOf A h)
          (sUnion (sUnion (graphOf A h))) := by
      obtain ⟨ia, ha⟩ := mem_sUnion_sUnion_of_pair hmem
      exact mem_sep.mpr ⟨ia, mem_congr_left (ordPair_congr Equiv.rfl ha.symm) hmem, ha⟩
    exact mem_sUnion.mpr ⟨_, htp, hz⟩

theorem childAtV_graphOf {A : PSet.{4}} (h : FBr A → PSet.{4}) (i0 : A.Idx) :
    Equiv (childAtV A (graphOf A h) (A.Func i0)) (h (Quotient.mk (FSetoid A) i0)) := by
  apply ext; intro z
  rw [childAtV_mem]
  constructor
  · rintro ⟨j, hj, hzj⟩
    have hq : Quotient.mk (FSetoid A) j = Quotient.mk (FSetoid A) i0 := Quotient.sound hj
    exact mem_congr_right ((fapp_graphOf h j).trans (hq ▸ Equiv.refl _)) hzj
  · intro hz
    exact ⟨i0, Equiv.refl _, mem_congr_right (fapp_graphOf h i0).symm hz⟩

end Witness

/-! ### §6 the counter-model

The `ψ`-value `dataVal 1 [xW]` sits in `PsiF (iterPhiUnion)` but not in the
union itself: extracting its child at `ord (N + 1)` pins a depth-`N+1` tree
inside `iterPhi N`, contradicting strict staging. -/
section Counter

variable (P : Premises4)

def fxZW (P : Premises4) : PSet.{4} := dataVal 1 [graphOf (fxDomBig P) (fxhW P)]

theorem fxT_mem_iUnionN (n : Nat) :
    fxT P n ∈ iterPhiUnion P fxμ fxFd fxσ fxρp :=
  mem_iUnionN.mpr ⟨n, fxT_mem_iter P n⟩

theorem fx_xW_mem_pi :
    graphOf (fxDomBig P) (fxhW P) ∈
      piSet (fxDomBig P)
        ((semF P fxμ fxFd fxσ fxρp fxNode.1).fib (iterPhiUnion P fxμ fxFd fxσ fxρp) 0 []) := by
  refine graph_mem_piSet
    (fun x x' hx => (semF P fxμ fxFd fxσ fxρp fxNode.1).fib_resp _ 0 [] hx) _ ?_
  intro i
  rw [fx_hW_beta P i]
  exact fxT_fib_mem P (fxT_mem_iUnionN P (fxNumOfT P ((fxDomBig P).Func i)).down)

theorem fx_zW_mem_PsiF :
    fxZW P ∈ PsiF P fxμ fxFd fxσ fxρp (iterPhiUnion P fxμ fxFd fxσ fxρp) := by
  refine (fx_mem_PsiF_iff P).mpr ⟨?_, ⟨⟨1, by omega⟩, [_], Equiv.refl _,
    ⟨fx_xW_mem_pi P, trivial⟩⟩⟩
  refine dataVal_mem_stage (fx_S P) 1 [graphOf (fxDomBig P) (fxhW P)] ?_
  intro x hx
  cases hx with
  | head => exact fx_xW_mem P
  | tail _ ht => exact absurd ht (List.not_mem_nil _)

theorem fx_zW_not_mem : fxZW P ∉ iterPhiUnion P fxμ fxFd fxσ fxρp := by
  intro hz
  obtain ⟨N, hN⟩ := mem_iUnionN.mp hz
  have h1 := (fx_mem_PsiF_iff P).mp
    (show fxZW P ∈ PsiF P fxμ fxFd fxσ fxρp (iterPhi P fxμ fxFd N fxσ fxρp) from hN)
  obtain ⟨_, j, xs, hia, hIn⟩ := h1
  obtain ⟨jv, hjt⟩ := j
  have hj1 : 1 = jv := ord_inj (ordPair_equiv (ordPair_equiv hia).2).1
  subst hj1
  cases xs with
  | nil => exact hIn.elim
  | cons x' xs' =>
    cases xs' with
    | cons x'' xs'' => exact hIn.2
    | nil =>
      obtain ⟨hpi, _⟩ := hIn
      have hia' : Equiv (dataVal 1 [graphOf (fxDomBig P) (fxhW P)])
          (dataVal 1 [x']) := hia
      have hlen : List.length [graphOf (fxDomBig P) (fxhW P)] = List.length [x'] := rfl
      obtain ⟨_, hle⟩ := dataVal_inj hlen hia'
      obtain ⟨hxwx', _⟩ := hle
      have hy : ord (N + 1 : Nat) ∈ fxDomBig P :=
        (fx_domBig_mem P).mpr ⟨N, Equiv.refl _⟩
      obtain ⟨i0, hi0⟩ := id hy
      obtain ⟨hcv, _⟩ := childAtV_mem_fib (semF P fxμ fxFd fxσ fxρp fxNode.1)
        (X := iterPhi P fxμ fxFd N fxσ fxρp) (k := 0) (pre := [])
        (domB := fxDomBig P) hpi (y := ord (N + 1 : Nat)) hy
      have hp : (fxNumOf P ((fxDomBig P).Func i0) ⟨i0, Equiv.refl _⟩).down = N :=
        fx_numOf_pinned P ⟨i0, Equiv.refl _⟩ hi0
      have hcg : Equiv
          (childAtV (fxDomBig P) (graphOf (fxDomBig P) (fxhW P)) ((fxDomBig P).Func i0))
          (fxT P N) := by
        refine (childAtV_graphOf (fxhW P) i0).trans ?_
        show Equiv (fxT P (fxNumOf P ((fxDomBig P).Func i0) ⟨i0, Equiv.refl _⟩).down)
          (fxT P N)
        rw [hp]
        exact Equiv.refl _
      have hc : Equiv (childAtV (fxDomBig P) x' (ord (N + 1 : Nat))) (fxT P N) :=
        ((childAtV_congr hi0).symm.trans
          (childAtV_congr_left hxwx').symm).trans hcg
      exact fxT_not_mem_iter P N (mem_congr_left hc hcv)

/-! ### §7 the residue closes

`FnContUnion` fails at this fixture: the `.fn`-bridge counter-model at the
`PsiF` level.  Together with `fnW_diverges`/`fnContGSig_false`
(`RcicF3FamKTFnObstr`) this closes residue `[rcic-f3-famkt-bridge-fn-cont]`:
the `≥` direction of the `iterPhiUnion` bridge needs a `.fn`-freeness
hypothesis, and the two-stage counter-model (GSig-level obstruction + this
realizability fixture) is the witness that no strengthening of the statement
can drop it. -/

/-- **Residue closure** `[rcic-f3-famkt-bridge-fn-cont]`: `FnContUnion` is
refuted at a concrete fixture — `iterPhiUnion` is not `PsiF`-pre-fixed when a
constructor has a `.fn` field over an infinite small domain. -/
theorem fnContUnion_false (P : Premises4) :
    ¬ FnContUnion (P := P) (μ := fxμ) (fd := fxFd) fxσ fxρp := fun hsub =>
  fx_zW_not_mem P (hsub (fxZW P) (fx_zW_mem_PsiF P))

end Counter

end Rcic.F3.PSet
