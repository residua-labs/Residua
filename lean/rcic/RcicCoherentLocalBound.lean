import Std

/-!
# Finite control: a two-step bound on both local legs does not imply confluence

This is an abstract five-vertex graph, not an admitted native RCIC
countermodel. Its proper edges are:

  `a -> b,c`, `b -> a,x`, `c -> a,y`.

Every vertex also has a reflexive edge. The vertices `x` and `y` are
absorbing. Every ordered local peak has a join with at most two steps
on each leg. At the three nontrivial forks, the joins are:

  `b <- a -> c`: join at `a` in one step on each side;
  `a <- b -> x`: join at `x` in two steps and zero steps;
  `a <- c -> y`: join at `y` in two steps and zero steps.

Nevertheless, `a -> b -> x` and `a -> c -> y` cannot join. Thus even a
bound of two on BOTH local joining legs cannot support a general
confluence consumer without additional hypotheses. In particular it
cannot replace the right-at-most-one premise of the structural strip
proof merely by changing the numeric bound to two.

Paths are ordinary lists of successive vertices. `Walk` checks adjacent
edges and the endpoint; no native step, certificate, star, decoration,
or closure is redefined. Taking the decoration set at every vertex to
be `Unit` makes every source, target, and adjacency decoration equation
automatic. Hence adding those equalities to an abstract local-star
contract does not remove this counterexample.

All witnesses are explicit finite lists. No choice, termination of the
graph, native oracle, or unproved proposition is used.

Only the three closed control theorems are public. The private graph is
an abstract consumer countercheck, with `closure_claim = 0` for native RCIC.
-/

namespace RcicCoherentLocalBound

private inductive Vertex where
  | a | b | c | x | y
  deriving DecidableEq, Repr


/-- The reflexive adjacency table for the five-vertex control graph. -/
private def edge : Vertex → Vertex → Bool
  | .a, .a | .a, .b | .a, .c => true
  | .b, .a | .b, .b | .b, .x => true
  | .c, .a | .c, .c | .c, .y => true
  | .x, .x | .y, .y => true
  | _, _ => false

private abbrev Edge (u v : Vertex) : Prop := edge u v = true

/-- The list contains successive targets of edges beginning at `u`.
The empty list is the zero-step path, with endpoint `u`. -/
private def Walk : Vertex → Vertex → List Vertex → Prop
  | u, v, [] => u = v
  | u, v, w :: ws => Edge u w ∧ Walk w v ws

/-- Reachability expressed by an ordinary finite list witness. -/
private def Reaches (u v : Vertex) : Prop := ∃ ws : List Vertex, Walk u v ws

/-- A fixed centre for every local peak with the indicated source. -/
private def centre : Vertex → Vertex
  | .a => .a
  | .b => .x
  | .c => .y
  | .x => .x
  | .y => .y

/-- Explicit short path from each successor to its source's chosen centre.
Entries for nonedges are irrelevant and use the empty list. -/
private def repair : Vertex → Vertex → List Vertex
  | .a, .b | .a, .c => [.a]
  | .b, .a => [.b, .x]
  | .b, .b => [.x]
  | .c, .a => [.c, .y]
  | .c, .c => [.y]
  | _, _ => []

private theorem edge_reflexive (u : Vertex) : Edge u u := by
  cases u <;> decide

/-- Every original edge target reaches its source's selected centre along
the concrete lookup-table path. This covers reflexive edges as well. -/
private theorem repair_valid (u v : Vertex) (h : Edge u v) :
    Walk v (centre u) (repair u v) := by
  cases u <;> cases v <;> simp_all [Edge, edge, Walk, centre, repair]

private theorem repair_length_le_two (u v : Vertex) : (repair u v).length ≤ 2 := by
  cases u <;> cases v <;> decide

/-- Every ORDERED local peak has two explicit joining lists, each of
length at most two. No side is selected by an unspecified disjunction. -/
theorem local_peaks_join_in_two (u v w : Vertex)
    (hv : Edge u v) (hw : Edge u w) :
    ∃ (z : Vertex) (left right : List Vertex),
      Walk v z left ∧ left.length ≤ 2 ∧
      Walk w z right ∧ right.length ≤ 2 :=
  ⟨centre u, repair u v, repair u w,
    repair_valid u v hv, repair_length_le_two u v,
    repair_valid u w hw, repair_length_le_two u w⟩

private theorem x_absorbing (v : Vertex) (h : Edge .x v) : v = .x := by
  cases v <;> simp_all [Edge, edge]

private theorem y_absorbing (v : Vertex) (h : Edge .y v) : v = .y := by
  cases v <;> simp_all [Edge, edge]

/-- A walk from an absorbing vertex remains there. Induction is on the
literal list of successive vertices, not on generated paths. -/
private theorem walk_from_absorbing (u : Vertex)
    (hu : ∀ v : Vertex, Edge u v → v = u)
    (ws : List Vertex) : ∀ v : Vertex, Walk u v ws → v = u := by
  induction ws with
  | nil =>
      intro v h
      exact h.symm
  | cons w ws ih =>
      intro v h
      have hw : w = u := hu w h.1
      subst w
      exact ih v h.2

private theorem a_to_x : Walk .a .x [.b, .x] := by simp [Walk, Edge, edge]

private theorem a_to_y : Walk .a .y [.c, .y] := by simp [Walk, Edge, edge]

/-- The two absorbing vertices have no common endpoint along any two
finite lists, with no bound imposed on either list. -/
private theorem no_walk_join_x_y :
    ¬ ∃ (z : Vertex) (left right : List Vertex), Walk .x z left ∧ Walk .y z right := by
  intro h
  obtain ⟨z, left, right, hl, hr⟩ := h
  have hx : z = .x := walk_from_absorbing .x x_absorbing left z hl
  have hy : z = .y := walk_from_absorbing .y y_absorbing right z hr
  have hxy : (show Vertex from .x) = .y := hx.symm.trans hy
  cases hxy

private theorem no_reachable_join_x_y : ¬ ∃ z : Vertex, Reaches .x z ∧ Reaches .y z := by
  intro h
  obtain ⟨z, ⟨left, hl⟩, ⟨right, hr⟩⟩ := h
  exact no_walk_join_x_y ⟨z, left, right, hl, hr⟩

/-- Explicit fork from one vertex to two unjoinable finite endpoints. -/
theorem finite_nonconfluence_witness :
    Reaches .a .x ∧ Reaches .a .y ∧ ¬ ∃ z : Vertex, Reaches .x z ∧ Reaches .y z :=
  ⟨⟨[.b, .x], a_to_x⟩, ⟨[.c, .y], a_to_y⟩, no_reachable_join_x_y⟩

/-- Local joining with the displayed bound does not make this graph
confluent. This is an abstract countercheck on a proposed consumer. -/
theorem not_confluent :
    ¬ (∀ u v w : Vertex, Reaches u v → Reaches u w →
      ∃ z : Vertex, Reaches v z ∧ Reaches w z) := by
  intro h
  exact no_reachable_join_x_y (h .a .x .y ⟨[.b, .x], a_to_x⟩ ⟨[.c, .y], a_to_y⟩)

#print axioms local_peaks_join_in_two
#print axioms finite_nonconfluence_witness
#print axioms not_confluent

end RcicCoherentLocalBound
