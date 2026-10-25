import rcic.RcicF3DBoundBridge
import rcic.RcicF3PropIota

/-!
# F3 class D: what `BoundDG` forces on the bound (the shape of the gap)

`BoundG` constrains the recursor's bound `K rr` only under `Prop` large
elimination (its third group clause); its first clause and `WalkB2` bound the
constructors' typings at the constructors' own instances `K (f + 1 + i)`.
`BoundDG` bounds every field's typing at the recursor's instances, so a field
headed by a constant `c` applied at a parameter level forces `K rr ≤ K c`
(`boundDG_rec_le_head`). Hence the shape of a `K` with `BoundG K` and not
`BoundDG K`: a universe-polymorphic group whose field is `c.{u} …` with
`K (f + 1 + i) ≤ K c < K rr` (the family not uniformly `Prop`). This is why
`boundDG_of_boundG` takes `RecBelowCtors` (`K rr ≤ K (f + 1 + i)`), and why no
`K' ≠ K` lowered at the recursors can stand in for it: `BoundG` is not
monotone under lowering a recursor's bound (the typings of later members, and
of later groups' constructors, may use the recursor at instances up to the
original bound), and the class-D induction needs `BoundG` and `BoundDG` at one
`K` (one `AllSound P μ K`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The instance vector of the family's arity with every entry at `b`
evaluates a parameter below the arity to `b`. -/
theorem evalTotal_param_replicate (n b j : Nat) (hj : j < n) :
    evalTotal (σOf (List.replicate n b)) (.param j) = b := by
  show σOf (List.replicate n b) j = b
  unfold σOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hj]
  rfl

/-- **`BoundDG` forces the recursor's bound below a field's head constant's.**
In a group with `BoundDG K`, a constructor field `c.{… param j …} args`
(`j` below the family's arity) has `K rr ≤ K c`. -/
theorem boundDG_rec_le_head (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {hE : EnvWfT E} {hfam : fm.mclass = .inductiveM}
    {hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM} {hrec : rm.mclass = .recursorM}
    {hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'}
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length)
    (k : Fin (node.a.constructorViews i).fields.length) (c : Nat) (ls : List Level) (args : List (Expr Nat))
    (hf : (node.a.constructorViews i).fields[k] = foldApps (.const c ls) args) (j : Nat)
    (hj : j < node.a.family.member.arity) (hl : Level.param j ∈ ls) : K rr ≤ K c := by
  obtain ⟨_, hDG⟩ := hD
  obtain ⟨l, d, hd⟩ := hDG node i (List.replicate node.a.family.member.arity (K rr)) (List.length_replicate _ _)
    (fun v hv => Nat.le_of_eq (List.eq_of_mem_replicate hv)) k
  obtain ⟨d', hd'⟩ := lokt_cast (σOf _) 4 K hf d hd
  have h := lok_spine_const (σOf (List.replicate node.a.family.member.arity (K rr))) 4 K c ls args d' hd' _ hl
  rw [evalTotal_param_replicate _ _ _ hj] at h
  exact h

end PSet

end Rcic.F3
