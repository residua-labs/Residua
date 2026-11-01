import rcic.RcicF3PiCleanViews
import rcic.RcicF3Layout

/-!
# Admission-produced plans with the original recursive field syntax

The cache retains every normalized domain and the complete parameter/index
argument list. Its indices retain the original field and its position before
any motive, minor, or IH binder is inserted. Data is obtained by matching the
actual Option reader; admission supplies proofs, not selected witnesses.

The constructors are logical, noncomputable definitions. This suppresses
compiler-generated proof-erasure artifacts in the strict declaration
inventory; the kernel definitions still reduce through the actual reader.
No native executable cache is claimed.

The canonical cache uses the explicit `h14.fuelAt`. The stored minor is read
at its actual list position. `h12` supplies its derivation at a possibly
different fuel, as a proposition; no fuel is chosen from that existential.
This module does not change the production endpoint. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalPlan
open Rcic.Declarative

/-- An actual recursive reader result, in the original ordinary-field scope.
`arguments` includes the canonical parameters and every dependent index. -/
structure Recursive (E : ResolvedEnv) (fuel f nu np ni prior : Nat)
    (A : Expr Nat) (inner : Nat) : Type where
  domains : List (Expr Nat)
  arguments : List (Expr Nat)
  read : piTelescopeFuel E fuel A =
    some (domains, foldApps (.const f (canonL nu)) arguments)
  depth : domains.length = inner
  argument_count : arguments.length = np + ni
  parameter_prefix : ∃ indices : List (Expr Nat),
    arguments = policyParameterLocals np (prior + domains.length) ++ indices ∧
      indices.length = ni
  domains_free : ∀ e ∈ domains, occursConst f e = false
  arguments_free : ∀ e ∈ arguments, occursConst f e = false

/-- Original fields are kept even when no recursive argument is emitted. -/
inductive Field (E : ResolvedEnv) (fuel f nu np ni prior : Nat)
    (A : Expr Nat) : FieldShape → Type where
  | plain (free : occursConst f A = false) :
      Field E fuel f nu np ni prior A .nonrecursive
  | recursive {inner : Nat} (reader : Recursive E fuel f nu np ni prior A inner) :
      Field E fuel f nu np ni prior A (.recursive inner)

/-- The indices retain the complete original field order and original scope. -/
inductive Fields (E : ResolvedEnv) (fuel f nu np ni : Nat) :
    Nat → List FieldShape → List (Expr Nat) → Type where
  | nil (prior : Nat) : Fields E fuel f nu np ni prior [] []
  | cons {prior : Nat} {s : FieldShape} {A : Expr Nat}
      {ss : List FieldShape} {Fs : List (Expr Nat)}
      (head : Field E fuel f nu np ni prior A s)
      (tail : Fields E fuel f nu np ni (prior + 1) ss Fs) :
      Fields E fuel f nu np ni prior (s :: ss) (A :: Fs)

/-- Compare the actual reader output with admission's proof witnesses. This
is a proposition, so no existential syntax witness is selected as data. -/
theorem recursive_facts {E : ResolvedEnv} {fuel f nu np ni prior inner : Nat}
    {A b : Expr Nat} {idx ds : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni (np + prior) A =
      .permitted (.recursive inner) idx)
    (hr : piTelescopeFuel E fuel A = some (ds, b)) :
    b = foldApps (.const f (canonL nu)) (appsSpine b).2 ∧
    ds.length = inner ∧ (appsSpine b).2.length = np + ni ∧
    (∃ indices : List (Expr Nat),
      (appsSpine b).2 = policyParameterLocals np (prior + ds.length) ++ indices ∧
        indices.length = ni) ∧
    (∀ e ∈ ds, occursConst f e = false) ∧
    (∀ e ∈ (appsSpine b).2, occursConst f e = false) := by
  obtain ⟨ds₀, indices, hd, hi, hr₀⟩ := PiRawFieldViews.of_admitted h
  have he : (ds, b) = (ds₀, foldApps (.const f (canonL nu))
      (policyParameterLocals np (prior + ds₀.length) ++ indices)) :=
    Option.some.inj (hr.symm.trans hr₀)
  have hds : ds = ds₀ := congrArg Prod.fst he
  subst ds₀
  have hb : b = foldApps (.const f (canonL nu))
      (policyParameterLocals np (prior + ds.length) ++ indices) :=
    congrArg Prod.snd he
  have ha : (appsSpine b).2 =
      policyParameterLocals np (prior + ds.length) ++ indices := by
    rw [hb]
    simp only [appsSpine_foldApps, appsSpine, List.nil_append]
  have hb' : b = foldApps (.const f (canonL nu)) (appsSpine b).2 := by
    rw [ha]
    exact hb
  have hr' : piTelescopeFuel E fuel A =
      some (ds, foldApps (.const f (canonL nu)) (appsSpine b).2) :=
    hr.trans (congrArg some (congrArg (Prod.mk ds) hb'))
  have hf := (PiCleanViews.of_admitted h).recursive_frees hr'
  refine ⟨hb', hd, ?_, ⟨indices, ha, hi⟩, hf.1, hf.2⟩
  rw [ha, List.length_append, policyParameterLocals_length, hi]

/-- Type-valued extraction uses only the successful Option reader. -/
noncomputable def of_admitted {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni (np + prior) A = .permitted s idx) :
    Field E fuel f nu np ni prior A s := by
  cases s with
  | nonrecursive => exact .plain (fieldAnalyze_nonrec_free h)
  | recursive inner =>
      cases hr : piTelescopeFuel E fuel A with
      | none =>
          apply False.elim
          obtain ⟨ds, indices, _, _, hs⟩ := PiRawFieldViews.of_admitted h
          rw [hr] at hs
          cases hs
      | some result =>
          rcases result with ⟨ds, b⟩
          have hf := recursive_facts h hr
          exact .recursive {
            domains := ds
            arguments := (appsSpine b).2
            read := hr.trans (congrArg some (congrArg (Prod.mk ds) hf.1))
            depth := hf.2.1
            argument_count := hf.2.2.1
            parameter_prefix := hf.2.2.2.1
            domains_free := hf.2.2.2.2.1
            arguments_free := hf.2.2.2.2.2 }

/-- The complete original admitted list produces a cache at every slot. -/
noncomputable def of_fields {E : ResolvedEnv} {fuel f nu np ni : Nat} :
    ∀ (Fs : List (Expr Nat)) (prior : Nat) (ss : List FieldShape),
      fieldShapesFuel E fuel f nu np ni (np + prior) Fs = some ss →
      Fields E fuel f nu np ni prior ss Fs
  | [], prior, ss, h => by
      have he : ss = [] := (Option.some.inj h).symm
      subst ss
      exact .nil prior
  | A :: Fs, prior, ss, h => by
      cases ha : fieldAnalyze E fuel f nu np ni (np + prior) A with
      | unresolved =>
          simp only [fieldShapesFuel, ha] at h
          cases h
      | refused why =>
          simp only [fieldShapesFuel, ha] at h
          cases h
      | permitted s idx =>
          cases ht : fieldShapesFuel E fuel f nu np ni ((np + prior) + 1) Fs with
          | none =>
              simp only [fieldShapesFuel, ha, ht] at h
              cases h
          | some rest =>
              have he : ss = s :: rest := by
                simpa only [fieldShapesFuel, ha, ht, Option.bind_some, Option.map_some',
                  pure, Option.some.injEq] using h.symm
              subst ss
              have ht' : fieldShapesFuel E fuel f nu np ni (np + (prior + 1)) Fs =
                  some rest := by simpa only [Nat.add_assoc] using ht
              exact .cons (of_admitted ha) (of_fields Fs (prior + 1) rest ht')

theorem Fields.length {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : Fields E fuel f nu np ni prior ss Fs) : ss.length = Fs.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- The cached certificate projects to the existing proof-only reader view. -/
theorem Field.view {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape} (p : Field E fuel f nu np ni prior A s) :
    PiRawFieldViews.View E fuel f nu np ni prior A s := by
  cases p with
  | plain => trivial
  | @recursive inner r =>
      obtain ⟨indices, hp, hi⟩ := r.parameter_prefix
      refine ⟨r.domains, indices, r.depth, hi, ?_⟩
      rw [← hp]
      exact r.read

theorem Field.clean {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape} (p : Field E fuel f nu np ni prior A s) :
    PiCleanViews.Clean E fuel f nu np ni A s := by
  cases p with
  | plain hf => exact hf
  | recursive r =>
      exact ⟨r.domains, r.arguments, r.depth, r.argument_count, r.read,
        r.domains_free, r.arguments_free⟩

theorem Fields.views {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (p : Fields E fuel f nu np ni prior ss Fs) :
    PiRawFieldViews.Views E fuel f nu np ni prior ss Fs := by
  induction p with
  | nil prior => exact .nil prior
  | cons head _ ih => exact .cons head.view ih

/-- A constructor's cache and stored minor belong to this actual admitted
node. Result indices remain the original constructor view's expressions. -/
structure Constructor {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (j : Fin node.a.constructors.length) : Type where
  fuel : Nat
  fuel_admitted : fuel = node.h14.fuelAt j
  shapes : List FieldShape
  shapes_admitted : shapes = node.h14.shapesAt j
  analyzed : fieldShapesFuel node.E0 fuel node.a.family.ref node.a.family.member.arity
    node.a.family.parameters.length node.a.family.indices.length
    node.a.family.parameters.length (node.a.constructorViews j).fields = some shapes
  fields : Fields node.E0 fuel node.a.family.ref node.a.family.member.arity
    node.a.family.parameters.length node.a.family.indices.length 0 shapes
    (node.a.constructorViews j).fields
  minor : Expr Nat
  minor_stored : node.a.minorTypes[j.val]? = some minor
  minor_derivation : ∃ minorFuel : Nat,
    fieldShapesFuel node.E0 minorFuel node.a.family.ref node.a.family.member.arity
      node.a.family.parameters.length node.a.family.indices.length
      node.a.family.parameters.length (node.a.constructorViews j).fields = some shapes ∧
      derivedMinor node.a j minorFuel shapes = some minor

/-- This producer reads the actual minor list and both admission clauses.
The existential derivation fuel is retained in Prop, never selected as data. -/
noncomputable def constructorOfNode {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (j : Fin node.a.constructors.length) :
    Constructor node j := by
  have hj : j.val < node.a.minorTypes.length := by
    rw [node.a.minorCount]
    exact j.isLt
  let R := node.a.minorTypes[j.val]'hj
  have hstored : node.a.minorTypes[j.val]? = some R := List.getElem?_eq_getElem hj
  refine {
    fuel := node.h14.fuelAt j
    fuel_admitted := rfl
    shapes := node.h14.shapesAt j
    shapes_admitted := rfl
    analyzed := node.h14.analyzed j
    fields := of_fields (node.a.constructorViews j).fields 0 (node.h14.shapesAt j)
      (by simpa only [Nat.add_zero] using node.h14.analyzed j)
    minor := R
    minor_stored := hstored
    minor_derivation := ?_ }
  obtain ⟨shapes, fuel, hshapes, hderived⟩ := node.h12 j
  have hs : shapes = node.h14.shapesAt j :=
    fieldShapesFuel_agree node.E0 hshapes (node.h14.analyzed j)
  rw [hs] at hshapes hderived
  exact ⟨fuel, hshapes, hderived.trans hstored⟩

/-- Existential packing of actual typed admission data is ordinary Type data.
It does not pack a semantic soundness or evaluation-existence hypothesis. -/
structure Plan : Type where
  E : ResolvedEnv
  E' : ResolvedEnv
  f : Nat
  rr : Nat
  rm : CheckedMember
  node : RecNode E E' f rr rm
  constructors : (j : Fin node.a.constructors.length) → Constructor node j

noncomputable def ofNode {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) : Plan where
  E := E
  E' := E'
  f := f
  rr := rr
  rm := rm
  node := node
  constructors := constructorOfNode node

/-- The actual constructive group scan supplies the node; no choice from
the propositional `group_node` interface is involved. -/
noncomputable def ofGroup {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E)
    (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    Plan :=
  ofNode (groupNode hE hfam hctors hrec hmem).val

end Rcic.F3.PSet.EvalPlan
