import rcic.RcicF3EvalPropRecMem
import rcic.RcicIotaLegacyShapes

/-!
# The literal stable iota clause on singleton PendA groups

The current production IotaAt quantifies legacy IotaWitness values. A
witness's admitted shape row is exactly its legacy kinds mapped to
nonrecursive or recursive zero. A group with at most one constructor and
a positive-depth PendA field therefore has no such witness, in any common
extension of the admitted group. Prop/anySort selection supplies the
constructor bound; it does not exclude the family or its elements.

This proves the literal production IotaAt clause. It does not assert a
universal equation for IotaWitnessS or the higher-order shape schema. The
actual installed AccR indexed-IH equation is retained separately in the
composition module. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.EvalPropRecIota
open Rcic.Declarative Rcic.Model.PS

/-- Align only the constructor row consumed by the actual legacy witness.
The recursor and constructor entries must coexist in the same extension. -/
theorem witness_kinds {E E' Efin E'' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (node : RecNode E E' f rr rm)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E''.members r = some m → Efin.members r = some m)
    (w : IotaWitness E'') (hwr : w.recRef = rr) :
    ∃ j : Fin node.a.constructors.length,
      analyzeFields node.a.family.ref (node.a.constructorViews j).fields =
        some w.kinds := by
  have hrm : E'.members rr = some rm :=
    node.sub rr rm (members_extend_eq node.E0 rr rm)
  have hm : w.recMember = rm := by
    have h1 := hsub _ _ w.hrec
    have h3 : Efin.members w.recRef = some rm := by
      rw [hwr]
      exact hsubF _ _ hrm
    exact (Option.some.inj (h3.symm.trans h1)).symm
  obtain ⟨hnp, hnM, _, hfr⟩ := iota_align node.a w hwr hm
  have hjk : w.ctorIdx < node.a.constructors.length := by
    have := w.hidx
    omega
  let j : Fin node.a.constructors.length := ⟨w.ctorIdx, hjk⟩
  have hcref : w.ctorRef = node.a.family.ref + 1 + j.val := by
    rw [w.hctorIdx, hfr]
  have hcm : w.ctorMember = node.a.constructors[j.val] := by
    have h1 := hsub _ _ w.hctor
    have h2 := node.a.constructorsPresent j
    have h3 := hsubF _ _
      (node.sub _ _ (members_extend_preserved node.fresh _ _ h2))
    rw [hcref] at h1
    rw [h1] at h3
    exact Option.some.inj h3
  have hst := (node.a.constructorViews j).storedType
  have hcpl := (node.a.constructorViews j).parameterCount
  have hctm : w.ctorMember.mtype =
      policyPi ((node.a.constructorViews j).parameters ++
        (node.a.constructorViews j).fields)
        (foldApps (.const node.a.family.ref (policyFamilyLevels node.a.family))
          (policyParameterLocals (node.a.constructorViews j).parameters.length
            (node.a.constructorViews j).fields.length ++
              (node.a.constructorViews j).resultIndices)) := by
    rw [hcm]
    exact hst
  have hnpar := w.hnpar
  rw [hctm, piCount_policyPi,
    piCount_foldApps _ (fun _ _ h => Expr.noConfusion h),
    List.length_append] at hnpar
  have hpeel := w.hpeel
  rw [hctm, show w.nparams + w.fields.length =
      ((node.a.constructorViews j).parameters ++
        (node.a.constructorViews j).fields).length by
      rw [List.length_append]
      omega, peelPis_policyPi] at hpeel
  have hdoms : w.ctorDoms =
      (node.a.constructorViews j).parameters ++
        (node.a.constructorViews j).fields :=
    (congrArg Prod.fst (Option.some.inj hpeel)).symm
  have hkinds := w.hkinds
  rw [hdoms, hnp, ← hcpl, List.drop_left, hfr] at hkinds
  exact ⟨j, hkinds⟩

/-- An admitted witness row contains no positive-depth recursive shape.
This reuses the repository's complete legacy-to-shape agreement theorem. -/
theorem witness_row {E E' Efin E'' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (node : RecNode E E' f rr rm)
    (hFF : FamFreeBodies node.E0 node.a.family.ref)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E''.members r = some m → Efin.members r = some m)
    (w : IotaWitness E'') (hwr : w.recRef = rr) :
    ∃ j : Fin node.a.constructors.length,
      ∀ s, s ∈ node.h14.shapesAt j →
        s = .nonrecursive ∨ s = .recursive 0 := by
  obtain ⟨j, hk⟩ := witness_kinds node hsubF hsub w hwr
  have hop : ∀ ls, transparentBody node.E0 node.a.family.ref ls = none := by
    intro ls
    unfold transparentBody
    rw [node.a.family.present]
    show (if transparent node.a.family.member.mclass then _ else none) = none
    rw [node.a.family.hasClass]
    rfl
  have heq := fieldShapesFuel_eq_kinds hFF hop
    (node.a.constructorViews j).fields node.a.family.parameters.length hk
    (node.h14.analyzed j)
  refine ⟨j, fun s hs => ?_⟩
  rw [heq] at hs
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hs
  cases k with
  | plain => exact Or.inl rfl
  | directRec => exact Or.inr rfl

/-- The sole constructor cannot simultaneously have the PendA shape and
the legacy witness row. This is independent of the semantic table. -/
theorem no_witness {E E' Efin E'' : ResolvedEnv} {f rr : Nat}
    {rm fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hA : PendA node)
    (hsmall : node.a.constructors.length ≤ 1)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E''.members r = some m → Efin.members r = some m)
    (w : IotaWitness E'') (hwr : w.recRef = rr) : False := by
  have hFF : FamFreeBodies node.E0 node.a.family.ref := by
    rw [node.fam]
    exact famFreeBodies_node hE (groupMembersT_head_fresh hmem) hmem node
  obtain ⟨j, hj⟩ := witness_row node hFF hsubF hsub w hwr
  obtain ⟨i, k, m, ha⟩ := hA
  have hij : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
  have hs : FieldShape.recursive (m + 1) ∈ node.h14.shapesAt j := by
    rw [← hij]
    exact List.getElem?_mem ha
  rcases hj _ hs with h | h
  · exact FieldShape.noConfusion h
  · have hz : m + 1 = 0 := FieldShape.recursive.inj h
    omega

/-- The literal IotaAt clause, stable in every common extension, is
produced on the at-most-one-constructor PendA face. -/
theorem iota_at (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {E E' Efin : ResolvedEnv} {f rr : Nat}
    {rm fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hA : PendA node)
    (hsmall : node.a.constructors.length ≤ 1)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) :
    IotaAt P μ K Efin rr := by
  intro E'' hsub w hwr
  exact (no_witness hE hmem node hA hsmall hsubF hsub w hwr).elim

/-- Uniform Prop/anySort admission produces the constructor bound used by
the literal iota proof; no semantic or iota callback is assumed. -/
theorem iota_prop (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {E E' Efin : ResolvedEnv} {f rr : Nat}
    {rm fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hA : PendA node)
    (hProp : UniformProp node.a.family.resultLevel)
    (hpolicy : node.a.policy = .anySort)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) :
    IotaAt P μ K Efin rr :=
  iota_at P μ K hE hmem node hA
    (selection_prop node.a (fun _ => 0) (hProp _) hpolicy).2 hsubF

end Rcic.F3.PSet.EvalPropRecIota
