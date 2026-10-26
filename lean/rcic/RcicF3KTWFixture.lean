import rcic.RcicF3KTWRecMem
import rcic.RcicTypedFunRecPins

/-!
# The W fixture: every `famKT_fix` premise discharged for the function-recursive W group.
-/

namespace Rcic.F3.PSet

open Rcic.Declarative

noncomputable section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4})

/-- `W`'s single constructor's fields are class A: `wFieldA` family-free,
`wFieldF` a `FnRec` at `d = 1` with domain `wFieldA` and no index args. -/
theorem w_fieldsClassA : ∀ c, c ∈ (famDataOf wGroupAdmitted).ctors →
    FieldsClassA (famDataOf wGroupAdmitted).fref
      wGroupAdmitted.family.member.arity (famDataOf wGroupAdmitted).params.length
      (famDataOf wGroupAdmitted).indices.length c.1 0 := by
  intro c hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  obtain ⟨i, hi⟩ := i
  have hc1 : wGroupAdmitted.constructors = [wSupMember] := rfl
  have : i = 0 := by rw [hc1] at hi; simp at hi; omega
  subst this
  show FieldsClassA _ _ _ _ [wFieldA, wFieldF] 0
  exact ⟨Or.inl rfl, Or.inr (Or.inr ⟨wFieldA, [], rfl, rfl, rfl,
    fun e he => nomatch he⟩), trivial⟩

/-- `FamBounded` for `W` — every expression is closed below arity 0. -/
theorem w_bounded : FamBounded (famDataOf wGroupAdmitted)
    wGroupAdmitted.family.member.arity where
  params := fun e he => nomatch (List.not_mem_nil _ he)
  indices := fun e he => nomatch (List.not_mem_nil _ he)
  res := rfl
  ctors := fun c hc => by
    obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
    obtain ⟨i, hi⟩ := i
    have hc1 : wGroupAdmitted.constructors = [wSupMember] := rfl
    have : i = 0 := by rw [hc1] at hi; simp at hi; omega
    subst this
    constructor
    · intro e he
      show exprLevelsBounded wGroupAdmitted.family.member.arity e = true
      have hf : (wGroupAdmitted.constructorViews ⟨0, hi⟩).fields = [wFieldA, wFieldF] := rfl
      rw [hf, List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · rw [List.mem_singleton] at he
        subst e
        rfl
    · intro e he
      have hri : (wGroupAdmitted.constructorViews ⟨0, by omega⟩).resultIndices = [] := rfl
      exact absurd he (by rw [hri]; exact List.not_mem_nil e)

/-- `W`'s parameters and indices are empty, hence family-free. -/
theorem w_famFree : ∀ e, e ∈ (famDataOf wGroupAdmitted).params ++
    (famDataOf wGroupAdmitted).indices →
    occursConst (famDataOf wGroupAdmitted).fref e = false :=
  fun e he => nomatch (List.not_mem_nil _ he)

/-- `W`'s result indices are empty, hence family-free. -/
theorem w_ri : ∀ c, c ∈ (famDataOf wGroupAdmitted).ctors → ∀ e, e ∈ c.2 →
    occursConst (famDataOf wGroupAdmitted).fref e = false := by
  intro c hc e he
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  obtain ⟨i, hi⟩ := i
  have hc1 : wGroupAdmitted.constructors = [wSupMember] := rfl
  have : i = 0 := by rw [hc1] at hi; simp at hi; omega
  subst this
  have hri : (wGroupAdmitted.constructorViews ⟨0, by omega⟩).resultIndices = [] := rfl
  exact absurd he (by rw [hri]; exact List.not_mem_nil e)

/-- `fref ≠ 1,2` from the member kinds at refs 1,2: the family member is
`.inductiveM`, so the family ref cannot coincide with a ref whose member has
any other class. -/
theorem hf_of_members {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (h1 : ∀ m1, E.members 1 = some m1 → m1.mclass ≠ .inductiveM)
    (h2 : ∀ m2, E.members 2 = some m2 → m2.mclass ≠ .inductiveM) :
    (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : a.family.ref = 1 := h
    have hp := a.family.present
    rw [h'] at hp
    exact h1 _ hp a.family.hasClass
  · have h' : a.family.ref = 2 := h
    have hp := a.family.present
    rw [h'] at hp
    exact h2 _ hp a.family.hasClass

/-- `fref ≠ 1,2` at a Nat core prefix: refs 1,2 are the Nat constructors. -/
theorem hf_of_natPrefix {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (h1 : E.members 1 = some natZeroMember) (h2 : E.members 2 = some natSuccMember) :
    (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2 :=
  hf_of_members a
    (fun m1 hm => by rw [h1] at hm; cases hm; intro c; cases c)
    (fun m2 hm => by rw [h2] at hm; cases hm; intro c; cases c)

/-- `W`'s reference is 4. -/
theorem w_hf : (famDataOf wGroupAdmitted).fref ≠ 1 ∧ (famDataOf wGroupAdmitted).fref ≠ 2 :=
  hf_of_natPrefix wGroupAdmitted rfl rfl

/-- `W`'s result-index lengths hold. -/
theorem w_hres : ∀ c, c ∈ (famDataOf wGroupAdmitted).ctors →
    c.2.length = (famDataOf wGroupAdmitted).indices.length :=
  hres_of_admitted wGroupAdmitted

/-- `W`'s `NonIRSem`: at `k = 0` the prefixes are empty; at `k = 1` the
`LEq` reduces to `x ≈ x'` and `den_congr` closes both clauses. -/
theorem w_nonIR : ∀ σ ρp (j : Fin (famDataOf wGroupAdmitted).ctors.length),
    NonIRSem P μ σ ρp (famDataOf wGroupAdmitted).fref
      ((famDataOf wGroupAdmitted).ctors.get j).1 := by
  intro σ ρp j
  obtain ⟨j, hj⟩ := j
  have hc1 : wGroupAdmitted.constructors = [wSupMember] := rfl
  have : j = 0 := by
    rw [famDataOf_ctors_length] at hj
    rw [hc1] at hj; simp at hj; omega
  subst this
  show NonIRSem P μ σ ρp _ [wFieldA, wFieldF]
  intro k hk pre pre' hl hl' hle
  rcases k with _ | _ | k
  · have : pre = [] := List.length_eq_zero.mp hl
    subst this
    have : pre' = [] := List.length_eq_zero.mp hl'
    subst this
    exact ⟨Equiv.refl _, Equiv.refl _⟩
  · obtain ⟨x, rfl⟩ : ∃ x, pre = [x] := by
      match pre, hl with | [x], _ => exact ⟨x, rfl⟩
    obtain ⟨x', rfl⟩ : ∃ x', pre' = [x'] := by
      match pre', hl' with | [x'], _ => exact ⟨x', rfl⟩
    show Equiv (den (mkM P μ) σ (push [x] ρp) (fieldAt [wFieldA, wFieldF] 1))
        (den (mkM P μ) σ (push [x'] ρp) (fieldAt [wFieldA, wFieldF] 1)) ∧
      Equiv (den (mkM P μ) σ (push [x] ρp) (piDom (fieldAt [wFieldA, wFieldF] 1)))
        (den (mkM P μ) σ (push [x'] ρp) (piDom (fieldAt [wFieldA, wFieldF] 1)))
    have hxx' : Equiv x x' := hle.1
    have hρ : ∀ i, Equiv ((push [x] ρp) i) ((push [x'] ρp) i) :=
      fun i => vcons_congr hxx' (fun _ => Equiv.rfl) i
    exact ⟨den_congr (mkM P μ) σ _ hρ, den_congr (mkM P μ) σ _ hρ⟩
  · have : [wFieldA, wFieldF].length = 2 := rfl
    exact absurd hk (by omega)

/-- `W`'s result level is nonzero (`Sort 1`). -/
theorem w_type : ∀ σ, evalTotal σ (famDataOf wGroupAdmitted).resLevel ≠ 0 := by
  intro σ
  exact Nat.succ_ne_zero _

/-- `W` satisfies the `famKT` fixed point at every instance. -/
theorem w_famKT_fix (vs : List Nat) :
    Equiv (famVal (mkM P (upd μ (famDataOf wGroupAdmitted).fref
        (famKT P μ (famDataOf wGroupAdmitted)))) W4 (σOf vs)
        (famDataOf wGroupAdmitted))
      (famKT P μ (famDataOf wGroupAdmitted) vs) :=
  famKT_fix P μ (famDataOf wGroupAdmitted) wGroupAdmitted.family.member.arity
    (w_nonIR P μ) w_bounded w_famFree w_fieldsClassA w_ri w_hres w_hf vs

end

end Rcic.F3.PSet
