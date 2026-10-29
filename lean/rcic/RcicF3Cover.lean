import rcic.RcicF3Bridge
import rcic.RcicF3WhnfSyn

/-!
# F3 coverage: every axiom-free admitted environment falls in a named class

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (groupMembersT_preserve)

namespace PSet

/-! ### the per-field clause of `RecFieldsDirect` -/

/-- `RecFieldsDirect`'s clause at one field (depth `d`). -/
def DirectClause (f : Nat) (lsF : List Level) (np nq d : Nat) (A : Expr Nat) : Prop :=
  occursConst f A = false ∨ ∃ idx : List (Expr Nat),
    A = foldApps (.const f lsF) (policyParameterLocals np d ++ idx) ∧ idx.length = nq ∧
      ∀ e, e ∈ idx → occursConst f e = false

theorem recFieldsDirect_of_clauses {f : Nat} {lsF : List Level} {np nq : Nat} :
    (Fs : List (Expr Nat)) → (d : Nat) →
    (∀ k A, Fs[k]? = some A → DirectClause f lsF np nq (d + k) A) → RecFieldsDirect f lsF np nq Fs d
  | [], _, _ => trivial
  | A :: Fs, d, h => ⟨h 0 A (by simp), recFieldsDirect_of_clauses Fs (d + 1) fun k B hk => by
      have := h (k + 1) B (by simpa using hk)
      rwa [show d + (k + 1) = d + 1 + k by omega] at this⟩

theorem clauses_of_recFieldsDirect {f : Nat} {lsF : List Level} {np nq : Nat} :
    (Fs : List (Expr Nat)) → (d : Nat) → RecFieldsDirect f lsF np nq Fs d →
    ∀ k A, Fs[k]? = some A → DirectClause f lsF np nq (d + k) A
  | [], _, _, k, A, h => by simp at h
  | B :: Fs, d, ⟨hB, hFs⟩, 0, A, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; exact hB
  | B :: Fs, d, ⟨_, hFs⟩, k + 1, A, h => by
      simp only [List.getElem?_cons_succ] at h
      have := clauses_of_recFieldsDirect Fs (d + 1) hFs k A h
      rwa [show d + 1 + k = d + (k + 1) by omega] at this

/-! ### shapes read off admission -/

/-- A field the admission analysis classifies `nonrecursive` is syntactically family-free. -/
theorem shapes_nonrec_free (E : ResolvedEnv) (fuel fam nu np nq : Nat) :
    (Ts : List (Expr Nat)) → (depth : Nat) → (shapes : List FieldShape) →
    fieldShapesFuel E fuel fam nu np nq depth Ts = some shapes →
    ∀ (k : Nat) (T : Expr Nat), shapes[k]? = some FieldShape.nonrecursive → Ts[k]? = some T →
      occursConst fam T = false
  | [], _, shapes, _, k, T, _, hT => by simp at hT
  | A :: Ts, depth, shapes, h, k, T, hs, hT => by
      unfold fieldShapesFuel at h
      cases ha : fieldAnalyze E fuel fam nu np nq depth A with
      | refused _ => rw [ha] at h; cases h
      | unresolved => rw [ha] at h; cases h
      | permitted s idx =>
          rw [ha] at h
          cases hr : fieldShapesFuel E fuel fam nu np nq (depth + 1) Ts with
          | none => rw [hr] at h; cases h
          | some rest =>
              rw [hr] at h
              have e : shapes = s :: rest := (Option.some.inj h).symm
              subst e
              cases k with
              | succ k =>
                  simp only [List.getElem?_cons_succ] at hs hT
                  exact shapes_nonrec_free E fuel fam nu np nq Ts (depth + 1) rest hr k T hs hT
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hs hT
                  subst hT
                  subst hs
                  exact fieldAnalyze_nonrec_free ha

/-! ### pending classes, read at a recursor node -/

section Node

variable {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}

/-- The node-level body of `GroupClass`. On S2 the class's node row does not require
family-free fields — `recPkg_classG` discharges the package without the `occursConst`
clause — so a `Prop` family with `anySort` elimination and a family-mentioning field is
inside the proved class; `PendC` names it for the C lane's sharper treatment anyway. -/
def GroupClassAt (node : RecNode E E' f rr rm) : Prop :=
  (∀ i, RecFieldsDirect f (policyFamilyLevels node.a.family) node.a.family.parameters.length
      node.a.family.indices.length (node.a.constructorViews i).fields 0) ∧
    (UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
            (node.a.constructorViews i).resultIndices = none)

theorem groupClass_iff_at : GroupClass E E' f rr rm ↔ ∀ node : RecNode E E' f rr rm, GroupClassAt node :=
  Iff.rfl

/-- **A**: a function-recursive field (admission shape `recursive (m+1)`). -/
def PendA (node : RecNode E E' f rr rm) : Prop :=
  ∃ (i : Fin node.a.constructors.length) (k m : Nat), (node.h14.shapesAt i)[k]? = some (.recursive (m + 1))

/-- **D**: a directly recursive field (shape `recursive 0`) that is not the canonical family
application syntactically (reached through δ/β). -/
def PendD (node : RecNode E E' f rr rm) : Prop :=
  ∃ (i : Fin node.a.constructors.length) (k : Nat) (A : Expr Nat),
    (node.a.constructorViews i).fields[k]? = some A ∧ (node.h14.shapesAt i)[k]? = some (.recursive 0) ∧
      ¬ DirectClause f (policyFamilyLevels node.a.family) node.a.family.parameters.length
        node.a.family.indices.length (0 + k) A

/-- **C**: a `Prop` family with large elimination whose constructor has a field mentioning the family. -/
def PendC (node : RecNode E E' f rr rm) : Prop :=
  UniformProp node.a.family.resultLevel ∧ node.a.policy = .anySort ∧
    ∃ (i : Fin node.a.constructors.length) (T : Expr Nat),
      T ∈ (node.a.constructorViews i).fields ∧ occursConst f T = true

/-- **B**: a `Prop` family with large elimination whose constructor has a field revealed in the
result indices. -/
def PendB (node : RecNode E E' f rr rm) : Prop :=
  UniformProp node.a.family.resultLevel ∧ node.a.policy = .anySort ∧
    ∃ (i : Fin node.a.constructors.length) (k : Nat), k < (node.a.constructorViews i).fields.length ∧
      posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k))
        (node.a.constructorViews i).resultIndices ≠ none

/-- **Exported for the B lane**: every field is family-free or
canonical-direct at a node with no function-recursive field (`¬ PendA`) and
no noncanonical `recursive 0` field (`¬ PendD`). Discharges
`NodeFieldRow.1`'s `∀ i, RecFieldsDirect` — the first conjunct of
`PartitionSteps.stepB1` (which receives exactly `¬ PendA`/`¬ PendD`); a
`PendB` node's revelation lives in the result indices, not the field
shapes, so `PendB` need not be refuted. -/
theorem recFieldsDirect_of_notAD (P : Premises4) (node : RecNode E E' f rr rm)
    (hA : ¬ PendA node) (hD : ¬ PendD node) :
    ∀ i, RecFieldsDirect f (policyFamilyLevels node.a.family) node.a.family.parameters.length
      node.a.family.indices.length (node.a.constructorViews i).fields 0 := by
  intro i
  refine recFieldsDirect_of_clauses _ 0 fun k A hk => ?_
  have hlen := fieldShapesFuel_length _ _ _ _ _ _ _ _ _ (node.h14.analyzed i)
  have hk' : k < (node.a.constructorViews i).fields.length := by
    refine @Decidable.byContradiction _ (P.dec _) fun hn => ?_
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hk
    cases hk
  have hk2 : k < (node.h14.shapesAt i).length := by omega
  have hs : (node.h14.shapesAt i)[k]? = some ((node.h14.shapesAt i)[k]'hk2) :=
    List.getElem?_eq_getElem hk2
  generalize (node.h14.shapesAt i)[k]'hk2 = s at hs
  cases s with
  | nonrecursive =>
      left
      have := shapes_nonrec_free _ _ _ _ _ _ _ _ _ (node.h14.analyzed i) k A hs hk
      rwa [node.fam] at this
  | recursive m =>
      cases m with
      | succ m => exact absurd ⟨i, k, m, hs⟩ hA
      | zero =>
          cases P.dec (DirectClause f (policyFamilyLevels node.a.family) node.a.family.parameters.length
              node.a.family.indices.length (0 + k) A) with
          | isTrue hcl => simpa [DirectClause] using hcl
          | isFalse hcl => exact absurd ⟨i, k, A, hk, hs, hcl⟩ hD

/-- The proved-class row from the negative field facts: no function-recursive
field (`¬ PendA`), no noncanonical `recursive 0` field (`¬ PendD`), and no
index-revealed field (`¬ PendB`). A family-mentioning field is allowed — it is
`recursive 0` and canonical, and `recPkg_classG`'s `propEmpty_of_lim` branch
handles the resulting empty family at `UniformProp`/`anySort`. -/
theorem groupClassAt_of_notADB (P : Premises4) (node : RecNode E E' f rr rm)
    (hA : ¬ PendA node) (hD : ¬ PendD node) (hB : ¬ PendB node) :
    GroupClassAt node := by
  refine ⟨recFieldsDirect_of_notAD P node hA hD, fun hup hany i k hk => ?_⟩
  refine @Decidable.byContradiction _ (P.dec _) fun hn => ?_
  exact hB ⟨hup, hany, i, k, hk, hn⟩

/-- **Node coverage**: a recursor node satisfies the group conditions of `ClassG`, or is in one of
the pending classes A, B, C, D. -/
theorem node_cover (P : Premises4) (node : RecNode E E' f rr rm) :
    GroupClassAt node ∨ PendA node ∨ PendB node ∨ PendC node ∨ PendD node := by
  cases P.dec (PendA node) with
  | isTrue hA => exact Or.inr (Or.inl hA)
  | isFalse hA =>
  cases P.dec (PendD node) with
  | isTrue hD => exact Or.inr (Or.inr (Or.inr (Or.inr hD)))
  | isFalse hD =>
  cases P.dec (PendC node) with
  | isTrue hC => exact Or.inr (Or.inr (Or.inr (Or.inl hC)))
  | isFalse hC =>
  cases P.dec (PendB node) with
  | isTrue hB => exact Or.inr (Or.inr (Or.inl hB))
  | isFalse hB =>
  exact Or.inl (groupClassAt_of_notADB P node hA hD hB)

end Node

/-! ### coverage of a whole derivation -/

/-- **PendW**: the constructors' own admission views split off a different parameter count than
the recursor's family view (`RcicF3WalkWitness` is an admitted instance). -/
def PendW {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} {S : ResolvedEnv}
    {E1 : ResolvedEnv} {ms : List (Nat × CheckedMember)} (hmem : GroupMembersT S E1 ms E')
    (node : RecNode E E' f rr rm) : Prop :=
  ¬ WalkClass node.a.family.parameters.length hmem

/-- One group's coverage: in the proved class, or in a named pending class. -/
def NodeCovered {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} {S : ResolvedEnv}
    {E1 : ResolvedEnv} {ms : List (Nat × CheckedMember)} (hmem : GroupMembersT S E1 ms E')
    (node : RecNode E E' f rr rm) : Prop :=
  (GroupClassAt node ∧ WalkClass node.a.family.parameters.length hmem) ∨ PendA node ∨ PendB node ∨
    PendC node ∨ PendD node ∨ PendW hmem node

theorem nodeCovered (P : Premises4) {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} {S : ResolvedEnv}
    {E1 : ResolvedEnv} {ms : List (Nat × CheckedMember)} (hmem : GroupMembersT S E1 ms E')
    (node : RecNode E E' f rr rm) : NodeCovered hmem node := by
  cases P.dec (WalkClass node.a.family.parameters.length hmem) with
  | isTrue hw =>
      rcases node_cover P node with h | h | h | h | h
      · exact Or.inl ⟨h, hw⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  | isFalse hw => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hw))))

/-- The coverage predicate: `ClassG`'s recursion, with each group arm covered by the proved class
or a named pending class, and the axiom arm still excluded. -/
def Covered : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ _ _ _ _ _ => False
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => Covered hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => Covered hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => Covered hE
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem =>
      Covered hE ∧ ∀ node : RecNode E E' f rr rm, NodeCovered hmem node

/-- **Coverage.** Every axiom-free admitted environment is covered: each of its groups is in the
proved class (`GroupClassAt` and `WalkClass`) or in one of the named pending classes A, B, C, D, W. -/
theorem EnvWfT_axiomFree_covered (P : Premises4) : {E : ResolvedEnv} → (hW : EnvWfT E) → AxiomFreeEnv' E → Covered hW
  | _, .empty, _ => trivial
  | _, .axiom E r A u hE hfresh _ _ _, hax =>
      (hax r _ (members_extend_eq E r _) rfl).elim
  | _, .definition E r' _ _ _ hE hfresh _ _ _ _ _ _, hax =>
      EnvWfT_axiomFree_covered P hE fun r m h => hax r m (members_extend_preserved hfresh r m h)
  | _, .thm E r' _ _ hE hfresh _ _ _ _ _ _, hax =>
      EnvWfT_axiomFree_covered P hE fun r m h => hax r m (members_extend_preserved hfresh r m h)
  | _, .opaque E r' _ _ _ hE hfresh _ _ _ _ _ _, hax =>
      EnvWfT_axiomFree_covered P hE fun r m h => hax r m (members_extend_preserved hfresh r m h)
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem, hax =>
      ⟨EnvWfT_axiomFree_covered P hE fun r m h => hax r m (groupMembersT_preserve hmem r m h),
       fun node => nodeCovered P hmem node⟩

/-- The proved class is covered. -/
theorem covered_of_classG : {E : ResolvedEnv} → (hW : EnvWfT E) → ClassG hW → Covered hW
  | _, .empty, _ => trivial
  | _, .axiom _ _ _ _ _ _ _ _ _, hC => hC
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hC => covered_of_classG hE hC
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hC => covered_of_classG hE hC
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hC => covered_of_classG hE hC
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem, hC =>
      ⟨covered_of_classG hE hC.1, fun node => Or.inl ⟨hC.2.1 node, hC.2.2 node⟩⟩

/-! ### assembly: per-class step hypotheses

`GInvSteps Cl Bd` is the interface each class lane discharges: for every arm of `EnvWfT`, if the
derivation is in the (proved or pending) class `Cl` and respects the level bound `Bd`, then so does
the base derivation, and the model invariant `GInv` passes from the base to the arm. The
assembly is generic in `Cl` and `Bd`: nothing in it is specific to R-CIC beyond `EnvWfT`'s shape. -/

structure GInvSteps (P : Premises4) (K : Nat → Nat) (Cl Bd : ∀ {E : ResolvedEnv}, EnvWfT E → Prop) : Prop where
  stepDef : ∀ (E : ResolvedEnv) (r : Nat) (A v : Expr Nat) (u : Level) (hE : EnvWfT E)
      (hfresh : E.members r = none) (hA : HasTyT E 0 [] A (.sort u)) (hv : HasTyT E 0 [] v A)
      (hclA : ∀ k, Rcic.Declarative.lift k 1 A = A) (hclv : ∀ k, Rcic.Declarative.lift k 1 v = v)
      (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true),
      Cl (EnvWfT.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) →
      Bd (EnvWfT.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) →
      Cl hE ∧ Bd hE ∧ (GInv P K hE → GInv P K (EnvWfT.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv))
  stepThm : ∀ (E : ResolvedEnv) (r : Nat) (A p : Expr Nat) (hE : EnvWfT E)
      (hfresh : E.members r = none) (hA : HasTyT E 0 [] A (.sort .zero)) (hp : HasTyT E 0 [] p A)
      (hclA : ∀ k, Rcic.Declarative.lift k 1 A = A) (hclp : ∀ k, Rcic.Declarative.lift k 1 p = p)
      (hlvlA : exprLevelsBounded 0 A = true) (hlvlp : exprLevelsBounded 0 p = true),
      Cl (EnvWfT.thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp) →
      Bd (EnvWfT.thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp) →
      Cl hE ∧ Bd hE ∧ (GInv P K hE → GInv P K (EnvWfT.thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp))
  stepOpq : ∀ (E : ResolvedEnv) (r : Nat) (A v : Expr Nat) (u : Level) (hE : EnvWfT E)
      (hfresh : E.members r = none) (hA : HasTyT E 0 [] A (.sort u)) (hv : HasTyT E 0 [] v A)
      (hclA : ∀ k, Rcic.Declarative.lift k 1 A = A) (hclv : ∀ k, Rcic.Declarative.lift k 1 v = v)
      (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true),
      Cl (EnvWfT.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) →
      Bd (EnvWfT.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) →
      Cl hE ∧ Bd hE ∧ (GInv P K hE → GInv P K (EnvWfT.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv))
  stepGrp : ∀ (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
      (rr : Nat) (rm : CheckedMember) (E' : ResolvedEnv) (hE : EnvWfT E)
      (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
      (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'),
      Cl (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
      Bd (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) →
      Cl hE ∧ Bd hE ∧ (GInv P K hE → GInv P K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))

/-- The model invariant along a derivation, from the step hypotheses. The axiom arm is excluded by
`Cl` (`hax`). -/
theorem gInv_of_steps (P : Premises4) (K : Nat → Nat) (Cl Bd : ∀ {E : ResolvedEnv}, EnvWfT E → Prop)
    (S : GInvSteps P K Cl Bd)
    (hax : ∀ (E : ResolvedEnv) (r : Nat) (A : Expr Nat) (u : Level) (hE : EnvWfT E)
      (hfresh : E.members r = none) (hA : HasTyT E 0 [] A (.sort u)) (hcl : ∀ k, Rcic.Declarative.lift k 1 A = A)
      (hlvl : exprLevelsBounded 0 A = true), ¬ Cl (EnvWfT.axiom E r A u hE hfresh hA hcl hlvl)) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → Cl hW → Bd hW → GInv P K hW
  | _, .empty, _, _ => fun _ _ _ _ =>
      ⟨fun _ _ h => (Option.noConfusion h), fun _ _ _ _ h => (Option.noConfusion h)⟩
  | _, .axiom E r A u hE hfresh hA hcl hlvl, hC, _ => (hax E r A u hE hfresh hA hcl hlvl hC).elim
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hC, hB =>
      let t := S.stepDef E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB
      t.2.2 (gInv_of_steps P K Cl Bd S hax hE t.1 t.2.1)
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp, hC, hB =>
      let t := S.stepThm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp hC hB
      t.2.2 (gInv_of_steps P K Cl Bd S hax hE t.1 t.2.1)
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hC, hB =>
      let t := S.stepOpq E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB
      t.2.2 (gInv_of_steps P K Cl Bd S hax hE t.1 t.2.1)
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC, hB =>
      let t := S.stepGrp E f fm ctors rr rm E' hE hfam hctors hrec hmem hC hB
      t.2.2 (gInv_of_steps P K Cl Bd S hax hE t.1 t.2.1)

/-- **Assembly.** From class coverage (`hCover`: every axiom-free admitted environment with the
empty type at 0 and its recursor at 1 is in `Cl`), the per-class step hypotheses at every instance
bound `K`, the level bound (`hBound`) and the model's final step (`hFinal`: in `Cl` with the
invariant, the recursor at 1 has no closed term), the target `RcicConsistentEmpty` follows. Relative to
`Premises4`; generic in `Cl` and `Bd`. -/
theorem rcicConsistentEmpty_of_cover (P : Premises4)
    (Cl : ∀ {E : ResolvedEnv}, EnvWfT E → Prop) (Bd : (Nat → Nat) → ∀ {E : ResolvedEnv}, EnvWfT E → Prop)
    (S : ∀ K : Nat → Nat, GInvSteps P K Cl (Bd K))
    (hax : ∀ (E : ResolvedEnv) (r : Nat) (A : Expr Nat) (u : Level) (hE : EnvWfT E)
      (hfresh : E.members r = none) (hA : HasTyT E 0 [] A (.sort u)) (hcl : ∀ k, Rcic.Declarative.lift k 1 A = A)
      (hlvl : exprLevelsBounded 0 A = true), ¬ Cl (EnvWfT.axiom E r A u hE hfresh hA hcl hlvl))
    (hCover : ∀ (E : ResolvedEnv) (hW : EnvWfT E), AxiomFreeEnv' E → E.members 0 = some falseFamMember →
      E.members 1 = some falseRecMemberU → Cl hW)
    (hBound : ∀ (E : ResolvedEnv) (hW : EnvWfT E) (n : Nat) (e : Expr Nat) (h : HasTyT E n [] e (.const 0 [])),
      ∃ K, Bd K hW ∧ LOKt (fun _ => 0) 4 K h)
    (hFinal : ∀ (K : Nat → Nat) (E : ResolvedEnv) (hW : EnvWfT E), Cl hW → Bd K hW → GInv P K hW →
      E.members 1 = some falseRecMemberU → ∀ (n : Nat) (e : Expr Nat) (h : HasTyT E n [] e (.const 0 [])),
      LOKt (fun _ => 0) 4 K h → False) :
    RcicConsistentEmpty := by
  intro E hW hax' h0 h1 n e h
  obtain ⟨K, hB, hl⟩ := hBound E hW n e h
  have hC := hCover E hW hax' h0 h1
  exact hFinal K E hW hC hB (gInv_of_steps P K Cl (Bd K) (S K) hax hW hC hB) h1 n e h hl

/-! ### the proved class is an instance of the interface -/

theorem steps_classG (P : Premises4) (K : Nat → Nat) :
    GInvSteps P K (fun {E} (hW : EnvWfT E) => ClassG hW) (fun {E} (hW : EnvWfT E) => BoundG K hW) where
  stepDef := fun E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, hB.1, fun IH => gInv_single P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.2 hC IH⟩
  stepThm := fun E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp hC hB =>
    ⟨hC, hB.1, fun IH => gInv_single P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp hB.2 hC IH⟩
  stepOpq := fun E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv hC hB =>
    ⟨hC, hB.1, fun IH => gInv_single P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.2 hC IH⟩
  stepGrp := fun E f fm ctors rr rm E' hE hfam hctors hrec hmem hC hB =>
    ⟨hC.1, hB.1, fun IH => gInv_group P K hE hfam hctors hrec hmem hC hB IH⟩

/-- `rcicConsistentEmpty_of_class_bounds` is the `ClassG` instance of the generic assembly. -/
theorem rcicConsistentEmpty_of_cover_classG (P : Premises4)
    (hClass : ∀ (E : ResolvedEnv) (hW : EnvWfT E), AxiomFreeEnv' E → E.members 0 = some falseFamMember →
      E.members 1 = some falseRecMemberU → ClassG hW)
    (hBound : ∀ (E : ResolvedEnv) (hW : EnvWfT E) (n : Nat) (e : Expr Nat) (h : HasTyT E n [] e (.const 0 [])),
      ∃ K, BoundG K hW ∧ LOKt (fun _ => 0) 4 K h) :
    RcicConsistentEmpty :=
  rcicConsistentEmpty_of_cover P (fun {E} (hW : EnvWfT E) => ClassG hW)
    (fun K {E} (hW : EnvWfT E) => BoundG K hW) (steps_classG P)
    (fun _ _ _ _ _ _ _ _ _ hC => hC) hClass hBound
    (fun K E hW hC hB IH h1 n e h hl => by
      have hRA := readsOKAlong_envCtx hW hC (envCtx hW) (fun _ _ => rfl)
      have hF := (faithfulR_envμR P (envCtx hW) hW hRA).1
      have hI := IH (envCtx hW) (fun _ _ => rfl) _ hF
      have hES := envSound_of P (Efin := E) (fun _ _ h => h) hI.1
        (fun r m hm hk => hI.2 E (fun _ _ h => h) r m hm hk) (fun _ => 0) n
      exact empty_of_falseRec P (hI.1 1 _ h1) (sound_ty (P.good _ rfl) hES h hl ρ0 trivial))

/-- **Headline.** With the pending classes' step hypotheses stated at the coverage predicate
`Covered`, the target follows: coverage supplies `hCover`. Every pending class (A, B, C, D, W) is
discharged by supplying its arm of `GInvSteps` for `Covered`; nothing is assumed silently. -/
theorem rcicConsistentEmpty_of_covered (P : Premises4)
    (Bd : (Nat → Nat) → ∀ {E : ResolvedEnv}, EnvWfT E → Prop)
    (S : ∀ K : Nat → Nat, GInvSteps P K (fun {E} (hW : EnvWfT E) => Covered hW) (Bd K))
    (hBound : ∀ (E : ResolvedEnv) (hW : EnvWfT E) (n : Nat) (e : Expr Nat) (h : HasTyT E n [] e (.const 0 [])),
      ∃ K, Bd K hW ∧ LOKt (fun _ => 0) 4 K h)
    (hFinal : ∀ (K : Nat → Nat) (E : ResolvedEnv) (hW : EnvWfT E), Covered hW → Bd K hW → GInv P K hW →
      E.members 1 = some falseRecMemberU → ∀ (n : Nat) (e : Expr Nat) (h : HasTyT E n [] e (.const 0 [])),
      LOKt (fun _ => 0) 4 K h → False) :
    RcicConsistentEmpty :=
  rcicConsistentEmpty_of_cover P (fun {E} (hW : EnvWfT E) => Covered hW) Bd S
    (fun _ _ _ _ _ _ _ _ _ hC => hC)
    (fun E hW hax _ _ => EnvWfT_axiomFree_covered P hW hax) hBound hFinal

end PSet

end Rcic.F3

#print axioms Rcic.F3.PSet.EnvWfT_axiomFree_covered
#print axioms Rcic.F3.PSet.node_cover
#print axioms Rcic.F3.PSet.rcicConsistentEmpty_of_cover
#print axioms Rcic.F3.PSet.rcicConsistentEmpty_of_covered
#print axioms Rcic.F3.PSet.rcicConsistentEmpty_of_cover_classG
#print axioms Rcic.F3.PSet.covered_of_classG
