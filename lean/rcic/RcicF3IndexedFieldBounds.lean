import rcic.RcicF3PropEvalSafeIndex
import rcic.RcicF3AccBoundScopeAttack
import rcic.RcicF3CandidateBoundFields

/-!
# Separate ordinary and unrevealed-proof field bounds

`Rows` retains a bounded ordinary sort typing for every original field and
a bounded Prop typing only for fields absent from the bare result indices.
The first part supplies InstOK and typed reader normalization; the second
part supplies the already-produced safe-index comparison.

`BoundGIndexed` is a separate environment predicate. It keeps BoundG's
stored constructor typings, WalkB2, definition-body bounds, complete
recursor universe vectors, and actual family-parameter contexts. Only its
last all-Prop field clause is replaced with Rows. The old BoundG and every
existing checked-tier theorem remain unchanged.

The old bound implies this new predicate by an actual admission induction.
The concrete strict-broadening witness concerns the Rows interface at the
admitted AccP node. No BoundGIndexed witness for all possible views of the
whole AccP admission, imported Acc environment, or new universal tier is
asserted here.

closure_claim = 0; scope_closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.IndexedFieldBounds

open Rcic.Declarative Rcic.Declarative.Ann PropEval PiIndex PropEvalSafeIndex

/-- Every required original row is typed at an ordinary sort, in its
actual dependent prefix, at the entire supplied syntax valuation. -/
def OrdinaryBounds (S : ResolvedEnv) (ar : Nat) (σ K : Nat → Nat)
    (Ps Fs : List (Expr Nat)) : Prop :=
  ∀ j : Fin Fs.length, ∃ l : Level,
    ∃ d : HasTyT S ar (policyPrefixContext (Ps ++ Fs) (Ps.length + j.val))
      Fs[j] (.sort l), LOKt σ 4 K d

/-- The old all-Prop row clause, isolated only for the implication and
strict-broadening witness. This does not redefine BoundG. -/
def AllPropRows (S : ResolvedEnv) (ar : Nat) (σ K : Nat → Nat)
    (Ps Fs : List (Expr Nat)) : Prop :=
  ∀ j : Fin Fs.length, ∃ l : Level, UniformProp l ∧
    ∃ d : HasTyT S ar (policyPrefixContext (Ps ++ Fs) (Ps.length + j.val))
      Fs[j] (.sort l), LOKt σ 4 K d

structure Rows (S : ResolvedEnv) (ar : Nat) (σ K : Nat → Nat)
    (Ps Fs Is : List (Expr Nat)) : Prop where
  ordinary : OrdinaryBounds S ar σ K Ps Fs
  unrevealed : UnrevealedBounds S ar σ K Ps Fs Is

/-- The former clause constructively supplies both new consumers. -/
theorem Rows.of_allProp {S : ResolvedEnv} {ar : Nat} {σ K : Nat → Nat}
    {Ps Fs Is : List (Expr Nat)} (h : AllPropRows S ar σ K Ps Fs) :
    Rows S ar σ K Ps Fs Is := by
  constructor
  · intro j
    obtain ⟨l, _, d, hd⟩ := h j
    exact ⟨l, d, hd⟩
  · intro j _
    obtain ⟨l, hl, d, hd⟩ := h j
    exact ⟨l, hl σ, d, hd⟩

/-- Ordinary rows pay all constant-instance checks. Revealed fields are
included; no Prop typing of those fields is used. -/
theorem Rows.instOK {S : ResolvedEnv} {ar : Nat} {σ K : Nat → Nat}
    {Ps Fs Is : List (Expr Nat)} (h : Rows S ar σ K Ps Fs Is) :
    ∀ A ∈ Fs, InstOK S σ K A := by
  intro A hA
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hA
  obtain ⟨l, d, hd⟩ := h.ordinary ⟨k, hk⟩
  exact instOK_of_lokt σ 4 K d hd

/-- The semantic comparator is produced from the second row component,
not stored as part of the row interface. -/
theorem Rows.compare (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K σ : Nat → Nat)
    {S : ResolvedEnv} {ar : Nat} (Ps Fs Is : List (Expr Nat))
    (hES : EnvSound (mkM P μ) σ K S ar) (h : Rows S ar σ K Ps Fs Is)
    (ps ps' xs xs' : List PSet.{4})
    (hp : TelFits (mkM P μ) σ Ps ρ0 ps)
    (hp' : TelFits (mkM P μ) σ Ps ρ0 ps')
    (hx : TelFits (mkM P μ) σ Fs (push ps ρ0) xs)
    (hx' : TelFits (mkM P μ) σ Fs (push ps' ρ0) xs')
    (hk : key (ps ++ Is.map (den (mkM P μ) σ (push xs (push ps ρ0)))) =
      key (ps' ++ Is.map (den (mkM P μ) σ (push xs' (push ps' ρ0))))) :
    LEq xs xs' :=
  fields_equiv_of_bounds P μ K σ Ps Fs Is hES h.unrevealed
    ps ps' xs xs' hp hp' hx hx' hk

/-- This predicate broadens only the final field clause of BoundG. The
quantification over vs intentionally has no family-arity length equality;
the extra recursor motive universe remains part of the actual valuation. -/
def BoundGIndexed (K : Nat → Nat) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => BoundGIndexed K hE
  | _, .definition _ _ _ _ _ hE _ _ hv _ _ _ _ =>
      BoundGIndexed K hE ∧ LOKt (fun _ => 0) 4 K hv
  | _, .thm _ _ _ _ hE _ _ hp _ _ _ _ =>
      BoundGIndexed K hE ∧ LOKt (fun _ => 0) 4 K hp
  | _, .opaque _ _ _ _ _ hE _ _ hv _ _ _ _ =>
      BoundGIndexed K hE ∧ LOKt (fun _ => 0) 4 K hv
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem =>
      BoundGIndexed K hE ∧
      (∀ node : RecNode E E' f rr rm,
        ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
        vs.length = node.a.family.member.arity →
        (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
        ∃ (u : Level) (d : HasTyT (extendEnv E f fm) node.a.family.member.arity []
          (node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d) ∧
      WalkB2 K hmem ∧
      (∀ node : RecNode E E' f rr rm, UniformProp node.a.family.resultLevel →
        node.a.policy = .anySort →
        ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
        (∀ v, v ∈ vs → v ≤ K rr) →
        Rows (extendEnv E f fm) node.a.family.member.arity (σOf vs) K
          node.a.family.parameters (node.a.constructorViews i).fields
          (node.a.constructorViews i).resultIndices)

/-- Literal admission induction proves the direction required for a
broadening. It does not manufacture the old all-Prop clause in reverse. -/
theorem of_boundG (K : Nat → Nat) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → BoundG K hW → BoundGIndexed K hW
  | _, .empty, _ => True.intro
  | _, .axiom _ _ _ _ hE _ _ _ _, h => of_boundG K hE h
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, h => ⟨of_boundG K hE h.1, h.2⟩
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, h => ⟨of_boundG K hE h.1, h.2⟩
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, h => ⟨of_boundG K hE h.1, h.2⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _, h =>
      ⟨of_boundG K hE h.1, h.2.1, h.2.2.1,
        fun node hProp hpolicy i vs hv =>
          Rows.of_allProp (h.2.2.2 node hProp hpolicy i vs hv)⟩

/-- Stored definition-body bounds survive the broadening. This is the
minimal input consumed by transparent-body InstOK and regularity proofs. -/
theorem envBound (K : Nat → Nat) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → BoundGIndexed K hW → EnvBound K hW
  | _, .empty, _ => True.intro
  | _, .axiom _ _ _ _ hE _ _ _ _, h => envBound K hE h
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, h => ⟨envBound K hE h.1, h.2⟩
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, h => ⟨envBound K hE h.1, h.2⟩
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, h => ⟨envBound K hE h.1, h.2⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _, h => envBound K hE h.1

/-- The separate bound is inhabited on the actual admitted False group. -/
theorem falseEnv_bound (K : Nat → Nat) : BoundGIndexed K falseEnvUWfT :=
  of_boundG K falseEnvUWfT (falseEnvUWfT_boundG K)

/-- Complete group-instance bounds now directly produce indexed evaluation
functionality, retaining the actual syntax valuation and typed IH theorem. -/
theorem functional_of_boundIndexed (C : Context) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hB : BoundGIndexed K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hM : C.M = mkM P μ)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (hES : EnvSound (mkM P μ) C.σ K (extendEnv C.E C.f fm)
      C.node.a.family.member.arity)
    (vs : List Nat) (hσ : C.σ = σOf vs)
    (hvs : ∀ v, v ∈ vs → v ≤ K C.rr)
    {i : Index.{4}} {z z' : PSet.{4}} (h : Eval C i z) (h' : Eval C i z') :
    Equiv z z' := by
  apply PropEvalSafeIndex.functional_of_bounds C P μ K
    (extendEnv C.E C.f fm) C.node.a.family.member.arity hM h0 hpolicy hES ?_ h h'
  intro j
  rw [hσ]
  exact (hB.2.2.2 C.node (selection_prop C.node.a C.σ h0 hpolicy).1
    hpolicy j vs hvs).unrevealed

/-! ## Actual AccP row package and strictness, at the same P -/

theorem accP_recursive_row_bound (K σ : Nat → Nat) :
    LOKt σ 4 K (accPFieldDomTyT (E := accPFamEnvT) (n := 0) rfl rfl) := by
  change 1 ≤ 4 ∧ 0 ≤ 4 ∧ 1 ≤ 4 ∧
    (0 ≤ 4 ∧ 0 ≤ 4 ∧
      ((LevelsOK σ (K 9) [] ∧ True) ∧ True) ∧
      (LevelsOK σ (K 10) [] ∧ True))
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · exact ⟨⟨(fun _ h => nomatch h), True.intro⟩, True.intro⟩
  · exact ⟨(fun _ h => nomatch h), True.intro⟩

/-- The data-valued x field is bounded at Sort 1; the recursive field is
bounded at Prop. Both use the exact original dependent contexts. -/
theorem accP_rows (K σ : Nat → Nat) :
    Rows accPFamEnvT 0 σ K [] [.sort .zero, paFieldDom] [.bvar 1] := by
  constructor
  · intro j
    match j with
    | ⟨0, _⟩ => exact ⟨.succ .zero, HasTyT.sort [] .zero, by change 1 ≤ 4; decide⟩
    | ⟨1, _⟩ => exact ⟨.imax (.succ .zero) (.imax .zero .zero),
        accPFieldDomTyT rfl rfl, accP_recursive_row_bound K σ⟩
  · intro j hnot
    match j with
    | ⟨0, _⟩ => exact (hnot (List.mem_singleton.mpr rfl)).elim
    | ⟨1, _⟩ => exact ⟨.imax (.succ .zero) (.imax .zero .zero), rfl,
        accPFieldDomTyT rfl rfl, accP_recursive_row_bound K σ⟩

/-- This row package is literally the selected admitted AccP node's data.
It is not a theorem about the separate real imported Acc environment. -/
theorem accP_rows_at_node (K σ : Nat → Nat) :
    Rows accPFamEnvT 0 σ K Rcic.F3.StepDGCheck.accPNode.a.family.parameters
      (Rcic.F3.StepDGCheck.accPNode.a.constructorViews ⟨0, by decide⟩).fields
      (Rcic.F3.StepDGCheck.accPNode.a.constructorViews ⟨0, by decide⟩).resultIndices :=
  accP_rows K σ

theorem accP_allProp_refuted (P : Premises4) (K σ : Nat → Nat) :
    ¬ AllPropRows accPFamEnvT 0 σ K [] [.sort .zero, paFieldDom] := by
  intro h
  obtain ⟨l, hl, d, hd⟩ := h ⟨0, by decide⟩
  exact AccBoundScopeAttack.no_bounded_prop_sort P (AccBoundScopeAttack.prefixTable P)
    K σ (AccBoundScopeAttack.prefix_sound P K σ 0) l hl d hd

def Witness (P : Premises4) : Prop :=
  (∀ K, BoundGIndexed K falseEnvUWfT) ∧
  (∀ K σ, Rows accPFamEnvT 0 σ K [] [.sort .zero, paFieldDom] [.bvar 1]) ∧
  (∀ K σ, EnvSound (mkM P (AccBoundScopeAttack.prefixTable P)) σ K accPFamEnvT 0) ∧
  (∀ K σ, ¬ AllPropRows accPFamEnvT 0 σ K [] [.sort .zero, paFieldDom]) ∧
  (∀ K, ¬ BoundG K accPEnvWfT)

theorem component_witness (P : Premises4) : Witness P :=
  ⟨falseEnv_bound, accP_rows, fun K σ => AccBoundScopeAttack.prefix_sound P K σ 0,
    accP_allProp_refuted P, AccBoundScopeAttack.boundG_refuted P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.IndexedFieldBounds

#print axioms Rcic.F3.PSet.IndexedFieldBounds.Rows.instOK
#print axioms Rcic.F3.PSet.IndexedFieldBounds.Rows.compare
#print axioms Rcic.F3.PSet.IndexedFieldBounds.of_boundG
#print axioms Rcic.F3.PSet.IndexedFieldBounds.envBound
#print axioms Rcic.F3.PSet.IndexedFieldBounds.functional_of_boundIndexed
#print axioms Rcic.F3.PSet.IndexedFieldBounds.accP_rows_at_node
#print axioms Rcic.F3.PSet.IndexedFieldBounds.component_witness
#print axioms Rcic.F3.PSet.IndexedFieldBounds.component_nonrefutable
