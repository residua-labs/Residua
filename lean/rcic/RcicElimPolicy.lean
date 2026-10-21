/-
# Declaration-time Prop elimination safety

This module supplies the mandatory `IndMemberElimSafe` premise of the
repaired `EnvWf.indMember`. It complements the existing universal
`RecursorGroupIdxAdmitted.typing` certificate: neither a successful old
admission Bool nor a handwritten typing certificate establishes this
policy on its own.

The policy reads the actual stored motive and result, a complete
constructor census, and genuine typing of singleton proof fields in
their declaration telescope. The constructor arm prevents any later
constructor for an already sealed family, regardless of reference order.

Scope: 05 §§10–11 elimination SAFETY. Safe monomorphic specializations
of Type/empty/singleton recursors remain admitted. Native §11's unique
fresh motive parameter and complete canonical recursor generation are
not claimed here. No conversion characterization, injectivity theorem,
or normalization assumption is a premise.
-/
import rcic.RcicAdmit
import rcic.RcicInvertFamily

namespace Rcic.Declarative

/- TREE ADAPTATION (main 45df7eccc6, #6075): `CtxWf` already lives in
`RcicInvertFamily` with these three constructors. #6070 relocated it
into this file on face. Redefining it here is a second inductive in
the same namespace, which `RcicFoundation` cannot import beside
`RcicInvertFamily`. This file uses that inductive; it does not move it.
-/

/- `piResult`, `piLastDom`, `spineHeadRef`, `memberFamRef` live in
`RcicFamRef` (below `EnvWf`). This file uses those; it does not
redefine them. -/

/-- The total-valuation universe classification of 05 §5. A single
valuation, in particular the all-zero valuation, cannot establish it. -/
def UniformPropLevel (u : Level) : Prop :=
  ∀ ρ : Nat → Nat, eval (fun i => some (ρ i)) u = some 0

def UniformTypeLevel (u : Level) : Prop :=
  ∀ ρ : Nat → Nat, ∃ k : Nat,
    eval (fun i => some (ρ i)) u = some (k + 1)

theorem uniformPropLevel_zero : UniformPropLevel .zero := fun _ => rfl

theorem uniformTypeLevel_succ_zero : UniformTypeLevel (.succ .zero) :=
  fun _ => ⟨0, rfl⟩

theorem eval_totalValuation (ρ : Nat → Nat) :
    (u : Level) → ∃ k, eval (fun i => some (ρ i)) u = some k
  | .zero => ⟨0, rfl⟩
  | .param i => ⟨ρ i, rfl⟩
  | .succ u => by
      obtain ⟨k, hk⟩ := eval_totalValuation ρ u
      exact ⟨k + 1, by simp only [eval, hk, Option.map]⟩
  | .max u v => by
      obtain ⟨k, hk⟩ := eval_totalValuation ρ u
      obtain ⟨l, hl⟩ := eval_totalValuation ρ v
      exact ⟨max k l, by simp only [eval, hk, hl, Option.bind, Option.map]⟩
  | .imax u v => by
      obtain ⟨l, hl⟩ := eval_totalValuation ρ v
      by_cases hz : l = 0
      · exact ⟨0, by simp [eval, hl, hz]⟩
      · obtain ⟨k, hk⟩ := eval_totalValuation ρ u
        exact ⟨max k l, by
          simp only [eval, hl, Option.bind, if_neg hz, hk, Option.map]⟩

theorem uniformTypeLevel_succ (u : Level) : UniformTypeLevel (.succ u) := by
  intro ρ
  obtain ⟨k, hk⟩ := eval_totalValuation ρ u
  exact ⟨k, by simp only [eval, hk, Option.map]⟩

theorem uniformPropLevel_not_type {u : Level}
    (hp : UniformPropLevel u) : ¬ UniformTypeLevel u := by
  intro ht
  obtain ⟨k, hk⟩ := ht (fun _ => 0)
  have heq := (hp (fun _ => 0)).symm.trans hk
  have heq' := Option.some.inj heq
  omega

/- `NoRecursorFor`, `CtorBeforeRecursors`, and `CtorCensus` are defined in
`RcicIndGroupJudgment`, next to `memberFamRef` in `RcicFamRef`, so
`EnvWf` can name the admission judgment without importing this file.
The theorems below are the same statements. -/
theorem CtorBeforeRecursors.no_existing {E : ResolvedEnv}
    {m rm : CheckedMember} {f rr : Nat}
    (h : CtorBeforeRecursors E m) (hf : memberFamRef m = some f)
    (hr : E.members rr = some rm) (hk : rm.mclass = .recursorM)
    (hrf : memberFamRef rm = some f) : False := by
  obtain ⟨f', hf', hnone⟩ := h
  have hff : f' = f := Option.some.inj (hf'.symm.trans hf)
  subst f'
  exact hnone rr rm hr hk hrf

theorem CtorCensus.constructor_bounds {E : ResolvedEnv} {f r c : Nat}
    {cm : CheckedMember} (h : CtorCensus E f r)
    (hc : E.members c = some cm) (hk : cm.mclass = .constructorM)
    (hf : memberFamRef cm = some f) : f < c ∧ c < r :=
  (h.2 c).mp ⟨cm, hc, hk, hf⟩

/-- Raw telescope domains are stored oldest first; local contexts are
newest first. The field itself has not yet entered this context. -/
def fieldContext (ds : List (Expr Nat)) (j : Nat) : LCtx :=
  (ds.take j).reverse.map LocalDecl.assumption

/-- Genuine proof-field evidence, at the family's own universe arity,
in the exact context computed from the constructor's preceding binders. -/
def FieldProofAt (E : ResolvedEnv) (nU : Nat) (ds : List (Expr Nat))
    (j : Nat) (hj : j < ds.length) : Prop :=
  Nonempty (CtxWf E nU (fieldContext ds j)) ∧
  Nonempty (HasTy E nU (fieldContext ds j) (ds[j]'hj) (.sort .zero))

/-- The full constructor telescope places binder `j` at de Bruijn
index `ds.length - 1 - j`. Exposure is exact bare-variable membership
among result INDICES, never mere occurrence or definitional equality. -/
def RevealedFieldAt (ds : List (Expr Nat)) (res : Expr Nat)
    (nparams j : Nat) : Prop :=
  (Expr.bvar (ds.length - 1 - j) : Expr Nat) ∈
    (appsSpine res).2.drop nparams

def CtorFieldsSafe (E : ResolvedEnv) (nU nparams : Nat)
    (ds : List (Expr Nat)) (res : Expr Nat) : Prop :=
  nparams ≤ ds.length ∧
  ∀ (j : Nat) (hj : j < ds.length), nparams ≤ j →
    FieldProofAt E nU ds j hj ∨ RevealedFieldAt ds res nparams j

/-- A singleton witness includes exact saturated landing and canonical
parameters BEFORE any purported result index is used for exposure.
`ctorResultParamShape` alone does not check saturation. -/
def SingletonFieldsSafe (E : ResolvedEnv) (f : Nat)
    (fm : CheckedMember) (nparams nindices : Nat) : Prop :=
  ∃ (cm : CheckedMember) (ds : List (Expr Nat)) (res : Expr Nat),
    E.members (f + 1) = some cm ∧
    cm.mclass = .constructorM ∧
    cm.arity = fm.arity ∧
    peelPis (piCount cm.mtype) cm.mtype = some (ds, res) ∧
    nparams ≤ ds.length ∧
    ctorResultParamShape f res fm.arity nparams (ds.length - nparams) = true ∧
    (appsSpine res).2.length = nparams + nindices ∧
    CtorFieldsSafe E fm.arity nparams ds res

/-- Fold a raw telescope back into Π form without changing its local
indices. Its surrounding parameter context is preserved verbatim. -/
def elimFoldPis (ds : List (Expr Nat)) (B : Expr Nat) : Expr Nat :=
  ds.foldr Expr.pi B

/-- 05 §11 motive, in the recursor's parameter context: copied family
indices, then a major of the saturated family, then the ACTUAL sort. -/
def motiveTypeExpr (f : Nat) (fm : CheckedMember)
    (familyDoms : List (Expr Nat)) (nparams nindices : Nat)
    (uM : Level) : Expr Nat :=
  elimFoldPis (familyDoms.drop nparams)
    (.pi
      (foldApps (.const f ((List.range fm.arity).map Level.param))
        (bvarSpine (nparams + nindices)))
      (.sort uM))

/-- A candidate split must agree with the actual family telescope,
actual recursor count, complete group size, and actual final major.
Admission requires a candidate to exist AND checks every candidate. -/
def RecursorSplit (f : Nat) (fm : CheckedMember) (r : Nat)
    (m : CheckedMember) (nparams nindices : Nat) : Prop :=
  nparams + nindices = piCount fm.mtype ∧
  nparams + 1 + (r - f - 1) + nindices + 1 = piCount m.mtype ∧
  piLastDom m.mtype = some
    (majorTyExpr f ((List.range fm.arity).map Level.param)
      nparams (r - f - 1) nindices)

/-- Safe targets, allowing existing bounded monomorphic specializations.
The PropOnly alternative constrains the real motive level by `eqN`;
arity equality is not a substitute for that condition. -/
def ElimTargetSafe (E : ResolvedEnv) (f : Nat) (fm : CheckedMember)
    (nparams nindices nctors : Nat) (uI uM : Level) : Prop :=
  UniformTypeLevel uI ∨
  (UniformPropLevel uI ∧
    (eqN uM .zero ∨ nctors = 0 ∨
      (nctors = 1 ∧ SingletonFieldsSafe E f fm nparams nindices)))

theorem ElimTargetSafe.prop_many {E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {nparams nindices nctors : Nat} {uI uM : Level}
    (h : ElimTargetSafe E f fm nparams nindices nctors uI uM)
    (hp : UniformPropLevel uI) (hc : 1 < nctors) : eqN uM .zero := by
  rcases h with ht | ⟨_, hm | hzero | ⟨hone, _⟩⟩
  · exact (uniformPropLevel_not_type hp ht).elim
  · exact hm
  · exact ((by decide : ¬ (1 < 0)) (hzero ▸ hc)).elim
  · exact (Nat.lt_irrefl 1 (hone ▸ hc)).elim

/-- This data is declaration evidence, not an oracle or an assumed
metatheorem. The final body and actual motive slot are mandatory even
when there are no constructors and the old per-constructor Bool is
vacuous. Family/recursor decomposition is tied to the stored types. -/
structure RecursorElimCertificate (E : ResolvedEnv) (r : Nat)
    (m : CheckedMember) : Type where
  familyRef : Nat
  famMember : CheckedMember
  familyDoms : List (Expr Nat)
  familyLevel : Level
  recDoms : List (Expr Nat)
  recBody : Expr Nat
  hrecK : m.mclass = .recursorM
  hfam : E.members familyRef = some famMember
  hfamK : famMember.mclass = .inductiveM
  hfamily : peelPis (piCount famMember.mtype) famMember.mtype =
    some (familyDoms, .sort familyLevel)
  hfamilyBound : exprLevelsBounded famMember.arity famMember.mtype = true
  hrec : peelPis (piCount m.mtype) m.mtype = some (recDoms, recBody)
  hhead : memberFamRef m = some familyRef
  hcensus : CtorCensus E familyRef r
  hsplit : ∃ nparams nindices, RecursorSplit familyRef famMember r m nparams nindices
  hsafe : ∀ nparams nindices,
    RecursorSplit familyRef famMember r m nparams nindices →
    recDoms.take nparams = familyDoms.take nparams ∧
    recBody = recBodyExpr (r - familyRef - 1) nindices ∧
    ∃ uM : Level,
      recDoms[nparams]? = some
        (motiveTypeExpr familyRef famMember familyDoms nparams nindices uM) ∧
      levelBounded m.arity uM = true ∧
      ElimTargetSafe E familyRef famMember nparams nindices
        (r - familyRef - 1) familyLevel uM

def RecursorElimSafe (E : ResolvedEnv) (r : Nat)
    (m : CheckedMember) : Prop :=
  Nonempty (RecursorElimCertificate E r m)

/-- Mandatory admission gate. Ordinary singleton classes and a bare
family do not introduce an elimination rule. All constructor and
recursor admissions must supply their respective evidence. -/
def IndMemberElimSafe (E : ResolvedEnv) (r : Nat)
    (m : CheckedMember) : Prop :=
  match m.mclass with
  | .constructorM => CtorBeforeRecursors E m
  | .recursorM => RecursorElimSafe E r m
  | _ => True

theorem indMemberElimSafe_ctor {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (hk : m.mclass = .constructorM) :
    IndMemberElimSafe E r m ↔ CtorBeforeRecursors E m := by
  simp only [IndMemberElimSafe, hk]

theorem indMemberElimSafe_rec {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (hk : m.mclass = .recursorM) :
    IndMemberElimSafe E r m ↔ RecursorElimSafe E r m := by
  simp only [IndMemberElimSafe, hk]

theorem indMemberElimSafe_ind {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (hk : m.mclass = .inductiveM) :
    IndMemberElimSafe E r m := by
  simp only [IndMemberElimSafe, hk]

theorem RecursorElimSafe.census {E : ResolvedEnv} {r f : Nat}
    {m : CheckedMember} (h : RecursorElimSafe E r m)
    (hf : memberFamRef m = some f) : CtorCensus E f r := by
  obtain ⟨c⟩ := h
  have hff : c.familyRef = f := Option.some.inj (c.hhead.symm.trans hf)
  exact hff ▸ c.hcensus

theorem RecursorElimSafe.family {E : ResolvedEnv} {r f : Nat}
    {m : CheckedMember} (h : RecursorElimSafe E r m)
    (hf : memberFamRef m = some f) :
    ∃ fm, E.members f = some fm ∧ fm.mclass = .inductiveM := by
  obtain ⟨c⟩ := h
  have hff : c.familyRef = f := Option.some.inj (c.hhead.symm.trans hf)
  exact ⟨c.famMember, hff ▸ c.hfam, c.hfamK⟩

end Rcic.Declarative
