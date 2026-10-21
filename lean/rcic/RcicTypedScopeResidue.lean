import rcic.RcicTypedConv

/-!
# Constructive scope audit along an admitted environment

`EnvWfT.inScope_or_outside` makes a finite, reproducible scope audit. Its positive branch is the
existing `EnvWfT.inScope_of_scopeCheck`. Its other branch names an actual group occurrence and keeps
the reader/checker receipts for every parameter split of that group's written family telescope.

`OutsideScope` is an audit residue, **not** the semantic complement of `EnvWfT.InScope`. In
particular, `checkerNoAnswer` records one finite run of a sound, possibly incomplete checker. It
does not assert that every checker fails, that no `GroupInScopeT` exists, or that a later admission
reconstruction cannot supply one. The same qualification applies to the selected reader skeleton
in the delta-field and profile-shape receipts. No checker completeness principle is used.

The four names distinguish an observed function-recursive admitted field, a checked skeleton with
a delta-recursive field, a concrete failure of the elimination-profile shape clause, and an
operational reader/checker failure. A failed level-order test is operational: it is never promoted
to a semantic profile refutation. Function-recursive observations use the actual Type-valued
admission views and a chosen fuel; they do not extract a fuel from admission's Prop existentials.
-/

namespace Rcic.Declarative

/-! ## Actual group occurrences -/

/-- The full data of one `EnvWfT.group` step, including its admission derivation. -/
structure ScopeGroupT : Type where
  E : ResolvedEnv
  f : Nat
  fm : CheckedMember
  ctors : List (Nat × CheckedMember)
  rr : Nat
  rm : CheckedMember
  target : ResolvedEnv
  hE : EnvWfT E
  hfam : fm.mclass = .inductiveM
  hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM
  hrec : rm.mclass = .recursorM
  hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) target

/-- A group in the actual derivation, rather than an arbitrary group present in the final map. -/
def EnvWfT.GroupAt : {E : ResolvedEnv} → EnvWfT E → ScopeGroupT → Prop
  | _, .empty, _ => False
  | _, .axiom _ _ _ _ hE _ _ _ _, g => hE.GroupAt g
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, g => hE.GroupAt g
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, g => hE.GroupAt g
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, g => hE.GroupAt g
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, g =>
      g = ⟨E, f, fm, ctors, rr, rm, E', hE, hfam, hctors, hrec, hmem⟩ ∨ hE.GroupAt g

/-- Every split of the written family telescope into parameters and indices is tried. -/
def ScopeGroupT.parameterSplits (g : ScopeGroupT) : List Nat :=
  List.range ((peelPisAll g.fm.mtype).1.length + 1)

/-! ## Function-recursive observations in the actual admission views -/

private def scopeAnalysisFunRecB : FieldAnalyze → Bool
  | .permitted (.recursive (Nat.succ _)) _ => true
  | _ => false

private theorem scopeAnalysisFunRecB_witness {a : FieldAnalyze}
    (h : scopeAnalysisFunRecB a = true) :
    ∃ inner indices, a = .permitted (.recursive (inner + 1)) indices := by
  cases a with
  | permitted shape indices =>
      cases shape with
      | nonrecursive => simp [scopeAnalysisFunRecB] at h
      | recursive inner =>
          cases inner with
          | zero => simp [scopeAnalysisFunRecB] at h
          | succ inner => exact ⟨inner, indices, rfl⟩
  | refused why => simp [scopeAnalysisFunRecB] at h
  | unresolved => simp [scopeAnalysisFunRecB] at h

/-- A field occurrence together with the exact positive `fieldAnalyze` equation. The recursive
    tail increments the depth, so the witness retains its position in the admission's fields. -/
def ScopeFieldsFunRecAt (E : ResolvedEnv) (fuel fam nuniv np ni : Nat) :
    Nat → List (Expr Nat) → Prop
  | _, [] => False
  | depth, D :: ds =>
      (∃ inner indices,
        fieldAnalyze E fuel fam nuniv np ni depth D =
          .permitted (.recursive (inner + 1)) indices) ∨
      ScopeFieldsFunRecAt E fuel fam nuniv np ni (depth + 1) ds

private def scopeFieldsFunRecB (E : ResolvedEnv) (fuel fam nuniv np ni : Nat) :
    Nat → List (Expr Nat) → Bool
  | _, [] => false
  | depth, D :: ds =>
      scopeAnalysisFunRecB (fieldAnalyze E fuel fam nuniv np ni depth D) ||
      scopeFieldsFunRecB E fuel fam nuniv np ni (depth + 1) ds

private theorem scopeFieldsFunRecB_witness (E : ResolvedEnv) (fuel fam nuniv np ni : Nat) :
    (depth : Nat) → (ds : List (Expr Nat)) →
    scopeFieldsFunRecB E fuel fam nuniv np ni depth ds = true →
    ScopeFieldsFunRecAt E fuel fam nuniv np ni depth ds
  | _, [], h => by cases h
  | depth, D :: ds, h => by
      rcases Bool.or_eq_true_iff.mp h with hD | hds
      · exact Or.inl (scopeAnalysisFunRecB_witness hD)
      · exact Or.inr (scopeFieldsFunRecB_witness E fuel fam nuniv np ni (depth + 1) ds hds)

/-- A structural finite scan; it needs no decidability instance for an existential over `Fin`. -/
private def scopeAnyFin : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, p => p ⟨0, Nat.zero_lt_succ n⟩ || scopeAnyFin n (fun i => p i.succ)

private theorem scopeAnyFin_witness : (n : Nat) → (p : Fin n → Bool) →
    scopeAnyFin n p = true → ∃ i, p i = true
  | 0, _, h => by cases h
  | n + 1, p, h => by
      rcases Bool.or_eq_true_iff.mp h with hz | ht
      · exact ⟨⟨0, Nat.zero_lt_succ n⟩, hz⟩
      · obtain ⟨i, hi⟩ := scopeAnyFin_witness n (fun i => p i.succ) ht
        exact ⟨i.succ, hi⟩

/-- The observation is indexed by the exact stored admission, including its prefix environment.
    Recursor admissions expose their own constructor views as well. -/
def IndGroupAdmitted.ScopeFunRecField {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : IndGroupAdmitted E r m) (fuel : Nat) : Prop :=
  match a with
  | .family _ _ _ _ _ => False
  | .constructor fv cv _ _ _ _ _ =>
      ScopeFieldsFunRecAt E fuel fv.ref fv.member.arity
        fv.parameters.length fv.indices.length fv.parameters.length cv.fields
  | .recursor a _ _ _ _ _ _ =>
      ∃ i : Fin a.constructors.length,
        ScopeFieldsFunRecAt E fuel a.family.ref a.family.member.arity
          a.family.parameters.length a.family.indices.length a.family.parameters.length
          (a.constructorViews i).fields

private def IndGroupAdmitted.scopeFunRecB {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : IndGroupAdmitted E r m) (fuel : Nat) : Bool :=
  match a with
  | .family _ _ _ _ _ => false
  | .constructor fv cv _ _ _ _ _ =>
      scopeFieldsFunRecB E fuel fv.ref fv.member.arity
        fv.parameters.length fv.indices.length fv.parameters.length cv.fields
  | .recursor a _ _ _ _ _ _ =>
      scopeAnyFin a.constructors.length (fun i =>
        scopeFieldsFunRecB E fuel a.family.ref a.family.member.arity
          a.family.parameters.length a.family.indices.length a.family.parameters.length
          (a.constructorViews i).fields)

private theorem IndGroupAdmitted.scopeFunRecB_witness {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : IndGroupAdmitted E r m) (fuel : Nat)
    (h : a.scopeFunRecB fuel = true) : a.ScopeFunRecField fuel := by
  cases a with
  | family hfresh view href hm hProfile => cases h
  | constructor fv cv hfresh h04 hContig h07 h08 =>
      exact scopeFieldsFunRecB_witness E fuel fv.ref fv.member.arity
        fv.parameters.length fv.indices.length fv.parameters.length cv.fields h
  | recursor a hfresh h04 h07 h08 h12 h14 =>
      obtain ⟨i, hi⟩ := scopeAnyFin_witness _ _ h
      exact ⟨i, scopeFieldsFunRecB_witness E fuel a.family.ref a.family.member.arity
        a.family.parameters.length a.family.indices.length a.family.parameters.length
        (a.constructorViews i).fields hi⟩

/-- An actual admitted member along this `GroupMembersT` derivation has a positive observation. -/
def GroupMembersT.ScopeFunRecField {S : ResolvedEnv} (fuel : Nat) :
    {E : ResolvedEnv} → {entries : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E entries E' → Prop
  | _, _, _, .nil _ => False
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ _ rest =>
      a.ScopeFunRecField fuel ∨ rest.ScopeFunRecField fuel

private def GroupMembersT.scopeFunRecB {S : ResolvedEnv} (fuel : Nat) :
    {E : ResolvedEnv} → {entries : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E entries E' → Bool
  | _, _, _, .nil _ => false
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ _ rest =>
      a.scopeFunRecB fuel || rest.scopeFunRecB fuel

private theorem GroupMembersT.scopeFunRecB_witness {S : ResolvedEnv} (fuel : Nat) :
    {E : ResolvedEnv} → {entries : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    (hmem : GroupMembersT S E entries E') →
    hmem.scopeFunRecB fuel = true → hmem.ScopeFunRecField fuel
  | _, _, _, .nil _, h => by cases h
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ _ rest, h => by
      rcases Bool.or_eq_true_iff.mp h with ha | hr
      · exact Or.inl (a.scopeFunRecB_witness fuel ha)
      · exact Or.inr (rest.scopeFunRecB_witness fuel hr)

/-! ## Receipts for the reader and the clauses of the existing test -/

/-- Clause names describe observed tests, not semantic nonexistence theorems. -/
inductive ScopeCheckClause : Type
  | family | constructors | layout | recursor | profileIndexOrder
  deriving DecidableEq, Repr

def ScopeCheckClause.test (clause : ScopeCheckClause) (C : CheckerT)
    (g : ScopeGroupT) (sk : GroupSkelT) : Bool :=
  match clause with
  | .family => famCheckB C g.E g.fm sk
  | .constructors => ctorsCheckB C g.E g.f g.fm sk g.ctors sk.ctors
  | .layout => decide (g.ctors.map Prod.fst = List.range' (g.f + 1) g.ctors.length)
  | .recursor => recCheckB C g.E g.f g.fm g.ctors g.rr g.rm sk
  | .profileIndexOrder =>
      sk.indices.all (fun d => levelIsZero sk.sort || C.levelLe d.2 sk.sort)

/-- The second, structural clause of `profileCheckB`, separated from its checker-dependent order
    clause. Failure means each of these written alternatives failed on this skeleton. -/
def scopeProfileShapeB (sk : GroupSkelT) : Bool :=
  decide (sk.elim = .propOnly) || !levelIsZero sk.sort || sk.ctors.isEmpty ||
    unitSkelB sk || structSkelB sk

inductive ScopeCheckerNoAnswerAt (C : CheckerT) (fuel : Nat) (g : ScopeGroupT)
    (np : Nat) : Type
  | reader
      (hread : groupSkel? C g.E fuel g.f g.fm g.ctors g.rm np = none)
  | clause (sk : GroupSkelT)
      (hread : groupSkel? C g.E fuel g.f g.fm g.ctors g.rm np = some sk)
      (which : ScopeCheckClause) (hfailed : which.test C g sk = false)

/-- A passing group test with a concrete delta-recursive field. This identifies the failed
    `hsndK` requirement of `groupInScopeT_of_check` for this checked skeleton. -/
structure ScopeDrecDAt (C : CheckerT) (fuel : Nat) (g : ScopeGroupT) (np : Nat) : Type where
  sk : GroupSkelT
  hread : groupSkel? C g.E fuel g.f g.fm g.ctors g.rm np = some sk
  hcheck : groupCheckB C g.E g.f g.fm g.ctors g.rr g.rm sk = true
  ctor : CtorSkelT
  hctor : ctor ∈ sk.ctors
  domain : Expr Nat
  indices : List (Expr Nat)
  hfield : FieldT.drecD domain indices ∈ ctor.fields

/-- All clauses before the structural profile clause passed. `hshape` is a concrete failure of
    that clause. It is not a claim that every possible view has an invalid `GroupProfileT`. -/
structure ScopeProfileOutsideAt (C : CheckerT) (fuel : Nat) (g : ScopeGroupT)
    (np : Nat) : Type where
  sk : GroupSkelT
  hread : groupSkel? C g.E fuel g.f g.fm g.ctors g.rm np = some sk
  hfamily : famCheckB C g.E g.fm sk = true
  hctors : ctorsCheckB C g.E g.f g.fm sk g.ctors sk.ctors = true
  hlayout : decide (g.ctors.map Prod.fst = List.range' (g.f + 1) g.ctors.length) = true
  hrec : recCheckB C g.E g.f g.fm g.ctors g.rr g.rm sk = true
  hindices : sk.indices.all (fun d => levelIsZero sk.sort || C.levelLe d.2 sk.sort) = true
  hshape : scopeProfileShapeB sk = false

/-- The delta receipt refutes the exact `hsndK` obligation for its own checked skeleton. -/
theorem ScopeDrecDAt.not_noDrecD {C : CheckerT} {fuel : Nat} {g : ScopeGroupT} {np : Nat}
    (receipt : ScopeDrecDAt C fuel g np) :
    ¬ (∀ k ∈ receipt.sk.ctors, ∀ d ∈ k.fields, d.isDrecD = false) := by
  intro hnd
  have h := hnd receipt.ctor receipt.hctor (.drecD receipt.domain receipt.indices) receipt.hfield
  simp [FieldT.isDrecD] at h

/-- A structural-profile receipt proves failure of the exact combined profile check. -/
theorem ScopeProfileOutsideAt.profileCheck_eq_false {C : CheckerT} {fuel : Nat}
    {g : ScopeGroupT} {np : Nat} (receipt : ScopeProfileOutsideAt C fuel g np) :
    profileCheckB C receipt.sk = false := by
  change (receipt.sk.indices.all (fun d => levelIsZero receipt.sk.sort || C.levelLe d.2 receipt.sk.sort) &&
    scopeProfileShapeB receipt.sk) = false
  simp only [receipt.hshape, Bool.and_false]

structure ScopeCandidatePassT (C : CheckerT) (fuel : Nat) (g : ScopeGroupT)
    (np : Nat) : Type where
  sk : GroupSkelT
  hread : groupSkel? C g.E fuel g.f g.fm g.ctors g.rm np = some sk
  hcheck : groupCheckB C g.E g.f g.fm g.ctors g.rr g.rm sk = true
  hnd : ∀ k ∈ sk.ctors, ∀ d ∈ k.fields, d.isDrecD = false

inductive ScopeAttemptFailure (C : CheckerT) (fuel : Nat) (g : ScopeGroupT)
    (np : Nat) : Prop
  | checker (receipt : ScopeCheckerNoAnswerAt C fuel g np)
  | drecD (receipt : ScopeDrecDAt C fuel g np)
  | profile (receipt : ScopeProfileOutsideAt C fuel g np)

private def scopeNoDrecDB (sk : GroupSkelT) : Bool :=
  sk.ctors.all (fun k => k.fields.all (fun d => !d.isDrecD))

private theorem scopeNoDrecDB_spec {sk : GroupSkelT} (h : scopeNoDrecDB sk = true) :
    ∀ k ∈ sk.ctors, ∀ d ∈ k.fields, d.isDrecD = false := by
  intro k hk d hd
  have hkd := List.all_eq_true.mp (List.all_eq_true.mp h k hk) d hd
  cases hD : d.isDrecD <;> simp_all

private theorem scopeAllFalseWitness {α : Type} (p : α → Bool) :
    (xs : List α) → xs.all p = false → ∃ x ∈ xs, p x = false
  | [], h => by cases h
  | x :: xs, h => by
      cases hx : p x with
      | false => exact ⟨x, List.mem_cons_self _ _, hx⟩
      | true =>
          have ht : xs.all p = false := by simpa only [List.all_cons, hx, Bool.true_and] using h
          obtain ⟨y, hy, hp⟩ := scopeAllFalseWitness p xs ht
          exact ⟨y, List.mem_cons_of_mem _ hy, hp⟩

private theorem scopeDrecD_of_false {sk : GroupSkelT} (h : scopeNoDrecDB sk = false) :
    ∃ k ∈ sk.ctors, ∃ D indices, FieldT.drecD D indices ∈ k.fields := by
  obtain ⟨k, hk, hfields⟩ := scopeAllFalseWitness
    (fun k : CtorSkelT => k.fields.all (fun d => !d.isDrecD)) sk.ctors h
  obtain ⟨d, hd, hD⟩ := scopeAllFalseWitness (fun d : FieldT => !d.isDrecD) k.fields hfields
  cases d with
  | plain D u => simp [FieldT.isDrecD] at hD
  | drec indices => simp [FieldT.isDrecD] at hD
  | drecD D indices => exact ⟨k, hk, D, indices, hd⟩

/-- An actual call of the reader, followed by the existing checks, supplies either a passing
    certificate or the precise failed clause. All branching here is on computable finite data. -/
theorem scopeCandidatePass_or_failure (C : CheckerT) (fuel : Nat) (g : ScopeGroupT) (np : Nat) :
    Nonempty (ScopeCandidatePassT C fuel g np) ∨ ScopeAttemptFailure C fuel g np := by
  cases hread : groupSkel? C g.E fuel g.f g.fm g.ctors g.rm np with
  | none => exact Or.inr (.checker (.reader hread))
  | some sk =>
      cases hf : famCheckB C g.E g.fm sk with
      | false => exact Or.inr (.checker (.clause sk hread .family hf))
      | true =>
          cases hc : ctorsCheckB C g.E g.f g.fm sk g.ctors sk.ctors with
          | false => exact Or.inr (.checker (.clause sk hread .constructors hc))
          | true =>
              cases hl : decide (g.ctors.map Prod.fst = List.range' (g.f + 1) g.ctors.length) with
              | false => exact Or.inr (.checker (.clause sk hread .layout hl))
              | true =>
                  cases hr : recCheckB C g.E g.f g.fm g.ctors g.rr g.rm sk with
                  | false => exact Or.inr (.checker (.clause sk hread .recursor hr))
                  | true =>
                      cases hi : sk.indices.all (fun d => levelIsZero sk.sort || C.levelLe d.2 sk.sort) with
                      | false => exact Or.inr (.checker (.clause sk hread .profileIndexOrder hi))
                      | true =>
                          cases hs : scopeProfileShapeB sk with
                          | false =>
                              exact Or.inr (.profile ⟨sk, hread, hf, hc, hl, hr, hi, hs⟩)
                          | true =>
                              have hp : profileCheckB C sk = true := by
                                change (sk.indices.all
                                  (fun d => levelIsZero sk.sort || C.levelLe d.2 sk.sort) &&
                                  scopeProfileShapeB sk) = true
                                simp only [hi, hs, Bool.true_and]
                              have hg : groupCheckB C g.E g.f g.fm g.ctors g.rr g.rm sk = true := by
                                simp only [groupCheckB, hf, hc, hl, hr, hp, Bool.true_and]
                              cases hn : scopeNoDrecDB sk with
                              | true => exact Or.inl ⟨⟨sk, hread, hg, scopeNoDrecDB_spec hn⟩⟩
                              | false =>
                                  obtain ⟨k, hk, D, indices, hd⟩ := scopeDrecD_of_false hn
                                  exact Or.inr (.drecD ⟨sk, hread, hg, k, hk, D, indices, hd⟩)

/-- A complete finite-search receipt: every written parameter split was attempted and failed in
    its specifically recorded way. This is not a quantification over checkers or fuel budgets. -/
def ScopeSearchFailure (C : CheckerT) (fuel : Nat) (g : ScopeGroupT) : Prop :=
  ∀ np ∈ g.parameterSplits, ScopeAttemptFailure C fuel g np

private theorem scopeSearchList (C : CheckerT) (fuel : Nat) (g : ScopeGroupT) :
    (splits : List Nat) →
    (∃ np ∈ splits, Nonempty (ScopeCandidatePassT C fuel g np)) ∨
      (∀ np ∈ splits, ScopeAttemptFailure C fuel g np)
  | [] => Or.inr (by simp)
  | np :: splits => by
      rcases scopeCandidatePass_or_failure C fuel g np with hpass | hfail
      · exact Or.inl ⟨np, List.mem_cons_self _ _, hpass⟩
      · rcases scopeSearchList C fuel g splits with hpass | hrest
        · obtain ⟨j, hj, hpass⟩ := hpass
          exact Or.inl ⟨j, List.mem_cons_of_mem _ hj, hpass⟩
        · refine Or.inr ?_
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hfail
          · exact hrest j hj

/-! ## The named, nonexclusive audit residue -/

/-- These are positive receipts about a particular admitted group and finite audit. They are not
    a semantic `¬GroupInScopeT` predicate. Each branch keeps the complete failed search. -/
inductive OutsideScope (g : ScopeGroupT) : Prop
  | funRecField (C : CheckerT) (fuel : Nat) (run : ScopeSearchFailure C fuel g)
      (field : g.hmem.ScopeFunRecField fuel)
  | drecDField (C : CheckerT) (fuel : Nat) (run : ScopeSearchFailure C fuel g)
      (np : Nat) (hsplit : np ∈ g.parameterSplits) (receipt : ScopeDrecDAt C fuel g np)
  | profileOutside (C : CheckerT) (fuel : Nat) (run : ScopeSearchFailure C fuel g)
      (np : Nat) (hsplit : np ∈ g.parameterSplits) (receipt : ScopeProfileOutsideAt C fuel g np)
  | checkerNoAnswer (C : CheckerT) (fuel : Nat) (run : ScopeSearchFailure C fuel g)
      (np : Nat) (hsplit : np ∈ g.parameterSplits) (receipt : ScopeCheckerNoAnswerAt C fuel g np)

/-- Prefer a witnessed delta-field or structural profile failure from any attempted split to an
    operational fallback. The fallback still carries an actual failed reader or named clause. -/
private theorem scopeOutsideScan (C : CheckerT) (fuel : Nat) (g : ScopeGroupT)
    (run : ScopeSearchFailure C fuel g)
    (fallback : ∃ np ∈ g.parameterSplits, Nonempty (ScopeCheckerNoAnswerAt C fuel g np)) :
    (splits : List Nat) → (∀ np ∈ splits, np ∈ g.parameterSplits) → OutsideScope g
  | [], _ => by
      obtain ⟨np, hnp, ⟨receipt⟩⟩ := fallback
      exact .checkerNoAnswer C fuel run np hnp receipt
  | np :: splits, hsub => by
      have hnp := hsub np (List.mem_cons_self _ _)
      cases run np hnp with
      | checker receipt =>
          exact scopeOutsideScan C fuel g run fallback splits
            (fun j hj => hsub j (List.mem_cons_of_mem _ hj))
      | drecD receipt => exact .drecDField C fuel run np hnp receipt
      | profile receipt => exact .profileOutside C fuel run np hnp receipt

theorem ScopeGroupT.outside_of_searchFailure (g : ScopeGroupT) (C : CheckerT) (fuel : Nat)
    (run : ScopeSearchFailure C fuel g) : OutsideScope g := by
  cases hfun : g.hmem.scopeFunRecB fuel with
  | true => exact .funRecField C fuel run (g.hmem.scopeFunRecB_witness fuel hfun)
  | false =>
      have hz : 0 ∈ g.parameterSplits := by simp [ScopeGroupT.parameterSplits]
      cases run 0 hz with
      | checker receipt =>
          exact scopeOutsideScan C fuel g run ⟨0, hz, ⟨receipt⟩⟩ g.parameterSplits (fun _ h => h)
      | drecD receipt => exact .drecDField C fuel run 0 hz receipt
      | profile receipt => exact .profileOutside C fuel run 0 hz receipt

/-- The parameterized one-group audit. The success certificate retains the actual reader call. -/
theorem ScopeGroupT.scopeCheck_or_outside (g : ScopeGroupT) (C : CheckerT) (fuel : Nat) :
    (∃ np ∈ g.parameterSplits, Nonempty (ScopeCandidatePassT C fuel g np)) ∨ OutsideScope g := by
  rcases scopeSearchList C fuel g g.parameterSplits with hpass | hfail
  · exact Or.inl hpass
  · exact Or.inr (g.outside_of_searchFailure C fuel hfail)

/-! ## Induction on the environment derivation -/

structure ScopeAuditConfig : Type where
  checker : CheckerT
  fuel : Nat

/-- Executable expression-node count; no generated `SizeOf` instance is needed. -/
private def scopeExprSize : Expr Nat → Nat
  | .bvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app f x => 1 + scopeExprSize f + scopeExprSize x
  | .lam A b => 1 + scopeExprSize A + scopeExprSize b
  | .pi A B => 1 + scopeExprSize A + scopeExprSize B
  | .letE A v b => 1 + scopeExprSize A + scopeExprSize v + scopeExprSize b
  | .lit _ => 1

/-- A reproducible positive default budget depending on the expression-node counts of the
    group's stored types. It is a resource limit, not a claimed completeness bound for conversion
    or field analysis. -/
def ScopeGroupT.auditFuel (g : ScopeGroupT) : Nat :=
  64 + 4 * (scopeExprSize g.fm.mtype + scopeExprSize g.rm.mtype +
    g.ctors.foldl (fun total c => total + scopeExprSize c.2.mtype) 0)

/-- The default is the existing conversion-aware certified checker, at the documented budget. -/
def ScopeGroupT.defaultAudit (g : ScopeGroupT) : ScopeAuditConfig :=
  ⟨convChecker g.auditFuel, g.auditFuel⟩

/-- The stronger parameterized API builds the existing `ScopeCheck`, or supplies a named residue
    at an actual group. Singleton extensions preserve their prefix result. -/
theorem EnvWfT.scopeCheck_or_outsideWith (config : ScopeGroupT → ScopeAuditConfig) :
    {E : ResolvedEnv} → (hW : EnvWfT E) →
    hW.ScopeCheck ∨ ∃ g, hW.GroupAt g ∧ OutsideScope g
  | _, .empty => Or.inl True.intro
  | _, .axiom _ _ _ _ hE _ _ _ _ => hE.scopeCheck_or_outsideWith config
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.scopeCheck_or_outsideWith config
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => hE.scopeCheck_or_outsideWith config
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => hE.scopeCheck_or_outsideWith config
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem => by
      let g : ScopeGroupT := ⟨E, f, fm, ctors, rr, rm, E', hE, hfam, hctors, hrec, hmem⟩
      rcases hE.scopeCheck_or_outsideWith config with hprefix | ⟨g', hat, hout⟩
      · rcases g.scopeCheck_or_outside (config g).checker (config g).fuel with hpass | hout
        · obtain ⟨np, hnp, ⟨pass⟩⟩ := hpass
          exact Or.inl ⟨hprefix, (config g).checker, pass.sk, pass.hcheck, pass.hnd⟩
        · exact Or.inr ⟨g, Or.inl rfl, hout⟩
      · exact Or.inr ⟨g', Or.inr hat, hout⟩

/-- The requested constructive dichotomy. Its positive branch literally composes the existing
    scope-test theorem; its other branch is the nonexclusive audit residue documented above. -/
theorem EnvWfT.inScope_or_outside {E : ResolvedEnv} (hW : EnvWfT E) :
    hW.InScope ∨ ∃ g, hW.GroupAt g ∧ OutsideScope g := by
  rcases hW.scopeCheck_or_outsideWith ScopeGroupT.defaultAudit with hcheck | hout
  · exact Or.inl (hW.inScope_of_scopeCheck hcheck)
  · exact Or.inr hout

end Rcic.Declarative

#print axioms Rcic.Declarative.EnvWfT.scopeCheck_or_outsideWith
#print axioms Rcic.Declarative.EnvWfT.inScope_or_outside
