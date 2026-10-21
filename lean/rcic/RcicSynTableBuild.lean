import rcic.RcicSynTable
import rcic.RcicSynGroupStage

/-!
# S2 δ half of `buildTableSyntax` — erased-table syntax with real provenance

`research/rcic/sortrow/S2_ERASED_TABLE_COVERAGE.md` §1–2. The builder walks the actual
`EnvWfT` construction tree and emits, for every `.definition` node, the bare nullary δ
rule `deltaRule r Db`, where `Db` is the same enriched body derivation that
`enrichEnvWfT` installs as the node's `hv` field. `axiom`/`thm`/`opaque`/`group` nodes
preserve the accumulated table and add nothing (group members never have bodies, so δ
never reaches one — the ι part is a separate item). Every emitted rule carries a
`RuleOrigin` back into the real node; no caller-supplied table or correctness premise
is consulted.

Deliverables:

- `RuleOrigin` — provenance into the actual tree (`defHere` at the real singleton
  node, `under*` forwarding parents, `groupMember` a real `GroupStageAt` cursor, used
  by the ι half).
- `RuleEntry` / `buildTableSyntax` / `tableOf`.
- `head_mem_build`, `major_none_tableOf`, `tableWF_build`.
- `deltaRule_lookup` — the transparent member's real δ entry, characterized by the
  environment's own `EnvWfP.defAdm` admission derivation (`DefAdm.hv`).
- Teeth (`§5`): an ablated builder that drops δ rules still satisfies `TableWF` but
  fails `deltaRule_lookup`-style coverage; the origin equation pins the emitted rhs
  to the member's own stored body (a same-type body swap is refused); the builder is
  a function of `hEnv` alone.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `RuleOrigin` -/

/-- Where a table rule comes from: `defHere` is the real `.definition` node that emitted
the δ rule; each `under*` constructor forwards the same origin through one real parent
step of the `EnvWfT` tree; `groupMember` is a real `GroupStageAt` cursor into the node's
`GroupMembersT` chain (no δ rule is emitted there — it exists for the ι half). There is
no constructor for a fabricated or reordered position. -/
inductive RuleOrigin : {E : ResolvedEnv} → EnvWfT E → Type
  | defHere {E : ResolvedEnv} {r : Nat} {A v : Expr Nat} {u : Level}
      {hE : EnvWfT E} {hfresh : E.members r = none}
      {hA : HasTyT E 0 [] A (.sort u)} {hv : HasTyT E 0 [] v A}
      {hclA : ∀ k, lift k 1 A = A} {hclv : ∀ k, lift k 1 v = v}
      {hlvlA : exprLevelsBounded 0 A = true} {hlvlv : exprLevelsBounded 0 v = true} :
      RuleOrigin (.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv)
  | underAxiom {E : ResolvedEnv} {r : Nat} {A : Expr Nat} {u : Level}
      {hE : EnvWfT E} {hfresh : E.members r = none} {hA : HasTyT E 0 [] A (.sort u)}
      {hcl : ∀ k, lift k 1 A = A} {hlvl : exprLevelsBounded 0 A = true}
      (p : RuleOrigin hE) :
      RuleOrigin (.axiom E r A u hE hfresh hA hcl hlvl)
  | underDefinition {E : ResolvedEnv} {r : Nat} {A v : Expr Nat} {u : Level}
      {hE : EnvWfT E} {hfresh : E.members r = none}
      {hA : HasTyT E 0 [] A (.sort u)} {hv : HasTyT E 0 [] v A}
      {hclA : ∀ k, lift k 1 A = A} {hclv : ∀ k, lift k 1 v = v}
      {hlvlA : exprLevelsBounded 0 A = true} {hlvlv : exprLevelsBounded 0 v = true}
      (p : RuleOrigin hE) :
      RuleOrigin (.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv)
  | underThm {E : ResolvedEnv} {r : Nat} {A p' : Expr Nat}
      {hE : EnvWfT E} {hfresh : E.members r = none}
      {hA : HasTyT E 0 [] A (.sort .zero)} {hp : HasTyT E 0 [] p' A}
      {hclA : ∀ k, lift k 1 A = A} {hclp : ∀ k, lift k 1 p' = p'}
      {hlvlA : exprLevelsBounded 0 A = true} {hlvlp : exprLevelsBounded 0 p' = true}
      (p : RuleOrigin hE) :
      RuleOrigin (.thm E r A p' hE hfresh hA hp hclA hclp hlvlA hlvlp)
  | underOpaque {E : ResolvedEnv} {r : Nat} {A v : Expr Nat} {u : Level}
      {hE : EnvWfT E} {hfresh : E.members r = none}
      {hA : HasTyT E 0 [] A (.sort u)} {hv : HasTyT E 0 [] v A}
      {hclA : ∀ k, lift k 1 A = A} {hclv : ∀ k, lift k 1 v = v}
      {hlvlA : exprLevelsBounded 0 A = true} {hlvlv : exprLevelsBounded 0 v = true}
      (p : RuleOrigin hE) :
      RuleOrigin (.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv)
  | underGroup {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
      {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember} {E' : ResolvedEnv}
      {hE : EnvWfT E} {hfam : fm.mclass = .inductiveM}
      {hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM} {hrec : rm.mclass = .recursorM}
      {hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'}
      (p : RuleOrigin hE) :
      RuleOrigin (.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)
  | groupMember {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
      {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember} {E' : ResolvedEnv}
      {hE : EnvWfT E} {hfam : fm.mclass = .inductiveM}
      {hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM} {hrec : rm.mclass = .recursorM}
      {hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'}
      {Eᵢ : ResolvedEnv} (stage : GroupStageAt hmem Eᵢ) :
      RuleOrigin (.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)

/-! ## §2 `RuleEntry`, the emitted δ body, `buildTableSyntax`, `tableOf` -/

/-- One emitted rule together with its provenance into `hEnv`. -/
structure RuleEntry {E : ResolvedEnv} (hEnv : EnvWfT E) where
  rule : CRule
  origin : RuleOrigin hEnv

/-- The body derivation a `.definition` node's δ rule erases: the same enrichment
`enrichEnvWfT` installs as the node's `hv` field, so the emitted `deltaRule` is exactly
the admission derivation the environment itself stores. -/
noncomputable def defBodyAt {E : ResolvedEnv} {A v : Expr Nat}
    (hE : EnvWfT E) (hv : HasTyT E 0 [] v A) : TyP E 0 [] v A :=
  enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E)
    (memberSortP_of_envWfP (enrichEnvWfT hE)) (letCtxConvP_of_envWfT hE) (.nil E 0) hv

/-- The erased-rule table, computed from the actual `EnvWfT` tree. `.definition` adds
exactly one nullary bare `deltaRule` for that node's own body; every other node
preserves the accumulated table (ι rules for `group` are a separate item). -/
noncomputable def buildTableSyntax :
    {E : ResolvedEnv} → (hEnv : EnvWfT E) → List (RuleEntry hEnv)
  | _, .empty => []
  | _, .axiom _ _ _ _ hE _ _ _ _ =>
      (buildTableSyntax hE).map fun e => ⟨e.rule, .underAxiom e.origin⟩
  | _, .definition _ r _ _ _ hE _ _ hv _ _ _ _ =>
      ⟨deltaRule r (defBodyAt hE hv), .defHere⟩ ::
        (buildTableSyntax hE).map fun e => ⟨e.rule, .underDefinition e.origin⟩
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ =>
      (buildTableSyntax hE).map fun e => ⟨e.rule, .underThm e.origin⟩
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ =>
      (buildTableSyntax hE).map fun e => ⟨e.rule, .underOpaque e.origin⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _ =>
      (buildTableSyntax hE).map fun e => ⟨e.rule, .underGroup e.origin⟩

/-- The bare rule list the table predicates consume. -/
noncomputable def tableOf {E : ResolvedEnv} (hEnv : EnvWfT E) : List CRule :=
  (buildTableSyntax hEnv).map (·.rule)

theorem tableOf_empty : tableOf .empty = [] := rfl

theorem tableOf_axiom {E : ResolvedEnv} {r : Nat} {A : Expr Nat} {u : Level}
    {hE : EnvWfT E} {hfresh : E.members r = none} {hA : HasTyT E 0 [] A (.sort u)}
    {hcl : ∀ k, lift k 1 A = A} {hlvl : exprLevelsBounded 0 A = true} :
    tableOf (.axiom E r A u hE hfresh hA hcl hlvl) = tableOf hE := by
  simp [tableOf, buildTableSyntax, List.map_map]

theorem tableOf_definition {E : ResolvedEnv} {r : Nat} {A v : Expr Nat} {u : Level}
    {hE : EnvWfT E} {hfresh : E.members r = none}
    {hA : HasTyT E 0 [] A (.sort u)} {hv : HasTyT E 0 [] v A}
    {hclA : ∀ k, lift k 1 A = A} {hclv : ∀ k, lift k 1 v = v}
    {hlvlA : exprLevelsBounded 0 A = true} {hlvlv : exprLevelsBounded 0 v = true} :
    tableOf (.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) =
      deltaRule r (defBodyAt hE hv) :: tableOf hE := by
  simp [tableOf, buildTableSyntax, List.map_map]

theorem tableOf_thm {E : ResolvedEnv} {r : Nat} {A p : Expr Nat}
    {hE : EnvWfT E} {hfresh : E.members r = none}
    {hA : HasTyT E 0 [] A (.sort .zero)} {hp : HasTyT E 0 [] p A}
    {hclA : ∀ k, lift k 1 A = A} {hclp : ∀ k, lift k 1 p = p}
    {hlvlA : exprLevelsBounded 0 A = true} {hlvlp : exprLevelsBounded 0 p = true} :
    tableOf (.thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp) = tableOf hE := by
  simp [tableOf, buildTableSyntax, List.map_map]

theorem tableOf_opaque {E : ResolvedEnv} {r : Nat} {A v : Expr Nat} {u : Level}
    {hE : EnvWfT E} {hfresh : E.members r = none}
    {hA : HasTyT E 0 [] A (.sort u)} {hv : HasTyT E 0 [] v A}
    {hclA : ∀ k, lift k 1 A = A} {hclv : ∀ k, lift k 1 v = v}
    {hlvlA : exprLevelsBounded 0 A = true} {hlvlv : exprLevelsBounded 0 v = true} :
    tableOf (.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) = tableOf hE := by
  simp [tableOf, buildTableSyntax, List.map_map]

theorem tableOf_group {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember} {E' : ResolvedEnv}
    {hE : EnvWfT E} {hfam : fm.mclass = .inductiveM}
    {hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM} {hrec : rm.mclass = .recursorM}
    {hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'} :
    tableOf (.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) = tableOf hE := by
  simp [tableOf, buildTableSyntax, List.map_map]

/-! ## §3 table invariants (`head_mem_build`, `major_none_tableOf`, `tableWF_build`) -/

/-- Every emitted rule's head resolves to a member of the environment the node
actually built — provenance is a lookup, never a label. -/
theorem head_mem_build : {E : ResolvedEnv} → (hEnv : EnvWfT E) →
    ∀ ρ ∈ tableOf hEnv, ∃ m, E.members ρ.head = some m
  | _, .empty, _, h => (List.not_mem_nil _ h).elim
  | _, .axiom E r' _ _ hE hfresh _ _ _, ρ, hρ => by
      rw [tableOf_axiom] at hρ
      rcases head_mem_build hE ρ hρ with ⟨m, hm⟩
      exact ⟨m, envExt_extendEnv _ hfresh _ _ hm⟩
  | _, .definition E r' _ _ _ hE hfresh _ _ _ _ _ _, ρ, hρ => by
      rw [tableOf_definition] at hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · exact ⟨⟨.definitionM, 0, _, some _⟩, members_extend_self _ _ _⟩
      · rcases head_mem_build hE ρ hρ' with ⟨m, hm⟩
        exact ⟨m, envExt_extendEnv _ hfresh _ _ hm⟩
  | _, .thm E r' _ _ hE hfresh _ _ _ _ _ _, ρ, hρ => by
      rw [tableOf_thm] at hρ
      rcases head_mem_build hE ρ hρ with ⟨m, hm⟩
      exact ⟨m, envExt_extendEnv _ hfresh _ _ hm⟩
  | _, .opaque E r' _ _ _ hE hfresh _ _ _ _ _ _, ρ, hρ => by
      rw [tableOf_opaque] at hρ
      rcases head_mem_build hE ρ hρ with ⟨m, hm⟩
      exact ⟨m, envExt_extendEnv _ hfresh _ _ hm⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem, ρ, hρ => by
      rw [tableOf_group] at hρ
      rcases head_mem_build hE ρ hρ with ⟨m, hm⟩
      exact ⟨m, groupMembersT_ext hmem _ _ hm⟩

/-- Every emitted rule is bare (`major = none`) — the δ half emits no ι/constructor
rules. -/
theorem major_none_tableOf : {E : ResolvedEnv} → (hEnv : EnvWfT E) →
    ∀ ρ ∈ tableOf hEnv, ρ.major = none
  | _, .empty, _, h => (List.not_mem_nil _ h).elim
  | _, .axiom _ _ _ _ hE _ _ _ _, ρ, hρ => by
      rw [tableOf_axiom] at hρ; exact major_none_tableOf hE ρ hρ
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, ρ, hρ => by
      rw [tableOf_definition] at hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · rfl
      · exact major_none_tableOf hE ρ hρ'
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, ρ, hρ => by
      rw [tableOf_thm] at hρ; exact major_none_tableOf hE ρ hρ
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, ρ, hρ => by
      rw [tableOf_opaque] at hρ; exact major_none_tableOf hE ρ hρ
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _, ρ, hρ => by
      rw [tableOf_group] at hρ; exact major_none_tableOf hE ρ hρ

/-- The computed table satisfies `TableWF`: δ rules are closed (`ClosedWf` of the
enriched body), and every head is fresh by `head_mem_build` against the node's own
`hfresh` side condition. -/
theorem tableWF_build : {E : ResolvedEnv} → (hEnv : EnvWfT E) → TableWF (tableOf hEnv)
  | _, .empty => tableWF_nil
  | _, .axiom _ _ _ _ hE _ _ _ _ => by rw [tableOf_axiom]; exact tableWF_build hE
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv => by
      rw [tableOf_definition]
      refine tableWF_cons_deltaRule (tableWF_build hE) r ?_ ?_ ?_
      · exact closedWf_enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E)
          (memberSortP_of_envWfP (enrichEnvWfT hE)) (letCtxConvP_of_envWfT hE)
          (.nil E 0) hv
      · intro σ hσ hhead
        rcases head_mem_build hE σ hσ with ⟨m, hm⟩
        rw [hhead] at hm
        exact Option.noConfusion (hfresh.symm.trans hm)
      · intro ρ hρ d m' hm'
        rw [major_none_tableOf hE ρ hρ] at hm'
        exact Option.noConfusion hm'
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => by rw [tableOf_thm]; exact tableWF_build hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => by rw [tableOf_opaque]; exact tableWF_build hE
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _ => by rw [tableOf_group]; exact tableWF_build hE

/-- `Eq.rec` along a proof of `a = a` collapses: the scrutinee is `rfl` up to proof
irrelevance. Used to discharge the `subst`/`injection` transports inside
`EnvWfP.defAdm`'s same-head arms, where every transported equality is reflexive
after the caller's own substitutions. -/
theorem eqRec_self {α : Sort u} {a : α} {motive : (b : α) → a = b → Sort v}
    (v : motive a (Eq.refl a)) (p : a = a) : @Eq.rec α a motive v a p = v := by
  rw [show p = Eq.refl a from Subsingleton.elim _ _]

theorem eqNdrec_self {α : Sort u} {a : α} {motive : α → Sort v}
    (v : motive a) (p : a = a) : @Eq.ndrec α a motive v a p = v := by
  rw [show p = Eq.refl a from Subsingleton.elim _ _]

/-- `Option.noConfusion` on a reflexive `some`-equality applies its branch to `rfl`. -/
theorem optNoConf_self {α : Type u} {P : Sort v} {a : α}
    (h : (some a : Option α) = some a) (f : a = a → P) :
    Option.noConfusion h f = f rfl := by
  rw [show h = rfl from Subsingleton.elim _ _]

/-- `cases h :`-shaped `Decidable.rec` on a known `isFalse` outcome collapses to the
    `isFalse` arm. `EnvWfP.defAdm`'s match is compiled with the scrutinee embedded in
    the motive and the trailing `pf : e = e` argument, so ordinary `rw`/`cases h :`
    cannot rewrite it; rewriting the whole application sidesteps the dependent
    abstraction. (`D` is constant in the uses here.) -/
theorem decRec_isFalse {p : Prop} {e : Decidable p} {D : Sort _}
    {aF : ∀ (h : ¬p), e = isFalse h → D} {aT : ∀ (h : p), e = isTrue h → D}
    (h : ¬p) (he : e = isFalse h) (pf : e = e) :
    Decidable.rec (motive := fun t => e = t → D) aF aT e pf = aF h he := by
  subst he; rfl

/-- The `isTrue` half of `decRec_isFalse`. -/
theorem decRec_isTrue {p : Prop} {e : Decidable p} {D : Sort _}
    {aF : ∀ (h : ¬p), e = isFalse h → D} {aT : ∀ (h : p), e = isTrue h → D}
    (h : p) (he : e = isTrue h) (pf : e = e) :
    Decidable.rec (motive := fun t => e = t → D) aF aT e pf = aT h he := by
  subst he; rfl

/-! ## §4 `deltaRule_lookup` -/

/-- The real δ lookup: a transparent member (`transparent m.mclass = true`, i.e. a
`.definition` member with `m.body = some b`) has exactly its `deltaRule` in the computed
table, built from the environment's own admission derivation `EnvWfP.defAdm`. No
caller-supplied body or table is consulted. -/
theorem deltaRule_lookup : {E : ResolvedEnv} → (hEnv : EnvWfT E) →
    {r : Nat} → {m : CheckedMember} → {b : Expr Nat} →
    (hres : E.members r = some m) → (hbody : m.body = some b) →
    (htr : transparent m.mclass = true) →
    ∃ e ∈ buildTableSyntax hEnv,
      e.rule = deltaRule r ((enrichEnvWfT hEnv).defAdm hres hbody htr).hv
  | _, .empty, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r' A u hE hfresh hA hcl hlvl, r, m, b, h, hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.axiomM, 0, A, none⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          rcases deltaRule_lookup hE ((members_extend_ne E _ hr).symm.trans h) hb htr with
            ⟨e, hmem, hrule⟩
          refine ⟨⟨e.rule, .underAxiom e.origin⟩, List.mem_map.mpr ⟨e, hmem, rfl⟩, ?_⟩
          rw [hrule]
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
  | _, .definition E r' A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, r, m, b, h, hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.definitionM, 0, A, some v⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          have hbv : v = b := Option.some.inj hb
          subst hbv
          refine ⟨⟨deltaRule r (defBodyAt hE hv), .defHere⟩, List.Mem.head _, ?_⟩
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isTrue rfl hdec]
          simp only [eqRec_self, eqNdrec_self, optNoConf_self]
          rfl
      | isFalse hr =>
          rcases deltaRule_lookup hE ((members_extend_ne E _ hr).symm.trans h) hb htr with
            ⟨e, hmem, hrule⟩
          refine ⟨⟨e.rule, .underDefinition e.origin⟩,
            List.Mem.tail _ (List.mem_map.mpr ⟨e, hmem, rfl⟩), ?_⟩
          rw [hrule]
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
  | _, .thm E r' A p hE hfresh hA hp hclA hclp hlvlA hlvlp, r, m, b, h, hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.theoremM, 0, A, some p⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          rcases deltaRule_lookup hE ((members_extend_ne E _ hr).symm.trans h) hb htr with
            ⟨e, hmem, hrule⟩
          refine ⟨⟨e.rule, .underThm e.origin⟩, List.mem_map.mpr ⟨e, hmem, rfl⟩, ?_⟩
          rw [hrule]
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
  | _, .opaque E r' A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, r, m, b, h, hb, htr => by
      cases hdec : Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm : ⟨.opaqueM, 0, A, some v⟩ = m :=
            Option.some.inj ((members_extend_self E r _).symm.trans h)
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          rcases deltaRule_lookup hE ((members_extend_ne E _ hr).symm.trans h) hb htr with
            ⟨e, hmem, hrule⟩
          refine ⟨⟨e.rule, .underOpaque e.origin⟩, List.mem_map.mpr ⟨e, hmem, rfl⟩, ?_⟩
          rw [hrule]
          simp only [enrichEnvWfT, EnvWfP.defAdm]
          rw [decRec_isFalse hr hdec]
          simp only [DefAdm.step, DefAdm.lift']
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, r, m, b, h, hb, htr => by
      rcases deltaRule_lookup hE
          ((enrichGroupMembersT (cvWalkHyp_of_envWfT hE)
            (memberSortP_of_envWfP (enrichEnvWfT hE)) hmem).body_old h hb) hb htr with
        ⟨e, hmem', hrule⟩
      refine ⟨⟨e.rule, .underGroup e.origin⟩, List.mem_map.mpr ⟨e, hmem', rfl⟩, ?_⟩
      rw [hrule]
      simp only [enrichEnvWfT, EnvWfP.defAdm, DefAdm.lift']

/-! ## §5 Teeth -/

/-- The pin fixture: one transparent definition `7 := Prop : Type 0` over `emptyEnv`. -/
def pinTableDef :
    EnvWfT (extendEnv emptyEnv 7 ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩) :=
  .definition emptyEnv 7 (.sort (.succ .zero)) (.sort .zero) (.succ (.succ .zero))
    .empty rfl (.sort [] (.succ .zero)) (.sort [] .zero)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- The ablated builder: identical walk, but the `.definition` node emits nothing
    (the δ-deletion bug). -/
noncomputable def buildTableAblated :
    {E : ResolvedEnv} → (hEnv : EnvWfT E) → List CRule
  | _, .empty => []
  | _, .axiom _ _ _ _ hE _ _ _ _ => buildTableAblated hE
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => buildTableAblated hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => buildTableAblated hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => buildTableAblated hE
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _ => buildTableAblated hE

/-- TOOTH 1 (deletion rejected by coverage, not by `TableWF`): the weak check still
    accepts the ablated table — `TableWF []` holds — while the real coverage predicate
    finds no rule at head `7`. -/
theorem tooth_ablated_tableWF : TableWF (buildTableAblated pinTableDef) := tableWF_nil

theorem tooth_ablated_no_delta :
    ∀ ρ ∈ buildTableAblated pinTableDef, ρ.head ≠ 7 :=
  fun _ h => (List.not_mem_nil _ h).elim

/-- ... while the real builder's coverage produces the entry, with its real head. -/
theorem tooth_real_covers :
    ∃ e ∈ buildTableSyntax pinTableDef,
      e.rule = deltaRule 7 ((enrichEnvWfT pinTableDef).defAdm
        (members_extend_self _ _ _) rfl rfl).hv :=
  deltaRule_lookup pinTableDef (members_extend_self _ _ _) rfl rfl

/-- TOOTH 2 (body swap refused by the origin equation): the member record's stored
    body is pinned — `m.body = some b'` forces `b'` to be the original body, so a
    same-type replacement cannot satisfy `m.body = some b` in `deltaRule_lookup`. -/
theorem tooth_body_pinned {b' : Expr Nat}
    (hb' : (⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ : CheckedMember).body =
      some b') :
    b' = .sort .zero :=
  (Option.some.inj (show (some (.sort .zero) : Option (Expr Nat)) = some b' from hb')).symm

end Rcic.Syn
