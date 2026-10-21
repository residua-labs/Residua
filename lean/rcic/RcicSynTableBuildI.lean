import rcic.RcicSynTableBuild
import rcic.RcicSynGroupStage
import rcic.RcicSynNatSuccIota

/-!
# `tableOfI` — `tableOf` plus the erased ι rules of every admitted group (PART 1)

`buildTableSyntax`/`tableOf` carry only δ rules: the `.group` arm forwards the
accumulated table unchanged, so `AllBelowScoped`/`StepSuppliers` read `false`
against `tableOf natEnvUWfT` at every weight — the group's ι rules are never
issued. This module is the additive builder from the tableOfI split: it does
not touch `tableOf`; it reuses `RuleEntry`/`RuleOrigin` verbatim and emits, per
`.group` node, one `CRule` per constructor whose field analysis admits a rule
(the same gate `IotaWitness` uses — function-recursive fields and unsafe index
terms have no witness and get no rule).

Scope of the erased rhs. The rule template is `λ^K`, `K = nargs + ctorSpine`,
applied to `args ++ bs`; spine argument `p ↦ .bvar (K-1-p)`. The body is the
ctor's minor applied to each field plus, for `directRec` fields, the recursive
call `rec (params·motive·minors prefix) (field's own indices) field` —
`familyIdx`/`recCallField`'s order. Index terms are erased by `eraseTelK`,
which maps a telescope bvar to its spine argument; `.letE` inside an index
term is gated out by `iotaIdxSafe` (its `.star` arm is dead code — the honest
erased form needs an `instantiate` this builder does not perform), and `.lit`
erases to `natExpand`'s fixed shape. `ls'` is unused: the ctor telescope
instantiates at the redex's rec levels (`IotaWitness.hctorAfter` uses `w.ls`),
which is `rhs`'s first argument.

PART 1 lands the interface only: `iotaRulesOf`, `buildTableSyntaxI`,
`tableOfI`, and the Nat positive control pinning the emitted succ rule to the
landed `natSuccRule` kernel. `TableWF` over `tableOfI` is the next part.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 erased-template pieces -/

/-- `.lit n`'s erased shape: `natExpand` is hardcoded at refs `1`/`2`
(zero/succ), env-independent. -/
def eraseLit : Nat → ETm
  | 0 => .const 1 []
  | n + 1 => .app (.const 2 []) (eraseLit n)

/-- Erase a subterm of the `t`-th ctor-telescope domain into the `K`-λ rule
template at the redex's rec levels `ls`. Local binder depth `d`; a telescope
bvar `k` (`k - d < t`) names telescope domain `t-1-(k-d)`, i.e. ctor-spine
argument `nargs + (t-1-(k-d))`, i.e. `.bvar (K-1-(…))`. `.letE` arms are
unreachable under the `iotaIdxSafe` gate. -/
def eraseTelK (K nargs t : Nat) (ls : List Level) : Nat → Expr Nat → ETm
  | d, .bvar k =>
      if k < d then .bvar k else .bvar (K - 1 - (nargs + t - 1 - (k - d)))
  | _, .sort l => .sort (instLevel ls l)
  | _, .const r ms => .const r (ms.map (instLevel ls))
  | d, .app f a => .app (eraseTelK K nargs t ls d f) (eraseTelK K nargs t ls d a)
  | d, .lam _ b => .lam (eraseTelK K nargs t ls (d + 1) b)
  | d, .pi a b => .pi (eraseTelK K nargs t ls d a) (eraseTelK K nargs t ls (d + 1) b)
  | _, .letE _ _ _ => .star
  | _, .lit n => eraseLit n

/-- An index term is safely erasable at telescope position `t`: every
telescope bvar resolves inside the ctor telescope, and no `letE` survives. -/
def iotaIdxSafe (t : Nat) : Nat → Expr Nat → Bool
  | d, .bvar k => k < d || k - d < t
  | _, .sort _ => true
  | _, .const _ _ => true
  | d, .app f a => iotaIdxSafe t d f && iotaIdxSafe t d a
  | d, .lam _ b => iotaIdxSafe t (d + 1) b
  | d, .pi a b => iotaIdxSafe t d a && iotaIdxSafe t (d + 1) b
  | _, .letE _ _ _ => false
  | _, .lit _ => true

/-- The erased field arguments for one ctor body: each field itself, and for
`directRec` fields the recursive call `rec prefix idx field` — `recCallField`'s
erased shape. `ds`/`ks` are the aligned field domains and kinds; `j` counts
fields. -/
def iotaFieldArgs (rr : Nat) (ls : List Level) (K nargs nparams nMinors : Nat) :
    List (Expr Nat) → List RecKind → Nat → List ETm
  | _, [], _ => []
  | [], _ :: _, _ => []
  | A :: ds, k :: ks, j =>
      let fvar := ETm.bvar (K - 1 - (nargs + nparams + j))
      let rest := iotaFieldArgs rr ls K nargs nparams nMinors ds ks (j + 1)
      match k with
      | .plain => fvar :: rest
      | .directRec =>
          let preMajor :=
            (List.range (nparams + 1 + nMinors)).map fun p => .bvar (K - 1 - p)
          let idx := (familyIdx nparams A).map (eraseTelK K nargs (nparams + j) ls 0)
          fvar :: ETm.appN (.const rr ls) (preMajor ++ idx ++ [fvar]) :: rest

/-- Every `directRec` field's `familyIdx` terms must be safely erasable —
otherwise the emitted rule would compute an index this table cannot
represent, and `IotaWitness`'s `hkinds` would have no erased image. -/
def iotaCtorSafe (nparams : Nat) : List (Expr Nat) → List RecKind → Nat → Bool
  | _, [], _ => true
  | [], _ :: _, _ => false
  | A :: ds, k :: ks, j =>
      (match k with
       | .plain => true
       | .directRec => (familyIdx nparams A).all (iotaIdxSafe (nparams + j) 0)) &&
        iotaCtorSafe nparams ds ks (j + 1)

/-- The `K`-λ wrapper around a spine body. -/
def lamN : Nat → ETm → ETm
  | 0, t => t
  | n + 1, t => .lam (lamN n t)

/-- One constructor's erased ι rule, when the group's own `analyzeFields`
admits it and every recursive call's index terms erase safely. `ctorIdx` is
the ctor's position in the group list — the minor sits at pre-major position
`nparams + 1 + ctorIdx` — and `ctorRef` is its environment ref. -/
def iotaRuleOfCtor (rr fam nparams nindices nMinors : Nat) (ctorIdx : Nat)
    (ctorRef : Nat) (cm : CheckedMember) : Option CRule :=
  let ctorSpine := piCount cm.mtype
  if ctorSpine < nparams then none else
  match peelPis ctorSpine cm.mtype with
  | none => none
  | some (doms, _) =>
      let fields := doms.drop nparams
      match analyzeFields fam fields with
      | none => none
      | some kinds =>
          let nargs := nparams + 1 + nMinors + nindices
          if iotaCtorSafe nparams fields kinds 0 then
            let K := nargs + ctorSpine
            some { head := rr
                   nargs := fun _ => nargs
                   major := some (ctorRef, fun _ => ctorSpine)
                   rhs := fun ls _ =>
                     lamN K (ETm.appN (.bvar (K - 1 - (nparams + 1 + ctorIdx)))
                       (iotaFieldArgs rr ls K nargs nparams nMinors fields kinds 0)) }
          else none

/-! ## §2 `iotaRulesOf`, `buildTableSyntaxI`, `tableOfI` -/

/-- The erased ι rules of ONE `.group` node — one per admitted constructor.
`nindices` is read off the recursor's stored type (its body's app spine is
`motive idx… major`, so `nindices = spine-1`); `nparams` is the family's
telescope minus the indices; `nMinors` is the group's own ctor count.
Malformed nodes (non-Π recursor type, empty major spine, family telescope
shorter than the indices) emit no rules rather than a wrong one. -/
def iotaRulesOf (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rr : Nat) (rm : CheckedMember) :
    List CRule :=
  match peelPis (piCount rm.mtype) rm.mtype with
  | none => []
  | some (_, recBody) =>
      match (appsSpine recBody).2.length with
      | 0 => []
      | nindices + 1 =>
          let fTel := piCount fm.mtype
          if fTel < nindices then [] else
          let nparams := fTel - nindices
          let nMinors := ctors.length
          (ctors.mapIdx fun i c =>
            iotaRuleOfCtor rr f nparams nindices nMinors i c.1 c.2).filterMap id

/-- `buildTableSyntax` with the ι half restored: same δ rules at the same
nodes, and each `.group` node additionally emits its `iotaRulesOf`. ι rules
are registered at the group's own stage (`GroupStageAt.here`); per-member
cursors are a later refinement — the group's recursor+ctor pair is what the
rule names. -/
noncomputable def buildTableSyntaxI :
    {E : ResolvedEnv} → (hEnv : EnvWfT E) → List (RuleEntry hEnv)
  | _, .empty => []
  | _, .axiom _ _ _ _ hE _ _ _ _ =>
      (buildTableSyntaxI hE).map fun e => ⟨e.rule, .underAxiom e.origin⟩
  | _, .definition _ r _ _ _ hE _ _ hv _ _ _ _ =>
      ⟨deltaRule r (defBodyAt hE hv), .defHere⟩ ::
        (buildTableSyntaxI hE).map fun e => ⟨e.rule, .underDefinition e.origin⟩
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ =>
      (buildTableSyntaxI hE).map fun e => ⟨e.rule, .underThm e.origin⟩
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ =>
      (buildTableSyntaxI hE).map fun e => ⟨e.rule, .underOpaque e.origin⟩
  | _, .group _ f fm ctors rr rm _ hE _ _ _ hmem =>
      (iotaRulesOf f fm ctors rr rm).map (fun ρ =>
          (⟨ρ, RuleOrigin.groupMember (.here hmem)⟩ : RuleEntry _)) ++
        (buildTableSyntaxI hE).map fun e => ⟨e.rule, .underGroup e.origin⟩

/-- The bare rule list: `tableOf`'s entries plus the ι rules of every group
node. -/
noncomputable def tableOfI {E : ResolvedEnv} (hEnv : EnvWfT E) : List CRule :=
  (buildTableSyntaxI hEnv).map (·.rule)

theorem tableOfI_empty : tableOfI .empty = [] := rfl

theorem tableOfI_axiom {E : ResolvedEnv} {r : Nat} {A : Expr Nat} {u : Level}
    {hE : EnvWfT E} {hfresh : E.members r = none} {hA : HasTyT E 0 [] A (.sort u)}
    {hcl : ∀ k, lift k 1 A = A} {hlvl : exprLevelsBounded 0 A = true} :
    tableOfI (.axiom E r A u hE hfresh hA hcl hlvl) = tableOfI hE := by
  simp [tableOfI, buildTableSyntaxI, List.map_map]

theorem tableOfI_definition {E : ResolvedEnv} {r : Nat} {A v : Expr Nat} {u : Level}
    {hE : EnvWfT E} {hfresh : E.members r = none} {hA : HasTyT E 0 [] A (.sort u)}
    {hv : HasTyT E 0 [] v A} {hclA : ∀ k, lift k 1 A = A} {hclv : ∀ k, lift k 1 v = v}
    {hlvlA : exprLevelsBounded 0 A = true} {hlvlv : exprLevelsBounded 0 v = true} :
    tableOfI (.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) =
      deltaRule r (defBodyAt hE hv) :: tableOfI hE := by
  simp [tableOfI, buildTableSyntaxI, List.map_map]

theorem tableOfI_thm {E : ResolvedEnv} {r : Nat} {A p : Expr Nat}
    {hE : EnvWfT E} {hfresh : E.members r = none} {hA : HasTyT E 0 [] A (.sort .zero)}
    {hp : HasTyT E 0 [] p A} {hclA : ∀ k, lift k 1 A = A} {hclp : ∀ k, lift k 1 p = p}
    {hlvlA : exprLevelsBounded 0 A = true} {hlvlp : exprLevelsBounded 0 p = true} :
    tableOfI (.thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp) = tableOfI hE := by
  simp [tableOfI, buildTableSyntaxI, List.map_map]

theorem tableOfI_opaque {E : ResolvedEnv} {r : Nat} {A v : Expr Nat} {u : Level}
    {hE : EnvWfT E} {hfresh : E.members r = none} {hA : HasTyT E 0 [] A (.sort u)}
    {hv : HasTyT E 0 [] v A} {hclA : ∀ k, lift k 1 A = A} {hclv : ∀ k, lift k 1 v = v}
    {hlvlA : exprLevelsBounded 0 A = true} {hlvlv : exprLevelsBounded 0 v = true} :
    tableOfI (.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) = tableOfI hE := by
  simp [tableOfI, buildTableSyntaxI, List.map_map]

/-- `·.rule` projects the ι entries back to the emitted rules. -/
theorem map_rule_iotaEntry {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {E' : ResolvedEnv} {hE : EnvWfT E} {hfam : fm.mclass = .inductiveM}
    {hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM} {hrec : rm.mclass = .recursorM}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    ∀ l : List CRule,
      ((l.map fun ρ => (⟨ρ, RuleOrigin.groupMember (.here hmem)⟩ :
          RuleEntry (.group E f fm ctors rr rm E' hE hfam hctors hrec hmem)))
        |>.map (·.rule)) = l := fun l => by
  induction l with
  | nil => rfl
  | cons a t ih => exact congrArg (a :: ·) ih

theorem tableOfI_group {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {E' : ResolvedEnv} {hE : EnvWfT E} {hfam : fm.mclass = .inductiveM}
    {hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM} {hrec : rm.mclass = .recursorM}
    {hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'} :
    tableOfI (.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) =
      iotaRulesOf f fm ctors rr rm ++ tableOfI hE := by
  simp only [tableOfI, buildTableSyntaxI]
  rw [List.map_append, map_rule_iotaEntry]
  congr 1
  induction buildTableSyntaxI hE with
  | nil => rfl
  | cons e t ih => exact congrArg (e.rule :: ·) ih

/-- `tableOf`'s rules are all still there — `tableOfI` only adds. -/
theorem mem_tableOfI_of_mem_tableOf {E : ResolvedEnv} (hEnv : EnvWfT E) {ρ : CRule}
    (h : ρ ∈ tableOf hEnv) : ρ ∈ tableOfI hEnv := by
  induction hEnv with
  | empty => cases h
  | «axiom» _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOfI_axiom]; exact ih (tableOf_axiom ▸ h)
  | definition _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOf_definition] at h
      rcases List.mem_cons.mp h with rfl | h
      · rw [tableOfI_definition]; exact List.Mem.head _
      · rw [tableOfI_definition]; exact List.Mem.tail _ (ih h)
  | thm _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOfI_thm]; exact ih (tableOf_thm ▸ h)
  | «opaque» _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOfI_opaque]; exact ih (tableOf_opaque ▸ h)
  | group _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOf_group] at h
      rw [tableOfI_group]; exact List.mem_append_right _ (ih h)

/-! ## §3 the Nat positive control -/

/-- The `zero` ι rule `tableOfI` emits for `natEnvUWfT`:
`rec P mz ms zero → mz`. -/
def natZeroRule : CRule where
  head := 3
  nargs := fun _ => 3
  major := some (1, fun _ => 0)
  rhs := fun _ _ => .lam (.lam (.lam (.bvar 1)))

/-- The group emits exactly its two constructor rules, and the succ rule is
kernel-identical to the landed singleton `natSuccRule`. -/
theorem iotaRulesOf_nat :
    iotaRulesOf 0 natFamMember [(1, natZeroMember), (2, natSuccMember)]
        3 natRecMemberU = [natZeroRule, natSuccRule] :=
  rfl

/-- PART-1 positive control: every rule of the landed `natSuccTable` —
`natSuccRule` itself — is in `tableOfI natEnvUWfT`. -/
theorem natSucc_tableOfI_positive_control :
    ∀ ρ ∈ natSuccTable, ρ ∈ tableOfI natEnvUWfT := by
  intro ρ hρ
  simp only [natSuccTable, List.mem_singleton] at hρ; subst hρ
  have hg : tableOfI natEnvUWfT =
      iotaRulesOf 0 natFamMember [(1, natZeroMember), (2, natSuccMember)]
        3 natRecMemberU ++ tableOfI .empty := tableOfI_group
  rw [hg, tableOfI_empty, iotaRulesOf_nat]
  exact List.mem_append_left _ (List.Mem.tail _ (List.Mem.head _))

#print axioms eraseTelK
#print axioms iotaIdxSafe
#print axioms iotaFieldArgs
#print axioms iotaCtorSafe
#print axioms iotaRuleOfCtor
#print axioms iotaRulesOf
#print axioms buildTableSyntaxI
#print axioms tableOfI
#print axioms tableOfI_group
#print axioms mem_tableOfI_of_mem_tableOf
#print axioms iotaRulesOf_nat
#print axioms natSucc_tableOfI_positive_control

end Rcic.Syn
