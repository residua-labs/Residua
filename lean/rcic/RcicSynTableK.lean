import rcic.RcicSynTableCongrI
import rcic.RcicSynTableIotaWF
import rcic.RcicSynCR
import rcic.RcicSynCommute

/-!
# `tableOfK` — erased K rules for singleton-`Prop` large-eliminating recursors

`tableOfI` emits one constructor-major ι rule per admitted constructor. For a
singleton-`Prop` large-eliminating group (`Eq`, `Loop`), the erased major is
always `★` — the proof argument is dropped by `TyP.eps`'s app clause — so the
ctor-major rule never matches the erased redex `rec (params·M·m·idx)` whose
spine simply has no major slot. This module is the additive K-table: for a
gated group it emits the bare rule

    `const rr ls  ~>  λ^{nparams+2+nindices}. m (rc₁ … rc_f)`,

i.e. schematically `rec M m ★ ~> m` (plus the erased recursive calls one per
`directRec` field — all fields of a gated group are proofs, hence erased).

Replacement, not augmentation. Emitting the K rule *alongside* the ctor rules
of the same group would (a) violate `TableWF.bare_unique`/`ctor_disjoint`
invariants and (b) create a genuine non-joinable critical pair: on
`appN (const rr ls) (args ++ [ctorSpine])` the ctor rule rewrites to `m`, the
K rule (fired at the bare `const rr ls` subterm) rewrites to `m ctorSpine`.
`iotaRulesKOf` therefore emits `[K]` *instead of* `iotaRulesOf`'s output when
`iotaKGate` holds; the pair and its non-joinability are exhibited in §7.
On the erased image of `eps` the two never actually compete — the erased
ctor-major redex and the erased variable-major redex are the same term
(the major always drops for a `Prop` family).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the gate and the emitted rule -/

/-- The group's param count, as `iotaRulesOf` computes it: the family
    telescope minus the index count read off the recursor's body spine. -/
def iotaKNparams (fm rm : CheckedMember) : Nat := piCount fm.mtype - iotaNindices rm

/-- The kept arity of the erased K redex: `nparams + motive + minor + indices`
    (the ctor count is one by the singleton gate, and the major always erases
    for a `Prop` family). -/
def iotaKNargs (fm rm : CheckedMember) : Nat :=
  iotaKNparams fm rm + 2 + iotaNindices rm

/-- The singleton ctor's field count: its Π-spine minus the params. -/
def iotaKNfields (fm cm rm : CheckedMember) : Nat :=
  piCount cm.mtype - iotaKNparams fm rm

/-- The emitted K rule: head `rr`, bare and nullary; the right side is the
    `nargs`-λ `m (rc₁ … rc_f)` — the unique minor sits at erased spine
    position `nparams + 1`, i.e. `bvar nindices` under the λ-tower, and each
    recursive call keeps exactly the pre-major prefix `params·M·m` (the
    field, a proof, drops — this is correct only because the K gate forces
    `nindices = 0` whenever fields exist, so no index arguments are owed). -/
def iotaKRule (rr nargs nparams nindices nfields : Nat) : CRule where
  head := rr
  nargs := fun _ => 0
  major := none
  rhs := fun ls _ =>
    lamN nargs
      (.appN (.bvar nindices)
        ((List.range nfields).map fun _ =>
          .appN (.const rr ls)
            ((List.range (nparams + 2)).map fun p => .bvar (nargs - 1 - p))))

/-- The K gate: a singleton-`Prop` large-eliminating group with only
    proof-erased fields.
    (a) the family's telescope ends in literal `Sort 0` — every member of the
        family (the major, every ctor field of family type) is a proof and
        erases to `★`;
    (b) the recursor's body spine is `motive idx… major` with at least the
        major argument, and it carries exactly one extra level variable over
        the family — the `AnySort`/`Sort u` large-elimination slot;
    (c) the group's ctor list is a singleton (checked by `iotaKRuleOf`'s
        match, not here);
    (d) every ctor field is a `directRec` family application (`isFamilyApp`)
        with no index arguments — a proof, erased — and if fields exist at
        all the family has no indices: an erased recursive call cannot
        reconstruct index terms. -/
def iotaKGate (f : Nat) (fm cm rm : CheckedMember) : Bool :=
  match peelPis (piCount fm.mtype) fm.mtype with
  | some (_, .sort .zero) =>
      match peelPis (piCount rm.mtype) rm.mtype with
      | some (_, recBody) =>
          match (appsSpine recBody).2.length with
          | 0 => false
          | nindices + 1 =>
              let fTel := piCount fm.mtype
              if fTel < nindices then false else
              let nparams := fTel - nindices
              match peelPis (piCount cm.mtype) cm.mtype with
              | none => false
              | some (domsC, _) =>
                  if piCount cm.mtype < nparams then false else
                  let fields := domsC.drop nparams
                  decide (rm.arity = fm.arity + 1) &&
                    (decide (nindices = 0) || fields.isEmpty) &&
                    fields.all (fun A =>
                      isFamilyApp f A && (familyIdx nparams A).isEmpty)
      | none => false
  | _ => false

/-- Emit the single K rule iff the group is a singleton `iotaKGate` pass. -/
def iotaKRuleOf (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rr : Nat) (rm : CheckedMember) :
    Option CRule :=
  match ctors with
  | [(_, cm)] =>
      if iotaKGate f fm cm rm then
        some (iotaKRule rr (iotaKNargs fm rm) (iotaKNparams fm rm)
          (iotaNindices rm) (iotaKNfields fm cm rm))
      else none
  | _ => none

/-- A `.group` node's erased rules in the K-table: when `iotaKRuleOf` emits,
    the bare K rule REPLACES the ctor-major rules (coexistence at the same
    head is the §7 non-joinable critical pair); otherwise the node's
    `iotaRulesOf` emission stands. -/
def iotaRulesKOf (f : Nat) (fm : CheckedMember)
    (ctors : List (Nat × CheckedMember)) (rr : Nat) (rm : CheckedMember) :
    List CRule :=
  match iotaKRuleOf f fm ctors rr rm with
  | some ρ => [ρ]
  | none => iotaRulesOf f fm ctors rr rm

/-- What `iotaKRuleOf` emits when it emits: the singleton ctor `cr`, the gate
    `true`, and the literal `iotaKRule` at the group's own counts. -/
theorem iotaKRuleOf_spec {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (h : iotaKRuleOf f fm ctors rr rm = some ρ) :
    ∃ (cr : Nat) (cm : CheckedMember), ctors = [(cr, cm)] ∧
      iotaKGate f fm cm rm = true ∧
      ρ = iotaKRule rr (iotaKNargs fm rm) (iotaKNparams fm rm)
        (iotaNindices rm) (iotaKNfields fm cm rm) := by
  unfold iotaKRuleOf at h
  split at h
  · rename_i cr cm
    split at h
    · rename_i hg
      injection h with hρ
      exact ⟨cr, cm, rfl, hg, hρ.symm⟩
    · exact Option.noConfusion h
  · exact Option.noConfusion h

/-- Membership in `iotaRulesKOf`'s output is either the emitted K rule or a
    fallthrough `iotaRulesOf` member. -/
theorem mem_iotaRulesKOf {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (h : ρ ∈ iotaRulesKOf f fm ctors rr rm) :
    (iotaKRuleOf f fm ctors rr rm = some ρ) ∨
      ρ ∈ iotaRulesOf f fm ctors rr rm := by
  unfold iotaRulesKOf at h
  split at h
  · rename_i ρ' hρ'
    rcases List.mem_singleton.mp h with rfl
    exact .inl hρ'
  · exact .inr h

/-- Every `iotaRulesKOf` member is headed at the group's own `rr`. -/
theorem iotaRulesKOf_head {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (h : ρ ∈ iotaRulesKOf f fm ctors rr rm) : ρ.head = rr := by
  rcases mem_iotaRulesKOf h with hK | hI
  · obtain ⟨_, _, _, _, rfl⟩ := iotaKRuleOf_spec hK
    rfl
  · obtain ⟨i, hi, hemi⟩ := mem_iotaRulesOf hI
    exact (iotaRuleOfCtor_spec hemi).1

/-- A bare member of `iotaRulesKOf` is the K rule itself: ctor-major
    emissions always carry `major = some`. -/
theorem bare_mem_iotaRulesKOf {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (h : ρ ∈ iotaRulesKOf f fm ctors rr rm)
    (hm : ρ.major = none) : iotaKRuleOf f fm ctors rr rm = some ρ := by
  rcases mem_iotaRulesKOf h with hK | hI
  · exact hK
  · obtain ⟨i, hi, hemi⟩ := mem_iotaRulesOf hI
    obtain ⟨-, -, k, hmaj⟩ := iotaRuleOfCtor_spec hemi
    exact Option.noConfusion (hmaj.symm.trans hm)

/-- A ctor-major member of `iotaRulesKOf` comes from the `iotaRulesOf`
    fallthrough — the K rule carries `major = none`. -/
theorem ctorMajor_mem_iotaRulesKOf {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (h : ρ ∈ iotaRulesKOf f fm ctors rr rm) {d : Nat}
    {m : List Level → Nat} (hm : ρ.major = some (d, m)) :
    ρ ∈ iotaRulesOf f fm ctors rr rm := by
  rcases mem_iotaRulesKOf h with hK | hI
  · obtain ⟨cr, cm, _, _, hρ⟩ := iotaKRuleOf_spec hK
    subst hρ
    exact Option.noConfusion hm
  · exact hI

/-- When the gate fires, `iotaRulesKOf` is the singleton K list — used to
    discharge the same-node `bare_unique` case. -/
theorem iotaRulesKOf_eq_of_bare {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (h : ρ ∈ iotaRulesKOf f fm ctors rr rm)
    (hm : ρ.major = none) :
    iotaRulesKOf f fm ctors rr rm = [ρ] := by
  have hK := bare_mem_iotaRulesKOf h hm
  unfold iotaRulesKOf
  rw [hK]

/-! ## §2 `tableOfK` -/

/-- The K-table: `tableOf`'s δ rules verbatim, and at each `.group` node the
    `iotaRulesKOf` emission in place of `iotaRulesOf`. -/
noncomputable def tableOfK : {E : ResolvedEnv} → EnvWfT E → List CRule
  | _, .empty => []
  | _, .axiom _ _ _ _ hE _ _ _ _ => tableOfK hE
  | _, .definition _ r _ _ _ hE _ _ hv _ _ _ _ =>
      deltaRule r (defBodyAt hE hv) :: tableOfK hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => tableOfK hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => tableOfK hE
  | _, .group _ f fm ctors rr rm _ hE _ _ _ _ =>
      iotaRulesKOf f fm ctors rr rm ++ tableOfK hE

theorem tableOfK_empty : tableOfK .empty = [] := rfl

theorem tableOfK_axiom {arity : Nat} {E : ResolvedEnv} {r : Nat} {A : Expr Nat} {u : Level}
    {hE : EnvWfT E} {hfresh : E.members r = none} {hA : HasTyT E arity [] A (.sort u)}
    {hcl : ∀ k, lift k 1 A = A} {hlvl : exprLevelsBounded arity A = true} :
    tableOfK (.axiom E r A u hE hfresh hA hcl hlvl) = tableOfK hE := rfl

theorem tableOfK_definition {E : ResolvedEnv} {r : Nat} {A v : Expr Nat}
    {u : Level} {hE : EnvWfT E} {hfresh : E.members r = none}
    {hA : HasTyT E 0 [] A (.sort u)} {hv : HasTyT E 0 [] v A}
    {hclA : ∀ k, lift k 1 A = A} {hclv : ∀ k, lift k 1 v = v}
    {hlvlA : exprLevelsBounded 0 A = true} {hlvlv : exprLevelsBounded 0 v = true} :
    tableOfK (.definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) =
      deltaRule r (defBodyAt hE hv) :: tableOfK hE := rfl

theorem tableOfK_thm {E : ResolvedEnv} {r : Nat} {A p : Expr Nat}
    {hE : EnvWfT E} {hfresh : E.members r = none}
    {hA : HasTyT E 0 [] A (.sort .zero)} {hp : HasTyT E 0 [] p A}
    {hclA : ∀ k, lift k 1 A = A} {hclp : ∀ k, lift k 1 p = p}
    {hlvlA : exprLevelsBounded 0 A = true} {hlvlp : exprLevelsBounded 0 p = true} :
    tableOfK (.thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp) =
      tableOfK hE := rfl

theorem tableOfK_opaque {E : ResolvedEnv} {r : Nat} {A v : Expr Nat}
    {u : Level} {hE : EnvWfT E} {hfresh : E.members r = none}
    {hA : HasTyT E 0 [] A (.sort u)} {hv : HasTyT E 0 [] v A}
    {hclA : ∀ k, lift k 1 A = A} {hclv : ∀ k, lift k 1 v = v}
    {hlvlA : exprLevelsBounded 0 A = true} {hlvlv : exprLevelsBounded 0 v = true} :
    tableOfK (.opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv) =
      tableOfK hE := rfl

theorem tableOfK_group {E : ResolvedEnv} {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {E' : ResolvedEnv} {hE : EnvWfT E} {hfam : fm.mclass = .inductiveM}
    {hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM} {hrec : rm.mclass = .recursorM}
    {hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E'} :
    tableOfK (.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) =
      iotaRulesKOf f fm ctors rr rm ++ tableOfK hE := rfl

/-- `tableOfK` keeps every δ rule of `tableOf`. -/
theorem mem_tableOfK_of_mem_tableOf {E : ResolvedEnv} (hEnv : EnvWfT E)
    {ρ : CRule} (h : ρ ∈ tableOf hEnv) : ρ ∈ tableOfK hEnv := by
  induction hEnv with
  | empty => cases h
  | «axiom» _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOfK_axiom]; exact ih (tableOf_axiom ▸ h)
  | thm _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOfK_thm]; exact ih (tableOf_thm ▸ h)
  | «opaque» _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOfK_opaque]; exact ih (tableOf_opaque ▸ h)
  | definition _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOf_definition] at h
      rcases List.mem_cons.mp h with rfl | h
      · rw [tableOfK_definition]; exact List.Mem.head _
      · rw [tableOfK_definition]; exact List.Mem.tail _ (ih h)
  | group _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      rw [tableOf_group] at h
      rw [tableOfK_group]; exact List.mem_append_right _ (ih h)

/-! ## §3 head/major classification -/

/-- Every `tableOfK` rule is either a `tableOf` δ rule or a group emission at
    its own `rr`: the bare K rule (`major = none`) or an `iotaRulesOf` ctor
    rule (`major` the ctor ref, which resolves `.constructorM`). -/
theorem tableOfK_head_major {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfK hEnv,
      (∃ m, E.members ρ.head = some m ∧ m.mclass = .definitionM ∧
        ρ ∈ tableOf hEnv) ∨
      (∃ m, E.members ρ.head = some m ∧ m.mclass = .recursorM ∧
        (ρ.major = none ∨
         ∃ (d : Nat) (k : List Level → Nat) (md : CheckedMember),
           ρ.major = some (d, k) ∧ E.members d = some md ∧
             md.mclass = .constructorM)) := by
  induction hEnv with
  | empty => intro ρ hρ; cases hρ
  | «axiom» _ _ _ _ hE hfresh _ _ _ ih =>
      intro ρ hρ; rw [tableOfK_axiom] at hρ
      rcases ih ρ hρ with ⟨m, hm, hmc, htb⟩ | ⟨m, hm, hmc, hmaj⟩
      · refine .inl ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, ?_⟩
        rw [tableOf_axiom]; exact htb
      · exact .inr ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc,
          hmaj.imp_right fun ⟨d, k, md, h1, h2, h3⟩ =>
            ⟨d, k, md, h1, envExt_extendEnv _ hfresh _ _ h2, h3⟩⟩
  | thm _ _ _ _ hE hfresh _ _ _ _ _ _ ih =>
      intro ρ hρ; rw [tableOfK_thm] at hρ
      rcases ih ρ hρ with ⟨m, hm, hmc, htb⟩ | ⟨m, hm, hmc, hmaj⟩
      · refine .inl ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, ?_⟩
        rw [tableOf_thm]; exact htb
      · exact .inr ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc,
          hmaj.imp_right fun ⟨d, k, md, h1, h2, h3⟩ =>
            ⟨d, k, md, h1, envExt_extendEnv _ hfresh _ _ h2, h3⟩⟩
  | «opaque» _ _ _ _ _ hE hfresh _ _ _ _ _ _ ih =>
      intro ρ hρ; rw [tableOfK_opaque] at hρ
      rcases ih ρ hρ with ⟨m, hm, hmc, htb⟩ | ⟨m, hm, hmc, hmaj⟩
      · refine .inl ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, ?_⟩
        rw [tableOf_opaque]; exact htb
      · exact .inr ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc,
          hmaj.imp_right fun ⟨d, k, md, h1, h2, h3⟩ =>
            ⟨d, k, md, h1, envExt_extendEnv _ hfresh _ _ h2, h3⟩⟩
  | definition _ r A v _ hE hfresh _ _ _ _ _ _ ih =>
      intro ρ hρ; rw [tableOfK_definition] at hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · refine .inl ⟨⟨.definitionM, 0, A, some v⟩, members_extend_self _ _ _, rfl, ?_⟩
        rw [tableOf_definition]; exact List.Mem.head _
      · rcases ih ρ hρ' with ⟨m, hm, hmc, htb⟩ | ⟨m, hm, hmc, hmaj⟩
        · refine .inl ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, ?_⟩
          rw [tableOf_definition]; exact List.Mem.tail _ htb
        · exact .inr ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc,
            hmaj.imp_right fun ⟨d, k, md, h1, h2, h3⟩ =>
              ⟨d, k, md, h1, envExt_extendEnv _ hfresh _ _ h2, h3⟩⟩
  | group E f fm ctors rr rm E' hE hfam hctors hrec hmem ih =>
      intro ρ hρ; rw [tableOfK_group] at hρ
      rcases List.mem_append.mp hρ with hι | hδ
      · rcases mem_iotaRulesKOf hι with hK | hI
        · obtain ⟨cr, cm, _, _, rfl⟩ := iotaKRuleOf_spec hK
          exact .inr ⟨rm,
            groupMembersT_lookup hmem (List.mem_cons_of_mem _
              (List.mem_append_right _ (List.mem_singleton_self _))),
            hrec, .inl rfl⟩
        · obtain ⟨i, hi, hemi⟩ := mem_iotaRulesOf hI
          obtain ⟨hhead, -, k, hmaj⟩ := iotaRuleOfCtor_spec hemi
          refine .inr ⟨rm, ?_, hrec, .inr
            ⟨ctors[i].1, k, ctors[i].2, hmaj, ?_, hctors _ (List.getElem_mem hi)⟩⟩
          · rw [hhead]
            exact groupMembersT_lookup hmem (List.mem_cons_of_mem _
              (List.mem_append_right _ (List.mem_singleton_self _)))
          · exact groupMembersT_lookup hmem (List.mem_cons_of_mem _
              (List.mem_append_left _ (List.getElem_mem hi)))
      · rcases ih ρ hδ with ⟨m, hm, hmc, htb⟩ | ⟨m, hm, hmc, hmaj⟩
        · refine .inl ⟨m, groupMembersT_ext hmem _ _ hm, hmc, ?_⟩
          rw [tableOf_group]; exact htb
        · exact .inr ⟨m, groupMembersT_ext hmem _ _ hm, hmc,
            hmaj.imp_right fun ⟨d, k, md, h1, h2, h3⟩ =>
              ⟨d, k, md, h1, groupMembersT_ext hmem _ _ h2, h3⟩⟩

/-- Every `tableOfK` rule's head resolves in the node's env. -/
theorem head_mem_tableOfK {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfK hEnv, ∃ m, E.members ρ.head = some m := by
  intro ρ hρ
  rcases tableOfK_head_major hEnv ρ hρ with ⟨m, hm, -, -⟩ | ⟨m, hm, -, -⟩ <;>
    exact ⟨m, hm⟩

/-! ## §4 `RuleCongrData` for the K rule, hence `congr`/`closed` -/

/-- `RuleCongrData` for `iotaKRule`: the rhs `λ^{nargs}. bvar nindices
    (rc-calls)` is congruent — only the rec-call `const rr ls` carries `ls`,
    handled by `LvlEq.const` — and closed at `0`: the minor's `bvar nindices`
    and each rec-call `bvar (nargs-1-p)` stay under the λ-tower. The guard
    hypotheses are exactly the gate's arities (`nargs = nparams+2+nindices`). -/
theorem iotaKRule_data {rr nargs nparams nindices nfields : Nat}
    (hnargs : nargs = nparams + 2 + nindices) :
    RuleCongrData (iotaKRule rr nargs nparams nindices nfields) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ls₁ ls₂ ms₁ ms₂ hls _
    apply lvlEq_lamN
    refine lvlEq_appN (.bvar _) (lvlEqList_map fun p _ =>
      lvlEq_appN (.const _ hls) (lvlEqList_refl _))
  · intro _ _ _; rfl
  · intro _ _ hm _ _ _; cases hm
  · intro ls ms
    subst hnargs
    apply closedAt_lamN
    apply closedAt_appN
    · show nindices < nparams + 2 + nindices; omega
    · intro x hx
      rcases List.mem_map.mp hx with ⟨p, _, rfl⟩
      apply closedAt_appN
      · trivial
      · intro y hy
        rcases List.mem_map.mp hy with ⟨q, hq, rfl⟩
        show nparams + 2 + nindices - 1 - q < nparams + 2 + nindices
        rcases List.mem_range.mp hq with hq
        omega

/-- Every member of `iotaRulesKOf` carries `RuleCongrData`. -/
theorem iotaRulesKOf_data {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (h : ρ ∈ iotaRulesKOf f fm ctors rr rm) : RuleCongrData ρ := by
  rcases mem_iotaRulesKOf h with hK | hI
  · obtain ⟨cr, cm, _, _, rfl⟩ := iotaKRuleOf_spec hK
    exact iotaKRule_data rfl
  · exact iotaRulesOf_data hI

/-- Per-rule `RuleCongrData` for every rule of `tableOfK hEnv`. -/
theorem ruleData_tableOfK {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfK hEnv, RuleCongrData ρ := by
  induction hEnv with
  | empty =>
      intro ρ hρ
      rw [tableOfK_empty] at hρ
      exact absurd hρ (List.not_mem_nil _)
  | «axiom» _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfK_axiom] at hρ
      exact ih ρ hρ
  | definition _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfK_definition] at hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · exact deltaRule_data _ (closedWf_enrichHasTyT _ _ _ _ _ _)
      · exact ih ρ hρ'
  | thm _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfK_thm] at hρ
      exact ih ρ hρ
  | «opaque» _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfK_opaque] at hρ
      exact ih ρ hρ
  | group _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ
      rw [tableOfK_group] at hρ
      rcases List.mem_append.mp hρ with hL | hR
      · exact iotaRulesKOf_data hL
      · exact ih ρ hR

/-- The `congr` field of `TableWF (tableOfK hEnv)`. -/
theorem tableCongr_tableOfK {E : ResolvedEnv} (hEnv : EnvWfT E) :
    TableCongr (tableOfK hEnv) :=
  tableCongr_of_ruleData (ruleData_tableOfK hEnv)

/-- The `closed` field of `TableWF (tableOfK hEnv)`. -/
theorem tableClosed_tableOfK {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfK hEnv, ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms) :=
  tableClosed_of_ruleData (ruleData_tableOfK hEnv)

/-! ## §5 the four structural `TableWF` fields on `tableOfK hEnv` -/

/-- `TableWF.rigid`: a ctor-major rule's major ref resolves `.constructorM`,
    while every table head resolves `.definitionM`/`.recursorM` — class
    disjoint. K rules are bare, so they never enter this obligation. -/
theorem tableOfK_rigid {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfK hEnv, ∀ {d : Nat} {m : List Level → Nat},
      ρ.major = some (d, m) → ∀ σ ∈ tableOfK hEnv, σ.head ≠ d := by
  intro ρ hρ d m hm σ hσ hhead
  rcases tableOfK_head_major hEnv ρ hρ with ⟨_, _, _, htb⟩ |
      ⟨_, _, _, hmaj⟩
  · exact Option.noConfusion (hm.symm.trans (major_none_tableOf hEnv ρ htb))
  · rcases hmaj with hn | ⟨d', k, md, hmaj', hd, hmc'⟩
    · exact Option.noConfusion (hm.symm.trans hn)
    · have hd' : d = d' :=
        congrArg Prod.fst (Option.some.inj (hm.symm.trans hmaj'))
      subst hd'
      rcases tableOfK_head_major hEnv σ hσ with ⟨ms, hs, hcs, -⟩ |
          ⟨ms, hs, hcs, -⟩ <;>
        exact members_ne_of_mclass_ne hs hd
          (fun h => MemberClass.noConfusion (hcs.symm.trans (h.trans hmc')))
          hhead

/-- `ctor_disjoint` within ONE `iotaRulesKOf` call: a ctor-major member comes
    from the `iotaRulesOf` fallthrough, where the landed same-head argument
    applies. -/
theorem iotaRulesKOf_ctor_disjoint {S E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)} {rr : Nat}
    {rm : CheckedMember} {E' : ResolvedEnv}
    (hmem : GroupMembersT S E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    ∀ ρ ∈ iotaRulesKOf f fm ctors rr rm,
      ∀ σ ∈ iotaRulesKOf f fm ctors rr rm, ρ.head = σ.head →
      ∀ {d e : Nat} {m n : List Level → Nat},
        ρ.major = some (d, m) → σ.major = some (e, n) →
        ρ.nargs = σ.nargs ∧ (d = e → σ = ρ) := by
  intro ρ hρ σ hσ hh d e m n hm hn
  exact iotaRulesOf_ctor_disjoint hmem ρ
    (ctorMajor_mem_iotaRulesKOf hρ hm) σ
    (ctorMajor_mem_iotaRulesKOf hσ hn) hh hm hn

/-- `ctor_disjoint` on `tableOfK hEnv`. -/
theorem tableOfK_ctor_disjoint {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfK hEnv, ∀ σ ∈ tableOfK hEnv, ρ.head = σ.head →
      ∀ {d e : Nat} {m n : List Level → Nat},
        ρ.major = some (d, m) → σ.major = some (e, n) →
        ρ.nargs = σ.nargs ∧ (d = e → σ = ρ) := by
  induction hEnv with
  | empty => intro ρ hρ; cases hρ
  | «axiom» _ _ _ _ hE _ _ _ _ ih =>
      intro ρ hρ σ hσ; rw [tableOfK_axiom] at hρ hσ
      exact ih ρ hρ σ hσ
  | thm _ _ _ _ hE _ _ _ _ _ _ _ ih =>
      intro ρ hρ σ hσ; rw [tableOfK_thm] at hρ hσ
      exact ih ρ hρ σ hσ
  | «opaque» _ _ _ _ _ hE _ _ _ _ _ _ _ ih =>
      intro ρ hρ σ hσ; rw [tableOfK_opaque] at hρ hσ
      exact ih ρ hρ σ hσ
  | definition _ r _ _ _ hE hfresh _ hv _ _ _ _ ih =>
      intro ρ hρ σ hσ hh d e m n hm hn
      rw [tableOfK_definition] at hρ hσ
      rcases List.mem_cons.mp hρ with hρh | hρt <;>
        rcases List.mem_cons.mp hσ with hσh | hσt
      · subst hρh; subst hσh
        exact ⟨rfl, fun _ => rfl⟩
      · subst hρh
        obtain ⟨ms, hs⟩ := head_mem_tableOfK hE σ hσt
        rw [show (deltaRule r (defBodyAt hE hv)).head = r from rfl] at hh
        rw [hh] at hfresh
        exact Option.noConfusion (hfresh.symm.trans hs)
      · subst hσh
        obtain ⟨mr, hr⟩ := head_mem_tableOfK hE ρ hρt
        rw [show (deltaRule r (defBodyAt hE hv)).head = r from rfl] at hh
        rw [← hh] at hfresh
        exact Option.noConfusion (hfresh.symm.trans hr)
      · exact ih ρ hρt σ hσt hh hm hn
  | group E f fm ctors rr rm E' hE hfam hctors hrec hmem ih =>
      intro ρ hρ σ hσ hh d e m n hm hn
      rw [tableOfK_group] at hρ hσ
      rcases List.mem_append.mp hρ with hρι | hρt <;>
        rcases List.mem_append.mp hσ with hσι | hσt
      · exact iotaRulesKOf_ctor_disjoint hmem ρ hρι σ hσι hh hm hn
      · have hhead := iotaRulesKOf_head hρι
        obtain ⟨ms, hs⟩ := head_mem_tableOfK hE σ hσt
        have hrr : E.members rr = none := groupMembersT_freshE hmem
          (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_singleton_self _)))
        rw [← hhead] at hrr
        rw [hh] at hrr
        exact Option.noConfusion (hs.symm.trans hrr)
      · have hhead := iotaRulesKOf_head hσι
        obtain ⟨mr, hr⟩ := head_mem_tableOfK hE ρ hρt
        have hrr : E.members rr = none := groupMembersT_freshE hmem
          (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_singleton_self _)))
        rw [← hhead, ← hh] at hrr
        exact Option.noConfusion (hr.symm.trans hrr)
      · exact ih ρ hρt σ hσt hh hm hn

/-- `bare_unique` on `tableOfK hEnv`: a bare rule is a `tableOf` δ rule or a
    gated group's K rule; same-head peers are class-separated or identical. -/
theorem tableOfK_bare_unique {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfK hEnv, ρ.major = none →
      ∀ σ ∈ tableOfK hEnv, σ.head = ρ.head → σ = ρ := by
  induction hEnv with
  | empty => intro ρ hρ; cases hρ
  | «axiom» _ _ _ _ hE _ _ _ _ ih =>
      intro ρ hρ hm σ hσ; rw [tableOfK_axiom] at hρ hσ
      exact ih ρ hρ hm σ hσ
  | thm _ _ _ _ hE _ _ _ _ _ _ _ ih =>
      intro ρ hρ hm σ hσ; rw [tableOfK_thm] at hρ hσ
      exact ih ρ hρ hm σ hσ
  | «opaque» _ _ _ _ _ hE _ _ _ _ _ _ _ ih =>
      intro ρ hρ hm σ hσ; rw [tableOfK_opaque] at hρ hσ
      exact ih ρ hρ hm σ hσ
  | definition _ r _ _ _ hE hfresh _ hv _ _ _ _ ih =>
      intro ρ hρ hm σ hσ hh
      rw [tableOfK_definition] at hρ hσ
      rcases List.mem_cons.mp hρ with hρh | hρt <;>
        rcases List.mem_cons.mp hσ with hσh | hσt
      · subst hρh; subst hσh; rfl
      · subst hρh
        obtain ⟨ms, hs⟩ := head_mem_tableOfK hE σ hσt
        rw [show (deltaRule r (defBodyAt hE hv)).head = r from rfl] at hh
        rw [← hh] at hfresh
        exact Option.noConfusion (hfresh.symm.trans hs)
      · subst hσh
        obtain ⟨mr, hr⟩ := head_mem_tableOfK hE ρ hρt
        rw [show (deltaRule r (defBodyAt hE hv)).head = r from rfl] at hh
        rw [hh] at hfresh
        exact Option.noConfusion (hfresh.symm.trans hr)
      · exact ih ρ hρt hm σ hσt hh
  | group E f fm ctors rr rm E' hE hfam hctors hrec hmem ih =>
      intro ρ hρ hm σ hσ hh
      rw [tableOfK_group] at hρ hσ
      rcases List.mem_append.mp hρ with hρι | hρt <;>
        rcases List.mem_append.mp hσ with hσι | hσt
      · rw [iotaRulesKOf_eq_of_bare hρι hm] at hσι
        rcases List.mem_singleton.mp hσι with rfl
        rfl
      · have hhead := iotaRulesKOf_head hρι
        obtain ⟨ms, hs⟩ := head_mem_tableOfK hE σ hσt
        have hrr : E.members rr = none := groupMembersT_freshE hmem
          (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_singleton_self _)))
        rw [← hhead, ← hh] at hrr
        exact Option.noConfusion (hs.symm.trans hrr)
      · have hhead := iotaRulesKOf_head hσι
        obtain ⟨mr, hr⟩ := head_mem_tableOfK hE ρ hρt
        have hrr : E.members rr = none := groupMembersT_freshE hmem
          (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_singleton_self _)))
        rw [← hhead, hh] at hrr
        exact Option.noConfusion (hr.symm.trans hrr)
      · exact ih ρ hρt hm σ hσt hh

/-- `bare_nullary` on `tableOfK hEnv`: bare rules are δ rules or the K rule —
    both `nargs = 0`. -/
theorem tableOfK_bare_nullary {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfK hEnv, ρ.major = none → ∀ ls, ρ.nargs ls = 0 := by
  induction hEnv with
  | empty => intro ρ hρ; cases hρ
  | «axiom» _ _ _ _ hE _ _ _ _ ih =>
      intro ρ hρ; rw [tableOfK_axiom] at hρ
      exact ih ρ hρ
  | thm _ _ _ _ hE _ _ _ _ _ _ _ ih =>
      intro ρ hρ; rw [tableOfK_thm] at hρ
      exact ih ρ hρ
  | «opaque» _ _ _ _ _ hE _ _ _ _ _ _ _ ih =>
      intro ρ hρ; rw [tableOfK_opaque] at hρ
      exact ih ρ hρ
  | definition _ r _ _ _ hE hfresh _ _ _ _ _ _ ih =>
      intro ρ hρ hm ls
      rw [tableOfK_definition] at hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · rfl
      · exact ih ρ hρ' hm ls
  | group E f fm ctors rr rm E' hE hfam hctors hrec hmem ih =>
      intro ρ hρ hm ls
      rw [tableOfK_group] at hρ
      rcases List.mem_append.mp hρ with hρι | hρt
      · obtain ⟨cr, cm, _, _, rfl⟩ := iotaKRuleOf_spec (bare_mem_iotaRulesKOf hρι hm)
        rfl
      · exact ih ρ hρt hm ls

/-! ## §6 assembly: `TableWF` and confluence -/

/-- `TableWF (tableOfK hEnv)` — all six fields from `hEnv` alone. -/
theorem tableWF_tableOfK {E : ResolvedEnv} (hEnv : EnvWfT E) :
    TableWF (tableOfK hEnv) where
  congr := tableCongr_tableOfK hEnv
  closed := tableClosed_tableOfK hEnv
  rigid := tableOfK_rigid hEnv
  ctor_disjoint := tableOfK_ctor_disjoint hEnv
  bare_unique := tableOfK_bare_unique hEnv
  bare_nullary := tableOfK_bare_nullary hEnv

/-- The erased calculus stays confluent on the K-table — the landed
    `confluent_eStep_wf` architecture applies verbatim. -/
theorem confluent_eStep_tableOfK {E : ResolvedEnv} (hEnv : EnvWfT E) :
    Confluent (EStep (tableOfK hEnv)) :=
  confluent_eStep_wf (tableWF_tableOfK hEnv)

/-! ## §7 the K-vs-ctor critical pair: why the gate *replaces* the ctor rules

A gated group emits **either** the bare K rule **or** the constructor-major
rules, never both.  The minimal gated shape — a `Sort 0` family with no
parameters, no indices, and one field-free constructor (`True`-like:
`nparams = 0`, `nindices = 0`, `ctorSpine = 0`) — already exhibits the
conflict on the erased spine `rr M m c`:

- the bare K rule fires at the `const rr` head subterm and gives
  `(λ². bvar 0) M m c`, which β-reduces to `app m c`;
- the constructor-major rule fires at the whole spine and gives
  `(λ². bvar 0) M m`, which β-reduces to `m`.

Both chains are forced and end in distinct `EStep`-normal forms; the pair is
not joinable.  `iotaRulesKOf` therefore *replaces* `iotaRulesOf` when the
gate fires. -/

/-- The bare K rule `rr ~> λ². bvar 0` of the minimal gated shape. -/
def kcpKRule : CRule := iotaKRule 65 2 0 0 0

/-- The constructor-major rule `iotaRuleOfCtor` emits for the same shape
(`rr M m c ~> m`, major `c = const 64`), stated as the literal rule. -/
def kcpCtorRule : CRule :=
  { head := 65
    nargs := fun _ => 2
    major := some (64, fun _ => 0)
    rhs := fun _ _ => lamN 2 (.bvar 0) }

/-- The mutant coexistence table — deliberately **not** `TableWF`. -/
def kcpTable : List CRule := [kcpKRule, kcpCtorRule]

/-- Every rule in the mutant table has head 65. -/
theorem kcpTable_head {ρ : CRule} (h : ρ ∈ kcpTable) : ρ.head = 65 := by
  simp only [kcpTable, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> rfl

/-- A step of the head through a spine: `f → g` lifts to `f xs → g xs`. -/
theorem rStep_appN_head {tbl : List CRule} {f g : ETm} (h : RStep tbl f g) :
    (xs : List ETm) → RStep tbl (f.appN xs) (g.appN xs)
  | [] => h
  | x :: xs => rStep_appN_head (.appL x h) xs

/-- `EStep`-normality of `bvar` on the mutant table. -/
theorem kcpBvar_normal {i : Nat} {u : ETm} (h : EStep kcpTable (.bvar i) u) :
    False :=
  h.elim (rStep_bvar_normal _ _ _) (etaStep_bvar_normal _ _)

/-- No root step of the mutant table has `const 64` at its head: both rules
have head 65. -/
theorem kcpTable_no_root_64 {a b : ETm} (h : CRoot kcpTable a b)
    (ha : a = .const 64 []) : False := by
  cases h with
  | bare hρ _ ls args hn =>
      have hsp := congrArg ETm.spineHead ha
      rw [ETm.spineHead_appN] at hsp
      simp only [ETm.spineHead] at hsp
      injection hsp with h1 _
      rw [kcpTable_head hρ] at h1
      exact absurd h1 (by decide)
  | ctor hρ _ ls ls' args bs hn hb =>
      have hsp := congrArg ETm.spineHead ha
      rw [ETm.spineHead_appN] at hsp
      simp only [ETm.spineHead] at hsp
      injection hsp with h1 _
      rw [kcpTable_head hρ] at h1
      exact absurd h1 (by decide)

/-- `const 64` is `EStep`-normal in the mutant table. -/
theorem kcpConst64_normal {t : ETm} (h : EStep kcpTable (.const 64 []) t) :
    False := by
  rcases h with h | h
  · generalize hs : (ETm.const 64 [] : ETm) = s at h
    cases h with
    | cr hc => exact kcpTable_no_root_64 hc hs.symm
    | _ => cases hs
  · generalize hs : (ETm.const 64 [] : ETm) = s at h
    cases h <;> cases hs

/-- `λ². bvar 0` is `EStep`-normal in the mutant table: it is not an η redex
(its inner body is a `bvar`, not `app (lift F) (bvar 0)`), and `bvar 0` is
normal. -/
theorem kcpLam2_normal {t : ETm}
    (h : EStep kcpTable (lamN 2 (.bvar 0)) t) : False := by
  rcases h with h | h
  · generalize hs : (lamN 2 (.bvar 0) : ETm) = s at h
    cases h with
    | cr hc =>
        obtain ⟨c, ls, xs, hx⟩ := cRoot_lhs hc
        rw [← hs] at hx
        have hsp := congrArg ETm.spineHead hx
        rw [ETm.spineHead_appN] at hsp
        cases hsp
    | lam h' =>
        cases hs
        generalize hs2 : (lamN 1 (.bvar 0) : ETm) = s2 at h'
        cases h' with
        | cr hc =>
            obtain ⟨c, ls, xs, hx⟩ := cRoot_lhs hc
            rw [← hs2] at hx
            have hsp := congrArg ETm.spineHead hx
            rw [ETm.spineHead_appN] at hsp
            cases hsp
        | lam h'' =>
            cases hs2
            exact False.elim (rStep_bvar_normal _ _ _ h'')
        | _ => cases hs2
    | _ => cases hs
  · generalize hs : (lamN 2 (.bvar 0) : ETm) = s at h
    cases h with
    | eta F => cases hs
    | lam h' =>
        cases hs
        generalize hs2 : (lamN 1 (.bvar 0) : ETm) = s2 at h'
        cases h' with
        | eta F => cases hs2
        | lam h'' =>
            cases hs2
            exact False.elim (etaStep_bvar_normal _ _ h'')
        | _ => cases hs2
    | _ => cases hs

/-- The pair source `rr M m c` with `M = bvar 1`, `m = bvar 0`, `c = const 64`. -/
def kcpSrc : ETm := .app (.app (.app (.const 65 []) (.bvar 1)) (.bvar 0)) (.const 64 [])

/-- The K-side direct reduct: the bare rule fired at the `const 65` head. -/
def kcpDK : ETm := .app (.app (.app (lamN 2 (.bvar 0)) (.bvar 1)) (.bvar 0)) (.const 64 [])

/-- The ctor-side direct reduct: the constructor-major rule fired at the spine. -/
def kcpDC : ETm := .app (.app (lamN 2 (.bvar 0)) (.bvar 1)) (.bvar 0)

/-- The bare K rule fires at the `const 65` head subterm of `kcpSrc`. -/
theorem kcp_step_bare : RStep kcpTable kcpSrc kcpDK :=
  rStep_appN_head (.cr (.bare (List.Mem.head _) rfl [] [] rfl))
    [.bvar 1, .bvar 0, .const 64 []]

/-- The constructor-major rule fires at the whole `kcpSrc` spine. -/
theorem kcp_step_ctor : RStep kcpTable kcpSrc kcpDC :=
  .cr (.ctor (List.Mem.tail _ (List.Mem.head _)) rfl [] [] [.bvar 1, .bvar 0] [] rfl rfl)

/-- The K-side chain is forced: `kcpDK`'s only step is the β at the head
`app (lamN 2 (bvar 0)) (bvar 1)` of its function part, which computes to
`app (app (lam (bvar 0)) (bvar 0)) (const 64 [])`. -/
theorem kcpDK_step {z : ETm} (h : EStep kcpTable kcpDK z) :
    z = .app (.app (.lam (.bvar 0)) (.bvar 0)) (.const 64 []) := by
  rcases h with h | h
  · generalize hs : (kcpDK : ETm) = s at h
    cases h with
    | cr hc =>
        obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
        rw [← hs] at hx
        have hsp := congrArg ETm.spineHead hx
        rw [ETm.spineHead_appN] at hsp
        cases hsp
    | appL _ h' =>
        cases hs
        generalize hs2 : (ETm.app (.app (lamN 2 (.bvar 0)) (.bvar 1)) (.bvar 0) : ETm) = s2 at h'
        cases h' with
        | cr hc =>
            obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
            rw [← hs2] at hx
            have hsp := congrArg ETm.spineHead hx
            rw [ETm.spineHead_appN] at hsp
            cases hsp
        | appL _ h'' =>
            cases hs2
            generalize hs3 : (ETm.app (lamN 2 (.bvar 0)) (.bvar 1) : ETm) = s3 at h''
            cases h'' with
            | beta M N =>
                cases hs3
                rfl
            | cr hc =>
                obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
                rw [← hs3] at hx
                have hsp := congrArg ETm.spineHead hx
                rw [ETm.spineHead_appN] at hsp
                cases hsp
            | appL _ h''' =>
                cases hs3
                exact False.elim (kcpLam2_normal (.inl h'''))
            | appR _ h''' =>
                cases hs3
                exact False.elim (rStep_bvar_normal _ _ _ h''')
            | _ => cases hs3
        | appR _ h'' =>
            cases hs2
            exact False.elim (rStep_bvar_normal _ _ _ h'')
        | _ => cases hs2
    | appR _ h' =>
        cases hs
        exact False.elim (kcpConst64_normal (.inl h'))
    | _ => cases hs
  · generalize hs : (kcpDK : ETm) = s at h
    cases h with
    | eta F => cases hs
    | appL _ h' =>
        cases hs
        generalize hs2 : (ETm.app (.app (lamN 2 (.bvar 0)) (.bvar 1)) (.bvar 0) : ETm) = s2 at h'
        cases h' with
        | eta F => cases hs2
        | appL _ h'' =>
            cases hs2
            generalize hs3 : (ETm.app (lamN 2 (.bvar 0)) (.bvar 1) : ETm) = s3 at h''
            cases h'' with
            | eta F => cases hs3
            | appL _ h''' =>
                cases hs3
                exact False.elim (kcpLam2_normal (.inr h'''))
            | appR _ h''' =>
                cases hs3
                exact False.elim (etaStep_bvar_normal _ _ h''')
            | _ => cases hs3
        | appR _ h'' =>
            cases hs2
            exact False.elim (etaStep_bvar_normal _ _ h'')
        | _ => cases hs2
    | appR _ h' =>
        cases hs
        exact False.elim (kcpConst64_normal (.inr h'))
    | _ => cases hs

/-- The second K-side step is forced: `app (app (lam bvar0) bvar0) c`'s only
step is the β at `app (lam bvar0) (bvar 0)`, giving `app m c`. -/
theorem kcpDK1_step {z : ETm}
    (h : EStep kcpTable (.app (.app (.lam (.bvar 0)) (.bvar 0)) (.const 64 [])) z) :
    z = .app (.bvar 0) (.const 64 []) := by
  rcases h with h | h
  · generalize hs : (.app (.app (.lam (.bvar 0)) (.bvar 0)) (.const 64 []) : ETm) = s at h
    cases h with
    | beta M N => cases hs
    | cr hc =>
        obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
        rw [← hs] at hx
        have hsp := congrArg ETm.spineHead hx
        rw [ETm.spineHead_appN] at hsp
        cases hsp
    | appL _ h' =>
        cases hs
        generalize hs2 : (ETm.app (.lam (.bvar 0)) (.bvar 0) : ETm) = s2 at h'
        cases h' with
        | beta M N =>
            cases hs2
            rfl
        | cr hc =>
            obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
            rw [← hs2] at hx
            have hsp := congrArg ETm.spineHead hx
            rw [ETm.spineHead_appN] at hsp
            cases hsp
        | appL _ h'' =>
            cases hs2
            generalize hs3 : (ETm.lam (.bvar 0) : ETm) = s3 at h''
            cases h'' with
            | cr hc =>
                obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
                rw [← hs3] at hx
                have hsp := congrArg ETm.spineHead hx
                rw [ETm.spineHead_appN] at hsp
                cases hsp
            | lam h3 =>
                cases hs3
                exact False.elim (rStep_bvar_normal _ _ _ h3)
            | _ => cases hs3
        | appR _ h'' =>
            cases hs2
            exact False.elim (rStep_bvar_normal _ _ _ h'')
        | _ => cases hs2
    | appR _ h' =>
        cases hs
        exact False.elim (kcpConst64_normal (.inl h'))
    | _ => cases hs
  · generalize hs : (.app (.app (.lam (.bvar 0)) (.bvar 0)) (.const 64 []) : ETm) = s at h
    cases h with
    | eta F => cases hs
    | appL _ h' =>
        cases hs
        generalize hs2 : (ETm.app (.lam (.bvar 0)) (.bvar 0) : ETm) = s2 at h'
        cases h' with
        | eta F => cases hs2
        | appL _ h'' =>
            cases hs2
            generalize hs3 : (ETm.lam (.bvar 0) : ETm) = s3 at h''
            cases h'' with
            | eta F => cases hs3
            | lam h3 =>
                cases hs3
                exact False.elim (etaStep_bvar_normal _ _ h3)
            | _ => cases hs3
        | appR _ h'' =>
            cases hs2
            exact False.elim (etaStep_bvar_normal _ _ h'')
        | _ => cases hs2
    | appR _ h' =>
        cases hs
        exact False.elim (kcpConst64_normal (.inr h'))
    | _ => cases hs

/-- `app m c` is `EStep`-normal in the mutant table. -/
theorem kcpNK_normal {z : ETm}
    (h : EStep kcpTable (.app (.bvar 0) (.const 64 [])) z) : False := by
  rcases h with h | h
  · generalize hs : (.app (.bvar 0) (.const 64 []) : ETm) = s at h
    cases h with
    | cr hc =>
        obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
        rw [← hs] at hx
        have hsp := congrArg ETm.spineHead hx
        rw [ETm.spineHead_appN] at hsp
        cases hsp
    | appL _ h' => cases hs; exact False.elim (rStep_bvar_normal _ _ _ h')
    | appR _ h' => cases hs; exact False.elim (kcpConst64_normal (.inl h'))
    | _ => cases hs
  · generalize hs : (.app (.bvar 0) (.const 64 []) : ETm) = s at h
    cases h with
    | eta F => cases hs
    | appL _ h' => cases hs; exact False.elim (etaStep_bvar_normal _ _ h')
    | appR _ h' => cases hs; exact False.elim (kcpConst64_normal (.inr h'))
    | _ => cases hs

/-- The ctor-side chain is forced: `kcpDC`'s only step is the β at
`app (lamN 2 (bvar 0)) (bvar 1)`, giving `app (lam bvar0) bvar0`. -/
theorem kcpDC_step {z : ETm} (h : EStep kcpTable kcpDC z) :
    z = .app (.lam (.bvar 0)) (.bvar 0) := by
  rcases h with h | h
  · generalize hs : (kcpDC : ETm) = s at h
    cases h with
    | cr hc =>
        obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
        rw [← hs] at hx
        have hsp := congrArg ETm.spineHead hx
        rw [ETm.spineHead_appN] at hsp
        cases hsp
    | appL _ h' =>
        cases hs
        generalize hs2 : (ETm.app (lamN 2 (.bvar 0)) (.bvar 1) : ETm) = s2 at h'
        cases h' with
        | beta M N =>
            cases hs2
            rfl
        | cr hc =>
            obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
            rw [← hs2] at hx
            have hsp := congrArg ETm.spineHead hx
            rw [ETm.spineHead_appN] at hsp
            cases hsp
        | appL _ h'' =>
            cases hs2
            exact False.elim (kcpLam2_normal (.inl h''))
        | appR _ h'' =>
            cases hs2
            exact False.elim (rStep_bvar_normal _ _ _ h'')
        | _ => cases hs2
    | appR _ h' =>
        cases hs
        exact False.elim (rStep_bvar_normal _ _ _ h')
    | _ => cases hs
  · generalize hs : (kcpDC : ETm) = s at h
    cases h with
    | eta F => cases hs
    | appL _ h' =>
        cases hs
        generalize hs2 : (ETm.app (lamN 2 (.bvar 0)) (.bvar 1) : ETm) = s2 at h'
        cases h' with
        | eta F => cases hs2
        | appL _ h'' =>
            cases hs2
            exact False.elim (kcpLam2_normal (.inr h''))
        | appR _ h'' =>
            cases hs2
            exact False.elim (etaStep_bvar_normal _ _ h'')
        | _ => cases hs2
    | appR _ h' =>
        cases hs
        exact False.elim (etaStep_bvar_normal _ _ h')
    | _ => cases hs

/-- `app (lam bvar0) bvar0`'s only step is the final β, giving `bvar 0`. -/
theorem kcpDC1_step {z : ETm}
    (h : EStep kcpTable (.app (.lam (.bvar 0)) (.bvar 0)) z) :
    z = .bvar 0 := by
  rcases h with h | h
  · generalize hs : (.app (.lam (.bvar 0)) (.bvar 0) : ETm) = s at h
    cases h with
    | beta M N =>
        cases hs
        rfl
    | cr hc =>
        obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
        rw [← hs] at hx
        have hsp := congrArg ETm.spineHead hx
        rw [ETm.spineHead_appN] at hsp
        cases hsp
    | appL _ h' =>
        cases hs
        generalize hs2 : (ETm.lam (.bvar 0) : ETm) = s2 at h'
        cases h' with
        | cr hc =>
            obtain ⟨r, ls, xs, hx⟩ := cRoot_lhs hc
            rw [← hs2] at hx
            have hsp := congrArg ETm.spineHead hx
            rw [ETm.spineHead_appN] at hsp
            cases hsp
        | lam h'' =>
            cases hs2
            exact False.elim (rStep_bvar_normal _ _ _ h'')
        | _ => cases hs2
    | appR _ h' =>
        cases hs
        exact False.elim (rStep_bvar_normal _ _ _ h')
    | _ => cases hs
  · generalize hs : (.app (.lam (.bvar 0)) (.bvar 0) : ETm) = s at h
    cases h with
    | eta F => cases hs
    | appL _ h' =>
        cases hs
        generalize hs2 : (ETm.lam (.bvar 0) : ETm) = s2 at h'
        cases h' with
        | eta F => cases hs2
        | lam h'' =>
            cases hs2
            exact False.elim (etaStep_bvar_normal _ _ h'')
        | _ => cases hs2
    | appR _ h' =>
        cases hs
        exact False.elim (etaStep_bvar_normal _ _ h')
    | _ => cases hs

/-- The K-side chain reaches the normal form `app m c` in two β steps. -/
theorem kcp_chain_K :
    RStar (EStep kcpTable) kcpDK (.app (.bvar 0) (.const 64 [])) :=
  .step (.inl (rStep_appN_head (.beta (lamN 1 (.bvar 0)) (.bvar 1))
        [.bvar 0, .const 64 []]))
    (.step (.inl (.appL _ (.beta (.bvar 0) (.bvar 0)))) (.refl _))

/-- The ctor-side chain reaches the normal form `bvar 0` in two β steps. -/
theorem kcp_chain_C : RStar (EStep kcpTable) kcpDC (.bvar 0) :=
  .step (.inl (rStep_appN_head (.beta (lamN 1 (.bvar 0)) (.bvar 1)) [.bvar 0]))
    (.step (.inl (.beta (.bvar 0) (.bvar 0))) (.refl _))

/-- Every reduct of `kcpDK` is a point of the forced chain. -/
theorem kcpDK_reduct {z : ETm} (h : RStar (EStep kcpTable) kcpDK z) :
    z = kcpDK ∨ z = .app (.app (.lam (.bvar 0)) (.bvar 0)) (.const 64 []) ∨
    z = .app (.bvar 0) (.const 64 []) := by
  cases h with
  | refl => exact .inl rfl
  | step h1 h2 =>
      obtain rfl := kcpDK_step h1
      cases h2 with
      | refl => exact .inr (.inl rfl)
      | step h3 h4 =>
          obtain rfl := kcpDK1_step h3
          cases h4 with
          | refl => exact .inr (.inr rfl)
          | step h5 _ => exact absurd h5 (fun h6 => kcpNK_normal h6)

/-- Every reduct of `kcpDC` is a point of the forced chain. -/
theorem kcpDC_reduct {z : ETm} (h : RStar (EStep kcpTable) kcpDC z) :
    z = kcpDC ∨ z = .app (.lam (.bvar 0)) (.bvar 0) ∨ z = .bvar 0 := by
  cases h with
  | refl => exact .inl rfl
  | step h1 h2 =>
      obtain rfl := kcpDC_step h1
      cases h2 with
      | refl => exact .inr (.inl rfl)
      | step h3 h4 =>
          obtain rfl := kcpDC1_step h3
          cases h4 with
          | refl => exact .inr (.inr rfl)
          | step h5 _ => exact absurd h5 (fun h6 => kcpBvar_normal h6)

/-- `≈` never relates an `app` to a `lam`. -/
theorem lvlEq_app_lam_ne {f a b : ETm} : ¬ LvlEq (.app f a) (.lam b) :=
  fun h => by cases h

/-- `≈` never relates an `app` to a `bvar`. -/
theorem lvlEq_app_bvar_ne {f a : ETm} {i : Nat} : ¬ LvlEq (.app f a) (.bvar i) :=
  fun h => by cases h

/-- `≈` never relates a `bvar` to an `app`. -/
theorem lvlEq_bvar_app_ne {i : Nat} {f a : ETm} : ¬ LvlEq (.bvar i) (.app f a) :=
  fun h => by cases h

/-- `≈` never relates a `bvar` to a `lam`. -/
theorem lvlEq_bvar_lam_ne {i : Nat} {b : ETm} : ¬ LvlEq (.bvar i) (.lam b) :=
  fun h => by cases h

/-- `≈` inversion on `lam`. -/
theorem lvlEq_lam_inv {b b' : ETm} : LvlEq (.lam b) (.lam b') → LvlEq b b'
  | .lam h => h

/-- `≈` inversion on `app`, function part. -/
theorem lvlEq_app_inv {f f' a a' : ETm} : LvlEq (.app f a) (.app f' a') →
    LvlEq f f'
  | .app h _ => h

/-- **The critical pair is not joinable.**  Every `d` reached from the K
reduct is `lam`-headed or ends in the `const 64` argument; every `e` reached
from the ctor reduct is `lam`-headed or `bvar 0` itself; no pair is `≈`.
Emitting both rules for one gated group would therefore break confluence —
the gate replaces rather than augments. -/
theorem kcp_not_joinable :
    ¬ JoinMod (EStep kcpTable) LvlEq kcpDK kcpDC := by
  rintro ⟨d, e, hK, hle, hC⟩
  rcases kcpDK_reduct hK with rfl | rfl | rfl <;>
    rcases kcpDC_reduct hC with rfl | rfl | rfl
  · exact lvlEq_app_lam_ne (lvlEq_app_inv (lvlEq_app_inv hle))
  · exact lvlEq_app_lam_ne (lvlEq_app_inv hle)
  · exact lvlEq_app_bvar_ne hle
  · exact lvlEq_bvar_lam_ne (lvlEq_lam_inv (lvlEq_app_inv (lvlEq_app_inv hle)))
  · exact lvlEq_app_lam_ne (lvlEq_app_inv hle)
  · exact lvlEq_app_bvar_ne hle
  · exact lvlEq_bvar_app_ne (lvlEq_app_inv hle)
  · exact lvlEq_bvar_lam_ne (lvlEq_app_inv hle)
  · exact lvlEq_app_bvar_ne hle
