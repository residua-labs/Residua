import rcic.RcicSynTableNoHead
import rcic.RcicSynTableBuildI

/-!
# tableOfI team, PART 2 — `TableWF`'s structural fields for `tableOfI hEnv`

`~/.residua-lean/briefs/swe-tablei-common.md` (cc, 2026-10-19). The wall
(`RcicSynBelowPortsTableObstruction`): `tableOf` emits no ι rules, so
`AllBelowScoped`/`StepSuppliers` are false on `tableOf natEnvUWfT` at every
weight. PART 1 (`swe-constlit`, `RcicSynTableBuildI`, PR #7719) supplies
`iotaRulesOf`/`buildTableSyntaxI`/`tableOfI` — `tableOf`'s δ entries plus, at
each admitted `.group` node, one erased `CRule` per constructor whose field
analysis passes the `iotaCtorSafe` gates.

This module is PART 2 — repaired per the lane-2 audit (no assumption-side
`ctor_inj`/`nargs_eq`): the four structural `TableWF` fields `rigid`,
`ctor_disjoint`, `bare_unique`, `bare_nullary` are proved directly on
`tableOfI hEnv` with `hEnv : EnvWfT E` as the only hypothesis. Both properties
the audit flagged are *derived*:

* `nargs_eq`: `iotaRuleOfCtor` emits `nargs := fun _ ↦ N` where
  `N = nparams + 1 + nMinors + nindices` is `let`-bound once per
  `iotaRulesOf` call — `mem_iotaRulesOf`/`iotaRuleOfCtor_spec` pin the same
  `N` (as `piCount fm.mtype - iotaNindices rm` etc.), so same-call rules
  share `nargs` literally.
* `ctor_inj`: `GroupMembersT` installs each member fresh in the chain's own
  base env, so the ctor refs of one group are pairwise distinct
  (`groupMembersT_fst_nodup`/`groupMembersT_ctors_fst_nodup`); equal majors
  then force equal `ctors[i]`, hence identical emissions.

The δ/ι separation is member-class disjointness: δ heads resolve to
`.definitionM` members (`head_defM_build`), ι heads to the group's
`.recursorM` member (`groupMembersT_lookup` on `(rr, rm)`), ι majors to
`.constructorM` members — and each env ref resolves to at most one member
(`members_ne_of_mclass_ne`). Cross-group same-head pairs die on freshness: a
group's recursor ref is `none` in every env built before its node
(`groupMembersT_freshE`).

`tableCongr_append` is the team's canonical append combinator — the single
copy lives here (PART 3's `RcicSynTableCongrI` must not re-declare it).
`tableWF_tableOfI` assembles the full `TableWF` with PART 3's `congr`/`closed`
halves as hypotheses; `tableWF_nat_tableOfI` discharges them concretely on the
wall instance — `tableOfI natEnvUWfT = [natZeroRule, natSuccRule]` by
`iotaRulesOf_nat` — giving `TableWF (tableOfI natEnvUWfT)` outright.

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 member-chain facts: lookup, base-freshness, ref nodup -/

/-- Every pair a `GroupMembersT` chain installs resolves to its member in the
    chain's end env: each step `extendEnv`s, and later installs are fresh so
    they never overwrite earlier ones. -/
theorem groupMembersT_lookup {S : ResolvedEnv} :
    {E : ResolvedEnv} → {l : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E l E' → {r : Nat} → {m : CheckedMember} → (r, m) ∈ l →
    E'.members r = some m
  | _, _, _, .nil _, _, _, h => absurd h (List.not_mem_nil _)
  | _, _, _, .cons E r₀ m₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest, _, _, h => by
      rcases List.mem_cons.1 h with h | h
      · obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq ..).mp h
        exact groupMembersT_ext hrest _ _ (members_extend_self _ _ _)
      · exact groupMembersT_lookup hrest h

/-- Every pair a `GroupMembersT` chain installs is fresh in the chain's BASE
    env: each step's `hfresh` is at its own prefix env, and membership `none`
    descends an `extendEnv` when the refs differ — which they must, since the
    later ref is fresh where the earlier already resolves. -/
theorem groupMembersT_freshE {S E : ResolvedEnv} {l : List (Nat × CheckedMember)}
    {E' : ResolvedEnv} (h : GroupMembersT S E l E') :
    ∀ {r m}, (r, m) ∈ l → E.members r = none := by
  induction h with
  | nil E => intro r m hm; cases hm
  | cons E r₀ m₀ rest E' hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
      intro r m hm
      rcases List.mem_cons.mp hm with hhead | htail
      · cases hhead; exact hfresh
      · have h' := ih htail
        have h'' : (if r = r₀ then some m₀ else E.members r) = none := h'
        by_cases hr : r = r₀
        · rw [if_pos hr] at h''
          exact Option.noConfusion h''
        · rw [if_neg hr] at h''
          exact h''

/-- The refs a member chain installs are pairwise distinct: a later ref is
    fresh in the env that already resolves each earlier one. -/
theorem groupMembersT_fst_nodup {S E : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    {E' : ResolvedEnv} (h : GroupMembersT S E ms E') :
    (ms.map Prod.fst).Nodup := by
  induction h with
  | nil E => exact List.nodup_nil
  | cons E r₀ m₀ rest E' hfresh _ _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hr
      rcases List.mem_map.mp hr with ⟨x, hx, hfx⟩
      have hfr := groupMembersT_freshE hrest hx
      rw [hfx] at hfr
      rw [members_extend_self] at hfr
      exact Option.noConfusion hfr

/-- The ctor refs of one admitted group are pairwise distinct — the `ctors`
    segment is a sublist of the chain's own member list. -/
theorem groupMembersT_ctors_fst_nodup {S E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)} {rr : Nat}
    {rm : CheckedMember} {E' : ResolvedEnv}
    (hmem : GroupMembersT S E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    (ctors.map Prod.fst).Nodup :=
  List.Nodup.sublist
    (List.Sublist.map Prod.fst
      ((List.sublist_append_left ctors [(rr, rm)]).trans
        (List.sublist_cons_self (f, fm) _)))
    (groupMembersT_fst_nodup hmem)

/-! ## §2 the `iotaRulesOf` emission spec -/

/-- Positional membership in `mapIdx.go`'s output: anything it emits either was
    already in the accumulator or is `f (acc.size + i) l[i]` at a real position.
    Proved on `go` itself — core's `List.mem_mapIdx`/`getElem?_mapIdx` route
    through `enum`/`range` and pull `Classical.choice`, which this module's
    axiom gate excludes. -/
theorem mem_mapIdx_go' {α β : Type _} {f : Nat → α → β} {b : β} :
    ∀ {l : List α} {acc : Array β},
      b ∈ List.mapIdx.go f l acc →
        b ∈ acc.toList ∨ ∃ (i : Nat) (hi : i < l.length), f (acc.size + i) l[i] = b
  | [], _, h => .inl h
  | a :: t, acc, h => by
      rcases mem_mapIdx_go' (acc := acc.push (f acc.size a)) h with hacc |
          ⟨i, hi, hgi⟩
      · rw [Array.push_toList] at hacc
        rcases List.mem_append.mp hacc with hacc | hacc
        · exact .inl hacc
        · obtain rfl : b = f acc.size a := List.eq_of_mem_singleton hacc
          exact .inr ⟨0, Nat.succ_pos _, rfl⟩
      · refine .inr ⟨i + 1, Nat.succ_lt_succ hi, ?_⟩
        rw [Array.size_push] at hgi
        have hadd : acc.size + 1 + i = acc.size + (i + 1) := by omega
        rw [hadd] at hgi
        exact hgi

/-- Positional membership in `l.mapIdx f`: every emitted element is
    `f i l[i]` at position `i`. The `Classical.choice`-free sibling of
    `List.mem_mapIdx`, via `mem_mapIdx_go'`. -/
theorem mem_mapIdx' {α β : Type _} {f : Nat → α → β} {b : β} {l : List α}
    (h : b ∈ l.mapIdx f) : ∃ (i : Nat) (hi : i < l.length), f i l[i] = b := by
  have h' : b ∈ List.mapIdx.go f l #[] := h
  rcases mem_mapIdx_go' h' with hacc | ⟨i, hi, hgi⟩
  · exact absurd hacc (List.not_mem_nil _)
  · refine ⟨i, hi, ?_⟩
    have e0 : ((#[] : Array β).size) = 0 := rfl
    rw [e0] at hgi
    rwa [Nat.zero_add] at hgi

/-- The index count `iotaRulesOf` extracts from the recursor's stored type:
    its body's app spine is `motive idx… major`, so `length - 1` — the same
    `nindices` the emitted rules see, named as a function of `rm` so the spec
    is literal-equality strong (the `0`-spine arm emits no rules; the value
    there is unreachable through membership). -/
def iotaNindices (rm : CheckedMember) : Nat :=
  match peelPis (piCount rm.mtype) rm.mtype with
  | none => 0
  | some (_, recBody) => (appsSpine recBody).2.length - 1

/-- Membership in `iotaRulesOf`'s output pins the full emission: position `i`
    of the ctor list, the group's own `nparams`/`nindices`/`nMinors`, and the
    `iotaRuleOfCtor` call itself — so two emitted rules with equal ctor refs
    are the same `iotaRuleOfCtor` output. -/
theorem mem_iotaRulesOf {f : Nat} {fm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} {rr : Nat} {rm : CheckedMember}
    {ρ : CRule} (h : ρ ∈ iotaRulesOf f fm ctors rr rm) :
    ∃ (i : Nat) (hi : i < ctors.length),
      iotaRuleOfCtor rr f (piCount fm.mtype - iotaNindices rm)
        (iotaNindices rm) ctors.length i ctors[i].1 ctors[i].2 = some ρ := by
  simp only [iotaRulesOf] at h
  split at h
  · exact absurd h (List.not_mem_nil _)
  · rename_i x recBody hpeel
    split at h
    · exact absurd h (List.not_mem_nil _)
    · rename_i nindices hlen
      split at h
      · exact absurd h (List.not_mem_nil _)
      · rcases List.mem_filterMap.mp h with ⟨a, ham, ha⟩
        rcases mem_mapIdx' ham with ⟨i, hi, hgi⟩
        have hI : iotaNindices rm = nindices := by
          simp only [iotaNindices, hpeel, hlen]
          omega
        refine ⟨i, hi, ?_⟩
        have hem := hgi.trans ha
        rw [← hI] at hem
        exact hem

/-- What `iotaRuleOfCtor` emits when it emits: head the group recursor `rr`,
    `nargs` the shared `nparams + 1 + nMinors + nindices`, `major` the ctor
    ref with its `ctorSpine` arity — everything else is gated out. -/
theorem iotaRuleOfCtor_spec {rr fam nparams nindices nMinors ctorIdx ctorRef : Nat}
    {cm : CheckedMember} {ρ : CRule}
    (h : iotaRuleOfCtor rr fam nparams nindices nMinors ctorIdx ctorRef cm =
      some ρ) :
    ρ.head = rr ∧
    ρ.nargs = (fun _ => nparams + 1 + nMinors + nindices) ∧
    ∃ k, ρ.major = some (ctorRef, k) := by
  simp only [iotaRuleOfCtor] at h
  split at h
  · exact Option.noConfusion h
  · split at h
    · exact Option.noConfusion h
    · split at h
      · exact Option.noConfusion h
      · split at h
        · injection h with hρ
          subst hρ
          exact ⟨rfl, rfl, _, rfl⟩
        · exact Option.noConfusion h

/-! ## §3 head/major classification of `tableOfI hEnv` -/

/-- Two refs resolving to members of different classes are different refs —
    `members` is a function, so equal refs give equal members. -/
theorem members_ne_of_mclass_ne {E : ResolvedEnv} {a b : Nat} {ma mb : CheckedMember}
    (ha : E.members a = some ma) (hb : E.members b = some mb)
    (hne : ma.mclass ≠ mb.mclass) : a ≠ b := by
  intro h; subst h
  exact hne (congrArg CheckedMember.mclass (Option.some.inj (ha.symm.trans hb)))

/-- Every `tableOfI` rule is either a `tableOf` δ rule (head resolves to the
    `.definitionM` member) or an `iotaRulesOf` emission (head resolves to the
    group's `.recursorM` member and its major to a `.constructorM` member) —
    all resolutions in the node's own env, transported out by the chain's
    `EnvExt`. -/
theorem tableOfI_head_major {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfI hEnv,
      (∃ m, E.members ρ.head = some m ∧ m.mclass = .definitionM ∧
        ρ ∈ tableOf hEnv) ∨
      (∃ m, E.members ρ.head = some m ∧ m.mclass = .recursorM ∧
        ∃ (d : Nat) (k : List Level → Nat) (md : CheckedMember),
          ρ.major = some (d, k) ∧ E.members d = some md ∧
            md.mclass = .constructorM) := by
  induction hEnv with
  | empty => intro ρ hρ; cases hρ
  | «axiom» _ _ _ _ hE hfresh _ _ _ ih =>
      intro ρ hρ; rw [tableOfI_axiom] at hρ
      rcases ih ρ hρ with ⟨m, hm, hmc, htb⟩ | ⟨m, hm, hmc, d, k, md, hmaj, hdm, hmc'⟩
      · refine .inl ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, ?_⟩
        rw [tableOf_axiom]; exact htb
      · exact .inr ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, d, k, md, hmaj,
          envExt_extendEnv _ hfresh _ _ hdm, hmc'⟩
  | thm _ _ _ _ hE hfresh _ _ _ _ _ _ ih =>
      intro ρ hρ; rw [tableOfI_thm] at hρ
      rcases ih ρ hρ with ⟨m, hm, hmc, htb⟩ | ⟨m, hm, hmc, d, k, md, hmaj, hdm, hmc'⟩
      · refine .inl ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, ?_⟩
        rw [tableOf_thm]; exact htb
      · exact .inr ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, d, k, md, hmaj,
          envExt_extendEnv _ hfresh _ _ hdm, hmc'⟩
  | «opaque» _ _ _ _ _ hE hfresh _ _ _ _ _ _ ih =>
      intro ρ hρ; rw [tableOfI_opaque] at hρ
      rcases ih ρ hρ with ⟨m, hm, hmc, htb⟩ | ⟨m, hm, hmc, d, k, md, hmaj, hdm, hmc'⟩
      · refine .inl ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, ?_⟩
        rw [tableOf_opaque]; exact htb
      · exact .inr ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, d, k, md, hmaj,
          envExt_extendEnv _ hfresh _ _ hdm, hmc'⟩
  | definition _ r _ _ _ hE hfresh _ _ _ _ _ _ ih =>
      intro ρ hρ; rw [tableOfI_definition] at hρ
      rcases List.mem_cons.mp hρ with rfl | hρ'
      · refine .inl ⟨⟨.definitionM, 0, _, some _⟩, members_extend_self _ _ _, rfl, ?_⟩
        rw [tableOf_definition]; exact List.Mem.head _
      · rcases ih ρ hρ' with ⟨m, hm, hmc, htb⟩ |
            ⟨m, hm, hmc, d, k, md, hmaj, hdm, hmc'⟩
        · refine .inl ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, ?_⟩
          rw [tableOf_definition]; exact List.Mem.tail _ htb
        · exact .inr ⟨m, envExt_extendEnv _ hfresh _ _ hm, hmc, d, k, md, hmaj,
            envExt_extendEnv _ hfresh _ _ hdm, hmc'⟩
  | group E f fm ctors rr rm E' hE hfam hctors hrec hmem ih =>
      intro ρ hρ; rw [tableOfI_group] at hρ
      rcases List.mem_append.mp hρ with hι | hδ
      · obtain ⟨i, hi, hemi⟩ := mem_iotaRulesOf hι
        obtain ⟨hhead, -, k, hmaj⟩ := iotaRuleOfCtor_spec hemi
        refine .inr ⟨rm, ?_, hrec, ctors[i].1, k, ctors[i].2, hmaj, ?_,
          hctors _ (List.getElem_mem hi)⟩
        · rw [hhead]
          exact groupMembersT_lookup hmem (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_singleton_self _)))
        · exact groupMembersT_lookup hmem (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.getElem_mem hi)))
      · rcases ih ρ hδ with ⟨m, hm, hmc, htb⟩ |
            ⟨m, hm, hmc, d, k, md, hmaj, hdm, hmc'⟩
        · refine .inl ⟨m, groupMembersT_ext hmem _ _ hm, hmc, ?_⟩
          rw [tableOf_group]; exact htb
        · exact .inr ⟨m, groupMembersT_ext hmem _ _ hm, hmc, d, k, md, hmaj,
            groupMembersT_ext hmem _ _ hdm, hmc'⟩

/-- Every `tableOfI` rule's head resolves in the node's env — the projection
    of `tableOfI_head_major`. -/
theorem head_mem_tableOfI {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfI hEnv, ∃ m, E.members ρ.head = some m := by
  intro ρ hρ
  rcases tableOfI_head_major hEnv ρ hρ with ⟨m, hm, -, -⟩ | ⟨m, hm, -, -⟩ <;>
    exact ⟨m, hm⟩

/-! ## §4 the four `TableWF` fields on `tableOfI hEnv` -/

/-- `TableWF.rigid` on `tableOfI hEnv`: a major-bearing rule's ctor ref
    resolves to `.constructorM`; every table head resolves to `.definitionM`
    or `.recursorM` — never equal. -/
theorem tableOfI_rigid {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfI hEnv, ∀ {d : Nat} {m : List Level → Nat},
      ρ.major = some (d, m) → ∀ σ ∈ tableOfI hEnv, σ.head ≠ d := by
  intro ρ hρ d m hm σ hσ hhead
  rcases tableOfI_head_major hEnv ρ hρ with ⟨_, _, _, htb⟩ |
      ⟨_, _, _, d', k, md, hmaj, hd, hmc'⟩
  · exact Option.noConfusion (hm.symm.trans (major_none_tableOf hEnv ρ htb))
  · have hd' : d = d' := congrArg Prod.fst (Option.some.inj (hm.symm.trans hmaj))
    subst hd'
    rcases tableOfI_head_major hEnv σ hσ with ⟨ms, hs, hcs, -⟩ |
        ⟨ms, hs, hcs, -⟩ <;>
      exact members_ne_of_mclass_ne hs hd
        (fun h => MemberClass.noConfusion (hcs.symm.trans (h.trans hmc'))) hhead

/-- `ctor_disjoint` within ONE `iotaRulesOf` call: `nargs` is the same literal
    `fun _ ↦ N` (`iotaRuleOfCtor_spec` at the shared call parameters), and
    equal ctor majors force equal `ctors[i]` — the chain's ctor refs are
    nodup — hence identical emissions. -/
theorem iotaRulesOf_ctor_disjoint {S E : ResolvedEnv} {f : Nat}
    {fm : CheckedMember} {ctors : List (Nat × CheckedMember)} {rr : Nat}
    {rm : CheckedMember} {E' : ResolvedEnv}
    (hmem : GroupMembersT S E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
    ∀ ρ ∈ iotaRulesOf f fm ctors rr rm,
      ∀ σ ∈ iotaRulesOf f fm ctors rr rm, ρ.head = σ.head →
      ∀ {d e : Nat} {m n : List Level → Nat},
        ρ.major = some (d, m) → σ.major = some (e, n) →
        ρ.nargs = σ.nargs ∧ (d = e → σ = ρ) := by
  intro ρ hρ σ hσ _ d e m n hm hn
  obtain ⟨i, hi, hρi⟩ := mem_iotaRulesOf hρ
  obtain ⟨j, hj, hσj⟩ := mem_iotaRulesOf hσ
  obtain ⟨-, hna, ki, hmaji⟩ := iotaRuleOfCtor_spec hρi
  obtain ⟨-, hnb, kj, hmajj⟩ := iotaRuleOfCtor_spec hσj
  refine ⟨hna.trans hnb.symm, fun hde => ?_⟩
  have hdi : d = ctors[i].1 :=
    congrArg Prod.fst (Option.some.inj (hm.symm.trans hmaji))
  have hej : e = ctors[j].1 :=
    congrArg Prod.fst (Option.some.inj (hn.symm.trans hmajj))
  have hcfst : ctors[i].1 = ctors[j].1 := hdi.symm.trans (hde.trans hej)
  have hnd := groupMembersT_ctors_fst_nodup hmem
  have hij : i = j :=
    List.getElem?_inj (xs := ctors.map Prod.fst) (by rwa [List.length_map]) hnd
      (by rw [List.getElem?_map, List.getElem?_map,
              List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
              Option.map_some', Option.map_some']
          exact congrArg some hcfst)
  subst hij
  exact Option.some.inj (hσj.symm.trans hρi)

/-- `TableWF.ctor_disjoint` on `tableOfI hEnv`: two major-bearing rules with
    the same head sit in the same `iotaRulesOf` call — every other pairing
    dies on member-class or freshness — and there the group's own ctor nodup
    discharges `ctor_inj`, while `nargs` is the call's single `fun _ ↦ N`. -/
theorem tableOfI_ctor_disjoint {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfI hEnv, ∀ σ ∈ tableOfI hEnv, ρ.head = σ.head →
      ∀ {d e : Nat} {m n : List Level → Nat},
        ρ.major = some (d, m) → σ.major = some (e, n) →
        ρ.nargs = σ.nargs ∧ (d = e → σ = ρ) := by
  induction hEnv with
  | empty => intro ρ hρ; cases hρ
  | «axiom» _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ σ hσ; rw [tableOfI_axiom] at hρ hσ; exact ih ρ hρ σ hσ
  | thm _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ σ hσ; rw [tableOfI_thm] at hρ hσ; exact ih ρ hρ σ hσ
  | «opaque» _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ σ hσ; rw [tableOfI_opaque] at hρ hσ; exact ih ρ hρ σ hσ
  | definition _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro ρ hρ σ hσ hh d e m n hm hn
      rw [tableOfI_definition] at hρ hσ
      rcases List.mem_cons.mp hρ with rfl | hρ' <;>
        rcases List.mem_cons.mp hσ with rfl | hσ'
      · exact Option.noConfusion hm
      · exact Option.noConfusion hm
      · exact Option.noConfusion hn
      · exact ih ρ hρ' σ hσ' hh hm hn
  | group E f fm ctors rr rm E' hE hfam hctors hrec hmem ih =>
      intro ρ hρ σ hσ hh d e m n hm hn
      rw [tableOfI_group] at hρ hσ
      rcases List.mem_append.mp hρ with hρι | hρt <;>
        rcases List.mem_append.mp hσ with hσι | hσt
      · exact iotaRulesOf_ctor_disjoint hmem ρ hρι σ hσι hh hm hn
      · obtain ⟨i, hi, hemi⟩ := mem_iotaRulesOf hρι
        obtain ⟨hhead, -, -⟩ := iotaRuleOfCtor_spec hemi
        obtain ⟨ms, hs⟩ := head_mem_tableOfI hE σ hσt
        have hrr : E.members rr = none := groupMembersT_freshE hmem
          (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_singleton_self _)))
        rw [← hhead] at hrr
        rw [hh] at hrr
        exact Option.noConfusion (hs.symm.trans hrr)
      · obtain ⟨j, hj, hσj⟩ := mem_iotaRulesOf hσι
        obtain ⟨hshead, -, -⟩ := iotaRuleOfCtor_spec hσj
        obtain ⟨mr, hr⟩ := head_mem_tableOfI hE ρ hρt
        have hrr : E.members rr = none := groupMembersT_freshE hmem
          (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_singleton_self _)))
        rw [← hshead, ← hh] at hrr
        exact Option.noConfusion (hr.symm.trans hrr)
      · exact ih ρ hρt σ hσt hh hm hn

/-- `TableWF.bare_unique` on `tableOfI hEnv`: a bare rule is a `tableOf` δ
    rule (`ι` rules always carry a major), so its head resolves
    `.definitionM`; a same-head ι rule would resolve `.recursorM` — class
    disjoint — and the δ–δ case is the landed `tableWF_build`. -/
theorem tableOfI_bare_unique {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfI hEnv, ρ.major = none →
      ∀ σ ∈ tableOfI hEnv, σ.head = ρ.head → σ = ρ := by
  intro ρ hρ hm σ hσ hhead
  rcases tableOfI_head_major hEnv ρ hρ with ⟨md, hdm, hmc, htb⟩ |
      ⟨_, _, _, d', k, _, hmaj, -, -⟩
  · rcases tableOfI_head_major hEnv σ hσ with ⟨_, _, _, htb'⟩ |
        ⟨ms, hs, hcs, -⟩
    · exact (tableWF_build hEnv).bare_unique ρ htb hm σ htb' hhead
    · rw [hhead] at hs
      have hme : ms.mclass = md.mclass :=
        congrArg CheckedMember.mclass (Option.some.inj (hs.symm.trans hdm))
      exact MemberClass.noConfusion (hcs.symm.trans (hme.trans hmc))
  · exact Option.noConfusion (hmaj.symm.trans hm)

/-- `TableWF.bare_nullary` on `tableOfI hEnv`: a bare rule is a `tableOf` δ
    rule — the landed `bare_nullary` case. -/
theorem tableOfI_bare_nullary {E : ResolvedEnv} (hEnv : EnvWfT E) :
    ∀ ρ ∈ tableOfI hEnv, ρ.major = none → ∀ ls, ρ.nargs ls = 0 := by
  intro ρ hρ hm ls
  rcases tableOfI_head_major hEnv ρ hρ with ⟨_, _, _, htb⟩ |
      ⟨_, _, _, _, _, _, hmaj, -, -⟩
  · exact (tableWF_build hEnv).bare_nullary ρ htb hm ls
  · exact Option.noConfusion (hmaj.symm.trans hm)

/-! ## §5 assembly and the Nat wall control -/

/-- `TableCongr` distributes over append — generic in the two tables. The
    team's canonical copy lives in this module (PART 3's `RcicSynTableCongrI`
    consumes it). -/
theorem tableCongr_append {t₁ t₂ : List CRule} (h₁ : TableCongr t₁) (h₂ : TableCongr t₂) :
    TableCongr (t₁ ++ t₂) where
  rhs := by
    intro ρ hρ ls ls₂ ms ms₂ hls hms
    rcases List.mem_append.mp hρ with h | h
    · exact h₁.rhs ρ h hls hms
    · exact h₂.rhs ρ h hls hms
  nargs := by
    intro ρ hρ ls ls₂ hls
    rcases List.mem_append.mp hρ with h | h
    · exact h₁.nargs ρ h hls
    · exact h₂.nargs ρ h hls
  marity := by
    intro ρ hρ d m hm ls ls₂ hls
    rcases List.mem_append.mp hρ with h | h
    · exact h₁.marity ρ h hm hls
    · exact h₂.marity ρ h hm hls

/-- The `TableWF` of `tableOfI hEnv`, taking PART 3's `congr`/`closed` halves
    as hypotheses — the four structural fields are §4. -/
theorem tableWF_tableOfI {E : ResolvedEnv} (hEnv : EnvWfT E)
    (hcongr : TableCongr (tableOfI hEnv))
    (hclosed : ∀ ρ ∈ tableOfI hEnv, ∀ ls ms, ETm.ClosedAt 0 (ρ.rhs ls ms)) :
    TableWF (tableOfI hEnv) where
  congr := hcongr
  closed := hclosed
  rigid := tableOfI_rigid hEnv
  ctor_disjoint := tableOfI_ctor_disjoint hEnv
  bare_unique := tableOfI_bare_unique hEnv
  bare_nullary := tableOfI_bare_nullary hEnv

/-- `TableCongr` for the singleton `natZeroRule` — the rhs `λ³. bvar 1` is
    level-free, so congruence is reflexivity through the `lam`/`bvar`
    constructors. -/
theorem tableCongr_natZero : TableCongr [natZeroRule] where
  rhs := by
    intro ρ hρ _ _ _ _ _ _
    simp only [List.mem_singleton] at hρ; subst hρ
    exact .lam (.lam (.lam (.bvar _)))
  nargs := by
    intro ρ hρ _ _ _
    simp only [List.mem_singleton] at hρ; subst hρ; rfl
  marity := by
    intro ρ hρ _ _ hm
    simp only [List.mem_singleton] at hρ; subst hρ; cases hm; exact fun _ => rfl

/-- `TableCongr` for the landed Nat ι pair. -/
theorem tableCongr_natZeroSucc : TableCongr [natZeroRule, natSuccRule] :=
  tableCongr_append tableCongr_natZero natSuccTable_wf.congr

/-- `TableClosed` for the landed Nat ι pair: zero's `λ³. bvar 1` closes by
    `decide` under `ClosedAt`; succ's is `natSuccTable_wf.closed`. -/
theorem tableClosed_natZeroSucc :
    ∀ ρ ∈ [natZeroRule, natSuccRule], ∀ ls ms,
      ETm.ClosedAt 0 (ρ.rhs ls ms) := by
  intro ρ hρ ls ms
  rcases List.mem_cons.mp hρ with rfl | hρ
  · simp only [natZeroRule, ETm.ClosedAt]
    decide
  · exact natSuccTable_wf.closed ρ hρ ls ms

/-- PART-2 headline on the wall instance: `TableWF (tableOfI natEnvUWfT)` —
    the real Nat env's ι rules `[natZeroRule, natSuccRule]` discharged
    outright (the `congr`/`closed` halves are concrete on the two-rule list). -/
theorem tableWF_nat_tableOfI : TableWF (tableOfI natEnvUWfT) := by
  have htl : tableOfI natEnvUWfT = [natZeroRule, natSuccRule] := by
    have hg : tableOfI natEnvUWfT =
        iotaRulesOf 0 natFamMember [(1, natZeroMember), (2, natSuccMember)]
          3 natRecMemberU ++ tableOfI .empty := tableOfI_group
    rw [hg, iotaRulesOf_nat, tableOfI_empty, List.append_nil]
  rw [htl]
  exact { congr := tableCongr_natZeroSucc
          closed := tableClosed_natZeroSucc
          rigid := htl ▸ tableOfI_rigid natEnvUWfT
          ctor_disjoint := htl ▸ tableOfI_ctor_disjoint natEnvUWfT
          bare_unique := htl ▸ tableOfI_bare_unique natEnvUWfT
          bare_nullary := htl ▸ tableOfI_bare_nullary natEnvUWfT }

#print axioms groupMembersT_lookup
#print axioms groupMembersT_freshE
#print axioms groupMembersT_fst_nodup
#print axioms groupMembersT_ctors_fst_nodup
#print axioms iotaNindices
#print axioms mem_iotaRulesOf
#print axioms iotaRuleOfCtor_spec
#print axioms members_ne_of_mclass_ne
#print axioms tableOfI_head_major
#print axioms head_mem_tableOfI
#print axioms tableOfI_rigid
#print axioms iotaRulesOf_ctor_disjoint
#print axioms tableOfI_ctor_disjoint
#print axioms tableOfI_bare_unique
#print axioms tableOfI_bare_nullary
#print axioms tableCongr_append
#print axioms tableWF_tableOfI
#print axioms tableCongr_natZero
#print axioms tableCongr_natZeroSucc
#print axioms tableClosed_natZeroSucc
#print axioms tableWF_nat_tableOfI

end Rcic.Syn
