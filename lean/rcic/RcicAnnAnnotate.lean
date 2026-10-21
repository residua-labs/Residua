import rcic.RcicAnnErase

/-!
# M3-c2 — annotation: the typed judgment's derivations lift to the copy

The bridge's second half. `RcicAnnErase` erases the copy's derivations into the typed judgment
on `main`'s syntax (`RcicTypedJ`); this module goes back. A derivation of `HasTyT` / `ConvT` in
the erased environment lifts, in ANY well-formed annotated context that erases to its context, to
a derivation on the copy of an annotation of its subject (and type), whenever the environment is
one the copy admits (`AnnEnvA`: well-formed at the concrete ι, the small-index profile, Prop
families eliminating into Prop only, struct groups exempt; the premises of the copy's rows).

Each rule is lifted by lifting its premises and rebuilding the copy's rule. The copy's rules
carry more premises than the typed judgment's (the codomain typings, the right-hand typings of the
congruences, both typings of a type conversion). The copy's metatheory supplies them: regularity,
the endpoints of a conversion, functionality, context conversion, level irrelevance. Two lifts of
one term may differ at the `λ` / `Π` annotations. Annotation coherence (`annCohA`, M3-c0) glues
them: two well-typed types with one erasure are convertible.

ι is the one rule whose lift needs a fact proved later. The copy's ι step reads the annotated
redex (`iotaFnA`), and its rule needs the reduct TYPED at the redex's type: ι subject reduction,
the right-hand typing `ConvA.iota` carries as a named M-001 deviation. At a struct group the rule is
`ConvA.structIota` (W-1 (e)), which carries a conversion to the struct arm's reduct as well. So the
hypothesis is ι subject reduction in its conversion form (`IotaSRA`, W-1 (e-2)): a ι step at a typed
redex is a conversion at the redex's type. Nothing else is assumed. `RcicAnnIotaSR` proves it
(`iotaSRA`) and restates the lift without it (`annHasTyT'`, `annConvT'`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the admitted environment, and ι subject reduction -/

/-- an environment the copy admits under the profile: well-formed at the concrete ι, the
    small-index profile, its Prop families eliminating into Prop only, struct groups exempt (W-1 (e-2):
    `PropElimStructA`; it was `PropElimOnlyA` before). These are the premises of the copy's rows at the
    concrete ι (`sortConvCharA_rec`, `piConvInjA_rec`, `famAppConvInjA_rec`). -/
structure AnnEnvA (E : ResolvedEnvA) : Prop where
  wf : Nonempty (EnvWfA (iotaIfaceA E) E)
  small : SmallIndexProfileA E
  propElim : PropElimStructA E
  /-- no constructor has a function-recursive field: `main`'s ι and kinds are the tree's, which has none
      (R-NoFunRec-1 step 1 (1c-ε3)); the erasure and the bridge read it. -/
  noFun : EnvNoFunA E

/-- ι SUBJECT REDUCTION on the copy at the concrete ι, in its conversion form (W-1 (e-2)): a ι step at a
    typed redex is a conversion at the redex's type, so the reduct keeps the redex's type. `ConvA.iota`
    carries the reduct's typing as a premise (`hrhs`, a named M-001 deviation), and `ConvA.structIota`
    a conversion to the struct arm's reduct besides; the lift of `ConvT.iota` needs the conversion. -/
def IotaSRA (E : ResolvedEnvA) (n : Nat) : Prop :=
  ∀ {Γ : LCtxA} {lhs rhs T : ExprA}, CtxWfA E (iotaIfaceA E) n Γ → iotaFnA E lhs = some rhs →
    HasTyA E (iotaIfaceA E) n Γ lhs T → Nonempty (ConvA E (iotaIfaceA E) n Γ lhs rhs T)

namespace AnnEnvA
variable {E : ResolvedEnvA}

theorem hE (C : AnnEnvA E) : EnvClosedA E := C.wf.elim envWfA_closed
theorem hEL (C : AnnEnvA E) : EnvLevelsA E := C.wf.elim envWfA_levels
theorem hEN (C : AnnEnvA E) : EnvNormClosedA E := C.wf.elim envWfA_normClosed
theorem hENC (C : AnnEnvA E) : EnvNormCtorTypeA E := C.wf.elim envWfA_normCtorType
theorem hENL (C : AnnEnvA E) : EnvNormLevelsA E := C.wf.elim envWfA_normLevels
theorem hI (C : AnnEnvA E) : IotaLiftA (iotaIfaceA E) := iotaFnA_lift C.hE C.hEN
theorem hIS (C : AnnEnvA E) : IotaSubstA (iotaIfaceA E) := iotaFnA_subst C.hE C.hEN
theorem hR (_C : AnnEnvA E) : IotaRecHeadA E (iotaIfaceA E) := iotaFnA_recHead E
theorem hIL (C : AnnEnvA E) : IotaLevelsA (iotaIfaceA E) := iotaFnA_levels C.hEL C.hENL

/-- what erasure reads of ι (`IotaErasesA`; named `hNS` for its callers since W-1 (b′), when it said that ι
    is at no struct group). The `EnvNormEraseA` hypothesis is the `drecD` boundary
    (R-NoDeltaRec-4d-iii): at a `drecD` member the normed and stored constructor types erase
    differently and the ι-correspondence is out of scope. -/
theorem hNS (C : AnnEnvA E) (hn : EnvNormEraseA E) : IotaErasesA E :=
  C.wf.elim fun hW => iotaErasesA_of_envWfA hW C.noFun hn

/-- the semantic environment, at the height valuation `fun _ => 1`. -/
theorem hS (C : AnnEnvA E) (n : Nat) : EnvSemA E (iotaIfaceA E) n (fun _ => 1) :=
  C.wf.elim fun hW => envSemA_of_envWfA_recStruct hW posValA_one C.small C.propElim

end AnnEnvA

/-! ## (2) every member's type, and every body, typed -/

section Members
variable {I : IotaIfaceA}

/-- a well-formed environment types each member's stored type at a sort, in the empty context at
    the member's own universe arity. -/
theorem envWfA_memberTy : {E : ResolvedEnvA} → EnvWfA I E →
    ∀ (r : Nat) (m : CheckedMemberA), E.members r = some m →
      ∃ u, Nonempty (HasTyA E I m.arity [] m.mtypeA (.sort u))
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiomM E r A u hE hfresh hA _ _ => fun r' m' hm' => by
      have hpre := prefixA_extend E r ⟨.axiomM, 0, A, none, 0, none⟩ hfresh
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨u, ⟨hasTyEnvA hpre hA⟩⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        obtain ⟨w, ⟨h⟩⟩ := envWfA_memberTy hE r' m' hm'
        exact ⟨w, ⟨hasTyEnvA hpre h⟩⟩
  | _, .definitionM E r A v u hE hfresh hA _ _ _ _ _ => fun r' m' hm' => by
      have hpre := prefixA_extend E r ⟨.definitionM, 0, A, some v, 0, none⟩ hfresh
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨u, ⟨hasTyEnvA hpre hA⟩⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        obtain ⟨w, ⟨h⟩⟩ := envWfA_memberTy hE r' m' hm'
        exact ⟨w, ⟨hasTyEnvA hpre h⟩⟩
  | _, .theoremM E r A p hE hfresh hA _ _ _ _ _ => fun r' m' hm' => by
      have hpre := prefixA_extend E r ⟨.theoremM, 0, A, some p, 0, none⟩ hfresh
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨.zero, ⟨hasTyEnvA hpre hA⟩⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        obtain ⟨w, ⟨h⟩⟩ := envWfA_memberTy hE r' m' hm'
        exact ⟨w, ⟨hasTyEnvA hpre h⟩⟩
  | _, .opaqueM E r A v u hE hfresh hA _ _ _ _ _ => fun r' m' hm' => by
      have hpre := prefixA_extend E r ⟨.opaqueM, 0, A, some v, 0, none⟩ hfresh
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨u, ⟨hasTyEnvA hpre hA⟩⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        obtain ⟨w, ⟨h⟩⟩ := envWfA_memberTy hE r' m' hm'
        exact ⟨w, ⟨hasTyEnvA hpre h⟩⟩
  | _, .group E f fm u hE _ _ _ hT _ _ cs hfresh => fun r' m' hm' => by
      have hpre := prefixA_groupEnvA hfresh
      rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
      · exact ⟨u, ⟨hasTyEnvA hpre hT⟩⟩
      · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
        have hm : c.member = m' := congrArg Prod.snd hce
        subst hm
        exact ⟨c.u, ⟨hasTyEnvA (prefixA_extend_groupEnvA hfresh) c.hT⟩⟩
      · obtain ⟨w, ⟨h⟩⟩ := envWfA_memberTy hE r' m' hb
        exact ⟨w, ⟨hasTyEnvA hpre h⟩⟩
  | _, .groupRec E f fm u hE _ _ _ hT _ _ cs hfresh _ rec hrf => fun r' m' hm' => by
      have hpreR : PrefixA (groupEnvA E f fm (cs.map GroupCtorA.entry)) (groupRecEnvA cs rec) :=
        prefixA_extend _ _ _ hrf
      have hpre := prefixA_trans (prefixA_groupEnvA hfresh) hpreR
      unfold groupRecEnvA at hm'
      by_cases hr : r' = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact ⟨rec.u, ⟨hasTyEnvA hpreR rec.hT⟩⟩
      · rw [members_extendEnvA_ne _ _ _ hr] at hm'
        rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
        · exact ⟨u, ⟨hasTyEnvA hpre hT⟩⟩
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
          have hm : c.member = m' := congrArg Prod.snd hce
          subst hm
          exact ⟨c.u, ⟨hasTyEnvA (prefixA_trans (prefixA_extend_groupEnvA hfresh) hpreR) c.hT⟩⟩
        · obtain ⟨w, ⟨h⟩⟩ := envWfA_memberTy hE r' m' hb
          exact ⟨w, ⟨hasTyEnvA hpre h⟩⟩

/-- a well-formed environment bounds each member's type levels at its arity
    (R-NoDeltaRec-4d-iii). -/
theorem envWfA_memberLvl : {E : ResolvedEnvA} → EnvWfA I E →
    ∀ (r : Nat) (m : CheckedMemberA), E.members r = some m →
      exprLevelsBoundedA m.arity m.mtypeA = true
  | _, .empty => fun _ _ h => Option.noConfusion h
  | _, .axiomM E r A _ hE hfresh _ _ hlvl => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'; exact hlvl
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_memberLvl hE r' m' hm'
  | _, .definitionM E r A _ _ hE hfresh _ _ _ _ hlvl _ => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'; exact hlvl
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_memberLvl hE r' m' hm'
  | _, .theoremM E r A _ hE hfresh _ _ _ _ hlvl _ => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'; exact hlvl
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_memberLvl hE r' m' hm'
  | _, .opaqueM E r A _ _ hE hfresh _ _ _ _ hlvl _ => fun r' m' hm' => by
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'; exact hlvl
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        exact envWfA_memberLvl hE r' m' hm'
  | _, .group E f fm _ hE _ _ _ _ hlvl _ cs hfresh => fun r' m' hm' => by
      rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
      · exact hlvl
      · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
        have hm : c.member = m' := congrArg Prod.snd hce
        subst hm; exact c.hlvl
      · exact envWfA_memberLvl hE r' m' hb
  | _, .groupRec E f fm _ hE _ _ _ _ hlvl _ cs hfresh _ rec hrf => fun r' m' hm' => by
      unfold groupRecEnvA at hm'
      by_cases hr : r' = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'; exact rec.hlvl
      · rw [members_extendEnvA_ne _ _ _ hr] at hm'
        rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb
        · exact hlvl
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
          have hm : c.member = m' := congrArg Prod.snd hce
          subst hm; exact c.hlvl
        · exact envWfA_memberLvl hE r' m' hb

/-- a well-formed environment types each body at its member's type. Only definitions, theorems
    and opaque constants have bodies, all at arity `0`. -/
theorem envWfA_memberBody : {E : ResolvedEnvA} → EnvWfA I E →
    ∀ (r : Nat) (m : CheckedMemberA) (b : ExprA), E.members r = some m → m.bodyA = some b →
      Nonempty (HasTyA E I m.arity [] b m.mtypeA)
  | _, .empty => fun _ _ _ h => Option.noConfusion h
  | _, .axiomM E r A _ hE hfresh _ _ _ => fun r' m' b hm' hb => by
      have hpre := prefixA_extend E r ⟨.axiomM, 0, A, none, 0, none⟩ hfresh
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        exact Option.noConfusion hb
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        obtain ⟨h⟩ := envWfA_memberBody hE r' m' b hm' hb
        exact ⟨hasTyEnvA hpre h⟩
  | _, .definitionM E r A v _ hE hfresh _ hv _ _ _ _ => fun r' m' b hm' hb => by
      have hpre := prefixA_extend E r ⟨.definitionM, 0, A, some v, 0, none⟩ hfresh
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        cases hb
        exact ⟨hasTyEnvA hpre hv⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        obtain ⟨h⟩ := envWfA_memberBody hE r' m' b hm' hb
        exact ⟨hasTyEnvA hpre h⟩
  | _, .theoremM E r A p hE hfresh _ hp _ _ _ _ => fun r' m' b hm' hb => by
      have hpre := prefixA_extend E r ⟨.theoremM, 0, A, some p, 0, none⟩ hfresh
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        cases hb
        exact ⟨hasTyEnvA hpre hp⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        obtain ⟨h⟩ := envWfA_memberBody hE r' m' b hm' hb
        exact ⟨hasTyEnvA hpre h⟩
  | _, .opaqueM E r A v _ hE hfresh _ hv _ _ _ _ => fun r' m' b hm' hb => by
      have hpre := prefixA_extend E r ⟨.opaqueM, 0, A, some v, 0, none⟩ hfresh
      by_cases hr : r' = r
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        cases hb
        exact ⟨hasTyEnvA hpre hv⟩
      · rw [members_extendEnvA_ne E r _ hr] at hm'
        obtain ⟨h⟩ := envWfA_memberBody hE r' m' b hm' hb
        exact ⟨hasTyEnvA hpre h⟩
  | _, .group E f fm _ hE _ hnobody _ _ _ _ cs hfresh => fun r' m' b hm' hb => by
      rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb'
      · rw [hnobody] at hb; exact Option.noConfusion hb
      · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
        have hm : c.member = m' := congrArg Prod.snd hce
        subst hm
        rw [c.hnobody] at hb; exact Option.noConfusion hb
      · obtain ⟨h⟩ := envWfA_memberBody hE r' m' b hb' hb
        exact ⟨hasTyEnvA (prefixA_groupEnvA hfresh) h⟩
  | _, .groupRec E f fm _ hE _ hnobody _ _ _ _ cs hfresh _ rec hrf => fun r' m' b hm' hb => by
      have hpreR : PrefixA (groupEnvA E f fm (cs.map GroupCtorA.entry)) (groupRecEnvA cs rec) :=
        prefixA_extend _ _ _ hrf
      unfold groupRecEnvA at hm'
      by_cases hr : r' = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm'
        cases hm'
        rw [rec.hnobody] at hb; exact Option.noConfusion hb
      · rw [members_extendEnvA_ne _ _ _ hr] at hm'
        rcases members_groupEnvA _ r' m' hm' with ⟨_, rfl⟩ | hc | hb'
        · rw [hnobody] at hb; exact Option.noConfusion hb
        · obtain ⟨c, _, hce⟩ := List.mem_map.mp hc
          have hm : c.member = m' := congrArg Prod.snd hce
          subst hm
          rw [c.hnobody] at hb; exact Option.noConfusion hb
        · obtain ⟨h⟩ := envWfA_memberBody hE r' m' b hb' hb
          exact ⟨hasTyEnvA (prefixA_trans (prefixA_groupEnvA hfresh) hpreR) h⟩

end Members

/-! ## (3) closed derivations instantiated and weakened -/

section Inst
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- a closed conversion transports to any context (`hasTyClosedWeakenA`'s twin). -/
def convClosedWeakenA (hE : EnvClosedA E) (hI : IotaLiftA I) {a b A : ExprA}
    (hcla : ∀ k, liftA k 1 a = a) (hclb : ∀ k, liftA k 1 b = b) (hclA : ∀ k, liftA k 1 A = A) :
    (Γ : LCtxA) → ConvA E I n [] a b A → ConvA E I n Γ a b A
  | [], h => h
  | d :: Γ, h => by
      have hw := convWeakenA hE hI d (c := 0) (Nat.zero_le _)
        (convClosedWeakenA hE hI hcla hclb hclA Γ h)
      rw [hcla 0, hclb 0, hclA 0] at hw
      exact hw

end Inst

section MemberInst
variable {E : ResolvedEnvA} {n : Nat}

/-- a member's type at bounded levels of its arity, typed at a sort in any context. -/
theorem hasTyA_memberTy_inst (C : AnnEnvA E) {r : Nat} {m : CheckedMemberA}
    (hres : E.members r = some m) {ls : List Level} (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (Γ : LCtxA) :
    ∃ u, Nonempty (HasTyA E (iotaIfaceA E) n Γ (instantiateLevelsA ls m.mtypeA) (.sort u)) := by
  obtain ⟨hW⟩ := C.wf
  obtain ⟨u, ⟨h⟩⟩ := envWfA_memberTy hW r m hres
  have h' : HasTyA E (iotaIfaceA E) n [] (instantiateLevelsA ls m.mtypeA) (.sort (instLevel ls u)) :=
    hasTyA_instLevels C.hEL C.hIL hwf hlen h
  exact ⟨instLevel ls u, ⟨hasTyClosedWeakenA C.hE C.hI
    (liftA_instantiateLevelsA_closed (C.hE r m hres).1 ls) (fun _ => rfl) Γ h'⟩⟩

/-- a member's body at bounded levels of its arity, typed at its type in any context. -/
theorem hasTyA_memberBody_inst (C : AnnEnvA E) {r : Nat} {m : CheckedMemberA} {b : ExprA}
    (hres : E.members r = some m) (hb : m.bodyA = some b) {ls : List Level}
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true) (Γ : LCtxA) :
    Nonempty (HasTyA E (iotaIfaceA E) n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)) := by
  obtain ⟨hW⟩ := C.wf
  obtain ⟨h⟩ := envWfA_memberBody hW r m b hres hb
  have h' : HasTyA E (iotaIfaceA E) n [] (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA) :=
    hasTyA_instLevels C.hEL C.hIL hwf hlen h
  exact ⟨hasTyClosedWeakenA C.hE C.hI (liftA_instantiateLevelsA_closed ((C.hE r m hres).2 b hb) ls)
    (liftA_instantiateLevelsA_closed (C.hE r m hres).1 ls) Γ h'⟩

/-- LEVEL IRRELEVANCE at a member's type: two `=ₙ` bounded instantiations are convertible, in any
    context, at a sort. -/
theorem convA_memberTy_levels (C : AnnEnvA E) {r : Nat} {m : CheckedMemberA}
    (hres : E.members r = some m) {ls ls' : List Level} (hlen : ls.length = m.arity)
    (hlen' : ls'.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls') (Γ : LCtxA) :
    ∃ u, Nonempty (ConvA E (iotaIfaceA E) n Γ (instantiateLevelsA ls m.mtypeA)
      (instantiateLevelsA ls' m.mtypeA) (.sort u)) := by
  obtain ⟨hW⟩ := C.wf
  obtain ⟨u, ⟨h⟩⟩ := envWfA_memberTy hW r m hres
  obtain ⟨c⟩ := convA_levelIrr_wf C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hEL C.hIL hwf hwf' hlen
    hlen' heq .nil h
  have hcl := (C.hE r m hres).1
  exact ⟨instLevel ls u, ⟨convClosedWeakenA C.hE C.hI (liftA_instantiateLevelsA_closed hcl ls)
    (liftA_instantiateLevelsA_closed hcl ls') (fun _ => rfl) Γ c⟩⟩

end MemberInst

/-! ## (4) the context's lookups typed -/

section Lookup
variable {E : ResolvedEnvA} {n : Nat}

theorem ctxWfA_lookupType_ty (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    {i : Nat} {A : ExprA} (h : lookupTypeA Γ i = some A) :
    ∃ u, Nonempty (HasTyA E (iotaIfaceA E) n Γ A (.sort u)) := by
  have hb := (substTyA_id C.hE C.hI hΓ).ty i A h
  rw [SubstA.id_apply, substA_id] at hb
  obtain ⟨u, hu⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ hb
  exact ⟨u, ⟨hu⟩⟩

theorem ctxWfA_lookupValue_ty (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    {i : Nat} {A v : ExprA} (hty : lookupTypeA Γ i = some A) (hval : lookupValueA Γ i = some v) :
    Nonempty (HasTyA E (iotaIfaceA E) n Γ v A) := by
  have hc := (substTyA_id C.hE C.hI hΓ).val i A v hty hval
  rw [SubstA.id_apply, substA_id, substA_id] at hc
  exact ⟨convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ hc⟩

end Lookup

/-! ## (5) erasure inverted at lookups and literals -/

theorem lookupTypeA_of_erase {Γ : LCtxA} {i : Nat} {A : Expr Nat}
    (h : lookupType (eraseCtx Γ) i = some A) : ∃ AA, lookupTypeA Γ i = some AA ∧ erase AA = A := by
  rw [lookupType_eraseCtx] at h
  cases hl : lookupTypeA Γ i with
  | none => rw [hl] at h; exact Option.noConfusion h
  | some AA => rw [hl] at h; exact ⟨AA, rfl, Option.some.inj h⟩

theorem lookupValueA_of_erase {Γ : LCtxA} {i : Nat} {v : Expr Nat}
    (h : lookupValue (eraseCtx Γ) i = some v) : ∃ vA, lookupValueA Γ i = some vA ∧ erase vA = v := by
  rw [lookupValue_eraseCtx] at h
  cases hl : lookupValueA Γ i with
  | none => rw [hl] at h; exact Option.noConfusion h
  | some vA => rw [hl] at h; exact ⟨vA, rfl, Option.some.inj h⟩

/-- a literal's expansion has no binder, so its only annotation is itself. -/
theorem erase_eq_natExpand : (t : Nat) → {e : ExprA} → erase e = natExpand t → e = natExpandA t
  | 0, _, h => erase_eq_const (r := 1) (ls := []) h
  | t + 1, _, h => by
      obtain ⟨f', a', rfl, hf, ha⟩ := erase_eq_app (f := .const 2 []) (a := natExpand t) h
      rw [erase_eq_const hf, erase_eq_natExpand t ha]
      rfl

/-! ## (6) retyping across one erasure (annotation coherence at types) -/

section Retype
variable {E : ResolvedEnvA} {n : Nat}

/-- two types with one erasure, each typed at a sort, are type-convertible. -/
theorem tyConvA_of_erase (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    {A B : ExprA} {l l' : Level} (he : erase A = erase B)
    (hA : HasTyA E (iotaIfaceA E) n Γ A (.sort l)) (hB : HasTyA E (iotaIfaceA E) n Γ B (.sort l')) :
    Nonempty (TyConvA E (iotaIfaceA E) n Γ A B) := by
  obtain ⟨c⟩ := annCohA C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one A hΓ he hA hB
  exact ⟨tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ c⟩

theorem hasTyA_reannot (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    {e T A : ExprA} {l : Level} (h : HasTyA E (iotaIfaceA E) n Γ e T) (he : erase T = erase A)
    (hA : HasTyA E (iotaIfaceA E) n Γ A (.sort l)) : Nonempty (HasTyA E (iotaIfaceA E) n Γ e A) := by
  obtain ⟨_, hs⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ h
  obtain ⟨t⟩ := tyConvA_of_erase C hΓ he hs hA
  exact ⟨hasTyA_of_tyConvA h t⟩

theorem convA_reannot (C : AnnEnvA E) {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    {a b T A : ExprA} {l : Level} (h : ConvA E (iotaIfaceA E) n Γ a b T) (he : erase T = erase A)
    (hA : HasTyA E (iotaIfaceA E) n Γ A (.sort l)) : Nonempty (ConvA E (iotaIfaceA E) n Γ a b A) := by
  obtain ⟨_, hs⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ h)
  obtain ⟨t⟩ := tyConvA_of_erase C hΓ he hs hA
  exact ⟨convA_of_tyConvA h t⟩

end Retype

/-! ## (7) a concrete ι step is a declarative one -/

/-- every value of the concrete ι off a struct group is a declarative ι step: the redex is a recursor
    spine at its major, below its major a recursor spine never head-steps, and off a struct group the
    head step there is ι's (at a struct group it is the struct arm's, W-1 (e)). -/
theorem iotaRelA_of_fn {E : ResolvedEnvA} {Γ : LCtxA} {e e' : ExprA} (hns : iotaAtStructA E e = false)
    (h : iotaFnA E e = some e') : (iotaIfaceA E).rel E Γ e e' := by
  obtain ⟨s, c, g, hs, hc, hg, _⟩ := iotaFnA_some h
  have hsp := recSpineA_some hs
  have hst := iotaAtStructA_of_layers hs hc hg
  obtain ⟨hrm, _⟩ := iotaGroupA_some hg
  obtain ⟨r, ls, m, hhead, hres, hcls, hlen⟩ := iotaFnA_recHead E e e' h
  rw [hsp] at hhead hlen
  simp only [ExprA.const.injEq] at hhead
  obtain ⟨rfl, rfl⟩ := hhead
  rw [hres] at hrm
  injection hrm with hrm
  have he : foldAppsA (.const s.recRef s.ls) (s.preMajor ++ [s.major]) = e := by
    have := foldAppsA_appsSpineA e
    rw [hsp] at this
    exact this
  rw [foldAppsA_snoc] at he
  subst he
  simp only [List.length_append, List.length_singleton] at hlen
  exact iotaRelA_of (foldAppsA_const_not_lam _ _ _)
    (hStepFnA_recSpine_below Γ hres hcls s.ls s.preMajor (by omega))
    (by rw [structHeadA_of_spine (by rw [foldAppsA_const_head]) hres, hrm, ← hst, hns]) h

/-! ## (8) THE ANNOTATION

Every arm makes its recursive calls before it substitutes anything: a substitution rewrites the
premises' types, and the recursion is structural on the premises. -/

theorem eraseCtx_assumption {ΓA : LCtxA} {Γ : LCtx} {AA : ExprA} {A : Expr Nat}
    (hA : erase AA = A) (h : eraseCtx ΓA = Γ) : eraseCtx (.assumption AA :: ΓA) = .assumption A :: Γ := by
  subst hA h; rfl

theorem eraseCtx_letBinding {ΓA : LCtxA} {Γ : LCtx} {AA vA : ExprA} {A v : Expr Nat}
    (hA : erase AA = A) (hv : erase vA = v) (h : eraseCtx ΓA = Γ) :
    eraseCtx (.letBinding AA vA :: ΓA) = .letBinding A v :: Γ := by
  subst hA hv h; rfl

section Annotate
variable {E : ResolvedEnvA} {n : Nat}

mutual

/-- ANNOTATION OF TYPING: a typing of the typed judgment in the erased environment lifts, in any
    well-formed annotated context erasing to its context, to a typing on the copy of an annotation
    of its subject at an annotation of its type. -/
theorem annHasTyT (C : AnnEnvA E) (hSR : IotaSRA E n) (hn : EnvNormEraseA E) :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT (eraseEnv E) n Γ e T →
    ∀ {ΓA : LCtxA}, CtxWfA E (iotaIfaceA E) n ΓA → eraseCtx ΓA = Γ →
      ∃ eA TA, erase eA = e ∧ erase TA = T ∧ Nonempty (HasTyA E (iotaIfaceA E) n ΓA eA TA)
  | _, _, _, .sort _ l, ΓA, _, _ => ⟨.sort l, .sort (.succ l), rfl, rfl, ⟨.sort ΓA l⟩⟩
  | _, _, _, .bvar _ i _ h, ΓA, hΓ, hctx => by
      subst hctx
      obtain ⟨AA, hAA, rfl⟩ := lookupTypeA_of_erase h
      obtain ⟨u, ⟨hu⟩⟩ := ctxWfA_lookupType_ty C hΓ hAA
      exact ⟨.bvar i, AA, rfl, rfl, ⟨.bvar ΓA i AA u hAA hu⟩⟩
  | _, _, _, .const _ r ls _ hres hlen hwf, ΓA, _, _ => by
      obtain ⟨mA, hresA, rfl⟩ := members_of_eraseEnv hres
      obtain ⟨u, ⟨hT⟩⟩ := hasTyA_memberTy_inst C hresA hlen hwf ΓA
      exact ⟨.const r ls, instantiateLevelsA ls mA.mtypeA, rfl, erase_instantiateLevelsA _ _,
        ⟨.const ΓA r ls mA u hresA hlen hwf hT⟩⟩
  | _, _, _, .pi _ _ u _ v hA hB, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyT C hSR hn hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨BA, SB, hBe, hSBe, ⟨tB⟩⟩ :=
        annHasTyT C hSR hn hB (.assumption hΓ tA) (eraseCtx_assumption hAe hctx)
      obtain rfl := erase_eq_sort hSBe
      subst hAe hBe hctx
      exact ⟨.pi AA u BA v, .sort (.imax u v), rfl, rfl, ⟨.pi ΓA AA u BA v tA tB⟩⟩
  | _, _, _, .lam _ _ u _ _ hA hbody, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyT C hSR hn hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.assumption AA :: ΓA) := .assumption hΓ tA
      obtain ⟨bA, BA, hbe, hBe, ⟨tb⟩⟩ := annHasTyT C hSR hn hbody hΓ' (eraseCtx_assumption hAe hctx)
      subst hAe hbe hBe hctx
      obtain ⟨v, tB⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ' tb
      exact ⟨.lam AA u bA, .pi AA u BA v, rfl, rfl, ⟨.lam ΓA AA u bA BA v tA tB tb⟩⟩
  | _, _, _, .app _ _ _ _ _ hf ha, ΓA, hΓ, hctx => by
      obtain ⟨fA, TfA, hfe, hTf, ⟨tf⟩⟩ := annHasTyT C hSR hn hf hΓ hctx
      obtain ⟨aA, TaA, hae, hTa, ⟨ta⟩⟩ := annHasTyT C hSR hn ha hΓ hctx
      subst hfe hae hctx
      obtain ⟨AA, u, BA, v, rfl, hAe, rfl⟩ := erase_eq_pi hTf
      obtain ⟨_, ts⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ tf
      obtain ⟨hAu, hBv⟩ := hasTyA_pi_parts ts
      obtain ⟨ta'⟩ := hasTyA_reannot C hΓ ta (hTa.trans hAe.symm) hAu
      have hTy : HasTyA E (iotaIfaceA E) n ΓA (instantiate0A aA BA) (.sort v) :=
        hasTyA_inst0' C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hBv ta'
      exact ⟨.app fA aA, instantiate0A aA BA, rfl, erase_instantiate0A _ _,
        ⟨.app ΓA fA aA AA BA u v v hBv hTy tf ta'⟩⟩
  | _, _, _, .letE _ _ u _ _ _ hA hv hb, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyT C hSR hn hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨vA, TvA, hve, hTv, ⟨tv⟩⟩ := annHasTyT C hSR hn hv hΓ hctx
      obtain ⟨tv'⟩ := hasTyA_reannot C hΓ tv (hTv.trans hAe.symm) tA
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.letBinding AA vA :: ΓA) := .letBinding hΓ tA tv'
      obtain ⟨bA, BA, hbe, hBe, ⟨tb⟩⟩ :=
        annHasTyT C hSR hn hb hΓ' (eraseCtx_letBinding hAe hve hctx)
      subst hAe hve hbe hBe hctx
      obtain ⟨w, tBw⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ' tb
      have hTy : HasTyA E (iotaIfaceA E) n ΓA (instantiate0A vA BA) (.sort w) :=
        hasTyA_inst0Let C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ tBw tv'
      exact ⟨.letE AA vA bA, instantiate0A vA BA, rfl, erase_instantiate0A _ _,
        ⟨.letE ΓA AA u w vA BA bA tA tv' hTy tb⟩⟩
  | _, _, _, .lit _ t _ hexp, ΓA, hΓ, hctx => by
      obtain ⟨eA, TA, he, hTe, ⟨te⟩⟩ := annHasTyT C hSR hn hexp hΓ hctx
      subst hTe
      obtain rfl := erase_eq_natExpand t he
      exact ⟨.lit t, TA, rfl, rfl, ⟨.lit ΓA t TA te⟩⟩
  | _, _, _, .conv _ _ _ _ _ h hc, ΓA, hΓ, hctx => by
      obtain ⟨eA, TeA, hee, hTe, ⟨te⟩⟩ := annHasTyT C hSR hn h hΓ hctx
      obtain ⟨AA, BA, SA, hAe, hBe, hSe, ⟨c⟩⟩ := annConvT C hSR hn hc hΓ hctx
      subst hee hBe hctx
      obtain rfl := erase_eq_sort hSe
      have tAA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ c
      obtain ⟨te'⟩ := hasTyA_reannot C hΓ te (hTe.trans hAe.symm) tAA
      exact ⟨eA, BA, rfl, rfl, ⟨hasTyA_of_tyConvA te' (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ c)⟩⟩

/-- ANNOTATION OF CONVERSION: a conversion of the typed judgment in the erased environment lifts,
    in any well-formed annotated context erasing to its context, to a conversion on the copy
    between annotations of its two sides at an annotation of its type. -/
theorem annConvT (C : AnnEnvA E) (hSR : IotaSRA E n) (hn : EnvNormEraseA E) :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvT (eraseEnv E) n Γ a b T →
    ∀ {ΓA : LCtxA}, CtxWfA E (iotaIfaceA E) n ΓA → eraseCtx ΓA = Γ →
      ∃ aA bA TA, erase aA = a ∧ erase bA = b ∧ erase TA = T ∧
        Nonempty (ConvA E (iotaIfaceA E) n ΓA aA bA TA)
  | _, _, _, _, .refl _ _ _ h, ΓA, hΓ, hctx => by
      obtain ⟨aA, TA, hae, hTe, ⟨ta⟩⟩ := annHasTyT C hSR hn h hΓ hctx
      exact ⟨aA, aA, TA, hae, hae, hTe, ⟨.refl ΓA aA TA ta⟩⟩
  | _, _, _, _, .symm _ _ _ _ h, ΓA, hΓ, hctx => by
      obtain ⟨aA, bA, TA, hae, hbe, hTe, ⟨c⟩⟩ := annConvT C hSR hn h hΓ hctx
      exact ⟨bA, aA, TA, hbe, hae, hTe, ⟨.symm ΓA aA bA TA c⟩⟩
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, ΓA, hΓ, hctx => by
      obtain ⟨aA, bA, TA, hae, hbe, hTe, ⟨c1⟩⟩ := annConvT C hSR hn h1 hΓ hctx
      obtain ⟨bA', cA, TA', hb', hce, hT', ⟨c2⟩⟩ := annConvT C hSR hn h2 hΓ hctx
      have tb := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ c1
      have tb' := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ c2
      obtain ⟨cbb⟩ := annCohA C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one bA hΓ
        (hbe.trans hb'.symm) tb tb'
      obtain ⟨_, ts⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ tb
      obtain ⟨c2'⟩ := convA_reannot C hΓ c2 (hT'.trans hTe.symm) ts
      exact ⟨aA, cA, TA, hae, hce, hTe, ⟨.trans ΓA aA bA cA TA c1 (.trans ΓA bA bA' cA TA cbb c2')⟩⟩
  | _, _, _, _, .beta _ _ _ _ _ u hA hbody harg, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyT C hSR hn hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.assumption AA :: ΓA) := .assumption hΓ tA
      obtain ⟨bA, BA, hbe, hBe, ⟨tb⟩⟩ := annHasTyT C hSR hn hbody hΓ' (eraseCtx_assumption hAe hctx)
      obtain ⟨xA, TxA, hxe, hTx, ⟨tx⟩⟩ := annHasTyT C hSR hn harg hΓ hctx
      subst hAe hbe hBe hxe hctx
      obtain ⟨tx'⟩ := hasTyA_reannot C hΓ tx hTx tA
      have hred := hasTyA_inst0' C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ tb tx'
      exact ⟨.app (.lam AA u bA) xA, instantiate0A xA bA, instantiate0A xA BA, rfl,
        erase_instantiate0A _ _, erase_instantiate0A _ _, ⟨.beta ΓA AA u bA xA BA tA tb tx' hred⟩⟩
  | _, _, _, _, .zeta _ _ _ _ _ u hA hv hb, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyT C hSR hn hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨vA, TvA, hve, hTv, ⟨tv⟩⟩ := annHasTyT C hSR hn hv hΓ hctx
      obtain ⟨tv'⟩ := hasTyA_reannot C hΓ tv (hTv.trans hAe.symm) tA
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.letBinding AA vA :: ΓA) := .letBinding hΓ tA tv'
      obtain ⟨bA, BA, hbe, hBe, ⟨tb⟩⟩ :=
        annHasTyT C hSR hn hb hΓ' (eraseCtx_letBinding hAe hve hctx)
      subst hAe hve hbe hBe hctx
      have hred := hasTyA_inst0Let C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ tb tv'
      exact ⟨.letE AA vA bA, instantiate0A vA bA, instantiate0A vA BA, rfl,
        erase_instantiate0A _ _, erase_instantiate0A _ _, ⟨.zeta ΓA AA vA bA BA u tA tv' tb hred⟩⟩
  | _, _, _, _, .zetaLocal _ i _ _ hval hty _, ΓA, hΓ, hctx => by
      subst hctx
      obtain ⟨vA, hvA, rfl⟩ := lookupValueA_of_erase hval
      obtain ⟨AA, hAA, rfl⟩ := lookupTypeA_of_erase hty
      obtain ⟨tv⟩ := ctxWfA_lookupValue_ty C hΓ hAA hvA
      exact ⟨.bvar i, vA, AA, rfl, rfl, rfl, ⟨.zetaLocal ΓA i AA vA hvA hAA tv⟩⟩
  | _, _, _, _, .delta _ r ls _ b hres hbody htr hlen hwf _, ΓA, _, _ => by
      obtain ⟨mA, hresA, rfl⟩ := members_of_eraseEnv hres
      obtain ⟨bA, hbA, rfl⟩ : ∃ bA, mA.bodyA = some bA ∧ erase bA = b := by
        cases hb' : mA.bodyA with
        | none =>
            have : (eraseMember mA).body = none := by
              show mA.bodyA.map erase = none
              rw [hb']; rfl
            rw [this] at hbody
            exact Option.noConfusion hbody
        | some bA =>
            have : (eraseMember mA).body = some (erase bA) := by
              show mA.bodyA.map erase = some (erase bA)
              rw [hb']; rfl
            rw [this] at hbody
            exact ⟨bA, rfl, Option.some.inj hbody⟩
      obtain ⟨tb⟩ := hasTyA_memberBody_inst C hresA hbA hlen hwf ΓA
      exact ⟨.const r ls, instantiateLevelsA ls bA, instantiateLevelsA ls mA.mtypeA, rfl,
        erase_instantiateLevelsA _ _, erase_instantiateLevelsA _ _,
        ⟨.delta ΓA r ls mA bA hresA hbA htr hlen hwf tb⟩⟩
  | _, _, _, _, .iota _ _ _ _ h hlhs _, ΓA, hΓ, hctx => by
      obtain ⟨lA, TA, hle, hTe, ⟨tl⟩⟩ := annHasTyT C hSR hn hlhs hΓ hctx
      subst hle
      obtain ⟨hW⟩ := C.wf
      obtain ⟨rA, hfn, rfl⟩ := iotaFnA_of_derivedIota hW hn h
      exact ⟨lA, rA, TA, rfl, rfl, hTe, hSR hΓ hfn tl⟩
  | _, _, _, _, .lit _ t _ _ h hexp, ΓA, hΓ, hctx => by
      obtain ⟨eA, TA, he, hTe, ⟨te⟩⟩ := annHasTyT C hSR hn hexp hΓ hctx
      cases h
      obtain rfl := erase_eq_natExpand t he
      exact ⟨.lit t, natExpandA t, TA, rfl, erase_natExpandA t, hTe, ⟨.lit ΓA t TA te⟩⟩
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, ΓA, hΓ, hctx => by
      obtain ⟨fA, gA, TfA, hfe, hge, hTf, ⟨c1⟩⟩ := annConvT C hSR hn h1 hΓ hctx
      obtain ⟨aA, bA, TaA, hae, hbe, hTa, ⟨c2⟩⟩ := annConvT C hSR hn h2 hΓ hctx
      subst hfe hge hae hbe hctx
      obtain ⟨AA, u, BA, v, rfl, hAe, rfl⟩ := erase_eq_pi hTf
      have tf := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ c1
      obtain ⟨_, ts⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ tf
      obtain ⟨hAu, hBv⟩ := hasTyA_pi_parts ts
      obtain ⟨c2'⟩ := convA_reannot C hΓ c2 (hTa.trans hAe.symm) hAu
      have tg := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ c1
      have tb := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ c2'
      have hBb : HasTyA E (iotaIfaceA E) n ΓA (instantiate0A bA BA) (.sort v) :=
        hasTyA_inst0' C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hBv tb
      have happ : HasTyA E (iotaIfaceA E) n ΓA (.app gA bA) (instantiate0A bA BA) :=
        .app ΓA gA bA AA BA u v v hBv hBb tg tb
      have cB : ConvA E (iotaIfaceA E) n ΓA (instantiate0A bA BA) (instantiate0A aA BA) (.sort v) :=
        hasTyA_func0 C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hBv (.symm _ _ _ _ c2') hAu
      have hrt := hasTyA_of_tyConvA happ (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cB)
      exact ⟨.app fA aA, .app gA bA, instantiate0A aA BA, rfl, rfl, erase_instantiate0A _ _,
        ⟨.app ΓA fA gA aA bA AA BA u v c1 c2' hBv hrt⟩⟩
  | _, _, _, _, .lam _ _ _ _ _ _ u hA hb, ΓA, hΓ, hctx => by
      obtain ⟨AA, AA', SA, hAe, hA'e, hSe, ⟨cA⟩⟩ := annConvT C hSR hn hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cA
      have tA' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ cA
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.assumption AA :: ΓA) := .assumption hΓ tA
      obtain ⟨bA, bA', BA, hbe, hb'e, hBe, ⟨cb⟩⟩ :=
        annConvT C hSR hn hb hΓ' (eraseCtx_assumption hAe hctx)
      subst hAe hA'e hbe hb'e hBe hctx
      have tb' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ' cb
      obtain ⟨v, tB⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ'
        (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ' cb)
      have K : CtxConvA E (iotaIfaceA E) n (.assumption AA :: ΓA) (.assumption AA' :: ΓA) :=
        .assumption (ctxConvA_refl ΓA) ⟨tA⟩ ⟨tA'⟩ ⟨cA⟩
      have hRT := iotaRecHeadTypedA_of C.hR
      obtain ⟨tb''⟩ := hasTyA_ctxConv C.hE C.hI hRT K tb'
      obtain ⟨tB'⟩ := hasTyA_ctxConv C.hE C.hI hRT K tB
      have hlam : HasTyA E (iotaIfaceA E) n ΓA (.lam AA' u bA') (.pi AA' u BA v) :=
        .lam ΓA AA' u bA' BA v tA' tB' tb''
      have cpi : ConvA E (iotaIfaceA E) n ΓA (.pi AA' u BA v) (.pi AA u BA v) (.sort (.imax u v)) :=
        .pi ΓA AA' AA BA BA u u v v (eqNA_refl u) (eqNA_refl v) (.symm _ _ _ _ cA)
          (.refl _ _ _ tB') (.pi ΓA AA u BA v tA tB)
      have hrt := hasTyA_of_tyConvA hlam (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cpi)
      exact ⟨.lam AA u bA, .lam AA' u bA', .pi AA u BA v, rfl, rfl, rfl,
        ⟨.lam ΓA AA AA' bA bA' BA u u v (eqNA_refl u) cA cb hrt⟩⟩
  | _, _, _, _, .pi _ _ _ _ _ u v hA hB, ΓA, hΓ, hctx => by
      obtain ⟨AA, AA', SA, hAe, hA'e, hSe, ⟨cA⟩⟩ := annConvT C hSR hn hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cA
      have tA' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ cA
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.assumption AA :: ΓA) := .assumption hΓ tA
      obtain ⟨BA, BA', SB, hBe, hB'e, hSBe, ⟨cB⟩⟩ :=
        annConvT C hSR hn hB hΓ' (eraseCtx_assumption hAe hctx)
      obtain rfl := erase_eq_sort hSBe
      subst hAe hA'e hBe hB'e hctx
      have tB' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ' cB
      have K : CtxConvA E (iotaIfaceA E) n (.assumption AA :: ΓA) (.assumption AA' :: ΓA) :=
        .assumption (ctxConvA_refl ΓA) ⟨tA⟩ ⟨tA'⟩ ⟨cA⟩
      obtain ⟨tB''⟩ := hasTyA_ctxConv C.hE C.hI (iotaRecHeadTypedA_of C.hR) K tB'
      have hrt : HasTyA E (iotaIfaceA E) n ΓA (.pi AA' u BA' v) (.sort (.imax u v)) :=
        .pi ΓA AA' u BA' v tA' tB''
      exact ⟨.pi AA u BA v, .pi AA' u BA' v, .sort (.imax u v), rfl, rfl, rfl,
        ⟨.pi ΓA AA AA' BA BA' u u v v (eqNA_refl u) (eqNA_refl v) cA cB hrt⟩⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ u hA hv hb, ΓA, hΓ, hctx => by
      obtain ⟨AA, AA', SA, hAe, hA'e, hSe, ⟨cA⟩⟩ := annConvT C hSR hn hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cA
      have tA' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ cA
      obtain ⟨vA, vA', TvA, hve, hv'e, hTv, ⟨cv⟩⟩ := annConvT C hSR hn hv hΓ hctx
      obtain ⟨cv'⟩ := convA_reannot C hΓ cv (hTv.trans hAe.symm) tA
      have tv := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cv'
      have tv' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ cv'
      have tv'A' := hasTyA_of_tyConvA tv' (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cA)
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.letBinding AA vA :: ΓA) := .letBinding hΓ tA tv
      obtain ⟨bA, bA', BA, hbe, hb'e, hBe, ⟨cb⟩⟩ :=
        annConvT C hSR hn hb hΓ' (eraseCtx_letBinding hAe hve hctx)
      subst hAe hA'e hve hv'e hbe hb'e hBe hctx
      have hRT := iotaRecHeadTypedA_of C.hR
      have K' : CtxConvA E (iotaIfaceA E) n (.letBinding AA vA :: ΓA) (.letBinding AA' vA' :: ΓA) :=
        .letBinding (ctxConvA_refl ΓA) ⟨tA⟩ ⟨tA'⟩ ⟨cA⟩ ⟨tv'A'⟩ ⟨cv'⟩
      obtain ⟨tb''⟩ := hasTyA_ctxConv C.hE C.hI hRT K' (convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ' cb)
      obtain ⟨s, tBs⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ'
        (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ' cb)
      obtain ⟨tBs'⟩ := hasTyA_ctxConv C.hE C.hI hRT K' tBs
      have hlet : HasTyA E (iotaIfaceA E) n ΓA (.letE AA' vA' bA') (instantiate0A vA' BA) :=
        .letE ΓA AA' u s vA' BA bA' tA' tv'A' (hasTyA_inst0Let C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ tBs' tv'A') tb''
      have cBv : ConvA E (iotaIfaceA E) n ΓA (instantiate0A vA' BA) (instantiate0A vA BA) (.sort s) :=
        convA_inst0Let_func C.hE C.hI C.hR C.hIS hΓ tBs tv' (.symm _ _ _ _ cv') tv (.refl ΓA vA AA tv)
          (.symm _ _ _ _ cv')
      have hrt := hasTyA_of_tyConvA hlet (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cBv)
      exact ⟨.letE AA vA bA, .letE AA' vA' bA', instantiate0A vA BA, rfl, rfl, erase_instantiate0A _ _,
        ⟨.letE ΓA AA AA' vA vA' bA bA' BA u cA cv' cb hrt⟩⟩
  | _, _, _, _, .sorts _ l₁ l₂ h, ΓA, _, _ =>
      ⟨.sort l₁, .sort l₂, .sort (.succ l₁), rfl, rfl, rfl, ⟨.sorts ΓA l₁ l₂ h⟩⟩
  | _, _, _, _, .consts _ r ls ls' _ hres hlen hwf hwf' h, ΓA, hΓ, _ => by
      obtain ⟨mA, hresA, rfl⟩ := members_of_eraseEnv hres
      have hlen' : ls'.length = mA.arity := (eqNList_length ls ls' h).symm.trans hlen
      obtain ⟨u', ⟨tT'⟩⟩ := hasTyA_memberTy_inst C hresA hlen' hwf' ΓA
      have hc' : HasTyA E (iotaIfaceA E) n ΓA (.const r ls') (instantiateLevelsA ls' mA.mtypeA) :=
        .const ΓA r ls' mA u' hresA hlen' hwf' tT'
      obtain ⟨_, ⟨cT⟩⟩ := convA_memberTy_levels C hresA hlen hlen' hwf hwf' h ΓA
      have hrt := hasTyA_of_tyConvA hc' (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ (.symm _ _ _ _ cT))
      exact ⟨.const r ls, .const r ls', instantiateLevelsA ls mA.mtypeA, rfl, rfl,
        erase_instantiateLevelsA _ _, ⟨.consts ΓA r ls ls' mA hresA hlen hwf hwf' h hrt⟩⟩
  | _, _, _, _, .eta _ _ _ _ h, ΓA, hΓ, hctx => by
      obtain ⟨fA, TfA, hfe, hTf, ⟨tf⟩⟩ := annHasTyT C hSR hn h hΓ hctx
      subst hfe hctx
      obtain ⟨AA, u, BA, v, rfl, rfl, rfl⟩ := erase_eq_pi hTf
      obtain ⟨_, ts⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ tf
      obtain ⟨hAu, hBv⟩ := hasTyA_pi_parts ts
      have hbody := hasTyA_eta_body C.hE C.hI hAu hBv tf
      have hrt : HasTyA E (iotaIfaceA E) n ΓA (.lam AA u (.app (liftA 0 1 fA) (.bvar 0)))
          (.pi AA u BA v) := .lam ΓA AA u _ BA v hAu hBv hbody
      refine ⟨.lam AA u (.app (liftA 0 1 fA) (.bvar 0)), fA, .pi AA u BA v, ?_, rfl, rfl,
        ⟨.eta ΓA fA AA BA u v tf hrt⟩⟩
      show Expr.lam (erase AA) (.app (erase (liftA 0 1 fA)) (.bvar 0)) = _
      rw [erase_liftA]
  | _, _, _, _, .irr _ _ _ _ hP hp hq, ΓA, hΓ, hctx => by
      obtain ⟨PA, SP, hPe, hSe, ⟨tP⟩⟩ := annHasTyT C hSR hn hP hΓ hctx
      obtain ⟨pA, TpA, hpe, hTp, ⟨tp⟩⟩ := annHasTyT C hSR hn hp hΓ hctx
      obtain ⟨qA, TqA, hqe, hTq, ⟨tq⟩⟩ := annHasTyT C hSR hn hq hΓ hctx
      subst hpe hqe hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨tp'⟩ := hasTyA_reannot C hΓ tp (hTp.trans hPe.symm) tP
      obtain ⟨tq'⟩ := hasTyA_reannot C hΓ tq (hTq.trans hPe.symm) tP
      exact ⟨pA, qA, PA, rfl, rfl, hPe, ⟨.irr ΓA PA pA qA tP tp' tq'⟩⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, ΓA, hΓ, hctx => by
      obtain ⟨aA, bA, TA, hae, hbe, hTe, ⟨c⟩⟩ := annConvT C hSR hn h hΓ hctx
      obtain ⟨AA, AA', SA, hAe, hA'e, hSe, ⟨cA⟩⟩ := annConvT C hSR hn hA hΓ hctx
      subst hae hbe hA'e hctx
      obtain rfl := erase_eq_sort hSe
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cA
      obtain ⟨c'⟩ := convA_reannot C hΓ c (hTe.trans hAe.symm) tA
      exact ⟨aA, bA, AA', rfl, rfl, rfl,
        ⟨convA_of_tyConvA c' (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cA)⟩⟩

end

/-- a well-formed typed context has a well-formed annotation. -/
theorem annCtxWfT (C : AnnEnvA E) (hSR : IotaSRA E n) (hn : EnvNormEraseA E) :
    {Γ : LCtx} → CtxWfT (eraseEnv E) n Γ →
      ∃ ΓA, eraseCtx ΓA = Γ ∧ Nonempty (CtxWfA E (iotaIfaceA E) n ΓA)
  | _, .nil => ⟨[], rfl, ⟨.nil⟩⟩
  | _, .assumption _ _ _ hΓ hA => by
      obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT C hSR hn hΓ
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyT C hSR hn hA hΓA hctx
      obtain rfl := erase_eq_sort hSe
      exact ⟨.assumption AA :: ΓA, eraseCtx_assumption hAe hctx, ⟨.assumption hΓA tA⟩⟩
  | _, .letBinding _ _ _ _ hΓ hA hv => by
      obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT C hSR hn hΓ
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyT C hSR hn hA hΓA hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨vA, TvA, hve, hTv, ⟨tv⟩⟩ := annHasTyT C hSR hn hv hΓA hctx
      obtain ⟨tv'⟩ := hasTyA_reannot C hΓA tv (hTv.trans hAe.symm) tA
      exact ⟨.letBinding AA vA :: ΓA, eraseCtx_letBinding hAe hve hctx, ⟨.letBinding hΓA tA tv'⟩⟩

end Annotate

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.envWfA_memberTy
#print axioms Rcic.Declarative.Ann.envWfA_memberBody
#print axioms Rcic.Declarative.Ann.iotaRelA_of_fn
#print axioms Rcic.Declarative.Ann.annHasTyT
#print axioms Rcic.Declarative.Ann.annConvT
#print axioms Rcic.Declarative.Ann.annCtxWfT
