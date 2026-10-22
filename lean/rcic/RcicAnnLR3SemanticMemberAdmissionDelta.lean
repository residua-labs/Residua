import rcic.RcicAnnLR3SemanticMemberAdmissionReadback

/-!
# Admission readback commutes with every actual transparent delta step

Head support follows from the source body's admitted typing. A fresh
definition preserves the old reader on supported heads. Induction over
the complete admission tree then preserves both successful and failed
readback across every transparent delta lookup, including later groups
and recursors. No fuel, normalization or semantic membership premise is
used. This does not assert completeness for arbitrary conversion.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.AdmissionUniverseReadback
open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

def HeadSupported (E : ResolvedEnvA) (A : ExprA) : Prop :=
  match A with
  | .const r _ => ∃ m, E.members r = some m
  | _ => True

theorem headSupported_prefix {E W : ResolvedEnvA} (h : PrefixA E W)
    {A : ExprA} (hA : HeadSupported E A) : HeadSupported W A := by
  cases A <;> try trivial
  rcases hA with ⟨m, hm⟩
  exact ⟨m, h _ _ hm⟩

theorem headSupported_instantiate {E : ResolvedEnvA} {A : ExprA}
    (hA : HeadSupported E A) (ls : List Level) :
    HeadSupported E (instantiateLevelsA ls A) := by
  cases A <;> simp_all [HeadSupported, instantiateLevelsA]

theorem headSupported_of_typed {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {e A : ExprA}
    (h : HasTyA E I n Γ e A) : HeadSupported E e := by
  have hs := hasTyA_constsIn h
  cases e <;> trivial

theorem addRead_preserves (old : Valuation → ExprA → Option (Option Nat))
    {E : ResolvedEnvA} (r : Nat) (b : ExprA)
    (hf : E.members r = none) (ν : Valuation) (A : ExprA)
    (hA : HeadSupported E A) : addRead old r b ν A = old ν A := by
  cases A <;> try rfl
  rename_i q ls
  have hqr : q ≠ r := by
    intro heq
    rcases hA with ⟨m, hm⟩
    simp [heq, hf] at hm
  simp only [addRead, if_neg hqr]

theorem definitionBody_lookup {E : ResolvedEnvA} {r : Nat}
    {ls : List Level} {b : ExprA}
    (h : EnvironmentEval.definitionBody E r ls = some b) :
    ∃ m, E.members r = some m ∧ transparent m.mclass = true ∧
      ∃ v, m.bodyA = some v ∧ instantiateLevelsA ls v = b := by
  cases hm : E.members r with
  | none => simp [EnvironmentEval.definitionBody, hm] at h
  | some m =>
    cases ht : transparent m.mclass with
    | false => simp [EnvironmentEval.definitionBody, hm, ht] at h
    | true =>
      cases hb : m.bodyA with
      | none => simp [EnvironmentEval.definitionBody, hm, ht, hb] at h
      | some v =>
        have hv : instantiateLevelsA ls v = b := by
          simpa [EnvironmentEval.definitionBody, hm, ht, hb] using h
        exact ⟨m, rfl, ht, v, hb, hv⟩

theorem definitionBody_eq_of_rigid_extension {E W : ResolvedEnvA}
    (hp : PrefixA E W)
    (hnew : ∀ r m, W.members r = some m →
      E.members r = some m ∨ transparent m.mclass = false) :
    ∀ r ls, EnvironmentEval.definitionBody W r ls =
      EnvironmentEval.definitionBody E r ls := by
  intro r ls
  cases hm : E.members r with
  | some m =>
    have hw := hp r m hm
    simp [EnvironmentEval.definitionBody, hm, hw]
  | none =>
    cases hw : W.members r with
    | none => simp [EnvironmentEval.definitionBody, hm, hw]
    | some m =>
      rcases hnew r m hw with hold | hr
      · simp [hm] at hold
      · simp [EnvironmentEval.definitionBody, hm, hw, hr]

theorem definitionBody_extend_rigid (E : ResolvedEnvA) (r : Nat)
    (m : CheckedMemberA) (hf : E.members r = none)
    (ht : transparent m.mclass = false) :
    ∀ q ls, EnvironmentEval.definitionBody (extendEnvA E r m) q ls =
      EnvironmentEval.definitionBody E q ls := by
  intro q ls
  by_cases hqr : q = r
  · subst q
    simp [EnvironmentEval.definitionBody, extendEnvA, hf, ht]
  · simp [EnvironmentEval.definitionBody, extendEnvA, hqr, Ne.symm hqr]

theorem definitionBody_extend_transparent (E : ResolvedEnvA) (r : Nat)
    (m : CheckedMemberA) (b : ExprA) (hb : m.bodyA = some b)
    (ht : transparent m.mclass = true) :
    ∀ q ls, EnvironmentEval.definitionBody (extendEnvA E r m) q ls =
      if q = r then some (instantiateLevelsA ls b)
      else EnvironmentEval.definitionBody E q ls := by
  intro q ls
  by_cases hqr : q = r
  · subst q
    simp [EnvironmentEval.definitionBody, extendEnvA, hb, ht]
  · simp [EnvironmentEval.definitionBody, extendEnvA, hqr, Ne.symm hqr]

theorem definitionBody_group_rigid {E : ResolvedEnvA} {f : Nat}
    {fm : CheckedMemberA} (cs : List (Nat × CheckedMemberA))
    (hp : PrefixA E (groupEnvA E f fm cs))
    (hfm : transparent fm.mclass = false)
    (hc : ∀ r m, (r, m) ∈ cs → transparent m.mclass = false) :
    ∀ r ls, EnvironmentEval.definitionBody (groupEnvA E f fm cs) r ls =
      EnvironmentEval.definitionBody E r ls := by
  apply definitionBody_eq_of_rigid_extension hp
  intro r m hm
  rcases members_groupEnvA cs r m hm with h | h | h
  · rcases h with ⟨_, rfl⟩
    exact Or.inr hfm
  · exact Or.inr (hc r m h)
  · exact Or.inl h

structure Good {E : ResolvedEnvA} (R : Reader E) : Prop where
  bodyHead : ∀ r ls b,
    EnvironmentEval.definitionBody E r ls = some b → HeadSupported E b
  delta : ∀ ν r ls b, EnvironmentEval.definitionBody E r ls = some b →
      R.read ν (.const r ls) = R.read ν b

theorem good_empty : Good Reader.empty where
  bodyHead := by
    intro r ls b h
    simp [EnvironmentEval.definitionBody, emptyEnvA] at h
  delta := by
    intro ν r ls b h
    simp [EnvironmentEval.definitionBody, emptyEnvA] at h

theorem good_weaken {E W : ResolvedEnvA} {R : Reader E}
    (g : Good R) (hp : PrefixA E W)
    (hbody : ∀ r ls, EnvironmentEval.definitionBody W r ls =
      EnvironmentEval.definitionBody E r ls) : Good (R.weaken hp) where
  bodyHead := by
    intro r ls b h
    exact headSupported_prefix hp (g.bodyHead r ls b ((hbody r ls).symm.trans h))
  delta := by
    intro ν r ls b h
    exact g.delta ν r ls b ((hbody r ls).symm.trans h)

theorem good_addTransparent {E W : ResolvedEnvA} {R : Reader E}
    (g : Good R) (hp : PrefixA E W) {r : Nat}
    {m : CheckedMemberA} {b : ExprA}
    (hm : W.members r = some m) (hb : m.bodyA = some b)
    (ht : transparent m.mclass = true) (hf : E.members r = none)
    (hs : HeadSupported E b)
    (hshape : ∀ q ls, EnvironmentEval.definitionBody W q ls =
      if q = r then some (instantiateLevelsA ls b)
      else EnvironmentEval.definitionBody E q ls) :
    Good (R.addTransparent hp hm hb ht) := by
  constructor
  · intro q ls B hδ
    rw [hshape q ls] at hδ
    by_cases hqr : q = r
    · have hB : instantiateLevelsA ls b = B := by simpa [hqr] using hδ
      rw [← hB]
      exact headSupported_prefix hp (headSupported_instantiate hs ls)
    · have hold : EnvironmentEval.definitionBody E q ls = some B := by
        simpa [hqr] using hδ
      exact headSupported_prefix hp (g.bodyHead q ls B hold)
  · intro ν q ls B hδ
    change addRead R.read r b ν (.const q ls) = addRead R.read r b ν B
    rw [hshape q ls] at hδ
    by_cases hqr : q = r
    · have hB : instantiateLevelsA ls b = B := by simpa [hqr] using hδ
      subst q
      rw [← hB]
      calc
        addRead R.read r b ν (.const r ls) =
            R.read ν (instantiateLevelsA ls b) := by simp [addRead]
        _ = addRead R.read r b ν (instantiateLevelsA ls b) :=
          (addRead_preserves R.read r b hf ν _ (headSupported_instantiate hs ls)).symm
    · have hold : EnvironmentEval.definitionBody E q ls = some B := by
        simpa [hqr] using hδ
      obtain ⟨old, holdLookup, _, _, _, _⟩ := definitionBody_lookup hold
      have hq : HeadSupported E (.const q ls) := ⟨old, holdLookup⟩
      calc
        addRead R.read r b ν (.const q ls) = R.read ν (.const q ls) :=
          addRead_preserves R.read r b hf ν _ hq
        _ = R.read ν B := g.delta ν q ls B hold
        _ = addRead R.read r b ν B :=
          (addRead_preserves R.read r b hf ν B (g.bodyHead q ls B hold)).symm

theorem readerOf_good {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) : Good (readerOf hE) := by
  induction hE with
  | empty => exact good_empty
  | axiomM E r A u hE hfresh hA hcl hlvl ih =>
      exact good_weaken ih (prefixA_extend E r _ hfresh)
        (definitionBody_extend_rigid E r _ hfresh rfl)
  | definitionM E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv ih =>
      exact good_addTransparent ih
        (prefixA_extend E r ⟨.definitionM, 0, A, some v, 0, none⟩ hfresh)
        (members_extendEnvA_self E r _) rfl rfl hfresh (headSupported_of_typed hv)
        (definitionBody_extend_transparent E r _ v rfl rfl)
  | theoremM E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp ih =>
      exact good_weaken ih (prefixA_extend E r _ hfresh)
        (definitionBody_extend_rigid E r _ hfresh rfl)
  | opaqueM E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv ih =>
      exact good_weaken ih (prefixA_extend E r _ hfresh)
        (definitionBody_extend_rigid E r _ hfresh rfl)
  | group E f fm u hE hcls hnobody hclT hT hlvl fv cs hfresh ih =>
      apply good_weaken ih (prefixA_groupEnvA hfresh)
      apply definitionBody_group_rigid (cs.map GroupCtorA.entry) (prefixA_groupEnvA hfresh)
      · rw [hcls]
        rfl
      · intro r m hm
        obtain ⟨c, _, hc⟩ := List.mem_map.mp hm
        have hcm : c.member = m := congrArg Prod.snd hc
        rw [← hcm, c.hcls]
        rfl
  | groupRec E f fm u hE hcls hnobody hclT hT hlvl fv cs hfresh hlayout rec hrfresh ih =>
      apply good_weaken ih
        (prefixA_trans (prefixA_groupEnvA hfresh) (prefixA_extend _ _ _ hrfresh))
      intro r ls
      have hg : EnvironmentEval.definitionBody
            (groupEnvA E f fm (cs.map GroupCtorA.entry)) r ls =
          EnvironmentEval.definitionBody E r ls := by
        apply definitionBody_group_rigid (cs.map GroupCtorA.entry) (prefixA_groupEnvA hfresh)
        · rw [hcls]
          rfl
        · intro q m hm
          obtain ⟨c, _, hc⟩ := List.mem_map.mp hm
          have hcm : c.member = m := congrArg Prod.snd hc
          rw [← hcm, c.hcls]
          rfl
      have hr := definitionBody_extend_rigid
        (groupEnvA E f fm (cs.map GroupCtorA.entry))
        (f + 1 + cs.length) rec.member hrfresh (by rw [rec.hcls]; rfl) r ls
      exact hr.trans hg

theorem readAdmitted_delta {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (ν : Valuation) {r : Nat} {ls : List Level} {b : ExprA}
    (hδ : EnvironmentEval.definitionBody E r ls = some b) :
    readAdmitted hE ν (.const r ls) = readAdmitted hE ν b :=
  (readerOf_good hE).delta ν r ls b hδ

theorem readAdmitted_view_delta {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (ν : Valuation) {r : Nat} {ls : List Level} {b : ExprA}
    (hδ : EnvironmentEval.definitionBody (SemanticMemberEval.view E) r ls = some b) :
    readAdmitted hE ν (.const r ls) = readAdmitted hE ν b := by
  apply readAdmitted_delta hE ν
  simpa only [SemanticMemberEval.definitionBody_preserved] using hδ

theorem readAdmitted_sort {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (ν : Valuation) (l : Level) :
    readAdmitted hE ν (.sort l) = some (eval ν l) := by
  induction hE <;> first | rfl | assumption

inductive SortDeltaChain (E : ResolvedEnvA) (ν : Valuation) :
    ExprA → Option Nat → Prop where
  | sort (l : Level) : SortDeltaChain E ν (.sort l) (eval ν l)
  | delta {r : Nat} {ls : List Level} {b : ExprA} {k : Option Nat}
      (step : EnvironmentEval.definitionBody E r ls = some b)
      (tail : SortDeltaChain E ν b k) : SortDeltaChain E ν (.const r ls) k

/-- Complete for every finite head-sort/transparent-delta chain. The
algorithm takes only the admission tree, not this chain certificate. -/
theorem readAdmitted_complete {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (ν : Valuation) {A : ExprA} {k : Option Nat}
    (h : SortDeltaChain E ν A k) : readAdmitted hE ν A = some k := by
  induction h with
  | sort l => exact readAdmitted_sort hE ν l
  | delta step tail ih => exact (readAdmitted_delta hE ν step).trans ih

end Rcic.Declarative.Ann.LR3.AdmissionUniverseReadback
