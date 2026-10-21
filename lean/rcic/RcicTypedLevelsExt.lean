import rcic.RcicTypedLevels

/-!
# `RcicTypedLevelsExt` — projection-parameterized `EnvWfT` discharges

`RcicTypedLevels` is landed and sealed, so its declarations keep their
statements verbatim. This module generalizes the two discharge theorems
the conversion-walk emitters consume — `envWfT_group_arity` and
`iotaLevelsT_of_envWfT` — by taking the `EnvWfT` projections they
actually read as hypotheses. The same conclusions then hold at
`GroupMembersT`-intermediate environments, which never carry an
`EnvWfT`, once their stage data is supplied (`cvWalkHyp_cons`).

`Rcic.Syn.iotaLevelsT_of` is the `RcicSynMember.CvWalkHyp` consumer;
`envWfT_group_arity` / `iotaLevelsT_of_envWfT` themselves are unchanged
in `RcicTypedLevels`.
-/

namespace Rcic.Declarative

/-- The per-member arity-coherence certificates `envWfT_declArities`
    produces, named so the same shape can be carried through a
    `GroupMembersT` prefix (whose intermediate environments never carry an
    `EnvWfT`). -/
def DeclAritiesT (E : ResolvedEnv) : Type :=
  ∀ r m, E.members r = some m →
    Σ' (E0 : ResolvedEnv), groupArityCoherent E0 m = true ×'
      (∀ r' m', E0.members r' = some m' → E.members r' = some m')

/-- `envWfT_group_arity` with `envWfT_declArities` projected up front. -/
noncomputable def groupArity_of_declAritiesT {E : ResolvedEnv}
    (hdecl : DeclAritiesT E)
    {r f : Nat} {m fm : CheckedMember}
    (hm : E.members r = some m) (hf : memberFamRef m = some f)
    (hfam : E.members f = some fm) :
    ((m.mclass = .constructorM) → m.arity = fm.arity) ×'
    ((m.mclass = .recursorM) →
      m.arity = fm.arity ∨ m.arity = fm.arity + 1) := by
  obtain ⟨E0, ha, hext⟩ := hdecl r m hm
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have ha' := ha
    simp only [groupArityCoherent, hc, hf] at ha'
    cases hfm0 : E0.members f with
    | none => rw [hfm0] at ha'; exact Bool.noConfusion ha'
    | some fm0 =>
        rw [hfm0] at ha'
        have hfe : fm0 = fm :=
          Option.some.inj ((hext f fm0 hfm0).symm.trans hfam)
        subst hfe
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha'
        exact ha'.2
  · have ha' := ha
    simp only [groupArityCoherent, hc, hf] at ha'
    cases hfm0 : E0.members f with
    | none => rw [hfm0] at ha'; exact Bool.noConfusion ha'
    | some fm0 =>
        rw [hfm0] at ha'
        have hfe : fm0 = fm :=
          Option.some.inj ((hext f fm0 hfm0).symm.trans hfam)
        subst hfe
        simp only [Bool.and_eq_true, Bool.or_eq_true,
          decide_eq_true_eq] at ha'
        exact ha'.2

/-- `envWfT_ctorArity` with `envWfT_declArities` projected up front. -/
theorem ctorArity_of_declAritiesT {E : ResolvedEnv} (hdecl : DeclAritiesT E)
    (w : IotaWitness E) : w.ctorMember.arity = w.famMember.arity :=
  (groupArity_of_declAritiesT hdecl w.hctor (memberFamRef_ctorMember w)
    w.hfam).1 w.hctorK

/-- `envWfT_recArity` with `envWfT_declArities` projected up front. -/
theorem recArity_of_declAritiesT {E : ResolvedEnv} (hdecl : DeclAritiesT E)
    (w : IotaWitness E) : w.recMember.arity = w.famMember.arity ∨
      w.recMember.arity = w.famMember.arity + 1 :=
  (groupArity_of_declAritiesT hdecl w.hrec (memberFamRef_recMember w)
    w.hfam).2 w.hrecK

/-- `envWfT_ctorArityS` with `envWfT_declArities` projected up front. -/
theorem ctorArityS_of_declAritiesT {E : ResolvedEnv} (hdecl : DeclAritiesT E)
    (w : IotaWitnessS E) : w.ctorMember.arity = w.famMember.arity :=
  (groupArity_of_declAritiesT hdecl w.hctor (memberFamRef_ctorMemberS w)
    w.hfam).1 w.hctorK

/-- `envWfT_recArityS` with `envWfT_declArities` projected up front. -/
theorem recArityS_of_declAritiesT {E : ResolvedEnv} (hdecl : DeclAritiesT E)
    (w : IotaWitnessS E) : w.recMember.arity = w.famMember.arity ∨
      w.recMember.arity = w.famMember.arity + 1 :=
  (groupArity_of_declAritiesT hdecl w.hrec (memberFamRef_recMemberS w)
    w.hfam).2 w.hrecK

/-- `iotaLevelsT_of_envWfT` with the `EnvWfT` projections taken as
    hypotheses — the only data the discharge reads, so the same conclusion
    holds at `GroupMembersT`-intermediate environments (which never carry
    an `EnvWfT`) once their stage data is supplied. -/
theorem iotaLevelsT_of {E : ResolvedEnv} (hEL : EnvLevelsT E)
    (hB0 : ∀ r m b, E.members r = some m → m.body = some b →
      exprLevelsBounded 0 b = true)
    (hdecl : DeclAritiesT E) :
    IotaLevelsT E :=
  ⟨fun w => by
      have hsup : ∀ r ls b, transparentBody E r ls = some b →
          exprLevelsBounded w.recMember.arity b = true :=
        fun _ _ _ htb =>
          transparentBody_lvl0 hB0 htb
      have hle : w.ctorMember.arity ≤ w.recMember.arity := by
        have hctorA := ctorArityS_of_declAritiesT hdecl w
        rcases recArityS_of_declAritiesT hdecl w with h | h <;> omega
      have hbmt : exprLevelsBounded w.recMember.arity
          w.ctorMember.mtype = true :=
        exprLevelsBounded_mono hle _
          (hEL w.ctorRef w.ctorMember w.hctor).1
      obtain ⟨hds, hres⟩ := peelPis_bounded _ _ w.hpeel hbmt
      have htel : exprLevelsBounded w.recMember.arity
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = true := by
        rw [exprLevelsBounded_lift]
        exact ctorFieldTelRaw_bounded hds hres
      have hrecB : exprLevelsBounded w.recMember.arity
          (.const w.recRef (canonRecLevels w.recMember.arity)) = true :=
        levelsBounded_canonRecLevels _
      have hminor : exprLevelsBounded w.recMember.arity
          (.bvar (w.fields.length + w.nindices +
            (w.nMinors - 1 - w.ctorIdx))) = true := rfl
      rw [w.hlsLen]
      exact iotaOpenRhs_bounded hsup hrecB hminor
        preMajorBvars_bounded fieldBvars_bounded htel w.hschema,
    fun w => by
      have hle : w.ctorMember.arity ≤ w.recMember.arity := by
        have hctorA := ctorArity_of_declAritiesT hdecl w
        rcases recArity_of_declAritiesT hdecl w with h | h <;> omega
      have hbmt : exprLevelsBounded w.recMember.arity
          w.ctorMember.mtype = true :=
        exprLevelsBounded_mono hle _
          (hEL w.ctorRef w.ctorMember w.hctor).1
      rw [w.hlsLen]
      exact hbmt⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.DeclAritiesT
#print axioms Rcic.Declarative.groupArity_of_declAritiesT
#print axioms Rcic.Declarative.ctorArity_of_declAritiesT
#print axioms Rcic.Declarative.recArity_of_declAritiesT
#print axioms Rcic.Declarative.ctorArityS_of_declAritiesT
#print axioms Rcic.Declarative.recArityS_of_declAritiesT
#print axioms Rcic.Declarative.iotaLevelsT_of