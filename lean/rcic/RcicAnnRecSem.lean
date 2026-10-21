import rcic.RcicAnnRecTel
import rcic.RcicAnnSpineConv
import rcic.RcicAnnFrecDomSyn
import rcic.RcicAnnTelTy
import rcic.RcicAnnFrecArm
import rcic.RcicAnnFrecWorld
import rcic.RcicAnnFrecBeta

/-!
# M2-f (5b)/(6c) — the recursors' clause at the group step

At a group's recursor `r` (`EnvWfA.groupRec`), the clause relates `r ls` and `r ls'` at the
recursor's type. With the clauses of the base, the family and the constructors in hand, the
recursor's type (typed in the DerivationScope) falls under the fundamental theorem.

* A recursor type at a zero motive level is a proposition (`recTypeA_propTy`): the `prop` clause
  relates the two heads, typed and convertible.
* Otherwise the family is a Type family (`PropElimStructA`) and the clause is the telescope lemma's:
  every pair of full applications to related arguments is related at the motive instance. The
  arguments split at the recursor's parameters `qs` (`recArgsSplitPA`); the major's relation is the
  `fam` clause's least fixed point at the canonical relations, at a family application in the fiber
  of `qs`, and the claim is proved by induction on it: a stuck major gives two extended neutrals
  (`neutKA_recApp`, reflection); a constructor form gives, after the major's chain and ι (at the
  recursor's parameters), the minor applied to the fields and the induction hypotheses, related
  along the minor's telescope (the minor walk), at the minor's conclusion, moved to the redex's type
  by the motive's relation. The form's own parameters are only convertible with `qs` (P2, M2-f (6)):
  the constructor at the recursor's levels and parameters is related to the major through the fixed
  point, by a conversion along the constructor's mirror telescope (`mirrorParConvA`,
  `convA_spine`). No parameter-freeness is assumed (M2-f (6c)).
* At a unit group (O1-b-1: one constructor without fields, a `Prop` family without indices,
  `unitGroupA`) the family is a proposition and `PropElimOnlyA` exempts the recursor. Every full
  application steps to its minor (K-unit, or ι at the constructor), and the clause relates the two
  minors at the redex's type (`recUnitAppsA`): the major and the constructor are related at the family
  application by the `prop` clause, and the motive carries the pair.
* At a struct group (W-1 (c): one constructor whose fields are all proofs, a `Prop` family without
  indices, `structGroupA`) `PropElimStructA` exempts the recursor as well. Every full application steps
  to its minor applied to the major's projections (K-struct, or ι at the constructor, which contracts
  there to the same reduct). The projections are typed along the fields (`structProjsA_substTyA`);
  the two sides' projections are a valid pair along the minor's domain, every field a proof
  (`validSubstA_propTel`: the fundamental theorem across the two level lists types the right's
  projections at the left's domains, where proofs are related); and the minor's conclusion at the
  projections is the redex's type, the major related to the constructor at its projections by the
  `prop` clause (`recStructAppsA`).

Entry points: `recSemClauseA` (the clause at one group's recursor), `envSemRecStepA_of_structProfile`
and `envSemRecStepA_of_profile` (the recursors' step of the environment induction under the profile)
and `envSemA_of_envWfA_recStruct` / `envSemA_of_envWfA_rec` (`EnvSemA` at the concrete ι of a
well-formed environment under `SmallIndexProfileA` and `PropElimStructA`, resp. `PropElimOnlyA`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the fixed data at a group -/

/-- THE FIXED DATA of the recursors' clause at a group, at the concrete ι of `E`: the base `E₀` with
    its fundamental theorem in `E`, the family (a Type family) with its view and its constructors'
    census, the small-index profile. R-NoFunRec-1 step 1 (1c-ε2d): and the group environment `G` (the
    base with the family and its constructors, a prefix of `E`) with its closure facts, its typed
    recursor-head fact and its conversion fundamental theorem in `E`, from the environment induction's
    hypothesis at `G`. -/
structure RecBaseA (E₀ E : ResolvedEnvA) (n : Nat) (ρ₀ : Nat → Nat) (f : Nat) (fm : CheckedMemberA)
    (fv : FamViewA fm) (cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)) : Type where
  hfund : BaseFundA E₀ E (iotaIfaceA E) n ρ₀
  hfc : BaseFundConvA E₀ E (iotaIfaceA E) n ρ₀
  hE₀ : EnvClosedA E₀
  hE : EnvClosedA E
  /-- the norm-evidence ι reads at the constructor members' `normA` (R-NoDeltaRec-3b). -/
  hEN : EnvNormClosedA E
  /-- every constructor's `normA` is const-headed at its `piBody` (R-NoDeltaRec-4d-iii). -/
  hNCT : EnvNormCtorTypeA E
  hI : IotaLiftA (iotaIfaceA E)
  hR₀ : IotaRecHeadTypedA E₀ (iotaIfaceA E)
  hEL₀ : EnvLevelsA E₀
  hEL : EnvLevelsA E
  hENL : EnvNormLevelsA E
  hIL : IotaLevelsA (iotaIfaceA E)
  hS : SmallIndexProfileA E
  hfm : E.members f = some fm
  hcls : fm.mclass = .inductiveM
  hnobody : fm.bodyA = none
  hfresh : E₀.members f = none
  hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
    ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm
  hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA
  u : Level
  hT : HasTyA E₀ (iotaIfaceA E) fm.arity [] fm.mtypeA (.sort u)
  hUT : UniformType fv.sort
  hR : IotaRecHeadA E (iotaIfaceA E)
  hCtor : ∀ gc ∈ cs, EnvSemClauseA E (iotaIfaceA E) n ρ₀ gc.ref gc.member
  /-- the group's freshness stack — `drecD`'s evidence lives in the family's extension, which is
      a prefix of the group environment under it (R-NoDeltaRec-4d-iii). -/
  hgf : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry)
  hmemG : (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)).members f = some fm
  hpre₀G : PrefixA E₀ (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))
  hpreG : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E
  hEG : EnvClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))
  hELG : EnvLevelsA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))
  hRG : IotaRecHeadTypedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) (iotaIfaceA E)
  hfcG : BaseFundConvA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E (iotaIfaceA E) n ρ₀

section Base
variable {E₀ E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
  {cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)}

theorem applyTelA_nil_eq {T T' : ExprA} (h : applyTelA [] T = some T') : T' = T := by
  simp only [applyTelA] at h
  injection h with h
  exact h.symm

/-- THE CANONICAL INDEX RELATION IS A PER ON A FIBER, at parameters related to themselves along the
    family's type: the flipped pair at the other telescope and the composite pair, from the relation at
    the domain reached (`famRsFA_eq`), its symmetry and transitivity, and the two domains' equality
    (`famFldFeqA`). -/
theorem RecBaseA.idxPer (C : RecBaseA E₀ E n ρ₀ f fm fv cs) {ls₀ : List Level}
    (hb₀ : levelsBounded n ls₀ = true) (hl₀ : ls₀.length = fm.arity) {k : Nat}
    (hk : ht ρ₀ (instLevel ls₀ fv.sort) ≤ k) {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ))
    {qs : List ExprA} (hqs : qs.length = fm.nparamsA)
    (hqrel : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls₀ fm.mtypeA) (qs ++ []) (qs ++ [])) :
    IdxPerA n (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm []) fm qs ls₀ := by
  have hFeq := famFldFeqA (fv := fv) C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hS
    C.hfm C.hcls C.hcl C.hT C.hUT hb₀ hl₀ hk (k := k) hΓ (is := []) hqs hqrel [] (Or.inl rfl)
  intro lsF lsF' TF TF' hlF hlFF hTF hTF'
  have hTF₀ : applyTelA (qs.map (wkExprA [])) (instantiateLevelsA lsF fm.mtypeA) = some TF := by
    rw [map_wkExprA_nil]; exact hTF
  have hTF₀' : applyTelA (qs.map (wkExprA [])) (instantiateLevelsA lsF' fm.mtypeA) = some TF' := by
    rw [map_wkExprA_nil]; exact hTF'
  have hrig := rigid_of_sortBody fv.piBody
  refine ⟨fun pre pre' A u B v hw _ hTA => ?_, fun p₁ p₂ p₃ A u B v h₁₂ _ _ hTA => ?_⟩
  · have hTAf : applyTelA (qs ++ pre) (instantiateLevelsA lsF fm.mtypeA) = some (.pi A u B v) := by
      rw [applyTelA_append, hTF]; exact hTA
    obtain ⟨A', u', B', v', hTA'f⟩ := applyTelA_pi_transfer_levels hrig lsF lsF' (xs' := qs ++ pre')
      (by rw [List.length_append, List.length_append, argsRelPA_length hw]) hTAf
    have hTA' : applyTelA pre' TF' = some (.pi A' u' B' v') := by
      rw [applyTelA_append, hTF'] at hTA'f; exact hTA'f
    refine ⟨A', u', B', v', hTA', fun x x' hr => ?_⟩
    have heq := hFeq lsF lsF' _ _ pre pre' A u B v A' u' B' v' hlF hlFF hTF₀ hTF₀'
      (by rw [map_wkExprA_nil]; exact hw) hTA hTA'
    rw [famRsFA_eq hTAf] at hr
    rw [famRsFA_eq hTA'f]
    exact LRRelA_transport' C.hNCT heq (LRRelA_symm C.hNCT hr)
  · have hTAf : applyTelA (qs ++ p₁) (instantiateLevelsA lsF fm.mtypeA) = some (.pi A u B v) := by
      rw [applyTelA_append, hTF]; exact hTA
    obtain ⟨A', u', B', v', hTA'f⟩ := applyTelA_pi_transfer_levels hrig lsF lsF' (xs' := qs ++ p₂)
      (by rw [List.length_append, List.length_append, argsRelPA_length h₁₂]) hTAf
    have hTA' : applyTelA p₂ TF' = some (.pi A' u' B' v') := by
      rw [applyTelA_append, hTF'] at hTA'f; exact hTA'f
    refine ⟨A', u', B', v', hTA', fun x₁ x₂ x₃ r₁₂ r₂₃ => ?_⟩
    have heq := hFeq lsF lsF' _ _ p₁ p₂ A u B v A' u' B' v' hlF hlFF hTF₀ hTF₀'
      (by rw [map_wkExprA_nil]; exact h₁₂) hTA hTA'
    rw [famRsFA_eq hTAf] at r₁₂ ⊢
    rw [famRsFA_eq hTA'f] at r₂₃
    exact LRRelA_trans C.hNCT r₁₂ (LRRelA_transport' C.hNCT (LREqA_symm C.hNCT heq) r₂₃)

/-- THE WHOLE DOMAIN OF A FUNCTION-RECURSIVE FIELD, ACROSS TWO INSTANCES (R-NoFunRec-1 step 1 (1c-ε2d), N1).
    As `plainDomA`, a walk reaching a function-recursive field: the domain reached on the left (after `pre`,
    at `ps`, `lsC`) and on the right (after `pre'`, at `ps'`, `lsC'`) are equal at any height `j` above the
    family's sort, and valid there. The domain mentions the family, so its base derivation lives in the
    group environment (`frecDomTyG`) and the fundamental theorem is the group's (`fundLevelsA` with
    `hfcG`), read at the walk's valid pair; the sort is below the family's (`frecSort_ht_le`). -/
theorem RecBaseA.frecDomEq (C : RecBaseA E₀ E n ρ₀ f fm fv cs)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA}
    (hρ : WkOk₀A E (iotaIfaceA E) n ρ Γ) {c : Nat} {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {jn : Nat} {T T' : ExprA}
    {pre pre' : List ExprA} {D : ExprA} {uD : Level} {C₀ : ExprA} {vC : Level} {D' : ExprA}
    {uD' : Level} {C₀' : ExprA} {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T
      ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C₀ vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C₀' vC')) :
    LREqA E (iotaIfaceA E) n ρ₀ j (wkCtxA ρ Γ) D D' ∧
      (∃ R, LRTyA E (iotaIfaceA E) n ρ₀ j (wkCtxA ρ Γ) D R) ∧
      (∃ R, LRTyA E (iotaIfaceA E) n ρ₀ j (wkCtxA ρ Γ) D' R) := by
  refine frecWalkA C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hfresh C.hcensus C.hcl
    C.hT hb hl hΓ hps hps' hrel hρ hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' ?_
  intro fsPre B uB Bs idx hBs hlen hlen' hdom hΓp huniv hDe hDe' ⟨fsRest, res, ⟨hty⟩⟩ ⟨K₁, hK₁⟩
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hbC' : levelsBounded n lsC' = true := hlCC.2
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hd0 := frecDomTyG C.hEG C.hI C.hRG (iotaFnA_subst C.hE C.hEN) C.hpre₀G (fv := fv)
    (hasTyEnvA C.hpre₀G C.hT) C.hmemG fsPre hty
  have hΓG := viewTy_ctx_env C.hpre₀G hΓp
  obtain ⟨K₃, hK₃⟩ := fundLevelsA C.hfcG C.hEG C.hI C.hRG C.hELG C.hIL hbC hbC' hlC hlC' hlCC.1 hΓG hd0
  have hK1 : K₁ ≤ max K₁ (max K₃ (max k j)) := by omega
  have hK3 : K₃ ≤ max K₁ (max K₃ (max k j)) := by omega
  have hKk : k ≤ max K₁ (max K₃ (max k j)) := by omega
  have hKj : j ≤ max K₁ (max K₃ (max k j)) := by omega
  have hV₁ := (hK₁ _ hK1 hKj hKk).2
  obtain ⟨_, hDrel⟩ := hK₃ _ hK3 (wkCtxA ρ Γ) _ _ hΓρ hV₁
  have hht : ht ρ₀ (instLevel lsC (frecDomA f (canonLevelsA fm.arity) fv.sort
      ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0))) SubstA.id ((B, uB) :: Bs) idx).2) ≤ j := by
    rw [frecDomA_snd]
    exact Nat.le_trans (frecSort_ht_le C.hUT huniv hlsC) hj
  obtain ⟨heq, hva, hvb⟩ := (LRRelA_sort_elim' hDrel).1 j hht
  have hpl : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hpl' : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  have hDC := frecDomA_reach fv hlC hpl hlen hDe
  have hDC' := frecDomA_reach fv hlC' hpl' hlen' hDe'
  rw [hDC, hDC'] at heq
  rw [hDC] at hva
  rw [hDC'] at hvb
  exact ⟨heq, hva, hvb⟩

end Base

/-! ## (2) the minor applied to the ι reduct's arguments -/

theorem applyTelA_cons_pi (a : ExprA) (as : List ExprA) (D : ExprA) (u : Level) (B : ExprA) (v : Level) :
    applyTelA (a :: as) (.pi D u B v) = applyTelA as (instantiate0A a B) := rfl

/-- THE MINOR ALONG THE REDUCT'S ARGUMENTS: the ι right-hand side's arguments (`rhsArgsA`, each field
    followed by its recursive call at a recursive one) walk the minor's telescope (each field binder
    takes the field, each induction-hypothesis binder the call), to the minor's conclusion at the
    fields: the motive at the result indices, substituted by the plain fields, and the constructor
    applied to the parameters and the fields. -/
theorem applyTelA_minor_rhsArgsA (rc : ExprA) (PRE : List ExprA) (np K : Nat) (f c : Nat) (ls : List Level)
    (wF wM : Level) (res : List ExprA) (mot : ExprA) (pl : List ExprA) :
    (fsR : List FieldA) → (fl : List ExprA) → (σ : SubstA) → (vs : List ExprA) → vs.length = fsR.length →
    applyTelA (rhsArgsA rc PRE np K vs (fsR.map FieldA.shape)
        (ctorFieldsA f ls wF pl σ (fsR.map FieldA.norm) res).1)
      (minorFieldsA f c ls wF wM pl mot fl σ fsR res).1 =
      some (foldAppsA mot (res.map (substA (consListA (plainArgsA fsR vs) σ)) ++
        [foldAppsA (.const c ls) (pl ++ (fl ++ vs))]))
  | [], fl, σ, [], _ => by
      simp [rhsArgsA, minorFieldsA, applyTelA, plainArgsA, consListA]
  | [], _, _, _ :: _, h => nomatch h
  | _ :: _, _, _, [], h => nomatch h
  | .plain D u :: fsR, fl, σ, v :: vs, h => by
      simp only [List.map, FieldA.shape, FieldA.norm, ctorFieldsA, minorFieldsA, rhsArgsA, recCallsA,
        List.nil_append, applyTelA]
      have e1 := instantiate0A_ctorFieldsA_plain f ls wF res (fsR.map FieldA.norm) pl σ v
      have e2 := instantiate0A_minorFieldsA_plain f c ls wF wM res fsR pl mot fl σ v
      rw [e1, e2, applyTelA_minor_rhsArgsA rc PRE np K f c ls wF wM res mot pl fsR (fl ++ [v]) (SubstA.cons v σ) vs
        (Nat.succ.inj h)]
      simp only [plainArgsA, consListA, List.append_assoc, List.singleton_append]
 
  | .drec _ :: fsR, fl, σ, v :: vs, h
  | .frec _ _ _ _ :: fsR, fl, σ, v :: vs, h
  | .drecD _ _ :: fsR, fl, σ, v :: vs, h => by
      simp only [List.map, FieldA.shape, FieldA.norm, ctorFieldsA, minorFieldsA, rhsArgsA, recCallsA,
        List.singleton_append]
      have e1 := instantiate0A_ctorFieldsA_drec f ls wF res (fsR.map FieldA.norm) pl σ v
      rw [e1, applyTelA_cons_pi, instantiate0A_eq_substA_cons v, substA_pi, applyTelA_cons_pi,
        instantiate0A_instantiate0A_up, substA_minorFieldsA_drec f c ls wF wM res fsR pl mot fl σ v,
        applyTelA_minor_rhsArgsA rc PRE np K f c ls wF wM res mot pl fsR (fl ++ [v]) σ vs (Nat.succ.inj h)]
      simp only [plainArgsA, List.append_assoc, List.singleton_append]

/-! ## (3) helpers for the minor walk -/

theorem plainArgsA_snoc_plain (D : ExprA) (u : Level) (v : ExprA) :
    (fsPre : List FieldA) → (pre : List ExprA) → pre.length = fsPre.length →
    plainArgsA (fsPre ++ [FieldA.plain D u]) (pre ++ [v]) = plainArgsA fsPre pre ++ [v]
  | [], [], _ => rfl
  | .plain _ _ :: fs, x :: xs, h => by
      show x :: plainArgsA (fs ++ [FieldA.plain D u]) (xs ++ [v]) = x :: (plainArgsA fs xs ++ [v])
      rw [plainArgsA_snoc_plain D u v fs xs (Nat.succ.inj h)]
  | .drec _ :: fs, _ :: xs, h | .frec _ _ _ _ :: fs, _ :: xs, h | .drecD _ _ :: fs, _ :: xs, h => by
      show plainArgsA (fs ++ [FieldA.plain D u]) (xs ++ [v]) = plainArgsA fs xs ++ [v]
      rw [plainArgsA_snoc_plain D u v fs xs (Nat.succ.inj h)]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem plainArgsA_snoc_drec (idx : List ExprA) (v : ExprA) :
    (fsPre : List FieldA) → (pre : List ExprA) → pre.length = fsPre.length →
    plainArgsA (fsPre ++ [.drec idx]) (pre ++ [v]) = plainArgsA fsPre pre
  | [], [], _ => rfl
  | .plain _ _ :: fs, x :: xs, h => by
      show x :: plainArgsA (fs ++ [.drec idx]) (xs ++ [v]) = x :: plainArgsA fs xs
      rw [plainArgsA_snoc_drec idx v fs xs (Nat.succ.inj h)]
  | .drec _ :: fs, _ :: xs, h | .frec _ _ _ _ :: fs, _ :: xs, h | .drecD _ _ :: fs, _ :: xs, h => by
      show plainArgsA (fs ++ [.drec idx]) (xs ++ [v]) = plainArgsA fs xs
      rw [plainArgsA_snoc_drec idx v fs xs (Nat.succ.inj h)]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem plainArgsA_snoc_drecD (D : ExprA) (idx : List ExprA) (v : ExprA) :
    (fsPre : List FieldA) → (pre : List ExprA) → pre.length = fsPre.length →
    plainArgsA (fsPre ++ [.drecD D idx]) (pre ++ [v]) = plainArgsA fsPre pre
  | [], [], _ => rfl
  | .plain _ _ :: fs, x :: xs, h => by
      show x :: plainArgsA (fs ++ [.drecD D idx]) (xs ++ [v]) = x :: plainArgsA fs xs
      rw [plainArgsA_snoc_drecD D idx v fs xs (Nat.succ.inj h)]
  | .drec _ :: fs, _ :: xs, h | .frec _ _ _ _ :: fs, _ :: xs, h | .drecD _ _ :: fs, _ :: xs, h => by
      show plainArgsA (fs ++ [.drecD D idx]) (xs ++ [v]) = plainArgsA fs xs
      rw [plainArgsA_snoc_drecD D idx v fs xs (Nat.succ.inj h)]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem plainArgsA_snoc_frec (B : ExprA) (uB : Level) (Bs : List (ExprA × Level)) (idx : List ExprA) (v : ExprA) :
    (fsPre : List FieldA) → (pre : List ExprA) → pre.length = fsPre.length →
    plainArgsA (fsPre ++ [.frec B uB Bs idx]) (pre ++ [v]) = plainArgsA fsPre pre
  | [], [], _ => rfl
  | .plain _ _ :: fs, x :: xs, h => by
      show x :: plainArgsA (fs ++ [.frec B uB Bs idx]) (xs ++ [v]) = x :: plainArgsA fs xs
      rw [plainArgsA_snoc_frec B uB Bs idx v fs xs (Nat.succ.inj h)]
  | .drec _ :: fs, _ :: xs, h | .frec _ _ _ _ :: fs, _ :: xs, h | .drecD _ _ :: fs, _ :: xs, h => by
      show plainArgsA (fs ++ [.frec B uB Bs idx]) (xs ++ [v]) = plainArgsA fs xs
      rw [plainArgsA_snoc_frec B uB Bs idx v fs xs (Nat.succ.inj h)]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- the induction hypothesis's binder under its field. -/
theorem substA_cons_ihDom (v mot : ExprA) (xs : List ExprA) :
    substA (SubstA.cons v SubstA.id) (foldAppsA (liftA 0 1 mot) (xs.map (liftA 0 1) ++ [.bvar 0])) =
      foldAppsA mot (xs ++ [v]) := by
  rw [substA_foldAppsA, substA_cons_liftA, substA_id, List.map_append, map_substA_cons_liftA, map_substA_id]
  rfl

/-- the ι reduct's recursive call at a recursive field: the recursor at the parameters, the motive and
    the minors, the field's indices, the field. -/
theorem recCallFieldA_eq (r : Nat) (ls : List Level) (pfx is₁ : List ExprA) (np K : Nat)
    (hpfx : pfx.length = np + 1 + K) (v : ExprA) (f : Nat) (lsF : List Level) (pl idx : List ExprA)
    (hpl : pl.length = np) :
    recCallFieldA (.const r ls) (pfx ++ is₁) np K v (foldAppsA (.const f lsF) (pl ++ idx)) =
      foldAppsA (.const r ls) (pfx ++ idx ++ [v]) := by
  simp only [recCallFieldA, recPrefixA, familyIdxA, foldAppsA_const_head]
  rw [← hpfx, List.take_left, ← hpl, List.drop_left, List.append_assoc]

theorem minorLevelA_isZero (wF wM : Level) :
    (fs : List FieldA) → isZero (minorLevelA wF wM fs) = isZero wM
  | [] => rfl
  | .plain _ _ :: fs => by simp only [minorLevelA, isZero_imax, minorLevelA_isZero wF wM fs]
 
  | .drec _ :: fs
  | .frec _ _ _ _ :: fs
  | .drecD _ _ :: fs => by simp only [minorLevelA, isZero_imax, minorLevelA_isZero wF wM fs]

/-- `m` binders ending in a sort. -/
def SortTelA : Nat → ExprA → Prop
  | 0, .sort _ => True
  | m + 1, .pi _ _ B _ => SortTelA m B
  | _, _ => False

theorem sortTelA_substA : (m : Nat) → (T : ExprA) → (σ : SubstA) → SortTelA m T → SortTelA m (substA σ T)
  | 0, .sort _, _, _ => trivial
  | m + 1, .pi _ _ B _, σ, h => sortTelA_substA m B σ.up h
  | 0, .bvar _, _, h => h.elim
  | 0, .const _ _, _, h => h.elim
  | 0, .app _ _, _, h => h.elim
  | 0, .lam _ _ _, _, h => h.elim
  | 0, .pi _ _ _ _, _, h => h.elim
  | 0, .letE _ _ _, _, h => h.elim
  | 0, .lit _, _, h => h.elim
  | _ + 1, .bvar _, _, h => h.elim
  | _ + 1, .sort _, _, h => h.elim
  | _ + 1, .const _ _, _, h => h.elim
  | _ + 1, .app _ _, _, h => h.elim
  | _ + 1, .lam _ _ _, _, h => h.elim
  | _ + 1, .letE _ _ _, _, h => h.elim
  | _ + 1, .lit _, _, h => h.elim

theorem sortTelA_liftA : (m : Nat) → (T : ExprA) → (c a : Nat) → SortTelA m T → SortTelA m (liftA c a T)
  | 0, .sort _, _, _, _ => trivial
  | m + 1, .pi _ _ B _, c, a, h => sortTelA_liftA m B (c + 1) a h
  | 0, .bvar _, _, _, h => h.elim
  | 0, .const _ _, _, _, h => h.elim
  | 0, .app _ _, _, _, h => h.elim
  | 0, .lam _ _ _, _, _, h => h.elim
  | 0, .pi _ _ _ _, _, _, h => h.elim
  | 0, .letE _ _ _, _, _, h => h.elim
  | 0, .lit _, _, _, h => h.elim
  | _ + 1, .bvar _, _, _, h => h.elim
  | _ + 1, .sort _, _, _, h => h.elim
  | _ + 1, .const _ _, _, _, h => h.elim
  | _ + 1, .app _ _, _, _, h => h.elim
  | _ + 1, .lam _ _ _, _, _, h => h.elim
  | _ + 1, .letE _ _ _, _, _, h => h.elim
  | _ + 1, .lit _, _, _, h => h.elim

theorem sortTelA_piTelA (s w : Level) : (ds : List (ExprA × Level)) → SortTelA ds.length (piTelA ds (.sort s) w).1
  | [] => trivial
  | (_, _) :: ds => sortTelA_piTelA s w ds

/-- a list typed along a sort-ended telescope of `m` binders has `m` entries. -/
theorem argsTyA_sortTelA_length {E : ResolvedEnvA} {I : IotaIfaceA} {a : Nat} {Γ : LCtxA} :
    {T : ExprA} → {xs : List ExprA} → ArgsTyA E I a Γ T xs → (m : Nat) → SortTelA m T → xs.length = m
  | _, _, .nil _, 0, _ => rfl
  | _, _, .nil _, _ + 1, h => h.elim
  | _, _, .cons _ _ _ _ _ _ _ _, 0, h => h.elim
  | _, _, .cons _ _ B _ x _ _ tl, m + 1, h => by
      have h' : SortTelA m (instantiate0A x B) := by
        rw [instantiate0A_eq_substA_cons]; exact sortTelA_substA m B _ h
      exact congrArg Nat.succ (argsTyA_sortTelA_length tl m h')

/-- a constructor view's directly recursive fields carry the full index list. -/
theorem CtorViewA.drec_length {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm cm : CheckedMemberA}
    {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm) :
    ∀ idx, FieldA.drec idx ∈ v.fields → idx.length = fv.indices.length := by
  suffices h : ∀ {Γ : LCtxA} {k : Nat} {fs : List FieldA} {res : List ExprA},
      FieldsTyA E I fm.arity (fun k => liftA 0 k fv.idxTelA) Γ k fs res →
      ∀ idx, FieldA.drec idx ∈ fs → idx.length = fv.indices.length from h v.typed
  intro Γ k fs res hfs
  induction hfs with
  | nil => intro idx h; cases h
  | plain _ _ D u fs res _ _ ih =>
      intro idx h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact ih idx h
  | drec Γ k idx' fs res hidx _ ih =>
      intro idx h
      rcases List.mem_cons.mp h with h | h
      · cases h
        exact argsTyA_sortTelA_length hidx _
          (sortTelA_liftA _ _ 0 k (sortTelA_piTelA fv.sort (.succ fv.sort) fv.indices))
      · exact ih idx h
  | frec _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro idx h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact ih idx h
  | drecD _ _ _ _ _ _ _ _ ih =>
      intro idx h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact ih idx h

/-- `norm` and `instLevels` commute: normalizing a `.drecD` only drops its surface domain, and
    level instantiation never touches the norm boundary. -/
theorem FieldA.instLevels_norm (ls : List Level) : (x : FieldA) →
    (x.norm).instLevels ls = (x.instLevels ls).norm
  | .plain _ _ => rfl
  | .drec _ => rfl
  | .frec _ _ _ _ => rfl
  | .drecD _ _ => rfl

theorem map_instLevels_norm (ls : List Level) (fs : List FieldA) :
    (fs.map (FieldA.instLevels ls)).map FieldA.norm = (fs.map FieldA.norm).map (FieldA.instLevels ls) := by
  induction fs with
  | nil => rfl
  | cons x fs ih => simp only [List.map_cons, FieldA.instLevels_norm, ih]

/-- a `.drec` in the normalized constructor fields comes from either a `.drec` or a `.drecD` in
    the raw fields; both carry their index telescope's typing, so the length bound still holds. -/
theorem CtorViewA.drec_length_norm {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm cm : CheckedMemberA}
    {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm) :
    ∀ idx, FieldA.drec idx ∈ v.fields.map FieldA.norm → idx.length = fv.indices.length := by
  suffices h : ∀ {Γ : LCtxA} {k : Nat} {fs : List FieldA} {res : List ExprA},
      FieldsTyA E I fm.arity (fun k => liftA 0 k fv.idxTelA) Γ k fs res →
      ∀ idx, FieldA.drec idx ∈ fs.map FieldA.norm → idx.length = fv.indices.length from h v.typed
  intro Γ k fs res hfs
  induction hfs with
  | nil => intro idx h; cases h
  | plain _ _ D u fs res _ _ ih =>
      intro idx h
      rw [List.map_cons] at h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact ih idx h
  | drec Γ k idx' fs res hidx _ ih =>
      intro idx h
      rw [List.map_cons] at h
      rcases List.mem_cons.mp h with h | h
      · simp only [FieldA.norm] at h
        cases h
        exact argsTyA_sortTelA_length hidx _
          (sortTelA_liftA _ _ 0 k (sortTelA_piTelA fv.sort (.succ fv.sort) fv.indices))
      · exact ih idx h
  | frec _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro idx h
      rw [List.map_cons] at h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact ih idx h
  | drecD Γ k D idx' fs res hidx _ ih =>
      intro idx h
      rw [List.map_cons] at h
      rcases List.mem_cons.mp h with h | h
      · simp only [FieldA.norm] at h
        cases h
        exact argsTyA_sortTelA_length hidx _
          (sortTelA_liftA _ _ 0 k (sortTelA_piTelA fv.sort (.succ fv.sort) fv.indices))
      · exact ih idx h


/-- the result indices of plain fields typed along an index telescope have its length. -/
theorem fieldsTyA_plain_idx_length {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {idxTel : Nat → ExprA}
    {N : Nat} (hN : ∀ k, SortTelA N (idxTel k)) :
    (ds : List (ExprA × Level)) → {Γ : LCtxA} → {k : Nat} → {res : List ExprA} →
    FieldsTyA E I n idxTel Γ k (ds.map plainA) res → res.length = N
  | [], _, k, _, h => by
      simp only [List.map] at h
      cases h with
      | nil _ _ _ hres => exact argsTyA_sortTelA_length hres N (hN k)
  | (D, u) :: ds, _, _, _, h => by
      simp only [List.map, plainA] at h
      cases h with
      | plain _ _ _ _ _ _ hD tl => exact fieldsTyA_plain_idx_length hN ds tl

/-- a constructor view's function-recursive fields carry the full index list. -/
theorem CtorViewA.frec_length {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm cm : CheckedMemberA}
    {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm) :
    ∀ B uB Bs idx, FieldA.frec B uB Bs idx ∈ v.fields → idx.length = fv.indices.length := by
  suffices h : ∀ {Γ : LCtxA} {k : Nat} {fs : List FieldA} {res : List ExprA},
      FieldsTyA E I fm.arity (fun k => liftA 0 k fv.idxTelA) Γ k fs res →
      ∀ B uB Bs idx, FieldA.frec B uB Bs idx ∈ fs → idx.length = fv.indices.length from h v.typed
  intro Γ k fs res hfs
  induction hfs with
  | nil => intro B uB Bs idx h; cases h
  | plain _ _ D u fs res _ _ ih =>
      intro B uB Bs idx h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact ih B uB Bs idx h
  | drec Γ k idx' fs res hidx _ ih =>
      intro B uB Bs idx h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact ih B uB Bs idx h
  | frec Γ k B₀ uB₀ Bs₀ idx₀ fs res hdom _ _ ih =>
      intro B uB Bs idx h
      rcases List.mem_cons.mp h with h | h
      · cases h
        exact fieldsTyA_plain_idx_length
          (fun k => sortTelA_liftA _ _ 0 k (sortTelA_piTelA fv.sort (.succ fv.sort) fv.indices))
          ((B₀, uB₀) :: Bs₀) hdom
      · exact ih B uB Bs idx h
  | drecD _ _ _ _ _ _ _ _ ih =>
      intro B uB Bs idx h
      rcases List.mem_cons.mp h with h | h
      · cases h
      · exact ih B uB Bs idx h

/-! ## (4) the group's family and constructors at the recursor's levels -/

/-- the canonical structural relation at the group's family. -/
abbrev FamLfpA (E : ResolvedEnvA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (f : Nat)
    (fm : CheckedMemberA) : CRelA :=
  LfpWA (FamPhiWA E (iotaIfaceA E) n Γ f fm (famRsA E (iotaIfaceA E) n ρ₀ k Γ)
    (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm) (famRsIA E (iotaIfaceA E) n ρ₀ k Γ)) []

/-- the function-recursive position's relation at the canonical fixed point (R-NoFunRec-1 step 1
    (1c-ε1)): the clause's `F` at the constructor `c` at `lsC`, the carrier's parameters `qs` and levels
    `lsD`, with the fixed point at every extension. -/
abbrev FamFunLfpA (E : ResolvedEnvA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (f : Nat)
    (fm : CheckedMemberA) (c : Nat) (lsC : List Level) (qs : List ExprA) (lsD : List Level) :
    Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop :=
  famFunRelA E (iotaIfaceA E) n Γ fm (innerRelsA (famRsIA E (iotaIfaceA E) n ρ₀ k Γ) [] c lsC) qs lsD
    (fun ρ' => LfpWA (FamPhiWA E (iotaIfaceA E) n Γ f fm (famRsA E (iotaIfaceA E) n ρ₀ k Γ)
      (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm) (famRsIA E (iotaIfaceA E) n ρ₀ k Γ)) ρ')

/-- THE RECURSOR'S INDUCTION PREDICATE at a carrier `D`: at any full index list (`ni` indices) whose
    family application at the recursor's parameters `qs` is a recursive domain of `D`'s fiber (at the
    recursor's family levels `lsF`), and any right indices related to them (the parameters with
    them, `qs'` on the right), the two recursor applications are related at the motive. -/
def RecIHA (E : ResolvedEnvA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (f r : Nat)
    (fm : CheckedMemberA) (ni : Nat) (lsF ls ls' : List Level) (mot : ExprA) (qs qs' pfx pfx' : List ExprA) :
    CRelA :=
  fun D y y' => ∀ (is₁ is₁' : List ExprA), is₁.length = ni →
    RecDomRelA E (iotaIfaceA E) n Γ f fm (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm []) lsF qs D
      (foldAppsA (.const f lsF) (qs ++ is₁)) →
    ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) (qs ++ is₁) (qs' ++ is₁') →
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA mot (is₁ ++ [y]))
      (foldAppsA (.const r ls) (pfx ++ is₁ ++ [y])) (foldAppsA (.const r ls') (pfx' ++ is₁' ++ [y']))

/-- the recursor's induction predicate at every world (R-NoFunRec-1 step 1 (1c-ε1)): at a world `ρ`,
    `RecIHA` in the weakened context with the motive, the parameters and the prefixes weakened there. -/
def RecIHWA (E : ResolvedEnvA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (f r : Nat)
    (fm : CheckedMemberA) (ni : Nat) (lsF ls ls' : List Level) (mot : ExprA) (qs qs' pfx pfx' : List ExprA) :
    WkSpecA → CRelA :=
  fun ρ => RecIHA E n ρ₀ k (wkCtxA ρ Γ) f r fm ni lsF ls ls' (wkExprA ρ mot) (qs.map (wkExprA ρ))
    (qs'.map (wkExprA ρ)) (pfx.map (wkExprA ρ)) (pfx'.map (wkExprA ρ))

theorem recIHWA_nil (E : ResolvedEnvA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (f r : Nat)
    (fm : CheckedMemberA) (ni : Nat) (lsF ls ls' : List Level) (mot : ExprA) (qs qs' pfx pfx' : List ExprA) :
    RecIHWA E n ρ₀ k Γ f r fm ni lsF ls ls' mot qs qs' pfx pfx' [] =
      RecIHA E n ρ₀ k Γ f r fm ni lsF ls ls' mot qs qs' pfx pfx' := by
  simp only [RecIHWA, wkCtxA, wkExprA, List.map_id']

/-- the predicate at a weakened context reads the original's at the composed world. -/
theorem recIHWA_wk (E : ResolvedEnvA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (f r : Nat)
    (fm : CheckedMemberA) (ni : Nat) (lsF ls ls' : List Level) (mot : ExprA) (qs qs' pfx pfx' : List ExprA)
    (σ ρ' : WkSpecA) :
    RecIHWA E n ρ₀ k (wkCtxA σ Γ) f r fm ni lsF ls ls' (wkExprA σ mot) (qs.map (wkExprA σ))
      (qs'.map (wkExprA σ)) (pfx.map (wkExprA σ)) (pfx'.map (wkExprA σ)) ρ' =
    RecIHWA E n ρ₀ k Γ f r fm ni lsF ls ls' mot qs qs' pfx pfx' (WkSpecA.comp σ ρ') := by
  simp only [RecIHWA, wkCtxA_comp, wkExprA_comp, map_wkExprA_comp]

/-- the function-recursive position's relation under the induction: the clause's `F` whose pairs at every
    extension satisfy the predicate at that world (`RecIHWA`) and are in the fixed point. -/
abbrev FamFunIHA (E : ResolvedEnvA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (f r : Nat)
    (fm : CheckedMemberA) (ni : Nat) (lsF ls ls' : List Level) (mot : ExprA) (qs qs' pfx pfx' : List ExprA)
    (c : Nat) (lsC : List Level) (ps : List ExprA) (lsD : List Level) :
    Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop :=
  famFunRelA E (iotaIfaceA E) n Γ fm (innerRelsA (famRsIA E (iotaIfaceA E) n ρ₀ k Γ) [] c lsC) ps lsD
    (fun ρ' D y y' => RecIHWA E n ρ₀ k Γ f r fm ni lsF ls ls' mot qs qs' pfx pfx' ρ' D y y' ∧
      LfpWA (FamPhiWA E (iotaIfaceA E) n Γ f fm (famRsA E (iotaIfaceA E) n ρ₀ k Γ)
        (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm) (famRsIA E (iotaIfaceA E) n ρ₀ k Γ)) ρ' D y y')

/-- the core induction's motive (R-NoFunRec-1 step 1 (1c-ε1)): at a world, the predicate there (at a
    well-formed one) with the fixed point beside it. -/
abbrev RecCoreA (E : ResolvedEnvA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (f r : Nat)
    (fm : CheckedMemberA) (ni : Nat) (lsF ls ls' : List Level) (mot mot' : ExprA) (qs qs' ms ms' : List ExprA) :
    WkSpecA → CRelA :=
  fun ρ D y y' =>
    (WkOkA E (iotaIfaceA E) n ρ Γ → RecIHWA E n ρ₀ k Γ f r fm ni lsF ls ls' mot qs qs' (qs ++ [mot] ++ ms)
      (qs' ++ [mot'] ++ ms') ρ D y y') ∧
    LfpWA (FamPhiWA E (iotaIfaceA E) n Γ f fm (famRsA E (iotaIfaceA E) n ρ₀ k Γ)
      (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm) (famRsIA E (iotaIfaceA E) n ρ₀ k Γ)) ρ D y y'

section GroupAt
variable {E₀ E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
  {cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)}

/-- a group constructor's telescope after parameters `qs`, off the NORMED type
    (R-NoDeltaRec-4d-iii): a δ-reached field's domain reads as the family application there. -/
theorem RecBaseA.ctorTel (_C : RecBaseA E₀ E n ρ₀ f fm fv cs) (gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv)
    (lsX : List Level) (hl : lsX.length = fm.arity) {qs : List ExprA} (hqs : qs.length = fm.nparamsA) :
    applyTelA qs (instantiateLevelsA lsX (gc.member.normA.getD gc.member.mtypeA)) =
      some (ctorFieldsA f lsX (instLevel lsX fv.sort) qs (consListA qs SubstA.id)
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsX))
        (gc.view.res.map (instantiateLevelsA lsX))).1 :=
  gc.applyTel_params lsX hl qs hqs

/-- a group constructor's telescope after a prefix of its fields, generic over the walked
    fields list `fsAll` — the raw `gc.view.fields` or its `map FieldA.norm` image
    (R-NoDeltaRec-4d-iii). -/
theorem applyTelA_groupCtor_prefix (gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv) (lsX : List Level)
    {fsAll fsPre fsRest : List FieldA} (hfs : fsAll = fsPre ++ fsRest) {pre : List ExprA}
    (hpre : pre.length = fsPre.length) (pl : List ExprA) (σ : SubstA) :
    applyTelA pre (ctorFieldsA f lsX (instLevel lsX fv.sort) pl σ (fsAll.map (FieldA.instLevels lsX))
        (gc.view.res.map (instantiateLevelsA lsX))).1 =
      some (ctorFieldsA f lsX (instLevel lsX fv.sort) pl (consListA (plainArgsA fsPre pre) σ)
        (fsRest.map (FieldA.instLevels lsX)) (gc.view.res.map (instantiateLevelsA lsX))).1 := by
  rw [hfs, List.map_append]
  have h := applyTelA_ctorFieldsA_prefix f lsX (instLevel lsX fv.sort) (gc.view.res.map (instantiateLevelsA lsX))
    (fsRest.map (FieldA.instLevels lsX)) (fsPre.map (FieldA.instLevels lsX)) pre (by rw [List.length_map, hpre]) pl σ
  rw [plainArgsA_instLevels] at h
  exact h

theorem RecBaseA.famWhnf (C : RecBaseA E₀ E n ρ₀ f fm fv cs) (Γ : LCtxA) (lsX : List Level) (xs : List ExprA) :
    hStepFnA E (iotaIfaceA E).fn Γ (foldAppsA (.const f lsX) xs) = none :=
  hStepFnA_constSpine_none (iotaFnA_recHead E) C.hfm (Or.inr C.hnobody)
    (by rw [C.hcls]; exact fun h => MemberClass.noConfusion h) Γ (ls := lsX) _ (by rw [foldAppsA_const_head])

theorem RecBaseA.famNotProp (C : RecBaseA E₀ E n ρ₀ f fm fv cs) (Γ : LCtxA) (lsX : List Level) (xs : List ExprA) :
    ¬ IsPropTy E (iotaIfaceA E) Γ (foldAppsA (.const f lsX) xs) := fun h => by
  have h3 := ((isPropTy_famApp_iff C.hfm fv.piBody lsX xs).mp h).2.2
  rw [isZero_false_of_uniformType (uniformType_instLevel C.hUT lsX)] at h3
  cases h3

/-- at a valid family application, the canonical fixed point IS the relation. -/
theorem RecBaseA.lrRel (C : RecBaseA E₀ E n ρ₀ f fm fv cs) {k : Nat} {Γ : LCtxA} {lsX : List Level}
    {qs is : List ExprA} (hqs : qs.length = fm.nparamsA) {R : ExprA → ExprA → Prop}
    (hR : LRTyA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f lsX) (qs ++ is)) R) {a b : ExprA}
    (h : FamLfpA E n ρ₀ k Γ f fm (foldAppsA (.const f lsX) (qs ++ is)) a b) :
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f lsX) (qs ++ is)) a b := by
  refine ⟨R, hR, ?_⟩
  rw [lrTyA_fam_canon C.hE C.hEN C.hfm C.hcls hqs (C.famWhnf Γ lsX _) (C.famNotProp Γ lsX _) hR]
  exact h

/-- THE FIELD BINDER OF A FUNCTION-RECURSIVE POSITION (R-NoFunRec-1 step 1 (1c-ε2d)): along a walk at the
    group constructor's levels `lsC` and the carrier's parameters `qs`, a pair of the clause's
    `famFunRelA` at a function-recursive field's domain there, with the output in the fixed point, is
    related at the field's domain at the recursor's levels `lsF`. The two domains are equal and valid
    (`frecDomEq` on the walk's diagonal); at the first the pair is related (`lrRelA_of_famFunRelA`), at
    the second by transport. -/
theorem RecBaseA.frecFieldRel (C : RecBaseA E₀ E n ρ₀ f fm fv cs) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ))
    {lsF lsC lsD : List Level} (hbF : levelsBounded n lsF = true) (hlF : lsF.length = fm.arity)
    (hk : ht ρ₀ (instLevel lsF fv.sort) ≤ k) (hFC : eqNListB n lsF lsC)
    {qs : List ExprA} (hqs : qs.length = fm.nparamsA)
    (hqd : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) (qs ++ []) (qs ++ []))
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgcE : E.members gc.ref = some gc.member)
    {ksPre ks : List FieldShape} {jn : Nat}
    (hsp : gc.view.fields.map FieldA.shape = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {pre pre' : List ExprA}
    (hpl : pre.length = ksPre.length)
    {T : ExprA} (hTvC : applyTelA qs (instantiateLevelsA lsC (gc.member.normA.getD gc.member.mtypeA)) = some T)
    {TF : ExprA} (hTvF : applyTelA qs (instantiateLevelsA lsF (gc.member.normA.getD gc.member.mtypeA)) = some TF)
    (hwC : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC) X F fm.nparamsA qs T ksPre pre pre')
    {AC : ExprA} {uC : Level} {BC : ExprA} {vC : Level} (hTD_C : applyTelA pre T = some (.pi AC uC BC vC))
    {AF : ExprA} {uF : Level} {BF : ExprA} {vF : Level} (hTD_F : applyTelA pre TF = some (.pi AF uF BF vF))
    {XF : WkSpecA → CRelA}
    (hX : ∀ ρ' D y y', XF ρ' D y y' → LfpWA (FamPhiWA E (iotaIfaceA E) n Γ f fm
      (famRsA E (iotaIfaceA E) n ρ₀ k Γ) (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm)
      (famRsIA E (iotaIfaceA E) n ρ₀ k Γ)) ρ' D y y')
    {x x' : ExprA}
    (hF : famFunRelA E (iotaIfaceA E) n Γ fm (innerRelsA (famRsIA E (iotaIfaceA E) n ρ₀ k Γ) [] gc.ref lsC)
      qs lsD XF (fm.nparamsA + ksPre.length) (qs ++ pre) AC jn x x') :
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ AF x x' := by
  have hlC : lsC.length = fm.arity := (eqNListA_length hFC.1).symm.trans hlF
  have hkinds := gc.view.shapes C.hfresh
  have hkinds' : ctorShapesA f fm.nparamsA (gc.member.normA.getD gc.member.mtypeA) =
      some (ksPre ++ FieldShape.recursive (jn + 1) :: ks) := by
    rw [gc.normA_getD, ← hsp]; exact hkinds
  have hqd' := argsRelKA_refl_left C.hNCT hqd
  obtain ⟨heq, hvC, _⟩ := RecBaseA.frecDomEq C hbF hlF hk (k := k) hΓ hqs hqs hqd (ρ := []) (Or.inl rfl)
    hgcE gc.hcls gc.view.famRef hkinds' rfl (eqNListA_refl lsF) hFC (eqNListB_symm hFC hbF)
    (by rw [map_wkExprA_nil]; exact hTvC) (by rw [map_wkExprA_nil]; exact hTvF)
    (by rw [map_wkExprA_nil]; exact argsRelA_diag C.hNCT (famRsA_refl_left C.hNCT) hwC) hTD_C hTD_F
  have hrel := lrRelA_of_famFunRelA C.hE C.hI C.hR C.hNCT C.hEN C.hfm C.hcls C.hnobody C.hfresh C.hcensus C.hUT hlC hΓ
    hgcE gc.hcls gc.view.famRef hkinds' rfl hqs hTvC hpl hTD_C hvC hX hF
  exact LRRelA_transport' C.hNCT heq hrel

/-- THE INNER BINDERS OF THE TWO REDUCTS' FUNCTION-RECURSIVE DOMAINS CONVERT BINDERWISE (R-NoFunRec-1 step 1
    (1c-ε2d-L3b-2)): along the walk at the recursor's levels on the left (parameters `qs`) and on the
    right (`qs'`, `lsF'`), the two domains' binders are pairwise convertible, each at its own sort
    (`frecDomConvCoreA`, from the base binders' typing in the group environment). -/
theorem RecBaseA.frecTelConv (C : RecBaseA E₀ E n ρ₀ f fm fv cs) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ))
    {lsF lsF' : List Level} (hbF : levelsBounded n lsF = true) (hlF : lsF.length = fm.arity)
    (hFF : eqNListB n lsF lsF')
    {qs qs' : List ExprA} (hqs : qs.length = fm.nparamsA) (hqs' : qs'.length = fm.nparamsA)
    (hqq : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) (qs ++ []) (qs' ++ []))
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgcE : E.members gc.ref = some gc.member)
    {ksPre ks : List FieldShape} {jn : Nat}
    (hsp : gc.view.fields.map FieldA.shape = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    {pre pre' : List ExprA} {TF TR : ExprA}
    (hTvF : applyTelA qs (instantiateLevelsA lsF (gc.member.normA.getD gc.member.mtypeA)) = some TF)
    (hTvR : applyTelA qs' (instantiateLevelsA lsF' (gc.member.normA.getD gc.member.mtypeA)) = some TR)
    (hwF : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsF) (fun _ _ _ => True)
      (fun _ _ _ _ _ _ => True) fm.nparamsA qs TF ksPre pre pre')
    {AF AR : ExprA} {uF uR : Level} {BF BR : ExprA} {vF vR : Level}
    (hTD_F : applyTelA pre TF = some (.pi AF uF BF vF))
    (hTD_R : applyTelA pre' TR = some (.pi AR uR BR vR)) :
    TelConvA E (iotaIfaceA E) n Γ (piDomListA AF) (piDomListA AR) := by
  have hkinds := gc.view.shapes C.hfresh
  have hkinds' : ctorShapesA f fm.nparamsA (gc.member.normA.getD gc.member.mtypeA) =
      some (ksPre ++ FieldShape.recursive (jn + 1) :: ks) := by
    rw [← hsp]; exact gc.normA_getD ▸ hkinds
  exact (frecDomConvCoreA (fv := fv) (cs := cs) C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀
    C.hEL₀ C.hEL C.hIL (iotaFnA_subst C.hE C.hEN) C.hR C.hfresh C.hcensus C.hcl C.hT C.hpre₀G C.hpreG
    C.hmemG hbF hlF hΓ hqs hqs'
    hqq (ρ := [])
    (Or.inl rfl) hgcE gc.hcls gc.view.famRef hkinds' rfl (eqNListA_refl lsF) (eqNListB_refl hbF) hFF
    (by rw [map_wkExprA_nil]; exact hTvF) (by rw [map_wkExprA_nil]; exact hTvR)
    (by rw [map_wkExprA_nil]; exact hwF) hTD_F hTD_R).2

/-- THE INDUCTION HYPOTHESIS AT AN ARBITRARY WORLD AND RELATED ARGUMENTS (R-NoFunRec-1 step 1
    (1c-ε2d-L3b-3c)): `frecCallRel` for the pair's `RecIHWA` at a world `ρ` and arguments `as`, `as'`
    related along the weakened domain, the two calls and the motive instance read under the arguments
    and the weakening substitution. -/
theorem RecBaseA.frecCallRelAt (C : RecBaseA E₀ E n ρ₀ f fm fv cs) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ))
    {lsF lsF' lsC lsD : List Level} (hbF : levelsBounded n lsF = true) (hlF : lsF.length = fm.arity)
    (hFF : eqNListB n lsF lsF') (hk : ht ρ₀ (instLevel lsF fv.sort) ≤ k) (hFC : eqNListB n lsF lsC)
    {qs qs' : List ExprA} (hqs : qs.length = fm.nparamsA) (hqs' : qs'.length = fm.nparamsA)
    (hqq : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) (qs ++ []) (qs' ++ []))
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgcE : E.members gc.ref = some gc.member)
    {ksPre ks : List FieldShape} {jn : Nat}
    (hsp : gc.view.fields.map FieldA.shape = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    {pre pre' : List ExprA}
    {T TF TR : ExprA} (hTvC : applyTelA qs (instantiateLevelsA lsC (gc.member.normA.getD gc.member.mtypeA)) = some T)
    (hTvF : applyTelA qs (instantiateLevelsA lsF (gc.member.normA.getD gc.member.mtypeA)) = some TF)
    (hTvR : applyTelA qs' (instantiateLevelsA lsF' (gc.member.normA.getD gc.member.mtypeA)) = some TR)
    {r : Nat} {ls ls' : List Level} {mot : ExprA} {pfx pfx' : List ExprA}
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    (hwC : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC) X F fm.nparamsA qs T ksPre pre pre')
    (hwF : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsF) (fun _ _ _ => True)
      (fun _ _ _ _ _ _ => True) fm.nparamsA qs TF ksPre pre pre')
    {dsC dsF dsR : List (ExprA × Level)} {iC iF iR : List ExprA} {wC wF wR : Level}
    {uC uF uR : Level} {BC BF BR : ExprA} {vC vF vR : Level}
    (hTD_C : applyTelA pre T = some (.pi (piTelA dsC (foldAppsA (.const f lsC)
      (qs.map (liftNA dsC.length) ++ iC)) wC).1 uC BC vC))
    (hTD_F : applyTelA pre TF = some (.pi (piTelA dsF (foldAppsA (.const f lsF)
      (qs.map (liftNA dsF.length) ++ iF)) wF).1 uF BF vF))
    (hTD_R : applyTelA pre' TR = some (.pi (piTelA dsR (foldAppsA (.const f lsF')
      (qs'.map (liftNA dsR.length) ++ iR)) wR).1 uR BR vR))
    (hdC : dsC.length = jn + 1) (hdF : dsF.length = jn + 1) (hdR : dsR.length = jn + 1)
    (hwF₀ : isZero wF = false) (hwC₀ : isZero wC = false)
    {v v' : ExprA}
    (hh : FamFunIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' gc.ref lsC qs lsD
      (fm.nparamsA + ksPre.length) (qs ++ pre) (piTelA dsC (foldAppsA (.const f lsC)
      (qs.map (liftNA dsC.length) ++ iC)) wC).1 jn v v')
    (hdl : iF.length = fv.indices.length) {ρ : WkSpecA} (hρ : WkOkA E (iotaIfaceA E) n ρ Γ)
    {as as' : List ExprA} (hl : as.length = dsF.length)
    (hKF : ArgsRelKA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ) (substA (wkSubstA ρ) (piTelA dsF
      (foldAppsA (.const f lsF) (qs.map (liftNA dsF.length) ++ iF)) wF).1) as as') :
    LRRelA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ)
      (substA (consListA as (wkSubstA ρ)) (foldAppsA (liftNA dsF.length mot)
        (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])))
      (substA (consListA as (wkSubstA ρ)) (foldAppsA (.const r ls) (pfx.map (liftNA dsF.length) ++ iF ++
        [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])))
      (substA (consListA as' (wkSubstA ρ)) (foldAppsA (.const r ls') (pfx'.map (liftNA dsF.length) ++ iR ++
        [foldAppsA (liftNA dsF.length v') (paramLocalsA dsF.length)]))) := by
  have hlC : lsC.length = fm.arity := (eqNListA_length hFC.1).symm.trans hlF
  have hkinds := gc.view.shapes C.hfresh
  have hkinds' : ctorShapesA f fm.nparamsA (gc.member.normA.getD gc.member.mtypeA) =
      some (ksPre ++ FieldShape.recursive (jn + 1) :: ks) := by
    rw [← hsp]; exact gc.normA_getD ▸ hkinds
  have hqd := argsRelKA_refl_left C.hNCT hqq
  have hmC : dsC.length = dsF.length := hdC.trans hdF.symm
  have hmR : dsR.length = dsF.length := hdR.trans hdF.symm
  obtain ⟨heqCF, hvC, hvF'⟩ := RecBaseA.frecDomEq C hbF hlF hk (k := k) hΓ hqs hqs hqd (ρ := []) (Or.inl rfl)
    hgcE gc.hcls gc.view.famRef hkinds' rfl (eqNListA_refl lsF) hFC (eqNListB_symm hFC hbF)
    (by rw [map_wkExprA_nil]; exact hTvC) (by rw [map_wkExprA_nil]; exact hTvF)
    (by rw [map_wkExprA_nil]; exact argsRelA_diag C.hNCT (famRsA_refl_left C.hNCT) hwC) hTD_C hTD_F
  have heq := LREqA_symm C.hNCT heqCF
  have hl' : as'.length = dsF.length := (argsRelKA_length hKF).symm.trans hl
  have hKF₀ : ArgsRelKA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ (piTelA dsF
      (foldAppsA (.const f lsF) (qs.map (liftNA dsF.length) ++ iF)) wF).1) as as' := by
    rw [wkExprA_eq_substA]; exact hKF
  have hq := LREqA_wk C.hE C.hEN C.hI heq ρ hρ
  have hACpi : IsPiTelA dsF.length (wkExprA ρ (piTelA dsC (foldAppsA (.const f lsC)
      (qs.map (liftNA dsC.length) ++ iC)) wC).1) := by
    rw [← hmC]; exact isPiTelA_wk_piTelA _ wC hwC₀ dsC ρ
  have hKC := argsRelKA_of_lrEqA C.hNCT hρ.2 hKF₀ (isPiTelA_wk_piTelA _ wF hwF₀ dsF ρ) hACpi
    (by rw [hl]; exact Nat.le_refl _) hq
  have hKCd := argsRelKA_refl_left C.hNCT hKC
  have hTfullC : applyTelA (qs ++ pre) (instantiateLevelsA lsC (gc.member.normA.getD
      gc.member.mtypeA)) =
      some (.pi (piTelA dsC (foldAppsA (.const f lsC) (qs.map (liftNA dsC.length) ++ iC)) wC).1 uC BC
        vC) := by
    rw [applyTelA_append, hTvC]; exact hTD_C
  have hTfullF : applyTelA (qs ++ pre) (instantiateLevelsA lsF (gc.member.normA.getD
      gc.member.mtypeA)) =
      some (.pi (piTelA dsF (foldAppsA (.const f lsF) (qs.map (liftNA dsF.length) ++ iF)) wF).1 uF BF
        vF) := by
    rw [applyTelA_append, hTvF]; exact hTD_F
  have hP₁ := argsRelKA_innerRelsA_PA (ρ := []) (ρ' := ρ) (i := fm.nparamsA + ksPre.length)
    (ii := 0) (iprev := []) C.hE hgcE gc.normA_getD_closed hTfullC hKC rfl
  have hP₁d := argsRelKA_innerRelsA_PA (ρ := []) (ρ' := ρ) (i := fm.nparamsA + ksPre.length)
    (ii := 0) (iprev := []) C.hE hgcE gc.normA_getD_closed hTfullC hKCd rfl
  have hPF := argsRelKA_innerRelsA_PA (ρ := []) (ρ' := ρ) (i := fm.nparamsA + ksPre.length)
    (ii := 0) (iprev := []) C.hE hgcE gc.normA_getD_closed hTfullF hKF₀ rfl
  have hCC : applyTelA as (wkExprA ρ (piTelA dsC (foldAppsA (.const f lsC)
      (qs.map (liftNA dsC.length) ++ iC)) wC).1) =
      some (substA (consListA as (wkSubstA ρ)) (foldAppsA (.const f lsC)
        (qs.map (liftNA dsC.length) ++ iC))) :=
    applyTelA_wk_piTelA _ wC dsC ρ as (hl.trans hmC.symm)
  have hCF : applyTelA as (wkExprA ρ (piTelA dsF (foldAppsA (.const f lsF)
      (qs.map (liftNA dsF.length) ++ iF)) wF).1) =
      some (substA (consListA as (wkSubstA ρ)) (foldAppsA (.const f lsF)
        (qs.map (liftNA dsF.length) ++ iF))) :=
    applyTelA_wk_piTelA _ wF dsF ρ as hl
  have hCR : applyTelA as' (wkExprA ρ (piTelA dsR (foldAppsA (.const f lsF')
      (qs'.map (liftNA dsR.length) ++ iR)) wR).1) =
      some (substA (consListA as' (wkSubstA ρ)) (foldAppsA (.const f lsF')
        (qs'.map (liftNA dsR.length) ++ iR))) :=
    applyTelA_wk_piTelA _ wR dsR ρ as' (hl'.trans hmR.symm)
  have hX := hh.1 ρ hρ as as' _ hP₁ (by rw [hl, hdF]) hCC
  obtain ⟨-, -, hRecIH, -⟩ := hX
  have hRD₀ := frecInnerRecWorldA (X := fun _ _ _ _ _ => True) (F := fun _ _ _ _ _ _ _ _ _ _ => True)
    C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hS C.hfm C.hcls C.hfresh C.hcensus C.hcl C.hT C.hUT
    hbF hlF hk (k := k) hΓ hqs hqs hqd [] (Or.inl rfl) gc.ref gc.member lsF lsC lsF
    (ksPre ++ FieldShape.recursive (jn + 1) :: ks) ksPre ks jn T TF pre pre _ _ _ _ _ _ _ _
    hgcE gc.hcls gc.view.famRef hkinds' rfl (eqNListA_refl lsF) hFC (eqNListB_symm hFC hbF)
    (by rw [map_wkExprA_nil]; exact hTvC) (by rw [map_wkExprA_nil]; exact hTvF)
    (by rw [map_wkExprA_nil]; exact argsRelA_diag C.hNCT (famRsA_refl_left C.hNCT) hwC) hTD_C hTD_F
    ρ hρ _ _ _ _ (by rw [map_wkExprA_nil]; exact hP₁d) (hl.trans hdF) hCC hCF
  have hwk : ∀ xs : List ExprA, xs.map (substA (wkSubstA ρ)) = xs.map (wkExprA ρ) := fun xs =>
    List.map_congr_left (fun e _ => (wkExprA_eq_substA ρ e).symm)
  have hshF : substA (consListA as (wkSubstA ρ)) (foldAppsA (.const f lsF)
      (qs.map (liftNA dsF.length) ++ iF)) =
      foldAppsA (.const f lsF) (qs.map (wkExprA ρ) ++ iF.map (substA (consListA as (wkSubstA ρ)))) := by
    rw [← hl, substA_famBody, hwk]
  have hshR : substA (consListA as' (wkSubstA ρ)) (foldAppsA (.const f lsF')
      (qs'.map (liftNA dsR.length) ++ iR)) =
      foldAppsA (.const f lsF') (qs'.map (wkExprA ρ) ++ iR.map (substA (consListA as' (wkSubstA ρ)))) := by
    rw [hmR, ← hl', substA_famBody, hwk]
  have hRD : RecDomRelA E (iotaIfaceA E) n (wkCtxA ρ Γ) f fm
      (famRsFA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ) fm []) lsF (qs.map (wkExprA ρ))
      (substA (consListA as (wkSubstA ρ)) (foldAppsA (.const f lsC) (qs.map (liftNA dsC.length) ++ iC)))
      (foldAppsA (.const f lsF) (qs.map (wkExprA ρ) ++ iF.map (substA (consListA as (wkSubstA ρ))))) := by
    rw [← hshF]
    simpa only [map_wkExprA_nil, famRsFA_wkCtx, WkSpecA.comp_nil, WkSpecA.comp] using hRD₀
  have hPF₂ : ArgsRelPA (innerRelsA (famRsIA E (iotaIfaceA E) n ρ₀ k Γ) [] gc.ref lsF
      (fm.nparamsA + ksPre.length) (qs.map (wkExprA []) ++ pre) ρ) 0 []
      (wkExprA ρ (piTelA dsF (foldAppsA (.const f lsF) (qs.map (liftNA dsF.length) ++ iF)) wF).1)
      as as' := by
    rw [map_wkExprA_nil]; exact hPF
  have hRR₀ := frecInnerRecWorldA (X := fun _ _ _ _ _ => True) (F := fun _ _ _ _ _ _ _ _ _ _ => True)
    C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hS C.hfm C.hcls C.hfresh C.hcensus C.hcl C.hT C.hUT
    hbF hlF hk (k := k) hΓ hqs hqs' hqq [] (Or.inl rfl) gc.ref gc.member lsF lsF lsF'
    (ksPre ++ FieldShape.recursive (jn + 1) :: ks) ksPre ks jn TF TR pre pre' _ _ _ _ _ _ _ _
    hgcE gc.hcls gc.view.famRef hkinds' rfl (eqNListA_refl lsF) (eqNListB_refl hbF) hFF
    (by rw [map_wkExprA_nil]; exact hTvF) (by rw [map_wkExprA_nil]; exact hTvR)
    (by rw [map_wkExprA_nil]; exact hwF) hTD_F hTD_R
    ρ hρ _ _ _ _ hPF₂ (hl.trans hdF) hCF hCR
  simp only [map_wkExprA_nil] at hRR₀
  obtain ⟨lsA, lsA', isA, isA', TF₁, TF₁', hA, hA', _, _, hTF₁, _, hwI, _⟩ := hRR₀
  rw [hshF] at hA
  rw [hshR] at hA'
  obtain ⟨_, elA, exA⟩ := foldAppsA_const_inj hA
  obtain ⟨_, elA', exA'⟩ := foldAppsA_const_inj hA'
  have exA₁ := List.append_cancel_left exA
  have exA₁' := List.append_cancel_left exA'
  subst elA elA' exA₁ exA₁'
  have hidxF := argsRelPA_famRsFA_KA hwI hTF₁
  have hqq' : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) qs qs' := by
    simpa only [List.append_nil] using hqq
  have hqq_w := argsRelKA_wk C.hE C.hI C.hEN ρ hρ hqq'
  rw [wkExprA_closed (liftA_instantiateLevelsA_closed C.hcl lsF)] at hqq_w
  have hidx := argsRelKA_append hqq_w hTF₁ hidxF
  have hfin := hRecIH _ _ (by rw [List.length_map]; exact hdl) hRD hidx
  have eB := substA_motBody mot iF v as (wkSubstA ρ)
  have eL := substA_recBody r ls pfx iF v as (wkSubstA ρ)
  have eR := substA_recBody r ls' pfx' iR v' as' (wkSubstA ρ)
  rw [hl] at eB eL
  rw [hl'] at eR
  rw [eB, eL, eR]
  simpa only [hwk, ← wkExprA_eq_substA] using hfin


/-- THE INDUCTION HYPOTHESIS AT THE EXTENSION WORLD OF A FUNCTION-RECURSIVE FIELD'S INNER BINDERS
    (R-NoFunRec-1 step 1 (1c-ε2d-L3b-2)). A pair of the clause's function-recursive relation at the field's
    domain `AC` (at the constructor's levels `lsC`), at the world of the inner binders of the field's
    domain `AF` at the recursor's levels, with the bound variables as the inner arguments (related to
    themselves, along `AC` by the equality `AF = AC`): the pair's `RecIHWA` there, at the indices the two
    reducts read (`AF`'s on the left, `AR`'s on the right: related as recursive domains by
    `frecInnerRecWorldA`), relates the two direct calls at the motive. -/
theorem RecBaseA.frecCallRel (C : RecBaseA E₀ E n ρ₀ f fm fv cs) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ))
    {lsF lsF' lsC lsD : List Level} (hbF : levelsBounded n lsF = true) (hlF : lsF.length = fm.arity)
    (hFF : eqNListB n lsF lsF') (hk : ht ρ₀ (instLevel lsF fv.sort) ≤ k) (hFC : eqNListB n lsF lsC)
    {qs qs' : List ExprA} (hqs : qs.length = fm.nparamsA) (hqs' : qs'.length = fm.nparamsA)
    (hqq : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) (qs ++ []) (qs' ++ []))
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgcE : E.members gc.ref = some gc.member)
    {ksPre ks : List FieldShape} {jn : Nat}
    (hsp : gc.view.fields.map FieldA.shape = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    {pre pre' : List ExprA}
    {T TF TR : ExprA} (hTvC : applyTelA qs (instantiateLevelsA lsC (gc.member.normA.getD gc.member.mtypeA)) = some T)
    (hTvF : applyTelA qs (instantiateLevelsA lsF (gc.member.normA.getD gc.member.mtypeA)) = some TF)
    (hTvR : applyTelA qs' (instantiateLevelsA lsF' (gc.member.normA.getD gc.member.mtypeA)) = some TR)
    {r : Nat} {ls ls' : List Level} {mot : ExprA} {pfx pfx' : List ExprA}
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    (hwC : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC) X F fm.nparamsA qs T ksPre pre pre')
    (hwF : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsF) (fun _ _ _ => True)
      (fun _ _ _ _ _ _ => True) fm.nparamsA qs TF ksPre pre pre')
    {dsC dsF dsR : List (ExprA × Level)} {iC iF iR : List ExprA} {wC wF wR : Level}
    {uC uF uR : Level} {BC BF BR : ExprA} {vC vF vR : Level}
    (hTD_C : applyTelA pre T = some (.pi (piTelA dsC (foldAppsA (.const f lsC)
      (qs.map (liftNA dsC.length) ++ iC)) wC).1 uC BC vC))
    (hTD_F : applyTelA pre TF = some (.pi (piTelA dsF (foldAppsA (.const f lsF)
      (qs.map (liftNA dsF.length) ++ iF)) wF).1 uF BF vF))
    (hTD_R : applyTelA pre' TR = some (.pi (piTelA dsR (foldAppsA (.const f lsF')
      (qs'.map (liftNA dsR.length) ++ iR)) wR).1 uR BR vR))
    (hdC : dsC.length = jn + 1) (hdF : dsF.length = jn + 1) (hdR : dsR.length = jn + 1)
    (hwF₀ : isZero wF = false) (hwC₀ : isZero wC = false)
    {v v' : ExprA}
    (hh : FamFunIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' gc.ref lsC qs lsD
      (fm.nparamsA + ksPre.length) (qs ++ pre) (piTelA dsC (foldAppsA (.const f lsC)
      (qs.map (liftNA dsC.length) ++ iC)) wC).1 jn v v')
    (hvF : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (piTelA dsF (foldAppsA (.const f lsF)
      (qs.map (liftNA dsF.length) ++ iF)) wF).1 v v')
    (hdl : iF.length = fv.indices.length) :
    LRRelA E (iotaIfaceA E) n ρ₀ k (telCtxA dsF ++ Γ)
      (foldAppsA (liftNA dsF.length mot)
        (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)]))
      (foldAppsA (.const r ls) (pfx.map (liftNA dsF.length) ++ iF ++
        [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)]))
      (foldAppsA (.const r ls') (pfx'.map (liftNA dsF.length) ++ iR ++
        [foldAppsA (liftNA dsF.length v') (paramLocalsA dsF.length)])) := by
  have hkinds := gc.view.shapes C.hfresh
  have hkinds' : ctorShapesA f fm.nparamsA (gc.member.normA.getD gc.member.mtypeA) =
      some (ksPre ++ FieldShape.recursive (jn + 1) :: ks) := by
    rw [← hsp]; exact gc.normA_getD ▸ hkinds
  have hIC := iotaConstHeadA_of_recHead C.hR
  have hqd := argsRelKA_refl_left C.hNCT hqq
  obtain ⟨heqCF, -, -⟩ := RecBaseA.frecDomEq C hbF hlF hk (k := k) hΓ hqs hqs hqd (ρ := []) (Or.inl rfl)
    hgcE gc.hcls gc.view.famRef hkinds' rfl (eqNListA_refl lsF) hFC (eqNListB_symm hFC hbF)
    (by rw [map_wkExprA_nil]; exact hTvC) (by rw [map_wkExprA_nil]; exact hTvF)
    (by rw [map_wkExprA_nil]; exact argsRelA_diag C.hNCT (famRsA_refl_left C.hNCT) hwC) hTD_C hTD_F
  obtain ⟨R_F, hR_F⟩ := LRRelA_valid hvF
  obtain ⟨sF, ⟨tF⟩⟩ := LRTyA_hasTy hR_F
  obtain ⟨⟨tdsF⟩, -⟩ := telTyA_of_hasTy_piTelA _ wF dsF tF
  have hok : WkOkA E (iotaIfaceA E) n (telWorldA dsF) Γ := wkOkA_telWorldA tdsF hΓ
  have hAF_pi : IsPiTelA dsF.length (piTelA dsF (foldAppsA (.const f lsF)
      (qs.map (liftNA dsF.length) ++ iF)) wF).1 := isPiTelA_piTelA _ wF hwF₀ dsF
  have hKF := argsRelKA_bvarsA_of_lrEqA (ρ₀ := ρ₀) C.hE C.hEN C.hNCT C.hI hIC hΓ _ wF hwF₀ tF
    ⟨R_F, hR_F⟩ hAF_pi
    (LREqA_trans C.hNCT (LREqA_symm C.hNCT heqCF) heqCF)
  have hKF' : ArgsRelKA E (iotaIfaceA E) n ρ₀ k (wkCtxA (telWorldA dsF) Γ)
      (substA (wkSubstA (telWorldA dsF)) (piTelA dsF (foldAppsA (.const f lsF)
        (qs.map (liftNA dsF.length) ++ iF)) wF).1) (paramLocalsA dsF.length) (paramLocalsA dsF.length) := by
    rw [← wkExprA_eq_substA, wkCtxA_telWorldA, wkExprA_telWorldA]; exact hKF
  have h := RecBaseA.frecCallRelAt C hΓ hbF hlF hFF hk hFC hqs hqs' hqq hgcE hsp hTvC hTvF hTvR hwC hwF
    hTD_C hTD_F hTD_R hdC hdF hdR hwF₀ hwC₀ hh hdl hok (by rw [paramLocalsA_length]) hKF'
  rw [wkCtxA_telWorldA] at h
  simpa only [substA_consListA_telWorldA] using h

/-- THE λ-WRAPPED CALL AT A FUNCTION-RECURSIVE FIELD'S DOMAIN is the λ-telescope over the domain's binders
    around the direct call at the family's indices, the field applied to the bound variables. -/
theorem recCallFunA_frec (r : Nat) (ls : List Level) (pfx is₁ : List ExprA) (np nm : Nat)
    (hpfx : pfx.length = np + 1 + nm) (v : ExprA) (ds : List (ExprA × Level)) (lsF : List Level)
    (pl idx : List ExprA) (hpl : pl.length = np) (w : Level) :
    recCallFunA (.const r ls) (pfx ++ is₁) np nm v
      (piTelA ds (foldAppsA (.const f lsF) (pl ++ idx)) w).1 =
      lamTelA ds (foldAppsA (.const r ls) (pfx.map (liftNA ds.length) ++ idx ++
        [foldAppsA (liftNA ds.length v) (paramLocalsA ds.length)])) := by
  unfold recCallFunA
  rw [piDomListA_piTelA, piBodyA_piTelA, piDomListA_of_not_pi (foldAppsA_const_ne_pi f lsF _),
    piBodyA_of_not_pi (foldAppsA_const_ne_pi f lsF _), List.append_nil, List.map_append,
    recCallFieldA_eq r ls (pfx.map (liftA 0 ds.length)) (is₁.map (liftA 0 ds.length)) np nm
      (by rw [List.length_map]; exact hpfx) _ f lsF pl idx hpl,
    ← paramLocalsA_eq_range]
  have hf : liftNA ds.length = liftA 0 ds.length := funext fun e => liftNA_eq e ds.length
  rw [hf]

/-- THE λ-PAIR AT THE INDUCTION HYPOTHESIS'S TYPE (R-NoFunRec-1 step 1 (1c-ε2d-L3b-2), T1–T3): from the two
    direct calls related at the motive in the context of the left binders (the extension world's
    relation), the two λ-wrapped calls — on the left over the left domain's binders, on the right over the
    right domain's, convertible binderwise — are typed at the left hypothesis's type, and convertible
    there. The right λ is typed at the left Π by context conversion, one binder at a time
    (`convA_lamTelA₂`); the bodies' typing and conversion are the relation's escape. -/
theorem frecCallFunA_pair {E : ResolvedEnvA} (hE : EnvClosedA E) (hI : IotaLiftA (iotaIfaceA E))
    (hR : IotaRecHeadA E (iotaIfaceA E)) (hIS : IotaSubstA (iotaIfaceA E)) {k : Nat} {Γ : LCtxA}
    (hΓ : CtxWfA E (iotaIfaceA E) n Γ) {np nm : Nat} {lsF lsF' : List Level} {r : Nat}
    {ls ls' : List Level} {mot v v' : ExprA} {pfx pfx' is₁ is₁' qs qs' iF iR : List ExprA}
    (hpfx : pfx.length = np + 1 + nm) (hpfx' : pfx'.length = np + 1 + nm)
    (hqs : qs.length = np) (hqs' : qs'.length = np) {dsF dsR : List (ExprA × Level)}
    {wF wR wM : Level} (hlen : dsR.length = dsF.length)
    (tdsF : TelTyA E (iotaIfaceA E) n Γ dsF) (hTel : TelConvA E (iotaIfaceA E) n Γ dsF dsR)
    (hB : HasTyA E (iotaIfaceA E) n (telCtxA dsF ++ Γ) (foldAppsA (liftNA dsF.length mot)
      (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) (.sort wM))
    (hcall : LRRelA E (iotaIfaceA E) n ρ₀ k (telCtxA dsF ++ Γ)
      (foldAppsA (liftNA dsF.length mot)
        (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)]))
      (foldAppsA (.const r ls) (pfx.map (liftNA dsF.length) ++ iF ++
        [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)]))
      (foldAppsA (.const r ls') (pfx'.map (liftNA dsF.length) ++ iR ++
        [foldAppsA (liftNA dsF.length v') (paramLocalsA dsF.length)]))) :
    Nonempty (HasTyA E (iotaIfaceA E) n Γ
      (recCallFunA (.const r ls) (pfx ++ is₁) np nm v
        (piTelA dsF (foldAppsA (.const f lsF) (qs.map (liftNA dsF.length) ++ iF)) wF).1)
      (piTelA dsF (foldAppsA (liftNA dsF.length mot)
        (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) wM).1) ∧
    Nonempty (HasTyA E (iotaIfaceA E) n Γ
      (recCallFunA (.const r ls') (pfx' ++ is₁') np nm v'
        (piTelA dsR (foldAppsA (.const f lsF') (qs'.map (liftNA dsR.length) ++ iR)) wR).1)
      (piTelA dsF (foldAppsA (liftNA dsF.length mot)
        (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) wM).1) ∧
    Nonempty (ConvA E (iotaIfaceA E) n Γ
      (recCallFunA (.const r ls) (pfx ++ is₁) np nm v
        (piTelA dsF (foldAppsA (.const f lsF) (qs.map (liftNA dsF.length) ++ iF)) wF).1)
      (recCallFunA (.const r ls') (pfx' ++ is₁') np nm v'
        (piTelA dsR (foldAppsA (.const f lsF') (qs'.map (liftNA dsR.length) ++ iR)) wR).1)
      (piTelA dsF (foldAppsA (liftNA dsF.length mot)
        (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) wM).1) := by
  rw [recCallFunA_frec r ls pfx is₁ np nm hpfx v dsF lsF _ iF (by rw [List.length_map]; exact hqs) wF,
    recCallFunA_frec r ls' pfx' is₁' np nm hpfx' v' dsR lsF' _ iR (by rw [List.length_map]; exact hqs') wR,
    hlen]
  obtain ⟨⟨tL⟩, ⟨tR⟩⟩ := LRRelA_hasTy hcall
  obtain ⟨cLR⟩ := LRRelA_conv hcall
  obtain ⟨cc⟩ := convA_lamTelA₂ hE hI hR hIS hΓ tdsF hTel hB cLR
  exact ⟨⟨hasTyA_lamTelA tdsF hB tL⟩, ⟨convA_hasTy_right hE hI hR hIS hΓ cc⟩, ⟨cc⟩⟩

/-- THE IH BINDER'S RELATION (R-NoFunRec-1 step 1 (1c-ε2d-L3b-3c)): the two λ-wrapped calls are related
    at the induction hypothesis's type. -/
theorem RecBaseA.frecIHRel (C : RecBaseA E₀ E n ρ₀ f fm fv cs) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ))
    {lsF lsF' lsC lsD : List Level} (hbF : levelsBounded n lsF = true) (hlF : lsF.length = fm.arity)
    (hFF : eqNListB n lsF lsF') (hk : ht ρ₀ (instLevel lsF fv.sort) ≤ k) (hFC : eqNListB n lsF lsC)
    {qs qs' : List ExprA} (hqs : qs.length = fm.nparamsA) (hqs' : qs'.length = fm.nparamsA)
    (hqq : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) (qs ++ []) (qs' ++ []))
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgcE : E.members gc.ref = some gc.member)
    {ksPre ks : List FieldShape} {jn : Nat}
    (hsp : gc.view.fields.map FieldA.shape = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    {pre pre' : List ExprA}
    {T TF TR : ExprA} (hTvC : applyTelA qs (instantiateLevelsA lsC (gc.member.normA.getD gc.member.mtypeA)) = some T)
    (hTvF : applyTelA qs (instantiateLevelsA lsF (gc.member.normA.getD gc.member.mtypeA)) = some TF)
    (hTvR : applyTelA qs' (instantiateLevelsA lsF' (gc.member.normA.getD gc.member.mtypeA)) = some TR)
    {r : Nat} {ls ls' : List Level} {mot : ExprA} {pfx pfx' : List ExprA}
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    (hwC : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC) X F fm.nparamsA qs T ksPre pre pre')
    (hwF : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsF) (fun _ _ _ => True)
      (fun _ _ _ _ _ _ => True) fm.nparamsA qs TF ksPre pre pre')
    {dsC dsF dsR : List (ExprA × Level)} {iC iF iR : List ExprA} {wC wF wR : Level}
    {uC uF uR : Level} {BC BF BR : ExprA} {vC vF vR : Level}
    (hTD_C : applyTelA pre T = some (.pi (piTelA dsC (foldAppsA (.const f lsC)
      (qs.map (liftNA dsC.length) ++ iC)) wC).1 uC BC vC))
    (hTD_F : applyTelA pre TF = some (.pi (piTelA dsF (foldAppsA (.const f lsF)
      (qs.map (liftNA dsF.length) ++ iF)) wF).1 uF BF vF))
    (hTD_R : applyTelA pre' TR = some (.pi (piTelA dsR (foldAppsA (.const f lsF')
      (qs'.map (liftNA dsR.length) ++ iR)) wR).1 uR BR vR))
    (hdC : dsC.length = jn + 1) (hdF : dsF.length = jn + 1) (hdR : dsR.length = jn + 1)
    (hwF₀ : isZero wF = false) (hwC₀ : isZero wC = false)
    {v v' : ExprA}
    (hh : FamFunIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' gc.ref lsC qs lsD
      (fm.nparamsA + ksPre.length) (qs ++ pre) (piTelA dsC (foldAppsA (.const f lsC)
      (qs.map (liftNA dsC.length) ++ iC)) wC).1 jn v v')
    (hvF : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (piTelA dsF (foldAppsA (.const f lsF)
      (qs.map (liftNA dsF.length) ++ iF)) wF).1 v v')
    (hdl : iF.length = fv.indices.length)
    (hpfx : pfx.length = fm.nparamsA + 1 + cs.length) (hpfx' : pfx'.length = fm.nparamsA + 1 + cs.length)
    {is₁ is₁' : List ExprA} {wM : Level} (hwM : isZero wM = false)
    (hTel : TelConvA E (iotaIfaceA E) n Γ dsF dsR)
    (hIH : ∃ R, LRTyA E (iotaIfaceA E) n ρ₀ k Γ (piTelA dsF (foldAppsA (liftNA dsF.length mot)
      (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) wM).1 R) :
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ (piTelA dsF (foldAppsA (liftNA dsF.length mot)
      (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) wM).1
      (recCallFunA (.const r ls) (pfx ++ is₁) fm.nparamsA cs.length v
        (piTelA dsF (foldAppsA (.const f lsF) (qs.map (liftNA dsF.length) ++ iF)) wF).1)
      (recCallFunA (.const r ls') (pfx' ++ is₁') fm.nparamsA cs.length v'
        (piTelA dsR (foldAppsA (.const f lsF') (qs'.map (liftNA dsR.length) ++ iR)) wR).1) := by
  have hΓn := hΓ
  obtain ⟨hΓt⟩ := hΓ
  have hlen : dsR.length = dsF.length := hdR.trans hdF.symm
  have hIS := iotaFnA_subst C.hE C.hEN
  have hcall := RecBaseA.frecCallRel C hΓn hbF hlF hFF hk hFC hqs hqs' hqq hgcE hsp hTvC hTvF hTvR hwC hwF
    hTD_C hTD_F hTD_R hdC hdF hdR hwF₀ hwC₀ hh hvF hdl
  obtain ⟨⟨hbL⟩, ⟨hbR⟩⟩ := LRRelA_hasTy hcall
  obtain ⟨R, hR⟩ := hIH
  obtain ⟨s, ⟨tIH⟩⟩ := LRTyA_hasTy hR
  obtain ⟨⟨tdsF⟩, hBc⟩ := telTyA_of_hasTy_piTelA _ wM dsF tIH
  obtain ⟨hB⟩ := hBc (by rw [hdF]; exact Nat.succ_pos _)
  obtain ⟨hT1, hT2, hT3⟩ := frecCallFunA_pair C.hE C.hI C.hR hIS hΓt hpfx hpfx' hqs hqs' hlen tdsF hTel hB
    hcall
  have hpi : IsPiTelA dsF.length (piTelA dsF (foldAppsA (liftNA dsF.length mot)
      (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) wM).1 :=
    isPiTelA_piTelA _ wM hwM dsF
  refine ⟨R, hR, ?_⟩
  refine telIntroA C.hE C.hI C.hNCT C.hEN dsF.length ⟨hΓt⟩ hpi hR hT1 hT2 hT3 ?_
  intro ρ hρ as as' hK hl Cc hC
  obtain ⟨hΔ⟩ := hρ.2
  have hτ := substTyA_wkSubstA C.hE C.hI hΓt ρ hρ.1
  have hKS : ArgsRelKA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ) (substA (wkSubstA ρ) (piTelA dsF
      (foldAppsA (liftNA dsF.length mot) (iF ++ [foldAppsA (liftNA dsF.length v)
        (paramLocalsA dsF.length)])) wM).1) as as' := by
    rw [← wkExprA_eq_substA]; exact hK
  have hKF := argsRelKA_piTelA_body (foldAppsA (liftNA dsF.length mot)
      (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)]))
    (foldAppsA (.const f lsF) (qs.map (liftNA dsF.length) ++ iF)) wM wF dsF (wkSubstA ρ) hKS hl
  have hcoreAt := RecBaseA.frecCallRelAt C hΓn hbF hlF hFF hk hFC hqs hqs' hqq hgcE hsp hTvC hTvF hTvR hwC
    hwF hTD_C hTD_F hTD_R hdC hdF hdR hwF₀ hwC₀ hh hdl hρ hl hKF
  have hC' : Cc = substA (consListA as (wkSubstA ρ)) (foldAppsA (liftNA dsF.length mot)
      (iF ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) := by
    have := applyTelA_wk_piTelA (foldAppsA (liftNA dsF.length mot) (iF ++ [foldAppsA (liftNA dsF.length v)
      (paramLocalsA dsF.length)])) wM dsF ρ as hl
    rw [this] at hC
    exact (Option.some.inj hC).symm
  subst hC'
  have eW : recCallFunA (.const r ls) (pfx ++ is₁) fm.nparamsA cs.length v
      (piTelA dsF (foldAppsA (.const f lsF) (qs.map (liftNA dsF.length) ++ iF)) wF).1 =
      lamTelA dsF (foldAppsA (.const r ls) (pfx.map (liftNA dsF.length) ++ iF ++
        [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) :=
    recCallFunA_frec r ls pfx is₁ fm.nparamsA cs.length hpfx v dsF lsF _ iF (by rw [List.length_map]; exact
      hqs) wF
  have eW' : recCallFunA (.const r ls') (pfx' ++ is₁') fm.nparamsA cs.length v'
      (piTelA dsR (foldAppsA (.const f lsF') (qs'.map (liftNA dsR.length) ++ iR)) wR).1 =
      lamTelA dsR (foldAppsA (.const r ls') (pfx'.map (liftNA dsF.length) ++ iR ++
        [foldAppsA (liftNA dsF.length v') (paramLocalsA dsF.length)])) := by
    rw [recCallFunA_frec r ls' pfx' is₁' fm.nparamsA cs.length hpfx' v' dsR lsF' _ iR
      (by rw [List.length_map]; exact hqs') wR, hlen]
  rw [eW, eW', wkExprA_eq_substA, wkExprA_eq_substA, substA_lamTelA, substA_lamTelA]
  have hargsL := convArgsA_refl_left (convArgsA_of_argsRelKA hKS)
  have hLeft := lrRelA_lamTel_apps_left C.hE C.hI C.hR hIS (k := k) tdsF hB hbL hΔ hτ hl hargsL hcoreAt
  obtain ⟨htelR⟩ := telTyA_of_telConvA C.hE C.hI C.hR hIS hΓt tdsF hTel
  obtain ⟨hcc⟩ := ctxConvA_tel C.hE C.hI C.hR hIS (ctxConvA_refl Γ) hΓt hTel
  obtain ⟨hBR⟩ := hasTyA_ctxConv C.hE C.hI (iotaRecHeadTypedA_of C.hR) hcc hB
  obtain ⟨hbR'⟩ := hasTyA_ctxConv C.hE C.hI (iotaRecHeadTypedA_of C.hR) hcc hbR
  have hl' : as'.length = dsF.length := (argsRelKA_length hKS).symm.trans hl
  obtain ⟨R₁, hR₁, -⟩ := LRTyA_wk C.hE C.hEN C.hI hR ρ hρ
  have hv₁ : ∃ R₂, LRTyA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ) (substA (wkSubstA ρ) (piTelA dsF
      (foldAppsA (liftNA dsF.length mot) (iF ++ [foldAppsA (liftNA dsF.length v)
        (paramLocalsA dsF.length)])) wM).1) R₂ := by
    rw [← wkExprA_eq_substA]; exact ⟨R₁, hR₁⟩
  obtain ⟨hargsR0⟩ := convArgsA_right_of_argsRelKA C.hNCT ⟨hΔ⟩ hKS (len := dsF.length)
    (by rw [← wkExprA_eq_substA]; exact isPiTelA_wk_piTelA _ wM hwM dsF ρ)
    (by rw [hl]; exact Nat.le_refl _) hv₁
  obtain ⟨hargsR⟩ := convArgsA_telConv C.hE C.hI C.hR hIS hTel hΔ hτ hl' hargsR0
  have hpos : 0 < as.length := by rw [hl, hdF]; exact Nat.succ_pos _
  have hEq := lrEqA_applyTelA_self C.hNCT ⟨hΔ⟩ hK (isPiTelA_wk_piTelA _ wM hwM dsF ρ) hpos
    (by rw [hl]; exact Nat.le_refl _) ⟨R₁, hR₁⟩ (applyTelA_wk_piTelA (foldAppsA (liftNA dsF.length mot) (iF
      ++ [foldAppsA (liftNA dsF.length v) (paramLocalsA dsF.length)])) wM dsF ρ as hl)
      (applyTelA_wk_piTelA (foldAppsA (liftNA dsF.length mot) (iF ++ [foldAppsA (liftNA dsF.length v)
        (paramLocalsA dsF.length)])) wM dsF ρ as' hl')
  obtain ⟨hc⟩ := LREqA_tyConv (LREqA_symm C.hNCT hEq)
  exact lrRelA_lamTel_apps_right C.hE C.hI C.hR hIS (k := k) htelR hBR hbR' hΔ hτ (hl'.trans hlen.symm)
    hargsR ⟨hc⟩ hLeft

end GroupAt

/-! ## (5) THE MINOR WALK -/

section MinorWalk
variable {E₀ E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
  {cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)}

/-- THE MINOR WALK. Along a constructor form's field walk at its levels `lsC` and the carrier's
    parameters `qs` (the canonical field relation at the plain fields, the induction hypothesis and the
    fixed point at the recursive ones), the ι reduct's arguments on the two sides (at the recursor's
    family levels `lsF`, `lsF'` and parameters `qs`, `qs'`) are related along the minor's telescope at
    `lsF`, `qs`: a plain field carried from its domain at `lsC` to the one at `lsF` (`plainDomA` on the
    walk's diagonal); a recursive field moved within the fiber (`recDomA`, `lfpWA_recDom`) and related by
    canonicity there; its induction hypothesis from the walk's predicate, at the indices the two
    reducts read (`recDomA` across `lsF`, `qs` and `lsF'`, `qs'`). The fields come out related along the
    constructor's telescope at `lsF`, `qs` too. -/
theorem minorWalkA (C : RecBaseA E₀ E n ρ₀ f fm fv cs) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ))
    {lsF lsF' : List Level} (hbF : levelsBounded n lsF = true) (hlF : lsF.length = fm.arity)
    (hFF : eqNListB n lsF lsF') (hk : ht ρ₀ (instLevel lsF fv.sort) ≤ k)
    {qs qs' : List ExprA} (hqs : qs.length = fm.nparamsA) (hqs' : qs'.length = fm.nparamsA)
    (hqq : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) (qs ++ []) (qs' ++ []))
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgcE : E.members gc.ref = some gc.member)
    {lsC : List Level} (hFC : eqNListB n lsF lsC) (lsD : List Level)
    {r : Nat} {ls ls' : List Level} {mot : ExprA} {pfx pfx' is₁ is₁' : List ExprA}
    (hpfx : pfx.length = fm.nparamsA + 1 + cs.length) (hpfx' : pfx'.length = fm.nparamsA + 1 + cs.length)
    {wM : Level} (hwM : isZero wM = false)
    (hdl : ∀ idx, FieldA.drec idx ∈ gc.view.fields.map FieldA.norm → idx.length = fv.indices.length)
    :
    ∀ (fsRest fsPre : List FieldA) (pre pre' vs vs' : List ExprA), gc.view.fields = fsPre ++ fsRest →
      pre.length = fsPre.length →
      ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC)
        (famRecRelA fm qs lsD (fun D y y' =>
          RecIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' D y y' ∧
          FamLfpA E n ρ₀ k Γ f fm D y y'))
        (FamFunIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' gc.ref lsC qs lsD) fm.nparamsA qs (ctorFieldsA f lsC (instLevel lsC fv.sort) qs (consListA qs SubstA.id)
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsC)) (gc.view.res.map (instantiateLevelsA lsC))).1
        (fsPre.map FieldA.shape) pre pre' →
      ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC)
        (famRecRelA fm qs lsD (fun D y y' =>
          RecIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' D y y' ∧
          FamLfpA E n ρ₀ k Γ f fm D y y'))
        (FamFunIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' gc.ref lsC qs lsD) (fm.nparamsA + pre.length) (qs ++ pre)
        (ctorFieldsA f lsC (instLevel lsC fv.sort) qs (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsC)) (gc.view.res.map (instantiateLevelsA lsC))).1
        (fsRest.map FieldA.shape) vs vs' →
      ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsF) (fun _ _ _ => True) (fun _ _ _ _ _ _ => True)
        fm.nparamsA qs
        (ctorFieldsA f lsF (instLevel lsF fv.sort) qs (consListA qs SubstA.id)
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1
        (fsPre.map FieldA.shape) pre pre' →
      ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ
        (ctorFieldsA f lsF (instLevel lsF fv.sort) qs (consListA qs SubstA.id)
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1 pre pre' →
      (∃ R, LRTyA E (iotaIfaceA E) n ρ₀ k Γ
        (minorFieldsA f gc.ref lsF (instLevel lsF fv.sort) wM qs mot pre
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
          (fsRest.map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1 R) →
      ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ
        (minorFieldsA f gc.ref lsF (instLevel lsF fv.sort) wM qs mot pre
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
          (fsRest.map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1
        (rhsArgsA (.const r ls) (pfx ++ is₁) fm.nparamsA cs.length vs (fsRest.map FieldA.shape)
          (ctorFieldsA f lsF (instLevel lsF fv.sort) qs (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
            ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1)
        (rhsArgsA (.const r ls') (pfx' ++ is₁') fm.nparamsA cs.length vs' (fsRest.map FieldA.shape)
          (ctorFieldsA f lsF' (instLevel lsF' fv.sort) qs'
            (consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id))
            ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF')) (gc.view.res.map (instantiateLevelsA lsF'))).1) ∧
      ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ
        (ctorFieldsA f lsF (instLevel lsF fv.sort) qs (consListA qs SubstA.id)
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1
        (pre ++ vs) (pre' ++ vs')
  | [], fsPre, pre, pre', vs, vs', _, _, _, hs, _, hwK, _ => by
      have hl := argsRelA_length hs
      simp only [List.map_nil, List.length_nil] at hl
      match vs, vs', hl with
      | [], [], _ =>
          refine ⟨?_, by simpa using hwK⟩
          simp only [List.map_nil, rhsArgsA]
          exact .nil _
  | .drecD D₀ idx₀ :: fsRest, fsPre, pre, pre', vs, vs', hfs, hpre, hwC, hs, hwF, hwK, hM => by
      have hpre' : pre'.length = fsPre.length := by rw [(argsRelA_length hwC).2, List.length_map]
      have hlC : lsC.length = fm.arity := (eqNListA_length hFC.1).symm.trans hlF
      have hlF' : lsF'.length = fm.arity := (eqNListA_length hFF.1).symm.trans hlF
      have hkinds := gc.view.shapes C.hfresh
      have hkinds' : ctorShapesA f fm.nparamsA (gc.member.normA.getD gc.member.mtypeA) =
          some (gc.view.fields.map FieldA.shape) := gc.normA_getD.symm ▸ hkinds
      have hqd := argsRelKA_refl_left C.hNCT hqq
      have hsp : gc.view.fields.map FieldA.shape =
          fsPre.map FieldA.shape ++ FieldShape.recursive 0 :: fsRest.map FieldA.shape := by
        rw [hfs, List.map_append]; rfl
      have hfsN : gc.view.fields.map FieldA.norm =
          fsPre.map FieldA.norm ++ FieldA.drec idx₀ :: fsRest.map FieldA.norm := by
        rw [hfs, List.map_append]; rfl
      have hTD_C := applyTelA_groupCtor_prefix gc lsC hfsN
        (by simpa using hpre) qs (consListA qs SubstA.id)
      have hTD_F := applyTelA_groupCtor_prefix gc lsF hfsN
        (by simpa using hpre) qs (consListA qs SubstA.id)
      have hTD_R := applyTelA_groupCtor_prefix gc lsF' hfsN
        (by simpa using hpre') qs' (consListA qs' SubstA.id)
      simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA, plainArgsA_norm] at hTD_C hTD_F hTD_R
      simp only [List.map, FieldA.instLevels, FieldA.shape, FieldA.norm, ctorFieldsA] at hs
      have hTvC := C.ctorTel gc lsC hlC hqs
      have hTvF := C.ctorTel gc lsF hlF hqs
      have hTvR := C.ctorTel gc lsF' hlF' hqs'
      cases hs with
      | directRec _ _ _ _ _ _ v v' _ vs₀ vs₀' hh hs' =>
        -- the recursive domain moved within the fiber to `lsF`
        have hRD₀ := recDomA (fv := fv) (cs := cs) C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hS C.hfm
          C.hcls C.hfresh C.hcensus C.hcl C.hT C.hUT hbF hlF hk (k := k) hΓ (ps := qs) (ps' := qs)
          (is := []) (is' := []) hqs hqs hqd (ρ := []) (Or.inl rfl) hgcE gc.hcls
          gc.view.famRef hkinds' hsp (eqNListA_refl lsF) hFC (eqNListB_symm hFC hbF)
          (by rw [map_wkExprA_nil]; exact hTvC) (by rw [map_wkExprA_nil]; exact hTvF)
          (by rw [map_wkExprA_nil]; exact argsRelA_diag C.hNCT (famRsA_refl_left C.hNCT) hwC) hTD_C hTD_F
        have hRD : RecDomRelA E (iotaIfaceA E) n Γ f fm (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm []) lsF qs
            (foldAppsA (.const f lsC) (qs ++ (idx₀.map (instantiateLevelsA lsC)).map
              (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)))))
            (foldAppsA (.const f lsF) (qs ++ (idx₀.map (instantiateLevelsA lsF)).map
              (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))))) := by
          simpa only [map_wkExprA_nil] using hRD₀
        have hLfpL := (lfpWA_recDom (ρ := []) (C.idxPer hbF hlF hk hΓ hqs hqd) hqs hRD).1 hh.2.2.2
        -- the δ-reached field's surface domain converts to the family application at its
        -- indices (the view's `drecD_typed`): the conversion's fundamental arm relates them
        -- at the sort, giving the equality and both validities at the clause's height
        obtain ⟨-, hcv₀, -⟩ := gc.view.drecD_typed fsPre D₀ idx₀ fsRest hfs
        obtain ⟨hc⟩ := hcv₀
        have hcG := convEnvA (prefixA_extend_groupEnvA C.hgf) hc
        have hcI := convA_instLevels C.hELG C.hIL hbF hlF hcG
        obtain ⟨Kd, hKd⟩ := C.hfcG hcI
        obtain ⟨hwfp⟩ := fv.paramsCtxWf C.hT
        obtain ⟨K₁, hK₁⟩ := fieldWalkA (f := f) (s := instLevel lsF fv.sort) (pl := qs)
          (j := k) (Γ := Γ) (ρ := []) (X := fun _ _ _ => True) (F := fun _ _ _ _ _ _ => True)
          C.hfc C.hE₀ C.hI C.hNCT C.hR₀ C.hEL₀ C.hIL hbF hlF hgcE hΓ fsPre
          (by have hty := gc.view.typed; rw [hfs] at hty; exact hty) hwfp
        obtain ⟨K₃, hK₃⟩ := paramSubstA C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL
          fv C.hcl C.hT hbF hbF hlF hlF (eqNListA_refl lsF)
        have hV₀ : ValidSubstA E (iotaIfaceA E) n ρ₀ (max (max Kd K₁) (max K₃ k)) (wkCtxA [] Γ)
            (consListA (qs.map (wkExprA [])) SubstA.id) (consListA (qs.map (wkExprA [])) SubstA.id)
            (instCtxA lsF (telCtxA fv.params)) :=
          hK₃ _ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) qs qs [] []
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hΓ hqs hqs hqd
            [] (Or.inl rfl)
        have hV₁ : ValidSubstA E (iotaIfaceA E) n ρ₀ (max (max Kd K₁) (max K₃ k)) (wkCtxA [] Γ)
            (consListA (plainArgsA fsPre pre) (consListA (qs.map (wkExprA [])) SubstA.id))
            (consListA (plainArgsA fsPre pre) (consListA (qs.map (wkExprA [])) SubstA.id))
            (instCtxA lsF (plainCtxA fsPre (telCtxA fv.params))) :=
          hK₁ _ (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
            _ _ fm.nparamsA (qs.map (wkExprA [])) pre pre hV₀
            (by rw [map_wkExprA_nil, ← hfs]; exact hTvF)
            (by rw [map_wkExprA_nil, ← hfs]; exact argsRelA_diag C.hNCT (famRsA_refl_left C.hNCT) hwF)
        have hV : ValidSubstA E (iotaIfaceA E) n ρ₀ (max (max Kd K₁) (max K₃ k)) Γ
            (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
            (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
            (instCtxA lsF (plainCtxA fsPre (telCtxA fv.params))) := by
          simpa only [map_wkExprA_nil] using hV₁
        have hstep : instantiateLevelsA lsF ∘ liftA 0 (plainIdxA fsPre 0) =
            liftA 0 (plainIdxA fsPre 0) ∘ instantiateLevelsA lsF :=
          funext fun x => instantiateLevelsA_liftA lsF 0 _ x
        have h₂ : substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) ∘
            liftA 0 (plainIdxA fsPre 0) = substA (consListA qs SubstA.id) := by
          funext x
          show substA _ (liftA 0 (plainIdxA fsPre 0) x) = _
          rw [show plainIdxA fsPre 0 = (plainArgsA fsPre pre).length from
            (plainIdxA_length fsPre pre hpre 0).trans (Nat.zero_add _)]
          exact substA_consListA_liftA _ _ _
        have hpl : (paramLocalsA fv.params.length).map
            (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) ∘
              (instantiateLevelsA lsF ∘ liftA 0 (plainIdxA fsPre 0))) = qs := by
          rw [hstep, ← List.map_map, ← List.map_map, map_instantiateLevelsA_paramLocalsA,
            List.map_map, h₂, fv.nparams, ← hqs, map_substA_consListA_paramLocalsA]
        have hAppF : substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
            (instantiateLevelsA lsF (foldAppsA (.const f (canonLevelsA fm.arity))
              ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idx₀))) =
          foldAppsA (.const f lsF) (qs ++ (idx₀.map (instantiateLevelsA lsF)).map
            (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)))) := by
          rw [instantiateLevelsA_foldAppsA, substA_foldAppsA]
          simp only [List.map_append, List.map_map]
          congr 1
          · show substA _ (instantiateLevelsA lsF (.const f (canonLevelsA fm.arity))) = .const f lsF
            rw [show instantiateLevelsA lsF (.const f (canonLevelsA fm.arity)) =
                .const f ((canonLevelsA fm.arity).map (instLevel lsF)) from rfl, ← hlF,
              canonLevelsA_instLevel, substA_const]
          · rw [hpl]
        obtain ⟨_, hDrel⟩ := hKd _ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) Γ _ _
          hΓ hV
        rw [hAppF] at hDrel
        obtain ⟨heq, hva, hvb⟩ := (LRRelA_sort_elim' hDrel).1 k hk
        obtain ⟨RF, hRF⟩ := hvb
        have hvFam := C.lrRel hqs hRF hLfpL
        -- the minor's field binder, then its induction hypothesis binder
        obtain ⟨RM, hRM⟩ := hM
        simp only [List.map, FieldA.instLevels, minorFieldsA] at hRM
        obtain ⟨⟨RL, hRL⟩, hcod⟩ := LRTyA_pi_peel hΓ hRM
          (by rw [isZero_imax, minorFieldsA_snd, minorLevelA_isZero]; exact hwM)
        have hvF : LRRelA E (iotaIfaceA E) n ρ₀ k Γ
            (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
              (instantiateLevelsA lsF D₀)) v v' :=
          LRRelA_transport' C.hNCT (LREqA_symm C.hNCT heq) hvFam
        obtain ⟨RI, hRI⟩ := hcod v v' hvF
        rw [instantiate0A_eq_substA_cons, substA_pi, substA_cons_ihDom] at hRI
        obtain ⟨_, hcod₂⟩ := LRTyA_pi_peel hΓ hRI (by rw [minorFieldsA_snd, minorLevelA_isZero]; exact hwM)
        -- the indices the two reducts read, related along the family's telescope at `lsF`
        have hRR₀ := recDomA (fv := fv) (cs := cs) C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hS C.hfm
          C.hcls C.hfresh C.hcensus C.hcl C.hT C.hUT hbF hlF hk (k := k) hΓ (ps := qs) (ps' := qs')
          (is := []) (is' := []) hqs hqs' hqq (ρ := []) (Or.inl rfl) hgcE gc.hcls
          gc.view.famRef hkinds' hsp (eqNListA_refl lsF) (eqNListB_refl hbF) hFF
          (by rw [map_wkExprA_nil]; exact hTvF) (by rw [map_wkExprA_nil]; exact hTvR)
          (by rw [map_wkExprA_nil]; exact hwF) hTD_F hTD_R
        simp only [map_wkExprA_nil] at hRR₀
        obtain ⟨lsA, lsA', isA, isA', TF, TF', hA, hA', _, _, hTF, _, hwI, _⟩ := hRR₀
        obtain ⟨_, elA, exA⟩ := foldAppsA_const_inj hA
        obtain ⟨_, elA', exA'⟩ := foldAppsA_const_inj hA'
        have exA₁ := List.append_cancel_left exA
        have exA₁' := List.append_cancel_left exA'
        subst elA elA' exA₁ exA₁'
        have hidxF := argsRelPA_famRsFA_KA hwI hTF
        have hqq' : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) qs qs' := by
          simpa only [List.append_nil] using hqq
        have hidx := argsRelKA_append hqq' hTF hidxF
        have hIHrel := hh.2.2.1 _ _ (by
          simp only [List.length_map]
          exact hdl idx₀ (List.mem_map.mpr ⟨.drecD D₀ idx₀, by rw [hfs]; simp, rfl⟩)) hRD hidx
        obtain ⟨RM₁, hRM₁⟩ := hcod₂ _ _ hIHrel
        rw [instantiate0A_instantiate0A_up] at hRM₁
        have e1 := substA_minorFieldsA_drec f gc.ref lsF (instLevel lsF fv.sort) wM
          (gc.view.res.map (instantiateLevelsA lsF)) (fsRest.map (FieldA.instLevels lsF)) qs mot pre
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) v
          (foldAppsA (.const r ls) (pfx ++ (idx₀.map (instantiateLevelsA lsF)).map
            (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))) ++ [v]))
        rw [e1] at hRM₁
        have e2 := instantiate0A_ctorFieldsA_drec f lsF (instLevel lsF fv.sort) (gc.view.res.map
          (instantiateLevelsA lsF))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF)) qs (consListA (plainArgsA fsPre pre)
            (consListA qs SubstA.id)) v
        have e3 := instantiate0A_ctorFieldsA_drec f lsF' (instLevel lsF' fv.sort)
          (gc.view.res.map (instantiateLevelsA lsF')) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF')) qs'
          (consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id)) v'
        have eC := instantiate0A_ctorFieldsA_drec f lsC (instLevel lsC fv.sort) (gc.view.res.map
          (instantiateLevelsA lsC))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsC)) qs (consListA (plainArgsA fsPre pre)
            (consListA qs SubstA.id)) v
        have hσ₁ : consListA (plainArgsA (fsPre ++ [FieldA.drecD D₀ idx₀]) (pre ++ [v])) (consListA qs SubstA.id) =
            consListA (plainArgsA fsPre pre) (consListA qs SubstA.id) := by
          rw [plainArgsA_snoc_drecD D₀ idx₀ v fsPre pre hpre]
        have hσ₁' : consListA (plainArgsA (fsPre ++ [FieldA.drecD D₀ idx₀]) (pre' ++ [v'])) (consListA qs' SubstA.id) =
            consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id) := by
          rw [plainArgsA_snoc_drecD D₀ idx₀ v' fsPre pre' hpre']
        -- the extended prefixes
        have hfs₁ : gc.view.fields = (fsPre ++ [FieldA.drecD D₀ idx₀]) ++ fsRest := by rw [hfs, List.append_assoc]; rfl
        have hpre₁ : (pre ++ [v]).length = (fsPre ++ [FieldA.drecD D₀ idx₀]).length := by simp [hpre]
        have hwC₁ := argsRelA_snoc hwC (FieldShape.recursive 0) hTD_C hh
        have hwF₁ := argsRelA_snoc (X := fun _ _ _ => True) (f := v) (f' := v') hwF (FieldShape.recursive 0) hTD_F trivial
        have hwK₁ := argsRelKA_append hwK hTD_F (ArgsRelKA.cons _ _ _ _ v v' [] [] hvFam (.nil _))
        have ek : fsPre.map FieldA.shape ++ [FieldShape.recursive 0] = (fsPre ++ [FieldA.drecD D₀ idx₀]).map FieldA.shape := by
          simp [FieldA.shape]
        rw [ek] at hwC₁ hwF₁
        have hs₁ : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC)
            (famRecRelA fm qs lsD (fun D y y' =>
              RecIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' D y y' ∧
              FamLfpA E n ρ₀ k Γ f fm D y y'))
            (FamFunIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' gc.ref lsC qs lsD) (fm.nparamsA + (pre ++ [v]).length) (qs ++ (pre ++ [v]))
            (ctorFieldsA f lsC (instLevel lsC fv.sort) qs (consListA (plainArgsA (fsPre ++ [FieldA.drecD D₀ idx₀])
              (pre ++ [v])) (consListA qs SubstA.id)) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsC))
              (gc.view.res.map (instantiateLevelsA lsC))).1
            (fsRest.map FieldA.shape) vs₀ vs₀' := by
          rw [hσ₁, ← eC, List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc]
          exact hs'
        have hM₁ : ∃ R, LRTyA E (iotaIfaceA E) n ρ₀ k Γ
            (minorFieldsA f gc.ref lsF (instLevel lsF fv.sort) wM qs mot (pre ++ [v])
              (consListA (plainArgsA (fsPre ++ [FieldA.drecD D₀ idx₀]) (pre ++ [v])) (consListA qs SubstA.id))
              (fsRest.map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1 R := by
          rw [hσ₁]; exact ⟨RM₁, hRM₁⟩
        obtain ⟨ih1, ih2⟩ := minorWalkA C hΓ hbF hlF hFF hk hqs hqs' hqq hgcE hFC lsD hpfx hpfx' hwM hdl
          fsRest
          (fsPre ++ [FieldA.drecD D₀ idx₀]) (pre ++ [v]) (pre' ++ [v']) vs₀ vs₀' hfs₁ hpre₁ hwC₁ hs₁ hwF₁ hwK₁ hM₁
        rw [hσ₁, hσ₁'] at ih1
        refine ⟨?_, by simpa using ih2⟩
        simp only [List.map, FieldA.instLevels, FieldA.shape, ctorFieldsA, minorFieldsA, rhsArgsA, recCallsA,
          List.singleton_append]
        rw [e2, e3, recCallFieldA_eq r ls pfx is₁ fm.nparamsA cs.length hpfx v f lsF qs _ hqs,
          recCallFieldA_eq r ls' pfx' is₁' fm.nparamsA cs.length hpfx' v' f lsF' qs' _ hqs']
        refine .cons _ _ _ _ v v' _ _ hvF ?_
        rw [instantiate0A_eq_substA_cons v, substA_pi, substA_cons_ihDom]
        refine .cons _ _ _ _ _ _ _ _ hIHrel ?_
        rw [instantiate0A_instantiate0A_up, e1]
        exact ih1
  | .plain D u :: fsRest, fsPre, pre, pre', vs, vs', hfs, hpre, hwC, hs, hwF, hwK, hM => by
      have hpre' : pre'.length = fsPre.length := by rw [(argsRelA_length hwC).2, List.length_map]
      have hlC : lsC.length = fm.arity := (eqNListA_length hFC.1).symm.trans hlF
      have hlF' : lsF'.length = fm.arity := (eqNListA_length hFF.1).symm.trans hlF
      have hkinds := gc.view.shapes C.hfresh
      have hkinds' : ctorShapesA f fm.nparamsA (gc.member.normA.getD gc.member.mtypeA) =
          some (gc.view.fields.map FieldA.shape) := gc.normA_getD.symm ▸ hkinds
      have hqd := argsRelKA_refl_left C.hNCT hqq
      have hsp : gc.view.fields.map FieldA.shape = fsPre.map FieldA.shape ++ FieldShape.nonrecursive :: fsRest.map FieldA.shape := by
        rw [hfs, List.map_append]; rfl
      have hfsN : gc.view.fields.map FieldA.norm =
          fsPre.map FieldA.norm ++ FieldA.plain D u :: fsRest.map FieldA.norm := by
        rw [hfs, List.map_append]; rfl
      have hTD_C := applyTelA_groupCtor_prefix gc lsC hfsN
        (by simpa using hpre) qs (consListA qs SubstA.id)
      have hTD_F := applyTelA_groupCtor_prefix gc lsF hfsN
        (by simpa using hpre) qs (consListA qs SubstA.id)
      have hTD_R := applyTelA_groupCtor_prefix gc lsF' hfsN
        (by simpa using hpre') qs' (consListA qs' SubstA.id)
      simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA, plainArgsA_norm] at hTD_C hTD_F hTD_R
      simp only [List.map, FieldA.instLevels, FieldA.shape, FieldA.norm, ctorFieldsA] at hs
      have hTvC := C.ctorTel gc lsC hlC hqs
      have hTvF := C.ctorTel gc lsF hlF hqs
      cases hs with
      | plain _ _ _ _ _ _ v v' _ vs₀ vs₀' hh hs' =>
        -- the field at `lsC`, carried to `lsF`
        have hvC := hh
        rw [famRsA_eq hgcE (by rw [applyTelA_append, hTvC]; exact hTD_C)] at hvC
        obtain ⟨heq, _, _⟩ := plainDomA (fv := fv) (cs := cs) C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI
          C.hR₀ C.hEL₀ C.hIL
          C.hfresh C.hcensus C.hcl C.hT C.hUT hbF hlF hk (k := k) hΓ (ps := qs) (ps' := qs) (is := []) (is' := [])
          hqs hqs hqd (ρ := []) (Or.inl rfl) hgcE gc.hcls gc.view.famRef hkinds' hsp
          (eqNListA_refl lsF) hFC (eqNListB_symm hFC hbF) (by rw [map_wkExprA_nil]; exact hTvC)
          (by rw [map_wkExprA_nil]; exact hTvF)
          (by rw [map_wkExprA_nil]; exact argsRelA_diag C.hNCT (famRsA_refl_left C.hNCT) hwC) hTD_C hTD_F
        have hvF : LRRelA E (iotaIfaceA E) n ρ₀ k Γ
            (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) (instantiateLevelsA lsF D)) v v' :=
          LRRelA_transport' C.hNCT heq hvC
        -- the minor's next state
        obtain ⟨RM, hRM⟩ := hM
        simp only [List.map, FieldA.instLevels, minorFieldsA] at hRM
        obtain ⟨_, hcod⟩ := LRTyA_pi_peel hΓ hRM (by rw [minorFieldsA_snd, minorLevelA_isZero]; exact hwM)
        obtain ⟨RM₁, hRM₁⟩ := hcod v v' hvF
        have e1 := instantiate0A_minorFieldsA_plain f gc.ref lsF (instLevel lsF fv.sort) wM
          (gc.view.res.map (instantiateLevelsA lsF)) (fsRest.map (FieldA.instLevels lsF)) qs mot pre
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) v
        rw [e1] at hRM₁
        have e2 := instantiate0A_ctorFieldsA_plain f lsF (instLevel lsF fv.sort) (gc.view.res.map (instantiateLevelsA lsF))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF)) qs (consListA (plainArgsA fsPre pre) (consListA qs
            SubstA.id)) v
        have e3 := instantiate0A_ctorFieldsA_plain f lsF' (instLevel lsF' fv.sort)
          (gc.view.res.map (instantiateLevelsA lsF')) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF')) qs'
          (consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id)) v'
        have eC := instantiate0A_ctorFieldsA_plain f lsC (instLevel lsC fv.sort) (gc.view.res.map (instantiateLevelsA lsC))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsC)) qs (consListA (plainArgsA fsPre pre) (consListA qs
            SubstA.id)) v
        have hσ₁ : consListA (plainArgsA (fsPre ++ [FieldA.plain D u]) (pre ++ [v])) (consListA qs SubstA.id) =
            SubstA.cons v (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) := by
          rw [plainArgsA_snoc_plain D u v fsPre pre hpre, consListA_snoc]
        have hσ₁' : consListA (plainArgsA (fsPre ++ [FieldA.plain D u]) (pre' ++ [v'])) (consListA qs' SubstA.id) =
            SubstA.cons v' (consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id)) := by
          rw [plainArgsA_snoc_plain D u v' fsPre pre' hpre', consListA_snoc]
        -- the extended prefixes
        have hfs₁ : gc.view.fields = (fsPre ++ [FieldA.plain D u]) ++ fsRest := by rw [hfs, List.append_assoc]; rfl
        have hpre₁ : (pre ++ [v]).length = (fsPre ++ [FieldA.plain D u]).length := by simp [hpre]
        have hwC₁ := argsRelA_snoc hwC FieldShape.nonrecursive hTD_C
          (show famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC (fm.nparamsA + (fsPre.map FieldA.shape).length)
            (qs ++ pre) v v' by rw [List.length_map, ← hpre]; exact hh)
        have hwF₁ := argsRelA_snoc hwF FieldShape.nonrecursive hTD_F
          (show famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsF (fm.nparamsA + (fsPre.map FieldA.shape).length)
            (qs ++ pre) v v' by
            rw [famRsA_eq hgcE (by rw [applyTelA_append, hTvF]; exact hTD_F)]; exact hvF)
        have hwK₁ := argsRelKA_append hwK hTD_F (ArgsRelKA.cons _ _ _ _ v v' [] [] hvF (.nil _))
        have ek : fsPre.map FieldA.shape ++ [FieldShape.nonrecursive] = (fsPre ++ [FieldA.plain D u]).map FieldA.shape := by
          simp [FieldA.shape]
        rw [ek] at hwC₁ hwF₁
        have hs₁ : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC)
            (famRecRelA fm qs lsD (fun D y y' =>
              RecIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' D y y' ∧
              FamLfpA E n ρ₀ k Γ f fm D y y'))
            (FamFunIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' gc.ref lsC qs lsD) (fm.nparamsA + (pre ++ [v]).length) (qs ++ (pre ++ [v]))
            (ctorFieldsA f lsC (instLevel lsC fv.sort) qs
              (consListA (plainArgsA (fsPre ++ [FieldA.plain D u]) (pre ++ [v])) (consListA qs SubstA.id))
              ((fsRest.map FieldA.norm).map (FieldA.instLevels lsC)) (gc.view.res.map (instantiateLevelsA lsC))).1
            (fsRest.map FieldA.shape) vs₀ vs₀' := by
          rw [hσ₁, ← eC, List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc]
          exact hs'
        have hM₁ : ∃ R, LRTyA E (iotaIfaceA E) n ρ₀ k Γ
            (minorFieldsA f gc.ref lsF (instLevel lsF fv.sort) wM qs mot (pre ++ [v])
              (consListA (plainArgsA (fsPre ++ [FieldA.plain D u]) (pre ++ [v])) (consListA qs SubstA.id))
              (fsRest.map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1 R := by
          rw [hσ₁]; exact ⟨RM₁, hRM₁⟩
        obtain ⟨ih1, ih2⟩ := minorWalkA C hΓ hbF hlF hFF hk hqs hqs' hqq hgcE hFC lsD hpfx hpfx' hwM hdl
          fsRest
          (fsPre ++ [FieldA.plain D u]) (pre ++ [v]) (pre' ++ [v']) vs₀ vs₀' hfs₁ hpre₁ hwC₁ hs₁ hwF₁ hwK₁ hM₁
        rw [hσ₁, hσ₁'] at ih1
        refine ⟨?_, by simpa using ih2⟩
        simp only [List.map, FieldA.instLevels, FieldA.shape, ctorFieldsA, minorFieldsA, rhsArgsA, recCallsA,
          List.nil_append]
        rw [e2, e3]
        refine .cons _ _ _ _ v v' _ _ hvF ?_
        rw [e1]
        exact ih1
  | .frec B uB Bs idx :: fsRest, fsPre, pre, pre', vs, vs', hfs, hpre, hwC, hs, hwF, hwK, hM => by
      have hpre' : pre'.length = fsPre.length := by rw [(argsRelA_length hwC).2, List.length_map]
      have hlC : lsC.length = fm.arity := (eqNListA_length hFC.1).symm.trans hlF
      have hlF' : lsF'.length = fm.arity := (eqNListA_length hFF.1).symm.trans hlF
      have hkinds := gc.view.shapes C.hfresh
      have hqd := argsRelKA_refl_left C.hNCT hqq
      have hsp : gc.view.fields.map FieldA.shape =
          fsPre.map FieldA.shape ++ FieldShape.recursive (Bs.length + 1) :: fsRest.map FieldA.shape := by
        rw [hfs, List.map_append]; rfl
      have hfsN : gc.view.fields.map FieldA.norm =
          fsPre.map FieldA.norm ++ FieldA.frec B uB Bs idx :: fsRest.map FieldA.norm := by
        rw [hfs, List.map_append]; rfl
      have hTD_C := applyTelA_groupCtor_prefix gc lsC hfsN
        (by simpa using hpre) qs (consListA qs SubstA.id)
      have hTD_F := applyTelA_groupCtor_prefix gc lsF hfsN
        (by simpa using hpre) qs (consListA qs SubstA.id)
      have hTD_R := applyTelA_groupCtor_prefix gc lsF' hfsN
        (by simpa using hpre') qs' (consListA qs' SubstA.id)
      simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA, plainArgsA_norm] at hTD_C hTD_F hTD_R
      simp only [List.map, FieldA.instLevels, FieldA.shape, FieldA.norm, ctorFieldsA] at hs
      have hTvC := C.ctorTel gc lsC hlC hqs
      have hTvF := C.ctorTel gc lsF hlF hqs
      have hTvR := C.ctorTel gc lsF' hlF' hqs'
      cases hs with
      | funRec _ _ _ _ _ _ v v' j _ vs₀ vs₀' hh hs' =>
        have hpl : pre.length = (fsPre.map FieldA.shape).length := by rw [List.length_map]; exact hpre
        have hvF := RecBaseA.frecFieldRel C hΓ hbF hlF hk hFC hqs hqd hgcE hsp hpl hTvC hTvF hwC hTD_C hTD_F
          (XF := fun ρ' D y y' => RecIHWA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx'
            ρ' D y y' ∧ LfpWA (FamPhiWA E (iotaIfaceA E) n Γ f fm (famRsA E (iotaIfaceA E) n ρ₀ k Γ)
              (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm) (famRsIA E (iotaIfaceA E) n ρ₀ k Γ)) ρ' D y y')
          (fun _ _ _ _ h => h.2) hh
        have hTel := RecBaseA.frecTelConv C hΓ hbF hlF hFF hqs hqs' hqq hgcE hsp hTvF hTvR hwF hTD_F hTD_R
        rw [piDomListA_frecDomA, piDomListA_frecDomA] at hTel
        have hdlF := gc.view.frec_length B uB Bs idx (by rw [hfs]; simp)
        obtain ⟨RM, hRM⟩ := hM
        simp only [List.map, FieldA.instLevels, minorFieldsA] at hRM
        obtain ⟨⟨RL, hRL⟩, hcod⟩ := LRTyA_pi_peel hΓ hRM
          (by rw [isZero_imax, minorFieldsA_snd, minorLevelA_isZero]; exact hwM)
        obtain ⟨RI, hRI⟩ := hcod v v' hvF
        rw [instantiate0A_eq_substA_cons, substA_pi, frecIHA_closed_cons] at hRI
        obtain ⟨⟨RIH, hRIH⟩, hcod₂⟩ := LRTyA_pi_peel hΓ hRI
          (by rw [minorFieldsA_snd, minorLevelA_isZero]; exact hwM)
        have hvF' := hvF
        have hTD_C' := hTD_C
        have hTD_F' := hTD_F
        have hTD_R' := hTD_R
        rw [frecDomA_eq_piTelA'] at hvF' hTD_C' hTD_F' hTD_R'
        have hdC : (substTelA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
            ((instantiateLevelsA lsC B, instLevel lsC uB) :: instDomsA lsC Bs)).length = Bs.length + 1 := by
          rw [substTelA_length, List.length_cons, instDomsA_length]
        have hdF : (substTelA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
            ((instantiateLevelsA lsF B, instLevel lsF uB) :: instDomsA lsF Bs)).length = Bs.length + 1 := by
          rw [substTelA_length, List.length_cons, instDomsA_length]
        have hdR : (substTelA (consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id))
            ((instantiateLevelsA lsF' B, instLevel lsF' uB) :: instDomsA lsF' Bs)).length = Bs.length + 1
              := by
          rw [substTelA_length, List.length_cons, instDomsA_length]
        have hh' := hpl ▸ hh
        rw [frecDomA_eq_piTelA'] at hh'
        have hIHrel := RecBaseA.frecIHRel (is₁ := is₁) (is₁' := is₁') C hΓ hbF hlF hFF hk hFC hqs hqs' hqq
          hgcE hsp hTvC hTvF hTvR hwC hwF
          hTD_C' hTD_F' hTD_R' hdC hdF hdR (isZero_false_of_uniformType (uniformType_instLevel C.hUT lsF))
          (isZero_false_of_uniformType (uniformType_instLevel C.hUT lsC)) hh' hvF'
          (by rw [List.length_map, List.length_map]; exact hdlF) hpfx hpfx' hwM hTel ⟨RIH, hRIH⟩
        obtain ⟨RM₁, hRM₁⟩ := hcod₂ _ _ hIHrel
        rw [instantiate0A_instantiate0A_up] at hRM₁
        rw [substA_minorFieldsA_drec f gc.ref lsF (instLevel lsF fv.sort) wM
          (gc.view.res.map (instantiateLevelsA lsF)) (fsRest.map (FieldA.instLevels lsF)) qs mot pre
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) v _] at hRM₁
        have e2 := instantiate0A_ctorFieldsA_drec f lsF (instLevel lsF fv.sort) (gc.view.res.map
          (instantiateLevelsA lsF))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF)) qs (consListA (plainArgsA fsPre pre) (consListA qs
            SubstA.id)) v
        have e3 := instantiate0A_ctorFieldsA_drec f lsF' (instLevel lsF' fv.sort)
          (gc.view.res.map (instantiateLevelsA lsF')) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF')) qs'
          (consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id)) v'
        have eC := instantiate0A_ctorFieldsA_drec f lsC (instLevel lsC fv.sort) (gc.view.res.map
          (instantiateLevelsA lsC))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsC)) qs (consListA (plainArgsA fsPre pre) (consListA qs
            SubstA.id)) v
        have hσ₁ : consListA (plainArgsA (fsPre ++ [FieldA.frec B uB Bs idx]) (pre ++ [v])) (consListA qs
          SubstA.id) =
            consListA (plainArgsA fsPre pre) (consListA qs SubstA.id) := by
          rw [plainArgsA_snoc_frec B uB Bs idx v fsPre pre hpre]
        have hσ₁' : consListA (plainArgsA (fsPre ++ [FieldA.frec B uB Bs idx]) (pre' ++ [v'])) (consListA
          qs' SubstA.id) =
            consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id) := by
          rw [plainArgsA_snoc_frec B uB Bs idx v' fsPre pre' hpre']
        have hfs₁ : gc.view.fields = (fsPre ++ [FieldA.frec B uB Bs idx]) ++ fsRest := by
          rw [hfs, List.append_assoc]; rfl
        have hpre₁ : (pre ++ [v]).length = (fsPre ++ [FieldA.frec B uB Bs idx]).length := by simp [hpre]
        have hwC₁ := argsRelA_snoc hwC (FieldShape.recursive (Bs.length + 1)) hTD_C hh
        have hwF₁ := argsRelA_snoc (X := fun _ _ _ => True) (f := v) (f' := v') hwF
          (FieldShape.recursive (Bs.length + 1)) hTD_F trivial
        have hwK₁ := argsRelKA_append hwK hTD_F (ArgsRelKA.cons _ _ _ _ v v' [] [] hvF (.nil _))
        have ek : fsPre.map FieldA.shape ++ [FieldShape.recursive (Bs.length + 1)] =
            (fsPre ++ [FieldA.frec B uB Bs idx]).map FieldA.shape := by
          simp [FieldA.shape]
        rw [ek] at hwC₁ hwF₁
        have hs₁ : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC)
            (famRecRelA fm qs lsD (fun D y y' =>
              RecIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' D y y' ∧
              FamLfpA E n ρ₀ k Γ f fm D y y'))
            (FamFunIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' gc.ref lsC qs lsD)
            (fm.nparamsA + (pre ++ [v]).length) (qs ++ (pre ++ [v]))
            (ctorFieldsA f lsC (instLevel lsC fv.sort) qs
              (consListA (plainArgsA (fsPre ++ [FieldA.frec B uB Bs idx]) (pre ++ [v]))
                (consListA qs SubstA.id)) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsC))
              (gc.view.res.map (instantiateLevelsA lsC))).1
            (fsRest.map FieldA.shape) vs₀ vs₀' := by
          rw [hσ₁, ← eC, List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc]
          exact hs'
        have hM₁ : ∃ R, LRTyA E (iotaIfaceA E) n ρ₀ k Γ
            (minorFieldsA f gc.ref lsF (instLevel lsF fv.sort) wM qs mot (pre ++ [v])
              (consListA (plainArgsA (fsPre ++ [FieldA.frec B uB Bs idx]) (pre ++ [v]))
                (consListA qs SubstA.id))
              (fsRest.map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1 R := by
          rw [hσ₁]; exact ⟨RM₁, hRM₁⟩
        obtain ⟨ih1, ih2⟩ := minorWalkA C hΓ hbF hlF hFF hk hqs hqs' hqq hgcE hFC lsD hpfx hpfx' hwM hdl
          fsRest
          (fsPre ++ [FieldA.frec B uB Bs idx]) (pre ++ [v]) (pre' ++ [v']) vs₀ vs₀' hfs₁ hpre₁ hwC₁ hs₁ hwF₁
          hwK₁ hM₁
        rw [hσ₁, hσ₁'] at ih1
        refine ⟨?_, by simpa using ih2⟩
        simp only [List.map, FieldA.instLevels, FieldA.shape, ctorFieldsA, minorFieldsA, rhsArgsA, recCallsA,
          List.singleton_append]
        rw [e2, e3]
        simp only [frecDomA_eq_piTelA']
        refine .cons _ _ _ _ v v' _ _ hvF' ?_
        rw [instantiate0A_eq_substA_cons v, substA_pi, frecIHA_closed_cons]
        refine .cons _ _ _ _ _ _ _ _ hIHrel ?_
        rw [instantiate0A_instantiate0A_up, substA_minorFieldsA_drec f gc.ref lsF (instLevel lsF fv.sort) wM
          (gc.view.res.map (instantiateLevelsA lsF)) (fsRest.map (FieldA.instLevels lsF)) qs mot pre
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) v _]
        exact ih1

  | .drec idx :: fsRest, fsPre, pre, pre', vs, vs', hfs, hpre, hwC, hs, hwF, hwK, hM => by
      have hpre' : pre'.length = fsPre.length := by rw [(argsRelA_length hwC).2, List.length_map]
      have hlC : lsC.length = fm.arity := (eqNListA_length hFC.1).symm.trans hlF
      have hlF' : lsF'.length = fm.arity := (eqNListA_length hFF.1).symm.trans hlF
      have hkinds := gc.view.shapes C.hfresh
      have hkinds' : ctorShapesA f fm.nparamsA (gc.member.normA.getD gc.member.mtypeA) =
          some (gc.view.fields.map FieldA.shape) := gc.normA_getD.symm ▸ hkinds
      have hqd := argsRelKA_refl_left C.hNCT hqq
      have hsp : gc.view.fields.map FieldA.shape =
          fsPre.map FieldA.shape ++ FieldShape.recursive 0 :: fsRest.map FieldA.shape := by
        rw [hfs, List.map_append]; rfl
      have hfsN : gc.view.fields.map FieldA.norm =
          fsPre.map FieldA.norm ++ FieldA.drec idx :: fsRest.map FieldA.norm := by
        rw [hfs, List.map_append]; rfl
      have hTD_C := applyTelA_groupCtor_prefix gc lsC hfsN
        (by simpa using hpre) qs (consListA qs SubstA.id)
      have hTD_F := applyTelA_groupCtor_prefix gc lsF hfsN
        (by simpa using hpre) qs (consListA qs SubstA.id)
      have hTD_R := applyTelA_groupCtor_prefix gc lsF' hfsN
        (by simpa using hpre') qs' (consListA qs' SubstA.id)
      simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA, plainArgsA_norm] at hTD_C hTD_F hTD_R
      simp only [List.map, FieldA.instLevels, FieldA.shape, FieldA.norm, ctorFieldsA] at hs
      have hTvC := C.ctorTel gc lsC hlC hqs
      have hTvF := C.ctorTel gc lsF hlF hqs
      have hTvR := C.ctorTel gc lsF' hlF' hqs'
      cases hs with
      | directRec _ _ _ _ _ _ v v' _ vs₀ vs₀' hh hs' =>
        -- the recursive domain moved within the fiber to `lsF`
        have hRD₀ := recDomA (fv := fv) (cs := cs) C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hS C.hfm
          C.hcls C.hfresh C.hcensus C.hcl C.hT C.hUT hbF hlF hk (k := k) hΓ (ps := qs) (ps' := qs)
          (is := []) (is' := []) hqs hqs hqd (ρ := []) (Or.inl rfl) hgcE gc.hcls
          gc.view.famRef hkinds' hsp (eqNListA_refl lsF) hFC (eqNListB_symm hFC hbF)
          (by rw [map_wkExprA_nil]; exact hTvC) (by rw [map_wkExprA_nil]; exact hTvF)
          (by rw [map_wkExprA_nil]; exact argsRelA_diag C.hNCT (famRsA_refl_left C.hNCT) hwC) hTD_C hTD_F
        have hRD : RecDomRelA E (iotaIfaceA E) n Γ f fm (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm []) lsF qs
            (foldAppsA (.const f lsC) (qs ++ (idx.map (instantiateLevelsA lsC)).map
              (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)))))
            (foldAppsA (.const f lsF) (qs ++ (idx.map (instantiateLevelsA lsF)).map
              (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))))) := by
          simpa only [map_wkExprA_nil] using hRD₀
        have hLfpL := (lfpWA_recDom (ρ := []) (C.idxPer hbF hlF hk hΓ hqs hqd) hqs hRD).1 hh.2.2.2
        -- the minor's field binder, then its induction hypothesis binder
        obtain ⟨RM, hRM⟩ := hM
        simp only [List.map, FieldA.instLevels, minorFieldsA] at hRM
        obtain ⟨⟨RL, hRL⟩, hcod⟩ := LRTyA_pi_peel hΓ hRM
          (by rw [isZero_imax, minorFieldsA_snd, minorLevelA_isZero]; exact hwM)
        have hvF := C.lrRel hqs hRL hLfpL
        obtain ⟨RI, hRI⟩ := hcod v v' hvF
        rw [instantiate0A_eq_substA_cons, substA_pi, substA_cons_ihDom] at hRI
        obtain ⟨_, hcod₂⟩ := LRTyA_pi_peel hΓ hRI (by rw [minorFieldsA_snd, minorLevelA_isZero]; exact hwM)
        -- the indices the two reducts read, related along the family's telescope at `lsF`
        have hRR₀ := recDomA (fv := fv) (cs := cs) C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hS C.hfm
          C.hcls C.hfresh C.hcensus C.hcl C.hT C.hUT hbF hlF hk (k := k) hΓ (ps := qs) (ps' := qs')
          (is := []) (is' := []) hqs hqs' hqq (ρ := []) (Or.inl rfl) hgcE gc.hcls
          gc.view.famRef hkinds' hsp (eqNListA_refl lsF) (eqNListB_refl hbF) hFF
          (by rw [map_wkExprA_nil]; exact hTvF) (by rw [map_wkExprA_nil]; exact hTvR)
          (by rw [map_wkExprA_nil]; exact hwF) hTD_F hTD_R
        simp only [map_wkExprA_nil] at hRR₀
        obtain ⟨lsA, lsA', isA, isA', TF, TF', hA, hA', _, _, hTF, _, hwI, _⟩ := hRR₀
        obtain ⟨_, elA, exA⟩ := foldAppsA_const_inj hA
        obtain ⟨_, elA', exA'⟩ := foldAppsA_const_inj hA'
        have exA₁ := List.append_cancel_left exA
        have exA₁' := List.append_cancel_left exA'
        subst elA elA' exA₁ exA₁'
        have hidxF := argsRelPA_famRsFA_KA hwI hTF
        have hqq' : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsF fm.mtypeA) qs qs' := by
          simpa only [List.append_nil] using hqq
        have hidx := argsRelKA_append hqq' hTF hidxF
        have hIHrel := hh.2.2.1 _ _ (by
          simp only [List.length_map]
          exact hdl idx (List.mem_map.mpr ⟨.drec idx, by rw [hfs]; simp, rfl⟩)) hRD hidx
        obtain ⟨RM₁, hRM₁⟩ := hcod₂ _ _ hIHrel
        rw [instantiate0A_instantiate0A_up] at hRM₁
        have e1 := substA_minorFieldsA_drec f gc.ref lsF (instLevel lsF fv.sort) wM
          (gc.view.res.map (instantiateLevelsA lsF)) (fsRest.map (FieldA.instLevels lsF)) qs mot pre
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) v
          (foldAppsA (.const r ls) (pfx ++ (idx.map (instantiateLevelsA lsF)).map
            (substA (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))) ++ [v]))
        rw [e1] at hRM₁
        have e2 := instantiate0A_ctorFieldsA_drec f lsF (instLevel lsF fv.sort) (gc.view.res.map
          (instantiateLevelsA lsF))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF)) qs (consListA (plainArgsA fsPre pre)
            (consListA qs SubstA.id)) v
        have e3 := instantiate0A_ctorFieldsA_drec f lsF' (instLevel lsF' fv.sort)
          (gc.view.res.map (instantiateLevelsA lsF')) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsF')) qs'
          (consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id)) v'
        have eC := instantiate0A_ctorFieldsA_drec f lsC (instLevel lsC fv.sort) (gc.view.res.map
          (instantiateLevelsA lsC))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsC)) qs (consListA (plainArgsA fsPre pre)
            (consListA qs SubstA.id)) v
        have hσ₁ : consListA (plainArgsA (fsPre ++ [FieldA.drec idx]) (pre ++ [v])) (consListA qs SubstA.id) =
            consListA (plainArgsA fsPre pre) (consListA qs SubstA.id) := by
          rw [plainArgsA_snoc_drec idx v fsPre pre hpre]
        have hσ₁' : consListA (plainArgsA (fsPre ++ [FieldA.drec idx]) (pre' ++ [v'])) (consListA qs' SubstA.id) =
            consListA (plainArgsA fsPre pre') (consListA qs' SubstA.id) := by
          rw [plainArgsA_snoc_drec idx v' fsPre pre' hpre']
        -- the extended prefixes
        have hfs₁ : gc.view.fields = (fsPre ++ [FieldA.drec idx]) ++ fsRest := by rw [hfs, List.append_assoc]; rfl
        have hpre₁ : (pre ++ [v]).length = (fsPre ++ [FieldA.drec idx]).length := by simp [hpre]
        have hwC₁ := argsRelA_snoc hwC (FieldShape.recursive 0) hTD_C hh
        have hwF₁ := argsRelA_snoc (X := fun _ _ _ => True) (f := v) (f' := v') hwF (FieldShape.recursive 0) hTD_F trivial
        have hwK₁ := argsRelKA_append hwK hTD_F (ArgsRelKA.cons _ _ _ _ v v' [] [] hvF (.nil _))
        have ek : fsPre.map FieldA.shape ++ [FieldShape.recursive 0] = (fsPre ++ [FieldA.drec idx]).map FieldA.shape := by
          simp [FieldA.shape]
        rw [ek] at hwC₁ hwF₁
        have hs₁ : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC)
            (famRecRelA fm qs lsD (fun D y y' =>
              RecIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' D y y' ∧
              FamLfpA E n ρ₀ k Γ f fm D y y'))
            (FamFunIHA E n ρ₀ k Γ f r fm fv.indices.length lsF ls ls' mot qs qs' pfx pfx' gc.ref lsC qs lsD) (fm.nparamsA + (pre ++ [v]).length) (qs ++ (pre ++ [v]))
            (ctorFieldsA f lsC (instLevel lsC fv.sort) qs (consListA (plainArgsA (fsPre ++ [FieldA.drec idx])
              (pre ++ [v])) (consListA qs SubstA.id)) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsC))
              (gc.view.res.map (instantiateLevelsA lsC))).1
            (fsRest.map FieldA.shape) vs₀ vs₀' := by
          rw [hσ₁, ← eC, List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc]
          exact hs'
        have hM₁ : ∃ R, LRTyA E (iotaIfaceA E) n ρ₀ k Γ
            (minorFieldsA f gc.ref lsF (instLevel lsF fv.sort) wM qs mot (pre ++ [v])
              (consListA (plainArgsA (fsPre ++ [FieldA.drec idx]) (pre ++ [v])) (consListA qs SubstA.id))
              (fsRest.map (FieldA.instLevels lsF)) (gc.view.res.map (instantiateLevelsA lsF))).1 R := by
          rw [hσ₁]; exact ⟨RM₁, hRM₁⟩
        obtain ⟨ih1, ih2⟩ := minorWalkA C hΓ hbF hlF hFF hk hqs hqs' hqq hgcE hFC lsD hpfx hpfx' hwM hdl
          fsRest
          (fsPre ++ [FieldA.drec idx]) (pre ++ [v]) (pre' ++ [v']) vs₀ vs₀' hfs₁ hpre₁ hwC₁ hs₁ hwF₁ hwK₁ hM₁
        rw [hσ₁, hσ₁'] at ih1
        refine ⟨?_, by simpa using ih2⟩
        simp only [List.map, FieldA.instLevels, FieldA.shape, ctorFieldsA, minorFieldsA, rhsArgsA, recCallsA,
          List.singleton_append]
        rw [e2, e3, recCallFieldA_eq r ls pfx is₁ fm.nparamsA cs.length hpfx v f lsF qs _ hqs,
          recCallFieldA_eq r ls' pfx' is₁' fm.nparamsA cs.length hpfx' v' f lsF' qs' _ hqs']
        refine .cons _ _ _ _ v v' _ _ hvF ?_
        rw [instantiate0A_eq_substA_cons v, substA_pi, substA_cons_ihDom]
        refine .cons _ _ _ _ _ _ _ _ hIHrel ?_
        rw [instantiate0A_instantiate0A_up, e1]
        exact ih1

end MinorWalk

/-! ## (6) helpers for the core induction -/

section CoreHelpers
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem levelsBounded_take {k : Nat} : (ls : List Level) → (a : Nat) → levelsBounded k ls = true →
    levelsBounded k (ls.take a) = true
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, _ => rfl
  | l :: ls, a + 1, h => by
      simp only [levelsBounded, Bool.and_eq_true] at h
      show (levelBounded k l && levelsBounded k (ls.take a)) = true
      rw [Bool.and_eq_true]
      exact ⟨h.1, levelsBounded_take ls a h.2⟩

theorem eqNList_take : (ls ls' : List Level) → (a : Nat) → eqNList ls ls' → eqNList (ls.take a) (ls'.take a)
  | [], [], 0, _ => trivial
  | [], [], _ + 1, _ => trivial
  | _ :: _, _ :: _, 0, _ => trivial
  | _ :: ls, _ :: ls', a + 1, h => ⟨h.1, eqNList_take ls ls' a h.2⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- the converse of `argsRelPA_famRsFA_KA`, at the identity world. -/
theorem argsRelKA_famRsFA_PA {j : Nat} {Γ : LCtxA} {fm : CheckedMemberA} {lsF : List Level} :
    {i : Nat} → {prev : List ExprA} → {T : ExprA} → {pre pre' : List ExprA} →
    ArgsRelKA E I n ρ₀ j Γ T pre pre' →
    applyTelA prev (instantiateLevelsA lsF fm.mtypeA) = some T →
    ArgsRelPA (famRsFA E I n ρ₀ j Γ fm [] lsF) i prev T pre pre'
  | _, _, _, _, _, .nil _, _ => .nil _ _ _
  | i, prev, _, _, _, .cons A u B v f f' fs fs' h hs, hT => by
      refine .cons i prev A u B v f f' fs fs' ⟨A, u, B, v, hT, h⟩ (argsRelKA_famRsFA_PA hs ?_)
      rw [applyTelA_append, hT]; rfl

/-- the motive's type, under the parameters' values `qs`, at a full index list: the major's binder over
    the family at the parameters and the indices. -/
theorem applyTelA_motTyA (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level)) (wF wM : Level)
    (qs is : List ExprA) (hqs : qs.length = params.length) (his : is.length = idxs.length) :
    applyTelA is (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) =
      some (.pi (foldAppsA (.const f ls) (qs ++ is)) wF (.sort wM) (.succ wM)) := by
  have h := applyTelA_piTelA (.pi (famLocalsA f ls params.length idxs.length) wF (.sort wM) (.succ wM))
    (.imax wF (.succ wM)) idxs is his (consListA qs SubstA.id)
  show applyTelA is (substA (consListA qs SubstA.id) (piTelA idxs
    (.pi (famLocalsA f ls params.length idxs.length) wF (.sort wM) (.succ wM)) (.imax wF (.succ wM))).1) = _
  rw [h, substA_pi]
  have hfun : (substA (consListA is (consListA qs SubstA.id)) ∘ liftA 0 is.length) =
      substA (consListA qs SubstA.id) := funext fun e => substA_consListA_liftA is _ e
  have e : substA (consListA is (consListA qs SubstA.id)) (famLocalsA f ls params.length idxs.length) =
      foldAppsA (.const f ls) (qs ++ is) := by
    rw [famLocalsA, substA_foldAppsA, substA_const, List.map_append, ← his, paramLocalsA_consListA,
      List.map_map, hfun, ← hqs, paramLocalsA_consListA]
  rw [e]
  rfl

theorem applyTelA_motTyA_full (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level)) (wF wM : Level)
    (qs is : List ExprA) (x : ExprA) (hqs : qs.length = params.length) (his : is.length = idxs.length) :
    applyTelA (is ++ [x]) (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) =
      some (.sort wM) := by
  rw [applyTelA_append, applyTelA_motTyA f ls params idxs wF wM qs is hqs his]
  rfl

/-- a substitution keeps a telescope's binders and their levels. -/
theorem isPiTelA_substA : (len : Nat) → (σ : SubstA) → (T : ExprA) → IsPiTelA len T → IsPiTelA len (substA σ T)
  | 0, _, _, _ => trivial
  | len + 1, σ, .pi _ _ C _, ⟨hv, h⟩ => ⟨hv, isPiTelA_substA len σ.up C h⟩
  | _ + 1, _, .bvar _, h => h.elim
  | _ + 1, _, .sort _, h => h.elim
  | _ + 1, _, .const _ _, h => h.elim
  | _ + 1, _, .app _ _, h => h.elim
  | _ + 1, _, .lam _ _ _, h => h.elim
  | _ + 1, _, .letE _ _ _, h => h.elim
  | _ + 1, _, .lit _, h => h.elim

theorem isPiTelA_motTyA (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level)) (wF wM : Level)
    (σ : SubstA) : IsPiTelA (idxs.length + 1) (substA σ (motTyA f ls params idxs wF wM).1) :=
  isPiTelA_substA _ σ _ (isPiTelA_piTelA_app (.pi (famLocalsA f ls params.length idxs.length) wF (.sort wM)
    (.succ wM)) (.imax wF (.succ wM)) (by rw [isZero_imax]; rfl) (L := 1) ⟨rfl, trivial⟩ idxs)

/-- the motive's arguments: related indices (any body) under the parameters' values, a related major. -/
theorem motArgsA {k : Nat} {Γ : LCtxA} (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level))
    (wF wM : Level) (B : ExprA) (w : Level) {qs is is' : List ExprA} {x x' : ExprA}
    (hqs : qs.length = params.length)
    (hidx : ArgsRelKA E I n ρ₀ k Γ (substA (consListA qs SubstA.id) (piTelA idxs B w).1) is is')
    (his : is.length = idxs.length)
    (hx : LRRelA E I n ρ₀ k Γ (foldAppsA (.const f ls) (qs ++ is)) x x') :
    ArgsRelKA E I n ρ₀ k Γ (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1)
      (is ++ [x]) (is' ++ [x']) := by
  have h1 : ArgsRelKA E I n ρ₀ k Γ (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) is is' :=
    argsRelKA_piTelA_body (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := k) (Γ := Γ) B
      (.pi (famLocalsA f ls params.length idxs.length) wF (.sort wM) (.succ wM)) w (.imax wF (.succ wM)) idxs
      (consListA qs SubstA.id) hidx his
  exact argsRelKA_append h1 (applyTelA_motTyA f ls params idxs wF wM qs is hqs his)
    (.cons _ _ _ _ x x' [] [] hx (.nil _))

/-- the motive at related indices and majors: related at its sort. -/
theorem motRelA {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {f : Nat} {ls : List Level}
    {params idxs : List (ExprA × Level)} {wF wM : Level} {qs : List ExprA} (hqs : qs.length = params.length)
    {mA mA' : ExprA}
    (hm : LRRelA E I n ρ₀ k Γ (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) mA mA')
    {B : ExprA} {w : Level} {is is' : List ExprA} {x x' : ExprA}
    (hidx : ArgsRelKA E I n ρ₀ k Γ (substA (consListA qs SubstA.id) (piTelA idxs B w).1) is is')
    (his : is.length = idxs.length)
    (hx : LRRelA E I n ρ₀ k Γ (foldAppsA (.const f ls) (qs ++ is)) x x') :
    LRRelA E I n ρ₀ k Γ (.sort wM) (foldAppsA mA (is ++ [x])) (foldAppsA mA' (is' ++ [x'])) :=
  LRRelA_apps hΓ (motArgsA f ls params idxs wF wM B w hqs hidx his hx) (idxs.length + 1) (by simp [his])
    (isPiTelA_motTyA f ls params idxs wF wM _) hm _ (applyTelA_motTyA_full f ls params idxs wF wM qs is x hqs his)

/-- the motive at related indices: related at the major's binder. -/
theorem motPiA {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {f : Nat} {ls : List Level}
    {params idxs : List (ExprA × Level)} {wF wM : Level} {qs : List ExprA} (hqs : qs.length = params.length)
    {mA mA' : ExprA}
    (hm : LRRelA E I n ρ₀ k Γ (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) mA mA')
    {B : ExprA} {w : Level} {is is' : List ExprA}
    (hidx : ArgsRelKA E I n ρ₀ k Γ (substA (consListA qs SubstA.id) (piTelA idxs B w).1) is is')
    (his : is.length = idxs.length) :
    LRRelA E I n ρ₀ k Γ (.pi (foldAppsA (.const f ls) (qs ++ is)) wF (.sort wM) (.succ wM))
      (foldAppsA mA is) (foldAppsA mA' is') := by
  have h1 : ArgsRelKA E I n ρ₀ k Γ (substA (consListA qs SubstA.id) (motTyA f ls params idxs wF wM).1) is is' :=
    argsRelKA_piTelA_body (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := k) (Γ := Γ) B
      (.pi (famLocalsA f ls params.length idxs.length) wF (.sort wM) (.succ wM)) w (.imax wF (.succ wM)) idxs
      (consListA qs SubstA.id) hidx his
  exact LRRelA_apps hΓ h1 idxs.length (Nat.le_of_eq his)
    (isPiTelA_mono _ _ _ (Nat.le_succ _) (isPiTelA_motTyA f ls params idxs wF wM _)) hm _
    (applyTelA_motTyA f ls params idxs wF wM qs is hqs his)

/-- an application into a sort at two convertible arguments: both typed, type-convertible. -/
theorem appSortConvA {Γ : LCtxA} {g D w w' : ExprA} {u v : Level}
    (hg : HasTyA E I n Γ g (.pi D u (.sort v) (.succ v)))
    (hw : HasTyA E I n Γ w D) (hw' : HasTyA E I n Γ w' D) (hc : ConvA E I n Γ w w' D) :
    Nonempty (HasTyA E I n Γ (.app g w) (.sort v)) ∧ Nonempty (HasTyA E I n Γ (.app g w') (.sort v)) ∧
      Nonempty (TyConvA E I n Γ (.app g w) (.app g w')) := by
  have hB : HasTyA E I n (.assumption D :: Γ) (.sort v) (.sort (.succ v)) := .sort _ v
  have ha : HasTyA E I n Γ (.app g w) (.sort v) :=
    .app Γ g w D (.sort v) u (.succ v) (.succ v) hB (.sort Γ v) hg hw
  have ha' : HasTyA E I n Γ (.app g w') (.sort v) :=
    .app Γ g w' D (.sort v) u (.succ v) (.succ v) hB (.sort Γ v) hg hw'
  exact ⟨⟨ha⟩, ⟨ha'⟩, ⟨.of Γ _ _ v v v ha (eqNA_refl v) ha' (eqNA_refl v)
    (.app Γ g g w w' D (.sort v) u (.succ v) (.refl Γ g _ hg) hc hB ha')⟩⟩

/-- the motive's instances along a chain from a term convertible to `y`: typed, convertible to the
    instance at `y`. -/
theorem motInstCondA {Γ : LCtxA} {g Dm D y z w : ExprA} {u v : Level}
    (hg : HasTyA E I n Γ g (.pi Dm u (.sort v) (.succ v))) (hDc : TyConvA E I n Γ D Dm)
    (hy : HasTyA E I n Γ y Dm) (hyz : ConvA E I n Γ y z D) (hzw : TyHRedStarA E I n Γ z w D) :
    (∃ s, Nonempty (HasTyA E I n Γ (.app g w) (.sort s))) ∧
      Nonempty (TyConvA E I n Γ (.app g w) (.app g y)) := by
  obtain ⟨czw⟩ := tyHRedStarA_conv hzw
  obtain ⟨tw⟩ := tyHRedStarA_hasTy_end hzw
  obtain ⟨_, ⟨tw'⟩, ⟨tc⟩⟩ := appSortConvA hg hy (hasTyA_of_tyConvA tw hDc)
    (convA_of_tyConvA (.trans _ _ _ _ _ hyz czw) hDc)
  exact ⟨⟨v, ⟨tw'⟩⟩, ⟨tc.symm⟩⟩

/-- a recursor spine one short of its telescope, of a group with a constructor, is at its major. -/
theorem recAtMajorA_recSpine {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (hcls : m.mclass = .recursorM) (hctor : recHasCtorA r m = true) (ls : List Level) (xs : List ExprA)
    (hlen : xs.length + 1 = piCountA m.mtypeA) : recAtMajorA E (foldAppsA (.const r ls) xs) = true := by
  unfold recAtMajorA
  rw [foldAppsA_const_head]
  exact (recAtMajorA'_const E r ls xs.length).2 ⟨m, hres, hcls, hlen, hctor⟩

/-- the recursor's telescope after the parameters, the motive, the minors and the indices: the major's
    binder over the family application at the parameters and the indices, its codomain the motive at
    the indices and the major. -/
theorem applyTelA_recPrefixA (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level)) (wF wM w : Level)
    (cds : List MinorDataA) (qs : List ExprA) (mot : ExprA) (ms is : List ExprA) (hqs : qs.length = params.length)
    (hms : ms.length = cds.length) (his : is.length = idxs.length) :
    ∃ B, applyTelA (qs ++ ([mot] ++ ms ++ is))
        (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
      some (.pi (foldAppsA (.const f ls) (qs ++ is)) wF B w) ∧
      ∀ x, instantiate0A x B = foldAppsA mot (is ++ [x]) := by
  have hT : (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
      substA SubstA.id (piTelA (params ++ ([motTyA f ls params idxs wF wM] ++
        minorDomsA f ls wF wM params.length 0 cds ++ liftDomsA 0 (cds.length + 1) idxs))
        (.pi (liftA idxs.length (cds.length + 1) (famLocalsA f ls params.length idxs.length)) wF
          (recBodyA idxs.length cds.length) w) (.imax wF w)).1 := by
    rw [substA_id, recDomsA, piTelA_append]
    simp only [List.append_assoc]
    rfl
  have hlen : (qs ++ ([mot] ++ ms ++ is)).length = (params ++ ([motTyA f ls params idxs wF wM] ++
      minorDomsA f ls wF wM params.length 0 cds ++ liftDomsA 0 (cds.length + 1) idxs)).length := by
    simp only [List.length_append, List.length_singleton, minorDomsA_length, liftDomsA_length, hms, his, hqs]
  rw [hT, applyTelA_piTelA _ _ _ _ hlen SubstA.id, substA_pi]
  have hfun : (substA (consListA is (consListA qs SubstA.id)) ∘ liftA 0 is.length) =
      substA (consListA qs SubstA.id) := funext fun e => substA_consListA_liftA is _ e
  have e : substA (consListA (qs ++ ([mot] ++ ms ++ is)) SubstA.id)
      (liftA idxs.length (cds.length + 1) (famLocalsA f ls params.length idxs.length)) =
      foldAppsA (.const f ls) (qs ++ is) := by
    have e1 : cds.length + 1 = ([mot] ++ ms).length := by
      rw [List.length_append, hms, List.length_singleton]; omega
    rw [consListA_append, consListA_append, e1, ← his, substA_consListA_liftA_cut, famLocalsA, substA_foldAppsA,
      substA_const, List.map_append, paramLocalsA_consListA, List.map_map, hfun, ← hqs, paramLocalsA_consListA]
  refine ⟨substA (consListA (qs ++ ([mot] ++ ms ++ is)) SubstA.id).up (recBodyA idxs.length cds.length), ?_,
    fun x => ?_⟩
  · rw [e]
  · rw [instantiate0A_substA_up, ← consListA_snoc,
      show qs ++ ([mot] ++ ms ++ is) ++ [x] = qs ++ ([mot] ++ ms ++ is ++ [x]) by simp, consListA_append,
      ← hms, ← his]
    exact substA_recBodyA mot x ms is

theorem applyTelA_recFullA (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level)) (wF wM w : Level)
    (cds : List MinorDataA) (qs : List ExprA) (mot x : ExprA) (ms is : List ExprA) (hqs : qs.length = params.length)
    (hms : ms.length = cds.length) (his : is.length = idxs.length) :
    applyTelA (qs ++ ([mot] ++ ms ++ is ++ [x]))
        (piTelA (recDomsA f ls params idxs wF wM cds) (recBodyA idxs.length cds.length) w).1 =
      some (foldAppsA mot (is ++ [x])) := by
  obtain ⟨B, hB, hx⟩ := applyTelA_recPrefixA f ls params idxs wF wM w cds qs mot ms is hqs hms his
  rw [show qs ++ ([mot] ++ ms ++ is ++ [x]) = qs ++ ([mot] ++ ms ++ is) ++ [x] by simp, applyTelA_append, hB]
  show some (instantiate0A x B) = _
  rw [hx]

/-- the minor's binder count: a field, and an induction hypothesis after a recursive one. -/
def minorArityA : List FieldA → Nat
  | [] => 0
  | .plain _ _ :: fs => minorArityA fs + 1
  | .drec _ :: fs | .frec _ _ _ _ :: fs | .drecD _ _ :: fs => minorArityA fs + 2

theorem isPiTelA_minorFieldsA (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA)
    (hwM : isZero wM = false) :
    (fs : List FieldA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    IsPiTelA (minorArityA fs) (minorFieldsA f c ls wF wM pl mot fl σ fs res).1
  | [], _, _, _, _ => trivial
  | .plain _ _ :: fs, _, _, _, _ =>
      ⟨by rw [minorFieldsA_snd, minorLevelA_isZero, hwM], isPiTelA_minorFieldsA f c ls wF wM res hwM fs _ _ _ _⟩
  | .drec _ :: fs, _, _, _, _ | .frec _ _ _ _ :: fs, _, _, _, _ | .drecD _ _ :: fs, _, _, _, _ =>
      ⟨by rw [isZero_imax, minorFieldsA_snd, minorLevelA_isZero, hwM],
        ⟨by rw [minorFieldsA_snd, minorLevelA_isZero, hwM], isPiTelA_minorFieldsA f c ls wF wM res hwM fs _ _ _ _⟩⟩

theorem rhsArgsA_length_le (rc : ExprA) (PRE : List ExprA) (np K : Nat) (f : Nat) (ls : List Level) (wF : Level)
    (res : List ExprA) (pl : List ExprA) :
    (fsR : List FieldA) → (σ : SubstA) → (vs : List ExprA) →
    (rhsArgsA rc PRE np K vs (fsR.map FieldA.shape)
        (ctorFieldsA f ls wF pl σ (fsR.map FieldA.norm) res).1).length ≤
      minorArityA fsR
  | [], _, [] => Nat.zero_le _
  | [], _, _ :: _ => Nat.zero_le _
  | _ :: _, _, [] => Nat.zero_le _
  | .plain D u :: fsR, σ, v :: vs => by
      simp only [List.map, FieldA.shape, FieldA.norm, ctorFieldsA, rhsArgsA, recCallsA, List.nil_append,
        List.length_cons, minorArityA]
      have e1 := instantiate0A_ctorFieldsA_plain f ls wF res (fsR.map FieldA.norm) pl σ v
      rw [e1]
      exact Nat.succ_le_succ (rhsArgsA_length_le rc PRE np K f ls wF res pl fsR _ vs)
  | .drec _ :: fsR, σ, v :: vs | .frec _ _ _ _ :: fsR, σ, v :: vs | .drecD _ _ :: fsR, σ, v :: vs => by
      simp only [List.map, FieldA.shape, FieldA.norm, ctorFieldsA, rhsArgsA, recCallsA,
        List.singleton_append, List.length_cons, minorArityA]
      have e1 := instantiate0A_ctorFieldsA_drec f ls wF res (fsR.map FieldA.norm) pl σ v
      rw [e1]
      have := rhsArgsA_length_le rc PRE np K f ls wF res pl fsR σ vs
      omega

/-- a concrete ι step at a spine whose head does not step and is no struct group's (W-1 (e): there
    the head step is the struct arm's) is a declarative ι step. -/
theorem iotaRelA_of {E : ResolvedEnvA} {Γ : LCtxA} {h z e' : ExprA} (hnl : ∀ A u b, h ≠ .lam A u b)
    (hh : hStepFnA E (iotaFnA E) Γ h = none) (hsh : structHeadA E h = false)
    (hι : iotaFnA E (.app h z) = some e') : (iotaIfaceA E).rel E Γ (.app h z) e' :=
  ⟨hι, hStepFnA_app_iota E (iotaFnA E) Γ hnl hh (structPosA_of_head hsh) hι⟩

/-- a constructor view's result carries the full index list. -/
theorem CtorViewA.res_length {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm cm : CheckedMemberA}
    {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm) : v.res.length = fv.indices.length := by
  suffices h : ∀ {Γ : LCtxA} {k : Nat} {fs : List FieldA} {res : List ExprA},
      FieldsTyA E I fm.arity (fun k => liftA 0 k fv.idxTelA) Γ k fs res → res.length = fv.indices.length from
    h v.typed
  intro Γ k fs res hfs
  induction hfs with
  | nil Γ k res hres =>
      exact argsTyA_sortTelA_length hres _
        (sortTelA_liftA _ _ 0 k (sortTelA_piTelA fv.sort (.succ fv.sort) fv.indices))
  | plain _ _ _ _ _ _ _ _ ih => exact ih
  | drec _ _ _ _ _ _ _ ih => exact ih
  | frec _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | drecD _ _ _ _ _ _ _ _ ih => exact ih

/-- the recursor's prefix before the indices keeps the parameters in front. -/
theorem take_pfxA {qs : List ExprA} {np : Nat} (h : qs.length = np) {mot : ExprA} {ms is : List ExprA} :
    (qs ++ [mot] ++ ms ++ is).take np = qs := by
  rw [List.append_assoc, List.append_assoc]
  exact List.take_left' h

/-- the recursor's `j`-th minor in its prefix. -/
theorem getElem?_pfx_minorA {qs ms is : List ExprA} {mot : ExprA} {j : Nat} (hj : j < ms.length) :
    (qs ++ [mot] ++ ms ++ is)[qs.length + 1 + j]? = some (ms[j]'hj) := by
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by omega), List.singleton_append,
    show qs.length + 1 + j - qs.length = j + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

end CoreHelpers

/-! ## (6') the parameters' telescope and a constructor's mirrors -/

section MirrorPar
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE PARAMETERS' TELESCOPE AND A CONSTRUCTOR'S MIRROR TELESCOPE, TWO-SIDED, ACROSS `=ₙ` LISTS: a list
    related to itself along the parameters' telescope at `ls`, under a pair valid at `ls` and at `ls'`, is
    pointwise convertible at the parameters' domains, each domain (at `ls`) convertible with the mirror's
    at `ls'` — the level change by the parameter's base derivation across the two lists (`fundLevelsA`),
    the mirror by its base conversion at `ls'` (`tyConvA_lreqA`). `mirrorSubstA` read the other way. -/
theorem mirrorParConvA (hfc : BaseFundConvA E₀ E I n ρ₀) (hEN : EnvNormCtorTypeA E)
    (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {ls ls' : List Level} (hb : levelsBounded n ls = true) (hb' : levelsBounded n ls' = true)
    (hl : ls.length = a) (hl' : ls'.length = a) (heq : eqNList ls ls') :
    {Γp : LCtxA} → {ms ps : List (ExprA × Level)} → MirrorsConvA E₀ I a Γp ms ps →
    CtxWfA E₀ I a (telCtxA ps ++ Γp) →
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) → ∀ (κ : SubstA),
      ValidSubstA E I n ρ₀ K Δ κ κ (instCtxA ls Γp) → ValidSubstA E I n ρ₀ K Δ κ κ (instCtxA ls' Γp) →
      ∀ (B : ExprA) (w : Level) (B' : ExprA) (w' : Level) (as : List ExprA),
      ArgsRelKA E I n ρ₀ K Δ (substA κ (piTelA (instDomsA ls ps) B w).1) as as → as.length = ps.length →
      ParConvA E I n Δ (substA κ (piTelA (instDomsA ls ps) B w).1) (substA κ (piTelA (instDomsA ls' ms) B' w').1)
        as as
  | _, _, _, .nil _, _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ as _ hlen => by
      cases as with
      | cons _ _ => cases hlen
      | nil => exact .nil _ _⟩
  | _, _, _, .cons Γ M um P up ms ps hc _ tl, hwf => by
      have hwf' : CtxWfA E₀ I a (telCtxA ps ++ (.assumption P :: Γ)) :=
        telCtxA_cons_append (P, up) ps Γ ▸ hwf
      have hPΓ := ctxWfA_drop (telCtxA ps) hwf'
      cases hPΓ with
      | assumption hΓ hPty =>
          obtain ⟨K₁, hK₁⟩ := mirrorParConvA hfc hEN hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq tl hwf'
          obtain ⟨K₂, hK₂⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb hb hl hl (eqNList_refl ls) hΓ hPty
          obtain ⟨K₂', hK₂'⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb' hb' hl' hl' (eqNList_refl ls') hΓ hPty
          obtain ⟨K₂x, hK₂x⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq hΓ hPty
          obtain ⟨K₃, hK₃⟩ := tyConvA_lreqA hfc hEN hEL₀ hIL hb' hl' hc
            ⟨K₂', fun K hK Δ κ hΔ hV => LREqA_of_sortRel (hK₂' K hK Δ κ κ hΔ hV).2⟩
          refine ⟨max (max K₁ K₂) (max K₂' (max K₂x K₃)),
            fun K hK Δ hΔ κ hV hV' B w B' w' as hrel hlen => ?_⟩
          have hk1 : K₁ ≤ K := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hK
          have hk2 : K₂ ≤ K := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hK
          have hk2' : K₂' ≤ K := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hK
          have hk2x : K₂x ≤ K := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _)
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hK
          have hk3 : K₃ ≤ K := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _)
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hK
          cases as with
          | nil => cases hlen
          | cons x xs =>
              cases hrel with
              | cons _ _ _ _ _ _ _ _ h hs =>
                  rw [instantiate0A_substA_up] at hs
                  have hPP : LREqA E I n ρ₀ K Δ (substA κ (instantiateLevelsA ls P))
                      (substA κ (instantiateLevelsA ls' P)) := LREqA_of_sortRel (hK₂x K hk2x Δ κ κ hΔ hV).2
                  have he : LREqA E I n ρ₀ K Δ (substA κ (instantiateLevelsA ls P))
                      (substA κ (instantiateLevelsA ls P)) := LREqA_of_sortRel (hK₂ K hk2 Δ κ κ hΔ hV).2
                  have he' : LREqA E I n ρ₀ K Δ (substA κ (instantiateLevelsA ls' P))
                      (substA κ (instantiateLevelsA ls' P)) := LREqA_of_sortRel (hK₂' K hk2' Δ κ κ hΔ hV').2
                  have hMP := hK₃ K hk3 Δ κ hΔ hV'
                  have hV₁ : ValidSubstA E I n ρ₀ K Δ (SubstA.cons x κ) (SubstA.cons x κ)
                      (instCtxA ls (.assumption P :: Γ)) := ValidSubstA_cons hEN hV he h
                  have hV₁' : ValidSubstA E I n ρ₀ K Δ (SubstA.cons x κ) (SubstA.cons x κ)
                      (instCtxA ls' (.assumption P :: Γ)) := ValidSubstA_cons hEN hV' he' (LRRelA_transport' hEN hPP h)
                  have ih := hK₁ K hk1 Δ hΔ _ hV₁ hV₁' B w B' w' xs hs (Nat.succ.inj hlen)
                  refine .cons _ _ _ _ _ _ _ _ x x xs xs (LRRelA_conv h)
                    (LREqA_tyConv (LREqA_trans hEN hPP (LREqA_symm hEN hMP))) ?_
                  rw [instantiate0A_substA_up, instantiate0A_substA_up]
                  exact ih

end MirrorPar


/-! ## (7) the recursor at a context and a height -/

section RecAt
variable {E₀ E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
  {cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)}

/-- related parameters and indices along the family's type: the indices along the index telescope under
    the parameters' values, any body. -/
theorem RecBaseA.idxBody (_C : RecBaseA E₀ E n ρ₀ f fm fv cs) {lsX : List Level} {k : Nat} {Γ : LCtxA}
    {qs qs' is is' : List ExprA} (hqs : qs.length = fm.nparamsA) (hqs' : qs'.length = fm.nparamsA)
    (h : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsX fm.mtypeA) (qs ++ is) (qs' ++ is'))
    (hl : is.length = fv.indices.length) (B : ExprA) (w : Level) :
    ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (substA (consListA qs SubstA.id) (piTelA (instDomsA lsX fv.indices) B w).1)
      is is' := by
  have h' : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (substA SubstA.id (piTelA (instDomsA lsX fv.params ++
      instDomsA lsX fv.indices) (instantiateLevelsA lsX (.sort fv.sort)) (instLevel lsX (.succ fv.sort))).1)
      (qs ++ is) (qs' ++ is') := by
    rw [substA_id, ← instDomsA_append, ← fv.inst_tel]; exact h
  have hl₁ : qs.length = (instDomsA lsX fv.params).length := by rw [instDomsA_length, fv.nparams, hqs]
  have hl₁' : qs'.length = (instDomsA lsX fv.params).length := by rw [instDomsA_length, fv.nparams, hqs']
  obtain ⟨_, h2⟩ := argsRelKA_piTelA_append_inv _ _ _ _ SubstA.id h' hl₁ hl₁'
  exact argsRelKA_piTelA_body _ B _ w _ _ h2 (by rw [instDomsA_length]; exact hl)

/-- the parameters along their telescope and the indices under their values, joined along the family's
    type. -/
theorem RecBaseA.jointRel (_C : RecBaseA E₀ E n ρ₀ f fm fv cs) {lsX : List Level} {k : Nat} {Γ : LCtxA}
    {qs qs' is is' : List ExprA} (hqs : qs.length = fm.nparamsA) (hl : is.length = fv.indices.length)
    (hpar : ∀ (B : ExprA) (w : Level),
      ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (piTelA (instDomsA lsX fv.params) B w).1 qs qs')
    {B₀ : ExprA} {w₀ : Level}
    (hidx : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ
      (substA (consListA qs SubstA.id) (piTelA (instDomsA lsX fv.indices) B₀ w₀).1) is is') :
    ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsX fm.mtypeA) (qs ++ is) (qs' ++ is') := by
  have h := argsRelKA_piTelA_append (E := E) (I := iotaIfaceA E) (n := n) (ρ₀ := ρ₀) (k := k) (Γ := Γ)
    (instantiateLevelsA lsX (.sort fv.sort)) (.sort .zero) (instLevel lsX (.succ fv.sort)) .zero
    (instDomsA lsX fv.params) (instDomsA lsX fv.indices) SubstA.id
    (by rw [substA_id]; exact hpar _ _) (by rw [instDomsA_length, fv.nparams]; exact hqs)
    (argsRelKA_piTelA_body B₀ _ w₀ _ _ _ hidx (by rw [instDomsA_length]; exact hl))
  rw [substA_id, ← instDomsA_append, ← fv.inst_tel] at h
  exact h

/-- the recursor's type at a list of its arity, in the builder's form: only the family's level bound is
    read. -/
theorem recTelA (hEL : EnvLevelsA E) (hfm : E.members f = some fm)
    (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs) {ls : List Level} (hl : ls.length = rec.member.arity) :
    instantiateLevelsA ls rec.member.mtypeA =
      (piTelA (recDomsA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params)
          (instDomsA (ls.take fm.arity) fv.indices)
          (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
          ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))))
        (recBodyA (instDomsA (ls.take fm.arity) fv.indices).length
          ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length)
        (instLevel ls (rec.elim.motiveLevel fm.arity))).1 := by
  have h := instantiateLevelsA_groupRecTypeA cs rec.elim ls (by rw [hl, rec.harity]; omega)
    (hEL f fm hfm).1
  rw [rec.stored, h]
  simp only [instDomsA_length, List.length_map, List.length_reverse]

/-- the recursor's telescope count: the parameters, the motive, the minors, the indices, the major. -/
theorem piCountA_groupRecA (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs) :
    piCountA rec.member.mtypeA = fm.nparamsA + 1 + cs.length + fv.indices.length + 1 := by
  rw [rec.stored]
  unfold groupRecTypeA
  rw [piCountA_recTypeA]
  simp only [List.length_map, List.length_reverse, fv.nparams]

/-- at a non-zero motive universe the recursor's type has no propositional layer. -/
theorem recPiTelA (hEL : EnvLevelsA E) (hfm : E.members f = some fm)
    (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs) {ls : List Level} (hl : ls.length = rec.member.arity)
    (hwM : isZero (instLevel ls (rec.elim.motiveLevel fm.arity)) = false) :
    IsPiTelA (fm.nparamsA + 1 + cs.length + fv.indices.length + 1) (instantiateLevelsA ls rec.member.mtypeA) := by
  rw [recTelA hEL hfm rec hl]
  have h := isPiTelA_piTelA (recBodyA (instDomsA (ls.take fm.arity) fv.indices).length
    ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length) _ hwM
    (recDomsA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params) (instDomsA (ls.take fm.arity) fv.indices)
      (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
      ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))))
  have hc : (recDomsA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params)
      (instDomsA (ls.take fm.arity) fv.indices)
      (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
      ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)))).length =
      fm.nparamsA + 1 + cs.length + fv.indices.length + 1 := by
    rw [recDomsA_length]
    simp only [List.length_map, List.length_reverse, instDomsA_length, fv.nparams]
  rw [hc] at h
  exact h

/-- a family application at related parameters and indices is a recursive domain of its own fiber. -/
theorem RecBaseA.recDomRefl (_C : RecBaseA E₀ E n ρ₀ f fm fv cs) {k : Nat} {Γ : LCtxA} {lsX : List Level}
    (hbX : levelsBounded n lsX = true) {qs qs' is is' : List ExprA} (hqs : qs.length = fm.nparamsA)
    (hqs' : qs'.length = fm.nparamsA)
    (h : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA lsX fm.mtypeA) (qs ++ is) (qs' ++ is')) :
    RecDomRelA E (iotaIfaceA E) n Γ f fm (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm []) lsX qs
      (foldAppsA (.const f lsX) (qs ++ is)) (foldAppsA (.const f lsX) (qs ++ is)) := by
  obtain ⟨T', hT', _, h2⟩ := argsRelKA_append_inv (hqs.trans hqs'.symm) h
  exact ⟨lsX, lsX, is, is, T', T', rfl, rfl, eqNListB_refl hbX, eqNListB_refl hbX, hT', hT',
    argsRelKA_famRsFA_PA (argsRelKA_refl_left _C.hNCT h2) hT', ⟨.refl _ _⟩⟩

/-- at a valid family application, the relation IS the canonical fixed point. -/
theorem RecBaseA.lfpOf (C : RecBaseA E₀ E n ρ₀ f fm fv cs) {k : Nat} {Γ : LCtxA} {lsX : List Level}
    {qs is : List ExprA} (hqs : qs.length = fm.nparamsA) {a b : ExprA}
    (h : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f lsX) (qs ++ is)) a b) :
    FamLfpA E n ρ₀ k Γ f fm (foldAppsA (.const f lsX) (qs ++ is)) a b := by
  obtain ⟨R, hR, hab⟩ := h
  rw [lrTyA_fam_canon C.hE C.hEN C.hfm C.hcls hqs (C.famWhnf Γ lsX _) (C.famNotProp Γ lsX _) hR] at hab
  exact hab

/-- a group constructor's application never head-steps. -/
theorem RecBaseA.ctorWhnf (C : RecBaseA E₀ E n ρ₀ f fm fv cs) (gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv)
    (hgcE : E.members gc.ref = some gc.member) (Γ : LCtxA) (lsX : List Level) (xs : List ExprA) :
    hStepFnA E (iotaIfaceA E).fn Γ (foldAppsA (.const gc.ref lsX) xs) = none :=
  hStepFnA_constSpine_none C.hR hgcE (Or.inr gc.hnobody)
    (by rw [gc.hcls]; exact fun h => MemberClass.noConfusion h) Γ (ls := lsX) _ (by rw [foldAppsA_const_head])

/-- A RELATED FIELD LIST WALKS ITS TELESCOPE CANONICALLY: fields related along a group constructor's
    telescope at `lsX` after parameters `qs` walk it with the canonical field relation at the plain
    positions and the canonical fixed point at the recursive ones — a family application in the fiber
    of `qs`, where the relation IS the fixed point (`RecBaseA.lfpOf`). -/
theorem RecBaseA.fieldsWalk (C : RecBaseA E₀ E n ρ₀ f fm fv cs) (gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv)
    (hgcE : E.members gc.ref = some gc.member) {lsX lsD : List Level} (hlX : lsX.length = fm.arity)
    (hXD : eqNList lsX lsD) {k : Nat} {Γ : LCtxA} {qs : List ExprA} (hqs : qs.length = fm.nparamsA) :
    ∀ (fsRest fsPre : List FieldA) (pre vs vs' : List ExprA), gc.view.fields = fsPre ++ fsRest →
      pre.length = fsPre.length → vs.length = fsRest.length →
      ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ
        (ctorFieldsA f lsX (instLevel lsX fv.sort) qs (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsX)) (gc.view.res.map (instantiateLevelsA lsX))).1 vs vs' →
      ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsX) (famRecRelA fm qs lsD (FamLfpA E n ρ₀ k Γ f fm))
        (FamFunLfpA E n ρ₀ k Γ f fm gc.ref lsX qs lsD) (fm.nparamsA + pre.length) (qs ++ pre)
        (ctorFieldsA f lsX (instLevel lsX fv.sort) qs (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id))
          ((fsRest.map FieldA.norm).map (FieldA.instLevels lsX)) (gc.view.res.map (instantiateLevelsA lsX))).1
        (fsRest.map FieldA.shape) vs vs'
  | [], _, _, vs, vs', _, _, hvs, hK => by
      cases vs with
      | cons _ _ => cases hvs
      | nil =>
          cases vs' with
          | cons _ _ => cases argsRelKA_length hK
          | nil => exact .nil _ _ _
  | .plain D u :: fsRest, fsPre, pre, vs, vs', hfs, hpre, hvs, hK => by
      have hfsN : gc.view.fields.map FieldA.norm =
          fsPre.map FieldA.norm ++ FieldA.plain D u :: fsRest.map FieldA.norm := by
        rw [hfs, List.map_append]; rfl
      have hTD := applyTelA_groupCtor_prefix gc lsX hfsN (pre := pre)
        (by rw [List.length_map]; exact hpre) qs (consListA qs SubstA.id)
      have hTv := C.ctorTel gc lsX hlX hqs
      simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA, plainArgsA_norm] at hTD hK
      simp only [List.map, FieldA.instLevels, FieldA.shape, FieldA.norm, ctorFieldsA]
      cases hK with
      | nil => cases hvs
      | cons _ _ _ _ v v' vs₀ vs₀' hh hs =>
        have e := instantiate0A_ctorFieldsA_plain f lsX (instLevel lsX fv.sort)
          (gc.view.res.map (instantiateLevelsA lsX)) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsX)) qs
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) v
        have hσ₁ : consListA (plainArgsA (fsPre ++ [FieldA.plain D u]) (pre ++ [v])) (consListA qs SubstA.id) =
            SubstA.cons v (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) := by
          rw [plainArgsA_snoc_plain D u v fsPre pre hpre, consListA_snoc]
        have hfs₁ : gc.view.fields = (fsPre ++ [FieldA.plain D u]) ++ fsRest := by
          rw [hfs, List.append_assoc]; rfl
        have hpre₁ : (pre ++ [v]).length = (fsPre ++ [FieldA.plain D u]).length := by simp [hpre]
        rw [e, ← hσ₁] at hs
        have ih := RecBaseA.fieldsWalk C gc hgcE hlX hXD hqs fsRest (fsPre ++ [FieldA.plain D u]) (pre ++ [v])
          vs₀ vs₀' hfs₁ hpre₁ (Nat.succ.inj hvs) hs
        rw [List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc] at ih
        refine .plain _ _ _ _ _ _ v v' _ _ _ ?_ ?_
        · rw [famRsA_eq hgcE (by rw [applyTelA_append, hTv]; exact hTD)]; exact hh
        · rw [e, ← hσ₁]; exact ih
  | .drecD D₀ idx₀ :: fsRest, fsPre, pre, vs, vs', hfs, hpre, hvs, hK => by
      -- the δ-reached field reads as a plain recursive field in the normed telescope
      -- (R-NoDeltaRec-4d-iii): the walk's relation and its output live at the family
      -- application, where the arm is the `drec` arm verbatim.
      have hfsN : gc.view.fields.map FieldA.norm =
          fsPre.map FieldA.norm ++ FieldA.drec idx₀ :: fsRest.map FieldA.norm := by
        rw [hfs, List.map_append]; rfl
      simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hK
      simp only [List.map, FieldA.instLevels, FieldA.shape, FieldA.norm, ctorFieldsA]
      cases hK with
      | nil => cases hvs
      | cons _ _ _ _ v v' vs₀ vs₀' hh hs =>
        have e := instantiate0A_ctorFieldsA_drec f lsX (instLevel lsX fv.sort)
          (gc.view.res.map (instantiateLevelsA lsX)) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsX)) qs
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) v
        have hσ₁ : consListA (plainArgsA (fsPre ++ [FieldA.drecD D₀ idx₀]) (pre ++ [v])) (consListA qs SubstA.id) =
            consListA (plainArgsA fsPre pre) (consListA qs SubstA.id) := by
          rw [plainArgsA_snoc_drecD D₀ idx₀ v fsPre pre hpre]
        have hfs₁ : gc.view.fields = (fsPre ++ [FieldA.drecD D₀ idx₀]) ++ fsRest := by
          rw [hfs, List.append_assoc]; rfl
        have hpre₁ : (pre ++ [v]).length = (fsPre ++ [FieldA.drecD D₀ idx₀]).length := by simp [hpre]
        rw [e, ← hσ₁] at hs
        have ih := RecBaseA.fieldsWalk C gc hgcE hlX hXD hqs fsRest (fsPre ++ [FieldA.drecD D₀ idx₀])
          (pre ++ [v]) vs₀ vs₀' hfs₁ hpre₁ (Nat.succ.inj hvs) hs
        rw [List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc] at ih
        refine .directRec _ _ _ _ _ _ v v' _ _ _ ⟨carrierParamsA_famApp hqs lsX,
          by rw [carrierLevelsA_foldAppsA]; exact hXD, C.lfpOf hqs hh⟩ ?_
        rw [e, ← hσ₁]; exact ih
  | .frec B uB Bs idx :: fsRest, fsPre, pre, vs, vs', hfs, hpre, hvs, hK => by
      have hfsN : gc.view.fields.map FieldA.norm =
          fsPre.map FieldA.norm ++ FieldA.frec B uB Bs idx :: fsRest.map FieldA.norm := by
        rw [hfs, List.map_append]; rfl
      have hTD := applyTelA_groupCtor_prefix gc lsX hfsN (pre := pre)
        (by rw [List.length_map]; exact hpre) qs (consListA qs SubstA.id)
      have hTv := C.ctorTel gc lsX hlX hqs
      simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hK
      simp only [List.map, FieldA.instLevels, FieldA.shape, FieldA.norm, ctorFieldsA]
      cases hK with
      | nil => cases hvs
      | cons _ _ _ _ v v' vs₀ vs₀' hh hs =>
        have e := instantiate0A_ctorFieldsA_drec f lsX (instLevel lsX fv.sort)
          (gc.view.res.map (instantiateLevelsA lsX)) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsX)) qs
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) v
        have hσ₁ : consListA (plainArgsA (fsPre ++ [FieldA.frec B uB Bs idx]) (pre ++ [v])) (consListA qs
          SubstA.id) =
            consListA (plainArgsA fsPre pre) (consListA qs SubstA.id) := by
          rw [plainArgsA_snoc_frec B uB Bs idx v fsPre pre hpre]
        have hfs₁ : gc.view.fields = (fsPre ++ [FieldA.frec B uB Bs idx]) ++ fsRest := by
          rw [hfs, List.append_assoc]; rfl
        have hpre₁ : (pre ++ [v]).length = (fsPre ++ [FieldA.frec B uB Bs idx]).length := by simp [hpre]
        have hsp : gc.view.fields.map FieldA.shape =
            fsPre.map FieldA.shape ++ FieldShape.recursive (Bs.length + 1) :: fsRest.map FieldA.shape := by
          rw [hfs, List.map_append]; rfl
        have hkinds : ctorShapesA f fm.nparamsA (gc.member.normA.getD gc.member.mtypeA) =
            some (gc.view.fields.map FieldA.shape) := gc.normA_getD.symm ▸ gc.view.shapes C.hfresh
        have hF := famFunRelA_of_lrRel C.hE C.hI C.hEN C.hR C.hfm C.hcls C.hnobody C.hfresh C.hcensus
          C.hUT hlX hXD hgcE gc.hcls gc.view.famRef hkinds hsp hqs hTv
          (by rw [List.length_map]; exact hpre) hTD (by rw [plainArgsA_norm]; exact hh)
        rw [List.length_map, ← hpre, plainArgsA_norm] at hF
        rw [e, ← hσ₁] at hs
        have ih := RecBaseA.fieldsWalk C gc hgcE hlX hXD hqs fsRest (fsPre ++ [FieldA.frec B uB Bs idx]) (pre ++ [v])
          vs₀ vs₀' hfs₁ hpre₁ (Nat.succ.inj hvs) hs
        rw [List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc] at ih
        refine .funRec _ _ _ _ _ _ v v' Bs.length _ _ _ hF ?_
        rw [e, ← hσ₁]; exact ih
  | .drec idx :: fsRest, fsPre, pre, vs, vs', hfs, hpre, hvs, hK => by
      simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hK
      simp only [List.map, FieldA.instLevels, FieldA.shape, FieldA.norm, ctorFieldsA]
      cases hK with
      | nil => cases hvs
      | cons _ _ _ _ v v' vs₀ vs₀' hh hs =>
        have e := instantiate0A_ctorFieldsA_drec f lsX (instLevel lsX fv.sort)
          (gc.view.res.map (instantiateLevelsA lsX)) ((fsRest.map FieldA.norm).map (FieldA.instLevels lsX)) qs
          (consListA (plainArgsA fsPre pre) (consListA qs SubstA.id)) v
        have hσ₁ : consListA (plainArgsA (fsPre ++ [FieldA.drec idx]) (pre ++ [v])) (consListA qs SubstA.id) =
            consListA (plainArgsA fsPre pre) (consListA qs SubstA.id) := by
          rw [plainArgsA_snoc_drec idx v fsPre pre hpre]
        have hfs₁ : gc.view.fields = (fsPre ++ [FieldA.drec idx]) ++ fsRest := by
          rw [hfs, List.append_assoc]; rfl
        have hpre₁ : (pre ++ [v]).length = (fsPre ++ [FieldA.drec idx]).length := by simp [hpre]
        rw [e, ← hσ₁] at hs
        have ih := RecBaseA.fieldsWalk C gc hgcE hlX hXD hqs fsRest (fsPre ++ [FieldA.drec idx]) (pre ++ [v])
          vs₀ vs₀' hfs₁ hpre₁ (Nat.succ.inj hvs) hs
        rw [List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc] at ih
        refine .directRec _ _ _ _ _ _ v v' _ _ _ ⟨carrierParamsA_famApp hqs lsX,
          by rw [carrierLevelsA_foldAppsA]; exact hXD, C.lfpOf hqs hh⟩ ?_
        rw [e, ← hσ₁]; exact ih

/-- THE RECURSOR AT A CONTEXT AND A HEIGHT: a group's recursor in the concrete environment, at bounded
    `=ₙ` lists `ls`, `ls'` with a non-zero motive universe; the height above the family's and the
    motive's sorts; the recursor's type valid with its two heads typed and convertible at it; the
    family's type at the recursor's family levels valid with its head typed; parameter lists `qs`, `qs'`
    related along the parameters' telescope (any body); a motive pair and minor pairs related at their
    binders under the left parameters' values. -/
structure RecAtA (C : RecBaseA E₀ E n ρ₀ f fm fv cs) (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs)
    (ls ls' : List Level) (k : Nat) (Γ : LCtxA) (qs qs' : List ExprA) (mot mot' : ExprA) (ms ms' : List ExprA) :
    Prop where
  hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ)
  hgf : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry)
  hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length
  hpre : PrefixA (groupRecEnvA cs rec) E
  hl : ls.length = rec.member.arity
  hb : levelsBounded n ls = true
  hb' : levelsBounded n ls' = true
  heq : eqNList ls ls'
  hwM : isZero (instLevel ls (rec.elim.motiveLevel fm.arity)) = false
  hkF : ht ρ₀ (instLevel (ls.take fm.arity) fv.sort) < k
  hkM : ht ρ₀ (instLevel ls (rec.elim.motiveLevel fm.arity)) ≤ k
  hRT : ∃ R, LRTyA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls rec.member.mtypeA) R
  hr₁ : Nonempty (HasTyA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) ls)
    (instantiateLevelsA ls rec.member.mtypeA))
  hr₂ : Nonempty (HasTyA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) ls')
    (instantiateLevelsA ls rec.member.mtypeA))
  hrc : Nonempty (ConvA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) ls) (.const (f + 1 + cs.length) ls')
    (instantiateLevelsA ls rec.member.mtypeA))
  hRF : ∃ R, LRTyA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) R
  hfF : Nonempty (HasTyA E (iotaIfaceA E) n Γ (.const f (ls.take fm.arity))
    (instantiateLevelsA (ls.take fm.arity) fm.mtypeA))
  hqs : qs.length = fm.nparamsA
  hqs' : qs'.length = fm.nparamsA
  hpar : ∀ (B : ExprA) (w : Level), ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ
    (piTelA (instDomsA (ls.take fm.arity) fv.params) B w).1 qs qs'
  hms : ms.length = cs.length
  hms' : ms'.length = cs.length
  hmot : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (substA (consListA qs SubstA.id)
    (motTyA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params) (instDomsA (ls.take fm.arity) fv.indices)
      (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) mot mot'
  hmin : ∀ (i : Nat) (hi : i < ms.length) (hi' : i < ms'.length)
    (hc : i < ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length),
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ (substA (SubstA.cons mot (consListA qs SubstA.id))
      (minorTyA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
        (instLevel ls (rec.elim.motiveLevel fm.arity)) (instDomsA (ls.take fm.arity) fv.params).length
        ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)))[i]).1) ms[i] ms'[i]
  hall : ∃ (is is' : List ExprA) (x x' : ExprA), is.length = fv.indices.length ∧
    is'.length = fv.indices.length ∧
    ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls rec.member.mtypeA)
      (qs ++ ([mot] ++ ms ++ is ++ [x])) (qs' ++ ([mot'] ++ ms' ++ is' ++ [x']))

namespace RecAtA
variable {C : RecBaseA E₀ E n ρ₀ f fm fv cs} {rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs}
  {ls ls' : List Level} {k : Nat} {Γ : LCtxA} {qs qs' : List ExprA} {mot mot' : ExprA} {ms ms' : List ExprA}

theorem members (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    E.members (f + 1 + cs.length) = some rec.member :=
  (members_groupRecA R.hgf R.hlay R.hpre).1

theorem lF (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') : (ls.take fm.arity).length = fm.arity := by
  rw [List.length_take, R.hl, rec.harity]
  exact Nat.min_eq_left (Nat.le_add_right _ _)

theorem bF (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') : levelsBounded n (ls.take fm.arity) = true :=
  levelsBounded_take ls _ R.hb

theorem FF (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    eqNListB n (ls.take fm.arity) (ls'.take fm.arity) :=
  ⟨eqNList_take ls ls' _ R.heq, levelsBounded_take ls' _ R.hb'⟩

theorem lF' (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') : (ls'.take fm.arity).length = fm.arity :=
  (eqNListA_length R.FF.1).symm.trans R.lF

theorem msF (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    ms.length = ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length := by
  simp [R.hms]

theorem msF' (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    ms'.length = ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length := by
  simp [R.hms']

theorem qP (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    qs.length = (instDomsA (ls.take fm.arity) fv.params).length := by
  rw [instDomsA_length, fv.nparams]; exact R.hqs

/-- the parameters related along the family's type, with no index. -/
theorem hqq (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) (qs ++ []) (qs' ++ []) := by
  rw [List.append_nil, List.append_nil, fv.inst_split]
  exact R.hpar _ _

theorem hqd (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) (qs ++ []) (qs ++ []) :=
  argsRelKA_refl_left C.hNCT R.hqq

/-- the recursor's type at `ls`, in the builder's form. -/
theorem tel (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    instantiateLevelsA ls rec.member.mtypeA =
      (piTelA (recDomsA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params)
          (instDomsA (ls.take fm.arity) fv.indices)
          (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
          ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))))
        (recBodyA (instDomsA (ls.take fm.arity) fv.indices).length
          ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length)
        (instLevel ls (rec.elim.motiveLevel fm.arity))).1 :=
  recTelA C.hEL C.hfm rec R.hl

theorem piCount (_R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    piCountA rec.member.mtypeA = fm.nparamsA + 1 + cs.length + fv.indices.length + 1 :=
  piCountA_groupRecA rec

theorem piTel (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') :
    IsPiTelA (fm.nparamsA + 1 + cs.length + fv.indices.length + 1) (instantiateLevelsA ls rec.member.mtypeA) :=
  recPiTelA C.hEL C.hfm rec R.hl R.hwM

/-- the family's applications at related full argument lists, at the recursor's family levels. -/
theorem famApp (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {as as' : List ExprA}
    (h : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) as as')
    (hl : as.length = fm.nparamsA + fv.indices.length) :
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ (.sort (instLevel (ls.take fm.arity) fv.sort))
      (foldAppsA (.const f (ls.take fm.arity)) as) (foldAppsA (.const f (ls.take fm.arity)) as') := by
  obtain ⟨RF, hRF⟩ := R.hRF
  obtain ⟨hfF⟩ := R.hfF
  exact famAppSortRelA C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hS C.hR C.hfm
    C.hcls C.hnobody C.hfresh C.hcensus C.hcl C.hT C.hEL (iotaFnA_subst C.hE C.hEN) C.hpre₀G C.hpreG
    C.hmemG R.bF R.lF (eqNListA_refl _) R.hΓ R.hkF hRF hfF hfF (.refl _ _ _ hfF) h
    (by rw [hl, instDomsA_length, List.length_append, fv.nparams])

theorem famValid (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {as as' : List ExprA}
    (h : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) as as')
    (hl : as.length = fm.nparamsA + fv.indices.length) :
    ∃ RF, LRTyA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) as) RF :=
  ((LRRelA_sort_elim' (R.famApp h hl)).1 k (Nat.le_of_lt R.hkF)).2.1

theorem motRel (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {mA mA' : ExprA}
    (hm : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (substA (consListA qs SubstA.id) (motTyA f (ls.take fm.arity)
      (instDomsA (ls.take fm.arity) fv.params) (instDomsA (ls.take fm.arity) fv.indices)
      (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) mA mA')
    {qs₂ is is' : List ExprA} {x x' : ExprA} (hq₂ : qs₂.length = fm.nparamsA)
    (h : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) (qs ++ is) (qs₂ ++ is'))
    (hl : is.length = fv.indices.length)
    (hx : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is)) x x') :
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ (.sort (instLevel ls (rec.elim.motiveLevel fm.arity)))
      (foldAppsA mA (is ++ [x])) (foldAppsA mA' (is' ++ [x'])) :=
  motRelA R.hΓ R.qP hm (C.idxBody R.hqs hq₂ h hl (.sort .zero) .zero) (by rw [instDomsA_length]; exact hl) hx

theorem motPi (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {mA mA' : ExprA}
    (hm : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (substA (consListA qs SubstA.id) (motTyA f (ls.take fm.arity)
      (instDomsA (ls.take fm.arity) fv.params) (instDomsA (ls.take fm.arity) fv.indices)
      (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) mA mA')
    {qs₂ is is' : List ExprA} (hq₂ : qs₂.length = fm.nparamsA)
    (h : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) (qs ++ is) (qs₂ ++ is'))
    (hl : is.length = fv.indices.length) :
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ (.pi (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is))
      (instLevel (ls.take fm.arity) fv.sort) (.sort (instLevel ls (rec.elim.motiveLevel fm.arity)))
      (.succ (instLevel ls (rec.elim.motiveLevel fm.arity)))) (foldAppsA mA is) (foldAppsA mA' is') :=
  motPiA R.hΓ R.qP hm (C.idxBody R.hqs hq₂ h hl (.sort .zero) .zero) (by rw [instDomsA_length]; exact hl)

/-- the right indices have the left ones' length. -/
theorem idxLen (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {is₁ is₁' : List ExprA}
    (hidx : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA)
      (qs ++ is₁) (qs' ++ is₁'))
    (hl₁ : is₁.length = fv.indices.length) : is₁'.length = fv.indices.length := by
  have h := argsRelKA_length hidx
  simp only [List.length_append, R.hqs, R.hqs'] at h
  omega

/-- the recursor's full arguments at related parameters, indices and majors, along its type. -/
theorem fullRel (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {is₁ is₁' : List ExprA} {x x' : ExprA}
    (hl₁ : is₁.length = fv.indices.length)
    (hidx : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA)
      (qs ++ is₁) (qs' ++ is₁'))
    (hx : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) x x') :
    ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls rec.member.mtypeA)
      (qs ++ [mot] ++ ms ++ is₁ ++ [x]) (qs' ++ [mot'] ++ ms' ++ is₁' ++ [x']) := by
  have hfull := recArgsJoinPA (E := E) (I := iotaIfaceA E) (n := n) (ρ₀ := ρ₀) (K := k) (Γ := Γ) f
    (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params) (instDomsA (ls.take fm.arity) fv.indices)
    (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
    (instLevel ls (rec.elim.motiveLevel fm.arity)) _ R.qP R.msF R.msF' (by rw [instDomsA_length]; exact hl₁)
    (R.hpar _ _) R.hmot R.hmin (C.idxBody R.hqs R.hqs' hidx hl₁ (.sort .zero) .zero) hx
  rw [← R.tel] at hfull
  simpa only [List.append_assoc] using hfull

/-- THE RECURSOR'S SPINES BELOW THE MAJOR, at related parameters and indices and related majors: typed at
    the major's binder over the family application at the left parameters and indices, the codomain the
    motive at the indices and the major, typed under the binder. -/
theorem prefixA (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {is₁ is₁' : List ExprA} {x x' : ExprA}
    (hl₁ : is₁.length = fv.indices.length)
    (hidx : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA)
      (qs ++ is₁) (qs' ++ is₁'))
    (hx : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) x x') :
    ∃ B, (∀ z, instantiate0A z B = foldAppsA mot (is₁ ++ [z])) ∧
      Nonempty (HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ ms ++ is₁))
        (.pi (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) (instLevel (ls.take fm.arity) fv.sort) B
          (instLevel ls (rec.elim.motiveLevel fm.arity)))) ∧
      Nonempty (HasTyA E (iotaIfaceA E) n Γ
        (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ ms' ++ is₁'))
        (.pi (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) (instLevel (ls.take fm.arity) fv.sort) B
          (instLevel ls (rec.elim.motiveLevel fm.arity)))) ∧
      Nonempty (HasTyA E (iotaIfaceA E) n (.assumption (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) :: Γ) B
        (.sort (instLevel ls (rec.elim.motiveLevel fm.arity)))) := by
  have hl₁' := R.idxLen hidx hl₁
  have hlI : is₁.length = (instDomsA (ls.take fm.arity) fv.indices).length := by
    rw [instDomsA_length]; exact hl₁
  have hfull := R.fullRel hl₁ hidx hx
  obtain ⟨RT, hRT⟩ := R.hRT
  obtain ⟨hr₁⟩ := R.hr₁
  obtain ⟨hr₂⟩ := R.hr₂
  obtain ⟨hrc⟩ := R.hrc
  obtain ⟨Tp, hTp, hpreRel, _⟩ := argsRelKA_append_inv
    (xs := qs ++ [mot] ++ ms ++ is₁) (xs' := qs' ++ [mot'] ++ ms' ++ is₁') (ys := [x]) (ys' := [x'])
    (by simp only [List.length_append, List.length_singleton, R.hqs, R.hqs', R.hms, R.hms', hl₁, hl₁']) hfull
  obtain ⟨B, hB, hBx⟩ := applyTelA_recPrefixA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params)
    (instDomsA (ls.take fm.arity) fv.indices) (instLevel (ls.take fm.arity) fv.sort)
    (instLevel ls (rec.elim.motiveLevel fm.arity)) (instLevel ls (rec.elim.motiveLevel fm.arity)) _ qs mot ms is₁
    R.qP R.msF hlI
  rw [← R.tel, show qs ++ ([mot] ++ ms ++ is₁) = qs ++ [mot] ++ ms ++ is₁ by simp only [List.append_assoc]] at hB
  rw [hB] at hTp
  injection hTp with hTp
  subst hTp
  obtain ⟨⟨tH⟩, ⟨tH'⟩, _, ⟨RP, hRP⟩⟩ := spineConvA C.hE C.hI C.hNCT R.hΓ hpreRel _
    (by simp only [List.length_append, List.length_singleton, R.hqs, R.hms, hl₁] <;> omega) R.piTel hRT hr₁ hr₂ hrc
    _ hB
  rw [LRTyA_eq] at hRP
  obtain ⟨_, ⟨tP⟩⟩ := tyKA_hasTy hRP
  obtain ⟨_, ⟨hBty⟩⟩ := hasTyA_pi_inv tP
  exact ⟨B, hBx, ⟨tH⟩, ⟨tH'⟩, ⟨hBty⟩⟩

/-- THE STUCK CASE: majors reducing to stuck terms give two extended neutrals at the redex's type
    (`neutKA_recApp`, reflection: typed and convertible by the arguments' relation along the
    recursor's type), expanded back along the two majors' chains (`LRRelA_expand_majorChain`). At a
    group without a constructor (O1-a) the major arm is off, so the redexes themselves are the
    extended neutrals and no chain is walked. -/
theorem stuck (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {D y y' N N' : ExprA}
    (hconv : Nonempty (ConvA E (iotaIfaceA E) n Γ y y' D))
    (hyN : TyHRedStarA E (iotaIfaceA E) n Γ y N D) (hyN' : TyHRedStarA E (iotaIfaceA E) n Γ y' N' D)
    (hN : StuckTmA E (iotaIfaceA E) Γ N) (hN' : StuckTmA E (iotaIfaceA E) Γ N') :
    RecIHA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls' mot qs qs'
      (qs ++ [mot] ++ ms) (qs' ++ [mot'] ++ ms') D y y' := by
  intro is₁ is₁' hl₁ hRD hidx
  have hl₁' := R.idxLen hidx hl₁
  have hlI : is₁.length = (instDomsA (ls.take fm.arity) fv.indices).length := by
    rw [instDomsA_length]; exact hl₁
  have hlJ : (qs ++ is₁).length = fm.nparamsA + fv.indices.length := by rw [List.length_append, R.hqs, hl₁]
  -- the carrier moves within its fiber to the family application at the parameters and indices
  have hPer := C.idxPer R.bF R.lF (Nat.le_of_lt R.hkF) R.hΓ R.hqs R.hqd
  have hmv : ∀ {a b : ExprA}, FamLfpA E n ρ₀ k Γ f fm D a b →
      FamLfpA E n ρ₀ k Γ f fm (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) a b :=
    fun h => (lfpWA_recDom (ρ := []) hPer R.hqs hRD).1 h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨hDc₀⟩⟩ := id hRD
  have hDc : TyConvA E (iotaIfaceA E) n Γ D (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) := hDc₀
  obtain ⟨cy⟩ := tyHRedStarA_conv hyN
  obtain ⟨cy'⟩ := tyHRedStarA_conv hyN'
  obtain ⟨hc⟩ := hconv
  obtain ⟨ty⟩ := tyHRedStarA_hasTy_head hyN
  obtain ⟨tN⟩ := tyHRedStarA_hasTy_end hyN
  obtain ⟨tN'⟩ := tyHRedStarA_hasTy_end hyN'
  have hLyy : FamLfpA E n ρ₀ k Γ f fm D y y' :=
    LfpWA.fold famPhiWA_mono ⟨⟨hc⟩, Or.inr ⟨N, N', hyN, hyN', hN, hN'⟩⟩
  have hLNN : FamLfpA E n ρ₀ k Γ f fm D N N' :=
    LfpWA.fold famPhiWA_mono ⟨⟨.trans _ _ _ _ _ (.symm _ _ _ _ cy) (.trans _ _ _ _ _ hc cy')⟩,
      Or.inr ⟨N, N', tyHRedStarA_refl tN, tyHRedStarA_refl tN', hN, hN'⟩⟩
  obtain ⟨RF, hRF⟩ := R.famValid hidx hlJ
  have hyy : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) y y' :=
    C.lrRel R.hqs hRF (hmv hLyy)
  have hNN : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) N N' :=
    C.lrRel R.hqs hRF (hmv hLNN)
  -- the recursor's arguments at the stuck majors
  have hfull := R.fullRel hl₁ hidx hNN
  obtain ⟨RT, hRT⟩ := R.hRT
  obtain ⟨hr₁⟩ := R.hr₁
  obtain ⟨hr₂⟩ := R.hr₂
  obtain ⟨hrc⟩ := R.hrc
  have hpc := R.piCount
  have hlenP : (qs ++ [mot] ++ ms ++ is₁).length + 1 = piCountA rec.member.mtypeA := by
    rw [hpc]; simp only [List.length_append, List.length_singleton, R.hqs, R.hms, hl₁] <;> omega
  have hlenP' : (qs' ++ [mot'] ++ ms' ++ is₁').length + 1 = piCountA rec.member.mtypeA := by
    rw [hpc]; simp only [List.length_append, List.length_singleton, R.hqs', R.hms', hl₁'] <;> omega
  cases hct : recHasCtorA (f + 1 + cs.length) rec.member
  case false =>
    -- O1-a: a group without a constructor has no ι and no major arm, so the redexes themselves are
    -- extended neutrals, typed and convertible at the motive's instance at the majors
    have happY : applyTelA (qs ++ [mot] ++ ms ++ is₁ ++ [y]) (instantiateLevelsA ls rec.member.mtypeA) =
        some (foldAppsA mot (is₁ ++ [y])) := by
      rw [R.tel, show qs ++ [mot] ++ ms ++ is₁ ++ [y] = qs ++ ([mot] ++ ms ++ is₁ ++ [y]) by
        simp only [List.append_assoc]]
      exact applyTelA_recFullA _ _ _ _ _ _ _ _ qs mot y ms is₁ R.qP R.msF hlI
    obtain ⟨⟨tL⟩, ⟨tR⟩, ⟨cLR⟩, _⟩ := spineConvA C.hE C.hI C.hNCT R.hΓ (R.fullRel hl₁ hidx hyy) _
      (by simp only [List.length_append, List.length_singleton, R.hqs, R.hms, hl₁] <;> omega) R.piTel hRT hr₁ hr₂
      hrc _ happY
    have hAy : ∃ RA, LRTyA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA mot (is₁ ++ [y])) RA :=
      ((LRRelA_sort_elim' (R.motRel R.hmot R.hqs' hidx hl₁ hyy)).1 k R.hkM).2.1
    exact LRRelA_reflect C.hE C.hI hAy
      (neutKA_recApp C.hE C.hI R.members rec.hcls (ls := ls) hlenP (Or.inr hct))
      (neutKA_recApp C.hE C.hI R.members rec.hcls (ls := ls') hlenP' (Or.inr hct))
      ⟨tL⟩ ⟨tR⟩ ⟨cLR⟩
  -- the neutral pair, typed and convertible at the motive's instance at the stuck major
  have happN : applyTelA (qs ++ [mot] ++ ms ++ is₁ ++ [N]) (instantiateLevelsA ls rec.member.mtypeA) =
      some (foldAppsA mot (is₁ ++ [N])) := by
    rw [R.tel, show qs ++ [mot] ++ ms ++ is₁ ++ [N] = qs ++ ([mot] ++ ms ++ is₁ ++ [N]) by
      simp only [List.append_assoc]]
    exact applyTelA_recFullA _ _ _ _ _ _ _ _ qs mot N ms is₁ R.qP R.msF hlI
  obtain ⟨⟨tL⟩, ⟨tR⟩, ⟨cLR⟩, _⟩ := spineConvA C.hE C.hI C.hNCT R.hΓ hfull _
    (by simp only [List.length_append, List.length_singleton, R.hqs, R.hms, hl₁] <;> omega) R.piTel hRT hr₁ hr₂ hrc
    _ happN
  -- the prefix: the major's binder, typed
  obtain ⟨B, hBx, ⟨tH⟩, ⟨tH'⟩, ⟨hBty⟩⟩ := R.prefixA hl₁ hidx hNN
  -- the motive's instances
  obtain ⟨⟨hg⟩, _⟩ := LRRelA_hasTy (R.motPi R.hmot R.hqs' hidx hl₁)
  have tyD : HasTyA E (iotaIfaceA E) n Γ y (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) :=
    hasTyA_of_tyConvA ty hDc
  obtain ⟨_, _, ⟨cvN⟩⟩ := appSortConvA hg (hasTyA_of_tyConvA tN hDc) tyD
    (convA_of_tyConvA (.symm _ _ _ _ cy) hDc)
  have cvN' : TyConvA E (iotaIfaceA E) n Γ (foldAppsA mot (is₁ ++ [N])) (foldAppsA mot (is₁ ++ [y])) := by
    rw [foldAppsA_snoc, foldAppsA_snoc]; exact cvN
  have hAy : ∃ RA, LRTyA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA mot (is₁ ++ [y])) RA :=
    ((LRRelA_sort_elim' (R.motRel R.hmot R.hqs' hidx hl₁ hyy)).1 k R.hkM).2.1
  -- reflection at the redex's type
  have hrefl := LRRelA_reflect C.hE C.hI hAy
    (neutKA_recApp C.hE C.hI R.members rec.hcls (ls := ls) hlenP (Or.inl ⟨hN, unitGroupA_groupRecA_of_type rec C.hUT, structGroupA_groupRecA_of_type rec C.hUT⟩))
    (neutKA_recApp C.hE C.hI R.members rec.hcls (ls := ls') hlenP' (Or.inl ⟨hN', unitGroupA_groupRecA_of_type rec C.hUT, structGroupA_groupRecA_of_type rec C.hUT⟩))
    ⟨hasTyA_of_tyConvA tL cvN'⟩ ⟨hasTyA_of_tyConvA tR cvN'⟩ ⟨convA_of_tyConvA cLR cvN'⟩
  rw [foldAppsA_snoc (.const _ ls) (qs ++ [mot] ++ ms ++ is₁) N,
    foldAppsA_snoc (.const _ ls') (qs' ++ [mot'] ++ ms' ++ is₁') N'] at hrefl
  rw [foldAppsA_snoc (.const _ ls) (qs ++ [mot] ++ ms ++ is₁) y,
    foldAppsA_snoc (.const _ ls') (qs' ++ [mot'] ++ ms' ++ is₁') y']
  -- the two majors' chains
  obtain ⟨tchain⟩ := hyN
  obtain ⟨tchain'⟩ := hyN'
  have hL := LRRelA_expand_majorChain C.hE C.hI
    (recAtMajorA_recSpine R.members rec.hcls hct ls _ hlenP)
    (unitMinorA_foldAppsA_none R.members (unitGroupA_groupRecA_of_type rec C.hUT) ls _)
    (by rw [structHeadA_foldAppsA R.members]; exact structGroupA_groupRecA_of_type rec C.hUT)
    (hStepFnA_recSpine_below Γ R.members rec.hcls ls _ (by omega))
    tH hBty hDc (fun z z' hs => iotaFnA_app_none_of_step (tyHRedA_hStep hs)) tchain
    (fun w hw => by
      rw [hBx w, foldAppsA_snoc, foldAppsA_snoc]
      exact motInstCondA hg hDc tyD (.refl _ _ _ ty) hw) hrefl
  exact LRRelA_expand_majorChain_right C.hE C.hI
    (recAtMajorA_recSpine R.members rec.hcls hct ls' _ hlenP')
    (unitMinorA_foldAppsA_none R.members (unitGroupA_groupRecA_of_type rec C.hUT) ls' _)
    (by rw [structHeadA_foldAppsA R.members]; exact structGroupA_groupRecA_of_type rec C.hUT)
    (hStepFnA_recSpine_below Γ R.members rec.hcls ls' _ (by omega))
    tH' hBty hDc (fun z z' hs => iotaFnA_app_none_of_step (tyHRedA_hStep hs)) tchain'
    (fun w hw => by
      rw [hBx w, foldAppsA_snoc, foldAppsA_snoc]
      exact motInstCondA hg hDc tyD hc hw) hL

/-- THE INSTANCE AT A WELL-FORMED EXTENSION (R-NoFunRec-1 step 1 (1c-ε1)): the instance weakened along a
    world, with the parameters, the motive and the minors weakened there. The typing data weaken (the
    types are closed); the related pairs are read off the whole related list along the recursor's type,
    weakened (`argsRelKA_wk`) and split again (`recArgsSplitPA`), so no substitution form is commuted. -/
theorem wk (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {ρ : WkSpecA}
    (hρ : WkOkA E (iotaIfaceA E) n ρ Γ) :
    RecAtA C rec ls ls' k (wkCtxA ρ Γ) (qs.map (wkExprA ρ)) (qs'.map (wkExprA ρ)) (wkExprA ρ mot)
      (wkExprA ρ mot') (ms.map (wkExprA ρ)) (ms'.map (wkExprA ρ)) := by
  have hTcl : ∀ j, liftA j 1 (instantiateLevelsA ls rec.member.mtypeA) =
      instantiateLevelsA ls rec.member.mtypeA := liftA_instantiateLevelsA_closed rec.hclT ls
  have hFcl : ∀ j, liftA j 1 (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) =
      instantiateLevelsA (ls.take fm.arity) fm.mtypeA := liftA_instantiateLevelsA_closed C.hcl _
  obtain ⟨is, is', x, x', hi, hi', hall⟩ := R.hall
  have hw0 := argsRelKA_wk C.hE C.hI C.hEN ρ hρ hall
  rw [wkExprA_closed hTcl] at hw0
  simp only [List.map_append, List.map_cons, List.map_nil] at hw0
  have hw := hw0
  rw [recTelA C.hEL C.hfm rec R.hl] at hw
  have hlens : (qs.map (wkExprA ρ) ++ ([wkExprA ρ mot] ++ ms.map (wkExprA ρ) ++ is.map (wkExprA ρ) ++
      [wkExprA ρ x])).length = (instDomsA (ls.take fm.arity) fv.params).length +
      (1 + ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length +
        (instDomsA (ls.take fm.arity) fv.indices).length + 1) := by
    simp only [List.length_append, List.length_singleton, List.length_map, List.length_reverse,
      instDomsA_length, fv.nparams, R.hqs, R.hms, hi]
  obtain ⟨qs₂, qs₂', mot₂, mot₂', x₂, x₂', ms₂, ms₂', is₂, is₂', he, he', hq, hq', hm, hm', hi₂, hi₂', hpar,
      hmot, hmin, -, -, -⟩ := recArgsSplitPA _ _ _ _ _ _ _ _ hw hlens
  have hcl : ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length =
      cs.length := by simp
  have hil₂ : is₂.length = is.length := by rw [hi₂, instDomsA_length, hi]
  have hil₂' : is₂'.length = is'.length := by rw [hi₂', instDomsA_length, hi']
  obtain ⟨e1, e2⟩ := List.append_inj he (by rw [List.length_map, R.qP, hq])
  obtain ⟨e1', e2'⟩ := List.append_inj he' (by rw [List.length_map, R.hqs', hq', instDomsA_length, fv.nparams])
  obtain ⟨e3, e4⟩ := List.append_inj' e2 rfl
  obtain ⟨e3', e4'⟩ := List.append_inj' e2' rfl
  obtain ⟨e5, e6⟩ := List.append_inj' e3 (by rw [List.length_map, hil₂])
  obtain ⟨e5', e6'⟩ := List.append_inj' e3' (by rw [List.length_map, hil₂'])
  obtain ⟨e7, e8⟩ := List.append_inj' e5 (by rw [List.length_map, R.hms, hm, hcl])
  obtain ⟨e7', e8'⟩ := List.append_inj' e5' (by rw [List.length_map, R.hms', hm', hcl])
  have em : mot₂ = wkExprA ρ mot := (List.singleton_inj.mp e7).symm
  have em' : mot₂' = wkExprA ρ mot' := (List.singleton_inj.mp e7').symm
  subst e1 e1' e8 e8' em em'
  refine ⟨hρ.2, R.hgf, R.hlay, R.hpre, R.hl, R.hb, R.hb', R.heq, R.hwM, R.hkF, R.hkM, ?_, ?_, ?_, ?_, ?_, ?_,
    (by rw [List.length_map]; exact R.hqs), (by rw [List.length_map]; exact R.hqs'), hpar,
    (by rw [List.length_map]; exact R.hms), (by rw [List.length_map]; exact R.hms'), hmot, hmin,
    ⟨is.map (wkExprA ρ), is'.map (wkExprA ρ), wkExprA ρ x, wkExprA ρ x', (by rw [List.length_map]; exact hi),
      (by rw [List.length_map]; exact hi'), hw0⟩⟩
  · obtain ⟨RT, hRT⟩ := R.hRT
    obtain ⟨RT', hRT', -⟩ := LRTyA_wk C.hE C.hEN C.hI hRT ρ hρ
    rw [wkExprA_closed hTcl] at hRT'
    exact ⟨RT', hRT'⟩
  · have h := hasTyA_wk_ne C.hE C.hI ρ hρ.1 R.hr₁
    rw [wkExprA_const, wkExprA_closed hTcl] at h
    exact h
  · have h := hasTyA_wk_ne C.hE C.hI ρ hρ.1 R.hr₂
    rw [wkExprA_const, wkExprA_closed hTcl] at h
    exact h
  · have h := convA_wk_ne C.hE C.hI ρ hρ.1 R.hrc
    rw [wkExprA_const, wkExprA_const, wkExprA_closed hTcl] at h
    exact h
  · obtain ⟨RF, hRF⟩ := R.hRF
    obtain ⟨RF', hRF', -⟩ := LRTyA_wk C.hE C.hEN C.hI hRF ρ hρ
    rw [wkExprA_closed hFcl] at hRF'
    exact ⟨RF', hRF'⟩
  · have h := hasTyA_wk_ne C.hE C.hI ρ hρ.1 R.hfF
    rw [wkExprA_const, wkExprA_closed hFcl] at h
    exact h

/-- THE CONSTRUCTOR CASE: majors reducing to one group constructor at `=ₙ` levels, each form with its own
    parameters (convertible with the carrier's, P2). ι fires on each side (`iotaFnA_groupRecA`) at the
    recursor's parameters: the `j`-th minor applied to the fields and the recursive calls. The minor walk
    relates the two reducts' arguments along the minor's telescope (the induction hypothesis at the
    recursive fields), so the reducts are related at the minor's conclusion: the motive at the result
    indices and the constructor at the recursor's family levels and parameters. The result indices are
    related to the redex's (the coherence, `resDomA`, composed by `IdxPerA`). The constructor form at the
    recursor's levels and parameters is related to the major by the canonical fixed point: the major's
    form converts with it (P2 carried onto the constructor's mirror telescope at the recursor's levels,
    `mirrorParConvA`, then `convA_spine` with the constructor's clause at the heads), and the pair is a
    constructor step of the operator, its fields walked from the minor walk's relation at the recursor's
    levels (`RecBaseA.fieldsWalk`). So the conclusion equals the redex's type; the ι steps and the
    majors' chains expand back. -/
theorem ctor (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {D y y' : ExprA}
    (hconv : Nonempty (ConvA E (iotaIfaceA E) n Γ y y' D)) (hLyy : FamLfpA E n ρ₀ k Γ f fm D y y')
    {c : Nat} {cm : CheckedMemberA} {lsC lsC' : List Level} {kinds : List FieldShape}
    {ps₁ ps₂ fs fs' : List ExprA} {T₁ T₁' : ExprA}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hlC : eqNListBB n (carrierLevelsA D) lsC) (hlsC : eqNListB n lsC lsC')
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hT : applyTelA (carrierParamsA fm D) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T₁)
    (hT' : applyTelA (carrierParamsA fm D) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T₁')
    (hcoh : FamCohA f fm (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm []) D fs T₁ fs' T₁')
    (hp₁ : ps₁.length = fm.nparamsA) (hp₂ : ps₂.length = fm.nparamsA)
    (ha : TyHRedStarA E (iotaIfaceA E) n Γ y (foldAppsA (.const c lsC) (ps₁ ++ fs)) D)
    (hb : TyHRedStarA E (iotaIfaceA E) n Γ y' (foldAppsA (.const c lsC') (ps₂ ++ fs')) D)
    (hna : hStepFnA E (iotaIfaceA E).fn Γ (foldAppsA (.const c lsC) (ps₁ ++ fs)) = none)
    (hargs : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] c lsC)
      (famRecRelA fm (carrierParamsA fm D) (carrierLevelsA D)
        (fun D y y' => RecIHA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls'
          mot qs qs' (qs ++ [mot] ++ ms) (qs' ++ [mot'] ++ ms') D y y' ∧ FamLfpA E n ρ₀ k Γ f fm D y y'))
      (FamFunIHA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls' mot qs qs'
        (qs ++ [mot] ++ ms) (qs' ++ [mot'] ++ ms') c lsC (carrierParamsA fm D) (carrierLevelsA D))
      fm.nparamsA (carrierParamsA fm D) T₁ kinds fs fs')
    (hP₁ : ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA lsC fm.mtypeA) (carrierParamsA fm D) ps₁) :
    RecIHA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls' mot qs qs'
      (qs ++ [mot] ++ ms) (qs' ++ [mot'] ++ ms') D y y' := by
  intro is₁ is₁' hl₁ hRD hidx
  have hl₁' := R.idxLen hidx hl₁
  have hlJ : (qs ++ is₁).length = fm.nparamsA + fv.indices.length := by rw [List.length_append, R.hqs, hl₁]
  have hPer := C.idxPer R.bF R.lF (Nat.le_of_lt R.hkF) R.hΓ R.hqs R.hqd
  obtain ⟨hc⟩ := hconv
  obtain ⟨hΓ'⟩ := R.hΓ
  -- the major at the family application at the parameters and indices; the prefixes; the motive
  have hmv : ∀ {a b : ExprA}, FamLfpA E n ρ₀ k Γ f fm D a b →
      FamLfpA E n ρ₀ k Γ f fm (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) a b :=
    fun h => (lfpWA_recDom (ρ := []) hPer R.hqs hRD).1 h
  obtain ⟨RF, hRF⟩ := R.famValid hidx hlJ
  have hyy : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) y y' :=
    C.lrRel R.hqs hRF (hmv hLyy)
  obtain ⟨B, hBx, ⟨tH⟩, ⟨tH'⟩, ⟨hBty⟩⟩ := R.prefixA hl₁ hidx hyy
  obtain ⟨⟨hg⟩, _⟩ := LRRelA_hasTy (R.motPi R.hmot R.hqs' hidx hl₁)
  -- the carrier: a family application in the fiber of the recursor's parameters
  obtain ⟨lsA, lsA', isA, isA', TF, TF', hA, hA', hl₀, _, hTF, _, hwI, ⟨hDc₀⟩⟩ := id hRD
  have hDc : TyConvA E (iotaIfaceA E) n Γ D (foldAppsA (.const f (ls.take fm.arity)) (qs ++ is₁)) := hDc₀
  obtain ⟨_, _, exA'⟩ := foldAppsA_const_inj hA'
  have exI := List.append_cancel_left exA'
  rw [← exI] at hwI
  subst hA
  have htk : (qs ++ isA).take fm.nparamsA = qs := List.take_left' R.hqs
  have hdr : (qs ++ isA).drop fm.nparamsA = isA := List.drop_left' R.hqs
  have hcp : carrierParamsA fm (foldAppsA (.const f lsA) (qs ++ isA)) = qs := by
    rw [carrierParamsA_foldAppsA, htk]
  rw [hcp, carrierLevelsA_foldAppsA] at hargs
  rw [hcp] at hT hT' hP₁
  rw [carrierLevelsA_foldAppsA] at hlC
  -- the constructor in the group, at candidate index `j`
  obtain ⟨gc, hgc, hgr, hgm⟩ := C.hcensus c cm hcm hk hfam
  subst hgr hgm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (List.mem_reverse.mpr hgc)
  obtain ⟨_, hjK⟩ := ref_of_layoutA R.hlay hj
  have hlA : lsA.length = fm.arity := (eqNListA_length hl₀.1).symm.trans R.lF
  have hlCl : lsC.length = fm.arity := (eqNListA_length hlC.1.1).symm.trans hlA
  have hlCl' : lsC'.length = fm.arity := (eqNListA_length hlsC.1).symm.trans hlCl
  have hbC : levelsBounded n lsC = true := hlC.1.2
  rw [C.ctorTel gc lsC hlCl R.hqs] at hT
  injection hT with hT
  subst hT
  rw [C.ctorTel gc lsC' hlCl' R.hqs] at hT'
  injection hT' with hT'
  subst hT'
  rw [gc.normA_getD, gc.view.shapes C.hfresh] at hkinds
  injection hkinds with hkinds
  subst hkinds
  have hfsL : fs.length = gc.view.fields.length := by rw [(argsRelA_length hargs).1, List.length_map]
  have hfsL' : fs'.length = gc.view.fields.length := by rw [(argsRelA_length hargs).2, List.length_map]
  -- the minor at `j` and its type
  have hjm : j < ms.length := R.hms ▸ hjK
  have hjm' : j < ms'.length := R.hms' ▸ hjK
  have hjc : j < ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length := by
    simp only [List.length_map, List.length_reverse]; exact hjK
  obtain ⟨_, hjg⟩ := List.getElem?_eq_some_iff.mp hj
  have hMT : ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)))[j]'hjc =
      (gc.ref, gc.view.fields.map (FieldA.instLevels (ls.take fm.arity)),
        gc.view.res.map (instantiateLevelsA (ls.take fm.arity))) := by
    simp only [List.getElem_map, hjg]; rfl
  have hσ : (fun i => substA (SubstA.cons mot (consListA qs SubstA.id)) (SubstA.id.shift1 i)) =
      consListA qs SubstA.id := by
    funext i
    show substA (SubstA.cons mot (consListA qs SubstA.id)) (liftA 0 1 (SubstA.id i)) = consListA qs SubstA.id i
    rw [substA_cons_liftA]
    rfl
  have hpl : ((paramLocalsA (instDomsA (ls.take fm.arity) fv.params).length).map (liftA 0 1)).map
      (substA (SubstA.cons mot (consListA qs SubstA.id))) = qs := by
    rw [map_substA_cons_liftA, ← R.qP, paramLocalsA_consListA]
  have hmj : LRRelA E (iotaIfaceA E) n ρ₀ k Γ
      (minorFieldsA f gc.ref (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
        (instLevel ls (rec.elim.motiveLevel fm.arity)) qs mot [] (consListA qs SubstA.id)
        (gc.view.fields.map (FieldA.instLevels (ls.take fm.arity)))
        (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).1 (ms[j]'hjm) (ms'[j]'hjm') := by
    have h := R.hmin j hjm hjm' hjc
    rw [hMT, minorTyA, substA_minorFieldsA, hpl, hσ] at h
    exact h
  -- the minor walk, and the two reducts related at the minor's conclusion
  have hFC : eqNListB n (ls.take fm.arity) lsC := eqNListB_trans hl₀ hlC.1
  have hpfx : (qs ++ [mot] ++ ms).length = fm.nparamsA + 1 + cs.length := by
    simp only [List.length_append, List.length_singleton, R.hqs, R.hms]
  have hpfx' : (qs' ++ [mot'] ++ ms').length = fm.nparamsA + 1 + cs.length := by
    simp only [List.length_append, List.length_singleton, R.hqs', R.hms']
  obtain ⟨RM, hRM, _⟩ := id hmj
  have hargs₀ : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k Γ [] gc.ref lsC)
      (famRecRelA fm qs lsA (fun D y y' =>
        RecIHA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls' mot qs qs'
          (qs ++ [mot] ++ ms) (qs' ++ [mot'] ++ ms') D y y' ∧ FamLfpA E n ρ₀ k Γ f fm D y y'))
      (FamFunIHA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls' mot qs qs'
        (qs ++ [mot] ++ ms) (qs' ++ [mot'] ++ ms') gc.ref lsC qs lsA)
      (fm.nparamsA + ([] : List ExprA).length) (qs ++ [])
      (ctorFieldsA f lsC (instLevel lsC fv.sort) qs (consListA (plainArgsA [] []) (consListA qs SubstA.id))
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsC))
        (gc.view.res.map (instantiateLevelsA lsC))).1
      (gc.view.fields.map FieldA.shape) fs fs' := by
    rw [List.length_nil, Nat.add_zero, List.append_nil]; exact hargs
  obtain ⟨hW1, hW2⟩ := minorWalkA C R.hΓ R.bF R.lF R.FF (Nat.le_of_lt R.hkF) R.hqs R.hqs' R.hqq hcm hFC lsA
    (r := f + 1 + cs.length) (ls := ls) (ls' := ls') (mot := mot) (pfx := qs ++ [mot] ++ ms)
    (pfx' := qs' ++ [mot'] ++ ms') (is₁ := is₁) (is₁' := is₁') hpfx hpfx' R.hwM gc.view.drec_length_norm
    gc.view.fields [] [] [] fs fs' (List.nil_append _).symm rfl (.nil _ _ _) hargs₀ (.nil _ _ _) (.nil _)
    ⟨RM, hRM⟩
  have happM := applyTelA_minor_rhsArgsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ ms ++ is₁) fm.nparamsA
    cs.length f gc.ref (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
    (instLevel ls (rec.elim.motiveLevel fm.arity)) (gc.view.res.map (instantiateLevelsA (ls.take fm.arity))) mot qs
    (gc.view.fields.map (FieldA.instLevels (ls.take fm.arity))) [] (consListA qs SubstA.id) fs
    (by rw [List.length_map]; exact hfsL)
  have hlenM := rhsArgsA_length_le (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ ms ++ is₁) fm.nparamsA
    cs.length f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
    (gc.view.res.map (instantiateLevelsA (ls.take fm.arity))) qs
    (gc.view.fields.map (FieldA.instLevels (ls.take fm.arity))) (consListA qs SubstA.id) fs
  rw [map_shape_instLevels] at happM hlenM
  rw [map_instLevels_norm] at happM hlenM
  rw [plainArgsA_instLevels] at happM
  have hred := LRRelA_apps R.hΓ hW1 _ hlenM (isPiTelA_minorFieldsA f gc.ref (ls.take fm.arity)
    (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity))
    (gc.view.res.map (instantiateLevelsA (ls.take fm.arity))) R.hwM _ qs mot [] (consListA qs SubstA.id)) hmj _
    happM
  simp only [List.nil_append] at hred
  -- the results of the constructor at the form's levels and at the recursor's, after the fields
  have hfsLN : fs.length = (gc.view.fields.map FieldA.norm).length := by
    rw [List.length_map]; exact hfsL
  have hRC := applyTelA_groupCtor_prefix gc lsC (fsAll := gc.view.fields.map FieldA.norm)
    (fsPre := gc.view.fields.map FieldA.norm) (fsRest := [])
    (List.append_nil _).symm hfsLN qs (consListA qs SubstA.id)
  have hRF' := applyTelA_groupCtor_prefix gc (ls.take fm.arity)
    (fsAll := gc.view.fields.map FieldA.norm) (fsPre := gc.view.fields.map FieldA.norm) (fsRest := [])
    (List.append_nil _).symm hfsLN qs (consListA qs SubstA.id)
  simp only [List.map_nil, ctorFieldsA, plainArgsA_norm] at hRC hRF'
  generalize hresC : (gc.view.res.map (instantiateLevelsA lsC)).map
    (substA (consListA (plainArgsA gc.view.fields fs) (consListA qs SubstA.id))) = resC at hRC
  generalize hresF : (gc.view.res.map (instantiateLevelsA (ls.take fm.arity))).map
    (substA (consListA (plainArgsA gc.view.fields fs) (consListA qs SubstA.id))) = resF at hRF' hred
  have hresL : resF.length = fv.indices.length := by
    rw [← hresF, List.length_map, List.length_map]; exact gc.view.res_length
  -- the carrier's indices and the form's result indices (the coherence)
  obtain ⟨lsA₀, lsR, _, xsA, isR, _, TF₀, R₁, _, hspA, hTF₀, hR₁, hspR, _, hwR, _, _, _, _⟩ := hcoh
  rw [foldAppsA_const_head] at hspA
  injection hspA with e1 e2
  injection e1 with _ e1
  subst e1 e2
  rw [htk, hTF] at hTF₀
  injection hTF₀ with eTF
  subst eTF
  rw [hRC] at hR₁
  injection hR₁ with hR₁
  subst hR₁
  rw [htk, foldAppsA_const_head] at hspR
  injection hspR with e3 e4
  injection e3 with _ e3
  have e5 := List.append_cancel_left e4
  subst e3 e5
  rw [htk, hdr] at hwR
  -- the results at the form's levels and at the recursor's, related (`resDomA`)
  obtain ⟨lsB, lsB', isB, isB', TFB, TFB', hB1, hB2, _, _, hTFB, hTFB', hwB, _⟩ :=
    resDomA (fv := fv) (cs := cs) C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL C.hS C.hfm
      C.hcls C.hfresh C.hcensus C.hcl C.hT C.hUT R.bF R.lF (Nat.le_of_lt R.hkF) (k := k) R.hΓ (ps := qs)
      (ps' := qs) (is := []) (is' := []) R.hqs R.hqs R.hqd (ρ := []) (Or.inl rfl) hcm gc.hcls
      gc.view.famRef (gc.normA_getD.symm ▸ gc.view.shapes C.hfresh) (eqNListA_refl _) hFC
      (eqNListB_symm hFC R.bF)
      (by rw [map_wkExprA_nil]; exact C.ctorTel gc lsC hlCl R.hqs)
      (by rw [map_wkExprA_nil]; exact C.ctorTel gc (ls.take fm.arity) R.lF R.hqs)
      (by rw [map_wkExprA_nil]; exact argsRelA_diag C.hNCT (famRsA_refl_left C.hNCT) hargs) hRC hRF'
  simp only [map_wkExprA_nil] at hB1 hB2 hTFB hTFB' hwB
  obtain ⟨_, eB1, eB1'⟩ := foldAppsA_const_inj hB1
  obtain ⟨_, eB2, eB2'⟩ := foldAppsA_const_inj hB2
  have eB1c := List.append_cancel_left eB1'
  have eB2c := List.append_cancel_left eB2'
  subst eB1 eB2 eB1c eB2c
  -- composed by `IdxPerA`: the carrier's to the recursor-side result, that to the redex's indices
  have a1 := hPer.comp hl₀ hlC.1 hTF hTFB hwR hwB
  have a2 := hPer.flip hl₀ (eqNListB_symm hl₀ R.bF) hTF hTFB' a1
  have a3 := hPer.comp (eqNListB_refl R.bF) hl₀ hTFB' hTF a2 hwI
  have hqF : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) qs qs := by
    simpa only [List.append_nil] using R.hqd
  have hidxR : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA)
      (qs ++ resF) (qs ++ is₁) := argsRelKA_append hqF hTFB' (argsRelPA_famRsFA_KA a3 hTFB')
  have hlJR : (qs ++ resF).length = fm.nparamsA + fv.indices.length := by
    rw [List.length_append, R.hqs, hresL]
  obtain ⟨hEqF, _, _⟩ := (LRRelA_sort_elim' (R.famApp hidxR hlJR)).1 k (Nat.le_of_lt R.hkF)
  -- THE CONSTRUCTOR FORM AT THE RECURSOR'S LEVELS AND PARAMETERS CONVERTS WITH THE MAJOR'S: P2 carried
  -- onto the constructor's mirror telescope at the recursor's levels, the fields with themselves, the
  -- two heads by the constructor's clause; `convA_spine` at the result
  obtain ⟨hwf⟩ := fv.paramsCtxWf C.hT
  have hwf₀ : CtxWfA E₀ (iotaIfaceA E) fm.arity (telCtxA fv.params ++ []) := (List.append_nil _).symm ▸ hwf
  obtain ⟨Km, hKm⟩ := mirrorParConvA C.hfc C.hNCT C.hE₀ C.hI C.hR₀ C.hEL₀ C.hIL hbC R.bF hlCl R.lF
    (eqNListA_symm hFC.1) gc.view.mirrorsConv hwf₀
  obtain ⟨Kp, hKp⟩ := paramSubstA C.hfund C.hfc C.hNCT C.hEN C.hE₀ C.hE C.hI C.hR₀ C.hEL₀ C.hIL fv C.hcl
    C.hT R.bF hbC R.lF
    hlCl hFC.1
  have hVC := hKp (max Km (max Kp k)) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) qs qs [] []
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) R.hΓ R.hqs R.hqs R.hqd [] (Or.inl rfl)
  simp only [map_wkExprA_nil] at hVC
  rw [← telCtxA_instDomsA] at hVC
  have hrelC := argsRelKA_of_validSubst C.hNCT (instDomsA lsC fv.params) (instantiateLevelsA lsC fv.idxTelA)
    (instLevel lsC (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2) qs qs
    (by rw [instDomsA_length, fv.nparams]; exact R.hqs) (by rw [instDomsA_length, fv.nparams]; exact R.hqs) hVC
  have hPC := hKm (max Km (max Kp k)) (Nat.le_max_left _ _) Γ R.hΓ SubstA.id (ValidSubstA_nil _ _ _)
    (ValidSubstA_nil _ _ _) (instantiateLevelsA lsC fv.idxTelA)
    (instLevel lsC (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2)
    (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
      (paramLocalsA (instDomsA (ls.take fm.arity) gc.view.mirrors).length) SubstA.id
      ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
      (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).1
    (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
      (paramLocalsA (instDomsA (ls.take fm.arity) gc.view.mirrors).length) SubstA.id
      ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
      (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).2
    qs (by rw [substA_id]; exact hrelC) (by rw [fv.nparams]; exact R.hqs)
  rw [substA_id, substA_id, ← fv.inst_split] at hPC
  have hcT : (piTelA (instDomsA (ls.take fm.arity) gc.view.mirrors)
      (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
        (paramLocalsA (instDomsA (ls.take fm.arity) gc.view.mirrors).length) SubstA.id
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
        (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).1
      (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
        (paramLocalsA (instDomsA (ls.take fm.arity) gc.view.mirrors).length) SubstA.id
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
        (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).2).1 =
      instantiateLevelsA (ls.take fm.arity) (gc.member.normA.getD gc.member.mtypeA) := by
    rw [gc.inst_tel _ R.lF]; rfl
  rw [hcT] at hPC
  have hPF : ConvArgsA E (iotaIfaceA E) n Γ
      (instantiateLevelsA (ls.take fm.arity) (gc.member.normA.getD gc.member.mtypeA)) qs ps₁ :=
    convArgsA_rebase hPC hP₁
  have hfF : ConvArgsA E (iotaIfaceA E) n Γ
      (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort) qs (consListA qs SubstA.id)
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
        (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).1 fs fs := by
    have h := convArgsA_refl_left (convArgsA_of_argsRelKA hW2)
    simpa only [List.nil_append] using h
  obtain ⟨k₀, hk₀⟩ := C.hCtor gc hgc (ls.take fm.arity) lsC (R.lF.trans gc.harity.symm) R.bF hFC.2 hFC.1
  have hcK := hk₀ (max k k₀) (Nat.le_max_right _ _) Γ R.hΓ
  -- the stored↔δ-normal bridge at `Γ` (R-NoDeltaRec-4d-iii): `normConv` in the family's extension,
  -- instantiated at the form's levels, lifted along the prefix and closed-weakened — the same
  -- `hTCG` block as `ctorSemClauseA`.
  obtain ⟨hTn⟩ : Nonempty (TyConvA E (iotaIfaceA E) n Γ
      (instantiateLevelsA (ls.take fm.arity) gc.member.mtypeA)
      (instantiateLevelsA (ls.take fm.arity) (gc.member.normA.getD gc.member.mtypeA))) := by
    obtain ⟨tc⟩ := gc.view.normConv
    have tc' : TyConvA (extendEnvA E₀ f fm) (iotaIfaceA E) fm.arity [] gc.member.mtypeA
        (gc.member.normA.getD gc.member.mtypeA) := by
      rw [gc.normA_getD, gc.view.stored]; exact tc
    have hpreE : PrefixA (extendEnvA E₀ f fm) E :=
      prefixA_trans (prefixA_extend_groupEnvA C.hgf) C.hpreG
    have hEL₁ : EnvLevelsA (extendEnvA E₀ f fm) := fun r m h => C.hEL r m (hpreE r m h)
    exact ⟨tyConvA_closedWeaken C.hE C.hI
      (liftA_instantiateLevelsA_closed gc.hclT (ls.take fm.arity))
      (liftA_instantiateLevelsA_closed gc.normA_getD_closed (ls.take fm.arity)) Γ
      (tyConvA_env hpreE (tyConvA_instLevels hEL₁ C.hIL R.bF R.lF tc'))⟩
  have happF : applyTelA (qs ++ fs)
      (instantiateLevelsA (ls.take fm.arity) (gc.member.normA.getD gc.member.mtypeA)) =
      some (foldAppsA (.const f (ls.take fm.arity)) (qs ++ resF)) := by
    rw [applyTelA_append, C.ctorTel gc (ls.take fm.arity) R.lF R.hqs]; exact hRF'
  obtain ⟨hcvF⟩ := convA_spine C.hE C.hI C.hR (iotaFnA_subst C.hE C.hEN) hΓ'
    (convArgsA_append hPF (C.ctorTel gc (ls.take fm.arity) R.lF R.hqs) hfF)
    ((LRRelA_conv hcK).elim fun hc => ⟨convA_of_tyConvA hc hTn⟩) _ happF
  -- at the carrier
  obtain ⟨cy⟩ := tyHRedStarA_conv ha
  obtain ⟨tFI⟩ := LREqA_tyConv hEqF
  have tFD : TyConvA E (iotaIfaceA E) n Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ resF))
      (foldAppsA (.const f lsA) (qs ++ isA)) := .trans _ _ _ _ tFI hDc.symm
  have hcvD : ConvA E (iotaIfaceA E) n Γ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ fs)) y
      (foldAppsA (.const f lsA) (qs ++ isA)) :=
    .trans _ _ _ _ _ (convA_of_tyConvA hcvF tFD) (.symm _ _ _ _ cy)
  have tcF := convA_hasTy_left C.hE C.hI C.hR (iotaFnA_subst C.hE C.hEN) hΓ' hcvD
  -- the pair is a constructor step of the operator: the fields walked at the recursor's levels
  have hfw :=
    C.fieldsWalk gc hcm R.lF hl₀.1 R.hqs gc.view.fields [] [] fs fs (List.nil_append _).symm rfl hfsL
      (by have h := argsRelKA_refl_left C.hNCT hW2; simpa only [List.nil_append] using h)
  have hPq : ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) qs qs :=
    convArgsA_refl_left (convArgsA_of_argsRelKA hqF)
  have hLcy : FamLfpA E n ρ₀ k Γ f fm (foldAppsA (.const f lsA) (qs ++ isA))
      (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ fs)) y := by
    refine LfpWA.fold famPhiWA_mono ⟨⟨hcvD⟩, Or.inl ⟨gc.ref, gc.member, ls.take fm.arity, lsC,
      gc.view.fields.map FieldA.shape, qs, ps₁, fs, fs,
      (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort) qs (consListA qs SubstA.id)
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
        (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).1,
      (ctorFieldsA f lsC (instLevel lsC fv.sort) qs (consListA qs SubstA.id)
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsC))
        (gc.view.res.map (instantiateLevelsA lsC))).1,
      hcm, hk, hfam, ?_, hFC, (gc.normA_getD.symm ▸ gc.view.shapes C.hfresh), ?_, ?_, ?_, R.hqs, hp₁,
      tyHRedStarA_refl tcF, ha,
      C.ctorWhnf gc hcm Γ _ _, hna, ?_, ?_, ?_⟩⟩
    · rw [carrierLevelsA_foldAppsA]; exact ⟨eqNListB_symm hl₀ R.bF, hlC.2⟩
    · rw [hcp]; exact C.ctorTel gc (ls.take fm.arity) R.lF R.hqs
    · rw [hcp]; exact C.ctorTel gc lsC hlCl R.hqs
    · exact ⟨lsA, ls.take fm.arity, lsC, qs ++ isA, resF, resC, TF,
        foldAppsA (.const f (ls.take fm.arity)) (qs ++ resF), foldAppsA (.const f lsC) (qs ++ resC),
        foldAppsA_const_head _ _ _, by rw [htk]; exact hTF, hRF', by rw [htk, foldAppsA_const_head],
        eqNListA_symm hl₀.1, by rw [htk, hdr]; exact a1, hRC, by rw [htk, foldAppsA_const_head],
        hlC.1.1, by rw [htk, hdr]; exact hwR⟩
    · rw [hcp, carrierLevelsA_foldAppsA]
      simpa only [List.length_nil, Nat.add_zero, List.append_nil] using hfw
    · rw [hcp]; exact hPq
    · rw [hcp]; exact hP₁
  have hyc : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ resF))
      (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ fs)) y :=
    LRRelA_transport' C.hNCT (LREqA_symm C.hNCT hEqF) (C.lrRel R.hqs hRF (hmv hLcy))
  -- the minor's conclusion equals the redex's type
  obtain ⟨hEqM, _, _⟩ :=
    (LRRelA_sort_elim' (R.motRel (LRRelA_refl_left C.hNCT R.hmot) R.hqs hidxR hresL hyc)).1 k R.hkM
  have hredY := LRRelA_transport' C.hNCT hEqM hred
  -- ι on each side
  have hpc := R.piCount
  have hlenP : (qs ++ [mot] ++ ms ++ is₁).length + 1 = piCountA rec.member.mtypeA := by
    rw [hpc]; simp only [List.length_append, List.length_singleton, R.hqs, R.hms, hl₁] <;> omega
  have hlenP' : (qs' ++ [mot'] ++ ms' ++ is₁').length + 1 = piCountA rec.member.mtypeA := by
    rw [hpc]; simp only [List.length_append, List.length_singleton, R.hqs', R.hms', hl₁'] <;> omega
  have hprel : (qs ++ [mot] ++ ms ++ is₁).length = fv.params.length + 1 + cs.length + fv.indices.length := by
    simp only [List.length_append, List.length_singleton, R.hqs, R.hms, hl₁, fv.nparams]
  have hprel' : (qs' ++ [mot'] ++ ms' ++ is₁').length = fv.params.length + 1 + cs.length + fv.indices.length := by
    simp only [List.length_append, List.length_singleton, R.hqs', R.hms', hl₁', fv.nparams]
  have hmin₁ : (qs ++ [mot] ++ ms ++ is₁)[fv.params.length + 1 + j]? = some (ms[j]'hjm) := by
    rw [fv.nparams, ← R.hqs]; exact getElem?_pfx_minorA hjm
  have hmin₂ : (qs' ++ [mot'] ++ ms' ++ is₁')[fv.params.length + 1 + j]? = some (ms'[j]'hjm') := by
    rw [fv.nparams, ← R.hqs']; exact getElem?_pfx_minorA hjm'
  have hιL := iotaFnA_groupRecA R.hgf R.hlay C.hcls R.hpre hj (ls := ls) (lsC := lsC) (ps₁ := ps₁) (fs := fs)
    hprel R.hl (by rw [fv.nparams]; exact hp₁) hfsL hmin₁
  have hιR := iotaFnA_groupRecA R.hgf R.hlay C.hcls R.hpre hj (ls := ls') (lsC := lsC') (ps₁ := ps₂) (fs := fs')
    hprel' ((eqNList_length ls ls' R.heq).symm.trans R.hl) (by rw [fv.nparams]; exact hp₂) hfsL' hmin₂
  have hct : recHasCtorA (f + 1 + cs.length) rec.member = true := recHasCtorA_of_iotaFnA R.members hιL
  rw [fv.nparams, take_pfxA R.hqs] at hιL
  rw [fv.nparams, take_pfxA R.hqs'] at hιR
  rw [foldAppsA_snoc] at hιL hιR
  obtain ⟨ty⟩ := tyHRedStarA_hasTy_head ha
  have tyD := hasTyA_of_tyConvA ty hDc
  obtain ⟨⟨sz, ⟨tzB⟩⟩, ⟨czB⟩⟩ := motInstCondA hg hDc tyD (.refl _ _ _ ty) ha
  obtain ⟨⟨sz', ⟨tzB'⟩⟩, ⟨czB'⟩⟩ := motInstCondA hg hDc tyD hc hb
  obtain ⟨tz⟩ := tyHRedStarA_hasTy_end ha
  obtain ⟨tz'⟩ := tyHRedStarA_hasTy_end hb
  have hlhsL : HasTyA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ ms ++ is₁))
      (foldAppsA (.const gc.ref lsC) (ps₁ ++ fs))) (foldAppsA mot (is₁ ++ [y])) := by
    have h1 : HasTyA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ ms ++ is₁))
        (foldAppsA (.const gc.ref lsC) (ps₁ ++ fs))) (instantiate0A (foldAppsA (.const gc.ref lsC) (ps₁ ++ fs)) B) :=
      .app Γ _ _ _ B _ _ sz hBty (by rw [hBx, foldAppsA_snoc]; exact tzB) tH (hasTyA_of_tyConvA tz hDc)
    rw [hBx, foldAppsA_snoc] at h1
    rw [foldAppsA_snoc]
    exact hasTyA_of_tyConvA h1 czB
  have hlhsR : HasTyA E (iotaIfaceA E) n Γ
      (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ ms' ++ is₁'))
      (foldAppsA (.const gc.ref lsC') (ps₂ ++ fs'))) (foldAppsA mot (is₁ ++ [y])) := by
    have h1 : HasTyA E (iotaIfaceA E) n Γ
        (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ ms' ++ is₁'))
        (foldAppsA (.const gc.ref lsC') (ps₂ ++ fs'))) (instantiate0A (foldAppsA (.const gc.ref lsC') (ps₂ ++ fs')) B) :=
      .app Γ _ _ _ B _ _ sz' hBty (by rw [hBx, foldAppsA_snoc]; exact tzB') tH' (hasTyA_of_tyConvA tz' hDc)
    rw [hBx, foldAppsA_snoc] at h1
    rw [foldAppsA_snoc]
    exact hasTyA_of_tyConvA h1 czB'
  obtain ⟨⟨trL⟩, ⟨trR⟩⟩ := LRRelA_hasTy hredY
  have hshT : ∀ (ls : List Level) (pre : List ExprA),
      structHeadA E (foldAppsA (.const (f + 1 + cs.length) ls) pre) = false := fun _ _ => by
    rw [structHeadA_foldAppsA R.members]; exact structGroupA_groupRecA_of_type rec C.hUT
  have hstepL := TyHRedA.iota Γ _ _ _ (iotaRelA_of (foldAppsA_const_not_lam _ _ _)
    (hStepFnA_recSpine_below Γ R.members rec.hcls ls _ (by omega)) (hshT _ _) hιL) hlhsL trL
  have hstepR := TyHRedA.iota Γ _ _ _ (iotaRelA_of (foldAppsA_const_not_lam _ _ _)
    (hStepFnA_recSpine_below Γ R.members rec.hcls ls' _ (by omega)) (hshT _ _) hιR) hlhsR trR
  have h2 := LRRelA_expand_right C.hE C.hI ⟨⟨hlhsR⟩, ⟨hstepR⟩⟩
    (LRRelA_expand_left C.hE C.hI ⟨⟨hlhsL⟩, ⟨hstepL⟩⟩ hredY)
  -- the two majors' chains
  rw [foldAppsA_snoc (.const _ ls) (qs ++ [mot] ++ ms ++ is₁) y,
    foldAppsA_snoc (.const _ ls') (qs' ++ [mot'] ++ ms' ++ is₁') y']
  obtain ⟨tchain⟩ := ha
  obtain ⟨tchain'⟩ := hb
  have hL := LRRelA_expand_majorChain C.hE C.hI
    (recAtMajorA_recSpine R.members rec.hcls hct ls _ hlenP)
    (unitMinorA_foldAppsA_none R.members (unitGroupA_groupRecA_of_type rec C.hUT) ls _)
    (by rw [structHeadA_foldAppsA R.members]; exact structGroupA_groupRecA_of_type rec C.hUT)
    (hStepFnA_recSpine_below Γ R.members rec.hcls ls _ (by omega))
    tH hBty hDc (fun z z' hs => iotaFnA_app_none_of_step (tyHRedA_hStep hs)) tchain
    (fun w hw => by
      rw [hBx w, foldAppsA_snoc, foldAppsA_snoc]
      exact motInstCondA hg hDc tyD (.refl _ _ _ ty) hw) h2
  exact LRRelA_expand_majorChain_right C.hE C.hI
    (recAtMajorA_recSpine R.members rec.hcls hct ls' _ hlenP')
    (unitMinorA_foldAppsA_none R.members (unitGroupA_groupRecA_of_type rec C.hUT) ls' _)
    (by rw [structHeadA_foldAppsA R.members]; exact structGroupA_groupRecA_of_type rec C.hUT)
    (hStepFnA_recSpine_below Γ R.members rec.hcls ls' _ (by omega))
    tH' hBty hDc (fun z z' hs => iotaFnA_app_none_of_step (tyHRedA_hStep hs)) tchain'
    (fun w hw => by
      rw [hBx w, foldAppsA_snoc, foldAppsA_snoc]
      exact motInstCondA hg hDc tyD hc hw) hL

/-- THE CORE INDUCTION: every pair of the canonical fixed point at a carrier satisfies the recursor's
    induction predicate — induction on the fixed point, the fixed point itself carried beside the
    predicate (the conjunction device) so the constructor case folds its recursive fields back. The
    predicate is read at every well-formed world (R-NoFunRec-1 step 1 (1c-ε1), `RecIHWA`), so a
    function-recursive field's pairs, which the operator gives at the extensions, reach it at the composed
    world: the constructor case at a world is `RecAtA.ctor` at the instance weakened there
    (`RecAtA.wk`). -/
theorem core (R : RecAtA C rec ls ls' k Γ qs qs' mot mot' ms ms') {D y y' : ExprA}
    (h : FamLfpA E n ρ₀ k Γ f fm D y y') :
    RecIHA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls' mot qs qs'
      (qs ++ [mot] ++ ms) (qs' ++ [mot'] ++ ms') D y y' := by
  have step : ∀ (ρ : WkSpecA) (D y y' : ExprA),
      FamPhiWA E (iotaIfaceA E) n Γ f fm (famRsA E (iotaIfaceA E) n ρ₀ k Γ)
        (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm) (famRsIA E (iotaIfaceA E) n ρ₀ k Γ)
        (RecCoreA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls' mot mot' qs qs' ms ms')
        ρ D y y' →
      RecCoreA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls' mot mot' qs qs' ms ms'
        ρ D y y' := by
    intro ρ D y y' hΦ
    have hL : LfpWA (FamPhiWA E (iotaIfaceA E) n Γ f fm (famRsA E (iotaIfaceA E) n ρ₀ k Γ)
        (famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm) (famRsIA E (iotaIfaceA E) n ρ₀ k Γ)) ρ D y y' :=
      LfpWA.fold famPhiWA_mono (famPhiA_mono (fun _ _ _ h => h.2) (fun _ _ _ _ _ h => h.2) hΦ)
    refine ⟨fun hρ => ?_, hL⟩
    have Rw := R.wk hρ
    have hpf : qs.map (wkExprA ρ) ++ [wkExprA ρ mot] ++ ms.map (wkExprA ρ) =
        (qs ++ [mot] ++ ms).map (wkExprA ρ) := by simp
    have hpf' : qs'.map (wkExprA ρ) ++ [wkExprA ρ mot'] ++ ms'.map (wkExprA ρ) =
        (qs' ++ [mot'] ++ ms').map (wkExprA ρ) := by simp
    obtain ⟨hcv, hs⟩ := hΦ
    rcases hs with ⟨c, cm, lsC, lsC', kinds, ps₁, ps₂, fs, fs', T, T', hcm, hk, hfam, hlC, hlsC, hkinds, hT, hT',
        hcoh, hp₁, hp₂, ha, hb, hna, _, hargs⟩ | ⟨N, N', ha, hb, hN, hN'⟩
    · have hLw : FamLfpA E n ρ₀ k (wkCtxA ρ Γ) f fm D y y' := by
        show LfpWA _ [] D y y' 
        rw [famLfpWA_wk, WkSpecA.comp_nil]; exact hL
      have hRsF : famRsFA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ) fm [] = famRsFA E (iotaIfaceA E) n ρ₀ k Γ fm ρ := by
        rw [famRsFA_wkCtx]; simp only [WkSpecA.comp_nil]
      have hRs : famRsA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ) [] = famRsA E (iotaIfaceA E) n ρ₀ k Γ ρ := by
        rw [famRsA_wkCtx]; simp only [WkSpecA.comp_nil]
      have hRI : ∀ (c : Nat) (lsC : List Level), innerRelsA (famRsIA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ)) [] c lsC =
          innerRelsA (famRsIA E (iotaIfaceA E) n ρ₀ k Γ) ρ c lsC := fun c lsC => by
        rw [famRsIA_wkCtx, innerRelsA_comp, WkSpecA.comp_nil]
      have hargs2 : ArgsRelA (famRsA E (iotaIfaceA E) n ρ₀ k (wkCtxA ρ Γ) [] c lsC)
          (famRecRelA fm (carrierParamsA fm D) (carrierLevelsA D)
            (fun D y y' => RecIHA E n ρ₀ k (wkCtxA ρ Γ) f (f + 1 + cs.length) fm fv.indices.length
              (ls.take fm.arity) ls ls' (wkExprA ρ mot) (qs.map (wkExprA ρ)) (qs'.map (wkExprA ρ))
              (qs.map (wkExprA ρ) ++ [wkExprA ρ mot] ++ ms.map (wkExprA ρ))
              (qs'.map (wkExprA ρ) ++ [wkExprA ρ mot'] ++ ms'.map (wkExprA ρ)) D y y' ∧
              FamLfpA E n ρ₀ k (wkCtxA ρ Γ) f fm D y y'))
          (FamFunIHA E n ρ₀ k (wkCtxA ρ Γ) f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity) ls ls'
            (wkExprA ρ mot) (qs.map (wkExprA ρ)) (qs'.map (wkExprA ρ))
            (qs.map (wkExprA ρ) ++ [wkExprA ρ mot] ++ ms.map (wkExprA ρ))
            (qs'.map (wkExprA ρ) ++ [wkExprA ρ mot'] ++ ms'.map (wkExprA ρ)) c lsC (carrierParamsA fm D)
            (carrierLevelsA D))
          fm.nparamsA (carrierParamsA fm D) T kinds fs fs' := by
        simp only [FamFunIHA]
        rw [hRs, hRI c lsC]
        refine argsRelA_mono (famRecRelA_mono (fun D a b h => ⟨?hr, ?hl⟩))
          (fun i prev A j g g' hF => ?hf) hargs.1
        case hr =>
          rw [hpf, hpf']
          exact h.1 hρ
        case hl =>
          show LfpWA _ [] D a b
          rw [famLfpWA_wk, WkSpecA.comp_nil]
          exact h.2
        case hf =>
          refine famFunRelA_mono (fun ρ' hρ' => famRecRelA_mono (fun D a b hx => ⟨?hr2, ?hl2⟩)) i prev A j g g' hF
          case hr2 =>
            rw [hpf, hpf', recIHWA_wk]
            exact hx.1 (wkOkA_comp hρ hρ')
          case hl2 =>
            rw [famLfpWA_wk]
            exact hx.2
      have hc := Rw.ctor hcv hLw hcm hk hfam hlC hlsC hkinds hT hT' (by rw [hRsF]; exact hcoh) hp₁ hp₂ ha hb hna
        hargs2 hargs.2.1
      simpa only [RecIHWA, List.map_append, List.map_cons, List.map_nil] using hc
    · have hc := Rw.stuck hcv ha hb hN hN'
      simpa only [RecIHWA, List.map_append, List.map_cons, List.map_nil] using hc
  have hmain := (LfpWA.ind (X := RecCoreA E n ρ₀ k Γ f (f + 1 + cs.length) fm fv.indices.length (ls.take fm.arity)
    ls ls' mot mot' qs qs' ms ms') step h).1 ⟨trivial, R.hΓ⟩
  rwa [recIHWA_nil] at hmain

end RecAtA
end RecAt


/-! ## (7') O1-b-1: THE UNIT GROUP

The K-unit arm fires at a recursor whose type passes `unitGroupA`. At a group's recursor the test
holds only at a unit group: one constructor, no index, a `Prop` family, a constructor without fields
(`unitShape_of_unitGroupA`). There every full application steps to its minor, and the clause relates
the two minors at the redex's type (`recUnitAppsA`). -/

section UnitShape

/-- a lift keeps the spine head when it is a constant. -/
theorem appsSpineA_liftA_head_const (c a : Nat) : (e : ExprA) → {r : Nat} → {ls : List Level} →
    (appsSpineA (liftA c a e)).1 = .const r ls → (appsSpineA e).1 = .const r ls
  | .app g x, r, ls, h => appsSpineA_liftA_head_const c a g (r := r) (ls := ls) h
  | .bvar i, r, ls, h => by
      have : (appsSpineA (liftA c a (.bvar i))).1 = liftA c a (.bvar i) := by
        simp only [liftA]; split <;> rfl
      rw [this] at h
      simp only [liftA] at h
      split at h <;> exact ExprA.noConfusion h
  | .const _ _, _, _, h => h
  | .sort _, _, _, h => ExprA.noConfusion h
  | .lam _ _ _, _, _, h => ExprA.noConfusion h
  | .pi _ _ _ _, _, _, h => ExprA.noConfusion h
  | .letE _ _ _, _, _, h => ExprA.noConfusion h
  | .lit _, _, _, h => ExprA.noConfusion h

/-- the domains of a telescope name only what the telescope names. -/
theorem constsInA_piTelA_doms {D : Nat → Prop} (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → ConstsInA D (piTelA ds B w).1 → ∀ d ∈ ds, ConstsInA D d.1
  | [], _, d, hd => absurd hd (List.not_mem_nil d)
  | (A, u) :: ds, h, d, hd => by
      have h' : ConstsInA D A ∧ ConstsInA D (piTelA ds B w).1 := h
      rcases List.mem_cons.1 hd with rfl | hd'
      · exact h'.1
      · exact constsInA_piTelA_doms B w ds h'.2 d hd'

theorem liftDomsA_append (a : Nat) : (c : Nat) → (xs ys : List (ExprA × Level)) →
    liftDomsA c a (xs ++ ys) = liftDomsA c a xs ++ liftDomsA (c + xs.length) a ys
  | c, [], ys => by simp only [List.nil_append, liftDomsA, List.length_nil, Nat.add_zero]
  | c, (D, u) :: xs, ys => by
      have ih := liftDomsA_append a (c + 1) xs ys
      have e : c + 1 + xs.length = c + (xs.length + 1) := by omega
      rw [e] at ih
      show (liftA c a D, u) :: liftDomsA (c + 1) a (xs ++ ys) = _
      rw [ih]
      rfl

/-- a minor premise's type is never a sort. -/
theorem minorFieldsA_ne_sort (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) (w : Level) :
    (fs : List FieldA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    (minorFieldsA f c ls wF wM pl mot fl σ fs res).1 ≠ .sort w
  | [], pl, mot, fl, σ, h => by
      simp only [minorFieldsA] at h
      rw [foldAppsA_snoc] at h
      exact ExprA.noConfusion h
 
  | .plain _ _ :: _, _, _, _, _, h
  | .drec _ :: _, _, _, _, _, h
  | .frec _ _ _ _ :: _, _, _, _, _, h
  | .drecD _ _ :: _, _, _, _, _, h =>
      ExprA.noConfusion h

/-- a minor premise without fields is no Π; with fields its first codomain is never a sort. -/
theorem minorFieldsA_nil_not_pi (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA)
    (pl : List ExprA) (mot : ExprA) (fl : List ExprA) (σ : SubstA) (A : ExprA) (u : Level) (B : ExprA) (v : Level) :
    (minorFieldsA f c ls wF wM pl mot fl σ [] res).1 ≠ .pi A u B v := by
  intro h
  simp only [minorFieldsA] at h
  rw [foldAppsA_snoc] at h
  exact ExprA.noConfusion h

theorem minorFieldsA_cod_ne_sort (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    ∀ A u B v w, (minorFieldsA f c ls wF wM pl mot fl σ fs res).1 = .pi A u B v → B ≠ .sort w
  | [], pl, mot, fl, σ, A, u, B, v, _, h => absurd h (minorFieldsA_nil_not_pi f c ls wF wM res pl mot fl σ A u B v)
  | .plain _ _ :: fs, pl, mot, fl, σ, A, u, B, v, w, h => by
      simp only [minorFieldsA] at h
      injection h with _ _ hB _
      rw [← hB]
      exact minorFieldsA_ne_sort f c ls wF wM res w fs _ _ _ _
 
  | .drec _ :: fs, pl, mot, fl, σ, A, u, B, v, w, h
  | .frec _ _ _ _ :: fs, pl, mot, fl, σ, A, u, B, v, w, h
  | .drecD _ _ :: fs, pl, mot, fl, σ, A, u, B, v, w, h => by
      simp only [minorFieldsA] at h
      injection h with _ _ hB _
      rw [← hB]
      exact fun h' => ExprA.noConfusion h'

theorem minorFieldsA_cons_pi (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA) :
    (fs : List FieldA) → fs ≠ [] → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    ∃ A u B v, (minorFieldsA f c ls wF wM pl mot fl σ fs res).1 = .pi A u B v
  | [], h, _, _, _, _ => absurd rfl h
 
  | .plain _ _ :: _, _, _, _, _, _
  | .drec _ :: _, _, _, _, _, _
  | .frec _ _ _ _ :: _, _, _, _, _, _
  | .drecD _ _ :: _, _, _, _, _, _ =>
      ⟨_, _, _, _, rfl⟩

/-- what the unit test reads, when it holds. -/
theorem unitGroupA_true_inv {r : Nat} {m : CheckedMemberA} (h : unitGroupA r m = true) :
    ∃ D uD Dm um Dmot umot rest,
      (piDomListA m.mtypeA).reverse = (D, uD) :: (Dm, um) :: (Dmot, umot) :: rest ∧
      (∃ f ls, (appsSpineA D).1 = .const f ls ∧ r = f + 2) ∧ levelIsZero uD = true ∧
      (∃ D' u w v, Dmot = .pi D' u (.sort w) v ∧ D = liftA 0 2 D') ∧ (∀ A u B v, Dm ≠ .pi A u B v) := by
  unfold unitGroupA at h
  split at h
  next D uD Dm um Dmot umot rest hL =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨D, uD, Dm, um, Dmot, umot, rest, hL, ?_, h2, ?_, ?_⟩
    · split at h1
      next f ls hf => exact ⟨f, ls, hf, of_decide_eq_true h1⟩
      next => exact absurd h1 (by decide)
    · split at h3
      next D' u w v => exact ⟨D', u, w, v, rfl, of_decide_eq_true h3⟩
      next => exact absurd h3 (by decide)
    · split at h4
      next => exact absurd h4 (by decide)
      next hn => exact fun A u B v e => hn A u B v e
  next => exact absurd h (by decide)

/-- the reversed lifted index telescope ends with its last index, lifted past the earlier ones. -/
theorem liftDomsA_snoc_reverse (c a : Nat) (pre : List (ExprA × Level)) (x : ExprA × Level) :
    (liftDomsA c a (pre ++ [x])).reverse = (liftA (c + pre.length) a x.1, x.2) :: (liftDomsA c a pre).reverse := by
  rw [liftDomsA_append]
  simp only [liftDomsA, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]

/-- O1-b-1, THE SOUNDNESS OF THE UNIT TEST: at a group's recursor the test holds only at a unit group —
    one constructor, no index, a `Prop` sort, a constructor without fields. The index domains name
    only members of the base (`hfree`), where the family is fresh (`hf0`). -/
theorem unitShape_of_unitGroupA {I : IotaIfaceA} {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)} (rec : GroupRecA I E₀ f fm fv cs)
    (hfree : ∀ d ∈ fv.indices, ConstsInA (domA E₀) d.1) (hf0 : E₀.members f = none)
    (hu : unitGroupA (f + 1 + cs.length) rec.member = true) :
    cs.length = 1 ∧ fv.indices = [] ∧ levelIsZero fv.sort = true ∧
      ∀ cd ∈ cs.reverse.map GroupCtorA.minorData, cd.2.1 = [] := by
  obtain ⟨D, uD, Dm, um, Dmot, umot, rest, hL, ⟨f', ls', hD, hr⟩, hz, ⟨D', u', w', v', hmot, hDD⟩, hDm⟩ :=
    unitGroupA_true_inv hu
  have hst : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst
  rw [hst, piDomListA_recTypeA_reverse] at hL
  injection hL with h1 hL'
  injection h1 with hD1 hu1
  subst hD1 hu1
  have hhead := appsSpineA_majorDom f (canonLevelsA fm.arity) fv.params.length fv.indices.length
    ((cs.reverse.map GroupCtorA.minorData).length + 1)
  rw [hD] at hhead
  injection hhead with hf _
  subst hf
  have hcs : cs.length = 1 := by omega
  have hcds : (cs.reverse.map GroupCtorA.minorData).length = 1 := by
    rw [List.length_map, List.length_reverse, hcs]
  obtain ⟨cd, hcd⟩ : ∃ cd, cs.reverse.map GroupCtorA.minorData = [cd] := by
    match h : cs.reverse.map GroupCtorA.minorData, hcds with
    | [cd], _ => exact ⟨cd, rfl⟩
  rw [hcd] at hL' hDD hD
  have hnoidx : fv.indices = [] := by
    cases hR : fv.indices.reverse with
    | nil => exact List.reverse_eq_nil_iff.1 hR
    | cons b rs =>
        exfalso
        have hI : fv.indices = rs.reverse ++ [b] := by
          rw [← List.reverse_reverse fv.indices, hR, List.reverse_cons]
        rw [hI, List.reverse_append, liftDomsA_snoc_reverse, List.cons_append] at hL'
        injection hL' with _ hL2
        cases rs with
        | nil =>
            -- one index: the third binder from the end is the minor
            simp only [List.reverse_nil, liftDomsA, List.nil_append, minorDomsA, List.reverse_append,
              List.reverse_cons, List.singleton_append, List.cons_append] at hL2
            injection hL2 with hm0 _
            injection hm0 with hm0 _
            rw [liftA_zero] at hm0
            exact minorFieldsA_cod_ne_sort f' cd.1 (canonLevelsA fm.arity) fv.sort
              (rec.elim.motiveLevel fm.arity) cd.2.2 cd.2.1 _ _ _ _ D' u' (.sort w') v' w'
              (hm0.trans hmot) rfl
        | cons a pre =>
            -- two or more: the third binder from the end is an index, which cannot name the family
            rw [List.reverse_cons, liftDomsA_snoc_reverse, List.cons_append] at hL2
            injection hL2 with ha _
            injection ha with ha _
            rw [hmot] at ha
            have hmem : a ∈ fv.indices := by rw [hI]; simp
            have hca := hfree a hmem
            cases ha1 : a.1 with
            | pi A₀ u₀ B₀ v₀ =>
                rw [ha1] at ha hca
                simp only [liftA] at ha
                injection ha with hA _ _ _
                rw [← hA] at hDD
                have h1 := hD
                rw [hDD] at h1
                have h2 := appsSpineA_liftA_head_const _ _ _ (appsSpineA_liftA_head_const _ _ _ h1)
                obtain ⟨m0, hm0⟩ := constsInA_head A₀ hca.1 _ _ h2
                rw [hf0] at hm0
                exact Option.noConfusion hm0
            | bvar i =>
                rw [ha1] at ha; simp only [liftA] at ha; split at ha <;> exact ExprA.noConfusion ha
            | sort _ => rw [ha1] at ha; exact ExprA.noConfusion ha
            | const _ _ => rw [ha1] at ha; exact ExprA.noConfusion ha
            | app _ _ => rw [ha1] at ha; exact ExprA.noConfusion ha
            | lam _ _ _ => rw [ha1] at ha; exact ExprA.noConfusion ha
            | letE _ _ _ => rw [ha1] at ha; exact ExprA.noConfusion ha
            | lit _ => rw [ha1] at ha; exact ExprA.noConfusion ha
  refine ⟨hcs, hnoidx, hz, ?_⟩
  -- the constructor has no field: the second binder from the end is the minor, not a Π
  intro cd' hcd'
  rw [hcd] at hcd'
  cases List.mem_singleton.1 hcd'
  rw [hnoidx] at hL'
  simp only [liftDomsA, List.append_nil, minorDomsA, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.cons_append] at hL'
  injection hL' with hm0 _
  injection hm0 with hm0 _
  rw [liftA_zero] at hm0
  cases hfl : cd.2.1 with
  | nil => rfl
  | cons fl fls =>
      exfalso
      obtain ⟨A, u, B, v, hpi⟩ := minorFieldsA_cons_pi f' cd.1 (canonLevelsA fm.arity) fv.sort
        (rec.elim.motiveLevel fm.arity) cd.2.2 cd.2.1 (by rw [hfl]; exact List.cons_ne_nil _ _) _ _ _ _
      exact hDm A u B v (hm0.symm.trans hpi)


end UnitShape

section UnitClause
variable {E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat}

/-- O1-b-1, THE RECURSORS' CLAUSE AT A UNIT GROUP, at one world: full applications to related arguments
    are related at their type. Both sides step to their minors (K-unit, or ι when the major is the
    constructor); the minors are related at the minor's type `M (c qs)`; and that type is the redex's
    `M x`: the family application is a proposition, so the major is related to the constructor there
    (proof irrelevance), and the motive carries the pair. -/
theorem recUnitAppsA (hE : EnvClosedA E) (hEL : EnvLevelsA E)
    (hN : EnvNormClosedA E) (hNCT : EnvNormCtorTypeA E) (hNL : EnvNormLevelsA E)
    {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {u : Level} (hW : EnvWfA (iotaIfaceA E) E₀)
    (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none) (hclT : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA)
    (hT : HasTyA E₀ (iotaIfaceA E) fm.arity [] fm.mtypeA (.sort u)) (fv : FamViewA fm)
    (cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)) (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length)
    (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs) (hpre : PrefixA (groupRecEnvA cs rec) E)
    (hfund : BaseFundA E₀ E (iotaIfaceA E) n ρ₀) (hfc : BaseFundConvA E₀ E (iotaIfaceA E) n ρ₀)
    (hR₀ : IotaRecHeadTypedA E₀ (iotaIfaceA E))
    (hpreG : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    (ih : EnvSemAt E (iotaIfaceA E) n ρ₀ (domA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))))
    (hct : recHasCtorA (f + 1 + cs.length) rec.member = true)
    (hunit : unitGroupA (f + 1 + cs.length) rec.member = true)
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgc : cs.reverse = [gc]) (hnoidx : fv.indices = [])
    (hzF : levelIsZero fv.sort = true) (hnf : gc.view.fields = [])
    {ls ls' : List Level} (hl : ls.length = rec.member.arity) (hb : levelsBounded n ls = true)
    (heq : eqNList ls ls') (hwM : isZero (instLevel ls (rec.elim.motiveLevel fm.arity)) = false)
    {k : Nat} (hkM : ht ρ₀ (instLevel ls (rec.elim.motiveLevel fm.arity)) ≤ k)
    {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ))
    {RT : ExprA → ExprA → Prop}
    (hRT : LRTyA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls rec.member.mtypeA) RT)
    (hr₁ : HasTyA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) ls) (instantiateLevelsA ls rec.member.mtypeA))
    (hr₂ : HasTyA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) ls') (instantiateLevelsA ls rec.member.mtypeA))
    (hrc : ConvA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) ls) (.const (f + 1 + cs.length) ls')
      (instantiateLevelsA ls rec.member.mtypeA))
    {as as' : List ExprA}
    (hrel : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls rec.member.mtypeA) as as')
    (hlen : as.length = fm.nparamsA + 1 + cs.length + fv.indices.length + 1)
    {Cc : ExprA} (hC : applyTelA as (instantiateLevelsA ls rec.member.mtypeA) = some Cc) :
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ Cc (foldAppsA (.const (f + 1 + cs.length) ls) as)
      (foldAppsA (.const (f + 1 + cs.length) ls') as') := by
  have hI := iotaFnA_lift hE hN
  have hIS := iotaFnA_subst hE hN
  have hR := iotaFnA_recHead E
  have hIL := iotaFnA_levels hEL hNL
  have hE₀ := envWfA_closed hW
  have hEL₀ := envWfA_levels hW
  obtain ⟨hΓ'⟩ := hΓ
  have hgc0 : cs.reverse[0]? = some gc := by rw [hgc]; rfl
  have hcs1 : cs.length = 1 := by rw [← List.length_reverse, hgc]; rfl
  have hgcm : gc ∈ cs := List.mem_reverse.mp (by rw [hgc]; exact List.mem_singleton_self gc)
  obtain ⟨hrm, hfm, _⟩ := members_groupRecA hfresh hlay hpre
  have hres0 : gc.view.res = [] :=
    List.eq_nil_of_length_eq_zero (by rw [gc.view.res_length, hnoidx]; rfl)
  have hlF : (ls.take fm.arity).length = fm.arity := by
    rw [List.length_take, hl, rec.harity]; exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hbF : levelsBounded n (ls.take fm.arity) = true := levelsBounded_take ls _ hb
  have hls' : ls'.length = rec.member.arity := (eqNList_length ls ls' heq).symm.trans hl
  -- the arguments: the parameters, the motive, the one minor, no index, the major
  have hrel' := hrel
  rw [recTelA hEL hfm rec hl] at hrel'
  obtain ⟨qs, qs', mot, mot', x, x', ms, ms', is, is', rfl, rfl, hqs, hqs', hms, hms', his, his', hpar, hmot,
      hmin, hidx, hmaj, happ⟩ :=
    recArgsSplitPA _ _ _ _ _ _ _ _ hrel'
      (by simp only [List.length_map, List.length_reverse, instDomsA_length, fv.nparams]; omega)
  have hidx0 : instDomsA (ls.take fm.arity) fv.indices = [] := by rw [hnoidx]; rfl
  obtain rfl : is = [] := List.eq_nil_of_length_eq_zero (by rw [his, hidx0]; rfl)
  obtain rfl : is' = [] := List.eq_nil_of_length_eq_zero (by rw [his', hidx0]; rfl)
  have hcd : (cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)) =
      [(gc.ref, [], [])] := by
    rw [hgc]
    simp only [List.map_cons, List.map_nil, GroupCtorA.minorData, MinorDataA.inst, hnf, hres0]
  have hcd1 : ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length = 1 := by
    rw [hcd]; rfl
  obtain ⟨mn, rfl⟩ : ∃ mn, ms = [mn] := by
    match ms, hms.trans hcd1 with
    | [mn], _ => exact ⟨mn, rfl⟩
  obtain ⟨mn', rfl⟩ : ∃ mn', ms' = [mn'] := by
    match ms', hms'.trans hcd1 with
    | [mn'], _ => exact ⟨mn', rfl⟩
  have hqsN : qs.length = fm.nparamsA := by rw [hqs, instDomsA_length, fv.nparams]
  have hqsN' : qs'.length = fm.nparamsA := by rw [hqs', instDomsA_length, fv.nparams]
  have hqP : qs.length = fv.params.length := by rw [hqs, instDomsA_length]
  have hqP' : qs'.length = fv.params.length := by rw [hqs', instDomsA_length]
  -- the minor at the constructor's instance of the motive
  have hc0 : 0 < ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length := by
    rw [hcd1]; exact Nat.zero_lt_one
  have hMT : ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)))[0]'hc0 =
      (gc.ref, [], []) := by
    have h : ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)))[0]? =
        some (gc.ref, [], []) := by rw [hcd]; rfl
    obtain ⟨_, h'⟩ := List.getElem?_eq_some_iff.mp h
    exact h'
  have hσ : (fun i => substA (SubstA.cons mot (consListA qs SubstA.id)) (SubstA.id.shift1 i)) =
      consListA qs SubstA.id := by
    funext i
    show substA (SubstA.cons mot (consListA qs SubstA.id)) (liftA 0 1 (SubstA.id i)) = consListA qs SubstA.id i
    rw [substA_cons_liftA]
    rfl
  have hpl : ((paramLocalsA (instDomsA (ls.take fm.arity) fv.params).length).map (liftA 0 1)).map
      (substA (SubstA.cons mot (consListA qs SubstA.id))) = qs := by
    rw [map_substA_cons_liftA, ← hqs, paramLocalsA_consListA]
  have hmin0 := hmin 0 (by simp) (by simp) hc0
  rw [hMT, minorTyA, substA_minorFieldsA, hpl, hσ] at hmin0
  have hmin0' : LRRelA E (iotaIfaceA E) n ρ₀ k Γ
      (foldAppsA mot ([] ++ [foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ [])])) mn mn' := hmin0
  -- the motive at the major's binder, the family application typed at its sort, which is zero
  have hmP := motPiA ⟨hΓ'⟩ hqs hmot (hidx (.sort .zero) .zero) his
  obtain ⟨⟨hg₀⟩, _⟩ := LRRelA_hasTy hmP
  have hg : HasTyA E (iotaIfaceA E) n Γ mot (.pi (foldAppsA (.const f (ls.take fm.arity)) (qs ++ []))
      (instLevel (ls.take fm.arity) fv.sort) (.sort (instLevel ls (rec.elim.motiveLevel fm.arity)))
      (.succ (instLevel ls (rec.elim.motiveLevel fm.arity)))) := hg₀
  obtain ⟨RP, hRP⟩ := LRRelA_valid hmP
  rw [LRTyA_eq] at hRP
  obtain ⟨_, ⟨tP⟩⟩ := tyKA_hasTy hRP
  obtain ⟨⟨tQ⟩, _⟩ := hasTyA_pi_inv tP
  have hwF0 : eqN (instLevel (ls.take fm.arity) fv.sort) .zero :=
    (levelIsZero_iff _).mp (levelIsZero_instLevel _ hzF)
  have tQ0 := hasTyA_of_tyConvA tQ (tyConvA_sorts Γ hwF0)
  -- the family application is a proposition: its relation is the `prop` clause's
  have hnr : fm.mclass ≠ .recursorM := by rw [hcls]; exact fun h => MemberClass.noConfusion h
  have hTQn : hStepFnA E (iotaIfaceA E).fn Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) = none :=
    hStepFnA_constSpine_none hR hfm (Or.inr hnobody) hnr Γ (ls := ls.take fm.arity) _ (by rw [foldAppsA_const_head])
  have hD0 : (piDomsA fm.mtypeA).length = (instDomsA (ls.take fm.arity) (fv.params ++ fv.indices)).length := by
    rw [fv.stored, piDomsA_piTelA]
    simp [instDomsA, piDomsA]
  have hTQP : IsPropTy E (iotaIfaceA E) Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) :=
    (isPropTy_famApp_iff hfm fv.piBody (ls.take fm.arity) (qs ++ [])).mpr
      ⟨hlF, by rw [hD0, List.append_nil, hqs, hnoidx]; simp [instDomsA], (isZero_iff_eqN_zero _).mpr hwF0⟩
  have hTK := TyKA.prop (E := E) (I := iotaIfaceA E) (n := n) (ρ₀ := ρ₀) (k := k)
    (LE := fun j _ => LREqA E (iotaIfaceA E) n ρ₀ j) (LT := fun j _ => LRTyA E (iotaIfaceA E) n ρ₀ j)
    (whTyA_of_hasTy tQ) hTQn hTQP
  rw [← LRTyA_eq] at hTK
  obtain ⟨⟨tx⟩, ⟨tx'⟩⟩ := LRRelA_hasTy hmaj
  -- the constructor at the parameters, typed at the family application: its mirror telescope (P2)
  have hqF : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA)
      (qs ++ []) (qs ++ []) := by
    have h : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA)
        (qs ++ []) (qs' ++ []) := by
      rw [List.append_nil, List.append_nil, fv.inst_split]; exact hpar _ _
    exact argsRelKA_refl_left hNCT h
  obtain ⟨hwf⟩ := fv.paramsCtxWf hT
  have hwf₀ : CtxWfA E₀ (iotaIfaceA E) fm.arity (telCtxA fv.params ++ []) := (List.append_nil _).symm ▸ hwf
  obtain ⟨Km, hKm⟩ := mirrorParConvA hfc hNCT hE₀ hI hR₀ hEL₀ hIL hbF hbF hlF hlF (eqNListA_refl _)
    gc.view.mirrorsConv hwf₀
  obtain ⟨Kp, hKp⟩ := paramSubstA hfund hfc hNCT hN hE₀ hE hI hR₀ hEL₀ hIL fv hclT hT hbF hbF hlF hlF
    (eqNListA_refl _)
  have hVC := hKp (max Km (max Kp k)) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) qs qs [] []
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) ⟨hΓ'⟩ hqsN hqsN hqF [] (Or.inl rfl)
  simp only [map_wkExprA_nil] at hVC
  rw [← telCtxA_instDomsA] at hVC
  have hrelC := argsRelKA_of_validSubst hNCT (instDomsA (ls.take fm.arity) fv.params)
    (instantiateLevelsA (ls.take fm.arity) fv.idxTelA)
    (instLevel (ls.take fm.arity) (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2) qs qs
    (by rw [instDomsA_length, fv.nparams]; exact hqsN) (by rw [instDomsA_length, fv.nparams]; exact hqsN) hVC
  have hPC := hKm (max Km (max Kp k)) (Nat.le_max_left _ _) Γ ⟨hΓ'⟩ SubstA.id (ValidSubstA_nil _ _ _)
    (ValidSubstA_nil _ _ _) (instantiateLevelsA (ls.take fm.arity) fv.idxTelA)
    (instLevel (ls.take fm.arity) (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2)
    (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
      (paramLocalsA (instDomsA (ls.take fm.arity) gc.view.mirrors).length) SubstA.id
      (gc.view.fields.map (FieldA.instLevels (ls.take fm.arity)))
      (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).1
    (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
      (paramLocalsA (instDomsA (ls.take fm.arity) gc.view.mirrors).length) SubstA.id
      (gc.view.fields.map (FieldA.instLevels (ls.take fm.arity)))
      (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).2
    qs (by rw [substA_id]; exact hrelC) (by rw [fv.nparams]; exact hqsN)
  rw [substA_id, substA_id, ← fv.inst_split] at hPC
  have hcT : (piTelA (instDomsA (ls.take fm.arity) gc.view.mirrors)
      (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
        (paramLocalsA (instDomsA (ls.take fm.arity) gc.view.mirrors).length) SubstA.id
        (gc.view.fields.map (FieldA.instLevels (ls.take fm.arity)))
        (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).1
      (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
        (paramLocalsA (instDomsA (ls.take fm.arity) gc.view.mirrors).length) SubstA.id
        (gc.view.fields.map (FieldA.instLevels (ls.take fm.arity)))
        (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).2).1 =
      instantiateLevelsA (ls.take fm.arity) gc.member.mtypeA := by
    rw [gc.view.inst_tel _ hlF]; rfl
  rw [hcT] at hPC
  have hPq : ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) qs qs := by
    have h := convArgsA_refl_left (convArgsA_of_argsRelKA hqF)
    simpa only [List.append_nil] using h
  have hPF := convArgsA_rebase hPC hPq
  obtain ⟨k₀, hk₀⟩ := ih gc.ref gc.member ⟨gc.member, members_groupEnvA_ctor hfresh hgcm⟩
    (hpreG _ _ (members_groupEnvA_ctor hfresh hgcm)) (ls.take fm.arity) (ls.take fm.arity)
    (hlF.trans gc.harity.symm) hbF hbF (eqNListA_refl _)
  have hcK := hk₀ (max k k₀) (Nat.le_max_right _ _) Γ ⟨hΓ'⟩
  have happF : applyTelA qs (instantiateLevelsA (ls.take fm.arity) gc.member.mtypeA) =
      some (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) := by
    rw [gc.view.applyTel_params (ls.take fm.arity) hlF qs hqsN, hnf, hres0]
    rfl
  obtain ⟨hcvF⟩ := convA_spine hE hI hR hIS hΓ' hPF (LRRelA_conv hcK) _ happF
  have tc₀ : HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ []))
      (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) := by
    have h := convA_hasTy_left hE hI hR hIS hΓ' hcvF
    simpa only [List.append_nil] using h
  -- the major and the constructor, related at the proposition (irrelevance); the motive carries them
  have hxc : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) x
      (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ [])) :=
    LRRelA.of hTK ⟨⟨tx⟩, ⟨tc₀⟩, ⟨.irr Γ _ x _ tQ0 tx tc₀⟩⟩
  have hMM := motRelA ⟨hΓ'⟩ hqs (LRRelA_refl_left hNCT hmot) (B := .sort .zero) (w := .zero) (is := [])
    (is' := []) (.nil _) his hxc
  obtain ⟨hEqM, _, _⟩ := (LRRelA_sort_elim' hMM).1 k hkM
  have hred : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA mot ([] ++ [x])) mn mn' :=
    LRRelA_transport' hNCT (LREqA_symm hNCT hEqM) hmin0'
  obtain ⟨⟨tmn⟩, ⟨tmn'⟩⟩ := LRRelA_hasTy hred
  obtain ⟨⟨tMx⟩, ⟨tMc⟩, ⟨tyXC⟩⟩ := appSortConvA hg tx tc₀ (.irr Γ _ x _ tQ0 tx tc₀)
  obtain ⟨⟨tMx'⟩, _, ⟨tyX'X⟩⟩ := appSortConvA hg tx' tx (.irr Γ _ x' x tQ0 tx' tx)
  -- the two spines below the major, typed at the major's binder
  have hfull : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls rec.member.mtypeA)
      (qs ++ [mot] ++ [mn] ++ [x]) (qs' ++ [mot'] ++ [mn'] ++ [x']) := by
    have e1 : qs ++ ([mot] ++ [mn] ++ [] ++ [x]) = qs ++ [mot] ++ [mn] ++ [x] := by simp
    have e2 : qs' ++ ([mot'] ++ [mn'] ++ [] ++ [x']) = qs' ++ [mot'] ++ [mn'] ++ [x'] := by simp
    rw [e1, e2] at hrel
    exact hrel
  obtain ⟨Tp, hTp, hpreRel, _⟩ := argsRelKA_append_inv (xs := qs ++ [mot] ++ [mn])
    (xs' := qs' ++ [mot'] ++ [mn']) (ys := [x]) (ys' := [x'])
    (by simp only [List.length_append, List.length_singleton, hqs, hqs']) hfull
  obtain ⟨B, hB, hBx⟩ := applyTelA_recPrefixA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params)
    (instDomsA (ls.take fm.arity) fv.indices) (instLevel (ls.take fm.arity) fv.sort)
    (instLevel ls (rec.elim.motiveLevel fm.arity)) (instLevel ls (rec.elim.motiveLevel fm.arity)) _ qs mot [mn] []
    hqs hms his
  rw [← recTelA hEL hfm rec hl, show qs ++ ([mot] ++ [mn] ++ []) = qs ++ [mot] ++ [mn] by simp] at hB
  rw [hB] at hTp
  injection hTp with hTp
  subst hTp
  obtain ⟨⟨tH⟩, ⟨tH'⟩, _, ⟨RQ, hRQ⟩⟩ := spineConvA hE hI hNCT ⟨hΓ'⟩ hpreRel _
    (by simp only [List.length_append, List.length_singleton, hqsN, hcs1, hnoidx, List.length_nil]; omega)
    (recPiTelA hEL hfm rec hl hwM) hRT hr₁ hr₂ hrc _ hB
  rw [LRTyA_eq] at hRQ
  obtain ⟨_, ⟨tPB⟩⟩ := tyKA_hasTy hRQ
  obtain ⟨_, ⟨hBty⟩⟩ := hasTyA_pi_inv tPB
  -- the spine facts at both sides
  have hpc := piCountA_groupRecA rec
  have hlenP : (qs ++ [mot] ++ [mn]).length + 1 = piCountA rec.member.mtypeA := by
    rw [hpc]; simp only [List.length_append, List.length_singleton, hqsN, hcs1, hnoidx, List.length_nil]
  have hlenP' : (qs' ++ [mot'] ++ [mn']).length + 1 = piCountA rec.member.mtypeA := by
    rw [hpc]; simp only [List.length_append, List.length_singleton, hqsN', hcs1, hnoidx, List.length_nil]
  have hprel : (qs ++ [mot] ++ [mn]).length = fv.params.length + 1 + cs.length + fv.indices.length := by
    simp only [List.length_append, List.length_singleton, hqP, hcs1, hnoidx, List.length_nil]
  have hprel' : (qs' ++ [mot'] ++ [mn']).length = fv.params.length + 1 + cs.length + fv.indices.length := by
    simp only [List.length_append, List.length_singleton, hqP', hcs1, hnoidx, List.length_nil]
  have hmin1 : (qs ++ [mot] ++ [mn])[fv.params.length + 1]? = some mn := by
    rw [← hqP, List.append_assoc, List.getElem?_append_right (by omega),
      show qs.length + 1 - qs.length = 1 by omega]
    rfl
  have hmin1' : (qs' ++ [mot'] ++ [mn'])[fv.params.length + 1]? = some mn' := by
    rw [← hqP', List.append_assoc, List.getElem?_append_right (by omega),
      show qs'.length + 1 - qs'.length = 1 by omega]
    rfl
  have hfn := hStepFnA_recSpine_below Γ hrm rec.hcls ls (qs ++ [mot] ++ [mn]) (by omega)
  have hfn' := hStepFnA_recSpine_below Γ hrm rec.hcls ls' (qs' ++ [mot'] ++ [mn']) (by omega)
  have hnl := foldAppsA_const_not_lam (f + 1 + cs.length) ls (qs ++ [mot] ++ [mn])
  have hnl' := foldAppsA_const_not_lam (f + 1 + cs.length) ls' (qs' ++ [mot'] ++ [mn'])
  have huM : unitMinorA E (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) = some mn :=
    unitMinorA_foldAppsA_snoc hrm hunit ls (qs ++ [mot]) mn
  have huM' : unitMinorA E (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) = some mn' :=
    unitMinorA_foldAppsA_snoc hrm hunit ls' (qs' ++ [mot']) mn'
  have hshU : ∀ (ls : List Level) (pre : List ExprA),
      structHeadA E (foldAppsA (.const (f + 1 + cs.length) ls) pre) = false := fun _ _ => by
    rw [structHeadA_foldAppsA hrm]; exact structGroupA_false_of_unit hunit
  -- ι at the constructor, on each side: the minor
  have hιc : iotaFnA E (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn]))
      (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ []))) = some mn := by
    have h := iotaFnA_groupRecA hfresh hlay hcls hpre hgc0 (ls := ls) (lsC := ls.take fm.arity)
      (pre := qs ++ [mot] ++ [mn]) (ps₁ := qs) (fs := []) (minor := mn) hprel hl hqP (by rw [hnf]; rfl) hmin1
    rw [foldAppsA_snoc] at h
    rw [h]; rfl
  have hιc' : iotaFnA E (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn']))
      (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ []))) = some mn' := by
    have h := iotaFnA_groupRecA hfresh hlay hcls hpre hgc0 (ls := ls') (lsC := ls.take fm.arity)
      (pre := qs' ++ [mot'] ++ [mn']) (ps₁ := qs) (fs := []) (minor := mn') hprel' hls' hqP (by rw [hnf]; rfl)
      hmin1'
    rw [foldAppsA_snoc] at h
    rw [h]; rfl
  -- the left redex and the left spine at the constructor, typed at the redex's type
  have tLx : HasTyA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) x)
      (foldAppsA mot ([] ++ [x])) := by
    have h1 := HasTyA.app Γ _ x _ B _ _ (instLevel ls (rec.elim.motiveLevel fm.arity)) hBty
      (by rw [hBx]; exact tMx) tH tx
    rw [hBx] at h1
    exact h1
  have tLc : HasTyA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn]))
      (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ []))) (foldAppsA mot ([] ++ [x])) := by
    have h1 := HasTyA.app Γ _ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ [])) _ B _ _
      (instLevel ls (rec.elim.motiveLevel fm.arity)) hBty (by rw [hBx]; exact tMc) tH tc₀
    rw [hBx] at h1
    exact hasTyA_of_tyConvA h1 tyXC.symm
  have tRx : HasTyA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) x')
      (foldAppsA mot ([] ++ [x])) := by
    have h1 := HasTyA.app Γ _ x' _ B _ _ (instLevel ls (rec.elim.motiveLevel fm.arity)) hBty
      (by rw [hBx]; exact tMx') tH' tx'
    rw [hBx] at h1
    exact hasTyA_of_tyConvA h1 tyX'X
  have tRc : HasTyA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn']))
      (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ []))) (foldAppsA mot ([] ++ [x])) := by
    have h1 := HasTyA.app Γ _ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ [])) _ B _ _
      (instLevel ls (rec.elim.motiveLevel fm.arity)) hBty (by rw [hBx]; exact tMc) tH' tc₀
    rw [hBx] at h1
    exact hasTyA_of_tyConvA h1 tyXC.symm
  -- each redex converts to its minor at the left's type: irrelevance moves the major to the constructor,
  -- where ι fires
  have cL : ConvA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) x)
      mn (foldAppsA mot ([] ++ [x])) := by
    have c1 := ConvA.app Γ _ _ x (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ [])) _ B _ _
      (.refl Γ _ _ tH) (.irr Γ _ x _ tQ0 tx tc₀) hBty (by rw [hBx]; exact tLc)
    rw [hBx] at c1
    exact .trans _ _ _ _ _ c1 (.iota Γ _ _ _ (iotaRelA_of hnl hfn (hshU _ _) hιc) tLc tmn)
  have cR : ConvA E (iotaIfaceA E) n Γ
      (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) x') mn'
      (foldAppsA mot ([] ++ [x])) := by
    have c1 := ConvA.app Γ _ _ x' (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ [])) _ B _ _
      (.refl Γ _ _ tH') (.irr Γ _ x' _ tQ0 tx' tc₀) hBty
      (by rw [hBx]; exact hasTyA_of_tyConvA tRc tyX'X.symm)
    rw [hBx] at c1
    exact .trans _ _ _ _ _ (convA_of_tyConvA c1 tyX'X) (.iota Γ _ _ _ (iotaRelA_of hnl' hfn' (hshU _ _) hιc') tRc tmn')
  -- the head steps: K-unit, or ι when the major is the constructor (to the minor all the same)
  have sL : TyHRedA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) x)
      mn (foldAppsA mot ([] ++ [x])) := by
    cases hix : iotaFnA E (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) x) with
    | none =>
        exact .kunit Γ _ x mn _ (recAtMajorA_recSpine hrm rec.hcls hct ls _ hlenP) huM hfn hix cL tmn
    | some e' =>
        have he : e' = mn := iotaFnA_unitGroupA hfresh hlay hcls hpre hgc hnf hprel hl hmin1
          (by rw [foldAppsA_snoc]; exact hix)
        subst he
        exact .iota Γ _ _ _ (iotaRelA_of hnl hfn (hshU _ _) hix) tLx tmn
  have sR : TyHRedA E (iotaIfaceA E) n Γ
      (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) x') mn'
      (foldAppsA mot ([] ++ [x])) := by
    cases hix : iotaFnA E (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) x') with
    | none =>
        exact .kunit Γ _ x' mn' _ (recAtMajorA_recSpine hrm rec.hcls hct ls' _ hlenP') huM' hfn' hix cR tmn'
    | some e' =>
        have he : e' = mn' := iotaFnA_unitGroupA hfresh hlay hcls hpre hgc hnf hprel' hls' hmin1'
          (by rw [foldAppsA_snoc]; exact hix)
        subst he
        exact .iota Γ _ _ _ (iotaRelA_of hnl' hfn' (hshU _ _) hix) tRx tmn'
  have h2 := LRRelA_expand_right hE hI ⟨⟨tRx⟩, ⟨sR⟩⟩ (LRRelA_expand_left hE hI ⟨⟨tLx⟩, ⟨sL⟩⟩ hred)
  rw [recTelA hEL hfm rec hl, happ] at hC
  injection hC with hC
  subst hC
  rw [show qs ++ ([mot] ++ [mn] ++ [] ++ [x]) = qs ++ [mot] ++ [mn] ++ [x] by simp,
    show qs' ++ ([mot'] ++ [mn'] ++ [] ++ [x']) = qs' ++ [mot'] ++ [mn'] ++ [x'] by simp,
    foldAppsA_snoc (.const _ ls) (qs ++ [mot] ++ [mn]) x, foldAppsA_snoc (.const _ ls') (qs' ++ [mot'] ++ [mn']) x']
  exact h2

end UnitClause

/-! ## (7'') W-1 (c): THE STRUCT GROUP

The struct arm fires at a recursor whose type passes `structGroupA`. At a group's recursor the test
holds only at a struct group: one constructor, no index, a `Prop` family, a motive universe not zero,
and a constructor whose fields are all PROOFS — plain fields at sorts zero at every valuation, at
least one (`structShape_of_structGroupA`). -/

section StructShape

/-- what the struct test reads of the minor's domain, when it holds: a Π whose binders are all
    annotated with sorts zero at every valuation. -/
theorem structGroupA_true_minor {r : Nat} {m : CheckedMemberA} (h : structGroupA r m = true) :
    ∃ D uD Dm um rest, (piDomListA m.mtypeA).reverse = (D, uD) :: (Dm, um) :: rest ∧
      (∃ A u B v, Dm = .pi A u B v) ∧ (piDomListA Dm).all (fun p => levelIsZero p.2) = true := by
  unfold structGroupA at h
  split at h
  next D uD Dm um Dmot umot rest hL =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨_, h4⟩ := h
    refine ⟨D, uD, Dm, um, (Dmot, umot) :: rest, hL, ?_⟩
    split at h4
    next A u B v => exact ⟨⟨A, u, B, v, rfl⟩, h4⟩
    next => exact absurd h4 (by decide)
  next => exact absurd h (by decide)

theorem levelIsZero_frecLevelA (w : Level) : (ds : List (ExprA × Level)) →
    levelIsZero (frecLevelA w ds) = levelIsZero w
  | [] => rfl
  | (_, _) :: ds => levelIsZero_frecLevelA w ds

/-- a minor premise whose binders are all annotated with sorts zero at every valuation, the motive's
    sort not: every field is plain, at such a sort (a recursive field's induction hypothesis is
    annotated with the motive's sort, through its inner binders at a function-recursive one). -/
theorem minorFieldsA_proofs (f c : Nat) (ls : List Level) (wF wM : Level) (res : List ExprA)
    (hwM : levelIsZero wM = false) :
    (fs : List FieldA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) → (σ : SubstA) →
    (piDomListA (minorFieldsA f c ls wF wM pl mot fl σ fs res).1).all (fun p => levelIsZero p.2) = true →
    ∀ fld ∈ fs, ∃ D u, fld = .plain D u ∧ levelIsZero u = true
  | [], _, _, _, _, _, fld, hfld => absurd hfld (List.not_mem_nil fld)
  | .plain D u :: fs, pl, mot, fl, σ, h, fld, hfld => by
      simp only [minorFieldsA, piDomListA, List.all_cons, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hfld with rfl | hfld'
      · exact ⟨D, u, rfl, h.1⟩
      · exact minorFieldsA_proofs f c ls wF wM res hwM fs _ _ _ _ h.2 fld hfld'
  | .drec _ :: fs, pl, mot, fl, σ, h, _, _ | .drecD _ _ :: fs, pl, mot, fl, σ, h, _, _ => by
      simp only [minorFieldsA, piDomListA, List.all_cons, Bool.and_eq_true] at h
      rw [hwM] at h
      exact absurd h.2.1 (by decide)
  | .frec B uB Bs idx :: fs, pl, mot, fl, σ, h, _, _ => by
      simp only [minorFieldsA, piDomListA, List.all_cons, Bool.and_eq_true] at h
      have h2 := h.2.1
      rw [frecIHA_snd, levelIsZero_frecLevelA, hwM] at h2
      exact absurd h2 (by decide)

/-- W-1 (c), THE SOUNDNESS OF THE STRUCT TEST at a group's recursor: one constructor, no index, a `Prop`
    family, a motive universe not zero, and a constructor whose fields are all PROOFS — plain, at sorts
    zero at every valuation — at least one of them. -/
theorem structShape_of_structGroupA {I : IotaIfaceA} {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)} (rec : GroupRecA I E₀ f fm fv cs)
    (hst : structGroupA (f + 1 + cs.length) rec.member = true) :
    cs.length = 1 ∧ fv.indices = [] ∧ levelIsZero fv.sort = true ∧
      levelIsZero (rec.elim.motiveLevel fm.arity) = false ∧
      ∀ cd ∈ cs.reverse.map GroupCtorA.minorData, cd.2.1 ≠ [] ∧
        ∀ fld ∈ cd.2.1, ∃ D u, fld = .plain D u ∧ levelIsZero u = true := by
  obtain ⟨hcs, hni, hwM⟩ := structGroupA_groupRecA_true rec hst
  obtain ⟨D, uD, Dm, um, Dmot, umot, rest, hL, _, hz, _⟩ := structGroupA_true_inv hst
  obtain ⟨D₁, uD₁, Dm₁, um₁, rest₁, hL₁, ⟨A, u, B, v, hpi⟩, hall⟩ := structGroupA_true_minor hst
  have hst' : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst'
  have hcds : (cs.reverse.map GroupCtorA.minorData).length = 1 := by
    rw [List.length_map, List.length_reverse, hcs]
  obtain ⟨cd, hcd⟩ : ∃ cd, cs.reverse.map GroupCtorA.minorData = [cd] := by
    match cs.reverse.map GroupCtorA.minorData, hcds with
    | [cd], _ => exact ⟨cd, rfl⟩
  have hL₀ : (piDomListA rec.member.mtypeA).reverse =
      (liftA 0 2 (famLocalsA f (canonLevelsA fm.arity) fv.params.length 0), fv.sort) ::
        (liftA 0 0 (minorTyA f (canonLevelsA fm.arity) fv.sort (rec.elim.motiveLevel fm.arity)
            fv.params.length cd).1,
          (minorTyA f (canonLevelsA fm.arity) fv.sort (rec.elim.motiveLevel fm.arity) fv.params.length cd).2) ::
        (motTyA f (canonLevelsA fm.arity) fv.params [] fv.sort (rec.elim.motiveLevel fm.arity)) ::
          fv.params.reverse := by
    rw [hst', piDomListA_recTypeA_reverse, hcd, hni]
    simp [minorDomsA, liftDomsA]
  rw [hL₀] at hL hL₁
  injection hL with h1 _
  injection h1 with _ huD
  injection hL₁ with _ hL₁'
  injection hL₁' with h2 _
  injection h2 with hDm _
  rw [liftA_zero] at hDm
  refine ⟨hcs, hni, huD ▸ hz, hwM, ?_⟩
  intro cd' hcd'
  rw [hcd] at hcd'
  cases List.mem_singleton.1 hcd'
  rw [← hDm] at hpi hall
  unfold minorTyA at hpi hall
  refine ⟨fun hnil => ?_, minorFieldsA_proofs _ _ _ _ _ _ hwM _ _ _ _ _ hall⟩
  rw [hnil] at hpi
  exact minorFieldsA_nil_not_pi _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpi

end StructShape

/-! ## (7''') W-1 (c): THE RECURSORS' CLAUSE AT A STRUCT GROUP

At a struct group every full application of the recursor steps to its minor applied to the major's
projections (K-struct, or ι when the major is the constructor). The projections are typed along the
fields (Lemma P, `structProjsA_substTyA`); the two sides' projections are a valid pair along the
minor's domain because every field is a proof (Lemma V, `validSubstA_propTel`: the fundamental theorem
across the two level lists types the right's projections at the left's domains, where proofs are related
by `irr`); and the minor's conclusion at the projections is the redex's type (the family application is
a proposition, where the major is related to the constructor at its projections). `recStructAppsA` is
the clause at one world; its two height thresholds (`hVP`, `hVF`) are computed where the clause is
assembled. -/

section Tel
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- W-1 (c): A CONSTRUCTOR APPLIED TO ITS PARAMETERS AND PLAIN FIELDS IS TYPED at the family application:
    the parameters pointwise along the constructor's type, the fields a typed substitution over the
    fields' telescope (whatever tail below the parameters). -/
theorem ctorApp_hasTyA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Δ : LCtxA} (hΔ : CtxWfA E I n Δ) {c f : Nat} {lsC : List Level} {wF : Level} {Tc : ExprA}
    (hc : HasTyA E I n Δ (.const c lsC) Tc) {ps : List ExprA} (hPF : ConvArgsA E I n Δ Tc ps ps)
    {ds : List (ExprA × Level)} {Θ : LCtxA} {τ : SubstA}
    (happ : applyTelA ps Tc = some (ctorFieldsA f lsC wF ps (consListA ps τ) (ds.map plainA) []).1)
    {as : List ExprA} (hlen : as.length = ds.length)
    (hσ : SubstTyA E I n Δ (consListA as (consListA ps τ)) (telCtxA ds ++ Θ)) :
    Nonempty (HasTyA E I n Δ (foldAppsA (.const c lsC) (ps ++ as)) (foldAppsA (.const f lsC) ps)) := by
  have hF := convArgsA_ctorFieldsA (E := E) (I := I) (n := n) f lsC wF [] ds Θ ps (consListA ps τ)
    (consListA ps τ) as as hlen hlen (convSubstA_refl hσ)
  have hJ := convArgsA_append hPF happ hF
  have hC : applyTelA (ps ++ as) Tc = some (foldAppsA (.const f lsC) ps) := by
    rw [applyTelA_append, happ, Option.some_bind, applyTelA_ctorFieldsA_plain f lsC wF [] ds ps _ as hlen]
    simp only [ctorFieldsA, List.map_nil, List.append_nil]
  obtain ⟨hcv⟩ := convA_spine hE hI hR hIS hΔ hJ ⟨.refl _ _ _ hc⟩ _ hC
  exact ⟨convA_hasTy_left hE hI hR hIS hΔ hcv⟩

/-- a struct constructor's minor premise at the parameters `qs` and any motive `M`: the Π-telescope over
    the fields' substituted domains, at `M` applied to the constructor at the lifted parameters and the
    field locals. -/
theorem minorTyA_plain_eq (f c : Nat) (ls : List Level) (wF wM : Level) (ds : List (ExprA × Level))
    (qs : List ExprA) (np : Nat) (hnp : qs.length = np) (M : ExprA) :
    substA (SubstA.cons M (consListA qs SubstA.id)) (minorTyA f ls wF wM np (c, ds.map plainA, [])).1 =
      (piTelA (substTelA (consListA qs SubstA.id) ds)
        (.app (liftNA ds.length M) (foldAppsA (.const c ls) (qs.map (liftNA ds.length) ++ paramLocalsA ds.length)))
        wM).1 := by
  subst hnp
  have hσ : (fun i => substA (SubstA.cons M (consListA qs SubstA.id)) (SubstA.id.shift1 i)) =
      consListA qs SubstA.id := by
    funext i
    show substA (SubstA.cons M (consListA qs SubstA.id)) (liftA 0 1 (SubstA.id i)) = consListA qs SubstA.id i
    rw [substA_cons_liftA]
    rfl
  have hpl : ((paramLocalsA qs.length).map (liftA 0 1)).map (substA (SubstA.cons M (consListA qs SubstA.id))) =
      qs := by
    rw [map_substA_cons_liftA, paramLocalsA_consListA]
  simp only [minorTyA]
  rw [substA_minorFieldsA, hpl, hσ, minorFieldsA_plain_eq]
  simp only [minorFieldsA, List.map_nil, List.nil_append, substA_bvar, SubstA.cons_zero]
  rfl

/-- W-1 (c), THE SELECTOR IS TYPED at the minor premise of its field's motive `λ (_ : S). F`: under the
    fields' binders the selected field's own type is, by proof irrelevance on the fields before it
    (`convSubstA_propExtA`), the field's domain `F` at the earlier fields' values, which the motive's body
    reads back (β at the constructor application `K` under the binders). -/
theorem fieldSelA_hasTyA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ Θ : LCtxA} (hΓ : CtxWfA E I n Γ) {σq : SubstA} (hσq : SubstTyA E I n Γ σq Θ)
    {dI : List (ExprA × Level)} (tdI : TelTyA E I n Θ dI) (hzI : ∀ d ∈ dI, eqN d.2 .zero)
    {done rest : List (ExprA × Level)} {D : ExprA} {u : Level} (hsplit : done ++ (D, u) :: rest = dI)
    {pre : List ExprA} (hpre : pre.length = done.length)
    (hσp : SubstTyA E I n Γ (consListA pre σq) (telCtxA done ++ Θ))
    {S : ExprA} {wF : Level} (hS : HasTyA E I n Γ S (.sort wF))
    {K : ExprA} (hK : HasTyA E I n (telCtxA (substTelA σq dI) ++ Γ) K (liftNA dI.length S)) :
    Nonempty (HasTyA E I n Γ (fieldSelA (substTelA σq dI) done.length)
      (piTelA (substTelA σq dI)
        (.app (liftNA dI.length (.lam S wF (liftA 0 1 (substA (consListA pre σq) D)))) K) .zero).1) := by
  subst hsplit
  -- the telescope's pieces
  obtain ⟨tdone, trest⟩ := TelTyA.split done tdI
  have hD : HasTyA E I n (telCtxA done ++ Θ) D (.sort u) := by
    cases trest with
    | cons _ _ _ _ hD _ => exact hD
  have hzu : eqN u .zero := hzI (D, u) (List.mem_append_right _ (List.mem_cons_self _ _))
  have hzdone : ∀ d ∈ done, eqN d.2 .zero := fun d hd => hzI d (List.mem_append_left _ hd)
  generalize hm : (done ++ (D, u) :: rest).length = m at hK ⊢
  have hm' : m = done.length + (rest.length + 1) := by
    rw [← hm, List.length_append, List.length_cons]
  have tFs := (TelTyA.subst hE hI hR hIS tdI hσq).1
  have hΓm : CtxWfA E I n (telCtxA (substTelA σq (done ++ (D, u) :: rest)) ++ Γ) := ctxWfA_telCtx tFs hΓ
  have hlenFs : (telCtxA (substTelA σq (done ++ (D, u) :: rest))).length = m := by
    rw [telCtxA_length, substTelA_length, hm]
  -- the field's domain at the earlier values, and the motive
  have hF : HasTyA E I n Γ (substA (consListA pre σq) D) (.sort u) := hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσp hD
  have hFw : HasTyA E I n (.assumption S :: Γ) (liftA 0 1 (substA (consListA pre σq) D)) (.sort .zero) :=
    hasTyA_retype_sort (hasTyWeakenA hE hI (.assumption S) (Nat.zero_le _) hF) hzu
  -- under the fields' binders
  have hFm := hasTyA_liftN hE hI hF (telCtxA (substTelA σq (done ++ (D, u) :: rest)))
  have hSm := hasTyA_liftN hE hI hS (telCtxA (substTelA σq (done ++ (D, u) :: rest)))
  rw [hlenFs, liftNA_sort] at hFm hSm
  generalize hΓmdef : telCtxA (substTelA σq (done ++ (D, u) :: rest)) ++ Γ = Γm at hΓm hFm hSm hK
  generalize hFdef : substA (consListA pre σq) D = F at hF hFw hFm ⊢
  have elam : liftNA m (.lam S wF (liftA 0 1 F)) = .lam (liftNA m S) wF (liftA 1 m (liftA 0 1 F)) := by
    rw [liftNA_eq, liftNA_eq]; rfl
  have ebody : liftA 1 m (liftA 0 1 F) = liftA 0 1 (liftNA m F) := by
    rw [liftNA_eq, liftA_liftA_permute 1 m 0 0 (Nat.le_refl 0) F]
  have hbody : HasTyA E I n (.assumption (liftNA m S) :: Γm) (liftA 1 m (liftA 0 1 F)) (.sort .zero) := by
    rw [ebody]
    exact hasTyA_retype_sort (hasTyWeakenA hE hI (.assumption (liftNA m S)) (Nat.zero_le _) hFm) hzu
  have hred : HasTyA E I n Γm (instantiate0A K (liftA 1 m (liftA 0 1 F))) (.sort .zero) := by
    rw [ebody, instantiate0A_liftA_one]
    exact hasTyA_retype_sort hFm hzu
  have hMm : HasTyA E I n Γm (liftNA m (.lam S wF (liftA 0 1 F))) (.pi (liftNA m S) wF (.sort .zero) (.succ .zero)) := by
    rw [elam]
    exact .lam _ _ _ _ _ _ hSm (.sort _ _) hbody
  have hB : HasTyA E I n Γm (.app (liftNA m (.lam S wF (liftA 0 1 F))) K) (.sort .zero) :=
    .app Γm _ K (liftNA m S) (.sort .zero) wF (.succ .zero) (.succ .zero) (.sort _ _) (.sort _ _) hMm hK
  have cβ : ConvA E I n Γm (.app (liftNA m (.lam S wF (liftA 0 1 F))) K) (liftNA m F) (.sort .zero) := by
    have h := ConvA.beta Γm (liftNA m S) wF (liftA 1 m (liftA 0 1 F)) K (.sort .zero) hSm hbody hK hred
    have e2 : instantiate0A K (liftA 1 m (liftA 0 1 F)) = liftNA m F := by rw [ebody, instantiate0A_liftA_one]
    rw [e2] at h
    rw [elam]
    exact h
  -- the selected field's variable, at its own type under the fields' binders
  have hFs : substTelA σq (done ++ (D, u) :: rest) = substTelA σq done ++
      (substA (upNA done.length σq) D, u) :: substTelA (upNA done.length σq).up rest := by
    rw [substTelA_append]; rfl
  have hR'len : (substTelA (upNA done.length σq).up rest).length = rest.length := substTelA_length _ _
  have hΓm' : Γm = telCtxA ((substA (upNA done.length σq) D, u) :: substTelA (upNA done.length σq).up rest) ++
      (telCtxA (substTelA σq done) ++ Γ) := by
    rw [← hΓmdef, hFs, telCtxA_append, List.append_assoc]
  have hup := (TelTyA.subst hE hI hR hIS tdone hσq).2
  have hτ₁ := substTyA_liftN hE hI hup
    (telCtxA ((substA (upNA done.length σq) D, u) :: substTelA (upNA done.length σq).up rest))
  rw [← hΓm', telCtxA_length, List.length_cons, hR'len] at hτ₁
  have hτ₂ := substTyA_liftN hE hI hσp (telCtxA (substTelA σq (done ++ (D, u) :: rest)))
  rw [hlenFs, hΓmdef] at hτ₂
  have hPE := propExtA_telTyA (Θ := Θ) .base tdone hzdone
  have hCS := convSubstA_propExtA hE hI hR hIS hPE hτ₁ hτ₂ (fun j A hj _ => by
    obtain ⟨p, rfl⟩ : ∃ p, j = p + done.length := ⟨j - done.length, by omega⟩
    show liftNA (rest.length + 1) (upNA done.length σq (p + done.length)) =
      liftNA m (consListA pre σq (p + done.length))
    rw [upNA_add, liftNA_add, ← hpre, consListA_add, hpre, hm'])
  have hQ := hasTyA_func hE hI (iotaRecHeadTypedA_of hR) hIS hCS hD
  have e1 : substA (fun j => liftNA m (consListA pre σq j)) D = liftNA m F := by
    rw [← hFdef, liftNA_substA]
  rw [e1] at hQ
  have hnat := hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hτ₁ hD
  have hlook : lookupTypeA Γm rest.length =
      some (substA (fun j => liftNA (rest.length + 1) (upNA done.length σq j)) D) := by
    rw [hΓm', ← liftNA_substA, liftNA_eq, ← hR'len]
    exact lookupTypeA_telCtxA_head _ u _ _
  have hv : HasTyA E I n Γm (.bvar rest.length) (.app (liftNA m (.lam S wF (liftA 0 1 F))) K) :=
    .conv Γm _ _ _ u .zero (.bvar Γm _ _ u hlook hnat) hnat hzu hB
      (.trans _ _ _ _ _ (convA_of_tyConvA hQ (tyConvA_sorts Γm hzu)) (.symm _ _ _ _ cβ))
  subst hΓmdef
  have hsel : fieldSelA (substTelA σq (done ++ (D, u) :: rest)) done.length =
      lamTelA (substTelA σq (done ++ (D, u) :: rest)) (.bvar rest.length) := by
    unfold fieldSelA
    rw [substTelA_length, hm]
    congr 2
    omega
  rw [hsel]
  exact ⟨hasTyA_lamTelA tFs hB hv⟩

/-- W-1 (c), THE PROJECTIONS WALK THE MINOR'S DOMAIN: when each projection is typed at its field's domain
    once the earlier ones are (`hstep`), the projections of `y` along the minor's field telescope form a
    typed substitution over the fields, each field's domain at the earlier projections. -/
theorem structProjsA_substTy {Γ Θ : LCtxA} {σq : SubstA} {dI : List (ExprA × Level)}
    (r : Nat) (ls₀ : List Level) (ps : List ExprA) (S : ExprA) (uS : Level) (Fs : List (ExprA × Level))
    (y Body : ExprA) (w : Level)
    (hstep : ∀ (done : List (ExprA × Level)) (D : ExprA) (u : Level) (rest : List (ExprA × Level))
      (pre : List ExprA), done ++ (D, u) :: rest = dI → pre.length = done.length →
      Nonempty (SubstTyA E I n Γ (consListA pre σq) (telCtxA done ++ Θ)) →
      Nonempty (HasTyA E I n Γ (structProjA r ls₀ ps S uS Fs y pre.length (substA (consListA pre σq) D))
        (substA (consListA pre σq) D))) :
    (rest done : List (ExprA × Level)) → (pre : List ExprA) → done ++ rest = dI → pre.length = done.length →
    Nonempty (SubstTyA E I n Γ (consListA pre σq) (telCtxA done ++ Θ)) →
    Nonempty (SubstTyA E I n Γ
      (consListA (pre ++ structProjsA r ls₀ ps S uS Fs y rest.length pre.length
        (substA (consListA pre SubstA.id) (piTelA (substTelA (upNA pre.length σq) rest) Body w).1)) σq)
      (telCtxA dI ++ Θ))
  | [], done, pre, hsp, _, h => by
      rw [List.append_nil] at hsp
      subst hsp
      simp only [List.length_nil, structProjsA, List.append_nil]
      exact h
  | (D, u) :: rest, done, pre, hsp, hl, h => by
      obtain ⟨hπ⟩ := hstep done D u rest pre hsp hl h
      obtain ⟨h₀⟩ := h
      have h' : SubstTyA E I n Γ
          (consListA (pre ++ [structProjA r ls₀ ps S uS Fs y pre.length (substA (consListA pre σq) D)]) σq)
          (telCtxA (done ++ [(D, u)]) ++ Θ) := by
        rw [consListA_snoc, telCtxA_snoc]
        exact substTyA_cons h₀ hπ
      have ih := structProjsA_substTy r ls₀ ps S uS Fs y Body w hstep rest (done ++ [(D, u)])
        (pre ++ [structProjA r ls₀ ps S uS Fs y pre.length (substA (consListA pre σq) D)])
        (by rw [List.append_assoc]; exact hsp) (by simp [hl]) ⟨h'⟩
      rw [List.length_append, List.length_singleton, upNA_succ] at ih
      have eT : substA (consListA pre SubstA.id) (piTelA (substTelA (upNA pre.length σq) ((D, u) :: rest)) Body w).1 =
          .pi (substA (consListA pre σq) D) u
            (substA (consListA pre SubstA.id).up (piTelA (substTelA (upNA pre.length σq).up rest) Body w).1)
            (piTelA (substTelA (upNA pre.length σq).up rest) Body w).2 := by
        simp only [substTelA, piTelA, substA_pi]
        rw [substA_consListA_upNA]
      rw [eT]
      simp only [List.length_cons, structProjsA]
      rw [instantiate0A_consListA_up]
      rw [List.append_assoc, List.singleton_append] at ih
      exact ih

/-- the motive's type at the parameters, at a family without indices. -/
theorem substA_motTyA_noIdx (f : Nat) (ls : List Level) (params : List (ExprA × Level)) (wF wM : Level)
    (qs : List ExprA) (hqs : qs.length = params.length) :
    substA (consListA qs SubstA.id) (motTyA f ls params [] wF wM).1 =
      .pi (foldAppsA (.const f ls) qs) wF (.sort wM) (.succ wM) := by
  have hfun : (substA (consListA qs SubstA.id) ∘ liftA 0 0) = substA (consListA qs SubstA.id) :=
    funext fun e => by simp only [Function.comp, liftA_zero]
  simp only [motTyA, piTelA, famLocalsA, substA_pi, substA_foldAppsA, substA_const, List.map_append,
    List.map_map, paramLocalsA, List.map_nil, List.append_nil, substA_sort, List.length_nil, hfun]
  rw [← hqs, paramLocalsA_consListA]

/-- W-1 (c), A PROJECTION IS TYPED at its field's domain, the earlier fields at their projections: the
    recursor at the zero motive level over the parameters, the motive `λ (_ : S). F`, the field's selector
    (`fieldSelA_hasTyA`) and the major; its type `(λ (_ : S). F) y` is `F` by β. -/
theorem structProjA_hasTyA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {r f c : Nat} {ls₀ lsF : List Level} {wF : Level}
    {pI dI : List (ExprA × Level)}
    (hrc : HasTyA E I n Γ (.const r ls₀)
      (piTelA (recDomsA f lsF pI [] wF .zero [(c, dI.map plainA, [])]) (recBodyA 0 1) .zero).1)
    {qs : List ExprA} (hqs : qs.length = pI.length)
    (hpar : ConvArgsA E I n Γ (piTelA pI (.sort .zero) .zero).1 qs qs)
    (hσq : SubstTyA E I n Γ (consListA qs SubstA.id) (telCtxA pI))
    (tdI : TelTyA E I n (telCtxA pI) dI) (hzI : ∀ d ∈ dI, eqN d.2 .zero)
    (hS : HasTyA E I n Γ (foldAppsA (.const f lsF) qs) (.sort wF))
    (hK : HasTyA E I n (telCtxA (substTelA (consListA qs SubstA.id) dI) ++ Γ)
      (foldAppsA (.const c lsF) (qs.map (liftNA dI.length) ++ paramLocalsA dI.length))
      (liftNA dI.length (foldAppsA (.const f lsF) qs)))
    {y : ExprA} (hy : HasTyA E I n Γ y (foldAppsA (.const f lsF) qs))
    {done rest : List (ExprA × Level)} {D : ExprA} {u : Level} (hsplit : done ++ (D, u) :: rest = dI)
    {pre : List ExprA} (hpre : pre.length = done.length)
    (hσp : SubstTyA E I n Γ (consListA pre (consListA qs SubstA.id)) (telCtxA done ++ telCtxA pI)) :
    Nonempty (HasTyA E I n Γ
      (structProjA r ls₀ qs (foldAppsA (.const f lsF) qs) wF (substTelA (consListA qs SubstA.id) dI) y
        pre.length (substA (consListA pre (consListA qs SubstA.id)) D))
      (substA (consListA pre (consListA qs SubstA.id)) D)) := by
  -- the field's domain
  have hD : HasTyA E I n (telCtxA done ++ telCtxA pI) D (.sort u) := by
    subst hsplit
    obtain ⟨_, trest⟩ := TelTyA.split done tdI
    cases trest with
    | cons _ _ _ _ hD _ => exact hD
  have hzu : eqN u .zero :=
    hzI (D, u) (by rw [← hsplit]; exact List.mem_append_right _ (List.mem_cons_self _ _))
  have hF := hasTyA_substA hE hI (iotaRecHeadTypedA_of hR) hIS hσp hD
  -- the selector at its minor premise
  obtain ⟨hsel⟩ := fieldSelA_hasTyA hE hI hR hIS hΓ hσq tdI hzI hsplit hpre hσp hS hK
  rw [← hpre] at hsel
  -- the motive
  have hFw : HasTyA E I n (.assumption (foldAppsA (.const f lsF) qs) :: Γ)
      (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D)) (.sort .zero) :=
    hasTyA_retype_sort (hasTyWeakenA hE hI (.assumption _) (Nat.zero_le _) hF) hzu
  have hM : HasTyA E I n Γ (.lam (foldAppsA (.const f lsF) qs) wF
        (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D)))
      (.pi (foldAppsA (.const f lsF) qs) wF (.sort .zero) (.succ .zero)) :=
    .lam _ _ _ _ _ _ hS (.sort _ _) hFw
  -- the recursor's arguments, pointwise
  have hmot : Nonempty (ConvA E I n Γ
      (.lam (foldAppsA (.const f lsF) qs) wF (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D)))
      (.lam (foldAppsA (.const f lsF) qs) wF (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D)))
      (substA (consListA qs SubstA.id) (motTyA f lsF pI [] wF .zero).1)) := by
    rw [substA_motTyA_noIdx f lsF pI wF .zero qs hqs]
    exact ⟨.refl _ _ _ hM⟩
  have hmin : ∀ (i : Nat)
      (hi : i < [fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length].length)
      (hi' : i < [fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length].length)
      (hc : i < [((c, dI.map plainA, []) : MinorDataA)].length),
      Nonempty (ConvA E I n Γ [fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length][i]
        [fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length][i]
        (substA (SubstA.cons (.lam (foldAppsA (.const f lsF) qs) wF
            (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D))) (consListA qs SubstA.id))
          (minorTyA f lsF wF .zero pI.length [((c, dI.map plainA, []) : MinorDataA)][i]).1)) := by
    intro i hi _ _
    obtain rfl : i = 0 := by simpa using hi
    show Nonempty (ConvA E I n Γ (fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length)
      (fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length)
      (substA (SubstA.cons (.lam (foldAppsA (.const f lsF) qs) wF
          (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D))) (consListA qs SubstA.id))
        (minorTyA f lsF wF .zero pI.length (c, dI.map plainA, [])).1))
    rw [minorTyA_plain_eq f c lsF wF .zero dI qs pI.length hqs]
    exact ⟨.refl _ _ _ hsel⟩
  have hJ := recArgsJoinC (E := E) (I := I) (n := n) (Γ := Γ) f lsF pI [] wF .zero .zero
    [((c, dI.map plainA, []) : MinorDataA)] (qs := qs) (qs' := qs)
    (x := y) (x' := y) (is := []) (is' := []) hqs rfl rfl rfl hpar hmot hmin (.nil _)
    ⟨.refl _ _ _ (by rw [List.append_nil]; exact hy)⟩
  -- the type reached
  obtain ⟨B, hB, hBx⟩ := applyTelA_recPrefixA f lsF pI [] wF .zero .zero [((c, dI.map plainA, []) : MinorDataA)] qs
    (.lam (foldAppsA (.const f lsF) qs) wF (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D)))
    [fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length] [] hqs rfl rfl
  simp only [List.length_nil, List.length_singleton] at hB
  have happ : applyTelA (qs ++ ([.lam (foldAppsA (.const f lsF) qs) wF
        (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D))] ++
        [fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length] ++ [] ++ [y]))
      (piTelA (recDomsA f lsF pI [] wF .zero [((c, dI.map plainA, []) : MinorDataA)]) (recBodyA 0 1) .zero).1 =
      some (.app (.lam (foldAppsA (.const f lsF) qs) wF
        (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D))) y) := by
    rw [show ∀ (a b : ExprA), qs ++ ([a] ++ [b] ++ [] ++ [y]) = qs ++ ([a] ++ [b] ++ []) ++ [y] from
      fun _ _ => by simp, applyTelA_append, hB]
    show some (instantiate0A y B) = _
    rw [hBx]
    rfl
  obtain ⟨hcv⟩ := convA_spine hE hI hR hIS hΓ hJ ⟨.refl _ _ _ hrc⟩ _ happ
  have ht := convA_hasTy_left hE hI hR hIS hΓ hcv
  -- β
  have hred : HasTyA E I n Γ (instantiate0A y (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D)))
      (instantiate0A y (.sort .zero)) := by
    rw [instantiate0A_liftA_one]
    exact hasTyA_retype_sort hF hzu
  have cβ := ConvA.beta Γ (foldAppsA (.const f lsF) qs) wF
    (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D)) y (.sort .zero) hS hFw hy hred
  rw [instantiate0A_liftA_one] at cβ
  have hMy : HasTyA E I n Γ (.app (.lam (foldAppsA (.const f lsF) qs) wF
      (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D))) y) (.sort .zero) :=
    .app Γ _ y _ (.sort .zero) wF (.succ .zero) (.succ .zero) (.sort _ _) (.sort _ _) hM hy
  have e : qs ++ ([ExprA.lam (foldAppsA (.const f lsF) qs) wF
        (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D))] ++
        [fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length] ++ [] ++ [y]) =
      qs ++ [.lam (foldAppsA (.const f lsF) qs) wF
        (liftA 0 1 (substA (consListA pre (consListA qs SubstA.id)) D)),
        fieldSelA (substTelA (consListA qs SubstA.id) dI) pre.length, y] := by simp
  rw [e] at ht
  exact ⟨.conv Γ _ _ _ .zero .zero ht hMy (eqNA_refl _) (hasTyA_retype_sort hF hzu) cβ⟩

/-- W-1 (c), THE PROJECTIONS ARE TYPED: the projections of a major `y` along the minor's domain (any body)
    form a typed substitution over the fields' telescope after the parameters'. -/
theorem structProjsA_substTyA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {r f c : Nat} {ls₀ lsF : List Level} {wF : Level}
    {pI dI : List (ExprA × Level)}
    (hrc : HasTyA E I n Γ (.const r ls₀)
      (piTelA (recDomsA f lsF pI [] wF .zero [(c, dI.map plainA, [])]) (recBodyA 0 1) .zero).1)
    {qs : List ExprA} (hqs : qs.length = pI.length)
    (hpar : ConvArgsA E I n Γ (piTelA pI (.sort .zero) .zero).1 qs qs)
    (hσq : SubstTyA E I n Γ (consListA qs SubstA.id) (telCtxA pI))
    (tdI : TelTyA E I n (telCtxA pI) dI) (hzI : ∀ d ∈ dI, eqN d.2 .zero)
    (hS : HasTyA E I n Γ (foldAppsA (.const f lsF) qs) (.sort wF))
    (hK : HasTyA E I n (telCtxA (substTelA (consListA qs SubstA.id) dI) ++ Γ)
      (foldAppsA (.const c lsF) (qs.map (liftNA dI.length) ++ paramLocalsA dI.length))
      (liftNA dI.length (foldAppsA (.const f lsF) qs)))
    {y : ExprA} (hy : HasTyA E I n Γ y (foldAppsA (.const f lsF) qs)) (Body : ExprA) (w : Level) :
    Nonempty (SubstTyA E I n Γ
      (consListA (structProjsA r ls₀ qs (foldAppsA (.const f lsF) qs) wF (substTelA (consListA qs SubstA.id) dI)
        y dI.length 0 (piTelA (substTelA (consListA qs SubstA.id) dI) Body w).1) (consListA qs SubstA.id))
      (telCtxA dI ++ telCtxA pI)) := by
  have h := structProjsA_substTy (E := E) (I := I) (n := n) (Γ := Γ) (Θ := telCtxA pI)
    (σq := consListA qs SubstA.id) (dI := dI) r ls₀ qs (foldAppsA (.const f lsF) qs) wF
    (substTelA (consListA qs SubstA.id) dI) y Body w
    (fun done D u rest pre hsp hl ⟨hσp⟩ =>
      structProjA_hasTyA hE hI hR hIS hΓ hrc hqs hpar hσq tdI hzI hS hK hy hsp hl hσp)
    dI [] [] rfl rfl ⟨by simpa using hσq⟩
  have e1 : substA (consListA ([] : List ExprA) SubstA.id)
      (piTelA (substTelA (upNA ([] : List ExprA).length (consListA qs SubstA.id)) dI) Body w).1 =
      (piTelA (substTelA (consListA qs SubstA.id) dI) Body w).1 := substA_id _
  rw [e1] at h
  simpa using h

/-- two proofs of a valid proposition are related at it (`irr`; the `irr` arm's construction). -/
theorem LRRelA_of_propValid {ρ₀ : Nat → Nat} {k : Nat} {Γ : LCtxA} {P p q : ExprA}
    (hPV : PropValidA E I n Γ P) (hP : HasTyA E I n Γ P (.sort .zero)) (hp : HasTyA E I n Γ p P)
    (hq : HasTyA E I n Γ q P) : LRRelA E I n ρ₀ k Γ P p q := by
  obtain ⟨N, hN, hNt⟩ := hPV
  obtain ⟨tc⟩ := whTyA_tyConv hN
  have hT : LRTyA E I n ρ₀ k Γ P (fun a b => Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N)) := by
    rw [LRTyA_eq]; exact tyKA_of_tripleLike hN hNt
  exact ⟨_, hT, ⟨hasTyA_of_tyConvA hp tc⟩, ⟨hasTyA_of_tyConvA hq tc⟩,
    ⟨convA_of_tyConvA (.irr Γ _ _ _ hP hp hq) tc⟩⟩

/-- W-1 (c), VALUES ALONG A TELESCOPE OF PROPOSITIONS ARE A VALID PAIR: over a valid pair below it, two
    value lists, each a typed substitution at its own instance of a telescope of propositions typed in
    `E₀` (two `=ₙ` level lists), are valid at the left's: the fundamental theorem across the two lists
    relates each pair of domains, so the right value is typed at the left's domain, a proposition, where
    two typed values are related. -/
theorem validSubstA_propTel {E₀ : ResolvedEnvA} {ρ₀ : Nat → Nat} (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hNCT : EnvNormCtorTypeA E)
    (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀)
    (hIL : IotaLevelsA I) {a : Nat} {lsL lsR : List Level} (hbL : levelsBounded n lsL = true)
    (hbR : levelsBounded n lsR = true) (hlL : lsL.length = a) (hlR : lsR.length = a) (heq : eqNList lsL lsR) :
    {Θ : LCtxA} → CtxWfA E₀ I a Θ → {ds : List (ExprA × Level)} → TelTyA E₀ I a Θ ds →
    (∀ d ∈ ds, levelIsZero d.2 = true) →
    ∃ K, ∀ k, K ≤ k → ∀ (Γ : LCtxA), Nonempty (CtxWfA E I n Γ) → ∀ (σ σ' : SubstA) (as as' : List ExprA),
      as.length = ds.length → as'.length = ds.length →
      ValidSubstA E I n ρ₀ k Γ σ σ' (instCtxA lsL Θ) →
      Nonempty (SubstTyA E I n Γ (consListA as σ) (telCtxA (instDomsA lsL ds) ++ instCtxA lsL Θ)) →
      Nonempty (SubstTyA E I n Γ (consListA as' σ') (telCtxA (instDomsA lsR ds) ++ instCtxA lsR Θ)) →
      ValidSubstA E I n ρ₀ k Γ (consListA as σ) (consListA as' σ') (telCtxA (instDomsA lsL ds) ++ instCtxA lsL Θ)
  | _, _, _, .nil _, _ => ⟨0, fun k _ Γ _ σ σ' as as' hl hl' hσ _ _ => by
      cases as with
      | cons _ _ => exact nomatch hl
      | nil =>
          cases as' with
          | cons _ _ => exact nomatch hl'
          | nil => exact hσ⟩
  | Θ, hΘ, _, .cons _ D u ds hD tl, hz => by
      obtain ⟨k₁, h₁⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hbL hbR hlL hlR heq hΘ hD
      obtain ⟨k₂, h₂⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hbL hbL hlL hlL (eqNList_refl _) hΘ hD
      obtain ⟨K, hK⟩ := validSubstA_propTel hfc hNCT hE₀ hI hR₀ hEL₀ hIL hbL hbR hlL hlR heq (.assumption hΘ hD) tl
        (fun d hd => hz d (List.mem_cons_of_mem _ hd))
      refine ⟨max (max k₁ k₂) K, fun k hk Γ hΓ σ σ' as as' hl hl' hσ hL hR => ?_⟩
      obtain ⟨x, as, rfl⟩ : ∃ x xs, as = x :: xs := by
        cases as with
        | nil => exact nomatch hl
        | cons x xs => exact ⟨x, xs, rfl⟩
      obtain ⟨x', as', rfl⟩ : ∃ x xs, as' = x :: xs := by
        cases as' with
        | nil => exact nomatch hl'
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hl₀ : as.length = ds.length := Nat.succ.inj hl
      have hl₀' : as'.length = ds.length := Nat.succ.inj hl'
      obtain ⟨tL⟩ := hL
      obtain ⟨tR⟩ := hR
      have elen : (instDomsA lsL ds).length = as.length := by rw [instDomsA, List.length_map, hl₀]
      have elen' : (instDomsA lsR ds).length = as'.length := by rw [instDomsA, List.length_map, hl₀']
      -- the head values, at their own domains
      have hxL : HasTyA E I n Γ x (substA σ (instantiateLevelsA lsL D)) := by
        have h := tL.ty _ _ (lookupTypeA_telCtxA_head (instantiateLevelsA lsL D) (instLevel lsL u)
          (instDomsA lsL ds) (instCtxA lsL Θ))
        rw [elen, substA_consListA_cons_liftA, consListA_cons_head] at h
        exact h
      have hxR : HasTyA E I n Γ x' (substA σ' (instantiateLevelsA lsR D)) := by
        have h := tR.ty _ _ (lookupTypeA_telCtxA_head (instantiateLevelsA lsR D) (instLevel lsR u)
          (instDomsA lsR ds) (instCtxA lsR Θ))
        rw [elen', substA_consListA_cons_liftA, consListA_cons_head] at h
        exact h
      -- the two domains, related across the lists; the left's, related to itself under the pair
      obtain ⟨_, hLR⟩ := h₁ k (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk)
        Γ σ σ' hΓ hσ
      obtain ⟨_, hLL⟩ := h₂ k (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk)
        Γ σ σ' hΓ hσ
      have hzu : isZero (instLevel lsL u) = true :=
        (isZero_iff_eqN_zero _).mpr ((levelIsZero_iff _).mp (levelIsZero_instLevel _ (hz (D, u) (List.mem_cons_self _ _))))
      have hz0 : eqN (instLevel lsL u) .zero := (isZero_iff_eqN_zero _).mp hzu
      obtain ⟨hPV, _, ⟨tFL⟩, ⟨tFR⟩, ⟨cFLR⟩, _⟩ := LRRelA_sortP_elim hzu hLR
      have he := (LRRelA_sort_elim hLL).1
      have hxR' : HasTyA E I n Γ x' (substA σ (instantiateLevelsA lsL D)) :=
        .conv Γ _ _ _ _ _ hxR tFR (eqNA_refl _) tFL (.symm _ _ _ _ cFLR)
      have ha := LRRelA_of_propValid (ρ₀ := ρ₀) (k := k) hPV (hasTyA_retype_sort tFL hz0) hxL hxR'
      have hσ₁ := ValidSubstA_cons hNCT hσ he ha
      -- the tail
      have tL₀ : SubstTyA E I n Γ (consListA as (SubstA.cons x σ))
          (telCtxA ((instantiateLevelsA lsL D, instLevel lsL u) :: instDomsA lsL ds) ++ instCtxA lsL Θ) := tL
      have tR₀ : SubstTyA E I n Γ (consListA as' (SubstA.cons x' σ'))
          (telCtxA ((instantiateLevelsA lsR D, instLevel lsR u) :: instDomsA lsR ds) ++ instCtxA lsR Θ) := tR
      rw [telCtxA_cons_append] at tL₀ tR₀
      have hrec := hK k (Nat.le_trans (Nat.le_max_right _ _) hk) Γ hΓ (SubstA.cons x σ) (SubstA.cons x' σ') as as'
        hl₀ hl₀' hσ₁ ⟨tL₀⟩ ⟨tR₀⟩
      show ValidSubstA E I n ρ₀ k Γ (consListA as (SubstA.cons x σ)) (consListA as' (SubstA.cons x' σ'))
        (telCtxA ((instantiateLevelsA lsL D, instLevel lsL u) :: instDomsA lsL ds) ++ instCtxA lsL Θ)
      rw [telCtxA_cons_append]
      exact hrec

/-- the recursor's telescope after the parameters and the motive: the first minor's domain, at the
    motive and the parameters. -/
theorem applyTelA_recMotA (f : Nat) (ls : List Level) (params idxs : List (ExprA × Level)) (wF wM w : Level)
    (cd : MinorDataA) (cds : List MinorDataA) (body : ExprA) (qs : List ExprA) (mot : ExprA)
    (hqs : qs.length = params.length) :
    ∃ B v, applyTelA (qs ++ [mot]) (piTelA (recDomsA f ls params idxs wF wM (cd :: cds)) body w).1 =
      some (.pi (substA (SubstA.cons mot (consListA qs SubstA.id)) (minorTyA f ls wF wM params.length cd).1)
        (minorTyA f ls wF wM params.length cd).2 B v) := by
  have hT : (piTelA (recDomsA f ls params idxs wF wM (cd :: cds)) body w).1 =
      substA SubstA.id (piTelA params (piTelA ([motTyA f ls params idxs wF wM] ++
        minorDomsA f ls wF wM params.length 0 (cd :: cds) ++ liftDomsA 0 ((cd :: cds).length + 1) idxs ++
        [(liftA idxs.length ((cd :: cds).length + 1) (famLocalsA f ls params.length idxs.length), wF)]) body w).1
        (piTelA ([motTyA f ls params idxs wF wM] ++
        minorDomsA f ls wF wM params.length 0 (cd :: cds) ++ liftDomsA 0 ((cd :: cds).length + 1) idxs ++
        [(liftA idxs.length ((cd :: cds).length + 1) (famLocalsA f ls params.length idxs.length), wF)]) body w).2).1 := by
    rw [substA_id, ← piTelA_append, recDomsA]
    simp only [List.append_assoc]
  rw [hT, applyTelA_append, applyTelA_piTelA _ _ _ _ hqs SubstA.id, Option.some_bind]
  simp only [List.append_assoc, List.singleton_append, piTelA]
  rw [substA_pi]
  simp only [applyTelA]
  rw [instantiate0A_substA_up]
  simp only [minorDomsA, List.cons_append, piTelA, substA_pi, liftA_zero]
  exact ⟨_, _, rfl⟩

/-- the projections' telescope read off the minor's domain: its first `m` binders are the fields'. -/
theorem piDomListA_take_piTelA (Fs : List (ExprA × Level)) (B : ExprA) (w : Level) :
    (piDomListA (piTelA Fs B w).1).take Fs.length = Fs := by
  rw [piDomListA_piTelA]
  exact List.take_left' rfl

/-- W-1 (c), THE STRUCT ARM AT A STRUCT RECURSOR'S SPINE: at the parameters, the motive and the minor, the
    arm answers the minor applied to the major's projections along the minor's domain. -/
theorem structArmA_recSpineA {E : ResolvedEnvA} {r : Nat} {rm : CheckedMemberA} (hrm : E.members r = some rm)
    (hst : structGroupA r rm = true) {ls lsF : List Level} {f c : Nat} {pI dI : List (ExprA × Level)}
    {wF wM : Level}
    (hT : instantiateLevelsA ls rm.mtypeA =
      (piTelA (recDomsA f lsF pI [] wF wM [(c, dI.map plainA, [])]) (recBodyA 0 1) wM).1)
    (hnf : structFieldCountA rm = dI.length) {qs : List ExprA} (hqs : qs.length = pI.length)
    (mot mn x : ExprA) :
    structArmA E (foldAppsA (.const r ls) (qs ++ [mot] ++ [mn])) x =
      some (foldAppsA mn (structProjsA r (motZeroLevelsA ls) qs (foldAppsA (.const f lsF) qs) wF
        (substTelA (consListA qs SubstA.id) dI) x dI.length 0
        (piTelA (substTelA (consListA qs SubstA.id) dI)
          (.app (liftNA dI.length mot) (foldAppsA (.const c lsF) (qs.map (liftNA dI.length) ++
            paramLocalsA dI.length))) wM).1)) := by
  obtain ⟨B, v, hB⟩ := applyTelA_recMotA f lsF pI [] wF wM wM (c, dI.map plainA, []) [] (recBodyA 0 1) qs mot hqs
  rw [minorTyA_plain_eq f c lsF wF wM dI qs pI.length hqs mot] at hB
  obtain ⟨B', hB', hBx⟩ := applyTelA_recPrefixA f lsF pI [] wF wM wM [(c, dI.map plainA, [])] qs mot [mn] [] hqs rfl rfl
  simp only [List.length_nil, List.length_singleton] at hB'
  rw [show qs ++ ([mot] ++ [mn] ++ []) = (qs ++ [mot]) ++ [mn] by simp, applyTelA_append, hB, Option.some_bind] at hB'
  have hmB : instantiate0A mn B = .pi (foldAppsA (.const f lsF) qs) wF B' wM := by
    have h := hB'
    simp only [applyTelA, List.append_nil] at h
    injection h
  have hsp : structSpineA E (.app (foldAppsA (.const r ls) (qs ++ [mot])) mn) =
      some ⟨r, motZeroLevelsA ls, (qs ++ [mot]).dropLast, foldAppsA (.const f lsF) qs, wF,
        (piTelA (substTelA (consListA qs SubstA.id) dI)
          (.app (liftNA dI.length mot) (foldAppsA (.const c lsF) (qs.map (liftNA dI.length) ++
            paramLocalsA dI.length))) wM).1, mn, structFieldCountA rm⟩ :=
    structSpineA_of_parts (foldAppsA_const_head r ls _) hrm hst (by rw [hT]; exact hB) hmB
  rw [foldAppsA_snoc]
  unfold structArmA
  rw [hsp, Option.some_bind, List.dropLast_concat, hnf]
  have hcount : dI.length ≤ piCountA (piTelA (substTelA (consListA qs SubstA.id) dI)
      (.app (liftNA dI.length mot) (foldAppsA (.const c lsF) (qs.map (liftNA dI.length) ++
        paramLocalsA dI.length))) wM).1 := by
    rw [piCountA_piTelA, substTelA_length]; omega
  simp only [hcount, if_true, StructSpineA.reduct]
  have ht := piDomListA_take_piTelA (substTelA (consListA qs SubstA.id) dI)
    (.app (liftNA dI.length mot) (foldAppsA (.const c lsF) (qs.map (liftNA dI.length) ++ paramLocalsA dI.length))) wM
  rw [substTelA_length] at ht
  rw [ht]

theorem take_set_of_le {α : Type} : (l : List α) → (i j : Nat) → j ≤ i → (a : α) → (l.set i a).take j = l.take j
  | [], _, _, _, _ => rfl
  | _ :: _, _, 0, _, _ => rfl
  | _ :: _, 0, _ + 1, h, _ => absurd h (by omega)
  | x :: l, i + 1, j + 1, h, a => by
      show x :: (l.set i a).take j = x :: l.take j
      rw [take_set_of_le l i j (by omega) a]

theorem motZeroLevelsA_length (ls : List Level) : (motZeroLevelsA ls).length = ls.length := List.length_set ..

theorem motZeroLevelsA_take {ls : List Level} {a : Nat} (h : ls.length = a + 1) :
    (motZeroLevelsA ls).take a = ls.take a := by
  unfold motZeroLevelsA
  rw [h, Nat.add_sub_cancel]
  exact take_set_of_le ls a a (Nat.le_refl a) _

theorem instLevel_motZero_param {ls : List Level} {a : Nat} (h : ls.length = a + 1) :
    instLevel (motZeroLevelsA ls) (.param a) = .zero := by
  rw [instLevel_param]
  unfold motZeroLevelsA
  rw [h, Nat.add_sub_cancel, List.getElem?_set_self (by omega)]
  rfl

theorem levelsBounded_set {k : Nat} : (l : List Level) → (i : Nat) → (a : Level) → levelsBounded k l = true →
    levelBounded k a = true → levelsBounded k (l.set i a) = true
  | [], _, _, _, _ => rfl
  | x :: l, 0, a, h, ha => by
      simp only [List.set, levelsBounded, Bool.and_eq_true] at h ⊢
      exact ⟨ha, h.2⟩
  | x :: l, i + 1, a, h, ha => by
      simp only [List.set, levelsBounded, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, levelsBounded_set l i a h.2 ha⟩

theorem levelsBounded_motZero {k : Nat} {ls : List Level} (h : levelsBounded k ls = true) :
    levelsBounded k (motZeroLevelsA ls) = true :=
  levelsBounded_set ls _ _ h rfl

/-- the empty context: every substitution is typed. -/
def substTyA_nil (Δ : LCtxA) (σ : SubstA) : SubstTyA E I n Δ σ [] where
  ty := fun i _ h => by cases i <;> simp [lookupTypeA] at h
  val := fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h

/-- a pointwise list along a substituted telescope extends a typed substitution over the telescope's
    binders. -/
theorem substTyA_of_convArgsA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I) (hIS : IotaSubstA I)
    {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → (Θ : LCtxA) → (τ : SubstA) → (as as' : List ExprA) → as.length = ds.length →
    ConvArgsA E I n Γ (substA τ (piTelA ds B w).1) as as' → Nonempty (SubstTyA E I n Γ τ Θ) →
    Nonempty (SubstTyA E I n Γ (consListA as τ) (telCtxA ds ++ Θ))
  | [], _, _, [], _, _, _, h => h
  | (D, u) :: ds, Θ, τ, a :: as, _, hl, hc, ⟨hτ⟩ => by
      simp only [piTelA, substA_pi] at hc
      cases hc with
      | cons _ _ _ _ _ _ _ as' hr hs =>
          obtain ⟨c⟩ := hr
          have ha := convA_hasTy_left hE hI hR hIS hΓ c
          rw [instantiate0A_substA_up] at hs
          have ih := substTyA_of_convArgsA hE hI hR hIS hΓ B w ds (.assumption D :: Θ) (SubstA.cons a τ) as as'
            (Nat.succ.inj hl) hs ⟨substTyA_cons hτ ha⟩
          rw [← telCtxA_cons_append (D, u) ds Θ] at ih
          exact ih
  | [], _, _, _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, _, _, [], _, hl, _, _ => nomatch hl

/-- W-1 (e-2): the same along a constructor's plain fields (`ctorFieldsA`): a pointwise list along the
    fields' telescope extends a typed substitution over the fields' binders. -/
theorem substTyA_of_convArgsA_ctorFieldsA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) (f : Nat) (ls : List Level) (w : Level)
    (res : List ExprA) :
    (ds : List (ExprA × Level)) → (Θ : LCtxA) → (pl : List ExprA) → (τ : SubstA) → (as as' : List ExprA) →
    as.length = ds.length → ConvArgsA E I n Γ (ctorFieldsA f ls w pl τ (ds.map plainA) res).1 as as' →
    Nonempty (SubstTyA E I n Γ τ Θ) → Nonempty (SubstTyA E I n Γ (consListA as τ) (telCtxA ds ++ Θ))
  | [], _, _, _, [], _, _, _, h => h
  | (D, u) :: ds, Θ, pl, τ, a :: as, _, hl, hc, ⟨hτ⟩ => by
      simp only [List.map, plainA, ctorFieldsA] at hc
      cases hc with
      | cons _ _ _ _ _ _ _ as' hr hs =>
          obtain ⟨c⟩ := hr
          have ha := convA_hasTy_left hE hI hR hIS hΓ c
          rw [instantiate0A_ctorFieldsA_plain] at hs
          have ih := substTyA_of_convArgsA_ctorFieldsA hE hI hR hIS hΓ f ls w res ds (.assumption D :: Θ) pl
            (SubstA.cons a τ) as as' (Nat.succ.inj hl) hs ⟨substTyA_cons hτ ha⟩
          rw [← telCtxA_cons_append (D, u) ds Θ] at ih
          exact ih
  | [], _, _, _, _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, _, _, _, [], _, hl, _, _ => nomatch hl

theorem liftNA_closed {e : ExprA} (h : ∀ k, liftA k 1 e = e) : (m : Nat) → liftNA m e = e
  | 0 => rfl
  | m + 1 => by show liftA 0 1 (liftNA m e) = e; rw [liftNA_closed h m, h 0]

theorem liftNA_const (m r : Nat) (ls : List Level) : liftNA m (.const r ls) = .const r ls := by
  rw [liftNA_eq]; rfl

theorem liftNA_foldAppsA (m : Nat) : (h : ExprA) → (xs : List ExprA) →
    liftNA m (foldAppsA h xs) = foldAppsA (liftNA m h) (xs.map (liftNA m))
  | _, [] => rfl
  | h, x :: xs => by
      show liftNA m (foldAppsA (.app h x) xs) = foldAppsA (liftNA m h) (liftNA m x :: xs.map (liftNA m))
      rw [liftNA_foldAppsA m (.app h x) xs]
      show foldAppsA (liftNA m (.app h x)) (xs.map (liftNA m)) =
        foldAppsA (.app (liftNA m h) (liftNA m x)) (xs.map (liftNA m))
      rw [liftNA_eq, liftNA_eq, liftNA_eq]
      rfl

theorem map_plainA_instLevels (ls : List Level) (ds : List (ExprA × Level)) :
    (ds.map plainA).map (FieldA.instLevels ls) = (instDomsA ls ds).map plainA := by
  simp only [instDomsA, List.map_map]
  rfl

/-- a minor premise of plain fields at the parameters `qs` (no field local yet): the Π-telescope over the
    fields' substituted domains at the motive applied to the constructor at the fields' variables. -/
theorem minorFieldsA_plain_piTel (f c : Nat) (ls : List Level) (wF wM : Level) (ds : List (ExprA × Level))
    (qs : List ExprA) (M : ExprA) :
    (minorFieldsA f c ls wF wM qs M [] (consListA qs SubstA.id) (ds.map plainA) []).1 =
      (piTelA (substTelA (consListA qs SubstA.id) ds)
        (.app (liftNA ds.length M) (foldAppsA (.const c ls) (qs.map (liftNA ds.length) ++ paramLocalsA ds.length)))
        wM).1 := by
  rw [minorFieldsA_plain_eq]
  simp only [minorFieldsA, List.map_nil, List.nil_append]
  rfl

theorem minorArityA_plainA : (ds : List (ExprA × Level)) → minorArityA (ds.map plainA) = ds.length
  | [] => rfl
  | (_, _) :: ds => by
      show minorArityA (ds.map plainA) + 1 = ds.length + 1
      rw [minorArityA_plainA ds]

/-- the projections along a telescope's walk: one per binder. -/
theorem structProjsA_length (r : Nat) (ls₀ : List Level) (ps : List ExprA) (S : ExprA) (uS : Level)
    (Fsel : List (ExprA × Level)) (y Body : ExprA) (w : Level) :
    (rest : List (ExprA × Level)) → (i : Nat) → (τ : SubstA) →
    (structProjsA r ls₀ ps S uS Fsel y rest.length i (substA τ (piTelA rest Body w).1)).length = rest.length
  | [], _, _ => rfl
  | (D, u) :: rest, i, τ => by
      simp only [piTelA, substA_pi, List.length_cons, structProjsA]
      rw [instantiate0A_substA_up, structProjsA_length r ls₀ ps S uS Fsel y Body w rest (i + 1)]

end Tel

/-- a plain field's domain in the plain telescope is the domain of a plain field. -/
theorem mem_plainTelA {d : ExprA × Level} : (fs : List FieldA) → d ∈ plainTelA fs → FieldA.plain d.1 d.2 ∈ fs
  | [], h => absurd h (List.not_mem_nil d)
  | .plain D u :: fs, h => by
      simp only [plainTelA] at h
      rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self _ _
      · exact List.mem_cons_of_mem _ (mem_plainTelA fs h')
  | .drec _ :: fs, h | .frec _ _ _ _ :: fs, h | .drecD _ _ :: fs, h => by
      simp only [plainTelA] at h
      exact List.mem_cons_of_mem _ (mem_plainTelA fs h)

/-- a minor premise of plain fields and no index counts its fields: the motive's application after
    them is no Π. -/
theorem piCountA_minorTyA_plain (f c : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (ds : List (ExprA × Level)) : piCountA (minorTyA f ls wF wM np (c, ds.map plainA, [])).1 = ds.length := by
  unfold minorTyA
  dsimp only
  rw [minorFieldsA_plain_eq, piCountA_piTelA, substTelA_length]
  simp only [minorFieldsA, liftNA_bvar, piCountA_foldAppsA_bvar, Nat.add_zero]

/-- W-1 (c): at a struct group the member's field count (`structFieldCountA`, what the struct arm
    reads) is the number of its one constructor's fields. -/
theorem structFieldCountA_groupRecA {I : IotaIfaceA} {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)} (rec : GroupRecA I E₀ f fm fv cs)
    {gc : GroupCtorA I E₀ f fm fv} (hgc : cs.reverse = [gc]) (hnoidx : fv.indices = [])
    (hplain : gc.view.fields = (plainTelA gc.view.fields).map plainA) :
    structFieldCountA rec.member = (plainTelA gc.view.fields).length := by
  have hst' : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst'
  have hres0 : gc.view.res = [] :=
    List.eq_nil_of_length_eq_zero (by rw [gc.view.res_length, hnoidx]; rfl)
  generalize hds : plainTelA gc.view.fields = ds at hplain ⊢
  have hcd : cs.reverse.map GroupCtorA.minorData = [(gc.ref, ds.map plainA, [])] := by
    rw [hgc]
    simp only [List.map, GroupCtorA.minorData]
    rw [← hplain, hres0]
  have hL₀ : (piDomListA rec.member.mtypeA).reverse =
      (liftA 0 2 (famLocalsA f (canonLevelsA fm.arity) fv.params.length 0), fv.sort) ::
        (liftA 0 0 (minorTyA f (canonLevelsA fm.arity) fv.sort (rec.elim.motiveLevel fm.arity)
            fv.params.length (gc.ref, ds.map plainA, [])).1,
          (minorTyA f (canonLevelsA fm.arity) fv.sort (rec.elim.motiveLevel fm.arity) fv.params.length
            (gc.ref, ds.map plainA, [])).2) ::
        (motTyA f (canonLevelsA fm.arity) fv.params [] fv.sort (rec.elim.motiveLevel fm.arity)) ::
          fv.params.reverse := by
    rw [hst', piDomListA_recTypeA_reverse, hcd, hnoidx]
    simp [minorDomsA, liftDomsA]
  unfold structFieldCountA
  rw [hL₀]
  dsimp only
  rw [liftA_zero, piCountA_minorTyA_plain]

/-- W-1 (e-2), A STRUCT GROUP'S SHAPE, read once: its one constructor, no index, a `Prop` family, plain
    fields in `Prop`, and the member's field count (what the struct arm reads). The recursors' clause
    (`recSemClauseA`) and ι subject reduction (`RcicAnnIotaSR`) read it here. -/
theorem structCtorA_of_structGroupA {I : IotaIfaceA} {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)} (rec : GroupRecA I E₀ f fm fv cs)
    (hst : structGroupA (f + 1 + cs.length) rec.member = true) :
    ∃ gc : GroupCtorA I E₀ f fm fv, cs.reverse = [gc] ∧ fv.indices = [] ∧ levelIsZero fv.sort = true ∧
      gc.view.fields = (plainTelA gc.view.fields).map plainA ∧
      (∀ d ∈ plainTelA gc.view.fields, levelIsZero d.2 = true) ∧
      structFieldCountA rec.member = (plainTelA gc.view.fields).length := by
  obtain ⟨hcs1, hnoidx, hzF, _, hcd⟩ := structShape_of_structGroupA rec hst
  obtain ⟨gc, hgc⟩ : ∃ gc, cs.reverse = [gc] := by
    match cs.reverse, (List.length_reverse cs).trans hcs1 with
    | [gc], _ => exact ⟨gc, rfl⟩
  have hflds := (hcd gc.minorData (by rw [hgc]; exact List.mem_singleton_self _)).2
  have hplain : gc.view.fields = (plainTelA gc.view.fields).map plainA :=
    fields_plainTelA _ fun fld hf => (hflds fld hf).elim fun D h => h.elim fun u h => ⟨D, u, h.1⟩
  refine ⟨gc, hgc, hnoidx, hzF, hplain, fun d hd => ?_, structFieldCountA_groupRecA rec hgc hnoidx hplain⟩
  obtain ⟨D, u, e, hu⟩ := hflds _ (mem_plainTelA _ hd)
  injection e with _ e2
  rw [e2]
  exact hu

theorem map_snd_substTelA : (σ : SubstA) → (ds : List (ExprA × Level)) →
    (substTelA σ ds).map Prod.snd = ds.map Prod.snd
  | _, [] => rfl
  | σ, (D, u) :: ds => by simp only [substTelA, List.map_cons, map_snd_substTelA σ.up ds]

/-- a minor premise of plain fields: its binders carry the fields' levels. -/
theorem piDomListA_minorTyA_plain (f c : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (ds : List (ExprA × Level)) (res : List ExprA) :
    (piDomListA (minorTyA f ls wF wM np (c, ds.map plainA, res)).1).map Prod.snd = ds.map Prod.snd := by
  unfold minorTyA
  dsimp only
  rw [minorFieldsA_plain_eq, piDomListA_piTelA, List.map_append, map_snd_substTelA]
  simp only [minorFieldsA, liftNA_bvar, piDomListA_foldAppsA_bvar, List.map_nil, List.append_nil]

/-- a minor premise with a plain field is a Π. -/
theorem minorTyA_plain_pi (f c : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (D : ExprA) (u : Level) (ds : List (ExprA × Level)) (res : List ExprA) :
    ∃ D' B v, (minorTyA f ls wF wM np (c, ((D, u) :: ds).map plainA, res)).1 = .pi D' u B v := by
  unfold minorTyA
  dsimp only
  rw [minorFieldsA_plain_eq]
  exact ⟨_, _, _, rfl⟩

/-- W-1 (e-3), THE STRUCT TEST IS COMPLETE ON BUILT RECURSOR TYPES: the recursor type 05 §13 builds for a
    group with one constructor whose fields are all plain, at least one, at levels zero at every
    valuation, and no index, over a family whose sort is zero at every valuation and with a motive whose
    sort is not (AnySort), passes `structGroupA` at the recursor's own reference. -/
theorem structGroupA_of_recTypeA {r f : Nat} {m : CheckedMemberA} {ls : List Level}
    {params : List (ExprA × Level)} {wF wM : Level} {c : Nat} {ds : List (ExprA × Level)} {res : List ExprA}
    (hst : m.mtypeA = recTypeA f ls params [] wF wM [(c, ds.map plainA, res)]) (hne : ds ≠ [])
    (hzds : ∀ d ∈ ds, levelIsZero d.2 = true) (hr : r = f + 2) (hz : levelIsZero wF = true)
    (hwM : levelIsZero wM = false) : structGroupA r m = true := by
  subst hr
  have hL : (piDomListA m.mtypeA).reverse =
      (liftA 0 2 (famLocalsA f ls params.length 0), wF) ::
        (liftA 0 0 (minorTyA f ls wF wM params.length (c, ds.map plainA, res)).1,
          (minorTyA f ls wF wM params.length (c, ds.map plainA, res)).2) ::
        (motTyA f ls params [] wF wM) :: params.reverse := by
    rw [hst, piDomListA_recTypeA_reverse]
    simp [minorDomsA, liftDomsA]
  obtain ⟨⟨D₀, u₀⟩, ds', rfl⟩ : ∃ d₀ ds', ds = d₀ :: ds' := match ds, hne with
    | d₀ :: ds', _ => ⟨d₀, ds', rfl⟩
  obtain ⟨D, B, v, hpi⟩ := minorTyA_plain_pi f c ls wF wM params.length D₀ u₀ ds' res
  have hall := piDomListA_minorTyA_plain f c ls wF wM params.length ((D₀, u₀) :: ds') res
  rw [hpi] at hall
  have hallZ : (piDomListA (ExprA.pi D u₀ B v)).all (fun p => levelIsZero p.2) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hp' : p.2 ∈ ((D₀, u₀) :: ds').map Prod.snd := by rw [← hall]; exact List.mem_map_of_mem _ hp
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp hp'
    rw [← hde]; exact hzds d hd
  unfold structGroupA
  rw [hL, liftA_zero, hpi]
  simp [appsSpineA_majorDom, hz, hwM, motTyA, piTelA, liftA, hallZ]

section StructSide
variable {E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat}

/-- W-1 (e-2), ONE SIDE OF A STRUCT RECURSOR'S SPINE AT THE TYPING LEVEL: given the parameters `qsX` typed
    along the family's and the constructor's types at the levels `lsX.take fm.arity`, and both heads typed, the
    family application is typed at its sort, the constructor typed at it over any typed fields, the projections
    of any major of the family application typed along the fields, and any two typed field substitutions
    convertible (every field is a proof). `structSideA` reads the premises off the relation; ι subject
    reduction (`RcicAnnIotaSR`), off a typed redex. -/
theorem structSideTyA (hE : EnvClosedA E) (hEL : EnvLevelsA E)
    (hN : EnvNormClosedA E) (hNL : EnvNormLevelsA E)
    {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} (hEL₀ : EnvLevelsA E₀) (fv : FamViewA fm)
    (cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)) (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length)
    (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs) (hpre : PrefixA (groupRecEnvA cs rec) E)
    (hpreG : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    (hst : structGroupA (f + 1 + cs.length) rec.member = true)
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgc : cs.reverse = [gc]) (hnoidx : fv.indices = [])
    (hplain : gc.view.fields = (plainTelA gc.view.fields).map plainA)
    (hzds : ∀ d ∈ plainTelA gc.view.fields, levelIsZero d.2 = true)
    {lsX : List Level} (hlX : lsX.length = rec.member.arity) (hbX : levelsBounded n lsX = true)
    {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) {qsX : List ExprA} (hqX : qsX.length = fm.nparamsA)
    (hPq : ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA (lsX.take fm.arity) fm.mtypeA) qsX qsX)
    (hPF : ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA (lsX.take fm.arity) gc.member.mtypeA) qsX qsX)
    (hFc : HasTyA E (iotaIfaceA E) n Γ (.const f (lsX.take fm.arity))
      (instantiateLevelsA (lsX.take fm.arity) fm.mtypeA))
    (hcΔ : ∀ Δ, CtxWfA E (iotaIfaceA E) n Δ → Nonempty (HasTyA E (iotaIfaceA E) n Δ
      (.const gc.ref (lsX.take fm.arity)) (instantiateLevelsA (lsX.take fm.arity) gc.member.mtypeA))) :
    Nonempty (HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const f (lsX.take fm.arity)) qsX)
      (.sort (instLevel (lsX.take fm.arity) fv.sort))) ∧
    (∀ as : List ExprA, as.length = (plainTelA gc.view.fields).length →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA as (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params))) →
      Nonempty (HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const gc.ref (lsX.take fm.arity)) (qsX ++ as))
        (foldAppsA (.const f (lsX.take fm.arity)) qsX))) ∧
    (∀ (y Body : ExprA) (w : Level),
      HasTyA E (iotaIfaceA E) n Γ y (foldAppsA (.const f (lsX.take fm.arity)) qsX) →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ
        (consListA (structProjsA (f + 1 + cs.length) (motZeroLevelsA lsX) qsX
          (foldAppsA (.const f (lsX.take fm.arity)) qsX) (instLevel (lsX.take fm.arity) fv.sort)
          (substTelA (consListA qsX SubstA.id) (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)))
          y (plainTelA gc.view.fields).length 0
          (piTelA (substTelA (consListA qsX SubstA.id) (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)))
            Body w).1) (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params)))) ∧
    (∀ as bs : List ExprA, as.length = (plainTelA gc.view.fields).length →
      bs.length = (plainTelA gc.view.fields).length →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA as (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params))) →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA bs (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params))) →
      Nonempty (ConvSubstA E (iotaIfaceA E) n Γ (consListA as (consListA qsX SubstA.id))
        (consListA bs (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params)))) := by
  have hI := iotaFnA_lift hE hN
  have hIS := iotaFnA_subst hE hN
  have hR := iotaFnA_recHead E
  have hIL := iotaFnA_levels hEL hNL
  have hgcm : gc ∈ cs := List.mem_reverse.mp (by rw [hgc]; exact List.mem_singleton_self gc)
  obtain ⟨hrm, hfm, _⟩ := members_groupRecA hfresh hlay hpre
  have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpreG
  have hELG : EnvLevelsA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) := fun r m h => hEL r m (hpreG r m h)
  have hres0 : gc.view.res = [] :=
    List.eq_nil_of_length_eq_zero (by rw [gc.view.res_length, hnoidx]; rfl)
  -- the recursor at the motive's zero level
  obtain ⟨_, _, _, hwM0, _⟩ := structShape_of_structGroupA rec hst
  have helim : rec.elim = .anySort := by
    cases h : rec.elim with
    | anySort => rfl
    | propOnly => rw [h] at hwM0; exact absurd (hwM0.symm.trans rfl) Bool.false_ne_true
  have harity : rec.member.arity = fm.arity + 1 := by rw [rec.harity, helim]; rfl
  have hl₀ : (motZeroLevelsA lsX).length = rec.member.arity := by rw [motZeroLevelsA_length, hlX]
  have hb₀ := levelsBounded_motZero hbX
  have hlX' : lsX.length = fm.arity + 1 := hlX.trans harity
  have hrc₀ : HasTyA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) (motZeroLevelsA lsX))
      (instantiateLevelsA (motZeroLevelsA lsX) rec.member.mtypeA) :=
    .const Γ _ _ rec.member (instLevel (motZeroLevelsA lsX) rec.u) hrm hl₀ hb₀
      (hasTyClosedWeakenA hE hI (liftA_instantiateLevelsA_closed rec.hclT _) (fun _ => rfl) Γ
        (hasTyEnvA hpreG (hasTyA_instLevels hELG hIL hb₀ hl₀ rec.hT)))
  rw [recTelA hEL hfm rec hl₀, motZeroLevelsA_take hlX', helim] at hrc₀
  generalize hds : plainTelA gc.view.fields = ds at hplain hzds ⊢
  have hcd : (cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (lsX.take fm.arity)) =
      [(gc.ref, (instDomsA (lsX.take fm.arity) ds).map plainA, [])] := by
    rw [hgc]
    simp only [List.map_cons, List.map_nil, GroupCtorA.minorData, MinorDataA.inst, hres0]
    rw [hplain, map_plainA_instLevels]
  rw [hcd, hnoidx] at hrc₀
  simp only [RecElimA.motiveLevel, instLevel_motZero_param hlX', List.length_nil, List.length_singleton] at hrc₀
  have e0 : instDomsA (lsX.take fm.arity) ([] : List (ExprA × Level)) = [] := rfl
  rw [e0, List.length_nil] at hrc₀
  -- the levels of the family
  have hlF : (lsX.take fm.arity).length = fm.arity := by rw [List.length_take, hlX']; omega
  have hbF : levelsBounded n (lsX.take fm.arity) = true := levelsBounded_take lsX _ hbX
  generalize hlsF : lsX.take fm.arity = lsF at hrc₀ hPq hPF hFc hcΔ hlF hbF ⊢
  have hqP : qsX.length = (instDomsA lsF fv.params).length := by rw [hqX, instDomsA, List.length_map, fv.nparams]
  -- the parameters, pointwise and as a typed substitution
  have hparC : ConvArgsA E (iotaIfaceA E) n Γ (piTelA (instDomsA lsF fv.params) (.sort .zero) .zero).1 qsX qsX := by
    have h := hPq
    rw [fv.inst_split, ← substA_id (piTelA _ _ _).1] at h
    have h' := convArgsA_piTelA_body _ (.sort .zero) _ .zero _ SubstA.id h hqP
    rwa [substA_id] at h'
  obtain ⟨hσq⟩ : Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA qsX SubstA.id) (telCtxA (instDomsA lsF fv.params))) := by
    have h := substTyA_of_convArgsA hE hI hR hIS hΓ (.sort .zero) .zero (instDomsA lsF fv.params) [] SubstA.id qsX qsX
      hqP (by rw [substA_id]; exact hparC) ⟨substTyA_nil Γ SubstA.id⟩
    rwa [List.append_nil] at h
  -- the family application at its sort
  have happF : applyTelA qsX (instantiateLevelsA lsF fm.mtypeA) = some (.sort (instLevel lsF fv.sort)) := by
    rw [fv.applyTel_params lsF qsX hqX, FamViewA.idxTelA, hnoidx]
    rfl
  obtain ⟨cF⟩ := convA_spine hE hI hR hIS hΓ hPq ⟨.refl _ _ _ hFc⟩ _ happF
  have hS := convA_hasTy_left hE hI hR hIS hΓ cF
  -- the constructor's head, typed in every context; its type applied to any parameters
  have hcE : E.members gc.ref = some gc.member := hpreG _ _ (members_groupEnvA_ctor hfresh hgcm)
  have happc : ∀ (ps : List ExprA) (τ : SubstA), ps.length = fm.nparamsA →
      applyTelA ps (instantiateLevelsA lsF gc.member.mtypeA) =
        some (ctorFieldsA f lsF (instLevel lsF fv.sort) ps (consListA ps τ) ((instDomsA lsF ds).map plainA) []).1 := by
    intro ps τ hps
    rw [← substA_mtype hE hcE lsF τ, gc.view.inst_tel lsF hlF,
      applyTelA_ctorTypeA_params_tail _ _ _ _ _ _ ps (by rw [instDomsA_length, gc.view.mirrors_length]; exact hps) τ,
      hplain, map_plainA_instLevels, hres0]
    rfl
  -- (2): the constructor over typed fields
  have out2 : ∀ as : List ExprA, as.length = ds.length →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA as (consListA qsX SubstA.id))
        (telCtxA (instDomsA lsF ds) ++ telCtxA (instDomsA lsF fv.params))) →
      Nonempty (HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const gc.ref lsF) (qsX ++ as))
        (foldAppsA (.const f lsF) qsX)) := by
    intro as hlen ⟨hσ⟩
    obtain ⟨hc⟩ := hcΔ Γ hΓ
    exact ctorApp_hasTyA hE hI hR hIS hΓ hc hPF (happc qsX SubstA.id hqX) (by rw [hlen, instDomsA_length]) hσ
  -- the fields' telescope
  have tdI : TelTyA E (iotaIfaceA E) n (telCtxA (instDomsA lsF fv.params)) (instDomsA lsF ds) := by
    have t := ((telTyA_of_fieldsTyA gc.view.typed).instLevels hEL₀ hIL hbF hlF).env hpre₀
    rw [← telCtxA_instDomsA, hds] at t
    exact t
  have hzI : ∀ d ∈ instDomsA lsF ds, eqN d.2 .zero := by
    intro d hd
    obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.mp hd
    exact (levelIsZero_iff _).mp (levelIsZero_instLevel _ (hzds d₀ hd₀))
  -- the constructor under the fields' binders, at their variables
  have tFs := (TelTyA.subst hE hI hR hIS tdI hσq).1
  have hΓm := ctxWfA_telCtx tFs hΓ
  have hup := (TelTyA.subst hE hI hR hIS tdI hσq).2
  have eup : upNA (instDomsA lsF ds).length (consListA qsX SubstA.id) =
      consListA (paramLocalsA (instDomsA lsF ds).length)
        (consListA (qsX.map (liftNA (instDomsA lsF ds).length))
          (fun j => liftNA (instDomsA lsF ds).length (SubstA.id j))) :=
    funext (upNA_consListA _ qsX SubstA.id)
  rw [eup] at hup
  obtain ⟨hcm⟩ := hcΔ _ hΓm
  have hPFm := convArgsA_liftN hE hI hPF (telCtxA (substTelA (consListA qsX SubstA.id) (instDomsA lsF ds)))
  rw [telCtxA_length, substTelA_length, liftNA_closed (liftA_instantiateLevelsA_closed gc.hclT lsF)] at hPFm
  obtain ⟨hKm⟩ := ctorApp_hasTyA hE hI hR hIS hΓm hcm hPFm
    (happc _ _ (by rw [List.length_map]; exact hqX)) (paramLocalsA_length _) hup
  have hK : HasTyA E (iotaIfaceA E) n (telCtxA (substTelA (consListA qsX SubstA.id) (instDomsA lsF ds)) ++ Γ)
      (foldAppsA (.const gc.ref lsF) (qsX.map (liftNA (instDomsA lsF ds).length) ++
        paramLocalsA (instDomsA lsF ds).length))
      (liftNA (instDomsA lsF ds).length (foldAppsA (.const f lsF) qsX)) := by
    rw [liftNA_foldAppsA, liftNA_const]
    exact hKm
  have hPE := propExtA_telTyA (E := E) (I := iotaIfaceA E) (n := n) (Θ := telCtxA (instDomsA lsF fv.params))
    .base tdI hzI
  refine ⟨⟨hS⟩, out2, fun y Body w hy => ?_, fun as bs ha hb ⟨hσa⟩ ⟨hσb⟩ => ?_⟩
  · have h := structProjsA_substTyA hE hI hR hIS hΓ hrc₀ hqP hparC hσq tdI hzI hS hK hy Body w
    rwa [instDomsA_length] at h
  · refine ⟨convSubstA_propExtA hE hI hR hIS hPE hσa hσb (fun j A hj _ => ?_)⟩
    obtain ⟨p, rfl⟩ : ∃ p, j = p + as.length := ⟨j - as.length, by rw [instDomsA_length] at hj; omega⟩
    rw [consListA_add, show p + as.length = p + bs.length by rw [ha, hb], consListA_add]

/-- W-1 (c), ONE SIDE OF A STRUCT RECURSOR'S SPINE, at the levels `lsX` and parameters `qsX` related to
    themselves along the family's type: the family application typed at its sort, the constructor typed
    at it over any typed fields, and the projections of any major of the family application typed along
    the fields. -/
theorem structSideA (hE : EnvClosedA E) (hEL : EnvLevelsA E)
    (hN : EnvNormClosedA E) (hNCT : EnvNormCtorTypeA E) (hNL : EnvNormLevelsA E)
    {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {u : Level} (hW : EnvWfA (iotaIfaceA E) E₀)
    (hclT : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA)
    (hT : HasTyA E₀ (iotaIfaceA E) fm.arity [] fm.mtypeA (.sort u)) (fv : FamViewA fm)
    (cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)) (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length)
    (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs) (hpre : PrefixA (groupRecEnvA cs rec) E)
    (hfund : BaseFundA E₀ E (iotaIfaceA E) n ρ₀) (hfc : BaseFundConvA E₀ E (iotaIfaceA E) n ρ₀)
    (hR₀ : IotaRecHeadTypedA E₀ (iotaIfaceA E))
    (hpreG : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    (ih : EnvSemAt E (iotaIfaceA E) n ρ₀ (domA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))))
    (hst : structGroupA (f + 1 + cs.length) rec.member = true)
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgc : cs.reverse = [gc]) (hnoidx : fv.indices = [])
    (hplain : gc.view.fields = (plainTelA gc.view.fields).map plainA)
    (hzds : ∀ d ∈ plainTelA gc.view.fields, levelIsZero d.2 = true)
    {lsX : List Level} (hlX : lsX.length = rec.member.arity) (hbX : levelsBounded n lsX = true)
    {Γ : LCtxA} (hΓ : CtxWfA E (iotaIfaceA E) n Γ) {qsX : List ExprA} (hqX : qsX.length = fm.nparamsA)
    {kX : Nat} (hqF : ArgsRelKA E (iotaIfaceA E) n ρ₀ kX Γ (instantiateLevelsA (lsX.take fm.arity) fm.mtypeA)
      (qsX ++ []) (qsX ++ [])) :
    Nonempty (HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const f (lsX.take fm.arity)) qsX)
      (.sort (instLevel (lsX.take fm.arity) fv.sort))) ∧
    (∀ as : List ExprA, as.length = (plainTelA gc.view.fields).length →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA as (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params))) →
      Nonempty (HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const gc.ref (lsX.take fm.arity)) (qsX ++ as))
        (foldAppsA (.const f (lsX.take fm.arity)) qsX))) ∧
    (∀ (y Body : ExprA) (w : Level),
      HasTyA E (iotaIfaceA E) n Γ y (foldAppsA (.const f (lsX.take fm.arity)) qsX) →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ
        (consListA (structProjsA (f + 1 + cs.length) (motZeroLevelsA lsX) qsX
          (foldAppsA (.const f (lsX.take fm.arity)) qsX) (instLevel (lsX.take fm.arity) fv.sort)
          (substTelA (consListA qsX SubstA.id) (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)))
          y (plainTelA gc.view.fields).length 0
          (piTelA (substTelA (consListA qsX SubstA.id) (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)))
            Body w).1) (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params)))) ∧
    (∀ as bs : List ExprA, as.length = (plainTelA gc.view.fields).length →
      bs.length = (plainTelA gc.view.fields).length →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA as (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params))) →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA bs (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params))) →
      Nonempty (ConvSubstA E (iotaIfaceA E) n Γ (consListA as (consListA qsX SubstA.id))
        (consListA bs (consListA qsX SubstA.id))
        (telCtxA (instDomsA (lsX.take fm.arity) (plainTelA gc.view.fields)) ++
          telCtxA (instDomsA (lsX.take fm.arity) fv.params)))) := by
  have hI := iotaFnA_lift hE hN
  have hIL := iotaFnA_levels hEL hNL
  have hE₀ := envWfA_closed hW
  have hEL₀ := envWfA_levels hW
  have hgcm : gc ∈ cs := List.mem_reverse.mp (by rw [hgc]; exact List.mem_singleton_self gc)
  obtain ⟨_, hfm, _⟩ := members_groupRecA hfresh hlay hpre
  have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpreG
  obtain ⟨_, _, _, hwM0, _⟩ := structShape_of_structGroupA rec hst
  have helim : rec.elim = .anySort := by
    cases h : rec.elim with
    | anySort => rfl
    | propOnly => rw [h] at hwM0; exact absurd (hwM0.symm.trans rfl) Bool.false_ne_true
  have harity : rec.member.arity = fm.arity + 1 := by rw [rec.harity, helim]; rfl
  have hlX' : lsX.length = fm.arity + 1 := hlX.trans harity
  have hlF : (lsX.take fm.arity).length = fm.arity := by rw [List.length_take, hlX']; omega
  have hbF : levelsBounded n (lsX.take fm.arity) = true := levelsBounded_take lsX _ hbX
  generalize hlsF : lsX.take fm.arity = lsF at hqF hlF hbF ⊢
  -- the parameters along the family's type
  have hPq : ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA lsF fm.mtypeA) qsX qsX := by
    have h := convArgsA_refl_left (convArgsA_of_argsRelKA hqF)
    simpa only [List.append_nil] using h
  -- the family application at its sort
  have hFc : HasTyA E (iotaIfaceA E) n Γ (.const f lsF) (instantiateLevelsA lsF fm.mtypeA) :=
    .const Γ f lsF fm (instLevel lsF u) hfm hlF hbF
      (hasTyClosedWeakenA hE hI (liftA_instantiateLevelsA_closed hclT lsF) (fun _ => rfl) Γ
        (hasTyEnvA hpre₀ (hasTyA_instLevels hEL₀ hIL hbF hlF hT)))
  -- the constructor at the parameters (P2): its mirror telescope, as in the unit clause
  obtain ⟨hwf⟩ := fv.paramsCtxWf hT
  have hwf₀ : CtxWfA E₀ (iotaIfaceA E) fm.arity (telCtxA fv.params ++ []) := (List.append_nil _).symm ▸ hwf
  obtain ⟨Km, hKm⟩ := mirrorParConvA hfc hNCT hE₀ hI hR₀ hEL₀ hIL hbF hbF hlF hlF (eqNListA_refl _)
    gc.view.mirrorsConv hwf₀
  obtain ⟨Kp, hKp⟩ := paramSubstA hfund hfc hNCT hN hE₀ hE hI hR₀ hEL₀ hIL fv hclT hT hbF hbF hlF hlF
    (eqNListA_refl _)
  have hVC := hKp (max Km (max Kp kX)) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) qsX qsX [] []
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) ⟨hΓ⟩ hqX hqX hqF [] (Or.inl rfl)
  simp only [map_wkExprA_nil] at hVC
  rw [← telCtxA_instDomsA] at hVC
  have hrelC := argsRelKA_of_validSubst hNCT (instDomsA lsF fv.params)
    (instantiateLevelsA lsF fv.idxTelA)
    (instLevel lsF (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2) qsX qsX
    (by rw [instDomsA_length, fv.nparams]; exact hqX) (by rw [instDomsA_length, fv.nparams]; exact hqX) hVC
  have hPC := hKm (max Km (max Kp kX)) (Nat.le_max_left _ _) Γ ⟨hΓ⟩ SubstA.id (ValidSubstA_nil _ _ _)
    (ValidSubstA_nil _ _ _) (instantiateLevelsA lsF fv.idxTelA)
    (instLevel lsF (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2)
    (ctorFieldsA f lsF (instLevel lsF fv.sort)
      (paramLocalsA (instDomsA lsF gc.view.mirrors).length) SubstA.id
      (gc.view.fields.map (FieldA.instLevels lsF))
      (gc.view.res.map (instantiateLevelsA lsF))).1
    (ctorFieldsA f lsF (instLevel lsF fv.sort)
      (paramLocalsA (instDomsA lsF gc.view.mirrors).length) SubstA.id
      (gc.view.fields.map (FieldA.instLevels lsF))
      (gc.view.res.map (instantiateLevelsA lsF))).2
    qsX (by rw [substA_id]; exact hrelC) (by rw [fv.nparams]; exact hqX)
  rw [substA_id, substA_id, ← fv.inst_split] at hPC
  have hcT : (piTelA (instDomsA lsF gc.view.mirrors)
      (ctorFieldsA f lsF (instLevel lsF fv.sort)
        (paramLocalsA (instDomsA lsF gc.view.mirrors).length) SubstA.id
        (gc.view.fields.map (FieldA.instLevels lsF))
        (gc.view.res.map (instantiateLevelsA lsF))).1
      (ctorFieldsA f lsF (instLevel lsF fv.sort)
        (paramLocalsA (instDomsA lsF gc.view.mirrors).length) SubstA.id
        (gc.view.fields.map (FieldA.instLevels lsF))
        (gc.view.res.map (instantiateLevelsA lsF))).2).1 =
      instantiateLevelsA lsF gc.member.mtypeA := by
    rw [gc.view.inst_tel _ hlF]; rfl
  rw [hcT] at hPC
  have hPF := convArgsA_rebase hPC hPq
  -- the constructor's head, typed in every context
  have hcE : E.members gc.ref = some gc.member := hpreG _ _ (members_groupEnvA_ctor hfresh hgcm)
  obtain ⟨k₀, hk₀⟩ := ih gc.ref gc.member ⟨gc.member, members_groupEnvA_ctor hfresh hgcm⟩ hcE lsF lsF
    (hlF.trans gc.harity.symm) hbF hbF (eqNListA_refl _)
  have hcΔ : ∀ Δ, CtxWfA E (iotaIfaceA E) n Δ →
      Nonempty (HasTyA E (iotaIfaceA E) n Δ (.const gc.ref lsF) (instantiateLevelsA lsF gc.member.mtypeA)) :=
    fun Δ hΔ => (LRRelA_hasTy (hk₀ k₀ (Nat.le_refl _) Δ ⟨hΔ⟩)).1
  subst hlsF
  exact structSideTyA hE hEL hN hNL hEL₀ fv cs hfresh hlay rec hpre hpreG hst hgc hnoidx hplain hzds hlX hbX hΓ hqX
    hPq hPF hFc hcΔ

/-- W-1 (c), THE RECURSORS' CLAUSE AT A STRUCT GROUP, at one world: full applications to related arguments
    are related at their type. Each side steps to its minor applied to its major's projections (K-struct,
    at every major since W-1 (e)); the left's projections and the right's are related along the
    minor's domain (every field is a proof: the right's projections are typed at the left's domains by the
    fundamental theorem on the field types, and proofs are related by `irr`); so the two reducts are related
    at the minor's conclusion `M (c qs π)`, which is the redex's `M x` (the family application is a
    proposition, where the major is related to the constructor at its projections). -/
theorem recStructAppsA (hE : EnvClosedA E) (hEL : EnvLevelsA E)
    (hN : EnvNormClosedA E) (hNCT : EnvNormCtorTypeA E) (hNL : EnvNormLevelsA E)
    {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {u : Level} (hW : EnvWfA (iotaIfaceA E) E₀)
    (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none) (hclT : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA)
    (hT : HasTyA E₀ (iotaIfaceA E) fm.arity [] fm.mtypeA (.sort u)) (fv : FamViewA fm)
    (cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)) (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length)
    (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs) (hpre : PrefixA (groupRecEnvA cs rec) E)
    (hfund : BaseFundA E₀ E (iotaIfaceA E) n ρ₀) (hfc : BaseFundConvA E₀ E (iotaIfaceA E) n ρ₀)
    (hR₀ : IotaRecHeadTypedA E₀ (iotaIfaceA E))
    (hpreG : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    (ih : EnvSemAt E (iotaIfaceA E) n ρ₀ (domA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry))))
    (hct : recHasCtorA (f + 1 + cs.length) rec.member = true)
    (hst : structGroupA (f + 1 + cs.length) rec.member = true)
    {gc : GroupCtorA (iotaIfaceA E) E₀ f fm fv} (hgc : cs.reverse = [gc]) (hnoidx : fv.indices = [])
    (hzF : levelIsZero fv.sort = true)
    (hplain : gc.view.fields = (plainTelA gc.view.fields).map plainA)
    (hzds : ∀ d ∈ plainTelA gc.view.fields, levelIsZero d.2 = true)
    (hnf : structFieldCountA rec.member = (plainTelA gc.view.fields).length)
    {ls ls' : List Level} (hl : ls.length = rec.member.arity) (hb : levelsBounded n ls = true)
    (hb' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (hwM : isZero (instLevel ls (rec.elim.motiveLevel fm.arity)) = false)
    {k : Nat} (hkM : ht ρ₀ (instLevel ls (rec.elim.motiveLevel fm.arity)) ≤ k)
    (hVP : ∀ {Γ : LCtxA} (qs qs' : List ExprA), Nonempty (CtxWfA E (iotaIfaceA E) n Γ) →
      qs.length = fm.nparamsA → qs'.length = fm.nparamsA →
      ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) (qs ++ []) (qs' ++ []) →
      ValidSubstA E (iotaIfaceA E) n ρ₀ k Γ (consListA qs SubstA.id) (consListA qs' SubstA.id)
        (instCtxA (ls.take fm.arity) (telCtxA fv.params)))
    (hVF : ∀ (Γ : LCtxA), Nonempty (CtxWfA E (iotaIfaceA E) n Γ) → ∀ (σ σ' : SubstA) (as as' : List ExprA),
      as.length = (plainTelA gc.view.fields).length → as'.length = (plainTelA gc.view.fields).length →
      ValidSubstA E (iotaIfaceA E) n ρ₀ k Γ σ σ' (instCtxA (ls.take fm.arity) (telCtxA fv.params)) →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA as σ)
        (telCtxA (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)) ++
          instCtxA (ls.take fm.arity) (telCtxA fv.params))) →
      Nonempty (SubstTyA E (iotaIfaceA E) n Γ (consListA as' σ')
        (telCtxA (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields)) ++
          instCtxA (ls'.take fm.arity) (telCtxA fv.params))) →
      ValidSubstA E (iotaIfaceA E) n ρ₀ k Γ (consListA as σ) (consListA as' σ')
        (telCtxA (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)) ++
          instCtxA (ls.take fm.arity) (telCtxA fv.params)))
    {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E (iotaIfaceA E) n Γ))
    {RT : ExprA → ExprA → Prop}
    (hRT : LRTyA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls rec.member.mtypeA) RT)
    (hr₁ : HasTyA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) ls) (instantiateLevelsA ls rec.member.mtypeA))
    (hr₂ : HasTyA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) ls') (instantiateLevelsA ls rec.member.mtypeA))
    (hrc : ConvA E (iotaIfaceA E) n Γ (.const (f + 1 + cs.length) ls) (.const (f + 1 + cs.length) ls')
      (instantiateLevelsA ls rec.member.mtypeA))
    {as as' : List ExprA}
    (hrel : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls rec.member.mtypeA) as as')
    (hlen : as.length = fm.nparamsA + 1 + cs.length + fv.indices.length + 1)
    {Cc : ExprA} (hC : applyTelA as (instantiateLevelsA ls rec.member.mtypeA) = some Cc) :
    LRRelA E (iotaIfaceA E) n ρ₀ k Γ Cc (foldAppsA (.const (f + 1 + cs.length) ls) as)
      (foldAppsA (.const (f + 1 + cs.length) ls') as') := by
  have hI := iotaFnA_lift hE hN
  have hIS := iotaFnA_subst hE hN
  have hR := iotaFnA_recHead E
  have hIL := iotaFnA_levels hEL hNL
  have hE₀ := envWfA_closed hW
  have hEL₀ := envWfA_levels hW
  obtain ⟨hΓ'⟩ := hΓ
  have hcs1 : cs.length = 1 := by rw [← List.length_reverse, hgc]; rfl
  have hgcm : gc ∈ cs := List.mem_reverse.mp (by rw [hgc]; exact List.mem_singleton_self gc)
  obtain ⟨hrm, hfm, _⟩ := members_groupRecA hfresh hlay hpre
  have hres0 : gc.view.res = [] :=
    List.eq_nil_of_length_eq_zero (by rw [gc.view.res_length, hnoidx]; rfl)
  have hlF : (ls.take fm.arity).length = fm.arity := by
    rw [List.length_take, hl, rec.harity]; exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hbF : levelsBounded n (ls.take fm.arity) = true := levelsBounded_take ls _ hb
  have hls' : ls'.length = rec.member.arity := (eqNList_length ls ls' heq).symm.trans hl
  have hlF' : (ls'.take fm.arity).length = fm.arity := by
    rw [List.length_take, hls', rec.harity]; exact Nat.min_eq_left (Nat.le_add_right _ _)
  have hbF' : levelsBounded n (ls'.take fm.arity) = true := levelsBounded_take ls' _ hb'
  have heqF : eqNList (ls.take fm.arity) (ls'.take fm.arity) := eqNList_take ls ls' _ heq
  -- the arguments: the parameters, the motive, the one minor, no index, the major
  have hrel' := hrel
  rw [recTelA hEL hfm rec hl] at hrel'
  obtain ⟨qs, qs', mot, mot', x, x', ms, ms', is, is', rfl, rfl, hqs, hqs', hms, hms', his, his', hpar, hmot,
      hmin, hidx, hmaj, happ⟩ :=
    recArgsSplitPA _ _ _ _ _ _ _ _ hrel'
      (by simp only [List.length_map, List.length_reverse, instDomsA_length, fv.nparams]; omega)
  have hidx0 : instDomsA (ls.take fm.arity) fv.indices = [] := by rw [hnoidx]; rfl
  obtain rfl : is = [] := List.eq_nil_of_length_eq_zero (by rw [his, hidx0]; rfl)
  obtain rfl : is' = [] := List.eq_nil_of_length_eq_zero (by rw [his', hidx0]; rfl)
  have hcd : (cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)) =
      [(gc.ref, (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA, [])] := by
    rw [hgc]
    simp only [List.map_cons, List.map_nil, GroupCtorA.minorData, MinorDataA.inst, hres0]
    rw [(congrArg (List.map (FieldA.instLevels (ls.take fm.arity))) hplain).trans (map_plainA_instLevels _ _)]
  have hcd1 : ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length = 1 := by
    rw [hcd]; rfl
  obtain ⟨mn, rfl⟩ : ∃ mn, ms = [mn] := by
    match ms, hms.trans hcd1 with
    | [mn], _ => exact ⟨mn, rfl⟩
  obtain ⟨mn', rfl⟩ : ∃ mn', ms' = [mn'] := by
    match ms', hms'.trans hcd1 with
    | [mn'], _ => exact ⟨mn', rfl⟩
  have hqsN : qs.length = fm.nparamsA := by rw [hqs, instDomsA_length, fv.nparams]
  have hqsN' : qs'.length = fm.nparamsA := by rw [hqs', instDomsA_length, fv.nparams]
  -- the minor, at its domain: the Π-telescope over the fields
  have hc0 : 0 < ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity))).length := by
    rw [hcd1]; exact Nat.zero_lt_one
  have hMT : ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)))[0]'hc0 =
      (gc.ref, (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA, []) := by
    have h : ((cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls.take fm.arity)))[0]? =
        some (gc.ref, (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA, []) := by
      rw [hcd]; rfl
    obtain ⟨_, h'⟩ := List.getElem?_eq_some_iff.mp h
    exact h'
  have hmin0 := hmin 0 (by simp) (by simp) hc0
  rw [hMT, minorTyA_plain_eq _ _ _ _ _ _ qs _ hqs, instDomsA_length] at hmin0
  -- the motive at the major's binder; the family application typed at its sort, which is zero
  have hmP := motPiA ⟨hΓ'⟩ hqs hmot (hidx (.sort .zero) .zero) his
  obtain ⟨⟨hg₀⟩, _⟩ := LRRelA_hasTy hmP
  have hg : HasTyA E (iotaIfaceA E) n Γ mot (.pi (foldAppsA (.const f (ls.take fm.arity)) (qs ++ []))
      (instLevel (ls.take fm.arity) fv.sort) (.sort (instLevel ls (rec.elim.motiveLevel fm.arity)))
      (.succ (instLevel ls (rec.elim.motiveLevel fm.arity)))) := hg₀
  obtain ⟨RP, hRP⟩ := LRRelA_valid hmP
  rw [LRTyA_eq] at hRP
  obtain ⟨_, ⟨tP⟩⟩ := tyKA_hasTy hRP
  obtain ⟨⟨tQ⟩, _⟩ := hasTyA_pi_inv tP
  have hwF0 : eqN (instLevel (ls.take fm.arity) fv.sort) .zero :=
    (levelIsZero_iff _).mp (levelIsZero_instLevel _ hzF)
  have tQ0 := hasTyA_of_tyConvA tQ (tyConvA_sorts Γ hwF0)
  have hnr : fm.mclass ≠ .recursorM := by rw [hcls]; exact fun h => MemberClass.noConfusion h
  have hTQn : hStepFnA E (iotaIfaceA E).fn Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) = none :=
    hStepFnA_constSpine_none hR hfm (Or.inr hnobody) hnr Γ (ls := ls.take fm.arity) _ (by rw [foldAppsA_const_head])
  have hD0 : (piDomsA fm.mtypeA).length = (instDomsA (ls.take fm.arity) (fv.params ++ fv.indices)).length := by
    rw [fv.stored, piDomsA_piTelA]
    simp [instDomsA, piDomsA]
  have hTQP : IsPropTy E (iotaIfaceA E) Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) :=
    (isPropTy_famApp_iff hfm fv.piBody (ls.take fm.arity) (qs ++ [])).mpr
      ⟨hlF, by rw [hD0, List.append_nil, hqs, hnoidx]; simp [instDomsA], (isZero_iff_eqN_zero _).mpr hwF0⟩
  have hTK := TyKA.prop (E := E) (I := iotaIfaceA E) (n := n) (ρ₀ := ρ₀) (k := k)
    (LE := fun j _ => LREqA E (iotaIfaceA E) n ρ₀ j) (LT := fun j _ => LRTyA E (iotaIfaceA E) n ρ₀ j)
    (whTyA_of_hasTy tQ) hTQn hTQP
  rw [← LRTyA_eq] at hTK
  obtain ⟨⟨tx⟩, ⟨tx'⟩⟩ := LRRelA_hasTy hmaj
  -- the parameters: related along the left's family type; the right's, along their own
  have hqF : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA)
      (qs ++ []) (qs' ++ []) := by
    rw [List.append_nil, List.append_nil, fv.inst_split]; exact hpar _ _
  obtain ⟨KR, hKR⟩ := paramSubstA hfund hfc hNCT hN hE₀ hE hI hR₀ hEL₀ hIL fv hclT hT hbF hbF' hlF hlF' heqF
  have hVR := hKR (max KR k) (Nat.le_max_left _ _) qs qs' [] [] (Nat.le_max_right _ _) ⟨hΓ'⟩ hqsN hqsN' hqF
    [] (Or.inl rfl)
  simp only [map_wkExprA_nil] at hVR
  have hVRR := ValidSubstA_refl_right hNCT hVR
  rw [← telCtxA_instDomsA] at hVRR
  have hqFR : ArgsRelKA E (iotaIfaceA E) n ρ₀ (max KR k) Γ (instantiateLevelsA (ls'.take fm.arity) fm.mtypeA)
      (qs' ++ []) (qs' ++ []) := by
    rw [List.append_nil, fv.inst_split]
    exact argsRelKA_of_validSubst hNCT (instDomsA (ls'.take fm.arity) fv.params) _ _ qs' qs'
      (by rw [instDomsA_length, fv.nparams]; exact hqsN') (by rw [instDomsA_length, fv.nparams]; exact hqsN') hVRR
  -- the two sides
  obtain ⟨⟨hSL⟩, hCL, hPL, hXL⟩ := structSideA hE hEL hN hNCT hNL hW hclT hT fv cs hfresh hlay rec hpre hfund hfc hR₀ hpreG
    ih hst hgc hnoidx hplain hzds hl hb hΓ' hqsN (argsRelKA_refl_left hNCT hqF)
  obtain ⟨⟨hSR⟩, _, hPR, _⟩ := structSideA hE hEL hN hNCT hNL hW hclT hT fv cs hfresh hlay rec hpre hfund hfc hR₀ hpreG
    ih hst hgc hnoidx hplain hzds hls' hb' hΓ' hqsN' hqFR
  -- the left's projections of the major and of the constructor at them
  have tx₀ : HasTyA E (iotaIfaceA E) n Γ x (foldAppsA (.const f (ls.take fm.arity)) qs) := by
    rw [List.append_nil] at tx; exact tx
  have hlenπ : ∀ y, (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs
      (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort)
      (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)))
      y (plainTelA gc.view.fields).length 0
      (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)))
        (.app (liftNA (plainTelA gc.view.fields).length mot)
          (foldAppsA (.const gc.ref (ls.take fm.arity))
            (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length)))
        (instLevel ls (rec.elim.motiveLevel fm.arity))).1).length = (plainTelA gc.view.fields).length := by
    intro y
    have h := structProjsA_length (f + 1 + cs.length) (motZeroLevelsA ls) qs
      (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort)
      (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) y
      (.app (liftNA (plainTelA gc.view.fields).length mot)
          (foldAppsA (.const gc.ref (ls.take fm.arity))
            (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length)))
      (instLevel ls (rec.elim.motiveLevel fm.arity))
      (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) 0 SubstA.id
    rw [substA_id, substTelA_length, instDomsA_length] at h
    exact h
  have hlenπ' : ∀ y, (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls') qs' (foldAppsA (.const f (ls'.take fm.arity)) qs') (instLevel (ls'.take fm.arity) fv.sort) (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) y (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot') (foldAppsA (.const gc.ref (ls'.take fm.arity)) (qs'.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls' (rec.elim.motiveLevel fm.arity))).1).length = (plainTelA gc.view.fields).length := by
    intro y
    have h := structProjsA_length (f + 1 + cs.length) (motZeroLevelsA ls') qs' (foldAppsA (.const f (ls'.take fm.arity)) qs') (instLevel (ls'.take fm.arity) fv.sort) (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) y (.app (liftNA (plainTelA gc.view.fields).length mot') (foldAppsA (.const gc.ref (ls'.take fm.arity)) (qs'.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls' (rec.elim.motiveLevel fm.arity)) (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) 0 SubstA.id
    rw [substA_id, substTelA_length, instDomsA_length] at h
    exact h
  have hPx := hPL x (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity)) tx₀
  obtain ⟨hcx⟩ := hCL (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) (hlenπ x) hPx
  have hPcx := hPL (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity)) hcx
  -- the right's major, at its own family application
  obtain ⟨KF, hKF⟩ := famHeadsA hfc hE₀ hI hR₀ hEL₀ hIL hfm hT hbF hbF' hlF hlF' heqF
  obtain ⟨_, _, _, ⟨cff⟩⟩ := hKF (max KF k) (Nat.le_max_left _ _) Γ ⟨hΓ'⟩
  have hPqq : ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) qs qs' := by
    have h := convArgsA_of_argsRelKA hqF
    simpa only [List.append_nil] using h
  have happF : applyTelA qs (instantiateLevelsA (ls.take fm.arity) fm.mtypeA) = some (.sort (instLevel (ls.take fm.arity) fv.sort)) := by
    rw [fv.applyTel_params _ qs hqsN, FamViewA.idxTelA, hnoidx]; rfl
  obtain ⟨cFF⟩ := convA_spine hE hI hR hIS hΓ' hPqq ⟨cff⟩ _ happF
  have hwF0' : eqN (instLevel (ls'.take fm.arity) fv.sort) .zero := (levelIsZero_iff _).mp (levelIsZero_instLevel _ hzF)
  have hww : eqN (instLevel (ls.take fm.arity) fv.sort) (instLevel (ls'.take fm.arity) fv.sort) := eqNA_trans hwF0 (eqNA_symm hwF0')
  have tx'R : HasTyA E (iotaIfaceA E) n Γ x' (foldAppsA (.const f (ls'.take fm.arity)) qs') := by
    rw [List.append_nil] at tx'
    exact .conv Γ x' _ _ _ _ tx' hSL hww hSR (convA_of_tyConvA cFF (tyConvA_sorts Γ hww))
  have hPx' := hPR x' (.app (liftNA (plainTelA gc.view.fields).length mot') (foldAppsA (.const gc.ref (ls'.take fm.arity)) (qs'.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls' (rec.elim.motiveLevel fm.arity)) tx'R
  -- the two projection lists: a valid pair along the fields, so related along the minor's domain
  have hVPq := hVP qs qs' ⟨hΓ'⟩ hqsN hqsN' hqF
  have hVx := hVF Γ ⟨hΓ'⟩ (consListA qs SubstA.id) (consListA qs' SubstA.id) (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls') qs' (foldAppsA (.const f (ls'.take fm.arity)) qs') (instLevel (ls'.take fm.arity) fv.sort) (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) x' (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot') (foldAppsA (.const gc.ref (ls'.take fm.arity)) (qs'.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls' (rec.elim.motiveLevel fm.arity))).1) (hlenπ x) (hlenπ' x') hVPq
    (by rw [← telCtxA_instDomsA]; exact hPx) (by rw [← telCtxA_instDomsA]; exact hPx')
  have hArgs := argsRelKA_minorFieldsA (E := E) (I := iotaIfaceA E) (n := n) (ρ₀ := ρ₀) (k := k) f gc.ref (ls.take fm.arity)
    (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity)) [] (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)) (instCtxA (ls.take fm.arity) (telCtxA fv.params)) qs mot [] (consListA qs SubstA.id) (consListA qs' SubstA.id) (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls') qs' (foldAppsA (.const f (ls'.take fm.arity)) qs') (instLevel (ls'.take fm.arity) fv.sort) (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) x' (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot') (foldAppsA (.const gc.ref (ls'.take fm.arity)) (qs'.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls' (rec.elim.motiveLevel fm.arity))).1)
    (by rw [hlenπ x, instDomsA_length]) (by rw [hlenπ' x', instDomsA_length]) hVx
  rw [minorFieldsA_plain_piTel, instDomsA_length] at hArgs
  have hpiT : IsPiTelA (plainTelA gc.view.fields).length (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1 := by
    have h := isPiTelA_minorFieldsA f gc.ref (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity)) [] hwM ((instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA) qs mot [] (consListA qs SubstA.id)
    rw [minorArityA_plainA, minorFieldsA_plain_piTel, instDomsA_length] at h
    exact h
  have eDm : (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1 = (minorFieldsA f gc.ref (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity)) qs mot [] (consListA qs SubstA.id) ((instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA) []).1 := by
    rw [minorFieldsA_plain_piTel, instDomsA_length]
  have hCapp : ∀ y, y.length = (plainTelA gc.view.fields).length → applyTelA y (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1 =
      some (.app mot (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ y))) := by
    intro y hy
    rw [eDm, applyTelA_minorFieldsA_plain _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hy, instDomsA_length])]
    simp only [minorFieldsA, List.map_nil, List.nil_append]
    rfl
  have hApps := LRRelA_apps ⟨hΓ'⟩ hArgs (plainTelA gc.view.fields).length (Nat.le_of_eq (hlenπ x)) hpiT hmin0 _ (hCapp _ (hlenπ x))
  -- the major and the constructor at its projections: related at the proposition; the motive carries them
  have tcx : HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) := by
    rw [List.append_nil]; exact hcx
  have hxc : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) x (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) :=
    LRRelA.of hTK ⟨⟨tx⟩, ⟨tcx⟩, ⟨.irr Γ _ x _ tQ0 tx tcx⟩⟩
  have hMM := motRelA ⟨hΓ'⟩ hqs (LRRelA_refl_left hNCT hmot) (B := .sort .zero) (w := .zero) (is := []) (is' := [])
    (.nil _) his hxc
  obtain ⟨hEqM, _, _⟩ := (LRRelA_sort_elim' hMM).1 k hkM
  have hred : LRRelA E (iotaIfaceA E) n ρ₀ k Γ (foldAppsA mot ([] ++ [x])) (foldAppsA mn (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))
      (foldAppsA mn' (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls') qs' (foldAppsA (.const f (ls'.take fm.arity)) qs') (instLevel (ls'.take fm.arity) fv.sort) (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) x' (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot') (foldAppsA (.const gc.ref (ls'.take fm.arity)) (qs'.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls' (rec.elim.motiveLevel fm.arity))).1)) :=
    LRRelA_transport' hNCT (LREqA_symm hNCT hEqM) hApps
  obtain ⟨⟨tmn⟩, ⟨tmn'⟩⟩ := LRRelA_hasTy hred
  -- the spines below the major, typed at the major's binder (as at a unit group)
  have hfull : ArgsRelKA E (iotaIfaceA E) n ρ₀ k Γ (instantiateLevelsA ls rec.member.mtypeA)
      (qs ++ [mot] ++ [mn] ++ [x]) (qs' ++ [mot'] ++ [mn'] ++ [x']) := by
    have e1 : qs ++ ([mot] ++ [mn] ++ [] ++ [x]) = qs ++ [mot] ++ [mn] ++ [x] := by simp
    have e2 : qs' ++ ([mot'] ++ [mn'] ++ [] ++ [x']) = qs' ++ [mot'] ++ [mn'] ++ [x'] := by simp
    rw [e1, e2] at hrel
    exact hrel
  obtain ⟨⟨tL⟩, ⟨tR⟩, ⟨cLR⟩, _⟩ := spineConvA hE hI hNCT ⟨hΓ'⟩ hfull _
    (by simp only [List.length_append, List.length_singleton, hqsN, hcs1, hnoidx, List.length_nil]; omega)
    (recPiTelA hEL hfm rec hl hwM) hRT hr₁ hr₂ hrc Cc
    (by rw [show qs ++ [mot] ++ [mn] ++ [x] = qs ++ ([mot] ++ [mn] ++ [] ++ [x]) by simp]; exact hC)
  obtain ⟨Tp, hTp, hpreRel, _⟩ := argsRelKA_append_inv (xs := qs ++ [mot] ++ [mn])
    (xs' := qs' ++ [mot'] ++ [mn']) (ys := [x]) (ys' := [x'])
    (by simp only [List.length_append, List.length_singleton, hqs, hqs']) hfull
  obtain ⟨B, hB, hBx⟩ := applyTelA_recPrefixA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params)
    (instDomsA (ls.take fm.arity) fv.indices) (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity)) (instLevel ls (rec.elim.motiveLevel fm.arity)) _ qs mot [mn] [] hqs hms his
  rw [← recTelA hEL hfm rec hl, show qs ++ ([mot] ++ [mn] ++ []) = qs ++ [mot] ++ [mn] by simp] at hB
  rw [hB] at hTp
  injection hTp with hTp
  subst hTp
  obtain ⟨⟨tH⟩, ⟨tH'⟩, _, ⟨RQ, hRQ⟩⟩ := spineConvA hE hI hNCT ⟨hΓ'⟩ hpreRel _
    (by simp only [List.length_append, List.length_singleton, hqsN, hcs1, hnoidx, List.length_nil]; omega)
    (recPiTelA hEL hfm rec hl hwM) hRT hr₁ hr₂ hrc _ hB
  rw [LRTyA_eq] at hRQ
  obtain ⟨_, ⟨tPB⟩⟩ := tyKA_hasTy hRQ
  obtain ⟨_, ⟨hBty⟩⟩ := hasTyA_pi_inv tPB
  rw [recTelA hEL hfm rec hl, happ] at hC
  injection hC with hC
  subst hC
  -- the spine facts at both sides
  have hpc := piCountA_groupRecA rec
  have hlenP : (qs ++ [mot] ++ [mn]).length + 1 = piCountA rec.member.mtypeA := by
    rw [hpc]; simp only [List.length_append, List.length_singleton, hqsN, hcs1, hnoidx, List.length_nil]
  have hlenP' : (qs' ++ [mot'] ++ [mn']).length + 1 = piCountA rec.member.mtypeA := by
    rw [hpc]; simp only [List.length_append, List.length_singleton, hqsN', hcs1, hnoidx, List.length_nil]
  have hqP : qs.length = fv.params.length := by rw [hqs, instDomsA_length]
  have hprel : (qs ++ [mot] ++ [mn]).length = fv.params.length + 1 + cs.length + fv.indices.length := by
    simp only [List.length_append, List.length_singleton, hqP, hcs1, hnoidx, List.length_nil]
  have hmin1 : (qs ++ [mot] ++ [mn])[fv.params.length + 1]? = some mn := by
    rw [← hqP, List.append_assoc, List.getElem?_append_right (by omega),
      show qs.length + 1 - qs.length = 1 by omega]
    rfl
  have hfn := hStepFnA_recSpine_below Γ hrm rec.hcls ls (qs ++ [mot] ++ [mn]) (by omega)
  have hfn' := hStepFnA_recSpine_below Γ hrm rec.hcls ls' (qs' ++ [mot'] ++ [mn']) (by omega)
  have hgc0 : cs.reverse[0]? = some gc := by rw [hgc]; rfl
  -- the struct arm at the two spines
  have hT_L : instantiateLevelsA ls rec.member.mtypeA = (piTelA (recDomsA f (ls.take fm.arity) (instDomsA (ls.take fm.arity) fv.params) []
      (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity)) [(gc.ref, (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).map plainA, [])]) (recBodyA 0 1) (instLevel ls (rec.elim.motiveLevel fm.arity))).1 := by
    rw [recTelA hEL hfm rec hl, hcd, hnoidx]; rfl
  have hcd' : (cs.reverse.map GroupCtorA.minorData).map (MinorDataA.inst (ls'.take fm.arity)) =
      [(gc.ref, (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields)).map plainA, [])] := by
    rw [hgc]
    simp only [List.map_cons, List.map_nil, GroupCtorA.minorData, MinorDataA.inst, hres0]
    rw [(congrArg (List.map (FieldA.instLevels (ls'.take fm.arity))) hplain).trans (map_plainA_instLevels _ _)]
  have hT_R : instantiateLevelsA ls' rec.member.mtypeA = (piTelA (recDomsA f (ls'.take fm.arity) (instDomsA (ls'.take fm.arity) fv.params) []
      (instLevel (ls'.take fm.arity) fv.sort) (instLevel ls' (rec.elim.motiveLevel fm.arity)) [(gc.ref, (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields)).map plainA, [])]) (recBodyA 0 1) (instLevel ls' (rec.elim.motiveLevel fm.arity))).1 := by
    rw [recTelA hEL hfm rec hls', hcd', hnoidx]; rfl
  have hnfI : structFieldCountA rec.member = (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields)).length := by rw [hnf, instDomsA_length]
  have hnfI' : structFieldCountA rec.member = (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields)).length := by rw [hnf, instDomsA_length]
  have hsA : ∀ y, structArmA E (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) y = some (foldAppsA mn (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) y (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)) := by
    intro y
    have h := structArmA_recSpineA hrm hst hT_L hnfI hqs mot mn y
    rw [instDomsA_length] at h
    exact h
  have hsA' : structArmA E (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) x' = some (foldAppsA mn' (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls') qs' (foldAppsA (.const f (ls'.take fm.arity)) qs') (instLevel (ls'.take fm.arity) fv.sort) (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) x' (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot') (foldAppsA (.const gc.ref (ls'.take fm.arity)) (qs'.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls' (rec.elim.motiveLevel fm.arity))).1)) := by
    have h := structArmA_recSpineA hrm hst hT_R hnfI' (by rw [hqs', instDomsA_length, instDomsA_length]) mot' mn' x'
    rw [instDomsA_length] at h
    exact h
  -- the redexes, typed at the left's type
  obtain ⟨⟨tMx⟩, ⟨tMc⟩, ⟨tyXC⟩⟩ := appSortConvA hg tx tcx (.irr Γ _ x _ tQ0 tx tcx)
  obtain ⟨⟨tMx'⟩, _, ⟨tyX'X⟩⟩ := appSortConvA hg tx' tx (.irr Γ _ x' x tQ0 tx' tx)
  have tLx : HasTyA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) x) (foldAppsA mot ([] ++ [x])) := by
    have h1 := HasTyA.app Γ _ x _ B _ _ (instLevel ls (rec.elim.motiveLevel fm.arity)) hBty (by rw [hBx]; exact tMx) tH tx
    rw [hBx] at h1
    exact h1
  have tLc : HasTyA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)))) (foldAppsA mot ([] ++ [x])) := by
    have h1 := HasTyA.app Γ _ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) _ B _ _ (instLevel ls (rec.elim.motiveLevel fm.arity)) hBty (by rw [hBx]; exact tMc) tH tcx
    rw [hBx] at h1
    exact hasTyA_of_tyConvA h1 tyXC.symm
  have tRx : HasTyA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) x') (foldAppsA mot ([] ++ [x])) := by
    have h1 := HasTyA.app Γ _ x' _ B _ _ (instLevel ls (rec.elim.motiveLevel fm.arity)) hBty (by rw [hBx]; exact tMx') tH' tx'
    rw [hBx] at h1
    exact hasTyA_of_tyConvA h1 tyX'X
  -- ι at the constructor at the major's projections: the minor at the constructor's projections
  have hfl : gc.view.fields.length = (plainTelA gc.view.fields).length := by
    have h := congrArg List.length hplain
    rwa [List.length_map] at h
  have hιF := iotaFnA_groupRecA hfresh hlay hcls hpre hgc0 (ls := ls) (lsC := (ls.take fm.arity))
    (pre := qs ++ [mot] ++ [mn]) (ps₁ := qs) (minor := mn) hprel hl hqP ((hlenπ x).trans hfl.symm) hmin1
  rw [foldAppsA_snoc, congrArg (List.map FieldA.shape) hplain,
    (congrArg (fun fs => (fs.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity))) hplain).trans
      ((congrArg (·.map (FieldA.instLevels (ls.take fm.arity))) (map_norm_plainA _)).trans
        (map_plainA_instLevels _ _)),
    rhsArgsA_plain _ _ _ _ _ _ _ _ _ _ _ _ _ ((hlenπ x).trans (instDomsA_length _ _).symm)
      (instDomsA_length _ _).symm] at hιF
  obtain ⟨⟨tmn0⟩, _⟩ := LRRelA_hasTy hmin0
  obtain ⟨hcs⟩ := hXL (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) (hlenπ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)))) (hlenπ x) hPcx hPx
  have hCA := convArgsA_minorFieldsA (E := E) (I := iotaIfaceA E) (n := n) f gc.ref (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort) (instLevel ls (rec.elim.motiveLevel fm.arity)) [] (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))
    (telCtxA (instDomsA (ls.take fm.arity) fv.params)) qs mot [] (consListA qs SubstA.id) (consListA qs SubstA.id) (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)
    (by rw [hlenπ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))), instDomsA_length]) (by rw [hlenπ x, instDomsA_length]) hcs
  rw [minorFieldsA_plain_piTel, instDomsA_length] at hCA
  obtain ⟨c3⟩ := convA_spine hE hI hR hIS hΓ' hCA ⟨.refl _ _ _ tmn0⟩ _ (hCapp _ (hlenπ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)))))
  obtain ⟨hccx⟩ := hCL (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1) (hlenπ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)))) hPcx
  have tccx : HasTyA E (iotaIfaceA E) n Γ (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) (foldAppsA (.const f (ls.take fm.arity)) (qs ++ [])) := by
    rw [List.append_nil]; exact hccx
  obtain ⟨_, _, ⟨tyXCC⟩⟩ := appSortConvA hg tx tccx (.irr Γ _ x _ tQ0 tx tccx)
  have c3T : ConvA E (iotaIfaceA E) n Γ (foldAppsA mn (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)) (foldAppsA mn (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)) (foldAppsA mot ([] ++ [x])) :=
    convA_of_tyConvA c3 tyXCC.symm
  -- the left redex converts to its reduct: irrelevance to the constructor, then ι there (the struct rule, carrying
  -- the per-field irrelevance back to the arm's reduct)
  have c1 : ConvA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) x) (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)))) (foldAppsA mot ([] ++ [x])) := by
    have c := ConvA.app Γ _ _ x (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs ++ (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1))) _ B _ _ (.refl Γ _ _ tH) (.irr Γ _ x _ tQ0 tx tcx) hBty
      (by rw [hBx]; exact tLc)
    rw [hBx] at c
    exact c
  have c2 := ConvA.structIota (E := E) (I := iotaIfaceA E) (n := n) Γ _ _ _ _ _
    (recAtMajorA_recSpine hrm rec.hcls hct ls _ hlenP) (hsA _) hιF tLc tmn (.symm _ _ _ _ c3T)
  have cL : ConvA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) x) (foldAppsA mn (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)) (foldAppsA mot ([] ++ [x])) :=
    .trans _ _ _ _ _ c1 c2
  -- the head steps: the struct arm at every major (W-1 (e))
  have sL : TyHRedA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) x) (foldAppsA mn (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls) qs (foldAppsA (.const f (ls.take fm.arity)) qs) (instLevel (ls.take fm.arity) fv.sort) (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) x (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs SubstA.id) (instDomsA (ls.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot) (foldAppsA (.const gc.ref (ls.take fm.arity)) (qs.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls (rec.elim.motiveLevel fm.arity))).1)) (foldAppsA mot ([] ++ [x])) :=
    .kstruct Γ _ x _ _ (recAtMajorA_recSpine hrm rec.hcls hct ls _ hlenP) (hsA x) hfn cL tmn
  have cLR' : ConvA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls) (qs ++ [mot] ++ [mn])) x) (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) x') (foldAppsA mot ([] ++ [x])) := by
    rw [← foldAppsA_snoc, ← foldAppsA_snoc]; exact cLR
  obtain ⟨cmm⟩ := LRRelA_conv hred
  have cR : ConvA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) x') (foldAppsA mn' (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls') qs' (foldAppsA (.const f (ls'.take fm.arity)) qs') (instLevel (ls'.take fm.arity) fv.sort) (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) x' (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot') (foldAppsA (.const gc.ref (ls'.take fm.arity)) (qs'.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls' (rec.elim.motiveLevel fm.arity))).1)) (foldAppsA mot ([] ++ [x])) :=
    .trans _ _ _ _ _ (.symm _ _ _ _ cLR') (.trans _ _ _ _ _ cL cmm)
  have sR : TyHRedA E (iotaIfaceA E) n Γ (.app (foldAppsA (.const (f + 1 + cs.length) ls') (qs' ++ [mot'] ++ [mn'])) x') (foldAppsA mn' (structProjsA (f + 1 + cs.length) (motZeroLevelsA ls') qs' (foldAppsA (.const f (ls'.take fm.arity)) qs') (instLevel (ls'.take fm.arity) fv.sort) (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) x' (plainTelA gc.view.fields).length 0 (piTelA (substTelA (consListA qs' SubstA.id) (instDomsA (ls'.take fm.arity) (plainTelA gc.view.fields))) (.app (liftNA (plainTelA gc.view.fields).length mot') (foldAppsA (.const gc.ref (ls'.take fm.arity)) (qs'.map (liftNA (plainTelA gc.view.fields).length) ++ paramLocalsA (plainTelA gc.view.fields).length))) (instLevel ls' (rec.elim.motiveLevel fm.arity))).1)) (foldAppsA mot ([] ++ [x])) :=
    .kstruct Γ _ x' _ _ (recAtMajorA_recSpine hrm rec.hcls hct ls' _ hlenP') hsA' hfn' cR tmn'
  have h2 := LRRelA_expand_right hE hI ⟨⟨tRx⟩, ⟨sR⟩⟩ (LRRelA_expand_left hE hI ⟨⟨tLx⟩, ⟨sL⟩⟩ hred)
  rw [show qs ++ ([mot] ++ [mn] ++ [] ++ [x]) = qs ++ [mot] ++ [mn] ++ [x] by simp,
    show qs' ++ ([mot'] ++ [mn'] ++ [] ++ [x']) = qs' ++ [mot'] ++ [mn'] ++ [x'] by simp,
    foldAppsA_snoc (.const _ ls) (qs ++ [mot] ++ [mn]) x, foldAppsA_snoc (.const _ ls') (qs' ++ [mot'] ++ [mn']) x']
  exact h2

end StructSide

/-! ## (8) THE RECURSORS' CLAUSE -/

section RecClause
variable {E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE RECURSOR'S CLAUSE (`EnvSemClauseA`) at a group's recursor, at the concrete ι, under the profile
    (small indices, Prop families with a constructor eliminating into Prop only), with the clauses of the
    base, the family and the constructors in hand: the recursor's type is valid and its two heads typed
    and convertible (`famHeadsA` on its typing in the group's environment). At a zero motive universe
    the type is a proposition (`recTypeA_propTy`), where the heads are related by the `prop` clause.
    Otherwise the heads are related by the telescope lemma: every pair of full applications to related
    arguments is related at their type. At a group without a constructor (O1-a) they are extended
    neutrals, related by reflection. At a unit group (O1-b-1) every full application steps to its minor,
    and the two minors are related at the redex's type (`recUnitAppsA`). At a struct group (W-1 (c)) every
    full application steps to its minor at the major's projections, and the two reducts are related at the
    redex's type (`recStructAppsA`). At any other group with a constructor the family is a Type family
    (`PropElimStructA`), and they are related by the core induction on the major's canonical fixed point
    (`RecAtA.core`). -/
theorem recSemClauseA (hE : EnvClosedA E) (hEL : EnvLevelsA E) (hN : EnvNormClosedA E)
    (hNCT : EnvNormCtorTypeA E) (hNL : EnvNormLevelsA E) (hρ : PosValA ρ₀) (hS : SmallIndexProfileA E)
    (hPE : PropElimStructA E)
    {E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {u : Level} (hW : EnvWfA (iotaIfaceA E) E₀)
    (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none) (hclT : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA)
    (hT : HasTyA E₀ (iotaIfaceA E) fm.arity [] fm.mtypeA (.sort u)) (fv : FamViewA fm)
    (cs : List (GroupCtorA (iotaIfaceA E) E₀ f fm fv)) (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length)
    (rec : GroupRecA (iotaIfaceA E) E₀ f fm fv cs)
    (hfreshR : (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)).members (f + 1 + cs.length) = none)
    (hpre : PrefixA (groupRecEnvA cs rec) E)
    (hclo : CtorClosedA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E)
    (ih : EnvSemAt E (iotaIfaceA E) n ρ₀ (domA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)))) :
    EnvSemClauseA E (iotaIfaceA E) n ρ₀ (f + 1 + cs.length) rec.member := by
  intro ls ls' hl hb hb' heq
  have hI := iotaFnA_lift hE hN
  have hIS := iotaFnA_subst hE hN
  have hIL := iotaFnA_levels hEL hNL
  have hR := iotaFnA_recHead E
  have hpreG : PrefixA (groupEnvA E₀ f fm (cs.map GroupCtorA.entry)) E :=
    prefixA_trans (prefixA_extend _ _ _ hfreshR) hpre
  have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpreG
  have ih₀ : EnvSemAt E (iotaIfaceA E) n ρ₀ (domA E₀) := fun r m hD hres =>
    ih r m (hD.elim fun m₁ h => ⟨m₁, prefixA_groupEnvA hfresh r m₁ h⟩) hres
  obtain ⟨hfund, hfc⟩ := baseFundA_of hE hI hIS hNCT hN hR hρ hpre₀ ih₀
  obtain ⟨_, hfcG⟩ := baseFundA_of hE hI hIS hNCT hN hR hρ hpreG ih
  obtain ⟨hrm, hfm, _⟩ := members_groupRecA hfresh hlay hpre
  have hl' : ls'.length = rec.member.arity := (eqNList_length ls ls' heq).symm.trans hl
  -- the recursor's heads
  obtain ⟨K₀, hK₀⟩ := famHeadsA hfcG (fun r m h => hE r m (hpreG r m h)) hI (iotaRecHeadTypedA_prefix hpreG hR)
    (fun r m h => hEL r m (hpreG r m h)) hIL hrm rec.hT hb hb' hl hl' heq
  by_cases hz : isZero (instLevel ls (rec.elim.motiveLevel fm.arity)) = true
  · -- a zero motive universe: the recursor's type is a proposition
    refine ⟨K₀, fun k hk Δ hΔ => ?_⟩
    obtain ⟨⟨RT, hRT⟩, ⟨hr₁⟩, ⟨hr₂⟩, ⟨hrc⟩⟩ := hK₀ k hk Δ hΔ
    have hst : rec.member.mtypeA = recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
        (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData) := rec.stored
    obtain ⟨hn, hP⟩ := recTypeA_propTy (E := E) (I := iotaIfaceA E) ls f (canonLevelsA fm.arity) fv.params
      fv.indices fv.sort (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData) hz Δ
    rw [← hst] at hn hP
    have hRT' := hRT
    rw [LRTyA_eq] at hRT'
    obtain ⟨_, ⟨hTty⟩⟩ := tyKA_hasTy hRT'
    have hpr := TyKA.prop (E := E) (I := iotaIfaceA E) (n := n) (ρ₀ := ρ₀) (k := k)
      (LE := fun j _ => LREqA E (iotaIfaceA E) n ρ₀ j) (LT := fun j _ => LRTyA E (iotaIfaceA E) n ρ₀ j)
      (whTyA_of_hasTy hTty) hn hP
    rw [← LRTyA_eq] at hpr
    exact ⟨_, hpr, ⟨hr₁⟩, ⟨hr₂⟩, ⟨hrc⟩⟩
  · have hwM : isZero (instLevel ls (rec.elim.motiveLevel fm.arity)) = false := by simpa using hz
    cases hct : recHasCtorA (f + 1 + cs.length) rec.member
    next =>
      -- O1-a: a group without a constructor has no ι and no major arm, so every full application of its
      -- recursor is an extended neutral (`neutKA_recApp`), related by reflection at its type
      have hPT := recPiTelA hEL hfm rec hl hwM
      have hTcl : ∀ j, liftA j 1 (instantiateLevelsA ls rec.member.mtypeA) =
          instantiateLevelsA ls rec.member.mtypeA :=
        liftA_instantiateLevelsA_closed rec.hclT ls
      refine ⟨K₀, fun k hk Δ hΔ => ?_⟩
      obtain ⟨⟨RT, hRT⟩, ⟨hr₁⟩, ⟨hr₂⟩, ⟨hrc⟩⟩ := hK₀ k hk Δ hΔ
      refine ⟨RT, hRT, telIntroA hE hI hNCT hN _ hΔ hPT hRT ⟨hr₁⟩ ⟨hr₂⟩ ⟨hrc⟩ ?_⟩
      intro ρ hρw as as' hrel hlen Cc hC
      rw [wkExprA_closed hTcl] at hrel hC
      rw [wkExprA_const, wkExprA_const]
      obtain ⟨⟨RTρ, hRTρ⟩, ⟨hr₁ρ⟩, ⟨hr₂ρ⟩, ⟨hrcρ⟩⟩ := hK₀ k hk (wkCtxA ρ Δ) hρw.2
      obtain ⟨⟨tL⟩, ⟨tR⟩, ⟨cLR⟩, hA⟩ := spineConvA hE hI hNCT hρw.2 hrel _ (Nat.le_of_eq hlen) hPT hRTρ hr₁ρ
        hr₂ρ hrcρ Cc hC
      have hlen' : as'.length = as.length := (argsRelKA_length hrel).symm
      have hpc := piCountA_groupRecA rec
      have hne : as ≠ [] := fun h => by rw [h] at hlen; exact Nat.noConfusion hlen
      have hne' : as' ≠ [] := fun h => hne (List.eq_nil_of_length_eq_zero (by rw [← hlen', h]; rfl))
      obtain ⟨pre, x, rfl⟩ : ∃ pre x, as = pre ++ [x] :=
        ⟨as.dropLast, as.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
      obtain ⟨pre', x', rfl⟩ : ∃ pre x, as' = pre ++ [x] :=
        ⟨as'.dropLast, as'.getLast hne', (List.dropLast_concat_getLast hne').symm⟩
      simp only [List.length_append, List.length_singleton] at hlen hlen'
      exact LRRelA_reflect hE hI hA
        (neutKA_recApp hE hI hrm rec.hcls (ls := ls) (by omega) (Or.inr hct))
        (neutKA_recApp hE hI hrm rec.hcls (ls := ls') (by omega) (Or.inr hct)) ⟨tL⟩ ⟨tR⟩ ⟨cLR⟩
    by_cases hunit : unitGroupA (f + 1 + cs.length) rec.member = true
    · -- O1-b-1: a unit group: every full application steps to its minor (K-unit, or ι at the
      -- constructor), and the two minors are related at the redex's type (`recUnitAppsA`)
      have hfree : ∀ d ∈ fv.indices, ConstsInA (domA E₀) d.1 := by
        have hc := hasTyA_constsIn hT
        rw [fv.stored] at hc
        exact fun d hd => constsInA_piTelA_doms _ _ _ hc d (List.mem_append_right _ hd)
      obtain ⟨hcs1, hnoidx, hzF, hnf⟩ := unitShape_of_unitGroupA rec hfree hfresh.base hunit
      obtain ⟨gc, hgc⟩ : ∃ gc, cs.reverse = [gc] := by
        match cs.reverse, (List.length_reverse cs).trans hcs1 with
        | [gc], _ => exact ⟨gc, rfl⟩
      have hnf' : gc.view.fields = [] := hnf gc.minorData (by rw [hgc]; exact List.mem_singleton_self _)
      have hPT := recPiTelA hEL hfm rec hl hwM
      have hTcl : ∀ j, liftA j 1 (instantiateLevelsA ls rec.member.mtypeA) =
          instantiateLevelsA ls rec.member.mtypeA :=
        liftA_instantiateLevelsA_closed rec.hclT ls
      refine ⟨max K₀ (ht ρ₀ (instLevel ls (rec.elim.motiveLevel fm.arity))), fun k hk Δ hΔ => ?_⟩
      have hk₁ : K₀ ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
      obtain ⟨⟨RT, hRT⟩, ⟨hr₁⟩, ⟨hr₂⟩, ⟨hrc⟩⟩ := hK₀ k hk₁ Δ hΔ
      refine ⟨RT, hRT, telIntroA hE hI hNCT hN _ hΔ hPT hRT ⟨hr₁⟩ ⟨hr₂⟩ ⟨hrc⟩ ?_⟩
      intro ρ hρw as as' hrel hlen Cc hC
      rw [wkExprA_closed hTcl] at hrel hC
      rw [wkExprA_const, wkExprA_const]
      obtain ⟨⟨RTρ, hRTρ⟩, ⟨hr₁ρ⟩, ⟨hr₂ρ⟩, ⟨hrcρ⟩⟩ := hK₀ k hk₁ (wkCtxA ρ Δ) hρw.2
      exact recUnitAppsA hE hEL hN hNCT hNL hW hcls hnobody hclT hT fv cs hfresh hlay rec hpre hfund hfc
        (iotaRecHeadTypedA_prefix hpre₀ hR) hpreG ih hct hunit hgc hnoidx hzF hnf' hl hb heq hwM
        (Nat.le_trans (Nat.le_max_right _ _) hk) hρw.2 hRTρ hr₁ρ hr₂ρ hrcρ hrel hlen hC
    have hun : unitGroupA (f + 1 + cs.length) rec.member = false := by simpa using hunit
    by_cases hstr : structGroupA (f + 1 + cs.length) rec.member = true
    · -- W-1 (c): a struct group: every full application steps to its minor at the major's projections
      -- (K-struct, or ι at the constructor), and the two reducts are related at the redex's type
      -- (`recStructAppsA`); its two height thresholds, the parameters' valid substitution (`paramSubstA`)
      -- and the fields' (`validSubstA_propTel`), are taken here
      obtain ⟨gc, hgc, hnoidx, hzF, hplain, hzds, hnf⟩ := structCtorA_of_structGroupA rec hstr
      have hPT := recPiTelA hEL hfm rec hl hwM
      have hTcl : ∀ j, liftA j 1 (instantiateLevelsA ls rec.member.mtypeA) =
          instantiateLevelsA ls rec.member.mtypeA :=
        liftA_instantiateLevelsA_closed rec.hclT ls
      have hlF : (ls.take fm.arity).length = fm.arity := by
        rw [List.length_take, hl, rec.harity]; exact Nat.min_eq_left (Nat.le_add_right _ _)
      have hlF' : (ls'.take fm.arity).length = fm.arity := by
        rw [List.length_take, hl', rec.harity]; exact Nat.min_eq_left (Nat.le_add_right _ _)
      have hbF : levelsBounded n (ls.take fm.arity) = true := levelsBounded_take ls _ hb
      have hbF' : levelsBounded n (ls'.take fm.arity) = true := levelsBounded_take ls' _ hb'
      have hR₀ := iotaRecHeadTypedA_prefix hpre₀ hR
      obtain ⟨KP, hKP⟩ := paramSubstA hfund hfc hNCT hN (envWfA_closed hW) hE hI hR₀ (envWfA_levels hW) hIL fv hclT hT
        hbF hbF hlF hlF (eqNList_refl _)
      obtain ⟨hwfP⟩ := fv.paramsCtxWf hT
      obtain ⟨KV, hKV⟩ := validSubstA_propTel hfc hNCT (envWfA_closed hW) hI hR₀ (envWfA_levels hW) hIL hbF hbF'
        hlF hlF' (eqNList_take ls ls' _ heq) hwfP (telTyA_of_fieldsTyA gc.view.typed) hzds
      refine ⟨max (max K₀ KP) (max KV (ht ρ₀ (instLevel ls (rec.elim.motiveLevel fm.arity)))),
        fun k hk Δ hΔ => ?_⟩
      have hk₁ : K₀ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
      have hkP : KP ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
      have hkV : KV ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hk
      have hkM : ht ρ₀ (instLevel ls (rec.elim.motiveLevel fm.arity)) ≤ k :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk
      obtain ⟨⟨RT, hRT⟩, ⟨hr₁⟩, ⟨hr₂⟩, ⟨hrc⟩⟩ := hK₀ k hk₁ Δ hΔ
      refine ⟨RT, hRT, telIntroA hE hI hNCT hN _ hΔ hPT hRT ⟨hr₁⟩ ⟨hr₂⟩ ⟨hrc⟩ ?_⟩
      intro ρ hρw as as' hrel hlen Cc hC
      rw [wkExprA_closed hTcl] at hrel hC
      rw [wkExprA_const, wkExprA_const]
      obtain ⟨⟨RTρ, hRTρ⟩, ⟨hr₁ρ⟩, ⟨hr₂ρ⟩, ⟨hrcρ⟩⟩ := hK₀ k hk₁ (wkCtxA ρ Δ) hρw.2
      exact recStructAppsA hE hEL hN hNCT hNL hW hcls hnobody hclT hT fv cs hfresh hlay rec hpre hfund hfc hR₀ hpreG ih
        hct hstr hgc hnoidx hzF hplain hzds hnf hl hb hb' heq hwM hkM
        (fun qs qs' hΓ hq hq' hrq => by
          have h := hKP k hkP qs qs' [] [] (Nat.le_refl k) hΓ hq hq' hrq [] (wkOk₀A_nil _ _ _ _)
          rwa [map_wkExprA_nil, map_wkExprA_nil] at h)
        (hKV k hkV) hρw.2 hRTρ hr₁ρ hr₂ρ hrcρ hrel hlen hC
    have hns : structGroupA (f + 1 + cs.length) rec.member = false := by simpa using hstr
    -- a group with a constructor: under the profile a Type family; the telescope lemma, the core
    -- induction at every world
    have hUT : UniformType fv.sort := by
      rcases fv.profile with hUP | hUT
      · exfalso
        have he := elim_propOnly_of_propElimStructA hPE hfresh hlay hcls hpre hUP
          ((recHasCtorA_groupRecA rec).1 hct) hun hns
        have h0 : isZero (instLevel ls (rec.elim.motiveLevel fm.arity)) = true := by rw [he]; rfl
        rw [h0] at hwM
        exact Bool.noConfusion hwM
      · exact hUT
    have C : RecBaseA E₀ E n ρ₀ f fm fv cs :=
      { hfund := hfund, hfc := hfc, hE₀ := envWfA_closed hW, hE := hE, hEN := hN, hNCT := hNCT,
        hI := hI,
        hR₀ := iotaRecHeadTypedA_prefix hpre₀ hR, hEL₀ := envWfA_levels hW, hEL := hEL, hENL := hNL, hIL := hIL, hS := hS,
        hfm := hfm, hcls := hcls, hnobody := hnobody, hfresh := hfresh.base,
        hcensus := fun _ _ hc hk hf => groupCensusA hcls hfresh (ctorFamInA_of_envWfA hW) hclo hc hk hf,
        hcl := hclT, u := u, hT := hT, hUT := hUT, hR := hR,
        hCtor := fun gc hgc => ih gc.ref gc.member ⟨gc.member, members_groupEnvA_ctor hfresh hgc⟩
          (hpreG _ _ (members_groupEnvA_ctor hfresh hgc)),
        hgf := hfresh, hmemG := members_groupEnvA_family hfresh, hpre₀G := prefixA_groupEnvA hfresh, hpreG := hpreG,
        hEG := fun r m h => hE r m (hpreG r m h), hELG := fun r m h => hEL r m (hpreG r m h),
        hRG := iotaRecHeadTypedA_prefix hpreG hR, hfcG := hfcG }
    have hlF : (ls.take fm.arity).length = fm.arity := by
      rw [List.length_take, hl, rec.harity]; exact Nat.min_eq_left (Nat.le_add_right _ _)
    obtain ⟨KF, hKF⟩ := famHeadsA C.hfc C.hE₀ C.hI C.hR₀ C.hEL₀ C.hIL C.hfm C.hT (levelsBounded_take ls _ hb)
      (levelsBounded_take ls _ hb) hlF hlF (eqNListA_refl _)
    refine ⟨max (max K₀ KF) (max (ht ρ₀ (instLevel (ls.take fm.arity) fv.sort) + 1)
      (ht ρ₀ (instLevel ls (rec.elim.motiveLevel fm.arity)))), fun k hk Δ hΔ => ?_⟩
    have hk₁ : K₀ ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
    have hk₂ : KF ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
    have hkF : ht ρ₀ (instLevel (ls.take fm.arity) fv.sort) < k :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hk)
    have hkM : ht ρ₀ (instLevel ls (rec.elim.motiveLevel fm.arity)) ≤ k :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk
    obtain ⟨⟨RT, hRT⟩, ⟨hr₁⟩, ⟨hr₂⟩, ⟨hrc⟩⟩ := hK₀ k hk₁ Δ hΔ
    have hTcl : ∀ j, liftA j 1 (instantiateLevelsA ls rec.member.mtypeA) =
        instantiateLevelsA ls rec.member.mtypeA :=
      liftA_instantiateLevelsA_closed rec.hclT ls
    refine ⟨RT, hRT, telIntroA hE hI hNCT hN _ hΔ (recPiTelA C.hEL C.hfm rec hl hwM) hRT ⟨hr₁⟩ ⟨hr₂⟩ ⟨hrc⟩ ?_⟩
    intro ρ hρw as as' hrel hlen Cc hC
    rw [wkExprA_closed hTcl] at hrel hC
    rw [wkExprA_const, wkExprA_const]
    obtain ⟨⟨RTρ, hRTρ⟩, ⟨hr₁ρ⟩, ⟨hr₂ρ⟩, ⟨hrcρ⟩⟩ := hK₀ k hk₁ (wkCtxA ρ Δ) hρw.2
    obtain ⟨⟨RFρ, hRFρ⟩, ⟨hfFρ⟩, _, _⟩ := hKF k hk₂ (wkCtxA ρ Δ) hρw.2
    have hrel' := hrel
    rw [recTelA C.hEL C.hfm rec hl] at hrel'
    obtain ⟨qs, qs', mot, mot', x, x', ms, ms', is, is', rfl, rfl, hqs, hqs', hms, hms', his, his', hpar, hmot, hmin,
        hidx, hmaj, happ⟩ :=
      recArgsSplitPA _ _ _ _ _ _ _ _ hrel'
        (by simp only [List.length_map, List.length_reverse, instDomsA_length, fv.nparams]; omega)
    have hqsN : qs.length = fm.nparamsA := by rw [hqs, instDomsA_length, fv.nparams]
    have hqsN' : qs'.length = fm.nparamsA := by rw [hqs', instDomsA_length, fv.nparams]
    have R : RecAtA C rec ls ls' k (wkCtxA ρ Δ) qs qs' mot mot' ms ms' :=
      { hΓ := hρw.2, hgf := hfresh, hlay := hlay, hpre := hpre, hl := hl, hb := hb, hb' := hb', heq := heq,
        hwM := hwM, hkF := hkF, hkM := hkM, hRT := ⟨RTρ, hRTρ⟩, hr₁ := ⟨hr₁ρ⟩, hr₂ := ⟨hr₂ρ⟩,
        hrc := ⟨hrcρ⟩, hRF := ⟨RFρ, hRFρ⟩, hfF := ⟨hfFρ⟩, hqs := hqsN, hqs' := hqsN', hpar := hpar,
        hms := by simpa using hms, hms' := by simpa using hms', hmot := hmot, hmin := hmin,
        hall := ⟨is, is', x, x', his.trans (instDomsA_length _ _), his'.trans (instDomsA_length _ _),
          by rw [recTelA C.hEL C.hfm rec hl]; exact hrel'⟩ }
    have hl₁ : is.length = fv.indices.length := his.trans (instDomsA_length _ _)
    have hidxJ := C.jointRel hqsN hl₁ hpar (hidx (.sort .zero) .zero)
    rw [recTelA C.hEL C.hfm rec hl, happ] at hC
    injection hC with hC
    subst hC
    have hcore := R.core (C.lfpOf hqsN hmaj) is is' hl₁ (C.recDomRefl R.bF hqsN hqsN' hidxJ) hidxJ
    simpa only [List.append_assoc] using hcore

/-- THE RECURSORS' CLAUSE AT THEIR GROUP STEP (`EnvSemRecStepA`), at the concrete ι, under the struct
    profile (W-1 (c)). -/
theorem envSemRecStepA_of_structProfile (hE : EnvClosedA E) (hEL : EnvLevelsA E)
    (hN : EnvNormClosedA E) (hNCT : EnvNormCtorTypeA E) (hNL : EnvNormLevelsA E) (hρ : PosValA ρ₀)
    (hS : SmallIndexProfileA E) (hPE : PropElimStructA E) :
    EnvSemRecStepA E (iotaIfaceA E) n ρ₀ :=
  fun _ _ _ _ hW hcls hnobody hclT hT fv cs hfresh hlay rec hfreshR hpre hclo ih =>
    recSemClauseA hE hEL hN hNCT hNL hρ hS hPE hW hcls hnobody hclT hT fv cs hfresh hlay rec hfreshR
      hpre hclo ih

/-- THE RECURSORS' CLAUSE AT THEIR GROUP STEP (`EnvSemRecStepA`), at the concrete ι, under the profile. -/
theorem envSemRecStepA_of_profile (hE : EnvClosedA E) (hEL : EnvLevelsA E)
    (hN : EnvNormClosedA E) (hNCT : EnvNormCtorTypeA E) (hNL : EnvNormLevelsA E) (hρ : PosValA ρ₀)
    (hS : SmallIndexProfileA E) (hPE : PropElimOnlyA E) :
    EnvSemRecStepA E (iotaIfaceA E) n ρ₀ :=
  envSemRecStepA_of_structProfile hE hEL hN hNCT hNL hρ hS (propElimStructA_of_propElimOnlyA hPE)

/-- THE SEMANTIC ENVIRONMENT AT THE CONCRETE ι, DISCHARGED: a well-formed environment with the
    small-index profile and its Prop families eliminating into Prop only, the recursors of unit and
    struct groups exempt (`PropElimStructA`), satisfies `EnvSemA`; the families', constructors' and
    recursors' clauses at their group steps (M2-f (4b), (4c), (5b)/(6c), O1-b-1, W-1 (c)), every ι
    hypothesis at `iotaIfaceA E` from closedness. -/
theorem envSemA_of_envWfA_recStruct (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀)
    (hS : SmallIndexProfileA E) (hPE : PropElimStructA E) : EnvSemA E (iotaIfaceA E) n ρ₀ :=
  fun r m hres =>
    envSemAt_of_envWfA (envWfA_closed hW) (envWfA_levels hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW))
      (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_levels (envWfA_levels hW) (envWfA_normLevels hW))
      (envWfA_normCtorType hW) (envWfA_normClosed hW) (iotaFnA_recHead E) hρ
      (envSemFamStepA_of_profile (envWfA_closed hW) (envWfA_levels hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW))
        (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_levels (envWfA_levels hW) (envWfA_normLevels hW))
        (envWfA_normCtorType hW) (envWfA_normClosed hW) (iotaFnA_recHead E) hρ hS)
      (envSemCtorStepA_of_profile (envWfA_closed hW) (envWfA_levels hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW))
        (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_levels (envWfA_levels hW) (envWfA_normLevels hW))
        (envWfA_normCtorType hW) (envWfA_normClosed hW) (iotaFnA_recHead E) hρ hS)
      (envSemRecStepA_of_structProfile (envWfA_closed hW) (envWfA_levels hW)
        (envWfA_normClosed hW) (envWfA_normCtorType hW) (envWfA_normLevels hW) hρ hS hPE) hW
      (prefixA_refl E) (ctorClosedA_refl E) r m ⟨m, hres⟩ hres

/-- the same under `PropElimOnlyA` (no struct group exempt), the profile before W-1 (c). -/
theorem envSemA_of_envWfA_rec (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀) (hS : SmallIndexProfileA E)
    (hPE : PropElimOnlyA E) : EnvSemA E (iotaIfaceA E) n ρ₀ :=
  envSemA_of_envWfA_recStruct hW hρ hS (propElimStructA_of_propElimOnlyA hPE)

/-- the fundamental theorem at the concrete ι, under the profile (struct groups exempt, W-1 (e-2)). -/
theorem fundA_rec (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀) (hS : SmallIndexProfileA E)
    (hPE : PropElimStructA E) :
    FundHasTyA E (iotaIfaceA E) n ρ₀ ∧ FundConvA E (iotaIfaceA E) n ρ₀ :=
  fundA_iota (envWfA_closed hW) (envWfA_normClosed hW) (envWfA_normCtorType hW)
    (envSemA_of_envWfA_recStruct hW hρ hS hPE) hρ

/-- ROW 1 at the concrete ι, under the profile: convertible sorts are `=ₙ`. -/
theorem sortConvCharA_rec (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀) (hS : SmallIndexProfileA E)
    (hPE : PropElimStructA E) {Γ : LCtxA} {l₁ l₂ u : Level}
    (hΓ : CtxWfA E (iotaIfaceA E) n Γ) (h : ConvA E (iotaIfaceA E) n Γ (.sort l₁) (.sort l₂) (.sort u)) :
    eqN l₁ l₂ :=
  sortConvCharA (envWfA_closed hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW))
    (envWfA_normCtorType hW) (envWfA_normClosed hW) (iotaFnA_recHead E) (envSemA_of_envWfA_recStruct hW hρ hS hPE) hρ hΓ h

/-- ROW 2 at the concrete ι, under the profile — at any codomain since M2-g′. -/
theorem piConvInjA_rec (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀) (hS : SmallIndexProfileA E)
    (hPE : PropElimStructA E) {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    {D' : ExprA} {u' : Level} {C' : ExprA} {v' w : Level} (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    (h : ConvA E (iotaIfaceA E) n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) :
    eqN u u' ∧ eqN v v' ∧ Nonempty (TyConvA E (iotaIfaceA E) n Γ D D') ∧
      Nonempty (TyConvA E (iotaIfaceA E) n (.assumption D :: Γ) C C') :=
  piConvInjA (envWfA_closed hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW)) (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW))
    (envWfA_normCtorType hW) (envWfA_normClosed hW) (iotaFnA_recHead E) (envSemA_of_envWfA_recStruct hW hρ hS hPE) hρ hΓ h

end RecClause


#print axioms RecBaseA.idxPer
#print axioms mirrorParConvA
#print axioms RecBaseA.fieldsWalk
#print axioms applyTelA_minor_rhsArgsA
#print axioms minorWalkA
#print axioms plainArgsA_snoc_frec
#print axioms recIHWA_nil
#print axioms recIHWA_wk
#print axioms RecAtA.prefixA
#print axioms RecAtA.stuck
#print axioms RecAtA.wk
#print axioms convA_lamTelA
#print axioms hasTyA_recCallFunA
#print axioms convA_recCallFunA
#print axioms stepAtA_beta
#print axioms RecAtA.ctor
#print axioms RecAtA.core
#print axioms recTelA
#print axioms piCountA_groupRecA
#print axioms recPiTelA
#print axioms unitShape_of_unitGroupA
#print axioms recUnitAppsA
#print axioms structGroupA_true_minor
#print axioms minorFieldsA_proofs
#print axioms structShape_of_structGroupA
#print axioms mem_plainTelA
#print axioms piCountA_minorTyA_plain
#print axioms structFieldCountA_groupRecA
#print axioms ctorApp_hasTyA
#print axioms fieldSelA_hasTyA
#print axioms structProjsA_substTy
#print axioms structProjA_hasTyA
#print axioms structProjsA_substTyA
#print axioms LRRelA_of_propValid
#print axioms validSubstA_propTel
#print axioms structArmA_recSpineA
#print axioms structSideTyA
#print axioms structSideA
#print axioms recStructAppsA
#print axioms structCtorA_of_structGroupA
#print axioms structGroupA_of_recTypeA
#print axioms substTyA_of_convArgsA_ctorFieldsA
#print axioms recSemClauseA
#print axioms envSemRecStepA_of_structProfile
#print axioms envSemRecStepA_of_profile
#print axioms envSemA_of_envWfA_recStruct
#print axioms envSemA_of_envWfA_rec
#print axioms fundA_rec
#print axioms sortConvCharA_rec
#print axioms piConvInjA_rec
#print axioms RecBaseA.frecDomEq
#print axioms RecBaseA.frecFieldRel
#print axioms fieldsTyA_plain_idx_length
#print axioms CtorViewA.frec_length
#print axioms RecBaseA.frecTelConv
#print axioms RecBaseA.frecCallRel
#print axioms RecBaseA.frecCallRelAt
#print axioms RecBaseA.frecIHRel
#print axioms recCallFunA_frec
#print axioms frecCallFunA_pair

end Rcic.Declarative.Ann
