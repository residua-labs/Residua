import rcic.RcicAnnFamSem
import rcic.RcicAnnLREnvG
import rcic.RcicAnnSemTelG
import rcic.RcicAnnTelIntroG
import rcic.RcicAnnFamClauseG
import rcic.RcicAnnFamBuildG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnFrecDomSynG
import rcic.RcicAnnLRRowsG
/-!
# M2-f (4b) — the families' semantic clause at the group step

The clause at a group's family (`EnvSemClauseAg`) by the telescope lemma (`telIntroAg`): the family's
type is valid at its instance, and the two instances' heads are typed at it and convertible
(`famHeadsAg`, level irrelevance on the base derivation); at a full application to related arguments
the two applications are related at the family's sort (`famAppSortRelAg`). For a Type family the left
application's validity is `TyKAg.fam`, with the data of `RcicAnnFamBuild` at the sort's height; the
two applications' equality is `EqKAg.fam`, with the cross data; the right one's validity comes from
the equality (`LREqA_validg`). A function-recursive field's inner data are `famFldIAg` and its siblings
(R-NoFunRec-1 step 1 (1c-δ)). For a Prop family both applications are propositions
(`isPropTy_famApp_iff`), and the sort's relation asks for no data.

At the group step only the base's clauses are in hand (`baseFundA_ofg`); the census comes from
constructor closure (`groupCensusA`), the ι head typed at the base from the full one
(`iotaRecHeadTypedA_prefix`). This proves `EnvSemFamStepAg` under the small-index profile
(`envSemFamStepA_of_profileg`), and with it the semantic environment from the constructors' and the
recursors' clauses alone (`envSemA_of_envWfA_profileg`). Outside the profile the families' clause is
unsatisfiable at a well-formed environment (`RcicAnnFamHeight`), so the premise is not removable.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section FamSem
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE FAMILY'S HEADS: at bounded `=ₙ` lists `ls`, `ls'`, at every height above a threshold and in
    every well-formed context, the family's type at `ls` is valid, and the two heads are typed at it
    and convertible (`fundLevelsAg` on the base typing of the family's type). -/
theorem famHeadsAg (hfc : BaseFundConvAg E₀ E I n ρ₀) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} (hfm : E.members f = some fm) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) {ls ls' : List Level}
    (hb : levelsBounded n ls = true) (hb' : levelsBounded n ls' = true)
    (hl : ls.length = fm.arity) (hl' : ls'.length = fm.arity) (heq : eqNList ls ls') :
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ (Γ : LCtxA), Nonempty (CtxWfA E I n Γ) →
      (∃ R, LRTyAg E I n ρ₀ K Γ (instantiateLevelsA ls fm.mtypeA) R) ∧
      Nonempty (HasTyA E I n Γ (.const f ls) (instantiateLevelsA ls fm.mtypeA)) ∧
      Nonempty (HasTyA E I n Γ (.const f ls') (instantiateLevelsA ls fm.mtypeA)) ∧
      Nonempty (ConvA E I n Γ (.const f ls) (.const f ls') (instantiateLevelsA ls fm.mtypeA)) := by
  obtain ⟨K₀, hK₀⟩ := fundLevelsAg hfc hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq .nil hT
  refine ⟨K₀, fun K hK Γ hΓ => ?_⟩
  obtain ⟨_, hTrel⟩ := hK₀ K hK Γ SubstA.id SubstA.id hΓ (ValidSubstA_nilg _ _ _)
  rw [substA_id, substA_id, substA_id] at hTrel
  obtain ⟨_, ⟨RT, hRT⟩, _, ⟨hTty⟩, ⟨hTty'⟩, ⟨hTconv⟩⟩ := LRRelA_sort_elimg hTrel
  have hf₂' : HasTyA E I n Γ (.const f ls') (instantiateLevelsA ls' fm.mtypeA) :=
    .const _ _ _ _ _ hfm hl' hb' hTty'
  have hTc₂ : TyConvA E I n Γ (instantiateLevelsA ls fm.mtypeA) (instantiateLevelsA ls' fm.mtypeA) :=
    .of _ _ _ _ _ _ hTty (eqNA_refl _) hTty' (eqNA_refl _) hTconv
  have hf₂ := hasTyA_of_tyConvA hf₂' hTc₂.symm
  exact ⟨⟨RT, hRT⟩, ⟨.const _ _ _ _ _ hfm hl hb hTty⟩, ⟨hf₂⟩, ⟨.consts _ _ _ _ _ hfm hl hb hb' heq hf₂⟩⟩

/-- M2-g′: ALL THE ARGUMENTS' CONVERSIONS at every bounded list `=ₙ` the left one — `famParConvAg`
    over the whole family telescope, in the context itself (no world): the datum `PropEqA.fam`
    carries. Arguments related along the family's type at `ls` are a valid pair for the whole
    telescope's context at `lsX` (`validSubstA_of_tel_lvg`), hence two-sided convertible along it
    (`parConvA_of_validSubstg`). -/
theorem famArgsParConvAg (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {fm : CheckedMemberA} (fv : FamViewA fm)
    {u : Level} (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {as as' : List ExprA}
    (hlen : as.length = (fv.params ++ fv.indices).length)
    (hrel : ArgsRelKAg E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) as as') :
    ∀ lsX : List Level, eqNListB n ls lsX →
      ParConvA E I n Γ (instantiateLevelsA lsX fm.mtypeA) (instantiateLevelsA lsX fm.mtypeA) as as' := by
  intro lsX hlX
  have hlXl : lsX.length = fm.arity := (eqNListA_length hlX.1).symm.trans hl
  obtain ⟨hwf⟩ := fv.telCtxWf hT
  obtain ⟨K₀, hK₀⟩ := validSubstA_of_tel_lvg hfund hfc hE₀ hI hEN hR₀ hEL₀ hIL hb hlX.2 hl hlXl hlX.1
    (fv.params ++ fv.indices) hwf
  have hrelK := argsRelKA_monog (Nat.le_max_right K₀ k) hrel
  rw [fv.inst_tel] at hrelK
  have hV := hK₀ (max K₀ k) (Nat.le_max_left _ _) Γ hΓ _ _ as as' hlen hrelK
  rw [← telCtxA_instDomsA] at hV
  have hlen' : as'.length = (fv.params ++ fv.indices).length := (argsRelKA_lengthg hrel).symm.trans hlen
  have h := parConvA_of_validSubstg hEN (instDomsA lsX (fv.params ++ fv.indices))
    (instantiateLevelsA lsX (.sort fv.sort)) (instLevel lsX (.succ fv.sort)) as as'
    (by simp [instDomsA, hlen]) (by simp [instDomsA, hlen']) hV
  rwa [← fv.inst_tel] at h

/-- THE FAMILY'S APPLICATIONS RELATED AT ITS SORT. At a group's family, two full applications at
    bounded `=ₙ` lists, to arguments related along the family's type at the left list, are related at
    the family's sort, above its height. The applications are typed and convertible there
    (`spineConvAg`) and never head-step (`IotaRecHeadA`). A Type family: the left application is valid
    at the sort's height with the `fam` clause (`TyKAg.fam`, the data of `RcicAnnFamBuild` at the left
    arguments' diagonal), the two are equal there (`EqKAg.fam`, the cross data), and the right one is
    valid by the equality (`LREqA_validg`). A Prop family: both are propositions, typed, convertible. -/
theorem famAppSortRelAg (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E) (hR : IotaRecHeadA E I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hEL : EnvLevelsA E) (hIS : IotaSubstA I) {G : ResolvedEnvA} (hpre₀G : PrefixA E₀ G)
    (hpreG : PrefixA G E) (hmemG : G.members f = some fm)
    {ls ls' : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    (hls : eqNList ls ls')
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) (hk : ht ρ₀ (instLevel ls fv.sort) < k)
    {RT : ExprA → ExprA → Prop} (hRT : LRTyAg E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) RT)
    (hf₁ : HasTyA E I n Γ (.const f ls) (instantiateLevelsA ls fm.mtypeA))
    (hf₂ : HasTyA E I n Γ (.const f ls') (instantiateLevelsA ls fm.mtypeA))
    (hfc₁ : ConvA E I n Γ (.const f ls) (.const f ls') (instantiateLevelsA ls fm.mtypeA))
    {as as' : List ExprA} (hrel : ArgsRelKAg E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) as as')
    (hlen : as.length = (instDomsA ls (fv.params ++ fv.indices)).length) :
    LRRelAg E I n ρ₀ k Γ (.sort (instLevel ls fv.sort)) (foldAppsA (.const f ls) as)
      (foldAppsA (.const f ls') as') := by
  have hlen' : as'.length = (instDomsA ls (fv.params ++ fv.indices)).length :=
    (argsRelKA_lengthg hrel).symm.trans hlen
  have hnp₀ : fm.nparamsA ≤ (instDomsA ls (fv.params ++ fv.indices)).length := by
    rw [← fv.nparams]
    simp only [instDomsA, List.length_map, List.length_append]
    exact Nat.le_add_right _ _
  have hu := fv.applyTel_full ls as hlen
  obtain ⟨⟨hAty⟩, ⟨hBty⟩, ⟨hconv⟩, _⟩ := spineConvAg hE hI hEN hΓ hrel _ (Nat.le_of_eq hlen)
    (by rw [fv.inst_tel]
        exact isPiTelA_piTelA (instantiateLevelsA ls (.sort fv.sort)) (instLevel ls (.succ fv.sort)) rfl _)
    hRT hf₁ hf₂ hfc₁ _ hu
  obtain ⟨ps, is, rfl, hps⟩ : ∃ ps is, as = ps ++ is ∧ ps.length = fm.nparamsA :=
    ⟨as.take fm.nparamsA, as.drop fm.nparamsA, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; exact Nat.min_eq_left (by rw [hlen]; exact hnp₀)⟩
  obtain ⟨ps', is', rfl, hps'⟩ : ∃ ps is, as' = ps ++ is ∧ ps.length = fm.nparamsA :=
    ⟨as'.take fm.nparamsA, as'.drop fm.nparamsA, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; exact Nat.min_eq_left (by rw [hlen']; exact hnp₀)⟩
  have hnr : fm.mclass ≠ .recursorM := by rw [hcls]; exact fun h => MemberClass.noConfusion h
  have hnA : hStepFnA E I.fn Γ (foldAppsA (.const f ls) (ps ++ is)) = none :=
    hStepFnA_constSpine_none hR hfm (Or.inr hnobody) hnr Γ (ls := ls) _ (by rw [foldAppsA_const_head])
  have hnB : hStepFnA E I.fn Γ (foldAppsA (.const f ls') (ps' ++ is')) = none :=
    hStepFnA_constSpine_none hR hfm (Or.inr hnobody) hnr Γ (ls := ls') _ (by rw [foldAppsA_const_head])
  rcases fv.profile with hUP | hUT
  · -- a Prop family: both applications are propositions
    have hz : isZero (instLevel ls fv.sort) = true :=
      (isZero_iff_eqN_zero _).mpr (uniformProp_eqN_zero (uniformProp_instLevel hUP ls))
    have hz' : isZero (instLevel ls' fv.sort) = true :=
      (isZero_iff_eqN_zero _).mpr (uniformProp_eqN_zero (uniformProp_instLevel hUP ls'))
    have hD : (piDomsA fm.mtypeA).length = (instDomsA ls (fv.params ++ fv.indices)).length := by
      rw [fv.stored, piDomsA_piTelA]
      simp [instDomsA, piDomsA]
    have hPA : IsPropTy E I Γ (foldAppsA (.const f ls) (ps ++ is)) :=
      (isPropTy_famApp_iff hfm fv.piBody ls (ps ++ is)).mpr ⟨hl, hlen.trans hD.symm, hz⟩
    have hPB : IsPropTy E I Γ (foldAppsA (.const f ls') (ps' ++ is')) :=
      (isPropTy_famApp_iff hfm fv.piBody ls' (ps' ++ is')).mpr
        ⟨(eqNList_length ls ls' hls).symm.trans hl, hlen'.trans hD.symm, hz'⟩
    have hsP := TyKAg.sortP (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := k)
      (LE := fun j _ => LREqAg E I n ρ₀ j) (LT := fun j _ => LRTyAg E I n ρ₀ j)
      (whTyA_of_hasTy (.sort Γ (instLevel ls fv.sort))) hz
    rw [← LRTyA_eqg] at hsP
    -- M2-g′: the two propositions' structure, the family's arguments convertible at every list
    have hlenM : (ps ++ is).length = (fv.params ++ fv.indices).length := by
      rw [hlen]; simp [instDomsA]
    exact ⟨_, hsP,
      ⟨_, whTyA_of_hasTy hAty, hnA, hPA⟩,
      ⟨_, whTyA_of_hasTy hBty, hnB, hPB⟩, ⟨hAty⟩, ⟨hBty⟩, ⟨hconv⟩,
      .fam (whTyA_of_hasTy hAty) (whTyA_of_hasTy hBty) hnA hnB hfm hcls hls
        (famArgsParConvAg hfund hfc hEN hNC hE₀ hI hR₀ hEL₀ hIL fv hT hb hl hΓ hlenM hrel)
        ⟨.of Γ _ _ _ _ _ hAty (eqNA_refl _) hBty (eqNA_refl _) hconv⟩⟩
  · -- a Type family: the `fam` clause at the sort's height
    have hz : isZero (instLevel ls fv.sort) = false :=
      isZero_false_of_uniformType (uniformType_instLevel hUT ls)
    have hnp : ¬ IsPropTy E I Γ (foldAppsA (.const f ls) (ps ++ is)) := fun h => by
      have h3 := ((isPropTy_famApp_iff hfm fv.piBody ls (ps ++ is)).mp h).2.2
      rw [hz] at h3
      cases h3
    have hj : ht ρ₀ (instLevel ls fv.sort) ≤ ht ρ₀ (instLevel ls fv.sort) := Nat.le_refl _
    have hrelD := argsRelKA_refl_leftg hEN hrel
    have hTyA : ∃ R, LRTyAg E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ (foldAppsA (.const f ls) (ps ++ is)) R :=
      ⟨_, by
        rw [LRTyA_eqg]
        exact .fam (whTyA_of_hasTy hAty) hnA hnp hfm hcls fv.piBody hps hu hz
          (famRsAg E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ)
          (famRsFAg E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ fm) (famRsIAg E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ)
          (by rw [← LRTyA_eqg]
              exact famFldAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
          (by rw [← LRTyA_eqg]
              exact famFldFAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hrelD)
          (by rw [← LREqA_eqg]
              exact famFldeqAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
          (famFldRecAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps
            hrelD)
          (by rw [← LREqA_eqg]
              exact famFldFeqAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hrelD)
          (famXsAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hps hrelD)
          (by rw [← LRTyA_eqg]
              exact famFldIAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
          (by rw [← LREqA_eqg]
              exact famFldIeqAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
          (famFldIRecAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps
            hrelD)
          (famFldIdomAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb
            hl hΓ hps hrelD)⟩
    have hEq : LREqAg E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ (foldAppsA (.const f ls) (ps ++ is))
        (foldAppsA (.const f ls') (ps' ++ is')) := by
      rw [LREqA_eqg]
      exact .fam (whTyA_of_hasTy hAty) (whTyA_of_hasTy hBty) hnA hnB hfm hcls fv.piBody hls hps hps'
        (famRsAg E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ)
        (famRsFAg E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ fm) (famRsIAg E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ)
        (by rw [← LRTyA_eqg]
            exact famFldAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
        (by rw [← LRTyA_eqg]
            exact famFldFAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hrelD)
        (by rw [← LREqA_eqg]
            exact famFldeqAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
        (famFldRecAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps
          hrelD)
        (by rw [← LREqA_eqg]
            exact famFldFeqAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hrelD)
        (by rw [← LREqA_eqg]
            exact famXFldAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps' hrel)
        (famXRecAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps'
          hrel)
        (famXResAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps'
          hrel)
        (famXResRAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps'
          hrel)
        (by rw [← LREqA_eqg]
            exact famXFeqAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hps' hrel)
        (famXsAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hps' hrel)
        ⟨.of _ _ _ _ _ _ hAty (eqNA_refl _) hBty (eqNA_refl _) hconv⟩
        (famParConvAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hl hΓ hps hps' hrel)
        (by rw [← LRTyA_eqg]
            exact famFldIAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
        (by rw [← LREqA_eqg]
            exact famFldIeqAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
        (famFldIRecAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps
          hrelD)
        (by rw [← LREqA_eqg]
            exact famXFldIAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps' hrel)
        (famXRecIAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps'
          hrel)
        (famFldIdomAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb
          hl hΓ hps hrelD)
        (famXFldIdomAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb
          hl hΓ hps hps' hrel)
    obtain ⟨RA, hRA⟩ := hTyA
    have hsT := TyKAg.sortT (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := k)
      (LE := fun j _ => LREqAg E I n ρ₀ j) (LT := fun j _ => LRTyAg E I n ρ₀ j)
      (whTyA_of_hasTy (.sort Γ (instLevel ls fv.sort))) hz hk
    rw [← LRTyA_eqg] at hsT
    exact ⟨_, hsT,
      hEq, ⟨RA, hRA⟩, LREqA_validg hEN hEq ⟨RA, hRA⟩, ⟨hAty⟩, ⟨hBty⟩, ⟨hconv⟩⟩

/-- THE FAMILY'S CLAUSE (`EnvSemClauseAg`) at a group's family: at `=ₙ` bounded lists, above the
    family's sort's height and the heads' threshold, the two heads are related at the family's type
    by the telescope lemma — every full application to related arguments, at every world, is related
    at the family's sort (`famAppSortRelAg`; the family's type is closed, so worlds leave it fixed). -/
theorem famSemClauseAg (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E) (hR : IotaRecHeadA E I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hEL : EnvLevelsA E) (hIS : IotaSubstA I) {G : ResolvedEnvA} (hpre₀G : PrefixA E₀ G)
    (hpreG : PrefixA G E) (hmemG : G.members f = some fm) :
    EnvSemClauseAg E I n ρ₀ f fm := by
  intro ls ls' hl hb hb' heq
  have hl' : ls'.length = fm.arity := (eqNList_length ls ls' heq).symm.trans hl
  obtain ⟨K₀, hK₀⟩ := famHeadsAg hfc hE₀ hI hR₀ hEL₀ hIL hfm hT hb hb' hl hl' heq
  refine ⟨max K₀ (ht ρ₀ (instLevel ls fv.sort) + 1), fun k hk Δ hΔ => ?_⟩
  have hk0 : K₀ ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hks : ht ρ₀ (instLevel ls fv.sort) < k :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans (Nat.le_max_right _ _) hk)
  obtain ⟨⟨RT, hRT⟩, hf₁, hf₂, hfc₁⟩ := hK₀ k hk0 Δ hΔ
  have hpiT : IsPiTelA (instDomsA ls (fv.params ++ fv.indices)).length (instantiateLevelsA ls fm.mtypeA) := by
    rw [fv.inst_tel]
    exact isPiTelA_piTelA (instantiateLevelsA ls (.sort fv.sort)) (instLevel ls (.succ fv.sort)) rfl _
  have hTcl : ∀ j, liftA j 1 (instantiateLevelsA ls fm.mtypeA) = instantiateLevelsA ls fm.mtypeA :=
    liftA_instantiateLevelsA_closed hcl ls
  refine ⟨RT, hRT, telIntroAg hE hI hEN hNC _ hΔ hpiT hRT hf₁ hf₂ hfc₁ ?_⟩
  intro ρ hρ as as' hrel hlen C hC
  rw [wkExprA_closed hTcl] at hrel hC
  rw [wkExprA_const, wkExprA_const]
  obtain ⟨⟨RTρ, hRTρ⟩, ⟨hf₁ρ⟩, ⟨hf₂ρ⟩, ⟨hfc₁ρ⟩⟩ := hK₀ k hk0 (wkCtxA ρ Δ) hρ.2
  rw [fv.applyTel_full ls as hlen] at hC
  injection hC with hC
  subst hC
  exact famAppSortRelAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hR hfm hcls hnobody hfresh hcensus hcl hT hEL hIS
    hpre₀G hpreG hmemG hb hl heq hρ.2 hks hRTρ hf₁ρ hf₂ρ hfc₁ρ hrel hlen

/-- THE FAMILY'S CLAUSE AT ITS GROUP STEP (`EnvSemFamStepAg`), under the small-index profile: the
    base's fundamental theorem from its clauses (`baseFundA_ofg`), the census from closure
    (`groupCensusA`), the ι head typed at the base (`iotaRecHeadTypedA_prefix`). -/
theorem envSemFamStepA_of_profileg (hE : EnvClosedA E) (hEL : EnvLevelsA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hK : PropKeyA E I n) (hS : SmallIndexProfileA E) :
    EnvSemFamStepAg E I n ρ₀ := by
  intro E₀ f fm u hW hcls hnobody hclT hT fv cs hfresh hpre hclo ih
  have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpre
  obtain ⟨hfund, hfc⟩ := baseFundA_ofg hE hI hIS hEN hNC hR hρ hK hpre₀ ih
  exact famSemClauseAg hfund hfc hEN hNC (envWfA_closed hW) hE hI (iotaRecHeadTypedA_prefix hpre₀ hR)
    (envWfA_levels hW) hIL hS hR (hpre f fm (members_groupEnvA_family hfresh)) hcls hnobody hfresh.base
    (fun _ _ hc hk hf => groupCensusA hcls hfresh (ctorFamInA_of_envWfA hW) hclo hc hk hf) hclT hT
    hEL hIS (prefixA_groupEnvA hfresh) hpre (members_groupEnvA_family hfresh)

/-- THE SEMANTIC ENVIRONMENT WITH THE FAMILIES DISCHARGED: a well-formed environment with the
    small-index profile satisfies `EnvSemAg` given the clause at its constructors (M2-f (4c)) and at
    its recursors (M2-f (5)). -/
theorem envSemA_of_envWfA_profileg (hW : EnvWfA I E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hK : PropKeyA E I n)
    (hS : SmallIndexProfileA E)
    (hCtor : EnvSemCtorAg E I n ρ₀) (hRec : EnvSemRecAg E I n ρ₀) : EnvSemAg E I n ρ₀ :=
  fun r m hres =>
    envSemAt_of_envWfAg (envWfA_closed hW) (envWfA_levels hW) hI hIS hIL (envWfA_normCtorType hW)
      (envWfA_normClosed hW) hR hρ hK
      (envSemFamStepA_of_profileg (envWfA_closed hW) (envWfA_levels hW) hI hIS hIL
        (envWfA_normCtorType hW) (envWfA_normClosed hW) hR hρ hK hS) (envSemCtorStepA_of_ctorg hCtor)
      (envSemRecStepA_of_recg hRec) hW
      (prefixA_refl E)
      (ctorClosedA_refl E) r m ⟨m, hres⟩ hres

end FamSem

#print axioms famHeadsAg
#print axioms famAppSortRelAg
#print axioms famSemClauseAg
#print axioms envSemFamStepA_of_profileg
#print axioms envSemA_of_envWfA_profileg

end Rcic.Declarative.Ann
