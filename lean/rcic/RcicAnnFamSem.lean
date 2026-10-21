import rcic.RcicAnnFamBuild
import rcic.RcicAnnFrecDomSyn

/-!
# M2-f (4b) — the families' semantic clause at the group step

The clause at a group's family (`EnvSemClauseA`) by the telescope lemma (`telIntroA`): the family's
type is valid at its instance, and the two instances' heads are typed at it and convertible
(`famHeadsA`, level irrelevance on the base derivation); at a full application to related arguments
the two applications are related at the family's sort (`famAppSortRelA`). For a Type family the left
application's validity is `TyKA.fam`, with the data of `RcicAnnFamBuild` at the sort's height; the
two applications' equality is `EqKA.fam`, with the cross data; the right one's validity comes from
the equality (`LREqA_valid`). A function-recursive field's inner data are `famFldIA` and its siblings
(R-NoFunRec-1 step 1 (1c-δ)). For a Prop family both applications are propositions
(`isPropTy_famApp_iff`), and the sort's relation asks for no data.

At the group step only the base's clauses are in hand (`baseFundA_of`); the census comes from
constructor closure (`groupCensusA`), the ι head typed at the base from the full one
(`iotaRecHeadTypedA_prefix`). This proves `EnvSemFamStepA` under the small-index profile
(`envSemFamStepA_of_profile`), and with it the semantic environment from the constructors' and the
recursors' clauses alone (`envSemA_of_envWfA_profile`). Outside the profile the families' clause is
unsatisfiable at a well-formed environment (`RcicAnnFamHeight`), so the premise is not removable.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section FamSem
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE FAMILY'S HEADS: at bounded `=ₙ` lists `ls`, `ls'`, at every height above a threshold and in
    every well-formed context, the family's type at `ls` is valid, and the two heads are typed at it
    and convertible (`fundLevelsA` on the base typing of the family's type). -/
theorem famHeadsA (hfc : BaseFundConvA E₀ E I n ρ₀) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} (hfm : E.members f = some fm) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) {ls ls' : List Level}
    (hb : levelsBounded n ls = true) (hb' : levelsBounded n ls' = true)
    (hl : ls.length = fm.arity) (hl' : ls'.length = fm.arity) (heq : eqNList ls ls') :
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ (Γ : LCtxA), Nonempty (CtxWfA E I n Γ) →
      (∃ R, LRTyA E I n ρ₀ K Γ (instantiateLevelsA ls fm.mtypeA) R) ∧
      Nonempty (HasTyA E I n Γ (.const f ls) (instantiateLevelsA ls fm.mtypeA)) ∧
      Nonempty (HasTyA E I n Γ (.const f ls') (instantiateLevelsA ls fm.mtypeA)) ∧
      Nonempty (ConvA E I n Γ (.const f ls) (.const f ls') (instantiateLevelsA ls fm.mtypeA)) := by
  obtain ⟨K₀, hK₀⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq .nil hT
  refine ⟨K₀, fun K hK Γ hΓ => ?_⟩
  obtain ⟨_, hTrel⟩ := hK₀ K hK Γ SubstA.id SubstA.id hΓ (ValidSubstA_nil _ _ _)
  rw [substA_id, substA_id, substA_id] at hTrel
  obtain ⟨_, ⟨RT, hRT⟩, _, ⟨hTty⟩, ⟨hTty'⟩, ⟨hTconv⟩⟩ := LRRelA_sort_elim hTrel
  have hf₂' : HasTyA E I n Γ (.const f ls') (instantiateLevelsA ls' fm.mtypeA) :=
    .const _ _ _ _ _ hfm hl' hb' hTty'
  have hTc₂ : TyConvA E I n Γ (instantiateLevelsA ls fm.mtypeA) (instantiateLevelsA ls' fm.mtypeA) :=
    .of _ _ _ _ _ _ hTty (eqNA_refl _) hTty' (eqNA_refl _) hTconv
  have hf₂ := hasTyA_of_tyConvA hf₂' hTc₂.symm
  exact ⟨⟨RT, hRT⟩, ⟨.const _ _ _ _ _ hfm hl hb hTty⟩, ⟨hf₂⟩, ⟨.consts _ _ _ _ _ hfm hl hb hb' heq hf₂⟩⟩

/-- the family's type at `ls` is its telescope instantiated. -/
theorem FamViewA.inst_tel {fm : CheckedMemberA} (fv : FamViewA fm) (ls : List Level) :
    instantiateLevelsA ls fm.mtypeA =
      (piTelA (instDomsA ls (fv.params ++ fv.indices)) (instantiateLevelsA ls (.sort fv.sort))
        (instLevel ls (.succ fv.sort))).1 := by
  rw [fv.stored]
  exact congrArg Prod.fst (instantiateLevelsA_piTelA ls (.sort fv.sort) (.succ fv.sort) _)

/-- a full list fills the family's type up to its sort. -/
theorem FamViewA.applyTel_full {fm : CheckedMemberA} (fv : FamViewA fm) (ls : List Level)
    (as : List ExprA) (hlen : as.length = (instDomsA ls (fv.params ++ fv.indices)).length) :
    applyTelA as (instantiateLevelsA ls fm.mtypeA) = some (.sort (instLevel ls fv.sort)) := by
  have happ := applyTelA_piTelA (instantiateLevelsA ls (.sort fv.sort)) (instLevel ls (.succ fv.sort))
    (instDomsA ls (fv.params ++ fv.indices)) as hlen SubstA.id
  rw [substA_id, ← fv.inst_tel] at happ
  exact happ

/-- the whole telescope's context is well formed in the base (the family's typing). -/
theorem FamViewA.telCtxWf {fm : CheckedMemberA} (fv : FamViewA fm) {a : Nat} {u : Level}
    (hT : HasTyA E₀ I a [] fm.mtypeA (.sort u)) :
    Nonempty (CtxWfA E₀ I a (telCtxA (fv.params ++ fv.indices))) := by
  rw [fv.stored] at hT
  have h := (ctxWfA_telA _ _ (fv.params ++ fv.indices) (Γ := []) .nil hT).1
  rw [List.append_nil] at h
  exact h

/-- M2-g′: ALL THE ARGUMENTS' CONVERSIONS at every bounded list `=ₙ` the left one — `famParConvA`
    over the whole family telescope, in the context itself (no world): the datum `PropEqA.fam`
    carries. Arguments related along the family's type at `ls` are a valid pair for the whole
    telescope's context at `lsX` (`validSubstA_of_tel_lv`), hence two-sided convertible along it
    (`parConvA_of_validSubst`). -/
theorem famArgsParConvA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {fm : CheckedMemberA} (fv : FamViewA fm)
    {u : Level} (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {as as' : List ExprA}
    (hlen : as.length = (fv.params ++ fv.indices).length)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) as as') :
    ∀ lsX : List Level, eqNListB n ls lsX →
      ParConvA E I n Γ (instantiateLevelsA lsX fm.mtypeA) (instantiateLevelsA lsX fm.mtypeA) as as' := by
  intro lsX hlX
  have hlXl : lsX.length = fm.arity := (eqNListA_length hlX.1).symm.trans hl
  obtain ⟨hwf⟩ := fv.telCtxWf hT
  obtain ⟨K₀, hK₀⟩ := validSubstA_of_tel_lv hfund hfc hE₀ hI hEN hR₀ hEL₀ hIL hb hlX.2 hl hlXl hlX.1
    (fv.params ++ fv.indices) hwf
  have hrelK := argsRelKA_mono (Nat.le_max_right K₀ k) hrel
  rw [fv.inst_tel] at hrelK
  have hV := hK₀ (max K₀ k) (Nat.le_max_left _ _) Γ hΓ _ _ as as' hlen hrelK
  rw [← telCtxA_instDomsA] at hV
  have hlen' : as'.length = (fv.params ++ fv.indices).length := (argsRelKA_length hrel).symm.trans hlen
  have h := parConvA_of_validSubst hEN (instDomsA lsX (fv.params ++ fv.indices))
    (instantiateLevelsA lsX (.sort fv.sort)) (instLevel lsX (.succ fv.sort)) as as'
    (by simp [instDomsA, hlen]) (by simp [instDomsA, hlen']) hV
  rwa [← fv.inst_tel] at h

/-- THE FAMILY'S APPLICATIONS RELATED AT ITS SORT. At a group's family, two full applications at
    bounded `=ₙ` lists, to arguments related along the family's type at the left list, are related at
    the family's sort, above its height. The applications are typed and convertible there
    (`spineConvA`) and never head-step (`IotaRecHeadA`). A Type family: the left application is valid
    at the sort's height with the `fam` clause (`TyKA.fam`, the data of `RcicAnnFamBuild` at the left
    arguments' diagonal), the two are equal there (`EqKA.fam`, the cross data), and the right one is
    valid by the equality (`LREqA_valid`). A Prop family: both are propositions, typed, convertible. -/
theorem famAppSortRelA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
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
    {RT : ExprA → ExprA → Prop} (hRT : LRTyA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) RT)
    (hf₁ : HasTyA E I n Γ (.const f ls) (instantiateLevelsA ls fm.mtypeA))
    (hf₂ : HasTyA E I n Γ (.const f ls') (instantiateLevelsA ls fm.mtypeA))
    (hfc₁ : ConvA E I n Γ (.const f ls) (.const f ls') (instantiateLevelsA ls fm.mtypeA))
    {as as' : List ExprA} (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) as as')
    (hlen : as.length = (instDomsA ls (fv.params ++ fv.indices)).length) :
    LRRelA E I n ρ₀ k Γ (.sort (instLevel ls fv.sort)) (foldAppsA (.const f ls) as)
      (foldAppsA (.const f ls') as') := by
  have hlen' : as'.length = (instDomsA ls (fv.params ++ fv.indices)).length :=
    (argsRelKA_length hrel).symm.trans hlen
  have hnp₀ : fm.nparamsA ≤ (instDomsA ls (fv.params ++ fv.indices)).length := by
    rw [← fv.nparams]
    simp only [instDomsA, List.length_map, List.length_append]
    exact Nat.le_add_right _ _
  have hu := fv.applyTel_full ls as hlen
  obtain ⟨⟨hAty⟩, ⟨hBty⟩, ⟨hconv⟩, _⟩ := spineConvA hE hI hEN hΓ hrel _ (Nat.le_of_eq hlen)
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
    have hsP := TyKA.sortP (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := k)
      (LE := fun j _ => LREqA E I n ρ₀ j) (LT := fun j _ => LRTyA E I n ρ₀ j)
      (whTyA_of_hasTy (.sort Γ (instLevel ls fv.sort))) hz
    rw [← LRTyA_eq] at hsP
    -- M2-g′: the two propositions' structure, the family's arguments convertible at every list
    have hlenM : (ps ++ is).length = (fv.params ++ fv.indices).length := by
      rw [hlen]; simp [instDomsA]
    exact ⟨_, hsP,
      ⟨_, whTyA_of_hasTy hAty, tripleLikeA_of_prop hnA hPA⟩,
      ⟨_, whTyA_of_hasTy hBty, tripleLikeA_of_prop hnB hPB⟩, ⟨hAty⟩, ⟨hBty⟩, ⟨hconv⟩,
      .fam (whTyA_of_hasTy hAty) (whTyA_of_hasTy hBty) hnA hnB hfm hcls hls
        (famArgsParConvA hfund hfc hEN hNC hE₀ hI hR₀ hEL₀ hIL fv hT hb hl hΓ hlenM hrel)
        ⟨.of Γ _ _ _ _ _ hAty (eqNA_refl _) hBty (eqNA_refl _) hconv⟩⟩
  · -- a Type family: the `fam` clause at the sort's height
    have hz : isZero (instLevel ls fv.sort) = false :=
      isZero_false_of_uniformType (uniformType_instLevel hUT ls)
    have hnp : ¬ IsPropTy E I Γ (foldAppsA (.const f ls) (ps ++ is)) := fun h => by
      have h3 := ((isPropTy_famApp_iff hfm fv.piBody ls (ps ++ is)).mp h).2.2
      rw [hz] at h3
      cases h3
    have hj : ht ρ₀ (instLevel ls fv.sort) ≤ ht ρ₀ (instLevel ls fv.sort) := Nat.le_refl _
    have hrelD := argsRelKA_refl_left hEN hrel
    have hTyA : ∃ R, LRTyA E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ (foldAppsA (.const f ls) (ps ++ is)) R :=
      ⟨_, by
        rw [LRTyA_eq]
        exact .fam (whTyA_of_hasTy hAty) hnA hnp hfm hcls fv.piBody hps hu hz
          (famRsA E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ)
          (famRsFA E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ fm) (famRsIA E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ)
          (by rw [← LRTyA_eq]
              exact famFldA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
          (by rw [← LRTyA_eq]
              exact famFldFA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hrelD)
          (by rw [← LREqA_eq]
              exact famFldeqA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
          (famFldRecA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps
            hrelD)
          (by rw [← LREqA_eq]
              exact famFldFeqA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hrelD)
          (famXsA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hps hrelD)
          (by rw [← LRTyA_eq]
              exact famFldIA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
          (by rw [← LREqA_eq]
              exact famFldIeqA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
          (famFldIRecA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps
            hrelD)
          (famFldIdomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb
            hl hΓ hps hrelD)⟩
    have hEq : LREqA E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ (foldAppsA (.const f ls) (ps ++ is))
        (foldAppsA (.const f ls') (ps' ++ is')) := by
      rw [LREqA_eq]
      exact .fam (whTyA_of_hasTy hAty) (whTyA_of_hasTy hBty) hnA hnB hfm hcls fv.piBody hls hps hps'
        (famRsA E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ)
        (famRsFA E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ fm) (famRsIA E I n ρ₀ (ht ρ₀ (instLevel ls fv.sort)) Γ)
        (by rw [← LRTyA_eq]
            exact famFldA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
        (by rw [← LRTyA_eq]
            exact famFldFA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hrelD)
        (by rw [← LREqA_eq]
            exact famFldeqA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
        (famFldRecA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps
          hrelD)
        (by rw [← LREqA_eq]
            exact famFldFeqA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hrelD)
        (by rw [← LREqA_eq]
            exact famXFldA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps' hrel)
        (famXRecA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps'
          hrel)
        (famXResA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps'
          hrel)
        (famXResRA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps'
          hrel)
        (by rw [← LREqA_eq]
            exact famXFeqA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hps' hrel)
        (famXsA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hps' hrel)
        ⟨.of _ _ _ _ _ _ hAty (eqNA_refl _) hBty (eqNA_refl _) hconv⟩
        (famParConvA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hl hΓ hps hps' hrel)
        (by rw [← LRTyA_eq]
            exact famFldIA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
        (by rw [← LREqA_eq]
            exact famFldIeqA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hrelD)
        (famFldIRecA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps
          hrelD)
        (by rw [← LREqA_eq]
            exact famXFldIA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps' hrel)
        (famXRecIA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps'
          hrel)
        (famFldIdomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb
          hl hΓ hps hrelD)
        (famXFldIdomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb
          hl hΓ hps hps' hrel)
    obtain ⟨RA, hRA⟩ := hTyA
    have hsT := TyKA.sortT (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := k)
      (LE := fun j _ => LREqA E I n ρ₀ j) (LT := fun j _ => LRTyA E I n ρ₀ j)
      (whTyA_of_hasTy (.sort Γ (instLevel ls fv.sort))) hz hk
    rw [← LRTyA_eq] at hsT
    exact ⟨_, hsT,
      hEq, ⟨RA, hRA⟩, LREqA_valid hEN hEq ⟨RA, hRA⟩, ⟨hAty⟩, ⟨hBty⟩, ⟨hconv⟩⟩

/-- THE FAMILY'S CLAUSE (`EnvSemClauseA`) at a group's family: at `=ₙ` bounded lists, above the
    family's sort's height and the heads' threshold, the two heads are related at the family's type
    by the telescope lemma — every full application to related arguments, at every world, is related
    at the family's sort (`famAppSortRelA`; the family's type is closed, so worlds leave it fixed). -/
theorem famSemClauseA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
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
    EnvSemClauseA E I n ρ₀ f fm := by
  intro ls ls' hl hb hb' heq
  have hl' : ls'.length = fm.arity := (eqNList_length ls ls' heq).symm.trans hl
  obtain ⟨K₀, hK₀⟩ := famHeadsA hfc hE₀ hI hR₀ hEL₀ hIL hfm hT hb hb' hl hl' heq
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
  refine ⟨RT, hRT, telIntroA hE hI hEN hNC _ hΔ hpiT hRT hf₁ hf₂ hfc₁ ?_⟩
  intro ρ hρ as as' hrel hlen C hC
  rw [wkExprA_closed hTcl] at hrel hC
  rw [wkExprA_const, wkExprA_const]
  obtain ⟨⟨RTρ, hRTρ⟩, ⟨hf₁ρ⟩, ⟨hf₂ρ⟩, ⟨hfc₁ρ⟩⟩ := hK₀ k hk0 (wkCtxA ρ Δ) hρ.2
  rw [fv.applyTel_full ls as hlen] at hC
  injection hC with hC
  subst hC
  exact famAppSortRelA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hR hfm hcls hnobody hfresh hcensus hcl hT hEL hIS
    hpre₀G hpreG hmemG hb hl heq hρ.2 hks hRTρ hf₁ρ hf₂ρ hfc₁ρ hrel hlen

/-- THE FAMILY'S CLAUSE AT ITS GROUP STEP (`EnvSemFamStepA`), under the small-index profile: the
    base's fundamental theorem from its clauses (`baseFundA_of`), the census from closure
    (`groupCensusA`), the ι head typed at the base (`iotaRecHeadTypedA_prefix`). -/
theorem envSemFamStepA_of_profile (hE : EnvClosedA E) (hEL : EnvLevelsA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hS : SmallIndexProfileA E) :
    EnvSemFamStepA E I n ρ₀ := by
  intro E₀ f fm u hW hcls hnobody hclT hT fv cs hfresh hpre hclo ih
  have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpre
  obtain ⟨hfund, hfc⟩ := baseFundA_of hE hI hIS hEN hNC hR hρ hpre₀ ih
  exact famSemClauseA hfund hfc hEN hNC (envWfA_closed hW) hE hI (iotaRecHeadTypedA_prefix hpre₀ hR)
    (envWfA_levels hW) hIL hS hR (hpre f fm (members_groupEnvA_family hfresh)) hcls hnobody hfresh.base
    (fun _ _ hc hk hf => groupCensusA hcls hfresh (ctorFamInA_of_envWfA hW) hclo hc hk hf) hclT hT
    hEL hIS (prefixA_groupEnvA hfresh) hpre (members_groupEnvA_family hfresh)

/-- THE SEMANTIC ENVIRONMENT WITH THE FAMILIES DISCHARGED: a well-formed environment with the
    small-index profile satisfies `EnvSemA` given the clause at its constructors (M2-f (4c)) and at
    its recursors (M2-f (5)). -/
theorem envSemA_of_envWfA_profile (hW : EnvWfA I E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hS : SmallIndexProfileA E)
    (hCtor : EnvSemCtorA E I n ρ₀) (hRec : EnvSemRecA E I n ρ₀) : EnvSemA E I n ρ₀ :=
  fun r m hres =>
    envSemAt_of_envWfA (envWfA_closed hW) (envWfA_levels hW) hI hIS hIL (envWfA_normCtorType hW)
      (envWfA_normClosed hW) hR hρ
      (envSemFamStepA_of_profile (envWfA_closed hW) (envWfA_levels hW) hI hIS hIL
        (envWfA_normCtorType hW) (envWfA_normClosed hW) hR hρ hS) (envSemCtorStepA_of_ctor hCtor)
      (envSemRecStepA_of_rec hRec) hW
      (prefixA_refl E)
      (ctorClosedA_refl E) r m ⟨m, hres⟩ hres

end FamSem

#print axioms famHeadsA
#print axioms FamViewA.inst_tel
#print axioms FamViewA.applyTel_full
#print axioms famAppSortRelA
#print axioms famSemClauseA
#print axioms envSemFamStepA_of_profile
#print axioms envSemA_of_envWfA_profile

end Rcic.Declarative.Ann
