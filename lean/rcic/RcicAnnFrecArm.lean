import rcic.RcicAnnTelTy

/-!
# R-NoFunRec-1 step 1 (1c-ε2d): the function-recursive pair as a relation at its declared domain

The field binder of a function-recursive position: a pair of the clause's `famFunRelA` at its declared
domain `A` is related there (`LRRelA`). By the Kripke telescope lemma (`telIntroA`) at `A`: the full
applications come from the pair's `FunRelA` (the inner arguments, related along the weakened domain,
read at the clause's inner relations), the typing and the conversion from its declared pair.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section FrecArm
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}


/-- a valid Π with no propositional layer has a valid domain and, at related arguments, valid
    instances. -/
theorem LRTyA_pi_peel {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {D B : ExprA} {u v : Level}
    {R : ExprA → ExprA → Prop} (h : LRTyA E I n ρ₀ k Γ (.pi D u B v) R) (hv : isZero v = false) :
    (∃ RD, LRTyA E I n ρ₀ k Γ D RD) ∧
      ∀ a a', LRRelA E I n ρ₀ k Γ D a a' → ∃ RC, LRTyA E I n ρ₀ k Γ (instantiate0A a B) RC := by
  have hnp : ¬ IsPropTy E I Γ (.pi D u B v) := fun h' => by
    rw [(isPropTy_pi_iff E I Γ D u B v).1 h'] at hv
    cases hv
  rw [LRTyA_eq] at h
  obtain ⟨RD, RC, hD, hC, _, _⟩ := tyKA_pi_inv h hnp
  have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
  have hD0 : LRTyA E I n ρ₀ k Γ D (RD []) := by rw [LRTyA_eq]; exact hD [] hρ
  refine ⟨⟨RD [], hD0⟩, fun a a' haa => ⟨RC [] a, ?_⟩⟩
  rw [LRTyA_eq]
  exact hC [] hρ a a' (haa.at hD0)


/-- related inner arguments along a telescope reached from a field's weakened domain are related by the
    canonical inner relations (the converse of `argsRelKA_of_innerRelsA`). -/
theorem argsRelKA_innerRelsA_PA (hE : EnvClosedA E) {j : Nat} {Γ : LCtxA} {ρ ρ' : WkSpecA} {c : Nat}
    {cm : CheckedMemberA} {lsC : List Level} {i : Nat} {prev : List ExprA} {D : ExprA} {uD : Level}
    {C : ExprA} {vC : Level} (hm : E.members c = some cm)
    (hncl : ∀ j', liftA j' 1 (cm.normA.getD cm.mtypeA) = cm.normA.getD cm.mtypeA)
    (hT : applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC)) :
    ∀ {ii : Nat} {iprev : List ExprA} {T : ExprA} {zs zs' : List ExprA},
    ArgsRelKA E I n ρ₀ j (wkCtxA ρ' (wkCtxA ρ Γ)) T zs zs' →
    applyTelA iprev (wkExprA ρ' D) = some T →
    ArgsRelPA (innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC i prev ρ') ii iprev T zs zs'
  | _, _, _, _, _, .nil _, _ => .nil _ _ _
  | ii, iprev, _, _, _, .cons A u B v f f' fs fs' h hs, hD => by
      refine .cons ii iprev A u B v f f' fs fs' ?_
        (argsRelKA_innerRelsA_PA hE hm hncl hT hs (applyTelA_snoc iprev _ hD))
      rw [innerRelsA_famRsIA hE hm hncl hT hD]
      exact h

/-- the instance of a valid telescope at related arguments is valid. -/
theorem lrTyA_applyTelA {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' → {len : Nat} →
    as.length ≤ len → IsPiTelA len T → {R : ExprA → ExprA → Prop} → LRTyA E I n ρ₀ k Γ T R →
    ∀ C, applyTelA as T = some C → ∃ RC, LRTyA E I n ρ₀ k Γ C RC
  | _, _, _, .nil _, _, _, _, _, hT, C, hC => by
      injection hC with hC
      subst hC
      exact ⟨_, hT⟩
  | _, _, _, .cons A u B v f f' fs fs' h hs, len, hlen, hpi, _, hT, C, hC => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          obtain ⟨hv, hpi'⟩ := hpi
          obtain ⟨_, hcod⟩ := LRTyA_pi_peel hΓ hT hv
          obtain ⟨RC, hRC⟩ := hcod f f' h
          exact lrTyA_applyTelA hΓ hs (Nat.le_of_succ_le_succ hlen) (isPiTelA_instantiate len 0 f B hpi') hRC
            C hC

/-- THE FULL APPLICATIONS OF A FUNCTION-RECURSIVE PAIR (R-NoFunRec-1 step 1 (1c-ε2d)): the inner
    arguments, related along the weakened domain at an extension, are related by the clause's inner
    relations, so the pair's `FunRelA` takes them to the output relation at the codomain reached; the
    output relation (`hout`, the caller's) is the relation there. -/
theorem fullAppsRelA_of_funRel (hE : EnvClosedA E) (hI : IotaLiftA I) (hNC : EnvNormClosedA E)
    {k : Nat} {Γ : LCtxA} {c : Nat}
    {cm : CheckedMemberA} {lsC : List Level} {i : Nat} {prev : List ExprA} {A : ExprA} {uA : Level}
    {B : ExprA} {vB : Level} {j : Nat} {v v' : ExprA} {XF : WkSpecA → CRelA}
    (hm : E.members c = some cm)
    (hncl : ∀ j', liftA j' 1 (cm.normA.getD cm.mtypeA) = cm.normA.getD cm.mtypeA)
    (hT : applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi A uA B vB))
    (hF : FunRelA (innerRelsA (famRsIA E I n ρ₀ k Γ) [] c lsC) XF
      (fun ρ' => WkOkA E I n ρ' Γ) i prev A j v v')
    (hpi : IsPiTelA (j + 1) A) (hRA : ∃ R, LRTyA E I n ρ₀ k Γ A R)
    (hout : ∀ ρ' : WkSpecA, WkOkA E I n ρ' Γ → ∀ (as : List ExprA) (C y y' : ExprA)
      (RC : ExprA → ExprA → Prop), as.length = j + 1 → applyTelA as (wkExprA ρ' A) = some C →
      LRTyA E I n ρ₀ k (wkCtxA ρ' Γ) C RC → XF ρ' C y y' → RC y y') :
    FullAppsRelA E I n ρ₀ k Γ A (j + 1) v v' := by
  intro ρ hρ as as' hK hlen C hC
  have hP : ArgsRelPA (innerRelsA (famRsIA E I n ρ₀ k Γ) [] c lsC i prev ρ) 0 [] (wkExprA ρ A) as as' :=
    argsRelKA_innerRelsA_PA hE hm hncl hT hK rfl
  have hX := hF ρ hρ as as' C hP hlen hC
  obtain ⟨R, hR⟩ := hRA
  obtain ⟨R', hR', -⟩ := LRTyA_wk hE hNC hI hR ρ hρ
  obtain ⟨RC, hRC⟩ := lrTyA_applyTelA hρ.2 hK (Nat.le_of_eq hlen) (isPiTelA_wk ρ (j + 1) A hpi) hR' C hC
  exact ⟨RC, hRC, hout ρ hρ as C _ _ RC hlen hC hRC hX⟩

/-- ARGUMENTS RELATED ALONG A TELESCOPE ARE RELATED ALONG AN EQUAL ONE: at a Π, the domains' equality
    carries the relation and the codomains' equality at the related pair carries the rest. -/
theorem argsRelKA_of_lrEqA (hEN : EnvNormCtorTypeA E) {k : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' → {T' : ExprA} →
    {len : Nat} →
    IsPiTelA len T → IsPiTelA len T' → as.length ≤ len → LREqA E I n ρ₀ k Γ T T' →
    ArgsRelKA E I n ρ₀ k Γ T' as as'
  | _, _, _, .nil _, T', _, _, _, _, _ => .nil T'
  | _, _, _, .cons A u B v f f' fs fs' h hs, T', len, hpiL, hpiR, hlen, hEq => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          match T', hpiR with
          | .pi A' u' B' v', ⟨hv', hB'⟩ =>
              obtain ⟨hvL, hBL⟩ := hpiL
              rw [LREqA_eq] at hEq
              obtain ⟨_, _, _, hDeq, RD, hD, hC⟩ := eqKA_pi_inv hvL hEq
              have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
              have hAA : LREqA E I n ρ₀ k Γ A A' := by
                rw [LREqA_eq]; exact hDeq [] hρ
              obtain ⟨R, hR, hff⟩ := LRRelA_refl_left hEN h
              have hD0 : LRTyA E I n ρ₀ k Γ A (RD []) := by rw [LRTyA_eq]; exact hD [] hρ
              rw [LRTyA_unique hR hD0] at hff
              have hBB : LREqA E I n ρ₀ k Γ (instantiate0A f B) (instantiate0A f B') := by
                rw [LREqA_eq]; exact hC [] hρ f f hff
              exact .cons A' u' B' v' f f' fs fs' (LRRelA_transport' hEN hAA h)
                (argsRelKA_of_lrEqA hEN hΓ hs (isPiTelA_instantiate len 0 f B hBL)
                  (isPiTelA_instantiate len 0 f B' hB') (Nat.le_of_succ_le_succ hlen) hBB)

variable {E₀ : ResolvedEnvA}

/-- THE FUNCTION-RECURSIVE PAIR IS RELATED AT ITS DECLARED DOMAIN (R-NoFunRec-1 step 1 (1c-ε2d), the field
    binder): a pair of the clause's `famFunRelA` at the field's domain `A`, whose outputs lie in the
    fixed point, is related at `A`, once `A` is valid. The converse of `famFunRelA_of_lrRel`: the Kripke
    telescope lemma at `A` (`fullAppsRelA_of_funRel`), the output at the codomain reached — the family at
    the weakened parameters — the canonical fixed point there. -/
theorem lrRelA_of_famFunRelA (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hUT : UniformType fv.sort) {ls : List Level} (hl : ls.length = fm.arity) {lsD : List Level}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {c : Nat} {cm : CheckedMemberA}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    {kinds ksPre ks : List FieldShape} {jn : Nat}
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ (FieldShape.recursive (jn + 1)) :: ks)
    {ps : List ExprA} (hps : ps.length = fm.nparamsA) {T : ExprA}
    (hTc : applyTelA ps (instantiateLevelsA ls (cm.normA.getD cm.mtypeA)) = some T) {pre : List ExprA}
    (hpl : pre.length = ksPre.length)
    {A : ExprA} {u : Level} {B : ExprA} {v : Level} (hTD : applyTelA pre T = some (.pi A u B v))
    (hRA : ∃ R, LRTyA E I n ρ₀ k Γ A R) {XF : WkSpecA → CRelA}
    (hX : ∀ ρ' D y y', XF ρ' D y y' → LfpWA (FamPhiWA E I n Γ f fm (famRsA E I n ρ₀ k Γ)
      (famRsFA E I n ρ₀ k Γ fm) (famRsIA E I n ρ₀ k Γ)) ρ' D y y')
    {x x' : ExprA}
    (hF : famFunRelA E I n Γ fm (innerRelsA (famRsIA E I n ρ₀ k Γ) [] c ls) ps lsD XF
      (fm.nparamsA + ksPre.length) (ps ++ pre) A jn x x') :
    LRRelA E I n ρ₀ k Γ A x x' := by
  have hz : isZero (instLevel ls fv.sort) = false :=
    isZero_false_of_uniformType (uniformType_instLevel hUT ls)
  have hnr : fm.mclass ≠ .recursorM := by rw [hcls]; exact fun h => MemberClass.noConfusion h
  have hcl := liftA_instantiateLevelsA_closed (envNormClosedA_getD hNC hE hcm hk) ls
  have hTfull : applyTelA (ps ++ pre) (instantiateLevelsA ls (cm.normA.getD cm.mtypeA)) = some (.pi A u B v) := by
    rw [applyTelA_append, hTc]; exact hTD
  have hpiA : IsPiTelA (jn + 1) A := by
    obtain ⟨ds, idxI, σ, hds, hAe⟩ := ctorFrecDomA hfresh hcensus hl hps hcm hk hfam hkinds hsp hTc hpl
      hTD
    rw [hAe]
    have h := isPiTelA_ctorFieldsA f ls (instLevel ls fv.sort) idxI hz (ds.map plainA) ps σ
    rw [List.length_map, hds] at h
    exact h
  obtain ⟨R, hRR⟩ := hRA
  refine ⟨R, hRR, telIntroA hE hI hEN hNC (jn + 1) hΓ hpiA hRR hF.2.1 hF.2.2.1 hF.2.2.2 ?_⟩
  refine fullAppsRelA_of_funRel hE hI hNC hcm (envNormClosedA_getD hNC hE hcm hk) hTfull hF.1 hpiA ⟨R, hRR⟩ ?_
  intro ρ' hρ' as C y y' RC hlen hC hRC hXo
  have hTc_c : applyTelA (ps.map (wkExprA ρ')) (instantiateLevelsA ls (cm.normA.getD cm.mtypeA)) = some (wkExprA ρ' T) := by
    rw [applyTelA_wk_closed ρ' ps hcl, hTc]; rfl
  have hTD_c : applyTelA (pre.map (wkExprA ρ')) (wkExprA ρ' T) =
      some (.pi (wkExprA ρ' A) u (wkExprA (WkSpecA.ub ρ') B) v) := by
    rw [applyTelA_wk, hTD, Option.map_some', wkExprA_pi_ub]
  have hpsw : (ps.map (wkExprA ρ')).length = fm.nparamsA := by rw [List.length_map, hps]
  obtain ⟨ds, idxI, σ, hds, hAe⟩ := ctorFrecDomA hfresh hcensus hl hpsw hcm hk hfam hkinds hsp hTc_c
    (by rw [List.length_map]; exact hpl) hTD_c
  have hCe : C = foldAppsA (.const f ls) (ps.map (wkExprA ρ') ++ idxI.map (substA
      (consListA (plainArgsA (ds.map plainA) as) σ))) := by
    rw [hAe] at hC
    have h := applyTelA_ctorFieldsA f ls (instLevel ls fv.sort) idxI (ds.map plainA) as
      (by rw [List.length_map, hds, hlen]) (ps.map (wkExprA ρ')) σ
    exact Option.some.inj (hC.symm.trans h)
  have hnD : hStepFnA E I.fn (wkCtxA ρ' Γ) C = none := by
    rw [hCe]
    exact hStepFnA_constSpine_none hR hfm (Or.inr hnobody) hnr (wkCtxA ρ' Γ) (ls := ls) _
      (by rw [foldAppsA_const_head])
  have hnpD : ¬ IsPropTy E I (wkCtxA ρ' Γ) C := fun h => by
    rw [hCe] at h
    have h3 := ((isPropTy_famApp_iff hfm fv.piBody ls _).mp h).2.2
    rw [hz] at h3
    cases h3
  have hLfp := hX ρ' C y y' hXo.2.2
  rw [hCe] at hRC hLfp
  have hcan := lrTyA_fam_canon hE hNC hfm hcls hpsw (by rw [← hCe]; exact hnD) (by rw [← hCe]; exact hnpD) hRC
  rw [hcan]
  show LfpWA _ [] _ y y'
  rw [famLfpWA_wk, WkSpecA.comp_nil]
  exact hLfp

end FrecArm

#print axioms argsRelKA_innerRelsA_PA
#print axioms lrTyA_applyTelA
#print axioms fullAppsRelA_of_funRel
#print axioms argsRelKA_of_lrEqA
#print axioms lrRelA_of_famFunRelA

end Rcic.Declarative.Ann
