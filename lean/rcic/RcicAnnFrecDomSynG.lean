import rcic.RcicAnnFrecDomSyn
import rcic.RcicAnnLREnvG
import rcic.RcicAnnSemTelG
import rcic.RcicAnnTelIntroG
import rcic.RcicAnnFamClauseG
import rcic.RcicAnnFamBuildG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnLRRowsG
/-!
# R-NoFunRec-1 step 1 (1c-ε2d-a0) — the function-recursive domain's syntactic evidence

The function-recursive field's domain is typed in the group environment `G`, a prefix of the full one,
by the view-typing chain (`frecDomTyG`). This module holds that chain below the recursors' clause, and
the experiment of (1c-ε2d-a0): the conversion between the two instances' declared domains, produced
from syntactic typing in `G`, level irrelevance, and the walk's valid substitution evidence, with no
semantic fundamental theorem of `G` or `E`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) the fields' typing (R-NoFunRec-1 step 1 (1c-ε2d-0))

Moved here from `RcicAnnViewTy`, below the recursors' clause, with the typed recursor-head fact
(`IotaRecHeadTypedA`) in place of `IotaRecHeadA`: the group environment, a prefix of the full one, has
only the typed fact (`iotaRecHeadTypedA_prefix`). R-NoFunRec-1 step 1 (1c-ε2d): the family-open data
(`viewTy_openFam`), the environment moves of the fields' typing (`viewTy_fields_env`) and the weakening past
a context (`viewTy_wkBy`) moved with it, for the whole function-recursive domain's typing (`frecDomTyG`). -/

section ViewTyFields
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end ViewTyFields

section ViewTyEnvMove
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

end ViewTyEnvMove

/-! ## (0b) the function-recursive field's whole domain (R-NoFunRec-1 step 1 (1c-ε2d), N1)

The base domain `frecDomA … SubstA.id` over the parameter locals, in the plain context past a prefix, is
typed in the group environment (`frecDomTyG`: `viewTy_fields` over the carried facts, `frecOpenA`); its
instance at the walk's substitution is the walk's reached domain (`frecDomA_instance`). -/

section FrecDomG
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/- (`plainIdxA_add` landed upstream in `RcicAnnGroup` — same statement, same proof shape.) -/

end FrecDomG

/-! ## (1) the experiment (1c-ε2d-a0): the declared domains' conversion, from syntactic evidence only -/

section FrecDomSyn
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE WALK'S VALID PAIR IS A CONVERTIBLE SUBSTITUTION PAIR, on a context of assumptions: each variable's
    pair is typed and convertible at the left's substituted type, the right's typing moved across the
    domains' type conversion. -/
theorem convSubstA_of_validSubstAg : (Γ : LCtxA) → AssumpOnlyA Γ → {k : Nat} → {Δ : LCtxA} →
    {σ σ' : SubstA} → ValidSubstAg E I n ρ₀ k Δ σ σ' Γ → Nonempty (ConvSubstA E I n Δ σ σ' Γ)
  | [], _, _, Δ, σ, σ', _ =>
      ⟨{ left := { ty := fun i _ h => by cases i <;> simp [lookupTypeA] at h
                   val := fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h }
         right := { ty := fun i _ h => by cases i <;> simp [lookupTypeA] at h
                    val := fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h }
         conv := fun i _ h => by cases i <;> simp [lookupTypeA] at h }⟩
  | d :: Γ, hd, k, Δ, σ, σ', h => by
      obtain ⟨D, rfl⟩ := hd d (List.mem_cons_self _ _)
      have hσ : σ = SubstA.cons (σ 0) (fun i => σ (i + 1)) := funext fun i => by cases i <;> rfl
      have hσ' : σ' = SubstA.cons (σ' 0) (fun i => σ' (i + 1)) := funext fun i => by cases i <;> rfl
      have htail : ValidSubstAg E I n ρ₀ k Δ (fun i => σ (i + 1)) (fun i => σ' (i + 1)) Γ := by
        refine ⟨fun i B hB => ?_, fun i B v hB hv => ?_⟩
        · have h1 := h.1 (i + 1) (liftA 0 1 B) (by rw [lookupTypeA_cons_succ, hB]; rfl)
          rw [substA_liftA_succ, substA_liftA_succ] at h1
          exact h1
        · have h1 := h.2 (i + 1) (liftA 0 1 B) (liftA 0 1 v) (by rw [lookupTypeA_cons_succ, hB]; rfl)
            (by rw [lookupValueA_cons_succ, hv]; rfl)
          rw [substA_liftA_succ, substA_liftA_succ, substA_liftA_succ] at h1
          exact h1
      have h0 := h.1 0 (liftA 0 1 D) (lookupTypeA_cons_zero_assumption D Γ)
      rw [substA_liftA_succ, substA_liftA_succ] at h0
      obtain ⟨tl⟩ := convSubstA_of_validSubstAg Γ (fun d' hd' => hd d' (List.mem_cons_of_mem _ hd')) htail
      obtain ⟨t0⟩ := (LRRelA_hasTyg h0.2).1
      obtain ⟨t0'⟩ := (LRRelA_hasTyg h0.2).2
      obtain ⟨c0⟩ := LRRelA_convg h0.2
      obtain ⟨tc⟩ := LREqA_tyConvg h0.1
      have t0'' : HasTyA E I n Δ (σ' 0) (substA (fun i => σ' (i + 1)) D) := hasTyA_of_tyConvA t0' tc
      have hres := convSubstA_cons_gen tl t0 t0'' c0
      rw [← hσ, ← hσ'] at hres
      exact ⟨hres⟩

/-- THE PRODUCER (1c-ε2d-a0), WITH ITS BINDERWISE HALF (1c-ε2d-L3b-2). A walk reaching a function-recursive
    field reaches a declared domain on each side (after `pre` at `ps`, `lsC`; after `pre'` at `ps'`, `lsC'`);
    the two are type-convertible, and their inner binders are convertible pairwise (`TelConvA`).
    From the walk's evidence only: the field list's typing in `E₀` and the valid substitution pair
    (the base's fundamental theorem, through `frecWalkAg`), the base domain's syntactic typing in the
    group environment `G` (`frecDomTyG`), level irrelevance in `G`, and functionality in `E`. No
    fundamental theorem of `G` or `E`, no Π-injectivity, no recursor clause. -/
theorem frecDomConvCoreAg {E₀ E G : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat}
    {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) (hIS : IotaSubstA I) (hR : IotaRecHeadA E I)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hpre₀G : PrefixA E₀ G) (hpreG : PrefixA G E) (hmemG : G.members f = some fm)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity) {j : Nat}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKAg E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA}
    (hρ : WkOk₀A E I n ρ Γ) {c : Nat} {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {jn : Nat} {T T' : ExprA}
    {pre pre' : List ExprA} {D : ExprA} {uD : Level} {C₀ : ExprA} {vC : Level} {D' : ExprA}
    {uD' : Level} {C₀' : ExprA} {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsAg E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T
      ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C₀ vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C₀' vC')) :
    Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') ∧
      TelConvA E I n (wkCtxA ρ Γ) (piDomListA D) (piDomListA D') := by
  refine frecWalkAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hb hl hΓ
    hps hps' hrel hρ hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' ?_
  intro fsPre B uB Bs idx hBs hlen hlen' hdom hΓp huniv hDe hDe' ⟨fsRest, res, ⟨hty⟩⟩ ⟨K₁, hK₁⟩
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hbC' : levelsBounded n lsC' = true := hlCC.2
  obtain ⟨hΓρ⟩ := ctxWfA_wk₀ hΓ hρ
  have hEG : EnvClosedA G := fun r m h => hE r m (hpreG r m h)
  have hd0 := frecDomTyG hEG hI (iotaRecHeadTypedA_prefix hpreG hR) hIS hpre₀G (fv := fv)
    (hasTyEnvA hpre₀G hT) hmemG fsPre hty
  have hΓG := viewTy_ctx_env hpre₀G hΓp
  have hK1 : K₁ ≤ max K₁ (max k j) := by omega
  have hKk : k ≤ max K₁ (max k j) := by omega
  have hKj : j ≤ max K₁ (max k j) := by omega
  have hV₁ := (hK₁ _ hK1 hKj hKk).2
  have hasm : AssumpOnlyA (instCtxA lsC (plainCtxA fsPre (telCtxA fv.params))) :=
    assumpOnlyA_instCtxA lsC (assumpOnlyA_plainCtxA fsPre _ (assumpOnlyA_telCtxA fv.params))
  obtain ⟨cs'⟩ := convSubstA_of_validSubstAg _ hasm hV₁
  obtain ⟨hc⟩ := frecSubstConvA hE hI hIS hR hEL hIL hpreG hΓG hd0 hbC hbC' hlC hlC' hlCC.1 cs'
  have hps₁ : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hps₂ : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  have hDC := frecDomA_reach fv hlC hps₁ hlen hDe
  have hDC' := frecDomA_reach fv hlC' hps₂ hlen' hDe'
  refine ⟨?_, ?_⟩
  · rw [hDC, hDC'] at hc
    exact ⟨tyConvA_of_sortConv hE hI hR hIS hΓρ hc⟩
  · rw [← hDe, ← hDe', ← frecDomA_eq, ← frecDomA_eq]
    exact frecTelConvAux hE hI hIS hR hEL hIL hpre₀G hpreG hbC hbC' hlC hlC' hlCC.1 idx
      ((B, uB) :: Bs) hΓp hdom _ _ cs'

/-- THE PRODUCER (1c-ε2d-a0), its type-conversion half. -/
theorem frecDomConvAg {E₀ E G : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat}
    {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) (hIS : IotaSubstA I) (hR : IotaRecHeadA E I)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hpre₀G : PrefixA E₀ G) (hpreG : PrefixA G E) (hmemG : G.members f = some fm)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity) {j : Nat}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKAg E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA}
    (hρ : WkOk₀A E I n ρ Γ) {c : Nat} {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {jn : Nat} {T T' : ExprA}
    {pre pre' : List ExprA} {D : ExprA} {uD : Level} {C₀ : ExprA} {vC : Level} {D' : ExprA}
    {uD' : Level} {C₀' : ExprA} {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsAg E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T
      ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C₀ vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C₀' vC')) :
    Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') :=
  (frecDomConvCoreAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb
    hl hΓ hps hps' hrel hρ hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD').1

/-- THE DECLARED-DOMAIN DATUM (`hFldIdom`) (R-NoFunRec-1 step 1 (1c-ε2d-L1)): at a function-recursive
    position, the declared domains reached by two walks at `=ₙ` level lists, on one parameter list,
    are type-convertible. `frecDomConvAg` at the diagonal parameters. -/
theorem famFldIdomAg {E₀ E G : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hpre₀G : PrefixA E₀ G) (hpreG : PrefixA G E) (hmemG : G.members f = some fm)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity) {j : Nat}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKAg E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsAg E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') :=
  fun _ρ hρ _c _cm _lsA _lsC _lsC' _kinds _ksPre _ks _jn _T _T' _pre _pre' _D _uD _C _vC _D' _uD' _C' _vC'
      hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' =>
    frecDomConvAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb hl
      hΓ hps hps hrel hρ hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD'

/-- the same across two parameter lists, at one level list (`hXFldIdom`). -/
theorem famXFldIdomAg {E₀ E G : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hpre₀G : PrefixA E₀ G) (hpreG : PrefixA G E) (hmemG : G.members f = some fm)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity) {j : Nat}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKAg E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsAg E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre T' = some (.pi D' uD' C' vC') →
      Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') :=
  fun _ρ hρ _c _cm _lsA _lsC _kinds _ksPre _ks _jn _T _T' _pre _pre' _D _uD _C _vC _D' _uD' _C' _vC'
      hcm hk hfam hkinds hsp hlA hlAC hTc hTc' hw hTD hTD' =>
    frecDomConvAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb hl
      hΓ hps hps' hrel hρ hcm hk hfam hkinds hsp hlA hlAC (eqNListB_refl hlAC.2) hTc hTc'
      (argsRelA_diag hEN (famRsA_refl_leftg hEN) hw) hTD hTD'

end FrecDomSyn

/-! ## (2) the non-vacuous instance

A family `Fam.{l} : Sort (l+1)` with a constructor `mk`, a plain variable `x : Sort l`, and the base domain
`Π (_ : x) (_ : x), Fam.{l}` with two inner binders. The left instance is at the level `2` and the
parameter `Sort 1`; the right at the level `imax 1 2` (`=ₙ` `2`, syntactically different) and the
parameter's β-redex (convertible, not equal). The core lemma gives the two declared domains' conversion,
and a field of the left domain carries to the right. The substitution pair is given as a `ConvSubstA`
here; the producer builds it from the walk's valid pair (`convSubstA_of_validSubstAg`). -/

namespace FrecDomSynTest

end FrecDomSynTest

#print axioms convSubstA_of_validSubstAg
#print axioms frecDomConvCoreAg
#print axioms frecDomConvAg
#print axioms famFldIdomAg
#print axioms famXFldIdomAg

end Rcic.Declarative.Ann
