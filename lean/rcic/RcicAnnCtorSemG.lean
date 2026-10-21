import rcic.RcicAnnCtorSem
import rcic.RcicAnnLREnvG
import rcic.RcicAnnSemTelG
import rcic.RcicAnnTelIntroG
import rcic.RcicAnnFamClauseG
import rcic.RcicAnnFamBuildG
import rcic.RcicAnnFamSemG
import rcic.RcicAnnEnvWfG
import rcic.RcicAnnFrecDomSynG
import rcic.RcicAnnLRRowsG
/-!
# M2-f (4c) — the constructors' clause at the group step

At a group's constructor `c`, the clause (`EnvSemClauseAg`) relates `c ls` and `c ls'` at the
constructor's type. Once the family's clause holds at the step (M2-f (4b)), the constructor's type,
typed in the base extended by the family, falls under the fundamental theorem. A Prop family's
constructor type is a proposition, related by the `prop` clause. For a Type family the telescope
lemma reduces the clause to full applications: two full constructor applications to related
arguments are related at the result, a family application, where the relation is the `fam`
clause's least fixed point at the canonical relations (`lrTyA_fam_canong`). The two applications are
its constructor disjunct: the fields walk with the canonical relations (`ctorWalkAg`, the recursive
fields by canonicity at their domains, a function-recursive one by its own relatedness at its type,
`famFunRelA_of_lrRelg`; R-NoFunRec-1 step 1 (1c-δ)); the results are coherent with the carrier (`resDomAg`, under
the parameters' valid pair carried from the constructor's parameter mirrors, `mirrorSubstAg`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the `fam` clause's relation is canonical -/

section Canon
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE `fam` CLAUSE'S RELATION IS CANONICAL. At a Type-level family application valid at `k`, the
    term relation is the least fixed point at the canonical relations (`famRsAg` / `famRsFAg` at `k`):
    the clause's `Rs` / `RsF` agree with them on every reached domain (`hFld` / `hFldF` at the
    every world, uniqueness), and its inner relations `RsI` with `famRsIAg` on every reached inner
    domain (`hFldI`; R-NoFunRec-1 step 1 (1b): the constructor types are closed, `hE`), so the two
    fixed points coincide (`lfpWA_le_of`, both ways). -/
theorem lrTyA_fam_canong (hE : EnvClosedA E) (hNC : EnvNormClosedA E) {k : Nat} {Γ : LCtxA}
    {r : Nat} {ls : List Level} {ps is : List ExprA}
    {m : CheckedMemberA} {R : ExprA → ExprA → Prop}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hps : ps.length = m.nparamsA)
    (hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
    (hnp : ¬ IsPropTy E I Γ (foldAppsA (.const r ls) (ps ++ is)))
    (hR : LRTyAg E I n ρ₀ k Γ (foldAppsA (.const r ls) (ps ++ is)) R) :
    R = fun a b => LfpWA (FamPhiWA E I n Γ r m (famRsAg E I n ρ₀ k Γ) (famRsFAg E I n ρ₀ k Γ m) (famRsIAg E I n ρ₀ k Γ)) []
      (foldAppsA (.const r ls) (ps ++ is)) a b := by
  rw [LRTyA_eqg] at hR
  cases hR with
  | prop hA' hn' hP =>
      have e := whTyA_det (whTyA_self hA') hA' hn hn'
      subst e
      exact absurd hP hnp
  | sortT hA' _ _ =>
      have e := whTyA_det (whTyA_self hA') hA' hn (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | sortP hA' _ =>
      have e := whTyA_det (whTyA_self hA') hA' hn (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | pi hA' _ _ _ _ _ _ _ _ =>
      have e := whTyA_det (whTyA_self hA') hA' hn (hStepFnA_pi _ _ _ _ _ _ _)
      exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | fam hA' hn' _ hm' _ _ hps' _ _ Rs RsF RsI hFld hFldF _ _ _ _ hFldI _ _ =>
      have e := whTyA_det (whTyA_self hA') hA' hn hn'
      obtain ⟨er, els, exs⟩ := foldAppsA_const_inj e
      subst er
      subst els
      rw [hm] at hm'
      cases hm'
      obtain ⟨eps, eis⟩ := List.append_inj exs (by rw [hps, hps'])
      subst eps
      subst eis
      have hU : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsC lsA : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
          (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          ArgsRelA (famRsAg E I n ρ₀ k Γ ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m (famRsAg E I n ρ₀ k Γ) (famRsFAg E I n ρ₀ k Γ m) (famRsIAg E I n ρ₀ k Γ)) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famRsIAg E I n ρ₀ k Γ) ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famRsAg E I n ρ₀ k Γ) (famRsFAg E I n ρ₀ k Γ m) (famRsIAg E I n ρ₀ k Γ)) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) =
            famRsAg E I n ρ₀ k Γ ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) := by
        intro ρ hρ c cm lsC lsA kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlAC hT hw _
          hTD
        have hD := hFld ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA
          hlAC hT hw hTD
        rw [← LRTyA_eqg] at hD
        have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
            some (.pi D uD C vC) := by
          rw [applyTelA_append, hT]; exact hTD
        rw [famRsA_eqg hcm hTfull]
        exact LRTyA_uniqueg hD (LRTyA_rel_selfg hD)
      have hUF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          ArgsRelPA (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          ArgsRelPA (famRsFAg E I n ρ₀ k Γ m ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) →
          RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre) =
            famRsFAg E I n ρ₀ k Γ m ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre) := by
        intro ρ hρ lsF TF pre pre' D uD C vC hlF hTF hw _ hTD
        have hD := hFldF ρ hρ lsF TF pre pre' D uD C vC hlF hTF hw hTD
        rw [← LRTyA_eqg] at hD
        have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsF m.mtypeA) =
            some (.pi D uD C vC) := by
          rw [applyTelA_append, hTF]; exact hTD
        rw [famRsFA_eqg hTfull]
        exact LRTyA_uniqueg hD (LRTyA_rel_selfg hD)
      have hUI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsC lsA : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA) (pre pre' : List ExprA)
          (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          ArgsRelA (famRsAg E I n ρ₀ k Γ ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m (famRsAg E I n ρ₀ k Γ) (famRsFAg E I n ρ₀ k Γ m) (famRsIAg E I n ρ₀ k Γ)) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famRsIAg E I n ρ₀ k Γ) ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famRsAg E I n ρ₀ k Γ) (famRsFAg E I n ρ₀ k Γ m) (famRsIAg E I n ρ₀ k Γ)) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) →
          ∀ (ys ys' : List ExprA) (B : ExprA) (uB : Level) (C' : ExprA) (vB : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) ys ys' →
          ArgsRelPA (innerRelsA (famRsIAg E I n ρ₀ k Γ) ρ c lsC (m.nparamsA + ksPre.length)
            (ps.map (wkExprA ρ) ++ pre) ρ') 0 [] (wkExprA ρ' D) ys ys' →
          applyTelA ys (wkExprA ρ' D) = some (.pi B uB C' vB) →
          innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' (0 + ys.length)
              ([] ++ ys) =
            innerRelsA (famRsIAg E I n ρ₀ k Γ) ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ'
              (0 + ys.length) ([] ++ ys) := by
        intro ρ hρ c cm lsC lsA kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlAC hT hw _
          hTD ρ' hρ' ys ys' B uB C' vB hy _ hB
        have hD := hFldI ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA
          hlAC hT hw hTD ρ' hρ' ys ys' B uB C' vB hy hB
        rw [← LRTyA_eqg] at hD
        have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
            some (.pi D uD C vC) := by
          rw [applyTelA_append, hT]; exact hTD
        rw [Nat.zero_add, List.nil_append,
            innerRelsA_famRsIAg hE hcm (envNormClosedA_getD hNC hE hcm hk) hTfull hB]
        exact LRTyA_uniqueg hD (LRTyA_rel_selfg hD)
      have hAp : carrierParamsA m (foldAppsA (.const r ls) (ps ++ is)) = ps.map (wkExprA []) := by
        rw [map_wkExprA_nil, carrierParamsA_foldAppsA, ← hps, List.take_left]
      have hAl : eqNList ls (carrierLevelsA (foldAppsA (.const r ls) (ps ++ is))) := by
        rw [carrierLevelsA_foldAppsA]; exact eqNList_refl ls
      funext a b
      apply propext
      constructor
      · intro h
        exact lfpWA_le_of hU hUF hUI (wkOk₀A_nil E I n Γ) hAp hAl h
      · intro h
        exact lfpWA_le_of
          (fun ρ hρ c cm lsC lsA kinds ksPre ks T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 w₁ w₂ h9 =>
            (hU ρ hρ c cm lsC lsA kinds ksPre ks T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 w₂ w₁ h9).symm)
          (fun ρ hρ lsF TF pre pre' D uD C vC h1 h2 w₁ w₂ h3 =>
            (hUF ρ hρ lsF TF pre pre' D uD C vC h1 h2 w₂ w₁ h3).symm)
          (fun ρ hρ c cm lsC lsA kinds ksPre ks j T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 w₁ w₂ h9 ρ' hρ' ys
              ys' B uB C' vB y₁ y₂ hB =>
            (hUI ρ hρ c cm lsC lsA kinds ksPre ks j T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 w₂ w₁ h9 ρ' hρ' ys
              ys' B uB C' vB y₂ y₁ hB).symm)
          (wkOk₀A_nil E I n Γ) hAp hAl h
  | stuck hA' hN =>
      have e := whTyA_det (whTyA_self hA') hA' hn hN.1
      subst e
      exact (hN.2 (by rw [foldAppsA_const_head]; exact ⟨m, hm, hind⟩)).elim

end Canon

/-! ## (2) constructor walks -/

section Walks
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- A LIST RELATED ALONG A CONSTRUCTOR'S FIELD TELESCOPE WALKS with the canonical field relation at
    the same height: at a plain position the related pair is the relation at the domain reached
    (`famRsA_eqg`); at a recursive one `hX` supplies the recursive positions' pair, at a function-recursive
    one `hF` (R-NoFunRec-1 step 1 (1c-δ)). -/
theorem ctorWalkAg {k : Nat} {Γ : LCtxA} {c : Nat} {cm : CheckedMemberA} {lsC : List Level}
    (hcm : E.members c = some cm) {np : Nat} {ps : List ExprA} {T₀ : ExprA}
    (hT₀ : applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T₀) {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ksAll : List FieldShape}
    (hX : ∀ (ksPre ks : List FieldShape) (pre pre' : List ExprA) (A : ExprA) (u : Level) (B : ExprA)
      (v : Level) (f f' : ExprA), ksAll = ksPre ++ (FieldShape.recursive 0) :: ks →
      ArgsRelA (famRsAg E I n ρ₀ k Γ [] c lsC) X F np ps T₀ ksPre pre pre' →
      applyTelA pre T₀ = some (.pi A u B v) → LRRelAg E I n ρ₀ k Γ A f f' → X A f f')
    (hF : ∀ (ksPre ks : List FieldShape) (j : Nat) (pre pre' : List ExprA) (A : ExprA) (u : Level) (B : ExprA)
      (v : Level) (f f' : ExprA), ksAll = ksPre ++ (FieldShape.recursive (j + 1)) :: ks →
      ArgsRelA (famRsAg E I n ρ₀ k Γ [] c lsC) X F np ps T₀ ksPre pre pre' →
      applyTelA pre T₀ = some (.pi A u B v) → LRRelAg E I n ρ₀ k Γ A f f' →
      F (np + ksPre.length) (ps ++ pre) A j f f') :
    {T : ExprA} → {rest rest' : List ExprA} → ArgsRelKAg E I n ρ₀ k Γ T rest rest' →
    ∀ (ksPre ks : List FieldShape) (pre pre' : List ExprA), ksAll = ksPre ++ ks → rest.length = ks.length →
      applyTelA pre T₀ = some T →
      ArgsRelA (famRsAg E I n ρ₀ k Γ [] c lsC) X F np ps T₀ ksPre pre pre' →
      ArgsRelA (famRsAg E I n ρ₀ k Γ [] c lsC) X F np ps T₀ ksAll (pre ++ rest) (pre' ++ rest')
  | _, _, _, .nil _, ksPre, ks, pre, pre', hks, hlen, _, hw => by
      cases ks with
      | nil =>
          rw [hks]
          simp only [List.append_nil]
          exact hw
      | cons _ _ => cases hlen
  | _, _, _, .cons A u B v f f' fs fs' h hs, ksPre, ks, pre, pre', hks, hlen, hTpre, hw => by
      cases ks with
      | nil => cases hlen
      | cons kd ks' =>
          have hkind : kindRelA (famRsAg E I n ρ₀ k Γ [] c lsC) X F (np + ksPre.length) (ps ++ pre) A kd f f' := by
            cases kd using FieldShape.cases3 with
            | funRec j => exact hF ksPre ks' j pre pre' A u B v f f' hks hw hTpre h
            | plain =>
                have hTfull : applyTelA (ps ++ pre) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
                    some (.pi A u B v) := by
                  rw [applyTelA_append, hT₀]; exact hTpre
                show famRsAg E I n ρ₀ k Γ [] c lsC (np + ksPre.length) (ps ++ pre) f f'
                rw [famRsA_eqg hcm hTfull]
                exact h
            | directRec => exact hX ksPre ks' pre pre' A u B v f f' hks hw hTpre h
          have hw' := argsRelA_snoc hw kd hTpre hkind
          have hT' : applyTelA (pre ++ [f]) T₀ = some (instantiate0A f B) := by
            rw [applyTelA_append, hTpre]; rfl
          have ih := ctorWalkAg hcm hT₀ hX hF hs (ksPre ++ [kd]) ks' (pre ++ [f]) (pre' ++ [f'])
            (by rw [hks, List.append_assoc]; rfl) (Nat.succ.inj hlen) hT' hw'
          rw [List.append_assoc, List.append_assoc] at ih
          exact ih

end Walks

/-! ## (3) the constructor's telescope -/

/-! ## (4) the parameter mirrors -/

section Mirrors
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- A BASE TYPE CONVERSION, at `ls`, gives type equality under a pair's left image, from the right
    side's validity there (`convA_instLevels`, the base's conversion arm). -/
theorem tyConvA_lreqAg (hfc : BaseFundConvAg E₀ E I n ρ₀) (hEN : EnvNormCtorTypeA E)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {a : Nat} {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = a) {Γ : LCtxA} :
    {M P : ExprA} → TyConvA E₀ I a Γ M P →
    (∃ K₀, ∀ K, K₀ ≤ K → ∀ (Δ : LCtxA) (κ : SubstA), Nonempty (CtxWfA E I n Δ) →
      ValidSubstAg E I n ρ₀ K Δ κ κ (instCtxA ls Γ) →
      LREqAg E I n ρ₀ K Δ (substA κ (instantiateLevelsA ls P)) (substA κ (instantiateLevelsA ls P))) →
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ (Δ : LCtxA) (κ : SubstA), Nonempty (CtxWfA E I n Δ) →
      ValidSubstAg E I n ρ₀ K Δ κ κ (instCtxA ls Γ) →
      LREqAg E I n ρ₀ K Δ (substA κ (instantiateLevelsA ls M)) (substA κ (instantiateLevelsA ls P))
  | _, _, .refl _ _, hP => hP
  | _, _, .of _ _ _ _ _ _ _ _ _ _ hc, _ => by
      obtain ⟨K₀, hK₀⟩ := hfc (convA_instLevels hEL₀ hIL hb hl hc)
      refine ⟨K₀, fun K hK Δ κ hΔ hV => ?_⟩
      obtain ⟨_, hrel⟩ := hK₀ K hK Δ κ κ hΔ hV
      exact LREqA_of_sortRelg hrel
  | _, _, .trans _ _ _ _ h₁ h₂, hP => by
      obtain ⟨K₂, hK₂⟩ := tyConvA_lreqAg hfc hEN hEL₀ hIL hb hl h₂ hP
      obtain ⟨K₁, hK₁⟩ := tyConvA_lreqAg hfc hEN hEL₀ hIL hb hl h₁
        ⟨K₂, fun K hK Δ κ hΔ hV => LREqA_transg hEN (hK₂ K hK Δ κ hΔ hV) (LREqA_symmg hEN (hK₂ K hK Δ κ hΔ hV))⟩
      exact ⟨max K₁ K₂, fun K hK Δ κ hΔ hV =>
        LREqA_transg hEN (hK₁ K (Nat.le_trans (Nat.le_max_left _ _) hK) Δ κ hΔ hV)
          (hK₂ K (Nat.le_trans (Nat.le_max_right _ _) hK) Δ κ hΔ hV)⟩

/-- THE PARAMETER MIRRORS RELATE AS THE FAMILY'S PARAMETERS: a list related along the mirror
    telescope, under a valid pair for a base-well-formed context, extends the pair validly for the
    context grown by the family's parameters — each argument carried from its mirror's domain to
    the parameter's along their conversion in the base (`tyConvA_lreqAg`). -/
theorem mirrorSubstAg (hfc : BaseFundConvAg E₀ E I n ρ₀) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = a) :
    {Γp : LCtxA} → {ms ps : List (ExprA × Level)} → MirrorsConvA E₀ I a Γp ms ps →
    CtxWfA E₀ I a (telCtxA ps ++ Γp) →
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) → ∀ (κ κ' : SubstA),
      ValidSubstAg E I n ρ₀ K Δ κ κ' (instCtxA ls Γp) →
      ∀ (B : ExprA) (w : Level) (as as' : List ExprA),
      ArgsRelKAg E I n ρ₀ K Δ (substA κ (piTelA (instDomsA ls ms) B w).1) as as' → as.length = ms.length →
      ValidSubstAg E I n ρ₀ K Δ (consListA as κ) (consListA as' κ') (instCtxA ls (telCtxA ps ++ Γp))
  | _, _, _, .nil _, _ => ⟨0, fun _ _ _ _ κ κ' hV _ _ as as' hrel hlen => by
      cases as with
      | cons _ _ => cases hlen
      | nil =>
          cases as' with
          | cons _ _ => cases argsRelKA_lengthg hrel
          | nil => exact hV⟩
  | _, _, _, .cons Γ M um P up ms ps hc _ tl, hwf => by
      have hwf' : CtxWfA E₀ I a (telCtxA ps ++ (.assumption P :: Γ)) :=
        telCtxA_cons_append (P, up) ps Γ ▸ hwf
      have hPΓ := ctxWfA_drop (telCtxA ps) hwf'
      cases hPΓ with
      | assumption hΓ hPty =>
          obtain ⟨K₁, hK₁⟩ := mirrorSubstAg hfc hE₀ hI hEN hNC hR₀ hEL₀ hIL hb hl tl hwf'
          obtain ⟨K₂, hK₂⟩ := fundLevelsAg hfc hE₀ hI hR₀ hEL₀ hIL hb hb hl hl (eqNList_refl ls) hΓ hPty
          obtain ⟨K₃, hK₃⟩ := tyConvA_lreqAg hfc hEN hEL₀ hIL hb hl hc
            ⟨K₂, fun K hK Δ κ hΔ hV => LREqA_of_sortRelg (hK₂ K hK Δ κ κ hΔ hV).2⟩
          refine ⟨max K₁ (max K₂ K₃), fun K hK Δ hΔ κ κ' hV B w as as' hrel hlen => ?_⟩
          have hk1 : K₁ ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
          have hk2 : K₂ ≤ K := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hK
          have hk3 : K₃ ≤ K := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK
          cases as with
          | nil => cases hlen
          | cons x xs =>
              cases hrel with
              | cons _ _ _ _ _ x' _ xs' h hs =>
                  rw [instantiate0A_substA_up] at hs
                  have he : LREqAg E I n ρ₀ K Δ (substA κ (instantiateLevelsA ls P))
                      (substA κ' (instantiateLevelsA ls P)) := LREqA_of_sortRelg (hK₂ K hk2 Δ κ κ' hΔ hV).2
                  have hMP := hK₃ K hk3 Δ κ hΔ (ValidSubstA_refl_leftg hEN hV)
                  have hV₁ : ValidSubstAg E I n ρ₀ K Δ (SubstA.cons x κ) (SubstA.cons x' κ')
                      (instCtxA ls (.assumption P :: Γ)) := ValidSubstA_consg hEN hV he (LRRelA_transport'g hEN hMP h)
                  have ih := hK₁ K hk1 Δ hΔ _ _ hV₁ B w xs xs' hs (Nat.succ.inj hlen)
                  rw [telCtxA_cons_append]
                  exact ih

end Mirrors

/-! ## (5) a full constructor application -/

section CtorApp
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the canonical fixed point at a weakened context is the clause's own at the composed world
    (R-NoFunRec-1 step 1 (1c-ε1): the canonical data commute with weakening, `lfpWA_reindex`). -/
theorem famLfpWA_wkg (j : Nat) (σ ρ : WkSpecA) (Γ : LCtxA) (f : Nat) (fm : CheckedMemberA) :
    LfpWA (FamPhiWA E I n (wkCtxA σ Γ) f fm (famRsAg E I n ρ₀ j (wkCtxA σ Γ))
      (famRsFAg E I n ρ₀ j (wkCtxA σ Γ) fm) (famRsIAg E I n ρ₀ j (wkCtxA σ Γ))) ρ =
    LfpWA (FamPhiWA E I n Γ f fm (famRsAg E I n ρ₀ j Γ) (famRsFAg E I n ρ₀ j Γ fm) (famRsIAg E I n ρ₀ j Γ))
      (WkSpecA.comp σ ρ) := by
  rw [famRsA_wkCtxg, famRsFA_wkCtxg, famRsIA_wkCtxg, lfpWA_reindex]

/-- THE FUNCTION-RECURSIVE POSITION'S PAIR (R-NoFunRec-1 step 1 (1c-δ)): at a function-recursive field of a
    group constructor's walk, a pair related at the field's own type `Π (B :: Bs), F idx` is a pair of
    the clause's `famFunRelA`. At an extension `ρ'`, the pair weakens (`LRRelA_wkg`) and takes the inner
    arguments, related along the weakened domain, to related full applications (`LRRelA_appsg`); the
    codomain is the family at the weakened parameters, where the relation is the clause's fixed point at
    the weakened context (`lrTyA_fam_canong`), which is the clause's own at `ρ'` (`lfpWA_reindex`: the
    canonical data commute with weakening, `famRsA_wkCtxg`). (1c-ε2d-L2): the declared pair is the
    relation's own typing and conversion at the field's domain (`LRRelA_hasTyg`, `LRRelA_convg`). -/
theorem famFunRelA_of_lrRelg (hE : EnvClosedA E) (hI : IotaLiftA I) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hUT : UniformType fv.sort) {ls : List Level} (hl : ls.length = fm.arity) {lsD : List Level}
    (hXD : eqNList ls lsD) {k : Nat} {Γ : LCtxA} {c : Nat} {cm : CheckedMemberA}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    {kinds ksPre ks : List FieldShape} {jn : Nat}
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ (FieldShape.recursive (jn + 1)) :: ks)
    {ps : List ExprA} (hps : ps.length = fm.nparamsA) {T : ExprA}
    (hTc : applyTelA ps (instantiateLevelsA ls (cm.normA.getD cm.mtypeA)) = some T) {pre : List ExprA}
    (hpl : pre.length = ksPre.length)
    {A : ExprA} {u : Level} {B : ExprA} {v : Level} (hTD : applyTelA pre T = some (.pi A u B v))
    {x x' : ExprA} (hAx : LRRelAg E I n ρ₀ k Γ A x x') :
    famFunRelA E I n Γ fm (innerRelsA (famRsIAg E I n ρ₀ k Γ) [] c ls) ps lsD
      (fun ρ' => LfpWA (FamPhiWA E I n Γ f fm (famRsAg E I n ρ₀ k Γ) (famRsFAg E I n ρ₀ k Γ fm)
        (famRsIAg E I n ρ₀ k Γ)) ρ')
      (fm.nparamsA + ksPre.length) (ps ++ pre) A jn x x' := by
  refine ⟨?_, (LRRelA_hasTyg hAx).1, (LRRelA_hasTyg hAx).2, LRRelA_convg hAx⟩
  intro ρ' hρ' ys ys' C hys hlen hC
  have hz : isZero (instLevel ls fv.sort) = false :=
    isZero_false_of_uniformType (uniformType_instLevel hUT ls)
  have hnr : fm.mclass ≠ .recursorM := by rw [hcls]; exact fun h => MemberClass.noConfusion h
  obtain ⟨gc₀, _, hgr₀, hgm₀⟩ := hcensus c cm hcm hk hfam
  have hncl : ∀ k, liftA k 1 (cm.normA.getD cm.mtypeA) = cm.normA.getD cm.mtypeA :=
    hgm₀ ▸ fun k => gc₀.normA_getD_closed k
  have hcl := liftA_instantiateLevelsA_closed hncl ls
  have hTfull : applyTelA (ps ++ pre) (instantiateLevelsA ls (cm.normA.getD cm.mtypeA)) = some (.pi A u B v) := by
    rw [applyTelA_append, hTc]; exact hTD
  have hTc_c : applyTelA (ps.map (wkExprA ρ')) (instantiateLevelsA ls (cm.normA.getD cm.mtypeA)) = some (wkExprA ρ' T) := by
    rw [applyTelA_wk_closed ρ' ps hcl, hTc]; rfl
  have hTD_c : applyTelA (pre.map (wkExprA ρ')) (wkExprA ρ' T) =
      some (.pi (wkExprA ρ' A) u (wkExprA (WkSpecA.ub ρ') B) v) := by
    rw [applyTelA_wk, hTD, Option.map_some', wkExprA_pi_ub]
  obtain ⟨ds, idxI, σ, hds, hAe⟩ := ctorFrecDomA hfresh hcensus hl ((by rw [List.length_map, hps]) : (ps.map (wkExprA ρ')).length = fm.nparamsA)
    hcm hk hfam hkinds hsp hTc_c (by rw [List.length_map, hpl]) hTD_c
  have hpi : IsPiTelA (jn + 1) (wkExprA ρ' A) := by
    rw [hAe]
    have h := isPiTelA_ctorFieldsA f ls (instLevel ls fv.sort) idxI hz (ds.map plainA) (ps.map (wkExprA ρ')) σ
    rw [List.length_map, hds] at h
    exact h
  have hys' := argsRelKA_of_innerRelsAg (ρ := []) hE hNC hcm (envNormClosedA_getD hNC hE hcm hk) hTfull hys rfl
  have hAx' := LRRelA_wkg hE hNC hI hAx ρ' hρ'
  obtain ⟨RC, hRC, hab⟩ := LRRelA_appsg hρ'.2 hys' (jn + 1) (Nat.le_of_eq hlen) hpi hAx' C hC
  have hCe : C = foldAppsA (.const f ls) (ps.map (wkExprA ρ') ++ idxI.map (substA
      (consListA (plainArgsA (ds.map plainA) ys) σ))) := by
    rw [hAe] at hC
    have h := applyTelA_ctorFieldsA f ls (instLevel ls fv.sort) idxI (ds.map plainA) ys
      (by rw [List.length_map, hds, hlen]) (ps.map (wkExprA ρ')) σ
    exact Option.some.inj (hC.symm.trans h)
  have hpsw : (ps.map (wkExprA ρ')).length = fm.nparamsA := by rw [List.length_map, hps]
  refine ⟨by rw [hCe, carrierParamsA_foldAppsA, List.take_left' hpsw],
    by rw [hCe, carrierLevelsA_foldAppsA]; exact hXD, ?_⟩
  have hnD : hStepFnA E I.fn (wkCtxA ρ' Γ) C = none := by
    rw [hCe]
    exact hStepFnA_constSpine_none hR hfm (Or.inr hnobody) hnr (wkCtxA ρ' Γ) (ls := ls) _
      (by rw [foldAppsA_const_head])
  have hnpD : ¬ IsPropTy E I (wkCtxA ρ' Γ) C := fun h => by
    rw [hCe] at h
    have h3 := ((isPropTy_famApp_iff hfm fv.piBody ls _).mp h).2.2
    rw [hz] at h3
    cases h3
  rw [hCe] at hRC
  have hcan := lrTyA_fam_canong hE hNC hfm hcls hpsw (by rw [← hCe]; exact hnD) (by rw [← hCe]; exact hnpD) hRC
  rw [hcan] at hab
  rw [famLfpWA_wkg, WkSpecA.comp_nil] at hab
  rw [hCe]
  exact hab

/-- THE FULL CONSTRUCTOR APPLICATIONS, RELATED AT THE RESULT. At a Type family's group constructor,
    two full applications at bounded `=ₙ` lists to arguments related along the constructor's type at
    the left list are related at the result, a family application, at its height or above. The
    result is valid there (`spineConvAg`), with the canonical fixed point as its relation
    (`lrTyA_fam_canong`); the two applications are its constructor disjunct: typed and convertible,
    rigid, the fields walking with the canonical relations (`ctorWalkAg`; a recursive field by
    canonicity at its domain, `ctorDrecDomA`, a function-recursive one by `famFunRelA_of_lrRelg`), and the results coherent with the carrier
    (`resDomAg`, under the parameters' valid pair from the mirrors, `mirrorSubstAg`, and the fields'
    from the walk, `fieldWalkAg`, `famAppArgsAg`). -/
theorem ctorAppRelAg (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E) (hR : IotaRecHeadA E I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    (gc : GroupCtorA I E₀ f fm fv) (hgc : E.members gc.ref = some gc.member)
    {ls ls' : List Level} (hb : levelsBounded n ls = true) (hb' : levelsBounded n ls' = true)
    (hl : ls.length = fm.arity) (hls : eqNList ls ls')
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) (hk : ht ρ₀ (instLevel ls fv.sort) ≤ k)
    {RT : ExprA → ExprA → Prop} (hRT : LRTyAg E I n ρ₀ k Γ (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)) RT)
    (hf₁ : HasTyA E I n Γ (.const gc.ref ls) (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)))
    (hf₂ : HasTyA E I n Γ (.const gc.ref ls') (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)))
    (hfc₁ : ConvA E I n Γ (.const gc.ref ls) (.const gc.ref ls') (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)))
    {as as' : List ExprA} (hrel : ArgsRelKAg E I n ρ₀ k Γ (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)) as as')
    (hlen : as.length = gc.view.mirrors.length + gc.view.fields.length)
    {C : ExprA} (hC : applyTelA as (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)) = some C) :
    LRRelAg E I n ρ₀ k Γ C (foldAppsA (.const gc.ref ls) as) (foldAppsA (.const gc.ref ls') as') := by
  have hz : isZero (instLevel ls fv.sort) = false :=
    isZero_false_of_uniformType (uniformType_instLevel hUT ls)
  have hl' : ls'.length = fm.arity := (eqNList_length ls ls' hls).symm.trans hl
  have hmir : gc.view.mirrors.length = fm.nparamsA := by rw [gc.view.mirrorsConv.length, fv.nparams]
  have hlen' := (argsRelKA_lengthg hrel).symm.trans hlen
  have hnr : fm.mclass ≠ .recursorM := by rw [hcls]; exact fun h => MemberClass.noConfusion h
  have hnrc : gc.member.mclass ≠ .recursorM := by rw [gc.hcls]; exact fun h => MemberClass.noConfusion h
  -- the spines: typed at the result, convertible, the result valid
  obtain ⟨⟨hAty⟩, ⟨hBty⟩, ⟨hconv⟩, ⟨RC, hRC⟩⟩ := spineConvAg hE hI hEN hΓ hrel _ (Nat.le_of_eq hlen)
    (gc.isPiTel ls hl hz) hRT hf₁ hf₂ hfc₁ C hC
  -- split at the parameters
  have hnp₀ : fm.nparamsA ≤ as.length := by rw [hlen, ← hmir]; exact Nat.le_add_right _ _
  have hnp₀' : fm.nparamsA ≤ as'.length := by rw [hlen', ← hmir]; exact Nat.le_add_right _ _
  obtain ⟨ps, fs, rfl, hps⟩ : ∃ ps fs, as = ps ++ fs ∧ ps.length = fm.nparamsA :=
    ⟨as.take fm.nparamsA, as.drop fm.nparamsA, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; exact Nat.min_eq_left hnp₀⟩
  obtain ⟨ps', fs', rfl, hps'⟩ : ∃ ps fs, as' = ps ++ fs ∧ ps.length = fm.nparamsA :=
    ⟨as'.take fm.nparamsA, as'.drop fm.nparamsA, (List.take_append_drop _ _).symm,
      by rw [List.length_take]; exact Nat.min_eq_left hnp₀'⟩
  have hfsl : fs.length = gc.view.fields.length := by
    rw [List.length_append, hps, ← hmir] at hlen; omega
  have hfsl' : fs'.length = gc.view.fields.length := by
    rw [List.length_append, hps', ← hmir] at hlen'; omega
  obtain ⟨T₁, hT₁, hrelP, hrelF⟩ := argsRelKA_append_invg (hps.trans hps'.symm) hrel
  have hTv := gc.applyTel_params ls hl ps hps
  rw [hT₁] at hTv
  injection hTv with hT₁e
  subst hT₁e
  have hTv₁ := gc.applyTel_params ls hl ps hps
  have hTv₂ := gc.applyTel_params ls' hl' ps hps
  -- the canonical relation at the carrier height `k`
  have hkinds := gc.view.shapes hfresh
  have hwalk : ArgsRelA (famRsAg E I n ρ₀ k Γ [] gc.ref ls)
      (famRecRelA fm ps ls (fun D a b => LfpWA (FamPhiWA E I n Γ f fm (famRsAg E I n ρ₀ k Γ)
        (famRsFAg E I n ρ₀ k Γ fm) (famRsIAg E I n ρ₀ k Γ)) [] D a b))
      (famFunRelA E I n Γ fm (innerRelsA (famRsIAg E I n ρ₀ k Γ) [] gc.ref ls) ps ls
        (fun ρ' => LfpWA (FamPhiWA E I n Γ f fm (famRsAg E I n ρ₀ k Γ) (famRsFAg E I n ρ₀ k Γ fm)
          (famRsIAg E I n ρ₀ k Γ)) ρ'))
      fm.nparamsA ps (ctorFieldsA f ls (instLevel ls fv.sort) ps (consListA ps SubstA.id)
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels ls)) (gc.view.res.map (instantiateLevelsA ls))).1
      (gc.view.fields.map FieldA.shape) fs fs' := by
    have h := ctorWalkAg (np := fm.nparamsA) hgc hTv₁
      (X := famRecRelA fm ps ls (fun D a b => LfpWA (FamPhiWA E I n Γ f fm (famRsAg E I n ρ₀ k Γ)
        (famRsFAg E I n ρ₀ k Γ fm) (famRsIAg E I n ρ₀ k Γ)) [] D a b))
      (F := famFunRelA E I n Γ fm (innerRelsA (famRsIAg E I n ρ₀ k Γ) [] gc.ref ls) ps ls
        (fun ρ' => LfpWA (FamPhiWA E I n Γ f fm (famRsAg E I n ρ₀ k Γ) (famRsFAg E I n ρ₀ k Γ fm)
          (famRsIAg E I n ρ₀ k Γ)) ρ'))
      (ksAll := gc.view.fields.map FieldA.shape)
      (fun ksPre ks pre pre' A u B v x x' hsp hw hTD hAx => by
        obtain ⟨isD, rfl⟩ := ctorDrecDomA hfresh hcensus hl hps hgc gc.hcls gc.view.famRef
            (gc.normA_getD.symm ▸ hkinds) hsp hTv₁
          hw hTD
        refine ⟨by rw [carrierParamsA_foldAppsA, ← hps, List.take_left],
          by rw [carrierLevelsA_foldAppsA]; exact eqNList_refl ls, ?_⟩
        obtain ⟨RD, hRD, hab⟩ := hAx
        have hnD : hStepFnA E I.fn Γ (foldAppsA (.const f ls) (ps ++ isD)) = none :=
          hStepFnA_constSpine_none hR hfm (Or.inr hnobody) hnr Γ (ls := ls) _ (by rw [foldAppsA_const_head])
        have hnpD : ¬ IsPropTy E I Γ (foldAppsA (.const f ls) (ps ++ isD)) := fun h => by
          have h3 := ((isPropTy_famApp_iff hfm fv.piBody ls (ps ++ isD)).mp h).2.2
          rw [hz] at h3
          cases h3
        rw [lrTyA_fam_canong hE hNC hfm hcls hps hnD hnpD hRD] at hab
        exact hab)
      (fun ksPre ks j pre pre' A u B v x x' hsp hw hTD hAx =>
        famFunRelA_of_lrRelg hE hI hNC hR hfm hcls hnobody hfresh hcensus hUT hl (eqNList_refl ls) hgc gc.hcls gc.view.famRef (gc.normA_getD.symm ▸ hkinds)
          hsp hps hTv₁ (argsRelA_length hw).1 hTD hAx)
      hrelF [] _ [] [] rfl (by rw [List.length_map, hfsl]) rfl (.nil _ _ _)
    simpa only [List.nil_append] using h
  -- the parameters' valid pair, from the mirrors
  obtain ⟨hwf⟩ := fv.paramsCtxWf hT
  have hwf₀ : CtxWfA E₀ I fm.arity (telCtxA fv.params ++ []) := (List.append_nil _).symm ▸ hwf
  obtain ⟨Km, hKm⟩ := mirrorSubstAg hfc hE₀ hI hEN hNC hR₀ hEL₀ hIL hb hl gc.view.mirrorsConv hwf₀
  -- the fields' typing and the result's indices
  have hty : FieldsTyA E₀ I fm.arity (fun k => liftA 0 k fv.idxTelA) (telCtxA fv.params) 0
      (gc.view.fields ++ []) gc.view.res := (List.append_nil _).symm ▸ gc.view.typed
  obtain ⟨Kw, hKw⟩ := fieldWalkAg (f := f) (s := instLevel ls fv.sort) (pl := ps) (j := k) (Γ := Γ)
    (ρ := []) (X := fun _ _ _ => True) (F := fun _ _ _ _ _ _ => True) hfc hE₀ hI hEN hR₀ hEL₀ hIL hb hl hgc hΓ gc.view.fields hty hwf
  have hdrop := FieldsTyA.drop gc.view.fields hty
  have hΓp := ctxWfA_plainCtx gc.view.fields hty hwf
  cases hdrop with
  | nil _ _ _ hres =>
      obtain ⟨Ka, hKa⟩ := famAppArgsAg hfc hEN hNC hE₀ hI hR₀ hEL₀ hIL fv hb hb hl hl (eqNList_refl ls) hΓp hres
      have hK1 : Km ≤ max (max Km Kw) (max Ka k) :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      have hK2 : Kw ≤ max (max Km Kw) (max Ka k) :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
      have hK3 : Ka ≤ max (max Km Kw) (max Ka k) :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have hKk : k ≤ max (max Km Kw) (max Ka k) :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      have hrelP' := argsRelKA_monog hKk hrelP
      rw [gc.inst_tel ls hl, ← substA_id (ctorTypeA _ _ _ _ _ _)] at hrelP'
      have hV₀ := hKm _ hK1 Γ hΓ SubstA.id SubstA.id (ValidSubstA_nilg _ _ _) _ _ ps ps' hrelP'
        (by rw [hps, ← hmir])
      rw [List.append_nil] at hV₀
      have hV₀d := ValidSubstA_refl_leftg hEN hV₀
      have hTc₀ := hTv₁
      rw [show gc.view.fields = gc.view.fields ++ [] from (List.append_nil _).symm] at hTc₀
      have hw₀ := argsRelA_diag hEN (famRsA_refl_leftg hEN) hwalk
      rw [show List.map FieldA.norm gc.view.fields =
        List.map FieldA.norm (gc.view.fields ++ []) by rw [List.append_nil]] at hw₀
      have hV₁ := hKw _ hK2 hKk _ _ fm.nparamsA ps fs fs hV₀d hTc₀ hw₀
      have hjc : plainIdxA gc.view.fields 0 = (plainArgsA gc.view.fields fs).length := by
        rw [plainIdxA_length gc.view.fields fs (by rw [hfsl]) 0, Nat.zero_add]
      obtain ⟨_, hrelC⟩ := hKa _ hK3 Γ hΓ ps ps _ _ hps hps hjc hV₀d hV₁
      -- the result
      have hpfx := applyTelA_ctorFieldsA_prefix f ls (instLevel ls fv.sort)
        (gc.view.res.map (instantiateLevelsA ls)) []
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels ls)) fs
        (by rw [List.length_map, List.length_map]; exact hfsl) ps (consListA ps SubstA.id)
      rw [List.append_nil, plainArgsA_instLevels] at hpfx
      have hCfs : applyTelA fs (ctorFieldsA f ls (instLevel ls fv.sort) ps (consListA ps SubstA.id)
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels ls))
          (gc.view.res.map (instantiateLevelsA ls))).1 = some C := by
        rw [applyTelA_append, hTv₁] at hC; exact hC
      have hCfs₀ := hCfs
      rw [hpfx] at hCfs
      simp only [ctorFieldsA] at hCfs
      injection hCfs with hCe
      have e1 : (gc.view.res.map (instantiateLevelsA ls)).map
          (substA (consListA (plainArgsA gc.view.fields fs) (consListA ps SubstA.id))) =
          gc.view.res.map (fun x => substA (consListA (plainArgsA gc.view.fields fs) (consListA ps SubstA.id))
            (instantiateLevelsA ls x)) := by
        rw [List.map_map]; rfl
      have hrelC' := hrelC
      rw [← e1] at hrelC'
      -- the right result
      have hpfx' := applyTelA_ctorFieldsA_prefix f ls' (instLevel ls' fv.sort)
        (gc.view.res.map (instantiateLevelsA ls')) []
        ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels ls')) fs'
        (by rw [List.length_map, List.length_map]; exact hfsl') ps (consListA ps SubstA.id)
      rw [List.append_nil, plainArgsA_instLevels] at hpfx'
      -- coherence with the carrier
      have hcoh := resDomAg (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT
        hb hl hk hΓ (ps := ps) (ps' := ps) hps hps hrelC' (wkOk₀A_nil E I n Γ) hgc gc.hcls
        gc.view.famRef (gc.normA_getD.symm ▸ hkinds) (eqNList_refl ls) (eqNListB_refl hb) ⟨hls, hb'⟩
        (by rw [map_wkExprA_nil]; exact hTv₁) (by rw [map_wkExprA_nil]; exact hTv₂)
        (by rw [map_wkExprA_nil]; exact hwalk) hCfs₀ hpfx'
      rw [map_wkExprA_nil] at hcoh
      obtain ⟨lsA, lsA', isA, isA', TF, TF', hCe', hR'e, hlA, hlAA, hTF, _, hwI, _⟩ := hcoh
      subst hCe'
      obtain ⟨_, els, _⟩ := foldAppsA_const_inj hCe
      subst els
      have hnA : hStepFnA E I.fn Γ (foldAppsA (.const gc.ref ls) (ps ++ fs)) = none :=
        hStepFnA_constSpine_none hR hgc (Or.inr gc.hnobody) hnrc Γ (ls := ls) _ (by rw [foldAppsA_const_head])
      have hnB : hStepFnA E I.fn Γ (foldAppsA (.const gc.ref ls') (ps' ++ fs')) = none :=
        hStepFnA_constSpine_none hR hgc (Or.inr gc.hnobody) hnrc Γ (ls := ls') _ (by rw [foldAppsA_const_head])
      have hnC : hStepFnA E I.fn Γ (foldAppsA (.const f ls) (ps ++ isA)) = none :=
        hStepFnA_constSpine_none hR hfm (Or.inr hnobody) hnr Γ (ls := ls) _ (by rw [foldAppsA_const_head])
      have hnpC : ¬ IsPropTy E I Γ (foldAppsA (.const f ls) (ps ++ isA)) := fun h => by
        have h3 := ((isPropTy_famApp_iff hfm fv.piBody ls (ps ++ isA)).mp h).2.2
        rw [hz] at h3
        cases h3
      have hCp : carrierParamsA fm (foldAppsA (.const f ls) (ps ++ isA)) = ps := by
        rw [carrierParamsA_foldAppsA, ← hps, List.take_left]
      have hCl : carrierLevelsA (foldAppsA (.const f ls) (ps ++ isA)) = ls := carrierLevelsA_foldAppsA _ _ _
      have htk : (ps ++ isA).take fm.nparamsA = ps := by rw [← hps, List.take_left]
      have hdr : (ps ++ isA).drop fm.nparamsA = isA := by rw [← hps, List.drop_left]
      -- P2: the parameters convertible with the carrier's, at both level lists — the mirrors'
      -- valid pair read along the family's type (`famParConvAg`)
      have hV₀P := hV₀
      rw [← telCtxA_instDomsA] at hV₀P
      have hrelPF : ArgsRelKAg E I n ρ₀ (max (max Km Kw) (max Ka k)) Γ (instantiateLevelsA ls fm.mtypeA)
          (ps ++ []) (ps' ++ []) := by
        rw [List.append_nil, List.append_nil, fv.inst_split]
        exact argsRelKA_of_validSubstg hEN _ _ _ ps ps' (by simp [instDomsA, hps, fv.nparams])
          (by simp [instDomsA, hps', fv.nparams]) hV₀P
      have hP2 := famParConvAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hl hΓ hps hps' hrelPF []
        (wkOk₀A_nil E I n Γ)
      simp only [map_wkExprA_nil] at hP2
      have hP2l := hP2 ls (eqNListB_refl hb)
      refine ⟨RC, hRC, ?_⟩
      rw [lrTyA_fam_canong hE hNC hfm hcls hps hnC hnpC hRC]
      refine LfpWA.fold famPhiWA_mono ⟨⟨hconv⟩, Or.inl ⟨gc.ref, gc.member, ls, ls',
        gc.view.fields.map FieldA.shape, ps, ps', fs, fs',
        (ctorFieldsA f ls (instLevel ls fv.sort) ps (consListA ps SubstA.id)
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels ls)) (gc.view.res.map (instantiateLevelsA ls))).1,
        (ctorFieldsA f ls' (instLevel ls' fv.sort) ps (consListA ps SubstA.id)
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels ls')) (gc.view.res.map (instantiateLevelsA ls'))).1,
        hgc, gc.hcls, gc.view.famRef, ?_, ⟨hls, hb'⟩, (gc.normA_getD.symm ▸ hkinds), ?_, ?_, ?_, hps, hps',
        tyHRedStarA_refl hAty, tyHRedStarA_refl hBty, hnA, hnB, ?_⟩⟩
      · rw [hCl]; exact ⟨⟨eqNList_refl ls, hb⟩, hb⟩
      · rw [hCp]; exact hTv₁
      · rw [hCp]; exact hTv₂
      · refine ⟨ls, ls, lsA', ps ++ isA, isA, isA', TF, _, _, foldAppsA_const_head _ _ _, ?_, hCfs₀, ?_,
          eqNList_refl ls, ?_, hpfx', ?_, hlAA.1, ?_⟩
        · rw [htk]; exact hTF
        · rw [foldAppsA_const_head, htk]
        · rw [htk, hdr]; exact argsRelPA_diag hEN (famRsFA_refl_leftg hEN) hwI
        · rw [hR'e, foldAppsA_const_head, htk]
        · rw [htk, hdr]; exact hwI
      · rw [hCp, hCl]
        exact ⟨hwalk, parConvA_convArgsA (parConvA_trans hP2l (parConvA_symm hP2l)),
          parConvA_convArgsA (hP2 ls' ⟨hls, hb'⟩)⟩

end CtorApp

/-! ## (6) the clause at a constructor -/

section CtorClause
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- THE CONSTRUCTOR'S CLAUSE (`EnvSemClauseAg`) at a group's constructor, with the family's clause in
    hand (the base extended by the family satisfies the fundamental theorem): the constructor's type
    is valid and its two heads typed and convertible (`famHeadsAg` on its typing in the base and the
    family). A Prop family's constructor type is a proposition, where the two heads are related by
    the `prop` clause. A Type family's are related by the telescope lemma, every full application
    pair related at the result (`ctorAppRelAg`). -/
theorem ctorSemClauseAg (hfund : BaseFundAg E₀ E I n ρ₀) (hfc : BaseFundConvAg E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hfc₁ : BaseFundConvAg (extendEnvA E₀ f fm) E I n ρ₀)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E) (hR : IotaRecHeadA E I)
    (hE₁ : EnvClosedA (extendEnvA E₀ f fm)) (hR₁ : IotaRecHeadTypedA (extendEnvA E₀ f fm) I)
    (hEL₁ : EnvLevelsA (extendEnvA E₀ f fm))
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hnobody : fm.bodyA = none)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hpre₁ : PrefixA (extendEnvA E₀ f fm) E)
    (gc : GroupCtorA I E₀ f fm fv) (hgc : E.members gc.ref = some gc.member) :
    EnvSemClauseAg E I n ρ₀ gc.ref gc.member := by
  intro ls ls' hl hb hb' heq
  have hlf : ls.length = fm.arity := hl.trans gc.harity
  have hl' : ls'.length = gc.member.arity := (eqNList_length ls ls' heq).symm.trans hl
  have hnr : fm.mclass ≠ .recursorM := by rw [hcls]; exact fun h => MemberClass.noConfusion h
  obtain ⟨K₀, hK₀⟩ := famHeadsAg hfc₁ hE₁ hI hR₁ hEL₁ hIL hgc gc.hT hb hb' hl hl' heq
  -- the stored↔δ-normal bridge (R-NoDeltaRec-4d-iii): the view's `normConv` at the family's
  -- extension, instantiated and lifted to the big env's relation by `tyConvA_lreqAg` — seeded
  -- by the normal form's own validity (`normTyped`) — and to any context by closed weakening.
  -- The clause's outer contract stays at the stored type; all internal work runs normal-side.
  obtain ⟨tc⟩ := gc.view.normConv
  have tc' : TyConvA (extendEnvA E₀ f fm) I fm.arity [] gc.member.mtypeA
      (gc.member.normA.getD gc.member.mtypeA) := by
    rw [gc.normA_getD, gc.view.stored]; exact tc
  have hTCG : ∀ Γ : LCtxA, TyConvA E I n Γ (instantiateLevelsA ls gc.member.mtypeA)
      (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)) := fun Γ =>
    tyConvA_closedWeaken hE hI (liftA_instantiateLevelsA_closed gc.hclT ls)
      (liftA_instantiateLevelsA_closed gc.normA_getD_closed ls) Γ
      (tyConvA_env hpre₁ (tyConvA_instLevels hEL₁ hIL hb hlf tc'))
  obtain ⟨lN, ⟨hNT⟩⟩ := gc.view.normTyped
  have hNT' : HasTyA (extendEnvA E₀ f fm) I fm.arity []
      (gc.member.normA.getD gc.member.mtypeA) (.sort lN) := by
    rw [gc.normA_getD]; exact hNT
  obtain ⟨KN, hKN⟩ := fundLevelsAg hfc₁ hE₁ hI hR₁ hEL₁ hIL hb hb hlf hlf (eqNList_refl ls)
    .nil hNT'
  obtain ⟨KT, hKT⟩ := tyConvA_lreqAg hfc₁ hEN hEL₁ hIL hb hlf tc'
    ⟨KN, fun K hK Δ κ hΔ hV => LREqA_of_sortRelg (hKN K hK Δ κ κ hΔ hV).2⟩
  refine ⟨max K₀ (max KT (ht ρ₀ (instLevel ls fv.sort) + 1)), fun k hk Δ hΔ => ?_⟩
  have hk0 : K₀ ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hkT : KT ≤ k := Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_right _ _) hk)
  have hks : ht ρ₀ (instLevel ls fv.sort) ≤ k :=
    Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hk)))
  have hLE : LREqAg E I n ρ₀ k Δ (instantiateLevelsA ls gc.member.mtypeA)
      (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)) := by
    have h := hKT k hkT Δ SubstA.id hΔ (ValidSubstA_nilg _ _ _)
    rwa [substA_id, substA_id] at h
  obtain ⟨⟨RT, hRT⟩, ⟨hf₁⟩, ⟨hf₂⟩, ⟨hfc₁'⟩⟩ := hK₀ k hk0 Δ hΔ
  have hTCΔ := hTCG Δ
  obtain ⟨RT', hRTN⟩ := LREqA_validg hEN hLE ⟨RT, hRT⟩
  rcases fv.profile with hUP | hUT
  · -- a Prop family: the constructor's type is a proposition
    have hz : isZero (instLevel ls fv.sort) = true :=
      (isZero_iff_eqN_zero _).mpr (uniformProp_eqN_zero (uniformProp_instLevel hUP ls))
    obtain ⟨hn, hP⟩ := gc.propTy hfm hR hnobody hnr ls hlf hz Δ
    have hRTN' := hRTN
    rw [LRTyA_eqg] at hRTN'
    obtain ⟨_, ⟨hTtyN⟩⟩ := tyKA_hasTyg hRTN'
    have hpr := TyKAg.prop (E := E) (I := I) (n := n) (ρ₀ := ρ₀) (k := k)
      (LE := fun j _ => LREqAg E I n ρ₀ j) (LT := fun j _ => LRTyAg E I n ρ₀ j) (whTyA_of_hasTy hTtyN) hn hP
    rw [← LRTyA_eqg] at hpr
    exact LRRelA_transport'g hEN (LREqA_symmg hEN hLE)
      ⟨_, hpr, ⟨hasTyA_of_tyConvA hf₁ hTCΔ⟩, ⟨hasTyA_of_tyConvA hf₂ hTCΔ⟩,
        ⟨convA_of_tyConvA hfc₁' hTCΔ⟩⟩
  · -- a Type family: the telescope lemma, normal-side, transported back at the boundary
    have hz : isZero (instLevel ls fv.sort) = false :=
      isZero_false_of_uniformType (uniformType_instLevel hUT ls)
    have hTcl : ∀ j, liftA j 1 (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)) =
      instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA) :=
    liftA_instantiateLevelsA_closed gc.normA_getD_closed ls
    refine LRRelA_transport'g hEN (LREqA_symmg hEN hLE)
      ⟨RT', hRTN, telIntroAg hE hI hEN hNC _ hΔ (gc.isPiTel ls hlf hz) hRTN
        ⟨hasTyA_of_tyConvA hf₁ hTCΔ⟩ ⟨hasTyA_of_tyConvA hf₂ hTCΔ⟩
        ⟨convA_of_tyConvA hfc₁' hTCΔ⟩ ?_⟩
    intro ρ hρ as as' hrel hlen C hC
    rw [wkExprA_closed hTcl] at hrel hC
    rw [wkExprA_const, wkExprA_const]
    obtain ⟨⟨RTρ, hRTρ⟩, ⟨hf₁ρ⟩, ⟨hf₂ρ⟩, ⟨hfc₁ρ⟩⟩ := hK₀ k hk0 (wkCtxA ρ Δ) hρ.2
    have hLEρ : LREqAg E I n ρ₀ k (wkCtxA ρ Δ) (instantiateLevelsA ls gc.member.mtypeA)
        (instantiateLevelsA ls (gc.member.normA.getD gc.member.mtypeA)) := by
      have h := hKT k hkT (wkCtxA ρ Δ) SubstA.id hρ.2 (ValidSubstA_nilg _ _ _)
      rwa [substA_id, substA_id] at h
    obtain ⟨RTρ', hRTNρ⟩ := LREqA_validg hEN hLEρ ⟨RTρ, hRTρ⟩
    have hTCρ := hTCG (wkCtxA ρ Δ)
    exact ctorAppRelAg hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hR hfm hcls hnobody hfresh hcensus hcl hT hUT gc hgc
      hb hb' hlf heq hρ.2 hks hRTNρ (hasTyA_of_tyConvA hf₁ρ hTCρ) (hasTyA_of_tyConvA hf₂ρ hTCρ)
      (convA_of_tyConvA hfc₁ρ hTCρ) hrel hlen hC

/-- THE CONSTRUCTORS' CLAUSE AT THEIR GROUP STEP (`EnvSemCtorStepAg`), under the small-index
    profile: the base's fundamental theorem and the base-and-family's, from their clauses
    (`baseFundA_ofg`); the census from closure. -/
theorem envSemCtorStepA_of_profileg (hE : EnvClosedA E) (hEL : EnvLevelsA E) (hI : IotaLiftA I)
    (hIS : IotaSubstA I) (hIL : IotaLevelsA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hK : PropKeyA E I n)
    (hS : SmallIndexProfileA E) : EnvSemCtorStepAg E I n ρ₀ := by
  intro E₀ f fm u hW hcls hnobody hclT hT fv cs hfresh hpre hclo ihF gc hgc
  have hpre₁ : PrefixA (extendEnvA E₀ f fm) E := prefixA_trans (prefixA_extend_groupEnvA hfresh) hpre
  have hpre₀ : PrefixA E₀ E := prefixA_trans (prefixA_groupEnvA hfresh) hpre
  have ih₀ : EnvSemAtg E I n ρ₀ (domA E₀) := fun r m hD hres => ihF r m (domA_extendEnvA hD) hres
  obtain ⟨hfund, hfc⟩ := baseFundA_ofg hE hI hIS hEN hNC hR hρ hK hpre₀ ih₀
  obtain ⟨_, hfc₁⟩ := baseFundA_ofg hE hI hIS hEN hNC hR hρ hK hpre₁ ihF
  exact ctorSemClauseAg hfund hfc hEN hNC hfc₁ (envWfA_closed hW) hE hI (iotaRecHeadTypedA_prefix hpre₀ hR)
    (envWfA_levels hW) hIL hS hR (fun r m h => hE r m (hpre₁ r m h)) (iotaRecHeadTypedA_prefix hpre₁ hR)
    (fun r m h => hEL r m (hpre₁ r m h)) (hpre f fm (members_groupEnvA_family hfresh)) hcls hnobody
    hfresh.base (fun _ _ hc hk hf => groupCensusA hcls hfresh (ctorFamInA_of_envWfA hW) hclo hc hk hf) hclT hT
    hpre₁ gc (hpre _ _ (members_groupEnvA_ctor hfresh hgc))

/-- THE SEMANTIC ENVIRONMENT WITH THE FAMILIES AND THE CONSTRUCTORS DISCHARGED: a well-formed
    environment with the small-index profile satisfies `EnvSemAg` given the clause at its recursors
    alone (`EnvSemRecAg`, M2-f (5)). -/
theorem envSemA_of_envWfA_groupsg (hW : EnvWfA I E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hIL : IotaLevelsA I) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hρ : PosValA ρ₀) (hK : PropKeyA E I n) (hS : SmallIndexProfileA E)
    (hRec : EnvSemRecAg E I n ρ₀) : EnvSemAg E I n ρ₀ :=
  fun r m hres =>
    envSemAt_of_envWfAg (envWfA_closed hW) (envWfA_levels hW) hI hIS hIL hEN hNC hR hρ hK
      (envSemFamStepA_of_profileg (envWfA_closed hW) (envWfA_levels hW) hI hIS hIL hEN hNC hR hρ hK hS)
      (envSemCtorStepA_of_profileg (envWfA_closed hW) (envWfA_levels hW) hI hIS hIL hEN hNC hR hρ hK hS)
      (envSemRecStepA_of_recg hRec) hW
      (prefixA_refl E) (ctorClosedA_refl E) r m ⟨m, hres⟩ hres

end CtorClause

#print axioms lrTyA_fam_canong
#print axioms ctorWalkAg
#print axioms famLfpWA_wkg
#print axioms famFunRelA_of_lrRelg
#print axioms tyConvA_lreqAg
#print axioms mirrorSubstAg
#print axioms ctorAppRelAg
#print axioms ctorSemClauseAg
#print axioms envSemCtorStepA_of_profileg
#print axioms envSemA_of_envWfA_groupsg

end Rcic.Declarative.Ann
