/-
# RcicSynMSAP — the member-sort assumption-prefix hypothesis (L-MSAP)

`RcicSynBelowCToRows.lean` threads `StepSuppliers → AllBelowScoped → SortCoh → TypedRowsWf`
conditionally; its sortRow leg takes the hypothesis

    hMSAP : MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv)

i.e. every member's *enriched* stored-type derivation `TyP.ewk … (typeAdm hres).hT`
satisfies `TyP.AssumpPref`. This module **proves that hypothesis outright** —
`memberSortP_of_envWfT_ap` — by induction over `EnvWfT`:

* `typeAdm`'s `isTrue` arms return the `EnvWfP`/`GroupMembersP` constructor's own stored
  `hA`/`hT` field; under `enrichEnvWfT`/`enrichGroupMembersT` those fields are
  `enrichHasTyT` outputs, whose AP is the landed `assumpPref_enrichHasTyT`.
* `typeAdm`'s `isFalse` arms return `TypeAdm.step`, which keeps `.hT` unchanged —
  the prefix induction hypothesis.
* The one genuinely new stone is `memberSortP_extendEnv_ap`: `memberSortP_extendEnv`'s
  `by`-compiled body is `Eq.rec`-laden, but after `unfold`+`dsimp` the dite splits and
  both arms reduce to `TyP.ewk` wraps — AP follows the ewk arm of `TyP.AssumpPref`.

No `sorry`, no new axioms: everything rides the landed AP machinery.
-/
import rcic.RcicSynEnrich
import rcic.RcicSynWalkLetAP

open Rcic.Declarative
namespace Rcic.Syn

/-- **Extension step.** `memberSortP_extendEnv` splits the membership evidence:
    at the fresh index it returns `TyP.ewk hT`, otherwise `TyP.ewk (hm's derivation)` —
    the `ewk` arm of `TyP.AssumpPref` is the child's AP, so both arms are AP when the
    inputs are. The `by`-compiled body needs `unfold`+`dsimp` to expose the dite. -/
theorem memberSortP_extendEnv_ap {E : ResolvedEnv} {r₀ : Nat} {m₀ : CheckedMember}
    {u₀ : Level}
    (hm : MemberSortP E) (hfresh : E.members r₀ = none)
    (hT : TyP E m₀.arity [] m₀.mtype (.sort u₀))
    (hAm : hm.AssumpPref) (hAT : hT.AssumpPref) :
    (memberSortP_extendEnv hm hfresh hT).AssumpPref := by
  intro r m hres
  show ((memberSortP_extendEnv hm hfresh hT) r m hres).2.AssumpPref
  by_cases h : r = r₀
  · subst h
    have hmmeq : m₀ = m := Option.some.inj ((members_extend_self E r m₀).symm.trans hres)
    subst hmmeq
    show (memberSortP_extendEnv hm hfresh hT r m₀ (members_extend_self E r m₀)).2.AssumpPref
    unfold memberSortP_extendEnv
    simp only [dif_pos, if_pos, Nat.reduceEqDiff]
    rw [dif_pos rfl]
    exact hAT
  · have hresE : E.members r = some m := members_extend_ne E m₀ h ▸ hres
    show (memberSortP_extendEnv hm hfresh hT r m (members_extend_preserved hfresh r m hresE)).2.AssumpPref
    unfold memberSortP_extendEnv
    dsimp only
    rw [dif_neg h]
    exact hAm r m _

/-- **Pack step.** `memberSortP_of_envWfP`'s point value is `TyP.ewk … (typeAdm hres).hT`;
    the ewk arm of `TyP.AssumpPref` reduces this to the admission derivation's AP. -/
theorem memberSortP_of_envWfP_ap {E : ResolvedEnv} (hEP : EnvWfP E)
    (h : ∀ {r m} (hres : E.members r = some m), (hEP.typeAdm hres).hT.AssumpPref) :
    (memberSortP_of_envWfP hEP).AssumpPref :=
  fun _ _ hres => h hres

/-- **Decidable-cases lift.** `GroupMembersP.typeAdm`/`EnvWfP.typeAdm` build their
    fresh-vs-old split with `cases Nat.decEq`, which elaborates to `Decidable.casesOn`
    whose motive mentions the proof term `e = t` — so `rw`/`split` on the scrutinee all
    hit the dependent-motive wall. Abstracting the scrutinee to a bound variable `e`
    (with its `isFalse`/`isTrue` minors and the `e = e` witness) makes `cases e` fire,
    and the remaining `Eq.rec`/`noConfusion` transports inside each minor reduce by K
    once the queried index and member are substituted. -/
theorem decEq_casesOn_hT_ap {p : Prop} (e : Decidable p)
    {E₂ : ResolvedEnv} {W : Nat → Nat} {r : Nat} {m : CheckedMember}
    (f : ∀ h : ¬p, e = isFalse h → TypeAdm E₂ W r m)
    (g : ∀ h : p, e = isTrue h → TypeAdm E₂ W r m)
    (w : e = e)
    (hf : ∀ h w, (f h w).hT.AssumpPref) (hg : ∀ h w, (g h w).hT.AssumpPref) :
    ((Decidable.casesOn (motive := fun t => e = t → TypeAdm E₂ W r m) e f g) w).hT.AssumpPref := by
  cases e with
  | isFalse h => exact hf h w
  | isTrue h => exact hg h w

/-- **Group step.** For `g : GroupMembersT S E₁ ms E'`, every admission derivation that
    `(enrichGroupMembersT hw hm g).typeAdm` returns has an AP `hT`: `nil` defers to the
    `old` channel (members before the group), `cons` recurses — the rebuilt `old` channel
    discharges the fresh member by `assumpPref_enrichHasTyT` and old members by `hold`,
    while `memberSortP_extendEnv_ap` keeps `hm₂`'s AP alive for the next step. -/
theorem enrichGroupMembersT_typeAdm_ap {S : ResolvedEnv} :
    {E₁ : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    (hw : CvWalkHyp E₁) → {hm : MemberSortP E₁} → hm.AssumpPref →
    (g : GroupMembersT S E₁ ms E') →
    ∀ {Aw : Nat → Nat} {r : Nat} {m : CheckedMember}
      (h : E'.members r = some m)
      (old : E₁.members r = some m → TypeAdm E₁ Aw r m)
      (_hold : ∀ (h' : E₁.members r = some m), (old h').hT.AssumpPref),
      ((enrichGroupMembersT hw hm g).typeAdm Aw h old).hT.AssumpPref
  | _, _, _, _, _, _, .nil _, _, _, _, h, _, hold => hold h
  | _, _, _, hw, hm, hhm,
      .cons _ rf mf rest _ hfresh hnobody hclT _ hlvlB _ harities _ _ u hT _ _ hrest,
      Aw, rq, mq, h, old, hold => by
      have hTPap : (enrichHasTyT hw.closed (envExt_refl _) hm
          (letCtxConvP_of_cvWalkHyp hw (n := mf.arity)) (.nil _ mf.arity) hT).AssumpPref :=
        assumpPref_enrichHasTyT hw.closed (envExt_refl _) hhm (letCtxConvP_ap hw)
          (.nil _ mf.arity) hT trivial
      have hhm₂ := memberSortP_extendEnv_ap hm hfresh _ hhm hTPap
      refine enrichGroupMembersT_typeAdm_ap (cvWalkHyp_cons hw hfresh hnobody hclT hlvlB
        harities) hhm₂ hrest h _ ?_
      intro h'
      refine decEq_casesOn_hT_ap _ _ _ _ ?_ ?_
      · intro hne _
        exact hold _
      · intro heq _
        subst heq
        have hmmeq : mf = mq := Option.some.inj ((members_extend_self _ rq mf).symm.trans h')
        subst hmmeq
        exact hTPap

/-- **Environment step** — the recursive heart: every `typeAdm` output of the enriched
    environment satisfies `TyP.AssumpPref`. Each `EnvWfT` step ctor reuses
    `decEq_casesOn_hT_ap`: the `isFalse` (preserved-member) arm is the induction
    hypothesis through `TypeAdm.step`, the `isTrue` (fresh-member) arm is the enriched
    stored type whose AP is `assumpPref_enrichHasTyT` fed by the prefix IH +
    `letCtxConvP_ap`; `group` defers to `enrichGroupMembersT_typeAdm_ap`. -/
theorem enrichEnvWfT_typeAdm_ap :
    {E : ResolvedEnv} → (hEnv : EnvWfT E) →
    ∀ {r : Nat} {m : CheckedMember} (hres : E.members r = some m),
      ((enrichEnvWfT hEnv).typeAdm hres).hT.AssumpPref
  | _, .empty, _, _, hres => Option.noConfusion hres
  | _, .axiom E r' A u hE hfresh hA hcl hlvl, rq, mq, hres => by
      have hhmE : (memberSortP_of_envWfP (enrichEnvWfT hE)).AssumpPref :=
        memberSortP_of_envWfP_ap _ (fun h' => enrichEnvWfT_typeAdm_ap hE h')
      have hAP : (enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E)
          (memberSortP_of_envWfP (enrichEnvWfT hE)) (letCtxConvP_of_envWfT hE)
          (.nil E 0) hA).AssumpPref :=
        assumpPref_enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E) hhmE
          (letCtxConvP_ap (cvWalkHyp_of_envWfT hE)) (.nil E 0) hA trivial
      refine decEq_casesOn_hT_ap _ _ _ _ ?_ ?_
      · intro hne _
        exact enrichEnvWfT_typeAdm_ap hE _
      · intro heq _
        subst heq
        have hmmeq : ⟨.axiomM, 0, A, none⟩ = mq :=
          Option.some.inj ((members_extend_self _ rq ⟨.axiomM, 0, A, none⟩).symm.trans hres)
        subst hmmeq
        exact hAP
  | _, .definition E r' A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, rq, mq, hres => by
      have hhmE : (memberSortP_of_envWfP (enrichEnvWfT hE)).AssumpPref :=
        memberSortP_of_envWfP_ap _ (fun h' => enrichEnvWfT_typeAdm_ap hE h')
      have hAP : (enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E)
          (memberSortP_of_envWfP (enrichEnvWfT hE)) (letCtxConvP_of_envWfT hE)
          (.nil E 0) hA).AssumpPref :=
        assumpPref_enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E) hhmE
          (letCtxConvP_ap (cvWalkHyp_of_envWfT hE)) (.nil E 0) hA trivial
      refine decEq_casesOn_hT_ap _ _ _ _ ?_ ?_
      · intro hne _
        exact enrichEnvWfT_typeAdm_ap hE _
      · intro heq _
        subst heq
        have hmmeq : ⟨.definitionM, 0, A, some v⟩ = mq :=
          Option.some.inj ((members_extend_self _ rq ⟨.definitionM, 0, A, some v⟩).symm.trans hres)
        subst hmmeq
        exact hAP
  | _, .thm E r' A p hE hfresh hA hp hclA hclp hlvlA hlvlp, rq, mq, hres => by
      have hhmE : (memberSortP_of_envWfP (enrichEnvWfT hE)).AssumpPref :=
        memberSortP_of_envWfP_ap _ (fun h' => enrichEnvWfT_typeAdm_ap hE h')
      have hAP : (enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E)
          (memberSortP_of_envWfP (enrichEnvWfT hE)) (letCtxConvP_of_envWfT hE)
          (.nil E 0) hA).AssumpPref :=
        assumpPref_enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E) hhmE
          (letCtxConvP_ap (cvWalkHyp_of_envWfT hE)) (.nil E 0) hA trivial
      refine decEq_casesOn_hT_ap _ _ _ _ ?_ ?_
      · intro hne _
        exact enrichEnvWfT_typeAdm_ap hE _
      · intro heq _
        subst heq
        have hmmeq : ⟨.theoremM, 0, A, some p⟩ = mq :=
          Option.some.inj ((members_extend_self _ rq ⟨.theoremM, 0, A, some p⟩).symm.trans hres)
        subst hmmeq
        exact hAP
  | _, .opaque E r' A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, rq, mq, hres => by
      have hhmE : (memberSortP_of_envWfP (enrichEnvWfT hE)).AssumpPref :=
        memberSortP_of_envWfP_ap _ (fun h' => enrichEnvWfT_typeAdm_ap hE h')
      have hAP : (enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E)
          (memberSortP_of_envWfP (enrichEnvWfT hE)) (letCtxConvP_of_envWfT hE)
          (.nil E 0) hA).AssumpPref :=
        assumpPref_enrichHasTyT (envClosed_of_envWfT hE) (envExt_refl E) hhmE
          (letCtxConvP_ap (cvWalkHyp_of_envWfT hE)) (.nil E 0) hA trivial
      refine decEq_casesOn_hT_ap _ _ _ _ ?_ ?_
      · intro hne _
        exact enrichEnvWfT_typeAdm_ap hE _
      · intro heq _
        subst heq
        have hmmeq : ⟨.opaqueM, 0, A, some v⟩ = mq :=
          Option.some.inj ((members_extend_self _ rq ⟨.opaqueM, 0, A, some v⟩).symm.trans hres)
        subst hmmeq
        exact hAP
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, rq, mq, hres =>
      enrichGroupMembersT_typeAdm_ap (cvWalkHyp_of_envWfT hE)
        (memberSortP_of_envWfP_ap _ (fun h' => enrichEnvWfT_typeAdm_ap hE h'))
        hmem hres _ (fun h' => enrichEnvWfT_typeAdm_ap hE h')

/-- **L-MSAP discharged.** The `hMSAP` hypothesis of `RcicSynBelowCToRows` is a theorem:
    `MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv)`. -/
theorem memberSortP_of_envWfT_ap {E : ResolvedEnv} (hEnv : EnvWfT E) :
    MemberSortP.AssumpPref (memberSortP_of_envWfT hEnv) :=
  memberSortP_of_envWfP_ap (enrichEnvWfT hEnv)
    (fun hres => enrichEnvWfT_typeAdm_ap hEnv hres)

end Rcic.Syn
