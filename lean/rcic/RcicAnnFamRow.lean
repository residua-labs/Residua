import rcic.RcicAnnRecSem

/-!
# M2-f (5c)/(6b) — row (3) on the copy: convertible applications of one family

`FamAppConvInj` (main's `RcicInvertFamily`): convertible applications of one family have `=ₙ`
level lists and pointwise convertible arguments. On the copy the row comes out of the type
equality the way rows (1) and (2) do (`RcicAnnLRRows`): the fundamental theorem relates the two
applications as types, and at a Type-level family application in weak-head normal form the only
clause is `EqKA.fam`. That clause carries:

* the level lists `=ₙ` (`hls`);
* the parameters pointwise convertible along the family's type (`hpar`, M2-f (6): a conversion,
  not a relation, so no parameter domain is asked for at the clause's height — L-RING D2 keeps
  holding);
* the indices related along the family telescope at the LEFT parameters (`hxs`), each step valid
  (`hFldF`), so pointwise convertible by escape (`convArgsA_of_argsRelPA`).

So the row is whole (`famAppConvInjA`): both parts, along the instantiated family type. At the
concrete ι (`famAppConvInjA_rec`) it needs `EnvSemA` from the environment's well-formedness under
the small-index profile and `PropElimStructA` only (`PropElimOnlyA` before W-1 (e-2)): the recursors'
clause carries parameters since M2-f (6c), and struct groups since W-1 (c). At a `Prop`-level conversion (M2-g′, `famAppConvInjA_prop`) the relation at the sort
carries the two propositions' structure (`PropEqA.fam`): the same family, `=ₙ` level lists, the
arguments convertible along the family's type at every bounded `=ₙ` list, read at the left list. That
the conversion's sort IS `Prop`-level whenever the family is a `Prop` family — type uniqueness along
the family spine — is the premise there, and the row's remaining case (M2-g′ (e)).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) pointwise conversion along a telescope (`ConvArgsA`, `RcicAnnFam` (4b)) -/

section Row3
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a plain walk whose every step is valid — the pair is related by a relation that implies
    conversion at the reached domain — is a pointwise conversion along its telescope. -/
theorem convArgsA_of_argsRelPA {Γ : LCtxA} {R : Nat → List ExprA → ExprA → ExprA → Prop} :
    ∀ {i₀ : Nat} {prev₀ : List ExprA} {T₀ : ExprA} {fs fs' : List ExprA},
    ArgsRelPA R i₀ prev₀ T₀ fs fs' →
    (∀ (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      ArgsRelPA R i₀ prev₀ T₀ pre pre' → applyTelA pre T₀ = some (.pi D uD C vC) →
      ∀ g g', R (i₀ + pre.length) (prev₀ ++ pre) g g' → Nonempty (ConvA E I n Γ g g' D)) →
    ConvArgsA E I n Γ T₀ fs fs'
  | _, _, _, _, _, .nil _ _ T, _ => .nil T
  | _, _, _, _, _, .cons i prev A u B v f f' fs fs' h hs, hval => by
      refine .cons A u B v f f' fs fs' ?_ ?_
      · have h0 : R (i + ([] : List ExprA).length) (prev ++ []) f f' := by
          rw [List.length_nil, Nat.add_zero, List.append_nil]; exact h
        exact hval [] [] A u B v (.nil i prev _) rfl f f' h0
      · refine convArgsA_of_argsRelPA hs (fun pre pre' D uD C vC hw hT g g' hg => ?_)
        have hi : i + (f :: pre).length = i + 1 + pre.length := by
          rw [List.length_cons]; omega
        have hp : prev ++ f :: pre = prev ++ [f] ++ pre := by
          rw [List.append_assoc, List.singleton_append]
        refine hval (f :: pre) (f' :: pre') D uD C vC (.cons i prev A u B v f f' pre pre' h hw) hT g g' ?_
        rw [hi, hp]; exact hg

/-- THE TYPE EQUALITY AT A TYPE-LEVEL FAMILY APPLICATION, INVERTED. Both sides are weak-head
    normal (a family head is rigid and no recursor), so the only clause is `fam`. It gives the level
    lists `=ₙ`, the parameters pointwise convertible along the family's type (`hpar` at the trivial
    world), and the indices pointwise convertible along the family telescope at the left
    parameters. -/
theorem eqKA_famApp_inv (hR : IotaRecHeadA E I) {k : Nat} {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    {ls ls' : List Level} {xs xs' : List ExprA} {u₀ : Level}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hsh : piBodyA m.mtypeA = .sort u₀)
    (hz : isZero (instLevel ls u₀) = false)
    (h : LREqA E I n ρ₀ k Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs')) :
    eqNList ls ls' ∧ (xs.take m.nparamsA).length = m.nparamsA ∧ (xs'.take m.nparamsA).length = m.nparamsA ∧
      ConvArgsA E I n Γ (instantiateLevelsA ls m.mtypeA) (xs.take m.nparamsA) (xs'.take m.nparamsA) ∧
      ∀ TF, applyTelA (xs.take m.nparamsA) (instantiateLevelsA ls m.mtypeA) = some TF →
        ConvArgsA E I n Γ TF (xs.drop m.nparamsA) (xs'.drop m.nparamsA) := by
  have hrig : transparent m.mclass = false ∨ m.bodyA = none := Or.inl (by rw [hind]; rfl)
  have hnr : m.mclass ≠ .recursorM := by rw [hind]; exact fun h' => MemberClass.noConfusion h'
  have hnF := hStepFnA_constSpine_none hR hm hrig hnr Γ (ls := ls) (foldAppsA (.const r ls) xs)
    (by rw [foldAppsA_const_head])
  have hnF' := hStepFnA_constSpine_none hR hm hrig hnr Γ (ls := ls') (foldAppsA (.const r ls') xs')
    (by rw [foldAppsA_const_head])
  rw [LREqA_eq] at h
  cases h with
  | sort hA _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_sort E I.fn Γ _) hnF
      exact absurd e.symm (foldAppsA_const_ne_sort _ _ _ _)
  | pi hA _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA (whTyA_self hA) (hStepFnA_pi E I.fn Γ _ _ _ _) hnF
      exact absurd e.symm (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck hA _ hN _ _ =>
      have e := whTyA_det hA (whTyA_self hA) hN.1 hnF
      subst e
      have hP := (isPropTy_famApp_iff hm hsh ls xs).mp (tripleLikeA_famApp_isProp hm hind hN)
      rw [hP.2.2] at hz
      exact Bool.noConfusion hz
  | @fam _ _ _ r₀ ls₀ ls₀' ps ps' is is' m₀ _ hA hB hnA hnB hm' _ _ hls hps hps' _ RsF _ _ hFldF _ _ _ _ _ _ _ _
      hxs _ hpar =>
      have e := whTyA_det hA (whTyA_self hA) hnA hnF
      obtain ⟨er, el, exs⟩ := foldAppsA_const_inj e
      subst r₀
      subst ls₀
      subst xs
      have e' := whTyA_det hB (whTyA_self hB) hnB hnF'
      obtain ⟨_, el', exs'⟩ := foldAppsA_const_inj e'
      subst ls₀'
      subst xs'
      have em := hm.symm.trans hm'
      injection em with em
      subst m₀
      have hb : levelsBounded n ls = true := whTyA_famApp_bounded hA
      rw [List.take_left' hps, List.drop_left' hps, List.take_left' hps', List.drop_left' hps']
      have hP := hpar [] (wkOk₀A_nil E I n Γ) ls (eqNListB_refl hb)
      simp only [map_wkExprA_nil] at hP
      refine ⟨hls, hps, hps', parConvA_convArgsA hP, fun TF hTF => ?_⟩
      refine convArgsA_of_argsRelPA (hxs TF hTF) (fun pre pre' D uD C vC hw hT g g' hg => ?_)
      have hTF₀ : applyTelA (ps.map (wkExprA [])) (instantiateLevelsA ls m.mtypeA) = some TF := by
        rw [map_wkExprA_nil]; exact hTF
      have hw₀ : ArgsRelPA (RsF [] ls) m.nparamsA (ps.map (wkExprA [])) TF pre pre' := by
        rw [map_wkExprA_nil]; exact hw
      have hty := hFldF [] (wkOk₀A_nil E I n Γ) ls TF pre pre' D uD C vC (eqNListB_refl hb) hTF₀ hw₀ hT
      rw [map_wkExprA_nil] at hty
      have hLR : LRTyA E I n ρ₀ k Γ D (RsF [] ls (m.nparamsA + pre.length) (ps ++ pre)) := by
        rw [LRTyA_eq]; exact hty
      exact escape_LRTyA hLR hg

/-- ROW (3) — `FamAppConvInj` at a Type-level family application: convertible applications of one
    family have `=ₙ` level lists and pointwise convertible arguments along the instantiated family
    type — the parameters by the clause's `hpar`, the indices by its walk. -/
theorem famAppConvInjA (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List ExprA} {u₀ w : Level}
    (hΓ : CtxWfA E I n Γ) (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hsh : piBodyA m.mtypeA = .sort u₀) (hz : isZero (instLevel ls u₀) = false)
    (h : ConvA E I n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsA E I n Γ (instantiateLevelsA ls m.mtypeA) xs xs' := by
  obtain ⟨k₀, hk⟩ := fund_tyEq hE hI hIS hEN hNC hR hS hρ hΓ h
  obtain ⟨hls, _, _, hP, hI'⟩ := eqKA_famApp_inv hR hm hind hsh hz (hk k₀ (Nat.le_refl _))
  obtain ⟨TF, hTF⟩ := convArgsA_applyTel hP
  have hc := convArgsA_append hP hTF (hI' TF hTF)
  rw [List.take_append_drop, List.take_append_drop] at hc
  exact ⟨hls, convArgsA_length hc, hc⟩

/-- ROW (3) AT A `Prop`-LEVEL CONVERSION (M2-g′): convertible applications of one family, the
    conversion at a `Prop`-level sort, have `=ₙ` level lists and pointwise convertible arguments
    along the instantiated family type. The relation at the sort carries the two propositions'
    STRUCTURE (`PropEqA`); both sides are weak-head normal, so it is the `fam` clause's, inverted at
    the application (`propEqA_famApp_inv`) and read at the left list itself. At a `Prop` family the
    conversion's sort is `Prop`-level for every typing of a full application — type uniqueness along
    the spine, which is the premise `hw` here (M2-g′ (e)). -/
theorem famAppConvInjA_prop (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hR : IotaRecHeadA E I) (hS : EnvSemA E I n ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {r : Nat} {m : CheckedMemberA} {ls ls' : List Level} {xs xs' : List ExprA} {w : Level}
    (hΓ : CtxWfA E I n Γ) (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hw : isZero w = true)
    (h : ConvA E I n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsA E I n Γ (instantiateLevelsA ls m.mtypeA) xs xs' := by
  obtain ⟨k₀, hk⟩ := fund_conv hE hI hIS hEN hNC hR hS hρ hΓ h
  obtain ⟨_, _, ⟨ht⟩, _, _, hP⟩ := LRRelA_sortP_elim hw (hk k₀ (Nat.le_refl _))
  have hrig : transparent m.mclass = false ∨ m.bodyA = none := Or.inl (by rw [hind]; rfl)
  have hnr : m.mclass ≠ .recursorM := by rw [hind]; exact fun h' => MemberClass.noConfusion h'
  have hnF := hStepFnA_constSpine_none hR hm hrig hnr Γ (ls := ls) (foldAppsA (.const r ls) xs)
    (by rw [foldAppsA_const_head])
  have hnF' := hStepFnA_constSpine_none hR hm hrig hnr Γ (ls := ls') (foldAppsA (.const r ls') xs')
    (by rw [foldAppsA_const_head])
  obtain ⟨_, hls, hargs⟩ := propEqA_famApp_inv hm hind hnF hnF' hP
  have hb : levelsBounded n ls = true := whTyA_famApp_bounded (whTyA_of_hasTy ht)
  have hc := parConvA_convArgsA (hargs ls (eqNListB_refl hb))
  exact ⟨hls, convArgsA_length hc, hc⟩

end Row3

section Row3Rec
variable {E : ResolvedEnvA} {n : Nat} {ρ₀ : Nat → Nat}

/-- ROW (3) at the concrete ι, under the profile: `famAppConvInjA` with `EnvSemA` from the
    environment's well-formedness (`envSemA_of_envWfA_rec`, parameters allowed since M2-f (6c)). -/
theorem famAppConvInjA_rec (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀) (hS : SmallIndexProfileA E)
    (hPE : PropElimStructA E) {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    {ls ls' : List Level} {xs xs' : List ExprA} {u₀ w : Level}
    (hΓ : CtxWfA E (iotaIfaceA E) n Γ) (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hsh : piBodyA m.mtypeA = .sort u₀) (hz : isZero (instLevel ls u₀) = false)
    (h : ConvA E (iotaIfaceA E) n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA ls m.mtypeA) xs xs' :=
  famAppConvInjA (envWfA_closed hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW))
    (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW)) (envWfA_normCtorType hW) (envWfA_normClosed hW)
    (iotaFnA_recHead E) (envSemA_of_envWfA_recStruct hW hρ hS hPE) hρ
    hΓ hm hind hsh hz h

/-- ROW (3) at a `Prop`-level conversion, at the concrete ι, under the profile (M2-g′). -/
theorem famAppConvInjA_prop_rec (hW : EnvWfA (iotaIfaceA E) E) (hρ : PosValA ρ₀)
    (hS : SmallIndexProfileA E) (hPE : PropElimStructA E) {Γ : LCtxA} {r : Nat} {m : CheckedMemberA}
    {ls ls' : List Level} {xs xs' : List ExprA} {w : Level}
    (hΓ : CtxWfA E (iotaIfaceA E) n Γ) (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hw : isZero w = true)
    (h : ConvA E (iotaIfaceA E) n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs') (.sort w)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsA E (iotaIfaceA E) n Γ (instantiateLevelsA ls m.mtypeA) xs xs' :=
  famAppConvInjA_prop (envWfA_closed hW) (iotaFnA_lift (envWfA_closed hW) (envWfA_normClosed hW))
    (iotaFnA_subst (envWfA_closed hW) (envWfA_normClosed hW)) (envWfA_normCtorType hW) (envWfA_normClosed hW)
    (iotaFnA_recHead E) (envSemA_of_envWfA_recStruct hW hρ hS hPE) hρ
    hΓ hm hind hw h

end Row3Rec

#print axioms convArgsA_of_argsRelPA
#print axioms eqKA_famApp_inv
#print axioms famAppConvInjA
#print axioms famAppConvInjA_rec
#print axioms famAppConvInjA_prop
#print axioms famAppConvInjA_prop_rec

end Rcic.Declarative.Ann
