import rcic.RcicAnnAnnotate
import rcic.RcicTypedJD
import rcic.RcicAnnIotaSR

/-!
# R-NoDeltaRec-4d-iv — annotation of the D-judgment (`annConvTD`)

`annConvT` (`RcicAnnAnnotate`) annotates `ConvT (eraseEnv E)` conversions back to the copy.
Its single `EnvNormEraseA` read is the `.iota` arm: `iotaFnA_of_derivedIota` asks that a
STORED-type derived ι of the erased environment be a step of the copy's ι — which needs the
stored and normalized constructor types to erase equally, false at a `.drecD` member
(`drCtorMemberA_diverge`).

This module ports the same three lifts to the D-judgment (`RcicTypedJD`): `ConvTD`/`HasTyTD`/
`CtxWfTD` carry `EA.members`-hits of annotated members directly (no `members_of_eraseEnv`)
and `DerivedIotaN` ι steps, whose annotation `iotaFnA_of_derivedIotaN` (`RcicAnnIotaCorrN`)
needs only `EnvWfA`. The `EnvNormEraseA` premise is gone, not assumed: the remaining premise
is ι subject reduction (`IotaSRA`), the same named hypothesis `annConvT` carries, and it is
discharged by `RcicAnnIotaSR`'s `iotaSRA` at the `'` variants.

(0) `annHasTyTD`/`annConvTD`: the mutual annotation lifts at the D-judgment.
(1) `annCtxWfTD`: the context lift.
(2) the `'` variants, `IotaSRA` discharged (`iotaSRA`, `RcicAnnIotaSR`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section AnnotateD
variable {E : ResolvedEnvA} {n : Nat}

mutual

/-- ANNOTATION OF TYPING at the D-judgment: a `HasTyTD` typing lifts, in any well-formed
    annotated context erasing to its context, to a typing on the copy of an annotation of its
    subject at an annotation of its type. `annHasTyT`'s twin — every arm identical but the
    member reads (already annotated) and ι (the normalized correspondence). No
    `EnvNormEraseA`. -/
theorem annHasTyTD (C : AnnEnvA E) (hSR : IotaSRA E n) :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyTD E n Γ e T →
    ∀ {ΓA : LCtxA}, CtxWfA E (iotaIfaceA E) n ΓA → eraseCtx ΓA = Γ →
      ∃ eA TA, erase eA = e ∧ erase TA = T ∧ Nonempty (HasTyA E (iotaIfaceA E) n ΓA eA TA)
  | _, _, _, .sort _ l, ΓA, _, _ => ⟨.sort l, .sort (.succ l), rfl, rfl, ⟨.sort ΓA l⟩⟩
  | _, _, _, .bvar _ i _ h, ΓA, hΓ, hctx => by
      subst hctx
      obtain ⟨AA, hAA, rfl⟩ := lookupTypeA_of_erase h
      obtain ⟨u, ⟨hu⟩⟩ := ctxWfA_lookupType_ty C hΓ hAA
      exact ⟨.bvar i, AA, rfl, rfl, ⟨.bvar ΓA i AA u hAA hu⟩⟩
  | _, _, _, .const _ r ls m hres hlen hwf, ΓA, _, _ => by
      obtain ⟨u, ⟨hT⟩⟩ := hasTyA_memberTy_inst C hres hlen hwf ΓA
      exact ⟨.const r ls, instantiateLevelsA ls m.mtypeA, rfl, erase_instantiateLevelsA _ _,
        ⟨.const ΓA r ls m u hres hlen hwf hT⟩⟩
  | _, _, _, .pi _ _ u _ v hA hB, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyTD C hSR hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨BA, SB, hBe, hSBe, ⟨tB⟩⟩ :=
        annHasTyTD C hSR hB (.assumption hΓ tA) (eraseCtx_assumption hAe hctx)
      obtain rfl := erase_eq_sort hSBe
      subst hAe hBe hctx
      exact ⟨.pi AA u BA v, .sort (.imax u v), rfl, rfl, ⟨.pi ΓA AA u BA v tA tB⟩⟩
  | _, _, _, .lam _ _ u _ _ hA hbody, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyTD C hSR hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.assumption AA :: ΓA) := .assumption hΓ tA
      obtain ⟨bA, BA, hbe, hBe, ⟨tb⟩⟩ := annHasTyTD C hSR hbody hΓ' (eraseCtx_assumption hAe hctx)
      subst hAe hbe hBe hctx
      obtain ⟨v, tB⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ' tb
      exact ⟨.lam AA u bA, .pi AA u BA v, rfl, rfl, ⟨.lam ΓA AA u bA BA v tA tB tb⟩⟩
  | _, _, _, .app _ _ _ _ _ hf ha, ΓA, hΓ, hctx => by
      obtain ⟨fA, TfA, hfe, hTf, ⟨tf⟩⟩ := annHasTyTD C hSR hf hΓ hctx
      obtain ⟨aA, TaA, hae, hTa, ⟨ta⟩⟩ := annHasTyTD C hSR ha hΓ hctx
      subst hfe hae hctx
      obtain ⟨AA, u, BA, v, rfl, hAe, rfl⟩ := erase_eq_pi hTf
      obtain ⟨_, ts⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ tf
      obtain ⟨hAu, hBv⟩ := hasTyA_pi_parts ts
      obtain ⟨ta'⟩ := hasTyA_reannot C hΓ ta (hTa.trans hAe.symm) hAu
      have hTy : HasTyA E (iotaIfaceA E) n ΓA (instantiate0A aA BA) (.sort v) :=
        hasTyA_inst0' C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hBv ta'
      exact ⟨.app fA aA, instantiate0A aA BA, rfl, erase_instantiate0A _ _,
        ⟨.app ΓA fA aA AA BA u v v hBv hTy tf ta'⟩⟩
  | _, _, _, .letE _ _ u _ _ _ hA hv hb, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyTD C hSR hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨vA, TvA, hve, hTv, ⟨tv⟩⟩ := annHasTyTD C hSR hv hΓ hctx
      obtain ⟨tv'⟩ := hasTyA_reannot C hΓ tv (hTv.trans hAe.symm) tA
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.letBinding AA vA :: ΓA) := .letBinding hΓ tA tv'
      obtain ⟨bA, BA, hbe, hBe, ⟨tb⟩⟩ :=
        annHasTyTD C hSR hb hΓ' (eraseCtx_letBinding hAe hve hctx)
      subst hAe hve hbe hBe hctx
      obtain ⟨w, tBw⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ' tb
      have hTy : HasTyA E (iotaIfaceA E) n ΓA (instantiate0A vA BA) (.sort w) :=
        hasTyA_inst0Let C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ tBw tv'
      exact ⟨.letE AA vA bA, instantiate0A vA BA, rfl, erase_instantiate0A _ _,
        ⟨.letE ΓA AA u w vA BA bA tA tv' hTy tb⟩⟩
  | _, _, _, .lit _ t _ hexp, ΓA, hΓ, hctx => by
      obtain ⟨eA, TA, he, hTe, ⟨te⟩⟩ := annHasTyTD C hSR hexp hΓ hctx
      subst hTe
      obtain rfl := erase_eq_natExpand t he
      exact ⟨.lit t, TA, rfl, rfl, ⟨.lit ΓA t TA te⟩⟩
  | _, _, _, .conv _ _ _ _ _ h hc, ΓA, hΓ, hctx => by
      obtain ⟨eA, TeA, hee, hTe, ⟨te⟩⟩ := annHasTyTD C hSR h hΓ hctx
      obtain ⟨AA, BA, SA, hAe, hBe, hSe, ⟨c⟩⟩ := annConvTD C hSR hc hΓ hctx
      subst hee hBe hctx
      obtain rfl := erase_eq_sort hSe
      have tAA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ c
      obtain ⟨te'⟩ := hasTyA_reannot C hΓ te (hTe.trans hAe.symm) tAA
      exact ⟨eA, BA, rfl, rfl, ⟨hasTyA_of_tyConvA te' (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ c)⟩⟩

/-- ANNOTATION OF CONVERSION at the D-judgment. `annConvT`'s twin; the `.iota` arm calls
    `iotaFnA_of_derivedIotaN`, which needs `EnvWfA` only — `EnvNormEraseA` is gone. -/
theorem annConvTD (C : AnnEnvA E) (hSR : IotaSRA E n) :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvTD E n Γ a b T →
    ∀ {ΓA : LCtxA}, CtxWfA E (iotaIfaceA E) n ΓA → eraseCtx ΓA = Γ →
      ∃ aA bA TA, erase aA = a ∧ erase bA = b ∧ erase TA = T ∧
        Nonempty (ConvA E (iotaIfaceA E) n ΓA aA bA TA)
  | _, _, _, _, .refl _ _ _ h, ΓA, hΓ, hctx => by
      obtain ⟨aA, TA, hae, hTe, ⟨ta⟩⟩ := annHasTyTD C hSR h hΓ hctx
      exact ⟨aA, aA, TA, hae, hae, hTe, ⟨.refl ΓA aA TA ta⟩⟩
  | _, _, _, _, .symm _ _ _ _ h, ΓA, hΓ, hctx => by
      obtain ⟨aA, bA, TA, hae, hbe, hTe, ⟨c⟩⟩ := annConvTD C hSR h hΓ hctx
      exact ⟨bA, aA, TA, hbe, hae, hTe, ⟨.symm ΓA aA bA TA c⟩⟩
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, ΓA, hΓ, hctx => by
      obtain ⟨aA, bA, TA, hae, hbe, hTe, ⟨c1⟩⟩ := annConvTD C hSR h1 hΓ hctx
      obtain ⟨bA', cA, TA', hb', hce, hT', ⟨c2⟩⟩ := annConvTD C hSR h2 hΓ hctx
      have tb := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ c1
      have tb' := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ c2
      obtain ⟨cbb⟩ := annCohA C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one bA hΓ
        (hbe.trans hb'.symm) tb tb'
      obtain ⟨_, ts⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ tb
      obtain ⟨c2'⟩ := convA_reannot C hΓ c2 (hT'.trans hTe.symm) ts
      exact ⟨aA, cA, TA, hae, hce, hTe, ⟨.trans ΓA aA bA cA TA c1 (.trans ΓA bA bA' cA TA cbb c2')⟩⟩
  | _, _, _, _, .beta _ _ _ _ _ u hA hbody harg, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyTD C hSR hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.assumption AA :: ΓA) := .assumption hΓ tA
      obtain ⟨bA, BA, hbe, hBe, ⟨tb⟩⟩ := annHasTyTD C hSR hbody hΓ' (eraseCtx_assumption hAe hctx)
      obtain ⟨xA, TxA, hxe, hTx, ⟨tx⟩⟩ := annHasTyTD C hSR harg hΓ hctx
      subst hAe hbe hBe hxe hctx
      obtain ⟨tx'⟩ := hasTyA_reannot C hΓ tx hTx tA
      have hred := hasTyA_inst0' C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ tb tx'
      exact ⟨.app (.lam AA u bA) xA, instantiate0A xA bA, instantiate0A xA BA, rfl,
        erase_instantiate0A _ _, erase_instantiate0A _ _, ⟨.beta ΓA AA u bA xA BA tA tb tx' hred⟩⟩
  | _, _, _, _, .zeta _ _ _ _ _ u hA hv hb, ΓA, hΓ, hctx => by
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyTD C hSR hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨vA, TvA, hve, hTv, ⟨tv⟩⟩ := annHasTyTD C hSR hv hΓ hctx
      obtain ⟨tv'⟩ := hasTyA_reannot C hΓ tv (hTv.trans hAe.symm) tA
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.letBinding AA vA :: ΓA) := .letBinding hΓ tA tv'
      obtain ⟨bA, BA, hbe, hBe, ⟨tb⟩⟩ :=
        annHasTyTD C hSR hb hΓ' (eraseCtx_letBinding hAe hve hctx)
      subst hAe hve hbe hBe hctx
      have hred := hasTyA_inst0Let C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ tb tv'
      exact ⟨.letE AA vA bA, instantiate0A vA bA, instantiate0A vA BA, rfl,
        erase_instantiate0A _ _, erase_instantiate0A _ _, ⟨.zeta ΓA AA vA bA BA u tA tv' tb hred⟩⟩
  | _, _, _, _, .zetaLocal _ i _ _ hval hty _, ΓA, hΓ, hctx => by
      subst hctx
      obtain ⟨vA, hvA, rfl⟩ := lookupValueA_of_erase hval
      obtain ⟨AA, hAA, rfl⟩ := lookupTypeA_of_erase hty
      obtain ⟨tv⟩ := ctxWfA_lookupValue_ty C hΓ hAA hvA
      exact ⟨.bvar i, vA, AA, rfl, rfl, rfl, ⟨.zetaLocal ΓA i AA vA hvA hAA tv⟩⟩
  | _, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf _, ΓA, _, _ => by
      obtain ⟨tb⟩ := hasTyA_memberBody_inst C hres hbody hlen hwf ΓA
      exact ⟨.const r ls, instantiateLevelsA ls b, instantiateLevelsA ls m.mtypeA, rfl,
        erase_instantiateLevelsA _ _, erase_instantiateLevelsA _ _,
        ⟨.delta ΓA r ls m b hres hbody htr hlen hwf tb⟩⟩
  | _, _, _, _, .iota _ _ _ _ h hlhs _, ΓA, hΓ, hctx => by
      obtain ⟨lA, TA, hle, hTe, ⟨tl⟩⟩ := annHasTyTD C hSR hlhs hΓ hctx
      subst hle
      obtain ⟨hW⟩ := C.wf
      obtain ⟨rA, hfn, rfl⟩ := iotaFnA_of_derivedIotaN hW h
      exact ⟨lA, rA, TA, rfl, rfl, hTe, hSR hΓ hfn tl⟩
  | _, _, _, _, .lit _ t _ _ h hexp, ΓA, hΓ, hctx => by
      obtain ⟨eA, TA, he, hTe, ⟨te⟩⟩ := annHasTyTD C hSR hexp hΓ hctx
      cases h
      obtain rfl := erase_eq_natExpand t he
      exact ⟨.lit t, natExpandA t, TA, rfl, erase_natExpandA t, hTe, ⟨.lit ΓA t TA te⟩⟩
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, ΓA, hΓ, hctx => by
      obtain ⟨fA, gA, TfA, hfe, hge, hTf, ⟨c1⟩⟩ := annConvTD C hSR h1 hΓ hctx
      obtain ⟨aA, bA, TaA, hae, hbe, hTa, ⟨c2⟩⟩ := annConvTD C hSR h2 hΓ hctx
      subst hfe hge hae hbe hctx
      obtain ⟨AA, u, BA, v, rfl, hAe, rfl⟩ := erase_eq_pi hTf
      have tf := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ c1
      obtain ⟨_, ts⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ tf
      obtain ⟨hAu, hBv⟩ := hasTyA_pi_parts ts
      obtain ⟨c2'⟩ := convA_reannot C hΓ c2 (hTa.trans hAe.symm) hAu
      have tg := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ c1
      have tb := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ c2'
      have hBb : HasTyA E (iotaIfaceA E) n ΓA (instantiate0A bA BA) (.sort v) :=
        hasTyA_inst0' C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hBv tb
      have happ : HasTyA E (iotaIfaceA E) n ΓA (.app gA bA) (instantiate0A bA BA) :=
        .app ΓA gA bA AA BA u v v hBv hBb tg tb
      have cB : ConvA E (iotaIfaceA E) n ΓA (instantiate0A bA BA) (instantiate0A aA BA) (.sort v) :=
        hasTyA_func0 C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ hBv (.symm _ _ _ _ c2') hAu
      have hrt := hasTyA_of_tyConvA happ (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cB)
      exact ⟨.app fA aA, .app gA bA, instantiate0A aA BA, rfl, rfl, erase_instantiate0A _ _,
        ⟨.app ΓA fA gA aA bA AA BA u v c1 c2' hBv hrt⟩⟩
  | _, _, _, _, .lam _ _ _ _ _ _ u hA hb, ΓA, hΓ, hctx => by
      obtain ⟨AA, AA', SA, hAe, hA'e, hSe, ⟨cA⟩⟩ := annConvTD C hSR hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cA
      have tA' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ cA
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.assumption AA :: ΓA) := .assumption hΓ tA
      obtain ⟨bA, bA', BA, hbe, hb'e, hBe, ⟨cb⟩⟩ :=
        annConvTD C hSR hb hΓ' (eraseCtx_assumption hAe hctx)
      subst hAe hA'e hbe hb'e hBe hctx
      have tb' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ' cb
      obtain ⟨v, tB⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ'
        (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ' cb)
      have K : CtxConvA E (iotaIfaceA E) n (.assumption AA :: ΓA) (.assumption AA' :: ΓA) :=
        .assumption (ctxConvA_refl ΓA) ⟨tA⟩ ⟨tA'⟩ ⟨cA⟩
      have hRT := iotaRecHeadTypedA_of C.hR
      obtain ⟨tb''⟩ := hasTyA_ctxConv C.hE C.hI hRT K tb'
      obtain ⟨tB'⟩ := hasTyA_ctxConv C.hE C.hI hRT K tB
      have hlam : HasTyA E (iotaIfaceA E) n ΓA (.lam AA' u bA') (.pi AA' u BA v) :=
        .lam ΓA AA' u bA' BA v tA' tB' tb''
      have cpi : ConvA E (iotaIfaceA E) n ΓA (.pi AA' u BA v) (.pi AA u BA v) (.sort (.imax u v)) :=
        .pi ΓA AA' AA BA BA u u v v (eqNA_refl u) (eqNA_refl v) (.symm _ _ _ _ cA)
          (.refl _ _ _ tB') (.pi ΓA AA u BA v tA tB)
      have hrt := hasTyA_of_tyConvA hlam (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cpi)
      exact ⟨.lam AA u bA, .lam AA' u bA', .pi AA u BA v, rfl, rfl, rfl,
        ⟨.lam ΓA AA AA' bA bA' BA u u v (eqNA_refl u) cA cb hrt⟩⟩
  | _, _, _, _, .pi _ _ _ _ _ u v hA hB, ΓA, hΓ, hctx => by
      obtain ⟨AA, AA', SA, hAe, hA'e, hSe, ⟨cA⟩⟩ := annConvTD C hSR hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cA
      have tA' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ cA
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.assumption AA :: ΓA) := .assumption hΓ tA
      obtain ⟨BA, BA', SB, hBe, hB'e, hSBe, ⟨cB⟩⟩ :=
        annConvTD C hSR hB hΓ' (eraseCtx_assumption hAe hctx)
      obtain rfl := erase_eq_sort hSBe
      subst hAe hA'e hBe hB'e hctx
      have tB' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ' cB
      have K : CtxConvA E (iotaIfaceA E) n (.assumption AA :: ΓA) (.assumption AA' :: ΓA) :=
        .assumption (ctxConvA_refl ΓA) ⟨tA⟩ ⟨tA'⟩ ⟨cA⟩
      obtain ⟨tB''⟩ := hasTyA_ctxConv C.hE C.hI (iotaRecHeadTypedA_of C.hR) K tB'
      have hrt : HasTyA E (iotaIfaceA E) n ΓA (.pi AA' u BA' v) (.sort (.imax u v)) :=
        .pi ΓA AA' u BA' v tA' tB''
      exact ⟨.pi AA u BA v, .pi AA' u BA' v, .sort (.imax u v), rfl, rfl, rfl,
        ⟨.pi ΓA AA AA' BA BA' u u v v (eqNA_refl u) (eqNA_refl v) cA cB hrt⟩⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ u hA hv hb, ΓA, hΓ, hctx => by
      obtain ⟨AA, AA', SA, hAe, hA'e, hSe, ⟨cA⟩⟩ := annConvTD C hSR hA hΓ hctx
      obtain rfl := erase_eq_sort hSe
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cA
      have tA' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ cA
      obtain ⟨vA, vA', TvA, hve, hv'e, hTv, ⟨cv⟩⟩ := annConvTD C hSR hv hΓ hctx
      obtain ⟨cv'⟩ := convA_reannot C hΓ cv (hTv.trans hAe.symm) tA
      have tv := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cv'
      have tv' := convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ cv'
      have tv'A' := hasTyA_of_tyConvA tv' (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cA)
      have hΓ' : CtxWfA E (iotaIfaceA E) n (.letBinding AA vA :: ΓA) := .letBinding hΓ tA tv
      obtain ⟨bA, bA', BA, hbe, hb'e, hBe, ⟨cb⟩⟩ :=
        annConvTD C hSR hb hΓ' (eraseCtx_letBinding hAe hve hctx)
      subst hAe hA'e hve hv'e hbe hb'e hBe hctx
      have hRT := iotaRecHeadTypedA_of C.hR
      have K' : CtxConvA E (iotaIfaceA E) n (.letBinding AA vA :: ΓA) (.letBinding AA' vA' :: ΓA) :=
        .letBinding (ctxConvA_refl ΓA) ⟨tA⟩ ⟨tA'⟩ ⟨cA⟩ ⟨tv'A'⟩ ⟨cv'⟩
      obtain ⟨tb''⟩ := hasTyA_ctxConv C.hE C.hI hRT K' (convA_hasTy_right C.hE C.hI C.hR C.hIS hΓ' cb)
      obtain ⟨s, tBs⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ'
        (convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ' cb)
      obtain ⟨tBs'⟩ := hasTyA_ctxConv C.hE C.hI hRT K' tBs
      have hlet : HasTyA E (iotaIfaceA E) n ΓA (.letE AA' vA' bA') (instantiate0A vA' BA) :=
        .letE ΓA AA' u s vA' BA bA' tA' tv'A' (hasTyA_inst0Let C.hE C.hI (iotaRecHeadTypedA_of C.hR) C.hIS hΓ tBs' tv'A') tb''
      have cBv : ConvA E (iotaIfaceA E) n ΓA (instantiate0A vA' BA) (instantiate0A vA BA) (.sort s) :=
        convA_inst0Let_func C.hE C.hI C.hR C.hIS hΓ tBs tv' (.symm _ _ _ _ cv') tv (.refl ΓA vA AA tv)
          (.symm _ _ _ _ cv')
      have hrt := hasTyA_of_tyConvA hlet (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cBv)
      exact ⟨.letE AA vA bA, .letE AA' vA' bA', instantiate0A vA BA, rfl, rfl, erase_instantiate0A _ _,
        ⟨.letE ΓA AA AA' vA vA' bA bA' BA u cA cv' cb hrt⟩⟩
  | _, _, _, _, .sorts _ l₁ l₂ h, ΓA, _, _ =>
      ⟨.sort l₁, .sort l₂, .sort (.succ l₁), rfl, rfl, rfl, ⟨.sorts ΓA l₁ l₂ h⟩⟩
  | _, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h, ΓA, hΓ, _ => by
      have hlen' : ls'.length = m.arity := (eqNList_length ls ls' h).symm.trans hlen
      obtain ⟨u', ⟨tT'⟩⟩ := hasTyA_memberTy_inst C hres hlen' hwf' ΓA
      have hc' : HasTyA E (iotaIfaceA E) n ΓA (.const r ls') (instantiateLevelsA ls' m.mtypeA) :=
        .const ΓA r ls' m u' hres hlen' hwf' tT'
      obtain ⟨_, ⟨cT⟩⟩ := convA_memberTy_levels C hres hlen hlen' hwf hwf' h ΓA
      have hrt := hasTyA_of_tyConvA hc' (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ (.symm _ _ _ _ cT))
      exact ⟨.const r ls, .const r ls', instantiateLevelsA ls m.mtypeA, rfl, rfl,
        erase_instantiateLevelsA _ _, ⟨.consts ΓA r ls ls' m hres hlen hwf hwf' h hrt⟩⟩
  | _, _, _, _, .eta _ _ _ _ h, ΓA, hΓ, hctx => by
      obtain ⟨fA, TfA, hfe, hTf, ⟨tf⟩⟩ := annHasTyTD C hSR h hΓ hctx
      subst hfe hctx
      obtain ⟨AA, u, BA, v, rfl, rfl, rfl⟩ := erase_eq_pi hTf
      obtain ⟨_, ts⟩ := hasTyA_regular C.hE C.hI C.hR C.hIS hΓ tf
      obtain ⟨hAu, hBv⟩ := hasTyA_pi_parts ts
      have hbody := hasTyA_eta_body C.hE C.hI hAu hBv tf
      have hrt : HasTyA E (iotaIfaceA E) n ΓA (.lam AA u (.app (liftA 0 1 fA) (.bvar 0)))
          (.pi AA u BA v) := .lam ΓA AA u _ BA v hAu hBv hbody
      refine ⟨.lam AA u (.app (liftA 0 1 fA) (.bvar 0)), fA, .pi AA u BA v, ?_, rfl, rfl,
        ⟨.eta ΓA fA AA BA u v tf hrt⟩⟩
      show Expr.lam (erase AA) (.app (erase (liftA 0 1 fA)) (.bvar 0)) = _
      rw [erase_liftA]
  | _, _, _, _, .irr _ _ _ _ hP hp hq, ΓA, hΓ, hctx => by
      obtain ⟨PA, SP, hPe, hSe, ⟨tP⟩⟩ := annHasTyTD C hSR hP hΓ hctx
      obtain ⟨pA, TpA, hpe, hTp, ⟨tp⟩⟩ := annHasTyTD C hSR hp hΓ hctx
      obtain ⟨qA, TqA, hqe, hTq, ⟨tq⟩⟩ := annHasTyTD C hSR hq hΓ hctx
      subst hpe hqe hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨tp'⟩ := hasTyA_reannot C hΓ tp (hTp.trans hPe.symm) tP
      obtain ⟨tq'⟩ := hasTyA_reannot C hΓ tq (hTq.trans hPe.symm) tP
      exact ⟨pA, qA, PA, rfl, rfl, hPe, ⟨.irr ΓA PA pA qA tP tp' tq'⟩⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, ΓA, hΓ, hctx => by
      obtain ⟨aA, bA, TA, hae, hbe, hTe, ⟨c⟩⟩ := annConvTD C hSR h hΓ hctx
      obtain ⟨AA, AA', SA, hAe, hA'e, hSe, ⟨cA⟩⟩ := annConvTD C hSR hA hΓ hctx
      subst hae hbe hA'e hctx
      obtain rfl := erase_eq_sort hSe
      have tA := convA_hasTy_left C.hE C.hI C.hR C.hIS hΓ cA
      obtain ⟨c'⟩ := convA_reannot C hΓ c (hTe.trans hAe.symm) tA
      exact ⟨aA, bA, AA', rfl, rfl, rfl,
        ⟨convA_of_tyConvA c' (tyConvA_ofConv C.hE C.hI C.hR C.hIS hΓ cA)⟩⟩

end

/-- a well-formed typed context at the D-judgment has a well-formed annotation
    (`annCtxWfT`'s twin). -/
theorem annCtxWfTD (C : AnnEnvA E) (hSR : IotaSRA E n) :
    {Γ : LCtx} → CtxWfTD E n Γ →
      ∃ ΓA, eraseCtx ΓA = Γ ∧ Nonempty (CtxWfA E (iotaIfaceA E) n ΓA)
  | _, .nil => ⟨[], rfl, ⟨.nil⟩⟩
  | _, .assumption _ _ _ hΓ hA => by
      obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD C hSR hΓ
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyTD C hSR hA hΓA hctx
      obtain rfl := erase_eq_sort hSe
      exact ⟨.assumption AA :: ΓA, eraseCtx_assumption hAe hctx, ⟨.assumption hΓA tA⟩⟩
  | _, .letBinding _ _ _ _ hΓ hA hv => by
      obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfTD C hSR hΓ
      obtain ⟨AA, SA, hAe, hSe, ⟨tA⟩⟩ := annHasTyTD C hSR hA hΓA hctx
      obtain rfl := erase_eq_sort hSe
      obtain ⟨vA, TvA, hve, hTv, ⟨tv⟩⟩ := annHasTyTD C hSR hv hΓA hctx
      obtain ⟨tv'⟩ := hasTyA_reannot C hΓA tv (hTv.trans hAe.symm) tA
      exact ⟨.letBinding AA vA :: ΓA, eraseCtx_letBinding hAe hve hctx, ⟨.letBinding hΓA tA tv'⟩⟩

end AnnotateD

/-! ## (2) `IotaSRA` discharged -/

section Discharged
variable {E : ResolvedEnvA} {n : Nat}

/-- annotation of typing at the D-judgment, `IotaSRA` discharged by `iotaSRA`
    (`RcicAnnIotaSR`). Premises: `AnnEnvA` alone — no `EnvNormEraseA`. -/
theorem annHasTyTD' (C : AnnEnvA E) {Γ : LCtx} {e T : Expr Nat}
    (h : HasTyTD E n Γ e T) {ΓA : LCtxA} (hΓA : CtxWfA E (iotaIfaceA E) n ΓA)
    (hctx : eraseCtx ΓA = Γ) :
    ∃ eA TA, erase eA = e ∧ erase TA = T ∧ Nonempty (HasTyA E (iotaIfaceA E) n ΓA eA TA) :=
  annHasTyTD C (iotaSRA C) h hΓA hctx

/-- annotation of a well-formed D-context. -/
theorem annCtxWfTD' (C : AnnEnvA E) {Γ : LCtx} (hΓ : CtxWfTD E n Γ) :
    ∃ ΓA, eraseCtx ΓA = Γ ∧ Nonempty (CtxWfA E (iotaIfaceA E) n ΓA) :=
  annCtxWfTD C (iotaSRA C) hΓ

/-- annotation of conversion at the D-judgment, `IotaSRA` discharged. Premises: `AnnEnvA`
    alone. -/
theorem annConvTD' (C : AnnEnvA E) {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvTD E n Γ a b T) {ΓA : LCtxA} (hΓA : CtxWfA E (iotaIfaceA E) n ΓA)
    (hctx : eraseCtx ΓA = Γ) :
    ∃ aA bA TA, erase aA = a ∧ erase bA = b ∧ erase TA = T ∧
      Nonempty (ConvA E (iotaIfaceA E) n ΓA aA bA TA) :=
  annConvTD C (iotaSRA C) h hΓA hctx

end Discharged

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.annHasTyTD
#print axioms Rcic.Declarative.Ann.annConvTD
#print axioms Rcic.Declarative.Ann.annCtxWfTD
#print axioms Rcic.Declarative.Ann.annHasTyTD'
#print axioms Rcic.Declarative.Ann.annConvTD'
#print axioms Rcic.Declarative.Ann.annCtxWfTD'
