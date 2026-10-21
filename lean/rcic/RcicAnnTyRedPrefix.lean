import rcic.RcicAnnLevels

/-!
# DT-025 / A-6 M1 — step and chain transport for the W-DT025-Hop discharge

The hop-face discharge (the admission-induction route on #6351,
`research/rcic/dt025-a6/M1_HOP_DISCHARGE_SCRATCH.md`) computes each transparent
member's body chain at the member's own admission prefix `E₀`, then transports
it to the full environment `E`, an arbitrary level instantiation `ls`, and an
arbitrary well-formed context `Γ'`. This file holds the two missing transport
families that route needs:

1. **environment-prefix monotonicity** (`tyHRedA_prefix`, `tmChainA_prefix`,
   `tyHRedStarA_prefix`): every environment read inside a typed step is on a
   constant of the stepping term, which `hasTyA_constsIn` bounds to `E₀`'s
   domain, and `PrefixA` preserves the reads (the iota-machinery agreement
   lemmas `recAtMajorA_prefix`, `unitMinorA_prefix`, `structArmA_prefix`,
   `structHeadA_prefix`, `hStepFnA_prefix`, `iotaRel_prefix` of
   `RcicAnnLREnv`). The typing premises travel by `hasTyEnvA` /
   `convEnvA` / `tyConvA_env`.

2. **level instantiation** (`tyHRedA_instLevels`, `tmChainA_instLevels`,
   `tyHRedStarA_instLevels`): `instantiateLevelsA` commutes with every shape
   the steps consult (`instantiateLevelsA_instantiate0A`,
   `instantiateLevelsA_instantiateLevelsA`, `appsSpineA_instLevels`,
   `unitMinorA_instLevels`, `structArmA_instLevels`,
   `structHeadA_instLevels`, `recAtMajorA_instLevels`,
   `hStepFnA_instLevels`, `instantiateLevelsA_natExpandA`), and the typing /
   conversion premises travel by `hasTyA_instLevels` / `convA_instLevels` /
   `tyConvA_instLevels` of `RcicAnnLevels`.

Together with `tyHRedStarA_wk` (context weakening, `RcicAnnFamWk`) these give
the full `prefix r, [] → E, Γ', ls` transport of `HopFacesA`'s δ-face.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the reduct names only constants of the stepping environment -/

/-- a typed step's reduct is a typed term of the same environment, so its
    constants are in `E`'s domain (`hasTyA_constsIn` on the carried reduct
    typing, `tyHRedA_hasTy_right`). -/
theorem tyHRedA_constsIn {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {a b A : ExprA} (h : TyHRedA E I n Γ a b A) :
    ConstsInA (domA E) b :=
  hasTyA_constsIn (tyHRedA_hasTy_right h)

/-! ## (2) environment-prefix monotonicity -/

section EnvPrefix
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- ONE typed step transports along `E₀ ⊑ E`. Every guarded env-read
    (`recAtMajorA`, `unitMinorA`, `structArmA`, `structHeadA`, `hStepFnA`,
    `I.rel`) is at a term whose constants lie in `domA E₀` — `f`'s own typing
    `hfTy` in `major`, the conversion's left side in `kunit`/`kstruct`, the
    step's lhs typing in `iota` — and `PrefixA` agrees on `E₀`'s members. -/
def tyHRedA_prefix (hpre : PrefixA E₀ E) :
    {Γ : LCtxA} → {a b A : ExprA} → TyHRedA E₀ I n Γ a b A →
    TyHRedA E I n Γ a b A
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred =>
      .beta Γ A u body arg B (hasTyEnvA hpre hA) (hasTyEnvA hpre hbody)
        (hasTyEnvA hpre harg) (hasTyEnvA hpre hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred =>
      .zeta Γ A value body B u (hasTyEnvA hpre hA) (hasTyEnvA hpre hv)
        (hasTyEnvA hpre hb) (hasTyEnvA hpre hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      .zetaLocal Γ i A v hval hty (hasTyEnvA hpre hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      .delta Γ r ls m b (hpre r m hres) hbody htr hlen hwf (hasTyEnvA hpre hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota Γ lhs rhs T (iotaRel_prefix hpre (hasTyA_constsIn hlhs) h)
        (hasTyEnvA hpre hlhs) (hasTyEnvA hpre hrhs)
  | _, _, _, _, .lit Γ t T hexp => .lit Γ t T (hasTyEnvA hpre hexp)
  | _, _, _, _, .app Γ f f' a A B T₀ u v w h hc hB hTy ha =>
      .app Γ f f' a A B T₀ u v w (tyHRedA_prefix hpre h) (tyConvA_env hpre hc)
        (hasTyEnvA hpre hB) (hasTyEnvA hpre hTy) (hasTyEnvA hpre ha)
  | _, _, _, _, .conv Γ a b A A' h hc =>
      .conv Γ a b A A' (tyHRedA_prefix hpre h) (tyConvA_env hpre hc)
  | _, _, _, _, .major Γ f a a' A B T₀ u v hrec hu hs hf hi h hc hfTy hB hrt =>
      have hcf : ConstsInA (domA E₀) f := hasTyA_constsIn hfTy
      .major Γ f a a' A B T₀ u v (recAtMajorA_prefix hpre hcf ▸ hrec)
        (unitMinorA_prefix hpre hcf ▸ hu) (structHeadA_prefix hpre hcf ▸ hs)
        (hStepFnA_prefix hpre I.fn Γ f hcf ▸ hf) hi (tyHRedA_prefix hpre h)
        (tyConvA_env hpre hc) (hasTyEnvA hpre hfTy) (hasTyEnvA hpre hB)
        (hasTyEnvA hpre hrt)
  | _, _, _, _, .kunit Γ f a mn T hrec hu hf hi hcv hrt =>
      have hcf : ConstsInA (domA E₀) f := (convA_constsIn hcv).1.1
      .kunit Γ f a mn T (recAtMajorA_prefix hpre hcf ▸ hrec)
        (unitMinorA_prefix hpre hcf ▸ hu) (hStepFnA_prefix hpre I.fn Γ f hcf ▸ hf)
        hi (convEnvA hpre hcv) (hasTyEnvA hpre hrt)
  | _, _, _, _, .kstruct Γ f a e T hrec hs hf hcv hrt =>
      have hcf : ConstsInA (domA E₀) f := (convA_constsIn hcv).1.1
      .kstruct Γ f a e T (recAtMajorA_prefix hpre hcf ▸ hrec)
        (structArmA_prefix hpre hcf a ▸ hs) (hStepFnA_prefix hpre I.fn Γ f hcf ▸ hf)
        (convEnvA hpre hcv) (hasTyEnvA hpre hrt)

/-- a whole chain transports along `E₀ ⊑ E`. -/
def tmChainA_prefix (hpre : PrefixA E₀ E) {Γ : LCtxA} {A : ExprA} :
    {a N : ExprA} → TmChainA E₀ I n Γ A a N → TmChainA E I n Γ A a N
  | _, _, .refl _ h => .refl _ (hasTyEnvA hpre h)
  | _, _, .cons a a' _ ha hs t =>
      .cons a a' _ (hasTyEnvA hpre ha) (tyHRedA_prefix hpre hs) (tmChainA_prefix hpre t)

/-- chains, at the `TyHRedStarA` level. -/
theorem tyHRedStarA_prefix (hpre : PrefixA E₀ E) {Γ : LCtxA} {a N A : ExprA}
    (h : TyHRedStarA E₀ I n Γ a N A) : TyHRedStarA E I n Γ a N A :=
  h.elim fun t => ⟨tmChainA_prefix hpre t⟩

/-- the endpoint is preserved along `E₀ ⊑ E` for `E₀`-named constants —
    `hStepFnA_prefix` pointwise. -/
theorem hStepFnA_none_prefix (hpre : PrefixA E₀ E) (IFn : IotaFnA) (Γ : LCtxA)
    {e : ExprA} (hc : ConstsInA (domA E₀) e)
    (h : hStepFnA E₀ IFn Γ e = none) : hStepFnA E IFn Γ e = none :=
  hStepFnA_prefix hpre IFn Γ e hc ▸ h

end EnvPrefix

/-! ## (3) level instantiation -/

section InstLevels
variable {E : ResolvedEnvA} {I : IotaIfaceA} {a n : Nat} {ls : List Level}

/-- the `ConstsArityA` mirror of `convA_constsIn` (`RcicAnnLREnv`): a
    conversion's sides carry their constants' arities, hereditary through the
    embedded typings. Needed at `kunit`/`kstruct`, whose only typed side is the
    conversion `hcv`. -/
def convA_constsArity {n : Nat} :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E I n Γ a b A →
    ConstsArityA E a ∧ ConstsArityA E b
  | _, _, _, _, .refl _ _ _ h => ⟨hasTyA_constsArity h, hasTyA_constsArity h⟩
  | _, _, _, _, .symm _ _ _ _ h => (convA_constsArity h).symm
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 =>
      ⟨(convA_constsArity h1).1, (convA_constsArity h2).2⟩
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg hred =>
      ⟨⟨⟨hasTyA_constsArity hA, hasTyA_constsArity hbody⟩, hasTyA_constsArity harg⟩,
       hasTyA_constsArity hred⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb hred =>
      ⟨⟨hasTyA_constsArity hA, hasTyA_constsArity hv, hasTyA_constsArity hb⟩,
       hasTyA_constsArity hred⟩
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => ⟨trivial, hasTyA_constsArity hv⟩
  | _, _, _, _, .delta _ r ms m _ hres _ _ hlen _ hb =>
      ⟨⟨m, hres, hlen⟩, hasTyA_constsArity hb⟩
  | _, _, _, _, .iota _ _ _ _ _ hlhs hrhs =>
      ⟨hasTyA_constsArity hlhs, hasTyA_constsArity hrhs⟩
  | _, _, _, _, .structIota _ _ _ _ _ _ _ _ _ hlhs hrhs _ =>
      ⟨hasTyA_constsArity hlhs, hasTyA_constsArity hrhs⟩
  | _, _, _, _, .lit _ _ _ hexp => ⟨trivial, hasTyA_constsArity hexp⟩
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 _ _ =>
      ⟨⟨(convA_constsArity h1).1, (convA_constsArity h2).1⟩,
       ⟨(convA_constsArity h1).2, (convA_constsArity h2).2⟩⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ hA hb hrt =>
      ⟨⟨(convA_constsArity hA).1, (convA_constsArity hb).1⟩, hasTyA_constsArity hrt⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ hA hB hrt =>
      ⟨⟨(convA_constsArity hA).1, (convA_constsArity hB).1⟩, hasTyA_constsArity hrt⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hrt =>
      ⟨⟨(convA_constsArity hA).1, (convA_constsArity hv).1, (convA_constsArity hb).1⟩,
       hasTyA_constsArity hrt⟩
  | _, _, _, _, .sorts _ _ _ _ => ⟨trivial, trivial⟩
  | _, _, _, _, .consts _ r _ _ m hres hlen _ _ _ hrt =>
      ⟨⟨m, hres, hlen⟩, hasTyA_constsArity hrt⟩
  | _, _, _, _, .eta _ _ _ _ _ _ h hrt => ⟨hasTyA_constsArity hrt, hasTyA_constsArity h⟩
  | _, _, _, _, .irr _ _ _ _ _ hp hq => ⟨hasTyA_constsArity hp, hasTyA_constsArity hq⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h _ _ _ _ _ => convA_constsArity h

/-- ONE typed step instantiates. The `delta` arm composes the two level
    substitutions (`instantiateLevelsA_instantiateLevelsA`); `beta`/`zeta`/
    `app`/`major` use `instantiateLevelsA_instantiate0A`; the guarded reads
    commute by the `*_instLevels` shape lemmas; `iota` splits into `I.fn`
    (`hIL`) and `hStepFnA` (`hStepFnA_instLevels`, arity-correct by
    `hasTyA_constsArity`). -/
def tyHRedA_instLevels (hEL : EnvLevelsA E) (hIL : IotaLevelsA I)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtxA} → {x y A : ExprA} → TyHRedA E I a Γ x y A →
    TyHRedA E I n (instCtxA ls Γ) (instantiateLevelsA ls x)
      (instantiateLevelsA ls y) (instantiateLevelsA ls A)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred => by
      rw [instantiateLevelsA_instantiate0A, instantiateLevelsA_instantiate0A]
      exact .beta (instCtxA ls Γ) (instantiateLevelsA ls A) (instLevel ls u)
        (instantiateLevelsA ls body) (instantiateLevelsA ls arg)
        (instantiateLevelsA ls B) (hasTyA_instLevels hEL hIL hls hlen hA)
        (hasTyA_instLevels hEL hIL hls hlen hbody)
        (hasTyA_instLevels hEL hIL hls hlen harg)
        (by rw [← instantiateLevelsA_instantiate0A, ← instantiateLevelsA_instantiate0A]
            exact hasTyA_instLevels hEL hIL hls hlen hred)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred => by
      rw [instantiateLevelsA_instantiate0A, instantiateLevelsA_instantiate0A]
      exact .zeta (instCtxA ls Γ) (instantiateLevelsA ls A)
        (instantiateLevelsA ls value) (instantiateLevelsA ls body)
        (instantiateLevelsA ls B) (instLevel ls u)
        (hasTyA_instLevels hEL hIL hls hlen hA) (hasTyA_instLevels hEL hIL hls hlen hv)
        (hasTyA_instLevels hEL hIL hls hlen hb)
        (by rw [← instantiateLevelsA_instantiate0A, ← instantiateLevelsA_instantiate0A]
            exact hasTyA_instLevels hEL hIL hls hlen hred)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv => by
      have hval' : lookupValueA (instCtxA ls Γ) i =
          some (instantiateLevelsA ls v) := by
        rw [lookupValueA_instCtxA, hval]; rfl
      have hty' : lookupTypeA (instCtxA ls Γ) i =
          some (instantiateLevelsA ls A) := by
        rw [lookupTypeA_instCtxA, hty]; rfl
      exact .zetaLocal (instCtxA ls Γ) i (instantiateLevelsA ls A)
        (instantiateLevelsA ls v) hval' hty' (hasTyA_instLevels hEL hIL hls hlen hv)
  | _, _, _, _, .delta Γ r ms m b hres hbody htr hlen' hwf hb => by
      show TyHRedA E I n (instCtxA ls Γ) (.const r (ms.map (instLevel ls)))
        (instantiateLevelsA ls (instantiateLevelsA ms b))
        (instantiateLevelsA ls (instantiateLevelsA ms m.mtypeA))
      rw [instLevels_mbody hEL hres hbody hlen' ls, instLevels_mtype hEL hres hlen' ls]
      exact .delta (instCtxA ls Γ) r (ms.map (instLevel ls)) m b hres hbody htr
        (length_map_arity hlen' _) (levelsBounded_inst hls hlen hwf)
        (by rw [← instLevels_mbody hEL hres hbody hlen' ls,
            ← instLevels_mtype hEL hres hlen' ls]
            exact hasTyA_instLevels hEL hIL hls hlen hb)
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs => by
      refine .iota (instCtxA ls Γ) (instantiateLevelsA ls lhs)
        (instantiateLevelsA ls rhs) (instantiateLevelsA ls T) ⟨?_, ?_⟩
        (hasTyA_instLevels hEL hIL hls hlen hlhs)
        (hasTyA_instLevels hEL hIL hls hlen hrhs)
      · rw [hIL ls lhs, h.1]; rfl
      · rw [hStepFnA_instLevels hEL hIL ls Γ lhs (hasTyA_constsArity hlhs), h.2]
        rfl
  | _, _, _, _, .lit Γ t T hexp => by
      rw [instantiateLevelsA_natExpandA]
      exact .lit (instCtxA ls Γ) t (instantiateLevelsA ls T)
        (by rw [← instantiateLevelsA_natExpandA]
            exact hasTyA_instLevels hEL hIL hls hlen hexp)
  | _, _, _, _, .app Γ f f' x A B T₀ u v w h hc hB hTy ha => by
      rw [instantiateLevelsA_instantiate0A]
      exact .app (instCtxA ls Γ) (instantiateLevelsA ls f)
        (instantiateLevelsA ls f') (instantiateLevelsA ls x)
        (instantiateLevelsA ls A) (instantiateLevelsA ls B)
        (instantiateLevelsA ls T₀) (instLevel ls u) (instLevel ls v)
        (instLevel ls w) (tyHRedA_instLevels hEL hIL hls hlen h)
        (tyConvA_instLevels hEL hIL hls hlen hc)
        (hasTyA_instLevels hEL hIL hls hlen hB)
        (by rw [← instantiateLevelsA_instantiate0A]
            exact hasTyA_instLevels hEL hIL hls hlen hTy)
        (hasTyA_instLevels hEL hIL hls hlen ha)
  | _, _, _, _, .conv Γ x y A A' h hc => by
      exact .conv (instCtxA ls Γ) (instantiateLevelsA ls x)
        (instantiateLevelsA ls y) (instantiateLevelsA ls A)
        (instantiateLevelsA ls A') (tyHRedA_instLevels hEL hIL hls hlen h)
        (tyConvA_instLevels hEL hIL hls hlen hc)
  | _, _, _, _, .major Γ f x x' A B T₀ u v hrec hu hs hf hi h hc hfTy hB hrt => by
      rw [instantiateLevelsA_instantiate0A]
      refine .major (instCtxA ls Γ) (instantiateLevelsA ls f)
        (instantiateLevelsA ls x) (instantiateLevelsA ls x')
        (instantiateLevelsA ls A) (instantiateLevelsA ls B)
        (instantiateLevelsA ls T₀) (instLevel ls u) (instLevel ls v)
        ?_ ?_ ?_ ?_ ?_ (tyHRedA_instLevels hEL hIL hls hlen h)
        (tyConvA_instLevels hEL hIL hls hlen hc)
        (hasTyA_instLevels hEL hIL hls hlen hfTy)
        (hasTyA_instLevels hEL hIL hls hlen hB)
        (by rw [← instantiateLevelsA_instantiate0A]
            exact hasTyA_instLevels hEL hIL hls hlen hrt)
      · rw [recAtMajorA_instLevels]; exact hrec
      · rw [unitMinorA_instLevels, hu]; rfl
      · rw [structHeadA_instLevels]; exact hs
      · rw [hStepFnA_instLevels hEL hIL ls Γ f (hasTyA_constsArity hfTy), hf]; rfl
      · show I.fn (instantiateLevelsA ls (.app f x)) = none
        rw [hIL, hi]; rfl
  | _, _, _, _, .kunit Γ f x mn T hrec hu hf hi hcv hrt => by
      refine .kunit (instCtxA ls Γ) (instantiateLevelsA ls f)
        (instantiateLevelsA ls x) (instantiateLevelsA ls mn)
        (instantiateLevelsA ls T) ?_ ?_ ?_ ?_
        (convA_instLevels hEL hIL hls hlen hcv)
        (hasTyA_instLevels hEL hIL hls hlen hrt)
      · rw [recAtMajorA_instLevels]; exact hrec
      · rw [unitMinorA_instLevels, hu]; rfl
      · rw [hStepFnA_instLevels hEL hIL ls Γ f (convA_constsArity hcv).1.1, hf]; rfl
      · show I.fn (instantiateLevelsA ls (.app f x)) = none
        rw [hIL, hi]; rfl
  | _, _, _, _, .kstruct Γ f x e T hrec hs hf hcv hrt => by
      refine .kstruct (instCtxA ls Γ) (instantiateLevelsA ls f)
        (instantiateLevelsA ls x) (instantiateLevelsA ls e)
        (instantiateLevelsA ls T) ?_ ?_ ?_
        (convA_instLevels hEL hIL hls hlen hcv)
        (hasTyA_instLevels hEL hIL hls hlen hrt)
      · rw [recAtMajorA_instLevels]; exact hrec
      · rw [structArmA_instLevels hEL ls f x (convA_constsArity hcv).1.1, hs]; rfl
      · rw [hStepFnA_instLevels hEL hIL ls Γ f (convA_constsArity hcv).1.1, hf]; rfl

/-- a whole chain instantiates. -/
def tmChainA_instLevels (hEL : EnvLevelsA E) (hIL : IotaLevelsA I)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) {Γ : LCtxA} {A : ExprA} :
    {x N : ExprA} → TmChainA E I a Γ A x N →
    TmChainA E I n (instCtxA ls Γ) (instantiateLevelsA ls A)
      (instantiateLevelsA ls x) (instantiateLevelsA ls N)
  | _, _, .refl _ h => .refl _ (hasTyA_instLevels hEL hIL hls hlen h)
  | _, _, .cons x x' N ha hs t =>
      .cons (instantiateLevelsA ls x) (instantiateLevelsA ls x') (instantiateLevelsA ls N)
        (hasTyA_instLevels hEL hIL hls hlen ha)
        (tyHRedA_instLevels hEL hIL hls hlen hs) (tmChainA_instLevels hEL hIL hls hlen t)

/-- chains, at the `TyHRedStarA` level. -/
theorem tyHRedStarA_instLevels (hEL : EnvLevelsA E) (hIL : IotaLevelsA I)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) {Γ : LCtxA} {x N A : ExprA}
    (h : TyHRedStarA E I a Γ x N A) :
    TyHRedStarA E I n (instCtxA ls Γ) (instantiateLevelsA ls x)
      (instantiateLevelsA ls N) (instantiateLevelsA ls A) :=
  h.elim fun t => ⟨tmChainA_instLevels hEL hIL hls hlen t⟩

end InstLevels

end Rcic.Declarative.Ann
