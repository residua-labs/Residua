import rcic.RcicSynSRLitPiCLW
import rcic.RcicTypedSubstLet
import rcic.RcicTypedLevels
import rcic.RcicCtxConvT
import rcic.RcicIARecIH
import rcic.RcicParRedT
import rcic.RcicSubstCalc
import rcic.RcicTypedEnvEntry

/-!
# `RcicSynSRLitPiErase` — `TyPEraseW` attacked by mutual induction (cc 12:50Z, item 1)

`TyPEraseW` (CLW §B1, as consumed): every `TyP` derivation erases to a
`HasTyT` derivation at the same judgment. `tyPErase`/`cvPErase` below is
that induction, `CvP`'s motive strengthened to the triple
`ConvT × HasTyT-left × HasTyT-right` — the `cctx`/`fsub` arms consume
endpoint typings that live inside the CvP premise's own `dl`/`dr` fields,
invisible to a bare `ConvT` motive.

Each TyP rule against its HasTyT image:

| TyP ctor | image | cost |
|---|---|---|
| sort/bvar/pi/lam/app/letE/lit | same ctor (+ `ConvT.sorts` conv for `sort`'s eqN slack) | free |
| conv | `HasTyT.conv` + the mutual CvP half | free |
| const | `.const` + `hasTyT_of_tyConvT` | `InstEqNCongrW` (named already, §B2) |
| wk/esub/lsub/linst | `hasTyTWeaken`/`hasTyT_substS`/`hasTyT_substLetS`/`hasTyT_instLevels` | `TyPEraseGatesW` at E |
| cctx | `hasTyT_ctx` over one converted binder | `TyPEraseGatesW` at E |
| ewk | `hasTyTEwk` (§1) | `DerivedIotaEwkW` |

and on the CvP side the same plus `fsub` via `convT_substCongr` at `j = 0`
(gates only). So `TyPEraseW` — which quantifies envs UNRESTRICTED — reduces
to exactly three named Props:

1. `TyPEraseGatesW` — every env carries `EnvClosed ∧ EnvMembersSubstStable ∧
   EnvLevelsT ∧ IotaLevelsT` (the fronts every landed typed transport reads).
2. `InstEqNCongrW` — the `const` arm's `eqNList` instantiation congruence.
3. `DerivedIotaEwkW` — `ewk`'s only missing image: `IotaWitness` walks E's
   member list, so env extension does not transport a derived iota.

On-cone (Demand-reachable) inhabitants in §4: all four gates at `emptyEnv`
(each an `EnvWfT.empty` projection) and `DerivedIotaEwkW` at source
`emptyEnv`, vacuous (`IotaWitness.hfam` needs a member `emptyEnv` lacks).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 the two new named Props (`InstEqNCongrW` is already named, CLW §B2) -/

/-- the gate bundle the erasure reads at every env it visits: the four
    structures the landed `HasTyT`/`ConvT` transports are gated on
    (`EnvClosed` for wk/cctx; `+EnvMembersSubstStable` for esub/lsub/fsub;
    `EnvLevelsT ∧ IotaLevelsT` for linst). All four are `EnvWfT`-theorems
    per env — the wall is that they hold at EVERY env a derivation touches. -/
def TyPEraseGatesW : Prop :=
  ∀ (E : ResolvedEnv),
    EnvClosed E ∧ EnvMembersSubstStable E ∧ EnvLevelsT E ∧ IotaLevelsT E

/-- `ewk`'s only missing image, isolated: `DerivedIota E₀` does not transport
    across `EnvExt E₀ E` — `IotaWitness` reads E's member rules, which the
    extension may change. Every other constructor transports structurally
    (§1 proves both sides under exactly this hypothesis). -/
def DerivedIotaEwkW : Prop :=
  ∀ {E₀ E : ResolvedEnv}, EnvExt E₀ E → ∀ {l r : Expr Nat},
    DerivedIota E₀ l r → Nonempty (DerivedIota E l r)

/-! ## §1 env extension on `HasTyT`/`ConvT` modulo `DerivedIotaEwkW`

`const`/`delta`/`consts` re-resolve their member through `hext`; `.iota` is
the boundary's one consumption. -/

mutual

/-- `HasTyT` under env extension. -/
def hasTyTEwk (hι : DerivedIotaEwkW) {E₀ E : ResolvedEnv} (hext : EnvExt E₀ E) :
    {n : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    HasTyT E₀ n Γ e A → Nonempty (HasTyT E n Γ e A)
  | _, _, _, _, .sort Γ l => ⟨.sort Γ l⟩
  | _, _, _, _, .bvar Γ i A h => ⟨.bvar Γ i A h⟩
  | _, _, _, _, .const Γ r ls m hres hlen hwf =>
      ⟨.const Γ r ls m (hext _ _ hres) hlen hwf⟩
  | _, _, _, _, .pi Γ A u B v hA hB =>
      (hasTyTEwk hι hext hA).elim fun ka =>
      (hasTyTEwk hι hext hB).elim fun kb => ⟨.pi Γ A u B v ka kb⟩
  | _, _, _, _, .lam Γ A u body B hA hbody =>
      (hasTyTEwk hι hext hA).elim fun ka =>
      (hasTyTEwk hι hext hbody).elim fun kb => ⟨.lam Γ A u body B ka kb⟩
  | _, _, _, _, .app Γ f a A B hf ha =>
      (hasTyTEwk hι hext hf).elim fun kf =>
      (hasTyTEwk hι hext ha).elim fun ka => ⟨.app Γ f a A B kf ka⟩
  | _, _, _, _, .letE Γ A u value B body hA hv hb =>
      (hasTyTEwk hι hext hA).elim fun ka =>
      (hasTyTEwk hι hext hv).elim fun kv =>
      (hasTyTEwk hι hext hb).elim fun kb => ⟨.letE Γ A u value B body ka kv kb⟩
  | _, _, _, _, .lit Γ t T hexp =>
      (hasTyTEwk hι hext hexp).elim fun k => ⟨.lit Γ t T k⟩
  | _, _, _, _, .conv Γ e A B u h hc =>
      (hasTyTEwk hι hext h).elim fun k =>
      (convTEwk hι hext hc).elim fun kc => ⟨.conv Γ e A B u k kc⟩

/-- `ConvT` under env extension. -/
def convTEwk (hι : DerivedIotaEwkW) {E₀ E : ResolvedEnv} (hext : EnvExt E₀ E) :
    {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    ConvT E₀ n Γ a b T → Nonempty (ConvT E n Γ a b T)
  | _, _, _, _, _, .refl Γ a A h =>
      (hasTyTEwk hι hext h).elim fun k => ⟨.refl Γ a A k⟩
  | _, _, _, _, _, .symm Γ a b A h =>
      (convTEwk hι hext h).elim fun k => ⟨.symm Γ a b A k⟩
  | _, _, _, _, _, .trans Γ a b c A h1 h2 =>
      (convTEwk hι hext h1).elim fun k1 =>
      (convTEwk hι hext h2).elim fun k2 => ⟨.trans Γ a b c A k1 k2⟩
  | _, _, _, _, _, .beta Γ A body arg B u hA hbody harg =>
      (hasTyTEwk hι hext hA).elim fun kA =>
      (hasTyTEwk hι hext hbody).elim fun kb =>
      (hasTyTEwk hι hext harg).elim fun kg => ⟨.beta Γ A body arg B u kA kb kg⟩
  | _, _, _, _, _, .zeta Γ A value body B u hA hv hb =>
      (hasTyTEwk hι hext hA).elim fun kA =>
      (hasTyTEwk hι hext hv).elim fun kv =>
      (hasTyTEwk hι hext hb).elim fun kb => ⟨.zeta Γ A value body B u kA kv kb⟩
  | _, _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      (hasTyTEwk hι hext hv).elim fun kv => ⟨.zetaLocal Γ i A v hval hty kv⟩
  | _, _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      (hasTyTEwk hι hext hb).elim fun kb =>
      ⟨.delta Γ r ls m b (hext _ _ hres) hbody htr hlen hwf kb⟩
  | _, _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      (hι hext h).elim fun k =>
      (hasTyTEwk hι hext hlhs).elim fun kl =>
      (hasTyTEwk hι hext hrhs).elim fun kr => ⟨.iota Γ lhs rhs T k kl kr⟩
  | _, _, _, _, _, .lit Γ t exp T h hexp =>
      (hasTyTEwk hι hext hexp).elim fun k => ⟨.lit Γ t exp T h k⟩
  | _, _, _, _, _, .app Γ f g a b A B h1 h2 =>
      (convTEwk hι hext h1).elim fun k1 =>
      (convTEwk hι hext h2).elim fun k2 => ⟨.app Γ f g a b A B k1 k2⟩
  | _, _, _, _, _, .lam Γ A A' b b' B u hA hb =>
      (convTEwk hι hext hA).elim fun kA =>
      (convTEwk hι hext hb).elim fun kb => ⟨.lam Γ A A' b b' B u kA kb⟩
  | _, _, _, _, _, .pi Γ A A' B B' u v hA hB =>
      (convTEwk hι hext hA).elim fun kA =>
      (convTEwk hι hext hB).elim fun kB => ⟨.pi Γ A A' B B' u v kA kB⟩
  | _, _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb =>
      (convTEwk hι hext hA).elim fun kA =>
      (convTEwk hι hext hv).elim fun kv =>
      (convTEwk hι hext hb).elim fun kb => ⟨.letE Γ A A' v v' b b' B u kA kv kb⟩
  | _, _, _, _, _, .sorts Γ l₁ l₂ h => ⟨.sorts Γ l₁ l₂ h⟩
  | _, _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h =>
      ⟨.consts Γ r ls ls' m (hext _ _ hres) hlen hwf hwf' h⟩
  | _, _, _, _, _, .eta Γ f A B h =>
      (hasTyTEwk hι hext h).elim fun k => ⟨.eta Γ f A B k⟩
  | _, _, _, _, _, .irr Γ P p q hP hp hq =>
      (hasTyTEwk hι hext hP).elim fun kP =>
      (hasTyTEwk hι hext hp).elim fun kp =>
      (hasTyTEwk hι hext hq).elim fun kq => ⟨.irr Γ P p q kP kp kq⟩
  | _, _, _, _, _, .tyConv Γ a b A A' u h hA =>
      (convTEwk hι hext h).elim fun k =>
      (convTEwk hι hext hA).elim fun kA => ⟨.tyConv Γ a b A A' u k kA⟩

end
/-! ## §2 the erasure, mutual over `TyP`/`CvP`

`cvPErase`'s motive is the triple: the conversion plus BOTH endpoints'
typings — `cctx` needs its `hA` premise's endpoint typings (which are
`hA.dl`/`hA.dr`, NOT subterms the recursor sees), and `fsub` needs `hab`'s
left endpoint as the substitution's replacement typing. -/

mutual

/-- TyP→HasTyT erasure. Arms: `sort` retypes through `ConvT.sorts` (eqN
    symmetric on the definitional `eval`); `const` is `.const` retyped by
    `hB2` + `hasTyT_of_tyConvT`; `conv` is the mutual CvP half; transports
    read `hG` at the ambient env; `ewk` is §1 modulo `hι`. -/
def tyPErase (hG : TyPEraseGatesW) (hB2 : InstEqNCongrW) (hι : DerivedIotaEwkW) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e A : Expr Nat} →
    TyP E n Γ e A → Nonempty (HasTyT E n Γ e A)
  | _, _, _, _, _, .sort _ _ _ l k h =>
      ⟨.conv _ _ _ _ _ (.sort _ l) (.sorts _ _ _ fun ρ => (h ρ).symm)⟩
  | _, _, _, _, _, .bvar _ _ _ i A _ h _ => ⟨.bvar _ i A h⟩
  | _, _, _, _, _, .const _ _ _ r ls ls₀ m _ hres hlen hwf hls _ =>
      (hB2 hls).elim fun kc =>
        ⟨hasTyT_of_tyConvT (.const _ r ls m hres hlen hwf) kc⟩
  | _, _, _, _, _, .pi _ _ _ A u B v hA hB =>
      (tyPErase hG hB2 hι hA).elim fun ka =>
      (tyPErase hG hB2 hι hB).elim fun kb => ⟨.pi _ A u B v ka kb⟩
  | _, _, _, _, _, .lam _ _ _ A u body B _ hA hbody _ =>
      (tyPErase hG hB2 hι hA).elim fun ka =>
      (tyPErase hG hB2 hι hbody).elim fun kb => ⟨.lam _ A u body B ka kb⟩
  | _, _, _, _, _, .app _ _ _ f a A B _ hf ha _ =>
      (tyPErase hG hB2 hι hf).elim fun kf =>
      (tyPErase hG hB2 hι ha).elim fun ka => ⟨.app _ f a A B kf ka⟩
  | _, _, _, _, _, .letE _ _ _ A u value B body _ hA hv hb _ =>
      (tyPErase hG hB2 hι hA).elim fun ka =>
      (tyPErase hG hB2 hι hv).elim fun kv =>
      (tyPErase hG hB2 hι hb).elim fun kb => ⟨.letE _ A u value B body ka kv kb⟩
  | _, _, _, _, _, .lit _ _ _ t _ hexp =>
      (tyPErase hG hB2 hι hexp).elim fun k => ⟨.lit _ t _ k⟩
  | _, _, _, _, _, .conv _ _ _ e A B u h hc =>
      (tyPErase hG hB2 hι h).elim fun k =>
      (cvPErase hG hB2 hι hc).1.elim fun kc => ⟨.conv _ e A B u k kc⟩
  | E, _, _, _, _, .wk _ _ _ _ _ d c D =>
      (tyPErase hG hB2 hι D).elim fun k => ⟨hasTyTWeaken d (hG E).1 k⟩
  | E, _, _, _, _, .esub _ _ _ _ _ t v j _ D hget hv _ =>
      (tyPErase hG hB2 hι D).elim fun k =>
      (tyPErase hG hB2 hι hv).elim fun kv =>
        ⟨hasTyT_substS (hG E).1 (hG E).2.1 v t k hget kv⟩
  | E, _, _, _, _, .lsub _ _ _ _ _ t v j _ D hget hv _ =>
      (tyPErase hG hB2 hι D).elim fun k =>
      (tyPErase hG hB2 hι hv).elim fun kv =>
        ⟨hasTyT_substLetS (hG E).1 (hG E).2.1 t v k hget kv⟩
  | E, _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen D =>
      (tyPErase hG hB2 hι D).elim fun k =>
        ⟨hasTyT_instLevels (hG E).2.2.1 (hG E).2.2.2 hls hlen k⟩
  | _, _, _, _, _, .ewk _ _ _ _ _ _ hext D =>
      (tyPErase hG hB2 hι D).elim fun k => hasTyTEwk hι hext k
  | E, _, _, _, _, .cctx _ _ _ _ _ A A' _ D hA =>
      (tyPErase hG hB2 hι D).elim fun k =>
      (cvPErase hG hB2 hι hA).1.elim fun kc =>
      (cvPErase hG hB2 hι hA).2.1.elim fun kl =>
      (cvPErase hG hB2 hι hA).2.2.elim fun kr =>
        ⟨hasTyT_ctx (hG E).1 (.assumption (ctxConvT_refl _) kl kr kc) k⟩

/-- CvP→ConvT erasure with both endpoints. Non-transport arms: the matching
    `ConvT` ctor (premise typings from the field IHs) plus `dl`/`dr`'s
    erasures. Transports: `convTWeaken`/`convT_substS`/`convT_instLevels`
    plus `hasTyT*` for the endpoints; `ewk` via §1; `cctx` via `convT_ctx`
    over `CtxConvT.assumption` built from `hA`'s own triple; `fsub` is
    `convT_substCongr` at `j = 0` (`hab`'s left endpoint is the
    replacement's typing). -/
def cvPErase (hG : TyPEraseGatesW) (hB2 : InstEqNCongrW) (hι : DerivedIotaEwkW) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvP E n Γ a b T →
    Nonempty (ConvT E n Γ a b T) ∧ Nonempty (HasTyT E n Γ a T) ∧
      Nonempty (HasTyT E n Γ b T)
  | _, _, _, _, _, _, .refl _ _ _ _ _ _ dl dr =>
      (tyPErase hG hB2 hι dl).elim fun kl =>
      (tyPErase hG hB2 hι dr).elim fun kr => ⟨⟨.refl _ _ _ kl⟩, ⟨kl⟩, ⟨kr⟩⟩
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ h dl dr =>
      ⟨(cvPErase hG hB2 hι h).1.elim fun k => ⟨.symm _ _ _ _ k⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ h1 h2 dl dr =>
      ⟨(cvPErase hG hB2 hι h1).1.elim fun k1 =>
        (cvPErase hG hB2 hι h2).1.elim fun k2 => ⟨.trans _ _ _ _ _ k1 k2⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .beta _ _ _ A body arg B u hA hbody harg dl dr =>
      ⟨(tyPErase hG hB2 hι hA).elim fun kA =>
        (tyPErase hG hB2 hι hbody).elim fun kb =>
        (tyPErase hG hB2 hι harg).elim fun kg => ⟨.beta _ A body arg B u kA kb kg⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .zeta _ _ _ A value body B u hA hv hb dl dr =>
      ⟨(tyPErase hG hB2 hι hA).elim fun kA =>
        (tyPErase hG hB2 hι hv).elim fun kv =>
        (tyPErase hG hB2 hι hb).elim fun kb => ⟨.zeta _ A value body B u kA kv kb⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .zetaLocal _ _ _ i A v hval hty hv dl dr =>
      ⟨(tyPErase hG hB2 hι hv).elim fun kv =>
        ⟨.zetaLocal _ i A v hval hty kv⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .delta _ _ _ r ls m b hres hbody htr hlen hwf hb dl dr =>
      ⟨(tyPErase hG hB2 hι hb).elim fun kb =>
        ⟨.delta _ r ls m b hres hbody htr hlen hwf kb⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .iota _ _ _ lhs rhs T h hlhs hrhs dl dr =>
      ⟨(tyPErase hG hB2 hι hlhs).elim fun kl =>
        (tyPErase hG hB2 hι hrhs).elim fun kr => ⟨.iota _ lhs rhs T h kl kr⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .lit _ _ _ t exp T h hexp dl dr =>
      ⟨(tyPErase hG hB2 hι hexp).elim fun k => ⟨.lit _ t exp T h k⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .app _ _ _ f g a b A B h1 h2 dl dr =>
      ⟨(cvPErase hG hB2 hι h1).1.elim fun k1 =>
        (cvPErase hG hB2 hι h2).1.elim fun k2 => ⟨.app _ f g a b A B k1 k2⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .lam _ _ _ A A' b b' B u hA hb dl dr =>
      ⟨(cvPErase hG hB2 hι hA).1.elim fun kA =>
        (cvPErase hG hB2 hι hb).1.elim fun kb => ⟨.lam _ A A' b b' B u kA kb⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .pi _ _ _ A A' B B' u v hA hB dl dr =>
      ⟨(cvPErase hG hB2 hι hA).1.elim fun kA =>
        (cvPErase hG hB2 hι hB).1.elim fun kB => ⟨.pi _ A A' B B' u v kA kB⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .letE _ _ _ A A' v v' b b' B u hA hv hb dl dr =>
      ⟨(cvPErase hG hB2 hι hA).1.elim fun kA =>
        (cvPErase hG hB2 hι hv).1.elim fun kv =>
        (cvPErase hG hB2 hι hb).1.elim fun kb =>
          ⟨.letE _ A A' v v' b b' B u kA kv kb⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .sorts _ _ _ l₁ l₂ h dl dr =>
      ⟨⟨.sorts _ l₁ l₂ h⟩, tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .consts _ _ _ r ls ls' m hres hlen hwf hwf' h dl dr =>
      ⟨⟨.consts _ r ls ls' m hres hlen hwf hwf' h⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .eta _ _ _ f A B h dl dr =>
      ⟨(tyPErase hG hB2 hι h).elim fun k => ⟨.eta _ f A B k⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .irr _ _ _ P p q hP hp hq dl dr =>
      ⟨(tyPErase hG hB2 hι hP).elim fun kP =>
        (tyPErase hG hB2 hι hp).elim fun kp =>
        (tyPErase hG hB2 hι hq).elim fun kq => ⟨.irr _ P p q kP kp kq⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | _, _, _, _, _, _, .tyConv _ _ _ a b A A' u h hA dl dr =>
      ⟨(cvPErase hG hB2 hι h).1.elim fun k =>
        (cvPErase hG hB2 hι hA).1.elim fun kA => ⟨.tyConv _ a b A A' u k kA⟩,
        tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
  | E, _, _, _, _, _, .wk _ _ _ _ _ _ d c h =>
      ⟨(cvPErase hG hB2 hι h).1.elim fun kc =>
        ⟨convTWeaken d (hG E).1 (c := c) kc⟩,
        (cvPErase hG hB2 hι h).2.1.elim fun kl => ⟨hasTyTWeaken d (hG E).1 (c := c) kl⟩,
        (cvPErase hG hB2 hι h).2.2.elim fun kr => ⟨hasTyTWeaken d (hG E).1 (c := c) kr⟩⟩
  | E, _, _, _, _, _, .esub _ _ _ _ _ _ t v j _ h hget hv _ =>
      ⟨(cvPErase hG hB2 hι h).1.elim fun kc =>
        (tyPErase hG hB2 hι hv).elim fun kv =>
          ⟨convT_substS (hG E).1 (hG E).2.1 v t kc hget kv⟩,
        (cvPErase hG hB2 hι h).2.1.elim fun kl =>
        (tyPErase hG hB2 hι hv).elim fun kv =>
          ⟨hasTyT_substS (hG E).1 (hG E).2.1 v t kl hget kv⟩,
        (cvPErase hG hB2 hι h).2.2.elim fun kr =>
        (tyPErase hG hB2 hι hv).elim fun kv =>
          ⟨hasTyT_substS (hG E).1 (hG E).2.1 v t kr hget kv⟩⟩
  | E, _, _, _, _, _, .linst _ _ _ _ _ _ _ ls hls hlen h =>
      ⟨(cvPErase hG hB2 hι h).1.elim fun kc =>
        ⟨convT_instLevels (hG E).2.2.1 (hG E).2.2.2 hls hlen kc⟩,
        (cvPErase hG hB2 hι h).2.1.elim fun kl =>
          ⟨hasTyT_instLevels (hG E).2.2.1 (hG E).2.2.2 hls hlen kl⟩,
        (cvPErase hG hB2 hι h).2.2.elim fun kr =>
          ⟨hasTyT_instLevels (hG E).2.2.1 (hG E).2.2.2 hls hlen kr⟩⟩
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ hext h =>
      ⟨(cvPErase hG hB2 hι h).1.elim fun kc => convTEwk hι hext kc,
        (cvPErase hG hB2 hι h).2.1.elim fun kl => hasTyTEwk hι hext kl,
        (cvPErase hG hB2 hι h).2.2.elim fun kr => hasTyTEwk hι hext kr⟩
  | E, _, _, _, _, _, .cctx _ _ _ _ _ _ A A' _ h hA =>
      (cvPErase hG hB2 hι hA).1.elim fun kcA =>
      (cvPErase hG hB2 hι hA).2.1.elim fun klA =>
      (cvPErase hG hB2 hι hA).2.2.elim fun krA =>
        let hcc : CtxConvT E _ (.assumption A :: _) (.assumption A' :: _) :=
          .assumption (ctxConvT_refl _) klA krA kcA
        ⟨(cvPErase hG hB2 hι h).1.elim fun kc => ⟨convT_ctx (hG E).1 hcc kc⟩,
          (cvPErase hG hB2 hι h).2.1.elim fun kl => ⟨hasTyT_ctx (hG E).1 hcc kl⟩,
          (cvPErase hG hB2 hι h).2.2.elim fun kr => ⟨hasTyT_ctx (hG E).1 hcc kr⟩⟩
  | E, _, _, _, _, _, .fsub _ _ _ A B S a b _ hB hA hab dl dr => by
      obtain ⟨kB⟩ := tyPErase hG hB2 hι hB
      obtain ⟨kcv, kav, _⟩ := cvPErase hG hB2 hι hab
      obtain ⟨kav'⟩ := kav
      obtain ⟨kcv'⟩ := kcv
      refine ⟨?_, tyPErase hG hB2 hι dl, tyPErase hG hB2 hι dr⟩
      have h0 := convT_substCongr (hG E).1 (hG E).2.1 a b A (j := 0) kB (by simp)
        (by rw [lift_zero, lift_zero]; exact kav')
        (by rw [lift_zero, lift_zero, lift_zero]; exact kcv')
      simp only [lift_zero] at h0
      exact ⟨h0⟩

end
/-! ## §3 the reduction

`TyPEraseW` as consumed (CLW §B1, unchanged) follows from the three named
Props. No arm is dropped: 14/14 `TyP` constructors and 24/24 `CvP`
constructors are covered above. -/

/-- TyPEraseW modulo gates + the const congruence + the iota env residue. -/
theorem tyPEraseW_of (hG : TyPEraseGatesW) (hB2 : InstEqNCongrW)
    (hι : DerivedIotaEwkW) : TyPEraseW := by
  intro _ _ _ _ _ D; exact tyPErase hG hB2 hι D

/-- the CvP half, exposed at the same boundary triple. -/
theorem cvPEraseW_of (hG : TyPEraseGatesW) (hB2 : InstEqNCongrW)
    (hι : DerivedIotaEwkW) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CvP E n Γ a b T) :
    Nonempty (ConvT E n Γ a b T) := (cvPErase hG hB2 hι h).1

/-! ## §4 on-cone instances (Demand-reachable, inhabited)

The cone the rows consume is `E' := emptyEnv`-rooted derivations: every
gate fronts `EnvWfT.empty`, and `DerivedIotaEwkW` at source `emptyEnv` is
vacuous — an `IotaWitness` needs `E.members familyRef = some famMember`
(`hfam`), which `emptyEnv` cannot supply. -/

/-- all four gates at `emptyEnv` — the inhabited fragment of
    `TyPEraseGatesW` at the cone's canonical env. -/
theorem tyPEraseGates_empty :
    EnvClosed emptyEnv ∧ EnvMembersSubstStable emptyEnv ∧ EnvLevelsT emptyEnv ∧
      IotaLevelsT emptyEnv :=
  ⟨envClosed_of_envWfT EnvWfT.empty, envMembersSubstStable_of_envWfT EnvWfT.empty,
    envWfT_levels EnvWfT.empty, iotaLevelsT_of_envWfT EnvWfT.empty⟩

/-- `DerivedIotaEwkW` instantiated at source `emptyEnv`: vacuous, the
    witness's `hfam` resolves `none = some _`. -/
theorem derivedIotaEwk_empty {E : ResolvedEnv} (_hext : EnvExt emptyEnv E)
    {l r : Expr Nat} (h : DerivedIota emptyEnv l r) :
    Nonempty (DerivedIota E l r) := by
  cases h with | of w => exact Option.noConfusion w.hfam

/-- same vacuity at every memberless env (the gate conjunction too: all
    four gates are ∀-over-members/witnesses). -/
theorem tyPEraseGates_of_memberless (E : ResolvedEnv)
    (hE : ∀ r m, E.members r = some m → False) :
    EnvClosed E ∧ EnvMembersSubstStable E ∧ EnvLevelsT E ∧ IotaLevelsT E :=
  ⟨fun r m h => absurd h (hE r m), fun r m h => absurd h (hE r m),
    fun r m h => absurd h (hE r m),
    ⟨fun w => absurd w.hfam (hE _ _), fun w => absurd w.hfam (hE _ _)⟩⟩

#print axioms Rcic.Syn.TyPEraseGatesW
#print axioms Rcic.Syn.DerivedIotaEwkW
#print axioms Rcic.Syn.hasTyTEwk
#print axioms Rcic.Syn.convTEwk
#print axioms Rcic.Syn.tyPErase
#print axioms Rcic.Syn.cvPErase
#print axioms Rcic.Syn.tyPEraseW_of
#print axioms Rcic.Syn.cvPEraseW_of
#print axioms Rcic.Syn.tyPEraseGates_empty
#print axioms Rcic.Syn.derivedIotaEwk_empty
#print axioms Rcic.Syn.tyPEraseGates_of_memberless

end Rcic.Syn
