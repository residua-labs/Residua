import rcic.RcicTypedLevels
import rcic.RcicTypedGroupPins

/-!
# R-TypedLevelsCongr — `convT_instantiateLevels` (DT-009 "fifth hole")

The typed, INDEXED analogue of `convInstantiateLevels`
(`RcicLevelCalc.lean:709`): the index-free `Conv` version recurses on the
term's structure because `Conv` carries no type. `ConvT`'s congruence
arms each FIX the index's shape — `app`'s index is `instantiate0 a B`
of the LEFT argument, `pi`'s is `sort (imax u v)`, `consts`'s is
`instantiateLevels ls m.mtype` — so structural recursion on `T` cannot
choose the index. This file recurses on the `HasTyT` derivation instead:
each of the nine rules pins its own index.

    HasTyT E a Γ T A  →
      ConvT E n (instLvlsCtx ls Γ) (instantiateLevels ls T)
        (instantiateLevels ls' T) (instantiateLevels ls A)

It is the THIRD member of `RcicTypedLevels`'s `Inst` family
(`hasTyT_instLevels`/`convT_instLevels`, same-list whole-derivation
maps), not a new mutual: the `conv` arm needs an index transport
`instLs A → instLs B`, which the premise-based recursion cannot supply —
`convT_instLevels` supplies it verbatim through `ConvT.tyConv`.

## Arm notes — one line per `HasTyT` rule

| arm | rule applied | index gap | closed by |
|-----|--------------|-----------|-----------|
| `sort`  | `ConvT.sorts`  | `sort (instL (succ l))` vs `sort (succ (instL l))` | `instLevel_succ` — an `rfl` defining equation |
| `bvar`  | `ConvT.refl` on `HasTyT.bvar` | none — `bvar` has no levels | `instLvlsCtx_lookupType` |
| `const` | `ConvT.consts` | `instLs (instLevels ms m.mtype)` vs `instLevels (ms.map instL) m.mtype` | `instLevels_mtype` (`instantiateLevels_compose`, `EnvLevelsT`-fronted); `instLevel_eqNList_map` for the pointwise `eqN`; `levelsBounded_inst` on both sides |
| `pi`    | `ConvT.pi`     | `sort (instL (imax u v))` vs `sort (imax (instL u) (instL v))` | `instLevel_imax` — `rfl` |
| `lam`   | `ConvT.lam`    | none | `instLvlsDecl` distributes over `.assumption` definitionally; index `instLs (pi A B)` is `rfl` |
| `app`   | `ConvT.app`    | `instLs (inst0 a B)` vs `inst0 (instLs a) (instLs B)` | `instantiateLevels_instantiate0` |
| `letE`  | `ConvT.letE`   | same `inst0` gap | same lemma; `instLvlsDecl` over `.letBinding` |
| `lit`   | `ConvT.refl` on `HasTyT.lit` | none — `instLs (lit t) = lit t` | `hasTyT_instLevels` + `instantiateLevels_natExpand` |
| `conv`  | `ConvT.tyConv` | index `instLs A → instLs B` | `convT_instLevels` on the `ConvT` premise |

## The index-shape design

`ConvT.refl` cannot relate `instLs T` to `instLs' T` (the two lists
differ pointwise by `eqN`, not `=`). Each arm therefore applies its
congruence rule and closes the index gap by, in order: (a) `rfl` level
algebra — `instLevel`'s defining equations are `rfl`, so `sort`-shaped
gaps collapse; (b) sealed commutation lemmas —
`instantiateLevels_instantiate0`, `instLevels_mtype`; (c) `.tyConv`
index transport fed by `convT_instLevels` — only `.conv` needs it, and
its premise is a `ConvT`, not a `HasTyT`, so no structural IH exists
there anyway. No `.symm` is needed anywhere: a consumer wanting the
opposite direction instantiates with `ls`, `ls'` swapped.

Fronts are the `Inst` family's own: `EnvLevelsT`/`IotaLevelsT`
(discharged at `EnvWfT` by `envWfT_levels`/`iotaLevelsT_of_envWfT`),
`levelsBounded n` on both lists, `ls.length = a` on the left
(`ls'.length = a` follows inside by `eqNList_length`). All syntactic —
no injectivity rows, no `InScope`, no Loop.

## Pins

`natEnvU`'s recursor (`natRecMemberU`, arity 1) carries the `const`
arm: `[.param 0]` instantiated at `[.zero]` vs `[.max .zero .zero]`
(eqN-nontrivial — the two `const`s differ literally in their level
argument). A `sort`/`pi` pin at arity 1 over `emptyEnv` exercises the
`rfl` index collapses.
-/

namespace Rcic.Declarative

/-- THE FIFTH HOLE: `instantiateLevels` congruence on the typed judgment,
    two pointwise-`eqN` level lists. Structural recursion on the `HasTyT`
    derivation (`termination_by sizeOf h`, the `Inst` convention). -/
def convT_instantiateLevels (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    {a n : Nat} {ls ls' : List Level} (heq : eqNList ls ls')
    (hls : levelsBounded n ls = true) (hls' : levelsBounded n ls' = true)
    (hlen : ls.length = a) :
    {Γ : LCtx} → {T A : Expr Nat} → HasTyT E a Γ T A →
    ConvT E n (instLvlsCtx ls Γ) (instantiateLevels ls T)
      (instantiateLevels ls' T) (instantiateLevels ls A)
  | _, _, _, .sort Γ l =>
      .sorts _ _ _ (instLevel_eqNList heq l)
  | _, _, _, .bvar Γ i A h =>
      .refl _ _ _ (.bvar _ i _ (instLvlsCtx_lookupType h))
  | _, _, _, .const Γ r ms m hres hlen' hwf => by
      have hlen'' : ls'.length = a := by
        rw [← hlen]; exact (eqNList_length _ _ heq).symm
      show ConvT E n (instLvlsCtx ls Γ)
        (.const r (ms.map (instLevel ls))) (.const r (ms.map (instLevel ls')))
        (instantiateLevels ls (instantiateLevels ms m.mtype))
      rw [instLevels_mtype hEL hres hlen' ls]
      exact .consts _ r _ _ m hres (length_map_arity hlen' _)
        (levelsBounded_inst hls hlen hwf)
        (levelsBounded_inst hls' hlen'' hwf)
        (instLevel_eqNList_map heq ms)
  | _, _, _, .pi Γ A u B v hA hB =>
      .pi _ _ _ _ _ (instLevel ls u) (instLevel ls v)
        (convT_instantiateLevels hEL hIL heq hls hls' hlen hA)
        (convT_instantiateLevels hEL hIL heq hls hls' hlen hB)
  | _, _, _, .lam Γ A u body B hA hbody =>
      .lam _ _ _ _ _ (instantiateLevels ls B) (instLevel ls u)
        (convT_instantiateLevels hEL hIL heq hls hls' hlen hA)
        (convT_instantiateLevels hEL hIL heq hls hls' hlen hbody)
  | _, _, _, .app Γ f a A B hf ha => by
      show ConvT E n (instLvlsCtx ls Γ)
        (.app (instantiateLevels ls f) (instantiateLevels ls a))
        (.app (instantiateLevels ls' f) (instantiateLevels ls' a))
        (instantiateLevels ls (instantiate0 a B))
      rw [instantiateLevels_instantiate0]
      exact .app _ _ _ _ _ _ _
        (convT_instantiateLevels hEL hIL heq hls hls' hlen hf)
        (convT_instantiateLevels hEL hIL heq hls hls' hlen ha)
  | _, _, _, .letE Γ A u value B body hA hv hb => by
      show ConvT E n (instLvlsCtx ls Γ)
        (.letE (instantiateLevels ls A) (instantiateLevels ls value)
          (instantiateLevels ls body))
        (.letE (instantiateLevels ls' A) (instantiateLevels ls' value)
          (instantiateLevels ls' body))
        (instantiateLevels ls (instantiate0 value B))
      rw [instantiateLevels_instantiate0]
      exact .letE _ _ _ _ _ _ _ (instantiateLevels ls B) (instLevel ls u)
        (convT_instantiateLevels hEL hIL heq hls hls' hlen hA)
        (convT_instantiateLevels hEL hIL heq hls hls' hlen hv)
        (convT_instantiateLevels hEL hIL heq hls hls' hlen hb)
  | _, _, _, .lit Γ t T hexp => by
      have h' := hasTyT_instLevels hEL hIL hls hlen hexp
      rw [instantiateLevels_natExpand] at h'
      exact .refl _ _ _ (.lit _ t _ h')
  | _, _, _, .conv Γ e A B u h hc =>
      .tyConv _ _ _ _ _ (instLevel ls u)
        (convT_instantiateLevels hEL hIL heq hls hls' hlen h)
        (convT_instLevels hEL hIL hls hlen hc)
termination_by _ _ _ h => sizeOf h
decreasing_by all_goals (simp; try omega)

/-! ## Pins: `emptyEnv` for the `rfl` arms, `natEnvU` for `const` -/

/-- arity-1 `sort` pin over `emptyEnv`: `[.param 0]` at `[.zero]` vs
    `[.zero]` (refl `eqNList`). Exercises the `instLevel_succ` collapse. -/
def pin_convTinstLevels_sort :
    ConvT emptyEnv 0 []
      (instantiateLevels [.zero] (.sort (.param 0)))
      (instantiateLevels [.zero] (.sort (.param 0)))
      (instantiateLevels [.zero] (.sort (.succ (.param 0)))) :=
  convT_instantiateLevels (a := 1) (n := 0) (ls := [.zero]) (ls' := [.zero])
    (envWfT_levels .empty) (iotaLevelsT_of_envWfT .empty)
    (⟨fun _ => rfl, True.intro⟩ : eqNList [.zero] [.zero]) rfl rfl rfl
    (.sort [] (.param 0))

/-- arity-1 `pi` pin over `emptyEnv`: `.pi (.sort (.param 0)) (.sort .zero)`
    at `[.zero]` vs `[.max .zero .zero]` (eqN-nontrivial). The `imax` index
    collapses by `instLevel_imax`. -/
def pin_convTinstLevels_pi :
    ConvT emptyEnv 0 []
      (instantiateLevels [.zero] (.pi (.sort (.param 0)) (.sort .zero)))
      (instantiateLevels [.max .zero .zero] (.pi (.sort (.param 0)) (.sort .zero)))
      (instantiateLevels [.zero]
        (.sort (.imax (.succ (.param 0)) (.succ .zero)))) :=
  convT_instantiateLevels (a := 1) (n := 0) (ls := [.zero]) (ls' := [.max .zero .zero])
    (envWfT_levels .empty) (iotaLevelsT_of_envWfT .empty)
    (⟨fun _ => rfl, True.intro⟩ : eqNList [.zero] [.max .zero .zero]) rfl rfl rfl
    (.pi [] _ (.succ (.param 0)) _ (.succ .zero)
      (.sort [] (.param 0)) (.sort _ .zero))

/-- the `const` arm at a REAL member: `natRecMemberU` (arity 1) in
    `natEnvU`, `[.param 0]` instantiated at `[.zero]` vs
    `[.max .zero .zero]` — the two `const`s differ literally. -/
def pin_convTinstLevels_const :
    ConvT natEnvU 0 []
      (.const 3 [.zero]) (.const 3 [.max .zero .zero])
      (instantiateLevels [.zero] natRecMemberU.mtype) :=
  convT_instantiateLevels (a := 1) (n := 0) (ls := [.zero]) (ls' := [.max .zero .zero])
    (envWfT_levels natEnvUWfT)
    (iotaLevelsT_of_envWfT natEnvUWfT)
    (⟨fun _ => rfl, True.intro⟩ : eqNList [.zero] [.max .zero .zero]) rfl rfl rfl
    (.const [] 3 [.param 0] natRecMemberU rfl rfl rfl)

#print axioms Rcic.Declarative.convT_instantiateLevels
#print axioms Rcic.Declarative.pin_convTinstLevels_sort
#print axioms Rcic.Declarative.pin_convTinstLevels_pi
#print axioms Rcic.Declarative.pin_convTinstLevels_const

end Rcic.Declarative
