import rcic.RcicTypedValidity
import rcic.RcicTypedEnvEntry
import rcic.RcicTypedLevelsCongr
import rcic.RcicTypedSubstLet
import rcic.RcicParRedSRTyped
import rcic.RcicTypedGroupPins

namespace Rcic.Declarative

/-!
# DT-007 + DT-009 at `EnvWfT` — the two named debts discharged

`regularT_of_envWfT` / `DT009T_endpoints_of_envWfT` (RcicTypedValidity /
RcicTypedEnvEntry) front the typed regularity/endpoint packages by two
named debts: `SubstLetT` (dttyped lane) and `ConstsRightDataT` (tymig
lane). Both debts are now payable at `EnvWfT` alone:

* `SubstLetT` — #6329's `hasTyT_substLet0_of_envWfT` is the `j = 0` head
  form of the debt's own shape (arg-order wrap).
* `ConstsRightDataT` — `constsRightDataT_of_envWfT` below: the member's
  `const`-rule typing at `ls'` is retyped to `instantiateLevels ls
  m.mtype` by the conv-transport of #6330's `convT_instantiateLevels`
  (applied to `envWfT_mtypeSortTyped`'s `mtype` sort-typing, lists
  swapped), weakened `[] → Γ` by `convTLiftPrefix` with the member
  closedness collapsing the lifts.

With both fronts internal, DT-007 restates at `EnvWfT` with no `InScope`
(`DT007T_typing_regularity_of_envWfT`, the `Σ'`/`∃` re-packaging of
`regularT_of_envWfT` at the sealed row's shape) and DT-009 collapses to
`EnvWfT`-only (`DT009T_endpoints_envWfT`, all seven supplies
discharged). The sealed counterparts stay byte-untouched — these are
BESIDE them per the counterpart convention. `closure_claim = 0`.
-/

/-- `SubstLetT` discharged at `EnvWfT`: the named debt IS the `j = 0`
    letBinding head-substitution, #6329's L1 with the two premises
    swapped into the front's order. -/
def substLetT_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} :
    SubstLetT E n :=
  fun hv hb => hasTyT_substLet0_of_envWfT hW hb hv

/-- `ConstsRightDataT` discharged at `EnvWfT` — the tymig debt paid by
    `convT_instantiateLevels` (#6330): `m.mtype` is sort-typed at `[]`
    with bound `m.arity` (`envWfT_mtypeSortTyped`), so the level-list
    congruence (lists swapped: `ls'` left, `ls` right) produces
    `instLs' m.mtype ≡ instLs m.mtype` at the empty context;
    `convTLiftPrefix` carries it into `Γ` where the member closedness
    (`EnvClosed`, from `hW`) collapses every lift on `mtype`/`sort`.
    The `.const` rule at `ls'` plus `.conv` at `instLevel ls' u` lands
    the front's exact shape. -/
def constsRightDataT_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} :
    ConstsRightDataT E n :=
  fun {Γ} _hΓ {_ m ls ls'} hres hlen hwf hwf' heq => by
    have hcl := envClosed_of_envWfT hW
    obtain ⟨u, hmT⟩ := envWfT_mtypeSortTyped hW _ m hres
    have hlen' : ls'.length = m.arity :=
      (eqNList_length ls ls' heq).symm.trans hlen
    have hc0 : ConvT E n [] (instantiateLevels ls' m.mtype)
        (instantiateLevels ls m.mtype) (.sort (instLevel ls' u)) :=
      convT_instantiateLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW)
        (eqNList_symm heq) hwf' hwf hlen' hmT
    have hclm : lift 0 1 m.mtype = m.mtype := (hcl _ m hres).1 0
    have hcΓ : ConvT E n Γ (instantiateLevels ls' m.mtype)
        (instantiateLevels ls m.mtype) (.sort (instLevel ls' u)) := by
      have hw := convTLiftPrefix hcl Γ hc0
      simp only [List.append_nil, lift_instantiateLevels, lift] at hw
      rw [lift_of_closed _ hclm 0 Γ.length] at hw
      exact hw
    exact .conv Γ _ _ _ (instLevel ls' u)
      (.const Γ _ ls' m hres hlen' hwf') hcΓ

/-- DT-007 at `EnvWfT`: typing regularity with `InScope` dropped — the
    `regularT_of_envWfT` package with both named debts discharged,
    re-packaged at the sealed row's `∃ w, Nonempty` shape. -/
theorem DT007T_typing_regularity_of_envWfT {E : ResolvedEnv}
    (hW : EnvWfT E) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e T : Expr Nat} (h : HasTyT E n Γ e T) :
    ∃ w : Level, Nonempty (HasTyT E n Γ T (.sort w)) :=
  let ⟨w, hw⟩ := regularT_of_envWfT hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) hΓ h
  ⟨w, ⟨hw⟩⟩

/-- DT-009 at `EnvWfT`, unconditionally: all seven supplies discharged —
    five read off `endpoints3_of_envWfT`, zeta off the L1 debt, consts
    off the data front. -/
def DT009T_endpoints_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) :
    Nonempty (HasTyT E n Γ a T) ∧ Nonempty (HasTyT E n Γ b T) :=
  DT009T_endpoints_of_envWfT hW hΓ
    (convTEtaLeftT_of_envWfT hW (substLetT_of_envWfT hW)
      (constsRightDataT_of_envWfT hW))
    (convTAppRightT_of_envWfT hW (substLetT_of_envWfT hW)
      (constsRightDataT_of_envWfT hW))
    (convTLamRightT_of_envWfT hW (substLetT_of_envWfT hW)
      (constsRightDataT_of_envWfT hW))
    (convTPiRightT_of_envWfT hW (substLetT_of_envWfT hW)
      (constsRightDataT_of_envWfT hW))
    (convTLetRightT_of_envWfT hW (substLetT_of_envWfT hW)
      (constsRightDataT_of_envWfT hW))
    (convTZetaRightT_of_substLet (substLetT_of_envWfT hW))
    (convTConstsRightT_of_data (constsRightDataT_of_envWfT hW)) h

/-- S3 front-door alias (#6479, cc ruling): `convT_endpoints` IS
    `DT009T_endpoints_envWfT` — unconditional endpoint typing for `ConvT`
    at `EnvWfT`, all seven supplies discharged. -/
def convT_endpoints {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) :
    Nonempty (HasTyT E n Γ a T) ∧ Nonempty (HasTyT E n Γ b T) :=
  DT009T_endpoints_envWfT hW hΓ h

/-! ## pins — real fixtures only -/

/-- PIN (wiring tooth): `constsRightDataT_of_envWfT` directly, at
    `natEnvU`'s recursor member — `ls = [.zero]` vs
    `ls' = [.max .zero .zero]` differ literally, so the level-list
    congruence runs nontrivially. -/
def pin_constsRightDataT_natU :
    HasTyT natEnvU 1 [] (.const 3 [.max .zero .zero])
      (instantiateLevels [.zero] natRecMemberU.mtype) :=
  constsRightDataT_of_envWfT (n := 1) natEnvUWfT CtxWfT.nil
    (r := 3) (m := natRecMemberU) (ls := [.zero])
    (ls' := [.max .zero .zero]) rfl rfl rfl rfl ⟨fun _ => rfl, True.intro⟩

/-- PIN (DT-007): regularity at `natEnvU` — the recursor's instantiated
    type is sort-typed with no `InScope` premise. -/
theorem pin_DT007T_envWfT_natU :
    ∃ w : Level, Nonempty (HasTyT natEnvU 1 []
      (instantiateLevels [.zero] natRecMemberU.mtype) (.sort w)) :=
  DT007T_typing_regularity_of_envWfT natEnvUWfT CtxWfT.nil
    (.const [] 3 [.zero] natRecMemberU rfl rfl rfl)

/-- PIN (DT-009): the consts right endpoint at `natEnvU`, consumed
    through the unconditional wrapper — `const r ls'` typed at
    `instLs m.mtype` with `ls ≠ ls'` literally (the `hconst` path,
    i.e. this file's wiring). -/
theorem pin_DT009T_envWfT_natU :
    Nonempty (HasTyT natEnvU 1 [] (.const 3 [.max .zero .zero])
      (instantiateLevels [.zero] natRecMemberU.mtype)) :=
  (DT009T_endpoints_envWfT natEnvUWfT CtxWfT.nil
    (.consts [] 3 [.zero] [.max .zero .zero] natRecMemberU rfl rfl rfl rfl
      ⟨fun _ => rfl, True.intro⟩)).2

#print axioms Rcic.Declarative.substLetT_of_envWfT
#print axioms Rcic.Declarative.constsRightDataT_of_envWfT
#print axioms Rcic.Declarative.DT007T_typing_regularity_of_envWfT
#print axioms Rcic.Declarative.DT009T_endpoints_envWfT
#print axioms Rcic.Declarative.convT_endpoints
#print axioms Rcic.Declarative.pin_constsRightDataT_natU
#print axioms Rcic.Declarative.pin_DT007T_envWfT_natU
#print axioms Rcic.Declarative.pin_DT009T_envWfT_natU

end Rcic.Declarative
