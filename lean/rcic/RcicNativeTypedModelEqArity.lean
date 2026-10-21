import rcic.RcicNativeTypedModelCovRelEqGap
import rcic.RcicPiRowSaturation

/-!
# The Eq-gap arity port at named conversion rows

Every `EqGapTypedCtorArity` consumer in
`RcicNativeTypedModelCovRelEqGap` bottoms out at this boundary. Its proof
is a three-way spine analysis against `eqReflT.mtype`'s two-Π telescope:
`hasTyT_spineInv_rows` peels stored domains, which needs Π-injectivity
of `TyConvT` (`PiRowField`); the under- and over-application arms then
close by shape disjointness between `.pi` and `const 63`-headed family
applications, in both directions.

Neither ingredient is dischargeable at `eqEnvT` on the landed routes:
`GroupInScopeT`/`InScope` is uninhabitable — `GroupProfileT` forces a
`.propOnly` eliminator on an indexed Prop-family, while
`eqRecAdm.policy = .anySort`; the `AllBelowScoped`/`tableOf` simulation
is refuted at retained-ι environments
(`natSucc_not_allBelowScoped_tableOf` at `natEnvU`, the same shape);
and every `ShallowTypeSoundness*`/`FundamentalLR*` variant is the
fundamental lemma itself, the supplier whose boundary is being mapped
here.  They therefore stand as named premises — `EqGapArityRows` — not
fabricated instances.  The two converse theorems show the premises are
tight: a shape failure at a realizable witness gives an actual typed
wrong-arity substitution that refutes the port.

All landed definitions and observations are unchanged. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelEqArityAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelKAudit TypedModelKFailureAudit
open TypedModelKControlAudit TypedModelKTypedBetaAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2InputsAudit ReadbackCK2GapAudit
open PiProbeRelIotaAudit

/-! ## the arity port at named conversion rows

Every supplier above bottoms out at `EqGapTypedCtorArity`.  Its proof is
a three-way spine analysis against `eqReflT.mtype`'s two-Π telescope:
`hasTyT_spineInv_rows` peels stored domains, which needs Π-injectivity
of `TyConvT` (`PiRowField`); the under- and over-application arms then
close by shape disjointness between `.pi` and `const 63`-headed family
applications, in both directions.

Neither ingredient is dischargeable at `eqEnvT` on the landed routes:
`GroupInScopeT`/`InScope` is uninhabitable — `GroupProfileT` forces a
`.propOnly` eliminator on an indexed Prop-family, while
`eqRecAdm.policy = .anySort`; the `AllBelowScoped`/`tableOf` simulation
is refuted at retained-ι environments
(`natSucc_not_allBelowScoped_tableOf` at `natEnvU`, the same shape);
and every `ShallowTypeSoundness*`/`FundamentalLR*` variant is the
fundamental lemma itself, the supplier whose boundary is being mapped
here.  They therefore stand as named premises — `EqGapArityRows` — not
fabricated instances.  The two converse theorems show the premises are
tight: a shape failure at a realizable witness gives an actual typed
wrong-arity substitution that refutes the port. -/

/-- The conversion rows the Eq-gap arity proof consumes: Π-injectivity
    for telescope inversion, plus both directions of `.pi`↔`const 63`
    shape disjointness under `TyConvT`. -/
structure EqGapArityRows (n : Nat) : Prop where
  /-- `TyConvT` is injective at `.pi` in both components. -/
  piRow : PiRowField eqEnvT n
  /-- No sort-indexed conversion chain joins a `.pi` to a family application. -/
  pi_famApp : ∀ {Γ : LCtx}, CtxWfT eqEnvT n Γ → ∀ {A B : Expr Nat}
    {ls : List Level} {ys : List (Expr Nat)},
    ¬ Nonempty (TyConvT eqEnvT n Γ (.pi A B) (foldApps (.const 63 ls) ys))
  /-- No sort-indexed conversion chain joins a family application to a `.pi`. -/
  famApp_pi : ∀ {Γ : LCtx}, CtxWfT eqEnvT n Γ → ∀ {A B : Expr Nat}
    {ls : List Level} {ys : List (Expr Nat)},
    ¬ Nonempty (TyConvT eqEnvT n Γ (foldApps (.const 63 ls) ys) (.pi A B))

/-- The stored `Eq.refl` type's outer domain, for the `policyPi`
    decomposition below. -/
private def eqReflDom0 : Expr Nat := .sort (.succ .zero)

/-- The stored `Eq.refl` type's inner domain (`α` under the first binder). -/
private def eqReflDom1 : Expr Nat := .bvar 0

/-- The stored `Eq.refl` result `Eq α a a` under both binders. -/
private def eqReflResult : Expr Nat :=
  foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 0]

/-- `instantiateLevels` is the identity on the parameter-free `Eq.refl` type. -/
private theorem instantiateLevels_eqReflT (us : List Level) :
    instantiateLevels us eqReflT.mtype =
      policyPi [eqReflDom0, eqReflDom1] eqReflResult := rfl

/-- The arity port under the named rows.  Under-application leaves a `.pi`
    residual convertible to the family target; over-application retypes the
    saturated `Eq α a a` result at a `.pi`.  The exact two-argument arm
    passes unchanged. -/
theorem eqGapTypedCtorArity_of_rows (hR : EqGapArityRows n) :
    EqGapTypedCtorArity n := by
  intro Δ σ hΔ hT hc
  obtain ⟨_, _, ⟨h0⟩⟩ := eqGap_typedSubst_data hT
  obtain ⟨us, args, he⟩ := (isCtorSpine_eq_iff (σ 0)).mp hc
  have hsp : (appsSpine (σ 0)).2.length = args.length := by
    rw [he, appsSpine_foldApps_const]
  rw [hsp]
  rw [he] at h0
  rcases Nat.lt_trichotomy args.length 2 with hlt | heq | hgt
  · -- under-application: `args` is `[]` or `[x]`; the residual is a `.pi`
    exfalso
    match args, hlt with
    | [], _ =>
        simp only [foldApps] at h0
        obtain ⟨m', hres', _, _, hcv⟩ := hasTyTInv_const h0 rfl
        have hmem : eqEnvT.members 64 = some eqReflT := by simp [eqEnvT_mem]
        have hmeq : m' = eqReflT := Option.some.inj (hres'.symm.trans hmem)
        subst hmeq
        rw [show instantiateLevels us eqReflT.mtype =
            .pi eqReflDom0 (.pi eqReflDom1 eqReflResult) from
          instantiateLevels_eqReflT us] at hcv
        exact hR.pi_famApp hΔ
          (ls := []) (ys := [σ 2, σ 1, gapBetaIndex (σ 2) (σ 1)]) ⟨hcv⟩
    | [x], _ =>
        have hpi : instantiateLevels us eqReflT.mtype =
            policyPi [eqReflDom0] (.pi eqReflDom1 eqReflResult) :=
          instantiateLevels_eqReflT us
        obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows pinEqGroupWfT hR.piRow
          hΔ (r := 64) (m := eqReflT) (by simp [eqEnvT_mem]) hpi [x] rfl h0
        rw [instPrefix_pi] at hconv
        exact hR.pi_famApp hΔ
          (ls := []) (ys := [σ 2, σ 1, gapBetaIndex (σ 2) (σ 1)]) ⟨hconv⟩
    | _ :: _ :: _ :: _, h => simp only [List.length_cons] at h; omega
  · exact heq
  · -- over-application: the two-argument prefix is typed, at a Π
    exfalso
    obtain ⟨x, y, z, rest, rfl⟩ : ∃ x y z rest,
        args = x :: y :: z :: rest := by
      match args, hgt with
      | [], h => simp at h
      | [_], h => simp at h
      | [_, _], h => simp at h
      | x :: y :: z :: rest, _ => exact ⟨x, y, z, rest, rfl⟩
    have hsplit : foldApps (.const 64 us) (x :: y :: z :: rest) =
        foldApps (foldApps (.const 64 us) [x, y]) (z :: rest) := by
      rw [show x :: y :: z :: rest = [x, y] ++ z :: rest from rfl,
        foldApps_append]
    obtain ⟨A, B, ⟨hf⟩⟩ := Rcic.Syn.hasTyT_foldApps_prefix_pi
      (f := foldApps (.const 64 us) [x, y]) (hsplit ▸ h0) rfl
    have hpi : instantiateLevels us eqReflT.mtype =
        policyPi [eqReflDom0, eqReflDom1] eqReflResult :=
      instantiateLevels_eqReflT us
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows pinEqGroupWfT hR.piRow
      hΔ (r := 64) (m := eqReflT) (by simp [eqEnvT_mem]) hpi [x, y] rfl hf
    have hinst : instPrefix [x, y] eqReflResult =
        foldApps (.const 63 []) [x, y, y] := by
      simp [instPrefix, instantiate0, instantiate, eqReflResult, foldApps,
        instantiate_lift_id, lift_zero]
    rw [hinst] at hconv
    exact hR.famApp_pi hΔ (ls := []) (ys := [x, y, y]) ⟨hconv⟩

/-- A `.pi` residual collapsing to the Eq target refutes the arity port:
    the one-argument constructor spine `Eq.refl A` is then a typed
    substitution into `eqGapCtx`, of length one.  The premise is exactly
    the under-application shape `pi_famApp` forbids. -/
theorem not_eqGapTypedCtorArity_of_pi_famApp
    (hΔ : CtxWfT eqEnvT n Δ) {A' a' : Expr Nat}
    (hA : Nonempty (HasTyT eqEnvT n Δ A' (.sort (.succ .zero))))
    (ha : Nonempty (HasTyT eqEnvT n Δ a' A'))
    (h : Nonempty (TyConvT eqEnvT n Δ
      (.pi A' (foldApps (.const 63 []) [lift 0 1 A', .bvar 0, .bvar 0]))
      (foldApps (.const 63 []) [A', a', gapBetaIndex A' a']))) :
    ¬ EqGapTypedCtorArity n := by
  intro hAr
  obtain ⟨hA⟩ := hA
  obtain ⟨ha⟩ := ha
  obtain ⟨h⟩ := h
  let σ : SubstT := SubstT.cons (.app (.const 64 []) A')
    (SubstT.cons a' (SubstT.cons A' SubstT.id))
  have hσ0 : HasTyT eqEnvT n Δ (.app (.const 64 []) A')
      (.pi A' (foldApps (.const 63 []) [lift 0 1 A', .bvar 0, .bvar 0])) := by
    have hc64 : HasTyT eqEnvT n Δ (.const 64 [])
        (instantiateLevels [] eqReflT.mtype) :=
      .const Δ _ _ eqReflT rfl rfl rfl
    have happ : HasTyT eqEnvT n Δ (.app (.const 64 []) A')
        (instantiate0 A' (.pi (.bvar 0) eqReflResult)) := by
      rw [show instantiateLevels [] eqReflT.mtype =
          .pi eqReflDom0 (.pi eqReflDom1 eqReflResult) from
        instantiateLevels_eqReflT []] at hc64
      exact .app Δ _ _ _ _ hc64 hA
    have heq : instantiate0 A' (.pi (.bvar 0) eqReflResult) =
        .pi A' (foldApps (.const 63 []) [lift 0 1 A', .bvar 0, .bvar 0]) := by
      simp (config := { decide := true }) only
        [instantiate0, instantiate, eqReflResult, foldApps,
         ite_true, ite_false]
    rw [heq] at happ
    exact happ
  have hσ0' : HasTyT eqEnvT n Δ (.app (.const 64 []) A')
      (foldApps (.const 63 []) [A', a', gapBetaIndex A' a']) :=
    hasTyT_of_tyConv hσ0 h
  have hT : TypedSubstT eqEnvT n Δ σ eqGapCtx := by
    constructor
    · intro i A hi
      cases i with
      | zero =>
          have hA' : A = foldApps (.const 63 [])
              [.bvar 2, .bvar 1, gapBetaIndex (.bvar 2) (.bvar 1)] :=
            (Option.some.inj hi).symm
          subst A
          exact ⟨hσ0'⟩
      | succ i =>
          cases i with
          | zero =>
              have hA' : A = .bvar 2 := (Option.some.inj hi).symm
              subst A
              exact ⟨ha⟩
          | succ i =>
              cases i with
              | zero =>
                  have hA' : A = .sort (.succ .zero) := (Option.some.inj hi).symm
                  subst A
                  exact ⟨hA⟩
              | succ i => simp [eqGapCtx, lookupType] at hi
    · intro i v hv
      rw [lookupValue_eqGapCtx_none] at hv
      exact Option.noConfusion hv
  have hc' : IsCtorSpine eqEnvT (σ 0) :=
    (isCtorSpine_eq_iff (σ 0)).mpr ⟨[], [A'], rfl⟩
  have hlen := hAr hΔ hT hc'
  have hsp : (appsSpine (σ 0)).2 = [A'] := by
    show (appsSpine (foldApps (.const 64 []) [A'])).2 = [A']
    rw [appsSpine_foldApps_const]
  rw [hsp] at hlen
  simp at hlen

/-- A saturated `Eq α a a` collapsing to a `.pi` whose instantiated codomain
    is the Eq target refutes the arity port: the three-argument constructor
    spine `Eq.refl A a z` is then a typed substitution, of length three.
    The premise is exactly the over-application shape `famApp_pi` forbids. -/
theorem not_eqGapTypedCtorArity_of_famApp_pi
    (hΔ : CtxWfT eqEnvT n Δ) {A' a' z : Expr Nat} {X Y : Expr Nat}
    (hA : Nonempty (HasTyT eqEnvT n Δ A' (.sort (.succ .zero))))
    (ha : Nonempty (HasTyT eqEnvT n Δ a' A'))
    (hz : Nonempty (HasTyT eqEnvT n Δ z X))
    (h : Nonempty (TyConvT eqEnvT n Δ
      (foldApps (.const 63 []) [A', a', a']) (.pi X Y)))
    (hY : instantiate0 z Y =
      foldApps (.const 63 []) [A', a', gapBetaIndex A' a']) :
    ¬ EqGapTypedCtorArity n := by
  intro hAr
  obtain ⟨hA⟩ := hA
  obtain ⟨ha⟩ := ha
  obtain ⟨hz⟩ := hz
  obtain ⟨h⟩ := h
  let σ : SubstT := SubstT.cons (foldApps (.const 64 []) [A', a', z])
    (SubstT.cons a' (SubstT.cons A' SubstT.id))
  have hσ01 : HasTyT eqEnvT n Δ (foldApps (.const 64 []) [A', a'])
      (foldApps (.const 63 []) [A', a', a']) := by
    have hc64 : HasTyT eqEnvT n Δ (.const 64 [])
        (instantiateLevels [] eqReflT.mtype) :=
      .const Δ _ _ eqReflT rfl rfl rfl
    rw [show instantiateLevels [] eqReflT.mtype =
        .pi eqReflDom0 (.pi eqReflDom1 eqReflResult) from
      instantiateLevels_eqReflT []] at hc64
    have happ1 : HasTyT eqEnvT n Δ (.app (.const 64 []) A')
        (instantiate0 A' (.pi (.bvar 0) eqReflResult)) :=
      .app Δ _ _ _ _ hc64 hA
    have happ2 : HasTyT eqEnvT n Δ
        (.app (.app (.const 64 []) A') a')
        (instantiate0 a' (instantiate 1 (lift 0 1 A') eqReflResult)) :=
      .app Δ _ _ _ _ happ1 ha
    have heq : instantiate0 a' (instantiate 1 (lift 0 1 A') eqReflResult) =
        foldApps (.const 63 []) [A', a', a'] := by
      simp (config := { decide := true }) only
        [instantiate0, instantiate, eqReflResult, foldApps,
         instantiate_lift_id, ite_true, ite_false]
    rw [heq] at happ2
    exact happ2
  have hσ0 : HasTyT eqEnvT n Δ
      (foldApps (.const 64 []) [A', a', z])
      (foldApps (.const 63 []) [A', a', gapBetaIndex A' a']) := by
    have hpi' : HasTyT eqEnvT n Δ (foldApps (.const 64 []) [A', a'])
        (.pi X Y) := hasTyT_of_tyConv hσ01 h
    have happ := HasTyT.app Δ _ _ _ _ hpi' hz
    rw [hY] at happ
    exact happ
  have hT : TypedSubstT eqEnvT n Δ σ eqGapCtx := by
    constructor
    · intro i A hi
      cases i with
      | zero =>
          have hA' : A = foldApps (.const 63 [])
              [.bvar 2, .bvar 1, gapBetaIndex (.bvar 2) (.bvar 1)] :=
            (Option.some.inj hi).symm
          subst A
          exact ⟨hσ0⟩
      | succ i =>
          cases i with
          | zero =>
              have hA' : A = .bvar 2 := (Option.some.inj hi).symm
              subst A
              exact ⟨ha⟩
          | succ i =>
              cases i with
              | zero =>
                  have hA' : A = .sort (.succ .zero) := (Option.some.inj hi).symm
                  subst A
                  exact ⟨hA⟩
              | succ i => simp [eqGapCtx, lookupType] at hi
    · intro i v hv
      rw [lookupValue_eqGapCtx_none] at hv
      exact Option.noConfusion hv
  have hc' : IsCtorSpine eqEnvT (σ 0) :=
    (isCtorSpine_eq_iff (σ 0)).mpr ⟨[], [A', a', z], rfl⟩
  have hlen := hAr hΔ hT hc'
  have hsp : (appsSpine (σ 0)).2 = [A', a', z] := by
    show (appsSpine (foldApps (.const 64 []) [A', a', z])).2 = [A', a', z]
    rw [appsSpine_foldApps_const]
  rw [hsp] at hlen
  simp at hlen

-- BEGIN RCIC_NATIVE_TYPED_MODEL_EQ_ARITY_ROOTS
#print axioms EqGapArityRows
#print axioms eqGapTypedCtorArity_of_rows
#print axioms not_eqGapTypedCtorArity_of_pi_famApp
#print axioms not_eqGapTypedCtorArity_of_famApp_pi
-- END RCIC_NATIVE_TYPED_MODEL_EQ_ARITY_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelEqArityAudit
