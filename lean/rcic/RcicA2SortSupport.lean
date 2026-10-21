import Lean
import rcic.RcicEtaKPeakPins
import rcic.RcicDT0709EnvWf
import rcic.RcicDTMetaTypedSR
import rcic.RcicTypedInvert

/-!
A-2, conditional sorting support.
Base: bc734a23c6cb317a40b9ddc988f4fbf21efac61e.
Native-checked continuation; exact commands and source hashes are in
research/rcic/irr-postponement/F8_A2_SORT_NATIVE_VALIDATION_2026_10_14.txt.
The only new logical premise is SortUnique, always an explicit argument.
No unrestricted type-uniqueness, piRow, PEqT transitivity, or new reduction rule.
All uses of Nonempty elimination end in Prop. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxRecDepth 16384

namespace Rcic.Declarative.F8A2Support

/-- Precisely the sort-uniqueness interface requested from the sortRow lane. -/
def SortUnique (E : ResolvedEnv) (n : Nat) : Prop :=
  EnvWfT E → ∀ {Γ : LCtx} {T : Expr Nat} {u v : Level},
    CtxWfT E n Γ → HasTyT E n Γ T (.sort u) →
    HasTyT E n Γ T (.sort v) → eqN u v

/-- An actual proof typing, not a classification assigned to the outer index. -/
def IsProof (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) : Prop :=
  ∃ P : Expr Nat, Nonempty (HasTyT E n Γ P (.sort .zero)) ∧
    Nonempty (HasTyT E n Γ e P)

theorem succ_eqN_injective {u v : Level} (h : eqN (.succ u) (.succ v)) :
    eqN u v := by
  intro ρ
  have hh := h ρ
  cases hu : eval ρ u <;> cases hv : eval ρ v <;> simp_all [eval]

theorem imax_eqN_zero_right {u v : Level} (h : eqN (.imax u v) .zero) :
    eqN v .zero := by
  intro ρ
  have hh := h ρ
  cases hv : eval ρ v with
  | none => simp [eval, hv] at hh
  | some k =>
      by_cases hk : k = 0
      · simp [eval, hv, hk]
      · cases hu : eval ρ u with
        | none => simp [eval, hv, hk, hu] at hh
        | some j =>
            have hm : max j k = 0 := by simpa [eval, hv, hk, hu] using hh
            have hz : k = 0 := by omega
            exact False.elim (hk hz)

theorem eqNList_trans_local : {xs ys zs : List Level} →
    eqNList xs ys → eqNList ys zs → eqNList xs zs
  | [], [], [], _, _ => True.intro
  | [], [], _ :: _, _, h => False.elim h
  | [], _ :: _, _, h, _ => False.elim h
  | _ :: _, [], _, h, _ => False.elim h
  | _ :: _, _ :: _, [], _, h => False.elim h
  | x :: xs, y :: ys, z :: zs, h, k =>
      ⟨fun ρ => (h.1 ρ).trans (k.1 ρ), eqNList_trans_local h.2 k.2⟩

section Generic
variable {E : ResolvedEnv} {n : Nat}

/-- Fixed-sort transport ALONG a type chain. This is not the ordinary
term retyping function: endpoint sorts are aligned by the explicit SU premise. -/
theorem sort_transport (su : SortUnique E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A B : Expr Nat} → TyConvT E n Γ A B → {u : Level} →
    HasTyT E n Γ A (.sort u) → Nonempty (HasTyT E n Γ B (.sort u))
  | _, _, .refl _ _, _, hA => ⟨hA⟩
  | A, B, .of _ _ _ v hc, u, hA => by
      obtain ⟨⟨hAv⟩, ⟨hBv⟩⟩ := convT_endpoints hW hΓ hc
      have hvu : eqN v u := fun ρ => (su hW hΓ hA hAv ρ).symm
      exact ⟨.conv Γ B (.sort v) (.sort u) (.succ v) hBv
        (.sorts Γ v u hvu)⟩
  | _, _, .trans _ _ _ _ c₁ c₂, _, hA => by
      obtain ⟨hB⟩ := sort_transport su hW hΓ c₁ hA
      exact sort_transport su hW hΓ c₂ hB

/-- A sort-to-sort chain can be read using SU and endpoint transport;
no separate sortRow or piRow premise is silently imported. -/
theorem sort_chain_eq (su : SortUnique E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level}
    (c : TyConvT E n Γ (.sort u) (.sort v)) : eqN u v := by
  obtain ⟨hv⟩ := sort_transport su hW hΓ c (HasTyT.sort Γ u)
  exact succ_eqN_injective (su hW hΓ hv (HasTyT.sort Γ v))

/-- Sorting a Pi in Prop forces its actual codomain to be sorted in Prop.
The domain's sort evidence is returned so the binder context is certified. -/
theorem pi_zero_inv (su : SortUnique E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat}
    (hpi : HasTyT E n Γ (.pi A B) (.sort .zero)) :
    ∃ u : Level, Nonempty (HasTyT E n Γ A (.sort u)) ∧
      Nonempty (HasTyT E n (.assumption A :: Γ) B (.sort .zero)) := by
  obtain ⟨u, v, hA, hB, c⟩ := hasTyTInv_pi hpi rfl
  have hv0 := imax_eqN_zero_right (sort_chain_eq su hW hΓ c)
  exact ⟨u, ⟨hA⟩, ⟨.conv _ B (.sort v) (.sort .zero) (.succ v) hB
    (.sorts _ v .zero hv0)⟩⟩

/-- Proofhood propagates backwards through the FUNCTION of an application.
This is the prefix obligation: it cannot be replaced by an assertion that
internal proof roots never change a whole expression's head. -/
theorem proof_app_function (su : SortUnique E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f a : Expr Nat}
    (h : IsProof E n Γ (.app f a)) : IsProof E n Γ f := by
  obtain ⟨P, ⟨hP⟩, ⟨hfa⟩⟩ := h
  obtain ⟨A, B, hf, ha, c⟩ := hasTyTInv_app hfa rfl
  obtain ⟨w, ⟨hpi⟩⟩ := DT007T_typing_regularity_of_envWfT hW hΓ hf
  obtain ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hpi rfl
  obtain ⟨hBi0⟩ := sort_transport su hW hΓ c.symmT hP
  have hBiv := hasTyT_subst0S (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) hB ha
  have hv0 := su hW hΓ hBiv hBi0
  have hB0 : HasTyT E n (.assumption A :: Γ) B (.sort .zero) :=
    .conv _ B (.sort v) (.sort .zero) (.succ v) hB (.sorts _ v .zero hv0)
  have hPi0 : HasTyT E n Γ (.pi A B) (.sort .zero) :=
    .conv Γ (.pi A B) (.sort (.imax u .zero)) (.sort .zero)
      (.succ (.imax u .zero)) (.pi Γ A u B .zero hA hB0)
      (.sorts Γ (.imax u .zero) .zero (fun _ => rfl))
  exact ⟨.pi A B, ⟨hPi0⟩, ⟨hf⟩⟩

theorem proof_foldApps_head (su : SortUnique E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    (xs : List (Expr Nat)) → {f : Expr Nat} →
    IsProof E n Γ (foldApps f xs) → IsProof E n Γ f
  | [], _, h => h
  | _ :: xs, _, h =>
      proof_app_function su hW hΓ (proof_foldApps_head su hW hΓ xs h)

/-- A variable cannot be a proof when its literal lookup type is positively
sorted. Its original inversion chain, rather than general type uniqueness,
connects any proposed proof type back to that lookup. -/
theorem bvar_not_proof (su : SortUnique E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {i : Nat} {T : Expr Nat}
    (hlk : lookupType Γ i = some T)
    (hT : HasTyT E n Γ T (.sort (.succ .zero))) :
    ¬ IsProof E n Γ (.bvar i) := by
  rintro ⟨P, ⟨hP⟩, ⟨hp⟩⟩
  obtain ⟨B, hlkB, c⟩ := hasTyTInv_bvar hp rfl
  have hBT : B = T := Option.some.inj (hlkB.symm.trans hlk)
  subst B
  obtain ⟨hT0⟩ := sort_transport su hW hΓ c.symmT hP
  have bad := su hW hΓ hT hT0 (fun _ => none)
  simp [eval] at bad
end Generic

abbrev one : Level := .succ .zero
abbrev positiveContext : LCtx := F8EtaK.ctx one

def positiveContextWf : CtxWfT eqEnvT 2 positiveContext :=
  F8EtaK.contextWf one F8EtaK.positive_levels

/-- For ANY well-formed surrounding context, the recursor at a universe
semantically equal to 1 is not a proof. Six Pi inversions end at the actual
motive application, which has sort u, contradicting u =n 1 if the telescope
had been Prop-sorted. No pi injectivity or arbitrary type uniqueness is used. -/
theorem rec65_not_proof (su : SortUnique eqEnvT 2)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT 2 Γ) (ls : List Level)
    (hls : eqNList [one] ls) : ¬ IsProof eqEnvT 2 Γ (.const 65 ls) := by
  cases ls with
  | nil => exact False.elim hls
  | cons u rest =>
    cases rest with
    | cons v vs => exact False.elim hls.2
    | nil =>
      rintro ⟨P, ⟨hP⟩, ⟨hp⟩⟩
      obtain ⟨m, hm, _, _, c⟩ := hasTyTInv_const hp rfl
      change some eqRecT = some m at hm
      have hm' : m = eqRecT := (Option.some.inj hm).symm
      subst m
      obtain ⟨h0⟩ := sort_transport su F8EtaK.envWf hΓ c.symmT hP
      obtain ⟨u0, ⟨a0⟩, ⟨h1⟩⟩ := pi_zero_inv su F8EtaK.envWf hΓ h0
      have g1 := CtxWfT.assumption Γ _ u0 hΓ a0
      obtain ⟨u1, ⟨a1⟩, ⟨h2⟩⟩ := pi_zero_inv su F8EtaK.envWf g1 h1
      have g2 := CtxWfT.assumption _ _ u1 g1 a1
      obtain ⟨u2, ⟨a2⟩, ⟨h3⟩⟩ := pi_zero_inv su F8EtaK.envWf g2 h2
      have g3 := CtxWfT.assumption _ _ u2 g2 a2
      obtain ⟨u3, ⟨a3⟩, ⟨h4⟩⟩ := pi_zero_inv su F8EtaK.envWf g3 h3
      have g4 := CtxWfT.assumption _ _ u3 g3 a3
      obtain ⟨u4, ⟨a4⟩, ⟨h5⟩⟩ := pi_zero_inv su F8EtaK.envWf g4 h4
      have g5 := CtxWfT.assumption _ _ u4 g4 a4
      obtain ⟨u5, ⟨a5⟩, ⟨h6⟩⟩ := pi_zero_inv su F8EtaK.envWf g5 h5
      have g6 := CtxWfT.assumption _ _ u5 g5 a5
      let Δ : LCtx :=
        [.assumption (foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]),
         .assumption (.bvar 3),
         .assumption (instantiateLevels [u] eqMinorT),
         .assumption (instantiateLevels [u] eqMotT),
         .assumption (.bvar 0), .assumption (.sort one)] ++ Γ
      have gΔ : CtxWfT eqEnvT 2 Δ := g6
      have hBody0 : HasTyT eqEnvT 2 Δ
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) (.sort .zero) := h6
      have hM : HasTyT eqEnvT 2 Δ (.bvar 3)
          (lift 0 4 (instantiateLevels [u] eqMotT)) := .bvar Δ 3 _ rfl
      have hb : HasTyT eqEnvT 2 Δ (.bvar 1) (.bvar 5) := .bvar Δ 1 _ rfl
      have hp0 : HasTyT eqEnvT 2 Δ (.bvar 0)
          (foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 1]) :=
        .bvar Δ 0 _ rfl
      have hBodyU : HasTyT eqEnvT 2 Δ
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) (.sort u) :=
        .app _ _ _ _ _ (.app _ _ _ _ _ hM hb) hp0
      have h0u := su F8EtaK.envWf gΔ hBody0 hBodyU
      have bad : eqN one .zero := fun ρ => (hls.1 ρ).trans (h0u ρ).symm
      have impossible := bad (fun _ => none)
      simp [one, eval] at impossible

theorem rec_spine_not_proof (su : SortUnique eqEnvT 2)
    {Γ : LCtx} (hΓ : CtxWfT eqEnvT 2 Γ) (ls : List Level)
    (hls : eqNList [one] ls) (xs : List (Expr Nat)) :
    ¬ IsProof eqEnvT 2 Γ (foldApps (.const 65 ls) xs) :=
  fun h => rec65_not_proof su hΓ ls hls
    (proof_foldApps_head su F8EtaK.envWf hΓ xs h)

/-- Literal type of the minor, under one arbitrary new binder. -/
def minorType : Expr Nat :=
  .app (.app (.bvar 2) (.bvar 3))
    (.app (.app (.const 64 []) (.bvar 4)) (.bvar 3))

def minor_type_sort (A : Expr Nat) :
    HasTyT eqEnvT 2 (.assumption A :: positiveContext) minorType (.sort one) :=
  let Δ := .assumption A :: positiveContext
  let hM : HasTyT eqEnvT 2 Δ (.bvar 2)
      (lift 0 3 (instantiateLevels [one] eqMotT)) := .bvar Δ 2 _ rfl
  let ha : HasTyT eqEnvT 2 Δ (.bvar 3) (.bvar 4) := .bvar Δ 3 _ rfl
  let hα : HasTyT eqEnvT 2 Δ (.bvar 4) (.sort one) := .bvar Δ 4 _ rfl
  let hr : HasTyT eqEnvT 2 Δ (.const 64 []) eqReflT.mtype :=
    .const Δ 64 [] eqReflT rfl rfl rfl
  let hMa : HasTyT eqEnvT 2 Δ (.app (.bvar 2) (.bvar 3))
      (.pi (foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 3]) (.sort one)) :=
    .app _ _ _ _ _ hM ha
  let hrα : HasTyT eqEnvT 2 Δ (.app (.const 64 []) (.bvar 4))
      (.pi (.bvar 4) (foldApps (.const 63 []) [.bvar 5, .bvar 0, .bvar 0])) :=
    .app _ _ _ _ _ hr hα
  let hra : HasTyT eqEnvT 2 Δ (.app (.app (.const 64 []) (.bvar 4)) (.bvar 3))
      (foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 3]) :=
    .app _ _ _ _ _ hrα ha
  .app _ _ _ _ _ hMa hra

theorem minor_not_proof (su : SortUnique eqEnvT 2) (A : Expr Nat)
    (hΓ : CtxWfT eqEnvT 2 (.assumption A :: positiveContext)) :
    ¬ IsProof eqEnvT 2 (.assumption A :: positiveContext) (.bvar 1) :=
  bvar_not_proof su F8EtaK.envWf hΓ
    (show lookupType (.assumption A :: positiveContext) 1 = some minorType from rfl)
    (minor_type_sort A)

/-- The entire lambda is not a proof. This closes its loose PEqT.proof arm
without silently identifying the leaf's proposition with commonIndex. -/
theorem lambda_minor_not_proof (su : SortUnique eqEnvT 2) (A : Expr Nat) :
    ¬ IsProof eqEnvT 2 positiveContext (.lam A (.bvar 1)) := by
  rintro ⟨P, ⟨hP⟩, ⟨hp⟩⟩
  obtain ⟨u, B, hA, hb, c⟩ := hasTyTInv_lam hp rfl
  obtain ⟨hpi0⟩ := sort_transport su F8EtaK.envWf positiveContextWf c.symmT hP
  obtain ⟨_, _, ⟨hB0⟩⟩ := pi_zero_inv su F8EtaK.envWf positiveContextWf hpi0
  exact minor_not_proof su A (.assumption _ A u positiveContextWf hA)
    ⟨B, ⟨hB0⟩, ⟨hb⟩⟩

end Rcic.Declarative.F8A2Support

/-! Native audit: every explicit public declaration, including all helpers.
An elaboration placeholder is forbidden; a declared conditional premise is not
an axiom and must remain visible in the theorem's type. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [
    ``Rcic.Declarative.F8A2Support.SortUnique,
    ``Rcic.Declarative.F8A2Support.IsProof,
    ``Rcic.Declarative.F8A2Support.succ_eqN_injective,
    ``Rcic.Declarative.F8A2Support.imax_eqN_zero_right,
    ``Rcic.Declarative.F8A2Support.eqNList_trans_local,
    ``Rcic.Declarative.F8A2Support.sort_transport,
    ``Rcic.Declarative.F8A2Support.sort_chain_eq,
    ``Rcic.Declarative.F8A2Support.pi_zero_inv,
    ``Rcic.Declarative.F8A2Support.proof_app_function,
    ``Rcic.Declarative.F8A2Support.proof_foldApps_head,
    ``Rcic.Declarative.F8A2Support.bvar_not_proof,
    ``Rcic.Declarative.F8A2Support.one,
    ``Rcic.Declarative.F8A2Support.positiveContext,
    ``Rcic.Declarative.F8A2Support.positiveContextWf,
    ``Rcic.Declarative.F8A2Support.rec65_not_proof,
    ``Rcic.Declarative.F8A2Support.rec_spine_not_proof,
    ``Rcic.Declarative.F8A2Support.minorType,
    ``Rcic.Declarative.F8A2Support.minor_type_sort,
    ``Rcic.Declarative.F8A2Support.minor_not_proof,
    ``Rcic.Declarative.F8A2Support.lambda_minor_not_proof]
  for t in targets do
    unless env.contains t do throwError "Missing declaration {t}"
    let (_, st) := ((CollectAxioms.collect t).run env).run {}
    for ax in st.axioms do
      unless [``propext, ``Quot.sound].contains ax do
        throwError "Forbidden axiom {ax} in {t}"
    for c in st.visited.toList do
      if [`Rcic.Declarative.TypedRowsWf, `Rcic.Declarative.PiRowInjT,
          `Rcic.Declarative.DT012T_type_uniqueness,
          `Rcic.Declarative.DT012T_type_uniqueness_of_typedRowsWf].contains c then
        throwError "Unexpected global row/type-uniqueness dependency {c} in {t}"
    logInfo m!"{t}: {st.axioms}"
  logInfo m!"A2_CONDITIONAL_AUDIT: {targets.length} names; premise remains explicit"
