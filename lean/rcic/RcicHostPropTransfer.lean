import rcic.RcicA2SortSupport
import rcic.RcicParRedSRTyped
import rcic.RcicTypedSubstLet
import rcic.RcicLevelZero
import rcic.RcicAnnAlg

/-!
# piRow wall, piece A — host-Prop transfer from zero-sort coherence

Spec: `research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §2 (J line, #7515). The spec's Lean
was never compiled; this module is its compiled form, built by composition over the landed
A-2 sorting support (`RcicA2SortSupport`: `IsProof`, `imax_eqN_zero_right`), the `EnvWfT`
endpoint theorem (`convT_endpoints`), DT-007 regularity, the typed inversions, and the
head substitutions.

The only new premise is `ZeroSortCoherence E n`, the zero fragment of `SortUnique E n`:
a type sorted at `u` and at `Prop` has `u =ₙ 0`. Everything the A-2 file did with full sort
uniqueness that the host theorem needs is redone here from the fragment alone
(`sort_transport0`, `pi_zero_inv0`, `proof_app_function0`), plus the λ / let / literal
proofhood helpers (§2.5), the nine-constructor worker `hostProp_of_isProof0` (§2.6, recursion
on the single original derivation only), the proof-leaf finish by `ConvT.irr` at the common
host (§2.7), and the Boolean type-uniqueness corollary.

No `piRow`, no generic native type uniqueness, no normalization, no erased-to-native
reflection. Nothing here constructs `ZeroSortCoherence` (that is `RcicHostPropScoped`, §3.1).
`closure_claim = 0`.
-/
set_option autoImplicit false

namespace Rcic.Declarative.HostProp

open Rcic.Declarative.F8A2Support (IsProof SortUnique imax_eqN_zero_right)

/-- §2.1 zero-sort coherence: the zero fragment of sort uniqueness. Strictly weaker than
    `SortUnique E n` — only a `Prop` sorting of the same type is compared. -/
def ZeroSortCoherence (E : ResolvedEnv) (n : Nat) : Prop :=
  EnvWfT E → ∀ {Γ : LCtx} {A : Expr Nat} {u : Level},
    CtxWfT E n Γ → HasTyT E n Γ A (.sort u) → HasTyT E n Γ A (.sort .zero) → eqN u .zero

/-- full sort uniqueness restricts to the fragment. -/
theorem zeroSortCoherence_of_sortUnique {E : ResolvedEnv} {n : Nat} (su : SortUnique E n) :
    ZeroSortCoherence E n := by
  intro hW Γ A u hΓ hu h0
  exact su hW hΓ hu h0

section Generic
variable {E : ResolvedEnv} {n : Nat}

/-- §2.2 Helper 1: `Prop`-sorting transported ALONG a type chain from the fragment alone.
    Each link's endpoints are typed by DT-009 at the link's sort `v`; the fragment aligns `v`
    with `0` against the carried `Prop` sorting; `ConvT.sorts` retypes the far endpoint. -/
theorem sort_transport0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A B : Expr Nat} → TyConvT E n Γ A B →
    HasTyT E n Γ A (.sort .zero) → Nonempty (HasTyT E n Γ B (.sort .zero))
  | _, _, .refl _ _, hA => ⟨hA⟩
  | _, B, .of _ _ _ v hc, hA => by
      obtain ⟨⟨hAv⟩, ⟨hBv⟩⟩ := convT_endpoints hW hΓ hc
      have hv0 : eqN v .zero := zsc hW hΓ hAv hA
      exact ⟨.conv Γ B (.sort v) (.sort .zero) (.succ v) hBv (.sorts Γ v .zero hv0)⟩
  | _, _, .trans _ _ _ _ c₁ c₂, hA => by
      obtain ⟨hB⟩ := sort_transport0 zsc hW hΓ c₁ hA
      exact sort_transport0 zsc hW hΓ c₂ hB

/-- no sort converts to a proposition: transporting the `Prop` sorting back along the chain
    would sort `sort l` in `Prop`; against its canonical successor sorting the fragment gives
    `succ l =ₙ 0`. -/
theorem not_sort_tyConvT_prop (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {l : Level} {P : Expr Nat}
    (c : TyConvT E n Γ (.sort l) P) (hP : HasTyT E n Γ P (.sort .zero)) : False := by
  obtain ⟨h0⟩ := sort_transport0 zsc hW hΓ c.symmT hP
  exact Ann.not_eqN_succ_zero l (zsc hW hΓ (HasTyT.sort Γ l) h0)

/-- §2.6 `sort` row: a sort is never a proof. -/
theorem sort_not_proof0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {l : Level} (h : IsProof E n Γ (.sort l)) : False := by
  obtain ⟨P, ⟨hP⟩, ⟨hp⟩⟩ := h
  exact not_sort_tyConvT_prop zsc hW hΓ (hasTyTInv_sortT hp rfl) hP

/-- §2.6 `pi` row: a Π is never a proof (its inversion chain starts at a sort). -/
theorem pi_not_proof0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat} (h : IsProof E n Γ (.pi A B)) : False := by
  obtain ⟨P, ⟨hP⟩, ⟨hp⟩⟩ := h
  obtain ⟨_, _, _, _, c⟩ := hasTyTInv_pi hp rfl
  exact not_sort_tyConvT_prop zsc hW hΓ c hP

/-- §2.3 Helper 2: a Π sorted in `Prop` has its codomain sorted in `Prop`. The inversion's
    components are rebuilt into the canonical `HasTyT.pi` sorting and compared DIRECTLY with the
    given `Prop` sorting by the fragment; the inversion's chain residue is unused. The domain's
    sort evidence is returned so the binder context is certified. -/
theorem pi_zero_inv0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B : Expr Nat}
    (hpi : HasTyT E n Γ (.pi A B) (.sort .zero)) :
    ∃ u : Level, Nonempty (HasTyT E n Γ A (.sort u)) ∧
      Nonempty (HasTyT E n (.assumption A :: Γ) B (.sort .zero)) := by
  obtain ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hpi rfl
  have h0 : eqN (.imax u v) .zero := zsc hW hΓ (HasTyT.pi Γ A u B v hA hB) hpi
  have hv0 := imax_eqN_zero_right h0
  exact ⟨u, ⟨hA⟩, ⟨.conv _ B (.sort v) (.sort .zero) (.succ v) hB (.sorts _ v .zero hv0)⟩⟩

/-- §2.4 Helper 3: external proofhood of an application gives proofhood of its function.
    No comparison with the domain of another typing of `f` — hence no Π injectivity. -/
theorem proof_app_function0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f a : Expr Nat}
    (h : IsProof E n Γ (.app f a)) : IsProof E n Γ f := by
  obtain ⟨P, ⟨hP⟩, ⟨hfa⟩⟩ := h
  obtain ⟨A, B, hf, ha, c⟩ := hasTyTInv_app hfa rfl
  obtain ⟨_, ⟨hpi⟩⟩ := DT007T_typing_regularity_of_envWfT hW hΓ hf
  obtain ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hpi rfl
  obtain ⟨hBi0⟩ := sort_transport0 zsc hW hΓ c.symmT hP
  have hBiv := hasTyT_subst0S (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) hB ha
  have hv0 := zsc hW hΓ hBiv hBi0
  have hB0 : HasTyT E n (.assumption A :: Γ) B (.sort .zero) :=
    .conv _ B (.sort v) (.sort .zero) (.succ v) hB (.sorts _ v .zero hv0)
  have hPi0 : HasTyT E n Γ (.pi A B) (.sort .zero) :=
    .conv Γ (.pi A B) (.sort (.imax u .zero)) (.sort .zero)
      (.succ (.imax u .zero)) (.pi Γ A u B .zero hA hB0)
      (.sorts Γ (.imax u .zero) .zero (fun _ => rfl))
  exact ⟨.pi A B, ⟨hPi0⟩, ⟨hf⟩⟩

/-- §2.5 λ: external proofhood of `λ A, body` gives proofhood of `body` under the SAME written
    `A` (the external typing is inverted; its `Prop` sorting is transported back to the Π;
    Helper 2 reads the codomain). The domain's sort evidence certifies the binder context. -/
theorem proof_lam_body0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body : Expr Nat}
    (h : IsProof E n Γ (.lam A body)) :
    ∃ u : Level, Nonempty (HasTyT E n Γ A (.sort u)) ∧
      IsProof E n (.assumption A :: Γ) body := by
  obtain ⟨P, ⟨hP⟩, ⟨hp⟩⟩ := h
  obtain ⟨u, B, hA, hb, c⟩ := hasTyTInv_lam hp rfl
  obtain ⟨hpi0⟩ := sort_transport0 zsc hW hΓ c.symmT hP
  obtain ⟨_, _, ⟨hB0⟩⟩ := pi_zero_inv0 zsc hW hΓ hpi0
  exact ⟨u, ⟨hA⟩, B, ⟨hB0⟩, ⟨hb⟩⟩

/-- §2.5 let: external proofhood of `let A value body` gives proofhood of `body` in the let
    context. The external body typing is regularized to `B' : sort w`; head let-substitution
    with the value typing gives `value[B'] : sort w`; the external result chain transported back
    gives `value[B'] : Prop`; the fragment aligns `w` with `0`. Two typings of the same syntax
    only — no changed-declaration comparison. -/
theorem proof_letE_body0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A value body : Expr Nat}
    (h : IsProof E n Γ (.letE A value body)) :
    ∃ u : Level, Nonempty (HasTyT E n Γ A (.sort u)) ∧ Nonempty (HasTyT E n Γ value A) ∧
      IsProof E n (.letBinding A value :: Γ) body := by
  obtain ⟨P, ⟨hP⟩, ⟨hp⟩⟩ := h
  obtain ⟨u, B, hA, hv, hb, c⟩ := hasTyTInv_letE hp rfl
  have hΓ' : CtxWfT E n (.letBinding A value :: Γ) := .letBinding Γ A u value hΓ hA hv
  obtain ⟨w, ⟨hBw⟩⟩ := DT007T_typing_regularity_of_envWfT hW hΓ' hb
  have hBiw := hasTyT_substLet0_of_envWfT hW hBw hv
  obtain ⟨hBi0⟩ := sort_transport0 zsc hW hΓ c.symmT hP
  have hw0 := zsc hW hΓ hBiw hBi0
  exact ⟨u, ⟨hA⟩, ⟨hv⟩, B,
    ⟨.conv _ B (.sort w) (.sort .zero) (.succ w) hBw (.sorts _ w .zero hw0)⟩, ⟨hb⟩⟩

/-- §2.5 lit: external proofhood of a literal is proofhood of its exact expansion — the
    inversion's own expansion typing, at the proposition reached by transporting the `Prop`
    sorting back along the chain. -/
theorem proof_lit_expand0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {t : Nat}
    (h : IsProof E n Γ (.lit t)) : IsProof E n Γ (natExpand t) := by
  obtain ⟨P, ⟨hP⟩, ⟨hp⟩⟩ := h
  obtain ⟨T', hexp, c⟩ := hasTyTInv_lit hp rfl
  obtain ⟨hT0⟩ := sort_transport0 zsc hW hΓ c.symmT hP
  exact ⟨T', ⟨hT0⟩, ⟨hexp⟩⟩

/-- §2.6 the exhaustive worker on the nine typing constructors: an external proofhood
    certificate of `e` makes the ORIGINAL derivation's own type a proposition. Recursion is on
    the single original derivation `D`; every recursive call is on an actual proper typing child
    (`hbody`, `hf`, `hb`, `hexp`, `h`). Regularity / inversion outputs, endpoint proofs and
    substituted typings are never recursive subjects. -/
theorem hostProp_of_isProof0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E) :
    {Γ : LCtx} → {e T : Expr Nat} → (D : HasTyT E n Γ e T) → CtxWfT E n Γ →
    IsProof E n Γ e → Nonempty (HasTyT E n Γ T (.sort .zero))
  | _, _, _, .sort _ _, hΓ, hpf => (sort_not_proof0 zsc hW hΓ hpf).elim
  | _, _, _, .bvar Γ _ A hlk, hΓ, hpf => by
      obtain ⟨P, ⟨hP⟩, ⟨hp⟩⟩ := hpf
      obtain ⟨A', hlk', c⟩ := hasTyTInv_bvar hp rfl
      have hAA : A' = A := Option.some.inj (hlk'.symm.trans hlk)
      subst hAA
      exact sort_transport0 zsc hW hΓ c.symmT hP
  | _, _, _, .const Γ _ _ m hres _ _, hΓ, hpf => by
      obtain ⟨P, ⟨hP⟩, ⟨hp⟩⟩ := hpf
      obtain ⟨m', hres', _, _, c⟩ := hasTyTInv_const hp rfl
      have hmm : m' = m := Option.some.inj (hres'.symm.trans hres)
      subst hmm
      exact sort_transport0 zsc hW hΓ c.symmT hP
  | _, _, _, .pi _ _ _ _ _ _ _, hΓ, hpf => (pi_not_proof0 zsc hW hΓ hpf).elim
  | _, _, _, .lam Γ A u _ B hA hbody, hΓ, hpf => by
      obtain ⟨_, _, hpb⟩ := proof_lam_body0 zsc hW hΓ hpf
      obtain ⟨hB0⟩ := hostProp_of_isProof0 zsc hW hbody (.assumption Γ A u hΓ hA) hpb
      exact ⟨.conv Γ (.pi A B) (.sort (.imax u .zero)) (.sort .zero) (.succ (.imax u .zero))
        (.pi Γ A u B .zero hA hB0) (.sorts Γ (.imax u .zero) .zero (fun _ => rfl))⟩
  | _, _, _, .app Γ _ _ _ _ hf ha, hΓ, hpf => by
      obtain ⟨hPi0⟩ := hostProp_of_isProof0 zsc hW hf hΓ (proof_app_function0 zsc hW hΓ hpf)
      obtain ⟨_, _, ⟨hB0⟩⟩ := pi_zero_inv0 zsc hW hΓ hPi0
      exact ⟨hasTyT_subst0S (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hB0 ha⟩
  | _, _, _, .letE Γ A u value _ _ hA hv hb, hΓ, hpf => by
      obtain ⟨_, _, _, hpb⟩ := proof_letE_body0 zsc hW hΓ hpf
      obtain ⟨hB0⟩ := hostProp_of_isProof0 zsc hW hb (.letBinding Γ A u value hΓ hA hv) hpb
      exact ⟨hasTyT_substLet0_of_envWfT hW hB0 hv⟩
  | _, _, _, .lit _ _ _ hexp, hΓ, hpf =>
      hostProp_of_isProof0 zsc hW hexp hΓ (proof_lit_expand0 zsc hW hΓ hpf)
  | _, _, _, .conv Γ _ A B u h hc, hΓ, hpf => by
      obtain ⟨hA0⟩ := hostProp_of_isProof0 zsc hW h hΓ hpf
      exact sort_transport0 zsc hW hΓ (.of Γ A B u hc) hA0

/-- §2.7 the native proof-leaf finish: common-host typings `p q : T` and ONE external
    certificate `p : P`, `P : Prop` give `ConvT p q T` by `ConvT.irr` at the host. No
    `TyConvT T P`, no uniqueness request. -/
theorem irr_of_common_host0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {p q T P : Expr Nat}
    (hpT : HasTyT E n Γ p T) (hqT : HasTyT E n Γ q T)
    (hpP : HasTyT E n Γ p P) (hP : HasTyT E n Γ P (.sort .zero)) :
    Nonempty (ConvT E n Γ p q T) := by
  obtain ⟨hT0⟩ := hostProp_of_isProof0 zsc hW hpT hΓ ⟨P, ⟨hP⟩, ⟨hpP⟩⟩
  exact ⟨.irr Γ T p q hT0 hpT hqT⟩

/-- §2.7 corollary, Boolean type uniqueness: two typings of one term at sorted types agree
    on the `Prop` bit. This proves neither `TyConvT T U` nor `eqN u v`. -/
theorem bit_unique_of_hostProp0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e T U : Expr Nat} {u v : Level}
    (heT : HasTyT E n Γ e T) (heU : HasTyT E n Γ e U)
    (hT : HasTyT E n Γ T (.sort u)) (hU : HasTyT E n Γ U (.sort v)) :
    levelIsZero u = levelIsZero v := by
  have key : ∀ {T U : Expr Nat} {u v : Level}, HasTyT E n Γ e T → HasTyT E n Γ e U →
      HasTyT E n Γ T (.sort u) → HasTyT E n Γ U (.sort v) →
      levelIsZero u = true → levelIsZero v = true := by
    intro T U u v heT heU hT hU hu
    have hu0 : eqN u .zero := (levelIsZero_iff u).mp hu
    have hT0 : HasTyT E n Γ T (.sort .zero) :=
      .conv Γ T (.sort u) (.sort .zero) (.succ u) hT (.sorts Γ u .zero hu0)
    obtain ⟨hU0⟩ := hostProp_of_isProof0 zsc hW heU hΓ ⟨T, ⟨hT0⟩, ⟨heT⟩⟩
    exact (levelIsZero_iff v).mpr (zsc hW hΓ hU hU0)
  cases hu : levelIsZero u with
  | true => exact (key heT heU hT hU hu).symm
  | false =>
      cases hv : levelIsZero v with
      | false => rfl
      | true => exact absurd (key heU heT hU hT hv) (by simp [hu])

end Generic

end Rcic.Declarative.HostProp

#print axioms Rcic.Declarative.HostProp.zeroSortCoherence_of_sortUnique
#print axioms Rcic.Declarative.HostProp.sort_transport0
#print axioms Rcic.Declarative.HostProp.not_sort_tyConvT_prop
#print axioms Rcic.Declarative.HostProp.sort_not_proof0
#print axioms Rcic.Declarative.HostProp.pi_not_proof0
#print axioms Rcic.Declarative.HostProp.pi_zero_inv0
#print axioms Rcic.Declarative.HostProp.proof_app_function0
#print axioms Rcic.Declarative.HostProp.proof_lam_body0
#print axioms Rcic.Declarative.HostProp.proof_letE_body0
#print axioms Rcic.Declarative.HostProp.proof_lit_expand0
#print axioms Rcic.Declarative.HostProp.hostProp_of_isProof0
#print axioms Rcic.Declarative.HostProp.irr_of_common_host0
#print axioms Rcic.Declarative.HostProp.bit_unique_of_hostProp0
