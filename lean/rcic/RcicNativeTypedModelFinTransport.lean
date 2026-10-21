import rcic.RcicNativeTypedModelBeta
import rcic.RcicNativeTypedModelTel

/-!
# RcicNativeTypedModelFinTransport — the ruling's transport and escape laws, measured at the pin

Item 2.3 slice 2, executing the cc ruling of 2026-10-19 17:42Z (PR #7726, comment 6273447296)
steps 1, 2 and 4.  The ruling keeps the bundled `T`-motive and prescribes two candidate laws;
this module states each at the exact shape its consumer would use it, then kernel-checks both.
**Both are refuted**, by junk-environment witnesses at the canonical model, with the empty
readback (`RedR` = reflexivity only, `NormalR` vacuous — no readback laws needed):

* `TypedFinTransportAt` (step 1): the binder type's IH-relations at a code `a` realized on the
  `ρ`-side, plus the demand's `CTyS`-typing at `a`, do **not** move the typing to any code
  realized on the `ρ'`-side.  `not_typedFinTransportAt`: at `Γ = [y : Sort 1]`,
  `A = Π (x := y), Sort 0`, the related pair `ρ = {y ↦ π sort [([], prop)]}`, `ρ' = ∅`: the
  `ρ`-code `a = π (π sort [([], prop)]) [([], prop)]` types the demand
  `uLam = lam [( [lam [([π ⊥ []], ⊥)]], ⊥)]`, but `A`'s `ρ'`-codes are all `π ⊥ f` (the empty
  environment realizes no code at `y`, so every `Π`-domain code at `ρ'` is `⊥`), and `⊥`-domains
  type only `⊥` demands.  Related type codes with different typed sets, as the ruling's step 2
  anticipated; the fix is the clause strengthening (step 2's second half), not a motive premise.

* `RelSubstEnvTypedFin` (step 4, the escape): `RelSubstAtT` does **not** type the environments.
  `not_relSubstEnvTypedFin_cexEnvP`: at the one-axiom environment `cexEnvP`, the related pair
  `ρ = ρ' = {x ↦ spine 0 []}` under `x : ∀ (p : Prop), p` admits the constant-headed spine
  compact through `SpineClauseS` (the axiom's `foldApps` reading, `ConvArgsT.nil`, and the
  saturation conditional vacuous at an axiom member) — while `TypingFin.EnvTypedFinAtT` needs a realized
  code of the Π-headed type typing it, and `ApproxT` realizes only `Π`-codes there, at which
  `CTyS` types only `lam`/`⊥` elements.  **The clause that must carry typing is the element
  spine clause `SpineClauseS`** (equivalently `RelSubstAtT`'s compact conjunct): it admits
  constant-headed spine compacts with no typing obligation.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

/-! ### §0 — the readback that does nothing -/

/-- The empty readback: `RedR` is reflexivity only and everything is normal. -/
def emptyReadback : Readback := fun _ _ _ => False

def emptyNormalR {Γ : LCtx} {X : Expr Nat} : NormalR emptyReadback Γ X := fun _ h => h

/-! ### §1 — the two candidate laws, at the consumer's shape -/

/-- **The ruling's step-1 transport law.**  `A[ρ]` and `A[ρ']` related at a sort by the IH on
    `hA` — the three relation instances `domRelations_of_ih` returns at the code `a` — move the
    finite-joint `CTyS`-typing of a demand list from a code realized at `ρ` to one realized at
    `ρ'`, and symmetrically. -/
def TypedFinTransportAt (M : CtxModelT E) (R : Readback) (n : Nat) : Prop :=
  ∀ {Γ Δ : LCtx} {A : Expr Nat} {u : Level} {ρ ρ' : EnvT} {σ σ' : SubstT},
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ →
    ∀ {a : CptT}, (M.Ap ρ A a ∨ M.Ap ρ' A a) →
      LRSCoreS R E n Δ (substT σ A) (substT σ' A) (.sort u) a →
      LRSCoreS R E n Δ (substT σ A) (substT σ A) (.sort u) a →
      LRSCoreS R E n Δ (substT σ' A) (substT σ' A) (.sort u) a →
      ∀ {us : List CptT}, (∀ v ∈ us, CTyS E v a) →
        (∃ a', M.Ap ρ' A a' ∧ ∀ v ∈ us, CTyS E v a') ∧
        (∃ a', M.Ap ρ A a' ∧ ∀ v ∈ us, CTyS E v a')

/-- **The ruling's step-4 escape law**: relatedness of the two environment/substitution pairs
    types both environments along the context. -/
def RelSubstEnvTypedFin (M : CtxModelT E) (R : Readback) (n : Nat) : Prop :=
  ∀ {Δ Γ : LCtx} {ρ ρ' : EnvT} {σ σ' : SubstT},
    RelSubstAtT M R n Δ ρ ρ' σ σ' Γ → TypingFin.EnvTypedFinAtT M Γ ρ ∧ TypingFin.EnvTypedFinAtT M Γ ρ'

/-! ### §2 — the transport countermodel -/

section Transport

variable {E : ResolvedEnv}

/-- The context `y : Sort 1` (the level `pinPiT`'s Π lives at). -/
def tpUniv : Level := .imax (.succ .zero) (.succ .zero)
def tpCtx : LCtx := [LocalDecl.assumption (.sort tpUniv)]

theorem lookupType_tpCtx_zero : lookupType tpCtx 0 = some (.sort tpUniv) := by
  simp [lookupType, tpCtx, lift]

/-- The substituent: `Π (a : Sort 0), Sort 0` — Π-headed (so `y`'s relatable compacts are
    Π-shaped), and a sort element under `pinPiT`. -/
def tpDom : Expr Nat := .pi (.sort .zero) (.sort .zero)
def tpSigma : SubstT := fun _ => tpDom

/-- The binder type under test: `Π (x := y), Sort 0` — its codes at an environment are
    Π-codes whose domain codes are `y`'s compacts at that environment. -/
def tpBindTy : Expr Nat := .pi (.bvar 0) (.sort .zero)

/-- `y`'s single compact: a Π-code with a sort domain and one proposition output (`sortCode 0`)
    — related at the universe by the `.pi` clause (both elements read back to `tpDom`). -/
def tpA1 : CptT := .pi .sort [([], .prop)]

/-- The code of `tpBindTy` at `ρ`: domain `tpA1` (realized at `y`), one step with an empty
    demand and a proposition output. -/
def tpA : CptT := .pi tpA1 [([], .prop)]

/-- The typed side: `y ↦ tpA1`.  The junk side: empty. -/
def rhoP : EnvT := fun i c => i = 0 ∧ c = tpA1
def rhoJunk : EnvT := fun _ _ => False

/-- The demand element: a λ-step whose demand is the proposition-code `π ⊥ []` (typed at
    `tpA1`'s sort domain) and whose output is `⊥`. -/
def xDemand : CptT := .lam [([.pi .bot []], .bot)]

/-- The demand list: one λ-step whose demand is `xDemand` and whose output is `⊥` — typed at
    `tpA` (`.lam` at a non-Prop Π-code, `⊥` compatible with the proposition output, coverage
    by `⊥`). -/
def uLam : CptT := .lam [([xDemand], .bot)]

theorem uLam_ne_bot : uLam ≠ .bot := fun h => CptT.noConfusion h
theorem xDemand_ne_bot : xDemand ≠ .bot := fun h => CptT.noConfusion h
theorem spine0_ne_bot : CptT.spine 0 [] ≠ .bot := fun h => CptT.noConfusion h

theorem substT_tpBindTy : substT tpSigma tpBindTy = .pi tpDom (.sort .zero) := by
  simp [substT, tpBindTy, tpSigma, SubstT.up]

theorem substT_tpUniv : substT tpSigma (.sort tpUniv) = .sort tpUniv := by
  simp [substT]

theorem not_isPropCT_tpA1 : ¬ IsPropCT E tpA1 := by
  intro h
  cases h with
  | pi _ hout => exact not_isPropCT_prop E (hout ([], .prop) (List.mem_singleton_self _))

theorem not_isPropCT_tpA : ¬ IsPropCT E tpA := by
  intro h
  cases h with
  | pi _ hout => exact not_isPropCT_prop E (hout ([], .prop) (List.mem_singleton_self _))

theorem tyCodeCT_pDemand : TyCodeCT (.pi .bot []) :=
  .pi .bot (fun _ ht => (List.not_mem_nil _ ht).elim)

/-- The demand element is typed at `tpA1` (a λ-step at a non-Prop Π-code, its demand a
    proposition-code at the sort domain, `⊥` compatible with the proposition output). -/
theorem ctyS_xDemand_tpA1 : CTyS E xDemand tpA1 := by
  rw [CTyS.eq_def]
  refine Or.inr ⟨[([.pi .bot []], .bot)], rfl, not_isPropCT_tpA1, ?_, ?_, ?_⟩
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    rw [CTyS]
    exact Or.inr tyCodeCT_pDemand
  · intro s hs t ht _
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp ht with rfl
    rw [CTyS]
    exact Or.inl rfl
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact Or.inl rfl

/-- The demand list is typed at the `ρ`-side code `tpA`. -/
theorem ctyS_uLam_tpA : CTyS E uLam tpA := by
  rw [CTyS.eq_def]
  refine Or.inr ⟨[([xDemand], .bot)], rfl, not_isPropCT_tpA, ?_, ?_, ?_⟩
  · intro s hs u hu
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp hu with rfl
    exact ctyS_xDemand_tpA1
  · intro s hs t ht _
    rcases List.mem_singleton.mp hs with rfl
    rcases List.mem_singleton.mp ht with rfl
    show CTyS E CptT.bot CptT.prop
    rw [CTyS]
    exact Or.inl rfl
  · intro s hs
    rcases List.mem_singleton.mp hs with rfl
    exact Or.inl rfl

/-- `tpA1` is realized at `y` on the typed side. -/
theorem apprT_rhoP_tpA1 : ApproxT E rhoP (.bvar 0) tpA1 := .bvar ⟨rfl, rfl⟩

/-- `tpA` is realized at `tpBindTy` on the typed side: the `Π`-introduction at the domain code
    `tpA1` with one proposition-output step (the closed sort's code). -/
theorem apprT_rhoP_tpA : ApproxT E rhoP tpBindTy tpA :=
  .pi apprT_rhoP_tpA1
    (fun s hs u hu => by
      rcases List.mem_singleton.mp hs with rfl
      exact (List.not_mem_nil _ hu).elim)
    (fun s hs => by
      rcases List.mem_singleton.mp hs with rfl
      exact sortCode_zero ▸ approxT_sort_code E _ .zero)

/-- `y`'s compact `tpA1` is related at the universe: both elements read back to `tpDom`, the
    domain code is a sort code (both sort readbacks), the single step's output is read at the
    closed sort codomain (instantiation is constant). -/
theorem lrSCoreS_empty_tpA1 (E : ResolvedEnv) (n : Nat) :
    LRSCoreS emptyReadback E n [] tpDom tpDom (.sort tpUniv) tpA1 := by
  have hsort : ∀ (M : Expr Nat), instantiate0 M (.sort .zero) = .sort .zero := by
    intro M; rfl
  rw [LRSCoreS.eq_def]
  refine ⟨⟨tpUniv, .refl _⟩, .sort .zero, .sort .zero, .sort .zero, .sort .zero, .refl _,
    .refl _, ⟨.assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)⟩,
    ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.succ .zero, ?_⟩, ?_⟩
  · rw [LRSCoreS.eq_def]
    exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero, .refl _, .refl _⟩
  · intro s hs _ N N' hN hN' hconv _
    rcases List.mem_singleton.mp hs with rfl
    refine ⟨.succ .zero, ?_⟩
    rw [hsort N, hsort N', LRSCoreS.eq_def]
    exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero, .refl _, .refl _⟩

/-- The `IH`-on-`hA` relation instances at `tpA`: Π-clauses down both readbacks, the domain
    code `tpA1` related at the universe. -/
theorem lrSCoreS_empty_tpA (E : ResolvedEnv) (n : Nat) :
    LRSCoreS emptyReadback E n [] (substT tpSigma tpBindTy) (substT tpSigma tpBindTy)
      (.sort (.imax tpUniv (.succ .zero))) tpA := by
  have hsort : ∀ (M : Expr Nat), instantiate0 M (.sort .zero) = .sort .zero := by
    intro M; rfl
  rw [substT_tpBindTy, LRSCoreS.eq_def]
  refine ⟨⟨_, .refl _⟩, tpDom, .sort .zero, tpDom, .sort .zero, .refl _, .refl _,
    ⟨.assumption [] tpDom tpUniv .nil (pinPiT E n)⟩, ⟨.refl _ _⟩, ⟨.refl _ _⟩,
    ⟨tpUniv, lrSCoreS_empty_tpA1 E n⟩, ?_⟩
  · intro s hs _ N N' hN hN' hconv _
    rcases List.mem_singleton.mp hs with rfl
    refine ⟨.succ .zero, ?_⟩
    rw [hsort N, hsort N', LRSCoreS.eq_def]
    exact ⟨⟨.succ .zero, .refl _⟩, .zero, .zero, .refl _, .refl _⟩

/-- The related substitution pair at `tpCtx`: constant `tpDom`, typed by `pinPiT`, convertible
    by reflexivity; `y`'s compact related; no let-bound variables. -/
def hS_tp (E : ResolvedEnv) (n : Nat) :
    RelSubstAtT (ctxModelT_approxT E) emptyReadback n [] rhoP rhoJunk tpSigma tpSigma tpCtx := by
  refine ⟨⟨fun i A hA => ?_, fun i v hv => by
      cases i <;> simp [lookupValue, tpCtx] at hv⟩,
    ⟨fun i A hA => ?_, fun i v hv => by
      cases i <;> simp [lookupValue, tpCtx] at hv⟩,
    fun i A hA => ?_, fun i A hA c hc => ?_,
    fun i v A hv hA c hc => by
      cases i <;> simp [lookupValue, tpCtx] at hv⟩
  · cases i with
    | zero =>
        have hAq : some A = lookupType tpCtx 0 := hA.symm
        rw [lookupType_tpCtx_zero] at hAq
        injection hAq with hAq'
        subst hAq'
        rw [substT_tpUniv]
        exact ⟨pinPiT E n⟩
    | succ i => simp [lookupType, tpCtx] at hA
  · cases i with
    | zero =>
        have hAq : some A = lookupType tpCtx 0 := hA.symm
        rw [lookupType_tpCtx_zero] at hAq
        injection hAq with hAq'
        subst hAq'
        rw [substT_tpUniv]
        exact ⟨pinPiT E n⟩
    | succ i => simp [lookupType, tpCtx] at hA
  · cases i with
    | zero =>
        have hAq : some A = lookupType tpCtx 0 := hA.symm
        rw [lookupType_tpCtx_zero] at hAq
        injection hAq with hAq'
        subst hAq'
        rw [substT_tpUniv]
        exact ⟨.refl [] _ _ (pinPiT E n)⟩
    | succ i => simp [lookupType, tpCtx] at hA
  · cases i with
    | zero =>
        have hAq : some A = lookupType tpCtx 0 := hA.symm
        rw [lookupType_tpCtx_zero] at hAq
        injection hAq with hAq'
        subst hAq'
        have hc0 : rhoP 0 c := by
          rcases hc with h | h
          · exact h
          · exact False.elim h
        have hcq : c = tpA1 := hc0.2
        subst hcq
        have hAz : tpSigma 0 = tpDom := rfl
        have hTz : substT tpSigma (.sort tpUniv) = .sort tpUniv := substT_tpUniv
        rw [hAz, hTz]
        exact ⟨lrSCoreS_empty_tpA1 E n, lrSCoreS_empty_tpA1 E n,
          lrSCoreS_empty_tpA1 E n, lrSCoreS_empty_tpA1 E n⟩
    | succ i => simp [lookupType, tpCtx] at hA

/-- `tpBindTy`'s codes at the junk environment: every `Π`-domain is `⊥` (no compacts at `y`). -/
theorem apprT_rhoJunk_tpBindTy {a : CptT} (h : ApproxT E rhoJunk tpBindTy a) :
    a = .bot ∨ ∃ f, a = .pi .bot f := by
  rcases approxT_pi_inv h with rfl | ⟨a₀, f, rfl, hA₀, -⟩
  · exact Or.inl rfl
  · rcases approxT_bvar_inv hA₀ with rfl | hρ
    · exact Or.inr ⟨f, rfl⟩
    · exact False.elim hρ

/-- No code of `tpBindTy` at the junk environment types the demand list: `⊥` does not type
    `uLam`, and `π ⊥ f`'s domain does not type `xDemand`. -/
theorem not_ctyS_uLam_rhoJunk {a : CptT} (h : ApproxT E rhoJunk tpBindTy a)
    (hty : CTyS E uLam a) : False := by
  rcases apprT_rhoJunk_tpBindTy h with rfl | ⟨f, rfl⟩
  · exact uLam_ne_bot (ctyS_bot_inv hty)
  · rcases ctyS_pi_inv hty with h0 | ⟨f', heq, -, hdom, -, -⟩
    · exact uLam_ne_bot h0
    · unfold uLam at heq
      injection heq with heq'
      subst heq'
      rcases hdom ([xDemand], .bot) (List.mem_singleton_self _) xDemand
        (List.mem_singleton_self _) with h
      exact xDemand_ne_bot (ctyS_bot_inv h)

/-- **The ruling's step 1 is FALSE on typed inputs** — the kernel countermodel of step 2:
    related type codes with different typed sets. -/
theorem not_typedFinTransportAt (E : ResolvedEnv) (n : Nat) :
    ¬ TypedFinTransportAt (ctxModelT_approxT E) emptyReadback n := by
  intro h
  obtain ⟨hρ', -⟩ := h (Δ := []) (ρ := rhoP) (ρ' := rhoJunk) (σ := tpSigma) (σ' := tpSigma)
    (hS_tp E n) (a := tpA) (Or.inl apprT_rhoP_tpA)
    (lrSCoreS_empty_tpA E n) (lrSCoreS_empty_tpA E n) (lrSCoreS_empty_tpA E n)
    (us := [uLam])
    (fun v hv => by rcases List.mem_singleton.mp hv with rfl; exact ctyS_uLam_tpA)
  obtain ⟨a', hreal, hty⟩ := hρ'
  exact not_ctyS_uLam_rhoJunk hreal (hty uLam (List.mem_singleton_self _))

end Transport

/-! ### §3 — the escape countermodel -/

section Escape

/-- The context `x : ∀ (p : Prop), p` and the substitution by the axiom constant. -/
def cexCtxS : LCtx := [LocalDecl.assumption cexPolyAxiomType]
def sigmaS : SubstT := fun _ => Expr.const 0 []

theorem lookupType_cexCtxS_zero : lookupType cexCtxS 0 = some cexPolyAxiomType := by
  simp [lookupType, cexCtxS, lift, cexPolyAxiomType]

/-- The related pair: `x ↦ spine 0 []` on both sides. -/
def rhoSpine : EnvT := fun i c => i = 0 ∧ c = CptT.spine 0 []

theorem substT_sigmaS : substT sigmaS cexPolyAxiomType = cexPolyAxiomType := by
  simp [substT, cexPolyAxiomType, sigmaS, SubstT.up]

/-- The element spine clause admits the constant-headed spine compact: the axiom's own
    `foldApps` reading, `ConvArgsT` at `nil`, and the saturation conditional vacuous at an axiom
    member. -/
def spineClauseS_cex (n : Nat) :
    SpineClauseS emptyReadback cexEnvP n [] (Expr.const 0 []) (Expr.const 0 [])
      cexPolyAxiomType 0 [] := by
  refine ⟨cexMemberP, [], [], [], [], cexEnvP_members, .refl _, .refl _, emptyNormalR,
    emptyNormalR, True.intro, Nat.le_refl 0, Nat.le_refl 0,
    ConvArgsT.nil _, fun _ hInd => nomatch hInd⟩

/-- The related substitution pair: the axiom constant typed by its member, convertible by
    reflexivity; `x`'s spine compact related by the spine clause. -/
def hS_spine (n : Nat) :
    RelSubstAtT (ctxModelT_approxT cexEnvP) emptyReadback n [] rhoSpine rhoSpine
      sigmaS sigmaS cexCtxS := by
  have hty : HasTyT cexEnvP n [] (Expr.const 0 []) cexPolyAxiomType := by
    have h0 : HasTyT cexEnvP n [] (Expr.const 0 []) (instantiateLevels [] cexMemberP.mtype) :=
      .const [] 0 [] cexMemberP cexEnvP_members rfl rfl
    have heq : instantiateLevels [] cexMemberP.mtype = cexPolyAxiomType := rfl
    rw [heq] at h0
    exact h0
  refine ⟨⟨fun i A hA => ?_, fun i v hv => by
      cases i <;> simp [lookupValue, cexCtxS] at hv⟩,
    ⟨fun i A hA => ?_, fun i v hv => by
      cases i <;> simp [lookupValue, cexCtxS] at hv⟩,
    fun i A hA => ?_, fun i A hA c hc => ?_,
    fun i v A hv hA c hc => by
      cases i <;> simp [lookupValue, cexCtxS] at hv⟩
  · cases i with
    | zero =>
        have hAq : some A = lookupType cexCtxS 0 := hA.symm
        rw [lookupType_cexCtxS_zero] at hAq
        injection hAq with hAq'
        subst hAq'
        rw [substT_sigmaS]
        exact ⟨hty⟩
    | succ i => simp [lookupType, cexCtxS] at hA
  · cases i with
    | zero =>
        have hAq : some A = lookupType cexCtxS 0 := hA.symm
        rw [lookupType_cexCtxS_zero] at hAq
        injection hAq with hAq'
        subst hAq'
        rw [substT_sigmaS]
        exact ⟨hty⟩
    | succ i => simp [lookupType, cexCtxS] at hA
  · cases i with
    | zero =>
        have hAq : some A = lookupType cexCtxS 0 := hA.symm
        rw [lookupType_cexCtxS_zero] at hAq
        injection hAq with hAq'
        subst hAq'
        rw [substT_sigmaS]
        exact ⟨.refl [] _ _ hty⟩
    | succ i => simp [lookupType, cexCtxS] at hA
  · cases i with
    | zero =>
        have hAq : some A = lookupType cexCtxS 0 := hA.symm
        rw [lookupType_cexCtxS_zero] at hAq
        injection hAq with hAq'
        subst hAq'
        have hc0 : rhoSpine 0 c := by
          rcases hc with h | h
          · exact h
          · exact h
        have hcq : c = CptT.spine 0 [] := hc0.2
        subst hcq
        have hSz : sigmaS 0 = Expr.const 0 [] := rfl
        rw [lrSCoreS_spine_iff, hSz, substT_sigmaS]
        exact ⟨spineClauseS_cex n, spineClauseS_cex n, spineClauseS_cex n, spineClauseS_cex n⟩
    | succ i => simp [lookupType, cexCtxS] at hA

/-- No `Π`-code types a spine element. -/
theorem not_ctyS_spine_pi {a₀ : CptT} {f : List (List CptT × CptT)} :
    ¬ CTyS cexEnvP (CptT.spine 0 []) (.pi a₀ f) := by
  intro h
  rcases ctyS_pi_inv h with h0 | ⟨f', heq, -, -, -, -⟩
  · exact spine0_ne_bot h0
  · exact CptT.noConfusion heq

/-- **The ruling's step 4 is FALSE**: the escape from relatedness to environment typing is
    blocked at the element spine clause — `SpineClauseS` admits `spine 0 []` at the Π-typed
    variable with no typing obligation, while `TypingFin.EnvTypedFinAtT` needs a realized Π-code typing
    it, and the model realizes only Π-codes at the Π-headed type. -/
theorem not_relSubstEnvTypedFin_cexEnvP (n : Nat) :
    ¬ RelSubstEnvTypedFin (ctxModelT_approxT cexEnvP) emptyReadback n := by
  intro h
  obtain ⟨hρ, -⟩ := h (hS_spine n)
  obtain ⟨a, hreal, hty⟩ := hρ 0 cexPolyAxiomType rfl [CptT.spine 0 []]
    (fun u hu => by rcases List.mem_singleton.mp hu with rfl; exact ⟨rfl, rfl⟩)
  have hreal' : ApproxT cexEnvP rhoSpine cexPolyAxiomType a := hreal
  have hty' : CTyS cexEnvP (CptT.spine 0 []) a :=
    hty _ (List.mem_singleton_self _)
  rcases approxT_pi_inv hreal' with rfl | ⟨a₀, f, rfl, -, -⟩
  · exact spine0_ne_bot (ctyS_bot_inv hty')
  · exact not_ctyS_spine_pi hty'

end Escape

-- BEGIN GLM FUND TRANSPORT SEAL (axiom queries; every public declaration)
#print axioms emptyReadback
#print axioms emptyNormalR
#print axioms TypedFinTransportAt
#print axioms RelSubstEnvTypedFin
#print axioms tpUniv
#print axioms tpCtx
#print axioms lookupType_tpCtx_zero
#print axioms tpDom
#print axioms tpSigma
#print axioms tpBindTy
#print axioms tpA1
#print axioms tpA
#print axioms rhoP
#print axioms rhoJunk
#print axioms xDemand
#print axioms uLam
#print axioms uLam_ne_bot
#print axioms xDemand_ne_bot
#print axioms spine0_ne_bot
#print axioms substT_tpBindTy
#print axioms substT_tpUniv
#print axioms not_isPropCT_tpA1
#print axioms not_isPropCT_tpA
#print axioms tyCodeCT_pDemand
#print axioms ctyS_xDemand_tpA1
#print axioms ctyS_uLam_tpA
#print axioms apprT_rhoP_tpA1
#print axioms apprT_rhoP_tpA
#print axioms lrSCoreS_empty_tpA1
#print axioms lrSCoreS_empty_tpA
#print axioms hS_tp
#print axioms apprT_rhoJunk_tpBindTy
#print axioms not_ctyS_uLam_rhoJunk
#print axioms not_typedFinTransportAt
#print axioms cexCtxS
#print axioms sigmaS
#print axioms lookupType_cexCtxS_zero
#print axioms rhoSpine
#print axioms substT_sigmaS
#print axioms spineClauseS_cex
#print axioms hS_spine
#print axioms not_ctyS_spine_pi
#print axioms not_relSubstEnvTypedFin_cexEnvP
-- END GLM FUND TRANSPORT SEAL

end Rcic.Declarative.NativeValleys.TypedModelAudit
