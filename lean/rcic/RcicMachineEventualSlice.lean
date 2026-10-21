/-
RM-025 Carrier 2 — Positive eventuality slice lifting (`RcicNormalizingErase` /
`TypedState` / `InferSlice` / `CheckSlice`) under the explicit module-boundary
hypothesis `Normalizing`, non-vacuous fragment proof and inhabitants, and the
named residual wall `normalization_full` (`docs/rcic/03_REFERENCE_MACHINE.md:391,
401-408`, `research/rcic/rm/S0_RM024_025.md`, cc ruling R3 on #7058).

`closure_claim = 0`.
-/
import rcic.RcicMachineEventual
import rcic.RcicNormalizingErase
import rcic.RcicTypedMachineAccept
import rcic.RcicDT025Restated

namespace Rcic.Machine.Eventual

open Rcic.Declarative
open Rcic.Declarative.Ann
open Rcic.Declarative.NormalizingErase
open Rcic.Machine

/-! ## 1. `WhnfJoin` and `convCert` completeness for common-WHNF pairs -/

/-- Two expressions `l` and `r` join at a common machine weak-head normal form
    `w` when both reduce via `MachineRed E n Γ` to `w` and
    `machineWhnfDone E w = true`. -/
def WhnfJoin (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l r : Expr Nat) : Prop :=
  ∃ w : Expr Nat,
    Nonempty (MachineRed E n Γ l w) ∧
    Nonempty (MachineRed E n Γ r w) ∧
    machineWhnfDone E w = true

/-- Reflexivity of `WhnfJoin` for any term reducing to a WHNF `w`. -/
theorem whnfJoin_refl (E : ResolvedEnv) (n : Nat) (Γ : LCtx) {e w : Expr Nat}
    (k : MachineRed E n Γ e w) (hdone : machineWhnfDone E w = true) :
    WhnfJoin E n Γ e e :=
  ⟨w, ⟨k⟩, ⟨k⟩, hdone⟩

/-- Reflexivity of `WhnfJoin` for an expression already in WHNF. -/
theorem whnfJoin_of_done (E : ResolvedEnv) (n : Nat) (Γ : LCtx) {e : Expr Nat}
    (hdone : machineWhnfDone E e = true) :
    WhnfJoin E n Γ e e :=
  whnfJoin_refl E n Γ (.refl Γ e) hdone

/-- Symmetry of `WhnfJoin`. -/
theorem whnfJoin_symm {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l r : Expr Nat}
    (h : WhnfJoin E n Γ l r) :
    WhnfJoin E n Γ r l := by
  rcases h with ⟨w, hl, hr, hdone⟩
  exact ⟨w, hr, hl, hdone⟩

/-- `convCert` completeness for any pair `l, r` with explicit `MachineRed` chains
    to a common head-normal form `w`: at fuel
    `Nat.max (machineRedSteps kl) (machineRedSteps kr) + 1`, `convCert` succeeds. -/
theorem convCert_complete_of_machineRed_join {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A : Expr Nat) {l r w : Expr Nat}
    (kl : MachineRed E n Γ l w) (kr : MachineRed E n Γ r w)
    (hdone : machineWhnfDone E w = true) :
    ∃ c : Conv E n Γ l r,
      convCert E n (Nat.max (machineRedSteps kl) (machineRedSteps kr) + 1) Γ A l r = .ok c := by
  let f₀ := Nat.max (machineRedSteps kl) (machineRedSteps kr)
  rw [convCert]
  by_cases hlr : l = r
  · subst hlr
    simp only [dif_pos rfl]
    exact ⟨_, rfl⟩
  · rw [dif_neg hlr]
    rcases whnfCert_complete_of_machineRed kl hdone f₀
      (Nat.le_max_left (machineRedSteps kl) (machineRedSteps kr)) with
      ⟨⟨wl, kl'⟩, hwl_ok, hwl_eq⟩
    simp only at hwl_eq
    rcases whnfCert_complete_of_machineRed kr hdone f₀
      (Nat.le_max_right (machineRedSteps kl) (machineRedSteps kr)) with
      ⟨⟨wr, kr'⟩, hwr_ok, hwr_eq⟩
    simp only at hwr_eq
    split
    · next msg hno => rw [hwl_ok] at hno; nomatch hno
    · next wl₂ kl₂ hwl₂ =>
        have hwl₂_eq : wl₂ = w := by
          rw [hwl_ok] at hwl₂
          injection hwl₂ with h1
          exact (congrArg PSigma.fst h1).symm.trans hwl_eq
        subst hwl₂_eq
        split
        · next msg hno => rw [hwr_ok] at hno; nomatch hno
        · next wr₂ kr₂ hwr₂ =>
            have hwr₂_eq : wr₂ = wl₂ := by
              rw [hwr_ok] at hwr₂
              injection hwr₂ with h1
              exact (congrArg PSigma.fst h1).symm.trans hwr_eq
            subst hwr₂_eq
            simp only [dif_pos rfl]
            exact ⟨_, rfl⟩

/-- `WhnfJoin` implies `convCert` succeeds at some finite positive fuel `f`. -/
theorem convCert_complete_of_whnfJoin {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A : Expr Nat) {l r : Expr Nat} (hjoin : WhnfJoin E n Γ l r) :
    ∃ (f : Nat) (c : Conv E n Γ l r), convCert E n f Γ A l r = .ok c := by
  rcases hjoin with ⟨w, ⟨kl⟩, ⟨kr⟩, hdone⟩
  rcases convCert_complete_of_machineRed_join A kl kr hdone with ⟨c, hc⟩
  exact ⟨_, c, hc⟩

/-- Any `WhnfJoin` pair is eventually accepted by `.convAt A l r` with
    `.conversionConfirmed`. -/
theorem RM025_whnfJoin_convAt_eventual {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A : Expr Nat) {l r : Expr Nat} (hjoin : WhnfJoin E n Γ l r) :
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.convAt A l r) .conversionConfirmed :=
  (RM025_convAt_confirmed_iff_eventual E n Γ A l r).mpr
    (convCert_complete_of_whnfJoin A hjoin)

/-! ## 2. Module-boundary `Normalizing` hypothesis and `RM025_normalizing_eventually_accepted` -/

/-- Explicit module-boundary positive eventuality hypothesis (`Normalizing`,
    cc ruling R3 on #7058):
    1. `sortA`: the expected type `A` eventually synthesizes a sort `.sort u`.
    2. `inferE`: the term `e` eventually synthesizes a type `Te` that joins with
       `A` at a common machine WHNF (`WhnfJoin E n Γ Te A`).
    Normalization of the full theory is NOT assumed anywhere as a fact;
    `Normalizing` is an explicit hypothesis discharged on positive fragments. -/
structure Normalizing (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat) : Prop where
  sortA : ∃ u : Level,
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.infer A) (.inferredType (.sort u))
  inferE : ∃ Te : Expr Nat,
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.infer e) (.inferredType Te) ∧
    WhnfJoin E n Γ Te A

/-- **Main Carrier 2 Theorem (`RM025_normalizing_eventually_accepted`, R3):**
    under the explicit module-boundary hypothesis `Normalizing E n Γ e A`,
    the resumable reference machine eventually accepts `.check e A` with `.checked`. -/
theorem RM025_normalizing_eventually_accepted {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A : Expr Nat} (hnorm : Normalizing E n Γ e A) :
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.check e A) .checked := by
  rcases hnorm.sortA with ⟨u, hevA⟩
  rcases (RM025_infer_eventual_iff E n Γ A (.sort u)).mp hevA with
    ⟨fA, ⟨TA, hA⟩, hinfA, hTA⟩
  simp only at hTA
  subst hTA
  rcases hnorm.inferE with ⟨Te, hevE, hjoin⟩
  rcases (RM025_infer_eventual_iff E n Γ e Te).mp hevE with
    ⟨fe, ⟨Te', he⟩, hinfE, hTe'⟩
  simp only at hTe'
  subst hTe'
  rcases convCert_complete_of_whnfJoin A hjoin with ⟨fc, hc, hconv⟩
  let f₀ := Nat.max fA (Nat.max fe fc)
  have hfA : fA ≤ f₀ := Nat.le_max_left fA (Nat.max fe fc)
  have hfe : fe ≤ f₀ :=
    Nat.le_trans (Nat.le_max_left fe fc) (Nat.le_max_right fA (Nat.max fe fc))
  have hfc : fc ≤ f₀ :=
    Nat.le_trans (Nat.le_max_right fe fc) (Nat.le_max_right fA (Nat.max fe fc))
  rcases inferCert_mono hinfA hfA with ⟨⟨TA', hA'⟩, hinfA', hTA_eq⟩
  simp only at hTA_eq
  subst hTA_eq
  rcases inferCert_mono hinfE hfe with ⟨⟨Te'', he'⟩, hinfE', hTe_eq⟩
  simp only at hTe_eq
  subst hTe_eq
  rcases convCert_mono hconv hfc with ⟨hc', hconv'⟩
  apply (RM025_check_eventual_iff E n Γ e A).mpr
  refine ⟨f₀ + 1, .conv Γ e Te'' A he' hc', ?_⟩
  simp only [checkCert, hinfA', hinfE', hconv']

/-- Threshold stabilization form of `RM025_normalizing_eventually_accepted`:
    `Normalizing E n Γ e A` yields a finite budget threshold `B` from which every
    inner budget `b ≥ B` and outer budget `m ≥ 1` accepts `.check e A`. -/
theorem RM025_normalizing_acceptsFrom {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A : Expr Nat} (hnorm : Normalizing E n Γ e A) :
    ∃ B : Nat, TaskAcceptsFrom ⟨E, n, Γ⟩ (.check e A) .checked B :=
  (taskEventuallyAccepts_iff_acceptsFrom (t := .check e A) (p := .checked) trivial).mp
    (RM025_normalizing_eventually_accepted hnorm)

/-- Soundness of `Normalizing`: any `Normalizing` pair has a declarative derivation
    `Nonempty (HasTy E n Γ e A)`. -/
theorem RM025_normalizing_hasTy {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A : Expr Nat} (hnorm : Normalizing E n Γ e A) :
    Nonempty (HasTy E n Γ e A) :=
  (RM025_check_sound_and_eventual_iff E n Γ e A).2
    (RM025_normalizing_eventually_accepted hnorm)

/-! ## 3. Lifting `TypedState` (`RcicTypedMachineAccept`) and `RcicNormalizingErase` (`TmChainA`) -/

/-- Lifting a `TypedState` check run (`RcicTypedMachineAccept.RM016T_run_check_sound`)
    under the module-boundary `Normalizing` hypothesis:
    an accepted `typedRun (k + 1) s = .accepted (.checked e A d)` with
    `Normalizing E n Γ e A` yields both the typed judgment `HasTyT E n Γ e A`
    and raw-machine positive eventuality
    `TaskEventuallyAccepts s.ambient (.check e A) .checked`. -/
def RM025_typedState_normalizing_eventually_accepted
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (k : Nat) (s : TypedState) (e A : Expr Nat)
    (hamb : s.ambient = ⟨E, n, Γ⟩)
    (htask : s.task = .checkT2 A e)
    (hacc : Σ' d, typedRun (k + 1) s = .accepted (.checked e A d))
    (hnorm : Normalizing E n Γ e A) :
    HasTyT E n Γ e A ×'
      PProd (Nonempty (HasTy E n Γ e A))
        (TaskEventuallyAccepts s.ambient (.check e A) .checked) := by
  have htyT : HasTyT s.ambient.env s.ambient.univs s.ambient.ctx e A :=
    RM016T_run_check_sound k s e A htask hacc
  rw [hamb] at htyT ⊢
  exact ⟨htyT, ⟨RM025_normalizing_hasTy hnorm, RM025_normalizing_eventually_accepted hnorm⟩⟩

/-- Annotated typed head-step slice (`StepIsMachineHead`) on `TyHRedA`
    (`RcicNormalizingErase.lean`): steps whose erased counterpart is a single
    `MachineRed` head step (`.beta`, `.zeta`, `.delta`, and `.conv` wrappers). -/
def StepIsMachineHead {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {a b A : ExprA} : TyHRedA EA I n Γ a b A → Prop
  | .beta .. => True
  | .zeta .. => True
  | .delta .. => True
  | .conv _ _ _ _ _ h _ => StepIsMachineHead h
  | _ => False

/-- Every `StepIsMachineHead` step is disjoint from `StepHasKStop`
    (`RcicNormalizingErase.lean:32`). -/
theorem stepIsMachineHead_not_kStop {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    {Γ : LCtxA} → {a b A : ExprA} → (s : TyHRedA EA I n Γ a b A) →
    StepIsMachineHead s → ¬ StepHasKStop s
  | _, _, _, _, .beta .., _, hk => hk
  | _, _, _, _, .zeta .., _, hk => hk
  | _, _, _, _, .delta .., _, hk => hk
  | _, _, _, _, .conv _ _ _ _ _ h _, hm, hk => stepIsMachineHead_not_kStop h hm hk

/-- Under `StepIsMachineHead s`, `tyHRedA_erase` never stops (`(tyHRedA_erase hI s).1 = b`). -/
theorem tyHRedA_erase_fst_of_machineHead {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : ∀ e e', I.fn e = some e' →
      DerivedIota (eraseEnv EA) (erase e) (erase e'))
    {Γ : LCtxA} {a b A : ExprA} {s : TyHRedA EA I n Γ a b A}
    (hm : StepIsMachineHead s) :
    (tyHRedA_erase hI s).1 = b := by
  rcases (tyHRedA_erase hI s).2.2 with h | ⟨_, hk⟩
  · exact h
  · exact False.elim (stepIsMachineHead_not_kStop s hm hk)

/-- Prepending a single erased `StepIsMachineHead` step onto a `MachineRed` chain. -/
def stepIsMachineHead_prepend {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    {Γ : LCtxA} → {a b A : ExprA} → {w : Expr Nat} →
    (s : TyHRedA EA I n Γ a b A) →
    StepIsMachineHead s →
    MachineRed (eraseEnv EA) n (eraseCtx Γ) (erase b) w →
    MachineRed (eraseEnv EA) n (eraseCtx Γ) (erase a) w
  | Γ, _, _, _, _, .beta _ A _ body arg _ _ _ _ _, _, k => by
      rw [erase_instantiate0A] at k
      exact MachineRed.headBeta (eraseCtx Γ) (erase A) (erase body) (erase arg) [] k
  | Γ, _, _, _, _, .zeta _ A value body _ _ _ _ _ _, _, k => by
      rw [erase_instantiate0A] at k
      exact MachineRed.headZeta (eraseCtx Γ) (erase A) (erase value) (erase body) [] k
  | Γ, _, _, _, _, .delta _ r ls m b hres hbody htr _ _ _, _, k => by
      rw [erase_instantiateLevelsA] at k
      have hmemb : (eraseEnv EA).members r = some (eraseMember m) :=
        members_eraseEnv_some hres
      have hbody' : (eraseMember m).body = some (erase b) := by
        show m.bodyA.map erase = some (erase b)
        rw [hbody]
        rfl
      exact MachineRed.headDelta (eraseCtx Γ) r ls (eraseMember m) (erase b) []
        hmemb hbody' htr k
  | _, _, _, _, _, .conv _ _ _ _ _ h _, hm, k =>
      stepIsMachineHead_prepend h hm k
  | _, _, _, _, _, .zetaLocal .., hm, _ => False.elim hm
  | _, _, _, _, _, .iota .., hm, _ => False.elim hm
  | _, _, _, _, _, .lit .., hm, _ => False.elim hm
  | _, _, _, _, _, .app .., hm, _ => False.elim hm
  | _, _, _, _, _, .major .., hm, _ => False.elim hm
  | _, _, _, _, _, .kunit .., hm, _ => False.elim hm
  | _, _, _, _, _, .kstruct .., hm, _ => False.elim hm

/-- Chain-level predicate `ChainIsMachineHead` on `TmChainA` (`RcicNormalizingErase.lean`):
    every step in `t` satisfies `StepIsMachineHead`. -/
def ChainIsMachineHead {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {A a N : ExprA} : TmChainA EA I n Γ A a N → Prop
  | .refl _ _ => True
  | .cons _ _ _ _ s t => StepIsMachineHead s ∧ ChainIsMachineHead t

/-- No step inside a `ChainIsMachineHead` chain has `StepHasKStop`. -/
theorem chainStepAt_not_kStop {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {A : ExprA} :
    {a N : ExprA} → {t : TmChainA EA I n Γ A a N} →
    {X b : ExprA} → {s' : TyHRedA EA I n Γ X b A} →
    ChainStepAt t X b s' → ChainIsMachineHead t → ¬ StepHasKStop s'
  | _, _, .cons _ _ _ _ s _, _, _, _, .head _ _ _, hc =>
      stepIsMachineHead_not_kStop s hc.1
  | _, _, .cons _ _ _ _ _ _, _, _, _, .tail _ _ _ hcs, hc =>
      chainStepAt_not_kStop hcs hc.2

/-- Every `ChainIsMachineHead` chain erases without stopping in `tmChainA_erase`:
    `(tmChainA_erase hI t).1 = N`, yielding `ParRedStar (eraseEnv EA) n (eraseCtx Γ) (erase a) (erase N)`. -/
theorem tmChainA_erase_of_machineHead {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : ∀ e e', I.fn e = some e' →
      DerivedIota (eraseEnv EA) (erase e) (erase e'))
    {Γ : LCtxA} {A a N : ExprA} (t : TmChainA EA I n Γ A a N)
    (hc : ChainIsMachineHead t) :
    (tmChainA_erase hI t).1 = N ∧
      Nonempty (ParRedStar (eraseEnv EA) n (eraseCtx Γ) (erase a) (erase N)) := by
  rcases (tmChainA_erase hI t).2.2 with hN | ⟨X, s', hk, ⟨hstep⟩⟩
  · refine ⟨hN, ?_⟩
    have hpar := (tmChainA_erase hI t).2.1
    rw [hN] at hpar
    exact ⟨hpar⟩
  · exact False.elim (chainStepAt_not_kStop hstep hc hk)

/-- Erasing a `ChainIsMachineHead` chain `TmChainA EA I n Γ A a N` directly to
    a `MachineRed` derivation from `erase a` to `erase N`. -/
def tmChainA_toMachineRed {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {A : ExprA} :
    {a N : ExprA} →
    (t : TmChainA EA I n Γ A a N) →
    ChainIsMachineHead t →
    MachineRed (eraseEnv EA) n (eraseCtx Γ) (erase a) (erase N)
  | a, _, .refl _ _, _ => .refl (eraseCtx Γ) (erase a)
  | _, _, .cons _ _ _ _ s t, hc =>
      stepIsMachineHead_prepend s hc.1 (tmChainA_toMachineRed t hc.2)

/-- **Lifting `RcicNormalizingErase` (`TmChainA`) to `.whnfAt` eventuality:**
    any `TmChainA EA I n Γ A a N` satisfying `ChainIsMachineHead t` whose
    endpoint `erase N` is machine head-normal (`machineWhnfDone (eraseEnv EA) (erase N) = true`)
    is eventually accepted by `.whnfAt (erase A) (erase a)` with
    `.inferredWhnf (erase A) (erase N)` and witnesses `WhnfJoin` between `erase a` and `erase N`. -/
theorem RM025_tmChainA_whnf_eventual {EA : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {A a N : ExprA}
    (t : TmChainA EA I n Γ A a N)
    (hc : ChainIsMachineHead t)
    (hdone : machineWhnfDone (eraseEnv EA) (erase N) = true) :
    TaskEventuallyAccepts ⟨eraseEnv EA, n, eraseCtx Γ⟩
      (.whnfAt (erase A) (erase a))
      (.inferredWhnf (erase A) (erase N)) ∧
    WhnfJoin (eraseEnv EA) n (eraseCtx Γ) (erase a) (erase N) := by
  let k := tmChainA_toMachineRed t hc
  exact ⟨(RM025_whnf_eventual_iff (eraseEnv EA) n (eraseCtx Γ) (erase A) (erase a) (erase N)).mpr
      ⟨⟨k⟩, hdone⟩,
    ⟨erase N, ⟨k⟩, ⟨.refl (eraseCtx Γ) (erase N)⟩, hdone⟩⟩

/-- **Lifting `RcicNormalizingErase` (`TmChainA`) to `Normalizing` and `.check` eventuality:**
    if `t : TmChainA EA I n Γ (.sort u) Te A` is an annotated type-reduction chain
    satisfying `ChainIsMachineHead t` to a head-normal type `erase A`, and `erase A`
    and `erase e` eventually synthesize `.sort v` and `erase Te`, then
    `Normalizing (eraseEnv EA) n (eraseCtx Γ) (erase e) (erase A)` holds and
    `.check (erase e) (erase A)` is eventually accepted. -/
theorem RM025_tmChainA_normalizing_check_eventual {EA : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {u v : Level} {e Te A : ExprA}
    (t : TmChainA EA I n Γ (.sort u) Te A)
    (hc : ChainIsMachineHead t)
    (hdone : machineWhnfDone (eraseEnv EA) (erase A) = true)
    (hsortA : TaskEventuallyAccepts ⟨eraseEnv EA, n, eraseCtx Γ⟩
      (.infer (erase A)) (.inferredType (.sort v)))
    (hinfE : TaskEventuallyAccepts ⟨eraseEnv EA, n, eraseCtx Γ⟩
      (.infer (erase e)) (.inferredType (erase Te))) :
    Normalizing (eraseEnv EA) n (eraseCtx Γ) (erase e) (erase A) ∧
    TaskEventuallyAccepts ⟨eraseEnv EA, n, eraseCtx Γ⟩
      (.check (erase e) (erase A)) .checked := by
  have ⟨_, hjoin⟩ := RM025_tmChainA_whnf_eventual t hc hdone
  have hnorm : Normalizing (eraseEnv EA) n (eraseCtx Γ) (erase e) (erase A) :=
    ⟨⟨v, hsortA⟩, ⟨erase Te, hinfE, hjoin⟩⟩
  exact ⟨hnorm, RM025_normalizing_eventually_accepted hnorm⟩

/-! ## 4. Nontrivial inductive fragment (`InferSlice` / `CheckSlice`) proving `Normalizing` -/

/-- Constructive algorithmic synthesis fragment (`InferSlice E n Γ e T`):
    the 7-constructor inductive slice closed under `.sort`, `.bvar`, `.const`
    (arity `0`, `ls = []`), `.pi`, `.lam`, `.app` (with `MachineRed` Π-exposure
    and `WhnfJoin` argument conversion), and `.letE` (with `WhnfJoin` value
    conversion). -/
inductive InferSlice (E : ResolvedEnv) (n : Nat) : LCtx → Expr Nat → Expr Nat → Prop
  | sort (Γ : LCtx) (l : Level) :
      InferSlice E n Γ (.sort l) (.sort (.succ l))
  | bvar (Γ : LCtx) (i : Nat) (A : Expr Nat) :
      lookupType Γ i = some A →
      InferSlice E n Γ (.bvar i) A
  | const (Γ : LCtx) (r : Nat) (m : CheckedMember) :
      E.members r = some m →
      0 = m.arity →
      InferSlice E n Γ (.const r []) (instantiateLevels [] m.mtype)
  | pi (Γ : LCtx) (A B : Expr Nat) (u v : Level) :
      InferSlice E n Γ A (.sort u) →
      InferSlice E n (.assumption A :: Γ) B (.sort v) →
      InferSlice E n Γ (.pi A B) (.sort (.imax u v))
  | lam (Γ : LCtx) (A body Tbody : Expr Nat) (u : Level) :
      InferSlice E n Γ A (.sort u) →
      InferSlice E n (.assumption A :: Γ) body Tbody →
      InferSlice E n Γ (.lam A body) (.pi A Tbody)
  | app (Γ : LCtx) (fn arg Tf A B Targ : Expr Nat) :
      InferSlice E n Γ fn Tf →
      Nonempty (MachineRed E n Γ Tf (.pi A B)) →
      InferSlice E n Γ arg Targ →
      WhnfJoin E n Γ Targ A →
      InferSlice E n Γ (.app fn arg) (instantiate0 arg B)
  | letE (Γ : LCtx) (A value body Tval Tbody : Expr Nat) (u : Level) :
      InferSlice E n Γ A (.sort u) →
      InferSlice E n Γ value Tval →
      WhnfJoin E n Γ Tval A →
      InferSlice E n (.letBinding A value :: Γ) body Tbody →
      InferSlice E n Γ (.letE A value body) (instantiate0 value Tbody)

/-- Positive bidirectional checking fragment (`CheckSlice E n Γ e A`):
    `A` synthesizes `.sort u` in `InferSlice`, `e` synthesizes `Te` in
    `InferSlice`, and `Te` joins with `A` via `WhnfJoin`. -/
structure CheckSlice (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat) : Prop where
  sortA : ∃ u : Level, InferSlice E n Γ A (.sort u)
  inferE : ∃ Te : Expr Nat, InferSlice E n Γ e Te ∧ WhnfJoin E n Γ Te A

/-- Every `InferSlice` derivation succeeds in `inferCert` at some finite positive fuel `f`. -/
theorem inferSlice_inferCert_ok {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (h : InferSlice E n Γ e T) :
    ∃ (f : Nat) (c : Σ' (T' : Expr Nat), HasTy E n Γ e T'),
      inferCert E n f Γ e = .ok c ∧ c.1 = T := by
  induction h with
  | sort Γ l =>
      exact ⟨1, ⟨.sort (.succ l), .sort Γ l⟩, rfl, rfl⟩
  | bvar Γ i A hlk =>
      refine ⟨1, ?_⟩
      rw [inferCert]
      split
      · next A' hlt =>
          rw [hlk] at hlt
          injection hlt with hA
          subst hA
          exact ⟨_, rfl, rfl⟩
      · next hlt =>
          rw [hlk] at hlt
          exact nomatch hlt
  | const Γ r m hmemb har =>
      rcases inferCert_const_nil_ok (n := n) (f := 0) (Γ := Γ) hmemb har with
        ⟨c, hok, hc⟩
      exact ⟨1, c, hok, hc⟩
  | pi Γ A B u v _ _ ihA ihB =>
      rcases ihA with ⟨fA, ⟨TA, dA⟩, hinfA, hTA⟩
      simp only at hTA
      subst hTA
      rcases ihB with ⟨fB, ⟨TB, dB⟩, hinfB, hTB⟩
      simp only at hTB
      subst hTB
      let f₀ := Nat.max fA fB
      rcases inferCert_mono hinfA (Nat.le_max_left fA fB) with ⟨⟨TA', dA'⟩, hinfA', hTA'⟩
      simp only at hTA'
      subst hTA'
      rcases inferCert_mono hinfB (Nat.le_max_right fA fB) with ⟨⟨TB', dB'⟩, hinfB', hTB'⟩
      simp only at hTB'
      subst hTB'
      refine ⟨f₀ + 1, ⟨.sort (.imax u v), .pi Γ A u B v dA' dB'⟩, ?_, rfl⟩
      simp only [inferCert, hinfA', hinfB']
  | lam Γ A body Tbody u _ _ ihA ihbody =>
      rcases ihA with ⟨fA, ⟨TA, dA⟩, hinfA, hTA⟩
      simp only at hTA
      subst hTA
      rcases ihbody with ⟨fB, ⟨TB, dB⟩, hinfB, hTB⟩
      simp only at hTB
      subst hTB
      let f₀ := Nat.max fA fB
      rcases inferCert_mono hinfA (Nat.le_max_left fA fB) with ⟨⟨TA', dA'⟩, hinfA', hTA'⟩
      simp only at hTA'
      subst hTA'
      rcases inferCert_mono hinfB (Nat.le_max_right fA fB) with ⟨⟨TB', dB'⟩, hinfB', hTB'⟩
      simp only at hTB'
      subst hTB'
      refine ⟨f₀ + 1, ⟨.pi A TB', .lam Γ A u body TB' dA' dB'⟩, ?_, rfl⟩
      simp only [inferCert, hinfA', hinfB']
  | app Γ fn arg Tf A B Targ _ hkTf _ hjoin ihfn iharg =>
      rcases ihfn with ⟨ffn, ⟨Tf', dfn⟩, hinffn, hTf'⟩
      simp only at hTf'
      subst hTf'
      rcases hkTf with ⟨kTf⟩
      let fw := machineRedSteps kTf
      rcases whnfCert_complete_of_machineRed kTf rfl fw (Nat.le_refl fw) with
        ⟨⟨Tfw, kTf'⟩, hwhnf, hTfw⟩
      simp only at hTfw
      subst hTfw
      rcases iharg with ⟨farg, ⟨Targ', darg⟩, hinfarg, hTarg'⟩
      simp only at hTarg'
      subst hTarg'
      rcases convCert_complete_of_whnfJoin A hjoin with ⟨fc, dc, hconv⟩
      let f₀ := Nat.max (Nat.max ffn fw) (Nat.max farg fc)
      have hffn : ffn ≤ f₀ :=
        Nat.le_trans (Nat.le_max_left ffn fw)
          (Nat.le_max_left (Nat.max ffn fw) (Nat.max farg fc))
      have hfw : fw ≤ f₀ :=
        Nat.le_trans (Nat.le_max_right ffn fw)
          (Nat.le_max_left (Nat.max ffn fw) (Nat.max farg fc))
      have hfarg : farg ≤ f₀ :=
        Nat.le_trans (Nat.le_max_left farg fc)
          (Nat.le_max_right (Nat.max ffn fw) (Nat.max farg fc))
      have hfc : fc ≤ f₀ :=
        Nat.le_trans (Nat.le_max_right farg fc)
          (Nat.le_max_right (Nat.max ffn fw) (Nat.max farg fc))
      rcases inferCert_mono hinffn hffn with ⟨⟨Tf'', dfn'⟩, hinffn', hTf''⟩
      simp only at hTf''
      subst hTf''
      rcases whnfCert_mono hwhnf hfw with ⟨⟨Tfw', kTf''⟩, hwhnf', hTfw'⟩
      simp only at hTfw'
      subst hTfw'
      rcases inferCert_mono hinfarg hfarg with ⟨⟨Targ'', darg'⟩, hinfarg', hTarg''⟩
      simp only at hTarg''
      subst hTarg''
      rcases convCert_mono hconv hfc with ⟨dc', hconv'⟩
      refine ⟨f₀ + 1, ⟨instantiate0 arg B, .app Γ fn arg A B (.conv Γ fn Tf'' (.pi A B) dfn' (machineRed_toConv kTf'')) (.conv Γ arg Targ'' A darg' dc')⟩, ?_, rfl⟩
      simp only [inferCert, inferCert.inferCert_app, hinffn', hwhnf', hinfarg', hconv']
  | letE Γ A value body Tval Tbody u _ _ hjoin _ ihA ihval ihbody =>
      rcases ihA with ⟨fA, ⟨TA, dA⟩, hinfA, hTA⟩
      simp only at hTA
      subst hTA
      rcases ihval with ⟨fval, ⟨Tval', dval⟩, hinfval, hTval'⟩
      simp only at hTval'
      subst hTval'
      rcases convCert_complete_of_whnfJoin A hjoin with ⟨fc, dc, hconv⟩
      rcases ihbody with ⟨fbody, ⟨Tbody', dbody⟩, hinfbody, hTbody'⟩
      simp only at hTbody'
      subst hTbody'
      let f₀ := Nat.max (Nat.max fA fval) (Nat.max fc fbody)
      have hfA : fA ≤ f₀ :=
        Nat.le_trans (Nat.le_max_left fA fval)
          (Nat.le_max_left (Nat.max fA fval) (Nat.max fc fbody))
      have hfval : fval ≤ f₀ :=
        Nat.le_trans (Nat.le_max_right fA fval)
          (Nat.le_max_left (Nat.max fA fval) (Nat.max fc fbody))
      have hfc : fc ≤ f₀ :=
        Nat.le_trans (Nat.le_max_left fc fbody)
          (Nat.le_max_right (Nat.max fA fval) (Nat.max fc fbody))
      have hfbody : fbody ≤ f₀ :=
        Nat.le_trans (Nat.le_max_right fc fbody)
          (Nat.le_max_right (Nat.max fA fval) (Nat.max fc fbody))
      rcases inferCert_mono hinfA hfA with ⟨⟨TA', dA'⟩, hinfA', hTA'⟩
      simp only at hTA'
      subst hTA'
      rcases inferCert_mono hinfval hfval with ⟨⟨Tval'', dval'⟩, hinfval', hTval''⟩
      simp only at hTval''
      subst hTval''
      rcases convCert_mono hconv hfc with ⟨dc', hconv'⟩
      rcases inferCert_mono hinfbody hfbody with ⟨⟨Tbody'', dbody'⟩, hinfbody', hTbody''⟩
      simp only at hTbody''
      subst hTbody''
      refine ⟨f₀ + 1, ⟨instantiate0 value Tbody'', .letE Γ A u value Tbody'' dA' (.conv Γ value Tval'' A dval' dc') dbody'⟩, ?_, rfl⟩
      simp only [inferCert, hinfA', hinfval', hconv', hinfbody']

/-- Every `InferSlice E n Γ e T` derivation is eventually accepted by `.infer e`
    with `.inferredType T`. -/
theorem inferSlice_eventually_accepts {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (h : InferSlice E n Γ e T) :
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.infer e) (.inferredType T) :=
  (RM025_infer_eventual_iff E n Γ e T).mpr (inferSlice_inferCert_ok h)

/-- **Nontrivial Fragment Theorem (`normalizing_of_checkSlice`, R3):**
    every `CheckSlice E n Γ e A` derivation satisfies the module-boundary
    `Normalizing E n Γ e A` predicate. -/
theorem normalizing_of_checkSlice {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (h : CheckSlice E n Γ e A) :
    Normalizing E n Γ e A := by
  rcases h.sortA with ⟨u, hA⟩
  rcases h.inferE with ⟨Te, he, hjoin⟩
  exact ⟨⟨u, inferSlice_eventually_accepts hA⟩,
    ⟨Te, inferSlice_eventually_accepts he, hjoin⟩⟩

/-- Every `CheckSlice E n Γ e A` derivation is eventually accepted by
    `.check e A` with `.checked`. -/
theorem RM025_checkSlice_eventually_accepted {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A : Expr Nat} (h : CheckSlice E n Γ e A) :
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.check e A) .checked :=
  RM025_normalizing_eventually_accepted (normalizing_of_checkSlice h)

/-! ## 5. Residual general wall `normalization_full` and negative Loop pins -/

/-- **Residual General Wall (`normalization_full`, cc ruling R3 on #7058):**
    whether every well-typed term `HasTyT E n Γ e A` in a well-formed environment
    `EnvWfT E` and context `CtxWfT E n Γ` satisfies `Normalizing E n Γ e A`. -/
def normalization_full : Prop :=
  ∀ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e A : Expr Nat),
    EnvWfT E → CtxWfT E n Γ → HasTyT E n Γ e A → Normalizing E n Γ e A

/-- Conditional full-theory completeness under `normalization_full`:
    if `normalization_full` held, every `HasTyT E n Γ e A` would be eventually
    accepted by `.check e A`. -/
theorem RM025_completeness_of_normalization_full
    (hfull : normalization_full)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) (hty : HasTyT E n Γ e A) :
    TaskEventuallyAccepts ⟨E, n, Γ⟩ (.check e A) .checked :=
  RM025_normalizing_eventually_accepted (hfull E n Γ e A hW hΓ hty)

/-- Any `MachineRed` chain starting at `omegaXT = (λx:X. x x)(λx:X. x x)`
    reduces only to `omegaXT` itself (a 1-cycle β-loop). -/
theorem machineRed_omegaXT_eq {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e w : Expr Nat} → (k : MachineRed E n Γ e w) → e = omegaXT →
    w = omegaXT
  | _, _, _, .refl _ _, he => he
  | _, _, _, .headBeta _ A body arg rest k, he =>
      have hnext : foldApps (instantiate0 arg body) rest = omegaXT := by
        have hsp := congrArg appsSpine he
        rw [appsSpine_foldApps_beta] at hsp
        have hom : appsSpine omegaXT =
            (.lam loopXT (.app (.bvar 0) (.bvar 0)),
             [.lam loopXT (.app (.bvar 0) (.bvar 0))]) := rfl
        rw [hom] at hsp
        injection hsp with h1 h2
        injection h1 with hA hbody
        injection h2 with harg hrest
        subst hA hbody harg hrest
        rfl
      machineRed_omegaXT_eq k hnext
  | _, _, _, .headZeta _ A value body rest _, he => by
      have hsp := congrArg appsSpine he
      rw [appsSpine_foldApps_zeta] at hsp
      exact nomatch hsp
  | _, _, _, .headDelta _ r ls _ _ rest _ _ _ _, he => by
      have hsp := congrArg appsSpine he
      rw [appsSpine_foldApps_const] at hsp
      exact nomatch hsp

/-- **Negative WHNF Eventuality Pin on `omegaXT`:**
    `.whnfAt A omegaXT` never eventually accepts any `.inferredWhnf A w` at any
    budget in any environment `E`. -/
theorem not_whnf_eventual_omegaXT (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A w : Expr Nat) :
    ¬ TaskEventuallyAccepts ⟨E, n, Γ⟩ (.whnfAt A omegaXT) (.inferredWhnf A w) := by
  intro hev
  rcases (RM025_whnf_eventual_iff E n Γ A omegaXT w).mp hev with ⟨⟨k⟩, hdone⟩
  have hw := machineRed_omegaXT_eq k rfl
  subst hw
  exact nomatch hdone

/-- Helper: `.const 62 [.succ .zero]` has a nonempty level spine, so `inferCert`
    never succeeds on it at any fuel `f`. -/
theorem inferCert_const62_no (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (f : Nat) :
    ∀ c, inferCert E n f Γ (.const 62 [.succ .zero]) ≠ .ok c := by
  cases f with
  | zero => intro c h; exact nomatch h
  | succ f₀ => intro c h; exact nomatch h

/-- Helper: if `inferCert` never succeeds on `fn`, it never succeeds on `.app fn arg`. -/
theorem inferCert_app_fn_no {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {fn : Expr Nat}
    (hfn : ∀ f c, inferCert E n f Γ fn ≠ .ok c) (arg : Expr Nat) (f : Nat) :
    ∀ c, inferCert E n f Γ (.app fn arg) ≠ .ok c := by
  cases f with
  | zero => intro c h; exact nomatch h
  | succ f₀ =>
      intro c h
      simp only [inferCert] at h
      split at h
      · exact nomatch h
      · next Tf dfn heq => exact absurd heq (hfn f₀ ⟨Tf, dfn⟩)

/-- Helper: if `inferCert` never succeeds on `A`, `checkCert` never succeeds on `e` at `A`. -/
theorem checkCert_expected_no {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat}
    (hA : ∀ f c, inferCert E n f Γ A ≠ .ok c) (e : Expr Nat) (f : Nat) :
    ∀ c, checkCert E n f Γ e A ≠ .ok c := by
  cases f with
  | zero => intro c h; exact nomatch h
  | succ f₀ =>
      intro c h
      simp only [checkCert] at h
      split at h
      · exact nomatch h
      · next TA dA heq => exact absurd heq (hA f₀ ⟨TA, dA⟩)

/-- `inferCert` never succeeds on `loopXT = .app loopFT (.bvar 0)` at any fuel `f`. -/
theorem inferCert_loopXT_no (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (f : Nat) :
    ∀ c, inferCert E n f Γ loopXT ≠ .ok c :=
  inferCert_app_fn_no
    (inferCert_app_fn_no
      (inferCert_app_fn_no (inferCert_const62_no E n Γ) loopMotTT) loopMinTT)
    (.bvar 0) f

/-- **Negative Check Eventuality Pin on `omegaXT` at `loopXT`:**
    `.check omegaXT loopXT` never eventually accepts `.checked` at any budget,
    and `Normalizing E n Γ omegaXT loopXT` is false. -/
theorem not_normalizing_and_not_check_eventual_omegaXT (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    ¬ Normalizing E n Γ omegaXT loopXT ∧
    ¬ TaskEventuallyAccepts ⟨E, n, Γ⟩ (.check omegaXT loopXT) .checked := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨u, hevA⟩, _⟩
    rcases (RM025_infer_eventual_iff E n Γ loopXT (.sort u)).mp hevA with
      ⟨fA, c, hok, _⟩
    exact inferCert_loopXT_no E n Γ fA c hok
  · intro hev
    rcases (RM025_check_eventual_iff E n Γ omegaXT loopXT).mp hev with ⟨f, c, hok⟩
    exact checkCert_expected_no (inferCert_loopXT_no E n Γ) omegaXT f c hok

/-- The unrestricted `normalization_full` wall is refuted on `eraseEnv pinLoopEnvA`
    at `omegaXT : loopXT` (`omegaT_pinLoop_typed`, `RcicNormalizingFalsePinLoop.lean`),
    confirming why `Normalizing` must remain an explicit module-boundary hypothesis (R3). -/
theorem not_normalization_full : ¬ normalization_full := by
  intro hfull
  have hW : EnvWfT (eraseEnv pinLoopEnvA) := pinLoopEraseWfT
  have hΓ : CtxWfT (eraseEnv pinLoopEnvA) 1 loopΓ :=
    .assumption [] loopTyT .zero .nil loopTyT_ty
  have hty : HasTyT (eraseEnv pinLoopEnvA) 1 loopΓ omegaXT loopXT :=
    omegaT_pinLoop_typed
  exact (not_normalizing_and_not_check_eventual_omegaXT (eraseEnv pinLoopEnvA) 1 loopΓ).1
    (hfull (eraseEnv pinLoopEnvA) 1 loopΓ omegaXT loopXT hW hΓ hty)

/-! ## 6. Non-vacuity Inhabitant Pins (R3 teeth) -/

/-- **Pin 1 (`CheckSlice` / `Normalizing` multi-redex inhabitant):**
    `slicePinTerm = let X : Sort 1 := Sort 0 in (λ y : Sort 1. y) X`
    checked against `slicePinType = (λ Z : Sort 2. Z) (Sort 1)`, where
    `slicePinTerm` synthesizes `Sort 1` via `.letE` + `.app` + `.lam` + `.bvar` + `.sort`
    and `slicePinType` β-reduces via `MachineRed.headBeta` to `Sort 1`. -/
def slicePinTerm : Expr Nat :=
  .letE (.sort (.succ .zero)) (.sort .zero)
    (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.bvar 0))

def slicePinType : Expr Nat :=
  .app (.lam (.sort (.succ (.succ .zero))) (.bvar 0)) (.sort (.succ .zero))

/-- `CheckSlice` derivation for `(slicePinTerm, slicePinType)`. -/
theorem pin_checkSlice_inhabitant :
    CheckSlice emptyEnv 0 [] slicePinTerm slicePinType := by
  refine ⟨⟨.succ (.succ .zero), ?_⟩, ⟨.sort (.succ .zero), ?_, ?_⟩⟩
  · -- `slicePinType : Sort 2` via `.app` + `.lam` + `.bvar` + `.sort`
    have hlam : InferSlice emptyEnv 0 []
        (.lam (.sort (.succ (.succ .zero))) (.bvar 0))
        (.pi (.sort (.succ (.succ .zero))) (.sort (.succ (.succ .zero)))) :=
      .lam [] (.sort (.succ (.succ .zero))) (.bvar 0) (.sort (.succ (.succ .zero)))
        (.succ (.succ (.succ .zero)))
        (.sort [] (.succ (.succ .zero)))
        (.bvar [.assumption (.sort (.succ (.succ .zero)))] 0
          (.sort (.succ (.succ .zero))) rfl)
    exact .app []
      (.lam (.sort (.succ (.succ .zero))) (.bvar 0))
      (.sort (.succ .zero))
      (.pi (.sort (.succ (.succ .zero))) (.sort (.succ (.succ .zero))))
      (.sort (.succ (.succ .zero)))
      (.sort (.succ (.succ .zero)))
      (.sort (.succ (.succ .zero)))
      hlam
      ⟨.refl [] _⟩
      (.sort [] (.succ .zero))
      (whnfJoin_of_done emptyEnv 0 [] rfl)
  · -- `slicePinTerm : Sort 1` via `.letE` + `.app` + `.lam` + `.bvar` + `.sort`
    let Γ₁ : LCtx := [.letBinding (.sort (.succ .zero)) (.sort .zero)]
    have hbody : InferSlice emptyEnv 0 Γ₁
        (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.bvar 0))
        (.sort (.succ .zero)) :=
      .app Γ₁
        (.lam (.sort (.succ .zero)) (.bvar 0))
        (.bvar 0)
        (.pi (.sort (.succ .zero)) (.sort (.succ .zero)))
        (.sort (.succ .zero))
        (.sort (.succ .zero))
        (.sort (.succ .zero))
        (.lam Γ₁ (.sort (.succ .zero)) (.bvar 0) (.sort (.succ .zero))
          (.succ (.succ .zero))
          (.sort Γ₁ (.succ .zero))
          (.bvar (.assumption (.sort (.succ .zero)) :: Γ₁) 0
            (.sort (.succ .zero)) rfl))
        ⟨.refl Γ₁ _⟩
        (.bvar Γ₁ 0 (.sort (.succ .zero)) rfl)
        (whnfJoin_of_done emptyEnv 0 Γ₁ rfl)
    exact .letE [] (.sort (.succ .zero)) (.sort .zero)
      (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.bvar 0))
      (.sort (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort [] (.succ .zero))
      (.sort [] .zero)
      (whnfJoin_of_done emptyEnv 0 [] rfl)
      hbody
  · -- `WhnfJoin emptyEnv 0 [] (Sort 1) slicePinType` via 1-step `headBeta`
    refine ⟨.sort (.succ .zero), ⟨.refl [] (.sort (.succ .zero))⟩, ⟨?_⟩, rfl⟩
    exact .headBeta [] (.sort (.succ (.succ .zero))) (.bvar 0)
      (.sort (.succ .zero)) [] (.refl [] (.sort (.succ .zero)))

/-- `Normalizing` inhabitant discharged by `normalizing_of_checkSlice`. -/
theorem pin_normalizing_inhabitant :
    Normalizing emptyEnv 0 [] slicePinTerm slicePinType :=
  normalizing_of_checkSlice pin_checkSlice_inhabitant

/-- Non-vacuous execution pin for `pin_normalizing_inhabitant`:
    `.check slicePinTerm slicePinType` refuses `[rcic_infer_fuel]` at inner
    budget `1`, accepts `.checked` at inner budget `5`, and satisfies
    `TaskEventuallyAccepts ⟨emptyEnv, 0, []⟩ (.check slicePinTerm slicePinType) .checked`. -/
theorem pin_checkSlice_normalizing_eventually_accepted :
    runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .check slicePinTerm slicePinType, 1⟩ =
      .done (.refused "[rcic_infer_fuel]") ∧
    runRawR 1 ⟨⟨emptyEnv, 0, []⟩, .check slicePinTerm slicePinType, 5⟩ =
      .done (.accepted .checked) ∧
    TaskEventuallyAccepts ⟨emptyEnv, 0, []⟩
      (.check slicePinTerm slicePinType) .checked :=
  ⟨rfl, rfl, RM025_checkSlice_eventually_accepted pin_checkSlice_inhabitant⟩

/-- **Pin 2 (`TypedState` lifting inhabitant):**
    lifting `pinTypedCheckZeroState` (`pin_typedRun_check_zero`, `RcicTypedMachineAccept.lean:309`)
    through `RM025_typedState_normalizing_eventually_accepted`. -/
theorem pin_normalizing_natZero :
    Normalizing natEnvU 1 [] (.const 1 []) (.const 0 []) :=
  normalizing_of_checkSlice
    ⟨⟨.succ .zero, .const [] 0 natFamMember rfl rfl⟩,
     ⟨.const 0 [], .const [] 1 natZeroMember rfl rfl,
      whnfJoin_of_done natEnvU 1 [] rfl⟩⟩

def pin_typedState_check_zero_eventually_accepted :
    HasTyT natEnvU 1 [] (.const 1 []) (.const 0 []) ×'
      PProd (Nonempty (HasTy natEnvU 1 [] (.const 1 []) (.const 0 [])))
        (TaskEventuallyAccepts pinTypedCheckZeroState.ambient
          (.check (.const 1 []) (.const 0 [])) .checked) :=
  RM025_typedState_normalizing_eventually_accepted 1 pinTypedCheckZeroState
    (.const 1 []) (.const 0 []) rfl rfl pin_typedRun_check_zero pin_normalizing_natZero

/-- **Pin 3 (`RcicNormalizingErase` / `TmChainA` lifting inhabitant):**
    concrete 1-step `.beta` `TmChainA` on `ExprA` (`(λ x : Sort 1. x) (Sort 0) → Sort 0`)
    erased via `RM025_tmChainA_whnf_eventual` to `.whnfAt` positive eventuality and `WhnfJoin`. -/
def pinBetaChainA :
    TmChainA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.sort (.succ .zero))
      (.app (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.sort .zero))
      (.sort .zero) :=
  have hS0 : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.sort .zero) (.sort (.succ .zero)) := .sort [] .zero
  have hS1 : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort [] (.succ .zero)
  have hbody : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0
      [.assumption (.sort (.succ .zero))] (.bvar 0) (.sort (.succ .zero)) :=
    .bvar [.assumption (.sort (.succ .zero))] 0 (.sort (.succ .zero))
      (.succ (.succ .zero)) rfl
      (.sort [.assumption (.sort (.succ .zero))] (.succ .zero))
  have hlam : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0))
      (.pi (.sort (.succ .zero)) (.succ (.succ .zero))
        (.sort (.succ .zero)) (.succ (.succ .zero))) :=
    .lam [] (.sort (.succ .zero)) (.succ (.succ .zero))
      (.bvar 0) (.sort (.succ .zero)) (.succ (.succ .zero)) hS1
      (.sort [.assumption (.sort (.succ .zero))] (.succ .zero)) hbody
  have happ : HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.app (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.sort .zero))
      (.sort (.succ .zero)) :=
    .app [] (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.sort .zero)
      (.sort (.succ .zero)) (.sort (.succ .zero)) (.succ (.succ .zero))
      (.succ (.succ .zero)) (.succ (.succ .zero))
      (.sort [.assumption (.sort (.succ .zero))] (.succ .zero))
      hS1 hlam hS0
  have hstep : TyHRedA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.app (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.sort .zero))
      (.sort .zero) (.sort (.succ .zero)) :=
    .beta [] (.sort (.succ .zero)) (.succ (.succ .zero))
      (.bvar 0) (.sort .zero) (.sort (.succ .zero)) hS1 hbody hS0 hS0
  .cons _ _ _ happ hstep (.refl (.sort .zero) hS0)

theorem pin_tmChainA_beta_eventual :
    TaskEventuallyAccepts ⟨eraseEnv emptyEnvA, 0, []⟩
      (.whnfAt (.sort (.succ .zero))
        (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero)))
      (.inferredWhnf (.sort (.succ .zero)) (.sort .zero)) ∧
    WhnfJoin (eraseEnv emptyEnvA) 0 []
      (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
      (.sort .zero) :=
  RM025_tmChainA_whnf_eventual pinBetaChainA ⟨trivial, trivial⟩ rfl

end Rcic.Machine.Eventual
