import rcic.RcicNativeTypedModelFund
import rcic.RcicNativeTypedModelProbe

/-!
# Typed-model substitution — `ApproxT` under `instantiate`

Port of `RcicNativePiModelDeltaIota`'s semantic substitution lemma
(`approxDI_subst_intro`/`approxDI_subst_elim`/`approxDI_subst_iff`, itself the
δ/ι form of `RcicNativePiModelIdeal`'s `approxI_subst_intro`/`_elim`) to the
typed-demand model `ApproxT` of `RcicNativeTypedModel`.

The statement is the typed analogue: an approximation of `e` at the
inserted environment `EnvT.insert ρ j (denT E (EnvT.drop ρ j) r)` transfers to
an approximation of `instantiate j (lift 0 j r) e` at `ρ`, and conversely.
The `pi`/`lam` constructors' `CTyS` side conditions are demand-set properties
(the compacts `u ∈ s.1` and the domain code `a` are untouched by expression
substitution), so they pass through both directions verbatim.

Contents:
* **`EnvT.drop` algebra** — `insert_lt`/`insert_self`/`insert_gt`,
  `drop_zero`/`drop_cons`/`drop_succ`/`insert_drop_one`: the `EnvI` identities
  of `RcicNativePiModelIdeal`, verbatim on `CptT` environments.
* **Closed-term environment transfer** — `approxT_const_env`,
  `approxT_natExpand_env`: constants and literals approximate the same
  compacts at every environment.
* **`approxT_liftN_intro`/`approxT_liftN_elim`** — `j`-fold lift across
  `EnvT.drop`, the `i = j` arm of the substitution lemma.
* **`approxT_subst_intro`/`approxT_subst_elim`/`approxT_subst_iff`** — the
  substitution theorem; `approxT_subst0_iff` is the `j = 0`/`EnvT.cons`
  specialization.
* **Finite demand** — `EnvT.update` algebra (`update_self`/`update_ne`/
  `cons_update`/`update_cons_zero`), `approxT_mono_update`, and the typed
  port of `approxDI_factor_list`/`_args`/`approxT_factor`: every derivation
  reads only finitely many compacts of any one variable.
* **`ModelSubstFactorT`** — the exact `RcicNativeTypedModelTypingFin`
  (`agy/typing-fin`, #7738's consumer shape) structure, and the
  unconditional instance `modelSubstFactorT_approxT` for
  `ctxModelT_approxT`: `subst0_intro` is `subst0_iff` + environment
  monotonicity (`demandT us ≤ denT arg` from `∀ u ∈ us, ApproxT ρ arg u`),
  `subst0_factor` is `subst0_iff` + `approxT_factor` at `j = 0`.  No typing
  premise on `arg` — this is the layer that survives #7738's
  `not_argTypedFinAt_polyId` obstruction.  `modelSubstFactorT_witness_polyId`
  is the non-degenerate witness: the identity's contractum at the real
  argument `cexP` (`Π (X : Sort 0). Sort 0`) factors through a demand list
  containing `.pi .bot []`.

`closure_claim = 0`: additive layer, no existing statements touched.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

/-! ## `EnvT.drop` and the insert algebra (`EnvI` port) -/

/-- Inserting below the cutoff leaves the entry untouched. -/
theorem EnvT.insert_lt {ρ : EnvT} {k i : Nat} (S : CptT → Prop) (h : i < k) :
    EnvT.insert ρ k S i = ρ i := by
  simp [EnvT.insert, h]

theorem EnvT.insert_self (ρ : EnvT) (k : Nat) (S : CptT → Prop) :
    EnvT.insert ρ k S k = S := by
  simp [EnvT.insert]

theorem EnvT.insert_gt {ρ : EnvT} {k i : Nat} (S : CptT → Prop) (h : k < i) :
    EnvT.insert ρ k S i = ρ (i - 1) := by
  have h1 : ¬ i < k := Nat.not_lt.mpr (Nat.le_of_lt h)
  have h2 : i ≠ k := Nat.ne_of_gt h
  simp [EnvT.insert, h1, h2]

/-- Drop the first `k` entries (`EnvI.drop`). -/
def EnvT.drop (ρ : EnvT) (k : Nat) : EnvT := fun i => ρ (i + k)

theorem EnvT.drop_zero (ρ : EnvT) : EnvT.drop ρ 0 = ρ := rfl

theorem EnvT.drop_cons (S : CptT → Prop) (ρ : EnvT) (k : Nat) :
    EnvT.drop (EnvT.cons S ρ) (k + 1) = EnvT.drop ρ k := by
  funext i
  show EnvT.cons S ρ (i + (k + 1)) = ρ (i + k)
  rw [show i + (k + 1) = (i + k) + 1 from rfl]
  rfl

theorem EnvT.drop_succ (ρ : EnvT) (k : Nat) :
    EnvT.drop ρ (k + 1) = EnvT.drop (EnvT.drop ρ 1) k := rfl

theorem EnvT.insert_drop_one (ρ : EnvT) : EnvT.insert (EnvT.drop ρ 1) 0 (ρ 0) = ρ := by
  funext i
  cases i with
  | zero => rw [EnvT.insert_self]
  | succ i => rw [EnvT.insert_gt _ (Nat.succ_pos i)]; rfl

/-! ## Closed-term environment transfer -/

/-- A constant head's approximations do not depend on the environment. -/
theorem approxT_const_env {E : ResolvedEnv} (ρ ρ' : EnvT) {r : Nat} {ls : List Level}
    {c : CptT} (h : ApproxT E ρ (.const r ls) c) :
    ApproxT E ρ' (.const r ls) c := by
  cases h with
  | bot => exact .bot _ _
  | const _ _ _ hrigid hnp => exact .const _ _ _ hrigid hnp
  | delta hd hh => exact .delta hd hh
  | recursor ls hnp hpre hflds hh => exact .recursor ls hnp hpre hflds hh
  | recursorProp ls hP hpre hh => exact .recursorProp ls hP hpre hh

/-- A literal's expansion is closed, so its approximations transfer across
    environments (`approxDI_natExpand_env`). -/
theorem approxT_natExpand_env {E : ResolvedEnv} (ρ ρ' : EnvT) :
    ∀ (t : Nat) {c : CptT},
      ApproxT E ρ (natExpand t) c → ApproxT E ρ' (natExpand t) c := by
  intro t
  induction t with
  | zero =>
      intro c h
      exact approxT_const_env ρ ρ' h
  | succ t ih =>
      intro c h
      rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩ | ⟨r, args, u, rfl, hf, ha⟩
      · exact .bot _ _
      · exact .app (approxT_const_env ρ ρ' hf) hs (fun u hu => ih (ha u hu))
      · exact .appSpine (approxT_const_env ρ ρ' hf) (ih ha)

/-! ## `j`-fold lifting across `EnvT.drop` (`approxDI_liftN_intro`/`_elim`) -/

theorem approxT_liftN_intro {E : ResolvedEnv} {e : Expr Nat} {c : CptT} :
    ∀ (ρ : EnvT) (j : Nat), ApproxT E (EnvT.drop ρ j) e c →
      ApproxT E ρ (lift 0 j e) c
  | ρ, 0, h => by rw [EnvT.drop_zero] at h; rw [lift_zero_idx]; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx]
      rw [EnvT.drop_succ] at h
      have := approxT_lift_intro (approxT_liftN_intro (EnvT.drop ρ 1) j h) 0 (ρ 0)
      rwa [EnvT.insert_drop_one] at this

theorem approxT_liftN_elim {E : ResolvedEnv} {e : Expr Nat} {c : CptT} :
    ∀ (ρ : EnvT) (j : Nat), ApproxT E ρ (lift 0 j e) c →
      ApproxT E (EnvT.drop ρ j) e c
  | ρ, 0, h => by rw [EnvT.drop_zero]; rw [lift_zero_idx] at h; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx] at h
      rw [EnvT.drop_succ]
      have h' : ApproxT E (EnvT.insert (EnvT.drop ρ 1) 0 (ρ 0))
          (lift 0 1 (lift 0 j e)) c := by
        rwa [EnvT.insert_drop_one]
      exact approxT_liftN_elim (EnvT.drop ρ 1) j (approxT_lift_elim (lift 0 j e) h')

/-! ## Semantic substitution (`approxDI_subst_intro`/`_elim`/`_iff` ported) -/

/-- **Introduction.**  `e`'s approximation at the inserted environment —
    variable `j` reading `r`'s full demand set at `EnvT.drop ρ j` — is
    `instantiate j (lift 0 j r) e`'s approximation at `ρ`.  The `pi`/`lam`
    `CTyS` premises pass through unchanged. -/
theorem approxT_subst_intro {E : ResolvedEnv} {ρ' : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxT E ρ' e c) :
    ∀ (ρ : EnvT) (j : Nat) (r : Expr Nat),
      ρ' = EnvT.insert ρ j (denT E (EnvT.drop ρ j) r) →
      ApproxT E ρ (instantiate j (lift 0 j r) e) c := by
  induction h with
  | bot => intro ρ j r _; exact .bot _ _
  | @bvar ρ' i c h =>
      intro ρ j r hρ
      subst hρ
      simp only [instantiate]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        rw [EnvT.insert_self] at h
        exact approxT_liftN_intro ρ i h
      · rw [if_neg hij]
        by_cases hlt : j < i
        · rw [if_pos hlt]
          rw [EnvT.insert_gt _ hlt] at h
          exact .bvar h
        · rw [if_neg hlt]
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rw [EnvT.insert_lt _ hil] at h
          exact .bvar h
  | sort => intro ρ j r _; exact .sort _ _
  | pi _ hT _ ihA ihf =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .pi (ihA ρ j r hρ) hT (fun s hs => ihf s hs _ (j + 1) r
        (by rw [hρ, EnvT.cons_insert, EnvT.drop_cons]))
  | lam _ hT hnt _ ihA ihb =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .lam (ihA ρ j r hρ) hT hnt (fun s hs => ihb s hs _ (j + 1) r
        (by rw [hρ, EnvT.cons_insert, EnvT.drop_cons]))
  | app _ hs _ ihf iha =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .app (ihf ρ j r hρ) hs (fun u hu => iha u hu ρ j r hρ)
  | const _ _ _ hrigid hnp => intro _ _ _ _; exact .const _ _ _ hrigid hnp
  | delta hdelta h _ => intro _ _ _ _; exact .delta hdelta h
  | recursor ls hnp hpre hflds h _ => intro _ _ _ _; exact .recursor ls hnp hpre hflds h
  | recursorProp ls hP hpre h _ => intro _ _ _ _; exact .recursorProp ls hP hpre h
  | appSpine _ _ ihf iha =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .appSpine (ihf ρ j r hρ) (iha ρ j r hρ)
  | letE _ ih =>
      intro ρ j r hρ
      have := ih ρ j r hρ
      simp only [instantiate] at this ⊢
      exact .letE this
  | lit _ ih =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .lit (by have := ih ρ j r hρ; rwa [natExpand_instantiate] at this)

/-- **Elimination.**  An approximation of the instantiated term already lived
    at the inserted environment. -/
theorem approxT_subst_elim {E : ResolvedEnv} :
    (e : Expr Nat) → ∀ {ρ : EnvT} {j : Nat} {r : Expr Nat} {c : CptT},
      ApproxT E ρ (instantiate j (lift 0 j r) e) c →
      ApproxT E (EnvT.insert ρ j (denT E (EnvT.drop ρ j) r)) e c
  | .bvar i, ρ, j, r, c, h => by
      simp only [instantiate] at h
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at h
        exact .bvar (by rw [EnvT.insert_self]; exact approxT_liftN_elim ρ i h)
      · rw [if_neg hij] at h
        by_cases hlt : j < i
        · rw [if_pos hlt] at h
          rcases approxT_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [EnvT.insert_gt _ hlt]; exact h0)
        · rw [if_neg hlt] at h
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rcases approxT_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [EnvT.insert_lt _ hil]; exact h0)
  | .sort l, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxT_sort_inv h with rfl | rfl
      · exact .bot _ _
      · exact .sort _ _
  | .const k ls, ρ, j, r, c, h => by
      simp only [instantiate] at h
      exact approxT_const_env ρ _ h
  | .app f a, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩
        | ⟨k, args, u, rfl, hf, ha⟩
      · exact .bot _ _
      · exact .app (approxT_subst_elim f hf) hs
          (fun u hu => approxT_subst_elim a (ha u hu))
      · exact .appSpine (approxT_subst_elim f hf) (approxT_subst_elim a ha)
  | .lam A b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxT_lam_inv h with rfl | ⟨a, g, rfl, hA, hnt, hg⟩
      · exact .bot _ _
      · exact .lam (approxT_subst_elim A hA) (fun s hs => (hg s hs).1) hnt
          (fun s hs => by
            rw [EnvT.cons_insert, ← EnvT.drop_cons (demandT s.1) ρ j]
            exact approxT_subst_elim b ((hg s hs).2))
  | .pi A B, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxT_pi_inv h with rfl | ⟨a, f, rfl, hA, hf⟩
      · exact .bot _ _
      · exact .pi (approxT_subst_elim A hA) (fun s hs => (hf s hs).1)
          (fun s hs => by
            rw [EnvT.cons_insert, ← EnvT.drop_cons (demandT s.1) ρ j]
            exact approxT_subst_elim B ((hf s hs).2))
  | .letE A v b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      cases h with
      | bot => exact .bot _ _
      | letE h =>
          rcases approxT_app_inv h with rfl | ⟨g, s, rfl, hf, hs, ha⟩
            | ⟨k, args, u, rfl, hf, ha⟩
          · exact .letE (.bot _ _)
          · rcases approxT_lam_inv hf with h1 | ⟨a', g', e, hA', hnt', hg'⟩
            · cases h1
            · injection e with eg
              subst eg
              rw [lift_shift_comp_idx] at hg'
              exact .letE (.app
                (.lam (approxT_subst_elim A hA')
                  (fun s' hs' => (hg' s' hs').1) hnt'
                  (fun s' hs' => by
                    rw [EnvT.cons_insert, ← EnvT.drop_cons (demandT s'.1) ρ j]
                    exact approxT_subst_elim b ((hg' s' hs').2)))
                hs
                (fun u hu => approxT_subst_elim v (ha u hu)))
          · rcases approxT_lam_inv hf with h1 | ⟨a', g', e, _, _, _⟩
            · cases h1
            · cases e
  | .lit t, ρ, j, r, c, h => by
      simp only [instantiate] at h
      cases h with
      | bot => exact .bot _ _
      | lit h' => exact .lit (approxT_natExpand_env ρ _ t h')

/-- The substitution equivalence (`approxDI_subst_iff`). -/
theorem approxT_subst_iff (E : ResolvedEnv) (ρ : EnvT) (j : Nat) (a e : Expr Nat)
    (c : CptT) :
    ApproxT E ρ (instantiate j (lift 0 j a) e) c ↔
      ApproxT E (EnvT.insert ρ j (denT E (EnvT.drop ρ j) a)) e c :=
  ⟨approxT_subst_elim e, fun h => approxT_subst_intro h ρ j a rfl⟩

/-- Beta at the outermost binder (`approxI_subst_iff` at `j = 0`): the
    `ReadbackModelInv`/`WhStepCK` `ctxModelT` arm's shape. -/
theorem approxT_subst0_iff (E : ResolvedEnv) (ρ : EnvT) (a e : Expr Nat) (c : CptT) :
    ApproxT E ρ (instantiate 0 a e) c ↔
      ApproxT E (EnvT.cons (denT E ρ a) ρ) e c := by
  have h0 : instantiate 0 (lift 0 0 a) e = instantiate 0 a e := by rw [lift_zero_idx]
  have h1 : EnvT.insert ρ 0 (denT E (EnvT.drop ρ 0) a) =
      EnvT.cons (denT E ρ a) ρ := by
    rw [EnvT.insert_zero, EnvT.drop_zero]
  rw [← h0, ← h1]
  exact approxT_subst_iff E ρ 0 a e c

/-! ## Finite demand — the typed `approxDI_factor`

Port of `RcicNativePiModelDeltaIota`'s `approxDI_mono_update` /
`approxDI_factor_list` / `approxDI_factor_args` / `approxDI_factor` to
`ApproxT`: every derivation uses only finitely many compacts of any one
variable `j`.  `const`/`delta`/`recursor`/`recursorProp` do not read `ρ`,
so their demand on `j` is `[]`; the `pi`/`lam` `CTyS` side conditions and
the `lam` non-triviality witness are environment-independent and pass
through verbatim. -/

/-- Replace entry `j`. -/
def EnvT.update (ρ : EnvT) (j : Nat) (S : CptT → Prop) : EnvT :=
  fun i => if i = j then S else ρ i

theorem EnvT.update_self (ρ : EnvT) (j : Nat) (S : CptT → Prop) :
    EnvT.update ρ j S j = S := by
  show (if j = j then S else ρ j) = S
  rw [if_pos rfl]

theorem EnvT.update_ne {ρ : EnvT} {j i : Nat} (S : CptT → Prop) (h : i ≠ j) :
    EnvT.update ρ j S i = ρ i := by
  show (if i = j then S else ρ i) = ρ i
  rw [if_neg h]

theorem EnvT.cons_update (S T : CptT → Prop) (ρ : EnvT) (j : Nat) :
    EnvT.cons S (EnvT.update ρ j T) = EnvT.update (EnvT.cons S ρ) (j + 1) T := by
  funext i
  cases i with
  | zero =>
      show S = EnvT.update (EnvT.cons S ρ) (j + 1) T 0
      rw [EnvT.update_ne _ (Nat.succ_ne_zero j).symm]
      rfl
  | succ i =>
      show EnvT.update ρ j T i = EnvT.update (EnvT.cons S ρ) (j + 1) T (i + 1)
      by_cases h : i = j
      · subst h
        rw [EnvT.update_self, EnvT.update_self]
      · rw [EnvT.update_ne _ h, EnvT.update_ne _ (fun h' => h (Nat.succ.inj h'))]
        rfl

/-- Updating index `0` of a `cons`ed environment is re-`cons`ing. -/
theorem EnvT.update_cons_zero (S T : CptT → Prop) (ρ : EnvT) :
    EnvT.update (EnvT.cons S ρ) 0 T = EnvT.cons T ρ := by
  funext i
  cases i with
  | zero =>
      rw [EnvT.update_self]
      rfl
  | succ i =>
      rw [EnvT.update_ne _ (Nat.succ_ne_zero i)]
      rfl

theorem approxT_mono_update {E : ResolvedEnv} {ρ : EnvT} {j : Nat} {e : Expr Nat}
    {c : CptT} (us us' : List CptT) (hsub : ∀ u ∈ us, u ∈ us')
    (h : ApproxT E (EnvT.update ρ j (demandT us)) e c) :
    ApproxT E (EnvT.update ρ j (demandT us')) e c :=
  approxT_mono_env (fun i d hd => by
    by_cases hij : i = j
    · subst hij
      rw [EnvT.update_self] at hd ⊢
      exact hsub d hd
    · rw [EnvT.update_ne _ hij] at hd ⊢
      exact hd) h

/-- Collecting the demands of the finitely many sub-derivations under a binder. -/
theorem approxT_factor_list {E : ResolvedEnv} {ρ : EnvT} {j : Nat} {B : Expr Nat} :
    (f : List (List CptT × CptT)) →
    (∀ s ∈ f, ∃ us : List CptT, (∀ u ∈ us, ρ j u) ∧
      ApproxT E (EnvT.cons (demandT s.1) (EnvT.update ρ j (demandT us))) B s.2) →
    ∃ us : List CptT, (∀ u ∈ us, ρ j u) ∧
      ∀ s ∈ f, ApproxT E (EnvT.cons (demandT s.1) (EnvT.update ρ j (demandT us))) B s.2
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | s :: rest, ih => by
      obtain ⟨us₁, h₁, hs⟩ := ih s (List.mem_cons_self _ _)
      obtain ⟨us₂, h₂, hrest⟩ :=
        approxT_factor_list rest (fun s' hs' => ih s' (List.mem_cons_of_mem _ hs'))
      refine ⟨us₁ ++ us₂, fun u hu => ?_, fun s' hs' => ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact h₁ u hu
        · exact h₂ u hu
      · cases List.mem_cons.mp hs' with
        | inl heq =>
            subst heq
            rw [EnvT.cons_update] at hs ⊢
            exact approxT_mono_update us₁ _ (fun u hu => List.mem_append.mpr (Or.inl hu)) hs
        | inr hs'' =>
            have := hrest s' hs''
            rw [EnvT.cons_update] at this ⊢
            exact approxT_mono_update us₂ _ (fun u hu => List.mem_append.mpr (Or.inr hu)) this

/-- Collecting the demands of the finitely many argument derivations of an
    application step. -/
theorem approxT_factor_args {E : ResolvedEnv} {ρ : EnvT} {j : Nat} {a : Expr Nat} :
    (us0 : List CptT) →
    (∀ u ∈ us0, ∃ us : List CptT, (∀ w ∈ us, ρ j w) ∧
      ApproxT E (EnvT.update ρ j (demandT us)) a u) →
    ∃ us : List CptT, (∀ w ∈ us, ρ j w) ∧
      ∀ u ∈ us0, ApproxT E (EnvT.update ρ j (demandT us)) a u
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | u :: rest, ih => by
      obtain ⟨us₁, h₁, hu⟩ := ih u (List.mem_cons_self _ _)
      obtain ⟨us₂, h₂, hrest⟩ :=
        approxT_factor_args rest (fun u' hu' => ih u' (List.mem_cons_of_mem _ hu'))
      refine ⟨us₁ ++ us₂, fun w hw => ?_, fun u' hu' => ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact h₁ w hw
        · exact h₂ w hw
      · cases List.mem_cons.mp hu' with
        | inl heq =>
            subst heq
            exact approxT_mono_update us₁ _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hu
        | inr hu'' =>
            exact approxT_mono_update us₂ _ (fun w hw => List.mem_append.mpr (Or.inr hw))
              (hrest u' hu'')

/-- Finite demand on `ApproxT`: every derivation uses only finitely many compacts of
    any one variable `j`. -/
theorem approxT_factor {E : ResolvedEnv} {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxT E ρ e c) (j : Nat) :
    ∃ us : List CptT, (∀ u ∈ us, ρ j u) ∧
      ApproxT E (EnvT.update ρ j (demandT us)) e c := by
  induction h generalizing j with
  | bot => exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .bot _ _⟩
  | @bvar ρ i c h =>
      by_cases hij : i = j
      · subst hij
        refine ⟨[c], fun u hu => ?_, .bvar ?_⟩
        · have heq := List.mem_singleton.mp hu; subst heq; exact h
        · rw [EnvT.update_self]; exact List.mem_singleton.mpr rfl
      · exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim,
          .bvar (by rw [EnvT.update_ne _ hij]; exact h)⟩
  | sort => exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .sort _ _⟩
  | @pi ρ A B a f _ hT _ ihA ihf =>
      obtain ⟨usA, hA₁, hA₂⟩ := ihA j
      obtain ⟨usB, hB₁, hB₂⟩ := approxT_factor_list f (fun s hs => by
        obtain ⟨us, h₁, h₂⟩ := ihf s hs (j + 1)
        exact ⟨us, h₁, by rw [EnvT.cons_update]; exact h₂⟩)
      refine ⟨usA ++ usB, fun u hu => ?_, .pi ?_ hT ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hA₁ u hu
        · exact hB₁ u hu
      · exact approxT_mono_update usA _ (fun u hu => List.mem_append.mpr (Or.inl hu)) hA₂
      · intro s hs
        have := hB₂ s hs
        rw [EnvT.cons_update] at this ⊢
        exact approxT_mono_update usB _ (fun u hu => List.mem_append.mpr (Or.inr hu)) this
  | @lam ρ A b a g _ hT hnt _ ihA ihb =>
      obtain ⟨usA, hA₁, hA₂⟩ := ihA j
      obtain ⟨usB, hB₁, hB₂⟩ := approxT_factor_list g (fun s hs => by
        obtain ⟨us, h₁, h₂⟩ := ihb s hs (j + 1)
        exact ⟨us, h₁, by rw [EnvT.cons_update]; exact h₂⟩)
      refine ⟨usA ++ usB, fun u hu => ?_, .lam ?_ hT hnt ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hA₁ u hu
        · exact hB₁ u hu
      · exact approxT_mono_update usA _ (fun u hu => List.mem_append.mpr (Or.inl hu)) hA₂
      · intro s hs
        have := hB₂ s hs
        rw [EnvT.cons_update] at this ⊢
        exact approxT_mono_update usB _ (fun u hu => List.mem_append.mpr (Or.inr hu)) this
  | @app ρ f a g s _ hs _ ihf iha =>
      obtain ⟨usf, hf₁, hf₂⟩ := ihf j
      obtain ⟨usa, ha₁, ha₂⟩ := approxT_factor_args s.1 (fun u hu => iha u hu j)
      refine ⟨usf ++ usa, fun w hw => ?_, .app ?_ hs ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact hf₁ w hw
        · exact ha₁ w hw
      · exact approxT_mono_update usf _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hf₂
      · exact fun u hu => approxT_mono_update usa _
          (fun w hw => List.mem_append.mpr (Or.inr hw)) (ha₂ u hu)
  | const _ _ _ hrigid hnp =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .const _ _ _ hrigid hnp⟩
  | delta hdelta h =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .delta hdelta h⟩
  | recursor ls hnp hpre hflds h =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .recursor ls hnp hpre hflds h⟩
  | recursorProp ls hP hpre h =>
      exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .recursorProp ls hP hpre h⟩
  | appSpine _ _ ihf iha =>
      obtain ⟨usf, hf₁, hf₂⟩ := ihf j
      obtain ⟨usa, ha₁, ha₂⟩ := iha j
      refine ⟨usf ++ usa, fun w hw => ?_, .appSpine ?_ ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact hf₁ w hw
        · exact ha₁ w hw
      · exact approxT_mono_update usf _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hf₂
      · exact approxT_mono_update usa _ (fun w hw => List.mem_append.mpr (Or.inr hw)) ha₂
  | letE _ ih =>
      obtain ⟨us, h₁, h₂⟩ := ih j
      exact ⟨us, h₁, .letE h₂⟩
  | lit _ ih =>
      obtain ⟨us, h₁, h₂⟩ := ih j
      exact ⟨us, h₁, .lit h₂⟩

/-! ## `ModelSubstFactorT` at the concrete typed model -/

/-- Unconditional substitution-factorization laws of a `CtxModelT`, stated
    without any typing side condition on `arg` (exact text of the
    `RcicNativeTypedModelTypingFin` structure on `agy/typing-fin` — #7738's
    `fundT_beta_pointwise` and `modelBetaExpandTypedM_of_substFactor` are the
    consumers).  Defined here pending that module's landing; if it lands
    first under this name, delete this copy. -/
structure ModelSubstFactorT {E : ResolvedEnv} (M : CtxModelT E) : Prop where
  subst0_intro : ∀ {ρ : EnvT} {arg body : Expr Nat} {us : List CptT} {c : CptT},
    (∀ u ∈ us, M.Ap ρ arg u) → M.Ap (EnvT.cons (demandT us) ρ) body c →
    M.Ap ρ (instantiate0 arg body) c
  subst0_factor : ∀ {ρ : EnvT} {arg body : Expr Nat} {c : CptT},
    M.Ap ρ (instantiate0 arg body) c →
    ∃ us : List CptT, (∀ u ∈ us, M.Ap ρ arg u) ∧ M.Ap (EnvT.cons (demandT us) ρ) body c

/-- **The `ModelSubstFactorT` instance for `ApproxT`** (`ctxModelT_approxT`),
    unconditional.  `subst0_intro`: a body denotation under the demand
    environment transfers to the reduct — `demandT us ≤ denT ρ arg` holds by
    the `∀ u ∈ us, ApproxT ρ arg u` premise, so `approxT_mono_env` weakens to
    the `denT`-inserted environment and `approxT_subst0_iff.mpr` instantiates.
    `subst0_factor`: `approxT_subst0_iff.mp` exposes the body derivation at
    the `denT`-inserted environment, `approxT_factor` at `j = 0` carves its
    finite demand on the argument, and `EnvT.update_cons_zero` rewrites the
    updated environment back to `EnvT.cons (demandT us) ρ`. -/
theorem modelSubstFactorT_approxT (E : ResolvedEnv) :
    ModelSubstFactorT (ctxModelT_approxT E) where
  subst0_intro {ρ arg body us c} hus hb :=
    (approxT_subst0_iff E ρ arg body c).mpr
      (approxT_mono_env (fun i v hv => by
        cases i with
        | zero => exact hus v hv
        | succ i => exact hv) hb)
  subst0_factor {ρ arg body c} h := by
    have hb := (approxT_subst0_iff E ρ arg body c).mp h
    obtain ⟨us, hus, hb'⟩ := approxT_factor hb 0
    rw [EnvT.update_cons_zero] at hb'
    exact ⟨us, hus, hb'⟩

/-- **Non-degenerate witness** — the polymorphic identity's contractum applied
    at a real argument.  `instantiate0 cexP (.bvar 0)` is the contractum of
    `(λ x. x) cexP`, the last link of `(λ (X : Sort 1) (x : X). x) T t → t`
    with `T := cexP` (`Π (X : Sort 0). Sort 0`, the #7721/#7738 argument
    shape).  `subst0_factor` returns a demand `us` that is not only inhabited
    — the `bvar` inversion forces `.pi .bot [] ∈ us` — so the factorization
    is non-vacuous exactly on the polymorphic-identity argument form whose
    joint typing is unobtainable (`not_argTypedFinAt_polyId`). -/
theorem modelSubstFactorT_witness_polyId (E : ResolvedEnv) (ρ : EnvT) :
    ∃ us : List CptT, .pi .bot [] ∈ us ∧ (∀ u ∈ us, ApproxT E ρ cexP u) ∧
      ApproxT E (EnvT.cons (demandT us) ρ) (.bvar 0) (.pi .bot []) ∧
      ApproxT E ρ (instantiate0 cexP (.bvar 0)) (.pi .bot []) := by
  have hred : ApproxT E ρ (instantiate0 cexP (.bvar 0)) (.pi .bot []) :=
    (approxT_subst0_iff E ρ cexP (.bvar 0) (.pi .bot [])).mpr
      (.bvar (approxT_pi_bot_nil E ρ _ _))
  obtain ⟨us, hus, hb⟩ := (modelSubstFactorT_approxT E).subst0_factor hred
  have hmem : .pi .bot [] ∈ us := by
    rcases approxT_bvar_inv hb with hbot | h0
    · exact CptT.noConfusion hbot
    · exact h0
  exact ⟨us, hmem, hus, hb, hred⟩

#print axioms EnvT.insert_lt
#print axioms EnvT.insert_self
#print axioms EnvT.insert_gt
#print axioms EnvT.drop
#print axioms EnvT.drop_zero
#print axioms EnvT.drop_cons
#print axioms EnvT.drop_succ
#print axioms EnvT.insert_drop_one
#print axioms approxT_const_env
#print axioms approxT_natExpand_env
#print axioms approxT_liftN_intro
#print axioms approxT_liftN_elim
#print axioms approxT_subst_intro
#print axioms approxT_subst_elim
#print axioms approxT_subst_iff
#print axioms approxT_subst0_iff
#print axioms EnvT.update
#print axioms EnvT.update_self
#print axioms EnvT.update_ne
#print axioms EnvT.cons_update
#print axioms EnvT.update_cons_zero
#print axioms approxT_mono_update
#print axioms approxT_factor_list
#print axioms approxT_factor_args
#print axioms approxT_factor
#print axioms ModelSubstFactorT
#print axioms modelSubstFactorT_approxT
#print axioms modelSubstFactorT_witness_polyId

end Rcic.Declarative.NativeValleys.TypedModelAudit
