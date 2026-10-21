import rcic.RcicNativeValleyDecoTransfer

/-!
# RcicNativePiModelIdeal — the ideal-based approximation relation and β-soundness

#7619 (`typedSoundnessAtBot_refuted`) shows that #7613's first-layer `Approx`, with the
singleton ideal `Cpt.down u = (c = u)`, is NOT β-sound: a λ-body may use its variable at
several compacts, and a single-compact step function cannot record that.  Its
`full_argument_body_probe` names the repair: interpret a variable by the argument's FULL
approximation set, and recover the finite step function by finite-demand factorization.

This module is that repair, as NEW additive definitions (#7613's `Approx` is kept):

* `CptI` — compacts whose step functions are BOUNDED steps `List CptI × CptI`: an input is a
  finite set of compacts (the finite demand on the argument), an output one compact.
  No information order and no joins are needed: a demand is a list, and the environment
  interprets a variable by a set of compacts.
* `ApproxI ρ e c` — the approximation relation on raw syntax with set-valued environments
  (`EnvI`); `letE` is the β-redex, `lit` is its expansion.
* `approxI_mono_env` (environments grow), `approxI_factor` (finite demand: any derivation
  uses only finitely many compacts of any one variable), the lift lemmas
  (`approxI_lift_intro`/`_elim`, `approxI_liftN_intro`/`_elim`), the substitution lemmas
  (`approxI_subst_intro`/`_elim`: `⟦e[j := lift 0 j r]⟧_ρ = ⟦e⟧_{ρ[j ↦ ⟦r⟧_{ρ↓j}]}`), and
  **β-soundness `approxI_beta`** and **ζ-soundness `approxI_zeta`** as semantic equalities.
  `natExpand` is closed, so `lit` is sound by construction (`approxI_natExpand_env`).
* `SemEqI`, its congruences for `pi`/`lam`/`app`, and model Π-injectivity `semEqI_pi_inj`.

Recursions: every lemma is by induction on the `ApproxI` derivation (the step-function
lists give finitely many sub-derivations) or on the raw term; the `letE`/`lit` clauses are
handled by the equations `lift`/`instantiate` satisfy on the redex and on `natExpand`
(`natExpand_lift`, `natExpand_instantiate`).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

/-! ### compacts with bounded steps, environments -/

/-- Compacts: `bot`, the collapsed universe, Π with a compact domain and a bounded step
    function, λ as a bounded step function, constant-headed spines. -/
inductive CptI : Type
  | bot : CptI
  | sort : CptI
  | pi : CptI → List (List CptI × CptI) → CptI
  | lam : List (List CptI × CptI) → CptI
  | spine : Nat → List CptI → CptI

/-- Environments: a set of compacts per variable. -/
def EnvI : Type := Nat → CptI → Prop

/-- Extend. -/
def EnvI.cons (S : CptI → Prop) (ρ : EnvI) : EnvI
  | 0 => S
  | i + 1 => ρ i

/-- Insert at position `k`, shifting the entries at or above `k`. -/
def EnvI.insert (ρ : EnvI) (k : Nat) (S : CptI → Prop) : EnvI :=
  fun i => if i < k then ρ i else if i = k then S else ρ (i - 1)

/-- Drop the first `k` entries. -/
def EnvI.drop (ρ : EnvI) (k : Nat) : EnvI := fun i => ρ (i + k)

/-- Replace entry `j`. -/
def EnvI.update (ρ : EnvI) (j : Nat) (S : CptI → Prop) : EnvI :=
  fun i => if i = j then S else ρ i

/-- Pointwise inclusion. -/
def EnvI.le (ρ ρ' : EnvI) : Prop := ∀ i c, ρ i c → ρ' i c

/-- The finite set of a demand. -/
def demand (us : List CptI) : CptI → Prop := fun c => c ∈ us

theorem EnvI.insert_lt {ρ : EnvI} {k i : Nat} (S : CptI → Prop) (h : i < k) :
    EnvI.insert ρ k S i = ρ i := by
  simp [EnvI.insert, h]

theorem EnvI.insert_self (ρ : EnvI) (k : Nat) (S : CptI → Prop) : EnvI.insert ρ k S k = S := by
  simp [EnvI.insert]

theorem EnvI.insert_gt {ρ : EnvI} {k i : Nat} (S : CptI → Prop) (h : k < i) :
    EnvI.insert ρ k S i = ρ (i - 1) := by
  have h1 : ¬ i < k := Nat.not_lt.mpr (Nat.le_of_lt h)
  have h2 : i ≠ k := Nat.ne_of_gt h
  simp [EnvI.insert, h1, h2]

theorem EnvI.cons_insert (S T : CptI → Prop) (ρ : EnvI) (k : Nat) :
    EnvI.cons S (EnvI.insert ρ k T) = EnvI.insert (EnvI.cons S ρ) (k + 1) T := by
  funext i
  cases i with
  | zero =>
      show S = EnvI.insert (EnvI.cons S ρ) (k + 1) T 0
      rw [EnvI.insert_lt _ (Nat.succ_pos k)]
      rfl
  | succ i =>
      show EnvI.insert ρ k T i = EnvI.insert (EnvI.cons S ρ) (k + 1) T (i + 1)
      by_cases h1 : i < k
      · rw [EnvI.insert_lt _ h1, EnvI.insert_lt _ (Nat.succ_lt_succ h1)]
        rfl
      · by_cases h2 : i = k
        · subst h2
          rw [EnvI.insert_self, EnvI.insert_self]
        · have h3 : k < i := Nat.lt_of_le_of_ne (Nat.not_lt.mp h1) (Ne.symm h2)
          rw [EnvI.insert_gt _ h3, EnvI.insert_gt _ (Nat.succ_lt_succ h3)]
          cases i with
          | zero => exact absurd h3 (Nat.not_lt_zero _)
          | succ i => rfl

theorem EnvI.insert_zero (S : CptI → Prop) (ρ : EnvI) : EnvI.insert ρ 0 S = EnvI.cons S ρ := by
  funext i
  cases i with
  | zero => rw [EnvI.insert_self]; rfl
  | succ i => rw [EnvI.insert_gt _ (Nat.succ_pos i)]; rfl

theorem EnvI.drop_zero (ρ : EnvI) : EnvI.drop ρ 0 = ρ := by
  funext i; simp [EnvI.drop]

theorem EnvI.drop_cons (S : CptI → Prop) (ρ : EnvI) (k : Nat) :
    EnvI.drop (EnvI.cons S ρ) (k + 1) = EnvI.drop ρ k := by
  funext i
  show EnvI.cons S ρ (i + (k + 1)) = ρ (i + k)
  rw [show i + (k + 1) = (i + k) + 1 from rfl]
  rfl

theorem EnvI.drop_succ (ρ : EnvI) (k : Nat) :
    EnvI.drop ρ (k + 1) = EnvI.drop (EnvI.drop ρ 1) k := by
  funext i
  show ρ (i + (k + 1)) = ρ (i + k + 1)
  rfl

theorem EnvI.insert_drop_one (ρ : EnvI) : EnvI.insert (EnvI.drop ρ 1) 0 (ρ 0) = ρ := by
  funext i
  cases i with
  | zero => rw [EnvI.insert_self]
  | succ i => rw [EnvI.insert_gt _ (Nat.succ_pos i)]; rfl

theorem EnvI.update_self (ρ : EnvI) (j : Nat) (S : CptI → Prop) : EnvI.update ρ j S j = S := by
  show (if j = j then S else ρ j) = S
  rw [if_pos rfl]

theorem EnvI.update_ne {ρ : EnvI} {j i : Nat} (S : CptI → Prop) (h : i ≠ j) :
    EnvI.update ρ j S i = ρ i := by
  show (if i = j then S else ρ i) = ρ i
  rw [if_neg h]

theorem EnvI.cons_update (S T : CptI → Prop) (ρ : EnvI) (j : Nat) :
    EnvI.cons S (EnvI.update ρ j T) = EnvI.update (EnvI.cons S ρ) (j + 1) T := by
  funext i
  cases i with
  | zero =>
      show S = EnvI.update (EnvI.cons S ρ) (j + 1) T 0
      rw [EnvI.update_ne _ (Nat.succ_ne_zero j).symm]
      rfl
  | succ i =>
      show EnvI.update ρ j T i = EnvI.update (EnvI.cons S ρ) (j + 1) T (i + 1)
      by_cases h : i = j
      · subst h
        rw [EnvI.update_self, EnvI.update_self]
      · rw [EnvI.update_ne _ h, EnvI.update_ne _ (fun h' => h (Nat.succ.inj h'))]
        rfl

theorem EnvI.le_cons {ρ ρ' : EnvI} (h : EnvI.le ρ ρ') (S : CptI → Prop) :
    EnvI.le (EnvI.cons S ρ) (EnvI.cons S ρ') := by
  intro i c hc
  cases i with
  | zero => exact hc
  | succ i => exact h i c hc

/-! ### the approximation relation -/

/-- `ApproxI ρ e c`: the compact `c` approximates `⟦e⟧_ρ`. -/
inductive ApproxI : EnvI → Expr Nat → CptI → Prop
  | bot (ρ : EnvI) (e : Expr Nat) : ApproxI ρ e .bot
  | bvar {ρ : EnvI} {i : Nat} {c : CptI} (h : ρ i c) : ApproxI ρ (.bvar i) c
  | sort (ρ : EnvI) (l : Level) : ApproxI ρ (.sort l) .sort
  | pi {ρ : EnvI} {A B : Expr Nat} {a : CptI} {f : List (List CptI × CptI)}
      (hA : ApproxI ρ A a) (hB : ∀ s ∈ f, ApproxI (EnvI.cons (demand s.1) ρ) B s.2) :
      ApproxI ρ (.pi A B) (.pi a f)
  | lam {ρ : EnvI} {A b : Expr Nat} {f : List (List CptI × CptI)}
      (hb : ∀ s ∈ f, ApproxI (EnvI.cons (demand s.1) ρ) b s.2) : ApproxI ρ (.lam A b) (.lam f)
  | app {ρ : EnvI} {f a : Expr Nat} {g : List (List CptI × CptI)} {s : List CptI × CptI}
      (hf : ApproxI ρ f (.lam g)) (hs : s ∈ g) (ha : ∀ u ∈ s.1, ApproxI ρ a u) :
      ApproxI ρ (.app f a) s.2
  | const (ρ : EnvI) (r : Nat) (ls : List Level) : ApproxI ρ (.const r ls) (.spine r [])
  | appSpine {ρ : EnvI} {f a : Expr Nat} {r : Nat} {args : List CptI} {u : CptI}
      (hf : ApproxI ρ f (.spine r args)) (ha : ApproxI ρ a u) :
      ApproxI ρ (.app f a) (.spine r (args ++ [u]))
  | letE {ρ : EnvI} {A v b : Expr Nat} {c : CptI} (h : ApproxI ρ (.app (.lam A b) v) c) :
      ApproxI ρ (.letE A v b) c
  | lit {ρ : EnvI} {t : Nat} {c : CptI} (h : ApproxI ρ (natExpand t) c) : ApproxI ρ (.lit t) c

/-- The denotation as a set of compacts. -/
def denI (ρ : EnvI) (e : Expr Nat) : CptI → Prop := fun c => ApproxI ρ e c

/-- Semantic equality. -/
def SemEqI (ρ : EnvI) (a b : Expr Nat) : Prop := ∀ c, ApproxI ρ a c ↔ ApproxI ρ b c

/-! ### environments grow -/

theorem approxI_mono_env {ρ ρ' : EnvI} (hle : EnvI.le ρ ρ') {e : Expr Nat} {c : CptI}
    (h : ApproxI ρ e c) : ApproxI ρ' e c := by
  induction h generalizing ρ' with
  | bot => exact .bot _ _
  | bvar h => exact .bvar (hle _ _ h)
  | sort => exact .sort _ _
  | pi _ _ ihA ihB => exact .pi (ihA hle) (fun s hs => ihB s hs (EnvI.le_cons hle _))
  | lam _ ihb => exact .lam (fun s hs => ihb s hs (EnvI.le_cons hle _))
  | app _ hs _ ihf iha => exact .app (ihf hle) hs (fun u hu => iha u hu hle)
  | const => exact .const _ _ _
  | appSpine _ _ ihf iha => exact .appSpine (ihf hle) (iha hle)
  | letE _ ih => exact .letE (ih hle)
  | lit _ ih => exact .lit (ih hle)

/-! ### inversions -/

theorem approxI_bvar_inv {ρ : EnvI} {i : Nat} {c : CptI} (h : ApproxI ρ (.bvar i) c) :
    c = .bot ∨ ρ i c := by
  cases h with
  | bot => exact Or.inl rfl
  | bvar h => exact Or.inr h

theorem approxI_sort_inv {ρ : EnvI} {l : Level} {c : CptI} (h : ApproxI ρ (.sort l) c) :
    c = .bot ∨ c = .sort := by
  cases h with
  | bot => exact Or.inl rfl
  | sort => exact Or.inr rfl

theorem approxI_const_inv {ρ : EnvI} {r : Nat} {ls : List Level} {c : CptI}
    (h : ApproxI ρ (.const r ls) c) : c = .bot ∨ c = .spine r [] := by
  cases h with
  | bot => exact Or.inl rfl
  | const => exact Or.inr rfl

theorem approxI_pi_inv {ρ : EnvI} {A B : Expr Nat} {c : CptI} (h : ApproxI ρ (.pi A B) c) :
    c = .bot ∨ ∃ a f, c = .pi a f ∧ ApproxI ρ A a ∧
      ∀ s ∈ f, ApproxI (EnvI.cons (demand s.1) ρ) B s.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | pi hA hB => exact Or.inr ⟨_, _, rfl, hA, hB⟩

theorem approxI_lam_inv {ρ : EnvI} {A b : Expr Nat} {c : CptI} (h : ApproxI ρ (.lam A b) c) :
    c = .bot ∨ ∃ f, c = .lam f ∧ ∀ s ∈ f, ApproxI (EnvI.cons (demand s.1) ρ) b s.2 := by
  cases h with
  | bot => exact Or.inl rfl
  | lam hb => exact Or.inr ⟨_, rfl, hb⟩

theorem approxI_app_inv {ρ : EnvI} {f a : Expr Nat} {c : CptI} (h : ApproxI ρ (.app f a) c) :
    c = .bot ∨
      (∃ g s, c = s.2 ∧ ApproxI ρ f (.lam g) ∧ s ∈ g ∧ ∀ u ∈ s.1, ApproxI ρ a u) ∨
      (∃ r args u, c = .spine r (args ++ [u]) ∧ ApproxI ρ f (.spine r args) ∧ ApproxI ρ a u) := by
  cases h with
  | bot => exact Or.inl rfl
  | app hf hs ha => exact Or.inr (Or.inl ⟨_, _, rfl, hf, hs, ha⟩)
  | appSpine hf ha => exact Or.inr (Or.inr ⟨_, _, _, rfl, hf, ha⟩)

theorem approxI_letE_inv {ρ : EnvI} {A v b : Expr Nat} {c : CptI} (h : ApproxI ρ (.letE A v b) c) :
    c = .bot ∨ ApproxI ρ (.app (.lam A b) v) c := by
  cases h with
  | bot => exact Or.inl rfl
  | letE h => exact Or.inr h

theorem approxI_lit_inv {ρ : EnvI} {t : Nat} {c : CptI} (h : ApproxI ρ (.lit t) c) :
    c = .bot ∨ ApproxI ρ (natExpand t) c := by
  cases h with
  | bot => exact Or.inl rfl
  | lit h => exact Or.inr h

/-! ### closed literal expansions do not depend on the environment -/

theorem approxI_natExpand_env (ρ ρ' : EnvI) : (t : Nat) → {c : CptI} →
    ApproxI ρ (natExpand t) c → ApproxI ρ' (natExpand t) c
  | 0, _, h => by
      rcases approxI_const_inv h with h0 | h0 <;> subst h0
      · exact .bot _ _
      · exact .const _ _ _
  | t + 1, _, h => by
      rcases approxI_app_inv h with h0 | ⟨g, s, _, hf, _, _⟩ | ⟨r, args, u, heq, hf, ha⟩
      · subst h0; exact .bot _ _
      · rcases approxI_const_inv hf with h1 | h1 <;> cases h1
      · rcases approxI_const_inv hf with h1 | h1
        · cases h1
        · cases h1
          subst heq
          exact .appSpine (.const _ _ _) (approxI_natExpand_env ρ ρ' t ha)

/-! ### finite demand -/

theorem approxI_mono_update {ρ : EnvI} {j : Nat} {e : Expr Nat} {c : CptI}
    (us us' : List CptI) (hsub : ∀ u ∈ us, u ∈ us')
    (h : ApproxI (EnvI.update ρ j (demand us)) e c) :
    ApproxI (EnvI.update ρ j (demand us')) e c :=
  approxI_mono_env (fun i d hd => by
    by_cases hij : i = j
    · subst hij
      rw [EnvI.update_self] at hd ⊢
      exact hsub d hd
    · rw [EnvI.update_ne _ hij] at hd ⊢
      exact hd) h

/-- Collecting the demands of the finitely many sub-derivations under a binder. -/
theorem approxI_factor_list {ρ : EnvI} {j : Nat} {B : Expr Nat} :
    (f : List (List CptI × CptI)) →
    (∀ s ∈ f, ∃ us : List CptI, (∀ u ∈ us, ρ j u) ∧
      ApproxI (EnvI.cons (demand s.1) (EnvI.update ρ j (demand us))) B s.2) →
    ∃ us : List CptI, (∀ u ∈ us, ρ j u) ∧
      ∀ s ∈ f, ApproxI (EnvI.cons (demand s.1) (EnvI.update ρ j (demand us))) B s.2
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | s :: rest, ih => by
      obtain ⟨us₁, h₁, hs⟩ := ih s (List.mem_cons_self _ _)
      obtain ⟨us₂, h₂, hrest⟩ :=
        approxI_factor_list rest (fun s' hs' => ih s' (List.mem_cons_of_mem _ hs'))
      refine ⟨us₁ ++ us₂, fun u hu => ?_, fun s' hs' => ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact h₁ u hu
        · exact h₂ u hu
      · cases List.mem_cons.mp hs' with
        | inl heq =>
            subst heq
            rw [EnvI.cons_update] at hs ⊢
            exact approxI_mono_update us₁ _ (fun u hu => List.mem_append.mpr (Or.inl hu)) hs
        | inr hs'' =>
            have := hrest s' hs''
            rw [EnvI.cons_update] at this ⊢
            exact approxI_mono_update us₂ _ (fun u hu => List.mem_append.mpr (Or.inr hu)) this

/-- Collecting the demands of the finitely many argument sub-derivations. -/
theorem approxI_factor_args {ρ : EnvI} {j : Nat} {a : Expr Nat} :
    (us0 : List CptI) →
    (∀ u ∈ us0, ∃ us : List CptI, (∀ w ∈ us, ρ j w) ∧ ApproxI (EnvI.update ρ j (demand us)) a u) →
    ∃ us : List CptI, (∀ w ∈ us, ρ j w) ∧ ∀ u ∈ us0, ApproxI (EnvI.update ρ j (demand us)) a u
  | [], _ => ⟨[], fun _ h => (List.not_mem_nil _ h).elim, fun _ h => (List.not_mem_nil _ h).elim⟩
  | u :: rest, ih => by
      obtain ⟨us₁, h₁, hu⟩ := ih u (List.mem_cons_self _ _)
      obtain ⟨us₂, h₂, hrest⟩ :=
        approxI_factor_args rest (fun u' hu' => ih u' (List.mem_cons_of_mem _ hu'))
      refine ⟨us₁ ++ us₂, fun w hw => ?_, fun u' hu' => ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact h₁ w hw
        · exact h₂ w hw
      · cases List.mem_cons.mp hu' with
        | inl heq =>
            subst heq
            exact approxI_mono_update us₁ _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hu
        | inr hu'' =>
            exact approxI_mono_update us₂ _ (fun w hw => List.mem_append.mpr (Or.inr hw))
              (hrest u' hu'')

/-- Finite demand: a derivation uses only finitely many compacts of any one variable. -/
theorem approxI_factor {ρ : EnvI} {e : Expr Nat} {c : CptI} (h : ApproxI ρ e c) (j : Nat) :
    ∃ us : List CptI, (∀ u ∈ us, ρ j u) ∧ ApproxI (EnvI.update ρ j (demand us)) e c := by
  induction h generalizing j with
  | bot => exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .bot _ _⟩
  | @bvar ρ i c h =>
      by_cases hij : i = j
      · subst hij
        refine ⟨[c], fun u hu => ?_, .bvar ?_⟩
        · have heq := List.mem_singleton.mp hu
          subst heq
          exact h
        · rw [EnvI.update_self]; exact List.mem_singleton.mpr rfl
      · exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .bvar (by rw [EnvI.update_ne _ hij]; exact h)⟩
  | sort => exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .sort _ _⟩
  | @pi ρ A B a f _ _ ihA ihB =>
      obtain ⟨usA, hA₁, hA₂⟩ := ihA j
      obtain ⟨usB, hB₁, hB₂⟩ := approxI_factor_list f (fun s hs => by
        obtain ⟨us, h₁, h₂⟩ := ihB s hs (j + 1)
        exact ⟨us, h₁, by rw [EnvI.cons_update]; exact h₂⟩)
      refine ⟨usA ++ usB, fun u hu => ?_, .pi ?_ ?_⟩
      · rcases List.mem_append.mp hu with hu | hu
        · exact hA₁ u hu
        · exact hB₁ u hu
      · exact approxI_mono_update usA _ (fun u hu => List.mem_append.mpr (Or.inl hu)) hA₂
      · intro s hs
        have := hB₂ s hs
        rw [EnvI.cons_update] at this ⊢
        exact approxI_mono_update usB _ (fun u hu => List.mem_append.mpr (Or.inr hu)) this
  | @lam ρ A b f _ ihb =>
      obtain ⟨usb, hb₁, hb₂⟩ := approxI_factor_list f (fun s hs => by
        obtain ⟨us, h₁, h₂⟩ := ihb s hs (j + 1)
        exact ⟨us, h₁, by rw [EnvI.cons_update]; exact h₂⟩)
      exact ⟨usb, hb₁, .lam hb₂⟩
  | @app ρ f a g s _ hs _ ihf iha =>
      obtain ⟨usf, hf₁, hf₂⟩ := ihf j
      obtain ⟨usa, ha₁, ha₂⟩ := approxI_factor_args s.1 (fun u hu => iha u hu j)
      refine ⟨usf ++ usa, fun w hw => ?_, .app ?_ hs ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact hf₁ w hw
        · exact ha₁ w hw
      · exact approxI_mono_update usf _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hf₂
      · exact fun u hu => approxI_mono_update usa _ (fun w hw => List.mem_append.mpr (Or.inr hw))
          (ha₂ u hu)
  | const => exact ⟨[], fun _ h => (List.not_mem_nil _ h).elim, .const _ _ _⟩
  | appSpine _ _ ihf iha =>
      obtain ⟨usf, hf₁, hf₂⟩ := ihf j
      obtain ⟨usa, ha₁, ha₂⟩ := iha j
      refine ⟨usf ++ usa, fun w hw => ?_, .appSpine ?_ ?_⟩
      · rcases List.mem_append.mp hw with hw | hw
        · exact hf₁ w hw
        · exact ha₁ w hw
      · exact approxI_mono_update usf _ (fun w hw => List.mem_append.mpr (Or.inl hw)) hf₂
      · exact approxI_mono_update usa _ (fun w hw => List.mem_append.mpr (Or.inr hw)) ha₂
  | letE _ ih =>
      obtain ⟨us, h₁, h₂⟩ := ih j
      exact ⟨us, h₁, .letE h₂⟩
  | lit _ ih =>
      obtain ⟨us, h₁, h₂⟩ := ih j
      exact ⟨us, h₁, .lit h₂⟩

/-! ### lifting -/

theorem approxI_lift_intro {ρ : EnvI} {e : Expr Nat} {c : CptI} (h : ApproxI ρ e c) :
    ∀ (k : Nat) (S : CptI → Prop), ApproxI (EnvI.insert ρ k S) (lift k 1 e) c := by
  induction h with
  | bot => intro k S; exact .bot _ _
  | @bvar ρ i c h =>
      intro k S
      simp only [lift]
      by_cases hk : k ≤ i
      · rw [if_pos hk]
        exact .bvar (by rw [EnvI.insert_gt _ (Nat.lt_succ_of_le hk)]; simpa using h)
      · rw [if_neg hk]
        exact .bvar (by rw [EnvI.insert_lt _ (Nat.lt_of_not_le hk)]; exact h)
  | sort => intro k S; exact .sort _ _
  | pi _ _ ihA ihB =>
      intro k S
      simp only [lift]
      exact .pi (ihA k S) (fun s hs => by rw [EnvI.cons_insert]; exact ihB s hs (k + 1) S)
  | lam _ ihb =>
      intro k S
      simp only [lift]
      exact .lam (fun s hs => by rw [EnvI.cons_insert]; exact ihb s hs (k + 1) S)
  | app _ hs _ ihf iha =>
      intro k S
      simp only [lift]
      exact .app (ihf k S) hs (fun u hu => iha u hu k S)
  | const => intro k S; exact .const _ _ _
  | appSpine _ _ ihf iha =>
      intro k S
      simp only [lift]
      exact .appSpine (ihf k S) (iha k S)
  | letE _ ih =>
      intro k S
      simp only [lift]
      exact .letE (ih k S)
  | lit _ ih =>
      intro k S
      simp only [lift]
      exact .lit (by have := ih k S; rwa [natExpand_lift] at this)

theorem approxI_lift_elim : (e : Expr Nat) → ∀ {ρ : EnvI} {k : Nat} {S : CptI → Prop} {c : CptI},
    ApproxI (EnvI.insert ρ k S) (lift k 1 e) c → ApproxI ρ e c
  | .bvar i, ρ, k, S, c, h => by
      simp only [lift] at h
      by_cases hk : k ≤ i
      · rw [if_pos hk] at h
        rcases approxI_bvar_inv h with h0 | h0
        · subst h0; exact .bot _ _
        · rw [EnvI.insert_gt _ (Nat.lt_succ_of_le hk)] at h0
          exact .bvar (by simpa using h0)
      · rw [if_neg hk] at h
        rcases approxI_bvar_inv h with h0 | h0
        · subst h0; exact .bot _ _
        · rw [EnvI.insert_lt _ (Nat.lt_of_not_le hk)] at h0
          exact .bvar h0
  | .sort l, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxI_sort_inv h with h0 | h0 <;> subst h0
      · exact .bot _ _
      · exact .sort _ _
  | .const r ls, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxI_const_inv h with h0 | h0 <;> subst h0
      · exact .bot _ _
      · exact .const _ _ _
  | .app f a, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxI_app_inv h with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨r, args, u, heq, hf, ha⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .app (approxI_lift_elim f hf) hs (fun u hu => approxI_lift_elim a (ha u hu))
      · subst heq
        exact .appSpine (approxI_lift_elim f hf) (approxI_lift_elim a ha)
  | .lam A b, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxI_lam_inv h with h0 | ⟨f, heq, hb⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .lam (fun s hs => approxI_lift_elim b (by
          have := hb s hs; rw [EnvI.cons_insert] at this; exact this))
  | .pi A B, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxI_pi_inv h with h0 | ⟨a, f, heq, hA, hB⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .pi (approxI_lift_elim A hA) (fun s hs => approxI_lift_elim B (by
          have := hB s hs; rw [EnvI.cons_insert] at this; exact this))
  | .letE A v b, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxI_letE_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · rcases approxI_app_inv h' with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨r, args, u, heq, hf, ha⟩
        · subst h0; exact .letE (.bot _ _)
        · subst heq
          rcases approxI_lam_inv hf with h1 | ⟨f', heq', hb⟩
          · cases h1
          · cases heq'
            exact .letE (.app (.lam (fun s' hs' => approxI_lift_elim b (by
              have := hb s' hs'; rw [EnvI.cons_insert] at this; exact this))) hs
              (fun u hu => approxI_lift_elim v (ha u hu)))
        · rcases approxI_lam_inv hf with h1 | ⟨f', heq', _⟩
          · cases h1
          · cases heq'
  | .lit t, ρ, k, S, c, h => by
      simp only [lift] at h
      rcases approxI_lit_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · exact .lit (approxI_natExpand_env _ _ t h')

theorem approxI_liftN_intro {e : Expr Nat} {c : CptI} :
    ∀ (ρ : EnvI) (j : Nat), ApproxI (EnvI.drop ρ j) e c → ApproxI ρ (lift 0 j e) c
  | ρ, 0, h => by rw [EnvI.drop_zero] at h; rw [lift_zero_idx]; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx]
      rw [EnvI.drop_succ] at h
      have := approxI_lift_intro (approxI_liftN_intro (EnvI.drop ρ 1) j h) 0 (ρ 0)
      rwa [EnvI.insert_drop_one] at this

theorem approxI_liftN_elim {e : Expr Nat} {c : CptI} :
    ∀ (ρ : EnvI) (j : Nat), ApproxI ρ (lift 0 j e) c → ApproxI (EnvI.drop ρ j) e c
  | ρ, 0, h => by rw [EnvI.drop_zero]; rw [lift_zero_idx] at h; exact h
  | ρ, j + 1, h => by
      rw [← lift_shift_comp_idx] at h
      rw [EnvI.drop_succ]
      have h' : ApproxI (EnvI.insert (EnvI.drop ρ 1) 0 (ρ 0)) (lift 0 1 (lift 0 j e)) c := by
        rwa [EnvI.insert_drop_one]
      exact approxI_liftN_elim (EnvI.drop ρ 1) j (approxI_lift_elim (lift 0 j e) h')

/-! ### substitution -/

theorem approxI_subst_intro {ρ' : EnvI} {e : Expr Nat} {c : CptI} (h : ApproxI ρ' e c) :
    ∀ (ρ : EnvI) (j : Nat) (r : Expr Nat),
      ρ' = EnvI.insert ρ j (denI (EnvI.drop ρ j) r) →
      ApproxI ρ (instantiate j (lift 0 j r) e) c := by
  induction h with
  | bot => intro ρ j r _; exact .bot _ _
  | @bvar ρ' i c h =>
      intro ρ j r hρ
      subst hρ
      simp only [instantiate]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        rw [EnvI.insert_self] at h
        exact approxI_liftN_intro ρ i h
      · rw [if_neg hij]
        by_cases hlt : j < i
        · rw [if_pos hlt]
          rw [EnvI.insert_gt _ hlt] at h
          exact .bvar h
        · rw [if_neg hlt]
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rw [EnvI.insert_lt _ hil] at h
          exact .bvar h
  | sort => intro ρ j r _; exact .sort _ _
  | pi _ _ ihA ihB =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .pi (ihA ρ j r hρ) (fun s hs => ihB s hs _ (j + 1) r
        (by rw [hρ, EnvI.cons_insert, EnvI.drop_cons]))
  | lam _ ihb =>
      intro ρ j r hρ
      simp only [instantiate]
      rw [lift_shift_comp_idx]
      exact .lam (fun s hs => ihb s hs _ (j + 1) r (by rw [hρ, EnvI.cons_insert, EnvI.drop_cons]))
  | app _ hs _ ihf iha =>
      intro ρ j r hρ
      simp only [instantiate]
      exact .app (ihf ρ j r hρ) hs (fun u hu => iha u hu ρ j r hρ)
  | const => intro ρ j r _; exact .const _ _ _
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

theorem approxI_subst_elim : (e : Expr Nat) → ∀ {ρ : EnvI} {j : Nat} {r : Expr Nat} {c : CptI},
    ApproxI ρ (instantiate j (lift 0 j r) e) c →
    ApproxI (EnvI.insert ρ j (denI (EnvI.drop ρ j) r)) e c
  | .bvar i, ρ, j, r, c, h => by
      simp only [instantiate] at h
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at h
        exact .bvar (by rw [EnvI.insert_self]; exact approxI_liftN_elim ρ i h)
      · rw [if_neg hij] at h
        by_cases hlt : j < i
        · rw [if_pos hlt] at h
          rcases approxI_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [EnvI.insert_gt _ hlt]; exact h0)
        · rw [if_neg hlt] at h
          have hil : i < j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) hij
          rcases approxI_bvar_inv h with h0 | h0
          · subst h0; exact .bot _ _
          · exact .bvar (by rw [EnvI.insert_lt _ hil]; exact h0)
  | .sort l, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxI_sort_inv h with h0 | h0 <;> subst h0
      · exact .bot _ _
      · exact .sort _ _
  | .const k ls, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxI_const_inv h with h0 | h0 <;> subst h0
      · exact .bot _ _
      · exact .const _ _ _
  | .app f a, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxI_app_inv h with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨k, args, u, heq, hf, ha⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .app (approxI_subst_elim f hf) hs (fun u hu => approxI_subst_elim a (ha u hu))
      · subst heq
        exact .appSpine (approxI_subst_elim f hf) (approxI_subst_elim a ha)
  | .lam A b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxI_lam_inv h with h0 | ⟨f, heq, hb⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .lam (fun s hs => by
          rw [EnvI.cons_insert, ← EnvI.drop_cons (demand s.1) ρ j]
          exact approxI_subst_elim b (hb s hs))
  | .pi A B, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rw [lift_shift_comp_idx] at h
      rcases approxI_pi_inv h with h0 | ⟨a, f, heq, hA, hB⟩
      · subst h0; exact .bot _ _
      · subst heq
        exact .pi (approxI_subst_elim A hA) (fun s hs => by
          rw [EnvI.cons_insert, ← EnvI.drop_cons (demand s.1) ρ j]
          exact approxI_subst_elim B (hB s hs))
  | .letE A v b, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxI_letE_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · rcases approxI_app_inv h' with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨k, args, u, heq, hf, ha⟩
        · subst h0; exact .letE (.bot _ _)
        · subst heq
          rcases approxI_lam_inv hf with h1 | ⟨f', heq', hb⟩
          · cases h1
          · cases heq'
            rw [lift_shift_comp_idx] at hb
            exact .letE (.app (.lam (fun s' hs' => by
              rw [EnvI.cons_insert, ← EnvI.drop_cons (demand s'.1) ρ j]
              exact approxI_subst_elim b (hb s' hs'))) hs
              (fun u hu => approxI_subst_elim v (ha u hu)))
        · rcases approxI_lam_inv hf with h1 | ⟨f', heq', _⟩
          · cases h1
          · cases heq'
  | .lit t, ρ, j, r, c, h => by
      simp only [instantiate] at h
      rcases approxI_lit_inv h with h0 | h'
      · subst h0; exact .bot _ _
      · exact .lit (approxI_natExpand_env _ _ t h')

/-! ### β and ζ -/

/-- β-soundness: the redex and the contractum have the same approximations. -/
theorem approxI_beta (ρ : EnvI) (A b a : Expr Nat) :
    SemEqI ρ (.app (.lam A b) a) (instantiate0 a b) := by
  intro c
  constructor
  · intro h
    rcases approxI_app_inv h with h0 | ⟨g, s, heq, hf, hs, ha⟩ | ⟨k, args, u, heq, hf, ha⟩
    · subst h0; exact .bot _ _
    · subst heq
      rcases approxI_lam_inv hf with h1 | ⟨f', heq', hb⟩
      · cases h1
      · cases heq'
        have h₁ : ApproxI (EnvI.cons (denI ρ a) ρ) b s.2 :=
          approxI_mono_env (fun i d hd => by
            cases i with
            | zero => exact ha d hd
            | succ i => exact hd) (hb s hs)
        have h₂ := approxI_subst_intro h₁ ρ 0 a (by rw [EnvI.insert_zero, EnvI.drop_zero])
        rwa [lift_zero_idx] at h₂
    · rcases approxI_lam_inv hf with h1 | ⟨f', heq', _⟩
      · cases h1
      · cases heq'
  · intro h
    have h₁ : ApproxI ρ (instantiate 0 (lift 0 0 a) b) c := by rwa [lift_zero_idx]
    have h₂ := approxI_subst_elim b h₁
    rw [EnvI.insert_zero, EnvI.drop_zero] at h₂
    obtain ⟨us, hus, h₃⟩ := approxI_factor h₂ 0
    have h₄ : ApproxI (EnvI.cons (demand us) ρ) b c := by
      refine approxI_mono_env (fun i d hd => ?_) h₃
      cases i with
      | zero => rw [EnvI.update_self] at hd; exact hd
      | succ i => rw [EnvI.update_ne _ (Nat.succ_ne_zero i)] at hd; exact hd
    exact .app (s := (us, c)) (.lam (f := [(us, c)]) (fun s hs => by
      have heq := List.mem_singleton.mp hs
      subst heq
      exact h₄)) (List.mem_singleton.mpr rfl)
      (fun u hu => hus u hu)

/-- ζ-soundness: `letE` is the β-redex by construction. -/
theorem approxI_zeta (ρ : EnvI) (A v b : Expr Nat) :
    SemEqI ρ (.letE A v b) (instantiate0 v b) := by
  intro c
  constructor
  · intro h
    rcases approxI_letE_inv h with h0 | h'
    · subst h0; exact .bot _ _
    · exact (approxI_beta ρ A b v c).mp h'
  · intro h
    exact .letE ((approxI_beta ρ A b v c).mpr h)

/-! ### model Π-injectivity -/

/-- Π is injective in the model: on domains, and on codomains at every finite demand. -/
theorem semEqI_pi_inj {ρ : EnvI} {A B A' B' : Expr Nat} (h : SemEqI ρ (.pi A B) (.pi A' B')) :
    SemEqI ρ A A' ∧ ∀ us, SemEqI (EnvI.cons (demand us) ρ) B B' := by
  refine ⟨fun a => ⟨fun hA => ?_, fun hA' => ?_⟩, fun us v => ⟨fun hB => ?_, fun hB' => ?_⟩⟩
  · have := (h (.pi a [])).mp (.pi hA (fun _ hs => (List.not_mem_nil _ hs).elim))
    rcases approxI_pi_inv this with h0 | ⟨_, _, heq, hA', _⟩
    · cases h0
    · cases heq; exact hA'
  · have := (h (.pi a [])).mpr (.pi hA' (fun _ hs => (List.not_mem_nil _ hs).elim))
    rcases approxI_pi_inv this with h0 | ⟨_, _, heq, hA, _⟩
    · cases h0
    · cases heq; exact hA
  · have := (h (.pi .bot [(us, v)])).mp (.pi (.bot ρ A) (fun s hs => by
      have heq := List.mem_singleton.mp hs; subst heq; exact hB))
    rcases approxI_pi_inv this with h0 | ⟨_, _, heq, _, hB'⟩
    · cases h0
    · cases heq; exact hB' (us, v) (List.mem_singleton.mpr rfl)
  · have := (h (.pi .bot [(us, v)])).mpr (.pi (.bot ρ A') (fun s hs => by
      have heq := List.mem_singleton.mp hs; subst heq; exact hB'))
    rcases approxI_pi_inv this with h0 | ⟨_, _, heq, _, hB⟩
    · cases h0
    · cases heq; exact hB (us, v) (List.mem_singleton.mpr rfl)

/-- Π and sorts are disjoint in the model. -/
theorem semEqI_pi_sort_disjoint {ρ : EnvI} {A B : Expr Nat} {l : Level}
    (h : SemEqI ρ (.pi A B) (.sort l)) : False := by
  have := (h (.pi .bot [])).mp (.pi (.bot ρ A) (fun _ hs => (List.not_mem_nil _ hs).elim))
  rcases approxI_sort_inv this with h0 | h0 <;> cases h0

#print axioms CptI
#print axioms EnvI
#print axioms ApproxI
#print axioms denI
#print axioms SemEqI
#print axioms approxI_mono_env
#print axioms approxI_bvar_inv
#print axioms approxI_pi_inv
#print axioms approxI_lam_inv
#print axioms approxI_app_inv
#print axioms approxI_letE_inv
#print axioms approxI_lit_inv
#print axioms approxI_natExpand_env
#print axioms approxI_mono_update
#print axioms approxI_factor_list
#print axioms approxI_factor_args
#print axioms approxI_factor
#print axioms approxI_lift_intro
#print axioms approxI_lift_elim
#print axioms approxI_liftN_intro
#print axioms approxI_liftN_elim
#print axioms approxI_subst_intro
#print axioms approxI_subst_elim
#print axioms approxI_beta
#print axioms approxI_zeta
#print axioms semEqI_pi_inj
#print axioms semEqI_pi_sort_disjoint

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
