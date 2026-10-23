import rcic.RcicAnnLR3EnvironmentLambdaArms
import rcic.RcicAnnLR3EnvironmentTelescopePorts
import rcic.RcicAnnLR3PairedArms
import rcic.RcicAnnSubstCalc
import rcic.RcicAnnEnvWf

/-!
# EnvironmentEval substitution/let group of the paired arms

Target evaluator: `EnvironmentTelescopeInsertion.image E
EnvironmentEval.neutralFamilySyntax`, i.e. `EnvironmentEval.denote
(internalView E) (hook E neutralFamilySyntax)`, the relational union over
finite `Translation` witnesses at the routed internal view. Supplies the
paired substitution port, the let evaluation equation, and the six
contracts `Ty_letE`, `Conv_zeta`, `Conv_letE`, `Ty_app`, `Conv_app`,
`Conv_beta` exactly against `RcicAnnLR3PairedArms`, at the
`legacyUniverseSystem` attachment (the same `EnvironmentLambdaArms.model`
at the image).

## Evaluator laws

* `translation_closed`: a `Translation` of a `ClosedAt d` source denotes
  identically under environments agreeing below `d`. The `constBody`
  case needs `DefinitionBodiesClosed E'` and the `constRigid` case needs
  `HookEnvironmentIndependent E' F'` — the two named ports, discharged
  at the telescope image by `internalView_body_conditions` and
  `default_hook_conditions` from source admission (`EnvWfA`). No level
  condition is used, so no `ConstsArityA` is carried.
* `translation_lift` / `translation_delift`: a translation of `s` lifts
  to a translation of `liftA k j s` whose denotation shifts the
  environment (`dropAtEnv`), and conversely.
* `denote_subst_intro` / `denote_subst_elim`: the paired substitution
  law at arbitrary index; `denote_subst0` is the `j = 0` port.
* `denote_letE`: the let equation — premise-free (only the finite cover
  `approxI_factor` and `finite_compacts`).
* `denote_beta`, `denote_zeta`: composed from `denote_application`,
  `denote_lambda_application`, `denote_subst0`, `denote_letE`.

## Arms

Every arm keeps every source premise and child-IH position; no
`Fundamental` premise. The only extra premise is `hE : EnvWfA I E` —
source admission — from which `internalView_body_conditions` and
`default_hook_conditions` discharge the named stored-data and hook
ports. `conv_letE_supplied` additionally carries
`(IotaLiftA, IotaRecHeadA, IotaSubstA)` because `CtxWfA` of
`.letBinding A v :: Γ` needs the left typings of the `ConvA` premises
via `convA_hasTy_left` (`EnvClosedA` comes from `envWfA_closed hE`).
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.EnvironmentEvalSubst

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements PairedStatements InductiveCodes
open EnvironmentPortConditions

variable {E : ResolvedEnvA} {F : EnvironmentEval.FamilySyntax} {ν : Valuation}

/-! ## §0 Environment algebra -/

/-- Drop `j` entries at depth `k` of the environment — the semantic
counterpart of `liftA k j` (at `k = 0` this is `EnvI.drop ρ j`). -/
def dropAtEnv (ρ : EnvI) (k j : Nat) : EnvI :=
  fun i => if i < k then ρ i else ρ (i + j)

theorem dropAtEnv_zero (ρ : EnvI) (j : Nat) :
    dropAtEnv ρ 0 j = EnvI.drop ρ j := by
  funext i
  show (if i < 0 then ρ i else ρ (i + j)) = ρ (i + j)
  rw [if_neg (Nat.not_lt_zero i)]

theorem dropAtEnv_cons_succ (x : CptI → Prop) (ρ : EnvI) (k j : Nat) :
    dropAtEnv (EnvI.cons x ρ) (k + 1) j = EnvI.cons x (dropAtEnv ρ k j) := by
  funext i; cases i with
  | zero =>
      show (if (0 : Nat) < k + 1 then x else EnvI.cons x ρ (0 + j)) = x
      rw [if_pos (Nat.zero_lt_succ k)]
  | succ i =>
      show (if i + 1 < k + 1 then ρ i else EnvI.cons x ρ (i + 1 + j)) =
        (if i < k then ρ i else ρ (i + j))
      by_cases hik : i < k
      · rw [if_pos hik, if_pos (Nat.succ_lt_succ hik)]
      · rw [if_neg hik, if_neg (fun h => hik (Nat.lt_of_succ_lt_succ h))]
        show EnvI.cons x ρ (i + 1 + j) = ρ (i + j)
        rw [show i + 1 + j = (i + j) + 1 from Nat.add_right_comm i 1 j]
        rfl

/-- `EnvI.le` with a strictly larger head. -/
theorem cons_le_cons_env {S S' : CptI → Prop} {ρ ρ' : EnvI}
    (hS : ∀ c, S c → S' c) (hρ : EnvI.le ρ ρ') :
    EnvI.le (EnvI.cons S ρ) (EnvI.cons S' ρ') := by
  intro i c h
  cases i with
  | zero => exact hS c h
  | succ i => exact hρ i c h

/-! ## §1 Closedness -/

/-- `ClosedAt d e`: no free variable at or above `d`, phrased as
lift-invariance at every cutoff `d + k`. -/
def ClosedAt (d : Nat) (e : ExprA) : Prop := ∀ k, liftA (d + k) 1 e = e

theorem ClosedAt.bvar {d i : Nat} (h : ClosedAt d (.bvar i)) : i < d := by
  by_cases hlt : i < d
  · exact hlt
  · exfalso
    have h0 := h 0
    simp only [Nat.add_zero, liftA] at h0
    rw [if_pos (Nat.le_of_not_lt hlt)] at h0
    exact absurd (ExprA.bvar.inj h0) (Nat.succ_ne_self i)

theorem ClosedAt.app_left {d : Nat} {f a : ExprA} (h : ClosedAt d (.app f a)) :
    ClosedAt d f := fun k => by
  have hk := h k
  rw [liftA_app] at hk
  exact (ExprA.app.inj hk).1

theorem ClosedAt.app_right {d : Nat} {f a : ExprA} (h : ClosedAt d (.app f a)) :
    ClosedAt d a := fun k => by
  have hk := h k
  rw [liftA_app] at hk
  exact (ExprA.app.inj hk).2

theorem ClosedAt.lam_dom {d : Nat} {A : ExprA} {u : Level} {b : ExprA}
    (h : ClosedAt d (.lam A u b)) : ClosedAt d A := fun k => by
  have hk := h k
  rw [liftA_lam] at hk
  exact (ExprA.lam.inj hk).1

theorem ClosedAt.lam_body {d : Nat} {A : ExprA} {u : Level} {b : ExprA}
    (h : ClosedAt d (.lam A u b)) : ClosedAt (d + 1) b := fun k => by
  have hk := h k
  rw [liftA_lam] at hk
  have hb := (ExprA.lam.inj hk).2.2
  rwa [show d + 1 + k = d + k + 1 by omega]

theorem ClosedAt.pi_dom {d : Nat} {A : ExprA} {u : Level} {B : ExprA} {v : Level}
    (h : ClosedAt d (.pi A u B v)) : ClosedAt d A := fun k => by
  have hk := h k
  rw [liftA_pi] at hk
  exact (ExprA.pi.inj hk).1

theorem ClosedAt.pi_body {d : Nat} {A : ExprA} {u : Level} {B : ExprA} {v : Level}
    (h : ClosedAt d (.pi A u B v)) : ClosedAt (d + 1) B := fun k => by
  have hk := h k
  rw [liftA_pi] at hk
  have hb := (ExprA.pi.inj hk).2.2.1
  rwa [show d + 1 + k = d + k + 1 by omega]

theorem ClosedAt.letE_dom {d : Nat} {A v b : ExprA} (h : ClosedAt d (.letE A v b)) :
    ClosedAt d A := fun k => by
  have hk := h k
  rw [liftA_letE] at hk
  exact (ExprA.letE.inj hk).1

theorem ClosedAt.letE_val {d : Nat} {A v b : ExprA} (h : ClosedAt d (.letE A v b)) :
    ClosedAt d v := fun k => by
  have hk := h k
  rw [liftA_letE] at hk
  exact (ExprA.letE.inj hk).2.1

theorem ClosedAt.letE_body {d : Nat} {A v b : ExprA} (h : ClosedAt d (.letE A v b)) :
    ClosedAt (d + 1) b := fun k => by
  have hk := h k
  rw [liftA_letE] at hk
  have hb := (ExprA.letE.inj hk).2.2
  rwa [show d + 1 + k = d + k + 1 by omega]

theorem closedAt_zero_of_closed {e : ExprA} (h : ∀ k, liftA k 1 e = e) :
    ClosedAt 0 e := fun k => by simpa using h k

theorem closedAt_natExpandA (n : Nat) : ClosedAt 0 (natExpandA n) :=
  closedAt_zero_of_closed (liftA_natExpandA_closed n)

/-! ## §2 Rigid/tag heads are environment-independent -/

theorem taggedHead_environment (ρ σ : EnvI) (i : Option Nat) :
    ValueEq (denI ρ (.app (.const 10 []) (levelTerm i)))
      (denI σ (.app (.const 10 []) (levelTerm i))) :=
  approxI_app_rel (FunctionEval.constant_environment ρ σ 10 [])
    (FunctionEval.constant_environment ρ σ (levelRef i) [])

/-! ## §3 denI transports used by the translation lemmas -/

/-- Inclusion between pi denotations, replayed per compact. -/
theorem denI_pi_incl {ρ₁ ρ₂ : EnvI} {A' B' tA tB : Expr Nat} {u : CptI}
    (hA : ∀ c, denI ρ₁ A' c → denI ρ₂ tA c)
    (hB : ∀ (x : CptI → Prop) (c : CptI),
      denI (EnvI.cons x ρ₁) B' c → denI (EnvI.cons x ρ₂) tB c)
    (h : denI ρ₁ (.pi A' B') u) : denI ρ₂ (.pi tA tB) u := by
  rcases approxI_pi_inv h with hb | ⟨a, f, he, ha, hf⟩
  · subst hb; exact .bot _ _
  · subst he; exact .pi (hA _ ha) (fun s hs => hB _ _ (hf s hs))

/-- Inclusion between tagged pi denotations; the closed head is moved by
`taggedHead_environment`. -/
theorem denI_tagged_pi_incl {ρ₁ ρ₂ : EnvI} {k : Option Nat}
    {A' B' tA tB : Expr Nat} {c : CptI}
    (hA : ∀ x, denI ρ₁ A' x → denI ρ₂ tA x)
    (hB : ∀ (x : CptI → Prop) (y : CptI),
      denI (EnvI.cons x ρ₁) B' y → denI (EnvI.cons x ρ₂) tB y)
    (h : denI ρ₁ (taggedTerm k (.pi A' B')) c) :
    denI ρ₂ (taggedTerm k (.pi tA tB)) c := by
  rcases approxI_app_inv h with hb | ⟨g, s, he, hf, hs, ha⟩ |
      ⟨r, args, u, he, hf, ha⟩
  · subst hb; exact .bot _ _
  · subst he
    exact .app ((taggedHead_environment ρ₁ ρ₂ k _).mp hf) hs
      (fun u hu => denI_pi_incl hA hB (ha u hu))
  · subst he
    exact .appSpine ((taggedHead_environment ρ₁ ρ₂ k _).mp hf)
      (denI_pi_incl hA hB ha)

/-! ## §4 Closed sources denote independently of the environment -/

theorem translation_closed (hdef : DefinitionBodiesClosed E)
    (hhook : HookEnvironmentIndependent E F)
    {e : ExprA} {t : Expr Nat}
    (ht : EnvironmentEval.Translation E F ν e t) :
    ∀ {d : Nat}, ClosedAt d e → ∀ {ρ σ : EnvI} {c : CptI},
      (∀ i, i < d → ∀ x, ρ i x → σ i x) → denI ρ t c → denI σ t c := by
  induction ht with
  | cut e =>
      intro _ _ ρ σ c _ hc
      have := EnvironmentEval.cutTerm_only_bottom hc
      subst this; exact .bot σ _
  | bvar i =>
      intro d hcl ρ σ c hag hc
      have hid := hcl.bvar
      rcases approxI_bvar_inv hc with hb | hb
      · subst hb; exact .bot σ _
      · exact .bvar (hag i hid c hb)
  | sort l =>
      intro _ _ ρ σ c _ hc
      exact (FunctionEval.sortTerm_environment ρ σ _ c).mp hc
  | constBody hb htr ih =>
      intro d _ ρ σ c _ hc
      exact ih (closedAt_zero_of_closed (hdef _ _ _ hb))
        (fun i hi => absurd hi (Nat.not_lt_zero i)) hc
  | constRigid hr =>
      intro _ _ ρ σ c _ hc
      exact (rigidTerm_environmentIndependent hhook ν _ _ ρ σ c).mp hc
  | app hf ha ihf iha =>
      intro d hcl ρ σ c hag hc
      rcases approxI_app_inv hc with hb | ⟨g, s, he, hfg, hs, harg⟩ |
          ⟨r, args, u, he, hfg, harg⟩
      · subst hb; exact .bot σ _
      · subst he
        exact .app (ihf hcl.app_left hag hfg) hs
          (fun u hu => iha hcl.app_right hag (harg u hu))
      · subst he
        exact .appSpine (ihf hcl.app_left hag hfg)
          (iha hcl.app_right hag harg)
  | lam hA hb ihA ihB =>
      intro d hcl ρ σ c hag hc
      rcases approxI_lam_inv hc with hb | ⟨g, he, hgb⟩
      · subst hb; exact .bot σ _
      · subst he
        exact .lam (fun s hs => ihB hcl.lam_body
          (fun i hi x hx => by
            cases i with
            | zero => exact hx
            | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi) x hx)
          (hgb s hs))
  | pi hA hB ihA ihB =>
      intro d hcl ρ σ c hag hc
      exact denI_tagged_pi_incl
        (fun x hx => ihA hcl.pi_dom hag hx)
        (fun x y hy => ihB hcl.pi_body
          (fun i hi z hz => by
            cases i with
            | zero => exact hz
            | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi) z hz) hy) hc
  | letE hA hv hb ihA ihv ihB =>
      intro d hcl ρ σ c hag hc
      rcases approxI_letE_inv hc with hb | happ
      · subst hb; exact .bot σ _
      · rcases approxI_app_inv happ with hb | ⟨g, s, he, hf, hs, ha⟩ |
            ⟨r, args, u, he, hf, ha⟩
        · subst hb; exact .bot σ _
        · subst he
          rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
          · cases hb
          · cases he'
            exact .letE (.app (.lam (fun s hs => ihB hcl.letE_body
              (fun i hi x hx => by
                cases i with
                | zero => exact hx
                | succ i => exact hag i (Nat.lt_of_succ_lt_succ hi) x hx)
              (hgb s hs))) hs
              (fun u hu => ihv hcl.letE_val hag (ha u hu)))
        · subst he
          rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
          · cases hb
          · cases he'
  | lit expanded ih =>
      intro _ _ ρ σ c _ hc
      exact ih (closedAt_natExpandA _)
        (fun i hi => absurd hi (Nat.not_lt_zero i)) hc

/-! ## §5 Lifting and de-lifting translations -/

theorem liftA_natExpandA_id (k j t : Nat) :
    liftA k j (natExpandA t) = natExpandA t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [natExpandA, litSuccA, liftA, ih]

theorem translation_lift (hdef : DefinitionBodiesClosed E)
    (hhook : HookEnvironmentIndependent E F)
    {s : ExprA} {w : Expr Nat}
    (ht : EnvironmentEval.Translation E F ν s w) :
    ∀ (k j : Nat), ∃ t', EnvironmentEval.Translation E F ν (liftA k j s) t' ∧
      ∀ (ρ : EnvI) {c : CptI}, denI (dropAtEnv ρ k j) w c → denI ρ t' c := by
  induction ht with
  | cut e =>
      exact fun _ _ => ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
        have := EnvironmentEval.cutTerm_only_bottom h
        subst this; exact .bot ρ _⟩
  | bvar i =>
      intro k j
      by_cases hki : k ≤ i
      · refine ⟨.bvar (i + j), ?_, fun ρ c h => ?_⟩
        · simp only [liftA, if_pos hki]; exact .bvar _
        · cases h with
          | bot => exact .bot ρ _
          | bvar h =>
              exact .bvar (by
                simp only [dropAtEnv, if_neg (Nat.not_lt.mpr hki)] at h
                exact h)
      · refine ⟨.bvar i, ?_, fun ρ c h => ?_⟩
        · simp only [liftA, if_neg hki]; exact .bvar _
        · cases h with
          | bot => exact .bot ρ _
          | bvar h =>
              exact .bvar (by
                simp only [dropAtEnv, if_pos (Nat.lt_of_not_le hki)] at h
                exact h)
  | sort l =>
      exact fun _ _ => ⟨sortTerm (eval ν l), .sort _, fun ρ _ h =>
        (FunctionEval.sortTerm_environment _ _ _ _).mp h⟩
  | constRigid hr =>
      exact fun _ _ => ⟨EnvironmentEval.rigidTerm E F ν _ _, .constRigid hr,
        fun ρ _ h => (rigidTerm_environmentIndependent hhook ν _ _ _ _ _).mp h⟩
  | constBody hb htr ih =>
      exact fun _ _ => ⟨_, .constBody hb htr, fun ρ _ h =>
        translation_closed hdef hhook htr
          (closedAt_zero_of_closed (hdef _ _ _ hb))
          (fun i hi => absurd hi (Nat.not_lt_zero i)) h⟩
  | app hf ha ihf iha =>
      intro k j
      obtain ⟨tf', htf', hf''⟩ := ihf k j
      obtain ⟨ta', hta', ha''⟩ := iha k j
      refine ⟨.app tf' ta', ?_, fun ρ c h => ?_⟩
      · exact .app htf' hta'
      · rcases approxI_app_inv h with hb | ⟨g, s, he, hfg, hs, harg⟩ |
            ⟨r, args, u, he, hfg, harg⟩
        · subst hb; exact .bot ρ _
        · subst he
          exact .app (hf'' ρ hfg) hs (fun u hu => ha'' ρ (harg u hu))
        · subst he
          exact .appSpine (hf'' ρ hfg) (ha'' ρ harg)
  | lam hA hb ihA ihB =>
      intro k j
      obtain ⟨tA', htA', hA''⟩ := ihA k j
      obtain ⟨tb', htb', hB''⟩ := ihB (k + 1) j
      refine ⟨.lam tA' tb', ?_, fun ρ c h => ?_⟩
      · exact .lam htA' htb'
      · rcases approxI_lam_inv h with hb | ⟨g, he, hgb⟩
        · subst hb; exact .bot ρ _
        · subst he
          exact .lam (fun s hs => hB'' _ (by
            rw [dropAtEnv_cons_succ]; exact hgb s hs))
  | pi hA hB ihA ihB =>
      rename_i A B u v A' B'
      intro k j
      obtain ⟨tA', htA', hA''⟩ := ihA k j
      obtain ⟨tB', htB', hB''⟩ := ihB (k + 1) j
      refine ⟨taggedTerm (eval ν (.imax u v)) (.pi tA' tB'), ?_, fun ρ c h => ?_⟩
      · show EnvironmentEval.Translation E F ν
            (.pi (liftA k j A) u (liftA (k + 1) j B) v) _
        exact .pi htA' htB'
      · exact denI_tagged_pi_incl
          (fun x hx => hA'' ρ hx)
          (fun x y hy => hB'' _ (by
            rw [dropAtEnv_cons_succ]; exact hy)) h
  | letE hA hv hb ihA ihv ihB =>
      intro k j
      obtain ⟨tA', htA', _⟩ := ihA k j
      obtain ⟨tv', htv', hv''⟩ := ihv k j
      obtain ⟨tb', htb', hB''⟩ := ihB (k + 1) j
      refine ⟨.letE tA' tv' tb', ?_, fun ρ c h => ?_⟩
      · exact .letE htA' htv' htb'
      · rcases approxI_letE_inv h with hb | happ
        · subst hb; exact .bot ρ _
        · rcases approxI_app_inv happ with hb | ⟨g, s, he, hf, hs, ha⟩ |
              ⟨r, args, u, he, hf, ha⟩
          · subst hb; exact .bot ρ _
          · subst he
            rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
            · cases hb
            · cases he'
              exact .letE (.app (.lam (fun s hs => hB'' _ (by
                rw [dropAtEnv_cons_succ]; exact hgb s hs))) hs
                (fun u hu => hv'' ρ (ha u hu)))
          · subst he
            rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
            · cases hb
            · cases he'
  | lit expanded ih =>
      intro k j
      obtain ⟨t', ht', hd'⟩ := ih k j
      rw [liftA_natExpandA_id] at ht'
      exact ⟨_, .lit ht', fun ρ _ h => hd' ρ h⟩

theorem translation_delift (hdef : DefinitionBodiesClosed E)
    (hhook : HookEnvironmentIndependent E F)
    {s : ExprA} :
    ∀ {k j : Nat} {t : Expr Nat},
      EnvironmentEval.Translation E F ν (liftA k j s) t →
    ∃ w, EnvironmentEval.Translation E F ν s w ∧
      ∀ (ρ : EnvI) {c : CptI}, denI ρ t c → denI (dropAtEnv ρ k j) w c := by
  induction s with
  | bvar i =>
      intro k j t ht
      by_cases hki : k ≤ i
      · have hsrc : liftA k j (.bvar i) = .bvar (i + j) := by
          simp only [liftA, if_pos hki]
        rw [hsrc] at ht
        cases ht with
        | cut =>
            exact ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
              have := EnvironmentEval.cutTerm_only_bottom h
              subst this; exact .bot _ _⟩
        | bvar _ =>
            refine ⟨.bvar i, .bvar i, fun ρ c h => ?_⟩
            cases h with
            | bot => exact .bot _ _
            | bvar h =>
                exact .bvar (by
                  simp only [dropAtEnv, if_neg (Nat.not_lt.mpr hki)]
                  exact h)
      · have hsrc : liftA k j (.bvar i) = .bvar i := by
          simp only [liftA, if_neg hki]
        rw [hsrc] at ht
        cases ht with
        | cut =>
            exact ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
              have := EnvironmentEval.cutTerm_only_bottom h
              subst this; exact .bot _ _⟩
        | bvar _ =>
            refine ⟨.bvar i, .bvar i, fun ρ c h => ?_⟩
            cases h with
            | bot => exact .bot _ _
            | bvar h =>
                exact .bvar (by
                  simp only [dropAtEnv, if_pos (Nat.lt_of_not_le hki)]
                  exact h)
  | sort l =>
      intro k j t ht
      have hsrc : liftA k j (.sort l) = .sort l := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          exact ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
            have := EnvironmentEval.cutTerm_only_bottom h
            subst this; exact .bot _ _⟩
      | sort _ =>
          exact ⟨sortTerm (eval ν l), .sort _, fun ρ _ h =>
            (FunctionEval.sortTerm_environment _ _ _ _).mp h⟩
  | const r ls =>
      intro k j t ht
      have hsrc : liftA k j (.const r ls) = .const r ls := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          exact ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
            have := EnvironmentEval.cutTerm_only_bottom h
            subst this; exact .bot _ _⟩
      | constRigid hr =>
          exact ⟨EnvironmentEval.rigidTerm E F ν r ls, .constRigid hr,
            fun ρ _ h => (rigidTerm_environmentIndependent hhook ν _ _ _ _ _).mp h⟩
      | constBody hb htr =>
          exact ⟨_, .constBody hb htr, fun ρ _ h =>
            translation_closed hdef hhook htr
              (closedAt_zero_of_closed (hdef _ _ _ hb))
              (fun i hi => absurd hi (Nat.not_lt_zero i)) h⟩
  | app f a ihf iha =>
      intro k j t ht
      have hsrc : liftA k j (.app f a) =
          .app (liftA k j f) (liftA k j a) := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          exact ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
            have := EnvironmentEval.cutTerm_only_bottom h
            subst this; exact .bot _ _⟩
      | app hf ha =>
          obtain ⟨wf, htwf, hf''⟩ := ihf hf
          obtain ⟨wa, htwa, ha''⟩ := iha ha
          refine ⟨.app wf wa, .app htwf htwa, fun ρ c h => ?_⟩
          rcases approxI_app_inv h with hb | ⟨g, s, he, hfg, hs, harg⟩ |
              ⟨r, args, u, he, hfg, harg⟩
          · subst hb; exact .bot _ _
          · subst he
            exact .app (hf'' ρ hfg) hs (fun u hu => ha'' ρ (harg u hu))
          · subst he
            exact .appSpine (hf'' ρ hfg) (ha'' ρ harg)
  | lam A u b ihA ihB =>
      intro k j t ht
      have hsrc : liftA k j (.lam A u b) =
          .lam (liftA k j A) u (liftA (k + 1) j b) := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          exact ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
            have := EnvironmentEval.cutTerm_only_bottom h
            subst this; exact .bot _ _⟩
      | lam htA htb =>
          obtain ⟨wA, htA', _⟩ := ihA htA
          obtain ⟨wb, htb', hB''⟩ := ihB htb
          refine ⟨.lam wA wb, .lam htA' htb', fun ρ c h => ?_⟩
          rcases approxI_lam_inv h with hb | ⟨g, he, hgb⟩
          · subst hb; exact .bot _ _
          · subst he
            exact .lam (fun s hs => by
              rw [← dropAtEnv_cons_succ]
              exact hB'' _ (hgb s hs))
  | pi A u B v ihA ihB =>
      intro k j t ht
      have hsrc : liftA k j (.pi A u B v) =
          .pi (liftA k j A) u (liftA (k + 1) j B) v := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          exact ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
            have := EnvironmentEval.cutTerm_only_bottom h
            subst this; exact .bot _ _⟩
      | pi htA htB =>
          obtain ⟨wA, htA', hA''⟩ := ihA htA
          obtain ⟨wB, htB', hB''⟩ := ihB htB
          refine ⟨taggedTerm (eval ν (.imax u v)) (.pi wA wB), ?_, fun ρ c h => ?_⟩
          · exact .pi htA' htB'
          · exact denI_tagged_pi_incl
              (fun x hx => hA'' ρ hx)
              (fun x y hy => by
                rw [← dropAtEnv_cons_succ]
                exact hB'' _ hy) h
  | letE A v b ihA ihv ihB =>
      intro k j t ht
      have hsrc : liftA k j (.letE A v b) =
          .letE (liftA k j A) (liftA k j v) (liftA (k + 1) j b) := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          exact ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
            have := EnvironmentEval.cutTerm_only_bottom h
            subst this; exact .bot _ _⟩
      | letE htA htv htb =>
          obtain ⟨wA, htA', _⟩ := ihA htA
          obtain ⟨wv, htv', hv''⟩ := ihv htv
          obtain ⟨wb, htb', hB''⟩ := ihB htb
          refine ⟨.letE wA wv wb, .letE htA' htv' htb', fun ρ c h => ?_⟩
          rcases approxI_letE_inv h with hb | happ
          · subst hb; exact .bot _ _
          · rcases approxI_app_inv happ with hb | ⟨g, s, he, hf, hs, ha⟩ |
                ⟨r, args, u, he, hf, ha⟩
            · subst hb; exact .bot _ _
            · subst he
              rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
              · cases hb
              · cases he'
                exact .letE (.app (.lam (fun s hs => by
                  rw [← dropAtEnv_cons_succ]
                  exact hB'' _ (hgb s hs))) hs
                  (fun u hu => hv'' ρ (ha u hu)))
            · subst he
              rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
              · cases hb
              · cases he'
  | lit n =>
      intro k j t ht
      have hsrc : liftA k j (.lit n) = .lit n := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          exact ⟨EnvironmentEval.cutTerm, .cut _, fun ρ _ h => by
            have := EnvironmentEval.cutTerm_only_bottom h
            subst this; exact .bot _ _⟩
      | lit expanded =>
          exact ⟨t, .lit expanded, fun ρ _ h =>
            translation_closed hdef hhook expanded (closedAt_natExpandA n)
              (fun i hi => absurd hi (Nat.not_lt_zero i)) h⟩

/-! ## §6 The paired substitution law -/

/-- The domain compacts inside a list of pi-payload compacts. -/
def piDoms (us : List CptI) : List CptI :=
  us.filterMap (fun u => match u with | .pi a _ => some a | _ => none)

/-- The fibre-row observations inside a list of pi-payload compacts. -/
def piRows (ρ : EnvI) (us : List CptI) : List (EnvI × CptI) :=
  us.flatMap (fun u => match u with
    | .pi _ f => f.map (fun s => (EnvI.cons (demand s.1) ρ, s.2))
    | _ => [])

/-- Denote the instantiated source at inserted index — introduction. -/
theorem denote_subst_intro (hdef : DefinitionBodiesClosed E)
    (hhook : HookEnvironmentIndependent E F)
    {e : ExprA} {t : Expr Nat} {s : ExprA}
    (ht : EnvironmentEval.Translation E F ν e t) :
    ∀ (j : Nat) (ρ : EnvI) (X : CptI → Prop) {c : CptI},
      denI (EnvI.insert ρ j X) t c →
      (∀ d, X d → EnvironmentEval.denote E F ν (EnvI.drop ρ j) s d) →
      EnvironmentEval.denote E F ν ρ (instantiateA j (liftA 0 j s) e) c := by
  induction ht with
  | cut e =>
      intro _ _ _ _ hc _
      have := EnvironmentEval.cutTerm_only_bottom hc
      subst this; exact EnvironmentEval.denote_bot _ _ _ _ _
  | bvar i =>
      intro j ρ X c hc hX
      rcases approxI_bvar_inv hc with hb | hb
      · subst hb; exact EnvironmentEval.denote_bot _ _ _ _ _
      · by_cases hlt : i < j
        · refine ⟨.bvar i, ?_, .bvar ?_⟩
          · show EnvironmentEval.Translation E F ν
                (if i = j then liftA 0 j s
                  else if j < i then .bvar (i - 1) else .bvar i) (.bvar i)
            rw [if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ j < i)]
            exact .bvar i
          · rw [EnvI.insert_lt _ hlt] at hb; exact hb
        · by_cases heq : i = j
          · subst heq
            have hXc : X c := by rw [EnvI.insert_self] at hb; exact hb
            obtain ⟨w, hsw, hwc⟩ := hX c hXc
            obtain ⟨t', ht', hincl⟩ := translation_lift hdef hhook hsw 0 i
            refine ⟨t', ?_, hincl ρ ?_⟩
            · show EnvironmentEval.Translation E F ν
                  (if i = i then liftA 0 i s
                    else if i < i then .bvar (i - 1) else .bvar i) t'
              rw [if_pos rfl]; exact ht'
            · rw [dropAtEnv_zero]; exact hwc
          · have hgt : j < i := by omega
            refine ⟨.bvar (i - 1), ?_, .bvar ?_⟩
            · show EnvironmentEval.Translation E F ν
                  (if i = j then liftA 0 j s
                    else if j < i then .bvar (i - 1) else .bvar i)
                  (.bvar (i - 1))
              rw [if_neg (by omega : ¬ i = j), if_pos hgt]
              exact .bvar _
            · rw [EnvI.insert_gt _ hgt] at hb; exact hb
  | sort l =>
      intro _ _ _ _ hc _
      exact ⟨sortTerm (eval ν l), .sort _,
        (FunctionEval.sortTerm_environment _ _ _ _).mp hc⟩
  | constRigid hr =>
      intro _ _ _ _ hc _
      exact ⟨_, .constRigid hr,
        (rigidTerm_environmentIndependent hhook ν _ _ _ _ _).mp hc⟩
  | constBody hb htr ih =>
      intro _ _ _ _ hc _
      exact ⟨_, .constBody hb htr,
        translation_closed hdef hhook htr
          (closedAt_zero_of_closed (hdef _ _ _ hb))
          (fun i hi => absurd hi (Nat.not_lt_zero i)) hc⟩
  | app hf ha ihf iha =>
      intro j ρ X c hc hX
      rcases approxI_app_inv hc with hb | ⟨g, s, he, hfg, hs, harg⟩ |
          ⟨r, args, u, he, hfg, harg⟩
      · subst hb; exact EnvironmentEval.denote_bot _ _ _ _ _
      · subst he
        obtain ⟨wf, htwf, hwf⟩ := ihf j ρ X hfg hX
        obtain ⟨wa, htwa, hwa⟩ := EnvironmentEval.finite_compacts s.1
          (fun u hu => iha j ρ X (harg u hu) hX)
        exact ⟨.app wf wa, .app htwf htwa, .app hwf hs hwa⟩
      · subst he
        obtain ⟨wf, htwf, hwf⟩ := ihf j ρ X hfg hX
        obtain ⟨wa, htwa, hwa⟩ := iha j ρ X harg hX
        exact ⟨.app wf wa, .app htwf htwa, .appSpine hwf hwa⟩
  | lam hA hb ihA ihB =>
      rename_i A b u A' b'
      intro j ρ X c hc hX
      rcases approxI_lam_inv hc with hb | ⟨g, he, hgb⟩
      · subst hb; exact EnvironmentEval.denote_bot _ _ _ _ _
      · subst he
        have hmerge : liftA 0 1 (liftA 0 j s) = liftA 0 (j + 1) s :=
          liftA_liftA_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) s
        obtain ⟨wA, htA, _⟩ := ihA j ρ X (.bot _ A') hX
        have hobs : ∀ p ∈
            List.map (fun sgm => (EnvI.cons (demand sgm.1) ρ, sgm.2)) g,
            EnvironmentEval.denote E F ν p.1
              (instantiateA (j + 1) (liftA 0 (j + 1) s) b) p.2 := by
          intro p hp
          obtain ⟨sgm, hsgm, rfl⟩ := List.mem_map.mp hp
          have hgb' : denI (EnvI.insert (EnvI.cons (demand sgm.1) ρ) (j + 1) X)
              b' sgm.2 := by
            rw [← EnvI.cons_insert]; exact hgb sgm hsgm
          have hd := ihB (j + 1) (EnvI.cons (demand sgm.1) ρ) X hgb'
            (fun d hd => by rw [EnvI.drop_cons]; exact hX d hd)
          exact hd
        obtain ⟨wb, htb, hwb⟩ := EnvironmentEval.finite_observations _ hobs
        have htb' : EnvironmentEval.Translation E F ν
            (instantiateA (j + 1) (liftA 0 1 (liftA 0 j s)) b) wb := by
          rw [← hmerge] at htb; exact htb
        exact ⟨.lam wA wb, .lam htA htb', .lam (fun sgm hsgm =>
          hwb _ (List.mem_map.mpr ⟨sgm, hsgm, rfl⟩))⟩
  | pi hA hB ihA ihB =>
      rename_i A B u v A' B'
      intro j ρ X c hc hX
      rcases approxI_app_inv hc with hb | ⟨g, sgm, he, hf, hs, harg⟩ |
          ⟨r, args, w, he, hf, harg⟩
      · subst hb; exact EnvironmentEval.denote_bot _ _ _ _ _
      · subst he
        have hmerge : liftA 0 1 (liftA 0 j s) = liftA 0 (j + 1) s :=
          liftA_liftA_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) s
        have hdoms : ∀ a ∈ piDoms sgm.1,
            EnvironmentEval.denote E F ν ρ (instantiateA j (liftA 0 j s) A) a := by
          intro a ha
          obtain ⟨u', hu', hfl⟩ := List.mem_filterMap.mp ha
          cases u' with
          | pi a' f' =>
              simp only [Option.some.injEq] at hfl; subst hfl
              rcases approxI_pi_inv (harg _ hu') with hb | ⟨a'', f'', hpi, hAa, hBf⟩
              · cases hb
              · cases hpi; exact ihA j ρ X hAa hX
          | bot => cases hfl
          | sort => cases hfl
          | lam _ => cases hfl
          | spine _ _ => cases hfl
        obtain ⟨wA, htA, hwA⟩ := EnvironmentEval.finite_compacts _ hdoms
        have hrows : ∀ p ∈ piRows ρ sgm.1,
            EnvironmentEval.denote E F ν p.1
              (instantiateA (j + 1) (liftA 0 (j + 1) s) B) p.2 := by
          intro p hp
          obtain ⟨u', hu', hfl⟩ := List.mem_flatMap.mp hp
          cases u' with
          | pi a' f' =>
              obtain ⟨sgm, hsgm, hpm⟩ := List.mem_map.mp hfl
              subst hpm
              rcases approxI_pi_inv (harg _ hu') with hb | ⟨a'', f'', hpi, hAa, hBf⟩
              · cases hb
              · cases hpi
                have hgb' : denI
                    (EnvI.insert (EnvI.cons (demand sgm.1) ρ) (j + 1) X)
                    B' sgm.2 := by
                  rw [← EnvI.cons_insert]; exact hBf sgm hsgm
                exact ihB (j + 1) (EnvI.cons (demand sgm.1) ρ) X hgb'
                  (fun d hd => by rw [EnvI.drop_cons]; exact hX d hd)
          | bot => cases hfl
          | sort => cases hfl
          | lam _ => cases hfl
          | spine _ _ => cases hfl
        obtain ⟨wB, htB, hwB⟩ := EnvironmentEval.finite_observations _ hrows
        have htB' : EnvironmentEval.Translation E F ν
            (instantiateA (j + 1) (liftA 0 1 (liftA 0 j s)) B) wB := by
          rw [← hmerge] at htB; exact htB
        refine ⟨taggedTerm (eval ν (.imax u v)) (.pi wA wB), .pi htA htB',
          .app ((taggedHead_environment _ _ _ _).mp hf) hs ?_⟩
        intro u' hu'
        rcases approxI_pi_inv (harg u' hu') with hb | ⟨a', f', hpi, hAa, hBf⟩
        · subst hb; exact .bot ρ _
        · subst hpi
          exact .pi (hwA a' (List.mem_filterMap.mpr
              ⟨.pi a' f', hu', rfl⟩))
            (fun sgm hsgm => hwB _ (List.mem_flatMap.mpr
              ⟨.pi a' f', hu', List.mem_map.mpr ⟨sgm, hsgm, rfl⟩⟩))
      · subst he
        have hmerge : liftA 0 1 (liftA 0 j s) = liftA 0 (j + 1) s :=
          liftA_liftA_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) s
        have hdoms : ∀ a ∈ piDoms [w],
            EnvironmentEval.denote E F ν ρ (instantiateA j (liftA 0 j s) A) a := by
          intro a ha
          obtain ⟨u', hu', hfl⟩ := List.mem_filterMap.mp ha
          have hu_eq : u' = w := List.mem_singleton.mp hu'
          subst hu_eq
          cases u' with
          | pi a' f' =>
              simp only [Option.some.injEq] at hfl; subst hfl
              rcases approxI_pi_inv harg with hb | ⟨a'', f'', hpi, hAa, hBf⟩
              · cases hb
              · cases hpi; exact ihA j ρ X hAa hX
          | bot => cases hfl
          | sort => cases hfl
          | lam _ => cases hfl
          | spine _ _ => cases hfl
        obtain ⟨wA, htA, hwA⟩ := EnvironmentEval.finite_compacts _ hdoms
        have hrows : ∀ p ∈ piRows ρ [w],
            EnvironmentEval.denote E F ν p.1
              (instantiateA (j + 1) (liftA 0 (j + 1) s) B) p.2 := by
          intro p hp
          obtain ⟨u', hu', hfl⟩ := List.mem_flatMap.mp hp
          have hu_eq : u' = w := List.mem_singleton.mp hu'
          subst hu_eq
          cases u' with
          | pi a' f' =>
              obtain ⟨sgm, hsgm, hpm⟩ := List.mem_map.mp hfl
              subst hpm
              rcases approxI_pi_inv harg with hb | ⟨a'', f'', hpi, hAa, hBf⟩
              · cases hb
              · cases hpi
                have hgb' : denI
                    (EnvI.insert (EnvI.cons (demand sgm.1) ρ) (j + 1) X)
                    B' sgm.2 := by
                  rw [← EnvI.cons_insert]; exact hBf sgm hsgm
                exact ihB (j + 1) (EnvI.cons (demand sgm.1) ρ) X hgb'
                  (fun d hd => by rw [EnvI.drop_cons]; exact hX d hd)
          | bot => cases hfl
          | sort => cases hfl
          | lam _ => cases hfl
          | spine _ _ => cases hfl
        obtain ⟨wB, htB, hwB⟩ := EnvironmentEval.finite_observations _ hrows
        have htB' : EnvironmentEval.Translation E F ν
            (instantiateA (j + 1) (liftA 0 1 (liftA 0 j s)) B) wB := by
          rw [← hmerge] at htB; exact htB
        refine ⟨taggedTerm (eval ν (.imax u v)) (.pi wA wB), .pi htA htB',
          .appSpine ((taggedHead_environment _ _ _ _).mp hf) ?_⟩
        rcases approxI_pi_inv harg with hb | ⟨a', f', hpi, hAa, hBf⟩
        · subst hb; exact .bot ρ _
        · subst hpi
          exact .pi (hwA a' (List.mem_filterMap.mpr
              ⟨.pi a' f', List.mem_singleton.mpr rfl, rfl⟩))
            (fun sgm hsgm => hwB _ (List.mem_flatMap.mpr
              ⟨.pi a' f', List.mem_singleton.mpr rfl,
                List.mem_map.mpr ⟨sgm, hsgm, rfl⟩⟩))
  | letE hA hv hb ihA ihv ihB =>
      rename_i A v b A' v' b'
      intro j ρ X c hc hX
      rcases approxI_letE_inv hc with hb | happ
      · subst hb; exact EnvironmentEval.denote_bot _ _ _ _ _
      · rcases approxI_app_inv happ with hb | ⟨g, row, he, hf, hs, ha⟩ |
            ⟨r, args, u, he, hf, ha⟩
        · subst hb; exact EnvironmentEval.denote_bot _ _ _ _ _
        · subst he
          rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
          · cases hb
          · cases he'
            have hmerge : liftA 0 1 (liftA 0 j s) = liftA 0 (j + 1) s :=
              liftA_liftA_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) s
            obtain ⟨wA, htA, _⟩ := ihA j ρ X (.bot _ A') hX
            obtain ⟨wv, htv, hwv⟩ := EnvironmentEval.finite_compacts row.1
              (fun u hu => ihv j ρ X (ha u hu) hX)
            have hobs : ∀ p ∈
                List.map (fun sgm => (EnvI.cons (demand sgm.1) ρ, sgm.2)) g,
                EnvironmentEval.denote E F ν p.1
                  (instantiateA (j + 1) (liftA 0 (j + 1) s) b) p.2 := by
              intro p hp
              obtain ⟨sgm, hsgm, rfl⟩ := List.mem_map.mp hp
              have hgb' : denI
                  (EnvI.insert (EnvI.cons (demand sgm.1) ρ) (j + 1) X)
                  b' sgm.2 := by
                rw [← EnvI.cons_insert]; exact hgb sgm hsgm
              exact ihB (j + 1) (EnvI.cons (demand sgm.1) ρ) X hgb'
                (fun d hd => by rw [EnvI.drop_cons]; exact hX d hd)
            obtain ⟨wb, htb, hwb⟩ := EnvironmentEval.finite_observations _ hobs
            have htb' : EnvironmentEval.Translation E F ν
                (instantiateA (j + 1) (liftA 0 1 (liftA 0 j s)) b) wb := by
              rw [← hmerge] at htb; exact htb
            exact ⟨.letE wA wv wb, .letE htA htv htb',
              .letE (.app (.lam (fun sgm hsgm =>
                hwb _ (List.mem_map.mpr ⟨sgm, hsgm, rfl⟩))) hs
                (fun u hu => hwv u hu))⟩
        · subst he
          rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
          · cases hb
          · cases he'
  | lit expanded ih =>
      rename_i n _
      intro _ _ _ _ hc _
      exact ⟨_, .lit expanded,
        translation_closed hdef hhook expanded (closedAt_natExpandA n)
          (fun i hi => absurd hi (Nat.not_lt_zero i)) hc⟩

/-- Denote at inserted index implies denotation of the instantiated
source — elimination direction. -/
theorem denote_subst_elim (hdef : DefinitionBodiesClosed E)
    (hhook : HookEnvironmentIndependent E F)
    {s : ExprA} :
    ∀ {e : ExprA} {t : Expr Nat} {j : Nat} {ρ : EnvI} {X : CptI → Prop}
      {c : CptI},
      EnvironmentEval.Translation E F ν (instantiateA j (liftA 0 j s) e) t →
      denI ρ t c →
      (∀ d, EnvironmentEval.denote E F ν (EnvI.drop ρ j) s d → X d) →
      EnvironmentEval.denote E F ν (EnvI.insert ρ j X) e c := by
  intro e
  induction e with
  | bvar i =>
      intro t j ρ X c ht hc hX
      by_cases hlt : i < j
      · have hsrc : instantiateA j (liftA 0 j s) (.bvar i) = .bvar i := by
          simp only [instantiateA]
          rw [if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ j < i)]
        rw [hsrc] at ht
        cases ht with
        | bvar _ =>
            rcases approxI_bvar_inv hc with hb | hb
            · subst hb; exact ⟨.bvar i, .bvar i, .bot _ _⟩
            · exact ⟨.bvar i, .bvar i, .bvar (by
                rw [EnvI.insert_lt _ hlt]; exact hb)⟩
        | cut =>
            have := EnvironmentEval.cutTerm_only_bottom hc
            subst this; exact ⟨.bvar i, .bvar i, .bot _ _⟩
      · by_cases heq : i = j
        · subst heq
          have hsrc : instantiateA i (liftA 0 i s) (.bvar i) = liftA 0 i s := by
            show (if i = i then liftA 0 i s else _) = liftA 0 i s
            rw [if_pos rfl]
          rw [hsrc] at ht
          obtain ⟨w, hsw, hw⟩ := translation_delift hdef hhook ht
          have hwc : denI (EnvI.drop ρ i) w c := by
            have := hw ρ hc; rwa [dropAtEnv_zero] at this
          have hXc : X c := hX c ⟨w, hsw, hwc⟩
          exact ⟨.bvar i, .bvar i, .bvar (by rw [EnvI.insert_self]; exact hXc)⟩
        · have hgt : j < i := by omega
          have hsrc : instantiateA j (liftA 0 j s) (.bvar i) = .bvar (i - 1) := by
            simp only [instantiateA]
            rw [if_neg heq, if_pos hgt]
          rw [hsrc] at ht
          cases ht with
          | bvar _ =>
              rcases approxI_bvar_inv hc with hb | hb
              · subst hb; exact ⟨.bvar i, .bvar i, .bot _ _⟩
              · exact ⟨.bvar i, .bvar i, .bvar (by
                  rw [EnvI.insert_gt _ hgt]; exact hb)⟩
          | cut =>
              have := EnvironmentEval.cutTerm_only_bottom hc
              subst this; exact ⟨.bvar i, .bvar i, .bot _ _⟩
  | sort l =>
      intro t j ρ X c ht hc hX
      have hsrc : instantiateA j (liftA 0 j s) (.sort l) = .sort l := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          have := EnvironmentEval.cutTerm_only_bottom hc
          subst this; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
      | sort _ =>
          exact ⟨sortTerm (eval ν l), .sort _,
            (FunctionEval.sortTerm_environment _ _ _ _).mp hc⟩
  | const r ls =>
      intro t j ρ X c ht hc hX
      have hsrc : instantiateA j (liftA 0 j s) (.const r ls) = .const r ls := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          have := EnvironmentEval.cutTerm_only_bottom hc
          subst this; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
      | constRigid hr =>
          exact ⟨_, .constRigid hr,
            (rigidTerm_environmentIndependent hhook ν _ _ _ _ _).mp hc⟩
      | constBody hb htr =>
          exact ⟨t, .constBody hb htr,
            translation_closed hdef hhook htr
              (closedAt_zero_of_closed (hdef _ _ _ hb))
              (fun i hi => absurd hi (Nat.not_lt_zero i)) hc⟩
  | app f a ihf iha =>
      intro t j ρ X c ht hc hX
      have hsrc : instantiateA j (liftA 0 j s) (.app f a) =
          .app (instantiateA j (liftA 0 j s) f)
            (instantiateA j (liftA 0 j s) a) := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          have := EnvironmentEval.cutTerm_only_bottom hc
          subst this; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
      | app hf ha =>
          rcases approxI_app_inv hc with hb | ⟨g, sgm, he, hfg, hs, harg⟩ |
              ⟨r, args, u, he, hfg, harg⟩
          · subst hb; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
          · subst he
            obtain ⟨wf, htwf, hwf⟩ := ihf hf hfg hX
            obtain ⟨wa, htwa, hwa⟩ := EnvironmentEval.finite_compacts sgm.1
              (fun u hu => iha ha (harg u hu) hX)
            exact ⟨.app wf wa, .app htwf htwa, .app hwf hs hwa⟩
          · subst he
            obtain ⟨wf, htwf, hwf⟩ := ihf hf hfg hX
            obtain ⟨wa, htwa, hwa⟩ := iha ha harg hX
            exact ⟨.app wf wa, .app htwf htwa, .appSpine hwf hwa⟩
  | lam A u b ihA ihB =>
      intro t j ρ X c ht hc hX
      have hsrc : instantiateA j (liftA 0 j s) (.lam A u b) =
          .lam (instantiateA j (liftA 0 j s) A) u
            (instantiateA (j + 1) (liftA 0 1 (liftA 0 j s)) b) := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          have := EnvironmentEval.cutTerm_only_bottom hc
          subst this; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
      | lam htA htb =>
          rename_i tA tb
          have hmerge : liftA 0 1 (liftA 0 j s) = liftA 0 (j + 1) s :=
            liftA_liftA_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) s
          rw [hmerge] at htb
          obtain ⟨wA, htA', _⟩ := ihA htA (.bot _ tA) hX
          rcases approxI_lam_inv hc with hb | ⟨g, he, hgb⟩
          · subst hb; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
          · subst he
            have hobs : ∀ p ∈
                List.map (fun sgm =>
                  (EnvI.cons (demand sgm.1) (EnvI.insert ρ j X), sgm.2)) g,
                EnvironmentEval.denote E F ν p.1 b p.2 := by
              intro p hp
              obtain ⟨sgm, hsgm, rfl⟩ := List.mem_map.mp hp
              have hd := ihB htb (hgb sgm hsgm)
                (fun d hd => by rw [EnvI.drop_cons] at hd; exact hX d hd)
              rwa [EnvI.cons_insert]
            obtain ⟨wb, htb', hwb⟩ := EnvironmentEval.finite_observations _ hobs
            exact ⟨.lam wA wb, .lam htA' htb', .lam (fun sgm hsgm =>
              hwb _ (List.mem_map.mpr ⟨sgm, hsgm, rfl⟩))⟩
  | pi A u B v ihA ihB =>
      intro t j ρ X c ht hc hX
      have hsrc : instantiateA j (liftA 0 j s) (.pi A u B v) =
          .pi (instantiateA j (liftA 0 j s) A) u
            (instantiateA (j + 1) (liftA 0 1 (liftA 0 j s)) B) v := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          have := EnvironmentEval.cutTerm_only_bottom hc
          subst this; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
      | pi htA htB =>
          have hmerge : liftA 0 1 (liftA 0 j s) = liftA 0 (j + 1) s :=
            liftA_liftA_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) s
          rw [hmerge] at htB
          rcases approxI_app_inv hc with hb | ⟨g, sgm, he, hf, hs, harg⟩ |
              ⟨r, args, w, he, hf, harg⟩
          · subst hb; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
          · subst he
            have hdoms : ∀ a ∈ piDoms sgm.1,
                EnvironmentEval.denote E F ν (EnvI.insert ρ j X) A a := by
              intro a hmem
              obtain ⟨u', hu', hfl⟩ := List.mem_filterMap.mp hmem
              cases u' with
              | pi a' f' =>
                  simp only [Option.some.injEq] at hfl; subst hfl
                  rcases approxI_pi_inv (harg _ hu') with hb |
                      ⟨a'', f'', hpi, hAa, hBf⟩
                  · cases hb
                  · cases hpi; exact ihA htA hAa hX
              | bot => cases hfl
              | sort => cases hfl
              | lam _ => cases hfl
              | spine _ _ => cases hfl
            obtain ⟨wA, htA', hwA⟩ := EnvironmentEval.finite_compacts _ hdoms
            have hrows : ∀ p ∈ piRows (EnvI.insert ρ j X) sgm.1,
                EnvironmentEval.denote E F ν p.1 B p.2 := by
              intro p hp
              obtain ⟨u', hu', hfl⟩ := List.mem_flatMap.mp hp
              cases u' with
              | pi a' f' =>
                  obtain ⟨sgm2, hsgm2, hpm⟩ := List.mem_map.mp hfl
                  subst hpm
                  rcases approxI_pi_inv (harg _ hu') with hb |
                      ⟨a'', f'', hpi, hAa, hBf⟩
                  · cases hb
                  · cases hpi
                    have hd := ihB htB (hBf sgm2 hsgm2)
                      (fun d hd => by rw [EnvI.drop_cons] at hd; exact hX d hd)
                    show EnvironmentEval.denote E F ν
                      (EnvI.cons (demand sgm2.1) (EnvI.insert ρ j X)) B sgm2.2
                    rw [EnvI.cons_insert]; exact hd
              | bot => cases hfl
              | sort => cases hfl
              | lam _ => cases hfl
              | spine _ _ => cases hfl
            obtain ⟨wB, htB', hwB⟩ := EnvironmentEval.finite_observations _ hrows
            refine ⟨taggedTerm (eval ν (.imax u v)) (.pi wA wB), .pi htA' htB',
              .app ((taggedHead_environment _ _ _ _).mp hf) hs ?_⟩
            intro u' hu'
            rcases approxI_pi_inv (harg u' hu') with hb | ⟨a', f', hpi, hAa, hBf⟩
            · subst hb; exact .bot _ _
            · subst hpi
              exact .pi (hwA a' (List.mem_filterMap.mpr
                  ⟨.pi a' f', hu', rfl⟩))
                (fun sgm2 hsgm2 => hwB _ (List.mem_flatMap.mpr
                  ⟨.pi a' f', hu', List.mem_map.mpr ⟨sgm2, hsgm2, rfl⟩⟩))
          · subst he
            have hdoms : ∀ a ∈ piDoms [w],
                EnvironmentEval.denote E F ν (EnvI.insert ρ j X) A a := by
              intro a hmem
              obtain ⟨u', hu', hfl⟩ := List.mem_filterMap.mp hmem
              have hu_eq : u' = w := List.mem_singleton.mp hu'
              subst hu_eq
              cases u' with
              | pi a' f' =>
                  simp only [Option.some.injEq] at hfl; subst hfl
                  rcases approxI_pi_inv harg with hb |
                      ⟨a'', f'', hpi, hAa, hBf⟩
                  · cases hb
                  · cases hpi; exact ihA htA hAa hX
              | bot => cases hfl
              | sort => cases hfl
              | lam _ => cases hfl
              | spine _ _ => cases hfl
            obtain ⟨wA, htA', hwA⟩ := EnvironmentEval.finite_compacts _ hdoms
            have hrows : ∀ p ∈
                piRows (EnvI.insert ρ j X) [w],
                EnvironmentEval.denote E F ν p.1 B p.2 := by
              intro p hp
              obtain ⟨u', hu', hfl⟩ := List.mem_flatMap.mp hp
              have hu_eq : u' = w := List.mem_singleton.mp hu'
              subst hu_eq
              cases u' with
              | pi a' f' =>
                  obtain ⟨sgm2, hsgm2, hpm⟩ := List.mem_map.mp hfl
                  subst hpm
                  rcases approxI_pi_inv harg with hb |
                      ⟨a'', f'', hpi, hAa, hBf⟩
                  · cases hb
                  · cases hpi
                    have hd := ihB htB (hBf sgm2 hsgm2)
                      (fun d hd => by rw [EnvI.drop_cons] at hd; exact hX d hd)
                    show EnvironmentEval.denote E F ν
                      (EnvI.cons (demand sgm2.1) (EnvI.insert ρ j X)) B sgm2.2
                    rw [EnvI.cons_insert]; exact hd
              | bot => cases hfl
              | sort => cases hfl
              | lam _ => cases hfl
              | spine _ _ => cases hfl
            obtain ⟨wB, htB', hwB⟩ := EnvironmentEval.finite_observations _ hrows
            refine ⟨taggedTerm (eval ν (.imax u v)) (.pi wA wB), .pi htA' htB',
              .appSpine ((taggedHead_environment _ _ _ _).mp hf) ?_⟩
            rcases approxI_pi_inv harg with hb | ⟨a', f', hpi, hAa, hBf⟩
            · subst hb; exact .bot _ _
            · subst hpi
              exact .pi (hwA a' (List.mem_filterMap.mpr
                  ⟨.pi a' f', List.mem_singleton.mpr rfl, rfl⟩))
                (fun sgm2 hsgm2 => hwB _ (List.mem_flatMap.mpr
                  ⟨.pi a' f', List.mem_singleton.mpr rfl,
                    List.mem_map.mpr ⟨sgm2, hsgm2, rfl⟩⟩))
  | letE A v b ihA ihv ihB =>
      intro t j ρ X c ht hc hX
      have hsrc : instantiateA j (liftA 0 j s) (.letE A v b) =
          .letE (instantiateA j (liftA 0 j s) A)
            (instantiateA j (liftA 0 j s) v)
            (instantiateA (j + 1) (liftA 0 1 (liftA 0 j s)) b) := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          have := EnvironmentEval.cutTerm_only_bottom hc
          subst this; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
      | letE htA htv htb =>
          rename_i tA tv tb
          have hmerge : liftA 0 1 (liftA 0 j s) = liftA 0 (j + 1) s :=
            liftA_liftA_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) s
          rw [hmerge] at htb
          rcases approxI_letE_inv hc with hb | happ
          · subst hb; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
          · rcases approxI_app_inv happ with hb | ⟨g, sgm, he, hf, hs, ha⟩ |
                ⟨r, args, u, he, hf, ha⟩
            · subst hb; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
            · subst he
              rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
              · cases hb
              · cases he'
                obtain ⟨wA, htA', _⟩ := ihA htA (.bot _ tA) hX
                obtain ⟨wv, htv', hwv⟩ := EnvironmentEval.finite_compacts sgm.1
                  (fun u hu => ihv htv (ha u hu) hX)
                have hobs : ∀ p ∈
                    List.map (fun sgm2 =>
                      (EnvI.cons (demand sgm2.1) (EnvI.insert ρ j X), sgm2.2)) g,
                    EnvironmentEval.denote E F ν p.1 b p.2 := by
                  intro p hp
                  obtain ⟨sgm2, hsgm2, rfl⟩ := List.mem_map.mp hp
                  have hd := ihB htb (hgb sgm2 hsgm2)
                    (fun d hd => by rw [EnvI.drop_cons] at hd; exact hX d hd)
                  show EnvironmentEval.denote E F ν
                    (EnvI.cons (demand sgm2.1) (EnvI.insert ρ j X)) b sgm2.2
                  rw [EnvI.cons_insert]; exact hd
                obtain ⟨wb, htb', hwb⟩ :=
                  EnvironmentEval.finite_observations _ hobs
                exact ⟨.letE wA wv wb, .letE htA' htv' htb',
                  .letE (.app (.lam (fun sgm2 hsgm2 =>
                    hwb _ (List.mem_map.mpr ⟨sgm2, hsgm2, rfl⟩))) hs
                    (fun u hu => hwv u hu))⟩
            · subst he
              rcases approxI_lam_inv hf with hb | ⟨g', he', hgb⟩
              · cases hb
              · cases he'
  | lit n =>
      intro t j ρ X c ht hc hX
      have hsrc : instantiateA j (liftA 0 j s) (.lit n) = .lit n := rfl
      rw [hsrc] at ht
      cases ht with
      | cut =>
          have := EnvironmentEval.cutTerm_only_bottom hc
          subst this; exact ⟨EnvironmentEval.cutTerm, .cut _, .bot _ _⟩
      | lit expanded =>
          exact ⟨t, .lit expanded,
            translation_closed hdef hhook expanded (closedAt_natExpandA n)
              (fun i hi => absurd hi (Nat.not_lt_zero i)) hc⟩

/-- The paired substitution law at arbitrary index. -/
theorem denote_subst (hdef : DefinitionBodiesClosed E)
    (hhook : HookEnvironmentIndependent E F)
    (ν : Valuation) (ρ : EnvI) (j : Nat) (s e : ExprA) :
    ValueEq (EnvironmentEval.denote E F ν ρ (instantiateA j (liftA 0 j s) e))
      (EnvironmentEval.denote E F ν
        (EnvI.insert ρ j (EnvironmentEval.denote E F ν (EnvI.drop ρ j) s)) e) := by
  intro c; constructor
  · rintro ⟨t, ht, hc⟩
    exact denote_subst_elim hdef hhook ht hc (fun _ h => h)
  · rintro ⟨t, ht, hc⟩
    exact denote_subst_intro hdef hhook ht j ρ _ hc (fun _ h => h)

/-- The `j = 0` paired substitution port. -/
theorem denote_subst0 (hdef : DefinitionBodiesClosed E)
    (hhook : HookEnvironmentIndependent E F)
    (ν : Valuation) (ρ : EnvI) (s e : ExprA) :
    ValueEq (EnvironmentEval.denote E F ν ρ (instantiate0A s e))
      (EnvironmentEval.denote E F ν
        (EnvI.cons (EnvironmentEval.denote E F ν ρ s) ρ) e) := by
  have h := denote_subst hdef hhook ν ρ 0 s e
  rw [liftA_zero, EnvI.insert_zero, EnvI.drop_zero] at h
  exact h

/-! ## §7 The let equation and beta/zeta computations -/

/-- The let evaluation equation, premise-free: ζ-evaluates `letE` to the
body at the extended environment. -/
theorem denote_letE (E : ResolvedEnvA) (F : EnvironmentEval.FamilySyntax)
    (ν : Valuation) (ρ : EnvI) (A v b : ExprA) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.letE A v b))
      (EnvironmentEval.denote E F ν
        (EnvI.cons (EnvironmentEval.denote E F ν ρ v) ρ) b) := by
  intro c; constructor
  · rintro ⟨t, ht, hc⟩
    cases ht with
    | cut =>
        have := EnvironmentEval.cutTerm_only_bottom hc
        subst this; exact EnvironmentEval.denote_bot _ _ _ _ _
    | letE hA hv hb =>
        rcases approxI_letE_inv hc with hb' | happ
        · subst hb'; exact EnvironmentEval.denote_bot _ _ _ _ _
        · rcases approxI_app_inv happ with hb' | ⟨g, s, he, hf, hs, ha⟩ |
              ⟨r, args, u, he, hf, ha⟩
          · subst hb'; exact EnvironmentEval.denote_bot _ _ _ _ _
          · subst he
            rcases approxI_lam_inv hf with hb' | ⟨g', he', hgb⟩
            · cases hb'
            · cases he'
              exact ⟨_, hb, approxI_mono_env (cons_le_cons_env
                (fun u hu => ⟨_, hv, ha u hu⟩) (fun _ _ h => h)) (hgb s hs)⟩
          · subst he
            rcases approxI_lam_inv hf with hb' | ⟨g', he', hgb⟩
            · cases hb'
            · cases he'
  · rintro ⟨t, ht, hc⟩
    obtain ⟨us, hus, hb⟩ := approxI_factor hc 0
    have henv : EnvI.update (EnvI.cons (EnvironmentEval.denote E F ν ρ v) ρ) 0
        (demand us) = EnvI.cons (demand us) ρ := by
      funext i; cases i <;> simp [EnvI.update, EnvI.cons]
    rw [henv] at hb
    obtain ⟨tv, htv, htv'⟩ := EnvironmentEval.finite_compacts us
      (fun u hu => hus u hu)
    have hlam : denI ρ (.lam EnvironmentEval.cutTerm t) (.lam [(us, c)]) :=
      .lam (fun sgm hsgm => by
        obtain rfl := List.mem_singleton.mp hsgm
        exact hb)
    have happ : denI ρ (.app (.lam EnvironmentEval.cutTerm t) tv) c :=
      .app hlam (List.mem_singleton.mpr rfl) (fun u hu => htv' u hu)
    exact ⟨.letE EnvironmentEval.cutTerm tv t,
      .letE (.cut A) htv ht, .letE happ⟩

/-- ζ computation: `letE` denotes as its instantiated reduct. -/
theorem denote_zeta (hdef : DefinitionBodiesClosed E)
    (hhook : HookEnvironmentIndependent E F)
    (ν : Valuation) (ρ : EnvI) (A v b : ExprA) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.letE A v b))
      (EnvironmentEval.denote E F ν ρ (instantiate0A v b)) :=
  (denote_letE E F ν ρ A v b).trans (denote_subst0 hdef hhook ν ρ v b).symm

/-- β computation at the environment evaluator. -/
theorem denote_beta (hdef : DefinitionBodiesClosed E)
    (hhook : HookEnvironmentIndependent E F)
    (ν : Valuation) (ρ : EnvI) (A body arg : ExprA) (u : Level) :
    ValueEq (EnvironmentEval.denote E F ν ρ (.app (.lam A u body) arg))
      (EnvironmentEval.denote E F ν ρ (instantiate0A arg body)) :=
  (EnvironmentEval.denote_application E F ν ρ (.lam A u body) arg).trans
    ((EnvironmentEval.denote_lambda_application E F ν ρ A body u
      (EnvironmentEval.denote E F ν ρ arg)).trans
      (denote_subst0 hdef hhook ν ρ arg body).symm)

/-! ## §8 The six arms at the telescope image -/

/-- The EnvironmentEval model at the legacy universe attachment, at the
routed internal view and default neutral hook. -/
def substModel (E : ResolvedEnvA) : AnnSemantics :=
  EnvironmentLambdaArms.model (EnvironmentTelescopeInsertion.internalView E)
    (EnvironmentTelescopeInsertion.hook E EnvironmentEval.neutralFamilySyntax)

/-- The stored-data and hook ports my laws need, packaged from source
admission via the telescope suppliers. -/
theorem imageConditions {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvWfA I E) :
    DefinitionBodiesClosed (EnvironmentTelescopeInsertion.internalView E) ∧
    HookEnvironmentIndependent (EnvironmentTelescopeInsertion.internalView E)
      (EnvironmentTelescopeInsertion.hook E
        EnvironmentEval.neutralFamilySyntax) :=
  ⟨(EnvironmentTelescopePorts.internalView_body_conditions hE).2.2.2.2.1,
    (EnvironmentTelescopePorts.default_hook_conditions hE).2.1⟩

/-- The shared application judgment: pi-view decode, function relatedness,
and the substituted-type code. Mirrors `InductiveApplicationArms`. -/
theorem application_judgment {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E)
    {ν μ : Valuation} {Γ : LCtxA} {ρ σ : EnvI}
    {f g a b A B : ExprA} {u v : Level}
    (hf : PairedJudgment (substModel E) ν μ Γ ρ σ f g (.pi A u B v))
    (ha : PairedJudgment (substModel E) ν μ Γ ρ σ a b A)
    (ht : RelatedCode (substModel E).toCodeSystem
      ((substModel E).image ν Γ ρ (instantiate0A a B))
      ((substModel E).image μ Γ σ (instantiate0A a B))) :
    PairedJudgment (substModel E) ν μ Γ ρ σ (.app f a) (.app g b)
      (instantiate0A a B) := by
  obtain ⟨kf, Rf, Sf, hcf, hfg⟩ := hf
  obtain ⟨ka, Ra, Sa, hca, hab⟩ := ha
  obtain ⟨kt, Rt, St, hct⟩ := ht
  have hcodef : CodeI kf (EnvironmentEval.denote _ _ ν ρ (.pi A u B v)) Rf :=
    hcf.left_code
  obtain ⟨kA, kB, D, C, hD, hC, hcoherent, hRf⟩ :=
    EnvironmentLambdaArms.denote_pi_view hcodef
  have hRa : CodeI ka (EnvironmentEval.denote _ _ ν ρ A) Ra := hca.left_code
  have harg : D (EnvironmentEval.denote _ _ ν ρ a)
      (EnvironmentEval.denote _ _ μ σ b) :=
    (code_coherent hRa hD _ _).mp hab
  have hfun : FunctionPER NeutralPi.applyValue D C
      (EnvironmentEval.denote _ _ ν ρ f) (EnvironmentEval.denote _ _ μ σ g) :=
    (hRf _ _).mp hfg
  have hresult := EnvironmentEval.denote_applications_related hfun harg
  have hcode : CodeI kB (EnvironmentEval.denote _ _ ν ρ (instantiate0A a B))
      (C (EnvironmentEval.denote _ _ ν ρ a)) :=
    code_value_eq (hC _ _ harg)
      (denote_subst0 (imageConditions hE).1 (imageConditions hE).2 ν ρ a B).symm
  have hRt : CodeI kt (EnvironmentEval.denote _ _ ν ρ (instantiate0A a B)) Rt :=
    hct.left_code
  refine ⟨kt, Rt, St, hct, ?_⟩
  exact (code_coherent hcode hRt _ _).mp hresult

theorem ty_app_supplied {I : IotaIfaceA} (E : ResolvedEnvA)
    (hE : EnvWfA I E) (n : Nat) :
    PairedArms.Ty_app (substModel E) E I n := by
  intro Γ f a A B u v w hB hTy hf ha ihB ihTy ihf iha hΓ ν μ ρ σ hν hρ
  have ht := (ihTy hΓ ν μ ρ σ hν hρ).related_types legacyUniverseTransport
  exact application_judgment hE (ihf hΓ ν μ ρ σ hν hρ)
    (iha hΓ ν μ ρ σ hν hρ) ht

theorem conv_app_supplied {I : IotaIfaceA} (E : ResolvedEnvA)
    (hE : EnvWfA I E) (n : Nat) :
    PairedArms.Conv_app (substModel E) E I n := by
  intro Γ f g a b A B u v hfg hab hB hrt ihfg ihab ihB ihrt hΓ ν μ ρ σ hν hρ
  exact application_judgment hE (ihfg hΓ ν μ ρ σ hν hρ)
    (ihab hΓ ν μ ρ σ hν hρ) (ihrt hΓ ν μ ρ σ hν hρ).type_related

theorem conv_beta_supplied {I : IotaIfaceA} (E : ResolvedEnvA)
    (hE : EnvWfA I E) (n : Nat) :
    PairedArms.Conv_beta (substModel E) E I n := by
  intro Γ A u body arg B _ _ _ _ _ _ _ ih_red hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hc, hr⟩ := ih_red hΓ ν μ ρ σ hν hρ
  refine ⟨k, R, S, hc, ?_⟩
  change R (EnvironmentEval.denote _ _ ν ρ (.app (.lam A u body) arg))
    (EnvironmentEval.denote _ _ μ σ (instantiate0A arg body))
  rw [NeutralCodes.valueEq_eq
    (denote_beta (imageConditions hE).1 (imageConditions hE).2 ν ρ A body arg u)]
  exact hr

theorem ty_letE_supplied {I : IotaIfaceA} (E : ResolvedEnvA)
    (hE : EnvWfA I E) (n : Nat) :
    PairedArms.Ty_letE (substModel E) E I n := by
  intro Γ A u w value B body hA hv hTy hb ih_hA ih_hv ih_hTy ih_hb hΓ ν μ ρ σ hν hρ
  obtain ⟨kv, Rv, Sv, hcpv, hrelv⟩ := ih_hv hΓ ν μ ρ σ hν hρ
  have hΓ' : CtxWfA E I n (.letBinding A value :: Γ) := .letBinding hΓ hA hv
  have hρ' : PairedRealises (substModel E) ν μ (.letBinding A value :: Γ)
      (EnvI.cons (EnvironmentEval.denote _ _ ν ρ value) ρ)
      (EnvI.cons (EnvironmentEval.denote _ _ μ σ value) σ) :=
    .letBinding hρ hcpv hrelv
      (TypedPER.left_member ((substModel E).lawful hcpv.left_code) hrelv)
      (hcpv.to_right
        (TypedPER.right_member ((substModel E).lawful hcpv.left_code) hrelv))
  obtain ⟨kb, Rb, Sb, hcpb, hrelb⟩ := ih_hb hΓ' ν μ
    (EnvI.cons (EnvironmentEval.denote _ _ ν ρ value) ρ)
    (EnvI.cons (EnvironmentEval.denote _ _ μ σ value) σ) hν hρ'
  refine ⟨kb, Rb, Sb,
    ⟨code_value_eq hcpb.left_code
        (denote_subst0 (imageConditions hE).1 (imageConditions hE).2 ν ρ value B).symm,
      code_value_eq hcpb.right_code
        (denote_subst0 (imageConditions hE).1 (imageConditions hE).2 μ σ value B).symm,
      hcpb.transport⟩, ?_⟩
  change Rb (EnvironmentEval.denote _ _ ν ρ (.letE A value body))
    (EnvironmentEval.denote _ _ μ σ (.letE A value body))
  rw [NeutralCodes.valueEq_eq (denote_letE _ _ ν ρ A value body),
    NeutralCodes.valueEq_eq (denote_letE _ _ μ σ A value body)]
  exact hrelb

theorem conv_zeta_supplied {I : IotaIfaceA} (E : ResolvedEnvA)
    (hE : EnvWfA I E) (n : Nat) :
    PairedArms.Conv_zeta (substModel E) E I n := by
  intro Γ A value body B u hA hv hb hred ih_hA ih_hv ih_hb ih_hred hΓ ν μ ρ σ hν hρ
  obtain ⟨kT, RT, ST, hcpT, hrelT⟩ := ih_hred hΓ ν μ ρ σ hν hρ
  refine ⟨kT, RT, ST, hcpT, ?_⟩
  change RT (EnvironmentEval.denote _ _ ν ρ (.letE A value body))
    (EnvironmentEval.denote _ _ μ σ (instantiate0A value body))
  rw [NeutralCodes.valueEq_eq
    (denote_zeta (imageConditions hE).1 (imageConditions hE).2 ν ρ A value body)]
  exact hrelT

/-- `Conv_letE` at the environment evaluator. The three iota regularity
hypotheses are required for `CtxWfA` of `.letBinding A v :: Γ` — the left
typings of the `ConvA` premises — via `convA_hasTy_left`; `EnvClosedA`
comes from `envWfA_closed hE`. No contract premise retains them. -/
theorem conv_letE_supplied {I : IotaIfaceA} (E : ResolvedEnvA)
    (hE : EnvWfA I E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) (n : Nat) :
    PairedArms.Conv_letE (substModel E) E I n := by
  intro Γ A A' v v' b b' B u hA hv hb hrt ih_hA ih_hv ih_hb ih_hrt
    hΓ ν μ ρ σ hν hρ
  obtain ⟨kv, Rv, Sv, hcpv, hrelv⟩ := ih_hv hΓ ν μ ρ σ hν hρ
  obtain ⟨k2, Rv2, Sv2, hcp2, hrel2⟩ := ih_hv hΓ μ μ σ σ
    (ValuationRel.refl μ) hρ.right_diagonal
  have hright : Sv (EnvironmentEval.denote _ _ μ σ v')
      (EnvironmentEval.denote _ _ μ σ v) :=
    ((substModel E).lawful hcpv.right_code).symm
      (((substModel E).coherent hcp2.right_code hcpv.right_code _ _).mp
        ((hcp2.transport _ _).mp hrel2))
  have hΓ' : CtxWfA E I n (.letBinding A v :: Γ) :=
    .letBinding hΓ
      (convA_hasTy_left (envWfA_closed hE) hI hR hIS hΓ hA)
      (convA_hasTy_left (envWfA_closed hE) hI hR hIS hΓ hv)
  have hρ' : PairedRealises (substModel E) ν μ (.letBinding A v :: Γ)
      (EnvI.cons (EnvironmentEval.denote _ _ ν ρ v) ρ)
      (EnvI.cons (EnvironmentEval.denote _ _ μ σ v') σ) :=
    .letBinding hρ hcpv hrelv
      (TypedPER.left_member ((substModel E).lawful hcpv.left_code) hrelv)
      hright
  obtain ⟨kb, Rb, Sb, hcpb, hrelb⟩ := ih_hb hΓ' ν μ
    (EnvI.cons (EnvironmentEval.denote _ _ ν ρ v) ρ)
    (EnvI.cons (EnvironmentEval.denote _ _ μ σ v') σ) hν hρ'
  obtain ⟨kT, RT, ST, hcpT, _⟩ := ih_hrt hΓ ν μ ρ σ hν hρ
  refine ⟨kT, RT, ST, hcpT, ?_⟩
  have hRbl : CodeI kb (EnvironmentEval.denote _ _ ν
      (EnvI.cons (EnvironmentEval.denote _ _ ν ρ v) ρ) B) Rb := hcpb.left_code
  have hRb : CodeI kb (EnvironmentEval.denote _ _ ν ρ (instantiate0A v B)) Rb :=
    code_value_eq hRbl
      (denote_subst0 (imageConditions hE).1 (imageConditions hE).2 ν ρ v B).symm
  have hTl : CodeI kT (EnvironmentEval.denote _ _ ν ρ (instantiate0A v B)) RT :=
    hcpT.left_code
  have hSR : Same RT Rb := code_coherent hTl hRb
  change RT (EnvironmentEval.denote _ _ ν ρ (.letE A v b))
    (EnvironmentEval.denote _ _ μ σ (.letE A' v' b'))
  rw [NeutralCodes.valueEq_eq (denote_letE _ _ ν ρ A v b),
    NeutralCodes.valueEq_eq (denote_letE _ _ μ σ A' v' b')]
  exact (hSR _ _).mpr hrelb

end Rcic.Declarative.Ann.LR3.EnvironmentEvalSubst
