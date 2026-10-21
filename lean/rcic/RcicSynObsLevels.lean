import rcic.RcicSynTable
import rcic.RcicUniverseClass

/-!
# S4 — δ-Level observation support (`OutLevels`/`GateLevels`, observation congruence, supply table, native u★ control)

`research/rcic/sortrow/S4_DELTA_LEVEL_OBSERVATIONS.md` §§1–3 (ChatGPT S4 #7322).
`closure_claim` stays 0.

1. **`TyP.outLevels θ` / `TyP.gateLevels θ`**: pure structural observers on a `TyP` derivation.
   `θ` records the real `linst` composite entered so far (`linst ls` recurses with
   `fun l => θ (instLevel ls l)`). Only the children `eps` actually reads are scanned:
   `bvar`'s domain typing, `lam`'s regularity fields, `conv`/`cctx`'s conversion trees, and
   `esub`/`lsub`'s `hvT` proof fields are never erasure dependencies.

2. **`obsLvlEq_eps` / `obsLvlEq_eps_id`**: the finite observation congruence —
   `eqN` on every `OutLevels` entry, exact `levelIsZero` bit equality on every `GateLevels`
   entry, and `DispLvlEq ρ₁ ρ₂` give `LvlEq (D.eps φ ρ₁) (D.eps ψ ρ₂)`. The proof reuses
   `lvlEq_eps`'s constructor decomposition and `DispLvlEq` transport helpers verbatim; a gate
   needs no full `eqN`, only the bit equation.

3. **§3 supply table**: `supplyOut_eq_of_bounded` (bounded observation, via
   `instLevel_map_of_levelHom`), `supplyOut_of_eqN_rep` (bounded representative route),
   `supplyGate_succ` (successor gate — both bits false under any `LevelHom`),
   `supplyGate_uniformType` / `supplyGate_uniformProp` (param-free uniform gates), and the
   residual obligation kept as `GateStable`/`OutStable` — a concrete body-observation
   obligation, never a global hypothesis.

4. **§2 native reverse control** (`Dvstar`): a real admission body typing
   `v = lam s₀ (bvar 0) : pi s₀ s₀` (s₀ = `sort zero`), whose λ-domain annotation is
   `u★ = succ (imax (param 0) zero)` via `CvP.sorts` retyping `s₀ : sort (succ zero)` to
   `s₀ : sort u★`. `u★` fails `levelBounded 0`, yet it is a successor so both exchange maps
   preserve its (false) bit — `deltaExchange_vstar` gives the δ exchange on the same `Dvstar`.

5. **Teeth**: `tooth_missing_gate_refuted` (an observer that omits the lam domain gate is
   refuted by `Dvstar`: its recorded-gate premise holds while keep/drop flips) and
   `tooth_levelBounded_everywhere_refuted` (the blanket `levelBounded`-everywhere contract is
   refuted by the `u★` pin). `W-TABLE-DELTA-OBSERVATION-STABILITY` stays open: certificates
   for every observation of every actual admission `Db` are a separate residue.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 structural observers -/

/-- The output-level observations of a derivation: levels whose `σ`-image actually appears in
    the erased term (`sort` heads and `const` level lists). `θ` is the `linst` composite
    entered so far, mirroring `TyP.eps`'s own σ-pass. -/
def TyP.outLevels (θ : Level → Level) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP E n Γ e T → List Level
  | _, _, _, _, _, .sort _ _ _ l _ _ => [θ l]
  | _, _, _, _, _, .bvar _ _ _ _ _ _ _ _ => []
  | _, _, _, _, _, .const _ _ _ _ ls _ _ _ _ _ _ _ _ => ls.map θ
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => hA.outLevels θ ++ hB.outLevels θ
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hbody _ => hbody.outLevels θ
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _ => hf.outLevels θ ++ ha.outLevels θ
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ hv hb _ => hv.outLevels θ ++ hb.outLevels θ
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.outLevels θ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _ => h.outLevels θ
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => D.outLevels θ
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv _ => D.outLevels θ ++ hv.outLevels θ
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv _ => D.outLevels θ ++ hv.outLevels θ
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D => D.outLevels (fun l => θ (instLevel ls l))
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.outLevels θ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.outLevels θ

/-- The gate-level observations of a derivation: levels whose `σ`-image decides a
    `levelIsZero` erasure branch (`bvar`, `const`, `pi`/`lam` domain sorts, `esub`). A gate is
    what decides keep/drop; it needs only the bit equation, never full `eqN`. -/
def TyP.gateLevels (θ : Level → Level) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP E n Γ e T → List Level
  | _, _, _, _, _, .sort _ _ _ _ _ _ => []
  | _, _, _, _, _, .bvar _ _ _ _ _ u _ _ => [θ u]
  | _, _, _, _, _, .const _ _ _ _ _ _ _ u _ _ _ _ _ => [θ u]
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB => θ u :: (hA.gateLevels θ ++ hB.gateLevels θ)
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ _ hbody _ => θ u :: hbody.gateLevels θ
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _ => hf.gateLevels θ ++ ha.gateLevels θ
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ hv hb _ => hv.gateLevels θ ++ hb.gateLevels θ
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.gateLevels θ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _ => h.gateLevels θ
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => D.gateLevels θ
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ u D _ hv _ => θ u :: (D.gateLevels θ ++ hv.gateLevels θ)
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv _ => D.gateLevels θ ++ hv.gateLevels θ
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D => D.gateLevels (fun l => θ (instLevel ls l))
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.gateLevels θ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.gateLevels θ

/-- The top-call views: `θ := id`, i.e. observations in the derivation's own level space. -/
def TyP.OutLevels {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : List Level := D.outLevels id

def TyP.GateLevels {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : List Level := D.gateLevels id

/-! ## §2 premise plumbing and the observation congruence -/

theorem obsPremise_append_left {P : Level → Prop} {xs ys : List Level}
    (h : ∀ l ∈ xs ++ ys, P l) : ∀ l ∈ xs, P l :=
  fun l hl => h l (List.mem_append_left ys hl)

theorem obsPremise_append_right {P : Level → Prop} {xs ys : List Level}
    (h : ∀ l ∈ xs ++ ys, P l) : ∀ l ∈ ys, P l :=
  fun l hl => h l (List.mem_append_right xs hl)

theorem obsPremise_cons {P : Level → Prop} {a : Level} {xs : List Level}
    (h : ∀ l ∈ a :: xs, P l) : ∀ l ∈ xs, P l :=
  fun l hl => h l (List.Mem.tail _ hl)

/-- `const`'s output list: pointwise `eqN` on the `θ`-images gives `eqNList` on the erased
    level lists (`eqNList_map_of_pointwise` specialized to recorded membership). -/
theorem eqNList_map_of_obs {θ φ ψ : Level → Level} {ls : List Level}
    (h : ∀ l ∈ ls.map θ, eqN (φ l) (ψ l)) :
    eqNList (ls.map (fun l => φ (θ l))) (ls.map (fun l => ψ (θ l))) := by
  induction ls with
  | nil => exact True.intro
  | cons l ls ih =>
      refine ⟨h (θ l) (List.mem_map.mpr ⟨l, List.Mem.head _, rfl⟩), ih ?_⟩
      intro l' hl'
      exact h l' (List.Mem.tail _ hl')

/-- The finite observation congruence: `eqN` on every recorded output level and bit equality
    on every recorded gate level suffice — the same constructor decomposition as `lvlEq_eps`,
    with each `hσ l` discharge replaced by the recorded membership. `θ` is the accumulated
    `linst` composite, so the lemma is invariant under level-instantiation nodes. -/
theorem obsLvlEq_eps :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → {θ φ ψ : Level → Level} → {ρ₁ ρ₂ : List Disp} →
    (∀ l ∈ D.outLevels θ, eqN (φ l) (ψ l)) →
    (∀ l ∈ D.gateLevels θ, levelIsZero (φ l) = levelIsZero (ψ l)) →
    DispLvlEq ρ₁ ρ₂ → LvlEq (D.eps (fun l => φ (θ l)) ρ₁) (D.eps (fun l => ψ (θ l)) ρ₂)
  | _, _, _, _, _, .sort _ _ _ l _ _, θ, φ, ψ, _, _, hout, _, _ =>
      .sort (hout (θ l) (List.mem_singleton.mpr rfl))
  | _, _, _, _, _, .bvar _ _ _ i _ u _ _, θ, φ, ψ, _, _, _, hgate, hρ => by
      have hbit : levelIsZero (φ (θ u)) = levelIsZero (ψ (θ u)) :=
        hgate (θ u) (List.mem_singleton.mpr rfl)
      simp only [TyP.eps, hbit]
      cases levelIsZero (ψ (θ u)) with
      | true => exact .star
      | false => exact lvlEq_resolve hρ i
  | _, _, _, _, _, .const _ _ _ r ls _ _ u _ _ _ _ _, θ, φ, ψ, _, _, hout, hgate, _ => by
      have hbit : levelIsZero (φ (θ u)) = levelIsZero (ψ (θ u)) :=
        hgate (θ u) (List.mem_singleton.mpr rfl)
      simp only [TyP.eps, hbit]
      cases levelIsZero (ψ (θ u)) with
      | true => exact .star
      | false => exact .const r (eqNList_map_of_obs hout)
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB, θ, φ, ψ, _, _, hout, hgate, hρ => by
      have hbit : levelIsZero (φ (θ u)) = levelIsZero (ψ (θ u)) := hgate (θ u) (List.Mem.head _)
      simp only [TyP.eps, hbit]
      cases levelIsZero (ψ (θ u)) with
      | true =>
          exact .pi (obsLvlEq_eps hA (obsPremise_append_left hout)
              (obsPremise_append_left (obsPremise_cons hgate)) hρ)
            ((obsLvlEq_eps hB (obsPremise_append_right hout)
              (obsPremise_append_right (obsPremise_cons hgate)) (.drop hρ)).lift' 0 1)
      | false =>
          exact .pi (obsLvlEq_eps hA (obsPremise_append_left hout)
              (obsPremise_append_left (obsPremise_cons hgate)) hρ)
            (obsLvlEq_eps hB (obsPremise_append_right hout)
              (obsPremise_append_right (obsPremise_cons hgate)) (.keep hρ))
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ hA hbody hB, θ, φ, ψ, ρ₁, ρ₂, hout, hgate, hρ => by
      have hbit : levelIsZero (φ (θ u)) = levelIsZero (ψ (θ u)) := hgate (θ u) (List.Mem.head _)
      cases hzu : levelIsZero (ψ (θ u)) with
      | true =>
          rw [eps_lam_drop (σ := fun l => φ (θ l)) (hbit.trans hzu),
            eps_lam_drop (σ := fun l => ψ (θ l)) hzu]
          exact obsLvlEq_eps hbody hout (obsPremise_cons hgate) (.drop hρ)
      | false =>
          rw [eps_lam_keep_eq hA hbody hB (σ := fun l => φ (θ l)) ρ₁ (hbit.trans hzu),
            eps_lam_keep_eq hA hbody hB (σ := fun l => ψ (θ l)) ρ₂ hzu]
          exact lvlEq_lam_match (obsLvlEq_eps hbody hout (obsPremise_cons hgate) (.keep hρ))
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha hT, θ, φ, ψ, _, _, hout, hgate, hρ => by
      rw [eps_app_eq hf ha hT, eps_app_eq hf ha hT]
      exact lvlEq_app_match
        (obsLvlEq_eps hf (obsPremise_append_left hout) (obsPremise_append_left hgate) hρ)
        (obsLvlEq_eps ha (obsPremise_append_right hout) (obsPremise_append_right hgate) hρ)
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT, θ, φ, ψ, _, _, hout, hgate, hρ => by
      rw [let_eps_eq hA hv hb hT, let_eps_eq hA hv hb hT]
      exact obsLvlEq_eps hb (obsPremise_append_right hout) (obsPremise_append_right hgate)
        (dispLvlEq_let_match
          (obsLvlEq_eps hv (obsPremise_append_left hout) (obsPremise_append_left hgate) hρ) hρ)
  | _, _, _, _, _, .lit _ _ _ _ _ hexp, θ, φ, ψ, _, _, hout, hgate, hρ =>
      obsLvlEq_eps hexp hout hgate hρ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, θ, φ, ψ, _, _, hout, hgate, hρ =>
      obsLvlEq_eps h hout hgate hρ
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D, θ, φ, ψ, _, ρ₂, hout, hgate, hρ => by
      have ih := obsLvlEq_eps D hout hgate (hρ.removeAt c)
      rcases hρ.getElem?_keep_cases c with ⟨hk₁, hk₂⟩ | ⟨hn₁, hn₂⟩
      · rw [eps_wk_keep hk₁, eps_wk_keep hk₂, hρ.countKeep_take_eq c]
        exact ih.lift' (countKeep (ρ₂.take c)) 1
      · rw [eps_wk_not_keep_of_ne hn₁, eps_wk_not_keep_of_ne hn₂]
        exact ih
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ hv _, θ, φ, ψ, _, ρ₂, hout, hgate, hρ => by
      have hbit : levelIsZero (φ (θ u)) = levelIsZero (ψ (θ u)) := hgate (θ u) (List.Mem.head _)
      simp only [TyP.eps, hbit]
      cases levelIsZero (ψ (θ u)) with
      | true =>
          exact obsLvlEq_eps D (obsPremise_append_left hout)
            (obsPremise_append_left (obsPremise_cons hgate)) (hρ.insertDisp_drop j)
      | false =>
          rw [hρ.countKeep_take_eq j]
          exact (obsLvlEq_eps D (obsPremise_append_left hout)
            (obsPremise_append_left (obsPremise_cons hgate))
            (hρ.insertDisp_keep j)).inst' (countKeep (ρ₂.take j))
            (obsLvlEq_eps hv (obsPremise_append_right hout)
              (obsPremise_append_right (obsPremise_cons hgate)) hρ)
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D hget hv hvT, θ, φ, ψ, _, _, hout, hgate, hρ => by
      rw [lsub_eps_eq D hget hv hvT, lsub_eps_eq D hget hv hvT]
      exact obsLvlEq_eps D (obsPremise_append_left hout) (obsPremise_append_left hgate)
        (dispLvlEq_lsub_match
          (obsLvlEq_eps hv (obsPremise_append_right hout) (obsPremise_append_right hgate) hρ)
          hρ j)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, θ, φ, ψ, _, _, hout, hgate, hρ =>
      obsLvlEq_eps D (θ := fun l => θ (instLevel ls l)) hout hgate hρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, θ, φ, ψ, _, _, hout, hgate, hρ =>
      obsLvlEq_eps D hout hgate hρ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, θ, φ, ψ, _, _, hout, hgate, hρ =>
      obsLvlEq_eps D hout hgate hρ

/-- The `θ := id` specialization stated against the top-call eps maps: `eqN` on `OutLevels`,
    bit equality on `GateLevels`, `DispLvlEq` on the disposition lists. -/
theorem obsLvlEq_eps_id {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) {φ ψ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (hout : ∀ l ∈ D.OutLevels, eqN (φ l) (ψ l))
    (hgate : ∀ l ∈ D.GateLevels, levelIsZero (φ l) = levelIsZero (ψ l))
    (hρ : DispLvlEq ρ₁ ρ₂) :
    LvlEq (D.eps φ ρ₁) (D.eps ψ ρ₂) :=
  obsLvlEq_eps D (θ := id) hout hgate hρ

/-- The δ-exchange shape on a closed derivation: `φ = instLevel (ls.map σ)` vs
    `ψ = fun l => σ (instLevel ls l)`, at `ρ := []`. -/
theorem obsLvlEq_eps_delta {E : ResolvedEnv} {a : Nat} {e T : Expr Nat}
    (D : TyP E a [] e T) {σ : Level → Level} {ls : List Level}
    (hout : ∀ l ∈ D.OutLevels, eqN (instLevel (ls.map σ) l) (σ (instLevel ls l)))
    (hgate : ∀ l ∈ D.GateLevels,
      levelIsZero (instLevel (ls.map σ) l) = levelIsZero (σ (instLevel ls l))) :
    LvlEq (D.eps (instLevel (ls.map σ)) []) (D.eps (fun l => σ (instLevel ls l)) []) :=
  obsLvlEq_eps_id D hout hgate .nil

/-! ## §3 per-observation supply table -/

theorem eqN_of_eqLevel {l l' : Level} (h : l = l') : eqN l l' :=
  fun ρ => congrArg (eval ρ) h

/-- `eqN` transports through `instLevel` (a fixed substitution is an `eval`-map on the
    valuation side). Sibling of `Rcic.Declarative.eqN_instLevel` (`RcicTypedLevels`), kept
    local so this module's import cone stays `RcicSynTable + RcicUniverseClass`. -/
theorem eqN_instLevel_obs {l l' : Level} (h : eqN l l') (ls : List Level) :
    eqN (instLevel ls l) (instLevel ls l') := fun ρ => by
  rw [eval_instLevel, eval_instLevel]
  exact h _

/-- A parameter-free level is fixed by every `instLevel` (`levelParamSubst` only reads
    `.param` leaves). -/
theorem instLevel_of_paramFree (ms : List Level) :
    (l : Level) → levelBounded 0 l = true → instLevel ms l = l
  | .zero, _ => rfl
  | .succ l, h => by
      rw [instLevel_succ, instLevel_of_paramFree ms l h]
  | .max a b, h => by
      rw [instLevel_max, instLevel_of_paramFree ms a (boolAnd_left h),
        instLevel_of_paramFree ms b (boolAnd_right h)]
  | .imax a b, h => by
      rw [instLevel_imax, instLevel_of_paramFree ms a (boolAnd_left h),
        instLevel_of_paramFree ms b (boolAnd_right h)]
  | .param i, h => absurd (of_decide_eq_true h) (Nat.not_lt_zero i)

/-- A parameter-free level is fixed by every `LevelHom` (the hom fields leave only the
    constructors a bounded level can actually use). -/
theorem LevelHom.map_of_paramFree {σ : Level → Level} (hσ : LevelHom σ) :
    (l : Level) → levelBounded 0 l = true → σ l = l
  | .zero, _ => hσ.map_zero
  | .succ l, h => by rw [hσ.map_succ, LevelHom.map_of_paramFree hσ l h]
  | .max a b, h => by
      rw [hσ.map_max, LevelHom.map_of_paramFree hσ a (boolAnd_left h),
        LevelHom.map_of_paramFree hσ b (boolAnd_right h)]
  | .imax a b, h => by
      rw [hσ.map_imax, LevelHom.map_of_paramFree hσ a (boolAnd_left h),
        LevelHom.map_of_paramFree hσ b (boolAnd_right h)]
  | .param i, h => absurd (of_decide_eq_true h) (Nat.not_lt_zero i)

/-- §3 row 1 — the level really has `levelBounded ls.length`: the original
    `instLevel_map_of_levelHom` supplies the output observation. -/
theorem supplyOut_eq_of_bounded {σ : Level → Level} (hσ : LevelHom σ) (ls : List Level)
    {l : Level} (hb : levelBounded ls.length l = true) :
    eqN (instLevel (ls.map σ) l) (σ (instLevel ls l)) :=
  eqN_of_eqLevel (instLevel_map_of_levelHom hσ ls l hb)

/-- §3 row 2 — `l` itself is not bounded, but a bounded representative `l₀` with
    `eqN l l₀` exists: both maps' `eqN`-preservation plus the exchange on `l₀` transport it. -/
theorem supplyOut_of_eqN_rep {φ ψ : Level → Level} {l l₀ : Level}
    (hφ : eqN (φ l) (φ l₀)) (hψ : eqN (ψ l) (ψ l₀)) (h₀ : eqN (φ l₀) (ψ l₀)) :
    eqN (φ l) (ψ l) :=
  eqN_trans hφ (eqN_trans h₀ (eqN_symm hψ))

/-- The uniform side facts: a `UniformProp` gate's bit is `true`, a `UniformType` gate's bit
    is `false`. -/
theorem levelIsZero_true_of_uniformProp {u : Level} (hUP : UniformProp u) :
    levelIsZero u = true := (levelUniformZero_iff u).mpr hUP

theorem levelIsZero_false_of_uniformType {u : Level} (hUT : UniformType u) :
    levelIsZero u = false := by
  cases hz : levelIsZero u with
  | false => rfl
  | true =>
      have hp : UniformProp u := (levelUniformZero_iff u).mp hz
      exact absurd (hUT fun _ => 0)
        (by rw [hp (fun _ => 0)]; exact Nat.lt_irrefl 0)

/-- §3 row 3 — the gate is a successor: both δ-exchange maps carry it to a `succ`, so both
    bits are false. -/
theorem supplyGate_succ_bits {σ : Level → Level} (hσ : LevelHom σ) (ms : List Level)
    (l : Level) :
    levelIsZero (instLevel (ms.map σ) (.succ l)) = false ∧
      levelIsZero (σ (instLevel ms (.succ l))) = false := by
  rw [instLevel_succ, instLevel_succ, hσ.map_succ]
  exact ⟨rfl, rfl⟩

/-- §3 row 3, premise form — the successor gate supplies the gate-bit equation. -/
theorem supplyGate_succ {σ : Level → Level} (hσ : LevelHom σ) (ms : List Level) (l : Level) :
    levelIsZero (instLevel (ms.map σ) (.succ l)) =
      levelIsZero (σ (instLevel ms (.succ l))) :=
  let h := supplyGate_succ_bits hσ ms l; h.1.trans h.2.symm

/-- §3 row 3′ — a parameter-free `UniformType` gate: both maps fix it, both bits are the
    `UniformType` `false`. -/
theorem supplyGate_uniformType {σ : Level → Level} (hσ : LevelHom σ) (ms : List Level)
    {u : Level} (hb : levelBounded 0 u = true) (hUT : UniformType u) :
    levelIsZero (instLevel (ms.map σ) u) = false ∧
      levelIsZero (σ (instLevel ms u)) = false := by
  rw [instLevel_of_paramFree _ u hb, instLevel_of_paramFree _ u hb,
    LevelHom.map_of_paramFree hσ u hb]
  exact ⟨levelIsZero_false_of_uniformType hUT, levelIsZero_false_of_uniformType hUT⟩

/-- §3 row 3′, premise form. -/
theorem supplyGate_uniformType_eq {σ : Level → Level} (hσ : LevelHom σ) (ms : List Level)
    {u : Level} (hb : levelBounded 0 u = true) (hUT : UniformType u) :
    levelIsZero (instLevel (ms.map σ) u) = levelIsZero (σ (instLevel ms u)) :=
  let h := supplyGate_uniformType hσ ms hb hUT; h.1.trans h.2.symm

/-- §3 row 4 — a parameter-free `UniformProp` gate: both maps fix it, both bits are the
    `UniformProp` `true`. -/
theorem supplyGate_uniformProp {σ : Level → Level} (hσ : LevelHom σ) (ms : List Level)
    {u : Level} (hb : levelBounded 0 u = true) (hUP : UniformProp u) :
    levelIsZero (instLevel (ms.map σ) u) = true ∧
      levelIsZero (σ (instLevel ms u)) = true := by
  rw [instLevel_of_paramFree _ u hb, instLevel_of_paramFree _ u hb,
    LevelHom.map_of_paramFree hσ u hb]
  exact ⟨levelIsZero_true_of_uniformProp hUP, levelIsZero_true_of_uniformProp hUP⟩

/-- §3 row 4, premise form. -/
theorem supplyGate_uniformProp_eq {σ : Level → Level} (hσ : LevelHom σ) (ms : List Level)
    {u : Level} (hb : levelBounded 0 u = true) (hUP : UniformProp u) :
    levelIsZero (instLevel (ms.map σ) u) = levelIsZero (σ (instLevel ms u)) :=
  let h := supplyGate_uniformProp hσ ms hb hUP; h.1.trans h.2.symm

/-- §3 row 5 — any other actual gate keeps a concrete body-observation stability obligation.
    These are the named shapes of `obsLvlEq_eps`'s premises; they are discharged per real
    admission `Db`, never promoted to a global hypothesis on all annotations. -/
def GateStable (φ ψ : Level → Level) (l : Level) : Prop :=
  levelIsZero (φ l) = levelIsZero (ψ l)

def OutStable (φ ψ : Level → Level) (l : Level) : Prop := eqN (φ l) (ψ l)

/-! ## §4 the native reverse control: `v = lam s₀ (bvar 0) : pi s₀ s₀` at `u★` -/

/-- `s₀`. Both `v` and `T` below are parameter-free as expressions. -/
def s0Expr : Expr Nat := .sort .zero

/-- `u★ = succ (imax (param 0) zero)`: syntactically mentions the out-of-range `param 0`,
    semantically `eqN` to `succ zero`. -/
def deltaStarU : Level := .succ (.imax (.param 0) .zero)

theorem eqN_succZero_deltaStarU : eqN (.succ .zero) deltaStarU := fun _ => rfl

theorem eqN_deltaStarU_succZero : eqN deltaStarU (.succ .zero) := fun _ => rfl

theorem eqN_succSuccZero_succDeltaStarU : eqN (.succ (.succ .zero)) (.succ deltaStarU) :=
  fun _ => rfl

/-- `s₀ : sort (succ zero)`, the plain typing. -/
def tyP_s0_succZero : TyP emptyEnv 0 [] s0Expr (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 [] .zero (.succ .zero) (eqN_refl _)

/-- `sort (succ zero) ≡ sort u★` at `sort (succ (succ zero))`, the original `CvP.sorts`
    with `eqN (succ zero) u★`. -/
def cvP_sorts_uStar :
    CvP emptyEnv 0 [] (.sort (.succ .zero)) (.sort deltaStarU) (.sort (.succ (.succ .zero))) :=
  CvP.sorts emptyEnv 0 [] (.succ .zero) deltaStarU eqN_succZero_deltaStarU
    (TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.sort emptyEnv 0 [] deltaStarU (.succ (.succ .zero)) eqN_succSuccZero_succDeltaStarU)

/-- `s₀ : sort u★` — the **real domain typing** of the λ, via `conv` on the `CvP.sorts` step.
    The annotation `u★` is carried into the derivation, not the term. -/
def tyP_s0_uStar : TyP emptyEnv 0 [] s0Expr (.sort deltaStarU) :=
  TyP.conv emptyEnv 0 [] s0Expr (.sort (.succ .zero)) (.sort deltaStarU) (.succ (.succ .zero))
    tyP_s0_succZero cvP_sorts_uStar

/-- `bvar 0 : s₀` in context `[s₀]`, whose own domain typing `s₀ : sort (succ zero)` is an
    eps-unread regularity field — only its gate index `.succ .zero` is an observation. -/
def tyP_bvar0_s0 : TyP emptyEnv 0 [.assumption s0Expr] (.bvar 0) s0Expr :=
  TyP.bvar emptyEnv 0 [.assumption s0Expr] 0 s0Expr (.succ .zero) rfl
    (TyP.sort emptyEnv 0 [.assumption s0Expr] .zero (.succ .zero) (eqN_refl _))

/-- The admission body typing itself: `v = lam s₀ (bvar 0) : pi s₀ s₀`, with the λ-domain
    sort annotation `u★`. The original body and type are kept; nothing is rewritten to a
    canonical derivation. -/
def Dvstar : TyP emptyEnv 0 [] (.lam s0Expr (.bvar 0)) (.pi s0Expr s0Expr) :=
  TyP.lam emptyEnv 0 [] s0Expr deltaStarU (.bvar 0) s0Expr (.succ .zero)
    tyP_s0_uStar tyP_bvar0_s0
    (TyP.sort emptyEnv 0 [.assumption s0Expr] .zero (.succ .zero) (eqN_refl _))

/-- The recorded observations of `Dvstar`: no output levels (nothing is a `sort`/`const` leaf
    on the eps path) and exactly two gates — the λ-domain `u★`, then the `bvar` node's own
    domain-sort `.succ .zero`. -/
theorem outLevels_Dvstar : Dvstar.OutLevels = [] := rfl

theorem gateLevels_Dvstar : Dvstar.GateLevels = [deltaStarU, .succ .zero] := rfl

/-- `u★` is a recorded gate of the actual admission body typing. -/
theorem pin_uStar_is_gate : deltaStarU ∈ Dvstar.GateLevels := by
  rw [gateLevels_Dvstar]; exact List.Mem.head _

/-- The pin: `u★` fails `levelBounded 0` — it syntactically mentions `param 0`, which is out
    of range for an arity-0 body. -/
theorem pin_uStar_not_bounded : levelBounded 0 deltaStarU = false := rfl

/-- Yet `u★` is a successor, so **every** `LevelHom` δ-exchange preserves its gate bit:
    both sides stay `false`. -/
theorem pin_uStar_exchange_gate {σ : Level → Level} (hσ : LevelHom σ) (ls : List Level) :
    levelIsZero (instLevel (ls.map σ) deltaStarU) =
      levelIsZero (σ (instLevel ls deltaStarU)) :=
  supplyGate_succ hσ ls _

/-- The full observation supply on the actual `Dvstar`: the sole `u★` gate and the `bvar`
    gate `.succ .zero` are both successors, so `obsLvlEq_eps_delta` applies with empty output
    premises. -/
theorem deltaExchange_vstar {σ : Level → Level} (hσ : LevelHom σ) (ls : List Level) :
    LvlEq (Dvstar.eps (instLevel (ls.map σ)) [])
      (Dvstar.eps (fun l => σ (instLevel ls l)) []) :=
  obsLvlEq_eps_delta Dvstar
    (fun _ hl => by rw [outLevels_Dvstar] at hl; exact absurd hl (List.not_mem_nil _))
    (fun l hl => by
      rw [gateLevels_Dvstar] at hl
      cases hl with
      | head => exact supplyGate_succ hσ ls _
      | tail _ hl' =>
          cases hl' with
          | head => exact supplyGate_succ hσ ls _
          | tail _ h'' => exact absurd h'' (List.not_mem_nil _))

/-! ## §5 teeth -/

/-- The buggy observer for the first tooth: identical to `gateLevels` except it forgets the
    `lam` domain gate — an observer that misses a level which really decides keep/drop. -/
def TyP.gateLevelsMissLam (θ : Level → Level) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP E n Γ e T → List Level
  | _, _, _, _, _, .sort _ _ _ _ _ _ => []
  | _, _, _, _, _, .bvar _ _ _ _ _ u _ _ => [θ u]
  | _, _, _, _, _, .const _ _ _ _ _ _ _ u _ _ _ _ _ => [θ u]
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB =>
      θ u :: (hA.gateLevelsMissLam θ ++ hB.gateLevelsMissLam θ)
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hbody _ => hbody.gateLevelsMissLam θ
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _ =>
      hf.gateLevelsMissLam θ ++ ha.gateLevelsMissLam θ
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ hv hb _ =>
      hv.gateLevelsMissLam θ ++ hb.gateLevelsMissLam θ
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.gateLevelsMissLam θ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _ => h.gateLevelsMissLam θ
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => D.gateLevelsMissLam θ
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ u D _ hv _ =>
      θ u :: (D.gateLevelsMissLam θ ++ hv.gateLevelsMissLam θ)
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv _ =>
      D.gateLevelsMissLam θ ++ hv.gateLevelsMissLam θ
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D =>
      D.gateLevelsMissLam (fun l => θ (instLevel ls l))
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.gateLevelsMissLam θ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.gateLevelsMissLam θ

/-- The counter-map for the tooth: sends exactly `u★` to `zero`, fixes everything else. -/
def phiUStarZero (l : Level) : Level := if l = deltaStarU then .zero else l

theorem phiUStarZero_at_uStar : phiUStarZero deltaStarU = .zero := rfl

theorem phiUStarZero_at_succZero : phiUStarZero (.succ .zero) = .succ .zero := rfl

/-- Tooth 1 — an observer missing the λ-domain gate is refused by `Dvstar`: the buggy
    premise `∀ l ∈ gateLevelsMissLam` is satisfied by `phiUStarZero` vs `id`, yet the
    erasures differ (`keep`-disposition on the binder flips to `.drop`, `.star` vs
    `.lam (.bvar 0)`), so no `LvlEq`. -/
theorem tooth_missing_gate_refuted :
    (∀ l ∈ Dvstar.gateLevelsMissLam id,
      levelIsZero (phiUStarZero l) = levelIsZero (id l)) ∧
    Dvstar.eps phiUStarZero [.keep] = .star ∧
    Dvstar.eps id [.keep] = .lam (.bvar 0) ∧
    ¬ LvlEq (Dvstar.eps phiUStarZero [.keep]) (Dvstar.eps id [.keep]) := by
  refine ⟨?_, rfl, rfl, fun h => by nomatch h⟩
  intro l hl
  have hl' : l = .succ .zero := by
    have : Dvstar.gateLevelsMissLam id = [.succ .zero] := rfl
    rw [this] at hl
    exact List.mem_singleton.mp hl
  rw [hl', phiUStarZero_at_succZero]; rfl

/-- Tooth 2 — the blanket "every erasure-read annotation is `levelBounded`" contract is
    refused by the `u★` pin: `u★` is a recorded gate yet fails `levelBounded 0`. -/
theorem tooth_levelBounded_everywhere_refuted :
    ¬ (∀ l ∈ Dvstar.GateLevels, levelBounded 0 l = true) := fun h => by
  have h0 : levelBounded 0 deltaStarU = true := h deltaStarU pin_uStar_is_gate
  rw [pin_uStar_not_bounded] at h0
  exact Bool.noConfusion h0

#print axioms Rcic.Syn.obsLvlEq_eps
#print axioms Rcic.Syn.obsLvlEq_eps_id
#print axioms Rcic.Syn.obsLvlEq_eps_delta
#print axioms Rcic.Syn.eqNList_map_of_obs
#print axioms Rcic.Syn.eqN_instLevel_obs
#print axioms Rcic.Syn.instLevel_of_paramFree
#print axioms Rcic.Syn.LevelHom.map_of_paramFree
#print axioms Rcic.Syn.supplyOut_eq_of_bounded
#print axioms Rcic.Syn.supplyOut_of_eqN_rep
#print axioms Rcic.Syn.supplyGate_succ_bits
#print axioms Rcic.Syn.supplyGate_succ
#print axioms Rcic.Syn.supplyGate_uniformType
#print axioms Rcic.Syn.supplyGate_uniformType_eq
#print axioms Rcic.Syn.supplyGate_uniformProp
#print axioms Rcic.Syn.supplyGate_uniformProp_eq
#print axioms Rcic.Syn.levelIsZero_true_of_uniformProp
#print axioms Rcic.Syn.levelIsZero_false_of_uniformType
#print axioms Rcic.Syn.eqN_succZero_deltaStarU
#print axioms Rcic.Syn.eqN_deltaStarU_succZero
#print axioms Rcic.Syn.eqN_succSuccZero_succDeltaStarU
#print axioms Rcic.Syn.outLevels_Dvstar
#print axioms Rcic.Syn.gateLevels_Dvstar
#print axioms Rcic.Syn.pin_uStar_is_gate
#print axioms Rcic.Syn.pin_uStar_not_bounded
#print axioms Rcic.Syn.pin_uStar_exchange_gate
#print axioms Rcic.Syn.deltaExchange_vstar
#print axioms Rcic.Syn.phiUStarZero_at_uStar
#print axioms Rcic.Syn.phiUStarZero_at_succZero
#print axioms Rcic.Syn.tooth_missing_gate_refuted
#print axioms Rcic.Syn.tooth_levelBounded_everywhere_refuted

end Rcic.Syn
