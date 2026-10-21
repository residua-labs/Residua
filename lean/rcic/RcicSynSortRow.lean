import rcic.RcicSynLetTransportCL
import rcic.RcicERPiSlotConv

/-!
# Syntactic sortRow, build step 4a — Π-injectivity in E, sort/Π disjointness, and heterogeneous `TyCvP` chain `sortRow`

`research/rcic/semantic/S3_ES_ARMS.md` §50 and `S0_SORTROW_SYNTACTIC.md` §2.4, §4.

1. **§1 Π-injectivity in E (`convE_pi_inv_wf`) and Sort/Π disjointness in E (`not_convE_sort_pi_wf`)**:
   - `appN_eq_pi`, `appN_const_ne_pi`, `rStep_pi_inv`, `etaStep_pi_inv`, `eStep_pi_inv`,
     `rstar_eStep_pi_inv`, `lvlEq_pi_inv`, `convMod_of_rstar_fwd`.
   - `convE_pi_inv_wf`: for every `TableWF tbl`, `ConvMod (EStep tbl) LvlEq (.pi A B) (.pi A' B')`
     implies `ConvMod (EStep tbl) LvlEq A A' ∧ ConvMod (EStep tbl) LvlEq B B'`.
   - `not_convE_sort_pi_wf` and `not_convE_pi_sort_wf`: for every `TableWF tbl`,
     `¬ ConvMod (EStep tbl) LvlEq (.sort l) (.pi A B)` and `¬ ConvMod (EStep tbl) LvlEq (.pi A B) (.sort l)`.

2. **§2 `EUT` on `TyP.app` via Π-injectivity in E + `instEnd`**:
   - `eut_app_nodes_drop` and `eut_app_nodes_keep`: from `EUT tbl σ ρ hf₁ hf₂` on two function
     typings `hf₁ : TyP E n Γ f (.pi A₁ B₁)` and `hf₂ : TyP E n Γ f (.pi A₂ B₂)` and `CL`
     of `hfᵢ.reg.2` against canonical `TyP.pi` nodes, `convE_pi_inv_wf` extracts codomain
     convertibility `CL tbl σ (binderDisp b :: ρ) hB₁ hB₂`, and `instEnd` (with `CL tbl σ ρ ha₁ ha₂`
     on `keep`) yields `EUT tbl σ ρ (TyP.app ... hT₁) (TyP.app ... hT₂)`.

3. **§3 Conjecture 2.9 item 3 (`sort u ≢ Π A B`) and heterogeneous `TyCvP` chain `sortRow` (without `hUniq` / `DT012T`)**:
   - `not_cvp_sort_pi_es_cl`, `not_cvp_sort_pi_of_below`, `not_cvp_pi_sort_of_below`:
     no `CvP` between `sort u` and `.pi A B` can satisfy `ES` and `Below` under any `TableWF` table.
   - `TyCvP`, `TyCvP.ESChain`, `convMod_of_tyCvP_esChain`, `eqN_of_tyCvP_sorts_esChain`,
     `sortRow_of_tyCvP_esChain_id`, `not_tyCvP_sort_zero_succ_esChain`:
     a heterogeneous `TyCvP` chain between `sort u` and `sort v` (whose `.of` steps may sit at
     distinct intermediate sorts `uᵢ`, requiring **zero `hUniq` / `DT012T_type_uniqueness`**)
     collapses directly in `ConvMod (EStep tbl) LvlEq` via `ES` at each step and `CL` at each
     junction, yielding `eqN (σ u) (σ v)` (and `eqN u v` at `σ = id`).

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Π-injectivity in E (`convE_pi_inv_wf`) and Sort/Π disjointness in E (`not_convE_sort_pi_wf`) -/

theorem appN_eq_pi {f : ETm} {xs : List ETm} {A B : ETm} (h : ETm.appN f xs = .pi A B) :
    xs = [] ∧ f = .pi A B := by
  induction xs generalizing f with
  | nil => exact ⟨rfl, h⟩
  | cons x xs ih =>
      have h' := (ih h).2
      cases h'

theorem appN_const_ne_pi (c : Nat) (ls : List Level) (xs : List ETm) (A B : ETm) :
    ETm.appN (.const c ls) xs ≠ .pi A B := by
  intro h
  have h' := (appN_eq_pi h).2
  cases h'

theorem rStep_pi_inv {tbl : List CRule} {A B t : ETm} (h : RStep tbl (.pi A B) t) :
    (∃ A', t = .pi A' B ∧ RStep tbl A A') ∨ (∃ B', t = .pi A B' ∧ RStep tbl B B') := by
  generalize hs : ETm.pi A B = s at h
  cases h with
  | beta => cases hs
  | cr hc =>
      obtain ⟨c, ls, xs, rfl⟩ := cRoot_lhs hc
      exact absurd hs.symm (appN_const_ne_pi c ls xs A B)
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL _ hA =>
      cases hs
      exact .inl ⟨_, rfl, hA⟩
  | piR _ hB =>
      cases hs
      exact .inr ⟨_, rfl, hB⟩

theorem etaStep_pi_inv {A B t : ETm} (h : EtaStep (.pi A B) t) :
    (∃ A', t = .pi A' B ∧ EtaStep A A') ∨ (∃ B', t = .pi A B' ∧ EtaStep B B') := by
  generalize hs : ETm.pi A B = s at h
  cases h with
  | eta => cases hs
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL _ hA =>
      cases hs
      exact .inl ⟨_, rfl, hA⟩
  | piR _ hB =>
      cases hs
      exact .inr ⟨_, rfl, hB⟩

theorem eStep_pi_inv {tbl : List CRule} {A B t : ETm} (h : EStep tbl (.pi A B) t) :
    (∃ A', t = .pi A' B ∧ EStep tbl A A') ∨ (∃ B', t = .pi A B' ∧ EStep tbl B B') := by
  cases h with
  | inl hr =>
      rcases rStep_pi_inv hr with ⟨A', rfl, hA⟩ | ⟨B', rfl, hB⟩
      · exact .inl ⟨A', rfl, .inl hA⟩
      · exact .inr ⟨B', rfl, .inl hB⟩
  | inr he =>
      rcases etaStep_pi_inv he with ⟨A', rfl, hA⟩ | ⟨B', rfl, hB⟩
      · exact .inl ⟨A', rfl, .inr hA⟩
      · exact .inr ⟨B', rfl, .inr hB⟩

theorem rstar_eStep_pi_inv {tbl : List CRule} {A B t : ETm}
    (h : RStar (EStep tbl) (.pi A B) t) :
    ∃ A' B', t = .pi A' B' ∧ RStar (EStep tbl) A A' ∧ RStar (EStep tbl) B B' := by
  generalize hs : ETm.pi A B = s at h
  induction h generalizing A B with
  | refl =>
      exact ⟨A, B, hs.symm, .refl A, .refl B⟩
  | step h1 _ ih =>
      subst hs
      rcases eStep_pi_inv h1 with ⟨A₁, rfl, hA₁⟩ | ⟨B₁, rfl, hB₁⟩
      · obtain ⟨A', B', rfl, hA', hB'⟩ := ih rfl
        exact ⟨A', B', rfl, .step hA₁ hA', hB'⟩
      · obtain ⟨A', B', rfl, hA', hB'⟩ := ih rfl
        exact ⟨A', B', rfl, hA', .step hB₁ hB'⟩

theorem lvlEq_pi_inv {A₁ B₁ A₂ B₂ : ETm} (h : LvlEq (.pi A₁ B₁) (.pi A₂ B₂)) :
    LvlEq A₁ A₂ ∧ LvlEq B₁ B₂ := by
  cases h with
  | pi hA hB => exact ⟨hA, hB⟩

theorem convMod_of_rstar_fwd {R Q : ETm → ETm → Prop} {a b : ETm}
    (h : RStar R a b) : ConvMod R Q a b := by
  induction h with
  | refl a => exact .refl a
  | step h1 _ ih => exact .trans (.fwd h1) ih

/-- Π-INJECTIVITY IN E (`S0` §2.4 item 2): for every `TableWF` table,
    `ConvMod (EStep tbl) LvlEq (.pi A B) (.pi A' B')` implies
    `ConvMod (EStep tbl) LvlEq A A' ∧ ConvMod (EStep tbl) LvlEq B B'`. -/
theorem convE_pi_inv_wf {tbl : List CRule} (hW : TableWF tbl) {A B A' B' : ETm}
    (h : ConvMod (EStep tbl) LvlEq (.pi A B) (.pi A' B')) :
    ConvMod (EStep tbl) LvlEq A A' ∧ ConvMod (EStep tbl) LvlEq B B' := by
  obtain ⟨c, d, hc, hq, hd⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) h
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := rstar_eStep_pi_inv hc
  obtain ⟨A₂, B₂, rfl, hA₂, hB₂⟩ := rstar_eStep_pi_inv hd
  obtain ⟨hqA, hqB⟩ := lvlEq_pi_inv hq
  exact ⟨(convMod_of_rstar_fwd hA₁).trans ((ConvMod.eqv hqA).trans (convMod_of_rstar_rev hA₂)),
    (convMod_of_rstar_fwd hB₁).trans ((ConvMod.eqv hqB).trans (convMod_of_rstar_rev hB₂))⟩

/-- SORT/Π DISJOINTNESS IN E (`S0` §2.4 item 3): for every `TableWF` table,
    `sort l` and `pi A B` are never convertible modulo `≈`. -/
theorem not_convE_sort_pi_wf {tbl : List CRule} (hW : TableWF tbl) (l : Level) (A B : ETm) :
    ¬ ConvMod (EStep tbl) LvlEq (.sort l) (.pi A B) := by
  intro h
  obtain ⟨c, d, hc, hq, hd⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) h
  have hc' := rstar_of_normal (eStep_sort_normal tbl l) hc
  obtain ⟨A₂, B₂, rfl, _, _⟩ := rstar_eStep_pi_inv hd
  subst hc'
  cases hq

theorem not_convE_pi_sort_wf {tbl : List CRule} (hW : TableWF tbl) (A B : ETm) (l : Level) :
    ¬ ConvMod (EStep tbl) LvlEq (.pi A B) (.sort l) := by
  intro h
  exact not_convE_sort_pi_wf hW l A B (ConvMod.symm' LvlEq.symm' h)

/-! ## §2 `EUT` on `TyP.app` via Π-injectivity in E + `instEnd` -/

/-- `EUT` on two `TyP.app` nodes on a proof domain (`levelIsZero (σ u₁) = true`):
    `convE_pi_inv_wf` extracts `CL tbl σ (.drop :: ρ) hB₁ hB₂` from `EUT tbl σ ρ hf₁ hf₂`,
    and `instEnd_eps_drop` bridges to `hT₁, hT₂`. -/
theorem eut_app_nodes_drop {tbl : List CRule} (hW : TableWF tbl) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat}
    {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁)) (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A₂ (.sort u₂)) (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂))
    (hu₁ : levelIsZero (σ u₁) = true) (hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂))
    (heutf : EUT tbl σ ρ hf₁ hf₂)
    (hpi₁ : CL tbl σ ρ hf₁.reg.2 (TyP.pi E n Γ A₁ u₁ B₁ v₁ hA₁ hB₁))
    (hpi₂ : CL tbl σ ρ (TyP.pi E n Γ A₂ u₂ B₂ v₂ hA₂ hB₂) hf₂.reg.2)
    (hinst₁ : CL tbl σ ρ hT₁ (instEnd hB₁ ha₁ hA₁))
    (hinst₂ : CL tbl σ ρ (instEnd hB₂ ha₂ hA₂) hT₂) :
    EUT tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  have hu₂ : levelIsZero (σ u₂) = true := hbit.symm.trans hu₁
  have hpi₁' : ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (piSlot true (hB₁.eps σ (.drop :: ρ)))) (hf₁.reg.2.eps σ ρ) := by
    have h1 := ConvMod.symm' LvlEq.symm' hpi₁
    simpa only [CL, eps_pi_drop hu₁] using h1
  have hpi₂' : ConvMod (EStep tbl) LvlEq
      (hf₂.reg.2.eps σ ρ) (.pi (hA₂.eps σ ρ) (piSlot true (hB₂.eps σ (.drop :: ρ)))) := by
    have h2 := ConvMod.symm' LvlEq.symm' hpi₂
    simpa only [CL, eps_pi_drop hu₂] using h2
  have hconvPi : ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (piSlot true (hB₁.eps σ (.drop :: ρ))))
      (.pi (hA₂.eps σ ρ) (piSlot true (hB₂.eps σ (.drop :: ρ)))) :=
    hpi₁'.trans (heutf.trans hpi₂')
  have hBconv := convMod_unpiSlot hW.closed (convE_pi_inv_wf hW hconvPi).2
  have hinst₁' : ConvMod (EStep tbl) LvlEq (hT₁.eps σ ρ) (hB₁.eps σ (.drop :: ρ)) := by
    simpa only [CL, instEnd_eps_drop hB₁ ha₁ hA₁ hu₁] using hinst₁
  have hinst₂' : ConvMod (EStep tbl) LvlEq (hB₂.eps σ (.drop :: ρ)) (hT₂.eps σ ρ) := by
    simpa only [CL, instEnd_eps_drop hB₂ ha₂ hA₂ hu₂] using hinst₂
  exact hinst₁'.trans (hBconv.trans hinst₂')

/-- `EUT` on two `TyP.app` nodes on a relevant domain (`levelIsZero (σ u₁) = false`):
    `convE_pi_inv_wf` extracts `CL tbl σ (.keep :: ρ) hB₁ hB₂` from `EUT tbl σ ρ hf₁ hf₂`,
    and `instEnd_eps_keep` + `CL tbl σ ρ ha₁ ha₂` bridges to `hT₁, hT₂`. -/
theorem eut_app_nodes_keep {tbl : List CRule} (hW : TableWF tbl) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat}
    {u₁ v₁ w₁ u₂ v₂ w₂ : Level}
    (hf₁ : TyP E n Γ f (.pi A₁ B₁)) (ha₁ : TyP E n Γ a A₁)
    (hT₁ : TyP E n Γ (instantiate0 a B₁) (.sort w₁))
    (hf₂ : TyP E n Γ f (.pi A₂ B₂)) (ha₂ : TyP E n Γ a A₂)
    (hT₂ : TyP E n Γ (instantiate0 a B₂) (.sort w₂))
    (hA₁ : TyP E n Γ A₁ (.sort u₁)) (hB₁ : TyP E n (.assumption A₁ :: Γ) B₁ (.sort v₁))
    (hA₂ : TyP E n Γ A₂ (.sort u₂)) (hB₂ : TyP E n (.assumption A₂ :: Γ) B₂ (.sort v₂))
    (hu₁ : levelIsZero (σ u₁) = false) (hbit : levelIsZero (σ u₁) = levelIsZero (σ u₂))
    (heutf : EUT tbl σ ρ hf₁ hf₂)
    (hcla : CL tbl σ ρ ha₁ ha₂)
    (hpi₁ : CL tbl σ ρ hf₁.reg.2 (TyP.pi E n Γ A₁ u₁ B₁ v₁ hA₁ hB₁))
    (hpi₂ : CL tbl σ ρ (TyP.pi E n Γ A₂ u₂ B₂ v₂ hA₂ hB₂) hf₂.reg.2)
    (hinst₁ : CL tbl σ ρ hT₁ (instEnd hB₁ ha₁ hA₁))
    (hinst₂ : CL tbl σ ρ (instEnd hB₂ ha₂ hA₂) hT₂) :
    EUT tbl σ ρ
      (TyP.app E n Γ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E n Γ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) := by
  have hu₂ : levelIsZero (σ u₂) = false := hbit.symm.trans hu₁
  have hpi₁' : ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (hB₁.eps σ (.keep :: ρ))) (hf₁.reg.2.eps σ ρ) := by
    have h1 := ConvMod.symm' LvlEq.symm' hpi₁
    simpa only [CL, eps_pi_keep hu₁] using h1
  have hpi₂' : ConvMod (EStep tbl) LvlEq
      (hf₂.reg.2.eps σ ρ) (.pi (hA₂.eps σ ρ) (hB₂.eps σ (.keep :: ρ))) := by
    have h2 := ConvMod.symm' LvlEq.symm' hpi₂
    simpa only [CL, eps_pi_keep hu₂] using h2
  have hconvPi : ConvMod (EStep tbl) LvlEq
      (.pi (hA₁.eps σ ρ) (hB₁.eps σ (.keep :: ρ)))
      (.pi (hA₂.eps σ ρ) (hB₂.eps σ (.keep :: ρ))) :=
    hpi₁'.trans (heutf.trans hpi₂')
  have hBconv := (convE_pi_inv_wf hW hconvPi).2
  have hmid : ConvMod (EStep tbl) LvlEq
      (ETm.inst 0 (ha₁.eps σ ρ) (hB₁.eps σ (.keep :: ρ)))
      (ETm.inst 0 (ha₂.eps σ ρ) (hB₂.eps σ (.keep :: ρ))) :=
    (convMod_inst_body hW.closed hBconv 0 (ha₁.eps σ ρ)).trans
      (convMod_inst_repl hW.closed hcla (hB₂.eps σ (.keep :: ρ)) 0)
  have hinst₁' : ConvMod (EStep tbl) LvlEq
      (hT₁.eps σ ρ) (ETm.inst 0 (ha₁.eps σ ρ) (hB₁.eps σ (.keep :: ρ))) := by
    simpa only [CL, instEnd_eps_keep hB₁ ha₁ hA₁ hu₁] using hinst₁
  have hinst₂' : ConvMod (EStep tbl) LvlEq
      (ETm.inst 0 (ha₂.eps σ ρ) (hB₂.eps σ (.keep :: ρ))) (hT₂.eps σ ρ) := by
    simpa only [CL, instEnd_eps_keep hB₂ ha₂ hA₂ hu₂] using hinst₂
  exact hinst₁'.trans (hmid.trans hinst₂')

/-! ## §3 Conjecture 2.9 item 3 (`sort u ≢ Π A B`) and heterogeneous `TyCvP` chain `sortRow` -/

/-- Conjecture 2.9 item 3 from `ES` + `CL`: no `CvP E n Γ (.sort u) (.pi A B) T`
    can satisfy `ES` and endpoint `CL` under a `TableWF` table. -/
theorem not_cvp_sort_pi_es_cl {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u uA vB : Level} {A B T : Expr Nat}
    (h : CvP E n Γ (.sort u) (.pi A B) T)
    (hA : TyP E n Γ A (.sort uA)) (hB : TyP E n (.assumption A :: Γ) B (.sort vB))
    (σ : Level → Level) (ρ : List Disp)
    (hes : ES tbl σ ρ h)
    (hL : CL tbl σ ρ h.dl (TyP.sort E n Γ u (.succ u) (eqN_refl _)))
    (hR : CL tbl σ ρ h.dr (TyP.pi E n Γ A uA B vB hA hB)) :
    False := by
  have hL' : ConvMod (EStep tbl) LvlEq (.sort (σ u)) (h.dl.eps σ ρ) := by
    have h1 := ConvMod.symm' LvlEq.symm' hL
    simpa only [CL, eps_sort] using h1
  have hR' : ConvMod (EStep tbl) LvlEq (h.dr.eps σ ρ)
      (.pi (hA.eps σ ρ) (piSlot (levelIsZero (σ uA)) (hB.eps σ (binderDisp (levelIsZero (σ uA)) :: ρ)))) := by
    simpa only [CL, eps_pi_clause] using hR
  exact not_convE_sort_pi_wf hW (σ u) (hA.eps σ ρ)
    (piSlot (levelIsZero (σ uA)) (hB.eps σ (binderDisp (levelIsZero (σ uA)) :: ρ)))
    (hL'.trans (hes.trans hR'))

/-- Conjecture 2.9 item 3 from `Below`: wrapping `h : CvP E n Γ (.sort u) (.pi A B) (.sort (.imax uA vB))`
    in `CvP.symm` bounds `h.dl`, `h.dr`, `TyP.sort`, and `TyP.pi ... hA hB`. -/
theorem not_cvp_sort_pi_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u uA vB : Level} {A B : Expr Nat}
    (h : CvP E n Γ (.sort u) (.pi A B) (.sort (.imax uA vB)))
    (hA : TyP E n Γ A (.sort uA)) (hB : TyP E n (.assumption A :: Γ) B (.sort vB))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hes : ES tbl σ ρ h)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.symm E n Γ (.sort u) (.pi A B) (.sort (.imax uA vB)) h
        (TyP.pi E n Γ A uA B vB hA hB) h.dl))) :
    False := by
  let canonR := TyP.pi E n Γ A uA B vB hA hB
  let canonL := TyP.sort E n Γ u (.succ u) (eqN_refl _)
  let hsymm := CvP.symm E n Γ (.sort u) (.pi A B) (.sort (.imax uA vB)) h canonR h.dl
  have ht : hsymm.isTransport = false := rfl
  have hdl : h.dl.wt Aw < hsymm.wt Aw := by simp only [CvP.wt]; omega
  have hdr : h.dr.wt Aw < hsymm.wt Aw := by
    have := CvP.wt_dr_lt Aw h
    simp only [CvP.wt]; omega
  have hcL : canonL.wt Aw < hsymm.wt Aw := by
    have := TyP.wt_pos Aw h.dl
    simp only [TyP.wt, CvP.wt]; omega
  have hcR : canonR.wt Aw < hsymm.wt Aw := by simp only [CvP.wt]; omega
  have hL := cl_under Aw tbl hsymm ht Bel h.dl canonL σ ρ hρ hdl hcL
  have hR := cl_under Aw tbl hsymm ht Bel h.dr canonR σ ρ hρ hdr hcR
  exact not_cvp_sort_pi_es_cl hW h hA hB σ ρ hes hL hR

theorem not_cvp_pi_sort_of_below (Aw : Nat → Nat) {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u uA vB : Level} {A B : Expr Nat}
    (h : CvP E n Γ (.pi A B) (.sort u) (.sort (.imax uA vB)))
    (hA : TyP E n Γ A (.sort uA)) (hB : TyP E n (.assumption A :: Γ) B (.sort vB))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hes : ES tbl σ ρ h)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.symm E n Γ (.pi A B) (.sort u) (.sort (.imax uA vB)) h
        h.dr (TyP.pi E n Γ A uA B vB hA hB)))) :
    False := by
  let canonL := TyP.pi E n Γ A uA B vB hA hB
  let canonR := TyP.sort E n Γ u (.succ u) (eqN_refl _)
  let hsymm := CvP.symm E n Γ (.pi A B) (.sort u) (.sort (.imax uA vB)) h h.dr canonL
  have ht : hsymm.isTransport = false := rfl
  have hdl : h.dl.wt Aw < hsymm.wt Aw := by
    have := CvP.wt_dl_lt Aw h
    simp only [CvP.wt]; omega
  have hdr : h.dr.wt Aw < hsymm.wt Aw := by simp only [CvP.wt]; omega
  have hcL : canonL.wt Aw < hsymm.wt Aw := by simp only [CvP.wt]; omega
  have hcR : canonR.wt Aw < hsymm.wt Aw := by
    have := TyP.wt_pos Aw h.dr
    simp only [TyP.wt, CvP.wt]; omega
  have hL := cl_under Aw tbl hsymm ht Bel canonL h.dl σ ρ hρ hcL hdl
  have hR := cl_under Aw tbl hsymm ht Bel h.dr canonR σ ρ hρ hdr hcR
  have hL' : ConvMod (EStep tbl) LvlEq
      (.pi (hA.eps σ ρ) (piSlot (levelIsZero (σ uA)) (hB.eps σ (binderDisp (levelIsZero (σ uA)) :: ρ)))) (h.dl.eps σ ρ) := by
    simpa only [CL, canonL, eps_pi_clause] using hL
  have hR' : ConvMod (EStep tbl) LvlEq (h.dr.eps σ ρ) (.sort (σ u)) := by
    simpa only [CL, canonR, eps_sort] using hR
  exact not_convE_pi_sort_wf hW (hA.eps σ ρ)
    (piSlot (levelIsZero (σ uA)) (hB.eps σ (binderDisp (levelIsZero (σ uA)) :: ρ))) (σ u)
    (hL'.trans (hes.trans hR'))

/-- Enriched `TyConvT` chain: reflexive-transitive closure of `CvP E n Γ A B (.sort u)`
    at possibly distinct intermediate sorts `u`. -/
inductive TyCvP (E : ResolvedEnv) (n : Nat) : LCtx → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (A : Expr Nat) : TyCvP E n Γ A A
  | of (Γ : LCtx) (A B : Expr Nat) (u : Level) (h : CvP E n Γ A B (.sort u)) :
      TyCvP E n Γ A B
  | trans (Γ : LCtx) (A B C : Expr Nat) (h₁ : TyCvP E n Γ A B) (h₂ : TyCvP E n Γ B C) :
      TyCvP E n Γ A C

/-- `ES` and `CL` along a heterogeneous `TyCvP` chain between endpoint typings `dA` and `dB`:
    requires **zero `hUniq` / `DT012T_type_uniqueness`**, because `CL` is heterogeneous
    in the ascribed types (`T₁` vs `T₂`). -/
inductive TyCvP.ESChain (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {A B T₁ T₂ : Expr Nat} → TyCvP E n Γ A B →
    TyP E n Γ A T₁ → TyP E n Γ B T₂ → Prop
  | refl {A T₁ T₂ : Expr Nat} (dA : TyP E n Γ A T₁) (dB : TyP E n Γ A T₂)
      (hcl : CL tbl σ ρ dA dB) :
      TyCvP.ESChain tbl σ ρ (.refl Γ A) dA dB
  | of {A B T₁ T₂ : Expr Nat} {u : Level} (h : CvP E n Γ A B (.sort u))
      (dA : TyP E n Γ A T₁) (dB : TyP E n Γ B T₂)
      (hL : CL tbl σ ρ dA h.dl) (hes : ES tbl σ ρ h) (hR : CL tbl σ ρ h.dr dB) :
      TyCvP.ESChain tbl σ ρ (.of Γ A B u h) dA dB
  | trans {A B C T₁ T₂ Tₘ : Expr Nat} (h₁ : TyCvP E n Γ A B) (h₂ : TyCvP E n Γ B C)
      (dA : TyP E n Γ A T₁) (dM : TyP E n Γ B Tₘ) (dC : TyP E n Γ C T₂)
      (hc₁ : TyCvP.ESChain tbl σ ρ h₁ dA dM)
      (hc₂ : TyCvP.ESChain tbl σ ρ h₂ dM dC) :
      TyCvP.ESChain tbl σ ρ (.trans Γ A B C h₁ h₂) dA dC

/-- Every `TyCvP.ESChain` collapses directly to `ConvMod (EStep tbl) LvlEq (dA.eps σ ρ) (dB.eps σ ρ)`. -/
theorem convMod_of_tyCvP_esChain {tbl : List CRule} {σ : Level → Level} {ρ : List Disp}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B T₁ T₂ : Expr Nat}
    {c : TyCvP E n Γ A B} {dA : TyP E n Γ A T₁} {dB : TyP E n Γ B T₂}
    (hc : TyCvP.ESChain tbl σ ρ c dA dB) :
    ConvMod (EStep tbl) LvlEq (dA.eps σ ρ) (dB.eps σ ρ) := by
  induction hc with
  | refl _ _ hcl => exact hcl
  | of _ _ _ hL hes hR => exact hL.trans (hes.trans hR)
  | trans _ _ _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- HETEROGENEOUS CHAIN `sortRow` (`TypedRowsWf.sortRow` shape on `TyCvP`, with zero `hUniq`):
    for any `c : TyCvP E n Γ (.sort u) (.sort v)` satisfying `TyCvP.ESChain` between
    canonical `TyP.sort` nodes under a `TableWF` table, `eqN (σ u) (σ v)` holds. -/
theorem eqN_of_tyCvP_sorts_esChain {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u v : Level}
    (c : TyCvP E n Γ (.sort u) (.sort v))
    (σ : Level → Level) (ρ : List Disp)
    (hc : TyCvP.ESChain tbl σ ρ c
      (TyP.sort E n Γ u (.succ u) (eqN_refl _))
      (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    eqN (σ u) (σ v) := by
  have hconv : ConvMod (EStep tbl) LvlEq (.sort (σ u)) (.sort (σ v)) := by
    simpa only [eps_sort] using convMod_of_tyCvP_esChain hc
  exact eqN_of_convE_sort_wf hW hconv

/-- At `σ = id`, `eqN_of_tyCvP_sorts_esChain` yields `eqN u v` (`TypedRowsWf.sortRow`). -/
theorem sortRow_of_tyCvP_esChain_id {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u v : Level}
    (c : TyCvP E n Γ (.sort u) (.sort v))
    (ρ : List Disp)
    (hc : TyCvP.ESChain tbl id ρ c
      (TyP.sort E n Γ u (.succ u) (eqN_refl _))
      (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    eqN u v :=
  eqN_of_tyCvP_sorts_esChain hW c id ρ hc

/-- Non-vacuity of heterogeneous chain `sortRow`: no `TyCvP` chain between `sort 0`
    and `sort (succ u)` can satisfy `TyCvP.ESChain` under any `TableWF` table. -/
theorem not_tyCvP_sort_zero_succ_esChain {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u : Level}
    (c : TyCvP E n Γ (.sort .zero) (.sort (.succ u)))
    (ρ : List Disp)
    (hc : TyCvP.ESChain tbl id ρ c
      (TyP.sort E n Γ .zero (.succ .zero) (eqN_refl _))
      (TyP.sort E n Γ (.succ u) (.succ (.succ u)) (eqN_refl _))) :
    False :=
  not_eqN_zero_succ u (sortRow_of_tyCvP_esChain_id hW c ρ hc)

end Rcic.Syn
