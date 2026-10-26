import rcic.RcicFamAppRevLok
import rcic.RcicAnnLRRows

/-!
# RcicFamAppTwinLokFund — `LOKc`-indexed LR fundamental theorem on the copy for recursor-free Prop-family twins (gap β core)

Per cc's 2026-10-25 04:30Z addendum:
`typedRowsWf_of_annEnvA` (`RcicAnnRowsSupply`) tracks the universe-arity bound (`levelsBounded n ls = true`),
erasing `Nonempty (ConvA ...)` from `EqKA` / `PropEqA` without the F3 stage bound `LOKc σ N K` (`RcicF3Defs`).
Meanwhile, `RcicFamAppRevLok` proved that:
1. Every step after the twin's rows (`bkConvB`, `bkTyConvB`, `trConv_selfB`, `twinIdxConvB`) preserves `LOKc σ N K`
   and `DiagRecIota`;
2. `RevEnv.rev_inj_internalB_lok` gives `LOKc σ N K` index conversion for every revealed singleton `R : RevEnv`
   directly from its AnySort recursor without using rows.

This module builds the **`LOKc`-indexed version of the copy's logical-relations fundamental theorem** for
recursor-free Prop-family twin environments (`gEnvA` / `R.twin₁A` shape: `I = noIotaA`, no recursors, no
constructors, no transparent bodies, and Prop-valued inductive families `u₀ = .zero`).

closure_claim = 0.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Rcic.Declarative.Ann.Lok

open Rcic.Declarative
open Rcic.Declarative.Ann
open Rcic.F3.PSet
open Rcic.Syn.ClassC (LOKtc castT LOKc_castT castHT LOKt_castHT LOKt_of_tyConv)

/-! ## §1 `LOK`-carrying base relations on the copy (`HasTyAL`, `ConvAL`, `TyConvAL`, `WhTyAL`, `StepAtAL`, `ParConvAL`) -/

/-- `LOKc` is preserved along `convT_of_tyConv` (`RcicDeclarative.lean`) with zero `.sorts` steps. -/
theorem LOKc_of_tyConv {E : ResolvedEnv} {n : Nat} {a b : Expr Nat} (σ : Nat → Nat) (N : Nat)
    (K : Nat → Nat) :
    ∀ {Γ : LCtx} {A B : Expr Nat} (d : ConvT E n Γ a b A) (c : TyConvT E n Γ A B),
      LOKc σ N K d → LOKtc σ N K c → LOKc σ N K (convT_of_tyConv d c)
  | _, _, _, d, .refl _ _, hd, _ => by simp only [convT_of_tyConv]; exact hd
  | _, _, _, d, .of _ _ _ u c, hd, hc => by
      simp only [convT_of_tyConv, LOKc]; simp only [LOKtc] at hc; exact ⟨hd, hc⟩
  | _, _, _, d, .trans _ _ _ _ c₁ c₂, hd, hc => by
      simp only [convT_of_tyConv]; simp only [LOKtc] at hc
      exact LOKc_of_tyConv σ N K _ c₂ (LOKc_of_tyConv σ N K d c₁ hd hc.1) hc.2

theorem LOKtc_symmT {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    ∀ {Γ : LCtx} {A B : Expr Nat} (c : TyConvT E n Γ A B),
      LOKtc σ N K c → LOKtc σ N K c.symmT
  | _, _, _, .refl _ _, _ => by simp only [TyConvT.symmT, LOKtc]
  | _, _, _, .of _ _ _ _ h, hc => by simp only [TyConvT.symmT, LOKtc, LOKc] at hc ⊢; exact hc
  | _, _, _, .trans _ _ _ _ c₁ c₂, hc => by
      simp only [LOKtc] at hc
      simp only [TyConvT.symmT, LOKtc]
      exact ⟨LOKtc_symmT σ N K c₂ hc.2, LOKtc_symmT σ N K c₁ hc.1⟩

theorem ex_hasTyT_lok_cast {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    {Γ Γ' : LCtx} {e e' A A' : Expr Nat} (hΓ : Γ = Γ') (he : e = e') (hA : A = A')
    (h : ∃ d : HasTyT E n Γ e A, LOKt σ N K d) :
    ∃ d' : HasTyT E n Γ' e' A', LOKt σ N K d' := by
  subst hΓ he hA; exact h

theorem ex_convT_lok_cast {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    {Γ Γ' : LCtx} {a a' b b' A A' : Expr Nat} (hΓ : Γ = Γ') (ha : a = a') (hb : b = b') (hA : A = A')
    (h : ∃ d : ConvT E n Γ a b A, LOKc σ N K d) :
    ∃ d' : ConvT E n Γ' a' b' A', LOKc σ N K d' := by
  subst hΓ ha hb hA; exact h

theorem ex_tyConvT_lok_cast {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    {Γ Γ' : LCtx} {A A' B B' : Expr Nat} (hΓ : Γ = Γ') (hA : A = A') (hB : B = B')
    (h : ∃ d : TyConvT E n Γ A B, LOKtc σ N K d) :
    ∃ d' : TyConvT E n Γ' A' B', LOKtc σ N K d' := by
  subst hΓ hA hB; exact h

mutual
/-- Weakening on `HasTyT` (`RcicTypedWeaken.lean`) preserves `LOKt σ N K`. -/
theorem hasTyT_weaken_lok (D : LocalDecl) {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat}
    {K : Nat → Nat} (hcl : EnvClosed E) :
    {c : Nat} → {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) →
      LOKt σ N K d →
      ∃ d' : HasTyT E n (insertAt D c Γ) (lift c 1 e) (lift c 1 A), LOKt σ N K d'
  | c, _, _, _, .sort Γ l, hd =>
      ⟨.sort (insertAt D c Γ) l, hd⟩
  | c, _, _, _, .bvar Γ i A h, _ => by
      by_cases hic : i < c
      · have hl := lookupType_insertAt_lt D hic h
        exact ex_hasTyT_lok_cast rfl (by simp only [lift, if_neg (by omega : ¬ c ≤ i)]) rfl
          ⟨.bvar (insertAt D c Γ) i (lift c 1 A) hl, trivial⟩
      · have hl := lookupType_insertAt_ge D (by omega : c ≤ i) h
        exact ex_hasTyT_lok_cast rfl (by simp only [lift, if_pos (by omega : c ≤ i)]) rfl
          ⟨.bvar (insertAt D c Γ) (i + 1) (lift c 1 A) hl, trivial⟩
  | c, _, _, _, .const Γ r ls m hres hlen hwf, hd => by
      have hm := (hcl r m hres).1 c
      exact ex_hasTyT_lok_cast rfl rfl (by simp only [lift_instantiateLevels, hm])
        ⟨.const (insertAt D c Γ) r ls m hres hlen hwf, hd⟩
  | c, _, _, _, .pi Γ A u B v hA hB, ⟨hu, hv, hdA, hdB⟩ => by
      obtain ⟨hA', hdA'⟩ := hasTyT_weaken_lok D hcl (c := c) hA hdA
      obtain ⟨hB', hdB'⟩ := hasTyT_weaken_lok D hcl (c := c + 1) hB hdB
      exact ⟨.pi _ _ u _ v hA' hB', by simp only [LOKt]; exact ⟨hu, hv, hdA', hdB'⟩⟩
  | c, _, _, _, .lam Γ A u body B hA hbody, ⟨hdA, hdb⟩ => by
      obtain ⟨hA', hdA'⟩ := hasTyT_weaken_lok D hcl (c := c) hA hdA
      obtain ⟨hb', hdb'⟩ := hasTyT_weaken_lok D hcl (c := c + 1) hbody hdb
      exact ⟨.lam _ _ u _ _ hA' hb', by simp only [LOKt]; exact ⟨hdA', hdb'⟩⟩
  | c, _, _, _, .app Γ f a A B hf ha, ⟨hdf, hda⟩ => by
      obtain ⟨hf', hdf'⟩ := hasTyT_weaken_lok D hcl (c := c) hf hdf
      obtain ⟨ha', hda'⟩ := hasTyT_weaken_lok D hcl (c := c) ha hda
      have h := lift_instantiate_low 1 c 0 a (by omega) B
      exact ex_hasTyT_lok_cast rfl rfl (by simp only [instantiate0]; exact h.symm)
        ⟨.app _ _ _ _ _ hf' ha', by simp only [LOKt]; exact ⟨hdf', hda'⟩⟩
  | c, _, _, _, .letE Γ A u value B body hA hv hb, ⟨hdA, hdv, hdb⟩ => by
      obtain ⟨hA', hdA'⟩ := hasTyT_weaken_lok D hcl (c := c) hA hdA
      obtain ⟨hv', hdv'⟩ := hasTyT_weaken_lok D hcl (c := c) hv hdv
      obtain ⟨hb', hdb'⟩ := hasTyT_weaken_lok D hcl (c := c + 1) hb hdb
      have h := lift_instantiate_low 1 c 0 value (by omega) B
      exact ex_hasTyT_lok_cast rfl rfl (by simp only [instantiate0]; exact h.symm)
        ⟨.letE _ _ u _ _ _ hA' hv' hb', by simp only [LOKt]; exact ⟨hdA', hdv', hdb'⟩⟩
  | c, _, _, _, .lit Γ t T hexp, hd => by
      obtain ⟨hexp', hd'⟩ := ex_hasTyT_lok_cast rfl (natExpand_lift c 1 t) rfl
        (hasTyT_weaken_lok D hcl (c := c) hexp hd)
      exact ⟨.lit _ _ _ hexp', hd'⟩
  | c, _, _, _, .conv Γ e A B u h hc, ⟨hd, hdc⟩ => by
      obtain ⟨h', hd'⟩ := hasTyT_weaken_lok D hcl (c := c) h hd
      obtain ⟨hc', hdc'⟩ := convT_weaken_lok D hcl (c := c) hc hdc
      exact ⟨.conv _ _ _ _ u h' hc', by simp only [LOKt]; exact ⟨hd', hdc'⟩⟩

/-- Weakening on `ConvT` (`RcicTypedWeaken.lean`) preserves `LOKc σ N K`. -/
theorem convT_weaken_lok (D : LocalDecl) {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat}
    {K : Nat → Nat} (hcl : EnvClosed E) :
    {c : Nat} → {Γ : LCtx} → {a b T : Expr Nat} → (d : ConvT E n Γ a b T) →
      LOKc σ N K d →
      ∃ d' : ConvT E n (insertAt D c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T), LOKc σ N K d'
  | c, _, _, _, _, .refl Γ a A h, hd => by
      obtain ⟨h', hd'⟩ := hasTyT_weaken_lok D hcl (c := c) h hd
      exact ⟨.refl _ _ _ h', hd'⟩
  | c, _, _, _, _, .symm Γ a b A h, hd => by
      obtain ⟨h', hd'⟩ := convT_weaken_lok D hcl (c := c) h hd
      exact ⟨.symm _ _ _ _ h', hd'⟩
  | c, _, _, _, _, .trans Γ a b b' A h1 h2, ⟨hd1, hd2⟩ => by
      obtain ⟨h1', hd1'⟩ := convT_weaken_lok D hcl (c := c) h1 hd1
      obtain ⟨h2', hd2'⟩ := convT_weaken_lok D hcl (c := c) h2 hd2
      exact ⟨.trans _ _ _ _ _ h1' h2', by simp only [LOKc]; exact ⟨hd1', hd2'⟩⟩
  | c, _, _, _, _, .beta Γ A body arg B u hA hbody harg, ⟨hdA, hdb, hda⟩ => by
      obtain ⟨hA', hdA'⟩ := hasTyT_weaken_lok D hcl (c := c) hA hdA
      obtain ⟨hb', hdb'⟩ := hasTyT_weaken_lok D hcl (c := c + 1) hbody hdb
      obtain ⟨hg', hda'⟩ := hasTyT_weaken_lok D hcl (c := c) harg hda
      have h := lift_instantiate_low 1 c 0 arg (by omega) B
      have h2 := lift_instantiate_low 1 c 0 arg (by omega) body
      exact ex_convT_lok_cast rfl rfl
        (by simp only [instantiate0]; exact h2.symm)
        (by simp only [instantiate0]; exact h.symm)
        ⟨.beta _ _ _ _ _ u hA' hb' hg', by simp only [LOKc]; exact ⟨hdA', hdb', hda'⟩⟩
  | c, _, _, _, _, .zeta Γ A value body B u hA hv hb, ⟨hdA, hdv, hdb⟩ => by
      obtain ⟨hA', hdA'⟩ := hasTyT_weaken_lok D hcl (c := c) hA hdA
      obtain ⟨hv', hdv'⟩ := hasTyT_weaken_lok D hcl (c := c) hv hdv
      obtain ⟨hb', hdb'⟩ := hasTyT_weaken_lok D hcl (c := c + 1) hb hdb
      have h := lift_instantiate_low 1 c 0 value (by omega) B
      have h2 := lift_instantiate_low 1 c 0 value (by omega) body
      exact ex_convT_lok_cast rfl rfl
        (by simp only [instantiate0]; exact h2.symm)
        (by simp only [instantiate0]; exact h.symm)
        ⟨.zeta _ _ _ _ _ u hA' hv' hb', by simp only [LOKc]; exact ⟨hdA', hdv', hdb'⟩⟩
  | c, _, _, _, _, .zetaLocal Γ i A v hval hty hv, hd => by
      obtain ⟨hv', hdv'⟩ := hasTyT_weaken_lok D hcl (c := c) hv hd
      by_cases hic : i < c
      · exact ex_convT_lok_cast rfl (by simp only [lift, if_neg (by omega : ¬ c ≤ i)]) rfl rfl
          ⟨.zetaLocal _ i _ _
            (lookupValue_insertAt_lt D hic hval) (lookupType_insertAt_lt D hic hty) hv',
            by simp only [LOKc]; exact hdv'⟩
      · have hge : c ≤ i := by omega
        exact ex_convT_lok_cast rfl (by simp only [lift, if_pos hge]) rfl rfl
          ⟨.zetaLocal _ (i + 1) _ _
            (lookupValue_insertAt_ge D hge hval)
            (lookupType_insertAt_ge D hge hty) hv',
            by simp only [LOKc]; exact hdv'⟩
  | c, _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb, ⟨hls, hdb⟩ => by
      have hbc : lift c 1 (instantiateLevels ls b) = instantiateLevels ls b := by
        rw [lift_instantiateLevels, (hcl r m hres).2 b hbody c]
      have hmt : lift c 1 (instantiateLevels ls m.mtype) = instantiateLevels ls m.mtype := by
        rw [lift_instantiateLevels, (hcl r m hres).1 c]
      obtain ⟨hb', hdb'⟩ := ex_hasTyT_lok_cast rfl hbc hmt
        (hasTyT_weaken_lok D hcl (c := c) hb hdb)
      exact ex_convT_lok_cast rfl rfl hbc.symm hmt.symm
        ⟨.delta _ r ls m b hres hbody htr hlen hwf hb', by simp only [LOKc]; exact ⟨hls, hdb'⟩⟩
  | c, _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs, ⟨hdl, hdr⟩ => by
      obtain ⟨hl', hdl'⟩ := hasTyT_weaken_lok D hcl (c := c) hlhs hdl
      obtain ⟨hr', hdr'⟩ := hasTyT_weaken_lok D hcl (c := c) hrhs hdr
      exact ⟨.iota _ _ _ _ (iotaLift E lhs rhs h c) hl' hr', by simp only [LOKc]; exact ⟨hdl', hdr'⟩⟩
  | c, _, _, _, _, .lit Γ t exp T h hexp, hd => by
      obtain ⟨hexp', hd'⟩ := hasTyT_weaken_lok D hcl (c := c) hexp hd
      exact ⟨.lit _ _ _ _ (litLift t exp h c) hexp', hd'⟩
  | c, _, _, _, _, .app Γ f g a b A B h1 h2, ⟨hd1, hd2⟩ => by
      obtain ⟨h1', hd1'⟩ := convT_weaken_lok D hcl (c := c) h1 hd1
      obtain ⟨h2', hd2'⟩ := convT_weaken_lok D hcl (c := c) h2 hd2
      have h := lift_instantiate_low 1 c 0 a (by omega) B
      exact ex_convT_lok_cast rfl rfl rfl (by simp only [instantiate0]; exact h.symm)
        ⟨.app _ _ _ _ _ _ _ h1' h2', by simp only [LOKc]; exact ⟨hd1', hd2'⟩⟩
  | c, _, _, _, _, .lam Γ A A' b b' B u hA hb, ⟨hdA, hdb⟩ => by
      obtain ⟨hA', hdA'⟩ := convT_weaken_lok D hcl (c := c) hA hdA
      obtain ⟨hb', hdb'⟩ := convT_weaken_lok D hcl (c := c + 1) hb hdb
      exact ⟨.lam _ _ _ _ _ _ u hA' hb', by simp only [LOKc]; exact ⟨hdA', hdb'⟩⟩
  | c, _, _, _, _, .pi Γ A A' B B' u v hA hB, ⟨hu, hv, hdA, hdB⟩ => by
      obtain ⟨hA', hdA'⟩ := convT_weaken_lok D hcl (c := c) hA hdA
      obtain ⟨hB', hdB'⟩ := convT_weaken_lok D hcl (c := c + 1) hB hdB
      exact ⟨.pi _ _ _ _ _ u v hA' hB', by simp only [LOKc]; exact ⟨hu, hv, hdA', hdB'⟩⟩
  | c, _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb, ⟨hdA, hdv, hdb⟩ => by
      obtain ⟨hA', hdA'⟩ := convT_weaken_lok D hcl (c := c) hA hdA
      obtain ⟨hv', hdv'⟩ := convT_weaken_lok D hcl (c := c) hv hdv
      obtain ⟨hb', hdb'⟩ := convT_weaken_lok D hcl (c := c + 1) hb hdb
      have h := lift_instantiate_low 1 c 0 v (by omega) B
      exact ex_convT_lok_cast rfl rfl rfl (by simp only [instantiate0]; exact h.symm)
        ⟨.letE _ _ _ _ _ _ _ _ u hA' hv' hb', by simp only [LOKc]; exact ⟨hdA', hdv', hdb'⟩⟩
  | c, _, _, _, _, .sorts Γ l₁ l₂ h, hd =>
      ⟨.sorts (insertAt D c Γ) l₁ l₂ h, hd⟩
  | c, _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h, hd => by
      have hm := (hcl r m hres).1 c
      exact ex_convT_lok_cast rfl rfl rfl (by simp only [lift_instantiateLevels, hm])
        ⟨.consts (insertAt D c Γ) r ls ls' m hres hlen hwf hwf' h, hd⟩
  | c, _, _, _, _, .eta Γ f A B h, hd => by
      obtain ⟨hf', hd'⟩ := hasTyT_weaken_lok D hcl (c := c) h hd
      have hp : lift (c + 1) 1 (lift 0 1 f) = lift 0 1 (lift c 1 f) := by
        rw [lift_lift_permute 1 1 c 0 (by omega), show 1 + c = c + 1 from by omega]
      have hb : lift c 1 (Expr.lam A (Expr.app (lift 0 1 f) (Expr.bvar 0))) =
          Expr.lam (lift c 1 A) (Expr.app (lift 0 1 (lift c 1 f)) (Expr.bvar 0)) := by
        simp only [lift, hp, show (if c + 1 ≤ 0 then Expr.bvar (0 + 1) else Expr.bvar 0) = Expr.bvar 0 from by simp]
      exact ex_convT_lok_cast rfl hb.symm rfl rfl
        ⟨.eta (insertAt D c Γ) (lift c 1 f) (lift c 1 A) (lift (c + 1) 1 B) hf',
         by simp only [LOKc]; exact hd'⟩
  | c, _, _, _, _, .irr Γ P p q hP hp hq, ⟨hdP, hdp, hdq⟩ => by
      obtain ⟨hP', hdP'⟩ := hasTyT_weaken_lok D hcl (c := c) hP hdP
      obtain ⟨hp', hdp'⟩ := hasTyT_weaken_lok D hcl (c := c) hp hdp
      obtain ⟨hq', hdq'⟩ := hasTyT_weaken_lok D hcl (c := c) hq hdq
      exact ⟨.irr _ _ _ _ hP' hp' hq', by simp only [LOKc]; exact ⟨hdP', hdp', hdq'⟩⟩
  | c, _, _, _, _, .tyConv Γ a b A A' u h hA, ⟨hd, hdA⟩ => by
      obtain ⟨h', hd'⟩ := convT_weaken_lok D hcl (c := c) h hd
      obtain ⟨hA', hdA'⟩ := convT_weaken_lok D hcl (c := c) hA hdA
      exact ⟨.tyConv _ _ _ _ _ u h' hA', by simp only [LOKc]; exact ⟨hd', hdA'⟩⟩
end

theorem tyConvT_weaken_lok (D : LocalDecl) {E : ResolvedEnv} {n : Nat} {σ : Nat → Nat} {N : Nat}
    {K : Nat → Nat} (hcl : EnvClosed E) :
    {c : Nat} → {Γ : LCtx} → {A B : Expr Nat} → (d : TyConvT E n Γ A B) →
      LOKtc σ N K d →
      ∃ d' : TyConvT E n (insertAt D c Γ) (lift c 1 A) (lift c 1 B), LOKtc σ N K d'
  | c, Γ, A, _, .refl _ _, _ => ⟨.refl (insertAt D c Γ) (lift c 1 A), by simp only [LOKtc]⟩
  | c, _, _, _, .of _ A B u d, hdc => by
      simp only [LOKtc] at hdc
      obtain ⟨d', hdc'⟩ := convT_weaken_lok D hcl (c := c) d hdc
      exact ⟨.of _ _ _ u d', by simp only [LOKtc]; exact hdc'⟩
  | c, _, _, _, .trans _ A B C c₁ c₂, hdc => by
      simp only [LOKtc] at hdc
      obtain ⟨c₁', hd1'⟩ := tyConvT_weaken_lok D hcl (c := c) c₁ hdc.1
      obtain ⟨c₂', hd2'⟩ := tyConvT_weaken_lok D hcl (c := c) c₂ hdc.2
      exact ⟨.trans _ _ _ _ c₁' c₂', by simp only [LOKtc]; exact ⟨hd1', hd2'⟩⟩

/-- `EnvClosedA E` implies `EnvClosed (eraseEnv E)`. -/
theorem envClosed_eraseEnv {E : ResolvedEnvA} (hE : EnvClosedA E) : EnvClosed (eraseEnv E) := by
  intro r m hm
  obtain ⟨mA, hmA, rfl⟩ := members_of_eraseEnv hm
  obtain ⟨hclT, hclB⟩ := hE r mA hmA
  refine ⟨fun k => ?_, fun b hb k => ?_⟩
  · show lift k 1 (erase mA.mtypeA) = erase mA.mtypeA
    rw [← erase_liftA, hclT k]
  · cases hbA : mA.bodyA with
    | none =>
        have : (eraseMember mA).body = none := by show mA.bodyA.map erase = none; rw [hbA]; rfl
        rw [this] at hb; exact Option.noConfusion hb
    | some bA =>
        have : (eraseMember mA).body = some (erase bA) := by
          show mA.bodyA.map erase = some (erase bA); rw [hbA]; rfl
        rw [this] at hb
        obtain rfl := Option.some.inj hb
        rw [← erase_liftA, hclB bA hbA k]

theorem eraseDecl_liftDeclA (c : Nat) :
    (d : LocalDeclA) → eraseDecl (liftDeclA c d) = liftDecl c (eraseDecl d)
  | .assumption A => by simp only [liftDeclA, eraseDecl, liftDecl, erase_liftA]
  | .letBinding A v => by simp only [liftDeclA, eraseDecl, liftDecl, erase_liftA]

theorem eraseCtx_insertAtA (d : LocalDeclA) :
    (c : Nat) → (Γ : LCtxA) → eraseCtx (insertAtA d c Γ) = insertAt (eraseDecl d) c (eraseCtx Γ)
  | 0, Γ => rfl
  | c + 1, [] => rfl
  | c + 1, x :: Γ => by
      show eraseDecl (liftDeclA c x) :: eraseCtx (insertAtA d c Γ) =
        liftDecl c (eraseDecl x) :: insertAt (eraseDecl d) c (eraseCtx Γ)
      rw [eraseDecl_liftDeclA, eraseCtx_insertAtA d c Γ]

section BaseAL

/-- `LOK`-carrying typing on the copy (`I = noIotaA`): unweighted copy typing paired with an
    `LOKt σ N K`-bounded typing on `eraseEnv E`. -/
def HasTyAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (Γ : LCtxA) (e A : ExprA) : Prop :=
  Nonempty (HasTyA E noIotaA n Γ e A) ∧
    ∃ d : HasTyT (eraseEnv E) n (eraseCtx Γ) (erase e) (erase A), LOKt σ N K d

/-- `LOK`-carrying conversion on the copy (`I = noIotaA`). -/
def ConvAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (Γ : LCtxA) (a b A : ExprA) : Prop :=
  Nonempty (ConvA E noIotaA n Γ a b A) ∧
    ∃ d : ConvT (eraseEnv E) n (eraseCtx Γ) (erase a) (erase b) (erase A), LOKc σ N K d

/-- `LOK`-carrying type-conversion chain on the copy (`I = noIotaA`). -/
def TyConvAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (Γ : LCtxA) (A B : ExprA) : Prop :=
  Nonempty (TyConvA E noIotaA n Γ A B) ∧
    ∃ d : TyConvT (eraseEnv E) n (eraseCtx Γ) (erase A) (erase B), LOKtc σ N K d

/-- `LOK`-carrying weak-head type reduction (`WhTyA` paired with `TyConvAL`). -/
def WhTyAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (Γ : LCtxA) (A B : ExprA) : Prop :=
  WhTyA E noIotaA n Γ A B ∧ TyConvAL E n σ N K Γ A B

/-- `LOK`-carrying typed weak-head term step (`StepAtA` paired with `HasTyAL` and `ConvAL`). -/
def StepAtAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (Γ : LCtxA) (a a' A : ExprA) : Prop :=
  StepAtA E noIotaA n Γ a a' A ∧ HasTyAL E n σ N K Γ a A ∧ ConvAL E n σ N K Γ a a' A

/-- `LOK`-carrying two-sided parallel conversion along two Π-telescopes (`ParConvA` with `ConvAL` and `TyConvAL`). -/
inductive ParConvAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (Γ : LCtxA) : ExprA → ExprA → List ExprA → List ExprA → Prop where
  | nil (T T' : ExprA) : ParConvAL E n σ N K Γ T T' [] []
  | cons (A : ExprA) (u : Level) (B : ExprA) (v : Level) (A' : ExprA) (u' : Level) (B' : ExprA)
      (v' : Level) (f f' : ExprA) (fs fs' : List ExprA) :
      ConvAL E n σ N K Γ f f' A →
      TyConvAL E n σ N K Γ A A' →
      ParConvAL E n σ N K Γ (instantiate0A f B) (instantiate0A f' B') fs fs' →
      ParConvAL E n σ N K Γ (.pi A u B v) (.pi A' u' B' v') (f :: fs) (f' :: fs')

variable {E : ResolvedEnvA} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}

theorem convAL_refl {Γ : LCtxA} {a A : ExprA} (h : HasTyAL E n σ N K Γ a A) :
    ConvAL E n σ N K Γ a a A :=
  ⟨h.1.elim fun t => ⟨.refl Γ a A t⟩, h.2.elim fun d hd => ⟨.refl _ _ _ d, hd⟩⟩

theorem convAL_symm {Γ : LCtxA} {a b A : ExprA} (h : ConvAL E n σ N K Γ a b A) :
    ConvAL E n σ N K Γ b a A :=
  ⟨h.1.elim fun c => ⟨.symm Γ a b A c⟩, h.2.elim fun d hd => ⟨.symm _ _ _ _ d, hd⟩⟩

theorem convAL_trans {Γ : LCtxA} {a b c A : ExprA}
    (h1 : ConvAL E n σ N K Γ a b A) (h2 : ConvAL E n σ N K Γ b c A) :
    ConvAL E n σ N K Γ a c A :=
  ⟨h1.1.elim fun c1 => h2.1.elim fun c2 => ⟨.trans Γ a b c A c1 c2⟩,
   h1.2.elim fun d1 hd1 => h2.2.elim fun d2 hd2 => ⟨.trans _ _ _ _ _ d1 d2, hd1, hd2⟩⟩

theorem tyConvAL_refl (Γ : LCtxA) (A : ExprA) : TyConvAL E n σ N K Γ A A :=
  ⟨⟨.refl Γ A⟩, ⟨.refl _ _, by simp only [LOKtc]⟩⟩

theorem tyConvAL_symm {Γ : LCtxA} {A B : ExprA} (h : TyConvAL E n σ N K Γ A B) :
    TyConvAL E n σ N K Γ B A :=
  ⟨h.1.elim fun c => ⟨c.symm⟩, h.2.elim fun d hd => ⟨d.symmT, LOKtc_symmT σ N K d hd⟩⟩

theorem tyConvAL_trans {Γ : LCtxA} {A B C : ExprA}
    (h1 : TyConvAL E n σ N K Γ A B) (h2 : TyConvAL E n σ N K Γ B C) :
    TyConvAL E n σ N K Γ A C :=
  ⟨h1.1.elim fun c1 => h2.1.elim fun c2 => ⟨.trans Γ A B C c1 c2⟩,
   h1.2.elim fun d1 hd1 => h2.2.elim fun d2 hd2 => ⟨.trans _ _ _ _ d1 d2, by simp only [LOKtc]; exact ⟨hd1, hd2⟩⟩⟩

theorem tyConvAL_of_convAL {Γ : LCtxA} {A B : ExprA} {l l' u : Level}
    (hAl : Nonempty (HasTyA E noIotaA n Γ A (.sort l))) (hlu : eqN l u)
    (hBl : Nonempty (HasTyA E noIotaA n Γ B (.sort l'))) (hl'u : eqN l' u)
    (hc : ConvAL E n σ N K Γ A B (.sort u)) :
    TyConvAL E n σ N K Γ A B :=
  ⟨hAl.elim fun tA => hBl.elim fun tB => hc.1.elim fun c => ⟨.of Γ A B l l' u tA hlu tB hl'u c⟩,
   hc.2.elim fun d hd => ⟨.of _ _ _ u d, by simpa only [LOKtc] using hd⟩⟩

/-- Transport `HasTyAL` along `TyConvAL` with ZERO `.sorts` steps. -/
theorem hasTyAL_of_tyConvAL {Γ : LCtxA} {e A B : ExprA}
    (h : HasTyAL E n σ N K Γ e A) (hc : TyConvAL E n σ N K Γ A B) :
    HasTyAL E n σ N K Γ e B :=
  ⟨h.1.elim fun t => hc.1.elim fun c => ⟨hasTyA_of_tyConvA t c⟩,
   h.2.elim fun d hd => hc.2.elim fun c hdc => ⟨hasTyT_of_tyConv d c, LOKt_of_tyConv σ N K d c hd hdc⟩⟩

/-- Transport `ConvAL` along `TyConvAL` with ZERO `.sorts` steps. -/
theorem convAL_of_tyConvAL {Γ : LCtxA} {a b A B : ExprA}
    (h : ConvAL E n σ N K Γ a b A) (hc : TyConvAL E n σ N K Γ A B) :
    ConvAL E n σ N K Γ a b B :=
  ⟨h.1.elim fun t => hc.1.elim fun c => ⟨convA_of_tyConvA t c⟩,
   h.2.elim fun d hd => hc.2.elim fun c hdc => ⟨convT_of_tyConv d c, LOKc_of_tyConv σ N K d c hd hdc⟩⟩

/-- Reflexive `WhTyAL` requires only unweighted `HasTyA` because `TyConvT.refl` has `LOKtc = True`. -/
theorem whTyAL_of_hasTy {Γ : LCtxA} {A : ExprA} {u : Level}
    (hA : Nonempty (HasTyA E noIotaA n Γ A (.sort u))) :
    WhTyAL E n σ N K Γ A A :=
  ⟨hA.elim fun t => whTyA_of_hasTy t, tyConvAL_refl Γ A⟩

theorem whTyAL_headRefl {Γ : LCtxA} {A N₀ : ExprA} (h : WhTyAL E n σ N K Γ A N₀) :
    WhTyAL E n σ N K Γ A A :=
  ⟨whTyA_headRefl h.1, tyConvAL_refl Γ A⟩

theorem whTyAL_endRefl {Γ : LCtxA} {A N₀ : ExprA} (h : WhTyAL E n σ N K Γ A N₀) :
    WhTyAL E n σ N K Γ N₀ N₀ :=
  ⟨(whTyA_hasTy_end h.1).elim fun _ t => t.elim fun t => whTyA_of_hasTy t, tyConvAL_refl Γ N₀⟩

theorem whTyAL_step_left {Γ : LCtxA} {A A' B : ExprA} {u : Level}
    (hstep : StepAtAL E n σ N K Γ A A' (.sort u))
    (hA' : Nonempty (HasTyA E noIotaA n Γ A' (.sort u)))
    (hwh : WhTyAL E n σ N K Γ A' B) :
    WhTyAL E n σ N K Γ A B :=
  ⟨hstep.2.1.1.elim fun t => hstep.1.2.elim fun s => whTyA_cons t s hwh.1,
   tyConvAL_trans (tyConvAL_of_convAL hstep.2.1.1 (eqNA_refl u) hA' (eqNA_refl u) hstep.2.2) hwh.2⟩

theorem tyConvAL_nf {Γ : LCtxA} {A B N₀ N₀' : ExprA}
    (hA : WhTyAL E n σ N K Γ A N₀) (hB : WhTyAL E n σ N K Γ B N₀')
    (hc : TyConvAL E n σ N K Γ A B) :
    TyConvAL E n σ N K Γ N₀ N₀' :=
  tyConvAL_trans (tyConvAL_symm hA.2) (tyConvAL_trans hc hB.2)

theorem parConvAL_symm {Γ : LCtxA} {T T' : ExprA} {fs fs' : List ExprA} :
    ParConvAL E n σ N K Γ T T' fs fs' → ParConvAL E n σ N K Γ T' T fs' fs
  | .nil T T' => .nil T' T
  | .cons A u B v A' u' B' v' f f' fs fs' hc hd hs =>
      .cons A' u' B' v' A u B v f' f fs' fs
        (convAL_of_tyConvAL (convAL_symm hc) hd)
        (tyConvAL_symm hd) (parConvAL_symm hs)

theorem parConvAL_trans {Γ : LCtxA} {T T' T'' : ExprA} {fs fs' fs'' : List ExprA} :
    ParConvAL E n σ N K Γ T T' fs fs' →
    ParConvAL E n σ N K Γ T' T'' fs' fs'' →
    ParConvAL E n σ N K Γ T T'' fs fs''
  | .nil T _, .nil _ T'' => .nil T T''
  | .cons A u B v A' u' B' v' f f' fs fs' hc hd hs,
    .cons _ _ _ _ A'' u'' B'' v'' _ f'' _ fs'' hc' hd' hs' =>
      .cons A u B v A'' u'' B'' v'' f f'' fs fs''
        (convAL_trans hc (convAL_of_tyConvAL hc' (tyConvAL_symm hd)))
        (tyConvAL_trans hd hd') (parConvAL_trans hs hs')

/-- Single-insertion weakening (`insertAtA`) for `HasTyAL`. -/
theorem hasTyAL_weaken (hE : EnvClosedA E) (d : LocalDeclA) {c : Nat} {Γ : LCtxA}
    (hc : c ≤ Γ.length) {e A : ExprA} (h : HasTyAL E n σ N K Γ e A) :
    HasTyAL E n σ N K (insertAtA d c Γ) (liftA c 1 e) (liftA c 1 A) := by
  refine ⟨h.1.elim fun t => ⟨hasTyWeakenA hE noIotaA_lift d hc t⟩, ?_⟩
  obtain ⟨dt, hdt⟩ := h.2
  exact ex_hasTyT_lok_cast (eraseCtx_insertAtA d c Γ).symm (erase_liftA e c 1).symm (erase_liftA A c 1).symm
    (hasTyT_weaken_lok (eraseDecl d) (envClosed_eraseEnv hE) (c := c) dt hdt)

/-- Single-insertion weakening (`insertAtA`) for `ConvAL`. -/
theorem convAL_weaken (hE : EnvClosedA E) (d : LocalDeclA) {c : Nat} {Γ : LCtxA}
    (hc : c ≤ Γ.length) {a b A : ExprA} (h : ConvAL E n σ N K Γ a b A) :
    ConvAL E n σ N K (insertAtA d c Γ) (liftA c 1 a) (liftA c 1 b) (liftA c 1 A) := by
  refine ⟨h.1.elim fun cv => ⟨convWeakenA hE noIotaA_lift d hc cv⟩, ?_⟩
  obtain ⟨dc, hdc⟩ := h.2
  exact ex_convT_lok_cast (eraseCtx_insertAtA d c Γ).symm
    (erase_liftA a c 1).symm (erase_liftA b c 1).symm (erase_liftA A c 1).symm
    (convT_weaken_lok (eraseDecl d) (envClosed_eraseEnv hE) (c := c) dc hdc)

/-- Single-insertion weakening (`insertAtA`) for `TyConvAL`. -/
theorem tyConvAL_weaken (hE : EnvClosedA E) (d : LocalDeclA) {c : Nat} {Γ : LCtxA}
    (hc : c ≤ Γ.length) {A B : ExprA} (h : TyConvAL E n σ N K Γ A B) :
    TyConvAL E n σ N K (insertAtA d c Γ) (liftA c 1 A) (liftA c 1 B) := by
  refine ⟨h.1.elim fun cv => ⟨tyConvA_weaken hE noIotaA_lift d hc cv⟩, ?_⟩
  obtain ⟨dc, hdc⟩ := h.2
  exact ex_tyConvT_lok_cast (eraseCtx_insertAtA d c Γ).symm (erase_liftA A c 1).symm (erase_liftA B c 1).symm
    (tyConvT_weaken_lok (eraseDecl d) (envClosed_eraseEnv hE) (c := c) dc hdc)

/-- World weakening (`WkSpecA`) for `HasTyAL`. -/
theorem hasTyAL_wk (hE : EnvClosedA E) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {e A : ExprA} →
      HasTyAL E n σ N K Γ e A →
      HasTyAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ e) (wkExprA ρ A)
  | _, [], _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, h =>
      hasTyAL_wk hE (insertAtA d c Γ) ρ hρ (hasTyAL_weaken hE d hc h)

/-- World weakening (`WkSpecA`) for `ConvAL`. -/
theorem convAL_wk (hE : EnvClosedA E) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {a b A : ExprA} →
      ConvAL E n σ N K Γ a b A →
      ConvAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) (wkExprA ρ A)
  | _, [], _, _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, _, h =>
      convAL_wk hE (insertAtA d c Γ) ρ hρ (convAL_weaken hE d hc h)

/-- World weakening (`WkSpecA`) for `TyConvAL`. -/
theorem tyConvAL_wk (hE : EnvClosedA E) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {A B : ExprA} →
      TyConvAL E n σ N K Γ A B →
      TyConvAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ A) (wkExprA ρ B)
  | _, [], _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, h =>
      tyConvAL_wk hE (insertAtA d c Γ) ρ hρ (tyConvAL_weaken hE d hc h)

/-- World weakening (`WkSpecA`) for `WhTyAL`. -/
theorem whTyAL_wk (hE : EnvClosedA E) (Γ : LCtxA) (ρ : WkSpecA)
    (hρ : WkSpecA.ok ρ Γ) {A B : ExprA} (h : WhTyAL E n σ N K Γ A B) :
    WhTyAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ A) (wkExprA ρ B) :=
  ⟨whTyA_wk hE noIotaA_lift Γ ρ hρ h.1, tyConvAL_wk hE Γ ρ hρ h.2⟩

/-- World weakening (`WkSpecA`) for `StepAtAL`. -/
theorem stepAtAL_wk (hE : EnvClosedA E) (Γ : LCtxA) (ρ : WkSpecA)
    (hρ : WkSpecA.ok ρ Γ) {a a' A : ExprA} (h : StepAtAL E n σ N K Γ a a' A) :
    StepAtAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ a') (wkExprA ρ A) :=
  ⟨⟨hasTyA_wk_ne hE noIotaA_lift ρ hρ h.1.1, h.1.2.elim fun s => ⟨tyHRedA_wk hE noIotaA_lift Γ ρ hρ s⟩⟩,
   hasTyAL_wk hE Γ ρ hρ h.2.1, convAL_wk hE Γ ρ hρ h.2.2⟩

/-- World weakening (`WkSpecA`) for `ParConvAL`. -/
theorem parConvAL_wk (hE : EnvClosedA E) {Γ : LCtxA} (ρ : WkSpecA) (hρ : WkSpecA.ok ρ Γ) :
    ∀ {T T' : ExprA} {xs ys : List ExprA},
      ParConvAL E n σ N K Γ T T' xs ys →
      ParConvAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ T) (wkExprA ρ T') (xs.map (wkExprA ρ)) (ys.map (wkExprA ρ))
  | _, _, _, _, .nil _ _ => .nil _ _
  | _, _, _, _, .cons A u B v A' u' B' v' f f' fs fs' hc hd hs => by
      rw [wkExprA_pi_ub, wkExprA_pi_ub, List.map_cons, List.map_cons]
      refine .cons _ u _ v _ u' _ v' _ _ _ _
        (convAL_wk hE Γ ρ hρ hc) (tyConvAL_wk hE Γ ρ hρ hd) ?_
      rw [← wkExprA_instantiate0A, ← wkExprA_instantiate0A]
      exact parConvAL_wk hE ρ hρ hs

end BaseAL

/-! ## §2 `PropEqAL` — `LOK`-carrying propositional type structure (`pi`, `fam`, `stuck`) -/

section PropEqAL

/-- `PropEqA` (`RcicAnnPropEq.lean`) with `WhTyAL`, `ParConvAL`, and `TyConvAL`. -/
inductive PropEqAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    LCtxA → ExprA → ExprA → Prop where
  | pi {Γ : LCtxA} {a b D C D' C' : ExprA} {u v u' v' : Level}
      (ha : WhTyAL E n σ N K Γ a (.pi D u C v))
      (hb : WhTyAL E n σ N K Γ b (.pi D' u' C' v'))
      (hu : eqN u u') (hv : eqN v v')
      (hDty : Nonempty (HasTyA E noIotaA n Γ D (.sort u)))
      (hD'ty : Nonempty (HasTyA E noIotaA n Γ D' (.sort u')))
      (hD : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
        TyConvAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
      (hC : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ D₀ : ExprA,
        Nonempty (CtxWfA E noIotaA n (.assumption D₀ :: wkCtxA ρ Γ)) →
        TyConvAL E n σ N K (wkCtxA ρ Γ) D₀ (wkExprA ρ D) →
        PropEqAL E n σ N K (.assumption D₀ :: wkCtxA ρ Γ)
          (wkExprA (WkSpecA.ub ρ) C) (wkExprA (WkSpecA.ub ρ) C'))
      (hc : TyConvAL E n σ N K Γ a b) : PropEqAL E n σ N K Γ a b
  | fam {Γ : LCtxA} {a b : ExprA} {r : Nat} {ls ls' : List Level} {xs xs' : List ExprA}
      {m : CheckedMemberA}
      (ha : WhTyAL E n σ N K Γ a (foldAppsA (.const r ls) xs))
      (hb : WhTyAL E n σ N K Γ b (foldAppsA (.const r ls') xs'))
      (hna : hStepFnA E noIotaA.fn Γ (foldAppsA (.const r ls) xs) = none)
      (hnb : hStepFnA E noIotaA.fn Γ (foldAppsA (.const r ls') xs') = none)
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM) (hls : eqNList ls ls')
      (hargs : ∀ lsX : List Level, eqNListB n ls lsX →
        ParConvAL E n σ N K Γ (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA) xs xs')
      (hc : TyConvAL E n σ N K Γ a b) : PropEqAL E n σ N K Γ a b
  | stuck {Γ : LCtxA} {a b N₀ N₀' : ExprA}
      (ha : WhTyAL E n σ N K Γ a N₀) (hb : WhTyAL E n σ N K Γ b N₀')
      (hN : StuckA E noIotaA Γ N₀) (hN' : StuckA E noIotaA Γ N₀')
      (hc : TyConvAL E n σ N K Γ a b) : PropEqAL E n σ N K Γ a b

variable {E : ResolvedEnvA} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}

theorem propEqAL_tyConv {Γ : LCtxA} {a b : ExprA} :
    PropEqAL E n σ N K Γ a b → TyConvAL E n σ N K Γ a b
  | .pi _ _ _ _ _ _ _ _ hc => hc
  | .fam _ _ _ _ _ _ _ _ hc => hc
  | .stuck _ _ _ _ hc => hc

theorem propEqAL_stuck_refl {Γ : LCtxA} {a b : ExprA} {l : Level}
    (ha : Nonempty (HasTyA E noIotaA n Γ a (.sort l)))
    (hb : Nonempty (HasTyA E noIotaA n Γ b (.sort l)))
    (hna : StuckA E noIotaA Γ a) (hnb : StuckA E noIotaA Γ b)
    (hab : ConvAL E n σ N K Γ a b (.sort l)) :
    PropEqAL E n σ N K Γ a b :=
  .stuck (whTyAL_of_hasTy ha) (whTyAL_of_hasTy hb) hna hnb
    (tyConvAL_of_convAL ha (eqNA_refl l) hb (eqNA_refl l) hab)

theorem propEqAL_symm {Γ : LCtxA} {a b : ExprA}
    (h : PropEqAL E n σ N K Γ a b) : PropEqAL E n σ N K Γ b a := by
  induction h with
  | pi ha hb hu hv hDty hD'ty hD _ hc ih =>
      refine .pi hb ha (eqNA_symm hu) (eqNA_symm hv) hD'ty hDty
        (fun ρ hρ => tyConvAL_symm (hD ρ hρ))
        (fun ρ hρ D₀ hctx hD₀ => ih ρ hρ D₀ hctx (tyConvAL_trans hD₀ (tyConvAL_symm (hD ρ hρ))))
        (tyConvAL_symm hc)
  | fam ha hb hna hnb hm hind hls hargs hc =>
      exact .fam hb ha hnb hna hm hind (eqNListA_symm hls)
        (fun lsX h => parConvAL_symm (hargs lsX ⟨eqNListA_trans hls h.1, h.2⟩))
        (tyConvAL_symm hc)
  | stuck ha hb hN hN' hc => exact .stuck hb ha hN' hN (tyConvAL_symm hc)

theorem propEqAL_trans {Γ : LCtxA} {a b c : ExprA}
    (h₁ : PropEqAL E n σ N K Γ a b) (h₂ : PropEqAL E n σ N K Γ b c) : PropEqAL E n σ N K Γ a c := by
  induction h₁ generalizing c with
  | @pi Γ a b D C D' C' u v u' v' ha hb hu hv hDty hD'ty hD _ hc ih =>
      cases h₂ with
      | pi hb₂ hc₂ hu₂ hv₂ _ hD'ty₂ hD₂ hC₂ hc₂' =>
          have e := whTyA_det hb.1 hb₂.1 (hStepFnA_pi E noIotaA.fn Γ D' u' C' v') (hStepFnA_pi E noIotaA.fn Γ _ _ _ _)
          injection e with e1 e2 e3 e4
          subst e1 e2 e3 e4
          refine .pi ha hc₂ (eqNA_trans hu hu₂) (eqNA_trans hv hv₂) hDty hD'ty₂
            (fun ρ hρ => tyConvAL_trans (hD ρ hρ) (hD₂ ρ hρ))
            (fun ρ hρ D₀ hctx hD₀ => ih ρ hρ D₀ hctx hD₀ (hC₂ ρ hρ D₀ hctx (tyConvAL_trans hD₀ (hD ρ hρ))))
            (tyConvAL_trans hc hc₂')
      | fam hb₂ _ hnb₂ _ _ _ _ _ _ =>
          exact absurd (whTyA_det hb.1 hb₂.1 (hStepFnA_pi E noIotaA.fn Γ D' u' C' v') hnb₂).symm
            (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | stuck hb₂ _ hN₂ _ _ =>
          have e := whTyA_det hb.1 hb₂.1 (hStepFnA_pi E noIotaA.fn Γ D' u' C' v') hN₂.1
          subst e
          exact (stuckA_not_pi hN₂).elim
  | @fam Γ a b r ls ls' xs xs' m ha hb hna hnb hm hind hls hargs hc =>
      cases h₂ with
      | pi hb₂ _ _ _ _ _ _ _ _ =>
          exact absurd (whTyA_det hb.1 hb₂.1 hnb (hStepFnA_pi E noIotaA.fn Γ _ _ _ _))
            (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
      | fam hb₂ hc₂ hnb₂ hnc₂ hm₂ _ hls₂ hargs₂ hc₂' =>
          obtain ⟨e1, e2, e3⟩ := foldAppsA_const_inj (whTyA_det hb.1 hb₂.1 hnb hnb₂)
          subst e1 e2 e3
          rw [hm] at hm₂
          injection hm₂ with e4
          subst e4
          exact .fam ha hc₂ hna hnc₂ hm hind (eqNListA_trans hls hls₂)
            (fun lsX h => parConvAL_trans (hargs lsX h)
              (hargs₂ lsX ⟨eqNListA_trans (eqNListA_symm hls) h.1, h.2⟩))
            (tyConvAL_trans hc hc₂')
      | stuck hb₂ _ hN₂ _ _ =>
          have e := whTyA_det hb.1 hb₂.1 hnb hN₂.1
          rw [← e] at hN₂
          exact (stuckA_not_famApp hN₂ hm hind).elim
  | stuck ha hb hN hN' hc =>
      cases h₂ with
      | pi hb₂ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hb.1 hb₂.1 hN'.1 (hStepFnA_pi E noIotaA.fn _ _ _ _ _)
          subst e
          exact (stuckA_not_pi hN').elim
      | fam hb₂ _ hnb₂ _ hm₂ hind₂ _ _ _ =>
          have e := whTyA_det hb.1 hb₂.1 hN'.1 hnb₂
          subst e
          exact (stuckA_not_famApp hN' hm₂ hind₂).elim
      | stuck hb₂ hc₂ hN₂ hN₂' hc₂' =>
          exact .stuck ha hc₂ hN hN₂' (tyConvAL_trans hc hc₂')

theorem propEqAL_wk (hE : EnvClosedA E) {Γ : LCtxA} {a b : ExprA}
    (h : PropEqAL E n σ N K Γ a b) (ρ : WkSpecA) (hρ : WkOkA E noIotaA n ρ Γ) :
    PropEqAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) := by
  cases h with
  | pi ha hb hu hv hDty hD'ty hD hC hc =>
      have ha' := whTyAL_wk hE Γ ρ hρ.1 ha
      have hb' := whTyAL_wk hE Γ ρ hρ.1 hb
      rw [wkExprA_pi_ub] at ha' hb'
      have hDty' := hasTyA_wk_ne hE noIotaA_lift ρ hρ.1 hDty
      have hD'ty' := hasTyA_wk_ne hE noIotaA_lift ρ hρ.1 hD'ty
      rw [wkExprA_sort] at hDty' hD'ty'
      refine .pi ha' hb' hu hv hDty' hD'ty' (fun ρ' hρ' => ?_)
        (fun ρ' hρ' D₀ hctx hD₀ => ?_) (tyConvAL_wk hE Γ ρ hρ.1 hc)
      · have hD' := hD (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ')
        rw [wkCtxA_comp, wkExprA_comp, wkExprA_comp] at hD'
        exact hD'
      · have hC' := hC (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ') D₀ (by rw [wkCtxA_comp]; exact hctx)
          (by rw [wkCtxA_comp, wkExprA_comp]; exact hD₀)
        rw [wkCtxA_comp, WkSpecA.ub_comp, wkExprA_comp, wkExprA_comp] at hC'
        exact hC'
  | @fam _ _ _ r ls ls' xs xs' m ha hb hna hnb hm hind hls hargs hc =>
      have ha' := whTyAL_wk hE Γ ρ hρ.1 ha
      have hb' := whTyAL_wk hE Γ ρ hρ.1 hb
      have hna' := hStepFnA_wk_none hE noIotaA_lift Γ ρ hρ.1 hna
      have hnb' := hStepFnA_wk_none hE noIotaA_lift Γ ρ hρ.1 hnb
      rw [wkExprA_foldAppsA, wkExprA_const] at ha' hb' hna' hnb'
      refine .fam ha' hb' hna' hnb' hm hind hls (fun lsX h => ?_) (tyConvAL_wk hE Γ ρ hρ.1 hc)
      have hargs' := parConvAL_wk hE ρ hρ.1 (hargs lsX h)
      rw [wkExprA_closed (liftA_instantiateLevelsA_closed (hE r m hm).1 lsX) ρ] at hargs'
      exact hargs'
  | stuck ha hb hN hN' hc =>
      exact .stuck (whTyAL_wk hE Γ ρ hρ.1 ha) (whTyAL_wk hE Γ ρ hρ.1 hb)
        (stuckA_wk hE noIotaA_lift Γ ρ hρ.1 hN) (stuckA_wk hE noIotaA_lift Γ ρ hρ.1 hN')
        (tyConvAL_wk hE Γ ρ hρ.1 hc)

theorem propEqAL_expand_left {Γ : LCtxA} {a a' b : ExprA} {l : Level}
    (hstep : StepAtAL E n σ N K Γ a a' (.sort l))
    (ha' : Nonempty (HasTyA E noIotaA n Γ a' (.sort l)))
    (h : PropEqAL E n σ N K Γ a' b) :
    PropEqAL E n σ N K Γ a b := by
  have hc₀ : TyConvAL E n σ N K Γ a a' :=
    tyConvAL_of_convAL hstep.2.1.1 (eqNA_refl l) ha' (eqNA_refl l) hstep.2.2
  cases h with
  | pi ha hb hu hv hDty hD'ty hD hC hc =>
      exact .pi (whTyAL_step_left hstep ha' ha) hb hu hv hDty hD'ty hD hC (tyConvAL_trans hc₀ hc)
  | fam ha hb hna hnb hm hind hls hargs hc =>
      exact .fam (whTyAL_step_left hstep ha' ha) hb hna hnb hm hind hls hargs (tyConvAL_trans hc₀ hc)
  | stuck ha hb hN hN' hc =>
      exact .stuck (whTyAL_step_left hstep ha' ha) hb hN hN' (tyConvAL_trans hc₀ hc)

theorem propEqAL_expand_right {Γ : LCtxA} {a b b' : ExprA} {l : Level}
    (hstep : StepAtAL E n σ N K Γ b b' (.sort l))
    (hb' : Nonempty (HasTyA E noIotaA n Γ b' (.sort l)))
    (h : PropEqAL E n σ N K Γ a b') :
    PropEqAL E n σ N K Γ a b := by
  have hc₀ : TyConvAL E n σ N K Γ b' b :=
    tyConvAL_symm (tyConvAL_of_convAL hstep.2.1.1 (eqNA_refl l) hb' (eqNA_refl l) hstep.2.2)
  cases h with
  | pi ha hb hu hv hDty hD'ty hD hC hc =>
      exact .pi ha (whTyAL_step_left hstep hb' hb) hu hv hDty hD'ty hD hC (tyConvAL_trans hc hc₀)
  | fam ha hb hna hnb hm hind hls hargs hc =>
      exact .fam ha (whTyAL_step_left hstep hb' hb) hna hnb hm hind hls hargs (tyConvAL_trans hc hc₀)
  | stuck ha hb hN hN' hc =>
      exact .stuck ha (whTyAL_step_left hstep hb' hb) hN hN' (tyConvAL_trans hc hc₀)

theorem propEqAL_pi_inv {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    {D' : ExprA} {u' : Level} {C' : ExprA} {v' : Level} (hΓ : Nonempty (CtxWfA E noIotaA n Γ))
    (h : PropEqAL E n σ N K Γ (.pi D u C v) (.pi D' u' C' v')) :
    eqN u u' ∧ eqN v v' ∧ TyConvAL E n σ N K Γ D D' ∧
    PropEqAL E n σ N K (.assumption D :: Γ) C C' := by
  cases h with
  | pi ha hb hu hv hDty _ hD hC _ =>
      have e1 := whTyA_det ha.1 (whTyA_headRefl ha.1) (hStepFnA_pi E noIotaA.fn Γ _ _ _ _)
        (hStepFnA_pi E noIotaA.fn Γ D u C v)
      have e2 := whTyA_det hb.1 (whTyA_headRefl hb.1) (hStepFnA_pi E noIotaA.fn Γ _ _ _ _)
        (hStepFnA_pi E noIotaA.fn Γ D' u' C' v')
      injection e1 with e11 e12 e13 e14
      injection e2 with e21 e22 e23 e24
      subst e11 e12 e13 e14 e21 e22 e23 e24
      refine ⟨hu, hv, hD [] ⟨trivial, hΓ⟩, ?_⟩
      exact hC [] ⟨trivial, hΓ⟩ _ (hΓ.elim fun c => hDty.elim fun t => ⟨.assumption c t⟩)
        (tyConvAL_refl Γ _)
  | fam ha _ hna _ _ _ _ _ _ =>
      exact absurd (whTyA_det ha.1 (whTyA_headRefl ha.1) hna (hStepFnA_pi E noIotaA.fn Γ D u C v))
        (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck ha _ hN _ _ =>
      have e := whTyA_det ha.1 (whTyA_headRefl ha.1) hN.1 (hStepFnA_pi E noIotaA.fn Γ D u C v)
      subst e
      exact (stuckA_not_pi hN).elim

theorem propEqAL_famApp_inv {Γ : LCtxA} {r r' : Nat} {ls ls' : List Level} {xs xs' : List ExprA}
    {m : CheckedMemberA} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hn : hStepFnA E noIotaA.fn Γ (foldAppsA (.const r ls) xs) = none)
    (hn' : hStepFnA E noIotaA.fn Γ (foldAppsA (.const r' ls') xs') = none)
    (h : PropEqAL E n σ N K Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r' ls') xs')) :
    r = r' ∧ eqNList ls ls' ∧ ∀ lsX : List Level, eqNListB n ls lsX →
      ParConvAL E n σ N K Γ (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA) xs xs' := by
  cases h with
  | pi ha _ _ _ _ _ _ _ _ =>
      exact absurd (whTyA_det ha.1 (whTyA_headRefl ha.1) (hStepFnA_pi E noIotaA.fn Γ _ _ _ _) hn).symm
        (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | fam ha hb hna hnb hm₀ _ hls hargs _ =>
      obtain ⟨e1, e2, e3⟩ := foldAppsA_const_inj (whTyA_det ha.1 (whTyA_headRefl ha.1) hna hn)
      obtain ⟨e4, e5, e6⟩ := foldAppsA_const_inj (whTyA_det hb.1 (whTyA_headRefl hb.1) hnb hn')
      subst e1 e2 e3 e4 e5 e6
      rw [hm] at hm₀
      injection hm₀ with e7
      subst e7
      exact ⟨rfl, hls, hargs⟩
  | stuck ha _ hN _ _ =>
      have e := whTyA_det ha.1 (whTyA_headRefl ha.1) hN.1 hn
      rw [e] at hN
      exact (stuckA_not_famApp hN hm hind).elim

end PropEqAL

/-! ## §3 `EqKAL`, `TyKAL`, `LREqAL`, `LRTyAL`, `LRRelAL` and their metatheory -/

def PropValidAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (Γ : LCtxA) (a : ExprA) : Prop :=
  ∃ M, WhTyAL E n σ N K Γ a M ∧ TripleLikeA E noIotaA Γ M

mutual
inductive EqKAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) (LE : LowEqTA k) (LT : LowTyTA k) : LCtxA → ExprA → ExprA → Prop
  | sort {Γ : LCtxA} {A B : ExprA} {l l' : Level}
      (hA : WhTyAL E n σ N K Γ A (.sort l)) (hB : WhTyAL E n σ N K Γ B (.sort l'))
      (hk : ht ρ₀ l < k) (hl : eqN l l')
      (hc : TyConvAL E n σ N K Γ A B) : EqKAL E n σ N K ρ₀ k LE LT Γ A B
  | pi {Γ : LCtxA} {A B D C D' C' : ExprA} {u v u' v' : Level}
      (hA : WhTyAL E n σ N K Γ A (.pi D u C v)) (hB : WhTyAL E n σ N K Γ B (.pi D' u' C' v'))
      (hu : eqN u u') (hv : eqN v v')
      (hDty : Nonempty (HasTyA E noIotaA n Γ D (.sort u)))
      (hCty : Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)))
      (hD'ty : Nonempty (HasTyA E noIotaA n Γ D' (.sort u')))
      (hC'ty : Nonempty (HasTyA E noIotaA n (.assumption D' :: Γ) C' (.sort v')))
      (RD : WkSpecA → ExprA → ExprA → Prop)
      (hD : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
        TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
      (hDeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
        EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
      (hC : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
      (hc : TyConvAL E n σ N K Γ A B) : EqKAL E n σ N K ρ₀ k LE LT Γ A B
  | stuck {Γ : LCtxA} {A B M M' : ExprA}
      (hA : WhTyAL E n σ N K Γ A M) (hB : WhTyAL E n σ N K Γ B M')
      (hN : TripleLikeA E noIotaA Γ M) (hN' : TripleLikeA E noIotaA Γ M')
      (hc : TyConvAL E n σ N K Γ A B) : EqKAL E n σ N K ρ₀ k LE LT Γ A B

inductive TyKAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) (LE : LowEqTA k) (LT : LowTyTA k) :
    LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop
  | prop {Γ : LCtxA} {A A' : ExprA}
      (hA : WhTyAL E n σ N K Γ A A') (hn : hStepFnA E noIotaA.fn Γ A' = none)
      (hP : IsPropTy E noIotaA Γ A') :
      TyKAL E n σ N K ρ₀ k LE LT Γ A (fun a b =>
        HasTyAL E n σ N K Γ a A' ∧ HasTyAL E n σ N K Γ b A' ∧
        ConvAL E n σ N K Γ a b A')
  | sortT {Γ : LCtxA} {A : ExprA} {l : Level}
      (hA : WhTyAL E n σ N K Γ A (.sort l)) (hz : isZero l = false) (hk : ht ρ₀ l < k) :
      TyKAL E n σ N K ρ₀ k LE LT Γ A (fun a b =>
        LE (ht ρ₀ l) hk Γ a b ∧
        (∃ R, LT (ht ρ₀ l) hk Γ a R) ∧
        (∃ R, LT (ht ρ₀ l) hk Γ b R) ∧
        HasTyAL E n σ N K Γ a (.sort l) ∧ HasTyAL E n σ N K Γ b (.sort l) ∧
        ConvAL E n σ N K Γ a b (.sort l))
  | sortP {Γ : LCtxA} {A : ExprA} {l : Level}
      (hA : WhTyAL E n σ N K Γ A (.sort l)) (hz : isZero l = true) :
      TyKAL E n σ N K ρ₀ k LE LT Γ A (fun a b =>
        PropValidAL E n σ N K Γ a ∧ PropValidAL E n σ N K Γ b ∧
        HasTyAL E n σ N K Γ a (.sort l) ∧ HasTyAL E n σ N K Γ b (.sort l) ∧
        ConvAL E n σ N K Γ a b (.sort l) ∧ PropEqAL E n σ N K Γ a b)
  | pi {Γ : LCtxA} {A D C : ExprA} {u v : Level}
      (hA : WhTyAL E n σ N K Γ A (.pi D u C v))
      (hnp : ¬ IsPropTy E noIotaA Γ (.pi D u C v))
      (hDty : Nonempty (HasTyA E noIotaA n Γ D (.sort u)))
      (hCty : Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)))
      (RD : WkSpecA → ExprA → ExprA → Prop)
      (hD : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
        TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
      (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
      (hC : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
      (hCeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) :
      TyKAL E n σ N K ρ₀ k LE LT Γ A (fun f g =>
        (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
          RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
        HasTyAL E n σ N K Γ f (.pi D u C v) ∧ HasTyAL E n σ N K Γ g (.pi D u C v) ∧
        ConvAL E n σ N K Γ f g (.pi D u C v))
  | stuck {Γ : LCtxA} {A M : ExprA}
      (hA : WhTyAL E n σ N K Γ A M) (hN : StuckA E noIotaA Γ M) :
      TyKAL E n σ N K ρ₀ k LE LT Γ A (fun a b =>
        HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b M ∧
        ConvAL E n σ N K Γ a b M)
end

mutual
def LREqAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) : (k : Nat) → LCtxA → ExprA → ExprA → Prop
  | k => EqKAL E n σ N K ρ₀ k (fun j _ => LREqAL E n σ N K ρ₀ j) (fun j _ => LRTyAL E n σ N K ρ₀ j)
  termination_by k => k
  decreasing_by all_goals assumption

def LRTyAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) : (k : Nat) → LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop
  | k => TyKAL E n σ N K ρ₀ k (fun j _ => LREqAL E n σ N K ρ₀ j) (fun j _ => LRTyAL E n σ N K ρ₀ j)
  termination_by k => k
  decreasing_by all_goals assumption
end

theorem LREqAL_eq (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) :
    LREqAL E n σ N K ρ₀ k =
      EqKAL E n σ N K ρ₀ k (fun j _ => LREqAL E n σ N K ρ₀ j) (fun j _ => LRTyAL E n σ N K ρ₀ j) := by
  rw [LREqAL]

theorem LRTyAL_eq (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) :
    LRTyAL E n σ N K ρ₀ k =
      TyKAL E n σ N K ρ₀ k (fun j _ => LREqAL E n σ N K ρ₀ j) (fun j _ => LRTyAL E n σ N K ρ₀ j) := by
  rw [LRTyAL]

section LRMetatheory

variable {E : ResolvedEnvA} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
  {ρ₀ : Nat → Nat} {k : Nat} {LE : LowEqTA k} {LT : LowTyTA k}

theorem TyKAL_unique :
    {Γ : LCtxA} → {A : ExprA} → {R R' : ExprA → ExprA → Prop} →
    TyKAL E n σ N K ρ₀ k LE LT Γ A R → TyKAL E n σ N K ρ₀ k LE LT Γ A R' → R = R' :=
  fun {_Γ _A _R _R'} h h' =>
  TyKAL.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ A R _ => ∀ (R' : ExprA → ExprA → Prop),
      TyKAL E n σ N K ρ₀ k LE LT Γ A R' → R = R')
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro)
    -- TyKAL.prop
    (fun hA hn hP _ h' => by
      cases h' with
      | prop hA' hn' _ =>
          have e := whTyA_det hA.1 hA'.1 hn hn'
          cases e; rfl
      | sortT hA' _ _ =>
          have e := whTyA_det hA.1 hA'.1 hn (hStepFnA_sort _ _ _ _)
          subst e
          exact absurd hP (not_isPropTy_sort _ _ _ _)
      | sortP hA' _ =>
          have e := whTyA_det hA.1 hA'.1 hn (hStepFnA_sort _ _ _ _)
          subst e
          exact absurd hP (not_isPropTy_sort _ _ _ _)
      | pi hA' hnp' _ _ _ _ _ _ _ =>
          have e := whTyA_det hA.1 hA'.1 hn (hStepFnA_pi _ _ _ _ _ _ _)
          subst e
          exact absurd hP hnp'
      | stuck hA' hN' =>
          have e := whTyA_det hA.1 hA'.1 hn hN'.1
          subst e; rfl)
    -- TyKAL.sortT
    (fun hA hz _ _ h' => by
      cases h' with
      | sortT hA' _ _ =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e; rfl
      | sortP hA' hz' =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e; rw [hz] at hz'; cases hz'
      | prop hA' hn' hP' =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) hn'
          subst e
          exact absurd hP' (not_isPropTy_sort _ _ _ _)
      | pi hA' _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
      | stuck hA' hN' =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) hN'.1
          subst e
          exact (stuckA_not_sort hN').elim)
    -- TyKAL.sortP
    (fun hA hz _ h' => by
      cases h' with
      | sortP hA' _ =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e; rfl
      | sortT hA' hz' _ =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e; rw [hz] at hz'; cases hz'
      | prop hA' hn' hP' =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) hn'
          subst e
          exact absurd hP' (not_isPropTy_sort _ _ _ _)
      | pi hA' _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
      | stuck hA' hN' =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_sort _ _ _ _) hN'.1
          subst e
          exact (stuckA_not_sort hN').elim)
    -- TyKAL.pi
    (fun hA _hnp _hDty _hCty RD hD RC hC _hCeq ihD ihC _ihCeq _ h' => by
      cases h' with
      | pi hA' _ _ _ RD' hD' RC' hC' _ =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
          funext f g
          apply propext
          constructor
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨fun ρ hρ a a' hr => ?_, h2, h3, h4⟩
            have hRD : RD ρ = RD' ρ := ihD ρ hρ _ (hD' ρ hρ)
            have hr' : RD ρ a a' := by rw [hRD]; exact hr
            have hRC : RC ρ a = RC' ρ a := ihC ρ hρ a a' hr' _ (hC' ρ hρ a a' hr)
            rw [← hRC]; exact h1 ρ hρ a a' hr'
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨fun ρ hρ a a' hr => ?_, h2, h3, h4⟩
            have hRD : RD ρ = RD' ρ := ihD ρ hρ _ (hD' ρ hρ)
            have hr' : RD' ρ a a' := by rw [← hRD]; exact hr
            have hRC : RC ρ a = RC' ρ a := ihC ρ hρ a a' hr _ (hC' ρ hρ a a' hr')
            rw [hRC]; exact h1 ρ hρ a a' hr'
      | prop hA' hn' hP' =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_pi _ _ _ _ _ _ _) hn'
          subst e
          exact absurd hP' _hnp
      | sortT hA' _ _ =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | sortP hA' _ =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | stuck hA' hN' =>
          have e := whTyA_det hA.1 hA'.1 (hStepFnA_pi _ _ _ _ _ _ _) hN'.1
          subst e
          exact (stuckA_not_pi hN').elim)
    -- TyKAL.stuck
    (fun hA hN _ h' => by
      cases h' with
      | stuck hA' hN' =>
          have e := whTyA_det hA.1 hA'.1 hN.1 hN'.1
          cases e; rfl
      | prop hA' hn' _ =>
          have e := whTyA_det hA.1 hA'.1 hN.1 hn'
          subst e; rfl
      | sortT hA' _ _ =>
          have e := whTyA_det hA.1 hA'.1 hN.1 (hStepFnA_sort _ _ _ _)
          subst e
          exact (stuckA_not_sort hN).elim
      | sortP hA' _ =>
          have e := whTyA_det hA.1 hA'.1 hN.1 (hStepFnA_sort _ _ _ _)
          subst e
          exact (stuckA_not_sort hN).elim
      | pi hA' _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hA.1 hA'.1 hN.1 (hStepFnA_pi _ _ _ _ _ _ _)
          subst e
          exact (stuckA_not_pi hN).elim)
    h _R' h'

theorem LRTyAL_unique {E : ResolvedEnvA} {n : Nat} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}
    {ρ₀ : Nat → Nat} {k : Nat} {Γ : LCtxA} {A : ExprA} {R R' : ExprA → ExprA → Prop}
    (h : LRTyAL E n σ N K ρ₀ k Γ A R) (h' : LRTyAL E n σ N K ρ₀ k Γ A R') : R = R' := by
  rw [LRTyAL_eq] at h h'
  exact TyKAL_unique (LE := fun j _ => LREqAL E n σ N K ρ₀ j) (LT := fun j _ => LRTyAL E n σ N K ρ₀ j) h h'

/-! ### §3.1 Reduction invariance & escape -/

theorem tyKAL_of_whTyAL {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyAL E n σ N K Γ A A₀) (hn₀ : hStepFnA E noIotaA.fn Γ A₀ = none)
    (h : TyKAL E n σ N K ρ₀ k LE LT Γ A R) : TyKAL E n σ N K ρ₀ k LE LT Γ A₀ R := by
  cases h with
  | prop hA hn hP =>
      have e := whTyA_det hA.1 hA₀.1 hn hn₀
      subst e
      exact .prop (whTyAL_endRefl hA) hn hP
  | sortT hA hz hk =>
      have e := whTyA_det hA.1 hA₀.1 (hStepFnA_sort _ _ _ _) hn₀
      subst e
      exact .sortT (whTyAL_endRefl hA) hz hk
  | sortP hA hz =>
      have e := whTyA_det hA.1 hA₀.1 (hStepFnA_sort _ _ _ _) hn₀
      subst e
      exact .sortP (whTyAL_endRefl hA) hz
  | pi hA hnp hDty hCty RD hD RC hC hCeq =>
      have e := whTyA_det hA.1 hA₀.1 (hStepFnA_pi _ _ _ _ _ _ _) hn₀
      subst e
      exact .pi (whTyAL_endRefl hA) hnp hDty hCty RD hD RC hC hCeq
  | stuck hA hN =>
      have e := whTyA_det hA.1 hA₀.1 hN.1 hn₀
      subst e
      exact .stuck (whTyAL_endRefl hA) hN

theorem tyKAL_of_tripleLike {Γ : LCtxA} {A M : ExprA} (hA : WhTyAL E n σ N K Γ A M)
    (h : TripleLikeA E noIotaA Γ M) :
    TyKAL E n σ N K ρ₀ k LE LT Γ A (fun a b =>
      HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b M ∧
      ConvAL E n σ N K Γ a b M) :=
  h.2.elim (fun hP => .prop hA h.1 hP) (fun hs => .stuck hA ⟨h.1, hs⟩)

theorem tyKAL_of_whTyAL' {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyAL E n σ N K Γ A A₀) (hn₀ : hStepFnA E noIotaA.fn Γ A₀ = none)
    (h : TyKAL E n σ N K ρ₀ k LE LT Γ A₀ R) : TyKAL E n σ N K ρ₀ k LE LT Γ A R := by
  cases h with
  | prop hA hn hP =>
      have e := whTyA_det hA.1 (whTyA_headRefl hA.1) hn hn₀
      subst e; exact .prop hA₀ hn hP
  | sortT hA hz hk =>
      have e := whTyA_det hA.1 (whTyA_headRefl hA.1) (hStepFnA_sort _ _ _ _) hn₀
      subst e; exact .sortT hA₀ hz hk
  | sortP hA hz =>
      have e := whTyA_det hA.1 (whTyA_headRefl hA.1) (hStepFnA_sort _ _ _ _) hn₀
      subst e; exact .sortP hA₀ hz
  | pi hA hnp hDty hCty RD hD RC hC hCeq =>
      have e := whTyA_det hA.1 (whTyA_headRefl hA.1) (hStepFnA_pi _ _ _ _ _ _ _) hn₀
      subst e; exact .pi hA₀ hnp hDty hCty RD hD RC hC hCeq
  | stuck hA hN =>
      have e := whTyA_det hA.1 (whTyA_headRefl hA.1) hN.1 hn₀
      subst e; exact .stuck hA₀ hN

theorem eqKAL_tyConv {Γ : LCtxA} {A B : ExprA} (h : EqKAL E n σ N K ρ₀ k LE LT Γ A B) :
    TyConvAL E n σ N K Γ A B := by
  cases h with
  | sort _ _ _ _ hc => exact hc
  | pi _ _ _ _ _ _ _ _ _ _ _ _ hc => exact hc
  | stuck _ _ _ _ hc => exact hc

theorem tyKAL_hasTy {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKAL E n σ N K ρ₀ k LE LT Γ A R) : ∃ u, Nonempty (HasTyA E noIotaA n Γ A (.sort u)) := by
  cases h with
  | prop hA _ _ => exact whTyA_hasTy_head hA.1
  | sortT hA _ _ => exact whTyA_hasTy_head hA.1
  | sortP hA _ => exact whTyA_hasTy_head hA.1
  | pi hA _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hA.1
  | stuck hA _ => exact whTyA_hasTy_head hA.1

theorem escapeAL {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKAL E n σ N K ρ₀ k LE LT Γ A R) {a b : ExprA} (hr : R a b) :
    ConvAL E n σ N K Γ a b A := by
  cases h with
  | prop hA _ _ =>
      obtain ⟨_, _, hc⟩ := hr
      exact convAL_of_tyConvAL hc (tyConvAL_symm hA.2)
  | sortT hA _ _ =>
      obtain ⟨_, _, _, _, _, hc⟩ := hr
      exact convAL_of_tyConvAL hc (tyConvAL_symm hA.2)
  | sortP hA _ =>
      obtain ⟨_, _, _, _, hc, _⟩ := hr
      exact convAL_of_tyConvAL hc (tyConvAL_symm hA.2)
  | pi hA _ _ _ _ _ _ _ _ =>
      obtain ⟨_, _, _, hc⟩ := hr
      exact convAL_of_tyConvAL hc (tyConvAL_symm hA.2)
  | stuck hA _ =>
      obtain ⟨_, _, hc⟩ := hr
      exact convAL_of_tyConvAL hc (tyConvAL_symm hA.2)

theorem escapeAL_hasTy {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKAL E n σ N K ρ₀ k LE LT Γ A R) {a b : ExprA} (hr : R a b) :
    HasTyAL E n σ N K Γ a A ∧ HasTyAL E n σ N K Γ b A := by
  cases h with
  | prop hA _ _ =>
      obtain ⟨ha, hb, _⟩ := hr
      exact ⟨hasTyAL_of_tyConvAL ha (tyConvAL_symm hA.2), hasTyAL_of_tyConvAL hb (tyConvAL_symm hA.2)⟩
  | sortT hA _ _ =>
      obtain ⟨_, _, _, ha, hb, _⟩ := hr
      exact ⟨hasTyAL_of_tyConvAL ha (tyConvAL_symm hA.2), hasTyAL_of_tyConvAL hb (tyConvAL_symm hA.2)⟩
  | sortP hA _ =>
      obtain ⟨_, _, ha, hb, _⟩ := hr
      exact ⟨hasTyAL_of_tyConvAL ha (tyConvAL_symm hA.2), hasTyAL_of_tyConvAL hb (tyConvAL_symm hA.2)⟩
  | pi hA _ _ _ _ _ _ _ _ =>
      obtain ⟨_, ha, hb, _⟩ := hr
      exact ⟨hasTyAL_of_tyConvAL ha (tyConvAL_symm hA.2), hasTyAL_of_tyConvAL hb (tyConvAL_symm hA.2)⟩
  | stuck hA _ =>
      obtain ⟨ha, hb, _⟩ := hr
      exact ⟨hasTyAL_of_tyConvAL ha (tyConvAL_symm hA.2), hasTyAL_of_tyConvAL hb (tyConvAL_symm hA.2)⟩

theorem escape_LRTyAL {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAL E n σ N K ρ₀ k Γ A R) {a b : ExprA} (hr : R a b) :
    ConvAL E n σ N K Γ a b A := by
  rw [LRTyAL_eq] at h
  exact escapeAL h hr

theorem LREqAL_tyConv {Γ : LCtxA} {A B : ExprA} (h : LREqAL E n σ N K ρ₀ k Γ A B) :
    TyConvAL E n σ N K Γ A B := by
  rw [LREqAL_eq] at h
  exact eqKAL_tyConv h

/-! ### §3.2 Weakening & `LRRelAL` -/

theorem propValidAL_wk (hE : EnvClosedA E) {Γ : LCtxA} {a : ExprA}
    (ρ : WkSpecA) (hρ : WkSpecA.ok ρ Γ) (h : PropValidAL E n σ N K Γ a) :
    PropValidAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ a) := by
  obtain ⟨M, hM, hT⟩ := h
  exact ⟨wkExprA ρ M, whTyAL_wk hE Γ ρ hρ hM, tripleLikeA_wk hE noIotaA_lift Γ ρ hρ hT⟩

theorem EqKAL_wk (hE : EnvClosedA E) :
    {Γ : LCtxA} → {A B : ExprA} → EqKAL E n σ N K ρ₀ k LE LT Γ A B →
      ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
        EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ A) (wkExprA ρ B)
  | Γ, _, _, .sort hA hB hk hl hc, ρ, hρ => by
      have hA' := whTyAL_wk hE Γ ρ hρ.1 hA
      have hB' := whTyAL_wk hE Γ ρ hρ.1 hB
      simp only [wkExprA_sort] at hA' hB'
      exact .sort hA' hB' hk hl (tyConvAL_wk hE Γ ρ hρ.1 hc)
  | Γ, _, _, .pi hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc, ρ, hρ => by
      have hA' := whTyAL_wk hE Γ ρ hρ.1 hA
      have hB' := whTyAL_wk hE Γ ρ hρ.1 hB
      rw [wkExprA_pi_ub] at hA' hB'
      have hDty' := hasTyA_wk_ne hE noIotaA_lift ρ hρ.1 hDty
      have hD'ty' := hasTyA_wk_ne hE noIotaA_lift ρ hρ.1 hD'ty
      rw [wkExprA_sort] at hDty' hD'ty'
      refine .pi hA' hB' hu hv hDty' (hasTyA_wk_ne_binder hE noIotaA_lift ρ hρ.1 hCty) hD'ty'
        (hasTyA_wk_ne_binder hE noIotaA_lift ρ hρ.1 hC'ty)
        (fun ρ' => RD (WkSpecA.comp ρ ρ')) ?_ ?_ ?_ (tyConvAL_wk hE Γ ρ hρ.1 hc)
      · intro ρ' hρ'
        have h := hD (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ')
        rw [wkCtxA_comp, wkExprA_comp] at h
        exact h
      · intro ρ' hρ'
        have h := hDeq (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ')
        rw [wkCtxA_comp, wkExprA_comp, wkExprA_comp] at h
        exact h
      · intro ρ' hρ' a a' hr
        have h := hC (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ') a a' hr
        rw [wkCtxA_comp, WkSpecA.ub_comp, wkExprA_comp, wkExprA_comp] at h
        exact h
  | Γ, _, _, .stuck hA hB hN hN' hc, ρ, hρ =>
      .stuck (whTyAL_wk hE Γ ρ hρ.1 hA) (whTyAL_wk hE Γ ρ hρ.1 hB)
        (tripleLikeA_wk hE noIotaA_lift Γ ρ hρ.1 hN)
        (tripleLikeA_wk hE noIotaA_lift Γ ρ hρ.1 hN')
        (tyConvAL_wk hE Γ ρ hρ.1 hc)

theorem TyKAL_wk (hE : EnvClosedA E)
    (HLE : LowEqWkA E noIotaA n k LE) (HLT : LowTyWkA E noIotaA n k LT) :
    {Γ : LCtxA} → {A : ExprA} → {R : ExprA → ExprA → Prop} → TyKAL E n σ N K ρ₀ k LE LT Γ A R →
      ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∃ R' : ExprA → ExprA → Prop,
        TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ A) R' ∧
        ∀ x y : ExprA, R x y → R' (wkExprA ρ x) (wkExprA ρ y)
  | Γ, _, _, .prop hA hn hP, ρ, hρ =>
      ⟨_, .prop (whTyAL_wk hE Γ ρ hρ.1 hA) (hStepFnA_wk_none hE noIotaA_lift Γ ρ hρ.1 hn)
        ((isPropTy_wk_iff hE noIotaA_lift Γ ρ hρ.1 _).2 hP),
        fun _ _ ⟨hx, hy, hc⟩ => ⟨hasTyAL_wk hE Γ ρ hρ.1 hx, hasTyAL_wk hE Γ ρ hρ.1 hy, convAL_wk hE Γ ρ hρ.1 hc⟩⟩
  | Γ, _, _, .sortT hA hz hk, ρ, hρ => by
      have hA' := whTyAL_wk hE Γ ρ hρ.1 hA
      rw [wkExprA_sort] at hA'
      refine ⟨_, .sortT hA' hz hk, ?_⟩
      intro x y ⟨h1, ⟨R1, hLT1⟩, ⟨R2, hLT2⟩, hx, hy, hc⟩
      refine ⟨HLE _ _ Γ ρ hρ x y h1, HLT _ _ Γ ρ hρ x R1 hLT1, HLT _ _ Γ ρ hρ y R2 hLT2, ?_, ?_, ?_⟩
      · have h := hasTyAL_wk hE Γ ρ hρ.1 hx; rw [wkExprA_sort] at h; exact h
      · have h := hasTyAL_wk hE Γ ρ hρ.1 hy; rw [wkExprA_sort] at h; exact h
      · have h := convAL_wk hE Γ ρ hρ.1 hc; rw [wkExprA_sort] at h; exact h
  | Γ, _, _, .sortP hA hz, ρ, hρ => by
      have hA' := whTyAL_wk hE Γ ρ hρ.1 hA
      rw [wkExprA_sort] at hA'
      refine ⟨_, .sortP hA' hz, ?_⟩
      intro x y ⟨h1, h2, hx, hy, hc, hp⟩
      refine ⟨propValidAL_wk hE ρ hρ.1 h1, propValidAL_wk hE ρ hρ.1 h2, ?_, ?_, ?_,
        propEqAL_wk hE hp ρ hρ⟩
      · have h := hasTyAL_wk hE Γ ρ hρ.1 hx; rw [wkExprA_sort] at h; exact h
      · have h := hasTyAL_wk hE Γ ρ hρ.1 hy; rw [wkExprA_sort] at h; exact h
      · have h := convAL_wk hE Γ ρ hρ.1 hc; rw [wkExprA_sort] at h; exact h
  | Γ, _, _, .pi hA hnp hDty hCty RD hD RC hC hCeq, ρ, hρ => by
      have hA' := whTyAL_wk hE Γ ρ hρ.1 hA
      rw [wkExprA_pi_ub] at hA'
      have hnp' := fun h => hnp ((isPropTy_wk_iff hE noIotaA_lift Γ ρ hρ.1 _).1 h)
      rw [wkExprA_pi_ub] at hnp'
      have hDty' := hasTyA_wk_ne hE noIotaA_lift ρ hρ.1 hDty
      rw [wkExprA_sort] at hDty'
      refine ⟨_, .pi hA' hnp' hDty' (hasTyA_wk_ne_binder hE noIotaA_lift ρ hρ.1 hCty)
        (fun ρ' => RD (WkSpecA.comp ρ ρ')) ?_ (fun ρ' => RC (WkSpecA.comp ρ ρ')) ?_ ?_, ?_⟩
      · intro ρ' hρ'
        have h := hD (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ')
        rw [wkCtxA_comp, wkExprA_comp] at h; exact h
      · intro ρ' hρ' a a' hr
        have h := hC (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ') a a' hr
        rw [wkCtxA_comp, WkSpecA.ub_comp, wkExprA_comp] at h; exact h
      · intro ρ' hρ' a a' hr
        have h := hCeq (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ') a a' hr
        rw [wkCtxA_comp, WkSpecA.ub_comp, wkExprA_comp] at h; exact h
      · intro f g ⟨h1, h2, h3, h4⟩
        refine ⟨fun ρ' hρ' a a' hr => ?_, ?_, ?_, ?_⟩
        · have h := h1 (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ') a a' hr
          rw [wkExprA_comp, wkExprA_comp] at h; exact h
        · have h := hasTyAL_wk hE Γ ρ hρ.1 h2; rw [wkExprA_pi_ub] at h; exact h
        · have h := hasTyAL_wk hE Γ ρ hρ.1 h3; rw [wkExprA_pi_ub] at h; exact h
        · have h := convAL_wk hE Γ ρ hρ.1 h4; rw [wkExprA_pi_ub] at h; exact h
  | Γ, _, _, .stuck hA hN, ρ, hρ =>
      ⟨_, .stuck (whTyAL_wk hE Γ ρ hρ.1 hA) (stuckA_wk hE noIotaA_lift Γ ρ hρ.1 hN),
        fun _ _ ⟨hx, hy, hc⟩ => ⟨hasTyAL_wk hE Γ ρ hρ.1 hx, hasTyAL_wk hE Γ ρ hρ.1 hy, convAL_wk hE Γ ρ hρ.1 hc⟩⟩

theorem LR_wk_allAL (hE : EnvClosedA E) : ∀ k : Nat,
    (∀ {Γ : LCtxA} {A B : ExprA}, LREqAL E n σ N K ρ₀ k Γ A B →
      ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
        LREqAL E n σ N K ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ A) (wkExprA ρ B)) ∧
    (∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop},
      LRTyAL E n σ N K ρ₀ k Γ A R → ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      ∃ R' : ExprA → ExprA → Prop,
        LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ A) R' ∧
        ∀ x y : ExprA, R x y → R' (wkExprA ρ x) (wkExprA ρ y)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have HLE : LowEqWkA E noIotaA n k (fun j _ => LREqAL E n σ N K ρ₀ j) :=
      fun j hj _ ρ hρ _ _ h => (ih j hj).1 h ρ hρ
    have HLT : LowTyWkA E noIotaA n k (fun j _ => LRTyAL E n σ N K ρ₀ j) :=
      fun j hj _ ρ hρ _ _ h => ((ih j hj).2 h ρ hρ).elim fun R' hR' => ⟨R', hR'.1⟩
    refine ⟨fun h ρ hρ => ?_, fun h ρ hρ => ?_⟩
    · rw [LREqAL_eq] at h ⊢
      exact EqKAL_wk hE h ρ hρ
    · rw [LRTyAL_eq] at h ⊢
      exact TyKAL_wk hE HLE HLT h ρ hρ

theorem LREqAL_wk (hE : EnvClosedA E) {Γ : LCtxA} {A B : ExprA}
    (h : LREqAL E n σ N K ρ₀ k Γ A B) (ρ : WkSpecA) (hρ : WkOkA E noIotaA n ρ Γ) :
    LREqAL E n σ N K ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ A) (wkExprA ρ B) :=
  (LR_wk_allAL hE k).1 h ρ hρ

theorem LRTyAL_wk (hE : EnvClosedA E) {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAL E n σ N K ρ₀ k Γ A R) (ρ : WkSpecA) (hρ : WkOkA E noIotaA n ρ Γ) :
    ∃ R' : ExprA → ExprA → Prop,
      LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ A) R' ∧
      ∀ x y : ExprA, R x y → R' (wkExprA ρ x) (wkExprA ρ y) :=
  (LR_wk_allAL hE k).2 h ρ hρ

def LRRelAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) (Γ : LCtxA) (A a b : ExprA) : Prop :=
  ∃ R : ExprA → ExprA → Prop, LRTyAL E n σ N K ρ₀ k Γ A R ∧ R a b

theorem LRRelAL.of {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAL E n σ N K ρ₀ k Γ A R) {a b : ExprA} (hab : R a b) :
    LRRelAL E n σ N K ρ₀ k Γ A a b :=
  ⟨R, h, hab⟩

theorem LRRelAL.at {Γ : LCtxA} {A a b : ExprA} (h : LRRelAL E n σ N K ρ₀ k Γ A a b)
    {R : ExprA → ExprA → Prop} (hR : LRTyAL E n σ N K ρ₀ k Γ A R) : R a b := by
  obtain ⟨R', hR', hab⟩ := h
  rw [LRTyAL_unique hR hR']
  exact hab

theorem LRRelAL_wk (hE : EnvClosedA E) {Γ : LCtxA} {A a b : ExprA}
    (h : LRRelAL E n σ N K ρ₀ k Γ A a b) (ρ : WkSpecA) (hρ : WkOkA E noIotaA n ρ Γ) :
    LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ A) (wkExprA ρ a) (wkExprA ρ b) := by
  obtain ⟨R, hR, hab⟩ := h
  obtain ⟨R', hR', hmap⟩ := LRTyAL_wk hE hR ρ hρ
  exact ⟨R', hR', hmap a b hab⟩

theorem LRRelAL_hasTy {Γ : LCtxA} {A a b : ExprA}
    (h : LRRelAL E n σ N K ρ₀ k Γ A a b) :
    HasTyAL E n σ N K Γ a A ∧ HasTyAL E n σ N K Γ b A := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyAL_eq] at hR
  exact escapeAL_hasTy hR hab

theorem LRRelAL_conv {Γ : LCtxA} {A a b : ExprA}
    (h : LRRelAL E n σ N K ρ₀ k Γ A a b) :
    ConvAL E n σ N K Γ a b A := by
  obtain ⟨R, hR, hab⟩ := h
  exact escape_LRTyAL hR hab

theorem LRRelAL_valid {Γ : LCtxA} {A a b : ExprA}
    (h : LRRelAL E n σ N K ρ₀ k Γ A a b) :
    ∃ R, LRTyAL E n σ N K ρ₀ k Γ A R := by
  obtain ⟨R, hR, _⟩ := h
  exact ⟨R, hR⟩

theorem LRTyAL_hasTy {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAL E n σ N K ρ₀ k Γ A R) : ∃ u, Nonempty (HasTyA E noIotaA n Γ A (.sort u)) := by
  rw [LRTyAL_eq] at h
  exact tyKAL_hasTy h

/-! ### §3.3 Cumulativity in the height index -/

theorem LR_mono_allAL {j j' : Nat} (hjj : j ≤ j') :
    (∀ {Γ : LCtxA} {A B : ExprA},
      EqKAL E n σ N K ρ₀ j (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A B →
      EqKAL E n σ N K ρ₀ j' (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A B) ∧
    (∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop},
      TyKAL E n σ N K ρ₀ j (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A R →
      TyKAL E n σ N K ρ₀ j' (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A R) := by
  have mE : ∀ {Γ : LCtxA} {A B : ExprA},
      EqKAL E n σ N K ρ₀ j (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A B →
      EqKAL E n σ N K ρ₀ j' (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A B :=
    fun {_ _ _} h =>
    EqKAL.rec
      (motive_1 := fun Γ A B _ =>
        EqKAL E n σ N K ρ₀ j' (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A B)
      (motive_2 := fun Γ A R _ =>
        TyKAL E n σ N K ρ₀ j' (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A R)
      (fun hA hB hk hl hc => .sort hA hB (Nat.lt_of_lt_of_le hk hjj) hl hc)
      (fun hA hB hu hv hDty hCty hD'ty hC'ty RD _ _ _ hc ihD ihDeq ihC =>
        .pi hA hB hu hv hDty hCty hD'ty hC'ty RD ihD ihDeq ihC hc)
      (fun hA hB hN hN' hc => .stuck hA hB hN hN' hc)
      (fun hA hn hP => .prop hA hn hP)
      (fun hA hz hk => .sortT hA hz (Nat.lt_of_lt_of_le hk hjj))
      (fun hA hz => .sortP hA hz)
      (fun hA hnp hDty hCty RD _ RC _ _ ihD ihC ihCeq =>
        .pi hA hnp hDty hCty RD ihD RC ihC ihCeq)
      (fun hA hN => .stuck hA hN)
      h
  have mT : ∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop},
      TyKAL E n σ N K ρ₀ j (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A R →
      TyKAL E n σ N K ρ₀ j' (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A R :=
    fun {_ _ _} h =>
    TyKAL.rec
      (motive_1 := fun Γ A B _ =>
        EqKAL E n σ N K ρ₀ j' (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A B)
      (motive_2 := fun Γ A R _ =>
        TyKAL E n σ N K ρ₀ j' (fun i _ => LREqAL E n σ N K ρ₀ i) (fun i _ => LRTyAL E n σ N K ρ₀ i) Γ A R)
      (fun hA hB hk hl hc => .sort hA hB (Nat.lt_of_lt_of_le hk hjj) hl hc)
      (fun hA hB hu hv hDty hCty hD'ty hC'ty RD _ _ _ hc ihD ihDeq ihC =>
        .pi hA hB hu hv hDty hCty hD'ty hC'ty RD ihD ihDeq ihC hc)
      (fun hA hB hN hN' hc => .stuck hA hB hN hN' hc)
      (fun hA hn hP => .prop hA hn hP)
      (fun hA hz hk => .sortT hA hz (Nat.lt_of_lt_of_le hk hjj))
      (fun hA hz => .sortP hA hz)
      (fun hA hnp hDty hCty RD _ RC _ _ ihD ihC ihCeq =>
        .pi hA hnp hDty hCty RD ihD RC ihC ihCeq)
      (fun hA hN => .stuck hA hN)
      h
  exact ⟨mE, mT⟩

theorem LREqAL_mono {k k' : Nat} (hle : k ≤ k') {Γ : LCtxA} {A B : ExprA}
    (h : LREqAL E n σ N K ρ₀ k Γ A B) : LREqAL E n σ N K ρ₀ k' Γ A B := by
  rw [LREqAL_eq] at h ⊢
  exact (LR_mono_allAL hle).1 h

theorem LRTyAL_mono {k k' : Nat} (hle : k ≤ k') {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAL E n σ N K ρ₀ k Γ A R) : LRTyAL E n σ N K ρ₀ k' Γ A R := by
  rw [LRTyAL_eq] at h ⊢
  exact (LR_mono_allAL hle).2 h

theorem LRRelAL_mono {k k' : Nat} (hle : k ≤ k') {Γ : LCtxA} {A a b : ExprA}
    (h : LRRelAL E n σ N K ρ₀ k Γ A a b) : LRRelAL E n σ N K ρ₀ k' Γ A a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, LRTyAL_mono hle hR, hab⟩

/-! ### §3.4 Head expansion -/

theorem whTyAL_trans {Γ : LCtxA} {A B M : ExprA}
    (h : WhTyAL E n σ N K Γ A B) (h' : WhTyAL E n σ N K Γ B M) :
    WhTyAL E n σ N K Γ A M :=
  ⟨whTyA_trans h.1 h'.1, tyConvAL_trans h.2 h'.2⟩

theorem whTyAL_of_stepAtAL {Γ : LCtxA} {a a' : ExprA} {u : Level}
    (hs : StepAtAL E n σ N K Γ a a' (.sort u)) : WhTyAL E n σ N K Γ a a' :=
  whTyAL_step_left hs (stepAtA_hasTy_right hs.1) (whTyAL_of_hasTy (stepAtA_hasTy_right hs.1))

theorem tyKAL_expand {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyAL E n σ N K Γ A A₀)
    (h : TyKAL E n σ N K ρ₀ k LE LT Γ A₀ R) : TyKAL E n σ N K ρ₀ k LE LT Γ A R := by
  cases h with
  | prop hA' hn hP => exact .prop (whTyAL_trans hA₀ hA') hn hP
  | sortT hA' hz hk => exact .sortT (whTyAL_trans hA₀ hA') hz hk
  | sortP hA' hz => exact .sortP (whTyAL_trans hA₀ hA') hz
  | pi hA' hnp hDty hCty RD hD RC hC hCeq =>
      exact .pi (whTyAL_trans hA₀ hA') hnp hDty hCty RD hD RC hC hCeq
  | stuck hA' hN => exact .stuck (whTyAL_trans hA₀ hA') hN

theorem eqKAL_expand_left {Γ : LCtxA} {A A₀ B : ExprA}
    (hA₀ : WhTyAL E n σ N K Γ A A₀)
    (h : EqKAL E n σ N K ρ₀ k LE LT Γ A₀ B) : EqKAL E n σ N K ρ₀ k LE LT Γ A B := by
  cases h with
  | sort hA' hB hk hl hc =>
      exact .sort (whTyAL_trans hA₀ hA') hB hk hl (tyConvAL_trans hA₀.2 hc)
  | pi hA' hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc =>
      exact .pi (whTyAL_trans hA₀ hA') hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC
        (tyConvAL_trans hA₀.2 hc)
  | stuck hA' hB hN hN' hc =>
      exact .stuck (whTyAL_trans hA₀ hA') hB hN hN' (tyConvAL_trans hA₀.2 hc)

theorem eqKAL_expand_right {Γ : LCtxA} {A B B₀ : ExprA}
    (hB₀ : WhTyAL E n σ N K Γ B B₀)
    (h : EqKAL E n σ N K ρ₀ k LE LT Γ A B₀) : EqKAL E n σ N K ρ₀ k LE LT Γ A B := by
  cases h with
  | sort hA hB' hk hl hc =>
      exact .sort hA (whTyAL_trans hB₀ hB') hk hl (tyConvAL_trans hc (tyConvAL_symm hB₀.2))
  | pi hA hB' hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc =>
      exact .pi hA (whTyAL_trans hB₀ hB') hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC
        (tyConvAL_trans hc (tyConvAL_symm hB₀.2))
  | stuck hA hB' hN hN' hc =>
      exact .stuck hA (whTyAL_trans hB₀ hB') hN hN' (tyConvAL_trans hc (tyConvAL_symm hB₀.2))

theorem stepAtAL_tyConv {Γ : LCtxA} {a a' A A' : ExprA}
    (hs : StepAtAL E n σ N K Γ a a' A) (tc : TyConvAL E n σ N K Γ A A') :
    StepAtAL E n σ N K Γ a a' A' :=
  ⟨stepAtA_tyConv hs.1 tc.1, hasTyAL_of_tyConvAL hs.2.1 tc, convAL_of_tyConvAL hs.2.2 tc⟩

theorem tripleAL_expand_left {Γ : LCtxA} {a a' b M : ExprA}
    (hs : StepAtAL E n σ N K Γ a a' M)
    (h : HasTyAL E n σ N K Γ a' M ∧ HasTyAL E n σ N K Γ b M ∧ ConvAL E n σ N K Γ a' b M) :
    HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b M ∧ ConvAL E n σ N K Γ a b M :=
  ⟨hs.2.1, h.2.1, convAL_trans hs.2.2 h.2.2⟩

theorem tripleAL_expand_right {Γ : LCtxA} {a b b' M : ExprA}
    (hs : StepAtAL E n σ N K Γ b b' M)
    (h : HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b' M ∧ ConvAL E n σ N K Γ a b' M) :
    HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b M ∧ ConvAL E n σ N K Γ a b M :=
  ⟨h.1, hs.2.1, convAL_trans h.2.2 (convAL_symm hs.2.2)⟩

theorem propValidAL_expand {Γ : LCtxA} {a a' : ExprA} {l : Level}
    (hs : StepAtAL E n σ N K Γ a a' (.sort l)) (h : PropValidAL E n σ N K Γ a') :
    PropValidAL E n σ N K Γ a := by
  obtain ⟨M, hM, hT⟩ := h
  exact ⟨M, whTyAL_step_left hs (stepAtA_hasTy_right hs.1) hM, hT⟩

theorem stepAtAL_app (hE : EnvClosedA E) {Γ : LCtxA} {A D C f f' a : ExprA}
    {u v : Level} (ρ : WkSpecA) (hρ : WkSpecA.ok ρ Γ)
    (hA : WhTyAL E n σ N K Γ A (.pi D u C v))
    (hCty : Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)))
    (hTy : ∃ w, Nonempty (HasTyA E noIotaA n (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (.sort w)))
    (ha : HasTyAL E n σ N K (wkCtxA ρ Γ) a (wkExprA ρ D))
    (hs : StepAtAL E n σ N K Γ f f' A) :
    StepAtAL E n σ N K (wkCtxA ρ Γ) (.app (wkExprA ρ f) a) (.app (wkExprA ρ f') a)
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) := by
  have hs' := stepAtAL_tyConv hs hA.2
  have hsw := stepAtAL_wk hE Γ ρ hρ hs'
  rw [wkExprA_pi_ub] at hsw
  have hstepA := stepAtA_app hE noIotaA_lift ρ hρ hA.1 hCty hTy ha.1 hs.1
  refine ⟨hstepA, ⟨hstepA.1, ?_⟩, ⟨stepAtA_conv hstepA, ?_⟩⟩
  · obtain ⟨_, htf, htf_lok⟩ := hsw.2.1
    obtain ⟨_, hta, hta_lok⟩ := ha
    exact ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) C) a).symm
      ⟨.app _ _ _ _ _ htf hta, ⟨htf_lok, hta_lok⟩⟩
  · obtain ⟨_, hcf, hcf_lok⟩ := hsw.2.2
    obtain ⟨_, hta, hta_lok⟩ := ha
    exact ex_convT_lok_cast rfl rfl rfl (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) C) a).symm
      ⟨.app _ _ _ _ _ _ _ hcf (.refl _ _ _ hta), ⟨hcf_lok, hta_lok⟩⟩

abbrev ExpMotTyAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (Γ : LCtxA) (A : ExprA) (R : ExprA → ExprA → Prop) : Prop :=
  (∀ a a' b : ExprA, StepAtAL E n σ N K Γ a a' A → R a' b → R a b) ∧
  (∀ a b b' : ExprA, StepAtAL E n σ N K Γ b b' A → R a b' → R a b)

abbrev LowEqExpAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (k : Nat) (LE : LowEqTA k) : Prop :=
  ∀ (j : Nat) (hj : j < k) (Γ : LCtxA) (l : Level) (a a' b : ExprA),
    StepAtAL E n σ N K Γ a a' (.sort l) →
    (LE j hj Γ a' b → LE j hj Γ a b) ∧ (LE j hj Γ b a' → LE j hj Γ b a)

abbrev LowTyExpAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (k : Nat) (LT : LowTyTA k) : Prop :=
  ∀ (j : Nat) (hj : j < k) (Γ : LCtxA) (l : Level) (a a' : ExprA) (R : ExprA → ExprA → Prop),
    StepAtAL E n σ N K Γ a a' (.sort l) → LT j hj Γ a' R → LT j hj Γ a R

theorem expMinor_prop {Γ : LCtxA} {A A' : ExprA} (hA : WhTyAL E n σ N K Γ A A') :
    ExpMotTyAL E n σ N K Γ A (fun a b =>
      HasTyAL E n σ N K Γ a A' ∧ HasTyAL E n σ N K Γ b A' ∧
      ConvAL E n σ N K Γ a b A') :=
  ⟨fun _ _ _ hs h => tripleAL_expand_left (stepAtAL_tyConv hs hA.2) h,
   fun _ _ _ hs h => tripleAL_expand_right (stepAtAL_tyConv hs hA.2) h⟩

theorem expMinor_stuck {Γ : LCtxA} {A M : ExprA} (hA : WhTyAL E n σ N K Γ A M) :
    ExpMotTyAL E n σ N K Γ A (fun a b =>
      HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b M ∧
      ConvAL E n σ N K Γ a b M) :=
  ⟨fun _ _ _ hs h => tripleAL_expand_left (stepAtAL_tyConv hs hA.2) h,
   fun _ _ _ hs h => tripleAL_expand_right (stepAtAL_tyConv hs hA.2) h⟩

theorem expMinor_sortP {Γ : LCtxA} {A : ExprA} {l : Level} (hA : WhTyAL E n σ N K Γ A (.sort l)) :
    ExpMotTyAL E n σ N K Γ A (fun a b =>
      PropValidAL E n σ N K Γ a ∧ PropValidAL E n σ N K Γ b ∧
      HasTyAL E n σ N K Γ a (.sort l) ∧ HasTyAL E n σ N K Γ b (.sort l) ∧
      ConvAL E n σ N K Γ a b (.sort l) ∧ PropEqAL E n σ N K Γ a b) := by
  refine ⟨fun a a' b hs ⟨h1, h2, h4, h5, h6, h7⟩ => ?_,
          fun a b b' hs ⟨h1, h2, h4, h5, h6, h7⟩ => ?_⟩
  · have hs' := stepAtAL_tyConv hs hA.2
    have htr := tripleAL_expand_left hs' ⟨h4, h5, h6⟩
    exact ⟨propValidAL_expand hs' h1, h2, htr.1, htr.2.1, htr.2.2,
      propEqAL_expand_left hs' (stepAtA_hasTy_right hs'.1) h7⟩
  · have hs' := stepAtAL_tyConv hs hA.2
    have htr := tripleAL_expand_right hs' ⟨h4, h5, h6⟩
    exact ⟨h1, propValidAL_expand hs' h2, htr.1, htr.2.1, htr.2.2,
      propEqAL_expand_right hs' (stepAtA_hasTy_right hs'.1) h7⟩

theorem expMinor_sortT (HLE : LowEqExpAL E n σ N K k LE) (HLT : LowTyExpAL E n σ N K k LT)
    {Γ : LCtxA} {A : ExprA} {l : Level} (hA : WhTyAL E n σ N K Γ A (.sort l)) (hk : ht ρ₀ l < k) :
    ExpMotTyAL E n σ N K Γ A (fun a b =>
      LE (ht ρ₀ l) hk Γ a b ∧
      (∃ R, LT (ht ρ₀ l) hk Γ a R) ∧
      (∃ R, LT (ht ρ₀ l) hk Γ b R) ∧
      HasTyAL E n σ N K Γ a (.sort l) ∧ HasTyAL E n σ N K Γ b (.sort l) ∧
      ConvAL E n σ N K Γ a b (.sort l)) := by
  refine ⟨fun a a' b hs ⟨h1, ⟨R1, h2⟩, h3, h4, h5, h6⟩ => ?_,
          fun a b b' hs ⟨h1, h2, ⟨R2, h3⟩, h4, h5, h6⟩ => ?_⟩
  · have hs' := stepAtAL_tyConv hs hA.2
    have htr := tripleAL_expand_left hs' ⟨h4, h5, h6⟩
    exact ⟨(HLE _ hk Γ l a a' b hs').1 h1, ⟨R1, HLT _ hk Γ l a a' R1 hs' h2⟩, h3,
      htr.1, htr.2.1, htr.2.2⟩
  · have hs' := stepAtAL_tyConv hs hA.2
    have htr := tripleAL_expand_right hs' ⟨h4, h5, h6⟩
    exact ⟨(HLE _ hk Γ l b b' a hs').2 h1, h2, ⟨R2, HLT _ hk Γ l b b' R2 hs' h3⟩,
      htr.1, htr.2.1, htr.2.2⟩

theorem expMinor_pi (hE : EnvClosedA E) {Γ : LCtxA} {A D C : ExprA} {u v : Level}
    (hA : WhTyAL E n σ N K Γ A (.pi D u C v))
    (_hnp : ¬ IsPropTy E noIotaA Γ (.pi D u C v))
    (_hDty : Nonempty (HasTyA E noIotaA n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
    (hC : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (hCeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C)))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ),
      ExpMotTyAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      ExpMotTyAL E n σ N K (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a)) :
    ExpMotTyAL E n σ N K Γ A (fun f g =>
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      HasTyAL E n σ N K Γ f (.pi D u C v) ∧ HasTyAL E n σ N K Γ g (.pi D u C v) ∧
      ConvAL E n σ N K Γ f g (.pi D u C v)) := by
  refine ⟨fun f f' g hs ⟨h1, h2, h3, h4⟩ => ?_,
          fun f g g' hs ⟨h1, h2, h3, h4⟩ => ?_⟩
  · have hs' := stepAtAL_tyConv hs hA.2
    have htr := tripleAL_expand_left hs' ⟨h2, h3, h4⟩
    refine ⟨fun ρ hρ x x' hr => ?_, htr.1, htr.2.1, htr.2.2⟩
    have hx := (escapeAL_hasTy (hD ρ hρ) hr).1
    have hTy := tyKAL_hasTy (hC ρ hρ x x' hr)
    exact (ihC ρ hρ x x' hr).1 _ _ _ (stepAtAL_app hE ρ hρ.1 hA hCty hTy hx hs) (h1 ρ hρ x x' hr)
  · have hs' := stepAtAL_tyConv hs hA.2
    have htr := tripleAL_expand_right hs' ⟨h2, h3, h4⟩
    refine ⟨fun ρ hρ x x' hr => ?_, htr.1, htr.2.1, htr.2.2⟩
    have hx' := (escapeAL_hasTy (hD ρ hρ) hr).2
    have heq := hCeq ρ hρ x x' hr
    have hTy' : ∃ w, Nonempty (HasTyA E noIotaA n (wkCtxA ρ Γ) (instantiate0A x' (wkExprA (WkSpecA.ub ρ) C)) (.sort w)) := by
      cases heq with
      | sort _ hB _ _ _ => exact whTyA_hasTy_head hB.1
      | pi _ hB _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hB.1
      | stuck _ hB _ _ _ => exact whTyA_hasTy_head hB.1
    have hstep := stepAtAL_app hE ρ hρ.1 hA hCty hTy' hx' hs
    have tc := eqKAL_tyConv heq
    exact (ihC ρ hρ x x' hr).2 _ _ _ (stepAtAL_tyConv hstep (tyConvAL_symm tc)) (h1 ρ hρ x x' hr)

theorem tyKAL_termExpand (hE : EnvClosedA E)
    (HLE : LowEqExpAL E n σ N K k LE) (HLT : LowTyExpAL E n σ N K k LT) :
    {Γ : LCtxA} → {A : ExprA} → {R : ExprA → ExprA → Prop} →
    TyKAL E n σ N K ρ₀ k LE LT Γ A R → ExpMotTyAL E n σ N K Γ A R :=
  fun {_Γ _A _R} h =>
  TyKAL.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ A R _ => ExpMotTyAL E n σ N K Γ A R)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro)
    (fun hA _ _ => expMinor_prop hA)
    (fun hA _ hk => expMinor_sortT HLE HLT hA hk)
    (fun hA _ => expMinor_sortP hA)
    (fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC _ =>
      expMinor_pi hE hA hnp hDty hCty RD hD RC hC hCeq ihD ihC)
    (fun hA _ => expMinor_stuck hA)
    h

theorem LRTyAL_expand {Γ : LCtxA} {A A₀ : ExprA} {R : ExprA → ExprA → Prop}
    (hA₀ : WhTyAL E n σ N K Γ A A₀)
    (h : LRTyAL E n σ N K ρ₀ k Γ A₀ R) : LRTyAL E n σ N K ρ₀ k Γ A R := by
  rw [LRTyAL_eq] at h ⊢
  exact tyKAL_expand hA₀ h

theorem LREqAL_expand_left {Γ : LCtxA} {A A₀ B : ExprA}
    (hA₀ : WhTyAL E n σ N K Γ A A₀)
    (h : LREqAL E n σ N K ρ₀ k Γ A₀ B) : LREqAL E n σ N K ρ₀ k Γ A B := by
  rw [LREqAL_eq] at h ⊢
  exact eqKAL_expand_left hA₀ h

theorem LREqAL_expand_right {Γ : LCtxA} {A B B₀ : ExprA}
    (hB₀ : WhTyAL E n σ N K Γ B B₀)
    (h : LREqAL E n σ N K ρ₀ k Γ A B₀) : LREqAL E n σ N K ρ₀ k Γ A B := by
  rw [LREqAL_eq] at h ⊢
  exact eqKAL_expand_right hB₀ h

theorem LRTyAL_termExpand (hE : EnvClosedA E) {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAL E n σ N K ρ₀ k Γ A R) : ExpMotTyAL E n σ N K Γ A R := by
  have HLE : LowEqExpAL E n σ N K k (fun j _ => LREqAL E n σ N K ρ₀ j) :=
    fun j _ Γ l a a' b hs =>
      ⟨LREqAL_expand_left (whTyAL_of_stepAtAL hs),
       LREqAL_expand_right (whTyAL_of_stepAtAL hs)⟩
  have HLT : LowTyExpAL E n σ N K k (fun j _ => LRTyAL E n σ N K ρ₀ j) :=
    fun j _ Γ l a a' R hs =>
      LRTyAL_expand (whTyAL_of_stepAtAL hs)
  rw [LRTyAL_eq] at h
  exact tyKAL_termExpand hE HLE HLT h

theorem LRRelAL_expand_left (hE : EnvClosedA E) {Γ : LCtxA} {A a a' b : ExprA}
    (hs : StepAtAL E n σ N K Γ a a' A) (h : LRRelAL E n σ N K ρ₀ k Γ A a' b) :
    LRRelAL E n σ N K ρ₀ k Γ A a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, (LRTyAL_termExpand hE hR).1 a a' b hs hab⟩

theorem LRRelAL_expand_right (hE : EnvClosedA E) {Γ : LCtxA} {A a b b' : ExprA}
    (hs : StepAtAL E n σ N K Γ b b' A) (h : LRRelAL E n σ N K ρ₀ k Γ A a b') :
    LRRelAL E n σ N K ρ₀ k Γ A a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, (LRTyAL_termExpand hE hR).2 a b b' hs hab⟩

/-! ### §3.5 Neutral reflection -/

abbrev ReflMotTyAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (Γ : LCtxA) (A : ExprA) (R : ExprA → ExprA → Prop) : Prop :=
  ∀ a b : ExprA, NeutKA E noIotaA Γ a → NeutKA E noIotaA Γ b →
    HasTyAL E n σ N K Γ a A → HasTyAL E n σ N K Γ b A →
    ConvAL E n σ N K Γ a b A → R a b

abbrev LowEqReflAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (k : Nat) (LE : LowEqTA k) : Prop :=
  ∀ (j : Nat) (hj : j < k) (Γ : LCtxA) (l : Level) (a b : ExprA),
    NeutKA E noIotaA Γ a → NeutKA E noIotaA Γ b →
    HasTyAL E n σ N K Γ a (.sort l) → HasTyAL E n σ N K Γ b (.sort l) →
    ConvAL E n σ N K Γ a b (.sort l) → LE j hj Γ a b

abbrev LowTyReflAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (k : Nat) (LT : LowTyTA k) : Prop :=
  ∀ (j : Nat) (hj : j < k) (Γ : LCtxA) (l : Level) (a : ExprA),
    NeutKA E noIotaA Γ a → HasTyAL E n σ N K Γ a (.sort l) → ∃ R, LT j hj Γ a R

theorem reflMinor_prop {Γ : LCtxA} {A A' : ExprA} (hA : WhTyAL E n σ N K Γ A A') :
    ReflMotTyAL E n σ N K Γ A (fun a b =>
      HasTyAL E n σ N K Γ a A' ∧ HasTyAL E n σ N K Γ b A' ∧
      ConvAL E n σ N K Γ a b A') :=
  fun _ _ _ _ ha hb hab =>
    ⟨hasTyAL_of_tyConvAL ha hA.2, hasTyAL_of_tyConvAL hb hA.2, convAL_of_tyConvAL hab hA.2⟩

theorem reflMinor_stuck {Γ : LCtxA} {A M : ExprA} (hA : WhTyAL E n σ N K Γ A M) :
    ReflMotTyAL E n σ N K Γ A (fun a b =>
      HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b M ∧
      ConvAL E n σ N K Γ a b M) :=
  fun _ _ _ _ ha hb hab =>
    ⟨hasTyAL_of_tyConvAL ha hA.2, hasTyAL_of_tyConvAL hb hA.2, convAL_of_tyConvAL hab hA.2⟩

theorem reflMinor_sortP {Γ : LCtxA} {A : ExprA} {l : Level} (hA : WhTyAL E n σ N K Γ A (.sort l)) :
    ReflMotTyAL E n σ N K Γ A (fun a b =>
      PropValidAL E n σ N K Γ a ∧ PropValidAL E n σ N K Γ b ∧
      HasTyAL E n σ N K Γ a (.sort l) ∧ HasTyAL E n σ N K Γ b (.sort l) ∧
      ConvAL E n σ N K Γ a b (.sort l) ∧ PropEqAL E n σ N K Γ a b) := by
  intro a b hna hnb ha hb hab
  have ha' := hasTyAL_of_tyConvAL ha hA.2
  have hb' := hasTyAL_of_tyConvAL hb hA.2
  have hab' := convAL_of_tyConvAL hab hA.2
  exact ⟨⟨a, whTyAL_of_hasTy ha'.1, tripleLikeA_of_stuck (neutKA_stuck hna)⟩,
    ⟨b, whTyAL_of_hasTy hb'.1, tripleLikeA_of_stuck (neutKA_stuck hnb)⟩,
    ha', hb', hab', propEqAL_stuck_refl ha'.1 hb'.1 (neutKA_stuck hna) (neutKA_stuck hnb) hab'⟩

theorem reflMinor_sortT (HLE : LowEqReflAL E n σ N K k LE) (HLT : LowTyReflAL E n σ N K k LT)
    {Γ : LCtxA} {A : ExprA} {l : Level} (hA : WhTyAL E n σ N K Γ A (.sort l)) (hk : ht ρ₀ l < k) :
    ReflMotTyAL E n σ N K Γ A (fun a b =>
      LE (ht ρ₀ l) hk Γ a b ∧
      (∃ R, LT (ht ρ₀ l) hk Γ a R) ∧
      (∃ R, LT (ht ρ₀ l) hk Γ b R) ∧
      HasTyAL E n σ N K Γ a (.sort l) ∧ HasTyAL E n σ N K Γ b (.sort l) ∧
      ConvAL E n σ N K Γ a b (.sort l)) := by
  intro a b hna hnb ha hb hab
  have ha' := hasTyAL_of_tyConvAL ha hA.2
  have hb' := hasTyAL_of_tyConvAL hb hA.2
  have hab' := convAL_of_tyConvAL hab hA.2
  exact ⟨HLE _ hk Γ l a b hna hnb ha' hb' hab', HLT _ hk Γ l a hna ha', HLT _ hk Γ l b hnb hb',
    ha', hb', hab'⟩

theorem reflMinor_pi (hE : EnvClosedA E) {Γ : LCtxA} {A D C : ExprA} {u v : Level}
    (hA : WhTyAL E n σ N K Γ A (.pi D u C v))
    (_hnp : ¬ IsPropTy E noIotaA Γ (.pi D u C v))
    (_hDty : Nonempty (HasTyA E noIotaA n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
    (hC : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (hCeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C)))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ),
      ReflMotTyAL E n σ N K (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      ReflMotTyAL E n σ N K (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a)) :
    ReflMotTyAL E n σ N K Γ A (fun f g =>
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      HasTyAL E n σ N K Γ f (.pi D u C v) ∧ HasTyAL E n σ N K Γ g (.pi D u C v) ∧
      ConvAL E n σ N K Γ f g (.pi D u C v)) := by
  intro f g hnf hng hf hg hfg
  have hf' := hasTyAL_of_tyConvAL hf hA.2
  have hg' := hasTyAL_of_tyConvAL hg hA.2
  have hfg' := convAL_of_tyConvAL hfg hA.2
  refine ⟨fun ρ hρ x x' hr => ?_, hf', hg', hfg'⟩
  have hnf_w := neutKA_wk ρ hρ.1 hnf
  have hng_w := neutKA_wk ρ hρ.1 hng
  have hfw := hasTyAL_wk hE Γ ρ hρ.1 hf'
  have hgw := hasTyAL_wk hE Γ ρ hρ.1 hg'
  have hfgw := convAL_wk hE Γ ρ hρ.1 hfg'
  rw [wkExprA_pi_ub] at hfw hgw hfgw
  obtain ⟨hx, hx'⟩ := escapeAL_hasTy (hD ρ hρ) hr
  have hxx := escapeAL (hD ρ hρ) hr
  have hCw := hasTyA_wk_ne_binder hE noIotaA_lift ρ hρ.1 hCty
  obtain ⟨tCw⟩ := hCw
  obtain ⟨w, ⟨tCx⟩⟩ := tyKAL_hasTy (hC ρ hρ x x' hr)
  have heq := hCeq ρ hρ x x' hr
  have hTy' : ∃ w', Nonempty (HasTyA E noIotaA n (wkCtxA ρ Γ) (instantiate0A x' (wkExprA (WkSpecA.ub ρ) C)) (.sort w')) := by
    cases heq with
    | sort _ hB _ _ _ => exact whTyA_hasTy_head hB.1
    | pi _ hB _ _ _ _ _ _ _ _ _ _ _ => exact whTyA_hasTy_head hB.1
    | stuck _ hB _ _ _ => exact whTyA_hasTy_head hB.1
  obtain ⟨w', ⟨tCx'⟩⟩ := hTy'
  have tapp1 : HasTyAL E n σ N K (wkCtxA ρ Γ) (.app (wkExprA ρ f) x)
      (instantiate0A x (wkExprA (WkSpecA.ub ρ) C)) := by
    obtain ⟨⟨tf⟩, htf, htf_lok⟩ := hfw
    obtain ⟨⟨tx⟩, htx, htx_lok⟩ := hx
    refine ⟨⟨.app _ _ _ _ _ u v w tCw tCx tf tx⟩, ?_⟩
    exact ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) C) x).symm
      ⟨.app _ _ _ _ _ htf htx, ⟨htf_lok, htx_lok⟩⟩
  have tapp2' : HasTyAL E n σ N K (wkCtxA ρ Γ) (.app (wkExprA ρ g) x')
      (instantiate0A x' (wkExprA (WkSpecA.ub ρ) C)) := by
    obtain ⟨⟨tg⟩, htg, htg_lok⟩ := hgw
    obtain ⟨⟨tx'⟩, htx', htx'_lok⟩ := hx'
    refine ⟨⟨.app _ _ _ _ _ u v w' tCw tCx' tg tx'⟩, ?_⟩
    exact ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) C) x').symm
      ⟨.app _ _ _ _ _ htg htx', ⟨htg_lok, htx'_lok⟩⟩
  have tc := eqKAL_tyConv heq
  have tapp2 := hasTyAL_of_tyConvAL tapp2' (tyConvAL_symm tc)
  have capp : ConvAL E n σ N K (wkCtxA ρ Γ) (.app (wkExprA ρ f) x) (.app (wkExprA ρ g) x')
      (instantiate0A x (wkExprA (WkSpecA.ub ρ) C)) := by
    obtain ⟨⟨cfg⟩, hcfg, hcfg_lok⟩ := hfgw
    obtain ⟨⟨cxx'⟩, hcxx', hcxx'_lok⟩ := hxx
    obtain ⟨t2⟩ := tapp2.1
    refine ⟨⟨.app _ _ _ _ _ _ _ u v cfg cxx' tCw t2⟩, ?_⟩
    exact ex_convT_lok_cast rfl rfl rfl (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) C) x).symm
      ⟨.app _ _ _ _ _ _ _ hcfg hcxx', ⟨hcfg_lok, hcxx'_lok⟩⟩
  exact ihC ρ hρ x x' hr _ _ (neutKA_app x hnf_w) (neutKA_app x' hng_w) tapp1 tapp2 capp

theorem reflectAL (hE : EnvClosedA E)
    (HLE : LowEqReflAL E n σ N K k LE) (HLT : LowTyReflAL E n σ N K k LT) :
    {Γ : LCtxA} → {A : ExprA} → {R : ExprA → ExprA → Prop} →
    TyKAL E n σ N K ρ₀ k LE LT Γ A R → ReflMotTyAL E n σ N K Γ A R :=
  fun {_Γ _A _R} h =>
  TyKAL.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun Γ A R _ => ReflMotTyAL E n σ N K Γ A R)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro)
    (fun hA _ _ => reflMinor_prop hA)
    (fun hA _ hk => reflMinor_sortT HLE HLT hA hk)
    (fun hA _ => reflMinor_sortP hA)
    (fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC _ =>
      reflMinor_pi hE hA hnp hDty hCty RD hD RC hC hCeq ihD ihC)
    (fun hA _ => reflMinor_stuck hA)
    h

theorem LRRelAL_reflect (hE : EnvClosedA E) {Γ : LCtxA} {A a b : ExprA}
    (hA : ∃ R, LRTyAL E n σ N K ρ₀ k Γ A R)
    (hna : NeutKA E noIotaA Γ a) (hnb : NeutKA E noIotaA Γ b)
    (ha : HasTyAL E n σ N K Γ a A) (hb : HasTyAL E n σ N K Γ b A)
    (hab : ConvAL E n σ N K Γ a b A) :
    LRRelAL E n σ N K ρ₀ k Γ A a b := by
  have HLE : LowEqReflAL E n σ N K k (fun j _ => LREqAL E n σ N K ρ₀ j) := by
    intro j _ Γ l a b hna hnb ha hb hab
    rw [LREqAL_eq]
    exact .stuck (whTyAL_of_hasTy ha.1) (whTyAL_of_hasTy hb.1)
      (tripleLikeA_of_stuck (neutKA_stuck hna)) (tripleLikeA_of_stuck (neutKA_stuck hnb))
      (tyConvAL_of_convAL ha.1 (eqNA_refl l) hb.1 (eqNA_refl l) hab)
  have HLT : LowTyReflAL E n σ N K k (fun j _ => LRTyAL E n σ N K ρ₀ j) := by
    intro j _ Γ l a hna ha
    dsimp only
    rw [LRTyAL_eq]
    exact ⟨_, tyKAL_of_tripleLike (whTyAL_of_hasTy ha.1) (tripleLikeA_of_stuck (neutKA_stuck hna))⟩
  obtain ⟨R, hR⟩ := hA
  refine ⟨R, hR, ?_⟩
  rw [LRTyAL_eq] at hR
  exact reflectAL hE HLE HLT hR a b hna hnb ha hb hab

theorem LRRelAL_bvar (hE : EnvClosedA E) {Γ : LCtxA} {i : Nat} {A : ExprA}
    (hlk : lookupValueA Γ i = none)
    (hA : ∃ R, LRTyAL E n σ N K ρ₀ k Γ A R)
    (ht : HasTyAL E n σ N K Γ (.bvar i) A) :
    LRRelAL E n σ N K ρ₀ k Γ A (.bvar i) (.bvar i) :=
  LRRelAL_reflect hE hA
    (neutKA_bvar hE noIotaA_lift (iotaConstHeadA_of_recHead (noIotaA_recHead E)) hlk)
    (neutKA_bvar hE noIotaA_lift (iotaConstHeadA_of_recHead (noIotaA_recHead E)) hlk)
    ht ht (convAL_refl ht)

/-! ### §3.6 Conversion transport & PER -/

theorem tripleAL_eq_of_tyConv {Γ : LCtxA} {M M' : ExprA} (hc : TyConvAL E n σ N K Γ M M') :
    (fun a b : ExprA => HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b M ∧
        ConvAL E n σ N K Γ a b M) =
    (fun a b : ExprA => HasTyAL E n σ N K Γ a M' ∧ HasTyAL E n σ N K Γ b M' ∧
        ConvAL E n σ N K Γ a b M') := by
  funext a b
  apply propext
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨hasTyAL_of_tyConvAL h1 hc, hasTyAL_of_tyConvAL h2 hc, convAL_of_tyConvAL h3 hc⟩,
         fun ⟨h1, h2, h3⟩ => ⟨hasTyAL_of_tyConvAL h1 (tyConvAL_symm hc),
           hasTyAL_of_tyConvAL h2 (tyConvAL_symm hc), convAL_of_tyConvAL h3 (tyConvAL_symm hc)⟩⟩

abbrev TransMotAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) (LE : LowEqTA k) (LT : LowTyTA k) (Γ : LCtxA) (A B : ExprA) : Prop :=
  ∀ R R' : ExprA → ExprA → Prop,
    TyKAL E n σ N K ρ₀ k LE LT Γ A R → TyKAL E n σ N K ρ₀ k LE LT Γ B R' → R = R'

theorem transMinor_sort {Γ : LCtxA} {A B : ExprA} {l l' : Level}
    (hA : WhTyAL E n σ N K Γ A (.sort l)) (hB : WhTyAL E n σ N K Γ B (.sort l'))
    (_hk : ht ρ₀ l < k) (hl : eqN l l') (hc : TyConvAL E n σ N K Γ A B) :
    TransMotAL E n σ N K ρ₀ k LE LT Γ A B := by
  intro R R' tA tB
  have hz : isZero l = isZero l' := isZero_eqN hl
  have tc := tyConvAL_nf hA hB hc
  cases tA with
  | prop hA₁ hn₁ hP₁ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_sort _ _ _ _) hn₁
      subst e; exact absurd hP₁ (not_isPropTy_sort _ _ _ _)
  | pi hA₁ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
  | stuck hA₁ hN₁ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_sort _ _ _ _) hN₁.1
      subst e; exact (stuckA_not_sort hN₁).elim
  | sortT hA₁ hz₁ hk₁ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
      cases tB with
      | prop hB₁ hn₂ hP₂ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) hn₂
          subst e; exact absurd hP₂ (not_isPropTy_sort _ _ _ _)
      | pi hB₁ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
      | stuck hB₁ hN₂ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) hN₂.1
          subst e; exact (stuckA_not_sort hN₂).elim
      | sortP hB₁ hz₂ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e; rw [hz₁, hz₂] at hz; cases hz
      | sortT hB₁ _ hk₂ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          have hidx : ht ρ₀ l = ht ρ₀ l' := ht_of_eqN hl
          funext a b
          apply propext
          constructor
          · rintro ⟨h1, h2, h3, h4, h5, h6⟩
            exact ⟨(lowEq_cast LE _ _ hidx Γ a b).1 h1, (lowTy_cast LT _ _ hidx Γ a).1 h2,
              (lowTy_cast LT _ _ hidx Γ b).1 h3, hasTyAL_of_tyConvAL h4 tc,
              hasTyAL_of_tyConvAL h5 tc, convAL_of_tyConvAL h6 tc⟩
          · rintro ⟨h1, h2, h3, h4, h5, h6⟩
            exact ⟨(lowEq_cast LE _ _ hidx Γ a b).2 h1, (lowTy_cast LT _ _ hidx Γ a).2 h2,
              (lowTy_cast LT _ _ hidx Γ b).2 h3, hasTyAL_of_tyConvAL h4 (tyConvAL_symm tc),
              hasTyAL_of_tyConvAL h5 (tyConvAL_symm tc), convAL_of_tyConvAL h6 (tyConvAL_symm tc)⟩
  | sortP hA₁ hz₁ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
      cases tB with
      | prop hB₁ hn₂ hP₂ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) hn₂
          subst e; exact absurd hP₂ (not_isPropTy_sort _ _ _ _)
      | pi hB₁ _ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
      | stuck hB₁ hN₂ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) hN₂.1
          subst e; exact (stuckA_not_sort hN₂).elim
      | sortT hB₁ hz₂ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e; rw [hz₁, hz₂] at hz; cases hz
      | sortP hB₁ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
          funext a b
          apply propext
          constructor
          · rintro ⟨h1, h2, h4, h5, h6, h7⟩
            exact ⟨h1, h2, hasTyAL_of_tyConvAL h4 tc, hasTyAL_of_tyConvAL h5 tc,
              convAL_of_tyConvAL h6 tc, h7⟩
          · rintro ⟨h1, h2, h4, h5, h6, h7⟩
            exact ⟨h1, h2, hasTyAL_of_tyConvAL h4 (tyConvAL_symm tc),
              hasTyAL_of_tyConvAL h5 (tyConvAL_symm tc),
              convAL_of_tyConvAL h6 (tyConvAL_symm tc), h7⟩

theorem transMinor_stuck {Γ : LCtxA} {A B M M' : ExprA}
    (hA : WhTyAL E n σ N K Γ A M) (hB : WhTyAL E n σ N K Γ B M')
    (hN : TripleLikeA E noIotaA Γ M) (hN' : TripleLikeA E noIotaA Γ M')
    (hc : TyConvAL E n σ N K Γ A B) :
    TransMotAL E n σ N K ρ₀ k LE LT Γ A B := by
  intro R R' tA tB
  have tc := tyConvAL_nf hA hB hc
  have eA : R = fun a b => HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b M ∧
      ConvAL E n σ N K Γ a b M := by
    cases tA with
    | prop hA₁ hn₁ _ =>
        have e := whTyA_det hA.1 hA₁.1 hN.1 hn₁
        subst e; rfl
    | stuck hA₁ hN₁ =>
        have e := whTyA_det hA.1 hA₁.1 hN.1 hN₁.1
        subst e; rfl
    | sortT hA₁ _ _ =>
        have e := whTyA_det hA.1 hA₁.1 hN.1 (hStepFnA_sort _ _ _ _)
        subst e; exact (tripleLikeA_not_sort hN).elim
    | sortP hA₁ _ =>
        have e := whTyA_det hA.1 hA₁.1 hN.1 (hStepFnA_sort _ _ _ _)
        subst e; exact (tripleLikeA_not_sort hN).elim
    | pi hA₁ hnp₁ _ _ _ _ _ _ _ =>
        have e := whTyA_det hA.1 hA₁.1 hN.1 (hStepFnA_pi _ _ _ _ _ _ _)
        subst e; exact (hnp₁ (tripleLikeA_pi_isProp hN)).elim
  have eB : R' = fun a b => HasTyAL E n σ N K Γ a M' ∧ HasTyAL E n σ N K Γ b M' ∧
      ConvAL E n σ N K Γ a b M' := by
    cases tB with
    | prop hB₁ hn₁ _ =>
        have e := whTyA_det hB.1 hB₁.1 hN'.1 hn₁
        subst e; rfl
    | stuck hB₁ hN₁ =>
        have e := whTyA_det hB.1 hB₁.1 hN'.1 hN₁.1
        subst e; rfl
    | sortT hB₁ _ _ =>
        have e := whTyA_det hB.1 hB₁.1 hN'.1 (hStepFnA_sort _ _ _ _)
        subst e; exact (tripleLikeA_not_sort hN').elim
    | sortP hB₁ _ =>
        have e := whTyA_det hB.1 hB₁.1 hN'.1 (hStepFnA_sort _ _ _ _)
        subst e; exact (tripleLikeA_not_sort hN').elim
    | pi hB₁ hnp₁ _ _ _ _ _ _ _ =>
        have e := whTyA_det hB.1 hB₁.1 hN'.1 (hStepFnA_pi _ _ _ _ _ _ _)
        subst e; exact (hnp₁ (tripleLikeA_pi_isProp hN')).elim
  rw [eA, eB]
  exact tripleAL_eq_of_tyConv tc

theorem transMinor_pi {Γ : LCtxA} {A B D C D' C' : ExprA} {u v u' v' : Level}
    (hA : WhTyAL E n σ N K Γ A (.pi D u C v)) (hB : WhTyAL E n σ N K Γ B (.pi D' u' C' v'))
    (_hu : eqN u u') (hv : eqN v v')
    (_hDty : Nonempty (HasTyA E noIotaA n Γ D (.sort u)))
    (_hCty : Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)))
    (_hD'ty : Nonempty (HasTyA E noIotaA n Γ D' (.sort u')))
    (_hC'ty : Nonempty (HasTyA E noIotaA n (.assumption D' :: Γ) C' (.sort v')))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (_hDeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (_hC : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
    (hc : TyConvAL E n σ N K Γ A B)
    (ihDeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ),
      TransMotAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      TransMotAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C'))) :
    TransMotAL E n σ N K ρ₀ k LE LT Γ A B := by
  intro R R' tA tB
  have tc := tyConvAL_nf hA hB hc
  cases tA with
  | sortT hA₁ _ _ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | sortP hA₁ _ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | stuck hA₁ hN₁ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) hN₁.1
      subst e; exact (stuckA_not_pi hN₁).elim
  | prop hA₁ hn₁ hP₁ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) hn₁
      subst e
      cases tB with
      | sortT hB₁ _ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | sortP hB₁ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | stuck hB₁ hN₂ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) hN₂.1
          subst e; exact (stuckA_not_pi hN₂).elim
      | prop hB₁ hn₂ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) hn₂
          subst e; exact tripleAL_eq_of_tyConv tc
      | pi hB₁ hnp₂ _ _ _ _ _ _ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e; exact (hnp₂ ((isPropTy_pi_eqN hv).1 hP₁)).elim
  | pi hA₁ hnp₁ _ _ RD₁ hD₁ RC₁ hC₁ _ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
      cases tB with
      | sortT hB₁ _ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | sortP hB₁ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
          cases e
      | stuck hB₁ hN₂ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) hN₂.1
          subst e; exact (stuckA_not_pi hN₂).elim
      | prop hB₁ hn₂ hP₂ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) hn₂
          subst e; exact (hnp₁ ((isPropTy_pi_eqN hv).2 hP₂)).elim
      | pi hB₁ _ _ _ RD₂ hD₂ RC₂ hC₂ _ =>
          have e := whTyA_det hB.1 hB₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
          cases e
          have hRD₁ : ∀ ρ (hρ : WkOkA E noIotaA n ρ Γ), RD ρ = RD₁ ρ :=
            fun ρ hρ => TyKAL_unique (hD ρ hρ) (hD₁ ρ hρ)
          have hRD : ∀ ρ (hρ : WkOkA E noIotaA n ρ Γ), RD₁ ρ = RD₂ ρ :=
            fun ρ hρ => ihDeq ρ hρ _ _ (hD₁ ρ hρ) (hD₂ ρ hρ)
          have hRC : ∀ ρ (hρ : WkOkA E noIotaA n ρ Γ) a a', RD₁ ρ a a' → RC₁ ρ a = RC₂ ρ a :=
            fun ρ hρ a a' hr =>
              ihC ρ hρ a a' (by rw [hRD₁ ρ hρ]; exact hr) _ _ (hC₁ ρ hρ a a' hr)
                (hC₂ ρ hρ a a' (by rw [← hRD ρ hρ]; exact hr))
          funext f g
          apply propext
          constructor
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨fun ρ hρ a a' hr => ?_,
              hasTyAL_of_tyConvAL h2 tc, hasTyAL_of_tyConvAL h3 tc, convAL_of_tyConvAL h4 tc⟩
            have hr₁ : RD₁ ρ a a' := by rw [hRD ρ hρ]; exact hr
            have h := h1 ρ hρ a a' hr₁
            rw [hRC ρ hρ a a' hr₁] at h
            exact h
          · rintro ⟨h1, h2, h3, h4⟩
            refine ⟨fun ρ hρ a a' hr => ?_,
              hasTyAL_of_tyConvAL h2 (tyConvAL_symm tc),
              hasTyAL_of_tyConvAL h3 (tyConvAL_symm tc),
              convAL_of_tyConvAL h4 (tyConvAL_symm tc)⟩
            have h := h1 ρ hρ a a' (by rw [← hRD ρ hρ]; exact hr)
            rw [← hRC ρ hρ a a' hr] at h
            exact h

theorem eqKAL_transport {Γ : LCtxA} {A B : ExprA}
    (h : EqKAL E n σ N K ρ₀ k LE LT Γ A B) {R R' : ExprA → ExprA → Prop}
    (tA : TyKAL E n σ N K ρ₀ k LE LT Γ A R) (tB : TyKAL E n σ N K ρ₀ k LE LT Γ B R') : R = R' :=
  EqKAL.rec (motive_1 := fun Γ A B _ => TransMotAL E n σ N K ρ₀ k LE LT Γ A B)
    (motive_2 := fun _ _ _ _ => True)
    (fun hA hB hk hl hc => transMinor_sort hA hB hk hl hc)
    (fun hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc _ ihDeq ihC =>
      transMinor_pi hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihDeq ihC)
    (fun hA hB hN hN' hc => transMinor_stuck hA hB hN hN' hc)
    (fun _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ => True.intro)
    h R R' tA tB

def canonRelAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) (LE : LowEqTA k) (LT : LowTyTA k)
    (Γ : LCtxA) (A : ExprA) : ExprA → ExprA → Prop :=
  fun x y => ∃ R, TyKAL E n σ N K ρ₀ k LE LT Γ A R ∧ R x y

theorem canonRelAL_eq {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKAL E n σ N K ρ₀ k LE LT Γ A R) : canonRelAL E n σ N K ρ₀ k LE LT Γ A = R := by
  funext x y
  apply propext
  exact ⟨fun ⟨R', hR', hxy⟩ => by rw [← TyKAL_unique hR' h]; exact hxy, fun hxy => ⟨R, h, hxy⟩⟩

theorem tyKAL_canon {Γ : LCtxA} {A : ExprA} (h : ∃ R, TyKAL E n σ N K ρ₀ k LE LT Γ A R) :
    TyKAL E n σ N K ρ₀ k LE LT Γ A (canonRelAL E n σ N K ρ₀ k LE LT Γ A) := by
  obtain ⟨R, hR⟩ := h
  rw [canonRelAL_eq hR]
  exact hR

theorem perMinor_tripleAL {Γ : LCtxA} (M : ExprA) :
    PerMotA (fun a b : ExprA => HasTyAL E n σ N K Γ a M ∧ HasTyAL E n σ N K Γ b M ∧
      ConvAL E n σ N K Γ a b M) :=
  ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h2, h1, convAL_symm h3⟩,
   fun _ _ _ ⟨h1, _, h3⟩ ⟨_, h2', h3'⟩ => ⟨h1, h2', convAL_trans h3 h3'⟩⟩

theorem perMinor_sortTAL (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE) {Γ : LCtxA} {l : Level}
    (hk : ht ρ₀ l < k) :
    PerMotA (fun a b : ExprA =>
      LE (ht ρ₀ l) hk Γ a b ∧
      (∃ R, LT (ht ρ₀ l) hk Γ a R) ∧
      (∃ R, LT (ht ρ₀ l) hk Γ b R) ∧
      HasTyAL E n σ N K Γ a (.sort l) ∧ HasTyAL E n σ N K Γ b (.sort l) ∧
      ConvAL E n σ N K Γ a b (.sort l)) :=
  ⟨fun _ _ ⟨h1, h2, h3, h4, h5, h6⟩ =>
     ⟨HS _ _ Γ _ _ h1, h3, h2, h5, h4, convAL_symm h6⟩,
   fun _ _ _ ⟨h1, h2, _, h4, _, h6⟩ ⟨h1', _, h3', _, h5', h6'⟩ =>
     ⟨HT _ _ Γ _ _ _ h1 h1', h2, h3', h4, h5', convAL_trans h6 h6'⟩⟩

theorem perMinor_sortPAL {Γ : LCtxA} (l : Level) :
    PerMotA (fun a b : ExprA =>
      PropValidAL E n σ N K Γ a ∧ PropValidAL E n σ N K Γ b ∧
      HasTyAL E n σ N K Γ a (.sort l) ∧ HasTyAL E n σ N K Γ b (.sort l) ∧
      ConvAL E n σ N K Γ a b (.sort l) ∧ PropEqAL E n σ N K Γ a b) :=
  ⟨fun _ _ ⟨h1, h2, h4, h5, h6, h7⟩ =>
     ⟨h2, h1, h5, h4, convAL_symm h6, propEqAL_symm h7⟩,
   fun _ _ _ ⟨h1, _, h4, _, h6, h7⟩ ⟨_, h3', _, h5', h6', h7'⟩ =>
     ⟨h1, h3', h4, h5', convAL_trans h6 h6', propEqAL_trans h7 h7'⟩⟩

theorem perMinor_piAL {Γ : LCtxA} {A D C : ExprA} {u v : Level}
    (_hA : WhTyAL E n σ N K Γ A (.pi D u C v)) (_hnp : ¬ IsPropTy E noIotaA Γ (.pi D u C v))
    (_hDty : Nonempty (HasTyA E noIotaA n Γ D (.sort u)))
    (_hCty : Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (_hD : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
    (hC : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (hCeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C)))
    (ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ), PerMotA (RD ρ))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      PerMotA (RC ρ a)) :
    PerMotA (fun f g : ExprA =>
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      HasTyAL E n σ N K Γ f (.pi D u C v) ∧ HasTyAL E n σ N K Γ g (.pi D u C v) ∧
      ConvAL E n σ N K Γ f g (.pi D u C v)) := by
  have hmove : ∀ ρ (hρ : WkOkA E noIotaA n ρ Γ) a a', RD ρ a a' → RC ρ a' = RC ρ a :=
    fun ρ hρ a a' hr =>
      eqKAL_transport (hCeq ρ hρ a' a ((ihD ρ hρ).1 a a' hr))
        (hC ρ hρ a' a ((ihD ρ hρ).1 a a' hr)) (hC ρ hρ a a' hr)
  refine ⟨fun f g ⟨h1, h2, h3, h4⟩ => ⟨fun ρ hρ a a' hr => ?_, h3, h2, convAL_symm h4⟩,
    fun f g h ⟨h1, h2, _, h4⟩ ⟨h1', _, h3', h4'⟩ =>
      ⟨fun ρ hρ a a' hr => ?_, h2, h3', convAL_trans h4 h4'⟩⟩
  · have hr' : RD ρ a' a := (ihD ρ hρ).1 a a' hr
    have h := (ihC ρ hρ a' a hr').1 _ _ (h1 ρ hρ a' a hr')
    rw [hmove ρ hρ a a' hr] at h
    exact h
  · have hr' : RD ρ a' a := (ihD ρ hρ).1 a a' hr
    have hrr : RD ρ a' a' := (ihD ρ hρ).2 a' a a' hr' hr
    have h := h1' ρ hρ a' a' hrr
    rw [hmove ρ hρ a a' hr] at h
    exact (ihC ρ hρ a a' hr).2 _ _ _ (h1 ρ hρ a a' hr) h

theorem tyKAL_per (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE) {Γ : LCtxA} {A : ExprA}
    {R : ExprA → ExprA → Prop} (h : TyKAL E n σ N K ρ₀ k LE LT Γ A R) : PerMotA R :=
  TyKAL.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ R _ => PerMotA R)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ => True.intro)
    (fun _ _ _ => perMinor_tripleAL _)
    (fun _ _ hk => perMinor_sortTAL HS HT hk)
    (fun _ _ => perMinor_sortPAL _)
    (fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC _ =>
      perMinor_piAL hA hnp hDty hCty RD hD RC hC hCeq ihD ihC)
    (fun _ _ => perMinor_tripleAL _)
    h

abbrev TransMotEqAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) (LE : LowEqTA k) (LT : LowTyTA k) (Γ : LCtxA) (A B : ExprA) : Prop :=
  ∀ X : ExprA, EqKAL E n σ N K ρ₀ k LE LT Γ B X → EqKAL E n σ N K ρ₀ k LE LT Γ A X

theorem transEqMinor_sort {Γ : LCtxA} {A B : ExprA} {l l' : Level}
    (hA : WhTyAL E n σ N K Γ A (.sort l)) (hB : WhTyAL E n σ N K Γ B (.sort l'))
    (hk : ht ρ₀ l < k) (hl : eqN l l') (hc : TyConvAL E n σ N K Γ A B) :
    TransMotEqAL E n σ N K ρ₀ k LE LT Γ A B := by
  intro X h2
  cases h2 with
  | sort hB' hX _ hl' hc' =>
      have e := whTyA_det hB.1 hB'.1 (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
      exact .sort hA hX hk (eqNA_trans hl hl') (tyConvAL_trans hc hc')
  | pi hB' _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hB.1 hB'.1 (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
  | stuck hB' _ hN _ _ =>
      have e := whTyA_det hB.1 hB'.1 (hStepFnA_sort _ _ _ _) hN.1
      subst e; exact (tripleLikeA_not_sort hN).elim

theorem transEqMinor_stuck {Γ : LCtxA} {A B M M' : ExprA}
    (hA : WhTyAL E n σ N K Γ A M) (hB : WhTyAL E n σ N K Γ B M')
    (hN : TripleLikeA E noIotaA Γ M) (hN' : TripleLikeA E noIotaA Γ M')
    (hc : TyConvAL E n σ N K Γ A B) :
    TransMotEqAL E n σ N K ρ₀ k LE LT Γ A B := by
  intro X h2
  cases h2 with
  | sort hB' _ _ _ _ =>
      have e := whTyA_det hB.1 hB'.1 hN'.1 (hStepFnA_sort _ _ _ _)
      subst e; exact (tripleLikeA_not_sort hN').elim
  | pi hB' hX _ hv' _ _ _ _ _ _ _ _ hc' =>
      have e := whTyA_det hB.1 hB'.1 hN'.1 (hStepFnA_pi _ _ _ _ _ _ _)
      subst e
      exact .stuck hA hX hN
        ⟨hStepFnA_pi _ _ _ _ _ _ _, Or.inl ((isPropTy_pi_eqN hv').1 (tripleLikeA_pi_isProp hN'))⟩
        (tyConvAL_trans hc hc')
  | stuck _ hX _ hNX hc' =>
      exact .stuck hA hX hN hNX (tyConvAL_trans hc hc')

theorem transEqMinor_pi {Γ : LCtxA} {A B D C D' C' : ExprA} {u v u' v' : Level}
    (hA : WhTyAL E n σ N K Γ A (.pi D u C v)) (hB : WhTyAL E n σ N K Γ B (.pi D' u' C' v'))
    (hu : eqN u u') (hv : eqN v v')
    (hDty : Nonempty (HasTyA E noIotaA n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)))
    (_hD'ty : Nonempty (HasTyA E noIotaA n Γ D' (.sort u')))
    (_hC'ty : Nonempty (HasTyA E noIotaA n (.assumption D' :: Γ) C' (.sort v')))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (hDeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (_hC : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
    (hc : TyConvAL E n σ N K Γ A B)
    (ihDeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ),
      TransMotEqAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      TransMotEqAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C'))) :
    TransMotEqAL E n σ N K ρ₀ k LE LT Γ A B := by
  intro X h2
  cases h2 with
  | sort hB' _ _ _ _ =>
      have e := whTyA_det hB.1 hB'.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | stuck hB' hX hN hNX hc' =>
      have e := whTyA_det hB.1 hB'.1 (hStepFnA_pi _ _ _ _ _ _ _) hN.1
      subst e
      exact .stuck hA hX
        ⟨hStepFnA_pi _ _ _ _ _ _ _, Or.inl ((isPropTy_pi_eqN hv).2 (tripleLikeA_pi_isProp hN))⟩
        hNX (tyConvAL_trans hc hc')
  | pi hB' hX hu' hv' _ _ hD''ty hC''ty RD' hD' hD'eq hC' hc' =>
      have e := whTyA_det hB.1 hB'.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
      have hRD : ∀ ρ (hρ : WkOkA E noIotaA n ρ Γ), RD ρ = RD' ρ := fun ρ hρ =>
        eqKAL_transport (hDeq ρ hρ) (hD ρ hρ) (hD' ρ hρ)
      refine .pi hA hX (eqNA_trans hu hu') (eqNA_trans hv hv') hDty hCty hD''ty hC''ty RD hD
        (fun ρ hρ => ihDeq ρ hρ _ (hD'eq ρ hρ))
        (fun ρ hρ a a' hr => ihC ρ hρ a a' hr _ (hC' ρ hρ a a' (by rw [← hRD ρ hρ]; exact hr)))
        (tyConvAL_trans hc hc')

theorem eqKAL_trans :
    {Γ : LCtxA} → {A B X : ExprA} →
    EqKAL E n σ N K ρ₀ k LE LT Γ A B → EqKAL E n σ N K ρ₀ k LE LT Γ B X →
    EqKAL E n σ N K ρ₀ k LE LT Γ A X :=
  fun {_Γ _A _B X} h h2 =>
  EqKAL.rec (motive_1 := fun Γ A B _ => TransMotEqAL E n σ N K ρ₀ k LE LT Γ A B)
    (motive_2 := fun _ _ _ _ => True)
    (fun hA hB hk hl hc => transEqMinor_sort hA hB hk hl hc)
    (fun hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc _ ihDeq ihC =>
      transEqMinor_pi hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihDeq ihC)
    (fun hA hB hN hN' hc => transEqMinor_stuck hA hB hN hN' hc)
    (fun _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ => True.intro)
    h X h2

abbrev SymmMotEqAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) (LE : LowEqTA k) (LT : LowTyTA k) (Γ : LCtxA) (A B : ExprA) : Prop :=
  EqKAL E n σ N K ρ₀ k LE LT Γ B A ∧
  (∀ R : ExprA → ExprA → Prop, TyKAL E n σ N K ρ₀ k LE LT Γ A R →
    ∃ R', TyKAL E n σ N K ρ₀ k LE LT Γ B R')

theorem symmEqMinor_sort {Γ : LCtxA} {A B : ExprA} {l l' : Level}
    (hA : WhTyAL E n σ N K Γ A (.sort l)) (hB : WhTyAL E n σ N K Γ B (.sort l'))
    (hk : ht ρ₀ l < k) (hl : eqN l l') (hc : TyConvAL E n σ N K Γ A B) :
    SymmMotEqAL E n σ N K ρ₀ k LE LT Γ A B :=
  have hk' : ht ρ₀ l' < k := by rw [← ht_of_eqN hl]; exact hk
  ⟨.sort hB hA hk' (eqNA_symm hl) (tyConvAL_symm hc), fun _ _ => by
    cases hz : isZero l' with
    | false => exact ⟨_, .sortT hB hz hk'⟩
    | true => exact ⟨_, .sortP hB hz⟩⟩

theorem symmEqMinor_stuck {Γ : LCtxA} {A B M M' : ExprA}
    (hA : WhTyAL E n σ N K Γ A M) (hB : WhTyAL E n σ N K Γ B M')
    (hN : TripleLikeA E noIotaA Γ M) (hN' : TripleLikeA E noIotaA Γ M')
    (hc : TyConvAL E n σ N K Γ A B) :
    SymmMotEqAL E n σ N K ρ₀ k LE LT Γ A B :=
  ⟨.stuck hB hA hN' hN (tyConvAL_symm hc), fun _ _ => ⟨_, tyKAL_of_tripleLike hB hN'⟩⟩

theorem symmEqMinor_pi (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {A B D C D' C' : ExprA} {u v u' v' : Level}
    (hA : WhTyAL E n σ N K Γ A (.pi D u C v)) (hB : WhTyAL E n σ N K Γ B (.pi D' u' C' v'))
    (hu : eqN u u') (hv : eqN v v')
    (hDty : Nonempty (HasTyA E noIotaA n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)))
    (hD'ty : Nonempty (HasTyA E noIotaA n Γ D' (.sort u')))
    (hC'ty : Nonempty (HasTyA E noIotaA n (.assumption D' :: Γ) C' (.sort v')))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (_hDeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ →
      EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (hC : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
    (hc : TyConvAL E n σ N K Γ A B)
    (ihDeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ),
      SymmMotEqAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E noIotaA n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      SymmMotEqAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C'))) :
    SymmMotEqAL E n σ N K ρ₀ k LE LT Γ A B := by
  have hD' : ∀ ρ (hρ : WkOkA E noIotaA n ρ Γ),
      TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D')
        (canonRelAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D')) :=
    fun ρ hρ => tyKAL_canon ((ihDeq ρ hρ).2 (RD ρ) (hD ρ hρ))
  have hRD' : ∀ ρ (hρ : WkOkA E noIotaA n ρ Γ),
      canonRelAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D') = RD ρ :=
    fun ρ hρ => eqKAL_transport (ihDeq ρ hρ).1 (hD' ρ hρ) (hD ρ hρ)
  refine ⟨.pi hB hA (eqNA_symm hu) (eqNA_symm hv) hD'ty hC'ty hDty hCty _ hD'
    (fun ρ hρ => (ihDeq ρ hρ).1)
    (fun ρ hρ a a' hr' => (ihC ρ hρ a a' (by rw [← hRD' ρ hρ]; exact hr')).1)
    (tyConvAL_symm hc), fun R tA => ?_⟩
  cases tA with
  | sortT hA₁ _ _ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | sortP hA₁ _ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | stuck hA₁ hN₁ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) hN₁.1
      subst e; exact (stuckA_not_pi hN₁).elim
  | prop hA₁ hn₁ hP₁ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) hn₁
      subst e
      exact ⟨_, .prop hB (hStepFnA_pi _ _ _ _ _ _ _) ((isPropTy_pi_eqN hv).1 hP₁)⟩
  | pi hA₁ hnp₁ _ _ RD₁ hD₁ RC₁ hC₁ hCeq₁ =>
      have e := whTyA_det hA.1 hA₁.1 (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
      have hRD₁ : ∀ ρ (hρ : WkOkA E noIotaA n ρ Γ), RD ρ = RD₁ ρ :=
        fun ρ hρ => TyKAL_unique (hD ρ hρ) (hD₁ ρ hρ)
      refine ⟨_, .pi hB (fun h => hnp₁ ((isPropTy_pi_eqN hv).2 h)) hD'ty hC'ty _ hD'
        (fun ρ a => canonRelAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
        (fun ρ hρ a a' hr' => ?_) (fun ρ hρ a a' hr' => ?_)⟩
      · have hr : RD ρ a a' := by rw [← hRD' ρ hρ]; exact hr'
        have hr₁ : RD₁ ρ a a' := by rw [← hRD₁ ρ hρ]; exact hr
        exact tyKAL_canon ((ihC ρ hρ a a' hr).2 (RC₁ ρ a) (hC₁ ρ hρ a a' hr₁))
      · have hr : RD ρ a a' := by rw [← hRD' ρ hρ]; exact hr'
        have hr₁ : RD₁ ρ a a' := by rw [← hRD₁ ρ hρ]; exact hr
        have hper := tyKAL_per HS HT (hD ρ hρ)
        have hrr : RD ρ a' a' := hper.2 a' a a' (hper.1 a a' hr) hr
        exact eqKAL_trans (ihC ρ hρ a a' hr).1
          (eqKAL_trans (hCeq₁ ρ hρ a a' hr₁) (hC ρ hρ a' a' hrr))

theorem eqKAL_symm_valid (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE) :
    {Γ : LCtxA} → {A B : ExprA} → EqKAL E n σ N K ρ₀ k LE LT Γ A B →
    EqKAL E n σ N K ρ₀ k LE LT Γ B A ∧
    (∀ R : ExprA → ExprA → Prop, TyKAL E n σ N K ρ₀ k LE LT Γ A R →
      ∃ R', TyKAL E n σ N K ρ₀ k LE LT Γ B R') :=
  fun {_Γ _A _B} h =>
  EqKAL.rec (motive_1 := fun Γ A B _ => SymmMotEqAL E n σ N K ρ₀ k LE LT Γ A B)
    (motive_2 := fun _ _ _ _ => True)
    (fun hA hB hk hl hc => symmEqMinor_sort hA hB hk hl hc)
    (fun hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc _ ihDeq ihC =>
      symmEqMinor_pi HS HT hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihDeq ihC)
    (fun hA hB hN hN' hc => symmEqMinor_stuck hA hB hN hN' hc)
    (fun _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ => True.intro)
    h

theorem eqKAL_symm (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE) {Γ : LCtxA} {A B : ExprA}
    (h : EqKAL E n σ N K ρ₀ k LE LT Γ A B) : EqKAL E n σ N K ρ₀ k LE LT Γ B A :=
  (eqKAL_symm_valid HS HT h).1

theorem eqKAL_valid (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE) {Γ : LCtxA} {A B : ExprA}
    (h : EqKAL E n σ N K ρ₀ k LE LT Γ A B) {R : ExprA → ExprA → Prop}
    (hA : TyKAL E n σ N K ρ₀ k LE LT Γ A R) : ∃ R', TyKAL E n σ N K ρ₀ k LE LT Γ B R' :=
  (eqKAL_symm_valid HS HT h).2 R hA

def LRPerAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) : Prop :=
  (∀ {Γ : LCtxA} {A B : ExprA}, LREqAL E n σ N K ρ₀ k Γ A B → LREqAL E n σ N K ρ₀ k Γ B A) ∧
  (∀ {Γ : LCtxA} {A B X : ExprA}, LREqAL E n σ N K ρ₀ k Γ A B → LREqAL E n σ N K ρ₀ k Γ B X →
    LREqAL E n σ N K ρ₀ k Γ A X) ∧
  (∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}, LRTyAL E n σ N K ρ₀ k Γ A R → PerMotA R) ∧
  (∀ {Γ : LCtxA} {A B : ExprA}, LREqAL E n σ N K ρ₀ k Γ A B →
    (∃ R, LRTyAL E n σ N K ρ₀ k Γ A R) → ∃ R', LRTyAL E n σ N K ρ₀ k Γ B R')

theorem LRPerAL_all : ∀ k : Nat, LRPerAL E n σ N K ρ₀ k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have HS : LowEqSymmA k (fun j _ => LREqAL E n σ N K ρ₀ j) := fun j hj _ _ _ h => (ih j hj).1 h
    have HT : LowEqTransA k (fun j _ => LREqAL E n σ N K ρ₀ j) :=
      fun j hj _ _ _ _ h h' => (ih j hj).2.1 h h'
    refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_, fun h hA => ?_⟩
    · rw [LREqAL_eq] at h ⊢; exact eqKAL_symm HS HT h
    · rw [LREqAL_eq] at h h' ⊢; exact eqKAL_trans h h'
    · rw [LRTyAL_eq] at h; exact tyKAL_per HS HT h
    · obtain ⟨R, hR⟩ := hA
      rw [LREqAL_eq] at h
      rw [LRTyAL_eq] at hR
      obtain ⟨R', hR'⟩ := eqKAL_valid HS HT h hR
      exact ⟨R', by rw [LRTyAL_eq]; exact hR'⟩

theorem LREqAL_transport {Γ : LCtxA} {A B : ExprA} (h : LREqAL E n σ N K ρ₀ k Γ A B)
    {R R' : ExprA → ExprA → Prop}
    (hA : LRTyAL E n σ N K ρ₀ k Γ A R) (hB : LRTyAL E n σ N K ρ₀ k Γ B R') : R = R' := by
  rw [LREqAL_eq] at h
  rw [LRTyAL_eq] at hA hB
  exact eqKAL_transport h hA hB

theorem LRRelAL_transport {Γ : LCtxA} {A B a b : ExprA} (h : LREqAL E n σ N K ρ₀ k Γ A B)
    (hB : ∃ R', LRTyAL E n σ N K ρ₀ k Γ B R') (hab : LRRelAL E n σ N K ρ₀ k Γ A a b) :
    LRRelAL E n σ N K ρ₀ k Γ B a b := by
  obtain ⟨R, hR, hab⟩ := hab
  obtain ⟨R', hR'⟩ := hB
  refine ⟨R', hR', ?_⟩
  rw [LREqAL_transport h hR hR'] at hab
  exact hab

theorem LREqAL_symm {Γ : LCtxA} {A B : ExprA} (h : LREqAL E n σ N K ρ₀ k Γ A B) :
    LREqAL E n σ N K ρ₀ k Γ B A := (LRPerAL_all k).1 h

theorem LREqAL_trans {Γ : LCtxA} {A B X : ExprA} (h : LREqAL E n σ N K ρ₀ k Γ A B)
    (h' : LREqAL E n σ N K ρ₀ k Γ B X) : LREqAL E n σ N K ρ₀ k Γ A X := (LRPerAL_all k).2.1 h h'

theorem LREqAL_valid {Γ : LCtxA} {A B : ExprA} (h : LREqAL E n σ N K ρ₀ k Γ A B)
    (hA : ∃ R, LRTyAL E n σ N K ρ₀ k Γ A R) : ∃ R', LRTyAL E n σ N K ρ₀ k Γ B R' :=
  (LRPerAL_all k).2.2.2 h hA

theorem LRRelAL_symm {Γ : LCtxA} {A a b : ExprA} (h : LRRelAL E n σ N K ρ₀ k Γ A a b) :
    LRRelAL E n σ N K ρ₀ k Γ A b a := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, ((LRPerAL_all k).2.2.1 hR).1 a b hab⟩

theorem LRRelAL_trans {Γ : LCtxA} {A a b c : ExprA} (h : LRRelAL E n σ N K ρ₀ k Γ A a b)
    (h' : LRRelAL E n σ N K ρ₀ k Γ A b c) : LRRelAL E n σ N K ρ₀ k Γ A a c := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, ((LRPerAL_all k).2.2.1 hR).2 a b c hab (h'.at hR)⟩

theorem LRRelAL_refl_left {Γ : LCtxA} {A a b : ExprA} (h : LRRelAL E n σ N K ρ₀ k Γ A a b) :
    LRRelAL E n σ N K ρ₀ k Γ A a a := LRRelAL_trans h (LRRelAL_symm h)

theorem LRRelAL_transport' {Γ : LCtxA} {A B a b : ExprA} (h : LREqAL E n σ N K ρ₀ k Γ A B)
    (hab : LRRelAL E n σ N K ρ₀ k Γ A a b) : LRRelAL E n σ N K ρ₀ k Γ B a b := by
  obtain ⟨R, hR, hab'⟩ := hab
  exact LRRelAL_transport h (LREqAL_valid h ⟨R, hR⟩) ⟨R, hR, hab'⟩

theorem LRTyAL_canon {Γ : LCtxA} {A : ExprA} (h : ∃ R, LRTyAL E n σ N K ρ₀ k Γ A R) :
    LRTyAL E n σ N K ρ₀ k Γ A (canonRelAL E n σ N K ρ₀ k (fun j _ => LREqAL E n σ N K ρ₀ j)
      (fun j _ => LRTyAL E n σ N K ρ₀ j) Γ A) := by
  obtain ⟨R, hR⟩ := h
  rw [LRTyAL_eq] at hR ⊢
  exact tyKAL_canon ⟨R, hR⟩

theorem LRRelAL_eq_canon {Γ : LCtxA} {A : ExprA} (h : ∃ R, LRTyAL E n σ N K ρ₀ k Γ A R) :
    LRRelAL E n σ N K ρ₀ k Γ A =
      canonRelAL E n σ N K ρ₀ k (fun j _ => LREqAL E n σ N K ρ₀ j)
        (fun j _ => LRTyAL E n σ N K ρ₀ j) Γ A := by
  obtain ⟨R, hR⟩ := h
  funext x y
  apply propext
  refine ⟨fun hxy => ⟨R, by rw [← LRTyAL_eq]; exact hR, hxy.at hR⟩,
          fun ⟨R', hR', hxy⟩ => ⟨R', by rw [LRTyAL_eq]; exact hR', hxy⟩⟩

theorem LRTyAL_canon' {Γ : LCtxA} {A : ExprA} (h : ∃ R, LRTyAL E n σ N K ρ₀ k Γ A R) :
    LRTyAL E n σ N K ρ₀ k Γ A (fun a b => LRRelAL E n σ N K ρ₀ k Γ A a b) := by
  rw [LRRelAL_eq_canon h]
  exact LRTyAL_canon h

/-! ## §4 `ValidSubstAL`, `EnvSemAL`, `LOKtA` / `LOKcA`, and the `LOKc`-indexed fundamental theorem `fundAL` -/

/-! ### §4.1 Sort inversion and sort relatedness -/

theorem tyKAL_sort_inv {Γ : LCtxA} {u : Level} {R : ExprA → ExprA → Prop}
    (h : TyKAL E n σ N K ρ₀ k LE LT Γ (.sort u) R) :
    (isZero u = false ∧ ∃ hk : ht ρ₀ u < k, R = fun a b =>
        LE (ht ρ₀ u) hk Γ a b ∧ (∃ R, LT (ht ρ₀ u) hk Γ a R) ∧ (∃ R, LT (ht ρ₀ u) hk Γ b R) ∧
        HasTyAL E n σ N K Γ a (.sort u) ∧ HasTyAL E n σ N K Γ b (.sort u) ∧
        ConvAL E n σ N K Γ a b (.sort u)) ∨
    (isZero u = true ∧ R = fun a b =>
        PropValidAL E n σ N K Γ a ∧ PropValidAL E n σ N K Γ b ∧
        HasTyAL E n σ N K Γ a (.sort u) ∧ HasTyAL E n σ N K Γ b (.sort u) ∧
        ConvAL E n σ N K Γ a b (.sort u) ∧ PropEqAL E n σ N K Γ a b) := by
  have hS : WhTyA E noIotaA n Γ (.sort u) (.sort u) := whTyA_of_hasTy (.sort Γ u)
  cases h with
  | prop hA hn hP =>
      have e := whTyA_det hA.1 hS hn (hStepFnA_sort E noIotaA.fn Γ u)
      subst e
      exact absurd hP (not_isPropTy_sort E noIotaA Γ u)
  | sortT hA hz hk =>
      have e := whTyA_det hA.1 hS (hStepFnA_sort E noIotaA.fn Γ _) (hStepFnA_sort E noIotaA.fn Γ u)
      cases e
      exact Or.inl ⟨hz, hk, rfl⟩
  | sortP hA hz =>
      have e := whTyA_det hA.1 hS (hStepFnA_sort E noIotaA.fn Γ _) (hStepFnA_sort E noIotaA.fn Γ u)
      cases e
      exact Or.inr ⟨hz, rfl⟩
  | pi hA _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA.1 hS (hStepFnA_pi E noIotaA.fn Γ _ _ _ _) (hStepFnA_sort E noIotaA.fn Γ u)
      cases e
  | stuck hA hN =>
      have e := whTyA_det hA.1 hS hN.1 (hStepFnA_sort E noIotaA.fn Γ u)
      subst e
      exact (stuckA_not_sort hN).elim

theorem LRRelAL_sort_elim {Γ : LCtxA} {u : Level} {A B : ExprA}
    (h : LRRelAL E n σ N K ρ₀ k Γ (.sort u) A B) :
    LREqAL E n σ N K ρ₀ k Γ A B ∧ (∃ R, LRTyAL E n σ N K ρ₀ k Γ A R) ∧
    (∃ R, LRTyAL E n σ N K ρ₀ k Γ B R) ∧
    HasTyAL E n σ N K Γ A (.sort u) ∧ HasTyAL E n σ N K Γ B (.sort u) ∧
    ConvAL E n σ N K Γ A B (.sort u) := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyAL_eq] at hR
  rcases tyKAL_sort_inv hR with ⟨_, hk, e⟩ | ⟨_, e⟩
  · subst e
    obtain ⟨hle, hva, hvb, hta, htb, hc⟩ := hab
    exact ⟨LREqAL_mono (Nat.le_of_lt hk) hle,
      hva.elim fun R h => ⟨R, LRTyAL_mono (Nat.le_of_lt hk) h⟩,
      hvb.elim fun R h => ⟨R, LRTyAL_mono (Nat.le_of_lt hk) h⟩, hta, htb, hc⟩
  · subst e
    obtain ⟨⟨M, hM, hM'⟩, ⟨M₂, hM₂, hM₂'⟩, hta, htb, hc, _⟩ := hab
    refine ⟨?_, ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hM hM'⟩,
      ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hM₂ hM₂'⟩, hta, htb, hc⟩
    rw [LREqAL_eq]
    exact .stuck hM hM₂ hM' hM₂' (tyConvAL_of_convAL hta.1 (eqNA_refl u) htb.1 (eqNA_refl u) hc)

theorem LRRelAL_sort_elim' {Γ : LCtxA} {u : Level} {A B : ExprA}
    (h : LRRelAL E n σ N K ρ₀ k Γ (.sort u) A B) :
    (∀ k', ht ρ₀ u ≤ k' →
      LREqAL E n σ N K ρ₀ k' Γ A B ∧ (∃ R, LRTyAL E n σ N K ρ₀ k' Γ A R) ∧
      (∃ R, LRTyAL E n σ N K ρ₀ k' Γ B R)) ∧
    HasTyAL E n σ N K Γ A (.sort u) ∧ HasTyAL E n σ N K Γ B (.sort u) ∧
    ConvAL E n σ N K Γ A B (.sort u) := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyAL_eq] at hR
  rcases tyKAL_sort_inv hR with ⟨_, hk, e⟩ | ⟨_, e⟩
  · subst e
    obtain ⟨hle, hva, hvb, hta, htb, hc⟩ := hab
    refine ⟨fun k' hk' => ⟨LREqAL_mono hk' hle,
      hva.elim fun R h => ⟨R, LRTyAL_mono hk' h⟩,
      hvb.elim fun R h => ⟨R, LRTyAL_mono hk' h⟩⟩, hta, htb, hc⟩
  · subst e
    obtain ⟨⟨M, hM, hM'⟩, ⟨M₂, hM₂, hM₂'⟩, hta, htb, hc, _⟩ := hab
    refine ⟨fun k' _ => ⟨?_, ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hM hM'⟩,
      ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hM₂ hM₂'⟩⟩, hta, htb, hc⟩
    rw [LREqAL_eq]
    exact .stuck hM hM₂ hM' hM₂' (tyConvAL_of_convAL hta.1 (eqNA_refl u) htb.1 (eqNA_refl u) hc)

theorem LREqAL_of_sortRel {Γ : LCtxA} {u : Level} {A B : ExprA}
    (h : LRRelAL E n σ N K ρ₀ k Γ (.sort u) A B) : LREqAL E n σ N K ρ₀ k Γ A B :=
  (LRRelAL_sort_elim h).1

theorem LRRelAL_sort0_elim {Γ : LCtxA} {A B : ExprA}
    (h : LRRelAL E n σ N K ρ₀ k Γ (.sort .zero) A B) :
    PropValidAL E n σ N K Γ A ∧ PropValidAL E n σ N K Γ B ∧
    HasTyAL E n σ N K Γ A (.sort .zero) ∧ HasTyAL E n σ N K Γ B (.sort .zero) ∧
    ConvAL E n σ N K Γ A B (.sort .zero) ∧ PropEqAL E n σ N K Γ A B := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyAL_eq] at hR
  rcases tyKAL_sort_inv hR with ⟨hz, _, _⟩ | ⟨_, e⟩
  · cases hz
  · subst e; exact hab

theorem LRRelAL_sortP_elim {Γ : LCtxA} {u : Level} {A B : ExprA} (hz : isZero u = true)
    (h : LRRelAL E n σ N K ρ₀ k Γ (.sort u) A B) :
    PropValidAL E n σ N K Γ A ∧ PropValidAL E n σ N K Γ B ∧
    HasTyAL E n σ N K Γ A (.sort u) ∧ HasTyAL E n σ N K Γ B (.sort u) ∧
    ConvAL E n σ N K Γ A B (.sort u) ∧ PropEqAL E n σ N K Γ A B := by
  obtain ⟨R, hR, hab⟩ := h
  rw [LRTyAL_eq] at hR
  rcases tyKAL_sort_inv hR with ⟨hz', _, _⟩ | ⟨_, e⟩
  · rw [hz] at hz'; cases hz'
  · subst e; exact hab

/-- Sort-conversion level guard: either `u = u'` syntactically (zero `.sorts` cost, uses `TyConvT.refl`)
    or `evalTotal σ (.succ u) ≤ N ∧ evalTotal σ (.succ u') ≤ N` (uses `ConvT.sorts`). -/
def SortEqOK (σ : Nat → Nat) (N : Nat) (u u' : Level) : Prop :=
  u = u' ∨ (evalTotal σ (.succ u) ≤ N ∧ evalTotal σ (.succ u') ≤ N)

theorem SortEqOK.symm {u u' : Level} (h : SortEqOK σ N u u') : SortEqOK σ N u' u :=
  h.elim (fun he => Or.inl he.symm) (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)

theorem tyConvAL_sorts (Γ : LCtxA) {u u' : Level} (hu : eqN u u') (hOK : SortEqOK σ N u u') :
    TyConvAL E n σ N K Γ (.sort u) (.sort u') := by
  rcases hOK with rfl | ⟨hu1, _⟩
  · exact tyConvAL_refl Γ (.sort u)
  · exact tyConvAL_of_convAL ⟨.sort Γ u⟩ (eqNA_refl (.succ u)) ⟨.sort Γ u'⟩ (eqNA_succ (eqNA_symm hu))
      ⟨⟨.sorts Γ u u' hu⟩, ⟨.sorts (eraseCtx Γ) u u' hu, hu1⟩⟩

theorem LREqAL_sorts (Γ : LCtxA) {l l' : Level} (hk : ht ρ₀ l < k) (hl : eqN l l')
    (hOK : SortEqOK σ N l l') :
    LREqAL E n σ N K ρ₀ k Γ (.sort l) (.sort l') := by
  rw [LREqAL_eq]
  exact .sort (whTyAL_of_hasTy ⟨.sort Γ l⟩) (whTyAL_of_hasTy ⟨.sort Γ l'⟩) hk hl
    (tyConvAL_sorts Γ hl hOK)

theorem LREqAL_sort_refl (Γ : LCtxA) {l : Level} (hk : ht ρ₀ l < k) :
    LREqAL E n σ N K ρ₀ k Γ (.sort l) (.sort l) :=
  LREqAL_sorts Γ hk (eqNA_refl l) (Or.inl rfl)

theorem LRTyAL_sort_valid (Γ : LCtxA) {l : Level} (hk : ht ρ₀ l < k) :
    ∃ R, LRTyAL E n σ N K ρ₀ k Γ (.sort l) R := by
  rw [LRTyAL_eq]
  cases hz : isZero l with
  | false => exact ⟨_, .sortT (whTyAL_of_hasTy ⟨.sort Γ l⟩) hz hk⟩
  | true => exact ⟨_, .sortP (whTyAL_of_hasTy ⟨.sort Γ l⟩) hz⟩

theorem LRRelAL_sorts_refl (Γ : LCtxA) {l : Level} (hk : ht ρ₀ (.succ l) < k)
    (hl : evalTotal σ (.succ l) ≤ N) :
    LRRelAL E n σ N K ρ₀ k Γ (.sort (.succ l)) (.sort l) (.sort l) := by
  have hk' : ht ρ₀ l < ht ρ₀ (.succ l) := by rw [ht_succ]; exact Nat.lt_succ_self _
  have ht : HasTyAL E n σ N K Γ (.sort l) (.sort (.succ l)) :=
    ⟨⟨.sort Γ l⟩, ⟨.sort (eraseCtx Γ) l, hl⟩⟩
  refine ⟨_, by rw [LRTyAL_eq]; exact .sortT (whTyAL_of_hasTy ⟨.sort Γ (.succ l)⟩) (isZero_succ l) hk, ?_⟩
  exact ⟨LREqAL_sort_refl Γ hk', LRTyAL_sort_valid Γ hk', LRTyAL_sort_valid Γ hk',
    ht, ht, convAL_refl ht⟩

theorem LRRelAL_sorts (Γ : LCtxA) {l l' : Level} (hk : ht ρ₀ (.succ l) < k)
    (hl : eqN l l') (hl1 : evalTotal σ (.succ l) ≤ N) (hl2 : evalTotal σ (.succ l') ≤ N)
    (hOK : SortEqOK σ N (.succ l) (.succ l')) :
    LRRelAL E n σ N K ρ₀ k Γ (.sort (.succ l)) (.sort l) (.sort l') := by
  have hk' : ht ρ₀ l < ht ρ₀ (.succ l) := by rw [ht_succ]; exact Nat.lt_succ_self _
  have hk'' : ht ρ₀ l' < ht ρ₀ (.succ l) := by rw [← ht_of_eqN hl]; exact hk'
  have ht1 : HasTyAL E n σ N K Γ (.sort l) (.sort (.succ l)) :=
    ⟨⟨.sort Γ l⟩, ⟨.sort (eraseCtx Γ) l, hl1⟩⟩
  have ht2_0 : HasTyAL E n σ N K Γ (.sort l') (.sort (.succ l')) :=
    ⟨⟨.sort Γ l'⟩, ⟨.sort (eraseCtx Γ) l', hl2⟩⟩
  have ht2 : HasTyAL E n σ N K Γ (.sort l') (.sort (.succ l)) :=
    hasTyAL_of_tyConvAL ht2_0 (tyConvAL_sorts Γ (eqNA_succ (eqNA_symm hl)) hOK.symm)
  have hc : ConvAL E n σ N K Γ (.sort l) (.sort l') (.sort (.succ l)) :=
    ⟨⟨.sorts Γ l l' hl⟩, ⟨.sorts (eraseCtx Γ) l l' hl, hl1⟩⟩
  refine ⟨_, by rw [LRTyAL_eq]; exact .sortT (whTyAL_of_hasTy ⟨.sort Γ (.succ l)⟩) (isZero_succ l) hk, ?_⟩
  exact ⟨LREqAL_sorts Γ hk' hl (Or.inr ⟨hl1, hl2⟩),
    LRTyAL_sort_valid Γ hk', LRTyAL_sort_valid Γ hk'', ht1, ht2, hc⟩

/-! ### §4.2 Valid pairs of substitutions (`ValidSubstAL`) -/

def ValidSubstAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (k : Nat) (Δ : LCtxA) (s s' : SubstA) (Γ : LCtxA) : Prop :=
  (∀ i A, lookupTypeA Γ i = some A →
    LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A) ∧
    LRRelAL E n σ N K ρ₀ k Δ (substA s A) (s i) (s' i)) ∧
  (∀ i A v, lookupTypeA Γ i = some A → lookupValueA Γ i = some v →
    LRRelAL E n σ N K ρ₀ k Δ (substA s A) (s i) (substA s v) ∧
    LRRelAL E n σ N K ρ₀ k Δ (substA s A) (substA s v) (substA s' v))

theorem ValidSubstAL_mono {j j' : Nat} (hjj : j ≤ j') {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA}
    (h : ValidSubstAL E n σ N K ρ₀ j Δ s s' Γ) : ValidSubstAL E n σ N K ρ₀ j' Δ s s' Γ :=
  ⟨fun i A hA => ⟨LREqAL_mono hjj (h.1 i A hA).1, LRRelAL_mono hjj (h.1 i A hA).2⟩,
   fun i A v hA hv => ⟨LRRelAL_mono hjj (h.2 i A v hA hv).1, LRRelAL_mono hjj (h.2 i A v hA hv).2⟩⟩

theorem ValidSubstAL_symm {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA}
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ) : ValidSubstAL E n σ N K ρ₀ k Δ s' s Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    exact ⟨LREqAL_symm he, LRRelAL_transport' he (LRRelAL_symm hr)⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    obtain ⟨hv1, hv2⟩ := h.2 i A v hA hv
    have h1 : LRRelAL E n σ N K ρ₀ k Δ (substA s A) (s' i) (substA s' v) :=
      LRRelAL_trans (LRRelAL_symm hr) (LRRelAL_trans hv1 hv2)
    exact ⟨LRRelAL_transport' he h1, LRRelAL_transport' he (LRRelAL_symm hv2)⟩

theorem ValidSubstAL_refl_left {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA}
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ) : ValidSubstAL E n σ N K ρ₀ k Δ s s Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    exact ⟨LREqAL_trans he (LREqAL_symm he), LRRelAL_refl_left hr⟩
  · obtain ⟨hv1, hv2⟩ := h.2 i A v hA hv
    exact ⟨hv1, LRRelAL_refl_left hv2⟩

theorem ValidSubstAL_refl_right {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA}
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ) : ValidSubstAL E n σ N K ρ₀ k Δ s' s' Γ :=
  ValidSubstAL_refl_left (ValidSubstAL_symm h)

theorem ValidSubstAL_nil (Δ : LCtxA) (s s' : SubstA) : ValidSubstAL E n σ N K ρ₀ k Δ s s' [] :=
  ⟨fun i _ h => by cases i <;> simp [lookupTypeA] at h,
   fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h⟩

theorem ValidSubstAL_cons {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA} {A a a' : ExprA}
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (he : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A))
    (ha : LRRelAL E n σ N K ρ₀ k Δ (substA s A) a a') :
    ValidSubstAL E n σ N K ρ₀ k Δ (SubstA.cons a s) (SubstA.cons a' s') (.assumption A :: Γ) := by
  refine ⟨fun i B hB => ?_, fun i B v hB hv => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_assumption] at hB
        cases hB
        simp only [substA_cons_liftA]
        exact ⟨he, ha⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            simp only [substA_cons_liftA]
            exact h.1 i A' hΓ
  · cases i with
    | zero => rw [lookupValueA_cons_zero_assumption] at hv; cases hv
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hv
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hv; cases hv
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hv
              cases hB; cases hv
              simp only [substA_cons_liftA]
              exact h.2 i A' v' hΓ hΓv

theorem ValidSubstAL_consLet {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA} {A v : ExprA}
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (he : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A))
    (hv : LRRelAL E n σ N K ρ₀ k Δ (substA s A) (substA s v) (substA s' v)) :
    ValidSubstAL E n σ N K ρ₀ k Δ (SubstA.cons (substA s v) s) (SubstA.cons (substA s' v) s')
      (.letBinding A v :: Γ) := by
  refine ⟨fun i B hB => ?_, fun i B w hB hw => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        cases hB
        simp only [substA_cons_liftA]
        exact ⟨he, hv⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            simp only [substA_cons_liftA]
            exact h.1 i A' hΓ
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        rw [lookupValueA_cons_zero_let] at hw
        cases hB; cases hw
        simp only [substA_cons_liftA]
        exact ⟨LRRelAL_refl_left hv, hv⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hw
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hw; cases hw
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hw
              cases hB; cases hw
              simp only [substA_cons_liftA]
              exact h.2 i A' v' hΓ hΓv

theorem ValidSubstAL_consLet' {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA} {A v a' : ExprA}
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (he : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A))
    (ha : LRRelAL E n σ N K ρ₀ k Δ (substA s A) (substA s v) a')
    (hv : LRRelAL E n σ N K ρ₀ k Δ (substA s A) (substA s v) (substA s' v)) :
    ValidSubstAL E n σ N K ρ₀ k Δ (SubstA.cons (substA s v) s) (SubstA.cons a' s') (.letBinding A v :: Γ) := by
  refine ⟨fun i B hB => ?_, fun i B w hB hw => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        cases hB
        simp only [substA_cons_liftA]
        exact ⟨he, ha⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            simp only [substA_cons_liftA]
            exact h.1 i A' hΓ
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        rw [lookupValueA_cons_zero_let] at hw
        cases hB; cases hw
        simp only [substA_cons_liftA]
        exact ⟨LRRelAL_refl_left hv, hv⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hw
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hw; cases hw
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hw
              cases hB; cases hw
              simp only [substA_cons_liftA]
              exact h.2 i A' v' hΓ hΓv

theorem ValidSubstAL_wk (hE : EnvClosedA E) {Δ : LCtxA}
    {s s' : SubstA} {Γ : LCtxA} (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ) (ρ : WkSpecA)
    (hρ : WkOkA E noIotaA n ρ Δ) :
    ValidSubstAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (fun i => wkExprA ρ (s i)) (fun i => wkExprA ρ (s' i)) Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · obtain ⟨he, hr⟩ := h.1 i A hA
    have he' := LREqAL_wk hE he ρ hρ
    have hr' := LRRelAL_wk hE hr ρ hρ
    simp only [wkExprA_substA] at he' hr'
    exact ⟨he', hr'⟩
  · obtain ⟨h1, h2⟩ := h.2 i A v hA hv
    have h1' := LRRelAL_wk hE h1 ρ hρ
    have h2' := LRRelAL_wk hE h2 ρ hρ
    simp only [wkExprA_substA] at h1' h2'
    exact ⟨h1', h2'⟩

theorem ValidSubstAL_upConv (hE : EnvClosedA E)
    {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA} {A D : ExprA}
    (hΔD : Nonempty (CtxWfA E noIotaA n (.assumption D :: Δ)))
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (he : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A))
    (hvA : ∃ R, LRTyAL E n σ N K ρ₀ k Δ (substA s A) R)
    (hD : TyConvAL E n σ N K Δ D (substA s A)) :
    ValidSubstAL E n σ N K ρ₀ k (.assumption D :: Δ) s.up s'.up (.assumption A :: Γ) := by
  have hρ : WkOkA E noIotaA n [(.assumption D, 0)] Δ := wkOkA_push _ Δ hΔD
  have hw := ValidSubstAL_wk hE h [(.assumption D, 0)] hρ
  have he' := LREqAL_wk hE he _ hρ
  have hD' := tyConvAL_wk hE Δ [(.assumption D, 0)] hρ.1 hD
  simp only [wkExprA_push, wkCtxA_push] at hw he' hD'
  have hv' : ∃ R, LRTyAL E n σ N K ρ₀ k (.assumption D :: Δ) (liftA 0 1 (substA s A)) R :=
    hvA.elim fun R hR => (LRTyAL_wk hE hR _ hρ).elim fun R' hR' => ⟨R', hR'.1⟩
  have ht0_D : HasTyAL E n σ N K (.assumption D :: Δ) (.bvar 0) (liftA 0 1 D) :=
    ⟨hΔD.elim fun c => match c with
      | .assumption _ t =>
          ⟨.bvar (.assumption D :: Δ) 0 (liftA 0 1 D) _ rfl
            (hasTyA_wk hE noIotaA_lift Δ [(.assumption D, 0)] hρ.1 t)⟩,
     ⟨.bvar (.assumption (erase D) :: eraseCtx Δ) 0 (erase (liftA 0 1 D))
        (by simp [lookupType, erase_liftA]), by simp only [LOKt]⟩⟩
  have ht0 : HasTyAL E n σ N K (.assumption D :: Δ) (.bvar 0) (liftA 0 1 (substA s A)) :=
    hasTyAL_of_tyConvAL ht0_D hD'
  refine ⟨fun i B hB => ?_, fun i B v hB hv => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_assumption] at hB
        cases hB
        simp only [substA_up_liftA]
        exact ⟨he', LRRelAL_bvar hE rfl hv' ht0⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            have := hw.1 i A' hΓ
            simp only [substA_up_liftA, liftA_substA, SubstA.up_succ]
            exact this
  · cases i with
    | zero => rw [lookupValueA_cons_zero_assumption] at hv; cases hv
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hv
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hv; cases hv
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hv
              cases hB; cases hv
              have := hw.2 i A' v' hΓ hΓv
              simp only [substA_up_liftA, liftA_substA, SubstA.up_succ]
              exact this

theorem ValidSubstAL_up (hE : EnvClosedA E)
    {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA} {A : ExprA} {u : Level}
    (hΔ : Nonempty (CtxWfA E noIotaA n Δ))
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (he : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A))
    (hvA : ∃ R, LRTyAL E n σ N K ρ₀ k Δ (substA s A) R)
    (htA : Nonempty (HasTyA E noIotaA n Δ (substA s A) (.sort u))) :
    ValidSubstAL E n σ N K ρ₀ k (.assumption (substA s A) :: Δ) s.up s'.up (.assumption A :: Γ) :=
  ValidSubstAL_upConv hE (hΔ.elim fun c => htA.elim fun t => ⟨.assumption c t⟩) h he hvA
    (tyConvAL_refl _ _)

theorem ValidSubstAL_up' (hE : EnvClosedA E)
    {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA} {A D : ExprA} {u : Level}
    (hΔ : Nonempty (CtxWfA E noIotaA n Δ))
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (he : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A))
    (heD : LREqAL E n σ N K ρ₀ k Δ D (substA s A))
    (hvD : ∃ R, LRTyAL E n σ N K ρ₀ k Δ D R)
    (htD : Nonempty (HasTyA E noIotaA n Δ D (.sort u))) :
    ValidSubstAL E n σ N K ρ₀ k (.assumption D :: Δ) s.up s'.up (.assumption A :: Γ) :=
  ValidSubstAL_upConv hE (hΔ.elim fun c => htD.elim fun t => ⟨.assumption c t⟩) h he
    (LREqAL_valid heD hvD) (LREqAL_tyConv heD)

/-- Generalized `ValidSubstAL` under a let-binding `.letBinding A₀ v₀ :: Δ` where `A₀` is `LREqAL`-equal
    to `substA s A` and `v₀` is `LRRelAL`-related to `substA s v` at `substA s A`. -/
theorem ValidSubstAL_upLet_gen (hE : EnvClosedA E)
    {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA} {A v A₀ v₀ : ExprA} {u : Level}
    (hΔ : Nonempty (CtxWfA E noIotaA n Δ))
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (he : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A))
    (heA₀ : LREqAL E n σ N K ρ₀ k Δ (substA s A) A₀)
    (hv₀ : LRRelAL E n σ N K ρ₀ k Δ (substA s A) (substA s v) v₀)
    (hv : LRRelAL E n σ N K ρ₀ k Δ (substA s A) (substA s v) (substA s' v))
    (htA₀ : Nonempty (HasTyA E noIotaA n Δ A₀ (.sort u))) :
    ValidSubstAL E n σ N K ρ₀ k (.letBinding A₀ v₀ :: Δ) s.up s'.up
      (.letBinding A v :: Γ) := by
  have htv₀ : HasTyAL E n σ N K Δ v₀ A₀ := (LRRelAL_hasTy (LRRelAL_transport' heA₀ hv₀)).2
  have hΔ' : Nonempty (CtxWfA E noIotaA n (.letBinding A₀ v₀ :: Δ)) :=
    hΔ.elim fun c => htA₀.elim fun t => htv₀.1.elim fun tv => ⟨.letBinding c t tv⟩
  have hρ : WkOkA E noIotaA n [(.letBinding A₀ v₀, 0)] Δ := wkOkA_push _ Δ hΔ'
  have hw := ValidSubstAL_wk hE h [(.letBinding A₀ v₀, 0)] hρ
  have he' := LREqAL_wk hE he _ hρ
  have heA₀' := LREqAL_wk hE heA₀ _ hρ
  have hv₀' := LRRelAL_wk hE hv₀ _ hρ
  have hv' := LRRelAL_wk hE hv _ hρ
  simp only [wkExprA_push, wkCtxA_push] at hw he' heA₀' hv₀' hv'
  have htv₀_w : HasTyAL E n σ N K (.letBinding A₀ v₀ :: Δ) (liftA 0 1 v₀) (liftA 0 1 A₀) :=
    hasTyAL_wk hE Δ [(.letBinding A₀ v₀, 0)] hρ.1 htv₀
  have ht0_A₀ : HasTyAL E n σ N K (.letBinding A₀ v₀ :: Δ) (.bvar 0) (liftA 0 1 A₀) :=
    ⟨htA₀.elim fun t => ⟨.bvar _ 0 _ u rfl (hasTyA_wk hE noIotaA_lift Δ _ hρ.1 t)⟩,
     ⟨.bvar (.letBinding (erase A₀) (erase v₀) :: eraseCtx Δ) 0 (erase (liftA 0 1 A₀))
        (by simp [lookupType, erase_liftA]), by simp only [LOKt]⟩⟩
  have hc0_A₀ : ConvAL E n σ N K (.letBinding A₀ v₀ :: Δ) (.bvar 0) (liftA 0 1 v₀) (liftA 0 1 A₀) :=
    ⟨htv₀_w.1.elim fun tv => ⟨.zetaLocal _ 0 _ _ rfl rfl tv⟩,
     htv₀_w.2.elim fun dtv hdtv =>
       ⟨.zetaLocal (.letBinding (erase A₀) (erase v₀) :: eraseCtx Δ) 0 (erase (liftA 0 1 A₀))
          (erase (liftA 0 1 v₀)) (by simp [lookupValue, erase_liftA]) (by simp [lookupType, erase_liftA]) dtv,
        by simpa only [LOKc] using hdtv⟩⟩
  have hs_A₀ : StepAtAL E n σ N K (.letBinding A₀ v₀ :: Δ) (.bvar 0) (liftA 0 1 v₀) (liftA 0 1 A₀) :=
    ⟨⟨ht0_A₀.1, htv₀_w.1.elim fun tv => ⟨.zetaLocal _ 0 _ _ rfl rfl tv⟩⟩, ht0_A₀, hc0_A₀⟩
  have hs : StepAtAL E n σ N K (.letBinding A₀ v₀ :: Δ) (.bvar 0) (liftA 0 1 v₀) (liftA 0 1 (substA s A)) :=
    stepAtAL_tyConv hs_A₀ (LREqAL_tyConv (LREqAL_symm heA₀'))
  have h0_v₀ : LRRelAL E n σ N K ρ₀ k (.letBinding A₀ v₀ :: Δ) (liftA 0 1 (substA s A))
      (.bvar 0) (liftA 0 1 v₀) :=
    LRRelAL_expand_left hE hs (LRRelAL_symm (LRRelAL_refl_left (LRRelAL_symm hv₀')))
  have h0_sv : LRRelAL E n σ N K ρ₀ k (.letBinding A₀ v₀ :: Δ) (liftA 0 1 (substA s A))
      (.bvar 0) (liftA 0 1 (substA s v)) :=
    LRRelAL_expand_left hE hs (LRRelAL_symm hv₀')
  refine ⟨fun i B hB => ?_, fun i B w hB hw_val => ?_⟩
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        cases hB
        simp only [substA_up_liftA]
        exact ⟨he', LRRelAL_expand_right hE hs h0_v₀⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
            rw [hΓ, Option.map_some'] at hB
            cases hB
            have := hw.1 i A' hΓ
            simp only [substA_up_liftA, liftA_substA, SubstA.up_succ]
            exact this
  · cases i with
    | zero =>
        rw [lookupTypeA_cons_zero_let] at hB
        rw [lookupValueA_cons_zero_let] at hw_val
        cases hB; cases hw_val
        simp only [substA_up_liftA]
        exact ⟨h0_sv, hv'⟩
    | succ i =>
        rw [lookupTypeA_cons_succ] at hB
        rw [lookupValueA_cons_succ] at hw_val
        cases hΓ : lookupTypeA Γ i with
        | none => rw [hΓ] at hB; cases hB
        | some A' =>
          cases hΓv : lookupValueA Γ i with
          | none => rw [hΓv] at hw_val; cases hw_val
          | some v' =>
              rw [hΓ, Option.map_some'] at hB
              rw [hΓv, Option.map_some'] at hw_val
              cases hB; cases hw_val
              have := hw.2 i A' v' hΓ hΓv
              simp only [substA_up_liftA, liftA_substA, SubstA.up_succ]
              exact this

theorem ValidSubstAL_upLet (hE : EnvClosedA E)
    {Δ : LCtxA} {s s' : SubstA} {Γ : LCtxA} {A v : ExprA} {u : Level}
    (hΔ : Nonempty (CtxWfA E noIotaA n Δ))
    (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (he : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A))
    (hv : LRRelAL E n σ N K ρ₀ k Δ (substA s A) (substA s v) (substA s' v))
    (htA : Nonempty (HasTyA E noIotaA n Δ (substA s A) (.sort u))) :
    ValidSubstAL E n σ N K ρ₀ k (.letBinding (substA s A) (substA s v) :: Δ) s.up s'.up
      (.letBinding A v :: Γ) :=
  ValidSubstAL_upLet_gen hE hΔ h he (LREqAL_trans he (LREqAL_symm he)) (LRRelAL_refl_left hv) hv htA

theorem ValidSubstAL_ext {Δ Γ : LCtxA} {s τ s' τ' : SubstA}
    (hs : ∀ i, s i = τ i) (hs' : ∀ i, s' i = τ' i) (h : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ) :
    ValidSubstAL E n σ N K ρ₀ k Δ τ τ' Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · have := h.1 i A hA
    rw [substA_ext hs A, substA_ext hs' A, hs i, hs' i] at this
    exact this
  · have := h.2 i A v hA hv
    rw [substA_ext hs A, substA_ext hs v, substA_ext hs' v, hs i] at this
    exact this

/-! ### §4.3 Π-clause helpers and β/η helpers -/

theorem hasTyT_pi_inv_lok {E₀ : ResolvedEnv} :
    ∀ {Γ : LCtx} {D C T : Expr Nat} (d : HasTyT E₀ n Γ (.pi D C) T),
      LOKt σ N K d →
      ∃ u v : Level,
        (∃ dD : HasTyT E₀ n Γ D (.sort u), LOKt σ N K dD) ∧
        (∃ dC : HasTyT E₀ n (.assumption D :: Γ) C (.sort v), LOKt σ N K dC)
  | _, _, _, _, .pi _ _ u _ v hA hB, hd => by
      simp only [LOKt] at hd
      exact ⟨u, v, ⟨hA, hd.2.2.1⟩, ⟨hB, hd.2.2.2⟩⟩
  | _, _, _, _, .conv _ _ _ _ _ h _, hd => by
      simp only [LOKt] at hd
      exact hasTyT_pi_inv_lok h hd.1

theorem hasTyT_lam_inv_lok {E₀ : ResolvedEnv} :
    ∀ {Γ : LCtx} {D b T : Expr Nat} (d : HasTyT E₀ n Γ (.lam D b) T),
      LOKt σ N K d →
      ∃ u : Level, ∃ dD : HasTyT E₀ n Γ D (.sort u), LOKt σ N K dD
  | _, _, _, _, .lam _ _ u _ _ hA _, hd => by
      simp only [LOKt] at hd
      exact ⟨u, hA, hd.1⟩
  | _, _, _, _, .conv _ _ _ _ _ h _, hd => by
      simp only [LOKt] at hd
      exact hasTyT_lam_inv_lok h hd.1

theorem tyKAL_pi_inv {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    {R : ExprA → ExprA → Prop}
    (h : TyKAL E n σ N K ρ₀ k LE LT Γ (.pi D u C v) R)
    (hnp : ¬ IsPropTy E noIotaA Γ (.pi D u C v)) :
    ∃ (RD : WkSpecA → ExprA → ExprA → Prop) (RC : WkSpecA → ExprA → ExprA → ExprA → Prop),
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ)) ∧
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a)) ∧
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) ∧
      R = fun f g =>
        (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
          RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
        HasTyAL E n σ N K Γ f (.pi D u C v) ∧ HasTyAL E n σ N K Γ g (.pi D u C v) ∧
        ConvAL E n σ N K Γ f g (.pi D u C v) := by
  cases h with
  | prop hA hn hP =>
      have e := whTyA_det hA.1 (whTyA_self hA.1) hn (hStepFnA_pi E noIotaA.fn Γ D u C v)
      subst e
      exact absurd hP hnp
  | sortT hA _ _ =>
      have e := whTyA_det hA.1 (whTyA_self hA.1) (hStepFnA_sort E noIotaA.fn Γ _) (hStepFnA_pi E noIotaA.fn Γ D u C v)
      cases e
  | sortP hA _ =>
      have e := whTyA_det hA.1 (whTyA_self hA.1) (hStepFnA_sort E noIotaA.fn Γ _) (hStepFnA_pi E noIotaA.fn Γ D u C v)
      cases e
  | pi hA _ _ _ RD hD RC hC hCeq =>
      have e := whTyA_det hA.1 (whTyA_self hA.1) (hStepFnA_pi E noIotaA.fn Γ _ _ _ _)
        (hStepFnA_pi E noIotaA.fn Γ D u C v)
      cases e
      exact ⟨RD, RC, hD, hC, hCeq, rfl⟩
  | stuck hA hNC =>
      have e := whTyA_det hA.1 (whTyA_self hA.1) hNC.1 (hStepFnA_pi E noIotaA.fn Γ D u C v)
      subst e
      exact (stuckA_not_pi hNC).elim

theorem LRRelAL_pi_elim {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    {f g : ExprA} (h : LRRelAL E n σ N K ρ₀ k Γ (.pi D u C v) f g)
    (hnp : ¬ IsPropTy E noIotaA Γ (.pi D u C v)) :
    ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA,
      LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ D) a a' →
      LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a') := by
  obtain ⟨R, hR, hfg⟩ := h
  rw [LRTyAL_eq] at hR
  obtain ⟨RD, RC, hD, hC, _, e⟩ := tyKAL_pi_inv hR hnp
  subst e
  intro ρ hρ a a' hr
  have hr' : RD ρ a a' := hr.at (by rw [LRTyAL_eq]; exact hD ρ hρ)
  exact ⟨RC ρ a, by rw [LRTyAL_eq]; exact hC ρ hρ a a' hr', hfg.1 ρ hρ a a' hr'⟩

theorem piEqAL_of_data {Δ : LCtxA} {D C D' C' : ExprA} {u v u' v' : Level}
    (hu : eqN u u') (hv : eqN v v')
    (tD : HasTyA E noIotaA n Δ D (.sort u)) (tC : HasTyA E noIotaA n (.assumption D :: Δ) C (.sort v))
    (tD' : HasTyA E noIotaA n Δ D' (.sort u')) (tC' : HasTyA E noIotaA n (.assumption D' :: Δ) C' (.sort v'))
    (hDeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
      LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) (wkExprA ρ D'))
    (hDv : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∃ R, LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) R)
    (hCeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a : ExprA,
      LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a a →
      LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
    (hc : TyConvAL E n σ N K Δ (.pi D u C v) (.pi D' u' C' v')) :
    LREqAL E n σ N K ρ₀ k Δ (.pi D u C v) (.pi D' u' C' v') := by
  rw [LREqAL_eq]
  refine .pi (whTyAL_of_hasTy ⟨.pi Δ D u C v tD tC⟩) (whTyAL_of_hasTy ⟨.pi Δ D' u' C' v' tD' tC'⟩)
    hu hv ⟨tD⟩ ⟨tC⟩ ⟨tD'⟩ ⟨tC'⟩
    (fun ρ a b => LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a b)
    (fun ρ hρ => ?_) (fun ρ hρ => ?_) (fun ρ hρ a a' hr => ?_) hc
  · have := LRTyAL_canon' (hDv ρ hρ); rw [LRTyAL_eq] at this; exact this
  · have := hDeq ρ hρ; rw [LREqAL_eq] at this; exact this
  · have := hCeq ρ hρ a (LRRelAL_refl_left hr); rw [LREqAL_eq] at this; exact this

theorem piTyAL_of_data {Δ : LCtxA} {D C : ExprA} {u v : Level} (hz : isZero v = false)
    (tD : HasTyA E noIotaA n Δ D (.sort u)) (tC : HasTyA E noIotaA n (.assumption D :: Δ) C (.sort v))
    (hDv : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∃ R, LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) R)
    (hCv : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
      LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a a' →
      ∃ R, LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) R)
    (hCeq : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
      LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a a' →
      LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) :
    LRTyAL E n σ N K ρ₀ k Δ (.pi D u C v) (fun f g =>
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
        LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a a' →
        LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      HasTyAL E n σ N K Δ f (.pi D u C v) ∧ HasTyAL E n σ N K Δ g (.pi D u C v) ∧
      ConvAL E n σ N K Δ f g (.pi D u C v)) := by
  rw [LRTyAL_eq]
  refine .pi (whTyAL_of_hasTy ⟨.pi Δ D u C v tD tC⟩) (fun h => ?_) ⟨tD⟩ ⟨tC⟩
    (fun ρ a b => LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ D) a b) (fun ρ hρ => ?_)
    (fun ρ a x y => LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) x y)
    (fun ρ hρ a a' hr => ?_) (fun ρ hρ a a' hr => ?_)
  · rw [(isPropTy_pi_iff E noIotaA Δ D u C v).1 h] at hz; cases hz
  · have := LRTyAL_canon' (hDv ρ hρ); rw [LRTyAL_eq] at this; exact this
  · have := LRTyAL_canon' (hCv ρ hρ a a' hr); rw [LRTyAL_eq] at this; exact this
  · have := hCeq ρ hρ a a' hr; rw [LREqAL_eq] at this; exact this

theorem fundArm_sort_wkAL (hE : EnvClosedA E)
    {k₀ : Nat} {Γ : LCtxA} {A A' : ExprA} {u : Level}
    (h : ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (s s' : SubstA), Nonempty (CtxWfA E noIotaA n Δ) →
      ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ →
      LREqAL E n σ N K ρ₀ k Δ (substA s (.sort u)) (substA s' (.sort u)) ∧
      LRRelAL E n σ N K ρ₀ k Δ (substA s (.sort u)) (substA s A) (substA s' A'))
    (hk : k₀ ≤ k) {Δ : LCtxA} {s s' : SubstA} (hs : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (ρ : WkSpecA) (hρ : WkOkA E noIotaA n ρ Δ) :
    LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (.sort u) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A')) := by
  have := (h k hk _ _ _ hρ.2 (ValidSubstAL_wk hE hs ρ hρ)).2
  simp only [wkExprA_substA]
  exact this

theorem fundArm_cons_wkAL (hE : EnvClosedA E)
    {k₀ : Nat} {Γ : LCtxA} {A e e' B : ExprA}
    (h : ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (s s' : SubstA), Nonempty (CtxWfA E noIotaA n Δ) →
      ValidSubstAL E n σ N K ρ₀ k Δ s s' (.assumption A :: Γ) →
      LREqAL E n σ N K ρ₀ k Δ (substA s B) (substA s' B) ∧
      LRRelAL E n σ N K ρ₀ k Δ (substA s B) (substA s e) (substA s' e'))
    (hk : k₀ ≤ k) {Δ : LCtxA} {s s' : SubstA} (hs : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (ρ : WkSpecA) (hρ : WkOkA E noIotaA n ρ Δ)
    (he : LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A)))
    {a a' : ExprA} (ha : LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) a a') :
    LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
      (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s'.up B))) ∧
    LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up e)))
      (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s'.up e'))) := by
  rw [wkExprA_substA, wkExprA_substA] at he
  rw [wkExprA_substA] at ha
  have hv := ValidSubstAL_cons (ValidSubstAL_wk hE hs ρ hρ) he ha
  have := h k hk _ _ _ hρ.2 hv
  simp only [wk_ub_subst_up]
  exact this

theorem fundArm_cons_wk_sortAL (hE : EnvClosedA E)
    {k₀ : Nat} {Γ : LCtxA} {A B B' : ExprA} {v : Level}
    (h : ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (s s' : SubstA), Nonempty (CtxWfA E noIotaA n Δ) →
      ValidSubstAL E n σ N K ρ₀ k Δ s s' (.assumption A :: Γ) →
      LREqAL E n σ N K ρ₀ k Δ (substA s (.sort v)) (substA s' (.sort v)) ∧
      LRRelAL E n σ N K ρ₀ k Δ (substA s (.sort v)) (substA s B) (substA s' B'))
    (hk : k₀ ≤ k) {Δ : LCtxA} {s s' : SubstA} (hs : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (ρ : WkSpecA) (hρ : WkOkA E noIotaA n ρ Δ)
    (he : LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A)))
    {a a' : ExprA} (ha : LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) a a') :
    LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (.sort v)
      (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
      (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s'.up B'))) := by
  rw [wkExprA_substA, wkExprA_substA] at he
  rw [wkExprA_substA] at ha
  have hv := ValidSubstAL_cons (ValidSubstAL_wk hE hs ρ hρ) he ha
  have := (h k hk _ _ _ hρ.2 hv).2
  simp only [wk_ub_subst_up]
  exact this

theorem propEqAL_codom_of_fund (hE : EnvClosedA E)
    {k₀ : Nat} {Γ : LCtxA} {A B B' : ExprA} {v : Level} (hz : isZero v = true)
    (hB : ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (s s' : SubstA), Nonempty (CtxWfA E noIotaA n Δ) →
      ValidSubstAL E n σ N K ρ₀ k Δ s s' (.assumption A :: Γ) →
      LREqAL E n σ N K ρ₀ k Δ (substA s (.sort v)) (substA s' (.sort v)) ∧
      LRRelAL E n σ N K ρ₀ k Δ (substA s (.sort v)) (substA s B) (substA s' B'))
    (hk : k₀ ≤ k) {Δ : LCtxA} {s s' : SubstA} (hs : ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ)
    (heA : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A))
    (hvA : ∃ R, LRTyAL E n σ N K ρ₀ k Δ (substA s A) R) :
    ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ D₀ : ExprA,
      Nonempty (CtxWfA E noIotaA n (.assumption D₀ :: wkCtxA ρ Δ)) →
      TyConvAL E n σ N K (wkCtxA ρ Δ) D₀ (wkExprA ρ (substA s A)) →
      PropEqAL E n σ N K (.assumption D₀ :: wkCtxA ρ Δ)
        (wkExprA (WkSpecA.ub ρ) (substA s.up B)) (wkExprA (WkSpecA.ub ρ) (substA s'.up B')) := by
  intro ρ hρ D₀ hctx hD₀
  have hsρ := ValidSubstAL_wk hE hs ρ hρ
  have heAρ := LREqAL_wk hE heA ρ hρ
  have hvAρ : ∃ R, LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) R :=
    hvA.elim fun R hR => (LRTyAL_wk hE hR ρ hρ).elim fun R' hR' => ⟨R', hR'.1⟩
  rw [wkExprA_substA, wkExprA_substA] at heAρ
  rw [wkExprA_substA] at hvAρ hD₀
  have hup := ValidSubstAL_upConv hE hctx hsρ heAρ hvAρ hD₀
  have hBr := (hB k hk _ _ _ hctx hup).2
  rw [wkExprA_ub_substA_up, wkExprA_ub_substA_up]
  exact (LRRelAL_sortP_elim hz hBr).2.2.2.2.2

theorem stepAtAL_beta_wk (hE : EnvClosedA E) {Δ : LCtxA} {D : ExprA} {u : Level}
    {b C : ExprA} {v w : Level}
    (tD : HasTyAL E n σ N K Δ D (.sort u))
    (tC : Nonempty (HasTyA E noIotaA n (.assumption D :: Δ) C (.sort v)))
    (tb : HasTyAL E n σ N K (.assumption D :: Δ) b C) (ρ : WkSpecA) (hρ : WkOkA E noIotaA n ρ Δ) {x : ExprA}
    (tx : HasTyAL E n σ N K (wkCtxA ρ Δ) x (wkExprA ρ D))
    (tred : HasTyAL E n σ N K (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) b))
      (instantiate0A x (wkExprA (WkSpecA.ub ρ) C)))
    (tTy : Nonempty (HasTyA E noIotaA n (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) C)) (.sort w))) :
    StepAtAL E n σ N K (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam D u b)) x)
      (instantiate0A x (wkExprA (WkSpecA.ub ρ) b)) (instantiate0A x (wkExprA (WkSpecA.ub ρ) C)) := by
  have tD' : HasTyAL E n σ N K (wkCtxA ρ Δ) (wkExprA ρ D) (.sort u) := by
    have := hasTyAL_wk hE Δ ρ hρ.1 tD; rwa [wkExprA_sort] at this
  have tb' : HasTyAL E n σ N K (.assumption (wkExprA ρ D) :: wkCtxA ρ Δ) (wkExprA (WkSpecA.ub ρ) b)
      (wkExprA (WkSpecA.ub ρ) C) := by
    have := hasTyAL_wk hE _ (WkSpecA.ub ρ) (WkSpecA.ok_ub ρ _ Δ hρ.1) tb
    rwa [wkCtxA_ub_cons, wkDeclA_assumption] at this
  have hstA : StepAtA E noIotaA n (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam D u b)) x)
      (instantiate0A x (wkExprA (WkSpecA.ub ρ) b)) (instantiate0A x (wkExprA (WkSpecA.ub ρ) C)) :=
    tD.1.elim fun dD => tC.elim fun dC => tb.1.elim fun db => tx.1.elim fun dx =>
      tred.1.elim fun dred => tTy.elim fun dTy =>
        stepAtA_beta_wk hE noIotaA_lift dD dC db ρ hρ dx dred dTy
  refine ⟨hstA, ⟨hstA.1, ?_⟩, ⟨stepAtA_conv hstA, ?_⟩⟩
  · rw [wkExprA_lam_ub]
    obtain ⟨dtD', hdtD'⟩ := tD'.2
    obtain ⟨dtb', hdtb'⟩ := tb'.2
    obtain ⟨dtx, hdtx⟩ := tx.2
    exact ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) C) x).symm
      ⟨.app _ _ _ _ _ (.lam _ _ u _ _ dtD' dtb') dtx,
        by simp only [LOKt]; exact ⟨⟨hdtD', hdtb'⟩, hdtx⟩⟩
  · rw [wkExprA_lam_ub]
    obtain ⟨dtD', hdtD'⟩ := tD'.2
    obtain ⟨dtb', hdtb'⟩ := tb'.2
    obtain ⟨dtx, hdtx⟩ := tx.2
    exact ex_convT_lok_cast rfl rfl
      (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) b) x).symm
      (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) C) x).symm
      ⟨.beta _ _ _ _ _ u dtD' dtb' dtx, by simp only [LOKc]; exact ⟨hdtD', hdtb', hdtx⟩⟩

theorem stepAtAL_beta_wk' (hE : EnvClosedA E) {Δ : LCtxA} {D : ExprA} {u : Level}
    {b C T : ExprA} (tD : Nonempty (HasTyA E noIotaA n Δ D (.sort u)))
    (tlam : HasTyAL E n σ N K Δ (.lam D u b) T)
    (tb : HasTyAL E n σ N K (.assumption D :: Δ) b C)
    (ρ : WkSpecA) (hρ : WkOkA E noIotaA n ρ Δ) {x : ExprA}
    (tx : HasTyAL E n σ N K (wkCtxA ρ Δ) x (wkExprA ρ D))
    (tred : Nonempty (HasTyA E noIotaA n (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) b))
      (instantiate0A x (wkExprA (WkSpecA.ub ρ) C))))
    (tredex : HasTyAL E n σ N K (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam D u b)) x)
      (instantiate0A x (wkExprA (WkSpecA.ub ρ) C))) :
    StepAtAL E n σ N K (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam D u b)) x)
      (instantiate0A x (wkExprA (WkSpecA.ub ρ) b)) (instantiate0A x (wkExprA (WkSpecA.ub ρ) C)) := by
  have tlam' : HasTyAL E n σ N K (wkCtxA ρ Δ) (.lam (wkExprA ρ D) u (wkExprA (WkSpecA.ub ρ) b))
      (wkExprA ρ T) := by
    have := hasTyAL_wk hE Δ ρ hρ.1 tlam; rwa [wkExprA_lam_ub] at this
  have tb' : HasTyAL E n σ N K (.assumption (wkExprA ρ D) :: wkCtxA ρ Δ) (wkExprA (WkSpecA.ub ρ) b)
      (wkExprA (WkSpecA.ub ρ) C) := by
    have := hasTyAL_wk hE _ (WkSpecA.ub ρ) (WkSpecA.ok_ub ρ _ Δ hρ.1) tb
    rwa [wkCtxA_ub_cons, wkDeclA_assumption] at this
  have hstA : StepAtA E noIotaA n (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam D u b)) x)
      (instantiate0A x (wkExprA (WkSpecA.ub ρ) b)) (instantiate0A x (wkExprA (WkSpecA.ub ρ) C)) :=
    tD.elim fun dD => tb.1.elim fun db => tx.1.elim fun dx => tred.elim fun dred =>
      tredex.1.elim fun dredex =>
        stepAtA_beta_wk' hE noIotaA_lift dD db ρ hρ dx dred dredex
  refine ⟨hstA, tredex, ⟨stepAtA_conv hstA, ?_⟩⟩
  rw [wkExprA_lam_ub]
  obtain ⟨dtl, hdtl⟩ := tlam'.2
  obtain ⟨uD, dtD', hdtD'⟩ := hasTyT_lam_inv_lok dtl hdtl
  obtain ⟨dtb', hdtb'⟩ := tb'.2
  obtain ⟨dtx, hdtx⟩ := tx.2
  exact ex_convT_lok_cast rfl rfl
    (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) b) x).symm
    (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) C) x).symm
    ⟨.beta _ _ _ _ _ uD dtD' dtb' dtx, by simp only [LOKc]; exact ⟨hdtD', hdtb', hdtx⟩⟩

theorem hasTyAL_eta_body (hE : EnvClosedA E) {Δ : LCtxA} {f D : ExprA} {u : Level}
    {C : ExprA} {v : Level}
    (tD : Nonempty (HasTyA E noIotaA n Δ D (.sort u)))
    (tC : Nonempty (HasTyA E noIotaA n (.assumption D :: Δ) C (.sort v)))
    (tf : HasTyAL E n σ N K Δ f (.pi D u C v)) :
    HasTyAL E n σ N K (.assumption D :: Δ) (.app (liftA 0 1 f) (.bvar 0)) C := by
  refine ⟨tD.elim fun dD => tC.elim fun dC => tf.1.elim fun df =>
    ⟨hasTyA_eta_body hE noIotaA_lift dD dC df⟩, ?_⟩
  have tf' : HasTyAL E n σ N K (.assumption D :: Δ) (liftA 0 1 f) (.pi (liftA 0 1 D) u (liftA 1 1 C) v) :=
    hasTyAL_weaken hE (.assumption D) (c := 0) (Nat.zero_le _) tf
  obtain ⟨dtf', hdtf'⟩ := tf'.2
  have heq : instantiate0 (.bvar 0) (erase (liftA 1 1 C)) = erase C := by
    change instantiate0 (erase (.bvar 0)) (erase (liftA 1 1 C)) = erase C
    rw [← erase_instantiate0A (liftA 1 1 C) (.bvar 0), instantiate0A_bvar0_liftA]
  exact ex_hasTyT_lok_cast rfl rfl heq
    ⟨.app _ _ _ _ _ dtf' (.bvar _ 0 _ (by simp [lookupType, eraseCtx, eraseDecl, erase_liftA])),
      by simp only [LOKt]; exact ⟨hdtf', trivial⟩⟩

/-! ### §4.4 `FundArmAL`, `EnvSemAL`, `LOKtA` / `LOKcA`, and the 27 arms of `fundAL` -/

def EnvSemClauseAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (r : Nat) (m : CheckedMemberA) : Prop :=
  ∀ ls ls' : List Level, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    LevelsOK σ (K r) ls → LevelsOK σ (K r) ls' →
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E noIotaA n Δ) →
      LRRelAL E n σ N K ρ₀ k Δ (instantiateLevelsA ls m.mtypeA) (.const r ls) (.const r ls')

def EnvSemAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → EnvSemClauseAL E n σ N K ρ₀ r m

theorem emptyEnvA_semAL : EnvSemAL emptyEnvA n σ N K ρ₀ :=
  fun _ _ h => Option.noConfusion h

def FundArmAL (E : ResolvedEnvA) (n : Nat) (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (ρ₀ : Nat → Nat) (Γ : LCtxA) (e e' A : ExprA) : Prop :=
  ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (s s' : SubstA), Nonempty (CtxWfA E noIotaA n Δ) →
    ValidSubstAL E n σ N K ρ₀ k Δ s s' Γ →
    LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A) ∧
    LRRelAL E n σ N K ρ₀ k Δ (substA s A) (substA s e) (substA s' e')

mutual
/-- `LOKt` stage bound on copy typing derivations (`HasTyA E noIotaA n Γ e A`). -/
def LOKtA (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E noIotaA n Γ e A → Prop
  | _, _, _, .sort _ l => evalTotal σ (.succ l) ≤ N
  | _, _, _, .bvar _ _ _ _ _ hA => LOKtA σ N K hA
  | _, _, _, .const _ r ls _ _ _ _ _ hT => LevelsOK σ (K r) ls ∧ LOKtA σ N K hT
  | _, _, _, .pi _ _ u _ v hA hB =>
      evalTotal σ u ≤ N ∧ evalTotal σ v ≤ N ∧ LOKtA σ N K hA ∧ LOKtA σ N K hB
  | _, _, _, .lam _ _ u _ _ v hA hB hbody =>
      evalTotal σ u ≤ N ∧ evalTotal σ v ≤ N ∧ LOKtA σ N K hA ∧ LOKtA σ N K hB ∧ LOKtA σ N K hbody
  | _, _, _, .app _ _ _ _ _ _ _ _ hB hTy hf ha =>
      LOKtA σ N K hB ∧ LOKtA σ N K hTy ∧ LOKtA σ N K hf ∧ LOKtA σ N K ha
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hTy hb =>
      LOKtA σ N K hA ∧ LOKtA σ N K hv ∧ LOKtA σ N K hTy ∧ LOKtA σ N K hb
  | _, _, _, .lit _ _ _ hexp => LOKtA σ N K hexp
  | _, _, _, .conv _ _ _ _ _ _ h hAl _ hB hc =>
      LOKtA σ N K h ∧ LOKtA σ N K hAl ∧ LOKtA σ N K hB ∧ LOKcA σ N K hc

/-- `LOKc` stage bound on copy conversion derivations (`ConvA E noIotaA n Γ a b A`). -/
def LOKcA (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E noIotaA n Γ a b A → Prop
  | _, _, _, _, .refl _ _ _ h => LOKtA σ N K h
  | _, _, _, _, .symm _ _ _ _ h => LOKcA σ N K h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => LOKcA σ N K h1 ∧ LOKcA σ N K h2
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg hred =>
      LOKtA σ N K hA ∧ LOKtA σ N K hbody ∧ LOKtA σ N K harg ∧ LOKtA σ N K hred
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb hred =>
      LOKtA σ N K hA ∧ LOKtA σ N K hv ∧ LOKtA σ N K hb ∧ LOKtA σ N K hred
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => LOKtA σ N K hv
  | _, _, _, _, .delta _ r ls _ _ _ _ _ _ _ hb => LevelsOK σ (K r) ls ∧ LOKtA σ N K hb
  | _, _, _, _, .iota _ _ _ _ _ _ _ => False
  | _, _, _, _, .structIota _ _ _ _ _ _ _ _ _ _ _ _ => False
  | _, _, _, _, .lit _ _ _ hexp => LOKtA σ N K hexp
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 hB hrt =>
      LOKcA σ N K h1 ∧ LOKcA σ N K h2 ∧ LOKtA σ N K hB ∧ LOKtA σ N K hrt
  | _, _, _, _, .lam _ _ _ _ _ _ u u' _ _ hA hb hrt =>
      SortEqOK σ N u u' ∧ LOKcA σ N K hA ∧ LOKcA σ N K hb ∧ LOKtA σ N K hrt
  | _, _, _, _, .pi _ _ _ _ _ u u' v v' _ _ hA hB hrt =>
      evalTotal σ u ≤ N ∧ evalTotal σ v ≤ N ∧
      SortEqOK σ N u u' ∧ SortEqOK σ N v v' ∧
      LOKcA σ N K hA ∧ LOKcA σ N K hB ∧ LOKtA σ N K hrt
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hrt =>
      LOKcA σ N K hA ∧ LOKcA σ N K hv ∧ LOKcA σ N K hb ∧ LOKtA σ N K hrt
  | _, _, _, _, .sorts _ l₁ l₂ _ =>
      evalTotal σ (.succ l₁) ≤ N ∧ evalTotal σ (.succ l₂) ≤ N ∧
      SortEqOK σ N (.succ l₁) (.succ l₂)
  | _, _, _, _, .consts _ r ls ls' _ _ _ _ _ _ hrt =>
      LevelsOK σ (K r) ls ∧ LevelsOK σ (K r) ls' ∧ LOKtA σ N K hrt
  | _, _, _, _, .eta _ _ _ _ _ _ h hrt => LOKtA σ N K h ∧ LOKtA σ N K hrt
  | _, _, _, _, .irr _ _ _ _ hP hp hq =>
      LOKtA σ N K hP ∧ LOKtA σ N K hp ∧ LOKtA σ N K hq
  | _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h hAl _ hA'l _ hA =>
      LOKcA σ N K h ∧ LOKtA σ N K hAl ∧ LOKtA σ N K hA'l ∧ LOKcA σ N K hA
end

def LOKctxA (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtxA} → CtxWfA E noIotaA n Γ → Prop
  | _, .nil => True
  | _, .assumption hΓ hA => LOKctxA σ N K hΓ ∧ LOKtA σ N K hA
  | _, .letBinding hΓ hA hv => LOKctxA σ N K hΓ ∧ LOKtA σ N K hA ∧ LOKtA σ N K hv

theorem hasTyArmSortAL (Γ : LCtxA) (l : Level) (hl : evalTotal σ (.succ l) ≤ N) :
    FundArmAL E n σ N K ρ₀ Γ (.sort l) (.sort l) (.sort (.succ l)) :=
  ⟨ht ρ₀ (.succ l) + 1, fun _ hk Δ _ _ _ _ =>
    ⟨LREqAL_sort_refl Δ hk, LRRelAL_sorts_refl Δ hk hl⟩⟩

theorem convArmSortsAL (Γ : LCtxA) (l₁ l₂ : Level) (h : eqN l₁ l₂)
    (hl1 : evalTotal σ (.succ l₁) ≤ N) (hl2 : evalTotal σ (.succ l₂) ≤ N)
    (hOK : SortEqOK σ N (.succ l₁) (.succ l₂)) :
    FundArmAL E n σ N K ρ₀ Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) :=
  ⟨ht ρ₀ (.succ l₁) + 1, fun _ hk Δ _ _ _ _ =>
    ⟨LREqAL_sort_refl Δ hk, LRRelAL_sorts Δ hk h hl1 hl2 hOK⟩⟩

theorem hasTyArmBvarAL {Γ : LCtxA} {i : Nat} {A : ExprA} (h : lookupTypeA Γ i = some A) :
    FundArmAL E n σ N K ρ₀ Γ (.bvar i) (.bvar i) A :=
  ⟨0, fun _ _ _ _ _ _ hs => hs.1 i A h⟩

theorem convArmSymmAL {Γ : LCtxA} {a b A : ExprA}
    (ih : FundArmAL E n σ N K ρ₀ Γ a b A) :
    FundArmAL E n σ N K ρ₀ Γ b a A := by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ s' s hΔ (ValidSubstAL_symm hs)
  exact ⟨LREqAL_symm he, LRRelAL_transport' he (LRRelAL_symm hr)⟩

theorem convArmTransAL {Γ : LCtxA} {a b c A : ExprA}
    (ih₁ : FundArmAL E n σ N K ρ₀ Γ a b A) (ih₂ : FundArmAL E n σ N K ρ₀ Γ b c A) :
    FundArmAL E n σ N K ρ₀ Γ a c A := by
  obtain ⟨k₁, h₁⟩ := ih₁
  obtain ⟨k₂, h₂⟩ := ih₂
  refine ⟨max k₁ k₂, fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨_, hr₁⟩ := h₁ k (le_max_of_le₁ hk) Δ s s hΔ (ValidSubstAL_refl_left hs)
  obtain ⟨he, hr₂⟩ := h₂ k (le_max_of_le₂ hk) Δ s s' hΔ hs
  exact ⟨he, LRRelAL_trans hr₁ hr₂⟩

theorem hasTyArmConvAL {Γ : LCtxA} {e A B : ExprA} {u : Level}
    (ih : FundArmAL E n σ N K ρ₀ Γ e e A)
    (ihB : FundArmAL E n σ N K ρ₀ Γ B B (.sort u))
    (ihc : FundArmAL E n σ N K ρ₀ Γ A B (.sort u)) :
    FundArmAL E n σ N K ρ₀ Γ e e B := by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := ihB
  obtain ⟨k₃, h₃⟩ := ihc
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨_, hr⟩ := h₁ k (le_max_of_le₁ hk) Δ s s' hΔ hs
  obtain ⟨_, hB⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ s s' hΔ hs
  obtain ⟨_, hc⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ s s hΔ (ValidSubstAL_refl_left hs)
  exact ⟨LREqAL_of_sortRel hB, LRRelAL_transport' (LREqAL_of_sortRel hc) hr⟩

theorem convArmTyConvAL {Γ : LCtxA} {a b A A' : ExprA} {l' u : Level}
    (ih : FundArmAL E n σ N K ρ₀ Γ a b A)
    (ihA' : FundArmAL E n σ N K ρ₀ Γ A' A' (.sort l'))
    (ihA : FundArmAL E n σ N K ρ₀ Γ A A' (.sort u)) :
    FundArmAL E n σ N K ρ₀ Γ a b A' := by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := ihA'
  obtain ⟨k₃, h₃⟩ := ihA
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨_, hr⟩ := h₁ k (le_max_of_le₁ hk) Δ s s' hΔ hs
  obtain ⟨_, hA'⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ s s' hΔ hs
  obtain ⟨_, hAA'⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ s s hΔ (ValidSubstAL_refl_left hs)
  exact ⟨LREqAL_of_sortRel hA', LRRelAL_transport' (LREqAL_of_sortRel hAA') hr⟩

theorem convArmZetaLocalAL {Γ : LCtxA} {i : Nat} {A v : ExprA}
    (hval : lookupValueA Γ i = some v) (hty : lookupTypeA Γ i = some A)
    (ih : FundArmAL E n σ N K ρ₀ Γ v v A) :
    FundArmAL E n σ N K ρ₀ Γ (.bvar i) v A := by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ s s' hΔ hs
  obtain ⟨hv1, _⟩ := hs.2 i A v hty hval
  exact ⟨he, LRRelAL_trans hv1 hr⟩

theorem hasTyArmLitAL (hE : EnvClosedA E) {Γ : LCtxA} (t : Nat) {T : ExprA}
    (ih : FundArmAL E n σ N K ρ₀ Γ (natExpandA t) (natExpandA t) T) :
    FundArmAL E n σ N K ρ₀ Γ (.lit t) (.lit t) T := by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ s s' hΔ hs
  simp only [substA_natExpandA] at hr
  obtain ⟨hl, _⟩ := LRRelAL_hasTy hr
  obtain ⟨d, hd⟩ := ex_hasTyT_lok_cast rfl (erase_natExpandA t) rfl hl.2
  have hs_lit : StepAtAL E n σ N K Δ (.lit t) (natExpandA t) (substA s T) :=
    ⟨⟨hl.1.elim fun x => ⟨.lit Δ t _ x⟩, hl.1.elim fun x => ⟨.lit Δ t _ x⟩⟩,
     ⟨hl.1.elim fun x => ⟨.lit Δ t _ x⟩,
      ⟨.lit (eraseCtx Δ) t (erase (substA s T)) d, hd⟩⟩,
     ⟨hl.1.elim fun x => ⟨.lit Δ t _ x⟩,
      ex_convT_lok_cast rfl rfl (erase_natExpandA t).symm rfl
        ⟨.lit (eraseCtx Δ) t (natExpand t) (erase (substA s T)) (.of t) d, hd⟩⟩⟩
  exact ⟨he, LRRelAL_expand_left hE hs_lit (LRRelAL_expand_right hE hs_lit hr)⟩

theorem convArmLitAL (hE : EnvClosedA E) {Γ : LCtxA} (t : Nat) {T : ExprA}
    (ih : FundArmAL E n σ N K ρ₀ Γ (natExpandA t) (natExpandA t) T) :
    FundArmAL E n σ N K ρ₀ Γ (.lit t) (natExpandA t) T := by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ s s' hΔ hs
  simp only [substA_natExpandA] at hr
  obtain ⟨hl, _⟩ := LRRelAL_hasTy hr
  obtain ⟨d, hd⟩ := ex_hasTyT_lok_cast rfl (erase_natExpandA t) rfl hl.2
  have hs_lit : StepAtAL E n σ N K Δ (.lit t) (natExpandA t) (substA s T) :=
    ⟨⟨hl.1.elim fun x => ⟨.lit Δ t _ x⟩, hl.1.elim fun x => ⟨.lit Δ t _ x⟩⟩,
     ⟨hl.1.elim fun x => ⟨.lit Δ t _ x⟩,
      ⟨.lit (eraseCtx Δ) t (erase (substA s T)) d, hd⟩⟩,
     ⟨hl.1.elim fun x => ⟨.lit Δ t _ x⟩,
      ex_convT_lok_cast rfl rfl (erase_natExpandA t).symm rfl
        ⟨.lit (eraseCtx Δ) t (natExpand t) (erase (substA s T)) (.of t) d, hd⟩⟩⟩
  simp only [substA_natExpandA]
  exact ⟨he, LRRelAL_expand_left hE hs_lit hr⟩

theorem convArmDeltaAL (hE : EnvClosedA E) {Γ : LCtxA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA}
    (hres : E.members r = some m) (hbody : m.bodyA = some b) (htr : transparent m.mclass = true)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true) (hls : LevelsOK σ (K r) ls)
    (ih : FundArmAL E n σ N K ρ₀ Γ (instantiateLevelsA ls b) (instantiateLevelsA ls b)
      (instantiateLevelsA ls m.mtypeA)) :
    FundArmAL E n σ N K ρ₀ Γ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA) := by
  obtain ⟨k₀, h⟩ := ih
  refine ⟨k₀, fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨he, hr⟩ := h k hk Δ s s' hΔ hs
  rw [substA_mtype hE hres, substA_mtype hE hres] at he
  rw [substA_mtype hE hres, substA_mbody hE hres hbody, substA_mbody hE hres hbody] at hr
  rw [substA_mtype hE hres, substA_mtype hE hres, substA_mbody hE hres hbody, substA_const]
  obtain ⟨hl, _⟩ := LRRelAL_hasTy hr
  obtain ⟨R, hR⟩ := LRRelAL_valid hr
  obtain ⟨u, hTu⟩ := LRTyAL_hasTy hR
  have hresE : (eraseEnv E).members r = some (eraseMember m) := by
    simp only [eraseEnv, hres, Option.map_some']
  have hbodyE : (eraseMember m).body = some (erase b) := by
    simp only [eraseMember, hbody, Option.map_some']
  have hmtype : erase (instantiateLevelsA ls m.mtypeA) = instantiateLevels ls (eraseMember m).mtype := by
    rw [erase_instantiateLevelsA]; rfl
  obtain ⟨db, hdb⟩ := ex_hasTyT_lok_cast rfl (erase_instantiateLevelsA b ls) hmtype hl.2
  have hst : StepAtAL E n σ N K Δ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA) :=
    ⟨⟨hTu.elim fun tu => ⟨.const Δ r ls m u hres hlen hwf tu⟩,
      hl.1.elim fun x => ⟨.delta Δ r ls m b hres hbody htr hlen hwf x⟩⟩,
     ⟨hTu.elim fun tu => ⟨.const Δ r ls m u hres hlen hwf tu⟩,
      ex_hasTyT_lok_cast rfl rfl hmtype.symm
        ⟨.const (eraseCtx Δ) r ls (eraseMember m) hresE hlen hwf, hls⟩⟩,
     ⟨hl.1.elim fun x => ⟨.delta Δ r ls m b hres hbody htr hlen hwf x⟩,
      ex_convT_lok_cast rfl rfl (erase_instantiateLevelsA b ls).symm hmtype.symm
        ⟨.delta (eraseCtx Δ) r ls (eraseMember m) (erase b) hresE hbodyE htr hlen hwf db,
         by simp only [LOKc]; exact ⟨hls, hdb⟩⟩⟩⟩
  exact ⟨he, LRRelAL_expand_left hE hst hr⟩

theorem hasTyArmConstAL (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀)
    {Γ : LCtxA} {r : Nat} {ls : List Level} {m : CheckedMemberA} {u : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hls : LevelsOK σ (K r) ls)
    (ih : FundArmAL E n σ N K ρ₀ Γ (instantiateLevelsA ls m.mtypeA) (instantiateLevelsA ls m.mtypeA) (.sort u)) :
    FundArmAL E n σ N K ρ₀ Γ (.const r ls) (.const r ls) (instantiateLevelsA ls m.mtypeA) := by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := hS r m hres ls ls hlen hwf hwf (eqNList_refl ls) hls hls
  refine ⟨max k₁ k₂, fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨_, hTT⟩ := h₁ k (le_max_of_le₁ hk) Δ s s' hΔ hs
  rw [substA_mtype hE hres, substA_mtype hE hres] at hTT
  rw [substA_mtype hE hres, substA_mtype hE hres, substA_const, substA_const]
  exact ⟨LREqAL_of_sortRel hTT, h₂ k (le_max_of_le₂ hk) Δ hΔ⟩

theorem convArmConstsAL (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀)
    {Γ : LCtxA} {r : Nat} {ls ls' : List Level} {m : CheckedMemberA}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (h : eqNList ls ls') (hls : LevelsOK σ (K r) ls) (hls' : LevelsOK σ (K r) ls')
    (ih : FundArmAL E n σ N K ρ₀ Γ (.const r ls') (.const r ls') (instantiateLevelsA ls m.mtypeA)) :
    FundArmAL E n σ N K ρ₀ Γ (.const r ls) (.const r ls') (instantiateLevelsA ls m.mtypeA) := by
  obtain ⟨k₁, h₁⟩ := ih
  obtain ⟨k₂, h₂⟩ := hS r m hres ls ls' hlen hwf hwf' h hls hls'
  refine ⟨max k₁ k₂, fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨he, _⟩ := h₁ k (le_max_of_le₁ hk) Δ s s' hΔ hs
  rw [substA_mtype hE hres, substA_mtype hE hres] at he
  rw [substA_mtype hE hres, substA_mtype hE hres, substA_const, substA_const]
  exact ⟨he, h₂ k (le_max_of_le₂ hk) Δ hΔ⟩

theorem convArmIrrAL {Γ : LCtxA} {P p q : ExprA}
    (ihP : FundArmAL E n σ N K ρ₀ Γ P P (.sort .zero))
    (ihp : FundArmAL E n σ N K ρ₀ Γ p p P)
    (ihq : FundArmAL E n σ N K ρ₀ Γ q q P) :
    FundArmAL E n σ N K ρ₀ Γ p q P := by
  obtain ⟨k₁, h₁⟩ := ihP
  obtain ⟨k₂, h₂⟩ := ihp
  obtain ⟨k₃, h₃⟩ := ihq
  refine ⟨max k₁ (max k₂ k₃), fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨_, hPP⟩ := h₁ k (le_max_of_le₁ hk) Δ s s' hΔ hs
  obtain ⟨heP, hp⟩ := h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Δ s s' hΔ hs
  obtain ⟨_, hq⟩ := h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Δ s' s' hΔ (ValidSubstAL_refl_right hs)
  obtain ⟨⟨M, hM, hMt⟩, _, hPt, hP't, hPc, _⟩ := LRRelAL_sort0_elim hPP
  have hpt : HasTyAL E n σ N K Δ (substA s p) (substA s P) := (LRRelAL_hasTy hp).1
  have hqt' : HasTyAL E n σ N K Δ (substA s' q) (substA s' P) := (LRRelAL_hasTy hq).1
  have htcP : TyConvAL E n σ N K Δ (substA s' P) (substA s P) :=
    tyConvAL_of_convAL hP't.1 (eqNA_refl .zero) hPt.1 (eqNA_refl .zero) (convAL_symm hPc)
  have hqt : HasTyAL E n σ N K Δ (substA s' q) (substA s P) :=
    hasTyAL_of_tyConvAL hqt' htcP
  have hirr : ConvAL E n σ N K Δ (substA s p) (substA s' q) (substA s P) :=
    ⟨hPt.1.elim fun tP => hpt.1.elim fun tp => hqt.1.elim fun tq => ⟨.irr Δ _ _ _ tP tp tq⟩,
     hPt.2.elim fun dtP hdtP => hpt.2.elim fun dtp hdtp => hqt.2.elim fun dtq hdtq =>
       ⟨.irr (eraseCtx Δ) _ _ _ dtP dtp dtq, ⟨hdtP, hdtp, hdtq⟩⟩⟩
  refine ⟨heP, ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hM hMt, ?_⟩⟩
  exact ⟨hasTyAL_of_tyConvAL hpt hM.2, hasTyAL_of_tyConvAL hqt hM.2, convAL_of_tyConvAL hirr hM.2⟩

theorem hasTyArmPiAL (hE : EnvClosedA E) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {A : ExprA} {u : Level} {B : ExprA} {v : Level}
    (hu : evalTotal σ u ≤ N) (hv : evalTotal σ v ≤ N)
    (ihA : FundArmAL E n σ N K ρ₀ Γ A A (.sort u))
    (ihB : FundArmAL E n σ N K ρ₀ (.assumption A :: Γ) B B (.sort v)) :
    FundArmAL E n σ N K ρ₀ Γ (.pi A u B v) (.pi A u B v) (.sort (.imax u v)) := by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kB, hB⟩ := ihB
  refine ⟨max (max kA kB) (ht ρ₀ (.imax u v) + 1), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkB : kB ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkh : ht ρ₀ (.imax u v) < k := le_max_of_le₂ hk
  refine ⟨LREqAL_sort_refl Δ hkh, ?_⟩
  have hAΔ : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s A) (substA s' A) := (hA k hkA Δ s s' hΔ hs).2
  obtain ⟨heA, hvA, hvA', tA, tA', cA⟩ := LRRelAL_sort_elim hAΔ
  have heA' : LREqAL E n σ N K ρ₀ k Δ (substA s' A) (substA s' A) := LREqAL_trans (LREqAL_symm heA) heA
  have hup := ValidSubstAL_up hE hΔ hs heA hvA tA.1
  have hup' := ValidSubstAL_up hE hΔ (ValidSubstAL_refl_right hs) heA' hvA' tA'.1
  have hΔA : Nonempty (CtxWfA E noIotaA n (.assumption (substA s A) :: Δ)) :=
    hΔ.elim fun c => tA.1.elim fun t => ⟨.assumption c t⟩
  have hΔA' : Nonempty (CtxWfA E noIotaA n (.assumption (substA s' A) :: Δ)) :=
    hΔ.elim fun c => tA'.1.elim fun t => ⟨.assumption c t⟩
  have hBΔ : LRRelAL E n σ N K ρ₀ k (.assumption (substA s A) :: Δ) (.sort v)
      (substA s.up B) (substA s'.up B) := (hB k hkB _ s.up s'.up hΔA hup).2
  have hBΔ' : LRRelAL E n σ N K ρ₀ k (.assumption (substA s' A) :: Δ) (.sort v)
      (substA s'.up B) (substA s'.up B) := (hB k hkB _ s'.up s'.up hΔA' hup').2
  obtain ⟨_, _, _, tB, _, cB⟩ := LRRelAL_sort_elim hBΔ
  obtain ⟨_, _, _, tB', _, _⟩ := LRRelAL_sort_elim hBΔ'
  have tpi : HasTyAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v) (.sort (.imax u v)) :=
    ⟨tA.1.elim fun a => tB.1.elim fun b => ⟨.pi Δ _ u _ v a b⟩,
     tA.2.elim fun da hda => tB.2.elim fun db hdb =>
       ⟨.pi (eraseCtx Δ) _ u _ v da db, ⟨hu, hv, hda, hdb⟩⟩⟩
  have tpi' : HasTyAL E n σ N K Δ (.pi (substA s' A) u (substA s'.up B) v) (.sort (.imax u v)) :=
    ⟨tA'.1.elim fun a => tB'.1.elim fun b => ⟨.pi Δ _ u _ v a b⟩,
     tA'.2.elim fun da hda => tB'.2.elim fun db hdb =>
       ⟨.pi (eraseCtx Δ) _ u _ v da db, ⟨hu, hv, hda, hdb⟩⟩⟩
  have cpi : ConvAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v)
      (.pi (substA s' A) u (substA s'.up B) v) (.sort (.imax u v)) :=
    ⟨cA.1.elim fun a => cB.1.elim fun b => tpi'.1.elim fun t =>
      ⟨.pi Δ _ _ _ _ u u v v (eqNA_refl u) (eqNA_refl v) a b t⟩,
     cA.2.elim fun da hda => cB.2.elim fun db hdb =>
       ⟨.pi (eraseCtx Δ) _ _ _ _ u v da db, ⟨hu, hv, hda, hdb⟩⟩⟩
  have hS : WhTyAL E n σ N K Δ (.sort (.imax u v)) (.sort (.imax u v)) :=
    whTyAL_of_hasTy ⟨.sort Δ _⟩
  cases hz : isZero v with
  | true =>
      have hz' : isZero (.imax u v) = true := by rw [isZero_imax]; exact hz
      refine ⟨_, by rw [LRTyAL_eq]; exact .sortP hS hz', ?_⟩
      refine ⟨⟨_, whTyAL_of_hasTy tpi.1, tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _)
        ((isPropTy_pi_iff E noIotaA Δ _ u _ v).2 hz)⟩,
        ⟨_, whTyAL_of_hasTy tpi'.1, tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _)
        ((isPropTy_pi_iff E noIotaA Δ _ u _ v).2 hz)⟩, tpi, tpi', cpi, ?_⟩
      exact .pi (whTyAL_of_hasTy tpi.1) (whTyAL_of_hasTy tpi'.1)
        (eqNA_refl u) (eqNA_refl v) tA.1 tA'.1
        (fun ρ hρ' => tyConvAL_wk hE Δ ρ hρ'.1
          (tyConvAL_of_convAL tA.1 (eqNA_refl u) tA'.1 (eqNA_refl u) cA))
        (propEqAL_codom_of_fund hE hz hB hkB hs heA hvA)
        (tyConvAL_of_convAL tpi.1 (eqNA_refl _) tpi'.1 (eqNA_refl _) cpi)
  | false =>
      have hvpos : 0 < ht ρ₀ v := ht_pos_of_isZero_false hρ v hz
      have hh : ht ρ₀ (.imax u v) = max (ht ρ₀ u) (ht ρ₀ v) := ht_imax_of_pos hvpos
      have hz' : isZero (.imax u v) = false := by rw [isZero_imax]; exact hz
      have hu_le : ht ρ₀ u ≤ ht ρ₀ (.imax u v) := by rw [hh]; exact Nat.le_max_left _ _
      have hv_le : ht ρ₀ v ≤ ht ρ₀ (.imax u v) := by rw [hh]; exact Nat.le_max_right _ _
      have hhk : ht ρ₀ (.imax u v) ≤ k := Nat.le_of_lt hkh
      have dA : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
          LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A)) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) R) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s' A)) R) :=
        fun ρ hρ' => (LRRelAL_sort_elim' (fundArm_sort_wkAL hE hA hkA hs ρ hρ')).1 _ hu_le
      have eA : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
          LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A)) :=
        fun ρ hρ' => LREqAL_of_sortRel (fundArm_sort_wkAL hE hA hkA hs ρ hρ')
      have eA' : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
          LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s' A)) (wkExprA ρ (substA s' A)) :=
        fun ρ hρ' => LREqAL_trans (LREqAL_symm (eA ρ hρ')) (eA ρ hρ')
      have eA0 : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
          LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s A)) :=
        fun ρ hρ' => LREqAL_trans (eA ρ hρ') (LREqAL_symm (eA ρ hρ'))
      have dB : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
          LRRelAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) a a' →
          LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s'.up B))) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up B))) R) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s'.up B))) R) :=
        fun ρ hρ' a a' haa => (LRRelAL_sort_elim' (fundArm_cons_wk_sortAL hE hB hkB hs ρ hρ'
          (eA ρ hρ') (LRRelAL_mono hhk haa))).1 _ hv_le
      have dB0 : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
          LRRelAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) a a' →
          LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        fun ρ hρ' a a' haa => (LRRelAL_sort_elim' (fundArm_cons_wk_sortAL hE hB hkB
          (ValidSubstAL_refl_left hs) ρ hρ' (eA0 ρ hρ') (LRRelAL_mono hhk haa))).1 _ hv_le |>.1
      have dB' : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
          LRRelAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s' A)) a a' →
          LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s'.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s'.up B))) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s'.up B))) R) :=
        fun ρ hρ' a a' haa =>
          let r := (LRRelAL_sort_elim' (fundArm_cons_wk_sortAL hE hB hkB
            (ValidSubstAL_refl_right hs) ρ hρ' (eA' ρ hρ') (LRRelAL_mono hhk haa))).1 _ hv_le
          ⟨r.1, r.2.1⟩
      have tyc : TyConvAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v)
          (.pi (substA s' A) u (substA s'.up B) v) :=
        tyConvAL_of_convAL tpi.1 (eqNA_refl _) tpi'.1 (eqNA_refl _) cpi
      have hT1 : ∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA s A) u (substA s.up B) v) R :=
        tA.1.elim fun a => tB.1.elim fun b =>
          ⟨_, piTyAL_of_data hz a b (fun ρ hρ' => (dA ρ hρ').2.1)
            (fun ρ hρ' a a' haa => (dB ρ hρ' a a' haa).2.1) dB0⟩
      have hT2 : ∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA s' A) u (substA s'.up B) v) R :=
        tA'.1.elim fun a' => tB'.1.elim fun b' =>
          ⟨_, piTyAL_of_data hz a' b' (fun ρ hρ' => (dA ρ hρ').2.2)
            (fun ρ hρ' a a' haa => (dB' ρ hρ' a a' haa).2)
            (fun ρ hρ' a a' haa => (dB' ρ hρ' a a' haa).1)⟩
      have hEq : LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA s A) u (substA s.up B) v)
          (.pi (substA s' A) u (substA s'.up B) v) :=
        tA.1.elim fun a => tB.1.elim fun b => tA'.1.elim fun a' => tB'.1.elim fun b' =>
          piEqAL_of_data (eqNA_refl _) (eqNA_refl _) a b a' b' (fun ρ hρ' => (dA ρ hρ').1)
            (fun ρ hρ' => (dA ρ hρ').2.1) (fun ρ hρ' a haa => (dB ρ hρ' a a haa).1) tyc
      refine ⟨_, by rw [LRTyAL_eq]; exact .sortT hS hz' hkh, ?_⟩
      exact ⟨hEq, hT1, hT2, tpi, tpi', cpi⟩

theorem hasTyArmLamAL (hE : EnvClosedA E)
    {Γ : LCtxA} {A : ExprA} {u : Level} {body B : ExprA} {v : Level}
    (hu : evalTotal σ u ≤ N) (hv : evalTotal σ v ≤ N)
    (ihA : FundArmAL E n σ N K ρ₀ Γ A A (.sort u))
    (ihB : FundArmAL E n σ N K ρ₀ (.assumption A :: Γ) B B (.sort v))
    (ihb : FundArmAL E n σ N K ρ₀ (.assumption A :: Γ) body body B) :
    FundArmAL E n σ N K ρ₀ Γ (.lam A u body) (.lam A u body) (.pi A u B v) := by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kB, hB⟩ := ihB
  obtain ⟨kb, hb⟩ := ihb
  refine ⟨max kA (max kB kb), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ hk
  have hkB : kB ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkb : kb ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  have hAΔ : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s A) (substA s' A) := (hA k hkA Δ s s' hΔ hs).2
  obtain ⟨heA, hvA, hvA', tA, tA', cA⟩ := LRRelAL_sort_elim hAΔ
  have heA' : LREqAL E n σ N K ρ₀ k Δ (substA s' A) (substA s' A) := LREqAL_trans (LREqAL_symm heA) heA
  have hup := ValidSubstAL_up hE hΔ hs heA hvA tA.1
  have hup' := ValidSubstAL_up hE hΔ (ValidSubstAL_refl_right hs) heA' hvA' tA'.1
  have hΔA : Nonempty (CtxWfA E noIotaA n (.assumption (substA s A) :: Δ)) :=
    hΔ.elim fun c => tA.1.elim fun t => ⟨.assumption c t⟩
  have hΔA' : Nonempty (CtxWfA E noIotaA n (.assumption (substA s' A) :: Δ)) :=
    hΔ.elim fun c => tA'.1.elim fun t => ⟨.assumption c t⟩
  have hBΔ : LRRelAL E n σ N K ρ₀ k (.assumption (substA s A) :: Δ) (.sort v)
      (substA s.up B) (substA s'.up B) := (hB k hkB _ s.up s'.up hΔA hup).2
  have hBΔ' : LRRelAL E n σ N K ρ₀ k (.assumption (substA s' A) :: Δ) (.sort v)
      (substA s'.up B) (substA s'.up B) := (hB k hkB _ s'.up s'.up hΔA' hup').2
  obtain ⟨_, _, _, tB, _, cB⟩ := LRRelAL_sort_elim hBΔ
  obtain ⟨_, _, _, tB', _, _⟩ := LRRelAL_sort_elim hBΔ'
  have hbΔ : LRRelAL E n σ N K ρ₀ k (.assumption (substA s A) :: Δ) (substA s.up B)
      (substA s.up body) (substA s'.up body) := (hb k hkb _ s.up s'.up hΔA hup).2
  have hbΔ' : LRRelAL E n σ N K ρ₀ k (.assumption (substA s' A) :: Δ) (substA s'.up B)
      (substA s'.up body) (substA s'.up body) := (hb k hkb _ s'.up s'.up hΔA' hup').2
  obtain ⟨tbody, _⟩ := LRRelAL_hasTy hbΔ
  obtain ⟨tbody', _⟩ := LRRelAL_hasTy hbΔ'
  have cbody := LRRelAL_conv hbΔ
  have tpi : HasTyAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v) (.sort (.imax u v)) :=
    ⟨tA.1.elim fun a => tB.1.elim fun b => ⟨.pi Δ _ u _ v a b⟩,
     tA.2.elim fun da hda => tB.2.elim fun db hdb =>
       ⟨.pi (eraseCtx Δ) _ u _ v da db, ⟨hu, hv, hda, hdb⟩⟩⟩
  have tpi' : HasTyAL E n σ N K Δ (.pi (substA s' A) u (substA s'.up B) v) (.sort (.imax u v)) :=
    ⟨tA'.1.elim fun a => tB'.1.elim fun b => ⟨.pi Δ _ u _ v a b⟩,
     tA'.2.elim fun da hda => tB'.2.elim fun db hdb =>
       ⟨.pi (eraseCtx Δ) _ u _ v da db, ⟨hu, hv, hda, hdb⟩⟩⟩
  have cpi : ConvAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v)
      (.pi (substA s' A) u (substA s'.up B) v) (.sort (.imax u v)) :=
    ⟨cA.1.elim fun a => cB.1.elim fun b => tpi'.1.elim fun t =>
      ⟨.pi Δ _ _ _ _ u u v v (eqNA_refl u) (eqNA_refl v) a b t⟩,
     cA.2.elim fun da hda => cB.2.elim fun db hdb =>
       ⟨.pi (eraseCtx Δ) _ _ _ _ u v da db, ⟨hu, hv, hda, hdb⟩⟩⟩
  have tyc : TyConvAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v)
      (.pi (substA s' A) u (substA s'.up B) v) :=
    tyConvAL_of_convAL tpi.1 (eqNA_refl _) tpi'.1 (eqNA_refl _) cpi
  have tlam : HasTyAL E n σ N K Δ (.lam (substA s A) u (substA s.up body))
      (.pi (substA s A) u (substA s.up B) v) :=
    ⟨tA.1.elim fun a => tB.1.elim fun b => tbody.1.elim fun t => ⟨.lam Δ _ u _ _ v a b t⟩,
     tA.2.elim fun da hda => tbody.2.elim fun dtb hdtb =>
       ⟨.lam (eraseCtx Δ) _ u _ _ da dtb, ⟨hda, hdtb⟩⟩⟩
  have tlam'_0 : HasTyAL E n σ N K Δ (.lam (substA s' A) u (substA s'.up body))
      (.pi (substA s' A) u (substA s'.up B) v) :=
    ⟨tA'.1.elim fun a => tB'.1.elim fun b => tbody'.1.elim fun t => ⟨.lam Δ _ u _ _ v a b t⟩,
     tA'.2.elim fun da hda => tbody'.2.elim fun dtb hdtb =>
       ⟨.lam (eraseCtx Δ) _ u _ _ da dtb, ⟨hda, hdtb⟩⟩⟩
  have tlam' : HasTyAL E n σ N K Δ (.lam (substA s' A) u (substA s'.up body))
      (.pi (substA s A) u (substA s.up B) v) :=
    hasTyAL_of_tyConvAL tlam'_0 (tyConvAL_symm tyc)
  have clam : ConvAL E n σ N K Δ (.lam (substA s A) u (substA s.up body))
      (.lam (substA s' A) u (substA s'.up body)) (.pi (substA s A) u (substA s.up B) v) :=
    ⟨cA.1.elim fun a => cbody.1.elim fun c => tlam'.1.elim fun t =>
      ⟨.lam Δ _ _ _ _ _ u u v (eqNA_refl u) a c t⟩,
     cA.2.elim fun da hda => cbody.2.elim fun dc hdc =>
       ⟨.lam (eraseCtx Δ) _ _ _ _ _ u da dc, ⟨hda, hdc⟩⟩⟩
  have eA : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
      LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A)) :=
    fun ρ hρ' => LREqAL_of_sortRel (fundArm_sort_wkAL hE hA hkA hs ρ hρ')
  have eA0 : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
      LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s A)) :=
    fun ρ hρ' => LREqAL_trans (eA ρ hρ') (LREqAL_symm (eA ρ hρ'))
  have vA : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
      ∃ R, LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) R :=
    fun ρ hρ' => (LRRelAL_sort_elim (fundArm_sort_wkAL hE hA hkA hs ρ hρ')).2.1
  have hEq : LREqAL E n σ N K ρ₀ k Δ (.pi (substA s A) u (substA s.up B) v)
      (.pi (substA s' A) u (substA s'.up B) v) :=
    tA.1.elim fun a => tB.1.elim fun b => tA'.1.elim fun a' => tB'.1.elim fun b' =>
      piEqAL_of_data (eqNA_refl _) (eqNA_refl _) a b a' b' eA vA
        (fun ρ hρ' x hxx => LREqAL_of_sortRel
          (fundArm_cons_wk_sortAL hE hB hkB hs ρ hρ' (eA ρ hρ') hxx)) tyc
  refine ⟨hEq, ?_⟩
  cases hz : isZero v with
  | true =>
      have hnf : TripleLikeA E noIotaA Δ (.pi (substA s A) u (substA s.up B) v) :=
        tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _) ((isPropTy_pi_iff E noIotaA Δ _ u _ v).2 hz)
      have hwh : WhTyAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v)
          (.pi (substA s A) u (substA s.up B) v) :=
        whTyAL_of_hasTy tpi.1
      refine ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hwh hnf, ?_⟩
      exact ⟨tlam, tlam', clam⟩
  | false =>
      have vB : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ x x' : ExprA,
          LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) x x' →
          ∃ R, LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B))) R :=
        fun ρ hρ' x x' hxx =>
          (LRRelAL_sort_elim (fundArm_cons_wk_sortAL hE hB hkB hs ρ hρ' (eA ρ hρ') hxx)).2.1
      have eB0 : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ x x' : ExprA,
          LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) x x' →
          LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
            (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        fun ρ hρ' x x' hxx => LREqAL_of_sortRel
          (fundArm_cons_wk_sortAL hE hB hkB (ValidSubstAL_refl_left hs) ρ hρ' (eA0 ρ hρ') hxx)
      refine tA.1.elim fun a => tB.1.elim fun b =>
        ⟨_, piTyAL_of_data hz a b vA vB eB0, fun ρ hρ' x x' hxx => ?_, tlam, tlam', clam⟩
      have ih := fundArm_cons_wkAL hE hb hkb hs ρ hρ' (eA ρ hρ') hxx
      obtain ⟨tx, tx'⟩ := LRRelAL_hasTy hxx
      obtain ⟨tred, tred'⟩ := LRRelAL_hasTy ih.2
      obtain ⟨R₁, hR₁⟩ := LRRelAL_valid ih.2
      obtain ⟨R₂, hR₂⟩ := LREqAL_valid ih.1 ⟨R₁, hR₁⟩
      obtain ⟨w₁, tTy⟩ := LRTyAL_hasTy hR₁
      obtain ⟨w₂, tTy'⟩ := LRTyAL_hasTy hR₂
      have tc := LREqAL_tyConv ih.1
      have tcA := LREqAL_tyConv (eA ρ hρ')
      have hsL : StepAtAL E n σ N K (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam (substA s A) u (substA s.up body))) x)
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up body)))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        stepAtAL_beta_wk hE tA tB.1 tbody ρ hρ' tx tred tTy
      have hsR : StepAtAL E n σ N K (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam (substA s' A) u (substA s'.up body))) x')
          (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA s'.up body)))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        stepAtAL_tyConv (stepAtAL_beta_wk hE tA' tB'.1 tbody' ρ hρ'
          (hasTyAL_of_tyConvAL tx' tcA) (hasTyAL_of_tyConvAL tred' tc) tTy') (tyConvAL_symm tc)
      exact LRRelAL_expand_left hE hsL (LRRelAL_expand_right hE hsR ih.2)

theorem hasTyArmAppAL (hE : EnvClosedA E)
    {Γ : LCtxA} {f a A B : ExprA} {u v w : Level}
    (ihB : FundArmAL E n σ N K ρ₀ (.assumption A :: Γ) B B (.sort v))
    (ihTy : FundArmAL E n σ N K ρ₀ Γ (instantiate0A a B) (instantiate0A a B) (.sort w))
    (ihf : FundArmAL E n σ N K ρ₀ Γ f f (.pi A u B v))
    (iha : FundArmAL E n σ N K ρ₀ Γ a a A) :
    FundArmAL E n σ N K ρ₀ Γ (.app f a) (.app f a) (instantiate0A a B) := by
  obtain ⟨kB, hB⟩ := ihB
  obtain ⟨kT, hT⟩ := ihTy
  obtain ⟨kf, hf⟩ := ihf
  obtain ⟨ka, ha⟩ := iha
  refine ⟨max (max kB kT) (max kf ka), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkB : kB ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkT : kT ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkf : kf ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hka : ka ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨_, hTT⟩ := hT k hkT Δ s s' hΔ hs
  have heT : LREqAL E n σ N K ρ₀ k Δ (substA s (instantiate0A a B)) (substA s' (instantiate0A a B)) :=
    LREqAL_of_sortRel hTT
  refine ⟨heT, ?_⟩
  obtain ⟨heA, haa⟩ := ha k hka Δ s s' hΔ hs
  obtain ⟨hepi, hff⟩ := hf k hkf Δ s s' hΔ hs
  rw [substA_instantiate0A]
  cases hz : isZero v with
  | false =>
      have hnp : ¬ IsPropTy E noIotaA Δ (.pi (substA s A) u (substA s.up B) v) := fun h => by
        rw [(isPropTy_pi_iff E noIotaA Δ _ u _ v).1 h] at hz; cases hz
      exact LRRelAL_pi_elim hff hnp [] ⟨trivial, hΔ⟩ (substA s a) (substA s' a) haa
  | true =>
      have hv := ValidSubstAL_cons hs heA haa
      have hBc := (hB k hkB Δ (SubstA.cons (substA s a) s) (SubstA.cons (substA s' a) s') hΔ hv).2
      rw [← instantiate0A_substA_up, ← instantiate0A_substA_up] at hBc
      obtain ⟨⟨M, hMb, hMt⟩, _, _, _, _⟩ := LRRelAL_sortP_elim hz hBc
      obtain ⟨tf, tf'⟩ := LRRelAL_hasTy hff
      obtain ⟨ta, ta'⟩ := LRRelAL_hasTy haa
      have cf := LRRelAL_conv hff
      have ca := LRRelAL_conv haa
      obtain ⟨RA, hRA⟩ := LRRelAL_valid haa
      obtain ⟨uA, tA⟩ := LRTyAL_hasTy hRA
      have hup := ValidSubstAL_up hE hΔ hs heA ⟨RA, hRA⟩ tA
      have hΔA : Nonempty (CtxWfA E noIotaA n (.assumption (substA s A) :: Δ)) :=
        hΔ.elim fun c => tA.elim fun t => ⟨.assumption c t⟩
      have hBup : LRRelAL E n σ N K ρ₀ k (.assumption (substA s A) :: Δ) (.sort v)
          (substA s.up B) (substA s'.up B) := (hB k hkB _ s.up s'.up hΔA hup).2
      obtain ⟨_, _, _, tB, _, _⟩ := LRRelAL_sort_elim hBup
      have heA' : LREqAL E n σ N K ρ₀ k Δ (substA s' A) (substA s' A) := LREqAL_trans (LREqAL_symm heA) heA
      obtain ⟨RA', hRA'⟩ := LREqAL_valid heA ⟨RA, hRA⟩
      obtain ⟨uA', tA'⟩ := LRTyAL_hasTy hRA'
      have hup' := ValidSubstAL_up hE hΔ (ValidSubstAL_refl_right hs) heA' ⟨RA', hRA'⟩ tA'
      have hΔA' : Nonempty (CtxWfA E noIotaA n (.assumption (substA s' A) :: Δ)) :=
        hΔ.elim fun c => tA'.elim fun t => ⟨.assumption c t⟩
      have hBup' : LRRelAL E n σ N K ρ₀ k (.assumption (substA s' A) :: Δ) (.sort v)
          (substA s'.up B) (substA s'.up B) := (hB k hkB _ s'.up s'.up hΔA' hup').2
      obtain ⟨_, _, _, tB', _, _⟩ := LRRelAL_sort_elim hBup'
      obtain ⟨tTy, tTy'⟩ := LRRelAL_hasTy hTT
      rw [substA_instantiate0A] at tTy tTy'
      have tcpi := LREqAL_tyConv hepi
      have tcA := LREqAL_tyConv heA
      have tcT := LREqAL_tyConv heT
      rw [substA_instantiate0A, substA_instantiate0A] at tcT
      have tapp : HasTyAL E n σ N K Δ (.app (substA s f) (substA s a))
          (instantiate0A (substA s a) (substA s.up B)) :=
        ⟨tB.1.elim fun b => tTy.1.elim fun t => tf.1.elim fun x => ta.1.elim fun y =>
          ⟨.app Δ _ _ _ _ u v w b t x y⟩,
         tf.2.elim fun dtf hdtf => ta.2.elim fun dta hdta =>
           ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (substA s.up B) (substA s a)).symm
             ⟨.app (eraseCtx Δ) _ _ _ _ dtf dta, ⟨hdtf, hdta⟩⟩⟩
      have tf'_pi' := hasTyAL_of_tyConvAL tf' tcpi
      have ta'_A' := hasTyAL_of_tyConvAL ta' tcA
      have tapp'_0 : HasTyAL E n σ N K Δ (.app (substA s' f) (substA s' a))
          (instantiate0A (substA s' a) (substA s'.up B)) :=
        ⟨tB'.1.elim fun b => tTy'.1.elim fun t => tf'_pi'.1.elim fun x => ta'_A'.1.elim fun y =>
          ⟨.app Δ _ _ _ _ u v w b t x y⟩,
         tf'_pi'.2.elim fun dtf hdtf => ta'_A'.2.elim fun dta hdta =>
           ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (substA s'.up B) (substA s' a)).symm
             ⟨.app (eraseCtx Δ) _ _ _ _ dtf dta, ⟨hdtf, hdta⟩⟩⟩
      have tapp' : HasTyAL E n σ N K Δ (.app (substA s' f) (substA s' a))
          (instantiate0A (substA s a) (substA s.up B)) :=
        hasTyAL_of_tyConvAL tapp'_0 (tyConvAL_symm tcT)
      have capp : ConvAL E n σ N K Δ (.app (substA s f) (substA s a)) (.app (substA s' f) (substA s' a))
          (instantiate0A (substA s a) (substA s.up B)) :=
        ⟨cf.1.elim fun c1 => ca.1.elim fun c2 => tB.1.elim fun b => tapp'.1.elim fun t =>
          ⟨.app Δ _ _ _ _ _ _ u v c1 c2 b t⟩,
         cf.2.elim fun dcf hdcf => ca.2.elim fun dca hdca =>
           ex_convT_lok_cast rfl rfl rfl (erase_instantiate0A (substA s.up B) (substA s a)).symm
             ⟨.app (eraseCtx Δ) _ _ _ _ _ _ dcf dca, ⟨hdcf, hdca⟩⟩⟩
      refine ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hMb hMt, ?_⟩
      exact ⟨hasTyAL_of_tyConvAL tapp hMb.2, hasTyAL_of_tyConvAL tapp' hMb.2,
        convAL_of_tyConvAL capp hMb.2⟩

theorem hasTyArmLetEAL (hE : EnvClosedA E)
    {Γ : LCtxA} {A : ExprA} {u w : Level} {value B body : ExprA}
    (ihA : FundArmAL E n σ N K ρ₀ Γ A A (.sort u))
    (ihv : FundArmAL E n σ N K ρ₀ Γ value value A)
    (ihTy : FundArmAL E n σ N K ρ₀ Γ (instantiate0A value B) (instantiate0A value B) (.sort w))
    (ihb : FundArmAL E n σ N K ρ₀ (.letBinding A value :: Γ) body body B) :
    FundArmAL E n σ N K ρ₀ Γ (.letE A value body) (.letE A value body) (instantiate0A value B) := by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kv, hv⟩ := ihv
  obtain ⟨kT, hT⟩ := ihTy
  obtain ⟨kb, hb⟩ := ihb
  refine ⟨max (max kA kv) (max kT kb), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkv : kv ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkT : kT ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkb : kb ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨_, hTT⟩ := hT k hkT Δ s s' hΔ hs
  have heT : LREqAL E n σ N K ρ₀ k Δ (substA s (instantiate0A value B)) (substA s' (instantiate0A value B)) :=
    LREqAL_of_sortRel hTT
  refine ⟨heT, ?_⟩
  have hAΔ : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s A) (substA s' A) := (hA k hkA Δ s s' hΔ hs).2
  obtain ⟨heA, _, _, tA, tA', _⟩ := LRRelAL_sort_elim hAΔ
  have heA' : LREqAL E n σ N K ρ₀ k Δ (substA s' A) (substA s' A) := LREqAL_trans (LREqAL_symm heA) heA
  obtain ⟨_, hvv⟩ := hv k hkv Δ s s' hΔ hs
  have hvv' : LRRelAL E n σ N K ρ₀ k Δ (substA s' A) (substA s' value) (substA s' value) :=
    LRRelAL_transport' heA (LRRelAL_refl_left (LRRelAL_symm hvv))
  obtain ⟨tv, _⟩ := LRRelAL_hasTy hvv
  have tv'' : HasTyAL E n σ N K Δ (substA s' value) (substA s' A) := (LRRelAL_hasTy hvv').1
  have hcons := ValidSubstAL_consLet hs heA hvv
  have hbc := (hb k hkb Δ _ _ hΔ hcons).2
  rw [← instantiate0A_substA_up, ← instantiate0A_substA_up, ← instantiate0A_substA_up] at hbc
  rw [substA_instantiate0A]
  have hupL := ValidSubstAL_upLet hE hΔ hs heA hvv tA.1
  have hupL' := ValidSubstAL_upLet hE hΔ (ValidSubstAL_refl_right hs) heA' hvv' tA'.1
  have hΔL : Nonempty (CtxWfA E noIotaA n (.letBinding (substA s A) (substA s value) :: Δ)) :=
    hΔ.elim fun c => tA.1.elim fun t => tv.1.elim fun x => ⟨.letBinding c t x⟩
  have hΔL' : Nonempty (CtxWfA E noIotaA n (.letBinding (substA s' A) (substA s' value) :: Δ)) :=
    hΔ.elim fun c => tA'.1.elim fun t => tv''.1.elim fun x => ⟨.letBinding c t x⟩
  have hbΔ := (hb k hkb _ s.up s'.up hΔL hupL).2
  have hbΔ' := (hb k hkb _ s'.up s'.up hΔL' hupL').2
  obtain ⟨tbody, _⟩ := LRRelAL_hasTy hbΔ
  obtain ⟨tbody', _⟩ := LRRelAL_hasTy hbΔ'
  obtain ⟨tTy, tTy'⟩ := LRRelAL_hasTy hTT
  rw [substA_instantiate0A] at tTy tTy'
  obtain ⟨tred, tred'⟩ := LRRelAL_hasTy hbc
  have tcT := LREqAL_tyConv heT
  rw [substA_instantiate0A, substA_instantiate0A] at tcT
  have tletL : HasTyAL E n σ N K Δ (.letE (substA s A) (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up B)) :=
    ⟨tA.1.elim fun a => tv.1.elim fun x => tTy.1.elim fun t => tbody.1.elim fun b =>
      ⟨.letE Δ _ u w _ _ _ a x t b⟩,
     tA.2.elim fun da hda => tv.2.elim fun dx hdx => tbody.2.elim fun db hdb =>
       ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (substA s.up B) (substA s value)).symm
         ⟨.letE (eraseCtx Δ) _ u _ _ _ da dx db, ⟨hda, hdx, hdb⟩⟩⟩
  have cletL : ConvAL E n σ N K Δ (.letE (substA s A) (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up B)) :=
    ⟨tA.1.elim fun a => tv.1.elim fun x => tbody.1.elim fun b => tred.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b r⟩,
     tA.2.elim fun da hda => tv.2.elim fun dx hdx => tbody.2.elim fun db hdb =>
       ex_convT_lok_cast rfl rfl
         (erase_instantiate0A (substA s.up body) (substA s value)).symm
         (erase_instantiate0A (substA s.up B) (substA s value)).symm
         ⟨.zeta (eraseCtx Δ) _ _ _ _ u da dx db, ⟨hda, hdx, hdb⟩⟩⟩
  have hsL : StepAtAL E n σ N K Δ (.letE (substA s A) (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up B)) :=
    ⟨⟨tletL.1, tA.1.elim fun a => tv.1.elim fun x => tbody.1.elim fun b => tred.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b r⟩⟩, tletL, cletL⟩
  have tletR_0 : HasTyAL E n σ N K Δ (.letE (substA s' A) (substA s' value) (substA s'.up body))
      (instantiate0A (substA s' value) (substA s'.up B)) :=
    ⟨tA'.1.elim fun a => tv''.1.elim fun x => tTy'.1.elim fun t => tbody'.1.elim fun b =>
      ⟨.letE Δ _ u w _ _ _ a x t b⟩,
     tA'.2.elim fun da hda => tv''.2.elim fun dx hdx => tbody'.2.elim fun db hdb =>
       ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (substA s'.up B) (substA s' value)).symm
         ⟨.letE (eraseCtx Δ) _ u _ _ _ da dx db, ⟨hda, hdx, hdb⟩⟩⟩
  have tred'_0 : HasTyAL E n σ N K Δ (instantiate0A (substA s' value) (substA s'.up body))
      (instantiate0A (substA s' value) (substA s'.up B)) :=
    hasTyAL_of_tyConvAL tred' tcT
  have cletR_0 : ConvAL E n σ N K Δ (.letE (substA s' A) (substA s' value) (substA s'.up body))
      (instantiate0A (substA s' value) (substA s'.up body))
      (instantiate0A (substA s' value) (substA s'.up B)) :=
    ⟨tA'.1.elim fun a => tv''.1.elim fun x => tbody'.1.elim fun b => tred'_0.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b r⟩,
     tA'.2.elim fun da hda => tv''.2.elim fun dx hdx => tbody'.2.elim fun db hdb =>
       ex_convT_lok_cast rfl rfl
         (erase_instantiate0A (substA s'.up body) (substA s' value)).symm
         (erase_instantiate0A (substA s'.up B) (substA s' value)).symm
         ⟨.zeta (eraseCtx Δ) _ _ _ _ u da dx db, ⟨hda, hdx, hdb⟩⟩⟩
  have hsR_0 : StepAtAL E n σ N K Δ (.letE (substA s' A) (substA s' value) (substA s'.up body))
      (instantiate0A (substA s' value) (substA s'.up body))
      (instantiate0A (substA s' value) (substA s'.up B)) :=
    ⟨⟨tletR_0.1, tA'.1.elim fun a => tv''.1.elim fun x => tbody'.1.elim fun b => tred'_0.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b r⟩⟩, tletR_0, cletR_0⟩
  have hsR : StepAtAL E n σ N K Δ (.letE (substA s' A) (substA s' value) (substA s'.up body))
      (instantiate0A (substA s' value) (substA s'.up body))
      (instantiate0A (substA s value) (substA s.up B)) :=
    stepAtAL_tyConv hsR_0 (tyConvAL_symm tcT)
  exact LRRelAL_expand_left hE hsL (LRRelAL_expand_right hE hsR hbc)

theorem convArmBetaAL (hE : EnvClosedA E)
    {Γ : LCtxA} {A : ExprA} {u : Level} {body arg B : ExprA}
    (ihA : FundArmAL E n σ N K ρ₀ Γ A A (.sort u))
    (ihb : FundArmAL E n σ N K ρ₀ (.assumption A :: Γ) body body B)
    (iha : FundArmAL E n σ N K ρ₀ Γ arg arg A)
    (ihr : FundArmAL E n σ N K ρ₀ Γ (instantiate0A arg body) (instantiate0A arg body) (instantiate0A arg B)) :
    FundArmAL E n σ N K ρ₀ Γ (.app (.lam A u body) arg) (instantiate0A arg body) (instantiate0A arg B) := by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kb, hb⟩ := ihb
  obtain ⟨ka, ha⟩ := iha
  obtain ⟨kr, hr⟩ := ihr
  refine ⟨max (max kA kb) (max ka kr), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkb : kb ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hka : ka ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨heT, _⟩ := hr k hkr Δ s s' hΔ hs
  refine ⟨heT, ?_⟩
  obtain ⟨heA, haa⟩ := ha k hka Δ s s' hΔ hs
  have hAΔ : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s A) (substA s' A) := (hA k hkA Δ s s' hΔ hs).2
  obtain ⟨_, hvA, _, tA, _, _⟩ := LRRelAL_sort_elim hAΔ
  have hup := ValidSubstAL_up hE hΔ hs heA hvA tA.1
  have hΔA : Nonempty (CtxWfA E noIotaA n (.assumption (substA s A) :: Δ)) :=
    hΔ.elim fun c => tA.1.elim fun t => ⟨.assumption c t⟩
  have hbup := (hb k hkb _ s.up s'.up hΔA hup).2
  obtain ⟨tbody, _⟩ := LRRelAL_hasTy hbup
  obtain ⟨RB, hRB⟩ := LRRelAL_valid hbup
  obtain ⟨v', tB⟩ := LRTyAL_hasTy hRB
  have hv := ValidSubstAL_cons hs heA haa
  have hbc := (hb k hkb Δ _ _ hΔ hv).2
  rw [← instantiate0A_substA_up, ← instantiate0A_substA_up, ← instantiate0A_substA_up] at hbc
  obtain ⟨tred, _⟩ := LRRelAL_hasTy hbc
  obtain ⟨RT, hRT⟩ := LRRelAL_valid hbc
  obtain ⟨w, tTy⟩ := LRTyAL_hasTy hRT
  obtain ⟨targ, _⟩ := LRRelAL_hasTy haa
  rw [substA_instantiate0A, substA_instantiate0A]
  have hst : StepAtAL E n σ N K Δ (.app (.lam (substA s A) u (substA s.up body)) (substA s arg))
      (instantiate0A (substA s arg) (substA s.up body)) (instantiate0A (substA s arg) (substA s.up B)) :=
    stepAtAL_beta_wk hE tA tB tbody [] ⟨trivial, hΔ⟩ targ tred tTy
  exact LRRelAL_expand_left hE hst hbc

theorem convArmZetaAL (hE : EnvClosedA E)
    {Γ : LCtxA} {A value body B : ExprA} {u : Level}
    (ihA : FundArmAL E n σ N K ρ₀ Γ A A (.sort u))
    (ihv : FundArmAL E n σ N K ρ₀ Γ value value A)
    (ihb : FundArmAL E n σ N K ρ₀ (.letBinding A value :: Γ) body body B)
    (ihr : FundArmAL E n σ N K ρ₀ Γ (instantiate0A value body) (instantiate0A value body) (instantiate0A value B)) :
    FundArmAL E n σ N K ρ₀ Γ (.letE A value body) (instantiate0A value body) (instantiate0A value B) := by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kv, hv⟩ := ihv
  obtain ⟨kb, hb⟩ := ihb
  obtain ⟨kr, hr⟩ := ihr
  refine ⟨max (max kA kv) (max kb kr), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkv : kv ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkb : kb ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨heT, _⟩ := hr k hkr Δ s s' hΔ hs
  refine ⟨heT, ?_⟩
  have hAΔ : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s A) (substA s' A) := (hA k hkA Δ s s' hΔ hs).2
  obtain ⟨heA, _, _, tA, _, _⟩ := LRRelAL_sort_elim hAΔ
  obtain ⟨_, hvv⟩ := hv k hkv Δ s s' hΔ hs
  obtain ⟨tv, _⟩ := LRRelAL_hasTy hvv
  have hupL := ValidSubstAL_upLet hE hΔ hs heA hvv tA.1
  have hΔL : Nonempty (CtxWfA E noIotaA n (.letBinding (substA s A) (substA s value) :: Δ)) :=
    hΔ.elim fun c => tA.1.elim fun t => tv.1.elim fun x => ⟨.letBinding c t x⟩
  have hbL := (hb k hkb _ s.up s'.up hΔL hupL).2
  obtain ⟨tbody, _⟩ := LRRelAL_hasTy hbL
  have hcons := ValidSubstAL_consLet hs heA hvv
  have hbc := (hb k hkb Δ _ _ hΔ hcons).2
  rw [← instantiate0A_substA_up, ← instantiate0A_substA_up, ← instantiate0A_substA_up] at hbc
  obtain ⟨tred, _⟩ := LRRelAL_hasTy hbc
  obtain ⟨RT, hRT⟩ := LRRelAL_valid hbc
  obtain ⟨w, tTy⟩ := LRTyAL_hasTy hRT
  rw [substA_instantiate0A, substA_instantiate0A]
  have tlet : HasTyAL E n σ N K Δ (.letE (substA s A) (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up B)) :=
    ⟨tA.1.elim fun a => tv.1.elim fun x => tTy.elim fun t => tbody.1.elim fun b =>
      ⟨.letE Δ _ u w _ _ _ a x t b⟩,
     tA.2.elim fun da hda => tv.2.elim fun dx hdx => tbody.2.elim fun db hdb =>
       ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (substA s.up B) (substA s value)).symm
         ⟨.letE (eraseCtx Δ) _ u _ _ _ da dx db, ⟨hda, hdx, hdb⟩⟩⟩
  have clet : ConvAL E n σ N K Δ (.letE (substA s A) (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up B)) :=
    ⟨tA.1.elim fun a => tv.1.elim fun x => tbody.1.elim fun b => tred.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b r⟩,
     tA.2.elim fun da hda => tv.2.elim fun dx hdx => tbody.2.elim fun db hdb =>
       ex_convT_lok_cast rfl rfl
         (erase_instantiate0A (substA s.up body) (substA s value)).symm
         (erase_instantiate0A (substA s.up B) (substA s value)).symm
         ⟨.zeta (eraseCtx Δ) _ _ _ _ u da dx db, ⟨hda, hdx, hdb⟩⟩⟩
  have hst : StepAtAL E n σ N K Δ (.letE (substA s A) (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up body))
      (instantiate0A (substA s value) (substA s.up B)) :=
    ⟨⟨tlet.1, tA.1.elim fun a => tv.1.elim fun x => tbody.1.elim fun b => tred.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b r⟩⟩, tlet, clet⟩
  exact LRRelAL_expand_left hE hst hbc

theorem convArmAppAL (hE : EnvClosedA E)
    {Γ : LCtxA} {f g a b A B : ExprA} {u v : Level}
    (ihfg : FundArmAL E n σ N K ρ₀ Γ f g (.pi A u B v))
    (ihab : FundArmAL E n σ N K ρ₀ Γ a b A)
    (ihB : FundArmAL E n σ N K ρ₀ (.assumption A :: Γ) B B (.sort v))
    (ihrt : FundArmAL E n σ N K ρ₀ Γ (.app g b) (.app g b) (instantiate0A a B)) :
    FundArmAL E n σ N K ρ₀ Γ (.app f a) (.app g b) (instantiate0A a B) := by
  obtain ⟨kf, hf⟩ := ihfg
  obtain ⟨ka, ha⟩ := ihab
  obtain ⟨kB, hB⟩ := ihB
  obtain ⟨kr, hr⟩ := ihrt
  refine ⟨max (max kf ka) (max kB kr), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkf : kf ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hka : ka ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkB : kB ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨heT, _⟩ := hr k hkr Δ s s' hΔ hs
  refine ⟨heT, ?_⟩
  obtain ⟨hepi, hfg⟩ := hf k hkf Δ s s' hΔ hs
  obtain ⟨heA, hab⟩ := ha k hka Δ s s' hΔ hs
  rw [substA_instantiate0A]
  cases hz : isZero v with
  | false =>
      have hnp : ¬ IsPropTy E noIotaA Δ (.pi (substA s A) u (substA s.up B) v) := fun h => by
        rw [(isPropTy_pi_iff E noIotaA Δ _ u _ v).1 h] at hz; cases hz
      exact LRRelAL_pi_elim hfg hnp [] ⟨trivial, hΔ⟩ (substA s a) (substA s' b) hab
  | true =>
      have hv := ValidSubstAL_cons hs heA hab
      have hBc := (hB k hkB Δ _ _ hΔ hv).2
      simp only [substA_sort, ← instantiate0A_substA_up] at hBc
      obtain ⟨⟨M, hMb, hMt⟩, _, tTy, tTy', _⟩ := LRRelAL_sortP_elim hz hBc
      have heBc := LREqAL_of_sortRel hBc
      obtain ⟨tf, tg⟩ := LRRelAL_hasTy hfg
      obtain ⟨ta, tb⟩ := LRRelAL_hasTy hab
      have cfg := LRRelAL_conv hfg
      have cab := LRRelAL_conv hab
      obtain ⟨RA, hRA⟩ := LRRelAL_valid hab
      obtain ⟨uA, tA⟩ := LRTyAL_hasTy hRA
      have hup := ValidSubstAL_up hE hΔ hs heA ⟨RA, hRA⟩ tA
      have hΔA : Nonempty (CtxWfA E noIotaA n (.assumption (substA s A) :: Δ)) :=
        hΔ.elim fun c => tA.elim fun t => ⟨.assumption c t⟩
      have hBup : LRRelAL E n σ N K ρ₀ k (.assumption (substA s A) :: Δ) (.sort v)
          (substA s.up B) (substA s'.up B) := (hB k hkB _ s.up s'.up hΔA hup).2
      obtain ⟨_, _, _, tB, _, _⟩ := LRRelAL_sort_elim hBup
      have heA' : LREqAL E n σ N K ρ₀ k Δ (substA s' A) (substA s' A) := LREqAL_trans (LREqAL_symm heA) heA
      obtain ⟨RA', hRA'⟩ := LREqAL_valid heA ⟨RA, hRA⟩
      obtain ⟨uA', tA'⟩ := LRTyAL_hasTy hRA'
      have hup' := ValidSubstAL_up hE hΔ (ValidSubstAL_refl_right hs) heA' ⟨RA', hRA'⟩ tA'
      have hΔA' : Nonempty (CtxWfA E noIotaA n (.assumption (substA s' A) :: Δ)) :=
        hΔ.elim fun c => tA'.elim fun t => ⟨.assumption c t⟩
      have hBup' : LRRelAL E n σ N K ρ₀ k (.assumption (substA s' A) :: Δ) (.sort v)
          (substA s'.up B) (substA s'.up B) := (hB k hkB _ s'.up s'.up hΔA' hup').2
      obtain ⟨_, _, _, tB', _, _⟩ := LRRelAL_sort_elim hBup'
      have tcpi := LREqAL_tyConv hepi
      have tcA := LREqAL_tyConv heA
      have tcBc := LREqAL_tyConv heBc
      have tapp : HasTyAL E n σ N K Δ (.app (substA s f) (substA s a))
          (instantiate0A (substA s a) (substA s.up B)) :=
        ⟨tB.1.elim fun b' => tTy.1.elim fun t => tf.1.elim fun x => ta.1.elim fun y =>
          ⟨.app Δ _ _ _ _ u v v b' t x y⟩,
         tf.2.elim fun dtf hdtf => ta.2.elim fun dta hdta =>
           ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (substA s.up B) (substA s a)).symm
             ⟨.app (eraseCtx Δ) _ _ _ _ dtf dta, ⟨hdtf, hdta⟩⟩⟩
      have tg_pi' := hasTyAL_of_tyConvAL tg tcpi
      have tb_A' := hasTyAL_of_tyConvAL tb tcA
      have tapp'_0 : HasTyAL E n σ N K Δ (.app (substA s' g) (substA s' b))
          (instantiate0A (substA s' b) (substA s'.up B)) :=
        ⟨tB'.1.elim fun b' => tTy'.1.elim fun t => tg_pi'.1.elim fun x => tb_A'.1.elim fun y =>
          ⟨.app Δ _ _ _ _ u v v b' t x y⟩,
         tg_pi'.2.elim fun dtg hdtg => tb_A'.2.elim fun dtb hdtb =>
           ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (substA s'.up B) (substA s' b)).symm
             ⟨.app (eraseCtx Δ) _ _ _ _ dtg dtb, ⟨hdtg, hdtb⟩⟩⟩
      have tapp' : HasTyAL E n σ N K Δ (.app (substA s' g) (substA s' b))
          (instantiate0A (substA s a) (substA s.up B)) :=
        hasTyAL_of_tyConvAL tapp'_0 (tyConvAL_symm tcBc)
      have capp : ConvAL E n σ N K Δ (.app (substA s f) (substA s a)) (.app (substA s' g) (substA s' b))
          (instantiate0A (substA s a) (substA s.up B)) :=
        ⟨cfg.1.elim fun c1 => cab.1.elim fun c2 => tB.1.elim fun b' => tapp'.1.elim fun t =>
          ⟨.app Δ _ _ _ _ _ _ u v c1 c2 b' t⟩,
         cfg.2.elim fun dcfg hdcfg => cab.2.elim fun dcab hdcab =>
           ex_convT_lok_cast rfl rfl rfl (erase_instantiate0A (substA s.up B) (substA s a)).symm
             ⟨.app (eraseCtx Δ) _ _ _ _ _ _ dcfg dcab, ⟨hdcfg, hdcab⟩⟩⟩
      refine ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hMb hMt, ?_⟩
      exact ⟨hasTyAL_of_tyConvAL tapp hMb.2, hasTyAL_of_tyConvAL tapp' hMb.2,
        convAL_of_tyConvAL capp hMb.2⟩

theorem convArmEtaAL (hE : EnvClosedA E)
    {Γ : LCtxA} {f A B : ExprA} {u v : Level}
    (ih : FundArmAL E n σ N K ρ₀ Γ f f (.pi A u B v))
    (ihrt : FundArmAL E n σ N K ρ₀ Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0)))
      (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v)) :
    FundArmAL E n σ N K ρ₀ Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) f (.pi A u B v) := by
  obtain ⟨kf, hf⟩ := ih
  obtain ⟨kl, hl⟩ := ihrt
  refine ⟨max kf kl, fun k hk Δ s s' hΔ hs => ?_⟩
  obtain ⟨hepi, hff⟩ := hf k (le_max_of_le₁ hk) Δ s s' hΔ hs
  obtain ⟨_, hll⟩ := hl k (le_max_of_le₂ hk) Δ s s' hΔ hs
  refine ⟨hepi, ?_⟩
  have elam : ∀ τ : SubstA, substA τ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) =
      .lam (substA τ A) u (.app (liftA 0 1 (substA τ f)) (.bvar 0)) := fun τ => by
    simp only [substA_lam, substA_app, substA_up_liftA, substA_bvar, SubstA.up_zero]
  simp only [elam] at hll ⊢
  obtain ⟨tf, tf'⟩ := LRRelAL_hasTy hff
  obtain ⟨tlam, _⟩ := LRRelAL_hasTy hll
  have cff := LRRelAL_conv hff
  obtain ⟨Rpi, hRpi⟩ := LRRelAL_valid hff
  obtain ⟨upi, tpi⟩ := LRTyAL_hasTy hRpi
  have hAB := tpi.elim fun t => hasTyA_pi_inv t
  obtain ⟨tA_ne, tB_ne⟩ := hAB
  have ceta_0 : ConvAL E n σ N K Δ (.lam (substA s A) u (.app (liftA 0 1 (substA s f)) (.bvar 0)))
      (substA s f) (.pi (substA s A) u (substA s.up B) v) :=
    ⟨tf.1.elim fun x => tlam.1.elim fun l => ⟨.eta Δ _ _ _ u v x l⟩,
     tf.2.elim fun dtf hdtf =>
       ex_convT_lok_cast rfl (by simp [erase, erase_liftA]) rfl rfl
         ⟨.eta (eraseCtx Δ) (erase (substA s f)) (erase (substA s A)) (erase (substA s.up B)) dtf,
          by simpa only [LOKc] using hdtf⟩⟩
  have ceta : ConvAL E n σ N K Δ (.lam (substA s A) u (.app (liftA 0 1 (substA s f)) (.bvar 0)))
      (substA s' f) (.pi (substA s A) u (substA s.up B) v) :=
    convAL_trans ceta_0 cff
  cases hz : isZero v with
  | true =>
      have hnf : TripleLikeA E noIotaA Δ (.pi (substA s A) u (substA s.up B) v) :=
        tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _) ((isPropTy_pi_iff E noIotaA Δ _ u _ v).2 hz)
      have hwh : WhTyAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v)
          (.pi (substA s A) u (substA s.up B) v) :=
        whTyAL_of_hasTy tpi
      refine ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hwh hnf, ?_⟩
      exact ⟨tlam, tf', ceta⟩
  | false =>
      have hnp : ¬ IsPropTy E noIotaA Δ (.pi (substA s A) u (substA s.up B) v) := fun h => by
        rw [(isPropTy_pi_iff E noIotaA Δ _ u _ v).1 h] at hz; cases hz
      rw [LRTyAL_eq] at hRpi
      obtain ⟨RD, RC, hD, hC, _, e⟩ := tyKAL_pi_inv hRpi hnp
      subst e
      have hRpi' : LRTyAL E n σ N K ρ₀ k Δ (.pi (substA s A) u (substA s.up B) v) (fun f g =>
          (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA, RD ρ a a' →
            RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
          HasTyAL E n σ N K Δ f (.pi (substA s A) u (substA s.up B) v) ∧
          HasTyAL E n σ N K Δ g (.pi (substA s A) u (substA s.up B) v) ∧
          ConvAL E n σ N K Δ f g (.pi (substA s A) u (substA s.up B) v)) := by
        rw [LRTyAL_eq]; exact hRpi
      refine ⟨_, hRpi', fun ρ hρ x x' hx => ?_, tlam, tf', ceta⟩
      have hK := (hff.at hRpi').1 ρ hρ x x' hx
      have hCx : LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
          (RC ρ x) := by rw [LRTyAL_eq]; exact hC ρ hρ x x' hx
      have hDx : LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (RD ρ) := by
        rw [LRTyAL_eq]; exact hD ρ hρ
      have hxx : LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) x x' := ⟨_, hDx, hx⟩
      obtain ⟨tx, _⟩ := LRRelAL_hasTy hxx
      have hK' : LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
          (.app (wkExprA ρ (substA s f)) x) (.app (wkExprA ρ (substA s' f)) x') := ⟨_, hCx, hK⟩
      obtain ⟨tred, _⟩ := LRRelAL_hasTy hK'
      obtain ⟨w, tTy⟩ := LRTyAL_hasTy hCx
      have tbody : HasTyAL E n σ N K (.assumption (substA s A) :: Δ)
          (.app (liftA 0 1 (substA s f)) (.bvar 0)) (substA s.up B) :=
        hasTyAL_eta_body hE tA_ne tB_ne tf
      have tred' : HasTyAL E n σ N K (wkCtxA ρ Δ)
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (.app (liftA 0 1 (substA s f)) (.bvar 0))))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B))) := by
        rw [eta_body_inst]; exact tred
      have tlam_w : HasTyAL E n σ N K (wkCtxA ρ Δ)
          (wkExprA ρ (.lam (substA s A) u (.app (liftA 0 1 (substA s f)) (.bvar 0))))
          (.pi (wkExprA ρ (substA s A)) u (wkExprA (WkSpecA.ub ρ) (substA s.up B)) v) := by
        have := hasTyAL_wk hE Δ ρ hρ.1 tlam
        rwa [substA_pi, wkExprA_pi_ub] at this
      have tredex : HasTyAL E n σ N K (wkCtxA ρ Δ)
          (.app (wkExprA ρ (.lam (substA s A) u (.app (liftA 0 1 (substA s f)) (.bvar 0)))) x)
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        ⟨tA_ne.elim fun a => tB_ne.elim fun b => tbody.1.elim fun tb => tx.1.elim fun t =>
          tred'.1.elim fun r => tTy.elim fun ty =>
            (stepAtA_beta_wk hE noIotaA_lift a b tb ρ hρ t r ty).1,
         tlam_w.2.elim fun dtl hdtl => tx.2.elim fun dtx hdtx =>
           ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) (substA s.up B)) x).symm
             ⟨.app _ _ _ _ _ dtl dtx, ⟨hdtl, hdtx⟩⟩⟩
      have hst : StepAtAL E n σ N K (wkCtxA ρ Δ)
          (.app (wkExprA ρ (.lam (substA s A) u (.app (liftA 0 1 (substA s f)) (.bvar 0)))) x)
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (.app (liftA 0 1 (substA s f)) (.bvar 0))))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        stepAtAL_beta_wk' hE tA_ne tlam tbody ρ hρ tx tred'.1 tredex
      have hK'' : LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (.app (liftA 0 1 (substA s f)) (.bvar 0))))
          (.app (wkExprA ρ (substA s' f)) x') := by
        rw [eta_body_inst]; exact hK'
      exact (LRRelAL_expand_left hE hst hK'').at hCx

theorem convArmPiAL (hE : EnvClosedA E) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {A A' B B' : ExprA} {u u' v v' : Level}
    (hu : eqN u u') (hv : eqN v v')
    (huN : evalTotal σ u ≤ N) (hvN : evalTotal σ v ≤ N)
    (huOK : SortEqOK σ N u u') (hvOK : SortEqOK σ N v v')
    (ihA : FundArmAL E n σ N K ρ₀ Γ A A' (.sort u))
    (ihB : FundArmAL E n σ N K ρ₀ (.assumption A :: Γ) B B' (.sort v))
    (ihrt : FundArmAL E n σ N K ρ₀ Γ (.pi A' u' B' v') (.pi A' u' B' v') (.sort (.imax u v))) :
    FundArmAL E n σ N K ρ₀ Γ (.pi A u B v) (.pi A' u' B' v') (.sort (.imax u v)) := by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kB, hB⟩ := ihB
  obtain ⟨kr, hr⟩ := ihrt
  refine ⟨max (max kA kB) (max kr (ht ρ₀ (.imax u v) + 1)), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkB : kB ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkr : kr ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkh : ht ρ₀ (.imax u v) < k := le_max_of_le₂ (le_max_of_le₂ hk)
  refine ⟨LREqAL_sort_refl Δ hkh, ?_⟩
  have hAΔ : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s A) (substA s' A') := (hA k hkA Δ s s' hΔ hs).2
  have hAΔ' : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s' A) (substA s' A') :=
    (hA k hkA Δ s' s' hΔ (ValidSubstAL_refl_right hs)).2
  obtain ⟨heAA', hvA, hvA'', tA, tA'', cAA'⟩ := LRRelAL_sort_elim hAΔ
  obtain ⟨heA'A', hvA', _, _, _, _⟩ := LRRelAL_sort_elim hAΔ'
  have heA : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A) := LREqAL_trans heAA' (LREqAL_symm heA'A')
  have heA' : LREqAL E n σ N K ρ₀ k Δ (substA s' A) (substA s' A) := LREqAL_trans (LREqAL_symm heA) heA
  have heD : LREqAL E n σ N K ρ₀ k Δ (substA s' A') (substA s' A) := LREqAL_symm heA'A'
  have hup := ValidSubstAL_up hE hΔ hs heA hvA tA.1
  have hup' := ValidSubstAL_up' hE hΔ (ValidSubstAL_refl_right hs) heA' heD hvA'' tA''.1
  have hΔA : Nonempty (CtxWfA E noIotaA n (.assumption (substA s A) :: Δ)) :=
    hΔ.elim fun c => tA.1.elim fun t => ⟨.assumption c t⟩
  have hΔA'' : Nonempty (CtxWfA E noIotaA n (.assumption (substA s' A') :: Δ)) :=
    hΔ.elim fun c => tA''.1.elim fun t => ⟨.assumption c t⟩
  have hBΔ : LRRelAL E n σ N K ρ₀ k (.assumption (substA s A) :: Δ) (.sort v)
      (substA s.up B) (substA s'.up B') := (hB k hkB _ s.up s'.up hΔA hup).2
  have hBΔ' : LRRelAL E n σ N K ρ₀ k (.assumption (substA s' A') :: Δ) (.sort v)
      (substA s'.up B) (substA s'.up B') := (hB k hkB _ s'.up s'.up hΔA'' hup').2
  obtain ⟨_, _, _, tB, _, cB⟩ := LRRelAL_sort_elim hBΔ
  obtain ⟨_, _, _, _, tB', _⟩ := LRRelAL_sort_elim hBΔ'
  have tpi : HasTyAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v) (.sort (.imax u v)) :=
    ⟨tA.1.elim fun a => tB.1.elim fun b => ⟨.pi Δ _ u _ v a b⟩,
     tA.2.elim fun da hda => tB.2.elim fun db hdb =>
       ⟨.pi (eraseCtx Δ) _ u _ v da db, ⟨huN, hvN, hda, hdb⟩⟩⟩
  have tpi' : HasTyAL E n σ N K Δ (.pi (substA s' A') u' (substA s'.up B') v') (.sort (.imax u v)) :=
    (LRRelAL_hasTy (hr k hkr Δ s s' hΔ hs).2).2
  have tA''u : HasTyAL E n σ N K Δ (substA s' A') (.sort u') :=
    hasTyAL_of_tyConvAL tA'' (tyConvAL_sorts Δ hu huOK)
  have tB'v : HasTyAL E n σ N K (.assumption (substA s' A') :: Δ) (substA s'.up B') (.sort v') :=
    hasTyAL_of_tyConvAL tB' (tyConvAL_sorts _ hv hvOK)
  have cpi : ConvAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v)
      (.pi (substA s' A') u' (substA s'.up B') v') (.sort (.imax u v)) :=
    ⟨cAA'.1.elim fun a => cB.1.elim fun b => tpi'.1.elim fun t =>
      ⟨.pi Δ _ _ _ _ u u' v v' hu hv a b t⟩,
     cAA'.2.elim fun da hda => cB.2.elim fun db hdb =>
       ⟨.pi (eraseCtx Δ) _ _ _ _ u v da db, ⟨huN, hvN, hda, hdb⟩⟩⟩
  have tyc : TyConvAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v)
      (.pi (substA s' A') u' (substA s'.up B') v') :=
    tyConvAL_of_convAL tpi.1 (eqNA_refl _) tpi'.1 (eqNA_refl _) cpi
  have hS : WhTyAL E n σ N K Δ (.sort (.imax u v)) (.sort (.imax u v)) :=
    whTyAL_of_hasTy ⟨.sort Δ _⟩
  have hzv : isZero v' = isZero v := (isZero_eqN hv).symm
  cases hz : isZero v with
  | true =>
      have hz' : isZero (.imax u v) = true := by rw [isZero_imax]; exact hz
      have hzv' : isZero v' = true := by rw [hzv]; exact hz
      refine ⟨_, by rw [LRTyAL_eq]; exact .sortP hS hz', ?_⟩
      refine ⟨⟨_, whTyAL_of_hasTy tpi.1, tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _)
        ((isPropTy_pi_iff E noIotaA Δ _ u _ v).2 hz)⟩,
        ⟨_, whTyAL_of_hasTy tpi'.1, tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _)
        ((isPropTy_pi_iff E noIotaA Δ _ u' _ v').2 hzv')⟩, tpi, tpi', cpi, ?_⟩
      exact .pi (whTyAL_of_hasTy tpi.1) (whTyAL_of_hasTy tpi'.1) hu hv tA.1 tA''u.1
        (fun ρ hρ' => tyConvAL_wk hE Δ ρ hρ'.1
          (tyConvAL_of_convAL tA.1 (eqNA_refl u) tA''.1 (eqNA_refl u) cAA'))
        (propEqAL_codom_of_fund hE hz hB hkB hs heA hvA) tyc
  | false =>
      have hzv' : isZero v' = false := by rw [hzv]; exact hz
      have hvpos : 0 < ht ρ₀ v := ht_pos_of_isZero_false hρ v hz
      have hh : ht ρ₀ (.imax u v) = max (ht ρ₀ u) (ht ρ₀ v) := ht_imax_of_pos hvpos
      have hz' : isZero (.imax u v) = false := by rw [isZero_imax]; exact hz
      have hu_le : ht ρ₀ u ≤ ht ρ₀ (.imax u v) := by rw [hh]; exact Nat.le_max_left _ _
      have hv_le : ht ρ₀ v ≤ ht ρ₀ (.imax u v) := by rw [hh]; exact Nat.le_max_right _ _
      have hhk : ht ρ₀ (.imax u v) ≤ k := Nat.le_of_lt hkh
      have wAA' := fun (ρ : WkSpecA) (hρ' : WkOkA E noIotaA n ρ Δ) =>
        fundArm_sort_wkAL hE hA hkA hs ρ hρ'
      have wA'A' := fun (ρ : WkSpecA) (hρ' : WkOkA E noIotaA n ρ Δ) =>
        fundArm_sort_wkAL hE hA hkA (ValidSubstAL_refl_right hs) ρ hρ'
      have eA : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
          LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A)) :=
        fun ρ hρ' => LREqAL_trans (LREqAL_of_sortRel (wAA' ρ hρ')) (LREqAL_symm (LREqAL_of_sortRel (wA'A' ρ hρ')))
      have eA0 : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
          LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s A)) :=
        fun ρ hρ' => LREqAL_trans (eA ρ hρ') (LREqAL_symm (eA ρ hρ'))
      have eA' : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
          LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s' A)) (wkExprA ρ (substA s' A)) :=
        fun ρ hρ' => LREqAL_trans (LREqAL_symm (eA ρ hρ')) (eA ρ hρ')
      have dA : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
          LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A')) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) R) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s' A')) R) :=
        fun ρ hρ' => (LRRelAL_sort_elim' (wAA' ρ hρ')).1 _ hu_le
      have dB : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
          LRRelAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) a a' →
          LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s'.up B'))) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up B))) R) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s'.up B'))) R) :=
        fun ρ hρ' a a' haa => (LRRelAL_sort_elim' (fundArm_cons_wk_sortAL hE hB hkB hs ρ hρ'
          (eA ρ hρ') (LRRelAL_mono hhk haa))).1 _ hv_le
      have dB0 : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
          LRRelAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) a a' →
          LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        fun ρ hρ' a a' haa =>
          let r1 := ((LRRelAL_sort_elim' (fundArm_cons_wk_sortAL hE hB hkB (ValidSubstAL_refl_left hs) ρ hρ'
            (eA0 ρ hρ') (LRRelAL_mono hhk haa))).1 _ hv_le).1
          let r2 := ((LRRelAL_sort_elim' (fundArm_cons_wk_sortAL hE hB hkB (ValidSubstAL_refl_left hs) ρ hρ'
            (eA0 ρ hρ') (LRRelAL_mono hhk (LRRelAL_refl_left (LRRelAL_symm haa))))).1 _ hv_le).1
          LREqAL_trans r1 (LREqAL_symm r2)
      have dB' : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
          LRRelAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ) (wkExprA ρ (substA s' A')) a a' →
          LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s'.up B')))
            (instantiate0A a' (wkExprA (WkSpecA.ub ρ) (substA s'.up B'))) ∧
          (∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) (wkCtxA ρ Δ)
            (instantiate0A a (wkExprA (WkSpecA.ub ρ) (substA s'.up B'))) R) :=
        fun ρ hρ' a a' haa =>
          let haa0 : LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s' A)) a a' :=
            LRRelAL_transport' (LREqAL_symm (LREqAL_of_sortRel (wA'A' ρ hρ'))) (LRRelAL_mono hhk haa)
          let haa1 : LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s' A)) a a :=
            LRRelAL_refl_left haa0
          let r1 := (LRRelAL_sort_elim' (fundArm_cons_wk_sortAL hE hB hkB (ValidSubstAL_refl_right hs) ρ hρ'
            (eA' ρ hρ') haa0)).1 _ hv_le
          let r2 := (LRRelAL_sort_elim' (fundArm_cons_wk_sortAL hE hB hkB (ValidSubstAL_refl_right hs) ρ hρ'
            (eA' ρ hρ') haa1)).1 _ hv_le
          ⟨LREqAL_trans (LREqAL_symm r2.1) r1.1, r2.2.2⟩
      have hT1 : ∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA s A) u (substA s.up B) v) R :=
        tA.1.elim fun a => tB.1.elim fun b =>
          ⟨_, piTyAL_of_data hz a b (fun ρ hρ' => (dA ρ hρ').2.1)
            (fun ρ hρ' a a' haa => (dB ρ hρ' a a' haa).2.1) dB0⟩
      have hT2 : ∃ R, LRTyAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA s' A') u' (substA s'.up B') v') R :=
        tA''u.1.elim fun a' => tB'v.1.elim fun b' =>
          ⟨_, piTyAL_of_data hzv' a' b' (fun ρ hρ' => (dA ρ hρ').2.2)
            (fun ρ hρ' a a' haa => (dB' ρ hρ' a a' haa).2)
            (fun ρ hρ' a a' haa => (dB' ρ hρ' a a' haa).1)⟩
      have hEq : LREqAL E n σ N K ρ₀ (ht ρ₀ (.imax u v)) Δ (.pi (substA s A) u (substA s.up B) v)
          (.pi (substA s' A') u' (substA s'.up B') v') :=
        tA.1.elim fun a => tB.1.elim fun b => tA''u.1.elim fun a' => tB'v.1.elim fun b' =>
          piEqAL_of_data hu hv a b a' b' (fun ρ hρ' => (dA ρ hρ').1) (fun ρ hρ' => (dA ρ hρ').2.1)
            (fun ρ hρ' a haa => (dB ρ hρ' a a haa).1) tyc
      refine ⟨_, by rw [LRTyAL_eq]; exact .sortT hS hz' hkh, ?_⟩
      exact ⟨hEq, hT1, hT2, tpi, tpi', cpi⟩

theorem convArmLamAL (hE : EnvClosedA E)
    {Γ : LCtxA} {A A' b b' B : ExprA} {u u' v : Level}
    (hu : eqN u u') (huOK : SortEqOK σ N u u')
    (ihA : FundArmAL E n σ N K ρ₀ Γ A A' (.sort u))
    (ihb : FundArmAL E n σ N K ρ₀ (.assumption A :: Γ) b b' B)
    (ihrt : FundArmAL E n σ N K ρ₀ Γ (.lam A' u' b') (.lam A' u' b') (.pi A u B v)) :
    FundArmAL E n σ N K ρ₀ Γ (.lam A u b) (.lam A' u' b') (.pi A u B v) := by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kb, hb⟩ := ihb
  obtain ⟨kr, hr⟩ := ihrt
  refine ⟨max kA (max kb kr), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ hk
  have hkb : kb ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨hepi, hll⟩ := hr k hkr Δ s s' hΔ hs
  refine ⟨hepi, ?_⟩
  have hAΔ : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s A) (substA s' A') := (hA k hkA Δ s s' hΔ hs).2
  have hAΔ' : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s' A) (substA s' A') :=
    (hA k hkA Δ s' s' hΔ (ValidSubstAL_refl_right hs)).2
  obtain ⟨heAA', hvA, hvA'', tA, tA'', cAA'⟩ := LRRelAL_sort_elim hAΔ
  obtain ⟨heA'A', _, _, _, _, _⟩ := LRRelAL_sort_elim hAΔ'
  have heA : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A) := LREqAL_trans heAA' (LREqAL_symm heA'A')
  obtain ⟨Rpi, hRpi⟩ := LRRelAL_valid hll
  obtain ⟨upi, tpi⟩ := LRTyAL_hasTy hRpi
  have hAB := tpi.elim fun t => hasTyA_pi_inv t
  obtain ⟨_, tB_ne⟩ := hAB
  have hup := ValidSubstAL_up hE hΔ hs heA hvA tA.1
  have hup' := ValidSubstAL_up' hE hΔ hs heA (LREqAL_symm heAA') hvA'' tA''.1
  have hΔA : Nonempty (CtxWfA E noIotaA n (.assumption (substA s A) :: Δ)) :=
    hΔ.elim fun c => tA.1.elim fun t => ⟨.assumption c t⟩
  have hΔA'' : Nonempty (CtxWfA E noIotaA n (.assumption (substA s' A') :: Δ)) :=
    hΔ.elim fun c => tA''.1.elim fun t => ⟨.assumption c t⟩
  have hbΔ : LRRelAL E n σ N K ρ₀ k (.assumption (substA s A) :: Δ) (substA s.up B)
      (substA s.up b) (substA s'.up b') := (hb k hkb _ s.up s'.up hΔA hup).2
  have hbΔ' : LRRelAL E n σ N K ρ₀ k (.assumption (substA s' A') :: Δ) (substA s.up B)
      (substA s.up b) (substA s'.up b') := (hb k hkb _ s.up s'.up hΔA'' hup').2
  obtain ⟨tb, _⟩ := LRRelAL_hasTy hbΔ
  obtain ⟨_, tb'⟩ := LRRelAL_hasTy hbΔ'
  have cb := LRRelAL_conv hbΔ
  have tlam : HasTyAL E n σ N K Δ (.lam (substA s A) u (substA s.up b))
      (.pi (substA s A) u (substA s.up B) v) :=
    ⟨tA.1.elim fun a => tB_ne.elim fun b₀ => tb.1.elim fun t => ⟨.lam Δ _ u _ _ v a b₀ t⟩,
     tA.2.elim fun da hda => tb.2.elim fun dtb hdtb =>
       ⟨.lam (eraseCtx Δ) _ u _ _ da dtb, ⟨hda, hdtb⟩⟩⟩
  have tlam' : HasTyAL E n σ N K Δ (.lam (substA s' A') u' (substA s'.up b'))
      (.pi (substA s A) u (substA s.up B) v) := (LRRelAL_hasTy hll).2
  have clam : ConvAL E n σ N K Δ (.lam (substA s A) u (substA s.up b))
      (.lam (substA s' A') u' (substA s'.up b')) (.pi (substA s A) u (substA s.up B) v) :=
    ⟨cAA'.1.elim fun a => cb.1.elim fun c => tlam'.1.elim fun t => ⟨.lam Δ _ _ _ _ _ u u' v hu a c t⟩,
     cAA'.2.elim fun da hda => cb.2.elim fun dcb hdcb =>
       ⟨.lam (eraseCtx Δ) _ _ _ _ _ u da dcb, ⟨hda, hdcb⟩⟩⟩
  have tA''u : HasTyAL E n σ N K Δ (substA s' A') (.sort u') :=
    hasTyAL_of_tyConvAL tA'' (tyConvAL_sorts Δ hu huOK)
  have eA : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
      LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A)) :=
    fun ρ hρ' => LREqAL_trans (LREqAL_of_sortRel (fundArm_sort_wkAL hE hA hkA hs ρ hρ'))
      (LREqAL_symm (LREqAL_of_sortRel (fundArm_sort_wkAL hE hA hkA (ValidSubstAL_refl_right hs) ρ hρ')))
  have eAA' : ∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ →
      LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (wkExprA ρ (substA s' A')) :=
    fun ρ hρ' => LREqAL_of_sortRel (fundArm_sort_wkAL hE hA hkA hs ρ hρ')
  cases hz : isZero v with
  | true =>
      have hnf : TripleLikeA E noIotaA Δ (.pi (substA s A) u (substA s.up B) v) :=
        tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _) ((isPropTy_pi_iff E noIotaA Δ _ u _ v).2 hz)
      have hwh : WhTyAL E n σ N K Δ (.pi (substA s A) u (substA s.up B) v)
          (.pi (substA s A) u (substA s.up B) v) :=
        whTyAL_of_hasTy tpi
      refine ⟨_, by rw [LRTyAL_eq]; exact tyKAL_of_tripleLike hwh hnf, ?_⟩
      exact ⟨tlam, tlam', clam⟩
  | false =>
      have hnp : ¬ IsPropTy E noIotaA Δ (.pi (substA s A) u (substA s.up B) v) := fun h => by
        rw [(isPropTy_pi_iff E noIotaA Δ _ u _ v).1 h] at hz; cases hz
      rw [LRTyAL_eq] at hRpi
      obtain ⟨RD, RC, hD, hC, hCeq, e⟩ := tyKAL_pi_inv hRpi hnp
      subst e
      have hRpi' : LRTyAL E n σ N K ρ₀ k Δ (.pi (substA s A) u (substA s.up B) v) (fun f g =>
          (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA, RD ρ a a' →
            RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
          HasTyAL E n σ N K Δ f (.pi (substA s A) u (substA s.up B) v) ∧
          HasTyAL E n σ N K Δ g (.pi (substA s A) u (substA s.up B) v) ∧
          ConvAL E n σ N K Δ f g (.pi (substA s A) u (substA s.up B) v)) := by
        rw [LRTyAL_eq]; exact hRpi
      refine ⟨_, hRpi', fun ρ hρ' x x' hx => ?_, tlam, tlam', clam⟩
      have hDx : LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) (RD ρ) := by
        rw [LRTyAL_eq]; exact hD ρ hρ'
      have hxx : LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ (substA s A)) x x' := ⟨_, hDx, hx⟩
      have hCx : LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
          (RC ρ x) := by rw [LRTyAL_eq]; exact hC ρ hρ' x x' hx
      have hCx' : LRTyAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
          (RC ρ x') := by
        rw [LRTyAL_eq]
        exact hC ρ hρ' x' x' ((LRRelAL_refl_left (LRRelAL_symm hxx)).at hDx)
      have hCeqx : LREqAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B)))
          (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA s.up B))) := by
        rw [LREqAL_eq]; exact hCeq ρ hρ' x x' hx
      have ih := fundArm_cons_wkAL hE hb hkb hs ρ hρ' (eA ρ hρ') hxx
      obtain ⟨tx, tx'⟩ := LRRelAL_hasTy hxx
      obtain ⟨tred, tred'⟩ := LRRelAL_hasTy ih.2
      obtain ⟨w₁, tTy⟩ := LRTyAL_hasTy hCx
      obtain ⟨w₂, tTy'⟩ := LRTyAL_hasTy hCx'
      have tcC := LREqAL_tyConv hCeqx
      have tcAA' := LREqAL_tyConv (eAA' ρ hρ')
      have hsL : StepAtAL E n σ N K (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam (substA s A) u (substA s.up b))) x)
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up b)))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        stepAtAL_beta_wk hE tA tB_ne tb ρ hρ' tx tred tTy
      have tB_w : Nonempty (HasTyA E noIotaA n (.assumption (wkExprA ρ (substA s A)) :: wkCtxA ρ Δ)
          (wkExprA (WkSpecA.ub ρ) (substA s.up B)) (.sort v)) :=
        hasTyA_wk_ne_binder hE noIotaA_lift ρ hρ'.1 tB_ne
      have tlam'_w : HasTyAL E n σ N K (wkCtxA ρ Δ) (wkExprA ρ (.lam (substA s' A') u' (substA s'.up b')))
          (.pi (wkExprA ρ (substA s A)) u (wkExprA (WkSpecA.ub ρ) (substA s.up B)) v) := by
        have := hasTyAL_wk hE Δ ρ hρ'.1 tlam'
        rwa [wkExprA_pi_ub] at this
      have tredex : HasTyAL E n σ N K (wkCtxA ρ Δ)
          (.app (wkExprA ρ (.lam (substA s' A') u' (substA s'.up b'))) x')
          (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        ⟨tB_w.elim fun hB' => tTy'.elim fun ty' => tlam'_w.1.elim fun hf => tx'.1.elim fun t' =>
          ⟨.app _ _ _ _ _ u v w₂ hB' ty' hf t'⟩,
         tlam'_w.2.elim fun dtl hdtl => tx'.2.elim fun dtx' hdtx' =>
           ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (wkExprA (WkSpecA.ub ρ) (substA s.up B)) x').symm
             ⟨.app _ _ _ _ _ dtl dtx', ⟨hdtl, hdtx'⟩⟩⟩
      have hsR : StepAtAL E n σ N K (wkCtxA ρ Δ) (.app (wkExprA ρ (.lam (substA s' A') u' (substA s'.up b'))) x')
          (instantiate0A x' (wkExprA (WkSpecA.ub ρ) (substA s'.up b')))
          (instantiate0A x (wkExprA (WkSpecA.ub ρ) (substA s.up B))) :=
        stepAtAL_tyConv (stepAtAL_beta_wk' hE tA''u.1 tlam' tb' ρ hρ'
          (hasTyAL_of_tyConvAL tx' tcAA')
          (hasTyAL_of_tyConvAL tred' tcC).1 tredex) (tyConvAL_symm tcC)
      exact (LRRelAL_expand_left hE hsL (LRRelAL_expand_right hE hsR ih.2)).at hCx

theorem convArmLetEAL (hE : EnvClosedA E)
    {Γ : LCtxA} {A A' v v' b b' B : ExprA} {u : Level}
    (ihA : FundArmAL E n σ N K ρ₀ Γ A A' (.sort u))
    (ihv : FundArmAL E n σ N K ρ₀ Γ v v' A)
    (ihb : FundArmAL E n σ N K ρ₀ (.letBinding A v :: Γ) b b' B)
    (ihrt : FundArmAL E n σ N K ρ₀ Γ (.letE A' v' b') (.letE A' v' b') (instantiate0A v B)) :
    FundArmAL E n σ N K ρ₀ Γ (.letE A v b) (.letE A' v' b') (instantiate0A v B) := by
  obtain ⟨kA, hA⟩ := ihA
  obtain ⟨kv, hv⟩ := ihv
  obtain ⟨kb, hb⟩ := ihb
  obtain ⟨kr, hr⟩ := ihrt
  refine ⟨max (max kA kv) (max kb kr), fun k hk Δ s s' hΔ hs => ?_⟩
  have hkA : kA ≤ k := le_max_of_le₁ (le_max_of_le₁ hk)
  have hkv : kv ≤ k := le_max_of_le₂ (le_max_of_le₁ hk)
  have hkb : kb ≤ k := le_max_of_le₁ (le_max_of_le₂ hk)
  have hkr : kr ≤ k := le_max_of_le₂ (le_max_of_le₂ hk)
  obtain ⟨heT, hrr⟩ := hr k hkr Δ s s' hΔ hs
  refine ⟨heT, ?_⟩
  have hAΔ : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s A) (substA s' A') := (hA k hkA Δ s s' hΔ hs).2
  have hAΔ' : LRRelAL E n σ N K ρ₀ k Δ (.sort u) (substA s' A) (substA s' A') :=
    (hA k hkA Δ s' s' hΔ (ValidSubstAL_refl_right hs)).2
  obtain ⟨heAA', hvA, _, tA, tA'', _⟩ := LRRelAL_sort_elim hAΔ
  obtain ⟨heA'A', _, _, _, _, _⟩ := LRRelAL_sort_elim hAΔ'
  have heA : LREqAL E n σ N K ρ₀ k Δ (substA s A) (substA s' A) := LREqAL_trans heAA' (LREqAL_symm heA'A')
  obtain ⟨_, hvv'⟩ := hv k hkv Δ s s' hΔ hs
  obtain ⟨_, hv'v'⟩ := hv k hkv Δ s' s' hΔ (ValidSubstAL_refl_right hs)
  have hvv : LRRelAL E n σ N K ρ₀ k Δ (substA s A) (substA s v) (substA s' v) :=
    LRRelAL_trans hvv' (LRRelAL_symm (LRRelAL_transport' (LREqAL_symm heA) hv'v'))
  obtain ⟨tv, _⟩ := LRRelAL_hasTy hvv
  have tv'' : HasTyAL E n σ N K Δ (substA s' v') (substA s' A') :=
    (LRRelAL_hasTy (LRRelAL_transport' heAA' hvv')).2
  have hcons := ValidSubstAL_consLet' hs heA hvv' hvv
  have hbc := (hb k hkb Δ _ _ hΔ hcons).2
  simp only [← instantiate0A_substA_up] at hbc
  rw [substA_instantiate0A]
  -- left ζ-step
  have hupL := ValidSubstAL_upLet hE hΔ hs heA hvv tA.1
  have hΔL : Nonempty (CtxWfA E noIotaA n (.letBinding (substA s A) (substA s v) :: Δ)) :=
    hΔ.elim fun c => tA.1.elim fun t => tv.1.elim fun x => ⟨.letBinding c t x⟩
  have hbL := (hb k hkb _ s.up s'.up hΔL hupL).2
  obtain ⟨tb, _⟩ := LRRelAL_hasTy hbL
  obtain ⟨tred, tred'⟩ := LRRelAL_hasTy hbc
  obtain ⟨RT, hRT⟩ := LRRelAL_valid hbc
  obtain ⟨w, tTy⟩ := LRTyAL_hasTy hRT
  have tletL : HasTyAL E n σ N K Δ (.letE (substA s A) (substA s v) (substA s.up b))
      (instantiate0A (substA s v) (substA s.up B)) :=
    ⟨tA.1.elim fun a => tv.1.elim fun x => tTy.elim fun t => tb.1.elim fun b₀ =>
      ⟨.letE Δ _ u w _ _ _ a x t b₀⟩,
     tA.2.elim fun da hda => tv.2.elim fun dx hdx => tb.2.elim fun db hdb =>
       ex_hasTyT_lok_cast rfl rfl (erase_instantiate0A (substA s.up B) (substA s v)).symm
         ⟨.letE (eraseCtx Δ) _ u _ _ _ da dx db, ⟨hda, hdx, hdb⟩⟩⟩
  have cletL : ConvAL E n σ N K Δ (.letE (substA s A) (substA s v) (substA s.up b))
      (instantiate0A (substA s v) (substA s.up b)) (instantiate0A (substA s v) (substA s.up B)) :=
    ⟨tA.1.elim fun a => tv.1.elim fun x => tb.1.elim fun b₀ => tred.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b₀ r⟩,
     tA.2.elim fun da hda => tv.2.elim fun dx hdx => tb.2.elim fun db hdb =>
       ex_convT_lok_cast rfl rfl
         (erase_instantiate0A (substA s.up b) (substA s v)).symm
         (erase_instantiate0A (substA s.up B) (substA s v)).symm
         ⟨.zeta (eraseCtx Δ) _ _ _ _ u da dx db, ⟨hda, hdx, hdb⟩⟩⟩
  have hsL : StepAtAL E n σ N K Δ (.letE (substA s A) (substA s v) (substA s.up b))
      (instantiate0A (substA s v) (substA s.up b)) (instantiate0A (substA s v) (substA s.up B)) :=
    ⟨⟨tletL.1, tA.1.elim fun a => tv.1.elim fun x => tb.1.elim fun b₀ => tred.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b₀ r⟩⟩, tletL, cletL⟩
  -- right ζ-step via ValidSubstAL_upLet_gen and ValidSubstAL_consLet'
  have hupR := ValidSubstAL_upLet_gen hE hΔ hs heA heAA' hvv' hvv tA''.1
  have hΔR : Nonempty (CtxWfA E noIotaA n (.letBinding (substA s' A') (substA s' v') :: Δ)) :=
    hΔ.elim fun c => tA''.1.elim fun t => tv''.1.elim fun x => ⟨.letBinding c t x⟩
  have hbR := (hb k hkb _ s.up s'.up hΔR hupR).2
  obtain ⟨_, tb'⟩ := LRRelAL_hasTy hbR
  have hcons0 := ValidSubstAL_consLet' (ValidSubstAL_refl_left hs)
    (LREqAL_trans heA (LREqAL_symm heA)) hvv' (LRRelAL_refl_left hvv)
  have heB0 : LREqAL E n σ N K ρ₀ k Δ (instantiate0A (substA s v) (substA s.up B))
      (instantiate0A (substA s' v') (substA s.up B)) := by
    have := (hb k hkb Δ _ _ hΔ hcons0).1
    simpa only [← instantiate0A_substA_up] using this
  have tcB0 := LREqAL_tyConv heB0
  have tR : HasTyAL E n σ N K Δ (.letE (substA s' A') (substA s' v') (substA s'.up b'))
      (instantiate0A (substA s v) (substA s.up B)) := by
    have := (LRRelAL_hasTy hrr).2
    rwa [substA_instantiate0A] at this
  have tR_0 : HasTyAL E n σ N K Δ (.letE (substA s' A') (substA s' v') (substA s'.up b'))
      (instantiate0A (substA s' v') (substA s.up B)) :=
    hasTyAL_of_tyConvAL tR tcB0
  have tred'_0 : HasTyAL E n σ N K Δ (instantiate0A (substA s' v') (substA s'.up b'))
      (instantiate0A (substA s' v') (substA s.up B)) :=
    hasTyAL_of_tyConvAL tred' tcB0
  have cletR_0 : ConvAL E n σ N K Δ (.letE (substA s' A') (substA s' v') (substA s'.up b'))
      (instantiate0A (substA s' v') (substA s'.up b'))
      (instantiate0A (substA s' v') (substA s.up B)) :=
    ⟨tA''.1.elim fun a => tv''.1.elim fun x => tb'.1.elim fun b₀ => tred'_0.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b₀ r⟩,
     tA''.2.elim fun da hda => tv''.2.elim fun dx hdx => tb'.2.elim fun db hdb =>
       ex_convT_lok_cast rfl rfl
         (erase_instantiate0A (substA s'.up b') (substA s' v')).symm
         (erase_instantiate0A (substA s.up B) (substA s' v')).symm
         ⟨.zeta (eraseCtx Δ) _ _ _ _ u da dx db, ⟨hda, hdx, hdb⟩⟩⟩
  have hsR_0 : StepAtAL E n σ N K Δ (.letE (substA s' A') (substA s' v') (substA s'.up b'))
      (instantiate0A (substA s' v') (substA s'.up b'))
      (instantiate0A (substA s' v') (substA s.up B)) :=
    ⟨⟨tR_0.1, tA''.1.elim fun a => tv''.1.elim fun x => tb'.1.elim fun b₀ => tred'_0.1.elim fun r =>
      ⟨.zeta Δ _ _ _ _ u a x b₀ r⟩⟩, tR_0, cletR_0⟩
  have hsR : StepAtAL E n σ N K Δ (.letE (substA s' A') (substA s' v') (substA s'.up b'))
      (instantiate0A (substA s' v') (substA s'.up b'))
      (instantiate0A (substA s v) (substA s.up B)) :=
    stepAtAL_tyConv hsR_0 (tyConvAL_symm tcB0)
  exact LRRelAL_expand_left hE hsL (LRRelAL_expand_right hE hsR hbc)

mutual
/-- `LOKc`-indexed fundamental theorem on the copy (typing half). -/
theorem fundHasTyAL (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀) :
    {Γ : LCtxA} → {e A : ExprA} → (d : HasTyA E noIotaA n Γ e A) →
      LOKtA σ N K d → FundArmAL E n σ N K ρ₀ Γ e e A
  | _, _, _, .sort Γ l, hd => hasTyArmSortAL Γ l hd
  | _, _, _, .bvar _ _ _ _ h _, _ => hasTyArmBvarAL h
  | _, _, _, .const _ _ _ _ _ hres hlen hwf hT, hd =>
      hasTyArmConstAL hE hS hres hlen hwf hd.1 (fundHasTyAL hE hS hρ hT hd.2)
  | _, _, _, .pi _ _ _ _ _ hA hB, hd =>
      hasTyArmPiAL hE hρ hd.1 hd.2.1 (fundHasTyAL hE hS hρ hA hd.2.2.1) (fundHasTyAL hE hS hρ hB hd.2.2.2)
  | _, _, _, .lam _ _ _ _ _ _ hA hB hbody, hd =>
      hasTyArmLamAL hE hd.1 hd.2.1 (fundHasTyAL hE hS hρ hA hd.2.2.1)
        (fundHasTyAL hE hS hρ hB hd.2.2.2.1) (fundHasTyAL hE hS hρ hbody hd.2.2.2.2)
  | _, _, _, .app _ _ _ _ _ _ _ _ hB hTy hf ha, hd =>
      hasTyArmAppAL hE (fundHasTyAL hE hS hρ hB hd.1) (fundHasTyAL hE hS hρ hTy hd.2.1)
        (fundHasTyAL hE hS hρ hf hd.2.2.1) (fundHasTyAL hE hS hρ ha hd.2.2.2)
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hTy hb, hd =>
      hasTyArmLetEAL hE (fundHasTyAL hE hS hρ hA hd.1) (fundHasTyAL hE hS hρ hv hd.2.1)
        (fundHasTyAL hE hS hρ hTy hd.2.2.1) (fundHasTyAL hE hS hρ hb hd.2.2.2)
  | _, _, _, .lit _ t _ hexp, hd =>
      hasTyArmLitAL hE t (fundHasTyAL hE hS hρ hexp hd)
  | _, _, _, .conv _ _ _ _ _ _ h _ _ hB hc, hd =>
      hasTyArmConvAL (fundHasTyAL hE hS hρ h hd.1) (fundHasTyAL hE hS hρ hB hd.2.2.1)
        (fundConvAL hE hS hρ hc hd.2.2.2)

/-- `LOKc`-indexed fundamental theorem on the copy (conversion half). -/
theorem fundConvAL (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀) :
    {Γ : LCtxA} → {a b A : ExprA} → (d : ConvA E noIotaA n Γ a b A) →
      LOKcA σ N K d → FundArmAL E n σ N K ρ₀ Γ a b A
  | _, _, _, _, .refl _ _ _ h, hd => fundHasTyAL hE hS hρ h hd
  | _, _, _, _, .symm _ _ _ _ h, hd => convArmSymmAL (fundConvAL hE hS hρ h hd)
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, hd =>
      convArmTransAL (fundConvAL hE hS hρ h1 hd.1) (fundConvAL hE hS hρ h2 hd.2)
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg hred, hd =>
      convArmBetaAL hE (fundHasTyAL hE hS hρ hA hd.1) (fundHasTyAL hE hS hρ hbody hd.2.1)
        (fundHasTyAL hE hS hρ harg hd.2.2.1) (fundHasTyAL hE hS hρ hred hd.2.2.2)
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb hred, hd =>
      convArmZetaAL hE (fundHasTyAL hE hS hρ hA hd.1) (fundHasTyAL hE hS hρ hv hd.2.1)
        (fundHasTyAL hE hS hρ hb hd.2.2.1) (fundHasTyAL hE hS hρ hred hd.2.2.2)
  | _, _, _, _, .zetaLocal _ _ _ _ hval hty hv, hd =>
      convArmZetaLocalAL hval hty (fundHasTyAL hE hS hρ hv hd)
  | _, _, _, _, .delta _ _ _ _ _ hres hbody htr hlen hwf hb, hd =>
      convArmDeltaAL hE hres hbody htr hlen hwf hd.1 (fundHasTyAL hE hS hρ hb hd.2)
  | _, _, _, _, .iota _ _ _ _ _ _ _, hd => False.elim hd
  | _, _, _, _, .structIota _ _ _ _ _ _ _ _ _ _ _ _, hd => False.elim hd
  | _, _, _, _, .lit _ t _ hexp, hd =>
      convArmLitAL hE t (fundHasTyAL hE hS hρ hexp hd)
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 hB hrt, hd =>
      convArmAppAL hE (fundConvAL hE hS hρ h1 hd.1) (fundConvAL hE hS hρ h2 hd.2.1)
        (fundHasTyAL hE hS hρ hB hd.2.2.1) (fundHasTyAL hE hS hρ hrt hd.2.2.2)
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hu hA hb hrt, hd =>
      convArmLamAL hE hu hd.1 (fundConvAL hE hS hρ hA hd.2.1) (fundConvAL hE hS hρ hb hd.2.2.1)
        (fundHasTyAL hE hS hρ hrt hd.2.2.2)
  | _, _, _, _, .pi _ _ _ _ _ _ _ _ _ hu hv hA hB hrt, hd =>
      convArmPiAL hE hρ hu hv hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1
        (fundConvAL hE hS hρ hA hd.2.2.2.2.1)
        (fundConvAL hE hS hρ hB hd.2.2.2.2.2.1) (fundHasTyAL hE hS hρ hrt hd.2.2.2.2.2.2)
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hrt, hd =>
      convArmLetEAL hE (fundConvAL hE hS hρ hA hd.1) (fundConvAL hE hS hρ hv hd.2.1)
        (fundConvAL hE hS hρ hb hd.2.2.1) (fundHasTyAL hE hS hρ hrt hd.2.2.2)
  | _, _, _, _, .sorts Γ l₁ l₂ h, hd =>
      convArmSortsAL Γ l₁ l₂ h hd.1 hd.2.1 hd.2.2
  | _, _, _, _, .consts _ _ _ _ _ hres hlen hwf hwf' h hrt, hd =>
      convArmConstsAL hE hS hres hlen hwf hwf' h hd.1 hd.2.1 (fundHasTyAL hE hS hρ hrt hd.2.2)
  | _, _, _, _, .eta _ _ _ _ _ _ h hrt, hd =>
      convArmEtaAL hE (fundHasTyAL hE hS hρ h hd.1) (fundHasTyAL hE hS hρ hrt hd.2)
  | _, _, _, _, .irr _ _ _ _ hP hp hq, hd =>
      convArmIrrAL (fundHasTyAL hE hS hρ hP hd.1) (fundHasTyAL hE hS hρ hp hd.2.1)
        (fundHasTyAL hE hS hρ hq hd.2.2)
  | _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h _ _ hA'l _ hA, hd =>
      convArmTyConvAL (fundConvAL hE hS hρ h hd.1) (fundHasTyAL hE hS hρ hA'l hd.2.2.1)
        (fundConvAL hE hS hρ hA hd.2.2.2)
end

theorem ValidSubstAL_id (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀) :
    {Γ : LCtxA} → (hΓ : CtxWfA E noIotaA n Γ) → LOKctxA σ N K hΓ →
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ValidSubstAL E n σ N K ρ₀ k Γ SubstA.id SubstA.id Γ
  | _, .nil, _ => ⟨0, fun _ _ => ValidSubstAL_nil [] SubstA.id SubstA.id⟩
  | _, .assumption (Γ := Γ) (A := A) (u := u) hΓ hA, hd => by
      obtain ⟨k₁, h₁⟩ := ValidSubstAL_id hE hS hρ hΓ hd.1
      obtain ⟨k₂, h₂⟩ := fundHasTyAL hE hS hρ hA hd.2
      refine ⟨max k₁ k₂, fun k hk => ?_⟩
      have hid := h₁ k (le_max_of_le₁ hk)
      have hAA := (h₂ k (le_max_of_le₂ hk) Γ SubstA.id SubstA.id ⟨hΓ⟩ hid).2
      simp only [substA_id] at hAA
      obtain ⟨heA, hvA, _, tA, _, _⟩ := LRRelAL_sort_elim hAA
      have heA' : LREqAL E n σ N K ρ₀ k Γ (substA SubstA.id A) (substA SubstA.id A) := by
        rw [substA_id]; exact heA
      have hvA' : ∃ R, LRTyAL E n σ N K ρ₀ k Γ (substA SubstA.id A) R := by rw [substA_id]; exact hvA
      have tA' : Nonempty (HasTyA E noIotaA n Γ (substA SubstA.id A) (.sort u)) := by
        rw [substA_id]; exact tA.1
      have := ValidSubstAL_up hE ⟨hΓ⟩ hid heA' hvA' tA'
      rw [substA_id] at this
      exact ValidSubstAL_ext SubstA.id_up SubstA.id_up this
  | _, .letBinding (Γ := Γ) (A := A) (v := v) (u := u) hΓ hA hv, hd => by
      obtain ⟨k₁, h₁⟩ := ValidSubstAL_id hE hS hρ hΓ hd.1
      obtain ⟨k₂, h₂⟩ := fundHasTyAL hE hS hρ hA hd.2.1
      obtain ⟨k₃, h₃⟩ := fundHasTyAL hE hS hρ hv hd.2.2
      refine ⟨max k₁ (max k₂ k₃), fun k hk => ?_⟩
      have hid := h₁ k (le_max_of_le₁ hk)
      have hAA := (h₂ k (le_max_of_le₁ (le_max_of_le₂ hk)) Γ SubstA.id SubstA.id ⟨hΓ⟩ hid).2
      have hvv := (h₃ k (le_max_of_le₂ (le_max_of_le₂ hk)) Γ SubstA.id SubstA.id ⟨hΓ⟩ hid).2
      simp only [substA_id] at hAA hvv
      obtain ⟨heA, _, _, tA, _, _⟩ := LRRelAL_sort_elim hAA
      have heA' : LREqAL E n σ N K ρ₀ k Γ (substA SubstA.id A) (substA SubstA.id A) := by
        rw [substA_id]; exact heA
      have hvv' : LRRelAL E n σ N K ρ₀ k Γ (substA SubstA.id A) (substA SubstA.id v) (substA SubstA.id v) := by
        rw [substA_id, substA_id]; exact hvv
      have tA' : Nonempty (HasTyA E noIotaA n Γ (substA SubstA.id A) (.sort u)) := by
        rw [substA_id]; exact tA.1
      have := ValidSubstAL_upLet hE ⟨hΓ⟩ hid heA' hvv' tA'
      rw [substA_id, substA_id] at this
      exact ValidSubstAL_ext SubstA.id_up SubstA.id_up this

theorem fundAL_self (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {e A : ExprA} (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (h : HasTyA E noIotaA n Γ e A) (hd : LOKtA σ N K h) :
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → LRRelAL E n σ N K ρ₀ k Γ A e e := by
  obtain ⟨k₁, h₁⟩ := ValidSubstAL_id hE hS hρ hΓ hdΓ
  obtain ⟨k₂, h₂⟩ := fundHasTyAL hE hS hρ h hd
  refine ⟨max k₁ k₂, fun k hk => ?_⟩
  have := (h₂ k (le_max_of_le₂ hk) Γ SubstA.id SubstA.id ⟨hΓ⟩ (h₁ k (le_max_of_le₁ hk))).2
  simpa only [substA_id] using this

theorem fundAL_conv (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {a b A : ExprA} (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (h : ConvA E noIotaA n Γ a b A) (hd : LOKcA σ N K h) :
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → LRRelAL E n σ N K ρ₀ k Γ A a b := by
  obtain ⟨k₁, h₁⟩ := ValidSubstAL_id hE hS hρ hΓ hdΓ
  obtain ⟨k₂, h₂⟩ := fundConvAL hE hS hρ h hd
  refine ⟨max k₁ k₂, fun k hk => ?_⟩
  have := (h₂ k (le_max_of_le₂ hk) Γ SubstA.id SubstA.id ⟨hΓ⟩ (h₁ k (le_max_of_le₁ hk))).2
  simpa only [substA_id] using this

theorem fundAL_tyEq (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {A B : ExprA} {u : Level} (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (h : ConvA E noIotaA n Γ A B (.sort u)) (hd : LOKcA σ N K h) :
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → LREqAL E n σ N K ρ₀ k Γ A B := by
  obtain ⟨k₀, hk⟩ := fundAL_conv hE hS hρ hΓ hdΓ h hd
  exact ⟨k₀, fun k hk' => LREqAL_of_sortRel (hk k hk')⟩

/-! ## §5 `LOKc`-indexed Rows 1, 2, 3 and `EnvSemAL` for recursor-free Prop-family twin environments -/

/-! ### §5.1 Row 1 (`sortConvCharAL`) and Row 2 (`piConvInjAL`) with `LOKc` -/

theorem eqKAL_sort_inv {Γ : LCtxA} {l l' : Level}
    (h : EqKAL E n σ N K ρ₀ k LE LT Γ (.sort l) (.sort l')) : eqN l l' := by
  cases h with
  | sort hA hB _ hl _ =>
      have eA := whTyA_det hA.1 (whTyA_self hA.1) (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
      have eB := whTyA_det hB.1 (whTyA_self hB.1) (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases eA; cases eB
      exact hl
  | pi hA _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA.1 (whTyA_self hA.1) (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | stuck hA _ hN _ _ =>
      have e := whTyA_det hA.1 (whTyA_self hA.1) hN.1 (hStepFnA_sort _ _ _ _)
      subst e
      exact (tripleLikeA_not_sort hN).elim

/-- Row 1 (`SortConvChar`) from the `LOKc`-indexed fundamental theorem. -/
theorem sortConvCharAL (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {l l' u : Level} (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (h : ConvA E noIotaA n Γ (.sort l) (.sort l') (.sort u)) (hd : LOKcA σ N K h) :
    eqN l l' := by
  obtain ⟨k₀, hk⟩ := fundAL_tyEq hE hS hρ hΓ hdΓ h hd
  have hEq := hk k₀ (Nat.le_refl k₀)
  rw [LREqAL_eq] at hEq
  exact eqKAL_sort_inv hEq

theorem eqKAL_pi_inv {Γ : LCtxA} {D C D' C' : ExprA} {u v u' v' : Level}
    (hz : isZero v = false)
    (h : EqKAL E n σ N K ρ₀ k LE LT Γ (.pi D u C v) (.pi D' u' C' v')) :
    eqN u u' ∧ eqN v v' ∧
    Nonempty (HasTyA E noIotaA n Γ D (.sort u)) ∧
    Nonempty (HasTyA E noIotaA n (.assumption D :: Γ) C (.sort v)) ∧
    Nonempty (HasTyA E noIotaA n Γ D' (.sort u')) ∧
    Nonempty (HasTyA E noIotaA n (.assumption D' :: Γ) C' (.sort v')) ∧
    (∃ RD : WkSpecA → ExprA → ExprA → Prop,
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → TyKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ)) ∧
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D')) ∧
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKAL E n σ N K ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))) := by
  cases h with
  | sort hA _ _ _ _ =>
      have e := whTyA_det hA.1 (whTyA_self hA.1) (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
  | pi hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC _ =>
      have eA := whTyA_det hA.1 (whTyA_self hA.1) (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      have eB := whTyA_det hB.1 (whTyA_self hB.1) (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases eA; cases eB
      exact ⟨hu, hv, hDty, hCty, hD'ty, hC'ty, RD, hD, hDeq, hC⟩
  | stuck hA _ hN _ _ =>
      have e := whTyA_det hA.1 (whTyA_self hA.1) hN.1 (hStepFnA_pi _ _ _ _ _ _ _)
      subst e
      have := (isPropTy_pi_iff E noIotaA Γ D u C v).1 (tripleLikeA_pi_isProp hN)
      rw [this] at hz
      cases hz

theorem piConvInjAL_type (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {D C D' C' : ExprA} {u v u' v' w : Level}
    (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (hz : isZero v = false)
    (h : ConvA E noIotaA n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) (hd : LOKcA σ N K h) :
    eqN u u' ∧ eqN v v' ∧
    TyConvAL E n σ N K Γ D D' ∧
    TyConvAL E n σ N K (.assumption D :: Γ) C C' := by
  obtain ⟨k₀, hk⟩ := fundAL_tyEq hE hS hρ hΓ hdΓ h hd
  have hEq := hk k₀ (Nat.le_refl k₀)
  rw [LREqAL_eq] at hEq
  obtain ⟨hu, hv, hDty, _, _, _, RD, hD, hDeq, hC⟩ := eqKAL_pi_inv hz hEq
  have hDconv : TyConvAL E n σ N K Γ D D' := eqKAL_tyConv (hDeq [] ⟨trivial, ⟨hΓ⟩⟩)
  have hΓD : Nonempty (CtxWfA E noIotaA n (.assumption D :: Γ)) :=
    hDty.elim fun tD => ⟨.assumption hΓ tD⟩
  have hρ₁ : WkOkA E noIotaA n [(.assumption D, 0)] Γ := wkOkA_push (.assumption D) Γ hΓD
  have hD₁ := hD [(.assumption D, 0)] hρ₁
  simp only [wkCtxA_push, wkExprA_push] at hD₁
  have hLR : LRTyAL E n σ N K ρ₀ k₀ (.assumption D :: Γ) (liftA 0 1 D) (RD [(.assumption D, 0)]) := by
    rw [LRTyAL_eq]; exact hD₁
  have ht0 : HasTyAL E n σ N K (.assumption D :: Γ) (.bvar 0) (liftA 0 1 D) :=
    ⟨hDty.elim fun tD =>
      ⟨.bvar (.assumption D :: Γ) 0 (liftA 0 1 D) u rfl (hasTyA_wk hE noIotaA_lift Γ [(.assumption D, 0)] hρ₁.1 tD)⟩,
     ⟨.bvar (.assumption (erase D) :: eraseCtx Γ) 0 (erase (liftA 0 1 D))
        (by simp [lookupType, erase_liftA]), by simp only [LOKt]⟩⟩
  have hb0 : RD [(.assumption D, 0)] (.bvar 0) (.bvar 0) :=
    (LRRelAL_bvar hE (Γ := .assumption D :: Γ) (i := 0) (k := k₀) rfl ⟨RD [(.assumption D, 0)], hLR⟩ ht0).at hLR
  have hC₁ := hC [(.assumption D, 0)] hρ₁ (.bvar 0) (.bvar 0) hb0
  have e : ∀ X : ExprA, instantiate0A (.bvar 0) (wkExprA (WkSpecA.ub [(.assumption D, 0)]) X) = X :=
    fun X => instantiate0A_bvar0_liftA X
  simp only [wkCtxA_push, e] at hC₁
  exact ⟨hu, hv, hDconv, eqKAL_tyConv hC₁⟩

theorem piConvInjAL_prop (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {D C D' C' : ExprA} {u v u' v' w : Level}
    (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (hzw : isZero w = true)
    (h : ConvA E noIotaA n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) (hd : LOKcA σ N K h) :
    eqN u u' ∧ eqN v v' ∧
    TyConvAL E n σ N K Γ D D' ∧
    TyConvAL E n σ N K (.assumption D :: Γ) C C' := by
  obtain ⟨k₀, hk⟩ := fundAL_conv hE hS hρ hΓ hdΓ h hd
  have hRel := hk k₀ (Nat.le_refl k₀)
  obtain ⟨_, _, _, _, _, hp⟩ := LRRelAL_sortP_elim hzw hRel
  obtain ⟨hu, hv, hD, hC⟩ := propEqAL_pi_inv ⟨hΓ⟩ hp
  exact ⟨hu, hv, hD, propEqAL_tyConv hC⟩

/-- Row 2 (`PiConvInj`) with `LOKtc`-carrying `TyConvAL` on both domain and codomain,
    at any Type-level codomain (`isZero v = false`) or Prop-level sort (`isZero w = true`). -/
theorem piConvInjAL (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {D C D' C' : ExprA} {u v u' v' w : Level}
    (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (hz : isZero v = false ∨ isZero w = true)
    (h : ConvA E noIotaA n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) (hd : LOKcA σ N K h) :
    eqN u u' ∧ eqN v v' ∧
    TyConvAL E n σ N K Γ D D' ∧
    TyConvAL E n σ N K (.assumption D :: Γ) C C' :=
  hz.elim (fun hzv => piConvInjAL_type hE hS hρ hΓ hdΓ hzv h hd)
    (fun hzw => piConvInjAL_prop hE hS hρ hΓ hdΓ hzw h hd)

theorem piConvInjAL_of_sortEq (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {D C D' C' : ExprA} {u v u' v' w : Level}
    (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (hsort : eqN (.imax u v) w)
    (h : ConvA E noIotaA n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w)) (hd : LOKcA σ N K h) :
    eqN u u' ∧ eqN v v' ∧
    TyConvAL E n σ N K Γ D D' ∧
    TyConvAL E n σ N K (.assumption D :: Γ) C C' := by
  refine piConvInjAL hE hS hρ hΓ hdΓ ?_ h hd
  cases hzv : isZero v with
  | false => exact Or.inl rfl
  | true =>
      refine Or.inr ?_
      rw [← isZero_eqN hsort, isZero_imax]
      exact hzv

/-! ### §5.2 Row 3 at Prop-level family applications (`famAppConvInjAL_prop`) with `LOKc` -/

theorem hStepFnA_indSpine_none {Γ : LCtxA} {r : Nat} {ls : List Level} (xs : List ExprA)
    {m : CheckedMemberA} (hm : E.members r = some m) (hind : m.mclass = .inductiveM) :
    hStepFnA E noIotaA.fn Γ (foldAppsA (.const r ls) xs) = none :=
  hStepFnA_constSpine_none (noIotaA_recHead E) hm (Or.inl (by rw [hind]; rfl))
    (by rw [hind]; exact fun h => MemberClass.noConfusion h) Γ
    (foldAppsA (.const r ls) xs) (by rw [appsSpineA_foldAppsA]; rfl)

/-- Row 3 (`FamAppConvInj`) at Prop-level family applications from the `LOKc`-indexed
    fundamental theorem, producing `eqNList ls ls'` and `ParConvAL` (`LOKc`-carrying
    argument conversions along the family telescope). -/
theorem famAppConvInjAL_prop (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {r : Nat} {ls ls' : List Level} {xs xs' : List ExprA}
    {m : CheckedMemberA} {w : Level}
    (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hna : hStepFnA E noIotaA.fn Γ (foldAppsA (.const r ls) xs) = none)
    (hnb : hStepFnA E noIotaA.fn Γ (foldAppsA (.const r ls') xs') = none)
    (hz : isZero w = true)
    (h : ConvA E noIotaA n Γ (foldAppsA (.const r ls) xs) (foldAppsA (.const r ls') xs') (.sort w))
    (hd : LOKcA σ N K h) :
    eqNList ls ls' ∧
    ∀ lsX : List Level, eqNListB n ls lsX →
      ParConvAL E n σ N K Γ (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA) xs xs' := by
  obtain ⟨k₀, hk⟩ := fundAL_conv hE hS hρ hΓ hdΓ h hd
  have hRel := hk k₀ (Nat.le_refl k₀)
  obtain ⟨_, _, _, _, _, hp⟩ := LRRelAL_sortP_elim hz hRel
  exact (propEqAL_famApp_inv hm hind hna hnb hp).2

theorem parConvAL_singleton_inv {Γ : LCtxA} {IA : ExprA} {uI : Level} {B : ExprA} {v : Level}
    {T' x x' : ExprA}
    (h : ParConvAL E n σ N K Γ (.pi IA uI B v) T' [x] [x']) :
    ConvAL E n σ N K Γ x x' IA := by
  cases h with
  | cons _ _ _ _ _ _ _ _ _ _ _ _ hc _ _ => exact hc

/-- 1-index specialization of `famAppConvInjAL_prop`: convertible applications
    `.app (.const r ls) x` and `.app (.const r ls') x'` of a 1-index Prop-valued family
    yield `eqNList ls ls'` and `ConvAL E n σ N K Γ x x' IA` (whose second component is
    `∃ d : ConvT (eraseEnv E) n (eraseCtx Γ) (erase x) (erase x') (erase IA), LOKc σ N K d`). -/
theorem famAppConvInjAL_prop1 (hE : EnvClosedA E) (hS : EnvSemAL E n σ N K ρ₀) (hρ : PosValA ρ₀)
    {Γ : LCtxA} {r : Nat} {ls ls' : List Level} {x x' IA B : ExprA} {uI v w : Level}
    {m : CheckedMemberA}
    (hΓ : CtxWfA E noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hwf : levelsBounded n ls = true)
    (hmT : instantiateLevelsA ls m.mtypeA = .pi IA uI B v)
    (hz : isZero w = true)
    (h : ConvA E noIotaA n Γ (.app (.const r ls) x) (.app (.const r ls') x') (.sort w))
    (hd : LOKcA σ N K h) :
    eqNList ls ls' ∧ ConvAL E n σ N K Γ x x' IA := by
  have hna : hStepFnA E noIotaA.fn Γ (foldAppsA (.const r ls) [x]) = none :=
    hStepFnA_indSpine_none [x] hm hind
  have hnb : hStepFnA E noIotaA.fn Γ (foldAppsA (.const r ls') [x']) = none :=
    hStepFnA_indSpine_none [x'] hm hind
  obtain ⟨hls, hpar⟩ := famAppConvInjAL_prop hE hS hρ hΓ hdΓ hm hind hna hnb hz h hd
  have hpar0 := hpar ls ⟨eqNList_refl ls, hwf⟩
  rw [hmT] at hpar0
  exact ⟨hls, parConvAL_singleton_inv hpar0⟩

/-! ### §5.3 `EnvSemAL` for recursor-free Prop-family twin environments (`gEnv₀` / `RevBase`) -/

theorem eqNList_nil_of_len_zero {ls ls' : List Level} (hlen : ls.length = 0) (h : eqNList ls ls') :
    ls = [] ∧ ls' = [] := by
  cases ls with
  | nil =>
      cases ls' with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ _ => cases h
  | cons _ _ => cases hlen

theorem wkExprA_of_closed {e : ExprA} (hcl : ∀ c, liftA c 1 e = e) :
    (ρ : WkSpecA) → wkExprA ρ e = e
  | [] => rfl
  | (_, c) :: ρ => by
      show wkExprA ρ (liftA c 1 e) = e
      rw [hcl c]
      exact wkExprA_of_closed hcl ρ

theorem neutKA_axiom {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (hax : m.mclass = .axiomM) (Γ : LCtxA) (ls : List Level) :
    NeutKA E noIotaA Γ (.const r ls) :=
  neutKA_const (noIotaA_recHead E) hres (Or.inl (by rw [hax]; rfl))
    (by rw [hax]; exact fun h => MemberClass.noConfusion h)
    (by rw [hax]; exact fun h => MemberClass.noConfusion h)
    (by rw [hax]; exact fun h => MemberClass.noConfusion h) Γ ls

theorem hasTyAL_const0 {r : Nat} {m : CheckedMemberA} {T : ExprA} {u : Level} {Δ : LCtxA}
    (hres : E.members r = some m) (hm0 : m.arity = 0)
    (hmT : instantiateLevelsA [] m.mtypeA = T)
    (tT : Nonempty (HasTyA E noIotaA n Δ T (.sort u))) :
    HasTyAL E n σ N K Δ (.const r []) T := by
  have hlen : ([] : List Level).length = m.arity := hm0.symm
  have hresE : (eraseEnv E).members r = some (eraseMember m) := by
    simp only [eraseEnv, hres, Option.map_some']
  have hmTE : instantiateLevels [] (eraseMember m).mtype = erase T := by
    show instantiateLevels [] (erase m.mtypeA) = erase T
    rw [← erase_instantiateLevelsA, hmT]
  refine ⟨tT.elim fun dt => ⟨hmT ▸ HasTyA.const Δ r [] m u hres hlen rfl (hmT ▸ dt)⟩, ?_⟩
  exact ex_hasTyT_lok_cast rfl rfl hmTE
    ⟨.const (eraseCtx Δ) r [] (eraseMember m) hresE hlen rfl, fun _ h => nomatch h⟩

/-- `EnvSemClauseAL` for an arity-0 sort-axiom (`U : Sort uI`, e.g. member `2` of `gEnv₀`).
    Requires ZERO bound on `N` or `K` because `HasTyT.const _ u []` has `LOKt = LevelsOK _ _ [] = True`. -/
theorem envSemClauseAL_sortAx0 (hE : EnvClosedA E) {u : Nat} {mU : CheckedMemberA} {uI : Level}
    (hres : E.members u = some mU) (hm0 : mU.arity = 0)
    (hax : mU.mclass = .axiomM)
    (hmT : instantiateLevelsA [] mU.mtypeA = .sort uI) :
    EnvSemClauseAL E n σ N K ρ₀ u mU := by
  intro ls ls' hlen _ _ h _ _
  rcases eqNList_nil_of_len_zero (hm0 ▸ hlen) h with ⟨rfl, rfl⟩
  refine ⟨ht ρ₀ uI + 1, fun k hk Δ _ => ?_⟩
  rw [hmT]
  have htU : HasTyAL E n σ N K Δ (.const u []) (.sort uI) :=
    hasTyAL_const0 hres hm0 hmT ⟨.sort Δ uI⟩
  have hna : NeutKA E noIotaA Δ (.const u []) := neutKA_axiom hres hax Δ []
  exact LRRelAL_reflect hE (LRTyAL_sort_valid Δ hk) hna hna htU htU (convAL_refl htU)

/-- Validity of `.const u []` in `LRTyAL` at every height `k ≥ ht ρ₀ uI` for an arity-0 sort-axiom `u`. -/
theorem const_sortAx0_valid (hE : EnvClosedA E) {u : Nat} {mU : CheckedMemberA} {uI : Level}
    (hres : E.members u = some mU) (hm0 : mU.arity = 0)
    (hax : mU.mclass = .axiomM)
    (hmT : instantiateLevelsA [] mU.mtypeA = .sort uI) :
    ∀ k, ht ρ₀ uI ≤ k → ∀ Δ : LCtxA,
      ∃ R, LRTyAL E n σ N K ρ₀ k Δ (.const u []) R := by
  intro k hk Δ
  have htU : HasTyAL E n σ N K Δ (.const u []) (.sort uI) :=
    hasTyAL_const0 hres hm0 hmT ⟨.sort Δ uI⟩
  have hna : NeutKA E noIotaA Δ (.const u []) := neutKA_axiom hres hax Δ []
  have hk1 : ht ρ₀ uI < ht ρ₀ uI + 1 := Nat.lt_succ_self _
  have hrel : LRRelAL E n σ N K ρ₀ (ht ρ₀ uI + 1) Δ (.sort uI) (.const u []) (.const u []) :=
    LRRelAL_reflect hE (LRTyAL_sort_valid Δ hk1) hna hna htU htU (convAL_refl htU)
  exact ((LRRelAL_sort_elim' hrel).1 k hk).2.1

theorem isPropTy_propFam1_app {f : Nat} {mF : CheckedMemberA} {IA : ExprA} {uI : Level}
    (hres : E.members f = some mF) (hm0 : mF.arity = 0)
    (hmT : instantiateLevelsA [] mF.mtypeA = .pi IA uI (.sort .zero) (.succ .zero))
    (Γ : LCtxA) (x : ExprA) :
    IsPropTy E noIotaA Γ (.app (.const f []) x) := by
  refine ⟨2, .zero, ?_, rfl⟩
  simp only [inferSortA, inferA_succ_app, inferA_succ_const, hres, hm0, ite_true, hmT,
    whnfA, hStepFnA_pi, hStepFnA_sort]
  rfl

/-- `EnvSemClauseAL` for an arity-0, 1-index Prop-valued inductive family
    `F : Π (x : IA), Sort 0` (e.g. member `0` of `gEnv₀`, or `R.f` in any `RevBase`).
    Proved directly from `piTyAL_of_data`, `TyKAL.sortP`, and `PropEqAL.fam` with ZERO bound on `N` or `K`. -/
theorem envSemClauseAL_propFam1 {f : Nat} {mF : CheckedMemberA} {IA : ExprA} {uI : Level}
    (hres : E.members f = some mF) (hm0 : mF.arity = 0) (hind : mF.mclass = .inductiveM)
    (hmT : instantiateLevelsA [] mF.mtypeA = .pi IA uI (.sort .zero) (.succ .zero))
    (hclIA : ∀ c, liftA c 1 IA = IA)
    (tIA : ∀ Δ : LCtxA, Nonempty (HasTyA E noIotaA n Δ IA (.sort uI)))
    (vIA : ∃ kIA : Nat, ∀ k, kIA ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E noIotaA n Δ) →
      ∃ R, LRTyAL E n σ N K ρ₀ k Δ IA R) :
    EnvSemClauseAL E n σ N K ρ₀ f mF := by
  obtain ⟨kIA, hvIA⟩ := vIA
  intro ls ls' hlen _ _ h _ _
  rcases eqNList_nil_of_len_zero (hm0 ▸ hlen) h with ⟨rfl, rfl⟩
  refine ⟨max kIA (ht ρ₀ .zero + 1), fun k hk Δ hΔ => ?_⟩
  have hkIA : kIA ≤ k := le_max_of_le₁ hk
  have hk0 : ht ρ₀ .zero < k := le_max_of_le₂ hk
  rw [hmT]
  have tTF : ∀ Γ' : LCtxA,
      Nonempty (HasTyA E noIotaA n Γ' (.pi IA uI (.sort .zero) (.succ .zero))
        (.sort (.imax uI (.succ .zero)))) :=
    fun Γ' => (tIA Γ').elim fun dIA =>
      ⟨.pi Γ' IA uI (.sort .zero) (.succ .zero) dIA (.sort (.assumption IA :: Γ') .zero)⟩
  have tf : ∀ Γ' : LCtxA, HasTyAL E n σ N K Γ' (.const f []) (.pi IA uI (.sort .zero) (.succ .zero)) :=
    fun Γ' => hasTyAL_const0 hres hm0 hmT (tTF Γ')
  obtain ⟨dIAΔ⟩ := tIA Δ
  have hRpi : LRTyAL E n σ N K ρ₀ k Δ (.pi IA uI (.sort .zero) (.succ .zero)) (fun g₁ g₂ =>
      (∀ ρ : WkSpecA, WkOkA E noIotaA n ρ Δ → ∀ a a' : ExprA,
        LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (wkExprA ρ IA) a a' →
        LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) (.sort .zero)))
          (.app (wkExprA ρ g₁) a) (.app (wkExprA ρ g₂) a')) ∧
      HasTyAL E n σ N K Δ g₁ (.pi IA uI (.sort .zero) (.succ .zero)) ∧
      HasTyAL E n σ N K Δ g₂ (.pi IA uI (.sort .zero) (.succ .zero)) ∧
      ConvAL E n σ N K Δ g₁ g₂ (.pi IA uI (.sort .zero) (.succ .zero))) := by
    refine piTyAL_of_data rfl dIAΔ (.sort (.assumption IA :: Δ) .zero)
      (fun ρ hρ => ?_) (fun ρ _ a _ _ => ?_) (fun ρ _ a a' _ => ?_)
    · rw [wkExprA_of_closed hclIA ρ]
      exact hvIA k hkIA (wkCtxA ρ Δ) hρ.2
    · rw [wkExprA_of_closed (fun _ => rfl) (WkSpecA.ub ρ)]
      exact LRTyAL_sort_valid _ hk0
    · rw [wkExprA_of_closed (fun _ => rfl) (WkSpecA.ub ρ)]
      exact LREqAL_sort_refl _ hk0
  refine ⟨_, hRpi, fun ρ _ a a' ha => ?_, tf Δ, tf Δ, convAL_refl (tf Δ)⟩
  rw [wkExprA_of_closed hclIA ρ] at ha
  rw [wkExprA_of_closed (fun _ => rfl) (WkSpecA.ub ρ),
      wkExprA_of_closed (fun _ => rfl) ρ]
  change LRRelAL E n σ N K ρ₀ k (wkCtxA ρ Δ) (.sort .zero) (.app (.const f []) a) (.app (.const f []) a')
  let Γ' := wkCtxA ρ Δ
  obtain ⟨ta, ta'⟩ := LRRelAL_hasTy ha
  have ca := LRRelAL_conv ha
  have tapp : ∀ {x : ExprA}, HasTyAL E n σ N K Γ' x IA →
      HasTyAL E n σ N K Γ' (.app (.const f []) x) (.sort .zero) := fun {x} tx =>
    ⟨(tf Γ').1.elim fun df => tx.1.elim fun dx =>
      ⟨.app Γ' (.const f []) x IA (.sort .zero) uI (.succ .zero) (.succ .zero)
        (.sort (.assumption IA :: Γ') .zero) (.sort Γ' .zero) df dx⟩,
     (tf Γ').2.elim fun dtf hdtf => tx.2.elim fun dtx hdtx =>
       ⟨.app (eraseCtx Γ') (.const f []) (erase x) (erase IA) (.sort .zero) dtf dtx,
        by simp only [LOKt]; exact ⟨hdtf, hdtx⟩⟩⟩
  have tFa := tapp ta
  have tFa' := tapp ta'
  have capp : ConvAL E n σ N K Γ' (.app (.const f []) a) (.app (.const f []) a') (.sort .zero) :=
    ⟨(convAL_refl (tf Γ')).1.elim fun cf => ca.1.elim fun c => tFa'.1.elim fun rt =>
      ⟨.app Γ' (.const f []) (.const f []) a a' IA (.sort .zero) uI (.succ .zero)
        cf c (.sort (.assumption IA :: Γ') .zero) rt⟩,
     (tf Γ').2.elim fun dtf hdtf => ca.2.elim fun dca hdca =>
       ⟨.app (eraseCtx Γ') (.const f []) (.const f []) (erase a) (erase a') (erase IA) (.sort .zero)
          (.refl _ _ _ dtf) dca,
        by simp only [LOKc]; exact ⟨hdtf, hdca⟩⟩⟩
  have hna : hStepFnA E noIotaA.fn Γ' (.app (.const f []) a) = none :=
    hStepFnA_indSpine_none [a] hres hind
  have hna' : hStepFnA E noIotaA.fn Γ' (.app (.const f []) a') = none :=
    hStepFnA_indSpine_none [a'] hres hind
  have hpv : PropValidAL E n σ N K Γ' (.app (.const f []) a) :=
    ⟨_, whTyAL_of_hasTy tFa.1, tripleLikeA_of_prop hna (isPropTy_propFam1_app hres hm0 hmT Γ' a)⟩
  have hpv' : PropValidAL E n σ N K Γ' (.app (.const f []) a') :=
    ⟨_, whTyAL_of_hasTy tFa'.1, tripleLikeA_of_prop hna' (isPropTy_propFam1_app hres hm0 hmT Γ' a')⟩
  have hpeq : PropEqAL E n σ N K Γ' (.app (.const f []) a) (.app (.const f []) a') := by
    refine .fam (r := f) (ls := []) (ls' := []) (xs := [a]) (xs' := [a'])
      (whTyAL_of_hasTy tFa.1) (whTyAL_of_hasTy tFa'.1) hna hna' hres hind (eqNList_refl [])
      (fun lsX hlsX => ?_)
      (tyConvAL_of_convAL tFa.1 (eqNA_refl .zero) tFa'.1 (eqNA_refl .zero) capp)
    rcases eqNList_nil_of_len_zero List.length_nil hlsX.1 with ⟨_, rfl⟩
    rw [hmT]
    exact .cons IA uI (.sort .zero) (.succ .zero) IA uI (.sort .zero) (.succ .zero)
      a a' [] [] ca (tyConvAL_refl Γ' IA) (.nil (.sort .zero) (.sort .zero))
  refine ⟨_, by rw [LRTyAL_eq]; exact .sortP (whTyAL_of_hasTy ⟨.sort Γ' .zero⟩) rfl, ?_⟩
  exact ⟨hpv, hpv', tFa, tFa', capp, hpeq⟩

/-- `EnvSemClauseAL` for an arity-0 constructor-axiom `mk : Π (x : IA), F x` of a Prop-valued
    family `F : IA → Prop` (e.g. member `1` of `gEnv₀`, or `R.f + 1` in `R.twin₁`).
    Requires ZERO bound on `N` or `K` because `mk`'s type has codomain sort `.zero` (`TripleLikeA`). -/
theorem envSemClauseAL_propCtorAx0 (hE : EnvClosedA E)
    {f a : Nat} {mF mA : CheckedMemberA} {IA : ExprA} {uI : Level}
    (hresF : E.members f = some mF) (hmF0 : mF.arity = 0)
    (hmFT : instantiateLevelsA [] mF.mtypeA = .pi IA uI (.sort .zero) (.succ .zero))
    (hresA : E.members a = some mA) (hmA0 : mA.arity = 0)
    (haxA : mA.mclass = .axiomM)
    (hmAT : instantiateLevelsA [] mA.mtypeA = .pi IA uI (.app (.const f []) (.bvar 0)) .zero)
    (hclIA : ∀ c, liftA c 1 IA = IA)
    (tIA : ∀ Δ : LCtxA, Nonempty (HasTyA E noIotaA n Δ IA (.sort uI))) :
    EnvSemClauseAL E n σ N K ρ₀ a mA := by
  intro ls ls' hlen _ _ h _ _
  rcases eqNList_nil_of_len_zero (hmA0 ▸ hlen) h with ⟨rfl, rfl⟩
  refine ⟨0, fun k _ Δ _ => ?_⟩
  rw [hmAT]
  let Δ' : LCtxA := .assumption IA :: Δ
  have tTF : Nonempty (HasTyA E noIotaA n Δ' (.pi IA uI (.sort .zero) (.succ .zero))
      (.sort (.imax uI (.succ .zero)))) :=
    (tIA Δ').elim fun dIA =>
      ⟨.pi Δ' IA uI (.sort .zero) (.succ .zero) dIA (.sort (.assumption IA :: Δ') .zero)⟩
  have tf : Nonempty (HasTyA E noIotaA n Δ' (.const f []) (.pi IA uI (.sort .zero) (.succ .zero))) :=
    (hasTyAL_const0 (σ := σ) (N := N) (K := K) hresF hmF0 hmFT tTF).1
  have tb0 : Nonempty (HasTyA E noIotaA n Δ' (.bvar 0) IA) :=
    (tIA Δ').elim fun dIA => by
      have dIA' : HasTyA E noIotaA n Δ' (liftA 0 1 IA) (.sort uI) := by rw [hclIA 0]; exact dIA
      have hb : HasTyA E noIotaA n Δ' (.bvar 0) (liftA 0 1 IA) := .bvar Δ' 0 (liftA 0 1 IA) uI rfl dIA'
      rw [hclIA 0] at hb
      exact ⟨hb⟩
  have tcod : Nonempty (HasTyA E noIotaA n Δ' (.app (.const f []) (.bvar 0)) (.sort .zero)) :=
    tf.elim fun df => tb0.elim fun db0 =>
      ⟨.app Δ' (.const f []) (.bvar 0) IA (.sort .zero) uI (.succ .zero) (.succ .zero)
        (.sort (.assumption IA :: Δ') .zero) (.sort Δ' .zero) df db0⟩
  have tTA : Nonempty (HasTyA E noIotaA n Δ (.pi IA uI (.app (.const f []) (.bvar 0)) .zero)
      (.sort (.imax uI .zero))) :=
    (tIA Δ).elim fun dIA => tcod.elim fun dcod =>
      ⟨.pi Δ IA uI (.app (.const f []) (.bvar 0)) .zero dIA dcod⟩
  have ta : HasTyAL E n σ N K Δ (.const a []) (.pi IA uI (.app (.const f []) (.bvar 0)) .zero) :=
    hasTyAL_const0 hresA hmA0 hmAT tTA
  have hna : NeutKA E noIotaA Δ (.const a []) := neutKA_axiom hresA haxA Δ []
  have hnf : TripleLikeA E noIotaA Δ (.pi IA uI (.app (.const f []) (.bvar 0)) .zero) :=
    tripleLikeA_of_prop (hStepFnA_pi _ _ _ _ _ _ _) ((isPropTy_pi_iff E noIotaA Δ _ _ _ .zero).2 rfl)
  have hvalid : ∃ R, LRTyAL E n σ N K ρ₀ k Δ (.pi IA uI (.app (.const f []) (.bvar 0)) .zero) R := by
    rw [LRTyAL_eq]
    exact ⟨_, tyKAL_of_tripleLike (whTyAL_of_hasTy tTA) hnf⟩
  exact LRRelAL_reflect hE hvalid hna hna ta ta (convAL_refl ta)

/-- Generic `EnvSemAL` extension theorem for any recursor-free Prop-family twin environment:
    if every member of `E` is either an arity-0 sort-axiom (`U : Sort uI`), the 1-index Prop-valued
    family (`F : IA → Prop` at `f`), its constructor-axiom (`mk : Π (x : IA), F x` at `a`), or
    already satisfies `EnvSemClauseAL` in `E`, then `EnvSemAL E n σ N K ρ₀` holds. -/
theorem twinEnvSemAL (hE : EnvClosedA E)
    {f a : Nat} {mF mA : CheckedMemberA} {IA : ExprA} {uI : Level}
    (hresF : E.members f = some mF) (hmF0 : mF.arity = 0) (hindF : mF.mclass = .inductiveM)
    (hmFT : instantiateLevelsA [] mF.mtypeA = .pi IA uI (.sort .zero) (.succ .zero))
    (hresA : E.members a = some mA) (hmA0 : mA.arity = 0)
    (haxA : mA.mclass = .axiomM)
    (hmAT : instantiateLevelsA [] mA.mtypeA = .pi IA uI (.app (.const f []) (.bvar 0)) .zero)
    (hclIA : ∀ c, liftA c 1 IA = IA)
    (tIA : ∀ Δ : LCtxA, Nonempty (HasTyA E noIotaA n Δ IA (.sort uI)))
    (vIA : ∃ kIA : Nat, ∀ k, kIA ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E noIotaA n Δ) →
      ∃ R, LRTyAL E n σ N K ρ₀ k Δ IA R)
    (hrest : ∀ r m, E.members r = some m → r ≠ f → r ≠ a → EnvSemClauseAL E n σ N K ρ₀ r m) :
    EnvSemAL E n σ N K ρ₀ := by
  intro r m hm
  by_cases hf : r = f
  · subst hf; rw [hresF] at hm; obtain rfl := Option.some.inj hm
    exact envSemClauseAL_propFam1 hresF hmF0 hindF hmFT hclIA tIA vIA
  · by_cases ha : r = a
    · subst ha; rw [hresA] at hm; obtain rfl := Option.some.inj hm
      exact envSemClauseAL_propCtorAx0 hE hresF hmF0 hmFT hresA hmA0 haxA hmAT hclIA tIA
    · exact hrest r m hm hf ha

/-! ### §5.4 Concrete instantiation at `gEnv₀` (`riTwinEnvA`) -/

/-- Annotated copy of `riFamM` (`RI : U → Prop` at index `0` of `gEnv₀`). -/
def riFamMA : CheckedMemberA :=
  ⟨.inductiveM, 0, .pi (.const 2 []) .zero (.sort .zero) (.succ .zero), none, 0, none⟩

/-- Annotated copy of `riAxM` (`mk : Π (x : U), RI x` at index `1` of `gEnv₀`). -/
def riAxMA : CheckedMemberA :=
  ⟨.axiomM, 0, .pi (.const 2 []) .zero (.app (.const 0 []) (.bvar 0)) .zero, none, 0, none⟩

/-- Annotated copy of `uAxM` (`U : Prop` at index `2` of `gEnv₀`). -/
def riAxUMA : CheckedMemberA :=
  ⟨.axiomM, 0, .sort .zero, none, 0, none⟩

/-- Annotated copy of `gEnv₀` (`RcicFamAppRevTwin.lean:94`), the recursor-free twin of `riEnv`. -/
def riTwinEnvA : ResolvedEnvA where
  members
    | 0 => some riFamMA
    | 1 => some riAxMA
    | 2 => some riAxUMA
    | _ + 3 => none

theorem riTwinEnvA_closed : EnvClosedA riTwinEnvA := by
  intro r m hm
  match r with
  | 0 =>
      change some riFamMA = some m at hm
      obtain rfl := Option.some.inj hm
      refine ⟨fun c => rfl, fun _ hb => Option.noConfusion hb⟩
  | 1 =>
      change some riAxMA = some m at hm
      obtain rfl := Option.some.inj hm
      refine ⟨fun c => by simp [riAxMA, liftA, shiftIdx], fun _ hb => Option.noConfusion hb⟩
  | 2 =>
      change some riAxUMA = some m at hm
      obtain rfl := Option.some.inj hm
      refine ⟨fun c => rfl, fun _ hb => Option.noConfusion hb⟩
  | _ + 3 => exact Option.noConfusion hm

theorem riTwinEnvA_semAL : EnvSemAL riTwinEnvA n σ N K ρ₀ := by
  have hres0 : riTwinEnvA.members 0 = some riFamMA := rfl
  have hres1 : riTwinEnvA.members 1 = some riAxMA := rfl
  have hres2 : riTwinEnvA.members 2 = some riAxUMA := rfl
  have tU : ∀ Δ : LCtxA, Nonempty (HasTyA riTwinEnvA noIotaA n Δ (.const 2 []) (.sort .zero)) :=
    fun Δ => (hasTyAL_const0 (E := riTwinEnvA) (σ := σ) (N := N) (K := K) hres2 rfl rfl ⟨.sort Δ .zero⟩).1
  have vU : ∃ kIA : Nat, ∀ k, kIA ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA riTwinEnvA noIotaA n Δ) →
      ∃ R, LRTyAL riTwinEnvA n σ N K ρ₀ k Δ (.const 2 []) R :=
    ⟨ht ρ₀ .zero, fun k hk Δ _ =>
      const_sortAx0_valid riTwinEnvA_closed hres2 rfl rfl rfl k hk Δ⟩
  refine twinEnvSemAL riTwinEnvA_closed hres0 rfl rfl rfl hres1 rfl rfl rfl (fun _ => rfl) tU vU ?_
  intro r m hm h0 h1
  match r with
  | 0 => exact absurd rfl h0
  | 1 => exact absurd rfl h1
  | 2 =>
      change some riAxUMA = some m at hm
      obtain rfl := Option.some.inj hm
      exact envSemClauseAL_sortAx0 riTwinEnvA_closed hres2 rfl rfl rfl
  | _ + 3 => exact Option.noConfusion hm

/-- `LOKc`-indexed Row 1 (`SortConvChar`), Row 2 (`PiConvInj`), and Row 3 (`FamAppConvInj` at `RI`)
    for `riTwinEnvA` (`gEnv₀`), with ZERO `N`/`K` overhead on `EnvSemAL`. -/
theorem riTwin_piConvInjAL (hρ : PosValA ρ₀)
    {Γ : LCtxA} {D C D' C' : ExprA} {u v u' v' w : Level}
    (hΓ : CtxWfA riTwinEnvA noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (hz : isZero v = false ∨ isZero w = true)
    (h : ConvA riTwinEnvA noIotaA n Γ (.pi D u C v) (.pi D' u' C' v') (.sort w))
    (hd : LOKcA σ N K h) :
    eqN u u' ∧ eqN v v' ∧
    TyConvAL riTwinEnvA n σ N K Γ D D' ∧
    TyConvAL riTwinEnvA n σ N K (.assumption D :: Γ) C C' :=
  piConvInjAL riTwinEnvA_closed riTwinEnvA_semAL hρ hΓ hdΓ hz h hd

theorem riTwin_famAppConvInjAL (hρ : PosValA ρ₀)
    {Γ : LCtxA} {x x' : ExprA} {w : Level}
    (hΓ : CtxWfA riTwinEnvA noIotaA n Γ) (hdΓ : LOKctxA σ N K hΓ)
    (hz : isZero w = true)
    (h : ConvA riTwinEnvA noIotaA n Γ (.app (.const 0 []) x) (.app (.const 0 []) x') (.sort w))
    (hd : LOKcA σ N K h) :
    ConvAL riTwinEnvA n σ N K Γ x x' (.const 2 []) :=
  (famAppConvInjAL_prop1 riTwinEnvA_closed riTwinEnvA_semAL hρ hΓ hdΓ
    (r := 0) (ls := []) (ls' := []) (m := riFamMA)
    rfl rfl rfl rfl hz h hd).2

end LRMetatheory

end Rcic.Declarative.Ann.Lok
