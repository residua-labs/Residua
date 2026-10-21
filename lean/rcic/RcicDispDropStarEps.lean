import rcic.RcicDispDropStar
import rcic.RcicSynTable

/-!
# Syntactic sortRow, S14 DISP-1 — `eps_dropStarEq` for the repaired eps

`research/rcic/sortrow/S14_DROP_INLINE_STAR_OBS.md` §3 (per-branch table),
stacked on the R2 erasure (`piSlot`, `lsubDisp`/`localize`) and DISP-0
(`RcicDispDropStar`). The theorem compares **the same derivation** `D` on two
`DropStarEq`-related displays — no AP, no `DisplayFits`, no native transport:

```
theorem eps_dropStarEq (D : TyP E n Γ e T) (σ : Level → Level)
    (hρ : DropStarEq ρ₁ ρ₂) : D.eps σ ρ₁ = D.eps σ ρ₂
```

§3 row-by-row: sort/const are ρ-independent past the shared `levelIsZero`
gate; bvar is `resolve_eq`; pi/lam extend both sides by the same disposition
and use the body IH; app rewrites both children; letE rewrites `hv`'s value
then conses; lit/conv/ewk/cctx are the child's IH; wk is `removeAt` +
`keepAt` + `countKeep_take`; esub is `insertDisp` congruence + the gate;
lsub is `insertDisp` congruence on the equal `lsubDisp` payload; linst is the
IH under the composite `σ ∘ instLevel ls`.

`closure_claim = 0`. Additive only — `TyP.eps` untouched.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `DropStarEq` is preserved under consing the same disposition
    (the pi/lam/letE rows pay this for `.drop`/`.keep`/`.inline ev`). -/
theorem DropStarEq.cons (d : Disp) {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂) :
    DropStarEq (d :: ρ₁) (d :: ρ₂) :=
  congrArg (normDisp d :: ·) h.eq

/-- S14 §3: the repaired `TyP.eps` agrees at every `DropStarEq`-related
    display pair. Structural recursion on the derivation (the `closedAt_eps`
    idiom — `TyP` is mutually inductive with `CvP`, so `induction` does not
    apply); each row uses only the display algebra of `RcicDispDropStar`. -/
theorem eps_dropStarEq :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → (σ : Level → Level) → {ρ₁ ρ₂ : List Disp} →
    DropStarEq ρ₁ ρ₂ → D.eps σ ρ₁ = D.eps σ ρ₂
  | _, _, _, _, _, .sort .., _, _, _, _ => rfl
  | _, _, _, _, _, .bvar _ _ _ i _ u _ _, σ, _, _, hρ => by
    cases hu : levelIsZero (σ u) with
    | true => simp only [eps_bvar_proof hu]
    | false =>
      simp only [eps_bvar_rel hu]
      exact hρ.resolve_eq i
  | _, _, _, _, _, .const _ _ _ _ _ _ _ u _ _ _ _ _, σ, _, _, _ => by
    cases hu : levelIsZero (σ u) with
    | true => simp only [eps_const_proof hu]
    | false => simp only [eps_const_rel hu]
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB, σ, ρ₁, ρ₂, hρ => by
    cases hu : levelIsZero (σ u) with
    | true =>
      simp only [eps_pi_drop hu]
      rw [eps_dropStarEq hA σ hρ, eps_dropStarEq hB σ (DropStarEq.cons .drop hρ)]
    | false =>
      simp only [eps_pi_keep hu]
      rw [eps_dropStarEq hA σ hρ, eps_dropStarEq hB σ (DropStarEq.cons .keep hρ)]
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ hA hbody hB, σ, ρ₁, ρ₂, hρ => by
    cases hu : levelIsZero (σ u) with
    | true =>
      simp only [eps_lam_drop hu]
      exact eps_dropStarEq hbody σ (DropStarEq.cons .drop hρ)
    | false =>
      simp only [eps_lam_keep_eq hA hbody hB _ hu]
      rw [eps_dropStarEq hbody σ (DropStarEq.cons .keep hρ)]
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha hT, σ, ρ₁, ρ₂, hρ => by
    simp only [eps_app_eq hf ha hT σ]
    rw [eps_dropStarEq hf σ hρ, eps_dropStarEq ha σ hρ]
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT, σ, ρ₁, ρ₂, hρ => by
    rw [let_eps_eq hA hv hb hT σ ρ₁, let_eps_eq hA hv hb hT σ ρ₂,
      eps_dropStarEq hv σ hρ]
    exact eps_dropStarEq hb σ (DropStarEq.cons _ hρ)
  | _, _, _, _, _, .lit _ _ _ _ _ hexp, σ, ρ₁, ρ₂, hρ => by
    simp only [eps_lit]
    exact eps_dropStarEq hexp σ hρ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h hc, σ, ρ₁, ρ₂, hρ => by
    simp only [eps_conv]
    exact eps_dropStarEq h σ hρ
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D, σ, ρ₁, ρ₂, hρ => by
    by_cases hk₁ : ρ₁[c]? = some .keep
    · have hk₂ : ρ₂[c]? = some .keep := (hρ.keepAt c).mp hk₁
      simp only [eps_wk_keep hk₁, eps_wk_keep hk₂]
      rw [eps_dropStarEq D σ (hρ.removeAt c), hρ.countKeep_take c]
    · have hk₁' : ρ₁[c]? = none ∨ ρ₁[c]? = some .drop ∨
          ∃ v, ρ₁[c]? = some (.inline v) := by
        cases hc : ρ₁[c]? with
        | none => exact Or.inl rfl
        | some d =>
          cases d with
          | keep => exact absurd hc hk₁
          | drop => exact Or.inr (Or.inl rfl)
          | inline v => exact Or.inr (Or.inr ⟨v, rfl⟩)
      have hk₂' : ρ₂[c]? = none ∨ ρ₂[c]? = some .drop ∨
          ∃ v, ρ₂[c]? = some (.inline v) := by
        cases hc : ρ₂[c]? with
        | none => exact Or.inl rfl
        | some d =>
          cases d with
          | keep => exact absurd ((hρ.keepAt c).mpr hc) hk₁
          | drop => exact Or.inr (Or.inl rfl)
          | inline v => exact Or.inr (Or.inr ⟨v, rfl⟩)
      simp only [eps_wk_not_keep hk₁', eps_wk_not_keep hk₂']
      exact eps_dropStarEq D σ (hρ.removeAt c)
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D hget hv hvT, σ, ρ₁, ρ₂, hρ => by
    cases hu : levelIsZero (σ u) with
    | true =>
      simp only [eps_esub_drop hu]
      exact eps_dropStarEq D σ (hρ.insertDisp rfl j)
    | false =>
      simp only [eps_esub_keep hu]
      rw [hρ.countKeep_take j, eps_dropStarEq hv σ hρ,
        eps_dropStarEq D σ (hρ.insertDisp rfl j)]
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j u D hget hv hvT, σ, ρ₁, ρ₂, hρ => by
    rw [lsub_eps_eq D hget hv hvT σ ρ₁, lsub_eps_eq D hget hv hvT σ ρ₂,
      hρ.countKeep_take j, eps_dropStarEq hv σ hρ]
    exact eps_dropStarEq D σ (hρ.insertDisp rfl j)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, σ, ρ₁, ρ₂, hρ => by
    simp only [eps_linst]
    exact eps_dropStarEq D (fun l => σ (instLevel ls l)) hρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, σ, ρ₁, ρ₂, hρ => by
    simp only [eps_ewk]
    exact eps_dropStarEq D σ hρ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, σ, ρ₁, ρ₂, hρ => by
    simp only [eps_cctx]
    exact eps_dropStarEq D σ hρ

/-! ### Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [
    ``Rcic.Syn.DropStarEq.cons,
    ``Rcic.Syn.eps_dropStarEq]
  for t in targets do
    unless env.contains t do throwError "missing declaration {t}"
    let (_, st) := ((CollectAxioms.collect t).run env).run {}
    for ax in st.axioms do
      unless [``propext, ``Quot.sound].contains ax do
        throwError "forbidden axiom {ax} in {t}"
  logInfo m!"[rcic_disp_dropstar_eps] {targets.length} decls: axioms ⊆ [propext, Quot.sound]"

#print axioms Rcic.Syn.eps_dropStarEq

end Rcic.Syn
