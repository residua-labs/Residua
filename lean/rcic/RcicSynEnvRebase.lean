import rcic.RcicSynDispForPath
import rcic.RcicSynErase
import rcic.RcicSynLetInline
import rcic.RcicSynAdm
import rcic.RcicIota

/-!
# Syntactic sortRow — environment rebase and the `.ewk` source-context pin

`research/rcic/sortrow/S1_COVERAGECAT.md` §2–3 (ChatGPT's approved S1, #7307).
Implementation credits: ChatGPT (spec), ct001 lane (Lean).

* **§1 the missing-constant refutation** (`S1` §2.2): `no_tyP_const_of_missing`
  composes `agreeOn_setW`, `TyP.wt_congr`, `TyP.admW_lt_of_const` exactly as
  sketched — a `const r` typing exists only if `r` is a member, because its
  weight exceeds `Aw r` whatever `Aw` says elsewhere. `no_source_spine` is the
  corollary at `emptyEnv`.
* **§2 the public-AP pin** (`S1` §2.3–2.5): at `E₀ = emptyEnv`,
  `E₁ = extendEnv emptyEnv 0 ⟨axiomM, 0, sort 0, none⟩`, the derivation
  `D = .ewk emptyEnv E₁ … (.sort …)` is a REAL derivation — `TyP.sort` needs no
  well-formed context — and it is `AssumpPref`, so it sits in the public AP
  domain. Yet the strict `DispForPathTy` route is impossible for it: the `.ewk`
  path constructor still needs a `CtxP emptyEnv 0 [assumption (const 0 [])]`,
  and `no_source_spine` refuses. This is **W-COV-EWK-SOURCE-CTX** pinned.
  `ceCtxTarget` is the companion control: the same spine shape DOES exist over
  the *target* environment (member `0` resolves there) — a target `CtxP` must
  never be passed off as the source `CtxP`.
* **§3 `rebaseTy`/`rebaseCv`** (`S1` §3.1): forward environment transport by
  rebuilding the real constructors. Inner `.ewk` nodes are ELIMINATED by
  composing the inclusions (`envExt_trans`) — the result is never re-wrapped
  in another `.ewk`. ι transports through `derivedIotaExt` (the original
  witness's `extWitness`; no new reduction witness is forged).
* **§4 correspondences**: index preserved (the signature), `AssumpPref`
  preserved, `eps` preserved exactly under the same `σ`/`ρ`, regularity and
  `dl`/`dr` correspondence (the pair equality `rebaseTy_reg` and the conjunction
  `rebaseCv_dl_dr`, from which erasure correspondence follows by
  `rebaseTy_eps`), `wt` non-increase, and atom lists in the composable
  non-increasing relation `AtomsLe`.

This module asserts no decrease composition and no arbitrary AP coverage;
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the missing-constant refutation (`S1` §2.2) -/

/-- No `TyP` of `const r ls` exists when `r` is not a member of `E`: weighing the
    derivation at `Aw' := setW Aw r (D.wt Aw)` — which AGREES with `Aw` on `E`'s
    members, so `wt_congr` keeps `D`'s weight — makes `admW_lt_of_const` read
    `D.wt Aw < D.wt Aw`. -/
theorem no_tyP_const_of_missing {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level} {T : Expr Nat} (hm : E.members r = none)
    (D : TyP E n Γ (.const r ls) T) : False := by
  have hlt : setW (fun _ => 0) r (D.wt (fun _ => 0)) r <
      D.wt (setW (fun _ => 0) r (D.wt (fun _ => 0))) :=
    TyP.admW_lt_of_const _ D ⟨ls, rfl⟩
  rw [setW_self, TyP.wt_congr D (agreeOn_setW _ _ hm)] at hlt
  exact Nat.lt_irrefl _ hlt

/-- no `CtxP` spine with a `const 0 []` assumption exists over `emptyEnv` —
    its introducing typing is a `const 0` typing of a missing member. -/
theorem no_source_spine (C : CtxP emptyEnv 0 [.assumption (.const 0 [])]) : False := by
  cases C with
  | assumption _ _ _ _ hA =>
      exact no_tyP_const_of_missing (r := 0) (ls := []) rfl hA

/-! ## §2 the public-AP pin (`S1` §2.4–2.5) -/

/-- an extension out of `emptyEnv` is vacuous: `emptyEnv` has no members to preserve. -/
theorem envExt_emptyEnv (E : ResolvedEnv) : EnvExt emptyEnv E := by
  intro r m h
  simp [emptyEnv] at h

/-- `E₁ = extendEnv emptyEnv 0 ⟨axiomM, 0, sort 0, none⟩`. -/
def ceE1 : ResolvedEnv := extendEnv emptyEnv 0 ⟨.axiomM, 0, .sort .zero, none⟩

/-- the counterexample derivation `D` (`S1` §2.4): an `.ewk` whose source is a
    `TyP.sort` over an UNPROVABLE context — `TyP.sort` reads no context and no
    member, so `D` is a real derivation in the public domain. -/
def ceD : TyP ceE1 0 [.assumption (.const 0 [])] (.sort .zero) (.sort (.succ .zero)) :=
  .ewk emptyEnv ceE1 0 [.assumption (.const 0 [])] (.sort .zero) (.sort (.succ .zero))
    (envExt_emptyEnv ceE1)
    (.sort emptyEnv 0 [.assumption (.const 0 [])] .zero (.succ .zero) (eqN_refl _))

/-- `D` is `AssumpPref`: `sort` is trivially so and `ewk` passes it through. -/
theorem ceD_assumpPref : ceD.AssumpPref := by
  trivial

/-- reading off a `.ewk` path's source spine (the `C₀` it stores). -/
theorem dispForPathTy_ewk_src {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {hext : EnvExt E₀ E} {D : TyP E₀ n Γ e T}
    {σ : Level → Level} {ρ : List Disp} {C : CtxP E n Γ}
    (p : DispForPathTy (.ewk E₀ E n Γ e T hext D) σ ρ C) :
    ∃ (C₀ : CtxP E₀ n Γ), Nonempty (DispForPathTy D σ ρ C₀) := by
  cases p with
  | ewk hC src => exact ⟨_, ⟨src⟩⟩

/-- the strict `DispForPathTy` route is impossible for `D`: its `.ewk` path
    constructor needs `src : DispForPathTy … σ ρ C₀` with
    `C₀ : CtxP emptyEnv 0 [assumption (const 0 [])]`, and `no_source_spine`
    refuses `C₀`. **W-COV-EWK-SOURCE-CTX**, pinned. -/
theorem ceD_no_strict_path {σ : Level → Level} {ρ : List Disp}
    {C : CtxP ceE1 0 [.assumption (.const 0 [])]}
    (p : DispForPathTy ceD σ ρ C) : False := by
  obtain ⟨C₀, _⟩ := dispForPathTy_ewk_src p
  exact no_source_spine C₀

/-- companion control: the same spine shape over the TARGET environment exists
    (member `0` resolves there) — a target `CtxP` must never serve as the source. -/
def ceCtxTarget : CtxP ceE1 0 [.assumption (.const 0 [])] :=
  .assumption ceE1 0 [] (.const 0 []) .zero (.nil ceE1 0)
    (.const ceE1 0 [] 0 [] [] ⟨.axiomM, 0, .sort .zero, none⟩ (.succ .zero)
      (members_extend_self emptyEnv 0 _) rfl rfl (eqNList_refl _)
      (.sort ceE1 0 [] .zero (.succ .zero) (eqN_refl _)))

/-! ## §3 `rebaseTy`/`rebaseCv` (`S1` §3.1) -/

mutual

/-- environment rebase: forward-transport a typing along `hext : EnvExt Ei E` by
    rebuilding every rule's real constructor. An inner `.ewk` node is eliminated
    by composing its inclusion with `hext` — the result is never a `.ewk`
    re-wrap of the whole input. -/
def rebaseTy {Ei E : ResolvedEnv} (hext : EnvExt Ei E) : {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP Ei n Γ e T → TyP E n Γ e T
  | _, _, _, _, .sort _ n Γ l k h => .sort E n Γ l k h
  | _, _, _, _, .bvar _ n Γ i A u h hA => .bvar E n Γ i A u h (rebaseTy hext hA)
  | _, _, _, _, .const _ n Γ r ls ls₀ m u hres hlen hwf hls hT =>
      .const E n Γ r ls ls₀ m u (hext r m hres) hlen hwf hls (rebaseTy hext hT)
  | _, _, _, _, .pi _ n Γ A u B v hA hB =>
      .pi E n Γ A u B v (rebaseTy hext hA) (rebaseTy hext hB)
  | _, _, _, _, .lam _ n Γ A u body B v hA hbody hB =>
      .lam E n Γ A u body B v (rebaseTy hext hA) (rebaseTy hext hbody) (rebaseTy hext hB)
  | _, _, _, _, .app _ n Γ f a A B w hf ha hT =>
      .app E n Γ f a A B w (rebaseTy hext hf) (rebaseTy hext ha) (rebaseTy hext hT)
  | _, _, _, _, .letE _ n Γ A u value B body w hA hv hb hT =>
      .letE E n Γ A u value B body w (rebaseTy hext hA) (rebaseTy hext hv)
        (rebaseTy hext hb) (rebaseTy hext hT)
  | _, _, _, _, .lit _ n Γ t T hexp => .lit E n Γ t T (rebaseTy hext hexp)
  | _, _, _, _, .conv _ n Γ e A B u h hc =>
      .conv E n Γ e A B u (rebaseTy hext h) (rebaseCv hext hc)
  | _, _, _, _, .wk _ n Γ e A d c D => .wk E n Γ e A d c (rebaseTy hext D)
  | _, _, _, _, .esub _ n Γ e A t v j u D hget hv hvT =>
      .esub E n Γ e A t v j u (rebaseTy hext D) hget (rebaseTy hext hv)
        (rebaseTy hext hvT)
  | _, _, _, _, .lsub _ n Γ e A t v j u D hget hv hvT =>
      .lsub E n Γ e A t v j u (rebaseTy hext D) hget (rebaseTy hext hv)
        (rebaseTy hext hvT)
  | _, _, _, _, .linst _ a n Γ e A ls hls hlen D =>
      .linst E a n Γ e A ls hls hlen (rebaseTy hext D)
  | _, _, _, _, .ewk E₀ _ n Γ e A hext' D => rebaseTy (envExt_trans hext' hext) D
  | _, _, _, _, .cctx _ n Γ e T A A' u D hA =>
      .cctx E n Γ e T A A' u (rebaseTy hext D) (rebaseCv hext hA)

/-- environment rebase on conversions: rule fields are rebuilt, member lookups
    re-pointed through `hext`, and ι goes through `derivedIotaExt` (the original
    witness's `extWitness`, keeping the original lhs/rhs). -/
def rebaseCv {Ei E : ResolvedEnv} (hext : EnvExt Ei E) : {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → CvP Ei n Γ a b T → CvP E n Γ a b T
  | _, _, _, _, _, .refl _ n Γ a A h dl dr =>
      .refl E n Γ a A (rebaseTy hext h) (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .symm _ n Γ a b A h dl dr =>
      .symm E n Γ a b A (rebaseCv hext h) (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .trans _ n Γ a b c A h1 h2 dl dr =>
      .trans E n Γ a b c A (rebaseCv hext h1) (rebaseCv hext h2)
        (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .beta _ n Γ A body arg B u hA hbody harg dl dr =>
      .beta E n Γ A body arg B u (rebaseTy hext hA) (rebaseTy hext hbody)
        (rebaseTy hext harg) (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .zeta _ n Γ A value body B u hA hv hb dl dr =>
      .zeta E n Γ A value body B u (rebaseTy hext hA) (rebaseTy hext hv)
        (rebaseTy hext hb) (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .zetaLocal _ n Γ i A v hval hty hv dl dr =>
      .zetaLocal E n Γ i A v hval hty (rebaseTy hext hv) (rebaseTy hext dl)
        (rebaseTy hext dr)
  | _, _, _, _, _, .delta _ n Γ r ls m b hres hbody htr hlen hwf hb dl dr =>
      .delta E n Γ r ls m b (hext r m hres) hbody htr hlen hwf
        (rebaseTy hext hb) (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .iota _ n Γ lhs rhs T h hlhs hrhs dl dr =>
      .iota E n Γ lhs rhs T (derivedIotaExt hext h) (rebaseTy hext hlhs)
        (rebaseTy hext hrhs) (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .lit _ n Γ t exp T h hexp dl dr =>
      .lit E n Γ t exp T h (rebaseTy hext hexp) (rebaseTy hext dl)
        (rebaseTy hext dr)
  | _, _, _, _, _, .app _ n Γ f g a b A B h1 h2 dl dr =>
      .app E n Γ f g a b A B (rebaseCv hext h1) (rebaseCv hext h2)
        (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .lam _ n Γ A A' b b' B u hA hb dl dr =>
      .lam E n Γ A A' b b' B u (rebaseCv hext hA) (rebaseCv hext hb)
        (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .pi _ n Γ A A' B B' u v hA hB dl dr =>
      .pi E n Γ A A' B B' u v (rebaseCv hext hA) (rebaseCv hext hB)
        (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .letE _ n Γ A A' v v' b b' B u hA hv hb dl dr =>
      .letE E n Γ A A' v v' b b' B u (rebaseCv hext hA) (rebaseCv hext hv)
        (rebaseCv hext hb) (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .sorts _ n Γ l₁ l₂ h dl dr =>
      .sorts E n Γ l₁ l₂ h (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .consts _ n Γ r ls ls' m hres hlen hwf hwf' h dl dr =>
      .consts E n Γ r ls ls' m (hext r m hres) hlen hwf hwf' h
        (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .eta _ n Γ f A B h dl dr =>
      .eta E n Γ f A B (rebaseTy hext h) (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .irr _ n Γ P p q hP hp hq dl dr =>
      .irr E n Γ P p q (rebaseTy hext hP) (rebaseTy hext hp) (rebaseTy hext hq)
        (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .tyConv _ n Γ a b A A' u h hA dl dr =>
      .tyConv E n Γ a b A A' u (rebaseCv hext h) (rebaseCv hext hA)
        (rebaseTy hext dl) (rebaseTy hext dr)
  | _, _, _, _, _, .wk _ n Γ a b T d c h => .wk E n Γ a b T d c (rebaseCv hext h)
  | _, _, _, _, _, .esub _ n Γ a b T t v j u h hget hv hvT =>
      .esub E n Γ a b T t v j u (rebaseCv hext h) hget (rebaseTy hext hv)
        (rebaseTy hext hvT)
  | _, _, _, _, _, .linst _ a' n Γ a b T ls hls hlen h =>
      .linst E a' n Γ a b T ls hls hlen (rebaseCv hext h)
  | _, _, _, _, _, .ewk E₀ _ n Γ a b T hext' h =>
      rebaseCv (envExt_trans hext' hext) h
  | _, _, _, _, _, .cctx _ n Γ a b T A A' u h hA =>
      .cctx E n Γ a b T A A' u (rebaseCv hext h) (rebaseCv hext hA)
  | _, _, _, _, _, .fsub _ n Γ A B S a b u hB hA hab dl dr =>
      .fsub E n Γ A B S a b u (rebaseTy hext hB) (rebaseTy hext hA)
        (rebaseCv hext hab) (rebaseTy hext dl) (rebaseTy hext dr)

end

/-! ## §4 correspondences -/

/-- index correspondence: the rebased derivation judges the SAME `(n, Γ, e, T)` —
    the signature IS the preservation statement; the `∃` names it for receipts. -/
theorem rebaseTy_index {Ei E : ResolvedEnv} (hext : EnvExt Ei E) {n : Nat}
    {Γ : LCtx} {e T : Expr Nat} (D : TyP Ei n Γ e T) :
    ∃ (D' : TyP E n Γ e T), D' = rebaseTy hext D := ⟨rebaseTy hext D, rfl⟩

theorem rebaseCv_index {Ei E : ResolvedEnv} (hext : EnvExt Ei E) {n : Nat}
    {Γ : LCtx} {a b T : Expr Nat} (h : CvP Ei n Γ a b T) :
    ∃ (h' : CvP E n Γ a b T), h' = rebaseCv hext h := ⟨rebaseCv hext h, rfl⟩

/-- erasure correspondence: rebasing never changes `eps` under the same `σ`, `ρ`
    (`eps` does not read the environment). -/
theorem rebaseTy_eps {Ei E : ResolvedEnv} (hext : EnvExt Ei E) (σ : Level → Level)
    (ρ : List Disp) : {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP Ei n Γ e T) → (rebaseTy hext D).eps σ ρ = D.eps σ ρ
  | _, _, _, _, .sort .. => rfl
  | _, _, _, _, .bvar .. => rfl
  | _, _, _, _, .const .. => rfl
  | _, _, _, _, .pi (hA := hA) (hB := hB) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ hA, rebaseTy_eps hext σ _ hB]
  | _, _, _, _, .lam (hbody := hbody) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ hbody]
  | _, _, _, _, .app (hf := hf) (ha := ha) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ hf, rebaseTy_eps hext σ _ ha]
  | _, _, _, _, .letE (hv := hv) (hb := hb) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ hv, rebaseTy_eps hext σ _ hb]
  | _, _, _, _, .lit (hexp := hexp) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ hexp]
  | _, _, _, _, .conv (h := h) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ h]
  | _, _, _, _, .wk (D := D) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ D]
  | _, _, _, _, .esub (D := D) (hv := hv) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ D, rebaseTy_eps hext σ _ hv]
  | _, _, _, _, .lsub (D := D) (hv := hv) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ D, rebaseTy_eps hext σ _ hv]
  | _, _, _, _, .linst (D := D) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext _ _ D]
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' D => by
      simp only [rebaseTy, TyP.eps]
      exact rebaseTy_eps (envExt_trans hext' hext) σ ρ D
  | _, _, _, _, .cctx (D := D) .. => by
      simp only [rebaseTy, TyP.eps, rebaseTy_eps hext σ _ D]

mutual

/-- `AssumpPref` correspondence: the rebuilt derivation keeps every
    `AssumptionPrefix` guard — its context is the SAME `Γ` at the same cutoff. -/
theorem rebaseTy_assumpPref {Ei E : ResolvedEnv} (hext : EnvExt Ei E) : {n : Nat} →
    {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    D.AssumpPref → (rebaseTy hext D).AssumpPref
  | _, _, _, _, .sort .. => fun _ => trivial
  | _, _, _, _, .bvar (hA := hA) .. => rebaseTy_assumpPref hext hA
  | _, _, _, _, .const (hT := hT) .. => rebaseTy_assumpPref hext hT
  | _, _, _, _, .pi (hA := hA) (hB := hB) .. => fun ⟨ha, hb⟩ =>
      ⟨rebaseTy_assumpPref hext hA ha, rebaseTy_assumpPref hext hB hb⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ hA hbody hB => fun ⟨ha, hd, hc⟩ =>
      ⟨rebaseTy_assumpPref hext hA ha, rebaseTy_assumpPref hext hbody hd,
        rebaseTy_assumpPref hext hB hc⟩
  | _, _, _, _, .app (hf := hf) (ha := ha) (hT := hT) .. => fun ⟨hf', ha', ht⟩ =>
      ⟨rebaseTy_assumpPref hext hf hf', rebaseTy_assumpPref hext ha ha',
        rebaseTy_assumpPref hext hT ht⟩
  | _, _, _, _, .letE (hA := hA) (hv := hv) (hb := hb) (hT := hT) .. =>
      fun ⟨ha, hv', hb', ht⟩ =>
        ⟨rebaseTy_assumpPref hext hA ha, rebaseTy_assumpPref hext hv hv',
          rebaseTy_assumpPref hext hb hb', rebaseTy_assumpPref hext hT ht⟩
  | _, _, _, _, .lit (hexp := hexp) .. => rebaseTy_assumpPref hext hexp
  | _, _, _, _, .conv (h := h) (hc := hc) .. => fun ⟨hd, hc'⟩ =>
      ⟨rebaseTy_assumpPref hext h hd, rebaseCv_assumpPref hext hc hc'⟩
  | _, _, _, _, .wk (D := D) .. => fun ⟨hp, hd⟩ =>
      ⟨hp, rebaseTy_assumpPref hext D hd⟩
  | _, _, _, _, .esub (D := D) (hv := hv) (hvT := hvT) .. => fun ⟨hp, hd, hv', ht⟩ =>
      ⟨hp, rebaseTy_assumpPref hext D hd, rebaseTy_assumpPref hext hv hv',
        rebaseTy_assumpPref hext hvT ht⟩
  | _, _, _, _, .lsub (D := D) (hv := hv) (hvT := hvT) .. => fun ⟨hp, hd, hv', ht⟩ =>
      ⟨hp, rebaseTy_assumpPref hext D hd, rebaseTy_assumpPref hext hv hv',
        rebaseTy_assumpPref hext hvT ht⟩
  | _, _, _, _, .linst (D := D) .. => rebaseTy_assumpPref hext D
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' D =>
      rebaseTy_assumpPref (envExt_trans hext' hext) D
  | _, _, _, _, .cctx (D := D) (hA := hA) .. => fun ⟨hd, ha⟩ =>
      ⟨rebaseTy_assumpPref hext D hd, rebaseCv_assumpPref hext hA ha⟩

theorem rebaseCv_assumpPref {Ei E : ResolvedEnv} (hext : EnvExt Ei E) : {n : Nat} →
    {Γ : LCtx} → {a b T : Expr Nat} → (h : CvP Ei n Γ a b T) →
    h.AssumpPref → (rebaseCv hext h).AssumpPref
  | _, _, _, _, _, .refl (h := h) (dl := dl) (dr := dr) .. => fun ⟨hd, hl, hr⟩ =>
      ⟨rebaseTy_assumpPref hext h hd, rebaseTy_assumpPref hext dl hl,
        rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .symm (h := h) (dl := dl) (dr := dr) .. => fun ⟨hd, hl, hr⟩ =>
      ⟨rebaseCv_assumpPref hext h hd, rebaseTy_assumpPref hext dl hl,
        rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .trans (h1 := h1) (h2 := h2) (dl := dl) (dr := dr) .. =>
      fun ⟨h1', h2', hl, hr⟩ =>
        ⟨rebaseCv_assumpPref hext h1 h1', rebaseCv_assumpPref hext h2 h2',
          rebaseTy_assumpPref hext dl hl, rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .beta (hA := hA) (hbody := hbody) (harg := harg) (dl := dl)
        (dr := dr) .. => fun ⟨ha, hb, hg, hl, hr⟩ =>
      ⟨rebaseTy_assumpPref hext hA ha, rebaseTy_assumpPref hext hbody hb,
        rebaseTy_assumpPref hext harg hg, rebaseTy_assumpPref hext dl hl,
        rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .zeta (hA := hA) (hv := hv) (hb := hb) (dl := dl) (dr := dr) .. =>
      fun ⟨ha, hv', hb', hl, hr⟩ =>
        ⟨rebaseTy_assumpPref hext hA ha, rebaseTy_assumpPref hext hv hv',
          rebaseTy_assumpPref hext hb hb', rebaseTy_assumpPref hext dl hl,
          rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .zetaLocal (hv := hv) (dl := dl) (dr := dr) .. =>
      fun ⟨hv', hl, hr⟩ =>
        ⟨rebaseTy_assumpPref hext hv hv', rebaseTy_assumpPref hext dl hl,
          rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .delta (hb := hb) (dl := dl) (dr := dr) .. => fun ⟨hb', hl, hr⟩ =>
      ⟨rebaseTy_assumpPref hext hb hb', rebaseTy_assumpPref hext dl hl,
        rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .iota (hlhs := hlhs) (hrhs := hrhs) (dl := dl) (dr := dr) .. =>
      fun ⟨hl, hr, hdl, hdr⟩ =>
        ⟨rebaseTy_assumpPref hext hlhs hl, rebaseTy_assumpPref hext hrhs hr,
          rebaseTy_assumpPref hext dl hdl, rebaseTy_assumpPref hext dr hdr⟩
  | _, _, _, _, _, .lit (hexp := hexp) (dl := dl) (dr := dr) .. =>
      fun ⟨he, hl, hr⟩ =>
        ⟨rebaseTy_assumpPref hext hexp he, rebaseTy_assumpPref hext dl hl,
          rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .app (h1 := h1) (h2 := h2) (dl := dl) (dr := dr) .. =>
      fun ⟨h1', h2', hl, hr⟩ =>
        ⟨rebaseCv_assumpPref hext h1 h1', rebaseCv_assumpPref hext h2 h2',
          rebaseTy_assumpPref hext dl hl, rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .lam (hA := hA) (hb := hb) (dl := dl) (dr := dr) .. =>
      fun ⟨ha, hb', hl, hr⟩ =>
        ⟨rebaseCv_assumpPref hext hA ha, rebaseCv_assumpPref hext hb hb',
          rebaseTy_assumpPref hext dl hl, rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .pi (hA := hA) (hB := hB) (dl := dl) (dr := dr) .. =>
      fun ⟨ha, hb', hl, hr⟩ =>
        ⟨rebaseCv_assumpPref hext hA ha, rebaseCv_assumpPref hext hB hb',
          rebaseTy_assumpPref hext dl hl, rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .letE (hA := hA) (hv := hv) (hb := hb) (dl := dl) (dr := dr) .. =>
      fun ⟨ha, hv', hb', hl, hr⟩ =>
        ⟨rebaseCv_assumpPref hext hA ha, rebaseCv_assumpPref hext hv hv',
          rebaseCv_assumpPref hext hb hb', rebaseTy_assumpPref hext dl hl,
          rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .sorts (dl := dl) (dr := dr) .. => fun ⟨hl, hr⟩ =>
      ⟨rebaseTy_assumpPref hext dl hl, rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .consts (dl := dl) (dr := dr) .. => fun ⟨hl, hr⟩ =>
      ⟨rebaseTy_assumpPref hext dl hl, rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .eta (h := h) (dl := dl) (dr := dr) .. => fun ⟨hd, hl, hr⟩ =>
      ⟨rebaseTy_assumpPref hext h hd, rebaseTy_assumpPref hext dl hl,
        rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .irr (hP := hP) (hp := hp) (hq := hq) (dl := dl) (dr := dr) .. =>
      fun ⟨hP', hp', hq', hl, hr⟩ =>
        ⟨rebaseTy_assumpPref hext hP hP', rebaseTy_assumpPref hext hp hp',
          rebaseTy_assumpPref hext hq hq', rebaseTy_assumpPref hext dl hl,
          rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .tyConv (h := h) (hA := hA) (dl := dl) (dr := dr) .. =>
      fun ⟨hd, ha, hl, hr⟩ =>
        ⟨rebaseCv_assumpPref hext h hd, rebaseCv_assumpPref hext hA ha,
          rebaseTy_assumpPref hext dl hl, rebaseTy_assumpPref hext dr hr⟩
  | _, _, _, _, _, .wk (h := h) .. => fun ⟨hp, hd⟩ =>
      ⟨hp, rebaseCv_assumpPref hext h hd⟩
  | _, _, _, _, _, .esub (h := h) (hv := hv) (hvT := hvT) .. =>
      fun ⟨hp, hd, hv', ht⟩ =>
        ⟨hp, rebaseCv_assumpPref hext h hd, rebaseTy_assumpPref hext hv hv',
          rebaseTy_assumpPref hext hvT ht⟩
  | _, _, _, _, _, .linst (h := h) .. => rebaseCv_assumpPref hext h
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ hext' h =>
      rebaseCv_assumpPref (envExt_trans hext' hext) h
  | _, _, _, _, _, .cctx (h := h) (hA := hA) .. => fun ⟨hd, ha⟩ =>
      ⟨rebaseCv_assumpPref hext h hd, rebaseCv_assumpPref hext hA ha⟩
  | _, _, _, _, _, .fsub (hB := hB) (hA := hA) (hab := hab) (dl := dl) (dr := dr) .. =>
      fun ⟨hb, ha, hc, hl, hr⟩ =>
        ⟨rebaseTy_assumpPref hext hB hb, rebaseTy_assumpPref hext hA ha,
          rebaseCv_assumpPref hext hab hc, rebaseTy_assumpPref hext dl hl,
          rebaseTy_assumpPref hext dr hr⟩

end

mutual

/-- weight non-increase: rebasing only ever removes the `1 +` of eliminated
    inner `.ewk` nodes. -/
theorem rebaseTy_wt_le (Aw : Nat → Nat) {Ei E : ResolvedEnv} (hext : EnvExt Ei E) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    (rebaseTy hext D).wt Aw ≤ D.wt Aw
  | _, _, _, _, .sort .. => by
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .bvar (hA := hA) .. => by
      have ih := rebaseTy_wt_le Aw hext hA
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .const (hT := hT) .. => by
      have ih := rebaseTy_wt_le Aw hext hT
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .pi (hA := hA) (hB := hB) .. => by
      have iha := rebaseTy_wt_le Aw hext hA
      have ihb := rebaseTy_wt_le Aw hext hB
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ hA hbody hB => by
      have iha := rebaseTy_wt_le Aw hext hA
      have ihb := rebaseTy_wt_le Aw hext hbody
      have ihc := rebaseTy_wt_le Aw hext hB
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .app (hf := hf) (ha := ha) (hT := hT) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hf
      have ih2 := rebaseTy_wt_le Aw hext ha
      have ih3 := rebaseTy_wt_le Aw hext hT
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .letE (hA := hA) (hv := hv) (hb := hb) (hT := hT) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hA
      have ih2 := rebaseTy_wt_le Aw hext hv
      have ih3 := rebaseTy_wt_le Aw hext hb
      have ih4 := rebaseTy_wt_le Aw hext hT
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .lit (hexp := hexp) .. => by
      have ih := rebaseTy_wt_le Aw hext hexp
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .conv (h := h) (hc := hc) .. => by
      have ih1 := rebaseTy_wt_le Aw hext h
      have ih2 := rebaseCv_wt_le Aw hext hc
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .wk (D := D) .. => by
      have ih := rebaseTy_wt_le Aw hext D
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .esub (D := D) (hv := hv) (hvT := hvT) .. => by
      have ih1 := rebaseTy_wt_le Aw hext D
      have ih2 := rebaseTy_wt_le Aw hext hv
      have ih3 := rebaseTy_wt_le Aw hext hvT
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .lsub (D := D) (hv := hv) (hvT := hvT) .. => by
      have ih1 := rebaseTy_wt_le Aw hext D
      have ih2 := rebaseTy_wt_le Aw hext hv
      have ih3 := rebaseTy_wt_le Aw hext hvT
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .linst (D := D) .. => by
      have ih := rebaseTy_wt_le Aw hext D
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' D => by
      have ih := rebaseTy_wt_le Aw (envExt_trans hext' hext) D
      simp only [rebaseTy, TyP.wt]; omega
  | _, _, _, _, .cctx (D := D) (hA := hA) .. => by
      have ih1 := rebaseTy_wt_le Aw hext D
      have ih2 := rebaseCv_wt_le Aw hext hA
      simp only [rebaseTy, TyP.wt]; omega

theorem rebaseCv_wt_le (Aw : Nat → Nat) {Ei E : ResolvedEnv} (hext : EnvExt Ei E) :
    {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} → (h : CvP Ei n Γ a b T) →
    (rebaseCv hext h).wt Aw ≤ h.wt Aw
  | _, _, _, _, _, .refl (h := h) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext h
      have ih2 := rebaseTy_wt_le Aw hext dl
      have ih3 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .symm (h := h) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseCv_wt_le Aw hext h
      have ih2 := rebaseTy_wt_le Aw hext dl
      have ih3 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .trans (h1 := h1) (h2 := h2) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseCv_wt_le Aw hext h1
      have ih2 := rebaseCv_wt_le Aw hext h2
      have ih3 := rebaseTy_wt_le Aw hext dl
      have ih4 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .beta (hA := hA) (hbody := hbody) (harg := harg) (dl := dl)
        (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hA
      have ih2 := rebaseTy_wt_le Aw hext hbody
      have ih3 := rebaseTy_wt_le Aw hext harg
      have ih4 := rebaseTy_wt_le Aw hext dl
      have ih5 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .zeta (hA := hA) (hv := hv) (hb := hb) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hA
      have ih2 := rebaseTy_wt_le Aw hext hv
      have ih3 := rebaseTy_wt_le Aw hext hb
      have ih4 := rebaseTy_wt_le Aw hext dl
      have ih5 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .zetaLocal (hv := hv) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hv
      have ih2 := rebaseTy_wt_le Aw hext dl
      have ih3 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .delta (hb := hb) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hb
      have ih2 := rebaseTy_wt_le Aw hext dl
      have ih3 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .iota (hlhs := hlhs) (hrhs := hrhs) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hlhs
      have ih2 := rebaseTy_wt_le Aw hext hrhs
      have ih3 := rebaseTy_wt_le Aw hext dl
      have ih4 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .lit (hexp := hexp) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hexp
      have ih2 := rebaseTy_wt_le Aw hext dl
      have ih3 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .app (h1 := h1) (h2 := h2) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseCv_wt_le Aw hext h1
      have ih2 := rebaseCv_wt_le Aw hext h2
      have ih3 := rebaseTy_wt_le Aw hext dl
      have ih4 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .lam (hA := hA) (hb := hb) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseCv_wt_le Aw hext hA
      have ih2 := rebaseCv_wt_le Aw hext hb
      have ih3 := rebaseTy_wt_le Aw hext dl
      have ih4 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .pi (hA := hA) (hB := hB) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseCv_wt_le Aw hext hA
      have ih2 := rebaseCv_wt_le Aw hext hB
      have ih3 := rebaseTy_wt_le Aw hext dl
      have ih4 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .letE (hA := hA) (hv := hv) (hb := hb) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseCv_wt_le Aw hext hA
      have ih2 := rebaseCv_wt_le Aw hext hv
      have ih3 := rebaseCv_wt_le Aw hext hb
      have ih4 := rebaseTy_wt_le Aw hext dl
      have ih5 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .sorts (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext dl
      have ih2 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .consts (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext dl
      have ih2 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .eta (h := h) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext h
      have ih2 := rebaseTy_wt_le Aw hext dl
      have ih3 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .irr (hP := hP) (hp := hp) (hq := hq) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hP
      have ih2 := rebaseTy_wt_le Aw hext hp
      have ih3 := rebaseTy_wt_le Aw hext hq
      have ih4 := rebaseTy_wt_le Aw hext dl
      have ih5 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .tyConv (h := h) (hA := hA) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseCv_wt_le Aw hext h
      have ih2 := rebaseCv_wt_le Aw hext hA
      have ih3 := rebaseTy_wt_le Aw hext dl
      have ih4 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .wk (h := h) .. => by
      have ih := rebaseCv_wt_le Aw hext h
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .esub (h := h) (hv := hv) (hvT := hvT) .. => by
      have ih1 := rebaseCv_wt_le Aw hext h
      have ih2 := rebaseTy_wt_le Aw hext hv
      have ih3 := rebaseTy_wt_le Aw hext hvT
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .linst (h := h) .. => by
      have ih := rebaseCv_wt_le Aw hext h
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ hext' h => by
      have ih := rebaseCv_wt_le Aw (envExt_trans hext' hext) h
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .cctx (h := h) (hA := hA) .. => by
      have ih1 := rebaseCv_wt_le Aw hext h
      have ih2 := rebaseCv_wt_le Aw hext hA
      simp only [rebaseCv, CvP.wt]; omega
  | _, _, _, _, _, .fsub (hB := hB) (hA := hA) (hab := hab) (dl := dl) (dr := dr) .. => by
      have ih1 := rebaseTy_wt_le Aw hext hB
      have ih2 := rebaseTy_wt_le Aw hext hA
      have ih3 := rebaseCv_wt_le Aw hext hab
      have ih4 := rebaseTy_wt_le Aw hext dl
      have ih5 := rebaseTy_wt_le Aw hext dr
      simp only [rebaseCv, CvP.wt]; omega

end

/-- the composable non-increasing relation on atom lists (`S1` §3.1): same
    positions, each atom not heavier. -/
inductive AtomsLe : List Nat → List Nat → Prop
  | nil : AtomsLe [] []
  | cons {x y : Nat} {xs ys : List Nat} : x ≤ y → AtomsLe xs ys →
      AtomsLe (x :: xs) (y :: ys)

theorem atomsLe_append {l₁ l₂ m₁ m₂ : List Nat}
    (h₁ : AtomsLe l₁ m₁) (h₂ : AtomsLe l₂ m₂) : AtomsLe (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hhd _ ih => exact AtomsLe.cons hhd ih

mutual

/-- atom-list non-increase, per position: a rebased node's only atom is its own
    weight (`rebaseTy_wt_le` pays), transports concatenate the children's
    non-increasing lists (`atomsLe_append` composes). -/
theorem rebaseTy_atoms_le (Aw : Nat → Nat) {Ei E : ResolvedEnv} (hext : EnvExt Ei E) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    AtomsLe ((rebaseTy hext D).atoms Aw) (D.atoms Aw)
  | _, _, _, _, .sort _ n Γ l k h => by
      exact AtomsLe.cons (rebaseTy_wt_le Aw hext (.sort _ n Γ l k h)) .nil
  | _, _, _, _, .bvar _ n Γ i A u h hA => by
      exact AtomsLe.cons (rebaseTy_wt_le Aw hext (.bvar _ n Γ i A u h hA)) .nil
  | _, _, _, _, .const _ n Γ r ls ls₀ m u hres hlen hwf hls hT => by
      exact AtomsLe.cons
        (rebaseTy_wt_le Aw hext (.const _ n Γ r ls ls₀ m u hres hlen hwf hls hT)) .nil
  | _, _, _, _, .pi _ n Γ A u B v hA hB => by
      exact AtomsLe.cons (rebaseTy_wt_le Aw hext (.pi _ n Γ A u B v hA hB)) .nil
  | _, _, _, _, .lam _ n Γ A u body B v hA hbody hB => by
      exact AtomsLe.cons
        (rebaseTy_wt_le Aw hext (.lam _ n Γ A u body B v hA hbody hB)) .nil
  | _, _, _, _, .app _ n Γ f a A B w hf ha hT => by
      exact AtomsLe.cons (rebaseTy_wt_le Aw hext (.app _ n Γ f a A B w hf ha hT)) .nil
  | _, _, _, _, .letE _ n Γ A u value B body w hA hv hb hT => by
      exact AtomsLe.cons
        (rebaseTy_wt_le Aw hext (.letE _ n Γ A u value B body w hA hv hb hT)) .nil
  | _, _, _, _, .lit _ n Γ t T hexp => by
      exact AtomsLe.cons (rebaseTy_wt_le Aw hext (.lit _ n Γ t T hexp)) .nil
  | _, _, _, _, .conv _ n Γ e A B u h hc => by
      exact AtomsLe.cons (rebaseTy_wt_le Aw hext (.conv _ n Γ e A B u h hc)) .nil
  | _, _, _, _, .wk (D := D) .. => by
      have ih := rebaseTy_atoms_le Aw hext D
      simp only [rebaseTy, TyP.atoms]; exact ih
  | _, _, _, _, .esub (D := D) (hv := hv) (hvT := hvT) .. => by
      have ih1 := rebaseTy_atoms_le Aw hext D
      have ih2 := rebaseTy_atoms_le Aw hext hv
      have ih3 := rebaseTy_atoms_le Aw hext hvT
      simp only [rebaseTy, TyP.atoms]
      exact atomsLe_append (atomsLe_append ih1 ih2) ih3
  | _, _, _, _, .lsub (D := D) (hv := hv) (hvT := hvT) .. => by
      have ih1 := rebaseTy_atoms_le Aw hext D
      have ih2 := rebaseTy_atoms_le Aw hext hv
      have ih3 := rebaseTy_atoms_le Aw hext hvT
      simp only [rebaseTy, TyP.atoms]
      exact atomsLe_append (atomsLe_append ih1 ih2) ih3
  | _, _, _, _, .linst (D := D) .. => by
      have ih := rebaseTy_atoms_le Aw hext D
      simp only [rebaseTy, TyP.atoms]; exact ih
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' D => by
      have ih := rebaseTy_atoms_le Aw (envExt_trans hext' hext) D
      simp only [rebaseTy, TyP.atoms]; exact ih
  | _, _, _, _, .cctx (D := D) (hA := hA) .. => by
      have ih1 := rebaseTy_atoms_le Aw hext D
      have ih2 := rebaseCv_atoms_le Aw hext hA
      simp only [rebaseTy, TyP.atoms]
      exact atomsLe_append ih1 ih2

theorem rebaseCv_atoms_le (Aw : Nat → Nat) {Ei E : ResolvedEnv} (hext : EnvExt Ei E) :
    {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} → (h : CvP Ei n Γ a b T) →
    AtomsLe ((rebaseCv hext h).atoms Aw) (h.atoms Aw)
  | _, _, _, _, _, .refl _ n Γ a A h dl dr => by
      exact AtomsLe.cons (rebaseCv_wt_le Aw hext (.refl _ n Γ a A h dl dr)) .nil
  | _, _, _, _, _, .symm _ n Γ a b A h dl dr => by
      exact AtomsLe.cons (rebaseCv_wt_le Aw hext (.symm _ n Γ a b A h dl dr)) .nil
  | _, _, _, _, _, .trans _ n Γ a b c A h1 h2 dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.trans _ n Γ a b c A h1 h2 dl dr)) .nil
  | _, _, _, _, _, .beta _ n Γ A body arg B u hA hbody harg dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.beta _ n Γ A body arg B u hA hbody harg dl dr)) .nil
  | _, _, _, _, _, .zeta _ n Γ A value body B u hA hv hb dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.zeta _ n Γ A value body B u hA hv hb dl dr)) .nil
  | _, _, _, _, _, .zetaLocal _ n Γ i A v hval hty hv dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.zetaLocal _ n Γ i A v hval hty hv dl dr)) .nil
  | _, _, _, _, _, .delta _ n Γ r ls m b hres hbody htr hlen hwf hb dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext
          (.delta _ n Γ r ls m b hres hbody htr hlen hwf hb dl dr)) .nil
  | _, _, _, _, _, .iota _ n Γ lhs rhs T h hlhs hrhs dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.iota _ n Γ lhs rhs T h hlhs hrhs dl dr)) .nil
  | _, _, _, _, _, .lit _ n Γ t exp T h hexp dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.lit _ n Γ t exp T h hexp dl dr)) .nil
  | _, _, _, _, _, .app _ n Γ f g a b A B h1 h2 dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.app _ n Γ f g a b A B h1 h2 dl dr)) .nil
  | _, _, _, _, _, .lam _ n Γ A A' b b' B u hA hb dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.lam _ n Γ A A' b b' B u hA hb dl dr)) .nil
  | _, _, _, _, _, .pi _ n Γ A A' B B' u v hA hB dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.pi _ n Γ A A' B B' u v hA hB dl dr)) .nil
  | _, _, _, _, _, .letE _ n Γ A A' v v' b b' B u hA hv hb dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.letE _ n Γ A A' v v' b b' B u hA hv hb dl dr)) .nil
  | _, _, _, _, _, .sorts _ n Γ l₁ l₂ h dl dr => by
      exact AtomsLe.cons (rebaseCv_wt_le Aw hext (.sorts _ n Γ l₁ l₂ h dl dr)) .nil
  | _, _, _, _, _, .consts _ n Γ r ls ls' m hres hlen hwf hwf' h dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.consts _ n Γ r ls ls' m hres hlen hwf hwf' h dl dr))
        .nil
  | _, _, _, _, _, .eta _ n Γ f A B h dl dr => by
      exact AtomsLe.cons (rebaseCv_wt_le Aw hext (.eta _ n Γ f A B h dl dr)) .nil
  | _, _, _, _, _, .irr _ n Γ P p q hP hp hq dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.irr _ n Γ P p q hP hp hq dl dr)) .nil
  | _, _, _, _, _, .tyConv _ n Γ a b A A' u h hA dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.tyConv _ n Γ a b A A' u h hA dl dr)) .nil
  | _, _, _, _, _, .fsub _ n Γ A B S a b u hB hA hab dl dr => by
      exact AtomsLe.cons
        (rebaseCv_wt_le Aw hext (.fsub _ n Γ A B S a b u hB hA hab dl dr)) .nil
  | _, _, _, _, _, .wk (h := h) .. => by
      have ih := rebaseCv_atoms_le Aw hext h
      simp only [rebaseCv, CvP.atoms]; exact ih
  | _, _, _, _, _, .esub (h := h) (hv := hv) (hvT := hvT) .. => by
      have ih1 := rebaseCv_atoms_le Aw hext h
      have ih2 := rebaseTy_atoms_le Aw hext hv
      have ih3 := rebaseTy_atoms_le Aw hext hvT
      simp only [rebaseCv, CvP.atoms]
      exact atomsLe_append (atomsLe_append ih1 ih2) ih3
  | _, _, _, _, _, .linst (h := h) .. => by
      have ih := rebaseCv_atoms_le Aw hext h
      simp only [rebaseCv, CvP.atoms]; exact ih
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ hext' h => by
      have ih := rebaseCv_atoms_le Aw (envExt_trans hext' hext) h
      simp only [rebaseCv, CvP.atoms]; exact ih
  | _, _, _, _, _, .cctx (h := h) (hA := hA) .. => by
      have ih1 := rebaseCv_atoms_le Aw hext h
      have ih2 := rebaseCv_atoms_le Aw hext hA
      simp only [rebaseCv, CvP.atoms]
      exact atomsLe_append ih1 ih2

end

/-- `dl`/`dr` correspondence, as literal equalities: the rebased conversion's
    endpoints are the rebases of the original endpoints. Erasure correspondence
    follows by `rebaseTy_eps`. -/
theorem rebaseCv_dl_dr {Ei E : ResolvedEnv} (hext : EnvExt Ei E) : {n : Nat} →
    {Γ : LCtx} → {a b T : Expr Nat} → (h : CvP Ei n Γ a b T) →
    (rebaseCv hext h).dl = rebaseTy hext h.dl ∧
    (rebaseCv hext h).dr = rebaseTy hext h.dr
  | _, _, _, _, _, .refl .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .symm .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .trans .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .beta .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .zeta .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .zetaLocal .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .delta .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .iota .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .lit .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .app .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .lam .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .pi .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .letE .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .sorts .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .consts .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .eta .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .irr .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .tyConv .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .fsub .. => ⟨rfl, rfl⟩
  | _, _, _, _, _, .wk (h := h) .. => by
      have ⟨h1, h2⟩ := rebaseCv_dl_dr hext h
      simp only [rebaseCv, CvP.dl, CvP.dr, rebaseTy, h1, h2]
      exact ⟨True.intro, True.intro⟩
  | _, _, _, _, _, .esub (h := h) .. => by
      have ⟨h1, h2⟩ := rebaseCv_dl_dr hext h
      simp only [rebaseCv, CvP.dl, CvP.dr, rebaseTy, h1, h2]
      exact ⟨True.intro, True.intro⟩
  | _, _, _, _, _, .linst (h := h) .. => by
      have ⟨h1, h2⟩ := rebaseCv_dl_dr hext h
      simp only [rebaseCv, CvP.dl, CvP.dr, rebaseTy, h1, h2]
      exact ⟨True.intro, True.intro⟩
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ hext' h => by
      simp only [rebaseCv, CvP.dl, CvP.dr, rebaseTy]
      exact rebaseCv_dl_dr (envExt_trans hext' hext) h
  | _, _, _, _, _, .cctx (h := h) .. => by
      have ⟨h1, h2⟩ := rebaseCv_dl_dr hext h
      simp only [rebaseCv, CvP.dl, CvP.dr, rebaseTy, h1, h2]
      exact ⟨True.intro, True.intro⟩

/-- regularity correspondence, as a pair equality: the rebased node's `reg` is
    the original level and the rebase of the original `reg` derivation. At `conv`
    it goes through `rebaseCv_dl_dr`'s `dr` half; regularity LEVEL and regularity
    ERASURE correspondences then follow by projection and `rebaseTy_eps`. -/
theorem rebaseTy_reg {Ei E : ResolvedEnv} (hext : EnvExt Ei E) : {n : Nat} →
    {Γ : LCtx} → {e T : Expr Nat} → (D : TyP Ei n Γ e T) →
    (rebaseTy hext D).reg = ⟨D.reg.1, rebaseTy hext D.reg.2⟩
  | _, _, _, _, .sort .. => rfl
  | _, _, _, _, .bvar .. => rfl
  | _, _, _, _, .const .. => rfl
  | _, _, _, _, .pi .. => rfl
  | _, _, _, _, .lam .. => rfl
  | _, _, _, _, .app .. => rfl
  | _, _, _, _, .letE .. => rfl
  | _, _, _, _, .lit (hexp := hexp) .. => by
      show (rebaseTy hext hexp).reg = ⟨hexp.reg.1, rebaseTy hext hexp.reg.2⟩
      exact rebaseTy_reg hext hexp
  | _, _, _, _, .conv _ n Γ _ _ B u _ hc => by
      exact congrArg (fun x => (⟨u, x⟩ : (u' : Level) × TyP E n Γ B (.sort u')))
        (rebaseCv_dl_dr hext hc).2
  | _, _, _, _, .wk (D := D) .. => by
      simp only [rebaseTy, TyP.reg]
      rw [rebaseTy_reg hext D]
  | _, _, _, _, .esub (D := D) .. => by
      simp only [rebaseTy, TyP.reg]
      rw [rebaseTy_reg hext D]
  | _, _, _, _, .lsub (D := D) .. => by
      simp only [rebaseTy, TyP.reg]
      rw [rebaseTy_reg hext D]
  | _, _, _, _, .linst (D := D) .. => by
      simp only [rebaseTy, TyP.reg]
      rw [rebaseTy_reg hext D]
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' D => by
      simp only [rebaseTy, TyP.reg]
      exact rebaseTy_reg (envExt_trans hext' hext) D
  | _, _, _, _, .cctx (D := D) .. => by
      simp only [rebaseTy, TyP.reg]
      rw [rebaseTy_reg hext D]

/-- regularity level correspondence, projected out of `rebaseTy_reg`. -/
theorem rebaseTy_reg_fst {Ei E : ResolvedEnv} (hext : EnvExt Ei E) {n : Nat}
    {Γ : LCtx} {e T : Expr Nat} (D : TyP Ei n Γ e T) :
    (rebaseTy hext D).reg.1 = D.reg.1 :=
  congrArg (·.1) (rebaseTy_reg hext D)

/-- regularity erasure correspondence (`S1` §3.1), composed from
    `rebaseTy_reg` and `rebaseTy_eps`. -/
theorem rebaseTy_reg_eps {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (σ : Level → Level) (ρ : List Disp) {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP Ei n Γ e T) :
    (rebaseTy hext D).reg.2.eps σ ρ = D.reg.2.eps σ ρ := by
  rw [rebaseTy_reg hext D]
  exact rebaseTy_eps hext σ ρ D.reg.2

/-- `dl`/`dr` erasure correspondence (`S1` §3.1), composed from
    `rebaseCv_dl_dr` and `rebaseTy_eps`. -/
theorem rebaseCv_dl_eps {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (σ : Level → Level) (ρ : List Disp) {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP Ei n Γ a b T) :
    (rebaseCv hext h).dl.eps σ ρ = h.dl.eps σ ρ := by
  rw [(rebaseCv_dl_dr hext h).1, rebaseTy_eps hext σ ρ h.dl]

theorem rebaseCv_dr_eps {Ei E : ResolvedEnv} (hext : EnvExt Ei E)
    (σ : Level → Level) (ρ : List Disp) {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP Ei n Γ a b T) :
    (rebaseCv hext h).dr.eps σ ρ = h.dr.eps σ ρ := by
  rw [(rebaseCv_dl_dr hext h).2, rebaseTy_eps hext σ ρ h.dr]

end Rcic.Syn
